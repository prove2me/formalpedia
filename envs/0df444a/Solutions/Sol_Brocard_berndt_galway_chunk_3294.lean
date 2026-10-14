-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3294
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:13:57.1281+00:00
-- url     : https://prove2.me/submissions/d4fbd7c4-2c87-4900-81cf-eb5c47124a62

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 592266187 ≤ n < 592446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 592267437 1250 592266187 592266203
    0x30702280c06030213032013090201170c0301030b270d08010b0a020c1c1704050f100e090a23100609050604060509060f040303020f011406030d050d1404 67
    0x80e4580308412400652000091500621002046401c1c1d903590754200ca400005032002d0500d483d0f2070b50f259018190b003040d4070025141c0011392000c0a94410070585200303032540c1407101c028a011160486040f0b84883c0004d804100500000c0d1064180700d8004090815100c0c0c0004001d400c640c6c4045c107024402110750004c1c0918460991100340d1500408800715030a20784042c000c4000d4681c2401c00004e801100300301c0d18405100503200000c00940d402583e91040740801ca542650b00340d010b403180074072602d00741540b00c5051509138400003080342a601d40302d80300c114880512841800c0100003810460b5030700510100703204901e609840c254138140c1021190310700390310300300186070780c5401807410003446030f9081c41551211421102950000c2c00d1a6484031520000210580b09000c0c407000d0307204011400100300b43e0001031840383e11580074000d0003800ca180804120500e0211041d95059101041010844c1c1c080d10081101400c0e40e60046661500130b0300c0f405213804142ca00f214640 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 592268687 1250 592267437 592267513
    0x606280302150324060a0e0a090e030d05070e0d0b061503011e080d021216020a06030603110d02030309040e010b10091a031302040e0102390c06070602030702 69
    0x44035a070241d0141051004c0c006801c88900804541a80540516032003408042d100c81d26880d9207101902c001407080340000d2084031003032844542c0740d40201e450b6910290030503002c900300c04d0081c00800b08a1101030510000451582c80744107482c54090960740d00515002107619a0034a158005d502800300c0004101e44a2805200044040305940c800743c0b164200303240211040c1d07404130b030380101890000034030742e1240d400412440080d07400040081d03100c102c1d0b034000502c450305a0010703012640a003229000c02c10301ca40230b00412980610009605810401502c155441c00c1d520072903910b058607000007134000307255000c107201c02c0c03140741d02001140c042c140420941680c14240a0001510340b40030b03041d820820342201031482a85002441561a43c60340b00800c0750035410b9503503914000c110041c2545071100d000300ca440b04520320b810341c8080e00c8032404444030000b807640b21000c40904030b42e11786851900c902000b500007500d0502103005000d4040c08544100c0a00501511101c400010742 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 592269937 1250 592268687 592268701
    0xf1c02090111060c041203110a05060604051303080609070903020a030f060c021507083d08030c12030c0f180a0905040f02010f0519031a0306062803021503 68
    0x481c040c0407142e940d1051082103207252003401514200c0d03a44245140b018409450282c4d2103100320f4035a040070344202c102c00814448001042d07406080c056404200d5a12108150000c0c0c07000c5000140204140c6070204643d820581c90303d951052080c07070302c6004503451780e0016071541c1c000d074001d441c4030111540400502800e4031907070403d44a0340c00208036024185028118109000300014240246440080c04411910030765650443c6802c980050108a000c0c0306500b013071600690f00d001400602012944201c000211110001094002c1c1400b51012042d0240d0f03a1004005000c5e1442c1406480c040407002e10103825042c99010f00280b401504805205038a0207981c030400d000340c00d12062001150361440e02c4c0d44402c0d0203180500310b0240300101607800d846005141e00950354104001c0042d00c0d45a0b1049015038041c0c640e0b1003003401d00708101a65a1010b03588c442d80030803d49600c3c040e408819101c3c44030400140003280c49165281c0004200407080c0704501600c481c0081041b5007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 592271187 1250 592269937 592269947
    0xa033519090c1409130b041707051507142a151807140118030c120204050109020c0727020406031416021009060e03040314060714070303020f1c020901 66
    0x246583c103407007074041d81c50841443c840d00001100041c2c0141720701c4010a05105050886042c030300e800b00401c47da0380e03480e07140580c0e42d10380c245078007441c15004c4004140000d00c1404580003081d00c102c130190402420f03d00420511111200080d01e1414050401964007414014140501000b885d46a950f2410702500c49000701442104011500309c91400e02030103080080b1021180000e02c2d140303080b0039101e00007114890fa01c0c3c1015048001600f000203008a51801001c102072094805102c03a907078031a100401d0f4012424506080d400488041c02803040d442170340308050300c402844001c6203d4402c02d6008aa03c0fa420a2000039140c0311003580c4105c41c5188250030038000e41d007003130700c1c00c810300c10007511001c420400303240180e141c0e905079080c03021940201111144690640340c0c1e0b55624170380700c0c025200400403101d00740242000901d205010b040c0c035902500c5c915030781c18900720713440c0c0d002c41c02540303c01d05010200c4010701c0b03840110501e41561600c1e00c81d09100c016078801c2c01800141c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 592272437 1250 592271187 592271219
    0x18020918211201120201121e052401020102160b070c120e2107030b0a0212010905070314040b06060318011b020c0a0f0509040c0503030c0a033519090c 66
    0x13100c0780610320400180d070700024009484d07504000005540b1420030b69800c808800074602ca82c1c4130704101c240140c007154841c4a9200304c030f400d42d030061401d800c4801a400d0740251a580d48440342d0f11603545022410402c2803a0348425980ba1004680510f50f44800104d040d1140000000c1d255810425031030038014102c4c1d0015150060300d5003840d039884420ba940700301030b000041c45041d211001ca080d699080e0180c0ba4030684581200000d0f41e102e0102c0070080404840301c600080c203000410b4458104080840c0c040e03a00b101401c002551288240941640003808111141000a4401d09954000e129000800c82040455076104403070100003480d03c1d00c0014003900c112243d0a04012680100c010482242d20079a4003d2155071030b410104007840035540030ba0b41500002070007003072600c40072410001c0c46211b45c880f8190314002c0c4010b0030040e03042408040b0021540700352103030803215480d5143ea01c04606881419951440410181500c49100085078030340c0901401340014030350318207007407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 592273687 1250 592272437 592272449
    0x5060f1c0b13081b190302030904060b030105011704020109051512011e030f15020a2703150f09080408030d0e0a050c09072c0418020918211201 63
    0x9811400c03d0301d0f81800751007506290b41e540080c80403180c0180c0b038180110350340c0c9040b03410700c000c4010712400e002e5141da01500c00d4070701c15842c0000104080b451101501d06071101a91000c582c404104079881850101801c140e05100045500041690321010301080c42c07594007007100e4642c400340501281980041c0c00c280880d050f240e841508502c2040303941002c898000420f224a448103080c0901052551032505a5a50000035000e20303d13a0070114480c048800c8405a00c041400030780940c0b100089800010516a1840f0302504201c5164011156001c4406000600c1c401b06544401307242d032080c1d1041c03600e50030200d60040e00810600c0756a003000d0001002d400841d000740d54032602e07082c0c85090507204601000c040b0741000e118038041e030100400f00742d1072001e50700d100e9240c804c1151503840c0ea030b00c140d0400c0400100085201d51038914981d0150800006031103000e84090411600d00300c001d40c610030b581280d01401001e2aa218121905003d0a40d1b00c03048032880090030300b0160021 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 592274937 1250 592273687 592273711
    0x9030210080714090103020c03120108070b1809191b2304030b2802040e060402180f040209180a0e0f1c031b0e0310060b0301030605060f1c0b 62
    0x41c003a500403503c50703800baa422100701d0360384c014040141c0083c000d070380c403190240c400860b10f00c01c12100441a1410390311500f040b9100c03184e4580280031a40314140044142c1d401055501c003250620030350294002c2d12a146240d01c1a84160080d801c4030413008e6180001c51560024490007038001c148040160500c5010500356030142c0a412694031441c40014408411940000e00c09580c0c41c0052076a00c940c114201040d8000e04007a50107901305004003100312503000b011810604c2c0ca4801c0b00c0710b2012004500b502d105c0d80ac000c005c0c0300e108071321189420a030200400c020503903610f50501c0c07034000860140b01c1c44d0b0404c40d034400210381140000c440d06070700511b00350000c0500020300045021441c1c4124010546d46c0c00114003410490f921403091f80d4a07055050360094026011a0385030005404542031800341c01c0c84070054900d81e01c070b0103001400800052000c0350060b000243d000c00c001d800c003800c01820402164030a00102c035094414089400c103d410401400070060b0821103000803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 592276187 1250 592274937 592274941
    0x303140c06040f0501090c0e091b03100b0126010306141b0304050a0b0a0c03110f0a03020c03070804030c0f140a1e080d0f02010609112d07030903021008 67
    0x92140c0c1d030700018101400c01400118500e0820509404c0040310b5540031003d0350204d5510f030020000f8000c191200c0c3d0040c042c0300c1072600c1c0d02d10b2110300030ba07210701e004009050988504440900030660501407904114401008040203440d200003003610583e030000041d419803540c10070740100d0710380d8120503500d400328405110414814500113001480300d4101903545c1c0d125407414901d011002c480c000c200000c0700042095805c0030368080075a4256a840c140007424103802c07181c43e140320b02c159003450a081441500b90407032083e0f000d402c45c47c03016000c49191015a8a48800079042a882150510a03800e0b0a00c069804101054010f219246030080001e00ca8000216028014050408101020070b903400345044011500001170080109407000300c43c10b07800003400d41d404d5885c203a000d17608100d000110303150f26104180c00c032b507200c0c0c42c41805c0c0440c0140305c0d50804c90f441c3c03801800403217501742201a450f68200402d00284651900782c013542c41c43c03040c8a120741c42290100140400d41003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 592277437 1250 592276187 592276207
    0x150e030a1713030c09050f06040b03070902130806011502120f03011215141501090e0109050c040f0e0a0f090b0105060a0c0503180109050a03050316060204090e0106030314 75
    0x2401e102909a9000c40c58407000c1d100d00d501e04600a03584040c0420303031035000c00122068290b010781c0c0a440590034460007940d07864144015250840c1440b84c055115079410005158641d025180016000d082c03680400da40c3c0307044034948402a040241d6a00120300310054690301005240150f48064502d0340c01d0402d00040003100b030005100e44e00085e00700704c1c007520401000c3c01034071000307004844040050100c5d8403900c0a80400883d01480c2404188104046948c0118141001c8070908201c04546a00b0800a4001f500c030240050b4051102404041131090310400b00501402ca4101c03008818600800488150349106000582071840c0c03000202c081000314803681d040d55000e50b400b0395540e0442004840e5811070304001f50940c0004035181040f000301c3c100b02c0e140c4500c241da40e80949611a0100042500356200017011a44204403050060303e04484c01804c4e54040c3d4001410035a0394121001510203060b4242d69a940d02d403c14004c0540182082501e402044409030502c24421 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 592278687 1250 592277437 592277453
    0x160f0e01080f0a1112012307020f0a140a0212010c080f04030f1823031507020d0e01051615050a111e0d09081b0a0b0105011209050106150e030a 63
    0x3d081310442207550200303501e50001003601e49000400030407081030424940391715035201c0110a240b88003811302041c40d01380300244840c1401400340240c582402c46030380e001030011004030001981d00401d07000c4400350381d450400c0c44601190710004550481d1441c00100040e2004081000c5880071400307200100794050300084040c280790600070540c1400e110f00c0603100381d180c0d2100c92112060b0603214502480007110301103000058040742c1c400c014030300c086561114121030074001603200000b002402e900c1124610070109043c14420302d0100400c0800d4040410a0b030240c5884004207039241e1151a144103c1340c2c40028804200072807200182014081d10606040c40c10150342481450390404005040791780050401108001c2d00301c813490a8001c60b004480d81c0130700f01c09080480345482002041980005a000342e03c9043d980c245001503e8422404001055042d9107a80035800140f0911481025180c41040342041c07108201c0000c1852000140c514082d401103140c2c940010340d02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 592279937 1250 592278687 592278703
    0x20423160c0b0901060e1009050c03040803060d08120f150109030c15090b070501091a090c060d09020d051606181530050c0304170309160f0e01080f 65
    0x88424582d89803100c3e001c0c240035200a40005045140401c188510455007240303903402c40700380110a00441d50348880c0810180000c0313401500350f0300304000084092030204512203c0e507200d0641c60f0709100503030390b1020f0511021140e40e40c40035100400e011fa02034508088410b50701d02441c0001030541117507144515840700307114011380810060343d010442c90140c00044098145108a55252906402d0041c06840c0c201d606940320400012231b040c60102c00c1d040144141c1c0c0250080c00650100410700c04542c2c030030108020541c1e034503103540b0b0041e070310000c00d0f48009000b07000070403e01c0c0756100d00f050342c502c0540c013200500991804a44110201d001e004d002c03641d51402e401d050010031041500c8083c8480400d5001000380d4448a8074200480d0040918081e44c000030030227070f5540c000c0d80380940720030756001e0400340041c000c10290090384802035134001206401c2d501d000e00503070610020b00c5c00329000141200309080040c011000500c2d041801050903100402818100d40c4641d070719a6a1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 592281187 1250 592279937 592279943
    0x20c0103020d1e091b1d0402130216060c0e0d1e0807030504080706111b04150e0a0b040c08150406170a05010b010810051309020423160c 60
    0xc207400302c0c00c41d01070b8080a030340f0083d03c64880344a000b00548500800d44240200c880035606511155a1004581000d09503400d031000020010109103c25446c42001031040340e2111718802a15011183d90001e80401050f001c40702499140d40d2401d035054070f0054100c44100803481004062590703071015107195050700800c0c00302a00f1201e80c041501c104007101c005d001030701c00007450020903038014010411175a803107044d075201503110902150f240030307000d00e00c25955000d02d40781d4a41c1c031004030b40c807256808000d2000911880000814040340015401882c820007584200541100c00740a10581c3c032508a40c2000040840740c0041c000381e0014043c00b1142d034400c08c0d4101241c9469009901a00141e52003810a035082203c6650762040303650200c0f001e5091a92003021540030302d5400c0d01440f4115030500c00c81c0d05150601900d00c00685107180c445464425400250300d55102d00300320090007403a074400302d2030032803880301c0d40c000302411f8416000d502d900c600c6101540300c0b401035900c0354 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 592282437 1250 592281187 592281191
    0x5040b0c0304031704090614060403110111070f09052505070f0b0423070b0d09030201150308070c080a030512040503091509040c020c09060f180708180a0201020c0103 73
    0x4500102140745000b00d4000500054101400c032030403d079071102074401c44180c00001e2014a44a01034820381d05c94072440b940e0049001d000a0001440c624164030400340185070005140c0024100140380c08130a0344102070780d049040701400503410314019640d1200490966000144221113504e44e804c088582038020040086007650030444060141c0742c2c0d494105140108d03600b864181030300380040720100d48111704c03080420309100c40c0000c03034001c08944070070450508010b0010501d501402c040b0104904556079018000d040202c50050360010714001e401441d00d500551600c128949902d403c440c8003640104c80c0d8200003941300302224810003500c00700c014603849601d00285036000701c0c0c100d103500c01103082d40403d6264050700030300b1540314100c41c10301400d2401481641c6a0800414003030700000b400000a040c1e06000203d489040c1006d08901d002056108110074080c600381c66050001c0ca001003842054846642a11644038051001d40b00c11104e40d40040d54079100092114103040e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 592283687 1250 592282437 592282447
    0xf01080702120c0714030d0e01140702090a050105120f0606010c030c020612070f0306080a0b09070e0708060301060b040e061e030a0809090108070e430801060f05040b 73
    0x180c401c1c40100c24106180503407a444050385a03c0940743c803018043c1d9003812500030a10740b401c3c500000c860b10601e901c1c1e16100c2c03c01040c0300c0111003d02001030a48842c1c001041a40f005856103840c0c00d101d1603410b4000581c41d41000104031450800c0c1d00c3c81000c40d40b251341025181e404c041040b54020000342007039440903075145402c0d51011400780f0080e50200c004900c01c400c2d2000c103490f01d4031807000d50350345404076143c09001f0b4003141e966000302c01042d0302070300b03200e0001003000c02e010350001520402c46004603652890200008012100b62001400c0d0a080c0729050609010b250f01410031000380500f41420b14a8807201b0580041c6a14403403c881024108894603251400b0302a01c8007406690030742640341003004031030b400110014007034014070000050580700071605109071104080ba0441e10b031203124001100301c1401071485103601030102c04e00c0b4010081c820008101e03080080d0b0000700c804020002d000c2080503406542408024180d070869580e016049505407908413120903111 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 592284937 1250 592283687 592283701
    0x5010c0c05060f1302150306010806040e0a03080c120103050a0b010608150607021f052206020d080a02091008060306100b03010b1c14191a09181c021b0f0108 69
    0x3c4c085414011307412958074401e04004c0c0d01400015880380780e00383c0303400e64983c444a0038003045604182190340ba81d0003003524040041d00c1150400d80205140300b0440c100802024410025070013a0300845031540402a85020842c02d849d045004000d1820304400c18a00541854215440d507103d15204903000100e0314115542c04278160341e0704c0d12841061180001e1424090402d50022003d510105200040c2c582d03051082c0c00401c1c00d444555000e001044000d10b004c1c1c45144029098010340b903000c0c4a005070070f454100600401000690b00c0f440c00d41091401d1506181001d00b0340d094100e0950001c2c0801100d403000c6034112204034a1540e500c441301081008003c03409542816064102202c0c3c07980490140c002703a010b050078104801e48408a09031b001c0441d0700e0040c02480308584d10122903074500e401d03800e0f00c2d440060001d040b004402c01001d12420894400c2e0044000c0c1c84c03902d40e0900e05981080010341a560740c4041803180e02850001400851a445a060401114000203020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 592286187 1250 592284937 592284961
    0xf160215010905010f0909020a030206070c0e10090f020306010c080306040225060b01050a02070501200a0303050a06050d020a15030e030f0403030e09070507020909190f05010c0c05060f 81
    0x40c0c942064401650311006100081c050a01c101412081240c4001c941d070a0a40700e002c038060f50003814000024695803e01c005e42c0c004840a50307641d90111400240c19055850447c420820071124441c03543c00d2105210485100c080c001f131a5510502c100034081e60400013070014544c100015a46a036161030014004e44101d1041c80e42010242c402c1e03035503080d05020110301c800e1040a05103c000003038001160176005003040c007001640168410481c0d5405000340338003480e00307002102c2e5118041285203140034414101100044d5880c4200101c5003054410b50000d0003040318904a1b108050b0001800302c03405010301e20001c201c402c950a5041d011f9400000e100074001c040d00c1e00c680e8909a1220b55420a00c400d90101d200c10560801c54a0a580203500c0395000743c0300c0c41c1c20000765030284503004800400d844850321503000480c2e0118103070004900340074850320b90108051000c0c5089401c0d03468481c070740e505104103080300c50b000a2000c40c6a0754007110845038049141d54522140e11 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 592287437 1250 592286187 592286203
    0xd020f0402070308160f05030a090c09050c030403080a06080d0e06040906030b0109050f01060903080904090501062309060306161403101403120d11040504020f09090a050f1602 77
    0x980329100154210405411201141c498840b0f45610781c0754503a0f608040d920441000c10380000540d04000042d605c885550020500a00804c2035410f056140d0000c60b081741c0e002e5a0400084001000700010541d0003081e040c2e00402908082c00254a041140ea0341c91780021403480a00010f92402e19580e03d900061b28000c120008042c8046949d1f802d1012a98100380940165107051100244101c2240c5140310304881e0503507100c0c407503a031554942042c1038018140c5d81d94403507220340b08a408560240220405440788480941c41c6008512035a0308100400c078046004a03915010010b4079903021443e958461080d040148599602d00d800300d07040010f841e050603188401006014015456184003000d84481503441a407000d40901016650344241880000540c410480d09400f294030b90480d28181100b041d841d03003030a403104001410703070700104a800c0720101d0100d07460000c0d180c0030765080c0e08402c0c2100c08200341d00b05610700f1a8205001420500a150100c0c113440c5418400c0110352 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 592288687 1250 592287437 592287439
    0x5150a031e08161430030c13080705010e0102010b0303030a020f19210515060c030904020301120506010f23010504050603040c260a0b060406030c030609050d08010e060d020f 76
    0x1221080750301e000c2d6260360804601078000d1064126200c0c3d09088030203080d95074070f03401d05504001c40005c5400542e960004140d0000c01906014900320180c900d1103103c0500b080c0c101500850b41041d000610b1b80c0a2a20440e04580c1091035a1246440220841e03400c000303904000b51f542c038206d00c1040643d109401079845030581510000103030a500450020384a00c6100102e0761412044003a88180e4034290350501e5109003070211018149840d200400b06c003600101528180b590710000602260400d03880003241d00c0f0402d078020100201445070602405485018150050621072000b02281d01d04d0b5021194480800058516070300440660300101401002980d41e46418581184803004a100305500d54000c010300030b503209034128070001005401001888010070b04d8880c1c0525034006400150841d0780d6500c0030010440b19400304011b140075080104100c800c0f8500145032101794920f210400080ca0010700111503401001030304003008071508420322203e0b00000c1d41c07180500880c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 592289937 1250 592288687 592288717
    0x30604051b0d020901032d0506011812053c03040e041412040b310605130e0103022d06031302010311070308060d14010f05150a031e08 59
    0x350000015400402d8201000c5c4c0c2c4c144245c0c50156047e0a03009000d4240141640c280d800100c1407048030342c4600c0c0d1041c03051401c40e0380f038211105030ac8090703410345c5c0120040d8210031803840d0500404100e050003010310f2503c2c0f049851184c0b48030f8062190703860001e01160710100c0160350a0001001980c02030001c004018401303040038074100e00c5907650340114200ea8001d80c6650170128008000340c5003100d0100460610708a90324612608120944441c0c540d5610312800e000881a412039040c0007a0102e44c403425510303004034440110565069001780055003800f0f00600050312070400c04070395508800c4400344441080c000208100325442290340c0c010002208002910120980c0c17030030803038000e89003005144d0300c041c81112035100d41c3e01d018011a12003000300b5441d041c410104050349005011800c0c00c446669492403d540050142c02d1407961560203000788504220090030408074119800342145186544034012000c42c90120580c800c40040e41c41c1c00d000742c078000c4034100041c0003c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 592291187 1250 592289937 592289947
    0x20907090815041101171b04030804261605090405100e100c020c09180f160609050102151b0c070b0c0c06030103260c0303040308070e010311030604051b 67
    0x3000b44072000f12825203000c18a0900003210394003c104440500320f2455040d00d05503980c045201040c0492842c41510305410400000858030b2000908013401024804410110000305140231f060544c91540186030081640401101100e45c2e51608403003042d94000c42c2555503003040c5040420100707007240e403a801c5c03040c1c081c0240c0380411060100265420308114110242100326a184407240403c1d800195072000300e0500329000b054802074004040c11181010b107508006828a11902c0c03082c04110304a50081c0b2a45030024004006040c0a100a00c0c40c0000300c428965801000b412990050b91a611010244140c5038101c80036500700c0e000700e400e02941c80403952110b0340300c04150441c0e8040c0035a1042d2a143c500d048904884e00444c003e201c0446c5050b000502c5c0c1803140c464034840781d04011611001c8014809544194083c1d04c403014946803540300941180130080c00e1604051418002040300401081070326000391050b20001000c0c2e035402c0d440141d000340d103660703508240d2011603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 592292437 1250 592291187 592291213
    0xf150d050a021b06041b0e0a321603050c0a0c0219030503041e0303090e07051201030501140702011806110d3e070b13020907051b0304120209070908 65
    0x3a045000b01d101720030403981811b128001d800140301c00c2c003c80e003514007440085902000c0b160841c00048080321052540d0340860403c11030940920b4201d110302d80821010007450300d002524032040c205587c00e0500061502480300f0b03104ac0720b84a1450203002d2180441d2081d51641c00c0b00b04001c4144c645000c2c0c4583d141d060140e600d4001d841071071481c00c0700041c1606031071180d8000004596040c3c85100c3c4803400d144028906143c0140801d003046400d12040400001480c509402540107000029403100d00108444206000820120075a814502c00356089a030045141000a8108070f00180301071030213490140c0c500c640c040d0811010f00341001c1e80e0308401303034800402082c94656500f03004403000c007190b1601d02c80310440318803807400240200c0303000c00d01081c2d04503400310680641e071811003101e0b0300203508508213452100004401044a03042c84004c2e48810540c4203911005606151502410046030003035040020b014105480200d0f8a29000e2011200505100401c2d20090f00c1614 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 592293687 1250 592292437 592292443
    0x60e0f0c030c030a050d080901020903060117010b0114250b0405010e0d0f020604110303070c0b09010f080105060901110f011803171006260a02090f150d050a021b 71
    0x100c850300c80d00840300e0040c01c920300051041d00c10b542c86000340060004a0700242d994600c020030070f46031550200002080741e5000c1c0031450103030404c42d40301100c640801003400d003100c00c4d48200505020f0200507401000b66098161035080d104050713003d41d040c00204c0c88051010710a0001003d0f1000701051000700101074006402d90a1080201d0f070841464590848a08201c03402d06005a00981c0104021844c01002c04d510303100c016080740d180159591302c0480022035035110201056002c503048946691061205800d49006e1a20400c9541071000050141c403803240c049040c822400b10000d070210084c00300311400702031f4130001c006581100e4000407400c02d0703e00e011800228861140800c50303021000550040005040c00c540791401e00d40e00740c4071000c183c40c5c56a0300810b4070b40c0304a202100c41d25041d1240b8000d07103000d611523090340144083c96001c80c50051081d02c0c1d04002640002d0341d80103490341101820000b18581d16106a000f0083c894000d600000e1100142110f02c003403000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 592294937 1250 592293687 592293703
    0x903170909070c0305030f180307060c1d0f060702011b1506090507080a05040305090a18110405060703050702061e07140610121b0621050f01050d060e0f 67
    0x594684550b50394421044811090840004010820a02c0422803441c000303403165521910307290356954002440d8410074a545c22203401119800d446001080f415940034401c0c56003001c1025a0710100c124100001e21204481c07014640601c4c8081038903810742e813189003007d18040c1864114101f03007840e41800c00300d03969031640003042d4600f0312100003018651480b40c075200c1c008517074070070105454941d140ca000c1d00010304190104102480301017120b95440003100d0040c6110300c140024040f00c0b55a100a8500000c205803001206100c20030a0b520b900b42104c001a0341841d004d0303a145518030000746203016150414841c64086080400281d0700c1400074025180201c200f440050324400100350385810072960b0714400c52030020200715072190710462042c0d0034400c40080500c4070020000d000414025070048000480030881c07092101d42903400c0707a0703902c168044244142c1c5011095a1003101061003514002c64004c001d010512040c0e0b40815281d281b02002d4415914040c14019034501030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 592296187 1250 592294937 592294939
    0xd0309051618050906010f030f060b031002040302040e0f030a05131511010510080304050f040f0906050403091a030612150c040f08010608060c070201021e100507032a09031709 77
    0x83d15011609403400080da40f4103d0300801d02025803a400d5039281450302c90b4508080780c2c115242c0420303e410707640601109080c03903817501005844624600400c4246c4014095181300c41d0052034002c680310101100b15840d0541d1410030a40d660001c80342000500001d0303112047c1c030000030040324404c0c3d030712030380003020b2004540c000c0c003813a250a0b00c0c40c140312109205403070059004020401503030038003580c801c0602e500140000344d405600700660f019200b80c030f0004c4030a43c2d0342d4002c100030990080c0c11a1b01038102d441c41c50303132413131707000486055140700c0500030070310612810500c61102101042032004800200413f07120905012801500a80044c0204c0c01a210511000700e440001407142e80100c620a0b0010700d800d40b103494010183d98400041039045004070444109034030b00b05840d0381342c680340c1c1d9030082c4420203103012180c044441c040c200c0c50030942002c10f200c15103042c2202007a50400d0303500c0004490307121140159580c100d2a8401440d8803000917580300c80000020180060303201c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 592297437 1250 592296187 592296191
    0x2102030f06010816030b0303040504050c2a030a3b090a020c031e0c03161a1302091008120c010b030c1003050408040509011403010b120d0309051618 65
    0x880c0700c01542d000b2011140c1c10b12558900c22010402442a088004092000760030b40b45070503103078408601907540031030700e40450340c0c030015a5034401640720303805410b0350200c1c49000c0c4c040d07100c580001d500c80c842d000c006010000302c01804440c280340840301c2c009026900d402c801030010715515031a0b0426003000075612455209000908e9044c2c0340c021610300c0700039100075502d420621030b40d4000c0704c00380c40c1e035103081800c081c410290900410801450074007400c0c0d8041240c0000c0c4d18041c40c60ac2c201e41d40d203c8500c110441802204040140300d0502b26a0464201403559910030307803841400401e90209015114880390701c00940b00c107100620310940e00074002c0c401110071000b8190780b4402500c419401141800100000c01c1c4a0350140703411a01c510a41480c0c0340e50b54001496030300080e0005417004094400b01c003c03600d424030a680da003000a1b505604402c1c4c80b0b840d8640c403094003003d01810315848440c81010008140711049001190080c05c02d401c54891091884084902c20b18040543c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 592298687 1250 592297437 592297441
    0xf0402270609012106030c0605040e010b070804060e0d051902091e011a0904050406020406031407050f0a2003090a0603050f07051c061e1208090103020a2102030f 71
    0x1060001c210307a180700301a1101c3d6050132403540b9610300e02da40c280d10740365041c2d84c900740400050710b0309010b10000d148580e40c0c01e0300c69060481004ca2944181e0240c2417201040120400050034803040d2022503445081c03c0400501a101003a04600d1050000345030380030b4007101c10460074a4440c82501c5d14003c2d90500441d40ea5242800307888074414507240c1000400b60010892800403000c48a40385228160b0181026030798008181030764400c7d1801c440d010340204080c015203078140301d21800f04108510004850400395001b828602c40c1c1c21504289074400a00e81e0002e9000d5501c1c158050b42d900b1000381c23a00c0c11a0179594580d00b1100d5070503c180c108030b0340021907a11901866020341e415110255190300e911000303540c81c1e030101c0304400d0001c03a106c22041e0000000d200c1d100003044c0794185600002d00c0b1084960640d98141c20000c0c1295070400c120000c201080192a60802c083c03d006a1b1a069218140c13021245d4001000d0103c641c00090a120720040d0042c0d030040701e81d00a00b14090f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 592299937 1250 592298687 592298689
    0x121401090f0c050705280c0303031a0409020a0e070302040521120309060621061501030e0f060408070c0b07030e0109060306080c0405070306080d020a0b0703290f040227 74
    0x41c0c490804c0c0901503038455904001d40e0140d5014451910304000c00c08440e2111566481640d40f010354000e1b00441e42e9001c030810325003800110400c9070007088508020303d103119400904201c01030700601e10790032095800644480e010b581124041c0030000c1203080040103903680c10400352b000241d480f4071030051416001c803005240c42901e000345800c1c2c000e49241d54a62051041244104845200116204082041100051061a001d1203403e8045482922600d00240a960300301118810907840301d9070502000c83c0c0880c507181c0080e48110760035a1358800303090009804c600e40d004111913200001c1c0c620101500102d00c261030040a030ae859020903502d16040c1c049400038828009a07070880303814a1038078500390b800107501c03c0d01d905000414039150200c1600c0d1920141042015034458610301d8140b000070f0b03000d140c0c000d41c0c616080c44040e0009028240205c1101881007002d00c940550703185540c4c0d8003580d5580180060411511400241030010b0032050000291042c401d50950305c00301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 592301187 1250 592299937 592299947
    0x506150f0607080f0702060a03140106020304060e011d06030f1f0f0b0c2d0601090203010b0a0f02010e162102100e010e1302070b0f070f121401090f0c 66
    0x100010710a600b0400c2030b4407105050f5002d40112401264104000c42c0140d4460340689400708007940c0001e00322146280852480d401a0001c20640d81b050104000040d4001e88c1c145e201030003031814004403000c0c0c20118240304246150380707a001002008020003842c4e0410268820000112094168101a402c03900030f0303601030050340040c8807200c20501c44117040c0c1c0300411965503580c007107440c00703102c80f02080c8032201c03c10160b9036264503600d03842c1c3c40d180007000030078090251100110710395454102024060720a081e0040240040e8440da03504c428002c0d031040741480248415551044071032284034401044a0280d6554841900c480c100c0c01d071b4003958044402d0350301800501440d207280506441c0c0e400d49021060401820035004800c0f40c0304c00c1e00410349818050f0000d6104d031600c0c030f0002c1180714014480c0310070b030b02e00c0c0c01000207944d88982501540302d610700f04121000345441c2a01c001c0d180700110011a003403014000110621a13a2015a2295030280c081002d1440040100c031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 592302437 1250 592301187 592301209
    0x30305090a12031b02130e1f050f04021203042d120506072f010b090f0702060f070905060c070f05030c0906060f04050904030e04061a0d0b06040b07050615 68
    0x100140c880900d500350b0b1841303c83c0131151640020145c160914000380e050003501e10b100291882d5801c50382000d80040d558003c0c0e078528108260081c029031a22840754901d03c01d005001900c16620329015120403403040c400c56029080c400c062a8422904c001141c2d2903d600b08001080c14842800003d811922440e000100960000c080e00c100e458201048406078011004a0f00f070381c0c04c146880ca030440c60448604844200100085904030f190303c1044518400141824060050401089000f0354007080c2164440040f10061076152140c4004603108072031034002d01d802c41800114040c3c503410006240c1e0880b4402d1444142c1c01d0344030300a240e240d2259070026504100c120022a6161404901500c0c400a031100e80030b091960b1200000c0c4001070580d0160003041c08400c2416031070425014804c0030781406e003e000c110351410130014a843c400c02d00d124044c1540e0b08160701140e6510b400700d0b4020300403006201c2c0c407170a050400c252505011340303c5080c2200c0c0345040c61001d0404800e210703 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 592303687 1250 592302437 592302443
    0xb090703060312180902070506012412050a181103012a0c02030a06020a050d05101d04141c1706150d020403150c0e010309261201030305090a12 63
    0x20031000a1a0f041d10b02400b4039203410361040c0202c0000c034002095102410a1500420007022294035000d00b000d00b045035592105400d42d1030308400d0300e605070840d01d0042001045c583c000f625aa51440400040125070500322510324820950313001d009047d0204171282030300f10001c110050103000f40007180c100c20307071502402120003505101460300516854445034000380a1304c080a205a83d144100da00000b40c80c00442c50118102040d080584100e9912a10225802001c0c42c20640c40f501003d00d620b480e5164400108009800c0002a190b03180d4014003030000c8502006a2502840e054005011300e100000c068002e180051212615250300503a00508909201400d5080800c1c4d141d02c20801204080e800b0400040040c0e19003001c000c1c01d00030607000142507010b01034010700769160004140e04050600c8420710101d48490016040480452040c0c0e040d0500c484148019004280e25201d031980014000010300da0024024a1030381c100329a031008503038950751292943c144442000e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 592304937 1250 592303687 592303703
    0x180212040c090c0c2102030c1203070906230f2b1404020a03020d030908060702151317090312030a09050609030a020307032016081002070503090915030d030b0907030603 74
    0x5c5194007411440d80c0102d440c09105603480d00500300394491400034012100e40c15400000200081660301402d020081c0c00d980c44c00712500300c85006c4100c00b800300356030040703080000081c00075900000c10003190001812000310801c81c650800300d501c40038000380c50510620341003540e0102c0d103034003c60406109170340c000c108000395030070b540074040e03c00c072102d104a0034006c42c4a07001c2a10f220800465100301c13520b9004050b15450400400358110014007402c0707036007600300c01c07640004080455400e600d02c0203100d00e44d00c078034408002038500340d00e00402d0b0741d001800000b0b02080251940060349240c0c01a0100e81c1d2688545c0e621035034903c100301e90840181c005122540c0001d00c980000004e07000c3c0d00c2c0d4000c1d9003100109510b0b0620f543d42150070b000040d45581080172400900c032080806010703000840c1082016242d4585920601441512840a280000c8d801d24a24080c00c0004030020707007101c081c000101405001800102c402c9842030070b2020003e25118071078050382d000e980d408009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 592306187 1250 592304937 592304963
    0x1090902091b0417030721020309041a040c03020405041109100309030e0901271a0f13060308070c0b070f0b04020a0302060a0207140a030201020601180212040c090c0c 73
    0x422404070b035036005003142030004201c00034600c0c00c9030f04445440c000c003c002e103540340f91038503000400e9580045001030f44c2818440b411345840d004402d0f50041c00c3c003914041400c0c451902c4500c1804010718001e60310524040c0c506d85510380c10343c00f40042c3d42c0141c6040080380040d02044109005c6c455142d41c0c004281e0b01c1c420941482a00b1100150303221b41081e003150800300c40018201c0600360090307442e421a0600c00801d8540148031020010402c5800300b00c13130700c1e888107580b2080c24031102850080d64180002d40d81a200c05603084d4072800b40038000c000d45926860700b903100350700500003030355490841ca001140000c00c040c200d0306141c1d484a1502d135544419500d22a450400410903603005101c460000096150710b0300170f25404c4056405005d40505010f001c05034010000c62140c0126101d00003800141d8000a5090640314084001d40440d441498000080e00c01c0701400030440c00c04c58280000c12811040c0c074010748440a8040c0014925560220391040403030b5005401d406070418 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 592307437 1250 592306187 592306201
    0xf070e060a030215090a0303210c0203040909110d05161508271e0114010f03080f190306090506060309060402040506033a050307050f0f04051f080109090209 69
    0x81d2104a0444d072100e00d03828000400c0024041400a50040d808038440b10901032080e0525112107440c6480c010040010710070f8580c00a6a82c000c0d0700502501c169101c18010900c280040d05141d03000e8002c02041031015030745030240d120b208034008890034007101031020508040b050510b80c3c61407015a20b00c0c0300355407481144212000358601201d80303043c3d10001c0203c8000c05204c407049507020388000b290804c242050303407421038004100c01e00030100108018044a0a80304924044a4110001688404485c0c40b60f222505c540c0e00c00000c2901d00281800590307425801c01c00441c1c2507008100100e03524101801400d20044400f0085a0081000240113140076401207410901c003604440b460048404151034000b80d58604080b42042240185008400114002c3c042c5034039103002c50440c100024082c00343d0248403070310f08038101c000c144246079088150660300141002051201003c50311011a480d001491f45a40001002c80d030011450340001d02554074401d03400341660050f41e6900f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 592308687 1250 592307437 592307449
    0x9110c060c1602030303040f1104090b040f05010608060f01060f080402061b12131701090309060e0112050406050916080a03080a06090615110712030809070b04080f070e060a0302 78
    0x296034044560b4601080101580b01000910b00c158481c0074180c10405041c24005e4051214002c450310541c140300880c4006621144985d4000c0c0e03104503400c1d800035207484c00da8007402c0550010b070b20a2040800f04440c10464108240c121112a1140c00980c100030800700c0c0d080a0441d03000e074014504010510050380404202c40c90305500c0c81c151540c80380d005541507041d9011000080380b06080c0c3e1014080c004002c0206c00d803d40000c0f0080244416554018041c00e01612070311007405a032400501e16640100321240b0014a41c035800c000601c0c11749000c10003010107603000d003103070b101e0907401e89004125820b0b240141ca407170fa0b0081000382555a0300701c0d5a60f00040ca00c0801c26120b950000b4100304501608010b0f146d0f100c060f00d42c909100704010721102c2446440c0042ea40510020840c1c0ca41c0c21051082e099007601d000ca001ea51201301661410801e68050b0f614004000350006400d040415200100d20503102a01c2000d540d130311207451121820748405500065860b01080186022 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 592309937 1250 592308687 592308697
    0x1030305131502100f14061306030602210702070605040b18030d051e19080603030c06090601080f0f07050d020d1707020f06070c0e1801110409110c060c 67
    0x240100c0e07445499070100e40503499041da0280c007680c0102e000c40c8980411303000d19508080d40b54820496200001c0107203500440107050070380240300c107100e800400240781c1c20900145410035010755039a0f001c0140840190700302400480003501d45404190681e02c0442c01c90200c035160703524603045c80e0030b0901a542651040224110141c140a50300580741c4081c08055004100c80c0c2350240c03246038010191031807140c0b03645a0240c0b484104040c903041c4800c2002040140e80341d1070581e040d982c40d031001c01d1441c49605469044c81c801e0700c04008034810b000405c18180da01c0f00081c0d444210010454681e41c400c00c4c2441440c54001842c28403140c20510100c2d00349500007404120250031a8894242d001a1050007440d00000056581d09604001a42c607030960700c140c541600e4400962141c24030301d0206e002d04c400d015101c5000c5441124114006500865064005c1214080c4002d40311000e40c070500c2500e03400390424180076141c42c814400d9030300941c00d035000780030250780d041c50700c104035480 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 592311187 1250 592309937 592309957
    0x50a150f03180203160306110703020703060b040f0203040f1509020d14070b0d290f01080402011103040e0411030304060807110a080f09040e0607050a140408011b0e150301030305 78
    0x507002c0c4a4001d40e07000c21202c10000040c100d0b040c1c40c00d0540c03c00314140d562042c3c0d0300440c46020072140c2e0010307500240784000c89802c0600001c80030003682c000790240609146c0c005a060000c820b0001f40f0541e00ea08043c128410040c8640100302c40388070740182c8075403800180d480790782c4040c0360012441c424441341840e550700090b5403507907480d02001007240e00b0003095055100e40e1001e51194520b0500d91000441104140f510480e80078403001561a1041c4064907040104030f0010908690064040002c20144401500d4680b40c40e40d0890102440c1114240c0358600c0e0b070f4441d90668240441150242c5440d41c2d15081103644509054413480e0440030b0200151040d00e400e0801b00328000c01401006a00c50300039942d500e03d1100304000c0d00c0c0e900e0400d05168204005002816402104652403528142405024258010a02c40303da0103903500038109035003454400419a011a00100000c0c10a600c540300c01d2242d101c14000013040c154580c074091f000400052011901900103010107100c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 592312437 1250 592311187 592311221
    0x402070602190f090501020c130c0c021c0b220f140a1109060111031e042408090d020705040b12010e0f0f030c07050f15070804050a150f03 61
    0xc0c400840840302c140d040e10100064900d80c0d0f40310015510840c0d01e00144024030043c800580214001100c1d0740d00c0c6c495044004d90340d0800c9800d1580241c440003015a002842a800090340c1c410040400b00c04100c01c40710f00000f0400124071551010306c1402140c10070a00490800c50f40e6108408c1c4d07030303c109050340c007445081071501c1c0f103800c2080358000701c51084d20f007180c244082d00140b0800d43c1c0c01401007410b1111042c0c401c0e01c0f01d01d000041d50b01800c28450900c840c2c508904000069105640028950740300800042054846c1c68031151640c0005507203403400365a40e036000300d803906880c210643c016000320404200c1031920b50808041031100a1915040720310b16041ca600f180d481003a12003064000c031702c0310b250080c0140320042441c00464061450711948040c10341d2200b000e401a14851442408c003054641c03102c00c07555040c21a0440b01c69a034130294103241d10300303400c18072a0900c644941400444da416000c40065140c00c4a6140c4503584000d0f810b00f5405000000302c1d40c3d203101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 592313687 1250 592312437 592312447
    0x1e030b1009060909032c010e0d150b030f070e06270703050601020606010c030c0215270438040e010609021911032d0406020309040b01020106050607020402070602 71
    0xc0d2881064001c0c4646500012103030b2a80c82d02624850350b0800b0240041b09051150003403040c4940d100100840910b0001c8051680b6000a408944040c0024046c036032120320b00410885158807210504004808668411480c010220380e5030b2120301031140003003a20310100d041c0d810010b0710303015030000c04290986019110b001ca1b4144480403146000040d44030030500c2520758060054542140c400e1a10403203144640d100504a0503440600900840b0300302c1108440b40784500c00c2c1d803480c5036a401d0424042d428908001d03e64154842801e00c1249050003604501000c041c1c96110001203420505144811840d8489a41201a0400e0308940c90340e81404402000f8805c0f00701401c6150001a2220011460040707010018142a070501c9200d540000f442c00000003030300c003103ca031204002448028049198076100340c1025207419010045800700c1e03825000320180000c0b540a03202048109241d600490a880785407040da50030107410004d81001d401d0036001081042d024400140c500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 592314937 1250 592313687 592313699
    0x1214090d050a0c1e02040f0528020c0a03080717040c0e060102210d0b0901050102030f0304050304051507050f06060913110a0603090c08030906030f220b07091e030b10 73
    0x80c1c4d0002040b45803542c02c00c208030840c90548140da840e070801e25410801407620f40c4903100b103c032000c1d40c11486035074000d44150042242d50122081c140b80c003000d41d1112151443d001c0d0031071400751a0540410070f800321110a103c1c5841003144296008004650581c1c41c00b044480701140c044c100c2811401121161501c8003114006100e10541c5070071841d6540d047e0f1070700001169039002140d0711504155004002c0c5a03800000e0715084941c500009590762541c1c5852481c40c0300c0d560115400800310801a0740e070f840c64178040d10200340501c0907914a0010484002c0c0c0307a00003220340075404241d00001c03440509128944200c80c5104040e1415044004000110890080d0b0f201a0010780c80314401c00400620104047c01807a04100450801d901c240020320140001004139001c20751100004050040e40003450940c3d03452070960070460142411b1121070000115054000310b0000306000680040882551070740c005071010310650b81d811559034062074100501a11219050070b4408141 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 592316187 1250 592314937 592314953
    0x1a090601060246031d0411030114010c05010c03020d0b090403020d080a060902040e0405160b120a020412150506010c05030f07080c070902040801060b04050612091207031214090d050a0c 81
    0x103c0c1d009807100c18a4810002c503a80d002c071200d0610500447c24400305130060311030320050360b0641d64090340d000680031400004941056810101521541c2000c81e001c2c0000e40541c010000301303134031a50901c460400007040c0005604140c9004006038002501d95102c10305c560300454006e1071102001c207005548248850503604150000360003080780c0024041048810001001d8042000480070400c910b41841c404250041c2c0c0c4840c9003040b5840d0009240c82001c2d81214042c100b20a0341d10718000403070900682c440070141e202440300385000b01003007140d030140b00f010301c030301c1d03404401146048110201c0004a4101a10486a5034010f00c141c0d000d4007402d0101d1380183c2001c1c8401a200c0c1c2c5050100d9080d9502c2d9402519a248104020302035511440100e43c83e10042e05d4881c0c80700e8590486240c03621018149070b0030814808114170042640c00030402102000d481001d000c4d0404456402c1d00c20841940c22401950000050540c01ca01035005011064078a04010400c0100c584840032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 592317437 1250 592316187 592316323
    0x3150e0309270708100b070f1401140903090d080c0102041a070b1006080a180503130e09011802010f0207030807060203190501050604090f091a0906010602 68
    0x800d414a02d52041d80341d02c40420b19a5101e1542e03e00070403603041c454181c028682c01400340d03004240002803030b00240228144500b05603030b84000203803c171090a481d0749008085c4064000120310300030020543c60301000040d103440440042000849030200e035a10989030f03026220207400c55400b808005070751107801d010008007448070b048490f43c132003403442d01e100501402082c9921069900c1001d01c10560321460f86139000340204000280000b6001100d0f00b486481300d4020090322000818a4200c042a182d1a00700c80c04410507207455100c070403c00b0b00f40d61410186203002e604141811004d0740c810041c4038100300d074500558948030b40300d4903461070560109105440c00e6400009000005041d5650180d101044090400c52075041600003081441240700b21003e542d120001c100041c0c1f0380b684040c04083c1c0c0254100f820416412290640450849060410f40264000043c96600200302e50041020003188044c140400b8004017064600600b60f603240300c4078a1500c1c04a4141c1210110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 592318687 1250 592317437 592317469
    0x41040c20030a0206070201090c0e0403170a1a010806090703110f12071704260409061806080d140a031409060901060b070b011401020f03130e1003150e0309 68
    0x9aa5602da21001901d0244058003142c116854850840081350754041d41e04181da204804180c0d10341c40d1400d0489015016070982c44078241041d080c03140b18502c0d5440000c500cdc86450704450b40c06000c50054400305811603005402564000008201c144642e01582e400f0b1b03a68800745082c807009028040c415084081c01c40109001082403045d03c80c2c118174207102c11320381540100301900c0e003644c03001c8503844a00300c00900b0340b02500040e8032101604044d900500f40d000404c100725940d0f00701e148000e00011621141c1c40c0c0c0f500c0000b240002000c2440c0800e5591502c40403a006640c0c06003040c254030002c0c0305000c02d9900c07440c0d00890102e19040310301440e9500010216407c01489240c2151042e80c42a4147d540810134040002e480c0007046044032152507003211424034040050f4105049014900140d000c000741c3d19483c0e000728441e41064802c0c545481c0c1d42c50791280025841c0300010301002d01a01d100f01048017075590907807c82056016404141c0703081920100c003180d07116034100c01e01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 592319937 1250 592318687 592318693
    0x922080306150301050303091e03191202010c09120215040303030f0605030d0e09100509010b0c0705010302041202090601091e140603041e050f0741040c20 68
    0x408650301d00a07242c0807181d04100311080c078552400c0d0000b1b0307a0f031240409803406441451104440d0401782500084440c0b000307000e80d020110301031414003048050480842e08440b84202c2394500510500c11542003c0060303d800c02c44900701a40410307820b0702c240080340e000c0076800d501204180440c000e00011442510089030382081c1440004c2540da40d900014081d50224068000890340840300f44101d08098070103006503120000c455600c421590001754100622000005050480c0002041c2c41240d4900b501c11854540c0011405e03803040f1b1166521603461468001c0241c6050300e05203401180c14100b541e5269520030588181c42c03011108034000183c098010040c0416020b241405c22008030351103403440c642540c13003420780d18104080203003a07801c44800000b004004c010308451064001c00700e844081c0c2c0c5108080030302182e0003d1021070070b80e01c00c8182282d840a4000703600f83d000c40e6290ba61800e034060034480100590740800081119031500c050b8103071000d50b80c42c0f580503820005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 592321187 1250 592319937 592319941
    0x4081c15061b02100c0f02040e0a030807020d1e050d0e010204050112060308070f23030901090b160b060a03080d0501030c0518040206030c09040c08010f1e0509220803 73
    0x4082c066410792160b0070404400c0d208940c00507500c0c10b00d40c1080905074141116807000500b0550000c811130507000350003a00c0c181e00c40a02400000e08a28035521a03a1110101e079250a02242c88074003c211240c04660442c40b100c08454002d401100000c000745001c03801c02054040140030345650b003400b00500e0b5030014081c44103503402142d01c0c221040180d0207005040c80c5984100b101c1c41000006000049030940070010801d5101081a82002501e540983c0700d444001c1c003500c030f030301181c0c02e18042420118000303040b65506060f58031922207040e2284101c149a114208a050001d055540c42030100c50b003c00003a400c032018105a2080300f10014856045180600c004001a000544200348191441c0c01101c1d151000e1603000754141c5840351240c0300c00e0300300c907090300400ba0540e40c01414000401d100a500c5116030b4120392071205800f0301140e44541044100d0001501040181500d94062060742000354002e5045a1804500900305071640e80008030b0000e903103401c40d00002c1c0002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 592322437 1250 592321187 592321199
    0xf070506180105090d1b080c030307080a150b09041a060406050d0b06090307180603021f080708070f0e06040504020f030a0c021b100e030105160201110301060804081c15 74
    0x8030f40341e0700c03000030401016540c1d1451790161000c3d207882e10341100301544081060410108070181c0c2c0c0e018540c1c40c22261682481030019000b1700c0c040b500b0380041854125640541001d0800030310440d00c800f003060f03184c216204d007804050080322500c00195000d56403102c03015102e0320001c0c4000c3c0303032595501c2e8503814011449405e03210b6004416109450900580c11396950100d07044e03084900d154440b821300e0b0503810040f0054040e540c0060f5002c0860b804100208000e05014144a41d003507844105035a1400c400b039a044400b611410002a00401e400030454007800c2c0d402e15a40b80140480d05044daa00e0024090740d2040c070818181c0c800c00720520208100d0ba001d0b844422486e800900110b4603035101c108013800c00318003418403a0303c00103000303c0d2090080203090040030300074009120301c2c6441d9207004403c05084640000661074503221461404040003a281a51110369604900d0348503502e07040700c160409200e8074074001045038a8001035595210304030040d135081e15400c035407d180c10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 592323687 1250 592322437 592322441
    0x40312021806043309150e04060609060f080c031603091202011d03090904060f0917040513060e0f041713030b0603010228020a0f0c050906061903020f0705061801 71
    0x2e0751803503e0084c101a0200030030742001241098a00e050a080c400c01503074a0304444004030b161110743c03c10324106001c115035034040c020800743c80c410748400616111701e05045480d05401c90723006804201c20b001023503500c0c91851440e04804510718001ca08121a500c0c0d100364075240e51b420401513036444240c1c20944075480705900724100024040c0d03003020342100c080768004000400003046182e848103840c1c0043c4c0982e004404058009151201c2040682e01e002001d0f4014041e080c40349c100100b880c94ae050940c041c400640300c0c516201c1c0d001d038a0343d00e2030301d180b10030141c41203a42c2c151818295200500301005000d2100c04141c0148220389141815810503030050034103402640100b00300950240119032499245d092071001c02d030f0010b40440120b0070a03100303810061004121600c008180030003400440140d65085591184586401c8100f100c1ca10a000c01d1030329101c21002400040741c000e0b40541624030242010a1501c0d40d5a80da0504060048609030310486d5250a02d81d94100700b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 592324937 1250 592323687 592323749
    0x51503070501090608043f03050903210a021e0712111c200105060405070207030201020619020403020d0f060509032a0a050d05030411040504031202180604 68
    0x81c01c0241001e1304102005000c500b0040020f0892002d4a08502c441d1050801030b5445481e05c1e1181c0b00742d6407440304040c0410b00040c458030002070030314020646a031004811104c040204010100881d140360614410200700140042c41445d42408804080041c00b00980402c2402c81061559040d007441c02c1c0e0040c80c1510752100401c00c0d0b42d43c80ba440a040041e500c1803030b00301640101d100501000381291403003118036100c0403142c0c280303100c4061020150000707409008220f400b07000707641e5010f00403640c408461102074016407003040412084240e91540b203000312014007001d49056141d402040c48a400440f0440702d19407180641c42c14030585204030b5803c0412076001c0c52408401c8078040c035580145e8034182e0002d500c2c0c540740c10803000007000750580c1658444141c0d000050303100b20103030a80e04122010f44036207004120700040b0345428403585200760781c1074590070800c001041c03d22000390041c032141c10303e2941401481c00c2c0d0390b95640c05403006000e090006025030303171410442c034807203421 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 592326187 1250 592324937 592324939
    0xf0d0909060605040311031c050a0201111914041d090607030902101101090606150210060f0905060f0a1e0915030b0405030d0c05090109170c0f040e010515030705 71
    0x1d8444284500d40d40031003200c0440e0b0f000400d80b400700b02c1d000e001a0900c85824040d108950a440c0340b60000c1d03800c9405030101e0155600200542484240081254810580b50090b15165a40f0b41201c0e140143e00b108100d03410010058249512184000020721010544078040000351040140003201004500e07440b030310902d428481c9801c035501045402110048410034401800f0101d40c5078842503010031403054208405100d200d40d5801070b25400320440000350014001c0314041c2a07002858002e08084400a902c041c00031407810480c80000c0401614403684079080007000c400e1541c0f250141405002150303404000181c3c00c46020280b880c140d0300c140e0b0407504150f03a034600080c2c3d0908080841e0740188100b149a6210319203581548900584048558a40142d202c07495a204d006440a1034082e200c460f41e464540320a108407080800180c0415445078907502514103200b000641080c0c030280c004034405d5407811006080d00c0040714149814902012a0161481c0c01c114107401410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 592327437 1250 592326187 592326191
    0x2d120216051210050702100501090f11120a0504020d0609030801060201050a0e03030609060a081b0f0a0335041e05122a0405130210020f0a03110f0f0d0909 68
    0x524040b010745440007019208501d5a0380c1c8001542680241315203807070f61000c482c00700030540c1c440003083c1c0180032942403d5906d81c43e1034505014014520300f1031700860090b03500800781d41c1d00d2200c400040c141c000d204a0f007145c1100b544000256083c0035020109200741c444886942c10248001d00319080188070441c460f0401c40c4c1d02c1d220343c0c400700459401079010354000c6082d5403000e020a5800703400f91300001407441510801038100381c8405c03580c480003a0485a0b85201090101040b02c1d1641500010b00215401009120a122400320f407000e4100540d41000c060300c002402942e0603001940850700b85000c480b407a424142c0300c10300310000f0f440c04440982d450440395030030700e41d0b511454030a014064501901d00c50108045042c851200740028006e0140b881c3c9420250610740d1400422402000124070740c251701130010544050200300f00004003481c0f030071610b00325242410a0b00eaa00c5a0040186070240d00346c0900c420105030300340c034004100f02c18002d24000c1c1340601c0e07988080d4820b4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 592328687 1250 592327437 592327459
    0x60c080711030319151a0304030201151a0a032a090801110a0f030902060f1b06310b1015050a05040315021204060e1006032d12021605 59
    0x1100c036013600041902d41d9200001c404102c5034120702030b8001900460312050813448000000e000301d03c02035101d1403180d8001d1202d006665040d920a01c110f0048000074075003100b00100705806035000d45200411441d0203d00000410703200300c000048030314543c0c4d8255150007098086034200440d400108040002004500d891000241e0f190184134051402c104c0c9080e10b00e400144030780c1083c0165600140a6980e5800e200300c59403403075110113480c80c45007524054024202d44040341007880f0360582030b24510384d0b0054031210b03511507400c91104c4400c408602101c0c400700d10b0901a01c0e205166858807159502d080400300d16041129114917800c020f010007d005802d944041a5412243d005050304008000381111401070301680041c046400410380401041c000c035600b0800c000840a4103a03084405400c00301021756040c2d020140044056821900e0440007001802610b108500e1050001280c0c2d81d40c0e2000542001480b98011781c0030003421045411a10f84200c01000c00b120441d01d64 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 592329937 1250 592328687 592328701
    0x5010e06090d020f010504080f0304170109030e06130e090d1407030215041a0703090c05040603020901170309030f0c0906010306080a0609050f0f07030b060613090c020109060c0807110303 82
    0xb0b5040020000d02520810300111140d0740100281c1c1e0203486d0900580769005058140c89907690001d02c15200c2c0070042c40710590300c88406120704c0201c40e03010307078421480300c01c8202071180d59800791107002807003c0d04241c0000d03003c04509030503000399201000b038142c03007a005000030404440b03410080c800303003020842100043d400040c071900c07640b4041611a010b075030714207244910703020407480310b40c0561102c402c002d0b1003030741540b00890251144030011041038845060104940c2d690200a411409080050002890180c254541c01089008680c03401039510082400d100700d410003460241d2103100b0600307544c5072248020380d1202c021300e02081420724004150b982d9100704440900041d40d00e00c00300c1c081c40300a006080c40e4044040460300007215815209903140103074407080c0e80c0c0e51070502c00300700c051a09800b101d19005c0420700c54030601d8185054800240045800c40e019507503a16884d00c006036660149540103807080d1182645483c0c250405400709000742d01000854108000300900c0d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 592331187 1250 592329937 592329949
    0x50a050901030b09100f0507201b190810050c0a0903020603070210110918010e0612070e01060c06050601080105150912060a090510020424030f09080405010e0609 71
    0x45039040890f40c01182c03180348185042c400024450008a403c1642c0d9000e030700041d82081c2c0c0113042c19a104c0444900e03840c0c40319a8000e105807401e416070495130340c611381450354406c8690091002007881418080501d0001c0c1c40b81c2a0343e022004c260454200440c0d450118441d4507407045094000601e01b41c2c1c44030f40100302c0c20b12800028450100400844d1226108106c81c24643c03c20080403c00f80319021241c44090b00480f0f8210310441c10382c11070301c0318140030442a904840d0f000804001644a8501b040003c84086500e0032092040c040001000c1c10258103c50003480142c5504e0b00c13171903c50078101d06849004119905000700e20004208a07112009044901c1424412880d1150182030004151a143d40501881803043e4801d0222001e81030740a00f4180f80315004030351801c440c20390b400f0141e00481c4180b100e40403d1020451120800c41400d11302c60466280c00540241c44401c50022070302c0c8080256a1003c02040c144030706c0d42c0143c10300200a9045524908010914000960b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 592332437 1250 592331187 592331189
    0x618090503040b0708090a060305160309050a03050715020a030204150c170d0207060207150e1606140c100c08091b06130e0403080f060121050c130e010807050a050901 73
    0xc62030f00043c0780d000e010180d01603d408040c0213120383d14170b581d140f40080c098441a5250181f5020b800c1c800b000c0340e8003d216001c0306540c80f1002d000401c1c102e84043d01e40d034002c4d4500fa502c80700c2c030340e032250402c032014401480303110702c15280140c42c0d40c2050034205070f0582d00b08100e8180021840a8070119000d40c5042e10f1121074181c00507510500d4907403801c081d004802e001450580049100d10130042c004410121140907000d0030400086410b003850342c0d50b0b10318040d40c551055003c106020f0f031032080b0840d00380390343d000104900d01603003020060b1500088072401418559118100c0c0c848551080025800000c2080200b508101c52480454000307480f0402c20f1260000065244c3c0e1048111007000c000c1031075003d0390b509071602e400d0241c9985402ca0700e4920000927040081c0d210b40c001e15454403d41c56580801844d14042641c8000402c0058807546940f80c00b4400f450714000c03d5003c0501a004420710909194548040940b801c1b03401d800092254110131418025a2a8540d0040c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 592333687 1250 592332437 592332449
    0xf10020a020c0909030c010e100506030d0807050c0102131401080a0b01050405040e0a02090f04050705030307080313020d0212030a02060f04051c030b06070c15020c0102061b09060d061809050304 85
    0x4016440d8482e00c6440c5110343c2030481d042d9420220f00c8e9145c02d0b00070482c0c403030101c004038041c0015602c20003090f1302ca10303800b0088000303c1c1140c0d01140307036240700b1005800d0602c00d00d000140742000c8611516200e000d00d034090011500100300b1600e0950340031101d16000305010320107000c81002030001034514007450003650b000d41c1d940c000418030704c04200300742e080d031607000b03002100d06d82030400b4610b41d5403504840aa8542c49940000aa51700740007046440c46900f01c00158207645501c45c40c0702c0c2440240f0810b9a00c0100704440b80013590b04d4180094941d03101000959440d8003841d006400c00100910f26514040c1c001d00b0000411800306400d6810080d014500019007000c0200760002c4c0a41802283c10000c0842c05408000d180111032003500c200031648110038843e15012a034031558915281d0040c1c00c4180418a142040704001345041042403c040c05c18603460045402d98016003202d41000782c0781c010422126418280ca203541e129603407010f1000075900e440c0c1c0e50b034a100780c2c0326074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 592334937 1250 592333687 592333699
    0x50c011103070b010806090714060f0c010905070902031608040b01030201080403051c0207020406120f060b060d1104050a1e150e040e0a0c060c02030615010309050d020f10020a020c 79
    0x8031030a1a06104032111907902004000c11941c407060040c0d980c1c2800c48101c440b40c80382ca500450580850f41d103015100c3c600400c290324043d40c0965030f4a43c1d40200c82035000c95901c030581c0d00300180044c0010006400c80040058072440c080032540b00d101c140d21240014094900c0074080820f48507030182c1d0540c0d03020300f008940c60b1a03601d021036103032050035000c0154400a944020004045030010725083d8001c54052002503140d840c6900c0461003400002c00c4d4540780c002c0e920010309650003802e60001d004124900f0302810f010061300b95800d544107040d2420780081c0501c610b24007003401c031010b081080600300d0500e000040303ea02d07100d0315008410800341c00e06070400c59140f02d601a90441c00c4041c01c1408428040c01225956100001382120b866225000204a180c400c140000001d90000c0081030580c65005918800301c071200e50650405868904020100b20200403100300030341d43e03a0086c21400c600b44041400e0009a41c3c0000840c0c3c0108003d0300340700d90010f9011600300d012201 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 592336187 1250 592334937 592334957
    0x1a0a05060318190f02010201051b160302032505060903040305250b210c0c07050108340e0603040b0f06010e040608100b03120a0c0309030b04290103050c01 68
    0x1482d1043c0903050003c0c48840f98814410040d0030090703144514801c2c2c0092080d03840b501550701206003a100c042001031010311a10400d0340b180c1c9d00050704280607005a81c64105070110720450114450304c80001c0c0d0b6400746250b01005001c00c80142e20001d04009981018112380d12a52108062401d11200858561580c20340910341c001150080c040701600070741d18410410304a55101007061240c03a0320f4640030011714488124400c035008011103801803d4031a00b021300543e040b02d800b4001e28926002202e075906942605041003084882c40160881c401e8550000144000d5018040e00d001d01018000c0c0030010f5030302d241042e00a81141ca484003d5511200122105081d14a04580c010b00700a00000c0441c8045030880034040070410074800d200384001496a6065100440e00b002002005070300c9405110b900c0c2d102405100307142481c1030719500e44070320f5800703e01590142c03241c10900d8540580400300d00d503100140c0840840d100001e602d551210740d1154007648049043c0010445 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 592337437 1250 592336187 592336231
    0xc0c03030901022e050112030215152404240f080606091c060b0f0109080307170705010c1e03140a0f0b130b0907020a150902060d0f1a0a050603 63
    0x4c0034082c0b02201142c01c00c03203503079902003c6d42e45044070792094000d8080d0842c4014284000e0300030502c07405040c0003d21604054074140020200500c96407a05001c032080d00451000c1d036600203000500300c0d95040d14070300424070b030712007222401c844c44c0c0420b2004076a03464249070b03045040998401030848610303455664102c082903165000c640400c07543c0480250300320412085620098604d6410f440140c0b034050913070300654100449000e40d82e410f038024001031001a01028100a4108107600c10b141004281e0f40c540742983c003856641d50105101e205240300c00001c4030000e0312000d6980c41d05001a88102004205041001d0069821103031a450368000f0384220760005041000050000b9858001d0b407000750008105240b8114403c2100a020481981c400180c0c40d8100e50090841c01d9071000e1032100c100204681101260000303800d020f01468106680b154001c18010300d1310101e00441003120b8895082d0a4602c2140300c1e24581d101809143c440c0001d80b40e101c10740d0700d02c03000c40a038045 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 592338687 1250 592337437 592337503
    0xc0301360f061e0303020a021c08070609030e0f06120903130e01051806060d0c02070e040501020306101407060504020d051c080c0711101202030c0c0c0303090102 71
    0x110108111420408914480300190780224111403854030f504a40400d50102141d041402d480003400591042200401620302007010380b2030011440c5840360804019600c0c1c040039004190280c40e125560400f00d01856040265200e005d001100d0010b2015989070001340c9078000c1101401d50412210000751645104000b05d130000569000f4180c00c00d03580b41c001440044090141c18050449000400f46d202196034803603019904c014102030402010304080001000740c0466401184190303440095a10304012505000718000e000159682c50558144a024006104120100415040044040d1030620281c0d81c01c0d0f540040302041544850001882c0c1d00c03026440038113a4011005c2002d0969485200240091155122903a55940b200310044260049100103040740400400c40e4400b4685a050a8200d00319418807109022880c1c865104030f80080340d40c007045400001d12000e04802c100900c182c141d00407002146401480c100003511060801c1851050f000c4102030102400404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 592339937 1250 592338687 592338779
    0xb1c080c010e120409110f07080c0309190314060402030303190b150c060c0f09010f031e20031504051b0315011b0309170304230103050c0301 62
    0x148040311801406a468010f469015101d00018507251104100b250040381e4140c4541d910a0341c42903080003c540c1352491503520200040582d4041044004d0340ca98480c1c600400318108500708429440c254070704030240010310b00e28001c490b0f0180c410000141ea0001c201c980c03240001404200c0704a40ca010f041c007030400440c002da0b110080c1c070724400c550001e51000d41040565901201d8072600c80d802d00740000d00c564140035490b8281004a0500c9500610044030f01101c00d150002e2150541c400580c0c08400140e500154a922507074040a003803015014588469950500f0074030310304000c1030190700c02e03070704c0b540c030314065911000060130300780402010100c0b400300c1689507580c07032800c0b0080303a444444001e91a4041849482400c2009807484510140aa459211f6010342800c00c10f43d02c5905201624060591101b080701041c1003010810151702e590103490488201440000094180e07000200301c604070350400d000400c002008508450924400c0d104804070542c440d00d1004050700e60 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 592341187 1250 592339937 592339961
    0x10f0f0f05162f0d0801060f1205040c033003020f040e1302060f030109050a0204030b04060504080f04030b24030a0f03090f06210501050d02190e18010b1c080c01 71
    0x210404040c3c2203011a03030075a4218540e44450749681c95600c1a0381c0048040e103800c00089201441302041e140702d41c80703203410501500e841c4120740da4030390340c2c1d20209103817841072504550112262004507401d00210800035619081c01d50508181c0d0050078068080c030b01c1000e1840240c1c002140003c0c02014080140c1500580082c0c0c1d5407190b56050291540284076000310180b6150005441602c02d10135074040c0d943c07000542d1745a41307468413008003400000d0001da903060000c0148506010111000340002c5101c1c60101140346400c441006501c28140d50b1640d4005400b124080d01c0c0e980401c0c800b03400ca0703128441810b1609141800c80304044580c119011f80340783d0341000f05596400240008038002550908510707030040c10100f1082c2d4100384529a0408039441180006180183d41c0500c0f80120680501500d0794a090354002601c0503102c503550000016500c0702034030300a00440c500c012081d81e44001c0b050321410340c4642c1c4211408040c1c21036401144d41a1104403e40080d41078042d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 592342437 1250 592341187 592341257
    0xb0421060e0d08010303020613030801090e2d010b1804170d020d090b06031b0402090103020c01020301030309180b03060f04031106010b03091b0a150908010f0f0f0516 73
    0x401610080c0c403c040a0005030f001d840741c86c0000e60480104840d0301e00d01c2c0e0307156a42c001603901c0c10800c000942145120317100b0270701a0040f20710700c40140101d00e80c81801e020718052404143c88a0b4a4212468246402d006140010700031840c0501d1485068020390b00003041c00d444000030f042650b042c000c00072600769243c0000f51040100001360040c950344c600501b00310356551180c0c2e0402d075441c903401c80040010500080e000c0720710300d8290b01130322181c0c2c8181405854808060700031400c9a00c241c2003140416008030040c041d04800c0c584068104a82e050100070840d40c03000042e503031305402043c51180303249034070009081510507540415078154141c211401561510301d010941d80049902c1800b034840d00e050355804070f501d5420800c0a01010740054003040c144083d8013001d840c407034000c02c06c1c49500c81001401080c01d00c41c0e0307642d00c22000c00c0021101022641c0c035040d01d01402c0d20310125401c01044c00820a074014141e45001c0d402d0900c101d4040204005a5601040050b211107081e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 592343687 1250 592342437 592342453
    0xa030f0903060519230105190302190e010602030c1b0a0e09010b15120433061805010303020309010e030708120d150e0c25080904060b0421060e 63
    0x5610800d50501300d40410340144891194040b13401e00e2041400a00302c0e0380d003403250041025051003402210303400c04507510464001c0e1a900480e480329a25483c0f801444040c032010403c0303080030310311103001d41941e1014500d81404007212a41d00c10f24000c2d2103130f2a0030841c130310203602d680740c501c504010310702c1c0e904050481c0341610b9003500a16690090500407290501040560140c00c02101c7d0240a016800d00b0b9039100d58407801d1000180d079103030305043c8004c46404c281100c001e59403000b20929004d0081016410322598408254030490b95145043c248401800003030740100c00e41d00410030a103030032071413580080300013171801c4d08981c030090f000d010b4150142203542204006294681c02e8030340c2408281c11507402d201c10380c1c8451085145030401c06001c07400700358039040103050724825140e4076000e158088003621500c940f001c0d411540f06c080011502c0b100d0a150160000034900d4000ba103050506d4400c0c000702209410501440600840c0030300f104201c030030f500c4a4142110b03842103030300034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 592344937 1250 592343687 592343701
    0x213090c0513060806030d080a0f090b15010206040b0a151e03201005030c090405070c05010c030506100f17040b040b0c030c07150e060f160905030a030f09030605 71
    0x60b5025405032001071101c00d0002c51030702d0181016601078071003c0d004110035030484070100c0301c42d00e018100110540d05c5260081001039240079020750140200d1580582d4103010f424200500c0b010301c0b00e03c0c155000002000081400300a10b154420681000801c000440601e4003141000356003120000400117890380729061280300758030084c0c1c3d106003500c59641d070199aa40b00183c12088a8a61001c040202041020720071005140c009410710b10344d03414080d01000080039110126240d5000501c01d02c40c48090000034000d2a00500c02420304002c5400d20700b0104010065010040050006500041a40c2c1d889100c251140d10f100b182c0d945100d003080c0c42c04211503c000da80a40310124000080f0b500c241c5030404980c016200e0b9010a49040307400d60303403000c3c400d40301008080c119903a8260640c800e1414441c041c8112199010018a0310b8139550f24040820801c0240c010010100420300035a200040c02109044d050309012072a1020300d00101d400c071006400040a00c1d044c00c0034007a00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 592346187 1250 592344937 592344947
    0x10c020a03032c060f090112060e04111e01050a110f0a060e0303070c1104020d091a0106020708120d0213030807120e240d020a0903020312040e0403030213090c 70
    0x5080303140100c2c40f40108820000b1049120f4070020301e6000741c04000000c6003220700001002c8203001030400180c210743c1030081c00b04660540d07200d0504e11102d0400c0004200b180903201030701d0582141c803022140c0000580031503d031200070319141441000103008464901030315080a112001c07404545400c110b0820702500ca181c0d450701203441900f80103480071140307008000d41b4410089a640c1c8101040c1c0c60300d40505800d24103210ba904140d00300842040c81040f4001c0703004082c00f40e030a01194a0308a4800c1c145010164040411504a00800c0c00a0803004c54014010981c54040a44806986c42c820000b8894589041035449084500004200c0c600c806003440e1801250112655204280c064801800501455600180940d8299601e00d00c1003100d040364070b07480d60721a084c42601030002d8200d07408a881e40c804610032034020404c5140401440c807565178507411080c2001d15064524454820242005040c10307008541c01e02c148070740c420102c00500e55038030240684022483c02a00c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 592347437 1250 592346187 592346207
    0x1803130801060f0b040e130809060c03070201120b0d020d021f02070e01090b060a0f090308041e080c09040b090c10080118050106120906200a17090a030e010c020a0303 73
    0x2d010600c181002604e683d00d60203441c21140b01600013881652008000301c14507029444c1100c007000140040c10302600e0f080080c010a075100c800465584000780000351802503590791140c9043d083c0300880906403550070821210560540307826408000902c00540c001c0c88220a1104607443c103032489043c2d9900107405c0c011543d605865541e1641c9a0304a4000d4072038078021650490401c00524601d98800c9100036510041850032007183d640301c3d40c0c3e07043e655000f903100340a40101822841600c00503100c00400030100440104200130104022075909400284050818a00440040c661041c1800082aa000000c015040041c41c44102510300300307003030060141c0e403d03140c81c5505800c1c00d240b00b40c40c140ca00c1a140d04040212421a007030280020640441e00c0700d03141c0c5032000c03002c0000e00d04180c21401c103a40b2140c440e80030080c002c102d0301584140c01e0710300c44054107110200f0000f083e03580c1d1940e0035240c031440500054005a50b0710070000c000a4214080c10000014560f100d40e00e64 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 592348687 1250 592347437 592347449
    0x3030703050403021f021e0f060702060702010e070f0e09100509062403060a0f0f050411010f05120105060a110a03110601120312050603011d0109060c0302070803180313080106 77
    0x60b00303203c2e03403102c850b51245485c150800503070710a6801943d11415280c00c14010700e550710442c0c030444410030049040038010340e6044007580c080428404181d170280600340a058101c0028040f10345010940801d0781d00d144a8400496115800308081c481c040c0200f0b4019141210305005c5400c102510a0b40c42d50304035500c100141030402c500286c80188004031100a500500400d00c0c0e44a011140005061004100c00301540d102034860b200c4010303009040c0b00d18050454011300c410040005000700800c5003c82041200401c403100e8003401c0d20003101d0541d601038030902d40f10007000d081500c214031944000405c80c42147e01e160200b5500441a06040c5c1e030070710a440350303a43d990f030b641c1c5600c425490300180810010407205e040719242e80e0010343c0c0244000e00104039205421143c9032041c00c048900011079448028040a01000380a07141008505180031490504107031207580d050302020b05410300c01842219224074821080040e51202c03000741800003074180d5101e0710b2034002d0086110306 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 592349937 1250 592348687 592348699
    0xd02121e04030f0309170a030e060904150801140609070309111305090111250f0b0103050d020c1e06160c0f061211041a0f0d0209011e0f0e040b0303070305040302 71
    0x401c5180c035800d003038078a001d1081c00404d2006031940e400d540781072745500c555400c0328082c010203409a40328019a03d006418400050045040c458000d00703440d001c8038006c9800301590180f0020762240351016500031494540014294554a01480c40d0618141800d610441a2894245100386075000300d024186410080000004130803100d1300c00c1c00b52001a07640104084442e4a442d81d8000340d8806840c480c0303140305010305550b6a995104da5080e04143c44a03400b03190191059501040820b514000440c0d038590518403140d10035000940d44e04d0b000f4001c9802085030381442842d83c0074440c0103580055541d042c5a1250700c0e0a41d0811b09116441c0021308000458014a842d84105079082203114200c51410b400e00c1e482d884071604d49103410409102c100b2034000c01c40c03040000ba00040b00103da0250355480c0983c00100560010703100c1355804940399945114058108500f07082c08006030034200d200110100000b4014a070503d10a40c050200003185e20405070f00c0002002a20320803140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 592351187 1250 592349937 592349939
    0xb0a030b030f1002070c0812030f100b070f03050c0109080c01060e010b03011e03080a020d0801151e020102091807080705030f042415170d02121e04030f0309 69
    0x800d0ba072041d10050310600c0c1e41100074070b030a035060b944d001080028011151041007965a452aa25000c40840041c0e200341c2c011041c000c1ea0a40c040b5003541150031034072140f41e030b54104071100401d48150400104082403101c540c0c0c0c201070107441656059440c2c04003c1010309200d041050403644031042980c1d0300d51821001081c2040401d10b02070580380300c00a1a070951307003012402c0e03000c1a016280c241c0c0007250a0400800652200c00602001d440d540c0a4100140c4021020780861010f80100903080d0308200d007000302540c0407032580501c000f010120224510842030581c0240b00340c00e100c1c0d8110b10103044040e8540c502111407070040031155222030450303036140f03002c53340c0780001d03282210941e240e00e020038085900d2152205d048404012066142003801010104079200d081d401d41c1441e001400811003110b001544000c04d00400d809844038050b401070003505d0f601c020b0007040000c41c7c08140741c05850021618209034005840c206580c60351241061100e46402010450004d503406c0c2d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 592352437 1250 592351187 592351189
    0x108090f0c040c270519080709020702010c1502121605070b0703150303020708060106182304020c06090618032d0a09140402072103150f031a0f0609130605010b0a030b 73
    0x1d032a801f210310f4900604541401d01003071070003951110f01c0980c1048160b0390020702050707211980b003080c04045580140c1d00d035140e100b5000101401090000384a941c1a88000701680240c121440198010356a29285c3e42e03588094008000c044a01411071510402c040101500050004140e410020413a100d5a07a100c0084421138410407442c071810000007020024a0740002109e0b583c54081480071202d100150301040c100c0c0c101c0d0340c0b000b40e960700001c2441004a421312070b80350400180c602c281c1c0a500402c00d9140d40384140445201912040800f601d001002c0d0500e44020350b204a0b08070340e4070221018001c111880a0040586800d1040b0314030042c1c0c0360030f1003140e001b01e60050403085406910b81c0390b40c030b030080d014200310241900c1d40d4a121040881c0150302c1d019110820b88030f4103c1d070131402c2c4559900c0300e41d040422101103d2050183c0d8002d4130550560040c0120f4520406e650741241c2d840109460440c006e02080c100307000496240c4c010310142604040d1070340c04001940d2240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 592353687 1250 592352437 592352479
    0x18010f0f060801061508190f24051e0d05190c0806010e07140d0e06160512010306020f12130209090a032001021201140108090f0c040c2705 61
    0x21180c003e04c0002501c480002d06d000d40520380d0b02000800369000c20700c880b52a460152500150101078040d940c1c040d4002e507021001032a12007000d01500d4501150410010405a00740c05c061158141c2d1f1201c2e007004d8507603400383c140a103a83d01c4429501c544585448001d8031146005049442c12082c0c0000b04641c00005412412105e11991211a9440e0501c0549a04800c01044500c0440410810802c5107060141a4914000c9001400a03103048051a8140310b1441c641c402004010003980d00131079858030b02d40381507a80140005070f07581107100c4071255074480c95464030150903641080108003c0390150114025009407410195580c80101c495120422110018082851031694162004140c075102d0701c7d0310805000185000e04050f0b2507440100709a00000c9070095403102d034102944e000c140c507908000000e000704407810051034990744035440b2214041c004c0307940d03e14001c0b001b48a00c0701d800500503185280c2654819096441c110b00166020701402006e8511800561550758 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 592354937 1250 592353687 592353689
    0xd060509070e041d0303040506180304120206090d150e0c09040209181f0501090c020307080d02070c0513091b050a0303050904110a020f010f0b100818010f0f06080106 73
    0x42e0703519404100d00d032003084024011501c5050300c038070665002001e060000c1008500403401180101100c0c54052514030112010341c0704150305420500c0100006480900d50284255048030141d031280c91181c04a510502117003000340518802c1001489005055801501d00c21101c00c10b0b0341e040741c8a4403d00141000c1540c000350040d05010004a1100005015840010b0300d036041e68041c06038040c020b0841d00c0f11540021045540f200104a13654041c0300b0400c0d5214140055402c000741034480c0d400e94090b41c0c2d0301907100c0e600010300702c08001c1501101c00c040c02000300307410302c81000c690003240145908017086900c15640c080800c0da44102ca07a464080310002850041028110baa04441c40d4001c464a2600243ca9035220400401c140025224241c0e003076009000e00304214020358256072005001c1c404103803814461015540302c200007141d8440f1542030034855500c07007840311a850000360f8600400c0c0c0d4640b116590304914107810600031000c10340c105000050304d9000a6080b603d80e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 592356187 1250 592354937 592354951
    0x5070903030e040c12024b0d0e010908030105030d0306030206040b0a14030406051608270f0607050a090509090c0d020d05120405120c0f011209170d060509 68
    0x29407000e403a01d0745001d802098a04d0382501d018401c2101c9000035905a8100754048819042c00c002d401805030f02074480326140321031078240c02205141c40014207060b801d80c80303100154408002001c0e2001d070b40c250400815210401d008204032911402e01d103400d0380007070040342d1017801784c4a4800d107458408e01400068980007030143d403900c0e00e031860601056000707441280a012080307829000c028200d501951080780603000105007031810b00050030000301e25800e01c00a0194902c00d04c80b6819010798111004207203602c02c04c0c3d03420b03e010700d442c2c03510078500050981407103a0720812208503403080c00351003c135102e519002185a1100200711342c2c904222806603c0e90700290080c0e000d86424081481064005061500c1418141e00c07070324240320040c00a20214400001c0820060030302c0300c02e00c1d44001c4090050b00360403800100050b0003040d2805028100420064224641002ca50000c010305074090720300354080c0c8120180c8c03492a00301040101a40b0b10700000064213040c4904000c4c031900e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 592357437 1250 592356187 592356197
    0x60f0608010e0d052508030a060e0408040e04170a02160501020718021608070c0602100203070c170d0c023f03041a07020c0f0406050f01120b09130302010507090303 72
    0x40454201c41c1504100810034056504608031000c54030352040c3c844955000d030724882c3e1f603403501c400d0070026182c00d94000c00024030110304000c0071581507029903041ea80c0811214801c1e8491382000c8001600501a40308150340005011180c6600002c2d0f600c030b90002001c0860900b603540300160784a004500c2212a2008401080c111034101503000703282d20340754030800c1d0101c0d00403511242e44942041e05c00325030303030046010107010782a01081500b80c61990340320b00f50b2442c0761502c030045c40c50b021030138001d03c000300c203a038103003042c5103480169020101f44500030002480c8000c4000e6880c00c04405c04035098a804400300c1001032420141c1c0440c0c1c01c240c0503040da0300340c4555400c1d080e078001041503030500c80350244417840003c1720070348500810300c944c010001d8003005010081448551341800c0d11031881c00c001001952608200421340a209080c00401e0380b00b02c031225009000840070341940006600104a00802030101c001e0b840c0380258020011a50342c882d055590903480d0101a012030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 592358687 1250 592357437 592357453
    0x20f03040b0f030907080d050d1416030b03010e19110d050d140927090109030206060f030c0415060f05030c0301030809120709020912030913090302070305060103060f0608010e 77
    0x102c002004540181c44c540440300503542d6801058105007800d008240040c00004403c0c0034846140185582441a02d501d000c030303810b04940e40b12408a2803040c0c4010305807910050300e55030340c0a40c030404000c421a07003541d004160244581c072049113100c108540c0d585000116010300c0c1496402e0710f846541c807000507c05480301c1c03d0240c07540e90f00d440d0b44000e03408040042400c15110304003481d0141e4806030040260044400494189a60042040c03440e6894058040b01081c2d00107503c581045083e03c0481080c1080c00209080c0740e800440030350070078103200d62020300607441e407050803c0740e0300c0d13540e034500e9200140f070704846501c000c3d983d0b04c1c001c0109100600200d198100184803122005024021112484450790300301820307580412002540807a0b040442d0602003041440d41d00344001442c40c04040c4400140304118a5540002c030981d0742c20004201402009480d0245401504035401581c0d00e141040140030200c4800c454141024800218180305008501000b427500340609802 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 592359937 1250 592358687 592358707
    0xf0212071805042003160603060f05030a151806140915090a030e0607120207080106050a080709230108060907060306120312111c111c0b010909050702030a020f03040b 73
    0x41315541c0781540e00d8024032203980c01c54146000403a008101c1620007164040c5010f4010407034820039840309000b608810b000e40c0004c0c0003644002203021800c000040e03081230320030091201d5990600021319035464011620010255820346a104000c107100f11200c401c0e000c0e00b0010100c100340d5006205900182101d40041d01460300d001005601600090070240c0305e0302d40b41380070001c0310b440c41d016802284003402185800c8c0240800780c101510f00800c1145460220355840c5198828003c416a99841598184108036004a1405e400c201805a6035031540e1042d40c603600c0941e03143c801d0303103d0942c0001b01c1c24003a000e00021039540140890095206072820741300c1c0d00c40761403000d150a0f035075881410015140380191114404104045189031003418820b002c4546543d00b80510500600c10406112214507a082d81d8000030080402c41030308500042e03420095907080740d4451403e22042061483d07001010706098a801d80c02c90315120a03140215440348218015403504000c20032917440c00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 592361187 1250 592359937 592359983
    0xa140105061507121e08060f0907050a1101090203070b0a1e09091a04060b120903030906011503020c03030106031a0d02100509010e06040803030702060a0c0e010c0f021207180504 78
    0x1800560901c454440c0400961160380170320800329101060843c0103100d01750030840c91405080b00142c40304032407424081c00103007642c00b9a000b084100040b03508880640c1303c080d0401c4007195805000c46003207c1d21510500141c1c1c20070944400014000c0c41412034108810100c6d140b40a1036840f010310a505103211100900141d440040c0303090007004542010f0344075880b8081c0107001e0940e5140c3c85169141c501c000c402800343c00c503101c5600074002d10115420108030300c3c2c110b82d0008032074030103030720300c0e00301507000c5c1c055400b010034540000700000030b6442e0150032240175458104000541984001c0c1081032013080d008010b034000c2440103c0c006405d00480083c0170715001418210704241b25440001c00560040d00150b14a4102105000c2d085404004254002c00b030800300788010121442700030584d00c3c002d58842c3c104650b015186051001150145440580191040105010051965584072403034400d10581526604450f00188442e100346030240390301468041d00a03010b100d0480b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 592362437 1250 592361187 592361213
    0x1902060d02090307090605010e03010b0a060503071403010b1e0c06070509032b030e0613170c010c0306080f0a0803060d080f0309010e0105071707030c02010e0a140105061507 76
    0x52056400c002400b0070750740810582e002401e1149010921030304000004000d01381071901d0a0290707041294008a03a9280301e80f45080d2203681ca84180c0300d41c1c1f84c0604030b8181400382c0301d40500f10750000021a14144110090880c1491100c200c1c000060454048205200c1e00800d04007641100002c40c50880c45040105080347c4003c00300d5100100b40d202d40c034022000c61405110384c122011400030490307007600501048100031005802e42c1c0c83c2c08240c0000786003070000001c0c00300094400c030400514160081d07443d04100c090081260f51220b40007e001080da81c00f440c4058031400c9000b4001d60000101042c505a00a00d282e040d902e8120a004829500350302c00c444281d814045845504042c002071480b030380c68000040b40722104440c17030b02c1c01c458029141108105495035620b4400300359a183d01d40060061400140c4404c04880480c0141140c1d048000300d40126011002030003d40c40601081400c4c120082249031035450802c1401502d069140c4d10b400000e101714070200741c404034100f0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 592363687 1250 592362437 592362457
    0x100903050c101e080a151a03130c08030c071401050f0d0608010207030513060e06030411010306170304031a0403020c0907031401030b0f0f0403050301120f140c0909190206 75
    0x4802c0c00c90f04482003860b00038120742d000035001d80204140003801d8010712101040300002142083d041000d0302240e6000c1244441120700d0000119008203155031039150010707082100d0048507a00d60359007545945c08503065140c00d208442303010601e01040c90512031041016191a803034015581c600d00c6030307500240385c035445066a98000044483c420700090103898400c0d0b43e03c50ba200c8018801c030031102c80c15000001004a8528025429202d0600b00c0f0b4029401c18541958130064400403000f40c01c0d95001501040403c041c01081404000701510607284507010384201c02c207443c0d9006042c3c0718101c0b0050010b034440c0c010302100341009030416400c07074540d00d408205004004a1003c68100a074411a101807a840401005814540059420685108004509048c181c400600600040c000d0958075854800080c1c02c203c40d180000d650a9846171401c131905c1643c904260b1110700e15001c0c64020a200400185050070100704040c04e00317242c1240c10348118041c2c00307018176078014000b68 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 592364937 1250 592363687 592363697
    0x1503070f080307030212090105160503070507093923070309151803110604091a030c03150f2809020f0a030f020d02150703020c100903050c10 62
    0x30800d40d588032000000740c01554011aa603e5440c9002807411803069040c089226080c4200a40c1d41ea1010864880a00a000400c4807501505043c2e081d88200301d0014442d00c28642d000903054502d8000c0c00901c4c803842100343c406a010480c0344500c1103140480c4010144503034500302d5480c02000f02c0300c01e00003e1a50703420a00345100503d9030303580c0182819400724200e41820010400c0a07202600e08101d5481d2044000c14000b20502d5040b9290100800600600444920a4a076078050b0f8008190000d0180140c4001002c1e02222007080881a406406800120038183c10f000a282d02c0c0c8042c074801104080e80c41483e5140c0e031810203003500204d26203026000c581030f01004190040d00300c0860300018032403450310411180c1d06100b00c805009803408081003000c2038202600181680d0160f0f1030100d00c5040e0b00c0001d000d00d400310303440380c8914801318500050583c0010301d00300001c0c2c01d94488803e4030080c41e080e1060403080c4030090403640414400c6100b41031a0313074241c2e00ba155900308 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 592366187 1250 592364937 592364939
    0x7021c14070605032401050712050d0f05010801110a0215070311040617090601050102030906220e010303030b01031104090e0705040f020a090b07020a030f030e06071202061e150307 79
    0x103150900304154040e100040f00401480507940002410801000c0000020008000e280001814500540e40c000d03205516124492200c18015400c5030b07103000000c48100034003c5070041907001031900f80140d458a61a1204c0030b140c420440d070458151031019002001c03010244400e88181250040141080580750500464100700903405003025044648402140004240d002c0c101d505000b800c403c0d9a5111100402081e6004000c5400d0f0b00302c2581d00384c2d91148807443c2c0020407920709490141c154594030002402101241c43c4d2030599109076000d11417000020b004505880d80300c0041c80d0300d03031820402000b80c4103540d4004c1d000c0742440f8054424031035862001600b200d10320000711003c2c9400180b9800c105a00c01900d2020308400c0e4080c5051400e40c2d0041000300c900350200400b01c007000c0d580107060502a03800100e01712802006103030380300c00c2890b00054803041d48076028054442c11012902000d80f58440d6074000800d4070401e2000c0da01d02001120036103014203155094054a84 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 592367437 1250 592366187 592366223
    0x109020d06020c060f0106090618050307031202100c0e0d050c18010501030c17010b031803040f030c27050622150617010b0904020d0504060501090f0207021c 69
    0x41000220380c000c80c0c00503200c0070019441420050014041c070070504020005100d61764000c108a4248d0708145003001c14a800440004080d244d40d030440740e89031003030007800002c07c000c415402c4034045040d404c0e0303800707035481840900c1610303040c111500100701110001c545901382030480b82c165600440032284c29252141c00300e20320050010a400842801c0c0700103010307a503018088c1c034004c0c41c841d2070148060065031040d00001c00060151111014000001c01c08154410244409403d0804190ba40d03d550340d0200c074801d1a420310040714000040c0c04009102c0c0528148101c20000d5500780d40540e222200004d0b008040041a19a02105446230500c040055205644e10ba0224010007c1d81c07540070000ca001d400401d078041c0c3c1c100601ca000317032030001c1c54107049681110040111389031182c25410000700a030241c001e88100407480e1a00304010300406400c0305040751217a07002000001c9402d90714409911509101942000c00400e008200035049512500395a002e401581641d800520b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 592368687 1250 592367437 592367449
    0x91b052b0f0504020f030f06040b0703060f06090e010e13060903200f0c040b01021b01020309181005061306080c040b04030f11010e0f0909010905031617091809010902 73
    0x41d640c107480550710002c1008600b410400000c220300114020064504114591692214020002400c2203030100118003d03a000e074000c0e80c083c1c800001269201c54a8040003481260648691040d40761518000225080c81410550284101c24002c0010b248107803520300150058107411010040b121030030120100210610b4600780411102511030303012581c0086280031026038902d03100c0e0b803a02512904d66030300090710038002002002940d620315401d0006074194007130541c00ca0381010301184c1e150760800c411289a032040c0f51212070035110681780d4003030000368090b8004c03102e0b42c00001c0c0801d202c03007400750f0790250b0701058480c4800d03d0700762588208941c4d5009075000700e50807009200014200855404c40300140102031800807000703074480c070018426504030743d5a11b0003145c82501062261400390407010441e178100342201d80c0e030b2070070358181658813620440a50f003000c1d000300708040040c0721800302d5600074001400f4810242801d03001d40588500a070205400750344c1c44000200503246d80d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 592369937 1250 592368687 592368701
    0x807051c0f0210050f1f0503010f0905010e121e040315021c0207020a171006060806011107240504120b071119080f04050415091b052b 59
    0x60703038411220100c0e41c40080e29045210f41c0558460341000e040050011030702a08540c069010b1080d1555401140e0428034402d40325040960107508150000c01d800200741c1285854500c43d1380204400d1710420000383c1c1780c040c10014400381c020100215524400041080842c0f0504104001c0c681540ca40d5515203510b040d40c651400e250700880c507902c0c4a0b0803290207140d00942c000b0700b546004400d90000d1101c03503550085600741c04071161850850081041140c40c0c104c0984410801c4a460350800f4021000485441d40007416006c400303294254003241c288201ca8800502c04403811740c000e0194100c0c88000342c03c41c1002418080050076480f81b0040d00491780c001c2003492040e050100000b002d600d0f164803030901640c04a2148175413540241c801c0f04081c0c0e0002c03803503510b8511520500c01c02d445a5030100e54003074240400036480d4403051812801702e4001c960208050910059448a408202c80c1c40d000418014010b0084038494076440301c0f400702100e8500c60100c507803d1003c0048a440d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 592371187 1250 592369937 592369993
    0x6030601020c030708011d060106050901030218060d0f050a09030c060e0a1704051f082802120603010c0c02010f05160602041e051c1b0f0803071e020d080705 69
    0x1074030b000002c4611114a90b0a107c3ca0380c802078074096050110186c007078441c04207640d0400d6800200c103020825031160001059800030642c0c0d0352951000f1404014206a90070000c4136842c00380410080c1101d80702d074440701035260720f914001849036220030000340019a100201c81c0902800032000907094404000b040740c10000c05078440c3d00701024441d84440500204017500310341c2c00003100c03464100000c01c1e030040001100d0803094801030601c0c4010f00c000e445c80c44140c4d0012621080300050712034042d20424085d0020071440b010350301c040f2580400500c019011580031550700d03401d039201d4001803190125000003c08a91080c2d80c03408102d0340b0a5000c482440e800b141c032504c10030340002e4920300807c400c64420740d000242412100341001e400e40000c1005c003030030044201602d084e0b013417440101080d0b480c105003180e54041207500c0340c0c48410115a1100c0f20018a03800d0041c00801068142c0c0241583c2da040b80d490b0f41c0d620481e84410020f941620901079500040c60102c03002c80c940c449 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 592372437 1250 592371187 592371191
    0xf21060f0108010b0a230301090204020f0418061412120409320712090503030f01050909010207122d1e02071404110408150f010e060d0206030601020c03070801 70
    0x85002c0c009030848004065075481201842c60410800e149014030784845981000540391810303000001070700401000d640290800d0001c070700c40790503001c00300c050005c4070081c000e4002c0922180c090401118064024984003031010040d11000b0705102110042e080d1103001115001c0d8881c800682840e00551300045005464101c9a007004e002c030704012300d0b1031842000809240d100b402004002107401011001000701a50f492030000c455604030040c100e8029055980d01e082070b49884000d201c09001e414050039811000c204084814822a40601d411085020b14280301c03072000c541503e00340d0200e101d84012540102209124101c21588541842d1550082c03c00700742a00150044840020410b42d0411003081040318440510300ca100d4504a0700024400829400d41000780915006100383d48a241c0c10180c10409000c0514052840007900258607a07a0f400c80c0e11550208958190308400a40c55000050410b040907640150050040d9002d681c907041c0402d00d0701c0035a60020065039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 592373687 1250 592372437 592372439
    0x1a0a0203040c06051903050601052a120403030f0e01171303082a030601050423011b05190804090903050d1a030d080a0f0e0a1109060f21060f01 63
    0x1c500071219000b8240750a045040c68021031005d054405441400c5051507191400110b041e0b102e9412194440c080e1402901e0306040c4601c502001001c44504006a01c90103010300b481621400c00e49044981c5941c2d80782d42c01901110450314a01c0700444141030140d0465190107911601c2d0210340b1641d80c42d02c0041000c040c80c14000c1150001600306034182e164904000c014041c00c8030081003542c00010072070760700c4c0c5031000101c03840d00c259800b003040110300c9541c0d613401482c4940994081c0100f683c0f411503802d0b004452000c02c9051905c020641d6000042204101d20019050085280280d403d181420340e02d15414080e80c5440c18201c000881c0010701054048a0f44592800481c520114104079480000400d40d5070040f451084280700000c00082c0c200708280c0c220703c11400c2084801c2c800101d6985609a44010082040b201662403d142500c2403c1c4440800d11070003004244490200c100c8e800d11441c0c0804500648e080748a25022030031400003004107d025510904c1541029 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 592374937 1250 592373687 592373693
    0x1805060108070915081b19090b041d04030c05011e0f0603110618181602010b03060a0902030703020603040c0e0c0f0702040c110604060c12050408070803041a0a020304 73
    0x42400107249605110718602d05210f504c08132040400c0d49010344c01c0182141d2144c1c034005403002088180b000d03400500098407034258854000c54180301103103440e0920500d0701c640300c0003140c2c00386006004207241b011003810b1b48050141002e40d081402400c10309180702c41920361601303540d881101c884002130b100f124503204021a100b800d00d41000143c1c200052400c0d0707a51140b050407191100d910888010680d280503248a056503503c0340c000510b088600384428603521601e50f8100c2d190030b401c603a85007410390114010b008910950b40000c000c2c1c01c00e651942600d100505009200341c0e0544a0980701000607160b031001940128018400600f059280c006c143c41c49500052050105c0341c0103000070114016000b00341c5943c1c507411a804119124144400c90380f10099040f940110f00c0f54030240414007085074086003030082180c0d48c0b0003800740036103409019914182e400400c4810200320050100328084003441d0454840c80c54800c015401c81d0f19444c03008030644560412650003c180810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 592376187 1250 592374937 592374947
    0x10e07050a080f03030402040b2209061404030e011b150f0606051303020f1f0e010216051503070509030d0224040f060903030609110c0d181502010618050601 69
    0xc0000b4001421056035540c001030f00c0303001c0944020301568584800d941c450741d95032903e405c0b1620b50120141c05074108442d160107800103260651b005458101d40b1119103448010480c4502d8040d00c80c0030100f00d00f20b004590340c030505103501c7c85080200100500242004021076880303d0240c50106021040881e01c2045810641c050380611004010f8007880c0400000750b40e080300c2d011118044d06018101c00304413040d1580800101c844141c2038102030980e0450440080703e0020b03421a4407844c0a2080c2590006c41070060356449880d66480c0340c100101000110f501c190f01d464010b0800000700046440c0412107521030000d170b00003082174400508910340503900314510307c40c134203540d08141c0c8662052062540014009944494001b800d060080c0c100900030100728104109850703c0c2c0203041c405810001c0041ca440c0252a03400d4856031280c40807080904c89a6822600c0c10b1030044000c1c0c003a2028000d00d400c2d9500c1d51000980340c1a03000c407032904a500b400c0c001c50545407035000101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 592377437 1250 592376187 592376189
    0x1504090b120a17090a0306180b0115090e060612012903061018050a060c0b01050609030606130b0307030c060e09091c0c17090a080a050309090c0705010e07050a 70
    0x45150b11202544000ca03c01c0c4240858501100c5600d90342e485250004c24840ba84980010b40480d04006044030800411601c548085000f05c0c400714460340c9030101c1c50112000309401800103103880ea0140304a00c0180c842c2500118014445c906d4000c0360300540f02c509401741d0080d2800d8039400003412410303900003003c421442d40400304501e1842c1c840e000403034803007001c00700c80200700048820f055801c100700304180240000401d0001903540d6000c0050284801c0c100440d14900703040000900390a140e803d03543c007800c00402900850351000180309844020102c03c5544039100c4000c001c0a4505003c080017860280c1440d403031144c10998081c05416515030118040c9804d08108111043c1c01300d40e501c0210410302641142655601084592051084000e0207910000c114070060030204001408017881c00c0d0790750754a5554070315146072915101e6101070013a0300204800007142c600200c0d120340c00070003960800d00386201030b01d0300c0b82142d8500f4880c00055002d04001e01292604000e031030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 592378687 1250 592377437 592377469
    0xe10030b070203270301230108070e19021e03040f110f0d060c090503010615020114040809060f0d05040302060919081815070b061c080a0e1504090b 65
    0x5441c0c91045401907a4a004900d800240d1104410004d10ba5650079041a000402c1d0100d902c1d034040b102d407580b41c100c2e10081c46441c2c06845001c0e40003c503070026602083c40b40600444514681c01c4000c0f541019600c0021140c0098034505940744040e480440034600450041109441141081c5821500351090700c144901c00c9004140d050b60b0f40c3e6079a0b01ca2140d441c0d00242c0403603800303514102a902405036410195165082040200d1101e021000720030800c030703096009100b000b80f0740304591540700d0140c8000c1c0a00c0310801080c4090b0401b9001412580303c0d8003c582c1c40d044020501c44115a000e0300c00324016048030b8240080600e04000b45105640314000030001d00c012959418401e2265401030784a1011100859241c0d965002001402d2000c072148148da4034898508568040403c031071040c42004e0504213040c11740c0807043d48110850303025850302e19004d030311441a2032440900c21030661015402e0b18103010101a0000391000701070100020900000c12020010007001480e801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 592379937 1250 592378687 592378693
    0xa0e01030f0504051c02100915060b04061d0d08120405060604060819060608030703050304050118020f0f03011508030a031b0207030b040c03051f0b041a10090e10030b0702 75
    0x1c8000300b2400f00d82445a9905103900c680c241d403e48030b01b0380c2006032001001c0f103150300d040481300074008840100a80c03070240c950100316403910340480c045c45010b21701401c00000c003825515200c0180c036800ea00c124440003050f00401c514141e850402580c402d60f00812941e136990144420000f041095980205044505006031400c044615580f003c4080e940610501c0c1c0001c0301041c84071355446034001d80076440a80e5a14001d03410051b240b50700a40c1c0465040d0300c2d00ba030952a90301185038049105900405144107001030b0b01c100100b4100031240203604d55664a100d01d084204001d4001c014070780b20700a50b0319150b40150150465003082169100303201c3e2025005d0145601180140c1030380d42c000044240c5444904109030a072100d13400081207885142240100610150481c1c107080051381c0040c02a802d101080c84141c40c0321000840388a2101292203146140c071500140354002c1c02d1512001096444020b40b01040050ba540a0740d440c10318014002d200720811866400403682c001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 592381187 1250 592379937 592379941
    0x21070b0c18150a050f040b0a11060106033804090507080c06090604030b0c0c0307082a060423070e070201050106050403110904030c0b070225030302030306190b0a0e01030f05 76
    0x40103150340b081683d1202002000a00c8509540030702c3c0503a03002e400e640b52429101d807000600507003441c0301d24584030380b2445850000144188240500c0f9050104200d28000d582c2003c409080a140300b100b403400f481002036010040c545030740c0b0450300d00b00c0c0101d000708800c80c03400c684142001c40b0215458000d80003005020000d4440904840c01ca90780000e01c0c0f201c5a0f03a001c4c203920240204180c23070b4101d000000c0c0d00740c1030041c0d04000d4400450510254640c0f49540344a00385c044d4050b42406605801010000c0d0104400c04080f00600c0e181800280c10384065041071400c000c4290004010094480b06000d20703194248280c5014010500b030891a0034210b03200c4420b500d00104060380315040c1d00c8009802c043c4607040120615901501d0859103003030041b00a03403a801034108100b9248480384001c0720300041c40c0c41140c100d13901500176524648420041c80b01321024a9400d1200c0b203009a000110780701d001e0014007072050203036904070842541c030000406a41103c040a0b002c2818002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 592382437 1250 592381187 592381219
    0x40902120741010c050d0c020406050a1212110a03031413021302090f04090b0a050f060a0317071406010e0c131401090302030708010e010e0f21070b0c18 67
    0x6104180000b80c5580580a0640100d030f40070344684e802851405071103100030300c0903044a44020a10301c2180c0034013803180c488043c030112005510581c40410302046850000c1403c4d1502142c040301c1514140101411602d8114a0b152030300008600081d0f44640003070140000c601860b8001d4a030241c01c55146055400040c0b4008103640050300f501d0307000440740295540c00d51768403100e42001c1d00500c000109414141c0c9000c804540d200c1c0c4160900c00080c0000500f803642b6403250600600c0070101c207040d80c6604014002100410425680030052400850444001e10820a038520028280f41d81081c01c0030005100140008030f030342034103101015807025003103a240281c503220101c4005200c030340b40040750700c42100c1c2c1c8041d40500034148045030581041d0070640d50448588001e009039200582c980f80d8408005a0103180b503000403005d264411840420002841d115005080c00d00a440c0c641c6190820140e4455011107000100f0348400c4800076407400d0500011580d446101c0d6183c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 592383687 1250 592382437 592382519
    0x606030209090c240a0f0203131205100501030b150607020414100e0f07030b011214011d09150402030a050f060103020a0b030405060117070e040c030311030f12060409021207 76
    0x1040e00082c05441b1069448003031080040c0c840d03044404a2801c080e540e0741d030700c80042e03920300041550301c1c2c00f03214030a0343c0c07404090260703c2c120381d0301c940c2d044025695004207640c0f245128103641e501070700800801000d40c2e520301501100c8098219400002d041107000440100c00981c001004034a0900c20002e507083c004110310750101c0103050203d54025a000104d03804105030501e002202e1800e03114071703104548440924161800a400700d5101f079950b00540100b41d10860b0500040d9001500300f0300841c6481d000150894401350444184030011741d01d09003480c01c41641c910003a071005004006601d00041d03c0c10003001ca10090a165003019100e1541700c0d581409600701111181603040740e4070408024070401015030a242d128036040070b1418205200303081c802a4000f44c1d4646442902c6003002c0f0480b0a40c2c1034840200d4605401070645004001004100651055452401c5400b588800ca1019912036111000e001864205900781d001c008158400c800031641d030703000e0f00c0380c1c5040c01c07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 592384937 1250 592383687 592383697
    0x206040510090f1b15020f03090f041409010911010f0806040e0309060f1c06230409140d030f061208400812030606070606030209090c24 60
    0x324000c1a070400a0070b02107100a40f842c0001d0482e850410400400000520940155140f0481d0504444010803080760b4500072981c81c2512500100002a0342d860104d00c05d41038070b900035001194010200003c072402e07040c100e60300448c0f1394440c1401001c00c01c3d080d00f4100c02c180b09007818008a039560a0090a500303000313200c1070140342c0e2125241003005040040e02d0b240d03500188004e0361000030284002c0701d0340041c0c4120038100098240105404c0382c0e03001d40c000707940300c202c0041e0104580500401c201d030512b50406070410769411b11300d00450550104c041c030780c0d10000c00030070003007006000c01811030300c110f403510b884646850001d01980e4081140104040c1d04040001d072103044400043c803000001c0c41d014065100c10806515030b8018103023401104450315004403c07061f0751603a5540d160b130003111541550617000c100140c0c251400c035020300641405507500159007510390340403820701e050694500d01ca036401000903000d680307082c0d110208000e8141c0307a481240d4001d42c54025042c054 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 592386187 1250 592384937 592384963
    0xb150c060a060e0f100302060a090f051507080d0f06030b01080c01030b10050901030b0301060815070207080c06031f03050309040e01110f0304030c0c030308100801021309180203120306090702060405 87
    0x10000864217004400c00c91102850700207040f00d41c2c8141700140170301115030318412402101005080000d003460210401c000d00000b03041418500b6000f0b07600c507030160784005100ca082031f80d07c02861450a40500c18100030f1841030036244115410b100c0f80e03910703010b038580d4018105070400e07060704e1280c0c46003038580c943c2c6002c0741841501c90300380b440180d000d800446c40c2241c0641c40c1c4400092400390015460b00c0c6000c82c00c0c03510505403601001241c440c4100c0c001d01d6000c4d8802c11070030300542400c17401958022070340280000781450003405014801c0d11a8002e958a51000c40c9900035460f217846180103520808008014190215851200d280100e116841d00d1005c013000140505008040b081c0b17005602c101c0c98542c0c0e44e282d24001e030000d00305407000c03e0900602000070030039000520032188160707e80c03103600b5012480d0032640005040c034140e181c1004144c4462080058504000da006840040c410050b128079100c2c0c144030f503142c4c0c010404011940004103210101d0000316407a0a0006 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 592387437 1250 592386187 592386211
    0x2010e0402030a0906090501020406090b0304050d0c080705030304030f14041a0a0e0d0501060315050f040219081905010b0901030b010306090807300315090f0b150c060a060e 76
    0xd6180100001009021300117072105080031546420001c06500900590307480d41c40b42c50585072100e422a10038001100d004002c0d901c0340c1d1241c04070900801d01d10048602c15030000385007917281e41d107060850304140c40c218042164a0595031580750480d205170007d080c3d00700214113003407400e54a042c8100ea241c0012100b1361000035103c174124495441010b0042e0f01070000f80c242501440c01c0d6000300310911050340c440c204640e0b01d0381c08801c14082e07240a41d804200140c0d443d203e40c4c01700001e100c0d40415034a081e140d03501d40010031003020301c900804c2d8006090f05800c1c10410381032450941e2507800100303100b020300c840140b0024460808180c1541d810000c00181000d07540307021030040c815040007800d44c4603081d001d0aa1000c9070440c46440c1d16140c00c0411402000e100181c1c191144204541000c009400045c007541e0310070340c4079400c110719000d030220f090041038010680602246e0900038880c600090081c1000b10200710441d0040c020020170828185440d02100d1003c9001c0c0031071305099 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 592388687 1250 592387437 592387441
    0x100504230a061e05040e0604050a1b090f05040908040e07051c0c1d010203091306030b070503040218130f110a14030111070807030f14122202010e040203 67
    0xc010031004200380141000400c9900c940700505991000050380c44500311154a03203025610540a903000c0781c034003030030710001390300d03030004010251130024134400010750390328086441140c1c81010182845140d07200d0880003070500014401600e0a5001030707001b142405c5e00d2100143d08041201e080b01c0302500c03074504649940c88204c449100b1040c0144454a0f0002002e0040c16940c7c4002d000720426103c0841003111815011b45411480c0c40550250f0018441c4421504000300d0520400c2c40c0c0a0002685a840e80d03106040d146083d9030481c00240040100011814640c95054100600052441e12031500503003c501504180000400c0d03000c000c80140204900700005950301b0100400700344005489515941e45100110707180f030302c258205801000d00721001c03c102d9040c56003100700146011019102611100c141e401c091003042000d9105c8180c4030540f03009402501c02c18154010241030103582c00f150600160400700d154103c085003400141e80100440e01c0c506000d560140c0c4075 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 592389937 1250 592388687 592388729
    0x3031806040e010b09010e012d0c020603040b01030203060f10031e08030a0b0a09020705151e0403080f010e01360204080304030c0b07030c06050a1127100504 69
    0x1a018a0b809246a02080310021428650003005090309081c20b90325003651142010044915041c1241d454108049650301c800301c010b030b0100d030300c3c910a096040240d005009940491000e82c03048800384c60034423a61005000b1440c090101580040420a02c80e00728284141da0300d00d416920300c00101047e010103e40803a0b082d00600824100e038101e1f00054030703031521841d1500074140c400c9109100d00e8049601241544440c4265580607030418010407154100c608000c0340464003512400002401c00700300c3c16a15485c0c07490f1440396110307a0b10103038507080c007000900d01003c060700040034182c0c2080043c402017201c58510b90b143c814010a032801d084503180c00c95178044201e450041c40b1070001801145c00c0d07100000600840740310307400c0e42540c00e60300c000c11100c5c0e000e00721005000451030031680000c03070b4580d0032494220020b4800081c01f10364501c4400c4007a80482555800f28825186400303c3c1001c55040c000c03420300542d440d001201e20b01900510500c1036003e41d150071740b2291000142c0f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 592391187 1250 592389937 592389949
    0x903170315060c011a040c0e090a140705070309090b0f060a1106070906080c09010c200402071a0f0402030c040c111e0708010b0105070b330a14030318 66
    0x30300c04000c0d02040d0341c1c12018070f400b4060a05c00300c444102680110161085082c01d20072001d00031a9a5282009003c500f4100444064003030706041c071254841a4007240050390014403409201c1c1500c13050f03a2009240b80c09443e001d111b030302120100d07141110202260712081c95110700300038200c480380d41c1c1d004003080c10359440c24407412414440c030500c130401041e10703003114101058552035210448290303100540c582d490307c58800150b001503059840f8100080340d40c02222800c074600074020b0544910840890102d800035001500d00c011000c903c030031651146842c1c01c3e080100f001c0e1070344651403d038011950320541e03003c80c0e60042d55506003003241da0f44900c501500c04001c007810b45554a00c00700541c0c81c6506c032000b40d800c1501580c01d002814220501c6042a1b000301a15242d003020080c1e240d044000c01b0080c0464811040640000d1030b40742818000b40e240030301710b0f02c035582602461092282045190300040c905024140b04008695000800d80344450200e60200d030040701c103c404155 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 592392437 1250 592391187 592391221
    0x60706020c0d02010e0f2b0908060c0d0c030c200a150e160f05060f040b0a02010912030c0c0b06040605030303070816141902030f0703080a0c09031703 66
    0x100c0707409480010501c0641c1900f044a40741c0320041100c6111102c00d40c082d4580f03202e0340420700160f21440782045082c0b880b40300c40051034014105461513a039034208613414520125140f00440c80c0000307040d0100340795803040084018070751404015039986140f01500c144038080c400224402c00710070500103a5002c0200042e866849100341c8203400701070514001030044510800103601901c0b9801d5500203941d070005044030106403041d44031500d44424000c09501415030034144040400002c1039072400d1500401c04036045600000324920036040c0a0480c0c42110240c808041c20b0442c413103ca240e22003100706c15950403050001d400d85030f04c2d001170300525155000c681c050102000f00200c15800c4181d042c4114040311a45941130b105000440d0003610703214036205114014800020914041404c024107405d031801142d141c00d44460b0340c2d50940d0003824044001804a500b008404802406212040b076210300304034660300e00f180d840b842403103282c4038403105a0602000294200440ca5500f007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 592393687 1250 592392437 592392457
    0xc070e130b310605010f080303060a060f030209090412120c0f0315150c05010c14031303020a080412030215010308070305031009020706020c010e0c0a171c020606091608040206070602 80
    0x52580c07240b0714108020713240920400085450000c4005040c2d0b40c048102c034403c40b0000c1c5224200e5040900a684a000c5039003030303204040c0d00740b08c0a226510b0b07404a041c01540034464210844d05000d030002c16910f410303942e000e011803d200204081940281c05002e0150340c904011954000c00c0301ca42d1600345207175200d2805200501140c2aa454000d050541401d005000030f12589103c0d010540740694001e03045001c02c98200006102c031100c1c40010068903100e40f0640c3c0c55050b054a492103e40c00c203410506610000b040d1172003c16804005c000c14214501901940541c5592120380a40c012910007905000f4000002088030700e0080700000074201c41101191240f4081c20201c00a41007160070f400c0d25171801d5010182460000790340d01007100b005000325801418441c00f045448201a44e91030a03200341c980654803081011591800c1004c55030041205191407010410040c41c0a010320070103e4860324400e071101e52140c01590700c20f405440071030f0385440600e00a802072040200076 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 592394937 1250 592393687 592393771
    0x132007021215100605040302150714010911030c040608060408030705040f06120c0206060f040e1005180705010c0b0a18050a050705090604020c06190b060c070e130b 72
    0x400300003440c01e42c8503401030301ca18600129450300d4481c141c68a00c640d00011354001d030b814152010401010000700b26080c8500c1200c0c8482d40b443c58103034291034582c10112000b40d95030f2224001d50404100d85d00a600045900b44826032429402030345510b03001d0320150627040000006120a80030781c00311001054130300312940742143d5030b480041104101d0609550a03504000e80110298030001d0400d011f003000401c03404c190b81c08003013000002c10a40c3c1c100c2c1001e000b00801d81004080da4483c20348100e5081031038210003040c0340301701810480e46412542c103100e0701601000202c2c8072094001d034000300139400001c160f408180741281e0700701d8584000341248103c04480040280100721101256000e680e401c10a8480004010503406110820341b001d500440008114011280e4020a00c041d100d600092440d031010104000da03015009601c69584415820050714070b540b1102907000f40c1440d081089040720799607107580c4c101c3c050825480d5a000f445c2014100b56960b005c6042c65a1461907 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 592396187 1250 592394937 592394953
    0xd0c170c12060901051005130906110f03160f0215093309011808030a27120f08010e0709081e071e0501081008010c09051320070212 58
    0x41e5594441c1c080300c00441ea5400c01c1c01041d100d92000346100282c40c030060a403921034440c5074414000f400014800e0b20000e44032040b903c08841840018081e2032080400d0030b42d40e18040d044880300c0c41c81900d0300010407882c42000405158085525658000d0507443c0c0a070b140c0328640c8680c80c00c40c030740c001e000c3c5083c04001d00c1003565a0703d89036080d00d2400401c3e45256665120b911500321400005507059180c030685040700000c51103c000d69020000300c1c00001c4400120b010388110900e1407554040e1a200c00810100f030015518603014881c207549030020f00d05455910042065106104100c6500212408182058041c0d00e034003001d4015001101c483c0315500d07041c0b20041109420003d2213004404c4003291007405046404201d0b800502021002450003004480001c401045070b0411380020f50042142d203070a000304240410700d5614003030b031396007054100700813000d161030301018141c80c01002c00c21402498000303820f4041e0019042d03850384503900219820041302d43c000402c501a002c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 592397437 1250 592396187 592396219
    0xd0602040e0c03041509380a02070203120405150904020d0504060b010e120a0311031306090f050f030a12020a08030f040b07050a0905090c09060a1d0d0c170c 69
    0x8003070344c4110f0003900c560302e041100000034021500b04200191a404240750014032100007038840c441c00041802011045000501646041040586282d003503150005081420340c903040042511060002c40c0542c640b510705000070310f4640000f20701020800c00807a5129441c0d4450303054507405038a041c800c0c007091800303140c880700410054500c0f501103910310f459a805410306c0a8030380b00860310600204061000c503202500c1c407882c00e8108001d184820000d111017840c200240c1c0b001821181c9800040d1401d0115000c01049035030083c0b0702030b80042403032032925079002500c4824242c00100e01500c0c4440320500304d003006501803026019081c00018804924070711110203100c0e82c040c501929464171103000c2280c0610907000103000159104209101b6482c0c50001c3c1758020500310350181c07a101d0b0010100301d16811035101c01d004100c0400b03d11040208441201c090f4030011240e1140b68447d03a40e50454001160141d010840001c03c00840d82d0074040040950b0302d6001407100c0301600b2460 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 592398687 1250 592397437 592397461
    0x10203041406070f02030d0e12040815010b07030c120210110913090b01091e0507030b01020c0604050310091109130311060403170703060902030c070618050703020d0602040e 76
    0x1100c03002644070b020000f804581c481c1c8a80b007185003241d405980313001c035800040805001c1c850084052400b41e0000030300c8800210780104014400d06010301201050808800c540c0b480580c04004404802c21101c03000961084c00d48820a0b4410003c030344121071600100c0c0303090500003000c500e00d0f20f824030718925284c100f4023a000c4000211001000c400b40c10008906448640c2c50081808075100018000803099420a10764900040282d459103800e160304441a2841583c90344040303651181c0c12012568180680c541d910800d1703a00360b20305840c3c08003090f17036110040c50001546a540800100708054202900c00c000402030078490b0f04c1c18100b80c16415902d000c0c0f42200491803103480c810000c0c80124040e4410b035019100ca2140e07081c05c07907624205901c02440b060405036500d60118a406591000d5406070003441030030f0342c590025190060440300703060a4025903101d00c0121600050700044d405003603a5066614907401085441d0600c007900a40c1c02c50603180032503d0402445079918 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 592399937 1250 592398687 592398713
    0x305190f1d0a0308130303020705010f05220201140a0e03010c02010507120917090f0d05062a0f0f070f0308060f040b0d02011b050105040503031e0f04030c02010302070501020304 78
    0x801c0184404059030200594400c004800200401d050034005807180c1c5003840d1003a45c06000e420050301e015039a5503450b0846038500700001506503030748103000c42229050008410300824091038011074030300d83c0010340b508400c525480304d03003000040c0c2c02180ba4402c5281ca2180354010b4024001c0c0600398801078045c1008441140024034000302d8980481c07004d00800406a07001030b2004000c01e501d44078043c451b440020015001000f000d00ea40098031400da0100c0c1e000d001d0b4000d03010906090107543c004d1030503035404000c0c1d40c3d424400d03610008a204100d0f078420451601c0117a50304407007000111180100030004d01b00b18120341d201c0042c19006002c592040c20104c0c0d031080381c81c0c010070030082281c500c8015182c00c03200d1090010010750050b10101e05082c000146046c0b404400d2352041d003543c000b11012986500007106002842c10b40c0b41c010b5a409800340040300c414903040101083c040c1c0c00403c0a801c02101d42d41020659000350304403450b99821100941d030304d20386414111110040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 592401187 1250 592399937 592399961
    0x30d0237230a030504060c032a050d020a0201120510050d050705031e0a06050601050f0408010f1103073c020a0c0816090f150608040303060608070509010305190f 71
    0x2518208581001d000c9003181440d585512818140b504084040f24200840d00d401c07001d200740320010306802c0d00c11000c085036421100000c18143d01c003e03c0e1140c10145c1d0b0240c1310341958403801c82100141c1e044440311200001c1240000382a5a038455170b900c60301c449030300940d0410004d80100702071000128440084c4c540c2903040351204545d5601c1c00310040030309031003482d1682000c10b1800c00141c0d2a0089908030f0014034241e401c1c40c1a038500c401e05a80325a018084c1695210f1070445c50700c0107409142544c21a10381400c1c250304c1c194501030510940b00c541420044c1040c2c0c0d45403240c00305501c01c640501040791900000b0307031840602035540c4154402c2610240001c07032002030100c000140b03510a112000b001c189119181408c42c802a00c40141c3d41c0703401c6525050b1f14607a203c81c0c08103104c020401943c451220f41450300f0b0103001c48819030071541c10444100c0030401d819401c4021611148020301e4009125500c000690311924244484540018140700c04081d2071412a0025501040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 592402437 1250 592401187 592401233
    0xc0f0d08040b010e0603070308130e010905010b1608070501021801080f09030a120e010f1e0b0a0e0c090a03080c0d0905030c012a080301090506030d0237 67
    0xa095800e4400140844000704a01455001446030f01d01c1690141d402c414054200e5564644a07503078a0100d800a180c07071a9a44481d071801c01c9400008861940100307000901048254100903a9000c039215454010100d100801c0510040149080440301d036960440c00854035040200400c034a02c3d0321107505c90340000c014101007400c0d2881012a1806a90480e004500d0070103281020f8400519a1419610b00c0f503450000614a5800b800b903500607003440d0100240c0060504500c4a400c1e0803c20603406407031800031141c800d40c0f83d095a07142502c0e0200e0075101c07a561590942d85441c451203405603009804502c0c000704205000010701420100b00043d20340500c0d11800445a000d002d02c119541030344811040411035006680440040035180414888082c55454806841005080441d6900e40000040010006078403070349401200460192006003c80b1800968880013100102045546400901c400b911200c0702100e54442c204d121205089580c10503207150840700c4000322040d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 592403687 1250 592402437 592402453
    0x2d08040306050f0f100608090f0601142106240d03020708120909060f030f19020f060a050a0e0a051509090f070206130c230301060605090a0522020c0f 66
    0xa0750081c139588680f035003140c503122992416004881420018140c8540340c000c0a031525005202844107a020303141e06800300e540c2031602414042090032652090000c08186d4140300b01a003400f06003607070001000c1714000b000b005040c0a2030800401a0840703a4048031322070032101056004554441150620000c4c1c8144504a81000c1c42a101d65666607a11201104c00503580f460706117001c00030110050700b128403244c1d889038000e20700700ca0442120840c10000314580110301d481f11000011180070381c1d407030703041c009410701c09069406103e1081050100c2011007003102d0716440040701c001c0c02c00030030b81c1c1281d80301300180c0c0005900141c00c29001d0184007000904040c059800e040c010505c80d80145042c2c0d50311101003843c0d910107101200c4c0034003603113000111400f068500442d4214051700a122003101c50040508550140d400341080c01020f005c2c100d019a110001c88007150703400d446004031a807001842c45024448810000c002505c00300e880c8080b000d0006000411b02e02c0181222089 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 592404937 1250 592403687 592403701
    0x306010509130204020c0a142107030504090906141603050112020d020111150708010501022e0c0201020c070b040f1a0304030c051504050d0e0402072d08040306050f 72
    0x1e200201d0324440d250b122412250b00604140c0d0082c06e070170f4030714002da41d121003050ba500103110f1440c400d041c404e84d001c0301517041c9080020600514008241d41c03220f00e090202c0d9000f400a000714481c0070308107965904000144401600840ca949070044510745051401340c015013119140b080c20480000c0c81c0ca400032400276607040c5206401c9030014016141c0308226070044039000d45c416080301040c042c411583c040090b10502c1a03024611a480395000d66050200091900744186500c1c07405110042007842c8080c0c0040d40100240f10b01c1101150144840313105901a102d8000c3da5030b00d5100d0080c2c00101c00c90040d0180c000d4131180030783e0300d12080d40e80748401d42458003003072803461042c010408030700020b004013528013949100b042510445005905c0e46d14603214110f03010360b0650031615a031480580c2c01903443c0c00001040354114207141268031058100b820340c41c4c10070300c0265440c40c03a40c03155030a11007816a0f20740c4600143c1e5110381b40d103080d001400042e6412141d410110000c2400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 592406187 1250 592404937 592404949
    0xc020f01150e06010c0812010302090603060f011e0b030c0409060608070503070e1203030403110708010608121e0c0109060605040b180c1b01020c0f070513020f04090e0a0203060105 79
    0x20001c00c0c011241c0d456007012900c154191001d01402e043c0454a030801c400a91180061300e0b0340c821544e180a2290315500500142806c01811a44070303801913410803d0201c4140d240a0543d2107900505032030141c0101c03810780c654801c0d00440404c080100030810100f094030010001e4a651600038031401e07640c2c0c40241c5c0c0039035042da0810041141400020300d0350b842440318280000c002001001c101c481c000e030b42411944140c40c1500000d66090768160041d10820200e00100404402004041e10340701001d0386404844c142c641420200041e03805040e281001b25052024180301010341c2c2d4411012030034001c00802000300e6000b8107020380000c140c98584200003503c0700107469002182c0b0901d541c8140410018815022410700b03002d4003074984a00d501d5551090307406000140d90b10402d02c90305160100001424001e40d01c210820300c46a00c40300c2d001020308038403800c05621004c030100400480e01441d044011010f182076080001d402c00062038043c001c3c029000e03a05540d80700d005000c6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 592407437 1250 592406187 592406201
    0x15121c081012050a0c030b040323040e151206010f290a1106070504080105010e132628080106090b0a0e0a0f081015090504051603060c020f01 62
    0x10004500d40020050407103100140c002e140c0c810026907148294540d1074040b1140150015180c107640501000101900007811140c00d803074054814181201d6021145030324803640c01605e002c2c2c00240042074400d01e6000c00c4804550004010200e00b92110880954855091203240d040100c00600040c140d401081d02004800c0458080c0c00c0740c40307040c01764401907404800b1b100d0411400c6586000c240d0810b000c942c0c001c03803640d0396059540d883c0814150075134030b0680002d03024515400510403540c1c0e0a007009030075180c0c0041d03881d141c6002800a0145885030300030410b1901c00c0010440c026003095818030390304946d011302c0030215250100044641400034012840800e000100610280b8210000303040044501d14056200c02d00c43e00c089120055240e02c440c07984900c5260034000700d102840005c108219599041250012140003d6600400c0740b007503071001d036901e002060074418144103040c24401912038118006c1d070b81749405001000542c241400501600b0580b00721520103010b100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 592408687 1250 592407437 592407451
    0x13031b05060628060f0908060c090909031213020a09090506040201050d0609020408010f0b0315040b0705090d140c0604030807080c0106030c0308041a0f0d0515121c08 73
    0x14566500703014081802c101094100f80c403e9000081000010041d5920003d008299203c102403220104041d01120303e54100c1d041a4004200700402c989405003034800400f0115920102a01c235050424258400e40e542081d540710b444003003203180011001c00864252083c3c8808400c40d590b00020780c02c440c4c0c880c1c00100705820050226003d0742c0b280c009400e1968098200040d420b07a1040c040c070882c0e005a000d03800694444c02e10940d003010b0b6202e501e60809042e405400c10f0301d010820351210510040000340712142007008140303101d102d102030b903011600180c41007804489900f0003040c1d000c00049201058864402910918288181610206c1e0751000b8202e0604030240e4502040f41c20100a101700ca40d43e406002001c551a103160303000441c000c1a41c1d80e130b16800e004102c0710100011920140c440f508000505402c51060111032002c2e500d041d00240948a24668124043d680c4904e030f0340c0402006401c4122440228a1446000100400020710f560b8aa01504e103518111864 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 592409937 1250 592408687 592408693
    0xa0911060703120e0106150806030106081f0f06030f0f02120706140706090206070b010e0606070206041206290414060607230615011d0901140a030b13031b05 69
    0x40c040014a500404c082c0031400300086003d54941d09100180f107004191000052050018000c10382001e108020141a600c0c0c0980180e107801c00071030000010051080240b966503600301031040100c0d41c414406158003109038800e0003d02d041c0740b81e10041d225810380c03080701c0d11501034400c01d20024001c0112800f40d250744100c075655400048107900103900580312551101c81880041e070b2000300500c0f040344121007440407541441c0c000c00d101e041c000c4c20036008c0e0201f0049080903903502400d07201210151910303142d46841d54901240504045a49d50000d5400c9500d02c0091824445810084090a44003000040002e020b0b20166080c180c034040c0e0004401c1210a02040500004400014a07015040070718031482280da46012811107000d2500003811103408602e60b4001603404041100400018480034814005900d0702c80c1807242d44c070802c440d440c08040b81e48031503e1000040d604a1409109403400b880d4000e07140024140071400100086100c1462404426007074078059000001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 592411187 1250 592409937 592409957
    0x1200c15010510200a1415192a050a020c01050715050c0f070b01030605010618290706020a140403170d0e0a060c08060109180911090a0911060703 64
    0xc265006001c1c0c0115004c4440c2c183c00d40300c01c07010b0800c09485018460858485000c0380c00d0750382030030f122441c0500108062101c0c2808030442080d00d1003840c03412a03840014810400c8164083c101607901260f8102d07126950442c1a910780001c040c008030841e503029144402d00ba034004644c14403510900601ca10100125583c4001d001c3d80714130360007405d010529207400d0b2030035588910398200400449120a0200050007080b8090090600400c920f040072005030400200c00340f020b8401e030144c1d030300c05901d943c009146008200c0d124080c00d41d00604803a82c5441a04010340a5401100f480c008201c4025001000780c1041040f1012a60010301c48680c036421000600103651242d40341403491a00d6603440500c0071006c1c028a81c10b00d210703500014a24201c044c0150558500800e1503047c480244010000f03800d091003060b4800d0071034100010720011620b0301c2c051600c64480e0031508a1070402c200410001c10750b00846515014100c91900440c0742c201f0450148039000c0f00800280800c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 592412437 1250 592411187 592411219
    0x910050603130c1a1e040302063709030507080a0213050406020d05190c030e25090c021b0307050a0e06010e03060901090303111206100201200c150105 66
    0x3540081c502c110401c030b03029540c2c0e404120944103030f0b90070b5a40103071002841c00c40741e240c5420904282a24000d40c17a04240c5540c001401d1401544224100c8090701112816410141480c0d2203994110041c2018105c02d0060002c0c440d00346070004807482e100e0f0560114004100060100809a004180c02240d681c1c040b00c110140002601c2181c1094007440803001011003070040910a0050240159031344c180310074014140c48652480b90305051031320211a90507140403c0701701003810700c640c3c002000070700c40d4907894828505a010f12801480e00d4028889140c1c0400d038220300b1051022400c9038103002204045e1a040148550769005085180400c001807502c100c0c0340d80120141040380100703c10b800420300780881280c600032503075544e07039440b0304158240c4a466080780308075030b01900f0f03c0082040303a021444007808840c4210662581d03014094800d4010800818500c004c07041038829441010005410000e10320315140540c0c90040002918070780c645040381d20044c004501510044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 592413687 1250 592412437 592412461
    0x61a0a0c030905100f170f0c0f0702120601060801080c030615040912270311060304080d0c03051b07030207140301020c06191107200409021e0910050603 67
    0x460890500141600c00200707075a661131880c280f21165260600400d03100d4030024400300e050030090226054601c2444500d04034050350680c013101030302e40a0340d558009101807007036000d6100001e610640080500d010300b940403407442e04035030a60f110a24183d8851a5054403080c40c44e0301d003074266000c0340026900c041d041c280c080074241c0160000a0246013502c980300c2d004900300580011800c1c842c1c00c11524680407000241a003083d9000d02119811580c84003020000103509900c5408080003007010b03c0f1010307007114400500c2c00002c00074048600e00c050040e02c6c0480343d070402000202850740d25460040100c2d680c01c1d9055000c1d10301c0c541483c0340c103910380b40c2000c0c0e555055036007441a0740b05a5410030156000b941d03680615015070249a000205541e00c8006c13409100009101210018085000071000804008405180381d40c010300454001c0c040b204020354803401100c4102240d54070749003043d000310410341d041c2080740e0b16442480901e01d918840d45800010410000d070b0204003031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 592414937 1250 592413687 592413707
    0x1d01030e0102070f021908151b0a0c0506061507110102011104080a1e050319020309040f020c190213020304152c0c030a11060f0a02030318010b0109032307090e01061a0a 74
    0x1020527948072001184440d441078102100c9207011926003a820014004100000c5600c8042100d1a07254079030400c4144109015041005102c444490030307000960703000b90001000078500d04030f01a00c0c3c2c0c0c0da42d040d007661082c007060151903401040300d221035485c0c55404039200e2a81c00000551070508004900741d01e080c202d01c41ca100310b020030300c41d0600960351409005490040d2120140e2601008000c4d035040c41c1c9168003030385440120030113002c0141c45449441051540382c0000603281d945a0800c40c3c0303103941401c039101041f8a4101c0c01c0b007844400480c104d040d064848400f080002c584540c0980d0741c00e03440041707581503212040100000707008c410600704d440e0000c0c00480c10051208040c10054220703850440143c4c002100700400185210340d0074a043d10280c3c000e0000b10a001c2c000f80110030140400f404c0900c04603a450300000c481c62010a0725043c00c030840380341035600c20b00480184998040340038207500380300300000c044500c191525031549210880a1034500300d14019901c0d6155 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 592416187 1250 592414937 592414951
    0xc0612140105060a110f0321070215070903020a0e07020d141e09030d080f0a020f0a050c1f06180b0f0121060e0a110a1d01030e0102070f02190815 64
    0x181c0c01c0000e507402007807050898410400000310b8a901d0b040302c00024403101001c1007040c450b00e07042041140c5500007608103008040000b104082d4403009c17330031124506540c0020303411a984c0000000c041000804852050266500743d51610f01e2910040310408501e040000301c0960a20998044c0034680c81c00c103800030002c1102c6881d1401c0c0c0e83c04a814412070f404e0040204040404008074081e5002660341e228804900451038a005030070f0001c500c1c0110903940c02004400f042d0a115803800f0840702e1025003009004580d403c000a407110050b080c0750140480111903100c550004484a004010480400030b040c02c0118a0346030045803851751000c4410120a01280321000d5200c00c0c0c4103100c0a00105c3c2c41002252800240d680150303580d203503c03900180d600f04501075585900020f00800c054000c5582c04d410604000100c0c094140446440c04551001070f851041014540c41100c03108d02c20b0300d404d0106071100780803801d00c10041c8220706407900310310714482d12594521b0510f42d01100c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 592417437 1250 592416187 592416197
    0x50609010203160501020304060b013b030109050f0d14040302060304060b09011d06010e010206072712021002010b010206040303050c0708031e06090601090b07080f070c0612140105060a 81
    0x143d04650b00c2c40003240109441d542d42c0001400140303c400e01840342400c0c03080c00c104e23201c800c905040500603180d9544e8411508040354113900d0442a8060742d40c0740b140f00400034001c4010300e0a090f5180c0305108010070280c803a218000f8a118056480403001c5010040600e0400b8070f1a0213014030341e44000c1045078016600c0c01016007640da41440c650281002000405e20710140c1d04089181c03010280c1781034140305210076003060680e03001451650060a51620200c060000c2c00b0003d031801c50300b0415808040200c0010075400f515024ac903600fa03000b207560070042244404103038200c400b0001c110b40140c22003000a03001c03a003c2d811040e04040988005440c040042d00d414829400907100700798074248240303901d6001707035601c018540c00100881d00d200003424008000b84c2500c41c0b6100710790401402049132403c2c8040b40059a5610407e003082d150396029600d00420380c00094010000404c00080740d03160240c8847c8188045501142c825150690a060800240e82c0200546408001e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 592418687 1250 592417437 592417447
    0x120e030706020a0f09050409110609121e0709140705070c03080703030902040f0c0801060c1401330602100f021903061403060f060d031e0f0306090213050609010203 72
    0x207480d03100402d030700c00083da142000c44079042801410342c401d030360209110300e092a4800c40864549001a0300020341118034550340d03e80b0002040561100741400c0c2028020301200340080107280c0080d0300030100b2031094800243c1c858800204a6131040b541c941c40e21400750016400d98054001840498012000d60941580e40d41e40c1c0c0c6600d81c040d5030200c3c0040d444402001c11402c05004030721a0980111040c407003144918002000340405210301000c0144c4180d1450078000e6620000306101a500000d102e0004400000c4d408080d082001450171050022014140503515044c6000e0703440d151f01400b01e0100d40001100540152482c9071041a4200003134031410840070000e4801489a07200800c909180452200e054010007800c04d0003a003000703081002c144088400f02d98410340886031010130070301a04044402084002c00680d110004184d503801d280c4d041305c0c40000b40710480c0e80a0200e552545584000c0c2c0c01010700c20825a41e8444003800b0a150100182c001c1d1001881104d0600d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 592419937 1250 592418687 592418693
    0xb0604110f0d021209011a010e0a0f030f0516270204170601080f0106050303030c0309150903070c060c031b050c1309020a050a1a0a021e06070f0807120e0307 69
    0x42e03109402c081e044075400070710149522075020809900400c1c22000f0050031049226a03080f040080c0c0b030490410542d11400c034041d94034044080064a445c080c0d00308003545a140102d180c0c0310a80080e141c41c8540943d2401c6044003c180106030380c111041c450340110007403000c0500220188800030035940922010820320341085180b03419200400c01003406506d0000c4240c204440300c9a2501e059040060a00c0a07450003c00c5a030000006021285d696035215145030a140100780b650382102c1208050104002000015010050188000103145d542c0c58400742c45130200c07050010041244050500480b000c2c80071b607401000e002d14151064000304000080c0401c0c100445040b003a655000210154246001c1000217050269109050709050000d80800c001944c0100b0600c2040006c0900d5058800c0c411001483c50410b0b140f61481c0248503000d0301c81c0340c110340c18400100000c0e220520380c1e2141700841e000e000c9503113903c90324211a0812002424042100c0181c51200300141000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 592421187 1250 592419937 592419967
    0x60b1306032c0c130204060f0c020f040204063501090513060509210405222403060b0f0f122103010305060a0902130f14010f05030c010c0b060411 64
    0x42090b4070081d04681000c1e1080200081c02503a02d0140c492040c071007032003c0d0750080c186100d11199410003a007035600a10000d418001c0104000b5049400811b000a519400201100c076820400750103a85e01035140d078198032100005103451a45960440040101c1141c943c401a0002000200c2449030b101c903840f84020b9440545103610365901c19258060803080c040c8007140921a04507090b0325151500300001c5521051a904003107550449a1548802400b5800072030000a09032901000c1143c2e03410400ca81c0e13042e48003c0d940282002844511890111100d4812a04c01840c80000d40910f030127110340002c00e45240e05040c8110300303a0410303850010300000d4000f40070b2504c00743d0f65030547c50050f00303103c00a054a003410f0700307090b0f04000594400c00d280366081040c400010351030550400c4000600a40300c0c0601a45043e0070001c60145040c40402040d90002c0d0108c1c0c000408040044401d40d1407900007810000400c1c010130822300d800e17000b244840c0c5402d00c0107420940c0108980f01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 592422437 1250 592421187 592421261
    0x922170c01060b0301230a140a08010f0b040c02061b0f07080d091412041802040b031302040e030a14070c050303120406060b072a090e0c04060b130603 66
    0x1d1100f1010004202c4400301c1c0c01c101c640400c524032107031901c14405000c20003040311800b480c828410f07440d440188a4480b60030040040c032000c40281b11403000350303a42030000d008042465000ea81480580c406040c000500701e40921040d40340c0c111718828000d540d0b6500d0700508031400310044100091001300311000b000d0481e01483e00c0c1c0000e0204020315250b54200340040e402801500607504005510450a05035401c4801e82da41d0226132000404100001384501c0d04807800740b4801100344030780324824a0030451a0b510030b0f50f0030000091040c0f081640c0f0300070074541800140800070070700201030714880908805446040603080d02c644410000f0f0035078104000d0a40414800c40400c001e200340f500400e401440f801c69040d00e85603880e200d0622130a0881500003c0d0012070600da041200180e00090040510200400804010f11440c94490344042100307841a42807000114061000c3c500f11441900d0210b5060280d910b425815400740206450180e03040c40100000750080d21076017855a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 592423687 1250 592422437 592422449
    0x240204090c02010b090624030a021314090c03010b1b0f010612120f120c140301120606140f2205040803010503010c080906070c0507031704050922170c0106 68
    0x1280f540789040610040100081513148607602c187c20b00301c10900e00048110701407a09004442d600c0d42ca451801d4080d200c1c80810846840341c282d070004054501c0403103070000480841e100306458035180c0d54044640028002d01d203400b0010456080903920307330440c00c1000c0b001c0b5420b44c1c04003808407050a0850348c05521106603003580c60014000c110101c403c0c00b44000311410f04604400301d466005001c3d039100705100c24144c0c0e480446400590041c03111000c007800031903e0319602d40e103505280e51030b092804012174001d41007180204003852440c2c00c44c8030920001c0d0402c906095401c0401004d000380031000a40ca13480e1051104005900d40200b1384128010190980d5035407600d0145800c403019042600c00300141d83c82030185000c00800ca0503040b403030510f49002d2120f40c600300360341402040c0d40b000305075441500391390100c034a0f550081e2040f580c0c100c506122036a10b030408400c1302c50204559030242d40840c140c4000080207500c080b84852041f032003490521151250b0f40d400c4401b075030401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 592424937 1250 592423687 592423691
    0x6080f0304061b0f02091909031d0405060d0201210606031e181226070e0303040803030106080a0603081201210f06021e1201180504240204090c0201 65
    0x10320203190001c1492042d80c81d400203c034201683c50b29044d98003200040004d200e240c4080210f10034010315024104030341c0d4910350822101c00c180c074010300401801c02801e03080340d40000c0c01d49100d141c5445900c1c481c1e000902501c0b01e540c07490b0700444e8000a0381c106102c030b5810340101d0070703255010380c804c98021384010b0301d000480d07007407050b035945808029603180110142001c41050500030084c04a40009900c10681240041e8040058511403003103000d01d4601c607000100c8211222001d1400e6000b141c03d81c0b15035208485850034540c691107140a490000c1e401000108095849940c00e10340c016040440001c0441d22542c0e4034900c1d9100200f42c181c80a201700c01400400b10300304000140c000c0c0580030551031036007569010710080d018800902200e41c003050031b500045103020401c072121089500c17990384141d000d00c82101940f00f0302480b04018144509034500103c103101d40703402282c0050245000400010398803417107448501059401030f4003400700240d2103d00d4001e04822003815000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 592426187 1250 592424937 592424939
    0x705060c070c0e190902060d140103061d0d0f17040302031c0b030a170417070608010b0a050301090c0207170d0206160e060a1119020f0316060f020106080f0304 70
    0xc2c03408004070703400c40c25041000e40180700390800c140181810742c54543c1d81c0401c1d9030019000060250160040f5004003a0a1201801109040d19229416644501801c000222505040740c3d10744d500d0a280144030b502100c03581650728012800c440b4150783c140b51140c0c03a460a241c052003142c1c1c080c0c40840c050392010804428400b8010640f243d6401d000b02d003000035074230040001b0f82d9104010700103841310503811000d02d0010440812200540482d0184007504090911050b1b55100540f1072140080c103504004500150802c04031110000303d5550541164280341c29a0001d09070b070000c3d10294800d01c000000c41d1981803043c002246007200c003800c0010750300c54029007400002054078540e00220326944c04401e402040d65100003078155403154031203800d80410759020a02003e4820345100ea2a2030108503810300b007007910300510a0716034030648003a10040c559a038007149481c0442e032560380000e1101920030300001e900d2441c11310000c92030596841005080103d504074400c0541c1002030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 592427437 1250 592426187 592426193
    0x11100c030b0f03060c04051909060b0c070b0a09030206030a0b091602070e0615031003050a150b010c02151c050f270606040c031d0d030e1f09080705060c07 68
    0xa10210b6000503405801240703080c00800c40d451040d8021a0322a1001d407a50004208041400c107001c3c0041d070360200704960f03c400f01c0c10499044942c80021a101e266000f00c2c0300c00280e01034030107000c003545507000154255801c010083e0030040100300f00c9951024281510b986401400307002c0c990307090001440c000310741170003070404c070894110a0f4820180028020300d500c0d03054602842e400c8044003540c580d16a40ca03c020f040e156640060311a210f00c000060a000c010065544c06603101032007004002813100054444154020f400380d44090300540c01d0505d0704000c0c00400000d00720446600140022100c00b81c2141c105441003101011a502080002e00448090020168814000300071080c400006555200001040c560140d9250401d20b80014081d4001c4003d441c8040300c030030040c0302d5004155079100d404903034010001c0c1c14900300c0c0e48075690100d84100c1000340340d0001c0b0b203449010f0400a0103032a080204680c100c00030403d00020a00c01e110031800b4051001e600c51356454941 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 592428687 1250 592427437 592427449
    0x6140c240601030e0a060509011803080f060906010c0b1b070503030603120310090b010c1203021201050a06050f0723070e0619050f03010603060f0e010e0c0a0611100c030b 75
    0x7000070341407501d400310034191141c000030501030f16640300001040566078002e548e4098620f120603503c080c07a0140c0c100041540140141d44501900d48210100e980d4903800c02044a200340c0d1243d0120f80c0b12030120020442d0403040c00c1e80802031101c0054108690058850544d0260303805076102d400120600400786028402602c500b00110412815401c000d801520400f40c144600311070710b03649035105030349030b406100700710800e90f0002c80807482805d0b060b60243c023961001540c03002d48da84120010030341c1d103070880c01d11082d42d02c180c0d2440e06050441d5946000b903400b1200035603132528104654031142c4041c00388052800510009010700c40d01d03210b454585018080d000600c03400e40510540d0b06550a04c01060407600b08554080800d030b007100c0400d0040c801a080505041c1c1443d139226a080c00c1a0401c101ea25072140c000c0040a02850865444101c5514596807011a0620070001184101d1003c1c4031519000161060005c0e0501c0726400c07950280404000302e9141d500c0b03540d1760300e401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 592429937 1250 592428687 592428691
    0x1f18080a0804210c1104200d1103040f140604030f1202070804080f0d0c02130f020904050405061503030c060609040c0e07030b040516080403050a0923090702030a050406140c24 77
    0xc1d82c0620000c0104507d03145107030005501d00c040d190300810066900400ba8100c03080715040c0002c05507032400c080c03e210688100314941a6000c1950803825020048005140352185d50182e484005042802e0800c680e16000603403e606113170b80034010f4802041410004200a00c051401402e8101100c09060b0414018101c0101030046142461015885020b084880300b801c0c0c07400014038005640c41c0c03000a0046144140d0000c0c0303404100820030070b001640600400060380348440c814952010540c2d64858000441800d800c80d0700071614500308200e81941083c4240e50464002d502c813003181c41c1d20309003150440c0000e40c0320b01440280d4140fa11540ea004410503a01e00e200284207075010740f5010000c2c000030100b040004900800c1d6100b0049400035100302c2c100100a0480e440718035071841c090f8461540308030319407800304120314000003c50388480540d4a400b418545480030139508002e43c2c00101c00405420004849011000e0001405290004030b05160001d14074030110549500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 592431187 1250 592429937 592429939
    0x306050612030706110706020c010b0a090b010e0f01020c060d02091e0108160306080a080301090c0201090201080112030c231c0903170c1f18080a0804210c11 69
    0x4042501c00510740200481e60f0590700184081600844002e04149611034064080c0c6401d1021503001c004900c103420002c00c0704c80460b032640000b030b00e603a500000c440554003580d010904000102d140b0341004040700e2031b03920050042e2600f51b8401400b040d40c0340d01c0480c001c00401c1d4001040b5115103000441800c00d0359000c5461461034070460b002a000600252800302070880c91036150002610070341003000601005401d030355802843d13141520407070b00203008503490315003400320341c040b00da10520a418115405a640c2c40150740b812102d03684074544400103034100980c2c14070000100d20410034812800e0300c2010222114a0100c024030f0426903209000d08110041c6041c0486a035484131200c01038030f4203d51000101b0246048011191250507044400f50007800000141190402e82a03a000c8ac151002880500142008240c00a400000082c1200ca081c001c06a0340f0703104000640d80300d845120b10351208042840b0840100e140c8445860005200030006810007510700015a14100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 592432437 1250 592431187 592431199
    0x6070518030a0f05100e0c0a23130c090b16080c030906030f010501020f0d02122a0601030b0a060b041a071b092007060b030a1e170306100e0d02061303060506 69
    0x4a03000000c0e900381c50f04d1007000101040321040549d050340c1c0c010107280c613180007031018150848448407100540b0703524404902060025100251403504501207602400801004008880035035503184c02c5a045031142250710b04c03040c0103500c5a912024015405003038601210b40466141a00091400100b410306401e00d0b04400c540c1e051945e00000ca030010615015505600c3d8826010f02040e0170107170200c0e031219610424800b20388a0400304255059901940301607849640340e003440d0003070b00c900784200106010100820021080a4206000c02c480c210144501d002c002c4d864140704018a00740c1500c03000842d00003009041494403404601000881b65003a0300c0d404110f005507940615070029103165143c0042c100166020300103002016407000c1300700e144200014008481051603501200c400041540b00c0709070300d840c007064a100d0440180030750b49440c0000c0d411079035102640425074000e0404a00100181d54450250503901c20004181c01680d2139401d010046d20b0b070207848240200c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 592433687 1250 592432437 592432453
    0x150b0708030105120a050c041d1b03062a090d0219060e040b0102060610170711010f1e09060b270105010c02060a140405130f05010806070518030a0f05100e 68
    0xd04081107102c1c85510880d030000d005101c84c0070f054441359003542c250226025030ad0b03180030407017a001401289040c0c190102c400301d41e580b1011004030f8400211010004110800055010560034014400c0c640c018281e03520410155021039035002128854030040381c0302079003c0c071040c3c0d402131281207101001c68081c42802500b00000c1d40f01d040207001c090180c8140409008550700403641420b1940c8030030104500c41c54941c100601d02220641d503a0034650034154440c2d2001d1450041009400d0848240091001d42c2602c0318014a036010084031100c0d00d5040c4601035a1307171030192020300f0710100c400040c10200107003d207040c901c1c1600841d0602240e004d000003d62505000c1e50880041030502c10024441d010050080380119480558004c06803500b26608104035041352092002c20882401180d88a00d03680d92920b00844144000500920600000c03242c1c802a80b206c00c44094251001c040860b110032003c0c510080042d0f03410703405039400354040c02180c0b00c0c402c0a031040c000138000d90 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 592434937 1250 592433687 592433693
    0x9010b0904020918040b011503020a090506130e09071410020a200a0303112b0509060403050706030219090302030a032604060507030608010e070306150b0708030105120a 74
    0x103802031582080c000d5a000c26076035035688507820250421001512010601d1034240741519030b900782409400040300340041800a000e009000b41c1d42580d0160702c1c0c200d406400c120a110320703500710000032190b0880303038900003800741c00101850780a1381030710000e04035140c1003c2907558080d4029a01501445c2c114050b400481d60101d580c4154036030001040f00c0c8941c22445c00311070280c0245550f5804a5400000020103070802da04213442c40c0c000d400d4410f215110351205100400400000c500808025402800b10348904010240a00000c022030300302074690721581c2c90f041c03050b0450b40100340e00090184504007003030710503000c0c0c1c0020316014602d1070565000c01e80341c0130040b800905000c05685640915003010785602040380410601c140c00c2d203410305025026000546448000c64031b04407000c50f9541040c054680f0300400000100a058515a01e4400a0401c400785030b20750708c945103002c150300c035444005006c00c074007608200d5283d504060400001652000c0c0082090740900301c46000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 592436187 1250 592434937 592434959
    0xd03030f0e070f0e040201050403140c12150408030c04090f06061b030905010e060f0309060a06080a111e030601030c030303050c1c0c02010b060f1206030f100b03032b0b0901 76
    0x240c1c4c104410030401c3e40c40ea840180c2c0c09025903080200001c2480c605060886000280200c0c1c601040710020020a030754412183c035000031607046800c8800010001e4041038000b001560006d00909aa0b45800e40d5240c40e60122041d04c0700f0b0400464840c4420404aa0700002c100011034444045900d040001e6a001c0c100100c82d124803814071500c250740007550381d07440303080d58400e0161041141c1d032841c1200c502d40c0c90740c50840d025280d107860628046060f480006c0c0c5600300d6580f01c1c00a20703091305414100b140b01d03000713201d003180c20f10888800f00c6c0c00c7d80c8041c40018000d610501c0080181411881d01409442000384031006944041c0613541e4400340c0c40644c030500603441c80b000201c40320400030803405000120701480d0008000542188552804002071a01500c0744c0442100c81e01e56500309604c6075506272240300e456000701c801d040c103045c0550140c00b02000c01411030340340120820050385580610717034403c180400c0c84906220f10f18042d00915419078412190b0030f0503036040042c6001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 592437437 1250 592436187 592436189
    0x31203010f090507030b060f090a0f08030d05090a350306100e010e030102180906061224150a030b0a03081606020702040f150b090a0e07020c0d03030f0e070f 69
    0xb280780e220000b0030755240c001d50009540b0500a42602d541d0400070244c081e01d94010000380e40141e000c10000901d501c101e1030300c00b064400780c1014500e008000f0f10490083d002c0a000444980079050741200001c5005003604803440c81c050f05230401810741c2c0c2808040003440d1800804880c6c0410401060341e8420009050340a1103041c00c400103101000100e035094035148070350350158400911a0803103103401344003901d050012201c0c0011540e404090000900130481036006c9008040003107030856101c0f040c861201041c450b04403006030300c28400941801d903c114442c4071118000f0307803200c0f03065260058840001003520802c042a07d103990740b5030383d481040420341825911038088000c10803207030102d500a5800503c18480e00800c040c0c08001882d00361040141d0a9801c400056100e10319030660b80303014401840360f002c0b50703c0c0581c02d001010000744030b901140581a14078610b031f9583e00b81d000c03d490207607074000b804403a141050740445840b5905440150310110040013991070581d4020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 592438687 1250 592437437 592437449
    0x38030114060c030c0d110f01090804032402040e07080a0b09070f09090207120906020d170705160f060612021e060f0a030203091018200a060e031203010f 67
    0x1a6a403016103040742d0440c091010203004a001c0c103801e17081007941c09000d201302c10b0206410f403840b440451041e682210807050f0028a1010240b10402c01b084076510360244a6a082c4900e0405c402c00704151000c9a0042e0400050900c944050190065002d99920303070011102c94100b01809103200020303d41c1c40c0041c50001005aa450224484c92240c1c040c10010105000d0a5450302d01a00e09004d0101d26001d03181c00103406a40005840380c400560120341e8081d1740c0702c42c6014403020b1418040c900c8001c1000003404020400000500144040c0030900d41c001c41c810901104e8600e404019281181d01401415810403003510159542c84c0141d40c03800c508051103c00c50a00801080c2d080c0641c0c0c1d6071400d03c05011540868454154000310302c0303031600b0000c0d20884000000110308455003c0d68581d008542e080c8840f00194451031640071003c00040243c810380108400950200581d03080f110000c0c280d0050b02480703040030400d01110349084290141990f040c00c0f064854541c261080d9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 592439937 1250 592438687 592438699
    0x3020a080a0e0c0d0804050a060c06050c130b0c0313031104050903030c0901030f060e040c0e09160603020a02071e060206010506030708220209010608070e0406050915010938030114 79
    0x7540805c100701003110002c0001501c00c0d40455900c40c0c010f0140c400c13030202600c03624240800201240c150004441100c1700300c603184400309040405900240e00040d1840200d440108600460800301100c04c1d0020340c450000681040802004c0c07106455014000c03180e02d500a1051205400d151400c0c2e401404e404c4c0b800151002440ca030a01c060150341c1e200d880d440400e8000e00052003203080c00c81c07003540c0f2070591291071030311012007190303407600c0319805209030515581d030910109100e6002050ba6880078411184901d4442c07a0f8242d41c40c200840449015176216020443c07260140145401002d04440b0103013145042c10b805458180300034603a510716601911180815441902000c03202a0041c11074036156848910262441400782d400c9804210080d501414a10b07040c043c01e03054400141019509860b1808007502003610342c001c80c0d05100d0130003804501088120035101204d55540e00e40307000d200a00c1c103400c12244d0030941d0851580400c1005100c01014401e0710054807400381da42d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 592441187 1250 592439937 592439959
    0x50306060706090b01080102190c0f080a0e19170303010b0409020705030717040617090d120906090605060906060310060516020916111f050714030703020a080a0e0c 72
    0x700c00010f258103100100041c42410003c40c104805602418402e800b59005490a030200c18090b03070035a2200320b004000e42c2071041d102000502035005003c9103200341c01d18a1107107074030b200096986801ca00e9101502640304004200341003003c4012002100200060341c82c55062552203c01c40c840d601401ea1513580000c0c0c01c1c0c2c1049070400c215410b1b5508445950a1400301040e447c4a40e40140b2400d40007a4a201c030307407070501c1c0d86a40c0003070141c0450030041c070b42a8840101503a81003400c950160a140d82d820036200800c001d4054200d8851245a00045c0c6140100c1000240e0402038286802a0000d00c2000b924221165404080d28020b04000b61900e00302c0001001101d03ca510094014040a0a000490003000c2104104080030b0302c40301c80040d1940e03403540e51510307040418210070280704140d5030b00c03c949a000e60b82121451504001c10000100c1a0b01241d00a0b50328100280d40040c0340709040e6401460207030031640300394050000345400303241e80350303130f03074411509140f0540301100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 592442437 1250 592441187 592441193
    0x1413090201020f0307030306090b061206010c02031903030501081501080d0c080405220509010b0d24050403050a020d140403030f030f05090a02040f0501032103020f0f0910020c010503060607 83
    0x803025001a0603c01100e81d01c20703c51400034064200c9203c1c43c002203040500c0740c0c0081c6010300a849103009021910b00655441100444845001e170780e040c0d802d03000300d078559102468150031000d400c07030082e1404682549800f00e1545082041e2001180300c4018100622808001080500b9a40c00c40e00d0400d02d0030000d82000300303080c0300300e0703102960198401d50300680f0007401450500202000010030041a03481c680c00d1030a95400074a0598015101c01c07051001a1007440142640300d00365014049a1403620903007421290141c40c1600802c802099280710300d6410424000703030b40c24170701c0d02c101c2c9000507014007145401030703000c02024800c3c2d100c81c1d981c0c054030a070710000849041c0d40081c8420f0805512054a9017031000c416070082c2c0c201412200004014080d0f98100c9a20030300068082c85d58503030507030820503a800d5640070182c007080441041900381c0003030700000e45500c026035910041e0004006100b02940c1e041c00943d00201006102680c000f810b407a44203000b951b00d0313540c404440c0b07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 592443687 1250 592442437 592442443
    0xf130302150403120c0801050a180e24090d050708030606220819050a0602031e04031805190510030f050f0a051f0302060a0c051f0501141309020102 65
    0x700800e010071000c207040200b8964050650318840201c0b444c00c00c102c90003c0022a9555000d004207034006440480800800c42100241403100b00c0150000901ca068410400d0914018601042d0042a20f01d01455808020f007240381d0090101d000401c921200c4002c00341c800e0040c00c3d0040c0030004088009240d070740710340341154100549802401e400c0003001400901c8825640a50140c5100b140100c914060725101c003202c595800500411203140c9555070180650f00041c94003000035200e1743c1600c1c890b0034009002c2d0245100352155541e50600c0300020b0b00c01c3e074940e4070452003618040d0881e42c1d10720034640403400361130041d02c489040c500195006d80250003401c1d08440d900d480d040801c001c00c050403007050b0040d030201109000a40f0f45610b034070600c0c02071f004101032580c03030ba0714100014584403000304200e4009092401002c031050300c4482c10a03200c0984060890925481d48040c40100e11420340076220003690015082505408148450039240003501c0044d5a1060315007507a00030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 592444937 1250 592443687 592443703
    0xb091303080a0b09071e09060e09040c0308040b2503050336062202011b060b0d080a021e0a020d1505011e140607030302070c0f0b1206090f130302 64
    0x2404100c1d10b0708080d44001d103011001c440ba060769111b07180f42e41c1e2400307210724424022a05160344880c500c40d900e408110440c07a0252044641d449d40d141c0c000000342c5248080c0c4020600c541d411510385080503082071002228036094000840d100c050b440009403c60180d0b0782108040301003982d07140310081000c240c000e5043d000306c402c2d40e42c28000501f068000171180e1103a403a40d44600e000c003100150386003440c04000c0000b40410065030f0760360680c0700640012002140509804141d04210102080714200c2d080700541e81c41c01c00145099410b03804000305a0500380d4466003444103440464a151079900141c4000d1055400104000034030a00720040070180d40d1420007003281c2d59403909207007084a5043d09040c030103001c00030001910204852a48401500585405d14222072584c0c01c4000754001442124a1441110082407205015005401800d194161981c0c1d489a1221191500000501c141d2248101d10100f2149129500071150440d00e948884440300741c7c00c0c42d080c0d04103440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 592446043 1106 592444937 592444939
    0x1a040303080c0c071a0c011d06010b1c0f0b010f020d020607031e0501030b100909170f0c0a050319030e07060f030b040f0e010b091303080a0b 62
    0xd0b210081008014031015911416110618512a00c00091040d030107040049600d03150101c0920428598821041d00e000b036041401001903650481405416045c10010640c00e040c000070b41d581070481e01100750b05101c5a0b001110020041c10032000d41400034000031320519020b4004500d00d4000c0009a0192581d40d80b800010350143c81c1c44c400039164a5103180701015151032034401c050181d4401c480341501810002208078100805803c1050a549011002d0700092014451141d48407402c071440c1c0e0b2a0107006520600398001c03100b0030744480c0903d248040400034044028004030659140c140c07030441001100700d044441000d0060442d03802010180034940c0112620b02142380c040c1380104910504002250a4800c3c40b070311040102e03203030500020901e02c20f000e103800140040d650300007240342442c6005140c020281c0d002d030038083c101000c00c510742d480d5017129441001c = true := by decide +kernel

theorem cover : BRFrame.Cov 592266187 592446043 := by
  have h0 := BRFrame.cov_init 592266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 592266187 ≤ n) (h2 : n < 592446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
