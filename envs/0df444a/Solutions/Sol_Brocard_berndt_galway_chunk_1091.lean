-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1091
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:12:14.884371+00:00
-- url     : https://prove2.me/submissions/95e9149d-626b-4ccb-b4d1-4aedadfb7965

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 196043165 ≤ n < 196223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 196044415 1250 196043165 196043207
    0x50c01090b0a060e13031d060a0201050105191d091e03040306060f12150b10020f063303070e07080405060612100203090c09010e090601080703030f050d200703 70
    0x8401c030194041500c14051b858241441e0401c001d072200d940704218241c102354420300005030340d43c035a641900500d040f00c60546104110001d0152802900e0b00c1a004014120385003880f0b0450b50f031201071596410031401801e031000c4002c3e1803050001e190700c010b84100c40c0d51000404004001c0c6c60311440008012a41c1c10341343c0307241010713803047c800e101040011b04185498400503000200070781c8081e01050000b08410303240706003680041d40707400d0355000c8545903000d103600240d040b81210000711b441842c041c031862100d07040b4210f5890002010031500e9050700c1640004a41424242e480c1030091415441d88061458146013003444d2040080c603503805142c00700458500e0090001300100e83d0300407001c0241e225034903602c18500e070410040d084c80d44032a194000041511100003068041e215420940c4d0f0700e030381c0311040c0e15035514007032000030300040c249030342400c0740f600c21005000788180c038042c04200c0d1940400b42c940781c030322550345086110b0000103108007015001415112040500a404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 196045665 1250 196044415 196044421
    0x120204050603071d060c0d0e0a2402011b03020c010b12030406120209041d061b04030209090c041a1305060a0e0405031c0603030e030303060a090c050c01090b0a060e 72
    0x840c00354000640003a0904c03a0f0041000014405008100355243d000741107940c9a0b1206002c150380c40400c410001d01150710440c000030b15013096240030701501c03070003400110050300701c3c00402007401002501c48215540e803e900c41c1c01140c1c080c804403000e1203590300940c40d0a46e11250500b15540039900504c6140356220030380d452580441034400712002420111071007552141628080c1c0300b000262648207180903000c1004610661208888090802c2141c1895540985455480e540751000f41c1c00050107010402c010701d4809007441e4003440c070400384d80c0c800503d440454140d4041c1d20500c08016040c05c220307406400e0144103001800100c1c0d80512160901c1004246154100d0280c40000780401d8000b40c03d1040400445000b0039154560b03246031810401100c0080c2540d000880018625003400d80c01d41c40c000040c3d07402020018409812240b5003041180200300c032080940034444140103e04076180e00384618101c441c00341102d45503d03d04603042000b21842e9030000304040c8490024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 196046915 1250 196045665 196045669
    0x20703180603150608060103060b04150e031b0d03090312210212040f0503120a0b0901240827030d06210f110a150e06091305100b0705060712020405 65
    0x10714001c0711013078182641d03030340c0794000101e0240c4801d070000e0240503c002800900200e400404d0f400c00b5880da5104040e11080208040d201c0d021160f41c02c400d081e01054480491a04900382444103200b402c04143c0c1c40c0d40c0b95215062010600f1000703012907001c1100441416003903120800c0405442803c6151408070f00c403202ca00000a407000d4151000d03d00e421041141c20011200c441211180c1c685151400d201202c01030030401280300e0003a41000000517120440aa002a00690660600d294600002c008417003402c0010400046850348414403003000c1c401488002c250049400950350707401d0b86010560a0350b00b65800810404004080c0a110401c0144100310665000709240550802401c0061a498440c03c0c0d10386e00014000340050340700c0882101a0302c0c400c1c151201012030031030f081005054000c1c1da14040e08210b0884000c0003220b851f034040c03903000060120030000d4989440c90041c03150000d41040311303140e1250f03091090840d0440301c00e409250400d80158901810040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 196048165 1250 196046915 196046951
    0x10c1a1e0709061b051f140105010e0d050c12160f0f05090a0f02030a090308060d08030c0c190b090708030307020709020a20031806090d081c020703180603 68
    0xb01e98800c110145145011341c4802001801c000c54000b001c4a8040c00c1144071085442c24150311814403900c3c0c080303914010b40921507900d0495405031610101000000c060060310310554400320740324050882031207416a101c014142999000ca0300400c00692281040c030031031a11908600213000b540c01d0100611a600e8466100f5240261020355081c1c82d04d540034005030030740c842585da00f41c0c004010001030241b2540829045400b07540e030451507403030b11014841d501c0b041d80c40140590000700001900c0c1d02442c0c00900104c0034503000ca41aa84070101150741103504120104c500f1107403072092108400c3d042041c0c83c00751401070050352443c146640c1c00b941d6000c0343e10a0720803040d000300c2d500700c016000d8661010035840030040406051045148030340c407540070701c01140701540b582010b1041c80c00c0c040150f8400000140c4040b42810407904c0b90740f1142c0103150380110f14032118160b907090503950300103001114881d03100c031084000e1000d445625280381c1e0b000070040525040b12030405032034600b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 196049415 1250 196048165 196048169
    0x60e0103021c08041512050a023a0203010308070c0608070203090f0f100f0f030b0303090f0303071e030201060506030c030609060109080a0503041a0408030a0509010c1a1e0709 77
    0x2c80c2c01c0442202c92401d04441d00075a1300103c24000d02d40b82006449030042c1c02d845440c208180f080280355602ea100710200e01552031a01b4000000d80038200c144807220300c1c01d5440b40b22501446040d0407107942c1e804240c1e4000d802c22644c100021801d0820410b411035000081d00c1a82403c0c07400d458803010080da83c1c015000c0c1d4501c901d44a04000c039840e04c031018014075a090141c4080383e01c0310100b1000d08081803149071100025081501e000312940329116186a07000004d014601d40f071040400c001104c0300c10081a64035000420644000500305040146140724000074010412402d050107802c460403907016030302404040080061984903141200e611943c21690103100d40c8880d80122900403441c0c004c0071081c840c02c0319401c00d00c04000302400c11902d01e60b075040e0490f0014294035101d4001c43c450489554030074044680d0850148010b081996410300d0402086440e644a4101c1c50f8401d020f0354001182440501801c5408820303600004c140314030405d140b0381014180104022518 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 196050665 1250 196049415 196049449
    0xc150f02091f0215060402070605010b0304031d010507061104080607091701150b16050d11070f0302010206040b0c0d02070b0f070804050607051809010608060a0602060f0c0d020d0e03030a060e010302 87
    0x7813000200c260b070b602c1d4141c1e4607040d0030032410000740da12041e00c101c5650050b01c080d00815050707035451103801e80ea1100d884038904103946150426030103684040c05031480410769201c0030300900c404506c0740310400c10b440c490580360341d4044c0040c0c941081c100d6626401420301c12240d0411030390405054840d05603504031401d8441c0a42ea9041f800240030300940840070091980c05081d140383c00340c0d0742c40400c00700d0701d44140c0180c03411195148072102c1c00c1503641c4002400360b0060030014010542c0481d215a221181c4c2030490700c0c1c00c00200c10301781260310090003200c0b4945c0007000e01c903200100706401c5600002a04050145060503242c19648100c006c103d042000400103012a011001c000c40007400000a00081c20650b116100038026031011100c00c0d00403181024000340c1c403071001911300d0203801d0901c02c20360181c03901c0f00c400c141540700420000b4542c2d007c00c440c0004c9051407080e010ba640c0c0020145440b41055030038032051317904507130205243c08030080045c000341c1d80f00d0b204441c40702d00d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 196051915 1250 196050665 196050703
    0x903070f050c0d0b0109060608040b151c1a0112020a090b0303040e0108101b120b0612190f140c07031b21030204150c150f02091f02 58
    0x30318505a0715058103079146036080301d005000c0e801001054040035042e2213208800f4056280c80b0030302202d18000869024181c010104081303800400402c152800a41002d08a2111101100809203110101560480303a40c0c3c490350b40d0405862407a207140d401341021b24809102c40e4150740000300300e1092801f0740707118543d031600c1d0071103940d50400c01c0310000c00d0f40c01c41c84443e9603940c0341c0c802d484881040080c0f01c0c03e0b0500c992440010541300324200c1491341501c8120f4503210304032848000b001c44001060b0061020000c2c111103800c0007008510821200c8035003c2c005414000c4c02082e030305c400321070000c264206901d6600e414405603044d41d000c1800250140c4a1841e82000c58520360450390958801218110362000d106c841d10400d0840c0340c0410482124080500d0b0842c100d10661190010003003060b80309240780c1b413040f030b17203400c105004901d491310181018051900300c3d650321140d040f01c140d001440d11075909050100c103031820f060b214542035038100d501d400b075112400f00c0c0202c0c2d60965 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 196053165 1250 196051915 196051943
    0x5010b1903060503070308130801020307210212090604021203040501021203060303040f080a03091e03110102120a1d0a060e0112060b030a060302011701030519080c01090503071208090307 82
    0x1c442e521a0000740001421a00d07030350341d40e00700520981d00000d0010344484600d400030450310307030500850b8090142360340c58088888070381507000325a1400c10b10900c0026020081c20101040c90070100b401580e4420292a00e82042e10403c02d01000c0802441c10300e40007400104110b03030700410303491800c41802101c41c0c0e8a50340e91000a00354032854005408010140d1800704124000085441402d4825213900c20f41e980c44d0404100c04549482a915030703105030340000c6c800141c455103074100311a41801103c2040c5180d02e12200b29401221078500010301d0400000c0090b0b8074196050001141541d500315981d00300f1400600e00d0903200340302414800c0845260115015540c8024010700440c8003480e16030801420401c061300071382c88140d00041210f10080c0b16800702c03500301d5040b65032020092080f084074004084020070002402e50343e545c0d0500080c000300c1428001c40c41613920940146641d1801c600e0b05e082001202d04a000400c02c0300d20801a4200300001102c0700c40d508a02d41e00c41c800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 196054415 1250 196053165 196053167
    0x1d0f0d05060a050f09010501030c060e1804060f0c0e060a140c010906020912010c120515030a111503040f1b15030e07080a1703060a03080c060a05070305010b19 70
    0x145404100400c00e218000400107a502654841c0707001d6507407562a42c0e190707280c0000c968280e0b0350a001c0500b000c500c03440d003088901d0295aa02c000002d0280040076070051503030312540b5813442181d0a03150030b92106401c07082c2013964419800814800c7c1807044031120641c001c0348481c01515040d40a1000d03800c003280c80340c6aa14140c921412504009000002051600801075041036144a0150700e0368050703940300110600980d100125075941c0c0c1c1c52a81411a560300180c5000741500d440501420300210403900d083c058000d805018042c50070341c5c250301e1000d1050742c14044e9404905c4a50034001e100000e94200980740d21300b9044003082c1140290010b0000c00d411543d4460b1000360039540315a01d155070150808908810503800f40c684482e41d03072010b5a1107000d40c10001b441541d141c05c100040e810050003454100502800f20490740e5240da40768000c650005408000070f61209040000040c50350141d60f030b00c1605881c0502c0f0325450180c40d204140500002c0c517505001c00700c1010111 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 196055665 1250 196054415 196054429
    0x102070506040804050102010b0603010e040b1f030303090209060f0310090203010b0604060c050c01080709050607110301060e040b100e0406051905010f0e160806060a03020405030d1e1d0f 82
    0x5810a050307071194109450100c42c1640580300b6035016500340301c141282440d0940a49040b20301c0540c540030661b90b50354902d2041c1c04010110310035000160391102070000100720080296100f6140011201458010000b41a000608542c03040422540d8000c1607140840e800c180003589900214850006100280c00b510014082d142c1140011a0014540c0e5100e41e402e41182d0180d0207940b03404003114011a10351070115203035004210611420011414641c2c028032140b400380741000039015841000900391151640158070055864040c00103000441c2c043d00d412003580c03104c8102d400d14041c081105020001c10243c40d203542c4500160740074002603548031034a201d0f44020082582c460380340c4449000c1c203018003086019110006000c00b039022011004a48198480c007181c0e0759408204032055008402102c100746d024407002480703850030002d101c1c0c00c0c210b90301d0f00c0c0c6d07400c0302099040a0b881c0310071314200100821a05030042d0401c200344144000710007621420840d03220329001c2098 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 196056915 1250 196055665 196055677
    0x1020a020118031e061a2b06020a0503011703090901060f03090605101d130807051e0d0f08070903020402130815100509150d0312020a0f0207060302120105060304050102 74
    0x522110307a0a903008146104041a8405214820401140c24080c0c0c54440c0e01000340d01b81c54101c4804648019441c21210640d0381c5c1c0200d030440039220342c819513210000c0ea0003400308a404070b24003000511440c6908141c08100004120045061800c40c1c80021048071040c4102c10512482c240c400400758403a403c2030302d800d83c100c08140900d09155800080321840d601c0303000003220700c84211950300d444000100e406614003414174249900c25442d0759134541c3c45110104d80f01d00c10445c0b94012101c403811146000031001e00604035180c00c915010340b51552186030f5504100c066401c0140c80c1b500301c1d4507002500e4040d80d00603100d90301449003003100e01c3c40e0707005101144a03041c561030100e900c400c044c600c2035881506018903a80d484091045040080e129a20b400c03117245c0d071500007800d0800140841074005c1c81c000d043c1c003000a03001300403a409503484900241e40048000d41c0103404129510003055685000c51070150b034004807a040400c1801810321420b000030108040c05000d40581701 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 196058165 1250 196056915 196056923
    0x30f19021908270316060806041107020f01020c030703030c120c15051b0c061b1207080601021c05070b070f05090f0a09020f030103060b010305070503070f0c0c0801240501020a02011803 81
    0x10405c04155403034210540c584904000945500300061050503d4015940c460752000b5009003060107907400c00c148190326480890462003054480c0306155000c205880040d4003d40b1900f01c8007884c1d0401c3d02c00310181c86522024030203028488400125810412400394400030070016081c0c580291045103101e082810724207030040460b02c06040040842c145005a005012603101c1e2060516101110b000315000c9144030074819000405143c010740120758442414070640341d03400800201941038444006103040081c0d0007203460001c019940b0403030742c0c1007560303400d10480001c00079034000e01074498840d6407030107200c10906180c0745884000040300609400c040030f54842d103400c1d9210806030001d2006541960400d071030f801a5500a00c602801001c4580d543c910b11f540e4424144c0b10442007840c004c0c2080440e550b06e80114180702e04402c0079104400c001301d84d5500d800d0303a03142940500c2081d407460185400041003107a80020301140c100794207091444620049004840020390303a544054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 196059415 1250 196058165 196058173
    0x31b0f0602030c09031e1f020f031303020c03060f0c130305070905040309090c0e01080c12010314010b0f0604050d0c090c1e0507150b03030f190219082703 68
    0x5441c80d83c54050030310144141c04841c20100302c0d0034403000040424405c1800d039000550602119200001c0e150100200501c02500e003c0011504141780d900480c2d605100c03030300050f00f44d02015814041030b1400c69040b001040e890800040e81891700d24050a100c60480300014102e071400d01c440018801140c000e001e9426031075903454442d02404044030210b001400d20030001c160540d8a10492000b0084d50b03a50740902d000c10b0005440c08000130341007904000042c080088402000c14426018501c140208a500301600b100c1f2802d4a4508000c030307200f41c021036203241960304e50a00340d4049460480e020351950f0300e1030038550382c0c410064001e8280903080c05401c54a40d40c02c410100016202c204100c3d81503110ba0074116210b010314074009040d840c00c40300d0b890340c01d0f500d5003055003031000c0102940d280c0000100c8191007540312050500568500d001c403e0369098050000300c0480f80020320180307075a03841c0d6841e0300d0b040c410348000c000c8012102c03140d03d68440e01c0e2010740c5031760400a0200c3d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 196060665 1250 196059415 196059421
    0x40306050702120c0c090703060b03070c0201031a06070f031e0206101409060d0503040807030c03060b0102030408030f03040f150227031f0908130806090a031b0f060203 74
    0x40140108079400405442801e40390744000074200101e400c24103000e40601100401481006104580500800101034503aa400729001e111000114000c601c50380b1703417400d8000188000b6003a600b200607442c8400c051800001542d03268403044409032a071042100190210906d0141c85038800303044401d201c0d007841c1c00700c4210940c0000c0c10600500401e995644c8a1703640302d42d21401c00320071008007600182c0150200b60282400b1039401c030080d20501c00c2c1e07420292150705491030501c15500c107032000300601c841007050060303d200b8023070a40c1c000e1000d149003c0c100044036a44e40728202151070304078000070014081c481404007107102c80c0d601400940342d0140303980004010b17401030400c5017014040309602c5090710194110303c800b4140b014010344080e6036505002c0f0744000107041082182501e466010000607907100c01004000202e1200040403410485440c1c5840001450721480741d114429003800701c3d4105090700c0500da07040c244043c000120b0325111560400040c4000c7c00e01d0700120034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 196061915 1250 196060665 196060673
    0xf0c1703010e010315020310030305030702070b0f04032303070206071103010614100c0330180c06020d0e060322032c0a03140a0507080604060524090a09080403 70
    0xd0b081c101d078020700610020b4090002550200c0c881030329141c0c550200800d0800010780500d020b581d01c20b10741d00581c3c83c1c10399101e8102020343c0c44140240807007070780094207008104042c00130020f84c400c44000401c070007851070a015940d21130280041d1240d42c0c0130072001c3c20003030480c920404440d8060001e1041659991601600501960316548140100d60401070300c1c2d0b104060034540c45826a8032016074818242e02c200b0802c1d040c010160348070241d54600340d0810458047c034000b00309980f200d90f81d03c01c22820584001d0701a07801c95403c541004903101078495000342c01e03100c0d07440c003120b4490b42d0fa150520f000c54882c541d41c8100d55041145610a42815001000c030070000c81d1007181d1501d420036021300081000c080b0780400e0340c01a401c071003e00200c0e0700740388a584041aa00200c03a45462507440d214038000182d440400d0783e910020402040100d9400380756003150aa0307420b404a5046140010080290821084d004008200001d041411560400d025841d00032400b5079413551a414 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 196063165 1250 196061915 196061939
    0xb030c0c0f031c06050301020a090608060406121a0919111804060609050117060a09020406080a050d021b0f0f0109050d080702030c090c0a11070b0d0e0705010f0f0c170301 75
    0x320f000000d4540380c000601403d0600807600007801965800081c00d05004054030400c1005e0030507500207a039403001258042d600b03601d0b07812032070188031525a8040c0c03000d41c07501c0e090743c000c1084240740c00605103003085000501a035640c1c0390303100d15510000d42000002c01d101000149605410300e561206000920105600030000d44010000600140c0e894490410086901d41074400055001400283e01c02c0455404800c1c2c1510040000c45c403d43d84015003450710620100980d16074000781c00038500d03a41c040021400790461a601d1b4010440740d203000506134554807800c00c3c01203840010305d45007684030703c51140140030018000c3c1200c03850b60804203415000b8010403030081c428003006205629001e0041c5114440c007800e218039007002c022040394400b942c806600114411a200402c030170113100e000d40f6201140c12070000d003074100c0b0260107160540c0ad502007414001e02d51f8080c1f841e12b034000c0d041c0e03007445640c3c10520000b001d28906040e200c44a800d1403003094201000128407030300988 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 196064415 1250 196063165 196063207
    0x2030706020313051b03030a051b0f2406090f0907090c0c0501050c03010e1303110a06020a031503020102060c1b011103060a0b16140c04330b030c0c0f03 67
    0x4012600302e030080030828a13102c072910045d075505078001c1c010400381511850040c60000342d0414840e00890b420f034070107480c14012a13400c42c01e0b0b4201814046400081c0f080080d1007900c0080381c0d6510b802c012003c50b84e1204081c000080407060072000a89110080000000a0064000070403c0c46d0b2142c400408002411200300c03150f50810300450301c811403e209403030503580e414078003030034544404001c0e0440004101c000c0b02808032106048941c0c400034800404882d0152a015903030700e0f1282c800404907011349400c0314290048013024000360741e00103055607000740c881d0300440e9034050f82c80310b104c01c070306081d445800d030307582046925005020480c02031801043d0130f99000440f030340c440280e14030074061400c0b82c25100440010a00110308138074640b13401640034074107841020300f80002042c183d403072004000714a450141016003002042c12010751142103142943c080036418540390a01074070020f400c1d40c0c0c3d61807001c15280f11846040c010040e0302d00d94081200c4d95104210700400c0c04540003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 196065665 1250 196064415 196064423
    0x50f1810020d090611070909021215061c11010509190b0403050606060f22030b131101110a0b09071e06020c0a030b0402040c030f060602010603110d02010906050a02030706020313 78
    0xa40001810390040d1721118000300c004024000b80c03424409150000c00405005a078800402c0098003030900c81801142d4102003150851041442d0a9080c07116845101a01d201b40940c00c03041000490400e280c03c2030b81980c240b0700380ea038484180c0c00107580368400d0390000301c5101040c840051900301000040040328451029a50f5070b40d94042040614044d80380410321003c41001aa0f42c461300318059501214202451174005c03079120340340c0782c0c480f4a049501b22404868152000140030044400e14031540d424a4031050003190380300740540f2184403100007011441c43c0000300e655807109007d6a03010b0f0a134850100d0403005044107000368580d041c490034002d4010880100b8003400c001c400302040d02e400c400c2140141d183d0342d0a0000604071407040c4400c256950600098030209402808001c00044d400424080e00b1401e0208001010150a034410b03680a280040107036044145c0c201100c1e06030800d29115640558181e04500c64104002d219601c00001c21020b200e1044200b80d0b11401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 196066915 1250 196065665 196065677
    0x51b120406060e01060210111e0a03050619090906090209090a060b0f0d0308061207060203091e1005030a090210090e06220e0f071d0c0307050f1810020d 67
    0x24945040990303031428055480160487c00c107644500406800581341445400a41403610141d000e4120b82c584407102500b540400010703005000b59410b0144035005502101e0b0144041e103250350840000c01c44d4840d0010303041d01c5021800500c00d45070301c4040102d801070810034262a24035603850300c409801c142207401d42e103052503481050510401a0884a00203000410b2400580e1000d680741c650003000641d01c481904d4003560f2010342403043c24003c20081c0c00035030700d600d102c03070420207a00c1c502c1560240c0c0c1034041c60a043c141e070701d44140515007601d609040d41e807500c3c0d000c41100a0300404402941061341d1300001081540e005d96000c00300c1e60703c65400f0381141c0715101040040a40800c1812500000440c07400d1441d02c00e40c03015180d028400229000f031015414000d0030800d0981c051306080310800030300301840280c003512550081d100c5512500d103240c0302c074020b0306501a1162208400001041d800d00f4401d61f43d41e00100c02c1030040686504e440e1101001b540c0c1c407421440040007a82d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 196068165 1250 196066915 196066919
    0xf020a0e0307060e1c05010912050c0c010305040507031205220905090d0c1b0515190f090312090b0d0c030e0a1e1719030b01080405060604051b12040606 67
    0x8420745400383c0001000300004002602500510030030000c46401baa459584c0b079810b1800108a502e100c114107004e0b03100c03551952040c00c40c241c2004000c56103141810b050400301f10000c1c0e400b0441c441501e03805403900220f10984882180c00d80601d180392100c03000038070b0400e0401806460351404039030009005114540d51005643c0c3c8642d000c3c0c1902010607005c802100c0090b010f500d202c0001c255804480380203a9440c40040c81403122401903410800c40020300302e4451484800a034010700a03414913091450381c4002c0185400d0b5640f0014200390003010051700080c0c40b4015010040c545a4102a00c65048200c01402050701c401c031034001c80d20707103522201d64607008103044c841d01d604a010001003828408211001055180046401c401c8010200e5500341220014013101d0f03186001d940d101c1ba10020000e012512800075035810302c068030080100044000840303e0b48008243c0d00400e2070780b152001e2820585400d900300d2901100483d248104611401e415485103000d0002030003216 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 196069415 1250 196068165 196068167
    0x6030b01061407060c021213080d080f0411030a0212012f0706020306060d0212011404060e011202031c02100b0d05070501080c0405041407020d140901030b01030f020a0e030706 77
    0x6001020340b00c8500501c09100803420342e5000c1c1e200c10306180195681314840021220b000d40c8501105000b00c9440c4c071060103070002c2040106000415400c000e10740d400c0c16020010002c80c0100014200807080801c50350603101800604080356014201c4e83c240d801c0c40c00154060311900e00d03150405849065031440110f21403000c51a0620680c05252903c0502e4032080040c0d403008143c03d82007441006114600c4441d0f100800303000c83c0c56910804294101901e0715403012015031275a20030390400b6400e1102a40003c602030443d00c101500701b040b6060340c03001c20706004440408800290041040300d00c0b054000c1040d01500c07080e141704004920480303080000078a00c50f500500103521907a41031015502a012a5402100c0b0a01c1542401d41e5080003900b0354070151b6100c142a07070010140101c640d0100109070000080e03041001d02e038036018900b003020b4003400008904140d1620100e1100f640203510180b520345548100b55510468014050b004021448856001c3c1c0308440340007502c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 196070665 1250 196069415 196069427
    0x316020109080d0c0302041208071703060901050f010e03010f020301140a0b030105310606030b0102030c062205011b09050a150309080909040b040506011208030105270a06030b0106 79
    0x20310760007080d0a04143c0c1c00180500280820450380c1c0c1815820071001c80c3c1c4103002c81c6855020781c07144101c0c07940c07000c56181080082800b10442ca002000c1441070046580c0e9010000e819618182d031401c0061030f01c2c600403036400d10076580007600b551804c0d800c9900144280c0045040c1d074503000c1c801c03075440c1030350050040c4503c09105584440b0070074001442503140200305e00d192300c850354296089034070600803680802d0b80c10440c8000c0ea59a1000c0401c03a06402d4016480541401d0010b1824102148503c175111040201030051405030101007203103036892110320300300d01c581040003007040110030381c1c0983c07804116542883c01309101180014051410741c842409950700ca8008001495030308506801030229100120713000700c4c0c18804079000e03464540d1640e2181d400340b607115076142098240b0354240302c4180c204541070a200010103000c50350240c104c03411200305942812084400b040c8c3c07110f61b004050010352a81d09130405028411419812100981c8d01465156210303903a10700085d121 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 196071915 1250 196070665 196070681
    0x30c0203070b010b09030109082209050118090501020c030a091a040b0406030b01090e070f08010e070203181305090609060f07270302061b010e010605010e1207031703160201 76
    0x402c200c44005202808040c0080c183e07035170029002250600e842d03a54400207802650f40c0404110079802040c070500e070005600c0000709000c6504100c15410b102c032031034080410050041505454010741c03420444250f0450350b20320020410b81e5200d5611080c000c00000d10b80c82101000c14100744103070b41510140080b03e0403070f89412407940c40c2c249130100035400317042080d4209060200c0340f40c0010700203045801e814411201503940d08070300220100003401200041c8c20071446090820b041104564001003120302c61a14a480301f03000303041c00d00014610f03090070030000d03401c0783c10a000e1040858000492074003500c0b0180a55035903550f0314150301ca010f1030450350800011014003200c42001d5513208042604048030101410315922500811203981c03280e103000900c901010821810b5003005c0c41041c0482c100040240405440c000000700303444488090140300d4850030b1595011500304100ea000103640c01032070411065800c50980e01160000c48407000500d05a01080c1c1000e0f106100d5150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 196073165 1250 196071915 196071923
    0x6040507020c22090b013201051308030406020604050d0810051201020c01060e0a1811060310080709022802061807051903020102010b01050711040f0f1803030c020307 73
    0x18652000b4001c200e8886001d10b418001911640da00d00d440604501481002c280503440b0000e45516091895404039040110700c200e0380d544001c501440959608004103420b401d2034115154800750200748070140503540b1030406480001030000f01f2070340100d5503910880c0240107031041031000d41c0c0c0c00e5814210032034010030b10025000050206140040050f40034882940005090118002d406d03030031500e46070400f9100c203100b102001591030160040405010200b680c1e521184019541d0b0b035a086129592148159004800a00e05450040c80708005141e8402202c12507079441050b41c00942c405d40403400d0305112415688500e0243c2d102c000b55100e4a07900519882d50340d41c004203040c400801c09900c02d40500080021165214400000300711705410701c420b02a85144006800c44d040d4400b04d41c140b210a2101e2008615040c2c40882c1c450401c0d200400c02c08040c8007080c005000c05030307c240e080c03071419a10102109650f034841c03000740d200351801c1000c080c2695090b650390042d082c2c020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 196074415 1250 196073165 196073173
    0x11701030803010e0403030e030310030233030a090b04110108060604051c060b0307081c02070605040303030f090b0703090b060103020f310b07051605131802061606050604050702 78
    0xc044c44195141760f00c0f6009140c00210300ea07200c5652803d5520645080f140640188400d1055180c242d81075103d112070345441e41000e0048801100300070008641050b40d522010002510b02812a00222400f40e444207495a451602d0b03c0e18280210010300780c02c0c0015a80800994035043c0003048a003a14801014155144070701825144c20741903003e401c85e2415103072214120700b0303181000389a0103071102c1006494420308181c00d8007280b0a08100720307402c6501c003040801403140c21400b1502541d030035240124000790402e02140c041c054071f42008000e2075800082200e0700d035041e8803a030b680c5885110417018503202e10004405174003c0c40380f0700b03100c02020030804110f150f1001ca41c0700564842c1e08424002c07900e80410301055541ca80c80342c60018400074001c000c00c04140001405841080130b00c1000c1d0b0b0604000c90503502c0c0802e604020190385080708154421003404120500761700404103a60f55207500200000e000d0101001c48050781801c001c14214502801014070401081e4010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 196075665 1250 196074415 196074419
    0x50c120715211503080a0c0b10060f11030f04060c023a020a05030111121305030301030803041103010e030a170c03150d150c11240c250201170103080301 67
    0x30800030480f03841a0460001e07509800000038210310007030540c0085075143c01046038210705200407241c4005000c0003960340e40700001c1c0101604403209042c20b504614100403041c0000d20010b00e10310401c98410070301c40c1d0200300021000da10203400c1340f0140c826294290100c0c0460034029009450f035074241c1c411440d0b0003400d401c0111b201c402c0e8502c82d000400e41e030442d9543c0d0b03011a08440100060349052070300040c200024212600704c164014051050a5040c3d13415620340300e4036800107000003412020000045411301130480c3c140b010040008008102030805100e85550303950229280030b000c5085011b070708501130382c0002014851404050703000d00c0c40d500d05a21201311100254610703488100030b03507090003240d0016600c80229031000d10000305400c42140c040c2c081045030f00c41000e030380c1c030001c58030301003505003000010f907040f090030070148640b20010280024002c3d80001406076226881c004024042e003405211014000e8841c0790003034100c203500d54820b420034007010b0401c0e0010001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 196076915 1250 196075665 196075727
    0x923011b08070203090604120b16050f0a0309060510090c050903191707030908011a010e0d02030c030a0b0a0609022b0612050a12052104050c120715 65
    0x1030030b80c0200144142c03407030b00035403c00062035504071350040014168201c065000700204444010707003103e0b4054008035901c0a01200030903d01c40c01c0d00040201001140c601400b5000e030300f00c070400940c0004180300c9480c107660035044603042881182c040e07500307100031500400d0103142120083d0f000500030304102e040c02c8042d00050f0410401c01c507020310103803860440000305800030f044628484d0340c5541c02d592914080314207640c4444411a401c26600030400c0301030ba00094a030203510000d40700109800c4040c00020304102c1042c02441d014083c500c07a5204110b0f50001c854420749409000b003207034645940c1020100d0140d1103805180c0c01a01011044424050000341030152640d480070800031f8540001111508500d041252940d001a480004202000e081848a1261407400303c5c1089056010342c2e101411280340c50705685103034001f05040c0302090140d10000400580000c1400a14901003030f540c1d1000d00c0341032030486043c80740095007486208440b140c50294010020031000d800300c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 196078165 1250 196076915 196076927
    0x70b0702120708030d0c08060604060c050f19021e010c0305131208040302100305060a0b0f040503011b090e0c0307080a1b02010204060207050402030405060c0703120923011b 76
    0x909aa1141115000000901040100384040e1080501950b212601c0c00340c400c0641d515134041d2400d1221900c204030481d1104000d4070211040391414400100c1141080d50030002102001e0107103000c2c41c000b17045907801d49000008114400d0750030030030106200d402001c0c00c031040040e00b80025201940000070a101f14003600c6040200b05c80783d182150340e40c800109500030300400700c4d0b80c00d201080400c10344c03811a060b20340c04100c90030207122900e4500001a01c4403218054080e416002050003001c181c400025180a4230010300204103002c1d08851200888081003031210003d401c800010070740590203040d1500515003001d00c5800e649074140103039811100200305a00d12075403454240001c41e22000d0f00c20b070000c00c5800060342c1ea402c0170002030400c07860380c0000b40254010400c1c000014000652147e100c00001400707a00c0c5c40c2c5502e02111102d1404a1010400d424064240c040c020203140b2000550080704084000c50490300925080c0d818000c200203108401261406100b40151 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 196079415 1250 196078165 196078177
    0x303070c0305160c0905090607080604020d020f030a0203090c150715091b062c090402010c0c03050309090109090201021005060a050a140a0b071709040f020a03020702130509070b 78
    0x30401a08000d200e124076180588005400e03102950b440c03c08001700d10003807103034681101500c0f0140195150520000d803141c80040c040381c2c009d0758000340c81b80140704260f050760051071140c407142c2d5880c00c00c0014500a0b41055802c803074180a42d007001c903c1490089a442c00707002030b82c0103e50405600342c4846081d0b9545002c04141940c0703e151410000c1d00e021000304e40e80c544895200d00e083d090100c000c141c120841000c1c00c8028070a20f81030454060712245481c40e5004640b892503590340e500c0122000e2075405401070036926140404000c00401002400300c4a0003030320000100eaa07160441400c2d02c24401020f40540c12203070b6443d15807900d90f040a54440300150045a0305540d440100d0089a07542d403010b02d0700702155026090610300b014050004145e82d02500d82489000c2d1102d041e03041800748148224a80010010b4280e1180d82141801c0407401740115102d0000c00c0024020352300100c000c0780310f0318003a8401103a42240e4800c1a001c3c6000b0001881c071241000c600e20b8103a800a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 196080665 1250 196079415 196079417
    0x15010303050d090609050f1605010504030b1f080f010c02010b0109030b25030c030605090115120608032811060105040902040b0402071a0a1b140702030a030305071407050303070c03 79
    0x1880c2ca00003041c1140140d040b12481030b0010402104904521401c112040d4182c0b0340b0f074164113104204d27680e400000d68007a6500450714001540b2a0811122072401c5032011020741d003584500025124408241c109031415044002e00800f00c14210032401c075019620780c0740c041030380c0410501c00300d070756640056070140c0c2681c410490704200c1341d0300d04030010640b100600065118060855015030500503140200000e458091481d410500c814100800050500d01004494824414080c000781c02c44801010605c0c01d40c0c0d07850401840300070300007185609800842d84050418401584102e29217130112807000080d00350759082c603040102a0001301c8050781e0094403a0506443c0d65901d1004000f4a841242c920346001c1c0d50112401c01728038020445145c0c14580b0301e160030060b44018440050360034518010f01c0480c200000d0f11102d0149600294051051000d910308040d01540154041c01c4a42c0b03440140c501d605080106a00c07e03860000e1241d0410b002180d034013030061025050091103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 196081915 1250 196080665 196080671
    0x9031b010b03060c0d0e0303040b0a02030417040b04030c1202030705120a0206030108070608060d120309030903060516030b0d03020c06090d0b090312060402282601050f0315010303050d 81
    0x210740000707442c188042d1211840c100300051166070488480c82802c054000d5407010b142540f6280d125806d0f041c5c4003c0141c0b0016800000183c200280c401005156181c02002c01d5148e41d26024241640c7d0400d02045509044160f00404d51513140c411020700f9650080c0188880d900345010301c4003103403c200e1000308034070400b885c500060380c03100b000e140603150b0500100186c1b454050014105080a0030542c0609240441d400205004200c5550141c2403402d02103400b000b1882c044510061035440508210714020074002095051502c0d02846003265030705115450b8420b04008903c14003000080141e804882c0c0d1305582d00780200607240d00d100080141284c032111b601d0b118960b481c11550181d141e04002024070306160314040064101800303440450902640e8210345410700050500b100041011040c1150a00e210340b81101e1703000300d50044000c0c070500e003c0b590006110280a600d110780d0f00740440d503009050010b02800164403000708140c10740d28585042e076503903001f500c1000d410f9407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 196083165 1250 196081915 196081931
    0x102090303040801020c0c01210b0f100c0210050405010c0303050a020906070c03051009120302030a1e0b01020f06070504170c0d0b04020906090c04260115050109080609031b01 77
    0x901400640020600d0f0030002d0f9580940002c261b0400151000381410b0280039401406d50b0240d091300c0300045d900c01440040c45040101c0040c24040c00c01604a5001208046111155034081a0801401d01c282c1d07400c0c3d20b2600740e0005640301d0140c2d019a50010300b401c018500424465000a500300301400c8005113000f40b480b011a06036802000e0a031001d80c100340041041003000c002401c0100c680c810b0070060320001e03946002091000d01c42c0d2200b010340200120b10390200300d60104030b40c002d942c80c00c3ea07502c00180d114000903040d846140c6000d405540a88060300c140815603611581199413120310301800c1c80200c040b82c007405e641d00d002502c6080840c4140d43c5484031a189000c0c0101240042c5c0c0c946441001000040102524090300b406020301548040000070f803400d54200c224685560301c940d07101e04440303118040e54400c581d82004c1c1c00b0034100c2c90391034464090720740030f80e6044111922860340135924441560554103603801000300b424202e0050b0082c06a46201c8000429010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 196084415 1250 196083165 196083169
    0x1202070b3414120405030c04050702100e0d0905060c1e0a0b0103031e030207020102060f0c0903011a0301050609090a032607090f05010f09090209030a080a050307090e13060e010209 79
    0x1c20722411100261038510045040c8000c2240d04501d11031031400518007400e00020949860200121a000325204c1e00401c807210300034494a5030146c10610b00300302d03001c902500303541c0d03d48985c1c0c4502c004c02c3c01100040b4044c10403800319100801c0c24001404070a18070900404412118004501140906020703680010700e1040c003070340210300a9480e03c0321040c00b1244203100b034000070341e0402894410403401d00140d80210300c095011101000410207075842c2e0402205501c00d280500343c2c95441d00c01c407030000c80140e019000d8500b0091b0002c0095640342d109101040f181920a1246076000500d0200001d2180703000300c00c01709450000002c844104180f0000019050f00c000002c5014242c0034000101201100c00041000b40703480101041c3c00315001d01078200031b0044040760340d000242d030801ca40341000741681d6150b0000b41182c0c1c07504070a8006080da0410f40c1c0d000009015100001399400001c08010301500c40c83d40c5131a094441903640400030400c011410754195001c0c01003021039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 196085665 1250 196084415 196084507
    0x2060a030212090c01090f051f020c04140906060a1a0906070c08011a060a0e09130804080622021302090d0c2601050c0a120608070b071202070b 63
    0x2e100a18001c0c0309000c01d010000d40428547e400c004031610540030200081d68414054441140c000140920800400d400c00c03820004190800c98000e418031214180854400001c01d100d03010210030b441b000c1d03c0342800c1200002d034038410007865038074651030215102074500040c612240000c002515240090b61000415941540301c600140d44d102441c219400010344004100c500403a9078620380416207901a00580d03444d20071030701a01001c0005808100308003500b0842c0b41d0008146c030f441781da441c642c840d076840c011107200505c3c00b0b5032140c2c82a000040844040843c1c0d0040180040003800c6007c43d0094100d00c1d400c82d8024141d41440c40860b0b80c140e41e8102030f100d0141601003801030740494940c0d0314140182001540c1c0b501d400c02c100e9522403030554410840d1881c0040d403003026283c280014006c640c0220740c4a0059000c0000d0700003d843c01424140d100b4015140a0100000280e8840b5000e00c00c00050110802100001c58504080c0da4400c02d1080941c108203411800b084103c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 196086915 1250 196085665 196085671
    0x21c0c02090f01050915102307050f0d0903030203040e151e15090a0b130b040e060109060302070b0406020c01020d050405010903090e070c0213020c0f25030305040302060a030212 78
    0x41d805010014045410b103103c0d01d5030b0080b210311348480030991b510301046490009411140030410402908800641c14200b00c00c0b24600041c003042d2209410b042c05500c8001030305543d0500c0c410f501841e41800d020392007a00403207803d900a142414500010980420f1005054148207101c0d9071311003074160b0340c40c260701c52150b181d41e01005005c0c002005128546412840200c92182c05122119040d542e880b00d05041c0c649088801e84c48a8000b0080b5842144e2500800b05844000c0740120f100302d400c00c0041d118107400d81e140c840465903600282e0407885090340140040c0390304000034011440c207400034074080b811180014a40747c034a100e98021280191001c540c50b0351140011403c0c1988004078030050200b40500a00c5402d04400203061402011002070042c8464118004002d0702a410b55420315068403c2d07440c80604c00140545800d9a8a072102c466083d040e02c920140e0368000710709090f00c1d8991036240c030741810740c1c0801009801c003003640c81c10140c00f003014113040958000c440380 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 196088165 1250 196086915 196086931
    0x1505040c110601170303010312050c0a0f0203060606040e060409030909020418050c0c0a030f020102091f0201060e09031b0307061401030c150c060c090b0a050a02070b070201021c0c0209 81
    0x1000319602601c142001e03010790000c1c113440f4414068880007a0080100c07811079900c0130000d1180960081b068a0f6402540719400e07050090070551424400c900d070310310360a02c0c400c5080e19055981c20042200c240101e004e500541680140081c40071300b070a0b0300c5191140d000382440c2610070358030705101007a684070390030907038102401040e0307035091448600690380c12192501000341040e03180c0018917520704000c0405170410020550925206000b075049601d10b2402404403041000c0c078180c4844440b913011010030040d0f281c403c0c00915401414500340c050640d2502961030514100080c40100d058a90b0380510b90100b0040340d00042d805105d0300c0c40034071006a4078801c0d58903604060f19503140b07036400304805a10484000c3c8207070303034000c81c41648641e1000c8001202600c48500b00c9020020381c001d210143c100240c41e4450b40e0f040340141c5002c8c0300c95821501020b4540d400303003d80380034100b00240581c3c004607802490f100f49a50381c0070700300180e1800b0081030030140c000034108501503503450 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 196089415 1250 196088165 196088177
    0x4060c02070e1008160b070b0403030b13060e0f070207050d020423041209030f0204050a140114040e011109040c17070c0c05030c0d140102042319181505040c 69
    0x44130501c030480d14000c42044503405a032400c00c5942481c4202c1c240107080c2c00e1000d0003d410180a54404c44211034040d240c40040c000070071030b130401058a07005d4904644640300000c1d1b8030340e540043d541e2180425501030080b043c80e000a0052140c1c50400c200d0b4400d03202c0104000003003061901e12058064000180068100b034102021a840458105c1c401c00843c407005102080001311090f041e02e60507200003803d40d680c0010070b0014050031800d070034015101c0d40001010301d8121129843c120040742d0810880384940350050880d0100707800b110700b014003840040700e1446c20b036210180d00c8021303041c420f110600f0210600340142c411503130000032407001c01006081c0700186100c480600002e800810b802460300002444100000b50000d00080506086040f032210a405460050110308a1f8002022550209120200e40c14190b640109603a90a501050350380151040851f500c40c2c0d4200002d125511088000d0201d1407c1380c07062044240000400f92528403904245450b41c1c0e5505c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 196090665 1250 196089415 196089419
    0x3031b01050f090a110d0609021c032601090216020a080706021002160f080c0d09030b2d06030a021804030306050109180203100e040b16140304060c02070e10 69
    0x1802500300083e20035050b592000803c800080c1c00b01e200c1c280c000c1022140e032102841c06242c40340190800d100000c0d0020034410f140b11070885902e880709603451090310369041c1c2c01c42043c40d0500241e0004422981c0b00c41c1d0500401c2000040e0b03004001400441c181c0c0c0d902055650046151040d8540c828541607020b03180c00c00c50300d541842100c0360601c859005514242c2681d1114901302c0301c1d8400544244850500c501c10826800100c3d20f01e442c055040d40d15a007200e04002d000000380c3d200966102034250300140200200244d08866940c0034583e41c042440d084010100d04100203107400d41512170609003202580d10031135070125085d0580b07207071a03041c9402e10300201503175200e6001c641800f4082106001c1440194240e40a030b02113405e0040e2030795191a00441c81c141c20f5800340b007400c5d04c01c0083c081404600c28051f80310360340c0f5414010100e42d0394842280d090a10055102c400b5606001040010710700d41c01803000ca01171441141e10b903580b80d5622000340241694600034038030300c030041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 196091915 1250 196090665 196090681
    0x50604031107030f08090d120203040906050402040302010f0c0c0b0304240b030319020312010305030912070b16020102010e06090607031d030a0806120307060204030629040b03031b0105 81
    0x20749100805000241022910310354468131842c00e030250041c0800c20105204a05441e54010400340b1604075005908061440101030349030340c001c2c02142d5440b0300b000740c003281d503044c07500880701100e606940305030645011550807540001141401c862060907940d00080d045100b101460103240070300550113880e40281c0c00180c84040c000c180202507410811140050754010003611030a070042100101c143d50303051812403c500c1400c00c010310f031f5419070380040f0a000001014100c40441034406000500054003102d90b250040e105000724468100f0402501210b000b9020300b5581c818000807441098518105040103401c0311350160960191040001d602e07454001c80826401803200809400741108655807684034120503030082c800e0f040042907041d00d984a100029014410a81e501d801e19441c09101035807041c4025140d450600300e42843c034420040944490b0121020080c01c401c1c801401d00000d000a41d80199140c0001d004a421031160411612030b007040d008000142442c018403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 196093165 1250 196091915 196091927
    0x402031e090c0f0d03020703110f0904050f010c11100f0204051e10030c0509060903120c060a060b030106050702130f0906060302120102190c0f17181f0c080f040305060403 75
    0x8248201d4030345100e8800301b500440c80c0800d0b2a00500d40c0f8000e03048010104419601d84480c098010940da0108000e00c04041040b04803400400000d10890050304001c40792070426118400c05500300940c0060001c80590140d20400f000500150506135a00005419542c0c20300c8a00302141c035045448525180c08400840740c4241420200604040800d004207a401003a40040c00342e1000104441c07680d5040041d100310740c01c480310095840450010791030302c0d0001502c1c0c2c0d410090410202150314090f800c180c90503210030340c0e0f841741458000d408010940040120681c0d0041d03880c010742c10800c6241c09401d10b458061400480d03440e2462050000c043c02c40c050400342a44148080380c0c0b01962100304911440c2c407482d00c0c0c50079800b5424007010040d1101402460b20034103000c3c5041c4104c0043c041c00401d6541210000c00c4100d81d4240075100e4829031300d01050010724003401c0800d50007170401d5540d035401101290304104144a408a407588950015685540800100410168068 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 196094415 1250 196093165 196093189
    0x31e020702010e06040b0a0c0c090905160501020a17031e010924030b010e0403110d090504180c15050c0a0c050907050f0904090813060e1306030503090402031e090c 72
    0xd1881407805c0c2c60031452136034034095440002c04002d00c942420050041445100010740406001000081d25516159070b86079094003c4880928490100003407641c00419151381c3c1680001c1580c4031440180095460759000502c04585550249004501d8407002d01d8100d01a1501810028440b5402011400c100270307180d1b105000182c003841d00b4000200c100b43c1e51411959840e6070400b10751a6850280c907039500b513100030441c03407282c65045884a64001005800c41d076042c0d5040113440f0403003010114443c5403010150543c04501c8040021807200c005148031280a403404900b8402d900e8405824100a03c06c140c1d130081c1300071428000d038507085c10629000340060600c42c0c6031001c8000041303039901808030800c0c8032b03036079842080091003140000c40c1d80c0c140c0c0780e000484c04a0b8540101401c040401c04102d03000320800c0e01075004a00340c0344529403d4a820000950912002208001c0650f00061240e945d1558410a1035056108014041c1c001c07000c07240030b05000108030701401400c803c09 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 196095665 1250 196094415 196094419
    0x2032b0e030d1514041107080d02070c09020304050d0f020703020310090c21170f0d0510120c030f03050405060c0705040c030c0f120e030414040c05090907050a031e020702010e 77
    0x2802d004c2080301c40c40c113009040e0880c143ca0100c6d078841c500380404d110340580d0b80040c00c404000540404502410b030700804c480c602c21a8600442c41d11800071800720b010844c0c005165502454010a406008a201801f602140e00c1156060341c0c480e070109042916070801c014040d40c51711b00d420104100a02a54003602074001284980c10090f14600c043d20300a04024001c1c2c0c1181402580340681c800845070541100344c8a030740c2c0d9408038140030005000407140401c1c881c6903e040415070b03c0202141040f02c5801550102c00076080d038403640e2032045814800c8051280c1008001200d80719000600100e150b0400a05025464582440251840803500740304041c58520102a080c1e04042000001d007420f250030310741c9034610b00a00c4003d02452601007078900c004180024078010500e0b051000c9a4141c800b400010320120098500303006980311954403080e40400545c441e445507020308402007180c40d0100c2e03540d076004450b40000040340741303d80c83c2940000b00031040d541c003c0d5041582000c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 196096915 1250 196095665 196095701
    0x60a06030b03070614040e15091f0308210c030906010b07021809070b13050a1d01031202190b15010809120703050c071203180602032b0e030d 62
    0x34040080c0d12000c0c10300804e0140880e0005460300c0300e4000060314041c0c0510101d451260500d400e400c0002940d1a800300e01c06c03100345c00000c260140b0130001e41c6d0551005040102030900f1a520f0700d4840d001000204886a2045100090404c0d402031072030003640c3c0c5d000c0842da2420315035003090a021050b04258a0302c07508210400050320b9507030f840c2541504002000d0352a40f04c60030505d00300140c60b400000d81c1030020030403940c10380d950210001100c1046810960507643c4403249004000e40c1c2e010715000c0744070a0010404184800b40e41103c0031f44601c140e64028a03104903d24804240040545000310f800c0100081c154071066400e0b1590030900700340c45c81e4901444803170f40e41d4000c19501c800000c000300d020010540540240d81880c0081000e4031800c0e0307281d501c1411301d54202d01c01940040c4140030400c1e94450240006016107071244c0c061850507116600c0d13441d02c0c107880d00100e500d24041d00013023030f0030a034944640e6000f231034500c001d546e40e0b0940d0a148009e842c90498035400c0c81507 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 196098165 1250 196096915 196096931
    0x803070c0b09010902010c08091207060513050a03080a08071205090105070305071706011d03060a02030912042102061903050106030b0a0e040f1a0a060303020d091203141c05060a0603 80
    0x3800842c04c15030f10b41d1080c0c0c8549d6074a002400b02d80d07034008104509002e4880e080300802d01d01c0e00705000d4004a554200303003402e0a6900c804000041c2400c1c030019110700341c10080d0903a1075210f0350503280d0114603428030700c034514400107018088070012a9444030b030742d40d40e10504c0b00b0942d050240c1c40d080504c616107421140800d070700a219503800500142d052048007640c50101d00c0c0020801e1860720350081c10740e4000e1074085001c10281d03008171458009400381080d80c2c01540408801d40782a1500f03811520341c0b042d03100f260310210010f0440b090b40e00040501c0513204110304e03050480740c030350619a0b020840794076047c0050300b5114544c0700d051082c030a61005000d4800a03000d01540300f0340111200c001c15055040c013440c6081d00f80300024090748018104181c03403c1c960040e604a0784250b080300d02c20080104111222885d41c0580d45c0e04008400c3c80c400840d11401ca0789241405001441f49000002041c21120200c403032541804d0704d07200c104000700c525007a000c4d400207009504061001030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 196099415 1250 196098165 196098167
    0x3170105090f070e061204170a020a11192304111e0d15061b120f0e0301020c0d090909021f09050409080c060709240302070803070c0b0901090201 64
    0x30042ca2002c2c42c028000340145115402d14810070700d0140c642c554070011001c1d40b41c0701580450b03041e12802c1c000e0405001404144040307400070b05807640503000c040c15950341c001c24484001c844030351001c80b903640c0102c1e441010715a01c000b05070b0103a800c500440014648e030168084219128491440d10f8444c11601c000b910844281202094005091101502940d4600d00442140c1c500c7d4510700070802946154059200c0c05494442d21b50084001d04502c01c244460040000241a1030001d002e02210728007031203480c040f4503ca424020180c40b01680443e003240c021756154141d40d84882c5101c2c1002d42c00c1114840544101d000501807a00c00c1d03000314282d6481c0102040c0b20310302001c01d5109107403107012641c014203402002405424198140104140c004440c0d0f403882d4040c0300046141d81d8040c422403400c59040c4101800d00a0203c00b22010035000d6000f000300f49902000204001103228004521400c01d9071203401c030f2540705041c0398040280091030107103035a1404405401503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 196100665 1250 196099415 196099429
    0xc0705031e0d0f051e040b0408010501170c030703021219060209100e0a0509060a0e0405060f131110020102041a1b0703030518040e030a0e01020c0d0209061306150302040303170105 79
    0x140b60719604100e210801c01d204045506c6682d200001c03900c00410b02152001c1c0642010b030490742c12050a034510300080302c0c150b03165034034852842e501d580000002c20042c14103440c0070203030640f03000903518160444488040c00b80200201120710300e500040700d050514021400d0302a030240e619080081035141000300d104103945018003846111103000040480e85d0769009007000d045800500006401c207440c01d66640d680030350350303089260300b2000010f62001000c0d03581c488191b04a10360000345401038060051840081c00100110354003003001158040d48055599001030300120159079680c1a0324003075102c50998140c601090304a2402000402c0e849020b4030302c074034000c10010090b865900700150003011110405d241d40c1c00003240c1541a1034001c0301050303a03c1c2c42038081e60328101c2c1040402420200c8400003c0d800310316800440c0035130402c01d1f80700c2e480540701c900000c0d600c5c0c0c0fa100c0b07004c0051035242c00d480010350000350910070581c2c00012390746c04a9100e02010200d5041000099103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 196101915 1250 196100665 196100677
    0x30b010b0406120f0905030c0106060f1704021201020919080c03030715020a030b1c1109130b060402070b040503030118020406050f0901030b19052d01050c0705031e0d0f05 75
    0xf594841c0c00c1d0020726130140d800303425155405021640d0300e284031038480303002e808648aa200071989a000d0111110300030300954a80c1c20160000c201c0640c6c550f1300300b020648203802c28207103d650a10401c007442e140c07640002d24005070701043d00411403500c1d092502d06500c1402c41e500a0b0428030180000400d540c2c0341e07a00450b0058005a141c052903e021001000d2204a83e54401e130200c065080d440c03d00f840034801580070740f00604c103600c2c0d030205019800c05c06590008120b200b0b1525000421042c0000c1030304124004c0000d40380c0301454031160800801603c1c01d450913080000100030081e01140150080e035503286047d81420b01d84040600107000d14450614003450024108280c0d0303200783c0c00700b120303440300030a424400c80320f481d200c100c4c40070103001b000c0c002c08034601e030028041800c26100da180600b801c1c4034102c41c1d03809001124950000c1e0510200c91042200101b120f91303081c8415060000c040102074072111a0001d039514003100c844405040c401035455102c0301551003000c49403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 196103165 1250 196101915 196101947
    0xf0e040318091e09052a040c050d0b010e0604051e060c1c0c1a0901020c01110301140d0206031503070906080318010305060d02011808030c0102040e010e01120b0406090204090309030b010b0406 84
    0x385800704003401e06d514400705504607038010714046d000003ca907040009841941d030240402c00c45060000300640c0d0811205140580c010b10a01081155242001402741c0180340000002206030248001c281075820500510700d03981c00c80300c0121a4825141c1c4820030f81e075a1031810000e080341c6034460710000c032081c03c0b10101c410a82c000080e200e6000b5011242203080340002081051106407451105410a0180c5170030380c98401b000e0755240c6401900300401e5030f0000c0549156449002c075085640d448045000e0701402061000900c0054520821005000081c051652000c0f0f04038041c0a0783d69030440340f41414078080c00d02509886003150720b003c0540c203080800801e03281d0748030b0540400040e0b02c00e41091000180e03a1039045819009081250446202c400059072940144d0000140c24001c000401c03108105030b2000c0f48820b221140c0050107045c00150410311600405c0a4480425040e00403940c500e0b010000c02559015440c010309811071010300700f5003020002001c141e03414103440c2d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 196104415 1250 196103165 196103203
    0x11041406031e07030c020c010201020f0909060d1202150a02070b0a0b030106120f290c07030e041a090a0c0c151121070206010f0e040318091e0905 64
    0xb008205141400c1c040d02416141060316890240002000b5010890010703005016000003041554014002c1d25580c0c04980d032201e040c42d00302004e01101410040c0300b16403098580032110003007040341038070360b5543c84613501a140400301034001e43da2101d0301601d070041d403900c104140008910030842c0d5030382002004402180440001d00040c0c05483c081c1c00919400c1d0f5800b41d02420401d1001e5400209880b88100c04400c0e002c00803030700c0640c60025003408000000900203000101c103400182040b9103e42010446c030611940820122035041c1c5c40301c41d007150228038000e024504042e519600804500003403043d800c9911008000d00c2c4543e2004100321054140ca03c01200190840b0b000998103c3d5502c0d214160b14000c400303000c248032001c42c24200c7d03041c04a24414800b180c6941a2009a1000d1500a182c00b4022010380001001641046066010a00d500c09500c00d250f00502c51840080707020481079001e500c100140b6803890340c6040c6080e28110008401046240c07001c00d42503580 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 196105665 1250 196104415 196104421
    0x30f0308040f0212010c0e0406120b131a010303020c03010b030d030e0307080a0806010909050c0a0c03030f050a0e0111031306050c0c0d0807080606090a0326070f05011104140603 78
    0x6014004640c82c0000d502030910200c0d007021640550041c40009185d944240c001d0684205000459145008048840c600c540301003000c200054041030300050000c001c0d220031007182c0c941003040600c0003103040342003038204010414182d04114040c4001401c07802040344015030f800280d07541c0156407003c001d15865040d4088004c0092003500d0b88036401c0850300d0750318200c0000041520b64122001400704200010218080380c2c035224142c0b00b14aa07094940c40c05e0310040d401e40b40039640c4001101059141c0c400300740c01c0d5030701c1e001c0c4a00490308050080342004104c1100c500b503078140d44101e120702c1c1e810f000300684100f00052051904c2e821680020740e5480b42c40c080403d5200f80080308109118100d282d031481940815204d10400e0982c1d1404602d031141e0080100900c11100749641c081d18050091010413414000314144640602420031202c500b65141466a004000306036031100c0000050401d100d400e001e030700c0340b4070010390b50306150500700a1464402c00424001038000c50f008000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 196106915 1250 196105665 196105673
    0x1e0204080105101d01060806040e1023070903020409020a030501150512010e0322050901180b0d1a0601030b1215070c0f030e060702040f15090506010504090e0307080708040906050a030f030804 84
    0x40f0030369100c105020717100200c41140c2e880000d00cc0340303a07051840385110070600c45004401b007011802451550754000788140b668007004040d00e241c84c1c0580c0e00c145d00e581c0000000b1000d12440144411400b03111501c01d1808007080303030b440103002010050b6410010307038850039600442210101210f00c00c12600d1000e40b0b0b01a5064100550009a0802c0070003001207415420b05000216982c104141440151064003c2c400c9080d46030000410b8046422400680d221805c504070b540100189130014205c851900003840254026600c40c83c1508202c0c940000f404c0110951540441e10b070512403901da565a03a20310003261607903000750402016000406059540404903020987c005006104850021028200910b40355040c0e812108100c071000a4070942c90152501c41e490503110b81c6e040500d0191000013414010b511200540010040d400010700c045000d01075650090304c46135110f80c00e00041508441c810742005204003203400040000030125000003a25591500c1c045480d42c0340c03450 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 196108165 1250 196106915 196106921
    0x601060f1110020a050c0c01090605030106081e161106010806041407090606030f0c09060e1c0611030f0108061015120608031804050402090a1e0204080105101d0106080604 75
    0x1c5002c124a000048465440d0703402000342030030030f030f40b81e090710702c07241c49840190b030201814482c10008c51414801009005d00468203194402c144020200c41d8800e28007008400f0002100da00d80711b054004181650190f118003500e028080b84002440207505002000355a030200400007000910400c524644a0300c00f0300500d4001d0007030712070601640c1c0d1a400c0c054003600308216075600b10341c541501802010b01c6801d01b407085540544a030818400c0c0fa03801e00c070650b8a1400c4459648802c2c0034041d00040c0e2a00c00c1d02c0c01032140c418825128202900036504202040c0e0155041e03502207002c0c040049031401101c0704440343c2c03ea10300c5c2c41d10308802040c0c4101180c0555209040c1c038001000a01c8980400108042500d000e00ca11018080c2010081115410f40d40a0740100551001484103080d1b50f20184402101800c0d042e61503859001c00d08c00e0340c0c000c2e040132000380d44940c14011034522402c0702602074181c40056010b40400d046265a02050500c110010401c400b00804c1c000d40302d0358 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 196109415 1250 196108165 196108183
    0xa06051512090f0d020c121c03020c16030f0620120a06080d0801030b0601110304051309021306061b050334081e07020a09091502041205010e0601060f11 67
    0x802c0e00d13084094404081d40b1000750703d89840c05001d4919200c2e228200c0401d0103190101c003881440300098129108800a4202d0307040c00d181845078070386020028072040c00c0240190710850181c08048920700d000425603c1c4a48050042d10400c0045492026200300b0713110f403101c400e14000f9243c0d4904003060007070700fa01c1d0300c005120300a2001c900c0c1010742c44a4014142d900070641486a40c807a4001110845011004000170380c005010506c039901e000303041c141300c1c120685000f02d01403440740c0004040b81c2040415415241d0b403001c00708000303504074810507514003600b4103881600c1d40300d40342d0944a21403520300341004004c40503500c2d500d807100301c061041e9000e041c0610001c5002d5203803116060b4454012070303c0383c25108410100c6502d4403c12652810b60280003003400c00d291684480c00340c210712108070740c80038410b1415000020b45202503c0100810010521245800d092a07801c5911020559400340c20032001400026004a00c4850165141c0b8100b0981903102070703101d0a000c000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 196110665 1250 196109415 196109443
    0x3061306020427050108070807063905070e0123010c0b1303110708030f16021e130908090d02010c0213051008072709051002030a0605151209 62
    0x18048038070701060f00800c2c042e5800104000b048a40d0b04c42c91500e40e40e082074440d0720060350051500740006480790081151407031700300f100402c540d8450356071184004c40c1001c403260001448542c500c02c1c07100821501d0000d1180c1107207504a0f5060621142e54441a801d681207800f041151455550748240e9040c0c180f41d030440c68556072801c00042940140001c00015000504008e98a9001040228850341100c0303004008520349140f0900070b400315040640c1e01410603e148980801581f1340c1c04585d80175035100100d1100508090702000110341d4810047c08015181c0002c44000070f00810032510340003c1150b0080682d81e40744012100303003e400030000d400141c03107078042010018580119000f80070400c6440d00c5c07a0380b941e07031141d59902c5034420b5485503460001c60a910220980e41c00080d000c0c01a00414140388584a0516040f424407000c94410760000c01c11805c038040780b041c50b000c0c0404960791164481040c140c500d560003104140c080c448411030224803592000c1000d4240446d02c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 196111915 1250 196110665 196110689
    0xb07080705013312020d02010221030115110a0813090603080301080118050d1404150f080114090103110a1a0307020d0c0323040f0801060515030402030613060204 71
    0x4200c0c0c1c544540202410f4220098018003000c81c840e0880010030360a44000c00c0205104c40388a80800c403440781d403084140d0541c0201c84a0302601410700c01081c00713030140340f003400741d032549843c032503001c001000d00140c4104800b082215445030707008a9000d10003074010300050745501c1c5503102103004d40f502da4040c4c003c4d14a010303000810014004050741c12036140c413000304084400c0c0401210840e018000c010700c0381e0002514242e030580514001501410808e440c107050503140c503484807191400300d1100b0003042c0b660107008103059008440c1409800040020844100e044010401096040c0801019450300d0824000d264031000000c0c1c004058400c01b1b030398606401aa5240a80e1090b100b2034014080ca00781c030740c041c034041d0300718603081c1d0b905940e0081010f20000c109120300600b0308142c400343d41d00b0800010071811113860301c00545219400020b0b8185030400f00810501140303060a41c0300d009000b004090707a03001c6200f560008500c141841d403400e1618104000b4071490300010400706c9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 196113165 1250 196111915 196111931
    0x1d0a140a0908220314010204030f0b04030302210402030c03030f040303030e01090204020703091a0f18191719050613030c050102161103060c0904020703092102030717070b0708070501 80
    0x2500c10f20000c5034001d040004400d5014001c031030907486513001c05842c0050740c02040c400500c08a04203680035010b403070014189585070210340469118198060700ba8210760042c001035250500c001d4144034012401145400700c00c100c2c20140f406144400b07424140d440f02e03a0003090400390401c8030507642c010011503644045260181c924843c0c1d00400c281d00c207103075000305580790302c05040703483c141c8110215034181000d40151a4110b2006801b050b04080041030011006c1c1665410b00040c00010a5010051a41340b1565280211610703410401942c1c0e20300000116501140903a0020b88407401c21760f00e0803680c103081e9620486618010b00c03039031001498034607000c8201c3c03100d41103900c03410b2032002c030610b5a400c0640c3c892066403070703800040080103071045a181a6000f0240d0b00d1090400b0700445036504007200c11428072280b5010000442461107045103414040c0070f0180142817410240300c6503203400c1590f14201802284c1c020070300001c400051040c10020342e14015481030080c01610 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 196114415 1250 196113165 196113217
    0x1030b030a08030f0109063209040507081207020a1403070e010612060b070b0105130b030f0705010f0c1101050f28120207020d0b0c070b011d0a140a0908 67
    0x183c001c64100c80d4680c100d8001140007121030180404072082040034520b820142d00c512048850b08400c031a0ba401180c0d01c090b166511407a1410303124a00540143c12610700d4816418105041d60b200402e0307207142009201c00503034801c1d000d24144c4060705130304000e0700c146501107403406409401075040440c440000007690b9034010080c120080304c1007018016540c0d68900c004940c01040001050021100018850790030b02cae02554000c05070401000c10000380082c0842e0810300c4215018400d9001f55100303001e1960003066100c5210550718080c0014649600d414010b9140b41c05514100070000034925000c80c1103c0507500528202c0c03800b4a0f1020300c0c0840301d802c0b43c26007004000401c4881c020345140b054580309440229401910f0a01e6001103a6564111900014085a1104424040100400c004019460107005640301241548030213480031007002e44014040740407907041010021a280480350030307a030400181c4c800800c09035220719200d0518040c0300003d6000070b9950035110400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 196115665 1250 196114415 196114417
    0x50d050403090b281b0b060f060f0409110f0a0509030c04020c010c090f0b0a0c0206040e010803041d0709030326071205100602030f13030602030f060f0d020112020901030b030a08 78
    0x4030083c040441500305564020703034580000c5601034507074441e81c6101704040340181074182d42c0080000d18001031009844000b55003038000040b04001c81e403003c2001e0140101030b01c101d046140c9070f10406400c0c401011000080f51180150082c20458003080008050b01c04002e10300d0b10710f000420642d00d46801180b218020881da00e454800242c19800005080d0211450785007a9076400d840f0740d2074102e0060080d00d8041e1800b034101d0300f0500070080054040007464a0a01030032042024681e11442c4c011500c440c01c0b264100044100762003428030100507008520b52080300e42c141070441862000d029042000c17044003a50b0301d00300303001008007c6500e074004411107100040308400c200365160002006c40c80c03980341c000c07003001d68410041c010800448a0203046001c0001d50700402154a0342d0340d0700242d8006480d03011540f20308005128803460705000703035002c03070380144d6140040041c5500024028002d0351079101d401580000c00c26007607482a005000034080c040e00300c5041c0b504038a410015 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 196116915 1250 196115665 196115707
    0x2090604090b0906010e010f1407230607031802090a0e01050708071107051e030a05030d1505010e13150e09060a14040f0204020307090816080c01030c050d050403090b 73
    0x49143c1000009000f5809004844400345041e0b40b1030701c114403107a0040d20340010505041800f000f090106200151055000447c09013440c100389603400f01c107031101480c0000103400d900031706041a0040300048541c2c0704501038150119640c4c9840d4980a034410010040c5100458542d4208010001c2242e000307903006000342c545d5558425000b20350340d5000d40fa5100c500a01742c0c0404031104083e5081900044001d80c08002025900071703d20a40c3e0b09132035544079803507172140c8a07211105201400c8042000c1c41c010301080c201000b0662900d40050105034280040f01803480ea9a10325050210b181c00000c0080c22260740c1c441c0c014180480c10582e9207000315611703500705043c0249002c40400125020b805641e10580803031100c0225420480603402c0200311200f0800d602200040c8480d0030448440a02000455070300e0311030818405034100704000301075030706040c00c21201c05030742648441240c11380010302c1c4002a16884500e4100e482c14180d03800380860f2480440c801101440c28880041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 196118165 1250 196116915 196116919
    0xa03060e2805060604231015080403050318011d1f020408060408250312050903130b1809250c03050a080702010912020a110418021302090604090b 64
    0x40594000d0780d1039103001d441d80c1c001c060360000008121541031980108451613240c8007550001e0200c040d000b181d414007190310061040c45010200701030707429843c1910308110103250075070303280c645601e0242582c4005415998440304401d1210004482035221002c442c4100044c2080c0640b82d9143d0340c0e480c40c2007018030340c1041c944e00d004c0b1401d07030b041e2080720304440441010304003039034580d00d032900150401e050147d0f0340d001d92480000d02c0d00d4002e1058400920036210000310881700f04004003141c00003400d060556104201c2502c001c580f02a01078100c500d228961030381c40d0503405c1544070060388280030b6900803640b20144503103041820042c0c00b84040108100000341040102200c0b00528030b140076012a0007000400103c51240314010b0f40017280d800085080510742e6115040c564542d1181d030016042442c4820802c4103484801e400407000700c1d024400d01e060b2500440c941e41c18490001d1103210003031550451031210750191403002100400e01d6442e1039440080101400c0300c42031083c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 196119415 1250 196118165 196118203
    0x906220606051e0739030b0406050907080618031b0102091806090103081b15060a0e0c030105091806042001020312010e06031e25060507110a03060e 65
    0x100e812103c07040d03c1e032242e000f40c0c04c008820f00c10460302040200180e9014207030b2182c00c903c0f1003070048400c8100d0080d8414038070318055241078244002202c0024105442a801c804010172542c840000c21580103030003086e19814000800305510314600c1601c2c0444007210f42c02c02035000b0100d042d03024200315802aa83d0309180c2c204208010348403941100c0b00c6501c10a075400600105e42c0c090081c0245030b00798554440140a0602d4461030010701100c400060814002002701d241012034140c0018000c0c3e5880f03c2c100d0904100b00c0c1c1803400140181401b507402c42c0c0028107507910b1641848804000a03007524243d04050500c003d182e05240102200c2c0822141c0da0381c0303154400001c480500714882c102070102e90030520b10601c03482c00585812b906210b402e0480c0d402d031000100e00055200d803d8000c00e10400d46402000d425150840b041d0030f1241114010481503402004960201d80d02201c40307800d0444060000e102d821042d08054001440c00c050005a00030001d507e400001c4020094 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 196120665 1250 196119415 196119457
    0x19110909161724010302070602070c0f080a0b06040b0103021b07030c1401020d1107320409020d0605130804081515031002030406022b050105010e090622060605 70
    0x3000d8140d020343d034074551001c50820104082100c9180c0c0c0048110525000d45030940075200c2034280d8104420696508a40d10401c10914003000f4208000b0706034440034051a81050300c40000a6600074031141c065038035a04808600da00c03076412505e85032200d404c030403406550040c41079030383d0150f400100d400307031070040000c517540c0382900216002c003105900030040410480700c100c42d13001034520703410002d102d84da0020070704110158030031a02104001400112100625038540e4011801c1d0545000b0743c03810a20402584900041c0c140240e0054408202a2130300100207036901400240980f01c280040350118452001080035280c4008608204000e500c980300d0f000c203603a01d4442e81302d6056000002c4002601e5141e006994468040c0000604012140d012441c81030030306200c4074116603034010316245d22545c0c0d00c41c0902604c02172801c0c241d8061000007250341c003000a00810f01c5108502c80d229100c0316a070480756100f0000000900030550303240c0340600990806c00780405262410303140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 196121915 1250 196120665 196120697
    0xa0e01060c2009061002010f06080d0909050906061e13050402030d0306083a020c0a060c0201050906180d0b060f091e0c1603050405181911090916 64
    0x1040e54280020300c030308110b44500701002003103202c45c0d4010080d0b54075200c2c4c071340d182911407003514002c003d04070140c02c0c042d8101c4401401c034102074014180d1985000140030044d0304c0000d019511440a448000036808440c1d8928100c9504149042d840100c040c2110388110581d081640103074803d904444a401f1807110507415510603020f40c00540d0b0000c5441070390b100f840c001c0301049040e410440000c0c0c85070407082459801c81901d60402603480046e90721803030b0500f000c0100c010000e034a0705104401040c3c0c0004c10303038032581c02007a1151001040228104001206260284100500c4c02e5104642d624104004100c200d49452082130007a84030446c0b810000307205c41c401c44010102c0a2240d1a0031403800300303c0c202425001c18148180601900c81c504400c0c1e0f509458082e8803144d4540d803420003004101c42e030000382c6143c0340c1d80003800d01040d02c40d0000e501c4050040000041307a41210500007000c1030041240d400da00a10036401d110f003444040b820191804403940d543e1000c4210050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 196123165 1250 196121915 196121963
    0x150f030e0a150b01030b041a0a080d0c080a030b060307030b0913050a081602030a150605040b060a0c110d060b030d030c090608070c060603060506010e03010c0c02040203060a0e01060c 80
    0x14003820110300548220001c80c03043e4000c20507101c05040020b00810300030301140031190381414040010780040c6901c5240e140076051400203245503c01013081c505040c0000b0008805c1000080a0300030220f43d409006000380c0042e02d02d8000549825180c0c07802c4c1c0401005401c050a00c2030094201c00c000c54040c8580c81c0012103059002002049150030b569110089030303000031215440c40414036a84001a030b414418980168081d24200c1d010000c03840540f02264107944c0005d00c22032912044600e50340344c80c003d41701c115015080404074031040c1c2c100f44010798100c010481d0300000301d031148401c010441d0b20070384102d8016001c480b030604c604803041e011200b01d1200c020200d01e04410401c006881a880c1583c403941030300d0a09410300103581c5e001e054484e00c3e001258a95100c2040102d196400241c81c482c40310304500078008883c07080b6000d010042c01d40c1020b809103030000f000030001c0e2240340ca150010002008a1621980d43c0c2000810310128940c00b162130f480f6880880c0d00d40d1f143c0070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 196124415 1250 196123165 196123183
    0x40f17030406060608071b060e060702030703030b01020706080c0c0c0411180f0d02130603230115030c090c0306150201020c160e0f040204140711070501080906010e04030207150f030e 80
    0xa11200c0004444030a01110b118101c84110f48c0135480d144138002640b018041203020b54074036002140c548c035107450054151144c010000d411503101070407c01401c0e130b00c07044550708194021010350351004400704480c101400ea0140da074000b400c041141690711003e4004001d040070324003007a580d401c1c0000402c550301740700c03401581d440030701070300d40401500d4003e80a2500701a18100002c00341d030345e81d4038040300d00c0820b0100d4001a61002420f001e042003800349082c1d024000011081e10350841d901c88640b071074680102030100b82d03a80c82480c5510300079440708011b000341d10f40c011800300b50b50500034040d51003602c21030414000d80490b6035000c500d808652050350510044103c1a40c2c8500e03403002642d0b8001c0c401c6e82c0c000d80322041092102e080d983c2c8540104219030f2011b03140f0040144a51130442d41d603000c60704200c0b100c000c00480110101e9010b05641c580e00d003184142d242d608040340303050b055400000801401100b41801581c004540c000007034100d8130240b0036a40c50351030a80d1140121 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 196125665 1250 196124415 196124417
    0x40c061205060603071103070c030c0e220b0604060305100207141b040902040f020d05010e010b070c0e0405031902010e06180a021908010c08090609070f0e040f1703040606060807 78
    0x13400400c11040c080c4c49030480038007180c000c0364180032042c0c55200050010354010f0b030f00e500b042135040c0300704104811070540c0f06600381d41440c14480d0003030b04101d4030800c450014244000c8480466020794441c0c000a0003103401004460401d1034510005c4020b500410040b40c4a02c1c51a8050102c030602240c1d82050007039280c1030070040e41c09881840050141040c0032030703100e5910030400e0030b1503000344080c00b541c004007400015158102a01380f0213841040c3c01c003c00404041c8070f050001a80c00d107080b0192810300240842c07640312403a10a24601900c1500c2d5400400102c1a07610160305521500c0b04040740750454569403950505140c10b2501c0181c02d11040e042140604098105580304c034864904280d0900d41d580e45d103920ac9400c444520f2607200004160609100c00c0c41810400c2c541c1002222000c1c1805074982100c4454500c1c062249400449540c3c0003c1e05100358288451042e60704a50100c2840c0d0138091251090380c403c035001c80c3c0302464088081000361060980d244a1801d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 196126915 1250 196125665 196125667
    0xb03010c050a080408040e0a0c08090313030807020a08031b070b0a1403062407020a0f05090601200a030906020f07030305041403030c03070c0611032104050f0105040c0612050606 78
    0x440ca000c640410f0000c0c820340703e052040100040c2c0c0941c10251501c20b02c0f5040300000c0d2a8a40c6400501e030701000703020301025600500c6152040c825080c03920b011294803e801e540c0c0c4c0d24162011403880300007540148c0c101d002c04241402d9001c00089c08213203800481013590140da490360203030780450149100748000107442544c00324041004000550f08210020040c043e0f1205c505076240c00c1d0490f0710080403110304003107100d80441c1051400d86010744140b003424486242050003040010038001c1c152410003032440e0708800074180a6440c403071040140011340d405000d1608010b48440250300c40c0a006200b5829003032014175010401b0300640340d0540d500c5117084d14022054120510003065664940030800c42120914020401400800c3c0b00e241d0007000e03545000000362600040c8840d0140d59042004280310000007041c4005881800b8852491151141c4c00c2c2549003251000121004d07600c3c00c410300050007800c41140044644650324a802e0703d141e940c4c62020780304141e0320280c000c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 196128165 1250 196126915 196126927
    0x140106080303041e23070e01050f0607030c0609050d0e01030203131212020c0c0405180a02041a060a030e1e060f060d0b0c07170309030702010e04020c0717010b03010c05 74
    0x180440040002c007801c902c0ca04d201c041d0a848042c0700203c0d07011061400016030000d5003c04409008000040084030b030031220561408010641c000c2172101b00d18814400040c1c2c500800d8000d001c00c40b40c06820100400c4204810728000390340c3d28940c690030010900d0030381c40b079805620074001c4034840c00300d074a55842c8004403070360ba500c580311580a5100612410f0401d403014500c807403010301051b92540d030051500024440a0208403440940b020850101c6114a82c207110f00c0043c0710050958142c0c1c00050581c10350942c000243d0300713021032a510a10004211451a0703150304240c40540101d42610500312018401825080d80b0f064607030b8640c1c201100140c0121400d802540d030282c0060700c5a40d45003002ea850000c40441228040504030303001c00c48100340304903a158070050310030440d40b480c50b5040c401c02584d40e1780a1400000d04020701042d044006440316010754003c0d081150071244401c3d00d035000c1e54188125210b815000e0762070711a0200003450140a40c0503068400d4841c00d10b001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 196129415 1250 196128165 196128173
    0x9090f0b0403050405131a0d080f0903030702040903020f06010501030614011110180507060c080906030a0b0301050a0b041107020607030f020c090c0a021b0102120a020705130914010608030304 84
    0x80041c4140d09000041c800040e06807503501a4101c0c22202c00f0001070030740d007920b200c020100b943c88103a034090190091074100050b0b600040b516160446400c20392144100000207240d4461090b0003034000e0300302080c07a410036400042540001003000103484e0541e880f40d0044086400300c3c810384c104c02d0914000704c0c91a502500300104144c800704290fa11910076207800200340c0d9400e4905507541c0c0c072506070541c14820141b0203140503142d58505400845000e13111040786001e8205010722550300007000c11003108250713024410315000a030085c040c03854011440710003414000074981c02942880a0402a07080b8901154442607004142500341412501c0c12900c0b44490710b030710425842112415030103a85d6040c10702b8850502202c00c2692410419402070900c58039069600c91610803905144440ea000315581001c0180000340c15128071401c5000c91a1603541d60055802c1440405100d80501c225045121900d01a4590b142014070b039656240c00c80e044c91180400303e801c2800450001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 196130665 1250 196129415 196129433
    0xf10050d030311040f08060106020312010e13020901080c24030a020703050715020712030902030a03050d0f060f090b010801300605150a050a030206030a0f15090b010909090f 76
    0x814040c2c980068a40031180e0b001c41203034801d0b040ba5030f56004c1c444040062507010442c00d0b01400140c4069401c00c0380b203035021013440c003040c010200c01204500014090000440b40001d11640042c5003c0895960b04a2140c070f801080c5070280c080c40314070010360a8040007180945016207840710140c0f540e0380350301c5207078002e42120008400304981006a40085507529002824076101240010303620000c3e8036101585100c0340401c0d00a05041c00c0c01400540d4020800031000d0f5018200701d070b500c40c402843c2400038005150240300d0286080710100c0d0400b101100c1c50241c071416041005602540303030042d10a84c0d402d2140d41d80b03040701e090f0040c48803a03003594582c40d0b5110703809140606100c203a6440040d40c41c2100d02c078014078841450200185020624900100825200c0121950854011070640c1c800108103201c0c00c1d442e0100303009103075800da10440e4040b6096490380f80e01e580b01c004c05030151403c00b200c0b90004001d4000803070030803414420507183c1740d440a00740d01c00c0107560f9140480c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 196131915 1250 196130665 196130689
    0x14070302032d190f0318170f12090c010314010611070b042d1d0405030c010e0d1d010c141609060812090306040b040f15050f0f1005 58
    0x110103100c08a00302c1184031000038160001140941c03202522030b000c8010441600307400b43d0401c160500307031031496100540100a040c40c0d00405070320303401c8007200b014035040c6c030400e511a02c1c204000181560074008500b6283c0c00703a00c0400c1076400002130600110b05a902c0c589040c8000041f240c01002200d0051001e03074440c40d8458259420203030340d01100a802e0300154031601e4200300c0d030b40c4000c0b2030201c01c030510407013460144181500d00b030814012034400403480488015005925001c0707010b1020400684480e103000c0002030000d1401ca024039500c0b0f01410303107901e021495103001179041403075244006840040c107945010240c0d100d07455541c110701520b10b440880d4004c22864030b401d50519414440030340389103100441c03141e1034160510b2a054081d44490041c00040c041d0400558000c00c05980058001d443d103c69074071141889050a655000c0080c120000150007010069941e0401846020505070303400040c1d0b101d020174504034404440007003040c0e80c4150123001500d005002240c0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 196133165 1250 196131915 196131967
    0x1809160e0403050a18091109091f0b0f121e0a0e0a031b0b090c030c0a080618031204030206040b06010e0a05100e03030409021306050a2a20011407030203 67
    0x1403e46d18101c1c601103861002001844420000302c40d5058200000b8a42d04401104403141d11524103501c0c0e41c0241486004200324460001071200a20820409070307004d60119100c07101c1c01d0306040031481c44060100c40034180640e01d000004200c1c40c840d1080c940248a004040d010303034419a5000c542c1c042c0c06400039407100d8441441c032000300d0509203040e442a2a41401881100311840406180c0b1100310212442a03485aa0910801d60b000c00c440340c200494030001611180d24400c0c46095000301d2001d089440c840d48200018181d000a80d640101c1c0941404403142d1a100c00440c3c0105000040701d0300320480d03000400c03003418040c0100d2003a280e5850720001d40d000480c000381c2180c4c807940c046c00126802081001504104804140040402d800c1903460402c810a01a0038034001c10180030360441e0f224115000300d15030701080754070640c1c0050115a05100c416614080b021645a254005000c0f20281c081d0100000226021950160021820801d80000c0000003005003071100c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 196134415 1250 196133165 196133207
    0x10f0b0405040504140a03030e060a02071707030c080a0e190806040f0206160f06050c0c060a0b060f0a120b0103050108190c050306090708010c021b010c021809160e0403050a 76
    0xe26030150a0148086e607620aa60105900c08015441c1c0e01c1d040b809402c0607041c0340304100780300010302e940d11130300f40c00c039002201c0741d840708124141961512401f08001d400d03148006525900b085c0d021013a072000340001c980228000d0541c0a445450000502401e1541d91002012401041111910050302c1d403000300120700d0031038442003181180079009421250000403c01402c100a128015103900070303001002581000300e410310096503030101034486405540e4401c48100c00381ca4847c02c41d1801720314294541d44d0340f00d51400007414a0aa444500c0d480e61400d090412a58801e014041c101d840c140000d02c51203078131171900d03801d000c803804044070201c41c0300b0800030f0030740c070b042c01454458003031070300070380a994a400b034281c1c25503a0106c00802150001c3c14201c22080e100714400341d10400a00e01001219014404120701607800503801240c80c7e403110800040110015040712000c4640c109034541c6941c681d006200b5200948004010400620120804500c142c5501d520b031035104800c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 196135665 1250 196134415 196134443
    0xf14040905120a110c090606030403092103021b01050d02090f0301050106020c130c1407230705040e062a070b0c0301030303050115090b0a0c170c06010f0b0405040504 73
    0x80d4036040d46101030061182c000f241d041c1c62030303402041c1481c10ba00c0c1e600250071042c4007a400103800420003000b20303114103804400f280c00d16100c0e0200303101408511400154001c0d41c3e10500c049003c0900e03049006114204d6665080381002a40d000d0030320040e1078003428004d9440f0004041c2d0000f00700309400c03610707503d45030820766000d0041c3c0d4020003850700580160303040041441100d162490340a1195428941c151314241d52004d546102e51034609005615080c80380b4003a48400c1056480000c2c1c00d185010f90031241c0f0340820850200c50046404200428907007074856101c842c100c2c1c81c00340c40e220145600504002c1d44140b26103100c1c0c0104240d14060380d95807282507031002640d03c0300075003002000601c109a054803074207002d4241c0030390304801d441184400504120704c5000d038142d900b5005c14102204c40c0918454007180c0d6000403400c94074024030140e241242c00100c50346200b48104d000000b8221042c0c07014034161480c261845107440d00741428000500009402141c014600000c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 196136915 1250 196135665 196135673
    0x10080c03070c02060d060e0619050402030601300c03110706020714060a140c03040807062703051806040807090507021e010c1d0102070501030b060d0c08010812040f140409 75
    0x1806980f0040400040c6c540c00c02803803130510304000304042d000d05040004980c00c030300030a214604603031044070056501e07591200101d5103400e00c150507680c210003142801c002110350001004200540882c104445440198101c1c16100542408421840100314110202e400c540007010300d6070084860315141d1060080b07a078134146040f1001c0700e00341d0780c4255114150000f02c00f49604001041859815410300e500d03184002d00c14550002c0400d0340e94103207280b501a4503041c1100c0170383c4a8050320960b161504016040e91700c00034400403818034260100d40d292800809480645503100e00400825042860420040202402c0e00d4194030400041458202010210040766503907480085074401c54080c01821051012a103200041481c0103800c1c0141d81c0094000222402440c000c1086008a00442d5140c4548260200c519040281c1d07000d50350703000405141206c01c2e43c011100c440408002c4103000f80254012104e400d0f070341c03d4080046541201c0503503400e070401400000c000a41d551 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 196138165 1250 196136915 196136917
    0x2060f04031e030207050f09060108040c1a0c06130803040b07030e2a030606150a0e1c0201020d05030f0a02030c1c1b08060f04020a200c0f10080c03070c0206 69
    0x1000b6260240c1c0740109404040e41486450020007003500c400b240b41d140000000c2c1351240082c0018108465a000a0300b808000d00c90740e030007841740c60554450900801d0103440c040d0301491200d8414418100891010f104140c010440d0642202d5401e0850b01c4603542c0d00f170002d802415950401d6200e400204800005100341030b0320002c5018101c50f510030145007111103602100d0711511036000601002038584030341064030300003030b000c8000c40c1d038400c1848416142c468241804580000000c0c0c820000c0c3c268007001425100c4c000d03022100400031032074048030719100481742000302c040100b0100319100026009140c00000b010701076410080400201c040101040c002d050340161603d8200b03000c20200390070b003d0014018035228a25242c040b0114020340c5000311201d01841e40004c01c83c44680c0304a1804e00a400c0d882210a102c2c040441e40560b904039001380340d84140c5901c11a003005141c00115003d2040c0141c858a0b030907600c005904030103800042401c2c042c880500020801030f60b6200c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 196139415 1250 196138165 196138193
    0x11070e040206032a030a1b02061f030803010f080609030a0516031e020d0e010f0509151b03031909022808070e0901060f0302060d0506040902270702160302060f0403 72
    0x1e00c0940d01da1511b04d20000680b8030740d00c0025030450510314840d2840d580868a194400035824072a0000d6841151f040c86081701a0b10103089040c02000106420184511242c211640607017141c08613211100c925803a48038400d9102c5c0850b20400080c10f00300b0503000001c071031034084d0a000f00001d204c0c88058940c0300c070072079000b401600811901760307400b80c212001c400b00040c28a4560704041c071600d0050702502c54007080d688500941d4202e80c020222440844d0441d0001011040a4140c00d000075662500107031240c101e00340600c10700e4083c81c0580d01c54200120740052016203d80c1012802816000324017a400e8002102d4800c08101018100101401450000c0a1560728908a0245802c66015410503541081c240c0c5040025a407a00b0580300080c00003c4005031945a140004000700791a010080d00200c1980c2010a40a01c0916688c0c130324900b100d980304180d0b01c00d5000c0703845807050082e8000403548880c0c10303c05070030440040c1201d50900d4020b549170a44076100d41152030b03814 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 196140665 1250 196139415 196139491
    0x14040609090308090105090f0a060f0f02040b0d05010506030f0a020c0709021803070e01080721051204150801050303043507061e020c10180b03060111070e04020603 72
    0x2c60140402001d003441b6280d071084d441c1c4040c01c5041850304905071904194040a0803a50721a0b843c07034243d0f41a94000000580350320421590346503180c020140d079410466441c034600346000e00010b041c0c1000c000300c1c1c0c45000d5200d0f48811540d50325095030f000b500120000881841101000b250361000351008011001246e910071040d040704c06e081600d4504150490b0b0240c81c031b020b0041080e401d00190b0300042d10450603846042d4400c00b07040005109040c107014240e0b1041002c00c40301d170b07050000208161480c20440c0844e1480703c400030780d0307119000c2c49030940560040104000c40103035a900032100398504942401c100c03400121100341701c0c0040c44c0e50b0305d0326044000100901a001040806c44d080540300291402c282500040d4444110200c0700d0301840c00700e003110a18910408809042083d480d0141c4011601d480e11505190000c4900b280803a0480c410b0400c001c000007400001c441e061200e01c0210780c0c495080c0141030304081c205140c039140000500034100c041480c810300140071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 196141915 1250 196140665 196140677
    0x9110304171c060f050409080711011403010605041d0403020a031b0213050727060c020a030204020c01060f0f1a0702010c020901060c020306060105030f070807110102040902030604110405010504140406090903 91
    0x501400d01305161503039001500c00e5103071a0381940001d8103007090302d103495081005400380300388002c01130b541188001180c0c020240000004199240c000c0054000da48448507400060045000b205040f044e0641d801b502603800400a800080e20405d000030410346980300800a40d0403a074040740e0185400c031380065a00d030b110020004c0080c1e2050006403085080740d08141c80000d4a050740038905518080d0204018070000c1e41ca056403a010540c0c801140d020b0011552413441044c85030080603280241c004040420301c0000390800004001030542d08412080107049811816082079035218510403130521910b00981400b5036180780c1e10500070900d54489840300100c40c0304240c2886001001e03175042c0b08050052004100d45e000703c0c00d601c64900d041024058580000070b480304680c819440d00550300000c3c0100d070b5014550095070040c00180c506110440000d01c4051103405180149800113205010130003800b658600401504900900006403194a520200095070804d00c1e042d008511 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 196143165 1250 196141915 196141919
    0x100b0706021b01110f09042009040b010e060a1b050708030c010c0c080322140f0705120616030f0501090b1c020901090c020106080109030f0909110304171c06 69
    0x400d400c00d040000c0c4800000c002080c0901440b8219014003c1402c144080106d009210382c0c40303d03031024038848600c1480e06080e4100583c3c0c00440e600000790075000d6410f1070003040e51540111072403103007a04d000b0540350510241e40b404440468500d219100c08500b2103801c1c0010034020300550000d0040d842c0650f03071704c010458009095920200310381c010050750040c0072021411f2207064a030401c50380303c2c4048804600317446402685098035005444100204502240700000054200006101c3c4068406d801e5540d010440441118034a07030102d80c100c90001284408110043c442d0200581800980302100035a488100c4409070050388401d5964000f8580516000070304011610035800140f07030b00301c2b441c0d0115071001c0040c42480c4105444c0e0a207003000324000e400680251801c41c000308100703411410020000c09080540f080440e85c41030000c034400c40e071802644214000b41d2001c602e103440d40d03035030701c49a580125095005208244054915844a0300d807a06460081c14030200340d0364 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 196144415 1250 196143165 196143187
    0x6100302070f0c12050f0a03090303050a050d06080601080f0318010809120d051902070210030b041805070302090906040c051c140c130209010207120503131203020c010e18100b070602 80
    0x4030b86c05d5031040c2d0303a1246215070700082d0321200410607203906140407511400c1201081c3c8250066007200c0700361506021000c03178488000501c00741240c034a0000c461185010344c80700e90701c1b8841c0e40d401c40403d1640d98803100030f550103051103a4014010008864951240c100d4180c41034100400e4014200d840f4801e00407103460b02c3c655038142011403001145450f20660003d04c42c4000c0b51903000626482c0d0401070360941d295413080701071840c4100c40d0101241c6070f180083c0c441c02d0b41d01049129401d241c02180822000007080e9200d40d034804115980780d4284010041030603102c641601c40c418100f508800003d0070b00c1010800315403520002c1400310b0080d81040069a08591364294051046c01841da5a070b9001032204100c0d104d6610311810043d00707040141c00e610481c074030701c00d4014680700c0024000103a42282c0b04103074041d90aa03114500d1401c01180d484441c0b041c0c1c1503103c030303070381100a88071034400b21031641002c038084045602640e102221011600301c407a06a40d815404221403410f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 196145665 1250 196144415 196144423
    0x1605060103020117090a060e03040503150f07050c122206030c0f0f02250302090408040603140c180102010e07060509041a010f050d020c1e100506100302070f0c1205 72
    0x10781c400d200b118600a50441c0c1c6d02c1c2040360002d00320319110301c0300d550a801d043c400c8170041d0401030140e8500100070709802c0b068480968080003500d00110010380c80e54882c0040c3c40c5d610001c80b0281404d01f1f8008000b1141d0340000450344c54008201d0004500c40d64184106030040419843c0410822086180034140300c00c40c402e07032010710500c8413011141c540d0124015130340b45592071200340c54150f440c981c001480355a03003009400102031001d0100f0b0080c8c1c0c9010b0300c21113640d50350030700041c403006401c0395004d001610444144403003400700902002e54044106c0d00c0101c1072000041008210075920f14046955002c2e01c0445c0c80001c11151034181030180c0e8542c1136001080b521120b810381d00091065038403241050030400702003200c494200780780d0110384aa0411f0012600ea00c59184030b1302d45950010008100c0343c0c03203240d0322602c09644500940f031048000519008680b140844190060341c0100c00403a0445013069890740042d0000322650040c024945111221400c50328000d858 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 196146915 1250 196145665 196145687
    0x80901180e04151803020c150706020c010203190603050c090604091505061315050f0102030418230708060625080a02070806010b0706020d0e031605010b01050a170c16050601030201 79
    0x200c038181d60f03200c0b00406d80008070414180420303201c4214445500030f40e04024090402d0043c0954000101c41c11000310540213140140070304401101c2c02649021040e0440d0312a01c030040058210440c82c810620f81aa08107900140282000c10799130105c1e901c0989030840340f503080310340b00e90350000d12000c2d0078492403480c4400d107207002c00c001c40700700d0204541c4094013a00c5420301c283c0219641260302c5c2d20900584000b04014422042280c10b40100d42010b0803810501030182689003a12950540040000300d00400003905c842e412074461f0010b00810390301c000240001c03007540c403040000d02c2c00003640d0700040d039005164942c3c498100e498000c0c10b04090b548542081c0d44404014003c10203800300701d0701c1a0381d10184c01070f503607500f10003820003610454980c0d4070315000100e1101090101c0003464800603100c0c8008220100d200001034031203008101c81e1800042c52202052001c219050016400580b1109014202070b0004984155030420b170030102d805811030401081156004100240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 196148165 1250 196146915 196146941
    0xc0a0302040510120f1a040b01030e06070f02060c2104170403081206060405130906181b081906020705010605061b07080304030305030c07110910030506060d080901180e0415 76
    0xc82c0400781c0710310003c02c41d01c1441d06c520482c0c0e54200004a680640e201c5a40342150f50156450344c40c1203c4080c21813403010740c0c0034016000e2000002c0e4080c41690440366a044500070240e44442c3c2968003005044004204844408807108020b9220040001420003940702d4008582d640c800ca0030054101c0a0240505000b440140014001c40e921060300400a102d20007000450708110f0034039102602d01c8801e8080b9040c81032480c4002c3c8a840c420b8000c1d990220102451001e82c0c4401c0199a100c45441c02c05040c0104010423001460980050417442c0c041c00000c50600d49500010350998040100c1d0450b040c03500e916220003440a000000041c60711802030350405281d510082d010b841700410013049060005007100c03c2000030b1683d894091409809100d42d483c1c48911038403100703e6804151600e1151800007081c0345460240d600d41a80d010a100e0b04040f070007001900c020100600c82d90303180ca000035010400421342e403005407045000f0b05c40e0840ba9100000200c0c21110740c1c001b080303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 196149415 1250 196148165 196148171
    0x906140d020f0d0309091a0102010c0804053301091b0203250501020c060705030a0b040e07090c02071707090e03070c0326031f1d0c0a0302040510120f 66
    0x40150b5621002045252820780300020340314624a0122117003103113908200c1102d441c0c0010000481c4001c00d040d0219a0b080e00204400c0c0c50242c01610065822100100281e00242c0100340301c00c0300031541550326140c5046600784060350303441d07811a11001d0704030840c3c2a41d5804a2480c0c0707100d02c0c070a0300625207280040c51410301c2c01002c0c11b01500220f40e1100b040a4003800040c1005004d504030380740104040d0030740c1d0081c00c1c02c2c400140346500030b03110050306900340034043c40030f854644240022401c514000300001440c20200101030000328001c0c500394010900000b40e10b0790030802400c2900b40d0200901305203400c10002c0001c071070602111380030a030700501c14580080c0d8080949010b803a0850202c0700010140080c1e00005c0aa1001e0035890076400f200740106001d00e926800840910315800c9000180c46090b4805406807050f40717035881d88410004a5074643d001c1c4000c00304a55180b8025181c1303070325040407804814440144400091034800501400305452041340c1e039070015046d043c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 196150665 1250 196149415 196149439
    0x6090c03190b0a050c07081201030303050912040915080708060601080a050708070c05030d02040b0309072709060605090403051c0c1d0d0f26030402091303090f090614 73
    0xb20070502c07402000104503070750301c20106000d01900401c0d510210380c0004050741d074040400c2c03080c03000c4400307200407004641000049030090340d021403d00211007440c002a401c10740340a40b150081d02d04d0703151240c06506410360204001c0c005000740805414804000c00481c1400c40004080907001000e0480151824051240c0d4681c03001e00d41e500140f040c070f08004000041e007016400d510400742c206101c41e20005000078110308403c09135220310074442c01c1e11103850390340d54004009081a0302404c00700880d00c081c10600300250303000094040c0500c00000700035849001080300c104c000c0c0c038258040350f0086101d0384080d0079410745051010301908c050203a20340350b800241c40e107058455900c910f4000300141d50120b45845031030803180c5802c80181125040070303040801703030010075902c00480c0b082010301c554008840d00048a0207039501900c406001d684480540807050451075040301000217092000881028028403003000c0c094004c1c002680c18a454a002a035651250703201e80600040025 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 196151915 1250 196150665 196150673
    0x20a020d120b1c210f020709090b010b0c030f0a1e0903030e04200406050918010509150105070204090c0504061a0f090112090f020f090f04020f0d0506090c0319 70
    0x9106040c0070300520350b400000c641c0c502200c00e00740b07801c4c030074003008209038000b83c0d220b500104020034490b16809490800351108920025180c0d04d52018005900c594010001d00d90071000034240114800b06030784c1000d070000300010003a48101d440c4000150700d01c224540410322608031701d041e0402e504001030043e2540c1c0e809000259500d600310701c110364515806480e02905d440340f0b502102c1851980b65a00d0721945c01070000e03080052000d0007a070215066103026002844118107035803009003042d809030740381b108203541018240c81c100d040100610800c80141c03130718004c100d22184a03010240b111810042844110b44940d0701c0b0f0f09a000c100c0b03202c00d0003918080e04690025400f10107007683c0b990310200503600d00d00d01c0012410003610303211425003408100301440a4042c42124104a240d504204003ca18132054032204c503140045c0700030900601d0440a20b407813008004d804401080c919880303c90802200f250a91202d0700000140c0c3c049190038864540e1500ea0365000c2904a41c80d511 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 196153165 1250 196151915 196151929
    0x206150d02090412030902360c041e050904030c0506090307030e06090d0b040b0a0b0907021e10060b0403060e0f071a0706020a02030903070801110901031d01020a020d120b 75
    0xf0141201c4800401c1c1e081040c46900030240181d009410001210b0b00d480841c80c0c44603150f642080303221051400e0050030b80f80702c08054020303d10058281d003464209640261100c0e007807407012550707200e4104000742c0e03a101c404101e88140d00036101c1c2e000341040d44c107149041000007070001c0490342041095200090b000080c0b291505801d4692603150340348440492801031101e40080c00f0041c000c4100070400c01d581010610480140e542401240d0700c4c5000e20180030000d40308580960062078104080350035070702106043c2c4034810115070450000fa05030f0cd04644694000100c10540000c0c2071090280f64040c444070102118018603543e40008005600d42c0b031980508142414210318034260406036005556489800c07150031075031820780c0c141c003035502d0380110052400307070103070170310004110b001845a07a0340c000440402503d00702c0b00f003004600904402e8101000a00c80302c00b41d076451b8100344040c0855800a400400000201d810302420728440b80401d00246424a10240295101c43c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 196154415 1250 196153165 196153171
    0x1090801060f09050903120108030304050c0307030201050a05220f03050601080304030b2205030f0901081b19050d0c020a150203011802180d06060f0b03040503030f041704060206150d0209 82
    0x440000c1d1300e4a03000c0f80a411403040380240c4d51041809400402d451101100450083e0300c12030456000c82058401d040c1c4404403840040d0204500340f1101d86801d000e20000d000405224220000d4180691034800b501d070080d0308107442c0c2030380c9000c1c20300c1004000c02c1331a0243c105403000754241880c6a488096a000c0101a00030b030f50f04d81c5082802c6021030b0380012121681c05015030361144080e6080403410b40181006034005084003010a034080f11031460313005940f22012103a85400c80100440703000d100001c1200c810080108a0800c41e080140302e1440d081550713501800c1851558280324071814070004404215510400c01080021640000c2403040060301e0b40258451007041e03882001c501285034500d400003805440c04040007030550000069411081210343d0f00b42d150030202c0480d000445005015510800c041010440b900880d00e07071091083e49500c1000b040f1103000c0c18241c000f60b00050243c0d002d2420301444100c2c40445140b680c005448020340081035400181070307d41c0c0a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 196155665 1250 196154415 196154429
    0x10b04090903091a09180708040b151f02150705070f020a031a01030201020f03070f171308280b0a1d031b10020403020d081606180201090801060f 64
    0x54800d881054003801611009001c82064180d850105850703e404c1a4030541c80c1c68032664140085001c1121500500380c003075540d980c0c500b0900d554503502c14600c01c0024000c00b01325040100014283d80d2a0a0180d240340000c40d8001d000c1c42c00004060f18100016551581d403070000c0040208a6601c40113460f0b00c160004084807a501c194008039010502c0b94001070b2003144140b000250b1250321008076812207100703074219402c02110b1a0001e44a0103030603801031604816007001800700e074000c1c040d10406040c0140345403410030342c841d2403009440d15a0080341d460300900c42c807081e540070400d140303048803c81c1521580e8801c0d07142d841141c4940d0040051030841e5903100d2242c2c3d449050107080d0b0f9400599401c036903650412000115006d149501c0c0d01546200381165071007203110300d00035507040301e80c082d05510400c07200c0e64850485412403400d0014504607600c658001c10030f00e010304481c513400388048610409644c00018402016034100e00000d13810413a0412503400230141d120116061 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 196156915 1250 196155665 196155671
    0x7080604030f1d06040311150a14030c04170d0f0906080106030c020c04061d0c0421050a080d09150e1b0d080a05042301090306050910050c030108070905010b0409 71
    0x4102d4540300d0f0f51a40600160011310110b0040f00b0440518004101d90100320340034003e1895101040c0054440c11a1601c000740f1213015110b140c030f001070041d5810500b8030122a0405466010f2116094000e40f80070060b54000f4821400e401c1e044540c0140c07401c0103141030040c881c24039001a00151040c41101c0806030360720030010600d071003400403c02d4030000420601915a40d41c901c03240780e16501e810056018074079000300f003610341c2c008120781c12210340b031400083c0104c29240c1c03407a11034222141030701c41c1d0240c48410000111007000501c1c04a142d440c0001d00e00300380b4140510300718060844020050310300f030710100340c2000003c1c00c04001c40580e00500201174200340403400c0c005181c1e90041c40a0b0012510f00c01031030b002400b070700c1550040e40b44031a290150342442a04140403108040c0441d1800c2d8042c4041365035600425400b980407004c41d1181f640040c2d0b00c004440003203a00d404a02c5c0007100500c10158140903000040c0700d031060500c690750400b642803c19109a00c10300140b45c0c4e07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 196158165 1250 196156915 196156937
    0x501050d0b07020a0f05010509190c03021504090906020a08060d02032a0d0b0106031b05030105130e1006060e0d0c12061d0f010605010f0c020111011503080c07080604030f 75
    0x803013007026040851380071a6502c5054100d1070b003e4044d00c419514426039001e804032075450360a0850200c084103420086003150a0300c3e6400b80422039480c1942c010602e081048040303201703000e82c001e00d84080d1160300016618488088000c06521020b440f41344103d0642d0038820261307400045055000c1000149104160a00160f009508940400312508812082000e50a01103d01d00300b41c102c603525141840210101c1e00c040356041b00b525950b5001c42c0341480184000e0a0614040e0601c00c5025000a030656040e60160304e80309580100542460f2110000c0c41b4140d0311041400050005171142c0140980070395800d41d50341d03101e000700c24010341c20819032824003c030b98020742500314805103210b4041450140c03c68440112540059242d8200000007489500c20082d03046150520780c4d401c2541c940c15401100c003641c00242d48607a030342d00c80004100c044c030304100d140015032045840a1340c0d042440f11141c20300006921048664200310200320100b900000e00764151036075480d02d0f800d841 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 196159415 1250 196158165 196158167
    0xf11030c130204090b121e0703060609150b040b07080d021204050f06010501170105040906060302092703031012050f15041b0807050d1505040308060901090501050d0b07 74
    0x182004103940d84050441c2040c031444019a00800959038569024415008114180412102160000113560b8441c55005590281c80e0010f0040c8401714000d4400c120b540340c40751350035641d9541110801742ea03640258500e0000c007a009500500441c070030305007000e240440a03c424014140f019021440c00504500294070580c1191607040c407800b284600f90605040c000c1c0d48101c002e1800c08180304c1e20001091341d60141c00d800e40c510b0700c00900100c1c41c2e0b0070072040c08090301948000316002c4d034640c40c02000607910819242c1c4101c540841d4180a407407450306100c0307600c01c42004414250010014482584030a001c4a005e48250781e0419110311072078a025440c01c2c0e006a40800c41d40560360710240140b00340e04525003d64001e501100140300388000324411b402c400d01c41c0ba042070b842128200443e0405001030900e080c0600e5035081d18000001449080e90400c480880c0000e11100402c605441c15034115400340601041c10441503042c140828a54401600701420103a18000014201 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 196160665 1250 196159415 196159423
    0x9011503080f0f2a1e0705010f1b060203160903260c03030403050a031a0a172409120a0804020f0d051c0e010e01020c0d050c060c07061b0f1103 63
    0x406580420204454002035406456001191a11300314001c115910b1410918000c502c0940309048001c0c1c40c01e10b10300710054600c405200d0003c0b0500000040c85003624200c000a014928041c010142c1c0c1ca280c20600b00d90314114019840b005c0c0001140d040c4041400018403c0c480502c801000c00e190a40045043c1c040c0201009000503200010801c020540d001001e0302809102e03890034000d80118800e0000c400681c040c0441d00032050010070043e81c840300e001e81514888a405542d024118459050500710000c3c0e0001090040427062024a00d41086166201d0419400e85800c101902000808130100540041d06c680128031409006a42d80358640d40c0f50341d0b004040380d01908082c4250205a403201c0340c3c500c082802242c00c04455401144403031418072050340070b000094440320408c4174020500c00c086d50f0a11810820b4105511880c0c020305608001c84000c0565a14040c0c0052404035045180c10100307581241c00c0e80050720481e002450654090000740d80e440100340441d01d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 196161915 1250 196160665 196160677
    0x50a080c1b0318090f060904030806011101020406020a02090a0501030312020a0e0a080d031a06040302041a090f0103052a130f0c05180907050a11070b0406050309011503080f0f 77
    0xc5400b002075010f801581c5010499070103041540c0110f07030b980c1ea0b00c1c00a1784e11203040b82d645400400c0d402c00103001900c0340840581c000d8050402140030344000c25240e003282c0043d0800c0c5d000da8000c118010940c0341850140764442904a0140315641c15550001e098600040d030105200d50045071034030b401c1b4020201140390190182515505582c4d43d8049642d500d103241c4018046890994aa8090100c28400e218070460140c480743c80d0500c5d6509210081c400c0d40444e220150184266008540d10569854000c5503000140c1c0c0e802c1d4118200b4a091940c0302c13034180e082490345500c0001082440215000310101155001600030246080101812000e0301c03c2c0d003000d1600d01c03501e5546030014060501c251002c91a03811200c4144280248a501501d1510100f0001e1050310399441c800c44400300c1c00c0c6420b906403641c0d83d0742d0341c2042d25aa0000d030003c03408a0000b004000d030410091080501020b081c40c4414927161960f181e40b40944200110ba103030411000811106441c1e6803401c943c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 196163165 1250 196161915 196161967
    0x9030a030c17270d020f1003060509040809030d0e03070605071b080f070803030915100e0a050a05070e150c0f0a0812091204230d05010b090601050a080c 67
    0x9a64141c419044140403a0714805071071000c06091454014200302e021341829541c00340c03038034000204800c2003289603200e5034070017010161207110100f040c1d215002c005009510416a613034484002000305803d00556050b0b070400c20070308800c0c5507003655000545008030703481800e01580d195580e042a0803914201400302494816a250005000c000012407107510308040c0151140769031039200e40740d1a8481550001d90a5024842c140728014550f820543c0114061555103880c41ea5560b100c0c6081108440850509503154200480342105000d040e0740601c491034032003240c82d20038001401088000c0030018071540c0c041206031700b40310100500000602d0887c2241e16480a5180c4002941c0c040321013460703014110f02c04541d40c843d00040d1000401c00714810380741010b0805240003c41191035824180201c0c3c0d001d802021511015120880c0390302034000803443d0402002840903224000d8100303410407004008014007a5440780c46c080d04400c07600c1d50382d51384500a00c60306074035901c0420030745 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 196164415 1250 196163165 196163167
    0xa08100e2a130f2f0a020319020a0506070905041b1b05070911070501150e01120206070c0b090406060203090f09040516080d0207060518121f0605010905030309030a030c17 75
    0x1410a4000703450590160400041300710004080c2140344003400341c0340c01d42016071b109203d440e0180803401d1003d0300410b103a10468040d403500e611443d1401c1000d40f07030310011400031841802242070030b00811040030a860b00b07040e441c003400e5800902c186600040320380310360b858483c80010020103000b007100900d5502d60920916002d10340c015610361100d2412a2950300e45240b1001c281c4001241008513a80c1c0c1d4001203190380380420403070040303120180499000000300030050004120141e804045c3c18421221501d40c0b0400060004131403290704118199441844603152030758626080c052160710076940d002d559180c91518074600b948100c004060120408404680000e000584201d000c2a40d070071903540c0f954800b4203940511034070441c1c06003121130f1000e000c800d003450082a250074029108480c00b102070074084e0f254442200100b80060b40c2c5508040141d582d0142d0503502604c02200954600503242d0002582c2d920310b007070020b0901408071415410700018110b0f08190803e15503541e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 196165665 1250 196164415 196164431
    0x1b260a060e060a050a030311150114030c0d110d080403081908070c120804050c090c1b01020f04030f020607060c02070911091305060a08100e2a130f 65
    0x110060880d6000e0702001524000004000740351030006241203a40c0500070207090350464808981a41088180d904103104445110101d0154041550b008141c0350590000181c01901014107103c2481c110707522030182082c50501203400c501050a85560071a40c1243c00b40f907a14184801e4043c5c1c0c1e00103000c51802080795090000c41423002c140300d24096803a20410346c3c4480054641244418014041001030b01e581c0b56190f005620319508103014600301c56200c246900000c600c01002c488012049401180e501d00403602c03551081d190b01203042c002d60811500c5400d40d140f0b8000d074070018060440c80411481036440f0345048070403d0743c00c41024000080c0b180720207583c4040d280710b4071142c1c0e450101c00480a030019010340d82440002890102e03a440f10300760080250201410f0140d00c02841c0c00009819101045103445c0341b10228000304001001c07000b000e042401c440601018424141a900750000711039162500d031170821210708089c8000c09520301c00810089501e0280346241c0005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 196166915 1250 196165665 196165681
    0x3070806130f0509010c0e031902010302070201030b210d050901020319030212040b0f0105041a09150a0801090c050907090b03040501092f0102120406030504050f010c0906030f1b26 79
    0x1000035034840c4d15580d01d1f1090300b205040da2501040c400210140e0044001c0c00158429002805044d00500d03011480e2142500003071007140304504441c0800359402c19170788807000140207190815140707007403031420480b07000c0010b5160301c60120000c2c900c4001d41ca1002c0c200c0e00960640e54060000101480c0c0f6142528245032545801d172900d130300700312504000290307515180c001c00451410f0342c090388208031840c8051008030079001d040c41c080d082c0c9082e00704229494013403d01004182003400800c1c642d440d070401c82603186c1582c01103802540118200700301640c00001100440c0e47d062095a03070ba0f5940d00f0803a0042c100c08074018030990309440c201820180001c202507114490500e00c5002c10707508401a6a1003100c078120202d8150188020000c103030096102c80d521a01400540701c041c544413240d982103030304007803d090102d2076141c0140181c3d036042c410341040710000c9404100ba405800c08a000d80d200600784a010405100d1145032440000508800449411a03848a07d81400301c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 196168165 1250 196166915 196166921
    0x1801060206090f060c040b03060a0305061513050c0406080709090903091e050f06071509080c0607110709020a030905010c030209010e0a0e0c0705030f131a03070806130f050901 77
    0x12410030034403d601c8002442c00000c11030500403910708041c107160518120103d115600000c00c5250711a10004000010840c0ad0001c1e5111750402e08103410003c0ba14000c0055011207000d0808000c0d15040070000980325a100300d9007a20381a0800e24801e5175000011070b05200282c2102c080c260402000b5030800d50810385820a55080d181c503450704403c09031044140c00981c1c03062543c848044030700b00d130071420b0284c000d03e0668054966101001c640e20a60002e807171364880100c41140b400034036107000c0704080c4000340c0c01c071705503151000210701c9822009079102c40e05d014400d02264000745a10006005e03034000d40354594060001c2c0501000500068000d420070750132580410400d070040c86091a08a4550054400c00d2a9800349500c0741c640801441d00102d004032850702c400c01c8010740344454580a400004103601c0c2d030802c06400c011260745410300716861184040d10610900901c0340e040f286496005205a0740f20b0514000c20280d8005800d10740d8411405a2800d0203100107400190 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 196169415 1250 196168165 196168171
    0x501030e190b061003150603020904020906040e090f060f0406050a091208040506010f0b0711010903020a08160504090f0210020c041a120a1a130b07020a03080c04050d030e1801060206 80
    0x1905040b2911070390b1000e80546000d02c20104c05108070346d00c01d100c50b501079800351902460144c03006051414030004503106a1258001702080302c1c0c0a4101f2110789010041030f01c0c18249100907040c0c1d410508034011640b200540001c0c506078450300000c400240700e41c0440851900081c1c540c95107040e01c80c0182c0003810a407400d1f20940940d4001141c4100050205012210807402c440c3c542511030b1110345030b511004407024100200c0303c13800070150341c0d1414042d0107440c00c903018140394000c10a0540500d441540036034092400e00501c20046201c900410002d6601500d08514a00364a10100c0c10305100000345a8041d03e0304c0c00000001003400c10311180c2d000103403000303059007404002c5d4607610220b0a00c010120310104101d4031305154402b4540c1e81141485065108031250b5540d030902140c4115014401640804040c20034103900c241d6060b0802c0c1c9010440303103400d041801052401c4203512010f814007080303211182c500e0701c8040714442911186040320006503144c40740203403104402d03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 196170665 1250 196169415 196169419
    0x2e0501120506090606031009050f030c03120a0c0509040209010e0312210112120309060218030c010c05060105150f0301080106240f08090109051005060a1e0501030e190b06 75
    0x1000800c65840081c044e40940b10050003002019516100c100180c090300e03030221118000c014103000c208100308080d00cac1e4812072401a58442003103014500200100070081c68481e800e01c5860611190424101d81d07801100b41c40142c1d48043c500e0042c0c03a80c00c90812420f42602c940020011541e41d118080d1030b02400001d101d0461200550400d855003038203014003000c00c1425100348000441c04410104858103d04002c40c800415885040403030b00101580d01c00b4080b10303505040c03103203014880e08494400908190740d90141980b0780c0e550f40c110502415000321014911059400809015901c0c0c41c854010a15a40d40c4c40c0d01c102400b0f03100341d10469500076070800c0701d14030400d00c01c1411031814459980e8544c66014029044809820160560031b4039580c5450b10b0010070824064103c1ea00c1c021580800c480c10031400340211106550300c5121502009c1501c880c1e6070000e141d200307003151401d103000305400d9080c103100c0b42001100c44100703000c52080b5250400304140210a030744a0101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 196171915 1250 196170665 196170673
    0x150909050118140c06040b0a03021b0307210807020c10090902040807140916031109040c030606110102090901030b07090803040621020403030804121e05040906060c02032e05011205 79
    0x400d0040c4805d0740624007540307400d0032003800150642403090b4090405201462541d656460301b10300715a045500c20074095410411809034440b4040e00b14082c0103942041c2c1c541942e02e03140001000b52a6100013060314454100600c00061542c4a220a40042c2c00102000c40d40e69561710700d810b83d980100d1181e503071440000c02d141000c80c0b5140300010b100c0d4190b801c02200d6400902011801440060740710b00c0340403401c2c0400c11171034542d4407601a11308442d440000707065081001c01703040340300d08005161071603004104900e05516850501c6044a902515842a03034888080a44080c5055002806288004600000e140d9031044000056040d8602080703030344100283d814080c6d20980c00064081030b100004034000845010050290032482c1c500490050309103000c012411000b10a4480080e00c04203040c00982c0a80c41960000c240c0d9080c04840c2d82c03015070100340c440c24142500b05240603940d6074910000441080c0002c081031400c0100401d41c1c40d04407a00705014401c50076212441 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 196173165 1250 196171915 196171933
    0x18091202010903080a15090c0c0c0b040b0f180d050709050c031e07021614010e0406031205071e03032a140a0c020d03020d1215090905011814 62
    0x4018854404507070f825680e140d566507140d11104001e803036042006103460030208800500310040e480b40060038030b111b603140080c83c9100c0c01e0000c01c0408641000c1e904d11800c000802130400c2c40c00803504500704044010f070715041400101e003e01e10742c42d1585600112040c841808101c0c0100c0d10750281c407054881049152108910251680000c03100310001000c504990440046080d00d103907444003442c8125021060700821040445001c4d9000100f07401d0400040d56040da00070b030a2242441d4269003c201076440d6454042150181110807004c0c0003002800005202c811801501743d5808480780d140750000c5850000c0c02008160b40f803000003001c0517801d0005190741c0d00e1410014050345d907030003240d001c2e2000008a0fa44414405824000482952001610b9010001c5420b60080d0047d2040817042c060140c0601280004e0902e181c1c0740130700394580b550100d01031609440000344001004d8189140c078500504013042c1042d000f0032541442402c000401e0340d650b10040d075940a56140b51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 196174415 1250 196173165 196173167
    0xa0f090303020c010c06090c031202100b0904030e1203040806060a06020f0703290a0905011506080f0402010309060f05040c0b0903070b0711060406020109050c1516030306180912 78
    0x18045000040058200302080310301d80d03224181c84185607001d844002030709038203691206900c98156001301e41502200b622601050f0b010301c59110045481030301481821070820015542000040000301070054511681849803510500000382c8540c85040342d50701da844410042d522a0104c802503c0381e00800000720f0468400b10344102c196000314028251141141d8403040302d03101300000408240d840d03889100344451090499402410801000154040c845c2011425100c1c084000c0c402817121b50f8081181310307400000303140d1180400014803602d8655100407406000006400303003680c0d0030042d4680c40d500d40c1d50700c0705014901c131f011100c4920340d40e01d40d544058081c1881c0c15600d80c00003a000c1108003000c1c8014500f440c440c80d05500078590550000300990090b40000340140e541e80621001c001d010800c0112504040301e1441c030600c00441c1c0c00002c0d00c68641d005200c02076071441c0d00105402900040c02910807030301d44061600301c0b030103204000c12a801040d160b04483d020840c000c0d07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 196175665 1250 196174415 196174427
    0x405090a0f1a15090a1e0204030309090b0d232a01020c100212090d050609150a0b090a0902040b09090d1706010c0318090203070302030609070801050108390a0f 70
    0x107074101409001d29617880c5850300d0010007100e41182510042e80994400100c110b2008102441c402e894048645040c00d040350200c1b035110000c01d0080c42042842c002013001c4442c1c009040ba05180b290018a011500e00c90501c4003010040c840010200140c3c120251030071010303a40024280e00712400c03074112a0400c2640e09441820070301580001041c00035005018004001403c0041c000e4914043c0079902d8514003030084803651072903002450400c4100d0040011160481c0701c4000500c001c05880300001d14407500030b001844441c0c1e4400482c3c085403250b421041000a00405401c880c7c504486843d44520040080b580007940e1118945450380d2004c0c080b41c0a0341042c4d40780c20307482c0c40c2c550b0151101c52441c01d00b0312210341c000c00700080c034000a0000314859060f40c3c2d0003607101d0800000780a800d100c098031007001e000c5640010b20141c1d911045842d0300c0005150b58081d8866400e001c65503082607162040c0c503110008807200a042a1701e401001608040c0c1e59000d448414020308a0700 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 196176915 1250 196175665 196175701
    0xe06040c0504210803010e180a050c10030e010510060f03020301080a0305030601090b030a09110306040201020a020603060f09010803030619060e1e060c010c030b04090b060405090a0f1a 81
    0x10641c248800d00a080c6051401da116031030490303a1180e0f0300115190515190000d030311400e1049502420807070440c0c942c0303481f20414075201009200c200c3c46075960941700c06800c22080e0092402c0d83c07a0038006c0c1d11981002a080644400800c01804c0201c0e03000540c290070f01483d004150703142c2e21400001c2c4603100b22070486641c00c000c2e01010fa203540e81128550300203001c10b410040180e1000c188001807030001e5000b000310b41800904030030b082c03600720464151100c1da42c1c401e8010b2000c22001d81d0300442d0160392290304a50942d52696044002a0203e0040950300e0f0481e507450700100b49904000001d50013140308541c12000e100662904040b00480b0303008410005060100c1702015041001040021f80074010700303405010660404592103030000c408000d840e039180c0c0c400d14420307a00340c03103441c0683e0001d40d0107018401e081d80350401c502401800050140c2da541e0002045490107100489989901410103c0c0c03942050514080c1188104102e201410803000400c01101d00340e824548 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 196178165 1250 196176915 196176917
    0x306070513050f220b010e04020406050d0e0102160302070e010909120e0103090b04051f1802060f04030206040612050a0204030209040b18061303030f0e0a0209090a1b0e06040c 77
    0x1c8010704150901c04045a08040c2c00d8111000c0e200041000000340391032180c3c0d01045200003007201488000504a24018078400c1c081c80c41000203122007a40601222a842d802600101d98076003e05c1c42d560080c0f003000e02d2116004442c5d0554400c265003c02d088046a140f5035406c0f8003662218415011110120300081034030014190f903003009401346140111902c1c1c14180003800781c06a407550394081900700d908036110f07006601070031840c510000c0d5400c0304141c8800200042c00b00c1d802848021a0a400c0103481617501280d640002e2180400301c901450b8050f03e035036259a6503410241c00d0260491100082c20b0500c400266040c1e100e10030b44044a030014014007054446071182220b582000d0001040d42c103142e1710140080e01d08202c0355000d08400c2019448012103070800404403410640481152824115420694100044d840e0b01d041d0301150020703415124000b0b25440d0084088000707041e400ba400c10100b0300e040f450190021149030407540002e680d28841080102c82c04086000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 196179415 1250 196178165 196178197
    0x1216090e0c09030601060c0b0f0907060c081e0903120901020303010323070b131706010b13090e010b04110a080c090a080a060b120a170a0e0d03020c03060705 69
    0x11100e00c000d20019004958004010b2a048280e004203007040002d8008a010a51261800f8100b00002021590042c0c441d04000000e05000d45031544400d5503216240030840402c13002424401500c0803103c20070b9201014174a06103182d00d0b0041d064004c030185510030300a000c800d034455114201150780310710050f4055403940c1e081d0fa864520089410030500e1110903d0116038040700d0b010040c0c2c101410300364005039215041c81040440d0400c003a080f9404490303036030404812218001908a0544013940b1400303480d4010b07a80d00089462a95101e0b166850820764600584d4606601c0301c0c1d4980303000da600b4403106108445110b00b52040581c04000124002c0025803101120f20240000000040030300c2c9005a80c0d00040303251454001080e0740059131082d413104c4074030340400d04492044404001e1b02002c14140c0f10668611a241020302c00b00700c4c0001c040d07281500c100c030f0a80d032181c0e00800c44040c00d41070381002075171140c21140440c081c0c0f06080105000a00a000f0f6507440f8408140d10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 196180665 1250 196179415 196179419
    0x405011b1e030c030e01050a1a030f060f04020105090306040f03020616080711120d0509070e0601050a11010b100c03020105151e061e120c09011b0c050a0b121609 71
    0x4400400c00f0b0010202015036079400a18050004e000e410300907009502d010a10341034500d0403443d0324a456203814030a1340b00c005401c02002c00408d00551200e00141c81c0d4145030344500069401d0b205480381e07541c0c94081e60b1b0404c820000c07200300c4408602e0080d4212401580da4040b09a4a1103c41840c100031070039240c0040c8e00c0501c503802410b0517602590a940d041c100784161003a0356042041c504089540390307410000056010020100240b807400c50314401810401c00282440c0702c4c007201c03d000c000a0410300380007030b6000d400540007400c2c041c2c654140d10940c104000c0c41042c81d40002c600550130640442d10300780c40c08100c2c2c090f4880c000e01c0c5041040c80c1d249141c1c0e9500b44031000d1504640f062243e90030011060307d542101c42040d05240e0741c2c1e01005800046880801000b07203240ca075091000c042940da0240520740019803280f603000c2408650b08000504003803590000307a00c980d040e41d0100314070040d040a0800760b80b50345100d582946a4103401806550440030074030000e580a203003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 196181915 1250 196180665 196180667
    0x70203120105131d0c03100603020a0e130b34080a02131a090909060f0f040302010e010e030d140f0a0b010504090212042a032402030405011b1e 63
    0x20443d03030054144009144400140c070040c0e12910382a80c8002c1d90000c042c0340e001810240b0180b02079501c0301104001c2542141c2c0014035501b041c0c06045001215600000c0071032403200030b10400c0607009800c480e0580f5200040a035862410032507401d40c0c21800080c0c0024510007842c500d50134015441c3d9424a030743d070120032002500310340203011400c4d01c44100040c01241c2107503000c07a050200d8404076a07548003582805801403000e005410154440e10802002d10200d11134260001d0585801c00310584580c02c040f40075104519030399000754a080c01d9103102c9100000100340e980c18446007400142030920b80885e2406048800c82c075060b10805c001041860030b90301001018105060103401c25440700b03807a8040b83c22580d1884030801da014140018405503403079000e00c500314050a030800314000a40b02c02e00014910000786802074546d80f000407d1708800800030303c0b4100da2700440d1280303064148103020b0203104e1101148424121181201c840c800c6941c05020451440d034056600c2c12800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 196183165 1250 196181915 196181929
    0x3061c02130218040908030a060f080703030c020a0503100e010b2704020406030b07030608060114030a0b09071a0405090601030b061b03210916051005030a11070317070203120105 78
    0x354440440781e0100e9803c0d0a65461003840c0b9150300400c4000e031249400c041c41c4081318003940244005180140040000c00400140102569810b24181100c0b141070700c0401c000c490290020399050049100380c0e05000308c2940502c1e24040301c800244101d0295806100c9686604800900041c0c010110041d0304000c840c4041d40080c13000c3d0001034020740d40e4544190b55403041d030341c4000003602e900f01000115000c00c1038a0141040c12650a00c1d408240c00095032450944002060540c4001c0042d00b0b00d5414013010000309007010310351190b510054021070082e80b140c003c2d20700c00c2c2100301c0821065442885128032030140545003e14240b0800340740000740e1503210880e000d5101c108480e004140001600d200d003900800b03d88101400c045124508001d040078004014001c0400104415510034040044601003410050354039101c41d0450000707801300d1010f145040c400010000101648441d40120300100c1c140740b882180c0700d6000407600d0348034561070070b80494072510042c40b9510b4040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 196184415 1250 196183165 196183177
    0x606021f051009110c12030703060608060d02040f0e06090109021201020906122e0905070804020102030a0e0d1a01080d03060f0b0a0219120e01050301080601090c0c080304060203061c021302 83
    0x803000f907043c140c255010900d84203103c40100c050400200a00408c1505401080e000d0300181c140403020385400008159004143c100c00382c82035446500c10281600d0742d0384050500f20b990010341c0c1c110700e40313440f1030740c06002c03030201c00c9000c2c0d6901d5017011210041071007030b1520364400a114515041002070040c0c1c003c8000781002d294500c407440410302810310700d0443da0301003030209580c0046178600041031003150300c003c01c290207000800c010400141c0e40407044400c0e1401070b080c11075040000c00c011038080001c060004101c05d181e1074140c0ca400180e82070085c100e85a28003140c060b443c44820445c1510307907a11a080401000403000d000110140015040d150700074811940b11254152103504511032a110039a034198428800c42c0320907a000b11031528145003070070309a255500d81000140d030341805101d40b4004d640d807541086615032158000b0f540060700030204a4480c182070500344005d51044e100d103449000c250003c50151840340c001e094180f0b400a2a100002e00c43c0034640019501407 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 196185665 1250 196184415 196184441
    0x20906070f1a010303090509010b030f0606130f03060e010b2d01050f1603030b040b01170408070b04050f010f0c020607080a02040503010603110f010503011518090606021f051009 78
    0x19000e07060b1100c011550350300079030280d80c0c0d1280d254504003d0103001201038000610b080030800070083e6180b0781700c1e40390360040070a03070b1502d40d40d6101000c40303001800f5a400c4007204426000c000003d00c40250404008903217060000c109900407034042203500b0760001d40060504200005c02c62091110342903000310317800103043c640e14000900c0004a1164024002506409201980c0000b40b5605100e00051100700395010404406004006081c0e6081e84440320340881469000504000c00c05042d114641d034400b0064066003014504641c42c1e41c401219002c0d50b62801c4001c1a00c0c40c0307540103492409100303402602e416100c4080072240f00100030518401103408000c0041c583e00c0902c41c9100441c0a01c00341140c641364401084000907070081c1090421200b0300040c49010000e45135442c441006041c0031240e0007001001c01c0b1001c104d50b0100c82900d00e070000019846e80c0208403c0c200003141c080015a92107001048401c0f100309503400e46004c0c903b0340040c1300b0410f2941c0000e07813001807 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 196186915 1250 196185665 196185683
    0x51b010f050d15120605010b031513060b070503030405060f1e180f01020901081b160515280908030106030c02010e0a060b01090f0605090f040b03070b1c020906070f 72
    0x12200c1d03090012415030702c1304e1040c03246543c0101c10721105102e032078054a110200e451441c10f0094141c00c1c0c85604491192181c806190604020b01284d4080d0b0003c1001500190321018182000d985a40088030151a0340c000d000000d28a007500c40200343c803485000c140040e00c48a201c10501d1441002000851070080303032507043d003044100f00040729a84258900150707503158000e000600c841c10181c1b003561219410160111134000c0350083d5500d07042c1c0540f400c4210011401d12514103415947c9034220000e9600911010b030207241201d14040302008164a043c0f00c181503100c003251107500001d04040810720060020500c82c3d003229010100a10011481410221600c1d00b04986800d046507071076a40c007070042895030002135400c01021001074400641c0c1c40c0440140c800c1c442d2418491043c00d007203040414640e00d607440711041d507001608860070552500c2c0020707540c0d40076060300805070710201000e44545103240229880502c0280440b401c00f00b095540c64003410000c1030481d00614 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 196188165 1250 196186915 196186931
    0x40f06020a031e0519050c090f030a080c07030209010e041a07051b0c01140a1d1c030e0102010e1603080904020f03070e01030f0501150815130207051b010f050d 70
    0x50078540703191000040f4000619070a20400184010034110007400e4020f0400003081140b0f005142030300c003a100151103140087d251000042c1c104221032a009282030404540480300440000e400819240b094a562600e641c9134088102016000ca5009104070744240c6a925080340b08084ea80e0015024240f440c140042d4401210b01780714580701910284c0d00c00380002040d5a0700031050b21945401c6601a4641056500000c080b560702620041c40f4940c9500044501c1d00c0b5907040390300188071000e64030803410f03a9280040c03030302c00c000d41c2460056003018849800745201168240c400380082c10602c1826107541d44092540c6c03c60404503034050f03801d21048419012503401503205054656522180c043d10a0026040b10000703011700707004901e4800180a07141c6190305040f14000c440c00c012010365154001404512a008a010340201e4202e0ae40341c43c11010350003804606105e0320a50b071091000e25418030103500c0d0014034a0000e8a401600c1c90f8444c084e90003003502240d800400310342d400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 196189415 1250 196188165 196188191
    0x30201020f07050109050613020d110109091a011211121306060e100b040b09060d060801060605070c05031204150509030105010f06020f07050321040801050f0f0708040f06020a03 78
    0xc0c204040a0390f580e51201910800c01c0003c2c0b0506c6d07401241d119000300c0b40c07105a008a4560b001d1894000c018604405030349403241c1c05214168014103150314148104228140540448602d000c01a8040340c07030345000441c841d10710b026190b003e20340e102410b1701b803031100d032100380c820b0704060a070b59000d0341c803401c40401141c0700b4040c1001806a00a4904242c14460100c1d0340c1c5440c40d500c01e00360040f0030301051150700300d180100d60800ea01101c85685070f1459281150050400368840204c640c41c1100015100703421001400340c2900926685804564130300030306072510080806441d5140d010001800b8003c400c1011042d8420245000c60800300c111010a085410030f0b082101d04900c1c21200f0080c1c29810410380391016a08400345c40c0c0580b619001c2641d5011610201100100d41c0000000700040b85055070001c0641c400280b1030741c00e006490307a004030000c1c1d81d40405100c8000008603074030b0040240340d025a0740014480e052012039102c540080d040011010105612140511980 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 196190665 1250 196189415 196189417
    0xb040b0d050307030809030c1005151306140604050a060f050c0f34050111030c011401050328170409020307020d0206090a05071703160804150305150d030201020f 71
    0x20340310390700540d40c440c0c031401e000c1c1000d080104440c055500c1044071441d03410000c24442c0d20310303e2000700412281c6038443c000c3d02004c00d10300c43d6074104030000d04ca00898440350304032008464440e10740a005150b02414071070107100d01d010b506c7e0801e664480403c40b0070b02c43c0d503581e4000c0b000d5141180c10207401000300c40c1040455401240c00d40e000d035048030141004000301f541500400c98030038801072040680c01105800a00c1400d042c0401d1020318940d031007061003182c4840b01d2140003000326011015400104640a025040c024421184c10441189940780a07050480503500c80350210030042d0344865020320740c1a800500500240300c00109102e00380055405919180c003d0301c032a500c1210000d103442802040b0800c0d641c4010040c00c08201d02150010540310b029810000c181c40446a451a51056032211810b00580745102424004003401600c207a8150b201610701c0c56030b00c0c030340c01c0b03040d40e00688201000e01048030340154185403101c130004005200b80009820600d00ca1200c80503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 196191915 1250 196190665 196190689
    0x10b0d0c03030314060306040609051606021c11071a04120302060f10120b0604060f0b040f0e0f130201110304090905060108030711060a170403030207111002030a030b040b 75
    0x10300380c5254018000c05401d40140200031101441d040d880303103130a0000940d900f41c05880038020300e41c0c5500002c24040184884603c1680c040c40361010550380d198003c1d5100c65080340d00c85c03a5a51684103070704441c85440c1c0d0074407080e0240002c042c92030411a140400303001c04001001d11240400c070000306c0b155207070f50402e00103020f80c0242035545444000c2e400b01640c020000d84840403405402e100f09006113400071300280c0c100c0c4081c8002d40d1848007043c000c0091350444004025100d10015004818400a0082c0c880303001c010740400b641c40ca0b1103400b4850a90ba000c1c1a81880e500041c1c809050281100042d4014035150200d124012641811640140c10440b0b107582c41c5d0f00c08006106041100c00c0c0180082402503140142984580e000003034041409441404006007011003a032252440d140c0d4240d5071102900c01e41401c0c58003800035030102c0c1c0d0854204401c012868000d242c900088001006c2d02d07005549418541c10003180248030007030b0500c0e80075aa80c034451146480c1c4a01001c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 196193165 1250 196191915 196191923
    0xa0605070305091b09160e04110903190b0601050702061b01050a060b04030807140708030d0b10030c080c0319050103060e070f0f050904060b1008010906080d02061602010b0d 76
    0x200c2c0d051060009040c201c840310094181c150f4003810001588403020260340c000c401c0c0b08001c100403699901140d0140c51002d00c20351040c201210201090141030042c01500d13000c070202c45041030118101850f100a2850240c60351682000140965020794020400d5610003000f8a2070910551341c00d4400220380c00c4840c42c260365441c00c0140b070049920841000e800450380450400c0d103160349001003442a001c004007081c8118000c01000103040100340c01403c0d0000c1903e84032802809408001c1948041081c0b050300720112005a0301d000703101e91100340d0410b903542d18941e81c0b60307881c000466001a01000707a020302031240104070000c81c420180654401c402c00320b000b624490500d440c0c07600c550004941d20308104000c000000ca508504412a0b2043d6100f01003a0b480e07080c001c008041544c0c415421203040d680024409500c4002c19060300e8242030200f00b026250340c000f6076102c0741e610784107000d64450001700d003a28031550700712150004540300100d180c075164402310f05030003200c0200712 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 196194415 1250 196193165 196193171
    0x902161a0411030a2a08060a05060a0e060f01030911041d060906070503010911070606060309050708010e0d0e031608060a050903090a05040e01110301082808030609090a06050703 78
    0x108102c0c6100e41c0507a9034804070010440d000036a11a810212015050740078081140701c1c010042d045d604144000074a040400c0d15100c2c504010718401403c01225000c0c0f1402e410300c0c0100d0208014140c1c2e5015941c081c100312140b00216005500808640405031034025050103c0d9802c3c0d0b446005a841381030204042e42c0a0401206800c2d01e8032001821103d9175400c640c04202c501c42c2c0c85000d0b42d0440e0310741000810300f0700c00041d03414014440e51070090040ea06290000c24420741607000104c12600c6181100d10346036030740481608039000d2030742d1981c1d6134010f030b000031641030310841009a02c400c0041c240d8101217682032038803119142c2903001d4241900001c080280c290450b203e45a03014100d940518178050565000407030f4042e0901076144110b80d03451341c44495075800d51044000040c050710403980e0756122203a0079500d40084200781e40c250034410f0300d2002c01d04200b504815241e80201c9481c110703111101004a401d10052803824140704541d0518045800c074050326010382c059071000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 196195665 1250 196194415 196194421
    0xc0803070c05010b0d0215030709180203220209010915050604090e0610030c12050316030e030f070311100215040305040e01081501061805060d0507020607180902161a 73
    0x2071400d4408120015201c2c1065002200142c1c447c1d000014403020280c1c5c005031b803641c901c1e405442c0860710341c01c030a03000158855224540c240ea54001c2d40035805e194030f0600504100c5010703580400c81000000e403c02030500040040303900d50b401002c5a00c5040c41031030f40d03c0da110808181d003600700c1c1c1c0c80031401c15159084104945024007100350011403014403e603009007507480700c01c00e411141c03061006c40351044070580284801407068900d0113003500a402030312100390400400f149801c01d80d69100c1c2c010581d00100d800310010b4244101c0e0792003411504099024000c2085010380450700205500600380607000c0c0c065400300d20741c03003188291541601c907810100030916810058206140da540b18803141e4212400c0211682e045451b41d18004405802c1100c0c81e1b280c111186d400507400c9840840e42e002801b6607900b005100782d00342c1e0308440260b40c075403408584c206410000c0200315201090140030008072030b00140030000000c0781c2d40304020000e6031544940d01c110a00a4619110700c018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 196196915 1250 196195665 196195673
    0x1a0702040608070803180105040e070e090132010203130f1d0402010c0609020a08031c1401030804030f050a0b010e090c0411090d020d02090c19170a020a0c0803070c 72
    0x1520001d00481c0c0b005102181c2084025585d80c400d03691001ea0518801e0080c01c02a8880c4007100c010300080da00001d4141080302d0050621003010015a22a284100c0007045280302920b6030740c0c602a40400808030b409805030200d0702d4000402246045000030801003100e038406c2d03c0600300400c410f24010b40b0043c40c10080e0070780000c1d209080004400f400b0305020240c0c0c0d010780500c00743d070380016000441c503401c1d100103800400031768000c54040c0000304102d1105042c21440140301020b4006c14081c030740b199216141140303424080200b030400140b109101003520f4080720030703141d4890390444000b03c0340da49401e003416800341d0100e2001d80c040e20170001782c9501404015032008080e01c0070301110640b0030380790302c046c084c10064034001d13040e0070f070351030107660320307481e160300f0064000d081200385007803200f0000e171546d001000811142c00e08004240da00c62180d00c2122002c2e0300e4008140b456103c03820032002035402402d2103820000205c2c0038001240307081d07000b14011300e040d4440720101812454 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 196198165 1250 196196915 196196921
    0x4150c12020109030e13060f1d01150c0813050301061403010b0d032a06020c1501080703030c080f0903100b13020412030e130e0c1c0302150a061a070204 67
    0xe03110071a414407001d280001c2d0070481058103c401150503d0500e051051030400901060b03002404040348114001480d00e090302d00108052742c0d1f0750261207281c1e02d94100312000c0c0804400c150010f0354071071040380420301d00406414811103401405c010035a54400080c250364964000d6064241301520304c0025140910a50400c807409a030780955444d074a48002d0500070701c00800d1083c0a00c041c22174007220481a155200c040e5124504545900318004084d0780c44a078010b290703030071201c6c0714000b10301131070b0000302c0c5011a985a902c0022020481c0e0700e41c400e54004040005402034248106103040e0b4050041e1010600c03400070014040c1021401c21006512821070580118410030050021400d003071480f2162540505002a0505c0588040350354580c0c2415130001d0a0726042e074a111406000c181a0b444000845117440d440304000c0b42035400404100c0300070050b2744400303072030b8400401030b200c0260700a070341f0040000d1031940c0e50000e58015000440c80e1394a17800000e0448210b01c0c0600c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 196199415 1250 196198165 196198193
    0xd08010f1d07050c01020f16110a0b0a03021b06090a06050604060b0d0908040b030a020c0106060806061204080c0307080910020703020a0911070c030f020411090102150a0204150c 78
    0x81c0e62000300306032000107544202400b600ea0420000005408480c41c0740075012106010f980080041e695843d0000690b00c0509003403040b10309550f01000611546400d0000700d040c3c916401c080c503e49200c4c844183c0080d880342d411900c20032130610245007120b809100c20b0f480f0318441d40280201c440180790543c1103c5001f080c15210394500182030109802d100c040c0e5800719404d44002030640741c07904122603180216482001303005000010030059141c01d80103066603003c207200174061030361100307400d9441c0320341212400c0d00104140500c20f510080c0041054000340505655858903000491040c2503038032510707050740d20450001d42070003030741080810314404007828406040f0540c19640001c20a12180c07107134661144d00d40f14206c1040c014070044a1109500521480c2141da40c1c2c51b2007010b00c3d40501003648100d03e000190548459010115042500140c0c05091400c42c3e100070348030514006000c0551843e400d00001c10343c01400d214513080b01000e5200c0d802000300f140b5010000304009 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 196200665 1250 196199415 196199429
    0x1012050303060909070b0a08100909050d0e0a05010e09060a080d09061106070c0b0a02040506070c080c09060a170c04091b090903020303060f18070e0a0806060a0509180d08010f 77
    0xc035042014050300b805664030087e0910703081c805c6807074220010700003180c150018092907103480d01010030401c0c0040c020f41510380d1612601c2c041c0c40300b00108030010304140301d4240898141d00d102240c83c03412061a640c0060000c2400f207547d40c541d00030b00d01d05820b11081d100450f0b1440e00602801d900490b1034407400109074002c08070392034411001840c84000035002041c0491a10200e12561041c0d010785001e402c0180c081c0740c50702501c0c04c00c400d0381c080700c0c0f040380320a00643e62a4181410b1520001d4428080500448101c42c070384400341090300800b9440c4251030181c2c1407040c1342540c442c0154801c96005440e06810f8040303000642c444080316a21500c1200c1c50100c500300000d0700842625032009007240d50411507080701003c28040004044048081c000c543e04000149410441601e1030304c0781505d42000c1181c54482107640c0750000e9840b640d000400340000c100074501072400e40d51010010780d1813071542549201080ca011101c40010000c00c9101d40140088070030360005400620f62 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 196201915 1250 196200665 196200673
    0x90c050a0b09030d111e0a060b0904050705010f03021c020d06060c050d26071d0a0e060609060c120702090a060302180402150a020708010c17010b031012050303060909 73
    0x40400002d55641d13401d000306040c400c107542c1440042e2014080310507008000d01e4208201005070500b40c1c1c840c2d00c000300840d038191805070040c101d030500805a911407980200141070581c200001510f58400040d100d6007003507020010317203000c03003042008010400c0055a02603254054125150151110354116100300100c4400b400007081c0300082e0081d00e4101400c004280d030591045418100540080080304459840300780400c45600031091800e5030a955103030b40325443e2000800010800d1481408103641001011a0413860f08100802e000c840040102d450076140c2a121401c00f030461011000f01200480c2071000e508050401c40d07801100c544003044800d05503800100380800480e41c20305030344c03a5040000c04540f40c1e421708590209482c1e180c951101d01c0114000c3da2021280034100f9154204010440c80e140070f1460301181c5940603049440c188e09080d00c6034079541000b041480020914240010380080003414000c000c0c1c001c3c005182d9900c0e0101c14401c0750b000c007a00c0d200c241d81c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 196203165 1250 196201915 196201927
    0x10b060a1106060907081605040302150c1b0604091e140106030f110304030516020901080706110f06010b0a091a0301170a0201081305030c0d020a03080a020909010510030f090c050a0b 80
    0x146c030820695005030100c0c5a41c0d042c1d540f006048440340941d800003904415280012284d60b940c107401b800e0000c0c141c008a94500070903020302c41c1d041c903064018070382082c000c0c4001d000c49542a002003203010b22880c800f01c89110141a001c041d10f12003031105802841100051001c82d40c14054804010032010042c01800141039556900303101c0100080d0411001141500015442400040740c141c5c000309030745c00c5941c46090b03d0303403036119034454071002c0703484a4003c0d49241c034003245040b0f1000c0da60b0045c040c0b076032820f03614850550001845808202060901103051840c209000c034a450300c030300c0c00a442c0d40c1003218082036010194480c50b0103034088254500140c4e403040000c1e9120711145410118087ca91515170303c0e5010b401040c01850040051201a10b40d00240360752003d800b030784da01d11850715405404401ca216010180d908040d1180042c482d605007030740070766807003140c41c500050b440300220102030844410b201c0888111403031100400151400100781800f4140c8c0321403241c5070113 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 196204415 1250 196203165 196203167
    0x16020703030507020f0a0e010617090a020f0d0804080705040f0b03070b0a1407120806180606090a08060f010f09060807050409080702030706171620010b060a1106060907 74
    0x805100040410100142800454550003505403030b442014040c580d00580301c02d000610440240120400110400340384e006180069003c103015020000c003810203c1200e8080c04110703112107140641040c04080c1143c00544034400130401042c1d103c02030f00405060404110507900007a80c104070107402c041e15101c82d03942c003080707041c01c840402090b95515210080c05991400d40d0140611452001203042c4081c800d034004411024203055803071508030350755041004180425501c072100700010703203400554a810040700a10709650001d03d0b2041c03c3d640d904030715140c03040413034000a030303001c504004000390410f505004001d0042440c050002d2810401c0b41551502c1510032284610f4648032043d0900c0010340032250451340140030ba411403a1a4240035000b040e211944e0655040350700001440302c040402c0140185806079207603690301e00b28170314040210b156612401c2c0c9a540c0ca03031454406950341001000f0304005034079407c29902810850504000e0b00402080c00b415904040011503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 196205665 1250 196204415 196204423
    0x5030c1b010c1220030c030702090703020309030706020d140103050a0c060809030a05090d0b10170714010c020a170708011b0206040210020c040908040302030c0409150b031207060905061602 83
    0x1c035007894015040105046004c003400c100c013540c1c08403404002100c1c03003150300c0032009000c444d000ba0f80008041d1120340341103040348811240700585030070501c24031002544c550004c00e21064001d0f40424428100c4200309541c0d075003a030080318258441280c07101041952008074004000c107040080c005d28241c0f400e51b4481c1b02d40f140d800100036000031441002d540d800c00d4140310f40d4101420841c18038000c4050006074520340103d045000020001000b5190006101c00640c1c00b60a82c08030b003185407900544640801404c1240d100741140c5005c03c032000c9051501003040903020081089a28200e842030841c2d1280c142c000303558012002c003031603294000910ba03803c1941605c5a0104107401c01d800c0303003844450001c00d07030300500b8081410f0600a8078000390054a00803000c0c0c030520850348041204444c01c1d40c5008011881101c000e071030b02e00c0c1c140e001e09000c1802a090b03a80d86624617411018980c00032408640003540c46042005112081180c2d030390100403a900c2c24500c4006810103955 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 196206915 1250 196205665 196205693
    0x6070906111e01020912030f09060a170a0501090f05100b0307050c06010b0304020a050d050c060d15030602070c05030a0803240301050a09051207081c020705030c1b010c 74
    0x52121070040706039000410031890b507030034580d8400304510104030350580780030b540b00300b09480c86501029541e2072002404011a401c0034816130790b0b146020b0b07031710017070040da500003a4010381442003c2c40700c03030300c220b00345000d0900c90750b41980e001940b981444c80b0300c42124a403c24009040f0f140c10200109480c0410b03104040d60340614100f42c680c0e94004040300e0314803074014001c1c1240a02d4000040120b8024050342c0904d100701d5100300d10603103032800c2c40000c0e900326101030a264001000505107041440081c9030001c0319100105501c285206031308860381450b40210b40341c590015250082c04445420040030701012800361441404030388070000c0c035000c09040486250510180c0f8503122511072140d0310284006802441b007860f0004844000700508401903545000b483c0c100d140007e0620300b00d0b084a64440c028030300308644180e003003104082c6803094083c2e81e9420070198020400420241c203241d048000200030000b4403151043e5144400c0c0c05280c140700e844c032401000035011030340d00c0352 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 196208165 1250 196206915 196206917
    0x150603010b0309010219090501020705060c0d0c030e3c010801031106070b010e0a06270e010e120315010206010302010c080702011413081605150a0504030b180f06070906 74
    0x2031683c44941c000341c024030584818402844403403419426280e08005003d08460098003640d5035290380d9030070b000b400e00c01c805070300a058010590707140072a8002c00380048083c0c005d1418102312400500825030554201d40702d2802040d42c89038840040e021100d00700382c2c04010b240545035000c601d0001a04000c0180801000b0711052a4441119101d580680719129040f052910455130745141140801c141903911942c480c0c288000170558510031b0111800c2402d240e401d001c01d01028100741d00061004510b0b1055035506c4060a240400d0100050740e0040e5400c000c1d00d55905108221649070745425891505542102c001040540c3e0084800b2007401d40043e6050b54070022071004955022644001c54010100400c41c030005408280c00e01c404d840860301180c1d02500d862404001008881c4510307a48445c0c12003400070415040700c0941602c2c407007420080d08280e01d80d81c3d601c3c80d00030105e17116a10203104a203400120301c030410600c1d0900c2260340240805080c0041c004051407018050300d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 196209415 1250 196208165 196208167
    0x4020408190618030306050f030606030618010608160501020f070b0f0708120708190e0a14030d06180b1914030c031603060e0d021b0d08070501050a05150603010b 71
    0x10050000640208054040014140703e68400b0340c82c001e0000c00103406054003911700041034426504000481034015a80200100510364880105104882014028000c1c0d9501c507080003501e49010003980400c0c840000d0405003041c1050700091400011640000303841c0d010442c20031100300003604980400c030510b04001c0c0c2c0d44000d82010003d509c120b40070108000b4003002040540c030b5220300218003404040098181c1d585454510300d0543c0d03d26007443c20a508030f48804030010303c0d240105042c19281d0340c152400c00d0031100812040350019441050ba00d601c9002c00c2020f041c07030707100d03601e045032088483c0000c0409021042440c0c0c02c3d64003d91404802941c1041e09035601048035a048050090441d541c200c035080c504048840984011503040c2c3c202600c0d948402008124240013400940c014903141d8440c10b94031440c15902850b46400c082d0003181c1d00e000c5805d503802805030500480021910f4101502014100c0d4030042c80100c90f00660444160b45a4030242241d0440d050380c001c035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 196210665 1250 196209415 196209463
    0xb1e0a0b040204030503071a10030503090d05010b090f070f050a02101512150c022806061a12010608061503090c040203130b060d0b070c23150604020408 67
    0x801c0c0244200e40004d8000d1001151000c10082100c0784140120326240360b450490311083d000c0d055140c1c2c2c80c00001c10179003080c0012200d41c20701500b1090058002c00000c01c08107000400f00c0d4042c0d07000e44d1200723a02c10850040112882e00710f06282a00c0c4c0d910718216242c029213102c02900c0d844601580d15210352030308540780b8214030455240e406465007440003c9200217914001c400110342c07140c0700c409242008d2f8505a0b0b01d0000c0b601c3c203450a0044407080d6913854034a10040700c2d08503401d0444206503038903c0803071800403401a22600311090290b03295200d1a03c45824010791050744000104480c11080000781d80340c85c40f50121010f04200000c0c5c0b1390302c0b042c000a0030030010700c00c002e402030300c003000304036068410080c003000f102d00072000410b850b11343e1003d200b501081c2c04c5024004d0780000d0081912940705003a0480c00030300440e02d590703001584039044415048046450541030b44030420345069503110b1400507800080484003185080d103491141e607110f17100040700c008400d900c01c0704 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 196211915 1250 196210665 196210669
    0x3070903020d21030207050111040e0112081e0a30091509081e090a05121009060b030c0109120b060310020703020a0c05041a1014040e040b1e0a0b 64
    0x100c02e4064900743c1c1002e40900c0c02074024000d41041a050b580b0390700b0400c0705140708038108200d80540b0300b4403420040c10780c240415840004103000313040301d140404001c00c122582e0070030f4003d5144000d04015590b00e0550504c01400c02388001d5018002c508250001600501e5080d000c4030f21540390180402c0c6038a603401c080000ea800d40f02040d041c00c2c204044c0c02d04104c0e180004208804200c550a480000341052500d21806a00040b64000c40d0006080c4003034070385040817078120300180c021100074a5030700c1a000161071041030304540341e5494034801c1d442450103002820360203000303203014113016141429090010035105406054641a600454050b40301400440c0f841418040150b580e0f41d42e42c030f070081d42c481841c1000da4407108490300c0440c441c40d041c0640750800c0741b0080084d140d80c410038200001560000d00b480e00740027610460f0400120843c0140c4000c1800c560b00881d54507240c04c10707042141c0000e1014581031442c4080107041003280a08035081002e50000003101440080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 196213165 1250 196211915 196211933
    0xe030f10180501050f0403110d0804030c0c0302040f0504060b0d1a040204060b070305072001021b032415010f0207060c020d0f0b07030606021c0302030a021e0301091103070903020d 79
    0x7024105508000801015041014045000350300c0b0380c0c8e03000c11000c110119a0b803900700c00700c030000000d11600c01280209111704040c5000d18003a0508201d0317559241d0004c0d0440300c0c0708409064444c0c50348100002c2c40100e00c180f00300300c041a42c0302422034880369108402070816041d80d92010785083c010400b55120359011781c01520719105020b50310001820050000d4000581c00c0310035962540403c00920117150000d0309429060b0000c010b60044202c011b59140344080480c0e402d132281001410303500101c1412400310b60083c0200100c00e01382403103014030036030714680d5a81c18072241c48403400340d0550000302c050403150785142c4440c001542d44000350142900240207040c4005c4402c00c10140300007400c20034041c4880391030030000555202c81c1689c446811440c800c541450010029030300398040d130011079000440b00b50040c5445020302d418042186e08440e5a018100302200500400c111072040d4215960001c000e1421884d005400903e81045808001d005045880b608420002c07141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 196214415 1250 196213165 196213211
    0xf2403121305042301050a061b1a16030501080601050d0209091f05070206070903031d0a050a0b0c070603060f0909080c01060806100501090e07050a110615010e030f10 73
    0xe100380413609460108800022060031444c402054050001400b0b00d00304010754122181500e50308404144040c0c02d4000002c20582640d00032501c00900c402d0a101140c080d01c11080c05a201c03525180d004001011160305170010341c00c6a0014005000c65581d43e02086a0203904450040160b940c1206550515010340c0040d4000750490441c0e40d45035a064002a00c201c60f95030854401d503035410002c0380c008040303103c007401140070320084108010031f41030000d103800400f03442014000da44201003030450b000c540c400401c0c004081080d1025003030900c060300003081e90340b4043c014a41420000c2081c00414410404083d9a48100c28104000c00d0190303100504e00100030400320b5980c140450303e0b09012101a081509900004545903000350800c40c26500d0b00c4108a9032666060000c0da03243d48500c50360024003242110300032221402300b06261103110070040012003032903600000f500740310fa079811551007500300c6031001c01e58050015403a00c240b02e1000d80031461240a030006031200c1a48 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 196215665 1250 196214415 196214419
    0x10803090d050723091303120b0103090219090506060403150c0c150b03010e010905150c1902011e060509150a05060c0f190b0403080712050f2403121305 67
    0x107002c1381c040802003c130301c0120040d400d982404d581d981c2c003800450086c1913020006c003c11090380c40140e8225599011600500060400081c40d00180d00010914010b031884071004d01c03030348981880401e070b2a0040d80e400c00303810303203070303203080504580c2c8202e200c4840c070b1600200d65644841c0104d40d41d1150046925958105140441c50382000003400301a00700c0c00c1c1194040d6080052440c041c000502c6071560f815000b9016102442121800c05c0491a0240c40c20720100b8041c0b01d03420601c86a074490800510300c940000800094544142c020301c5122000c4181e0246131150070000d54588440745a88440c001c4102803202120b5070010b180d030f003101c1d00720541050380810041e2902d8800a11540d107420b800341202e090b141c41d00101402c1c0c1266a00c01020302a0038408580024000c1c030745135401903081d041c0044105224100c2d2000c075481203a414541030101010b101d1403110802c06034403806000f18814100d481080c000c660360381059189040185000240f5544001403440f54401500740 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 196216915 1250 196215665 196215689
    0xf030c03140c0c0901081b060c070503010203100807060804030c1103011116060b040509120c010f02190806100504060e0d0c080606120f1b031014091203010803090d0507 74
    0x14030b85110b6403044405401c42c09982d4440000c1000000007901d980e280c1e030421050f010f04c2d078418050240c641c1203030107a0740c0d00c0c1c0302d0030f90046403c3e682030000d980302d4a5081e6810184a192088480c81d0543e00e07407141c018440c2030350a110109901001030170f4031541100080785200c5401c00402d005208103a051040e180010030a5603078040900c81e441440c41c0145401c0c07000d405400c04100448100382c41084071035105254404c1e040c0d41c00800b0382074582c480000001c80080070920304d01682c0c030150080f2005081c400881c40b810360031080c030303e4004409407001440d8550417500500b0606c50ad010b490b0038040104d500a21079a9101d96444202d5800745060030919901e088065690809841c424441c0b50203500320407101ca4001251110b00c8402802440380120651b01041e100410b0750005070140a449070010f24440c440c081c02191040e1040d00d00d04a10b065160346080c00d03198400305c0c01d070000c10001042100c800005030341202e10110382d0340314056501d03d041850100f1550100d111602 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 196218165 1250 196216915 196216927
    0x39031507020f0c040b0f0103090201090e010803120a0504030917030403051209010906170402010c031e2c030a080a0c1a01080c04061511030d020f070516030f030c0314 73
    0x160100d0845064901c0310200d41d0f803094601c0c1000283e980301e07550507802500030326000e00350f584250882c0401e0350040c1458580c903601d0300c0c1c0818492034240c0140764281c0c000103500c1003c0d034041c400035070321012100c8100200d05082d58000e04191151154100303241e103104d101c06202c0030a1048400442d03203c0115504003180341082c41e43c80e00121042c03400b00d52050703000a04903000300180f010032070341d4640c0510642e585900640e0728100c1007009404101c1454100220080c6801e030121400301185c880740c17078203400c030344681c40b400c0c0960406031712000c1c080c0020241038600281d1042802e5108565686402d080042284e9014046402810404d548104840143d110f441541d0503500900d041d100703114802801d00c0705545031032003840801100000504001d500c2424928070143c24041540d1401102103070070300690304108400b02c50440e00041110400008001c114841600300c2140b1940780c0c6151502c00c011002900c015061042c0040319404041c810f40701071480b5940c40200315151030f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 196219415 1250 196218165 196218167
    0x51c0509061810020c010f14040507060504080d1b022706040c0f0c060605030d05091809070618080a0b0103060c1805040f020d0f02030939031507 64
    0x21200340c0c0c03194001e000d00740214241c000c00030712064050254000525541a1141200e00254805440c2e00159542c907240486c0f26103031806a51050320000d11644200e0074141000340c00d008255029506110007007008000e1a0000710b894000a0741c20706010014008c2515604840100580002c7d403090702c14400c1580f5400c007840650541c03c0d600d044401e10390310360003800101c42d00000c1c44404280c1c1400040c455074454221462141c2c8030302808101c99035101d01003031904e040d01481c00046030300814002601e0a0403d0300c100c61a01040e40f00e40c0f80d0a08401c515250043e5005000802c00e10041000341c140c450200007000303151040444542072070345d04010008007401e00045a504c0c0c00d100032000424030034420148150103001344042c5007450301080000404000301d000c0c0e120b940070705c40b90a50030031502c10f030750352003c5488000da40d914007411224207040c1024900303546d611108542a0844049680c042800040340c0d030020303180910007001a2400700c568041c640d100c0300001c100000c1d2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 196220665 1250 196219415 196219421
    0x111070b042d0b0601050c0f0c011103040b1e0712030606030b033d1b02010e120301030305030402040e06070f091d041502040b0c0c0306010b0f030412051c 68
    0x6180110703110310260b02500901c07a0100000070300c002c0d0351410039800e42d0201d60f03840c40c815000041410303c180f8280720317007018a062004820402a0704d03040302e00ca000346944c000f2030760404501da12000d186480d00340440c0907502d00401190b07034040c1c204210040c1710840b210080350300c4180c02a09001500f01460801009845180544800281041507034031007401c00103031055840c050701040c040381c0c0c403031003000c40c1c4c41c481c080c8810780450501e18a040c800e0702c3c0c00c1c81900580d00c8040e14001214130b241d980a03080d1481d9040310407603a44000941c004846070002900c3c10f42e030b4949402552a25503000080c0034291801d03001003179020740c0341403020190302300042c1d180854041c0c46a902c115070342d449920349501030002c1200300140c84030008001482804200c195510b2072840141883e803500c019821a40285140e80300561203401e01040c24a400c114450050040001c401e140007107081603c1414080604002c00c41c00c2c056040d00c034500c1c0201e05403451607925203c10041090a1034086002d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 196221915 1250 196220665 196220671
    0x30102070812150406080c040f1d0705030c01020f030d0c0302070206040902070c15090509040f0b09060a0f2a0306080d270806040b1f09020c10050421020111070b 71
    0x741c41c03403291650f060801d8080d60045403500d10142c1103880c2c41c941408058100c03410411211580e41c0820a400000043c1074080741405500415900f810142414078113040350f81110b0565109a066010201d03001049802d0224050404200c02c101c44405038040c4c000c07000001d610680c003060110b103c011640c0640b072124090b101e40324510b640c900c01c2c070320040d16030b4070541c0005900340c805004900300326000e660824460a02000170b803503103480302c0e40c90316421703030b0310020701c0d0000820701000c003441c1d0084505c994030245081003443c00ca401d02801c25402c4d032200404941218109500d9580a075110b0802084d07104140ca183c81c0030030300c00402400d541e01c4a80300d680d604000c1c128410482e07000800c25a10507900a00003915a034507001400c5800510001444103080240c1c40c5800079500c0400007001692409620f0b91f00102c0581d0805402d11441215039103030a00700804581e18010441441200d094064104010340e5012401341103100c4d00a40d40303000000710b9104001d042c100c42c0348 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 196223021 1106 196221915 196221931
    0x8330f040911120601120f03050c07080d02070806090c0f1c0302010209131407050f0906130501030c020703031403100503010e01140601050a080c0306030102070812 72
    0x95403a406001c46402161110340111403c191880b09030580e50310001c0c003010b60603c0b80401d16400001c4c0050400a00f8194000c02c0c0750041048a06054554090344c5075561a0780d030f0075988084221300403006100e00d100002e2070100110394240907001d0b0801800498040b001042501d401d01000342e603102c000111510491042c1c2044400120300c40c0c2c00158940c0b00e040c04200f01c1e800c00c0a401c000c2c550a19a40180308101c1d10300d01036004080341041a2142e84180c2216020301669907055040350b0001400440458007144c003130225842640c0c144504101c600c401c9071900f0182c400200441d4411603103507510020030f0f0185603c440e00700c102d40d00941d40e030740002e82581d08400402c10103964503180305645901d0201c441d07500441c2030030510b281072612030000f440f50030000c008508030f0317a01001107038080c1c1d02901160046504500102e0b22992240b11058403000705850601c = true := by decide +kernel

theorem cover : BRFrame.Cov 196043165 196223021 := by
  have h0 := BRFrame.cov_init 196043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 196043165 ≤ n) (h2 : n < 196223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
