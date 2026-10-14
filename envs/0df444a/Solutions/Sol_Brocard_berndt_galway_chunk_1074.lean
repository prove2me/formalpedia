-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1074
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:07:16.805904+00:00
-- url     : https://prove2.me/submissions/ac1609d7-2df8-43cf-b8f5-d77c21fa002a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 192985611 ≤ n < 193165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 192986861 1250 192985611 192985613
    0x15020c04020703052d0a450b0301030507050d02041503060510090902030c06070302030d05070203030414010b10050d0f061d06060a0203030a02070c0b0d06060905030106080a06111c020304 82
    0x413080c00800040d40c0c144809200e41007446510030191030741c0c40c00d545825000f85160f1030025044030415035065030082105505030140c24600b82441119044000b2602c40c4160703a0100b08c00c2d14002800020140d80104a00b04003d1511001015049000400000c2c41c25401032403848141c40641c4102d61082d00c90341080a03540c800407010004000300c49041c440704036154002034580c1000f400d0310f442094007060079000c3c0b5100f0030541d41c0b031680c0c41000304514248150003a40d0f0f5002110101c41c5180103c10003400004107000e00106002d01030880c1c029a03603c004152901d03080148202003040d40c0303550b191f50540c0759016440c0200b82d040d0703207880104044d404040011341e00a0a01d03016503410041d0b44070140e800002c0f01e0303202c050600e006031201074924001c0c4a40c01542c0c0a6000200049108161900140d04ca04101c9103075445444c4103581d184245401d80381c9901c24448580c0100c40c7c0700c8040340544d00448a40100520030f00d1404080550b00141401d40c1070340c02d501c10b640801004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 192988111 1250 192986861 192986887
    0x5030f151c150b190b07060e100902040b01030c4d16050105070b190c032a0903061508010204030c031109060d080a0908010f0e0613050715020c0402070305 68
    0x140503540c151455840c80b04c3c0c03002c0805000405200e604041000090b16606000d60343e40249070300d035011001d407255270000c01d0544010f840d2142c4103901c52481c2c0103408a496000c2c2c46401c3c000c444903100d400c00c13a40300174460782e1141004020061050f550b002608400b141100009a621007841000e00040c94884103640c6018003000d60701100d020500c1c41809642c0e00a070076101c5599006101414a43e20b508008200c04881c01582d8007060420311181c0b1070a400d82c03c00107450952160300320804d0740005120b100c0c0900d92030310a0215410410500c00302d40303d81c0000c0007003800800ca00c01d01c50b65519805003264003980c0262607181c043c003424420400035000b681840e2004030340f102d50741d0911342d0008480009101005040c1c000020362200701c1400350000100802c2050020454800e10801c02c6015015400b000b882d00d00840380010200c5000c80d40101c1c003150048014400b607400c2480c60f9482e10106418501035108050400a807035071540001d20000f480380d924551101c7c000031185c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 192989361 1250 192988111 192988121
    0x1801050d1b031509060308040e0406020405030d03060e15060910030914030406090e100b09030f0a0b1506180907090b04031a0c07050a03030507180f140105030f151c15 73
    0x203134030401d09060080002c5034080c0242c6095444400c00311105440d1443c00a000348219071285408d4040d642d1800c18040d0943d01450864460040e81c644980c2d0705400c101c030b05081c0070b02041d0701c0b10051005081070300f003400340d8030442c07501802e000a00703820a0301d401000041411b00300b019944005000e00465501c410020300900d0100e0040841e8100702c1c7c1c04800321490380c018181d1031003000c10540e1150386c040180340d83d421070001c00e48224940504140944260441380920780d01c03840041800c46040c01422200c00460040700e0003481000c40c420404e41a401915080810541000108601740c4030790092000794811261364120301d418030300c07c02084400a2182c09071050a100303480c08544041019603055606190001d45961030030810340b43c1e2544155421030b1aa030042007c00c64440d13044a0001b588ca10300f02180324440740360300440711440300f120000c070741c9500b9902050395110201070301040c80a0040c90009410f01c40c850888000c03c0c00c010030b0300c140740701200309400b009040c815 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 192990611 1250 192989361 192989369
    0x3010305070312090e06091905090601090617031c0b0901090207051c0e2b1118061309080403060912080105030c06071410060b0301060e04021801050d1b0315 69
    0x404481c500d007200c09030030001c0c0100b11500511f40a00003641c10304640e507a070b802c001c1e9902006c11203414290b511907075a4009000e800051854400e000c5064081c0800006481c90f50300000d40c505031a181c0e051500350a22902c001c09a40c42c0c1c000c2c5125603407040200f5018102101005813a1800c90402c94030b000010856455a4107a210700c54114036482000040410025181c0310219860004010001f06042a0178000580001c860804100e2b45030f240b0031400c40704603100102c44002e62080003540c0e40070b49000d41e01845a846400310710480750001c00500340191040d5007003d079a5142c000554130b01a60896460b1044008a2030681d00525800d0140805400400a0018890201c2c203940319251014082e55054000d000107101e08011110b9004060340b818820280d540c160742013030350820301400000c280640441c01c01c5080c18800d450954440303641d000101001c2c04010f40e815031106e04c0e145010386d140c3d24080042980a6044540000b10780d900040c8038100a0155502200300c4d08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 192991861 1250 192990611 192990617
    0x7020a1203020d1b0b01060806131a090108060c041701092301140f31030809061f030311030d0518010b030f07090b06221701140703110c010203010305070312 69
    0x4080c007088084841031b0568405c1c1c10301050301d8581d400091000894013035045586801d2a56004c0b24000780550504081025510840300780d0700e03007000782d444500440310854071510600040040342d641803005911014007000024030b02c5010f40303515411155102c0996225443c00c01101b0441c03609201d0b00600d0000161000d030380d0b007000d07800f800030080064102c4e00804000c1d010441c03a9109956070506860a10140c0b0502c02620b180203890700c2021102051180200e000007407900b00441848050034261016403681c0c641550750503902c11098021308002c500c0180080e50b0031034a1481000d0040000c90f00d07000d5520031242c0304030300399102005d003a03019070082e8244582d0003000203900801e41d8081c234000300300e01a026000c2411800f030b040c071f100c05502c0c000c949540e18515803d84a0103035500200404034100350005041e00340c41c0401c001d407040110a80c00155564440d6000380040d1a14000301442c00c040da9094a09980080e0016a140e400621080041000010110f8614542c40c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 192993111 1250 192991861 192991907
    0x60f18070b03010609170a021e0616030905030601140d08090909011d01020702180901090b0703090501050f06130c0311121017070603050604020702040501030b0612071a07020a1203020d 81
    0x201c2e0382525007c41d04070080c007542d040340310b10b508411001c25003034020801605194079400d603940f0301d00c4207441c0c010040c0c01042924101007007508000c220181a81e05010040c0207035540c40041c04001c2180640030340701039005001d1100595118038285d402114407a0001c07401c0c24660890200c000310307484003040240c1c03040000c41c0050b2540d150440c1e00c50b001000c04202962003054007400b4100507100249004204001c10030400d0f09640081d0400b40500c0080106a0311455a15003079981511300d56880346000b0124407004001c2d4209220443d00e901d80800d0344d20030034044e900340c1d4005025400d0009100320800c01070140c1107940a0081c48040c034030011070144681003d80702c0303e00c0d00503031003095207500004a464469804450742d80b40e015104005540e0340341401c1c40d07044801d42d81503105040f00c2105121500d40007030660103480c0441c035104c92085500d502240d01c0c1c0d1102c0001c0f80c11181c2846c6c00140c0e906880c810102c1540a90086e008040034a0802840d007000000340350504d05081e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 192994361 1250 192993111 192993149
    0xa090c030f210906140c011806060b120f060409020a060201021209071508130c12060e060403050405220e0718061406030a0216080a14070203060f18070b03010609 71
    0x180710f903c212000e0381822440c509007903da0325414130600300301c0c160075800d041c25442c080882030b0501e01030f94040c4208100710394075104a0300c454880c400e00c51040804280100f01c41003125a5080d0304020001c0c80000e505a161340424500714090b030040d000346c2d40c04102d181000201d8aa03165220343c212020784070320303402d15124004c4403100d0025542044420f80018008001c0061808203107600000814002980c031098842c241902d030038200c40c154180610418000000100c0d90b0083e60b140d01c0d12401c15042c4000d12400c079040304004071031040b0203210300101403c2c034412a14400c0ea4200070b40100790400003082c0b01040751503c009a03072450244104010006103114030740111007140c0341a23070f82d22680c483c0d00c003a00884e01e49228070000c40c0080800c1054410003400208a203403180107103840c2a0f200740885020307100c2c0c069010340140002803a403404021400780d02482e08503441e541141120416498040b4070f4010420464000005000303440c0c20070042c9000b088000032101040b402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 192995611 1250 192994361 192994367
    0x9010302060d020c1218040606051206040b040207020405040803040302070b03240114130f09060e01030f140604050a050c04231b070c0f08010204030203150a090c030f21 74
    0x107a21801001c66a01260300304d050001489000340c120041050303143c44413042d800c4246001140650340b84202c1c03030b107039002036020301442c199406125003841014142d507800007400003800c0842c07540c651180c4d00f081a100140c3c4e0324451180903502900045c1c0d00d0b4078042c5400b91401c100741d002098480814001c12a6a44901c043d038114031081d101074040c2a0400301c0180d0300880ca03401559201a408280502d5981c1d00040b4581190003200440702015696012074007102d0403406282c00d29112080140081042d0081080b266485030030340426400000d1308250070104140c8084807284c002d40600418031100b0803d141103c0c1c0c04403002c010803c100008500d0103900300e074650045a222400245181c1300c013000f401451a80e00000725030314080c0c0e29105001301a58011045544011000890400c8051080e1815030354068000d14003404d07410907056105e5002071060012540300e524071000544040c01c807200070f40c420b021240c4140a145002202105181c0c3c0555200c2c4000581c80e9009074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 192996861 1250 192995611 192995617
    0x60b0f090f09040b130501140c1206060406090603020c0a06060f061205190c0e101101062306030c041e090c1701060e041b0908250302120a0609030503070306050901030206 75
    0x5001d0070645ea02680920308103024008a40c07402100c8035103e001c019200c1da07400d00408000e003640c408a00e02c0e5880701d04003c2c1c01e008030300407400003d070201c00a01606000303078010500d0300882c03c00c50751070141990703820041d585990404214410301390400c12140c0d4110030f20746030180480070140010b2409030501c0d03210322403a600d01e00c00070741c450f142c46410502400c006c81000b070004e02005003a044d4104003074022071401165264545c80c15000040c4010170300150041d204858514000e9140142c0802803582c0010300300810805081000055081c45400360b091051203000d5000c9010389032250b407008440e0003594000520447c15204040180405020340c151031140c03e050710320b0300b0043d0105000b00100c11042d03001e050b5140c01281610b030082c107003e0441c0c02000854440058121a44140d004509011580151b0350003040c0010b203402c8100850b00002681258480c82080e1515403c1e035003580000d5011034400030611000303640c14092480902015110640654503690101e21b0600c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 192998111 1250 192996861 192996871
    0xa06030b060f030a29030d0905060409200414090609040221120c060f100b030106050a110d080a0f1107080306010e03070e01080709050f0703090303060b0f090f09040b 73
    0x140c1c0000091110200e45c3c0c030062860506114801421451503011110328450384070a40c464410340c014210618031a011190aa07403001c0c0038613003024039080d01039010741242105a0701c6c1c0c4d400f5600c0080d0110500c4050300040031181c15a00c0040825024820200e0003d0500350154454508100144c0c8410703076500319001c5035002c44540d002440d80e255040810407070079171108500c0056104911403001403680e000b5100000000c800b5203c61f075011003106498866605042814801002000d0156016203220b17401400d0452144040d002c080d400c1c851145130386408200a00c00b48042e5480754410604100b0540381d041182d15803a4000c50030600550f0740042c5000d40000c005180d59120300100c4100e07560140441e421035444890301900007209000380061340c0325955000901d17440301d004960103035454268441c55500d82410850103002040d00640c00c0c16118203000804280d65801030a1040074104010781f41d0b11a001080034501c1c000d00020b204442950602c00810200009680c000e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 192999361 1250 192998111 192998137
    0x100f031a010c110613030602040e13020d0308100b0307030f1d0c04020919180b06030f0403050a03110f0403060e07030b060607050c0a0308030402040e0a080d020f040504090f020a06030b06 82
    0xb102102e0000c0c04d64070a812031010107542e070780c0c000401c0007030310b4029005a03180c0c030b210406c040d0749060342c00030014113005000e580103540c0081c19002c240160f044982042e0855400744a890715000500c010380c1c0142c03050400256244d04104a01c2d807980b20b607104a5040450f045260200c00d02500d544081d00e007460f078840c070360000d0104500d5441090328068200320815980f800da981308140080c9490250b9003001080c20b0031910002454070310101d078450101902c040c183e68440d901e0442c0c103900180b55800615940d441e800c8031514107000a48004000034001d69521829407810105403541c8a00c0c9490b2944643c00c01d00c00100384001e01079000300103841c0b00f40c4035000d03424054079103c1046540303500042051000320500c12040002d40c4180d00039281070082000c0c402400e65203401d601c4000d0200041800102c610700c2c02074000b45011102860101d080a464000007001c0766070443c4102e69844201d51410118281410300c2002000d20b41810010803045401080b11807040f0a0f41d4490307 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 193000611 1250 192999361 192999383
    0xa03120e0703050a050c011d03030a030207060902040509011b0206040b01051009170133030201110c04051501020d050c19030c0b10090e01020a120203070e100f031a010c 74
    0x84080d04020392401150008200c54000070310f030604a448680401d400d600280340141d80004080000d4100d582ca510003400840c80c001e10305500302c0003500031510032107429440c1c0c145c0758050303580e0303004244c00b5142540001500300f0714109550500d440c50030540040d9000b1310f0170400410a281290fa0445006940c0741c062401a0b4504640003000c40c0c01c144420304d82d0010b200e005100540c800003000c0b2807543c401c80c0496110100b00d51f0350151031100a8070401c0c92a062005520900c00c0000c400003010881f1140192900090f050340c20440c0c18480840c28400e8110721586d04120103105403055041481c5010b008803c0e554507820100d42400b54011507543c842c0c2050311980c420860340f40c0260003205981800080250f07000b000780702c0c51280c20f0a110b41201030300010f208071040c540b0b458840d003070034207200e55500019400c010540410311440740840156a100c0454154801d0000e40d10203121001384030002d4103e4400542a0f0100350440b102114280d80140d0410100c50b04090b40c248 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 193001861 1250 193000611 193000631
    0x90c0302040b0604150f18080d0e060c0706030b0f04180f170a0c12030b0a06030f061a030a05070815060705011e0b0a0503060408091c020301021602040e0a0312 70
    0x24181c441c0780d00402041e400003020300070841c2d229412040202ca10f540d200003211042880141051f02c0c0d000f6210180c02403284111000d02445030002c0c03004002c3c00040c01c08091500a90500510f45e01100100b0b4076078044043c1c920b000d108030250508225010010b035240100d00020140d14080300400701c501c00849441402800850b00b60607400300c02c4900d03074507030380d00340018090540c500003100c440e080182004000c034002d002c0c0f07000340b0202030700b491106441d1079021005801c4c20303d046107400382e4038030001c2240e07948841c91028850b4074811044ea24104080c000c0101c5000500c031900700030311030080c03107030101c4c41107500e10941008a4026132507080e0741c14924010803000c5e543c841262800c1c5c04200c4001110b400060320001c0c11121090403035030324803e0580303a90b0115401402c18004208448552800401401c1441a59907512400c403480340e0121b07007240e01000c0b01a0910300e0ba01c0b50b034021860940a04041124804040c240d43c8403280d0f00580310840314803d1045198840340224 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 193003111 1250 193001861 193001869
    0x815091207060b011101110d09080409090317010803030421030f05010602160e0f0c0c190b010e0a02121503161502071e030f0c0e0424090c0302040b 65
    0x1104902a440107561040c251800780001e00307a100002c0d02160b0b0b82c0d00702401025042c42105062900280002d240000c084020070040c09104012607215806000115601304503215492a9520070b0300c680008020700301d02c092440d0030590100d0a150b000b0000c000000e00020100306030380407041e42149215600301c0c0d040c2c0103032a55290f4001580d01c2c0500000c0d100e80d0000c0c46081d2103450200010301180c641c045030884010403584008450041c4000c655420794450060880390004016212900c0b032012000340c2c1e0540e000c1c007d64060356041c005100055002c40c965401c2104401d0031403810440040c202e0b031506e4018090300310220010110f2615880c1400501c5110f540c10600c0300800d45c0720580c00340400304c07034400000180b1840714007040c0d0310b0001908000740003c0507080044507156540300001c000c0704160031120065041c47c00644043c21601040c0624403c542e56150846d015400b5107541803a400f0025000d41000d180c4008540e200c141c007402d998042c0c1300405c041820070042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 193004361 1250 193003111 193003123
    0x207060603020409030807030e1b190806150102100e0c0409022b0c05040509120703050d020a1e08010506040302040509030c0a0305181f030e010b0a0b090a0e01081509 73
    0x41c1d00310742011319803c01c144e403000f0018071400c21074600f0019a031010400903580c00c03002680400c0008100f0310312405207403643c0300018551454152070005600c410046040041c141e410000052020001c05940d60b0144100c11034241030050400014414090f41c9565600c546100ea0045684031000820f5413900f4a24140107001c1c1418003040562200f0700300780e040d0092070151025028024049064545406502d00075402000100907400c1c5451003c44c03a0360064400b1000e11100308040b42c0c002d01c0c2800a04040100d41e01c51204020000c0c801030020403045454004000c681401840941d48000549041d20340684000840b6a42c050b03607a8658820240c84011b40d20590905108055121001b081001c9510114100b00c00100050100840c4002c010325251000720f2200101c482c480d17030080340c8210360303a0300106100c4103c0c1c020811103410707600b00e070008010009960b08241003114100c001014840e08036400c07503150541716038490b0740b242c03e17000c000c908240104848000c10404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 193005611 1250 193004361 193004363
    0x90603051806010b04051e090106080c04030c06050307031a091810180c0f12030c0204090c08010e0c010503010305030a050c0a0b0a020306040f151e030602120a050603031c0207060603 80
    0x89501c207586400b58038200d0b070043c1c41030324401c1101103212081c0110b11054500c1c0f01d040500360f204940d00307182d02036407103800040cc1040303010014800003020a14484901005240c81d480c2c0903a20300346010000c0643e00c00c401c0054503443d00c8100c03401c0b241c03201c0f0b80c620303070142d041705c01a10502079070711205081031310b040c00361f403441406d1a0410b003101505110780300d20940714803828128503548101c8005800d030780d8882c00d10468203003440b9402003070040d42d019024a2005100140460665590080100142d00030707211a80d9102c3c100b00b010765007005500e2140c502401c0c10303419580b642e902d69070f07030303103d41c0e001c40040003030102c2c0c07021410400b005a04107080d4070405a08007860103282e014025003007200c150344158103040ca142c01d506107900c1800c2c4480b440300310740351405080c850011200c00c605610315416600d511030000c041380203403019103408501150303183c0f420704150350204180d420240c107140c802e4000300104105400400c0110442c0c041d00f480241e198001414010001c1101703500c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 193006861 1250 193005611 193005613
    0x1f0306080f07050424061b02030d03050f09150105040e0304050307090b090c0708091918020711010207060c1202010b060a02010b0108150a0509060d06090c03050c0409030906030518 79
    0x1101407001c080451504103440e400c3e58108491002c4181000805904204100b0844061382081c031040d4070030002207e04010604044e49920142d80c0803c0c605034401c45400c0c0004d545105101240b82e21071141c0750403200403401010000049030144800800600c0b69034855941d030104031241600c148207840c01004010144c6102980d200b030744802401190b201140f0440050f030000746c904400d40180e40d1101d4100303814600340007150081c0034070861110078034115440c444e0400141191050b4003034101c07402420703000d44c940c0407600e0b02da4041d2561440e040c0c155046210b0038408940d02c00481c0515a4015147ca00310354445c91050f0b006107100c00759260000341c0040e48041064054100c03003031000702aa41d11806686141107903941900007001e241e07000701060410081480c2c42074029411820040808070b0303c000d01d80c0d0f85012100d0b82c031412111034610a90030018000248403061151400b40d40500c1a46425540100280d1141c0100018540c1d1080883e04103145483da40c0812a210300c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 193008111 1250 193006861 193006873
    0x10509060c01090b0108160801050106090b0901110111040f0b07020105030f041407060f020c0103050c0d090201140403050c10020a02090406110705072d0e16121103070e030303061f030608 82
    0x21b07188a84800d00012600250140c000300000c50000c1445a42c1c100c550b241c2c0e550603194140038840c0555404541558104a81040034010000742845003502c0c8820881080e591949070400038010340c070085e440b0094200d814402c450160740c20408481d40503108409542c0240d42d1882c040c5008201c0e103200c49191700c02c6134004180184c01405800c1420210703003c0301c0b2901e28110044003034440440c2c030060708220030300150041141c15009159020310505040d110001d01c02c2006801e034200354030540d82d503881103a4403442e40c104403504c0c00c10038041d44080c24109181d41c010440303040303011b40700900c213942e580e0301c860000c03202000360350180e5405010b90301c4180e69005084c4855041c0003a0541100143d44215842c1a0608940c0100c038a40c590f41d103000c3da00e628640c4641402c41c0c40c0d980a02445000c1181c000d040713841503092046100141580341e08219000500038083c04070313617501030f91041007031000c642d803200c418060302c540fa2410390294640e100011009041154465481341c031400c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 193009361 1250 193008111 193008119
    0x70224070602070c050306090c1005090310020d0c0c0f0b040c0902031e01050a030308160306030c090203091018120e040c030b030606101209020a1215050c09010509060c01090b01 78
    0x107a001441c0090080030b001e031300d691302c40701010b46800b400c0da0104003035441171000030364604102a081c4501c541d142400707820302040c24082403c0c405003025090603580d000404203070f41391311845081c0d107008071850100c02e042c00e15554000100c0c000c4401810301d07440d9500003020003800900c010b014200e424070641d01ca08241c01060241d98030b041442280410007c000f24050070b20060030400c072501079580604a86031005003000d0801d401017003c0805881e4840440401c406411a200504108a0040e5603162021060b0300340102e45043c072500c0f5040803400009030726464070080c04c0d80c0e085146031080400f40c1105965a56400710b9081e08681000300204a09825500450702c1c18010b609649140daa01010000001b044241003408500100e00318400040386070f000038840c51002d401400c84641391441c13014480d810701000c8450420101c201a8480c1c440d024898001c07421a00c0c5600700081c40b400a411802900300f61703030090030085555078607801d094105243c02600113a02e40040c5d40c503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 193010611 1250 193009361 193009373
    0x5150a12170d0b09090f0a08030411060403080a020106060207060f0e030a0b01090b040f0b100f1826010b0102120d0f050114031212070e0102010e011109040b0d0807022407 75
    0x183d104604c0c858602140052417041001c10105603103000c8102402e00c58171a80c3c3e601c0440c2d0806442664825822a200401c603140e0713030014809503000c5c00c10b15440e400c4850009080d95620f4014000b19004000301700007164100c892024131000f542050348112154401003468001d201130b0181549060000019140300c1641c452442a5015503050100003404580b5005a800904c402078024043e818500c5034140720f125071204803240c2c2c0c80c00140c05240c0d84c03020202518240c1044c100788541e0050210031030f429810440102030700da002481704010100001c3d40f0703906205109a51103c0c0010307448410844c030f03030200d00310007074466080141d561181e04404010203000c00e424068491300c2d220124850a00c07040c7d0702075a140107502003440c0d45280b8125482220f00244605540d00c1e0461001c2c9050280074842a015284503813940340c10b5208200016203006d8a40700f4041c0e22030650b10070120340c648046411198043c0d440e41d4401545004a02801019080740890070101054041c10054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 193011861 1250 193010611 193010621
    0x31504050c0c0111030105062d0a2a02010909020a032c0d11070b0a03020702030d080403090510120209030309030f0105010303031103070206070f05041a040905150a12170d 75
    0x80e4a0b4000c120680d0501d0100216200038003900e648035105000031604400b140e582da0504031084002d841a110704440d980c22281c008070740d45400b08602c4144049410002e00404d0304410300910705155100b0300c2d40010741140e5a5000d007220039900040c04005c5240241c000303044c80204d10410b00d1006a070421101301144c041044004140640c1180500e118819498890a2039140c2d01402c402d40c5401103c40c2c42d43e110080702c205058003400b4810140c1c1c1c060081d040403e0300740d12250658a441e26001b0029080c540110341701c0da10031021440001d2f03101500070040006070000684e915460b00010f440d60003950361056040c0715030303107009101c0340d010b402890490748692024441f480c3d80c0d00500e0058041204c2c1000183e21140c00110707a6881107110880c4034000d0309000d4a441c0d21540301c52109004d0144000134100009000c0212000340c1c030806030301122040844800d880361000290001a55105884003022500342c1c030020310001d80c110810060f0f031000b8950b99000050b0f4200b010381 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 193013111 1250 193011861 193011877
    0x1e05040305060a060501140c01111207080106020f0a021c0516301b030b010f0302090603071412010608192310020c12040303020f2104050105031504050c 67
    0xc082d00c030124420580c54015042603c405858040135465041515015500010406034803507480303d100114580300c04000f0903c0d04017000749560207141940000d002c2d0001a40803108551044034000c11118001c64012016a41101c0d2222048101c24544030038002102c0080c009001d2103407103690b01d4a90000f00021502c0c107121510cc14000500e000b01ca0416030b0794014602850401144005074120f0303031102f60382d604035407080403464880e01d4a03010480260011a2980002d210910640c41c2072800660300c40f50480041821030700301410789110300b40341c1c03500500a101740341b11103100c04000c0d08000c01070058030040301e05808482410250440381ca440a490600c1e40d0781d250418440c441c2c01010f15203241301c00502c41160007180000007980030f6440308d890350144807848406e6282800041000f180030342e00074072480101d09091418003035421451183c00100c000b8107200e4107600700c291801c4510900740140ca030f564941ea1100b400d880c100c1010380c403d10b000c08020758007481e07601500d064 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 193014361 1250 193013111 193013113
    0x6030203061e15010203120a1e0f1103130201050306010c0501092301020a021e0c060403110114030f13111801030c0602070506040306110903060a060510090509040f02011e05040305 79
    0x140c643d40700c007062110810b50700381c1c01030700308201014030740d2011400715420024601001a541e5481c1c1104c068800001281142007502d540c100d0012000d14060b000041d01c079501510700d541418188409264560180241444404000602d03035a000700540d604450302b000090091000d14a0170b1782d0000f1489415114640c40044210f28442051003540c0000c1545d8004041903100300800102e800044007158611344a6030401460703945444002c0d10003103210380e089540c5014890005412000d4450b2080b0380403000b802004603400f0000103d6800c89030829205c5501c81c22420200021940085016004841134041654603c480c60506040741d0141a0540800303440b0203080361110024803451703030310072010f00c41072020400d55441480f40c803045a6510f80b07409080000300f07081102c2122011340c42ca07541c0208210701d017004e40f06e00518020341e19120701c031581024001000404042c001808041e44420400304690090001d00901c221887c844810040c5c80e0500504e02e510a020031242 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 193015611 1250 193014361 193014421
    0xb0a121505070503090c041104080304030602040e150102061f0f0b030403080603010e150c0d1107060612020603010b0c0106170a050c0409111318060b040c090501120b040603020306 79
    0x5200380244d9010700c0318500503203801c948040400014110100c402c07022403404110008180d8400c2004000841c07080794007584807407916100d84105013004103800c019400d1528448500e07a40400d62607400b00001c552211135102000c0c580c1e1903104160000c001040c0c2914000c00e000d0b06080203180704903c81e6580f04180d590f503501341800d070303074035204084219840952110441010041c03030075400440301d03407070034189400303220031105407101b075401400120000984e000074000d40d03000b04005001c0c0403a40030440a074560202d0800d100c14413885842040106011103064002e4100740700400c03100002e0250020071101c95601c8003141042121240700f901e101d411b6600706401a0003c0700c3c0c1050042d612425460305008103080c82d000c0045102c1d40da403010091882c0b441e811810390740c0c028040020001d07c0d8800f40800c4807a0042100d0921035188820000b036a40311580301540b912000000c1a008044d2001c01d001d04170a40000f035240c020b480400c10b0320250016150810050300302c070604 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 193016861 1250 193015611 193015621
    0x30114010908062a03010608010f1e06050307020309120615031603060b0d0b0f072601030204021e04180b0a080a021c08070506010e01050a060903060b0a121505 70
    0x5400c0784078441c020080e08034000040c146601004590030010320044c0203803481c03408107540407103603000f40c02100100303040000600c046018900006c0c00380c940071911500303600c0c1c50841d03c0f015890503c108002c101000002074803481c802d106494600b24060080281100702410050710b420702100c00000704001800080d24500e0700150307070002001c04c1c843c0b5240803421500c4410207444850341060300010f071001e086000030144111180b080600d0082007040341441d000080680c42907440c8280302a82c0040000040c0c1100030004d41101d604640c01030390340d450800e45030000d51040c0e80710b074500e407408200004d054000e01d0850602002111040090b810000200407210103540103078011035000c00307a07076001801c00182d151031060300d41082031107580d00307651a0000b03544500800c41e200e0300140c0c0100840c01c0340350740003405840115500355009081460080015809200103041e044d25602008455202c1d078110030090a9110414440c44c1080d051980084140c00e4041c0d4410340f800780015 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 193018111 1250 193016861 193016867
    0x6030b01021b3d0e062506060f0902070506060904050c0d0c0b18040609020708070b09030f0a03140a0605060a0810080a120e01051602091503030a03090c0510140c030409020f03011401 80
    0x281181c01d401b545000380024030315074081400303c000d004668550340c5030000b0444c0f02c0410300300700007000e00ba6000f680e03070203031440c0c0305007072a6018001c94049e07990101400700040c00801d50303d1100605503160525900c5608180c01d14904c40c1d40001024040082d02d404110303a42c4420010100c8240c905010303180ea00c0007008100d200d00207024100b03607000d02410001500c585040307600510001700300ca00701520041d4209265100741c5104000c603642e003840107101110f000781e040e4412640c610401c1114604004540c41d480368002000400c50f14200140600303c1c4903100c08041d186c01c108075005180303a454800d00014602e0503420102e58510100109984190100c8a031314082800130110301d075142d070910000e0800076000c41441d18070706500120a49041020706148030555030080b802c14a1030420b060358032500e801880c002c2c69580000500c842d0070170040c403c600400807009030344140c1c038841d079402c500840c0c00c00c50b103403800040c8480350080841c001d141656608500101c03d2000c4034019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 193019361 1250 193018111 193018117
    0x90f01030507050111030d06180b0a080304060c0f1406061504080705060d0b042c030705060402060a140a0801090c0c05100509010b0603090706030b01021b3d0e06 71
    0x40890b80010340511555115111624955412800b100c2c10841c08180388826640e2070781064075030002105d4041c0c0441054040e441040038290b9030401001d04041c0300c00c1d22445030f03006102c144000300c0300c04400c12140d003031071101c01a080300741860f01d13048030454140c4544040c2c0750b062058888280d901111a4600122403c80711504010041039251606001c20f5410101340503400c0c0c1c1d56200129100d88840c059100581188070842c2c440307800c1201d0f00603803c1040a140301e0107a206102c20000501d00040c09604076404490880e144c1940401c1141c03140321019084d81d1308540810581001130300300c2c10040c1039030b001d14020301500c805250210384685a03c80e002c2c15a40c042c0b04090400e8a865008640015061001044000303c000114445620954800d00d040c0d00110013004026414802c10414107001d01c040d20a200501c4807050002d408110b0540c868200c0020700e4080c2c0c0c51040080080c0c3c1102c03003001003454800a400d0802c000213078030210105440d03c1401c000c41c60303d4421 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 193020611 1250 193019361 193019363
    0x80c06030108150a0e03030f04062417030714030c2103040b0702010f1107060c0203030c0d051e090c030c060a0f0e0a12050604050c01090308070803061518090f0103 72
    0x108242030120000c4085840c002c1d00816010360345c2c85010602400600046200e4084501c500d00541460305d0041c1c200c8a10300707081c1d40070f850010149030240c0c545600c188210780404501d1242514040b01d002d0443c82401401000840240000100e0580100280650301d81010076288404aa1b000c10108413442c2d00000340d07101d40420000e030000b00c4c0c0d40c00841e0410314910002a182086118080403160080141da40398140440d0100400003d8080e660000000381701840c1181400d015040e00c6004202d81d00c1c85164403040001c5203015810044281003006a07004e4243d81050f02105132258045003025029000d0319510003554207107042200e051f00d0b85070b990b0008134040c000c0e044444050441071942c0c0701c0200c12000941d00304079098400c40501500147c811400e291401e94500b401c007007049814080019001c0020450080940304000c4c2c022079065542c0d901c000028411101c0c0e0b80c1810101100414030604160008162080c805410b49880840e600da0740340200492009100c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 193021861 1250 193020611 193020613
    0x60f0108040f0f0204050c04090e281502040902190206160315030206030903030f0708090304090b0301090c090e010b0f09160504030b01060e0907051303121206030606080c06030108 79
    0x1020074009144942c01e2a03207540503c00548810340150300050a4071400d55680f400c151002c10140442d040e5172086428140d08100200002d2400140000c00144841c0341008c42c018400c0c0d00c80c060040c8044c0d159581008050300319519621a50a100250403500492109022044022102500014200703004807207042d8005042c03500326004070301400100d0750440480d00000030001c0113840300c90140d40169506000b4540342d01e0010607441c01c0348001025101082503010500c840305001000320703810754113100380102e0400000000309024041c6140c0040c021048031301d0004d82c044141c0d019140480c40640288030004018081100c0c1140c2d0000040e17110743d09401045420b14100c0706894032029905089052035a640c840806c01c3c00c099000001050b101d500312a280d1030100e2010340c1c0402c9070700b00745040101c0c00300c0c800c40301c110a010023040300101c910408e515a008a14810030007041110a00105072a46080405031400748142c810500c10b6010b04101d80c034021054074140c0388080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 193023111 1250 193021861 193021877
    0xe01060f0203090a0e09030409020408030a020f06010e0c18060c0f061302091f0e0421090305061f26070603020906030a02180d060b0f031209040905030c190308060f01 73
    0x41c61268000b8006042c0c910030f80b004008c005859800740c0003510043c0100801385848079170026010b4140140510800c61039080342005100b2003810812054200b01c110300b19a40b0f0b6000321101e95410785d116600650b22807408034202c07140140001d800c284100703501003582d0703180e00d6000070741c5010381d8450030080d8030642c04000141c6810031030b1028840c03c1054080c8020300c66891310041c03040074041c2c409480310a00c29000c105160f00084100d40504d19502d1f041140c54a1030f16a0307510380c54098114000300e01d0303850340205040e03001c1c601d0748041c21100402d0240c03c0c107202c1114820039940155002d1070300407044000f80b80760013482034600510026011618555525850000a40c0102001c1d2001900c20311081f000361246201070b2459440f558000910b08142c00400c0030020100d800917200794404c248400b10703080f460098031280d940558010540486a02d049800c1d8041d8068000e864443c81001b4000510f01c2140e61403180e00031340360b02e00191215070601181d00312402a0501107002c003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 193024361 1250 193023111 193023119
    0x2e03020316030e010b06040b0c0d08061503060a0e0a06091104050102070324090803010e06150406030903050712050415090806130f050d05030a0b0901140108040804090203010e01060f0203090a 84
    0x80d0f08414840340c0200d000107840d0f20300d400001c0540d00309070420500d904000c1450054102c1c104503a130402c00f0541002001841c040000940d941854213100c0607107007010010448a0303c91a04210282c1090017140425140c40c5000b01d004013600e00c65460443c0c242078244419514a508030f900740c0314180d018142d503508507240c0c80300000c03200c0d1441014030054981d60010702190b100e9171000b1031040001594030752504c4481034010302e001e440c1c0c0380300e0248a482c40c1281d20001c07080b10115002d5090200d07030b20300c0c0c0b4107081c0e515028488011b812465800e03205c0301007030340c040300a005803203038020419910b287d0600d049813200c40c14002d014950340310304081100402002006a0307918420071400690034110f03500c15060200c6070f03c01c0d501040f804001d101c008043d500450071040010361311002950b16013400c3d00051800580315030f06011101c0c0100e001c1c4074132001141c0103031110600641d81e0f075030b403010446009d080900c10ba4000403034407038000390114404000c40e1400c0d40001c0c11074040c9420 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 193025611 1250 193024361 193024367
    0x80309100e060a032003150112052e08060c070303060f08070b160515040b06040b06090f0d080a0f080f041a06010203042102041d12030c092e03020316 66
    0x3103c2d075030b244a20180399171070301e0b2480310342c002d601c90240c0314008221109480005440d00c590510400340a03405c1c0000c004d840400007030b485504000702030020341030030741000d083d02001080d6040b804a5001d26400c20203400c5000000f01841446580c08104080d5141d000515030030703240c000c41216800130801003211000200241009018031084440380102c0f56071820b01c0c100c40004290601940c29040100b401403c2088a9010500340c50034861a086040018468819402803500c5800508940681a10340340304410f54240d012207403a41d036642000c0e000d400c440000e4680000075180340c1c001664201080081c0c2c3c002c030740c04001c2095a24400c02c210b010510002e000504612007400300050065034800350004410b02c4503450780404682c0d00604c41618000c11800390070780d14560440c0150070000401c07511203401c8108043d16a01c03081403001152240b1000d10f644400780c00651039081000000d80c80020208002469008413804420781c142e0100701d40392403844d803082d05019041d0b40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 193026861 1250 193025611 193025621
    0x80625050d06050d1202060702031e13090504080301210b040b0403020a021908070909080a080a090f1a070309330203010e07020d0507020319060b0307080309100e060a03 74
    0x8260700101e041a11100416188008081c0c155850780c0c3d00c03403070b42000c03d4062003219000b80052000d9132a040400c10904a00511180313a0045004000386501e101d2550074004005030105080a01c20f504050030301660b1034000703001d086028000ca04003401901c006c1005249440d0303100d04c084446588607103503d001d00000800540c19030041d85101e6005940c1c1c0900070304c46056003191614841d0808104503e030a03066000320700d10903d41241180442d54103415a04298840d150455055a45020714005071401c201c00901682c4400d001504224481c0860600610203241e201015074a5501c2241914038008014203027807050507007440010510744085001c2d882c40081244401d411018507022640241c1c00031008106c000c0c18810301c20340c103010b00d9514107014905070b401c2100303c1e00007907201c910310381040f5101045501100700704542d603089504000401000e503030220b03599a030050b13101d03800004482d10400d603c2c0701c1c00c007034039000b0340442140040140c1031074103168021209400a003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 193028111 1250 193026861 193026877
    0xd06020c0a050a120306061b11012303010302090a1e0b12191e030905040225050c0109050d110f060412030c050d050c0d0e19030c08062505 61
    0x1001c0c41a150020400410096400380e00c030304091205407090220040445d030141d04480f040100044114101c0020391340c801c5091500070340f100718404003040058030300c4110114600d000d40c1c42c0007484182080f0341805181280e000380d600f03080581c2e82c04040d10458408024514154100b0075808000102540c0146c02c40d410281c4842c1412208a004d90b2528445100301031007075070220255030402c0300c584c1c0317081c110000a140480d4403c0707050742c01030858031050050a004a40c01b20758008000701040780201400441c607642c0302e0812507401c0043d22100a0385550b40030030110a00020746003070103d13074100455040300120720041251810048544104506954005820301012444442001c3c0e00208203219803107080440180d031501508142e003840d82001401400d1081d05200c15001c1100780030745c15075140c1005a030020600180c03008002440c0c0480865070790034003100300a007401450003512111811540165250303c0043d0708240403100c81d110010b8403c8681c041c00d03000710f001d41611 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 193029361 1250 193028111 193028113
    0x1206080316030e061b0d030203061804030e120f2a010518090f01030b061c140f071701062103122909071d061803010c0f0206010608060d06020c 63
    0x1c0301c00fa0001000fa800200c0d4030003c5984180d22602807000030410300d02e0f603004a09055007545406000070f41240c00c0b400d20519103402400004003018413580c0c0f9240a10402031030b010482490724409641c03000261002c070b1003407054070321540404620702c540e442100100ea00d08402d1511010044940741c200781410030070003400c0303000c111242d696a510a40b1130201d4810002d01380d89541403c5a0000001e405c45014000d841841c0300e07044a405420300416030000641011031040010300307440c10009040380e03501d40c00f40c40f10103d00408210700c0e2a601d884208020311805803209500381a00028640c1400b400010729443d00000307000d084600b0089002d10400107040000108030802400b03c00402200305850890f00c0a043c035111103140d801c029149031031240720240d240205290f40004031464418032010505289004c410029031050540140090042d461150005041514440028405400b4080000c68a10300c030319650b42c4110740041100110b110700303840d441d000f58000e884d80001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 193030611 1250 193029361 193029377
    0xe06040302040606030915020909040b1306090c05030c0105040e1605071a0709080c010906050d0207061107020a170a060f02121e1026010e060a050403120608031603 72
    0x580d803a4803e61000300400c0d140491380032001d1034080c00c110520b42411805900c184592200f42d2200d4000650080c3d021401c082c19484003a80c0c0000500003502c014500c60424014204018003000d15404841c1d05904071140d000d5050010340c0d45000b68000d0790015040840041d00e010b072911134a0b010800603051861501141c1d840715070b0f50b40b080d02c06c080788070030411091010269011680e003008155200207080640c480c0d100003840100c01c3d02c294010004003084204940f40f1640c11500c209a00400c00c1080143d849205981070300103030b0083c0d00c24004018005040d240303031007181c03200768907485c050055a0110384c1c0310002032000c003076000200e070390a10074103152840c90782d4000d00a45500030051204124440c1c115508070004100000380345800030100070510b014000c1c0340e00d81e40604a100710001810441c28010706403d500b074500b9205d0713042030000c10320085e480fa031b00841c020303a40c00d040210721500031400e83e031884c030035254250300402c903030845a803007103901c144060310a00d00f0400c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 193031861 1250 193030611 193030613
    0x11e0b011103030a0204060905150706110f04170f01021312050102191107050a0510030e120f0a0e0108040308040602071a180c03061b0f0d0c08040204140f070e060403 73
    0x481c5400031a5240302c04c2c0e60005050290a80146013800204000c07200d0f84c20801e24182c1003c918081c00324005c200070384848100e04415024010785080703080407581607031900c3c1da60103840d80d207600302c1c04480d041b4021580b144400da14180200c440802c40c041d0700a800624020b0181c405001030b00c0187c4207554240840c001e45030380c100341e41caa9034000d692601d4640d010407901078181205070344000d11a10311980104500d40700d80224170808500c0b801c000400c00d0b0640c2d881810100c41d40c0d142c29020b0000a0000941301200d0003070001c01405590700c0c03c4051180f40190307140c1e03400b61009000308103031a002030300084051700108081032007042d2040d85400031400e030101981050b100d461243c0341008000c200c50208002d80b80c542d14044005004c1d13402c040c458004020b2140101070240d000000f480300312030001004940c0030342140300c0308000d034030602400200301c48401d44049201d1070615010091003405051410b00880650100c2006500d4880c41039a80c070f1031040c015608108203100c004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 193033111 1250 193031861 193031863
    0x90501020301090b010e0d150902060906040303080106120204030506010b0708090d05030904111810110601030b011401050913201201031b0602030904090804050603100302030d02011e0b0111 83
    0x18003c0200762000316a0801100000d44024035582810b800b540304805c1c03003c0403800ca103140c040da800c1065400503a046803400410098459510b80790b40101c00028000201a8804041d5049400340e5980030044d4800712080016803140340700c0509554400d8005110b0281c1580c014100c0c14412040d4a1600705c8802c08039105c008100d1080da55500086a80e04450605024081c0c0c14000e00014600d410b4040d540160f01c2400520481cbc021a4a5000c65443c10300074004080c4030300004084030b06139a524544003e28007804d02452258029400c00b460b0b4950164064607401c44006040702d400c060b0007006c110040180c1c004544266807003650003260015424000d0119447c07514050681e50f056050a03403000d005204030a203081c4680c0c40411000341d000c02034400041c002c0b240031400c11800e04021000340195044030f988520000240071302c4c3c0da002910181120710a07002d95100d003120150503400c9580441180d84185004e0000a00700c05982d4020f80c40d160050410a1280c00e40084617 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 193034361 1250 193033111 193033117
    0xc1303061104030203010f0c140c070b070516180c030209010503150402040b0403230a02030a1b0e07020109030f03270807080307230415030f0905030c010b04240b0307020109050102 79
    0x1c40c103200e03034408c10031810725840303124051001d4086140902c4c00444415641d600c0da054843c185c02680045882000c2210034410b440c540989201f070b100c42952150110304802e43d182011521071440c151084103228064000d9a2911205865050a664850f2558000d2900710f40566034803a80c01c00020501149000141010b103024101c0740540340c00a8032241949070510f0007203003140e40852010b10040c1d9000802c9402c1640c400450341680c0200d51450309481d01a801c42c4001490304001c10600d01c1d4154440250b0340d0080e42d0382c80c0d481d0345004054040720202c3c81250504082070040359941600074100340307800740c80b4440c0c080c0351201f030b612000306640050321860009907549545031100c0207034006107403a590800070039914180c5004040d026600070342c03568405240d21a92800e40139441c0c2e0340300303101254005083da40e0355514080340d6030080841d003800c81d1056241a90f0f21110842c2d5020090b441488202c80c0c26106083c4071140520303406c01449801159282c2e61541d001910078005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 193035611 1250 193034361 193034381
    0x140d080a020c0111030f09121903120c11190215041205150903070308041109040b090114010305030f130f0b0a0f0c020d0b06060904050115080c130306110403020301 72
    0x2d000d00e80c0d400000186090142415010507900500820011101e900100ca40c0003908686d08411003810000c614240b0040c1c0d400d4140000504a003d01815088141009400c14a050400c02c40b0480d0304190382c1800b1020241c6110303802406042c058444103c1e07980c83c558001040841100c04d1107551030110b6206030000c44083c07600d000380317100f00081048100c0c0031300f007800c50114107032810342c0641e90b907406011005420030003603001240902004000c41c008840c40500351645070700c0c040c10110f54100c0152146480e5601e4000040c10f4560f0700b0740740c9411380340c0c000050361030f120303840120000d03e0b00070560b2842c034024400c0c000601079041802c810010804002e42c0340c0c840880c414040c111050141c3c0c48400c3c089000c13111401a9140700030b1002040c2d00403d03400030340c0c6407000820a58001c005007a030708a403038880045a038400003e8000703903038903a941e2186056981c010b22031100c0d00a0a0300750411440c007402c1840018015004480c0f0800008609400d2a58980000c0c3c250b13880014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 193036861 1250 193035611 193035613
    0x190204030605180115060503040b100923011e0504050c0c1606020d0e0609090705090d0510050610020a03030b060904060308091305060d0f020409211b0804140d080a02 73
    0x82908011503085c002c0304000e840c400400a070f55440d29002810a22008000519440d440c100050400c00304118074400380080300010000303190710207000d9040c0f1000c000d01d010220354007000007039540d00d0002d80d001200f4040e0640c20825182c0018031010780406041121032590a00107099024001c000c080500200b10000ba110b583c035141c0085e08042d03d8180d61020803da965842c04951101d13402c460144005a42c12040765444074012030351405002e0b2040da202608001c00700621500141241400c0f0700c0d01da0070083c81c0c48900408c600c009003002590090381000f0382031408280264000c203080d050280c441c80c58814008002011515503810440d840e04000c00c1550a40c05c00f075100cad01280302001000c0040d8245480020000d042e01c0200074502000c281d00c540454403543c00210500c1d61141200100910080d2000102c0003602d01d00b80019034540032100c044024003010a07040744e0481001881d05041030081400c0d05c1030310344e00c25080805903110b9000508484000e00380d00d0410f40c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 193038111 1250 193036861 193036891
    0x1706030a1e0308090c01050a0e0a0807060c050c0414060607050a0c0312020d080103030509042c060f0702030702010c03030507021e06060f01030b0604050405100801020a02240708190204030605 84
    0x440c01801d10f01c0050240403856015844070542ca0340c02c542180e0740f40384581400181580480009018110f550f080203000b4040c584000909075000840050214460701c25120b0704001d071803d2004441d0382c0407007a514509104082045801c002c40241001030041060701c680080b60340700c5180385501d030340c400c890030401e00301081c0d07403507505008440003c8001d1900c0e9070a549075446c028007078069401e0f0305100e85d590700500d400104800182240c40e207590740d0f24030410040745403015101c43c1e0454010398140903c20004060030310100c01c03100d001c3e90503158007202c06010744040f002498000d0844080d880740e800c1000c40c502c0030101514a94a60f40024455490a0018861540c40107080c0074181410005901c88958072001a50240c031010340f40044c041c0c3e01c050800c00381c44450341c841c0070603500c00120444040d6000c14288211441000088020014031101e4507451904403100d20008090b41e02144403405058600407c5440d280805801d0644944070101103070303415144644506251 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 193039361 1250 193038111 193038113
    0x1050607151b090602161a0903100207030e03030f030c07020d02031609060b0405030604170f040e041e1203051f12050d020304180b042d0501080304061706030a1e 71
    0x441200c80184c100b52014005c80314000350f401c1e61014076030284038501c0041c500414106050003041da0b8000c0c400034126000d404880c03d40100961100d001070780041d07548240e81c171440c2000400c40e5125400041c94074503540d20032111344c41350307005804202d901512a0040102587e4200100b480710b41c444100176a20610702005e800844080380d01044c080841404100701d00c0d43d000c95107a41c403a0b04491484003100c058034107560079100f45115041c1a10700402c3c007182480003052180c2c451486882078040c440d5505031100d0030300504000052084981250400f4440d1090704019080503244940704008509294240c4003004207400142c585040d80c800d080510108020710030301002d290000d5481c0c2401c1445c001c603002005002207641584800504041b1b072200d611461864101c104080300484085d4000e00085e48442c0c409c400480c01c0000124024401101325402c0b1505a1200a2400746007400201a20f03c000c050950600541065030081140c54038054101281c003c8048040c01e45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 193040611 1250 193039361 193039367
    0xa0506100306061202090d0209100e07020727151502060606160f080c07030b07020d18051903080a0c050d0804050a080d091a06040605010507020901050607151b 70
    0x42440c03000305824184100620b98000481588034803084501582d542000004103400003e45903000f5088000602084000c02d9503070401c1043e41d408842204550315002c0c0c00303e9884c0781034080d0700540c2c0368245001c00c0384480d01942080c24148424003044480c511003802021444a0303106540010f0110314800030b090b414010b09a002d40111016410040c12200c6003841c044400001001d42071685010310910040b2000e1f2017595141c1411580441d85910f0507200100c07058580c00c1c054440c1440d503194007030040d4141340c7e22602058403103080ca40317002c04001d06404800d0680d000c14402c2000440404c024400030141d10360552201500b807002442e00900d0306c00c0c14079800c41000384001c00d100c006400816610341e00358010700c015448618088d1554014174990100500c030504154500f501d64034200381d024032805013214200000f6a5807401507405100f80400254050301c07080040c0420314010003d0400b0078040c07030004101c0448050180b0840d021821240c213501d40c1202d10580d5a58 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 193041861 1250 193040611 193040629
    0x1090503160902031e070207030c1d04060b1306080a0c0501050304120507210201090201020c120304051201090b19060909020306060108060316030305031609060206070e06120a0506 79
    0x20380c020311180c46181841001c0d441140541c07440260000042800c02008143c181010485400441d844e802c18501c01781d030301e40f864030040740c03118103110000034a03d01e4102c4c80054410218044071056aa60340c2d00d0300144070283c09168084036000507115040c00c0d0380b1a00d406810103400420307842c405820407000305c41a641c4030300c0c1001820000c010001c3c44444107034400c0146420910340b54007036468100301342c000d40e1490061a6921090f003200071a415048850018000e0302075a50440b804410f201c0620f0410803201c6240d4410801005117003400c086101203802240000220581d440d03035a80d0342c00300e0650f0380d9417108000f43c418885019091251400070034541c1d40401030008541d012075124000109458140070391700e000941e55480c10721185400030800c0c80c8007080d00d610f902d4040c0003a00f05913145541c4c00295425400c81900841e2082d00365907440d001098aa51596400c50780e1408a07024a500004280040d450094076a81080d00441043c2030118182c40c24909110002c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 193043111 1250 193041861 193041869
    0xf1e0803041b030804091a090903031806070c1106040b1c0507170408030711030307030609050f01050109210c090515030a02060405010c020a031203020a180501050f07031e030b0109 79
    0x40ba8028040001400e0300e002c5a007120320f5910045410030717124000784425407540078010341040150040104242c07000c80150700c40e94011039000c485000301400039594040072600540411007490304100810902c05100c82c42440c000c00c540e240030707210340d050111034001e10b00506000c4180c1c50040d1002c2518002d2650102240c60322016a1808610640c076810000d00003914405000002c605264891208090340e090906c088954030b040946004004046901c04c4c0707424a4542000728488441259070103040302c42c16135a420b040b0741030003070040400224070412400c1c0f50301620f80030000b0340c80b014014000d02d420780c40007405151000700e0f0010401c244000a10075000140308000580e5900140c4090b02c41c20b28000d680f0041c0c0c0d10103d903540800790030250803a40c0d130295107000a64103800911028201c0d079034a411041c0a0440312600401b00e00519011443c1400071408140014002c1e09585010741342291440e459840b100b0200c0d608007861200182d00d03080000c00b19604001030500074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 193044361 1250 193043111 193043153
    0xc06010305150603060703020313050a0c2d060e0d1401150b0a0f0503090a060f05061f020615010512070c020103150605030a0c020a020a0b0301080105150d0f1e080304 73
    0x6450070314001390b120714008004409069020020404800c180f964000c8030540c460111403030000b503820031030780c414560700c0350101500c089000d100304a0101841007900c1240f60070305001070381c1030100c2a222a20b04146640c1c00440c5951060081b0f04280c2240b41c16103d4040001411080d40d001c0c406000c42c1600b000d000402c040011030050342c0d2046600081e08014517029460761990111503080220022002c2e15050410801e10354400584e4860343c014101107039510039042e1003040307901303283d002c040c03048003d40c01005c00103a00c520038920048012605240c41403502c00365414603000102d0a8a1300e00c00108860102030440d6010b1040c0b024030806d400e00c200140307103807402c0100700d84002031081600949441c0e400488038020004036101070380c0102800c0d03149890700b040b03804c1e5070401d100350b041a600380004121615404000200c035180080c05400800c002a02c0701c2600308192481101c00200c0c8620100c4204400d0a00018261203102d025a9070b060908088405841c2841d6803101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 193045611 1250 193044361 193044403
    0x9060405070f0804050313031b0f1a0322050a06050604051311060f0a02030304151406060c070f060c02131506120b090406140a0908040506090d080c06010305 69
    0x1205400c85408142d10034645001601039460703191440c1075000d10507540529500c05a8041b0801000351080d1640ea100c0c0020800e16030796801c05412900c005200f0200d4041016444600c51000c3c8001540d1017040309020310200402c4011280440300360160544198010404400800403d8000c40d500700c0001c6a05008508115940303088011080030000c110034024010220b040c0c96000030358420902d402801e075140c44030040083d44940c01198200e8803030b0400703004902c1d030308124410a001a214600841880d030343c0c01c1c0900000d9400f1002801043c0b28a42d0005400c2100307214003000f401841d61940450992841400504040a118200c3c060f0802000390b8404817200c03c010122121403403d805003a2681c03a0300002804a0040d03141c21000c4c02c0204014040c0d1500b140c41c2d01840e1044c201c5a41c0d0710806c1403c103c590074840180b82107000c001c2003010f480c100e40a0700f0205401001d44040c0c2d9495512020346501401e402c0325140c01c00401081030007414403560010780c61480d1f000325 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 193046861 1250 193045611 193045621
    0xf0c020a15121e0b01140d0c090801050c0a2105010605041e03050a02090705040e040503031602010e07090e070909062f07030315030b0f0f06030a1109040204090213060509060405 78
    0x40c1020308403d202c501e241e03440c00e0240080e0310503c18a507000e0b0f0340c4502c096507407581c1040c078000b03031003c0710781d9074041100c42c040018407610500c40d192182c2c052050307542c1030030141070301160b0f9000304c2c6001e201ca1407007030384071811500001c0c41824000c0400d40c4549035564074050101483c0c401c3d40001d1480380050100400c0440d030041028060b8030386c103d50000242d962105c06440ca4041d075006885c54940c0d0104010030044000015406500c8410440c6121465640c04900303885150003500b1598104100400c510304264120014004507641690701c1261107184050172240602000d03500715480f12190310707190007580c8034a510007004081104400104001c2e034043c900c5070540003002c041d0b44148008120072140f0903900a147d1005450700c0604001d850300110450564881901759070380d40105d0304038500010094080d5038070020800c0e420410700200001482e00074016070b082500c444c910b0740180e07508031541c040c54808071030008456080405101842c800101107900440c5801c1c1840 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 193048111 1250 193046861 193046891
    0x60803070b0f06040905060903030702150112030f03060b12010f0506040303080c07020307030f11030d0e0d0b04060b04020c0f1b0d0615030813030203010b0604060f0f0c020a1512 78
    0x1682c0071195090003140b5031101c0e00810700030301c912400074015004a000388590008044006d41c0902e40310350864110b1038041203c0003200301c085c450180c8104c0c0c0c072100c0e0130010f401035040500c60003181c00d0001d4119030700d00e103003080380d400484a20030550040005100d01c2d40c0394a44103028001c190384c028103240c296075025080d501c0c00f0b0f01d00040d85a011410b90300f190713000c112810180d03900c6000800790310014a800c07500d241c10011a64400d0084c540c881c1c28981c403e00d01085070220041c42403403054100d41b40c0e00d0310714002034000e60750b680c0c4918003080c09403180d0000704000c0b500d81c2d000700354050314044810704000c074010728015880300c08049182c840d40c1e440b103801d69241e00403c0c0010507a0741e140c184804451190300041a01602103110010500c000f11480101c900a40090101e980b007036082044500c164051000070852145048075011321422168021250600b841c2000300d0359500003a1080150703a005d02486110300c0f0340088003d81c020842c14191a10150030700c1080007010302c032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 193049361 1250 193048111 193048133
    0xc030f071d04170d060b0d060e15060405040903030f0e06010f0e190c030f0c050c1006150804021c1b05060a120c05071e0201020105090d05030112020a052206080307 72
    0x50340f1034040468120103600381c55100c040240380ca211103690b1007a03010a2034000d4402485030202004c18440012000510310150340c4041500800807442e00341090200300c02411034075001d90815590302003a00201c0d01d01d03c034071681044d10500034171156141441c6c070a0007403080d0700003501c051a018103000b1404d40c01e4044e0212441e0004002c03030104580740085000345900b0b40030550071801d0540300700085800400034400101724000b070300c01c01d24520114209460741d5201d0309070b018403c214480360702c40c8984015034010744010060181c541449101c04040d846112060b03c030740e60800a0160281e0200b058103004100503500c0d9420300d440304001600300c61488000030301194030b94446c00c10300307071041e41103440c42644646100d8a0103065000031020814024007207001d0761800c80800c002940004a140a03c1150341d261443d5a003440c50410a554074600200c4e00041c4c000c1020406549a01011503000c0005c224800f16940c1600b00d03034103441d020750280300ca90b0001c11250005c030350142c641d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 193050611 1250 193049361 193049393
    0x50d0f090e07030905011a120102090d020f040608030304060218010903021c06020d180b060402040320040f1409070b091513150906031406090a050403020c030f071d04 73
    0x50751042e80e1603a030240e0103050016001032055103009006246d1071300c1200007000364201514940121881807507658200d11401035074503800300c0710000c14401490000d010035881c00000d0404203070075556144480c50354100f0340c0c0c200d41803074022034012440c1139800080e104034682403802070001841c580200d0000e400ca0146104400f12011071441070065076011030f0710441503070b401040f5518445070380da8802c840031102280d0341d18541d0082100da1410f4000d903400c1c0d84d00110281d242c043d810012000800c0704c0c164217500306e6140c0300c0044200d001849100262001c1c0022510b00703182200780a401e04007aa08444000c110504c10b108007603c0324034100d8080703060943345550311502e80d503088036001510390002c110040082c0512501590107101c6070225849900e0521454056208444031503408a640c6500410500001262401140c00141c2c0007800790050f41c2c2030781a0030340440c1c203200035012066219030017804200082c2c242d0201c1035040000321400301d10182401d80d28a020400d500c15 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 193051861 1250 193050611 193050629
    0xc020d050c09090c090a0b030c01110708030714241602010b15041818020d06020702130204050a0b121305070801090b1014030705040218150304050d0f09 67
    0x40030490108868035103040300500d92070007032815611056a0f00080341c001402802c5860115864207018000c00130f42000044c06401012044401140d10518000c0da0100b0780c4541f440002d540c07142440203251681c0941c0c07409810f8002c0114062420303442c0344007100483c0f14801880e5100758140c68080d084401032071520040340c01d00e041203000d4054030126690000c01e6009208091001400400031204e0149040d400d18045141100803a8800040c1405c40c02521014200515103a0050050148180001810585290081094184045401c00329158005014801ca2038861020320003059200d2000c2c0c13801ca000c1d50b00c080030a90103040703030846107840d0742c1e036804000c1706104903805401c1c442c0082089907501e0600180301c65040e2000c18028a07104408114407480d50104c4551480140042110300d1820040c400203500205410384015100d800c00c17115503403458a50740c0025981991207440b4101410400c3c10800000a24400e1014001503100c415410003d0501190b00c0e6807 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 193053111 1250 193051861 193051879
    0x3030e060c030c0604020901060f0804080d060b03190e070f0b0703110a03080f070e031f020d14190b1305090a0212010507020f0d02100b060702040903120b0901060c02 73
    0x6000c14554081e40049118600010800550307996001512601c214001c0301c00d40200c3e40c0e110800c2d80c40314406001840007402c07520000e004a51010014110b1039004080000c18035542c006817580307030304240e03426401e186404010524912481c02109000d10001000e0201c007883c001401051000c80d00c02c001c1ea0400100d089010700d400740c0d02e5064201d01f20800c0d2407a07800d071481e0042426004880114031408420080f42d4410322540c4000110b9201400a281c07510540301e007072440b1001c0c441c2160100317400304100f0901418074042c0101554032a0504a610306103e6258400b410f081c48810340c1c1c0c039242c003610104a0b500c4158071840d01010000c002526286c0c0c8214500f00307050303000b02a40040c411400d280c018201540920701c030340c0e91907003910038035018102942c3d01e0b44901c4901000582c012620300c003044800e94403078950302c1300007481c0c0d174070f4818194045070560b400450281c0118080c02c0350041011207601a40f203269404a9a0b00440d606010b00604180c82200000c0d006100403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 193054361 1250 193053111 193053137
    0xa090522080f1201030c09060b0f070c050a1502010b0603040210050a050f19170405072106050108011515020703110112051005010f02030408061803070b0c1812070303 73
    0x54401c48030040c08522050f5600c92428220003d900d10a100884914505420003e0321001d58030628054405481000307180550f040c8008604e90010101507400d00d400030800145980e8480c1c0500040c1651100c12511022410003e421241000081402584100304110060f62200d443c208207a2003420515203880c8030b800201c3c3d071401083c0d0000007131100040d00c64900c2243d070910900d104c21550f190b16003c800404402c0c9584030654004040b07912486041c049810740008100b141520103448103c2c040356912800b0580350280c1c84020b460755150118180204000d6034440074190042c560700560301d0400b00250b0300d00152101910b5281a034030300c8402e82e84105c1c1004030080202d4404e2005061081134207001c41da062058601045070401e50310a294008403d07501150014009040303e561103292014000d00100c13100c280a0004000301c40014a0741c482c201e00404000300d90316150211b07001000f4802407070b201c003d40304070400146080907410001d00d00080d40d90501e0b06460071070034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 193055611 1250 193054361 193054373
    0x3150807062d020304170120030a0b1f0e0109060c0602030a0f02070c0f0501090806010b0918130c090e0316030e060d20160f0f12020c0a090522 63
    0x1194403064622610900b003102c903564004042e10643d044100301c0e2031400c00c4d404101d8201d902c0e410307000400c00301320003040d01440d009070041e40d40000800808a5030351081030014480c200303e0341d42030155070020315000d0f10242e48603460b902c00a00a0030b025070740780d003800b0010300304e844048001855243c00000141d6602181e4010701a52070318110252345a0400d4605440d280c0340d5401000c48043c41c0c600002202d41c401c481940403200301c10003074880e42c0d003403100c0c00400740c2c42010403a8218030b01d840600d19181c451901184680012006a20f9540d01e81c545617505c03003e650b00180d0818240300d22510010408022280c8000062104059290951500769030882c420340308550f01c0500403c140411300003980180c920222801e40d0700741c026031618243c03500c6004501f140d0004e601680f030000c001840760b41d010682d00340111800941440c0070303034883c103001625851420042c2c0041440c04000c0c1031107100180941901001800303589410070004515a00a194040c115090211400113201c1c0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 193056861 1250 193055611 193055657
    0x80a0f1a0106050a0e040510210b1003050d0e2b050d121811090c0408100212090c24130e04050f031804050405010b03010e0606010315080706 62
    0x48155006441d40e55001d000e81181c104031000700115001c00807800551500e4806d40e4403500c4600c0041480600b02000452180d40003150821404501007030300d0041461803050034410711240e10000c1800341540342041c186034030321002505010320031a80c2c41c07081d0340387c0d10504c000308034089440e0680b00481c42c04005a1981a0010f002805601448000c8560214441c208080080001e1100c0d000b680da8040704546283c0c1c1c080c14045100300c1c03521540ca0180c00094000e000040c0c0981840e03160160b05041400d034082038056282e001510748142000004030310351040c540405410420035800101c0c100d0103000351315012884c529007940360100d00344826a030a442c0b40a000f2549103440389201e1060020598041c1c3d40d500ca008083c18002d50700008803400392411911907554104802d06000c041c00300600116115500d40305108203a440900c16101e520307190600821182c1484400581254003900701d02039010b403002c0c02800207210018014084403990710b0082000d040400d13400391246 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 193058111 1250 193056861 193056893
    0x3030a0209120a0c1401032a0f02070e0103080307050403050f030301060e01110706110109050303090706081018050c0705010203130b01091503020607080903070b120f160f0909151509080a0f 83
    0x9854045202c001d808c1c052640141c064036080c80e500c641050580c0c0e943d08a00c02d6481d184c040300c0c018000151100003942e041041402c01a05180c1c070395580d142440c1c00c0c1d1812101c10f620200042049980c0807000440030002800c006003000c190700d000649912007030159505200030b03078035000c0d4042400d5000d4802a500310003a25142d0800d001c04d19103072801d40c883d810000d100440030854220300c1481c40011141800c000040da031345104c4000001d414010086441481c0500401c1c0100b40280002c61141c15008211007a500c291701e0601e107018010780041030075619048440841d5901c011045003501d404890b8540c0b03601d414505045180300b106d00d4a9010300454800044003080030001d809000d0303000d04882d120740d035205000c0400c000100e500e00a44904030a50584050099940150f154458503090a00d6500c50314417106480d1006140d1803d485102c00c100030301d0203491204505c0c40c502e441c10070291071904007401d644030755245003d813a1007140441101000300301001c41800c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 193059361 1250 193058111 193058141
    0x91002030d0204180501060302031012020f0406090b01081501091e1508071b0f110a080102190e091302061c11030f07090501090b070c050303030a0209120a0c140103 72
    0xe44d203071842d5002e85698603440182c0300e41482e001007103083c02030094a200b03840f0b8680980003107240592074000d00321003030016604a007403d29051426201c1c0c0c01140c0c0500514180402d440c01880c00040140600820425110f4600d803020035031b507039000301e04408503200300020b000200812800c04100802d01d070300c155100c0d9584564944102e80214110303118440075141e038404101c12620400914010701c5000300b010184809040001c2c40d43c09083c42e40c04030241c81544460780f070ba0302242c03c9a114400e402d82800919400c022150f40c000c4800050050940e01103140d800c05a000d170032502d0b015840240b20702030100b00b115008000341000600381c50080004c1c0072070094003034010416401501c040e800300000b40000790707206000701210b104492040e50781c00364591411090755410b4000c210200d5183c0b41c03100340056507030b8040000c1c0d030141506070b2005980750350001c10406501c4400c0018500790304090310703031000700724411002c508840c0200c0c0c40c1400c2c0c034816401200204004914980c0f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 193060611 1250 193059361 193059367
    0x1c02010209030d090f140a0b0a0e031608161d06061219050f070206040206030c0d110c011508030d0b0f040c0909060f140f010216030b100504050c091002030d02 70
    0x2d1a580444903501720740b01850030142c11a240d560135964401c1e1b00c84d403e9001026000b003048241c0d4a08018281200e141c40d02401c04400440003c0c28101c45002090300ca005002c010312003181d00b0f0040706a4003580c5201c182ea00f514000c80303041c100c4d81200d640068060f03901e00003011920b80f01c5c100e443c40340c008910f030b80d090302c0c21441402500260344c1c8417001840c9803000280510b0014519140112403540003841c1e07590344da50801195600040050b900340308244910748503559540035184c0301820409500d074503599040209070845200c20009a86506a51810060743e50080201c50210300d50250100c7c910f10380340040789902114488554003d45040244004c95a028018005031107083c801031041c0d41d41c80c0c0d80c48458001c0c4c0e000d106640c4854074032140d0645800440c0b03036036500e41801a82c1300c1038940d1450a0503440700d92301c15201e00240c0307020003601507006030a441c064041201e0821003402d10342c1d003031b210500918000e40c0c0150740d42d00c0030000c1240200241d0303484c540021003e550b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 193061861 1250 193060611 193060633
    0x30304050a0b04060f0c030c150608010c02010e060a02070b011206090b0a0f0c11030901030504050c060c06150108011203031a030303091501090c1b061b090617091c0201020903 77
    0xb42c030391080c0725920016100c68035000c04103201e40d03810240b90307804d513455200200e0180c4880e1f03101e2400f2508144020790301c1c200060158002e00450045a0f03613031700005a804480784100d810694010000760039544104200c02c00220784030089419500100b0000c40345c00d51910b0254000c00f244d0401408049501040241111498016181c003004450051110f1142044281d41c154420080d40315079800903c400105540319a000d0343e4014020b20454060f401d01c0008501039500c03514014220303410280810520742e0305401c1b490078201c030a103454240c543c50811200d00300c0396115001001c064941c0d031000c02a006404241e0b22200340141501d90740c0c1000d02185981b010940c510300a41c21501c00000f6000e2010f100f0328072041a07513200d40c0810b659640c503a0700d10b0745803000c085400a9880b1003906c405002103490215a220940b55100041c0c03d221000e094082031108920326965840c1c2085280385010500c42880b41a2950400a500fa004400c1c5d02900400c031006401d4852001481 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 193063111 1250 193061861 193061879
    0x4030302090a17100507090603020f1b0304290304080a020c0a15120506060a0311071223071104051008030c1e0d090b09010c0f050a05070b2106030304050a 68
    0xb010b40f00c00004a03620154682c0304081034810403552040840e94880b410041507020360000d01c01e4603050040d0500e08401411165006003240f07880011540c0301203002d2104190329021030115055810781000200d41203512a00c152100400091403024007060b03003005607008005400c8080002040c403500107403101e0641030f10590085803040010140b078000100701e10184103082c00b941c8060080c601d000c0d6100c0003a8003500d404000701b16100c40400034a0081842c1407001840713000740340d55180c0300310003403001004e060920203101031030208100107400000708042610b501c074090550300403805948401c2c076401301c1007031907004900f10300000440c0003d41501041d400c0e00010641c24580090310003110f004c2e0344240140350403020610419050050700c682c98017900c02c0307a40c14507044c4141513190341c03100303041c00f8806411a070070b80c0640030050802c00207020010241200800950900d070400800c01c1c0c9510b000c600b450f01c820103900200e00c0d5524140101c0380585005081e104e1400e41d83e50b048 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 193064361 1250 193063111 193063139
    0x7020f0d031107050105190c05130e071e020706020d08090d08100f180c090b030c0c07180b0a05061e07020a09090b010f050d0201200c10030b0f0904050a080304030302090a 75
    0x34402c0c61504005101c2230b8090f1b803e0b13035080c06c640d8012103460350900c3c0d10901e0b6410064820018040c5c500403840c1e604c141c0e4140807010b01d032213601400150b481d180000e45800300015486080c071000f1000c20084600010b49403c84080c941740514160300c41c0c00c00e080f402801c0e0740050040043c140301c0400c541c00d041c040c1e40002d006c003c00c2000003d001d90002c80f4852068058010018000c102007007110801401618003000141d05890066590b04418004403002c0302c128182251110980865458900c0041d8010082540c54514000d0a88185ca225040c18068031124041c0406c2040035526081d0031000540004a810080c0c46a60700f000c0c3c0a40100740f20b403c0081c0d071190400b148038100115161019607040e1101005c48081840542c4582000d046107a080d20a07949000030a0703440b071104c221a40210348002488407040742c04d2102030800d0100080c0079510f100180b200081700029425401d40e000484691680c03160f01c0c04078080e203e01c0c205168000340031080030404042030084 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 193065611 1250 193064361 193064401
    0x121209030317100e0903070b0a02091c060e060103210206070516060908070f022b02060702010c050601090614010e030d0c080706051f0509070e090601020f030c0c040507020f0d031107050105 83
    0x4010407940c880110305d062f0710a2840c015040000000c05d500b55000400000030282c0c03040d500460050601074080c0d2500d50241d2064550b0688025003480c0c40c1212705000110f085284083e00c01071500300e02c068241e101d010210205450801d0110091066039441540e1540c1d000500d550b80301098200782c001c00c02441c0007a88a000210300061346141540d600b900c042290501b003c07026112502002690b421204007a414030111000e0b000014030300703022580c00386c2040000050500d041c2191204441c0c0c965001d641400081d02052490b640c001446400090742407401419035046854410003a00038604014210342c1085c0030301c008942150344500b0084048200400c089548804001c42e03c01d041e00c80c0000310300c140402c40264205001404c1c0d100300c042c011104014400041903155601050a04105402405200c00c0c03a107068012540c21544504c0104420800b03110103540350408190b040050640d2801850119103400782540e018507003080c002c120625103045032542908200b00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 193066861 1250 193065611 193065623
    0x81b030c0a03060506030f0a0b040e060702060a0612030804020907110f0d12060608041b0512030c010e03070c090e0a020d03020307063b0a060501121209030317100e090307 75
    0x5408141303424010190ba20030104040c080c0c03450744070428950300621000307002075000f5807a2102c2140400c0104085401003200f58000e00c41460440320039070441c0d2180e00f0000d400c038100046440800c0e4030840c0d8030341003a011035000c003003038035040300680f072078040c0b20701c0c4400d54004c044d248060050042800c10000004e61158121043d040355013004a40060141c0b001080c681d40c00315022401c042c14064001240a202f4000b00341c581c80021490001c4103807140041e40300088238403100170280a02c0c44c03051134500003141003044603644d260765180d0714060f1100d10b40e40e840307001c084968108400e80c0010340160800c80259140e060007034036640240c50643c1e070182008450043c1e61070090591618821000141c02442e400715030420003803138039413605d91040c4900041c641c0400c0c4988582c80c028613940e030480d08091518078200300054a081690380178408001020000710760028104814040d40d690004540c0c1d580c011419080901a002000d61031000c0041004840001000b4185140244 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 193068111 1250 193066861 193066871
    0x200a1e0611040f060c05150a0207060f180b0a0b100507050c0d0c0902090d06020c07050102120f250515220c060c020d1509030e030c0a0303081b030c0a03 67
    0xd001501900c11446000f8002c801c016081003010712540030405000d200ba02680e002c4648801c1c40e0007801c00c1901d0840c50311358001960010030940c2d10404500a80803e0140107210010800154041000d10040c0c00c04c1e01803000101f03e60b10079408203030160380081100c0724840380c0450042894114410031a86440b84d04541226440c0007940000703c1c0d9804240146020308194085001e5040305145c0381c1c000c80700040c0c4000160250015001507142103000340384030703898040028a4609030000e011803600d82049960a5601074008641d00c0c054807002003028403000c204c07013001015040d80064514010718100c03d8a040101c0c04c3d050107462201086070103603000f00c0d507000505449640041155004d0b08040140c40d0055042d07464107800100300f14103c48980e1145104020400b180a00040d5180b06010800d42c00c0312500c030b07050000354010070040001c900425151201c031f000103000e2144040c00070f52420341c690b080807001880203804e06e072281000c0041e41420340195081b940403031b040c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 193069361 1250 193068111 193068131
    0x1080906060a030326150a3008040806070206010602010c0f020a0b09011d030c1002120f061309051b040203070215070507080a080612070501200a1e06 66
    0x1002400384100030010070001d03183d13641c2034460030002c034010000d03c0303805400c030f4001039816580c4521840e0020b62028400041c0b20821103000050f4120390f0b90140d052020541e09900c03401039a00d007900946000341e00c0308550806106601130b41d0f100102e144154000c0049403503010403c80c4c1210690b40091080d45448041a540000e0b600c040d2070040e48800180404100b80c03641c070a400c10850400080c002c020200004002021b80c1410030180e800041c0f0342d004070800304840303403600070360f150708600b000c503801400d810030031026005403100390f442000b00c3c00a036120f661410b402400031a042000304010301e4030700e4035103010b10108440300103008224004c030b04103030084134491900c95000e450707030814000800c0b040d0900030340698100041413203601d0000c0c4030704000f04044041d545820001d03190400c00c00c04c01142064185c542a080118204031598201e1518091072008603511030441d145030940500d4079400c990003610b040000c0e51010034090302c0f46030541a11f802131400b403018080c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 193070611 1250 193069361 193069363
    0x190e04050a1a040902040605030312090d020a020d0201030f0f1a0f0d0c0611160e06041506080604020f0c07260304030c0b0309010219030c020f0a050607030b061303050c010809 77
    0x21100e8070b024a03601581c1004100c0c681035203c28041840148006203da4032200468a0745d08006c080c181e42e520940c0034001079440400c040d0501500c1c500c010301005140d6404a9541400070300000e060645074507030751000606903005a5840111640104030301c0d644000780c0e100d1281380c500024003c0149a40846290514400050080b50440403034201c40c0d140c200b0840c0d49a25840c00036205003e003c0c1c1072180c8903007202d40362008291400d01d03541242403c100704400c555640992111000070360004001e01900000400d0348400121001070f150601030501802c1807084e0348400910703000d220710104080b00c903d440c42444528208a602031031200c0c0c44640c0d82c1b88140d0102604aa40c0a1000c12220303181c2c4000715800301e0541c0000d400c01c035007402c00c640b00820301030b01d402c0420344a100c1810300c2a410032041022800050003064207403000e807241521a0000341003a41015101da40400d52a240e2104403058020000ca05484556580c02e05070344601e0100e40322800a41c10001281c003800e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 193071861 1250 193070611 193070621
    0x190302070513060b070f0c03080c010504020f1f030f0204030501021309050c0304110904030c15050610031406150f07030504030309050402040e0a0e0f07060c020306011d01090207020402190e04050a 86
    0x7410071082450094651644030050803161b9084980d0131070340b03401000190003400904401c1814800219160802c0d00c1000400080c884101e406040d0645004c001480500096040442c3e107060018003040350405940c0684100d03000a44150300001d06242140701050299045400b0744004000c90788540f140f83c801c5100c00c1c4d801810007007940300c15000c1803a00c0d1584e640c12601c01d040005010703034107680d00d40700248203d4060f002c06070768030200017140c01c200b000c0c188034640c02c0c035040010800300400d0420983c00500028064000d0040c10b0800a00400c100c801e0350490304812034a50800340380007020750b840750000300c001400c0187d00150a08050098034240c0d1591920540b90f035490064020007060405203030007280c0b06102034a04010401d101b420050441c0b45d60b44984a0304e140180341c1380800683c001c07507540380b11481010030018900701c2c85041d1441e0364409640c0d01b4180c00060060700030100d1004481c2c01404844460306c1c1c00003914030b02542c00780c806021543e5102a4002154 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 193073111 1250 193071861 193071869
    0x1b052d0c150703030c03090606270c120902060403020415090b0118060815060406111204060906081906090b1306030b0a020d060902030c03040c15020705011119030207051306 76
    0x281c1c140b01c0800007900030b4014200d81001c81ca4002607003841034a5100540f000b660050304500c0c0c02402c8030300300124800e100c240d030300070000c0240551440400b004001185090601e480346079203a011403310f681e0481118000c6400800620080c00100b02140102855100d405141480c1200e204c0a6500585050400c40703a0b030b02c030044445103480d40035210311000401e49010301045440655856450314007510203080300b59241e4565000d0103900620340903510b03c03841d400001c188001c0200315030013505101036410f245401c420503107900d60340c40c45510350706100b441c0e41400c00d00701003807888036648a282c01c190110340c40c519045580350039200300c40113800042d02105605000079081c07940f40d0020841e028048000140b0303141d0b02c100500c100c1c0c10668030991504000400d0205000d800b900f010041c142504104c2c0d162005d11030041e540308140d105041c180a00c03020fa5015210b000e001040004800302114000c418003490000c0d180e0b0400c0c001c10340b03d41c40a001a05200c08117114034400d80f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 193074361 1250 193073111 193073149
    0x6070206101403010f1a01020709060b0f0918040b0f0f101505090303040e04141501050103090606150906301802100e041404031b052d0c 60
    0x1070501d500c400d108a48150219059900c82945d50100c03c064820302409070759500c207080ba0032011500090612046920410130345050450900100f03000c0c03c1180d108807a00340e41141d94603030703e81c0881c403e118a40340064420303805c030381000240325140b1006482006002c0014800303a071052032a10161009440042c0e456103018001e0045207044002096890001c1c20054245090840084d2030f6074869007098010145080612080025a0781803c092100c03400240c10030300545082601e030800148141410940c1340c654036014424a980284041c00c0d050010220342400c171007002d040000c240c81100b001615403030f080444989182d001c2500d040e00c1900700116000d045002802414040180300c420201c0765240c0401a996081241e00d9403045840c0c40c00000d24050400040792030482c180c500c425100c7d8100000250701c4443d00155910000c1c03071321080c8035941041ba1420414000342a0700041543c00076125640c0454080d000e42c0004080314034842e03400c41070000b0348241c200c49000c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 193075611 1250 193074361 193074391
    0xc060a0c0c030e150f070309090605040b0102061501090b04031208070306050d021201020c06070c06060e060105070618080a020102180a15050c120a0504050f030c010801120c180b010206070206 84
    0xd00e8401c0713000d40848080812503080941d000d02915050340130460890100f800c03800304100303a50342d80c014030b402814101c40400a40ca00040041c0d10350701c0081c00503c00b92500400390717200c0d0380a11444809440c204079080d890f1601d902d8400e5280d21004003110109101c20002004584030380503403001c1c1e070005806c20184031580d03428403100c002215503080c5195001e0110368114501001840d128195542d03031070000c040d01382091021150250442062a246141001843d07604401121600c80d03018cc0b00282c0405500c0a0140414598900900b04000020b00100342c9605401615810f18845544040d60040ea01003045940a0b4030602203102c141c0b001c008400c5000d1005043c44950503030507100125802c1041440650201c06400003050020900303010900b00700c0450480c6403020b40007000a249030000203000400305100d148600c4080642e41020040c1e005030b1704009200c0c4250500300030040c3c01512010380001c6010038014850640001e0682d440010403c1c06201180075a00c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 193076861 1250 193075611 193075637
    0x50705151e271504061407050c06010e06060c151e0405100203070c0506010815180a020f030705032b0504120f0609301d091005060c060a0c0c03 63
    0x11010100000d000075900506083c20410348400c80503a2045115440c0054001040c1c46030000c0e003000a4200810000c00780b0180e01c440c240060200d0541e510300e07915480c0d03a030312403000420301e1140011032001c40c069100d56075100464408000d0040f080d000401c19601c41103030b8060401e003400c54000c1c001d40e1144072810103146441d402160440d40500e40134154158580b01d8900d854401c0e80001030542c44801010000520044002d410042211403a50b01c00449424143d0f5a058070002910808250841410701e80d400c04c100c1d8000d000c0036040e1152000650404000481d419045480d98003000c6294038505104108540035242d101c640070b0078509072601c81100b82d075444007048031080d40c1c4508404c0411050040403200340201e104580d04020055a40c107405140c0040c00c2e0300b40402502d0b00e1510850010900e01d0b086000d440c104201d64800032044c0360b101881e400550881c0001074084242c00b00452071074824220000240582c80e5a0442128103503c0c100000c2d00187d080c00c00c0c26 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 193078111 1250 193076861 193076911
    0x715050a02120d060503060106020d0305070807081816170c010c080d05090309090c09030f07060c0201030f0f0507050d05060f06030105040203041119060834050705151e 74
    0x4144403c0090024810b038994011903c1c00c0c800303030000c0015906c043c801c1c104466060140039807000b80d40c03034100c0041c00d026002422590021f00004001e418410307080e411031400304070082c03000e005100020502552001850885002c2144102442c05012100c0e12907500400c0039000c0c0c0c0e80d000e42080e1501c13500f0f0150f40024100640705d40341c41e000401c80050140d0722440018040c42c1c4101c00306544411078410145000c0c0200c103e269641c0024104010b080c5c2c001114021903502820081401d03000070814100400f116a0300c000300500d443c0501c030440d0f46c05000f8100f00c21621200704600d45892040190a90f000e8440e5544810b003003005000c5030519401131341c0c105204804560040c0e102800003030401c02c008034170246e00c0c0340e809001c01003254004110b68004003880d198100d040550392020320004d40c0100821030b92900041c000942901c90000c803040d2980101c10b4826504020480381e03170152041d5045121012000001c40c0d0310040308e10301070b0107001480000f44044000039080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 193079361 1250 193078111 193078117
    0x70c050c0607080936010612060602100f091b17030c0d0509031911130504020d060903140c010f1a03071a0405130b03150f06010c020607020d050715050a0212 69
    0x5c8180c2c880b0f80b5540384203c40c42208a42c3c0c084e4091082e01a0a604003200101554424007003840705d103060000400240b42c0104030400c0c0f0b00e4481c0f1011401d58010007030140605000300008040c1100340e0485901c1368407250700700054079005250300100083c1d140301641d0f2801200c000e2030302078100300c0310301000300d01443c01000748502c00740540708070001e035011032140080c011405a0b0481c044040031110752901c2d044108001d511030100b00071030704050300495880890004003c00883d038400c1c8000c203041c0910380341000010040e6606503103c0c5036041840c081d0801408200d012410301c0f905080c1c0c1128801c005400000280c014000d003841d11544405544800080c3c40e213500c400c010218098413600c48550a403080c0305404152a45148107140c50710041804060b07643c481d902c203003c940d0442e0140b83d5008442440c00f00302d1140180006002c51140342c400039888100e800190040203000311b8403008070b6807100e41c0625125030508055a4520030005000f0058004126008269502c1030103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 193080611 1250 193079361 193079389
    0x20702030c27060d0501050a1e06030812060604030804031a0a060605070221030703050c06060108040b0f07050d0c030b040605090106020a0b09010f02220b040302090f0a0e0303070c050c06070809 85
    0x43c01c40d0313620154446a08591040d1180c60f42c1545803100304030f4203180c15030540200140100204411303803958554000a01503000c0249550300c81d031001c118540d5444042c0c50245400840b603030b0381d41e940c0e407030003400c0c1d1400f14052195800e15a80003d90800c180c0c4604811500355403503452802c1d444e50b01b0042e2084c4841c899001d15007542d0b46a90701d081c0104040d0007600d10944450703070340e5010000c1c0180392140060000b0b0410448404210000706002e103025000070f103c1e00700722641d4803410000d1701d0360f0181d0240304003114a401c0012035400c1d415008403c80003c10354040002e2506c403014060045400d004600c0960320600301c0c080040c803000e11719580007000d1400040c0c204404480c0d03006170f03406103400b4070050684a041c1d204213109011024010300d5080040d500c3c0601c0c541c0070400d0808001c140c2c0480d622600c0000c0c5078a074a07a081000c21240030b100340c0e90f0b00d18000502034131800e00c468068035988128845903e02c1c1c10706004551040350000d41d418180010241040302848250740 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 193081861 1250 193080611 193080619
    0x30f04020103060e01290a02031e070506042d02011b0201140f030403081006020a060f0b090414011d211b0705040b030a1101030b0103020f0d020702030c2706 69
    0x480044c9403800441c0f4140a01801174041081c0604509600e5800480d52400e03440c0d1002003211012403a000030450b00700ca042c030070b2610b8000c40343c0480c80c4071174024003001625a014907030070401000031070307130446098022000c90482618021b05014000c4590700c00003d0115440d22038200d036291801050000c845d00c14540400384041d103100800007070308075481d0702140e00d002005010402d90004000b0307500240c40c180d0580400d00e45000255503000c07601020306215a038001e61310304869141c0102c03c0020010701030781ea0f0340c14503103049508005441c007684501c2d441e21381010400b203141400c11036018504030060075402c07007030112a401040780c4001d480c010710041010780604614081d189881201a10103409010319004c14003003560300703138403205202c0c4c0c0081c1e8200c80000d03840c440d86220718000f072a0010790007600100503070003031280709500910501c0100300c0754241c0d6044d80040c001c45200b07605858086989500340a9041d4943c1a040000e84580103001103240914031200da220034014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 193083111 1250 193081861 193081871
    0x402061602130509010b0d0b0f04080f0c0a03110106050105040510020304050312030906281a0a0305030405130501150c081c05151005091302091210060902040308030f04020103 77
    0x41c0c001405012610328042d20b0b81d480c0c600f0015038050a1150030250b80003030f0380b0040003003000d039121360a1010040035496140e4140d03020406100245040d260040064035070295260038a1441c03e50b00c81a070b03403080300020882a540f5414910602940d0b040f0345040e1190340c1402d081c0740400c40c1001c021840001140f000303101c0052306036001c000c05c9003142286440c4030350f2411f28407029414120b0081c02102c1043c9680100e400800612082003080d061801c0000b40451000c140491040078110525078040440c05020003400004070013001150760440714000142d60f9880c1070016120244150740440110030001502c1d68000c40807648414440c0364254070700040c00c110782c0f403440402e540c4400026503410802040e00221640801c843c007084800100041403160010214460b04030302c107024108100c040c07040d000740364040c0c8440c100020010800b01d1202110255039644007490035400500708040000d1413071041c802c440949410041d414074568840c2100c09045030041c3c8200c0c10540d0359 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 193084361 1250 193083111 193083113
    0xb010815011a04031428110402030412050702013005090f0a030c050304030204020f07033c1209060e160308091012050106050d0c0306260a06060902030106140a0804020616 75
    0x40381010141e1b000200703002c002c05030f5086c10300080020f0401c0382e0182c0d104200344004500323007008a0700b4005061400c556100654401203480042ca4030070840340341303881780003a000340d4010350302034420511a40f0200903d83d9040c4010f81d940300314081c40030050304031451000c040784c03086600f030310814041c100f01c03441c0c580e407640400c0403680b1081c4400f40c00000455810209603200342c001101c0e41808040d450b026050040040075000022502041c2c2607401c4544a245409101c14403403960801c0d80c00c2061802a0410368082e1645113109942360103040781c0f1000180c4981501c4080e02e400054241c00c04071030701e0500c0a4480d6603a412000c1c800002d00000c800417450090901030701c000da0b00d0700d440e05242030008040e9800d0004403c00d160400b10706022200520081c0200c0322000704020070f01d0b0145900381d5041403031648020341141d080402c041900c0c481c94000f0350403100c803561041c0400311081440c802030f00440b01c2d000f0004070a0004a0094a013000c06012604000d0720b403c1c0004e116 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 193085611 1250 193084361 193084393
    0xc0319060e120a120e03070c350102120702062802070f0302010603022b080342040e0c0103110417010501030204050f0103031b0f0b010815011a040314 66
    0xb00800500103011119460079102060044003254841017004505040c1e0555071a61101c001d806203160704e02c6035200c04034070f51140007140b00d094400300c40000c0c0c28903018046107001c1d60000d84860390150044011520a51002032014810524a40c8103440c0d500191103000b10741203030b0006a480580c081c4095004908814180e00c2c0d428480c0d0000500d981ca144180a45102d00100a2030b0f040c8035100210b4800100c0c03a40414001c0c1e1040c0901d13a03940d191818a011105581204010044002120007802d41e480c0c01240b1914944404424451142010001038411400310004150400c1c070b038000d10303540a0b40010b0300c110f00440c0d50504143d21a1402030400c0c0400110b250280c2d1148010800e41c00d140c865150045450000e0032500d41c1142c0303005e07190040e40020003480c3d0494508a909010300e030081c0040050303200000c4113039565a03004140d034820f03408034181c40400c102000066252552442c4030b1000d14401e58190515240d9111401c0c801c80b149601c05450240c00110740c07020003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 193086861 1250 193085611 193085617
    0x3050c0c06041d10060905190b031e0108060c0d090320160f0303080105060d021e04080613110d061d030304120f09170c090c0a020c0319060e12 63
    0x14507801d49014840503d4000d0300041800740500c0c101902c51a028010164440d00e05000d41e80c054074407600380610f000072070f40c5408a80e80100e000c050701009000e400ba4101020b82c10000c16100c01e41c2032a40c0711003a02d52141c1c420364000918600800c50003802c40201c0d0000d0b55614040d0a0180c442264040782c5c100402d000030784004150400c0b82144081612080303010060321303d0046180c0d645040d640d010700385410601400c0d100e80c0d4040746080c25403010360110751655880c1d04c240183e0500280001085030030078010805140203110001d002c6605003101504510340052900400d00c01e201c060048542545a054840a4450001c0303031384100201c04403080340440c000119074a29103030810340d0300307003001411107420018020403d0a50b6075108440c48141c4854034004000310311104035203481c258546003500e030000170a408009584c401c0c0409001034480c540c0a03100601115010151275080060782141c0d100011455007010070340b10381c05140c00c00d02031011144104902c03503c90100d50 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 193088111 1250 193086861 193086869
    0x40809040f020322021503061f0507030909050f0a0c0e0405090705010f050301060806151603020709110703080114040e0f0303070f0f0e0f1906030605031203070c03050c0c0604 77
    0x642c00000784680111444201c0340c0c0304000d8036407400e02d00e0b040c2d80011032032500c146140c98041c82c0400403817100e6071110301c5e4808115a5584842c2001007030701e0082d0440d00031030300660200f4424240090b2a00003405038501c41c074100b50107000c2c80d55481c6140b000030f1000008050030404414606415910385100340381c01000341c0b078000c108082c80d0400040c401c0b9400301c1c10f5000c00100f4070040210035002a01250400811511850f0000182010309158000d581101c2401420020404145078002c2844c1064550040083c0400c07100c03080c15042030710906d4001030000344020010000c80c03e01403c01d0030002e600500200305841c1143c4650303c5c081880e194450301d0741000050004194002220100d01001d50402e03a20b00f0000d41e001400e5410701e1150310380104540314545250740d4881d000000605165984071465a4840400500402050003824043d100b1011a510130800f803006592054015990b620513803000e6940031562074000141040311481104030119003580c81c070000d07101030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 193089361 1250 193088111 193088141
    0xa02100e130f0501050f0303030a0e1c0e010f031e0213030c060906030b0102210a0c080c0f15040807080d0605030a03120f1a01050c1c0207031a10050904080904 70
    0x11001200b0310900320703035040c5d121074071170740d1880e1000c04980c03130100680340d122300c0b12800020542c40c14035a090802e1607a1180c900070f024030a0703100c10704ae40c128110f090050020380e00c0c1651000c000ea0140c084481550010600c1c24200341d40181c0300840d500102010183c9002c4689195a00c0c0d448020120301600b0030380c08500c0c90301c41440b500750301d441902c00c00c00c004d20081400108030002c2c2c00081030701d03008a031181c010005500180500a0038104202680090755a94900c110040c181d21040d0103800c2007a28086e0b0903640f211f81030103902a0b409245c0203088645050070940d2441040d500280396042519210400007074282d90601401020340e01036241d030200002c510207000201d8040706801d0408031714061401c07010514054407220400703000e0030065920072034a02ea86292464074840100303201030049451600780d034042500411688280e525611580c15540b00ba10051001c991580710344202840030040740c0b504104a98120703014003000e614061542c40800c080e202999005202 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 193090611 1250 193089361 193089371
    0x1b0302030c120310050d1e0308060a08030c030406260108011a030a050c0f06041a1902031206010f050f03040308090f030906120604060509130303060501050702030a02100e13 76
    0x4800c0244039207650b940410145510b50718065442c1d541030010b502440d4091040b0200c08810000c4506000d80da2616800c0c24001c2148a40340007040c07000c040340c885020322008040040c0c0039030004143c80d031500002010f1428603041c440c08070307001104c007107040503c54120b1503090001003107080024042e07e18400003040d8107105201c0064810a61000d050181e80000d6143e00810f4000c10100c400c148119402d5aa860314540000c50794015600032041442090f20200c0340303c0c1c0918010a05003070300629118840302d50302c0302a40c40e03024982c0000c007105a03a0001800961142da206900718a060030068103080491082103041d4000301d400300d000c075a0203020312120725001c2000360749001c058001180f80c00d1962000c1280c074000d40781e8400044000c00c01282c110b0355240c0140e0050070024010b81c480b0f1411010420805489800176400700c2e00c2e0030008126544180c04507100960061300400c0003114984c01d100440c501d9001c1d80c8200a81c00d581441d15990f0b4074101a8000c1c01c0404c00700c0d03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 193091861 1250 193090611 193090627
    0x40e060307051002160b0c1009031e02010b1801030f0b07020109060606020f12040803090603040f170d0f050106080402090a0f0606120b04061226030f01030b060d02011e1b030203 78
    0xb45e1006600408801c1c0418482000807e40c000f40c0410660240c03140810141441c1c80c0a552103da08006050502080312110344d40c60f605501115003c101251290a2205a00e034203981c080400e00004d880c4080000c02d503400b10301141c5022740c0101840c800010782c0c49141d211501218170942004005030020820101080410001074041600780e00d60145417031310301a0702c55036a100300a90035000c0c0d54044000340a0220203e4180e40854024005144007040401440c00551214002140301440c0406121108403a40314a9060361156281c40342c050b2a00d808124513a01c0c018069110346841c1e00003044a2200c50107500028005d5803142402400700007400c000392000c0000d803500907842d000f13040108a61170240c1000f00c9410481107400c98141c181c10050b8540a10031030342e003210001052142c001242d1207104c0c101c90084001014940b111820040f05505030600a030001d10a10003891050404902c01c201030046818941e40703c018604000000c9080490250301503040403e81e41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 193093111 1250 193091861 193091893
    0x3220506100303111203061002010906050705070b090a02010203090f03190506010f0915030201050913021615020a0c0b071106090109061d030708030402010509060d0c0e030c06040e060307051002 85
    0x8400184004e024195103213910f00600c0c1d4901000b0f007524480d03203901d40b0b8100c0017030007980b208482c150480703000c2c0480d01d0100030240c010342c0070080448612a60340005005443c0c0850758040050381603000d10301c4d101c0450100480c04240c0503d45900d40113900d901040c7c885182ea603c03940521840c090002585050184501203919611510f62541805101501e11480211140a807542400d00c1501d40f10000c020900c4540f030501d118030300300c0c070002ea40180390065440002c041840741c6006007080341e84441e200140c1c06101e000034042120301da1140006a22484019408050b41c60448415210b035001039142000545584120340d5440c25100240034450242009103084c0795814440e580c1103c0840c0d139248101700303018010b810040082402c6a226000b10344d103600c0010501602c2c0d2303105c24a81f00c01080d100c2d10190101c2e000c001001001d04000ca03c842c440a002802e43e42440e26050008130101c0340141740a80c140145100401c0340e030f803031041c0101000d1040c7c2c01440c1b04c240e081002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 193094361 1250 193093111 193093127
    0x901060510020106030c03021c0b0f09070605040803030721090b101a03010b0d110c010e2505090406091403071704300503190e0f0603220506100303 65
    0xd078046905150060010030090020b1000b01c0f641500c400d402c1c48400e04440c240f420b0341da9001040c01c14100b0600c0b6000485461b1240151051401c3e100c0300e0741e69820940d050b208038480d00241c2c0d002440060881800f503148107090100002440c40c0000c404a05642241c920307081c121405044e8000303100798000c0c425002d0000e40900c039224681e110701e407032000a00e4041403040c0e517003c6200080e07010586c811600000800d4a400d0200c0d074a881c0d01d10805d9002c0c146498103142284540e440d21441107101d492011301c00000300703070100712103030512040c0050b46900a1059070400d40f6840c095000410700c60340e480d401c3c40346102554881d08070345000d80008400c1c00b2245141c4505110500c105907003045542c1070641600d50f0b03504124001c1c00d0311407082402420141544c0004550300c5904c0d1110005c45000780c007a9a15010310f0394904041103440e40f401070240740c00c642d091002614071401110032130240c8111482000c8040002c1e6900c0b8039081007203451000c0881000010810142c000002c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 193095611 1250 193094361 193094389
    0x5070b0604020c030f07060e01090803010306050f1b0f0906040b27011707020a1b060e01030204150e0a0e04050106030201030506031b01140f03090601080c1801050103022109010605 79
    0x107503d8050f0302464140da07070154500304e05014500080c80350401034a9441240c031120385c00001e03c404800380c2400c08080e00240b200303551031810900003440001142c010b180c41031350760101c202410482128410b07215008401749100b210000c0200200076510100a007004100600c1e2040d500ca107a1110313148066000c00341d0f030b2840402c41c0490582070303030059444c100c410805002a899659604012440c1000c0c41c0e9000d407942d241862008068001e840601007903605503210002070030f1115004404034403a41c801d00a1204098100a603d1351040b145906007020040059011540b80c969114620400761401c54442c2e40d2400e0420441d6094011b017540580228050300034624941c4402071040c2c2030248003410407611a0040c0c6c4240e580350180c0703c18400441c40603441c0d1074800c00555035070350300b07005240b024412007100c102e0501d0b1100040581c10321004401e0350076481d1000642c041e401070001800f00c0f01d042d0410194084040000611440041c000030078024940030600c80f901c210040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 193096861 1250 193095611 193095619
    0x12021c0f032604050607030501080a0305030606070302010209120307110114070204051b070b0402040b0603040f080c010209040e1b01080606040303270303180603020307090504090c0504020a05070b06 87
    0x4a18042514000e6005049400d4101401d000b031a00000303884480c030303031212890354018010502007840b100003100da01c10348207903d0800040e41c90350f0b0030541c0e40c0e545060040c00a00200b002910300d00f840303005404014030074000907042c8107502c000103502600300103200c241070340042205014010920700c00604038000b0308000c4a22480d00074015821300c100b0707101a000b6500e4501041c0822122040d14280144032010350f42c40d0546442d001d2810181aa801c2e4896800d100480040b03142420407079010307951183c0d01c024207000681d6a6080368102204400055509020744d000326111401030003101700042c1d02404104c54900591343c5103041041d2402d04001c114001c00c1129180c8034100c0c1c09694250130414502c0c05c0c800203500702d680543d0008200f42d0003040c4000105500004202200195818080065500c40604274200d0104450003000501d08074401c0090382001d9000c00b6500740501d002041541e02c940120341a6400b0102003000540001001070a01101095082d04100112 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 193098111 1250 193096861 193096909
    0x8100e0c1f0909060501270305071e1d04020127091b0320070501020f210f10030f0f06061806060903050a1b0e0a0204170c0306010e0a02070503041202 66
    0x2050f4003410041c0c42c501c40d071f03250704050504600c030385420000c40d840f000315000c2d00c6c2ca8541c3c5030060704000316031110f54407581c00b004c5107160002940c81c8185504071090300c200d41c0c030ba400454103285910024641d40384c044044c400c1d0103041d05003a4025103101c040201e85085087c80c6001c00c202011203002c105449c050000d0003004001020184c1d402403059035548419440c100140213100d2510440448240010030008d00c0741e0f00c4200c2e24840e070002d0b40d40015582e8000303036207410710400c40d840d080e00e6040c44000c0c00080c0100000c0c11885009144d0b101e9500e0007542c4a204448594005147d10b2410f6080325a138020715008182c003524092410918880c51559030b55503e2080e600b00800d10b580141e4490010040290614001d03c90f0300024441801c0c20a4280001d42c4540910545d052411001c2d1030040c40005220008150250082140760f2800080803640700300a00303048070302c1da001c000d2400803460410103040a08a00400c0310301100759881042000803190f40c040c240c44c1524 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 193099361 1250 193098111 193098119
    0x301231009090e03040b180306010b04060c020d03110105041406090c010903122604050601140d260c06100801140f061f03050a050a0608100e0c1f090906 67
    0x10450320411201c00007030209455414504003130840c021900031540360140822403440054613041c442e0801c040c03d500b510407590b2141070034901880380d4000c0300c0c081a6400303801d00c01030903c8100c8070000b81c0a481d0080c0300c8613164000394250f4809507400d40300c0c0400c9111504d0301030f009200054015a4580c018a00c002d04400040c00100f03180c4000f800d601540c2c040c10311003038055028104002407001f280e6481124840e4001d005039020b4405883d5803003524000300d0000185203205003180c400412a0082c50020780e60301d02c40050601ca03849200b1501c588081901c80030401a0001d003075444050042c610303080003444121400356100000b180c1c10311400014600c51003101355040746451015034200d9880c44085550710b940380c4941541030201c0c180a182503641540321a00581c40707a40e040c8285c0d107801007204151205401211403540040c400914580b02c1a070203440098112400e441d000b0000b140000d0b206440741c240c001901038011340762290b065201c03481c50081c1c000f01c40204081414 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 193100611 1250 193099361 193099367
    0x506100f2a050d020304090b0306010b0f03100b0313020429151306110d140901180503030307030204061103030907060e010309061109040c080606070f0c0b03012310 72
    0x40403010461903900100d600407400d62036200c503001c0e6030408201d0355000001c0c54000d590740d01500c113081210307140c44000d040e00d24020803101d0480c0d42c0c01400d2810705200400c121041d520250103030000030b140e00000103800d03000b4000b0307611960b104010b03030440c1a02401071109035051342040c0d0784944e0041c82144c150702510801c402c25160203803113150701003051b401481c0c11441000d80c4901d0001a4140c0042c00039808a8a41c000201d014182d500100001109a034540110110440109014003811145501c41c41c86101880d040d002c280d0041a43c1d04040303070465006a41701c00010344c00007028008035411580305c111030f4020320011031031840d04544041d21900b450156508003c80e5074603010080c3c1c841d41140c0083c5800c840c04001a154244d80c0308100d80c44411254015400d00100041250169400500c10701018000c18070744042d5943d544601000928201c4294180b10300100e550722285002c0d50103442403031444802d68061240e180c19034050300300418841c844100a4040c00381d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 193101861 1250 193100611 193100627
    0xf021609020f12090105161b0611070807060c2006040b07050918010e01050a060503060402070c0b0a0302030f360c040c0c210c0818040603060506100f 66
    0x410300401601c605a01040c1c254500c03030b60280d08055003086007070042006066104600079100303c0c4450a0041c003166040d80d400380000481c1c444da68241800380080360040e00820940300c0c0950341b85145c602d19544944103608000300540e41290355900740041da42c2c1113080084603040c0e03280d41c42d24682400e81c420741d45800041c0000e2500d6800300101d41d0b800c3c0550300750740c48050011319802c0c0c240d2500300d00c0ca820311403d00c115010815040000596410400c1f80002034540a40c0c1e810324581d520360510010b548101e40807110201085000036024289201034840c0b080207640150380d03400e28050170a60303c18043e040b0a4082d0360302002440a070040da00c0d80d4084a500511656044c498403260741c101862010007070303001707818880c22810066204c0723005848179104550f50320800200044591092445003c58008074000360404000f2441010140201009180712410001e59a41c0401e060300c1070790340102d501c00c8c0c940c0c1c1441000c0c602a0103031503550341c0341e180c41d461400480e0b0004180384 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 193103111 1250 193101861 193101869
    0x70915060c0303023a1e0b06090307030b07021b0d030c02120f0d020f1b060d090c0905091009021e030705040e030702030706020708100e1603080a0f0216 67
    0x8100c400070202098000c0d010b98210200301c2c04280d075220b091350311900d02e0250b035140040301991480c014440c8103c1c3c5100e0004856458030103d08094441750201d80200300d03078044154410400c1c0641c401d45da0f400c2002c98040d6200c0c5d00d5001080c1030564010b4a8020013912074100c05c685403031500102d8a804c0e1038106016014074210741a54032a0000c94004960120380030310b94000c108151700403000c005020072400740c0c59801c450000d16424101a2102c2405150b0000241001803070305151420402a1094002032840042c0e00c08080e40d850140d203510340d00170007000d03484070b0800103d40401e0180030540005003809000e518145d600080540c050050083d800030440d40f41c80c4401d440401c041d901401d8050010801c030300002d250b81d5620741040310120300c030b8801d05401094192005c5154000c50f0611402001c10b40d50380888072010f091220003000305407044c1e01d660a002981442d000008500504030386075a903200080c02032507520b0b03624189003958001042c0d4030402d0a440c408100316 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 193104361 1250 193103111 193103117
    0xf010c0c021002070513020a0507060905070812030108030306091b07120e0904120818100902150408030f070f0210090e0a0b0a030f020102120304081c090503030f0603010e0f030c07091506 82
    0x948c507151083c2c1d000d00900101901c824904482c0c68104003001031b090f0151030156007103071038900c5000c1148820b44424041c0300c1e42c5800601c082541400e0501c100f94219aa911942003a04500079516400340c100110030f43e042d04140800342c0013183c200c0c0c09245103460680b003001251a10380c803006032041d5040d540204202d82d401c00590484040e501d522030036050501070b240184059403000001e000c0c0701c0000d9116140303204281004099078421141142d0451020b0b60070709118901ca01150341041c5015511038650f15900401a03441203d2954180302541b10001281d003481441648800d004102a2446240414003105662036040c8a07003141c0d4014075420001506200403400c0600801c0703003c1e110400801804200508000505004c105001091018510646102050703803000400074055420400200f108683c030700710020b5100002800100c1c5a0144c00c04440c80c00f5040c100000c4c0d60342000ca03808542c0b20003401008002e168102c2e0074021251884281c412104c0644942014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 193105611 1250 193104361 193104367
    0x4091a060a0503120d0b01020a0b0118020708030103030c12030209010c02060d14010e1608190b030a05100b3f01060909081c05070518030f010c0c02100207051302 71
    0xc0c0e0380c401c0044406010b010f41500c1d400c0740d03040c0194810341c004034108105039080c1684000503520028040600c0390f006140318040f64a000708509000c8801c0426040c0748e13400300b002a001c601403000441c0203512039500c442c09038141d030525152501e00004500c041600421542c0c00b035a038440f42c44442ea41c1c04079a1240e640c0050b07648170004285200c0968110080320000040390034001000c2807080c42040c9881c1e0400c107020008540c00c8008545107041c00740c1036000382801c500c9603032003a0a800c0000e0115032462082d916003601d011203c22403415426141c03040110103061180c1d111007480f002085180c0321503407840b40401c0202e148403034002e4101010001407031041094004000415494100300101e003294100b1000070b034481c0900d03410510786090182c1e541e001620560313200c1c502d01c2d6181818030026203107011005213080000c5902d40304a01c0c0c811300b07060080c420340e842883ca60315240f41c8912184188103100d20000340e10015508141c0c002c000c00d865446030050500500280166 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 193106861 1250 193105611 193105621
    0x709080d031a090103030905030708160b091230090d02011404150c02090702032b110d090501050705071709011707020f1903140d062c010504091a 64
    0x2401e007001c0380c2c00c1640f01000800000a143e0002d40380310035100207034256102c0301e4944095503626852401c0841e100104060100812158031000c0d0a050b1002000c6899030030940c00e060749011001241071b03403104100c1c480035403050b00501c00d2000c3d8452030101c270390804503d200010842c4101c010041c4c18020140c510001031519182110040c04800040d610094a19140240f4825204500b240030701090404242500c0c00001aa52441c0e44240c2d0b503205028894402401c1f803004144100940352103042c2002920b0107180a0b08040054036800114464141049401d48101501800a00c1800c00410300422804000070441a80004600c0e0341c0d02c2c2c7c2600100c81981942d252074520ba03081d0014080b4036540400c1c981407407002142140d04010b00b1240440640f03e11040003000308812041c1c0f03041c0b008030300b4041c02c100c041610700042c000381e40703012250b0142442140004085186030a00041c40302a4410fa8007412041d00c0410036807107141d03280a124294500b04412710303040c0d5030007d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 193108111 1250 193106861 193106891
    0x30301051e0303030f07021b030a020d03050d0c030e01110c06070302070f06020a0e031b0d02190b22060206010605070f02150c0106080111090108042004180302060709080d03 76
    0x1c481103809000c6913a2880c0c00f6200d0503481c481562400014018803002860440c041c2c41e040900d69001006045004160345c20800281801074044007441000d10440303855400343d01c00c55202d1042900d0201c1d0803412401c0b42d9003110a2140c1401d4080418001850002400a0015030200c805d080059a9103054180810750980d41080100f030580002040b00046034844401c04a00e4419001c0304c05880c0010214020200302d890600c0d00007640b28501000340c41e0040203180d191070260880e42080d503e55a000d882540b00700b00c10000a4401d81d004c072412000c15009400900c1d5034400b0380302a50410100620b00e125148028140c05d40c500b00d40801e6640b070175940e1000a86404086554400e0424924083c000030701c00e000c201d500e40600c080d02280081c0484005640c160b45004c0c0c19038695407601c0022425008401c49086041c3ca00249902e4030b00c01d11340140d501c411695102101440c0080c68440010098000c2002000c01040360540000e540a820f180a05010a0940e4465200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 193109361 1250 193108111 193108159
    0x11406090408190201090c03150b0904080a1d0d0305071704080607030b030c09180c010215070302030702070b0c010218040e0706080c070b01090f18031706011b0b010918020303030105 80
    0x280c01400080300c0003041010022949c0289561500180b00404c0032100b0416200c2c411600030b048200c040203c40182845014105070a01c07461050348040d400c101d002c1400311181a03c1140850800038040043c40303040324001070a078024984061505050100c0c6030746801e400303031500040c15151082100b040c2d0307061000950010001d407100ba0345252840c011448865102c0c1060b001380a0200e06241652010450504040311064201400d481d03a580c05c82c02948000e01400460050f407001103403990b94080100851b885100015032220311034681c4070490302861042d9072046103800102d100c03200e40440d01c9411614142800346060b50f0780c07001e080c3c81b0301c2140c200600c3e00b26420000b190b003000c0c0e94862400076001c0301d001c000300c44544410070311030101d60700b000d00818114050000004104084c003075000c0f8043c13400c10404000a403a68049002c001c0003203c4c1d001c070315001448461158400c49410341400d020701c0a204800e600404d4807884103018950068240c2402d02c1c1ea40b003003030132407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 193110611 1250 193109361 193109363
    0xf0115061b031e120f02070203070302060706060803070602090301151d0403020106050303070606030512071a0c04120b060405070f0f12060515041e0f0501051806030901140609040819020109 83
    0x141c240e6440c40d800081444000c110403403040d45c030f014500d203c8950540300b43c403820365000d80101040d50464080185942050400700c600c192074641c085a4180144060300002b44100005078480522000309406e455402400c5008036000304401c000b04002c140000e020200d8000d181e0000c2c1d01c481c2800c030b02505d0315801442d05031000180500802945078403a604890003071042e40c201c00b04c08540b00940344a003200c080c14045d04030b41c0c4280501c60f412500d80e080301440440624003a61034544100103509604207030742d0001d0325002c020640c03c150240c6039204655180c40c03801121822070141c8444042c1d0517580800070000d450b84e94844003503100c0c41c040d0000401c07043c503040240030006d685512900811240e20f00042d0303070b19500d281c5d8242000a46101402c1c01441c1414800111081e82116084c540380071201400440207499003401540142150000850a02c0382420654110100644024003940244003040041000f8400707582148101d80d009401d22007420004a000d80744582d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 193111861 1250 193110611 193110647
    0x90510030b150a0207140d02063f0f040b19060f030f05070b0a0e12190506070e01080609070804020102030c060a06060806010c030f0f050c010e0f0115061b03 69
    0x3060090b18580a03008810ba55801c6408031911020380403090f0b880c46030300581160004689400614104000e04180c105102549a0f0030300e41c0c1e11080c110043c0d0300013511b07110728005c0250820013184142e06900c82038640c1019542d0600b65940c200c00e2600400c10f034019101500c951605030003940005004041e0b000304180010345a0404001c1000131030402c6a29206040340060311902ca48140c0344d00142c1c58849a0b1040b50340d800b8040c059030b400c64040070741c3c01905210001c1082240480c51443c1c01403008000c0d0340351401015101d00b800c20441418400f0b4034003008802e548000880380e021600d854401110707200c61005078998050103618110f1406002c00300460304019501c040110b8400eaa82c0ca84c1d40c1d1120700040d6944007911f1009800504404541c1800360700540e203912401080e4513006103400d514503c45821030301070001b491502e400c01c091802b01c8607000d00440240250100382c000000303203000c801610801c091000c00c6040c0b8174a250703040038180a1fa00700684204101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 193113111 1250 193111861 193111879
    0x604060e0a1403030a180c06180522060614090f061b1b06030f040b220c050a06030204081b01051603210c1b080405060a091a030601090510030b 63
    0x1c1c2495480e50001c503060031117980f603d601810803034402c9520417840c94000c80013005a9003015401c0798014070480503c825003014280c00266034407042d0754299421210b4070700f1140d4100d0150703480207071540c1d64411410054503028080c0e084403071000311040c1202c12503401284038800307c003088071070080e201da0008a4500b600c0d840345040000c2004480300e40052164544d84101008124203800195920320001c1d1344040080c0014862081c0c0756041100c40a240d03c84034008207602c6100140100116072140035040c0810450410302100707005048e040c1001d504080c240b0709200c0c0d403002100b5400340f20520b1803520000f07c1c1d001300120380c012885900d845640c9542401c0140007412982240e042030800e80e10400c0c82080c40c0d210310f020041d565610b045034410305840103110850941000e40c0c0089003048001030b10751710b0308020000c1c1c8480e40c03990202585403a00f295101c2d0600c3e0810f103034407207003041000a182e9002d460340301510011650100c1034085c514048000381045030b03090390064100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 193114361 1250 193113111 193113143
    0x23060904090c18150b12100302031e06100b0901050703031404060207030f030c05041211061803210f07241b02030405030a0b0402120102030c0a110607020604060e0a 72
    0x4000d00d19440d400d101031040f020300350407110ba02c55080c807809101d140148100d2903034203030781d8040c1c1e90456942111f411b4a82e03180d07000203051030104c100f032541002000d0111003002e0420f101e11a0b0000c80101e41d400aa40f03044a11041c5100744030189041020000362501003501a5005404a00c1c0c850f08010f03c9150920740f0100940c402c41c001c1c0c02081c0040d0010125074420301940300030600c0e96981d1810a450300606041c10048170b80201c8009070822104112901c0c0c18001c0e15000d800311400d06141c040c0c150615041240b20001c030944074649609a40740c01010741c080795921040741080651794155400c1542c5521f400040c84c884441002019598000303254200341050040c6c0449442d5070542140c040c1da0720712aa1044a0301a0485920613022404d101015580700e400038280c040c0158102c5c103003d0072a8000c40e400c120030322000c10070001007507100c0043d5024941040090800741000d500103503450000420052149440703200d0714000d0941481f000b10a03a50200440a1204038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 193115611 1250 193114361 193114379
    0x1303020f190218060f0f0a0812030604110f040308090a0902190305010906081b04020c03030718050907080f18030a0e041b1202071e120923060904090c 66
    0x400342030f8030815880c0d9040c0c2c00b10003111401030042d00d000300144031003c2c1c0d4400344050500c00b103854552212940500180400080c01002c51015a4070072480c1c0d24901241080101d9500c050142040350301400f0000310601e20808039011340b60440a000d880e2050900020304c100c3d003d4010100c111700114507403800e199886d11040d50055181c40a10440c0c1e20b940e00034084070740c944246886548441c652607003240317035035080015144001d80054605010429102d1460b4001c0d5025000100b80e40c0060484c8403001141c0f202600e421154140036060082009001031405850742c0d02c80100d401c041a14079005004c550070107400e00081d60317180c0054a034042d03d20030f00c04050314003460900100318202140040c0d07000e1081703525150005242501f8a460009401101c8110340303201540301c54840b804040784040788018400d02e294107402e961590700800c0503d0a07800001d1820036464003894001341c100400b80c20180c16140c058851040c0c4000801400403141d019243d18a000c2c008110502 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 193116861 1250 193115611 193115653
    0x11040801050a05090c030d1116081b04020a08150310060f0f0503070f0605160218060102010b030a240f0f050103051204030807030509031f05070905030c03061303020f 73
    0x1030003a400c20282d030f1366551854a4010107400b05915400001c80000d03040c0c005c222001d030742111001260b007241c050305060240ea0586800400b0f1a61040d01d4a44580030400342c108200e09007940c0c1035050140c0740c840940100c801030200814541450701c0c81c82c0c140c8003000140b09000401806004069680d554514003180c18001c5200714101481c01046a08000603110211040c91706541c00440c034000086800760440300790200c0e1a05100c0d400347c0541d45400c03944000140505008a03039050510019007100c001c00e004034000c2d00018862004030310010034201c0c0b011000143d104204031000c800c0b40c0284151014100014a0041d000000083c1c59005030b050320b105804840003005803a800343d00d64000e51000600380c0c1010050040080d20900191082c0070f8090304a96680b0706004141c089132058000c1c03440c0b01c031b5540703040211881d80100007100900f42030f00a4103480b01c0c107d010946039040200803d426811500f02c5004142c8204410b080c2a0046006d4840f1543d00b00002c45180c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 193118111 1250 193116861 193116871
    0xf0904020711130f0c0c0b0a0e21030709120c0504050712181b0e0105010e040902030a12081e040605060102032205040f140a090809130204080607050f0f030a1104080105 74
    0x182ca48281c2026190040000c1c00200d50414032050711f40ea1503581e20307005460058030300619405030a5601002c5600c014500c20b00854841d0500d0310b921744a08010304070310285d0300c10501400c06051207000b107019111858103a41d816078000c18581d07280102601d0004d848240c6041c0b09280809564410f4102c00207421501d2041d0146000c02e0000703035541c0600c1d80e040c0500740c64003407168010402d541c0070711b034081030703900014202040b4690385400190030024240c9090305c05603801c00540c0d00c0750f50b210402c503910110318a0301400e101128035190b003203c20000c0004044583da4000700c0c000da802041a1003007014586a4007a13a02074030540c1040b4500306115650003541800c2c244600800980920031642108041080c00360351040d5040300540003840065400040c02c00503000282c03038544460741c5010b942403000d40e45a14000718a490140d004080c46d040250501c5100320b40f5900030308540c0701158105411313440361036035011080180040f0101b02d140c0c80e40043e001594038019005207110b9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 193119361 1250 193118111 193118141
    0x12622050c3d0909110c01050c130302060d02090406150f36030803010602010b15030103030c02150903070608060117040c050112020f04141002030f090402071113 71
    0x280e5000c2d081142c0107480320042103000104a00d84035041815505660302800038544282001c0e66405040210f074590341807803048003030005082a00701c2c0240515500040410000351400341d0280080c0500c0b8100e01009224500003e115a80d46006070156003142e24004c02c02c01c0440e0303959814820842861034942e020407100700804064902030407810340404502c0c0c0e1110b80150a074840181c01c8081d41c1c2200d4440103814a001c000700d00250040e40c01ba1203103400010f0b414003501c08100804c1107011000d011684200018000251304c40310140d01154183e96102200030700d038044420a0082c03100302c1e901403041141c0080c1e1680d1154029002d01d0080c1c0780c28460410700b1b442a0103201c400c44000d40b40c10341100041003154480c14101030380220510006041c5080544032003160381c001d601c0b6140c550300940035014a0302c0d10300450795154405000035440c0444100d14a50741c4e00550442d02e100c0c40d400300760300050000503603206c0c2902c00000c200211001100700f034240100795115090700c0b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 193120611 1250 193119361 193119379
    0x609050f0a02030103050304030f05030d050103030e0f0603010807270c0c0215070b01050f0102071a0304120207060f05070206120403080115110a020f1f030e010506012622050c 77
    0x100c09410701c03c82c0d060360381000c0514906421900c59070a186c0307440d602121948001c201030800031240e0300c5028065842561042c034030301c20302d800704000901410700542c4900da08000410103070b20300150343c00c00c84803981440b46200c041c005042c4240840390b031018040c0b0b800d1000f07e4415950120b0400a01ca00c21980c0c0d807803180646840c400b450040c2a07000308008d282c0c40041c0218a4900c40300349007114144121041c0d592281c00c0c001340b010140e1310300004100f0120500c41002100d80070107160203044e00c000c201062920300c0040164200d1080d079000d000300010010150745883c002c49001460820b543e242034289032400401162003445012042d1064519158000f40319600c50301d500341d00b1034000c0c50000015000c01404000d0654010380c448154021500c201d040380000c83d10f196240d03100010030101005c0c1180c02d49034003c1c450b03070401c850701c000401500e500440c0310580c417003041c17890942c603920045e1000c0340310b110b401c0c1843c14140c815000030403c40c001030017141a08040d140070807 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 193121861 1250 193120611 193120621
    0x150c0f0f120a08270f031b010c0207060509030106090c020d020d02010501050a09181218090506131a060409060602010608010b06030417070b07080601110616030c030f0609050f 77
    0x1079501841d20300d5400a810800455440c020340c0c807811011860008100e20903a6201c501c140c940502020b40300020342021425245400756401c600d01c84100c504001c0c4202152601c0c000c0d1103600c1809002c00b80030010035644005c1d1401d60200024100c840010001101c10040103582e43c45059200801440350381c1c1e500b5019841801498102d54016041804c060300f082101405004100da40b20482103028881801003141c1c01c110751030308040c9845914101d0540f04149401b0512a0860410182400144a8140c940500c04294540b103014005124401c101100310306c021031303462195122202107004641c11400b0360104048680c00d800800c0f1096486e81c0e41401e03282c10792019a80302c0740034000500031403526100500c01403046c50044e40340c95110740d1800200002a102100064500400c002c06960800c000e40803005040d0000c140d43d2a00d040001000d1036a0f0707821504244c0c8071740440034018061b4000181e11202c1410901140c6e4403198140001c1c9000c035010300c404000c2c580410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 193123111 1250 193121861 193121893
    0x140d0c030806010311070f060203060a0807080a0320060103080c0106090b0306060d03052b060602030c0a02010e1503010312090608010f03020405070c0b0405060105040c030e0c150c0f0f 81
    0x40400303525485400c0740d541d4403001500202504820184240004c001d00e0000803443c1d01f02e960514403a81005031281864824001c403010160071100c4141c5c000c000522040000050746814941d261924a203103007080f103400d02c10900c10300e070038a810744101c00003c0100b0000750064101070707994030002c00045aa40d812130040c0d4010508194254104401081190410310b45c0d130b0284034000d003441071030801c0c13490324403c034000b1100c000300f5101c0c08001c00c02c1c0380c00114010f100090200d44011424040380c4800552544103001c4002e0601c05404101295a02d03245260002c120020410301e483e980d482c20110111100e48441c6400554410310120324503010b065014161644006100090b81c1182c0c01d000080c4405012807081c440c0101c20300e000182100980c43c0300f24441c2c0054141545840217100540350494807500c107250a0820203900c03250000740f08042c41100f1981d14501000724030031103201e44110303413101c2646e015101e003082800400003054103010305202c0445802c460404011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 193124361 1250 193123111 193123127
    0x5100801090c021911030a050303010f060e01090302181015120b010c1509030318050f010e06010b180a080f06070e0901030b0406020a18080703020120031c09020607140d 74
    0x20811544d11040d00b2000c00c084042034040250003030201c40b001022515010700c2e58100343c0c40003440144c00401804056400100c5942c0480c4c01e00b0003118490865002941081d04c4000c0401010b000e1000200c9251808010380e0041950340203610140124884c000d10f03503460a46640125800e110f031070300d40303544541d0b841101145c00c03003200070b0a01c0042a401c0050704140c50203400b0541c40c2c0610840c201a4004070700c0080d0710800040501c40e03d40b814240c00d440d0941d404501176003040c1d004004464540b402c0311001c4034112004013440100038001020302d0001d4100c4103061182d1040c4440c106070010b80381d0f009844a845180c100e40f00d05c1c0070420340322001d00008254989072800304000880503009400c0900c42030914081041c07100d800300c00c2c1030f081030744108401e0b80700748000c10a40d41c20145100340c2802e5903500c03c075210108800d459907031292040202218003441128010400c0c075070710542120f64018030860b6521094100307114040010f80d2408101e000340030004404500801d02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 193125611 1250 193124361 193124383
    0x2091302160314091507050f060c07150501050913050307150506130b0102030a030c031d031804060302060a1b0b090105040605010e090d03110904091a0603072301030605100801090c02 80
    0x82c0d00017a00c040c84007166070b00190021a9980320f0301c5a10007034548140b00f0300303104141c030054880c1c8600031418050480003000164150551a0000601890703c412064aa1000301b015046621f4040d92030018034600c141c4402408110958410140d43e0901342c200030300990003159415840004002c0c208122521a1202130140e1701c00c000e0641c0c0390f80203030402646131041d8180010400ac00d402000103240ca403001c158413641000503102e030004200c0d03210721812142a1070400c602c80c19603000c541d0922407611741c00e09100816201040d1179000300405201160311100029440c1000080540a010203071812a801c2d4285000810b941c450b081509105208000090002e210583d60640051041448800300b04c1d004100d180d03015121805000485403040c0a12000c0f02c140c1103c500d191000984090310a4100101c10455445e190004c05006468414645890200440180c009003001e903c081e400103026a26009181d801480c414101d5080040c188035440c02d5110490301c80c1c29801d2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 193126861 1250 193125611 193125619
    0x90e0a1a12030720100c02010809010908220b0c0c01020c090c09100e030a0f05060f010e0106030b0a0306060801050f011a0412061401081605040203010609090209130216031409 77
    0x42144c0d40c52204c0c490b85003c90100f1003844102c0400c0072050992454008203040140f04d00455a1210039564021245c074000c019400c0160f0321750940d4031518a00180b4505021b040c6104610600c5000f8020121910700c590740300c84c10f09825441700c103903403410340c054081c00c0301450141c10030101c07151040250040551400106008000302c907070003100032004002407820444000c0d01e00300300074a941401501c01030001c1805203029407500000408542d16803459200402004254041050646c0d985060214403070951001050f542d85499001805050500e0b80016807000c042d80032500030b600d481517141710343c2c0c0c0701c2e402e0882c00c14188107240c0358940100002c00c2010300304000140700a10a0710b0100d1803040c50200202c4821007a08248026082105401c03804441022150010724050f2010750070766140c140044d00a403403070311940c41a19000206c024841e603e44081a00804c1001c07001c54440740d07460841c8090031b95148080303003c203005003551422400d8a0301501e01c0b0b550300030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 193128111 1250 193126861 193126867
    0x905072105010e0a020a1416052a060c0a02090703020406021507020705040c120e0606030d0c0f02011b060c051b0115030f02060706020c0c09180c060307090e0a1a1203 73
    0x3412030001d51000382c6c0070040115050042e51040242c400402c1c010b02c4240d481e8070710001504000b0704040c07444100c050714940c80c842c091141c0d03540b076580c102140c0007201c440352245010301c082c9090030345440e00254041c14a0041068031509507000d001030f560395900700c0b40128004542c0c8903a0300340c25952440540c1c405842081149000d411101180c0881c1c9005246401c1601000c006e450569055070307299040041040002d040800803128507a20038540000c0e0310f40301e134440b54013130684000041e040141481240307013070180160341a0300041d4410700801100700300001c024640c0c0c0103214244010218460b808207845014060095241c502c1010000ca42d4503660b039070480c1011340c2d84c0480e000401440740d240884c500744090b02c3c1d80c1c2c0304440544aa8441e0004001001e440145803075280003c070303500b021050b1000251815003020075100c041e60317600c03042c809a9006121b0b81c481500001103604005103000b00da003000c484c02e4054003072803e0310b4410314100f01070180608045010744c1d00c28 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 193129361 1250 193128111 193128121
    0x5030403061b03150509310317040305040e0403031103040c08011d10050901150b040f06090e060d02060d06080f070501050403050616090b21010806131b0905072105010e 74
    0x1a0b40d0306c541044502c0130041c001c4000303114501540c0f000701c401b2006100854108030501d500000c1010a40921091440302868a507501500900650042c0040394000703500160405000761b021030071240c1c0c1c24076419101c2c43d00c1e00d0401550442030080b500c1c3d65003807400120a10b600d426041e0301d034040300c0c40034006102904221200800004188441a6417070700b030345402d203070b0310ba0030080301403d0141d58490382c59080000100c580480355000c142002210301003007240240139030b0700642200c401c0343d0810307030007072079000003491409903070705a401b140e1a000c000280030000180c10103260f0401d0007030b100782c07940d1000107495a00a03072001034165001440040d42c010382c5441c1010250419080848049031912107032095a000780041c14001c00440c0110051802c841060300e00520781c03403006200500e085200300714804d050303400060001071004064072400090398140000340c8901a0100b0141c9090740000305190400440d02d84815048002040900814060039050740e40400a10303d42d5225 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 193130611 1250 193129361 193129369
    0x1b08030c0c0f031903080103120503060f19030602040909060e01020921160f140d0201020304050118030b090303160c030c030806061902030417010504020d0803060d05030403061b031505 81
    0x890000c0b00d506000740c8400c1c15040d4186140600c80a02940d20380304198114034001c907030708103078903117a50502c0824410402c2c00e039600d10f10040030210a807100e40002c01c0490f400300c00d10744150801080d00b8000f0802064025070b0360b1045441c030b40a502c0c18000d42481150313840c01c0380718191400d42c02c800780510140c1e0100400113982d08000d50f900885039450904940d043c003810700ba8008541003850080100702982c10341d500c000218200300c0c1c91400200301070340042c1d5244500d2040750305000711050030b040c60340007290b0403800564108072041c0c032607d450201c03141c6a50003101d040c0a8034de0303003207014040f0a00c00c40142c0c3e441c0364103442d59400001c80340c0741a103240c032005000743d500c59000c0010980484100d040075254501c160000c41d240d50500010080c0c100c80503c610841d60715000401000d640d0300200181100c1e002000c49030340c4d807120804641c8c1031003400005041440001400402c204c60340c0d021001240307045017196960f502881d0200c058400d02d10242d04841c0c5001c03c180003504c0c1c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 193131861 1250 193130611 193130629
    0x2041107080a0903021002030a0215180a0b01030302070b12010303030b1201090f050613030509060705030c07030b010e0f06090f1519030b1b03040f0c0b071b08030c0c 73
    0x4905005400c200a5a5408059030710101c901030008408aa0410850404018281c131451890001e0b5090400348500259200c269955031079821404c4804110701d25800143c40281000e103000741c0e040c200700c81c01d00d0140b50f5420300c0304030014030404800184c00c0684406450503039019a5034041142d1960300c0c100c01408510000d10340c00201000c428080b01007d1080364007080c4501c0086100c0e0030641803807401c0500c02420311841001c0e4020000019612404944540900f26a195110001400c20516500825055140600c903620000c4180044194102c1c104c4900b0400302055560f81c803c5070a40e10802e44101d43c002c540d040100b10340201c2402440d9020340d41140c0601c18000540006000128142000301150b1180c5000d2040c042c015404a0b40007042800c0602500c0d40c03071082605511008002500d07400008202408111001c0701d05001005004101a01d8064030704200c56040850000381c40e0160a8210010341884044240c501c2c0b0319038503000c1c00b400d10040c4d0a03c0f14440e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 193133111 1250 193131861 193131881
    0x1e030c25050d05060402010306090b0d0b1005060a020609070501031b050d110f0715050103050d0c0507030b0a0b0f01091a09030a05030a0f110111040303030903030e010f0e1501030c030204 82
    0x11424060101e025210304030401c180d140120001e00c86410b103030001608540990700295806420080d1050072516145561101968440030414055691502d03034101030003c0c3d0091988a440040c84d4001c81e80d001a842c0e00500700700096a07107144d0b4400065040b203007440c203079030340100141182c1c06900e03000381c000d44000d4180e0b0b50f0115006088468162040e403000002c0521b201c00820032509001d00a6940c8911101984080009504580710320b50754141c5250002c040003494034150040101c20710442005542c07050700d0903824240070b1062005007025001140c061110a03066188540c469021041142e080f07070b4001c1440810710f07031910515407041c01d0442d058030a140c00300b40021002c0000701000c62823991440741d510003241000b08440600c0882d0741c0181e040c924516800c0e800d4a007103408070703685410300003a050041e01d0154060000d144c48c1c030000307510b003400103003501003079400220111002005450801c1381e201103450000c1008e001c0500350104482080c0018186540004101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 193134361 1250 193133111 193133173
    0x10f0509060c010609021908010e040803060d060f05060f04090b0606030903090a0815011a0a03020d0f140f0a0e07120602090607030c1a192007051e030c 67
    0x702c10106071990960f80c041e4800082d0b1540050708041c00844900780008000c3c142c900002c240d490110380407100c407809000a800c442001010620030b1340c55140c0740c615240d000c0e9092010550780c144c4030004180840b070f207500481c55130b0601050b0b8903051084850903580420802201e86070036050141e0794200603c00c401900c800c00c80c5da04140d0f2203001c8400149815002000340717086800f85003031501c1c41030b03006080140a188e500890800140c0c20b8a20075080c0f4500141c41755050190341002c1c01540800081e401c0c07401c011091a10181e000c82485604101001d051685554820b181143e213105c0916a00f504480c2060006124030000e031303051b0034020103000d402d01d4591000107039254000c0304201c0210343c10084031010445040e50380840320300440f019082c2403400701040541185450b0a0800703450387c0360000c18103842c207846000c002000150013140c55640d60b103041070751090740b0464040b400e40e0900d2400ca40050000484480b003200e00082e0000c80410290109810341d41c0c0942006 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 193135611 1250 193134361 193134367
    0x4031b091b021b0a090e030415030608030a14040909121106060a031704270c0305060109050423130201030e010e030a050c07050411040e10060815041803080609090c010f050906 77
    0xc0c5401b4056a40350492200103541e4076440d0240c031100144d00d070522801814140882044900008000e0320004074050511903a145841d1080c807440d48556000b2211180c076021040c03041c400e4041d080780701200c41c0c0d00c92403a24000301c010ad640d29003003162001e9020003080c505100103000715170401ca000c25034916150405489082d1800070041d9080126220807106052180c000881c0c0540005610702c0e0904001505040c00020701144c000e010b8180207540707400745c4105080302840754000780100b00c040300c0ea03d400c21603400301d81c280d10440240d000a0404032281600c4070103103d10304210207600b00842c03138040c41c44404e130342c6504002020200c501924200107016100c1d4040d0010380c1c1c0148041c19501c030300381304005c41d0303511004c1c0202380080498241031010540048049030803a09291035441034055450000740501b04c41c1e02100c2ca84206a001181019000a12140101e80480e014111607559103d403c0e5200040d0003600e000550710f940784051580954018074a070304c0098134540ca = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 193136861 1250 193135611 193135619
    0x904020408010b0102060f090303160c0b07030c0909021303121b150e030a0e0112020403051f0b0603040b04020f0d02030f150c0a02070312020304031b091b021b0a 71
    0x1240c000d035100014594455500040c00c2d0390500c200340c0d110211410b1480982004107039155a408010000c1500800880856040d80c0c001c00d2505411548608048114600f02303000801034000841014007261080c5400301c0d9001480c001e0b6075440c195440c03030100e500d00d1610707042c0703c1c801c500d4503074001d020042c81c1d9030000741543e4003440c04c03190240780d41d550102c03030a15883c0c0480e0600002c82455410500c4098200b65020700c502907054003d10b4843d40d04860484a0b40091003540c0c0014002d00c11110401c6220000c0b88411044030360a410030000864520144620b500c0216401402000310800050061400c0c000b03000c01c03c0343c050300d0818100d03040d5003ca031524007010b900300125030100039000c8029608892242d4440c005008640c2000da01c0c0305d0295075020303a40001801c508180c480914518420000d4a0083da0400001d4104400102c0c0b4020242e0321801860300da141003400302c444645d084d40550103a018240d00801c3d0000c40841d00030f0340d140c0075000e556804165010005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 193138111 1250 193136861 193136869
    0x20f0d06090c150210020702091b210a0b010c15110d09030507050c030f0304030321110c0f03041d090f01051e10060c03050a0e100c060c080f0c090609 66
    0x60050000701c9440340103c2d6401c000030f4540303103200011152060040140b4001a01c4010340190020400034810440c1085041d040c0290301502103a01034124555031603040160300741c0101070096a410800708024034021004403503080303d82c000a0005040010200c0c40120180d200e00180c15400510030305221942c00b0320710a923001c1134010340c00540301043c070f80c06021082c0a8200c140000310024100005d1480c091a117038061440042c050019a2000c50130b19290312096200300c00803d9030401c81500301d0398403031405410400000e1424800c5811158004000004407819117260150000070946031202c0e0448110008280791900d006801c1c140900000034012240204c01d0307074075051034068000303408003100365008054452090f18003000300905034001d01400c2c0313135070340500c1e090340d80b00d542420a49400d04c01c1b6200a400082c05040c5010243d40100340248045c46017505101c0d030f800110048843c000155000d0b142754490b440800d0303640a00c0d20003444080400b508980c205542d0100017 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 193139361 1250 193138111 193138133
    0x9150311040b0a1205190b0402070210020303011a031b09040b0406140f010504150c0201020a080c0a110303070c0603020c01060914070e030604050c01030c110a050c040e030403020f0d0609 82
    0x8040400c2010410004664010079600c01d0b1a84c1400c0410203071a00d84040d00a0f2890007100d0f01980303076120203100564456404035519603030094414451180d52400017952030b4400d00c500950851010300c80d0503041e00240449010b1010010b40078801004803070300c00d0241c1d0103800419401595900c5440c0c26840f10700880307005104000b0a400d80640b01d105002c40304400c00302c2203040202c200410301403c00c610300036555030340040c54404042c2c842440103030701c1c011860070090540c01c40807070400ca652a00144e1040b000d8402c050405034150b282050507528054a41d0007440580900c406000b118465400381600400c4071001003061951004120708640049504c29141d100c01c10401c5038607900a5811030b000c89056004180728601a102c07903440d40c0300010518101030700e40070300d0210140b00da04411030721203564050356107260083c98a1a9101c00c1c0c207903002c0c0240c5c00c194091050304404010748003101e401501c1d12180212550800003aa40031310001c45400382c0d500c11500210301040c080c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 193140611 1250 193139361 193139369
    0x9010603020406060f05220305060901020c01060906080a2a080109110901060504090b041103090d020c0f060d021303120908100b0d030c020f0603091f05070915031104 73
    0x164540c1180107200c20f4803002d400210900003000e01d010300d100c2d0b205048a4000200c860015054202107242525588099102a0062054809100b044e5206500a25840000c04020008665100c0144081d00c1c5a0300c03801980da0849034400002c9015040c00b140d19520480c0d1550a5001c0342c09018a40c1485030024803941c1e55800300d03041002444800700e800c0b22011a82200950b14003400200716100701e0040d280101d864168600c020341f9282c02c034054800019422507241c0c5810720f4080d54410b1880c128100502c1402082189410504004201018050034842c84c001c0441208006036100301042400907001ca0b40010120f503a282140e01c5a2006a5900a0003840c08003c0b5160414402e40078030f00c1c9240ca00f202025544101d1024081030741401c0c8030f0b080720243d0001580b0480340003602c075040310000081000c0107202003103881202250f00c0203148500310780c41480003256401c454080105400d24410f00102000b0600040c0c503804929002c40c46005105d118045a0801d40c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 193141861 1250 193140611 193140613
    0x50c0705030601060e0a0e1302012a0f111807030b0a080307060c090f0b0d0c1719110c0706230408010204050f010201091a060d0503120601020f0f06040308060a0e09 72
    0x88281954602140c620700103192101c1c00c47c02500302101629010340e0012002414040700200d0700300790f2109403200e00e4140a5401d18001d8800c0c0074100100002d03440c40d01110707800303155610b8820300c0c9800d1503a030050120240100186554495094000380a0142d80031b9000349503c0300001c0c41c0c582080249103683c411200883c2d0001c08460150031500d0740d0300092100c0c0707041001801449644815031700600c030b0050380802c80d4601340c60180d950281c0c480301012a0b940400810420f0400c0145040301036101100401410301e44001c0b201c094018000d401010381c11000c0c042080910035407091190f616076142a07200f00d000c1c64000c500d00d40c056400b94042c0c1e500070408020b00e24050720b221201072400c2c00240085003050360703400003581001e44490000f4400c000445d0664403104c2420310260f07800300840e0b9079440461340d06140b14404844580c018400e0034203540c00b14001243c526101a01c81e402400203450355542a150700300001c2045820004041c40025010124034031103001d005550 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 193143111 1250 193141861 193141877
    0x190e010908210f010e131a13051b011b08090918060c0304053c032a07030f0f02090103030c0c0b0a0e0103020c0c0a0f06081312050c070503060106 64
    0x70701d40c5140303200103000f2075000b100000101711030b5569000c03041e4400c03603010b070212140f11945000406001901c5c041060040500c00b0881d281380c0c01c078030b0100868051741c201c0b105841581e440b1451a000c091b10305000075a0442c030f6185103240c000c81d00c00060700c202c107401c2c1460303c00301c04180711050845101902015070312910100000500842d42c012640d008a14a140b80c1900c1d41660b0741592031141c05801c1c00c1e1010160315000705071455003d412a0610602100210701d04c4030fa07240c000e40a011420b9403100090100c8082d01c9011840b50702942005d448030354510381790304206d5200c00e18140c440c03800e0a0300b0040103039113003519103018611076110441c00c40400c0c20306100008040c0c01c0038441c2c160400001c441c96802c07403c1781801040928003d030b918402500c80c2070601140c000c00d02c0d0080c411810206505001005050540b0800e950391249556000600051008042c0001c0c01c40c1e40314450048000e84900000d0012540340c40840b1005a5603901003440c09009a1000740041c2110b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 193144361 1250 193143111 193143157
    0x111070b03071e03060308090112110301120b06100215071403040b0f0906040b01051002070801060602011b030b01140d0e0a05010506010e09010825080d120e06190e010908 75
    0x3c000c9048181d441494100500d03819661440000d1182482040c1400403a05411440320202e4012071042c0d40042e0529450303507542d8044180c904442001142c41110034000503075a4104606207a25680c0d0715402042880c844140610002001030301d40303001c1244c034100c64a04040e58400443c0994842d41a02c15036140007200744a00c01e001500c2105036410501c00e0001040b01d240149054810441e420400449450816031800e00a40d21100d142d5081030000605140c065000300d29018202c4204448640d1091049046450140e520b90101f640640c03200040072518014000c0c541c1900c0c1e0001d08500b94041451810b09291070450707150b07441d403082201c80d507400058001a62404c0d110a820741d41000d00c01c0e519540c2c11914103801d886621840301c401168606440b006001c0d40d000e4448103820640020100c40004000401440c2002080b00c8001d800042507440b034074400c90a80004601ca641280180503004002d805642d2102141030101b5051401881180790528030105035a041c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 193145611 1250 193144361 193144397
    0x501050f0c25090b01090e06120109050d02010c1701090c0509030307110f0402090f0420041409010b0f16030210060b0304061404050a2a1404060f0f050111070b0307 72
    0x11070740107000003a0600c1c0145100d66001b10000c4281c810031383c1840100d90307e080200700b0306110850101c801d982014501814890045590601404107900902504034050000d0f142850349141c0a00302ca01c0c0c40004101603111a8403200c51903516107840e601e81440503000a203036410044082c0c1d0700d001c200360781301410324190300c02041400064400b0360070017a418000503500c025425411f0b008a40703601c083c008099a00020550344010700c5907041d201d517141c8c14014950320440d94100d000780c48210010074010892410780d69102d050700c00301c0d4070342440406c09090400410f0302c00c0f008d61041a90b494502038540c00344030040e00054062a48910301030030301134162401490601860f5441c117052001042c0040341c071450740c03904012020b07582090f2003060002c002c0b54a00c110000f00d0000710103d0588141c0ca048141341004690500081780c60b0007a68480103018401c4c9041c0e055001d40400240d4040d00b800301c04804d90344242c0d01030307965850240545070b0088803600e0002d11070410b51a50080c2c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 193146861 1250 193145611 193145683
    0x21314030c22060f1502011506020307060504020d02040e15010b03060a140f040f0e060604020703020a02011d04050a02030402040c03050f060f060c060a0e07080c0612090c0d030e040e010908040501050f0c 89
    0x62300102c2540543e2034032002075141d02c034000c800313046543c95800180564a911011210555010304200040c070b190254440d1035006541080d034600f20403000014030780c0c92803c240ea02800004100b44030091400d50040c91100f20340f81142d4011104110451507076650744900ca05140e40c0d400c4c003080c500038440405081140092002d80705610500072440420340c0000c0c8002c07032546c207092030b4000c1501044030404072442a2886a4003508200c10001860200e8000d10f028500c25038040c06118044481601074620445000c0c1052400c28001800740c0b507c47c10384285143d000e003440e8a081038158525080100031503004038416201c5c3c4511441c400308200240007095044050956084003a001a8051041f04040c1c42654060340225007102c070140300505000c500201498101c900900c2d000c0c018486046485200f14070b481420401d4000c180076030005950b00285882c40c7c14109001076406400503480301c1c00804e424800e0680c0b9510801410700e09916028050251002c3d41c620103101c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 193148111 1250 193146861 193146881
    0xc0a02040932251203020d0801120b0f06010e090a060f170d030f0f02070302010c0909060501090519120b040605070f0e130b04021314030c22060f150201 67
    0x42c420b4020b103101c074008101d03403a2000c0040d40780004003900005070541c020340c3c1d41085000b16400d910a004246e0000340c104036954480e210b60402c2c0c0e80e50903e51031284801302c0003500345110600060001151000640d80c401d80c1418803040c2a07801d50041b8a601104650050703006648141c280302c001e40f03040205004101e48020070082d10000170341c0035220700381c0501d0b900074540c40301e10b602117001c000c0d000300406040000301152145d00c0d900f40280038011101c44080818428100800d85070282e026040a488060b1a0b100455140800b40300386100700c0c0c8031140c15801d0542c4041040000480304c200d8060240115540c641020304200e811590013910b2041405a0b41203100c010a403c095600030360346007140c914241a1440b0038903c007908008100c258010b1001520080110902d150b0605031a90f401c45c40d030035002c5c1281410350b1050b80407c4294000d032101407101c0700194160090401030585400840c0c056650064510415002d82004100380854810a01d495034244034040500c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 193149361 1250 193148111 193148183
    0x708010e0d082508071206120b10050319050c030307020f09060102010e0d09031509030e060c0106050607030309050f0106032f0306100e0f070905060c0a020409 70
    0x98180394010655458000034808180b0900000003511644254111489800e40c107a000101d1404114018101d4504403110320115043e00e000010340c066500c030f14819121419115411080390f62104541080002c10b0081c819410301c10200e01c5481c14080303580c0804012820b1001f00000d4900b0600f440e00f140c19030703406940300348070f02d02c0503a40c0c00e01500c04102c1e00340c410b64403a4031030b000102e02501d504c400f404110311070f682c4d41d2560254420a200216030041e05a45208070010345410203171842c501001d00003442c2800c0d6408240f170311800420010f503850380000307207440c0c1d00c8000c5042c54000031400c0d000300f0390301c00046c01400002d02403800340e490040020000d0031f0455a0707100161040344002540b0403005006422516804241007614141c000c01f21040d41c940814221050103080c01000825180040800c0b200150301d145580201c44d1502c44008250401d401c0c001e0a400000405e80c1030721441d150400540c03580d1044c0c2c0c621a00402181081c20b000c000b0b500c034605601b403101c42c0c0c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 193150611 1250 193149361 193149371
    0x20a0e060603061002010b091f0603020f0d020a2102030f010b0a4401090c1805040c0302160f140304050609060d060b030c18120d08040503040f080f070801 68
    0x10580d1007030110303640060111003049901c01418412401080d040280ca50401c1e00300051048110000086071820135003001141c0070359403a07000c00c03002ea0141440900501c0418442c00010041a801401c4030842d289010f0304c2003a28503000c1e5000f0b461034001020101e0b800004d010391084014000340c098100001d00b18074003014920020a021100b10035481105940c00d042281c00f034010050341450b030641c006801031010305600515041a0a106481d00645001c039208a654090166248001c6401402c10f055034500402d00001e00130100d9a07070b00301542008100d00201406c00b40d00c0d4440d000303421915550041d89094219109440110a03040d0710500041000ba61007904480d4490b00580b400c50720307103198101c244050555500708001c0c08001004104203811a90054074100d40c040450000c0c0c248160240b00c0f2102e1103030000c0015030445600b030902c1501820b0707940e0300180f0500880340751075501c00d0290070146841d00054542e8000028503100342c0350801105000e80015802000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 193151861 1250 193150611 193150621
    0x50d1a060304020f0a0b0d0b040b0321030907030b070815091902070203030c01090813090c121d1b03010f0213030b07030f090602120708010302062b020d0603020a0e 72
    0x940340c000144000d200c2c5140c0c8900010a407244612040145150064281c0780e040107200000903000303111606015524001075400c40d4540081c8540307100c500b500920032228404106070480c1d900c018031307854880c0b24411f40040040c41034680d240c8a007071341d81d8880140b405d2854504032043d000c0491984544074403001e121814a80408003a200380c0b0741400182d1ba200c0c82c3c408207045000d1105a444594640300350301b0140b0154a00a2903a81410b0200040c030750740756180d41781111040552180000e040ca2900800b24126500a60103070050350700e09001601d40400c2146000340200c0031302c008003294030140e5070b5402c3c240280c07861948480700543c28407c41c50001c0d121440d9a20015000c00013940100e40b040340aa8007140c8121898030043c0001d442904004020b50b004841c52454400080002891903110703090384c0b410b0b070b94024a10351400d196000d00d820b8200c00844081c0740240140e01e0200414114030081c4a5081e0954000c60349600e103004220300e1075110361107441170400d03100400c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 193153111 1250 193151861 193151869
    0x11106010b1b0a0f0b01030201091a1903090507060e0a061407021009090c031401080d020a080a1103040e09060906042609041d06060d0503030f060d020d03050d1a 71
    0x1950540801000c241034002e99068907140034204800902a88208500c40091100f04044141628000e0304c541d00b4042c0d44680031068080d010660b44032202d0144140c15800a110701c404524500da0b18000c58440c102d40c0300c00d400c121643d40508003080c85004100a07606210b20304e00d00410041c202204941b0343c80d086924070388619a002440f81d15921508903040f070066540c1000f4003030400f030030008403600c000041d000301000c074202c640408603a8000143c11200142c0c1c004c3c11041c0354003800c0044125a80d1491030b81048505d602130198000300c0d0340b01488108098002003038184190191401c280707003120b003801c1c0094001715103504030742c0400002ca18011005001440c0c00d071010b00441d01a038011003a1805010500781d8011b04195050709a68200241090041910b109136052621200c041250341c05840100a100360802d0002401410041010550000021f0185805a5040d81c00078180c085018012804903c01185c030b0444640765200e108070744c03d440d541e001c02840e010300c006 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 193154361 1250 193153111 193153117
    0x20a02070e061503010602060a0f05010b0a110f0f0a0b0a0c050f030c0d050405010902040f06060e150403050607080907060219140c04020f0705010f06050904030f03110d0902011106010b 81
    0x10806a54080002c68102c0d00d450010002e0101d100380b201c0d4480d41c4650009444800035200c0d8807400c3c0c20150402400041d52040d0b0b4104c680c20700c143e618003800024150380b850301c03541540c02c0e1401041e0001c20464030600200c110070001d0b0010b056003882c07900d007020703d5240141000060a1a03d808040020380103c210b48441c0404c503829a100d03a5400c0520095115901031041d0542c206400d1104203c8150425030946d8421075061240310385070340b480c2007107031650310a050002c0d00110907054075003040480440141d008100241c034141c2c0300c1e01c031645440019902440010624000c02a244c8001c0c40a1409007013140302a085a41035030305400e54004102e50050400b070906090304000381402c10500405100141066488614403d02881c00340c200307480c1610743d9400c2015000340c680740b80c03141d0b80039110010b098050315100c60b2002c07034135180107100b00300c03d1664a514040d002900500503142c146107004000c10101464800100300c0d840300f500400440d401100140000c3c5905419 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 193155611 1250 193154361 193154369
    0xe0a0b06042d060e09042909010f1a0126040b180102040311040b0d0c080607020c0904120806010903080d0203010302310c0909060b0a032403080d0e030a02100f020a0207 74
    0xc00b02c040c0d162411f040011008000401048088003a00500002552a441c83c031030b611110080000069101510f0292040c0750703140c0d00120308904d015509580110980c0150030726841004100c40c0034400420700ca6a4251019200c3d1038803001004101502c4454110080400b10025030515145980c0c0400002030201352510880e00c070031050340191110b40d08803607629080219081071035511070700341d912210203503642d00043c01112030002e0301e4140008554042c1d54020707690700061032443e0003200d48400207030040b0704014041e0f0b00000440d032104060003100c018a00c0040e900e5146104003c40100c002c81d1a81201000f00e4400445100c060081031424400c102c010400084038881114800b840350402c480144c6460030108055100d04050401e4032501e4908002c0300d031921100c100324a201c03420b20a1100384503d000d1000402048c041c20b4208800c407004100000c00107103880c00d54010740c5541d00140d021000955090030315002c3d540300c1c1a42c00504620b4400d496500039110441805 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 193156861 1250 193155611 193155619
    0xb0906030a0f020a0f0806100c060c0314010303030c020c0117150406050d03050301170a020d060b01140a030c02010b0108221b030f0b0c130e0a0b06042d060e 69
    0x7000c02840760400c00000b19908402c65941e20700c550080c0545400c906840c1c00111210b000542c80e00700314804500444a40d02d80c44000f9400c0d40e540d0300580800030f036010030161500415040c0c05100302c82c5901852094070045442091300382d000b450039001c4040316041000041c9000340d03184c035140c0d404d41c02c02060f40c02616545c44282c082005480c3e280d0040c0c6d04945480e01440906a0040103541614128101c5891401c0c00000c219581e410702a07000c0d5106800c401403000042c41a80702c10000c91060608510014030240c2140d12500001c0c041004031343c50b424041c85082d420b100da40c4003c4c4090a140010382400240c070040d0594500042c40c4840024150300244061058100d5004458003154241a902e9180c4032002c400903960803965403200d400030840390041a0309844100c80801d1410b014a40740180251518170003030204480036030b0b00c50a201071500c0c1c09004201816400d05410078807001024a040c4007044c4503400140010039540038490f041e4000303c450a0310004403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 193158111 1250 193156861 193156867
    0x5070314130f02090a02120105060403022206080d030504062f0a09030b090f12070809010e06070b040804320f220618021201050108091e030d150b0906 66
    0x32070b0450b10380504801c065400181c982c204003142eaa680c0040188401c48028815140d98580034040306008074000250720490b1002c10b0400d24070a0344da0084154070610006c03031460742c1c907103200342052b0840e0000e00c0041d441d4410001030288071b00445521482148003d14020203003021013002d103901524440e00140c001031005003162080100710051030700081405030505059500c29034803e0696140e4006004848204000038425019101c050741c00c0103078103203031807034550044890030103800690798444c40900c003402c04103c4031000f09115174801c40358903a58a0400e000f101c1498681c40c030002d020f104d0454900c206000c5130b09003620308c01040e42c90f5001002c4600c0002e078800408840e010792095444415400b2480350f402c4803084842c00c07218a504c110004045c4c4040c1d101d004025208002004010001c9512490501d54889920020b641151041100c071020b60300000c0c082d01030b6a0f101040802e81a10789104001080c00389014462080d850b10b00042d42d1806016071480c8141808 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 193159361 1250 193158111 193158113
    0xe060a090f060b04120501050106080c03041205270f060406020703140120040501030b0612180f07060c020f0901031e030e1336021309021f02010507031413 68
    0x1070700807101400c403c0c00007640f91504d42d1030902850041c1182590151b003002c000207800f0b8005c1001b075000710b94018499240d542c130b9440700e0320845102c1c50000d0030003804014100410075080116040d58030701c48620850010682c040040318090907101c42c1c480e4408000800c10643c00150803012240d0114205420269a40c2894018001c03c2c0c25048036031909004421106805001401510400d803000c2120310341da0814040d483c020154203081c800d500001182d12030481c0e00e910408105000101c0c0c40300302c401950941450b03240c1e031109001c540504001e900318030780303d20111f807128010360f1148001e61543e122154100450402e5400c000341c1c40943c8801e241c82074070152070380e10300600000301045141c0c3d00070001b03220904880001c40094490b41480054020300311090810540360144216130740d400f04046094011040509940c1d034410440060315001d1942e49a503610140540b480c200b4044c001e803e5900c000d022008151804c000700090882d10340d40aa08440c032000320420113502 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 193160611 1250 193159361 193159391
    0xc0d030804050c12030c0706080114060702030a060e03070501050f071e02070506270d150f0b09010e0106110304080d0f030e010e0c010216050901060c0f080706150e060a09 75
    0x2404002e9038100013104007901010700000000c0142c52100412104543e43d212000c0714424803c2c05142d0691407548a0780d052031800501601e41940001c080d03400703401c41036407030710225101c2d0503c0da1080d42001c00c0880c02d00ca028451290301010801000e605481c004030020260100591008403940360a55460480d610030000140984000350103281d80d4a0b00c4815181190940c01c5903001c460f03010f1b014402d20b0b090124444001950000b0001c01032818008044040c20890485080940c0d603005185c00c699200e0504900070006132080c12825414100001c000881c0080c02c80e00035441080204808803000071108241c082a1501400c43c603191101180038180c41c5101800ea90b08180010050400100c0c02c860383d000240c00301c0f80c0700c5051112005840c8007030710906c2d90109001c0c004109442c0540c0344020101d10509140000140329504c001803038020803819284640e9548444184aa5001c205000340410b4044210b0134030780a400103035250500e0103a0f8a13800d8075108042d8034110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 193161861 1250 193160611 193160623
    0x203070c0b0a0b09131a06030c0d060e0705120705041802030604062c1009050a02030f06010906090501030b0601110102090307080c040c0302030c04120507050603270c0d03080405 78
    0x1500070400700340c07814050551070107002c201c1c4050348036440b12004544030309804c9504481c01c80c3d00c2081d21000c2d10801048110a40009003060f4140c01071241c0d128066803840b0301c600741c03284945000110102c00413101d600d0103040380c101c10300984030448090454000003551b0800c0b60360840e400700c0e5442c100c0c024814501102680250144981c2080c842000119048180941d10070003102c140307000a0008031500325050741054505802550a4145601c505d800091003d03000314211141c03a0b00c180d001c6031034410071402c0c19001d50005001408060b500740070b000010700c90004180517035411a12a0704261201600f2030b818021110384400c0081000e4064541c42034005003038980c07890b0303140c40c0750b9240c61003100e035144a00c2c038051901b12054000d10075a80500028002581000d0410540e072440d1280341c4c0040d11988180c0000088139940c1500441c8152840c000c44c0300314017050440498190b0404110010710b400c001030360345807515400544c0e90426018900802c0b41e0321103007130a5003890 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 193163111 1250 193161861 193161863
    0x160b0a0e0607050c010e0301051302010305100308040e010810020f2b06170c0a0608010303050f13090e0d030912050f0f030403030e06010905010e04080a031503051b1e040203070c 78
    0x10300c04503025040c020f001c10f40d060450f40a880b00200c1040a40400d0f08854045400d40100030024500f00003552007a8840d5a00403540101207850036182e4135214016045540000c0b02c03140e80000500846c48144207181001161035002d506240b0035561fa903003203003d81d49403152201424022005103550000d5100502c802c90b14040042507214403602c2d0710442114200300c880d224100c0e20302e965041004548045035100c0d500c0141907400c542c0c0c203d50503808000c0d0070f042510144503030040114010084001424030755000180301c211a0b144504020702c1c16018814949400c2082c00030810040c0b0044080d502c2d49022580c5180501a00e00c207030180c03107070030200c0d2180030041000b010b801d07a100103c2c441d141000c41e0f03403980e40da1142c2c10a4850074066001c82160400200d4006038100b80030b00090403240c100442c48207864900c0740c40d111800e40c016185035004080c41250158002c08524101c0426217500d6a4030b803d00031420b002e285010411402903500100045617180b0800703101e10346c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 193164361 1250 193163111 193163119
    0x110a051e16081018020a14120d02070611031306080604020705060406020703090f061202090d20010f0e030a0219030206030a020403120503070215040318030b1008160b0a0e 75
    0x7251074400d101d40d24005029075442d0f16280c00002d01035050030840d210600355000b800300c07201a051400e0f03200760f104c0080c0c1340e50700400b00c00145500341000b0320480740d05a107281c0c001c0c60725500d01280180b00c0703440d9580021190308200703c1f0a0848a49103000425250613040c00c400c00c1c0c4801002c5002807140d80e001030218010b810070b01c010401c0075001001510f000b59900000213403640c244100d400340314452600850080030006001828540242c007801d500141030f50603a91803500d80117440c103003d20065005040c24590120350b91b0700480c1c040d40c004440e00d031018040b072a01c40800e070f82c0c03030500c0e0003e48500c0310710b901e548902001501410165a002d4403054481c20712500d0040070f5003040c00200c8140c0c45500d61154624410001d5910494007070b4010240b0340c6601c0200f03454440007600c180d00b0042c41d45640c0140104581d4180c0c002d520400d6104d400307240c26809040d01c030081d0b40005250b074004102c0c0c0c0410310312040030344003a584a81e06440d40e91101081c184c07000c620b8840c1c05500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 193165467 1106 193164361 193164403
    0xd0f080a05061f051e13030b06040f020a020a0303060501050306010e09040609021203090a05120c061315050417150a021e160201110a051e 61
    0x1040001c0d201080483c10b0080480c2c16010b4a980c0d1070209500041c401c10000200140550a4a0005a882c2803001c0c03280ca828601119100c058006801500070074413035580e542c0a00752041542100710f5a8042d040c0010352920f004507003c0d400320f0700d002070009080d40904201c07481118160b64807000c1da61044104070511001810684910b940c405544005031103030590440d016200800460300c42c0950820070075900d10581009010b070700000c110700e50060b030010b00c0407102c07801143d44a032641c40740451100c440082c0d03800415003110b120b4031000c070036800c00020403d980c207200c0c40d888070210940c00a6681d074200740d103005071103401d0000102c0c0d0010b15400381c9810000000504000f080c1c0e6144400c16400c03000d40040e5090310100c000c4215038100344c0f60f8080146280140c030050301d4a444140d151180302d810060900144c041d120800c0700b092207c84002c850343c0d105070700703 = true := by decide +kernel

theorem cover : BRFrame.Cov 192985611 193165467 := by
  have h0 := BRFrame.cov_init 192985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 192985611 ≤ n) (h2 : n < 193165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
