-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1758
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:34:21.334118+00:00
-- url     : https://prove2.me/submissions/36cc64dc-1321-4f61-b272-4e6a195b8559

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 316007194 ≤ n < 316187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 316008444 1250 316007194 316007201
    0x90106021e0a0302030f0d0e070f0314010605090615040b0a050c06070c03050306370602010b040b211f0c030b010e0d1106071406090f0a0f17041503 65
    0x16040140903075a0035060074000001038400003030364164007075420407101080003012904040c07480c0c80b02c036440c0c840c0000030b2401000024000c0880c0320601400920b141011514207140d030407010a02c2e41007030414000c540316100b05035000681581c07000100f0705483c142c1280b5025540004035000d130300251180138154018050700c1c100d0280010b4a460f81c6845200b92454502c861005011030018400140246000d100792460300c084c005070703c011001311036848080e039402035020724940407245000388000303982403266044101013a81c08010002d40784001a0a10101000403100402c4180c0f4003170014100380004480741040c02059006103240e40c0e0407030007030710903114810b0029140402b02001e0758403501002c58040409407000110565a03250034241c5403885018541181c03007003041c00300090142c44180c00c80c41c003a0b07000d4110360800b50100c41c1840703419142030160354050922000400c09655440d80c403640d20403c1e10040c1c3d03a42c0c02d54000640071355406446c400f0f4203140404246034142c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 316009694 1250 316008444 316008463
    0x501141005120604180b070c1209050a0510030b030a0c03063207210f060807030b0106050d0b0a06050a03060603060b0f0f070209180f0a0b06090a0b09010602 69
    0x168004116503554030111168010002030100721a00c0202003031050070701c0c0e8170803428424101903100301c455440c1c680355290304003600c00c880005c40100c2e600d030602c00d0741a091145c002040c43d0600b1558604400103140c2a01405a54440d59601302c0d1565294020b5012101c071000180071394084000508000340da8100610050380c1860501440c444140c01e41002050300700098907003043d800d2038194100746507100c02400301050208441960f601070700440c04590f091030110303c0c0440d680740400c201c0400d0394141d81c842e0309150700240041c000242c00341e070b003141941c10f01c0c0382c03260301d4100d0030000401801d0b01440c0305420042000000c03c2c0680d00000401c945481500c042c4141959210700f14100c0e9854032560a00a80900c04a030143d51703848002c000c44d528104443c2d04001003500042d07500d4400343d0f9146140640c50a41b100c241d6000e10800e070b03440e442d510151440001d039460701e010700200100240d20501c06400014140507860388091010100074002010541c0c403040083e6139003e01c0c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 316010944 1250 316009694 316009699
    0x31f0b0916020f0d050403031b050601170f01021e0a14030403050a021522110909010204030507090911040c051c050a0b1504090c09030501090305031e0609041103070306050114 77
    0x4881e20003d040c00014240500c40c169a1a50b00d8580342d83c90440300c10a04491018142c0e00c054040c0740031603400c020329406050340907980c0f026900460b0f045071900800c1c405200884c1d0041c003180301d000c0500010820f0b00d00b100d05140d6564840a4811610311080d00c8100030041004030503c02419032180251048206a4084440c40c111001c51111200b200f150940400d0001083c0041c2c22030b500404111524480c40c00482c5000301840010541a000c1713440d000300f80e501190400c203010b0100001340c010404041e040107009429107a18150b8080030b0001c0e4001c903201d11a800b011445582210702d001c0b5401c039805480809034400c0300140c0410b0b0f4078440114240520160b080c0303843c0e440c1030301d07102820b1049858680381000510107440499100d00902503406400404203c087c010245042d04c45d0340c07032039640d240c030321400c000c0d5241307104001313041c0120318007048007689030b0500d1190426004800d4200d04890600001e28005094000030416401e14000207200384001640e2031164504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 316012194 1250 316010944 316010953
    0x30619120210021c0f0e04110c01050606031b07020d0f1b050a0b18030a02030d05070516031a060619090f0e040b01120606271406031f0b091602 63
    0x1150b4007280d0f140c1c00c2400201c3d4222090007540502d500030780c0380c0c0d8010f511604207810001a5440040c040301c0390040200795441300001c41c0f00400708284150303981314808540d00e60441c24486d2000c034419180c1c3d04003e0039504006113100540d65961039181120707a02c2002501080e246180480501c941c03000c091b10a02c1d08640f0204d00751a00f0251901590421034a0038204454001d20481d013900010640790940a00030032040588c0381070000d400408000d448007941c400440c0307071252501b42c2c0c405070030001003591541480003e40e40c209200e041495103008800300c0c7c90300d100040003442b0703040491381500800d0040d500c500390444200c5049070101c0020f40b0703016a0310b03040c0d05030580086070001c018180680044c05402d00d0f280301070007114052072000440940320000c0301d021080c072441c20112130b041c1d070004030984c2c09a402030000200000b619032106052500110360f4903407400700c0c403ca264900042e415441c07007080c0e002907a580c0c8000c290860506040b4400320010f850002004c005019 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 316013444 1250 316012194 316012219
    0x103060f050709141e0a12110301020415030f1e06180e0304030f05210c0d032f1c0c081f180e06090c0f03060402030c060306191202 58
    0x1d00607a1040b101303e02444648640003000b081400c403214898151459814041080300b5202c203401c80c0003900c0d1803802020070041d5070901d201102d070300c2800781d032290380100300900209562400703010f1600800d04010030032005200000016100040480101a03150b0000001d0f0076540d401100848080e03106040400918030364841c00c2c0d416409001c0d4095004000400008506c041c079040040d0080d070540f0a075003660050304072002020140d14061840128844502c5c60341880305034503c2489050400c40d19a4600b02c0000000389070b030198441900020302e03010324003004011a40391958400da902d00000c0324400040003056031507120310008020400183c00100d4000c0c04004559000c074007080e0a52410050140c0314200d00d5400300035a88851991780c984400300105c1e400b41c4072260161a0592041013401007031105001030390302c07a5008800344000342c0c8000c20440c4c5205019903007280c0d65907a400100d4840c411740c805030110319141890015010041c3d90440c1c0180f4401c0b500b80300c5446 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 316014694 1250 316013444 316013447
    0x4150c03150f0b03011203020304080604110f0609030d03020a030b04060b0a0324030b06121605010206100609090507030902130203040605060d11101107080619020c10180204050103060f0507 83
    0x84107070003603000c010f80810060000d80300c01103443e04441d100744100c900c3c180d16003020600f84201aa000c4070324400b0008104050700d041f2001301d0003000c00b44c48207400c3c01844070000355a085410010300525600044e0401440e100303404c90084584007078414004079540d8000c003840e5034404059a80028600180242040402d0103403502c003d2254140082090842d100c0036990b031005055958440d510508001044000b4032a0a83c0380015401114001d4544000642042c100074144078210071020070502880741c10407030340c106a0300302d20f1002955a880b001c00f17070010007801c0006035004000700029020702040341c0040d80302d1803140400344034030b80725a018800142c00d00400107002400c80c82c803002c2a810301e4030010300c1c0c040340c0380381c0f03442559100b5030032908101d495004030501e60480380030810526a5400e8980b1000303d40345045140840781c0f010079407034802c1500040d6006440b40c040d12108012130f1100c04110760010310410455940e131500710014200c0d950013500c1c05041400054859 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 316015944 1250 316014694 316014719
    0x4060b01020f070b0a170f06032104172103011e06080601030207020a0e150f060c12130b0d02030711060405070501030f02162d02060d0504150c0315 65
    0x2200210001c00f189402c21000e0402500040c002e00200302e07190f03081c42128100e40d0341c124029901005c101c205410410241400c140c0e0801c207500c000309040400c1c2c1084040d00007110100c58003040c1c2140d061784c800d600c00b800d003d510310001c0b13200340c01c400144103400394490003541201c080c11986100d82c54542640c65200c0c40510a0340c003c01c2c1280d0000300c1d00e5000760001d05100744028000150140c545445001004003074451220a090b005601501814454605c00850f40d0854201e418080040707100390341c5516800c0000b4414030b002c100d115036805106140c1014200c203402c42c0c2c1d11031400310500c40094104541c4140029450240243d83c540c0115455010395000406491024188401035001e1310f0441007040e030159003040102c46a9120005d6542c3c1e69102d080d003046141500180b03988400da40081c0008451250402013005940ea40210358640618250c08641a03031282010f81e20007010010f80c1112500f003100100c8213590680c070510540e88890301d00326040361240700e00c0b50340c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 316017194 1250 316015944 316015963
    0xd0c080f01030b071b0f030302030106030f090804091e020406020a030e0420031b0f030f18060f07030e0d0206010306061a040311031609051b0c0a030c1b060804060b0102 74
    0x80074032607004500420311818100d480d411050007a440b44170072a41e41c146881c8029035050b00020382c044010700c0010ba04d8090350420780407000c0c081c420049981c40300c2100344a40d100d2012003540e100c541c00c00070b032042c000d60740341d01e50490b401315102d40e51100042c4d11621513990440c0003031003000c010892498944140e0320701201445440170080c083d0301c040b5126034400f8002c0d0b66000e40042d0b45210715428040182480d15225440e0f03502ca00341451840004400a001031001d00c004d030303181590b0041c0c0052810b0340f003201c0003a080310507103071504240e0080c000018031424030700070f496028950a400266090403030340318941c100140c0380e0f04c022665500d480e520500845daa410030040010828104a9454104d0010165084403202c16048296440c0b0340e8400440562904100310348034050280350058a21960751403842c007a014166103440b005c80352030003000c0c0000003032810b081c07040459000024040c0f10341003090080d2522001351101d4400c440486085003007480b80800c9520102d00d0384103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 316018444 1250 316017194 316017203
    0x5040e01060e0a1b0c1a180a0606362d09020907020f0714040219180609060e010c1103011112060d020a0e0414030a030b0f0301050415110d020d0c080f0103 68
    0x100d040c041040c0c40701e040800381c0904499042e01f10005140501404000c99440c13203100c001902c1880c5c442d0050a03000c142c4a4200382d0f40419024844c01c2040905000c80c0800707104000808080c820203601000c2e5a00c1c10004030b500200039520742e0242e042c0c2c000c0180700c0c0201c462201c4d5030381d40c070f1040fa07856a114111689640000508011304620441c05c043d0810000b4009820b02011980c800c2444038038990100014000c0720480c1408003001c1d48800180c0586e01c0d000d40b02030b00301400901742e1481600f6172810030040d00c0c00b21041c0320003110600b21043c8008c00134032084110030492041908a141012101100b0700c0224101d490000307040c4600c0c40d4007a140b0702d0040e180004e940c8004400a00035548200c0c1c070306203007085450620040440c4102c94500040482e210420320048088101d030f014060380c944030a01c808030308001c1c0300c0840b0031604600414000c2913a0078940e882d0013442c0500052600100d2480b01d071401e10f070800196420140c3d51001c1e41d9840c0001000280802c0c4000792 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 316019694 1250 316018444 316018463
    0x120506030309120a02060703020606010f05030c1204060f09030503060a140f0d030c0c0f0f150806210604081206010801031e03140d09170702010905040e01060e0a1b0c 73
    0x140e06042243c1d411151158003c2640c2510b0f0050700483c1007a40302c03000840058102d801000510b40e08410031151030f1200b450134a0944c41c11117440303040c5210b17414100042d120a0740000b401c002c01900048000010000c09015865035458040c18039001500c120303102e240540c1010500454020002c1c1507603038001c1401c1804070300c55040c0f02c207a84c44003800381e041111016406021403000c01d03032800102080305403400e8051508480f01100b11123500094084d22170381c10341c00c121580c0096100c3d0080340443e120400819601d0f01c40c81c582c000c2400c0c050b0540100010403050107203000181a140007404001646030380c0740c03001152001000d00008016000054031400c030030b1040c0d00c1ea6510507203e424848001c80030240ba02031a5002142c0600f1903d8603200f1140070800743ca2100c08000001c51400e904100050340041d0540d4003a000d11805560348140c44030685000f5040140109030039120403149007060703120040a00070031000c032441b500c600784c40c03c0c03c00e511912102c8001c54014a100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 316020944 1250 316019694 316019707
    0xd020904020609040e120403050c04091a07120c020106090c0c2301020f030c03040219050a050111070e16180b030c160803091501050a1a0319020403030806011205060303 74
    0x110320350b00089030003a0405c0c1e8480071201d0b40b110400022016000c907084041e11140765140c00c0d440e08120480646c016810b182c100d80c000307034030740e01c116440705800000b8200554403194200e4017950052904061541020036107807041c0d406511400603295000703010710020708c0f6640251002282644014109103200340c2041a031043e050001074001610000540703000030741c15082c001a007095070701480880e0000300340000c51600340f506500042e4014203000d2224a81b0300010800b41d800d100e13260504c0030f00480554181010701c010702c041c15100c284c4e040c107030070500c81040d00c0c544401881e03170110b80c100b050301d42c1008099890302c080b541d070520301900d076a0341c02c02d1055403504809603648041944070b1104000400d908041c61043d091380c0020906000c0541d0613118144060744124045d80c0350710800d02401c902c441c1c00e545040c035002c0b542ca81c0c81d03c442c0500c1100b1541c80e0441c008062010ad03000c020507074490f11040c0904002d98500010303521200e074400c12a04140d13840e55056200300900d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 316022194 1250 316020944 316020949
    0x2e0303081603020409050a02040509091f0b060903010908090a091104030f030507050604060516030b0d060b19060c12020f0d03230f040c061704020108041e030e0f0d02090402 76
    0x1c00c04003012a14000d03081070f076604240c03c16100c05451301c5240360740114060020f420041c1c46141c3c040210002084200414008070528000068500c01c00544a16100e1080d0320341078226806e8442c043c0080200b1b1645040100c0143c001003a100c3c17140184540001c2c003000180603c040e609000060b403445c007803840d0303a06044001c51003400c41c00d003d400e003c180c1c04100140718007441207000381030116079071800d160804000442d140d03025007490724140c00310007140c860b0301d044030101e0703482000066403035040000180902d50605400c4400d0b45ca40602050103680000c2061010b803180c0c000341d002c68070845007a40c5031101521034a56540c043c04060702e510784130342c125034030458400e41f0341251800464a4504030440c100e592264100032041404104001c14500a00400003841c00000f50b030351800c080b400302c800250010781002148c8001c18213000803141d410501e070b5080919490b8000341d91402910310102d0369007a5118500d200074021080c18260740740183c0982c01805c41011b0380e103543c01c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 316023444 1250 316022194 316022221
    0x41b030c1514120105120706020322080a05010209010207090606020c13020d240503060103170c030d0e06040b0c030603030a1d030307051632040b06032e030308 70
    0x20040200610600d02c1d401c1c0348640350007803400034064101915950f0515080c80300d100306024042c03650ba84545420494103a01005842c0c01070103010b05c022074a030720314052060380d0445400c07100c80d42c0604000401000030560042c6050242a001d958105940c2d017202401c6079818850480541c100c02c00c0005076190849030b8513407a609900c001410649441d0041c0c045440f0f94142031845903440d00309007038007403081c0c00c0c44000f40320171030040003990f045585079030380042c101501280000b400704404051403020310039140c18030349902c002c1280850b2180c03140e80c0e50405540556440703298502180f082c01014040380d21400303002c1d00840c903001d020301040302d0030f6140700020303c40402041111a01560b080c00240800e5020b88000c0c20080d1040810000d6603226600a14007100e0000c1b800304080703003408207044072500c810786140b030044000340810040c2c54040600e59021000100f0010340e40c40610a80c043c030340729a505400c01c1151035181041a05c210300024020861003000901c84461029 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 316024694 1250 316023444 316023479
    0x901180b03160b0408011b091701020c0111070210090305120919062c0112090203010209090c0a02010b0d0503030a0c020307060e0d0e03010b010806090615070605041b030c 75
    0x1001c940c01510b800c841040e00500b030342c00c0700d41068000036003000342c2d4009005e11b450342421030840041342400000060300a072000e2150b246d01a00b2100d005c9403d400a40c10f880362000c00070002d0003a55154001c200242d484064200d2103030901c0d24002504600c940070b401c0680e0b41c4440240030b0700055644065080e00490361156012500560403ea480e560188201c014201030325260000742e51805400b4844500c0d507101700c00b0380c082c50f485155a0b0b900001120010034110380005440d1003600219029104038000d003500101d11701c0c1400030028402c1c00400d03c60b00c16600810941102c0030400c0303007041d03d9050180c4254000c3c00070a481c814140d12034003e4404c00e0046900d490030581c0ca4171b040d1a50726080d011140c11049a0081090304450b4075500d52030114000c00c01104c1d5500040c04681000d00b0f4a405400c1200000f0300d0b039120000308a48030042c05480e20380701ca0071890b00001401088a048601003074101000c18030080150501059903809040300403810700380811843c1000c03507603 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 316025944 1250 316024694 316024699
    0xa0906030b030c030111030f01051e0108070905030609070e01050609180a09050607030207051506010c060b011404090f0606051606020c120301060305090601050316050105030a020c01020f03040c050901180b 90
    0x764900840c130b540074440d000300c020200358100e40782c1c542000200f50301c0c003050740194001c00008001c0714222110382c810207000e4000b420180d00549903032038121007444441e04078a03018800e0505225201800107664004c60741494003103009680c0b41c10500255010700303c0c9982d0000301d07000560030400c8421800340c1d80001c803442d00080034807158803800c0ca0060b0580c3d0402c0402c0c0c1c0040c0e07500a002c41800042100c8101d48012482c0c1c0c14200002810a81d604002030003180d030320301e003402d107030703031007244890f020409a090309074403a030312480400010f124141444144511349030000a02501881c2941d84041010100745086929626420301a501048d0b000c040340c000e0a0355440a481010042e40c041c2143d0341e0001450b2812140c030740c0c90060181c103d144a948004003c030740a005503594402641e00038030340300f91a80c483d409504040d02803100805102c1d4004270f8200007030020700000d184180e001e03054a0043d10b0b0b945044c4100c020007070040916418484140c4d19003400541c0000f0500c841c003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 316027194 1250 316025944 316025953
    0x40b0732070c061206091802010813120302040e090c01050f0a09050d120201050a0504150b13020c03251101080c120106021f0e211309060611030a0906030b03 69
    0x140d0b803100d402030070940260000c00e1481c2d58180c3e0145861107044064440b07074404101c02c480d8007a03c2c258941031600000d040001c070000103525144c0b140349041005502001e84149990540005006508203008590032105d000300007648a880020360700a00b0310042c1c4550f4030304401268100c2d1540d002407800c400307000c41c09030006140d071200c1e4414110640251808080503007801c000070300b55140a072040c03c03460705082c24440803a003005285401c5a4000e100000c1c00100500030840504c0c00898051403584045002c020311480400103010380000c41c009a10281d800c0f01c10321a0408403d440036000301c10070030f0915007039401102075980110241d69110b042c80102e41403440002001d17040103005030040141480041c0f0948001d190002a004050003042e5402c20300940e038411813a84003d1060840245440b4100380400719107041e40640305c18194241c0703d01c900c101420b018815000010500403410801c14404400d860b0a10130350769804110510300802100034101c1c851845605005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 316028444 1250 316027194 316027207
    0x40f1802091b0307020309102d0309020315010503061e070503070c0f0f03020c060705030706020304020111060708070212040e06010305091009050a0b1f1802070606060206040b0732 79
    0x100020b503204501c0d517030080d5a5400d4220078440c69a0040c030b802400d00141940e04108100e80b411038000b185d01c101ca108a40020705041200600344030400a5054000c1e10307000a501040c1e800300d581030380e03c10744c2111001c0e2a0200c0c03400240b541541640099500d12002c641c81620030170003035401004c1483e04050000580c0c88081d0841455003007159540d5840550034101501800800684031b002c44040e0f0612101e611a2526441403400c0185130a40c0080058116805007112444c9400600704550781440c0640005c0c25019050f1500b401610811448221124400b011079050701d030040200340705070b1036140040d0003510014160851a010325030030300b246120644aa8009103000d10000d11a00400c0e04009058460203020350f502085400c490b034000c12988100682241c100039840c101c02a0582c40401c002d010708440240101c0c02c21100140c2541c0c000360141c0113a001d140c0101c65074480c0c2109840c80104c508646507181ca00b90440115404641d0074003040d9564084511719000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 316029694 1250 316028444 316028491
    0xb0d050a090206040923090703030c050a061d100902010f0309020d080c210f0702010c11030a1103010f05010f12030c08120106110f1009060b040515040f180209 70
    0x20005d40042444503901e2202000d440f203400303402d074003081c10500304440301d042259403261610f00501018082c40030030a24401008420401460144c1d04224104880fa0340030f1900b00384140088040d02ca540302d039000d020800500f41c401c2c00007090307058440800e4004411419400703070802c5502070303034080040c1c0025400721320039500170700351109290007034205414143c5800340f2090b004260424200010300c45524910072540031910100d409003000003180000c0d10781003250044030b07400707260540692120311003001014602d01030300600807030091080b840040540030445101348a0320020b070b049000c041013100042a010301c4180d0107885d007008000101c1e101e440b031030f40c0b00241044c00c0300005001040640d074002c40c40e40300125441c02400c180d4411000071070303850000c0b0021403101603070358440404102c4e440d4400c00d4003d0b0301401c14410340c6032194485181d205031589241c01075080038a1060b403030b00280b1a10302c43c250380140c02c543c4504c40d40c0034001c80040c000e00a041b505140e401402c946c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 316030944 1250 316029694 316029697
    0x40b06071709030d02060103050604060b03190605040b060607150f0b031b0a0815010b0313020315060406090c050409110903160510030e060a090510090803060f0303040b0d050a090206 80
    0xd1002207610354428920b0149803400b40c40c08441c2c0d0442d00440300600c0001c50100e0103642042d0444000300740d00c41a800080d0400b03103c9484000b40c020303003070114010000d054011a2055003d2843c010304d903035609081c000c103403040c003000906049103451a103070741c245554071620803440c00f4440015031540310740100745013039025124407010000408407002240741101d10302000e81012005440d03480030200034501130344d4041c000c1e05080c5101000042040c000050407500b40c40d0000c0848800c0051031a10030001d00d4181c85003402079044c04c001081303250341c0c1d0060180c1c4803a15982c0620709031610b0480c400401c20f90a40000102d000c100d41000e07550700700b08140314002070042514600d45040104031205041c49980814181000d1655490000c04990907900000107000880c401d403180ca4140d08002040300c942e00060710b00407408040c081804080c51140400744e441d2012211002c04059482c00b0391712455140c414200814039050750290031460300290700540220f9400340550000390b05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 316032194 1250 316030944 316030973
    0x8090106090f06030b06060a021b06130303030e0f071a1e0705030406021006260708030f090a0e0f0612240f070c05060a020708130605190e09010302040b0607 69
    0x15951a0304084c418044640303161500540c048810501e0014010400307510f0f04c0304880700e05454041500c01c000b1f50744031442114002c40360582840c0300d06850740f4024000701400083c0c0c1c9480d02c500c2c01e44a103020310001d80d02c0c1c16100e41100a160b05658140b241c6025840b00d5801c149030202c0071240300070541c00e403029001c490b205c2c601940c1c6a03801d0400c0240341c400c04003803c481c024100708042119000d505940210301141513101d01c441403c084420340b80c4005a403140c42c843c440020720080a82286014014080080322907205885c1c0da031a812224041c251210565880320030b0104215192100c850704c074203a0b030034007956140300754041110380790405141820ba174807083d0f40400c0441c0b031000c95103650080007400e081c0d0340c400e0380391901c42c0d03910001414510f041f5400030f140c205000e048401d0700c0361034a00e070001030940d5444501c000c000342c2101e040000c841d100d03c05210201c0c0c2c0a400800150b42001d060310f507903680717550204000740c1001000d058200f80c00f0030006001c03510f10f401e4000c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 316033444 1250 316032194 316032221
    0x4022110090f020118150e04021c05060a231215010f060305010b12152b05210a0c110d0c08161a070501060503070609080606120a030809010609 63
    0x1400d600c2c900014100e0b0300e50807010302991010780f905214100c415080b4000d1025141b800000b140d2140300468001d2140c26003402d10750415007401d0801c41c80320340016214402c192440d24000343e540caa041e102c10520b500108203421100c4100009090910404001301500011907010400d0265014810442038001202c01e4040d00740903c1810f4050017407500400440c4c0300c1c42e2921060310f029211807200a8032031240f4403028003044c40703181c0e2140d206418070b00703450301c0303101c0c89102d4101d603c0080300b15643c0488040c080c820360031640321603402030034109140524141d49000902c0030300300c40100580310101c0c0c0c91074103110156019219410001c4442c0d1041000340705003820b1821951605001004180d15601010b40600007440c480b0440d03c841c1c0001c0f490561660443e182c1240548079680065401d8440c0080000722141c0c0820550201d6000b8001c0c3d0702192901c2050010390180c3c484010a594024502030740068480c0c841e1940c0904003600010301161142900b01c02c0c0c5001101028 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 316034694 1250 316033444 316033463
    0x308030108010c0e15030402010f050d02180f040e07060c02011e030506030114060a0e1305240a0b01090b0a0306080706020a0311011505131803030501060f02060402211009 75
    0xc50250004c04056a5503422100e10f0301424a2055040140c400188001e04100d040c10180c070266019200759070480310702960030b6445d1a01d007040141c4101e400c5420900c180c01c0e07400c00e0202e40c14a03210741780700f0740c1780780001e0071070b85051501c151030260500e9800c038100141407440d0746032002884040b80e0b9019030b5940202c0c031800c02c0800c0500351400190002c03024844541404615034900c00264111140404407030312a5030390018180321300d0b410386805881401ba80021210900c160f2403070040100441c40e900c001078444c07594910442c3c500000c01c2c1e003c0303842d1081c24043c8850b4000648106810b074a0003180440d1a41103260070000e96511440241c1d11020b8a00101600303d910402040e40440c000c10510028010b5a4030a00721072140500501506000d4001e140e00d581003c08030601c00482440400443e15000340184001d224040000340210209800030b4808503146029540040034240700c902c90b02e90840d01c081c80e0740303070401d80c912a0f9882c40c1d04440301030046003012401500c015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 316035944 1250 316034694 316034711
    0x1012230708040f1a011d0705042c040f02180105010c0809031c1e0512040314070515190207020d020618120706020105010f0305070e0c0d05191d071707030803010801 72
    0x450b100c043e40000e1604c3c50340b4008001c2c00c40d23403000554040f00c0d0100b007014401ca4144440890f510700c41c0d81c0481c4521142800c12003400142910240894425144505241d1140624003070012017802024009407014291002282c1c24001410248130021300b56654090b0524a050007038029403013200204c0e08030500c1641c0c0100d0000340321141421b60078064600b4111848820623030a0060000b028402d000000030030640c1d03403005580314194004121020140340c40d00c05070500e40200c1d400d0443c204403000b49001a003050003642d5074981d015104a000400035030801c0001c0c4c100c181d250f210b0119510031682c2e107a8580031000001001d032406012090b08014000342900c0058000c5480f4000f00c010810000e0000940b28048404607282c01a894039000e140c035615215154011006d142408240300b0702943c3c9500c01c03040003c030b80c0f004200740030b1500943d0103121310504035000150042032080002c00d1006540001620340402078450480c1c59a03075441580e0001e801000b0301741c2d5101c0380c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 316037194 1250 316035944 316035959
    0xc050c030a120c020a020109050d0501061502100b01050405060a1d0a09090c05010e09070c030509092e060e09060a0801020a02060907050102031c02090f1012230708040f1a01 76
    0x200c00e030078015032000d00410141c41c6c00192105c0a42d106060203000070141c0d80c0c050003002c1d80b100c005007080c240030008650804500a6070f688540c80d1004e0104c1c504041c45c48a0743c080c4084604a504c042c00c0507042440804e400d566022555004031411018604011219a11500c0d103e025003481540018005980c2c10410007003a059001141442044481858103581d80c4a00c15804009840e112544d034036246401ca80b1805840c0040790003032068400c2c000807162400130090300d0141d030b43c0c41d03d4030552440320000c00c0201c50710403100403482d6003803000c140d81480329a140c0d00100180420340706640e01c0764100d017268005035190005070040c00030300c021a031050101d0002071809200a5090154074141c0050784080e0f501400507090b800108055507498020042c20910340c0209540c0b1113020001010301079280020a18185524186107800c03045413003c52400c050007525064140c40e65a903030b00741c0d40c6400181003540c948509034514400500c40f607690100b000083c8000d52000d5150608 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 316038444 1250 316037194 316037201
    0x140702010e0a08150a020702010206040215041d070807020114010513090f060204051f021203090c0a0e10210303050916030c051008150f0d02030f032d09040c050c030a12 74
    0xb205c88650b00401024008d40e81c0040d84942058048840e00b44040c116010480e492240e58072100c048904a80780784d0301080b20100040c483d10042d2904038269440401c101e0803544006005904240c4000c0103100300d0034504000801e44807902d070b00091801c03154403500c0428040080466007076400003801d1126040142244030042c500f13510482441c2900100651100324401082546000200c0010740c44e0b0000c10826681203000b41c49030400d00d8039005c5c102c412020440d07005c6030340303582e5040004410b505461028500841c401c0070380d01d01b40d003d13542140501009048034400703110b220440c5520301c0e540818800103500c2140d000c0000b600e400d0901051381c42e041250024020f801c0100f000d010144a8500c01c10442100c05181855041c400199400c1c50315070003940501c0740f40d2880c1c100000c0080107003178400e0b411070340040300042c0348000d85840c02d8030701d000c14403c070040c0140e0109080c140c0101c0080416030408500b0700441d0009507145401c0701c210700c0b0020f114a084084074101c0c3d8031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 316039694 1250 316038444 316038451
    0x908060a0615090605041206060b160201030506100206061017070c02010e040515130f0c11010e0304030302070b030a0207200103050606130b071707050a0302061303140702010e0a0815 80
    0x5119a00f10720340f03070001d0894025440313011030128804030100104041940448094a098040546c0b81c1d94502c048010105500400300d001c01d00d000040380080c5400c8151080340301c4140c0c010328180d0340b94070610801c410030207000303014030102080c0714800c45d0030207648501c10303141e41d95880c400c0c4429000051107100040ba5080c000c1749054240440e64100d21340041c4824803d90700e4428401c40084028001c003003081c1e1032454175240c600c0d4001e4440e8030848901a58250368024005801d688003059101d02c198400200980d203d05800c0000d030241e10083c5038008015800142170000c5902c1d10f030031407509644840e11101148103d4503036503030588aa203411080c1601c0042c2443c1d03e505134140c036825940241543d81d8004a60b00003000f10301c0344808030f6045040c8070316441c0d220615015a03510090f16040b009400381c0c00015000c0b100d0102e2100e00240c1690703d41f54039100301d0f11911030f145d205280581c10840701c10390798005a00ca140266000300a404006c000c80084849034000119004c0d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 316040944 1250 316039694 316039697
    0x309010518270c0f0706200307050715050606030624030f0f1006020c060f131e0b03040309090e0309040615020d0e0607230a060515060909010311010908060a0615 71
    0xe11134090300d10448010355000b250f022100241100001809070143d0f0090703a6100742100700017040203e01c9e58000b000d400180d00c1001203006601c900000758003a50000c4500c190804d0044c4001001032410300301d11a01c1c0390301004006040100e461a500350761b441124805180c1a62030f090080c186518883c5aa0014601c440303100c07460f0502c00025103c04c4d80480d2a07105080c00b10b103111100c0007002c1220310700c2c45204401c11445544481607480400c1490070a1a10046070500040e4220002d08036032140c1c1e030650711115803604012000d8005d028641e1940d9140c4410301c2100710320b4860744500000391074400d01041e135200480c00d00034507003040c02048a007001a40d11800009488031026200f090f0361280400b0b4103001c04500d008200e210510000d1405d02c45c82d0783c20010b1008039800103005a11580303540e92241514020301c1483d115806c0782c95080a9100d004102150010034000c0c0c1c10001490484902030383c40341d442d03250600030754005904a684c3c0c0b0003002410010004004d046025 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 316042194 1250 316040944 316040947
    0x605091c030909051801050103060e0c03030708160812090a02040b0d020105030a050c21060a050a0b030a05090c03161e030803011205030d06031104051005030309010518270c 76
    0x4a41d801015500d591140c002107988640c0401d0100752100c06403245202d09100802c040d40e500d00f01680640460503c1720010b0140510345180c5041c044111154103411040c1103150101c20502158006000030007500d00c01c42c103000c04c00030426402c002e98058840c01004086075090750040004583c001c564052244a46500420050f40c0020640b5441103c05100040b2603440d4281e8007058400c2601065002c19031100c9d440850404d0242c143c0242000d0703450312141a01c640a022100a50f401941c00002061001803414542c2d0b030040c544c0400c45a0940300d800f4004004245061518084a84141246076061018003103541c403c0c00c2e9803001a080c00882480c3d500c1d0040f5900c018080e0146c445100240e050902004004a807035a04040307404100c0982e907428801c0b1100780b0032201910850070100420111014910728030191000100554503014404005644590042c0c0301d000703ca4102207840282d968600100305614a11031054403c091030ba40240d0441110007803140c900c2d03100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 316043444 1250 316042194 316042249
    0x2180405060f130602030402032515020c06040905060d1407080609010b0109060f0903050703120f0207081c0e0307080304080f03030907060c02061201090b0a1d0417070804060509 78
    0x18050f40b511021900241d0050766a1903900100e41004000215600110034191740801c901181c0000c8100301c034164219443c0c905880e610498440c00442c050581c40709080c041170011803040d600c1a0f0300414018060b03c007603a01c0d03540745007218a101200700c0254014003001c2106680902c015075000400c2c074020010b0850303000000c4c00c1c2000b2401407404200b1103c1202d85014012a007140203581c00100b110381c2e66980e8507101590b244041909400100700d005e1140d45603000041400030750f003404000d401c0490100505202402058450801f008801c202c0340a8030744092000130064000c236005165101d06101c025464000343d0760030580399a200f0000c00090310404540780c8240c07001c40c50003048103600c9000060b081e010759454401c00e80e401100001c1c10903450782c8880444441901e03541c82aaa50314201c44005100f660882848040c860009001686003000b03d0030641b5070504850901009132110f500d241c00c103400c00300c0070070b40001d481d510a140250030000f0200503104010807850 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 316044694 1250 316043444 316043461
    0x170f060117011521020d0b040f02150c2503080705011b051801080a0f020a0906020d02031c020c1501030c0608010b0c190203070512340612060302180405060f 69
    0x484c01d1040d0b83c0c2c403080211a00455079410303043c0071181d400000e02c0003a4182410503848100300544124420300b0050004c0c48412010000d9415400010b4040d10402d10300b09001d804803514074036082041401a0b0010000614183c06410480d01803400020401c1c2e08400c605401007120a101042c41001d01100c81d40300680000107445900038030700b9640e00d13110601242e016100040190a6280c0040390a0301c9941d0300824200403140705900319481501301950607600c0740b007642551403007240c58a5004082e005560010800384440104880300d0300003d903a15010322400703030001c542a0b08580410800701e58001c0317809001d0010400c4052130040c0c0d40c15038070340e1044a4118a0380160001d4074030015940c6c18440a802888003a00070041c0f9911070030015190402c03000311200c40044982190602250b202c560104c02c100100000c030604c2c185441603c03000d060003ca03140960701d604c0088016190340c201c0340030010920094000c030f4141440c05a0404100920b0401124001410401c112 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 316045944 1250 316044694 316044719
    0xc01050a0515130b0f0a080d030b04020310060c08071a0106080907050105120a0b090c040e09010e06061c081306110a03080604090c030209040f120305060901170f0601170115 76
    0x2030f203001000184c1d02d034003980031800410742d04e07954641c8400c100c2000148580f01083d503000c421201d81e003c020207101d8200f00012400300755040465890154020f10401d03004500d1100c625000c4c003100750900526030b1f5442c0d0501001403601d5a501c2001d4010080142c100803c80e8104007002c01501665082800080040c0658400921184080302c00b0402d2f250071544800d85017a005841c0d260740b8030340214030407480d0303000b071141c60400b41840300000c03070782101845035103030018881c00942038685070403040181b00001822840c109100780740c84130000403082c40040c44000300c42240c0245642c41c04170060144a00007120340c03810340154031610300290703110050a62041e0107c4000039024641d0904000041d072031b4000942241522061105200c04210301d2294103214498040b41954034090850a450042d03a010b42c020002c1401400050142d41801c41c0d00d0040008030f8420704001040b151a00c4400e03442003c8403114000c401c0381400c028010700e006039400610402c0e030f8628260096800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 316047194 1250 316045944 316045969
    0x1b151617070c0f0804080d05070209060103360b0108031306030513050a06050f0612030a0c031e090602010c03022d0408070e06030721021003110c01050a0515 69
    0xc0140d40300085249014903000c400454204014020400480c542001d065019000d100302c2c0b40b107038141400303031139100e0b408840320a0303400f42c01c100403612042c0c0190064501d0408139404c155000b550b80d03801c0c0214101018041e4940e01eaa000c480c07415047c208661041a04041156001003040001824000c03030010300700e441c10f04e000680c965504043300320381e19035024001c1079405090540400c1c0801e03074000710700544c1040e99203000ca031503c1d000c11952030540c00f0004041d8105001036250300d0f0080a41300022400380c02c1003800301d0f54585840c11035002940d00c100200d004002c00340480c9038240b00300742c100085820210f01e468845500d5141444100b0000340d15024034082c035a181484070403d4900601c11703c0c0c12115955100c1284600e118011203030f4a019100d4514001104546c41c0b414004010041004100d00d4049800780414000710128174410305481d03001c681389186408004042400424000103070500f80340e0720050694034003802c096410000b4041045840d5240c49901d0b4a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 316048444 1250 316047194 316047227
    0x40302090c0c1902280807080109120f120c080a0c030501060e0927030307021501030804170f120a02010609061401120f050a1b03090b0604020f1b1516 66
    0x504802d42c8001841520429880c500385e036a0384000c000c0e04540408144241c9000d401501c2015454032070305400c8424051024094030f4819094004080c080c0403e808843e215241a1403209141d0392840c081e80c1c5081e15100000345104104045100e440c442c6108150240c90b040c0555450031200a03e00100d10b00740d54490700c4242c01003180204840942c24441190b100140088141a6040780d00e9800171140341000d8000c501c005041c0404e251480c2d8181d1f81c0c0200740398109400c0002d1044190144103c0d604a88107001403007000050070000096001d140c02c000760340e200d0200700d000303007924429840989802d00307045080c881662001c00f844010002860020408103d00f0385c03001c060009801210142031901060101880c1d241d00071081f2420046038605442401c0d4604074102d0b03131035800c0541080e041070085003552500350010800c100c2d038103080744e081400d4901c1d5442000030743d03025441d02e640291661a100c0d4825114103a001c0c08440d0034643c5103c0c080030141107040400c04000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 316049694 1250 316048444 316048483
    0x1112060f0f150d0e070e0901050415090521090a05060304050c09090a0c060e040c050306090604020d23010305011107170a031113180917030601030917040302090c0c 72
    0x80307001404506540b002d501e0100240501313864011314944413010780c040d82c000d181c4824006541c48005001d03c40c003455118411900b4442e00714a16401082d51500496050040d0416010800780400e440000311450030010350307541a01504004001c03016500c181d000750000d00820022810100d000c91400006588905050f2b4441c20100c0c1810325800e4000c0508200e04004101c1e6940070a07a200c55a4054504000801c1060700a407514001152251f41c03082c4818005411414650007500c524020840b000c2000043c0c100ca060620000c808150b000e00ca440b801042800002d000d141840e4240c1c600c0e05181000644403291010303511107106100344000101018030300d1180d403050256541626408c1d484801d110084560040d030b5115241c0c20708411035106403048894440c3d030030300b150f1240d03030300034000340c640c4141e400d40c1c03c000c100c02c2c1455658101403012070661441610301500000d00300d079a90342140704000c58004c020304101c81d581e100b4040034540c008005005018140c5101000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 316050944 1250 316049694 316049719
    0x70609050d0b0c090607050706030507020c0109080d0c0206190806040b090103020a14061b1506040c02030d05100f060216090c0503040602161e05010506061318020d1112060f0f 77
    0x5440c3c6c422494020300c203101f603810000d50940d0580c0024090320103a820341d1000250710300112140d1015004440f4281c202c001c1c1044140d0003206100d09891000e4112400c2204484440740c0c0d54081842c5640403c41c00d600f00041d9241a10400e100c24a0480d029070702d0354116004201e040080f8000c480c291000c00c00300004981d030701405e4410014000320000841d01c40704c42c0a03601c418202d600149003555003000301d529840d19001d11b843c14180c03a4001d50a04800d480080081c2038042e025140f5864031490101c1d42d100000000d0340a0801c5400074500048521a003103411a890340c40510441c3c40c000040440651040031a600542c1010015840d40107903c3d080031103062654008002e24864071440c3c400c0d0041414100c100c0c1d010300020421740c0d03558400e0140510aa51032404013204418060200729403041318400301d0000e89400504140074a2240c00031100020020f84100c28040307401e130803051241409562200003603503d030781000400c1c0701060040000d101081d00c61203880e1100d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 316052194 1250 316050944 316050949
    0x1505040506130918110405010503190809090103031e14070f060f0911030106230d0314120a1d07090e1002040308042115090309030f05070609050d0b0c09 67
    0xc0310090b0102c50740c100801c3c04045045113240c00c0f03a00d002c469445409000b28158a4144203860490744040c0c050915072824041d03d0701d9020a0a108a96100c0f05000360035803520741e82c07000c502940c402d881d80c09540783d01c0c001c035104805040c0c11800070070040c041500804040f14090b1002182d20114924842d8000d10300300d405070141da0416140c0500e440e2000061040d035558280070041c09400800c5039036215030f41c4090302c0000302c00075514071030492104815810300305a050110741c001c3c5044410090040c0d229146a8803940e00e200c42d0f003541138207001c1c0c060310600c610804901e0080941c0c005015401034140c482070284102d244035581c9610b201c0b0b080c03805000d6010030313090729030b421561292245441c9005400c80c1c0140314a0309242d600066482c034020421750401134002c20f603034105000003600c01e03000d890060812401c20010b49800000500b004000300e03440d51241000c1c00b030050414400030000c80c91980494400d80340c00d46c4d808041015414030384d4200079400002603640171403202 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 316053444 1250 316052194 316052227
    0x14190308130806070f0e0d031d030307020a0b0904320702030c0307050a050606030703210e09070503090d020d0c2a0315050106231c0c030608071505040506 68
    0xd050381d018a00c1040109076114a0302c00c060f04580c0c440b202c01d0030910302882041041c44d0002400301c0d1088044a001c030102d8115083d008100032b0459251040035070110380080d0b9030f50321850080c1004682009a8a8280500c040032203184080c3e50520a0340918241074000007290010909a1a004507541510900c12181c8000300802101c8c0e96020920708140e44850040040d1201d004000218030305240205000c001c03250040d007082c03c529400d05058043d482c168000c030041c0703e00811441110345a0301c9200388580a1900c3d62510780c9002d00e151804c004451900c082103402c01100308247c01d800000c03c0410540107181105084c15182c4103400c201684045042010b07030824000040000304021000d01c40d0140c079007030045903a5900162404446800050501c0c1c04820140b003440c6c100c107014001e4042c0080c4001d80d15038031540561708070344500da680400a0384884c001e204202c0c040008200404c1c1459034601f458902d000000c000d03006a0240c940301d2030b0300145100000d401206e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 316054694 1250 316053444 316053449
    0x30e0f03070b090109150e060c0c13140f0402100e0d1e12050702030307020d0807020a030804090b060903030a18180c0801050103020702280806040c1419030813 70
    0x1001c55403810786030341100c2c410b500401d444074009004142c001c07070181d1660140c40020107141e1038503240a2100020440d4540041086488034031031030001c40750642c0d0341500140c40145218000858424100c1084000c02d4000c0c030205131148142c0520006031210f40106a43c41414a0041d84105c114000145d031410f05c00d9000c1c1c162154510a922490072400404542d20b11642404629005e9090103540501030094040e605400070301c0710502508054415102c824071840300546000481c1c0d00260b203c610715003080e220580049014801c3d0013141c4650380c91924100c4440f414100d408002030394030703c6000c0e40c0c0010000b00c1c69024036004600040c1030003a0a201c905d16400303402d2070781d24a000301150100300700003c102c40c00000d1194007a101310303010b07550003900484000280b401440c0f44403501071001d48501070710520009400800b400014080d907c18401080154a466100401d414050102074440c0090381818103049915420f00412a54007412040c1ca5083c8961811140380640d13 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 316055944 1250 316054694 316054699
    0xb0306010e060415150e0d1205030a0b09090a29010b0901030b06030406020c070b03160f090909030e030c0a0f092408010507021c091e030203011404060609020313030e0f 74
    0x1401c2c003160083c2d4043d510b50b0f840160703550350020943c0d0786c01085503070a443c0c034000d00400d241c441405603492050004540c818a45034006c20840004408901c1c40c110448030000e09400c1034a40e4020048903d001c1c102e407101c00b403280d002e01e00081e40c03c1c0b503800304107215200c4035000000d0440c0003a402600010a84880141300c2c580301d1915040c4800654800f05610004d40901071010402819101c1524041c0e600504621070302400640150307121030381d102c0e55009224900100080c030440ea4080e513500103200361355880000714071001349032400408400c030601c0340e4403a480c140030041034010414115401c6030008140140c0380c10400c0d0843e8100c200200800078034540114141c04d0540041e40100d115a0860340c0781c1f12240366078222000c1141c203180c0051701d054000c01080794003d05409140f444040c1c02e2200b030307a503907001a08440c08401c807061805680002c000501506128400040420200a42c035514100110b4100301d07804540041c01c0c044401029001912040c03034000c40010302 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 316057194 1250 316055944 316055981
    0x607113403081207020a171b060108010911030307050c06030a0906051302010813020603070f09090c030e10091a13020316050f0604031a060612190c030b0306010e0604 73
    0x22400e003840a41c2c459800703440e1610040c00420b11041c40055241b01180d040360380e01191000c0350710050440e6100d40c00240c3c1031403151208516840082c0030b40c50080642900000300c84000e441d115500e1a01c508001d840f03500144070102c04200041a1800d07110780c01c440b5159240e6607144102d00419480c940600003074900b408006141c1402a80254118000d0700c5811581e030b00c42e0304001c0c880100c0c000094100b003081c004220094041c0b104c1c03036412113440c1016101642c039980700d40300b01c134883c03101c260000e0703103441d10411203180c1404900c4d0b0050404405104848803900c0700030408114188082d95841541d001500a103400c08a081400c0da006082e52010a20300403001a24079044c000d1501c83c0150501d01c0c03455180602c00c88d411a40c0c4061018000007142c1d45006030544020030321500400300308402440440000c0c00e052040188120a0031701c100c000413010222420005d00105061402c0c001d1f40e41941e00140c07850450b4620b00344031180c0ea8404001c035000d80303086900000e05501d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 316058444 1250 316057194 316057199
    0x31524030c090b031f02030c040b0c070e100b0301140d02060c06010305190c05040506030a050f0d26061e15090f0609010504060503091504050f06071134 67
    0x700d06041c4044a0600000703002071451681010f07181c10010b00b0b5209440160701d610044a4010340296522600c101160fa0405603200d10f0490f0aa100402030758440c1c110010612090181c0405150400e103075080d00e444050902e914503203148010b0040704030008250380d0710070203a6140c009001c402a8041c0402d9191300c45129170555a22003070108507024042e2030030021802040f4003d2030780711600700c5400c0e10303810301d00001d0200a12010b01040e4040c0510031020000c0f03101006001c998501d0b5500400022012010003404030540c0300c104056494000d2108021100c1c2c156803c4e04008120394540b00086a10703980007a01d11a0185a81c001d13000402e90304648840309d018210304c07041580c0c840f040d841c0351401c01c02140b08080c3c06d18003041b002c1c4001e200711446440507580c400c040004584409010400400074500c00f242c0403140ca41c8520b60b4411301d5174042c07101c0fa8000034076040078070700090f881c00140c0e00d030045a4101075252440c100c110140358110030745d8802c9001404080c102c1d154 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 316059694 1250 316058444 316058453
    0x822030f030b01030b03070306050a0906180510050705030103120c2003210418090c24030504020f061309050a0b1504030804030b06061912140103152403 67
    0x608a1811400300e0702c0c0c081c0040e9654041e020b000c00501c402805010903d080d40e0725200100300c090100c040c2203a0b2140148001400e9128000c3c2910450401052400302403030910300d422200c1c84100c082a09003001d002e0041d070444180c0c1d0550307a000e0030580704400500d808484000c1c1d042c80c007410412824240c910075114031072907510100015015100c0d80c03910210040d81a01c941c405100c45e201041004100076840805121000702c2c1d001804240384004c0d880348521402c15400c8100500c0c0c00c825020504480c00c001107042c0c207810305052040386080d80010b08961000c44105010f50000a0a603041d409844072410140840e210100722504050128400a05504d0107003030098900740498648001c20005460443c0e03401482c0e07516241c01c56440d0007002c0c201134000f5400c04418012800420821482030341031024590710700c00c802c05480386900546a021140c0090311040038018808602d1800b08607000c4002e10070040b81001503400d040385d90800151100075189001d244c04130802 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 316060944 1250 316059694 316059707
    0x1403040f050c09070816051314062101090f0b030a0201030b15030901090201110609120d1e051f051f1b03080a0f02030c0d0c0e030a0c0905130302030307082203 70
    0x54600346081e02c6d5411162000b03841500c04e0010b1500e01014424003040354601150503d84241030140101c1d09041e070b40c915141c0000c5006422082c40e01d00d50b1300500141e0741500c1500c2e055103403e1020700900c40b44401003525403840300320190425440752071001150720b03101c0307c41200030b49a00b140c659a1074640d09103030003170044010890014800d410000b1400d080022013500402400029010220708001c0e141d0749a03000c5e540001d5119125008100c45003a0403080c964040c0c1240c4000c503079403911629503800d818050600c03200341c1d004008288015190040a1b1481078190404011854050603059440c00384994084c0c0721400d001c44040d04042d03000341803600030800440140001081301d412a0140d000c1155010305086090001c01088442038129001c000581d00740a024020400003280c1013041070101507a80110185080041c10390601c1171a038050f0f40040502005111950025102d100c05800c2508000410012a4040c00401c402c50406150900d0700c115160036071901500310f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 316062194 1250 316060944 316060951
    0x21c03051b07050307080f030a11120309150c0f0901030b0a05090c19080f0601050d110a03020c1002030106020601050111100f0e100e030405010c05010b03070308090901061403040f050c090708 84
    0x6170043c0800042c4140001030819442260f10300514103101503004200ca840714070318241511380c450720341840d54401d0200e0045006101e140042d10400309402d84049c0c0079036000d450044585c0b000c104114102d4521340a45450200c00d29011030301e82c200100082c52100e107604500e80c00f01c080f42c10310000f110040002c2a04003152006440490301464041c4c50031036084030011140a10340000a003190303c910010582c264554000080c2c914100c24000515005841c603140440da000403216482441001008691111a5000d61642d030603c100251150700600c02c5505021164243c409404024031107103020048040c0c080180000c0e5403580e601424007003481000500510344540514003180c0100307040d000184004500d4940f07130400440350200c8000307040c4c6046d50380d5042d03a203043e50240103a030015401885030359212000074003041040e5406070b002e001403002d150b5506110843d008207481d03001c0d412481500381000181001401c0801c2d20a043c0c0d4040300d0001000031994001920501 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 316063444 1250 316062194 316062199
    0x14010303020d030608060601110a0b010e10093b0d082401090308031806040b01050405100e01091a0301021c0f29030115061e0507021c03051b0705 64
    0x80070b6031003031402d90440f03106000381012604000002400c035401000320084180c404012142d0740c24503600c424007449000c0c1c103c42c0218400c10148103182c02880350315806043d000500b0403c03000c1c1c11440003403070100c960140703151081d80d201400b0701103a09818140c040ca1417400380c4403044c1d80010300a0284608a030308802e5034501e2004a00344041021041c0302c4100d040c2c45a01c0c5484c2184c0740c2c81540e403c01428020340d41005041d40d15103100c00d02c003650242e8031500e000039113541031004000a07180c0040c40ca40c00140394041c00c120520280d0105811a0080103000a014074a035949402c0480304144140c0c1640c00003542103901040e00205034120361003240c040201044400041c4240c030044aa60510600d0b14100d41039914101001694004001400051300c5416103409886000a03503000030701090410480700300846513951030030f4405205180c4140b41001d0b80d400640c0c4003541d01a81d035902c1001c03d402c0000c0501442c2200e01559583c41d140416804200c42d69a4810301c60050a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 316064694 1250 316063444 316063453
    0x1020910030b01050a03110f0a0c061b0206011e0f12020a0801150311060412030f0f02061b0a031e02070606051516210305011707080303071d041401030302 68
    0xa18284070344161000040140d444e54503018014804802900001d240840c400c00101304c2d152581212074010300004042d07466195916419040c200d04903026200750b40400121284200d5030b6035404141203040d12960056041810202d02130000041d481c0d8000d801440528103001c1840080c2d0703078138101303020700c00c40d81440c0300c41e00c41540f2803c1e07070081411405d40c03040c00d20040c000159140c0c03034103041e03540180c569070401d5507940d210a00d64031501c0055001c1350035800a0901e40da48a401c0030701c801c2d0075000401e09070400d001000b10030700c40b02801b0030042d0404185c0c0018540720b50440d00d9a0954400c2d0410510703903200b155002540a02001c41d0240c0c0340c4400011941084218400c5074442d2a03216400d241c0300c0d29420010050840084442851a184000d4190440350f12110078000d240c0e40080c407136043c0483c45142c04822110300010354005202004a101c0000440e54806001d150030401c2000304000b0004162141500d00e034818284402a1070f100400808107049034025803c0700e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 316065944 1250 316064694 316064719
    0xf03171b01022b091110050702030105070302091503010612020c0a02030a0c050112050c0f0f07060515100507051c030e0f0303040b100b090405100b0304060c140c0307061a12010209 79
    0x71000c69003a440b00030102d072407178400340e2164502000100748040c12420718030310780f18140d03000074211141180c03000042580840e99034098100143c100031800b002d20816803942d410300700041c02000b1007030003e4603034580018060413400f1040c4490030485a0142c100c0340c8802c041d103820706004500d4002c0b21f001407200c2c403034610014110301400f0f02450944942902e890b0b040f80c0f51401a80c0f02404040340f0060030850500000d8103489080c0c800e11940ccc078440d07020f040386020080000d49084c0070004005050000d0404101e001c114000035800a0040341002151403c047c5c001e040801070641d40c5009014202004e00400301c02140300d0381c0321352402c08480d1b50f485100700081400d03000705103d848041c450700380d003070a180c0e0100f500032000c210f00d43d105503955004407110350300445049883c1515408402045500680d148648403900100c807402c082c40306001d907a9900544c0d0014001c551901480030280540c40038003081400084c080c5d00030981c000d6090307800f07984140c01c0d46001c2c00c10b03000700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 316067194 1250 316065944 316066027
    0x3020f01110a0804080306010c3f082404020d0b0405060301060602030304171201060203180906010e0f06090904030809060c070f03030b0a0503031309060f03171b0102 73
    0xc8403441e03406a200c00103c0d88413030300d170a00c49400050001e4180f0034034020342008501c442c1e1500e0780307200f104d400d6208540c001d840b284d903a03190075510301c9140d00b40e610b59848060b13800407541e0b07034404110700d0511040400d8003025009079201035480e6411070320000701e484103a410303600a14540002542d080c003403921245c2c14142204d8103032140d131700180c00600100d40040d800a9902c0f50030071807440d885d810304845000c81e44070680203903c00d00c0540c2c80015100300041214042c106941021168009a407404000203400d1a1102c00c0140c405d00c002c08400b4105d41e0f40b20b098a11040b40035100e00b010b80790514025141e50300c02d0701c1c4403180f0b1041d5000526032a6044007111132041d40185244046962a50158003910041030481d0b800103c0c0d00d80480d00da2401c0010b13181c4182d01c0c076000340080d0f180240e41000ca841c1078121b0b9403403a6909805002250000311030040c0c0c0d05c0b041c565159200e4000064588120400c00000c00c10f5000184074001e14195840c2c24151103444890382d000401d680c1c0a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 316068444 1250 316067194 316067197
    0x80903070506060904030e04150806070207050120070b030a20031501030f0902032506020a080703053103060b030316060b0f03030c01020a1b0819140703020f0111 71
    0x3004225520010004500e41800c21159800510905115a9602030392001800ba1030b1400320800c10000300e1001040303a80300800103a5000074150020b0004c039414000005c00600c1d50520007580d260280e00038401100c82008544018454806040c2d22410301040c400003508000d00c85040348201281408060b110010899008040050012203603101c000c1c010340c05041da4112a00b900b660b6507040d03e0150314140101412044440042c0421203100e0254582610300d5810090440d03101c4040c0c08000345200c011910142d802d0306159896041020b84da5600c207141c80c4408583c4604103040840b1019a5441c00043e40d100d20f5007032082110303403014142c3d40e008841260009010030007a50707010610a500000c01421f0140c818003484910001082c0f46038003602c5030390801d079030018070280d03080c1d407004884180410b00768001c401c107041d80d1103400080c02030200c480c4074003403800003175130410303005544030020012196050b9031203401074100039417140c0c8400b04100155003084548001d611030f060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 316069694 1250 316068444 316068457
    0xa05040e190e160521030d150f050919060b0a0c0c0504050609180c030a08040e10031205180d050604030e040b060f09032407020c0109150e0a03060c05040303080903 72
    0x203050000c140c03400041091711219446144905c2084200c1600400401d00052503072076110580032481c440c1051251481c0011a4442c042031f54920b0381c1448907549060010760004003094202c00d00110303e68440000309216840b203444030134002030a0601581004143c0c800500aa1a024500d5078a4041c4400e0780c104486c900d40c80101c030800103156545101640e002c020805085882121130b4001203854082a00c1c0b05494940000c20100204844024826448007034488004001461507503a40d03042e4a40d070300344105000c80890708000002d0007407074080c100580104860f00c058428208030b42c46802c01c0c0c80540c0002c032030105031034007070900e03004010f121348003d01454a80314013092040c82c01e40040200c41d606d805840c0828802040e0194500244060915182e94031700b00840007074980a00b44070a00c0c188444110200a036060303102007c0072190b024205620140f88120000703103031130425000201141d1400c240103107681c0c1d128002d0b005492081e00c601810b900c40d079804a030b60b8054103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 316070944 1250 316069694 316069723
    0x2010f0204120602070501060b0a0903020a0f0806130f02030712050105090105070909020c0102040b030f07092301030b181501110a050705010c03090e040602090f0d170a05040e190e 79
    0x9846041c00920305a0017484c20178000c40c00001e840e504d40b201484e42e58480c000301c41c0041c2c420762081c0150b20b4841d440038000d0204440d4090b00500d414181c40d20340707000070040e2a90005c0d0719484005c0c0145c100f507a5024590040954800b2a07d40420311580c41800d50141c0d0a9841c041c00034258030014030032030f0301036070103078403110310300c40c40d100080002e54480100c48007255020b2100003600000000607501a0b40c80143d120f62502d04450000d01c041c01c16484169425811001002444900d0008441104080c42c01059144d9004049440c110400351842c400d03140010030480c2071940f10b2410800070409a80f0821121507a0140c59500e180b151000707001504002802c102030740c010700328a00b0051080c1402e1960f00d68603001c14034070000441d001d460194000030491403e24041e4061000003804480042c0028083e4440c142c9003c845250031403100400641695041d02400c2a07a000380100205400186404131110302072009049004501d1410848041010700020032070304460600b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 316072194 1250 316070944 316070969
    0x606090504061d100f020d02130510080c0405041116140706052109010b062805030f0f1b1b0607030e030a0c1a0906040209010b0903070e0a0b0a1502010f0204 69
    0x20b03080c0382e2000307205c6100c410110560030050360107004038038001b40ca40d01c010880c0e0350121500c0d0109010580041410420410040380100402c0c0c82070b50301981c003500c0d01030720700050042c3d0520380d58100b40f0480c0c1103144407003040501c0314100700c024003203040800600001e07070300300d01ea80c1c10701500c86015a00c0b07006e11080c60382103030180800301c2e48895940000032400104102c01c0440100c0c0c003540c0a040242d1890400802c1d5001c0100d0190b200d80000c4000e2501614514104a0500b101d24018100c05c0f40150b02001040c0422110421300303100002c05d07070560b030341e80104c1000540480340e41d03110769000b40601400192201d00030301c2100c0800e883e05000d1450300040315000c88032100c4000c0120303000401000e0404420607c4a09144203a142a005120505150040141444050f4052021070208210746100b60310041210801c580703210507100010784410203000050662900d006030040004080061004500400c0e8201c0346c2294000300045450a1184d006920544c051800114503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 316073444 1250 316072194 316072213
    0x9020901020a030c060902060403050f01060608010b25060e1e0d080105090c0c0304060503180f07060c080c010c020a0b07110c0108040302010f14070f05040e060105090604030606090504061d 83
    0x4c1d025421020b104510014103aa240d50010303c1030f4215400c181d64540c01840ca03518004424425000901214280000c07103624181803440917201c0e0540045c0d030416041e0012443c807401012a10382182c4c8444280201c0040380111560740c100b074019000b00d03103214103803004500d8001c202c020312461607955450301c684c00d0100b030220360000648036901044042010442400301030015101a0103c5d690f050b03500c1c00c7c408195102424070802803110b0340c0004101c080350f03100001d020021285a130520160400560501c0342c4103000341060181c4650030400180e03c2d01d60b0119071000f0243c41500241e6583e02e42c4a421141041540341039250f9522400061a09600940500740d000d8407034070003c910340002ca0301c4002a01e50724241e1101d85041d47d400c1c01805504442c04103c0e01456250050405141888040c2941c1c1c011b400e840c1072083c00100070002d80c46100c211006983c1043c1e00b070100c25940c50141c7d0051004807001d4820518112044004080800802c1c0e98003c2d03000c0103040840c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 316074694 1250 316073444 316073447
    0x140a0e13061103040209010b1c1d1e060106080c1e091c02030d03090809040213050607050a03090906030203030315010306120b1e07051b033109020901020a03 69
    0x114058002a00396040c10011000144240a600311010055100e140c90f81054810720030f184106801c100c5d0440d070240210f4202c132400441d88080110404004241d8031020491315082a048544520391406181c07005030f606010f25507481c4846e070740c000444505a0762604221001c02d810f96032a22104000c0000c07080c0b1140010148550307240e640b01443c030304001d100c0061103445102c061044c6101100d00f0310130947c1390901c0801184981d509060114200d1695440880d106180450b48141e0b400f041294400b01e1599040e4094400604003039990358050416560358403003148110300149000401140c5842c1c1c0d400340108407507001d00158150340f10500b1000415110724202c904160b9034030000108068009116030180d0b0107011740300950300b40503e104007194404007600d80b10381d1909060190165004c1c0407240c40c03540019809045405440e0f04ea410341c81048508150f0380c66031820040100c07007038206545080001c905600702107075143c9040e0240e0003183c0840c0d0168010301007240209 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 316075944 1250 316074694 316074719
    0x4120b0a1e02070201020c060d051006020d09050d0809040c08161d0918031318022803060308030f0a0e1609020706020409090308071709120a02100c050c07140a 70
    0x910500551f644d20010b00040b460982045010102450302e5a00744002650f0b4405840080c001c2c52003e407100c120282d20240800e0818801d0714081c22416054209000309207040e200940070050080c0000d50719858000d000142c161040418680c4c40c103031104140f07010f0704025003c2c540603106000720641e44002c2001008006110340c1c0c4900c1813501001403504203000600071001c2200c5050560b90400182e801035041c240000c80c0d0462041010307400b142542803e042d0502c0702e42080d802e1312111003008602915041d4802488003101005000b2841e0246820303c0c4690106282040715400e018215030ba202e00c0d103080d1a0304071408460502c40e04c09180c0080428501800e805813420740d44400d240c08990b880c0f5000d6000400000034894425032003102c0300783e8240552600101d82c10110034907611242d501c8050b0020201c005030341e1b4103190081c403401c4101c1903501402c000200c500407015003903900516903103541d40220400030504040c2c410880c01190005011415410304125400118 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 316077194 1250 316075944 316075957
    0x90f03050706270306051902070c0909030c15060e0c031b09010903080423030d0206060906010915080103050d02030a140a02010b060715050c0304020d03030c1404120b0a1e02 76
    0x3c07658111026942e401808144015031045e0000900d40c5040c80311a49020081400e00c500b041c0100500c3c00803c40514007201980d100c0d00d400558a0ba481c40c003941c0032104072600030700103006008100c241c1200c41e40402c0407035108044000d5550b5504140144d07601c402c4808214401e28002025402c520726030142411079010304000b04641c5d1207485002044e08036502c207001082168000d0410a1200240307003980c0e0303400b80c000307000e80940c411029407100780c006e003018010510500066100d0f071043c00b92500a107400240745444640d2244000c0c094402400195441d114506007400701d1813002041b910002c2d1981c1d100320140e009a010340c000c0394024440c1004564170f61741486c1850707980300020300d1454030640040030000351213070140050702d00c0104101c40300c0000744204005030300d45060410200b9411724001901423a11101511800c81d08001061118400710b404280c0780718000c51600c11500036040e802c25070342c455040906541d0b00200800841c54a00e030309001450494018000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 316078444 1250 316077194 316077227
    0x5090114030a240207060506030f0a050d08041b09020a0201050f06100e13020f0c01060609060509010c1b08010c03150605070f05031c020712022d07080f0d090f03050706 74
    0x340c04490f4401c0030a0744c11540c0c0030380342e0550350011300907540346c10400c0d407455031030100140000ea0011b80b555504e5a00a0421206001e1210002420030003942e071060f0b504203142c03040340e002540303504241c0020f402141c20346002d50310380740118072400c5143d01035510681c2c008060340360158186408a1341a0340301103a40c3e0b00308120b220304600404003030010b804a0a844906e041e12440300c44913240c02d449040d44032800713000b40c01d00144280c030307031040881306000310a0030303c00b0740c0f0348803490420600c0c0f5841c07004800010640d600490701d070406401021032400c8955003400b031260707450300300903500c1c040d4858480030a004210200001d031800091801a90049041d00d09008050411085040c84014800350250303000886000300020b8840e6004412240d10080410066014101c855280040c0100e92950302a54010950400030020100980202c00503a0010100a00d02d182c0d144030407104040482e11007a40814078080070110981180e0300b013001460505d07c0c116042d21010000d001001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 316079694 1250 316078444 316078493
    0x7170a02091302180a090515060a11010e060a0b0f0303030a090807060e1005360f01020f040801060509090a0b0601110a15050a09231504060605090114030a 68
    0x1036000140d440500f96001d4244d4407406165402000c11201000c0c0350000c1514510f00303c01d010b0311900141054000e69010f48405985030800e600c1611401c281d21407810584d8200500c2641050010030418000e51410000380003009074541080003404a0121040d0154010700004419030b01c0f64111284c02c03070107170001034581500da85980d0250f41c1e0f11031001c1c009502400e1026410f5815106869000103a0b03000303517418402c4107820413a0083d54000d40c0b513a1401c8850b13410003c040901128021000c2c00c0000c550303c1030042100b036003030b4101d03200344811546041c100003102d00382020510310886404c000342400810f16500d0104a24018080904010118060201140701000720881d45402807900002c01c00004002c0001e03240d005000700e8140d41425a62400100b2104a00e00d60030044d841e8040c02680d03101e185403822401d182d10a11003a1030320140028000755601620681d00203440340c0440d0307a2a0300074034031062030032483d0130b40541c00000c40703030040740302c40c00341c18195042c402000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 316080944 1250 316079694 316079719
    0x1e060f03120a0c080c011410050f010e0402040b1201090c0903030807080a140405010b031e031611030703080c060109050103080d02031509100501021902100f0306080106030c0e07170a0209 82
    0x40c13000d60461991402c1da80c1d541c03000940303503500f0764881940c045910090100399030300382404907280100d181a45414000501b60400103943c450301918081c280740350845480d4805000080c01803003081c415900c41920701014040b6041c4130304000320036070707405807030710022a00c5030705003218807000060080e0076090792503a02c0c0a11203528a101c50103580100c1c008100c8520a00070035080620425100e0302c00d682441c1043c030034510100651309140d16111040401c0142800c1c8032510740a8030f1541a0b06000b6a04040b003007064290140c80147d04181c2268866a2a014001c0c110b640070700004e0b05c40141401001210040741e0011503001080030700c0c41804a40040205440c2d0300c058504071390b03801c4002002c0c444d0f07590411140e10100b00d204542c01e002000b0b60041811440402c1c000d0b02001808442a1211070094200b00000c210a03030003080f03c030b580c90070161420072150140c6904102414041078500d449082e47c0440d40300881c84603842038840c9803403c030080d4001c4203101c3c0c00c03140c0181c48 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 316082194 1250 316080944 316080953
    0xc0e100506070c050118030314070201030213031209080f1b040b030706110c03120a0e030703151a0301020a0f1805120d14070c03020405060f091e060f03120a0c 70
    0x501042803003014140840f5080a0015200068000c5803031080d92050900308046903010500c0200c1c0e2071884200750381c0d11618001207000e84120800c000306002210700000030080801d04a02c1c1c820525550042d0207910b80100036203401d0840d042c00001d900a24184eaa5003001c09500e240320000100002902c001c000c0219040c21104c0d4005030105504842c1c440407100c3c180110750039440c089016080c0c0450b0240300030454098100880c00b0080d00202040d4140c50401019000c1c2d030300710b0900380c42c042c3c520500c1e130040c20103141e2403c025907903070031110302e181414000c0d65014141616000d20040c00b00804031502a141d400c550141031010500048503124000c140520b18140800303060b01c1c100c088406401024040d003040c4521400300900c101040301020306500b0780f0f03411100401c00d44c0318200001c028036404030140394484401400e00c503581c040c2c01090380c150600346041c0703e900da860000300414070140d807070241e4254020005802d65449840024080108541007041c184005901d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 316083444 1250 316082194 316082197
    0x30a111c0c181e0806240d021311040305120a03061d040609152c060f011208070b1f0e01050607060203060d060606020f01200d020a021f060e0609040c0e100506 70
    0x40c0d10000d8510406000c801d08406e6800108002c0150b400d504451459808103400d80b0848003d50403042c0d403001043ca120041808940017550400120751a181d6a18802400c0c0c1d8000c1c50002c000c00c0c90004000b5200716505c005048400c802080c0c1082741d43c0f80e499101c09000189821a5440130055940200420b036106a201c00396202403c000c100740c0c0c00941c2030503c1031580001c402039204004000400000c920700d079040da841c5400030501c1ea111854401781034011880005d140740146030800a0b5400000c03452603200c556841400c4a1668649120f83c10610a0240702d401403002c1189c0d002060150300215049074000d031400f40124010380300d1500310b80b01a00070b4001a00300703d01c80030103680240101020380c6642d0f6104c1700200029000c005680c0300702c0d2070101d007140c1c0200d2443c00d880d0091005044130030300c0c40860844000741c01040002400b09025425920340c110010030300741c0c2018141d080c0324076408034420805a0500e0300c00c0c41c06100041032540020754078680801c45446840 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 316084694 1250 316083444 316083451
    0x9040f0e07050321310b0903060f0106020303070c031701031a070503010b070b2d0601021b0306010501080402030a15150b0915030a111c0c181e0806 65
    0x40c05060858200400c06050506034022031410000541262809100c150704545c17501d240102c0c1813107000c01d031070a04082000d444451541c1c08021110018100009200400054008070107032000390b0384241561f560001d0a008210040c0d00900000300341c0c60003202d8600006000b410256510f8950741c41da03100c41c0409800803501140c00c00b0911300009440c00c1e0540d003248582c00d0082c00c56041048030076160041080191414449501042065146808059590f142ca5140032080c01c0321108505a051003510315500608c9003480c460a5400303142c807280640100100640f00e183d10b80401111a10310140081e68140104e40e1002c00051400181503400c83e041103010800d80c242880044007286144c1c40009a0301d41004010040d644112340034400381c640010844e101c0e1242e644510003050181046000410000f855681d0540d00881200222101c0d08062241001815040b10300c01180c00704840007007000b600034004004003c07540140b030f00c07100484442859454410924110065 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 316085944 1250 316084694 316084721
    0x1e04080c040e1c030f0209030109060c0806030309010c020609030c030f070302100c02010f120e010e100f060b0403110d02041a010e0a080d03110903070303020d1215050609040f 77
    0x2124188000d09140c0251012510002c0280c6a910741241e44a0101c000104007401007540c0c81c408144031300e1190303042c0c40825101400030440d0145c2840c0031801098a01091000309014000003015460000215400e440c01030351410f8019501d0ba0902146401c80200b480d414040d18270101030070b8908003c40c426014142c00200070003444c60040c807049807101048202000041005a03001d40d0308504019031601c1503240408500d000201c918000740035200088c0815420000040d111100003e80c0421100a652080103448038100526040321210310404002000c18403007000400e00030701c0d4080300e080000e0b110581c600c45540c0050100d0b20451403241d10301e5626032036120b26592042d000202d404d03050350340808403400c15017040c1d6681318a194110406441e0020f18104802580035100401005802c4621940d01c03490085d440d070382c0d00084540083c1c5214103807420f00810b0700601c07548d040102c4507814600d080c5000e1183d11b41c44007a481d0341060711000400754040140c0719903400400705 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 316087194 1250 316085944 316085953
    0x10030623041b05060708030612070f080d0e09012603070c0308070303050604090b13020d0206030703020a02100209010503070309240501140303070c06081008190c2403021e0408 77
    0x14141034410314009604411300403042840302100148291003240e0f0080c40c229059623115042032011490b00a440d008596a1091410300103100e0742c00080242c0321304030380d85170f444075203941206110f6800824441d8a10981b6420610500b42c2d48180041e0442c0400406981c0340140d6915581107010a0740d1048510078070016140041c541c4c140315080d04014112010f1113115a42d44445660742006011540700c9203800d28924115a40c40110007012075000d06100d45900c1d061902030300a4201e034038500b0250190f02c040c4010202240f08651071032205840ea00e0440d19800c400f1401400307082e40031904500302698200883d0b01c100404801101c0400d404182581040700c01e08281500355145406940103001410009054801c2d410580d4010300d007919140d030307540c0c0c1250380c0d07da116885040700d0b010b0f14501d4403510004032510240ca81c02500026889513803140c25003c181701070301c007288000d071001404012403032003900140103081a034404030603415880500c030001d95200d6840003a45610 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 316088444 1250 316087194 316087223
    0x120403050d18060b010f0e1207170105010504050105122503140607200c04050417070614010e040506060d02041b030b0a090507050a11100c0f02060f1003062304 70
    0x10f513000303c1607124401e00e8a08202407100c0f00280c443c0302c101c070301244075001c190710350640d28408100404c0203250740b1001d14030070050aa0454000c04007070148034000d50804002003141c0c01c0160015907040501d4000b4001100300c1c40720911382c440c00c0500c9503000d4404032030000114466400e0451000317010b4014000c0c50030503840142040d00002c4a9000d00030013003c51070000380000c6000e00c2c0b6540305580c0400c480d559458008862003450306c41c0307400818007040000501080d980402415600c108110032a641c88008060b040c0000310b81c01042584600c00113a402c3c10212065102030384081c0000c248421200c02954010b40c0c2034001800195642c0044c0c3d0302450072240d07d1b002402203140030042360516081c014081d2168100d840e09000f00d880c0b420090301c0d41004920041404910204003925803003400810001446a0407001403042c10081079030307a4052103d1902403014410b44108a51035a907074140540114091800e150894411030350a4000820306c061045120710900040c204 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 316089694 1250 316088444 316088453
    0xc18130f1406070216090203090109020d0f03090506160303090c0b030109020a0206100303021c0e03030f0306040e070f060c0f05070b03010602070801050c042d08011a010212120403050d18 82
    0x400200709904562068500c0140c21000c050319178241c502c100405030b80c07603560380c20f5103000d0181450000d4020212205c806c050100c00ba402039002446691141e403803d55500402400f40202c01040c00040c2c00c080d16100003074000d62040e0001403088407014a540d540b0b089011041c0c000f6803007400d50035000a0b6651401b541406400c0d030045603105005219421900c0003035850014241001d902d44500d00c000e03000c1402021510004100103080700c0e600c11114038211100e40099540d98040d030b0510402611a8402090b03800c1920315981c00042030310301d008022074050f820039905562500e1741060340c401184040c002d400280012000345641c03545032200091820320300d03900c0104940d02d0001401404c4d1494021a0111031b0481030300c1e0a1011400f040201810b50b049408180764840040014540410340024541d035922100b0b8450960044006903141c0c40d0540c090036000e5400c000030590900c3c012040354025001c1d1070310301d0600b840340d0800340856444611101000c524a000c0f0010032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 316090944 1250 316089694 316089703
    0x13050a02150a0e120a120c05070b07061107051011090904121e0f050d0b0303031e01090c02062d1305070f05010206071110090b0f0601020c18130f14 65
    0x3c02c0070381d60300508082070013000741c450b202c48000422042c00103107854280c1e0b2189a4070102c0303681000c02d9402140d69000c0340c0c1c0c25076109202c121281800e10a00c24250300548003540e04203600031b00545110001e00459a0040201058010300c40c1c006116081d00780c2c640c06241ca20442c03150040809104200748040c0500141c100341d020304103403488000c8101980b19410410758002800e1170782d1a051001303000000f80400299183d011310011081150010000d209500c02140c41700c42c01c10b050340c90b068044162000c00369004051381c002070100d04480d00324069501c101c16011501c0c035003503580d04074180205c00b00740c5440ea58660030080d03131000e125003404a4002480c11a415940c3e0510781000030b034803100300900c0b600500c00c1c04513600c2141401409440b02d004001d21040082c1078081c603040c2d0b08100150b90002d2440c0a03032002400950002555920a880080801801c18400254104808001002d115102c2d004601250008821101c1203c245214030420410106881c1c591441c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 316092194 1250 316090944 316090967
    0x90e060603060a020a0c141c031b030c090b0306042a1d0d080a0201090b070906180605250807060e0c010320070c08030a0e010f050301060813050a02150a 67
    0x440c0d02c1040442202c0e50030051b0310307007a41e0b4040040c21543c01c034200220b081c51a0754004201c00a2420300c4e501d19640e140d800504074107507664001002d0b550121046086503085038180020690304001400442d804e8005180e0182d07005101040d110764000d1502e1300c99030200031300c0c0d4100c41e013403a009545a400400c62a184c1c42541180640f17102c0200c0010b00c0418140d801400c0880c0c009070700c0403480d2003900704030710068000303401c10b8560a02c02c0000300360002c0391166500113541e546020722444606024141107034101d54910781451f030003510381d8081e0111114205c41450310704649030f0001d11844e0141420078011000011421141d0305021f00744445042500d04040c6024215080001c0c1d00d00380c0206020038200c0e594031040d186c41e140c08110311541102550b44404100b1500c22644512211080d0703000b030382c600c810301658000588981c0801c2c00b414021420315070015265482c039a601c3c0c10701600641c111600b400a40e00415000f00a8042401c2c48080c0012000700003a041140c070300c3d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 316093444 1250 316092194 316092211
    0x6030203100203090613020316060e0316080715050c06070903061406030601170102041e0503010c020f0a030c240e01060518190b090906010e0a0219080709090e06060306 74
    0x355240440a00f40c0b00c050003001ba20400508085035030654a082004119002d49407007445407013038903900003174030003020341d0101e52007803290718100e20b5000003040d901e0781203981501c0201645814060412a032580d4514100e04001050001c0400c0c0c003020000b090180074203849a0f03150600f141004002d990b008081054904e6560041c03003103648000038007c1c119010381c00d00c1c01001d207092504602900c100c1e0b200881e15105981c9074066003003090203c3c02100c00c201d000300320039000d05805a803220540180c205041d00440142c00100b40181560104d451165090380107580300b550004809000054440494559800000745c100c41d0901c1580d000d06401c490b0060011021a0003000003140202880d100039410300701010000029003204840c034000808040982ca841c202d00e42d0369403000d2090b581107114038004200e0f0a000e0b07208948a00c222440060b1500038010001c4c2ca0b180307000781241c0100003a400000501e250144a80a00468044040d04a03400d01001b090b1402101034500380 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 316094694 1250 316093444 316093447
    0x9090109061d04020a0803070b1503010c02071e090204060206270c0409170415031b080a02070c17160b040e060d08190302072a0611030c010906060302031002 69
    0x401c1000b00a458020003040320141c01941e1184041090741c0507030303400b04403d44404178162041001c01c0240700d109643c04a40f042440e205801010300741d03111a016400542c100390000c3c0440003c1d11400e035040d90000360480c0000750f56070100d8040ba485640014010b802c202c050140c001520040006120148204100a10551f07180d440d150362502800521941e6100080801c020782d030b0b4141c901714541d40185548507507480e600c5d2116000c4174404c2c0c0b00000c0c90700e00c01426544a6040d01c2200f030056036110070705a03481562080095203d1041910480160309000940306085481c01c4030700d082d41400351251503121410b0418040f1075130007070300c00340340305000c1445506c1003000c00d56800030701107401d54805581030a0420700f520036030404801c007141c680300400740e49405400034041c0070300c0b403180f041c00650348000361030b10b83c01054070032603124010744020030803144121300c0d0903440028202503134901035042031050308548040504440203521480c0400551809203d440d500702d0384801c055 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 316095944 1250 316094694 316094699
    0x120118060c0206161409130e0607081e0c07080c1e010c11030a0302090a0306020304030c022707051e04031a070212040915050d2103091e0f0b07050909010906 69
    0x600407560240c04100f403174402180191003170390b540c0d5144850504c911400c001d2690440c0c040d540343e0900306c42840c0400c03032030390124542c0310030402648071030712020748464520b40b103000500302d40703034010401620b80d4030007446880404202030250590034510b26003020005116615040d080d2a6400e1009040c050100c624940c000c50200803941c420189103801662140c20000140004d00950000352090748080104820142c01070415004c081c02203640e404540f00003005000141e256821054200c1d0b18070700414141c9006401800801c045c028801160144a044031030b03035900701d584141e03451108000c40d0480034480910294101100d4400340503c00185240c060003031246102d1414640d980b91040c0301555007004400000e0200186190751096050a00d0b004c50807943c90300070442002d075817207100f07024001e2140782c000540c8480300100c81510f8001d0100480d0801e402500c00d01c4010165000003044101e03901e1180d03181c1e858041e25070014206210100340147c102410b0300f454601c09 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 316097194 1250 316095944 316095947
    0x10f1a0109030507140102120c03180405090c130605120a02040c030e0a0813050a141e012304050409030503180a0c1412010f02070618020f120118060c020616 69
    0x80c0c90075a85d1891020140c0494a00102d240130003066406440040215072444190004001400051006002010140f00c45002c00c0304070346043d80c00031502e40c0104e408180d241044d1420798101030604200240c0b09590b2800b2031100d040708020455550000d120100451925106140c030b20021840e0030072080b0b00080701e06035100c201ca58090903408001c680708685442c00c10f5008082c01029240700856980d415039600c1d0010740c121050b200b109403031408408019415513500c042c410503521000104050302102c411130241800007a60180100000308450700d9502520002038442d9990583c6c0c1d10300951119404c0c0d5003040100b4142e045001444085858140c1c1c800035905030900d90000b401000001400401050100002030350800303985418001c900d6015141c1c1c1c5000d1041800701d00c44000a005051412500082d40007a008645c4065400e106185200f0388080c84000508200400003038808000001130440b01d05440c0c4c064402c40581c1400a16009482403c440568180c40c00b030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 316098444 1250 316097194 316097203
    0x702070f090b0a03200316090c080c090f041b0e1206131e020a0e100602010605060a050723031e1207030b011202030915070c030905190503010f1a01090305 68
    0x2e0080d905d520803e10036080c1242940b107808500504540c0300d25281800143c044001d8852840024900352902c10468046c002300c601c5810041d071182e28021040b0104100c514401c082d454000e942c2d012404174106260ba881041000291900c003410815042000b408141c0c1150600550704208144080260321165250313032640d001c0300c144610b0515035480704100c510a03002944c030450400b4001240c0710b00540c0a80550b00d070300c115403070341602e861082e07003a94100e100b00c58001808000000101d446200a00f200740e104605002c85500c440f00b50100b070700d60b1030341101c3c400e40000409210480311910500414940d540e00b0504022512008a000c02c40091003c018141c0f10404162a030f0701c9001d103440301c6440070308115160305000303070040ea4402841c001c10110811a1010801040c01545446140da81c90350794102e10a00342000d100102c289500354500484c850000031a0954003030048821860102c200043d48100040380560600ba8034480d85060107140c1b9801c1c0042400401e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 316099694 1250 316098444 316098449
    0x3140f06190207050a0f051b010e090a0e12092b1b080a03020703050c010516060f020f07120e01110c01030e0a0807120f080c120403170702070f090b0a 66
    0x841081490880049001c0a4454160000c1c4240101281c24040107540c0c22028056406101280c07030b08036603560f03800f0742c201e05c40c8407050204001000e02c44403803500103801a405143c0f2000401c0c0340041a5105161080322218201d020401290807c0681840442d08400c0f03020f054000b4040d9150723052203042d201c0d040384094041c0ca60044040074240889049100905941084481c41c0d501818002d40b9600319020407919401102202d000945c0b00d2400e40c1c01d868100d00001030296803a07038507507009004c03816981a11640034820104055602d00150090700c2c01440c0703407103c450b11500e000308092404400d40d81030000412400d41c0306080002c1d08080740341b0030b007000283d01d44580c00c020b182010320b84008100c050001598000c0000c0e28128001101c480e0302c45043e51141001c080d1080302040703400d40354030241800102c0c2958180110260400d01908040b00801d103400000c1489050885d40140940c3c800b5000b0401078418010500061451050400c900324600c0000b44100c02d0740d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 316100944 1250 316099694 316099711
    0x403260115030603080d14060a050907181a03090114090c0105070303020d0207050a1202010c1b030e0315011505070c03031815030b090a050403022e05010f03140f06 72
    0x703421801c15070196209102030364001c64841c0e1181c007100084005403001d80240300080503001d010401c0c908004004030243e440007058100141c0e5032200c1103c4140504c080c030f0720301c03a450030000508140340e00501801186080c1d0307000e81ea07240c10070015081d40d407a200c0d08040c5c48201810404540340210781610004400d1811070b54680c55820100c0180c01250000e4450620026000c404c000740040d0303c1d10268801c2c0b900c0181003034001d00a03400c0f20b006201c18408541d0006e4040031103080000350a240500c47c2c00d10900c002d00300750100c2d1900d04400c202000c91000780006120010149d58030035545000c600c2c1161402006540d07075080b01000d17100060510010000008150518180c4ca4001d041c001c200d00095034050103006024000c890f1031540103904180c04910800102d004491169805800030400080c0c6100441c41e1030f802a01180c120700d01601c01030881054600a9500910a100c010103136241542488542c08000b520f1214640e40020355a4448010100e42142e000910 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 316102194 1250 316100944 316100969
    0xc010e010f1701180510061b02010909021803120702300a060207020a120b0f0a0f09050606030705060a02061311040c02030a03060b040803180d0b0103080304032601 72
    0x10700780c1c01c0e00c000e4062011103020480c100d00104564500e60501c0650b850080014131013500c51510320b40b03440a0398001d100000d0b0400e400046002c901c06d150040840c030614000d6100c80c1e440110500701c2e001440442c00c03c2c219074140594500e401c215801c24903110150307103840c004141e40001c0c001e0360a02040d544404c121004603111000b081c00c0b010079410070b10181c8900005a00e818402984466404c900c520311059020405488100040100b5940071030500841e0304d54541020f25000001c1480c4804c030384a1220134000c03049405401d000c9441781004020506000b400c15080010340c2e0441070003140b0902040d00090f50001d070045d0400e0102c0f001c00b00074903107818503160034110004c1d9035030030908003064141010f50000081803554806e650030006151680400d0f400d9101d6440b44110680c802e204140400089138626414090000d0600c910034810b6520200554402d034420340d5883c0000c0208400d158014001a812845500300001481b0340000d03d10b40004044c010b10b5020b240 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 316103444 1250 316102194 316102217
    0xa060e01080414120c0d0e0a03080705120f1e090a17031303080418090c090c0509040504060207140601030f030507020613140a050f03101509050f06120c010e01 70
    0x10000900d0b10f00b12a40b41522144040101d00d00069400082c440030b280c1300f004402c0a88a100e08440c88180400601c0340c26064030319100d903002074120b0b00701610940030b0040d501214804e5600103101a054250249840300101405201d075450300782040a5200c108014040c01a81c6d44280b60083e00e5080302d1545241c004288100d03d107014803101c00d0700c0506207034404030a01801801a0040340c405c20412004d651000415405440642c1070080502a004000b800003007001e4101030103c0ca10b9140c154240001c0078005020740d00c0541c0c094034903550010392a018010a8058103c80c010682d0003410194034554039031304008502e1001600f001408a46201155103c0c021600160091544116010b1710340d450204030520b40f07481c8910542d04814002000e0600185024280c000100580090f1042e051440080c100080f0ba0380403d010801c00802c0001c803e214650040039800242d0b42245000c20078001a207514150095a55120000072046030380e020300c004811601c00c0c03800204802 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 316104694 1250 316103444 316103453
    0x503120906070b13061109090105030c0108041202101503030206070c0b010303230a03050603210405040b011b0312050604060e04030c050106080f060a1103061e3106050a060e010804 79
    0x4c10700b0001c25107170500483c440c0c0b00c213007507000d415001000c4626a019980e9041010ba82e8104484124081201000000c0110740e16000100072090b840c01a142c2c1440852400401c480303c014000041215440e414414194100300c1951300c4041401c5c41e5405140648480d00c1c01c01e0305120040800052410b289080c2201c0d00b00c0080c0b200c2109840c680307914420780c0c01303400b50404845550003449840c0e00c00503c00122062909401c40112406150908010902029003950012241807007003a40d6442d02e440508200c0f1540b1600950b181c42d40003540b034410000f6500c0141c00107104604001060101c2003400008a17041949410a0794034442c3d81d26006024042075404550180904e805115141c0404a64144920b0206408001c1d0803a0008501e01380d000596103582c06c0203907400480183e00d000360510240d040d0003880c072a040c2402c0b003100e110314490500790f030b808281e0104000302101d40f44e016a0011340340031242030003c141458002020410700081c150304000b0300f0f02c003217418031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 316105944 1250 316104694 316104721
    0xa09180609090803041101141b031306021501050a0e01050402070317100e1e1810020301121509021318020604030b10090c050f0307050c0708070503120906070b 70
    0x20481d104060040d038415090103503442e0401c50303040d00c0310084103c80704400d621404140b1050317402e9101040c103058000d00c04189081c2035149000076403008211012034170107219455001041d841d0300601140c22000042e0140420603407045001e101103180a0040307900781030f11641520410703140181c80c0c18142c28112481100c80c41c9a02028510405101060f0708131a285000e40b41520190009078540c41d240100150b540701d200c0c44100403c2d404201c14048200b101000b800c042000c032080000d021628104030380c4280c0c058803c9070100c1d2912420005800c3c1e9551600b03042c9241007016040907000b00c1c269100d031075008802c003a030740c50210750046d0700e05007103c5d196600589006c0e140c5407280703480c1c0d010540035104a01021203c00c00050280380c9802184411100b90b500c0c1420488804402042034002a19820502009001c9c0e415801e5013040f001c0b00402012004012440c034000c107150401d00c458045820b105001c00c20b088541d1034070000c0311baa00340c1c020942031903583d4981d10312812 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 316107194 1250 316105944 316105949
    0xa02090316230108040807020d03021c030b31020f0c0106120b0606030403050703030203060d0501090506010504050a11070f030215010e06130b0117060a051203070b0106050a091806 79
    0x12054946400b180340201c5a03104004902803240068a035510280150b41103002140e00410700803041007005d0042c280102c098654a129004a9800400f050722000001c0361140d6808002a5284850003413450031212043c452624417011000c1401e005c400300f070480060703c95601680d81c0001c2c0d018106184c50080710010303503959000700001901c90b82d10582c94459010140c03180700b21100404c8192502c501201c1c05103074180c85961a203905030780d00340e000e03400c003c000690000216900d0070200d4028025034448611070700261940e0b40c1080100011107201812180c4810300d480741c440b60095449048130059900403003015510503261400b00d01e00308244007882c48051081000182c0d00d182c46105500401d012625500d00380c0c00783c032458044421550010340056502e20040700035000202d82540c121001901f5144419210303000300d42c80c081e40402d01003030b40d0b10011300c460a201401e555a0702402c118900b1074a030804000004140440c2400f80e9400c0e0044208006140e1415078002c000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 316108444 1250 316107194 316107223
    0x131b2a11060705100b0307060f0f0e04051905150d020f03011d0d0e040506180411091303020f0c06040312050d0513031e05030a0209010c0816020102190305030a020903 73
    0x54400b4640781054403501c140440c40882070500b550300c40340c0d01d00403500005480c400c0d50b80e41c0d030540e24403c040b80c01c140300e6075000c01400010010304416481e06c3c00307001c0c801c80b0310b4802e480040d9818034a070b000f100c0c0020000741444840d16421001a903403403a0b1804d19035011200031501080d050002801080200c0c0e0b908800c2c0c0d45a80071680000c40403039400c01d00803260720b44500102062040c00700b5030390300f1113041d0b40c056081681009510300c00e0300b0721398006001d081703400d010300303824400f003046510b064880100c600c18801511041550400162110a8002015000d48203040001c41c07013601480c003000345424005085e00c003c0611810a480c143c901d14407051040c0e040081c050040c0301c410b0401075001450301b0034a070800300c1440d9807558280b0700d981d88061440c6e80f450710220003034200060a80c1009001d210210108016501500c1c2c4007103d04000c001c2010103200280c600202c16001900a01805034035002203500305081d698030400001c0c015940700024400a8144641c0144001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 316109694 1250 316108444 316108447
    0x210207020418050a0510021e0c0307060e01150911030606091305040309030606060e09010911120f100f0e040219030209040308091204050d060c0c02131b2a1106 70
    0x2c0902400007000070318540240e00740d0303102c92803041074681a403055240c0c401c1c42c0e50b040314034000391040b03146c01006409040d0302502c0c201040b40d9110415581c402001e11844d0b07440d0f20100c0162600c00d2113000c01440c00c03081c1040242511500110302d8040104240d02c1150f01092812440d2500103410b01146103c082c10040e92820340750281891041d40801d40d01d0031318204c40803c0079801004804440d52000703020742d80c96840c140c0e04401a2014402d110346d51030f401d01a451058140440185c001ea00050190300ca03840c014820303031400d5035268003020310426045020880e6007107400c0102c1e0071070b80507640c40c03601040203501d0a0700da600c0b030707400250006c048608020916600942c22070040c8054415686c1d404c80549003aa1140254020f5030340c481798115526002401941c020f440240c0541030801d82a00d580e00005c582103071100000700c6054407070003083c00c0c100b400e03204076054100600300784900d002d03613079200078108040907158804080c1c1402c0d85d400344001181c0c0b10207200340090406 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 316110944 1250 316109694 316109741
    0x1f0507050705100606140304030e0d080c01060b0403120302030c0d090503040b030c030a05090d0912060b0301090c180c050319060503030f04030201080907061722080301060206072102070204 83
    0x40f001821244a10400556440e00780b000307030b03d0740400322401030350140d0f02d41012000000400240c0c0000d10710131034455130204800640310a003030003424001d01810000544481c03a41c00c160401035084c0340d004003007600c1081001010210402601d034070601812000801035000e1501d0780ca14825504000004840442004002c9102000844c070a80c4108010711a94440c18507a5554001e1751030040040751400005014600781000101c003181e00911010640083c204c0119007101c080034401ea68019129400b1b110910b14124214210322500c0820415982c0342a001022804003911614414080e407020b200341416541041029140c010256a130f030340700f808a2852507a0143c402203000c101d202002a21507440421007108550380d03500e40c1d0b1202e4100700500c0365003840040541206018555070422040f400d8028031030014401c00741160740754101900646070101c001c107032600700505000d01091400200050001404481d00c0c05621200d03203100040103881f80005a02d0540c1070008039 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 316112194 1250 316110944 316110973
    0x618081804110f0d090b04030e010f1b02040e0c031005160503041104020a0215010b130b0307022509091b0b0309070515070b041109091f0507050705 65
    0x3003903000c49008462065400000078001940d0401d45000015001403003415402d0107070720010700e40c201c010040061148404d0340d03241c00c61070303040d40d003a400140708040d10040e950f000501a104030f1403a00340481081c088000000c481e0622620090090b500e80c0c0f20300070000010480000180e0000341506d40c4082c94406006c02410100d44883c070810300251482240390285044901464011060030310100c02c1c4000c0c8006036100259030300851103940c200d2500b4400e181c0c50540070f420043e480795603e40c0166001c50b0818a01d40005444070400c01c18045410340000d1440300740791420700101140040c041c05440700f507910f0b07880500b0207414810b0300000c005013040d00607001010041102c0085440300503009480c0070403180015907038031100c6c003880546082c0c840c0c2c0c0c070729850300c000b40c0745030184980c0c40d81f8032004140c40c02c84489003654156000b5262501007a03038000380100042800b542d04c0341038040300308481c66584902c10f40c1da0300071990b8140f18404440903243c004040f42c1d000da144e03401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 316113444 1250 316112194 316112197
    0x5010f09090f1e0e03070b15060406030207060b0406120b0a021b0c0a060f05070f1106070506040614240f0307060908010501120f0312151508010504050103050613061808 74
    0x201e481d40103d0801e0b482c604007503c0c4540450700c0034000041d030400021741d03134544038041d01034520222130a5507400c52a25507552001000a07200a0340c1c00350b141d41c1603151030340030f850690003003910490070300005012000711aa20011601d4003e00011840c0d2a440340c510028411240c410b030744070744060315a1034245c01c00079500d150701806946107699543d0359901180c01c1001220100c000070b900b0030440d00403814000e048090540209806070306400000d0005810b688081000c860300e4010f2420001804407034440c80403110751800c00400e10745040707500c924408050703000e0740c11428003200d0741038070907240e003040d108907000c3c007030b0448100949664014140341110321520095600b00800406c541120803070030031080381c1c04001c044182d40243c4c2e055170403501c040004510703c2c2c0d480444010180d00a070b00032005010070900e00c1141c002512000f0a03078401600154081e03820040104000740001490a602101030700c44410318920b00e26011010f0804841b81070390101c514030820301480445030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 316114694 1250 316113444 316113461
    0x70c02280501021507140705030909130203010b03060708060d1403030a050103141b06210a0b030f060f040b070c060204090c08091609020a09051f020c030a0c05010f09090f 75
    0xc0841e8076542102c1c510104000c022214000000c01d20043d1b550489805800f620300300b481780d0243d0381880e40c08000300e200780c0c50481c1c44240703020859015805504082c443c034250902c060307000c2c11152512410240c020315000d003400b406901c099100c030701071042601c0780b94007502c000300076a07550341002a6580301800080c081035400c40402d58003060303a00d5000404c0810203201c0b062080a11155808200041e0000340080c010307900d0b01402c00b01d01d0002c0710b0700144107039440c4000041415190301458a02103075014540c80550052050003c005140c1c0e02c420b901c245e1000340c1c1c03207490366098000c807100c4c44d22031401881c4030700108011440300c0701c5030032030011742c605542c1c2d01007240e80302520542d4956420b40c0200001000c4241032001c1145e0341c00809100c8868104020600d45d2540840e181120352020b412082d03805040c0781c82529410702c13810b0310f00c00c021001407116904588400d907450009214a50600281c10b84901095003d41c0c540c1000744074040302004000d1401041070090705d84403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 316115944 1250 316114694 316114697
    0x140c0c04021204110a0f0302090712050712060501021203010b030703060510020c0315190c0318061406010302120c0702190e150a06050d110f072a0509070c02280501 72
    0x2ca0024135541403009000e4112000b0441c540d00c041e107180c00b80224044040c210400f082005a036210386418503001d00b5008d241542c0d0f0303503509501405440c50846409801c072504541241c0ca02440f0b800c0d004043d00d042d203842d121703440d6070703a211a0005d44c0180702540c0495000740555024440003038002c00c1b408a494002d609aa20030000c40c11141d9007004c089030344400d000e0190b441219003100681c8502085c10309400c0000750360f100f4410030315a88004000445406480e4031040340ca01d000251480d40040b82802d040d810260401c0c40807032980401492403118550218086055545070381c1c01156010080100108841d2144c0d01c10001c0801110b0245c00102002001c2c4000d042083d404011a0240d60b00c0a00344541c2c400c078440540042c40489414400521000c07079445001c10044c4540780c07103640445080d02da002ca4802024525400100448100000810990f01d030301c10700a034040f1562602034140d1003148002244601101c5c0040c600e03041001c0314241506001001d041030310001d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 316117194 1250 316115944 316115963
    0x1205010507020307200d15020a110a020f01080a1808030402030f0a022422080706020d080f0601030f050a0203010915030c0314071a03010f0b0307140c0c04021204 71
    0x2801d0301030780e80384038105005100c0c580e0240070000c042d1100b0301d2030385800c1004100050702906501e86449121340003400f030312001d50007e00004c3d12034101004000044100c400307803a50120030340008501c80149210b860620241400144001e503e643c88480c01d610a00e4007000346103846d0a0000541d00201d030104d009103c1c04901e425a00000906004015401000d00410107210050558000030300140200d815906010006290b00c83c24040782c2118110009040c02c94644000c0074507000241e4806d006540001403559049a070004e02182d00000d446c00c00446a150640100d004112410010050500e8101444503942c2c10b074005504a0350308043c01d00083d040c14410202c40341151100070b0225262440400002d000300504040c0d1199020659103078569610f51401117083c10900160301402c00001448091001302491001e840101041030a6180c56003003d03000040c485208d014043d008201c5a685000401013410b0f0818058030541d1103d1081d5050a0a42c4040e94111a00b880 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 316118444 1250 316117194 316117201
    0x203040e0c031302131413110919050606070f050a06060b0f04090b0301021309050405073006020904090803041e02100f02030d1b110d1d030304030c12050105 69
    0x1031101a00e0080f603c3c1c0d1283c00b20081e2607400c02001c0d540290b2031182c415196042e51040600f00c40030307284a10410f01e00d2501e045880d141101d107c4c803a64044900c540d40000502009591402c50320034a10440e03017002030103403507440c0013030f055026010008000078104011101040f4000c241c1d400b000e40714101c18007e45468454810260091800c010040b10051101b08280f000310b0f00014001c60000c4c00051070842030f408040801980d503042041026104d00501080107820003c0d00010091208207400305820b4111110115017003c2d91280519502c0d00c1140a000c1c0759411240f004000800411410041c2d10340440c19401c00c1b117007501c014048031001141c5151104091145070381c0184a0414040c00e4503058031440d481c02c01c6c220461009110000c40c100c07140c0b00392501c400135111440360f8040500d40082040b010090b1846094014500c194015900312110101d039681208010640158420201e4554051588007034042c0c0d8948a00080b42c01140040c60b112902400007031166a4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 316119694 1250 316118444 316118461
    0x1506020328020309090a060515071203151203111c02010605151603090e01061e020d02120901021002040b0324010f03090510110c010612080a080717070203040e 70
    0x41d11208200241c2c2040040203841d15001c01d10355804035220400166568448000c61301d41c004245108250303010004d0f1a0301032040000001002c40002e203000c1c1700a80c04583d4020310100f40744242009c803045484c3c01420507004a030031a082006d0748080350b01400152a003000d00f0540311000e003025505e4408089040e08204d110070308203070000c4014901d4505400030404071f00181c1305054013000350b0b8143c040307004649007481c140207181e90390321041d070520286403130907144440940140566100000880c0d200340c021071401020342d408000f1a8480c81c0d540010703420b021041010f04100c5100180c080380142ca003402440c06090b0f14562030318a02d00c18844002840e19004642c8d021589064040a0301d038440e8000d040f525118105942000361414401025607481403050741156501044884281c05c3c2441004014028000031501c200381503101c1001b07d03c90480e0203420000f1302000100c416016081503441040080001865031a204200a40b81d80040c000d44e203400396120086070300304 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 316120944 1250 316119694 316119757
    0xd1106070b0405160e0c0316140d050109110309100c050d05092b0518040b06130612021810170112150608030a110c0d0f050d0f0206040807020415060203 67
    0x352043d040c120303e59188e8486641d0752140645100b0f0820074008103903e11030307580300c001d40405120310a001c0f500d5410125040155a01c9039402d1798042d10503c00c101c4a88400901c0e400c4145000400041d9080e001d6421202c1d80f04000b02c4240c0d040c03c0030140310b0508000a15080030b00d8020b2821083d990344640c020365103c088201400c0007510501c9010000d0b4545000503032001070080001a12001c101d01089181d00712400c0a01452200f2004014441c1c00030f4100709041c40d0b81d0000c605c0c0c1400040005c00c00b404c1d1b00340c1c00f800382d01250356214151b402000310b05009412a243d403140c45d07969100ca0320080708250002c9500000940488a550045000303940640f510300b0099400c03c1c80c122411200d190b046070b1902e10138407070780c0080c0c16075450743c22041101b18020002c40001c80c609051040c905039a602200040208003c91404519030200e0f1060f049588501e04654448140c00014043d105008000c00c02c60604200040c42c540c000000309144082d10010f22501d00010b034058040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 316122194 1250 316120944 316120951
    0xc05030d150f05090f040303150504050403020c04060b16030e060708070807050d051215031c020a021c0807080706020f030c090909010912030e070f03121803020d1106070b0405160e 79
    0x80608417808140001d019800c607003644a81080d107001400d98540010703040c2e0308191425030141c1c004007159461402c1038003802001c0e21204031002d24142031107028140d0741101d15406010864160010103141d990141101e8603660000801c1d0348500c1282000c1e20581d022102c112064821244200e0005000c0d800340d6100c20241e4603c1342c0d281d52001c011107000c40d803541c010795060162450702188000002d4004445400380d60040103514641d1040c040203042c45014000e180c0c41040702d5000040d403400844d01003e43c00700200340c841c0381c41e1030302c0000380c091042c8a8401c1c82e80442040040c00f100c40280403234071801c950f002120b031105082e85080310006a0007030005030540e5060f20300c40e8045c6d00f003585039641030811103100903565003040c54240c461b40c00c1114850300840e09400c2c0c060f44910401801044004d050340702d9403440d4009a04642c2c00303040101028030040c0e00c0803160f81c900080e116800e0300709414100794a45840c5c03058640c64655a201000b0b800031030041214a81502c44610 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 316123444 1250 316122194 316122211
    0x608070f050904060e190605061003061a090315010303020309040f05060f0405070507020a140102070f2909031509070605271c150501050906030307030c05030d150f0509 74
    0xb19101c1d5242c800103003502c045080f92034440c1b100d012960582100b1011513060250750005040d081580c100240030b20b006410008060403e441800300744003000801c604c02103003003807440d03481c040c42c40030030f062181101c10004424a51030002082c1500400240103035001280c08005a40c0c018802d81c0803074109480c00f68011402003c844201c1c103150707019a4020310242422810130581d40c0c0001c0304026280c016280d09400c10301002c1107541c0402140010301000d4030b9602c611424160391540b01105000b1000c131550060901c00c4203104e07000c088581c4820040c040d01c40c009069100c00e8051402941c041d00d0324411a17000003440b0741b091040d51400015803800f1207050aa04040c99400202011410b07406035040c003e0b0b4017481c1c030036620070504502c2910411007021101a61000b00d60050313000034014070480f4100410361341c0103c01c60b000c81da490b0030545070340d44113428820f00d0350068512048906140004d014a030303048048043c000c480d0070300341a191090702e413010b018080c402038480301c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 316124694 1250 316123444 316123459
    0x8030105040c091d0403030b1201090b060429040204031703041202033f07120b03061006210e070810022b020c1507020c010c05061501020715030608070f05 68
    0x2401e1303420405805420600900c0c012641404d40c00020341241c1440100c0300705a0340d5000c0010800214100a40e07201c3e004903030070025051180640717200e1492264091801d021100b041c002c940d0303502d6041c1e0300595000001900080050744400340039a0007514280c0d02450b032000380c1c900c0d9600c0081110441c0106c0e00800c010902c05801902c2e0041c0a907103600d40d00c0c50003042d014245881e1450740c62292000b941c031505000380300c4150604803407100404034040e8000c20200300d22140415900030454a29143c0000210f00c1080500d03d1080e805441040140c01d203030201c0c0b800c1070005500803d503143c900c2600c51454039404458101c0c07040704482c0040984044944022040c2c1842a0a030009590000351030030035144002810300130104d920076189090b81c407d000070554104030050600c0000c0c2007003544038050742c461541d5440010f0118402c40034949041c011640b007804004000d240c51400c0501403000300c03c0c058007070155805009807610070903000058030861594071204561000e0100c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 316125944 1250 316124694 316124729
    0xf12080f040309060c11042309030a05180d060912020d03140402010509030f01111207030507021005060307030c080f0d1d090c280f0302070305122208030105040c09 72
    0xa032408241c4c585c0a40d00b0030100618901140c907540100c002001160140014600050200071400701c005031420f0290380c024400076141c250000212603216491321225030190210704005810228003000080081d8106000c0000b007111140303100101e44903a40030344840700b0120408034101c84668074101c496102d400042000355001d08001c02181c54050b0644c0ea02000c41034000d4207440011f4034101819038000381c1d210709486600b0f052500032403039113001c4c0500c6c109448000d43d00c221600024800d55a5440800c0107950200150001990700039072182c146566060000c2e00c2d01c0c1c0c0c840c000d00e001e028100c1040040c0d80b260030741280c01401e080c00035030700000d40d000b4481640c000500108411760f00304031014281e9a51071031840d1649040da907014508880c00c3d0010b044070102c0c98800c06050040c4402800130f60410291882c2059502c00c1105550f1208210070029948051441400e8000c000807028801c11034019410384400fa681880b42c03c21030300044880650034840e03a01c1c1c511800040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 316127194 1250 316125944 316125947
    0x1063002060f070c060804050c0603010602030d0b060d060905090d0e0a06080703060504021b120301180b13021605010b03030702090c0a0315080a0506060409110d0602070f12080f04030906 82
    0x1a0031080d081402e0181000c41d56070750040342843c2c039004140413030365220400040003010131191422500c00c0d00c600e030030b42d450300324081c2d524081e02c90307168002a00c82151504a40b01e203401d035a80707641d91170004d10a1039a50001d0000910042d00c03c0540d90045102c0000d0b0603001c0c050504040e40040c0c5009070f201d2074040d044540280140c07258003015182da4001a1130341d01c0380060603880c4030b201c00045426209940b050315018101090500404040c070040224550929442180e00d14403038021502804590020b50f9501c9100c440703807000c92003c9103020840c90f1080e94400702d0740c410300003000014010003c2660341e000e4840029800310320140041d1050603c0005045004050b00b0003040401c541c1018550b1801250020140d170751010051005100081206507001002038408000d9108582c403004200000900e94501a500d01d108203810030a050303049034800d0350050f10700d8405c17401601e070200c03c003041e100002c8000744000001c641c2080343d504c00c4a0145502d600d506000c60b00c4e0800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 316128444 1250 316127194 316127197
    0x1060e060705071d07081006091502010f02030709031403072f03100f0b0118030303090305040e3d0905060f09010305010e010c021906021b0a050106300206 68
    0xb01c07018064500005130901016121011140c00300c81c44045501e0285002081c2020080c891502100d03190820803089030000a080d040da221078450003d1059103103016805003074800000d40809200004200c1210b50000104054900c1210a09110180d0925a0350349005100000c0c1c904556207808002400c80c00701c0d24180484c803110305418040004002a0404840c8658214442d881c2c0031403000d440c44038030038408170a01c00d0a0582d4600d11100f400080e007090740c0001030034143c0c2e603924242814020310a44c1c005100c1081404928904603208414a0700005000600035503912040410303400e0041c000003110b0240302001d4101c0c0d10741800603016103400b07008180c002c03041d1144c01003582c5500301c0c03990103180030b02c00114848030085081c3c1e0031540071516140854221080840034410701c6900c08070700a030400c0006d611780c07910030070340722409900b011203c61a205000b400402c0200641010741115007600038102c0c0300c5146214806800400c4101a440140203401000145003440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 316129694 1250 316128444 316128457
    0x8060c0304111305101508061905030706020706080a020901170402040f0903020307020306010512070e07050f0712090605040b0a03180c030f0c1a09040b03010e10060512010501060e06 80
    0xa1080c08181000480e280040c21a903ca840c641c0fa0820030402e1051079490000030a02c1c0d4511880745028000b00425551000c1c3c007a81c4940300002800a40c1d020124002001e060000d041d10f01450b50b03031401031741c0d41e58688a0000070500c1d06002440b4000e8920a40b00040f806858885420a02200c2c07800600d500400c101d0340195200ca80102420041c1b203881da085100303400455070303103080c1c1c0101407030140140c4c04030380301d443c83c00c5000001001c01f00b01c441c100e545040c0c03020441d8440300420782d024050031035103800300e41000c00c54030140180242c68000341c03545a1a1a000341d13490b240116014811342c00707141a2082c040040040b03292213a801078170084100300440e007003002c5c117681b4540e00d0000c40c1d00a54030300640102e02001d03c144001d00e0070040005182684480811404ac94854007038150018032130f42c0c1d00c02034003016403402e4002c4410310b010001a03585030300c0740303401c8003004204601919001d1004445804881881440303014143d80f91922010049428601004880d52019 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 316130944 1250 316129694 316129703
    0x5030a2a150212090607021c171210050d020d030306081204180b0312070c050a080d17070206070e011107030302010507110c031207020a030b070e010f05031512120f070c0f08060c0304 80
    0x5c0700001c000c01d1502149c61111070003409640e41d51301e81d50020b0700301e0820103401d80813200e68610080203165188001d0b28005581600c4040f4030a02d0382c1400c0e80200b20b60ba2144680703000301e14810140d8070303000f001801a60311021100e945580200702c44d00886002e002020781580c05680902940c1e180c400103025600c7c414010003007860745841c0400c41481090f4007480440c4d10601903d8001500140300d040d40703440c080c082104600c1d101074008d640380340142210050100044840c5050b91054110865a0390081d081714000d550340d00d8024000c1100b01c40410000f002092060b090107c040380d103445000008000b0404101926861440c590260804030392208444000100140704810441d200300c1d1103480780350740c0c00c20780b000151205003245c10f14010402c08004200c1a000290b1000490200613a144c5228848162109184c04130b5020300034400d500c04602020703400103040007400d02c40e00c507440b020b2519695000760182d22810340110b00c85904054009800c9070004005541c0c800c1c000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 316132194 1250 316130944 316130989
    0x415140c18060d15060206130204021e0307021b0307030b01031401020c07080f06061c060507050c0109390938091005030a2a15021209060702 62
    0x22407001651640c04003070025501911000c50301d030f80d030701c0184a04006114500281074030703180c451000d07555010003000080c411640800c80390050f8803801c116010180440718516a03a0814000196580d0389000c00320034080c08448080015003804900e86088a40c00a000c41050f42199a5140b048141e22521021036500b4092004104800c01c40c1100601d6884003400b0130700ca68207596400c201000f00424020740d020080504a00303401c060344c12965401102c0020645c03070b0640102c0f051300ca0b500e200700b91903083c50030034010301100020601009003c18803803c0782d035101864a43c0103d41402c0e05440042070030204001003400307900170112040380311070340b512014424605440c0324072600400308610901c1051068680c01d2116820f0781210560a088078807618010010f9600c4c0310030318004040392000f40c00e24008ac454000640380c07070006a4172000400740c4402c80d052000202c441c1520061082f5601c40c140d003031a100c100c0d4440d660142c0054038183d82d9030288010300207680706c0e01040e69503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 316133444 1250 316132194 316132237
    0x4200a032708031005090c12100902040b0a08180a03110309041104090c020f100f0605030d0e1305090d0e06070c06030b010e040516350415140c 63
    0x1401c0751801072252103420000d44030b040c1030004000c1c10710f003508070760301032101101400945001841a242124030003034005400e60b4900d00310710201000ca501c007030403081c000704001c030300d0f0541440078200b070000359030350700055a1b240d207448078000301ca00341c00ea80141c010480340300c081f910075100005561466021240740980610204045a880c0b1000d650064000720f0700b40100d040ca0700078002c00110510080800003000340b4450703162202403074040d121640e110316800490078660405001008000d0950340c14512203030b805001900040d04031403180c50040c1412550004610604d4000c004d0403000340301445002c0401c6d0b50788a5901052a40201c3c1170050000140c4502d2140d00685607030383c2c0126005a00300009018452001021445541040d007001903084a11031561800f1201d458035442040c00030200c44a0038018501c0d42e0845445500a1007141c041d82454130300407803051180700302d810100e80e6020100c0c0d2a41100c184940b586502040100340c80d200a000624414031080020341c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 316134694 1250 316133444 316133501
    0x4110d1a012a140325030806031f020c07030c030501050402010206130c231003060509010512030d050c120c1317030901270810050106030b03060c070f060906090204200a03 75
    0x307401c170744110000d403403005501c000c150388900340300e8000200703600810504925007044d4003c811441c0400728499400b0880100741c40c000c200030002141c0010f001c0441e29201d0030301601038002110141c0c094864100407072030100d40302000c0f804a40c1c1202000440700c0c1003d0003500404146010300301e2f50a0b446010040d6551801070f0069981c03469240041c04920305001c0c01120f50b4141d0200b0f1141084911690f00304001104480c45605000c10014031a44c603040800161701508441d02e000c010f001c010441982c000c03100400c1004030003224020300583d101d4221042031612076485406810034400038082e075003d4004207000c580103054024501205200a20100c241a4460206507101171021344040c82d1034400d090240c68140b600b808100c07080c0340440e070303250b001070041c00540000143d09020701c02442c038050440740d0b2201c01485051558200840034212800d01a40300340e2504031004400c0724242e04180700740641c211118140942200150020032650482202c2c4a50301c1900c250300c003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 316135944 1250 316134694 316134727
    0x6010507200108060f0604030303090c1d07090b1801030218190603112b23041a01050f12031308030714060403080604110d1a012a1403 59
    0x3150040d403090041e0038428001003c52001030308a030b0251005502441550700c0e06011a01a250542008680c0d100c43d032804038490800ca500140f00c18000045003000411588803050090400c0c0e911944003944507140b181d010712601450300010304041180d007aa9500940240c212071440121100306509028089010404194000e04031040e031500d06001d910380520822520765088854a03080068140312001c4c920520041082e07140601411540882c10720340144822000c00300d40c092000c00c22110300701d00c1c03002c00d4030100c0b40c10400100040508146401c1d4504840c401807441e002c070320b4181c05200317141c031190043c1162400100903400029101c204480000e25516004641e00d4500d070801a000d00342c1c03803096000c2a00160140404264428030194115000f00c0f0002100201c802c103440140c89511001410181407003e0f0020440800e20440c250103001e803a4805900501c07405621440b90900f1100d80c02d0900b041c1c160b01140d00040e640098448102c1104c1c0b8164800c581d90450303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 316137194 1250 316135944 316135973
    0x203042102040929010f050103051b04060206190e06071404030804150323070e0d0219090c210e0c15040306060b0c0c13200d11091806010507 62
    0x7982083c00703039181d0010420207908201d95440804c60381d65041020b1004507081c24030841c0c1c10140c650010800c50f407080e280c507030b12155001290f40c0d51560f54110203902e500d81101c0e00300001c0840d603440700ba406160b0050f007007451503403c05484170795078813441510082c0c44440071400c50101070001000040300500104090405030801c04050380c290764004050740e0034244c1e80982d06450b07400c034002d1660803030001c0f50000c0441c244500096103a9001c00c40d2203440d07201c00795001c60407100d4a4080701c41c403000e0000361100e14105020300140240d00380e6450f210340001040c110503072480e400c0d08451681c409515800724000303a80004003081c000850800d00103a0701070540c03000250800c104a0240304680050003c05a242d0800d5240350307146031203601d2824064001e008000c0119807508450344080d13000769220710010310710803101c4201c01880d0004404a40207615024045142e13503041c50585094044c014900b45042d81400c9441401880103041c85040c00030a124802c0064150f103004800c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 316138444 1250 316137194 316137203
    0xd0305030a050a0b06030112061407050705010b01050901020705010e040912021e010c081305010b041107020301050109090c0501110f01050103121209021f1103070501050402120d02030421020409 85
    0x840e4102030411400300d90b4080d220307000c514a00a0112055260003003070303a0460b5580000f00a1802c03240c10848007502e08264510000c0001000304442e094204010703000003402003000f00071410803240103480510502030880e000d039000e59810081c0358803840c02007003100d602800220b40e400c030598440804003001c907032200158101c044010200030026040300b410004407802480045840130010b41030301000750034540907801408001d020300809400c001d4018001400400c00e003c92000700d1021604844400c92180d4200750002800c41010b026000066410091640c4440d140100546031001d0100f045000c50203100c20428a80c8070a124050003140102886440380d180c0c2000100600c000d6005641001c0c83c03c88880301684442c08008685800340d400740742c000f1000c3d44140c9984000161030020b9100010f40b040c108401900514010f074030a82d07080d100f14403800d0402c2d0708c60a460070120010380c0180000c00292086580c540c0c02c81154100e4802e80b00f01c1c9401040c144e648240d800d64 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 316139694 1250 316138444 316138447
    0x3070309060206100608010909140a05010507030e160e10080d0c0b0a1e020c12031f0f12080702121c021917070201020c0d11030c01031407080907050d0305 68
    0x501c41c1c0601c0030b9a40309030040342011100d410100301030700501c07060040c0c110b5240c0d282c00400810070041242d0180380300060071941c91816a15005002e8941100d0400c00281410b100000020300000d1601c1d91440d05800c490505090071565000345000800454444542000000b040c003000d108041e501111651420745e034410504202c0700e8010b000e4621b0010526040c21040045110054801e5a4072129405039031000d052136014a015840e0103481c0a0320000018008a105a407055030107460080401d60030540c0d80362141c8804d07a506100d0039004a5205a085002070341510040c08128070040459001c641060a00362425640b0b066203e43ca20042196010094041110020705d080c038140440007240c0c1c56407801200071045c071202005a2003c12031800b161f0091101c000032000c0034200c900513013840d080082c0c000d10800c513194001d0203012114820f0b540701e40105003080c0c00d007280da1010303030320342c41d5084509480041248a10b40178910f80403a080c0c2c1c03030800785003006010340c0e90203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 316140944 1250 316139694 316139699
    0x80706020304021017040b0c1c06091a10080c0f0f07020103060e1e0a0b09131a1003020d06060b0a0201060e0115020703031202070210031a0103090203060a0c020f03070309 75
    0x4a09007103203136616002d03c0014024500d00510b840541a4085d0b80440035154940320800c220b1450700600c6903101c2c0011100750844414403055221404841201000703002141c104050380792000c07600030b491034100250090b1089044d00605416420824003e03144e40f4081c0d44401498840d007064900241c014000a0b031f610a540e807501071600a08504c0d0102c00c4142000caa42258880904505000b01c11072040003604515456110443c0d040300603203078048a16010000401034884d94000b02c42201c0645040c10075481c030003492500c17559a0a2080c0307282e03401c40d001c1000c881c071114011a6183c1d142c82c8049845e0840340098240c0303542e40d40010032083c1c02d0040300001a00140c10460089215101c005025540010320f407080700e415040441070302e0b4042c200007029120745c460181d044003000f0040e034100c80e4158050340d54003c15440d0010308228000045080e04c02c1320310b0181d495404040480c0c692070466000c7c40320b048013030044602515804450300d045404c41d40b0285c0104900c030404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 316142194 1250 316140944 316140949
    0x2703051b0f1b0f030d0f030c12053c010504022d040807080a020310051e010303210b150a180306050906061206131103030d06150224040f08070602030402 67
    0x410f803034050201c024001800550000910400082e1846400c01da01da8005201d4140104a540f10156010700240080d1078440380f180c06140b107003041d29080001d44081c072280030910883c9030a180c0039400b80c0707501076440d203c2004040d4001e0b1100166601812100c0c000c0c4560700f004030000b6503013031a543c640b2585000c908a041610650040c10740c1e03003000310741c0300050f68003054001140754103500000d1141c580d008079140c3c82029020b121a05200c002c004003e054102d48207900d90003190600720790418017003111f0b40550b550151145d8120305151510041403100b507010b41200445e0f03150602c0200246480004400d0159000341c4407241e441084c070403541c5050000560201c0152489010495400c48569840310002c00021040d08004801e804010b0340c40010340400000404036602c0b400302c130103000000c0840d48070f5103011000d19014008604d0011031343c200c000614662170741d21007819408640c0010b00c01401141d913003210b264240005148440030f800240d0040c0350040e202d1506205 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 316143444 1250 316142194 316142209
    0x30f1006050c070302060c070305031605100e0a0f0611041706060103140a05070309020d11040c020609120d0e070e0a050c0310090222092703051b0f1b 66
    0x3103081045010030001c07403881c400103000300440340d043c0c175100c1d61044060790f031700c1c140349030784d0001411400001031040c0441e60b5500c0c4e0310449405070b42901c80114048200300c003120103107030404916801544266002c1003e1103040c240e42409071802280c3c60f40701995043c2c40303510a81010350340c048608076116001108104042c0d0100080c2001c0080e0300078000e4103590884010f0802c049242c81d000011040c43c441e03048075800c5503000d0001c445444180c503281c01c112086058050043d442e2902c440312061000441600485900c0050049d075142070300c408090740e200b40850440300752521644c0215080401c0f554006000c0003407207040350b090400315402520005010b003041c0c0d11040c418000e0000700100b9203022503100001c01a039503000c0c00c010b008200c0541c2d040b903610b0120100e001800d540176402c98520320060120b168006106e50000040440c0d8860340500000d0086c02a84540d10304114001707182500c0c6011108101e5003500d01d2840d1400b00b890015107080400c60001d56400c2030403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 316144694 1250 316143444 316143449
    0x2011b0917060903032a040612050702150a0c0903020a03030c03021204030809010f0c0b011e050411090906030304080a05010f1d10110c1912020303131203020f030f10 73
    0x3020380342d681024126240da0340805000460580c103a140851184405030303000c04040302d41c42180341d4072a90b40b050b000d00310240052003280c9660401e03000405052001c640e0204100c0724040c10165501c607480c1800040c01d0b41c91004091041400340440581d84400c601c00007944241d13280b0007070f5841450002e003803815440001d500d1000921041c0002154041554202c0c01d003882c2c4846902c2804034100c40f01507189501400d450701490020605e40019100c0102c0344000c02000c0b810389a4880a100071134203040070208402500b40129038462074500e0303017150803810081c2101e00f0913884a42441c103148903690212040d81d55151010a514a5806003002c1c0c030b2140e074141c0d285046c44140740d64a594440600c24081c40e5100c41c4520743d01008400d5036202482d0744100c0c0c5c051130080e94034861868034400161440087c91803065a141e20000c00c0302e101b004400c100d2069900c56648464480d21142d01c2402455002d20150354108903041c0954403a04203000e013120642000c0d003046580c610580c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 316145944 1250 316144694 316144739
    0x40c0902090f03100507022806020a031d0a020a050a0605030a020705030408101b0801060804150213030602131406070311010f1a0f01020105071b02030a05060903310302060a02011b09 80
    0xa591901035000306034031230120290044070140e0f0707403641a5801c070000c121045002c095035280d0f01c5c101c81418400a08a10f503548207550001d03c1648400c07c000702200c0c644103480024a0800005001030000d03009403001610034001c49040035114262a428603c0c1e4684207034000c0d0780c0da010190080c60000074141c1e5094641001409541000c000a00c1e41c08010800341c842d2503e00078010310b920a41d030485484400500e00429070b262a031411360007070b40c8031404176514600b6800020946030011020749881e48401000540b80803460f035810b82d02d410380c2251500c0e41d5560b400151501e40928080c01c0c81c2c01004088030003050f10303072804100e030311058808181d045a01d41f07403c00000395000000480c0c0e07070100c4a00d0140c240a24030019150140c80403008140340070340307003e100220038000064074240e424581d04201d00c07a40501040c4044074510400564070704420010800341c03e1900c01030030018201e100210701ca910142e20018054440d1194a00003007542c0c0f409c2003290b4105c80b002a000610 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 316147194 1250 316145944 316145983
    0x23030f0412210903090305031605010f06080c0d11040f020a030507030e2a0d0c05011b020607120c12050c0c0a030203070303270806060f09040c0902090f0310050702 72
    0x2c040008084a00c0100300c40c1c6035640d40041c03400341801070303450000075944141181d558101c010305000d4280e0703424500325415800d25125113019200b9009900c1511a2100242480d2200c002000380704020b5100940343c06800c086000b500e501c1c0d60045400101c01103201690341c6100c218024100d440040400d000c15181004031800503501041049600558000c2c11441c2e103000759004040c10f101145040d40804100d0101c41000201c0380c600b0111034098032105c0303c8100d8404406992405e050340258800c2c410414400041c00e0f801551050411510f0401120440c50303403201c10380208d0a035050089000400d019800c5681008a115180025601404014503550100b581e40002c0e00006041c030000003a12a419540c800c10319284000000030341103010303500c0c2481e948a5000ba00c500c0d000301084123042c44c45041000070107004079032012184680c0b81c40c0c0f1125600a4200c0c000c015840b51003118003040c3c5e641c0c208a091742261300b84900040c5801e00c01c10103031600c0300210581030745404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 316148444 1250 316147194 316147217
    0x11030f04140d020904140304050402070620040f030b100504230c07020d11040b06030106112e0515060a0210060e01030b0a05060307030b0903071505060f0123030f0412 73
    0x542c620f8441d042a4006c2c1c2c0700244004c6c0403082d43c2580295000300381c0081c8013281e15000e00c00d040e00540c440107850384103d10f442c1c03011510f080040c425030140302c8003001055804c000141078403e4040d8003201080c0c0c40014075803500c0c0004c00382c800c0b0403103006803107002402089114101807500e03074101c02076515042c60910309a020130400c04d9071003005410800172500c201115184c0340c0185202440050a180d641d68441d4006401c01c4408401003855205001003140c10414441c1e44a000c028001c2c150700720f5050f010f400f00c010703000090000c4020310741d100c0074001310b4450780c0c0a06071140341e980240210008181d030b01400c80f070840d88034000d812694001000070a400b40c080c40e40100b10820042f840d0303034480c800f10b46481c01b0356000804c680302101c00c2140302c0c2400b0000d8503031540704400b580c0403c40004103807825070b9002c1d95510f901c12543c05544410b58040d00d4844020b9a0701d4007a590038244072001900303260011034205400c641070a04000801c20700f0f12201502d200b082c18050f400c0c0300d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 316149694 1250 316148444 316148449
    0xe04170c12071a01183204030918060e1f050114040e010603060503010b090f010612090803011412010603030207030209090307050601151205060f0103050711030f04140d02 75
    0xa00c0500e11440014000703106018015140784490014010342d01c2c4070760f5540d41d810382e0843e080028006041452a05014160318046c011021811100e803000940358803200000202c01c104014000710113028034483c0003d2214000001420349561101c000a1b01d80d24104100b1440c08000340401406040320103c90074004d900b400035400d0324028a0944415900303460380352102d1260390001c2c1200340080c03000003409941604449d00303691045d0001c0c0040c4030440240900c41405540203042c1030701000044c415140718180910078551a2034010800341c281e501c400c8650340c02078026915210641c3c1c041c044506140840c8a1100c146030020080c803465610020340f51005400001d1040a08801081030114108107413060a1b812006640055030f440b8446041c41d91060800b101082010300056001c008500c1040e100e440040c01100d020340c04c2400460003444014421000c2c00f15524144803500010800313007450410382601d09a4641c204440c01c10394400800d246486001d0840d03007000142c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 316150944 1250 316149694 316149703
    0x228030e03270a090e010c120911090903070614040b0606040b0f160506070906082a070203010e06090a020901240e0a0b0d060906060c050d050a0212040e04170c 70
    0x100b079641040d400304030640001e4124510b82d02c01d040050401d07040c0a0000019841352900396480d40360600080b103051102001d0351300490000d0200c1c6560502c1d80d415003010968250302c2501441641d03d08401a9581401c80e83d90500108901d400b1004000c200401c40d82c01c00d404c0b00040341c00d00c0c02d182c41c1202418452299860740c08004c540440c8402041c1046480c08045542c84000d03101c50b454401001801100c1c940b043c130001030008000300711030300d9900544610350303d282c1c142da8040c480f01c82181c020550101500f241c040d9070752034810a10320800d1144a003c3d256001c0613000403001c2c1d00400c0920101a04811040101d440e182080403050183c5142d030005135040080703000d0070940c00201054010703400240c5d8034400090724040e201c480d0b40705105032490903a04110f915260392088901010002c001451503024400c0761a030b442c09a0b0207441403084d1031048450825500d6110304c607a8005500003580442c020080c4810446800c1350f41d0030740f00b00c061000b0b04021102403055030740e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 316152194 1250 316150944 316150987
    0xe0121050103020f0405370e06060406090c050a1b050604050717030a09061815032f07170f0f0304020f120d0c0309081204050a0f030803040210030228030e03 69
    0x1060000220347d2014810035a4140e80304482c3c140070400c00c90010701d0181c556004540c0240300d1480c0050124006d81c440c410140d0144165a55505003c0d0100b07080d21a200500386621302c0390840500000002c1d0300700320640c0300c0c91192010b018000d280802d074040a40078080040042d800030f002401c07980c0d5116801e03008440c00e03441e01800d6410003081880d901d40d5950014070202e0400c200e002c0400e07805420050072103500000039007a9407403141c24800b000566000343c11424008000319070205003000d010703155030a1410025440d020300d10746c00041d2540011205071031003001100700015031a004080e0080c82c0c1040e207030199400c04054043d51101c01c04500b080a000346003d003803090600c200300d40005007801c0d108032170f1012800c0241d00d449030024410188186410800410701c0405c500d24082282c1c2d214484904545071942003280d8000f03d01458001c2641c00d01c6029006861001c03a401684d158504044c60102e1000c001400e42d4030f03100c8110642e074020440d00d041e02c0b16010241e4074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 316153444 1250 316152194 316152241
    0x10c031e1a0108061c051b010216050405041407090606080f04020904150f142d0c070f020d06060306110f0304020609031c08010602010501060f020a030e0121050103020f0405 76
    0x2980c2e40c07404005003032415040c00c0c405c42c0d00c2c81e0070140703010403100198049104140c08841110030343c1d4072004a03607074110540b00d6070740c151040e4420000c606242d00100d4105100d44012200c0741c2c500c100c0c6900e01111613104600e0261030780c0701004040c0d00941c0180e0021050b4182042c54034058000c1a0b40400103440108001c1c0c0b030040d0215410601c0d800b030015040c20344400d10a9817a00c4584401130075054270320914940c0700155000406042e051402c07490a000c80641d007e5070745110321200c49801c1034205440c081d4002038000d0060f80d9840c144480c1c54402c003000100e490540c1051001c440200c100130030b000c2c0c01005943c41c600d0840050300ea0081e8102d42d00e80d529840d0101081c1403150071101c200490405a203026a0607400011980c140e41c91640204000c0ea40c80310304480040806610201680100700140007103803040b0780c40300c059501810480b80d1400c0310384601d007844d15111201440b41d544c3d840140114039000e82500b012440c01c4800307019605000000b2080c14062211418 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 316154694 1250 316153444 316153457
    0x14070201020d18051302180613060e030a080c01020711030f1e100c0c031704020a092d020403050601080d1e0c150906200d110408010c031e1a01 63
    0x2c1c1d040ea11918400c041c1034050800c4030701c1031460054170065041041503440c1c0b841440c2080603207080c15002c0d280c008000b260344400d2117280c06010307140160803000f810b0301402840460804104818000e04207501703604001603441e1403500b00b4180702c0700240701d041d100c0e82200b00240c1002500207010310640c204144000c0c003100341c41c20100e141034825000c0803421800d00403c10070b4960880b41145040e03000b6168030801d909000d001c0c1100a0b02110000d41c004112001030001c4c10250788000c202104643c0004820a0440d01140038029007803c0c3c0400c00b60002001d00400100b405800d00515403880103000f484003110001d840c9140d4030f2605030300d4908101d58100954071501c0c44000f00740e00610500d4602c0d1110700100d002c2c00711090180c4e556410007454944000800e5081001346083d03c48082c01d007802c4201d10006420070b41c04140103c00d0500021441140c280324145441c0256240014000b00a151403c0402c800f00700320303038003a86007088a4450f11010f443c40b012159003441c040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 316155944 1250 316154694 316154717
    0x7181a04030b040b191517030c060405030d0c081302010c0f080703050910050a020d050c21030708010e010b160206040e0f0a1a030705041808180114070201020d 70
    0x80026018039032018000581e94000d00091102455150b4045c0c00c14084000740076003038080d071a042d1181c0908800740b035070001c081040040341240d45060b6600d25901620701c1c1c8501070310490300d440c0040d0341c16221a000020b40841801261041540d00702140c24039441600c2c050642c03080e614182c81d0040d0600050800c2801001007805164454030742c410165600c814017030a0042c0f05400400b140b90040d00c0c8a0b652500c0c2600503016181000c8603076004102c14a08020704031100e0300a03806080403480382400300030ba0020500603500d0300f02c2c9507040243e01d903e4402e000400c40740060b448800d8007025200103112000c4004211154502a0b4403040c05c41a403610100c0c40c42d1042d584420100c010203424002d801c600d451000e4003035a4a010107200380388441c80c0b03501c8044a044d1000380c0c0355011880402007070401d508040c01040701c290034001d0155868450859950180100003200c09100700d07480c04035070708000307400380805002d41c0032400c0c441160300107580c2d00c44842c1220140000c41c0b000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 316157194 1250 316155944 316155989
    0x7140f0c030c0913050d0c03120207051b0312040801090204050f070212030705090901081f1104120809060c0d0201050714070b060d0c0902120a02120402060c0102090a030c0e0718 78
    0x3411355556014044601040003490010300c0038450000480c00640c00381c0408901908500031f031120f4a401c0009401d005091050b2241a803401840d4160940950303d040c0c030b80c1c010018090001010b02c1800031031018010f00c10003089650042c4070045641128003403040c0c8030b90000e421401d9040c044402c035a2501c03450800c2e101c3e4080d0307100c55540a10030380004146803501240c400d808031041000000345c81d0038091000b041d00c402a401c503010f01d100784010006505076030100388400c2c2c084d0441c5490007503a080842d43c04e50004160200c03d62102c001b01d100c2e25424401c1c00d07888011840c20907074006451810024900c103520001d020221042d02151996a8820850111640c00000c600b0b03540d94880a10019400c100c0c11041003805d00c00000d030034012540200c4200020060815159560719401c02280e5002a03040b003062350b60030701c0350b08000d8542082c4480950300407000104c4152600c4107020226400034281f004100c00141442c40c0c0c80d0091114030244e0346012080051030140d07084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 316158444 1250 316157194 316157221
    0x111181519021c0e090a060b0a03092d020a090903020a03030f0e0d0f030606021b0909190b040606080c0f1c05121216170402010504030807140f0c030c09 67
    0x12100316603c44020340100d007500120580702e002c5054400c8506a681c20540004480352881502031140341008903020480c86984812020740c481c0e0440744140c441212100318004040070490079103c4000007040662038983d040000821400c1824031800c82c5641e1300940700c40b80310358010300f13068603101030b403100381c203140c1061301140d000030200c03000c05c084c800c001072400c029841f8200201c1d29200c00400c000344080b851848100c01d01848a04c801010001d1295060004200d21804e000d120b008123682d00b0722074801105580606075400e90740c101814064200d07180c42d40250000d500c080c007a0700d040d4030380310b058052988003203480c0c0031101d150400e103441c00d1110110040c000c1c0100052500f030200240301401d02950391420072a150b5560b2204485640e42c0d81e0383c00e80205e5003281094200201006000386e000784185080d032308195a90b628505941c001c65011503044005e50314481d1219000c11041d0b01c40702c600700043c1a40202c4070080303900d494502d240d4a000d480510300068502c1040170 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 316159694 1250 316158444 316158463
    0x14101d1219141c0903030506030705010504051002010204150302130e06091801060833090a110102072309070504050d0b0a0b031c08090115050d020f03011118151902 72
    0x2800c0d241c6241c000f40032a0b0040002e070104a0110b0f2400002c61454280022084191001170719440c1c82e050400341040750101c40d103240f80301150340801c0f010600c1030140f0b86611480080780c401517141d404404103185003482981000b40303202418820011180c0d01c0e502c1c03807a0445120030300b50840844203c0958050401da8102c0c1120748170b54050b200d080c418200c40407414a40c0501246124516000200d040c0013064660074a541e0248407a1000b0400000004641070414011100415581c039101c08145900e2103500c162540185203207001410505403081c0e0151840c0f070300340d14003400c10340003c090119138503001c0e00461641e00021704040041d07000c040c040314004e08035203c10700c0c5150030249a080000003440019940c0000c109050343c14054010481c2d07031000880030041c01c043c184015800d40c0e4000303a03440b1200d0303091301495071000e10a1810f054461000c042e603070809982000140038030074251034050003800b441d40b000954010150741c41e0300b25480300b00c5060000703004201e14101404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 316160944 1250 316159694 316159717
    0x606010507030c111e0406080303160f090302090f1905091b0301022101050a06020c010c0b0606090904030801140a120305030c0f040b0304062714101d121914 69
    0x242e0035990800e0381c0340f117811a81084405010158441403441e49a00098071000501106245910b823001c2c010340c0905060800c43c54800e4040e55642c0000d0210781090310040d0845280f4030034480c99211301d00c822030491072640c030203100d18100461410307900c00000c114210f0444000c894054281c0d03003901294003458060f212030300328400c0c40300e0041d003103d0203100700b070702c1100c0004d400a0003a001260310140850140c41c0c441032010141c0780d02c4c04184004024960094080000300700301e50b40c1f27019250180307003c0d50b5994565818140c54140400c192030307500b4404c41519100b0810410b659411a10b41c070f52614103903803603448061a405450185031801480c5100216000c1903c85202c405148100e02030241406081c0207045c104200c0e116580807002c00035400d1082c0c2011600380103e40c104801008101d0f031b11050650a40821242e14507140040040f11000b2000012400c104070301005070308140300383c9040d80103600d0040f0601e0540042042c811140080e13001d0610746010b039002c40c9001c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 316162194 1250 316160944 316160959
    0x20a05120108030a020f1b0d0c0504050f0103060c020a02030318030313090b010806060910200114090d031b030c020c09070305040209100503030d02070f02100c060e0606010507030c11 80
    0x12101065244e0304040018401031241c00706008003820009600d00e0070b80b60120008466a601c0424001142c2c03040d0829141000c02c00300c0081e068941744140e0380708003015104004254114034003441a1140440c1207021540f1044075100586d07408001c8840e00c100246500b006208140d01180c02c50003085121502001c0082e400035041d00c441d0005042e40000b41d071080d10301d0740c42c48100600c502800d02100d406c02c444800340c00445002e840303134407004001d1400310301c0d80e5580b1324400386c2984d10103000800c0c0c060007103040c0a4419010400a10840198181407020076031103c0b0594103014185a00c00405442d4805d14010500a115015640078040c3c01d014a9280680c40600039101c00d0703400301e005420803c00a200740104017520401c0e0350000300a180b070100d00c000c4902c060f400c802d1080d9158040312a4010050342c0c2d08100b205407050ac1c0d1120b0300f240c8114241401110349010140c140d030340005042120607a481400c0b206000d91504125083c400903040580e400c0c41304011032500400c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 316163444 1250 316162194 316162199
    0x3070303020d14030106092312030d0f09020105030f1003061505010e0a030b150109090f05091002090f0111030d0606050d0c0e06030f090a0c03110108011502060a020a051201 76
    0xa001c11280c0c65924141c50f80444003044910f400d070203110912649000840c0b103202807001e00c0428002e40c1b607800c05500000e400c0400c03030300012070242d4400003c5199501c0004d4400c401c50b4a4002d0381c0f50500d03040c4040182030b4171030b000078103113110040502c040214500b0000d4081006502800b000d55001341c0208103080e07454203510041c03945400303040e01046ca0422500628a000b0145c04152503118148c2142030700e4151074a030701c03500c200c01014140704030130f58007283d419207600c80e0b541307210305240c0003140301d0528400c3c00b0b04103801c841c4d0700203080340100301403c4961907100d0b020300000800c1c07030600b1400c202c00362154114011451104900d5003815400a100c5502c1009410011000f00c42009191503850003603d02010703060703000c0e800072824400640e004210880440e0f00203255030030703500c41c03c1160b603500781074100a40089401c035542c2c0d0602c01c030340e50f4040350050240c400e4401030401210b41a00c06035a4a9004010b00c000319000180c650700203205409407201e880c0300030010300d401d58 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 316164694 1250 316163444 316163447
    0x51e121b04090c0b0c1c0c0c050f0a06120b03030c100624050313061a15070c180209102304060c170c01090b190c0f0c020409150e011b1d03070503070303 67
    0x50041f00c1600c59102c581400704051900c0741a2554802004003007021003490600103503490745440c851448003030750b5681d504030661018801800001d1404c0301409200600c1110b43c2c0031500e81d500400e40c200c640140729400c03666403d40c4036100400a040054232965040421002070110450040c211400d00c50394a003d03c004110002000d10100c80c01261907424030141c0b415402102c0010f442494401310810440b8020507000400c1082035401514002c082004144c0e2088152040c00005151442e04141d81d100707030241c0e01200440071051071500d490303c2c000620f0400943c5026015410f184410071501015004940d981018070000744540070040c101040301410855003c03141408800701c6e0a040c038058030a0194103032050301c414007441650981110000750040f8201e8010f640e030452500855120703101c540c1d1401e11081c1c0462050b0b0444181401d585640c0d107000a03660442300d180101581004024080c3e03001054025041e034945000a4600f401c142e020740d426000e010004010315 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 316165944 1250 316164694 316164707
    0x110a090e01050402011d0f0d110306090303010f050303040b270405090c01020c06030403080403050318070f031505040503030106050d060b0a02010c0f08040c051e121b04090c0b0c1c 79
    0x218002d81b583c0880e10940c01c003500e01010760149040d4088100302c42d018851401c180b4103a0524051014180d03140c4510700400e142040c1078072860340d0b0360302c00b200401441800000b054091300050b0040c1d41090329000555415004110889001c10f000c118070980040d07a00c00500b401110040003804582050400e442c0c80d00c513403400b05030050040c100c9880e00e60910508403030085625030b41d10001640d0301e0701e0486041e04044c01580c2100155005810603c07810003804010302807012040c1d840301e00e186024009241902c0e10420280c5c00c1908002c080f88001c02540e046070184d081c510356581c41114200014607213604903880700400030a11500e01c0d9815400020202c060362906600300d4601c0e4010b881050085900400100c0c90b06014002c0341811851245151001c11610f0001001d450018008404001c0040c041360b021702c2c000c03102c04e080d008040d00003c0382a1000c21640003140c0f100c5482d81c26901444c41c0c1240c000508241070001080044402841e000c0641c03001150b62a004145 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 316167194 1250 316165944 316165951
    0xb060301092a0b040806010b03180106030b150d2609060c010b040b031506040c1e0e010207090e060c090609030d11060c09013204090204170307050703110a090e0105 72
    0x4041580c008180f1030034080450f030664407804018038580c3e1134603100d040c165100070300003c0b44280400540f02a007600740a000040c5101c3d0340c5007611864118162118001c1090310039105190b1041d06501149d800100141c0d150285040048000e04d058000800d6219880003aa000305000603586400e440c10b600062000200b03d4090000640800c20580d032040d103c48a080c0312060000480c04070319055020070001c64147c1402c0c0300d100413203a41103042005088480c80030070f04901d01500360350790500407c00500b034107880400c041811011601d40e951401421811803520000b03168004c1d40c0c4a409840718554010100c6480303441004000f4058005c0841000c440e03c0342001013910001003005846510406079140302c0a4030701149042d10a501c54030008801915400403104404022001840600030310341c0050f0f5124a0100d9106c1011a01d0034080c19a400a0002c1c20002d8008140a02104d401000d100e4003d1038000c0010b000d42215404a20014500390038002d02c5078064100510 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 316168444 1250 316167194 316167263
    0x110408150603071215020307090302040507020c0907033605030a2105040f240c0f020f07060c020d0519030f0f080114060a02030c0604030c1412070b06030109 69
    0x600701d540b05202c0d6041135800e034004040140d00c0c5580386a0245940c0070b540d001c0c90528050b2455580c3e500820101e40c0b099411100581007071454134404c1c03c3c81c61050790403d000c0e243c2013000c086070842d42500d01240e20044004020241d40c1c0014540b90804540480754001c0256aa900c516001c05800d50588510402032400e07503148011408103d44195803159810030f18003603140c50260780da02e66249181000e40f101c0d002d22050040d55409600c9407060714501a01c404690b40f007a0358010b413611380e80754201850340d44020b40c144030a03a8000c00b01c1c0e0f800f0341d05903aa030a00c0062845c0031402c141c0080c00702d030000e1400c003080905155208079080360f403100a071102c449606005404590a41c801d02800c8a195103841440c0c4580c2000b00081088021604c1602e003000c080d000010f0a215042d50294009490003810070180070100401d65240b03905000101215000c041400000d4020701501524181e074100004485032402e4010320a00750b0b0100300c0300300800d00541c6003101e40144080d03181c1d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 316169694 1250 316168444 316168453
    0x2090915090915010b0d15090f060801150e10170a0215030702120c07050604171c0c0f06090b0f07030c110703060c0c08030f0a0b0612040204110408150603 68
    0x3806070030041501c42e5980419803e07425642e0070091502c482e64480c0e03020a006d545d440c1c50104110301022013a80241c20030900c0031589a6440c1c16610a54413103802c0480980d1400000c01e000046801611080b1400360349846072641e10560900c10300700007980004041c8030480c09134991403401107218039000c0d10031a0807c0c80c42603c5004038820740030490360075001d40e10686007030f120070154030040c081f2400c9800449051644600202c0c40e550000d6010342c011006d80c0c4407540517050180550700700c01c2841000c0d00c00706000707a0f0005100d0010180c0c050301b000c1c0103110610900603181c00055000303401812040c00f07828104900351895100b215200c0000c0e01d01102080507510404101050303d166500034a040c60541d19004000d000c00070621003440840390b40c800000d071811015622074484000e0540107072404400c3c000c2a591010038143c40f649003080b000c041e40b40422135640d049601550006400c0e00351092034003a6203d07a03008520319104280c0401d51198044841c248200f20580558 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 316170944 1250 316169694 316169701
    0x504030c083609040b0603011b080a1b0c0303090f0f14060f2a040e010f060206060f0112021c0f062903010b0310090f060816140f040209091509 63
    0x40d9100444600c00b1a030220b43c001c04180031482003000c10790414401000054580703a0341e174007503903406290f1004101003500341007004101d0540c1d110302c12020010441000600101450081aa211028006080c903690b00000340038405203404c80080700e54002c9020200285905050940824030b1028203c00d202d0000001c0200303214140b001d0242000240c0040e005086010a20030b040c00300d80002c098440500c170002d002c20700d4100d01c41c0200b071602c00c107041c2c4c6400c0500082c1007000003003100c2c0c0206100c80004001c1d90703100c0c0c45200d071100d10f100010b07240d41140840100400b041c1883d40718240c2040c071465840c501c9644008100ca250480b402030842100b1a04140d0003110905501792917000d000422805035504000d59022124042080881b6103070b5103103030100c0340c6c24581100b902d540c07040705101640701001815043e02d200c2445011161900c49072840902c01d5a1000b401408408803000445e1143e8041d11403480b0700a11120350fa02e42101003c241140c4611103070b06c92400540403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 316172194 1250 316170944 316171027
    0x3031e08061c08030a0212250e0301020d0507050909010b0306030a02040c0e030d09171f0e0a050f06070e010518010e0307030b04140106061b0b0414010203191b020c040504030c08 78
    0x801d000d4020060008d024031030860f0050b921010b0101c016134140d502000944210941c91080a01c0303501c468484503111070100c1c05010420038140c0040d01c0500341002070081590700000c50050a0754100c40c00709aa40040008440f0041c2c0c504085405110b01c0c1010120160844210710546007003d101e01000540800b00d42d5031400507007a243c512038072041080340c440f0101c3d0051501000040105d640c1d01e000c2ea6541c0e460801401c5561600d60841e400703004500d0380c04603a1010250003440c0c040c1c10b00800303107450302680d504450828184101a040c444080d00c1c2440f5480081da080000a00545001d052010f1690350310500030101e5440c01c0030119510740a948081c1051106c5c50140c0b041000c103556100145001610684001030000710308204c0e10424001140b2902441d510411250001040b00054420060300d154142c2c0980484080141c0d000810407507042007101d001c070b400d40311401c0c1a01c4000c0281d001a20250b4000b500c50049280c80305074290b002c4681c40c5241810428590 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 316173444 1250 316172194 316172221
    0x70c020324010b070203070302091501170906060d14010c050904060608190504030e091f0501050903030a140f0705030403030206010b09152a0703031e08061c08030a0212 74
    0x1d0681d00044040010301ca120040d9020b4101c1c1440039040b6602e040d16a000507168800490b03188070801850903140300c903035034840156034030181610801040d6007840c600035a05e030303440104001c0c05a0f1207410801c0900003c070028104048246000300310580c4030002c02080ca9004445090203a07050100015240e4424090a449101c3c03056110082013105035651000e400040c005600308503841c58424641c0d030396003050b1405110184048050012170100500344000d166015a05010b8144458660781d00e001c000c68080301601d25007896200c4141d040002c00b4050078001000403000803071752504100000000f00141c0f4001e408131400382e0303a100440081849544941604074003510f040405021040c405041203101450912244080c00c079025003041c22407003500340c1154444e4000b0014141c0100f400607c4080303c1010340101d411404024108902c0500020f004000b0340005803403841c030b00c1d280340c1e24040d03201c11030aa89003000c1500801942155406144845282000c2400085c0540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 316174694 1250 316173444 316173493
    0x40c05040e0c0306010207060c0303090804060507111503132105040e0108030307050d020f28030b0607020d0b13060207060510090b010e041806020f0c1c35070c0203 72
    0x1c6c0104840ea040980898030010708131400c41c00d264551082400180c080006400036100c10f903622340c1c454015050010a100317950295a0044000003d59040c01d161f0030100c0c4d5204c002c4070002d5002606c240352404104841a00c10855602054420358950754828000c0081301c0303401c4040c41c1c2c142d0302c80c880c40b07440344001d03220140400c00820900040d074805801518245040e140c8035414039083d403415403640220010720740c4003681954003010686407d0b2040940014054800c142001c125a0100d030f5204007001e0040c2140101c0000908003031462100e9000c059400b90095488414610309000945002d80c0c900710040c2070940041110754182c810703e11181016502c40c850303001e070b090602c0000d20345580180303001b240e8015100b000c075145000808843d02000d04c402e42d02c038802203906017032440008a945100041d00050945c056210146031412002002181d0f03038107801019038030300e0005a1113a5181620310b141003049680d0000c4548180a00907426128203c0c2081e412540e10b81080b0f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 316175944 1250 316174694 316174697
    0x15020705010f030b13060e0912030a0f0b030307060608010b06070b071d0409151505090703022505010b01080f07021509031e18030a0215030411040c05040e0c030601 72
    0x420085503100b0707464802d246809003400a415180748011809040a4440b6071220703d0303d0380710800c80a444411000e5100ca0300742c0152900751020350700115940300142a4a90050310303903500c84000400c0d85c1c401c0701e6000d0014201c0c0c0d52001e1524046000d0030301e91141c032600703501e029102c200034206239040717034100c1e58404550200c56480034000c0c0d8201800c0d096031030358044003a145440903252840358060b52070142c1401c009445010440c101a183c03070940f00000c952085604005a866004065800c040c607802c02503140c1201c050040e4520310081c80305110f81c00c20b812460144581035000984555003a40e0307840d500e50b108001206070940640345100183d11820801c184031080744155500100310206884c0351403480c1d4075200d8542150882c1c1150300301e00190104400c42d5170007a00f01c00c2c0c40181c021b05030f62061500082c03202c02c0009580c0841d550000000b0302017143e20000c424140c5401081007140c08140d80c0005e00070303006801504500709003580841d42103200e04090382d00c0365105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 316177194 1250 316175944 316175953
    0x908060a06050603041e050f0726070621051006200705120a0b0702011b02010e0705090a0207050d08060111012a050d0524010809060c1c0e010b09011502 67
    0xc545c0d43c40642046c0f004001d24080c0e407041143c1c0052002e00c40000e031240c0d02c00083c2003190034410ba00c40040404807c0c0e042e802e9101c08200c0380d2160124103403007151580e0504040c1c100281a200310035082b0a09106070803850403040000c0e0941c40c41e030a00607640c2555400d00c03845141303008c609868445419091f99a44034040400103860113141840c1e01d8484001074840440c00e0b40d4480c481d00d04140c84020140c0d4445178500c010000814580d8503683c4244000e0000d641494080340d125101d40c007a00303000c1c0144200140440d20309404031501250f10004a138200000b8200c014800340054600754001034482c1180d011161050244208101c08407000000b0340309040ca000710704450344054002444014041701d03d4110451040511410344c800184004510030842112404104503603203050101034810312030344800c006a03165100e5190005d0641e5041c00c031120802e400a000e800c140700504042c51450040c0040d08000806a0306883c280810b1b42c85003041c544104508104400582c030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 316178444 1250 316177194 316177201
    0xf0e010c02012c0301090b040501140403090303120b1329060f070f050f01060501140a051e0417070302090604090b1308130e040b090c010f12020f0a0908060a06050603 73
    0x405048031103890f07060b0b0002941c4454a600440e080d07404410090f5000701d2081d0400c03042c0003003801080c003400c0c0300b4a075458507443c00d6070b0064901c0c41e03207010250401085043c540c1c861490750380b1603c0340d03160007802c011000400701280b1010b880c4135060000101aa612400c070604036011081101e10402021a41071882e1005230618035000750200b0b4405068065040b03002ca1f02c14016690f440407200000f10f03142c0d0500c00007400200e469061070064400c100100654103074840306a4042c21100142c4000341a4610480b0120340102d07000000500c02c0500e450480340e40006514048134403d403440c80aaa880e0410482110f040c850081c1044099500090300d405144607000d0303600b440340003e90300b04400c42d825569241626041070808a00a100380810f00c401040c0c5540e00c081700350f005103400e1903103c0000300b082d90702043c1c500c1445460324003c2c1d15201e20350103441200041c800e049417a040e411380300500d4501544603e406500402000c26000780140c0650820307104c0140c00c0340e2842d05e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 316179694 1250 316178444 316178477
    0xe1e01060507030320160c1409070e0d02060301080d030b03030c25090c08010306051f060e010302040b22140105030103330f0b01030509070302040c0504150f0e010c0201 74
    0x1200011740000e08a09001c0b280a039031800340039154049610003402a020303c41c0c9003c28120a41350007403400e01404910030380c4207a0300c003500309501c0001c07403819420041c0d404000c2858003000610080d4000c40100001c980000c2c00121004081495a014440c0703030140c5040c1a164070400d440201250003e020610b421040004000340e0805823034060390380140c5d1030500703004403003415210100259940d070040060061500605401a9480c10101c02d070303a056191881c3d25181502c45c0c1402c4c8900390360344001d40da0007a41514028110080344695640e041010200d00421800141c0c0200405d100b01140054840100b081e0402c1c060b160070b031a590a43d1140401c0e181e9000c45d00b818545258541c1580c02490039115050b020310300300106000c1c1003c52950240d07031040c08024101450481002022070002865104030380c0c0580380012083c800c035504894901c9190001c040a074568040c80000350390042048000585654800c00f58540c04001120306480045d80a0f0000303141104003012203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 316180944 1250 316179694 316179701
    0x60501051309110c1903090608060315070e03061e010614090409060e010e0d1b020f1e1c060507030e031c020d1404060b010203030106141e040e1e010605070303 70
    0x20801c648402c4c102600c0402d16850b150601c50910300c4000710710405001c00d0b40000344000900304904001d10a4900100400d070b071002400c00300c4029200c0d050210300082e004084460000b8405400e40b4161b1030041c0c0003656051100118264219200740000383c0301d40b044a206900c600f05040711458420340104020141010b000142c1e01281d40f00d80003401c0e01424401c59003014842805002c1031128644054404050440300484081044041d034006a8403a0481d51034540110b132449020a024022030b00e03c0c0e000d03992080e400075140314803031481c0c5400c071030f0442c05c0d07034404c150500c140d40d00c000b42102aa82d1b001c54000c0254000d001001035a44a100d0f1062101043e0200508013042c6d44030307003002c0d100c66266035081183d0310030070710007400581e00452000000a0009614651408800501d2181c00c0544462076003404242a1020f0207807241c11840e01132a8032450f511503898071303c008419542a01c0059000b41100d8174581c44084d0b84545e0ba0403146a43c0300d46003440720f03540f0144c002c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 316182194 1250 316180944 316180961
    0xc03030c05121602060c190302030a0b031f180308010620121305030a020f0105030405210c010e0d05030c0a0504050a08150a0203040b0c09040f0519060501051309 71
    0xa200c014410301a1101e00703422101e214050f850316030a071602c1c840304040d05102010b007118644800030821040000c16000001c4054240c42c58016502e03030319480340c00b0061940d1800075030701d0701500e0350020805140e00c40001540c0e42101c0304000310102001401c90340d5914002c01804120071800400c001402150400003040c00400e00c1e0403040ca52080007402c00c00c03071031040d00320303100041010012841d1440c1690302a203410b9000380a01025500014452001001d0035030410038004002010020300380440704800c45000701d200200e800d8260382c40304507080714107103107920740c43d103952103614103000188254030308429200c0354030f10b0325841d800b100c0540c031509074041481020840010207031a60080280101000d40181030058132030020200e40e85000390440459070300500900c07002c02c030f0380390a00f500898448c10fa19611080400445c000d0581e01e40349410b65403a08007000030000c5209030044c0003a040200410419481310010358075801034200c00081104950424080e000c12580200c05 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 316183444 1250 316182194 316182197
    0x18050111010e010c0206090d02240601020a06020f040603140f04030f17090a1a0c270301020d05060a060512040f050c130f0c05040501120902210c13020a0c03030c 71
    0x2070281407100b0190964100480c100c0c0180d210604000105201307003c1880d0201c120320190080201ca068018450510100c640c103c4032518801b280540c0c0c0204184035089a0010007503490780c5100d1000103554103d1710444010a003081005003007229400319440c49441040000c18558407030b0307101221a4010450b201c01400009802d84d81d00c00702000c905031103420094010000701a0504d0411000c44c0c4441604204d01603040074020b82113000b02c19a08100700c1030b42e0308400e00c00d90304007200030301c1020850550103520005550941d10042c4d0801e0780700d2041510260400381d5105c00451f054815868410301c8064003070701050001d05803510000400740900100c401030350f6164005400400700d008003180440e5207001510b2443e030f090080501c19891803c2003820301b890100007038405200c0c80300b260110340d5280c0290045590b01c2e90240440154042e40c25202880c0300b698564900e40ca1145c0e074810310307841c0c400c0031640010307000329002e198440e96948080c030429907068004d04984d080ca0310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 316184694 1250 316183444 316183451
    0xb0403080a18051011090a03030f020709020a02060403020d1d06030603030405040e030706050a14180f0f0c0a080706050403120c0818090906240d050a0b0403020d1805011101 76
    0x540b00400440d00c201060046015041c0c0701c0d201846201200d19100b0000f94004050200004070340d82c04540c40c0c1200e40600349183c4042d4080000ca080045a4000e031001c1480455040100c84e400107035644140d103e50200c1c1c1d510046c03440142c03074450141c0301c182159101c0350601e000e2402c0c01405150442030140880b0b04160712140000c05550220480da4a01d0384040f400b142448814001e00b504200f10b48010011040d41c1d10844002440041c202c0700001088010401c03105420000d008511920758183c8007041182100942c8400401400f94440c0041410100d14041c000c900c00046070703d6030715118034140c82c50b60341d8854200008454014000c0c0c400c50480800da59070f000346030100007400c80302320100103d802c000c046903000d40f11014543c040c508001c01c4c8449444c0c0449282c03040c05a11b10b0314610040040c00c005503e1800a1888c0205c04c10441013200c28084140202e01c0f0381c0988503030004207071048401d07c80c1031850340200401d110b01002194052410450107480d64030020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 316185944 1250 316184694 316184711
    0x909021017240604082103061806030a06060b04080106090626070e15100e0906060d09020a150206060603042d0609300e100203120106030204060305060d0b0403080a 72
    0xf40d441e401c96846110303140c00180e5000c0d80281d020f15409014070301a40880c3c1103080c04070100d40c01e822040342c00c03e42c100d4040e01144403a6810880040c50540c001024006140c9603c011801504148074081d0a5800d003200480d05100354001e003401d461300e0b141e503a041d8401180c0039a0250880b00c100f81e12500a00101088102d41e10728982d1250380a0f5039044480744804051190902102d41c8820800c610158140700540da016070950700414111442a01c2e20070000b1103200529000c80c00030741c09042894001105000c000d00a555019581c082e991603030b0310360003400f80c1d910040368020071142100c00b510201040102a134507101800352260540c1080c1641c4200886500d0081038803800c03000c0c07144908480407000780030710304030104070b000f0000d244072240a0072462508144030301c40c0c800303034082200d00c40c4200182d40c50003410917001c6003103580d243c1c40a0000d501500400000034145000540c481c185100b1502400c1c0e4000c100341040d5803103840403070307460401811006150b9224480c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 316187050 1106 316185944 316185949
    0x30c06040e06040e010f0c0c0c12020117040809040227040204061407050a080f0a030b090f1501140a05090901050d1e030216090902101724 61
    0x40381301d0000703191440c0945011100b8803800e40c9086a110090381d40a02480c0f41e090140c41c1080d0326076154050720f00e9201024002070b003c14810b0340780d8001e1001c0c100c20340d6807040c020500c46040910ba400010180c7e409403441c80c0c104441c00b10f981d0003070f103031a81e40c1d10304442c41201c0840c90300f07162609c040c103205114904000340d90404034441c0e041c03110500144000da82d10001807a0780d42c444a1110b200d6400000e20200024541030010015040600c0e04034098010304060300259034424032110f4481d01e10000300d074100b0090044c50f0284a11a0020344060012501e541d500e4001c0c07441030080c0460143d001c01d10403244d1100d10000301d46000c6442524003010540d60554112a0030243e26080c0b82d07402c2034501100f96800010044400e40c0001c692500c02c681548100200300c4003150910524810108803001d034202003680d1840b030316000d0149101c100003141c0b46041d071900 = true := by decide +kernel

theorem cover : BRFrame.Cov 316007194 316187050 := by
  have h0 := BRFrame.cov_init 316007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 316007194 ≤ n) (h2 : n < 316187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
