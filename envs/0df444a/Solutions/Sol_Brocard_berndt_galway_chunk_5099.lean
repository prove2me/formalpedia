-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5099
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:44:33.071688+00:00
-- url     : https://prove2.me/submissions/713e37d8-2303-42a1-84bb-94718c0c4e7f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 916906474 ≤ n < 917086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 916907724 1250 916906474 916906489
    0x30f0a090b150307090e0606010906140301030f020d0f030e0f04140105090702031201080c190b0307031d070b071e02090a021e0a021b0f06071e080a020a0b060a12140c 73
    0x4541c00070381c007d101440342030b41e0304c01c040b600108403a1401c10302c01031400146040a21041c88014810301e00190503008545500250340c4204c0d40210210607003000c00d0a001c4d2000150501651203407000302e8180c4900e140500c100f1100351032107246102d45a00741014421201e002400000075440b0a020001100326045003441c003030003020026082e4203501c001444a80c224000001d00d1005e0101c405002d800301d15001e07254407000d585008078051142e0202c0702d000b2000c004c031000c0180100900030030110f8002e4000c0c02818494a561140b0484024102d110a012988000e5100300020302140007096a030f00a0440080007040003580200031500403429030f48440e8109016070001b011480d4042c80e000100040d80106403004000f06a0210000743c0d01c0c490042d000b0101070f00780042c00c030000881d000d5119401c0d4410806a581d8030a01d10203561074200080407642c2d4174111001030014206401460115598000c8086601200f83d583e24207003510307461044018800c1c103074201c9195440c02e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 916908974 1250 916907724 916907741
    0xf05031306110601051f05090f10030204050f030a030e010c0c0f0f051234080312060a06030b030303061201140408041509080d2105040602030f0a090b15030709 70
    0x2142c250304039a91009403400c01d03005074002445408012050070100020032500c00c142005440c000b661601c16800284101821b00c2c4503580010388a03922008060705a801001034480c06c58801c1e0042c654282050750304c840c208002800146003203103c40065000e0155075022520414107508441e8036006000c00404255210040343c100b0701c2810440742c20001604070304224004c1c083c02c4240100b028190460740410608900c00c1c503040412040e1141100200001c2c019000c1500d5071080004491b03401c400c01603032950702c55100000700040d100e0091082518402024000c2c508603a02e540401002d5049a101d1080399501c448460584864103150300b441684550b0741c26850300e09240403200800c400e09480c5c030500403540700501202d0703400204e2400a000b14074200b1800000040c030207025004685030f1102003070800041c482003200c182c0203540714018a4042c42c2c10b50703441e09074000a0701d40d1114007a0070303281040c0c0892105110012020400c1201500301c424007540d501c0c00c1c1c0111001078 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 916910224 1250 916908974 916908977
    0xc140a02100b0301090506060f19090f060609081902120a23011104031202070e0a0903030f1107020427030504051e1509030a080d14061c0f05031306 65
    0x60340000d10310792107440b4503120250700803c114502d50b521a56a44e2000c1c03d6680700f03a118851841c40c07541c460340204803000104c6100b460359a40c80540d5401b40031858040c3d00d01c1c40c01c090010402910821041c0c0440d05c03820010040c020741740f034a0038211400c01d00c060b83c0000d1141030300b11401c10100304e00c0036000e1240b0151120780c02c0c581c100d04c08800484d00400096410700f18540c60180d40d003019241501d40018402610b004103210691070035449174442e01400d103000f01000519019540800341c000d000761424000c80320350300c50035011100c18129014545000b44044405800c0130707400301011651885075044d003985581300307000f00010f1042e4124001000094203004505141d0246081907100d0280c0c81c0403d03001500191000c403804d003070044c4075800444c980d0075555040012000042e0001c03100340e903d5506508100190607010341302548100088041030880c14900f640340c1004039001c01e1140500100c3d51040d81315450004140c816110500484500da080c4280400c0204901d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 916911474 1250 916910224 916910233
    0x4090f0318080705010c0308091903180b1201030f06060806130c0905041a040c0312050a03050f09030d0c05040b03010b03220b01060c0203030705010507050d0f06050d02040c140a02 79
    0x50200162a058003500242c0c1c89402c04101081180d820019100c42158981041d40803070b40d81d4691580f41c0144000d10101d61b661002548050540040e103084018010344141c0f00c0803521101c600015129003504c2849581c1e54200410215811408c031885480c42207001241881d0b407941d000703182540981d8802031802e0424000307010070551856200003040544018452864907072200c3c12802c0061504c81240e18100c400102023000030640d05001e15481440403c1d410070215008085420005040000ca81b50a010620000c0090751052044083c40001e618001403003130b01030060584800107070248601404003286220424002c2c40c041c0c4844858039480c0c1c5005650b000740268108000f00018007515009000703d0b920174980d505403031070b038106280c0c41c10b02440443d241d44a10303000030f41594a42800e04c6070003039201d40181a00303402808188440382030340000404441c1c3c148510b981c0052402c400c1c00041c00d16801200b102441c070708044c0c00541c0c0c80301e2990030b190b10242d18900141c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 916912724 1250 916911474 916911497
    0x6010602030406020106140a27060303021509010510091d061503060f1003110d1506031412030117030712020c010909060e0712110c061902030403020601060e04090f03 73
    0x4d0900c90b107001410151242c0c10111050390214500c1d0000c0c0c000d01c031041d0903200c9022039100c2042d0b6131004260f00f42c101000031a076a4100252180509a2600c440d240740c000031401c141e605018103070081000d40712202c426440c203403800c0010b040400038101d40380000c000b00d000102080c012548180014001c0782c1e1405108000c042c18500d00401070702584002c1c1040c8202220800304c7c2200f5a9448410640c4e2403055078009006400301c1540200a0f4444515189112180342c00c00d40c204c1c2c0c45004403402c122801c400c595106c802d02c040f00c255143c02440108002041d0011403c0c0038170b4103c00f135070700d8540e960f02c030780d00d0685410300d541000d40d1001c0145082075a100082d10000d1031480000c010b45030401c80b41008540024110b2020040d01404008100c40c40c1d40c4080d030981d255070781da40d41d6208004519a02d5a10807694400d00c0c5021b4050302c802d031032580c003c49111f668103078050440d682c08c02c501a275012140b51545500a966900301c1800180414202c554140c000e4940c08883c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 916913974 1250 916912724 916912727
    0x20c1504030b09030a0c1509020d1103011409100b04090f050a12080c1207090b031f0e07020a120219230109020f040902151b190b070503061206010602030406 69
    0x140c00380c8600807a1340f0401074480700e1544441107600c02540310100c003004d481c4121825004c4c1540c80e401030740c006d44084014003000300887c206005420260000c3c4000960341d1a4074484a01c00c075203d000c16080b4401e01c1c5220185e59000c0c020340e0074020000108443c0c15186d80d01e00c98900c5000715841e41c850160182800443c28842c25800e10303610342016185000c202108542c05482401d4a0303203011880840c030400c0c005c80c0c07044040c001c900740f4a516440c000c40c4d280195a23101c20703140145030103680f002c07640008040705c80f44249003e800402d50103800e075076139103d20328101eaa0401140995042321300c03840b084811801e051402411142c0e600c142c90f0314072030010070a001d045290342c0c0c502029800142c8400c01c8840103040100c400080c101c0c2c203800071954182800b03044075584500001c0c20300074486000c1070003000c0c0c10f13a0b1084884070031100d017006112079040704000e0704800d90200010b0449105000541d803140014001e10720b4070381c58540c040c5c5801020303002940546c02c0400d080c050396 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 916915224 1250 916913974 916913993
    0x190c0b0f0c04032d050c040c2c0102210306010905030f100c03181202070e040506010e0a0e16081002280306080a0c030b0a02040e1501020c150403 64
    0x890110503016281c200328000001500c220b10008004035040091145800c08280b8000c11441462803d041c0c28103582c40c1598031944500c900c24851850705404000b03451280d6400b4410107850a01007034021406d0329501d40c00d03c00388104030b046110b02085981c0125044440b080400000100c46807a03040c080b002400f0300d151034000303a000364040385a00d45100341c000346003d00100c443d03a00046042071004206c4c01750500c0744d05a000f000d5650580400c22a1011003088440156820355122175107465074800141402e0360042c0140c4d1040d00123108000e46081d880d900310581480010740034281100142c280340a0041ea580001d4a18174100710380302050041c03100241034098114a0f01004030004241c500d0700038a2259182c1080100d01c80c011700990001d0080c1801c0000c0b2612803001d4035020940c86828081111500c10506c0803a42d071802500a88040e50040c001820055661920b0303420b50251800c4501d04621606050144603210b807004015000704c0c0c8042640d8031829400d1902c0003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 916916474 1250 916915224 916915231
    0xd090203010b0d03020d0305060111030a020303090f030a0c061104120609050706021216020d0512031f0b0d0f090c080c01140c0d11010f1a010e0d02030304120602190c0b 74
    0x480f81d03045980e00280e80850024a03110301030070005100d0700d031100121081078507444801c049210024440c00070701e80000213148a620f8070340844030742ca4030900c0140d440e8015010400c0104002280305c0000800f2a0445140ca04e400c0114171308041e0344a4064000f60150720301560260b6460010105004041c0300bc280030b04000d000403c082d041c03034254001c181c07007174624104405440c02000011980d58101c0b23114944c0d0045d0032900002000b14000e2007d6005544c29102c00d06405d08031a519414016104120786651030510f00301504010b0003c003030680d402c00000c3d080c4da10540440084d502d4030f00c4001901c0c0741c000609156a140001400d0b0781c144c580c05500542081c041407203024030005407140a0320031032400c00031644a242216001d8212101d80c1c0b0700b030b0307410f21400c042040b0031000400000d88099a0b800e0003824018184900a28000800380d01500100420b1002d4080c1c0304074500010710034100140303060301a044003119409a2f4111a000464200794601400300c0c3d200820340 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 916917724 1250 916916474 916916479
    0x1518030705010516030306091b020d080403020d0e120a0506093c0a05100b0907050c060c130e01090c030b12031909030605130302011a010905040f110d090203010b 71
    0xa141e0070640064141e0040b105184080803c0d60052020548250444001002080c1f000d1040307502800c2c000f265020500c00000040c401d100da28102d076445892041c1c0a1501074018203540d103030200c0100c49140ea41c0c1e00890308400c6060405924a02c10040908014000c2001d080c00c0d003080c00200e800d20110031541e080078004506842c0c2840b00d841526001803401840c18181c041c00642c81c00c0c2840030203900600103018040d0404551100c0d500a020380c03140c201c41c00302d1103075981201a18140200c0e0380c00d600582c040c000044007000000010007040750500321401701aa51481d0394403240030260000c1c0c400ca911180e803031800030341500420301c40000c200e800c0d0b00203460082500365070303000e0310310864141c045940f5174000340c5004140100195800c400c0501880ca4078600e0b0b83c01c105003184007100190f28000d541c0010204c041c000c800001c1c816501e5441062a0600704405420351051070a452559903c0070401542060000d0400d07084800d0003045074100b0303004050848807c103460a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 916918974 1250 916917724 916917733
    0x11030d05160c110402070507170601092a030c02032b05071106040f030e060a030e0607020c01020a02061c02190f0804150e0c09070c141b0907030b151803 67
    0x20000f040c11003080b03d40b00003543c00580b14440e5040c0180f4180c15540816890050103003181044600480d50314141e5841c20024041c80d80c4a460107031540d0840d0310400c140440800c06180300c40d100341c05c001d96441c400d2045034104200564031485401c0d002d0760a154480d1111140500e4200c14010079600284a08140b200306240c07003400b40e100c40004000a00c20403e0054100402d4001c554022030044003400140d191518003402a0062510322040e96840c440c0c0741c0019030b040d20008219a22600603806800008165424414190000c5100c16282105030700782c40804403a078409800501c2500e40c0401c808040080013818040f1508010b000300211841000b01040c400354504941600200c0d0010307808141181c503d04154812a401e640720400701c2c240222580d10104442203a8011800310300b80c400c40c580c174141d4520201552814800010054003242e241541d1010351003401414080f03080301081002400701072004910100c081008241c480b00035a0390380c40f1004c0c007581a402032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 916920224 1250 916918974 916918997
    0x40c0b16140c0d03080c0f070f0516053006131403042405091002030a110a120e121207031d09040212150c0d11040e0604020a11030d0516 60
    0x50143d20200c50143c00e001c400008582c2e100b01c41c401325000d050301003800980721032481c58802d060304440355003952a072064036032062000b01e903000700c48101e5100900302929000e8181c01410b40101d015825900032100650400c16590248225171080d18048025504090246000320144140d8598000140c3c0f052005100c04003101000f000e288180c0b1041c1040e0701e88134031040362244550752106411016401c0d0b80780ba019000006090300c6d80c81070711f0304060fa60031201d2483d62030301c0c03e01c0003a14480d03003030b0100840c040c09060740e5054003001a1032420190f0100c0c580511781500c84141c4e003140d0a0000f895002e050b0712864a0441004000f0349001d441c0c0c5640001d1322126000e080640310b000c40c0c401c000e003a50020042d5020540303044c1d0340d2a17464603140c905e01d1f000b80c1007003054485040c2032803201103075580c0040480d400c0d0b0f60740700c086003160b2b250310003400000d401101001062208180001c0000f281c104040c1000c100b0810001c10349192514003d06e0ba1076006440c030040c00b4213032070003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 916921474 1250 916920224 916920229
    0xf110c030a09120f0609300f020d020c0d1713080607080123060c100f06140a06050c03090d050a02041b090306020f0f031303030b010503040305070803040c0b16140c 72
    0x114284290002d05c040340c480700d02d041c42c1c0e030344001c0d8440c20342e011110115030203001d005403922050000101d40b10000601d180343c400b41e0b10b4100600b82c032001070300300d1a0310700c1051500d005016101c80c02180d014840d642c0c1142036030003681c002d4183d200c0b60601c00c4403c1100c40d00411859038002c103545091181545460100402d4000c0c65031404100850300e114211142c60300002d90790143c816200b21055040201c482800a107561580100403d0030007a02084d80c0c070791164803003600040a88002d140314a46001160650000515100b250004000e00307801076413040c80507028940a88090310a0320038a10401044900c0d01c07000e50007010f040303e07001c1d180d103802020480c220394000d01c0261741d902024100340ca6030b00c2010312010681201006001c0640c03044089400c405100703480070041c0161650043d502030100300e8008000400c01c104c1b180c00580490b000d141c1140c4211564124680ca401c2c4074606034002414000c11003c0f014455804d00140012500a00d24400094580a0000000f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 916922724 1250 916921474 916921493
    0x5120a231f06030903020c030109080a0f05070203030f0d0b300a21020f071a070201020f010908130e0c07020d030c0b0f15010518040f110c030a0912 65
    0x58403224115030000044900900382600a07010040d00040301c00c1079110403000d0020400040150010310034010051014201441354095158001c2e1081c5d0174009203081c12541ca0a1440c20003041080c103100020050b02c0c2040940ba03000004400c180e02c0d00e0001407070b1804c9840080403240b14031032451035800d07c07081c8034041000407051041008a403100d40400f90f0320784445600c00400316180300e546d503094050710f01069481c40c3d17190f038284c410b070f030070722501070340d41e1715203600507450307070038211001d034428200154000c0c2652881070050f56503142401e0849401c5801100090b10382d00c2002400c10002e60001242c04090b11010b4032400f22802d00680c40d910074026807000078001e5808010040038140a40000302c41c1c244c3c05000c81506151400800360f100c1d4090b1140514401a851103981541c01401650241e40700c9855200c0380d690420204000360402c40341243e28280d03686002c4030403194030002000541d00d41c00003559605d040007030007030111f80e0039031010111014610100e8001070b40d101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 916923974 1250 916922724 916922771
    0x705010f2c0111061801050907351e07050d0b01030206030a0920030c040b010519030f020706150503070b0f0a050405090a05070e010801051302161205120a 68
    0x410358082114480c00584103d411400e51040511855003082180c0310700c4842203150b0740701e0000a03c0360707803503020141d45e5501c003900400058035000c003e4000c81d001400920150802c1400141015040c107041c050b00303000b0403600d0344014040403981e400c00d0407410006040241410f488254100440b0344030b02c1520303081804000d2162100101003508a0840d03009240d01d550410a138004074220341241e0302c400300394081030a029004040346030311b0324a024440c0f11b081510603100c0c54030381810000010080d059014409d018107030748140c0c240c0103070b03124400340c0070451050000003000b0503541e0309810104116441103100e5408003000b40000101c10094401074201851010340300c0b02d6410080c0d444c2d008170342150380c018007900304200c805c0b90103402641c05040c81c1d4550020030b40c0ba00c001110070310024003410b9004815203100300802c51583e801004100030081185450307200507a180002846840c000800007100420405031050040e22115080600381d04204102c000c600342041c0700f001400c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 916925224 1250 916923974 916924037
    0x20d02190501090c08030a0e0d0f0b07020703062309030a020706050705030408060c0403060b15090f03011b0203040f080325060209090c0408010c1107030b09031201080705010f 77
    0x1000d004025003500020a1282c0c080340c0341c105961198881680c0e604480390000000e601d03c1d02d031001c0c60412003000042190800048401050ba0392140c5440c410302030f00d4031086200304d9070700201003031061084202601c46840212022030701140031920801c4090200c010316081005480c1d4004e400088440440c9c8840c01d102c6e440b84070310700300300d41903024a90004907140201410484141030382c0c0010420303039120f01820800100041c00b0703c0b1102c03e52811040940c1781c2041644414a0901c80341c1e0541c0b00020000324200b21203560410703442c0507030300001015a0010400707001002c0c180705080b011b081000300440c00c06d0b02d62307031240c3c44140c030703880041080c03095030000d0809025864045074900311010f485005141013040014580b0780c8a44a100060b503e00482801c465101c0c41d00d03824131646000c02080a9070842e105c000c0c0103007018200c0101ca120030004400c040100c3c034681d600030080100a40101454200090682ca82a00d444801c01c402a202c511030041a41c031031460f01e041c01d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 916926474 1250 916925224 916925263
    0x10232805090c0d0807140601150f020d0e0307030602281103090d06020d090c0306052212020703301715030118060209150c100902010521070906020d02 66
    0x3d03802e100c1000d2040281c080c120540c0e02117035a42c1e00d200040c0b154100c51724022044070240009000b2039440356406080300040c0c03c10707042d00a0340d9201d08001c91201034024187c40780142e9a543d14001c03a1300c15240174051585651485144c0b4500d02c01c4164100228282000f101c05845180c50300c1740300f9001c8142c40b4401c041075100034010b41da4180e407000b87d80303600104000302650401c407200380035520085654a0820000401d8a07060046010403203264202c44121101c07140c1d940b0a15817911420341e011441899000400f1541d1540e026461a484884503030082340c1c18613004456181164030381003170100300085098030302041d050003a40080007414004825180b10b0011340541020320088014a0306c50805000f4800c2c035a00400c8064000c9800e006088040f8031005042e01170030311840100d8122075580030070b41d012034001056482c41490050311f408260402c0440070440c81100080303607060b9404009080781c000c0101c03000b908890001b0140c000342d02c20000d544551040d1041c0d030070000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 916927724 1250 916926474 916926499
    0x5070906140405100206090d030c0f03180b0106121107021e0420132c0703090804030f050f0604020603070f09080709050f07030603030210232805090c 66
    0x1100c82602c010301001440302180e1103100d18025a50703c011364811149018040184100c54000e1141c80310030200364a9030510202c0024083d00104014540305d10082001004480010301c1000030070301801c81a01c4007201e40300b050410b10100d403020381e50045034440820825015030740743d030b040440c4010110100c482c80d14120012030040c00c22612003040c584610b10350591074158400140c035a58140f43e113841c894503600d0007428509800c100c180c000d09a008003410035580c403000c1c287c0760f00020b2806c0200341c0b0f03491650380c2c054550255200303540c5003140078100b0f01049000e00180c150310f9200c2e0010440e03420a40c0000703913241700144c401418807440c0d003042c001150140035001c00030329400341a0b60000707075500c1c0351602900048958441c030503019070001d1101400b038455401a240c05900810051303a02c0c4000340020001f28480f4240da081003581c800f000455070402620a40d07002009000841c001048048107201c0002c1100805091000b00801c10000103034511035100215107243c9080e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 916928974 1250 916927724 916927757
    0xf04020f090a090b01110718050c0c0f0318030c09062202030903030604061a031b0712170703020913090311060f0403021e061609080109051f05070906 66
    0x821001c8482c1c020450740c0e00040c1c4000140d04c4841605001c0e2200030506016412030364460000b805490002106104403c0c55450035611069201c05d0858005290422415089141040e008199032940c1d0000568102501c083d040c1c041040f20240c00902030b100b00000016075444009160a000703007900c0303070102034054410f1500024081c84000c11566420844d604030345990044070164011802d245002074000030041490b810740c61000200b07400c41d03c0d16201b4203281c00f105c810b14501140140806000f1854a05180100c440e294980a0b00e054011801210b06940140080107140c0f06011164694a601e030000f0341c0340b1401d0700300007220b500764942940d5201448029104a114440810045080f0045481d0113540a0303006c4940407420b40f404903800000540c41c20301c540d0030400c007059080a00d407070440545419800c0c4600c403252940340705030845903541d074290303025441aa9a80c4000355108038080e690f60510401348598601028054141c00d014800c40c0100300045c0c446440c0d19 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 916930224 1250 916928974 916928977
    0x2010e010e040f0504020f0607020303160c03020a06030c02010e07050303121b041e080111040504051005060c01150f060f0c06060305071404150f140d150c1701050f04020f 75
    0x110006004010034030028094500404c4200c500f280118030805411110389414401c0e13448241d4010b0040d03181152043d01d60010741c0c1c48800442e6000700c0030f030010005948401a40c40a45565500018400317040100282940c0e00240c0c0301031150030143c024426503c01000700c07000d880d00940300c4440d644138420340c044c02e04140346401040040108001c200c5103159240804504071031080402e00382e4540610070b0888500c083d005150340c10400042081e400d00d6002994080c2d03480306284030140c0e0b01c8001c00c2c401d034480d03152819540d40d1f401c0c0e10001c02132908c4c40d610241107100140680281008405044541042c1403441070240c040c0c9407000300503654000401443c0c0c07140c00d4034034181c1c0c2c8032480e500020308040950f110794241b000001c0c40170268440c800480700005844000d082c58105941c180d070b01c0315068240c002c00c01d1020f56010540325940060108c602960001e0b205190200052811010502d000e40305001040108140d6840c0d0b0300c07605051800301c1d80183d03100320020082c4030a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 916931474 1250 916930224 916930247
    0xc020a06031d03070809090108060606070f05011d0105060a0e06030a0b090a05030403061a1c08030601140c0705100c03021005060609120c13020a05041208070f0f05010f051302010e01 80
    0x201e200005011302000482c1001c0c1408520665200751241d072584000c2e500d85c81c080f00c1c07080d000f07071041c0400b1001c034410107084140b040c014800090444800100c0001d81c0c41c001d140f040050391544288103c500300b010500009042e41100784c48a401c00b500060388644145001500c03090114000c180300030002c0c00300040c829808002c40c2e80d40e40d80c0780b40c548090420006280803200e4281c400305c00ca0704003810040000c402c0030303c0001d0110360030b030745802d41c5400182081e4100164100a0081080440020044003058800604201e885d140401c400c100743c0f82030007001c2283c11300012001030703000242440d100b0001c1c0c4002c90255104004510f01c2d001d0310202650100400c14180202c501c0802e403401c00304802d03103014230340c0750800031120140d1040c142030f10b002503400c110400c00486124030342655640f1a107211850000640c4400a00d8660280150740f2251000300c0300301041024030070480c003d1000c0340c050105140c10268407103125032510003c1d050001442000c06541c0c85401032264 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 916932724 1250 916931474 916931531
    0x2070b040303020a0501050606090d0f1514090106120506010614160321020901120b0f0303030c03070e01020a021c140d032013030f06020d0207060b100c020a0603 71
    0x4440c1c1e81d906000b55a0212904251019403908002c02c0c118181101110340201c4c0c05018040c80c40880d0352107403c61301e1410380075980300e20040715186e800c5400c0d0080e0b102200c65140e01c4442030401c00d1076142181d02d1944100a81c2242800c044000340000c41d16604603001410043c003d0128901111810301c541070505560400200101042640010b9102c9940d1101100d40c0271051b64071205800320f1060b4014035000c1080703440c602c4030380384841d002100d001c90064840c490085900012030300c0c0d60000e0781d60b00e02454010041002540e4040c0900a11000910050030007620980100354140312070303690054040030440101c0e041c002c008241407a12410007040315a81c1811a40060081201d5144403171500c5140055078002e00c0d030907080e06c01046808a042e50500c0c510350f215240e882000d842194665024400c0000c0441d061000e004158013036131010640e103103200200000c4000c144c840350305008520300104007603240e01962605a54607801c1c00035840c107440006110f2951600941c49 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 916933974 1250 916932724 916932727
    0x215070c0f05071e03120f091401050c010e010c180b1803250f050d0b07180e010b04030b011e0b0d02070f080408151501050d020708070b01150302161202070b 69
    0x2400e01070004c400d0b8100c9001e00b0007031030418624131045490103002195500012861002031001d40e500e510740a10059050609503e0503000d41c45950a440712a81b070603d0a95490780a800b215804c001440d41003285000895100e50070000602d40c140142042c5101845100d00703400b002d508c00b040b413041c000f002c0d5400035000100500700d00404c0714440c001d02c46e5402ca40c5100003040d0810403208051158404900360035330341d80340c5040b140c0400070500c0c04048622808001120483c0da800d1358064070031702034415611410b43c20030340300a08042c0d04c00c0700c040c500340c40c003d01d50547c1c01c594101503c014824055558420a8000010f8051284003070305032003100c00c00b00304100b6000d004008440c0710a06403050b580b41c10003c8240580200c07890440c90481c41d500d85080d43c4602c0c01000c244540a0005080405644520010b0b800c0310b42c088800118140050116500300d004284160000c0d1505515281c480030301c01408440900c40244204a81c10b1481c2d50140280500400341081700000e6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 916935224 1250 916933974 916934009
    0xe0f09040f020a0504020f0d150e04060c02061012150617060f07020a0201020d0c020a03080f0901020f06010b0714030c0105041a010e0106211d0c010215070c0f0507 72
    0x3103880003a0070100d21038850840d0000c2c01c0c0c1024000e8600e0107403140030340da0402c4c0c8102d0100b0090411060184030090040300007081d01d101c102c04540c000c40c00ba00c40000e4526180c480a07150120140c40d0b0461000c0b050020070640100410328101140d016502002e06120041d01001805082d00728484a9034100d00075124614001411442414007140c00403103622524800e81c0c0b516500a00a40140c0098213000510741c000c9010303c03400d83c03000d800c0c0d602c040d5994030b9100854114040c0b01c0d01d61880020200440d40e410454031000102c003401910440d4500100c0003118413842c00010400c50700e01e070f00f141000000b80700761460500110003e022628003450700b00012000c05602901e10300d4084008594000c445410506a55180c0c9034407041d0680042188c141c3c40300040091586500c8070312003007024181182c100700b11040c075030060041d0448100060306004c83c07900303480220031030780c0d040280d500c0d844842c00101d40d4021503010340c0a0b4080c00c1c00c40c20010a80c220080080040400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 916936474 1250 916935224 916935233
    0x3010614031b0d0201050333030f0d12090204200912010603020604180207050a0503031b0313060b01110a0b0402130b0d0201180e1305070803190e0f0904 67
    0x69100480490642e80c6250724512045040701c0c56149998001d04060081d20040d409803000390b420070003024111154030740401c104039220745080c40503000b1144003042540c00b070404114900780034840d80007414038003405000c0144842c00c02d8004109480c1c8032443c07a0199100c542c4001400c44c40c2642c40c0000402555405000d81d0101060b40d0056407141c2510b03441c1c16040c0300c0c10b025290f00070802c1e03142c98581207080c040a20102c02c5217141c50750810180000810802c048000d20b440740c4091601c0c0d00c0e1503c002445422407405000500c4000c04c00c020307000c181d00359600d440d50350210000600000b5003004951800080101c40490f1040480c0c060500c110050b00b64441d0b4802c40e10080c01821090f119415a5810300d13800e40c100c0c0d440441800150300035400c0a491441c1c012240461568a84040c10304600070b594411100c1620510403042c0a410f200300f40250803400c009601e0021034000b20305d48880b8008030394007044030706500010956122007048a0001e0000c040c21020b0038182817 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 916937724 1250 916936474 916936499
    0x9060114090301021201061815080a110d050109050601091202190807060504180c170603010b040f020310060c02091b040902030403170a051306231305010632010e030106 74
    0x81d41c7c011070a0380d0380c0ba130031143c01c0d0300711b5105442d103030021041311401700314007950348582c0500102229600c640000044030003500c090240d408160700d003c901549452407240c100c4070090715460400484030b0781804801c2116060a10013981591000c10300b4484030f0315034200340000e400a45c2c942c0101c0f0b40009001c4d910501500c246c903d80019501c0c1c82d6103105d0880d045495511181000c41d21507010f086c040000f1181e240c1d88800d01400201c0c4132040030000504950f2111038013094075501206000d041c08450200740c0142030141030650150b031440d00045c5040780001c094102d006034250310700b00341c100f500003a500200003140d0b0940d20303414203150150800d00b80d080c415680408400c00290700810ba03003c0d85010304016189520081d486466402c05020314880090030f002c3e000380e18039a01c940103000c041c402c4401703001c1c15022800c1031030700724203444175540315550f0490345400c01283c8440c10080003001802c00744103408070041c00801038a01280c0c004900c0ea16502e0078600040700301c003088 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 916938974 1250 916937724 916937729
    0x20d1112060106180f090509012409060e1509042d0b090105010b040b0a1806090e0c0c0d081f030b15120d0309020315090d170609060114090301021201 66
    0x848000c01e104c44e44d001d0107001801442149020304000301e08110f0010250720003904a1911000441e085200f1440f12504808541d8841d960091225080001072401e20800016045014400c640b0742041d20030780031038038921511644502a080003240c204480480004201c02c1d050655038914a41c1418948100d4a03442007603601d011208001a00c9141c184600d5041e0340c03800e4040d50801e814856a2445a0000c0040c4420b00500707034036102211041a00080050070f480d40c0d0100e01c2ca04228041c200b8074000b400711010322409001c01c111020340414002c4208500c0e2800d020582e84100c09034244141e203989407000003108903000310a00c0125100c20380b20720680c2180214002c2c0070014003001d518240380010098002508200b0014400d4100c02c14880c00101202c260030343c89800404082d9081c0c0786c000140c1c0c4510900050660840c3c0d000083d1050440c10b070030a880c040d8085800000000c180034100070360420500c4c4544490303c2543c0500d1005070003151520000f1800c0d08042a00f070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 916940224 1250 916938974 916938977
    0x190b160f08031605030708010b0d02040b030109020405100c11090a0b0d0308060f0f010503060411041502010207170306060319021b15090309011d1309050a030801050603090307020d1112060106 84
    0x110101e1083c1d50165048030b004822654034101c0301c0c0c1ca804d01850864000ba4186034132a6001c00c0001180f000c6000a1070103029102c1c0700507600e6280004101c5030002c03654900c03007401100700340788001c44c02e840c014820020050b500c0c9140340c0c0d103a100340030041103409101ca50000415005005155100e00e40606c0b951040d44c0c210040c034014400c00a650b210355843c0e038000358040000031400d04164000d140800d85030200641040e4503401c03842c422001d214070200050390301007903000c14001d02a0452808100c0708644620b50704140010602501c402414245000004000c0d4542c0c551294125402c01c0c10304189401c100c03400340aa10317220075044034020740041819010600b101c03008012074004e0b03401611850140328600c80b50383d00b0203600211555200f035800c50510301141079402901040361044004e40b858601030f14014001a106030091400703003006104001c03111000108a4001c0c68049440500e40c00711868200f00308400c000d08150002c01d0101d82c0000600002806816200903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 916941474 1250 916940224 916940251
    0x302010f0b091501120219020303040c0e0c040504020714010614090603010e19050705220e010c020d0c02061e031915090e030d060b0307020705190b160f0803 69
    0xd490800c0500001610804040e03c1c02090882c00c541c02010180100c0301c80c1d00c40507041503c0c03240c0345840100460740086c0960000000c00003089520300018000d0540354010502d1030a101e12044480d0085004060080707034001040f00c280407107101107400e405c3d40607000b4404244c65a08038644047c0280b9038600580070603022070450714042c02180440a2110003c0c036841c04841610751031040110010366441c02201e20200c2d00d80c0721000140c2c908208040b25030000c1000312446411100308408008469240c0745101d20060b9012410316144400c9190480c0300150702d00002c1c1051098110409809041e4071001c135403200550051031140c042c40b0701c0301c03204106e032403042d905507100401c503400300c1e001443d414482001c02c3d92050001111250440e400e01e04444404030844c0c5c450303004082944008030410003031540c1002004090304050b40c0d1040021f948181c4102c004101b401518908d04c03006c514104424a506503c0e0308158001c0c483e03140700445414814800d620944140e0076070b040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 916942724 1250 916941474 916941491
    0xc08100605030613060209060d0203010915050306070207060f2a1101020604080906030c0913060924030605070507020d0b01090b01080402091302120d080117210c010b09040302010f 79
    0xc0101e00f030b03881165412107000903c5580c1d44c442c4000d501c1640780356400b4005101e078180340b54151019601900424400055442408488411440a0f42d03c454460750010041104071a0301050300c8007181c03658242a00c040041050655440403600f0100805c000006032a820301e1031510450300c02c10380204e920f11424500a0012a102c00b801c1f5000780c050542001200b503c2e0600c5401075a005901228190821083c440015054099025200d41403503c4410501030021f0318071400e640500d02ca4202c4015460080345001000520321020f8031040d541c1c03000a070b0035400b4030f00b00c0b40410f500810200b01d0507074a00d862144003a0030b00640702e43c00d140c519050030b41c3d4007540a00f80103540040c00d6401982d03482c0b10811025034444012a0842d03001500d032600500d00300214042075205456001080d81080300e03400e40c244001ea000708180c0c0c4600880e9070500368008d11408010513070700d42c2e01c2d921120343d482036015000c1140c0b1540c02885003010172003403550643c00041c82041c08c030003c0c0010301 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 916943974 1250 916942724 916942729
    0x10302100915050711091e070518040218090c030f0f040c0b0306040938220f05060f01090e0f0d0f0e09010303020a12020f21070c08100605 61
    0x460040003400070b440d20800c0903850141001c0e00c02a841003007100182e81c024000714141c03690580da0b01c01001e403017102d000c4000301400d10312984600b441c641103080c10352040e510084405d458030414050b45e800240c644100f0300990360703802c920354050070741d2102d804e00000c3c903181d0350710031100003040b50390000200d14015420f01d042406aa0405503001d11141008800c1c15640e0011300402c0c0e001d95644d0701d810008102c40c0340405100140c80c40503140c0e14140000f040d1440b45481c1c2c0c0ca4a0121130020460032000c1c4400340642d001c620140d04001050901d0161296840d5690107081489a20104800741c010442c2e100d05035000d0110501c2034100301480306945000a600b43d0380300f81c0004035110820751060070703400d40ca50414902026035240b0300010550801c0280c000380c0051300b02400c0141800035140c0182482500303840140403900c038000005486031b4400303440b40744001c601113060020910401c00c0d42c51451f040074410069075594070805540380c103031005150030310342010030001e900d2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 916945224 1250 916943974 916943987
    0x30807090909050709020f1b01021806090d1205070501091514060114180a090923060a1a03160602060a091106031b030c0901180b070b2d01030210 64
    0x10ba921200610380c40e401c140980c3c2c042e400451030509002000d0080f41280180c22685410741e0b903103807000680d1481600e20407044500c400540d0f5004090411801080e612030300c81003a0400e40089010002c80d0424a04a0341c900c1101c0b001382440d0700b03000c802d90600c40315080140c101848040304202040e0440804070b1501011a01c103404540c007140e210380c03d4402c000040c502035038070a00d4220a92016000100103000f5600a0024070340d503100c0020801c01d40781d030141042940c031100c2250081c0a040015035030100203024808240d211102e0000c03003140030030b00715003041c40203055440007001e02010059200c0300e40704020040c8070b07620200c2c54100c854411910001d402509200030185000306108681d40041c00d120300500c1c1d070f60901c02c5103c2d41d40c0050340c043e00d140082075a80304c0380c0000051146181480996a042e000c0a081120010791005c441e030042e0721005c031508680d01c000b080700d100041d03440b40000b0f000f026046000040034104003e41660b00c02c03101821000105801250710 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 916946474 1250 916945224 916945241
    0x3090e1005040f230612070906380904111b0d1103040504090c0b071a060f0a0e070309080c0106030201030e0102090d0803042409031e0207140303070804030308070909 73
    0x4140c107500410740c04e19020140d0542c4280c014180741d00d1070f804400841e140c240f05074007440010303a45610601c052540c10780c80028116403c2c0402901c9250038204008500c1d0b11701542014003c00205656641c4554100704842c075034007a0032549505000240f03040481319842041850b0245034400c3d003099010700080072980101100450800f400c1c801031200501c05d201044e40e040e41d101c0b00001e8045005401001070341e00c503603010034100c40188001003003004007a01c12071140c10101d0f51900389484e240c0340f50007160000029542075488210055000703044212010340b02840000c0ca604a6000540100c0d0440380b0030b990401c40180703802041800c034004c103110194045803002070080840d1941c1e024613000b41c01a0b105084000e1303030303030380b4801c00d00900860003a20759142c0f034080d414981c10008000d030092983d090044482480400292121064002d644840f60b04810fa1510307520100107803591558003541c907030358a684074107001e400700c0c02c101c03800c1d4002030100d44081004a56806034060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 916947724 1250 916946474 916946501
    0xf0f030c12020a140a0908071203084c0b1206090702120a0f0801060f08011e0305120315120303040206070609021816030606140703090e1005040f 64
    0x401c0a04015010007035030040020004010800c01054682c07500c0c0c0b002030881c101c40b5265a50020710b000b000601749050355001e8848080740a40620109070000e100c50345c40115030031680d420b1180c030341e80341040c07400c042d502c1005480d0050003e003a601191010f8027034412600e0302c51034080d5640d084407040c0d104004460101d503a070140498200e090108070103030040014015580c02c00d10a1003040034a401c180c5080d0300003174ac1042c001007003d802556481c0075003070b5490089100207010344050907005040c1b03c4d4441c5106400d180010031007054500c40d001d0350340001503d403003000d00119410160019504240f0040c09203100075014a040701c02c191034030f071154020314156615602006510f17000558181c0d02c05446201140059440044404d0030b48401d41d4000746505004588066040404020500b894900711041c84403c0e00403040010300c01050028955828070b030701c0c00b1504034031183d001410084c0e4000c11b02031606020403a980684909480030450901800d400034140d0b03607000c0c184c08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 916948974 1250 916947724 916947737
    0x5030a110f0f120a0e18040c0b0f0a0e370f0e1b1b010f111e0d0e010606020a0323180d0507081e010c0807180e070f0f030c 54
    0x10740940305102030440d1341d085081c01d038007266035000856115909044501a10020310007003008014074103900801401d0b4800c402400c00d400c40160810034800c0480c0c6a05000d500403500d80300351f0b50440c40c0c107100080c11684141a0020100301c10001070401c2c15003040e100500c0c00030a501c48090b0840f42110240c98034102c9540320081c89404060541810418894003041056407800301d981105410080c84000000e00b60303028001d100c220b03620803645655145003001a948821007100400002c903424840096586107848a800c0051101b101140001c0d401e110001401580206904060b540a615141500c8070f4100c441c00c510710105540340c006c2001841005140d9011710708044441c00090540313402e081d1140c4407107140180da98000c000710340c4030591600c90340d811304002c1c1500d00744c4080240880030304042e014107540c0006003002e0801144204012078201c07141190401020420302c2900c190800c02e00040054a142110300c02180d200c690345081584039124984011040c1c0d612030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 916950224 1250 916948974 916948993
    0x1e0a050705120f1914161a0c03150303090d1b1e0b0c150f15061c0504050709090c0614030609040311010905031b01060f0b070f060905030a110f0f 64
    0x20308100720301d40c500200300170007500c0b60078840d9000740c024401500c0340322901c0b00140e01468009603219114652000410ba02c906120110201a003036a401c035000c2500e054000d14000c010a10718040c801c482640011030204220074020701c4180344081d0131002420221180d00d07011b8807101601c0d480a40c0a20401081e0100403801120000d44000d071281e0303040e40c2100c0d070903144c0c8458554017510700c003130f103038451030148900c08848070912564600281c03181030812126400150480c601d1900755003015403148005003c002081c00700b41c000e058807030810001d08010703007005007020405006003004202c2c1250b02a40515010701943c0c4228001004402c4a649981d011900f0b21506034007aa05036403903207494000110140040c02990042c111030b0300300007000c1003030a030944d000e551081c40b5051800c03909001e501c840d041220000b603008082c403000c411041c0352a0004205080c0d015001d40004921840041c0d40440d2451800645004460103104401c0d0560384600481c80182c1d003940c0841281e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 916951474 1250 916950224 916950247
    0x307050a08060d06091103070602160306111905031509090d1101231b040302100c050a0206040b03090d030b03151b0301080f0d03050112081e0a050705120f 68
    0x15a81d11980c040e1540708003c4880c1d50b4842030f01d088440480d01c5c024602c0319080281000c02204c40141310900c0101002e62140d002c0312202c17030701c500015002c20b46407540c0300c035000100c004592079001d041e51903224003d104a00100140c001b610090303005501700200000324580001e00501a1903c0d001a0104001950040d00c505c80d604420030469500c0c0c0c90b543c481c07200b51030400e240441c09850485500d1500403076107561414102540c402e0208140070920142e119401019500100ca00b010303801c3c0d401e0750908518103600d80d14020342c40305001402041c0c4010101c060750144102c10100c0780703041350340f07201502600e81c0c0c0e0340a60381542c1b06042d802540100503810541158003100400020030840c54000d1030b07540f0982003295503601000c0c0303882009800b000040c60700c40091808003c654100300902c8800c020809001e024a0804201d030000700b802449003008040080c0b40156546a41180241c01c0d90000c800c1620700f40900c000c0510032139000340440d04000138221840d0b00c3c0c030503100d20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 916952724 1250 916951474 916951487
    0x3120b0405010e070c1b0909151a06070303020c0601260c010f03090305041e0302030d0f09030204020c0c030709060915260703051213120f02091302040609021e0307050a 74
    0x7025101d9030241503440741c0c1111000351b004040e20300750202081c1055981440040c80042002085482e40350203c010824940040c84000b03078081251060355458140c10210042d000340760700c2034181e001d440d00026044d104a034000640e03821032074000069084c0d012000340c441c04a801990f012501201420034028404e40c8000301c014802c0c1081e070305150300c400703107403c2c1c07000d42102c1000c084246181c02d0040d4641001420302800c000c1c82d1a00701c0e0088420f0051102c1c801e480024000c0c2d4001c1b40700141800c041c000b2200d102c002a04030b602c6a41e1b1008494003400f41c038800c0b12410b40c5050030585120740c01c0b10000040c0d0384420504e0100c150104406080141c1c0000c010f106d41c003907180080006201070152114840c2202021a101c003121405070502c510180e02520303600c110442c2134400108801c5005250a4044941c080950794907100d0f901840ca104d080250320515000d80892651301036400b0f01400950301480b158540404014442e8610007541c50b00301061050020100782480b801 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 916953974 1250 916952724 916952747
    0x2090c0901090b1309110301060207060f030621290f040609080f070c0f210303021b0a0501060b040605190e04110a1103160611090303040303120b0405010e07 69
    0x2d0b00d002c2590f51840c0c008429009440d294030401c410b50001c0141c4030203070052a01d00a20051420302d1545800000ba603650000c4c8580c406000512a00880d01c0b03010742c0c004001130201d00c51690002c4500f4020007400745110f2811201d12405086100001c024814290110301c405451107070661541c803f409001c01d001081107809035150558540000c0341c020181c000c550380c103020b15484810501c0e007240a0291908842d01c145a11035040000c848540b0391005908000d820341c0c0005100f505084000c0e1241d000070040c5402480003580003c00d0020f00c6000250044008200789500e0791404000d92040d0b10442c00015018004114007201520080d40103203102d04051040032210808a415140105200e1003035260114500d200e071504a040c0c0034003030406201452512403111441d5600c0d241d0284064412951000c0d41c0e0b8401120b030f400c507a07030008000d08503500c031070b81c82c41d00410550010000035540c0342026080600e0b801d09009490503a1103a04c0b0045050f9100c001c1107400d000400c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 916955224 1250 916953974 916953977
    0xf02030a0e0f0621042604050105130e090a02030f0309310501090603050c0301111b010b0a1e090e15070323061507081801090b0406020c12030702090c0901 68
    0x2041400031340720301003485202011180c1180d850626003801c1c0f10010161443c10100d600364036560313501802e00400e046406540003400c02d0303030b16294104289680b169150b00b000070066020f1084c883c0524000508807a180c0c400c0301150301031a215103120352203002d8a240c1c550003600d2290301c413200c1c5040318401030042c480c400c02c46d040d05141134500c00c103688081c0c0c00520007076a00d0b0018001e0250904c01d510740388000b80c009103c50310300690455024800c1c0c12401c407802180e40d019902d403850070341016081220003070100c6540d6881d140108010250381c5081c600d25031920380001307000d08071070207103c0e99070741740308058070702226603000c2e1683c0601d0007001c40b0101035880341a0581e021840b03450f0301c00c0d0f10342e107566001141341400900200a80260f5070240c40344081c4001030029043c0801c40d00300c40e29443c04850501e0300740c030068520a2703842e00201010139000c100452020303400603610740d441074100c0702c003200f040c1400b80070303038480c8245070010f0340040002e000030350070b5030440e001840d511006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 916956474 1250 916955224 916955227
    0x50301150e0c1c060605311a09061b0706080708010902031e0411010f0e0a1806180504030f08070f030c0e1507020906190e09010f0603120f02030a0e0f06 67
    0x3c20044000303c0d03415420a0707000c640c01017400d031400e8074544414031540354450503441100c902032a00c0d00c442d500070b204240c0181210746411008280d01d230240e804a81c030180c041c232346510443d0700c0e07448080d24045030054148507a107030014010344100356050140203240c0321f07005241d082902030f00284d400103141043d07240c454803055407881006880c26204078041c800744a040d00740c47c0001022001121020320400c50b4405003a80e46995074002401110400d04500c103d182d400040103001c0c0c00f480d4072070300340318520002c40705081506400c900c1c8a1031081e52425828624008107407000c48040d02c101000600010040180d107000f640441028106800c10803141e0710090b001400d07440e2140c2c41e07428100004902c2c0f100318241081d003030b40c1020080f507281c0310044a0010301562031b15148152809880100081400c0110030b6104007030145031103200307008582e143d0610260f24000480d40d8000204064900d5103564804030641c0c08105a41da141074005845204202c0110f42ca000f223541d10000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 916957724 1250 916956474 916956517
    0x120c2b0504440f0105071209060e0a1b06080c0a030f060308041d0906061c111905130b0907180510030606020d0f08270a0507050301150e0c 61
    0x1004112091882c941941c0441d580c000d01000750400b240034080d51040d0381403505201c40c044d042560016560584c1000040c500c0550601101401c10710440d4102400b07403008000c1800704c0501640c03c0703141c1c0408415900c565502c4122800c95003203d00d1202c2c24028031040450780c1c032941210102012012012400a4aa03141e0031096806544070722840c4041201e086070480c003081c20580e00c40d080101030309144c9040310200b0b1104182c50403180784082e80f102c0b5842044440f003405e12146002800f00c40c0c0d160101d07502d0792000c1e15540546442508a5240c1e4000d1784014014a644041c001c2c00282645c1c680c01d8050311280d0a50480c840c0e0000120780120f40ca480301c54000740d00c8201560007080c0b031450120080c3c281201c04003030304100151440e200c1003440c0c20001e4150441120852150403159452080104905001e464210303402030301d0000081c0000054090107030741c0c00701c1c0200030004240e00820344904481c800c1600b54941000014921500712001e800f10000c9101049000301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 916958974 1250 916957724 916957799
    0x7271d0c0c1f2004030303090302031c020405040506030c18090a0609050a120f08010605030601030f02070b040b1302210c030604061b11100e120c2b0504 67
    0x2001480468150b0140d4900a038224550082c16000520380904a4500c482d80040c03503501d100310b000c09800c0c180c4a141d15810507108100300c402d4280c6803403294644104d5200d400000e50f000f8455a485030b810035021a07283d150101d102000711500074034108510580071400042d2400003854103603213004a0040320301090791070180d000806d103d44060405204285032090000e400079056008024131040c1401c0c11503041a10756045d0f41c407604045440e9601d0f01c2c012000b425914010b411410300218004003002600c2c180da501951060300340d10038551380c0050443c0700ca1f150031000b03503005c03070035030b400703c0c541103080004003814a4008141c0b000030a02c0404240b5101e02a1021a10380daa100000c02d81d8801210203018138000364030b030541155140403001c942c4c81e20810201d1a40340e64402e42c5505c02c40313042101c03907040c22070035074103036101c01b01114199140c540304202c424400c04c1c4001e10780c3c5206101c1440704e40907241b584030542003a08000c804000f500c400044001c5d010b442c12a100d1120 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 916960224 1250 916958974 916958983
    0xe09061b040b0a11010f090803070c06110c100b0f150306040b0d1407060c0804030308070c120302040f0506090607170c0102040b0705010b01020705011b03050706020307271d0c0c 78
    0xa00180c0c886001c4c0070075162000782122200c4c050390400f06d251000307001c00161400d08803600f04415150a2004480a0900000401d52003401211021001030301c01c0703100b58045860400f0118224080000c1001641840079100c0130300d204a41c0401d00b941d448007250342d4035020b5a04003078040c0000603004170380310100d003842801403015140c0d2030141014040b9031004011050240000f4901203080e80c01d02c0d5503101c41406103010041c01d0002c1d2000090111740310300c10010003960024212210a02c510078050003e60260141281e84503090b0b00200b550f0911070202e440e03ca1010b05413500e400391035161a003031111030400160a010080001c289442800d002800c05013500c4540c0654541841c50094210780c514100c03581035422542b0708000a80e0040101c02d440c010200c40214250001e01d0200c0342d0b07200d20780008000520105c10722182540c010b240e00c50312602c09078800740303280b091b005c0c080744003070540300307134180c1c046e24036240301e55801c080074071079003001064103a11f081c4044084960f040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 916961474 1250 916960224 916960237
    0xc0402180310060812090618120607050903070608010807030b06061b0105060f041e1808130303021504080d0b0a12110a0b0c1b180c030901060e09061b040b 68
    0x454a80400340401241030104080a80c0645150340c038008000010603c7d40c003412040f049800ca8418582c00e954880c03004079001005040c01791410b0385010320000e4041e03080707400c10901030300c202c4502140b024080c254441c182c403494001030404501e07550318050a000c0c000d2010744c2106c8107010008198580d610000f601c4e88a1400200d40c5180c11424001a1400c0301e030740034400c50600c814088029501d80b61007001494030300e00403411211010580c5145564003200805414002030405800b042d408200425240700b5801d442516081c2c0443d1801034105683c00307409104100300520340071000d6405450480b86c09085440050b90301c400380841490b500313000b40c844c00c403d000e2107840351604120b0f81c1c1c041c1081e826040c1c1070125441c0726590b1010700000c2d003203981d500d0420240d030326500c010ba80984601c00203e42d44a41c500b503692403441e03400c1502d80c00455070031b10002203200f0042980c0144030301c40b00340c01405182d0341c4400300500700118200224038844100004500414400000c014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 916962724 1250 916961474 916961503
    0x150a051302061621053c030f090610060c0c0315051f060f03052715090a02090403230a0c0c120b0103081c1a040b040b030c04021803 58
    0x4450480741000c944c20224041c070507001201380102c0340c0c90550440261540e01c0c1c00340d0280382080c0d02280881c00c0300000c200468140c4040440c100b80e00d06410700c02548103040d26545424261503020320300da03890f1000d8030012802c0c0d460150500400e440703003119000b424061070784814103a80c1d03500c400300029020b00e500715595491340c0411882440c100081c00d041d1004040901d001031a0080c01403014000d000c006040548070804980b00784a000010041d03404120344900d80408050801d503a205180605400a212480001482c00d500802d04c1c00c00c2035006051660b260b41d0300d942c221a81c44002c0e03500702e8a0000000c40c40c101e5001c2034050500c02590b5207460f84040b20500345114440c43c0b5a100d03c031004d590350311031400502c400400604403030703101032447d45440d0840010100105218803502031703a490099a12040400e61074058540700d070540f801c00940141c41c0503c015035900e240c096805a009141205090a01c1d070700401d503e01a41c040350170201c080b1000281064245c902224 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 916963974 1250 916962724 916962757
    0x213061a04060e0f451006031a040e01023f100b0c07210b0c0a09030210030f180308070f0905060a0e030a0b0f060102150a05130206 58
    0x420b03550410a40e0307544039821580030280e0003813040011104110101c800a004000781c8900c845210a170200910b9a00e0350b138050407040b6813100d55020030079030446000814005504000a02034002d115800382070701c801e000e890080c0c0c4944280800341c00f242448048542d030800010000c0c84505400c0b410340045030117400e90290108980072034681d002d5104414600c2d040c414170005520304030002c0115007440c004640c48031801d60200d8240b00c00b5510420842c11850f841800040041503182034092107036071802c43c26280c0d280504003d01880c00c1c00c2000c198400e5044c000b6141c20920780c2c00341c01140c54041413103e17501620380d003540d2403100002c03841002d00c810304c01010f8008202c1c0b64010680e140846c1c0c01101414024a0348006214440c0211000100d00b07400921591000000c1e207006421517205a400c0d19005298110450341480d121441d000856500d61002c5200c0032204804c60b8103191703e032117484503040100005007110384c24150702882200180c0f503000150071107003107034003950 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 916965224 1250 916963974 916963979
    0x40f020306060f0d0b130c0f0806070c030c031d03100e0123010b070c030602040e1510052a010c0f120504170a0908010e010605040f0504020d0213061a04 67
    0x589008000707010507103d5000ea0006145988405808020036034000d18502810b0301c601c030740311820030100407002d000c4480d030107400300d0741c010045003400c00c8864090440300143d444603001c9807914a00303440100084ca1030140240800d200c1e4164901c0c42414604510ba98036800b00024034128403082d502842d40e03103814245481100a1240d840703410700d90300c000e612200150065080d102ea05010b4100c0700b20b400301d441024420201d005070003130355100b02d04568a68a400c030042803840c0403030310303000c0100d25075071041043e0801d03040712032480036a525854149460030026022544914424001130038009018140d241424007500e1258011034030760701030014080034010000b0f080d01c1e0440e00340e181020300348070000f80c0300140003a140300101021505c551240104440380809548258415801d08101c840030301e806501490407a84215010072902540c00002020340c0c00498010b0f5004144498540240c10040d9203000c1c400c64000000501c51f848102104070440242c19200c500c40011405 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 916966474 1250 916965224 916965229
    0xd05151207030611032211040603031d04290616230102123606391c06060309060b030102120601182c0f01060c0609020612040f02 57
    0x14040c1d030b001d0b1340d079000d8518603250640b9541d9101d0490003000a444018141080c460307009000e8078180c40c000d000713100c400d40d00d0400401400806c140f08003c280310000503011171506204030918219141005158012030444200c4011a1030028640103031040080c42d105203408001c01c00321505c05e0b141c111404070900f0000c500100103002104191784104000710000ca0381000869010100c800d0401c982003580100c5401c4448540c200c10190003400180e0740803050200d05580b044c00040040305841c1d40002d081030508a040f0420250100b4032000ca041c8101101c00501070039800c41c404558440c2c4201d4181c0455105903c0f090009584822200400031540201502290120007c3d410300000f50086140c1d01d20280c0094140a00c81c0c0e549030348080081440b41c01403140b0349002c07207600d000c0011404000c25192080307003c03125810000702c0c01000180340c603050b501250360300b1409140170b40d64180144054601aa88002c081c007044200000305041a841184940a40400384415105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 916967724 1250 916966474 916966481
    0x50a0605030d090302040b04060503010c020f0f0304050918031902010605131e0504150c0c060e0f030703110319020f0106050103021c02030402180c0703090f03080d051512070306 78
    0x814820381206920402c580d0b44000244103a03074045900040c01c2000d04000740040a0a5000e01d406500b000c12a00b0300310307000700c1c2c0d2000450b044020b0f40c03a5802c8200040c0d8030391145014181e071021101c030106000c05200304540080e81120f00860f0710f880300a8020b003801802c1c00c0800030050b0b44401081c05036044c500a10500700c0c01b2a01c0c24407044c410706070618404905180d2180740d00340d03500006014880c100d0b0090450f004080c80400a140039003200804450b030508050301d15500b40795001c01c40c030f00006a0800720705900405907003040c04a6900319500810714000b840e8511042c8008542000c4206010b000c4000540050401020170301045003555030640c07040d41418418406000786000310110000c4418032502c005980f5030760391000800900400503c3e480070742084040008880307101000380744031802600c580001a541e044c1180d0103e1040c040280411000e00110310f00b42c2c5d194014a801083c0d000304c90a0017060440401c0d508000c04913500d400b0390000c0001c00a1065510 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 916968974 1250 916967724 916967729
    0x30b090c041b050d1e090b01050a051f0908060705040e090111041403010e01020403060b090109090f02041a030a0b0a0606030603050c22050c04050a0602150a0b22050a06 74
    0x540910128405036044907080220346005410f00c800061303002084166035100e000c0300800c00c601155541e40c1386464000a0290741000c5a44888120001c5002d1900351042000c40e20004d29030a403030b4110a0030a82c140315081c544d1001c1c800c040703401040c0c00d00140071180c814082640e4141d182d51802415280b0028050084244c42c0d14041c151100364800e1000c03501a1405a120402500c0000002c41e0040500231001503442d440450040100107a5420503400d44c8030440d40501e841c0d8a9078040c608884038003400412150f00d82e82c6003001810a6007201e0403180b0450004081c03094070070b010904001d600340b4219001500b040030041540381034410300c0d010708001d01e4104125415a40c4959503003402c0d07400184941e829a800711070307032001c000c2d601c582185020028000d0b81043e1503007000d20307082409034900c55022544045401d610001c2c0d04582543c042014003d40c4c1c59418003400241a10552290401034285035000c0060254452074000100e03810001441d1401004503403c441e0303180c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 916970224 1250 916968974 916968979
    0x307060b130e0d081e0a05010302012d0804020d0204020307111c080f10050307030501020403020a05180a090c050d030903051b09040b0a090f1101090b0f0d0222030b090c 74
    0x4800355914080001c0c3e02010115a4244a6015112490344e01452030820003480c104d0807818040045102c50303500080d04903403007a01d40d040321501710b090114149104000c2426070b021885c035042030300380c80741e181d10740c009001a0140000700d0b22074020406030383c0202d4500c40481d025180b40d01b42c00301c01300415011510f105c1c0586034203c6c14848020808140a0006c4083e01105070219601c101c11080960045c04014202e455040d0b030791605a000c3d412030f11090380310f0b4200e03031030019960504c84401d0008a0040f0300c4c40c202075884030b21100090480f2502961007200301d01010906455084a9014150103502d0303003019546945030240c40c03c401103040c58511045900c03034981036129070140503000b03a80030a0050051703588003e048003d0801c909c000d011940c4800c40c901c2400840443c18002010aa0350003000d03e072034814019240c0300c0c0100c83c0070340e20340400c61541c00e003da81d4041c0c03000e1800321903041c80c090308420044a903110140c006a0740140702c2c005210000800300100c0d103400364107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 916971474 1250 916970224 916970231
    0x10e03011a06090307050a031b230d1103010507030603060b0604030f03110c030d031b08220501021b010c1106190c1b050105090c03210a050403050307060b13 69
    0x416401d414000041c0300c03801400049a60308031660280402005031202400c40c8030846e503281080b1a03d800d0b55000c0d19103140b1f81030307404242c0414040050030051102000111000d42d10014411f4240c1c14038800d80d0013101c10328402c0001e58080c082c42d0300400e01585d01145240c2982411011901840144d6100302420441007000401040f43e50f08043d81605250301c2c854030401c5880d04006070901d256505010744a506504260503902210f04a03440310000c1c00180380070141a28000000c1c0c175000440a1079680311844a405c031035961950f1480354002506100d00c481ca078469030721410440b074006945030400054100d030b00a4515402e0310140c0300900181c00c080c44511207242a4215030200c1030344841d0440c3d0a50b00170f8014414801890684050441003810282d008210a441c204402c0c011240003600c0ca1074002002c80403140c41c4c2682003640c100c161400b22450744800e01e144240b10341440000040b940a1000c3d000003070250743c0c0412109a10010400c03802071061107810350318038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 916972724 1250 916971474 916971491
    0xe030702030601031704170a151806020c191a070f09030b060103180302010f060812040e1302060c06040b060d11090a270c0603021c2c0a02010e0301 65
    0x3000150281140e03044600b03941104000f0b641703045d21340b080c1d40100207641c4401c41341082c0300c00001070721071489000303080c02e485180d840c5000c0f0f001e841c0841c1c161403202240420000c00318401c0c0c0c3c018170030b0a440e201101d4078910040100000c88142c91700580704c600101e80c5c4025102c80c0031004540c080301e1481c1105403045030000140040c0c800f030101601181c0498001030243e406a88200703d2829080b4110502d00c0c4a450024080c10701c104241284906040c00010f0481e80080d0050403407042c4008079040a007441122003c0e402c0c010460406076840c102ca640c0580c58200061001c0809440a4542403030241046000d103540a07103068000d0350464030031030103c9c180002802482da0704032800300d010740740d005002d40a0604209516400d0b28183c1603031208080d508010060548990010001385079500010740c1203009900400e188039059284150714003c0d00d51151544508101d000c2b01201c0c4400f820500c094880f45014040d61311000501043d0340c0c01940c0020003100c214000e02c03000700c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 916973974 1250 916972724 916972729
    0x81b120309030303010317070c0e090f030906090f04180b040c05060a0903120c081605070504050c0327070b09031e030d0b0d17091005040503070509191a040e030702 72
    0x100506c800340c507020048010303070300c050014421515482d4022140c1520641c8135040700e20911700a5440394050700c00c00c081c42241c61004803e1385c10003040100b4a034100512101402408050f54104950060b6a070b0b418203031030302c41a01c0881105000381d08154039454070b4030304640310081c2c40c0c101600c6107005000c01d012850b03202659070207880d8031480c10000e41c04100400d5540c5c3d40780020003880920701195020714445034007040e5218900400494003039550f07840038841140c00654003614040000c00005032000c1400c2019418085924091540080c464100d1424040d050700490304503500003c40d40c00710b1030104102c6614018040600a426031317880c2e41d65640b44900301c40d101c1c0135911008a440290f40f0003c4448829801c1500c1c0d15810461005020855004d48a2a4071070307110344c24511101c40c807034070980d010782c1c2002e07006000c7e050822003003040000c0e004042034409410305001440001a5000743d0002050400d00c500004002800300b10548240c10303599101e540c0300380f141d180560f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 916975224 1250 916973974 916973977
    0x7090501081009030e0a15090506030c07120521041709131508070803041509033f030c1209110d0201020106082e050705070b0a06081b1203090303 64
    0x101c182c100190f610140e2409481303080c0035030b01199020300c2210000460b6107040325015680401940c075880d500752140108152404291000d8441003014014000000d10111104282c1c3c1c007103081080c200840c1102c00c0821b551201181840031705104240020088080004056000103814003400e01c558000850301c20300801c0013041a081c0c460b0000003803044500c1c0041c01604002c03098a00070303522054400d65a074403921403411902d030401c8160910302e20520031041a00c0e0b100d031028032840329945010501803281003000458100c03c0690f0b00d60b41c0a110680004844191004900c5801d080e901404640d68016003400e444d007410782e00c80000d041d064280000c0501100d06030341c0c0d00410700041b801400e03560860007191281c40d4501c0035280c014004e12013101e030f442d2460007410824080c0001942c80948020011035800e00c11240003603420304c08a90300003245ca038009106683e800c282c5103090801081c1240b014584000342c1c40d1820a40c40c4440e00f52030030701c015490043c414000c2980d9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 916976474 1250 916975224 916975243
    0x615150901021009260414010c021e040623090f15011d0603010803180f0603010b16120f0206153d0e010e04140a02130905010b0c0709050108 62
    0x1513910306298040041c0d040c905a11141041da5082c0d80524100100c00c1a501c98001d204540d040940341c191258400e840d0908510f9015007148890700814502d040211a41180c0d95403040d120240801e02100f041a04a40c4075182040c03281034100881c107003c042c5c0d80141480c0304c1712400c081001103c0c4000e000b501401c0c0700a10308003281d9102d0410703038040c1200012075143c1c0300c1000070000030008800809003046842c034109110810000030b0070404810890140d841d041070050004100041000c0301801d00801c0b00602c01c4074040956483c01014810b81d0000b40100d00e01000d0f400c00c00303604000d03196002171016000220707095440c002035082d219018402e10768540c081c1c07586410401c0b413035a44c03040030800c500c0c0c203021020110000d041c1864519095000880d003555101d800d15142c005d8074600712904c0010b038080e4440024880c0a03602c01243c21203284004800028060000e00c0707402c1c02030070040040c58842d800d1052080c05e00d0714584c0840e203400d04090041c400c0b03400120341e0104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 916977724 1250 916976474 916976503
    0x1201110f041e0f150c0f030206010512030a1202030a0e100510092702130c021c170105040e0f0714040e03070b060d1416060906020102040f14060903061515090102 71
    0x310282c505070851701c4c50140c41008100b000749440480c2059000610380781a51001c132100009244094260303603603801a491004005500104521500c181e41d17402182c210100c0280401c10200b02002c02d840c08140780f85e13520442d40d45500300b01e06000c6820039600582030080090001042c0c091910b001050104407652003e100a03208004561b1506421500c1140f040c00c2442034400110b8003a46407021010f6055200f29200040c0c01c84500c600d00e40080c00c4c0c40082c0714141070b401c0c201408020301d0811420801c601c41e4690021541d242000110014008040210f56031000b0009200035a20ba03445808003d9200703000407400100b440360300075400322054a000341c1420f15814100e09807014207011170031900501c61030030b86003e008240c010035100c0036140c0214803903503682c040b400c0b803080d8410440409217240050007070480c1c40300882503c0100804c150700700620721000904028041d42c08030000300305140c4102041c1020b030503048880098a10b40390a00348481d0000c1c0d00c404c03940100c0030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 916978974 1250 916977724 916977749
    0x12030a1e0c24020702090903030a0b010e030d0c15020f030108010e0f0303190623010305091924023601351905060306151201110f041e0f 60
    0x24101c00301c0c1e040c0c80d134040d0020b1603420181084201540c030703540140c9140701d0700ca00304142d410342035014498100c058040500100051030394568121050b0310031180842e603a44021000c881400303503e0000c2c2c442481c40d031503030039a254546000341d42103411300e0500e041c090300309401d05100c5000c04030580c0d034840c01c1e00300d8403010007542d1103030100240003c1e040609500880100000641186481c0c0350341d40f8003c0c1c0342008241c803020040c40d5200b0740c074480000c90259030401c2c0800507038241c507008481c680410800c124440e8641080060342c00200f0103690403c04005000d6912650400d11a01040c107144694800b01d40200001c00b40d021003043c2a8940301e0010003019088240019070328118001052000182000c00c00c0091740f80741c40241c160341904210100d002c6280c080b8503035000300080003000c42c1e0007483c101446041c1401000e921029582e07500614245110f2a005101502c18041d1940c6d1f01c509200d49503601d11842c200b886488041c12000703200c0c1498006081041c0c0b9041e14000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 916980224 1250 916978974 916979033
    0x646050318010606030501090c030e030301170a1401141003030f0521010801021803060c03060108040206071202031309020c0c011116091d240612030a1e0c 68
    0x5a06000003000c4481082d8030389080000c0c501d42c1640968142c07800c2c11018003510403440e03000c0f4251072140c60710719140d40081004203c100700c02d0344024041c3c500f002c03da89151b2240e07261503580090b0a005103e840e51076044800d201e400c921750340f9500c1102c82c00d094040d5815518000c0003161440c1c01a820301500013001c0401000c1c0380c803541c00c0c0100e0351041880668641001078080d401006081c040700da40120f2003521442d01054580c400e00d1210641401e6640f581c004440d00c44005d8410b9070880004c00c03000021070340122038140210350301d800455942e8500001020717448805c3d4040c21000748180000b0300c4000d008110081502c8003481c251031101c11001300c26041c061050010811b0803800d56001032040070035040b426200c5904c0440c0ca04180761301030320544940d125070581c03010304440c02c400c4a100c0d02c454811500076074040c1480405101031038080e40703586d2240d00980042080440000001c80c034403c14500052404d2400015000150380c680b05e4503001c11201c2c0d0301088501085 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 916981474 1250 916980224 916980241
    0x90f0f0616031a060c1c0905012a0803070207060813050604110105040f06030501170a03021f0209040203010e0a05010519060c050c0423060d020d0f030e06460503 71
    0x1080c2006000740304c00c0d80c92140d80d074180d40d2191490f840d18400b051001410301040e0280c00d0107011100c044e11902034420555451403103845000f081360015983c1d054802010075443c01c0074512035a45500104000c3e424204050a180703401803001c0902d00c203190301900020400b040c81600240d0049600705000c14410060f9402d00450300645001d8500c1c400000d41d056040e041079040f80d0710710b00401019611184010b03110400e04102a015a0105401a0049000495841064000040060070032000c040020140c4e0b20a0340045400402c3d02c06000d00050184125401403000712342d51400c420450840805031851445010180407003402c2c84810b101040c0002540c560008100b00400c40046405955030310400030003119002030400040c1c0d880c100420201d40c1d0b01d400510f0071100500c03d546e9058004e9844108070100185c8080c07000f6140c481e08041d06086aa100e11089103c22142aa03411100e19025016540603984000000140c04c034841e5200b1a6061401d550340e6624150b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 916982724 1250 916981474 916981511
    0x604060516120c110a2d0504050103031215030506010b0d0905070e0f0c03190e0a0203072301050403081b0f030a08040b06010c0309090b010e09090f0f061603 69
    0x28042d1040d400c109004440303036405120b007402c1d140300d404d42c092040c1580040c030030300b00d4050040100c184c606034084540d001d0761080f061200e05003029004c69041d00ca0001c44c05480c02a07200b140400c2c03900b48485120141c60103949441e410000c03c80b0865032554582da640e985041c0720303000d2031a00003d035061451000d80c0000072031030b4100c0c0848200035074441c0d940842150458000e0100350601010500132070740d400480b0f01542050720300c0681b903c1a0303a2902c1c01003030000e101d010284500d241c058010b03241840702100070900380d010308850301000c3d03483d0396400d000480650f042050401007400010071a000f82c6502c00c109901031901381400c40305003403030201100303840300746844041014465643d000080f14411840391038007070070589070580150b40d00180348000501013019840203000c000000d03400000e4410051400c1d42601d00002c0c04105150f81c2642c0c17220107504494010280d0b5001001003010445c00c00c00104420f00c0c10064018401c1d03c203100d04d0f020542c03102c4040305420095607 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 916983974 1250 916982724 916982767
    0xe0d090b090a21021915050a0c05011d0c04090c2904090209010207090b030a030819091419020108040b13120c021801060c060e030729010f0506040605 66
    0x80500c210310300780d01c0044030070864164120311071004015030b005c000403a10801000c5034000684941e0300c6a0b40030068807190013600303044040144508004000c1042406000d00ba96103003900c5c0e8201c0700801c00383c1810070214003c450300076424100e00c18005040c84042508031404040c1d001c0c0c00d40e04042441988881d0a2440342c0f108502041c00305944043e40d0050071a03040903000c40f1102c2d41d980c600d01c0185c4440c140b4443e41354001540d040d0201e40250301c0c850380254009900080b0090070480c0c0d504440c0417200613188900f903040e103844000010410880c07485410b064400d00b5080382d030f0000701b080d04002c200410100c0d002000ca40f6040c0c0c44503c50392003907400581900d80802a0200800ca442c5000f800e038440e145100d1001d0101c41c50548032811395807681d0f82d83c054120952a0207010701450400c51142d0711080040c200800d105200f9051442d82002d0440345e812080a4400020501030300301c0c90554805220800c4161789027000c680440700e07141005c9445912540001300440c1909 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 916985224 1250 916983974 916983989
    0x10f091214010227040605060306040b0103061e050310060509071b021c02031e030f1b10140f010807150201140a0507020d020606090103170c010c0207090e0d090b090a 73
    0x2203901c051610b000c4100100b02c0d000c08004c1c8080714000001c100c182c6a15205040e0040c40c1080801d15900b001c0e08131903084503040c10045aa560384940c61450a04107000072903440380c2c8110240480e24040c028250140d40540701405224101070002e6000c480c003402c8441407008108030520307901c0401001406142d0010040203007070000308068051641c203080101d100f0b0181c0d0860b000141450b40e50203800d0300702c00307005509005030040013100076070015010b424003134020800410921401c01109082002004020030014201e07403c4108170769000d0701582891000c000148011503001401808840107407007151042031079103206a0060000980c100ca80c101654104034200c880ca41090f0b014005a03401c64161f90a032010498841100b03031a4158401c07001c2d001040420701283c0440b50319580098807500d072042241115003111800f03010040940c102081c00c10440283c0d01c944280b0b9410702c0090941b400e91914028000c29086c0610110030102158040190300e61945190190041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 916986474 1250 916985224 916985227
    0x1e230102120c010605040621150e100212090f0c1509040c0207080c011d0d03020f0303100e130201050304060e070506070807110114030408070501141e06010f0912140102 74
    0x441c82c1c039901a200501986010710f0402000064600100720312016181d40d0000d920641c1c0801c2e95642e0135002c0015003015003503103a01e01e890a05100b0302140d0030400c081d007030040e55a0170034560b41c0d88a40004000c1801078000030315102c4604400300d034585484104940060b413554221080f669540240440207420901e04040690031a8000800005540d0900201c8403c0030303109004441d00c1d001c1484845244140070038030402800d02811800c0801e2190040d0740c880d0400020301031660308206c0300d038449c0104000c010041444100070350354104050700d151902c84686600040c001b840701802c002c10441d0b0314001c901d04010144007200160100611095460046050124035600820020740c0d80c81110003203d40c3ca507010b0462103002c1d1617004000f6003075503078640740d40d03090350403081c416111035482d04103200d40120b04800f8284a42140d14034142c503902c2900520050b0034004007414140705005602e5500c9030b4108904108540803803821b07818500c0c007440e02030258001d116401c031141d0700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 916987724 1250 916986474 916986487
    0x1020d140c1312081201080d1716030b0f060a08041101090b09191e0e0a06060c1e0f12110a05250b0301030308060907021203070c26041e23010212 64
    0x3c0403907200540c2321542c0d5580d8206104000484420b00d098402440700d20740c090300e402100d07000750032601d07900348010405c0543c50302c01404140030390310100380000080c12407420041004481a50024030350400e1910f49c1469040030b4038691640314089405e845619803402e055401c40724000000050b2410340c6441a0224481d03c1d1040c45410a0141d032169909a00004118019a11408080310260381e10080744103129103408a003281c01600042c1fa080000076040e000ca02c038042484600743c400d0910481c41d030f581400c01402050f50586030116500000707500c10200c0c00c001000802492488148208401080030740d0340d0210940e408020403400c0072000000341a00411400e205800c07d6501c2c0a42c1c0d40da00d10b00300c0c0c96007a40c2203035500c1c2103820300210345a240308418040754244a00345800115178190002d4036510403038609503140f4180010103010713200c03078203141c900c1ea56910a098003249080c222420311114000f1000840c981520b84881d003aa031082250b601c1c10400c40700740595502 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 916988974 1250 916987724 916987739
    0x604091d1c0314101a190921020d08211009051e0705090f0d120e18010b07020f130903081015030509070801020d140c1312081201 57
    0x2007040d031910010030700d00b0410080b0140400c55441c840c2000030807811a140c00c101c4d084500c1088100f141d10340d85018031900e01c502c400500325058406054a82c003402524064082d441d12103a10601c001800d05281c000006842e01d015030740c4c5140c0e0204215031120711031212038907200c40320582412051080e1040c4040e5140c0a5011810344071100003d02550b82d5040b00c07144805d072004035032442154094001481948036101420020750022710000030300b07000f0b400007a0725005502007640c0220300e40c03602031101c940003001c0440c4030b1300036241c510036140c43c150b0784880540c052040081e06000020071108547d1160744014110070010001000e1204014400c4001c007500c00c000c40110b9090b1b03000c9040280c4d0401040c0496130401c111502409581c18118007502018084059500c00c1000124900000703001800c1c02d00a5000c00045a005c1d002c0030b0580c80308040d011100108042002d911042c3d00211014292006103a802d0400211494200000d102c2c54220f1066586003900100e5501e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 916990224 1250 916988974 916989013
    0x170a02010e040b2d0109231c051005090c03030912070306020417060702031216171603060902040e060118030209070c060b0117070f02030409020f030412020a020604091d 74
    0xf065613040b20303054607455401515800b003e40507846641c13940c10005031245030b003104070721300c1d5000242042c807001c0c0481919441281e40b50400310343c80e40008594807050449842480d0341726801c0300c001e09802e40300c0808251a0322412042c6406588088080a015101005004000d40d40213204554499540115580c04d035540f400a00720f0780a0000460740c0d09100000741d43c01d24050481e4140030340c407602240e011440020003104e0074840c4010030343e1092140c5043c990300c10808124248500c0e807600302c0040031501d036500305058070340c41800123000b0500c200a1f800c0d4070280030f007015818014035511038507000105a10017540034440104102590703034009a1009014402e110602080d00c2c1a801500c0d100303002500c100c80790410b600052103040c814103900c0d6560845005980c5803a444100711000d0f0382c40040e0702c402150703000090004008031651003500e41c810b40d2001d0804204241c0c000f88051007244600310941c0c0d165000c04010690320131040100e2042e20044680c15448501080d941 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 916991474 1250 916990224 916990279
    0x13080706021c0f120f090204091203060816270c02010209040506010318120e1804031103040305030d15090507030b0108010f0302150f16110307170a02010e040b 70
    0x40490300820481c1040c021850306800621036166964009000c0b02010005d028004510810030748440041001d80c0b168420b403d48240540980380204044100c00380544246a00030016a8011845c0303401d400f588030002c0c1c2c240c0300c5080c0c1c004c840324116400f1b051a100c400780d071141c03010301e00000c03120780e2030701540242510201a01c0c1401030350344040054080711080503070115440028090301000030320f01d404500800a140c245182164124801f00f46040c601e920001c0750000c0100501051540103602a0044c80c01d540c0150f240c282159211030b107a0207081e40e01ca2a003a2a40126441c6066612014024007080c0d0410481c500e0300c0d00004001d82101305106020941100002c1342651031000c10034180c80d0081d19030100d08c0c259841c2203625038002008a1500d403824130450440d030203002e1840003d2070040e00c018400c1c2d42c4281c00c1509211859115401d158a0281c0004080d07a011800800d41502401c000080442070f00c00305020b048c5e044a00b0340c3c800007030407a60301103109000c1c81c84d08 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 916992724 1250 916991474 916991503
    0x11060310032607032102131a030402010504060f02030409020c010b090601020c030a1b08010e0d1409011704060e100905071415070c03060c0503040b07091503021308070602 75
    0x3031074507100c0b0300c041070341600300314042c4400c100070715804240110050007151003c031a99880d001444070b0442c00320b800c142c89403200c82e00b90540800c0314040a0440d10340e0600c01c100d040e0300d141803950020300306100701d1140344244000d410700c20380318500034004e8500501e0b549909559078508036100c0340c000c0c264600840d110f060310302c0100b1b60380d52000541d0b600c110406030041201880a84801100022076024500c0181c0d0500c00841c118600703029000c03900c08584010010006140d0000d055007c20146002c0200c0c011700481c0030b5682e210304080c840c500036100544242d26141012805400b1100c0010018441d0a8038240d8600940d4004100300740100d054560030b540301e42e50b8880049082c580780d68000c00c0da200c0c00490b0b6107000000c000141c419049046a581e40741c0d1882c058405481c00d0301c000c988013000300401d20546586465115200b0301d0400740081c20007503158220713900030901200701603001c242109444004104c1ca4040c2044e0000c548210781e458000940e50200c0424020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 916993974 1250 916992724 916992743
    0x50105011b05031b0309040c02061014030c0609060903060f0105032104062604060c090e0603251a0a0f020f060a0c03020d0222050612040f1106031003 66
    0x694040d148503a401c14030381c0700c2e02461502c06811402c07032400035400700001240c001005441840d50f9507108420340b0001a4000d80294070300681c540c288180e99034001207090500c1b984102c5103076004100c1ea045076204407a42500d400390b250104c0e54501851400079014407445082c8140503c030160124102c42080301190200502506100390ba100e10020300d24031402c0510090221a0159001248400c01e048885c04d00b00741052031240c003c07000b07071016036281d50b503904100380d0154403101c018081c1ca2845c40d0507000b81000b801195540e014643c0352440d204620712099204131484980100500d0a1484082108a10b4000c15150391045490038049400200240700309800030400700032011468000c1c02160b13a8140041c4080c21184050764209a0300700a241c00248491002d000c6140e403aa542c0020052a074405c9d004906803904102e00c25802070040380b11078505110000e5002e980411080c4400c6114036080000e00c03c00720090b60b002201004000360302c02c115003664200d0303000301a5007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 916995224 1250 916993974 916993997
    0x160609020f0d02010203070b04021c080a0e0f010e090a0b03070e06120703020a03260a0f02070603180f0503250605130b040b190c030e01050615041a0c0d0305010501 72
    0x2c420310540b210001c3c00340e0400c1c81030f2000b0601c881c00e07095016002804c0000f00d103003080c1b0803582d01448018200c407249004104000d1480d44064107605241040c0c1e00148450803210000e8a01d82c0020780740b600c01d2900c400029543c0446411200ca5a0005000c60751741e19103032644203200700802c4079a64010b2008000003000c4107030009440044907001b43c00d560101e0b082d9100c1144004603c8400841c052101340d051181414a80c001c000203450364bc0c90303500240c51110004e040034029070100b4105420150441d401071144061740c100240d100f4045024130440d481d140c0e0031805410aa45106801d099641c140f1080780c2d0241c000c440e101c1e07001080140e031940300700074030b00c032180202a103007000900001d0001075021010702d400900d107804c01c1049802043d03060742501c1c0e094a105000948075050485001c400340030781d42d04054201c509095604c61010f049805029a204201a0b0f102d01c11800c214903034400126a4001c3e1440141c40b507144201030041c1c003401080c465280001c1d0043c140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 916996474 1250 916995224 916995229
    0x2f040203250e0306100510180b0a180b0a0917061b0c120c010c0207051c03090e01060519051e0307020c1903033908160609020f 56
    0x31a48a208881c40001c416102590100c0030411006400001c0c00041004114680d804100f040d104074641d1440320032071403c003420300480d84c509402c1841400680c90341d03901004400e1b03c8810654403c8030103036031502c81c103420440e071440d00d50505c04260305403c40003140b0080100c2c0200340b02030a540355441290794840c5c0e440071030b000c0a0401da410303410007004154200042184480a500003405407030400c071000c08481d0414207a842d8140340300000003401241180300b0300401f2640340d102d00142c0207880c64000410040c03059005600b003192a6105518109402445203001a140c0ca110515580d038441c070f000b90280e0701c440c2c0b95003410b404030083c00c0801441101120f032642c03944000380f03100c3c0e902c4028000e041d400c00707000c52040d802a01002c1d105903d0707210b130b08229102101d0440f541030f0301e1030602170030110010510404c03e030003082d200150303101240300000d04040040042c0a80d108036081109041c05002c40a0007110782c900c1041080c0290fa4000840290007103c1682041ca0350808 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 916997724 1250 916996474 916996477
    0xb011703070309031104090501020d061502070e0609060d080a0509032107020904020616051f090506011e0510030e0c0910091107050a03051908010501050d020a0c2f0402 74
    0x1401070000300d40110031320000720b000d005a8a04000030b131010544a0090703542178203a030003d1500d50800c074ad0304e02c000c00480b41d943e64900120318150000c3c0806508008030a1405000141858026a03200f804107036141c45084410340310030303000440b00e03484d15030900c8018125840700c03403414402d01c42c0301c0c00d07244d888803038005030b601c1d82c48001c03581460030059900380000310703a000780103aa00200501490351107507842d0605201c500d1150b0041c0078041004e8040f6503d0520441c500da03040c0c0d02c0e00003a10700083c00000c485054601c8060a2400000240c0608400841681000c0d801102428080b141c150305038010740600c071400d50540b080c046408050043d0b55408589111201006840401c45c443c00d640c809400c43c42d020074068079018668030f601c0d02d03011012008a00181e030008071144020100304041054082c103281442003549485c00081c0a030203540c0a0840003940000c80c56401d84c020240c00b00400e0f80b155032907201e840c40450b00004103141c00c1c10303c0645001c0c0d09046125140520 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 916998974 1250 916997724 916997737
    0x1061e0311040e0a140a020403021206060604061101150f080607081b0f090d0c03021c0b070e0102010e0a0510061a0a03270c03020f01080720030d06030b011703 70
    0x4581a052a14041c0388542c0c00d1400b074004c1541540d540c0750402d488144001c0c8078070a005030000966543c0c65071041c803400d40c6000128120540040701444010b0307960700d046030116142803824070340042100d480c550051040003516181a80d4032540082c080710b01c18180d0040320b0011040d41c5042c0c1e200f50b002c0d68034440884a17220303484807101d4041070b0840d400025101040c2142c00d03850411079148041b8541382648071003038400800c894020421841d200e14801c40302c07c1460311642005819983d034104140d405002c007018030603040d00200c004d9100350311485e4101111400c80d2540c01c506c2c02c160341c5442007110400d146509108002c140e1407000b1806000030404000081d282020980d0210024001c80200c504400130f40380c20700031448160100001d81901815045003030310f14510421005104071100c05040c0b064540c2000801500500f8140e683c2c001c11200a03052101019010300354451340c1c44e0340104600c1d001021040c001d00e604042d05a0700840d122041d40d0b140c42c00c1a982d80c0c010791 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 917000224 1250 916998974 916999001
    0xb01020c01080711010e0a061d0d0e04020d18030e3705090115080f01030819050d0207031706031c11031603050c010605090c120c0f0301061e03 63
    0x80c0000d03544568030482c0e200000c0d240c5402403103109040740b07094600c2c0c41e0340d034803855002150080600603076200b0017001c0c850705d00b0002d40d8205e020007050b0300ca00002c1c0e00401800f4400503040d505881d6501184c030030126140040012031220050400480c0c1c40c480141d00141c40307546405500d080c0140700e400007034118401c0c460403848000c80c0d060b202040c8001202d03082102d1100060139201d046055000e0540041a0100200c81b18001413100d2001840d03203032048500001003021031690004c5496104040b54200300c0c502e10210282ca5501ca40c1c034000402501c002020300034181e01c000214140d81c602d44400100d42c850a007017643c1e4500c001700c442c149801100807800302038081c02c0e074850420040740540e41000030001c000e03010706607040029000700f2000203149023600380c20b1180101600301121400740d58105004c1007205805044210084501c030758000c2491840180c0594010840304100a50340c7e68442c030340103219440c0303030544000e00c240c01d408034507000d4028040c4102c40000c2c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 917001474 1250 917000224 917000233
    0x901020a060b0f040504140d050a0509043317070503120a020a0f150506010804030e0402070c05040203150922030c020d0f06021b07050310330501030b03010b0102 71
    0x2911998000c089140c0b085600149110055840f80c466001d014815402103120a0600b0081c00c001c0e0300700b410b5000814201300c4104640002941c210058035480c40c82a00c0004440c001e0044145103800c3c1c980d0100075510031441850076418841d100141910f010405030552903d03212411a641c03026030040540c141c0211110090700301002e00036007036000e020b1045410154041c6c0740e2031280c05280e10269015100c00003e600307404503500405420003400e1070100d031680760036200180b0760070440c1e40351840381d42c0008e8100107114000e600e003005400020701c1190b0b42c0c285212010400104e00d2485170103140c4080003c2d81c00c00c900e41014000300b5804100c040c0d203c000381e07000c17640bc1d00070302c50483e40800e41d00c500300c0200f10381102140303000c1d225400040c1d945203198524135104072401c0500b10540d0051106100715240818010b2440701071260110785c1c1d031035205007000480850032081c100030071781c00c400750f01104042e003084040351020b0300d00b005480b180201307040c203803070000610714050b80c0b2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 917002724 1250 917001474 917001493
    0xb0c0d0f020309060f06220504032604031d1c0201090510050f07240608010506030f120f1b100b06030c09090406020f04030308090c010203070c210233090102 69
    0x40c9503480c3d46d8000c1005003049550901d602e55003403090280019504020b542d442040105a0001010a004100804441c01c2d0708204403680160020042c07000342001450420b04226242c0c8410780c2903000402800300c0c2000703c07420719082c1c038124032500c1030b070000d080301c5000542d40c1880c0c03001090900b0103584441c0362001c16003000740c4032b60004100301e0703408003941e041c0205075140c504003000311403040101145061410f84442e003580e81c051f202a201c2e8014000c03480ca07500c40000c11a20104c2100b4245888a28844030b0500074010314100b50900103841c0340c01144240013046c0e003a03202c110340008000b41c19419042c08400c4c00121007401c12071008000b910001e01c0d0480e861540a80301e5400940381c00b0082c0e100300c0841d001640101c0102e01c0c02000d00c00004010701684ca04410284011418807c3c0c60f22500e400c0300b50303882502c4000419554903240407a00b00c081c02c0c2c102d40c01500641640310440d0300c0b80c02307444c40b1700c00d0341c180550a881c0706014407805008a50081005034000c04400c070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 917003974 1250 917002724 917002741
    0xc0e0c0f090112020d0e07150e09040c03050d020d120504020d020402030901110409060311030c0307120c091d010c020a0c151110061a250602070b0c0d0f02030906 71
    0x140014001410f2001001a00d9040510390001300382d081d82e20700022901c19960703080203150581d640c01c001481c11030417086000e002d503c5079140f180b40c90308480a000c552110308110700b4680c01e41e000600300d806000030044c842a0001500c880140311550341c04010300c1c01c4c110300703411100180d40080d441113128071190094030b0a60080c2d600004440000541e100b545c01178800c00d079005070b124000305500e0350f8040050081c0340d490500c49113800c0d000703000d20b01c038a0070009450303401074094441c0501c03030884020140125415a64054807000100f0800c44100d0700b84030500c4400d0b201254401d41c200751203014101c2c0b020500001942e170180c0142040360804d80b07409102c0d43d80000e80d408000c0f4021800030520010414a0036264403c0d42c0014500e05000c050010326000812008800104116046040001c204034150175040158035103d240405e18103503000c0c4c800c40101405a622403414001610f02c0e0200a240e48030308040d0400015124a10002c240d000440d610000c7e504041300041500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 917005224 1250 917003974 917003977
    0x11030306090717010314010c0c020904020d240203060f03031309020a03090f0b06180c040e2d010806010f0305210405030d02010203010501030612020303070210110706020a0c0e0c0f 79
    0xe50301c1c104401881d51400c100802040c00b45d0050380e0304e22580300e19140030f6200303204a0355082210700d000c000580054011820000d00600003d0003080e0042151081c4603501c41d074140911002810350490f200e0065400740a904203407495840b0704000000740e071107840c001084515050f1001858038240e403800c10440020b401403425181895222003940001407c0203407110340c1644a84404d680c0740c1812814030090b0703d040d034140c00c005445041405626000c190654044420782c5024800a54034002c0003207016200070700c5a440b400d40c011f0b80c0380c402042088158181c40042c1300302c0b40603070b98031510403101150700d00c00900b25030007140c4d25a25400400e05010640e0030300440c038a28250307030ba5012a1810080d00100c500603580800144003944e03140c0035400080a10004c4405100e04580020303407284144d02009100740d040d0818240e0a41c0a21010421441e035242540c80040d5114000b0b901c03a1901d10086520138059131b404215500c40314205030065814100340350501d002c071521001907 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 917006474 1250 917005224 917005231
    0xa030b04110a120303020c0c010206010b04140d0816020f0108060d110d081308061021030e0a08030408120a092c0a02041805060906010e04060b0c0a121103030609 71
    0x4002c079040403030420070a84203412201c0c86582c0042c0e032200511101c5040040c44400305046401a80c0100884074981055406640c030b044950b80c0000140700c0054981c640e080c0c0020030441021603002d8007103002825440c1824020348136811048020401107403141c40484100b41c2c40a20b2902c80c03404034041c0d20b0440100b40000c0d2160007801c0c5280c80d140180c0e04071448c01161140126801d2181c03aa040c0403d40c1c00070301d540c003011200c900707017070310f4004a880d5400070081d08003270b81080009040c485c0305044d401c0304000d0310703100d8441c4e221850291a58041d0095406070f10800242c21215614070080f03507400b403200c1c1c5d80e5010440c241449030400000c2e0300ca20b10100c1072035100000342158021407980c007c620700d010040e0b03107500c0c15803400c280d5440d40c0c80396070740d007840c0c541042501d031200c01c01e4560120007464130003400d081140c00117004200c1d030780200070451008617016030b40c51000a14606a2800340c4120051110340e204102c955103c0343d000140550800d1020178010f041c421b003860340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 917007724 1250 917006474 917006479
    0x17130201020c1c0c080303100b16021519050f0d0e0319170601030c0f120e010906020301060318050a060207080403021c0b09010b06030103022e080105040b0a030b0411 73
    0x281c4814080003d1001d8080c01c800c0c8401152000150204203c2d1030400e00280005070256065282a007807074010180745120b000d030b1031000010300e00c3d002e101408468012641c001c010348003e00020701500d070b540c0c004d4074515900034203649101d6407a0f4020070985524000d5025903914159030f16401300050032444500d040e0a1005000703101b0440c0b03110010001c2c4545980c0d58040012041c00454040103014000754145490050001d0032554000500401c05c070107410411094610b074143d075030051030408000d103519460311480c1010841c0c2c81c5c00031412905995010f015a881c00955000030800c8800d000f003135540000918000516641c000e402c0f2035004500d55401d19a032500450346904d0320801413809c20b0840280304042014900156401900001c003c0203018012004609c05100c107010203441510090980785a1078121b0f00740340d03000b900c00e0b5003440840e11007080180c4201e400303000c4d5500c51790501020410354209604030008036900160a00c0003525103803107494446511201058 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 917008974 1250 917007724 917007733
    0x90a03120207020d1e0f11030105010504020a0e0d051903051905040605040e0c040e090d120b03070303050903100212070e0906090403051308071815060f050a030b04051e071713020102 80
    0xf06d0341c80d8801141e1980280ea68800380c901000406084a5050b00001d100e2072040c8020401c4c1c41c1d21100600034510140d50700b0f4042c03500c5040151410344034045082c0312115103081303d400c040d80702010f0b22003141c2c0703400002901d0800c1c45d07081e1010702941c0518400200140810003911500c0740d48250048901c440c5ca81c44d1130340b2981c21501118044032201d4990340620000345c40e41d40d020a20300229902c890041002e4041200000d4603072809100150400001003469125680d09001048140e80110011542c4a40010300da05402e0030440b541d001107241040154414105082024401d8600030060701380c0b03507555581a56980c000c4000c00300c100b0064100131903550001c02040c005003000310346404800714140d100e02c1c29241c0280e5403004103c41c80004000b01c540140441c1200c00150034941d442c2c440f0420101c0041c410025241e83c41424403051000d00156408803075004000e03a0224000303950354110a54001c0c101000d07030303019050310000190001c1c60b1084003040540c030520688 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 917010224 1250 917008974 917009033
    0xf1107051f1b03060e06150405060a020114090724080f040302011b080a0b0303160605061225060305070e060a02010605090c03090c010804050604030309030c0803090a03120207020d 79
    0x1d0b40140601c441c03404203a03649810f00a0308201010568002002c4420400305101000b40395002c0c0264411503001d42c0d0086400340546000303400c081800f00c4541c81c280103038540003080d40d554084074407440801c04d06004002c801d0388010160700a840c5400c1d15100440e072100c11501075821801031098003155a18802102403207000c00038a1003d1550b07079614119424100b113500107c402d110101c5201e40e00030030010186000700700304600140d40040c0300003142e54600001c9050314a000013051020b0040301c0f031031000070000c0030b07840710f41c01c80c5880ba0005040c1c450506404a40e026140d59010401c0400140008d240c0311008000c074001e184000304030242d5840c089240e07040306031403940e036444000c020400055010003082200700c2c42440d01c21014105a20f480c0c1e00c40002920140805072110554014180150080804140d00041080d680e240c45510300d5110f4442030000c41c0010101485900f98504600a8886068000b0039492900c2d5655442203000900000d103600c4200e6802c404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 917011474 1250 917010224 917010251
    0x130f0210090816170318130905030d14060109060c12030e010e03040302150403150e010605090c0d0e240a141e0f0112080c070b0a02010f1107051f 64
    0x11803030300f2111071009519a0400400701011314110314519080da1041c4480b94001c20038881e640d051010640301003807091040c40958000e090603883c0a071261000203a000106801c560004035103003601110052a900d5442c01160203160512851b400a11032810f2000840c810ac09a0b520031082e5090008580700110303146400c0d510343c1034278640c1d140c00104040081d0f0600042c4060344800c6214500e00c2c190640c3d6402d0302000e404146008010354030485240c98090950000e400707040c004104403520318001060034a070303900018440d213109080918032419450005000e441c0070700414689298008000015800381c40300418401c0070700e841c0c890031221000ea410320107026401070700d02c81c0c22600c11016030301030035103028040b100312481d000e00400003104812603c0c0d000c0c82c3d2004005075240c4000018a1520001760445d8404610004105014640550186840380c0b4003074414800301c602c1e010001940d0080f450040c010b03800c00c0c3d403202114038900815051144040c40009140b2000340207 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 917012724 1250 917011474 917011483
    0x30e01181d010f06050307050c0304120605041b06050307030b18070e011106161220250b040809030a08040b071e03170601051e070605130f02100908 65
    0x402a0340e509003811442010210300e460241250341003100040386041c0e8000c5c034a2200030300000410134042000c030030800c024022200140a15042111099454103240c4024002a202101c1610310070b25141c041f00c0b810040041168010b880d483c0c196640c144017030740a403100340100c0c3e40c490301c286c5c041c482c0381c03144401c07146c0980c003666201b6240f8030020001429180300c54001150701e134800340c20000c40403e44081402c420565140040515000c07111840c040d0540d02c2c1162008441101c0f1001031903501e001428590384114854030410308078040d40e08001d40c503090040d004840d644006404940d00d40003e021400b07020301200c41060840d101d500f110780054202c05644000002c404080c0b0107040000100304043c440642c0c00400d40359000317840302000078598294950038500091850303002d00181c42101c03c001c00c0106102d01c03015610350141d44041d400326025440d000c042a02001d0744a00f044040f6406450024028455000c00512040420100d4100300c00c00c80d011444100620 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 917013974 1250 917012724 917012729
    0xc0d1707140d1814010c0305120a0f0b0a1802071110030b041409030304060f0e0a051f0b0d0605040c1a0c06090d021209030309040c02030a0206130c03030e0118 70
    0x10103400706007030151000304100443c403145521281000310902103a440010020302049003401d00100100b1a860107442c41d000740211035940300004000c010712801c0d941c01041e0080000c60381001111114800c1007140c12140c068500080c201c000c2c01c0b49603200c2c0340d0042c13150714005c2e6501e006c44550400040ca550a81d02d62100000e41c4480e42e00d903090a00e1300803040b100340c0b0319201c9620707858000c0040b50b982c0401400582038503110141c007140304070690301101c104942401a154450b8244c1429a9641d4010b04001c1010100b1403001c814550300d4445d00c011440d00609102c400e8481d5102c8901400f0090300948040c2c07554039001401150904901c914203410500554443e080307001c0c002d042580c02006449503400880c40940c00d03903400319045907040480340107a9110f074000e10100e032445c000c040515030461300e00710901c822a5000406050300a05981c01c031100c1d82d41d203888203043d0b41c2c0c55400092820104030806d10000c1e005401403007000da4189044480c00ba1602081400302c0a1035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 917015224 1250 917013974 917014013
    0x140f19020a060501090501031a06010e04060602070e0f09190c05060d05060f03072d08070e0103052109060c0307170a02070504090515090a14010212090c0d1707 70
    0x700000381c20030925024082c014261a40204100e40c5982c07076480c032032000340000e5050100c2c00f10000303031145c0c000c15a84210100107041001041c0c0c98410280d515041809900885c031030301070000e800320440c0103100307114045e020003070f00b14011800c038044c60f1003204902c00c60f680e03c0000d101180e0340e112903000d018060030b00500800c280c00c040c418440c2094098606a00030b0b0407001082c404468035401a081151240c8460b07000e2316641030178070140c001d45030048122405030352400102807841007843ca060324025170641b1100c0242c4103454585590201e002c01900e00300f8004805036252020140c00417000b03140035245050b0040ea5010803200102c0c078042a010001300342c5010300b41e41080040d01500b015541000304054945801d07a131520750b202e580b81a0403640c03000900040040c0225000541d00c8061804050002c0a08c64083d400ca80348094055580c640007911042000440b01200b06024004440d910003d03101c4190029000c000c1c140481800c110a000142e031590740350410308141d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 917016474 1250 917015224 917015233
    0xe01120f05011409040f03050c010b0a1202030609060f0c0a0e061308060a021c1a120a0501050c0a050d0b031c02160902040e0f07020a150b091006140f1902 68
    0x14004071542d02e003d86034400d030040000404200010b50007165240ca0160141046a01c40e02c44410240c003415460b6032941d00010716800c00100400c004400b60a040e02c00c0b000c0d14490750325404400c2c0d960400302c5a074040096600041007141c0c02d50b8000b020150300d1071070f00f00b90203020500880c4640d403184070710a0403107025a601300040541480042d400180c0750b2015441e200c1da40c0da4a400000707100c0081480c1c10b030b5490015140703180000c400e0314a000003a06c842103840c0054105511268281415540c80d400e0100040100d03085104071002d44105442d81030402407044001c200406c21000a241c041c8503e00c58070100e00c511491500138022594001c20350b40242c01e00c0302c503103041a80e000d071005900510060003002c00483c025a4081040000741d072450f84e82c40300803131508801100140c10500b4001680c2c610b49000d030000021640c0984144a80d03488595040706268201d1040390001180c1840c40d44600809200030580e000718501403e0030002d981c501e00050900065840c809640b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 917017724 1250 917016474 917016479
    0xc05130e040606080708101d061003060b03030a1205040309030b18010f0603020d0b07052709070f0504150908030c0c031009050a020904031e050301061704120e01120f0501 75
    0x84a000f0003024190380030203041c0d66840d0030300c5103680c3d02d440d41e1041101c6843e40440038000200140d500c0100301b03003804503082e60400207011074111442d8001995440d051442103141c60400000b141d26000c09039840c521a4811b41c1040c0d4028080544101c0c104804200000003180081170514000c208a010f0307548000d05440303031142114009620740040714103124003040941d0701c40343c0032401640c20101002c035958809100700c1d060303c107605540706480b0103101c1940508040071002d200041042d24108010b803600081a14061204150400040c00400c801e0003401c0191751101540c055600b00700400396121015541960495141d00882c2c2d4808013a68017249000c000307140b00040791001c02c00c082ea000ea10760544494003018003034000c03040d04000c070b02010305c149001d03034070460600458803442d0380c2e003035000b4610b034800c0c410040000c2c014400d50300ba40d21020071395400f13150301c40c02c604100d4041181c1070b0340403007041580038140203c041038890807500902a2025110f12618001055070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 917018974 1250 917017724 917017733
    0x1b010c0e0d12082710051e0604020903070503101b080403051914070b070e0114071101050c0a0f021003020711041a310e0d030c05130e04 60
    0x1080120300074480e00c680111100410a2030220584080326458044032031381e9001e02c100c00401e9481440c14182c21140082e942d00c540105e840e1314140d148070820720194072010700c004141c0024500c0500c92410b40004188185001c0e1f004011018002d8103980580342e54030300190800170340e00c0d016214162903024070102d41d6124003200003c040c41d030410410354103103500d0051140c02089480140e90300c41c0e845400c45a4003c1101403403a24071140b2441d92819185401440300406039500c20104040c24004101d942c000e01d19922150703502c044d245d00700040c64449021681c922036609041c000700f00032008000718240966507980c0d00a5003002c0e0052450720501015403440000c4400b01441030000b2000605240b6480c40c1d002402c42c0e020951212012911604c030070030f140019070009a030014052061a9103d24982d1100440e0051107514201c43c8000b05456107142c0c401c00b5034001d000d50b8180d060180e07111500080d494a46903050110100100d0040c9a00d5008000c42420301c00401c001c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 917020224 1250 917018974 917018987
    0xa143109030804151b05090a0e04060c030e030405010c080702190b040e01080d05031609080106090b03010509030412020910090504061a010f0f051c0609020702030d0207050a1a1b010c 80
    0x140d83c684e02c00c00c4144500000d00581c1c00d40317214444e04008000402580b10342c4d4004084000e048604c110036103d0403c0c0c038100004103140c0341c00101182c2003107404181d2032b602000350380c02c4510684500d1144d0031607644a1903a50702080089a11054080c40c41c0308141d00c0d0700144001d0401c1b40825651241010f800d541e24070710590060300b40d980003c44980c0c2e580d0303210041e250402c60f80301c182440306807422000d48070081a50465541c640c070b08400007d04054603000505005c00a800030080c0d61188245d0765182d01c01c80c066a1a41d0091140400060400381c034a51b5100b071130001800c05e0582c95a154105603031055509541c144c0d1240e004403140c000407544c00c1d8140d2001d003840741440c640e18001404d4240910745800030f2120110310a550b1025450019a60220081c401c000258480e0f403000001c0d007080c14113900034030420003045041030000a010f030644d5002401729030440d00e000c007003d5940c14a80c0c44484c803100203000d11b00c0d5000c009043c425600242c0400031070301c03018060008020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 917021474 1250 917020224 917020253
    0xa02010e160b0c21071505010b18010c02130f060f12080c071e0906051921021816050c15070e09070c060e010b0d0f0c050d0b060a143109030804 63
    0x3c1c02d00d00001084403181c80420ac665440c0c91040300211640c1c40401602d11105844010307420100c140342e43d084d101c006622004500788070103420003805458030024a00100c1c68098100280014000c1d5030110b01c204000c0c1c07c2c1d905002d0200c8117003648403c280200711284508620b402d000210301400351882070b006170400b50030b0aa4880440d4840c142ca1007040e015988690800180200320300014800c070036010400868000d8101c8102c40500e06040345a20011110a14080003200e0b110821500c908120303040701c403020f00240b9a213029240d1452502d01e019140005010700350300c1a01e80c1d522903e96003449100d8686a00d0b08100b030b1170514074141c8580d0f800030441c503450101d00d00c05550750030003600444c1c0e811882c412900d29251600711080075041e04283c1c1c0c090b282407070b940300304101900001d20992059800e010019591044501c01c00ca20f41780d0345a0202c007205034441d80482100b0031400041c680044a81d0a004c00d405120031189400000e400240c200300030001440b01c0403100060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 917022724 1250 917021474 917021513
    0x5060a02011a040e0a0204050a02040929040c050318070302181b2b090b010e16030c0c11011701090e0f030906031b070503030c0a02010e160b0c2107 65
    0x1a500300080585c0d1034508005000b481950b840c008109000050360565000d000604010000c0c0000080918800c055114605140700c910b410450348500f0180141710400c0c0b03254540c075003982c0300c0d0422a452004034566203c0c69104070300000003d80d491084040c070760f010b021400c0b1403a003020808042843c2c1510383d241101c050400c0080d1b41040d50b030714904070100d5050540ca84c40503100c000d4502902400740f003d490b0b100a1070000c186810300e0fa0025028000c941d204095020100c0c0307082d4207442c41d4800010205120540c00307000710306120410400704005140000120502000c8a5003422003a0003080e065952210f425800c500200000000e441c240001075080048030000183c00384401898803a182c0000c05103440140856002c2d0b9543c140d20206590300c9180501045c14141c2003800081c00542c2820100c0056440200c1c100f0002540c1180d84c80c841c50410b1544840e50b4054601540d5512070b55640c900b14605002a0404261000b10810354034003003400d00010300646854bc2c5074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 917023974 1250 917022724 917022731
    0x403141b0d1e0f030204050d0c08060703060302060414120a03030b15040e07030c12050c12011d010314190c03021f1d010507021e090a0903080a09050705060a02011a04 73
    0x14025402c0b0481e61003400c0b828586282c0071644040e0440c064000c42d0b1120b50803031049400d00c000c01a18800742016078107880102c03101980e58543c00c40a0710300901c8007079000241080709020003640c0450610100030054004c1001d05540c1d042c0364070b01709900340d094000030742e03070a5841d005150070130741a181088110602c50615007000e071580c0001d0405404503042c50fa4591400e207109009454a264040c01c0580401c028946000b0807500c0341e0040a500360761080d8200040384c4140d4021281000c1d0101d551007203042c1e0b085542c0d03a0a1070110300f0300580c1c0d078441c62440c19059200c100d108485148150900444140795205004010a00025104c000c5005200000c1c400394802d220364858401d2075544c4520303004140042e58584241c060281d006084a00d890028489078000310110150980d044202c2d95912941c82080310803203c00203001445182c082a15854030b41c0100c10081e00030700030f8030040c9a6a03c0060401e9000400c2040036075100c41c0448100c4c0711300a21307801c6040307041e80e060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 917025224 1250 917023974 917023997
    0x60411280f1b0f0b0403020d020709060b1c0b060c0309090a020702090c0904060e0123010302030603251d04030314040f06090c08010501080c0f1c08030403141b0d 71
    0xe001c00b8940085070300c400882c1001041400402c201203003030b15400c01c041c41201c3c10b050030000d480e02c000700404000b61080c3c1400055110350303403060034101d1b42d105400390f0400d07503c0034400030710741d0202580c001180e0312000c02407400d5031140020316451221070011179035076a19109000800800810b484a9948180300c4d29026072207103c103090348550000d001541d180d400c800010028a8160490000c00b10307044004a0707801514040b484c01101d1100013041032480c0a0011021ba1104481041e0541c010410b03583c84241c07422041800c60138100345115695844a8150740c89070503c0250780b490002100c280810b140d05841421408052042e00210b545000d071192001e41d03e14004c000d0080c0d80c0d4110080500c0f0f290404540074040d000000d003c103503921480d5580e20000d8882a610038408003030150000d180c003c0448000c000c0b071601c410150710458844000300e400c000c1003a010f021042281c141200032000081c41745180354042008442464280c2034a01130000d148401440040e5446 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 917026474 1250 917025224 917025227
    0x110102070f080307050c0d08120a090b01090902191410030204120305031009060602030901080606070b01060206091b151e03040309090c05071106090406180504060c05130905060411280f 81
    0x2100c054041c513a01c0321925452b1408400c0c02448c1c22100501078501442c000b0850b008907410082c1c0d001d000712841038007640310301106800c0a855116481720a803425040000c2400c1140f840c0c0240181800c00600f007603a54803000043d425050411000944004100004a006c0302da180c805808100d01c2001440d051820180d582d00c10044281e041c44040800181b90356141c50446181c0c0d40c1c8a9003403043d659655102039958081a28022440d0190041001c446000a074010f8040d0b40300400c80c1c1c505540d81040f18029511044c10b8050407000d841008040c0002c036030065000b0b038806d40c3c94446030ba1070914110304440c8a42c01000401008101440100f4049034490700c0f81401160010b40d82e41d258400107005000301d42c41030b00c6842e100c1c0311000000d81564021441f0340c2c0250707400d001100c1c100108480c03074070844840f40e2143c2500201806214203540c8082e921500c00340c80011111501c220740c600e180c0100001030881000c40d1060741401c65100103a41c213900c89820091980500e8860 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 917027724 1250 917026474 917026477
    0xf11030f1630050a030e0d03090e07032003040c0b0918150a062a02090406110d090609030e031b0402070512131e030807110102070f080307050c0d08 65
    0x40c941103100b45a50700c2d80e0340101c10311040240c5041c40c0420b080d1810900d0200e8541d003120700306802040c00c032042126603042501509070400d034155a2421054188044c8101a400151020042540e140400d1100ca10358510422001c0d41a03100340762a86001d1400d00035043ea43d4202d03050080c1c05206c0300783c103600c90048840c400148025108650780d100311210001118020f58a50300449803880003515a42160841c1e14a040000c503655038005500703007400d51070f04980002504000440e002a02007005a40100314803c0f911005924110600134003006492940c2c2003a201180c0c1d0b22811407c15030020400d20075802d007500070700f28000030581d4080300d00140300d00d41402076800007400000c020701409110010781c800d000351603d664030310050304800b0401d030048040c91502e4241c000c202007000741d155401c03a50b01008091030500a603440000c1c0000b000d145605620a004022031907406101c0d05402800400300110344079880c2d07080c4580b4040a103054a4041e01c40e003441310010802180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 917028974 1250 917027724 917027729
    0xc16030c0609081b161d07112e05040b061207031a010503100b03100207030c050102030132060703050703110609032d0d1104090e0106030c06170105010806030a0f11030f16 75
    0x5e1b00030f01541c0c0c0c01c40145d80e02c1440c080b0104481c06091200c1c0718400e8800701c5040709a40c48000c2ea1100c06c162a545422603006a0b0050008650a00050420b12744950000c0080c07410303400b070303d80c92650f90ba10850301205000607410543e508038018042e0b400c042041c040c034885624802d214124454010a0302c5800044122407030a0b00011050149801041d0703850741e540d800781c0219620340c0e403800141003000c00d010702c0a020000c003c0100c500c0d4182d00242e070ba9140c81c014003071494006560b50640d0310b0b5102d044128180080c80c1c200701a500c07014003215128001b40405161b5552041141c46030100c001d1040e8040641c03980c01c80d252081c2050140c0d9840700d005080001c0c1c903205170291003441d01540d8170008802e4208951850750150640080c4c048070321401001c0c00258407100196103500b00d40280b85466040740380100070641c400c40d030442c0c10450180650304092101e03100c403160100c178828155000c001d041b03901d02c0c0d0360800308003c154403030741e074006002c144124400c440340421a61 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 917030224 1250 917028974 917029019
    0x80c01021809151203130b03040204140403020309061615051f0315050702030f031f0e0c09190909050105060f010906170613090501140c16030c0609081b16 68
    0x190380410004004004561840e02600c4c407046c40180c0d03500348000035500403603003240100c1c10b00000d2080e01080c1600180525810340256003840c03c0003050181a42242075021200343d07041d44010041515006120404620780c140820140360542e00f1550f04840c0c04d030700001e00e076101e00d82000441c400642c0c400341240c0c41e000102e40e545410310104c0ca0760007444d5512034241e0002080c80780a82a41041d01d000146258018103e41ea5a1191f4a1004004c44401c10420401c1103410b000d4581540d00d10000d042c803500380880b0580301c000080c200c8030200300880740c030b07907480041c070030b46c3e01d0880c44840c81d1040134a0080190b03410214010b0844042c0402d0f020900c1009000c50455a40e20000c08020800c9000801c0b03812001e080c040d002e00100c0718503821141d8400d02168030381160b0011104c00c11403000740f0001d00b038032316170701203410121055081d62611341d182000320024650300000c1c40d004500031a1004e00751710000e6450f040a0483c2c01c07001c41001050004c2040c642c0030310010030b8030702d10b5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 917031474 1250 917030224 917030239
    0x3010506070b13060c020a140327030f190501050f091e0a0206191806200102250210050702030601150c05072303280f080c0102180915 59
    0x1c3d444500004002c1c200014100360419048040c82c07940010200038450003070000c1440e0b05044034486850307100c0c1103c55001c0c03521211081d400a20480c100001116020b03040b105100281200319040c911901c0c0411a0020001380c0c41d01403040c00d0103842d400003030301788100110341451003c16585070703401c180c40040315407426000781e045a418840581c28036006003a20f595140f00400c804410000d1005e810003055079801c2828401180d054a002613400f0b0340c6941c04140003103030503400045030b142035400b4159020440c0c0c0681054a08103074010440182a841d800320440c0b0400c03854110784590101082401d000b0700000d6500040d5490444080329401c04480c120380904545211811001910500c18000b0000f40c105118900001c002214505490540c0c0000c0815481b10b0703010318003441c10900000f10344202d0310000e000b014002d22503640c1d00e0307070443c855955801d00d0300103040070501c9960102d843e14401c2c119203a141441441122507040520304074040914044554030414092582d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 917032724 1250 917031474 917031481
    0xa0308040c0b0712320f0d061203020708030703120c090b03070206090d0c02090a0b010e0d0501050601030c0801050d060903180f08120a02060118020d0f0b1503010506070b 75
    0x690041c000050300710300da002e0f6500c44032402d00950022024020400080b90203151000005400b032001041c42d81140804141013a504d100c2c00d181d4102440110b0b00714010014143c085100c0c0c403030100100f5840682e50380c1d100103400c020341014a541d0100c0c1070b40d01708100d000c000a904c14811100c420103e070001076110701c0020100d880c40b00f0b03600100c0741c0d8017000040c45202c94000621a110f010004212008285a84001c0f500da0044e40d03c02034102e1000da0201d0b07140070658214046800e07040c07400d00307a6403031800000703004481e9040042c3c0d443d954510030301c5100d59050085818950107400c1c002400c0d45030802003401d0443d82c1c0e001801d100d648111080070548101748600706c0b68160140fa03c03203541c43d2059072240c00078500c40c00b01c0350702c103d20780001002030480517030b031400e421070b0054092607207800381c0408503000d03d81c0e032076a500d0b43c00c202030085419503204400a03040d41c1c801c0002c109031401e0a12481803007004030182d52010520040100380e48813006c07506c46561003104881181c6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 917033974 1250 917032724 917032733
    0x24060903150a06082b1209030e03160602030a0507140613051605010c080306040f05090f010b10050406180801020a0302122a090111030f0304021314040803130507060806040c0801080a030804 83
    0x240191b81503002c540c02c001c00541070540c000f440c3d10b43d070302044065030b541907140610f4154281c901e108917809a0024064842031600980180c01e519014064100c2406030640885c2d04010048447c3d01c03800c2d40410701b8000703010003044898400b090317200c1000f680c0c505060010309030031680c100c000c040000000014413207490342d40010110343c039a094203004506121030307150785440e41d030746240d46958a05081748010b841c040a005100d1441601c03174030f103460700340101124a1800040d180640000300b40002645820034401003102c03000a540040c3c0381c180003d081c5c0c0701c1a50141c940203104c100281c102c490528110107000c9401e18928020340d030340f07520100503520340a1405a040381d6000c0880c3c3c10080020000040d0310551003140e00c00048082070740c107001190f2240b054009028244000600010f1010000710b812801540c140b0360711000507611145020745580203000014a41e01c02c0c00741e00e0030b1500a0302c0d00d1001d60305001007650705000341e05a40b15003071100a400c00581402240900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 917035224 1250 917033974 917033987
    0x1b020607050913180809032814030f07060c031b02151b0c0703171e0a0309050d0906020c010c11041a0d030302090a0e24060903150a06082b 61
    0x25504c0ea0300caa00c8001070f00380380440341c0000490500902600d0494a80c44622424070070108500000c41c0d55500ca85494440020401c0c51035070780d40348010009660400442801f411019106140c0407541c8507643d2401826500030440080403403200354400010f680d004100400e848281604507401a62110000b001083c2e00311080c2460170320010710842017207000700b04082074034085d00444007c0c40c101c0300c40b00014452803122012500c0d181c491070981116180051214a1b01440c01007500f0f4003580b90181809145503400d00071a00d0785d5010030003103030140806c02c8400d0003424040f401c40700c41c2e16808925201001c003a031140c1d689007051a0000c0c801400091041e0b40500041046041c618000d8000d60050a406204900400001507503020b0140343c2c511800a0034a154a11a0303810426103200070b6051400c1c3c2c0c01358041c082605182c03010002c0428064000c1c040e51040d041144124081f59120780102000fa004079024000c81c250420450f100703201e03a006a0005040a000101c555 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 917036474 1250 917035224 917035241
    0x10206072304091437060902030c030f0c090d0b1b1209190c060503100504020c151006020c01050f1215040c080402130906060302090a1b020607050913 66
    0x802012030b01140c40d100710750050380b90034030350101200282c030f42040003806941e1010800c40b03010206449603080c55a840d0426525003034150300881c1d00d0381c50341040c0050f0b820071258818064004010400362017520096185c0140440315028901062a40032400010000d4000b90100c0b0b202004115200401d945264020302d2815280380c441001e0004c910300700c581501c891400b0b00c07800b03115090420b41707103d5010003643cac045480b01030649041416181741c1c00040241d0140c01da0480300107055190380c00140041c000b00300150010361108001400789540c0504488005800c8540a10040c2e4000030450900c5801342403c41d12015000e18250851041d00d0361404521595024444043d030541a03480e8101c03801c0f9001d22007181d1034281210240b00c2103e010798040c0a04a078900180d0f45544803020260080300c000c2041616038011480f003803016121320700c40341d90741d043c2020054003605484d120140c0138409050a8141a1002030080c00340c4500c2c144254000754144130b001c04142d0000c040d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 917037724 1250 917036474 917036537
    0x4110c010c020a05060f06010c03200f0309011403010f0909051c0305060f090f01090f090f0b070e030304030c05040b130c020f0607030b15090411040909050706030b01020607 76
    0x300d00410071009446028514080303a1074400c10700405d03d14480c42542ca441400c0c1139568208a20080d2000c6518414249030325012078a100d1120110310030502851044080d0302c001165500b04941c0010040e240d07681a43c80400c60500041c051841000000401c945040c4008105210b0609000782043d5020300c3c040040b00b04000f0b000038994158000701e00c28441160ad400041e0380303180911044ae2000c5550400e02e42c0103000602ca04941580241d8008810107000540a101590ba11002070340d007181c10758810380104100300100d036100248890003103041e030186040614594035078015178610301500d48601d803100d01d1840161205040f01c0e106075541c04041c410006954030281d00c98411070403111090080000040e107080c003a0003096035042010b0121400204603040c00b11658101540c00d5500640f2890641c14000c3d5001c05040030300342003540018040d105103440c134540400c80d4004c07001e0605110304002103a80201c2c08603030142c0e450800c9a501c554482c0c0c0c02c000d21058103410303003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 917038974 1250 917037724 917037731
    0x40f0b0a0801050417070201050307080907050d050105060a1d0103060906200a0f0906020a080705070e161101110702060d0b091f05040506061e0d0501030f03081e0604110c01 76
    0x948000150001801369000b804038481c005644480300d1402d10600c00c0107400b01d00d040022800b107074807a2000070b5100b030408099861071030311800090900c02025400342e5486c3c0d194418031039075252440060006000403017001e050512100ba49004600d41440050100d42c0d40721541020322130380c0d800c80f08800030040014440344c00012070000d2990031101501d00050b01114039001c040b800342d290712003a1a500c0c0c000b0b10401d820b80c0c0c1c81c81c55650048000f100d10740a601400a90305c1d0b4410781403401007000c011941c031286061000100341c1044150b89c850359a041104c3c08079014030001c1101d00890f01a10400d58420f03c0d0010080907020060079250405102400c0282c41c0158621840700480c4d881020907100f0f41e50410002a40c1040e585036500010800180001c149002c400320902c200400c0c003282080c0c034407040c95040b21070907401614480340403407995040540c032403550f60344040041c0e00915220001c2d002a003c00700010b03c59800380b0390700c049403005103000358260381909031504020f0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 917040224 1250 917038974 917038979
    0x4051e030d060e090606043c2c01020703050412020f0307180b0d0206092e020303181507030c0504090203010b18150906090a05060c010c090f08030405040f0b0a 70
    0x801c8141c01110000813078003030980855200d00d068010044010320018003009000901c8501d4904d00044804c04100009091003801918489000300119a00780103070764041c0c829100c410780050501000001076a1b441044030a00117504078040c0c1d01a1401c0d0b6040c00c003900c13010310125123500d2118202551503c12202c0015148245040850f0a10310701c03d414400d051a82c0b062105110180300000c2d88540300780300d0414542400c01d42170503908010005040d13100004114034000c1c0310745055002c01078000204120310310320700c0c80c030b484822035401c4000e11021010b05000d050000c4c001e000c506c2016150342c54003003541c0c8664240c50260140103402c56480d44d4420302c200096002e000c1c00240c150401c600c810f2075142c200d903065079543e0013200d108d20740044102000081d0380400a016804503103c10081010780b41d000144c8580f000d0280005804a214030001d05003008983c014601c81c14240b03000c1c40030700004000d5408079003046d80c000c217040343e001c804400500100048aa0041e1846900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 917041474 1250 917040224 917040239
    0xb0712031d010e07050a1409040204020d090f050309090c070b06010e030f030a050301090b0402040e0a052203110609070815091c0c030e030724110d032304051e030d06 73
    0x2484c084510031901d506807030b640d40e440c150907c0e642440c01079000d9240800640541030580061800200403803001442c4040e43d80c0b02044400600c00a55141d4404101da0382e40c0d00308012013030b40081c0c0c401039450500240f03560310f480440d402400d190412061031164a0745072801c00c480c40f03440000100f5244c4030f900d651401041c98000340300350080c250400c04001454202807081741c041d81c501e80c0d4480c1617a50b80c2c540b070401520018021508011801d0749a01c02d0368a60800c00104900c03a54560004111600303400d40340c810054081015604100c82c2089007400c000340c001018841420514580e80d51038103a5030074003020200c04282442405200e05401ea8800c4400e00d40230700c25240c0c405448640c406041ea04d00e414011002d50aa0348420800840d00c0b0b030f40c905444400381c3c40d0459140b00002c0c12141420b800340924800300f41c9418400580303034a07480d0060f40000d60064803150034501510390079521450802e405061596075030b0700e2015420140300319a150540f140b82803020a980380d05 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 917042724 1250 917041474 917041483
    0xa090f0b0d05070914010e0a1a2d090c090618061615140615071703070f031b050f0904060b1305030f100c020a05030403050a030305090c010f0e0303070f0f03090b0712031d010e 77
    0x4407841041c140c140c50f1080388bd050300d800703000760100c20903981042c0d54481400400c0d84100d030714060b402203040c618000303079942d50700900c03044a00d108032000c407440d9071030551042c0801d424078001d80b600304042100c1102c0310410907944410104d45680403070400d90b17892402442911f4000d00540d022100300a0713021407000055004000c560b030ba095482480481c110102e030f0b0b8080314100c64405104c0d1050803984940c0c0070b0413200d2100000d0b24901020300c0c2c00902150156448803032440b8000c54250191401041040e004010030b5002d409401103400015071103840c1411041c3c012907407081a901c00f00c0c404c00981051310b40c0311088a6a6503140d0900710b07a52940c84030210002820301001800d020404101c0101c0b9860684070031a0300da104500c1036841411504400350540320034082c810100700c1c080100041c540c06000070320040d400e1824000c02c0343c6465041210b00300410010800000c0c03148140ca0210041132800060f4040303114071102c000d01924014103815800c004c51070304030460105 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 917043974 1250 917042724 917042779
    0x6070503041401081806010b03180f010915020a090e041b301e14030a0309200d110f0d080d0606020601050a090f0b0d05070914010e0a1a 60
    0x132038080c3d80d03a0754044050030640b80640c0010b281e800c40801001403250550103140c0040e2406480c00103245085441ca142280f00c840380b40e40d503911442000d00340111224600c1c0822201001549411001d1201408003442c610134040240d0810300040c00b842088281e0944142c1030142c2044099547e0069030300c107040300007603119254010781d400400d20f001c44840c041403d50103800100200300c1b2007140b842d2020105000d880582c181c020740d8081c1941403000341581da10581340020320a0300e5007085104031041c404200b10000509008991607550541060081c5909c01c9410440d9200030f03010509050842c9601307a0005c04080340750b0b040004080291032100000075080003040d0b901c80c4100c1c0d59a9003071048640100c42d884050200100c240c01c6183c0e01d480c403000129007020a2004503220590001003a00c16801680782803028012500980c01d41201a050580340c46d410209040745101026024509203075940d00d988518031041c101e00c21006100030400d0040c120700311070b80d140e1620b40a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 917045224 1250 917043974 917043977
    0x21090d02030d0c1a04031b051c0f080f01271107060b04140415150506040b0319061d090c04060306050a0b030f060622060b0405040c0e0f090606070503041401 69
    0x851480c84015100441644210340547e10b480204607940350b440c1c0a0130070448159010b0144221001d09082c5190280306c3c0c407596075075440d07544001008010b04116024002d0300320100e090700100000142e50b000365421501c040d1100101b406140134040041142d40ca15035100c8001103846001e001c03a5a1050200b100c06840a1250b40c1201100e03203054075048500420590090856000301e0301d0503400252144c0c1e0100c500c00150f40c841c80081c0c81508142d1101c80400400400c0090b1049a0040041e101f01d0200040c0710240c20625004084112001d02441031200040020110b00c800c005451007403034094020418140c8a06040300940300c04c07188001d031142003154100c1d45080004a40e110184d01c01c0148c80f0648441d001c0081d45421a41510310070000000407260240071846841d00400d103070300c1820340e00c6141c0014442950940c1d01c40e0001e0007400c0c8000200d40e01c0380410780c1441c8004035500203059443c280003e40c03a005081c1302500d10311010030003203407103426010080d2000702d09 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 917046474 1250 917045224 917045243
    0x18071e080415140414070504050a1506020a050304030f0836060f09090c12070309061a30030403080c01050f010503211b011a0321090d02030d0c 63
    0x81400000079141c400c1e00a4112810490018005c100381c5640c40078000d80350000c0c1d80d5003d94840028051f100c0c1507414070151540c541d04c10384002003002c04034008203102e001500c0004180d4035996180d005500c0b0140c945880c0c048a0381c10008054219035034210722100500341d01e0800c482c0038a002489540344400da0400c8407407915a1f10340402074a640d182210031507458000e10304244040c1003805804141080b00a04c2211006512081450300c95040c40d940003c3d031200c5814410103035034035005030150380758102080e1821902c1c4d01600118082d000746c0c81444400003028220782c139844000901500d8000420b000c005c100c1410000c0002c5000d6400a000035199048024140a000e2041c26496403022002d03011100c0005e008100c0342c42000000c9040080c06003403801e0415003401451520795540100183c01964104880300710541500180051051040e041c082c080c009003814551403004600040150340c1c0d20b060b01c0c2c45590141c192100070000f440c2c09401c0964024007252015107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 917047724 1250 917046474 917046503
    0x50714010225020307141e0a0e0711060f04120e0f0a0f08060c160b1f090605130b060a0c11060d151401050d0f0e07180c08040218071e0804 61
    0x104406241c4020007c02d001d00006030b01198018440a03070585c2a0407010080b80021600c0000440c141715909503202c1848582c8803215260030200300501c00003959903000c2c14880460b115948121086202e03041c541680f105c18400078140310180c03118940c2c420042000403803c1e490113221241125504411501c1d60b481d20103c89816000b034003480c11206042c03400800101e02101c80c03543e04401c03658a08404600e2400502d107007407040381c0200c480c254803004200510304150000a5500c111f5030010400702007001c0014117148101070f040001c101451740c2c0e100901030402000b994650008206070350700c0c01d5a5050801034480b003660500c04850400300011404224070b000144c81d40161344035403500402d00e156400a15111002d0103000d9030366201c9440410042250402828045500c208040c11003078480c0141c601a081410810000030207000c0140c9a2041c0400d40c1c035403c000502103139994110844a600390a851203031b0501100c904070204507004001c080c0100d0082d680c1000005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 917048974 1250 917047724 917047739
    0xa050c01170c0316050412110f010c023a0c0f050a03050a03140f1605070504090b010302040207050c06070f03020c060307020c0f0a1208030117010c050714010225020307 74
    0x7049a00340c4100d40208005062450b40d0085007100d52140c0c2481820103403030b4018002841c43c607a00441d01c842500807045a1464003218140600c0c07001d02e0008204c1c41950702062000d0385543c4041c90103501e0824400400c1d82000b02e469540d510403122004d1034206081840d04c5500c6445200c40b250300100003c1410b04041c000141030700d80110040084100b00e507800c40c3c003031000201d880d0344220240480c141180c0b0140040c544240b040c02041e005031003600f09a4100a03103a070205224514001c0d208001a48020880d41102d404440043c2c4807001400d0050510008240882c0d1144000480e0b4040002902c40411030038025800c03075040090f040103010309484182c4040c0d000d0781c4605108822441c0044401c00101c0000d48030660301c2d03944046014502201400403280000e0210040c020741c6015003c08000304000d4000717021800180c1005080b074807942c0c501910301c8000300c2c1071070342d440c03002d4044851010f28002e8100401640054020a02203481c204a00c130380a0044001030f4003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 917050224 1250 917048974 917049017
    0x40302100c0512130e04080310080c0121060b030412030507030b0a05040b22021e0f0702010807050903060703020306041a090114041e0c1211030106030b120a050c01 72
    0x125800402085418143c03009005030744c0140c50700d0b504040c120315000c25420080109203020b06c1c422500a0303201e0916900054500e5516084004240d001003445101e981e030100d038941c0040c038224804d0a00a00c48488000580031a8004101c04100001804200080044001c82019041d50204206c0d2100d12086003500d03244040d02d07522025400083c810380c0b5003a4041c101515000f400b520000e503100141503070b0a203c107007a407500c0507400f0807129031800d0349200004910188002082ca40041c2c41d030100c581e4050181c0181c100110100014441401a0121aa5040000d00301c031090701c0c00c1d1200402030351044540502603801c0190b00c04e50180211000041072030010702c111810303801c24004080361140c04945035806030b22880f0f41c80c00800200312070045405450404580030003400b001400881400070a002a81e10381540b0030310740c5110905503810b460680c0380100b911514400000c2c81100d10700181c2c410340c050a4a600104900002c0e40c000856080c2c03603110254403000c0030350414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 917051474 1250 917050224 917050247
    0x5091c090b0d051905090309030705010212030a18080c0c0a090504050a0311010f051003110607080405010516050d2a020a0b031e011202040501090c1d0a180204030210 73
    0x480704240004050341540b90441d50b0701034a815041c14000c069900200180c8405880c3e4006039000060722040c00d0038140501d502030503081c0001c11142881040320409840f00500c4402c025035a40c5141c80032549e0106604c407042c2d0040d41043d210340c10800b8043d100d40000d00028820f0010980009024485014a0380f0880e00000a800300c0c50b181d0f02c080d40d800f0011100003d15560740d0715190008519841141c1c002d41d0241c000d13111a5065141440d0070003900640b8600c0b400c1d09100400010380c0c103001312001d0390f0083c642680c540d561070b6044403c0c070b644484014144d02503c411004240e5110400145800c680240080d00c016400c50341d0010100a042c0139400119500d03060100034000c100450308050046101e11042c139082c00c200600c03036420f8202c903504c01401241c1c602503152a00805000d40b4094400b040892294038005e040a04680381c5040b0038a1204400122540c920754520010300b404800e210408140c1c600020017580140001c80c0f15640c11901c1c1c05203207100e41c0d0310018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 917052724 1250 917051474 917051489
    0xc170d090f05011b06020f1b0d020303090a030e030319050a0905060a0207270e031b16120201121a2b02130e011a090a0912050a110105091c09 62
    0x43c0303540007104450000c0c01300700c0161102a001c100343c07402d925100c030007480b2036203032041c90b540485950b003c1da6080101300030610045520500038010000c90105d002e40056a060a0100f54510403c02190441c0160314040300074100e000d0610f485107400500030080501c51340d84000d505612101000f4050007000c254ac00180d000303548c10300c02182c0480c00030400c1140003420068541d2041c01c0ea4041c0c400051541000d5000032030601c01c0c01c0501c1144812200206000c2d04000c21240121160300b40b80e0310a0071000405a8000070959004041e45800803030f131b0043c18003227030401d80c984001d0607002507400780c0a000803281700e90209600e48410031402411400c0d03603242441c190200f1070f003034104076032698100355240c070040a01c0c002407103123840e2800701603039008038082210100319442000030150070400e070601d0080000039aa0b080340d25000c114a082c2541c1312003194008403200205207000c11a150f1074030051042c42040082c025540e0548400c0c0c40e10410340d02c410407a0242ca10340325020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 917053974 1250 917052724 917052737
    0x206161b0321050702030d0c0210050910080a0b03012408061e09030d2f090102120d14090f01051803180d081204050d0c15090c170d090f0501 62
    0x40b41c405601480c00c0640d1038902d06141001c0342500041c2c02e001c04482c1c002d0208031a203070300c40114100b150002d07001c12103904141e420701c2080d0700450210071441350f55508003c085d50000708103400b0f0703500400000101070000c011a01044160703600030b514520600340e03540d044660006000d0000a801031040c012071300c0a00d444841294949842c40e0040e040071203c0c007051107a50509801c5110350441d0880005100081d0f200600c03c0b117121444c8045800c0c9103680c00c02000c1001d903000940400584041c1461954540405105200a04070380c4008110f142c2e1352418803810102c0050030006401e00000204029118a02d56a541c091400c08402203900148032690702d100c440318000032000e001601e0381c80d00102c01da480ca4426484844800703105d1000c0000e0005014040211480715166800c00e50001405a10340920410064181c004000d40b0782c0c00c0d2004024440c50440001d10290704441c240c0503262204507281c003501c0841c800014840d07100000c00c1100d412200f01240e0040c2c4a81 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 917055224 1250 917053974 917054003
    0xc060e0625210906080a020405060307081909060212070e09011809080a020a050c0a081b0301020405220506040606050d093003150605030c0d090206161b03 68
    0x5880441c40202580c0a0b40e051550110452040641c1e41d000566542c402a401c2d080090103001e542024208040c9507105000c28030040e240c5904494014640d420b000040d41d85015160540b85110820054035509107402002000840e0300940410703022401c80030020f0340c400c03c04540d08241940150391241c02039004019400600d4030f02c0216170616100451141210b440b60342c0301d5400001440c0050f8040020341d003e02005000c10782e00c0d03081c200e6845920501e480c15190741e0b0f00700c4256084084410f03805400142d40c09604a0300100806030080d100c140300740c08044070011032307085000c00322810000010401e107843e1044000741c03445d549840e400c0c6200c000c0c0040042000810482e00205004074484c03030345ca402100550183c1380d800c0c150040b151426002000c0d0346802003208034940e5020018810035030401c0030307603611540d81040203071100c1025002201070b20000002a4202400048041391881e01c0d41d081b00b14580a01c04035250100f282200005040c1c0e90710000d400151805d07402e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 917056474 1250 917055224 917055277
    0x619060f02120a09030302060f10090c1e0807120b010518061e0a030c141801120203040812060f010e040218090925140105030604180c060e06 62
    0x1001808035003481181e906420380700514826034460f02c04040841d100c94030070810160704000c42a031215015050440c1410b000b0001c0b1006415800751181c0c00b0348640405036018450401805094113000f48455074181480002d4940b010070f0f540700c03002403c00e100e52010801309000b1566103040603955036241a02a607041001e02d405624020340c072140c1004020400c4107070201d01541c0900d40a43c25603581c28094001d011103e140c141003050043d91400200c40030070740800c0e100b88604450725045026455001260313604201b400d00384256101009000c180304806002e8201209150035105007920784104001c1200351540395140081e000080d00440d604154001e030541050741c4402d0155070644000042035550300b00e84515042d840880682811159500d52001c506c1c426040b03008813a003803000c4001c11541c20398059050100010128846844941c000781d1250b401c5108102c0b124004d01d0114a00c442c030f803054030002402e810030341c03903e8900401120382c50300005c1c84654080700b09905 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 917057724 1250 917056474 917056487
    0xb0718060c03120608010509010c0e0d0b0f070c0b070203090a0902041401440115050307050705030d0218280323030a021006060503010f09180204020f070209061906 72
    0x11410f02c9840e000c000601d0b200900603180624410b9002003030019412100070651008280824441c5140382c1020703002c580000c0c5025000713032314688148069a0341210035103044030401c000a24102200b0b003007141455003c00501020442101c0c07140c010f036507500d0300307000f81e0184d8090140342138904212a18558003441c0075000d001c140740300700d5284686051420348034240d0650800646130f02041d032070501c2c4680c00b8141d8050420490884c48034200d18000400d5070000401000620200250b0101804820416110381c07142454040d50f5070124103950700c034507841f403466040c01191000e8a0051122401141d1600140800e18403514180f13580c481440540959a1200020403c9560707500c1d65002480101200140c94000b050122107042407034040301c0c0680c0c4420304002091005014540380743c0c4414086450b224400300740442203903500798290040c050300950262001038030308040b0203000701628401d40201c41107400c95480b4810710013864602030000c0c0c51420b40b4a014000d041c00303403c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 917058974 1250 917057724 917057747
    0x5072c040b0f07021e07090e03040f0515130314010e0f0c0f042726070605091504060c090501080408160503070b0901020717130311060d06030b0718060c03 68
    0x10407505d201d5404040f40d40754001074140100141c100f15410301444041c0c1c0241030200ca000c038020b5140034a03022004c403a4080d9070080c03d01c140400f90f085001d018128060f035190403c000688042c0b42d03502d190000040480181c241c2140d42402d0007142c2450001c5008403c8003105005130a484000004002a41040c0d40415074041e540c1c0001d140c4090180600c0e120041d10f5100500d035010307450402c1b40142d178141d000c0c043d540c1c02e076003110304007502003030b0070345540035484a00481d040d1510b440090400d1500c50390500c01e0001d101c100424807002e90451007000300c0301d071110b00782e00d81c603080111008041160702404c00b04003040030788145209484440e005031300038002e40b820200300740d0700e448450100350b030780a00580d00070900c001808030380030105041c40d0500e61024a090403070410941e845542e0711018002106040481e491a1589800c8944802c1031240070031610740c680c648001c404000380c410301d0018440c800005000c21000030100180c520b1516428124070b45540d04450030034400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 917060224 1250 917058974 917058977
    0x19150806091611011d0102090418170f0405030303090a02010807020c0102060f150604120b2d0601020c0d0b180c18060609060a0c030f2a0f05072c040b0f07 68
    0x1000000c5017000d000320100f0000525000250355010088100008d650000c005000f00000048038080010401d01003900414000740300e807a201c0c00c0728180301c6042e000e01e034003840c0c0601002042001c010300100315041640c1c400d894100c1141c540d09402c0744d49040b0140000e006da407143d8045090510b400d1180c80e4080004070f6400e1004001030049107681e0802e80c03140b001e4900c000d03982e500b0403904030701c0300c0c0d4450110741c88001600341420781c02e041c5a03401c04060141a6418000c24081d901c03d00000d40041d1018200d07008a03013180c40d201d5035044c4100c43e18030f101032240314240e025201c08500c486545400400940500c2c01e100030001c4d805002604140c1d000608202d055010b8032440301a0140350b0300754440c2040400c80c2c1c100a000f0540070a005400c10007104018030982e5180c1141141100041070186451915460030b680c0030402140b01500603c036040001480883c07010303120f5455800c99031200c2031104032401c0c46919103c1520300a009184800024441c011041c144560040c0903 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 917061474 1250 917060224 917060231
    0x70201240b0706051f0f230f211b03010515010e1009120b19111905070206040b040f0e2a07020405100609321915080609161101 56
    0x4120745c038004030386541d20804404090071001c0002c08460000040d0b40c1c580d4400e03401003802d0600c00030351100c80c4404024800e080328503840401c20140416030075007c103620100c942c0106010404125601c5100005200c0c0d801c18000500c0c60660301550810704406844060351684214104410b01d00042802c00c204070915200203540100b4486015207240a142e0580c40d90403c4040000c43d0241c05028030f1410f42800c850030800640c200844440d40e91100d10940f90600a543c01c4409105203d03001e944401d011401285518180300100229003120020244a65580d6900c00864808a13503810510100c030074001740010141e0501d0300d80b40302c00a401c5240940540c0002e086490664244421903e082c10600100d5002003801003d00404034407002d60b48080d0000e6413074640d80c41780c008005c49046844c03113a182c44610014900c0069030703d0440382e480d1690101d41c2403c11200b240d4001a502201080c12410440341e82c0b401010b15040f02842d4512815080d00e0110442501c00b0b000d668 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 917062724 1250 917061474 917061511
    0x20321180703050d08091f050609091b0103110c0102212206090f02090a06090b010203120415110d0b0307060311190203160303050906102103090b03070201240b070605 73
    0xa0069290380c101283d121b00040500702800ac0c010380841c0207000181c140e000078084411a01801a100038550092802041c4c4c1c3e980248046140d00411080703501c1580045035040d00030450818107041c001c61030b400500b9954230542800300003034101c42d030005101c407040b050001045507a01700811050089210307040c00200c13603000c665030307002c2100d0920490707645010600500190380517604006000b44002c5040142d00380142e81030b1070004d0300007015101002012284100c068005040150101c866030351102019102718002e090f14071001d9200b030017044c401143d400d01a1013030f400b101941d00601800c1690340389542c80310003186a415000d61106201451520f0302c0d132407152009034426a0b0120b6141080182c4920745000549800309400c50080d01f8440c03030f01035107186000409050380000f111011400d081e00c000c5d8058001d61254140041081b01c1150150800b440101200cbc00480c0841d0041102c010100d40328020700c2c91108040010f64013141c0b142c0c01c1540c10004c0c007100c180d070a09 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 917063974 1250 917062724 917062753
    0x160c0905330114040b1201151706040b06071a0606190509030a170706060b0f1204080f0d1a150a0509181e0907050f010807020321180703050d0809 64
    0x804c56485807205001c009024400c0421088840d401172040040c001d4011480e108080c011118045d1028105c0d84900c0004520340d0392500890003111010b018140c2e40c07149400c104d4025105800d41c00e1840d03402c080451307840d041c108100c45c0c1c0c41440c0d001544060f0b00c0e441d0100c3d9603500c010307a80c5515129100a81002c140e031004461180007400c0c1c1301075910800781c80c00c0c1054034001d60142100d410203018000d42d484a1108440104c044120001120f40e2140f80c03542d803e0080c1c0216406080c00424400d0004642d54840c04194140b002202c460403d00c10800c80c12440400d640000c0110601900713142070702030b0f0701900ea86000100550800d541c0d40d40801501e180440e80d000c03c00d106544400c14141d50303211001c1e003010043c80035060140c1400c003c20810320101c8880c130704200c07000c0d000a240500c20b0058412011010a9001c410908001c1542012b4000da03407032203140282c290700c080c1e0341000080e900100c0c0e90100c00783c00341c40c403d00410b0b074040200030035a940074090f0642100603407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 917065224 1250 917063974 917063977
    0x1b150609010b07150c0302040503123f0c121f1403101e050601110601050d0204110d0507090504090302072310020304060806060711040b0402160c0905330114 69
    0x2013101d40c6c0050f26170b03107000304041c44d02400c407e010040c48030800c00c0c101500340394140c1c446079400d070840346c10301309001a024461101c580e00d0030b521103000303a500384112558000001c1c0f10f81000d80303110300d01d56220014000941e0505100050036824055000c00008041a0017808407103401015a01260b003280d40c01c000b075880c00701e81c0a841e40650801d8010010f030741e10605821440a2034504050036107110004d50310b48040c0505481251000c40810444da07454100c020b00442d0104603c1d21500800e9500001e00360649400c008100d88440110711420a8802c1900158140d401052a00e242135101d03d540d24417200d103010007000002102c0204d803100e151a5860001960003103940f10320f820002040c5d15000390405102d000700300840000303d4211524101c601404480c000786a040d80d03c0050024490481c1c0c03500205035040124040c801019506070440e100700c403050009136603182c40884806808444c000c01c00c8a0324280581503400d42d402004810410b040c0010260b40c000a004400d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 917066474 1250 917065224 917065241
    0x6050307060302130f06020a03050d0b0604080c03150c160206040305070e010e060102031305011803141f1b08040606030602031312090302030619111b150609010b0715 73
    0x840d0300026a02521110884c03607100801946840c048074509007100203440d500c0188020f0104480880c880a80030350b55413040c81484002494999a10b640b4905162a0403180d94090710900544000c00034542120901500c0b8000313100190386407071410242d010504c82c0c07207101aa0801402d003c08000900200b1032500540503030b044003c01076151080b40e004086000741403604540082c825001c0d0703004a0745059007501c1c0d003400d103408041c1200400744143c0541c6d910103040781112034940a400031012680724601000c147c08207061910040e0600144c400724060702202d000d040c0c0c031402400744a2112250081d10410380070880c5952521110282d801c1540c100b155a803082000740304000700e00944080000036030802070501403441d00002e80318074004080d181c0762502110a0442d0035003981c003103a8803407110748200c4e495200146000303180141030200c04080c4d1280ca03929002c918410700d205489141c1c02040d01485a00300800d041c09600520700031501000e9103051401404064001c0405 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 917067724 1250 917066474 917066477
    0x12a030b03150f18060a0e0a02030d030c03110412020d020d120e0109120b0c030a090b0108030a030621110111150a06230621040b0402031501080c040504060605030706 73
    0x800b410140d4840d50000b40c080c052040241420b4130302c22805a001c162a988030299090000700c6000c6200054184441d48030025814021070b005081555003552000981329105d54082002c0180300c07941c41d10611980c026003040e01c01e184143c03c01480c014042c81072941c8060000c141c401c1e007135a90800c05009660349180841d1404c22001c225580c0000300c88000d0030302e0b000311000c9644903110a4286180030304282c00b10f0400100003580103089801443c02541d10030544016984e40d000c20b00e803603800c040740c60310002c2d003020000070311021490084d000031401c04c8603902c0c0709031071a910361a007428690001414003641d5040d102d1003460030b006086460300526202c24803071400c62000002c40d2407542046016503983c12480e151454100c1142010000c190b8066968001c1200b101803140e0801d4803003000030190a0402040000c0d803281103015902c00d5081710b03815240b40a1080004034240a4120359500c2408000b0345840c080d007101d500580a000002226501d8401090038403080750003900 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 917068974 1250 917067724 917067763
    0xa020313030803061804030503040b0c09030d030b0f04062d0905190c03020310060806130c0507050f07120809150d020c150705040513020d0218040e012a030b03 70
    0x1e040c200016213512105c51000d0000c07440c90030390340c00750213404003400203000e0343c1038000020b1040c9899021160422002012a5030030841030070014003800303207268080e002d400c0700000e20106c1c2c10540900700c16a1004100c0300315090740b045a44000200b007203262030100c43c14200002d92101ca91040502035140035042004541c1d00d51001800ea44c45a10380d02d003018410020004141c400c48042020380c1c0c4207150980007038841c44001104201c81c038070b00480a0380340841140b20180c0200c000d00c1d40600c22010348616604504160751201c205104d061406585003003c0b40000745402c00400060200402c00e002e2072070880740d04c06c1c1d55002540c040f29103c0d800100082d0b045820031401029400b4800f400c440d920307041100074507a01542c420035014515076040010050001e405681c13038903049400454035844141218221501305d041d42c1070045162030307140400482c041c09000c0b401c0c8a125022140c040e40014602803003811954000c1c2090b5841604080c10759040c0010303450307a0180251003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 917070224 1250 917068974 917068981
    0x109230a080a052b24050d06020f0a0c050f030a020d0f03020d0e1b0906061e07062406111e0a0f0f110907021b150c06040302010c110307080a020313030803 68
    0x40202c800c00300030140101840c6000c5c001c1140c0490b94902554810303902c244d0381c01480d103840806030003105030f80000c095021038042009948800c441c0c2000b03020740104c0e510a90700602150302c0384150078026006801c5442e02d101544d010740213030420107d991070014540050104544122400c20b5075010003600001d40c581004860358008010030318007201d40810a05200001841034424917010038492503610701c0101440300700c681a5070340350380c018000307016207a0b03c05013004c0c10052038100310b007000081180100c2ea841c4528100403a103141d84006120421000640455001c8149005c00e500e10580ca03510b13000441e00480000d8280c42400c7c0d10420041916040ca20488500b203228040ca070040300300940c0941c0010401150351484070003c44c0c611803600803407c2c1850007a196804541c0008a08400140c006001e0340301d113002e0360003000400d1684404a0b030309800c1c5541146c1552090080d02c0105840038014443ea005034011a1718010301944000810076003039006135480c00f400b02c00c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 917071474 1250 917070224 917070307
    0x1e031107050301020f1923030103120c0f0212010e030c0106090b0910030b040213091a0601080c04030212030c0d1d0103051b2a0109230a080a05 63
    0x11005030004400070340c108490030b0a0641d0ba0300030b10120b110070380c480b04280f0034080c1c021500c181d081f08803400309030714000c0303c010304584561080c44101e800a0a50014401003442a00c1e04101241d100303100c0c41c000700d9541c0812000b850340d030301200c109540e10000c9114000c02000184654480b250006c2005481c02c0185401ca130010103c450082040300104502c5a901961003010350b6485150141a6141d600205100c0b000440c05051b00900c2c294107641409202100d0b1071041014280e0b01c40250b0740c1301c0044960740825030341c200c800d01d002c2c041840145080102d60840803810f02c105c130b0801c00c031004100c3c5031040d00a000000310700510041c030a05041d0300010064039800782814045401d20f10399840c0e1180100142e0140200c0224501d8041900300120111084001c844040650030820a0b54001c1507111021500c2c1400c20840c10740d46901c00f01d003003a2424940001c0c1035020312030340f602542980400000020030a003040300308caa5251007480060295003198011160801c034825 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 917072724 1250 917071474 917071483
    0xb04020c070e1806220501050147091315050310061203120f05040606051002060f0402010c020a0803030708040b0106020316060c030902060412061803090e041e0311 72
    0x44201e003180c00c1400c0520307010024111713400c004d08200120850050071100400e091454200500a5017031400004000850300d0384440081d4001100045407030302d000f46103a100c820b0130782081030350500441c030101e0951540060011044058000e508503001400f9540858007214400300d5404042041400241410005480060510700301000f5060809a0b0b02400300131a075030080c2040341c0c29040d8841c0f00040e0f041503003540c13281e000070300440c01c182c9402000f40c500e42c010700340214010039030300040301e100160490103511500548a0952103603001100c24284150702640c0280d030000300059524000c2005500c601d00303542d2410210b0078240b911540f005010b92142e8219401480a0b0905903105a507078107103103602040005404004130700a8018003400b07000079611641c0440c000540d04100540c4010191207140108401404880458816900301301c001c0c0028036040400c0c0101d1020214041d0800e001d41201901c0020109829640032042e40301100010400b0300e03110380c1c0003030800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 917073974 1250 917072724 917072731
    0x4050604050c01020d09180603080307080403110c1c05030415050a26070c0516030c0f08120318100c12060b190513080d0f08060406050a0302090a0b04020c070e 70
    0x4c00b500c91000b070b2840040c10541140601c080c0e07030f5805070034855400b060354860030085500c0301503951240f6040b24051700703e41080320150045180c0001285d01108040b880142c0c11a008022082860455007001c0c003083e110101120a88410040440c074040c120380c50a040240a5503055034030820031500400f000ca25030442d1010b1030040000040e280d036001d50190380107034180380021485415040c094500030002076041110084107070301106120071804d07800240c420008250b40003680d14881d00740e494021a042c521114401d101156075012a0b0a8004c2e04030304a504407024507066221250460341c01102e4080440c10444520704602210300914000f018407440b401e040803640c882c1c400500c0105000d4004000000803440c1e44405480c0711b17000501039403011542000000d82000e009034000000d4640841c001c000061030529090003980705032900a000c0360700d200e195a0130311a0030700c40640136500f0030743c1b00e00c60380d113813905c17140b01429195060100401c440f80c9009145282d03d43c014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 917075224 1250 917073974 917073977
    0x301080d0e0a0e0727060215100503030306011409040f0906050901060b1b010e03040605030f010e010b0406030c02210310061713050307120509150a0804080a0e03030304050604050c01 80
    0x110081001048015403d584007425040210605c1c44199041d4446061088005da40c040703100700201c0e085600042071a4000203140303149010391200002d05c101010345108565040d84100006a0103501c18262449007507844440d507810250b01100040a840d07000180700e0b85d46584075044000d100060045540005031038008001342c0e4140404450301e03100381c0da000340d0303000202450060000c9007507000c2c0340085d81070015240c6450311010020010752003034602075007031269a000810300003900400d1034100d0f100507018610b028600b817000d9010740410001035017075018200c0e40142c2824512401c810032003408941c2a5a4a0719103010000c0c24020340040041050888003d812078044d0030410b600b00110042c90b10241078185441032541c46101001007034480c0140300001304d150000042c02c1d00341400c450030340e000b1030206560072542c06582c0d500c03c005803a490200b40400c0c1210001d01249000349042c1c8210303401c0304003191079940b00b0380b411251a407090040100b4000280308050f00751009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 917076474 1250 917075224 917075239
    0x50a0f1d070e09070906080307140f0607200d020c0a1a0409091103030c030408070b0304030c151112091e030a080915041a09070605041202060409020301080d0e 70
    0x81080c650344403000d01a69558100500118120800810000000f0300c43c403841030202c281c61704d25958407a0000001180d0a03906074075060340070342012804802500d40351009181994a107030048808510181d074074143d0405111000c2803c40d000d0204009000c0317941c00401008582100f0b0147c000c920343c0c844046900b201007200e004808078402c03038048844250012032004070384d04151030014040850036a040c07000180401030010040082c04c02c45c0c41c0001501c00c00d0703a440b00d40d004680b20132680100041c81c0c800003c400584a0032a66800c03a0208000044241d036041520005070300c154021441c0c1c05420b01041400b81e000c0245101000c5050b0488d0072644040c5400d550300e004017000c103001e008030b0340d0000d01181010002c0310120013102a140e2028100741c1091183d100341075000d503502500c3d00d00000d80c070030400504902119070340ea035079a1816103424203083d540d0705200e00483c0d00901c10040011001c034a0300180d80a8020000074120400e0070580182059404d060040d016210 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 917077724 1250 917076474 917076521
    0x12010209060f1305090708090705010806060a03051008030a09080c040e150406140a09030e011706010f1e09050a090c080a0902010c02040e010b03011116030e0112050a0f 74
    0xc8220030303940e44036000e41e189038540c0c00401031540f444425400c0700760484041c070100310704150302003425401030038441e058920701e61300c4600444020a049079007a4020038100043c006461280d0301030307079100c42e44030390707210103513454624841c01e503400180107200003150144244800031041c01000d44903202214100210080380c61b00e181c898040301803007241307002c41c4c000003402d00001707420401c048101141d40280a144c0300405500910803680c064000448048140099500402c0c5003096100000d220f168070f81e0341d1b4001100c18018039601e00d070810a00c44400741500039110442d0b40c3d62201503d803007600d10300340814054806119403001c200c4608018802c50940d8210b844180c0200043e01c020880600600050755a0301010704000d40044c50050f0b00f801001045d4040080320000310020b0200d41c8080705071781c899018103c00c07440c00421040520000038043c50052400310410704112401d510038011080c00c84034102d4045184507282c140b40ea2140c0d40500c1624407007440010707800e82801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 917078974 1250 917077724 917077729
    0x905010e130311010203010f1d0f0604020a090b0c060108010c02210906070812040c0906230d08030703050f0a06150c08160c05120a0f060c09030f1112010209 69
    0x3409070403464450035164812080c148203010808820081c98001d44d500d5950310300c07503422401c01d4420348003032946c545900340c4000200104540604910b0728401e101f80c5408042000035409980e0010038413100c4803001601181c400d014280c6066400081c00310356140110b41404d540c1c40b400100219007103148400700c008009103d003070200350b62009480d207945015011a00d288140d032070180c408900416000300d07400740c400940c0d11a1384100141000d6a40d2214140103480e460f0041d00c44802d00c0e044030031403142101c0c40004034960000c1080b40455096103e80003c0d51054403020002611780302080100c0b102d1000240e004207503603404228181c6003059400c90702540824603c100300494400c4010300151100b600c054802280046d90031154510b04058555124400d0340d02581d4035500802c04940085000c004003a0401c0d4031035540503003503030350000420f122194841400691200800416201c580f00c0812074800c03001041402c0e14802000704620042c064a059680104241c01868 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 917080224 1250 917078974 917078999
    0x13060e0a05011d15241908090a030e1816030612120e0117090c09010f0e070c1e0803040618120c0302030c06070207051003050402010c110f04091b090501 67
    0x1032048100c62141420103400a0006802c013070100a2111440300562050319180b0006c0a0401004603103034070020742c1110550b5952401c9a80003041e40240d46044007080c01b50502840000004004030341c0f0b0b8644c0c0d045004028410f45005100c20248215a040e55406d0710511018111a8201e0400c0c5246651215070002e48988040104003803440c010718a42d0149150395510300308100311140510308441e281d5503134065401540e02c910690000014803e1f40c030f94005055440c0c0d0045103001c1d50701d031142540c5400c80b68108945900e140380301d4800300005028599540c9100d02c03e0642e82e81890308100301600e41c0d5800355019200c1911212001611f0001d040300c801380c0e103081c4215541c90504059003103000d0104c103182a4001e050800002d07503800314450702540c20450b80082106202603048003198801c6500a011541202c1407001146600c0c030003444240c2c0040014402001400c080350070340b0102c0c8012119020084408102d030100b400140f030143c89102002c0019603d402000e8070300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 917081474 1250 917080224 917080231
    0x40f12050f040b16170a020c090f07050a1b0302010f061e090f02120f0906010b07080405040b0406050d060b0a0506070f080304140618060a060b031513060e0a05011d 72
    0x4403c0016416001265614000c00b01a0700b0400c1011210003000d01c0c029035900150050f03005004030203000d035862414680c40c9000341c2d2201358003800c6a48a20043c1d031207521002c0b0010a0152480c0107403016180203041685451080d4001b15400300204e0040080d5a0907070451400351400141000086001180c040101c6418100114404000c0c64002c40284204104039003544280790401401e145119070041c007440c001c0c0c013120710981c3c0c2c07030060055602503810b00500306c4c641040100124038281d0001510024020800194195240002600981e11900032561141c8030a403080c11454400e440070000c000075692180750040999912000c04c03034985005081c140701101240c280000e0b131b1030034000ca01c02401140c007603091600c420311819000f894040c007248030321000034005c2d507214007134a022030341001c0c0e84600f9912040703001248206072001040e013006c200769001d4469006809600d006016840c400c411609000c3c0310307031050b150160440d20802001044002d40032107140b119590 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 917082724 1250 917081474 917081489
    0x50115020c0d111e100201050919150c03050a0b0a060e010311070b0106020604140a1a130c09060504150501020307081c020d050a0e0a080a0f05040e040f12050f04 71
    0x104a20300074454000c41010242c000384409584c681802640601010f107660854440c80c503050700303040481c00e8800868140c5115000003443d07502c9200962990002c00303100d4122240321007008000c0c0c00498008100e00c000280e1500184039200f2580c0c46106500349060b19404005402c01001608c01000c8c20101130403d90360780c65507950310000009481d50958040c01c0c00405507940d0713000940d2100709403000e0b00c020310303c020600403207100000d51002540e4000740903030303c5086003158001602d000a0090704074016452030f050010f6030b417140020141c090441d0010b000c1e4104014041201c07100e80b84101e04e036042d690280056a0000151400180c0c030402280d540d5600610207010510b4010b082c1d401035001244200c07141c030f070a4104610420342c0d000d08020718140a00c1d4143c0d113024a40014228071010803c1545143c4910910121034040d814850f1819542319079008114004a030251002c524112040d000c002d85400702013040d92480c64840d060042003c2207450f2441140308010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 917083974 1250 917082724 917082739
    0xf0d021e010908030708070317100311030c03010516020c0604230d1415091906150807080304060f080f24060d06030605070912260a0909050115020c 65
    0x40c603845454110064800441030340c0e2219403615110820350016181100800c001141c0302c502503407806e00b080d01c21a680c441e5031846d00d03c0c58440401c0c099400b001b150301170141400c0600c03261000d0013610702aa121003010781c0000c00842000303041444010700540308600803c010810161300c8000d4407000510b2503008125592400d0000740c000036582d20050840c03940e0706044141c0d04001c1512035681001c101411817980e030301585c1e00c3d10350344500c0032040c01016582c1000301051055000c001c03407920200c03410361103588842e205441c0c07540582c1b04010031307400002d00340701d031551041900c0e01500c00c50800390002d00300240c0b900c2900341c009200c00502c40340341d00240249006080024516440a0000c69070383c0803900b01c9201414550000342c0d2284d090101180b140c0e845503a10a04580701c0c40d80381d04001c1801e980780d070041c03d201d03c40d0280d120b50481c2c0300c25030700210500502c0c1e1246952152000d403450160790000703440050f40070600d1100c2c580c0b000005180c01180d9980450403c58407403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 917085224 1250 917083974 917084029
    0x21203010314210406030f090f0b10090204080304150e1e03071701151e0504051329010f150302070c080708030a03140103230f060705090f0d02 63
    0x1480d080e0701e14209440800f0319071600581142160040c4161401e0341e406000c0c601180c02c441d001e840c1603881c02403035040c400001c030001c50a40031000d0340064040a4203840c0031754900500040e85c10540040140d50000a01088007500300d14090702c4201d00d90408401121098000071803200010321032005003a901d0111324450340e0705015001c064244801345803108c1c8140030000f4024000d4000000304900c003040d0102e692950000c092140c2e42c8403c41c0b02420034141014000586005000c10041661171801c00c400614401007101f0020300c8030190f4140f220001424400f52013060f840940322b06d01a40c414044058a01106111200503043c0540d4403252032516508980840e2320212940c042d00b100800e41200200040c1000e40050f40d0138070400c44042602c100221080c84010001c0d4a00307140d495000b42400c0d13071a0303540c1e00e075034050302c15403070b82c0701d41c2c040c20301d0800c1302d102d03000410000d070f00c07042c0385000074451494130070a503404a0000440c2d4007180200a83c4141200f60a081c81c084 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 917086330 1106 917085224 917085263
    0xc0615060215090d0c260a1b0807081c0501081c0e0604060f02030403081813090213051f03050a0c060518150403060509061005010212030103 62
    0x113030035110b99052050301c2c03008548008445110852030307034003022150155602e00c100041c00c2d44964984201c5030050048080c149850184401d1440c050081419002554801640148419a90564101010110148503140854103400c040000c10307801e802143d00117160980034145065500c40c3d07001540e00d4402503602e1030700018240030800c50644a904101b680000d24015240b405403291500c1415500c0018082c12006400e98000900d0801020346083c000c44904c040107618010340c00917003040069452981c20756200c0703010455680c01c9203000d00451101740e8040c0b200c103540c2d03e0a140c1303880c3c900d5070940b5080300003100000c009004000700c4035007d00104052034100200d5041040d02d1305d1500029030080340c02e12003c00042c107d48941070203910700340014505850813400b84402100380ea0041d0713045400c02000152030038921425281542da000091051746801c2d00766 = true := by decide +kernel

theorem cover : BRFrame.Cov 916906474 917086330 := by
  have h0 := BRFrame.cov_init 916906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 916906474 ≤ n) (h2 : n < 917086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
