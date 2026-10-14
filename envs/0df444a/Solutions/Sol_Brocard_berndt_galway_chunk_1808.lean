-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1808
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:45:10.533561+00:00
-- url     : https://prove2.me/submissions/980852c9-c1a7-4173-b713-d3f9741ce87f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 325000000 ≤ n < 325179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 325001250 1250 325000000 325000021
    0x1b0f060a2303010f0f05151b070905040804051804031202070201050c01060602160f08030922111c051e07021c0c030816022104050a080106050405010e10090b0f06070308 74
    0x55000381f80560a0b04480400102d51b142c05e80c5d04840c4400c200312902036400d2512410260241d1241040c14102420301040000120180080e00c0040d107464010760040d074081c5032118400e83d0060b002c90341c5c0d013117818601210350b0020844a8018107007240380042d408111803c680320380e0701c1000180c022103c0080c0c0b5412895504001708500c2c0715030f11525003041c108649034400d505072203200c1c550755020028101d031072452203152520785100030000d101c04154841c200e03031b0000e50f4594044120421040074903100e4855940134082d02c240300480c44804c803020781c14107000076080105502c02d100d01b50341145464545041400515911880c12806510b0050260b5038003070308950360081c00240d070101e020341c0080c1c001031a1041141e003020020444616180c00c0c4150f1f0040c4d0f4000c0310007803020032504da0541112040b5002560204000e81ea0b405001c1c860f00070079034140f00b0302c1c42542020850994603812103002c0481c02841141003c40801c0080c1a03580301c1c500480100d5002c004201c00c1499 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 325002500 1250 325001250 325001279
    0xf0306091407030b07050a030e06070207050310060803030a0b30060f1302090414030f04080706020304060504230409140f0613080d020403050304081b0f060a2303010f 73
    0x9041c4001c081c141d0540e5140a07030500c0c01030a030341c03c100380401c2c13804085100e50403100340640c0c09001d55109081c2000c0080d1110031601805020344200c08000b415079005100c0c40701116601006141552035100c1558013900001d85c031340b03610035503d0302408000380d8048510144580341600b000c1806180b10b800030300b090f600a105410704000d030800c21030000072a840c0303288082d034100c0c6d20000a648901d000d5542d90f54408100803103201c0411120f480c07041c1030b00208256103003801220714180c0d0760700c001c0f80d40348114020400050002d110402c035551100082c00110540d5690401d20f800501c5d01040c2103500b685010303610340d13500344034043c0c00e004203002550050023030344050700c2c180c80c20048070304410099400c01004a20001400104442d055041c1c1e00510342c004196541e550b0303141d1130296907559416151400c0540884a960685403015800c0c00c4810058999814400840e00035201e941e080f01d60210072450f02b8902600071143c40c80210702034040fa00340264900d0034403003c0c401d40303074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 325003750 1250 325002500 325002533
    0x20d09080307030f030e070e1f0f0b09010c050c04090809040c0e010806010f020a0206191b110103090f211202070b011202011704031709150105010311040f030609 71
    0x1c1041155001003a404070030b1000300106414042052a4810041450400d250f4010802941c4281c14808282d00c000c4843c035544040c0c0f5803510910391036000741c034000400c0e841045c1d403000c001c01244031154000c2c0c4d50100c031075000d0400c2e100d1401040c0c004c20180c421922044441030310014882115190501c180040c1142a05d813403101010b1200002c4d150200141006051100c181082000075100b003008045855010700100d85036000c4540d4072004e0403844040d107000c1081e030180c50240c14400b60307041d850642c01c00049140d041c410300c0150003c0c0707000481512482020806180403c51515440602c0d488855002c02c180ca103107100241113002c44050000001d004005982c0440c6511354840e0540d07401c1040405001a584016078840041d1417100701d03000aa03604201c14540c0100e8184507844039581c0700410f40c1c0c1c035140500d03241d0781914480311220003150018000c0d07510a500c41c91070307100e0210040785841d4580c0003102c0c041d0f03a03d0b48101d950391745550103a010400c2e442d80c40c03000b60 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 325005000 1250 325003750 325003753
    0x506040c0f0909020c0120090406080609060a02030403122f090a170312100305070e010506071202120d0501051c020a031401021303120207080d050d051312020d0908 72
    0x981c5015401400764101c1c1c8500d481c1940c001c140c6001801003944100c01103280c2140c00c95006605604031a030b140c001103207480c421484c00341e001035421401300340b481c803507090040034180c44e070b03600301000c002500040d10943c100648500400c4004109120381c2c203040c06400390104051100750003c2c2d0810b8800750100403880c005129000790394076241060380c143e404202411404580080c0d59070310b0350140074403d024800e290700034860808080c1100505807406141a983ea0607102c034140c10005034280705040d00100c003081030101088140071801e07401e1640780b0654040300d0b4402e80d841d0054100940c850940395450b8010040342c0780ca03071500c182503041700740e1889920346c0a40024503505803a110240c00040180d008440801c0294100c4182600301403003d1b240c10f441e400c0c0b56540d03082c0c01407464058401c0010205d02d0000015006200407c2da0759070514101303241c645080030f48405030201515410300c80146e000140c03c2c1f140c0d11500700441d4010314010000c0e11008000e00b9090b40000d505 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 325006250 1250 325005000 325005017
    0xb1b010b01020a06020d0b090c031f0b030601080a0608030c0708070801150b0d060b070b04021309020303041e050a031a01060504030804030209040f0b04120324140d05010f0506040c 79
    0x90390b008203035101041c0c0c101100507152075101210301c0241c0700002d42e82d07500c0f03a80320081000c82c0c6590405075010300142c482c1c042000e001090000c0c0b14522078040c4803c500003c1c80000c2440d1f115001d40d560110210300c011403280e60f600070300d43c610340024420f1801504242020f00a501c0108020740051014400070711580b80072041e40c44015800c2c1c01100369251001520340e500c4865a00040000c000d206c0480759140cdd0181006182010280ca04078468071105200c5001e40c9624020b0b440c1c0c850b001005945801d14001c85007081000a4821402d0620388500c0005c0986d903048000d001903000300790f146034441c41c00c4402850080c058003c4001c0c000d00740024004034001c0816942600c0e41035540040c0d503151400e201407039901041004240000040c204010010400103c1d5651262340d1014450304055212413054000714a601145c02400c40301c0c00c01141100c1410319a44100180c1b035a03040440a844407800e48120031859064180c030380d0103010742c1d4185846140841e001e0762802090 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 325007500 1250 325006250 325006271
    0x80a1d06040b0a021c030903090e10050f01020106030803181507142b0e1b030613060e0d18050603010b03070c110a08060f0612100213050405010b1b01 66
    0x314001c81c0203000c2c21403008a08540c125000b0851400c28000d0383e076010880480841008000e000951011000030741101c1380050342104402035640240480811007004604000a006a40081c00041c60456403600c60000120b0806401540900c4c1d035146000d003d400e07020040d900e012001c0d41861142c100c4842006440b60703003d02d031200302804d00441d00365203003010101d4072907481ea0003c8015220740800c0c41c03074140c94200d50081007c1460740080c0d440c0007014207540301078081c441506c941c05820000c0003031030305031180e1004103440b842444001803403018114042e00d080b080d54124000b081a00e4070406510036142d0b0010020301c1f08807602441c6605040a02101d03010141049082c02040c01c20f24041000000c2c003d402034101804460040e5643c0c001142c5e1940280d82c0f6080b80411400031982505228038903104142031b05000303000b9080d0f082c1d2500c00961000a1003450b0811080021600d0f50320390041c0b6000341900d61000b80c44045241078504841220040e2081d45d0785000100071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 325008750 1250 325007500 325007509
    0xc040501140307180b031509311a01090b100f030506010207032123041e08011d060708040302061302150d05010f060c080d0e010f0603080a1d 62
    0x5218070324140710280c0700d4445034410b4444441c0f242c255022284084004521000b14201652080e200741e00241050301c94902881040d0809079004c00362441101d80781400c08060f000b07035101514810030700601000e295266580e030703c18801d07415500c0b4184c0c03200401c112641030040302490034040703038000502c1701030300d0018103130500c048404400d06464000107001607000b803020100a40d00a02403001d07500c01d00c007084403150036900403100411101742ca03090400034024413482000c0454903035545040e003450f03100310740d528000340c0100c2510401507020503d19070a0040e00f0b0a0346042030701c1c1c0c2003040642e000e2030030910020203070020030410104001c0070a40c00200036030040c40c056165190311209002040283c00d00005070000c1550008440400350311582c0418121075840301c06a10303c0c1d0319607900310b811ba03e009070054100b1f08103202c452004c541c298007444a80e90144000544044d800d0001400d6800d07a500c26101c444011441030101600648803070204685220721020f04000080050f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 325010000 1250 325008750 325008767
    0xc1a0705160201021906021e0f07031b14060142020f0102040807061106190f06050d050703020415050904060c03061706091b03030702010e0307120b0405060c040501 72
    0x441c24281c03200c0d020302964002d001e140c541c00d09615040110380e1050401c50b0183d803041703090600340762021a8103001500d4200603034a000300000c25142c44c00c50291422603c901002c04008640050b444986000a443d64989a0108004009407040798941044003403494a080b0781d07044c1018080101030004503440b800d140e030704194400c21410340310320103a0807850015892007150441d840000d02003080440021840100c0d080d50f680c800c1c145040e545629100c01040d00c5001da03149845080303034aaa61b040e0008540c02110380000240b8994440000741801d440100656036900140c0c418415810540a944004854030340c0c03408405140402103804490020400392400782c0c1c6800d080034251007908044020180c2044480c3c1c0903800d42c40d100d84a0006440320070302841100c104460700102c4120002c400302c80100a1814140583c0065810b0170001d030f0381d240d141c014403201080420b040d1080001c042e0152034000080d00e0545130151404801502250b40c810041c001044a81ea010382003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 325011250 1250 325010000 325010017
    0xf06040612152c0f030c06070c0218160906050c0309040515040204181410031b0f090603021207050f06071a15090f011a130f060c1a0705 60
    0x52000d2080b4001100e00810380c04400c103d0004a00080c01030b0b100405540b920060401070684209120f001c80d41540ca01c034000305600d0903001380000851050144100002ea6400540000301e62105d502112000e00b6080307608400980c00c1150024416a000c50090b0140c42e03207042c40d500d018141e501c4075589000e1281c07003d1189032035400003140810038010001602c0d0f00a0015501c40d0740703541400e1010051400141c40203440c001008801855040030540200c1e61708001c0b444032400c546981c2e10707d49080280c1c078481401500002540308140c1d10180040c071540800003001e90a5104010b00095040341e80c0300c455104890501c481c0d9509100c900e400076007101c1c01599850140340556600305403141d0b464011750410104802e4071460381e82d9a10b801d07011211410160b40301070140c0c10100b400c1c01010710101807482d48204295041000706200c1500704406c0c0700c510780d0f0b0809010030710356603000100000c0d24400c8210401c032034284110010550491005214034001c403000f0f116000f031140c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 325012500 1250 325011250 325011263
    0x1a07090501021b01031506050a1403010f1208071208190501081c02100203040309062c0108060103090f0c030204230403050706060302040f05160c0221011d01050f06040612 75
    0x2d000f0540e0b000f5442910a0011182c1c800e100641c0d4400c040d015400c00f80340e40700851400307402c1b0340c02c40603031030200c0307050b81c081039500d212007810074000300c3d0044a469811122a48208041408141130080c488029a0f0a94600205282020482d0ba9002c2070106241c016410f00c00140074558002c2040d000c011b091089810002203800801c0f46410340309660681e2040c4000300703210926501c10042000c2d103680c0d4490614134140000c1070004500da001ea1070940d24918459a110ba41c031505c401c5800940501d0003003888210760b00c0d1304090516052088640181002d801c00440c1403078000c6010000c01401c0c070100e0106c090151520780840140002d0410000080070800c11189074880b901454026000f003284002c854454001401c06540c01200039882030004900944140c940ba04525405020f07414042e00922a00c4419021030040444039502c1c0d1406004400d155412030b03040069440000c14182049213070500c000d100074204a0040d81400c0040c0301c44d442888401e101c5613030015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 325013750 1250 325012500 325012543
    0x81b06062b110d0c0f1406040e0a0c0e0301110706140603062a04060c020f1c060e07030b09060f06040507090b0c010f020301080708070b072d0f1a0709050102 69
    0x700700240c01c080c010305540207400003140d000b81c5c0d4504442a0380401c00810009490001007080c00d000b580319081d60f040c0e04900184280780e1540100c0001d4480d810604201190380c00004d00390f4252440b200800c8401154000500605004910702c1036200135007022a07090170700110343c446c600100100104a4450030003000c048641c0c500c4e100041104411316195a00c1e90f10007000c0300010f4805a1003040e02d1141c1009a2070008a108100e00c01d141c3d80120200035540d41e900609114903c09049028403280000071a4108904610400703031f03140542014a0158120803070f0b0f4001401031809545071030200305203641c100340e185040d142981d18240d1900c1580c50000d000d130000c050915503640c004000015070140001d520400e8609100c2500c007040e0301d4000703034034807402030440180c0380c1c1400b11347c18040c2c110724061741002e8629000300e80116845076100d00b400c1406540c2c08440d04d502071025950a40410341240d90042011315120000d20302d000c00007507813440e42400c5040c001080e035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 325015000 1250 325013750 325013783
    0xa020705090f0105011b02030a0c0e0f09030301090c05070b0901060608090d0f1d12100c0302031005010f0203040e070503010302090a050402010c06151206021e040f03030c081b06062b 80
    0x1b080305001107038001d0848401640c14070705185003040ca4880c0076520082c500c003184c035030301541c010f01d40701d00c030080021425a07107003406210141490400a6082c42070402495000c0b0b00722810b03c074420007846001041891400800600245005081c1d10443e00654100701e000c0303a0025562f0495529860403850510410481d20346203540011600e900a60401c010144001c01040d642c0070003915510820515400d0942541688002c45040c400580e28810900096005100355500030b405d40c41200e040580307461106540c0d2100340c412200dc1180800100111b280c001465a84001c5c5000300f4081804c0070342c006418840b000d034000b01240e4983c8034401c0d14040c01080d25004002c0511a080807044c82c1c24008029440128159501300044032402c00c003030403903c102d07001c9030484a0580499031035614108c0e90500045c3e01120f0250b02044151401d100030303680314102c1214040904502d040010801002003000c03070200d540e0015081503980c0107580482c1d90aa550303003041c1601d42e4403145 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 325016250 1250 325015000 325015037
    0x15060c0a0803041707060b0310090209010308071704081b040b010206040f060b030a030e040f06030203120d1515030b01020c150708040302030a12030e0a02150a02100e030a020705090f010501 83
    0x10080c4c44008202c0403030044c0c14415540c1020800f1101642581c07101d60b0740c08683d1050391504440650011000c3c0c004000013807000000301515401200041d005466181001c840d96110358003440c02c66100b40c2524012070300d0442021050707078048908015004040e40081e450303900060001e40811103c2600c1d07c00c1c0007403500254110364006090324024181d41c50f000d42583e41c40705999004625102e407980d109401031040c4401d4a8000b001840d0807240001d8a0289500c21540741c00120b44960318003070008505010480600400400c000c4c804102002c01400c442c1c5121500c1e0456001200b140342546500506032020380b2400481903607030030f103070810600c58891544000e42500c50b8103030340c00600c610300340c400d01441480e44d0103004841d8000c1d2029070361094918040d50050018440500c140d1000004100502d0a401a22200f80400595a0441c2d40c1d6981ea01c40f40e0b040003d0765407085505104400142c40c00311165101410171685050304540140101418082c0c00108400b00c041c0717 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 325017500 1250 325016250 325016273
    0x1030504030e060a020304030b0f061c05010e0715022b030e0a050d08091c020606040e0a1205040611030403050c040b060d0219110c13050c090301090b15060c0a080304 73
    0x4040c14080e80d1301120f0344000d58a500034070050b1480410300c404114110002d01010703004100c004d00188402945003d104d17002c0d81c00c020101c40e80d40d0f0b030310b010601840c0140880001004008940b2442544041c0c004e410407078083e404030001003454405100c1d03042c108049810003e0f00b8500040c154203c41d01151520994960242c40d03445008090b00c2120781c0034a445201d40c5401080c1ca40603542c0d821462030481c1c440b0701e02005038101400250702401d1075401142029112411680c0f01c16141e214030300310001001c03100c1c0010704001030a00069800100a031003402440c8001c5240c1751a5855554503498264411071040781c80d0780c0780310007507a0fa60065500c01051641e0455484024000102660f01204520004030f000b446040d02c1d0a4800b00c0c61403004a4050038480c8050301c0c4203203040c0100001064504100c4080c001140c41e0b4800b44602c43c01c481c80f9007003100c45030600c40c1c40e00c4800d11010760307000d21801080100e0b003084000421001c21b03803540600002d81701c1d1580c0c07400d580c030f915 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 325018750 1250 325017500 325017527
    0x207030f140c060903030a1503050307031404050607060504050106080c2101060e071e0305060112111b0109060e0d02120f07240b24090613030c320103050403 69
    0x200f900300344031003e48044015070145100c90340400c220140d404942c8000c03000c52101820320b800500414002c24000c00444404010350b807140c0c0c5c82c1544070400035003542c0181c5402e60f04155504d0400040000911a450107065904010710030705907540c00054049060003052107000d450b50440380c8182c3c0342504501c000c2d00c5610381d41042e52404000c010413001c088520305082e100b1101403280a13070b01a100302c138041c140607550740e41d2180200302e0b810013a040c24104000b11300e030104003480035003003210500d0241502003000885c1a03c81ca0904006450519180c0e107443d40124014468450b0001000e0700e040052045440c0c903000c6a04240003030380035064003d808020498030380e00408005044200c8000c21034402004220301c00411710600208414980e06084244c40d200e12803044a40003a180c50000200040e142c03d1110105c1c0300d0621655104886c240b02c00c1c0301c117002c0e10454020a00120f4202c2104500072884204001003060034014100d05040c0d450b004075042c18403800683e406030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 325020000 1250 325018750 325018753
    0x90a050301180506010603050c04030201050a0903170904110c15090a02130c08090a05120d09060603050f07060c080306040e0a0203012a02011a040b060c010e1506040207030f140c 78
    0x82c42d00c244045101500c07a44112000e0003408000704e00c090091003114003031040c0c0924241040d0031a801502c85521100010052002a5000000050300410071001113900030415544075140002880107580601090341070210090103500014100025090380c03203800e0802d10a000e03240c1802490802010400280d04007000c0d8010941c14892500610080b014554500c9091b580e103000c410386803500000014011341041c00d51000e400406000340180d0b0b404010000b9034a925a0780c1c04003250040d030b208803903d4101c14810030703481209201d088024032860502408284455603101daa030712004001c0f030300ca10765407595042110f03000c0040010300b40c0d000d8020170040320400c960580c1000848002c02c0000c800b25000026071f841801090610340e40d080c0c10b08010f5a5003030410002d48110914150800010300c1601c400c40000d00800a158004070060508203220303150542d60081d0050100b0b000742c0c0100100b0300003aa0045c0c18014110207807a10722903280030301c085003a561180c01c903464850b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 325021250 1250 325020000 325020011
    0xa021504080613030906110607050c1216170406050913020d0c020a17070b0a0c0e19051e090604051b070606050f0102010c0f08060a0b0301080c1e1005090a050301 71
    0x1440c5443d040d140010301031313180c10066980d00c040840c0c4403c4072660050b107641262000c10b0035980200007900f0002249010f43d0010941c00a5004080c1c010ba4101d10760420340c03a01500910440d507940091800c0f18074100c0c3e103010b04020000d8a94403a201c09a8007900c0e07151203035031507200c40d50b060b24850720840d00f0900000a00401c001c0d642c090601080d41d440c1a01c002c0726906200d07100c12503060319801840006c86503900580b910003000e250040300280b0500650f00705095542c3c080d240018030512411450f128102001d210740c80170440c6100110140500381e84c4500d40c0d07168141a4010b90889011403640e0380c1d1166218035542e00151080c2483c004a4100d04003c1c2c80d4025005441c001d40f1001c004100c440012403d03280305859031004199810074100409200c1c05100303501c548040e10a402c16541d4481455090f4001d81c4200300d203410058103042645041c1d1802c0206051402803c5c90603008000080c0b10152216941d0060280004542e10691a880124001010014000c011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 325022500 1250 325021250 325021261
    0x807270b09090906011406090d0203030a050307110118330f051308041208040503071419082a060403030305041509110607050f07150216080a0215040806 67
    0xd00e0300312403901482455a84005141c3e00000a02281202c40303264185409602c480248015548003080094000348000c0700040940c07000c000234120400150f0f1440d035240390880004000b8000801e100d2516410700b4204400b8900b664521850300350440840c05088044603040c1402e1a00f2806801301a1661200300e00c0c90640e0f548060f5600c40000e90a1106a5600060258083c24458004d00440b020b000600071403103840ca0709011640b15000341d41c5040d44410010b403806409600c4882103c1c21000a0740807401d2241c221030400380301740c0e0121a083c0c101040715072105000001b1061801051010740102440c0030100e80170303148080c0000d0340d507648034203004002d8181103c00b900c05113100dc00c20009400503100700d800300d9400807400b80c00e400c024020050702c0e80c44680c0680b014032515030a601c811a040c002640104a500429000c25006240103410204c81504641c050305c0000c02c00c010707030600072a20850440d81150313400c040201200144481c0d000e981c01180751845500c04111 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 325023750 1250 325022500 325022519
    0x2010f120e010b0111010b28090f0605100507020310050606070611090a060c0803010b030a09080a0e010806010201092a0b1c185607050a080727 63
    0x4440340b4003a0707117016040c600d414000742078443c29090715800280049500340408080700c40004000000d00c100ca0a841c2e50310000300980c0c00100c0b02e0050940d4a200411851a2210714001c0a400c00c1c00c5c544d060450b16000240c980071040c20709020349888000080b060368582084031304840c0e02a804024156281c004061250804405c1e580954071700400440c3c00c80c00b4240c10642070380d2041207580f039030303003080302c041101d41001e46071290490f244c5a1650026048a019000b00d0450750389041500340140c000418074a03010b03100c507055916100040340810788003c3c03e0744507417140400189940c080702e403c810501b070341a80308070341c50340011801007583e5180c488021044041800b05008407c20f00000f00c1f40050b030b01030b0003801165444441815500e0090a2100c0030500d0301c5108100c0d0b61094100b02d0a031600d8043c1c082e502540e503120001c49003411041900f2204524015080c109c00075000f0300301010141c44d46e01446965050750604082e100180ca41b003405541001060381d80d10204030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 325025000 1250 325023750 325023761
    0xc0311030d06230d1502040906080a02040605010807170c070203030c1b04020a1205060d06111c020703080c0f0c0111030a140c03070e030c04020703080414010b0d02010f120e01 77
    0x60f0940700209010040941092070b80d104888002010080024080d1380c640d805c80003044101840580c00340000035403a042441004000d09010000d01040c01151041004580b1180c12442c140700d030340d105200c4420b900c805180d44e80490b0b202d41d8151625046070f84019805003440007503161200040c900d04010b0301141c030080c0c52002c1c80c3c1c0e401c90f0301c000ca400c0105900a409018000079400381c8000507002e41c0340c2100d500400d01900c00c000302c140341d840d094180c60000c825130304125800540f98244401d107400e5090000740e04e02c411800d0034500d540041824001514000b80c03480c0114124041110b044120741760140d000c0001c014a070681d0841d0030040d0021a84820000d02d881507140c0c40c80c000c4443c279031144d81d02c8800d851556440110580d01a448280819003510038036111310025103962009004007070080d1200d8002d860940780280c642d80c2e500100074610f9041c080480c580740c40b00c0e8400c0f03840325424246004140c2d0340756401c5a10508480250a5590810030184124201035005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 325026250 1250 325025000 325025009
    0x209090f0f0c0303190e1207060f03090c0501050a1206090501360e07030204020706050a0522172a010c1701030f0503120106030501050f0913030c0311030d06 69
    0x6607504440060203031516581c00d4071440b50540c100f0420030039540000344680c0d01141c180e0805606410031000031032400030a40e00301000d540c0c000340f42840815004003030700080f01e21926007071000041d1591901d5100420707100d1941840004124842030900511610f0b00410420074204070326a6161000030140c0020301c80c0303c90301e86885d58a00d004950b00c0500d9203000d100c0c1d1071004050258400070200401c0c110f13024415900803250080016901e600003002d1460081c04042040c2c1400518141201c8003d85200150404c0c3d114100d04552506494030340650401c0070300300c00320b04609404642d0702c07450714a02d00392140e09800f003c0140d03001d44550419000341c4020440104500c009031622640089004e4801208800410005004a00c0a40503174450000c1d241411002c0c1e90500c86000281c11060100e42c4510051015052407482d8020f800e40440d0b01c2c440c5402c108203080da42c0d154004000e810004c948612406260180800b903a500300f055007100d60303801803001c9682c000c250314001c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 325027500 1250 325026250 325026253
    0x439030507050a08150111121201140a030803040312020307020a0b060402090f0f0a0314100c2c030a1509150504030203030f040c0807060e010f03050c030c07030207030209090f 77
    0x8920081e10440c1a01c03c031082d0340d100c00d40d168850240705030110500b940c210303041002c58220030001a03410700001c00703503490000c880c0e602d554410105444c5440160000761050754490415112542c450340050116508100000d949442c0c60808a41094410b0b152002d8940004280316005900040a840541c058090b85c495a2110010402648a8006c2899100100c0b1160003803a1528131502c2da20404000e00410440340e91b035690300c03541c01149020700226006a580d040c6c030b44a49008440d6038041e1480c016001c0440c00c100d002150012001040100d0040400404e9903107080201c170300300603004061400030b4400e0702c02d21800b400081804a8400140a0046c0e503100c01074010700e230141703a06801450a650301d21003031f1518604002c005803090f0f050040c0000301c3ca841886014050441640c8031983c03100400000b5082c0410700541c0303002c2500e094200902d501c985020340390031610120910b83ea0baa5142800c03860710300c40d0341000e0f51100703000080c08100040002e203401242e10000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 325028750 1250 325027500 325027511
    0x40f081b03120c0c100905030d020109030210020a03020c06010e0a150305060a022805042c0402011125050a05100509190312020f060901020a050405043903 68
    0x100001280400c0010240e0180c1c44000211001d44584024205440c14030003100c0d003a5110740001a0a030088095240204514800a0181d800d0038042070300c50302c0b0540005e03c54801c4664000303544941124120b0310380c0d0390214844004a05ca42c04a5481d0303c00e60b000c8400551f101c50041e400801e094806854192804444110780d0004c20351800460341c20030007809013075841081e5100650320048070481c0204099950510b08800300384a8003c48402c2d603545500da0b41030000103d01616103107190301e01c3c410825216040c1a9902202c4d603406542840c04400c800416112a407403c0b8030300240700480c08442070300b11020100c60300344008858013241c201c02c003607544505210580401080c0c610000304c0030015144c244c20004000030902c1c0e410010482c0c0c140d42da84580180881d0200600010380210241e512803207010000b254002114200071850410100000f42c054130443c460079010b5a190441c10800da4041902c5610160f0000200080d141c0b5015440200da0028040400440e2404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 325030000 1250 325028750 325028773
    0xc0102160e011503020f0309070302040f0e0d1211040e0a0c09050102070b090a05040f14060a0f0501030e0309041d2a0607050c0621011e0b030714040f08 67
    0x100ca411120040038844181c1d003007192003110b059600d20301c50140740e000c0080814102501c00114800c20348040a00040c9086104020945400181e00170025051021488600402165518a070105400c0802c0618070040e00e000c040c01603d5400d00009402090004001c22000081c0c0e10840b6001c03800c20a0002c03940d0195800c10b814042c090042e8400001803025802d42030040c810050024034040c0c000c0c0d41c810015064038030368002d44ca102074403a4402c504040080c520f15812400459010302101c2c14440d54504e0419141b06035410140ca854200d0300c00344044c401c07210b280f5400750040c0710000c011000e8400d0301c071840324510202c1c418882c0c10740c54854441c081c2c50055891641c80700c10361201c0c03010400c05d50423440302540c0c68001c0c0501e6802558424008206203082104403804201d80051460907413801607000384001801030116603803500d00315841c2411740741104005074482c1c80d154402c8440200340d1b220881200c000046c0412252005e00000040345e80c43c4c403ca42070f41c02038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 325031250 1250 325030000 325030033
    0x70c110303130e040515010906061e0e130e07030309030b010611030403030c0311060415180b070309140d0527030d05090f061b1c0215070e0607050c0102 67
    0x70040500d00c0500b2000042c40002100b80d0481c0c0c21500130811038003c2e00c50030b65504410002a803041c5603869503448100001b5402c85200d01e141c40540742040c081e8529004003400c88564100501d00c21000c0311406040542d240d484083d109803d00c0c00c07109090b03109e150191400519001c180c138286201c0000280c0d5610609815078450b10001c040c508007461644c0540d1009404c4904405000004081c218085800c108a42c0700342d00540070502905171001d285411503514441c00b0703a0260701400e201c000700794140107c0340c100c0d0542c600010201c6140c18861401070000050402c0b07400f9110300c050401e50302001403c0450544200c41001c5003004040c1c111900d108602160103410400300d080c0d0f0340703009001509841c0c0b0040c120300c5401d481d03840004d156070700c00b40003907104507810071548000d04001c00c00648a041d00c7c1c0c1040380405ea00d800080d50781c015403070194408036141d40008010350320800c00001d02d11b070003811060702c605607450700640f43d060b409071070f90061042c0486400303030101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 325032500 1250 325031250 325031257
    0x721020a08063f10060f090902030303040809240304020f2b06020c030705030d05012705060d20090f0606120903040b070803040b011e050405061206070c110303 70
    0xa000e04003507070b4003010700c03402c4240f510302d4803040f901401c8480600d5800c0105002001a20001d0740000030300c40d0421210390700807a2a90000443e0034908014003005031000003c0f00d401035008455143c84031003000006d070070045212800751800070708070410f0304022202030103140030b14400c4483e906100000e0b0301b1b00c04680400e40d00c4918011241180c4c42e00f00d11444182580c00e4000d103c00740c9481d004485a80c0743d07034000da00031a45035100041e400b5810805201d403501509080f20560040300d18a1156410743d0001030300240215959808a10a41e880b13940c0000c0f90340d403241d0f401940c40d80380702c11194060319003841c00340030704401d400141c042c00303890b44d5492080800505160a00b00282c555414061000f40303030340355a100070880860206503030000b60500e40d103d00d266644d06d00d0180b412414425069000c4460038195810506080781458566400d40e0341c2914005525503400c000a00c0412400c000300001c0c0c003600702400401944007080141c01800782640c60981c2c1101d00c01d0694a20 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 325033750 1250 325032500 325032529
    0x10902060d150e07090348030b01030b01080d080103021c050c06191e0e30030a031415010e0102100c050405010311130e0721020a0806 59
    0x2810851422000750a9001102014140e81e51848158840c00302c00c400d0042512444049610203808100b08048244021600c0c02c4016503d0002c01072010500c01e050ba02c041d04555403000541078003d1202841b501c0801160890200605541c0d40d06000341c0694080c01756003d940150340040190341c0c05250880e0481e50301412052100b4000c503039981c000d858880e41124540941000044070781d4819010b44600001c00344c0000040602c5e901c00350401811007145907940e081001c084c560b4607007041e54043e10319015203005031000131300c0700300341c48101403200480c0341903440301d05000c0042400000382c07104c0500e91714208045140c520b42d64190300411035080d45140c0c1d100140a406521035000000380c003106004a44055030380c848603905941c0f08000d82c0d0300145000c902048150380c5409010065242c0c544114a1326038206400941c0d840c0b00e000d124180d2400201160038240b0a0250b06180484901d00e40766071502110603d0181d441803ca000000d206200802c84900d00158120000e2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 325035000 1250 325033750 325033759
    0x304210e06160b0c090405070207080d0804060209090403021b01090b1b03070b0705070317010302090f1005150306040f0e0604030804060b040501060e030d05041a0705010603021206040c08010902 85
    0x1003580e000c000032039002031032100d0020b0075001d5030000600d50740361082c0920b10a501881d11a1008420301045030802080e0004660000a08002080c004100c0c1665002c451402c00e1040d90340c0e0401c000688206800b00c1d0304598000d0030401032690106003400e0308021a0842a10030310400011241380c51280103143c00d10408011303085914640d89440141c498081e0203072410408030361511802038008035580c6000c1440050b000c01010f6000048210b0f054425680401035410f540100c0d21a00f0010300302501d4181c0da0000c500304070b001c400044001d09004051146601c40945210304c241c000760742aa0141d81495035a444421035400b590200d6100440140303c035a80c0d68800b100c00e0440540150f40003981d81c0c008403039640f1180074490281030746481d480008040042071501d03202c03101481600f0050f00340814495050600600e040d00400d07104040d4690000e03090050052041e984020b500c5034100084001c8400f0129042d84a503000e2141c0081c241e60344c1004c1801c0e9003503030303100941c030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 325036250 1250 325035000 325035017
    0x203060307060e0d0209010f080601092a09150c06140402060702091308030a02030601021009031209170304050c0913020108070c06021902010b1329120d05030421 71
    0x20742e44543d242d445000780c018000b0b9101980d54000c645004e000382c01200303401c1c44800043c0130a1104000160040000700c40c2001004044614462f0120141d1802d002c82010303281c960740305601c1480c0b0400036241e208500640d5829012001c1c00300c2c0c20545088a800c1c3c1002140c54049502d402280e06c9160060801481c01040790f0070400c803d17200a110805c04202ea400392008500484041d500c0380e0000080160342e410414006071524180c4041a800310342000b41400000e91f012200c8007c065004d00f0216160340a881d140f071810401c3c004080ba140b0300072081100b4400d0006600310303080381c26150501c02d5150000060a404003440020303020800031004604003c0c4684015840b07103000d208018201030b003004120041e1007040300500f006070b448203451802854540c0712600d00c1704214000700f00250f510019501800301603007070fa00001c50791310301c01c40c0305480c0c0c1e520082c0e441c2c10901c01c0c0d52500904440c06821900103a40c20703642011000401240362040c1c0c0c070480c07040003040d180d2000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 325037500 1250 325036250 325036259
    0x504110108040c080708010213150903230313060e0907050a0f030b030f070305060c04140907110f06040c05040c082a0418051003020d15270201120203060307 69
    0x4070900c01074001c0300c1d031072060400010500e00500007800900140d000140c2d0307502001881240c2c04800b600100c0240500350b054010031a0401e44901c102c81c1d00c107003015454494184240001501110402024007000442c0544000c0e48121381c8140c85a5807503030f000b5816103606100c1070020840da22000300f44100000d40b450b601948210710411007601d40841c0003a01c181c013103030802c1c1d60050440c2d01640320f804103000700241404510341c05061640e20754182440c00144641d1403000d212114003074403886c40415195442030413921005858075040b203603a4a010f6807907943e0307440d00302e0303099401c131a0105000c107052800707002d0105d1003400c6d59605400c90f114064240303c071840b15a03403d00d00c0c50070238a030306400c22048005800240840030704c2d503248601c405c035603405464005100381034800c245081800169141d40b00c48036015041100103003148000030b42c6030001c2c1801d1003080300c0d0031001141145141d03400710000403050b00c00c1e664000b070f1400c2c6443c400306a00064505940c543c004d000c0c10b11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 325038750 1250 325037500 325037507
    0x6091207030c020d02060f031005010f0906180515040306050a021215031615080a06060804081e07141603051209031002031003050706050a0203091509090a1b0305041101 74
    0x181543d000608001695450380c1c00a4443c2d4003051078088101000b008115032100ca00408400402003800c0c20a82e034410304100921400701401803001340039000341e25000c0c2e80040c5c0014006003030b010300044c04004001e824040e16410501c001c6522906043c00940090740e5070003980e060001c00c0d05004944c0c5c644100f11048100700f4641950148103020724400b4817001280c2e020020480b40b007520228420100e402001003800030002c06501d820101c04100c1c041e0700944007503006400010441d00c9000348400c0070010902940c940d402203602050440a220481074800700000030081141ca4442003040d2231340002400d4800a006a04034006c001406c420840007030040c04001001d6440148089641400303c1e0400e49840c0c0c0c50034020b00e024020031a041041c00050441350800c01d080c5252031600075502d2055942c0180150940000359049401d2142680c0801030000c125201c285898045040144141c00c60000070080c1b110390302034a80e000c2d2082901860308541d03d800e5020321a801034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 325040000 1250 325038750 325038767
    0xe010f03030806041a1513060e100f050d1119080f070807020a020d0b01050906060c0709090f06090b0703050604330e0903040303020607050c0613060e07030f050609120703 75
    0x11200305c100c03002130850741c0d13480310380000c8598a0750303420390740b02e500341d02c01c132410702c400c0380c20403820311101d5075801c011a55400d0442045101c0c42c5007492500d80d40d000111000c5c000c0d014510085e03410606418500c140003400340490240d031a8160000d850030b9031040350300380419509508a40c401c0d5001c00d901602ca8a010f07544090180126094000c0c1540032030800008a003064541060050040c0001c1c0b8000c9000f64001500319030a41c1050b00886101f625040f6a11807101c00e29958000d15040100c0700c03400648164210004214034405410710110300b031011240d000c0041e01d0400000c89a107481d101c1c0e02c2900611405d4581400190240c007401c07400d042a03895405096031900080c100c001154452040301004080c0d921030f891441c01a00e400005040e9030b0501c0070038420311143c00070004d0203552000324120680c2031020507003400401007060900c0089207004980001c4140700f0300741d2252481c5841030049824550300c8101180d100d041e0745409401d15113041151b01d01081c03251084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 325041250 1250 325040000 325040021
    0x30b030304050d0605090d050306060316020a060c03020a0e0618091807060f0e060304030e130e010c05180a0501020a03050c01020f04090c120501030327050603010801060e010f0303080604 82
    0x4907032400391035000080c4540d105070b200701c0320507440d41c08005007800144080c4421800c01d080150030b41c1400d0740080e06a0000030117000c108070800d11070309491442000440c1c0c00d107400410402c039540005030002d003c0d50140025a0102c0c40e80070211809007010b600301d5100207610840312195084c00c80400c01505406000001c0620061022940c0d502090110100910351780c1c8034800c803400c00c0039000e4000e038014005a1f20804c07041c002c1202003908583c051841e4101294000e29015980c0e82d1803008040b00c000416580d0300c0c2031200c0007420742007002008003605480d2050003c6044d81c0170000f54180b64082c0d42c1c0181c02c07019003140001d00640250854580369000941002c103003510002c51500183e001c03586aa440f00d8254801d07c0d0010110a41513807000e01c240305030740c10344d03d010b864001102c00c84000f00d22602041c03a290f42e0203400034009000f000b00384c0307983c0b941d4402d20507000c1d1480e030141401b207519070000010b420050081a50880741c1c03603214107400d0380c2d41508120003424000c48 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 325042500 1250 325041250 325041253
    0xb090126010e030d0905100506060a0c05030705150907091a0907020a0b040b0105130e0606060d02040e01030b090d1b060c030e0307210201060b030c070302010e0a03020106030506100510030b03 84
    0x16215050b5006101034804031520007000241d0718404e080c5079151880d00242c181c103003803a00c3c0074041c2c0c80c0c94400440300010700d90308082006034a03901d400d600d0b5200390740c0007826038011001b06244c118071003042540900e0040e001c8031030702602c40c04404101e031031800400c6851040d40702c480120381025000700e82d000c1c0090042d24001017040e110050384460440341251a11924801031200e03152640d00d02c038035101001070410403100c1e20322049603a440060916446035001088a603420101a0102c0c0c010302142c0141854659403803401c4c00e0703001401d84201e0007c0c024100800b40ca07501c9404403034456003035840c0700d001b00c04050f11014000c0030030001a104140e201c043c102c2420804100a00040388288451008004000c1035510400c4ca07001102c811641410300800110000105480e0080c44488a40d0b5070340d1800c0c0307820fa00419807095610701c54002c90350183c0c145074042d4851b00450b406141621480d696400c4000d504580c5801040e90083c0741041d90041c0380c0c03203070384200314030000a070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 325043750 1250 325042500 325042511
    0xb090f041508061e1605070b270309040507020f15130c06021c21020309031201032f0109030605040c0b160201110303060604150512040c05040b09012601 67
    0x110440d0070403204983c0c000d0083d944507010a40140b420b04003c5e4400707103804034140b8090f6030b160700400a21031451302038024121100814001d908100458006144000021840d03504c0c00c1e0702c07591a500301c40301c028410b91400c3c00181d459800443c4948030040c6050107005216841000389141d540041c03c0021114000c03006800081c02840460010700440e40081c40700b901000c00082280342124800801c01c500728000092401d1103030f00d0311400750740c3c820002d0307201d07503820300c00602d90302a0081c0348401d03c407210000021720840c009800100b40040e103401b100b0120700707940c1c1088035400740411400a0b06084081000c076080e6071009411074401d08013100c89a65034080800141c016441e0400e25014444d18102150b81144401d0058444072024505518003200064010702562184880501030000081380e0700d0712400c04c84d8814003000c4102c1c98203003860708140003a24282d02a1074050f9190440501291401425541c12650315280320408080c54048698110810303000441e0b0039902c0340d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 325045000 1250 325043750 325043759
    0x5030c060319180210030e030d0b0d060204030b06010909201c060b0d0c03140c0a050f040609030c0902030402091609050312070501060f030302030d15120b01030204060b090f0415 78
    0xc0c050840f201111681004106090340104420a000a5051818145442c0c0400c13022900401592004503604200080e6070070003001148100d404100028026480010003000f084111a45180500d0b000ea0340c100c11a80c8481c104412150030010403000a0240d0142c40e58080d110002024040b80c6820050030181c0004150b0040e600c003600540c136004004a01d082840c000c034030600300040c07040d00d01480140c21400803405090b50151210444a4000130101002ca010306c08071080304c4100000c81d030f41c69030303202c100800100c0d140c00200d403219000080000c80300c005000386c9004607002015a1102c4c0c031a00304901464602c0999030301442440d2500107181d55080c4200d46410584498041e41d0b001d152428a007101d4468100c09880c1c1c410702d00a0000ca41d000050baa006c5101c60800100944402100305c2458a2903014106007406501541c041003d541e8040d07040342d00c203580a20842d5180e4003002658050140c8294102500810100440c9019000760a107003408610f25035029880c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 325046250 1250 325045000 325045051
    0x2060d0e060a0b011d09060d05010219030204060239040b0604060201020705010f0504210e0406060c1101031107020607020d020d030807140a0507030509130c210605030c0603 76
    0x444004110707640d075207942d02c0e071075800002c17014640c50707034100c51820030b003080c4002222018042c2c2018050f1082090382c10400500754104d518800150740079810540f4000340c014041e40c454040c500040c0190030412404000450f0300000da04424051400100200d48504d110241468902e41d84140c40304559202d6484410040005d8a030980c005039460f102c0d42010f5080d608020300000d80180b900080001241c0842c0102d1080700c134a511000301c905024004a4111b001440a5544107103040c00c001b84094201e03450303200e0944504558580d000c0117800641c00c94500720054101c455003004118018a00706004008180c4014a61003555010381c010804000030f0040c00c401003240c54080c4506a0741202048600b201c0e0644041c1c68800401001403603402500d00090a00c2404140b8240e5565400c1000c5442d0b0000b03e0108510507c202004050801400c4101010108050800b081d001d65028940c1601d4001d00144601e2140d00180142640020415120f0071140b64810004404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 325047500 1250 325046250 325046263
    0x3020304030e04330305030405060f130e0f10050901051201020403120507050f0106081b1f020106090e030c1504020303070b01080601090606020a02090402100905191401020f030702060d0e 82
    0x29443d03007080760700b8405030710000d0640d1180c0c0d1303c14403d107401004000003400002150142c42c001c0d80c810b40c0320701d003021003900e490040c07815100e11032440300c4011039081007150906120710802c50400996071600590884240c0c500d00602d034000d22102e00501c61824141044201003810300c00043c50326513030703480f90300c81c0c1c000303200b804c800281000540d1b00610000700807803044000c820000b08036541c9490b41c40707a59202080349446061080f0400c60400f685c46035580c2d081070000f91042452170b042500024001d01140c003030003481c58030305a03148100305000020b481480c401c2000900080022880d0600b00282c000c0c0120b0b4184420421040000d2a80341d46500030000701c801404d442d4100196070741503404582128007190301069403200940d8901c1c0180d44c0042d01030724040c140300311200301100c9401060b00300d241c001c21446925412440240000c10444032003040e0314406038481d0700121303260b07030010801d40d00303079032061025402600c3e10b4802041000c0041d00002100706101c450b89042c2203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 325048750 1250 325047500 325047521
    0x2030d1407090503070b030402040f1805010506031606020c04090503040b131505120f1504020a0c050601140a03060c030f06080606040b041512140105011e0801020f030703020304030e04 81
    0x500340c9090050454100541d1006000d04034083d1030300c0d9080600e6031029000042c4040d20580d2506243e05403080164000a610003070b00146200724100d82c1440c80c0a82016202d850191049074440c0004041c0041c0001c140c41c0385d83e0192800d20800700800002d4504681d0954150108000000320040070304014027902003104068a000c9240030900888414548130401c1400820450301660301c0d070b40040c0507400350040c840e00303169031100007107107906040100425802610000301007940f0794101080d03134401132050040701c080d03a0f290050b1200e02650741341c6841c1c012507030754414030006030b1030f822071030407001d4510300010019406400381e0140c40c5a944080140c0c1c000c0c1c82444245c0c1020b004446510001740c405003e00002da06910150a50b24411400c60100841d0840c3c100103220780c1d4060f07400030980c0240065611105121580147c940d91030403070540c1c00c8000a900a4113000707035070309000d5012450342141c0d0340c0041030b0045d51000f0412400c1015041a50050341d4441c8160140007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 325050000 1250 325048750 325048781
    0x42f0409020a1d07030c021204170c0301060b04031103030c120a0309080a0306170105070e100201150f170a08090f03150f06133614010c0e040902030a030f02030d 71
    0x606210401401b181c0c20080140c003103411110364001450246401c4804554134080741c0000d1115400309030b070900344c0e600c00070799055090650018404030900c000d4020380f0b000c0c0540c940005a0202095a00d10aa01c0e0961482d080a04a041190105009000d048502d400c0c04590404207584125079503106607800d0002c2541e50781c050200c40c607644030300070001c031501000300080c0c00c0c210300c003600740c0b5100c1d5945403082080c1e5030000c034103900c00c1d04140350304050341c000300c003106440e034010422600c0b4034011706007074100041d00b400b01000d001070200103598000c00000e203040210024003660620301c85c0e07890f40600c07d000100c01c5008808a80c40d1107400501d02480350b070f00b0a54100940340894030307160744d03110b410b107a50a844008000806040e02c2c9125a0341400c22031247c410083c5a01c0a4001410303a4060421030290503006401c07000da04405030340c4000d1004500e10400044030003206004e505544003079021400240a0740d485c0c400c404141c01181d00380701d800b01495044e156104c5500d03050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 325051250 1250 325050000 325050059
    0x10e150102012313140d08160c0221060c0a0e01020a080403021903080a090312050f1b250509100b030a0c030e19020a0605030f0c131706042f0409020a 66
    0x3442d03400f4560a0300034613000201c050300c508d8082e0090070007202c45030107889a00700140480d60010078840d13003411710324a00182c03100c1d46000b0448150b07580009064070041540081e46032400d61003c0f60b11001240c3c091510380c00c00e41180c0a003c0f07440100c00d094100340102110101c08900220040c000b900c850b0756500c20414194070b04001d41852015401090100500c11800340d4100201035508840d45002c02c0e0700e84290b040c8913113250265800b40030404e410036068000252810095903000c0d02d0007941c0518031034a0702c150040c115402e900c60a012000c090001c02c100c140b80c0e401506404009160110314581c0100141d401c040048408030480743c6020118011030401e807081c00300600440c1009400c501d0800c4111541c0500141040c003004000540c20520701e12101000c3e02504d010100300c82c9a6401040d1555500300685051301c94540c0e0041800c542c401f510302e141c1a113012003522802203243d00381404090071031401c00b06e03405601c205010500d802140c00b4503020301d20741c0c1602c841 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 325052500 1250 325051250 325051273
    0x307020a140406050618060310120305070506090a03050d0903021f021c0b010e010f02210c01050a092409050111030402091501090513020d05010e15010201231314 71
    0x100c032400d5200724005c29090001e280f0380304034500088441c500903280c09580c2e94549500c0e12458410b5007210300c001c03034810b20f07039010b240e4400b01800b13046201d001101e15946803d990140e4860304000028009402040340341440c2c005601b01540b41c0e41710b40101c070a009406410300403c011503854030a090b5901107408030700240035240c907a0900c1c01400c0c0c100944104503000921501e410304083e4140405440c00c401d01500c01c0001d001882220341614002801c0d20100c00581c1c1c1c04284c030342c2c40560900000c19241d84540c03007402034555010380c02d854180e01018080c00682e0004c0c190b01c030f07100d656040080100317800f8003c0c0c000c40c21041107a2a0344e4505841041701d610805001519030b082c1c0d03022941c0b00d9980110994082d64000c50341030506504400c0d03540064441c0521a0807418240400011f004c04441007180c080c207400714144104080c0400120308a81610382150b46034403070f562880314a8130132005241c1d08601a08050128034025495032094040386e00001e030666806601d241e070703 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 325053750 1250 325052500 325052509
    0xd0b0a080f011802060f130b18122b0207050301021303061401120b0408070501090609020a0b12060603070c02060708040501030506040e0318120d02300d020c0307020a14 74
    0x140d0f00d042d40364181d424896000302d060f60240540c10341c811000001d55200018503800132500502030400b0441e510060b16020200480b50079400b07a0080000000302200100c000c00c000d030305920400012500d405c8006159030700e0625030000a0294007c4402c0407480351020b00050030051400f5013110071081c03561801004036110201c5019090704111b0051080020326125410300b150018182c80081d165400d040794284100074004110b90b20b0070240e00700b013081503080035603c0c038003c56840c902d43d42d0f0b43c001010749100e818146601c810300e00d00080d07400d1921501940e0054010321303281706807803450b07400314441c2d51064500390755074500070404200a42c0d140c003459622510580f41400300d822030b10441a03882c010b8132030070f2070401140d00a503802a22001c1e041082e140c086401c0f1450800e0740407010b0744401c40c6502e054880a500745120611500744404603141000c2601c0d107070303d01060b010840c802034100d2130440340f1a006c02c121180160799940ca030300000e0b2104040d0004001220001c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 325055000 1250 325053750 325053761
    0x30c0a1103120f130e090d0201050f070c290903190302040303050a030c0c08040f08010506060403053a0801170a02100309150c050712110604080d0b0a080f01 69
    0x49120b076000d400200c9605030000251810382004040254a0724103410080009400b0394004042003c043d004010403003000040c000781720880d03034000f04145c0e1900408809481d070101d501e030004c261000288c8000074102890004441000800c051408401c00e109503003406007030f604190544d03c0411580d030b0700790281846601c0070076142400c600e041d2031660060900d001b0000c00038149135440170a00c6009018042202c0015840b4407615034550f11703488240351880c114041c2c00f000390318000008006040004c1200c080d203400c00010503109038404034030018945903580d441240c066031082421000480050080805800e07140ca03d01d940c14005406020262200d00c580c042d03000c4030101c009a190044805c80038003061801064000c0340f818400120681c0b80384c420320b00b07454900981e100c40d522401501c100d501c5005807010529128000301c1d4140c03182c4202145640280000c5400102c101c0010400840710880104500d11070200240000c0d11941c011003003900007218040f45a40b003807244 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 325056250 1250 325055000 325055033
    0x302030d020f070b0c0a0f0b24090103230307050a02092401030c09030b09010609110a020d030504020f1e040f2901030902030703030e040506010503042a08030c0a 71
    0x1480c05070390002110380e5621803403040c10600500000e40340f217400028410221019000f58140700710350041d00d800e0511079000ca0f10946204100036a92003030700043c0030a000c2400f03008207091566400c685a4440c00c00c0d9590038000303070070252220f10303110550900240490a0140c0b001e4403800290f8010301c00c51200080c42c0c98604484d15031040801c1503490b000f00c40100c2c0038078000812070305207101030f29141c0c2c0c281c002900010648003001042601500450140c0d14096814043c83d1000b0340030800e81e006500b444005a000303159115560362190380603e80c0300340010030060468210401142e100318205500e005100c0d42c5840c09201343c2010300811207100c030868000c20007203106140e200d0710015000c0e505c000c0c201c10a2841c2403207a109800c40b11105ea00201665040da58274074026000840c4c000c0c26900890030400013030342a44c01407003603030310654012401e003c3c01e44480301c04c5c5109080041d680001c07681a5007003c10340c11410805045c00800d0f80000300070682d92070403d540c00007009440c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 325057500 1250 325056250 325056253
    0x50601050901120515061c180b0c070807080301030b06040c111f0e0f0304030c12020a0302040b12030f090a0f0b1207050c0d0e011806090b090d020315010302030d02 72
    0x91001c060b68012002c00c0204440c1d0b00c0014180c80701258407981c203c900e139880781c5c015801311342e1031507072002c205400b0828088030200708581c05043c007020390b055100388800780c108214640000e540111381d00091540501c00c040c5145402d003d6a10300c01503410a805c142c40301e40c0140108000d6050501c1a003042042c030b414454586031803080c4050381d60300714440210300c1c8000f1610180210b02c45070402410012207505131845100400101ea64982141c8400d50758507100303000019620000050b1104020703000303010418154159000e0201412240c6401c5403c4100f0f000c0783d4088032003d0000d000c0d0710740b950700c180d940e80b03d4503c00c002c05a00a5080070501074842e400800018113038900b201c41420381c092401e0103d603903160301514180a02080c1002500400d00c0d10000c07170f41d210035410309542c0240c071020300040c2445005464900c0602903030380403841c0d090091081000d180007038403800b50002c150000d030b06c500303a010900f05091a50504076035019000148110703c3c0a1001c100c0d4401540f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 325058750 1250 325057500 325057507
    0x120501081b010512011410050315060313021002030901090503010e0d0c0c0801181a07081503010609151703030f040201081503030c0609071e03080c0a0c0f0905060105 73
    0x200c2040d1035400007104001e01e01405900144141d01070016a00910f4510144105541e510183c0005141c10903285174420a03801000b00c110b180544160b90296020742c0101200c12244c809000d80c544c00509a4507080c0360901c11440181d4407007808000d203001c10780c041e60315164080000b409911403900428440d9052004410781501c2c005540302c256510707480c24011803807031402d019640041a400c01c4c0c4140d400c200d624000381200e15040e006152003a6201204903220f0114004202c00550740080011108001f0032001d40712014405c5902800600010300305544000090485081504000400502000c100041c40790080d0145091300c001000c0e618600e04802c1c480c08498004200030b040c85400e00125500c0c8001510b01a6103010140c1203e940d00548000fa5035a100121000c8030680305040012071010b01e411188090845040300c0c0307944040c159552110150080c0d50400c0c140d00c26008403401288030141e5500081c90441501e480060070403e000c0c1c144d9400818440c184103080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 325060000 1250 325058750 325058759
    0x50f01230c07020613090203070206070302210c2215020a0309061103040306050a1a01140904020c0f010603081914030a020309010603080a021e060106020703140106150f120501 77
    0xa000d940c001560450725a803240c0d50710014000340200490417105600341c150100d8031080980c0214040c0459408888440c0d842130012030681c403074502260550007002c40035298000040e84c3d196013084941d0386a60a0800034080c01c40b2042c1c014010342010448984104104e001e000046403103a0890301c0074014280301901c0180c140d880d0f42c0308035000c204041c00c406030040000c0c0280c602443e40207000740401d042c02185100545800904402d900d0312030b4114030b0b02580a051110000000a0900c80c24086010204030080d001080103002601982030440da01c19428491007024520441481d51107101c10301610304040034404220080c005656061000c21008070141e991106c11003030090394039500c091405014000319440202017120103d08158225008a46011a912180d5403682c408170920003241e9071300020b200d00720141e000031000384040f0349040e9503903a00003220700000c680c8582c1d401c0040d28a00e4420503400009401300b42e0110f0469001550400742940001e0034021541030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 325061250 1250 325060000 325060061
    0x150703091a040b010506071506060306051207050a1e05030a03171b030a0c020a05060c0301150e060708070203160303031b052109010902090a091103031309110c0a050f01 74
    0x107014071442020302041f060104012064568986031076110288400c40c1d440034040c0162465004040c8105504030410400090003d007250032a0001403100700303514500b80d802d2000d000d8407008021255866400819151820010341d054288a0307641c2c0008078102c500c20701c002d020090300c00708d84105011400b040c3c260000e0190b03a003001541e40001403104070b0013001da240200c2040000c0c02d40c0a000304201c000c0301d11202450483c0d482034400c80000d60002421030340c401d4803020301e6a002c941841500007103010302002d0140302e88054101c58604500440d00402c100042d4011000261522042e564005901210a1a403100c0781855410702001010342c02c800d0250414154030400c66030005008c8000942000179a640c020b440400182000350842c03000d85075a24050b1410310011141c040c41c0d08002040341c003080200704100c2c11250501200c48050304604c210b4140c840b806029502107107105010000406200e10001d02c010482d481c106406e4603c2c4150039440d5400d03100c00350440300d01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 325062500 1250 325061250 325061273
    0x90c0903030801330c0611070b01120204090507120c0e0c0a0c0503130b120615070b0402010207030602030a02180a0f06140706021314091e040302150703091a04 70
    0x2040003c1034181c0c1d100070209420155000c4c2c910410001100559115582040520305d074503000d14410700c186070400000102030700c01c1c01c1c0000c15005001c0b00402010360700d03414225010384014800f280402482c4c90701882d215064000f0740da001c4c0c0800301d00e000c00654014640c01000c2e0091803100515210103240554020100d500042c050444003000c1040401d00440d28040c1e004144a20842e4139001c0c030314210f411030411415110b07552800308420749080306c0c1040c1406810324104d45030155583d220b00c04404082c0c4101d05502c64004080009980c5001951045c600107c005880798901102542c0f1245080d150724007aa1450340280003040034168880181d800b14140018001c00e2160aa02180309aa101400d00d0f44086184000c1c2d800f0540298129424180c3d215002c40c2020100070541c1401d96840d0f040041c10101d02000e4400400d16580c014003e0040c0c4a11031091000d45008840c21500c010000c0d079103258400410803031403081c40300c140710500320104e81d1074195a85c210428 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 325063750 1250 325062500 325062509
    0x152206030501090516030902010306091104290306150705120909060f06030703091a01030807050610060f030b0d06060803090a081f05040213020c100534051201030804090c0903030801 80
    0x1507c400201040d039029070400c600500c0d40043c1000b0b089245000400242c020313009101120034203120341d02c195805d0403404035412204040303052a580300c01007080040340f081c0c0560b42c00840c0038416040481c0c0f040c00180810103610350100e58803480e4804112000b8002030407688507098600d55000c00c3c4e101c0e1000e817030740300806040004004205041c0f550b48a02114542c00380010944004401c1002160141820911038000c4404c01e0312010130100b00714029008400c006011402c000b0300e07040c07103900003e400a002401e20036607001d4645500d4180c41c8103400c4001c030341c3e000084000362400c1482c0782d40010556140035102d800e407584000303840c00210703207101002e09880740e003ca000d56a4031031207949110a0b4031800c56403101134603001d0761110500040c0c42881850a000030314140c0c0c00160242082d90bc3e6000912104000d04000b045900c4a034280c03820044148107200440603d40096400b031400f07059200e48072443d01518101380c80d013200011040008800c410000a60001c14a17030558 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 325065000 1250 325063750 325063757
    0x17010c090311040f110702030105010f031e1e0302070e090c0114091507030905030c090702150c040801060605070506130f24020706050f0105030318152206030501090516 74
    0x106070b00000a400341c1030f500c0102503036614080072000c030b4251a000900c25284250020700c401e85e6510041ca000c50911301c005060204410f00c1e02001040710300107020494070440044600c00d0803040d641c1c1c00901d821508401682c000c410030700c0b01c01000804e955000089000508049640c90f00091414240d2001c42541d694007181c910720039078610300d05100e2901c020207181d44030b034124140282105028800d8a000e801282c0c4480c801d41003603038415104031490380042c8030000d100c004940d075050f00242007080c41c04042c080410103540a000d071038004c0106903141911001d040c205141401005040d8520781c6044100d08400940c00b07501d03d9192680000115090b50b02c1c1c1b0401070300f44d48501d01e03060011440018160104241588807034015000c600c0303007403c41d80c6c0b1360081c1942c030f1043d2801c100c41e007006440000701c6442c246004000007a402030b1147e017400c02c10070382103031000340400568809842100041c040264144107075130040c500d054051120b8200200a040a04801c00e10315081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 325066250 1250 325065000 325065023
    0x60a2f070c0902210a180201050918090a03030f0606020a02130605091003052a120319081801110327100f1514101806020717010c0903 59
    0x2484034419a441c01489030030740941d0307035111001c121070424411101d80039443e4560004a1010304a510855001001d008020003000029400550302d90700050342440e840103030382c003003403100b4010002076074000c05035500108803000051601030709564448101000d000c2c6006401c01c00340d5400184505481e4040c9d401d1001e0350000d050031009440250041500103084d01d06011b60800c00035442d0003100e001e4801d81310100c84007480389117117035851100185654a55031100e810780c50004442480141e0760b030116881c10041840c001d100542c9540b2401c0403c4c0000100821b4042c420401c2e0041003480008000300c288034954070003180405000403844004044c2ca80c0e520200302e204041d91801c0c02411950070503c1445050050031111098044441c2050302000503040303180b4a510680e400400005405802c020900c102200c6080b034107001c101c0c1801503001c0d145101c280c48805071600d87d010300f62446c10040c40e5036155000b0040ca1b5484d078544100500d45a50004c0010140daa20071504d040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 325067500 1250 325066250 325066253
    0x80c090403030c110118020103110702010e10030b04091b0f0f09021305030109060c0e060c0a2009070e0f0607030f11100f09020f090601050a1b14060a2f07 68
    0x4c652400d50700029181d0b01e880600049030880d0070302190070b94801d130f0303090004480b04404c0301d9a0340641c2038000c0c0840c0b03040c06402080e2030800205c1c0300ca84e4080c540041c90a010400003401d4071031006050320618540c8482110300c940d841c40e44000742145106000d40380380343c1004d0028250140c4501284950701003400b00d51001140c4202c0d0080a0041c000e200c82501e40c1028402841e528610402181e81014000d5060030200140c5803549084c802420081201d9107514000c801c2d10b801158400c441c0d03004800069440b0500240500712566841068284110500c0742122820000d80e00c074800502160000a6000c1e07001c0c20110024500100744042003400c2c4c5140101c0c80e445103048500300240143e16035925404240054000c85500034241301410500034074410030380304070340058400c002c0502c0703840c0a0710100b5101c0f035058454402155460b00c600340c40d00912459401c0a810200501c0000b15683c01503032980c16124125071070340c0084034814003c89100c6002a4003880700402c000c0d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 325068750 1250 325067500 325067507
    0xe030d27080d030614010203071401020f12011a071509020d0c06030e06100b030f0705070209040f0b09010510060e1f09060210050603150a0209030703030f0207080c090403030c 77
    0xc100411103404162a00d449114854680300c1206000340001c1c80e1540000d0f9803001d420108103082d0b41a005949001c542e41c868428171054550000800d6400f00848000d5450b140010440042d210304001002d50600b5580034281554801c1500781c6141841b400020a0940c414081c800d606400e0004242000f4404614089080c8101038060f40c116100001d0450f0107030411880304a1080c00c1d100a6607411000382c040c0800d034041e50a0f0060140300203410318500d0380209c1d810691500b445402c2242a50024100207001c035002c6030292104a1144100040b05607400d0b0007082c4100280b0a925104010801210092203450100600d4803085480703a26000c1c00c80302038540030802c036406074044100292003104540701d00c100500c21000c042c42120064800c4034080c030802800b81c000308107600d40c68030232080080e01d64210030750b00b003010018558040000c0310085101ea100e48514500201000e401c01038294040c080a41100110300342c19901c108440d41e0242c3e00d420002101c01400c0000c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 325070000 1250 325068750 325068797
    0xa031b050903100c08060402090d141b09010b04060807050d02042702070f021e030303010909030f0203040311040b0f090907030311070b1c0b090108061b180409140a061b0e030d 77
    0x4c0c0c05010101d203040000000411400c480449014280c0f6010480ca0144140c2107400d200d3f1000e0540c05100c00d04c21a4841d2280c2c503046041858202d003070000d148560801c90f4401d52101c1410840304051403048444050020708007800904c0850402c183c07629140130303140784080000d00c103808004030100001202100c0e41c0310b0001c0502100c1d140c0d03840760250070007403030148002d802044000300021800d62001085030166644003c80000410700d000500c000b6007854401164813014481c1d12801c10786442d4030051058544100078442d0900d1410b001d07011030030200010341640c0100d6018014140103100b1500c0b20300010000031044140d00d80c1c0d02d030092503046551540444403100000d000503000543c0ba00070070303801405410030010508822402c0c4102c0c141c61250859180b007038a010316099205000b21409860030250450480300e205042c03001310030040711003c1d9a103c07541d010b03000d0300c001c44280400d1070a048000f0342103140029981c50386c4c0b0280604110340400d4500c140e513000ea144 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 325071250 1250 325070000 325070003
    0x40b03031c0209090f100608090c040924060b0906031503030a0f0e0109060c0b04053d02070308010b0c0304030b040f03080603160603020a031b050903100c08060402090d 74
    0x48003609081031101c8000795103c154041e105807018030101c0c0f029001051441d024900c1d402d00e03110300924003c4181e0301d0310f400414182c00b601800750810490340f51401148400ca11581d02d90f80c1d910050303000c0700c0300080782d0110f202d061450312009100320014401112801e0b81e04450032a02c0b07550701c0d0714010a107c2c10101d284e07058000826051440c0b40c01c0ac21541800445443e031030b00403c0c03000d00440d6050945c0c070031440002c0002c5d4480020640c00443d0302d030820301071819aa22040f21040500510241203140c50018040288c03000f540c845018640300d0310700c8136000c15403a01600c0e0710001e00c81181801024015400060315560a10040040b07500440d807040000082d864503041082c0d6841140e5401e50104071608005034503840d02080880c01d0b4040c140d4040400390a00204800a42050320304209140d560000a060f081843c500020008081e41e07c1c03580c1c451810041c9400c1c00d40c1c551a085203d0b003085940700030303c0d4222070300540c016800d880c01030700d60155500240c41504031440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 325072500 1250 325071250 325071277
    0xd0804080d120e1c02010b090720060f071817030304020405010902093a0c0501020708060c040b070c23090705090102030f03040201181712090f040b0303 67
    0x10000340908011981070003404454844107210002180e6031003c0d9443c4294081c80c42e00026052a541c0003165139600e0700d0310070361000045584d20100031400300e400c141c6540022846c1031448600d410b01c110070740219043c5150180101d41800d0349211100b40001e0544c406101c041201688050240303074107003008204140b038030a0241e00c1c80d51690740700d41c0140e034283d028504180000c83c40300766900840d503d1000240c81c0000d0015100484608010340380104013a01c101c00d00c0750f40201c2e5004502d01001e60042031000303060351821001900d00132807039200c40d805801490802c000c0b40c0100c010b80d2b04848100d20b41c15554100ca10701601044038580160516040e0302c0e08407034007400c2000507501584815540e03411107031191801903401d03010b80e055850040c0d0040000c40c030a0003152001d140c00510604002104080e894500a0401c085402c40d920010809c040e581c1c20000400034001c103801e030144d0261403c843d02c80490700d0300550030700b110300464a688080c13115450030000c88410140080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 325073750 1250 325072500 325072507
    0x105070c03060623030a0204050a0204051905030123130606090f0e0f0303060a120203010e060f0a1a01080f070e1f02120f190201110a090305061303080c090d08 70
    0x1805100030700302c80c05240d0510344c584060744424814400b1400011100400524412070a5420007008d41401000b240c2c03511340910000603243c40d18900c0c0800286005401c9000605050034142111200d0b4840c3c07402c0200c00710301c0d1740c402880c0c12110381c10003040a80b90758481006d06081014001c56800340400c0ba150283c5c5103280156030f8003621020100d60241c403c4245200c0c507080c0d8a0000ba603182d503000e02c00140800005c0a1f11a24481842c03020b40040f4888202050076410440221a201a900c0c3c00340300b0403ca0803418400d202c098400001010741c5107460600081c40b41070f00410407081410711002007280107024110040740e00000030b1650307800240200c81c4614441c213a6840001501c100c542e500d9030703d1000780a81d0007452550700c000c1e003066000030090701e03034100550106095550340c0440503042d03002940240a00e00e40c68a44400c002c0c0b030361030b00c0c81c51300b000107100810140a2501800009074490074240e008080c011106481c4c000c0d56000603400d04001e00000c3c00c503000007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 325075000 1250 325073750 325073753
    0xc0807110102061003080406110f0a06060f0b03270f0a081c11030402010c140a0b040b1e0a0c021f0e010e07032a05130603020301181a060105070c03 65
    0x5406000e202a802c1e03480340c0e1592450080d0039a4203000050118030300740b005109051080240c1c02d00118031404407500907032009680c074182440070000751020342e196182801040c10700c2c500c10004080c00e152140ca03500e0f00d4030300d28464080c14000c00f800a0180c400442c40c11104104444a580c506819100e50002516084071140d01c800003c060081d460104a4090000f034840d522403502407000d60b0745141d07115401180c18018849085640040c0031494200c003110030000848554461410301c010b5091506041c01c0d0580d00a1840442d521f0b004c629000c980034103030825030882e07089500881c2548a40c2c00980c18822024040c0310080e980b070620100102071500f2007450814903000800c6800e1303008806039100d05150001030b00300824044180000841c0564007a00d80b00c00d014411041a140c4002400c031003801c0c1d001e00403041d12483d050055280a201d03c804111168642e128079800e540c1d2668022040415400a100c100000242640c0d006000b01c805069100141e051070076142d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 325076250 1250 325075000 325075013
    0x5010203071e0c1e021908071404020c0307020112110a120612120810090e0a05010e062202040b0d0c06110c010512060d050d030902150f0f0a0c0807 65
    0x50060300d00c6800301856040300082e0143c0621200c003508525081a150000030030030b0868107080a040b80c01500381c5083c000f040c01d0707048800300940080000340c6003a524110042e424076941c247c401e1f10841c410040f8065a000010864142c158203007031180d44d00c01d130b0300c101c100185000c1484044080002850b145003a07408000e411800d42d807050100140c0741c49148000f80c1035840c810040c0b45e00c41220141840a019034100703540701024001d0481c015496401384c1d420395a4008104401da4060120001048000c1c000e00103404c07409001481107103842c8407041c1c400c822908006582448003001c1000350b46454100b0804100058003c101c440041c3c138020207640c00d14400c0c0303400a100711505c0c10b6415004a166060340038141c1d1285e04204464610101c8120041c1c02c4907402440c00800c100007030001d00c85000340c50516240090181424010301148100700c00ae001e48081c0c00f0440b035059588100243c9800b4002880103a0312030080c50800d44400d02c100c54081c208000c045001c0080211 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 325077500 1250 325076250 325076267
    0xb19060903020411120613060807060c0b0f060f12120a08010305070e0606030a020306030c0306040c06090b070203070b07020a1d0a0b01020607090509060d08070c080c01051e13030501020307 83
    0x109031410401c3d1034901d14802ca582c064080940c42e40c2501e000400c89a16003c50950fa90071f03219140055025510601c0615000681e40003c0119040014200601400f481c00e20f500c540c00d80c00300700f1300b4509034000800480e0841c2d9414841c1d80b86c0c035072210b01d40c2d50411107881142e01041d10700707680382101a0003406040c8248070442c1d0b14841c000d008150404010202405140081d0105086485041401c0040d400090030560144640100c1203e107075003c12486014038002c40140c0403050511300002c001c40801e03041445e041804208000040e01c0c00130b0b40720112500b8030001034441c001c0784005480e409079580050803001100c0926980002c001d980580202c45404080041803442e10040e601e5002c1100c040303020411070141080709042140703045034070040c014100b17009040305a5071000356030024030082e100010720070424441041d0420000341d2441090038030a00f000306c08520014640400c0042c00c1ca003038000708030440d8850901d01d002001d103034400000e544a10f04490001d10442 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 325078750 1250 325077500 325077503
    0xa1a0601080f1f12060e0a0803040b22111e03070504020327240609040b040203030d0c020307020307082b18030803040308180c010e0319030c120906120b19060903 71
    0x107161000c040c0a01200042510000392300401080c15030390f90f5140e0301c0c003a200043c005204601c40112000380f6040140d0b00100541c40303040c525151100f840b043c06402d404080e0398a46c48140c4000210141d0b0300000c804003119000c55000d65244d517201070149003410110401e6029030f00c01c07102803c0300c1c000854141246a5800c0c464034003d02d59580108040070185c4819030802041c03000b081c0401c2c03107499400e901c14005403c0f24980646001c41d130017200c0c4008a07000040c0c101054100441c1307014481c40000b030030b88000a0106101221620344c07040500c0c2c9040911103940c0710740300c86035401100b80b10303064101d0f00c1e01c45060a82d00e0800c1401e503401124100c0c00200800c002540b0f0b038110a044c08400d212401c002c0004960540042d19503206c0070007101e6040c41540b6210744422204115510380c58480da81b40444c85016141c01d01c031101600d44014280500032605101c041c3d44003060304042d05081d03001003060b02c01840480e02e800c048048415800203004d001142880d0040310080440703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 325080000 1250 325078750 325078763
    0x220305150a0e030909060424060c0c080111120a0b031207060c180b09010903080408010608060a0209030d0c0828020c0406140d02120f0a1a0601080f1f12 67
    0x350325903a6499124411098005d40c0180e1180c0816018100741e8022240b001442c1c1c000c00c6c403110b6103141c415190307100b540021700160344e074182c0100300452050360728001c20180f0020301c0340d8038040f07091440398041e40300c3c00f0742e1151f40c5c0000144008940c0e000b50307504a83c0a03050f584c10f0403c042c082c124543c030400c1c080d038280d410304822150350f034810350301e5840030704102c600c0349076007420214691507603403194070b0690411220110104c00304000c24010001031801c0400014050300e850222410301800403c403003000c51050000e41541d40b4085107181280f64145032a25400da031626110040b809540001d021450001d002c60101905020300c102e00c000a44e000c0361010511201040182e03806406800004003480500c15401d04015815101040c40100001000801300b001c80346090880d0240030220303480196101c0901281c030f40d1044425540c03910500e0603140080020300fa1080c094145c8400408900c0001e2108559089000b0009051030030130103007941d503400340c00002c0c00b002d0301035900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 325081250 1250 325080000 325080011
    0xc080712022406090402040f1103010f17070b0304081b0f0d1808100b03072102100c08120702010b061803070803040609060503061c06050f0912220305150a 68
    0x103040c02c00c01d018412100104000407590f80c41d800d0002800c010f854180d4000d448100c050028400a00a180601400d400b45a4030300d04e45080c441c40d0861214032002c80342c01c0345500b84040d00b0039100b02d03a400ba17040307240c0c43da9400e51103c40000c2c80d61803400b04151030003484811041c100e0041260316403180c0715a501d83e18580858020946152907105d201c8669011000038503004009c0e8200c404045030003400c1d41d81c3c1560780d032a00d40390840c904540b05400280748802e03c046181c0280b0002e00420189040e0003a40d8541c0c1d04c9107051301c514550158195200e50000325264400d4100090044010b404292a07181d81c00c490000e034000c40c0c1500d4403a008004001c600701400000341e80445200f0b40d52401040d2900d0416501540050700340381d00700840c408e80d01c0181e90741818092046204610014251500ca004407483c02005460903a0a8101000e000c801500b00340c203482030b0642010405082081004440000d00199800105180640460705c00b1208201c03584900ca8100c2007010b200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 325082500 1250 325081250 325081303
    0x120c0c0c14010c030c0524070306080307021509030c0616030801090e03220e2401020a2105130303020a05150610140c010e011a03030c0a02010c08071202 67
    0x801401840301e5000402407269040441c0c41402c210600720b014205485910005030546200c03138800d540160450b40303500302800310300c50341403003440002c0c0315000286085c5440c981c00510309003100c100b14a2038090204010301c003070b6401c0c408418201801400c01d51b5440c101b844180312900e00c20002d901160000b000040c440401e40104613810032860003840c43d0414400460700e00512410030082c100d840d141d03021a1284560160f0380c0120380000c80070b610b01d840348152048201600c541a030440d00034619020000d800a071030401e03020340e82d40c10300207505000c2000716030314090803842452000d600b10b000814140c011400b824428019015990f45008185441248590648990390040440c244400e085845003002c0000710001a48152800c0c0c103030701016007512000c00001069075990303852070707610742c0c80e101001c2c1c10050190080c60034108008006c6840c1c01400344003038140486146158200145a011951150342c480380f03d1054900c0210025030310314000307511030511802c1800305034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 325083750 1250 325082500 325082519
    0x9050103020708070f15020a02030712110706050307021006030c0801180503090103020d0209030604060b010810290f0c0105100504050903071b080a050c10050405061603120c0c0c 78
    0x7005503411426580c44e10300306a1307500751820f0a03400c003541c401c4a500c80802446a85000406000c0140e034025604c07402a42008400c002078148010288488800450304050020802204440840c1450f9407290740d034500990510902003801e0102600d8040040f0410900c000224165011030008100558519107030310002d000202015041e9401030244034103540c480d800602190007520409400d00c00b038000840c0c903141e010350b02240c1caaa00c07103943c1401fa580c4610020360010b181d54200e01400d20300800554180c48215113003000782d001c1108a01000c45690031030701100201c2074120703500d00d02c03a51807a0003040107440070300ca0180c0c183c1e4002541c0c68240561402003003880095403070440190798090441c481d500d80d102c05e40c600240c1c0011103032402c0c00310380d0240780101e001d400c07019130b188100320151001000781c07418401c0038441441544c684030151441030100d4070005c0b901c0040c504003500c0b5440d00421584403582402a4042c1c5164031064012543d48902c4040c0d1582b80ca40d070091 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 325085000 1250 325083750 325083757
    0x307170f011401080a0b07020a0f050d140a2a0b0103050d020d090513020a0c060e070e0a1505130e030a030905100c080c09130f0222060801260604120905010302 70
    0x5801344d500c408051000306003007039581600410b05004031003058859a4a071024580b10040a80780c54110454003200c494200540146140e102c4180600e4100c00359005400c00b00c2081c015912208800c00703224088018034030000c5199000b0034040e402d5a500d280c070907503880480140000601a01101600c3c41c0c0c00307082c840050340d20040c401081c12070181082e000a40100003100204004002c1e50808281e152150303014940071a000303080c0590400e412032000c8200070300100c1c911481c02c079002e001c4220070103c41d016507000710350303030400740ea60700451001030076060f45168440d00001440e10511074155002da96928131a0040d15403104501c01c0350400c030b88002d40580045212040040e014034242c0c0d000f060b844900400807260b040c0f99440c048126519491890203035580080c0d190004486003120048040c640c060700c1c10300c139041031002407c140d0180301d040d108004140d00750240303842c00c1042905640444048501610349800c00c0e6840c2c9068200c00b5002c42c40f140c00115141d4464000c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 325086250 1250 325085000 325085009
    0x3070b03011503020903011e0b030c090915040f083f0708070c05060f060405160509151b06180f06040f081201230f18060307170f011401 60
    0x10407030020b1401c1a80a980401c400c10f606540e6498910609908000e00001060000200142c881030060901d460105030340505441401c0400c100710382c610001420417514110080100c0e02070701c1c2d03460100c0c00074403440401085580045201d480314030306030f120000e490802540030444018a00550f0041030304007a940c1c1c80d4500d0581c005501c5d20b00800c085500507420b403034071040c3e0720030589481d4180381c2c094070401ca55a1865003406510b01c0d19009841e044002811224008000103802a145100c1c0303140e0b460160158902d160401c00d4000107589116521005000710000310704246074861710115010300d0b0f2282c0e10000c41c000380d400080e10401a00029000304241c0c1c82d030381c03034400d015446180116680c0d2400c003c40c0806e6684007011074000d280d60700d6803078001c001c0c403d88a80c8507042c81b00811700410550310051050790b5081c002c0e4041c441c1560034080c072a02c3d0500443c1c24049c060b082020800d802e54415840b01300005a03a00710088404000c05ca80080e0f5508030703070a21420301c00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 325087500 1250 325086250 325086269
    0x60605070317071107140901060201290a0905040b09010e24091606020609070803071a040606050301020c0d0305090114160e09010609030605070e01050409181a040203070b0301 77
    0x5042c5600c0042e64100e80003074640c01d11102e20074407403100600d0400c49401c0b102c0401141058412241400d00c0350078090000c81c0004d200545500da51001c1c3c051044980550543c402c14111005494029081000e410b07070007400c0c01246000d061106e82c01d00241c0340b8000943c606030ba0420500008030341040d0088020a2000c10100d42c9070a511003840050940040c5000e00e25410f0300782080d06481c0340003071403d0f40191060f850002e00c42810005903238007611154104001c0304000441e921b02a400140b1041d800b488203464a051a000800f403c5d00240d80661000540d084d602800180e1442d142ca01a23400344050760302c07641c44d00d0a8401c0002115109040361005c200841da02c0654044848030901e404041602c2401c0010400e10003a800440815580c60302402801194084d0990209290a101c204240f40000003000341c070880c414100000e603601d20165001c000d42d0620030700380c0e03001903910010300c0f079569501007238030b0080c5c408034824070401d000011420855000d1341e040311982803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 325088750 1250 325087500 325087517
    0x403030216050604090c0315030506010303110d0210020c0a02030a050304090b0a1d0c160c0501091d0109020c070317030f060a03080d0f060e0f010f050d26130305010f0606050703 78
    0x300b905c4054a401c0c04250145519840303885145040c0041c80c1c0001c2d80a0030041c0204d502d035090103800b5030260032400c0c0b442d401840781001d080b60006145102c00c0711030003005030b17609012200b8074203042001400940c540a132035900c1d82402000000b800c02d03a100003504101820340d03001040340010051203401030030b204865031f5000000c5905905a404003560251614110208401c0183c10072420070454884819440c240710659000701c04001900140020b01100345004250310b078610414820342d049203400182c074644071001400050002e55200142c0741c2014070426400d002904102c41402c1044d00c07000001c3e1052900d404542e04583e0440703212885c1000360211140a0603081c826107801710780f5550300049940321140480d10996010903c00041d50420308101617065103139110512990504846001264103580c100b0401d0201480c400c254001d41c2da2418001e000315940900640f811410000500006400c5462640c40b8224200f08003615a4410fa40c2c0c0d00900c00050002030b800c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 325090000 1250 325088750 325088759
    0xc02070f0801290604030b07050703020c010305040f020904051204060903050c0402030c0f0d02040b0418200a0309060f180b0603070f170708060a09140f1515060706020403030216050604 81
    0x503c0c0f9030002c03801400f0720385402d03100d80380c400b900c5100796010000914001021400d060381449200c040f18000d181c2400076042a4844074004085804064400d4001340c02050402c441003140e00388902e450440140c41c0d82e55898007814400e6640310940383e031700440c0029401813a0034030850f803042031682c030b0b0682042e001c039800150319048485954040c0c0da0802c000f0480b5024280940028004681e10343c4441c3d41e8003c01106480c84c001081c0250036264100224107a003080c142c52064005103400912200c2a00303104008d0f085880b44401c9152070039440381e400f602480c070322070320541c000d41400440f03495400234140c0d26416480382070280d1040d04404d209400c0c03c6582c4c071080b41014000c4507030a9458200d200d043c100d080c2d5180580da5600c600d0502007103020702000c1c0d1804840000b50207000300802505442d602d00c40d001401c0740403c90b00103a004608480945010030000c0c0c2016241c03605464890700035840703408140c0c054407603004105c1c40c400d26007081d80b0a885025181c6401e09152 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 325091250 1250 325090000 325090061
    0xa020607050d020d0504080901110109020109050d0317070e090f1005130209040f06050a06020106050f121e030403060509010903020a031404030213050a0506060f0403030f09030203010c02070f0801 86
    0x1800300802e206808000e442da00c81200d01486008601030810655a0032a010000d0121450107020031240d074104604e207800341c1c1e0400600821a8170030344105032200110b180440e8201c00b18120740c408070746004180402160720410300305e0381c4503041c0c445071600e0300e0700540c00c1301a0b181200c0740901172034000d01c00d002c9414150319050000d1040000981001c071007100003001c0c1c23030001408030803c4d60784400401c81ea00c0e0202c5000002c210700c4c00208051410400400c8074008032072803c41c0140f071f1031f500007101d091040001c40014081441c0300d580b442c08005481d41c4031351052000751441810100460015071061045444d401d40c19001131071469225503050700e41c0a0710040302996910284000009030302c072264503422104401c80d0025480c80c143c1d03541c3c0100c1e00c0c0603103c1c0e80142e80a1000300130f0340e040102142c0649801d030603e60003188105c40121132220781a00029015400d161407180c903182c0014110081e01d40345c04040c450183c4948545007201c00340d100a485101011050203102c0f601e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 325092500 1250 325091250 325091257
    0x5120105060f07200f0607150209030307080f030603070905070519051314130b150904021b0d0905220f0204030503071a0a1103011401030914150c0a02060705 69
    0x6050348803070300342403907601e510340300d500441c802c1107412100f40488600d91410070b5070300d049104d04858241c02d20f000c0e902c80c1c0c400c0002c00703540c010344236130b00141e03170720b51580c0400c10340d000aa88000031581d10003c0c00040d4034280c0094401d5030280c40345c2807010595851501515110300330f155580c0d400c106014903419956195481c126081c002d04115a07a102c0c4c0c2c1c48100310002d05051100600306203d98014401c2e10f4030350503424880c640c03801b41c21080c9561045800d0008a00604040d62550b00080000c1c0080c811000503400d00780c0c1080d102024458041010136004d07072140c4800c84007691f0340e401d000741e180101c54101007036000b200000c5240d45480e84040000250140018181030301c86c1e9800f49551301480301074401003008400f241c400c503000091142e01485460041c440750180c41c2c2075074254041809a98026820302403d048964466840720304036a400501a01c070f0484a00006600d4851601e001a405a0160002031054144000708c403241d00140d801804e82d513560b440101da6582 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 325093750 1250 325092500 325092517
    0xf030e010c06060605071b0503030405011d18180703120f110609010e1209100c02040b0d0c050102070803030f010608060a120804230d02060901110102030f04120512010506 75
    0x7860a1840c010035518894000980b6154451603a00c3d101d60a2490500e480a111b0814410f11000c0611068030080141d404450003030030300100c02210b0001004000d0340756030105400c41c0c00754040070035a80e41c00d40064080c000b41c500c0c10112102c1010940d44461050202400511040c007000145510541803120000501d05e09081d2212030085050708195042d00c0f040c070640e4541450841844007070244041088150206d03502d084030307101c00f05411150818007032090003c01c0c0c101300151b480e030f50400d03201c651000b04610181d020718036203101e000003e806100d005101300d2001003880400041164044e0380f4194a500f0282c0c41e000d8102c8402000030600780d0000d20b4608005052242d407009090028412a02c00340c6407402d04600c030301e0350b4410603107641004540e10003515142c2ca600f0240d01038140c0640700143d0751a400340042c1c1d0100780c4401150360540c4004200303e03044840f185007a01482c8210b501c0002740f1a80182103505000c0e500040002d9903c1c18010412443e002c4000c0c503452 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 325095000 1250 325093750 325093757
    0x120201141803070803071b030b13140307060e061b04170a080d0b0f2e030204050a0611070603110d09030c0b13031205070e0f031509030d05090303040f030e01 69
    0x80c11848086400c0400caa404610300340c5c008516002000101d80550810015a0611810083c690b41b210854050702900e120502ca9045080806019803d860024445821000c40b80d44140c146403040080401c02e28590084c003030a030115502c80103205c446c0c0e100b11403a5032000d007028202003d85580424180316960a0b10400e454400040c04a82c003801c0300c150204400076401240c0805d02820110590140f4440e00d2245241903030003c24035141c1000300c90181182500d10410b00083d0000d2285420403980001c16500c0014155480468141403500f42c100742c0350722a940701c0c0c5c250203803190090941d20401c01070013000f050410540c012849a406803400e0a0700c0101901d60469080341030ba850328600d10201800d509064001120340550001ea038800c10003454003840060203000c543d090103120310200300b6010040d607020840304405261760200c06060707003088001103680e5440020010b5456003403c1c0040c10041022042d240714a811151002c0d9850075680c04464999240e942c6c0c0341070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 325096250 1250 325095000 325095037
    0xc1c0e07080607080103110319080903121c0f200a120603110103140c0306040b010504030203010e030910050a020a1712190b0d02150307051c020306010912020114 71
    0x908004016590203103007180c48139a40c0354190704000c03035018501c501c0340f802544203042e82000240c00c2d001100c1030351f0700b02101c56215001030300000e080100f410f03401c0030704500101d2542c0d400058101c925000890039402000850400240c800c10354000086100c5800030006080355000400c030010540844146021410002c0150300d55003110340039003040d0380c0800307507540041c440c0d60103200c1d03403c15203036030740c0c031048585031905c40d545981c8001000c2c40d0095071100c3e040c0c02c060340200292406554010000d000800f107092150307030740e0341040c2c0c03e4a10445151000c400715030b008004550030708017503601030900d200982e10350003080e81c207043c00346100700010800b1032b003d603441c030001600540c101007580a40e41000340d09841640d1030200524880c41d688444040145c0c1c480c6240120445800400c5869584402055070b442c05101190f00c085040300000c86500309055008500c1035100340c1b12031900680f515583c406d50201500024089030b05016941810001c0f40080c10b02e4481a8207900c0030f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 325097500 1250 325096250 325096259
    0xa0b0907240e0105070b061003060503030c0d0e0a15030b061b010e0706110c090a1103040318060927022704050901050c07141618050c1c0e07 62
    0x4518601d01c4901d80148129210700240c01c1d800048807070b0340042403910508001940e01c40104415018083c00d11440f05a0440015507000c0d0700010007d010060680362110a400000e640310040418281d0008a003005070080c1c0380f034019480d401390b85c103400c10748809401c65841580200100a10380b039109000b800b03029031054a840700c00c2000510200041010010139030740e6458142c0e40e0b00038009021092201c04014003000400d250301c0c0704100c41860464031801d05880c0103260f0f18210000c00c400020400051680050503000c80360b40c4800102e00b21030b0b40d038000311a42041409803042604401403407a629002c444145a02400d50240c014542480e802210000c0141031100b240d03031029400181e203540c5410701c81c4a5100400c503000740080e04c0c140c0c1c480300507131261000c018506001c0300005c0c1d04240017040346c424070f4103240c0020000705071a02d20550603903003640768050741e039801c010015800500c81070640702c008445403a952120013080582e000503006003000e484881c45a1000080c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 325098750 1250 325097500 325097519
    0xf011b03030222321c02130e0303041a1302010c05070e1006030e0705030c01050a030e1b030c01030b0f060904090605010e0106180b0a0c081204050606030c0d050a0b0907 74
    0x108a49070001111000c0c60050381c81d0380341ca00c1e444d030301501c003624180c0700240c98a001c1880180111111400c5030041c604c00121040403120034890100d01d40790200c410004000020750080e8040c000c0b200d18945048038403040940d04403101c2c010b010300d550120300154068041c125155100740141c801d1103495115041d00144100c449008800c20750030704201041e0903200da01c036044002000741c01458100808a60360b01c40141d41141041030010707142c00024481d03130001c0c1e0100c01d0502602e032040540200721982d030340c6481905200303001d046000741e050360281c8140c14003000c0c090000c0c0c1d10001327200c080224541000d00219080341d140c08030b035000941944501c3e8003814607980a0b44155050040080030b4440500f09030941c02c0c00c0c1901070014032905010303a48030665524007000403001500c3c08021601526809520314505101403008002c000b080140c80340740c0560483e03c07081520020040001030030f83c1c01034803079001039082c0030214120311044c2b90b000e03903a4802c807901d9966411150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 325100000 1250 325098750 325098817
    0x1140a0e0c1c0542030f0d0302030f061905040c03090206030a0c110d080a15090f0f050901140c030702030405030607020f0d03020306100c021306060e0f011b030302 72
    0x10511943d103608003d0702c500b00c4200c122840c0e0f04030384894103184410701c0c50b001c0842c00005002440a03624604110f07a901004440580542402030f076400110a000c00707006034000b616a8200139480701c002503194105000901041c052054000c1030141c0742400f8400144800b604882c10140c80700390030300250300c41c5002580504010b880000342d8852151008281198607180700590307030480300e00d40010603803185000d500401304900004110111219041408156902100040b400d185980c40d011550b580001a0285504000d020564030b100c8401d0807203a404500c8013030341d51010085450a40d0260181d5440341040c01160f2501d91280c1c00280390290460301180103070700a401c00b010f2248207205507443d040d003a05043d8194100180096118065180d000c1c080040201c182c401b50740d0f81d4030500702e910f102c1c001c08000790fa49404000306840903983c1528082c0041500101c0b065204150102850180310306829960080b50703021006503008991002180546c41c40c100000c1403403884a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 325101250 1250 325100000 325100047
    0x30b011e181d01090507050703050d0b060403150c0f090803180f180108010b0103050402010c030f0c080c03090301110c0c0618060a050a02011a030718020c0303040c0303020601140a0e0c 81
    0x14038040e42c5840c03d50713001d50304010702c145c08104060004500003600081601d041c140c61a0780800c140741588040b46960040d503101030b210406100d180489440741d41e01001d500c401540e41c0301c0420211034025520040b051007000d81c40e6000708035040007994011000c40780d1503030003003001c45500c000000007458480340401d241d0210b1a101c0041081175824403880c5200760007030800303200510b0290000303822041e81d80310107024402039603142d051701441020140c84180e84003032000e4444c5114401a95260012483d0600943c82c10309242e0307141c90420b00b030760080c0b04000014040e480c00d0300c00b4080160001ca50b88009280e5240305000301d991030b4005001550308035610152501c104034030003406d545101032051510001c40801070031944001c1041d1042d500343c550030324036107030350f001150000b441048809142400301205001c10050f1340c0c120501180d0007582114120f9032075080c900700c6480c1030050541c0c4203103890410400a800880a0790b03110b01207910703090406852078500c00344130044915 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 325102500 1250 325101250 325101299
    0x4140105062b062d050303030a11071407050f1e0103150b0f0310050d050c0609191503150609180605040207030806030d05090d0204150f06020706030b011e18 69
    0x28084071201d101345495052412001030100030520b0200481d03120300c0050034800c0e81303507201d0303185110a0360440d00f200d0358941e00503076000d041b0445124441c2c84400900030981300c0d440c1024600e42070b1400744142e0791030604034030707105078440030800c01903008082084034020349640060300090740d560030310302030154011100c00d201e90700d14103064034a401c55180e8110a200302022203203c4007040b000962903840450a848071340c0c0e1240c0f9980000d40b00c0241d24001001314220103c0480c0d8040310a20340c08031240952818000284011203a814010550041c2e4000480c0e21004003d940d460300310046654042000003d40c0a1311a0040f40a0340d2090205a0200b000d003428400310381000c0002c41c402d01002d02e05541440c0043e0700040032a800014003034811a100c0c20101c0e8050a48403009004081040021440aa441c2d4000c0d440c0c0c580d0b8031402010070700e08801d0040710f5000380018106003c0b001445e6101e00c00e01c40003a50701c80d81401d140510400700c9034010848600490702058a40b00c080c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 325103750 1250 325102500 325102529
    0x903120e100902010908030703180b0f2215120c030606320c010c0e0a320405011d09060c09060a2102120604022104080c100204030204140105062b06 65
    0x1588142d0440c1d0b40c00310601072010001504445e81c0e00090b00c0f024030300541c15240c376201c04103080c0003100854011328032900c3c0c13220007500340540080c0b0030f42c0e28502c1d155050144c800c02807415021545c00744180c0300820010300280c50907101e4008551304c040c0075004000110038001c040c181c9a500701804d03000e810780d1b4031516004515000481e020100004458139580507084c1340c1620301a00b10201d51041e028080103e21745285003000c9041e10286001d48204015a0f56410113405101150300400d420700300000456006900030500ea44105004410640f40c1700080092215547c041c0c020348003000007a80200c40300c8c80c0e140b10030000144c90341c0d0f03015884600608041d500001c001d400c1d14411481040f03070650800b10b610326000e0f0385001c070340004402e60303890030884014403038110019540c5c014010640f402030080e074080c0c01a01d000b40c9040104a001080350b414514080c02907075480b1034203000c00e8185d240880108110b16000d40ea8044c020440d112850060302d1280e003140c1c20007000c05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 325105000 1250 325103750 325103777
    0x605150a2d030c050118080c120a142d06040f020d05060933130203100f060e090a03020c120118210912200904060903120e100902010908030703 63
    0x40065201c0d425030781e528480c500c7c1030321050381c1d0715040000d68010384d06610042c06110040c401000010380021f115000111540a40fa48880c064040c005862000480125501007001d07441d04107100745800a0803240c940d0b8981c51000708155100300d13481000300460b140010803e01085000d00ea0f03060040540c03031000200c8002c59407212a1001800d610300b49048003801c2183c60080d0841c2c981002da00d1460000c0c00400c4c208000100110b03401410040030000c440029480302c0c0454a0300682940c098442d000e042c0c2d115485400301400503030110384542024500704403803081c02005c000c000694085029102a5001e0160030260b401d282c02e220303112110303000e14103e00c0c0c50a06510300152540d0410005444d060340800001c1e20f40038100480403201c00781c014020b40103143c01003560303d091a1900d00a0041d00030403004400107840d9402802005196002d030721031541c01c02000c0e0980022040070200200800c42080e03040107040705000820300c1060005080c80341c00303562982a0380001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 325106250 1250 325105000 325105007
    0x40b12040f050d110f0c281d0402040b0a0608060114040f06020a0c0501020a0317152e05030709032004022107020606011d0109050a080a0605150a2d030c0501 69
    0x240c549811441c6c00206c0d41071425a650012180c03600d809000301504024401c00100d0703164540e4008480c07124803000d03804403240c5640c4481d441184202e40900107401d00d00c06210003c0180d12036130001c14040c00c04640c0f00e41c01a01c1202c0f01040200450341090307078a801d01000390350030707502a8002d038000071042d2003880580d9600303001800d028001030405001568009000714246550482800d10780360104524640c1d0000c16003d01034002e04504102c061f03000041d4800070500344402c07030a041d40c40e65176902c1340114240c902c40e0f8110b45541c100c40780b4680303502c2154060000c001a011140315284041170b80c4038400380050240c2907051072910006170a03c1101a080034020105550084d0304020603030380d001c40300780070440e0400e6080d4409050800103807000c0d91541c010942c030046180780400d034044001441080c8502920060240751601e00207040b0388244c68110f0b030f400a40028040c8245c6516180403102c141150090700a5001912030024002100d50000c40c0c10100292080185681c0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 325107500 1250 325106250 325106263
    0x10c090501031505010c17040e0f010e0a0c020c01050c01180809090c0414040207110a060809070e060307050103020c15130309080c0a091814030d11040b12040f050d11 73
    0x300504440f482c0d410030300068880320000c040104000407280381110b50301400c2d03007035900500001040c0005400d209405072001e800900446481103401c00001d18110154042c140d10a0380c10b0b000703060b5131400301004545551002903c00d510b90349582000001d5900703284200d050038002c2c2c081a48a0030003038100103489001510b006c2079641c0510042c4000008090000c00300001101c0040c1d0350804c9245c0348000c4102032120030340c010a441c00003d0300940103046503214416240503603001c5502ca40008424a00540707910b40c00d54450201445254029401091404c044000300d60042101c2001c41d03440e42d000f210030313018840d000c03201d00c400c040d04140c0302c40c050a001d0340505240313450708000c2140c07100c071b034401c401d180c544549000f907801c900620018030b16504030380c207000246042440c482c1d80c8d44c008220400d10600d08421089000200004d031007c2c3c50650608902c0d000201c0368244403e40040c0080d56107100941c411000980100045c032002c00450300d03816a4914003a40ca1401c091 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 325108750 1250 325107500 325107521
    0x1b150c2109031921180501020a0804030906111002030912070c05030c06090d24141006020d02120f040b19120b131109060703091505071a0a0e010c09050103 68
    0x440340c0e00d000300880c10300040c2d0340c0b02c01c00c1c000060203882803001c8010030384061740180640d44006080c019203940904140c1c4100d00984480750030310703034860b000c0300d040e0120070100d0305036048550040c104034151380042d6003000e8014110744041c1c4446141c2e00f00eaa122a000322018141c200c1e003080503007400e1000004000f0202d9030503003044244008520780c0034100c84003e0444280e880300e2403221800541090848a0080e41080100c20710300106480724029110f44c0c486880c81e07072001034000d10026501080c00190360240601103484202080140c100e02441ea000101c140f20100d00c52200201030041c19100100040c415403407a0b1014003607601942880d8103080c2818140c0f0000d49a281c0c0000104188410000c0e4005500d02c40d50702e50301421990035444040041e150040c2340d4800c40d0503007500d1803800c0d116144401c4540c00d07201807040340c80c0101b40e0304110540042c2c07800d60010242c1d02042e501c001080070b01d40020041d00b10342055117448041203c024043c001542e040c4a81e01088 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 325110000 1250 325108750 325108757
    0xf15060f020d0c02010513090501060c02090a020a02030a050d140406050a0b0102010903051b0106090504060b120c090103021c120201050a06050d051203100306090303021b150c21090319 81
    0xb0500c2e40c10003000302c0410f86001e070500c0800200303820017880d004804401001c0202041140e96141d40d4010002e2075940401d81c0314102c2e40003c620b01410600c201e40c841c101d5900150729100c2030000030381e22900155118170240b50b840710407205244030f070304040340300320302c1440001101d151101e99942120702c816116811a0b04d00a00c0c100000e8105045450188001910b80c251080f5104500e014090079045601940d0038003060000b04081ca801509203100100c41201e4003101c40b200d45a0b44013800d03403005038000b80e0b0b030b00100094108400045540302500c0300520122080d61111410114003240c5070300180c1d581c0d41000440c0c140c3e0720400c0058501140c100c9982d256988405a64200510314084004800808134050900c0c64002500940d170004090062500c1820090025002144551889526124200da0410000c00c44000958002258401e29110f0300595642d035001801c000c1141c5050007580310b0001c9001d5201c034400c5804000459660b1115182c415820000ca40c249003031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 325111250 1250 325110000 325110013
    0x40606030e0c01110c030a050a0302152e08030c060603120f0301030605090a021e090703050112060c030e010e0c0a15090603020a050715090c1a07060e010f15060f02 72
    0x70744400301d1844035804003442c2c0a120b20a03030031402401e103075000384015414803403440d01d0003c11034040389505443d4001d40903114001d00c401c1103402040310454404101a60307408003050031003038103803d0000c081d8a0605c0c84114136219000645140d20210203070109510090030004a80740421043c445200020012800e00c0d208000e00100c0f0f00044c00014481074460f00003c0082c1f808004108286400910005004420461040e45424a402800c0c09214980300040000b4028007038241210040d0030b104040000b99210709005000da08454801c1540301d4181090041c024001d40d24022134203006050722000001c1000503000841d405072241226000c52101030b541c1200c2d102040b2241030401607503444007404201c0c2e05100702c00300184500c24100c1c851b4143d1005501101d08a4400c0d48010480b903201c48402034cc4020100c00303003080740b1042080c0380000b03400f60441c000c0004c001001013001500300d80d0040a03603002030ba00300701c680b14003a0704010280c1d0001c0004404001c50019010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 325112500 1250 325111250 325111271
    0xc0f0f0809040c14071e020a170708010203010501090504020306010e090a0c091a0a08040309030501060b0307031a060a0e010e03100504030f08220222050907080708071e0e0c030604060603 82
    0x1394003840308068810b805401491740c000302080822240e02c0e1b03000700b0600704580c4076110249440c5c1c0d49031402c09a0b106250700460040414421641601c00c161a4005018a8070381004080d6100401703440c10480300c18604151510307824102c40c00349003c528086402c41c0040002003929080c0c3d44013001c80407061202c42115514001140c2110301c140c0b03001d2406581e50f003820307155109260300042166107041c2000855104c01d40245008000302c0d981400440944009140c4104001d1074043d801300b402c0041b2251107004240d052010300060424400401d41c400001e03003000b80c90508042c149846208001c101940321400c001c03041207034100a461401d107411100501c000c2265641e503c6c0c3c00d144106404e554400d0b050150710f403061007a1150303041960042d01d002c1e2409aa4803c058441c0460128907042c1c0800c05030243e80d50714008103402072030841124945c0003810358a04800500303032030226100e4600134030248908a091600e07a0b59007811800d100484415a02540425150008609 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 325113750 1250 325112500 325112537
    0x30c0c0303070f140304170312010e090d050c07080f0615011b0b0a091202010606090501020a031d041503080306011706030d120612050708100506030601060c0f0f0809040c 75
    0x42425040161503081320006401c441c9140700d6604034000086041070341d043c0014000004040c1e0001c880c4501c0fa65903680c1161a150803800e8468a5070f81c0c0100e8102c2d115588114003409002d80e5881c2142d2629a4500a1a0812580b850410010b411140070480a01840c01010140078421719240200e00048443d80100c1c002030003000703000390080360114440a245422403450150003841c40a40820381d02c03c00381c02010b2030721070000400c00c1c4550000e502e41c0042409039100340c01d41c40389114510b0400c3c2007001c1604206056178403a40d44c200042c0c60000102c0c030100554400c0081580d0383c20900005801101403942c00e8803100e102c8010440251008101401c42c001c1500b4a02c180300109040d07a0b010709190b0700001180d084001d4201c007032000000d0040102c410351019034042c02c842c0740c03e600a07904216102601a07002034010007013280b103109104100b5006410120052400b99949410700b11041000c0e0f44000300031448600301c0c6414854405003074070604090782a030802c4c05245 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 325115000 1250 325113750 325113773
    0x80712060504060f0e0303070806010201051009150e04030216150c20060a09060305060603061c0305070b0f1503161701021e0a020d08060904080a05090405010305030c0c030307 77
    0x4080035121000b24041007415000596a03148205041c031804040185080c1e813608100e4007203000909060100e40154010710034640030f0039032544004040c90620041c40007410300002d6030b11601c141102d00086034903928481c14000c520a6020b000c0304900c0e14440005121180c2100c0c41e4102100c0c02d1620785604011560696a40300300750302040c00001412840e1004904401c6821840000b19151401c4c1d218a0701c0c2c007030320b07102d440c00c01c01500c0302414400c0d14001100d5483e08010000c408554100c9800d0502010703078840d2818614104160b43c4141045030b0994202c11b080c01d8400a00011145001000840c25010fa00a05a044803584090148045032007102c0d102c0000403903c0c4400d4200b0340464803100c65299081c05400e03e00001c2c20881d90240d00c500006008404d00440107921403002e05000b150024103256154440c0c2d02c40b9801580072200400500c4000c000c10039282c1c0f0b540c054240218028405103031110a0b504030a410140c103040424880c0e0400c00c001800500e205608 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 325116250 1250 325115000 325115003
    0x9020726090a1508180102070c14030106060804020604031e080d1d060702120d020d06030503040906080303070e090c0c06100807060207051c060608071e0f06050313050123040c080712 80
    0x5814a44401117807041c0244940107001d002c0302c0030301e540407602c009440340e001303282c00e400da008001041c3c0d151804c691840e402da400952124003000f042000c5070501d901001c110301c02580000313400790181d58000d113940c4500c3c070310700079907885e4174400082c41c030100c2078402e130504c0f6040601950301d807079880203468615a4080000e032a01c081680114a001941507400c2240e85042c208601500ca0801580e40e4201c0d02c29160b0460800d000452010808800d80c0c3c042d5105481ea51a00644802042104030008017007144091040c401414105010803509006000746114001c5081c1044551030a00711903412900035540206810007032504d0f190381030450220301071007124482d041e40c5081c1010f82403a6000c5c8415200341034000c61206205090004481061400e00a185584050b00c2c900501103104510101c0c0c8c2c280001009894203520300c0820510034000015407900c08100c3c40c4d000c0001d0b580940101c111442004100441200d10f48094640040203001c2c5d103280c020384030f18040e0502d10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 325117500 1250 325116250 325116271
    0x10f0305151314060a0e010905060114040b0c06070503150d0507080610060f0207050108010b071a07120f09080403080a11070b0702030c10050409020726090a1508 71
    0xd003051007004410101d800e4020030b03500714414a1a801000b40c00ea0121601c541c240000c0400c480d031130b143c03110204586655100340350301da05e080d81040007490010800350501041e101c1d001c0102d070140c0c00600c05059290b009039180d403c41d002c1c81d450321000514001c00d00c4001c00602000d500740e074145c0e5400e40ca0481d810020110240381041c1800f8041d4405403203482088240f0210014403807994013554090f50f605c2c110190b100508907941c400b5031062034081607080006108a2540000a020031030161602d00c5040c2401032895500e031f02d040f602000000c0001c80003001201450103808803d0b16241b0f424040854903807102c0303050384603a1000030510744001861000040c020021041824140070544184c596100d110490795480b0801c100c2c428080d41300c06980a10344070030101c440008554400d41000e00f802c4044009603c1250143da1a00d155a2182c00c000b145000c0c19074000d041c0240349446480f45803d02c500511190000c40444000d40030b040e042c2c5520003040c5900003038080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 325118750 1250 325117500 325117511
    0x40311040e070b0f070605180d05030106080114030124140d05100225080d0c030525111905010b0108070f030b042301060f020721030e0603010e0402041a010f03 70
    0xa016041c14843c5e40d10040640b41032608100e44003041d20074500c006030084041c1c0303070006254081281c0d42d02c401d0090b000464446801440804500c0c16441600f0300d014000040c62005031000801c0001c2010324041010390802c0f060150703185c441003503002c5400070340300f81c00c9412182d5506920b5038101e0070701d00c1c882c1b6400316003500c0821444407680386411100c0e0714401c0080080c14070348025409040c240000ca818804070307000c1940f0a1140503c00d222556607880c10040c00800c1c0c22485407103848503010001c0480d80d10018450502031384650744496095204900d1aa1400c942504e10310302046042c05450340401c40404e4110203071341611030480c40c00203041c0e051080080c00034142007071603c910901e06440b00501d0301d20301d101c0d941611065111141c0042e0450000c80c0c1c1e0b03503454002d02c505010b241241c0e100c8000307025056803036a403203420210301c0d502c0400c0c0442c00d40d402c243c2c0001c02c221401c90a00081d070a16202c1c18220580d4541464080c00c00000060442002d88600e00c0800d40d460 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 325120000 1250 325118750 325118767
    0x14150a061b23010902040b0604060c030c020303040b0a0306091b020a0308220303050402040609110909270d030e01150519030501110a1704020d120c0c0308040311040e070b 75
    0x210b0540000800000d0041c0c1d1040b510403440c1c02400c0c4840e081b4080c52401c14411403e01d42401038404441065840b01c0041a01d0364007107422050051080307805200500c8040740d440303468005046a00c1300c41c0d800141d91440d00390b0340c0e401e0ba406041c5c0300010b49051308840441c4c5d070b40410b0b105540342d01802c00b41415241c03000181071030114501001e07130b8485405149010141e05030080b500a41c000c950500100c4e80b98591001114000c500940e280002000002885c1c20184a0541d20005040801d10100c81171078240c14044080ca401c0441c5070010801d8540700c5405200300700311201000000c1105410054240d0711180e4a4040c0f1031150394070300400007058003102c00c96000b843c0d0100080c009540140501c080f03d0704040c18030800300d03050782c4c0c20b20540401162081d120701e8005060010242080d110f989404420007119410402660014000300b0200800e69000f1403244404c42d0365035203141011113020038040351403441242031101020744001c0015402c815540c2c8038060700d985500300c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 325121250 1250 325120000 325120013
    0x60b040506031f0303090e0f15150c070305030a120c050906090d020d1103010b011704020d0201091505030103030305060609180c04051302031602031201030618050114150a061b 77
    0x40101071200d240c3e40c1c50102c2050b80c85240c41d8120b5001950f41103440d00c61002081c4411001c07141c801c2c0010601d241d00da880c0c50b10b4062441c003115009422443c0c0f052601d140d605001c07813030b00203807095400000c8070600756900040a84110001d681e00300b00000d0505401001840755180d5a8414071010804c0c00265440c2600c07040c085500070300e51403480c0d03404d10f0b2a5000c10f2350404868171a518003085150154001c0ea001e43d50710f40440000b0a840d82c4a50820004004600041e41013010a80c80820529601628080d1201580e120720762290b1442c5001001e85c0c80040c0114040d20081c4140c0d145501c5031424000b140e80000703412002c1da9900569401c2c1c038001c036445140d00100d00b048c0c61132445407560046003c3d5000d0805903a042c404110181d81e68402d03699904004406a0010400308000d5445060158460708003814090440d072075050940d00c14843c03a00390500c44900b80046040500781c141c003100070a40390400072602c1e000c030181c42898000154074140f00c503c1c1021042080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 325122500 1250 325121250 325121281
    0x3030f08180f010902040b01020a050604170909130b07030e0303040308071e1106010e01030f0803060109120317011703181216140409150c02010b130903080a060b04050603 75
    0x40d22003100c9080d1406090b16000e40342204007a40035500c0c204110f00c0c01c0d48041407403079501c2d8000c40203107029282c44d5507841c2414141942d96030503000605c100b01c01560307260049809030030303024600c1c61100c5041c1000541460058110420702d0314210032000603103404000e90703920075014200189a0307503c03d4010b0b50300d520603001c03d4110403040a040007005801246051180c101d5900302c400c07a80e01c1d080221a130007800c3c000500103c00328102007001585540086030f0041062400d001d40554a8030100380c03095500301d0440104003540110611000081440d600400740c5420003032400f042e41e581140c40e8030907101c41101d4841c0549041030701d45c40300c82420b0080b00c000d03001c50703103407035019041c050001c800c0b40240b401c2e2070030140500c0f0207454640900780907c1d80000400440d8403030300245000030320300c0d00102030541d503d600c00118595901c4e20304443c0c2040448001c55222807910300240010001803034403094500c0c00d081402500c508034142c4042da4016503e00b40d4a8440010065a004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 325123750 1250 325122500 325122541
    0xc1b030436050112150b0102030301050d17070b010503060708010303050d09021203070503040807080f0c010503190f05070905090c0304060902120a030509100f270302041803021603030f08 82
    0x24140b400004103c441c0400b40b10f0898080d030781d01000740d040c1c500d071030701586d441c40201801640148014015842c0c458100c04445110b48140765103803074080b0840c06c154101d000103940d0b0b00322070b4004200d603090600c210780d8800e2862030b0140c000d41c1580e401410b0790081c0100c408102d680d40c808181103444510420311108920412030343c5135a00380c544559268040c1c0a01c8842c0d01903604001000c900009101c880300c030b0400c003e8264403003014011911500001e2100c1c01e114100c040002c0001c81ca44a0320000307a95514012540b4506020003400001065101d070f801130000f08100480c0180c0a41580e0304980d019001040510f200d000281e01d8032070090f20000a4045c64020500300760700311005044110013601c0080d140b203008101079641c442c2071181c20002c0703558404c0c0c1448000c085058000b082c95450b600900058980c0c000c601103680069081d60320118001060007411b0301008408503007040a4164240346003943d07001003c102604010300d00b0b0050690106010302d900d0b501c40034882c0e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 325125000 1250 325123750 325123859
    0x105010b03040606050306010f06080703110703090501080c1206060309210304060b090105010503040605070210020406030204050427060504150c08150411040611070e0c1b0304 77
    0x658450412980503802074a0403100302e881c0c0300c00003415040100300b10741207c048103e41c401d032529103403040c0c0d400b03c4000c000d9401c042c0d6502c03201400e4200c0300060240d0f18000c1d51241d00311410840054103e20028086142c1c1000501004601c0c0401041c0786500071010f868041e140c2d02d41c00344407441d20303a20800e0f010700b08403900001040030a645001d1845103010792070901160000c0301c20b01c49004030a000301c40c00180104001404100c0580003079800051600c1101e010801c14000303441281c01980000380065000181000245064010b51380c00c1548146013000440740168020509015003c0c003c010a495400041c18400080d8103217580c99041d01c0140241d8100d05c80080c01d180c800c4807540702d41244004e1115803810980308001c1005854204503152a00b010025142c10144039200001031158400c08603000a01240c01f0340103418003012142c9880f080701c96040304000e4035040d8141d551090100b040280c01c05151090072651415118a80034505299040c00da0380301185175002d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 325126250 1250 325125000 325125011
    0x120b0a1701021201182007030e0f0603160e0a0602030a0c0c0b0d140906091905070315051602190b1510021e0303061f0c151a0303070215090406030501 66
    0x1486000c005d400d00c0480007a4100055a00041303004000c222148164500000c28004800080c1c0240303406001078400a0441048104100024070a0342c0100c83d288110502c001540d03003195041400e82d0b070341329000c4441311349081c20558001c0d500d01a0003000c20800a214000e5403e1080c070b0003062010b4920120b045c0c4e0b54107030320071600c0e010300249400e0700070648640e800075035405008907c184c011542c5c0c4000e0710011942c8852004c100c0901441942c060250500c000f00056400e1a0400c0e041140d0101140924142da035101e41c442000d01e95000399005861856000400003220000b800e45c801442000e641f02e040320008400e0708048180d0304080361541c0000000e800241d801c001c45491648406014a24603106803031780001e407041601701d040d5070304170603140860b550400174049207448e114446000d1915803404d034020042c00c3c002019a00d0501c01d21098040d2030621700f8190540041d480d00c40d455000c40e40414851144101c488404070307000c20b80c1c1c0e4032500044000c42d0808000d010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 325127500 1250 325126250 325126259
    0x17030403020c10020309280b0c0f0706020a0515070504080a0b0a2003060603060402280f09060206190f0f0f050604050603060a11090a0303050901120b0a1701021201 72
    0x42d00c40200001c60f110704602d250f020b41c07052002003140c04401014041c0450b04031140d45a0304080c03145072846042d000041c90120381c400d00d8030f01a00c0c0f4101c18100401c05c09c440c0c080d05178140031a5400c62411904800101000f141c2c0c00201498486946c98450380c10340c0d03e80030b044a03203000b56003101d1080e0244801030024007032282c009901031104180c042180d00340c6100c504000c10280074024a9110040c000038000c0d240940180d5846070700a8805071503d00340385903440514010b60351391545904c803580c11007441c81d0f04c002c0305e801c443c109082840c4000c0c1054406941d4030801000a07110503000041c0141d8410030f904141c43c4001c039a0418003071614103140300c80113070880500f401c00007890540042d031980b6050040303a0003004007401030022612185ca103c80a0000407104481142c81000b2148440d280d10106000441c06039681c60707200c43c591000107060350500f500824981e401c040c1c61000c2136681800788400c0710360380c005800d500100b0241d03080c061700458a1081d00c0d0b03680343c400001e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 325128750 1250 325127500 325127503
    0x1171303120507020a1401090b010f0806160c060c18080f061005181509010605030702010b04360c0801150801020307020604020f0609220e01090209040f1703040302 72
    0x8044500c240c03503a50480300c5101c0318004690007101d5860059010a00c16004101080b111001c28040400003080c10002601c1e40c542c07080081c2d00c06850724000c420100100041400450b03048008452401740314001c54600414034505240040c0905a0700c8040c000c50900416101c00d1422100103840300c0f00c1c0e503500d0316580310a180881c0e12154000c030000a82d2044c10384104d081a0342d0000c01601d607400603100361040281780209851246884000926841d5840310b0616001b04080c0c0e443d40d5892070461340c000d003900d503240000f901950811000e202d825504a204201c0880d448407612030b441030740c0c0c50303011282c0200705014044103000d40c03010401c01c5045d003085e07170210000c0741405485542d078100e1500302c1c0700c01c607044070058103c04042401882e00c1843c07030420030310003060b0605180c20340002030b800c9a03110422001589001403902d616002d240610480d10852800800c080500e64010860010004200500100e00300c0200801c0242e6034800451001f0000320711502c0303160501e0040e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 325130000 1250 325128750 325128781
    0x1020a020708070e0c0c0304030f050c01031d060402270a2c070501180302041401030312020a0813051e0601031a010b0702010c020109090906020405040e0d020a08090117 74
    0x4000500418030007040c8802c0c0060120100c4a848100c500503a44100c0b100350560405440c180c0d003800704100000105418400008105018002501400c20504005401c4a180c614030070003810a06070399005502021a44c281d100303805032440c8805c8a5122550648038940c0e00e40f0103031003120b140c103201c841d903030641c01030b03044d0140414152028640e24207101082d000300b903000462684920300034403295200b400505400c0c0c0e50391176a001c0036038803580002c042d1409155054801400c44004005140c0c2c40480800082c1c5541c401f1854258010750040166100400d122290060031004a0030450100900301690614200b1119019092200e03517840d41401e2100782c80070102c5c9a51400c100000d14001412561820004bc0c41c1c00b00e1940191289801880264180000e00c10006181415401172030243d6116070070060b5214108010401101c00c2071124440c2e81d070041000352900c03500080d05a840701d07004400346454110540040b43c00803540d016515024190340d092240201900041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 325131250 1250 325130000 325130017
    0x801050133020c120a1709060a030e1603030203030906010609060905060906070c0e16090e06010804140d020304080106140306041401020706020406030b011209030f11010b090915010b0909191b020102 87
    0x980f006840c56880d000428003487c903000c0e81c000d03010044041071f980290700c600e003d2203010040e00c517510880c41c058000101507603c10350160b0400020003601e09014405580908254107280d008581001c030028840003850050f40c0c051034001985e0f80555940748207031006691312030b0348034a60503111880414292000e44090100b03954120059901c40c2c000c0a1000951f07040c02e4042ea01580c50b40011252440c0291084c0d821142945507654105801d2008041c0c49606030000e50380c0320714040e911803c5464940c0a80c111500350140d00d600c42e900400c000d0b4005d9040224030b604458010300c040e0091064040c014101480081d0000c0c540390103801002203030b20241c030380c15880c4140484d03840c00d0720146040240040d80b8004051050342c01510b0500f5a0031400000080c0c40b0f8103500401c90104090b81c49400f181d00201c80882c1c1c1c3c00fa4244c01c2805414903400041c2080020b20100d5107110703010701031001e40301c03810040e2020002e00d5402404080c1a507950307041e4039091024040c2c002e5004111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 325132500 1250 325131250 325131263
    0xb01120c0f020d30021621111005180d03140c07050d0809030408010518012f070303270b0a0b0f0616140105010801050133020c120a 58
    0xf1401500740211002e190401d140c03460b2424800180140031110f00c10350300c1001c0603560a118414240307480000e201c8156101d41d508001030403200d035102020801c01c4038030a0801c84031910314900c00d0b0021440195021910b0008211602d03091f951261004e6600745181c018480c0f40c1070551942d60581008484490030500041c1c180ca0301840c00707102d071007541e0b000b9000394440c2e14004a450700c1004119800704540c802e60381031546840a082c2511015500c08541101c9000c3c4021002002c0c0315480b25420790a05801407038030005c82100c01c000c1c0c1800400003a82d0041800401d140c060780080c1d1243c501401d40800840004807842020076094400340c481e1181c0100141034045944a07a01400d00d0047c000307a5030818030030401000c0d60080c04403903168540c0c1e2a0401c00114280c1c94090350300c0c0d80d5800480c03a507040c540d800342102c40c16401007040804010b0004034034680021141c0d048808100c10601911420400381d2130145808901904003c00b625142a00180070400b80c07000d5100e82c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 325133750 1250 325132500 325132513
    0x720151513051b04030302060f150a06080a0b030105061807120203012d051804080702030703050d08060a060503061e060a0513050301060501080f0a0605030303040c030516030c090b01120c0f02 84
    0x3038001c1c0070f0f4001c0703020007001b6a200301c010401034001007140c1d80c2d0141d460300d4042602070b102800b01c4c038208900d81c0488045800c440901c0a40f908a0242d0004c080c02a4001c011506e415400241484a0740d60914000303190940801c00c4540b10b481055a44070f10a60159940c3d6980d610102c0300c01404601a4650440804c1800340d10006010107411103000401d0045008600a4040441c00e00900700302d420400400c8050010384007404004000c40c040c82c098042c2202c6140c000c1c00d2000000e01740c0303105940388441405080d0300030003620b03040041510400540c140c00c0b86503400b04041c0b0751426034040d03c049611181d044c0e200b002441d2200d450343d070707051081d507450040c54280d032030602415012882241c002001e200d06841311942c00280410003140d01c658403000700c0e086078415181a41c031030411803400d00c02e0180070082c9004c0c80e451040c030481c00d14910b495070118240280501800640c84000c00c507100e030300c1542c01c2034504a0311102005a00d03450714000e850362140d0350694001d0b0140c070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 325135000 1250 325133750 325133791
    0x2607050106032009151c0b010e040209100e01030b0430020f070b09040b0105070f0303050115080405100510080717070e2406071a072015151305 63
    0x442145005542000000e0541c450303070804c00c4032610440011082c0d1415102140d1b000c1403015007103a00030460500d50303504504090050100c0483c0003001302c09a120814020010a000c0c4481d0310304494009030718944549543c600740f410f90802810f20600c0030000640d141c0e0f046481155080b000c0003c4e004c0b80c0da4400207084203a00c03258184121144110288010003013420190011409010140342880c90810743e542d8249000000c05000e83c002695000107110b01c4450203000101d525160400e49507501d01030740ea06544840d0000401c01e466200c101054803075900300f124078080c2c60102c054816070358942402e0808200c940c1e481503024402d03074400003403020760601914003a41008143d85215541181c10f0b10395a1001201150007400400000003c205045902c0385000c80701c01d1400b519003010140180741d1210031844481c06e42280b58040480726001984c000716444d100c482d07542e2956541400449984810902500700c411a001801c0d848007a9004900c50b105c01549560120b511 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 325136250 1250 325135000 325135009
    0xf05060f060a03020a14240717030c181908010b090a09020a03030f02070909030f11032d04120305120115080411030a05030c010b011b26070501060320 66
    0x701c2c88040d400031943c107028001c0041421400581c2100038110400c80801c00c3c0f05142e0b054680f69807840303551f00c041280c0c401c2049d48081d0320b611429207540c00f415800d041d00f07048241d01c20100c00c0100550300750581c1e42c4944444400c86032015581e0a407079403650342d0f41c40b480d01030b0400600c0c851041c0c080c0000220422198421258102c3d000f40c946940d85040d0381d4203036141c1000c8585001544070707260b80091400d0f8a03011300d0005502c00e98420310441100f50f0003401c11064141c1e55003040e041448104014041001c10700d07400907141990801c03c1034042800100ea21943e004000c000801c1c141072003e05400030700901c220141e211001056a0740c1e034020104600c06581800c0004403003602080c00f049000181c9000984003d040c0d030185000d5580b801d25541c4242e90000641c2d4507160071800540e0003600f110100002441d20fa1514080c954400c0c4031041c0c510701e0b1101d040101c1c868008040b56410076220800d80c0300000700a41912030803c4e015408051420001c4400c101c2c44902507400d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 325137500 1250 325136250 325136269
    0x17041d060a03380c040501110c09040f12020c03120a0908070e01170304180c0e0306010602160b182b0818010c02031b0d060212070e060c060a090305070f05060f06 71
    0x132041900d07003003c1c104001103a0325030201d00705500710720a14a8100096079040d44060080c0e2090519190103925031419580e054082c6d82118155002400300c054580c40114100c403c50010100c0150b44a00034002901c000801b078000c1c00c680e20480d100440c03070020716038446040c2c03641001c2110914001079001560781c40fa0340504c079404000c0070401400e141c1d0a401c054110400ca0030b100e482c1068010219140c03a6090380144016030000c80340d1241c11641140c910302401203541e440307180c00301c04216000c425031101d940d20f0091011003508002d030000a100104428040c50041250426606051089811441100c50360780c445200c94070b0b46601582008000c0d9a001c0d01070721300104400c503d1210b80d000a245190464030790848040040e86500c020a130707030001c40040d4101c84c2080c5100400d00a51201310a02540d01009101030b4100e000888640c01128100080f07040b02c0b103460101e4036801500302c002c1c0b052409008840030402c012407213512034940c21050344416503604003041400407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 325138750 1250 325137500 325137511
    0xa1103031e07020607050102160c05120606090c1c0b0907031a0409051903021c05070c0905070306090608010207020102060f0618040206090d0b0417041d060a0338 71
    0x551106800c02103107010007070300d21140010204ea051042d9030300d075582a03134410382642c65000c42a180c080d081007011350f45580a04010340e415040951548525070b601c14000e041c403841124054001110804404100c8080b900d0621244040e802c0e61807880001d40b4124222920030b000b00400103000500c6885502000c0e401c0e203040009009a0700c05000040c590680259414000c0380000014084511388036400b0703d1080c0d00a00070381032000074542c901c07a00f6003001010044200074001c003090448091b04192000700c14005442d4a5283c0c0940c0201051340c0072142c0c007814044006442181980540401c1d03000f0703000d0b6178660343c4102507183d0452080724255408118202d13900440c8541c1600303c0d83c80361000d80418030380603140c0000303540e0380b05440084401182c81c030100400c02c090b211000241c1c6015000c11801c0c43d0800d407131100000e0080901700348aa41c0c0400042c0365580b044440c100841e0000070824103e05900305c6a980005201103c201c42c0070980e00107c20100e0300c400044c4101d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 325140000 1250 325138750 325138777
    0x9010906030c02101505030c12030a0513051306080c030c010203180109030f050c0109080a0b0103030305070210110a0f09030c120201050c060106120515100503060409140a110303 78
    0x850400100760010098000c04600714401c5500c0003205136041e01c210f900e6031000c6124107140e82e103818105032405507002a4030340190b4180290900316200001075984d840c0c1c103410300c075403510b1801c994640343c072034507504c5154004200503802c0c40c601c24980c003c02c01d442c640401d03544000150340506640c3c0802510701401a8410000105450b620711060702409a051425a4800b42e80392030308580c18003843d03403d444035003003002c0075011580c2105000000301040000703440020b4844c0c461411070501484094203040d120360000d00030074400e1114112103c1454010441d0000840d0071032950b42211b81010003282450400005490250880000300c1398080030368040386040521503c0403040d00c49089041c400144500e5200d03640c2848a20701030400382da6030704002c0f800c0030782800a994000e0000e21064072350004082c855220268514510042420225030f00c0e10340074081801032040c204050825045000c0302404c0c2800807c03000140c178000c0e00500c032514010410981c0fa8401e4a00300c0c03d88 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 325141250 1250 325140000 325140017
    0x8120a1a010e04110408061009060812180d050303090a0c212616030f0504051819061e05030102030c03190204091a090108010203092806060b1e0901 65
    0x8928040c4c0101c104482e03c28009820f1640e184a0b941c68624140c608403204d196620091210740400c0c0300343c00040c0400341c0144201d042c0c0980d00041c034031070030040d001ca45401c07070000c510580383d151680020a51010441e81d407403405d00e03802c6464030311899080320380411303034040050540c0c69440100385084c09203a0070300300400d403542c401600b1006100e10510303c1036040ba4205250310003030080d0048140c940c0740002e00403640d150050640e4502d0051209008007404144015104c1c4901c1a100014145a402254803418801401d00c54064407500805091560200341d14460b0301e850b045c40c2096000290109031503100301405c2c0d0000701c3c0c03040303c01c510900000b4810480d00b0711082d4030300f83c0724a00524007501c401c2d4400640f18a50014401d00c144030310103103850b00b1700b90000c5005080c0c10008600714102509016181c00c5850082c104003a240110284200b1070107101075a01a8030101c100000c1d0340c4c1e04c0a10002d5007010450920034101038100388001003200046545228059680c03101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 325142500 1250 325141250 325141277
    0x8130602061504090f171201050a0f030b131502040807081207030c0c08010f020909070f0509060d02210405060703150501050a0c1202010501050f010c0804061b08120a1a01 75
    0x13042d026a040e036110100c502a07201086100b84e1002141d02020703581603556446002c1c44190301410382c040340c050408420100900301400e1008800d5076441004405543c640085095034021009800340c80c1d20001c1407640085070700f503402001107031409000d075000b80c0d0f0b131102c0301626403402c1070310341c40400010030403040020b1003058541000d52084c501c001249450b55015401c5a00440c000c4045a40c00545d05400c5e01c2d10a8045600c68101d140c1450008080320700104a80225031103180206001b1981b00c60f003100580680d4201d0200e000c00e0411581070103d5803909960548050300c2502030382c000309144512a004282e4441200c803410f980c140d19003030045405a2190b0221410000e0700707094080040d0360001803601c40e0182d42d0000c80d09504050400454080300b07204181400082c03404080050582c0301903404071911070400c4103980803072038a110550800c105005090030000a0346d21000c050004105024421015041141e0304000c4c03401c810020229002d580070442d03030a0380c2036 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 325143750 1250 325142500 325142509
    0x30b04091707020315090706091e090b01030e011505090f13080f090d0c030c090e1c02070305060906040b0c0a120906020d0903051902031309020f1204081306020615 72
    0xc080b500c06000c03501c2d05001011100300b422800d03610744525403c69903003040b509038400800c1c030141c03070b50801403e00743d400c440ba8400380001c0da100300d500b03e58a442d0010340700e03030080d445140f03900ca00c1c40090000d0243c42400041181480c0500e41c415005800864554100f41000c28420031801681a02017045500c1708a4075800c0f8607040300c0050310403c040310480c0c8642c20b240d600c20b880340140311450b84c2035141940039407a00e6007061000601d4001d940801c1e41001400c9200414251500110340c03110350002c0b0300b0300503503400c00750480c410142408544480001d1852242c0e0051041204507140e4013818203051040500c588001111140f80001c0183c15501c00e010076441201c0042c07038075444981c040d0984075042e00a0b00824030110f0501201c031900c01c01d810103030043d8030141d4607002ca0307140c40e01003c684c00e002d0421120350100d0380ea03d03400306010072a01d90710410440c0e10903510317141c6003084c4681d0000d5a10203480d04a83d20025940b400090001c1c01010524680b60041c6040c4080c0f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 325145000 1250 325143750 325143757
    0xf080a060209191e0504020c0706110a02030d120f0605060724050c1c0608120d06030804090204080d0207050f1207030b0114091b03042012070501030b040917 69
    0x696000790f0780054503408803004040b00004103a00d0142040c0c01c4510101294440d125a124900982c01040b190151880c0801e401e01a9190381c2001420041883c016500d080f600c0b81c0020341511501d03040c00c03149600008180392162003100c06004201000f10900f0a4500c14410290030620030302c12000003c80704007060100034440361300c3c0303034100035110071401c00e03600181c3d41c180710f42c800040c240440c50300341c1d90310741900b140c41c24041c09498034140046568038101103180d46551004602810552141d4100c0380007550400ca155441710748541c0004004d5001b0320400159208030b05c120000d10340082031106c11510020920001251608140b080340003840e0032821182c003c0c040c0100001d40620f40c0c06001c0c1001c0d02e00039240c90071030b038280014840080c15991180d1104400002d526840e042240d034031a03400100d808000407031a0030042d4100030404543ea200e1621030301000a5100004ca0a003251000d03642070010114507024807040b5081403c0207440d03901c0f564100114580c9a4008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 325146250 1250 325145000 325145017
    0x61e0d1203020c070306050106020d05040f1214030c010c1106071409150c01050103060b0d0f110609040c0804170f04094b3b0a0b100f080a0602 63
    0x16141840307503040903007000c1e41178104071495540d5400610109030b042010010308407103810043d00e41400c1c5122010160043c4c03090002c4051075495078001c01048588130028143c00004030380e140c10404041c2c070b001e80780000d10312000a20a20204c44c8104000503528015407003519058131241036400c0c4240345910241c1d00a400105518036000d00801780002040181340f140000241d5504502d0b0407400d65000c03003500c521500c811401c0401040044000f00c48266001845000c4d041e007000124006000714280b481e0300c81e103054a402c0e2010f400422151040303200340419204401e041c8501c441600a2140032440e4090501c4284016900c59005107180d10707403a01400820b061060b68040e490780f03030402d0784d64031742d800300318107011004202d41800740c01841e10014007078001042281e41d50b087d1500030801c2c0030f003102880c8440c0c0107540c05078101d4034100101030703920001150811154005094500c0640c0071600003002404030030400c045c20580b0030342405011102900d441d8000030313420500e81e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 325147500 1250 325146250 325146257
    0xb0609130b01110304030602040f1a03070f182405180909030c19150b0609010806040e070801090b090c010807120b0307030f030f03090c050d0f050102030c03061e0d12 73
    0x2080e101c5003e003000a000110320402026035900d0400300014211001507020100c100440c00c010803201c0c1081c82540e90041d0039140c8045140c4903400201c8442c0030706a001c0e400381c1140140400d550121510a110491000c2c10343c0c8104200d143d41161284038505940c00081c0c60b05800709450314110308071030741002202c021070341019901c6081c1d40c01c007041c0314509415440d81054000400c0103410510840e01c8804004008021415011409c24850014502e04006807407001400a1351264060502c00c80410112001a0745600e2098000c203450b00d400c1d2465040800000c0c5650400583c0b4040d248042e0364a480c10b4551050644111014442c9624401c2c0c4501c0881016102000b500c0300071130140448450740108d81c04c01400064410f4a907404040c141200394021270f00b005011400c88405a40d02d8112049a04044500855071b001c010b01d1540000207100481152801460090104a501d19010003402083e20300302c0c0f11318002907800c1610401d440c0b0104001d000050021003d03410b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 325148750 1250 325147500 325147517
    0xb240901110d020708150c0307030f0207050706020c0a09050c0409181a190203070e0111010603080f030405060c1e07020127030c050d031b1112100b0609130b01 70
    0x1001c0c81d0a000c281801e00c401079100010800640d0b204010444a01c044508507040b02e0401a5045040748002000c0310241916004280f07070188150341107406568100302620051900c5000003503d40c10002545d601c94044404081110402da00c9407038003070507806094a240c076240420000c0034107034142ea13130798800070303d00190800301d007500001e0034070b4643c01c02100d0300f01d1804000008030b611000700381010240c4148100119035030000080e000c5c041003424182ca5511040e82e00902400641e000109104800301c0d04500903a40c50005e03500942c410b0303060324410740d05d00b0b0200340710740074166031350800b0424030840750318080390103000301610350041c5440303d940c3c60402d60800403c40251512615140494001c00038810404201c002501c4220f51a6402e420176880060607000d0b030040c20440000104441010411054501001c600d000f0b0041070120780113a40341610303000b4002100700818200240c03801d00e0300d000b00482c1c201e000c005111030452101051034400606c2c030420a541400380d0311 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 325150000 1250 325148750 325148777
    0x1605070804090605090a0c0c030e0604090212041a071709011103010803130503010506060406050f0405040e0f0d02010204240905150705120f04030312060317040602010b240901 77
    0x30041015000b0040d0100340640380c8004c1c07041714140104280111494003481004c52503110601c400103c0d011300d4012600314171540090f0701441250301004019100103a82400700d202c23590780c00c1c0310324000e04101d0000843e0b1003000da48600210345040010b10191645101441440415908010144000101c04103503581c0d02c1c000b54004c1c0c001c08050351000c41e4803c68007082c480d400015090940007400b4500300319011508900981c010172007032040c007003208000c520014041c1d60050070020403c0c0540352241c0d090540b11035402d80b801c5c6040c0102d2148501c128014001c660448075509000a81e001c1031601d000b400319081c3e400c0500304682030720006000d9a656030024060761400c142155120000d01d481c3c2d03d002c22a01c14802c0400c800d0010308208044c0105460440307425060a02850fa00141828002c1401d074000030400303c401494214080940d10113041911101d0b002001189618001c000c03c1c41d20603400d03106840e03901d0b168a1540703609840540f0001d18181400340c48140c44 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 325151250 1250 325150000 325150013
    0x1809020406030b150a060f05070f0501050f0f090c010c11030f06240d080909090a0b1303030b120a17070804031511031905100b03040605060108011d160507 68
    0xa030b803090b41c0c0f4000110620064000c00c840e82d50310100100c540c9801d140c40d190020b40300209a402e280144100031642c0001c0c03212181d030000c40d103a8000300821880c540f00703a496402c90000d842c1c00034403144110004588640c0001c1501500b10140c48445482d08180d0742c0c03591a6091015680d0513000300f10003107010880800400303029a421003058884040d0300c0d50150028840d05440303504c81d520078804007021407044021a006800180c0e4111186e40e92015007926100110b240144a64100810041c1c1c00e032840f01402c3e0640c0c8242c1c1c06200021f4901c040001c100e915800c80462508002d5110300091508108000c032461005151410701c2056140c1c4290b60b00198410f03282c500e0300009050801b0030912641c0c1e00d20200070105800c6080c02d501100140b1400c00c2d1800070b243ea21804942401040d40f01e010062108051040d56407070070b40f40220140c1002e0340c040e07010403a0340e000820740700c0c8070301401d10984942901c40303c800d40d10034150000326413090390440d052200420490300071610 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 325152500 1250 325151250 325151261
    0x60510060206040b1b0a020c03240103060e07031505060925031505100509030709020715020313080d0c031505101211040e0f0f0c04030f11090711070b07050718090204 73
    0x40c0e03a00600701d0308d10108241414015113014600c582c484150122490b11402c0380d503941940d0304a81300151030310887c00118946100b80c2c20143c494190803042020f00819900034030320994045d80c00b41c0c0c0c692543c66011044c940c0d03001e105007404c0c1201c80c1003604a8403d60044000d4660078503030030030325903490003c078a20341004410400020400501c01150341410840c40004154042c4c0071840e045454860000d8440749081d02c0c105250004046611400c50b4625072003900c0d00410003d94859803041c8840c0281040030410020a0070410f560005101080c101000c07502c1c050221400302d12158400c4800341c44003000c4e00c8205645a101c0101c0341c074880060006000f107006031681c281407594a003491030800a0031b00751603035440c1003000178441c00a810b0340d08517a030201d1440c1c030024040c07400300c00c401c0407180069003210701c080030810400c1e8480582010464500c080d214940e4841aa05c02644a6048054601c0d40200d4040040aa40009155011201440004901c00c040e4000b40a58a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 325153750 1250 325152500 325152517
    0x6090b0d06020c0c1c06060e1506210f04020f0f0f01030b03011d0f0f28050c300613020d26130602030c0a060c11100504060510060206040b1b 62
    0x3400c800301008006c9135100e4103026100c2e08034244d595107803034070501024020541450b0302501c40403030380c4c0c1c2099540749003044038115602c404102d54a81140c0b445070312034080360281d03c00d041070030b200096070030001e0040702c80c0000580520a10220200190050001c105041d50150b6031428890301300b0281d81810705803c40384201a185410200c1c0c1d800c0d1500c0d00e034586181c241e130080ca81c0c2034104202050f2081042080320001d0401513050700f400c0381040c02c81007a640c0c00c44400148000b091804c1e40401480c03910a0f0042c050f91225405225940d1004490600684080302c04080c054500040e40c900107074840e490301122001907542012081d0082119071550303810119040e80c1b44002c80403d5805060544000c3d030501d0700e5507401070380e1586002c00103040250f403902d0280c01c2e64480c400f05880154404100e4840006000070000107200c102c8040e503445280074040f9003021145889401141e0315079008106544494a1f400c021000203855003800c002415400300c844500c0001800c4d502 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 325155000 1250 325153750 325153789
    0x2090a3609050123010501030507030204050d2612060d020a03080705101a03030d0c050d020a05030411010302040e0403111e210c07060305060402090901150306090b0d06020c0c 77
    0x1251400d40d003900d00c030328280000c2a0314082c009492130007180c1070904484091a0108017a00c402400354000d2080d5000380d40c008908070390250502521008480740002d410000b074a902001c0500b84070907005000d11015018181300100b001890700c0074240b100c442c0010306070385003540d5940e039040f2390b0351008504580b56004645000000c0125224201000208480e829441890880040d480744034045042031550303038440c050076500b4401c006031404002041c408650704d03a40103070701a2194004580440d80d0910340960300d80c05500c280241d80884050070100d0400d616940d41c16240310450b000d030000f50344246405801d2912400005005804103040505484c0001c0119101e000c0040640e084074180701301704115a65000003030a0040310700d1483d00007025201e110008001c3e100e40b002072944103280c2e0001048a46061002e00e90900e2140c4040000594640481080e9490a10119840106104088c001ca08282c00a14000e07198034180c0341e2402c0b86c07100091685c0c04180f006c1811 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 325156250 1250 325155000 325155011
    0x4060303080906090c010c0b0901060506040b071106070201050406140d021204141506120c040501170706030903021207080c070b04061403090703021002070801110304060b0402090a36 80
    0xa070300c0203015244d0810515009050a052601e0020700203104c8840020001000300000900c80e40080d0f000b01d018000060645654587d600e000307810903049042c0c1900c5923442003c285503071303281c581c04580310303141d041e11914106803410078250b800076490040020051010081e0101000c06440200900078111461054508181c14410079517904041c2d07100301d56201100b20f071f040ca80c1160420340d024004a86141021011400e840e08040149841301c1c0c1140c200000440c01001204d03e40d0701c80000700080703400341561003004a0039502c5909000e805600030300780300d414808102c4010702403980109160f41c501784500704554501040c81e4040008450007080c2407081603801003071072a1102c800100d5034114100000c4040d2600e41922000f84500c0e0b15400381d045d05030003401800300074000500200000071562403440d400d584111401c8850625100c01c0f0541c616061091303552914002c1c02e0402490304001341d142e103c200800d0305131304241004024010315086c3c1780ca40e1280c4503c90300301044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 325157500 1250 325156250 325156261
    0x106080415050702030712030203070c06050901020909040501050612160303080601050c0a120e1504090203041103060411031509101e020c16050a0b0d0902130c390609110406030308 79
    0x101c07c461380c848808050040080c80000ca5114401c032240030b401190010362070700c030440040d0083c400c000c025500300b01c42a01b00018800c046d40404e01c940d0007500d11480c0c600380e4549013900d402086c150040307003c4110b2400e00c0802c0c07282d0a03c035801881814050324140c0030702000c80c50682c030010201c940042006000481303591140d003400030f01d03100390b401b905005500389125056000340c2c01445036940e07001c00044d090080001c1141c9080101074107594039400d050922184040c001d000c242c0c024810000d081000e1000140030070720540840e809045065010290b050180c00318030f02058007a190a0210300c000c8000d4402410407a05120040032021a69460f201f40003c0030f0b8880c034403400d146103040002010701d2084400310b00702081d0000786c0c0802c2d84002540c1d50031400c1c01003030b500d107414400300e0307181d406c25a800c08000300c0d007210055107541030465990f1425480111407810509150100003d8040c0d0010320a01e4401c10040c15480c00c10310114003210320aa00541c00100004140b00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 325158750 1250 325157500 325157513
    0x902090c0307090b09150304020d0602031f0509040320250f08070305150a0e030d05061206090705010c0201050d0c02010606110c0105070b0901140405030d0f050f01060804150507020307 81
    0x30003c011454203941810040c00000b00070411121584072a1b41000000408550b00c000c0c903080b142e80d0050045449040140207100440003140d1007110a140700300c0b0220b11894102030003442280c4c51796403040c0901080c00460501c0005104c00c0d42248101612038102d000880d51250440116204014030700e85000c040c9840c02096601481e21600f1811040c40420404120005001c0d1445101c0d01c942d00c5030081003000700f102c0100c2100c01e01020910420103107050300014040c0d10708031010002c03d98040f1102d92140300c10b985001d0a5800400100000d50140b03241d04861401410803030700382420a4010410f8501450032480141d6540341d09101031a040b0f8040e006240c04100100022020b090000c1d04a1180702d2024041421410018100e020250031250302e0345101508948103003045d140c06c40d5640c1280428140560800560042c0140c181c8142445226204195103241e481e00c002903400800103081078513400361014008490903460301809004010b45e40c01555070388403904040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 325160000 1250 325158750 325158767
    0x3070b04200d030f090621180c1409060f0d1103010b0618030607020a030203030a110d0c181208090603040f0b090f06010b0901021c02010b0d062a0804080d0902090c0307 74
    0x41b01401b10f1001010210406401c080c00366584090000074040103000c80741c00c00c64411a40140441c0c0800400708141481111840713170031105444500c01511030904010070f02403210030141e0040c09551005011030302405480450301030240002a0008845c2c000c0340240d408008184014180c104030301c021400c04122a503072090651014000002156038025102d2002508081a0503200c04030340c0165001001194a91110000d003040b1001500b6000f500340d900e0780481084288003000d00050f00050f042203034a41c1c90340540a145020230520802c07480d41c0014000303480f00c1c819029454005021540814041c0c030002004003070010000006625025058018401c89541846280aa642c002600c0105402c0a84c00302084001e2084e08070300401d0400c4d442a48030300025a4501401400ea000741d00d0f024250312828148240c01344002c031a1200401c0420000b8803800001c2d010480303142c0a4201070000e030902041c40001500019410703d010384d069944c41c8000824800c0072900300001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 325161250 1250 325160000 325160009
    0x4020d090c050906120a1202070b0304140106060915080a0e0d0801080d0e010c0f030212030a020408010f060f05010c050f0a080306090907051f20010b090903070b04200d030f09 77
    0x952410807603100e41720344800c141c03240280b0116105c0d4010003224003c1c0091400340411841250720b91a050038030103a842a00400000c0952038200c000c03d00c03520a645a4003078408104020600c03c0315801c00b2503100000400f02c6801c00c0d616840a002e2420601c401b50191900e903070783c5503d6505060059003084103a0209409010035400c40c0c88140c2d0b000000701c102941c01016005084200c0d0174240e0030301e047d556000440e00c2c0300208004601280381d002e002600d480a0003004054a11000d5030103d84541c06281110342001d1020441b562190246100c048d210f08141e40800c00c0003142d592604071108412500300c00007008125a508054000030390101c1103c00501c80e42c0c1c9004045134660a84496070040c00300f03511082803105010702d420400001c030824020002010704a0344c03a00918103030705140c0c8034444000100303614580010aa42203117030001d00840c0b02d51070320b545000c800e00c040001c03680070080f100785a0205030740d14080188014042d03201c991211441410050440649411 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 325162500 1250 325161250 325161259
    0x20406080120090a05130b09040b16020f19081201030b190504260403170703090e010803030705161a010f0801020c0c0613030506090304080709020711090604020d090c050906 76
    0x4048480e5030313001c030410480f0425102c1000150440c18104080c2507080541c6400a10103c24001000f00441c465031240d440707460b8807107011118000480e2074501d49014948540d00c408501c440c4003c04050006040340b1581d07081c0d2504010b401c03c4103807041d09038000e4901d446481d04000c2588144007641c000c0c4060880c04000030b03e42a9104c940e07813415007900400c0d5100b00429003000c0c00d500e800700d6011b19000a04900e03100000d5500c04c0c000d500c000303401c80000d84840d8000448245240400b4142c1c0c2100025501b1681d54150031034940d08559084001403808800c88004a076010b001d5a2a5003031a602d00d241a40c1840303c0d6075080348450317000c91800d030b01c100050511120046500c082e07000342283e0007583c540109060017001c2100c0d420107001c070b00806080c000841ca0010060088400c0181500c030307442e6032071080401f2800394100c003410782030020303896414a20382030724820f40c0400010401070070000f40c040d04508542c1d041d43d00f100c80e0030110500f8001850700101c1180d00c12001c0340c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 325163750 1250 325162500 325162507
    0x506060403080307210905030c010c0c03080103030c080d050705030703110f09060f1b030a090503070b04090203100f060e030c0301180f03020a08030a0204031a0903031503010603020406080120 84
    0x50b12036505200c02010322003008009081901c280b44403a042c24254101140b00748003100903414441c0d166405102c800815620700b0250402042c02107032025603c541545443c05941c0c42c50305d007a02d81d2203880c0350403200403004109040381500f907441b413079010f41c40e19a200c9407285040e00d000307001c80c0c107040b1a0018290303040c440c82d00d81c5543d01c400c0300c42b44102540c00a48420300b5581c107124600844250994020310310028041c80e0344000b01030444003826603036900c0d4440e9510149a201d00c21406a030840800801c014000740031542c00440d000348010225816056a5003402c84030b080c0c194004100051450000621030b283c10000005100b074220002c0040441c044504400c100c1541030080c01e4104c00d181d1981458024414160002c1d0041e0805a907403902114001c003e50042c0401c413102c2054192420b40d4100c044039041c45480000b000b0f51458884541c0d11a100041d07056803039140d92240c20220040e200c90051400070402c440002c00c419070402c4071554109a6942030a009520a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 325165000 1250 325163750 325163753
    0x1503110904120f05090904030c031706060f0702010c120f02070f050319030c0c0f0e090f060a1a151b06040f080306060f1204030f020a021806011b0501050a0506060403 73
    0x12110402c1d089407a0402041104090009840070300608184a500a0180b41080f080c0350308802c4480085120790f46240c090a5020142d0340a02d03c00d03034115811510034000160107001200003480c42c580141404504112103031349604114110308030000c0010a88107696107120380400c5840301805060002c0344440b0308000200e555134805000f40100c48802c2060b060a0601800d605040c4a810086c000e640d20744600402d03035200e031180300c0e0108000754080000c481d1b82000c5070b513510102041c0040e00403a140c0e000c15401030b016803860b0088036240303101e0320012a074074440b4601c8030150394011a500c030314240380030000907900701e0a03900c0c081c4c1011041100084071062201034032035001649580305d46070b0402107002c0b80561503081d0f0050707900181141c036140b00c107010548510f00c43c1c1e48a24400702e8261040340c6480180600075080003044400035442032020b115564411010300d080b211054003402c2c1240c0c281000b00c820703101079543c1c00500038102014003c1c141e102c14151040c500d400d245 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 325166250 1250 325165000 325165013
    0xf07031b030f020603250302091008040b1305010605040606030e0105070c08070615090906150501020d05091c02060f0c010c020d140a112a1c081c1503110904 69
    0x1003500070304c20b010020004045004c80c01d110f440501c412422442c00c81a5410094001c0d4440c88040d44100010701c55400c941d84254600e9124640c00b0040b40110b8580050581406503240004c8825540b81c0c0404507943d1110710a41c4001c2804d40e901080b004185c0d2201c80c21200301404000c02c21542d190b4940200b000d400448201c0d0382d00400c0003880c01d60218000c0d100c3e80d80f0790007038403c00741800948003e0081030b03003000311220b5103c1482040c1541d5600160b0756030038400c90b1400440c0c02405481070358075000704074455a1485600382c0f40368a070103900144903684400d03070760390180f9000b1840040b4880c0920406030f24644500040c15080c0d80340034040c03d000c200c050b00c4200a1030004011010234411800d030f002071241c40c400c07900b50a0342d01c4480d98103844d0310115140080303101e14208115141c840360030301044c142c8294182000d00b2540b0b03100b03070503413010601c50020404851078a505c6e0125108408055107007080d1648014150f1a0140340140d050100070712070844c060521000c58030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 325167500 1250 325166250 325166273
    0xc2502010c200d03081914060f011215030512040b0d0506010e1005030702010c0302030610050c0a0803013203060127110a0806030a081c0b030f07031b03 67
    0x200300c44024a11401020403001c1c00307142c00101d80e04034032002124810190001041d42c0201c0c24402c1c00201100441c00d1501203072116002d0030304030b030707000004a00d05042820740e10050030818900340b140020004019801d80340750081c003441c0100144020001e1280034000795402036004e201d0070b45414503180c5103540c1c9000c2e040c02c80c602140d4070004078905038050382440c16900c101034034001780140c2d007242c0603142c0e07042283c03140c0165082c081c3d0060300900c00c0c400c8074032480c002000c0187c00c011500003141e45410800006201780709460002c0701060300b400c0694000c1a12074824490001f0807000e4003600301220100c8040c80c1840c0c001100569070209109041d1484402c04040c000306082c0c10801407504035181700c82642c6000000321700407980c0d600400001200391110441c0e5154072080c10750742c003841c40c406042090103208859003504000030040c844440c200001c900f168101d00002e082140c1840001c07400d51000e01c0c10010060454400ba004007254901c40101c90b146850b8200800c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 325168750 1250 325167500 325167503
    0x30c090803030a23070c030e0a062f030304051f06030b150406171509210f070c350d08041502030403080108061312031d060c2502010c 59
    0x40e1601c0006400c011054079400594001ca213441c1d1031401c1204d00078110110341c03038040c0d00040100c2822012424818402c4046804950716101d400d810200ca0600700d88404004070360b603144d20007400080034010805140104d00907005880c0e005e4a00f161207480c40c2c00b40394940d410600341201040482c40e03180d412503110b0b00c1803c40785200c808210004000b005960080500700b0f610343d800c50103030440004e80202e0b09000f0840300c01140c582200c40d5640d600c9460301000910001c404c6480012640400381440700d07810820740742080f240d03644100c01000207800800e510414240034036515460041c1444d4039000c102c644c50114584603d03140c5d124109865988180400040072600308480200c08904010400d80c046440f401d007450010101642071190310801d00c950340224480203680d0000800c0207a012000a0021703840d0902075000d056441202011035045030f902d070160020a0060a1040384918400e95595010088400881e0384d243d0304520303500740f080302190040c1d070441c3d804010305 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 325170000 1250 325168750 325168771
    0xf05060c07030611040f050409120c05150f071e02030a050a140c0c0a08030a0c0204050c0702040c0806010210020408060c070c0f030b01140d030e12010608060c0307030c09080303 78
    0x16002400818a0001c09610050405103400301601c102c00d8580040c100f075564220007146405d80c2d070030420066a2102c01302400c88003c40d04c0403012140104c2d00c48210500c24010b0700d89403601450070302d40020040704c0105050150b00c0070010341c1503202d40405011100c07884283c00b04e41e10020025a680903444801c01880000203440d0312450240220010000c0208100c40c5d070340240d0245292507010142905014240440303012540060100644131001c00036540c002c6002425000c00005c4c00c00908403090b00c8108004c0c810250f100c03402007040040140e1944800703410300070002490f1000c2c094459080303510521040c00740d0800441c0d440d400111440170355031100305034141051101d805030b0240400703510029000040080c018111812a10700c81c035200c2c48480040300b03201b2031481d14400100060b1503803000e074205103410f11021018601c00c500000d00d43c2d840300c9036140760036001c4d200701d58940400b0003042011549400713060000c034011310304604014036000032559207010140508440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 325171250 1250 325170000 325170007
    0x5151005130b040302010e0a06080c07020d060507030506030f0307150c03111912090b07030e03090a1710060e1801090605070804140c0a0614070c030308091005010f0506 74
    0x21140304000307a441d044078a440c8038005590302d01002031141c2c800d201c1240070542582c1441850310700080140111102d545a608207540d40c501809400d51010504990190221aa02d00481c0c1306101c0c25120300120344002409040400403d8035002c80e0700750318005035104104902c0050526172882d8004c1c0c80307401f8042042000782d40c1c10303005032203580c0c90000100d001045800c040004000d2030b0540c0c01f01c039110103022108a42c202c0b41075507581500074004076072540c08991821f210390b100f004402048000c0d607082c0b4101000061400120354840d000304a006002985184010302203c1410280400108445403a051803c0340c50f580c0189902400032101074003010307003a402c2d0040414940d00040400503032038030140c06001940f09680a68880b000329280a9000c03400040545030340c900144056030403480c02d401140c4030000d01c1c0301e81c440311105208010014110b6032802001e0741c40ba80751041315151804a0f9845c1c01c807811126068141400300400c00c60384080b200d24181c0d107050301c0040e036 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 325172500 1250 325171250 325171279
    0x3183f03182109090501030f02121e01060602060f07080f0411030d050c0c01090503060112030905030607050a021209011d04021c0f110304050606010c0f05030307080f0a0515 76
    0x9841c605101801c0c0028a01c004500701e003481e0700300001c0036541e8660207801c41c0c6600700b460464109002c0200290400902c07000507203081c0142802e8076a03840110f0341c4811440303040d400d20000040c2c400403640c0d1141c105002c3d454040c01202d070700c44a54000842145040c0c0801031890201600803041d03440000040340c140844140200d9410304058203c51061800020040040e0300452000902d4024a9503140c0d56600c036450103011520018000c00c00742c0d003032498405500003c0e80c800c0b014411070190000300c940b800e1001c944207050030b803103807522420847c00103410038800b2840c4600d06070040100b000c041c0c1e0801d040541001558540800d45900c1c1408034009100b4a00c00d42c8980141080c01c103031805039904a03081c0c2e40a9000240522202100110702c94002520020a80d030005800500c880d4800c1810345000d40c09068000ca0344085a250b442c15503000340e030b52000003003401d0104010003a150351084d4004040300c00030412440c00d40d001800320000c10300554802c0304581a10302 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 325173750 1250 325172500 325172531
    0x1412011a0f0d140601050907020a030f0f0e040911100c1a15090a0c11071d071806030212060d02010c060506060904180204060e0603030a030c03183f03 66
    0x145980700c800f20f90100161141c07070760740721000d1240318415007030b900000b10180e202055441d0020741c59140c1d1800c2403281101a20390380703c00d803012820070010503a00b11030303980c0c0c41c001c42d00303414040c0310120082a111418491420714444488081c401c0c2084054001040c0684010b45003120402c000078549a0070300e032020f1960840c0500360f00c903a05800b03116020b00e56501c401c0064201303443d6110a0350010b10307c2c5440703903010301c240d0414401c002c004103040d00c0760a0545500c14400d00d000045c01403400c0b00c070b00c0620300740d4014000082c1c5c042120003030225003a6625030040001c8a802054400c00d9000030001603800754010310b11a1100c02080e01511841c059911294000b00280403c0c00c50703a810b1480c10045146c280c0c0305908201e00000e4032081d9078000c0d4011040903019500d0498400400c0d0007428801440004050307655006109081c496000391321807501c00e000040c0b084000c010b510407540080848203403c4007609407146004180c4070007903400c2007900d080100da0900701820b0742 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 325175000 1250 325173750 325173769
    0x1005070212070614550509011406060405090c0d0e0f060c0403020f010c060f05011403010f0b0907080903071b050f030105190e070f080c120105150904060b0a1412011a0f 74
    0x45d6032001c8890074032041c0355401c4603214048001c02046100b8800320614a040b00075034100e40c211004110900c40790800c1e1903403179030005503804064035103521074941c00107d8081d0598035080f03030070180c1220000e4000303001203030300400540c807107508050960300040d0601103420f480f24140601c80c10380400300941500800664030851404001d5581d45210340e6403280c101c041000d1080d407800c01000150b421522a081242d0740152010001c0e0752440d0050303a400c40064002c3d800c9120500c40b420026a60601e111000700b0301c11030013511140b8040034004e224030f5840a480c4241d04200410200d1042030209c80e0503440d03040d00116070500134003080d90034506581c00200024800e960081020040010061a50007003554901507042025010a080b01c20645981d420881d603a0006c802ca07180c4142e026030043c0c060300c00080c02032114000614000f1072584070b0550202444224049803405007168684203600354000d105d02044011600801c0c0352410101d03210b410000d0302a0081d48881c601c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 325176250 1250 325175000 325175131
    0x908030a0203030a020c2506020c06030906130503070804030606030b0105060c0d030c0909051303090503030a022a0907020606040e010b0d020d08070206030a1b111005070212070614 79
    0x400706d03031f42c0e00645925002440b0380144001f611500c0d140342d00f5403c101c401c03207102c0d0f000784010303041c0d035126154131200c4404c001c0020384052205020840120315030701d0082006500c03561001801c0e0345035240504084105902c890303c102800d1100c00010140800c405082c0c1c80c44e0701c0c1c0029600480d582c22b42d4801c045400102c600c03031501c3c081240c200079640d41d05c1340a90180c0c440c40b4000d80d8400030582c0c0c0e481107040210050b004211082502c0180600c01071302c1400c0310543c515441d0b10302010070b0780031a0482d0700c140103070b0090301030200d00c0c1014401d80e1903990000d0000e00ca00c0e48201c010aa450105100c000c0c003071010480c4034414409004180c0d200c440d80103017420b640b809d15046500251081c03c0d00b8a410032818141c8180300b900401308003144d001c00001610400710301a4035040184401041041076009486030980e809001000800e1980d1290000140c08080c0140f8114141d900400103500c00303518100340c03800140703407a03400110130050420354001011010041c200c0912001d48 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 325177500 1250 325176250 325176283
    0x9060a0f0605040e06120d143a0b0102120705010212130c0e1b090a090f020a09090606080103080711060a03020c06060a03021f03060308070302030a0908030a0203030a020c 75
    0x9001c03401c03541c800014400c0b03403699401d00705a41c4400041105411810000340c0055001061079000d0601800c1442c4640c60300741a241d0401c00d200041c9401204072500b00f190415002403190301f01540840f0040c01101418820444405449e00107907441c442d0f2078280040040202d949001c0140c00d40484000511051401940d42082948401041c1c001c071001c8440d0403d210000c900b5102101038148190035400012107a4001070740c0c07949486e07200a414540100c0800e002048695840c0205d062101c2d03007484c016030301c00b5044402000034019400514080d400c144080041c6a8449078280c1500c1d00015003680e101500d260803e04003401e0260326420050100e2100403158055003e000058207900c140d800b02d0f03442004125010302640030003903015051490000310f030b0821100000718080c080c140001c0d401e403a0340341d29850342c12192086005078400078802904030b074404000b100820a00d002036003440000e29019441380001080307018507660224000345940000c110b2800316182440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 325178750 1250 325177500 325177529
    0x11206051c23060907060c030909050903091f1209020307030201030b1201150f270c0e060706060f120816060912122012070203090a0b070203060601050304030e09060a 73
    0x400f03403520310844040c0c40c01e0188550000d03a1a005080f031503222940b40e500d4418250800c52144000c003405481030302d451005200607811600c2b0ba40700c41900e80b60300c0581100400b04440010840c82148800b25186410303c0301c4c03030f0016280090018180e070b909003804600c40007440080350007914034907494071701e56007009040204150261a91026218205020030380e4580307904101c11401e80e0352650031850705038100004020680e5500409200c021407800c0c2025140d041d0018010340c00559080d100c0070390f1294100940320006180e00001c3c0615225409a800c0e282c0301c20059001d038240e0840c0012001c440c0e001088000e07403280076826802444c198a00380580b0006200d11051451108072619044180b0217031421000900121305a109042d813030844081980200c3c141c000c0d000c0c0096100c00d104402d02a40c0721052030002d0160a2300c5e850b15000c1c5401014503081000c0c0400341800401c000340004a9400b8260f0720b5803003015142040b080c0c82e03032400f1941d18105640724042904d04907 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 325179856 1106 325178750 325178813
    0xd1b09061a0307081803041d0123010c0807020a17060f0a1802041505030105070c1205030402131d240615030711030720011206051c 58
    0x9106a87c00c095071061805d0300c0c04600c07501150042c60032001400003814642e404100b004040340c2010300c0d4450707400080c1c40c1c1505404041c00b036842c00a00d540640d2104403005000b0720001d0900c200301c541c035200316a115103050710005100301038800030600403006030041640d100403003206110504252760070000104105511440c08915071003001880c3e917402c2c85224400d420b1919844100320042c513041d6400d0840b600c00c00c090210600034080940c560304001c45200c024900b00154451410f000110303400d516501301303451403240c444407500c450001c03012030070002e10418810782161541d804000c20300c0020541c21010315014000940b26501c51031681401030000c1c4140d074503103155500d880030104159107140b04441340005040516591110750141c5e80e81c10400c041125505240024481c0e8060480500d00c05043e00d11a1081c403104141c0c2e900c45d003488250120040914 = true := by decide +kernel

theorem cover : BRFrame.Cov 325000000 325179856 := by
  have h0 := BRFrame.cov_init 325000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 325000000 ≤ n) (h2 : n < 325179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
