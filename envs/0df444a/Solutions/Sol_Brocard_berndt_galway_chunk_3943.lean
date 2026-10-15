-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3943
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:07:48.904118+00:00
-- url     : https://prove2.me/submissions/283cf30b-7d09-4e4d-8edc-034e6712ebb3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 708992805 ≤ n < 709172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 708994055 1250 708992805 708992821
    0x50d03090c0e0103081801020307030f030c0c0606031505010b030c0315120f0f010c0201090c0905060607080315010311041412030c12071515120606030f05010e07141302031b03 77
    0x3074409845d803103506d1903210020005500100c151903138150140c803011441c0b400040d05501422406840004020403002200e0008000d071083d040594003801400c4840e44c806c1d000841240e6042c4c009100d104414000c214510360203404490740840041c0c2408101007080d004500d80c00c00e48549000140079440414a40c0100094401300c0c1022180003030107680002034059080b20300802d000740c145604510b0500282d541600022f41004018000c20f01d4000703179444107041d0b500180d900d4a0b80f1030041025140542c4c4c14007403007448042081440b440c0510b0641021000d800a0759201d00960100c09458280c010510aa03510520038030182c034141ca4483c1c1c003c0c459603010041c1251130704849090100e801d5040c0c80b585001c400c0040c2c2c0501b9107801d184900c0305a02400c803040780c45d26100c0301c02100180e09131885484041c071550000c941c1c00c00c8500c20500346600794000d1705244101c071411062964a034020191004040d00005960740c9403810201d80310750120218042840002007401340b96 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 708995305 1250 708994055 708994057
    0xb340b040201030b0f2413030506072a030f0c051608100615081005031c08160e130e01090b09070915030204020a0c0c140a12050d03090c0e010308 64
    0x110300c00d03030f01003100e1140c40e002c02691415000d803e60300251030000780e8048484582e101c07401135103284002c0d414082c00312100062109103810071607040c2c01ca03200740070646800410400000c04600000e907060103603400c485503201e04031400070701003016000c11600038030b00903200070f80255085000d075051011200e041d094054003070f20908146110740c051440c80c21041d41309400590385160b16200900c110003001720b510031400b400300d407400d207a294000201c7c1d650030002c4036005c0d03c1c0100ca003c0c1e0032501d02c8014220b403500625041c00d16001c0d0b07520346400c6a1024100780c3c1d041c3d0448205103400c07007103510080244a0264051115071a1010366402e2180ca814060f20480c0407038119400d4035150011030040c0d41040b44c074a4a0307003c803920306000514158002c1d040041c04d130b2074a0007140c000ba031603103076840407654040c0c0f65407001200610340a0410381904000f40500c0d01e9401c0781d0044559500d40c0d6044000403100405503500c0b944010400c1c0410b6050041c4402c503292001961170382803810385 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 708996555 1250 708995305 708995311
    0x3040807020909160801050c0d1d0601030605190b030c090c0c07030b0f1806040f0f060c030c1803030e060d02090a030305120618041407050a0906090b0306010b340b 72
    0xc44c009010000c0d8110050040c98440c80032000c016083ca01c00312661800390540140e080d40c2d9080c207840b4540b01340400c001c1d403402503000d0040440d00f400c10110440c1245400c8040000250500034000f9090300c0c0024415050350081e03600c07240f144e031140110050340c080e6903401c2405014011001050000484105d4014800b44601501a0f22410b204011960640c02295101e41010002034007166a008022180ca8042c40c0d100c8070340155a44d903582150b09013160000840d58480c80c0c0198960f12141801100c0540c0b920000c9260031070b20090809038800e9401071040e074000070034450280d190380580e0301100000d05002d0b103031134503854050500d4012030311006c0200d1901002170382603e01601d2281d0308500c03a8101228503240c6844060101c1200411035601d07115801c40003c99031500c0c0d12182c024840c03590001801800c0c0340c05103054601c1c50b0030300d038400c0d0311000051000554900880c1c4c440c400e01d0700241800c0011506001c9195805110607443d04103410411007442045008244 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 708997805 1250 708996555 708996583
    0x3032e090203040c090e060a0f0b0409030c050c09070e09040f08120f0907121e140f06010b0c0319030905011409010b01031a130b0303040906030309060206190203040807020909 77
    0x2122503269001030003101c0764186d84200c01c1d0302440c0821240030035603000123103c000c500c00201d2084094400b203001e03502040011000503d41d03195907402d20105103d039507045041150200e10a052041004049074030300c00c01c49110380c91641c082010030104030082e06410707521034041c82d01d91066001820780c2e203204588000c400f0031444001500410b0200c0c001082c1c541c00d080030b6280701100e841e18050b1755040301c40d0b4400c1c0c1140080d10303000304424408400d1070318030400c0181591044a203060f81808010390041c02400d0003800a1502c819001c0150340240042604207400d00d4048101203000c3c00308604054129460f2030b60707009141010b4540280710b510740c00002d0001c8145070300110122802c2c0614400e601d68042201011071900d4001096a55603082c40401d1211205000038250f900c60b501c10f86c85a0399600e010010982c103c000c0e48000d000758005080103260006d52840c03824004a100404558000000f0f0304020b000c03401d4130401600645066240c2c0392014a580c0d90703090905040d9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 708999055 1250 708997805 708997823
    0x14090606041a0901080d18030309141903080306010f050910050307020a150b0109061701291605011805070b0a0306091506110a0c0b0d090b1e01150203032e09020304 72
    0x418200c000e6860b000440327a041d2760740e030905407404041070b00c3d00f5046c2c8626540081424036210181110300c0e400b002440c02480443e650741095000500040011003400e414403101b4414049255141804a0340742e80b05814860754070754031030303034103e0800d01520b80c000c1c66030340e20b400300440400705c99000180c9030740301b030301c0321060182c45600684030340300c011100300810601740300103004096400108a000b128000342011050752030111f1401182c0120846003002c07000d0014801c01c0c0701d000d010344c21040000c840402081080c50716400d132a1078142c041c0c410800000221160401d210b079001070001c15141c64100503e40d08180604640d207900e104840001d9004528201400c1001c221640782c107502c060303506107107480c00111994941060382001030040ea10b120403c045035801424520880f40d00c4402014201c2c0319514080d01c0c0c906030401d0000d06803401000d000d00d43c000044070b42000d2041640e0b140341600101c0e00b4801520a5a010f904450000000030351100ea038000d140990301c20001f007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 709000305 1250 708999055 708999077
    0x51902090f010e07031527050618040f0201120c050702100f0c0303231e01061b080c1c09030606081c0f121a0414090606041a0901080d 59
    0x901d503100c40a0081c21414403400c0085050f990084c0c2c800016210040400c0010a66a0340360300b0f07442417010560502100080400600000344d8420564841c20860f03c107200442442140c800c065401000200503560001c4000c081da80940100f030fa04030080c1000744070b01b401089000b45950071000301240141042c18cd241ea080e4010103008000f981c15075151020ba070400d4604070081e080031620001210040b0040d0405030141c2041070348501004403000008400401145042820583c401010041003200c40003001d42810446c42c80380d5000a00240c44485110703489040221030603841040046c00a80d10802e039400c41050011a030198004000f8241d4905141c0d44075140c400b440c000c0031500c0c6240c05803aa02482c81003a0020a925140b52031170740307840039a01140d14a83c46000c0b85e408408202546240a004a000201402000c03a000d4107240403195515140504000c0c8102e8444802c11030500a183e0158110355000f450410596036503246192107030408000304c2c00046003015a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 709001555 1250 709000305 709000321
    0x106052101170c0330040305060108010603020319030f0804110a080d0f020a020f041113091d0102070b011413110c07170604060506041e0e010501051503060906030a05190209 76
    0x408004d0750380f1700f0340d04406411490200c0150389807210150741031205210100206200f00b00d400d02a20a07100001340081c2980100742c9001c1402480e10300e40d40180450800103a0300164440c41403055007801c1d10103444a03d00700d0000300000c09003d0700603013642000610b81200281100e101d079803e44a840c10100c1032141280c031200c4c160341c040e40240b1300000411304d03424a640b0420000e1002d464450a00c00300515004900000b40d02600c10540c4480803181c103102d5064040381480b0161000714a1302403250b59019071039030705105016016661b0600383c0c205840702040d441024030780e1801080030b400d51680741c0426422280381102984205c0c00d004c501d05d1094444c580c0038129400040c00c00d44d8640d51074002404005083e550000d0302d800805158420007860081c641444a0000c40c0581000d503120382118416800303244952a400403079022803502100316500079800b501e05070341a503500004139280019240b4000c01c98170500d0070140c014104010340340ba4403072007112960815101c03082 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 709002805 1250 709001555 709001563
    0x130507090f0617040c03050f0d030c030209031020130e070906050f0a0c0c0605120f070c030c0f230607170f1302030106080708061e0106052101170c03 66
    0x207030b10045a1012021114154040c0001d039200b0f10501c030041c0e8050316550341d1750400403010541c00c120b030300c01d2994070100c2d0f80601a07400c02100c14502107080c001a50002036460804003210030340180d50b0020a16610010640a845005444140c1d03554504803845004555468464a03201c3c0c0d110700e002c90300244c414030325441280da20b0381c1c0791424034520381c0d070024140d4080c046640030b0016505007400069505811080109020385501c5d0301c03002d030f07080c01440d40742e03008090f16503d004440801403405d4220b03030f40c070101c9a010710f40203d09241900d401034181081c80e90180025040012098480c04250038034224940c4a100b80c07900c0b44c580710001d0b505007080740030300c003201c1d03032102e000a040a101c10b00c6070740d0108480d0003510204c500c640100e42110070b40d07044403640e5045200148207130b41c01080099044000c0949054407051100d100050500041c0114410400300107008032907a00c803d814005541d400320581c84040d42d42d1840c80108174201030180c1c42d1801801c110601034a07001c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 709004055 1250 709002805 709002809
    0x12070203030405130207170c01200a030c02011404050c120111040302060f22080d08060d120521010504050c130323070e041416050618130507090f 64
    0xc0d000310308041c2054100074140050f4841d0a08603607007480300101103130304184020a03e240c20003203199240090702605080d25145a10081040003081441d00344030190811910480454900040e850f0b00742c6104902402000c10748044105410040c007041c4800420030403038090bc1210790410000320000355600340d4600b55460300d440038040c0410409828541d00401040501c2c00301c5030b15011001c10300d1882c00104400003c14401480c1c0180310340c02d41008070a002140d41c0c00c145000c1d242020010302e91054900c0b005240b90116203491168034052000c0e1005084803103a59020790f5405000c46203451000d20a69201d28107000104051800300000c54404418500c4850040307402c40d02c50601460400c0c0c002e50311000c01000318404040f047c04080050050801d160400d8206810452100d80b60301102d02626004852101c2c062808a000382048035401e6400715140c3ca0b106401c0321094404541c41504410801c00e0290051030f190310443c41507002e500e859041030b4603940000e803010828 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 709005305 1250 709004055 709004059
    0x1b0b01170d0509010c020f21010605030f030d0f060e0702030c1506060d0e07051804170a080403080408040302060301290a020703021309081611030102161202070305160305120702 78
    0xf080007a525500c18906515424005049512050408000b18111200d83d600c15a000c191454001c01c080382c003802040000c1074100d0084c801080017481841d100c1c0710710400c2680460752030342c41342601020b50b008400240340d1010f8010062070000d5000c4e4a07a030164100c030300702d13000324526102e40d82c035000030311809454007808142c1065045c01e070040007007000350a8502075129030440017440e6a1201000c20703540207003210600a6040500d070911240032214aa440011f0782807000c1c140003a48440340550181c0c0528150200751141d05001e2601c0c801d43e0400f940002d030001c00400c5031990b45503480b03100026060b9440e022071084800c02c4050040f0b5210301d00503003042d18104090f05e08800208c0c01e0001c00342000903069210f50310701015501010100903241c0201d5004002e00100d04000000c0140c198001e51030001401e606445509010100074094681c01024448252080000302c001d15400001c035203201c038080c0c081100980701440111441d00c207007003100008841c60380940300e541d0b0780 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 709006555 1250 709005305 709005307
    0x90a0b27151b060a1b08092a011107060c20031204060f0807140c07150801031509080a03052d0114040614010f020f03030a0b0f090907050f011b0b01170d05 68
    0x100345c044880100141643d1003500c00e2404000390001e0050248860401605034001444810720000d0214005000c4036603140c2c100c07000410078140c005828000c816032141c01c40d00e201d41d40c01d0030303218403045600e1415010b1041c1002c8844241c1e0303640040c070946003a91190110070038113200485081c60704544100009100420754030040710003030003401719051410181c3e4040b50300e60040000c3c441c01820b100000070b10748001041806440e401ca9110003141180511113951b50b51500012441000d074044105540e60001a03d0501c10028102d00c00585051b03c5403801e0144000c0941880f0038001d5181c1d4030461030580c40180382c0b03807280340b0848100005814514004e58015038031201ca03080703900103502803001c03408034821041c0000d52017020010030002d000c0ca020b4040c0282c801c1d03012882c9005030421401d10052a000003060b9080301d4045071884006842200122014000a094400000b180038103000c10014801340d480c0c141da5020001a50607500b0300c0d140c0350340d420030203142008a20 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 709007805 1250 709006555 709006601
    0x80406080406061421010b1f03050c0f19051b0703050f010b0d0b0c0903060406060e07110a0b1f0906030b060108071d0105130803090a0b27151b060a 65
    0x803140d02590700041c20b40000081440e6107401180b48400425210b40001007442c00d23000c5032640500c45c0c1c54000146400241c107004411881401c00d00c101485401c01e1501c0f2040c3c1c01000d0b02c207000303e644100003184000941c1803e09141541c42034540401ca940703005030352410b03c40710814854462210303402010280014865103a21a00c007101a140c0c000c009000c121072851030310100040c0f4061b510a040000345c00c2d1a0040d000c0600d40080c1c280c1080019204651501100c001000e0042c2c0c1d80200014459885214140290722003036142c5084c4160400c8000a5280c0346601000071640602d408110641d5040011200110201c40e104082410452000100c03e0040108041d298060510038074081d40c502480c0c1829180b5848444150702c00501220300d42041000a40180300f0820135608281e4000e004903e0150306102d028280362012680104c40d540750740c8d0804506081805181d91107108901125881000d040c84014903c10000854800c00c11b603c04c05912051040000407101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 709009055 1250 709007805 709007839
    0xa090905040c05041b020f0a08180102011515080a02030609130f080711010e0103050103230a170a0908031801030c03020919150203030f01120f0804060804060614 71
    0x10191080e110040e030010b01040d140c80700c0c0b00d6129190708038074194120311842c5000915062030b00004244580000f01c150f00014125815548031503c130000b82034408080c640100d00601ca5140b4030724841500d20000102c02d804049404110340c95903a030040305960f0b0001100a03440243c5120390050711000010702034101d0704440d03043c010721400c402c0230042200d4541076825005020140d42081c0000e00c00d2580f9a00030a01c40a074010a0a05000d258516121010f250740c0d02c030040800340c0b2002c40328241c00c100c180980560540d1100c00090b03030400528004480b6008010300b4000305525403c04110880008250340030564050b070081000110000110040c10101c0019018113400382304100c00e0b0380d0740a00c96000311355030b860b2440015240581c3c403c06502c0c90304045081d500104184003601e400c00c400c10341074610786064000c1d140800d03c1d059400d01509240a410350784049800301c1c916600804135402503024110510802d502c81310a507040d00c0008200c1c940c0001d8140e90303401c9507 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 709010305 1250 709009055 709009061
    0x1e06110703060504051015090e060610031a040908090108060d0b0703091104050403030c02010b04021602062206030501030210051c0525030b180609010b070c092f0a0909 74
    0x4a40f08000386c1d18444444280f442c2a20550300c80703081e01038280101800711107403e2054907001c091410040102d0b06100d004206d14180340f1030104101a29035055140403d2441980e040422001d8000c02c800c0080e814000070700d800410b0000e00141c1c1240115445d4034180407442041a003210589003039848403101a0300a140d2900111030360100c40d82d4040850b0383c1c0b1b106080c030481c000c1c0c902183c0380340609030090840f84004130040c89103105103c40f50030103100600c400302482d030540d8404d03a900c0c00427220780181c00e011403900301c1207134440c0800700358a589600070b00d0480340f0a4031411030b5182003400c1a0340e43d0090300c62001101800c42a02c14150b4aa030700810341000e0000400c100104044101c400540745c85210b900110b6107601091800d0708200b071b55884100c0b0307901c0002940303007081c2c0d00003080007406100b504045c260128203001480100000c2d00024080703008100840141d041e035010720000886000c41780f0b1400705100c1100442e401d011034914411540c2c0b040d03007041c280030450b001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 709011555 1250 709010305 709010311
    0x80703120e030721050c09130201030b040e0a051b0301090b070804140303010f140f0901030b09010e1c0f020105060102031605010609050709030c061e0c020103151e061107030605 78
    0xc907105070b0070000748800c0b40d4080001c02242002c030004004d622420081d240000d0b004080d40164200000c114404038200d100101c01542481c0201e0312080e4440007401400c41400002241e0182c162808100240007800d10f02114800c9424031050200c20105400c0b40d054941c094582c00a00303002402c100e22030410143c1c80b43c460300040c561a000d03242610300d1504244c00c41070078000352540500400568250380d540b10903040741c00030134003071402c00452402c1c4010301c401070900c808503000c50a055802c0d001121300b59401402c5070238a852a1580c10102c6011495540219118001707001410f4410b014161080300d043e00150701c1c24040c80e12220482010f070341c0607250355591b03413004510a2140c1c02168003d0131283e45a081441c298249215682044e50001c410301c0b00f60b40b41c03e03004495100050f02d141c1c00c2c600301404440d4543c0010b078042c107444030701103c1040d884440810f140c480c0f120811240f06102040b140d0550f11204184c902d000c490180c000b0b540d00c02402000096031542141354 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 709012805 1250 709011555 709011559
    0xb09060108040312050103050106180b0a050904020a0306020711011e02060f0703090503190905061206061602030604061d070810050403090506041710050618040501180609020406080703120e 83
    0x35070b01c4581c4c41c40b408480b03080c3c00850f00d607516101c0801c9550100800e00e5052125030318200914200040003030721236603117403082c14040c5074950001760555440d01d840360021070300103a05550343c201d50300d0600049150782602c540468540031007032140b1020b611100f8810342c2260000d05007030310342c080450940750004104d00101a118084040000d400740054101010f41501c000420201101c0281070380c0000d400c07050040606004002c044000e01050981011742900c11a07a500120b0f2051803d141c0d001002075014829042448100070f50380c0d000302802405c02c00c3c07607001c0741311030041d090329030b040b5120744140b80c0c1c8000c0e10800341d249140c0c00b6540003446420030009480d9900003003200c0390800d030300c0300d840807040b9241903814480600048082101c0200d0812540c58038100207154140f16020304010b03203c1c0d8500040401000b51f00130034080c1e03481a443c403c8055149003404c00b601040408a00031030a181000a54081c0002d900c3c0c242c0c2d50240300101c10320000b002c00c4802d2640c410002d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 709014055 1250 709012805 709012817
    0x14041109030304170c010519030905030d05011d010e06060405041e06080319030c0c080a09030b180f19030c0606031704061e09091e110a09090b090601080403 69
    0x34103555041000740010888021000c4424040a50703c0d401d040c51031140905004d002c00040c0c0b56200c0054011240111074140040c1442a60405525500075140300c2511a440c1c5000030400f1940c102c88010001c4002c00d047c40d035aa240c40c035001c4040030a45d6a640c00c04c03414070040c0002e1400350001c0100714400ca0202e0201e000b0321062100703075421076015214581000494190400c10f681d14121400c0303450070280401d1590040081418024600c050800d560100c2c0001a9920480c0c01d44025038100440807a9410322044000071405400c0b40e4031040d1050340440545002e001c112106180b800701030002d0040d0712610141d80d1604884812110140c0d42c000100c0003411540c001ea06481d0501c5013035884074248140908040f040080d9007070340e03d048003480d0101da540000d0031026143e03e081c021662042821081750307580e11070003080d80f884d800c100300e0b582d00e203071820090080c140c1903549604c034a66440c0200400c4030102550650400e81e98000034600e5402000b8260b003140c480c0c0707850 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 709015305 1250 709014055 709014067
    0x906070507090615030603051f020c12040f1e050904081204050d030e0610030204021305060d140c120a0510170f070b090904120201020702030a06020309010f0204140411 74
    0x242480c0c403942140b0351160b9120803e0000401081c0880300c8034509040c10414182552561030f6120942104408480101c003c002580c0115806562001002004032008800c40000810313158005c3d0280200901c140440000d0742c2c100c02c240420f0316046031000eaa034003030034042800141000200281c601510400c082882c02444141d9244120b00480141541c13a0020754003c007030f41c8042da840d42041e4410820700c070300060b02180000849904440050303444091f5030658280070100c0c1d010b650301940205103600c0d0813030740c0e0b0444003005024058480b05643c80d2a1080c00724000c1001c00703401304072900d00182c4004000c1c1d0019800610200d0021849030382d5042505d40c520f602070b48032400e900540b0001007002070401440002c1d1107020300c0c15041c140b80c240444c004020082025003542400e00c42c0204d40c030b0007941100c0395180c0113000d440b420341d8103051980c041c4d8404e9038000015031815007201400f403514800d403400c1d02c010b10600d00342628101e0400c005001d413040d003400407080401031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 709016555 1250 709015305 709015313
    0x30209130807060b09060d03080f06060f0708091e0f090702011d03040e0f0c0715110a120501061409062a0607020f0109151e020301140109120506010e09160e01080d1112090607 77
    0x98001d0b207100e05c25865a07040700005111121030451c10a8030071402001090300103503102682d403d9548011303288180f01e41d40d18081240584040200d80180c201c0304d030700890307109001000403c10713030300c0d01c2d46a40303141c4e1034101e5240c1c52241f080ba40380503c1d0006100e400000f0707c0800701d130820b03115420000b1601b510081c1e10710406611403c081c3c0b01040c1c0080b00040700203514000e1500500d49800c100b010a9128295071546101e04924184690f90010301c0c1119000301e100030150b8010480007540c1d032102c0c94100550703192015a46c41d0003500c44c5640703c03074010005004004449921107141640c402d041751402c0e024101c05c0c0340c044007080c0b44c030301d0203011842030b440036600805200079200401007030b850000d8a00340054001d074656604503840d07400801c500046c40c504403407a940722012683c0d125440c50b824a90040e101004c0400e0004000401d139010b154100d050381c008400ba02d1405011403010b69559602e07510000d20b982151003909030340f9650401a02400802501c018940031090359 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 709017805 1250 709016555 709016557
    0x70302061b0d02130302031504030909020f0d0515030622121e02030405040e01020708030103121103070809040518060a0e0316060e0124030209130807060b09060d03080f06060f 77
    0x313410b010144015104000390701c0c0130000340241c3ca5586007051054142070310010142c8149000b010115500003034600c24089801c0c040303650a500c1c40c50200720302d0404c0e0003006602e480031031000f84203100741008a450b045100301451504200324a03500c00c400181e035078a990240b4207150010600c02c00420700f00040052100d0142040380940c00365070f80303d081c6020841101c00c500310622990388144040d1001440f02c00c112030549411003071101a0361075030350013112440c0703802c1c441e400940404101c40c000c000a0070040c103450700d01114140320580d2044285142c2110100801c440750744601c01040d01d043c0198002c4203a20b03400002e0340c0c601030340940808441000d8407011144203a6a2507012504c41d400e114004802c00c0641d0300c101940b0f200c0d42c40a805c81003038000644902c050301c0200f00b8800f20f0154a158483d4850f170495124000c5051900043c01c0a01c0f103540900390030381c00130380d891600d00c082c1a0039a81c5629180119165020b081240d10300060846801844c00c020520f24818544 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 709019055 1250 709017805 709017817
    0x1e0302030115081204080c0d051906050615030c0a030c1e050c1005130605090709050c0a02060105030c033403050714011e0e0414160e06070302061b0d02 67
    0x51080b40d9914a468051454900b1000c0d0194070f4003024442400440d40124080d00202800c6580c07119100311801c2c61828a98049050500e0400700904041080b0040d00042e10490781101e0712402070f120324000312114882100c0289a118007003295070034840c00381e400200d54084078648075980c41c0801d010a00c41481c032211a80204070080fa00c1d5200e0b8008128000c01d41c0c4140c00103008504000d00c0d1502d6506800c00e0042c00540c5039000034900350010411500101380c0c21900303101908142410390a80d601040a000050050100100741405c0001e58640c2200d406001084052064620219035042c03101c03503204100c500c0c5030b00c5200c1d801e09641a40145001c1e90241403003502e880d1030540070742c01441c21141440020507640150342640e8500b201c80c001241031040d81d403080c0742c00046c0100612040401d1004002c0c04bc03000da0f00b171440d03c001c070240c030030740b00d1540303031800721080104502440e14001c0040c0e100f00f000507802d80070000c010028070189207807941031090003a480c0c8143d070050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 709020305 1250 709019055 709019081
    0x20f04090609080a0c02270c0d1b0c1104140613110c0303160c020d030509060915030a060605040828050303041b0b13050f01171006271e03020301 64
    0x10701d0301c0c40651600e000401219040035409402014080181c82d1f60b031100104804008000401c10303d00345802604904440070b507a6040700c2c5150030009000d0b15144c415071040c0ea14401e07003e003034002814207115080d0500c03d032040d0020241d0b00e42081102c198001040e1316101c81d12040d0031859111110064060020315001441d160715100039131000021003c59140204885e024484025031600142c400c411074152404a540e2176240c0041440ca00ca60510389400c54452400004241000030245002e115000d00034040325903111803c0310f240c001d074041c02160b60000244007544a0101140300800c1c0007503210f000910115440c1d060451b0412076003500c2007401c14665008070341009400300054607907220300905002880d40a8004a902c40c02139500070098a608d44903544c0c0110290980c0000e140740d1010103180a03601001c0c003001e41d00c00d07103012a004e8100350f1440c05500c0201c100ca4441098000c4c020791030141c03c0328100e004604004a1158415400f0002d070f1000c1c0105a680b1800c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 709021555 1250 709020305 709020317
    0x20a03060f0f0e06090c0a0c060b09040b0703200f130e0c0a2d0806031f1406030c0d030815040c0302030f0907140621071d0d020f04090609080a 63
    0xd00810075483e0392009240b9441801030804000c0100595010754946241c0c03403600078a41001c40c601003006007204206558049c5001c400c1004001101c18120f1240c022980c01380000c10000c000000e9407020107410112118050022240d8101f0303100c090711003500701070441f804090751002a5401151b0a6803521141d090010b851504183c00c140c1081845500d52801a000c0340c00b0040e0001602c21581c89504110425010860a950400c0b00d141c10441c0070a40100a0b980c07105a200100417002c4c0f0103100c855030740c000841c18940800d0041051300058451400300d500303640e046942070001007440e8403081c80700702d0041c0c286d15284035020380141143c400590b41d00f40b00780c420107030304e000400e00c1456605c5001c05025003070410300c102c64500400c7e21060384845e90900401090070802d110100321840000401c40e01c80e81c04030550540c0d000c18680c0da50703607540c11001d115004c1820344000e90404407225140c106400c090340705400f0280540000107010802e030380e5003401648014084000105 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 709022805 1250 709021555 709021559
    0x204120c06032405060a0c0210021006050a080604032001061d150a050d02031f0c0f0c05060601080603100c0807030608030304020a06030914010626010b03060a020a03060f0f 76
    0x103054440c0c0800b4a0300e41c80390001d03c41004030000e502400c0790049a000d400d000c584201c0d024042d038482000c00d5401080c0c401150400c2c00000d5503030442030441400c590600f0400980340c1004d00810040d40e2090f1301030001a41c0c3da490a41d001122030010a543d00d10315040e0000c545000e200e084083c00366565103005c86101b1800100820401402d41101c10300002c20191481c0c7e140d01c3c5041c11240305444a03c2c403072243d800001e003048502c403142110003010070311403542c0c02c1c02a4082c51450a141d2a000c040c900d111408071062602d0b400000e0051344854013040d80383d07005510207a03120400030708540d5610407225840c026280015110380c00b0568110034031403195098065080034040315001036003946415000661503c0707140c400c01080c90760750801002400707840c05240d002c8001032002801599514140d800040305025095079042e00c0c0108507542e60803041c00f03242d443d000020000e10103921804031181c029440314950100b403640e500b0000501c0d02017040100028210781940ca01641c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 709024055 1250 709022805 709022807
    0x51e0703150f110306031f0209090118051303020a061107120905010207080d2f03030106020601180b1e01050c010f0e15130b04020f0d0803070f0f020a0f060204120c06 73
    0x240300410040349100f01402005025100003030b006880c5030103600410a0903618131000c0c8001d20504007070981090b0320a00200349840c0f01d1912000552043e541003240d66541d448055105800d110020010380007184000d0105071641c20004060300f070701c5210392030035629541d800d105604001d5008082004008100300540c0c06024030000ae01d262005062000c00f2200001c0214840d000150110195040040c2c80401000b0b0041640310615086075541d50711420060341d01c81091240d0000ba00180005901c0c100c418061050041c401524522004400b040190900c200c0a9511030420a0074413030600740c04400d001d03040ca401101c4a00107070345112844035504144440700540312811040c010703c680d40c2c3e03400c030551031502e4002504280c0f9840310310000d46005400c250480d030100c6010342040038030004030011030145c03055844410b05100d058809403266841d04400340007503040005d0716804180c3e080c01c00b5000d0380c812480146840d40b41c0d00705802c10707a00c1d80d070f0659268154002c140451 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 709025305 1250 709024055 709024061
    0x905040f0b070e0a1707030519060f0902060a0804022b020306090a120807022407080603070302090c07020301090f12080f190903030b03070b130b07051e0703150f 71
    0x1001d510300d0706050350aa4035011520500c510f00c1407075200c0004440301791084800380701640185900100741d6200c5652110f03030503450504207005644061801c40314550825141c42480c5901e40c0c00b40110f8240682e2200030fa4110000070720030b9802120941c042c1d80c0000d51128552103c0c441840c200c045044280189494224018a900c4060f80011030000c0402c00007000c2d2801e65500c2e01d8054001da4403520100d00781f44501d170000e4500318004842401d15400e11043e10300c10701381c658400d021541e4241c01c15644155920001e0b40142001000c50724586d170100c010200640080e0001c2144186c558410292b09910728081e0348506007040380351182c640c00000e464000c8a0700c0740c51000d80c1441010041c000c01e030002c494403001da60385060700406000340c20494149200070141d890071540c4068070b218980c050181142860000400802c1c040300b180c00340c070301c085c0d0403000400074114006812a80010148054643c92142c1d502c0003002401c03181034000450088030000c100c9040360b520f62015 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 709026555 1250 709025305 709025311
    0x19060e0712020f04090201050c0f060a11090a05090a020405060c06061005070b130c0803220501030c080a180804080f01050115021015231008130b0606040905040f0b 72
    0x240701407507281d10150351203c0c800e145883d41140d0000e280c989502c0103035110b114150711402c060054900d8914007034004195184644402001030121508240c080c11441c0300b0b07040c1d41075111181e00000c0c800c50921980f80360b40f02401a1006140a4960000038115005050f0120146e0722030410400d06040c581c0071030140c9030300c50800e40d04140311a80c0343c28011388000c01c000c2007040d55a51040602060940c26001041d0000540b41d444c1c40d42c4c000d02a102469560810098920280006d0f140d44248103c4400400e55a98181a0344a50300c03d6005464044c103000340e24444140c040010a815030010001007100200900041c00780c0d403025425a58144d01c00e04d10400040105043c1540210781700c140105804c40000b04812201000b40004400740c00c0901c44414180d907615010008802607202d4240c01c45611205404840707003101c0200007195040c82c805c080200d040002980c1480954001e07000900b61400c29481c0d40c0c0c40d000712541102c090b5560000c07207014106008003036200b690 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 709027805 1250 709026555 709026569
    0x20417010b120a080901020a0f050a020f09090d050304020d0c0b0d0b030c060d0c02101d0f0106080304060f020109020907091409010503030327030307030e071e140319060e07 76
    0x204100b8110041e0380c4500290784094000c44001a1079031042e0720900c840d04d4a258084100c0c40c0c180c5641c10019600c462a2000303d0003018040301403d96450040e40c480d1041e200304004141e02d50a42c1002c07142c942001d08202d070000b803014407980020307102c0c0c501100505948510305441d000d01507002d030282c17988200070b04e0003500101122400e5407581030464501c5081034401088044c0c0d0074204914000550501d088802e241082c02c0007800c503a15005021a8611412a14a089031003146800c8600c20b1207020001e500c1000100320f81401020290f0b143c034094000041c0102c0590003080c00e00c5012241e4800181d1805002e02c40440711800241074084142e441d0211981014003081d5a407002401d07212040c12040140b000442d103070f81203248150140c2c3c0076070f80c5a091440e00900640722102c4907031001d000300034010602c04842c044244c21500180142c8180700c2c5400c942d21050100c0205250300341c05540d184400d60100175410b400414819040040c2e10880060610f04104850f0020b031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 709029055 1250 709027805 709027819
    0x30414070f08030a1b0606060f12021612050f03070309031709060105060d09050304090b0a050d0c05040c0318110103050c070b06060c0a0f05071a0f030f09030904020417010b 76
    0x80010403002095402d1018103003841d44211178400000d420121310240020410760511101003401c0f03138000e43e50088021503445480c1001c41c01c4003010181c0c012400c0d02c4036140c48009004010a5034008485071410243c1009854290038034662103d6900481e1401b01180c4c403014940b007019071051401c041001450700c1c2070003e0516904680d00d509043c450103120721b5000c10301d0800132281c2d034401c0d01c46982c13107403c60707a5a541d0744000c100030703001c1d400455200741118a80012542800c020f08500c0b10303440400400507604160820000f8107080c207240c0101544c03000e4000c410045281d8550145004001c20110042050001405d81d840200070f0600d01030240607c100081000c280a50081c40803540240ca40801c099100d20745503905030b02602c0700904c0b041040c2482004501a82034914010f4280720212180b04e511030a4420340e80228415501040010202c00313041314140e4001580d0403e90345401c2c403840004082e43c010360040b81481c4008000d145241c8824811074804010030b0340d800c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 709030305 1250 709029055 709029059
    0xf070f060206060d020a05031f0b06090a0b210411041b02030a0c080c06040803011e03020d03030b1216090b030c010f0f050702090c0c100506030d031e02030414070f 72
    0x945521000e0200350081340034042500c03c6598100344040500b001400b200c0303802800c2d1614800c8860020101188149071442c5901a800c1443c12159040c1d0040c040081d02c80c600301c000001a48020f01d010b03030b030350701e0201c00f6040b000701c18000b140102d00640c21480c5203820302c0200001c44003d49010481c036441d010f145208290003100f920040030540c14175603408445803c10113407038452000c80e820607000b403404000802c1581d401450580e100f030701c40100103401440d0345c880d100e200c6010280d404010310200200080c4650131010342800054010361100817006089032034104d04280c00412104812400d01901e4450300c0741806143c0114010940c065528002030440b01c10624030108005031045542c102c203000e82c08444031154054800318041c940000c0d900096040b92007a08224015200c03083d00b86803503806010b00901c0020007520b02e01070f0124054000300610120014850029140c4080700f1200b480030714416170054940005403401402d1041c14607495410001a5440c00c00c07003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 709031555 1250 709030305 709030307
    0xd0f0615063b10120f021b16050418150b040c0804020901060c1a0703020d1b1403101d0403090f060909050613230117060402061b0f0f070f06 62
    0x14000000c0003655500320b05141850f040b210203030200c40300a072081c10010000b02d00925070340100500482000c03001883d803d036840c0c440c0c850107200724445a501444c40c00340518034103548941580c80140202c0b407884107299451600a01c80a1140f0003c82e64401484400341418010b2070350705480383c50020b4161905c1d42c006004403070180592001c000c0b80b0081c0b0001c01a900346c80c0c0c20f0000e83c88003400304c10314010f031000303000c2c2d8400400f8440315401d041d484001171002d007051110725081a150141055070b500d100312140c0e08000e20ba80c480246403880040e40c0c2e1a912110900341203052010341a0345410308000e411810715500203005002151001c02c03240340c2c01100c0e5410750300510710218450b102d1400180884500000140d00380d4945000e142c20740d2160052801c000001c4020090030b42c1c0d980000600503e00650101c211383c00640c0042c00510b0043e0041c030040e070050103424201c100750341500346042d0342c410008075994031003801c001071240100204030051400900400d0490306205e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 709032805 1250 709031555 709031657
    0x11060403150902040204031b08100b030d120b04060f050a05010206060d06050615041d071d010c06060321031404080711030f030f0405011107050d0f061506 68
    0x10701005107642e00c581a808550300c640481e802150418141c0c8080c8035441001240410a031280e40d00b9440b0700509400303031441c9801040c2801000801030701200b113a0103025a528112203000050075552a00c1e00949d541d81c0f4440e08020b8170f4001205076589041c9003c0c82007010954008c541950301c100100320041e41d42007103070b1800c540c0c007000100350b689501d000300c9c40c40300c171000e00c8036100c1101007400b003601030600310fa2800c2a038040c42c10482c1078907540c6069400000b494030045111440c0e000307152565006284c1d202d08640700b1709002071110790742d842d01d80c410002c08400a07682407100f07140c07140e81030b450f015407150301054841c92502801e140d51154950700c610300008100c5101011f490000d65802d020341c441c1049108143d0b55502460003008440d5849405540d0215541c82c0d584462030600060034020340d44003a1040100c200303544c0313a0f4a5140b00c048411164240c4641c1d04600502c10f6403680e80c014450780c0c0b10700761040c104200c0b09084920805410001d44c81c95103e030140006864 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 709034055 1250 709032805 709032833
    0x121b0b0c034219170a08040303030c0807030e03041e0b0708120109020901081303030e0d0f0201142e030c0f0617091b01030e0703121e090b1308011811060403 69
    0x8000741c0c01661030010030350415010905c050300c00a40424008141509504007040702142c0342e076400c800340e40b00780c4242d00f1180444c3e10855103038000e000500031404080b1410b4890030304540301c00340550ba00c0c44010102c2d03003c02011541624040f9024001071a0501c032680502107000c0d0540c1440310003000200280c500500c50180350301001d0f40c0300103040c0241e1005d85017a03201c1c0140c03035190380740c3c1001030b02d2a407011484070015882c0002801c107110a040c00c2070f00490001c44c1080a003980d91213140c039900e500c005900b0380c5e07815200f40040000d846009160007000c911240405007481e10b8005000c0303c02400c808520b009500c0b08106085201180301c4485c10085992a800510355400480040c207103407505040f00d2041103404414050b0581582004500940c0e81d82010410401e800e000c2031040c400301404512001000c4c0b2441c1c2101c00a4404589400300c0840045e070360b51032030360940301140f030212202c0108080e440240081d03d610100743c07110a99016142502d19036590326160210 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 709035305 1250 709034055 709034069
    0x7020c060a030b2d04141f0f1d0c03010627050d080910020c0603010e090a080703030b030601091a0603100f03121b0b0c034219 56
    0xc001c05201d002e64005445504058440a0119003d682c1181070000202c040420403055801e00d1615141078060440c482c03200001c80c028585540300540c0364200d158010130054450b124003c90700c00b04c40d00c0f5410040409121408010400b140d4440381e000018004000d039003000c00040c00f2032074016001b01403020b40c14000800300d40050308400340920180d04143d41c400b03846900c440c207114160000d0030500000720345403111544002c0f001c0e0380d5446e036510703100d4002c00180010000c4081d038580d5268442c84d000141d070413440703050b640c1c600194001281140840c0e52070707500c0052030404100d0240500716042040120030080a519103c151022031034a11802002002465a8000b04012401800c10011007a00182c6924000c20b411042806003030000b911546c00d03406a204a150b00341020f0741240c8070b14400d0b114110301480ca40d1008002d48200581d12425020041000d8158410890007c0c050b10011016001d00c02240e0641c00640740711304022279010607580043d040c003a08503410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 709036555 1250 709035305 709035307
    0x71a130b090c0907230c01020414270c1c090b09070503031e1b03070323041206150906060905091902070f0f080301060809030c0a0b0709090e0c0a06050307020c06 71
    0x2805e0110042d84980010b54036400e440420501c0341c4141c1500a003064480010300e00c3c1013401ca42d0306100040062140f44d495283e6207950b0b1800c0c43ca90507805d141c0010200a04a01c0c00009003107036807109505900e00440296903107011002e0000e20344442d41c102044601909009107400c00283c0d03240547c003820f00a402c0740d86421581144000101d60700f030386560740350300c811440d881812500ca401124040d8045900002d850004620002d0220007005c03440c4091800c1c1810400713510103203004003504440c04c9a40d4100c0b85c0307021184240703c00042c281d8001c0810002d0500c00001c3c82080c1d180d0101e401100d1110502a0000c244036a504038030804483c01030320341c0924200700c0d4480303004400241168811030510028090503400641c1607500070b40b070b101c0340c0f42c6410802694074403816000308125001120a40001382002c07031080d4102c8907501c0c04c8500c0640303c0a0f020221220b64004180b15800841000b14a00313004a0900092103e41442c504602d02544041d4032125810321691160710 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 709037805 1250 709036555 709036577
    0x305031015020a0813081006080c1912020a0513060f1508150f0d060b03120403150f0e0118020f0103020408150a06090c110c030303011406071a130b090c0907 69
    0x44da20b411704000d121110403544d407a0580a90800209020300075002c003130040305004c241c50704000c0c201d01c28101200107059286c900d000d004002c07010300300008036070120303440c000054030759241c1200780e2140c1c03200780b030000d213651800803000c950044940c460b280003500e0851840c450f982242c0300c5070b44804541420360700001404002054044c20645242d4071041ca250444248209980324402e4074401381c080307882d40c0c00c1c81503404685d40580d1100800c0342c1c3c440d201c40b4000c03072815044003c4041c41c05001060050020740b5681c03c0d505104170740c10091050351486000c0d85007104844e0070340d082c01e003000c500d002d0404003110f0b1601d2030403145c244003d142c1004102480f295074400d900400c010380081225414000c0014000020102c1122481c400e0381489810740c5400701c200c9040350003a0b188c2a0a50703100a09000e40b9411022060b203403001e1881c24903910705c1121000a100b54000c403041c000c21540c500d070180c49190090f08130741c82079010700900310054480d900b0050704038403281803441c4080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 709039055 1250 709037805 709037827
    0x31614031504050708010606180b0901120e0d0323041e080711031c020d0c021c030c1b1a0304020d0204090c2607060f02070905040305031015020a08 65
    0x200d858070703200040403110003004107010f0f0200c1c044096511300402880032a07554403040721480c541c07001d0310001c110710780340800c806a00a8001c1945e0030040c1030038600340c891070710b40c501150381104021140740c101c80b42b400e00c01e5926214041500c4040a00c1c0312105640c1078280700c8140c00140000e0488090030b00340c00d2003003a000c0420341f890743d026007400c0d5140e20034500307258802d1061441501910924052580c844042e00d20300400b003402e51300034041603001c000100c5512a0071501660461015904080d90511195a40c000075000c0e480f015141c02d80c2d403402e49507280c00d030040c04910107049007080c0304038154207148200c080290790b2416106e4446000090150210700340c002d5106243c05501c07002c0254560031030089910a1001440810350040e010f402c03610b59206c0c5031b075250030061080c82401d008000c2d00442ca8014412a61344645a5814000f12502518182e01144006c4108100320104d00041d030b01511110000840b07061403407130080e58810840f80010100080411042052 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 709040305 1250 709039055 709039063
    0xa0b07032106080d030606050a02060a0c14030a050108060606121303030609051006020d111908040e010f1503020c0a0b06060c03040306050a0609050402030706110c090a0f050603161403 81
    0x4541c1c40d50041101c0c60ba00d001c6140c0d2a148202003c012a09108000440790701483c04e481c010b4686401400480d030750221098000d0100e800c0002c01c2c070401d030501003411440c40020714400c5106440000c0c5a5041c03040040c60660b00504441c45107404110b00124001054400c3c1d41100e074840810740d0341000b0303107403c0c3e01a100c2c0d50881d2040b1840d1408119101c040c00c0100d8044601540030b0300c1600c070000c842120300403004035041040754049200380149140004c00e035150140540c4940f41055180e401c0031400344c1080c0e209030320f030107090b041c244800c10019100a040e0f03241e81c2030840c0f0702010402d000d502c070505a0780c0541075801c05000140d41c2d85441085800700900e0300309607582daa40700c0c40c0c560018901514020400d9280c0040800c0740701003403040ca402941c00034001c0c40c40301d25191045441901d032800e580d1040c042e58050b80f40c16110b1001c072a0066031041c01c0440c4504c0300e2803008044400040c4914070940c4a0b2808192118400d000745059034201007d003845010044003007450 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 709041555 1250 709040305 709040357
    0x21002091507111809030a0e040b03010c21050106090e0901090203070807060909090c0b13030215090112050c0405060f0403050d08090709020304231e030a0e0a0b0703 73
    0x105900240140401c0100f2031030000703c500031901566145a4403a06a0008104441c0360790203500801c42e241c00e183c000d43c00c840080d500100042960740701100404d003540c0e04088600302007503644820a110401200316658004103100313080140d90314040c001842d260346803140d200c5802c02c100100c0e0f0140d40c01e42088100c4c60700501112640d550b80d4928954800f0540b040c0800915400004511f40740070340107040340c0c10380180000d070b5000d08009a441103076002203101e51005050710000401602d5101408480f02c81248605032180c038a0f0002502d824038110001c6070041c90300040111518003079099805551068400c070351110314401d2040103a10903508080c6ca1441380c1ca07a00c1003d66400703102d41d44108540410b4440395581c818440c01680070540c0d0041c140944070b103401d9070114600101902070b0182504440505400c110b0303102c400800c00780201860303000010598107581d088051907818203400c0d2502261640740c080503040601400700001c0801295103c004282d40300710104d040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 709042805 1250 709041555 709041589
    0x108190206091c0b04151a0a03230d0c0b0619060e060c0f0d020708190b063606011b061d0d09030614010308070605061309030302030a110a02100209 65
    0x1e40b400d02c0d08110100e450415040301406041141c2c150758410081f07040c0200c41c1010702100e010a05680d02c08a02c510b11102e100385110b0300d00c0124500342c0f0304009520b00d011040d21804585030090500000201000304030300e0240c1d0341095101d02c400c40354031449088400c107280c41c2c0041c1c40f102000403a24810440b65403024070505c02c0d080040000800c081125800903000c565030705645c3c044080c0c940450030410b58510f401d5441c0200824626064641e1007440185100d02a014810061403010384040641044407407101d0480f102d810400106500a034003402e0a013084081d4070201045610076031070040131552110681458a60403040c902c1e000500101550800c0c400160003c011040034401500c4450804803020140d05440c0146416280c105640760728000c2e25440399400707001e000c3d1440d1740001580d4164150550a489400501d42c4240e50250b545c0c1426040d010035141c100b080107003004006c004084400b500041c900300d0f007244001015846083c1500000c0340c8105070f0740449 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 709044055 1250 709042805 709042823
    0x1c0327180c020c18010f08011116030201060b0d0518070b0901030902030102070c0806071e051603090b0d06030c0b0301050d14010b0901090c080a0c1d0609060408060108190206091c 79
    0x1a814049000d4142c031030518159908070399500d01f1074240c6441800046c3c0300c0c00c0800800700c103442c551050412050007400040752a036a64555103640c0d40c881112a02c0290741c030340c1808940400300060040c9085440c0081c4421424290000c0803885842d8009043c565605c0101c011500e027134042d2441b20f6040030003006007958503601180c444404031161400103004030400c02c048490601c2d41e40f002c10407592460f0410204003c0c0c1c003900000e40c0010b5060211194002400802000040010050180e00440c49a10714600089030b1800780d04080c03002c05040c401448281c8504602c221526042003a64180d08042c1a60700c0c01055036118150704140f001002090220b201d402407004224541d6035107c443e60341c0c64030b0f003040b2a2030380313038603000180b04d2901c010b4084010401c00c5900d000c01003d40d1300d00400300307000400c079a0117940035601503048800104a00042804250781900c205161540899850b85c0004c1c064403950b0100e03403003601d0069011303048580910180c1b41c2198000825 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 709045305 1250 709044055 709044079
    0x406050711150304021003090b18030c120405030c0f030303130c030b0106030506090a0c0e01050a030b030102180102060f010e060d06110703020c030c0d050a111c0327180c020c 77
    0x2c161544201c0301640a05014031030940064841d00c40e4105503034012242c800c0c03584609480c03c101c44007400398010700344002d00811880d00420301c042402a1034881c002580d03286400245802c03c4517008105100e001d080e1f00f150710585000c800c503584103c0781038510300300742d401e481c0000344906aa04080c210203207940000c40c4664040d44928020704045840070710f2035480c480c4100a84096002140c0064000324410700c8950083c0050000ea51050a009c120030040c440413a003260840380d40342c101c1c83c0740170000304005e5805018450700010f01c080418015030412080c01d40020020703000f1030151790b600342d85509003d15035102204940a4014056a0711800e0500950711048028250b20078042c000441740180341070642003440300e900001400c881c20a03501d42d01c0c100131200c444070382c01114204a404120111140540c100b9100c0c0d2207005112100502107034086460761101c078074050034140144504810444c01c1d8280f4090710304007064580c101311040303092039032508951b0340040b950280 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 709046555 1250 709045305 709045339
    0x51323130803040f0c0504110a03050603030d15050a352406120d140702030114040305070507090221041506080106060201050a05070c0f0309050307170d0c080406050711 74
    0x14032134003030240550b2104181c68104002c103c42c4983c0b80715002d100d04000d44400c4501941145502c034400900381c034185a9618036400c142c0d1034030450503e90704814642030106140028040c005800101c4a446d6400d150404554407180c2e00740c03070240d0040b0f1061506a40d01d8003007062001882c01c10244654000d504000c6950305142510014481c480300700304101d070380b100004e02c0700808405d0359503000c15a410a084a07115480142e050303806540f1900f19414400302010040c0c020341c440c0d680c0319139078411030400e50b00f0801140c20501074070f401040500484c4600551420240e451035a0341420360300c46142100c20804828250304506050000009207038906500140c100c900c281c000344441d603a1303543d8410132980100c91240204000640000100b044658188001842411f002030300c41c1d181e1001a00c0d101703007030f17202031907001c55144504001c00040c05903810081d81030400d840d2410240d90383d002107001e5801200c0030400c020600c41b040c4050384401d400010405060503e044040d186 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 709047805 1250 709046555 709046573
    0xd0302030405010e0606030d030f0b090114030d02011b050c1524040501050d0602090d1a180604030c0b0c1605030304110618040203180d030605132313080304 69
    0x5042e1000e510300000c0005451010801c24030030140100544101d402e980000d074010038907100207480c0c81d65034225109150701c541401074041c2c05050f1010101c55001420145480c0311002a04110f90400c0030000b1000c00280b45d0501d40500303401d055807501b05070b240c01072034820404034004011400905010802902c0b0300c601080d80361043d400c2080c09048800d02094030000c1c4202904044000c0002004c6802c55025206031040142807480841090303c41410100000d5142c0382d54510f07039018440b4039228001030300306c0c4583c1440a040145056240a801407500303080c068000401140002c003165030503012a81c00c106d08490a8441c0c80b820305000e40c1e41d07082180c0455000d40c101d0b0700f002407440c01c5010f94580c1c08c65810111040d011400900001c0e4202074a00f040101c400c044076507000100b801001000301003035400280e03462600c010440701000d0b41c801003c0e59031415400c1c40e018100040d640104038a0b0030105402c40d100c00482403070030481240003402c162808024002048a907030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 709049055 1250 709047805 709047811
    0x4050612150a0e07140d020406030b01030305180114181203040b03042a090b0301110d0e010507030c050d0e0f0105250e0a060f0309150c1214010b0f04080d030203 71
    0x410400c010b00304200d403244c0e40d12a5000300d41140960741c80c42480c80c98402142d03240c084c406000410030540c0d070f68440000000a8008a011030004a401d008030020142042c0101000b46042c01c0e083c200c8801c0c58103180729070500d0507040441400212203548891004101001c200c0003200d40d50f90390b03684120f0240d00207580c222a8102a0b00c116a10f015003650704112001500c0d120074209440c0c8550080109420000c0ca509552603003034256461481c038003d04940518aa404118070161030142c42c00c5880c001c000c0340c107141c03400700b8074111143c0c003006803440404071690004540c500a4409880c2480642a4840c07075030901040014000c1032030a81074000d01c08005000d03503d0300c003d0040d94503050380080c2641006038a9410070103075203d41d00b5151003961a050006100030241c5a403141c4c203500f60740b0180c41c3e0351030304a2184842e070b02c00504d0f185210251406c01c82042031030340742c0c40c07200c8040c828904801d001117106070881d0000070494000700301c85070481c0c1045516007c0607002e50422 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 709050305 1250 709049055 709049071
    0x4030b092b020601090c14031005061305131a060a05090d0f030801080604020d0b060609030706020102180603041203020705032502010809030307080106050a05130905040215070f020405061215 84
    0x210000040e01155400341941800d90f540f1611858165141fa81640e50070040010b408845240400160341e21070500500100005686d614591802c00d428469403540404510314517510701144002d940c4d214280c8070348002e07401c1700c5803596090b034002c044805000c1d07103071403d07405030302d401c03c50007002101c100a1400354440d46032803107581e0f82c4404442d244d030030460340603401605010120000502c40d190789a40080c00801050910280e0f50201f07141030b40e07540212000d80e50000303c2c030402d400060700398407607810225602d61851825640d18a0103c160352665402e15402140e450108281802034401c054a800303e1407230204e110003560b01d0315004604040e8017042003800810049070012040b28801c034000d844bd03074456482e24004488c075502c05e6014808002003405411005004400601c008010900d0045034505140c0100079499400001201c4142c03800c100d00c00010b001894003003801501241e0000d41b03a80c1d1440400c0d00c011740040740c401e45019003a54490140701801c0704900510003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 709051555 1250 709050305 709050313
    0xa020d06060c051504030c0f0c1724090c09041113050408092202070b10240e0a0504110a020f0d1b0609050f0d020d1404030b092b02 58
    0x601d4200303903030048442d20094040e412034000c07001d2420f0031044003a0024401d00e00310f80e0007003003501c80a00500b15401d04503001e00b0501020012141c1c0b0300106811141281d001c0d01c1703100c80300c400c01c55180740344c0d403c01074142800b400003800320902401403281503000503021580754070b824503018020918540d500c5100304c0181d1350041c500d15480c440d0b00d204552042d1445d10740740003e070801544078444445820070034201844080220101e0019000700303481408400e0460402c45480220144a50454038a8201c0100310340390b9079001120503081c2101f103041009c1000b549001203000324038903420141e0060b06049482d2201e440c6580104218003141d425079840c0230030312481c15240d86c810564180060211052045003143d0300c01d9038403141d4841c03d030000d0300080959a031400d105000380c030340c4120303000840c00001e0302e501413013281620120303850311004250b80210301400502541c0009043c1c8503801e0f0020304031160030018680803140b1245007100c40740000b005c1002020b0001d04000050017 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 709052805 1250 709051555 709051559
    0x120804260f060c0702040513060e0109031b0221070b1c150803030610110613020a0e040507210c080c15030f01030308040302071e061e021f0f050a020d06 67
    0x2004a0b000b0b0080210110740c914002c550780030000500000342030b90700140400881040000c1c214030030342060310070060010441c11481d00340504842c0d0791b901c90580300c03c02d644c414001a903a01307840034000601c804502a24034220380341c0c0b52074828140c20814200000092108050500b10180762000003858070900c51803409140803244017010f480350f10000da005002080d054071740030b175841e107080d100c40c5030140340a00c07200601460448143e03040c4810038200164070781582841d5012001034204030300768001c3c9042c141e03650f6980d1000c40c426000d003662110704210303c0340c64180900c14819040b5000724040d6454074001900e400354028064400c0c0c1e01c0b1400382e15070726464010380c2d104410411824003280e20316181a11101c0005004a003180203000c408100c1c1184072420601074504a24801c50792405d0440181c111070b010041c50110070100003400d040a41d00140e01074040305c8181d01e400003c070000c0d402301c001d800080d0340502c0170f900300030801018801c3c5a014140390f0302651000d00180e9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 709054055 1250 709052805 709052833
    0x151509090e0a15051b0409020901020f060c12070e03100b0901050f0d1b1a0306100509031908041805061503072a0f0b040b0907050a12080426 62
    0x1eaa060010100f14080c6100180300203641d0100d5400b045c08410413003c2641c070240303200240d0164002c628001d41c041192203003544e0410040101d41641d0004190a00300b40c20340c0026805030340052104042182d00203400b0900c507050004510001508490745034001c0c54a41001d04015080d040c02030b0040c200008607443d024a403840028000351007090402c2503030725406070000c040c44a0024018072400001000400b0f0485400306e007040d0820aa102e0401c001008001d18801149104000050040c840199000703c2d075010f0204031258019450182031520302014000c6600051281200100c9000104035541002d4882c4204031000188081f074440502078501098508100080c803c10002c4804c600c10010300c01c0e411541002e00200101c2c9658003000503c0c5a44100e90b0400c190040c00304000c501880c0c507400c464010041c20346941090085902e84441c0c0c440d4035807003482c05c05803c040c041c402e011580075044052a035070300c0d0600448a50024241601460403030300c55080ba0204807 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 709055305 1250 709054055 709054063
    0x2030306060a0e04090206070f05060703090c090b011e030c1b030e0607031e0e040e01051603020901030b04141006080105210f16210f06151509090e 65
    0x26040c010166410141036880072260030454940d61038000d6681c1c4605800360303840c4030140003c24031410200c1d248414130f280450a00b071000d00100300781814a00d00358000361881d05103c0503913090680c0001c4020040e0012119070b40c03000c1025106d0344424018002c15680f60304051700c0d5000c40c0d206e86c45003060341d94103021600c00c03c0c10302038005049094404c01d1442c1003001011030034081d1404c0b00c143c003000c4034844000b5680005020220b002001c111800f070429018030f40400e4141c4000300024034058580f14041100e0300c40000426070300103140000c580c0282e001040081014000b000451641800e403099014150782d00c0440d400810070001d40036104500c01410b803030015001c4880312400040380c5490043c0e03c00301138810300485032000b107240400c22010b040e400c2d00c004110100ca15108843c900b24181c3c081e80100c0075580741030b04020512000b441074607640e10040010b181c00c600001c4400c80c0344150808007600e10301900038551203611004180c1681d00d0520100030507595800002c0d51 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 709056555 1250 709055305 709055311
    0x1317150c040311150a02100605040c020706030b130f06030b131e0623011a0708030f06030703200901060e010806090705040b0f130f030b180106090c0816020303 70
    0x4426810881400043d00c501d0007400c0c22071003d8a00c0044002c0b6030035608a540007040400d0044e4010100300300c224005004140040a05803404c100782003414600a445d004640156001d0544408059030b842e1030300f03410b0b0038401150703039002c000c54103c1ca503903a0301810042c40292080c202e0703803010421180090314030300c000b00e40c012420481c900b451003910140011040090701e10560b190a862518000514584030955064001103403d40c1040d2a4219005110045891291050062000042d2200c04403a0000d029560b80202c5540d084002447c1500075040180091416240349a0800c40b0214804203400201d401e485240e8840d0300c00c9803103d0520150b6400100180b01080b12410003814040e000400c6161035483c090701c41c5040105548009000c8003501e100082800114280748403660140203030483c981d54070b0745191110907103400003038905045008000c0d00b529541c1025802080145a480014815041405000341000108503091a5860444054002e240380701108881c8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 709057805 1250 709056555 709056571
    0x20405060a0305040807061b021006150c080f0f12010902030c0d091406011502010e010c08010b0c070806041109090d1223160207060f0c02090903131715 67
    0x82040c0480070100c01611024200740c8818108011030004110b290040680d04500512041408042078078002d1424a8403210040e0f55071a1443c00d12180e22407042204402400d40f505e4141c603030090400a0f0544104041022042c07000a43c802e015481d0340d016200421000c034130800313103a90f00e1001300180e10040303607810480c01c000c00105041e10b004c3e030310180300c1500a82800d00390799260b282e0f0134640502078000e03040b040fa00300e10644900340c1c24010340b44000d018034000e210240b50010702400c26081802006641c1d00c0c0070520310454801044840700034075085c0100c03055410142081ea80d0002000740b518011200341c000501a200b001079103004090301a511390342c901c215140250300070541070030b80294014401a8180c680c85240f070314240603050a080d0207102c003001d4a00070340b4100e40b41d8040c3e018084050510f03010541c0105800300040c0d01550f0308120360307640c0c0310b61781d0552140d0b404840c06542c0d086408a20202c15040c0013003140c0001080340e2400c0c0ea42d01c207140a005081350541 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 709059055 1250 709057805 709057807
    0x1b1f08060310020c2a090901050a2a110f0102030a050a0b01051c02130302040e0c03210904091406040f030f0903020f0f03010207050a050d0f0e13110d29010302040506 73
    0x80900720f0068a0900005d81d4400d068004c58201000600030381c41980c40c2841ca13910750062020b020f40314070a003150000001d0040c0c1c070400c920182036207821400c00d0000c09001552082d007580450600c111030b0850080750003150349181c50108040244425a2906500303407800005035840d501800480301014410148d12000c01610305140c4c0180d440918501c00091a1601c0000142c645024040b400307880c8a001c0d080f42000c20081c586882d602c0300c4883e0084103000202c00316884403600300c0341c03500801e44010604000504020611160805a60429100f0382041100f44075240c40d491411910a55aa4040d80031a07030703048072408210f020103544411030151610300e5181c440c40c4c00310707001c1d005800036082c5025901da543c10403401c0c41f401d6038980c200158003600294001480180f081403420041400000c41000c03600c041b20401400507040d80c0c405140f40c1115419042e1000590a00c01c18000c0240005440c2e8225261040ca00b071455a0441c000c4c000398000d00907103041d240007030042 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 709060305 1250 709059055 709059073
    0x606040c030b0a030822180f0207120c05070b130603181b090b0d0b06040b15130303021207381003020906010807021b1f08060310020c 59
    0x80000c00c440c0c0300e01000c0c140d60308060301c202d407140c0025100442c0144002a03c2d000485044040d13072002c803000700c3c40410022404e00c401140c420074014500c29941c80040c01d514044c80a400030700c1a114045c00c41603c3c00031540180d50f10140e078000765441502501c0711142d9500e9100e10300c3c0145661035030f203510700940a0010702c4c840c1c1d00c111030761480190300311281c00b420b48440765101c1103151aa1850201740c88280480c0310340d8003c14080000603101290522030645505101d0b0304040c00562081d921000600525656203001070b080003c8101540c0d03585c1c1c800d0501c80c001e0352907407004274094002e28031041c034550642419105c0440d082a400a14404400e407401c0442c0c0242c1d41038010805903595000309024050346003840344124030084c1c40003034114010401e0208004229904009550081110543d4040340307038402e138144250400710b1651440002500c007019054a04110668214100740143c0e00c5081c5e180110340960689410f9803c1d940004264888e22403d26400e0b8018415 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 709061555 1250 709060305 709060309
    0xf05030415062c010608070f181e0605090306010e1503010c18060c0b010501111509070609080c011d0102010216051b0904030c08090109030501151404060807090e01180609050607050c0606 82
    0x560081e01ca80c51800941441c00d8084c03c4024082c92b42020040d05003400000700ca0030b01844480019081d03c0c2403603800c0c890088006665080140158031b2810498004507114644000710301e0443d0340002c0003402070012991009100c0030704150034001400c1084e000040041c01040a40c000350340008844a090b03080c24019140c41c0c0b0080300c02580391150005461a000c0d940710014081c5181c00301901003145400c0c001001c070409904200040d41106510700002e0ba00003000445844a000040024401d0280144e00901482004550318401c08c02c42d24200040414861400055922640c518101c81810311249641c00c4900401169903161500041403c4401a02c3c920905160040b5850744a0781c0d51402d541280004840420701c501c0280640c02e45420304140f441801d4500300111480c000795035035202903510502c02821303610104402417500030340024070700c0380031291136801c040b660f4684000140780e002019a414068400810b041034810001c540d104450b450050070b8685901007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 709062805 1250 709061555 709061567
    0x2030a0209090a0b070c2d0f02031c050c060f01261e030309062211061b0609240109180c0605040501020601050a060f05030415062c01060807 62
    0x210041043c4035810503a00010344131a0858420107150740c82d807008011a20300810110280c45006c800d90740b0040342c01050303080580b042e41c41c3d990050701e0061b001c16580082070400c2d11200c012400c074440c2c9850301c510b541c1c000c0c00404800558000701e405070341c1e4080850b0703c111020b00918030740103441c0c41c0021045403208600200e00341804107881030850590703d00d41490540b10110041a0008802c02907040d030203000166010000c01e400c1f001c40e807180031030a02d4644d21414001c10703000d582000c11084da00d80303c098175840c802c0c10044260aa0100e10340e1307603a88204555403101b620503560070450005001400b04540046070080481c56401d144016010300980b00303180013030481d00c000c10b50114100392034a00040c4000c0d101c40d0383d43c5041c10002030604005800c90750050754401000c210007503000350b009841e41814501f0507180c3d103591406203840070084070b00002d11410000c0200c2ca500c80e02c811b0090b684044166017246082600412125403030034401c0f00082001500020344a0340108 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 709064055 1250 709062805 709062811
    0x27010207050108090c0a0e180f0d0507030327051603030806040903021c0509011b08120c0c0d02062212030b0d060204090603052a060f040806041a01050a0302030a0209 73
    0x810344080c85c540e10007245c100600369003d40440142c440901c0b024480c640e0403002090300490140c20264980700c85940e40b8a0500e17105000c00000250b00803c0c188a640018540004240111100004460940704180c4800c0081e42d581c0240183c1d401c8512514a280049a0307164465103020f41c2e1340b40c104401030440c4a0183c055000d034040c00f0310540c403412481c0300c200200b030b11f03296207804101000400d10141c2c0890006000801d40e090800301d1205801e0394114076916803441015036030b60207110124060481e0090144c45560402e00c0c030250046061031040204030190004010904054459103d030264007400846003d0f00c50700c00d09200e60800080b4400c06040d02c104d40d510350f95550103ea206a00c000ca03403035038404080c030400400f40300d00e003201010094516100710190721201c00075010b040580d4428500080c2c80640039620505890081c000300d020382e074040c41d160800500a81c80000200700100205002141614019041a0a5980150080c0b01000c00750b420b00c0b408400103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 709065305 1250 709064055 709064071
    0xf010608071e0c08121603060b160507030203030c010c02010b0609010f0c08160602030907121e0213020415020d050c030d0b0f1f020606030105072a050303010b27010207050108 77
    0x12040d036002003000ca40080c40317410102280d103080303490a4a9507155146c10340001000b014104202000114103000c00d551400d040c880c0c0c0202070700c00c245880c0d4648500740c0c0c0000e4140c0400700c2c45010801e0198803090680600d50002d1180c4030006003004420302c500e01c401408940340c040819500352007445641c90341480760400ba0316107460b5140e20745403400c40140403120f0076000000c020b8041401d00c00d03040241903182010001c4025070390341c55240c408103060103894111511a24081d551004501112482d011604550310790b00c6402e840b004151418181c800740c400c0c0c0490065440c840c40444200b0084080903604200426607410301500580000a92041010004524940d541c00030440c4201008007101e04100c9050400317802e00f80010102031190745841d007000055900074201c0000d003410304452031000c2e240841101080580d291b0b002d0320324072002c0004140b54883c4001090385400342a1407070301c2c02088070410b85140c02c001d0f0080740160413000c81086254002e190303140d0040c00d9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 709066555 1250 709065305 709065317
    0x3020f160b03091e0a1b0b12040f06090b0406150302220605030706030c08010b03130b060118090b120a05030426060403020303010f080102090f120c0d05060f010608071e 74
    0x100c0d035060240f0805140544540b9006400e80705d08102e490726500c0e00b108052205d0020326894207914806a0061a041107500300125000408100c5c0820042070100d40c0070504018602003414000c000810071030b01100d20343d00d80851106040c11010110085a600410044182c61142e001110104000d01030a038120785604004c02d441e41c00380b01c0c3c9000b411043d070300001c0c0400080c0c0014112101a84400301d0408108144042070354414105102d00b90881c260a403151540340049984c0000d44410300f0250b1040580450f4081c495009202a008215210603142028a1080392100403c440050142e40100300400c800c40030000c040d000140e2040d2600401d6015024441c00d00108540440050300004010700c034450420920340c01074496031000310300b49807183c0c0c0455555072240d0f402c00c0c07207151000203129000c1c400b001920002c00002d4540d8910031194640695035940c10341d11a8580700f080400400c3e4640315052040c41fa1446960303200b1406410000100c83c5d801d01c0200c4405c12103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 709067805 1250 709066555 709066573
    0xf06020c1501120b0f09030702040b010912060e12160209071b05060609161710090903170609070f0513030b0f0a0b01110309121c080403020f160b0309 66
    0x40d224507018000c1003084692a0340b515075152200350490028442d604030141c040501c13030254130002c1900c1c0000d81c166000900070700440b00584220650784d002400c0d00010401003010025240c11055000c008041210303880c2c41c052180c4104c5000b00580345500403600c0c120440986841030103a5002840d82c103009100d0f1240d0003120b41c15030502d41c0150ba19a0241081c808203040510b840e6601410b01c01c030340b50340c00f1600c007801406101c44510301600c3c240c00e42c001c03900d9585919842d5009001ca510f00f00000302d0b10b0f10340601101318840d84a817046d034402000469600380244100e2040c841a5142c03011800c0d0008141c0d1950007141178030403111081480480040d9062421502607000000d01000f2894840c00400c16500080c2103070f41001442c040da036001c4c440000c00d0710b403500d20031540c4124401403440c82c03910301030011088503950080003055410b8950000300d002c1c0228020707801d456400d41d0826440d603a542c41c090350400d070000c101408000825031003015580214011044e140400b0b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 709069055 1250 709067805 709067833
    0x7060204090207032c1327080403030e0609011e09170a0b011d07120e06070c140a08030105120307080706061a090d0209070e101806080609041b08160e0705070f06020c 73
    0x7c5503190080390600b00c0000c0500a06800c0b100e192581181101c030300740350254000000300106500c814107080760787d824083c550b016000e0f0b004a00646200d0400d50403c03d1100b6502d41e44d466800019a010140e0b02c00101780400541c002000002c9030340e04110891b00c074046d088643c01c9101091104080c0d5500c1112020030083c00000e02410f0183c0c0e03242c00d80b0840381090040c0800312840c1680c6540006a5000000c2c944e0b401c0c4c90454608035441c10521440044031130662040030b0004040c40c100041d400d08114456001e801034039480074007074079144c550703010302c20280c440c4909896000b01d032024000e006190420100d58400e000c0d1904011100c03020010032170541c00482c408003c5419600200c0145100d00c42010080c0342c50314014030b80f420540301183c60504041c0c0301800d41680800c005d2400044c841c0c4850007800e8030021102510108015103a000d01103004620341880d5000c0420701d030303620580548010a070440e038540c442004c69998003000b58440c94803c51180500000d105681c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 709070305 1250 709069055 709069121
    0xa0b1b040f0302040501051210111c06080c0a0f05100909090b0108060a14131a0108010b1c03020c0130020d1805070b07060204090207032c13 62
    0x14181078100000003825441040143d460580240e030040304450480101298009030041c0500384d5518002000e55a600c5a035034148980c0c84901c01c1c4044100101d2010880e51f070194040314610000d0b21b0780e03140300c68200010071046100d1007034410940d10040c4414175003915070b5201c8011500780741c034605079101003c0059450400c801d0310404a07407001080b003402c050041c0e036031019107408204030800e50380d104400c54841c040d00c410030740f640b00c91030b030b000300404a020041044290b48203070070190307521080766002e070082d5503925029207a80768070320082100c00c4c80000c1c6040d42c95005040b058081900459050600508203403030050549500c0001c01e25242481c6000303240c0f450056611400c00c405441543c01c600451313100d04038504202c00c04030340d000c511041a90001805107030341d070350541400e001074019904250841d61000650004050b0420a02040d00e11041021f180721451480c40100c0182c5101036540c01c000c40c00741800b030803d4280d12810b8a103c80781507003002403169008001c45 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 709071555 1250 709070305 709070309
    0x130f08010506131112040503090913050f1f02030a27110d02030c06030403050c150a0e0d0806010302090102120708041701061202010c0302150f1e04050a0b1b04 70
    0x5075501c01c2406018284045003404541c2821402e014404c0380300354110161062114038000440c1c540003080c2000400e01c210ba4460900800d40761007801c0c1403001003500385428404071803622424074400340c445008a07155101036a800ca6482419002c0030001002e544010b100e49a40c541d1000c52401085140f811500c4507502c0d030b9003500c00c4a40511340500130302c10240605100e261104c00200050b80c0000c0da03810350031300c243c0c0c5180d240d031a6442c2c00e503070b0360080d00c00c00d602c00e0049201c0e541c092101c0303054841c4680c88000082c0a00403000d900240c50380180c0141c1c50004074a0303400605154003c0d0004c1501c124103104843c000d101c0f508038403846420050007141e081c6000102042200d000d20034041d0441c003c200204400c514100f080a0115007000000b4144441481e403542494024414419080440b074000381d400c1c40d18807081c41240f9002c840705080e03091444c401009411082d542c043c81103602100818a030842510f503510480700c000c020f40c1c021302c0e8100c6241c00d0101441c0203400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 709072805 1250 709071555 709071569
    0xd1e0c231306050a030614090c0a1e0c20090609090708160f0501140403150f0c020610080703030c061109060c031206090609041101020708010c053c130f 67
    0x340b070b2101c02d0070080c01c0d506c040e4401c0310020310a101c500c0b0690b0360b260700035800c01c8198580e903944990203002a20120018884882c1e00c008803940c0101c900e030043c489400461141d105040f04c40013401c03440b80481c100d581a00d030070040b244000364a0341801b000c0300307400c640c10f8411144040d40d00e0302e44c1c51a00d03030034400000900d0400e0700d040000203648003a0038080c2000342004411789001142c83c5615004921003c2c00c4c209400813010940501a4015000341c903220506001040030380c40042d42d507074030540c0d0708400840340d280c00013040040490080e0550f80d0568605030191800c0c0c403103d000e8100c960f000391002c0800c000300e03149d079074888004143c04071922001d580c880442d0004e005802c14018291801205e1150401900d41c1c2c0d0400c6050348a40c2c021041c1d40710b82c1c92040102c3ca08841070b0030106082d868480010182d50b00039024049501009070314101804038a44059190000249040c5451040c2c0484641c03942000b00a8807001d0b0a40c0301410b1210307600c8050b401030794401d5100c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 709074055 1250 709072805 709072807
    0x40506060f03190303270308130602070206040b070201120b060f1b07060807090f0e012702210604020903030a0c031710080d0915230d1e0c23130605 65
    0x180110149206c0c00f0181d40c82072041a001c40c541d9100649001d038001d244101c5545a11168002c0240640c1994841c5402810450726251904134002c85d5034407100d410b9020070041011268012028061703200c400d00c0c05082d16085c043c041c2c41c003002d5034201c1030004220401600078105069010050031001385119540c49403141407602020700f00c00d141e41c000940c0718a02c914140204441403450604603030024009000c800b82118440070342c072810740c4410030845c1c000524000c20030324541240f904c88124041c01d1140e034541ca410401244103201c03420350140c005104030303500e05001e8034420007580c2c020301707104030365079100104081e00d108211407814249900c2403041c06554001c01071000f00018500f4482101800c00d0300506904044c1176081c81004003440e1001944003d5100e600e084004248040783c40d40e0150404401800c201040c90040c00048814540c06481178000c98034800351607182d050820104000001501d215800c804001010801c2400f4409071074288600045c10156201 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 709075305 1250 709074055 709074071
    0x4030302041a09030d0e01180e0a0e060f22080f12130309090c030b03011b17070c080d0b060711090c0906030a02090d05070810050f040506060f03190303 67
    0x4062141c0c00000b10415600c820300c0710400d03e403400182d1000184136410480008903070740c40100d50041088030350300f0320701c941c80030005400982103d00e6801403051001c1401f401d403401c0501360761010708944040c1c40c4041c180104000390400c01c1c2440d1000900860000d12030301c251181c0742c450303000300391203e220500060390081032280e400c80d1580044488400007020003080d10300078090b0820b40034020a080c0c0e2680d10180190180d40115240c0034058000e000d200010b1640301010340c420101c841c003050901d418101c2c1840070a2410348a2401030b2144050b950741510f402c842d507004068030800640d65904403030003603980d0201400f000d5100e800d01c1e520007083c00c8140400d109000d841401d100c0c3c020b02c984a09030380c0305030a4980c000508030300142c680d01404006032000e014000060304900600d40e012440b40c00200c5c0310000003902c0441480980c990641c2d8910101c411100a0065003006c1c000c1a00c0b031070410b1488000343e90080443d400c20400460940c00312140180880101c0e0b80c880d80c2c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 709076555 1250 709075305 709075319
    0xf0a0b07090f06050702040b061608070c0605040602060117100203250e0f01050c07030c0807090605010e060f0706060b1c1a01050a11151e0603070f1505040b030403030204 75
    0x1070202a020032811030340300602d480c2c0054074038020726000a105a8903103181c3c003119298207081c0c032840d8140c0b101000103109582005000e0768040d607002e41e080035000e013000c11414001c4040341c086400c5a40100b000b07a1900f40c00d500300140040030103c140c0100c0302c2fa5120156140044c5005880c121540ca190042c3d0b202540d086001608483c01481414060780900e607840e401d0595100100382072940c0c1d12000400118100503040c1c100508028042e5030204407200000340302c400380c0300c040c142004815280c10054610001d8280e00c0d50b0b00400c10032008150300a120b01a028161284101055854407203d244040380c100705024200c00c401e00c050186100d04901402c0c0c00c103803149580c070401983c4070000038024800c01e5004014400c0004c0c488091042c1000700c05060402040c14404905044140002105022144048000078040880c0c91480d01045030801c0b00c0341003c20000403032405842c42074854064404030280041070000084800e06007000318400c6100b90340040ea0b850034021 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 709077805 1250 709076555 709076567
    0x7090320010f0201060b0430060c1209020306062209050c0f04140a02160b0403090f1d1803040302040207060212010609140904210f090602011505120f0a0b07 69
    0xb051801c40e81880300030800e50210900321019980040042403044005c08404800142220460f241d405c441ca0401070520855910003170021002d5641c1d00e03183e50303504484400342d820f01140a0340c0341c0c0080010a00a03d0f2144410000311002c2202a0f0040000303022181102c00c201c40a59440e00320402c020302601c0c00030103001061f00111020000080300350300ca0960300c138004061010081e0700290041c000b541d0315900115056201113605024517162034002c1842e1410301c942c00842c2c1071104c01040c0d09001c0752000c40c2d00001d0405003042a603842c0600312940c000d40701c82500501040201001688550008201071402600c026035103041030f0703031001d0180b0070590102081004220040c041e40c0703480c400800c99285c08a80c0d412850301c03542810030b1800e030740c698040d02c000c120014000798142c0107904078501c41d02c180c441d8803d080e074494003039007680c00f4010100d00d01c0040d09801d00c51407404500d6111405d50000442d080c00880c0191a49419551401030b07655901c3c00c420040c0c0154000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 709079055 1250 709077805 709077827
    0x210519050c1305040c03060302060a120b010806030d0309240e0c010509031c0207261b030c21070f2c13020409020a14030f0d08010e0709032001 63
    0x20419450041c4a10300e458080d445030207840e00c141d4172072500200c0d1034072a402040145070020001640c8040300000a0a00c10449006880c183d0a1070320003541980103003250361040c0380180140540c0788580314100c0080000740030480c1c44134615811100050002c14a443c1c4902c1c21000014241801d03144192070b0070614000c29040000070800220030303482c046801c5080000c54801c02d07450401c0c0584c268140483c60700300d15040c0700c1083d03c54200c40060f0340c41e024683e10100a0b100029411552441001c0d058010a90903600c00c888603196800c015288040404c91801c42d01c1d50404218030050030006240e10100b44489200c00c02c2c4080c030041d440d202640410000a9021142000c901c0400004000e1510305c5024210395020195200c60304a6242a9802403104d01426100c0e400d140000780e005613414081c0c850304850030340c03140001401100b41055521041031981c640b8410541c04200103000c8801c00507030b00030010004240412108038131110140c500c1e6801281d00c00149511111 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 709080305 1250 709079055 709079071
    0x21005090601140907140307030209120105010303081b0f030c130b03060901060f030e0f0f011406130e0a060212010512010c3f091109090d21051905 65
    0x764004210f00000843d803240410000e89800c000c50707440000c00d43d031490210510200380c500000800c0040e65250340100781e5000e0403140c00807021411503103142203620074000103020480000c04600781c5403085c0071020f10501c1c48031040c1d00c1c1c500c25400d24201c58009440c461013007074010841c883c5181195400e4009040482e114604501d0700600141c0e5600040c4101001d102c50341030310401c51882900142c101d040da01048071844c18031142e85036901c500030494917140b9480c003200107a07240b41d101c2400f4010b840041c205030030800c807101200010140c0c00d41207440c2c2e1180d410014000b55050001d46106c240c11072101c0d40e00d600d00401c0c091303c0c15405101c284c09900d41028140038541280140120202c0c40c099401000000d01780d4050400b01d10002d142694141164030500117420742144408034843c0d01400f07041554423091108911051700c003924076404c004500c6e403015100383c0c0d2000f01c004221503690f2400142010703050031580c00360740d240441346514400003504280382c041d05030401c01d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 709081555 1250 709080305 709080313
    0x5040e040f060c0e09240a0f2903070f09080d09090501050d0c03110f09011503230703050621030c010606090b0d02030601031b0521060f01080a02040305030c1f02030c070605060d1202100509 83
    0x1040d015100e640704c01440001800309000341c003c0c020f071007371020202926600d0300712151981c0c0c085016003c2c00c00c80c8a500701d418240400459903040800b4147c40300c80c2d02002c540c070858210341d14240a1207124030340c02c2c0c10840c6100c071640140c0e0f502c40c40c2c9008018458141402c840b03540c10080903203440044003601090b444e4803080d0207441e200840d5070f000095140c001641c0c2c5903440001c1c100d51090303c110810b2604180282000d10010004101134100203000300034140ea01e21081d240081d0501c030304407801c802030056114400198006540c08841450001403c2d08282e0080004044801070312000400100d441c494206c814644c8402e900700c400300c00445490b0400000302041448006141000308580c01305184201c143c06a90142d903118060341e407a90040041c09940311003140907441000d4411f00da0103000c03007507842120300401c04ca81c240c51400d00203860f4040039242c050722035a0000642000700e00407511103480701c042e40da07403580601803101c40740701a81d040d504003425520441d04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 709082805 1250 709081555 709081619
    0xf020f190e180f0915190b1203030408030711160806060a08030406030b0111030703170703150504020304050a0210050a1101050105030d0f05040e040f060c0e09240a0f 73
    0x89080c003592110f400c9800c01100d036201141e107810000760442050030716540c2010321182d8006d0041c044a07001c0b01400c20843c088403c020840021114100003480341c200b0408100407a0b21003000f1035002c0741070300f80003100104511896107852011a022a100e120190051140b0a024009244c01006c04c07288040013030709001c0801d803244240d01c1050207056690000b0790b02039000304102850800413000350f9403242054107024002d5882740902120355804070001aa8a83c064861040c2c02d407204491b19807464109030901c002940301502c21303070b4240f181c0c0d1002001a501c1d400e414012512598500d078551010706c0002d001c540140010800c03e0341080010720094400050000d1100b41603c0e00307000754020420159101d214503000103050a0900301004248001d8100310303032103107101d03620402a07284104812600841c840c3d294550016165010465041146854000c54914210080c1c40d000b039030000507905c00903a90102814000c0b00b1000c0008010a50400303082070460007a04031203207 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 709084055 1250 709082805 709082839
    0x30a0305011406181c0b09010506010306080f0601050913052a040c0512060109030f030305060f06031e07033902011b03020d0b1309120e0109090f020f190e 68
    0x40c0040303000764040c0038043c05a071000e00504c40c018105c944c0020f05484c00341014131101e4007034142200d0240c0440d05103c0c001966101c0099503803078581d0544040e056590901c400c101c092100900070450782d011000b00359004c07510911014000700d2083ca4400d580b803103a2440303680309584110030948a1840c0c0102c04081d190008110345128029501e42103641d0303906001a503101e401600081c0004801602032020141c055018900426088441c0412440700404000c210300c02118008180280d82401d8056040303440c00203034000302103003404030399092900341400046843c06107100124805002224081c2020204030300c11109600c001d01040c6036030009074580d102c9141040040513400aa00700141903030342d00150342d03040014003040e595020307a02000042c2218110540c0c640c115000e000003402e020307142c280f0700407030107071601c0120030714010f502c000502425180d0070106400300008284425040c00828588024104e00740380c410000800414000b24520390f94002c040400c403840311a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 709085305 1250 709084055 709084087
    0xc0804020a14010c03120207050106030305070c0902040b090618120109031211040627060e0103140f13060b120d1101060f0504020906190e0f09010e071b05030a0305011406 75
    0x102d50107046c00d1443d2044a260704009214001000c1e02079440c1045c044205540304006000a90040e01c0003045c40d611400440200e200701c4c8182ea0304c1d00740412007050142020000707011494205203010710200d49a03004a41c28034000900442141d5407490442e08040c0c00c45001300050040010810441c18441e0646820b0f200c2c070301900092003050b00b10940003480c1e0300c0306032210201e182030f030400c5142c0d60308c409044011040c600c0c6010a00f0403010385036604c03807154624803070310740d100d00c61029840307002d554690104001c1c001da4aa030b88440c482c00882e03d80080d04c483c11032562004002460400385d00822511100c8080c660a90400d80304100145202c0001c0c41518003ca8005a8a0f00400001003051240c4100060461341e0701c0c20707280f9415041744424000305404ea48420114022000b000011107090184141c4a00c0c02404115142d100750100211055204901012040c041c0c1b5014555000603281d000025141c0c8014050540020000400c4070401d403491414118040580441 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 709086555 1250 709085305 709085327
    0x6060304030c0f0611031009020a0804061808030c0c0f16140604090e1c0306180f0b1804020102010b040506060a080c0d020a03090c141507020109090c0804020a1401 72
    0x411210b600d114003800b10400700d00421680c41041004003050300c070b1210070181c00854540f80010401040050502c01600032540d104d81d55070740b041c2103582ea07079564500820080340c424400700342050100c00060480c0700194001c04581340007035100c08202210501e8062071248019207074002c40752941901c2060130040c01030300c030350b254a000740040d5200803600901580e402000150b08250b407005540d54046001141410050b03076070b0004150b03050b02902034a5941c45401004204009000d8600c12710394080403907004918004145c8091140c000b0311000c2c40e00c0210440083e4507014030045680910a642000d901604c00380201d19001002071a41d005030b0115809001441000540003503026049a000c007140310401c644923410084000d009008483d021685000c600d00c011a5064106603103a0483d14001c1402c1c1041804d09042c4207a038002c06001c03414445e84480100e07030703d40d5601038580c00111941c0c4102e030504c2e00e4010080c40e6010303588100441c08105010220f43d9a000e5000d0304 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 709087805 1250 709086555 709086557
    0x1050109031730060306010501300207080403151811130b0901080a060614280308030114180603060a09051914120903031206010e12010605010f05030606030403 70
    0x1c3c845400c014000410b81d40140e40d032907104010302c1404440aa0100702d03034080c0009604851180c0c0e01e80c00195448107090507441d000b042d0107030302e03440b94002a0080301c0941c01803003c0903040c07400e1a40c400810ba005504100c5110020320700070701503905184a5080042d0940c80c99820100301500d4155041c0001401d0318010030003600c0c5007841407641e800c4a107140101400f250161340c1c0d80c013002c0b902d8006040044039010304000000030045019103944600c400c0007003400340700e40c04800403641156110400800a0301c07541a0020114403007a003e0b500034480c540c07203461500b40701c008002c40300c001810344070b450b00281d4060000c07039240015025445000c100340001d002072a410010b00e841e45100d41d520700210400c103180100001d440c5071190300b00041b0220340351020301c09100e01312802003800141e09a4414000c05100c106091045900041d060410030203801002011580e22003180c0b03004a0300d691120010842564010b10005000d981c0d841c02c10f0450810b44d00041c41d620010740301034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 709089055 1250 709087805 709087807
    0x90e060a111c0e0a060b120318010c0f050106150e060a0c0204020d0905100b0a062a21030b03060c0a0504090902310501060905030d030e12040605030f010501090317 72
    0x50850554050b5410707800d01003c8810301130741803501e0341c060858a040280140c0501d200c0754100703140003041c1c89900c4180c001c0c12000d03082d0140112510100301c00c0a480b803001c084106404560284a250301825403291808a90901c1030400391200740c407802601d010b403608101e2081481da000328003942d9a5811180980d9841c201c142c400041d00d20901c01501074000d4182c0c030145031242c1d90104101d03400c01c2d181c10725104d0b40c60006407101960545403610441d80140c403109408450060001c0c420300c2015807404440290f075011414045801d441c5c03010070b95070340540302c0070f240400c0345ca0361050790045014505241d8140003400741c02144191030341c013920b40c0700d144110341c1e480e034051001e000e4401882601c0031501a1340b00a01c0d10030741e00064680d00e04000455064402e6180d0010340d01c019004122003600a40b0480044c80604201c24890242011a1031800c0c25040200000c3c00305558550300d0307082540d618072481e007060340058148a00b040b004c1002640043c4aa00302540c2d0f00b801d2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 709090305 1250 709089055 709089097
    0x612070806010201021b0601050f040506010203030c0c0a060e0f0f0705010903060b040603050607170708060607030509031507050a1205061507030207050d0b0a180507050d08090901090e060a11 84
    0x5034003900032809000c42d4600c008903810701c4050300084090403640200c40c02b4160003041014401102e0b001e40700f2a006800401c005805042950028030190f00500e00711a404045074485400302c40c8028602115600003038150070b030503181004a903019000400180c00304e1854200064120182c40c071001301155140c4805c0d100383d03580c0d988088011b540183c00c0d14050300d01218000c140080a20301e1040c05800c07140400c1100d4800c0e25450300c10355001c0c1000d403400380280c509a59542004c4841907052240301c1a442c0d29102841d40329000d08040d85030703203031180d400c2c480251500d200924611601842c1c5401c006155648140c8050348220010310145d642d0480d0804a08044550f00301e00d070094044d228000800c0a6011a075108070228182007119170f405205115410884c0400078000354040c440510240c80c140651800f5188500d0405207071208800100340302f090240c1c441e50400d0755401034141c81c2401840841c4c0d01014420b0b080124840c078004c16480c6008240036011a42c00070050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 709091555 1250 709090305 709090307
    0x1020607030606021f1d0307020a0e04120c02030a060f0f0f0e030a0f02160f061713110f0909032a060a0c0e03011a0307090b060904090f0218040302060105061207080601 74
    0x200e4208507440342101b05485524046295599000e01800c034001ca108040c000361503480b040740c280c0030325442185025540d0340c27102d04071605001c80c20b06903030601804c5200c0e000074500f44103814040f007031400041a2741d952940340e00101c40712001d81c010041c1c1020461206000084102c9500c000356041400502d501910200e1510301210304210650641040126211a01c01d40f072808440c015901d000f0100b80d01c0c4521a1240003e82d07014200d09060815000062541440d01d0038980f03026080030342102020f00050080c0600707448054040d08000340502084518040c5001e95925072075601690110601985549110003003d083c1010303a2400700e410314a100708800c562140004000303009500d107000c4100c140203a1803000c24407134401c021000490140c607001c2d4501c103d030028a0345042001e00010300c805131101c0c0348119035010400787c0e00801a501c820014800759200d08011010785400d1030301919007807040c1c02540c8038003805d10082205100207203a00e40c1c442c480e4a1300060a46031580 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 709092805 1250 709091555 709091561
    0x70314030c040e0103141002160609030e130902100f020613060b0907020f070f05010914280306050f0412030905071a0a14040b0a14041a0901020607030606021f 70
    0x10403005011100004c14032802c9101e0859051003001541e001c0303800c0d62900b00c08c03882205001689050100c00f9070004c03c1250748450300e19030290816071442c6484000040340f11400e10054584955901c0b900b20035070401504030b10f41030b80541001110310300312000203540c0d048000d09003032428448a01d03407401c11203140c0002c0d941c031201602d040c10909080c64040c4d05d45401c07000c1d620301e500c605000043d00392406410642103c4041c2c5411052900b0280031940151003000f405030401e80030072041c15006035180ca0300180c00411509500b071103040d4504001a550090000c284088020b010700c800704030071649103140611680ad0004d80401e99140c15070620b03200e0b900500a003080d0740e114801c0801c0c4c180040c105034095075a0000b440c560a07042d02c0d1745003e00d000711901101c0612401c03030594012504007403044001070742142000c0e03844803000c0c5c80b01000d003410840c03918081090411541c0401c180c0d50002c285003010b100c1e040c18020000c0d60760014020003103480e00d501e0007101d903414481e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 709094055 1250 709092805 709092809
    0xa02040308040b0a030510052409030a08041502060408031302010e0315011409190e12070303061d04020d021309080424081909061e05040b0a02070314030c04 69
    0xa1090b42c4581d5958804420b94200f0603009000c01c0c10500080e0345690510440c40070351703000802ea02000000081002c1d0a6004132001e03030086102080255540e9030200300c201c000501c24060150394508001c12016240038100010056600180c14000061108001d0765400341550030402e075246000e00040b81c0c645007180c0e080344c040c000e103686040c1080104a40d139042c0c9103c140b1402048100c00148241c1480884e40c240f4101003110066615080d243c01075441222030318102c480c0481d810b054225198004041140402c0c0c0c1d80300200000000040301c0c00444074110038101403480d0980109404d1141410000e1142c2c86268141001a40c654040b20303c003504290b000e0b4486481b10014105000810302c0014181040781403860b03020b10403d865846100304a040380c07040c1c08617078025006401c1d0906d085032074980f5080d146402200050f9110301004800402080314103080c01c01a01d940d50280414441e10300410030f12001ca074024800103044500004599526030700e0380008101401a5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 709095305 1250 709094055 709094063
    0x304020f06070209270c0618010215240d02100804150603060608071413090206160302100614030312130614040501050708010311240301060f0e15120a020403 69
    0xa50181301420b000e400e140385000d20000d10900050400d19a803551b51040c51100561001d000c0182c4c0704581c20710b5803500c2c007400381070045a01c130801c01c40090042c264100c400d44162070038200b4101800e9181083d041004000387d400110781072031a00031410350400d01000c001405190000f00d010000d10903100513500c2c01c440801c005460300e910380740002e0030f030a1164a140e441400c002040300e030003002400b84241d00c01441101510001c04040c0041c103002c0c4400c1c0d03401038040c401400c220300c01e8007680c58418440da005d0300108283c170750030034200c40e80c1d41c00211011b02c540d04003440350713140041107565560405001d0380455440280c0044000d94040001302030707070f09007102803c00c031031040103d0b03000e00c0c8184000e001e240d13980d5104592501c0309201c06032113444402020b841c6810005020103038035845d640485864440207400d84460380c803c0e441440068164001c6404c8240e022004045002e801c4039035043c18400850801c480303016805100750042d1000020929103401c584c102d0b0015540 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 709096555 1250 709095305 709095319
    0x9060b0d05251d0f0d0b18010f1b090303050d11090d030513240302070503091e0a0f0e07110a1203090b0a05090a03050a0e040e0307051507050304020f060702 69
    0x140740c07402080100780f407400e200301842c2040411030a181860b2040c041d03900c042e21801e900c0b400303516001c1c400000542240c8041c0b4a0f80d6121240c41070a0241060180c00048007142c1c464480d58001110b0401d4084202084141f0900303000290713115080b90860011100c02142051800310310b0000c521038001100c0c0c1c048000c503020020903400401510a81e10b48140400380c1c640c0c1d4031105c2c06102c51500d42110301100c40080d54503214081e5018080703460142d000c590900c0304100c00b180b48007007544280c182c54060b0941d62111450450100c001400013444840d008900e0044813140341c14002c1c14440178804001d500d070403030a404001c2000c03000d0f0012403005184c140100c0240c0205001070040da0b00a5010303002030000400b80c06280c2c0078140d01d80003480f004c02ca945040383c5a4000c008004100450400e00c42555942c0d4095502c001d40c098024558800403072a00501d040c0000b20000e0481400c0d0040280d03c40d0441e042e03a40c40340e0145c42c4074074850700d90300000d601751003004002540860 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 709097805 1250 709096555 709096621
    0xa03060f1514040303090905101e03020405011208091005120f01090b18060d03051306030509010c08061c021819060611030a111513050709060b0d05 65
    0x11071044002010358440c0c82d416007401045010201c288030324000900424a01041004866899407001341d10900d40d820f05046103458580006100e8031010703403803a140060b00820300551409101c1e441c0180101038511201c4922561440854040c0b485294840c002900d803468000d409103048507070100b90031100004a14019007680720410081c06100c08451500c40707544042d00340340c00030564610000e06015203030b0781c0340d004100e0380150070101103080280511020807242440c1000b04041c1500c2d46022541f407801d006d0440c21108480c56810800c80c52000b0700505c1e0300c07144c80c1200b44c0c0064403404e180f1a00c0c1c41c004501c03002c105502c080e1211441400300648698610600401840c540e0030034082565551022908010100c40300c856540081000700310560081445500c1954800142e8050364000c0500310051942202c51641003201909500c08110041c01040041c0610000401c0907504000110445004035414800250360310b40106260300b0420003880d03081404031503c145441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 709099055 1250 709097805 709097819
    0x21905030a0308070f170a05090a1502070308060604030b0c0f190309050f0105010b090d02010207080a0615150c060e0a0506090d03060f1a130803040e060a08010b030c060a03060f 78
    0x500112030503c0013034184417011212a2003460700c1400c0c400356060070b1079039490301e8000b04001d100c090031440d0039101e4015208001110010681919400030500580707518150401070042d604c010031892042004010600008005810198011004030000742c0c840b00000600b0321706215822001c000341607200b514101c600d0341900500400c51040d03040e102e0300d24800e0b44283c00c1c0c520030f0180018940382401034118508007003040026550051048602e45070741c5628207030600b01d104005403003007511000e03c00180d000328400c0c5c4d0014400c1c03802e07400505181d140000d2003100000130080c4003640320f5000398070260301044039120554114040c0c44076414403000066460305d850010002184c00c1010014110f04c590313101c14216040c04144810038584901d90803002d61244924601e100d0540d40007180f909020400340010300310a200c408801d0401000b00207915602e030340710141c260b0604110300c1c115200400c2c5002e242e80113072060368441050110a8002c0d1925070000c40f02c84a941c80c0000d010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 709100305 1250 709099055 709099067
    0x604030b01091505010810090506011b0c14030a0803040303110712030c080a1a091018020301331121180406030b040305030c130b07060b0103021303021905030a03 71
    0x40420308890200d860391303540041d1107000f0200c03070820000d04048010000603507250480d56105805140c44800342c4102c3d801448503c103050811780f484800103409000d21308040080c15100101113000307100c82042d80e0703031f007002522000341300504040e15000300c2d0a98000e880180c4510035403120401e0004403400c0d0004005240403440000016000b00118080a0484c422018002d100092050900007510140051004090018038440103460f000180d09424030070b1958503c2d00351030000d640d81d4034000c8c0340c40d1100300103103034038020340307042c05450400904041040b48503150034142189240030f1506881c0c20030310f008101080403042e07140c0c0c1c00f000110b0900100307902c485510b884110040c00c40c0c00d100449409000c020500c81100c408140801c1c015000380d0390040d81c80900e681343c41d030300b4201600200d206074000d13084514081101703003c204e6903024041c4002c10a280071410a00f0409249234503a0061201071302580a0306100513142c442340c828200900b07009011030710559941e1400520b4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 709101555 1250 709100305 709100321
    0x8070302101503060b1203070311121809040303060305070803090a09110a0c0f0f0b0402041a06041419060c12090608041103150412020d03020408030403060b0604030b0109 75
    0x5005000020204a00318401d812104441580540b0700300c2c15656038134018000c1d540d11650080c032402c04854480350400003401824800e980d20350783e040800441034a030540c0b1805007180c8a60610801c155629008070b0344c81800012140fa800e1a103135401e082d0018115600301070114042c03640049400700c0000010b100d80001a14801e444a545100540854103803241000d10501c0401c030700c0401520400401c00007034001c0c00781d02c88841403130f81c5440e03a22030314413412078007524610100019403525100c0c154168003480b419098032a403039400510184100e0080041264041c00b80e10307205d4540310001a00d07142e0703903440080042d03143c400180000d2800002240c8900002c2503032010503208840035000c90790591507040458807169035a8442d40c12240c01c060b0503104038402d103c4903103481c5100d140518040c484208100c9904d031002810480720350501400e240c010030003001840c0b8000304440c02c072078101c030f40040e10b8201503002407007a100311351002d1b04040354440003081d00107031179100c0c4d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 709102805 1250 709101555 709101557
    0xf130e010e0d0507050c0105090105160b06040b061e0333041b0e01080a0e03070f0201090609030c0302190803070c0503070905071709010b10030f050c0c0d1b0807080703 74
    0x441d400d80e2008580d0f6100b003110003440b580040032034602c194042c0c0042c0c00c00f044141015030a24042400e025a011032840085d03809444690511903036003814030074a206000240c94140c903005441c020340e8410010f44483c0e00b5141c00001c00145c8100060228407c1030260403d4104900f4560b08090b074008541422140b10341d1824480b00c2d10060b020103500c01180454441d5510205000010f640c6200010500c18103192142d4041c40030714001e00003800d00c1b0b4807540c8001e566030040d00004088004031341246d03040c0041c0240a1012612a58032035040f00d90441c1e0002c401000c43d0300355a4120300c2a0303ca5186072002158907170802501041d04c0041d25401d408581070380e5a240700c03400507200181e60510104540d400641c1a0b0401c407480d15521040c40000400c00d076484c4004503413022104400600021b45e91283d4440c030740c000740900ca401004c070f100950305026101811079110500070b03900c0420700184c414501c51045000391a40b03541130b048600c4d65107070b032850b0508820303130f600080c4118 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 709104055 1250 709102805 709102813
    0xc03060311061c051315020a030b0a08070909050a021206042006030a0c17010909050606091b0a030e12031f080c040b06090409060902090901020906090f130e010e 71
    0x550410000341d440340b00f6900c0d40d08240d035a5142103400100350107440c16000012401080c0c000c1800c0702c0080038000c1010360010303682c108400000b422610b10519281c0b04081c060000c0082c10320000703c84045d03032410300c40014144598a401898102030b00c0300290041000184036101e19808200c05124500569160b0800b0308580324818206030300c04140d91b4000320a10100b540d01d050f036844021201e4a90905481014051882d21003c1e00242d0000c00199100c1241c401001014008d0941044080d00e41a0090421041c1000006080d642c2030491400114034a916607201e9000030b035652030800144d58200c0310b14010303010a94400c07681992107071030302c010b4402e6418441c8661030860340094060035034640800200400f4101c100e1102d503101c03c00b409a40104d6941d84a20802c207445030301c00143c0307112503205100c0d18190040c01c05620f40d1050100011070707250482181d4031444125103101a03110700c00001001e03071088440e40c848292401c0d08109120405501100c80801e00c0e030121 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 709105305 1250 709104055 709104083
    0xf0304060807170c03060d0507290309060109050c070b160306061e0503071107140108070c0305030a0c170901090308010b090d0809220615050403021011010b040c030603 74
    0x1d60310350f400348540071a001c0300d020004000c0703101c1101035a003002d80103100b654a1401925000d207402d0700e5070040c4100c0400f00b00c0049260114013011130a1006584000b41181741c4025820f80700c101c144900d9400b55107030f000203840310324141c04550b0759540c481030146090030700e00b2006c031a08600300705d0000420316015001c100a40a0381301a0f50340508107031450000c00700114211219040a40030101744444180300781c60242007423102c0b1001d000003000c044542007001000410038070001d01020305010062100b40c010985c4201200c1d4410a51310300420024035407181200c4030044040d50888214500040c000509810b410044a0038040e40c0c2d0b916280e40c0360518021244100496568091460108200000c1c1498094031929400a082c0c0301a196890700641940b50f010380c06480c56907807602c0034030801d02e41c210b400030800e6440c85c003d4105030031036010900c06a1410585424420400c50384181e002d025000280b01e244050028010207480c000060040c201a020440b80c2440484032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 709106555 1250 709105305 709105307
    0x40501061d1504270b0a20030711160612050901050105130917040305060a0c0203071a090724080f06010903032d0905091003210509030f0304060807 65
    0x8464050142c182801002240361810400109030754980c1243c010080c80716030201e0844000c1d86201d1a005000000e01c6240c83c20410045406004440401d40c0c0ca058445034143c2c100e40c01e50b6880200340c00c0c44880d0701e040c00411450300311002d0b0000905140740c50081000c0d40d01c41c00031012010740510620154550080355030a941c82400b034141c2103107400a941100032400d0304016000b078080c058503040c803100c15440310056032140e0402e50f07840e4484000e2001400c1c483c80359101c162242d1010f90b080200c541e440c0503409103071150b50740d40c100d605000b141d501181803207900020505541d0040d04020b103080007406a001d4490380c1c00101d0110b41c001080c011a0344502da100d150140d40d0300c0c05c05410b50781d040d29600c42c0e03549281d0300400d1001c401e82d40e080c1c9030000100d00700300644854001a10f04130411008210003802040c0222080104000182d0310b11440500110311044101d203115150340215450700540300110f070b06200d1610100f01000011005005540c4141d81e03070788150f0b86440c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 709107805 1250 709106555 709106609
    0x50d0e06010b1c0209060a02060403021603050a0b0a1b0e13060f031e0b190c180e280506040c09030507090203041403190e10090b0901050f0304050106 66
    0x2c00d01c464140100040c800c040000b10201c14040801d1a005007841c2e5518042040b64000714048000340c0d21003020b01c000c0c19010801d1040143d010f01d0044846070450350307130a0b2141c2c0c070400d00400100408020174006900350b0403035605a4413990000100186013003008006075001500c0500443d5684208440c240d400e02901e400c2c0c56541c402120030500c0c558031110f92480c1001d07440c02030100c541c030080004211802150150103c08040e0f81c4d80415545a1400c0b1003040030006d0030b00042440c0002d1a0381c43c80c0510048170340f0003031110055551402c0300c40a6031600c1e407444041c13000c407001c40c0200810691003e800b540c015030b02009601d00b80c100542d5441410b00004d440d561200000f0081411241c00559001c3d2280032030503008000000b49030318623048414040b0344400c41007844070403660f0000c12080308071421a06603883c004283c40103400c02e40f850146510140e40040c05090f164002c2044841c0a103903083e1940d541d181c90300313106000349520f0155442001038004024030007980700d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 709109055 1250 709107805 709107809
    0x100f0c021b03010209030a0b010806074805060f0f101a040504060306020c0d0f05040e0c07021002030c01110a05030a2019030506090403020601060c170307050d0e0601 73
    0x1800401c521081c01e1100d40c50030301d218540d903501d0b40d0204003030400307501e003130110006040c8601900340742541403480309414110000c0072001005507020310251860010342112100316041508600d01010707900c1c0d50000048252104110025440c0381401001000501d0360301c909000c040300c0042c0e403107050b8042131a19081c1c411040800da03c2070300b44040f1500501c6001e282041012640c078166448000c101994a070783e10643d80d440c1e000c00d0740c1010000074004940c10912a00e402015480d1030580170f00540074901448a082d0608000201d034140248220b43c8140c2d0001e20a0034124160b1100070356981c80552240095420440c1d08031a511444081d6184484d540c4c96a60650340c1e03401d0f807400140080d00400081e44072003820943c804032444000d0a082d20810303800015240400405000c0d960094050381c00740d6400010000426400701d640b9042d12a140b90855845540d8148040c0700ca0b40e07560030581c04400001444101034008005215091080c034051020100340e81d0500c0d2101d10074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 709110305 1250 709109055 709109057
    0x18190b011403062e140f0301051b0d0905030c010c091d15010c12080105010221041403031c060f1d190608010e03041d131121100f0c 58
    0x5004110350400707114403202d0b00c004d142031040c0003905002c03000c900840c03168429200300a2400c504809820300d04900300510704203034024801ca007440000100595856410140364040116090000030403907007101c500756030490104c03512283d5007401c0038002c095414150020a120800010b00762890300e01c5610000d001c4026107a581ea180906071904044080e4024100021005500001418000702c280900701d16030340c0c42400d40c1010006840c0030f01c0307800c40840e52341d10011114545400b40341100c050b00d241191010821801d500424035600071890700350904a81940b4920802c1c21582c44030303046841809940808998510716401c0c84044e5a60240b1103948207000034202280b00c4110402c1003000d0f040000d891950f81d91040e08581c1d002071826036039040044c04000300030940380350399078445606003c0e125508000f24002c4080070070400c01400802e1231070010707460b41e40390f0b113028100c24010304000442001c010070040d1201800104001c80a241c0041c5600460092103541d60006407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 709111555 1250 709110305 709110313
    0x90405190b09192003070f0e0604141201090209130501050a02090d0b0907050301020a20071d100b030f04200a03030c020a03060c0801140f010c0204020318190b011403 73
    0x2012082c2e0180000760055005944004c03a8400d507815480c00541c45042c1c1980c5021501c1c240c0c0400802030b02c10001950320985003800b0611443d460b4079401e000c1604101c500714007020400c10743d0f5016190190029500440b01401c00024100a44e816a2410320a07002081503a8503040014102d02076000016080045a208440011010302209421000080868021680c0e920000c0e007a80d0080e50060b00003107041c0000c04114030000c98001041807000c0c054a982c40c00e040d0749442d80013810341d06401d0021420003103201c1c2e40701d0600d06d102410b04640c7d629903c1c54910700c80d607000034080d60126107035015020084140c0350800e101201d075040090400a103945588c401311500c042000d802d903803001e032400380000024124817854040712003546441071258501624030002c1c1c909101442c2c0500c0d40300781c03102c03a241c0e848186280016030407075005850791038400450301c5095181c03070708000074031900ea608003032844503406d00780c842d900c21640441c440ea00c0e08010031540c41c15003000c030f41580c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 709112805 1250 709111555 709111591
    0x1060e0f130e0a201008150a15050c190f0b0c0408150702150405031c0b090106020a0c0e0f01120f020301050406050a0b041406060708070f03050a0305090f0c10020102090405190b09 79
    0x140311f2001d045c0b00e80009105600090300c5136030305e01454038400c055001042d4002680b20204005000e0303501746074091900d080c001c4030345071100c42101360106c500800c840d821100041301440300030141c03806050300c00100c0d8030016000c0c440585008055841e070016114585c00d4403100c0c002c401c6e038188699071100142d0704022194130302182c201078181c0c4854055880307803580030700c54880b020590b0007041543d00804240002d400e003402542c503240c0103061408400810010b440c00f500800c181140d10b4900440312107402400c000f54103000583c030095055081805020034000543c200324050221800c0401c0068042d00401040380c0c1401000c040c505890000106503281480c09040d025010307d400700d2601e40969185217100400f24022030118a0101d1401840380e8188555544000072030014181d000d003603603009a407074011003d214402c0c808080c404c1070a078400c0d0161440850040d00501141c106a40707071007081303044644880740051a0007400c0415141c40130354640904808014508145 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 709114055 1250 709112805 709112821
    0x1403031014010905040e0d0e2e120c090f050a062c03030a082d040f151404060e0d05030a0b0a1203030506040501060e0f130e0a201008 59
    0x40c1c210803014144049508005030649540c001c20f40503017200030190404c2c503402c10002e02035100b8207070b0840c020703401e40078071300c1d0400d8800e5026002c991509482c030320002100b04d0201c4a2135000b200302c40c0c0543c1805002e00d00340b034010182c40e0540740015200240340e6255401d1120f001500e10480000a501480e0590b0092020504a6003030525807640e014588203003002c1391842d4082290000012501d104020601483c02d9010419441c4400009485440a2115403941802070006401c43d100b00e0081b4080108051411452120a603400d01c40491011459000c08e541114240c410a040520700c2101d1b81002c0b50310b1a51a49a4031480d0940c0c503180780da08010000c1103c459005007481e0400f00380042190100e5620a00c82c0d41e010820f444c0c8102840f0903a401070340b10400707100e100340d12007072b0550303801d043c1c071004a8080c1d614001029803182000042c00e0001301e036001034003030345000d0001e12041c044002034403d61074440280b070f0b100b04414000075900c04007800000860102c007040b884 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 709115305 1250 709114055 709114079
    0x60a172d0115090513120e030f0106080706020c030102030103081204080403241a100e0406030b0106230c0a030c03020f1e0c010302090904030503040f0f0c0314030310 73
    0x5800d0040d40081840d0312840d1821201e0810741c42e00c520001e0b11080201c0c0c070b42c0d4081c031079010340c1c0c92080e5001088107907916454081441c0380c03001804001c18640d02c0ea42c508000f180820386e43d2000038070190356980c08440e10340c041d9019001c010b004d04040c042841c00c3c1402202d040365404130301d5038a0406410f1442d0494400070700308481b8010100000000708a680616844100780030521003040b00d403034200c8208642240071040c0010035101032188482d584d540042401890307030f0504030005000301c030000e4000e1120f40c10041c4103000100c00400c1c12540058000ca58402401c0c032407900e945442066201405a151000510b910070702c0301c0701c0000d11414800c0b40c9503100f8011500040c6000120070700388070303030480c0c41c2d00b04551f020010002c0741002c2010600003002070804500d8001d03c1e202060328040001c2000c3c06120300040070400b0481505520026507810400d806044251880c00d00344802d050320080d901c29100510713540062034084122030083c00c0c00c0b41e40564040c980509644d034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 709116555 1250 709115305 709115353
    0x7080907030b0f06090717071416050c040b0a270207141617190f0507090509060601080906040f031e02070f080604170d020f0f03060a17 60
    0x5500940d10004006240060040e00440c1c21028040c85407401e0028480350090040c694020491681b20713008070020508100740e0042c1c2c80b0701d03229a68521000203070030320744940e5908620f82c0c00b005207804281702020900c07919604049034148007400120040110300b084901400c40c80001e201d14a914140d07110b005507440385800b00000d402c20807142c0b100700401c12890b000d410950042c0544510000c1a01440300292102c661846005010b4425040e600c14030700c0c11070800e0001ca800b102050040f407900100034294014110b40826490b44e110401902013a60410131921038036011507215030082c1030700e40c0f10f0004000200a250b95584801c600120030038816401c2c003107007601c030b404810008120311000c0c8403580c0040650a04e01010600245680e600201403600010107010000c0c25114030071200444861b02d46866039090040703040248200c007452881a1400078102083c2d070480340145104544c100d0b14001c0007070380c8240d151804900381400710616040680c0010b07215298900401c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 709117805 1250 709116555 709116571
    0x306180b0312360a03060b030606010809190c0506030412030501050906090c07061d0a03111501060f05090d030305040605070c12030914060a06450f050f06030705010c0b0708 76
    0x5401100001c80e84c40c010750f400680d1866101c01403481c1d02c1c00d0070421030b03070028006e10340003007140780c1600c0305030701ca20361448400f02d10907aa4803040184103200319800068200200980c2c0c1e40e080c136141440b05030305034000c6034011034208000040c070303441d140310307040d00c145009070046c0c1c0b02c1e0340d5640d01652268048441107910130755420076a52425988128020402c482000514004446050140c0300c0d030038107200b460007a0320020307059501d000b6000380541122250b007490341415951640507541405410034041d085450030710083c050641c035070022809907000310820000e070345904c04100d44002030000040c1a40c192802c076000018401c0c1d10401207a4000d02d11001d02503402e003039060500354107462002945031a000c041c0400302510005819036000d1881c04001c1c08048012901d47c0a20021a20951040020030100c40f1405810500c060140c3c1c1104004c24902010408030441007607d0304c1e0f0103445000008900d55000cac40d40c0f01c21464010040300d0030381e51a100e04460b10400105204 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 709119055 1250 709117805 709117897
    0xd020a051c030f050f0105120105090c10050f19030b030316021e130c0f1803022110140a0204031707050a0b090d020c09010b0d0506010306180b0312 65
    0x5050f89010f813003118000c002104038100254505010801c0040040310041c8803a4904002d01010034800610fa43d4011401d0311500c0180240fa001503803940140c01c40c500d8a0440000c904080103d1400545462a4692030420041c3c16030304c10b02d82c0e28010514039100990110f03844c1ea0161034601060703221000314280c40b0f1403421052021030b03518214034100d001c1703203030b00d5004802505400980040e010b04035460054504d10304001040404c210910020340228181c001907102130b00c6452411101009903c21030703201114640795000144066581c00100f54503540210b041e138481d500807102160380103400c1c410520510100f90034260b101603001c440620a000700701c00010f100c40c881c06e12a40130b01d005030038884540304000e8108130000e0034652240b071245c030040c0002e400d01400c1d209044440314001989a6903000140c0050000307803c00c1c184119450000721009207603070082402d01109a01340c8404800c00d2820046078003400c4100320010418180441c40919640d50361039180b00014244 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 709120305 1250 709119055 709119071
    0xf040209040e010f0b0d050a030f020307140307021219062f0301030b0a0b2d0a15121803230d050a0b09040302190309080d050c0d020a051c03 62
    0x80c12034150182072001a5100c050640f9000741c107118070245c3c14803c2d50b05034400702199541d26150610b104004051107211112401034910070016a00450b0b802482c4403099a10000c140b540c0c8d40203008100c1c46503124008008003004045242520215554405a0700c114203941300c0001d00640710f240da060906031110001c0e107030341801058100c9292292415038a5041d07041181d01450010041c060207400c011031200680c45921800500440d1945040c0c0c041e5294110820b000d04400c2e802c40c4d004281d00c4011a949002d0410602804e42540b038180d1044038046103181626a02550801aa244201c0c0d2201081c0591101c040303581d842e170b000700d680e4075041038100006d1300300c04c450766502070703403901009002c2070385201e0000912000c803032018207440d155900950347d5800303190415000c0380c1200110b0070580030708419009031051100f50344000100790402882d5400a201c0310219102c0c45d500070304850300200300d540039260420701400c0e0034040310f48103024805044241504040c2d444e410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 709121555 1250 709120305 709120309
    0x1703070b010e2d0402010c020f040507030e0f281e060209010f0e09012702030a02030f010b0a141305030f060a0c181214150624090f040209 61
    0x1890203402c02100c00031242c107048000c3c06042c5000004440c00201c608180001030301e9491910707602550900c2d1040b244540da01c0401c1c0f41545030744420b81c1183c1040148480c1c80d805400103160501f00c01e003140c13200c0c581c1e2659950307070310700e101d0720a14800300c176a80c2d52011400c08540c6000c61406640e800803010a8140701c03403501c2c801824150350060b401b25102c9490f40e0311101113003012040c4c0c80c000341c03004058400203400c0070303040c800e00302e00d282c000d2080d900d111a194031400302d03109548003c40d101d260126544d4041d500440d001c0000215010001ca00e9001803400d6a102103210303900d40c44504040007800c2c0e025445008e1082c5006881040018165001c0115105100c24230010700070504140e0026019208510340306001d0122030b004181c1d01d4400e40b805001100c0300c0c00c1c072441d2168200d0408140000b8281c10038803103800789110392101242c01e500703000c3c020031041d0b07170044400c7c003503401e2000d540043c5218034074a803200704074081c86494020205641214000c10040c508505600 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 709122805 1250 709121555 709121573
    0x90d09120204092102070e0c0901180504060e0610030212040b04050114091b01030203190915020c030307090618050d03020c120f060903040e0606070c03120507061b020601170307 78
    0x11101c2d81e10300f0240e080c40c0c403245e818080a80208014080c8039600d05200c1203d0b00507002d04c405850421070b4410b40f8030700d10a10070b5042401000090003c10155440e25004180349200326501c60040c4284480480708911034821981030b8050b048808002e51503540d40d640b030504001c1d10996241d0b40364003070701002c410307006040c900600c040070040c1007041c6600024411992010095810315206100b0800e10180c0a504c1c403a401c4043c1000040c1c1c2c2c460340c03501c81019280c0d43d40c50008503101003a84030305040004000c5000d00b1484c1c0b84c56601300d654583c1140c581c4a1903101c0c10741c165084c0403c00a03418810600132a1511078015242d0b03031800840410380c120441e0305482e4040d400030f882c08001920134046076401103280380c05185020b0501d01642031100303001c1c100900a00c0c0000c1c5100c117101c0c034003414401540d4410359071a00030b000240b0003001900074030b00641d0990314007002c414140c210400c4840e09400c03260080e145a0303107848190300d00f01d50035070f00c00580c7c2d0004018034000100e07910 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 709124055 1250 709122805 709122833
    0x30206010626130308060d03050a050c0319020c0312041a0904020705011b0e0f3d09030b060d0b0105060309120721090602030f1c0f0f05090d0912020409 67
    0x243c0c01d000101d0316410001d04eaa40701401c0c90f4000d04040360540046503102d01180d90418132410819a5514200081490f500c1003440c1040220404144400029401b00d44515444421021a84d241d03040d805416240d00c5640301d21807544491340d100d042000e080e1000f401d22040014030040c140b01468032101e080d1040d014507840b00c01d91719400b1401c426008164180c002100740c0302d0044407890000403036264070710700e50175106151212074604a40130451803030303180080c0001c0380241c07402d409107405064a84240412240c21041c040011034604203112030b0080540c000c081100c5136481c1405000c990b03800982512441c0c0a9010f40d103d1030840c0703c0041104c0c40c4524080c00300c900c0300364101a5200c0c0071441500400443c041c040000c00d60010503164404401c0c143c4664030381d240c83c156207158584050811042d410a80701604441035640441d203610803000061240e556840030030707510b0b4a00b0031461004521011014022032000400e044100340c400b8000003141d52a50b00c59008110f010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 709125305 1250 709124055 709124071
    0x12180e2421060705090d084605190c17070b190902130509070f09050703060503240a0902030304121e020f220609060f05060403030206010626 62
    0x1556030108040300708501544140d403442c044d410040700c100000e0702044c0d030321400740c80300300d001c64004060120030300d1a003113940c85c0441810070200e0083d4580704000c1e41640a5506411022104c04024065011a6400100c5004c40d03010080807031000e58081d0281da00030340d20443e01400b00400b184104008140c180c0c01810182003528011594202d4580c24880d4100c0c01400c0481020068913488400d0b280035195800c042141d56880704c040d49404800d502079044c013091888006802443e40c0d000340e019000540c2c00b4044607480740d0034160344000118180a106c40a00c040780301021403c8076854001e00d07094000314126041d900000c2c61600a41c02c10f80041c40d801c5180303000c00081e000d1995600022a0001e0b81510301078001680ba6004820624001c0c0581c84140b003500300c04070312201482441c0302c0108140c580760404a0003c280038003481e024021020004205440c140c6d06680869515a000303081c0790782044c2c0c00301c1e180c4504440090b2282110707001108583d00c1a003120f8440e00788 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 709126555 1250 709125305 709125349
    0x916120209010506031008010c020309031204120f030e03010203070f0e0a06051b0a061d1005010302030c060703030213090515040e0c0d02060d140f060d0b0103060e0c0d12180e24 78
    0x108010581040ee03480c090f0041e144003000200089500c1c0c00c154001716070400d020318142a01c42c24103a5960604420987e0b155100004001620f0b40000028a000d419991002d4840e03004070103200340020903000b075001142c0e0034032140c00300b0203414510340c031003001c0c02041d140a08020342e03540095418a691000d8000329100507590b202c6010403065080d1840843c0501640d417640d004071340c5449090003018059040040c5036400e0500a8044400d1b52440c2001d0036a841e036a0f90a040042505a42003100840030707010480e032a14040c060315400301701d501d01900c8008030790820000c004d41c040d403040380c2001050041041440540c80740c40d451040c0c8040000d010301d010070244943c55002050760740303d20a2648100c0110b800c40c0281e50540e0350001002840905085d07505140092402d4040d6000e01100300c0e0000700070000790038504041d120344409004d248142c01102e14001c0c0360268041c0c80c050380001403108500340c01d0242c1e01c1c286501020a90701680c070007080e0007000e440719550b400e8203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 709127805 1250 709126555 709126567
    0x9030c0803120708040c060f091d0103020909010b0105090d050a0f140105061c0209060429132306180106081f1811090402030916120209010506031008010c0203 70
    0x14414407443d0700c60350702d02d0041c20a182c256641c40c2c0100840c02084104042181445007041c003e0038240c0c00b404849029000e0415400d0844407022403d0000b20701400c1c415020861042c01405006c4160105031100c1d410b00410900384101c89504a200b07540510803c81d55501050b102c94041003100c0c098442c41e0001c0542c0380ca51825114080c1c1018041c11880000560100e4008002c0c005158110b40300107944d11241c0c000b40c00f8107000d140910800300500038a0700504030300a09509089425a0b410b0070a0218000c2e14040f01d01c140e0300301d42c012040e2240143c24a0909400550020b802090700210114140210a2541013604040d0206040000b88840d400700e082c0590740c1d40407030b050220381700d1381090065003650400344201040c498544178a0702ca14000102520464074000c1e00840d02c070f02d00718868551740e0203540500d1004440c0e600300490b8180e03206000e0b840c81600038003513504070b0b40f03440c041c4071060307200810111103048103110106011500f8000d001c0d550030513600031901c0350 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 709129055 1250 709127805 709127827
    0x40309060f0503191d1212060f0604170f060a0b01171504021e030406091a041a060303091513060516030c02010c0506040b0f0f151009030c0803 63
    0x3a074440e210100388941802000718502c0d400800c40b58845566202040d245501c0140b9248916005461030040c010068010307902036070800602142c104103100041c0944456082c0070164070140645608503004000602c607400424540c840d040d0340120480d8070046d160500942030020a445441c502521945207007030340d40c1d01c44d0821860400f40d031210103c50410403900c3c0c003091400f0011a000d0342d0081050340100c4003044440501c82409175405a49250030714210009000c00b1008032000048405070300f50241c08030769854401c83d442070011880c0340024030780e5201313500c0050036164144010410780c1c9454807840361000703089510032055030729001c640d0640303000180702c0e03000704c0300b0480140048090701c1184070b0103456507905804c02c110340c10110300049942d44400c0070098410300c107000a1104001c0c200b44101d10078010341140170110b0b2030341011404d907000b0544060040c0c01001000001303034a070041e070700030000c505803c00401d10340d526655690456034650100742c180c0c0001c56071741444 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 709130305 1250 709129055 709129067
    0x150e0906010e07030c08160c05030304050f0607170a1e29040c080118061e090c05040501050a0311090a030b240604090c03060e090109140c06090d060f020304030906 72
    0x10b94101408000341c0901700405456000f82140300d0f035507428901000483c014a0304003001c0d074005003074903928501400c00e15525207201c41000140c0c441d0f40001542c0c20b10541c0b840884680340c40c8107010f01d4036600d003d03070041d100c2c05038403200c00702a064048100e10b040d40f0035182501c03400c45200c41c50717143c0c1030082d9001c0c155151039180110705003107040d041e49900c0032a00f8156400b5654031a100d40c4642c0c19007004011a40010042080303101c50500c45490304841039084a1806406201441e81c0c07200444141c09a41300e41800702da018403180030b0150281c0c001c480c121410407521405c0080010020342d401c00c8550050324079a5850080c440f405080c00c402000301705650704003011000c41c3c940491143d06c03603803207000d00071381e41c0e048000000c92180d00320070002d18481c240100542030000041e4000e1800c0d440031074503017022002c43c48242c0d0010480c00300c41d4600070152800c10111009000010f000040b0449100da904e45070030030142c480740302950140c4d009a40380300e121030034403102400d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 709131555 1250 709130305 709130311
    0xa030b030727020715060f08160e06061c05011d060301180b0a32240f06071703180f0303040821090115050105160204150e0906010e 58
    0x40320b0b90b0500740003491900d00c503510210306801c0030060390b0381c6070f6050180109000002080031075017407010005200d1010400e0f503040d05e0b401c00c00d40300d50b0800006a0441d03510036101e0143d8079484140050141d25043d00985aa01441c0c1e0059545640490744002201c400742c00c503030600e21b10610740a0900c81480c411a0b40880c096000300422440c008941d9004a81c05070000c0404c1c0e007101c0010340500003508002186180021001c0320040d04284002d0513400701c1080d500081c074440d0004594800820081c80030903078000c0079690064802c0c05000714280e03051b01c096040b44003084000001084184024104205454840d480e810000c04a0300c4606090f80aa4025403040080718008034010003100d070015800078030560380d0a0285111008030000b07641c00d200c500c1550f002c01c41c9140c010b410907560701c011001c100c41d000f9111130040d00d650040054981e03500005107050b500505284d80100c500c078003400c40d1040c2d03e0f980c9180410004000321180421030704030034010012002d41c440c0950f0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 709132805 1250 709131555 709131569
    0xe0313050a030503030114011704030c030e091b0f0c0f0d0e010906091e0302090702010b092409070e0306040f03140406270b0d050f0105010203070506010e0c0f0a030b0307 75
    0x41d00a142d038581555070f000601070040209801c846075645a0b0280c0c08480426074030144c030240e03c3c5082d00340601034140000081c1c006c035400400c552540c4c6000340c0100e2080c210240545c122144940800e020354000d2083ea07240b500b0300300704000180c041080b0036010031441c500100b5000d01c1c80100146000a5505410b040c043da007a001d10039550400d00760f2095480d014002034054100c00071542d0500555400070790007611603230500034002c1d81074000ca030044400f40d8140c0441c0c0c440c10000710190821340442d01c429100e00c168084140303000c11040d42c01c0483c42c03400da1042014035000034140300003900c08031041224548060300301038010b200c07082d042d00ca0f4640340f405e080c07030040060310304003106140c03241c1509a204001082c200517004031029100c2d2a241d9615440140c0c04040148000c1c1d80080031684a00c000003007640c400001c80b003040f0ba11501400e00c84c0d10b802d0820b854080090800091074800340001603c04456001410030001540e6000c02c607030a80c03505260a28881d41c01040f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 709134055 1250 709132805 709132819
    0xf1206030b0615121306020d060e0f010803031501120e1f050109050709090b190603153005150c0316020d050901140702040207081c0c230c010e031305 66
    0x8041900c1200300d291707022112a806180b00900c43c60000024803074034181c4c12606192000100c4c00c030320125a440d2081d0400703040080f40f81d0300e4900d0141ea0340822034242e0007582c0300101400903548100001702c01d180c40b58202148120844d060181401034420824508650100e442502107600b405040e0040c6006030040003a404c0600c001841ca050500034008916110400c0d025680c0740e038100d9615143c0010a03844c00262601401005072003070308901c0562000684001c202032802080b2800b04003034412480e031883d01d20000305c420040e1a40c0c0705070f41c140918081406c4208101e20680c0c0704440c00d541023a5030b490300500b00c1c58035100c07030100081154040c0c7c180d20a40e603000743c21508013140900700140034065120800c034151103001e000940250010a2110820040101401550300c1d0081028880305290b1020780c00ca0b545d080380c60001860201040b61b0b1054554980c140102c610042646003082d261035542c00d6030100900e0302d01c5c0e60310004000041d2000c8507402c0b8007800b0212104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 709135305 1250 709134055 709134067
    0xa0b0406032304030e220e1b03160314070b0a033606020f0405040608030a02060c0f03010e061f090305010621060506010c050a030c03020613020603070f1206030b0615 73
    0x200009140c004440c02200d143c03030f40309900b55950070440c503031b038035400800e0041c0300182030560344505a0700e00d44031840c40300d105040300320b1802144c0004009501260044150f155848248092680d501064011b005401000c10080025402410722a00700d0300e0105101c0007140c06204181e8488030740e1500400400d0502c01c5c11511004c80d61b0f00d0940140c400358031a060180030720078620590b40701940c4103250602c0041d2040f0088043c00b1086410b400b40d40c020b65500d8000c101078030030255103070095502000103014800c00403442d160000d50107080601c0d56020b15000e80c1c0b10307100d0346001c14081592002c1c2041008824004d81b0f000c1d1920108115032207402d0b40d044c0e0002d400e8910000c0c1095114030006a1507449021030b891900c8e08041111290415818058a0010707254801e40c014094103000625500040014541e11036014040c1791440d034800c00101c072a01e104210403810003802c40100382c46030480340980e070040c40c0074000341c82d45401c0100800c02551006010112507620901c50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 709136555 1250 709135305 709135307
    0x604021306030305031f0f06020601171c1803061d010e010209061b01090203120a110105011a0d090c0f0e0f06100f0212030f010e0a290a0b040603230403 67
    0xd4a802905401d00181017110424404500143c5034100c2002e9038400e0747c1c0000c3d65680024014101c9e40b11a288800c2c58021300b1282d42c0700c0700f00180c1d0700810a0720700d8800102900c40ca820b411044a0103240a924035120b64642c0b0540d1186046030001914004504a01400c284500d03061203044900841c40c0c040140041032050041200000c151400d0b04400440390b0800e412a80d0340550003020307105813169440448800b500050780000025400d0103954021480c14800c1a05880c4000c901010702411000780c00043d80c0254032140c40b1b2510b0340a8440054103400c1301401802d802008c444c1041d003417005244c0190b00081104004102c0d200501101e80c88184090007549c0091400a40b50004201c080c0d00d030513084d000c1d048018400004002c0544143e003127082c181c8598080b50360310394958000c210300382c1b03074032102441075144a0320b030f10300000c407900c89102c612800180c080000d4503650300003843c50750410360185000c640c55018400726021100807884500011000c2c1a42d9400d090328 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 709137805 1250 709136555 709136557
    0xc230318030c1219020d06060e0915010e0c031e0a020405120703020604141c03030f060b0306012705030a080723120a0c0209131103070e13020616050604021306030305 73
    0x910318038900c000c1341d05544402c0c840041c035a8010b0b00501c11287d4400b900301c40c0c42d80840b0b590000e170040d030748012010b5403c0c1d545070303040712810b00706510113441c0c0000001803580061b010b214001e003550701c0180c2d2a07541c40400c6114980303075500161624900001e00145c941804181040c540010a0501c0182c2d50a0705a500f80d840400344007140d421f0601c0811044c80f11090483c0188905081e85410190302d60005102c5404085d01449866038603c1917600701e01054450a0125103c1850003d916800080c41c0709201100c581d00e00207a030b51800441e040017030041e025600003c0029001c81030042030006080303036003114446404400c15a00209413545000700502065490000d00300640c00d02ca07000350071a040c3c0092080c6600c2c1002c6080501078000700f182110300ca20070303108100b1107103004a01407085403181c50049000d542d03466801402e0160051040740c1c07000d0b0a00c5a00c41d0b084040280c10304051280000f4446400c050042000401d81c0070388007290241402c0702800080d034040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 709139055 1250 709137805 709137823
    0x1060b0c07140303091801050f01080103050619110c0f0111070206040308030a02042402010c0219020f0d0b0426070f03081905070f140a0c230318030c12 67
    0x152070b220070b1007031280000e041d0302c60001c507154090040141d42e2400d200b05507206040710000c0316a402c2c0500b5501c01502d14140920018205412800005102006112101c20344241c4102c0010754200042d2586140350080041c3d559207501c2030051010040c030034484d5a5442000707030a002d09101007030f0300150fa47e02c214040203081090100105000311841e4061b00e000c0c02e0041280c46840021040b02c20355440959110b60056003041e4010400900109040d03460300f220385520702140341e031b039024080e80d407142101482e00002503c0d5800042681000c200b402603110b00c282400320400070941c140030311402d41c503004050360100403140028270103550224904e9407500700800e1070350f071345c1440c6680d5140300c5e04d401c8119810309041200e403c0c1c0c80b81c04003a6a8a4907119005100900140f011082c002d0050203400b0591105011003ca442c0d00c15510303184891080c21010200111880381c1140c01c01c0f0b80d00c1c0704440d034003c440d43e4503160601c80401420001e03200d070020f41030450442a5100208 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 709140305 1250 709139055 709139069
    0x61d0909030f210c0d1503031209020112020c1518070312020f100209030d210234142a0307120506010306050c07110603070e03010507090801060b0c07 66
    0x5419140d80f4162840c034081900401100500e61410321030b803504c598042940f00c1e070700620b40790001d44849500e0107440c00f6a174041e950514103500210581d0300070003008006034180800a1036030448010340340020010074981c80007800743e11401000d00c0002203400341c0340c0c220158140d0017001070000300140500840b40c000801c0102c00000890590810264500300c032050b010382c400461030b0410310b030003c203030b0000e094040350036002440c1c0301283d0940d082c1e4034145190f02c04a4280341e000ca42030f0007901c12404000203561080843d403180d001c42007210105800ea409410f55950248019090426059604013004d000307050061464100b1091030400b400005403090000c9400781c0d101002510003500001520040207143c80c01d1065666000b40f208942c402d05080004200d01e000c54182e803031403940204445400707940c0c08100f1500c0d8100400e404204141c040756001c156509000780c501903451915200d4206040203000c40c25034445401c811000802080440102400003841c281100ca40c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 709141555 1250 709140305 709140307
    0x6150a030b011707020105040c05150904020711120105041a0601020a0308180a06060f080c0a030807061806200c070b03181e01060501090b040b070f0606061d0909030f 73
    0x600005031684808016007030f0b02110030208010a8a8056000078007850180009094042e62203040003240c1c810701d401d694420b10244a0401b031402c0503009854040c0c4201d1a458030f50340018041829100c00e0001052581e4544d030610040c000092516180407114101e11130710303881c101002035036500c0c002d0340080c03c2201107800100c189500401d01081c0564410940340580d5160404001600c1d4602641001c203c7c400000201c143c400aa01e01c044040540040104d034a5900c5981c82504a5402030722450740310800501c240000080114466100301d1000803d03c8181840e0004003c0000404450501c00c00c09612001e80005045080b1040b10402c140d0366a240780391440686110720100d81c6a104041c0e40080031042078000c1401c0c1c0b48032400030401282c3d03950045404641505c41d41d0314013002000b080c0041c44141c0002e180842c00307143c45242404081d41c13010110740095200000050b0000c411003201c03428160390f45402e05013201c29840b5810719854581c2c480c0302c0c82d895a001c2c2c01c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 709142805 1250 709141555 709141571
    0x601050405060d11031006170403170a0209030709020333100212030703060303021903050a030f021b0601061403040b0a023609071107140d08160b06150a03 68
    0x1009030041a141c01884c1c1c81540c60781040186906580300d94024030340858096102020541c013203100c1e940c46070390140d032031803151150307000003003607484025250381c0b15079400b00107000300d07a141000000300a082c2e079040140e80786002c06031401700603404200154021516010701150620140a1807102041140c0c1045070001004c8241e00d40301c0b59000032014500c0100400090640541c08881142d010b03400780c2d0350030200c42c803601da40a103104c030700140490014012442d407a48603901218128010040041c80c104d0200c1558030320008c140038441072640701d200107100c140d44c0318620314440c01400034210305500b0319a440e2418054020300d400c81807039000c525009428040e10b042d0107400b00c1c03004600e4808a0b10b2010355100440e00c140103020700c1d080c5000ca51041d11550862060040000140c81d10508203007450005800f50418a58402191319440f0b0110310041d00a02d2251180c41d000b048080480c035142c41ca080c0000c4c0182c0c810103040c000c0c1021080c05d0402c44207550818940010190 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 709144055 1250 709142805 709142827
    0x304090c1e0f17010e0403092c10120507051c0206030112080f030a024501021c1805010212121b0a02100b030613080c190c03060c0305060105040506 65
    0x4400c00f0a01880324403188000030318000c1c0000d115020314040e6451028180d20703840a808076900080003582800690400780e60492042030507660000074440d08121417550701d40f51321000e0b09010780e00b82c402c1e03086400700304224075001d07500310100800c43d080700c01807801b01e80001c0d4240c001481002d640150408003001086028000c69414904c1410b0003616800c0c242400310094000001850b1640c0d04070242c41c400c0181400754004142c0ea2803100c08d01e64000701e8a4100301c5002c418501c0c1540300c1d4940361103034031041211800c201c0329203546089103c0d07400c20070003c0307015050344618159001255005010380154080700c440c07404120140b00d440c3c0781c1003034036400912104200c1910402c0814000340344c90b0b01280c02c808000c900b96052000d1170f511800c050b118041610342d031085a645a26010009130720502520701c0380c05440668907400d0f000c013104414010500c1d07086070712000f0030400780300300f03c50741c864200c1418551078108902c1c502200040c010780718074080e0b24481c6101203180724940c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 709145305 1250 709144055 709144067
    0x19080d150e0702060604140c16060219081308090607030212070c1e060206160207030c170f01060b03040f0203011b03021b0a05030f130e01080304090c1e0f 68
    0x410480c0c041049100d80d03416460354941000e80d0140e0060003500085a000d03e042e00840301c1c00c03200500d820403aa100c840c0300c02125442005840ca0003000090040003285c1d5900c040e007621101100d000070032000049000340383c02001440039404c00c180070f259002150318141514915402a81d0466507070030765060580c40d0107422000005404800a203840c10005240c0000d800c80e10124001c1c1140c1c00f03070300d01280c0d10314010300514005038807200c00a4808882038400710010045030054454440c0c0300d40f103c51004542d5002004220b10815007505550700401030341e48409100b000801c071807410b010005070f1900c406003014040d402c0c420607a0056650230340c0403911451400c41da00603610070342540a00a03401ca100105011080210404102c0e0800725940c0004e55024002e0342c5401405d242d280019007100480300c003504040800820010a000c3e0b041e4064191200107507141c40c0340c914120241c50a1a10032020020030ba404c940b00000000070140164045080000064650100440720 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 709146555 1250 709145305 709145321
    0x120f16020a170c1f0e040209010309050102070b0115052b0e16080106061b0803090a021e19060c06091103010207030909050105090705030a0b03031905031819080d 71
    0x3540061005102d00340300e00140d200d50001c02541c0340c0616150622035054954103c0385101c001c2102c000200c406441c00ea03000b1700d503203d0305060014001d5102c1e100d403030072038018000445141d590b00006109541c54070110790311404043c58083d1414041030102c1c04004103500c00100da00000356816040e101a64100b180000d115008403100200c0850080e881c0c00c0702841003007425482c180c0b0108286104903107403080d901e6890551900701405580d41c0f01241d02c0109003244900408001e140140d1703a006008802c61035040c1e4104401002c94100101c0841c1c0d45a2010000cad0400030400009400000920351740e0742041001440300b07030074102540c103200e0f154103041d41948000340c1c0a042540044020301544d459001c00c108903038031036051144a050907101d00004c00c505000182990f4000c1d04480101540a4113481c10002c1c106d00d011042d0a00000d41800700b00c011081080540c22150340c580100ca4443c01000705015100d40d140e00c80002c1e0501a00041c000229101e500d1829001022 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 709147805 1250 709146555 709146569
    0x303100e040c0902160b09061905090706050c030403080a02031809010518060f0a0f1815030f0c1d091507050d0f060305030d060314030306030c1e040509070602120f16020a 75
    0x546481c000310810340350340b4115009c80c150300e0a140700c903800107018030600d0b00c288841e9008040a038144030303040d9115040f145001c0c0451008100201c0000c0403140a04034010041d001191903c1c05d100070503600741c81940f02580a58060710040049540310020290203070750f698441c2d0029180c000202e21416503079050507412491407100001c0c4003024422030000c9880c1d01003c01d0103032514244040a442e24843d20742c400e4a00d5410500202e8102c03000301421a1003004283e0400d69181c204803401a1b11420b40007190100300104920160f0034010160141c040108080e00b074942a0b10140c01030142d070401c0e0400c150358400703800600e4107952054014540107001c403038440d82540103d0000d0300b0b19000c01c460742c0e40811402841a02c0c004107903030250000802814002415034144984007000d48100d64100071401500800390301c0d02d10843d4000c000301d9020f40041400e1030303030191405041d00007042111030100f09002c1e012441200b6940c0c0c0c1412141c8c051642e55071400058200211500310031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 709149055 1250 709147805 709147823
    0x3f080c0c01090302061609050a031103031e0307140903211e0c0d0f0503010501032c010608070b091c050304051327050a030f0210020c0303100e040c090216 68
    0x70b82070640014180d0720442e1980383c01d00c949048200d00f10f4a95070644205900840240c60a20001d5452242d40c10103000c0a0100c0741800542d000982800c42c09006403070a101001040c0103504d81d0260280b07032502c1e03101450300c2ca041405800700303a5a0300c0d92000032408000071441c081c03101e0041000c03103080e00c030005031034100020b00c4503003c25a03a100d1404141ea910950b6006008280030b059001c40010854548a04581c0381a00560180184802c038100c0e114280050f0100d00301481507003031452101c1000001c0b0142040d4625103809080e42180c031001c0018001b00150b50344030440c1d04010003680301c00b0000070000349442e0b85503001e1900182d60100e0340b1450b402ea5425280d005c0d0f0b00c007031600306140b0000083c0c8045102041a0804081d1150b0407185940c40880d0040c2030060404d0014411900c003c0c0070001c02c0d40890b0411500c001880d00000b003030050710446041400c025240300f880040300340c282030780c0b550700008240c41101007682d001700e4070f9103200e080e08001c01180d0703800c206a8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 709150305 1250 709149055 709149071
    0x26071802040504050105120d0c0c031a041511070219080d052502011202090a0e1f301b0e01240807030b1201093f080c0c01 54
    0x400040d401c240103842c00355142c80c00028440c03500e10180c81030a4413240260444459049040f10141c041d0030003500c11140c05000040002c00c05100b0741b4031814042401c01d42803c00785080107180f050b11601c3c3c070701181080115003480702143c08507085298103c8888001d6039a812880b0504803140d4004905406006507031110303607400c4401081003c41e299a10342e03400ca074010b5107060f421840f0301c0c003a0001d91641d100094019241d4000c1c500100c004004c3c0c0192603035039001100c0640126a100aa40c0307918411b800d00f906000350500c050f002c070340245a070300c1c68200000341e01102d409070801d81c0118050100030a12680001c030641ca0a10030110303c40140d11040c03a0300d207802003803190000f403c5000c550100c1c040b2f00703880c0014a01450b99034061503511075403000c81c00362015201c030310f500000c01742c444d0b0483d90f024880c5c40c8c22a48208070340c1d402028495054040e20f0f00c4d040c240d4401c24050203895050086529040c00c3c5000c0904009201d620340d80c114642900508411a05c603620302041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 709151555 1250 709150305 709150349
    0x302070e0108010c02150103030e04021813020903071d070f17040503090a05030a02180c221401080c0301090f1b020a050106050604050f0d0503091c020a0605042607 72
    0xc0522480f40c1c00b282c006c01031094040071010706c24840a0002204401c1205103444c2c250008c0c406189001c048070012071005000400c02880144d441280030303030000d5018143e06051054800404564652054000b01e100c09100c0c1c0c2003001304550104070429030010450350080000404d00034014041d5941445c042c070300507581e5840300c0f807250b105441022002a84c0d180018900071031300e038090801c0c03000d4862040e1400c20454080c1004290002c02d0000000580f00300300201298081041840b0b6807924100c1e4840003140156a00c1c1d0402c0300900402400c00282c5044904450081074002103000c40d2030040c1c801400050721401c640c102c135410640768141d00091043d0341a0048008110782951801042994499031040d107030405840b9200c40d44924168103c094003900403c20341e0701e0300440c070740058100c1c42403c4100c401c4a099075441400d500341f0580940190480e030a009150500304003c0b14040c884011031000780010102c08080342d2002402201d00821200c59222005190104c4e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 709152805 1250 709151555 709151561
    0x3050303010302010216180b011e030203041406040f08030a0b0a030308040b07021c03050a023a1a0915040e010b0415030308040b0a0908040303050406031a03060606070302070e010801 80
    0x200607030044c814006c3d690308404c24441a030701201d51145105810401404082c00540004080c607414441451581c00d4509020381480d0099505c0f950700580d42e10786454400340d1482454681c0b00c1aa00030401c000000b285058200300e4560414803158995036100000c2c1d02620011a056410030b00c2501e00004141d008070005015900c5210300f86a180da0b01442203907585d0003091400c10300c603100400801c9242c001d500954110234101c9002d8a40700405c004600d000c00d582c51000d064544042c45581c0c6000f600e80c440c200c0303900400d4207020380e44008404030004685610322030302c19202032010400c888101110103c8188001c0c10030702c210320002c500c0a00902101d201103014500b40107101c2c4446225591340c0c42a81da0588540d411a00d031034440411902005001c486c031281d641284002044d10740c4040d10044d80b0903607486503102e042c1100107082d113016105801c82d900030314048030050f980104105620035000c0c3c405070b444585d64241286000500c1c0d0211249408140000c08d80c3d01d0190 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 709154055 1250 709152805 709152809
    0x6180109081c1d10090303110712090e130b090c1e031504020d03030b0a08030d1a0904050c01120b04090f0b01062a02060909190e0a0c0314160305030301 67
    0x108100511185110038042040d0900c0d005101504020a295198a803c2c3d1126002038040c7c9000135030603400000c0181164440314081e681da4803d10426042c403a030041e6058043c0003240004030007410b0680f25588410b0841070f0043c01c0714900000103000140c1048024480040103004900c1855286180c03070300840383c00c0f0024041d00130864070b900c0711480884485c0c010760f4094071910311100151401c6004201441005500000c1e1000000e0308603820009005031501020780016070348030010584215041c0001c2c80c40c000d07104107040001003080401c48000100d401e080190030015034100c080c0c014404800100d40c07140c640392110781031203840c4400102c0144200f100b0410359813070f2042038540040001e4003200c1200c401d41c0081c04c0c0c1d801115459000c80c8040e0640b4101105600001c00c040811940040010000008421245024010200706c3d00540000c2c290b000d00684a00309070b0b400c90300018001c05407135006118041e508001202d051090b5003003c001403602c914255880364028 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 709155305 1250 709154055 709154107
    0x1103101d1303121a092a07030216030305030f01050a05011d0a05060403200303030903030a111204031106070e011d0a0803040b1c0c082a0a030903021c020618010908 72
    0x174000101d8003021000c01280924114949000040c2e044036483c0e0b899004610840850150300c0c10210380880c4040702e03130007543c400e85841d5200d1400c00c2510808581c142e010921407240c94008009a9070000c1c8500311801c1001400d01c1005000740101c0c60051045c2d01c0641c0000c400a000024020001c000305203c0607440c00c20900c60b00039000301680d070f00094a1b0f85040e070b001000800c050480d0303079000f031075400c0603c03111070b0820081c0c003401c0709104021502500494103c281e82d0b40c003000240800d86c1e2100c560b08060030000e808600080c07101c03803541b2141c49641c160020b904a1540e0321110400103000041c1243c0e900c685440c5010860341107240f40c0b02c044901201440ca480410340034407503080000c0e98801030380350f841e1411220b00d29031413820180a640422401c0c040c0f04070100040c440710051751008191010070b071030028503103d0414a0021501d0b034265642030501d501251258003c0d022802541c0301101d021460350040260707420040a0010019a0542194036101c032040180c0c14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 709156555 1250 709155305 709155319
    0x1c030e010b0306040c0e0711010f090201020f0604080a05130f03120210090206032e03050601150201091203050c040f0609180e121605011103101d1303121a 68
    0x410701c10700d6030340c00c41918000c007604680e0405129440e202000103501803003d16000754150050280c0a0842d0103444142c00001c0e19400b120040d9601048007a1044420303d000700074525040d241d04046005034600302e01080000607150001010500000016101e50900a00b80b03590f240782c00c2940075801001600036019216082d28030112a01c01c050100380c020744000d00e1980c403242c14160345d400441284404180c0440c4042d42002502d600401441c4904003c1000354101241000306084008400085a05282d40f034000203150900c03241c400b101c5810040303180e85804202804601a60700003142c4603920300c100103001644000090300711892440020000e590f598103040942d0045a401e6006902c10003a40c0400600d144c020000316400591881610059039640c600f5200d2014501c01e082c1004001d01440315403018a00c030040008101c801c1c80d10b04100c460744041000185a0003403104002016002d1600500340c0000c54800c0a2003040309481783d04860fa00141c02c00882802005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 709157805 1250 709156555 709156571
    0x241f030b090103110108040303062309090f030415090b071a060f0108130813060206011401020a0f0b07090b0d0905070f0503030405120721050606010905090c07051c030e01 75
    0x2030070040c0c9816644c01c04001a40e0b280700c0300c0103440b40351000c0c1040b0201542c1d8200010719a000c2c24202c2044240340700401000c806c81d608101a0460103004502c26802c0b0744841403c402d80003045408403108404034240d19441003078180c2d06807001e64014072030a000003a2480030860000c40b60303080901041b0700ac90564032803500b4406440c0e1030714030140c0864011000b00c2c000449018020386900c2c03150201c10f142c50740c1c1030004092104142c0c0680c0142e4000720062010340703000406807404500c00e100801e0290510707200c04c1d04403114013102070202130079440441c00c100c1c410076082014100020b142030b03840c05030040c03000c010640c2d0740080e03529009500012410309420302c0084101c1d803008005609190030282001944020082e0140341841404030028241038510244249e0710103c00c900c3d8644510b904120f81040d01c02000f403410040c60703c0301840a681d820600c83e0b0052040006240c48150a1900924141d0042c105805030070200003507044081c0e0503004140412030100088c05400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 709159055 1250 709157805 709157809
    0x30114040605160914040e0d030618020702060a050a0210091a0f101412011104031a060109060c050a0605041b0e01180213031e02090c0c06241f030b 65
    0x40700106503000050111001082001c0c40c5e1035107010440401000014011740c0c2010551402e49043e02413004a5220304041084444564131003403031200d50301c000e6203000c0c295030014016100300b070642014404003003070592030790340b00304464000000024810000780c01d440c2451104040c50b002842490400c07440080c0b070800320400b015026101c294071103501182030000088416607503050050b0414207810041e01110801d0090030101c100da00203095440d81107040080100183d801380401d481038900c14815542da00032142022a01c007460801d2200445180487c2400007020740131b005241090280001c0c131403016030894000d4a40070505100a0743c40781e84000c004000d210f1030103510b00408490a034080140c004215054401880e204116269503c00141202d0128204603c0c030081103d0000c5040540c4255004060390401c10b04182800303400e10f541d494000c10700d800741808280c6009441030411403111407100001c14280e01650058149071040e0f40c07594881d00045e007014243d08841c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 709160305 1250 709159055 709159081
    0x7020f0d0c0303111006031a1e06010f030e0f010501211115190c06110301140f0301020f18190501300204080123011d0603010b030114040605 62
    0x6640e00090030007045140d601c0a90348100812030f000407902400380d82289641003031240c0c0740914402c8007050b91281411070841c4a03080001d00306030071410059100c1c80091400400294004002d1034180401c85107218114050401c50213028490310810030142800803042d081941640c090003944c184940d0100700410034041e0b16600036100510050180d007050904200d43c1ca1294804a036003850243c50311a5510f90f101100c41000c0040c4004400004018850042541d0301034810a1242994182968940501c031000300e030f18414081c003124405980c13030a4059482501c501902c2c10340b580046044941400e420000d40d80c0306021f80044e100681e50001ca050090b58010707503a1881400c2140368170604110000000c200d040c5011175600ca01040e01e00080000e8462031002185015600800d1840341395012440015030710f00c4801841046d2059040240703003035552649105c3d90700c40c0c80200340100480104c4076015400c0102440311420f41c980d02e1401940f10b03610030070841d82c501d1500005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 709161555 1250 709160305 709160329
    0xf0421020f01030209100c0f0203060f07080903030c0a0c060b04020a030c110105040809190503070308040e33060403020901032103020a08130618031d030102130506070302120301090207020f 83
    0x40304801e000305850061154501f2820a441416100e0150325240c00003441d0010440d414010882c1140410405941c0300b0302d13250f0042d0117030000b1400d40c10100d0542c105405801e8070b29040100d0b07a0515001d2111a401400c40180054411076483d181203000401800d400f03c07240b07000c41c0481d441184000e41c140329161040d5000b10849080c44450820030005580c460b80c180d41c1030000d840c001c900c90350248580b400452049601540e40c0f0300d0a06507e005040040101c1e01514045506503018188202c42105044169071481c8025050000190260040350030213500a5103550000c0100311042c8221040b88030f91800480807120101021000c1e803043c2c1c071050300010040e50116001e8103080700400b02c081e10413100030802da1a0f40d444050390741c2021314158001040b059070b848452000441c5e0060301a0143c00075032908030f05000e40140b03036036903100e1103001c6e603030009500d801d152003400342140ca80c60088a4640e00d59440310121701075088014141d102c0d0030f0810b8040454501031544101b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 709162805 1250 709161555 709161559
    0x501150c0c0b070c030602030c03041a13080f040806010f06020f072d0803070b150103090201020c0d060e070f0609060518120712030926060c0f0421020f01030209 71
    0x1a03840c14010384041d10f4010201c100d03450b6a6540c40440024160f0024612450b4172080458681c40d041c1054011421060035044081700e4600502052400410142c003c330354005c2000c582c0c4407031b501114038841c403956002c040c150041d4800800e111003400550300c1152416401ca0701042030310b28a0300d0700d070782c0300e48507139804082c0b15050a401c84109014002c11104c40c141a107a01c141d80d4032440381103900804003182e46030740420030030200410307000441c0109070003840c080003480e11540c0040d5582091030803070362080004000e214100a929000f40d4540403024090b9500c043c0d4a00c1d105003c84901d01450011510100780401e82c82d01c910152119110246a1001e0503800b000c01d11550488940340d1410901800801186804141101d00c441d140300350340740310364189484035101c54000a02001940080d0905801c008a030b03000503115004038200310340c5d940d01d06646507a813845201d103500074028030100d000000110b50881640643c0a8026101001c1e030000c03080c0110202c2c4181455a6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 709164055 1250 709162805 709162823
    0x3030a020d0804051005010603020901090e1909061803020609070b030c030402102304050414070503240d0b0f06030109030914060403150902100309120318150501150c 73
    0x31030035070701c900042c070f400c103003e0010744800b83c070b58910341403c0c1c0d20b00344c014502080d0005803021055174810380e800d0091541c08544695030034400003803000d1800389032550181c951500d000209004c65039005a0503010020300354040002c0300d14010351940d50032100c0800d24091014001500500d540460744141c1030300c42a5840c40d0354603801c00144081708440d41c010002410044240e0105016400406450000402da03c4e985444104402c3c1e99080d82c904100844000900c04c1460b0042d0581e500800380d42100f00c0ea80b00d564802000103036038103c203907912031281001fa4080c4804560200d001d66400c00d00041c0607500e1009240c00d0311079100b00100050b10400c420000750b440c204504111107002407084d441e0a649490b82d01e200f030280c02030750100990f40d0034002c04501c0d004840d0011050326080600c071409458440e5140c641c1c00301000c4040c503031640c0003100c1d0542c034406400102c1c3d170b0100b00e0328060108400c501005200c00d001b080b8800c600720303d0340314806000b92078a48507198405046 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 709165305 1250 709164055 709164073
    0xe0c0a0c030f18080105060a0b07050309012003160605090c0d0b09030412050304060905190b0a030b03010e2a130c0504050a0e1e0405061b0d2903030a02 67
    0xc4a4001401d038401c03082100c5105003076201030035454450f004088000005c105410801c0421402840075889842d04200401c1518001030001c82a40c082c0d07802420404480e00c2d801c0354840303200d1051141c000241c000000c4601c1100361110261221030700903901040b455961007969607a41c0e0949070000da014009558100001d418880ba01da400020803090b00c3c241030392001c1c0c05000c06100300b8105e655800c0402d06101072503001c4010002090126440b9607440c030844800001c4808d1405250042d01d400500c0080d264080d8200c9010900301a00030080b5038010800c00d41c403404040c5c440c1e03c03601c030214030440750442c161080406140000703001000d2280b80240f008001c2665500c440f043c030074140030000b0306030f480423a204010b02c2101e98100e5185031070b01300241c0000100e03825241c0c00c5e03405d60038000465400540d8540c040c0c00e244110319040081ca440d00800e004400c1242c203190704000c0c0508481b003103064082d50301c01c0540c400d8500c05907418100741e1240030301c017112401a031120680d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 709166555 1250 709165305 709165307
    0x6080a1a032104150503010815010f0603180b070804050c010905060d050a0e030f041e0605071104090602040b0a020601050904020108061c060507030203070f020a02092a070506010e0c0a0c03 83
    0x4041d510302d03207840c10769160035a81c5505a00b90181d500400d404240e000c001006009030074405c000c002d203078015101100b0b40c10980f0300c0020326514000c41c801c05a07544c1141844244403c000c602c10794000d00b07284075501e0074410043c506401102c0481c1e5902071507400c00f0303065000740c05070416110001e203101d0400c0c1214542030000c21004040c2045952a482c3d98034030450184018481001e244d070103140d0340c0d4100000c0310300782281403141401b210b10307010080007850340c000305a03003845074040405c900b0218483e001402070001c243e4090400351000400181d8009400b0060200c00540d4003a120240e81e10410005039440884020f070100d91100001202854442c14417588070540a881c04d518030034540f00c2d43c1c2116421075507000860ba00000340301f1229004840c108110b9828401401e80c00e405a000c0707138044102428107180d94841403401c0304410550700911200b40300686602d42c0382e030914101070340c1d0740782d0a00c940c031504e113005000700301c5584070f40d0111120001e9540b42c0c0e102401850350 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 709167805 1250 709166555 709166593
    0x228050402070501140f0403080108120708030a0e070609060f390605070903020a120c031214300c07021c0506090d0807031a15040e0106080a1a03 64
    0x8002c6843d556110714001e0040030314a2050701621012001d541240341503d4054114901030300f0803186580f0100c40720758902112411103081c00d50213a403e86c1c51751101c440c6600071b032a240200309458042cad050041103079503000001340c3c1200c010340d850302c0d015000386205480e524404800d207207403d002c0c20298078100d4900f840c062007a07024210fa00c000e80c04280c80f0b80044074421348074000000c0c0e10300410001d61500000210182540343c0d040340d074404c0c0c0d88da121a8410340c1d034403008106030b4882c1a441140745c01307045d2074802c202c2c03441400c0d951a00c92084140f09040420707000840c1e4680380707206078891b0800c002c00d1482464040c0d400c500e02806034003000700000c04100c883c240c2d50070030a034550000708244022405050030070f0041c440f919600380c02a01030900248480300701440d0041c08803858600103803080c0e07030f14410f03625411081502d50322510f0901c150f070000d40c410350000000158070b41e0312003152807050601203820804100b4280343c0c201016941c03007909074160701c03d04904001001300a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 709169055 1250 709167805 709167817
    0x6140a0506160f030908011a060304121808031306020715110705120a06050a1a010804020303070501020703020d02070b160b060a030b091f150314150109090228050402 73
    0x125002c4000302c2e5a034200400741800030032800940102003c001d940f009002c2c0580c405015402c0100c54091080840c030b59001c01440546a00742c0c020341140c100740945151030700c1010b48aa0703003500319200d401c02c1d6a07a51042c0604100c041031008009503491000c1903503015641e00826141075691010780840c0d10f1011140c00c0c03040d40c0030341000000c02e50b0310b04500e84806e104160280c1090301c0c1609002003140d00c01009062194105481c0980701c07050488100c84910090800d490340f900c45002182c40d40c00b07800e500600541c0b000403050185500001c52000b0114250700301d80d481901d8400e8601140100400098103424244d0f81000040c0503ca001d03511200260001c090603969849000e01c4000c02d813070202458129101a8241ca203200d050210400d00c0310400b4090808210354660744511503200c050800301d10510003c180807000d0102c0d41000468480f116103035610343d0310102c0108070b110002c0380701b03140b08101060325443c0002003404003155075000102440c5442e041c04041d40c400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 709170305 1250 709169055 709169077
    0x320d02060c0c010b130c030b04060e191808190c05030d0f0e0d0302090a05010302090d0b06010c1505180105040c061b02030609010209040b0319060c0905090f060406140a0506 76
    0x182c031543c1c0082c0c64580c2c202c01c20701740703000700890000c68a5901800b00c0e41488100c900642c00c0c00028490720300c680300130541080c08000341602000245180388000c00142d0102070308001c00d4001b001c144203050000d07101010000c12542c40d0110715100964500c20340074030003060364000707005840384400181e001d4514028100b0300402c00c04041c5031100d0034040a0300580c00400c0c0e0105510140b41482005400a44401e00b01180703000c45090000f0710b0300c0450307400185205500170014540f81d20924028901c190701416102114003c0c3c241c2c240a0a000c40b01c1c500d5801005a480e610007105000d9113010b13a40042c280000e460400340c040320034182032090581c268421030540c10060303c0c10003100f840350440100058503100510f0800050b00c8840748043e11a50001b100e201102c1014524120070540c041c0300081c48940510050310818216400143d018500c541084040c407000c0302040e01c212411035080207800d032a07101080d100310343e0024281c0c0008105405115504159000344400804 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 709171555 1250 709170305 709170311
    0xb04060b1002030412151b0c0308060d030c0f060222060f030504081902030f0f04080601050303212d06010233060d0519170711010c0f320d02060c0c01 66
    0x140500d41f04003400881075850010325800f80380814036502c142125048402225030000c1070981d610000c000070147d01000e00109040c0514808000e899030445001c45410707550a280d1980180e010b18044201c0d10400020404801d20002480e11910039284556440119582056004411030100401e10400b40d403e61204106050074207941030040c10049211492059071181481466428840107074400c0b4002d81c020f01800444080006142040300b40c05600d100c041e6482c54214010f4842c0f000302c44000c0c400180c000103075078170f1110703c50340b00340801e808031001e0b08520107403500c05503105407072500300d500c0c800c00060340b1200b0306811a4006a005000e907182c4103041d220281028400c46000d40510783c0030280108211440650450480101d030381507090510a446902c201400c0c0d0f5081070401080900721402c00c14511800e0096940048820f1001581c0c1500052020711092440846800f141c61668141c180001d08024600c031950180400c2e45039075503a904a60450000444a952 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 709172661 1106 709171555 709171571
    0x7020f0d030203041503090f0f020306250c020d1a01030201080109050108030405040b06070c1e0b0304080d0506010522030b0a180314070b04060b100203041215 70
    0x504404102c0d50b4818002c0c5c100c004141860700200720a510352580c03020b02c918840007120980c801c0e03080b07a203075403110742c0b100c064032942001c0129030749824040241e0f0a4400c03003500340e82c140301510036100d6420690b541c0038691107500c00c400300085814010002e41da441013125006002005040080c0c0d4100070310940c9900c40c81c007505000b103484030000c1e0305a845480403101c01d15000340c0c0740007038a40c0392040c0034803050030300c100541404540702c00860520060f004680c099540b01c003115180c03242900c1604090f00c4000c0c00f481c14003400340840c030814580400100c844600341140c050080c1d00f58500a8101c410140c01c0301030310b600d4450200000300e5400ea00381029a01400c003503600c800520703141c804034800c0d01c0e00105902d6100c801e0000704881070b0803a8003081d10456959a0780d070b50050301207a0700d000e984907018108a0b10840034020800d94405200b0106c000b40012032019 = true := by decide +kernel

theorem cover : BRFrame.Cov 708992805 709172661 := by
  have h0 := BRFrame.cov_init 708992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 708992805 ≤ n) (h2 : n < 709172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
