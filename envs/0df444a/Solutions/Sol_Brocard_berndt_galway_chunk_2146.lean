-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2146
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:47:21.787855+00:00
-- url     : https://prove2.me/submissions/73184bc3-208c-4b5c-8bb3-0c557f091086

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 385791366 ≤ n < 385971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 385792616 1250 385791366 385791377
    0x30103021c0b07030b031047060a0903061505030613050604080a030e06040f050706080103050d03050405031c0f05130201080411030c06030106050a0f02030a09120204020f040e01091407 81
    0x2d0086100340c109441d9108000c080320001d247e070011410841d018050244070000f15950305031880b00018900c07040300c007400004000c00442201c40e260020000b010342c1481800700050790340c03080d0300903481040a960080c90822608028114803525012a801210b11a00c02c00e00081d941e0081442840801d0742d000020f0140c944483ea110191078000200c0d00301815180c945010040c6030420039144a01c2c014441074048025038100a424180a40c0240c2c040100b802c0c0180f0200e40001540d22459229242c00103050340d03036040070760660240c203048101e00c1e0043d02903840300f4501a0481c10904640520030850354030340305411051004103d800a010860010014020420b032440750500b14801a045c0c4426003620070026030103034000d82040c00402c0010480e000c801e0740c003102164900e80a0700003540782c0301c44184081d110401074070490415a140044041c21900c4503019500c8404c01c451207152190307121840c0c0342d0303150401d008480100386402c03481a44a101c920310540100c41586a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 385793866 1250 385792616 385792621
    0xb041205160623040b0c06070314070507020118050a1d0901020304020f100302040806190b0a030201140a020f03040e0912070c0501030513050d020d12020c1b0d06050a02030103021c0b 80
    0xc0ba55803c0c1c00c0c1c0d0301da03078456000b0b001c0025003a4074400101444540300c001781a06191103040a001c0359122500c01c14504001000c00c0a440d812908451030681c090030602d2025840040c588044010f6400c682e4024070044400140300400c607000291103d007000e0310030425a10a030440d801c0f8081150040c0d80700340d403110600e0181c181008000f400b1421454003501d443c1d02c8000c010b01c0c100042e15070032204070340300c0121038000905101d5503038440001c0366001c611a185400003404116441e40704080100300250b4608818000c0003050114201c9030262500c1d41c2e5100c0320f000c80314100b101c82d22002e00400280c001611011400c460345184d0240000010b6818040110004c02e0020700310500d440483c0d8501003c250100940581e030f400f6a1b004180d812210a00207260020032511220200e0050200000040c800700c9c0042000381000301c0040031644850010705200d4110f81c010b001180f500003030080c120410f80045040c0d900a42d04034501c520801c004c0e418200c000740000c0c0144a00001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 385795116 1250 385793866 385793897
    0x40f0225020a030b070e0a06030515132318071805060d0609050a020f010509011e05070b071220071709030d0203031501080103050706050d02040b0412051606 69
    0x600c444410300103810007044035240d65540b540c00e18180e803400b010600305040307006280f402c5402e500c060450f524050101d81400000750035451450614107100342c1011703040f103803254003aa103c1c00d44081092506038100101405c0b04002aa013a5410407094607402e084803100e01002a00342d04940da0002d008070344219a80344080102005801d140e0300451081182c8042151401111071141c0600040c100c42d242500c10840c00c1d601051015050100c2404494140c0ea0411504e02c1d01c031100c14012802d00210304400c5400e4800c48000904014200f0280280c40b40d2149001c0c1c40120444400c005103401011a40f031707403d4004443c0031401c201006070600182040648640c000c0c0340d007200504148081c80024208030340343c074020005078004001c222149901d405d0803d605c103401e081c02c0401f541180c40ba01e440c0e580c54007440d03080c8000001c0c102d0419169504aa008154501c00261a55110180c00d4400c801200041d100b41c4903401c0070f8580721080344c4a100848400c0d49809040f03940d10134 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 385796366 1250 385795116 385795177
    0x403050f0307023a0315170a06092109230d120f080117070302010c1a0a0603150507020c011209050a11150405010507021315080309040f02 61
    0x4041408500520b2041c09150307412852000540a60313500085100c1c03100d40800000713080f00403480b0308042c10501c0c3c0c02c414503804180082915002c90400520400d144042c0789428840310000300400e240864490510010b00d40d03600400c2c1c4504803000c10100c0c1c40008640c8480540180302d07810a00d0600c00352100d66080c4104411900607000c9252450251511701540d040d444d0040d0100381d44081d501d03078880d03002c0401809840090081c07044080d071009a240c6d03030200c074007009050003c0751082c1001d020b1800001c0c1803607012140f91031402c3c5896041c3c4030203010284000c550345483c5031002c0300c040802d0701590780b082c1030540c000c02079001c4600046078007075019a612002d1036500c90089002c10002e00030b5580140c080e0380e2003413542d1070304000d0101020300701c494419000c2083c001401545e0340203080750200e80d0125075228060100110b040000c04c410300d052580030203900000584410b020001e4100804201d404000d9150b0032840341d0309911030303040c20f040100d82100c1a03400c03005001c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 385797616 1250 385796366 385796371
    0x6010e0f0d0c080705040e0d030e07180b010807450b12240409060f0c020c030c06040f0302091312050903010f021603030e01020f0f0904050603060403050f03 69
    0x18080401580003030003080419400d003030240c4006800000074441050104a220003d190030b850401c800c1a40d00310b00b41d00c0f402d4030040c00d420191205030060544c80204860001741850a620400000d149104400100600030500340403480400c001540385005e208011181740080d00d000c0d412461011034203030400310742d0590721000e40c5040b14105180d01c0051180740503000c03114580d41e0325011020590400030000307104000b80b044026143e8001c05034141c0c1083c82142c250390105410b071503440d203500078041c41500002c42d03d107000c4d1340b00310540d800902909180400c2c0c3c01d842d140181c039800e1140a20581c000d134020202d252800b0001420f04c000c3c00da511155074000c06440540952b0340003030001050340300c403002910218003421030307207801c0c03003007119940d00381c5400c52402d00b1200d0b03469030325400341300040c013819a12240083c3c441340a404954181894070a41d55075620b5506d8008a0f030b410800710306010f2460403000400c90308000071a5801a60145c9910f07040c00e43c410680c42d03056000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 385798866 1250 385797616 385797619
    0xf080f060d0f0623040b06030c03031c180807020f01031505280305060f010609180c090e0109020406170405030f0a030b18010603050906010b0339090901080a050606010e 74
    0x31840050600c2c001a120341400340200104c00295040500740443e10100207041d0511940004802075150b0f030b80001111103008241c0d0b40e1450060048014400a02042141d40500c104803140c10042181e0540201402d510880b2001a0700303449200441c22541c104800c560074548210040c0b00602d0218002c288800310070018505003c01144d009408400550040368140d006005008144200601c05409001030340791280000d89084c0310ba13071010741b48c04003800c401344c4d41c0d000b40346540e031148217414041c0462484126055955030364120082d4810300c51240000c44508003504982c09440c4918000e941220085040c102105900501544105402418581d0707071341d943c6c1002d844160480c403074002d200400c0b001c20b41c5806005410380300e004245010640010005101113003100d019260850f081481c020780014000c4a0081040003030700c0410000326070401c603003881d805000010108448195141d03003a50b6a1a00002d40d10043c81c40c00800380d800840024406500c69000381551140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 385800116 1250 385798866 385798871
    0x1031101030209191401081605160807020405100611120a0e1c03030911030a0b0106050a03150b0405012006010b0d14190c0c020906090a0b0a060f080f060d0f06 70
    0x60016244506502591002c0303d1204c1401c4000004c0da0440d40c041e034460a1032180423206546603100902610ad04ca1200c0f81d000c60102d122400d000300c0300d09030344c403c9a0240080080e4200f000348000e5002441c42070304000313408090841e140b5400814294a83c1c0300288480d801e183da061401d45000312440c50242c0c0203603031b00600b09203030000a03840c1c0b261350780640c80002c1c0d1a203081c1400007020019001c018080d602c02d0600c1000070302201c003200d0454415182c019164002d1103c00c8001e04511040303a03d02282c3c02c440801c0d107609590062045803800d889081c03078001000110420355000003180c9100e9000031004200c03002c2030400800103440c0c0e1040006006502d1648070b02040c0d0240c0e03c1c140401c1e41c17100340c464030035490b1190003417030006803e084400f184c3d603500040c1262001810b01d8002c00b80707203010810f4241d0540048407c01c80041040b4070880e168440100440080d000b004006000310011440c043e4400c100540940c401a005c030a01c0405a124580164114007007192883d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 385801366 1250 385800116 385800139
    0x309180209061209150115080601140a030e07050307180506010201090c12060608010203060d1401090b0403051e0a0e060703111609050f0906040b180d032301031101030209 75
    0x584002c028030403101200d0391a01103040031080b00340b622500f803c0d9141018500801844000c2845148000da0209840e0050003950f134140103d030100b00301c04030f0880710b000108541900541580013076104c036440404680b80d5590b103004155440600e885414000c105105400c0180d0038207406c40c075803042e0f06000100d061115030340c0700c0c0d890211680c0002407414030700141c1e0040000c2c5000e0140208100002036055007442c20006202d007088210081006c06820f080e01b41104080d00403020301a0040345411003803034242000740c02540f0541d00249003408581c0194072002190007a1084250256640d100b0580c011040c032410b684401c0068043c00350010540c181d6a604202da40702c070721035810142c0250b42c80c1c280900150750340500b041c51482228420403d4000000440d16801900044142443d4541041280b800c50344d45905507400e004185071034000a0301a000881041480d0b0217260312944480c1d071686040030280402009150700107090754683d0702c41c0e0007a0940030310050180a0b0340 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 385802616 1250 385801366 385801369
    0x1b040614040e0106050c1e1b012001240f0b210109060f080a050c060f0f0c03090a29031009050405011407020d05090d030e030f1005090a0309180209 65
    0x8072000d070f00c0070001400001b0b21003950202807000043c0c10b4016640c0d200c1c401000c1d203880d61500d4651388410380d4900c0f1305003d03d072280e100d0008a03503c100001580c01302c10b42c1104282d4060700441c0340d907204a0410042d0111440058a640d6080300c1001c0c1c4103e0015040090805450f402803015003100504249940f40000c110b080c070714000e0903c4100020745910b01103003200c40c808554440f000365000254020041000818400d003001700880b0b00554880c1c251904500c90f014405c1c1c108001c04011030003400d020700010051101c403004444c0304c1400d5903102c2e1803520400400300e074003000341c1506400840c0c103000c80d001b440c1c204000a032004441e81e102d40e91442140d03011101654180e440703c0f4540722140c110546103030400341c1391018046480c4020805041032040706e20aa014003d00403040003454403556007038841010080c1070755407090740791540b0741d504c4111100a4414500c2c10001c279000d00800115980400d5160f1116904140b80c08900852030a4250058076225020400c94006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 385803866 1250 385802616 385802639
    0x40308070c0812060906060421020316030b0613020307021911040c05120c03010e180c1c05070f260f240709030f0b04110603010b0705061b04061404 65
    0xc5003142c5030059460f00c4d004226140307101814044c01a1400c20052080842c10040001c07031917040603030b40703100820320f10200746800701d240d040c40d40a0302004c0b000300803c450351003464002c0c20201d030980341840440410008910003580c1d00c20140c0e20009103008406481c0958a69450107044040c0c0301e86008004281901c1c1844004130000b5000581a442180004403507a0040e40005000c2d08660406808480c50380d005800555507512482190a035044100000c1c0141c3c480075284030840e03900d60103041a084001b000c115540c3c02100d4000c210080980c400703c0445050048290742c82c62208943c0b58481004400180c16010348100088000c80811080030700040c42104d4912060703003800b0b00405207602a044508000c03041608001207403009150402454004000a07980d0311940b400343c5800001c00800e03904050302000008140fa80301003e003905902800a460866444c801ca1a0380c114140000012003002840240600f0f0310803203814290300040c01210749807544410300804d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 385805116 1250 385803866 385803877
    0xb030420090c040812090306040b04050723030f060f0105010c05100c0c02090a05010e0408220807050102011808030c030601020f030d061d061305090106050604030f030f0503040b040308070c08 84
    0x300c88900040c02c002c045005c121403581c0358111004035041c9500100001c2c0c0300c407000b510181a0900343e40101c0d06102007840204014081d0006040ca404600310801d240e4807100260640701c0d01920280d6246100c01048a5105440030001d01c3e461780c1c01d01006444070380d0611400d54003446440040c10342a80f1920503808d1200c9540c55110b00301e580e0f441003041c003a8004058080e92070400c0010001800440502c03604540d0200401d42c03111940303c14203d4441c108220000c119000c568000380c549004035507441030368000e0303000f800b00340d035031405031401e103102a000188400002c00c002040d12a07424040c6401910510503103a5440320301d85d0291440c2c016403107104465a480108000c01c500010300850209011055003c0e01e183c514000340989902d84550f80c0b45945030710010f00c10792020f610040142100422042d151030700ca0404092504001c1022030102d43d810312049a0703540500c0c181e9102c0c0d07a00c400d80d40119030b95594121582840608484140651002d03000300290b2518090031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 385806366 1250 385805116 385805131
    0x1a011d27010e04020f0a0e070c0f05160603050703020c1c020f07090212011403060a15120602030108010c020f1c021e16090203131704050d0c1a040b03042009 69
    0x18070504184c010480000041142c0f14880d80c0c0e8050100303c0382a54800f15580318616040c9402d4045079820407004907a91941c000746903009540d440120409042e9008096a2076990100129038821b03d0071750887c03242c103401c142c0c0d5602042c1c1901c0081d2450002c41c80031451032042d80d090710b5804540318504a03103a00882072107074000c0b544035090048054201d004114201c0020b44049100300440e85501d00501b11078021525220390000c00410700c6109001072041102c00e03860035116007032181c0250001e00924846500304000b24005070320000301852039003101c001510307d9450320540c2c03000103074605508105500441030007110042c40030180c4405003c2407000390103412801190002420302c10f03085504941e2043c01030050043d0925601a0803039070005c0000d2260100142041c6540510f070311041d408070f0329003117607410411216007580448088021700b000902e5070078078140644c01280a0812030207001d000060101c1d4010002c00c46880854840021049002d40800c1804c6070468040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 385807616 1250 385806366 385806389
    0x30c0f03120f0c24010302011b0203100905190804121b090b01030b03070f261903080702060105150d0216120f030204030c06050f1c1a011d2701 63
    0x328004091006503c0613011018851007115036038002e40c45681d040c00060b0401200e070110041d106120341c0c282c00079540060845107165499007401002c1c1100382d038119440c0c050035107840300b4401444030030101264001107107418241002212392291105110548542d4206c1744043c4210011600c0c0030080d01108501185e15a41c860016081e205142790180c043d80c4006c10800458000c2d440200546040031140407041c0601c149480395020103401c1070683d802013100c0c800c1c4100c0b0003800700790240d1103515405400d45e0f8090341a81c803540b00b4804c064012038422042a4070313200c98001002c824000c0e2900606103542205508003800ca042c0d0119410100e4880f24019030340c0141d041036503504c05180c2540740504550760844850860310032502030001c0822241081c00c40c6800303030780038480b00c0c0091030403405510300c400000e0072020350f003241494400c802c0c800c5594410700d00046245c04802c984d2840034000824030448442020001261a03201c4100075410b8140400a0b8024000d44840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 385808866 1250 385807616 385807627
    0x30c01321308061605090f06031806070c0308040204320a0e03070206071502041211090a140f0601090528170a0605070e04050c0a030509030306030c0f03120f 69
    0x3003054039650754000c641683d11650070000076204a850500e440032013880c1082c2c488040e04082840d40c514117001c41d03480000802045440c0f5240c1510301441044101101c106440300030b0262020034280784050006641800000c015003055045050324102004444a9002d00103000c2c3e00080303100024510070b000d10205002642041740142c80005500c44003461403e48203600051350740c0704220004140f0221840192945401396068400030104503a443c800540c0ca441c2640c041c0580b586828801d0b801a40811780c00700d039030f10903608040d11101e411640c9407120303ea149180310004140c40d042114807040480c803500c541100c00201000e00c40658640c1128211200101c41d0981040400829103120101c03981400501c207800c82e500b01034005043d8842e82070480e2151210086a5082400d007018450807034181401480000c4091717070100501c0e180c5100d4680c0303d11007a00c0765645a40710681d180110324012191000548004045800b05403180001d07012075000040c0140e02c2c1c50004c1031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 385810116 1250 385808866 385808887
    0x1050601080604110417100203130b101206021303080c0309150f040312030603051b1305063007060c021002010203090303010608090f070e2202030c0132 67
    0x141c4681024040300c003800707210007507280ba0042c0d004ea40700e028080e19103845541c1d095030090113801c022141041083d5524038040f004590080030001c011101b14600c40009400c0c101d40c1e1407c03d0584a1041c6145a0000d441d00c881001e50008280c3c428500082c100002c002404040140740c40400e1001a540301e800342000c2104541c040d2542d001c07415030030003200b07801e250308608880c241d0b0f038000b401d08400081c20b01d00300c001380496040203080e8030038130710012102c0400c2c40c8102040c0c0c5049400f020313040800003100c000d07121305491844e00b050701d440e481c140c0c204282c2c003044000b691145059180010b083c40c44ea2800d101544824040f0380340e6801d04048d403d21925000e181041c0340025840c6090601445550b417005218910803c003498002c5803184000f881440500000c41d0102e803041601c0e00b01da031003216800e840d00c01c4403103280c0d004000c0703501c010320582a000b50000c01070010501c000d00103513442007800b0f21449500720411000201910707005140b01c0290844046961110740d101c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 385811366 1250 385810116 385810127
    0x60d0204021c23011202060c1f1b212708030601032009041a0409050105090610030b01030206030c0c0a0501020405130504020d0201140d140a0c0504120b13120201050601 74
    0xe4402a07520f490005020314a012400e4001e0300e40e041d030b041680c4000c000c603024248099482c2d0742140c000c88002e60100c0107020380000315001d0701030b10b25411b016140c0b9420741e040094401c0c5285001484240c1d0701640d1041d40c041002500d4500c1c0b01c1101900314003240303c108180e01e00889040c81c0c003205014440d40d00d48240c45400c00ca501c13044050000d0420b0707841395030250000350784c42241c45594280c1c3c024260502c0b20035402001d04107008400361868075a0280400300e800c0140c0c2c1c0310310b8002070821200c0d603c00e030003101c2d040071040b04640d08540900c07546500041c04a1103010b401c21000f01c5254041002509140c082c1d000182ca682c00c110800c03201e01050054580e070941000c00303000250382c1e120800c41c510790742406c0058a49031310780c801c3c49850081c04900c1d41024508021000702c2041c1d9041580302d69180c1d80100309170b0070518010b80b4907014500600d0b0046034a15000b8000840000c1001d4019a02c801c00a044680c40e0740e031044035842a00344070b03006035145c000780002d650b0041c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 385812616 1250 385811366 385811411
    0xa090e06040903080c07020409080304050c090709061211040302060c0714042304050c0303130e01050628020307120302070b0f0108060703090201050417060f0f070206060d0204021c 79
    0x1c941c2401070b5011914018034014001c0e004203c5004001400021540d940d80100c226950000e24152203192504000d1703128010400074034010b407003c800042c1c40ba442082540283c49840c4c07601c500d40746020344a18010032f5107a13a8400984d00400011000d655014013410040010b240100006810503640407103400309000d1107800b807130500144501085d1242d903880059045030004184640c1c035824110b15214007104000d40501000400c41e4544004c0d0080c00c00f07039414550449445c0e6a95070500005110701c5000102c0d58810030a402c40c02c1c03207015030019803c451441241d003099042e86a0000e41e030600c00c80d0401082d0f0009101c41000310345000742d5882914081d024446601d0000400d031240b0303000740158101a0b80350201011a03000b01c095030013600054150007401b00b80f0f6000e0031340d20341c1c0c1a02c0950341e000d0340310002011441140c52041c410fa01031b901401c096280d10302404014401c00c4030032a403058007405404e10b05c05120011990b03500c02c031603002c26a4144111a1013400b03021 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 385813866 1250 385812616 385812619
    0x110d110c0616120c030c02060d1514101701030b060a231c02030c150c0a1202060c0301030f150e030309060a06080304060e19080303040f03120c0f0c03140a090e06 71
    0x4554244c0e0200340c1001e803c0034501d0301074440780e540300f80098444000701040c240007620258864004220038100340caa5061200c4141d4401045090000c07098641c045920f02c21403004c2c00d40001031000a490000c52a00400085c01034600320762541100c2000c40c240a06004c071054150403c0048c2d40f030075000d040341d48850401015042c02003900841e840d03820882c035881c0200d402501d15550401501d045803910084502601c0c1d0b405410300d0400348201428074050010310030000841c02c00000d44003145d040300c0e400700341c050b0380160036540c0c10385a400b0324040c2e0040c1d5030f1b101c440309100b2400b0700096100724000d002900c00c9141540100b0200c0b075540d0840302c2c80d544203000a00c46641c0000300314440400484102c5800100c2d0000106201e015400c007081c42c2c0008000e2004100701520460f40e110f12a0b00c41c01d440c0c441c41450300003100e03000010304000404a01d417484005002c0c00444010074000d25080e5540d40403040106500d521850000b4000352600504001800785c0291081d0003150 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 385815116 1250 385813866 385813877
    0x9200711130905070501050703020d30050f0a02040b0a0f02030d0c020105100605030907180207020d120e10050d0914010e0703030908010606020c150909041a0601110d110c061612 78
    0x140c0e2710000d5985920f8441e080c14801119100b40721011a01c3c40c20700e00100c21402c1d155556103501042c0c015100946044043c2d107101c00c04500801254000e440c00d4400c0407111906011003006c00326400c114910f0030744254082001904e40c02c2056010747e5a003c45550008180d905050400c072004881607480780e01004024404e110340b400b4003107540011101e2221080c104600402140d5009200e05000254007040240440c41007054045100b1000039040d282e039a2088a83c000f17116034a070700e882d0400d000038010051001c42141d56030000071b04a01070450344411008007034449084460061561107142d0100c2e000b00105a404050000038000030402441000d01e00720005c4e544080c5684d84910410010207100b1581e48110300f84d405c0000000c1800c1001d0401c0e041994904082c106032482041c2d541000500d0355015171025600c050840000705102c0401c0c0400300d0340c03020f50144003002d500a2018014042d40d501c80589840a1000c1c02c80e0040304142c0b82c050540004e40102405000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 385816366 1250 385815116 385815127
    0x314040f0222020304111002010b1c032723030a0201350105041503050601140114040b1803030304050705190801050a0e01061a0301060f1e020d08010920071113090507050105 76
    0x85404bc0d49100a1400e90840d0704500054070342622031010b020107401c181140720340703001046c0c6840d82101088a0340f2004001207030190f41c00c0d00740d018a5502410707805610411808005500c40c250700c100051911401e00303990101040643c940003180141140e06100300c00051025150034401c2000141c141007807042c00516503540c00761520014483c01079607a6101d50948142d0b40101018101c1403402610966075030740350755104400d50840d02c0c051805000740440b5070140d040000c1142d0089070440c0c0105041032a0500700f00600b0070083c00c000c41c4410312440000c11020074059103020b80d0b04244042010802a08c0c41800c65603240e2003c41814114101042c0019403c1e04483c1510724502c4d101c0346003001104161540c01c441000754031014a21200080300d154013190420910040380e03144101a661010600140c444c2001a000da00c009083c0e05001b40061000030802c80b8030403042c010490002500141c06400c1140a2002103070f25200e082d02041070030b205000c081c2c8001d003031081c01c09 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 385817616 1250 385816366 385816369
    0x507030612110f0603011707330219060501051206071d0d3509030309120106090203040c0f090204060804021c050f01020a0314040f0222020304111002010b 68
    0xc0030032024190b02c29040291115443c0d00c0590184424090700850340c03541d440401ca03c04440b181c2030080d042c00f03140310210b0800190182240c404605403440034481d6212030704007015902120710300341507204001071210510700305030b0010803207806080c0c0000c0c00d603d0101400f454542e10300810700e113600720fa410041c1c0340e5000348411511101c6480c20103048807825003c40ca0000f800103000d02440d0080420000c0d1000307102e40310380e9a0702c0c0e80140c00c2c00c1800718001055907020b98420340d80d240d001407200b40c0e01c900700005540701031075040d8008141d0581e00e0030600100c5c0d0040c0e9055071a120f9810003808000e1100d003546008201e501021845c15140c03103801841c181300500000d209400400d88020f003890043c820000301d5400100340d511802c1c0c201d02e0107000b544a0085c000100341002d005111018160941c03900c01d9401c24a40200c1c0342a550800680d801400c4180e42c0701c00804802010b01006c0b44040d5119510403400307000340c49040d00c100724481c0c4007051041c08681c141300000480307 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 385818866 1250 385817616 385817639
    0x9040e0d1403100305150103120804020114070c0308031609270504060209040f0b04061e091d06010b0d050105030105060a030204020a0c241b0c08090607230105070306 73
    0x2841e0400340182c0301c0d01da40031456200c005a600142680c41001c9003290401c007210606812a48240e000011a0060910546030300c0c40480300640410141c440f650355001d01c3c44009c2500501c00d01240b144280c0300e07038815038103810070f45840100310308200c0c0401c032a540205600c1c01401e0007400031b00e800404040d244844040380e807903a4410300d0b1100d01103410000282c058908410700108148041e00704425000000c2c0341c000d21840c440c03030400c400003840340b400794482903042e0000594606c0382424072180c9400351620443d02611002201c2030149074280500442d40030340800700c0c00964601c02c0b4000c00090318010b03000507209900d000144030443d510042404216036041c0d80150710b488280b2015240c040820780f002e40007140102c1000c0d203804409030360307029816103c1400c0140c5200e07490384121859410144101040e1580d4100c40404d00c3c08001d0100450020140ca252106036500c48038107140e526521000000d001381140d0034004280a0254480028501003004900e8405208072 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 385820116 1250 385818866 385818887
    0x1c0b07090f0e010b0a0507120c02150708030a0203070203070c060804170405030606040f02040503010f0516020607020303370e0f0c06070b04020301061e060206060102010213060f0c120509040e0d 85
    0x10313940c40000b800d4030000e001d10103440c440c903001082030104903150391000d00310380301c1e2a03002c070721540701106a6181d030710000c81514034858000c00c40500316a151200d6100a44c001f40100341944418010940003421200071400a04000d07510001c440c1428a401d403103502e0031100c00105070b40306000500a0b43c0303001507a113501c510110b6010440c60130000c0e0410081c803c60b00820f0305542842406043c500e16500800e00074500e00d00104c2040b00a020200d071074400c203a8004005800820100d405d5a20180724424203108482c948103214011010801000c100d080e250b1780c0b030540f9090701000c071103030030b0001e01c01c20300410b406050003c0c201c1000440510881c03c0003816403124802080540d06c0944c00b140140c455440255006419101c0402c4e00c0c0c501031140d00014859100011001d51040c0252002010000d246800481c03c002d820340c0c2d013640c03849a0350304008610504402068110440781c00c15502e9880d9503a4511808003440b05031800c000a20301140c0c0a4001d0840080e130001c030840d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 385821366 1250 385820116 385820129
    0x60c03130209070c0c1415070305040315021204030c0b06180109110d1a1306051804060b030105040b06030c010908031b1006031b1d040b061c0b07090f0e01 68
    0x350f50358014050b942d146800c000034040001c14000400c4a4145424864000724121601080035000c1e10201600348100503004000031000c0c8000c000040c02c020315044200f01c40300d8050300b00101c002d1040c04c600012a800d44c00507a40300309141c00e00208c4618281c106c002500c4445082e0240003200c100300a0601c18814040d40d220b0912440003041010b0700d880580b12038040c41565003d00002c50b103512160303c0203109035020740c180b00c2194668400c1004880c00580403804420143c5034800f4a1400104140d5035141c03a00700858441d5030070701c50140300c1d6100f00701d030b00150f09100c41854600750740c541e401030512141c500c0510203600d0020907103851104c040b1000e10145150402c1da414400e941852003019814148080100010300c0a444081442d1003000060103645071200900c0d450b11407030341441c0e0484113012030080342c0c001c6000d17644010003800b44e00070006c0481008505500703840c415620309810f40107100e10150700944900c01080080d092036009418580100c051403418072030403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 385822616 1250 385821366 385821379
    0x20309060601180e090705010201050708010e240616111c020607050a0206120103050c0a03080a0c060b15251a060d08030702031831150b0c060c031302 66
    0x20068008000f40e410003804004415220034100400c4455a4182d24011640554204070004e04050f200324840b034100ca4610000c00b903191100a40b041c04402030745800d0b241c00c805d4012041c5951030b504010004006500608241e0079001d0500000f50010041c110740b1600900c10290201c0c1e2a4907110b47c2000c0c0c0484050380e94403c545407641c50301c0c0024100940280c00420004250254400c566040b280928151008842d400c4100140c19003603000082900d1002c1c4200007620348111800340d152071180340300080001d0b0500000e8201859156025400000040d04070071040c03101400c98a0000ca083e85e800781c2030038603a2080320110201110081851500000070380d01c0c1d594005070350b1031076006222503a4904200c1d01c000c1d200d43c4800e83c10705100d05902d00b00c1815081050078543c0a1819100c05d0000004980656007042c0d0200281c0c010a61034003006080002049038050081900c800d6282d910170000c0996828240e00915031031000c0d0090040005400082000d44510765044908 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 385823866 1250 385822616 385822637
    0x706020c010c140703060903020a0302070509040803010306090c0b04150e030d2118030c02010807080705190c06061509090b030c10031b020f0c0603041e0c0b0f0306090109020309060601 81
    0xc142c54113000b9803002e0402d50410382c0302410b042d00419040381c42030003a0b00341c4044948541c03c0c040b9110080d1401009500100010008200554070124540b84a130007600079059503041e03000c40d181c2240c2c112915080115049484194000720003000e58002980500710007070003810003401406400301602c0c070269014031007c9040c50300d40c0c040400e45410464001100c1a00d003000bd100c224107140407804111300c1c1c00440c8205000c0c9800b588105080e0359a28581003213240d400303003012000408041841241040c48001803114000c590140015801241d52090500d00040800f80c03554088100c99140042d5909a61408200c00c1745c00c000580d8001d580e0341130100308500401202e0b24041103c9420903805030b4450b408a01c00342040005000c84070101d18070020000b45102c183d50043c0728080700c0300da240030070422a418407400d900070a150741155039248184011940030301001ca4000b03900004110003440c00981003405000f480720f0071800c510303005a03031664890b00901440c7c14498900f05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 385825116 1250 385823866 385823903
    0x150f120302120403150c02030c0a030f020a0b0f090c0109230f09090c0103200403020906190312020d0927020c070906090b040203070219081e0c0706020c010c 69
    0x900240280c0d00b8802c1641c03660f8030704126401081809106000505290701400c0c01c61001094a042050714400b4000d16403132507800b1345d00c68814031050070941c0196911000031a800089076441408009860307003403440c09c48100d50070080410f45441c14010351500500800c2003d00c00080308600510000802c0d141420000d11604c0d1000c0d0100d5002c13007040708102c5050400b003800d04c0c2c04807081e00c3c01e000040c2401c000901c3d4404607881c407080c1d004103000401c05840e148100d160031220141c0040c408480344410f401d0111001c0d0000e0f0b4959003071014002e000d40d410440ca6180202920342400e5050400c081500c00c102006034000c001c5180381c1d0310100e580f00d02d42c1114025400c020440306060358400220700605118440c143d0054505080451142028021644514820360182668814039060161010011802a2200340c03040c48000034600000e011002d42510340d10314140c880201c0543c462411845401a1003150400c083d550403c0e40c104032212200f580c0400611042942c0c0807 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 385826366 1250 385825116 385825123
    0x203070f05031605031b0102030c070602030a090f03350c1b071e140f0d050a0b01090e0c04091101050a020c100512010f08150601021e070801150f120302 67
    0x1d2060111a603105101004c0003800002031070f03008520038032008540903030300c416400c0740002c0b41d01080c000b0301040b16500040d8107500440d030002d4002800a0403107d60746500240021440c422004200141249101c541004003c94048004800180c269514110841102200190100504180224280c0790300140068040c5440342620115111159128100503264644010120414940c00000701c2c2c0d20706865804400b144002e4568130080900c1c1003407010300c00c018801500d00b80a4100d0900000e4400c640a60003030402140105034090000c80050030211000d81c0e0b144170382e207484400c0000614010701c1e01017180090030031030344550300458203038108800503400d1588128210040800c8581002c00317410280010b01e50300490382e80340c66542c12644030341d000c1e0306116408901da00816001051103150300003018410340b80324503440303034038a035111b0164000000284c0103d02c05001002e000d20070400700310394400c0c01c0a03a6500e040c5030405420900e014810041650140041c1854000c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 385827616 1250 385826366 385826377
    0x15050a110f0304090e010203091c2a0c09090213180807050601090b220c09050301090308180a02010e090a060e09010515060712031a030304090f0c0206070203070f0503 73
    0x426584144510016142c4036030160052000c01480d00d10340070300c02041442600c1c031450400c2c2c0140400303078081c100c1125540c03d49080303c0c20802c18030500749a00d044504c0c2450248011380402604840505d07042c050506250041d420305840d203031000001d6a00c01c0041020700c40b03d42400a100c0200819018201d02407900203041c0321000501d4408105001803160304a40b0b41d02c0301004000c500c50100195a0030544134110480460b440d0301501800c01d500c10102440d05041140d4010342da0b0010034252030414500b6408620301008100743d2140242c1da810445002d400502203400d6143c0c0060000c1c2c41440d840360140c030219000500e184826401040580110307201e44140e8030384842494003800e42120704480708001c40344c14004500b401c00c240c1e50555800040016082074025007100100350fa007120f004a41c0d030200c2400c0c11924148001c20290180b804089440b00743c5500311001d80b20703000385180441d4040c000700200954040240c0f8006a4042418002d2040394202149180182e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 385828866 1250 385827616 385827647
    0x606220b060f0f040314070e070e041d01090302010c050301080307080304140118140102040e0105040b0d02040204090c091e06050d09170c060f1029030703020408100615050a 76
    0x1502000f201201d00103030084a210309070040d00116050301c1961a004603128010201c5010400308102c20b00402c07919003102d002501c0050529035841c40e825a10001444400007030b5900c2001a051540c280a184c3c40304440b801e0852070755142020382681c0f8818450040e103103210100100781000740b94541103ca40941e54000d00c07203506580c0341680c103000c02c050211740745510f020190140501c18020384045911128907003050303070318180500c405400b1102c1026888a00b1004290050791144060700140110ba01d00080c01c1c2025000600401c107a0f0304481c0d101b801d01404e0342040c440c0c54002c401503890b0341c644141c90700d52070300494014007150140140a20311185404800740c0814018158484ca180c0c200c030810745820303191651003035050355400c00c840e10031102449684610f0707000a940180141040d90f900803884500c01154106030b0300c038000207400040400000d401046030350030011031807004024041c508105520528500c425100a006020a10118040c080d0404016901c2e9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 385830116 1250 385828866 385828897
    0x60a03020f04170d1d09070c02100e040f140408090604030b0403030f0506101d0109030b010e013605180316050f0a0203030904110c030a0309050606220b06 68
    0x1100e5183c02c11405902c03036164024829140d003040d20504c00d411071071035601414115000000c100c014841d402e400100035106004196601e180181c665807540e807114166681c4034030304500d050307040000340e5208908041045041c50000203000e56440b0a194116034882d0354203580705607001c0410340724000c503413015000916020401c000e01d90141c00c4000007855001040105656480802032818050562100003402c4000c2001014500c2c8464420b0074805040c98100641e5030f54807031200d0700090308034810b076050b9000108010221800d000ba05caa4580c04503440d1062010551354048100303081c1d0300a0551103c0118a40904081c0201221000300d010b881e41d9003181d002040780e110f030000007140d45110380b2031041000070001c18101e003035941c003c01031450001d00340c00300005480c1d1072140100090307080080ba2680c0c902000100140c5405840c0490030350340a040c4207083c904001c5c407850103110480b1660390321303403440c0c0302d007134440b0f030484100146a43e420030114200f8010303109003801c020b8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 385831366 1250 385830116 385830119
    0x602210d1104060c06050c1206040941030a021203100905070e0a05150405090406140906010315060501320f04080c030c01200c03070f151805060a03020f04 68
    0x181d01c0762004070380311702400080c003c0352941101900c86101c2c014030701441091040c0411442e151036001400d089026070b070441d481c0616502d0386030401104c020050b50b400f5800b100c8207170418800310100710a14084e0081d605220012802944856840c60000c2d84883c1c0000080e05034603080c000800603041d0030700f0801080c90003a801a110049000d04135108504080000a80d481c2c10a0800900881340740300300e007814613250601850b404040c10445245803540d0b82e0f001c20211109580344240c00c400001c281c00d500d5820585c5040d40e4040e89900c6081c02e00c0e20a0042303136040390304480390308694030000c5014035101d200c403001c0d00410100d10500d15400030f011fa800c50104406082079900c4001035030035901d404002c0646c1c03145508042400710300324a0348000c401079041c8083c01e0480e41c030400d50390300c1100080000c1c109680c80e00708200c50000e0400a1104000210039004841c01c9428102d041e60154400405064001d1040c141300e40c600043c0c940c0d08034400d030182c40d00c08114010031a12107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 385832616 1250 385831366 385831379
    0xd031101151e05150715110304031407110d0609140102030a0e28140712060b030c01090e0903040b04120308090a030e0f1c03030c02070602210d1104 65
    0x1c02942c80340750350444030074524041c52003007802000100c9800038400c4d640c003400d8105019a9400412040e0340b242c040d41c0200482c28aa4050f10181541c3c0d2508265285170500c3d010f4070700c00d061a40d4480c0d440040c0604400540b400e440d51030320300340844030101052a14078013007002e0711041c64010000710090703040400000c8150083c5028640662080c042c290961720365613650325000e00305400801052810b01e1152001c84401c0340311031302544000c0400c06c44d83e400e1918000b20f0343e00c400169550200c0f0070040c0134a51150500030503044002e441e1801c80030700020208030483c0120240d1403045008526010010030455000700020901543c8495403141d0700682064008401e401190b80a000200785050100b15031a40c26070549840956080d000280300c3c0440e601551035810a0b00101c200007011404080b06800c94400e990114130081ca0700d00090500c401c545c030070004d6601480c1000b0400741100d41510300c0d5000d4050a036121008091448c02620500700d51f05c1348000b0002e00481c54 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 385833866 1250 385832616 385832651
    0x3160f02190512210c0319170c0415080c09040c02060f010609050a030809012c040e0102030c0703050c0c120d09050312040603050403020718060611010209030c0d031101 74
    0x8490084443c001c034616081d81080e1601c802404501c803130310000b030038503990204040280003d18102c00440e0708155003c412160508807140a01010030515042c06000030303402642c1640c00030300100110b05140c501b103414100c591400a0040500000b5000502c4d10b00c400c03410303074401d9a4010020301a1100703105000c1d480b2030081e42c40c5e0688540c400700101c0d2150180341c0b00401ca400280000c0a800d155813201c04d40f90300071104990420401913001880c0920000d078a0110040ea0310706034a100c50010104422a000004d80d8140e03a401442040b401c00740800c01c1c0c80c6000e8060030500c1d034070001d10045a05103000c0520a075071049402d510021460340c0011004030f0165643c4405101a44400c00c15075100c1e1125140a6a03c80800041c01040d100b0340249403c14428011915059155500c00d410100daa0518511030799450404002c041c2c2e20490340303c10150450000c40c644900c100200c0d858020161100d40100c034400c5841c03040600c903001080f08181e840c0001c00c11140c007944003040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 385835116 1250 385833866 385833869
    0x40b070302061003110121050f0603010c08060f010c050102090a031a070c052a100f030f1116240605040605180f070e030703110316030503160f0219 65
    0x10720a440010b10fa2400000b50314060307a8100708031406458002c40115141d00c10550001429606801546000b4126020701c0d03000e2107000c1a48030b03035031502c5070626007120050303030501040040309414030440d92038140c1840440c04007840c2105048000d401d0660192181300c81d51600700000c1c080003c288142c0e030180c20b0407030f54900a22120f545070340304100c0c5c81e05c0740c04901900a810100c0d400c00d01c0040c1c456101040c02e80701300020070700301d921800a0305581460075010045102c0007042001c0d56818411140740c036030381e10b5042000c1414804105154001d030396401c81d2035120703a254141805000c00d4441c0320008139007001d400c3c1e81d0141c601180601000d205d40c500540c1010008a00d516203070743c02014210b44180031903c20b079546101303986200301c05400c1406001680c80c2800c85514140300c0c09010b9405814114000742400f4181407400420030519003030403200110520000c0c20100803111900480c1d0a400410a02400c2000f40c541c20300000030b61040f2951048031100041c5502c007030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 385836366 1250 385835116 385835123
    0x80f0403060506060c030919050d0c050109080d0801030f1a150f18040f0c0512011a03011503030f17040506060301050a020a270f06080901050a0219031e02040b07 71
    0xb140d00c801040c401c09024150400046400900c0f4005150401d08000444491003148407a101543d82000c50300c041c0c840d0320241c9000c01c0300002440f40756000340c000c000903e458030003460310b17603803040c4000c000c0d135818000100312070783c000341c1113040c00900041041040c1c0000d02010750390030207100b48002081c40216040c002c0700e05a194880d0307890f10b0b0034207401000c0510421312965486a9400101107410300f41203960322454031000c03605450b961a0ba82c5440084000040c2e0300800000302c01825a065103007034400ea0515081c840f04000100c1050100d030707414204100000748480781501c1c2c4009403c0c1000000c0b006804100034440005001030180070103070020401902d508520409901c600c0c0400b00106803981911484d45443d2602c12002141c0c0643c0ca640240d1100e49250700320442e070780040005031145040c02020202031080d182c00a060040441c030300000c080714500805102e40750402031503030303c84501000c0741151204400307040c81031404650f5951a0019000740b07400039001035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 385837616 1250 385836366 385836371
    0xe01060e0102030a05030402120a0606080a140706020706051e0a0c0b0a0501051e0102070b0c06040506010e100b090105090a09060f0e09030f0c19050c10030219030216080f040306 78
    0xd4550011084070601c60710b42d6030f9545196215024007026410b6418041183d10a008040703001c03034040d20404000c1d01205026007140c28041c01c3c540e038842ca454141d64150303041844200300759a000156202150100d080445d11546511000894856520010311a10200061715640360b60312800074024070b4031400c1d0041c01c5445040060003290310900030301ea00001000141d1050b80742100d0a9001c0680500c1280d00340c58644c4d800d82c07240d80142000c0105a4007075010b000421006000ea40c1c050504070302c28003600d182013180c44010014a202d40080382100081c0801664401d03c201d400b807081c05400b8030f01c05682c50080800070200c611804540408000b070100c0d404002400c16402003400c0001142003034143d00a094081d03101c015400002d200b00d40005c0d5074256415208030003180604003070420382c013074030041c800624100c10b042000c2601c100b01d80d00c105070002c0c208000f20389031417500581307403808400c1c7c40c8409400c80401525080002c140c2c1c810303207080c24005100b92441a50103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 385838866 1250 385837616 385837637
    0x70b09400624110109080706090b070c0b0c030a1d07091104030c0302131d071a0304050322051201020318030f0708090a2301021e12031f0e0106 63
    0x59040c68502c000e1540b0140400c0448400b01c40c800c0c40b010400d401100c000040404495907003080c0d0b544450412a1403680360f01030441440034201c0da0540c00002030408240a0b0441c0d901c0140c81000100400720691010010a50402e910360001e6841d01103031040364200c80e28090351540d114078603ca0920505d0400c4420a00020340d030f41070300d0890f54403885c20001c0c907065900b0400d40b1103c102480300810750711070004513400081480303007891a000e0000380410707504010489210745403c020400c0101020001cac00000b4000208503907502c0300e86200c0c0c0d820365000c54a0701c40c0100f0380d0790040da407051b0140240d8204a806500560044214181c0b282008000e044001d4580c00351030134000b040c04061103040040f03003504000b4214000010260a4141c0d1a4810340c0b81505189a222511460340348800301a540c04000468200b080b08460b824054824104140c1e1644c600d01c800c4950640880490480c400d42d8401941c84480482c1034824142c542c1481c1101040c00d108041c00075034080740 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 385840116 1250 385838866 385838879
    0x1180b1603233705010801050c070f020f03060a1401050a0f17010e0709050a0506090f07032403060b0112050702031902030c01060311010e03070b094006 67
    0x11010344500d031803506041458144240202808001c3c03610603000700519180c0100e660011002110600e03400005603406001010728084602c141c20400c42d6a24000501503440542c9054800c03807980122031004550080c400b180404429085442d011301c101e07803e020b507120443c1c00c5404503103c0000d1349009030781d8034001c001d1108003034803600600e004418424808155000427002408583ea800420142c001d46512840c2003503e50007407010a40d92001d001d80c4086600a0076006241112000c085041c4034050307000c1300e40090402c1042c103995418809141003400700c41c0080300489041c407000e0079030300c1c105800580846d21241d40040c000d11518554041c0510443c1d005502030742c02103080c000d43c018500c45c869811507a07581944800d20003c2d04540e8240200c3e8061440b030544d040342d40d030f0000300140020440c603602503c42d4208620a000c0d010070b030416520407802c119074030012080d414040941101070715400c00411419a122070060101da00780303e0b4003c010b480d030304208107591f41d903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 385841366 1250 385840116 385840121
    0x40c05040c020703080a031d030a020a0b070201020702101101090b0f01030c0806090318060d050a0e0d05090607060506011b05030a0206071b140f160f0b03061c0501180b1603 76
    0x40040302d01b4406d6046052085c2e10243c1c406e801c064986d40a10b495082c60b41c40c682003421440700590150341120b040003007038080b190300318019000079801c041d941e6000842803440c4500107400c2140103101402d80c503100350018405e032500706115603924101030410400818090106840861004100145030301000a6580c803070071083c400344d42445000340d0100640440350310f0046c3d10000510040b0b0064069100701c0c5d0107455400e400181e140703807010f0118100328107580703280c00b80034062111144030707203d810480e0345280e8020400211540da400041e00c0c407408000880103600400c05d9040e0400000000410120b40c00d6000c4924683e15040d00300c881e40c405004000f600075a10305000006682c00e5040c0201d10f60817001d80d80c0d1141822020352074810b20403004400b410040d5401c00c050007800e042c030b8000e08601d4105074558504003010440c00b1010035842c8020001070710b0244148442903010310106403c0015460402c0860300303040c0921542a15041aa04030035020b0440d468040d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 385842616 1250 385841366 385841369
    0x6060906150706020403080a0e011116060327030503070909050114010f0c020603070e190305060c0c1015180504170d0b0a12032c0f060909040c05040c0207 68
    0x40c40300040c04050310482001da0400c500440c3c0c484d809000110000d010b4a01412401c2c855690300c0c0d000704142c2000516418000b000c2c3c00541d080303501010309480414030480c1c240c9455040210300711400c1310b008010071006072040ca034007441c002e10724810164000300860250805907944041180c4490066044070380c2171140301d00001203610b0b07150386940254580c001c0d8204c3c600b4805c0d0404080d0700030402680c0304580745800200e403102000000d24100040210901800c11050275003804d5030358069480d01e000c0d003043c01d020f0700030500f081040030802540d0307080310b0b4240003071146216900940c1c1d04c810340c50150401c068901604200f0300714444c450740388207075044000c001a084800d440990240e01080f400954661200820300003600c1e106404401000106c12070740c2c030310046080c010300200544091039654080d401e0f00e031154001c5054500055030085403d4040c480324500050a9885030510300d68002000c1030800c13050180480015007250001d48080c8080c881c8440c00300e80701d20342c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 385843866 1250 385842616 385842619
    0x9010507030c0302241905060d0f08040f0b03010501080601031506082e0504050f01060903030f110f013c020d0204081009020f1c02010c1b0609030506060906 69
    0x14055440400d11500e5030b1400307030380a40182c403603100c003881000c45070f50703010102803110079010814400c2164821102420082d030003101000b841c14030b10002180b20400c4d10b40a00014013101a4500744155402201c0c0284400210f91209590310150030702e03150000d1041c02c1c04601c9a20001c5c185500074090300d042d8820900c0013900385401e080c801e0701d050300080d106a00e910b6917480e02881801b000c18441060700201c0d9061801e051a0500b08000e0b204000c0ca0036a2546d6010300400ca25a041807031181a1796146c00c4c00144e00d080020110389034400c4d08420740b071034803550481c1117990406600070520300141c80350310703c229844180700ea42d094a00c40e1070b103c1c000c000030711085031a1866074054544000391440251034a903175500480e2400d65041714030010b4070f82e14081c0104600e0705501e2031011100a8a1034842c1a400c1220f032074103400e540070003038107005c0c100405104108144100c5190f01c00344042e0b10b00e55070b8596000820120140c08103c549219940204440e480d216a03e103224040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 385845116 1250 385843866 385843877
    0x80c070f0b0a0605060703090f1e060c0503190c03020c060414010806150c1f0b060f0d06031e0501060812090d05010204050d14010506120c010f0e0d03030905120901 72
    0xa681ca1640304030009040540d455502d040c00304595440e034001b0302c22180690390b032103020360070804400040f807075a038408820714101d500b030f200e4022030341e459180131071303000c2c1c1003050010483e41410b60440c424400038100000c1c00100350300d00c07941c004a0300b03031805009a0840381008681d0702400103600c200d0003070b07030041410543c409009600c204446540b24401811543c01d0030900e1191400e40c0d0001442c515060300540102c1c2d16180e10429401c005201594041c440b0021a1000c118940b192038100d4040364000103c142c85061a0381000e402140d10000f40c8940d9050780006c504086c0302280202d8055080050014003003400144040c1c0309043c0e070903500d107006450000c000d000f48081c00126801e540902000a40355690038443e208a40280403d1107000000c1002508650005051610480c40c540303800050900015680c7c840341e00a0034000160f01d07844100303a40c40c0ba07100c0681540235141c100d044c030800d030789500b20780380c01d51085c001c50310740900d007590f01401e81c01fa46000d0703800a40c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 385846366 1250 385845116 385845143
    0xd02131e0c2006150d060f140702010c090911070b090d0f05180f01020a1407260c19030c1d07090e06101205090c0a0801020a0c110f0d060b01080c07 65
    0x440c134010b03082c100d00500d00d9481c0a4580d40d408151100940070404403907440720f035140f880600858059000c00244003c0003203c11000b805010540e060088085039039623028880d4071780401c0000c603001e0a4001b0f80005451400c600300a07a07550440e40d51100251101e41c0f1820784500660960740b6450041403602e150300500001e101e8800303c0c4507211360440c4104024200420a0b202d90980e500c0c2c81000541910341c102800744040c2224034611451514a02c0c2010f8054200414004040201292001658000448180070380d1503541c2010b0841030f64008002208440d0081c18182c2884910b0b8241459552440035510a110340c41104601d50f285800030721306140c10003100c2600d0000e0f0030100c0d5000500c102201c112141152a81c082e03500030b21541c0c02a14240b42c414008150005c001c4d071a00c1005580280420351401c002412180d08590710b01095072594451041510b000d880003d011045040560181807004202c0d0301107405080031443e101d50705812a01b6041d00a0f000071800c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 385847616 1250 385846366 385846381
    0x5040216060e012c070501050307020d030f060f0f030b1e010e0402010c0609080304020102010e0102040f090e030c0a300f0c0201030b03070b040303090806060d02131e0c2006 76
    0x2d128940007480d05568842c02d039618640f08000701c00403070482c0d0b512207aa0000f0216400c0c50130038a504103a0501005000300100550b0005417054044003a19002c01c1981584000b640602800d402c217400003100180085030806e070940c204c008607402520511255240d1035400900b5060b0756491021010440006008860000c031905801030b10626010100181076100d0604607410550300715416000002484159030f4240501402c4072403000007149018908170106c0040110342c4103410f291510395080071643c10040c4191009007502c80150740c506000f80c41c01180740b2003296807410f00000d2030100b0f003540807005000d50245400030344480f0140740c0d9a110546584001c004200d04140d11a40021070725242803210781d00a01100c10043e49032411483e015115106da50400b02040d44158200032080e5141a154858281c0581e034858013010303803101c2c040290600e0b13260f06035450305140760300445407600d07400200034040503512107460340d11626070b2100c1c8506024848920390b1198021a014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 385848866 1250 385847616 385847621
    0x10302010c0f0206040603050601020c091005192129180118050c01020705041814031e040509070302070b06060d0e12030a06051f0305072010060504021606 68
    0x814003442c004254030046038002070350396000380c01100009171140c0c24007000f541c0410403c02e61204c11550000c0e50701c1c10b035070740c2410700e4040c0c41003500c608110100000c4000004050300050b160001c0f000c000e0300d0368265828801c1d110b001040b140282040c04c441c00c05012041c0c8404800c01000462643c0d031640700005c2c010030003060324080c45550319040e000c1c40704002d0307542c19600351044000e000c005900320006814062160700090195041c501d40000b6a8604202d2201940d4000c44031080180d444060a1035405200110745021880e400042600c1440001500c201c52044038440c00b65694010b08805034050b800c0003c200ea910600411510300e401d0000d44507400403102c0005030030044807070951810b1b00711440c402c00911300100b4800628810f0240703201410080d01c50b142c1c51850303c03420101c80780c040c0c42e00100709030f0390b480400c4040d4450201000ca500000000030308040d003010400c1d448002115460030301901c0c080b400034250609009542d80e96906168803226114291a010301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 385850116 1250 385848866 385848887
    0x30a1a0703020405061606050a0603080702061605070f15090503030313050124050406061407031206180218040c0f050d1428140703180210170c0702010801030201 71
    0x52503003d110108141c0ca98102a194020314418000900d00c8113040107012240c02074021306105050020a10200f45200d040b10a515810b0702d001c0c0d65903400d50401c010780c44070800010818007800b403000922075854941c0e0010f0f2960429106119101c00b4029250040385114094040d0028030015100c00c040703210032a680342c019400410242801810346501240c401088584042c5821092019040c207100f0000034001070308140f042e9005401240404c7c0c090550f00030100100d58030306130011b1a89811000081010002904100c40315440000c0079400804440140b504000a401e2103450036000c4c01702c030140e07140c80f00e4105030003011044800e5402804886109501c4003515481e0403c40d11080384039401c81901195500785080040b060114040c9820f44510b040c078510950880e404803190703400440c0b0b400c7c00199226100707042c031005500d00c100070f50700280401650340110380118000c42003039102d0669401560300e400d20f12a8a015518001c3d00086200006100650103071a414a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 385851366 1250 385850116 385850131
    0x1501120201090803031029030f040807080304080d2a0507030302041203200c01080c03071b110a050a1a130b0c0c0a14090402040b040e100c0e030a1a 65
    0x2540c0c80d8441500300d14562090b14403d003101c02c50841000540c084c00c428941649442c0703154040170f050440c4800751348c000a0140750a41c503900f4041010030a090044628091344007485641381e107410304080c00f207604001105281c603810311555140d045034404032201481c05c000d54410940c006800e040b01d9030b8225240490905500b000080f4201c50b44100440c1c00a10030342e47c0c0080101c03a090682110340c0c900c0041c51b015880403441028070780e0006419540101d075a41d1454803076a410001b01d50b4010355801c80f03100c40050070702032018069405461000c498080d00c442203195524401d001c0042443c2c450b040760001c22101300c00120111074002e100b0001c404042d104915281d00c42403c0e594044013119440b6030104003070b45038a0400030090001400c120f82003803c00c0e1040310208801003402480284202d41d682a22803072503481e40c0c000c0411004640880c2c038a148aa850403001f012012000400304401c005600311034034000440e0054035600401e0498112002d03a40d11403402c00250144 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 385852616 1250 385851366 385851377
    0x1707410a05090907060314010602030f07021518030d020a151508030a09090c0302030421020111040b2d1905090d05010b011418130e010510090b031501120201 69
    0x2030281e03602d0030001d009140c5000a00030300d84c40c20a024080303071b041c000b07490103101045004101898010003aa0041042504016999880d901c0051003104140c0c00500c01d015010030404910091400050000c60040c0c089a070040525142030b40d0f9841c41d81070003400e850390412081c824034000d8010707001d040e1000ca13810480719200c61102d0b0450b0041480b0000203180d542d0300300010b028502681c0305c08140c41c1000c41c079505094460420362800300860f10348016080080280f050300c01d40c400c8244040c60740c14140c41c3d9444002c0381f003569000040d06034800c4000c402c180c810b43c1c6400c04e1030855900307000d8580d1822503421101e01c1209540e509060030b004091004d844251104000308042030303c1100005005543c40340050048400400c4410035030302c040c0302c418a00cd0010041e050404012074005503a4a0301c00c8030392000e010114a602510350a00f403d00c00746003140031030401a204800414454800c45505056981808041c6147c1503641c84004110f01d40000c00d0f603441903801850407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 385853866 1250 385852616 385852619
    0x3060f0105221d0a05041203020310051e040509011116051009030302070506100b0f2505060105011409030607030506210609070e01030503030a151707410a 68
    0x215100c103810340c008540c0050040f85100c1461840b51400d501c90040b0508100b00c0c20542c5405080e248014a01c3c418158004041800414015114001424010b1801c660504400d07414100020340c5248140540e007000007107012540c041c09011085070300d00141d00d00341600f200400c00664a040019250b0b40221001000d5180703031790140410b41402a1030140e501c100d10728155113068001001c1e040300158035a4144442c0070213008442420450b6101036071a40b41e403030710050382e1130340d1090380300e84900e0340b8130103e01044000f01d040c5049503001d0721110700c01882008501c80364441c020795164103800440009a800b4000d030302c05078000e6409416148117000340c100a00111841004c0a0711036480700080000e4546d013049a1405004410071b91120755140da9201c594034080908900c10140d2102016000454910f0000c1c0003020080c500c0c219081c0200c10440e22601107000e55110f5012030100001140d00407030301d02c5030f0703407079050103001010383e040070351080c907141034000d07140d221720382180 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 385855116 1250 385853866 385853917
    0xc0901051e0f040e010605070b061905180a05010b031006030504110405091c0f0507170705070f09060b070209040b0402010e1e0906011b08030405012304110603060f0105 74
    0x42d1030b4961210106658507420301406101902051380301038100702c01000f105001501840362241c2001040d500d5803418400d1110813440e05649400003500725041010000d1030802c17983d007050151103c22000c0040781d0700c8041d03400b8988422103090700341502181003086001d12035071000380c0c000d0203135221001d01c503040000141915070035101141e117980503403040c203814051080003806030402401c00040341c0e090014090b00707a00405101400e43c0748052080405c1e060601d04a400c210341c0b11040d03400382074440c1710204414550303000f0250311030f1904101241c2c0990b0307941166905900141580a5980e89030354800e46080d00410890402400c940c054509450720492070110074103103580d0001d03220020092122055000385414104022251449400300c4003a09440d00c60340c0000720a6540d54490074070350b02408014130010fa0031049242c1c00e210700038050310303031901840c4260300c4142200d0145042114501040d11441d0380010005002d00c2c0540c0508001d01140c0300b07008410031648030300030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 385856366 1250 385855116 385855177
    0xf11100c18060906090b070204020f0a050307020f2b0e03030a0e01080c04051c080705070f05010e040614010507030e04020a171b0a0804020d050601180c080c090105 72
    0x35003440215940c0c850642000d22064407031000742603030380740540000c1c0c9401d03c010050b0800f445005e20103440000d2134015511607804a070303070404504013029502c0050f0721004001e07038002c54400005000d501c0c100002c0c6240401c0d03921421803020f50b010804028208000a0340d01d10380c800206005610080d0086900d0a00141041030400e40300c208403200144000343c40344c20010112116100204000d000326940c0c0e0141842c498030020611140400c0b41ca401c0240c1d100745440a002d901c940103000421300481603601c401e9070000c1e40c4d1455925048000e120544916000301c0d401032448040c00308055201c1d00c05020f91500030701c0d008a60a48810200e812070b4016061180094100700010043e0215060300a801030008004103082042c060200f81142c01940d0401c1c040140400108055648075160391090700c0d001401d5400550f5200c2d80c200011480b0045d0042c0f45003019024105540074034620751140300300e43d01c100c0c0340041c080011a51540181500700e0760659000d0009036203001807 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 385857616 1250 385856366 385856381
    0x702240a1e021e040f030f080f0301031b0b090a0303030506010e12060108010b031501052214150109050a0506031f0801050601020705040209210f0a030c20010f1110 72
    0x10300c001a40c61500c640ca01c00c3c0702d01240c24440c0c0804080200300403400c0c045c2150300132240c2040801c0000d4846241c010380c20700c07030520410310b4400044004010b0241d50b801c0806400010607264035210340c2c422020300b00380605200c442d03000c1c078480750820100b4040d030011540040d052400100e0034036504001002c01c50b044408000503408100144075010007403103010900c6400302c00400c207044580d84100d17101003050080314021851605200240c001e406410101c90190b02810720000070131a82d403000345082102e9144061443e404154500e50040d00208140e41001d44101d22043c100020300c07081d940b02805140c20102c80103c604022048590304d0b030081c3c10048004034075400d20000081c0303405416000715106510411008180b0798807210f00201145d141c1803680da1306002d080e102c40c14610125141540f500418000c0c4042680c05800940d006214800d44808082031042150032039064a80d5070b8049000900403000240c043d0946006580040044900030310103e52020305032400d5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 385858866 1250 385857616 385857671
    0x90a0e01021605030702040b0303090603190f060b130e01080304060c140a0f0b061933090302040e19080f25032303060103020d060302090f040b0702240a 67
    0x201750ba00440c40c0c940188034941d00120021420020058005916484040e080202c0c04095290310079101500d50480c2100080b540001c011056a030b40c05802c40764020700510820070103040c004a107220345040c016042c7da090300019070a007414110705139000d600f0320030700b598095040b03041c42804910400c074010b103051103174110510220036840e0040d003400000c3c140c14800c18401d0603850044461880b8102100d484110782200e4081c4400c00442c9041140c1020415003c00da804c2140503030002d41801c2201e200359000c0140380300c074481c110746511038141c02c0540a24810003030070104612801801d0045501c1801d9850481c58452512150030345103105140324081100303000c241904950100d101194014405109190038002c00030360307100041c0300c9414142e01081711061000164030500207540c1c082e03c11890303414207503100c048045c802c42d01102e038040302e0000107440d00d1000c196140f04803106144a4800c0180841d0011100c43c01400c4102880e80e50b0001e0780c000044030210104802c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 385860116 1250 385858866 385858873
    0x506160c0f0e090109020d020108191406030706090305121b03030f0109050f090c1003200903120708040308090f060d0f150602030d1104050909150109060302090a0e01021605 76
    0xe42410042c80d514000c01802c040e0b407403d802c00c80943c0714145038480c0786a0902e002040c9649088140c4402041042202d0202d8075003401040d42400c19168240200411000c40b05800e6407201c00312050500303404001c00c650490541100c5c03211600010b44a0382c840301c00f0007840c5038610500181b03580c10484900e4a020000b80041003589010b11403160001074440341c0001a10345501455541c00008252030301075030b1014080092280b0039031003204d503501504100500c0400c0c0d41607034412504800340080c4640109244201c3d0840b8030821903102d964080955400d191850304e03004c0603500915403064000400449610040d130b41e542c01020980c0381030000007043c000c02c101c580c04686281402a4260210490920070b8079000020390b8440718507540042606143c1d00490001d90156501664201d082402848244500450300b203101d4101141c0d2080d00c3e0380e0300e221020595220b0f00c0081d4101c204c1002145081d5190703002071481c0300d0700b0030025140508040411252110040060383c8940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 385861366 1250 385860116 385860119
    0x130503120a0e2407030504260f0d1a09070212090303090402040303081506040f0e090f010603150c030c08010314070305190510020901020c091f0f0311040606090506160c0f 75
    0x80311461241c204800e445c0401043c9400c0d0f54406200340c1114510110313a081000d0864032040c11400c48205c904142ca039a80c0b1141080780c0741c0042e0411010540308100318502d0f01e01c050030301a04140c86068503034000d000410716030541b120ba0750b0160346601e8160000300081c48450301d83d0b0000304001c500c2039440b08900e01c1c00078031500407010401e9005104600401c41048581c0e94031040b6070584600c030341100a0ba4030b42d00010340c07501c01d140c41585195401d0040010034880780600080e2041c1d08050240f005410588040f4210b521911501c400701d0101c5005002060024070112030b241c08100072610f581e0b840c1d40303402c0d180c010280d00c0aa001503200442d44200541800278400d8205051015802c0940001c0080e4840006040b418000d6910070b0024001c1400850485010480e40c90000b210f207847e16040f0070034005501080e01c0c50701c0c1456034402941485e03c215401c44007070b640c5001510b420001000069484140381070000036001896001041c02c0c194040c00400c00107282c640c080b03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 385862616 1250 385861366 385861423
    0x601140f0409030203091306030c08010c080903040510140d050a05011a07050303130f08030a150e090606060a030608010f020406030b01020613060b01050f0c0f06130503120a0e 77
    0x2100c210034041c000ca05104402e40040d400200303071540c0000860700031100990f0350340148024401503101620303800351940001186c800650247c100b0315040d540d155403940d03d600541d81e90713208911655130000b91654046a0031403240d400c102c440c01c0c0e203411240c608500042818241d035029101b00c41d02581c0c5100400480b0b08030903c0c284c0340e08100d14080e0526415407222a26800024171080c0081c2050078030104200604a00c1009168007644094a9050902c8120000c1c04c42c0801144e00d48820007021540304100c168582c800c1c09414004c100b150740b08004e0282c650020010003007419110720010506100c21b000707601910020480c0107865078580803001701900d03406102c660540d0408010320480c010401100d003c50f94010f00c01183c6451281c004807214400c940c40120258401f1403001120742d000301e08002c1d801c20b9002107412070f072074804040482c44030705070000740325a10810000312800303004080b4582c800300040d00011203c00d00c81c4c1e41d07400d103404643c2170b0810090303114050b0f072803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 385863866 1250 385862616 385862629
    0x5100503160b040e1312031a0405040803190209030109140111090109091808030a0228020a03080405071215050a02270a0f0b090103060801091a0702030c060114 70
    0x8801200034841501d41110780d090b0740300343d0252101c0031515100203400303101406a80104076a00124858400404640080007803440502c158500c503440920f44003d46000c0c0202c1c0c0c0219048400302e40b86403079100c5a64540c400710717107100b12600d40a010044556a00303108641505004441801014054030101421100f0300c01454261441c280b040854503680480c0b0b400c00c0e0381200c040000d4138001071034481c4690b04010801054200300104218100e106034001c1d040740507440c07080d00e1542c0c0c4008103003522841103014440051340100901f070040ba1088400c16045030190f01070301d034003d45612001c4006002c0040030b480003142030800a40003001da120381035020b1500c0000318200301e400d0040550390b800580d0380324124100070380101403959424040100800101e40d034a40300d01d90314505800c00303802200c0c200740820300d002e01c00601828180a240c1c07089900c20b0007010031021b2400d0108900740080c149804610083c018140500c200300f01481c0a0404051010303035400a0a04000e03c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 385865116 1250 385863866 385863883
    0x11e030e1b041b020c1012110d0e07080309240408060601020d08070801030201030207030e0d0c1a0f0405040504231005062e230408151303030f02090405100503 70
    0x4140684080d400f03400399002c91043c070b40070b00c00c0312170442000296404039400c540c4042c0d401019407a1101000b6100074101c02886d41c14034403803051205c81c4042540c56100d0349a03104010041d0020059007001c0c2c5084c000c4120000000050001d00c0d40a1217003000c020f41140c3c005421035400101406806d6804001e02c011050052401d41704078503041c0340086c61101f040c07000030306164000c1581c608050143c80d958070b05501c00307032140c4005a118200007114460310310502c244a5000704803400c03020900821140320a8540034007d1a03c0d1418048c84000c01c1c0084c005c3c1d0711329072402201c0c003040074410404044140741c2c00007484607000a01d500d0045036400350800307200d0603800c5080c5070640c1e0006c40342183c3c3d042181540304151005c25007510304020255400350100c2030080c5140703000c40d510015006440d01002119080c8102c11480103101d0000e0b50310700d42c3d4814015583c400684641c2080c510014000b10240c10540500301090546a09a400b001230008210090015080403c510311 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 385866366 1250 385865116 385865141
    0x2070f050c04061a04050112021b070303030c0201060b03180106050a0e040606090b1c0c05031f0509010c021b01020a06090501091719140c0304080f011109011e030e1b04 74
    0x10b81028014130400c081d403140d48160780c113000c00d1a114510300a49941a2403540c05d101c0001c044500c031140c40304d6110b031180c1c0001c50100e40b400c518160340901c1407080e00d00303460f0901402450f60316910607420900c2181c1182d4100d641d29010007140903102e845519000f001c0e440f1f03e0307444d02d01b0a40b400a040c2c0361250010b03000b441c40e02a020341e85503102c1541300e110003408e081d0518041c2c090709000c1844203180d00004d030075106285411068403001c0e20380040389001c05608102c1525505009401e0315a0b10000350f0060340010300300d0501101c2c0c8400740d11846414011180a60450354a550907902545002d6405035920011030302400885134446072020200300640d85044d1004444250401030660003004100f60410040d022040d07210840d585510030108582c2c0f1651781d480fa0a03541c1f01c124402030110750a0051040d041c0b0f01ca0025a560040145c50f9903004825000c011403031070308a02802000c0507103442c08020140c1040c49418210759451040b444090207a000780029560086000c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 385867616 1250 385866366 385866389
    0x40f060e0d030f110406111005090f0106050d0f03050f1303210c03210b04020304050303011e05060301090f1b05190c02150a0c1e02010f02010203070e1302070f050c0406 74
    0x50980360500049501b520f0f03003400e01c4114041d01006181c035010380c0041c103ca5051408051042980d000502590440880402801070a498000384441103030310100003003810a1240c00c1d0000070f0700400c0602000c100e42d8201d02d007040302c52034007841d00007050f6106031111035281c030252280305e0a00c00c4900d07003465035003010403456540d56002008051101184d5041e9500c2d030030340859241c0590032007440307100c00402c255200d040a040047e04c0303904c00e224620901000b91000000d0540306800d2004940b8005d140340c3c02e40e0b280c1a44803014180495011960641d581c0c1d0500103511181401403280040381c0c0c0d0142c480b0b00c0c1d030031502894080b0806403000e000c0c688803c540143c0d600400070002e0080c0380019602c401c0c034500180c5405034541802031846000551036100014003002c0010254000d0313840c1c80f041140c1d40f00603400c0748002e45100300014001920301d43e06080c02110240560900400145000f00944850000c0e02ca07180040b02c0642002d801714440c1d14083c004c4002030074882021 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 385868866 1250 385867616 385867631
    0x30f1d030709152706150804021c0b0f0405120711100314010b07020307060804020108281509050108070f0306050a061d0603010f0608070e040f060e0d030f 68
    0x60766403001449014420b80d118400b01528050300396202000b408503800c51003e002412030012600b07213a00307105089075490441c2c00240c0701c003d178040340302540d841d4594110680341c540174004107401c5150348052100701444084001a100d4013514403d00c040a08880b540c02d017403500c0f9007080142400548100014071505c8041480c0f6005260703000700455290040300030f221020b9020302282c41c40707506240501c0000069500b034038401030120a10031000d03202003640320041900c80c00c60a0324042d0000340d000001800a815441200f4a15600805600150134000d40124261503504281c40b00021300248208251822401254003602541c1c024010721402d15425502c0c4000511010780b02540300c0c00411000031641e40716a02038000c0d914624a800d4400c640c1c4c000340c900540700580a980b034aa214a40c0b501d451140e05d0a4580c0384000d40708052400404007200040a442514403c800220003030004035503104000c07601c05c50401800700b02400703407800750440b110142d110140f281031001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 385870116 1250 385868866 385868869
    0xf0318052218080c070803031504051e07050706150b0a080a021c061401180b0703140a02061f0609060f020f0115050f0a03021509011b030f1d 62
    0xc000e803001041c40c01522000d960509403a000d040701000e40075101040351554418409020700810001901030200c50394140e45448060b5a80300c1161200701400d012001161285082e8000c581c028425035074010b4103010385d0403501000d800a440202c0800c000041ca0410022280161000342d40c0c0d115a10342c3c8585880d000b440d00703108401d69101085100e200280c10404e241c2c0c19110f10414009040c00c0180b020740300c2c0c00c01403c984c050b114000c0103441c0714003150b40c4280c60960540010a440300c3c0000d25003449240c058101d40011410700103403801c0f0b4421080104e01030046d54400c0da00802807414102c0c0c840b000940b4102030ba5032001010381c0107201458200f41c0550888900d450080303a484420315049092401d14510f20645500705058880c58411440d43e40040c1d5070201e407451044080841000005030080c17000940243c1840880c407011130b40480a810710f00418108800010381c5004245245a88602c04402007440120004681c0c0d40c8600058110409140080b008003405030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 385871366 1250 385870116 385870129
    0xd05070b0c031e070203030403080903090d1106041703090108060d050c0108180a0515100509010e070c050708010603050c2b021906050d1503080403030c0501180f031805 74
    0x74500001c0356000004a03240f414944091440340140c5003140e49642130041d0000c6d180c0d841520141c2c00680d403140410884070000c021140300b11340003018030400c180c03642d4035005070b0303244040c0d05580309800307000c00200f00b210707480c2214000034200302840c0e40341509000505650000b400d1140185c20b403080d250001040003400c0d4040d050242000142a9150a10306041d4809960300090030301461124100300000040e028895440e40c402590443c0e40b42c40c28550348e075030984913940d80300100000410180404064240e00721503140b1f002d256041440c0c40d02031814059a101c1e84c05d0ba99208010801d00c1400d0100d048540400c4500500302118003030f88002c1c410421400c02d000c80d82e68500c3c04119a203e203161361031110080c00d5107804595031038000c0c100c0d8001c1c00e0321009007414281c041d064200350085a605a0360f000f8540d90074181980c40c109d800c200d145104864966132015100451030b40d80c01840e028a00c20b80849545482920700200390401c42100030a00d2040c0402c284a00d64485 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 385872616 1250 385871366 385871371
    0x31d16090b0406030602280e0112150b0408061603021204060e0c031e070807060f0f0909090f030e0901060807030b1306060206010627030201030c0302130b03090d05070b 74
    0x80d408540084098002402040c070b80e80024030540c030000f51030301d240c101001d40d9100740b07444590351000507841c48001c0c3c0300e540080807002d0000340051182d9032079400a80c0318006038070300f4a0f406060349498042c6510304c0c1d4481d4200030305d1640041d081204051394010a201420380e1440c0035420402480606000714501030401401591940c1071b01c030464074200304600443c28014111030340182080c0091003201ca406003c59418042e0f0300d404141d4100000d40b20046403500c0d070f01c110040c2190b03c011294291003082c010f0030444a00400128502c0c1401030740780582c0100300c281008180f610f005000f0040d00c1c0c440901509800740108840b50b0031040c020b17800303001e80c100428008101c60008102c1005540039840d07180c5455004122642d000965030b0580d03007181c4540361141803881100b880d02038031100300302c080c62242ca014401548280c0220710502440e00b405418483d00c10380410303208000790840440ba010100400a40c08010000d840d074000c45414098034010003a21140d1003000c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 385873866 1250 385872616 385872629
    0x10b0c0307030e010e0a090e1b061e160501020d0e0f0c28080c0906010507050c013507030f020703120b030a1514160507030f0203090d03031d16 63
    0x540760f101603070740512201503040c80c0080521302850b44501b1108010403c02181c084135101d02c15004c1100703541702102000c4004020610390074201144541441c03080550351404443d03500303024418500100c40b0001140324803c000158480e07000c80414002c44091001009496115180072000008041800e0305803500969810841c5540c000c25822211700b003080c2102d9a43e000540051205c0c0e0214540f055140c0842d000c03040da40780e020044800b0300031b1850241c0035401c080384140b030720742c0103500c0e460103100d03800104803a0045544034481449951384c010700f03100404804001c0e02a40c14800c1d49024031b009a401c605001040d00d005148140d00341000514071760310311030707520280e40410903410b07007551218400c80902015060328001e0701a0b0010f44844081031008614041c14588101104420070780c1c3c1d003800d00d4442d1318121500d08034403000b01d0550004210307607501c80d221004010b034064001d031404540c4a148001a62071039092800b50b41250300904d5040c4540c1c4001440042241c03903 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 385875116 1250 385873866 385873877
    0x510030f0b0907120b040b100f0b03090a140d14030c0a0c0804050411130b040e04020415170304080f0106080303180f0a24090236010905010e010b0c030703 68
    0x4a04407078038070f400010703003241c61008078083c803420030452074054541c0304910540d1464042d8984810010b01c00c000c500814070108030f000c0007805400742400283d03038400c90103c111094a040c90b101c0d000905441c0c0108142a0404440810301d42c2e0000c210324040c0b80c01904030340c80c40c0303480c0b4004101c3d40110ba071001c1c20810344128140512409100f9a005468010301c20080100d00c01c80e00d100030b03806040502d020081241d40085c44901020990701140c01003440841c0c1e503543d0360f08210040429006800c0e504811380400301d180304c800300132001c010303407a01c1c0256551402e0500c4145403420201c0c2d0100d80342e05102050140b0540801500c0d0000d1960005041803036001c1581804d24030081d5201d03202c0c1c46007100641c1480070000f0b00495a40740b175510b40094903c485801d505403094107034040e401a94408807143c0480241c01406030340000b50740420070003d840201e4030701e207410a900c080441625030340144a040040c10320680180080110540b40c40b40440380580c49010f0340b00003600b40b28 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 385876366 1250 385875116 385875121
    0x201051506162a0503060903040315110c0d030605010e03062e08031801110a02030d08090c0303120601090f081f11030703290a0302040b06120a050405010510030f0b 72
    0x3645043c0909016009200307182c00405841c80243e40c0c00444c07003003e100e03200d0354011039810070b0040704072025a9041004a00c036440007601d1b85028000c0c81ca40c81c0400082080592841c2c030090090381c40e040031595000c1280c41c60000010024805450350328800d0b041034040c41704a48903d03031204104200c15010801491002007010142070199001c2c012034000007035900389440d64540e6803001a03400342c84040242c8805803000d41e9482c01c1600080d01a0b00c08884c1d011404c0c001d0388441e611a9460089456000b00e40740030900b10780020030081905c024400a01489680000400000d0240ea01e0100b2550b803400c04000d66441110001c542c46a062580d0007800c4411601b003540c1c0a030045810b16501d00b012040140103124030580280ca81c04030100d550300c0d03070011103500300c503999000b09007a805505607000c0000414ac60002c1a03806a82008810059070f8510440d40c85180d480d00002914600b904080342544c00c01402d42404a0074404240300003040703030f403040214640018200074a40e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 385877616 1250 385876366 385876373
    0x1e0b22060e01020f0403120f03111204020301110a05031005150d051510020a060f1505040e0a0f0308040501060503030301030201050a1803050f03040306113604021207020105150616 79
    0x244a05019801e004800017404401c2c008003102c00107120000360b40d4000800b4290a0071800c0f06c007650700c001002d010070045400300081003090250854002000014002a070804054070790780703e84250740205c1e034040b0804c03d00301c007140c103441d0052a0984140c0d12001c080055400ca902c07649101c080004c0e40d56020428800c00d00711181e00040e0003802d0702075081d0402350040d50b140100c80c0221080360410384101c00014241c050040d0a00c0340401286440341401e00308006400c03100385207800c40c461203441e0004550340710032004099000ea03c030020b440c00d01d800d025003514482d8201600a5104000402c0142d80c0310040340e21540c0d282c5007400552000300c1d1400591755448e4005031451189201e4040c07101c50110041c4100c03441110100f04002d11207101400c103010700100c05620b07001740a480f00464400070303010121100d103074402d05542c0303a03d100002c04a81200d200c0c1c005103c505c00402640a030244500d1b600014040c0e00c111120b2078030400a503444c4500c0c9103014080b400e2240c0203040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 385878866 1250 385877616 385877621
    0x3070b060d03260609090d090b0a02010f1505030d05070c03140a0c06031e060308030103022206080102090a082d070803071209051f0e06071e0b22060e01 67
    0x303c4200c240610816283c0f6400c0895020090380d0380740c403a09606010031040355001408003c00c4825480705442c81d40f40ca2039601054000d03c0030340055540399504d2a240d50311381e00c100c01502948002202405040105062034008107043e68401d02804006260100340c118084a04172580031180c1202c08404418103402c01c242014000e01004d01c412022805a0700340e0450b402084240324039210010b02070501d0801d488043c4006402c0043c2040188098103150554801c07141030a490300c4425190584500e0444089501c0441165401f00d1403103010302e8004045001400c002008002c0c04803d8508010740c54408000005942c0444100c0e170141e40c010b2111200809001040e00d465800c80d0801c41902482c2c200c036400028400c500c08605850102054261000b41d0070300d050301010b1500c400d588005400480380c0d80400d060003480c001602d10034550580052081c0c503602004c4c4649405103506002a20a08041c80d0410700744002400764000c44c405950018000710701102100c44c03c900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 385880116 1250 385878866 385878887
    0x7020a03080d0507080a0c0804020904020301090b0f06041a1f09150c0b180a031115070216050102060903120606070b1303090803071211070f151103070b060d03 70
    0x714040c0030031010b03015105540400e01c40d0010340c0f00c0321500d582d008120411514166480c00202c0c08100116001d0300b891a10385601500c050000100c4e1401621000c00b05107003120140c3c40c203a441020012181014003550320b403d104050f03c000c0c850681c800080502100da000805440c00400d0911205e612500307480c4020040c50703154500002106100402a004c06402a83d00b806c00b03201080b200d00b28807944288284c14032010305603810555801710b070030b00c6100c02403000501c20403035038864000b03000341c14500980755a001080d02d01031036500d0681310030783d0350302c99030554000504000c2c3d06040402104c02c01c0c41031400000469460000280c03050051100c003030440400700c0d08002c0c500701c07103815001210b4004d880d0049901e507074461240e9240300e1100c1c014800f4074024000f00e01140030f16500028400c1500c2039641c12504c0d03240801c0c500c1d1955200d0007800342e180c20364003087c0342c000402c11320407003290000d0f500d400042e480b041d10721000a00014081c3d00741d446014140340c810054501c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 385881366 1250 385880116 385880123
    0x7050903010f0c020a1a070921020916080a1a13180501020a090f060c080702060c010c0e1e15130909081207031802040b0102030f03102402070b07020a03 67
    0x210020f90088002e682c1c00150342c08440083d84c01c0d050441440110710103601c03500c3c1035920b011005040c501c0002c4019903a80305d032148101c1c1380740004011b07a01c887c02c01d407103110784100b4503026100c11b1100404000002d8070300401e0f02c0ca004003044850b03100843d20f941c40101950408558040c2c80031503401008030424945600d0b20f1414030004003e019001814400e1480e0f54028103180c4818102c0ca510400f48600c20104848080e18800503002d00c01070700f40e45000a0080382003030b01b134015507400e40d002030403204000b0f902031031240d61501d00b4207104c0d05541130507840754940c15006e201098155031000210a641100400c0c80d400407c440d41515001d009030800c1486185850b03e001c80081d0405444594004001d80000c1d00881c03081c4a6541d4161078038246120320031841c1c00f03110041580015aa0460008020214195295000640c090140d1603200b001035440c080542d2170101c400f416070420072481c0c2c01d24241701540058060203450340f002183d9038500c81840003816140d101e5000a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 385882616 1250 385881366 385881371
    0x1303271401020609031303110f0303030411090112021309020d0f062a0e04050c041d010302040b2205091f02030a060906050312030a0204030f0c03050f0105010e07050903010f 76
    0x85a40d400405450800480c01c0e000c9803060345403640d03500d40320f0040410003c5003e0202008001080d2000010300140350050203203100418a10046070641e40202c03015250407103148080b8203181001d1030818010041c2100e21501c445155001415138519003141340d800a80b203211003c15940c03407040503486181e00c110354246400c0a854844080d20007a00d813440b00b4407800040d10350009484400400d50b1030305a40380761400343c42c4420400108000b50108035583e10032700007c0b07400210b40d2003416010b0b254082035150b40d8910300c104026201d0301c84009000c0c8110068100324060840040c0404c8481c03503001181c0740d50356003e0700d8508000c201800310785498483c0060f82c500c06582c0114021001e0300340a000142d1a1002501502c116109842c0c16501600e01424811100c2d4040d6801090003c03000d4680b84e580d40320741000349a5080c080e034054a84200c208100300303040007590b071155a40e800901007589014001018054010215401c2c44800180c0420f1942d0a5004200700c0d0500c2c0807c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 385883866 1250 385882616 385882619
    0xa020d06120c0501090e0703090309050a0b040f0f03020904022704150e060912130306090305090a0603110406030c03090b041b0602030c120f0418021c0203130327 71
    0x241c040100c490400c2d15921250000440c3d15403007488002e05640820080b2480e90319000402c0f4010305100b030b000d600f0045100c20110315507891103040002000c54540481e212400c00360413071a003044d5036000750b05211842e20108016107072000300307590194045480036000d1400301072104d10b040c449001504c148581c8000c000401c092249901030002c507a01d010840e0712200c2c90b03030300e030f90300d40a9821140c1580008410060904080010001004046021a0200e40d00e030b58840a44a10400440c080341000c034907185581081060000149074902d002e014800140da100c0c0d01500c118014a010941c450740d202c54424000d40000c08483e42c0100c9000a9141030300f4801c8226681d0b158140780095403110014007140700109039001c40491001824038902c170b400030010300f54003a0b10304d01001c000c03c0c40001142020001204011003550801607507480c400c2c03800c0c450702c0d0403402200780b03424418414041d81c03400b1030100d40031840c0d0500b07081504002201c02c1240741543e00c014010410032440c030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 385885116 1250 385883866 385883879
    0xb130b010c0f0b15040b0120010b12012a0f0f030b19080d0302120105120a08030f0a060603060e0a240b07050c04090314130b1801090f080a06050a020d06 67
    0x1850300c0b402030007104ea41070500303140800051342e009043d1b00b400260390100398000d003e80001080da1130310700c100000400c0c10b43e460126081c0c0701c071040362802c0b6035590100b041c461862240f00d01c040381058007406c400c90030040c10144c011114806218100140e00f040f80300882d0181d03000107030f01070700206201140c1c1401c0d500320550040500405c13580c1d00442c1000c540081c003c1c020b40e1011412080191035a84c01c190038007508162005103a042840351041c044003140759600114000c0421481d14013162070605040401d55916500c4803040505c3c0010403c070126030000309a0700038031071510200b1030b035540f413104000010464400c01c46500d0002c000203401c208902c001d12180380725605031055014230000300411105800e05c05404510420b41812440d02c20704010012040a5680d8808282d00d640590b0001d40010070901d02041d00451803110f1580c0040f02da40040c80b01c03040d50582107041110076500c64041a10003008161543c0210755022440c0e01650380e03e001280c0708010441d902c40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 385886366 1250 385885116 385885133
    0x30f0d0b1302031009050402060f0a050a030507091d0901091e061505150c0a1e02030f0708100c020703150501030b16080117031201080304180b130b010c0f 68
    0x1030462140c811000c1c9410140355034026244502e0304070400d141c4552500248a0103000002c00490b40a03c040200d499414060b102a00e0403882d550380b07103901d0710080304003e002c075035002d8a07410510101c0c1c00c041100b075916103c0a125083c20071002d0200f91200f42c0110301400c1204d1008041c8004514104c500e80d001c41c0d20851103034081e0030148106410b020480003c3c0c6d083d4007800341c00c680101002130030021000010301c0b070240020126101c012450701c071600ac140ca45e4421031000710108289400b0b5250400c502469a02e4040152203100c0c0784c0b9100e26a0352031b542c050500426124046644024021b00440e001160082013101210580b03808080080100340021103003040d0b040041591064903102103654200343d41c40c0c194140e400c010101c200000055103400303462004126002c00c80c009070030340e14024941c1b5001561110f0601903001c0c0b20088000e680b919051403c01c014480b65104000941c584065010000c1c0200031b5400488200e04200c90180c0248400070201c820890f140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 385887616 1250 385886366 385886381
    0x180c020a052a0f0d020105090102120706050609090607270302060418110c030901201605030c0409241506020a12031e0f1803110d08060a0603050405030f0d 68
    0x3030b146802040780401c00c41100010000c054015441e48058030065020f1001003594000c1401207900c012507030f0b41510f417190300c41c3c602103c8007925007061010500305400c45a070011984000342c0503510b420000100848442c24075909604007004104800c04c0344035540c00061500904030507982c60320342804950240412041501491810081c003010340014420303110307808a118041e502d4220070400440d1492041c4940340300030091491821308600b070030080250b040303041d0050f4824461406040608000300264100e0095080220610015000c180100703044081c0442e4a0003500352084500014030324080c0049412081c20004500280c001441401c01403041c0048040511507140803816a40b071170040d800e0480311110080c2e0040d030f807504080c910200952000881d9280002c408603165154034041c0c0104000809503028510709010b0410120303014100010f0b10b042100100711440d0240c8a11803c141d130300c0010038104542032003182c018045c07840c0e1894448440880540080058 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 385888866 1250 385887616 385887673
    0x409050303010e060d03050f0f0d06060c02130b21010f020a111002120a0b1206011806090e0a02100912032c150702010e060304030504080708030301180c020a05 70
    0x800010744902d07104c407400040c0303541035985500300058a4028080c8d5000404002c04c0003109201040703901703c0b41c1c0310701401003c41d030fa18064400c80600510050710302036a0307004103c0d4241810050181c5401d0a40d03406c02021300d800d0302c0952000075042c5d005007161110003400354000070b5030040107680706040607040d05981007606d044011140644049102e1000c9000c82c4054074800a00103a84a42c00804104070180440910010f501402c60030048249c00c610104000d0103140382e02c1c000188680b5000c0d00102c9810088050818142691802103405c020f20a41112a401902500c0f88007000000c0c01c4500284c52840054600503103082541c44e0440e800a038014100320801d161604502800740c009410f51090302c540341d1104080394002c0c50280d040c051003030102021034444034000c500c910f00907651140c68a040c0b11560707041012542c0881800d52040c00184841d01100068003070aa4503800c1c00608038030002c5c400e90601999080c080c2107401008150540014101c0010035070245 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 385890116 1250 385888866 385888889
    0x702090f0708070e0a0614160b0106110318040903090f0803281e02150108030706110a08150a050402160501060504110712020c19090c080105010e1e040905030301 71
    0x1e0f84001283c552110058459000c1c3d00b05400b080154003800d0320f401c24440f2044010302c0c105080303c01c0111130507020b1b0100e555004a00040000c070350300a036515401c16a05d00a5071420240603200c0300c00c201050f025601c110b40d00c6c507440c070070580034000c620018125011020710301d59490006980301c1c0c014100d40d1910b4000080481d8805c445652120880351103902c0310358504040c1d8640700c07200e9034509445400e5116500c1030340600303100d00300c40c54020100d98005580e90440303403410030103803261010a0b2032681824442545080c0d00401c080b941303c100760403d07440108080c40060352514041c0c0c0711039041440017442520555111041190481c0a40b00900c0595900c0c000d1004071840c0d07403040004810144100c40000e4050140000040c0d45841210f0b030b0300c00c41b00c0c006540d007081c0120b40a4400b482001c200410b00c061702030038003a4003c1e818460200d6151a00191500b0040784d6060320440303600741e0007244000280c94880440d400584204203101d1140f801607502d51083c0600b000740308 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 385891366 1250 385890116 385890121
    0x10c0f0305040203061614070b01050307060c0b19090602030c070b01080f100e0a050f0604120f080103060f0905010f0218120c09090c0907120c02010b011e02030702090f0708 76
    0x103019006107806242e014005040d251340b401820245c2813041d900120801044403400b903450a12100a409900c1c0200b402d2131465143c4000c252070728007203038030a5051205d0401801c000c039603040a940e0f80056481155203d0744000118040140890a0300504951020081c803000d108100081d100091040e84140320030f0341c845d2f031010b640e910401c00d8142e0b07950000c5005071140c04190040241e0b401c000c4101e5440a0043e513489040903982c1170450b0b03996018400304000d1203000641503d80c10000d041028032481d0f0142c006004a4050001504981e1500b06820003103140323a110f9010303c1c0e0400020081c3d016082d1200000e91300000704c14409070540718403142d091802010f426a500c940c5401080880c1500c001d00c0800b40c4014000c07400703130080030100a855215050440c1c490442c2d5982d600301e01c0d66000c2554112080403500a00310380c504510b21403566048440d9511034402c0d5800c0103003280706040704914500c6003180083d085a440d070103110804151411190107005240c03a05e401e41ea = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 385892616 1250 385891366 385891397
    0x6050406030e0c03060105220507030c081006023a02070503070501030b0a0e061903032f1509160b130e040c0b0a0e06070302060714040e1b090307030302010c 69
    0x994150f00350544c90f0b00040010030161521480d018841c41c087c0c207407000c13901e03580e040c2a011641c0454061000c2910b600114560650189510b079004c1d0f1212020701d0502d060400007955501e00c07840c03131080803103192108403600e002040c0c0b6a028200aa214281454031b8440c000c0d100ea00e0b51040500900c500c00d40402d81e1b600a001c5c1400000713002c0c00e5405520701d0b1014010071030b0380180409400c0b51159803501a2010380a603a000954002e486949003804001c01c1100e812003060708484201c112500178811010b00810b42c04000424214244665110710320f0311424206284203030400c5c0d1310300d1000020030071000406400310001c4141503035180c1c1d5072407205a5000300200e800501ba05080c81050110030050805020340e0740300b603d040294400d400c0003040c101d52040d24168090f81c8800e082249080c1d00180c0b03a4082e80074480c81500342803410458100c44031000c0e08040056400442c42e0b451525a40e0980ea01c4020043c01c441440f07641c0d05019000b03000c882d50741c0c00007644e20344484041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 385893866 1250 385892616 385892623
    0x30e1002010e100b0d0b070801031a060d030804020a050d0c0807240507030203090603070e0a140f0105030a1814010e010204152106091401051008040308070903050706050406030e 78
    0x104010300003d400018507180404000748681c400195002881d0401000070501c200a551311410054492881035415400d0410003181841c130001354900c0002c0130032030b140c0c403403111010302030b607060800d0381c21a00d552000580151a9800c02c1d500030240d00401c0c4240502c001a060481e2081380548901076114558800c203810420b0803601818a15803551083e80d10450040c201c26000c4e106803401d005130200010559841500c00720006290101481d96928003094102c00502c901c81100c0303522100e1501203003041d03840b140741e2414040c011000403404001600080e10742100030510340c002540d0742c5007010800c0c4081090130b00d550310307109011110640c14400c42e8190342c62281040c407000e68450707048400381307511b0074004221720404407040701d86121760180c103015004401010170180b494406504404005901151044003003844803240701d074000c1200f0b608150580b4040c1c1803a0794a034070a40700540c0c2075000070300c280310703650b00020820703484030191040c0d91070b542d001e204030600500c24503507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 385895116 1250 385893866 385893881
    0x31116200904170d18050d0f080106030e03090312071520031f0803090f0609090a090f15090b06030303040507061b060e0102091908060109200304030e100201 69
    0x420501c40c0010501240b070360549100400844505503280403201031051041d9480340882c814180f824201c254208141131107100c22411141ca050f0048404196000301046c42c18410311003490740e41c10b240003410324140101c2d00d01600c06403c8610901c0403506020301507124003400e075140521422241c0000c6854010602e0502c1c0b80d07038400000610b094103804246c0d0010340003086a121603241d60380030350447c039003610042420401440d1188076041c24441c40814209000b0b2041c001000400c0d02c585c4c030b2140a94001103507143c0090080703010300c0c252200110f842c40203000010070120300046000141c1003480d0592040d000c801180d115582410394900094500034141e804c000f0080c002c07203205220071071006200501c0c58075003010f940c0710b0904846401c1c0d90301c50680d400060544240c1000001d02142d40030001f40101d926260074201c1c0d8481d801030091900343ca0312220104a42680510340103002d4540c0b10314180d9a08042ca00a007070b1a42031920103005959596442820070f00600c10040c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 385896366 1250 385895116 385895119
    0x1204110a03030c080a0c1a01050405071812082a0d0906080402010e0312130f080601030302030d0908041d040614070504060c080c0109050706032004060c020103111620 73
    0x4048050a99038684e580d080317801031904000081d602c00000c81d04e00000081c0e442480850703c201541008140000e03500d0041081007071090890000340d030144d60700001d43c211100e000c450104c041c0f16140680e150700c10900c0c0d010340001c840d060b0000c041441134040118460f400c00f1500207441690081e50811082c0c8240c01c0030544030400a4095402280780c541128401070070303600070049d0101186001e4004400d6002e44100658060007080c6100d07041c0406410341c0d42c02441c4940c550b49c0c0c002d580740f151040420fa410785039603038402001250000d0f1006040e070000d03400b01c131030f01b58003c0c441103000803a41a200c031070408981c020200c3c1122009030140001d41d685070724240c1040c2050307440740c400160455a00e02c1c10001007138071410038072030803030194461030180c40081d1502d200102038503080d80d01c491184241030070111049803442e084902300d4103182400207c1940f20300060f801404d400c140503a050b58009001916401a05006480144125845c1c00000300012601140b247c0c03e000b0745 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 385897616 1250 385896366 385896377
    0x3210f030605180a090206180405010504060e011502150a0b041a130213080a1115090a031104020d0603080309070617010501140705010e061527090a081204110a0303 72
    0xc0410f00c140c0c1e07070b0780105070f40030114502ca0a13502283c100e0b032080030104030301e65a4101c9281c0b10f1030503005031401403000321020b1041c14145015144404c4041c4240d1148400412130454108d000f8000044900350705408031003030340f4100c80c0e6540904200001300c0d1281d884c21041146c10109109450101c41000e171411a1912404525000075031040b40441003400c004080080c9020301004070020140c401c501210204440005210b801c401d1460b904501d4403060001c01c2d1691a035080450407245c01c40c4010602c0040b64000c0b50080c07060740c1c0c00c5000b01e42880404024408032100950007902404201c4201c1030352250220b81c14820881c07142c0b224442c0a004100307540c0710310b01c01c3c4441418a0485031070f00c110b1303603034050031a10203c0046400c0c1d009441013202c002c0c03501c100c0708416602a40c0707080b031841030030303082d56004030002c400489210100000b00e079004400300040c6040c1603006890b15a1400d0b0301050440000381181d046400481c05d4159100c1828820042030459034541ca46 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 385898866 1250 385897616 385897639
    0x2407120c02120c0f060408071106040b220816060f05070203250b0310060e10050a2114010e0702010c05070609030302090a0e0f070e0a061803210f030605 67
    0x102000c1c1d48980350f081d07510b1007440c00e841206001800340f28003032841180c00d41c0c6d40300780c00c0c60418185032040c100c140c4150b005210810011000b072048a800f000c00c1c0a00310030800420104001d030111640115040b4841d41d81d9540c440c0c17950340c0f010000d9454a80301c10f03407c101c40c030404a806204400c0006d4154211031044850100000c0c0e86030b0a04c1c0000740e1001a4070b880d01c4187e00c1e0341d0800c60b180704440100c2c200410605801c070410070540350b001d480100d940469030030b001c0d0561188444c1c1c44104000114807104021940700c401c184407089980c02c0c848040e4030594051410b80038001c10402d405080045184070380144100a040f00300d81e2030709410301354140c54030001041d801b2819428190200610a2181d031540075800103440d00991540c982d052980d8404504100100488284210308481078460b03901d0301c101e201100c0e01460000714004203004034202544c0507501c002e1420358180b440d03039065000000c01000b8019140c0c0c51114554107000201c0a68a0922510780c000341c20100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 385900116 1250 385898866 385898893
    0x70306150512100812040f091a060304020a030b13050c030a02030a0b1306090b040501050a062402120d0e190c051e0a030507051509030712052407120c02 67
    0xd4607038042c4642030380c15401e031395542d411070600751482d17048100380400180600529640f402c62030050080840d08008070b8070001c0309200400f14807101148a1940880007404540d40d400006010f10742c000c41c050700d103080001c2052310645007218100c2d01402074a64446940c01c00140d0a15000c1c0c004008204d00851519050700b100c00c003400620840c1c81452207140810700c030b4065442810b100e0940c100383d42c58142002402c581024107807200f4141028020014808480030301130000000484501100d180ca040a91801610a52a900801d40428201a031a183d540200c1e81d10429605940700120015084401800c00b200b0040002d18180c0081c4042d0400c814862086444a8040c80810203c80002440784110f540300300c50a41c000c0901380010f04068012006004061010500303040e0003400180e208e5070b507402146c0800041030a0034040c0a000c0001c0300f00c0700780000c071801c80140301050b05500324004869120214408040c854034407141440345032002040b9a0250100380620030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 385901366 1250 385900116 385900147
    0xb0c031204050708030c060a0e030c0a02060f092707080c03070c020109170d02120c0c060d1107060614010f020a0b04020310140402030c0d0510020913060305060703061505 75
    0x60060b280c520a040d00411980800c100915072030030003c0003000300d842e084514400ba40c200c1a0701e480d50f1341050018141d030b20070014200d0740803941203884946540c001d135644440c078092040d0391580b064a07407e82c0d69840b80d0b9406280c284824584003180d941c0d41d03c3d1003d4414481c16221800300f1001040065030b9030f403250801e00090340c030516040c29420340d50480c0c0e8082c14a00204034169400852400390b05c940c040184a10f8001c001e21444d09000d0302003074442d00c2c0c184180c1c05c0c40c0103180000318800049415405101d00c0c040248a883e00c031036580c142440200b03018002c0c602100314280144000b50b0060040301d100c180a503004216952280e91244601403024104030707014881d980c00502d03070880038002c441c0031844c0c0b104080024502030042500d07007078017101c0716400303240b0250f4484040b030000328074116081e010040160f40c44901d80007003104403da02540f02c9070b191816802100700722012408034002d040980d0f092010355201c01108940300d0522485c0c20100304d0400c44650500f2a80 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 385902616 1250 385901366 385901371
    0x705031602010605060a05030603070e060102030a2102300c0412021809160e04030503010e04111507060e0714040905010e070f030311060601020a0f1121070b0c0312 72
    0x348004560a0380c4c8038081422504007180c0d0078085040441004142d0a0800c40c24000701440e02c0c280701c190030110000f0352a0300c2026005400c1120200d140311011240c905040d0442207511401c66495242800704401106103080c036041c0c084280c000c0418903030030b01e5a1107010b012400801ca240c18644200740e44030301c00210040360484100410203894403450f8011b07500c41d14200d000b400341803495000c805000c07050364021b02c041c0c2210707001b030001080d0f200c0240c0e03054883c40c01d8002015113883c00d15403c080c2400445540c0060104004080b142d2010042c0c01d6641c4180d00902003841140d805940794103403800b07400802007001000c0802840c043d044607079514050790000a40609001c5034506040031a00300a038031a0500908100301940b02d150041030b00c503100080d041c18104600000c2d186c84440e44050300c40b03403418248a0038405c4040810710050001007007070a500c003584043d04040031b10340320605114022400c0000360f04040d44102d440f1003030b100b80a1890580403c1c1c0e5051181c1c4003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 385903866 1250 385902616 385902661
    0x110712022b05210103060609140f07030e0703050102040f05040f1a01030b0f0301050907050108090312070c080f130312050c1509010e1203060307050109050105030a050903090406120614070503 84
    0x24641040c010103c2c8900c05000e1801031001195060130408210b090311102502e0004d070307403609800c0084600110182c642c200120307140c081030188080c01c1e000d241500c0b41c0c1006d8003651000400044082c204400382c411100151001e000412400c0c02020444404038aa1902c5400080c0c5195040d0710941c8140707800c42d8001e1448034019980f0001c030b421240100c030b24007590751042009000340e68103c0310650344022090020352605004404440e49040090302c04800d21038803001060030052180d0545d1780d1000c00310a641c0e1144800d4910102443c0d841c801903480c002d8040030750384068440c41c1160008900b09000b40501c802c440043c0000c0b82d001080a48039550354843c203182000144541554070420700c001a8890508800f01810071031640d014905000000ca01006980d800c801035a03030107144100001026516884110b085105a203410717540035180880100e100822290359480250040c44100000381c100160402030a20540c0c0310004640d090000840e10358001001c50900082c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 385905116 1250 385903866 385903897
    0xf140618031c23040b041202030316061409030c07050603040807020619031a01090b0307020f0f150c160f1a01060509120606060f070303110712022b05 66
    0x11400c0c03007540068002d070200000c500c1d00800001040c240410003070604402da40d44e15251030504e036030030603129a114010341d000b03240000c1c509565013441520350001030407460381c003c0441450002d00504001c00e01e200c0ca45c0d40e25010651050000068618110038403004210301c1341003108024064000410860300d0003070030070100005031181d0000d00300222a5120703a1361042d443c904050255100360307010144900500150440e2071713a0002d10807044a00725800e07240e49440781807080741402a540354014040c4a504600854001e00040980070040c9041080e80a0340b2540d60304813041c8210503d0605415801e22840c001c144840461031310b140c400d626900400c01d2034000101906400d80c8040d002c15008510440c460504101184d0302081440103003125151a400190305030081c0b52001c51034002c00300e4400b0405000e5482440d0080102e407a507900d498051418088040c0b250310000014000d05d40d2912058a5030329100481e0b004070010403106000780380046a240e0040101da000540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 385906366 1250 385905116 385905133
    0x1104030602130e13030c0303050408090a030c05010f0804052d0609011b0206040b01090b0d0203030313030905010206070e012a11030c0a0b09060318030d02040f14061803 74
    0x40e00c9100800c141007410b00c0c6058000c0c41c2022004103d04003c4c02079209080d40c4084000080d840010500c0c465814180001c09448a0500e003030140100c0c20910381081303008a0200500c500003000d072003201c074240d841c840407410401044880c0c00065070024071030b40c00301c00c52040035510b100a2a04002c0f10100d20355200c6a688605403604000303682d043c500740d6662070064800e44655284200b5042d0900003000c00b400c4c2030361184107030b690500c1540c501c1907a484500429544800070380490540080403a03443c2d041460b000140b4042c0c1810440100c2c10206000800b5400810703858403030601500c0d0074901810120055899505409000b144102e1071700301c640884028061011405001720710b0310b801c210700750060524014100403a948a0800a8800c01040b280c41040310300c0342000751100c503105c0c1c07182d201d550200840c400031500342e804003144c4a00c500402d980504102c424900c242813102d580e8841545d84084020842d98010400b0480b046628854038440301103150082c0440b414078 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 385907616 1250 385906366 385906373
    0xe0a030317010f140d1e0510060509040312090c0504092913110a08011e05061e0409020315010902070501050105062b060e0a0621080a03110403 63
    0x1501941084021410081d0507840c254a80c8945038007526881c10400da00c0b5041024140142d400070328014031400c280e045000c10000f038840158045051541100300c0300d200703868295100d12280c8190b601c018503204001819181020006000e250582c54640010456070003070b001a1020480c1500e00d56208100014507071514880d03018035078001e200c000c2d152084800c50404e038031002e4030b008102c0450788045c010a0801b41e40100c52650344800f0b020240680400415020070710b5900c850030a510380204228101c2001c01c02070040ea030698020440340c0e07500c3e03041103200860021811034400320407a50040c1401c141d0b203d440030f40d00045c1118440c1468190300c0341c140c0c4d800d81000403000d80104028040100034051030340905011500142000c070182c15040d50705143c400c0440010741218070358805001683c0c01400a003100350101d04031072a01102100241c0414407406006541d1000503c098042851b07010286035800722010f440c0c464148030071405868040c03043c01c0503840801001000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 385908866 1250 385907616 385907629
    0x90a02040c111c0f140f032508071e0306090f320403080402121c020c0111030706050414030307020c10051e0307020708030c0c0315090d1224030506011208040b09010e 73
    0x55030451521080e8020230402d21207402d40d01d201120a000b500f005120a164004e101501e000404020a059a040101041b0080c244c56400400340c0c0380f801d001441c46501c642c00c95402e02d0303614400710440506500d030350040c0b582c0c2d007508600400300c040080760000b44200c40381900a0700042486160400603240c00d4240083c01c0c210200314000e0801c01030f01d00e5010300c00712105d15000d0800440e5540308003400ca40760320440718000c0406540708006010420750442c079900d5100c90400701e81d00e81c41c0c481406507940c00004070840c41200240c105400040c480c00c121102e80300d502985040c0b40c030314130030580d01607003000d4540400d45c040c40d0f8000c241c2c00380800140100140742c81c020810000b905080c14204000307054500101400c20040200140002801e500ca505181c42c000801c8004a42900c0081412071200d2085400000444400d000c03404c5119003502c4c050f0007a0759150b666025010f5130403e1400c001084543c00303000810100f4100006003811010604003800c5000550000800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 385910116 1250 385908866 385908871
    0xe030307080411040c08040b2a0904050a110d090212150a230c0a03060f0608160f0c0215040e0124080717090a02040c111c0f140f03 58
    0x3409460400c4240200c83d101c4064110080d03030100f0445441030300007002c5900041003d0207044690340450140d2503c45034030300c00c111005107008040d45480c5104121948070000580c8201e05201c00704200810601c64414025644058a031416400c400c030310002e814029404e86c0d111000c0180d64000400c103000c002c00241c0c1103040f13000b49140000c100303001c68000304805111003241d407210000d6a8001d400d403540002c804003c4585401c16040200c01401064020b2950802084400501907400c2306010340525001650300030040e05805040b240340550190850000d01488035020141c148031030140300f5541c049081d64585519466007514005081c0e0250700030241c1d9981810300070115880d20010a0158903085a0a007403082005201910085041e5491203480001c2a50320f14100320011049502510612115909480c060122215410180c01900400750380140c01aa400c10501032601140c0310300450f401c50070001c403440b441030a10300400a00801c0214004500003002c2c51 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 385911366 1250 385910116 385910131
    0x60f010512010618150e04020a03020108190c110f0a0201080604020c01020d020f1b011109040b0105160308060307050d0804030b10180203010312030b210102121303020c030313060f030e0303 83
    0x60350515040001e00b0b040c8446e440411004261820f220040c4d4402005c6002c90b902440d10003c1c0c2e403a07140c10b0b0743c29451181d00055401d03160400710b40082d03070480c2c000c014001d0000c090351800c89294104076228005041c0084c001443e8000042051030298050154008034000040c2010030307140440040f039209000460301c02001050b010305040101c0401076099540400034010b11403c0105d0507454014040030502c00da071501c00c83c114030b92152050320520b031808a00196040381a041c0134001c6035040c0e81e03440c000d0040540104841c100030b181c10400340da00100c814940761442d210542c3d651000345c800007003068030701000a211091021000b030725900c0c0c1c000043e070f25451868500c0c2e600c0e05a201e1803090600b014001740d000e98a9201c084c46d602100e58510888900d2409614024460100c0350103800d10201c0600488a600c06654000c05100303270210b840f8008202d080581e28001c0501c18800603125410071700106114041180398001c26040200c0c440c09091300890a60700100e5019 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 385912616 1250 385911366 385911371
    0x6030209011403010615020307020d020424050405060d0803190e0d090e101d0a18050610080109051c020a02040515090a060812030c04030c03050703060e060f010512010618 75
    0x394200e20f0300384201001480b441091030422000c40b00081d499004a04c000303031080b5a0f405450b07007551529080a100d0b188640c181800400f520340c8141e135005000c1c0225401989400d000842c2c600301200c0b15011503070000308440c1560340301020700003141064000210340c5070b02c800140c0045041004044412009910764080031801c001c0740d40000f440090080c0a044d4040d0750401c041001150880c450f020703010741c46080c3c0d40e101c0c282000903050400751050281c3d0f0800108017072040c0441c3e19401401c00020502c10a5903800405090b03400c03000e0058030342d4029066507421040b60140103c20f104050060310307810a086e0b000641103410407101ca28168800c58003183c160701d003821801d6800120060104042402d152801c1e690708040100245000350010202d03000c0401c2c0003d88004551140c4641c0c08262030f4030704141c4418030f500c0101c0303030517041c4801d6100c0d5140201c1c06030320900145014070b05c568a0203040202c2e800f010362080000d5560392201042e11100310103186400800458003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 385913866 1250 385912616 385912649
    0x40e04060c02010b0d02060c0f030a020114010e0103230c060703050301051f020d18090e150703061a0a18060320070507090506011209030201061703030601020709020d0603020901 78
    0x2020944610710031807400c5902d840fa415a860303591491400e5800d80560303160380c59881b2043da240c40c082c5c401801c0c09243c0700104000580c80e41c1500802e010500b002d500c0c031f55a907a10303401502c01701820300001700070071090001802e407510445450f60f01c0d10106c0d1b003140e40d94002c40d00464082c0d4450351003600001c10010043c401820241614525100001c007421141800300000a4407401607400400c2040342a00030345114400845003a005460380e520304025039401c0c0445681d0b11940b035240d1003131700c0304010000f43c4540d00a1045008541d42e01021440d0010030310440100f650140c01d912003030069540900c14191501d05a94001c0c2c005600c00041e40d90b688000c2d0030648025400c03109000104200000c000740c3d0208d80d0108596440d400071a980e128031740103855803156816a92922440c007030110323081c03503415000b4008907000d4010154680d8018000b00342c803480215001c81c0580c1c002d00b820000722440c0ea00409088881401c002003464803039000504c14042a4040390008222a25 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 385915116 1250 385913866 385913873
    0xf02092b08030f04022d010f0c0804181b0e060a050d090f0507050f010c0605040302120c0c0a0510080613020c030a021f05160e01180905041b08121e040e04 68
    0x41d180d243c01c010503c1b888402050b840d995040782d03055090f86c1000008130940030414003c490104120380c3c0318010315103c5465060981060b102c1105142510781085c011442c2081c1d03d19090860001e65903500c0400c9010714103001140c0e011075140d00070000c040001c140292424030401c140288600501380c59045103040031440c1c8189a00614031540c0341d90b0724501c69030b8201480640281d4030050200b4655124241030b41012265852140d610300f0000314400c01c03880124215032420400c0f20002f410503100c5080c80140000c0d04140400300d03075110701144842c0740c0b0000507031560540c1d400c09464424554202821900600c540c1001360344001c80c1030000910240d401c140d14085103900f00454030f46641028042d015601e040f0701400350f0b950381040b290744190f0083c2041e1440000070500c05d551803005000822081758241d27550b490001aaa4009081d000c82e9421500490028002c1030410303080c0d5401640900041d0f8200003603400813084402d140000342000b440c4400c1803240750310742800e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 385916366 1250 385915116 385915129
    0x2d030c03030f0510050d05010e0a05030d0606170406051008030f040501030b0910060c0f0209070f020d09080d140c0f15010b1213020102010f110903010f02092b08030f0402 75
    0xd041010b424103160421840130520480082151400c13a07556109031000c2c1405401000c0908050b4518003404005405210b0000010580d81072040010000e0aa681310100e030400030101103002034407846030104000c50010f800c0380340c100d1031000d010180181d640c455075145a000d0003a82c4e00340034012804203c0ca60f010b00c0740d0010400c003a61200042d140c00404111450428041d407014864466652800d0001d500854141658041d003505010304184030702825847c001a4035a0051003841840840c4a00c15083c420031211a1740060411540e0000140e0f00030040c0101d0b81410034060000040d6102e040020039a06925080908045030403d03030501d070140016005892080002c20aa85940c3d007440b048650110407040c40a018014601c0101d0143ca03444540c3c0400b1401c0100f4100745595000040004070000c6000b0890380c100e014030001a4021fa01d69142d10071030880b8410032034001c00035107096203449a101500701010307036680e03a40d0ba0740007520201d14000b0103000700800c40c00d051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 385917616 1250 385916366 385916381
    0x10e0a06030f0e0a12031503060e0318030109051506060f030f06090105010f050403120509030f07320f12150901140402280810050402100e0d2d030c0303 67
    0x1010f843c0c403118a8907408170044000b4401c03001c041d6a5800501e151180c01c402e81d02469100006201072001d900c145036803600010b00052000c919128985568a41480381d00d40d02540b00c0c02a00f544105c81858840d41a00203141c03c2e00900200010f420b0040c0b03240045120700300281c3c00141e02c0c1044d1040c4440c403041600600d050004004649443c1c40e00201501c0840e5031000c030760b2135107217400320044031540a01441c039501407003803c203040840000400c130642954080725511410707100304c100c0407650254030b081412460403001c80322049402c0c2900c0e00d1181c164082c00c1300003800ca5466009140c0802e405001c45d4111240052140940d000c0c0140d030603022a4004500d242e04240d00014024110220f5403c0301c0f1440480b9603500c8510703070764480c000b1701d0004c1c2a84d003e505030502c84000b500003203030120311421510720004007244c0540c9009100d0040076250f507144039010f0745c0780c019080d080f0144042182010059082991400011880c907034880c0d965007500300e040e840c018080d40c018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 385918866 1250 385917616 385917641
    0x1a010609061e0507021e0f09060a03110409020a0608070809030f041214010c030204051801080c120f060c1b0615040c03020408031812030304081602010e0a06030f 71
    0xc900040161581c8100c03510b5a002c10a55403001038580540240c80c28030070800f0080d048980d0855490f8400c5c903400105801500a40341035650300c5400007040179234202102c115a000086140c148045080c0191100a03a1005000000d01804680002c0e00d1100103a00c0440005d40d610100010641d1052005803c18070100045081681d9107007404801d004502074401e1213520701e0499400c0c0102807a4088a48108130001c20480400e003070002d010b0b50050103a18010710300100d80a11040394480d4050484d0410805404030790105000c000d40d03004c4124400b64107110302609986844001e00c803090083c004070720056038403000303508100e410011002600703032603401480800034103480710445001526001c8900045030860000190000e01440d00071124610003c1000d2402980d402d1847d000079004484241162017040d11141e0f903444100d40090004506102d451102c450025409500030320505222036030040100119150305281e030302c4103001949601e81d0b41140001c0c2d10401e00b03141c08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 385920116 1250 385918866 385918877
    0x41502011d1c1805101803060b010e0604030b061c1208160e090c090d08120417071509020a05040509010f050a14010302130b09180d08130b0408161a0106 67
    0x103002d000440c100150313110700c5000d40700100400e40c03034030701c902c6815481645072242110b0090301c1c0d003000340084c000c0820980c0030420381c401400711858050295001c0b29031002c3d90ba2440d0f65224244001d0300d048411054440d00b04c401d0780c40001d9038590400c50015001d589102c103518082d030f10060104107003050403040c080840f81d11500d40c1c45070031105600058044200da0f444c4000b04c0410307000d1240d000b001e000d50002203980090b038811101c1c10f50203940100c01d01d0307040082c03200004030544192000117045072030030010000c00c0d81068004022441c0001d08011016030350310045000e49000312030018840e591004020782c813240c2c0d4401c440c1c003c101030b441040f5014800c52449100d20041c00003903c555440d10740600d10182540060f419044080c054003000d090103850f0036240c100080e0310000500641074a60725445c46081210720032101171103110400e40560f2036840e01c004003d0002d840d141000c00151030007001105228503100d2103140d0040c8032083c20350b14170b0308661042c0c00c108100320 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 385921366 1250 385920116 385920137
    0x2130905010311220c02060910050c0a0e130609050f0903040b0706020d150f0e090c0913020f0402030705090315070203090910030b07080108160b041502011d1c 70
    0x20152454202555400d0f904c0070200d894440340340005425030b140352003070241803c440207405540441d1441c00340c25a1400c440449944900d0030003074420840300482104030621000001354400d0380000c1401c003001d09080b8850328610354003070035104c841d044000d109494801740107030004d0141c0101d6000d107415002d0760400381014030b821046c0c46401c2001e81030540205190882d01e1003a072005c41e90034030700c0000e885440d43d00c0d80f40c2a50051a03105d8036010030307443c500041c180c0780d02240f5040c100d4402891034800e0b40e01c0034a0a80003031900314003607800080403000c04400c0c0d100c606c011030044603603403216511490300e10101840d018001c100c00008421401c1840038107600042550200a000c4800000e903584d850048002d861700b40c1d1001e08880c0b0203034180032100da0040c41e95070680e240601958078820129804c005819080d108405103000108020406964002d11403401c2c10310301d10003c200400c98414520714040241c0c2a041180c10524910b90709020001c4501308000c814206061002e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 385922616 1250 385921366 385921373
    0x1e0c01091a091501260a060603030807020303010503070e0a0e0f07080106060c02060304020f150a030c090e04030c0303020d020408120a090602071d040609020303030708091b0d110307050d0501021309050103 90
    0x742c0184603151650b034a91300101154482e8060560f4178602c3c2d01c0c03c840d4145124284040030300298401a00482d0908010401c8544088101c1341a64806070040c07401c24501071480f0841d0600501804c44030b545e0743d60b00000030106002c410241100c4000400d221818032010500b111601e52001e000e21080a200e20016143e4070103591780150100c601004250044c008101d0130441c49500041e82a0005105050282c0643c000d01700341d1a9a6104203407503846200e040c240c00001d560280c04219041a1803001034480e400808044603011009800c180d40c6090b2a4681600003244c41d0b0086000308400c9541584880e0740c02c0104414401000c40f6480d020410005240c01d9205881a180c3c140018042c0080d079000710b0206030b400741c2201e42e28903040100800103503040d2403000c2039008101c1c00070234002c410002030a407400001c010f119184c00380da5030302626160700b0603450f0309401030b5100010340f0b130340354060240701c5400b9400169641d002c40403c007180715102d80040200c80c0c070f041c0062010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 385923866 1250 385922616 385922653
    0x130614070302060f070c08030c18040e1c05162906010813030201020f0315040609020a120207020f030a21020304060c0201050903120f04030c080f031e0c01091a09 71
    0x201c040381e00e0342c44c07603601c0b152000c9801c03c1ca0214040c0003135000005100340c0e03000f04c000030107042150192a40c0821201002c00055500f0329207600c40540c4400381900d0385914070340c0b90808004180c10618900b0b2880e442c1d24480c4d100401084e100243c0c1640c4006040307107100242c142c0a1074050040500349042c0001904611015080494112507140c40600f014002d5040b00c4503203502090241c2c507403074004694000c84510621042c044e038208030f000198060a80242c59052801ea04c8100c402e40d003030b1039a5802500004d01c141c1c5d000c1e41c0004100c02e1074805001c0c030043c40e4001c1089220742d07102c100e41c0c240c04102d500304480031507100300410031103264083c0349183c25a80c2440c00030b83d20070750100002e251401d80ba00da050754620000d81c04100070f8000d0001c0c0304aa2240c1001381d001c580c0c43c10340a855400d0b059000009400810080210f03070441c0c00300381f0f035103000b010f55542820321381108182156107050003164001e80d0250002d01d40d10111040a0f40040d50724010400c1850409280c2d91 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 385925116 1250 385923866 385923871
    0x100c02040c110c030606220f060f05040c02010c0504060507051e010c02060f01031a1f06020c030f1212180a03030c1704050d0e0a03081303020f060c06010b07020d0813061407030206 79
    0x35040c0c84000041b4121f00c05130044100840345807001e000350780d01c81da00180e080304540701d010310030391030300505943c003a00601444019800c10b403111410603103414402c0e1601c1d405080d0842e0380e0b0040c25024410503883d42d08964548040b100006101d11040101034134043c405003960b0341c04070f40c0c1d0b401080012150098004908490080e4230159101c080408110404840700a6900002c0300c0000c112039900180d24501110700f1000c8401818151080c03944400d0840c032a4420080200010b0054040d000d00c500d810058494220020b001c2054801d414040a200304600080d1107443c064401540418815802020028820314504103540d4141d650540e0381c4020082c80701240c59140150381e000d5031040150f40000ca850b64621101c507290150440601040748620414000b60304141801303001e849029044070020080c17a404e00f4200c0a560b04941000c0307030701081e1403515a002912203009040c40300700c004030806200342802c00103171800640c0ca48000382002e0074091040820790002c3c0894 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 385926366 1250 385925116 385925149
    0x30201120e01091b170604170c07030807021003020a080f04110a0602150a150909020307031a040218090a030804150e031206100806100c02040c110c030606 68
    0x11820000c04864005050000203040403546068000d0050001803074041d40800d006031800c0c00c0b180d4842501560072440200c40028a92141c40001c00242541c1c000610b2408200540d9061031049828a440d01103942c00807500140007050f070808505010403454034400c038504095091001010005104010040c00054100e0150004c201400a440d446540407580640320090854032054003941d1a10020b4401e0782c55007028000800510061045400040f0800741c0e1200d545c1c03600041c1005031227a402c0503641406031031000400600ba403078080c501c81c202100301007210329040c0100f14a00081140342020b0601410400c40c801a001c5150703044191f05017040b40e00c40e01c550a1044038078410802c1e104004d0b1400b81180c0840c00004080c10025080c5071034140c0340e40d10081400305950320442e0080200e0602c80102d460b074034205080e03031400d204514181004c445183c001500381c3e9050038541c00814490b11301c100598105109054502a042c3c0003409241400700114044074030140105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 385927616 1250 385926366 385926377
    0xb010302031605130302030f1e0705151e0301151d01120f091203051f0f060503070c0203120a021605100309150f0b090106080411040e0f19110306040c030201 69
    0x13250060f8001035003001381d03030044c01b1101c08416a0b10101e50301e00348500340c40510340d800d2000b0140541e00054410650b0000303410454a145841c0b0540500e400caa1841d0950700401c010b180c415418080245000381500403074150001030248000d0103070781c00c0d445003c41002c0e65155048031a600030b4881064410f07444000101c445000303034888014080e1002c010091110400c1c5480319580c141c0086001c1c1c1442c40e00703a1030f0010140da908510034081d1080c440003d5000da420003100b80a10090355105180b820b1180c07000315a0390003e420f0041e00c00601c0070b400000305d0000e040701d41c10080d410080c6851070000248a040c1400100b0240c3c5050a01c42051303103803519202013001d03d0081c2d00c0b0b01383e140314050055824034400b000140210341e0f25280501e2100000213a00d078442e50724240502e400541c3d5403918804101030101605080824400c0c600c05c9100320050544108070400184802141a403c00c441c14503205020105403000288a68480e0040c8008940c20318060300c210395090910 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 385928866 1250 385927616 385927627
    0x5130210180b0a05070c030c080115060e0904020d02121b03030414190e0c0408060604110a03090c0b04030c0e010f0b030c130906090b030f0f0c06031801020310090b010302031605 78
    0x446072171140d03001c0248440d0f66040004108580c1c8294201550704250003408030000030030b8403c5c20b445c03841c07040310001040315900c55403034140140350b0787c0c01c0350020784115210130498020a036150307110000b9004d00d900030441d00c0c503055502007038040801400c0b0040c51900d40340144c0584030380c0441c0102403098803032008a941801c0f41c4c00800c0000c183e00b40c11840302d403500a103a40025042803050385070038000c000000d011490544145500c1d4080ba00d8500d09102c0785401c01c4005143c0080f0484006203410310200c0c400d00e8604c0600000c0d803080818100e55414400c100401c8013041e44154011402482c2c113000d0085018266a40082c45098260301c80c84145641d041c2d00c60264082c104051801001040e5110143c03c070b1145240d0a400b250318100b08450641e87e80c000c4580500003a80040b90000e04514201e0300450704601c02c480e980707851184d960081c2d03007280e100343e4507044a04030f0050700300001001c0e4000d00f4801e010900341103007146800c40c1a0601c1c000300c40d05540c1040740000c1c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 385930116 1250 385928866 385928887
    0x2404150501110c09090d0e0907051c090212010e071d010314030d151e05060a0c08070b010e04020306011208030c090d0516170102070203100c0203040905130210180b 72
    0x24038511000802211041c24206000e90300c546c01c0440070000680d6540c028500e034184500510b00900f400c0c3d0300e89140115040ba20416503007003594210a442e01d840c641009070307541c1000080400c0d80d205c00002c1c11502010000d24000041d405075802003105441100f0140060070814110384e004200d4000320000b1420880c11449110b4000740d50a240c510001086500c555100040e40c1c1d0b44016030000940d284d81d4000a05201c1c07281d03542c44502000b002d0300c8a846003034001c00e8240300d840054200003480e650746107503003070981000c00c83c204020f08003c01e528041001600401040d50a418200002d8840f001c0d5840b000341035100d580000507402d07046445100c424401c0e250802c00350f503900d050414403801c05481c00d1042c2c6d8040402c00c102c00300010418401c407400154000c0007400d41c070003201000d2014003038514020065000c00e1000103140d44840c040c56100300d5450311059030b41e405610401050942003405001041510003601550804680101058540515900d5180c590410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 385931366 1250 385930116 385930123
    0x4120c1712010f05010e030c13090606080c0a061b1b0909060f0509010209030318040902130504021504031a09031b0309030c010201090209070302030604060e240415050111 75
    0x18109614100010014800d0036034804850680c0e81ca0f41003c50807a0b9150011590080401e0400b0b42c16000001b22038414a841170f11480b00401c6240c0c0810340c20f080d901d40404881080d03008a2007a0041c40040c0003500c0c2030b800308000b811480c20903c200c1844c66500800d1040c0b011001020050a0344505820400606001d401042034003000d0081d283c007860030a000d80840d112003c1c0485c207220204a4511060098035a2940003400460038030b400381c4640a001c0c068101480d4100f581c800000380541c58822844d1504809008040740c5400c1c82c0c8140400444601b1502c28616402d102c1840044c3c404074510f0000c610855266901c0d0720380384042c0741507101c0c21208118140c0c06d000c84410101001c00500fa4043c0224180c0340b28101e10401a42a80c810a00c001d40c01004480001c1d0707454041e80c06550094006000010a07a4030b0b0300102601000c1565110407155a03141c0c2202c80c0322000894800038581510140040c1e000c8016040702c0c00100e002e01c5062150010f50a0740940040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 385932616 1250 385931366 385931393
    0x111f090c0e01291603032412150b04020c030a080c0f03010e04020310060f06110604031b050709060f1809020f1e0a0303111e100c050c01050408180904120c 68
    0x8442c008410007040c035018004150706028200c2032244407114100240c7c0b003082c168220f800c4218032920318001c03a07560081d41c0c041c00f01e141c5406503550f01ca07000162541d102a1102400d0000155550701c601c180241402900401d0355000103403c000ca40b6017400ba8005590440e991615041c0c0c090310f80d0b100203401c02d10080401c00306076280c42c4c0d0014400711040841d4044134026124160115619400340d600c1c0c08040303a0180125400c2600c820780742d103c0a440752403581c007a81c25213054a8803000c9200655099030320506040618030410b01100c4000300003620014072014080200c51070582c00700304880b086440061150004540088002c02d10010008c01c0322401000f020603692240ba01600014588020201d1031040e84040500007080c0d4410030b80100a000c014108120310000380405007500c2d02411081120174840c10307034010401d0040b40d00603031240f0085511420a17050f800d9122039500c0c0030610a1a00707006210105001c07403900801700c08145440c2000311414200018561400c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 385933866 1250 385932616 385932637
    0x3100f083f130801050f01030f0c03060f05070e04144b070903200a08063922080d030b090a0905060601111f090c0e0129 53
    0x40060001041c050000401c58441904400d000b90303919030011500b00d03103084501c003100180190052000c94083e50182c5006441040e6500b81b040c0c80740c1e80c1e5002d807280895101c2c43c44d41c862080c800401d07000141410200e005807800c00c440d400315031043d050220003a00041075500310f0781c45550048103109100485030f44c05035030b244151700f11f00340d54001038648040c0d0700410342054000c695000c0c82501c03480201c9405c1000040c03003103014550b103040d040c90000b007994811108000002c0445c01844060301c180c0160105880041d58000030900030041002c40c0f4100b150740c1c90564000300d140d001034484070390ba007002160f84621800d441c141c07150519046654284521001e190440d0b60540041d500070310207440c80d100301e46801c0f000100340c6000e150002d0182d00f202c80002c1c607651207281c103118901c4500084684a250300000026580e00000c4614074407625800800144440e1901100040402141a40381589080700c1c901040600d6a510007030303800c80c80b9810640e40b5107181034907440145d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 385935116 1250 385933866 385933963
    0x1806041a09030d0804080403060c020114090a021908070b0c03130b0a1b031e020c04050c07021e0a030f2609100c020609042a020303100f08 61
    0x414104100503001801103520922889802d81003c62140e48140d00880c2c0c0044043d06060451355010040d0658091603803c5640c0d40800d0352454080c00c0c881c40c0a60748440140c00c2034041c034014011130401d4406100c0320311203c100300b0000100005a2207040fa8004152151502011000380f401e520034811003c1c1e62131b10103007000c24031005080082a074251316446490315a042c1481202038040c6510018010070308145201c880e00394822202c01990389284181c40b0541c10343d030002800c40710140c1d907100c1c8009011038041c08500300b043c0f03800140182ca41003d00390307100756000681d0192007804020001c10104101b41c2c01c014852801181070311400e9219504620b0846d2a401c1d650001840c06100d217200c82812921b55008140c4141211f030003401039450100c02d642404050040030141916103112411007103c110701b00302150300c0203940d076070245950342842c840a03020041c458004902c030940e95002003001c90f20004200079062803800f141c8810300c00c030326103200d0b060211040000403c1c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 385936366 1250 385935116 385935149
    0x9030e060a0e0118030201020a080d02120412030c0c1709060f22090b10051803030f120f09030327010f09060e150c0705010216060603020a061103180604 67
    0x703411240b500701d00b200a90300d000e4029a00b02d003c0155910520001e805a0001c1126201040d50b0b1401002e2030f0466101c0036151aa95013007070440400121782c203484040305501d035512299418064103200c04418074111182844984a250301e0043c813003000c0c3d0015000254100c084d44034070055445003003141c2d001c1f9403207441c2b00d46c00d04c001101501d6804000e48000c940031484210500c190591082d001e442c0c809400c900c42c60999050f0320090744008480d5a1280c5075900740e038104004d00700d00c0f0105400580720021180040705044000d0301032018041e880c400c000b40c4d0f46e000000d699200f0407031048242c10780c883c01748000e03680501300d4900509500701280d501d0001c02d01e803c200100c621902c0c0c10010482600750301c94031600103103004800c40344484042905000d034240501400b81c0220001464842021302c0034008090b89802210225160b000410642c17602608040050240381400d224515502c8038a81c5c482c4a4020003015420a8401c40c122585641d030035103000e040c5c040f928a8a10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 385937616 1250 385936366 385936387
    0x60307140c070e0a111801090506040909020f060f07033e0d020c0105040302040e010e010920030102041409100f0f0e060f06040314010b0901240e0105090409030e06 72
    0x4040c280140c6071009a0342e8003044d80c1c40914451490141c55205203541020550480a400803000621035410001501e002061581e1400c00800c0103122100000907111018414080b89801201c44688105c1080c06000b0203001c00c24200c566080d40341c0fa14811401c000b05420350507002c4894440c40e80144140b8405074100c0103400c06c0800c810090844e1500b041c4110101c0e40d03088607680341400100f082c402080141080d80000004c0c1181900208046480c105010300311400003005842d43c0000300000ca00a40c0403c1200c0d42c90503094000394985800c002007216110300c050b070b034036003c3c1030340c40300043c011141c8081d9580540481c4400c158102c2d81e0701540098505a0b0140303200c1c092809011840500d0034802155924002403d0300341080e195840ba030740f0040d4810f1181c1c0c902d5481da400401c46584040d489800781c440b541e4018000006c0198080c0800d005105002c1030100030b1600c0500c90380c2100540d190b03d04225004101907045180885042509201158200c4ca0114a0a4a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 385938866 1250 385937616 385937623
    0x3010906090b040c0f210c021e0703080406051b060c0918040c060503040c090606020d12020711130e240f0103210c0f03020a060c0e0609060307140c 65
    0x2140c0d0185000c1c440309a400c01040b040340c1c4d03107840e40d501048102410308149400340c1c2e0340440480074039022440c1c42c00b15034044c00c1500d150050400040c0c0290f014205104075141134036082d03038415001890742908603510382e0f110344503074001c92040c014082031642c5281d01c140c1488070950000020388990741003181141c5241e4001218140c4106804002104400c07030042ea010320560700005103c00007407412100340c80a038409403003a142d84032101b50200d841d40c03240c00345030010a90b80d401401c42c1500a1001001004159440c0c0e9409004000c0f171404222415414090b01c40120342c0660414000300324a0300130030b500c84a00955000321554070030559604100040c110480ca014961190303181601710156050901006210601d001d86003a460f90510348403001d1100c0b00d09100c2c0541da42c903100c480c0841503022080300181c0c020000d0300308006890040d54441e010b141008217200b0304140c0020b409006480f00203018140c01300008080510520105c0740b0503169040c4180e0314501240d00e1501c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 385940116 1250 385938866 385938869
    0xc08040314070f1401050301090b01090312050a030c031a120309030a08070b1e0c1e07080a0909060b07020f04060504020c070608330a03050d02010b0111070825090203010906 76
    0x2280e12040c00000b0703588400344c1d040d20b80c524141e44003459603003050620001400807030191410010f00340c10100000356a405111401501c91b100c09459050f115801800d40302c11a02800406080001e949110501900310764030a410071140307005444000251f00e451800b603008001d900d4800d92041c041031290490050412900440d052140c90307569860310b45403214111640409264000c000403003c00000c00505404075020140c0090214070381802e903c513401c0424260340c8103000041d5800c800d0f40040144c4024800c0000a12015281c0700000816004c1c14a029008101c28101d603409503071958807440290000030300454990507070640c15a41c49249004130004100d518010401c0e0b013084e90300c01c003580e40c9289000007036820585e00c020304400701081c090303400426060f0044001041400f1211340c20700306600002d103802504000400400140790880080c1d04403c8041c0300060700800d041641c040d0001184400e40c540760000310880c42d9962106032060b00c00710011801c141107401520 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 385941366 1250 385940116 385940129
    0x6050a030b0307080d0503090a050a0b090607020c010e060a050c0f150f01050a0504020f0702040507050c1504080a030b060d02070507030303060e10211424090601060c0804031407 78
    0x840000301c00d05140da61116405000700c0e0b07610000b4660a061311880003182e1150400b03090300c180d28602d03519146004d281880440e41888a08100705100300100840d41e4407020500c020440c540d28000040c090544407807413103005502c00075020003201c0c0a8002c03105501c4110084501444100b0030458490303c800312103d1a2a1f4010702141d402490081900c0c140e520091221210a10305000c2000944c00303a9008007200300c00f0b201440140ea114032807107120b6982c0d0f8a6240d0380e800040813450819034400c8100b8940764284043c44007040f100000e03504c87e8500390800082044100c00011298001c001c50510319500001d82c01e01044808200030080308d01c40d84040c00400c1d100e4801c952140b100310766900791459442d40070012401c1088510041c204080840c40c0c049845072660f0404602c10030104003150f018500c5a50948440344034510001b0340e0750303003042060828032280c54071468184103180c01c0040044400d428810103070b080707134000c640c000d014040b8100b50462194440000b032083c40e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 385942616 1250 385941366 385941371
    0x313021503160f0504210609060b1504030503030c160b07030905060f010522330e0907030308040302070e01090506010216050a031b08030301121101170f04060f050106050a03 76
    0xc0c02c03090700422144614604544030203041506010300801c42e00d140013003102c1d940c0750030400e28010410328070a0404c02c0b130084501007482d548500038000010820340c180d00c00c0440421003000072483c0030082d26003141e0605605981c131030700b02c4580418620707030b0312000c1e011004070703c184641c0b01d8055012142c014440c80a540342a0741d5000d01c1a01c0132000d114203604860300395150a0f06108800c2c2c16a82d03001c9014000480c00c180c80c241c41d03951810419210306000510382d20001000341500e44000604003214800e00302e18000601940b10845031000805106070304c8040707400c044c000d000110181071000500c036520b60356102031001500e019100c0c3c0d0b005d0f001d90704004482c5a600303005172080c3c41014000c5003680385956201c600c10407404070a5105020040d0010405030414030046008101d91890214240000d041c0b5075182c011b0b414030036050240b0003017501c41d00c1c6000c02c0c0195100c459440007481c0b66940c4c0c205a00903115103803500308601c0c0f03018000314111703421030007034108a8102d5504 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 385943866 1250 385942616 385942651
    0x112082215111903030f1410030204140c0f070302070b0a0302030a14010b1c0e030c0d0f0c320601151112090f0616080d110a0807050313021503 63
    0x581e0300c2c0d918a6100040d43d64181843da4003290094000b0b210883c0102c60000304207200f660040180003081da481c6d0030f508656403003001945010300811001e4807004245280e9801e108070050544d215041007002000310100f900000d041c02880390000600d411a40e240d0f03900100c4c8030060095200700d4264030801d03c0e200d02d69506c4040001d21605171044400c41c03034649002c40201600250010b00381d5000c2c191030300d180211030030050016100207401c080040103000070030036005d0b00000b079581d11b030000c2201c800300303040102d81e641e024a000280e041c2ca4104a02807040ca4450460074407141d520194400c517000050f100e0300500030084170300074650741c031084140d0426216880c2c2c600d180d4032582c011424801c0400c6490696603690300c82c000103100070314044a01071103142e4007080b510180c400e4480410800901d0200b401589001c00f10012907501d40852044080d050702c2c000703000d0004214002c4005a106d002c40c03550038491a80082100c107a8840c540140030300ea0348101d40e190502d8114500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 385945116 1250 385943866 385943897
    0x10060311040e0d0e210a05010501140312120a06030f05071401050a0804061508060a050601090b16030c02131503050d08040f1209150c0c08060112082215 67
    0x3a1803440c2c0110380c2c0c800b9507914404c0104980104000c001d503103900c2c584460072401c2002045050090b504ca01c0000c2941c4d0b160008680500d810070420354080d0f004841c401d858950b41e08103d8615005621102c101c907195450201e006008039003005043e10f035048808024003000140c90700403a0024010301c01640c188600445590080c3c143c4040424035040c04a03002480503007000d0052030420144409042c4c0c0c07105400d148c408107a8422001560700c1c020f00046503800107804000c1c000d40c0006c00c0c07801010814035640d5036074041d00a010028010f8241c1e0031591817160a44032412001d200b40011400c0000c6610f4440092004682c0d911a86130040410340c05108000d00c03968102c100b078407800d900c0da2920302c40304500481c8102001409100401c0c001c00d5100012848405aa1984152245890010118042a000480703641e100f04010071014410303800e8a0f08060707001c000c054072b840c00080380b4501f0100c070303001c035159244e00e41901140c00c401c0130644180c1c107039265441c50b81d4541d0700034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 385946366 1250 385945116 385945123
    0x100c120207060c1103032a010b03030a050a08062107140d0b2e0e01062705010f0203040302030601060e0901090509060a020f120403050c070e0c030103031110060311040e 74
    0x101e00808901c401e41214041113003105040d0f4490000b0781500c5c60300d10154100d00c01510051139800100c03490071014001840248651041d000f01500110300c0c1128400c00500940a1404100100519a4005070f03450322900d00c0f105a009032145602c0320308200b001069240e84850086002c20985440d9002c01031404a06003201d880d00510070034000d4544402c150340c0c6c20204980c4010040821480c001d80c2034800110710005e1100035112625941001c400502c0d04085410324885409640c102262100c440e4828400b01c480909105001c494545001da0550040f640081c1d4107010716800010390f940c011100800c80d03c1c0071101d82c122030380c850508000701d500569003501036500c500b001903020910b80c0d005000b0a114210001d00381200141d40d6626410f0071641140001c0e004a112901c0c02c80c00c20014000e03240d83c81040c04180350810034203406000c14030003d020040400340060300001e003030006c084540d1039104c0500a4984030704080d0000008039401d40d00403403400303405400305013010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 385947616 1250 385946366 385946369
    0xf030902060d05070216080304090b220c1701180b1c0803180a0f0210260a02041a04081b030c010806031006090e060a05010509070302070302010b100c120207 69
    0x8101c98140000c07040000014640148030105502c2564003c402e445c200703425640040030f201000399038a90900a0381310035595240c44180c0aa010013540191541c1c01042000d600100510000780745800500c04a6035119801c3e00c85010910200000c541d40c20301901c0c2e00d05c000c28120301030181c01c2c08001845280078080c0034540f5140d0340d401e0ba480c00103180800840e00448014105030714801c191a5050622910f400d040300e07440c0032510070345d046041c449000d802910042c200070701c115070108040808010040600d21944010000003142280290305980141c446080402c1740f8201140c84c0b118254424001e0031840c0c461648031070240003540e809844d02001c00b80203000c42440711001981c6404000c0c0611b40d050045034001c1d83c10300702e1031040c0c00084c0a20180407908180c2e40030a107003044070141c0340802c1c0b1410800180142e403681c80003680c002c803076407400507500d202c60300342280140b10043e040740c0c0c80380305d0302c403044220b59115030681c00300d900480ba0740c44401144001a61b5401c405d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 385948866 1250 385947616 385947619
    0x306050f041e09052d0d050d0902100513050f06040506072901140303030c09040c1e0e0109170303060d0f0b040b0f0901060503061306060306020d060f0f05010c0b07030b0d030f0f030902 81
    0x5003c1c000c036407d11a9001c2c00210b500000045415220782d40050502a00c1c00b001d030001500110300c0c3d008206840b44078000a01d010b0781c4a460070212500824210310540c040d480c020f41d4002804410440b41d000048481007035006100070709543d41441d088682428401c0b105542c0e044d0808102c58035001c02224004c08130421460301e4120a0b0062002901c10040c42506120416640700c7c5404820381910002c06d6181d80c2c2e49810500b1000090009c80d010303002016151310181c40b46a8819001040b02e400020841c0e01036401010740c58040a01d8140c440b0007045402c544040c04200072030103050b18002c202440346d5456554805203000d088410710f2048660541c42500480c1c2da0307400071003c20b07000c80c0c0105804501c9a88903101d4409070380c0008190881280d070f40f4010000c0035004104a00a000c840c07140c00101403034900020444524000c0c003512146200c2c0c00700f0ba03c9802548141284007025024510a4540d424041c028402015003030300400c000f2040701c0312151081c86280c01c2180d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 385950116 1250 385948866 385948873
    0x9010b0108010e18070e01090c170c031312050316050313140114010806040201030e070b0d18121d0109030302150403050408100204080c010306050f041e09052d 70
    0x603140301d41c4990800030380b945284d0300340154050034400040c001007000d044884500080f80d4075140c0020115080e0016110801403e40c3c05100800030180d003168010b1099607146440380c079041e0801a81c102035102c020511742c141599654019042006503200d26100b4610200c08001e041095400b488210390070240364040c0503540c40040c000008810401d03e40c000002a510741280880100c00003e8000300140d9106030f04100031036a15028201150f408031000d03026042c6800004400390040c8414414900e80f9419100d5025182041102c0140c0e0400c1404c40000070600000e0f055503941c1d034440c0c074903540c00e440ca1107803940210402c5040380e80c55030051800ba0740e1403000400407140500304408004082000242e840410050b1031681c01c0c5c42d00e40140e0b150310304140c0601e807100c003202e114181810044104076503612010700820111081d17901103190710802c2ca601f82089483e01900400b01d00d0490141c0c00e0110000e03050380c158940440d40303070102403e1921003040c841c0f0075200c68020391 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 385951366 1250 385950116 385950119
    0x5040b010b09090a0c11032a010905190809100e130c020a0b130c030c060914090a020a11120c060f061c0c1208190906121e0204080109020909010b010801 67
    0xc00c65110b08190b40041c9400004586c40e90350380741c15035000a21001012800030111005e54078011043e03007000310314200030803811085964440c0c8a80c0a004484501d0940d03c801509000300340c002c5038048000141016022800980080c1500b000711a04030701a5400f003483c1d6489241c0d51042820314001074008140b03811596940c8026910018a04036100b049001c841c4001540241c45401851040000c0740849080c17080003080000f159006200c0a4201d001180c40c1e52181c0030b0068201ca0903400c05070355448000825a02a80c002031113502e50701c50401d220089050b040301030041101d08209550303954941c501c4201c40351100790b40e21948500e41c480b4030800c1040f00303046045e101c0d118811f09810280e0750300b5403040d424a044000e40c0d280d000010851744040e0321741ca442281c1c0c006420300c10b01d100c3c1080f0008210030103501c200b080c05940c0c0c071f45881000c2c0c224400c11040e644403601c250354a82c1c0765520b850203080d20b520700328044d03180744d03010400543c0103004000202a0603994558039a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 385952616 1250 385951366 385951381
    0x4112a0318011e0f110114070e030129030c01030b180402190303050901032318030f040803130803070308130206040b12101e15051b0105040b010b0909 66
    0x5070580c428141030044080b51014148610500d500242d00d554542c5000b4000e02080900014001411480180d24009184003c1074124000c0368101c030030342c6400040c206100c00464010120b080c600001902c4000d15050a1414034441c403104100039000c1e1241084100010340c1610700e0340500036845100c030004140c0b003400040100798003a0004100a0807040810501107200440d5002940028000241c8501a507018001d03601540480161441c3e0b40c0c01c40d4082c0c502c0321001030400035400544080e00c400824081050b1041c5224054050342d44075680c050141c0d89600c84202c4106901d881e03007001600340001300503255003a4043d129218165142c22500a0400d5403000480c0c2c014414000030031074aa100001d0b000c40d80340d040e0806054182040304517000081d0ba8046898151500f01000020080307440c003404682191280108280944105a80c0d5001e084011030118111200400b0304210540080d03008034020006281e0782e07600c460250701c0038400c544199800142110118004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 385953866 1250 385952616 385952647
    0x30a17030403030b060403110a0f12060e030405040c0224070f03090201051312060b0402030714090301061e0e0601050f070809210a02030c0f0a0302150904112a03 71
    0xc42d110b464001003415500c4001003290f0401e030030944403200c508200310042e0600407011005007010f6042141c0007440c2c000c98041c988107100004009070b451b003207820b80c45801081503d01510005009001903620311a00940d580d4091230501d004c0294042c907100d06030240e0841034020406962003000306c404d504401c0e0068011114101d040210800103801d112030820540c030b003c3c220480841000c400c0d51704000d4141c815407510540304610400c18005019040422000881c1c00c0c2e500441c3c0f85c00f6002c0010340104500e610070922402007203509046004901e845e0030941e04070541a103959207829004541d14044c01d04280d0202004200c4400030600d801702910408000815200c068040c2440004442450800051841e40001819802c40c541802000707031003d410707551980b14074001d0700040e41150451201902540300070400c10040c4070380c801280d1407080e0140050281d0b60b041440000c1d594044000c40855100004480c05a0080306242e0401d161a8200860618020810766100c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 385955116 1250 385953866 385953871
    0x2090312070f0b0a0204030339020406030204050901020a0f02010e15040503091011010608010b060f03100e0f040c0b0a02070b0f09150703020118120c080d050a09030905030a1703 78
    0x480d0300e8041e20080003d240c1d140440d20640c2c03060720242e201c80c95031070081c01c200c80744240003040b4491140d03000c1107072001504418409040100741d980c60a07c50001c10002e1045810294100d41400c080068420054009002e004c035180d0324800a00e801c644120300b21890300549070030b16000768400c5200401c0c03d500498119004030140c910344080b00000501040640803900c0125286052051a04000303103d03020090ae20314000348442c080900029501340300390445400f80340000300101d5154000702031103102620b00d43c00c0c08101400d00b002c440c0d0301000221021078243c540b01c1e10102d007003800d05e03099507200242d0b03400801c051030034030203214540e0b0000c1e51410320200061010141550b10101c0f4950144880c8503090707583c0549040007070039510001c0c0000c860207020b00302c10000440700084070b1009049881c0c1840a20f543c0d2800c1e40b402c2c824000074400c1c2034202402d00c02144410b50100e031245100c0d4072044407050381d0f001072581314900458090841c0500d0910150511206030080d036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 385956366 1250 385955116 385955123
    0xa0609090b0f03010e0c04050a060602030904020a0201060e0c03090613050312091c110c0603010303090306020702010e06030c030a0c020d0912050a06050103030f08010b1206060901030b09010b18040209031207 91
    0x40201541da004a400c40b08480b40341222030780902c0000b46d49042038813031107401468012040c00900e04240c1c011f0b40c0d9124031061075025a5000078803c42c154403e6000c50040c04c60040f0007819402c01d24025049508240c80380d040c50300034440400e09840c9803d40301e280050384580a9400c00c060f15041c042140c00041903e840c900468014002400120781c070111006580d0304d40b4468401e010007080c0c50044654016801aa420401800400e4024a001040b240e000c0c401580d642d000d440100c54800d42c5a03070b0b9a1b08620301005120b02c41c03c4130000786116081c00142003280140590301240d60300184a8000049414003805201e0000c00071500020140140c003103918082595458a0803114264002d400140c8594949022070f0b511441d031500510250091500703042550341c054141e0703007010b480c540c800e0030005020b040d5a406604680c0018400410709069503950b00c240303034526407210065100c0004060501a140e16203031003620240c1101400600744000034110040d80740c0c0c03050f001038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 385957616 1250 385956366 385956379
    0x90c0a1d061908031b0703030c0803071e03021c09080315010306030f030806030609030403051b01020a050709060515030c0403080702031603121e020615011b060207020f0a0609090b 79
    0x20703259040c56040c00d0000d12002009581c0c805810300c542d07105005e40c020000c90303070300705030010404268880b000c1100180c1004020f540c9885000d010341d545c0340c8403414009401c900160300c064091f0580c3c0541060a111091a40b0440070081c030301084900c10b500080ca265002d1020400c88a42c440050300c404806040008203642c0f00e0711004000c41c2e1101d8100d00250481c4104003103400c00f482860f403c07000080c000c604190841d80c8080d260300000b8140e000e4500c40500f0040207070f01c00c001182d4a150003400365a480e945503031094000d45824060140a054101201412034050300b00301e034400c0c0000182a03040034115660184030380d00c204400e90707152240000d810301c2c40c403515060390011482403890040c0f24580000140050b5030100b2480d4005c021081448485a000f0803500d5101e01f540100e212580807c4005075200004102c3d0040290410003a1004000d80d40c0e005100d510b000702c5285510901003070821000380828040c5c0d41c002008100104403030400c83d00006001d00c03005018 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 385958866 1250 385957616 385957639
    0x12030105040c020118241a190303020c0d06090b090115150512040c0302060c1f0203041104090c0812120108010e0304151b030c1109100302010804080f030f090c0a1d06 73
    0x4400c142c41603540d00b0350b02001210051a680e2400323444c20700d0740171105600c4000d11459a14081d44071928490b159015200940d011030403c07005505c80340300e641d44107910b8002818484821030080c07144100301c5007018a40e140104442210dc002c00700d0700021580c6551030079100c65040390342c02001410480e4280f2400601000681d24800609440d10141c00200740d820b201720340000d0030342501056410694410414003011480407840c10301038a2080e074001c1103210031403500702c0c180c2980c2e50180074180175002401854011a00c0100702c0c6095001e02e800301070b6202c0006500b01d0b02d00c042d46501e954003c0100b0070085ea4502d450300680001c5080611046010400071f04203403025010441c0045c85403800c8070700300500030707003075940c0c0315801e4072207031041d2410701e100e00c50580030b500020b03052060440c0010100440c0ba42220414807040400c03076184d0500c903c08014881043e00c00d0961405101d0f203102050a01503200c1c0300710b540183d80c00c196800d140c844180c04040c0a452182c011740361020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 385960116 1250 385958866 385958933
    0x10e010e211207120206070e010504090203060d2003160f06080709050a090506090a06050a06051c020a031508061504090602210a06080105090304060305100812030105040c020118 78
    0x103450040d0042d01841520944654001c2c14106c0050645c014081d00d5854240166070050588069540d08540160b0b83d898190000d0b4291009890050882e91118041d109820305035100202030242a4201c9480c154000da1808103d60079000e080d004118401041100621903402542c00c21000c1c24460801e0f0749420109201003041d41168202c20340758400e20041d41066655507034481c005800c10043e007818038002419140c454415101082404200084a001918104220290b102200710741e03e551008001d00540581d103409148000ca543c40055600000301c0d4035032080d05500162502031a1705000c100080200e0784040e104664240b1100e00740141d0070f0808542078607000c407280d401e0314001c03011400b0b55039183c100548507414001440321308039000060300d003542d040e4140803c059554004100160090750300020151052864489040c040180198103070342d010707641440511803c0784107078265510710201000a0381c0d100d01ca10041591020212070a400990707903620794104a12 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 385961366 1250 385960116 385960153
    0x16030b01180e040c0b0304030c0b060a2105072103080c1b0c041104030c09020d0902031203070f08042a080d0225080601140a1a0306010e010e21 63
    0x30814107020150b1418041803107801000e1100402c10220090324521b440c0d5802080007a0a88005100c8243c01011505170380d10070039070201070880b60761002c5141000542d2002060900035094805018294010817a110082107140e0710b01c101c0c0040d00318940c0d60ba54201e61000000b040d04450803400e014036a4401000b620209e460b840c3c180c02058004160001c010494034040562142d40804020401c000b0b01c56801150845d141c1d0800103031990b840c0401c2c0070140400500007035060150b64010240c00705100055405000942e84030002000fa6134001d035106001500d02524803249104514010700b04241c44219008031354070b041c611269249501860301c00743e05055009a0400006020301d5550750b030a0b20390f1801c51a8000503064602900180c075054107000d41c20300c00f40840040342d80c03519080c0703181004144030034448001034584500c1d00c00c40d8005444450026621080b5160030350b106121105903140700408209403460a1a0b468075041480c4044a500b4001c6a441c40b00d443c00c480d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 385962616 1250 385961366 385961369
    0xe010b06030c070614130302011127060f071a0708010e04020f040f0c021b0d0c12050102090d06090b09010915020d1b020a0c09020f0d090819110f0616030b0118 70
    0x1b0120f0302a41c030407504d0041d01303450982d600c1c580c4000040c0844462403101c0c040e00c800040d60440402e01c91107500c4c001c00d081d0b114151a42404000014610041042000b9100c81e40500145005405e4031507001c11220b002080c850f11548880c4540807501518100054040360100204001078544a841803941503514482c2001c0250700011138494400e4400214603105580172182c0010074040c41d510014144824080e030402c0741c820418400400009604980d00100000c0038038075a40ca4501e07140026180041084070108020404240f50700d00500032088400d1303100c0d250750b01c04459620300f04000c3d000000704841c983d4030b1311408030f201120300004030f001c0315441d4050003120009040ca9007200043d0751108480c2803042002c1c00309210170200340c54a054406001040942c180d040c075810f14021a030084500d00da011542e025140d400c840e018000000a8081e5503180c800104141d0f05c4138401c96240c20400041c09440c80b20b507110b6131241c1c000c96814100000c160310b4504134011074407030b103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 385963866 1250 385962616 385962631
    0x2070c0b0a030b040e060720011419140c130506030c07020910031113020408032a01020a051c0608030a2c0607060911040213090e010b06030c070614 65
    0x140c0208050b8940202200c110040d20188442d6500a44d500c3e6110001084841000089881e20a0b80780c00d402113107040381580c500038001400a0b05090360841402c0c3c0b02904442407066443c103c44800e8068005003000030650340090f41c0d10700111352100d5200c2c4410141c22001e0840102d0305035112000b56000741c4951070000e440c0c088070b1040c8a80c02c0c001a02d07811000c10362000030400100c4640705034071100d100f59007031700c1e080c103658000f07101a01503034000c8112070101181503220903905010010ba640c440c040d82e4000614002e40c01401c0b48111404807000803030070002840e441e141940098800c003c0c0c2c00300018420340e0b8461507400c5400c0740348c1c1c0c4000260307001c0e5107120000114a0220082030100d298032403107070032600025030512075403600521041d210402001400b40402c0c1000e0401000380055554501d01c00740d50301070003194040d40c40b22a16001010a012005110f070094964000c0d088510b55121900540042c0d08054412142c280c0c40d14034000d021500d40070304a0081c01c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 385965116 1250 385963866 385963889
    0x31101021c050a0f0e100b031009030e010806100e0108090319020601060905030303070f0c050a140c03010e030405010e011b050d0c0b0601030e060a0c0c0506040503030916050102070902090402070c 86
    0x780f0350b2060303080d5a028540f0100c1079003480c109050300c010101d034680c44070052500000300007002c0004603041c50304040520103200c5c54042c054080c150001c0c0c0030710b81207070241d8500c0c44c01c1d03035034804001c00c80c40320000020000307480c80b0049003154000c020b113580152603081203d0030032070030b80e028517401406a4034603030050700505c00411a55801c540080701400045028500318508902700820501143e000320040001c840009410f00c1004e011861740203800c18000d0000e08213080000b0390760124240d840c0c1c043d40c42e0004108000d41c01205641c15a50165a81d0002000c070030011210b07100745089006800a0b18803003000001c0082100030f007008000e4492001010300c038108002e1800300100050705041c141f1002540200c07002c1162980300c0c42d44500040c0801d503130703042241c00c13541a5400504a129440905c41846400005944508400380c01c540841442280300060b603503942c8120790241c4d1107000705020410303050b0050602c240303000d0f1006080c6012a15458059034480d44030112020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 385966366 1250 385965116 385965121
    0xc2508030c1c06031106070f0c080c12010b0d03080402011103031f051c0206130305060c031023010c0825050706030911090402040207080c010204082107031101021c05 73
    0x80c4114402600c941c4070202040020314548405a060012005d090301c9400c0014080b01041107034030b84a42100e0f0001d612210782500d03200c0d41c0ba507a404d03189850f4402d4040480705108020305019088441c0c0014200c3d00c0c0e104400c0d030b030980b0640c4015004a042c080d030844607a00e80031b4108003441c800c5000b100300075072084c0300c003407040301c088120380055000b59000184281c074494100300380404540d05a03030583e0740b20b5000140500a9001e900020424002c40003400b1081a54102560042c5a17191800c1d0b20300e5a01c1c00c0081c02c446d1001352107e00c1c200c9403107000c056076004a25a5411500400ca540e142404946080c2e8503c0a1046000001c1640b4143c0d402401003c000c401c018181d2424104581049511842d030441c034034814842c03241c514400014215165901941c81e41540010126264944a00c045001c0c0d040350241982a1040303600302913450280003104920400000c800916100703050701c00300c034107071154090512559020050316402c044840641c1d0441d0800090010310360 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 385967616 1250 385966366 385966387
    0x19030b09070302030106080f060a0f0803040306050612060114040212010e040c0806130f02060c01020406090815070c02040c03060e0a0204061407020105160f02090f04030f02060c2508030c 82
    0xc0001a1240c1d0070144140010700c42c154016487c039030480e441e16804041d80d581d050015a0802c2e00303030040d814401c446c10300011642000405442981d00c00d09050000390740310818442c0d000c001d0341401c1c550364006001044000d0500c0340c820790303840340a0b0002d4604500940054035512007a0703c042da04028000c03c10003400394100301103001c0e00715140901014248030001c02c21115142c00040d00305103a00304c0b100d0841d62244101d507502c281c924006e6449569664010380f450100d841a190540a0080141440d0950300e00c1540f040fa9039840303101801c2540d40074040100710003204a004d1658900c0040b8040600fa85503034400d207245240981c0c2c444c14404010701d0450000b060544060b024011180142e070050256600720030741421a101088481c100541032140102c0080e400100b58400c0c0680f03e0031500580d44554026205e881050300255822641c80030100d908c080304800c10310907079440200c0004c000000c3c1909800209006040e910703803002590084d1108200c404000800c0020b2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 385968866 1250 385967616 385967629
    0x4030f11010807020c01020d050a0201060e0f070f05120117010f09060209010f030506030c010c15180b010e040b0109050603120f03011706070903060c03020c1606090b0c07050d0819030b 81
    0x200500c0540b00b140c5e5000c0010707540302202050841030000124041061a100358809001098035107101895414400e59844406000751841d400041e48a04256032060140c0201c4898020b4031080c0e00507a0702c0c003129107141100c2280201c0c0b255485a12041e0500164020141460b01402006a840121074005000300c001040440300b4107060000300802c941c0e01003501440b0080a00b042d0f1140c000070300d00440d1900b50003080d804070a01c0d008801840c80d01c132201d1812440d104e0032010001d070345c8480c054205058100e900600342084880140551501c54101c6034000c08090100c4034114026007042100d601b11400310b00ea1504003000421102088505a0301e02e040c0c0d2501400c46400c04180042005d400c50002034050be0b06d4000f6440703018400e604a507002e16901c0c00f40c42c11421954403100c0c8030341041c85181c00044404101283e6840e04104680c40a940040105003683c9000d00b071004402e4543d400342c481c18030a00140001c0c59081c20100d0741000e05540000e02e00d114402003018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 385970116 1250 385968866 385968871
    0xa030f0e0d0801050904030e030a030f14040503030d09110a18051003020303070803090c060d020d0b0916120b062212230c04020f0c0601090908040b030c04030f110108 73
    0x5440d8081c058003048150008282819610107440c21045030780d86040980e0401040c3d09031a8052051402400501d40d01440120103102c0fa5130b542c030100c1741601c2c1030140a000b203009031a8140c108000c2441030925540c01101d140d032040003841c1a44210000040036410130703034003080003406400344815018100740300c0c940e8404417080da40703e01181182c021a41d03900640741c0043c0711740320010201321841020090b001210100503c00c0d85d4607a01840b007c4065003090341c00214542c1090b00c00021403409903051880340c00c4002d03416540900c10703281210303120380310b09480c9090740e43c68030007400e00d0f10b803d401004000300c0184c1000d2520000c103003000b011907544d400009030883c1039016600203820b10f811020203c170218120351800c1244400c4174101010029000d07840ba10001d007980701c0590a0029250b0141624180c03a001d82c0d80c0d4a0f003005941d02400c000742020300030401802035400c0d900145400a903400032250509403241d4804031000c60203403080e107140d100d41910745025a400890344c0d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 385971223 1107 385970116 385970141
    0x307020d0533070c080a140f031510141818091605120d18030606030f1e0c050609010c020405041208091c120608030a030f 54
    0x80c102c0c040d41005400c0c410b0710000200407500440e1408803d64020070700c24506040804202d440560402c803a02aa01051007104040002c000c040c40c0b1641d00801798600d080008020002c00c1a2200c1500d4100007440c0c1910180300c00070f0341680d40031126500713012205004080000c034000c01c11300380841c030310580108200902c1070000345000f03805914008411095141c00c24403020f0010b20050300c1007276000b619150850361141450f840402c92003030340c4a2106850b60380b05d00c25141c0c031754410f640e0311080760130500038050041c0700c84102c080703411101b900d15109542e840e455001d091195a2289001280c0c400a07a401200d4043c12307140d00410800ca50320740b40c0350441c450940e02081800081c14180000e0310f0744000038010707640074002013203260380d00c0c040d031011141c240d802c0b2628103503280c940300c000500c854200081e2043c015540c402044821400b9101c108a81d01101d162 = true := by decide +kernel

theorem cover : BRFrame.Cov 385791366 385971223 := by
  have h0 := BRFrame.cov_init 385791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 385791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 385791366 ≤ n) (h2 : n < 385971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
