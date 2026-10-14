-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1718
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:25:17.951995+00:00
-- url     : https://prove2.me/submissions/2ddace2b-8213-4328-9bf9-1131a396dfb3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 308812949 ≤ n < 308992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 308814199 1250 308812949 308812951
    0xf0a12051f0203091b2101020a02010b03030f04030b043e060a0e04050a062303010c0e010c170d0c0903020f0d0f2010030f140105010c0b04170a050d0e0105 68
    0x80c1e526404220314051803107581e5920800b6540050032803480c0042c02c401c0c05524910b01b00c065030203950005021420035024428549180403e801450a10840d040c924455010354400940f00807045000a020407220b00705000303844056400305040708054080c1c1041c80c010b54000240d0b1130b10b9880c41c2c0126458100d0503907500000660f12946000101404e21020705805442c11401c152517200c0801c1118500070f580c0a00c0445410182050881a0400d400d682c0811101710900c4202010403009e80d92204405584039007280d189030406002d0002d080d214402e9a032030742007a520b403184401c0b10650003400401101c1c004c50300001101041c4041003051075052000414985209112a000440043c1c85c840140130002d501c21280c560301d40811403041034219150300003695250301842007862807040d401901307103a100800041d81404006841f502c11001f018150000202c006000c1020403801c850240c10b0031450552a8108803601500d03030b40120b0140010a401c2043d0089054014400e0f9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 308815449 1250 308814199 308814211
    0x50f030c1216030c0935071512090206090913020613171618090b0c0405011704030503180c0415030212161a0c01061806090216020f0a12051f0203 64
    0xc2d0740f00000c1d0f50a03201a4854010b106c08640c0480c03440c5003406102840040000d01d61b46114842011441500401c2488541d14000ca400c1c6060024809a1903d0050f81c60740c480540304042c03030f511801350000642050547c025440a000a03400c0382c41075460138a1011a0444181c0010ba040d858190030340391000c525009413007580c0000700f0410402111001ca07050107055000180c803003c1a15901c00880044a107002c105200280c20070095a001c4031141400c100d0601300c004505103940c1c010700d0b074400079000150420088040341021007042c440d500300340c00020b10801c1110349100c08410301640a00c0280e1252000340a001000c82000c81d12803100c4e543d042203040700307500b0605000500d21105841c0302c1e135900140711000c5202c5007407051001402c421440c454100740001c44000507600982c124000560062001d03103101454080341203241e990440d090b0004560b810042103002c809644801840c189004584c8107200c804103c0c500180c8840203401080c0b030340c100e2000280e20090b10f030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 308816699 1250 308815449 308815469
    0x501020c09061c080f12010f05100804030e0a050a0e180a031403040c170c0f01020111030c090d05070b03070801090507080a09080c010c05040509070f050f030c1216030c09 75
    0x3d90200307480a416022440d511894115040a04100003099142c10900e29030309944c21060051114250380c0c501e80e00200030031600c100c100c25079000000c01d110409400101800f10a00d03510f80740b0342e00d08032800c01174a8050401850280d49040c1e81703c408400345da11f1031f103401700606c06480c0700f54007007001880c00da01511200d050040f6084180d101c0e038001442920bc0d09442200800d40700c80d151144180360f16024001c000001d441010050010024440c4505680c500700400c2450908441580c0d40318910100d19074691a40f80046072000d55607040080160103803540215501180102650040c2d14070f035600e1105a8980c01108100c41061342d041022400b0140021640c1400f50042259a4441c4031020701b4100804221429600603c84034404140045418003a500b80600b5040d4031104c03a190518005910a001425130310070961100302c100740000009640483d20b000f01c40421080070030360700544c90b20b241e20f80e003181040e8801c90000f03030030460300c1d60b5001c1c0b00d00e92800c103031511905 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 308817949 1250 308816699 308816719
    0x4260a0f02040902040c0206070207061107050f0307050405040510140c071b030c0f05031209010926030d0b09240111150403050307020d09033c0501060501020c0906 72
    0x4400d0544036003024100d03071058a034000c050050321180036420804019070010591801c2c680310103070270080550000d000f000b00b003940c074504031000014040216207080d1440010b628141000c2800e216654001c65002404c18041c04108040081d0b20403c08141c1c5030100955445818052201841030300c6c0304141507030910148020800810415080c0c02c00391004070540e9030b59a6401c0301c4015641d001c00307a0050400c5080100781014400d1002e12030080c06e580746050b06880000c2c003070505900800c4046141030361801c600e482a000700040d06000c5500700d944070b40800349080d0181c498109918003480002d0f021500d9a07034480204050940c5115100640907215401100e0503c0030300700e00b1119124652400291a1003170341400e0041c0e000c0c0c2d82d01035580ca0304031400303032904910f0710b00700041040b040f1041020510480740c528641c201c41558040070701000c040300d4111114051440c8449801c2e004103410020154404001c4079000c3c0c0076103d03c50301c4a800c001482d20215442a04840404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 308819199 1250 308817949 308817953
    0x20c01050d09140f010f020309120c070b0c0102031005040c020604060b0406050d050c0f1005041a0c010c0915020a11090721061d0103080d1e020f04260a 67
    0x1504541c81909000502d1118948640e40c540c0311440c4022a182c100c00c100701200b5000780640c00c9034007030500e415451810001c1060f661114007e070020f1006001142a4116500a2218000074010806d2035515800041d8646000b50300548042540c0004030000040e24101350281803040b00c03540d00540a10b41d40c50311014007030321560300c00b03c0e806655120086816662007004440050140000341000c2c0c62a6051244020009102902c911006084011916404811501658181d00d220301d1035040f00180b038070f0035000304602c0182a50074076111418441e848824070040b940e00341d0400c46d4170704030780c0360a0383c0b50950280090141074505414204504048030a9070708003845242c5400b543c503072028990381500c0c401c81507007620381e12140308115514104410745074a40d203003102007071254507580d80d0960700d110301c08803100590b440f41e98510b4411032580400140d400d03203078419542d50821038001c0c00170394007a00440745103030035010415030400c9144450001111544004140c032480c95 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 308820449 1250 308819199 308819207
    0x70f020d0c06180506060a0801090803150120030304020102012009040e16061d01020d0f0c0c05120106060206010f030c06051e0f18010e0105030130030e1f020c01 71
    0x34070159001c6032590f100746114995403003100009070050001e00300f54240f2108000451441c0d074858015a03040400360f03800f02d92250100e0790480d240641a1901400500040e00c98442a050344600ba001640050700c03998000b000462240340300345c0c000c200d103080d080303900c240003402d00300c601803240f005014800281c10140d005209440328a400c40700d07030440c4412020100700081e00310b080041c8028103200090070442030100c5522009002030320000701002d20081c054401c0198032800c2008031100f00003405588260700000d0400604480c848500004e042c41c040e0105109180062007940000035419031100104010fa95204405052075442d1810846c0d0390b8006a00610140004510b1410014050001490403003091903080c0d031250f03007103205041c1c0d103480000068148201100d40c1001a03030301200b101d06480b014001003940c008421a180071030a43c4c41d5200c0c24241d80d00d0751071030902d9000003100b0588202142e03410f488129800110040592403428007000da40a030314100307190360003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 308821699 1250 308820449 308820467
    0xc0a03241206090506090d17060d1104020c0604080c1b031905070b0a09090b060a120e03070f1b120b01140f0d0b0103021c05030405041a120d08070f020d 67
    0x2c2d0a001c120042d007a1036850030300406803103255960380012822404150058507c8011010102c0d0454461400c0c10100b000400004001040c1c40c00005000308183c1e1640c2c1501e8100301003008441c990301e03091404040a81c03201d03045403018403e5002a000050b840000020300d14001780103041c0e05030700c070801c2c15800b0103d81c0c4200c070309024001d000328200038140c0203410f180c0c026546040b4920310b0424094101c40c01440114058a030410140400c560403001210646080c0e030000240032803240103050441c02110030041489940c1074618041c0100c00808031140a10a082402000c2c0d0b030b00500064100e504000402030761070000100110400800f83c82440003014140340d44844042001503500441e21000311400c0380c04100520a41c1861001507007c0445c45c00480314009242d00c500d6640d014074400d89104039120310200c4010400c16140d5019410701600e02004503041c0c1e28455122a031802003080050403900000b01c586104a80d070710b080d0032254010300300ba5481401d00300e0308200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 308822949 1250 308821699 308821703
    0xb06120c0405040201090e0c1201170c10030b060f030f01090c021506030a240c0503102102060318010c020a0c061805030d11011107030e061605060c0a032412 69
    0x10100e0001881f41105000320301c9034900e00041582c40c0b036100c00e003040003041078101502c814007224882814010015221100c031000f210b4645001001c0c3c441180540941e6050ba07801c01404140305004881e40c9000c3c50241902da08079450130f81e2980010360807078019040c500c0041c0d102d2107402d071005182c0c15070544c0005c00601914451070700da49503403920840510500c103c280c03084c40018544417181c80395612050141c07070800d29500740390f800000c1c03c55490048040c4604d4400d140c80c00300603514000640140e000e00110b80380c0c03604c04c60402c602d46c4000d5075000c0c554208480c01a8a0b80b002c101e1600c03295001580102080c2044000c460300c219103146c80218524488003c138040d9003c003c01100d0b90741d160340c0c81810040d0010910f094404d48011004a544140b200d40c00194024513a4142c1607829502c07a52a90000c07414080d010b000d542d4042c01c540100018070021494000090046244946003806500c01500404481c00404018017000024900f8103025102034014040c40703140c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 308824199 1250 308822949 308822957
    0x306210304050916020105070c0201140d15060509010206130c0306020a0507050a110f010215010608060607061a04050f0411040b0310020c0c1f23070f0f0b06120c0405040201 76
    0x1e80750004a4141c100130f4581c0c150020760072488250315070b0b09005090b44a019498140316103005c1e0385c0007031301c69096400d140d1030b1400c002c509140b03070780c050307502143c103e6100104005515076148009011035202d41c0c034890041c040e040c0026600a02031900e000384560280b984071860f45141c495200a40000c01407c0402c1010003041c2c010800803c4000051401041070aa42c80e442c0ca0070040104041c82103681903405c40d200d205103159952058604544482c00c18100c00da0b03d4800160407803041031001801e05140c80001c858030f0503a9031403a84901402d07036080055440e8a0702d928141501210300034060140070a02c11030506107500300f41000b42c1c001d400c40350f40f030307070001006001d07038202c00100d120940c06418041d10034942a160b01101203158104402c01e4511141300a042c12160301100c0d1109821903013841d0108004421205190303045030501700c500c146440c08460010510106035504038094001c90322900d0728030b04512402c04038400800a1007440c0003400007818000700180c0c140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 308825449 1250 308824199 308824207
    0x80c130603051f0c09060c06020a23041a09130908091302120109090b01060f12050405010218030c0a03060f06050a0f0608090d080c070615270203062103 67
    0x6404000e100e100303030404443c42001c0107030310b0340c40d10880e003041e1444010821a07103003c21805820010040c030854001101503a00e900042c0240c491943d0301c07100c00c10b84003600b440300b10100c4a05002d0401e65002c480b600200400d031050741c140c0c40c01506d840d5548900c0030a035003841400b96034056030b11144690070305400d01604100145410000c138141000c5160005010940c1140c100c0f0694003410000b141040601403645a40c49010340501403202071194184012000310b010300385081002030b9042c000d0042d86800d15003107020b90840d4015222161b001d4a0700041da00d0085401003130020094203061010740345031100760280c640c0c1c030b0381c10303010a03659500403400381c03600342c820000fa140e6440c01c0065180341ca68001c00103100101824950341109400649469200089d1600046000d00c21600c4002a09000005000851882001c0b0300c81d94000620400104c0000310300e152046c070002500f80201c00b00340140e11080702d170a0f501a02208030100d02c8410071011241300c1045004032410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 308826699 1250 308825449 308825453
    0xc260d081810180c1a040b0705011b0c02040b102a0804170d09080c01050306190303031b050301080303160903080307021b040b13050703090204050c0703030510080c130603 75
    0xc449883c0b16595030aa0f0300150710051140404162006240c0f0720a05416010210407001e03060003035000b0740b002c04400042d00c5080c400d094112503140885007212003507440800001609250801c030040380200c2c10005024450726110705c1e03009a1800544880c1080c072070b5002c2d0030044a070303040042040c41c5160742c40c0070046406440504041c143d80860380508000d100c2500740f82ca0503450903001041a200400d0007180c80104440034401020b003172040c0c49890303400c00103c05400d0515180100b00e440e403400030605030f03d07030041040490102242e0020106503141102d07181300074040d004480d0b0081010814107201c59102059004461800304006a01c030303920052140d1090f2103c10041c3e0224061405103c00c9044441425200b1102040349044600100d841d0306006098620034a54a400046189000760090f0004581c01042000345141c00034080d80c2d60740020509a0010f0b107890001070b0030250b09078211040d110a88020800b8407450002c0044144d225480c41c03002a858120001c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 308827949 1250 308826699 308826701
    0x61c050604080a0206061c0201050d060504021909061803020f120703080c01050112030c0209190c0903110306010303090e09150a090212010506060a05070206070c260d081810 76
    0x10080d4031400502c0d540b0603401c00000e01d45000904024440c6200c0500100340c2100c03494051240e42d4203080803070b1103004000890000f0b06441d4480d54005000003034440d81c4884146101400710b80c01d865580016840381c504540719902102d0000341d44404a000344054504000c00018581e80207100c000781c3c941d080d40e0b00c0c1c00e00d41d4990045503660f5010401c504d90300e00c28007640d0301600c50608001d08501c803d460041c10307074106500180c0180002d502003803041c0c410411401d144440e0a1302402040b620140c000e00da408603100c252000103a09000b00b11501e00451510b0499402d5601c000f6202d0429140804078030000c2d0150356944201480300896100100c2030610501600340001400038040c01403140307034140b9424500060749404100002ca64031141643c24214541c41e0250f01c0b41294404510320784aa81e6000d805c840a140c0002203507031004000c081e0070400040c40e00440d1165010090392404190400400700c5c88000000f00320110703c4400034040c2c0c0f10030702100e0b00317001100d09042c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 308829199 1250 308827949 308827951
    0x901050409051302041d0d1b030509040b06040f0e0f04121b020306130b18070909060b0d05160b0708030f04110d03020d020124060c0317130b0106020f06061c0506 71
    0x31007000300612100326064020b005502581c4441e00304800c80c0422071340b602c0c20018230084006c05101c40843e8444032500c03241c1c03144228000243c141a41c90785c0f5101d040c1e0b4107814500c00d0703d0b490076064000600802d41d9080d07070b40c0910f522100720002c0c0035104809030780103c0c02c0b1103080440b843e200380e60005694200021406456403c180050340c991034144080042c10040540d04160555142507401d07000010f854002c4800040d4006902122860b01801130244000c2556000c08001800d5080c0000810000c0e48010195003003500caa99400083c10f00c1e01a900300641300318000d00006541146910003258014030444004003912105000984888151001038006078400f0400c200700c80c0d0240716041402600c02c014030704001e92070042c0501645140299010095204082c00405000c0e0a2048d000e0004240b908030515081c2c4d0113042405104100303946180c810000024158004107050a403904004058409a41c407581880318028510010118810034a00c0c00f90104805000c16 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 308830449 1250 308829199 308829221
    0xd0602030a0504060507020313060311160606050325060309031b03080f060111070317040b0f03060a090c0503150f15030a0b010314190f02160c0b090105040905130204 73
    0xb5190400b42001c00c12260010988020356008001038035291207c040800c040705d10900d40415021240f0700514514011240c840a0079082064404100304e001e40018003074403825400c0710011ba4850103909030b80c1481d0801141044217240b024001144070343c2152840300e009081c400e98403c800030b04504a4400c00c1c0f001d500040320740d010700c548040c916555a40000c801d20b081040b10b03c0f040303650717601e80a1601c801829080e5031020301c841406110700f5540245280300d01685c5030051070701c0481e000d920445409100340c80091020480f0911407150401421b51039880c1d504580c3c8113010541c4c03400c54002c945900c00e19a6003003080595400c202030848259542d400c0380c513070402a600708251040444030307034181824541c0300054121310314072056000654107041c1509500501100d002052900c1ca440041400011190789000200d80078401e414071455164043c10350b60072a590840c007840c0803d60015800300f008020490b030f6504840d0b080340850b001c095501c03805a001a0403641c680407e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 308831699 1250 308830449 308830451
    0x21c08100b030c3a110d02090d0203010525020a03090909020118081005010e0f0c0d18081b0c090711030405130b121906020a0e0d051b0105040b0403110d0602030a 71
    0x14198840d0304400c00c0004c41d90030540140010301c4585c1a05500780605034203519026800b01c1c016407903540b5010070303124064004d8003c00050400440381050b41d194901c503004850b11020304860254400161100e900307403d40e590031242c6082082000140c1020381e8240e04000032503100d2007410480c150328400410001d0018440c1c002641860819114141e1014040c442848100074015529070201e40e4402968101d032955003034035042c0480200103001030950013180015860040051000040c81d00f000d0000794210104907510503695070701d81606c251034014006c003010581203030051116100390302010f0142c0e418252070ba40450a4241d02110035442c3c2d41d207801d40d201a82c2445c40b1220500034611000d00810460300c4250303010503c810f04020040b5030300080c41005a481201c2e07800d51a40002d1001d2540c45803401c0c00d55581003118407500d20940c4020110b2b00301e42c0181d08a604980142d0603103801c2910310f88518003151035500070207030407181c40c0503c42c00086092000398419507680074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 308832949 1250 308831699 308831767
    0x130501090629030705070c0e15010813020d03050d1e06090b01080705090618090901050a050108070e0115020c030a05070806060103270507080d021c08100b030c 70
    0xb42e000d90148080c800321492000c440800741d840140c4104582d84100d4a06190365641031a141c16202c00015912030301c0000d070100d042c0a00030002c2d240300034036140241e913810300c80c2d02e844110b64811801d40708021f50040b448681c81c0e000a025102400004900b80c000040803a02049410448080f01d0341161465070348180900c1107101314450300d00c54000c20328002d407032441d013400041d04038807501c3c204621070000410500c040d0285903451090442020b045201c4500700310f50040c0c00780006803503126106040100100d009000001e808048400c107c2480a00b6460055444501c8100b05024401c41c0646a0302148648081040c0c0080178411801081c403181740500490411402824003410141042c0e0200001c041e11300101c5200f619031413800d100c40d40c3d0f41c502280780204592004426020310204400c080381c010859000b680503490386c03c3c000c14940c000440300200c0c21100c0254048040205000410f4508059584a80568542d40c94580c0500c03210007c242100300aa14400c5110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 308834199 1250 308832949 308832959
    0xa020c1c05161a091507030203060301022b110a0207050f13090b100f05220b041505040b040203040302031b01140408040618061d01090b0f0c060f130605061305010906 73
    0x62601d076100d10158003030f0080d017640107445019510050315810030181c0100204000f40c0e1f003941255140c2d40c00391988500e00f004400c81e0700010070381c0549021070505c0d01004054402a10085a282c20410382c00341c0b00f1281080200b00102881011942d040303000d03460101000282440f402070310301c0c040d911494882ca4103180343e05580085810440b01213422050411030368890564101c42400404c200d11804911403294500405807405595803150a000c107682c1c4034102c0482000543c0e60130754090082088980030f01003644003c0e58000e005074000c000840c4500040d440720050345020800100f01e05c8400c4090b812400740c01e441c180c0306984001000c0006c60b81203040d425111450824040f8110310b41040607205014841515550300510400401980c0c42800301e038018042945401c1c2c1c9a010780072103c403013134101c05010340c618401c50001c20202026020304c03912500c174014072800c001189544d1040070f00805840c89800000c00c1c0c0350400030041c0c80c001c45000c2c1c072490800041300d034945 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 308835449 1250 308834199 308834243
    0x3140a020d0e03160b0c0a0816110d0f0e030a020d140f0d031508010e0d120b0a090b0907090e040807150e010b0108011203090b131a040e0a020c1c0516 66
    0x2034078040c80000308114988074142c20160035588000881d1000344c9d081c40c0e404060b60056502002d0041358001d441004e40a59000f5079030312150f090035074500078003480440c10316544e524851006035000e8524040705000625250000078150340e5481910746121007880a1440c184a03211001d0101c0c6e21410000c81d11071040d40020000d2443c0d60082c0560313074581c02820b85451100703807000f0410142544071140ca540c1c540002c0c402d504080c004400095841350020014440e906c1c03100c0c031881032074000c100418854401d44c1c040d50341d00d68060050303480b5541c4600403584100301c1290300001451610390081c245101d1042401d42410001c5041e00b81880010304154058100301d58202c6031020032004a64050700030403e843d60031403c140d50352840e40b82c04450340300550000000422f10841e0342c11800040340a00100ca10301c0058503010380b078020400b0280d00865880505640c02505440c000414422081206040904000e8584000c43c1400006084040c4041e608581c1c0c01c41404280d0b405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 308836699 1250 308835449 308835451
    0x8010b0103051003032316050606032e0207290915090c010c0f05070b070b0c041518030b0c0c1504020108040f03090e04060509060703140a020d0e03160b 67
    0x1505481c90641c02c507500903106c0d00c0c00c8038070300c0c8109030700d2907035003114400e14421960a801d041c00444044803440c038200741d8074003084540d00e0082c040e83c0011850001c0c421905005080401c6072907400f100900d1840000303400c041401e80b1012100890800302c01c4a02503119141c1e11107403080105031410b2940c81d80b8210440f800d15412410490400c000c020000c40d641c51a440d09180c200c0700500b03a41820000309441403000f6180e8020b14000166000c407680081080501c151040b65a55513a800403031058010380c8644101c00c4074007008845d0070341c030403030b00e12071311081900100701110780b207440b01d003000181280e003507881c030034000b840d090340c82c0c1c0c00c001445007540000441c1100e441c00da030000340510000391000304040c3c005c0503080700701402030034150003500c0d4408e2403c50900d49403c0070b0000e440161440c1d07906000349000305252600c00e00440140c1504404034002a8480b44601300003540004e1240c12001d40d21101001c0601c0c00388010300685d002040000031005040c140746000e140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 308837949 1250 308836699 308836711
    0xd080402120a12091d09030901050903030702121f06080d05070624230a05221b0908060603070b090a030f060203090c01080f01030201080403030b03062703041a03060a05030708010b010305 82
    0x3550003000446c0c2000000c94102031000e2800e0740c0c5809041001c20f24600444400030b6104000b68902592441c00180c00b41003843c2100321044410707074402d01d44040701c09600400c030300d940100a1054542d40200018205188590000208820708004030402042000c01282c014004030000f040071200b40d041c40d071291204800000d44221300000040c040c8142031080380d019000e1040120064110071000b11007200143c2014450031115102c100b0541300f80c0b081c182c1c0031907405140400c0f5408001203103442240050020700510f410308240c0700158200d99130031944210845d0001c0005100880c1202c83c540c0704d403c026840c0e0501d4061282440d400d2000503040103149410003194641407258181180e170282000052a02c40303090450240c40419560744c1c142c41500c05010625491080550706030305041c81e00f80c0741c10f51107480715449115501c120080d880c1d03440a144030118080d0001c6030003c1d401082c0d05100d55444021a08100b0f050303000116596403186000913558140c0150342d4840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 308839199 1250 308837949 308837999
    0x6010e040e0c150f03040f08070f0606090c030509060708100816080705010806060a03090503130b0a11010e07140f100207080d090f031e080310170d080402120a1209 72
    0x4041c522004c0f103408000c00250845070b046d408581800b140c1d100311108030ba08070704240d11100140c2810300181c8403c0c81002001d5141100f0f07501070620a10905004001620240141c9e40358048100d900140207000c82401c15070703581c40007441d80f03030400080c11072000b51003001c96042c2c80c1950302d5041019aa01203818000800e0801c01c1c280d403910200c510350116401c00181800aa00340985503000703441ea8142298205040421206051400741510308815503503062041d00c601c110700e00f079030504c0000c40071a500003a81885882d03207590940b50884000f510424180706224001024590280b44090140e0803541003849000c00031322548201c81000d080078203841d40380c560101c0740c241c4c43d4440640f1001390b401c4400d002040320480041c015412030462500c81c00c000c0095500c82074944200e44620342500103526800c40081980c11031440c0d65202e5070fa0540e200e8090141110720480c003111207002e130000c100000b5001e001e01d0504002550303200709074942050307440d0741d1601856007500300343e03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 308840449 1250 308839199 308839207
    0xf06190f17100b0d02010507030e04060b09101d0409060906020f04061806020304090203090c040c020d0318020d02010e060705150402010807110c0f030102040e011203080c030108031206010e040e0c15 87
    0x65224141044c080c0e070307420300e425995241ca90908443c05407141843c02d900c1410440e00058181d030310000b0f00700c001d00444401c035582e4400712046e0340060341003180c41ca058440390104011850a0fa2000400900420020503110380c01e41d14401280c1c41110591810316002c901401840d5101042c040b00461000d4480c400383e08040000c2e41c0c901032480382400309a00080007450b440801e014454030040050b00904c0908107418019490721110038441c4002440e10140300465803075a600d04d0301c01c64001c5e100d1a0000383e190011141013107403102c202d400074000c010800005800700642c000040c017001c160000f508043c03000400b00c0f017000d0007200c1004040b40300b401c0c610b41e01103007405207480103d800d07002104442000c80c0c0a8002c0c0d074003c464510008000150f020080c032200000c2c14480d55030070000355510040114240800e016001d0f15910601036040100171060b410b6030043c50505004220300350034000034082e144403054010b9580c00002900c101814a800703029199101c1150650074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 308841699 1250 308840449 308840471
    0xe120a08040204020306010908030a0c030e060412080702210609150402181b13050405010909030207030b0604180f020f03010c17060604090c081b030f06190f1710 71
    0x42400c0604040d22881d400808502507130f000300f01d520010500d01064a4480038026405009180045801d0b000b0030a0103071004164503205044071f00b514850341400711111782e1512181143d4008000032030700b00024406103804001c180e0003450403940100010102c40c500168254100f01d04060f42c01e0030105054180001a520301c041020034600c0526124170950764600200340ca003041c0315410080d120b0000e444040114400360110a91700161028001c0d86d90385c440b410100c0e000703082d000c1c0050300003801c24000070704c0003c55980c020340010000314850904044d0303240b00b00c0d104001110000d414102c403e04608050684401203170040f4020400c42d6003201c2c0103400403c034620001c011390f03c6e450004485654120aa401030702d0072100420a001c11108050300071401980c000174402c600c56403010b6042b20703440403640b194a18262110300d03038541206100a010b407000d44041305840104000c103c05483c0f0041500400c401d90214010241241400c0d08007041c403a910001c840c18005000340d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 308842949 1250 308841699 308841707
    0x6232206032702030a0605090a110a03020607080c010b0604090f050f010834080705130507020c040b0f04050f071101020f07020904021207060903120528050702030109060e120a 77
    0xd014042c40c4080c1868060034400a42803100d9010000d00d058504014418002000181c141c4624418444108401c0d4008100b000e2002c01c0d202c020742c440000c011a10000e0052409010380325070103000800c20300d122000080a0b80c0054000070f460a81d546070074010b44015028640d004820300034080c00550503c3c3d41a40c4400c0a1104d0034801c5001e55000e42c04950120380c1040c2080000300145d00150710b5125950b00c50089226441c8201440194261a180144903050141c4441d030018810380c00c042e006d00000d0401000120b500c9041c14605441681365400f8003840b07800d8042c2500f13903a103071080001e00018004882e071480c0340c1c0f0500a0311840070628040300d54041d0110307002030440c0d0340d52001031481c220500d400ca0450103203e0700023880c960808150001d1b24407900d001c3d02030100300d8000322800c0c0201c1d14001c59200c1120250443d10442501190580700e140c07034440e14050407500440d081d12041ca200300c400c0b55840c2c0e40d92055080601504034043c1c1c1c00325044d4582003e0f00b900034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 308844199 1250 308842949 308842991
    0x605070512030c09040203011e0812090f010c020d05010b03010612020603040204020d020405031e0c0d020f01120608030412020a0f062102130b09010315050a0623220603 74
    0x1400c90300000c0400c00c1c00250310300382c50844c030340100199a01d41c0c603208900c100c8440b000d42c4407005141480c1c0450700c0c0e680402c58115880303042c100c940c1809109003c2091000803070781e156040c0304030340e602a00980c071491a0001e03024000c01c0082090710002c0e09140c03c4038004e0340554030b800d041c200b451006a03110800c40e600690115030141e02c03020b08201050007882242c0c0700304d0b4103110380f40502d06d00301c269281039020002854255101c1e2134480d02030200307082400b1130080d400008114800f03069030007118408080382c00d9600000f042070311134090724a5680590410100d00d0b010b03000000442c50200350b01c0014082e0300c5104800740d481d000e0060001090700001900b0600300000c0180000000e074190f03210a80f485c11548020355582d401488a90b03c400b0140c0d00007800d2141c0303d0744640841d1180030403608042c28221441d4548082111b0b4a100681d00f03603140032600042e80c15412a00c400307020100b09080e441e04c07080302200c20940509041d0f80c000d806150500c00d005071041c0544d00b00d2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 308845449 1250 308844199 308844223
    0xd20010e0d03081b0a21060f0506030403030e240108010608060c030702150406020301050f0906030d140723060a060f180e1005061011030a05250303021306050705 71
    0x42c80e060312a10540c4c4100222260003140081012490f810340e1903001e50b49513075031440e0b000703103401182080020f80240e403c103000c5d2081e03008002c1c90812250410000456105019250000e00d40c555410041e00f080302d1460459040c0c4440c584807515480d0301c0c1c900500400e41d940007007141900d4026000c0d11400001c040307200b070007404400502658020300891009446d42c440c1840780c0d1500385400c00c0290800e00941c1d0107800038015100f00f6007031109545000380c074001c00801a000400800700c605425011582082140c1070018000042c400f4041e9181700d0781d80c00d401e10443c2002c800051400d03130018002114642011070401480103034800000c1035070031403031880e05003080c01c0d8178002c0503040310300c160f0055100364120b20300702001c03036030151380a02e504441450848420a07c202d40100c0c0301600709556800802042e5407250080004017419000c0300d5000354885410b4126100c00e000180b0140e0200343c0000d8600c5803055200d1005c0081c1025082c01420320400d030301d890b80e80740720903030403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 308846699 1250 308845449 308845457
    0x10509100c14031e01060507030e1e0405150306070815240a020f011a0306180109050616030b0d050d030509070b0403060b13060b0f07020109050d20010e0d03 69
    0x781559042c41480d015100d80c000300d01e00c5039203040c201c0000b400840f48100d0300020444d048004980240710301d044940c0a5059500c2d0007081103260200310986481142e00d54980c0722200101a8903100c90017001c2c801e040300b4441070140e1000c0002c0c1414540020108010450324000700304400c04000054160030a081c2d48841240024000980b440c0f00001c03a40d482c1401c011071202ca000c0e42c0040c400c1c14120030a030082c41180b680d164615000e4481501c11035164001740005114040c450740005243d07500d91002040b0030340741d6102d150400c801602c1a0a0341c3c2c0180c00700ea041395800d4012002441c07019110740300349540c1c07901c90300d444500d05007030102055100c901150783d0741350800c20f0030041c0c00461300f215511a40d0f45010340040c0980c4404500440328082c000f03580814a00c01c030300868040e03071626860300320b092100e00d0042c0e20080b8100c0c14000510307400310300d54460911001d1424070800c4201c001115038003c42c0110080418031f14100700e194405020f00b0340301c414000144a5160038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 308847949 1250 308846699 308846711
    0x80d03020708070b0a090c0504020406090b0309030d0908040e090316020906030a140f0136060e0304030305220303120c0309052d01020301031101081302151b01050910 73
    0x60500094415035402070701300c49052080c803000914550250300351038801c908a9000b83c1da038005000070b80c01144030f444080b80e031102c2c0030011000844021544100e404095034941640c0610f07400440350002401d039000203001c6401d001c88900d823520243c10400041c01141000d840e138515800030881264002d00a4145c3c00110321113032401c10425510036440403200c11403031442e810304da036070f45410142c5001c15800d2100004420141e920034510801172071015892041920020106516a0180841b1220360341c69000c60407442c1030010304007035482959069070f94000c41000c05031000140050101c0c0e030191a404000098000c80c4502034107403440c9000c00c4100c1c588109070020b254111029119000d1440c81660400040314000404e40854046c0d01c50400b04d4861b003800c030b000c240001049007402804c6681c0c1c42d030050381e050381c2c000228085182c900c1000c0d80421401da00e415510001c0440c00700d00b092001c1041c4a6100f06103201030002c020303900d848040c00d56502c12100340c00b005180d03145 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 308849199 1250 308847949 308847953
    0x21810050d0c0806040c080f0408071a01090f110a170613060306020306014515020106140102010c0509060f04030f1a07140a08060103022104021009080d030207 70
    0x9880e840c4003010010401c90b010400041d025101c2107139468810362402e4002c68a850240320094000e010005000050340da17603590b030f065a41e200143c141c6141d00050800158003211510b0036000e0414079601003920074081000c01c3c00c2d03440030711b044203941d40140b2084520715807000c3d042c04400103004028003240c03111004034020341e0900e040e000c0b071f01e420442d01109010040e001980151002c0e80c81b01501c60800d6088209849c2e0540020803840c0c003040701d0704204006007030301104048210f003aa203d13103a68807400f0009800086540c00580d4503040c003003202000c0741960b0383d034086080c0000d1040c4820240000c005100303080c951480344101148035442c070302598080d50013541d482000c030b61030f00a05040c0041d00718507940380801c49211060015804610841640c0c10603013540071154100741c0301c2101515100c5000304494100b581c01e2089a011642c05a24192104014002c150a0303042a0051100f14042500d4070f41c2070040c0c5400c10032600400040da91400c421520340140c8881c918 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 308850449 1250 308849199 308849207
    0x604020d06030c1d04050d050d1d0a03080c0a051c0f15030b010f12080315100906020f0303070f0f0e0603040b071d0a06030c02030f0307050306010909021810 69
    0x522009a0001e16000c4040200303e00006034609452012051002c441000b81c0700441c4ca1104039001012034203d020b00341e212502030340140105480588020614901101517800c03104081c0e107440003294015907555090541101541d904220901c04007407410040303c50240c203d200b01d0a4803020161070500f40310724050b00d5800980204040d50003400002d00540b10440c1c40380c0702d4042980c0701c40c1c48500000b4040f00d54031188045075600308018002d8841c03a04c5468240c3c000401d502c081001003004403010707a40310760050103003803100d0321280302c12410004002d1400010b9803a01580e94420001c0c8240260821481c4604d0745d02032801106445000c841101e451074070418154001034044103000c10840c41411041c0b08603d2039881a0740707800039524542c01141d4460718607400c1b950100c07080c40b07041d1280ccc0000083c281c3d01c0c0112858030144100d09074440e48100c40078800201c02109100e01580c2c802e00903001803400c500300b0360804200000d000b20325919442c0d16480740c02041d441c08542406 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 308851699 1250 308850449 308850457
    0x1080610031d010504020a0e060306181c02010e070609030b04020433051003020915250f060c0206040c0b0306120f0f0106060c24090f0c0509010e0103030215060402 72
    0x81000020070400b1108030680a04010b8070202c0c800c0c507480d40080b0b119032200000740d1090800800410721500d075454400185205101d01c202c0070300466039000306501c0d0800d10113100b001d5903800091b02074842c10255040200a4000d141000740428042010039160024690020740440d40001c80c01402c1010500d03102c1c42d02c48038141038480c400400c464094154602c4100d03142030318030416141003004110100d10991810a070321100320f03110800305d810744a0250240c80107148508003058400d1080b01c01c1ca00664a0480d0110f41c001088002c0010500400c8042403140c00200001c0c05c003651100c060906d61b0041030340c80c140100010742d0540d80c962810480c1c030004420f650100c807910b107289490b01010241100c20b9802c148000500c0740c442d62036003028540200c1a200550812515100c00e048580072040c0116160303951000852a40f03810340302c5880c0f1620140e469649000d05000c03030310a059001c455071032454001080400d4000c1000d007120b104405203040c0310b60f00d2000080080c02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 308852949 1250 308851699 308851721
    0x102070b0709030303050106082403070f030f230a0f02150f0304110f0109030b0411040e070608010b0a0f11070807080f010b0a0303090b0315090c09100e0108061003 72
    0x40c0140500c0001c039041041c20341038138001d60703041c841caa8a564081c1c0f02001d00350f4468201c402508091400c070b003c0ba03489414225401002c0c0d0300c40903903031040600a4242c03a0020366405007202000810080c4014a2802c0500f0615440980700d80c1d090f01d0f5500ca0541c3c410150981c009100d0702c2046690350250050300c007400e120010f40391201d440003843d042d0000c0703c08550340d15681e40390b00413906c0c00300300110100b10140d550b4400359040d942c400c2d0090201810440b10149254001c2001d545c5500921103180e110380020450b585c030b466001032500c203040e40040d01180c01045800000365200284030001602c0e4140180e03400c1041002901c0c1102c2079100c48800e00421001280c8104045400012403400c0c80003885000d50580420511400c6444020701062082000700100c045440c05941d0000d10a003004034070400d0780010500c02c83e001c5840c8810b9020002d48800c0601d8042c001d141e02c2c196610300300040035102c10018086210140005202c1c84001d0744034035401c3d22030f8000380c40d085 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 308854199 1250 308852949 308852963
    0xa060302040c08090606011403130305040803070627020a03110105120703020301081b030601060e010c17040e0a09050a080904020f0c0a0b062b02010306050d0c14042c010207 76
    0x240b02d4980140041410f881c58502c13400303900c3c00b02c0d26a601c10a01f0300c00c1690a44015442c3d80c40e950000c031013041040f9070032030500409000000b50007100f840540440c038050507010903001e0018110b20700410045041107414042030b80d41c1005611707210f20b584162a4022044041442d5403030041c0c0e00c5000742050b80c1001200c103800c000c1c58503410340145040714022000c86100f81419404040f10064280c0480d806038405001080841e119141c204015a01070400005008041d01c50800e000000740014004c098001000c016080050900550020303094100704101c0c40b079555203a4131a102c0e6040586140ca02145501c850382d9154125014101003031200d680c1c1b41041848151a170f03070040c03420f84045240717a00080301030422940843d43c400c4401c070070100d2841d036030900c0c2d41900318855080e4105a0340f42d5000ca0180c988210b0120182d01581c00104900e1034514540e2120000480c824081c500700402e0141e801082d0407901c00e400f00b146040c481d10301032059045d00a00030300303030050b10032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 308855449 1250 308854199 308854211
    0x309110d150f111801140c010c1d030c0111072303060609040506011a091302030603210a2102030414010b0102011802060d11040803130f08070501080a06030204 70
    0x45050000e521941c1c104060050000711600074044500c4082c540c180b86008001078409400285190740080405050210a003144165440031907088a0f030300e4407040e9561202c03429190340080c104a140c0b82d2818070100003100d2100802d4036010210400b82c1800071100604180071401d11a00d40034000700c007101101c401c80781c4021113007001c40003651802401034801140590a090106a100302e40250092040e6403030030000c60808681c001e00c01c200030380c007800103420b80c1e5036000c102411100c0100c00541c0740d04040080504018000114003034510703245006903602b003000f9003580c02201e0503040004c15000400000721003000701501c60803059200008010400c080c0d031400e0810303040024002c21500042100590895035240001c250740d506005d540030061a0600c000c00800c11803401c0803071180420303000d07051141c026400c80c00c025040460741d503087c2c036407028901c0000c20410b000e04030254075000c20704c0e0b2100211300442d070400100c500003c0c100c1e6050f4001000455001e4410440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 308856699 1250 308855449 308855453
    0x50a090c020c090a0f110a050f0d020f0310050907080709060302090a09020406081605070f06050601180305010e0f011a06091c03030b010e03010915050720060405060916060309110d 79
    0x18185c2140c0742d5580d034034000c1c14040c80100c0500b6140710324820340750355207071154480c0c0158458000340c0c0440b103090b40030464010207580100186010318031411481d807005060100308084600020b1941d420050303087d04200300958801100412a03000707080060340c510404000c102034660a0700042030041c0002000901e155112403002c0c8172710001300038280d820703030080d03000c8581c2e204280001d07099017444400400855125480070380c000c6c80505121202e144100e242181d4155550b0054a0341c0c1d649000224080105018001d44441c003000200503c2c807030b0020a12a201e045503c0d00c1c020100031846100c1c81d11440300e900c008100000e100d400f08541481c0c000d0141c640084100c0c0000c41d5103c00354003a0605020301001654080c105210138401c0000480040400810201c204040411502c4010a000f5260000d01c40140054031281c074281c10514600320300a803207c0c80c1175008102c0300c99440592007060058038100e00c4e01040c2401d0500702901c0a1a0b10b000080e1f0140441040d402 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 308857949 1250 308856699 308856701
    0x807080304031106041104020d0204030b0f0402040608030a120507110f01060f052d04110f0c010e0a0209010e06150d0b010f0905030a06050a0603170c0f0106050a090c020c090a 77
    0x2101c0d600c41d42e100000d0b03041014205854a03401d580083c070041c0703811440303945442c1940142c03c00c600408001410140e0ba40c44182d11360754295520002121200140f10030b5040502031180500400c00055280c600d40d01030051001d001541130340180d903540c50109415038480c5440b00d2138642e5141c1121894113402e00054001c2400740321320500a4008500003441c3e0802c01ca00041041028170011607861104082032519030303d550003d0351060b500e0760b0422103124107030050a030703030701882a03c80e884080d03051700c00b404c48032504a101042d43c442402140140d99510546040d1101000f50014546801011402607600220099034014002c59030b011400640c0c0c0c032039121800c09036102010403402c42014cc03142c106500800b500364004102e031402242440d0003c0fa00b094201030001030880c0d81352100c2d4142c02158001054402c0000303a14440784100304800045128010000c200c041d02c3c00000501c0c03c0e4051240300780700c6840ea00c031600068003d005204542001626840300d503c0c183d02840 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 308859199 1250 308857949 308857951
    0x90e1903090608091203010306020d0603020a0902040501090f03020609060d090b1303020c040c120c020a122102121801021b03131a0403081c180b07020c010c060b0d08070803 76
    0x34006110b11000130805000080c01d940c10130b46030140c80703141d6400d6456200c080e41c4890024805036427a11000801038466a0002004010030f0f440140c50360b0415000400654aa52101e6031948401c00184056561107041b1007a95800311980341d43d031040303050010042c21031400090401203402c0c082014003010500710840d1f852003503003034542e240c0f207080c03c001c2102e280c010a000043c0c0051907000c0202030f10740c445020b520980c01182c0503601a0740c0d480d031889200000c00c0d00003c14003040c0c0c5000b220441c5a0603c1910700701307029401c0c2a15010701c01c01d5904014194202140802003001d0000c40c00e60442d0f400214031602031041229501e00c0c265264440700ca10f0062245824002070750855882c174040210305001081c901e41451510781d0802c035003000c0201a480004060004141314003482841d00c0c090304070300c80201d42d62150604d810725100007041c02095400c46503244803543ea0110005d032401e0380c018000a1901003c102140d0010720035800140709940005440c010b200145000e1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 308860449 1250 308859199 308859209
    0x120c1905010f05070f0801090507050c0304080f010e03070503090613120b010e09010608071203200a050c180a0905030d0e0c1c02100c060209130905060702070f090e190309 75
    0x5201d66100d140e002c0f21038107260117114001840c5080103102e1501603420182d002602e5180241c06c4c030301807a0890741035034055404401c8650050902c0070541d1070038080c050500380c1c898040c0d0b0502000da1562900d912581c2941442840e00149170040b041103014402c010304550104540841d400e441c048522a0003030003881d501060034000207c20050501564058a61541c003070119075103002c2a44120b80d03081e403002c50034090810954140b00c803030640355034254940c00004002d48241404c00c10304101ca1211005c0c05041d40700034030303140d80340044c1c40c460700f02030480d9000900c0e0002d420014194019921a4404d9904040003441c3c03103100000c94104400044400d000c240b00c5080c4101a01380503500c2c02500000840101110980a11006101e56000e420301607d028004030008014090114010b54996a103074124400e001d820044c080d8030400703c2c0010000341d0304015200d00d10280a104090341039483e0007032500b03c5c80f002c2c490340343c054019043c18a02c4510500e0054600074050081c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 308861699 1250 308860449 308860451
    0xa03090201181805180303040b100e0408040b1c0c0513120b131401060e0703050f091e070905070503012306161103151005030708120c1905010f 63
    0x2c0780144503805007001282e1844100703c1551001c01c40e948080e100040501c201d002c4142c0c801a0035031001e1004620841c4104c80001d001d10701111070300b403420b186030007a0040d181d041c001c00c000070708820102c0c0c0c00d841801100a4a45121940318003000c04003175003d104071400c00503442c00c500c3c1c0100c00761001000211501680c1901d840d01424490503890003c0c0c05c0d58072030fa011441200c1c1c290f90a0b40002c0c000d014040f520078001401500359101e5a0006101100711001c001145600d4410545c00110351000d1210301d046c83c0ea89590b4071a0300141032514584d01850142101c4404c00100008006078181845185422003000d00329410912943e0044001428034590160b04c0c014904412040100304609280174a5030056490200c41c00031540c66590302d2280740e0590341000700d01903030070003594940580c1c034120343c4602c881e2026034002e030701a031f000d03110074420241c02080381030000010300e01c1e503900c03078082400b49480c3c04050629840070001c0c41c0c0801090203019040300e000000c04200c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 308862949 1250 308861699 308861717
    0x150209010210091226150108060913080306190803031005030f030304080306040e06131101031e020d1113050301050714070204091104111215010f0806010c080a03090201 74
    0x115403da40c4800f00c004c2003105506a26903000e4011041d1442240d052244403090740103052507080c0c4001c060f10202c40040001c4080e24032507a100c0a529444601594100d40c0c5080c600c0702881c0c101c0c00803900510380b9902000081450722100d050078001c0d048030001084140d07031081c00c507859500035640c02604904460021500d8140024980309400035003008501d1503850340c50305a926000034020030743c444d80301c07001c040c0004410030043c1e010b4800403640c1d00a2826074036025410701d08030450f41e03041c1400c3c9850a50286d140f19503140e4801000407001d42d445010703201440c000c2c0801c1204004c6000d020030080145c0005140701003da03401a0001c1151b600c07078280555191050351032106500204205c0c800050500341c02000c046442402240c49040d20500014150391515011540c110f00204031002030030030a010494004a11801c500715201c00200000c03d50404e02c0200d5041c0070a00c0702085199200310f0594040f40d03040311159445468002000300a4921030805a0000792603107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 308864199 1250 308862949 308862973
    0x305040b090a05120c03040315021c231e090609070b0906091e130e0601051e010507050c0a17010e0c0121020d0f020702011103031905131502090102 65
    0x1030082e519034000000345000c0c2070302d2407950101d51005002800d540801c4c48000700181d4079650050014049210140e121f05010f11780c001c54050190200144905100500d8104603600000d0b1140c14049281c40c0c40c0d96868440346030607012205030903001c08180104100c11a01d000c0b80e00343c01140364500784c480301a903d0070302d02506d001e0181840c2e480807080203130310b01624100100c0e0350484a20804a800c600e60580000c01590b0907000f00842c007901e4410050020714140901c50140608440b0301e01c6050403550707080e807110111080d150600c100042c1c030600b4080204a85040c90390020011100c8030307203c0c2152469101802480c0a00d50300f403042107000f141003c24200080c0c401a9200c440c03014a22a58480100c40701d030008038501da081214581030b050500510030303074022907580540d84038007500c00146101d41006480400e40c0082c4103005040101c1c1c0040c105001c1c0501c00070801c0e480780f100380039070008001c0005000100c2c4001c06154001c1507000340041c0d5038240c09070b0ba241a094 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 308865449 1250 308864199 308864203
    0x30603020102070e0433060614030402060318010207030f0e030c30070b12071403040609081204060501050a0f0e010b0a0908070b04150e091b0c0a030305040b09 70
    0x901000340541c0096805114110203040030f50f6201d4020b40440b181e0109443e103030a00501e0f401034500358800c046240a040501d180900c4d00103150518010929002059000e040b0b4080548000c0c0700d11400000301c0c441c1d01d581c1c04404148051200210740d0340200c0d280c00b418800c03964280002090700320240d00c645190118040c040c01c0303005032451001e549d2200010f401c85203e6400c03600c03c81d202a03101d544c40e0b8410032100010b4006101aa030303480e80d200b1003e0400050041c0840d08004900310009042c04c00042500d80055004e038000ca440c02c014a404c400070300070020401c0f1040389000c100000c0c4100390308200d04980090710008106500c52002c1006500320380140c4a40419000041103d00112001480020358a1400020301e40e2a09a0982030805592103454546800714041c4511078020844d03034054125402d0920b0708041070404103901d080c00901c44030b10308601d90043c0d192000c8000c101d400080980742a2104c5d1032061402a00500080d50b0980b04c07a43e40c443001070740300c000c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 308866699 1250 308865449 308865461
    0x601050910050123041703030414070b0f180405070e040f0b010509120a020a030b040312020a09030204020d090623060907021c020c03010903050301081c05160606080307120f03 77
    0x2040e5958038249013048003440c0307076006409010385240420400010703504011841040d240500c80c0c040c0d581c0b130401d410700c80d00c3ca540202e41400281c00201c1c2c02c106440303120040342d0b446802200715035120040c051181040300340030f185142d013003030500301040007859105400c0e90507607400325002c02a800b5920041c4044130501546207011510802001300300e440c03c3d0340300030402d003258401c841110601d41c2c040783c0802e500da0300440d0040e441d00180010142c028012921410341040118180404144003c000c008070b4032000c1e002e00e90004803182510401c0d0004000c550f0032500c28000103410503a000986c418001d01032180d908040c010600d02e15201e141a40101001c1c0e005010707aa84ea05003d1281e010040380980651144007061092030724203015010f1142d000784c940a80f41c0d0b00d482c41040c1090000003d0b01e41030700014a841005a8000013990794003109036920044400f45854100c00901190700409094807012500e8020000200003203520910725503a0704003c00a40c020075030641e00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 308867949 1250 308866699 308866709
    0x150c02030409090206160f0b0a1b0518090c0c07050402031009050c12040c050411070b0f0903070f0c060306050d11060a051603030e06090a0c05040c02010e0f0601050910 74
    0xc00c0300b08081a2142c100b200194002805285403034281c1140020010384007100f1100080403e070781e20300f40000c2da07107041e500509050052240d00c1d03105c040c840c3d0325500341841100740000032a0801c80002c0307000d1703030594550002e8030a01303450070a40e075001520381105500200b45c1c0718107600440e02d030810307000340c034000c40301007410300e2009013491002c80207400001c0c40c1c140c08240c1407089004140c10490326a0095002c0d6081d004040e00b018280801e070341c80c01080340c080c0607040107224001105205400c1e408030351399511011036120340c3c2d10182944203484000e00176103040c0d54034105000204114604446da0740e2800c2000c10340e200d061224520000034081d1010680d42459003103401d02900600c4d807002d42d45031181c9480300782c0365888180c000c00042600025aa00c008404c22034040054035044161603008011000f2180e845444c01c070014024035020b5500c5480b0310307120358000d410a400c00c5551800755949141203d055554680c003d1140c01d10072081100400e142c0b4881c444070009840d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 308869199 1250 308867949 308867953
    0x40e2a09130207020102030c031b0d09032102011b111501080a080304150203130203010605040219031505060c060a050109020909040b04020f0613050114090108060d0302070e01090504150c02 83
    0x1484128100c1c02504100f0050341540400c010ba285401001c0c07000b040c80d09000900342c02ca210084c1401494804108045801d0015481c01400420981081c0c60b0300c0e03c000f400c118403640284034040303014101040f406610920580341c0b07848020782059140c10b07000560801c51b0503010f58049072054900c028440c0603141d40010103014085404070b0000c40e801405110900351600c20b2503240005c80c0d20498414407203001c1404460308501c0c00380203000c01841d0031542981884401c90003602100c01c10a03511007450b5131820b20141d1b01016019a000600c4014500c544450800b0140c44d00d8140490742840154500f10000c0b4800c0464401d45910035001380c070b544250b680b2561403900c0c14501400c00d90b4130855050348192a66200001081004860034000400c40c1c580303400034101c0390341d07800000f03100e03202803200b01c00c2d59a100c2d088035803080c011541082252442d04003a810b1055a40101803a0600e510010030139082c0c0343c201601a0b84500c40c42d8154841c007070080c00803207041004140060b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 308870449 1250 308869199 308869219
    0x603060a0e090318272206140a110405040b010903050a0b06090c0403030c0303050c070f0804060f1103090913060903031a031b040b130f090308100b0301031502040e2a09 74
    0x45401720511680c442415643da100380c4030000e0304c5d8548480304070812500ca98440c0b44910a00b06003a070416003144c00e20a0034802005541c08004081c000c9001c0c0f41e0081d65140e110f00300340d0b03201d0040c0d80b00960704582a56001002802e000c2500541210002d001e604902c0124020000700c2c8102d80032240c1642e540c002004d000d5a048014060141c030340d2216043c14884071010503154a056030b200c030300c1801802d1343c581c40c00c80b0240091000304641424402c0b44a5100010380c0e01000f11000840100c80c071003504d45da417054480b0705960200b4040d0125142080c0d90b0301709501075101c0400d9120312100e094071f1025903000c00d0390314145410002e02d465968160103646041c240c000c600c3c041d034002c00080301204001c01d20400c542d4600f1016021980b610f124000741a080704409030000c40a17403225a0035130425190000510061000170300c403c220f010404500d403007a505850151140300740c042000d04100891941980b680e2940001c46d0700036881d50020f08034480c04445a11708041c001d0021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 308871699 1250 308870449 308870509
    0x409052e0b07110a0302060a030606110d0c0f0501110705010204140402090f010809030c01110418020f040e0403050702060703120b040b0f1c170c010605030a020d020603060a0e090318 80
    0x140340f0800e1500b900084052008030040e910f070005402c40c2c0034182e40001c0d0b200e25064004203600301d5172140d01c24a07044103800c4054030b54401a5007801540045240b00d8925481c50035600525003280c4071005075101140280c20054190010402c869204206c0c3d00c1c2002c140c0c2c2084201d1044a00640c0d1040c840000d006243d400b441e07403590302560390402d030303070503d04120685425035422442c1b41e00300b01d1000030300740800400c10a000244002e820001c6040401780c19500c0810b02c541c1c020350398071f0030441000904240c894000c0b40c038800c3d8060308042c0c58601915000d408240c0c5400181d55031802c0c01e2061001d400c00340f195241c5903400400d0f031004c0100c480e040c0000d40710180f81713100302a0280806d000203d03900482941512404096031943d66124280880c21101c4603000a8480c1e048080d225016a40d059810800390350102c900503a00c2c2ca48400160b204007417a4410081920344208021403544040050309810400100d03076a903405440301040403a5041e40c100019881044590f1f8003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 308872949 1250 308871699 308871713
    0x6340c0f0e280e03030c040305011503020105042610050712090809010c020423060102070b0708030109020306011b03050307110c130e0a0f050a03300c050409052e0b07 73
    0x2002c1032840d00207410661450b5040c1150b00c01c590b2580109400101001040000d110b502801018508850045411680000c0c920702c241d22a08020984900e81240140607041d01142c0121003a0700310b4071602105c0d0303a544040c04044501d0404a005120507804219060046c15212a0b1146403140707010605801501c81c40701c411000c0e038005030b07100f03800302d91000b000c1e000100114103191120310703031b25020b80020301d051540d41110640382004e02403800002d80710010390707040d0340c190000581c883c0d4408004031115503804440c0b54624103101924414590008000c5001d9215a80e0340c2d0310058560380051354032800003900c0d07904800c0906043c01e0f4004550310140485c101d290a41d0450420358964210124243c0024ad455801810081c010940c04c000709140140d038004540d00b203800c1200100c1c1c1180103142c0405501c0d0780301c002c41c050543c401e03c21074024010310701e410000c1d401e003801d0030454110180400914005070100c1440d001d01181c410008031447c050029180c10155910300c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 308874199 1250 308872949 308873011
    0x120d200a090501180e041103120705070501082d0718030f120915021b1c020907021c050d0b04110304031101060e010608090c04060506340c0f0e 63
    0x1c02c1c4044c1c1c10300d012446600e503901c40345c0103c7c0120603c0f103a078070205040605212207080107100c51401007040800045003c1031210450300242000c1c00141c0c0c454200c2e80c02e65119010404a51203140100c01ca500c8200602c540500c42c1c543d19180217100c200f403000d40f0cc05440c00007803c08852101000c0018481c03802c07a10703804d0250f14140c1941341d5a6103044a0034000006404056040000985c3c4040724504008440c06000c5501c00d02090444060608a0f42c8010001c0d0003004403400050484d402004000c25403c1d5000d405001203041c14801440b41c4c002509043d5038508105100038186018029184034541a240051642d10355a9040d9110b014002110407113540314000080c0300c000ea01ca40c2c40c001c0c1100d84924510b450803a2103107041c604602c00d403e00c00c40c80d215050005480e0001500e003038081050f031050003c18984c00390b0380309010702941440c002180401c0c480401500e020804210707900801c2000040740c07946c1ca0155490310407500c501100080c11014040490103200311 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 308875449 1250 308874199 308874227
    0x714030c040801060b07110406050d0f02040b0a080a1a0c041806030515040b24040902040204051c020907212301170d0203070b0c0705120d200a090501 66
    0x3103480c06555055650964155a002c015119408036103a028001c500e100560191400c580400445041c800001c2000101e01c0000d00354080d00200a011901d45901c4501d4031140204003a00403607454407103994605000d0b01c00ca91b43c0c55500c2c06410190788001d4024000e0b045620034030b0515007011a22411101071a0060b4440340d00c83d84000f01040040c071801c000c820380d03505008207614280c207040c54140e0000c1d00000300d040ca0762659401f00030b07050314690580070341280c0200740500d5034000a800390085401580d44034011580c40128441c9030461005004d209843d20707406a070301e1010503034042044c0010700a0081c0720461880100702203070320147d6680b807008050b42401d4191312070203903281c070240c1145c5103003034401081c0340c07000d50b0400c8075a8010039039100461400c155a5950700070880c019140300311101e00400e0410030441c0c144003481004c08907001c819100e440201c100006000f120303504940080c10b071401c09076044402001c590701e92025440c1c2a0000d8689001107445900c15600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 308876699 1250 308875449 308875471
    0x8070e0307061d0d1202011d07150c1a01060e0f0906041a0301060801020301030b0c031b091201020a020d020709060302030c060706091406150d020319080c0a2006070b0a020c0c0d081908071403 84
    0x9492f00045031800d0185403c054071400b025590305089006d0a2074041520051180d111100b045000e903076000003450740107809072400302e0800c00b039940c1300c0480c040300b40746c2c1645542451404600d240056010758100c0e8000c4641009a031551112440188000e55400c0d140c84140303210301c0d000146190081c121001701801c015150b00107918039608a800c43d403807070401038100325440a0350550402c0444098003580e40100a92843e6a00080d582c0005911282c041d06010031580300303101203540101c00b4681c001c5001c01e42a00052402074490074100d41e61154513640c0300c000f070f00c5824a20110b40030254007800420f6010108527076243c1281e10400220741d00d88c0b080143c40d05e40c07103061054010492103914920400000e40c2c01074101d20043c1070003140103441c140070750740228001e00702050300106035440050b515071507140007030b081c5880082103e4202c2e01084040e020000c0c8180248540d51070400001c2003541440b2044a2018040c1c45c0c040c0042d411212489540301044000e517004415455 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 308877949 1250 308876699 308876717
    0xb060c06011a120403030e0c0909030406030914030f22120f42050709030f06112802120d0b01110a0c0608070e0307061d0d1202011d0715 60
    0x4014500702108540171000a500c0d0314904521590130000028140000c40c3c010105141001009680b4000c030700c200420561a864180103000c06402c029403a215400e05807a030303030720703002d030004010741e204240800a882240f5000c0002c040b8500002c42916041400c20241030165100d1220361000c254082c0d900304840101808540303844194121040c14071000041c02c041810141504000c00185c108a00d134200301c208107070a940300100328141ca40c448010b0340041d806040c03400042a00551541d40380800054807410f01610b2030524082000168105096031507100d0126214440200011020074050000540504541d00a0000910185000409840e0000ca01c40c5880030072380b810741e05d210001c0300c00c1c0016540044159403054072400d1500e0011080800700f0b544a50900c83c03d0200a07000121032030030b088204414640c0c1500501c01c04400c00c87e070821103002c03907070b044072540550710b019540000800014003030352410620202800d034007071030010008110711050b40c0031020402d03122 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 308879199 1250 308877949 308877967
    0x20105092209150b0f100c080705070b031503010b031b0409060f0f060f0602060a050c0906031005010905010c0c050906011b03270b0d0f1508100b060c06011a 69
    0x110480001602400f03207422210140489001261326a40c05507025020300900c0e410151164440c207480700b5154a054420801103080c62401c90240e804c1c0100300e405a450002483c1d01004099070180340a10001034400880c8401c16080b40e043c0750351950103811407204001d806001c604417426081010b0804141201290b5880f02211261a180c540b52640c0d00d04c40b8411a0b21031041001070646483c10207142400d000001c1e40d640802000798840d076455038000f41c14044803c06035a009030026003038a40340c0c10080c0148024401354050b507800a4510300b0001010344c0700c1c400300d02c0b0281d04a0074800d0194144401d00c0246032000b003405041c000300690031030310801c05001d1103e4183c0a56540b81c404006e054101c80e80e4000c82d082d0f0000c4460103501448144000012102c20a03000c007000159103202510300341c0501503500d02c10005080360540003882580114520780c1d150310729241000062040307001c200f41405030b43c3e00d20809a02041c014040303414800003059000d902e260f904c83c2425017070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 308880449 1250 308879199 308879201
    0x6070309020f0613030605221b0e0103030c031713151103040c0e2d0403031407020d03150f0e10030b0c1c05060105030a090c05090907150302070201050922 68
    0x464000300d000081e0309400c20920031648116a00100070100f0071380b429034180b11510088e0002200580340e040b207000c0f00d002d060030342c035100310003407041403034880440d81d40c1e0a0181111300928800d0b004188002e401d000010310640070301e40b04604100007204010101d841d184080c09611007d10300203036490b40181500d0402c00007561003140701c0c0050303820980c1400050061842d018100340014440440212408444814151111840c28071403180c075507218103080380038264503d003081d0181507690602901e5503012030804400c040a80f01031141002c81e8030003900c0602c40c1d105030a62080e002d2010300001d0a140c840e240c001d20000c40c4c0b04401516034607001d403c4030041c1c60782480c030400080c015209100c00245000d000f022103008002c54a04a00060b000c3d11008090300d101d40d03178a209060400022042c004007030b08025201d240c00d8540350029a0395003945000340902071500c04c480c40340d21440303030080b20046079040e0b5401c2e0501d04094144841010042c01c0c040240d2203180b0786414400b81 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 308881699 1250 308880449 308880457
    0x30c05060a06060f0203030705070b0402040f0903050306180907030311100c05040f05101205090109140708060f100b0a05090d0b1005042304081b2404030206070309020f06 75
    0x1105500099003468032502406013903111811205541040c0100400140c0240071380d0001b540041d0301689a0382c03140700140080030a450f00e91405490065030006059100c00910300c600c405a4059010020001089950710340c11540511154030141051000900c07944205442c29851001c03540001003050400c010f40d458040d0180000f000481c0420a51422240d0ba00080005032a40324006042d031200508041441001d803540580f1880410201c40c0c0c2540a03c0000d50000ca15107442e50000b095280c0302c40b424450682144903e40200c0c01510004200c64002c0c4110755030013045d6803a04603140c0060708403641250500c602448040e420741c640d608042c0d1028442c0550ba40030b40340000c00308403056059040180524501442c1c0481602c502100b00340da81d1040e14001103c1c1d880b4980540c2d28400c0b80e030720540c4c041200c04407000c480381c005101c5840080014081c0c03001c242c600f05004c00b01400320b90150040e80040081354216000364011135006001400d40d940c1d00e40b8410101c0d41e180c1c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 308882949 1250 308881699 308881711
    0xd0e0a03020610090e0606010c11060f09091b07060e0a08030c0a03060905090d1101021b03070507080d0c030f021e0c030c0d0503030610030b090103060606110606100507030c0506 78
    0x1000042107076243ea2680050050400c0c12410083e42c072001c3c510715a03c1600415883c10300002107181000d0080020040351440700c001c200355982c002c09091880a0341100b075401d409149810042401036034861400d000000f50400700764101000d0382c80e044040c04030702003e842e0700e014a0740c0d0328012403214001503100b0032200107c95a246012030703006040f10b86950008c004140ba22081c440f1009020a03510f28009061508540362807103403040c240284201700380c0910384680c1c0c104004e4004400701c041d0142a0190302994641aa0f40c0c41150303c46103c04103850014400800c40c1001a000c2c0710b0000d4a000d003441203134500151180031540c0c03002c450140222903405800140c200746020080d952401300191041440c5000c680c2e6059501d000103400684a010704070400081e051096200321000c0302d0040c4041c48650307680c00c09100410450180c01700042024940c0008081e0003c3c03c940103440250100050741481c100484041e00084412002c1102203e42d20300411000c110240c000c1d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 308884199 1250 308882949 308882953
    0x22030b041101022406060711060315030f070311060309012003090c0a0e0403080702190b0f01050402070c050609030a05100c0206090a0507060f0c0602030703090204050c0705070b0d0e0a0302 83
    0x1180c1030002914148420110102003110122010500748213146001e40120302619030645501941ca49042a201c500c84100e811882c0441049400110300c081c001e0350702000d900f6160004000c0c011940ca8107458080900a5401003000c00c52508000e0011944500c88800004074200c581801c500d0b000025440a04901d1012061100d9400309014141400d82c044481079229450045252120503005102030240032131040011007640c002d0150044060b041c140d1a5034401b5145801c04103240240c42901064085074000b0481e81000e00c201d424a375041900d020f02a807410f000c22085a010072b020b945c050140f4080000020404c000480207400d03095804240000e406d00024a8200000c3c01c1d164640c0c8005000303004141e0208107902642c009151004407584041c0095407c0c03c408440188078070310000820501030380c9640300740c1202c0c0c1308407010b0080d40c82e00320301d03001039000f9840050401d80010780c1c02c102c0c030000c5000400d1202252b40c0003160f002210091b19003410321800f030503009a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 308885449 1250 308884199 308884223
    0xf0c21010f0f0b0126060406030b010f030614060d020915060409051608060d03030e1c030507030507051e18100903030e060403200111100c02120a020322030b04 70
    0x8200c43c0c016202685028a460600310301d0302000d25a0049103001c4464031485214080b801984903a003140002c5c64203c0c0c8400f4107941c0d1040808041c140500c0150341d07541c90f100148101513400c0f2644d0740108001043c0429600c450380030460601000752190200e4800c80300070186a07228903011701b0062200c12000521440c2c0703003146000d00c034022000c000811041303200b00400d43c0d640c000114815074052900040e01500080c80314500320b040c840302c019880003500b20342d404075890740080f4400c55450b80c080c031954541c5001038074240920707000700451103510900c501c2d00d44244006007010760b101c10300f82c25110031040b000c81c00c1d0f19064201c6e41c000408684080c0141504400c1115155000340c1c0e40626051864a418194400b5a91825003d4002c0c0417171450f16881080ca00001d0703185201607074000741c001e000c210000e05d64503d142000d03005181010814840341002c1d566000215000341d03141c164a0184840070706498040c0081c0c000b500744000c40415885900c1d24441d07031041d40f2003140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 308886699 1250 308885449 308885471
    0x3060503100209040f061a03040f0204050406230c041505041703190903050a0201120f06081e03040b04140d121205150a03021905090405060610020f0c21010f 69
    0x2500c000c1c0140b1191541005401c005981f6900d801c50b0301112007100c219200d80700c0746440882240d030280084d52250070b000a100034400d03513911801110990070446459a1075900341140e14080407645001c030390505120070401000d60001c1070380c11845034034096207483c2d2201c20700d1130a205d81428801142c0e20110708131000214100701200d110700030f03050051009145643d81c5d0b42e1940702d214001e0402c208808820700d5090705400c0058480d000c110207202646d01c4503000c40c0e580303102c9056000f1540c0b500341c0492079220701200b01c03002d46800c6207c141c0307882d040100706080c94400e40016030700b2100c80700800005c6007060242070ac50040940c1c0d801000c104d445803d800f80c1d2000792070344041082502c1c1e001d80726512a401881200d50569030b81039101c4c400008100707128625881140c00403810400c00003041408103e403403242c042250301c03100d8221060f1040703a07102c0b0043ca030b901c0680c2c0000107440711440d2052101d40901740c8800840d14001008140a0a5a90042c41010600e0712000c00da16 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 308887949 1250 308886699 308886701
    0x9081911070b0d11040302040504050c090c07020604050409230303090d030b060a2307080408060702070609030f05100c030f0605010518060d020903030703021f15060f0306050310020904 81
    0x10140d019030041881c5810071403658120310440f07410200d0035664000040d5220004020740d001141c00502c00c000900e0241000d6444c1d015546829105400480c001180840d03081d00b65602c041e000742c10b8500701402d0400788002003a440c0400c0d5151000094840007600c002610440035000803c09181c072070624101007032406410406035000d040c104400039169456075010b9402e103144900e0191540c032580b000792884480c600c40340c404892000a554010300c440000104112a1031204540107981c0740c54040740c0311415402440000750b6020003c1000c40d140084072401e5030700850a0f1400c521915517000b08488980b444400429112041e20400414900c02c040080000b820300d0362904212410241c02403008000d061f20922020440c0424004a903040c3c420b1000090704496684002c0d040c06540c40001410424450078003e0760442c0d407481030f01a9603001d92015411190040c1014000d94604003840030390030405541e1080025103036010802c0110b41c038903c038401a550400c01c81400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 308889199 1250 308887949 308887967
    0x15020109051515120a0b16170408030408090a030206040801020a120b1c1703010e04030219170c12030424060605040306021b06070e15090d02011b1b0504060e16080604090819 76
    0x4401c0240800410000c1aa4ac1c2c0450703034081d50001c480350343c0d002e000e00001c8022240390000794001c00045000b18048070f05500805c0541c1c0c044d01e540d02c000700a11803403030544031303107441090700301200c0c6d001c84814414081110300710503c607281d4480900c0c2040300d0400644c1007607109039681140070060000b4540c05101c0210b032105101c0c05180b80700780e9900e0b100101c40c00c2e1120344401c0c040c000fa510300303813500510025002d16146001c2ea44d07203080c6401c0601c1900c01c1a0070f14030409241c0303483c1403040d60a80c8100c7c0f0840e000c84d190903042c586141c0301c40000f5081007040c0291020103c22501c1550414054184242915150240c403030b0303101c1040c01a0300c1c940e22450401c0450030802e511041d03036104107030030342140e0918012600400c010488003101000120082c5a909003041c01044e0408024480059800a841c100328140c0c0e21003080100b10401e0740c0c4a0320301c030b0000020700c80c81e034800d03d1482d83c17004002c1c1c000300b0074040c15514164258492450302200f900d40c9007182c030000e64020914 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 308890449 1250 308889199 308889227
    0x10801020a09031b080a050f0c01210b040e0604060c0e0d210c051501090b0901050d06050411060f0d14010b0a030e010615020109051515120a0b16 64
    0x840c20051181d802611008480c04040c2802d149080c03460b00d0048501c03060000340c40c900d000d031214401c2c40d00e0101e98400004004003558080c001071000d503135104226140d640da000d9001501c0460209009400400010304041d401c55101c7c807a201c004101000100c0c001c030b20a000c002110620b01500804100240d20b030640302d5070304000450007180c40500b503400300301c0c4003040c42170310f041c040c040c00c0c0c030500d040d82c50090060003421403071456000748640050407078003c543c0074080b0000c90407c000000303c1c240200781c0d00a011070041e0700800c1041e80441d82c80340c41842000c540b000c410300002d00c55000300c440c404224200040c0d4000c884011300480c003c0380200d0002c01810350403d04d4004203406040d1498040599170410215800304c2508080020814251100ca920810400080c00fa0003410b0058030184180c05644071217a003500d90381403048500041031454044e05070200100201d6201103a125407140c5021800410703416030302903005000700c0d4004039809011410140030b02c0010100c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 308891699 1250 308890449 308890451
    0x40203070b03011a0903010b030f16120b1f090e0a110409020d031202190c030f021209040c050c030a08100f03110607060e060907090b0906031005091212010e010801 72
    0x100704070300f5044400700741c005080e40100d44171010880400d00400e141e81d5166898820701c151446a51800b140420315070100340300030b5140c191100960203401380303140c600502c00744161002424501030344103500c0c0e000031a0105592007681d0b80d07030088103494448400803101e4004031207031030402914407203c01d0040c1040d90140100e00d00e503000a10750300315031100902070210a0440a05400c01c1d64111034400611002c3e460000c1951a00100103401011013200880c440b528a500b072680001851580d0a0005880910701700c0c891045c480900300c400b0b1101c0c28420244610841c0e85020300103003004a1407031381c2c5c422441c0380440400920802d15031181d12540765661040c404510640f0002d050000e055a40395680c03015850050018491045203101e035005050a106610401042d00c800300c3e81e25600502142660508110012a083e9441d42e45079010303055400aa90942d00450b0380704d00fa101c250b078a01307288448610100c1c0e00c0301c00c052149039001c1c4018032110408940e11405404c000d40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 308892949 1250 308891699 308891701
    0x3040906050d120f050c100614010507021e01120203190b060f0301060302070809030607020a0204060815010e150604060323070c061e0207080405040b01020a0b01060807030b0d0803040203070b03 85
    0x15007600f0000010b0051040140b41c42d00c4810103070042c021144485600703001c55581000e1070344001c00801d103e01640d0043c0b01103c075040d4003984102c1c281e1700c80d2078008041e02c01003080c0b1041f00d1030b24802c0030f84c000e041c09242d0301400880d1031980701562107903d42d10b440560309001c00201c001103c800c042d0b800c1c803c82c41840602951786581003948cbc15200c2c18100143c2c0d4642c5130400d402c2a01a000c09180d241c03051f00200101140c0c04260101c400707100740ea0034041c25031688041916191003c862038440072451004100b000b0110300c0b01504510722070480d41a00d000440442c1c407aa00c0303600440d002c20344a24806100701d1540101e46e1600304141070311240c506111074000e00e1456000d202a01007500c8014242d01c004080004640350307180004210750f40c8640e0715102940e50807503c60984500d1912981d841a5400414041c24107984420403100303681c00d0000c113030f90403800500184101551000c180c132103070b26140480320000b800b40710071a49901c1c7c28030400d0310b00324040d00452031090041c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 308894199 1250 308892949 308892953
    0x810050108101403010609050a0b130c050f0706270302060106080105010503010504020a1107121b0803030c1308030714190201020c0f012601030314030708060409080d0e03040906050d 80
    0x310b800c1910418209001240c29400c006405001d19800c1b8a4003c2e07c0d150a01920540e558810750308010181c44103c05014807800c0c200031a04200c4101020034070400c00d40384c01d514208000e160040c85442d000a05440f0405c001981e00c0310000302c0c0c7e801e1000d0307507540b8003416010086540102540c0c40d11150b15070514000070928001031041501698000c510007142500501902e002d0502c03801c00c98a0301c1ea6034000140072903905400684403c24954251102c01a90807c6007080d18141801035113035031202c179000c0380c06620440c0242c40758800c1e40c42c045032814051005202c5c8a0040b0526890000701d1801e003420110803c0f03001401c5910800c0c40d40060740c01082010280000300d82c240c00c907209120041e50400c0034100e004034558880860200241320303211005040e00c1c000da032405a001c1900d21415040c1c032041d030340440440e054070005003107450944c001e190814032840c1790904087d0700901c8001518140c1d092041d035a00040740910085a0301e1290784002c2030120f40f5004150785903 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 308895449 1250 308894199 308894221
    0xc1203040c060c05010906050702030a11010908091c06024b0310050a1211011b0206030c09040c08070315120602091507120e090c0315040b100810050108 67
    0x14498a4188002a0f40742d000b071200c01c2d0721600c101500034106016900c0c0042d402074982d8072526019021500b049210704c1240307414418a1200c2c2d510882080c80d002b0b40034200542c0701080c409240106e510710605e04c0c0058800d0026040f200d21204589800d1050120203585801c0c0890410700c105031001c0d000b26140715400741040600d11610783d5550ba0340ca41c4105100ca060f03803600800d402000401c000546e404030b455010074040c1c0a8034440202d0108040110340c4005148901108080d1040686016144c01c100441d00500d1060869240c82c100902240580d01c1c1c44403420013180c4070301c0401c8007060f058042d03d600080303910380348034a141c2000e011000000c400840a048254007040303984440d105c01034002500380c82e40f803e00d5210301c2d00e4a0840f81c070f48901c90407000018080800601181092880716010382c0e04070081c0340c00c640c0c6042c0028a00401840c0160340603485a294107803e0300c404109208201a50360350921078540607050300060381066020904004002003040003078248 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 308896699 1250 308895449 308895473
    0x9090b03030304030c0203030c010c092d140102011b2003090310050612061003050f0304060f0507051608100b030a1109041b09050a0b0103060302010e04021e030109020c120304 77
    0x225045c44559084240082891401807180d10303080da41c0b031700ea42d4050075078101c0ea4140885150034400c0c00012035402103550340c00e5144501c110f40b10f851603020b00c110b4070400428110600e0620000441400c41e814101c0100303901e003407a030007095100201f00c04102892040c4c00c0f049040308000d510b015240300211b0342d90420045013804203070303480c00442c1310380e520481110640c608507021509142844a1351400242e61840300b102c1900c5115502101d424000c403d13202142c040d0380f1503c059100e02c80003603486600c200c404440f1800391088080d981023030202020050690040200624540d0407101401c0700c6844211900c01d030300c01c8880da00040c0f0030a0201110140c2614419003d85441c84c11100c401c0602d100151984070381000800c41c5102e95000c180701e8644a81705026075844400190111103c0d400064006182039806640354206600108850300c02c0034440064842e06400d0201240c1007070704003080140c0c0005480802c00010400603543c580390114441c990f08041c1d07500c9005100c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 308897949 1250 308896699 308896703
    0x40201090b070503070213150e010501090b0f13092301050604170a060f0b1005090d08032214120c0606041119020607080703090b0a0513020d08070309090b03030304 72
    0xc00007602c03404004050054540a6a000d05107400d80c0130102c080d10041d01c0803000c884c2503041700d0f10300010030010540c10785040341d0381a141c7c0d0545a04010160395541e102528074418138a0420039205603e51b010f0002c00100611840050020400d0f80e02444d40407019481940e1094040d005000f2548c3c6c242c112800c503042c0440721400d242c40340d6011810f10300c1088011b01070f94580510401d00509603004008085012603102c01000c1c0321001c16110780c042c0d01c0c0e6154110070781c0508140003511880003541c0200210702e110001200220101c1805007000c0021286400300d42c24540119004016645003e914409000d003001c84182045036921001002030340304a41303c8190011081c00c030811a0071103a10550307001c155907514070020b541d8550903500a000140c014000030000c034440d110b01100640d01c408a825161109003051003d85070103000203407013a10601c3d080006980b41100000200d104145c0161034510354200681904e2043d80b20070341c440e0a00200142c255804821039174025 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 308899199 1250 308897949 308897969
    0x40506090f01021c05030a0506180f04141e0105130f0f031812020307060206090c0111030d05010e0702010507020a0b0403052d0c103c05070305070e030604020109 71
    0x401d07110041380303026551500461200c009080020360705501800840c030900c1d4002040c03146450308414081401a41d04c115110041184040b42111092000e11900140214004101c03c40c0c803040640c180f41d104018a4603103aa4a441c02400342c000f8002c0c59030041044010150458464a07030022190b45074800034a045000d0000404050242c030509100c40080030b50442c80355100c92800c104000303c0300041e8824411346500081c7e031480020110b204804032005807103000c1054005440c03074041e80000791058042800305262240103882007500030400744440d2606810301c1c1038080e00319580a4880d1046401c03a034a1103000c00d407100051a040fa5040c81d001c1d660f10702c0c5484100a542c00c250321030500800c1221007624903040440505030900201c030a46149070503511b17040c1c04690415804021040c600b40c9481d004030086c00c5c13548819904a0f0300a660302503151100d004845c0b040f100803001c2035a40d410300c8002d951041c41d454420748141c004103030303d040070340001c1d207050034070300c1611050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 308900449 1250 308899199 308899219
    0x180e0a021c032703031205061e0109090f0903090f030b0114060c0a060507090902040323031306021606020d090b090102010603141b030607090b03040c03051c03050c04050609 76
    0x62140b070351045800c903410f1004001d01c11182d0b1591440045100940001e101d40c0007425080341c151060b24041d0100030401d2003410920600c4007103042d02c1c0c4010605003e19000d0000e14200d0070700500410401d00d1200040d480c0403440d019189400d107802c01c4a9481d075030740c024000281003089035415a0b04005400400304843c20000e07016104860081d00c0d14065201c0c0002004001c0d08464010b80c0f403034882e211203c1d106d500c00c40481c0110b1001602c00b2541e000c1880030000d00e0340403003848240318400d41e45403661113900a16205481e91024006a12860004194212104140c40034241c18800b8040705074207000d000700820541d0084140000b40000d22600607070003507101e41300039680300000c070030000c20010302d094440700380190b4406030200c825200b40681c83c011801511039680c0d5110300400c0c0303090a004000e140c00060013101c3d46000340c200440071620030010b005d0300d06000051152464400e43d00141580c00103003090400d030a09010030306c9a5940c00003501c0b080481a0303406815 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 308901699 1250 308900449 308900453
    0x70203120a1515020601030c0501140f030a060302060313061b0507141908040812041208030415020403120e270c0706051311010203030105090703020c0a020a180e0a021c 74
    0x42446540400080e03403d4450b8684241e40101d074541c100d9019601d8190003a030380c0d07401514600310711605c01c00c8101c030421100710510181c002950300b0140d1000c00013207941d260350201e0515801998040419172180c01040c00300f000e2030003400c07603140354284803501c4491210300c0503105000303400d0001c00c0d5029007103510030b0303000e030410002000c1400d02201251184440c14034903a03503440382c0101c4031140505446a04421000d40481b0101c0f185002d500841c0955603d42900c9c503000a48100d40182d207801020740700040318009000914091621050000303106080500300b03009100d609800fa0207000c00c00000043e00d285840b9400007042d1503043c20b030f079440e41c0c950300a2080080052130350380703441c0500681a0b40c980708a083c961052030580ca2403524080107a07030300d000074869543c1c131040510002d51103511075009052101d100e2011950300f02015030009074032141a820124160301101c009050100c0e007405000e1032440c808002e0b00151110360013048208a00e4a02d5603666421005c00c402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 308902949 1250 308901699 308901731
    0x12050912120a090525050904081e09040f0606033603022d070801060f270c020102030613090507030602090d06060f06030c0e010c030315050a0914070203120a 69
    0x10391194420151604900c00c95007030820040354141641c107030400701c45e012405003411043c0d90b000d1500540c0140c200044034020600410f118410090450018092280a03448034080c200070180d03d0200850b049003040c80050031107000c0a0900c10074200c1d00c00e0660382061241d16400007250b801100d48038103c1320704040c1c0c81c10702c0e5440a07020100005007006203083d00f0302c0e8810546c2e0868800c5d2084241c0d6265000e00ba186103014034117515814820800608038000c54035000303440c10202a0340603803038002818040380c0d00303000d40c00e015035000420884c092400043c8004150603030542007181d2001600e4180e0b80d40114000103000d1540061071a2840d070718030652200721644800148031664942040341d046074440e119034404241440000f120090003103c040145041c107940d084020301150710101c0142c064049141d618464120021800c4e132154131200c800307410010f5021818200024404003142c4006003071a0441d003041c0030010035a150324013480d8210520f0200410f1604001c62444 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 308904199 1250 308902949 308902961
    0xa0b0307030b0a140315090309010c022e0306050303040602120711030601080a150b010e09070504183201030b0406020f07030215010911041206020f0a12050912120a 72
    0x1940b1a02000000030030000280407003960802c04d8083d06c004175034408900c5000e040c29207003601305800a0003048001c0d4414428a840b141c00100040b1001d040c0c00c0b000c01c100b42500c08600c4000500c41c120104080d0907005510007020b040d0000c500e0140b03071450007500c40500401d503031449640003410b982405514060680ea1200c01030076250b2559523070303c00a98444000c00104ea00403407100143c4030b13290340c51041040081c0e068489041d4003000100700711149100401010600c01c0911012440c0030755940c1400802081c0000006d04509561a09400842c0300c2d00e0440350012064011102242c6403400301c0c11264046d0300c0ca4155181c9107400b0000c0c3c000c3d80c18828050a01150502c107242d0300103001c6680705440b07040c425060740c17101400403e60741e2154605076202000c0104104a030305442d407105242d80504030060400224000310101503000c0300d4032400062605c00304504842c014031403142c105061a0003002100d0503003c040300d090151004040c10f4407252800200042d500d40c01003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 308905449 1250 308904199 308904221
    0x1c15110a050c0106060e102d020c03160b1603020a021009140d0b0610020102120705040510030509060c070f0f061d011107060902120a0308190b0a0b030703 68
    0x9180c5419804030010016000b50010100303641c200180040c54074044c0e4045408140040c000710034050750350702d040d036661031142d040350500403071003854446840f0440d001e00b01d4202c0c03e44c043d001d507138650001c2620700708009500c8107001c1000c60040255000e84811141c5400c1580b010324140c001a04003682071109020001c0c2d002003c41c03034500300032540648460180e410208201d4002c210040c2840400d4400c4a00182400b032002c001c00e07414a070000c00a103404540e8400949044040008412407110070b841c0302d00410404a010b00083c64031818560b0725044510301004280342c01c0c4061990b4440181100b400160000343c0d00040c0b20442e901141c50a41105119081c07405515055000304510b030030562803403c2445260516840600658010710b8070510800d0901059455801c028115100100c2c0c0c4607843c2100340505d21828440a4415406502d904200e458400d1b40e000d9804880c460603114a858044a404103270f03140b5440c1e1003618282e008481e240e90728141c05500403c070300151 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 308906699 1250 308905449 308905481
    0x6090f210b1f0611060f2d1015020d031104050604030602040602060c07050703030c141501170304030c1a1308010f05160c0b0a0e030d020d0c080408030c070201050d0e010207020f1c15 80
    0x21414150031f000c4100e01440002e0b014244107951074422441c0c140c01c400010380103820001d15842c000744203410081da001d05800c100c1e8545540c480001c3c2d210b5006d640f080302e40c643c001c1420000f5a40500000e41d114000a002500e800d0041d030350b15440c0c000f13501000b0305105000c52200c01340400d5031741c020b0382c0b03250030300c200c9004401000c0c072021112000d1150310f1400c1c3c4201480b0401c00e10100980f41203a6104460b101094102892401445d69071041d030b40542d01c007805090301d00880101e100008001d1a000010284401c106000070750708011f02c44006040d400c0b283c981484e5000c41c0300c0320296040079032000d01d91210107181000e00790384d1100c2e0340300e403002080410445c0d91590085c00e441d48600c02c10000c0c3c0d8100d11080d43c04610071280500101428800511b030541c115004255452052410510f0b1001c086402d00458103486e4074901c03aa0350104205046040000c40119010b0302243da0748000840c5980007410313181c1010004015000039001d0581b090f0254000c0f010781010018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 308907949 1250 308906699 308906761
    0x81902071e230102040b1c09170a03060504020405060306040203040c05090c0a08160509060f220e0708090627060c031006090f210b1f0611060f 63
    0x1880d001c1d900010302c00946000140099080c400014400c4034101c07008911814102204a41104112131020025100c1c1e9501c0f03000c90350000309034519103c408250000102d0302d0700307d0000f00404448058100c540550b00c100400e201c16a5440f05480d4032000440700580e0ba90381c0c0e031414403d203421561040703402c0300740c000900000ba48003201614104100d0f070b4600c6e0082e03462650326400144003a6409011600c200300102050800700010701102c0d80000c4614540b00d07411800701030559039010b04409004245a007401400c900718003480d00700300e0034074045036982001c0144c1d80d00d44502910361940c0d03500403007014000c0b40c1402031402840000740203694070b03031401d102000300c25441110b41042d0a4180c4901260041c0244002000c1c0e501d2011100581400c0c00451400754003482010039072001c45520b044001020301d4441d5100303000704d08004100c1c2555110307500302ca450a0b08550203104004204052500001581130350002d024420321420380c0b91792180400c85104d04401c1c841e0888189 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 308909199 1250 308907949 308907953
    0xc0d051215130629070c171c0305010f09090201090902090a03050102041202010206100e360c0405060406180c03110705010203070f0c0f1b0504020a120606081902071e 73
    0xf50f51318905202940040101c40e0f8650203c41030b511403c0300040c031540350b0010a016808100e034024469002200485030070759182204100c17416880c04005e000a03494a0061000319074502c40f48008090780c1006100d00b481343c1c2d002820400b2640030398a8116404503001000350750b049944002141c01400840d600d40e11084490959404004280d000d40319010204d2805a49410018101c03080005840701585400800300072194403814040044800d120707041e4584405120f0180d4030202d034000802000140e4004d02090742c0000741081e1117540f414030100702d02e0b03806400c0003003210101c490000f1000c1304140e0540061a6984203411800c001107881e0041200550007580560780c66240e0401c2c820020104884080407207a00801215504003094006000001110902c5000288084100b5121004039040f608040340f8180000d400004042c2190900c2c41200d02030030042c80c1c4042540b41920124544907800d0f0074074190143e00050074000c0c01164440c01e0045565a0391081c0815164 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 308910449 1250 308909199 308909219
    0x804090213051516150b09010e0906010b030603120906040305060726060d15060803030703060e180703021002010212010b0d0e1b011b02060f0c0d0512151306 69
    0x640075030b80c09140c1c058900008490b40e43c0c280c51000c214021a10403208140c0d4480c020420007031040540c4581350f0108001c90b07075130003040741e0180c07012500c06004c0703240142e030080c54200f06034000072140d20204140062a01c2c085120707922807034285202d9950b00d1040003c1005803003503910140c040e00840c8103101e0b10725840200608030050495181e441d060191102c6050400152000b0b81d01c40d4100452000042001c0369100b5200c10702000020300541c0da42d800c5e81190b0040340d80c6400680c4c1e07598144010541c00c98200c1d04010107442080340312900c0d0b00095030741c0506020103071203030003085283c03050709100b5012908100103074607242c0950b50b5a120300710b40c20f81114130104a480d0403c0714201040e078001480c0f500f140c410030210801c1002550041d5070004001c482d603026800c0c04451040541c464400800d80e1312042d050441c1d485156840c1541005144621034003001410080348000091038843d85800c4414100d9035a04a007505000400380c02d40c01d401c050b100d90901400050048035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 308911699 1250 308910449 308910487
    0xe03070f12050706050a0e0f0f030601060e010906021c11030c0304080703021c0b040605151509010f080106050f0a030902030f0d0e0a08030712030221090d03050405030a030908040902 80
    0x115204549086440d20002e17602e6000d03810b035400000d14242e1240009140200c00c0ca01c13030742000f910b08106a6103c4c0040317801c0150036000355011440c0c00d15450501e59000074244020305062001d0174004a08224003035000c4050315801c0108881540e0100c82c4030300601c00c80d1440d10407a404c07aa55641d40e442c03410348850741403005074454030103060740d40211b5440001c507055070b41e071000708210b582c0c3c4c4070380c0d40d0302c02802e000d82030429001c80e202c85040036445903000c0303806d404c99480216443c0c114040004244140401c03441341004010401001516003141c107541780300c28160801c03a141c1140400840c01405000e502a51520842510311f017900070200f041d610708000780c1d8960541384d11314001c0c0050341c20b10380308281d480c2d0b10400113100800d949281c1d00300c2c40c2c03c081c900540781540b150b05040800510306010740011181c074080c02012901009000151151824144014031f415140e0984034003410300076800b419140d119440c104070340ba00850b00500006e0b0000c54440410440c4040c0b210340c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 308912949 1250 308911699 308911703
    0x50d030f0201050106030515150904090305090310020a05030705070f0803010b180631090e0f190f11010c08180418050d14040807030b1f0e06010e03070f12 68
    0x101e800d00200e00940b00340980c0d4440c1e4801c0c0101c80300121640c0a0004a5a103007827205000d010070302441240c0e983d80c1c050f01e0382e030390f020b5942e46495518000415007404211403800e000c00c0d10400080e0741c07041d009070a076a8072469500309180c9030351303441c2020701e030b40d00301d4003401071450f5000030000c221010b0750b10103040a01d00401e0034030704c401900414400316100b40c03152120390f480c3c00d6040020491803191428241000450760b2030049640b4040c80094505000514030036820000c660b4240341e908200c40c205070f007072445018110003115143d0203111041000c01512104042c00504003e034022140408400d40c0038001c5c5594a81110700340c04411a9000100d10850801c1e0b441460140d180040b00481c41e00100070300048480014203940141800802021000f000d10000484000501c002d00044d030180404048510703100c2c40b03404e9030400c1c00074014034030300c4844e50501c001160035407004da00c904207091600503043c000000a107014480d41c030100240020700004a1000007419600300b0240c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 308914199 1250 308912949 308912951
    0xa230d050315040519020c0106180902090906130807020303091008070e0118060809210406030617070b1b01050a0605090f160f030e1b13021204060504020a050d030f0201 74
    0x1500d140d003004190341c0c0170f0300e080100b500410b44a04d820b041c60750082000041d814000038030159a1001c514103074070880b01081c50b0390390f600e1220301541004005140e1005491010385203610b010384500c05a0416800d010b04a1000440d128045440400c201c4100c00303401400400506152200101590811034a010006503050711b080199400340015101c0240407121a003440b40c00c0c281e0441d2a9503004203490210321884804100001c981c03a10b407030420000040c2c05541d00d05141c009802e0724207643c1b00c0e035040783c820345040030803507030100c4c81c14241c0d460462119034850051400d0f007400e00300d418881061f9460300c0c023441804940e03503101c141140c4007500c0d40383c1c1c1ea41c0c9101c0440c0042c00121040c040f045120b61108807601d04c10301c0c06884489460500052700c0440d4104d540c40d001c1c00c203517402960301d000c2e2900c04540c5008104040501c000d14025840d00492901010f1003290190000300703c191150041400c55035148284406040301505000c0c41c120b807800c1c01030000d14401e60030030244d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 308915449 1250 308914199 308914231
    0x12070c06022a28080c0a08040303050c01050c07050c040903030b180a060503010203040209180a0b0c0a0201111c020304020d0524150f010e0301090606080d12060303020a230d0503 78
    0x14201501031440600f43da07080301038150701130310344181035400914101160b010381c011802c0000c003080060005540070380c0c1c2d140d0301c4030005500070f8219800a0400020320000b031040c200090b5001520350b5071480203a45c041802e400d00d150941c050860344003965030100d000072102c040d264005401500c5165000300602441e0760b42e00a1500701d05c41514041e40240c007010000c0c4004135041c080300c1120909804640c0d4040c0d1540b510240e6610640c2c4040c21004c002500301c038801e509002301585140c2981626151490055070412514500d100300741c0c049402000003815541c903400040d410070f80040031b0343c150010041d01c0c09011404603503085003185145012512802885016200c1e02c03201400204540080c00f00544040c1c0340340700040d41c903640b1b0700000000191a0700442c0f000380b850308014100e0300000754026040003501c41c030b075204140c43d280b4200086540000c68200003070f00194141c04100a41e441d11140c40705400c41000769220304104151f005510100940c801c0e81040c03510780c95 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 308916699 1250 308915449 308915473
    0x904050c070308010b0a0507080d02030105040b09090d0e01050c010906020306010f030b060a0309020d060f0510060512180f070e01170a02090606160c030f0c0b12070c06022a 76
    0x266008903080940003c10040040c030100744070340020428809142070080c00c044060b40c8501c047c2d4040583c40344640d8003c401040b05042c1801807000400c3e0403500d815961612484099076521103e22090400081c0c0003c00f599034040d50490300c4a4203034a0091107103a50a04140003c1c1d8016500e060004445c102904441072091044465500000b03000a142c007000c810120003600c0c0b100c10681e030000203821480000384452084035112090510003140c2032401e1a84220510115070101c024032800f0002c0700802040101031540c03140d811083c4c1030300c007103480b15084e28043c911900003c00384a0984042000740c40c07540700790b04942843c24421021085c1450560b01e80c080e8a600942040c1d0b160702081d028038002000d018400c0110305104500e6025448101d00424180d006940d0b94080c9040c600600c940341200b04040c1c8603190103149021400408102c00d40d01c003c046404204e00c0ca8004010440325030112004d15610003c01890004c0204000c0d502105580541c0c91a11031111030040f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 308917949 1250 308916699 308916721
    0x141b2b0804050a030f0306090e061b0c06130c030206030103030504050a0f0e0f070e10030905010f050403021e01110a05180102010605060d020702120304080f010606080103020a0b1815090405 83
    0xc41268030001030212032980e95411744400400c08000010f1507110b01012880f04554440c500c0d44101d000003c1941d410880248006030314419050040c0450030407603010006400140e0300c1c0c001c10000c108150102ca54100040740000d1608003e6001000000001c00e165001001e001920002c40e80c84050b21380d83c1001001c1c5141c3d612482181c0d580c4480000c800183d42c84019503c1245400c1c82010780c0c0c4503c0015035120444501c0308017281d9035841000c10700000b403080040207c060b0301d0410290401c4e840195680181c00c3e180b01c0745081c01c5020f4600410290010f03d0755030709982000d520350700e54804c00342994100e4450001d040521a0f42903a05602c140504411250060000d80c0760901050310345002c0c1d1300045099811003031861a008030441c0400c001d100401e8210b024000e0300c0d850350310050030b64205070300510400017064011320250b580e8440840482d4070b682c800c0d41e600c4203100c0302c01d00240c03120541d1a61002c5840840700c1c2251a0100901059200712000c1080303645072a42c0b01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 308919199 1250 308917949 308917951
    0x4050325050a120618140106091a0d29010321022e0e0f0127080909150a17071a03061203040b031905010e0403141b2b08 53
    0x181004241520500400d80380da0141400d130101c0d44181d445552640ca4111103086256102e10741d50723540341000c03c9440d02e24801c40d4880308208441e4003a5800820000314030740b84a00c0d0160030050403c6080e64600101c800380281c1084621040310690383d2400e10205c03c00c0074101012003105c1d40b0001c0010355201140b185043c000c80113015031715030301d4002010600301640f42c5001042da034840d818550030710108641e040101039107002185030a001c1600d406c0300d98540c00c4078810002e0b510701c081d001503c03070740540c1c82c482c50545a2a03070551301d17003510070516202c1d001c0b000d4110f5240300300894080103401c4141c00080c201c03011254010740c0c075050744015200400c01da4141c0801400403e1551800021130040039401808880c109a11421248150b5101b40c50021a04041c403090b000d1100e964029180127280c1001038402c00e1400c0d071000b030012484540303000407d06000072030a0501003411320a1040c40d001070201ca88010840b003060841d002c940013101c00e08200710f11a044c245100d04441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 308920449 1250 308919199 308919209
    0x18021c06030614060d050a030e0321040825030f03032403061b0e120304081605030d030905030a0e040f0e06060a0503010c050406030e0102040909030507020907260a0204050325050a 79
    0xd10705c807c0315031800c41341c0b0143c080005030716000f034101c0c00c98800280c0300d00310420340106034443e54881c508000e4a26101c030b40c011f500194880380b18a01381c0c0008030301c61001180c1d080140240b40301568a0210010041052000d03503540e0300c0d081780403007040824889002d50748604000c100742c824516820580813282c40407a0f00003441e5002c0c85410742011202e80001e07590282c00c480c20076894140603410300b00c10029103410b45c0c0000d4410001407070200078180898605080c00c001707821142d119242c6134800c140704070041c055402c0d0b441c01c075501d8540c011128891034510800a1380c2c05070511076255081601c010780f050100c000c000c145454103100b040312a541544400d403405252290070303400390242d43ca160b07441c0c0d542400009210304503800703441c16440c41ba544041e0760306982d00c100700d03045e01c000d00801d00704042d210398140d81400081040049421094854240f0744e1280340c180080d21658200c240c050054446034420f00c01080c440000aa008010b50030303050f0307203620a1041c00c640c20301c64 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 308921699 1250 308920449 308920453
    0x201905040b070f0501090b130302070501170f2a090109050a0b0304030f12051608090d12110c0a0605010f0806040213020309012a0207050a18021c06030614060d05 71
    0x1140041c1d1414020200c1c60302c40c030004a206c90341034950000e003440894203404400d0500c4604020035a041c041c0c103015200900304030302a14251f01b040000e111005080b01044c40700613010030040c4000c0c14a4074040c0b48003650042042c0c00c2c0c4911401d95400224240380855040440411146401001d500c1a60380410045056039120b490484022100740c00400901c584030140000c1c90f1980d0061611072080901c24600080b28603500620140e00100040c2903508580014412141e12103094140102003804c0807840301580d5005030041d00c6584400c4110384203030403802003041000d41043d8122401101c0400c0300d55a10000720b82c0f101030845000b580011841c1d20400c141510f0f038007568000320544000660301c08000d11441d0100a584030010030008203c4400c00391950420407200502002d4481e08042c61901c0c0801202c0000700f01956003083c1c0110350401e801d6440c410840c803c00040da401c4c0100c986d00d05140000304900f51600c6070800000d00000c401d0304200c20207021103984000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 308922949 1250 308921699 308921707
    0x2010e0d08040f050607030501050f01031a010806181005030114091527100b0103060305070308030a1808130e0415050901020c1e060f0717060301201905040b 69
    0x4801c035000400207104076292652150b420b03001c90f00801046201d03440e61f0b28002103d5040404000e00b0b81c0030001050704140c00d1050071042604108090007078000c0038203180609485500000e2490030580110001c4a01000100000485550030b030100301c0340264000c0010400034940680c001c102298190f625030701c0407500c5640d100c00110441da0004c00001c0c4c1035046d00350750640340d4543c03421048402440d0300010000440484520804405040c01d0808110b640e1956540a803261883d01c40075080b0100840000d8091410f504122a09040c1a001c5200b0302c445181034001d03504020000003a900521601041c0c8980841c3e800d401540c001d038000151080b8500408040e2000600d07a0b09155001c0c803030354040c44020805100c031585500c00515a07020050083c40ca0140d000305038000d103004a0741400000e030340110164120384224002080d165407482c021902410a0803e03003c0c0c8560415002400a1006c0002e0700c40b4041c42d0240c450000803407a421079090199005071108880108 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 308924199 1250 308922949 308922973
    0x14090127020a0906060309061103070e060c0c03071509080714120f0106120605090a0305090d030207030f0305210c0f13030c0b0a02120f0403120c0f03020c010f02010e 73
    0xc0040c5042910060241c0340035034981040c00d090f503040c2d030702c5000425200e0001d031082210380c4c011000002d4482508500750300d0007002c000c01461035401ca245c00380d040081d4007110150140b00c844030503c000350499110390b035542c02c507441c403c07070b0140c0c40c0001074031000000c40d0007000412107008844489010058241d180340410141c2d0480b44d01c40e003114824818121007006c0280551001800d8415035203840880c281044819100004d1000182d50000c0c444a0b0020790400300f510004d45041e20048020711180c0b070305900d41301c035540029003102c4810f5002d008141c0d12200a080e040428a80d011800d002428420f2203608140c403141f280e18000c0c4034580f240c1c4c00801c0070384122400704000b4130b0303100c0e0350303454a51148845810100074940c1c00120200010f03010058945c181c076a100040c0d150100c0740c40c01c0c00c90303409140001031180300c680d01c0603022a8411911040d00790b4000000600241161074060354468191039400d0104541c0d01415039064010320400510089010140940c80810 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 308925449 1250 308924199 308924261
    0x21002150c0904091b051813060b060705070e041103010902010836070e060a21020a180b01020601051005070b07050705070f050306130809040b01050d0f140901 70
    0x3502d03542d800941c1c4840003404122020f500c0000401d240b8101c80d00700307050034140070b10040100108050304034440c0c20310000e615403030401c40d02c4940011002545001a80c0000d08030b12070448058101c0c41488404a0301501402e0b226001d030f441080c02c06004000402894265848a60040d002c00c0c041d130005400803090130741c0c10042d0710301410304000da090f003a03001001c60b8800514141181d8440c0d9001c0c08040040344140707030050012210b010000341741010042000708400c0c6902c2481013183c002c1c1c002c648840312400d010301210198031403071030040d0101400806604600500600c6040000513036424200141401d2071031707070f540340c80c0303040a036032115200d5a8001d80110200b00e010003405012031000d202e4a070141c0405c10071510624585001c0519000001d00203c0022802e0703800e089c0000d500d601107400031074041c0c038081048071115005807410301070150080300729820481c007609092419400041000c1007000e104001b900c44109480c22180e00c402c1151038450700403503118806541c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 308926699 1250 308925449 308925457
    0x50310320301150b1215031002090f280e090d051b0a0b010f150e0906030a020a120314121b0715060801180213090f020901080a021002150c 61
    0x4007500104202000c42e9203043c4005942d8886080501c020030610410010b02c40303220f80111080d90659150f10750400040d80701d14488078059101c5900143c1003a003921404031424080310300404440e0441d5285d29205d86580c40074002e200d52590b80c81000c00c41408080c0c5d0036000c3d000d204020290b0102d030802c2942d040c0d10003e0288e00031100d604c40405811070401030006c0c0913100f40034091695151801d003072904441a0050200139034107400c0c51040c1d540c030a0304000048000c0f80c00040c1a25050701190070040d8400002e5000a142d01000c9900c46c08142488a90303486580c031340c05d00e4031440042240d24001c55030510012121000407804092259440404c0082032444003440c0020b80da03100741c140300d004180d80c041d40b42c036100c0c00c1228110078410b0115010150b4050450016140c1c00030b5a004020112034542d1070380d6842071001d0000c3c005a1a443c2039000d4201411541c442030419a10111800100d00ca40218081c1241c01840850a4090058061076803001511200c805c0111508 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 308927949 1250 308926699 308926799
    0x3050a050d091e0c0f03110105031509040602090f032a030312130311150c030a060503010609090525030f1a040321060b1b0319050310 59
    0x2841d807466401080f0000e040c050041442070043c107070380001d40b50401c20882242c1c006255000c11040070000305402000078403400c9001d2800035a6690b03011401d0300e0340062043e0540c1c00c1208541084108200e41e401411a80822158503c42e070f41d460003013542d00c60700250101050703042200c42c1d56500e038540d2562031aa10004007034900f4400d0712450310782118400c5500c3c0d4051a40906807009250300162001d15010305c4c480904802540d5044080840b54041e0004c0d40a031000000952018034a0b4803032409400010000d12409980d1044e01001d031010309410b0720b00740505d40c5400c120f500f05201c181f5500b1112100c4c0d9500c245103840300007480c0301d0402c080d640e4207800c0302d08219809603001e4807442136109441c0d00e4450020b540d40011416200c0c81e00c525150b11b05502800740304003120a40e8124440340e204000f030007150000d450b0450144250190f14108846a1115540e410402440c482c103108500e044185503295011480c081c001e103086001e0341e0b0340c540208050001d0380001d400c001d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 308929199 1250 308927949 308927951
    0x60c1c1e0e21210c120415030204140d1e0501050f07090f03060908090a120b0108030f12041e03050a020f0703081c110d1a0303250f0c0e04120c03050a050d 68
    0x100c0d8101d0542c00d1021781c84107a088980000340900281d049910444640f6940c1c0c80c0450070036081c43d504048500744145c1c01e6100e003521001c204c0c104024104000401142c00080303040741a406e1a125010381415140e199a100685000a42541c42035041c601103907070024400780018595250500140b0840409841c0c0c000100074803c0d2584590242c0b1000f44801c1c100c821402c007050520050084043e0030124060700100281d1054011950aa5250610001e41188561510320b007030100c01c1d9902000320180329003100c0101c2415003020150001d42481d07001d681944224800c441e0f118044c1d400000c2c10303503034240001d12109403100d66401107420705000015241005200c82d072166004500b11611454030780b0159181d0450b00620061100d030240c0055040007800f50035608100c1e42c0780080e1000007000e82c180c0007882035059000c0942034002c0d4138a80f94030340b280390907030000d60201d40035210103000c0c80c044bc04c03145c807501032031007166095924582801008682190254040700003a43d40c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 308930449 1250 308929199 308929207
    0x2010c1401060b070f1b0b030613200702031e0a0b1503010609060503010c0809030304030503040f0b09010c140c07060e04060812090f060c1c1e0e2121 66
    0x201c0d40100040010303038000c0141e01c07046000b42c0380c840c440701e51900501600c0400300d4402c21010842d47d0036a500450110750a51070700b42c940e820b50000302503180d01024901e5420481d52044c04030a0010010203009030195280d86c00c80c12180030040c0f00702184e540c8107500145241c00884c40000310140c005541d456103000360010301d40041e007035031006c2e045001d92998548080056240912542042d02014201384c0b0480c600102216181d000c0100701505200700040050104a4a1840c001d04154001010b042c41c0c14644401c80c000d112061055020902c001c008540e5020000199801e12161400410241c0e061290071105a907030118190b40040e01c50b1400705004030107114a843c40c20b040002c01c2d85500e002070800050300c40454040340284020420640100703004690301030f034003640c01c03c3d80d504500c03601d1040f2074002c4a4000340c01d08060100c94500c03c2a4401c6400d80c24901c01c0780c1c2641c980800300304000521080407441421a80f050380840d14107403144000ba4542c48081c5206424 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 308931699 1250 308930449 308930459
    0xa0507020a080d02060f2809030309020d0b01030b01321302221410080c0702090a1a092707030503191106010b040e100306060b07021c02010c140106 65
    0x243c4145040710314003603040342040044280c07003030311580c0c1c2c0070302c01c0382851403251100d0b1040c012030084210740755441038885800c0d1060500030340141e0510760703000d46095403d01a80c00c02c8242a803082c001282d044070084000580b4156141c420580021642c000785000c555454001d4681480c400e400e94010b6105404046400160720190800915000300c107107010707103c00380c000c1122240c0d400188081e4170011080840b51a803807580e0605020a003408801900d0740b840f40c1e0190302620718000d40c0008135400308103500c040c0340c101440010018034a0f203180f40c1c05100300304001104135400d0342550840c8020310b0000c400900355800e001011403d0326542a280e845081c10759110840403854003031480348426545911210320030310000303404060070455042004904d03152245103e29030030640b2a0001c610301f1180c00c14508015a0300c80e01c10040300340d5901440f2869080721a0036032051000581809000088074429a00541e0503552001240c0b00750f56481c3c8601007c460400b003a41d0b0315800410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 308932949 1250 308931699 308931703
    0x40b011e08030c010e0c0303040e010e180a080d0b090108030a0e06090301020313020a0e1005060703030e0d02100f0e03070f0f0f030c02041a100f030902030115140111030a0507020a08 80
    0x19080c52030000403070341e010881c20f1703680b0b00408054940d00a078410401080520202c118a50644409807080070707040e00c42890241c1e000c040c000c1580d030203000d41450030301001140002800740025042c0240300d028142005c000d01e4110910480c0745940040104030306580c4900c00031072900c0e00090245007002034900200742240c000300ca40842418110720b40c40154030300b48000c2030041190b078868445900d08807081d088420940d02c10781d406400c000c1030480406000f40c210b080703080010402c5900560722036900a6499200d44d6903034207954a04000711000381e40305d004018a0511400c025403031300242e40d8601713082c02e100090503141c000d1016083c500041082a80c00e851034000d55483e006001d031401003008540c151503085180c00c2441c1180d000f9a201c40c0e2000e40c28114908000c18002101c0c00250090140101c00079419480c0c520300c94004003a044140003550000041e2030a8107421200550300f1010380151840d8642c02800f00d92501841500100405407001e040c07040e07416a10ba070b000c0c2c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 308934199 1250 308932949 308932957
    0x71701080601080f060705070314070204020c010b01120605090619030f0b0702060f010e0402012007171b0a170a021201020a120c091e0b1c060602010203040b011e0803 73
    0x100d5008840100b01c1d40100b0041c070030805000002500302030601240181081c07050341002401d10284005040d5a9001305058805494019006566902c0c001200740c0c001c003242c0c64840d0201d00f01e058003250261142c45400c00b604c03170141002c0c01d08d031a06010440302c60304484c0b1480004200401c00f000003108500072104a5215a811900901340044080e0600744001c0c40782e10b0840c445401002102c49407209203800540a08201c40306803124070001d0b6140300e142c090b009551049000c001040c0e800c10f12040d5000c4400009d840d5104a032007242c020420820b4900c540c00100700b031007804100d120301112800e569440c82280e0260f0181d5010032841810f80a070408680d40c080740f001c0d42d00e900908004800c41042400300030031200c00d03102030143c0b0000d0081c10300000409a02070f2030714450325480400f41940400d056103403d17030580f2181001c81141c0c00308070002c0c14088000303500c0c0c0c014001d81e4044d0381e11112001040c6c0c03c20b003420619900c071002c0340d0440544642d0000300000309000070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 308935449 1250 308934199 308934209
    0x30f0102041e0e0f0c09030114100302010e1009171f0204030b0603010b030d181716080715030e0a06060b0d0b0904080f0304051f0c030e190b071701 65
    0x44070444100715210340d140b480340c0c46010810244010002c128001c00c1e5071590211070002a5500c5107113100100c0d0042101c8075146c094010014148104172084501d502c088074402d903650050300c54034000388054100c1441c01c68010805800d400d00a251000070b001c856111101c0c12285c210300c3e6104020b0741c5c0c4000007a081c120950018003841400742005200c1c0c0e000c14141e00a00200f01c3e0301011955605d5010000010003a01d010280329400101e0702c070000400441a401a040c00e042074010303100c5030541c0000c1a00d1004010001e010540130034080c040365203420016602e43e48401098001c0c06144203c10301c103000c1c0d03902480001c0c80702d200d450042e088504025813204c80701807000703045030702650304144100c42d070b0810840047c00b000100c3e0656490840750544030340321032405515000c0f240600e1410520b00c2184540035456550244a03c0d00c210f40d01806040c901091550300e4000c444000c415002c4d007681c0c0f45010030400c5084540000651901c8241c00b492188000d81e000000e80003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 308936699 1250 308935449 308935469
    0xf05011419180602030c0708040803030105180108070b0703030e030c060703111204082d120703092310290a0501080a090203030403060905010b03060108070b18030f010204 75
    0x902648503000c03451a00d0410800c4000c01010b03040d503102c8500c1c40c6034200010100744d000000600b03240380c02000d881c040359009000360303200ca86170000c1640700e401c24000c00c0d000e1420550110303401c0c018070b205141203848200103401080d0405d840c80f425940224026024152200500303004410200001e10150742044041c1c070382800c0c1000c0c02010384000001c4000d080106001f00c9804075001c042e869005540b1002040c2d41d180115820104150081548004980c200107030001c1e00311201c0007815040e03030030448901103a82c0c5d1102601144d8070a50041e01d00075070811101c03e1003c05c079a030f00c50001c0521003140d031071442c01d452000a0b60030500a6813003210040d03541d081c43c00038100d544032071880c0455001c52901e044c000000d0480d04014903507020503440759203a00030341d00c0a1003210062760b0040403d2100e00824140781d4043c09207041407174007920926000060b41c0760041200d2082d82c80e8071001e0303031030907410302010800e01d039101005607031602920311111a0b8420900c0100b000700303c0c80030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 308937949 1250 308936699 308936701
    0x30c07020a081509030a1b15180611160605150907020c0102102a091503051905070203090f04061d01030c090605060d02070305070614010911090a050d0f050114 70
    0xc540303c0b40600008040d50007444071752a4280c00c41c240c3c45c4c8075000140c158000390b0150400103c0c8030340250107c0f203a107103021090290119494051003403540120b1701445040840b03120003e1610403160f002500d05080c0e0411000160590000c035000311020301e21007102590000001d20321030703040e80c00d800580d200c50504030315542c06020751003501950500400800c0b0484094134206401c084030703030b13146100c0046110f20150180c038440018044c07050701ca00d010b8074400d02c090000c200503a10006004040c43c1c40c1103d800715070040a1040985601031800d150100051041e4400300e0885c02e98010340302d40d800304803107643d007002130201d0700280c100d28103d514505002000c0251904a881c519080210074042c64540a08a4124240480d4016074903541400c0899090082000c01080070b424162048403052032011018141c400b060802c0001d200d0110140350030780b166401e5550010050324081206103480f11092400c54014071f10740181c442590f4800782141c2d00c0552840c06001803078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 308939199 1250 308937949 308937973
    0x91e050c190503221401060807060e06090a0e0c040803070b04121e080717070906030c0224040201030b060a030212010506041d06040e120301080c0420030c07020a08 72
    0x6414a4900101070910529508000d02c0581000204105000340609001913420402c05510b03284c9008400900c0200b0a4a4940e403440d519100284280030008054013001e62003850210102c0d05055002040b9441e031900e02500300080d00c10051000381c0e4140c0602000401c1c3c1020700c001d11070035104180d083c80c6031406103010b80e03001c501480d002003080464102d400601c8600c041041503034410b410310004c25620100120703000002a00c2580c50350b00b00400707026899403c0000d010075980d49071400d202000504900302c0e654290724847c03140c1e4103140c070b010b410441508003400307030042d006141c00f10747c0e00c403c0380c0403441c1030f840035a000c00020342c00503000c0d00c1842c581200700c1c054882101e402c1d14007440e20b0a681d8100440070034441c00c400384480840c22a5aa03540001010b64285c0b06450180d140b900c146400d541013485105014010500401d615180c1031048000002d99208901e0500d140c03454a2461500001c220b440ca44800b0040c0c02c02580d140e03a0018028010f4100400724400e0341 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 308940449 1250 308939199 308939227
    0xc050405180108031c06211202010506060414180103080d060e0f16230c100c02150717151309020105221505220609091e050c 55
    0x8054100100e010003070060000340c401000300c2d951140c8200d0402e80d4100b07486030000080466a020b48042200300305440b02000c1807024000c0c68502660880304001e00c1010183d0903140308613a030943c01f410800080c0030300034200c01885e05c004005400038540c50900f4015881300c20003a04156405d1202261801d41c800450103010050100f54512110340e06007035620416005001d44181e4030116049100c184152280b00c00c101c2c6103821950f0350302154036140b54501194408400c0b40c1c100d0149030043c0320b0751121406100400c0c0800c4e402880a050240a03018000d54007030300346410482c00d041501681181122aa8040d0000d100040004140d090410000107800440556114105680f00000d40e803c0000d40e4041000c5501242e62400c400008102000f003542100801174070000d5007081c0c1c1540680074010340504403444000c080c80b401507621103c205407143c6000140b8440c1c040c0f1401c90640c1000c0901c50141504140c1e82e032a407001c25042d076000300c42c400940a408904200b0075000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 308941699 1250 308940449 308940469
    0x1020d051008070e06040902130606050c010c140a0c03110d0f0e0d0c0306051e16090518010b09040f0e01050603190b04060b0f060d0b0a050405090d0f11010c050405 72
    0x71940207080442c500010203c00ca000101414819547c481086040d0f4407028141e40d00150480c074104960303620340340003038002e801c0f00292441075840e01c1c41c2000700500640f50b00e0001c500046615040100000c4e0446400301440300407400c0242c5000e192041d500c0810515a918040751904800c0242c1080018500000d10041e01d1054040f0fa001d80f011540c2c114010055a030007807408915940e644100d0039401c0580100b9042d250801020019400380e04d40c1c0602101200d40d0742c0c401e41c40d0b650010082141215102010948024401040051070301c0005090300b135805440030442c00a40350641c0110398065180700d402e40d458008001252909111442c01046400c2d400d2105400075280d00d03c2100c0010300041a0a0b035074149510f044c2e5440d540d00c1050000100410303a1041e00d00050006403008042d003a00412910b01c0c081643c0c40c1c503000d101d201d0040903000f4118050b0b41d55088946122109614040c0a1300325003d0460003000c0c0114040311060742c172290741d90340c9448103200321010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 308942949 1250 308941699 308941709
    0x130902090f0115170711010e0a110306010602060c030c07032016090501060c060510050a030f1103010207080702090613020d021e091503070e090103030306060216050a170102070501020d0510 83
    0x1c0c100344c0000410358140c900d150404954589441d5110071a13036081d0060a508403001141e10400401c6000c10550366400186250240c003511072590341c0c2c100a036650a0107540c002180e41047c400076030007004038006000201d0181c074082d009031406807001d40301c00f00302c504040c800b0b07086030000407032688816106000900006504000e95072612400810101710340c80014002500d690210310300d80b80d03468403040074090061280782c1c010707076900d401d9084a0100404441074105031458110515061007170310042608501c000d45807404070f6003080f0141d60300400c5294001254501610040d40c54030181442001480d030040c3d0b038150b240410300840c0d1000003003540d890740801c504815503d60381e00c6c0120b404507400380161241c4582c08192860300e0080c003c1c81e04070301460000810325a150300840c084851359003d43d804c8030601340201d80f00031001c1c06015002807500000b0021340030294401c9000b605804001400c0883d075035151400d9034442c0c079480c141607441d0300c00d000b00e83c00c80ca441000180 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 308944199 1250 308942949 308942957
    0x103080d1812030911030609030c060702030f0318010f0e030901110703021806060720040c080402100f030e160608060a0806071206030609060606120b010c02130902090f0115 76
    0x941c03960388050880028035015020162034008a40c200406058031070704403070005054840034940005400c0daa50840e0071b1303ea00710b104020100c0d0049001100305c5451003142a03a030341c507590b05c0501560000081185a001d20740d81d030321801000b40c841e40b10301004182c01c1d0000c0c584c0d421614000519030344142051035102d0308800c20410047c3d8403002c0c43c5803a154205e255042d2540d507400001d5550051060181c403818858036459072800381c90300c440e00200c1044804010020240c8002ca0b030910080310000c2d0400403c1c3c140e690300074041c042c80700f1210303c01d142c089104500c94000a003000000c5203908050580d5120600c60703160040000c5a1142003a108124001d1a002c2200d560380c2d8050030103003e010040d0664031a45d06141c014801a40e000b4105005080391490880c00801d0700303100c1d1a00050320750045400c0c0c5040b600034000240d02c16560050013414503000c01028550580c282144030780d0740e1040314016180c030140603110f01082c1506105039850880060101554000980204 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 308945449 1250 308944199 308944241
    0xb100501050c0a0f031b0305040e010f030f0f0204020d0603051c050f0301140a0f14090601050c0a02012a0b0405010e0c101b0c0f03030e04060501050306120309090103080d 75
    0x2d040c001862510301134000c5000000e0000c982030135580040310140c2042081c001c02503400c2495080001082101c070b580801801d503a90300e81c10a2607503805804011300e80c1090801507808200705210140c44c240c0001c000600d80325003c01d500c0101c80c41c6c0c3e40111099000380b0f580c0500e075460f841e4500c01414040c10a5460041c24208080d40391005001e060703445400808100c0050f06d0344001e420280801982c0301b150a5101c4880101151541c0c0d081840f416581002500c2c40d4450020307a2a921031401c000e10107060180d00640b18981e0004074102007001402040c02a1200440c01d503101d18004d401800b00341c18103081c117900b5502600401d0000754031a813a1401e09880c0e06007006a80b10643c5000d00f00e0286141c2c0e0f240101c0e43e0494090301e41151103c0100e0700491740f003004000c4034070945506442242034020b10003598164855540800d500740006081414160b00f03007201c00e07000741d050342e241c045c04500244900c202a001035600c49408100391000380e83d00e1107000d85003034a100501a031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 308946699 1250 308945449 308945467
    0x1e0903030f0420061308190323070210090302090a060807050108090c040f0b0a080715180b0d1e0515060a230a140a0f03091106070b10050105 62
    0x81000140008102c40110b041d00b03c182c1c080d240e8010350310740f0010f003d1030759400d6001e40c00007002c0d45030050700c800f40154400d803d0002d052045142c5059855141c0320f16285a40c1011007542d008050300100d000c078104a8240103a50b18011101c119030343c0d455601c003c40c02d42c018000180802804202200e140c000705000c01c0300001840011102c003440c005e00c0e07582d01c0c40d00d460304204c441c03150035801c142802c00d280c5c03c071301c0740d83c10040c403c51003603980c20300c45551a0f200c0ca5480110744109000980e1180d0194409440358244c50100d05c10400400800c40c0d55403c010200ea0101081c0036500d5502c400d407031310341e1551040c081c00400090030b00748034a0034041907100e009002004d0300c1b441040009004080c850290203c021007001c11001c09814071079902e50b1003103550103184004002440468841e2884040c10107440d01d5143c9a55083c10301d810610301500140b404660982e00c81000601030603903961218020000180310300f00720039070340c20200040d400b0010f0359001141480014070151078 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 308947949 1250 308946699 308946721
    0x40c0812040306020706060506070506040b1f05040908070b0f0603100605090f06040f0c1106090a030c0807020d15020d0b090118090f0b0c180301090308071101141e090303 75
    0x10b5076004000180c1e98603c514007280280100e602ca9500000c02040300014040080703007061085000f0902542c1d1079032060181000108c01203c00c00c0e03800035180702880241029401110401d01c1221510325021341c50302d03206142e05c42215081164441d040401400342414040c1c030523080303500c10060200c1c5e418180024008070005080b042d440c401b61f00094295a07a54008600f40c04814034104541081c4c0d181c024661a41480398900c20301c1800701040341c24400281c0201541d40640e200d10580710150b03101c8000d903000d5441030f42d00280c5440c4400202d038001d00035642a020240d07006076181c6051181000b620034286030940300b1804c000c01000050310f441010040c0001c1d0780000107541c200351a203000f101442000160080030041d08112102400e50010300031120103900ca0700c907094540007050f0985884000080000740000c000c16200ea001e9508149034164000000c0385c4011200000c102e403030821100d8500c200b030030003000300803601c2c0320550701d0b00281c0d00000782d865490065001c0c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 308949199 1250 308947949 308947957
    0x2030f011d0105212104080105060a050a0e0a0902130606020f161502010f090605100803040b0d0509030903060f1f050d02150f040612060503030a0e040c110a0b040c0812 74
    0x203401d4103007998a2400b560a020b4196172500c18083c0303540303030218240040e010742c0041c007075401d5a6191001044161624540d075600716480181600d507071500b0151561098200940200f4050352140008030040c1c0d28600e8014001c40d60840c001003141c078020340240381c140304040341d0f8400c1e00b0408000c90222141c16821099520080b0150790924243c03404900410540902608082c9000140f1080000d00c0d00031901594060a90308007968403000c11030b459110358403552156150401c910070210300241c02c01580960b130101542e0400300200c000c00c0c10050102c4160105078540e00030044020300c4e11540d188060b02030300841001c1800d100128840c0c21024001901c6040b58451154809440300221001c0651074003031980c4499031603902802d8503103101030b03508485083c00008110740c200042035401e00011941c03544040d25012081c84001d0042c4610320040180603100181000d070100a01500b0702d225074200c4001385000c3c00d11120210090b046101d00f604444c038070390504904002a1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 308950449 1250 308949199 308949229
    0x1202010e0f0d02091902190f1103180111060a060927150603051920030d0e0a05030106060c05010b0f010207090e07120516050906010903061d0102030f011d0105 70
    0x2400e05840d011141821041010840381c143d0740005150466551f444069440307081c0a03446540b6102451744080c2e0381c1e00d501c83c600d00c950394070902c90b06034480d0039000795180c07400b01030505940b040702c3ca0340310314104503088808901e502e0f2a01010404011148a00003030f0300c1c00000001e19400c2031721141e811280c029403000e00522240041d95203824a5940300b003000355400341c22070b410120001a000b800310600e01044c2c070b20507800c1056200c0c51803e44a07211740c245008007e005c0c00702e0030400c1594a00301c0c0789a82900719510030404225030b1000d00c10703007004e404c95464021041d10103242c00c07802d40e0100150140120700c810582c0015036000202041a62000c1c100450380e411380e1141c2c0d910300f00c032a500c094440d0450065501c2840404521201c4044408291f1300e030094035581801741d2100c2c04d07070750b8500141c45410104089070300b0394015592141c007520320220102400303140500360b0b001a10301c1c0c1401c814040040200e1000c800b8080440d0003490150340c0907616080015411503680407030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 308951699 1250 308950449 308950459
    0x815070e180903131706070201050c03060402031f0f0302091302031e0f011104051314060f0111060c1b0105010810050406090b09060702100501140d030c08041202010e0f0d02 76
    0x320b11244014030030b032404001c0d0000c1000081d44c0ea407650800b8980c490b0f40c01165401001c002c00e0143c1e1060250b244508451105a4035544903442800002d500c01445030b0004010291100b80d421245141c5d40028110307103160f10380007400c1d80100014894050003810401607a040105d006071400b10b0144104d0040c042c41101c07038041191b15070f0a000c00f251025006528140407031203501c0c0b00c100071b44103503007080d0342e8207500c011840100c00440700d00c401022248a5a00d00040c0145440000d184884ac01031501e00c03d410b4042e01414600b5000b0b13650000400e40104410214003401030110140c020984000c5c00303035524103d0388944a600701c01d9841c8915803110000303410f00000d50098900d0592101c400301051034000401e035117a880030f41d0071100500410a04800303208003406010305990f8540c40744030081035500200840241602c0084050220722448a80030400a10242c030040201400219a1800620006000c041d100001e98490700b02d000d15101943c48041c1c0400109506841c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 308952949 1250 308951699 308951701
    0x6030e010e121c02040b030114030607020c091806151c0f03030917030403030b0a0504090b010506131a0918191505030a03030207051e0d0810030c0815070e18 69
    0x28021508090001800e03c81500002d0001440b16240d40110304958566000031305000c800030815480f540b05448000069010004862442c6040d0003616088100728a12038214498800a50300780541110f0342002400344072a403410f42c0c24605001ca000e034484424204481c0c0f900c0c2d462804903005004090300b090380e0f4941c941c0c00c01040c240c041414442044c0380d41d84a00c1e240c0303130050240560381045d40c005c1c00c0c013100c00604c608103401203402d0940d201c011158541e003000c0a1090075042031201001c003500c4407c00081720080c1c0490082c2d207030000754402c2d03560b6403c14240000840e0007800141000da070b10003001003454503401080982c1c40a18404600187c0180950035542d800e500040e0b450302814050104254044c3e0003001c003544200c00341d52400c600d140c1c8000c3c00600350741c406005900890807c0311001d1060381200d46c4848044400c0b2051a03ca4540740f40c6180503402070720581d84941c910303d6805915000c0b0b03c5d400030b40c5103409d18403401801c0c0440c0c9036a83c1c2407407030fa100d101420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 308954199 1250 308952949 308952967
    0x1323040506010e0a06270b030607020d0e030102071406010e0c03010e0123090c04030618030c0b07030e030d0c030e011b0c02040b042a030c020304150c0b0103050706030e010e12 77
    0x18101c14010200d001c19030301d40e403408100b040002c940c013944810181b0310b1f081c144022810007095061041e05107401411401410350829180083e5442103503a05550800c042e05c00140011668400a80404001c2c1034a604000c3c2030142100c010b090120050810b0004101181e6a804440c0c1550245559410750b003000350381820399540000e8078258401030190401c00300f001e03244040c0c42164003508092040d03003004c0f07100171490101031101500094800b51030b0710108058003d040d402100a250002e004c000e000f1089041d60002201611290b841c1d070070b15104d8540c54010740c0f00845403180200300c14440c0e102001007842e20900400c060050300d42d80c41056658640c860100c1680c040d0052010841200078000c2c0340100c08044201089244040c6100c0ba2080c86001c42c07070f0801c0d4001314030b06814800754014844030105510200200143c0e60300c00075070f40c1441c0d1802184540010301d2801d0401d00040c05880340201904296803401d485e034004460001580900c688540e51582d80d0341c1042 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 308955449 1250 308954199 308954201
    0x1401020706050106180501030b0f06090d15092102060601030c050c060a0603170f041a0405190e09030c061f050a060e0a09090503090f01030b1323040506010e0a 70
    0xe8001402080c5000000103515070005003c2e414802000c0c1c440e024581c80e10015000c4440e0070b403240303070011b400b0222403060303007450402070041c600000c1060451305601d1380c440c2c41144d4681205140140c41d03c00510400c0181e01800d24182c85010200c0da00300071011009640d880020074150405444203190360800c0d015004803200c3c14181c2007954001c1c40c2a41c0b0140c00741c1a50b1000700c4100b00380e031103105401c0c440c81094031350a6501f00c00e10343c541854003a003206908070041601d611820100000901943c4405021002107140e5009580851900046410b034034801404102c09030003c0003403056494010400f55845103240c0800c009103c201e072200005880f1941001d50800c0c000e1b078000c141e40c1d0300030320007600d1580102c0e500000191030303400d0002912812480240580c1c82840b44690b1450b1020310100620010700d000100901c084000a4116480c5204040342c00d0303a85102c00700510400c0c0410840c29072201403800307a0f0034107a40d020381c2c0701e40505c42d0304c08a0f0204000b2134405c0f191 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 308956699 1250 308955449 308955457
    0x50d0f0605131d160e090f03070303020f0409050f09011515030906060b04081005090d1d040b1f12090209040f031206031113090b0a18050f0a0506070e0d140102 70
    0x104400301c41004c1e02c51300074480c3d00443d50144c40949600b80000400030761000520003241000b01014508040fa265010342c003a4000038100306a0040034800428141d0140c454030344110041d640b40c005c0c1e4105580da00f82101c0450400240309000441e040c4266119a0620791004a06140c00a16041c41d800d115000f041c0540005651040002d00002c4c1101e000032081101c0d40003440070001c1c7e07105c2200641d6200014016040892504000c2003243c0300da07008592810705002c0c002154185640002504076911101031000003a000a50441c403e0f500090180400d008008200b10559564001809011000740000c1c80e48503294404030805110303008118810742140400d0100a07240d140c41e540d00103d242c1014003c807640c42400ac2d20510a005441c80c16811210001664079204100340c05000305002c8109079084d08e0760728800003241085070b1281c1ca00c00c1c6000c0e1540e0030981c41e08504002c00503105004200d4070032000381040d03031010441c01500d5884503400b07049004442c10170303002e405 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 308957949 1250 308956699 308956751
    0x20903010609052205060c0304030201140108070812030112080a120203100302010e0306101809050f031801110d0e1206040507030210140f0a0519050d0f060513 70
    0x420110700180c60106604100e00038940c08500c0164012aa403185030803409028000c1c0031903101034042203c00c2c103408000d54205000740b0022445407051441090009402e034094480c55100302010031401605100e842da42121701c41b4420300d103501d4076500c1e10104104020281c801701d0700190000b151070188880310302ca111258419901d0b40340080884500c0c0d003e42c8000e9004c074100d448141100e02e40030950911449203003142c062540d06084000207810711000404407050764460b4400040b850805c0540540001200210f954180c0b4222070401424440600343c14016922003c4224803000320701e0046032200c0c0c2c0340804103086c2e40c0300010b501615140b20381845010b80c00c140028071601040d034106482c000da4040c00c03180307000101100c0d089400e0301612800407041c00b124100501e142e000304900e0201d403410900f00b2805046071140440254074401c0400c00005141c0031660b0345000c0d8001c05c4000780d13070400080e8a880080303510800707080140c400035a0740b00e181104024121050b080c1c40a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 308959199 1250 308957949 308957951
    0x10140306040225201206040620070c090605040e12030c0f0c01020c0705191a041e0801060510050702010c0f060c030b01080f01031707030c050607050904140c1c02090301 74
    0x189480c146101e90803044c1380d00001c0302c003141485401e1410b00e940406220301c0080300a005a43d120703141c060040c41410706040400c0e541514021180510710050f100041c01844100300c4035182c645524105c91440d80310130b00a5003499591801404082803020061140f850034940d00c2c0c0d50241b04410354400c51844074000306002c114690464015030241c003c0070141d41c2240e14123a1104100039120b20151090b14064050403403d0040c0c1c40f50b00b040309a4000043c03c860f0809407914007074131503040c40d08a400d18840102400f0402e0300004d000f0741c001003e0588440300308540c0900010030a105048000c1c0c10f01c04a00294410008029154101c0b250826020440900d0f1480028040c00c86070640d140010140000700d405084c0100600781240c1d4060000701d24000c110813000b01507040f000084d001c0c0204001400040703981400118030070740003541c83d03941c0e490078401040111380503a08540d0300260107804210604900700c04a60741000c0c1c480035480c04030007002d80701002e4499a03d03001c0d019 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 308960449 1250 308959199 308959267
    0x304080d050a02060f060604090e1515090114010c080a260a1103130b040821010303090b120613090c26030307050a03090303020d0e060402101403060402 67
    0x580d4004098000042c0d0380d030039142d554403201102909a40203a440d1a4030010804c000c1081000c030394040680c080b4540d060f21000d50a400caa01c1170075004981c034403404282200c0c0e80d41d2030302d050405a130261150280300c415200b845d500017050a8a502401080128001156400c450203030032080300c0d0081781c0e24900007503070032694820214041a14000103aa0500b1014035030a05804103407881201c45d03000a080d00c0d0200e4803518803025002d0400d03158050f0030003030214150006401502004044603010607903500d03500d4010311480c050b03801030a1850301800080c0b2a0f042240003d80c0145d000c450481b0710100324215807000f0000b5210060599004c00d500141d11030780ad41140c8001c0d40388540c1180070b0140c811741e494a07480704585840000d20104a407140e4240260b200c08501c90203450014100403002d2090b104403a800c507032515060b40220204011494070b00b41d0103075030004d01e1801d2000e1101d40755815481e40406441184a16004900003c3c2c00c0c801e68410454004c00050300040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 308961699 1250 308960449 308960473
    0x25080d02100b030309031b01030b06030109021801030e030307110705210712052e29010216050d050313151b0f0b0405151501030b030105040206041502030408 69
    0x61851419800710300300342001a541102c2c41c001c0161a4440e001501903c410000490f0008a00c0406440c45042c03560b291244402600c1d40f60146010704640341d40141e442c2c4035049200003408030309400034101030a06801c0e0b02e90103008020750b40c0003031441c103000b0441007280c801107040501942000f41c004812420728011848115006449a0101e9058030081070b11486032510240401d43c010f810390b4024582d244022442e580c0803a91122003d81e40711042007444070030300c2a02c1d60b1004096003480368802c0d10320821444041e104800750240010451422141105000515144101c0e80328003643e5180318140503050040341c1d03122540055140d1180d072148401400900c407140b1610001d260865500c4d0011004040710108d1504052000340f4108255540d45e0040e200a0044902d809130100d45814202c0c04076406028010180000d40c058441c50001000c45182c184080d100b6814032052201580340c150032030b02a01e4070a00800117602e10142d05a00d584902e42c42001d161180c9102551 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 308962949 1250 308961699 308961703
    0x40e010e0a06060819030809071d04020103051f1a1207030e0d0201090b0f190f0204060e0312040311010507140a0b0c032401121409061825080d02 64
    0x75032030312a0b40100907060b00d0307029043d600c0b4150044200c607860103c00d240b000c80d0040022641c0900d2000c100c03895143c85005160b17442ca407107421003148041c44000d0000310368240c0a0586c0c48a01c668075045110000220500403000d28429100066981001d0841002100c0220380b401e01c0c82031440402420480c0c0024001d00d4070307080d40f64907409945c0080b0a514410b000b1590a00d03002100d416841d150a03000c4c40003114040c5c180e801d042107028419004c00002d000f240e20b0a503488400589452502001502c200c0110a40e503109400111114800700c154205403820782c3e030820840220419101c00507036a0b445150000340c603110304085006010b100000d104514680701d00380e01022611031403410b8903180020f80751890511060000740078011512080c1024144051620300541920010307031070126410783d91080300702c1c0850800c204800408003c2d41e50403103180309903281220450803d00e5262554542c56064414940550f403045401c0410701a010f1304641068411144103144080c1d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 308964199 1250 308962949 308962963
    0x6091c2705040c050c030304030806010e0306090f0105070201060609030f020f03060906070212071e151103160c03050403081e03010902130806070c08071b0807060e031f0b040e010e 79
    0x740c4520300384921280380c14071480076500c03010301d4900110f0554403180da09841c402d4008120320f04100080b099440665002c010b0580119041d101400145002768009402c1d50700081110381568145141080056480f0410b102101c0e089003004004c0030492002074080c06071189030300e03414800d030390610010b1403002c581107000303d1207502203d4039001e5a1018803003500600a002d0600c00010954000000a650b03161030101c4c8a10300386104034000126403800c80741484911141c82d04040104041c00e03910b0050210910f5460030440031090f410782c0c00400611444c080180301c140b0105900c14071040c0341c00b070b545034446050790441d01c035078503103a000000b0341203007014800004125400040200000c2141400380400e6552842e01c15040c1c3c55810940c1c3c17000204a49502115695001090041a446002e881d810000e00f90052a10500800e036460110040d0f10a070003002c0c0071200008805a02c03448041b1020011400c80044400140207040e0601701005550800b08050442c4901107004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 308965449 1250 308964199 308964209
    0x90302070f0e01050d0b04030e04050a090302060f0424110a050306041506140c031918090501060f030e0102070507090f060603050405030f090d0c0602010504030801050306091c27 78
    0x391400c01c1c2d8816003039124840030f11030680c00c00301a054400c007041a5640c4142d20031b0090804405a00400021404079141100c055011694030a0b2030002c040e0306019164200c18480e003584507509142c2c442c04c2a8004440c00c2c0d5009a101840c644882c0c50150840b502d0401d0103041c02e82c50340c17040c00c00904580d108071881c81c400e6140c841c00c1d0904c0351030701c1800025102c017541e1389031280c070320215045000e07484000841514401881140d4100340c40148950716802c0d16074a4224200d110101344852000c10b0f0448188213041c400103000055110440356600502c0385070128045c007100044030b00910a01501034070b64041c580010984d501143c000364102c00024804018041d07a6803011011101c003a03a00420307540042000140e1240100c014106501e0018203581804140b5900ca002030808d55100d000583d44880801061540004449004050a8010306003030f2030101452519003981070324906a90402000500d1500e1162140c4070494248414440061100e4140d103501280d40d4461 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 308966699 1250 308965449 308965469
    0x711100f0605031b0f010e15040501030b010c050d0509180a051b0c06060f061201030303090b100303022e02161b0b120402031c181a04090e030d09030207 67
    0x40c0d5803c2c00510300c4010003080c20500028194401000a040226000c3c94100511724849500796a14901922032006c425266150f585192000140507a916048501d0500070b04405120100d41c0104498a00e00701c0d40c5000341d61a4000c2001903403c82c0b1800418882c80b020104015041c10f00340d1105000b40310300302c90700020700034545000e02503108207244000e480d00b107000801e81c0c50500d040c80a0a1403001001c19040c20b030103840000003040240e1044d00041d440e5a0700b0028001e610802c19007050380c00d0a03480040d03056840c0039680b620f42e00f44107c0c040000d005400b0390410070443c1d00b002c078040e4100565480b0000242060007150040341900c080c20440e0458950901144908085031100110306081c00240c21a2980ca140005c2040c0e03054015400345100c1b040340354550903643d84803130300d5118012a031800341c14a1085690010b052401140b4984101c420301e440680f400c0b5401320700e010030740350f00d48440c20b030460086003656440175040c6640b810415401040b00020340d060004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 308967949 1250 308966699 308966711
    0x10c1a100b0f090d06020702190303140921100c05090109150c1202070f0e15030a0503090d0c08030d200a09030b040305160605071b0b0109050711100f 66
    0x1406410b1161140200700c285080000c0d11440c1044401c1a00181c0205001424a00990046900d464503030250328035080c0401d20a01c2015042803140058182d0304052900308030014010601641c00c02d123442c1400f0083d1540d40610120400c90a1031070010b01c2d20601c104a05481c01410b1504410126404188000380200d4042d0000030044070b21001c550340c0e0318003500f440d1a04c807883c40301da00c007400c114024050042601001442c480000b1320b03106c0c46107407840c5000c040d11908501010b0f05248650841003e510100d030000058924184046070654581050351511408004480e0710880e8035000c0482c0fa000244a15400403250644041080c469a43c4640d01c07040300740302c1c0b45c0c018004101844001e00c0803840d018400eaa215100e41415444e1409452003604400319a64003200c0395600c54003003082d11317540400c0144880e0400400310f22450304654071010a94814056004030960fa14006030b081c3c5e20601c030701c010a865410944120071180031b01e43d000f400d05081c4102004e81441 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 308969199 1250 308967949 308967959
    0x1503010911100507050c06031008010c02030301170a02030a02130b13020901090e070903170405061603020d050418050403022104061b080304120207050a14041a030d030b010c1a10 78
    0x4048440700c0d41c0c01400741c000440006d00b00640c0e900050841481810001070225110700c09224920001c075041d0000c54980d0300d400600242010a8164102660070040e541001600c0c0003810492881e4100c46014121002000490041150200e0b0580c4075900402ca0b013500340c019030007800e00d490300381c1c0c51012140d242c46038144c0210080d01c4400c0041c82d40007040002c907040e00100c0c3d565118004240d490716030340c5d03c0064041c0d00413a500f035a119100e11041410190100700f0200b1000c15410311030b0406140c90702080600b511200241c42c125141e17400601007620a00c003035048100200e901c090043d410350040750180d003060281038080b50700300a002c500d1188800001700000d6100c4c0d060b0b40b540e0399a958218503003c1040c07501c2d0944c800c030740000c00e4659a00741440c0140180200184410301d0752000c000507280ca0008100c0c41c0740c0c680701c0c0085113842c08660094108220305002c2901e101d030000481300d001a50704003814001c031500c0824005079000300401c0c0203014800c002d42c182a162 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 308970449 1250 308969199 308969207
    0x204050108070e07080705132601050c18040207020d0312060f1419030c181d03040302060c0307020a030b0a29120703050102070b06011d06070308150301091110 70
    0x3c1c091040d12410000c0001c038440d00c542007840e4051164078044d0b0034400c401c000e8005080550304004030a415841454803e80004d80c207050881721950000d12190130406214034840c4a0304100300540204142d00c140e0544031a01212203656001d003c0400102c454280140070b411a001040302d40390801c4000030308030050b04500d40a5071414007881074405004c10420502e900e051511442c600d880c158000089855404280002c0640d4401c4d074502e411a00740440c1200c0e00307940d03081203107a010041d6040e08007000017030350b096980c1680c0c0ca40c2d440348040305442c80c50044540081d0300954460020007005840d052441c040c25110100340004081d681e080303180010551002c030100315030b5807a4455589000601101120509810341d2280c5840303859407801c0e40e0040300c1c241d6048611405100043d41e100b00011240340031409019805136404000981e1803003050009000c100d05200412640000300b610140c95480042c000c101c2102c0b03d26281c410204208040340c0300d00d05d0205464900c13401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 308971699 1250 308970449 308970463
    0x1f050f0316091a030604020705010e010501080d03150b0306090c0c01020f120a140f0c040509090c030d0503070914041d0601050411070206030103020d0f0c0906080706030e15042d0204050108 83
    0x21003c14604696401062100070b4104210075501da64846064114130802031299030301070043c0354080d0448c2000c49001405071000d03c5414400400e151404001030801e08041d01c0e00000102c581c8149925000e440440a0003601001182c071352000910000550b5401d0003040201c00000b4601c2c590740d94901c21600716050600450345443c42d00d00001d0260044c0b10005510a4180620500b03254441300412041142102d52003a42e40c4403007403083e424a0100082c09420300540781051541c9401076004003010420b01c116030302080050f5507041541e840b0380254024140c00c07034461256203803a4418954a40f42807051074007641c500462510b0341c01001003115002e94026080c103155928503402d01946c812942c00564112404840410010302512902c10051160b040c1c081042800e02e04103034107025140c0e00080038545440f0072052003050200d489110061146c001070780d1646c031070a112034009000e4010b80d50600940055140e03001c03e000402c581180255420015070380c803604c0071a03407500d07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 308972949 1250 308971699 308971739
    0x7090605010503040212030d0f05101715070e10031e050c070803090a0606030f0308060306070c02101103030709080705100519120212010e09010501051f050f031609 72
    0x8100f0001d005804c00050032039555203d50202c918000d95403042404690005d40c6864031241c80e1410320800c500e001c407014001c1d000d20f400741c8000c586410811650340100225400b1142d26040000712524050b5141444522010b000120004800d48000300108544a001e03808280d41320f2034404600c10303034801d03a132141c40301440d098540021500c1c2c40029400040040741c2a2180781045400512203000e00b0004500c6a10a00c003040418a00980a42d0008010034021750010080007007403507101e820884005e80540320650040d8400408481c0104114400583d5102c00002d000d8610380c4540c1510460f104142900c2d9034075140e404001011484000c280f00095080c06403851764400903d900900500a00b000d01c106482450494140e800142030a10026000001041080d400007071440d0304c2464100200490343c1020001021810b028110006007a00020181441401181101c403924240e0242944a26010b10782400d18000307000031302d0001d00e4030b2200007008940c503850008141 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 308974199 1250 308972949 308972957
    0x20601080705130b03010c092d090e0c09090d030b03060402090109050c04180204030605130b04060533010f0801141903081809011409010302060d0e070b0306030709060501 75
    0x9207004100038100352124000b55031960707a88042061350368244100c8009070300b56114021580d142402e07040030010180f481e07402c1000c2c8070110140d00e501c2e414a21040c0c0f20700580c00a01100c0c400318003440c02070740e2951541c0044800c1e050003012040000c0741404491182d4007827121507152800c0c5034441d0401d88000303401c041070314014800c1d100550805684000c0e6509102e00b42a51a0142003a141d140c002c0c410350194005014400c0c8011402025400325404000d1440c0d400d0300e550359000380000030006026144d503440452045940b000d4010746900903030f0174441118030101640100d9503034080f6a075002c1540b0010001d1402d000e07040e51030403110a0b641a000f114808414000480e9004400f0480e448110384040009298040508400a48a1101550401f00c081801140c02d010780018074841000c840401540d50389200302c82c1035030380c103840041d00c0700c058680c0000680702c031600c030a40c0d031f0141c80d60108003a83e4881c003552052000f00c046400d03460740c44001c01308440060089034006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 308975449 1250 308974199 308974213
    0x81b0a081902040f14040605070f030c0225320d0b07141207050a081812070809090403050a02010b1906110a0c0609140906030a021905130903030c02060108 68
    0x5458103612081c000c0402c4000410300075042e0b40c00f42c00d20b0200300d400300c0301f50342d442050102040e804035241d80016a1814100000201c40c00b01030760b98107290702e001d120758208a004030a540c6024071084010000c43d24030380d01422768414442d40a4041020f0009410700d5101c0c00c03212450466844541c454210b8251011134940c6882205c0030106d1200d40c41c2c04100c204a9088009040d1106911401c601c1d0b55490311581ca400e00108820405070204030380710482400c443c1888004903404110f9112403400301e0395441d00d441c00a101e406828070050b44510424100310038590881c000b8a1519900e9008014000381c0108000e032000d8400050680e82030005420300069028000070122001d0000455000c6006552070a01507000c540040001984111042000351565070068151103c1211020114948140802d503150026500a442598160200c2d80b052800803060303005000050701c80207400c802030700d0316030190525002c02c400281c90445100902c51000c05c226050301e01c078002409203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 308976699 1250 308975449 308975453
    0x20705010216050f131b0305011401090f0b0a14040803041a0c07180b090405010b0a17190f0f050610090203071d01050c19261c0204081b0a0819 63
    0x881110241c1729510715a07509080c02c10000c030b0b2403051040f610385540114640d070415000e8010240420401d9040c0301d603004041c450034009420403000d440320301c2c48030341e10b420051340101c0320302c100d620061842010004000c12480301c040014015140000400c181c0056810641b01d00391198410020481d00180005c0c03040e003115400b00900454400c1c80403542020290000304d41e80801e903012505695258030b032008034105001c6a20091031544d01065038a021055400e4490310320180c0e02c100c002d00544494200201c1d102440c141e90380002c0e0510a860715464156a41c103415a00c0e26507034900c0c01c000251442e401d00880e40720341c40c2651107040c10002d140b02003400c2144428254180032092002c100785940421a83d0b90201031039a092a40d00014140401c001c1210b00c10070003501075541c0c600d00f43c030f00c24004441c034071412940054038040305040f555000740900d130001c610314060902c039946030740c91005400005440803070301c400009070b036001d84964401c0c07207041c00c03d1080c0881c081100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 308977949 1250 308976699 308976709
    0x7050a0e040908031501030b01020c03030d0504080c0f03120c1603030b150a0503151f08060a331d09040f060509060a0c0e0108010909060605040606020705010216050f 73
    0x24032080900007140d140030a94408695410403103400e000c0c0c0400c0b420410300c1d5a07040c0100b50b40460b00380050320440c8460004681c403031280b600c0e1051400d440f04080750800c43c400c0102e51010800350706507198002c980c2c0c0741d280c4076031001101901c42180038010074500d08440b8111482148124001c40d5100c00c00d5409801800020003e5540150b0f0060120072070654040200f241360340568580c0d40e246058504405040300781c0d08150b000340c081d42e102812402c0601c404040746103490415007000d90340d101c00900d003401503030850303d00c40102d1301090390102e10f17942065415000e03c135060300c00f800c02e41c2c1c400c4548017100e1216580041125080c51154188680d01c150041e002d08510b00402d40c0584440301a9071381079500b034007540d001c4030400c0089800383c4036040010f42c03985440d911020002d800200303110010b0050080c050f40e501d681c60b081100da68010001410040c100340b046964503c0082d440c0c601038030406015020b04036003c1b002d900000104020364000400303810b042115401846 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 308979199 1250 308977949 308977967
    0x6060d150302031903020111030103050a02011d0a0311100c050c010507030201061703030106080a0204080d0f0210112116030c02031314040608150c130e10140907050a 73
    0x114460103980c03010000d40c40502035a13403107105070361040341c1481c4a440c00a00b11004181003a940380301c244010301c0080c101041004001d902441c0c0218183c00d04455111050000c00c00c0715440f007078201c400410002030021501515004075214480c032600741c10213076034070520244020400d400900103040c4642c043d40252400b50301070b01c000140300d6218802503009644010404a240d400800100110303580080391070f0307220395041015401d117032502c40d0b119070340c18422440344207225402c54440100352080282e01c5221401c0c0c07006025900c18200084020742c4140034840402070320100c11509078066030502c40c0900c4108101c840f000c5400b10003103005007141c0301c0b5101180002c2043c0070714400c802e141507003c0c240c0c0e441021403130100d40301040100e40e810b621035030180e0065902024402c80d01704069500c008070000381d42d079584440081c92010121900001180c0c144502482010030f130080b10403003560700c0b844042c02c031520160104410554200d4030000051001c010701c410f4540b06820349 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 308980449 1250 308979199 308979221
    0x1b030e010c08180705060705010e06060315010302061e03100501021b01090b0304020103110c01020324090411060d060305030c06010f150f0e1507021504051c080f030903040303021506060d 82
    0x10b0ba422545031703030024813550321840040c0c40302d0307440e610300350342403001130082c5d68012400310020011800744003005001544144406449a000071555811881119058020b90420780c40c03240d9481c90201005101142540241e0b80107125106a40b4001040701d8207402c1039180c161074081610f40390400e20481680010800c80c109900c410090140d44000e0000c1e000c8460b43c140007513100d15280410031103442c02c4031014441015101c0340c2035402e440700c14940350000d801a02480250710300101146c03203445514240d541c0f41e0302d0020000f0900c20044003030700700091048182e035100e9a940c0100a0000024054041c0c0000b0122484200c42d0188035001e80460185c24055400d50014001948400c03030200190700880c40020700100318035106602020321004085110f080508000c0440c12441d07040b0701003c4403c008154040500c02c1c1e00d802c1c0c81c20642c1d6800030303d07924030700081910340300e03045440304602610030365029099808050005910a000c06441e090501038200c6204014060580403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 308981699 1250 308980449 308980453
    0x30603070b07060e070e0702060603062202010201060806010f03140304080c060304060b190302030d08010f0b07020301091205040e010f030827150307021e070b0a0504091b030e010c0818 81
    0x54440545000c0c8200d40c006c04442c4e03c619114501840003a05015008200a100760440010030040e90b0004802c2c1c2ca200c01780c07035440440c00b4603900c0142c1c0108030035080340312284544070001400e00c151040c44400c1e42d00c40c100c05031002008241e483d5603409540108601c2d900001881d83e2141010320140d9407280c0684400301d01d03580003401182046550181042340d400c00314809106508003007007543c80203401c500c0c210341250314002000411001c2400f4085400000059407015913a00b500030703440d0a9041851144059074010002d03106500c82c1c415410001c0000d0000076242c8090200981102c1e0401031842c544003100c0b005048065048180c9407101c1020366980c07030241c803484d08030103191054041c0250380f810308900c06440c000c03c5101041a1407076408809080b10000306481c0b080780c1191800b5a00c69044120a840074025038100d202420301e0807482900312070082d07940344108c00742c0e5182080382000582c112400d032480222018003040721203011801c04114011f10044410902c42 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 308982949 1250 308981699 308981711
    0x30b010e031b01210b1e0916090320011b1502031b12040b090109030e060a200d08060607030507111f0503090105090604151505130c1202030603070b0706 67
    0x5190040c00442c0d600500100741c2d902404402070614048440d00944031242c595883c05845001030545400140100d5071403c2c0651030230001802107030f914000e194001c02c4804424050744940d10504081c41600e4001282d80101e201950a0303400040d040c43c1d00415030110500f031000111000e076001522031001c501450320105a11510750b00a0b00c4000c0d51450444450f0509040c40c80c071040002d480010264034000a4600081e0010000c0c01145c4c02960000d860722500d107030680d2907001d00c015040180d02d107402d000009600200300d0503520740349501e0307006150f21000103000503801780e03400041c0890f83c00c206e02400328aa4801a0300d0f4140d008141a0415111401c10851103100c079030300c280400c102005000203400c082c02003e600c440541c00404051510303896a1a00340c0d944540a402d03a5696038a20080c00c03450300140f00901030141400c508001d0048139500102085460322001481148440f402040180222401044001d0040014a080004042081e444181c1c200c03140c40e5500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 308984199 1250 308982949 308982977
    0x705030d0501060f1e09060804150603081207020706080106030b030f0709141b0f0706090f151802061b0a020a0801050105031c09033f030b010e031b01 66
    0x301820b03010300080d560b03a1622040d800c201800d030816401120b05c1c41d079401d07154094002d9000d0f802d081190b0343d6262608040e101c50030300c440d400407031003c00c200f141d00340b070804010f03ca026802401c00040c40310390300c0c0301903803402c0703080303071079016a0065a0008541200400180e482508002140c981c01000ea80c2e427203c0482c05140341c40c4842d03000c070469945480800d00d4200c24085102d0b030000304c80c01c8402195402c1003440c003151207810842c0307040341d601140b44c034203104260384a0f400595000e003040c802c51840741803a0801512110804024508000c10360a045d04014400c4c0c64003607015101030b0802c0000e41c00380c012480c40510707280080c41200c11540c05a95031005444c0241444000069154108424981406840d0001c00b1a4a034240f000300c44440d4403900080c22a03400c900c285207500d035070603522007442d1000c1585210f508284007102040045901035800042c1d2303035440800801045800641e540450415895496040700d61743d0700f0f003001c441000e000520030500d0300e00c50104450b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 308985449 1250 308984199 308984201
    0x1d0f0d0203150702010e10060e0703091707050a02090a0e060117030d090f0201110a0305090f0406050315060a1e2603130306050c07080304111c0302010e06010f03030503010b0705030d 80
    0x40f180d03c00180c0d1206041d00c0f03084804d11403008081460b8000f07104880c2481039801175514090700c80b40805030340d09055014800c1c80c40c2c4101c1030741561440507035540c885080003a0b0303880218034103912a600c12408240b002a4034400d000c2030304030340b0010f4002a860b1078804456002800707410841400f003008601100001d911031813a10070701c901c5807610101c443d40001480311204400c072000d2070b8041105600426005000d940100030200c07070755801d4900c10380109010b401d40368485a058883c03070403803402081720f45940074401e4805450000302d15a8820f5600c1600c040348000d040d4908601d10b0034440c0c21075a8400d4100d86501d4041600080c403101006895580311180421504100c00810300401030345000d400c1c1c06c04845100c41c2d0508041e5211a200f5100c0036000805038050b01689129644580081c085114480007411110203118240640a04000c0011003414092803002059914004080f00706407501544c4a60450782003100c034500d268410b0350159030910091203d505080c1a03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 308986699 1250 308985449 308985451
    0x80405070f060809060705120a021c060e0405010c031a09130215040906051e01080405010f020c071a03130201110a0804180507030e03030712020c010f020403031d0f0d020315 76
    0xb5545008640c680b1403c124241a07000e80310303404112040194061407205040744503040840440010703503400720070801700e2020752601c1c0e002802d541814000030b1000d05005206200b140208001d0040700c49184045084844a500d201d0004070720b9015421181844a505540258803011011038055240c001503850f141c001c0e44044054400034040c0000d41140c050400180230907166010702c5032030030f0610703007074080c07001405810403101c01c00040034850250404190014481c104559403500e8440040d02c807000e5010f10040000502003c031222100001100d1161008005040c1c02040136401100d4a0341c0002918a0505c00c00b400c26000c1401e1400500081c408051100e0201282400c081c080d40c01c000c0c80c120506151050030401da660120880380e2100c11031401d082c11030130039158400280200c145103502c030362801c1a4050f200716550700400035079001c1e4484400071803540e001000c200030241c5965070072102142e0010418103203160320406480c4024282d484461110501c0340041c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 308987949 1250 308986699 308986709
    0x807050318011b08070f03022b030b0f060f0906040315091731030c09090c0512071a070210021c03020408070e04020f06071212020910080405070f 64
    0x44546055000da43c0c0020b5440d144007040d0120104042d403503119203626000d8500c0c06005030504000315820503100740441c0c80c00341c40441d00c01d81580020601c1486040c03002c2d001038042454003050b001d0a16007c821940001c80c02030846117407100b01c2d0f08407000d540001a0381e9401101c01d01011002480361128040035030020032001940052600b49010b207100300d820414040041003215081c151090781300c1071142a40d010300c0d011a0070300c040b280220120644d0010b0300c0802880e50200e40c80c1081d4204100c1180500c80c0e000c0e001d502c6004010280070803510248180d4000e64041000101580c0c0018008208041c42801d01c802a0041540d100110025800603042342d500c2c103103044101002c40e01000c0700f40c07a00310309090400f440d5607500e80e62800303903000c180e0381d010002d801c640c4c41c1c0c14106403040300a40455129015464400b10041c814902c010200750510345000381d801e054230984506040c000d044504682e081c51003610310000280083e61240150301d0081005c40700303100d203032000341 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 308989199 1250 308987949 308987977
    0x90b0708030613050408120702120c24060616020303040b0403050c0411031005120a020a0e070f0c2a05041d1e060408210f071205040b010b0708070503 66
    0x8540001080f003d182000c07190541c2e5460507080c000400c08100503109845ca2446400683e502c91400c00d91401c280d0602c0700e00170840009000b83c24200101d01101c00760510100d4503480001b80a1201604100310b601e035801000c00c0c00f032082400000b4009011441c0041e06527454580c4450040085a000d41c00982711a80084980c0742142418440d0000700c1c1d50700042e540c02d43c00c01c0d0406d45041c0d0300c94454a0320540c000c3d11420300103181408440342c0540e0080150000a40c0c440220382d40c3d03101107031502c0c081946c5c0c2a59200c440c2c0a01403410485a000d00f044185869150610003407142e076000327442d40100880d402007469122481000c1d8405040340301903041e000b010031407502d880c803200600c107114a103941440940c4100010019007041c1c0c0545101e440750307054591641d11418480b001151510010140a08112070420040c000c0a00e40d980311a0411035080c141d0650708140c3d402044150b003100100100d041c4003015107107040c4110001890309250741c43d01445e60b0800c1022049031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 308990449 1250 308989199 308989201
    0x30409061502060c163206090607050717090a0b09031e10111201030c0314060403120c03021303060c170108030a0f030e010c09150314060f01090b070803 67
    0x1a860050051108240610003004145072282044221340a4040e9440700070b800d5581c62410001522034401c21b8141c00800544009000d22102d2100800c2e440540741c94010040412440c1101140c4244510f2080c2c4426182a15664414014000d400300b00441c40300300740b00404655544008841c02064004092522128000100f50030004100840355a600c11784040c0c2c10240b0001c0f510002d400941640001d403030a51001c6100c05208880d000c1e0004994000048104940045800c0c180e9000310f154901074012070150640d5480b00b0b8402030701046001c814042451041c0d00561500806450054203028996071003412484694108942c6c058803903041c0b42903180d008400301c5001401404942c0c26500d0001d0f010780764800d85504d8000c102040d4070300000b450107a009510940d2003500200721f510390140340101194800c0c0243c00306035a1019881d10914468094110b0031518400d5140c0c00d9120041000420869010b030541801a00e010009000b103024000d40840c0c2e0261100c1552 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 308991699 1250 308990449 308990459
    0x1503040516091a040b06090d050114060d1e0201050c0109050705100504030c060302070809132013060818030406050a0f0c0b070305040f08030117071205030702060304031103040906 79
    0x207840d03501d400c0480d4280c9040405000702040180e0305528940c1510002007404c40c4070301141c442d129a82d032842d00003d4000c14003041100541c08000c0c0302d48512664181c5490786810800410030004000c0c04865458001c55242e00c80108101e1240748141401c91405540390011420b503180380a050780c907600b0400b401c1199090a0030000c840021920f05207103000c2c1103580e0400c454800d409060105030340400c190f000c200c0030408a035121072000344030084500f20700c1d1b0780c10007401c000b09941d5a40550021074100404400c2c0603a0987c4200b4290314150508000040b0b850321002001c902e0314002041320b0280c41031f01840280090019a550107595441201c4060701640040034602d0130080600c503074101142e00012400c3e0000420700c1d0104064455042c0711504180300c0001034540702d00007000140c1c41c0004400f1009100c10349040c0c03144540e40340500c28800000d02e030b01810940040143e0001403800d400255407091280c20300e90100400040ba41d407a6411640080d030126a40d5031041c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 308992805 1106 308991699 308991733
    0x30f010e2d060102010b0f0907050a030b0406030606031703070f050c0c030f07050f1206010b070c0906060c0605090316020f06090402070f02190e07050915030405 71
    0xc008124001038601c201064540b103000d58a4080c0355012130070110030b0090035200042c501d2030340ba80d41e02c20650382d41c0d0102c45004100b42d900c40d1001c100d81e49920136036020b58001c18001584505500e44410f0044003c1c1140100d250280b080100082c4d2000750781c0c1c401201407411646500c029600c0c02e19280220881e02d0b4503018841d98220f131294000360b600304440d0b04031a981074080f402820b0101030b02a034150148981c000c44010f1140e803181000030040300b44a882918a0643d543c002c541c11103a00303030801c8001465400d500d00034440b50703016143e0030400c0307400510701c0c06030b0184030000e1103d00d8200090041429007601d02c0355668140c00d46011003c09401075694024526003400702c1007005501701d200e55858210b10311080d010001034030680c1c000c880341e0300458445002c1518140c11028034103601400c21625508a0441880a50300461041d001000c83c8424104994 = true := by decide +kernel

theorem cover : BRFrame.Cov 308812949 308992805 := by
  have h0 := BRFrame.cov_init 308812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 308812949 ≤ n) (h2 : n < 308992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
