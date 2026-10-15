-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4220
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:54:55.602831+00:00
-- url     : https://prove2.me/submissions/d084c7f1-486f-4ae5-bba9-534d27647c1e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 758812949 ≤ n < 758992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 758814199 1250 758812949 758812981
    0x10f0e010e132a0e1b0405060f09010c080c2b02100b0112110d060503060702070e07090321090927110303121609150e0303040b0c06 58
    0x9101c0e5100801401500350320740004142007500110001600c03008101a003203c0788484010021003a0342032400644040e007003210b0303881901c3c1840e024492450071206000c0511540c05107680c42a428000e85588000505c007905e441c00040c107298a44610b00c5d102e000150b04208261160f40d03014141d041c050705000140c3c01c9509002c01b5110111120840d0069121040580140101551344203d9401c40e03110742e2205480141c034410401142d0344404807460b03182e02c0000e03100c030042d0512200040a0030b000880d5441840594041e0182d1030401c08140c280aa001e4a45400c000d0500700103c0807411038800305000e0700c817095020348001d85000c0c0c041d1a8500e29480350070381e245802c2c90342c0b0921510103103003020390b0a01d070201281d10400c0c1c40e20300259078004007441d40512000c501c03550b100b2200086240144d00c0e1001c48000000c000c1822110070045000740b46814100880f8028000c1c01500950b01c80e442c01030030349081980359540c3d00c41607002034047e24803960050060061100c41c800b0301f4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 758815449 1250 758814199 758814209
    0x31c02091305042d0201031a060403030507060e0a0206070605091c02010e150112240903020d021002071a040221250f06050a02150106030902011209170a05070506010f0e01 75
    0x500501c035a56104c080c102d129115020b0b0615440e180c12440340f590a641048488500900b900e0f01e0305d0316810b00801d40d801818088484902c1c02e002e003150f044001550307180c078a5006102920305003250f5640c10203040d02802000c8103100d01c00c070300c1605810049440c8901e001035800064a07030301c007007a918078041e030090700c1080010f40c080052100b905141509921190045d4151000f500148a22800b0303010031010303488120b00c3d2206480c100b40d4007042854a5030a1903086408401d9207200200480c424100f0040003010103003d990068080d07102d0199009c0d000034030004402e01a548000540800007102c3c0005400240d20040071203800c82020800c40070219240d4211800e04020111200c0240100c00c00d004c008207010304154800c02c0031701c0003901048001606565101c001034090b1414010490200362a42c00c42e0900032994030440281c590026203500005005c00b040c003481e03a101619810030000104105c80201e0800c02c1034a000f802e03149283c060940c1340a0501d4104001038002c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 758816699 1250 758815449 758815493
    0xf0708070e0607020f06130602070f15080702150a05071b150e0a0f050309150a0c061808040f080c06070302060c09040f33030203031c0209130504 64
    0x5000321240d100602010120007074444590711441400042c0c92444186841d40c0c1c88080000c030280841080d00e8060b0840d00b40c0d4089903001038641d00da01c2071020701d90003542c0c8040c0382c031380081c2e40c0d01d440713a808140c200c0d02c01c1c01a02c41342444000e4004480004556000c02c65885905001c061980440758411030480040340000c04e8900340e44210510354082250199251103044041990006110003440550f1080e1403085440d054501552603400400b032861082c0c50300003102c1d504200d964200c500d801d14179035401030005440d03660480206024005011103210021480300096540801080580fa02c3d0300801401454000d009180504500001f40100390a000c41d900180e000958580c101c240e048d0b20b592180c4040000c10018100300b0002c1d8030003805d103058030406c0b40350800e0481d08a14034981107520014103543e500c10b03400441c4802501540104800484c512403456080048078880308007500c1c1400200005044001c4d40b100078071700355030f11001d0208004910000d000412300c0450 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 758817949 1250 758816699 758816701
    0x1c090c0510091d070e030303040b1608010303120c14040b1e04030506420a0609140418020409032606060316020703140a0317010503030a050a0908070308030f0708 71
    0x20240c0b1100d440e903003040d4a08180f800880d000b00c1c0240f80140311014041e00304e075203c0c9042c0c20030781e410480c2a24103442501300709045003103682c41158610b059a0b0941c888890030b003a1000d0502c02480ca8040401c10401b008441102d40503015000740300034000c403906240c0b15050355500d0600d4052580800100d13800400081000907400304540b540001c54020209011140f1188800c2059140e262603c00c4c2d1541d000710101c0c7c2c01388a540d4009020180d800c2010300b903c50034260380d0010140030307030004840940740c5010b5515003074104061284c141041031181c0411903000c50113469540004402041d80f06e21100d0040c120319000100d602003000c1032101a0034a04081101840050407407440b021503a091080c43d02d00030400c0c28000c60348403440da0004a01240c80684400c0c1c0c41404500082c51070001ca103109030b01d400d4882c107846004003d10b02d48503211a05444590000300c80301c0c02d00c680e9032000101d140040c40640c001b03502502c1c0c0c80b55289041001c1458903000105500107200081e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 758819199 1250 758817949 758817959
    0x181b05062706032a04091b0e010804031b170a020106210308060603130f05030c01110c1c02070905100914040b0414030409020403061505011707051c090c051009 70
    0x44d419412900400d01c2d11440c00524030311401d480c4034540000c10000d040c600d4000b0b1074403007003000740703c0e00d0080d03a100342c02c0d40507910044607004d009840103400103d25400540c0c000131542d1000300e640e440b400d078a0007800c00200c803100040e003200b003400c00983d5403404100710050003000304803a4034401b400f003001032100300d035005454544090305150191802000207032071703980d40c40d07041d48441d41c000c1d0250b925540d2504d092641c1c3c2d03025248294055081000c00e11105601030240c8138040c904c2c40160001c8211184000020040c40070224210b100f4402e00058140c018442c1501a40e120400b1548807410b250b402015140840086000d4020900401011480142e03038240c1056000a0003034110741001003861650281c0d401038401c5510004000041100c039510001c008802c02c8070031040b040d980e400560b405040402c403803584408c1000041c684500c02c00c0284042086d80c030104101c83c124000690856000f91411200441c01003410301407440c02c07422181d01580d1314603203000014180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 758820449 1250 758819199 758819221
    0x403020a0e091f0617060103030e041a040e011407110c0a0b1209030d110301030c050402030f070324031401061e17010905150406050703181b0506270603 67
    0x1500e015144042c143c100501c2041268200b0f030700034034040110f4207036000c80401241c0c030758030217100403000300e8040540480307141414000c070440844d640440d545152184814000500b0071240c800409550b42c00c0d21a6042d400601180c2c05040a80d1f038000902d010702ca8985d20300303c0c0708591f03240701cac04107042d08009a005210881740382e0308103c050900c1ca034540741500392175409041020601c0038109640c001c044000c03100074504807409000004001d0355681d061004a100c20741c1c0c400040e6410b640041c0a40d40660041015001c1c144079844a0301460380314007080242580086400e5004a01d085911580c2402510041c04041e401402071102c034031450110b000d01842801c0b0002108132201c00054400c0d0b00c900384443d0804195030a0710b1200100402c01001180c0403160b003403070f05000c90983c034800d10903c1490010300c60348041c80036443d100c4d4074414982c08040000c010912402040e40d407980d8000d04800e541c1d504c580e122040c0703024101210980071a00c002c0c01010103108010742000384c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 758821699 1250 758820449 758820463
    0x712140a031503200321090904030e0409141006080712061b080610050901020607110f0d0f09120c03081c020a09050112050709051e04050c0403020a0e09 67
    0x1441c203002920003908850740303941610540c00980700107042c0003134106081000003e074042400442c16588120b07240c0007000180305042c00c1c1c0516000b000d100450b8607040603400030350014043c2c02c02c209044102c60000d000e42da50340d4421140240000b200450100c42000320070034001383d10070240300c072506120f0760550311111841082e030b05094804015003441500d900c042c1e00c8560040292184d2502010042e220681c1912024014400c1d84039448040303108d5002d44140a8059000c0d006903200c0b11021150034512a0000c80c050144c0c220400980d4030800150f541e0454680301c500480c002901c001c0c14882d1507900590030744007910750410000d80ea4002341c01c1901e40c0700d0401511203c04803540a800c12403402401415480000e80b005c5a0760414810740417580242d888014a420602c140f406a64050382d103600403e00c6032600b4030980c5001701002c40158041c2181c0a980e09100c1c00050548a095030500b461020009050040d4100207250501800ca40c0c05454014180100d5603a52222 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 758822949 1250 758821699 758821717
    0xb0405010e151005121608010e01140906120d03060e060307030c03120c0f1511180d0201140714071710020702010e12010c0e0319031b020411071214 65
    0x100f0880188403280202c0a40e0b03d42468602c0b03510507460104a56480e507405000c048012540c00400007402400780c502e054145c6064101c00c00344003480740240103203000c000d40b0940d8040c82c10070541d142c03014104420200403281c0da601041e0786141401c0d110071458041d069500a400401c000d00200b40580c0c010350071654461110750068040031011203041041a20050420b15221003d0051009141e400010364004c8402000601e00110b0081841e1082c001000f04000686450514520340b03c10a1500385006041038441d6610480b001d05486e8400300003281c0350040c0440442d004074040244070003030305228408450403042d488940e9078901546c07201c1048160001240002c42e4811986091361203009000b81080e2403045000902030f00f031501e121000201030041ca040d4a00e00080d80700544030520420065500b095101200c40c1c1d00103180c0040e2015003140c4080c010b071114440d85800c1804c1400c401d40f10f4802e8a00450b5100d141004e00003003004482c5406505100c0b1030440e01108 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 758824199 1250 758822949 758822959
    0x30b0a060516022106070f0807050c1e030703090b070c1809020a061706040605010527190317030c2517220e010e100b0408010b0405010e15 61
    0x80c801c4202e80e5410300340c0103000303400401c0852035000b508030302c01180d110321400030280c800c3d035a01c030355044030000210001c0a00080c2c1030f03000315082c140680010291185000151480c2c44002c030308851301403510701034440440c2d2000600348141548082c00b000a00318074090300d85044055120300800d0f280c1e80c01005401400d2684401c500b940da940100c86050307001d06440b000613030b5640c0140c007860314084280108288080001e02034506071007440240c99050b1101c0c0c1c144549604a5008544080015800004070340507a00c940d0361141c100c142d514500d00e2402c6140e03401c503c2d060969403065580c0440e021828824840000f4407001611080c26840c101c2462102036240f501c0c521200d03560000d03000e442c18040c022132004d1000010248040070301c0c80454101401d4001d01012000d504c40c000c1c5008102c0d005203c400c00f181441500000440040d030758440c1c440b03403009201d0384079900c0005140e650b000c8000072424280034140c0100005c80f01c20070186040682c0c0c0100d0f204919140d4450 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 758825449 1250 758824199 758824207
    0x715030218060919030803013b0901020409060b040f1a0313030c081201050405010510051b070b0a021006060c051507091d0a0f0207020109090b1c0501021306030b0a0605 74
    0x158030b814400000001410380e402c9403845da00c1c00c0a00807a402030103240001c3d03a407420340581c03a1202c1e15440300c61b000c1481102c00d08000b4200c002c1d9441f140a04075400954007004000351503141030060801601c0e6020007240d840303281445803c84401c2c503901090003501c1040c049808403160030140c0c0e600c081d800c0101035240d5080c1c94125042041e00e007000740580001301e82065910031010020b81625010b4404010a980307820030001d003121070810500005008001d10741030201100d03500143c0c43c1c7d18000f11498103880324042c01c8580c12103d641d10060780104044000100345007d42030040c0326a0400540d10b401c0ca480d0320341c4989002d00324003030b07030110413000c1020030b8420701551000740141c55198a045a0100c66900703a9841550f45005460038031041e0303900108680300700d41c11940d05840c1d0b000070300d140c0b040c5280904081204103130b0108000c0f01000f014411901504402071040c00010b0ba21110080040d14a1002e81c00c04001c041c030703003444001c2d6134960b8131039203091b9600b0707081043e12 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 758826699 1250 758825449 758825467
    0x1d0106170703063501023621280f050c0406080102121f031203020c0307060b0414010e070e13090f0b010902070809041814071503021806 60
    0x2400c2e16510440e048200c094841c242180d44025604c000080c1118038914a01070021050a078010740a010700610810104160455881d5044030074661265002d40e0b04100804001113a024035040d242c0303103420001c1c0e419440c542092200c40b0000e4106044100c0516003039401ca102c80708403050040080100031b02420612804000c81c04440301c00030070a0203610f440e164014040d411a03c0a03901e405076100100c0e4001c11f41907903610801d03c41400b480303806495038540e02a1480d45032524000d240e070802210b00150f02c1032000300303036035405010085a5500d0740828042120072454035811500744020043c014409007182264010b5020300c0d000c04e04005c1c0301c0c00241c020300000550003001d843d02c030715001008441e45102d070119000da1034840a9a0303030303240c061050b0703c60500000c188803410050245185403960001441440315200140015160f542e070011004d03150581c02c000e40e010741c80402102d007400480e080202d0b1a40307403e50900c12800801101441e1112026218040104503620 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 758827949 1250 758826699 758826701
    0x3060402030a0e0f03130906050306070507140d0e120f06072006090a032319090e100e0108160312020f160906050a03050303040201030504110a0603061d0106170703 72
    0x3c02014040c081c3c800465100e43c07099a070342e200301c814002d001202040040c1c00c1c5080c0c8546011204d010700507000c542d50350751084407260700885d001c0f81c40e00e00004118905003c10480340d92100410703103d407003180500c01e080010b5164401c0d40804180e05c603821010a8403000300c1c29680120036030070a12121500c145500d003507030039030114218180c45100c04100415000003075400e04a0300a40701e19428214a030002984860041d103ca00c004d28200800020844000d000707118410f01072810300d81c03050b245c1400308201c250503103d507030030400a5042800103040e8918614010001d81d0014850802e1019803c100160381c3d11010345020340300c529244e165130080c00010200902c00703064030481c0e045516a0700440f000750042498003841c1201c00702e114202a184101130325081030003142140d617203a0044003e80030003007089429030301c02c4404480e075844060b0b501002d0309040d04c000c11854140442c90b042e0100b8001c180d140d60582d40010010f242d00860701c0c0c082e002043e44512081e9550300c0041d8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 758829199 1250 758827949 758827961
    0x70e1501110f100b0405090f0d140f0a02010b0a0f12110303040815071b0c140f06040603021e040e0610140d060e09070f12020f03010c0c0c0803070803060402030a 71
    0xc50180d001e201400030f90a40c03080d040b08400320b4080000740c0340c1c040e01540c1d890740e14040303980c04d81c40403a42c840958080d8521004161101a0705444d1213412101c84040ea04002c90050241c2e4580c0c17002e924500d0b1808407100a04802d4601c0b01d40140b0780402491340c03040300c2e4005049030b01c6003007136602c490b1028403c035006028904100d1302c00d00a4800c20518030781085032403100180c040400302081c028030301010a00160071400c0b41c4280760601d0301650070501d90030041360b48680920405966501d4600191009142c1c54078016150092409031404442c03001c015580d8088041000340326140b40d180205d034000405989200d03803403542140c151100e0f02601008403c54401203004c02044443c0d81002003138401e039139040c0d082d5444819485543c0c20b603d004410a410304d010042c052280d450348074022860006094200340c1c601d5202080c01c490031350f603e07100040c045d18030308002d010800300d030f400040003035000851620a03035403502446400040c08803417046800202003505055960015 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 758830449 1250 758829199 758829223
    0x604060302180915130b1503090a0b0106181208190207030803101404020c0c041a0d060c0329010f03090503033408010e040602040f0905060102070e150111 68
    0x200036941020030020807550082c0813840c0c81512a0400f420b050200390103a10716060b000b52428061f0750701d20b54960150b0300001c00c0742e00940f0582010030041940691036a00814082d180d40308080c1c100c148000490085030004001c0f1410300d0501400a010740086400c0c0b80004520201a0106004100e06008013548090a0410701000303009185801820030003c4508407181043c4903003490062100346e000e941240d0a403900039900c032490318101900100c400001c0114070050000c42c2c43d0010341c14012415080d01c2c180d968017004510b103601071140104542c585910b152101c50b5849800c5201c0c000c00700294100029040c0614903203000c0d402403440a5488010b43e5100d00c3d008070458400c0c8039450105055002420010004000708142112000b880780da548106a003440014001d0104c007a1080b201e40b0f41c204030014540c00854480400380c6031400c400308980c2003400009250010b85d820032140c034160b62040c40341c80840c13294241d100341030a0070020308130809102e440b82044240104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 758831699 1250 758830449 758830459
    0x1080c01080435091f120903050d0f053403110708040b0c0105010f12020607020621160311030601031a040e031e0307020705010831140c060406030218 66
    0x10701040c106281000e000e0160701a517205da00700f244900401052041d010302100810b43c0400e074107a04c8909500400c0609000f81001490620800b42d1a021511248002c11019039100240405c41d0f841419516500090860192801c085100b6501c1ca0b62103640400c0241651071400501100280c810b446003250004036060315103944030264011684904103130203480d4a46000072400b00d01d02c044a0313080c2c0e140000c210145150581c03d0141c0d0b0361019005990002003032000c1905a0741d00000c80744e04000c8101c07152014104aa0704404d94646a80380505042c102440080780d0f044d0b25098031341c400c1007464041030003900d290710300061006800b00140c101d41041000d00c88888004001e113001800740d0480209140000c1001c21940029980030300181c0142c6010045507105894550b0030060b40c5800600b0311303213480042c510818210520300344542a24481d03509122200b070341c1000d80c110304406003581054020005205101e14000d400c203041c3c0c086500c2000000d01241120cc03404043c02c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 758832949 1250 758831699 758831783
    0x201172206050403121a2803050309010f0809031e12040305030105120a0803040b06180901091203090308070827010504050c0604140108040f0204020a030b0901080c010804 75
    0x40c02000b8050031242540404c21000f101e41c1d0b10150740c45800d0490301c0c01c895860071194104100040307207210407080741c80441681c0c40720444600300d4544600030342c424001503544054800c0058174010580d108002444100302c00c00c2442c103004022140728040d2444940480c200d1400d4900303090040d840d520b160001250100403c05420000540c16200704451641c0201e0310850310030f40c2c03103111000081c940e210500c085000030385002d1032183c00c480d0003080b42500f0001502c0c028410b07002202c00540913910780c054041808250038000c00d500e052850b05000450701518081c0115601a115004100c02c103000904071003800384001060304000064400340d00440c00109028003006d4409840341c2c0200805107429107480002c40341154840c1a0902d100520f42c40103407031004000f0800d40740e44004411100059950348020540c2400548000952501610a01510481c140c0200c005948401051030080e0f03000b00880f5403007940205010240e040808110b4001c08411100c0886a543c0f04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 758834199 1250 758832949 758832953
    0x4110408030a0f110a0c0b0306030a150902012a0b060f12071d100b07080d0204061805040203010605070b060604050406030c06032a030c020f120408010e010902011722 73
    0x1001e0f0710300b007a03030744d44086078188031301101d4a450781d5074002002c4901c080b504020fa441e0b80000307140c2c072482c000c0540b040e41380691a26244d90384d51003600c906081d03840441000319030b041001c0740c0d40010004001e2510b080250310b1009107100303202010704070440c1e10303000a25640d204400a182440d0103007440c82401e2003018881e41c0e5a6090103280b240e042503a00c111031f191000100b0500c103090340702100b00814030b010b1031440aa4050f0703d066415034820022031180b41814001403009100f20b9540707260107111000d86d41c441c22a207401c820310030303401000100000d55105007a41d1105030031000c0c4001035159400000ca0903c19a80300300d400a080842c00001c0c040b504050030101d9425031000e0001e11400000d0700200300600260400400e8080c1100107100d01c25400b00340001c0083c0112401104140e410724a0318a4031a003e00b40ca050000e014030100c5000e010b0f405548100c54001c1c081007070321350300103007440e2060210140d562000c00002a81500c4c9505600104001c044054040c02e1040c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 758835449 1250 758834199 758834207
    0xb131223011e09020108160c05070e0601020d02150604020d0f0f05010312020106080613050a240e151f0e010b25050c01050f12091e070f030204110408030a 68
    0x40307001c02d10020918039200840115000b003055080c2c2c16512020786581e0901616030000c03018580030200040700c09201c002610810049020740a40036500c0054903014000910301401c211051003103400c09100228640c240b41c1005410140848015854a1070f440100f0010258041c040c0c242d00e003400004000700c09198000b50589000f031118617020280e8071401e9081e0b8545200340503042e030244000400108615000c0000584100c040c0c0d21a0560350b12604000303604444141a071035203849045080c25898401c0c5e2000107902400303010100c84004286400401c000d000704500b005045402550400c44485d03d40544007035020300c949035841e0f0801101c203800c8513140030450354170011544040c0e4602c42d5420207581e409801849510700340001101c10750410411942000024004501c070b0404c4502914850705040e001000e084400e054400991124180d9800301500840001e12081c560ba001c40720030380742c064801007026224810f03009131511695201c82d00500002c82c01035816644 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 758836699 1250 758835449 758835461
    0x11030d090204110708030c0d021b16300c120f032303070c060219050d11131a04090203040605040b01081c08090a0507060210060b13122301 61
    0xc2e20200894100200491141c0c441d16201500780c41d003c2c80018000301c0e02100500f44071401079400340c107140e190312503841c0418010b920380c2156003248200000c4610040e05d0b610007400f078902001c4901390881c0c0c0059004080d04030f0b81c40c50f0b4620001c8041488042196403008100c2c0f0b00322402516800d0402e0f0f03c03409146c49080b00040c1507121100c1c200d10264144069044400030034512303503140c0d11001d441035550000100ca145400380402800701a003030030561507606580d00c0d03040d91040030100e40c0003199100d0b9101d900c0510180805141800c0e850100c40c25183e074601c1500c4c1c24004030300d0b8020f031401241d10424034540000100030411989410450140384145441000c0381d0722030a41d162203d810803540308280d260100702d92081d91042d2041c030382042160003a03d0500c2c005480d0300d810703d42180c00440c0582c0c40005412000100340c07007000300420391160641d08140301d2075a121176201503441360003c0e407903820254600b480210f20703280080a1050028901c800c1403415800d018103d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 758837949 1250 758836699 758836703
    0x616020106050105040f050910090c0518042013090c09050102010f060b0d2c010e1902011704050312070e0a0503010209060f210405010204091a03070b090111030d09 72
    0x1003070100001e440d50148040c2d409032078080c3d00926809003820144100c1c40c03030062844864101440700002d003401d040c403818014000d2039032003a94900540b40365903072041121000d035010300d240010441818203031800d141520380840d0800e542c2c0c1c0c0c3e0440d496025107491074002443d91b9250002c000151604141c030030702200c40030f800038000001c00c401218100c1e1414420042404d00401200d04261519030100e070304201000d115204400d601203002c0c001c2c07030889040008580d03450340d40c04120201001030040039480c0881512030510150700003010b940d40b080783c0840200b10315020400300701c0706105854004081074610030703091802940041015043d4030755039004ea640310801081c030f428103000300ca1090101404031460050080340ba104994000200400c210180d56441e013515031802e00c00d02e0059004d40000b68070749082414010444050380c8a01c8104641000c5c0103409440100d181411656081403194071012807200580d030710f080c90724901806000005564041031160b51105034030364 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 758839199 1250 758837949 758837951
    0x18060f061302070c0603020c0f03120f0f04110105090f0d0f02010f031802060d1104060801030606090e1c02010e0a030c1101020a020303070602070602040302042307020613200306160201 81
    0x220380356641d5400c901c80e030003020f0030080c01242c051010501940091004032891800c44da45060b00007003090454100030460002c425000050104845071f83c1007158201c41442c3d4003a9031810300d556504040410f903052141408000310303140340c6039602d0180200080c80c0242403146103030a6882c100181501b02d44041b0701150300d404482d0007040c0319100700008250000314518154129408004140c0c2200100354174254a80e4100d02603100d8110207400182016140c0585950540c50424191401504140300c8246032031408100b020340000c5440043c6100101c100f0005041041240034103644040710741c0c7c2d0b10410f05002e080640c05140c0c4080c0601030800e08181090003001262256444c1790b020f54181d2060002c080071035115801071144612451005240581ea94080742c1698240345007809090584040005044864810154008220320240640e440e08941003036424401103009400c01260b5100010004148094100d01c24001821a0910314007180014603440c03807686158015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 758840449 1250 758839199 758839219
    0x31e09060c080106090b0f0c0106080f19080d05041b30030804121b0f03020f06010b0d0b13151e0f14031911101107030b18060f06 57
    0x10b48248105410b8801958030080348524004280180e0380240000045558080200d80d844110911800c1d0003007580720054002c048003012101d00f418000d10200c08020f14020b07007900081c00480447d20341c813109480015054445003081582155000b0558420384100e45020aa0f48050300301c0c0304243e203902e60701032401d07408201d44911158074924001c0101e046003011900050900d60864022507080c50800c0324512203902e49001030700542c50644d2880c00002410f400d0542c140428000b1101c2803009001ca5450060280810f00c5001c13499800300d56a0784603420309546002c1500d0b15040c0c020700501214061030f40004284201c1c1c0b00c5d4114511400016907054800f03172a10070100e80f030040c50062001d203003040c0703190060503000704652705016001100e095441284a0700320440e000c0c6405283c1a80034400703005c401000c14041c2000d0141c50500c09203c04000101107068981c00703c13141c4691703140d06000c01c4000c621030484400d14080c00b401c00190b0b44004140300e20070740b42120f4139403030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 758841699 1250 758840449 758840471
    0xf0601090605120303011a310e06090a2f04050405280914060403090609141e151c06050d11040902030c031002030115020c01091401031e0906 62
    0x3d1040b440c00b858026003050004100c030380c001d0400645a12000010b941c50f294550340c01080b8601d00e00726003240199800b1710400c10340302e403804540241c00c0082440c160350a2480000e42e4014005040705080c82d00c455510f0075030783e81d840d18500c0c40b52051080020486a00d0200c04154105008080c0213500c0c00000a00551081d02d5840c603c032680c140c2c10740540c0345480300c880501144031080d00c9242202c00810b81c5014100244c9105074040e660782c01c2190704203c4020213201140d88030301c81401100500030021343e646160b88030400111958074210002140c0403510302600140e003824120b0010802d1000c610807249040d40c00803c104003009095110000c04c00000c909070800b07801d040013003075501f1f17a50a0650102010900040440da0b11502907800a803030302442c20828100260040010031001c00303105440d440b401c0c3c5a0014054090701d50000074002c414030304c604020840d102c016800340b03034040d0740f000c0261024502005003c14141d0840d001030564041e03300c80c850318201e10a91 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 758842949 1250 758841699 758841709
    0x70f03021003110d02031003170702040b010807020309060c01110406120f200c0c03011b081308030c030a06050d030801081504050705060a020c0406030f050708030a1e110f0601090605 80
    0x4060b01e2143c001d050402010f4900c0094100422628047e5225100403002c1400000034044c41800594441e64450083c8107000944400300e202605002410043c40005c2e500401036891b41030040e600750b40c40c1d00e0070698040c05009414880ca50607030700000e000c100c141e0300881c0ca00030b03581072480500904075000450812240744911024140b03c24509001041200c1001400302482000031141184440c41c0060b08441c4030011742d0307046082010041d030105410000c0c01d41e01c1a0b08840300d0a10800c0b41e120035855200007840c0d48120040040003c1180300242d1007a80030701b00192400c04030041c0b501c0d02600402c02805003c111f0701c10003155000d000083ca2007240700d01c0c0e221b4041d01009107403500303110301038200410308401e5000d034040c0b44c40319881e10312501c0700560190110800c001c203241000360410405800080268004000b40441d480d000b4a1004020414403609038808403580c03000c803002c01c0002c2c0e2101180c01500f90004003014000340f2a03041e81c0d0344400403c180c030b64800400c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 758844199 1250 758842949 758842961
    0xf0e01080c03101d0111093a030c1415011e03141216020108180304150e19060f0f09090f110a05181e120f070f03021003 53
    0x7030381c503078800c01d502d503190181500410620740903185108020400120f81d6825101b42c40d007250400480820700300b0f000e10381119417600702c0410154189100d0440c0350400d2100000000942c800711110f142d5104051044042c01807641d00300c505100c0031106a1142521450801d2150689040810010800c49440e00e070101140c0d4903001d05a1840d4074507035420301c04104072394803020240980c40c0ea8044004848005007040718415104880340c010394030025014403406050101038030b038210100716801500004640503252041642c070070940c8500c40c00c94600c03100e110a603420064090b4910304c20468003c6040039103034580c44503c48250306d44800c42d06c4080a2900b9000500f04100c10040c01e1008c0d0302240c0b9040c021200401c1c0c0b41030303140c0208070503403082ca045000074400141011281c0012181409c603800c045400118402002e51903000108413041c4961040410a482c5144068200100600700f5000410740c0d04c3c0c03a9442e100402d4440306844181d000b07003c0300d0001e4044900c240301c2c0b1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 758845449 1250 758844199 758844223
    0x1140108160509120106181806020c01091505090606010806061806041505031509010510050a0e040f060503060a021201060503070306120b070318080301061206030c0f0e0108 76
    0x14003031a5540c41d4661100480c40031440c0a1040c01c014582d1103032a8918000716441541c0d00225071945041000c043c1c041c0d6164140060314509000c46038602c00c01d628542c1d0803904205d0140c1c6a0001400841c010030181e1401020141d038800ba8036080641600316a10461004003070314120741c1c4002c01555114012070780540e0000c82000001e440188900542c0c0e04148040c0106080c9910354001d80001e0b604a00040082383d03011042080d42c08513800000d007105000d4915100381d502d00760110340c03a00014000c00062050105101000920030b03010304a04540090080c00391090320100700c0010000c3d40a400d012380a81c00001b82c640758203000710740551881544d0001c80d42c0c40d116003102c0d03a40026002208064403072100081e89500142082d6042e4019540403609017400c01d0b001e800c03100320807001151300198403200c102041401054070b044400a01301100010400f41d1080000c14035034200400c103034041b90700400c0d1180a88419015124000c082e800d060742c864000e1503803000140c5034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 758846699 1250 758845449 758845457
    0x307261e070c0b0705130e0106021e0f0a150209040f0b03120f120910050403030606081e04031b06050c0c160f0308071401020313020102010615090920180306011401 72
    0xc1900e480c8140000c1018114079407801b007446803140100c05007840c0a901c8040141e0183c0040070641140f02444503032808600000e02c52548110b20540c2c03603103910310700981034240200100590700c1c46d90301141c00d225070090003000000041c4e080da0000f070980100490003403142441124001910100322060004640386990030300f0b00e044110311401e1001030a050480c0030f5180303105d0064595000341800b9910940b408035681e42040d10060100c1ca0051104c4400052008604404200007892640194141ca02454004404d82c1038131074006417081c005000130300e031008006034072003a107014140c10070075001a2140e6880101c228500c04209004420702c654100100700002103c01c8000c03e0050300c90741801c6680e0390500041400c9810894440c15203598110584085603030a2060300003030324848900303c0d05e42c0c1c07502c0c40c0280188101d000d40705200307580c1c0b015030450503805604a6028514000501e80d648001c00c4e1081800303d03500300c110700912400c000801c0c03022041102840c1040181c0d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 758847949 1250 758846699 758846701
    0x80c0f0904080c030a05190e101218030c020901050a051807030f020d0903080109020a170a1d240f040308060d051c11070b0307261e070c0b 61
    0x304030a10340090000c81d124a802c128229000006001a11402c01c05468050326003001080d985030462103ca0584100040740a15485541d5520032032402c142051510040f12044040c2c0e04000388170206d0446003401490844604040c3e0041090342e400b48290303052120b90f44d07514248800001c890007410b62066813034460b0548a4445007245902a0340b924002c80c00400034807022040703034483c24200100d07030748622445003819085003d9030300405189104500d086401e0b08018801007008030b905500c0380442c0080388022031640c018008584001d80204011040305019603943c4080b031040700e007070710303828880b40d910120444070080c440c0c40c4a003800c6071195203996044426800c010a8554030401c0300f024080481c80411090085041d031000d88508075003104405400444804074918070303544070240501200f90390034166a000740540c2480e201c61880215400c8080494041007403882c0d03144c2c810031034400304203405050301400381c52121b05070f600c0d0201c04582e115030b03c9901402d142140c0c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 758849199 1250 758847949 758847979
    0x6050a1a04051504080c09070206180c06040b12090a030509060919060801081b0a051c121806030e0706080c040302040203010801020705160e45010501080c 68
    0x441815401004035146916240e240c00014910b41085012280b212201040501114108000b8500301c1001196001d4192419090084d40e58800030300301d03c01990f90800e4010b00f140c04002011076442d0007010781d40c441340c48518186030703904560001042c0c0c0c10314002243c1700000100700e100c034140d0507641d52440d01554100b40043c50744807184880e040780c01c00d60b52041840c1106c80b048060013403030346c400c8025407410742002d16040c1c06030f1b00d43c40391801c0e2565005840d0b65030f404810407100700b5a2042c12041001001e916070a2106034042c0c01c180c20401c21441d078903070007818000c034040c81e40044d8802a444542c00c0b4200c0d1503612030650154480107040c1300841c042c03140d55500000c40c01405282544940c08034059800c2a442440540c0d000300700d600030001c040c0018407201c500c074007180081c00d142100c602180ea501409480b22607aa03020448800c00341c02c14845207102c865400200b19481484c9015182c0f000181307130080079460400041001d0a010070180c0a15100414443c15040b601d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 758850449 1250 758849199 758849219
    0xa0605060d0807060606030f02090f0f01110706030c080f01180e030418090218090604060b030c0d050d080c090f01120906050424091e170d06090f06050a 67
    0x391540c0d60000540c18214005600d4000814140c0d1007940d0104000c0d10740701015007030700e1400003403086090040c4006d522075194200701d80c1c000d40701202c41e601c08041010040e01e1055000b61108600e0107020000b0640c41c1e056040303960f440341c0079518940117903242607124048803028004d858481d000b10300309520042c05504801c840114070815039140c282e41e440c42e009180c402c1d10308000030b141c9a034005010b40c5001982d441740b43c4010f00e80480366140c941007032070b00d07060018802028a5907445000205460401c00380c0d110a60140045500d21201c0c1810b07941c072070003c000113000075040000140d03a6583d0b0000e440d1810b0b40902030300740368801e0900556a28038500070001410340d8419a10000c540240103140c040ca020329000300c1d0316515110507008480c009541d50200328201116540041e040384298414103021056440c1c00d50342d58078040c1281d0329111032003520804c0110340d80640e005a940107004072002581c042080d6801c00002d002036800da0f214442d8481c10026007003101c1c81d40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 758851699 1250 758850449 758850451
    0x303120f150307060207090b0609090403080c27130603020f010c081c090311030306030601050607020f040e030307020705040603080706020a12020706020409050702010203100302061305030111071e050a0605 90
    0x81e44108184007080400b00c1d01c0c201d8140e0240005a005403020014224103104400002c4026a4013505c0d02e211007001c1410301c1000b42c802001c200600c0001040070341000300391016520f44245049444090b101d05061a04200d141184124110503110050311383c00c2c801c01d803c4030b601402c0c0c030791680010b50040d0343c51120394800b5500c40108001d1100c200013092040310f81501e040200180071040f504008001e0b0786021424482d5074010010f00c1200d0780c0c000f0351141101e40441c2d11955400c054408102803174060b10140ba00207090421010300020084081c40c41405550300b1270780301543e10340412043e0341c51884040c3c001c40d82081040080346840e0010a20200103042c2a401c094001441c4012640110b00c25103106a010501340b08024060103425040f0205100a500b10308040780c84001200035803000a06c01c9030001503c03d4011080200400107050040c020051000300100c40c84031940501c50031201c0c0d040c01c001509455020080425001e0380100081165000c00d07070700c40000f400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 758852949 1250 758851699 758851711
    0xc1506010c0f06200c060c0f040905131104020a1403041b0b19050901051b120f0408060a020705030d090203011b020f060a020412030503040816050a030207050303120f 73
    0x10382400e01ea0301140c10007500c494014414840003580c181c0c03420306440640c40411814408050801124100e103200040b0960081c4a00e18000e540c0c0700941620407052017942c1c040f407038241c00d110030011000740c2440c2c4440f141d800b4684a041d0006c88004003c00c9109009603c400300d604441e05201c1580d601000c0d580c814814041180f00a9a2480040c48200e99900160780f1303840c0060540c10010221307200038440862828401d0405070000c001034110b0058203e952907981c2001046052a2000c112001c80041d0700c104499560420b0b15401d4016030150146170020321610300840c0c3d024040b8402c9880041e0094007031403c15142d0040e00d0064040030f1400e9a15640b10141602000c01401e802e88111241c5e400030241d5561101c65242407001c001e060b982441e106000400070b042160550400069041c070b0802d81c1d1303607514981050940600c03000843d80c03c403082078010800c40f00240564480d4042d4003203400050b0754204040d40d902c80c000c1242c44806600d0080b802c20541010280d420603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 758854199 1250 758852949 758852957
    0x1506050403110f1c0501140f07050d0f0f0c02010b100f112107021009151211161b030f06021b1203060406060c02100e130204030f0201090501050c150601 67
    0x402000f0008400308840380b0000721440d03d05800300c2c00c01c0070034818509503d04018440165140c598000151480010044000c2c014009401095084654010000c080103a0800c00150303524110000040c80054061400b41d0320348081440185000d00f03542c0c40d43c80456407018a95070380e10400b01c40030354200b6040d040c00c0c45008130b640400581038041494854000302c009889000500400610b915483c403000306003d04144e007400f103140034521200d09000b16040240031036182401040081c00c0600d0301c41140d55022540c2518402154044a00c15014410070562007110840c51125904203200003081d80951090039000106250080c1c03171400740040c0820324918144c0259402c0000702070b0700c1010600000200001883c00307200c2c89014088500d003d0660b032243d54003042d10b40c8007880400f030030700140e0081018165030305040a0b500c00d4141c0415034031640e591906802c60340c09900200e022404846012646500ca0025182c180c02c1030402004080344888440e0034003240a41a07c1c100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 758855449 1250 758854199 758854219
    0x5180c040603200c2a0a030813120b0618190f020408150123010c1103070f060c030e09041e17040b03040501110720011e030f150605040311 61
    0x110240c070301402d40e4200311000781c120306a00d407036490324040e07a05c1eaa04514100000c0700c1209500c07010071005c150780e4010341c0303141c0e1400d020844062441c11544000130001c011000001001004400240100c005450702c1c044842071903044440000c080702c12216030b819600a002c01192103400c201500c0660500051410f9103d134552401c05072400c121401961102c0c0040092000c181e40419540009040c016448401280001d0110180e094040c1210202c00156691755800740701c940c0080000b44e0f68610304913569131026080001e4041c00750041690f68181c41141e0404041140c811540840d400340102e03008070341405071001003181940c0085504201081c010f0101c0020009009890140307034076884e05251550a490403a40d02010030b090600100000030700c01c0141031160452005800b000ea5000d81c0100e591241ca09142c10050f9968811802400c3c0c0680c40419814441081440714081914104036900a140308000000750304000800c041285840390920720200200075042d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 758856699 1250 758855449 758855501
    0x30c03050a030f020d1d0c0f060d0605063039131a090f0d0302010906570201110c030a1205090c010e0310051005180c040603 55
    0x205e80080649000040c2e944000810107900e45198004800342100103141e20a104004210a50106103055001300d00100366286110003c2e0003080103401d000d402c0940b0b50001d940b202c4040212003a1244d0410300c0e001001c034542810b1030850b80305815152145204601c084120032250341c3e03103110f8001c82ca03c280c1090b481606000c1c0148010891800b9121840741001680c0d95603414008407204a84000c0040c50015190070781c0440c1c5459007210001036841107400c0c268050020160020681451f089900096048000c000035006c00c05a1440c000e00b003000e828414105184540e2144002c00c41010440b8032031501301c2c8042400d600d10020851a82c41c40c00d8009980003130310f0080781900042464440c4650010900e40340c2c0d0a20301c0107000e2810203181c041c1e00c2d110301c55540d030b0421180903a440d8990724208218240070290310710070440c528084401c04034451090161074855103140444000b40c01c48400043e0041641188151410340740000940c0200b18086481c00142d20700000120 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 758857949 1250 758856699 758856701
    0x2010e1c0b010501180e01140109120c1d0f0604050a1d070303110d0c06020306012f060a0b0325030804030b091002160f2406180207030c03050a030f 65
    0x20661040450340c520b94186030024050001e6035415042c039200c0b45100700f2034944c0e101d00e418110b5411340b0a0b03600d00b900d1103004132082a040e81100118a0703441e000707030741044001a030b004100c540f286074041c9204181101c4400002045e22800d2240c180c10000c12031518190340303c1504207010590008400c09200d540c5005031450604e400d0762a041042d040003810f03044213145004084600142c903010804035406082c0ca000c41c4000b030000c079804000148964042d0005002c51003c185071841c02d50ba18920302c084503003a0801e99a8a4000d0f580811620781c2d09024021041000501414403581c0c41c01c0d160003a9040b500f182d2907260701007040000410100d10040c4055401a407240d40b480c588001002e00c2c18000c56081c440d440d2041200c03610b0300028001c03800c0f80c9a07000c0300c501101d000c2414000c82001c40012141075031034414650703d285e03195562028080b104080031049524a00041078000c074010a040600880c441111130301c006403007400280381840f5079040c00500128903400000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 758859199 1250 758857949 758857999
    0xc140c1302030f01090b060301030f1109010b190f051606060312090f05030312010b0c01090203031611041b0f1806030603051c022802090c1e031302010e 67
    0x4100341d90000912142a00e80d8410602404290805101d548290808030300e1503c014840504502031048110041000d074040841400c00010010310b41541c40f665450700c250322440a240311440714421000c4aa409541a120152071a4071078500b881d00d071035041c40703404640a500b21249595200d001c40081d40c010340f2400100c80b0f6645038840d850610054010704080342e08100c0c032992040c04510005d0520040890540c0c10300704090792078404175182207015000100000354503010103c4c40c82c6d2207904400750121003901443c840030400040c4c40c207110846041c100c100110810711600c0c50314150040c400e9a2404c00c2c20300d01003400d540c403080346004044881d0440350000791102010428408104102400101008071b4030401030034100010350355108c035543c0070b01c501c1c080000c400700e0801c14440407c4119009403100015103003440d4072101c143c0c0062051600e40a1500c02140b4501000064911a200001030074800394225001502c821001c0d4602c40d5000c7d03102655441c40c111104644 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 758860449 1250 758859199 758859229
    0xa0b01080a0f0e06180607020307171b15070e010302310e0a0c14120105010807050708030906090d0f05030402010804020a031407150f0c020f030f0706020303041209060c140c 76
    0x5070010405900c01d1798142040501150110340c0b080c806000030810b8022001030000135080200e42d900c0c0039006401c074504100f00701030080d00402000c0c1c05400030420006100701090341c0c4100c1020f0350307003005404a0195101c03801c4091030110034280031721408440c10502c0c1052181c0240e29603607540080340e84901c11518103201031345030b52b02c02c0165900103502402c2080c044c0e544a0034074841c000c0360f859141051240c1ca041151050105071864000c904a661003074000d287c2d280d80745007010741c00d40d41e10002c0c1c4e401100c138410410664906882404041488122550307124510f459580046035200c40c0600140e91101c0c06400c00400106408101c19107200081c1c040d1850529110a011011000300500010300a511850644a59100300c480341160342c102c031051a440e1881001c00d20303101c07500b042c41415125004000c00d07516000405984507a01c5004406540340c0904021503400411340b103940d0214101d200400c000400451303a102c261032010f0200c8503018004000520a89810b01c03a03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 758861699 1250 758860449 758860471
    0x7050c03070906050108541207061a10020d1d03071a13031407060507170a18060c02120a0209070c05012c060a0b01080a0f0e06 56
    0x121094202403060750000e01c041582080200c0c90100042c0030358000905240c0300049148070000000303c2841c0e0800301010312800e00c1052441000340809500c42d850844400300301005e84425250b400180030001040041012400c0050942e5050054414803a12203c488000d50415419488405c08522201880c1d801054501600038003d00503800744c080081040e2003419400c40941c400141840842e05240c130480c141ca1100041820b041c010158140041072a00c0b40020a0041c0d06002c000801c2802e010345400c5986ea400139111813140d00320051135915580114800c1c4e50700e4401074803e118490409401181111480004403400da070441d0000c10f2400c4907900543c10b01102d0401035401d400014141090303641c00207079244200410000c10081c130b500c0c2410403c102034126140021502c41490500011100e011210070320640d4031200511a2200040300c015860045202102040c1c40d0300301c80d9100c41d11804050000605404985a15140c030001408420440580309900d0100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 758862949 1250 758861699 758861713
    0xd140c0a080f0705190203120a0203040210031a0d0201110607092d150c0f030e0f01020a0308010308092e11120f0304060605040207050a060e070f0b0c120705 69
    0x544980c070054010719407656000d0420030129008021942111002060003d40f240d11202c128a076100c0c081140d41c2440000c2c061001c2c050381a00a140140d1086502d02c548401d181c0d02102181e20410901540540c520035001c91810008511001180185842d800b005202c6104900e0f210307080ea440000030790026070422600b000ca26a220081d070b0504011004a400d1154107451007640b07001d1241d541b0785981c2d101120034000d60750301014586c00401507016011038100a00a00c05201500d4001c2c2c0c0541040d4409620105207d625076034180c0f500d003280d90850300c1d2036140d9040051801d800605180c512482d05a001001140c40c99500c00340444030400303240c1c0103000c0d0090500a4596910001044d0030168503030742968507200b540014a52283c0d11030401401400700c541c80260440d01c000703480000d0050200b03500d40708502904080c098100480142d40e606c0341c4500c5041c0710303102c40d44d405100141a51004010f0070050204031070204444050f203014641c0a44002c41d1a90310030780c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 758864199 1250 758862949 758862967
    0xe07121112240d0b0f060d020d03020c0118030b0403081b04080c0a06021618020d18020411040f050904050a0203010e1006060806010507030c030c0b150906040207080f0d140c 76
    0x903209821582c0151400f40d1084a580d41c3c1d2507600102905820031401c541000540c6c0d44c0b110494800781b550000e0411a000c0c02d00d050294070381c442e44a506000a501c40006080e1030a45e005010850b07501002c1c1940d07590310350718119045000908409540d403860007001895100d41c40c080c001034039240300a000300070300d4a000c0101c02c040395484842550001c5800b4956901000a25400c548034600c2d95042c0c4c40d21040210000e00c00d03905d150107001d1500c4050704c094200044244140c1e84203490400503003146108000550040e440390000c01a0ba241c0d05200030304000681c55002481142142c1ca5141550f0010f03080d202c940400b201301d175101030410b11a4001a00604004105d94182694281001030000302184280c2c80c0c040c0074410782c500342004051081e1511404584c0140d07000b01181460ba00103041c0a5040c0c00740345c030910180c40403a505140c14821038009a42c841e40303903840c0c16000b400b140c3c03164008a40041003140da0301000c4182c40e036040700c0c5900c529142c40301169070704603071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 758865449 1250 758864199 758864251
    0x10e070c020d033b090403200c060a0518041401061206030602210705030403020d140d0608010605120304120314040b040605070201030606030e0c130f020705070f0e07121112 76
    0x2401d502e174800e00685041c000440d42080d104031071000c000c071012042011006240d45080700c0710740e8084c0c00600c0000c441c00200e40c0700000c0e051102c80b00390040350701c000d02810032040d1800b4843d0704040780b8080300100070762070040000c00c4000a030002c01150003a41e075261034040b60448418284060f4649403c045004280b81da01944034402e405c0035800c1d4106901c1c0203540e00c4103120300c102030203030702d041c86180ca21498040e2402e003d4080400d1000b0780d00c601e121b6000c0c0c1500c1c850390380039030080c2c032161004580c0842501c0540300b035030b4001c000c01a1161003c480140001441008102c010000407840b07030081e100030000b0341a580c9400399605403600c001422100903501c000f0805181c03403000000e07104042848009040c04031b51200c0c01d06c0450b2000030040150074100d07913150b4800100c0320200030005c2040070840b010382094a42842d070b21200103910351011142c0400003030a4540e4022a501f41d5030003000c824488440050404032400000e0a0352007064407680c6008440c001e44500c4201c003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 758866699 1250 758865449 758865557
    0x80c01030b0108010f03030c110402210c2701090b0309010926030601120b041e0c020706020a060c02010612061b0e06090904020d170c06010e070c020d03 67
    0xc03e01e44611558907020400640890300d020080c100051070061800380b240480c0c810314840d400070001c655460804036034420340211070140320400302d081800500310b14201c0094034925002031401d0481d40620105c1660905018120f80b414001c27001008603910076010069880703650300c0c5000181d2004503003446c0b503446025480051000140318100d40e8031003815030a503a0030070307001e003094030030141c0c40f0460741301610000d070b403a9410915010380269403280b03100041036182c564410812039410080f0040341c035030b440ca0251a000d64800c0d194180000d00030390001100003018400080c02a40381c04140075982c0322100140e40080d02d820043e5100e154090146a113900c4504041018034420808503419010300040309200316403000c0040c0940d21901a4400107035400025070030110b50114203d8843d800c2003c518035640f1138040046000704101e28101e005081e1070300c0f06000849a58204a0004904042101049030141140c00390313585045181c20030500440b00c1980d4404007040f0fa00c00e1541c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 758867949 1250 758866699 758866721
    0x304150f0e031605010503100510020a020f100207050904050f0706050a0f020a050d0c11060a08070807180515120702010204140607020901050409081b060a05010e040302060708150a080c0103 83
    0x43c69001044070390100c2c494040350820300380247c80c0e03641e20382000e10f00703107056101503000084040c00d0350100f41c1c04100d901c40503100319040c0008002010034400a0322295240b9000350303101200502851505211096101d40b080341126a80a150046203003044242c2c1d00000201d0008103081010700d0308180c1c219480c40b4640700a005009890300c500d40e0351044040769900380f00720a1140740a1052011134200f01c80c0016003410759440c40945c00406a040440300301c00010212008241881d2081e03da11000314000d040b040300403070804040019038041050401c00c2c0e02d1040041006440b4003100c0240700d1001500016221854545440c05448a4003001403042408000c1c040059039035101c0c060542d0b10580b40091aa4420b142001c40da108400e140c4a844035580301d01c013070100000903407520035070386940300384080e0b40d0b200310740c1080000c02e0b10b00501580140700080c03040d40c49545c0040d84045042c142d01d10250b40d00001c241d60146a4000b5422174001d20f00d124015600b500541880c12 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 758869199 1250 758867949 758867953
    0x816020604170a0908060f06150301080a081b190308090c01050f0903070b0d1b0809033a0504061109010909111b03070501050a150905090304150f0e03 66
    0x2152a81d120303005603080c60a00c1d003120b000402c3c01c6084500c03410b221009002c9030800c0f2582c90509000220f8460310440f0030620441004200b8000ca605403010380741202d40400c01400503420a0f40c40b401c00c4e41001d00010840c1550525803400f641c4108854420382503102c09a40f9581c1490400074503240f0000c00b550203c1e402010030f0826640d110f000c5900041e04100190b4503103503c400000e003003030400d9004020862001c40e0300d280d06c1032154880040c0012103458901003140c10801507a50704400c813842c003416001400b030848500c08080c440200403031600e00440008003144004008038840c1910003506644e1201080100302c880e1080d542c403084810000741c01c2814201c0000c100b810140034480125032208800250a003184003696001c4c158110346980c03d0030018001d561381d402c101801c0d6140d6007010045070402d0740c40d00c100e80851410445076100e1a04280e4803201500010302400e280d84020800082c103401c1c1e005000480404a5032011405900b030f80c4002e00a41404114920039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 758870449 1250 758869199 758869201
    0x20304060c020906030a1b230604120f061b08010e010e1f080615040f0b0a050409021324150203030a181a090d03050912030c070f0308160206 62
    0x6640040450030701c07a0b41165081d03100d65410012a0818031010001840a400c101060480c0542015003030f0036601110300e04241c110007000b40c00c807130b201250744454203c0c000f00004d10924803100c01e02a085400380070028054415030b03540004031490813514016075a51030715480341c500e5000009030300501c1d11044100b80c07175061200112400c10090310505c0305416121a41c600d0880c1502003000404d9044191420380c60b009150b5803400380e000c0f000500c101d290201208588410f8810b081002d0009801030b61200d05100c1444000d001010b02070340c1c000c101034680341d50b20304107014041e100d0340f6807001000e0030301416200304c4458070310740c000c1c50500303da800607020b02c203a001043d82e074800c1c1d99240c04181c05240000b10800300d826030f600501445080401d0305440103d000c0114042c05148027150300302e0111103800c400b120000c1d0b031583c682d50020030300c01540142c090082c1d84c100c0000c0d5146803074425aa96203400304030310f13120124082107505080092100242c0990898a1800d002a0000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 758871699 1250 758870449 758870459
    0x1e030901140405070f23010323070903020a090e0d1d040f02130b0a0c0303151e150c08070b0402190e0f060405190903120606030204080c060a0212030a0b0a0b07060507020304 76
    0x141d1b80304210581050342d110740d170f60340e00049084141040000c4040c4244a4140700c1002020320b405030009070702803003c3c00c400040003031061007020301f0494143c01070311000721041001c45104a8000c480c00e842e0784851207803807090340d45100311b00866170440e100503501c0c1000c0550800c00905036205c010002c10500c0050005a040000c40c44410742c145030000d18100c0b1801140520301843d000248001c0303007210308284c000c3e0f52100407015107100c01c2801c49502d24814045404a00c4a078008150101c00c0c40513800180c2c110300c240390064802003c900406048a104c0741c400c0c4060380c0040c40d001034150078415881030b8040465081170054a041c0b0051902c1d516600c602d614948204c251540c4e00c0007118189480703203203031009800303844c2001d00a042c3e49040c0140650010b00442d10107000304005004580742103812078590311000d8000d8015003080d112540e50a4100903d40300b07100e615072219205c0366a4080c0d21201900f0706001054440095040420480f103005001ca8155403040005103c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 758872949 1250 758871699 758871749
    0x15111209100c0f030b03120301180b15040b070804090e0d0306150e061602030610060206150d08030a0e070e070e042a020307020a090b0112021e030901140405070f 71
    0xc001000c0c1800700d80d000004021030307c2e1141000d05c503c1c410101100115042c0c4940345100b0035019100018000035103907000f00010fa0503454a0704240a1040004220000e1584041d041d5217019409a504041e582d07080704040e10304000c0300c107503540c00017144520000d4051007160040d1030b444070345007403105400d140900110003807010b240c81440007203124101d00c001100e22038140d076400b0f03007a5000ca0074011611007010106004a0000d40103000000d140c440b071500c10112007400c0280000c039404500d403103410a0b548041d029000c0551100181d074028681080b00ca80281214200191300e860310501c01410a41a201c01520440c10501c440002e00c94400d0100600c03008019100050900c090099143d8400c0b04c01c000c1d0041c1180d0b40014031006140c2c0038542451f800c1e25020712400748420f14070708030b224140391b4031508100c0031640c0041e0701003270001d1544504504d000141503120070340290011001140d04982540c003108007448501001c1410304020308424030858224032070502448 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 758874199 1250 758872949 758872967
    0x40c052812110307110102070c03080309010b12030712020f1203040c15020a0212071a0a482003071205060a05040f02060a0201020d0c0503090a15111209100c 69
    0x30702048405c0c00414441e542c00c0d81244c03c81ea600c0020141c0c41944c0c0d00e80701c1880e0700200d4480c42070303518142c08031381542010001c2000c60440c58021750300d005081d65078138840100b101c600e4021442201c040700c0e10400100a488801000d1100c03035600c80c545480c01c0c840001c1aa001040820315408040f0f10042d000149002410782c112100c03450703142c1c04200c16103401c03c254090003003001c500d443c56664114000080c2404505581c27458496801c4130181500c80000c0d800096200e4102c020f040f140402a071100d40d0000030340d0a00c2040b00d82c4c90b490703460301d08600b0018150440080d4005255601e801c00100c8010301c090f0400302e46003000d51711269101e420041a0031000c80d02d6a00040411035481002d6444640c020210380d1140d880b560028000c0d01721207511000700d46020071048925024906803131103031035040010091100c45907190001d81d1a038110f500718032a25036008022a080302c0016000340c0b444104244a24584100103030300e000e036103441c2401f045142c144ca080d0003d0f480710003d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 758875449 1250 758874199 758874211
    0x516020d1112040323030403080409050912070605060f0a0f0612060305030c031206041e02070201030b09010839121501140f100e040c0528121103 64
    0x25003048514900507070410404460b000c4032220005030101c00c01c0b01d28000d640519031074035091440c142c2070b004455038903c52070001804d2080b00380010410400030ba002640c1c0240c54000351107000860185a00c0c440e000905c0c02c07143d15485204100040c2440c80c00c0b00c0512104844482096103000b40f0300d84108550f01910302004181c10701080c07142602d8000c0002154860116980c070540b45190b02c1d125042844040c004401290100309140340c1401103d00c2020b85514a035184107800ca1800025030040008078107160700c91480904503915101c440d4000e05002c1f001e444c4980b0038052007058010100300b00c00d000b40f0081030003901c42c81c01406480d01408261030030840b03a03030301c00c0710725150001c411420b1035445450f0700040703580340840c0350501d800305055813134801092180c010842c400d0b9040003c0c0000070503a10a100e44c61074150054800c4c000c01e41080f91a000c2500600242280818040351a9a400d401441c425581c0014060360b4020540070801483c11403064090b0f4920000e815 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 758876699 1250 758875449 758875457
    0xb0c090405370b060310060210050c12061305040c0801060602160e0402011b06150803070201140f130b030f09071a030402040204150c0318060509062208100516020d 72
    0x503146501081d82c4140368152004200e1350300c0b03190404070003034a108a805840010b003c5e4040c6c926101c4054005e40d405511000ca1a42c1024980c00208180340c0c1d00400969012a0403500900c41d124144192800785008071251250107041c103009600391029540024215800588113502c807040c0c81d18041d080d01c1005c4500300880e20f90f800100c81ca2864025000c1e840d035000e49480307080111070303845441c000d1004424104034a0f81e400c00e0035244c3c012400b000e40400c001c04a0002c1e031150707500c0240601c0900c4106e030303810101102c0014404001a4011041092000041c412503600004003203501076050340042c0203803030034120480503000c0b14496401d601e84000c0045811551a80c041d0b501411003207100000301c000c075400080454020001c141c001c0348512840f282d28116507004035058850a8072600c0c03501901400348001940f04100706245280039800c00c03030a101160100f14000c04000c0b0003800035041d44500c07001140c1c4054002088400800303498002c840e00800d00606105090078 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 758877949 1250 758876699 758876791
    0xe1009030b0c0f0f0702031203010e07030519090327031703040303181110021626010e0312010803090f100c0512070b010b0309061807030b0c090405 65
    0x1d0b40d12154000d006590051200116a07a4807000001c00980a13a83c000c401b200c2419090602c131944a21007800b17040742040c144000141c2c4075009401c05078010394903000d00e28000f0048900c450880710b445004400040528000ca1012210f5a00a161294000d81c9525110345503540344032000040419012034410007000140030716000750700c80d00e10f0000d91a06402c032043709280403140381000f24601da06c28109003148002491002800540034582520b00070f01003403c02c003c0000840849d0500310000d40c2085502001d08000c1c060305403404080e500464882c400c0704405e0017206c2e4140c2004c55241d00500c541d243c1d0741e44100f0b0b034810366001a030390540c0e500c000b050102e842d000120780c041d01501c90064800348800c0201c00400c0c01500031414402d059803281c24100082c801a280304007207511601c049214581e13001160700100080e001220f0314240d403035a0341451100212000e94a024010584006500b414003c80d50b00030fa0420b45200303115031000040c0e80c00081c0c00702d20038411000f16 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 758879199 1250 758877949 758877961
    0x2150c03072f27010f0303020d030e061506091e011e050f0a0507142409070b0903030d05010603060f06031e0e0703050109060b01031506050403020d0c170d0e1009030b 73
    0x240c1101442c0c04410000f420540c0c44601000518001d0b20007140144034682d405005948288925030600d4a04009000301c0e440321110101c041d10120303680740e44001c040254038125900c4603130092504070b414010519411020f00003400c005200b070f21a090f6a801c200c102900030b0b038003404a40300307803000031515601ea07a2030bc041100d40780502d2074024850b02c69241c24040803c1c002803c0b0440b0300030038a1241c0401c16001184043c1401030710742c0c09541c0e00c51442800781c56213a10103003000c20805400c89080200c0b00c0c0d52402030b00c03001c0c1d0240010a41e5090148101c6083c08244000740956080502140000712040c10040d80740340b003084049a0366101840301301109011700c40083d030300100203020107041410000c0042000040040c0480e1403c200e814811340c036410302d942280c03860344416003400e00d10380174000c1c41d000341501100c81203400c84d00810550501c601e00c0c9000c0010b900101404030300f52a01420b0290b130207158911400182c02c1c4c8000143d40904030308240c07580001c80300d10540781c803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 758880449 1250 758879199 758879239
    0x60c030204091505100e0303072003190201080a111902030c01090602030604060e1e07030204050a06021606020f10091a0414060f06010807030902150c03072f 69
    0x154000c03560399403c01401c10303004004101c141082c0c030412114150060313582c4500396140400c120200e40c16400501c0010040368035000c100b40707585d0505520301810640c9400290900d41a255141540c2d014030460005650344a0282c07580700e2a003060410580240da01c400455000c1d4900d41c14011101c1100d8051240c03080c03082d10303a5100840000d014200b01c500e4880040c1d001150820f004a1034840002502d0603500c0c1c0981c0200303075040d9245030f00441031440c402030300c0c4014840b10900d034080000089944403055820018402d07503000d0f20b2460320050f983d0f04542010307804041150b010484010414001150ba14070440150000140241261404600640c9000e420244051958040005200454040e002d038904e5210698026070358220200fa02c0c1c81007916203a001581c04800076140c2d60195008403411400200070384107000000901d4011940141c04540480d0004035912042040968094500074103450340c01c0c0e034240110000582e00d5451500341880340b0348148846c0c10041c95 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 758881699 1250 758880449 758880457
    0x1810030b07032a0804120c0b010f140307050f10090b0a200601030b040f02030102070b012304061206020f0c0d020d110307030905240d06081207050703060c0302 70
    0x4031190010103803a000201034001c0c509400803c16080d000160f00c0001000108101408403050315002095220b948520f4020140160b0326414009000b40d403074007040304620020f000b0f040000c1101019410804d0480d08980c588442e203000c0d80c040c03071091159569500036102d4196042c2c4040006e21a0f1290444084d0103907805040112400154964125409a80600c005c4040403060111301c551624665462134240700182c10416000f000c1000100040c8002c0c420700e000800140c10035040b03445014030040c0a03801802c3c01035611b50f2031200d0022140744180380075000c48082242614244582c010906102700040c445c0d940010300200050401003503c0130100250201c0b10f401c2403905c0080e503a640161004008190081e1041c0d40d060400001c9901c01c507410b85c4c0d0080b9103890319090040080240e956a96107407010044041040d281314050051000294404989103240c40c1000703062141400440d803941e60304000d40e00220300002005011a5400034000900a004070000c07030023401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 758882949 1250 758881699 758881703
    0x151908060f04020c010501061b05030a140712020705090c210903130315060b0405011d060408030a0305012102010813020411030406050a0501061d040930030f0506181003 74
    0xc0301044d402540768055000d40d058502c9a103d4002c0780e022038040c420700a00b9448020003d5008020a00340783e807143c0b0f80c20380300b103800644541c01c2000d150b40d00048941c0d520070720070059101c1c110400041c60403c0029801c0030041d0451441c2520032403808041c80491450319140c40d20800120f882800300f0012949451051042030110070f4036450800580400245000f17155820a00c010501c80e03000c1c0111403c0300c2e8140c450046e00b007641c14043c1038002000141c40e501410900000a607200140b0040c0408402503a000840d0760608000e150000504042c060740c6152a0043c03900507600015500d410015070003000302004558400203010300300c1000343c094072420100a1004118240d002039014896401062200781e884070011910152003121000c1b6000d007880c500f080c5070400764020040c2d2400784500c002e82c1500c183c03088814503205104100320559012501c0c0f0f0302541403044c806c0b0121040c00030301c11801d200000408005a54410b0b0035002880002b00e101d10f105101d81400540e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 758884199 1250 758882949 758882951
    0x30409150302032b39170a02070b0405010c080f0405101e0e010f0c050c04020a0905090c0f07020f1f020102090a4e0b0105151908060f04 60
    0x7054101c054507040b90399062420101300015564690500480c201c3c0070340d080c5508140a0840c1155000c1170109141ca42e14a00070141000880814550a400c0701c0c0c0401c6812565a14401c81c0e400038580740140d44a0160010240020f0055a80c003400b407140e255007001d012904c80406001498040c0f00b59440198020011000c1d070042a0f084154000d4020554444402c1b0440140d4180d410389146070341c0d2400280718014804000f80160140c00d4a1801001295003180c0c40e280400c0480e480341c21450041004018200507500c1c1040d20a40d00002c540a69801c1452074418103105001d0701c10002d100c0c8101001e40710907074407031401c1e80058005450210b9484009164086d00030351040c481c1d2030041105d0716002c50101c4140042c03d00c0268070803a00e20014001001107004207603036070b4203489038406480824094a00e000c840c0c00b9040d00503c0c0d08039855240404010032054440c80c071491600c02849211030181d01d002c0034103400700132070800e40c445a44480000e0b00140840d03520942c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 758885449 1250 758884199 758884213
    0x1a0105030c120f060406080f060105120f010608150c0a0c0224070b0907060e0117090f15010602010b040e1e010612060603020a0605070209041b15030e0607030e03040915030203 77
    0x8001c3c40d03c00074041c031402c3d00c0c10040c03280c8a030f0080380c954030410101c22403a80704100400213420329401d40c4101e92884010b403141c85200002440c2595180c0c0d11005555201344092150b424694001c56001011103103480e141c1200d21308050b005d0340c0c14281c060310441c807802c202540c00d0b4240e45c104c0d514283c220601d0781d490241d417038805920700040d1905d000314420203002141081c0180034a03400c513181619a9003403c0650400c0c5904140000c0c90414107001e00f18900b0482d150030001d07807000d9144503c029401d5814082c0007421135111a608034421402c0c1560300250600105103940d800610b00321510243e100450154090b00d4a5841700d8050b0703410000c40c03800d021441e4000c20580b0f1084940b072021580c3c8107011241c0b0700449002a60101303064000c10001074410311040c0003003034400209405075030364121041d0f8207801c60b0b0740303000402d0715103043c041d02403c01d0080030b0780100d26013030403c2038850390368015540f8000e43c05425003030380c0d4a09001280d081c1e070544210042d540241143c0d94 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 758886699 1250 758885449 758885461
    0x112030c0312050c030403020705041512020d0c080a060c0212220810090311070302150d0906050a020c21042d0602010b0a1a09061606150f0501031a0105030c12 70
    0x2d41e0b0305c01c4400f46c0040c003d5000103d02858035020745548641e1240c80850310328200030181004034071021080340c2c89408144080c000031010ba242c04000c1481c1406410015034901744402502d80f60329111003150004185400504404d900b654458080220494502a0f40d03080542d0072907442d40007180103205218408820020980048020621a9852500c8040319544456498415020003988541f09101044080d500040600341c20b60340d600d80802c02001a40f543c00c00c680c1c0642d40a48407075000139144030000303401c0000011415031403c007005804d4210320300300c43c076004d24082d2449109041342c000011000032954090a8013001c0f19040308075543d050041e008203060101c06004d604410800102c4520407020305039168114031655142448100810005502034000c10b502e01c03c202803c00086440c2e807040c1c4810300814a1700e014480c1c1890a110100e2265910003810035040507160110008080340c1c80911410a0030000d84980f03451000b440903025006028003031960300420420 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 758887949 1250 758886699 758886721
    0x30a030c1718070602060f040212240f0601050705150a0618060807050307120b0406091e060e0109230705090f160e0d150f1805150112030c031205 64
    0x125110040b0345086903113007020f913101d1004681150004415100140150502503110034041c0d00c5401990032080c0300140c00d0726202d030380300c40410300c5c2c000304004c02003500100c4604070b422480900700581403441d40d9580716920a4030548141340703d03054101140d0884842e40000703000d028181660301070300c1c1c0d0101c900700040041c1d10414001c0d210384080080c040c28041070740d009551400000900c0c051040e100c0000341035014004031151603440740e00c00d0201e958407503240b04405e903013508245400f42c0703820f0481c00e44292242941040e4500701c4050001200910245a268078506000603102101c0d071a150408110b54003040d0001400c40401070034102d80c11015209010a035468058216014011200c0e05070310201c0a801101401c0a030300400c0c81c1001c0d058482c0c075018804078540740300d246e00c1401c0d620360b48a018480c140000c20740b0104182030207503c14205050701d038007060350f16090b0109260410464040c0521036a03002c01d01c2418450b40c075000f0141031002c42030201e82412040b0030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 758889199 1250 758887949 758887981
    0x1e031002090301050f040302151b0d1d0105010506180d170a18030b0411041d0109030e0d080405010c0f050318030f01090b0a110c0a06140c0c030a030c17 67
    0x984203529120015000519005c600c0c6d0103141c15130f008003680ca000c1c91450540e007030302a02c13203100501c000c03903003c142d054004001e000e50403600b1350100d101040b4151510000c0c1112040e219079074141001030102c1c0c3c440178155408800c0c181340c07840c101c05041740458450f844c00180030b000780515440e003015002d0036100130705203503c1c10b560354541c1c40019050180110000c2c00010041c4074840d000c01c000c07486940741c00c1b54210380208000380b0001d214000f25129034010741c10061a0751525882030505800c010700c1c0d0803041c0151140c03144a10950b03586841071103107002e080d060003041d10070042800b813540c078148134180c1d000e0122039a03071400d03140344a41d811101c908c081c464401c802c1032212140303060058400c81c0c1d0340103e2440c0103444051080019228058015a92a10602404559060411a407219140210000101441100700309940d201c4002c00d0450010000c218102544000100300c0d580b012031868005004c9281c5001103400140c81a05d01001c00d8518080c400b44a2a0341420 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 758890449 1250 758889199 758889217
    0x70504031202070501021e0c09240405041a0702071a0403060606020a03020a0201030e19080415020706450e07090501020a02091e070203090319050a021e031002 70
    0x206005000300d8404907600e01031405110300580000c4c1c2c0d941201115009040c00c1481100195600d10228001140120500b01d80890501c2003440d1a00f0f80c6480703240f00c541c1503803000ea030b0602640c546900d600d015090754071001100014008002b4063f00c0c82440300e02c002d4150108150441030f12122402c0c06a04227002c182c0e042842c040c0001131765400010020f1046074103401601d02551140c00650041c001755090910034010001488015040c004940745214800d50407203489500b070004620391071184544400965001da84103020b034541098070149940e4051001070ba01951000f0341c100341e0030400b560342100c1c1c1036200301c0070445003e0752624810344509c04032241c403980d07400d00210340c6200103100d42c5001d600f181c19044058141031803215032202030300b08128822034030349a034200f600c9002c8845400580012480d080d840c82d00f0710280c0440e4004101410b10214503450300c07030f200c5802d078a009101b4a6441c0d0b038080040f20042607003540e4803008090791255040e041154029600484c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 758891699 1250 758890449 758890463
    0x60c150a20030f13170d02180303030601120c0c0807060207021003061202060705010b090405150604060f0b130b0307020a03091d04031101025a09011707050403 70
    0xa0301c901c94405001c0c2d80c82180c0e0820120510f440d11010610004004607007a0381c1c08105841100400c1d10305030080c4041d20502d00010307511003150000a0310f171050361000070710940040081c4603441ea800024040c5540701050000b946501a29060f1703100d00310480002c001e8030020549000b40b14ac998094041e95000b507a00b0718814582040c100c0c11070f00180144428a0903001230b52000d400d0071005401b6040c800d0000050100c1100c1c00034090300b4007198111044da01072046a4080c1c0203041600380c0040c41079400380b0485081411221402042d802201c54401001c03421070010000f02102200410305a1811503803420540760013502d5070300402080e00403031380f19030740014440c071098000070200c40085940707641900d030356070111040782114011582c15134082c4901d02940c401070450302c810768151510b200c0d040d80c001c46100c1220110794503c0c003000c4810a0b40d83c0d01c5400402c1c9003010b5049040c03032241d903600c6400050780c03042d034101c01c00e50081180c003040110a41d040001801501c1c082c0792 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 758892949 1250 758891699 758891741
    0x18030f06050f060f060f07030c1703010f1203020307060b0118080601171501061803121205150d0b0c0c0303010e0114120d030221091c021b060c150a 65
    0x2080c0700b906001d444c4026000407042003e00300c0603400a0140400900c640340001c120002610345e111346c0d105010320301e04420304c0000104440b0b20b0800c44200145120a01721510000c580c601075204c5c020340c10054002916403a003002c6581c8610041d40c1c89112411125800d691074800445d900c210900803074010414080110b801da0380e000568071200e82845068400356130134094200c035203152002d20810212042c00011001415584d10691007010320740e102240c10a0003418a0186e4202400744516603441d0030000d02551aa1030402c6203a90f00102804201d84920707600c001c3d00d1144403e90744060101000110700c1001d84100e56040322107407803004000c02c55030001c0040010304840d0350401680800b041c20318041c003a070003900c00a4104620039801041401d00f00d2400002121201030681040790307140c8802080b02c020801e0003030703c3c3c0300a012101c1c48862500d10ba4914005a500c1a500800c41c4070310328000704103400808410410640c06408e0043c5410058100c1e110410080b07840f001b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 758894199 1250 758892949 758892961
    0x1050f01110a080c010617030a032714033c0a050a11010603021216091a0d1509030503010312020c090a0f062303071203020a020118030f06050f 63
    0x21881071000c1d1070303103006800d1007031490340d03100c1c095402201c0c901c05654903100b0001340c8800a00507040441e071800051942d5010a20005040300d01040001400c0e20840309030740740c68200040494182c0f903020141a0401050013500c0d07186000f2070400101c0001032258510040040040304044150f401042d42e0000d00c81016005071402401c410a000400500c601030071035101e000108006101c00c03000103802a00e9402248001981949000c03580d0b0100400c00281f12600103120010042c0c42e0b000c100c404540210214001c03458120580f00e90304103403d01d018408040121803142c1d00803002000008118034011308940c1091200303452003520841080342c96400483d4161380c1090041003402c0b02c1d6681e040b540c0040c0164900b40c3c80281d03507030001080031001601c81c018041d9429400c0c811400c54181018503100c80360300456110307203010044400082c0c000550620081d8242030090484040311140c0c11010455800608848000740c0c0144c144252544414003036441800b02c0c460a0352a4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 758895449 1250 758894199 758894207
    0x105030a0b040e152d04030c0501020315190609090f020408030d20030105030c01080721060510113304032d17150a1409092109120a030801050f01 64
    0x401c1401146003507000c00715417002070304e021154481c0c801c0c00c04c140c05203420748601e400c98104551080274000e1000c0c0c016190b24000181e14100c0000440d4008442c0c00c2c07020080c80c00d2070902c03601c04541e840e030000320b02c680ca85805407005049280b003107a4444a0300c2c0300020140080e01d2003604401000380c217a4a81030802811641038a4002e00180341c1007000d4401104c1d1050014070201c104503600d1032400700c052410030141070002c00d004001c145942401d0810106103184014501030143e5018424034002c40424400b00300001084200d102150100391030f1056517540c000340d590002040708000c02c044e08a07030007010070008031140e680c0e0b0fa20302c0300c1c04d00f07002408900307030f030000c00d42c218070b100002fa143d80d2005a0202d040444801c141d4072103c045224107040390040741d0f28440048004020b03050007001103030f201031100006d02c5060703258041d45001c84040c900302901d8040001303c40b030240c0c494a508010300c03040d07a4105c860720042802c004105004c28014140326900019107400c1643c41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 758896699 1250 758895449 758895481
    0x70302040906201912020d09030206040506090d1704030507080a09030b01120201050313020103180c05090901060e070e010201060f030b0604110301051c0215070308090f0604030504050105030a0b040e15 88
    0x800314070030550003018502030302c11700701e01549040340c1d0350200b141e200400002c2c05024403003403081d0000d005a04180c9080c2e03040180080c961f000c0c9520074202403042c180e0043e40e05c0040044501119640d8485080440d501c0c4a6914040c1c403082001076a03090b4944d00110402c21203000701c1c9a440540d880381c84201020b03c0b4484060300040d024004a440c66841120700e135901403050600040c10300f600001504100714044040d00c592601e81d0041080d0700b070007882c03241c0c400c03042002044858140411420300d203c0181c81c0ca001c218601c50030308903590003540800064120040c3c1e5417901175072460000100d56048031040d024034204110b0713010f420b4180042d203040e00c400034110f03d1106540c1112004104040300180c3c0d0110fa05440c08014044180007085107a010765504580c614041d400b05140013010988d12805034010001c0001090b404400d480c00d4031070900c2c10380c2c0c0c0d0745c42e50310800340541000180c40c0d80c090b00e401250f8460303160025a011041141403010b102a80d1141c25001807441 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 758897949 1250 758896699 758896717
    0x2006070312020306040603020307151701081c170c0c010b09160e13050117150f0105061b070f140a1d060d1502040905090c1305060307030204090620 65
    0x100007801ca45240496401542d80308070040e000042c941d5982d0002403400350b0320342c005982c03450b040d04049481a40410807140d1142c102c200101c06500d802d080555480e4013991800000e04101070800c0890300c03a6590550340802e01a0710449418402e504034a2584041d0460340990318010001d883c5060814040f44143d02d001c0ca40743c0c03004004041510040a0310440907800002c0c03005440410000d442614042c0038603040b0482d0701c11000c21207514251900d210004038504113000c2101c0640c0e000d40f80c605441c0c05856594503041c00c044c0348100144c40b05050200c0d801508408520107000150000c1210400c80c1e241c20700c00090310500c585000300e801007c6000307169a000f4081d013201704804540140e4050040919540252541022410702c0c0c202c41214030380005007042036034104d000d0241c020000401620154401e200010140a8207100c0c0310319442e2208006500c45e40c003803010000440d0054010320042e2018a0310400030000c03825031607400d000c08a90404103505100c10741703203180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 758899199 1250 758897949 758897957
    0x6010906020a0507090c140f0301060311070b04030e01050702032b09080a1b0b0d1a01030218330415020631020a090b0310232220060703 60
    0x1820400ba20f005800b0600d40b8006202450074641d1f0b180c1c1c502402445200c400a852945950404000400342c491001c00844501030074441740f000318418808540d00590706044c80320390010b298005803000e001b16400690300d4003480110400340d18003060012031103180240c5540440e80c0921050324040380b54050541540c0c011003507072000400128410152403a82d20b508801159540107805030342d030111051070303c511384034041200c1c458156801504610000d08081d82403502d803214010721011004c651a100d0a0800039404480c036403100b140344525003100100f402c2222102c030340c4003c4c3d401480f5404181151882843c501440490014020f044150780417640b80c060785c00c800038650080d1004d400502e403c408010040c1c0e98245064010705110b100401d007030034082c0800d4100980500700c500c0e510f041400580c1140001b0107034212040c0303816821041d9888400d20000a099085485519041068204424000302c0e985190f442d103503408002d184080c802003400f6580c055480e00034080303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 758900449 1250 758899199 758899213
    0xf08030304032012030c120117010e070e070806120f0a1b0b030609090718140610051b011d010b03070b0403020d0b180a15060b030408070f0215030a0506010906020a05 73
    0x401c0500c0042d500001e802001600700041002c0820f4031500a13440707901c01c45984a2000f07400707602800f4640310110148041c05078948dc0104888024000409100410446600165140d5151007044404c11892011a8010388003c5a031569650f510a002d03150140d001060070010040390b0f18881c02d464000701c51506644904041c40280c00b0301038800150340c010280042400400d000c0d40300015000c042d40400d03c440c010001cac810070200503001078000d41030013800c03402080d001000c441c0f951821500e40e05043c544111064010000740098041c001413070042002260015001400b050303000f1019115055561102503982e84554403009403c58140c0c1d1051000c03442846c50f0307a50100c101030050340c008008852050410a40c0703902203645451400044029154a03c51180540500b03200d03185103042640712024240a201700080000c0e24140c0d55408540f20358002c13050070080d1014842c0c0f00d040c100c4608001c0c060840b802d500065444d100090b510b880001d64100b469000f1010f0030384 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 758901699 1250 758900449 758900473
    0x40f050c0a0c020a03050a0f0326150406031e141902060706061706070207050105040311280b091804080a0c2103020d050109020a1202130f080303040320 67
    0x69082d104000f40ea10031464140000416820302165506030320441a1100f410724030326014001c4400b10210300950b000c0e50b00f43c0d2086c150030350825608641c0140e0218920003403440002e01805140c0c0004041c1141064440041034290002441442c030031080101c540540441040d910320a10088002c40141ca0000c04090b082c07050040181c5401000089201130711601008218028108100c0f00c5038000780400210305d03418003050700549002d18080307203400d184ad01c984c0d85c450b840d641c40500c10703440b4900801c80e8204451252220b068540b0b00d126405070303a2070041c0b000350091030900e401205098400344400c00f4040c40107100381e40c0542c0e03250400c500003c08584121000d682120200956405100306090b0242d555041d244075990250360b071504602120b05075101a840441c10a0040c801111001e4120610043d100d909a0005031a104500048103101c10700b54002414a0402c0101164000c4048000e5200c0d5000b40c4400300716000070f0800c44c081c04000c040400c8990440011000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 758902949 1250 758901699 758901707
    0x206030f130614061f050a030f0b041803030c080103031e020708010203090703300f140d0507030534020c04020c0a0309060801140d0609050a11040f050c0a 68
    0x50070480c28400800c0416441d5a003a04591040352007055103c010020410103103072060b90912007420040c0a085283c80c0104090f10b5801441c00c00c4007803503141c2d146003120001c1580300d5642030f02d000b40203001c4c0c070a8880d90b00c014010840c4090380000e040450b5140703128010600f9074102ca40c07503500d2421108060102144440ea6020310308114040d14100042c1c0010034005075000b00d0b25070003d03119031440c40c50007282460004d40d00d0302d07880229100c00100000082c040d9000e047c41814440f4540d00310100484103806400b440b500405000b01e141030b00032030913902c40c503c61440394a003008151954403a03150510340100304141d20104014854035580e20080442d0358007c0540126001010b45000080603a00400d800040070f51150400c00181580140b4500041215091400c6a035061503814901101000c48903070090801c0c0d03021008114042c2d1003c0e03c6140c018090380c0d00d8441518001d450400030055085c0304508006406000300b5840c842d80d809901c0400a41e031504aa4150a0b9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 758904199 1250 758902949 758902951
    0x1b0b0a05090d0203121b010b03030a050c071502031b1c110a080301030605090705010f2307060207110910081009030c050f031c0b0102060708100b0f07050c0103090206030f 75
    0xb40c0102d14a076031a00162010032120444008a081180d210010307090101c3d5005140d450f603444c0c50307040500c00d04158801008842c1455502c1c901103556070400709103a40307000718990000300300f100c0100655034120360100140c44520122501e2810581340c1c2c0c0d1809980b545607441000350000599800003040d07024840a402687c0781c0000e5610b90116519240b65540090703000392082d0740c540342004009007043c00b5040c040c05007401d110020582004005040d1084122420385800410540c1403203690707000c0c10750700f5540d44404259a5990f05281500c00c00c910f02d8000e5025554600200701030305140040d4030141c0e00042d00030990215651a1000034040a8905405003d4900b02e6000455014030002131020610300095564400d1490756645080c070003540340d20107610300350b0282080e84c0e0104a160304246285442e00f0207849440e40101030013000d6000782c42e501c2c80081c20b0140c02c0d142201800f0303040d014405940040541000640035640a11802581709504000042804141240c05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 758905449 1250 758904199 758904217
    0x3060603112a030a020a0605360106032f06191409030102040608090c060313060e1c020d140a08010b0a0311030411120c010f050702190f031b0b0a05 65
    0xc1c02c020030440030001c1c11548403022100040e0029101042441124000c0c2d54100d1038011803850507001e0140c960001001103007580441810762240ca007c1e0400940150b00559041240a500f030010404a11458581d00300ca04847d82c0c80d103001d0b00f03100e1802c102078514200c9800c035144035100354103a00311b4407040c4070101103402c07035003e009010345904c091000d8009801079880d420340e0790600034240c501c1d0030940e40c2c0c03e5218420400410940841400140b00c0d2a5846440810700d0503103111220b081c01d0891040c4401c0e45010800c40141c9540050301f04c04d840c080341c560b0304241d03241c000030700d01a00c81e01003c03001003100382004102e0ae01c4407030010441078446240000706911010803085250380700766400c0e0741819580904800d540b90003514090070448a2000f03004d1b034403040c400603010110745801c5005106000c0744000030342d2140440745070904141c01012071441d071254000e454000b05804192400f154001c91482075610f041c012800341d400030320210b810007924810032106c07903102240c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 758906699 1250 758905449 758905507
    0xf0d0e010e0d080705011509090c1203051e0d0b030a050705011808011a010e12060a020901030b03011b030e0a0507050f040f050907081b090112240c0306060311 70
    0x104001050003c0302400c81140314500204c0c0b02c151316407038080c05458680011203050300e051110000540f08280c800300f2102140001801d6404a0a06842a015003008404005d10070042c00301008102d900800440c601007104000e10001e01e002d00d50f0300d525a103401003003a070000406001c998080e070500000443c698011030450380d15040400e0a40d0860f203030440f208160443d241d0115030b004988141030030004d8074950070403a2200040c1d541c4100c040c2c9504000c6a001550010592103a0000051188050028000c044100080075001c070038403090700000900d4904a094031403008610840c0a0350400010f110890410040114010600400c0c44d84907549006212016415000c0d00c1d03c80c07070b11500581490303403825260324102110490f140d607404030700e151105203541d05d110b40207040d5819600d010800600038900174000d810016006901007a046c50032118001482e0441e02c000b424503035092022561380c0005805894559211048c840c4043c030012507000e484042111a030204880303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 758907949 1250 758906699 758906719
    0x90d080405100e09060607150b030c0a0605250b0118021632032d13061b0c030803070c0b150423011503060302090f0105030f0d0e010e 59
    0x40042d410035a4034600030042550481400311928003040320750340c88081507401078a0500030343d44070030300c0d01840380b9003e03e9191b03140e045401a0310100400003181070050070451b4060b4071540082c2c45500070058428100c25114288056911180600d0f6011503018912201c00c1c0d09001804040940d000e010160090b82800000d005003101080309400d6070054918003070440440440c0c440e0310310aa0ba2228000d040d4842c100c0e0304460010803120750300755400d0500c011200200210244c15052001d8600c059030100d14035402e40382c15080c40b0100c8049444203829046401508042070000c240007608290310b142e020000710300039000443e44940c1514203e5580191507548010802c7d081d2450a10000d071004c08001e40d05052281034401060140440034070322103100700d010509414060b0700504003140c4071890b01c1c240070303402820242d07500405085903880d02d0020050038950901c641c510a210b400b0148440e0392001c1202d074802d41d402d0307032007000c82c0d00c500d001503561184807020340e034004603001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 758909199 1250 758907949 758907959
    0x4060512070e0613080c010305040506180c0306070e13110f03040f0b09010e100209030705150c0d0315060302090114090a080303130b1f060f03020c01050405010c11030906090d0804 79
    0xc0e0040c1040c150030300c004c415460500b09158a01880c00003c0d90504d460b18082c0408107000050759940084016611407454401200c014140301c04003500a030148501e4081c451059000510001032007000d445958043c3c0840c444282a901201c09030032407600d0400241481c0003000e13000307551150141d415805130f4101c40c0e03501c070304042c81216800402d07595175024003c155414021041340c0442200e09509000d84000002d40712151403180c6446000701800e0380ea00401301c0c0044c0d07080300340084180d0b03a500030000c0c0c1c0540a04146650b03200044030605000c03a01a019200b078454407081a5102012080c12003916034290780b225100c1640300d08100b80019252000300020b42c402c1c0c28614801007000c56900d48072418080c09017481c0420340030b5008449507420001c130303800121101c524007602048100c0000f90002d120382c50300d914055080100300001d1101c1504140121205503480c02c540c0706c0c5022009480f070041c0c5a689500c0a410843c808452a1074005815030a0007081d0b002d04e015610 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 758910449 1250 758909199 758909209
    0x1c09060e011e080f0703060305030f03280c0e09040308060f060903030406030f060803030103080f070809040c050a0906030c0c02010302072a09110403120c05070e101a04060512070e 79
    0xa10a02d03000180c880b0f04101000c5440140c1a410404a00b018400a0308550760720f910390241003c1203401040100003d1140da192081c3c006070041a982000080c0144003850170141000505480105040d0500302c419801c0018045106503050790300c80141b41c41e120104980ca401c000c40c2e207a8054028025003003540e40030700040000f4101c544002500b140f403c01c030030b0103550150b0701201c19900240010004140102c0031202c240458006c42980d582461500902500404035251303003161030402302d016541c1e00b0400601c00d2406a0b01c1310115940c0c0c0700012410b81c1c10004d0901d001034a0301d80c050b00154001d4000c0c0442c1c3e449807020807a0f49540c00c81e444600f02200b59036800c1108424800c119400141c850740c114011001c00c03180c83c02e030650701d40f03040d00c50342440701c413041040d070003207070011b204050040368003404a00c0894080c07402e040c484030300120410b010b083e004110140e000c40b01c00100c039049408440c00ca0320740d80c0c10300c281602d2515140c68010007070810301c070400252002d65a11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 758911699 1250 758910449 758910497
    0x100e1f0602010b01020c0a1a031909060903020f07080c0f01052217030301030f03080916140f04060317030711010509011b02010b01080a0b0109030f050c031c09060e01 73
    0x1075400014a282c25500081c80c0260130303583d0500030300d600501400130030204c05040c0382c0b40c0100c0c403000d076580c2c07075600c02c0411000c6d030021044082c510302514101000342c550004400c00303000340c6c222858444031200703590305d8240d80c1c410711840da4040420703a4118200b0040c031115480701410090304202e86504072040442441d900c007c0c003440302000c1170000704196490f002c58503100800450941d0306560305d0784608803003a400907007400702170000107801b040304003c0006d0f1b4148c3c01d0b02948686a8894a2003000c62820311703e0b5100c4c1c0480c0c0b0102c0294201403148104991304100c0140d0ac200d03584803014060b50001d0700c0e10302040180c0c001e04215020074000c95000c0c0c48031038000515401078612401d00580442191000c69060108540e1260386c880c00c1580c001d8184040051621079010046e41c6440e41c81e4070007000280742001c0c580c1405000302c0c5241c41c868041d000d17148400d8010401003008080074403e036004c01c004140030b101d4140f085a9003c018076042c10101d1540d6000031007070380c0c4055 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 758912949 1250 758911699 758911709
    0xf0f15060f0d1410060e041e0b01060c3306080a050304090e07080a050c01120b0105180402041d010302030d05090312031e04060c020c030d0f050711210f06100e1f 71
    0x40c1d200d0500041140c2d48c06685604401c0d000c8000040308140e48202d02c1c0d480601c111800c010800081000744040b5a85501021100c0100c4114036507140c90761250862481e038400a0350341c60280c00040d9464045130321a90580e0141c061840c0909248010008114043d00120140700d070000128803800c040041c080b1860049000f00801040a4001822f45104080e4041403a04080702c100c4d480c7d0b0000252801000f8084d42c40c0c40716402403010034024007560340400c40c103003100300800488100110038141a280280c003668001e05051509951034428020600c2e01540010200203c0d00c1440c4085c43c0c0045000d1030400d00703000001100041818281c90a80c0c00a942e0b00650040c203030100101b09541c0015405001a481e2060707001d0000707040f035080c0300148100021558100a502e0600c0b00c1504030007000005550880c0c04c078951164020000d03861103100f2003011380b10808000584038071504803100c01c400d20500340305848131141800380150342001c0d0038003110307030705812003101105c0508 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 758914199 1250 758912949 758912969
    0xe0601080d09060f0c050a231204120f0c0f0323061504021b01020307030207151a04020d021e03070f091805090f0f15060f0d141006 58
    0x25040c24005414141003010075000d00400090420005401c40d41d41e4442c000c603030810b48045203542c01c00f2402c0c1103002800038803070790104c07a40d42c80003140e85582c0c220380114542124044010300c19440710b98404ea008100340d4030700d5406070390005081b6440b5045030134480c03c041d00d4035980d034000750002e44000360401c9415088074400040000c0090303035a0902206880000c01703940c100360368060580100306801d5400380b07800061004100c860047c0c605c0d000d2000c2c200840da240b42c0620010000e41004404641000080310014410082d81c0190301a00c1e0520314141b40c14000d113002c0100070343c880f4840d804002d0b001d002091100c41121130901000d80c034038013081da407032070070b40c2c1d0003000030034005010070a00005c400240300c84076543c1450301c00540b8143c00040c02c1e843c0e0001030340c9045e040f14000411842034000800000f00041342100344201d14120030041d9480780010816400000c04030381e03812034401c11016001c07804d43c0f4040210784000030140c5a18403c50002c410548000b904030017002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 758915449 1250 758914199 758914201
    0x80c041e0207120e2233030b0f31050d030e060a02070f0221191a01030201050922020d05040c060f080f06060d020c060603060a0e030d1a040e06 63
    0xb0f00c4d081107240b03004100450301e04030150403c40e280c041c102d21100d21161402d9644007540c00003c204400e100f44850982c002a4005001ea03c10a00d00840d90004403000c00840c004190015050348115001f140800154030000500700c2d44089900405c130859160380550003000700c040b030800c1c800700602c600d40390b401280654400b11400d250100c0a40180c0d01144100240340110328820075915074240d04440d1489244c20140c0740e00d102149004030384c0d226000c1c7d9101d140c61102c0481a456520340701d140d10103a013040305000328142070000d22029000c204200700410140c6440807802081c0001d5908031040d5118040f9450102d801050380000c41650302c1c024001440303039500c002e000400d524a815800200c3c9240010300e900406842d020f031000c01c0c5030108580d503549109881034600c0014045450f0340020302c2090780d441c4243d400d10701900851020804a220a0140e0194060b40308000c52a000003000213a00500420b0b008070241b5000500b500398a5403a40128582c0140e060020091 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 758916699 1250 758915449 758915483
    0x150103020309060f040c321903081b01020a05030906010603090c0e070908190605150a030206030405030f0712180f0b13030f03030b13091113020c1e16080c041e0207 72
    0xa4407103d019902c05c2aa018a600e080a0140ca044096030b0740012001d84591103540c40c200d00744be0907644008654000300e4034289150303000001e984110184d80c100c6909999441054040340c00150001e00660705078041401184d0180d001030f0341204440c40c010708442e40da800128244030701c1380b03081c01003035800382c000f0424012540529a0811040c1000128100c170700400601115001d00c0024000c003008800039003400303828010380e440349111100300744e03843c56246410610355480307201c10000700c2e0480340d40725006410001904183d802003848891241d0500401c9050341d0416180348681c02a000b5021000030340c0e44440741c990b80d12903207021815000480070000120940b460600e2070514299545011400d5241000c0d90400182d9607501810051440721010744185074011046204506c0c2c0d5651056460020f1400c1130440000d544002d10303101d0105521014911954442e98400c01514490345040c0d40800c40e00015004084908402e0b8030884040c3e8110702c03000d881d40349806000c403403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 758917949 1250 758916699 758916779
    0xb090706091d01090c020a0c2916021c02150c0d0f0207030201051e030f1801020903030301150c02030a080301060f0c1505040602130e150103020309060f040c 69
    0x8082d1103084041006056441010010050140314040025403511440c614040c004d01c6500d1a5076004604988115203032203082c00035040b9102d0202c2c0040e40541b40c03900c4099040c0542d60108410480400e204406030200710010284821350701000703410f041d00d04010380d41c403000c0701c00d00810011499290080d100d0014102110505501c0a001d10340c101c004c6030355804281641560f60900300036443e003240c52049904291000d2600c0441e050010500040301400c15940b4072400080003d4000d12002c02c0c402420b0b8003403410b40e507030560301c1800140b1980190b1400d0080f898101e15003103003614400c1d00020301c0c2444205094442020000040c01401c0d0300200c2441d500240741011103220744070f5a14480484140e14115000e0b0703075900c021030100000342d01101c21030200703002c1e00c8405544a05004481e064141c07188424030080300c55448195009000381d03841000c1c00e4001d09100d9540d01d081e04c1c2c203a44020700c00c5400303030100300b0041035201890410016040040f0078100b904050650521 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 758919199 1250 758917949 758917967
    0x15030f02090901050702030d020d0204050a0605090307050105090a2303030a080a060f0506220b0c0330011208160303090242040e0a27022b0b090706 65
    0x802d40d6410641000090354001048850201c86950f0041c1d0700c0c8480700a00000f40107a03040f1310b81c0701c6205000091410b51140182c500501c00310b05540609581e2001503401d072207900042900b001011804005040c500d50028000080c420744000c502e400c080d0001e030640e0301426484000c1140d600c2030020310740141c40f03084050000d0741550f07481c90382850009182030003194a0600042c0c21098011035000601c81000000c01c202445030351548414092075071281c00c6004508209801990900403100e074408220410054001f40800360740d0034205581c09041c0a040309846030300c41004212103080100b0400070229000703540004112407240f04000d1458424802e40410340a8a00743d20070b584010203c00c50306d418044035840030b110300d81c01c170803240340225030014125801d0340c0104400c0040c1908002c80040c000c0d150b40d4502019103243c0d24651407510b41c00780d0415150f403100441c05241c986207403100154911400740d100055550b400032900210368040309a08141c500304280d9810100305 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 758920449 1250 758919199 758919211
    0x8010207050a06021b070306021e07020a030609020303070c0e15010f08060910050d140105060618010e01030608010903020730110409050d09031101111e0115030f0209 73
    0x962810005459840d80e4211401e00908416400280e650143c0241c81c080000901e21800b030702c41040c0c1e00d05001000f0341002414010b207980b005403441001915004541d2025802040180741d0341c115141c40c1d0040450301c0c0f0407601440104a6a004a6020030070000201400c0050f5000c9240c03e000704c028941a510382e10b41031040382c1101c0c0200d1034018107201c0c1d02000565084907070380c2e0f0301d80b902103200d49554041ca4001c80028140024021035041d00c0501d80c10181c0203004586403202400814807a85110500c0341c5010310740e096440d071181044080d1040d05150100e052502c85061030b0845030310880c03c50250b801039000300210044502c0c80c50b00100f0307114202481071005201c039240d011450b94003c00700c081903403110041d41d446034064402d0079000b804803000c0d0041d500b00544050014002510403241c811011580d5600c1002c541480d0840ea10251842c07610004851915180102c440ca15954984441e90070154049609034019401070413048085029070041c01110b290140134 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 758921699 1250 758920449 758920451
    0xc08070501090e28091407120b01030b0603010f02040803120c030105030a110303071406010e0c07031b030c12030b040b040b060301120305070c0311180105010f030f0f23010801 77
    0x403c000806064038940d03801078280c2e08440f10341408820b08250040e0f4034410548061408022405104003d81c021155580c8002210300e9161210562141280714403801000306825400500005030310010040c0c2064024002080305601580c00500783d130440d0b0811003596201203540081900000011500000441b0301c03145503504000201c0d46550f5080c07000f0380980c4400d60200d03030780d440401c12100d034240c0180320503020400e04c2444c05e4031010300b07204141d80810f086002c44d604000d03100480341c0b0958940c84042c40080445650000e04400b404e00342e007480302c0d4200701004500010043c06d8490100d07a40010200151402c010440e0b880b400640d0041c1c0c03130b224010b08240c079000d0403030303040d210030030400050007045203030848040c451844000c0800828120020400141c0b440640d06804116508401e201218103803010780300c024442c040c009055010720b02c48507400799212030b04550030107902041c090300c8040d00d142074502094403002c40110744103000905c06ca054075410f003d4065140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 758922949 1250 758921699 758921717
    0x3150909060b0909100b030a0c171018240603030504171b0906120a03020105010905090c0d03140403051f0c1103121009181101141e090d0c08070501 65
    0x66220303903031100c2181d901d1901d40e80e0500d071700c0c266030100002c405031940030300100d103290f846600d500075100c0c0340c8000030134511a89a2f104d18071702507801080010311001840c2c13913940d000740d20340c2582c0c400003000c0380b0a4a2204602c45056042c180501c20246001c0d03152180d895103000b00c0e6a00284140303140350b60a03001080900e01041801030106003414040b12401c11986442c40020020061280c4180682c0703e010b004800f0036070190040384c100c2c0d031a080e00f003140e035595001c2c09459020310300c00c00e0740c48200492510000707800b5180360680d50046420320703800e06407603568061802d40b4bd403400c0c0000c40f690600541c141e081a002d90f00c0d42492615109003041c0640d40c1c00da90320b015401440442d40d44c07540003e56205130202c102c1b001809100310503c50014000400040c4800e201019121101d1000003905154002c0c0070107048002c0c10b002e05407800c20421034144031510b1120709000450010000309245944402c4054601d0780501090740c80302d460041c0301c42c900005640200d041c400c581c0c0f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 758924199 1250 758922949 758922961
    0x160201020717070e07051b39090a150806040b061005180301020702090a09030e040c050a0e18040507080d1d120c06040b070b15030a08070303150909060b09 68
    0x129503c001c85180d1340381c5031595182c00f801030342d20b4000c400319650407440c10704070752003480400101c2c002c100b1054a0349040e80082c040001c820001541030703a5100c410203811001c81800d180610603807040c4450b10000312216140340145481c011a80840204e610100c1070006125200c151643c000c0d008840d45440c403900c080014146005140d0072211000c5c018100f2141514207404562181e42c5c0140380644500d010b241120040205aa080d0001403d003050710b01241482e100756403070000603031911424013080030411207040c4c80740d52140b0380101c045400000c0ea0240600064000c038801d001400c02d050401c2d00340f5103086003c03003596040212410004420000e030810001c20408140c4120707540ca00f10030402450401c1d002a61508a0303400140011008032220251001c24840d5061407255140d030b03100001010b208180081e03158022840b585e0018041c0002011035034401c0c10046001c040110a0203802200c40e4000d4070003e40340d0703c3c290204580c5201e000401301c0112a110298240a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 758925449 1250 758924199 758924203
    0xc0915040b0f090105090c0708040f06180b18011b030207050112060e0103110607050d050921030313051f020a1b0f030f0e09090a0204230f0a020f160201020717 70
    0x6101e05c0d80681910004600c84c076003040100e070481504415000d41e40d59807810762007240d0b00c003407140b940018011884a0184215800c1e900c0466580c1c1c400c05081030b2940e50103070b6000e040d0a05880c1400900d0340c54118411844041c5180c1900036000303021070350703e4030001400c001110503401c0c846c1c5192680900a41d1034039080103066941101114411454000100304a8403030040043d01701c1c4104104100c119920000905000c071081d130743c0c4004604c006038101c51254000040c00002c0c0c20a20010b01603e814031100200a805102150303082e6080c00461940907081a0414183e11380018403c6003042d004a4400c0500760b038020049500741d140e071144500c141e0781420040030403606c001c0480c0c1c6280304214441306080014260740150410300200d540d90244240308034000e03410030a14852060459449a000514001410b0070326039604001d0300c051240142100c441d075a091000e580007800e044064030202207008102d0a5000c00c50001a01d84112607100d046110048001d83d5051200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 758926699 1250 758925449 758925451
    0x20622030c02010c02180610052805040506040b0414060906190210061d0717070507020d060f0e06090c0d080310080a030903060609110405010507050c0915040b0f09 72
    0x141c9006040d0041034401200d500e42c4041020f0362021140c100341807408084489107005480440d5074a40c00301c00d42009481c0303400b903140c1c10380030310040c90701d135250f05039251700300c0417201c030003480d020349425140c0000038034541043d0441c0c0e41c3d1140229050180c50701050424440d0391085610718140301040c0d0000b20940308800c19500c03280381d003003420360000380200056409039010b18824803400351602c2c120f00179810341d8001560f5000e0940e020511050091000d01d070303141e104110760002c543d240641074030180e1140100b26045440308810384042109440b4180081d03882601c041400d000110b00e90b85400300241070011640c0000d0b640401c40e9807940a034500003a844014591680c1d51012004034441840d400b40320359001d030780441010150711800700c1042d00d200c1c80c82044407945980c01b0304210b443c007a8210131110003c00007442598003820241c24018400c100300e41c008001e04c400300b03c03040d0f0107588003c01d000c202c80c0c1d04600ea03d06802502c440300d1040c0c401080c85c004220015030b4131a8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 758927949 1250 758926699 758926703
    0x8010902090604150e0909010207110a060e010503092803021e06070e0f0a0902070b0f01030f1709220c0309080d1503201008060a14011107090c020622 66
    0x7030310420103030703081c1c01010705d10315a20000302451440d19040b0300d218043d40c4a03e00488400042594400d81490510583e409035883e640d6034a4000070280011348181d88064041c0415200e04d03029160403c5902e5010841c0c042e905020340002030b00ea24000e4a08045980c1d0030079035075020309482c2e02c44100010290b511100c80e00e015034000308a00e011401007005d000314190030086585021914038219002064110f21540800f60190345140046e10094400c0c080102240c20100f602000300c3e80701d0001c80c2241110481c107c0c541110720f00054008548139050130b041040360700503540036006a201d5622032400500741400440c586540300f181520802010040c07103075941050602800e0606100d0010799803151484503680300c05a500305031182800348aa00c105450111030100c28801c41340c103802408042c003840c1e40e5601702100b0380340c08581d8400141c108001e1a60b1503120701400c01c00d5000a0051480010345004a500b000b42008001401e101003c89000200b155a924410480c000304c0e0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 758929199 1250 758927949 758927969
    0x601110a1a070f1e0909060b0931020904182102070b0d181703090c0f0607030e010e06070b0406270f060b041103061f0e010e03160e0708010902090604 66
    0x49640c13050f50048425001492503600d03011011038800c0d525001403a100d071046654810841214606030060203003030080c13000011441690684003100341d0080d040c101d4009201003a143c0002c0c1c04240180d4200b5026503c540e00007400d50140c082200f450b40b65000548041d1421300c1c244402003132144220242c00e90291703942d2255a80d80c1580c542a881c00c140d010294848012009051090700c0d081911a01000d0182010440c0c00f49410844806e14840242400f810090207440a43e0700001c0c120300d050501c907203007143c0e1446942c1d80c0001c0030401c1c8180031203032290170907040c04021035071850390b80702440020003c0e481c0021917202c007d0014552240c19003c2545940c60680050900f90700c10070307086410018003000004e1407001440c45040140c030030340464206107241c1308400c01420180f00202d82d034040318050725442000bc00714240d2000d0111955070f0301d40d141c020b40c50225503102000e101021028022569030004103a40140b032503d00541c103064140001814034440c0d4440c1c10814 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 758930449 1250 758929199 758929247
    0x81b24090703080309070f0b1e2109100e0f0a080a0201140a0218090c09040e01061203111b090c03180d03050601020115030c0501080601110a1a070f 65
    0x199030204003203409503034414400c544900b00000342c40d40c1c850b558020320030240e8140c80c01244440543c8151141c1c80107000c401007001c11015403004d00c0b07900444c1f5040c0c0e413054002c030b40d1b18440c40341d40c01e01d0300903d5584001e000310255071015608851010340756403a0354006c2d0340036048502001408001c1c10b5000403013184d6a17618820113138010100040c43d9800042c0c05820058401c407203501501030f0600a4004082010115041001e400c10444070044c1c0a00c0038040341c19141095801180c611400000016a494940300c2580850b40f0074a0210700107100c61480410700102440b02d1400203990283e980b20701c803041000075040f4480185007190b0000040700203a492002c0046140301800716805032000f6206507030000300a0101110254050742c00c01224040351418003280c0821290420000b0030124103001c011504c5441c090a07280c1004141100f43d80a4101400000001c611485062000c40181200b41c03860480003850305003400f820030124890b0303507000b000703c4804c04803621908402e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 758931699 1250 758930449 758930461
    0x203010b0a05031f0803282c0301061e05010207031e060b0904051b030712020d060b0a14041409030a2d0207080f0a022812081b24 57
    0x4403900e5181036040319507100380c2c0017661034000702c0148818005080389003a500f44402d01c504481d400055414002564503401c00c0607500020b940071440c0900310b010f5409880c0b44400030b0700703440890700114004000400d003805070940da908000e000300380c2030001e0049180313180c8509d0524031940061080b1406400c100c2c0302041147d41c015958217000030464105c0303040034204242d0b998000c11007010480740c0603041c2000ea180000c0c0c0a0201c80c80f03149803144c620701e50b03403d11045862159040310b8a44d150640c044070340c0d0b10103c40e50043c180c05503140100d031000d5020842921031090200b0320100340c0c441400038510010003165124902350a10340961209142a40203416543c8040c05845a410000044450b40070421b05c3c03c0341c4241040300d520a80d9055055129903000000070362005400240c1841c034140403181c41c5840718512a008000d546d40c034508124490745081c1100d0303200700003600c0c44012100c002c3c00f041ca0030000340102002400040c04d5400c2014400131001014025000111 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 758932949 1250 758931699 758931721
    0x2100b10201903050309250b070c0503010528020906041e1505070606080d020a0b07030f060b03040b13050c0402070212030c1617030904050403180e190203010b0a0503 73
    0x11064800c04901d410002da6410000e22542090300c90312500d0042c0c184200280c040000980340710078044c1c0022001a1500254110681c007000085800f4107151070700103090f5070280b00d41440350702145001e4040030442c2041e41c800c140a23441c0107001900c14081c00d0442c1d110b54041d00c0036034800c40501134504190190038000502c055002020b49071039100c00c8000c02d82d0000241c18072506c01e06045c411142c0b215100e9803101c01c20000000180c1c0b0001610f4040f4202068440d0000a5800c001540358034451640d402d40304903070000080c90100000340420400340000140d81b0041800741c01c8190700303056035195264008000c84500c540d401107101f01c00e5680700e80101500340000d030102d1f46d49280a00a20b6255818030343c0003007003d21007071400603000425100c0c000070407506002031454034003804200802010054401c2d010403503e12514134911245501d8031000c0c0224003070b40b041d140b0700655060a030805640080c00e4040c01800100800603440c0203075001c01301207080142e165a601188a9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 758934199 1250 758932949 758932963
    0x1503022706070f150f05060f2803050102270a031101180f08010b1503010501030c11060f01140a050a0b031807030803041704030f0b0601050c0d02100b1020 68
    0x1d80100401003d0204200b6050140408a038202c2c00522007002600f80c0c440496000300c4046c1d8004000c500b203000e10385824400c640d00c4248080080040020f10408007071b141489400807202690300080e61200200d41c0030319500c0d601780721000c0c25800b0f6124004a20300320300314400280b011801d5922404280e000d0b8003101b01c2c0540c0400b030003a40310394500100340c88143c1442900348030351803c0803e04690402950607245281618a01880c40c0d1810004500034003003059030000700b043c5000045c80d4000c0601085010b41002d1062003803a50403c1a0141c83d140c42c0044684681046070302082161500c805030011510558545516913860119a0f50111003050450b00d1600818002104101d540000b941c0a9401000700c9030503d0b030708035400c849034843c0f400301034880b04c0d103000a4800101d141650660002d010300d0b080e4100300d200711869281080c842031450150b0400e20402c40c07140b40521607075035040d83c106c504441e00100c0c0000940080700200300c030b00440c04100706054046400b04444 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 758935449 1250 758934199 758934203
    0xf010309170a09051512040b04031e050702010e030d020a1506030503040b0403050c040b0a172a01020c040c0e060a0c24051602190606031b150302270607 67
    0x4560b98508220000b40650314500429200e0b0704d030580e01103840000f04066405414400140c0c140c152142c1d2600d903411070005200318100303e01119080559000f10344001000140b83e16a01d8443e0460310025090301001c00441c0d009a00880d1841c1145900040c01e41c802ca4101c1c600300c0c0c401040c072506101922540e0406019448002000110040100e0061080300e004800740c0d41c1e112424420041940c03405a0003545c0f100348010244a403c140a2150b0b1041500500300c03026154074500c040074550150070b1440d54100b1b507103072224040d41c0611080319008006c41e01045075543c23426015090040c0301032154000da0001c03d0f0340660a01801c03040c41150f4020b0050569501d1007481309010360302240454080500341408965001c5610600b0300000e04150042c218803070701445c8199071650031040540d4801d480f90000404100c04039001e001481c550f03250305188606182e04001100d5001003400700301441000144070440c82030050741001b080640c02c83c82c01000741e2002402d140030361400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 758936699 1250 758935449 758935493
    0x7020d0f12140a20100e0609120f3c0a030f0b0f1e0409050601050111070317030601090305060718120305030604050c040e0903070209010909020f010309 67
    0x5940c062210744501c48210072081c0e500d9404901140e22030702410700800d0701d40d60100301d2007800034a01c24000704c80081c84800c400b048414007800c2d54142c0064904035000c40300030781c1111051211a0009001842d0803d030510406450450000c854801c544103031680385001d12446014a140c0400210107010074911031440c0c10150301d13014075a214290f00022030140482e180c0041c40c060312006016803102141d000f071030540303c1c0f007001061100c81c0100d00c6902103444882505440541e03594803881c0c1105015200510b0550304103400541606070041101115500081d001c00002d99801c004007800f4110740c58451f103e1301d6141c0140d551041c9a0030080150241c42c04100c00190300083c0c804046109046c00a4225511000166261071111024002031010000a440c44c14280c01240c0c00001c11408079150665407020000d0710901910689495000080c9036015468081012805003c09080403c00c01d0103c3d40000c1d004004440080c0c107054a48030004203200c80d51210540300303004001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 758937949 1250 758936699 758936723
    0x11070b0a2003181509210405040e010504050d170c0a0e090a0903140415350403030e01050c0301031203062301080903030709032301020a0908010c020a150207020d 71
    0x201c1000100400c0301c0c03d48051050030b000c9031020b41810a0300740592a407001401d032034044e26125a0341d040d5503034001e1000d500100030000c0c0c25107440c071486a060641c5400081e00b030a01d1b252590801d21448518010050315400e40000c41c0681010301d9041909080744079074030030b2052411303070350b0003150200f1941c0b0620030310030418160700b160801c05000d4031030ba8511390603400d840382c11041c0340035a0003240c0c401c40c81840c80000311030081204607514407000546440303002000600c1500b0340c011541c1700350000c241905000415400d40118001c25001100a10141c505109100c1d840d000500c405800341442e01800c0101c0d0340640d00800103411a02500340c002a00c0b500e1074240d04040810040c0001c0075a000941d8080c804010f4074040c40c03003a520103040324a15299040e036200e13642c80c0d0f6044800d20400c10003111009100410011f803280c0c8480050a28001e121030840d5800e0a400040d0340144607490000740048860105c94050050010307164482800071404102c031000e401070480c40c0e0700c0c1e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 758939199 1250 758937949 758937961
    0x2d1101150b040e1b030601030e03040f090e120708030412030b03012d0e1b13051510050304170c0a021c0c080f0d2316020411070b0a2003 60
    0x50300820969454007100303089929144c2201410900e4440c1c50303c4880740600208001e0741c46600040760040d1804100c0c0d00742511054100d010340b0b2180e000f80e07142070b95a8082680c1030010300011303601e19100b44405041c100b03503031142123461000610040c420481d90080200480c040e130301c6864a0000034008008149901c10709261500460090700c40760140c5400180548009000e01c4c00d20444600c050010b400300007858007862048082850f81c400800c03020040030503d5441550710920b800c49202c0e180d2081d02c01413048078005400c0350002c0040c10400c200104a0719198600c003240c501c1001551106040010742c20b01d001d000d402548500c110303c0d000c814414000c818030b1582c5c080c802c600d5095a4600c0e18a5903450264031340c40b81a00301c0440c0740402030240c0c0014034102100b041c88a0b04004885040387c5951041c8000707013030b000c5108612000e41c24070b8803a00c03000502c1011414500241a00c5010038908014480b070084d64862000c40504107076041e1250035089220000390300c03070402c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 758940449 1250 758939199 758939219
    0x4020c0307060501081e1011070506070201050f010e2a09150403060b060705060a020307180308030a050a06050f06090604051c11030304060e01030e01090b010b0403032d110115 77
    0x3071064030310b54811600d005c0c0d800b00d106d203c1c14040300291002000006504081c240c0a03100511894016400620103803010030710a0010510940807540002030383c2c5010b04001d5072010040e00110307030020401d81042003004095000304405920702e040e00c1d00103008403500c441a441540007881e0042c94012014042020000150096078070030001402123400b80401d01642d406035801c040d14a9000703e01154081c3e01d1540215000440341c03401008141d103182030508080003e40c4215801c0c1c80010412403440054031405402001420081c0405440c00300080c80e03443c5005481889000c000a01c1816682c50303404030b500801002d0302c0800050074202aa040c425803503001a00c0301d035000c4405541d1481c010003160291440c603201d030800688034400440051001101030b25003503583d10b0341e00c1d001c188545600b9008000e1403610075912801d500d8024400003d031006020b640364003104143d5030340076501c60584d160f24a0b16008001c501d0310151207015001ba02c0d07400ca070300388000c00040f13101c06071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 758941699 1250 758940449 758940451
    0x11104050a090209010207060f0e03010507081e01030c051c21021209060f0c0a020310020a1d24131503060e060d0809013b0607031d04020c03070605 65
    0x4070780007a80503603602c1004040e4801c11400600580240c88240400340c012405c0c84620901031501600580304100820300715042500c0e450042107107a020800455070211030507030100114080c5024a514650751036410240d103004d1644035081e000c400450403000024000e005681094032080c0174680c4030040703000c110001482c0c0005000b850100c148840c4120115840940e000d0402860071844000c00100d903006035280c1d00e03d6000d092940d030050398042264081d5407462400060340d40c0640a03016142070600c00984140c600e488061610541d15088141c40d0803440038a9011100d00001d0882c40d18440d2a09880840e910f101012640f0b01c4134800d0061241680d480c00c010060b2103002e0340009140444007640c6c4800030030310707030b42c00191044098200d21006060000849103042044003664914240e080107a04000b0010494000c0c80700c00c07440e482e4800c1d02d5075481c001f8503841c000c1c031403503030030440c041c0e265260200403100d911158125500041203000342d03901e46c0e40e0341c070344a0040c01c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 758942949 1250 758941699 758941709
    0x31803180a050a0317031b030a1a1008060d03020304030b15090c0c06131b060e0a0e060d1b03080301092a050a08040602040f120512090616020a08011104 67
    0x209007000814103003086040c07881983e800c490081615038400c030002009900003001019141881041070018548030f0000c0c0d8003884c544030740444d4004260601041c080c45030484a441604502c810344603907908507450540145090b14a042040d0b041d0130141c1ca9441030794401015004904d08000c54400c4845803820703890303c21120300702030f5143d041d082c946600442402c1c20481d00000046110046080c02414025120300d814261000115110313403225032036541f080c804650959801c9289180c4056410003810100348003202c90304120001c154000c0c201e20000b003141e840480c004a0304d0034031402a000855101400c66907035130b1540400700160041c910b174500d1090042c0c1e007104a6407100e40320715407a4940d0366289420034610003000c881c0c1e510042c0c010740b075082d400c000c0410303900301c1c0c201001c010b40094a10481000b104e460042d1501c0c4034510f45e16800a01400702d0151540c80c1e0303040b200151603419103602e045889000280c080342565114021940ca403121085401000c0f0f409041194 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 758944199 1250 758942949 758942959
    0x616060605100c05010e0c150c010f0515030c03030c0c010c060902031207030e0906010f0c060f060b0a021204030b01030b15031605010e0d050d140f07060204030611090a0b03180318 79
    0x50001c42e0701d280d03105078940c01940c1c421001e45458800d6008c01020300040f021000011030600d43c81d02c1110110340084d20343c903078201e0407818940d9290404004410755000103400940c6040460309819031984040c03132411b810403003509400000d000c002d400c10740c0740e1a001401d954010190350030101c046d50010790f044000c0fa81c3c00c4207104061030b042c031456201c1d4006845070001905048004c4580321021801101c41c1c03540e9100c4000007554911070800604400007045958140d006000707880e000707540a40b1038104408000620024400d10845411658800076800d0580c541c554018000029441c105030180b0032102910b200c0c0b1a403010030002c607032013a04d5112408448800b400340d10b54200c0702c0609160f00c043e0603244202d10441070400c0e00108880c0c1c40d42410280c0403003070140e070b010030010755080d80c0201e000d2080c040d2030711908144801801510f442d050300b04000c102d08040c94858140895008000035206088505401e0f090a0325001501d60754074010020030f940750241010701d4051 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 758945449 1250 758944199 758944211
    0xd0807031407080f06041d070f150210090c030213050f06030304230102010e031b010c080103051b060417010204030b010e0c0313051204060314070e0616060605100c0501 74
    0x100e074440d9195000c1d0500f81c1d1400c0560303a400c00400120f4402034401504160b0b20881c46607540225451005a150300d0380103010350300c2c41c00502d0325045000390000d410519500d800900300d1500014482203450320380764007181341c00c200d0400b03401c0039042d5400a500301d00025280801281660300c4a0700c03903415580301c0c07080e5481d1340080c1607990007075000c0d03180403880740e04221748044100717820840c1c0c0c0c080510010a0750301c0c0c018005801c54100d0800112200d041140301000c8610a0090b8981c150080c40d04101c6580746880f80d985e2003a00d2800940465403910354045107484031412100a0301c9066441c24440c50758a14650003544a0b1100380c90500300c00002141c0e25100d102110b0059261f01c0d655400c0d5115110401003015030b50b41c1c100c0b4030340308103860804440d01c150060002003010f0707100010402da40100e0040e12900c01041000ac2003155500e41455960340001d8500203280b0900542c1046161b01d403800081c0000d03080a5400395481c007100c1a100d602458a80c0381e070388103600074041c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 758946699 1250 758945449 758945471
    0x206120115030e19020427080c06010501020607140a030e0d1206120c0302131410261f0f02120405190803011404090b040b1b0c060c03090f0d080703 65
    0x280d010b4000c4c1c1040f1822010004d001500d443c1d0003580700380b600a50068085c1c81100214010b80303210010880e0780c1400820568440d160502c545070042100b030001d401c5600c1e00e010000c1040707440c0c8484011000d4045400d024031442603000020301301d80c00d0b0031130300ca0303110140c0c010f8403903241100090291818801d0210f610801d640b0300350410b039031006004914608560030450100c43d82c1d100c600006070386a460030580d03024511f5440c001e0480c6440c07104828140b210380c00c104000c00a13080a024503103d00569203c0700040c410310140031001d400c16150308528103a001520001c050a02818004a092118128aa000c03140140e2184040340d02d121903090407404126241d00c000f602c082000d0004000d4200c8442e581d010101008000080302d08180c1d45407845400c040c3c80c02c2d998402c50004021151484800802c003071003206480e03034206111614003540da00381c01001440d500c3e2002c40446e0310040100b1200340d50024000548030100e2075004020b2410381c0403194034002a040c5000f5820b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 758947949 1250 758946699 758946703
    0x60f0201140f090d03020921030d0507120e01020a0f051e1b1c02100b041107051b06090607020f12151614070615080d02010203010e06040b0306010608040206120115030e 74
    0xf20817601901235040440122444610013010030404101c2c2c3c081007010024030080c41c41030350f00c15032090301c42c43c00e65141c002e000403c44420654410450303104100c84400c10360031110071b186440140c50305594800340100714060b020f405103100719681e4000300700f008040c2d403400b5080070400b031100c080701d15440b0340207008004060303882c1d11040960041c01d1140790600c8036801c11f10840001900220710300c0c0070081c0340401d55008980598a030b4004010704114607010f11110f106400080312141e05004100c000100217119805c0028460000f4601c8400152242400a89000f010a00790785481407000e4081c40c0341141124846043d556403003d40600c103010301c5290f000d01c40070016260a081c1d941c1d550900618802c80945c0044064080c002a40c00c020000121054601d5001507101e500d48145c040290001400e02886a030901402d40e9458800150f03142c111426458460f03015121800450910b124120704e01080444503400401c0302c455400c5482c0c40d08000780d8040280c41d003003034a125 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 758949199 1250 758947949 758947957
    0x90a060902070503071e170f1306110d0f14180603040807031b0c0b1c02040f0315090f030c0312090c03120309081909050306090d0908030301060801060f0201140f090d0302 75
    0x1407c1c2200910303c000e418a1043c081d01c1034405d200401840c1c03100d81c20f0032003501e11071a40100c0019405d90200701c5105024050b0980381a0f85051007203401c505d03034001407c096003640b400440ca40c0040b4000b1450111240e140c1089003000e0101952400d180c00c0034a8a80d0207550154045017400000007104d440b04103c8015403074000680c609100e0070003455000650041528481d00c00a030300e6181c16000c03003480180000e00c00000f00c004214a1031030110b28100e520803001c08914038000002c401306070740c16052224a681880e0600b20380c09a45030a503250a60f80b21120025482c066048042111000703881c1c00b0390b0701130049880c0f021409a01182a1601a8002892064180408142c40094850001900f412410b02c0b001060304c0e00082450076108a4074059580c1c4040c0c070800720143c22500c010701030b00d84030004e9031444d81440005072000e181846018100305001500c0f02c4080d00c00e40c0b03d84258481682d00c0380303850514491a035250342003a507040f4018081e450418203024028400c072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 758950449 1250 758949199 758949203
    0x1b0302120304120201120b090906100512030f0f070f0b01031109090a03030509070e09010219050f09061b03030a0c1d0a17010e0609010509150103030e090a060902070503071e 76
    0x2010000e14079a004503455010b040c022800d803511f440d110354140d5160b03180035204030745560082c400791411302d0145140750415170081380141040384400c008050b0100071525989203540005648403080c4581d00325a00ca54580648400d01180d000d20401140685450499000301c20f11076141c0450010012400d10641c0c4201c10b41c0d005070f1554000a010742c0009501c8001403050395800da54407e0150030745101156591580d950008411810f4130000b02420402e80750f918041e0f040c141840010200d40c402d9000091013900c0c0825280451091404029a21884181569101c0c00d14000c44000340962941000c0403491044000350006a10345050121042c010847d0a40c00c0c03030201591250100c1d001e40b40095500c504c00900b2080c1c04025041c000c2c1480c400004161038494401f90400400000030006040340b50010404a076005245044650781243c0e842e02ca51500113004c8024402540090400343c000300b01d000a215010002d400b40502680751340307400341c1d84421510a030b0172203403c2c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 758951699 1250 758950449 758950469
    0xa060513110c03071406010e070206150a0b0a11011406100c0203120316080f0132131e0501030b01030f05160b0c150f060114071b0302120304 62
    0x106031260300c03660082000c211510010310b140c807000c0119181154018801614460b55442c032102200a0801a0760b00400310340a2403126400c0841d0000d489540c041c080104036410102c003851540d0703964400d180101001c07500241c0d142c22106024043d1901d000e03007400b065103000b01041d400c074012082d181c86813600800150301c0902e0200c0079a080119800140c0c0c040c46641c0c44071007003040b0f03c0300450007411441403103100401600c20081c8480c80041c00f0040f900c1700784004004100342d00d45040c0c404ca03d0959514105034040071034109592031012070b2944000c010700590603071149540103000003110101d84401d0b441c4180302d80000e840c130038403000b403120000000400116103016001542c007072041c0c0503a80c4903004124401d0304007005400c072540382d180004036400c1b00c0c1410000e09414841075019194186054145200f008000400c09418048101d44004480a00700103c960b6698000640d0035107120148042d4810149400f00304e0007018003c002481840b40081550200d560811b4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 758952949 1250 758951699 758951719
    0x1203050a0c090b0f1225020a150e0c0406230d02131517010c030b030f07050112060308030a09061805060103020f0a0819020a0f0311060a0e1302070302060a0605 70
    0x59411002d91011401e80e4100c0c0080c407035005801502c0b5845c5000e00440e0300b40d10401c580d242c00007421600c144d0200000d541c0690030560009411821a01c501c024142c00000c105806984407410300c3c508020060b4081d15282d00441c20b03410000f040307040c010780c0030b071010400003017001130018a010700d140180d4008942044020b0350591034100702c003100c607000c22501c649507840c07200c8080140420100310240c0d4643c070100030f4442d450f1181c2400a9011401031901c644040740030f0341c681d5083c5c00740c0d80c1000300a44e103600305902285c000200941e4800c0d01d56030b591400c51a80300c010150305400300c2d020344c140001c4102d920f00300c0d5400e0843e1904040a40303d103074a50380c00c00c00c001e039070300b40d045030040015000028854130034004040001d881c0310040c0045000c1d072041100118007600300c6041c00040040a101268143c0110000c80c64261a442e5951211540607158424007211040c0e0107941418180103180d943d0700500b110354442e80032607035141c94800e00d003019910382d03000751032b00408040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 758954199 1250 758952949 758952959
    0x120903060606020f0a20030f0d02010c0507201f0201052d0a020c0a080403110a0e0106050909180a081e040e040206210c0c2a0603070306121203050a0c09 67
    0x441181c0681044102d8040180c40c4440424107046145507170340055005450b0390000309c0d40a006203031480689190451802440d50fa917041d110016054800c0411055801c030313030301d5807500c0061440b03000050400350090492030354000c0c060003044a2911b011601c000306045142d108404c1003070800a0721502040564590004000070342242a00e140d09106030700030b075004a07403000c00400195024680d00302168414005112a8100070340c41810002600d40040142c40e1703001d03061b510060808c44080e01c43c0c0c1c0350591400000102c0f0300382c41c01f02e4010403400c101040704240c001d0104440b203646010b811801c000c1420a02d006074403c275181c9505000c0040c0051502030b0080c500d10718200c11800c0208400606a0740000044031206034007800021000c040e210300f000f044000e55034407020682583c403048044186d02141c004410300800000c00850120380c041c3e00715030003800320323075000c100850028200200c025407420f00300c0300403c0c54400456148850383c01052880d4449449d0703603181520341 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 758955449 1250 758954199 758954213
    0x10909090503041e030b04061d0d08131106040f1802070302060606071a0705031009061202061c0c0e0406050909060609070201020d020c070e010506070f021c120903060606020f0a 78
    0x40940b802d402c0310700001200080b19001118000c500900c80014405109e00c0e5503070812401c40d00080007540703c4401e042e10303917a11000b21580129004e9003240071003010b1400001c0e55500c0d0b5a05584048081404031b40b1031110700d80c000403125030741890400b00312021010b038224403890f04040d0040e00040001969420081c009003d018401c1210103d00c40c2045500b2004000a546080014800206114018a8a5180d03501400800d182008120324000c4080302605820b80001e000b0103002c03d995150000401100741622540241480726201d080d100406000441c1725052141d8a00103010502d402e06070f10b09407081d40c400300281350780e444180801c001e52200404050456400300000ba021594070f001070301720309003500300401c00f142c04e010148085400581265001e80000c0c0203000118000705941401e10b40c05684540182c842c1191500c46284080009030002c03400140001c6c1d01070f440504003007101c1c0502000c003d040e849200403a214600c14000196980c0001c038850045650 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 758956699 1250 758955449 758955479
    0xb07080c070b04120c080706050708160801091a19030606230409110d05100509030a080403050d02090603010b070c0f0b1b0f061603060501030510060e01020106090e0a0201090909050304 81
    0x11505040a19400ca46d840c0c1c21217501103d012a038060300c0340240411a50030454107a009900034a2040b251031484000628039281440f4074221951100c0050f4068482c404c891140040081c000722074802c2d4a241803001d1248506c0206d90f010b02d4148001003039062040030f00080700b4002480b56140c0444020040a080824001c0e1743c0b8104058160040307540d110102080c00744188090280d1210109411040312401090b00400d0f4004000d00c000b1035a1080072103500591508046ea102d407a1511000c2c002c1c0901d100c032170303009000000085030404e03004014051044c0329031214000c0c1615001500c040d01d600e44214102990140103100911804120070050031801d2000c55450103030800005160140075907e82e0015901c07050147d600c0341e8140100340113440d0a007400c0c0600c3c100340c00305138425411407159004000c51038031140d229030300c07e4008000520802030f05010386085d0480b140d48441c03d0b0705c0103c5c04181041c0300082e400745507000f102101c5070440003650401c0e20741407000b0110300c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 758957949 1250 758956699 758956733
    0x1606050405040b0112020a09141002120f120a051602010b060306220903050901021b03030301090e03120907050a120f08070f38061315120b07080c070b04 67
    0xb05819604845e00091003c0c08211200b135840240e490302d400040f44c2c521850302405400b807070f500d80d0f00f82407840c0c00090344680c2c583c200040fa5039a0f0141ca02e001c14900422512080101014040c080a00e529801030780c0941010562a09403154107003080e0308a4080c5c07039a844d04a101840018440c2c501500c201e40303c0081d400e00b07851003200662810f000c6410380401103002c20b4004c54462150f5904005003445030b1185d41608840c4160200020b6890005103e0298002d071220300c80e800707080c800d20954041c030020000c281000d0900c5413080b61114014000c0c0d60088400c60800106482c0c45078540800b1504944181a10740c09500c850200f0380c003000e025200c03818448040d000188909503486090b111100b0000c1103524070300c0d4411480c406c141c08030340034811100c040c02801da443e503c000a03800c0d010350300081c00d0303000a801c4c0500c400242d40020b09910a080c50b500500040742002031140905a03105900d0ba1780f00c41d900381c2c2501918501420020200c40081e000609035610b81c68641 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 758959199 1250 758957949 758957957
    0xd080601140309060a0e120d0c09031b0302011409090c0c0c19080607211a1924050703110115031a0c16020405190c020d021606050405040b01 62
    0x6507542103260704503441a20201444e0703018104020b00e1441611079640391300389550281508183c5841c080b2864080e03148001195076030340b440c0800c014001c2014078000c50b84903030604091255100410700f003404038032041c2c1c086883c112014003110a02c10485540f540300070081c1c1c03ca5254420b50f1086600440b001c3c9840d1302c610001801c1d980d440108070108440e42c101d22015603400c01c9003090405401034100c100703020034000d16a45c4501041e900d5500800008000200d90340300501101905c000c46008603042140c80101850400b900204401030383c8200310b0078000103500403410b410001180b000b600004409220400029105200e0346c40c1c44104480007103000040324411200340c00d550f034021540c2d6440c180107120703041040c2061640c021400345185050040b40202c01c241c03100d46e804024071690703586000030310752040f4051550901022010410540c1e151060280da43c0320001c0c2084050300c02c00545080c49889111824241e881a030b480380d0410380b8001c14480030300f481140301d60502c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 758960449 1250 758959199 758959217
    0x605030603011103102606010e07031b080408030a1401090c1b030926070909200120030d050717010e06061b0a060e010b010905040203091207050f07060c12030903020d080601 76
    0x6d0071041004a000e4180c1000010041c2016803018003194405850301c01c010744c40503042c10341c580e0812243c0390700940040d8a00e649a641d900301078020120031744414055004200049100c1d01d141d0300c1081050400c0e25001e444c5a440003282000e80d0f0404001400a80012420702803000c003a5101d041c007803810000b81103804225084141400b400342c009404851780c0b00c0801003446004035104299405e05c020740d407603404c400c1000030400300141003ca45901d5010442d02200c41040045500c90f40c0e048104103c6400c18200050404072440000c14003640c0010012038020070b00017110b4015003004000328a4014044008001250f9000040900c0e004503104d10012072000d000c0d8001c080300c4c130b5000060740188840090b0009541d5001680110700c188200460a41c002640d120400240c45035151140494600340d03191034042180100c0030300804c2000a1003175004042b640c800c80c03046540c10f01015440c4802c90440301c1040001d001a407059110407001c42c0071f50500c58001106150141d89 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 758961699 1250 758960449 758960519
    0x7030c0b010303080a1a0d02010f0c0611070b010b03160309030903050d0801092004050f15070501020319021603030b1207140307080708070e10050901060503060301110310 75
    0x18030320990003540492200740420552240905c151100006445405186a1419000300e40f8004001100134117004406c82003021003409800c111400030380c0010240708000000000c44080e401008040710f200d42d2000c008101110104152842100c810340d60883c0200512811001351800c03101c02d80501600b00004404a00180200743c081c195941300c80641c0c0d45807030030050403102c0d08440300307000590f214002c040e60081c820440e005c81d001142d8280114000c0000158400e02c041038640070840700081030300070400190051845280300614124400a0b121100000d034481d481c114006c8e080e03001036040c0024001d40c4101c24460b00605424400654070200307500d890181d07008001d1407550350010364104d1508001c100042c02c0d2031406001c41764071709001c007581c440e824060116801ca029000034548500c2c0055100248070042c880c801ea560740e01c501034840c3e1300a44100f8041d508052116800c0640001260302918800842e41c4080e440d014905c2080c040240e40c00001c3c202c0308000201c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 758962949 1250 758961699 758961713
    0x209280b03090303041109010b0405011206080d02150f060d141f0905010509120304080d0e0d030501151e110a06060f0e070c120e030102090d030f090e06030d0507030c 73
    0x12288a940b002035540341403a04190900491310403403580b003881c6060040c0080000c6006440840d071007030070900c0c09001201c410358040d01c440d0708403040d140304000807060480d43c00200214400341c04c3d407000d080c0380c8421852040303142d4100c0300c0300c0e007000340721408c2030018004885003481c4c08107140580c1c180b00c0455102280103450000451000c0380c45914500c1800800c2c4039042d000710445c0020100300c3d001842940341400000c0001d044d42e00046240321290f101500540c5d1112a40c45c14bd9203561800500500140020700840c031800c18411219424580920320542c140f24040c20588080d1000c1d00085034001c80f00c46054500b4050000b0980000380300740160000b404041015140c06810990754031010750008242d0340c20841130002c12070202e424900440090003280c078120000300c402d5804a800ba11681007100d8002c10700c0800c800a0541c80891558400110b55442d0f1a50f5640c00c0c80740704007041507072250381c141c00c0362014102041c018001400c0e4035100b400c0c400036003901d43d11605 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 758964199 1250 758962949 758962951
    0x140d020c070f1a0403021003020c070e010305030a08070e0102070b0a0c0209040501050402011e0503040605040f0b090c1302040e1f030507030302030a08060a12020906150c0a0c0602010209280b03 85
    0x2084180028410f0249091084400d40a514411220f9040921350740000d20892003070240307082890307400500c0c040c0c011070501c0418080c140c0306090040e2940e41f4505142e581d488032218000084050001c21869881404a6103050034140d000b0071038213080c10070101c640d03803200e1008820300800148100060f00d60403041c2d8401d50150000182c149043d00015050a00e02c0c0300070380140d0050880e600071070f44c01400b66508203070040030000c3c640d5900c0c40c0600c1c4a9403181801b40c421540c2c1c02c00c01000c240009948180701701d081d10020529140a80460207900030342c00b038400010140360010300314810180500101c11a20201030341010b550b500d4072402c0040701d41081c0c0c0140c10005842c00b49903040100d00c1e800c448240c0311802244e00d000d0046051b407040c1d200007072045050368040b4a03280c1d10b52240000403191060216540c1803400c0b00c0f0b66480c078900703030115070340703400d40b04001000382c018404d4032030541d00600302d4148550b0048020300d42c43e02002099081100c1800c1c00708100d10810069 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 758965449 1250 758964199 758964209
    0x1107050319061a01120c02010906020c0a1406011206020d20031f0e04030806130f06210c0e100b040b0d0b03010c050414061b0304030c06020607140d020c07 68
    0x2091981c01d5070900a0503a000c21003004450090b0440041480e41c1c04121003030115400d071400120085801e004a0152214a074080c04e41d50010400c0c0540b0407010070750940d40e520402c2c1094419001c2c3d80400d803260024882e080780816280c40600118605400612141c0032031200016140140c0e401c00d94101e000c00d404488500380401040a8580c503100c0c00c20081040492300c074070342450018101800311008000a08000080d408508661102c443c840c00d40e0800a44c144501c142020f0ba5100400940c411580d44240c2402811030303580340c2002e0003160681040d803081d00a414415078034400c860240428400030800d480c0010f04c800340c10068005414406600c507511001d0030702040a4441c40c04140d88242d01d003517608010180c10404a034104d42500036801405840316000a03024015105804d41c0c040e14065000c80380c0c1c0c0c0201c0244141c900c41c034124286a52280c4080341e0f43c1604542860100b081444601c42044484014001c84198004003516080081450900b001c0c510340c49 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 758966699 1250 758965449 758965483
    0xc011d120a0b090705100507050120030a0b041103040b090f0a150e010e0c01031d01060305010903020609070608040b060d080d06150f0212030c070b010303050910030c0c0311070503 79
    0x10800b040700c400d40c1a0381108042c4002d280711800c020001c0c0ca0410090141c03014003a002a5120800c0400c0d040226104021610600002010a140c0442d5801140c100b10414600712440711b00345050705c5800b0203c24021159400c594444d0b40b2440d24800c0a0080b0106202c0c4c124820707084e60081160303000c4684164560711003a844000010700307980800c447c501c2c1c182d06040305002c407250005041e050203c800d00c1c003c50311030301c0e03c508c040e00d16414150081c401c0d4200f400c080180b007415000040c20700c0c0300e039085900b5551800c0980b03407200154015000006c1d102c80102d00443c800380c26181d00804020280341c507555803030340c40b22400c1e07200d0510040510380700c1300100080243e2201c0c5103503180c06c07030038001c00e0041040b03002502d50720b202d90400500e10000c008030b40e900b15020160740200d94050380d0b030825542c49040203803142e000800404c1c03081459501c54010035100340210055074841d92101100810305940c01c0d500103480c0a0601100d10503100006000c1d9000c20240e1095024009 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 758967949 1250 758966699 758966713
    0x102040305071401081b040f120507050405010b0403030e040209041410150912050f0a150513032109060507050a0315060203040506070c082a0405010302030c011d12 72
    0x2400030708212081d4020303072880120743c034441c010b0798003c0c0b41c0b107038858010746543c5002810466001010f00503504107111b6014800000700344900050741c0f0003c9103006808613490300342c0d28020042650002d004000ca2000305000c1080000c0c0203c14a42d17458100410250a00182c1d0010404495100311100e4541840805100c0b4540402c3c00c0032000d045c5624141d80881c0c0d290001814078907643c801c4a80032a6003100c01c1e01400800e20404114109440a80b564418a070810201d94582480850302040c03074480071644107001c2a40000000b680358592002c00400e811000d40200c5e500d103c059060764644e50004001a468441d00b4810720054451503255041244024210b505603644806060520a410b00066400005540c1121f004803002e941c1c1c4c440a1504c000c200ca41c66005000a21450f0044049034480c80d0302c40c84800540300e90340610040302c00400c800d4a0082c44041d403d60000d0380951440d5101d80ea9400b62000340b454124090103199000c03601204207260142c01c26001a1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 758969199 1250 758967949 758967953
    0x31b070602300a0903020c0f010504080703080a0f0c03020705062203030801080c0406050d12121109151602040e150103060b0f011409010c060b0402031509012309070212070501020403 80
    0x2c4903000340341d450301080900c0382990082d55820001c05030714413466254001014030303071282d0101c40150403000161000990349141c961b48540100040c0313070100302040ca000300c00901c110030300ca2040d60542c1c01420290728000601c8296400765a008514071005d0348000800c446442d0100d0081d446a603e03940311350300d403080ca1410030303d08a0b5110322581c202034007001240d448030041d0030ba00c0d0300114025003a030030740d420648200c1000104080182c0c01c026604c0b04505e0711201a100c480c10994003002a0341c40c012240c40c0398403030004a04c0514204031984005404c0030390001c40c031846050202c0b03c1c3c035408514000c001c0b0100b6881280c00603141ca8240d0b18504040052441c517213000c2c200584110108a4000078034000c42808504201e256041c607400d0240680051501100c00740013196a41040401e2074541d88032030300d59901070402c020000548008110706846a003401d024002e0301344440d40100080814082c00b003008600c118528148039120080040040921030030006079134503d14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 758970449 1250 758969199 758969287
    0x30601060306080604171b0c10082e080106091d0c0108190b0d0f03020f0303060618061e19081306051b03070c05060606031b070602 58
    0x58210800705410300804003c80310000034002e8220394460102c8500d40300820200b50345010785840e0b00c0100300b4240480703c10200125400010041c19a01d140703c91b03460080076034a020301952000405019075503c1d4441c00702081c0e0421081c40102074621360ba0307680d411391900b914800c0d00301c549426981e100c1588001c3c801400b004444011a010b0203c2a1854002a040f0b0b00c0007000018940060f0012040007a03071680000b141810080c101e0a0003c0941800c40540c105c1481c114003500c56104440d89002c00001500e1044800600c0c1918200440c010042074094088500703410403c03d01802c00c200044040140107141e44e164180c0d1078082c3c5092040b45850722a0000c1c0c244802c0d40b060160a40691894004264104001040ca038540741c42d1006840348001c4410344000011090040c5241d000c0780d10550240101c08484c15925130208000c19840203558020b5006100c2c1c1c0e6081062600c5805054003e026040c01420501d00000c0701c520b40924180d1040180b55020414504600d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 758971699 1250 758970449 758970451
    0x504090f29010f1a03180106060503010302030f0f0c0d02060705072709030503060d110904050303160305102d06020a02091e0a050a0b03010f0204050a081222030609030c020306 77
    0x190b000303010302c600d00f04c904099051101c481c045aa00d0020000f0790340410340345811501080380c0c00030468595244002440742d0403c0c0070885c40780c05551a0966035000001d561200b04030701c1c002a1410050314020071440b5100c02e81c080707030000c000b8071013000810350500101c40201541000c5029500b200340100040c4030300030f070404400c0751605041402080d40401a40c0d40180c00760741c1500e4840460900848403100006401e912510700010041082b038003001940c00341c40d04001e035485030819035200303406651048402c09500c0807540c2d410400041d081110320a14076203c02d10060000302d00c0080d10001c52144c100c000580d1184800800b14140a00c680e5842007000c0070881c0c01a800c0810f101d032000002d04403640042d181c10100306220543d0344507260103103008000b000900886803001c4003940052080d20b2003104004c03400914040e02045500d08800d01e0304d11a880d01c0c441180414103182a585e580d640044440c6010000540a102d46503507e030085d264030b200c60520744105490550 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 758972949 1250 758971699 758971709
    0xf02130b09222f0d0507050906010302040504050406140a020903121b060c0705061e1902090303040905040507120b040b070e13050a050108010c0f03050603150c190203130504090f2901 80
    0x4c0d00c2c00180020510101d40041594012992001907444000c0124003a000b180c00880d4400c3c6008203200400a495000140401e40c41201c50f0a9a0780d6003d0342c4124001d01c4552501500200d0700058410748840003801005c10002081300510004244545090022102c1000902002540d00c0c14804c0400607180c2c000800a0051000d6094a2081c44076000c0904041051115440604651201c90b0142c44511602404036a1175584e034000303080140c0727000d0741c00359054041c49402046807413054800e8000e50790402d80306c6030580c980342c1c2c610f0a0280028032001c01c00160714022012540c452001c4165001d00200201e40d1342801c501310380440344181d01080d4030fa03140800781104150880700018880c0c41c0340c28000b40039500d01c0c0110381000104000000c8820012003001845054030024220080e1800e02c600706a0ba880d02042c1c1e41c0b44a94a0f40105680c07103244c0412407031500390000c1c52045e10809075140d1000050740e8281300d9a220202462091601c414400320003030501d056640100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 758974199 1250 758972949 758972959
    0xa0e071211031612091b0302041104080c010809010b090408030a0506010807090513140106020f16050d1e020d05061501080c070602030606160f02130b09222f 69
    0x104020400e050440c8006119000b40100c9030302070b000700941365002240d00d80d0000c2070041d0b449104050340704412603a005c2244220b00c3c203400c05102c104258251401c2e50f00407802803203660b540d01d0054401420090031a100c07036480d9a00c010a03031300c5114003d80a14440e58909499081c00e0020b80251040144440d0400030701400304001360750f04c0201042150b13401e0f0351070f400707a02a40145e180076002050502500d003400c0d0300001241580010783e0f040c0e444000003a0342c000b5410700000b00720b0b01070f58440d07660700030000032542c0c0c04200c855101001c03030600c010900c00b02c1c0e05154003150800c090882d058401c2d400c94010040c020410b10420300e8188401d00e0b16082618000c140c0303906501800d070000d41120340c080000360054a413041218110420201c50791150007142c41c007080200a10b078000c0b40540b10f031310010380603000c0f180207262400b10001c2032803101c1e03130f100c40010703140705c1402a00780246810b01c0484004100020308070028100706001d0f00000004001c0b10b5000c0742d50b001d81250140f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 758975449 1250 758974199 758974201
    0x30b0901020a0e0603060a1e050102060106090e190e1519091e0606030c090e0c042702040b040e01020d050906040203030304030e0a0306020307021506010201020c03040e04020a0e07121103 82
    0x141d00003050010f48000b1110b482d101e484030004512601c42c1500074010080c030700310028611403481c0e5130760002c4034026800c4820982e210b000494500ba03480c401c1ca00942c49020200d03a40f0444440802510749480d0000240030b2200c0c4603052600304407000d881c0d8041921001d000606580025540302403541c1c0c0c1040c408000265035441019048007010405842480290400c00c1002d03000180115044920a8009601c139043c0c040104180c0c01140103520804034500903908080c0200f61072420420280c0b83d80741c0e02d60000300c0094282c080d040381c2c825559030110302203655030700c110000042207000050303d8038a0046010110741c8043e014021a5014404200050f40c4c00401c4940c041d6052400c401d920300305501041d0300710031715000184814008002c00041e903500203812081c511b141c4021549544504c801a405c034804c0d1002011240c00030441440f900003140b481c2500540b001d00b0800006564036a200091181510030f100058103041c120413280d10140166808024951030301451 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 758976699 1250 758975449 758975467
    0xc0504110a0507050a0803010e0f0a0b090103030c030212031303031107081c02090d06020703260a020a140d0204081b0f1002010209040c200a080405120f0a03020601030b090102 77
    0xc98060529110100003000550f5010003405101c10701005034040d86141c2c480d40c58000504011008a032015404004640000c0d007100307082c003a0588916020382034240b02e03400d60b141128920813955060302540300c0c00070700c2c02c007800e0150000d5226083c4000c84100401c0c041c500142601e011b0050403d080d40d05001040110340301c0004c03201503480303104a007000f80c2c100801c100003a01a4001c0c0a0780800100b030241d0078480d80d5001880780ba48295035080310340d6054840c03181150340e6006920400081640028450744d5254010301443d0130b241001c5c5040115020201c0a5034081d0721080212034010404110b401010070050514200b5145001070b000c075254003003240c0c6803d2450440c031800011011960050007036044412070305000e0028040c1c20401a4082c0940f610303402e58440d0310100807019440203101141020f2120f0380140e84c2c500d0720f403605c410001c0c1c01d07428155030440d034000c1001e44196200100442508a4860b401034241d0758551700340b50101c0310000300301381d1041e4010003010714 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 758977949 1250 758976699 758976731
    0x11508090f0a151a15131203120c020607020606190305030f071a13030f0c02061305090703090c09150b12070801060e1c0c0503150108010b0102010e06010b0c03070c060c0c0504 77
    0x240c01c0e55500001d603202d043c162446c0b44101526401120320516103401041810b5114060521040701c8400901c201280810b00301c0e82d40400300c5103a00180c0004000c5185072030705624900c0141e030301c03c180100300d80e100e031241070071948442601e200c00400000c5000820940a05c0700c00201d0410341042100e180030740480c0568402c0c84130040810400e010b200340514001c2c4c40d5140c4654016103940e4403040b00364081110a106070142d280b04001c085c0001341034034440d020701c400403948018202401d80c50042d160303000e8030340300c040c04000e01100f54000c10b085040501030070307542c0d003120341c89000c1e0304000c40e018101980603003180c010440d03c0c0844842c5900e414110740303201c01340f1010114109a480c1005c07214250b05801581e031600440580c2000324001580c054181ca800b031000304040010307080103a08a0302c8001e01e04c80260803000c0100a80d848070001b9103450300c40d810a0300e242c89401d5444040d034a40e6500040d0105404514003401d009020281d50007400090f20308010904100340004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 758979199 1250 758977949 758977969
    0x105040804030b04051f09020906060f120a1805100606090e071815020c091012171324030908030112020d060903031d0303011508090f0a151a 62
    0xa0f040043d1107004c6410440c08010011100303a4890038a44048508500c020240401100980c410803915000c50458a000030407103520581900b001c900c2c0c14400318410040000060402881c690380c0d403030321140751243c07400c000a07840c401c90107044080800c940a008442c00c40d0090410050842818800c0411034402550080c0c058140100150412100d030361002e0000d401030144000309040090000d500050078200c90041150081c00c0c50395880c0ca10f4101100b41c3c4aa083c0c070000c1000480041440040101e00180c202007049203000806c0300210586074269100b458410b9030050745004100c08070b50000c1701c41225141c14000541c254440d003550b80410b0144540390078036445860210341e5640f0000303607007561040f018007141d215030801400419881c018241d412110310b20f25900d00501000b1a810b03903050fa580d42050440c0244110307078000c030041941c01903200d0b495404052510400c0018440f500c901060042101920040c1050707072203460501540210425001d116175881150103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 758980449 1250 758979199 758979203
    0xf02010302181906030b091311191202120118060c0c02032506020d0f0c060f0f2028020115090e1c120509011e150602010504080403 58
    0x16840d000780c89007078480d14680e9903981e0f0b88048290682220f01805800a004035803481e1810001503a511060007402c01c401c491450403000d80403541c500188a00101c0010a900a004000c0709624121105150455a081060200f610424010441ca0a03e51284c0b00c410040000d0182440780b200854000c1c0300b4040041c40f607500c80444503800c0b0312030a0344c000d445800038204c0703650103100d100407004c0000541d10030038944d01c0c00401240960000885030809081030741c9000805901c0103007110406034002c0f08442c400c1e12440101d54210190050f01030007400c800000403805003800307041092018850181c0004c00080c0700c003204061103429110f44115468200400103405010200c0c018942c2d501a15994850200007048040b03680c2d10141071041000c00701c1b4030215100c0c600800741a01440c8010010746820b03002000e0344100e400c91608610035000215481c1281c5040a003500e260714040c0d403650f9901d0203900090000e141e614001007141e80000c1007141081d48824415220328040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 758981699 1250 758980449 758980451
    0x1626100f0825032102010f14040203070f050d06050601030b060d0b10030b130908190801061106040b0a02070c0305030c010b04050105090103032a060c11212d16021504030f020103 78
    0x40d0404500130f4110b0721800c07041c11f6041015a203e004100b9008800760750607402841241004520304240d51806c1d810b82e40300502d2001c0c030906964904020b0400100324504154070341d0f407200019280c100113050805903c220200315906480d007888280150000b00314101810420750b0000c1c1d4031004284032041380c44070320104075000941886071081c4100581c10b081c459031000340c281610b9000c040d0b941a01c0d6155901f210000344501000e94604065401410030100b05020407140c1038190f004041c1c60388180f111803e21543c0341c90781d03419600326100601d0a03035122000344c40c09141500c12070b0302404040301d4a80180d410b58500401d801203c02400b26030316940c001000c0c0c94110800c50080980e800300341844452141c000c000c000600380440501140f003001403d00b0079611682c2c030a00524000880395080510075108824620801c500c0ca590344c4981c4a00c503c4071511300802882c00b5403074a042400e904041d44148400e0001c6c101e4030003070340342e414402070000542c4600c48540d00b50b02468 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 758982949 1250 758981699 758981753
    0x50603011104062a05010608070b0f0d1802100807110714062a0304050907051801050a0311220501020a05030405041a040f051626100f082503 62
    0x40b81351022500482602c007080ca01c80e0395075041000541100b01901c40300419544055030780c01c51010076010320000350101100501010581010340c0d440110112100084100c83e40c1c11a0082074600d881c0021150000b0a61030402050b10b40103200d4096003041c1c100100103061400b80f1503503800107244541407213207500003a1010f617450072191000d400f4076208041a90000304442e03090b5a80d0061003640c1c0076507140400110594001c0c4261a10701c0c450071450301842c1103940045541354024030410003071541d550cc445400741160005020904d0100640e00060415011102c5155103985c0c0014115840000800d00003070002c025101200c00669011451860303040c01100c0c406c5241c0f49040d005483d0007a02c01d00061540c00035800340f03c0c100001d03916152003200032965140c0c010034148404400f15045006480d01d84200c0d070344481074a5000511030389400282441c06820b921004155000b0020110170000210302101e0359001400c0d541c0c1500e24583e21841000d401200d034a401c011411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 758984199 1250 758982949 758982977
    0x4120201171905071b1205070210030b1512040209061201020d060e18151e131502032e050409030f08090601270b0303040902070c0503030a17041109071205060301110406 74
    0x1015235108580c014642102000d06640040040840107020361069443c1d0400001030307548d8a04543c031030745141e4407900352a40e55400703001e1031220140c9090b0b0800001080e091011100b88080c020082c400200440c0292a101c4250140751020b420348180b400380b140500084200003031480c2011580e10f450503055664901c030000e4030b0400300c600380040c0c00c9117010407551102c0c2041c0d0004092260b410784031b17282400400d5000700d000c2228108081c2c0a144e01420110411031204601c0600c040c00240140361964080303800d07100d504104038041680408641d101607000095264001d104000500302c5616110030780f10f00d00702c03644646211410342e1581e003048807055080340381ca03110050110707561a961040c0500096214407030581c0d80b0300c10700c0c0000c600ca20b80841100c0854103980e07502d07802c00d4070300b0310701d4034442c0c0010f041111045101c0540e040a40c443c030710344601c110000d88404040000030f100580a442008040350303c26450169003040c00c81004d001e4400790790035407070f0840000c5955 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 758985449 1250 758984199 758984207
    0x301061d030a0b0a18121b060c0c030f050c0703020d080d0c050315030102070c06030e070305150708010503010b03102003041b1a04120201171905071b12 67
    0x40c001541c0600803000300320244140045520700850030303901e0400111907514001c40581e1002d810050403150102501b5601d00d111306a48040380712900c007003421000c90740c0d40c3c0c6403c03140e40b1001c9001085002d03400c40281900420882820409800c0c00c924000d035020605450315a02d000c000d12079400903a8034024007a01105403040600180e10401400c1983e045c0580190011103c0c41080124544104854141030007540c4919900150403c1034505107401607001d0640712104580500c40c4840010200360100040d600c0d60f00850070f40419414000002040c070345050308054044d1307041c00f4541c1d005480016030020190450000082c04c945000c0700100c100400800000101c20080103020038440003c0c44421174241001080080b176580b0841d0a03008507058070b0b80c0b500301405003c2000102207a01340081a01d20524000b0340702c80090900940f024000c1c0c8a80d124000d00e03080c0303c81a01424841c440e0042040d061101d40502042c0c0c10200c3e08034401c1009003401d0b6404080c00c4440d001d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 758986699 1250 758985449 758985497
    0x60d0b06031003050f1f1a2706040203040302030304030f02100e100f0605010c140307060603060e12180f041401061d0d02010903030804050705120c150c03030106 71
    0x24809a52800c08407003002c86410240410342c0c441c0207030b0b03100b80700c01e1704005243c04800b035030121410f8451146808410041c40079601289013020079290786011943c62884108100c02e0317030154440002120f5044030345018000b00014000d600c104203120120750000140c03a4080e901d403816541000b400c201c103e0400f050015182405414107160045192012900c031242c283e281004001c42c0d203c0b03c40c80781c2035442c130344500c80c0494041c6d400d1501181c42100b8182c0051000c0c806c90380742054581c1c500084a0042c1d00c16901c103903075182c1c03048220300706100f511011070b10038030f000c0d0401141035030a0781c010b440019004d110b00f1844c408400d40352115000000142180e82e4021155a55488041e0001c142451004a28450704903458410b180a00c568619541c040c0e40d011a40c4e415031f601500d6081015000b620301e44561391000030b9507614180a1032081c40808007801c5000e82000c240b0203060b215080c9610245400c0c007082152100000540b41150031602d4559403024424003880c820301d103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 758987949 1250 758986699 758986721
    0x6100c02031006060806030102251406241f0c02040908030414070e011811091002070f050306130f030c051903170613050a0e030408060105090c030f06060d 68
    0x81d000882c10140483c0d0000013250785640f5044d216541d1501014203c1c8150398103030000014a1008030b524400300791a0200d1284201d000e40400000c2d02e002c0c51034880304072103140c14280c01e0348005c1300220012103844900c035401d95a84121522600020f400191034803004d5040051a12a110a40d80d80d50090000507802030a100c0d034030300b42424040d00c4508092010b000d036104160000035080140c82d60b0070304075604a0b21109112202c1030071a00580b0b08803a071001c0341c140070f115200f165580c400da404c08002c0d85800800c0308900c0d004007002e02000d207030b00c41ca200303030042c001308400b10800807120004103601140255840d9200d01d403c0e5a040300141c0040c0684c0f2480c00e03404070118002e514255013500a4075980003280c3c11380c029130880441180d856820580c00b840f044034030b6440c1d400007030b0031100d8201c010031144d03011401c403442c1d504547d000591551081004101900b06018403607085440212114a1450003040c5d0308030b2180040c00550090b48005060720303034608641d000182030a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 758989199 1250 758987949 758987953
    0x70e040e1510050a051207090f0b030f060603100e060408070618031701050418060b150c0703060b04112b0504080703080705091e0a0803040e0f01140906100c0203 71
    0xc207082e058000880614040c040c0039499242c008a543d2a1400180d85009100c0005044890078030350031602402090b501d8000b40e0b07455120b080b42c00c2e502800f19a00c0a0003c000400e5103191042c01c252504040c86d00041185117003d00c148e01002c1d011a90036401500702030134941d61001c510f0940c008040d046203821854000e12500c2040540c030520003600f024816220f0609a40c1310810002160710a04c0d1022403071010780000000201d5a41052060000007400a02480030300907440c18035502503a21115035801c011000d204228680c85000d90b1802c042c3c0c4e0030007507112511072004641c4a1028001280b003070200e0113202a1141ca43e09849180d000581840642458a400c1c03003982c01a11041f00414964000600c0c90352064060b00c00391000245201c420080c9100005048030288920540005006002117140e0b40700f040104018812600d28031041c2c98507000400d4180c0f010707040342085001f00ca41054141c1c1c3c1c1d140d202d81d00f06000701d5810412180d5100103035a04030b07401c00000e400d8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 758990449 1250 758989199 758989201
    0x1208031b0301060816021501030b04390e010f031403040f170f010c081b12040819080603030a03050a0b1011070512060a02310303090905070e040e15 65
    0x380e1300103046401101c60859000714002c201c0004c0e80c850301c40200d076100760410240108003290115882e01d8000303020b102400c8880c200c007c0009032050307204101417808030000c42ea014004000003179250043c060b104840c1e50550404070307000308403620307880064203440495a00a001000034002c0702c00a0042ca00602c0c055a03880403405040c02da8845031000c40e000300312aa0a40c80810300951100f000169a214101d548005904e1080810300a05142d0107000348071806c01000c110f1300440c0110301418001c2e442d0200040001081c1c0c40b02040482000084010301032651000015144001c1560501144613603440400d44010810480c1559204104045001c1c800d9004900c0c460340c2d840070f5050f51542c9844809003c003400b83c0b8a525481d035481040000c1001115502400c40d5280c03100d4840f4914010180a8580041c17404c8a0041ba883c00b400c100201508215404014200560305010078900790a0203000040c1400c0d805000d00d88a261a52070000c0521121101200020041d066 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 758991699 1250 758990449 758990459
    0x70305042315070f1413030203060c1b1b0d141f0c11070312020118080a03050106110316081b0708010f0207050a03030b0d0602040e0a05101208031b0301 67
    0x42c5440d0b10200304840c602d0341011807405485048480c0d4001d103107484140117202040c00f80480d66000800103100d2060140c00400185c1d4244140c034012013a84501544482c030340070020a15164040852b03c032940191100f26507603c203041c843c2500c0030201d0b642803850519007006840c071041c051031411240a15200021150b82d030194170440c030b40c102e1808103c0400c51200940d80202d010002811640c058481080040d40c1e10030202202d07460703480082000100e000d056143c00221a0040305c4284c00402c2e01e2041c15418443e003030050610389424150468034014480d1a48a8403200e0f03851f1b007000701d040100703110320842115043c81d070852110701d48a44942740303c1c4e241d44080c01090b180b5403d0400340e07074905641e40242d0b004247c00c01f01601c07011410b5a07082d80108100350280c2e41081814481c0d0011514620243c4010800e090010b40c0303600d0b00e03600c44011074000602d000904040c4020030301900580224500c00030f90301c010096501c1d00c4a00740c2c00d800201c20440c07070030240c0d030001c000300e8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 758992805 1106 758991699 758991703
    0xc1707110a020409060f02070f15020708030a0506030f0d0201020409050f010503030f0d0f020a11150f010b0f09031e0d080903090d0609051501050109120b0703050423 73
    0x251070b00c4900c1b00001030341c1000034191440340c1c0c03048100381405035038054040010540c0c1c004524145040c0d491003901e02010700035030043c658500001c1d410b42c608005010310390403200126401100c2400009001c0e6120f40a0084158100000316000407160054a03050b290010050b50400b459801e500b0794582190003030100349501d030034030380301200c00910090550039901c1d940e110181080e0f0380303803518208400e44a07040202c4a00200580300501546141c1510020306649540c4c41071240d00f18000e00400107202d40c03502540c05041281651171001058290440341035800002e1596000d48104208560b14107460704100200111880c10b044e83d004100d2182000066080b904d4480c9464403452443c49080c40c04000014000e6680054116005015500200d4918251661505a404400780541007810f49500105040103a0341c51202c5a0320091616180c2d6900130f004e0741d1ba = true := by decide +kernel

theorem cover : BRFrame.Cov 758812949 758992805 := by
  have h0 := BRFrame.cov_init 758812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 758812949 ≤ n) (h2 : n < 758992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
