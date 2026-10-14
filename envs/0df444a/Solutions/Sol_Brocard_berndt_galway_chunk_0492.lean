-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0492
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:05:15.351983+00:00
-- url     : https://prove2.me/submissions/d9daa723-9a50-445d-bcf4-bb42b46bd3fc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 88309353 ≤ n < 88489209 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 88310603 1250 88309353 88309391
    0x50403020105060936010e0a0201030c03020913020a0e12060f33010201060b18180603061303020106050a080d030c0207180905010204030203010c090311030606100c050a140312010504 80
    0x541740c0d544d0b500600e030042e1884525200c05403a0b10b10000b0000300922414659844e500810120f0000b810004224000e610a009880f8803940260000c03c00e40003420050020b50010b5440c5001c0101040202415030364000e00d03800740601034005170a09041910b01d1804001000301410303407406d15000002c0b524100508a503a0580d190600841841c80c2e280040340034220961251014010100d079a1004a518039060035a02c8402c503507405400020304030b0050155402c4849540c50380010002403400c110b0f100c0c1d40c0742c100c0c0c4a03100014031240c44000040120099402100c03a9a11403804120b585070180b2800d8800b02141c00241051450007850300318260003036120b02c0d259a00c4007100b10070031609406a401455000b0024001d00c081200010450180c07403105035250089004468050304002c1f41041c0143d40207080c40800c0d8510f50801d6400c1d40c2000c404440500c580c0781d0346004648180c071541040b02414018603520507148039822508401a04581c3c13142d072070403202c2803080202c130017 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 88311853 1250 88310603 88310641
    0xb040c0801110d05130b01090b0906030a020a181407050403030305071125030803010b070c0e0c03041e050604051c030e0d03050c0c06010303021c05090f0616060f0504030201050609 79
    0x40c0800c0e01d80c4e0b21180c14104ca5001d5000410b1b190842d800410411000c2d045200800f4069645002039960340302015a21445040080d402101e0742e02d00340036400425040701c2210810703040128074050407491640c0a550206d92040005102242c04c0c0105a814000c0350b07000441480e04817001c090130303000c80c0d0326104503015a9401303112903500a15014010313a903080003584c20405450302da41e981e04454109500078941155106580e4001054026541d01c0a50055102c1c440650550380c0302da403000d400c48040c0d843c1d640070840500c5c44a0019104000a52150384108068841b05030162102061440d8200c0e00c602451b0502107128100391001545802c81d001524020a090311803600014040c82030a45640140c090400044145600001c0300780395141e0251840401556003c0100d65600031101d50540c03044041614071064a012800351014072841c0c0c80540050b501c0350354034011141540035418a407038030303401040289070302813240350341c0b20750b05458030410b61a1142c04034143c100610 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 88313103 1250 88311853 88311877
    0x1e0d060e040b06090604090209010914010b0406090b0304140a0c05120f120d1b08060907050a0e010f05090301060311090105031c03020c010b060d14091b04110f070b040c080111 77
    0x100244151b91190401e141c0c01f03130042c1c628941d6503160ba032044003130140c10b035200c0160700a440000450b10001c000306d800310b5465503114804c00e400c2c0804103020f988040e03c250385e44240a01c0680001c030050100c6110103100e11101011300d1b2420301402030004c0000f00e200c985400004030b08842e6032000c180309003002800b2035807a641c0c072000150000140510200000e0280c01004412901500a1007041c010030b4100c130900c038250b4070702030201d0b001e2041b07010403000070b184041aa200341d40100881100ba01d400e081c66820101008046421107071958420303104a00443d44009050401800c1e1a016000c160301900701500406817400c800d0380500a84010998000f0b100c82e41c000080d401140c0714039008204a94541422600701d002d005d003111b804088044c0e08000c2441e00340001048001c0b4034500b242c50000c4029402044028000c1884810040100b0000001c01c4901c51004080c0c862041c040c500f2a400c090070903810001890300b15107243d0781b61040103001c076400c00083e03d0702e1744aa6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 88314353 1250 88313103 88313119
    0xc03061d060409140307050c0409030e09070923010912050304120503210702010b01030c1e0509060d02070c0806010303080a0b0f0301052a04180e031e0d060e040b06 72
    0x70001281c02441d1104000e01a1081c041e603040c1900700102c000c0032050300940031540c040035454200000c40f880408000c0110344040750040c2c1c24280720028641c010464284000e14555400e4180410002c4034480034240c59000d80c41e4a0035a00081104080c0c03128159883c480d8032280c2d5500c0c2d51344a01e02038031285003055141c403010450304004461141c100030704156440c0a01e00708111614a042e58110059420205410060751091051140300740285e5582111070011041505040c4010040380741040020807102c2042c1d224000113044d040480c650041c1e0383c059034207111041d007240d5040b94007260016401040400e07401b54040c0d070400088000041c44c803800100107184404030b0310040380c041d42414100403403041d070b43d440008150100c481240003509005210031952086010311400c0c50f541d8200d0b41290380b00b50b4400c070300410070007049038a0030700f0081c5482c000d04090900058540c84c0010450340711041409244010b0042c240002d40f541070554407502d1441c40104850f00500038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 88315603 1250 88314353 88314361
    0x4020906040801020a050319050f0408090a0504090b010e07081614090d0c050906010e1e04090b01030c06021006080d0e0103060f031b1401050706050c0405040c03020306040c03061d 79
    0xd180c084500606070380c002107584d001d403924007a100d50011104149001410400d583c158080303030040504c56004640070107101e54460b642e14401d50402d840a80d04a58418030104850b1214401c50707025a014103d001c2c0030358505290441098001050f90080002d08018885140e00b03c6540380d0f107500442c01c01d00c91014a0f03a0340800c0700d014124055138050700c1c140600d014041200e500c04150b803429035006801d6551100151041d040500c0703003c1c0c2240d40e801d000280c2032040545101c200b04010404659950a40c4810b00075410a0b0000d4400221410b81080327107503010842010300c64080c4000b4029580792040082d200c0e0003030300d80c26003401030000c0c0c801c0c0140c0c425400324000d008140c05855100b81c89007007843e116206a000c1d000c24402c10ba00115030003103034a6a01d04903410582d1014034018007596042d01400001c0c082c414000c000348008140365445d030040710304400460782d0040c1c881c50004104801c1d10f03060b82042062620b801c805200b0b642a0f80b41103d10307052040c0c0301d0b80b03090b02d03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 88316853 1250 88315603 88315609
    0x21611010203070b0a05040501061e0b030c070b1602010c020c010c03050d0e0d0f1202130b0d06090c110105100f15050f07081207050301050a03060e0c1008060a1d06040209 75
    0x480c1c214000c086a840070100300175542181d02841c001da0044000b0440c0b152587d0882e4031000c40c60195800f8100000010058041204005e6a00c10028002c0e541001000e59031541d403e5000c0e10f40600c405000b6102c0059980d091050a100d0342161000b0003a170780540d80040c1001d0084640602044030000d9060b44905442c1c00070700007405400100d23003400012260040082035501302e40b10009803142180e289403002e1740240d0301d8501303000d0b5492100321715252442580340e012607020000141c44e20270010f03070b9005610840d9040c0650341c540f4080314034140389480c2158402006000064524042800107081d100803190980d190104440f901c580300c1c1600361202d010708130080c4004200050703071108019890303014086107240d1661039045500c0e0040e0aa0311408240074445d0004192035080000c00d01a0700285804050300c0252620061a1400f01e091902d8a64280c8040b50520007488694240719038980000c0000d0001c103080f040320809a08031002d0080c017950f10903a00821040d030141d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 88318103 1250 88316853 88316857
    0x5010c1a0f01060201150b160302070801020a1d010804051c0306180606031d030a1b1a0403091406031303210b040606030b0108070c0c08070801020301080d03021611010203 75
    0x31062080080d150120462003121002d010f101c005500b40030f40b444112041d40e446009035201e1102c82400e1032508001c004000040c44020303411031107011000100c6020030310040c5141e03061740d51160304840c2514bc481d015291150310a6040000110810001c40c2d0040f8200354646500e403981c82c00004c0c405800c601400c529000800144000075503841e040c0c10b00d6000310202d9042c0c0e141031004500202480140c44030fa44401c59140d0820804402c9e041d11a820311805103001b0a140d40384070105840f031028002483e00540390034080581804241504940554002c1040c1103045241009490215401c0d0201a080405403000c1e012030400f0140610051031a1064456290307000c4031070781c24944094025090824080c03807510502003041c6100c1e0150f1141040103031200c0c1c0346600c0704075049510358460f110030b42d040701c5145030124680500388646d40c0200030240000d6182e504100404c0d00b4441904460000d0503c108400800d4211400d44c90881c1a00240480714400804005034118 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 88319353 1250 88318103 88318133
    0x2130f02120603060a060f0308070c0f140406050a060509040515030a150b0105070803010b0d0603020a09060306060f03020a03020913050303040b15180a090309080f031c110405010c 79
    0x1580086021922460040700251080000b02d04450303403600c5074078041e0215070304d5004040451001d85810f0011600c61001000050b20070f4142845903940c50380440d13000703095034100281104000302600306500e810300520300500300413942c4000307007440d02501174528410079038064000d580303880000301c0072851864114191600541540c1d010312983c502464098440841c15940600d00b1349400600e5200d40103884107203500802152441c0d0801940d1241c9070004c0700c940c031610351640c3c4007000685071070546400400010f030001c00c0b0941540741c42d400b550925004013000e1410038108201580d991900d110441ea01030301c6c1029280c0303901404000009680102805038800002400100181e910402d44905241400b20343d201200d00c041052a030340344242c00f01c0c15881c0038040707804d00c0281d074020005e41c1d11a0518210943e80c034644281080342c2c5038090356181e000411005600e689140781c1900d00207440c402004a11021321110003507004134011507041000c0600d40300e081180c5c0e001d0820b19 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 88320603 1250 88319353 88319381
    0xf03090201050c0d050c0d08010b030609090a050d02010203160e0d020103050402030a08030112021806180606090306010e0105040507140706020d02040b0d06060e04090f0f0507410d0213 81
    0x4104607130701e0240c401d5205844044051007070440741a0014442d40c41d00d416100440b00727191468a401d4200300d80c144010b006d1503018010241241e0000750108060001c0314900c1e0009a103d250100c100d040c00781c160030420050280320201c1c2181c90755411a040c0080b982400c000038143c032107001083c82d00d83e9902c2c009145207030000c00803844641c4211024090342c422113907040128031001040c4204103003071b20000e81126002c0002285071942482603544614050401c604081d010300010b07203401d50a0340703d24400305120005100e50705003400b541e80c0c00040390520b401100c0611340902c2c007070320522902510180e07021542e2900a00d007601164000c180c07400c52a503c62080100050042005108400104442e01501c00302c41c142030040d040307216008a49800300000035101c03001c02c01400541120305000c0c010000c503c011402911703000f502020410202c072241040425041650f4840410111510100076215240e40f240d543c140031039410740d904c0469101c1c60400b500a0007054841d004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 88321853 1250 88320603 88320613
    0x1506080d090e070f08060409150c030501051e06030411010903060905060702060a0614040b040e0307031d061206060714010e0a031403070512070c0c030803060405090705010f03090201050c 82
    0x104880d4040103000640e1510410042980c694600a03600c507248130f00b0714030110300c40c00d0010b001c500e03141d4403810b15140116642074044a4404c41101150014840303400881e5031940140610b0428040c0440e41d00c031400c0c0d425001d000d6010004010b030000400040a00c4e0b0003540c01c50984e4030a102c014011507105005004d01c0f422490459240e01c2d08903860f90052107400000f031281c400c04e019030401c40c1d0b00c8544001c800000282404040d2040c803d085400c40c2c0c0710080100c01d5038042000b499440c0c000d5645030344540b80c81d11003003091803204100c1c0e032082c1800d10620b1102402401c032640c1081c0b084507495940d03200c9240c00b1544100311405101c1c079501e44480100030050102c0c421103039034803954850701c1895a81c2045041400203551030790014100b03010400005c41200c40143d04000035007480125045503a860301d0291902d900129040c03030020040c410b9504141c01440c0e00f02030b8081c080c103041c5007410f000030319140e2030a00c50410140c4840c011419079000c3c004544c18822000b058030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 88323103 1250 88321853 88321873
    0xc02032a1002030103050c0a150f0215010905071211030105040c0c050d0306060e0307080a03030504031713230d05090d06020c0601031e0503070204020d02041203021b031603150608 79
    0x1500a4000744020340701c6007d5442000e82a10703041014a056400301010034092041c400c4040b240e00c4c812200100c2588141a0308a03060554420100c1c02000606008a914904501c00400500000981084050900c0c0c09480384200c50300c107403415101c0548001038a140d9001c0300b22071003071001d000a0a240910100038095641c0b5421141c203444a035111840d04030f80300e02c04e040d910074052042c1c40f900c0e00502c1000000a01c01c0c0c0140360414080e2070040030140c61803040014a403015114240300c440362400b1001046403860038100d0307000102c030b1b0800c003114820a080d501c07628044040401c021000440d0130141ea01d90440c4e0080b6a0424400c541f102c0d80300c102c440d1780304400e010a42e0700080400b00844052000c02000030780650010203581000225420700c400b030340120f011120000c3e000c2c0300102e280c11842d03581625443c0039900818049100e5020a0144030b2400c80c90f5000790440c148003000f0010b5000c18404070b0780c2c030210404082c140c1c041c04100030030341c039040f004843c0a0342d2601c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 88324353 1250 88323103 88323133
    0x90c18130f060f0f06020703060b040b121b0103050405030702101e0806090c03090d0c170c0a030305090105090703140c0a0f0f060f08060402070c09020307030e100c02032a 75
    0x241081d681c070080300f43c81036074a5001d80555030301c06100f580016400740d0310620000d011904041918007010b400403800e81a080000340040c003030f412120403640c2c002d82542982492410301014048002e090420660800c0e0311119202d1141c110064082c540907681c2d101181d2207200c40d000044003451688025a4200d82c0040c085401075403802d2040541602041410781c030201180d009801c210700408529119102c2500c0d43c401c4030708150766980d0080e028016042040005011102c02000549070201980c03802074121032001e0400c1002c3da24040070424004d800140c3c1000303890b04020341c0c1c0c040019262090346888030300307003206821405420001600e40200b40e840390981e80d8404600d0100b94032040211102c0300c1401d01e050000320a0030108141c2c0c205039000f4082075000b481f100b904561661113200c01d81c0c0c801e8400c1c1c00007995034103910500981c14421800c000480540910604906400080d85c902854080001040c40c9110740400765511004502d581220102501c0c4103055030320748 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 88325603 1250 88324353 88324361
    0x307020a0b15011706061909080307140105100b0a05070c0f09051902090907050702120d051e071a0c162003010c08010b0f0c0f0d0e090c18130f 63
    0xd5001c100c0c851165054500b00c4c194039446140d000c1d154604200c08040030903140700a050ba050244000c0045c0841d041d80140014140940511a88056001840211400c44100811a0822440750b00e02440882144000c440000c0304a2824a444e07481078205804010750aa20181102c50391420002c1d001d00740d50046845440800e0500300d100d403140c080001a0721503030071130503400710711040020001d50084010308801c900207802c40041138440e2542e146402d40700e040b03403000715a020ae00d4451503403000d062a800c00b401d5124107030504400d030759049161905201964042c08d02540050250b0504109860304501d204400b014200040d00305120341c13024020b0010903160070500c140da81803c05028400502c0900da031803c030580e1810100d05100e400408601607012410091414035040411000744500080406070090f40011034001d02203a10b2008854040c3d0701140c100b1801050003001d8603510b81229504440b0110b071180003522201c0c04a42060225180090b008a0f052086d48 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 88326853 1250 88325603 88325641
    0x3020c03120108150103050d03110f0706090c060507110f010311042d0501170402270115090e070f05040905040b0a0f0209030309040e0705100f020c100c0303020307020a0b 75
    0x206950744e01c64001901c031001c090174007001e40349922210558240e14030a40c0582900b01c11840201d0502c152041442419880310038107807805a1240f03d02c0090007403100c0d0030001018642001460f1107016a0b4001d20030b2a0100018480c01c14413208141ca079001e0b800403400c0152071a07003a50740710f8544842c405108a904c440c1600701c44501686160002c000c5030000030703107034140c480075001c04603030040540700f190080c012038000c030091041c84020085103021030a920301d040603221241d81030990901c15030540450303820400000040800100018010054000205150414409114480a032401d201c2d5038010078036245804200300c14000c010444070301a441d204001e1000c03221020020701070f402456100d81c0c0c950400c00c0303009101c0c0f0f81a84001c8d0320001640544029582d20350000b17540b0b0883c11002c41c04540d10049268000741d051002c00d807042805c07202d82000d000c00d4880141189a03464009060580c000081850203000300f10b04000389600c614034155920f0030000e501e6400514903 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 88328103 1250 88326853 88326869
    0x509180a05160504020405011b020d0203070b18090f01150512010902040303030b0d120c0f0204050f040506090703050d030c170421090e040b0711060f0411010509030a1203020c031201 80
    0x242c0214652606000325822248169540241400c0c422100c01010241c0f400890740326001c645c041300162130a0012400402c2c440a1903900c9800d44c1c00e031040404071881d02244140042c2081201403103680c04c03401d0640c0e00140c000e0082c080d800000b5a064411715006c140090003190000a4881c0c00d07800800a0b28800d580c148031071407810083c0302d00f80d00300c02c200a1201e0f520320110340b941032045002003801c42c090b0050f003a404007107401042c00c6860035a85600315446410800007404010800260842c40c25001408031902d56240c40381c484110f8845241055281c2c014030009512603140b195562800e41594a998101803030401521902d0007000b101010141c1d081c0da007a80d00910b907600c101c1e10407503a0554665034a80c1c81c46c03034100d0010f000070248407c2c140c20b0b4500d03d03420070455106401d01c146441032400c20f4209091304c94000c41d0050b0403c5001c0065090301d4074040f0b140004c1640c00b481c03030071600d2070003842940079019034400c2800328840843c01c0581503d03c3c0d00118100c603404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 88329353 1250 88328103 88328143
    0x6042a15120212061002190606030c080a0308010306051e07170109020408030d020c011103010b0306043602030c030d12050a09021c030e0402070506040201021005100509180a05 77
    0x41e00c041800da0003168002e1501511400024180341007216098034080400d106486004036080540200c140c440d0100307442c8141d0b0b03504240204411074214001810200c0010686180e42e560300624284050000a00080d1240e0201c0c2107032a0b0144c1c0d1605180700800350036071514007038800402d00c142d044010b0115442d25400062076024502c2101e041d1011400958600004006154040d41c0301d82c0d6040341ea590b0320381840b103d000310707500030f14040c001c0c01d0609940c0e0708040f41004141e9156004168101442243c00f20545100c80000c040c031041d44101c140c002026800001d06000b284035103150140100a2076000e4507038041504c4c2100d10705880c0800154940e408400110b0300c603028020340000b031a2144080403005d001c500c103816842842e20035060308030500420300740d07085002c08540580c4040207000441d0303014092401441311841d42082207107001c1c0d40702911200a481114003880a4401044104800720414440d6034501d80403107004000500d0083e079190f80440c202411150a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 88330603 1250 88329353 88329377
    0x3030815191e0b0a050a030c020c06041403070801020a0f090f05031905031315030f051b0901021002070302060702160f06110a1b06021b0306042a15 65
    0x200800c0500604500300c0e00103032031070510308007003045090404841e0b41560840e00008030038050380c00a0a82200c45e9807402d4641800721400b038180c403460403044d415034202041d61201130729610b0689085070b0301184000c071040312400200b414680e02c0e0b00304c92001d5000003400f0001e250490401038120017030b5911030860580c0d40c1007540c01d0708814090194140c124440d124510b0000c211a5a0800c1c09041520720f000c00f44101030012090643c031103124074103956101030a1980500c1941203040f040c5c2002d102503c3c141101c00f50b100b0143c0c007007096082e004214000d40340d00c2040303212600074000f00119503800c10341c01c2c0039680e507104544050041c4100c03107624000b01e298504d2082100c41c8000c0600c81181848015103040e10681e001c10001d110342c4043c0320100d441c0c0c4401005480606201010302030901c40020b0a2603400e801240041c006410296110707117001400320b42c00b60700818141300400030b1843c595440146c422405116803040b403804609041c2420001d142c40d03034140c031899100f006c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 88331853 1250 88330603 88330609
    0x40614120601140d030207080601080a02040c05030f1b090415050f010c1e02010e1003050906060d051b060906030a0609050708090a12090503101407090806041707020a03030815 77
    0x90240148a8a00b0f1858516241e40c2080240819054800d0050303648090300c66181602e0a04261311a40322980040d0400096040c58884c0c60508012031820038a145440e01c025190244080e1420000e83d482c1d55001c0301e42d043d000152059100000c01c14004000c0b5100100e40d00c1d02e1038095941b00c1c4000c400c10399401e40c0988681191554481845042c64007080074203090390a003c0070070782c140508801c0d645085da440c55204104541c01d510300140c030f800c200f1103903460321000500c100d000f11042082c1c00c020030000201c01e0522501c0c00b98031058181c1420201d0390380d0041031450f540100740401400409000d680041095400842041000b95a0310800700c4400780d05550291580d000100c0343d10220fa101401801d1046c0c0c0c1d4185045405d0351032022900d071001d4204c203a50b215988155500c0e002409081d4190084002d1514a1081e810800442d4907040c2c0508010715590340d0001e1900040300100030340d40e5a44e00104030709511592410302404090044a290091800d200b000c1e000600e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 88333103 1250 88331853 88331863
    0xd0c031b03050f190b060c0303090607030605060904110d050108030417070302010801050d050a121106010b0708031807051306080d08010b03070e03100603050c09070203071509060b04061412 83
    0x81003910160390781e241d6184007800d606480ca60814243c0c0c64071181c44591321040001c0241c0171020b1f00565a030f1500344411410094090500c80c209801c000041106543d542c1c00d40d02180c504540003c2c24917044d412500152055903030702d00440c4c4c1400b000280401c0044003400458041402e6210040501e1032081d4480b90705000090100fa22000140880d081403100804503620403000c8412017680d90703c80d8a60801c110080b40c0008038140100e0001035002d026048c0100304060001d401d20850380c0d03d008880c0801480490b0442151084c40d526580420031000146005408500941045682580a88002c0c001c1c98042c0c850700d040b1941c503030f102d420302c14102e503001d1040f02c3c1180c488080c00c840000700350440780da161046000d8025000894031440008522840081500c10410380520440020080070f51007503420501030903001c104024003c100030b050380c40c2d0000d00e0244074504000100a07035030440d500946070402c045071954284e0b000c064000c0044038145107040d03d032440d4594803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 88334353 1250 88333103 88333111
    0xf060601020a140a0b040c0f0b180415030803070c060506030d090b09010504090e03090307050306040f021c0615140d020d0b0402060403051605150304050c0d0302030d0c031b0305 78
    0x59200c010050007043c80341c540c01c100b4010407070036960104556101c40b64004005c2c0e6055a4011081e0000c000c4c0300301030a40c0000a00241e000182081200d99410f403e40c07a07510340c030707501880d25203891100c214003c0d000740f4007956000c182c0c0c645905040301c0c020000380c0025003c450f021701d0308012840a00c4c0001e202046440141e46229101342048455940f5400640001e41401001d01c00480c450784180070758240d80501320002d589a01d085010540380164941c8428003d402280c20310003c581030072228010310b5010703610030240c030440c0c1c00d0240b4070910500d0083c0403d40307042d80113102030200c42c01e02d00c116804454070070001c007107020030050080e40030080290b1088890900400041520051580c042d000038141e40c00c1c0b85d40d9864060a241440100180e40304072000d0038085854002403820001c6160459036046107860707641e1542d541495120684a50107a40a203010503200b041154a2501c18070300c1440030956902c80600a020f41901d0018204038448071403460b107210b44100d03441 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 88335603 1250 88334353 88334357
    0x3100603020d15110c01020c1b060d0c170405030c01060509012603090414041b03020a05131b0c0b0603030c07170f0604080a03051b040510050d0e0a03020f060601 71
    0xb032140a40d82e0b0b0320718030f031503602103800c002e458104a1441204e020b025007005c0d01603000260b85d4031440014141860351020304094010308600212441d13803540400d9030007440d4032520000d8010924141916641801d0011100202441c01008100100800a000341c2401c2000900c5643d455a08000804609005510490704040010181034100305e16503608680e01e601a40d10781420030380400c05848004183c00403013030b822028041000503203940e024117039050540302003d45081d07500203001ca80c00e52042c10311030080182800032840d5142c1c019100014041d0b8004c801d62104000600b801c41c460070152050303504580002c02c036080110440c5c0d12440c0500107050300b40e081114071794410902e299109103500c9203406c420035101e410810180250301504189443d06038058000b403e44000421088011850342c150700305520a01042c0c409070b51b0f0442e01100c481403803440890b802d0181820f00c1c0d10141c2000c40c64041c01102185d0400c1240c069130036501d0300ca9001e85001c0d0341e10740603543c0d40c0c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 88336853 1250 88335603 88335619
    0x60103030f03180c1d0c09011205060609040501090c110102070c030605070507060c020c1201090203060402090613060f2103020c010e01050d020a030c12060f1707080303010308090310060302 83
    0x74a201e540303c0c0c005410390011180580100761200400350190741c0100c0d2043c00c0688482000e134900f000c49a602c4015041110703d021084000200502c00e00c240c40d40c0c95035158000301e4615a115401d842c003d00c4003601c00c1046c0c0da59600f82d140500305001111000c140715454241640c503040c000c840c0c8483e0042480c2e07640d680f40d80d4030311000303000082c030391800c02c1414001080040c2d00e601950886a234158014100c07a010030040100f080d590441c1150240e140541c20801a200407540d594041d40490740d0202e0f540d52031002c20985400c4102c02c2c4000da181c0000400e440840b9148031041d5a10300400e032880030a620100f03054445c1804019000d61b001e5181e62020b50b1040c5480d10789660b0604d4620704018040242c0701c10ba07040f096007500800c0d210541131000c40c1d40011076100840030140b00b482080e20b446090701c0304e01c18078015204c0038600c4604080e10000c0070054900280310a0b01225030704d43c0e40b414035110035088005220f1090095014140c0b19030f034240940e105903500141001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 88338103 1250 88336853 88336877
    0x1080a09020d0f0c080d050426061f1e0e06010c02031504051c17061f050304050708060c040e1315020714010c020d02210301210213020c0f06010303 65
    0x890f034121001c4040351990071034000400c03480b8041c0034084041e02241c541c2034455080c40090074042040340b14116200700703c17010b000441100051b0054125514264422200810491110280c203250b00070b0a036001c0a11828400d840c0941c5c3c1600c1121443e29001310315454034001101e110141500181d855840252502800803e40d20491b800c64855021900255103030340c1028020801c50301548040340c02c00a81d5000015540041c9910040445215694011008800910494030900b100c100007020000a041040821280d00a40081350445407a45000c8ca1254815071150190006004054004c03c1811650f80c40e03010301244d100c2c0c9411036200e9412010300007504034004c1520035116409041c02549000c2c8100c440380c83d204c3c2d0160405c0e94401c58007910b8420385101d01d41c098000890703100308030046032080d203055230001d860111080041c00602383d00180b4510029500c15803401c5001e8000c3d503143e00414508045100340d5507130352030400c50103845010901c4081d0214000107114 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 88339353 1250 88338103 88338113
    0x1002030f0406050a110f0c01050f010501140a230d05070c051b0105070209150a060c1101080703020702040c020c0f09131b0f0e150105030412210608060702010e07080c190b03041101080a09020d 84
    0x1500f040fc1d00391803d8082100350f180070341041002139100e141100c000041c3c4410311104c034041c05038001254200a40e022889035205542d0346410f0340780d4602050a00391154150b03103e0b00444800c50b4009201c007a40d400c03e01607900b8a03456500c00d4a115140200300014401e000341c00c02143c0e550842c00150541c440680190380c103450007000c040c101507080001400680c0d80740b01e00800ca40956005213005840c0c0780030b1005050079000e0b072a204060482c100028000c15140804107194091100700920f60045070540c4c440503d42c1148145160041c80811003075104a0801e11880d01142032050301030030140150313036501c02510050003949a034510420082c1c0a80c1443c10140900b01d208080403884168401c01c48081c0c2d00604680e810075003d215005030309009045c0801b4402000d0700c1240c0c40c02c480c003595441c01c4400140200e014a01c4a802000f0391034803d13009200d013500d0507a8138505450130305003041c0310345450707400303d0a204046540700002d4420590f4a943c0a013490304500305035180c4c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 88340603 1250 88339353 88339357
    0xb0d030512070c021e0102010506190909031704031d01080f0f040c0504060b090901050a08100f090f0f0210020c150705031e04081002030f0406050a110f0c01050f01050114 75
    0xb40c401c3c00000315600c00181c551054154034090380c6201ea50030105814002425560007078401840385e03200d003001440399100c1441da40304881100030000350420f6503140c02c0c0d0f8842c941c00704130440c580300c107003c100a154109181c01c007600c0d4007100600c8050301540044d81c04660640d000f0402a0007200010038030006403a54980080c0a08420201180d44200150503078090750000004400042480006420004c541c0f9000d014100c5142c11106d0800e80702a43d15042c004e1903102080d00c90140340d00b412426071007103030240d0301325041d00410286800c09121481500c5400c90240c0d080c03a140301480c41c40031030944840100103090790020f1016402c0c25460380c0184c24140c0c1c660204110309000300c00005440200700d40180b40840e00c8525118109080c03108090640c940c071401082003125030f1090402d810b0740103500c100005242c0d00c92807550f10007400300011440304030ba030005507084085e944202030041d8442560080c03007a5650303000321012417842842900c0c041400412031180d10024400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 88341853 1250 88340603 88340611
    0x306040903020a150204050102060907150f05040806270735060f10170606011103120403030203060f0d0215030c0d0507030603021005091305060d020d0501020d0b0d030512 75
    0xc1200d445509940b03910b0300211828103113001441e0300041c10045540c05101481d4040020b1010f04040751600031210f0a0007003200d0100b00308480e080e0a4000e0300e0251043c1d8000d88000d03011210149050148110070210302c0d010907011068100207031803100f50019400054800344851800a00c0310070042800a5400c0c03039074040401c42c5001b14815070750702044414410208482200c00604141c020f03241070652603003003200b02581d005151b42004000040c1c4940101084c64040c3c41040c2d2005180c8c11405444081c204640e001810b0009240c0e054003e9409800115a224101141001040100400004000d402c030801e00da0f828056201c1c100079641c016148000980f80410038912041120b000711402000702e50754400034401c5d410103ca040181c400340d400c0003403400409000046543e91301005c1001000e4840b8000b504a86620304298840b1382d018052150003181c40c94480c0c040c1d0010180101c01310702c0c0c02c031018898903260245d85400e58140d11030514141d0041034298580e48010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 88343103 1250 88341853 88341857
    0x8071d13080a0e0405041b08060403090b090a08030315011e02150601052802120c03090d1401020a09140303030c030403050304020a0b07150501050a0605090607060f11071203110306040903 82
    0x81d100f1180d0351124013034184210711401d0740e0303030881c202044042d290708403640106007554080e800b004002500b0507510016115000110b80c0c640e1304c1c1d40005030240b980368124030490b00002c0b040c0f0604ae0084800c020451900741c03103000d60151499005143c4043c507a030300e030f0010781c8241066606074041354500c80e084003040c90200e1030107080315641c2140c030658400c0c607641140361f0b0316032000c100e41c10700080000a0440c0113041c5085100300046550f4041c00c0c1100c2c1c400e6003100f02440c01c0014504208901d079040340025034440c0304149000e001e614152207a120040d4004200d95101d02d40030046a20a44a5611503421600c854600721015040180202c0e0080d40000c0c0100b40d0900200140542074400c2e414403100342c40502034141516810380c0014003840c90107000344840381c4c2050580340c41c0881524420344540150420001402d181c00005040a10340210050103648180c010036405005d030701403000707043e18000210211000c0ca00c01000b4800c090020460500d0240c0000c02100d0180c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 88344353 1250 88343103 88343117
    0x6210b120105040b040512030106090b1308010c03020a0314040c060c050a05100b120715120b120708070b070c0b0307021c050306120a02060d05060105070c08071d13080a 74
    0x12421580c01c4540c20f41c1d040d030f00c1000003030400c01040002c001c3c101012803007000a50071035142c00d41c01ba2804003036004440c20143c0c0402c80d02400a00902964001c00c4268002c1c8145455114054000d500507041c4d00002410040d042620310b4501849a00496000c0c0440007200c2c58440210f611101d05002261507016062a82d03010540802800980d00040c450000714010840b0800c03010003ca06008034880e04098002c01604502201030f081841300350500744c081d02400301c040c0e002400b545c00c2c031035408510b82c00c040500d2003000811800fa00c89050480e491180c0b501c05070b81c0c4600a50000400e04401080103020b607410000c0516005007690048070401c404100c1020101080060780f1800110301000b003103000c0c40c010500d0343e0b103a010036019248105950b0041782c40d80c41240c00345400561150041107550348100c04441901d5005201c0d40c10494486183da82c94a10502c1806151417409107408411015882c029014100c10741c0c850700c1503c2160340e04281e98002140e03001c284024 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 88345603 1250 88344353 88344379
    0x2010c0b071706090708070e010509030a0807031403090a0305090103020c0d030e010b120604061808030a090c15020c041a06040902041a19030b03030d1406040606210b 73
    0x8020030354051429a1203026042840000b940300100c40248940e100d003c41c138041c0580c0f42c2d001200d407604900c651410013072884101c001030320f05214044010307400d84640c120709014080004040c0481e284a95642041c207901c440e0240700e1400b09840d4000d0a400070b64a207000030340a4030003032211442c1810054104620402864100700b902078030000800d440b10100f0020001c00e20a586c0071038001c54180303030881542c0c91410780c0c80900800050505644a8000340c0300ca001c81411030b1516882704d1025902d1400c28240405000a031400700ca03541200113010441000e081c100908010042d401007040e03a00070010800a061011140c000454a0341e4a41c400d0b9160302d801800a440c3d0b200000d40d40b1032a02e201c00c0e0712803807401170702c070b0b003800c0240f04021100009910610b0324040c1e625020070381504510001b400d5114203072054950914040104800c05e8003c25064132806088404000d119961201611080d90b940380c11707111000d84116a000d1707901142e02241d88420060a80707001844 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 88346853 1250 88345603 88345613
    0x7090807060e030a080d0f110c0a0b041e150c08010308030613060503032b020f040302130e0d080114090f0117010603120801050310020f0306040c020a0f0b010f0e1504020702010c 78
    0x2028001040c1065147c000706030144013140240041a011844802d00e0715144500840e109d02d6042d0009040d490a400840c0901c03840d00340201401c0e0128a800d05007203c0352400d510462048015080040d00700165222503c1c005e1000504032a003110f5060729558800d4200f101301c0b002680700e80201561154046941c7d10108003810100100c0300301000b900c0d0210300241482500d4048451903240100804881004207205850459038195103c42c0305401d800d40c6c0c00050103a40c0707845010340c810b100f00042603552254a46040f111752680c000c01e0b490000c0e0901140d14002c032103d02c5004228001000415000d2961440d0403035003500009040d51030740d41d0702000340203041c488400105c03050300604c0140b4050100d550b01c4204d2403000c515007105201c0c0e081003400002c2c02107106036035a0404001d018024807001c1c001660200042020030001e00e802c0c0150b0100307008149040b521454003040d070202c444a5240150100384001000b25240740802000e50310208080f070404c001002c114001038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 88348103 1250 88346853 88346857
    0x203060a061a07020a35030a0212042105030c0a030302030402040f020304031713020d12030506011b02061c0e1b030a0302060402040b0307050a0b09130212040215040807140907090807060e030a08 85
    0x1010502465556230084802480c100b403144010000d1641084200107030381041c0300c0904106406000c0d160200e0395070604a045000720107501c011405207e02410405034150b00540c4203a108480400880011004001c12030100712001800b040403981185a100ea4401e003032607104e025003005180700c009560104800001300d000c1150400d90628a0b120030503098019198000401e01e40900c03145803c10695035826040c0d070002cad00450001030f1080c20408942c5a0140c03215083c001408246805103005660f4642845880c8140145580b2103240b85004182801e50b0303a016401041551542d4007007200520713802151961500c03400301c000400c3c0d12408030b24802030555043c9980c944c035601007840601d40a031070514004510400c04c8501c40c01c40c814000380c010f50191000e0600900302e0901e01584d04c8ad0380c0206c159880b07000400110902c4413030316882049010f4818207015101e590044c1c0d0441d03200d00500540d03800180c01840420700c07038405101c18410003070481d40c8002444e113408003d0303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 88349353 1250 88348103 88348199
    0xf050f0706050621011401050d0206070602070302100518070b03060d02040b120604080c120f0d021803120405040f060e010608070201090f03110c010804031b06090203060a061a07020a 80
    0x5075192240c802c0c80a42005c1450300600c8d055944411010060707000038070038451100020030040c0d02160b440d0605108100900e2088005d0400300b0083c10100081e00000b078101142d689e0314490900080307408002032060700c0c0031303000240004c0c00030501075013004060504000e240390890404500036100701420400d40e80518000e5515035036494040c0c1c0d41d6030402260040808980c0400c020224003110002c0c101c0380180001540140c0b07030082c4081421801c00a400550b90521804111101c450a41d00050044500880d401c0001da061014288141d502c40d10580720146400030040014038001c201950b800740051000017011402595082803599a40300180c00080e030300c08081408bc4010082c4010007582420419030394501a40d009000700034090b40c400c9095071405480c4100015070308031880c00e9900074291a11490164074500050400d48202c0104103150001142040203c904030f0f414540c0213000c00ba401401c0c10101011a1450554641d5007003440d0503203905406242c4a100c05 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 88350603 1250 88349353 88349419
    0x1b100501081b0603040201080403020f0d080a0c140405040c0903170a030501060509031c090801060806060301050c0a0801050d0201091d011401020d02190f0503030c03070f050f07060506 81
    0x8954186030915141049020215804000c40da801c1c0a155403400140c0e580b003542441c0400803596980b8040341050640d0600c00500d00c140c0c0787c2c41441e40e410015540c82404258400c0000c0d000032101100c101c1c203400804250424100018000b50a0a0308480c509540070f04180c0400e50b542c2c0d46281c0c030420fa062504003030080124401c0c40a0b640741c09060300502c110705d841d505100b201c000180c0c481c01206c2003007141c0001c03642d80040c2d49000b04519001841550002c019480e5601c40c0c2c59100c0008070b803064440d500c2c0c03000040d4001c40724811303a0012545585d4079070300f81c1e0030b120a2000002c0e0011041e0b0602401c0140054410715500080c9010801c848020045515164004030040d02c65242241550405401c61044550024008a52034000c0d00c5400b504100307400c10b1050441a00c402502d140000810000308040d1900194003841c0141c0d6440c5e03c0030b4441c101142d40340602441c9d0450703d001085a1004514190002500000c008140c880030b01d001c8c2d43c0091001100c1c0702c407140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 88351853 1250 88350603 88350611
    0x3908040509070503060f130608030703080603060612070605030a020912010c03050f1603020f0f1908010f140d02210703021203040503030901080901021303030801030203061005151b10 80
    0xe1410203000680d0028201d04007641141403402c0082e168074207600c1c0780c3d4000c1c00c1500c81d03040400031716000742c00140308403c280d0395500443d080041101104070fa01600a21400c8080703006400c006ea5180e191409c580d01a003222070030031904940d16030000e03002e206c00355000e002181c90769568000149020658000000341c1b035101c104041c086c0c034002800c400e61034154104000321070360800b240c00022942880c0060381c03907600315500d05003801986d0003c4902840032540d4a070a1581409000c03245100da00d40c0411aa80e036060740f0400c1000303004095450007920758500f030305e04101d89890600740c801000710721103a8684210b610300c0c0d4004100343c002a440311070b081095061013800b801100503024051841c081c01d010100340e40344200c101040c104422500013444510081d17060780d08100d01c2c44a80ac2e401650307130400918082003800140e11034065940880c101000007908042181e002070b02c07112102d000700540c1c01541d000b20844840c01c84501640c01d002003010711400d03a54000c407c000003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 88353103 1250 88351853 88351859
    0x110a0c0317060f0d020d06020301030b061503060d0609081c0c09090b090105010e011b06021e07020a0e1906080106031712150a03080d0b03010e0c01390804 68
    0x101800c07810806402504040320a00415888a00a8a401820642c1c106240440b41d10102d50400d8000c0b10242800e44048008020055400101406150210780c1801c3c5081000c07840340c03003440f09641103540400e8102d003103000582c0c0d503040003d00601581c0e0b102d00307152717001da05d002403840070500c02071400d03941d4000c000340ca5810145040203080e400f00c042040c1008040800c6c000360040c0a0a03052000740300c10100c0b10307882811503000480015400c0c249151840c54140040c3d000740b200c40040d100040300b0422f03200020801d844070550010603031b0381000e180140740d202042001c0e002d490004441c0300c1b25180d240340c5000d1600107042c00c10001500614600385080003101e0f0b003600080400d0100110580703c041c1d00403080d00f1182c01c240205108001000040e40302540d540001c04145001c601d440003508141d00c8a450803000380c00030700c20305030449003da0b00c6924140d2858041000c45145401000784c506012801818029088081200a0750040070600316050704a40c0c2050000d014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 88354353 1250 88353103 88353107
    0x21e1206040201020706090f03080c07030f0506070824010c03110304170607030203010f0902220602010c120c0c0f050c040501240e09150a030b01300503031306110a0c03 74
    0x5100400c42c510f0f1040700182010200e1641d08c4442c80040c041560208011901c50780038040303503000356071007c20604001c1e118540b9589401d000c64052003c110f1140000302001000064002020482c003900321080e0000f01c0107460040c42c0810507070401504aa858415041c00c00082020705070115201d0410407504c5a50340c0380501c018440350406005100420116120b20005c40c26507028000260b1242006010034a81d00d4007603103110a00403c002000401d20303019070191088075415a604e0010b104014800000d0f0b48600311043d0008200091382c4012036003010f440b0100d94880d42c150b407500040c410000301602c1d000c0e0003040c0700204441c4041c01007c5d00446d0b030500421182010041d40030180005400d540c0024241c103403141e030a2040e8112a9141d250290140d03501c06105651544c4035010f040a00f0202500b400301c0e500361000010524016111900446038008000d600e5956517580d0a56208a550b0040ba86030f03441d038180301d1794a0b110401400007144c0d181c0d24050701446038100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 88355603 1250 88354353 88354363
    0x106090618271118120a02090117060702010b030c010c0c0f06110f061605070213140915130809150a0f08070f080a0e071208040303030c08070c021e120604020102 71
    0x514264203104004110101c400f110328041c1013001150b21242600000300941c0c100203081d503000f588004c83ca0008a217050b00714049003200c60410044592070340c2c1e0b551007030b402c0b148030310f09565040c0d1015422a28a600c510412003420744144503074850641d864015280e150803507004100415826076503918954401c1202c0c2c0300b00310101009100340c0c10003921040c04407403c40f01000030000001880d106540315048905003101009408120300801c5c80341d0030b5160f02c0252844612030040e0b5144a0480300700340310f114040c40c0104c4104500015a40d079220349544200026070b040010a0b001c1c010940411010308900c00c0b090702c0e100c10751140800028800d02c030041c01b4800b44030044000d92484c2d07a2144809610042e008070020b9414034402200f40742c000940c1c8408030030107400c00440200031030306020340101e0348207403814084807485070810759504200712041c030009010068080051316085c51021025a55a801c00c2140010302c80420b181f501b10320070940380750b0701410602085580c1044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 88356853 1250 88355603 88355621
    0x4120c050114040201260f04060e1c09060507080d020703090e04050a020109050405010b090f0103020d1112090706050703030b040605040504081305061824070c0f060206010609061827 80
    0x201c58030541010682041b580c06c0141829050210880018042104551000c01c80781103000448500c44412a002c1c4415810f4090319800075483c0c100004003a0b018400381e80302150310101041c24400f060003807000035000600d041d0300300f000f10480042c0e000c0000c0b054034000c50180014080d03500d1240005000e000295100070f00491420004000407a410700594281b40c2c01160850013080f00340c00100c0280c052403041003e29031401c0a4544986c001200900c0c070441030560b003544c507540d03128510f42c03100618410320004c1030041007000e0000f4801e60103400d0b000402403000441907100c3c40410100d40e01120211100340000a40504801e140081c10307008060441c2c5103440c0145109038400207010b40300401d801150071044c00c03080e00703085000241c0a41d031044406900c4020300c2c104860010480c0c4591402607501c447c0100d29944040f4499040c1e400c0703a1201c0e0281e510f0500112030741d04280c001c84e412486411004a0002844140e4100708039645c20408490710500d0915030441d12111 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 88358103 1250 88356853 88356887
    0x405070f021207020a06260c0405030f01060303090e0c070c062f070603020702040b0409060222050d170d05040503090a0b0405091f150c0b010806090604120c050114040201 75
    0x101140f401641c50307607440001c0e1691403820b064144984420180414448682142a44400d03000c006041560b00054812918220119400140c43c42c040e6401c8440303030300028000540040d828007041400784041d0340c01101000700907280000d551514000c058040d01f004000840c809200314850712091014011012600300210072900041a203d1340d8141900c2102d00385500070411800b55079031980108040440644207103c60200c1d450050020f51026181d400c115011103003146030040754102103801c3d140007506000156400361185010044080d640c0e449419003080902600780c0c02d07000f41402244200010350311442d103081044079101940d044010081c806001c10882c41c0c0d03545e41c84903001045900701c101d03108046916121240140c1d04804c108481030340c810b1035600e501a511045260207103d040035283d8a03103c1160703c03123109503910030b01ca5024001140104441019a0030148518207000025902e20303a180ca0035194410f0342001c80b0140c103000c000a42d41c22080400210410b2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 88359353 1250 88358103 88358107
    0x203070c091407032c03120a0c03050108060708040b060d0515060306091f0c050f03010609030b16020a0b0601031b2703080a030207150207080702040e0d0906110c0405070f0212 77
    0x4400c4c0086850800c4180035081d2684d6228a01384400c1c001c0b2811098000c1c07c0101500d00708503804094241c10950100181c50030300005401000401c440340115500d540d844000e484031f4440c151800710290907154040c90943e042c4002a80c20021040740303400505070500d0741d251034000c260608100501c00c3c0f4060300001002c481c1e0403441102d101c0042800390340081c04d40301e6100304403094040c040c896550000000000329030660040d540c00120780c400c441201315561070b082c440340c107070740101c4180c00580c0c05070340c49000003a10701900365804003061400140380c1c45020045000304415a1000000c034400144014510706030146100480f00810010100c80e86103a5844266208007280c4034101a070205031102005172003d84510102e248900a5446400303c2c00e00d910950701c41e0604070701c40c5282900a0000140226401d94000c030aa1901511a031030302d001920101da007800000303950700903040359404a54943c42105c1c0200340342d036900b103407203840048081d1070000c250548900040c01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 88360603 1250 88359353 88359371
    0x10b0105040f0e040606171b041b081b0307170a090803060d0602040504050103060b04150302061903110309160b04030203060412030b030a03020d0306090603050d080402010203070c09140703 83
    0x50907140d07403c0303441403a0f180d5526034030b504052004040c0c0d6000003c6401c40080794056940c0b0010b520490b1a0901c40c0d061074400d10541044100c3d840f11142c01c0400304410446c0c2c1c100d901618460303170300c80520103c11703c8052106c06840310a9108440000109803060182c25405800041c89540701074120b904000d050415205d5003c203010040070039120f070846205c500100310440c1c040e00e0090001400034040c55840f45085000781450040e050302461a00014010032417022681e40112900a0055483c03c02030522040b1001c01840501003490b0310380b00c030500010340343c000840c841c1001c44080d00c0b01101a84aa0315641510782c40520b40351000e00061000d030760040f4410707030011b501041800e00c0c155188000d07000342500c540556814004c202d0f074042416000302d02400300051950381002980c6e00d806100c0112070300b50001404c03503403000003400000d9004000681d000390050048a007005c0c003960322585003112035000311214070b4450001200c811a150020352304a01d19080510170420 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 88361853 1250 88360603 88360619
    0x60a151a0307020a1a0613150302010e041104170c0a180c09120506010e0109060303020a060902060906030a060e0604091a0705090d0303140c0a0206070507110904050109020102010b010504 82
    0x1016061086800300000424941c500801c0f41c01601d55001099400684003078100c0803036804102c840740d00511804000711641c18a82c410340d06000c03d0500081d42990558004680b00d03600d01348801d402c680d90b208599407440701319000c1c000800b03106404690681c0c10743d8069040120029469016101085050040c00c08074013030012640000c10700000c1c0041800c0c401c45203030307006a00c1860614000c2155a043c0a00402c8044c1600e91030602c00a150740d1381c0d400a01114024400580160060780201c030008072140c201040c41d0303000500340d90402071000009441d42e801580c49614035030b41c40c24200300500040c01c1a41d41715804403010130401c1d0341600c1c1c40c5100200c1c115a1030050501d180081c1d850b0340a41d05035004480064504071420341c1034070340030340208119503800076038020807030015025000c90001c17903d2147c0141d01409039a10785841c00d40c0d87d50400502207034062070410b00c400c20358070b8140030340c0e124a008000201b0b9201c60340c000682115542e8060504105e010413051040e00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 88363103 1250 88361853 88361879
    0x1d0103060612230304030209010308070c0608010b04180e072402031312050708061006030b030c0604030803071b060f0c0801080c0d030e06030702061f031502070201021905060a15 78
    0x1c03800250503100000750f075450390a5100d1900000c2d8013244140021044c02150006003400600c0703a02001c888070381b00c0100b41d400c483e0901c180d10032040100000e024103558145010841c1364411404150072810403d510700f000400d8110018101d049a4618000005801c0900c45840a130026500d02181012009619452405041c03d040c0002940b01c003048010080d40000744101c2080c1c404605014007580c4408089204540000b070a11915800034a8017003412001e8410003800f03540740c0303071030740d51120740641000300ba400a21645000071132105d800c100110f0425403090b400022084010580030b0110340c204a42e1408000b43d80005014404001561450380d034001c451900d1b804d0010300e001c0790f0140c0d08078620350b04100e010080c415480d400042c528000c0243c202c441c65216070104104480c1052440080e18034a0313903042045265201d41e00078441c940c01031040e980b02e00f1a4400240b407905403290200c40d50b502903410026504218450f95a80d5030040e54141c0c5650f00d003d0000102e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 88364353 1250 88363103 88363133
    0x30d15030203011d10021315020f07090e07090506090a1508070b07031e12051b040b0d050f040305030a051302030a0b0f0105060405091b040302030706050703020c01080609150402041d0103060612 85
    0x182c070b150407003001040c02000100048082c04ac1210246502c8002d80c2d0050a10183c00d034500e44502c04012a0864290048620a11018040b140e60f43e9980f55a00050804103030149000d0000042c081100001404444040c20103250f84503a10112458000c0811208459060072486030341d4503040815445181056012011900441d00b5180c0f00300c2d40002c00c80350b110000815100060000c0d10120341d802400500b00102003c00140c1d88100201c40d100c035040342d0003000500e080000619014a6034821500803000c41c1c110664007166034046031504c550b04c00c082d074429009008116041078000110390150030b00340e0309c50342820715000200309407090240084000035143c48034000c1c080e28001c1691b00079500141251403172030341c540c405400760b440410242c0050040c845c0080e010f500505000d8051100585401c03060b55514003042d048010001102d5070198081000145a0300c8280c1031103003841c1070200b01c10a035451440c00001705c0300658400c9500d04c996407082e0000c500c240b02da07841c1c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 88365603 1250 88364353 88364369
    0x1091803030c140703170108010603030c0605040c0e0c0702041a031002092701030b0703091104020904090507090c2d140702060f2a030d15030203011d100213 69
    0x3680d003140161844000e50740700303420920b40413844005042d807050201c4442506140300b01026601c80c42c281d401e83e0320900001e80407440c031980742e200107040b984c00160700c180500d0075845141c0d03c540c800c064414040c0c1c1c080c20f00030b8020070940d066141c140f03e00d41000400003a241940c07408200402d4442c42988050a81e076079000c607003010182c8555030286900f40500c441c007006130352411500841c00c8400e000c240c0d904400300000641444c0a032085888150700b0600c0d2105002e081c90400002e90b01561105401a4540a5440010720100048405003461078004500050030b206c0050419039001c0303120140b51443c0d0902c0d501a08011148481202545481d000c3c18509116800103072103841c0009402049c0042d0391822271401c0740142510103000600c0c00c4108003840500c80c20a00b00305540105508201710300c8840300c8007948000d4001e05130801c080348840e41e90300080d086404586250b0788001c103480701001d02e010b06101c51403442c150800114145009003003001000207a600070158 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 88366853 1250 88365603 88365611
    0x10206070e04200c0d0212130506030a1e0e010b031606080606070f0c14041e02210c030103060c080112020d0201030f020c0d02070503030405031005060d020d03080f0109180303 77
    0x10035100c0090000f1243d03982580655145200000b25030343d82884010040103010342d44802c02c00342407131421501d08510000c0c0214025042c0f804000981d440500510000707079840c07540110250400300003d4150007500c0d800950313400324180b81420f5401c5410000d2003900710140c00d11102020348001001c0d42c0e050300e44400f0565070103001c40d82a1181c6200506600e05a0800b07000700461040c900c419241e02080cbc3c0e84a035620710b030a01c401c0e44c2010740c00d40741e01e580701d00c14840384e01040d501030092004c07030380050710f060f03d825900003000000590712903040900000050041c460640940141426079184c010034035171414091118505081c10300a01ca0a1580c00c44800d6a100303409c00300100d45d0102d0b046603076500010b078081c5d03604000c1e400074002d409039060000301480c0c0842514120b41c8082c02030316070301c1d801c1c150344001801c00500711740e881000c0310352400250722071000d81a4060b01c07a84940c08a4101102c88940d02141603014500003800d286010003580864000f901d896030341820049 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 88368103 1250 88366853 88366871
    0x2c010c0f06060335030903030403120f020a05120708010e04120314161103180613090606020706180303050a0c0213050903070b0f090a080d021306030e010b010206070e04 74
    0x40103030060360b1000e4000702d041c130414150036071074603980c002c421800c0b807035410700240e240701d4001d0500045488030202e4000740001070109001700c642c0d01c421a0f1104000491080f4812888102c0c2c000f01641000144081150300c820318031030140c40c1e0850300c03504049100d589403070764005111400500c010a003440101e08405424001e800111041002885551701d0b460f0412a00d0b803d00b114066100c000340d80d0a904480c07940e00401102c2c40750070740004c42d040c0c01c0d1081c0c040c0b2055900003c24204c4a5011042c00a07a14002c0c0c81181c018000329400307001480d290940041c005840c0000107405a00724410400c0042d400c007080b280d0f420880e003098400060540005050760800e07101d280802c03801d0108018102da000b000a040307075841030490341410b8071404850350130943c0454000c5100d501c01500c0d080420a59409800381208040c0050318107100c0c004043d06513401c503405100031030b0303c0703030b0b10342840c10400c2c02507280070705081c4020310350317132400c4807004202c1c20a140013280966a154001c3c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 88369353 1250 88368103 88368113
    0x90a140c04020d0b040506040c091a0903030406030507090b0a05030105040c0c0f0b010501030e0109020306040305070203030d110307030b120c011b06060803120f011401031505102c010c0f 82
    0x100c00040c0144210b4403400786080060107005401152032140f45010000740e40c0e4a402e210742c002114060741c40104a504204400801651302e212a45d81c0ea8024801c1c05c2d6903075801c01c020009004a940e0100e074a08000d070002d446003110303400c00380364400706120513483c40350301c1000d40f41180c0c0d04130740c0403130070305a0207000b90b03a0040c1800d00034001900c035241d58010b100322181d80301d04a80007a0303010040f510307808020900700d40c05900000e60580040d8003042c00700f03110f0005020168002801d6a01c5d281d05400004101c0e5840302261300e00410100820002580620a0765202c030016240d003c0d00300c0c2c1d4031b48001d8840d07040b05a03040c140504020100400012440c3c2840f0307081e400b000802000340c43d448001e80d2a0013034007003068421090b10002f048120140c0e0301c5412610800151780c0103014080064000d00040c181a40706120711040004055480e58a07501c162a907640321107a288002103040d040a0b410325828840c01001c1100176140359034402c00501e0181e41110741414031140d030780b400e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 88370603 1250 88369353 88369363
    0x408100b0f0301020a1e1805040507030b09090115050405090d0c1106071a0105040b0a1208121905010e070e060c01091a09060a05011505031506040b0c070e090a14 71
    0x307002c0d0558070102d4a04a010f410050b2506118a411182c3d058203c2c01e07001203885400c00b480070400300030704107400c028a0410b5001300b9008001c505000c982c0144000110b44d0480085451038035581d160110102401d0b000f80000000d0801a2030600c2140350100c8200d595a414401c010b0400a02d00c000703800b0300001041c0c4982e0441d00a00f00e030b58589403130821084454130b4816180d1a40d08000000880b0710b40740c03094407520758000d841d0160191070a0303203520480c001d5482c00d0b10502410458404010124400c0070321644100d0070301144034080380d042d5401c44105070010440b40c0d040304103210100b60454048204100121483e0b0f5031150411040c50140c0818100200150045088011054a0a80401d101e02d6a080440300c440e518a00c403901911800e2064070544c503120700d824948144140300466001002c806441c00702c0c1480f80100c0c0d0746511a034044200e0b40b07000314500f07182e01c0041c00880010102e07401d48002c10f050a004a80e1503c40001c001808a0a000385442c88039409100d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 88371853 1250 88370603 88370629
    0x812060315010816090e070b180303070b01090f06050a12020102070b0d020703170601080402131401060503060102010c030516050c100603050c100c150b0402040b0d0605040e030408100b 81
    0x1c901919583d91001d182d030380c80c1c44800c01c180a60005001060201d4184102c00784585500000c00e100c52404000d008158020f08000704200300d607000181442e141040244032403440b40f0ba03880d100c1d624220401040b036490100101d4002c0c1409020403903985c4566000042e100c16a200042c030030040c1c40180d02c0c00249502003002070300041640000b100580e40035011b00c502036225400c3c2d810300510001d101081c00c503034032800b0a09410108025041c41210a000805040000a00c01c00501103520000c00c09a0285002844c000100105940e0a0140105454103818140083e081103d00306100c0000d4440c1031007002004100102d002070b0410034144006400c0c1c404200d0f0319120f00349a0340301c0300e994000a0040140355008690203110300031540000341c02443d0b80c6641c02d004100080603001c10314100e0740c415000d0001003022101403004003c9a0f692143c0003030420725280502064907080d968000480d0000d000801071800082000030007010700180000703a001040f000078441c2c141f030031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 88373103 1250 88371853 88371883
    0x3111303030512250e0105270f03150f0c0c0f01050402121603020f041d070602061e150f1003140c030412050304061b030e06010503030c070e0903070b0c19020a08120603 74
    0x1030300c0c445040341c2d4010341408e002c50540b0821144140101031659468015229001c07074580100010b003446022036546400c1010b00c01c54a01d8001b000300c881d4640002c100407580c0790b95481c0140021031401c1e0b011004485c1c0c100002d030124502c0c00707006008900c400e1001a02891041e010545540c0c0c60340c2c0451000240c0c2043c1c40d5840c2084c00c80030b540d80e017a81c020318000d03100300004a4009907a0194003401d036030319500c0e80100f07540c0300d030344801d40e00801c2c2102c0c40d048405049403400f075a44010300c0d120405000c0e074001418507d615055512504003030184100110200144400b0400500045440407600d080c2907a0740d443e030f860f0410080400141e0304546d01c1c2c40340e14119117180d158010008860241d41119210798940d070030503840380318655403880d46030701c244000c1008004030980c40e5400109101070b241000a02d03162000840d40c12244049200000240802d081d401000c41c080150a0341c401800c15240c90340c0c584045100780c802028030300350150001000d43e6010841c00686183d68 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 88374353 1250 88373103 88373137
    0x409020901030c060f05090a03080c0f030307020307061104080303070c0c09020a0e03010509071809080c010e0f060f240d0f1101090614030703111303030512250e0105 73
    0x7800c00140e50788813801140b001034440c840ea4107100e40309406498a900000304028041490f40d6074400d1107074005502c0921a0044803e052040b02e801d1010b50b05c900400d4014564911641c80e0440850f001c1c0c0d055414050400d10090000710400410f803984042c84e0b08200e030340d8140a00380142d10510039441843c01c0b500008040305a00d80c05030012201042c180d0080c000c5031200300b03410740c68540c94040d420000c2d070001c054034005103142c0c00410480e40205103861a003001b00481c1402e50392045008601544800704140c0004010011240c0c00f80c074284200d52541040c100080f03040010444907500e5940d0f03100094043ea607074000014160b680480038440569052170100650422100b030903001c11840a80001d0003402403002c182d40d02a0310004610f1559607208c03e6009000d80c1450461400c1c00740301d2886081d2150820501650180c1c442c152201c0134038149800f0088003c08200d02449140b0a042e408040c1c0800250400841d04144610481050048506008a275034540d00507680c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 88375603 1250 88374353 88374359
    0x4060809071503090b0108061b030c0d061e0e0106050d090c120b060a1d040210110a1b060f0203070213020918060f030c060301091e110a080106020d0c0206090409020901 74
    0x1580c1301c03055080c8182001c4000d6070b654001a5107a020841c1c0c03000540350319416406080c0e40041c004c50340060202205414001c40b24040c9044501c550481d400e09020301285c0174082104081c180000d14403082c528815606202c0c0040160185030540e51a0325110300410040100c100c3c280005895007542c0000502558100001c181400b03440e640c6c09a0380900000ca0040444100300c05846c1007083e050321283c82e15420311400041c50030303030700c810040345083e100c841410038044200d0103070060700328501c04e091422040e240410f45510040c1448030044000329102c3d0040140d0b2a0b50ba0111204006152460700c28000b0b842051916540301005000031000d4100c41c003280d6000c1c48081d540a14401a1001810340c1c2d0301548007105c2d0b000c0418001007240b88020f80282103402c40a4201168491000f100c1506858146031880d2141c80085131544045034865212401820fa620043c00e1650003001c0182c080d0a4010020f40550030000740003c00b5251a0801c9108503409080004550382d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 88376853 1250 88375603 88375607
    0x803040c2102011107060504121502030f0703240b0a020c030106120506131e0809030a030507030807020d08181e0a0201080a060b04061b060c0216061103040608090715 73
    0x3407101d034200d004c40d0704e080c407594103614001a100160b60300c60b00c0d5189032604000792014410030303580341101c991524414510410303e180c005580076001103017691003a07050461001d000d0b1880d0030283c11103d0044880308034a040c0501d142e00494020850866a03180e24400032800e100c1054503158241d82049d0001803501043c100340702905000f1300c1035a005440344103214850318811a80605070f0701d0380d2404200c4074003141814038003a03807140c820700346000520710103c1d0074030396156030680101c0d07004200c01052540107601d5980c42103183c406010840c41022004e040c41102900081a00c24003401502040204010300c403070b04007080421814030119128100c1e43c90200507401c82c0000c0ba4003000ca13903518983d00900d800c4c0d5500001a034203060900b10100c42c20380e08a01004c062100c04000100403901c644501e507010030341980640038076030b00e490030b48418041030341c051380400c400055100300c1310002005960a03900e241c0340140044d01d8640020b89014001c1c2c006c480104c1c000309805000035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 88378103 1250 88376853 88376909
    0x1112010213050103231501021b060304080c190c03060f0209132d020d0c02060106120903030f050411040617030d1104080d09050102011a010f0c03140c0c0301180c030803040c 76
    0xd0340c01d0303080f602610729040c0502c0b89400249d14180d040841400410005030b200c03006032010304500e208403003c04645694a444c4a19840b070241d41c0521814010300501c401809818403004400a0562400d00d0fa00c0c00700d204440001d002c5140340d0f5441404080b10805203480369010342e10081c0d410303000261846079500079401000282c1c0e010345004c034035941c1c2d60300100c0da440c12224181c456581581000d8408006014104c408508045e540c030042800e41442e40305103400380c2d024071000002110b0340e106001c122409508a080e945040b206030200f554400400c0302c0107220031130404121a070003064403030039600a0303400c2080c9501841400b030300300742c1e400300f003d00c101c4200741e0003031066842d501000a80038146002560000e800140204215401040036900051003031510350202c080c54450003026400c801d10b55400c2d40c12070140510240b800f4003800d0003580704000b0710000540942d8527a4030070103041c40020042c240120000701480281009600203103035400700c90b103903224030b4080d0440740 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 88379353 1250 88378103 88378141
    0x40e09010f09030203220e01031a0f0c090f030307020d0803090c15040e0601210b0103051e0f13080403030c03260112080c0307111201021305010323 65
    0x1a40c60001104007404290103407454081e01500a585425100780035001d0180320141040e1000490f1180003412030701c032130602402580a100c41020300008940d555076010780c0502600516a065003d006501c80e4034003c644809400b100c003079591601100100f811401400c1c8080e42c1300c6629500386041c452508000c5210300b0f104025640440807080030801804240c3c1d00122802c041030005014030403400d680d090b000381050405034038007011900c0040b00b450071650006880341e203908a84440756003500415810500c084440000780d1200f130a91480e025004006400504010000c140c22450400c401c44405401c4001c059550b5128280600b0340305401c00114006100c1e140030186401030b41d800441804842603c9091991030807034aa00074145003801991441801c010b0401c0e881c00070402003004070f200740100d6900b10002010000700388214022502c0c680d0042000b03001201c845031340c00099070b1b02404c000440d81074140111601c0302c81c0d0703941c40b003841c0c80801c1400400c0b80340c2c90803080c0c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 88380603 1250 88379353 88379371
    0x151d010302031c1403040201020c031e0d02071203181206061a1201030308090f100e010506100c060c0c0501020d090623061002030c06010b0408010f05090307060908040b040e 76
    0x740c440d66035425840c400c3c542440c0000500348404011002414100640c6c0281c01441110300606080001138108102c0044449400c811101500c00a4500707020303180015200d800074101c02c030318000c0e46840b40e180c2e004006080000105403070031b408809500050142c580e07025440d4102c4014948140100018060b07102624181c0712000d10030f800c40007c54440104440c14580140d1a540e02540e12920103800c3c0702c4a40620b905294401e0010080e048005000900104002040304003850840d103024003198003480d030070291941041d030499013500c00d8650040b80000c100950310401c4035003400142005250b175000080c0101005aa070304148521401a5000c2000092101c1d840d40d001604501c113180d00750f01040024002c1c68104400e0034081481e00640e440e0029071160617003040e0098000346080d5001143c2031261180902c41c0c2240c00302d01c1d040402c00c07420a80b2003282d0301c0c051a0307030081c00c583d143d4ad200ba0421282800b510014401c1c40c0b581c903250b5407907500602c5058002c0b00d807444 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 88381853 1250 88380603 88380613
    0x90203041a16020705101709010b0d05060a181a0604090623070302030112110310060626040c050f15030c07141b0d03031514090a0c020709151d01030203 67
    0x171640b800310703901c6080344810b44500004480d0b903030001c0c00384080180148002d5590700007102550b1100d6000701c101d40d100b200602218500f95520200b16001e20000030621a04603030308400203880f00c40d190303a102c00c141c40304080c3d80d40d80c036001070090014503500514442c01c3c00040504445154032074901030303550101042403542c0f120000c40490000340718100c906000400c0e030781c010900c540d510b0041c1407400750a0f00d0f094a4200c40210988500f0740c0440006110b4a81e0300d1162400c001001006c20045501e18283d810310b0b40790b810700b0448500815200740030f80058424256075401c0505504060780c031090392645882ca40101d040d401c007000698803ca007040c1e4010b0381c080701080031440703220749000110407403462070184170704030301080011414946e640300c04c480f11849820200c0010042c3d001642c07205d080410511144050190440c40c41f1401c145c0040344550700409d011047d10b40105002504041035440d01101082e140d2000c0103203a010300c03181c08603000582240b81601e000307800b00d40d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 88383103 1250 88381853 88381859
    0xc020c0103051b070503090a0f030209090309060d0506060c06040506090c030106050604141305040827030607050a0203040f0e01060f1803081b061503010c090302010504090203041a160207 82
    0x140c1581d100f00c031002100c518032104030851011650141401c1c030700950499062400d1900483c89081c80d0307410280038440e1104040045103446824964000d15200c0658180b01012000c24218000c00850028542e2603000103a40358544d042a100344080c0c03031045031890305082c20100c0d06ca01050f1502803c40c040c40354a0312050905020b410304848000d8161807810340303001b50401140040070481e5038017401d10240d007041080305005040c02180618001c507a01d201c0c621642200800c806440140a49213143c1b456459a003c0b9000750b000c07186041890752400075910407030661040f03800c118031210040c100800c400f0100c0422134180d401c5070316030041e41a1aa2010359200003900840402e0340c000c001e041c40014030520103000120907000000140400b984040350a11000710f55950311031000f1610a41a45400d0144001c10f0402d810001a01400c1d070300000e00c2d5118a01030003001540002c0400c08008009a0b440546500c800044d0030f1810400c50414607034403d50021401481034003004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 88384353 1250 88383103 88383107
    0x31d01090506030c0a0318050d08060d0812040501020f1611090c04060309020612041a0c130b0f07050613051b0603070e0a0503030409020912010603050d08090712060c020c01 76
    0x56034401848a8211384c2c0300255070a566105403030071002c2549a102c43c1c1c004540303000681c0025803050004d800240804480101500c0d001080c882c07246400390041808124070400711101400b1100c142d40f419600d6040260191066515020310f480e00001c5000341880c5100343c242e0102e1184010380740e0b0480441c100b01400c50162101c40c0f21b800c041004011140c00303540b00000d0284007414042c104480c1c0f64030506903840480d4203a038480d4601442da0301005c8045a504e07030051a40130640c1c1030440d00c02070500820502d008543c0070000c00039404100c90001d2050704ca02c00d521401b10b41052910094900941001247c00c47d40741c0702e410340c0000011009903480840c008080d00003070560b941c1c110110b482f95940300325241c000c400110080b80c10345050006102030402420056a180e5011701403010006a0342c1340740030756924061007800081c3c0080740180c080f008510308000035868850006060000c50b60000084054051400d0708010071500500c810010980035125403032030103401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 88385603 1250 88384353 88384367
    0x1020c0d0b130c0b03040303020901020c0a0303090603230c0406080c0405030c060d020c1501051314010b2109010507090603051e070201020d02131509030c0e130609031d01 75
    0x204150114400100891040d40d00005114083c104801500355034510750003050f44141c8040c4c000a4000850084030750701044030310a414029100c0031039252440e2801414610039015030b10030140c03905462000d000300400d0300000450007404055060500004170440c0d03902620134400410382c0c0600143c100d81c1550150b500710740780900585a01e408003000c000e2107500a01e031209180380d09000c5104150720400541c04c03a080c05006050b16541004100a850745d00382c544a0b440c1814a100050b54290400346181121403012100d0744600d247e1000580091846201c01c03008441c105c104000400c5c15004940950602d8591281c0c0365282c010440c00e0320022030350000b2a07004880f00d0202502000c1180c0d41c880980d100060034884000400e0050303a0001d04070091403030450f242848040f001e03031490220340c8101d04044003c58a9039407894915002489201901d03400000022040328102c01c502c2c6880380c1c00a000c2020400500c5d000d84a40030b45081015403103c0302c00112029405040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 88386853 1250 88385603 88385629
    0x6030c0e04050703020913150902010210090305160204060527100b031f08010c0c020a090e070b0c0a0b0c0c0d030b0112091707050f010513020f0f010306051e01020c 72
    0x201401c1c3d4241103400780130112501924402e120510051200e01040420840c22500d032480400810503070094000289081068421120b050749001010360009810100712402d0b032083c5d0038058000c00b01d500009000b0b004a03848650070204012090ba1031180c00e0101241c0b01e031030340c000705900e5201e1840000000016002d00c0741030748410004187c10140741d036101d00c20f6004014402040c80c1c2c40d1100079080d51560801c040c0400c40c1e140c42d0f2011071500203a06800b4115500040104034652034915a07140300620400e4015600043d00c01c1c25420240003882203550408a915003d08000303882032250340c890810000c40f8022011420f0090b4803a003e83c00007914142c1d034551040525082c07505c000c0c4048400ac60f21341c011b1011520860725428050501903005002078500909a01e084030f080d10320081c40312a0032160304c0c16440050b03607803842d10107615200303488803840e49039080010307401010150003650f80700c0d541001c03c0303000344446413290050f04c2082c0d003940c0c4248051414810390303001c500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 88388103 1250 88386853 88386863
    0x1e040b030406050a0f06080a030815010f080c07050706260f07050f091003020a08010905010803040e07110601081b030a0f0204020f070b0c0a14070309061206050402040906030c0e04 79
    0x1007070100c1e8040d002160070034080c80780010040c1500c03c0450440394564889083d58008802e030b64140b581003800c56a005010baa4404035800c80f0b600000e100d0380803003250105001c1000c0125107450180800d440c00c0ca88c0c45400c41d0806529024041c1040d03030400030b0124a040e4182403440c02c198010111070144001c007102641588400d081500d0301d170070550000c90005400d001d640031940d00d0120b19818407441e52401691950100801000b800c0142c2040d0007041c00c0800411034014000200d6049941d9592a0396007a20380e22800c403440c56501d84601303a9441802c00120750004013007074455000b420000b280c00402420400d05440c0c840b501c07009445800807180fa00094206500100840022820f0702440c140d00d56a0b030401454060301e0042c8001800706200b40516003140e903820b012482da03410141000169130b001804100240500001c00403045400000d0031a00c0d0450809040010010b6407202d4842e007080c0000c00d000d12040c0d0702d40002c4500060005034191800780525000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 88389353 1250 88388103 88388107
    0xe09030c15090a0507090c0305060907050301031104020c0d02100f0c0210020d020f0313060f060302090a0c1b061b050a09060c020604090e030304030305090115060315080609031e040b 80
    0x140384150012903000b0800105401412200400900280480800340014400c00640d0114131400142120402014180201c1d01641482515a0040117690440780e0042031407210500b5800418068016446280b2080c45200040c80783c2d95000316500003030014003001080b80000c154400c0068403205021500540c000a4001800510703d400030180c1c00b0380c0c840094a40001c4410022159004403004182a4400c009410801c28207004134048424502420302ca040e08603000140040c4c005071829480319652a980c2d181c0d940184e10188108147d10400d8000701c01c81e0030008050407201c820f540b4100c3c4820300d140400b500400699140054039558182d40600700003003602c01c0007072108180c1e4828424000028800a1400360010040000000e143c0300d09042c50b0150940c1e5014243c10440d904122803440d110050303010841c00c4170140e140101700c02c5450b468003180d4044503005488540107500401c240000000018001d03515408803190310601700c942c42c0a95801a805648601642 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 88390603 1250 88389353 88389373
    0x6030e1204050f190305150907060c1101030b0d12020307020f1c030c050c0402030a0905060a0b01080606090d05030703050c07060c0c1502100c0801140612280f060e09030c 75
    0x7507030703803100041400314080e007191700c070348070340d0b01c3c00d038001d003007400c0441c090070410401d81c0050203500003c100710300700b042559031150f481c101c503c41c1c4800c8c03450402d50f8900444005554000c641a20345800c6031400c0c1040e103c10b00e0080d03c030b0380440420380c0240d8085400d0509400c00d10310078412000300f071200100251841e0b508881c00b43e505041a1385901c920603079202540d640d48010b500a09035008000365071300391441d0460502600a18400c2000d241c81d0b2112180d0740c1011410394480350440740955280700d0a00042c007100d03589100507215200110701a001c00da0040e008007042c400c3c11003180c06480e610342d400c5802c0c00600c000281480031422081004410046035405218a680151032658807000e07105006c90703088002d80303400600a0300c01008945022040c2030070307204040d40c4151624402c0401200b0307a030f10103066013100c00002c54940303410b0081b01d0590008070408800a005404405000c01c0150119002d9070340c2c501550f10100350030540c0081260946045c001c05041d1032a2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 88391853 1250 88390603 88390609
    0x10c11060613050402030a14030301030b0a0b03070b13030b1017030c03160303060b0c0d1d0d020906060715050103020f01050c190203190303050a18260706050106030e1204050f 77
    0x50090030486c0c261048607440c40c0082d0907040e0524070300b840440215140d40c03441c00c00c40800740c00600703c44943c510701402d00a607520082080c4044e5118140c0c92a03481081008038a5107c80c6a80701410aa40580a0186289a0602e042c08507101c0601a032081504501c1003500c0303225143c4013046c66401005480a400e075010149540c09000341000104160b40300c2c18514241e06c1650080000d411110b8504001034100d00e8000d516015481c48400e03d120034400704102c40c1a045000c0e01c134401c0c034400100c035503071f5100c01c9403000703640400f41c00c40c101403807080603001c1c080a000c200d1044005d168441600d52242e400e07215600f01800003420703c9500e0b44220800c11010080990f014010b20030341448440f600360310309005901c6035030002140c2c60001d5610044688155608807108880f2000c0e50106080d1804111035001d00c0203490f40454846c2000c0f52244100400142101d08100001452580660051b0010600c51084d280070003100310340e101c070510542c00345950004c0103c07a9144981 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 88393103 1250 88391853 88391861
    0x30307030c170409020c01050f0903040509040c0902040602100c02030304030c080304030c06020c030901020c03070f0b0a05040f061d01140316050f0408070612090803130203100e010c11060613 84
    0x140030b01481880c18408800a01c0c0d40c0d40706800c0718414070740014945090410901c24903510162090401d03c2500702048034a450344160301c0740d40d110b031310f8103408201440840600c40005084903041103544955404000e900e40210000c240986854103028600260000c01168850380d4566151103a841c032603590070056404c064019410401840840c2c800500306100910013280750000454950881c040024500045028086d000381c100c040100281c50705400403400390707a403050302e40d0385950324150100c1d458000c42d44941002446c50800240042e0003d0810001021140814081c6049d210064440d407070740c0002d0340503810b0304200042c1e07540361160080c45401e142d031416514118010311030320030070340040d042250f0b19000040c1c1003050b144c12000040e091501c454050004401c0b0343c981d141c16000c001d150300d14060034166090115a028001d0312615041010308120900070740380344074020031a01c0150320120703c40740650350b0b0581000038158800c0100030a03d040e03205070900400e001d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 88394353 1250 88393103 88393127
    0x8190e030702030a0803010906090b090604050603120d05010f050904050703060e101a010f02061306090c180605040501061b020f01050f03070f0e1c0b1008121c0b03030703 75
    0x40c0c0828000440142c3d01400207118041c09100703000e4680d41468240c8045900541c03040301a5850320710058460b0b220040d21705da000200719800103090f030f160b20100e81400c3c12142100c0001000003600075242c55680c2c002416a098000346c008016240c84c1841070f00381098801030903c1e44992130420000700d0ba03802000000c1c4109050785e070a81c0720714016000391480e400b072a44d02225800400710840d6804621001201d0192008100c075042034107840d031200860781c10140c00d031611901c002e0280500400240001c02c940114060f0141c1381e14580c400510702402054070a030b003080c000158051060035880125400c02084103066452942006810341c00900024148107051041c0ca1500800101840c840c15441d00c0d43d030030885070305100428000c100002c041c0b02d4030983c00910713844094080e81c561019030040c400c2c5820f482d250780c40420112203511800c103500c9480b0904900042281c041c044100c0100b2000b102000440d01c41c0d13041d50280b04619406500510075030022a204010801c40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 88395603 1250 88394353 88394381
    0xe04060c050408030a0c11040b0a120809130b0109050f220b100906030510120f02030a021c020a090e0c010813050105040f1e020616060209091e070819 66
    0x141c20350f510079460464005503080400b0584049541040c40240781d240b01c2c1500b4129000c100500e100c400040c003107220b40c0540b15600340926400403c12410100b00d03030104d01e00401d030001e0808041900380103010420b00300c50000d802101c000441c4d0801d044044006e500c0140312400c0c50f4800c800e400400c5113103160f0070000c2c3c1c0c0c07a242c02c40540c0c2c075003040d02070f0000c1140d91402015030403ea800b40998a010708400d941003020307034080295184524a01d18516031008070b090048140340002440c000f061304010790301c03220009080081464800002c10300038400c3d00c0c0100e032a503450358104103c5200740b00990b0583c11940c0c500d1040e41c42540640c1d440864000b208518049a07102c0d50700b182d0382140c1c22a40b004010710000c00f440381002030501d40e00713040b01c512103142c0540e60103e0309e540500094000303031841c5880c9803800c00c0b82640503103c052038058503640722450032070703041880e030030007600c1440c80110a00b010a811501c0350024a114101c4511003002c1540d02000c400020700680b495011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 88396853 1250 88395603 88395607
    0xd110d0f0c0c060c0c060c0507030b04110a08060604060801090b010501081f0305031b030901140d06031407060f0512060d08040905150103061502060a0902061b01020d0b09010e04060c05 81
    0x41c00090540040c1c50503507240088620b072803170b001188181e640c000310240150036089100240f400108070050329440607040517151940c0c41d00c0501501300c00000343d0700030000e01000c9601c89001401d01e100c0c1104840c1070114560b956520380c203c452a01c4007030b10b80080b5a0040c0400c1d4002d2034019000302d0510b032401241c80c403000303d0b4805101c03d601308861a1b04009000101113034802e0081d2282081c80d130295103868081d100191074556403d20010010101280d41102510b00d6448400215040744003000085082700810f500e42e6218002c0341d0105460500a281591082e03094070b00785680314201c800c060306e4513002c1100b505d0041c08115070a41c0c0c204400300310ba86103801924081c1c4482ca2903288111601720000d025559a504070301c2901d001e5010700818142d0001d205500103194103400a12455140040b4420788545140c0c0e100050128003094840f503415801841030607500075040040d070b4503a0042100700308080c880c800d0b00c0d50743c140201e80840c0c0d0176842800c00c040c2a061240c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 88398103 1250 88396853 88396877
    0x40506150c0c030105010e07201903020703020405100308040e2203020105060306090d02100b030304080a032303010b03010303180e07051b0c10180e010906080d110d0f 73
    0x11040e402012076911940089144240301e040901485014003c11542e542d902d161a42008210800c011a503084180c032035140410000f1f010303c80072603101d04480544109154508001e9510314080c40101d00a9191000264040008401c82400da0780d000b900f4510303161078000c070500001000792048200004805807005124584440024100d1180e00003040b245810420076040c640002c00107080ca4124101064245a002c80c108208101500c00003500700100342c0031905d0740c0200c1d0003980c458030500c0c2924040c036400000a0140c2d584804540d02e805200c81200000da0100788a61001208103000620002c0e00442444408801251605462954403044c41035a00c4040e1946000f04200140201010f090b40c00341c02a070100460003043d0b80640100450514031b0141c07901030400c80c03001076003184608030598840c000d103010780900941396140c038402030040041c0e125090480c410340e110300340c5090080c40c0342c140c0ca00658029003c1d01e10366003c283c03105072f9801d020b0b030b003003001c140c01e11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 88399353 1250 88398103 88398139
    0xf060c0a0f2a1a0c0a230c0105101a191e05040512010219080601090b030702070518190e0c030304030f050f06040f03050703032a030f0b0609040506 65
    0x40c401d0302030118070305030300d8040c18104a1840101158100c060110010800001d461810205c0d030303183e0f107a840c02246140b00d041d591030b80300b401c080400f03032000000200000c81410540003140500072601e40782c4501640c034950403001d81c48001c00348034911800d0058034002820709030040014002400c20501701000703500d6480300982d50500b00404200d0114040c090380c10507040340c0c180c0c258a24000c40c5030030010801141c00c1d18000800c81c00f04a000400190580d10424100717004081402c980f0740c8a007800d0101035180c804034081c0302d02400034840004800c6c0303c3c44426500908c01c0c1700020200e00007030f05d1030342c020b0400c881458810f8410798030083c015407020001000114000e90f14500c0d111814645682820003d0f00306200540c0103030300740800300d502400f40440165241c10819500c04080c5801d40190030f8034500c6480404840300e01d030301440003034034007504100b0b00c030f580030894080c0c001d5031042101c0c1000502e6400a10070701c03c400403410154081e94002e5401405211074041c46462 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 88400603 1250 88399353 88399397
    0x15040321020c0a030e04090b0f040f0c031406060108010b0a030905030c030d150e06010f0509041d0c03010507030501140f060705071806050d11100903020a06050c0f060c0a0f 76
    0x1c4030b941c561001090b0301c02d041d845807175075500000444041c0600941600c07090021103018001c1c28024049801240070010540e1a55030041d5000e00d24003030040d076038101000c070a41844034a1500e030280d140061015031040003d181a600710b003a296050079001030007100104601041250144810005030b200030500700003401190880306004604403013240018502c00c030495218170b1465110100b13105083e03800080e0104014041c2c90b00fa625251180c00013070180085d050709011048025200c4030203040040f80a211081d001d43c024842d0341c5441d0401c80c00c60b0400d114052429030501d07200322092828071040010540c0080c0450f0605031240c031500d0801c0180d0f4028641000b04100c00120b140c0680141d400410341116032b6400d410079038031040007240041e2a03a6204030301b81c54404c601e440c010314524001e0741e0050000071a02d521000003801c4c0d5403003581e0f0b41c1fa10740700b9844845002075002071000c3c03007800451015402e18028a0040e20103601d0a1142400d0005102c071003000c040b0208030b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 88401853 1250 88400603 88400617
    0x10b130e0624040f050301020a022e0f0506040c18140102160902070c120305030106080c070c06080709090501080309010309081c0b040e0d0819020d020d05010303111504032102 77
    0x4810f0796989025218581d40805911540c000d90061000e0f4100c141c01080041c0c46d03007417010000700c01039601c541c0080b54085410316040064030382201e40300528926404544103000a540401203c050070409031070000315089000d00000c42000300b802004d1a01c0c1c0b20a217800018012101c1c0c104480e2000604511181c00403518540e021a84505000b40500b046000742401d0780580721407a10368600410340e00c4140a00d40600c1024400b00300c20003050000c03144040e80025106a1391911640d005050000c00d5401c0e2000911418001c5008182d074031409040700c10300710003146000720500040d00a001d501c03805851464050280c0524110f19458060410000791070010300001544100000c99a9442954120b5405142e009408582150020350012001041964040b8100d010351020b40b05080401c140700c0e00116400010031102c1e00100c1c107881c4a91940d034056030001f4003007941d13144071940b01034101ea00c040102c0c006c00c0c011243c62514012a0b0f484c8080b1a01083c030241c107a0b80310348 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 88403103 1250 88401853 88401919
    0x20f060f0708041e0501140a081e0901050a060b0405030309130902100906020d0503162003220501020a0203060f06031603140106050906101b0209130605010b130e06 72
    0x10004d1111600c015040001501003401d11403080d00d0040301e0500c450003031810103018420000003042202d00403817a50144100e01150000307a82c41d01d21807280c080d01c01502e00280c0141400004680036031800705a40c251003002e0011400c000e030100c1004069030b610b1440402c643d51312501c0c400962034a00c1d0883c0f912415840b003c44c0ca074a0100003d01e80505e01c485907040000074000d004030b010103080603501c100345a1601610418030081d0101540d00040c00740e1116200000b116881c1592120b01d001e5140320302410362019036941c1005984515820000a41c143c0011000038851125000711a41243c0c000c0e00701d51100c4e840d082ca03441805420342055501c2540e096181641d55002d01592014100c280c402d46401d052020100d030048641003400c07428409640c1441c00c0b400c564006055106400034659445070510611070440707510450070640d5140e0510002051341c8440e402154584508804030750307003080c03500e86651040a005042d607035002940590384035581220070000c1c0d18202c104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 88404353 1250 88403103 88403129
    0x60a03060e0312090706080c0c011d160801060302030c0d050109060f0b0405060d020102030a0c210302040f090501050901030f03020a0f0605100e0408030103060507050403080d02040609050d020f060f070804 90
    0xc80d01c00e80ba051004060319482e5100d05ca00380030703669121040603040041c1d20310075070710f5901c1256043d01600c1c580481d04642c1c001014146544c1e040028035001111054440803ca0758950000c1c900307075a20350102941503404100d00d000c582c10400031100b0418014400042d103103090b80c0d1380c2016101e552105002d15a2100c602c00594a80f61040d2908100102c1d4428068480380c0d0002c1d4880c01801c507028140981001000280f083c049003400300c0144c24203042942c000041d00c003038001d4116001ea88030860b1500303004560a06a80304150503100001c180790b409030b02c2c42d075036940020466042202140561505040000d119a05100c2c0003840b42101003585e203090208026880b2096010042c800c4800d0240804039000d503017268156504100e0111b0143d844500982c1c1c540300d076a10060500400141d8000e400d0681d60261041c1c84031a0b80700c440070b039030303c80420035007503540070003c2c1d030141c1c02420b400c18900e8030340001d00800305030a440c50300301400c5c0e803030301040c03500b103540a02e02c41800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 88405603 1250 88404353 88404367
    0x615031e0d080906190203060102031e031602030a091a0408010207030e030c0604030b16020c061303030e0f010e04090615080303040204060611100b0f0918010e011e0203060a03060e03 80
    0x71410607a40078000500800f014a001c01c5c00403001e10300120b44d007180d56400000700c0c07010392090040301c4414092030710304a65004543c09000743d80d40300b2a60441d4040d0407940c02c400316803000c000c55001030f21301e5070303154003c9041c010140441700d1245004404290200310001e1616802e00103006a14060340b92074004915035000d060401c0b60340ca4501d88110000c000070301c001061840003031341000030298414030381001c0031400da11b800e030340e82e500f03c2d03108038040340c944a00304040d29201c0949100ea900d52104602c00401d0002c000d18030811540440e8113210f002080341450742c800c0341038030700501f0081440851000407201c4038000b07402803422a0000000c00055050601401c4000e00e5175280c520f0103842440003454943d040f0300c00b000d2181740c44540040c81959540d01c5040d03030300b000a207400741c10f050603007900d0005001003804007115402c00100d00c0034100107105a6440390850f86d944200c100000380000c0003035000802180d8400030001c030110114455206000c01500104000c641c0c0c1c6034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 88406853 1250 88405603 88405607
    0x6180a0f06090507121a06070f03110c15030907051c030e060403030e13021c05090d090509180a06090501020a120504020609010302090102010906090c17010e0615031e0d 74
    0x40c0e960000c51070703075041200307009189071722454a0074181c248090010f032a0411441d55034003240300c000000c1c1d103c10049954001d001004e4400760750140710391649540381d0a006e22468944416880040e4885010140c4030300c4811544019a40022a0801e1304c0300d1503180c50000b10745103144903c0301c0400204000740401c0682041c0d21003600c40d021142c540c24245035a0b0020a000c0d600c54080e409809080840c2800c00042d8040d111150440d4800400750210350381441d00030001102c42440901c103121400c10f0f00e5014810031b0b0181c0300007800c451070b103a5500c1d03252070565080d001d4025051084080800104040d44107100b500744c4144000342c0d40385042800100782003404071181d862145044140b0005039580400c47c0d54006080c20003580319691480142e004000003e0080c200c18208001d4004004807030401d001954810341185400d100c10b040707154200c0321041c481080660000000c54282d081c4010405d4030080000e0840d0121000c40790304146148141a0510f1180d100d0324100440903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 88408103 1250 88406853 88406861
    0x70804021801030b01080d031104050f0604030b0103062901020604030f021203091b0102060c120a0b19030204050a110904050402030f0f0c040516020303040b040c0504140910200306180a0f 82
    0x147d07143c0b800b03214480c15508603042c11303c0b451041e68401e1115108540716a02d84105a0f001580c000542d0310140da564101640545030313014031035900d00b9202c0328010461200d40d120002801045e4001c10f2184d0740c07a07406842038191300e044402907110710813030f481e19000003500440c840c1c082000903111000c10044040341d1200a000c1942c10b542010301007098403607018054419010028030084180e07250307108004c0081c6a4212401d030840d6031240c1c55200d1966200410048a00c02d4508100c5903031400c03c1c1ca000c0700c00403d51030000000c1088240020714254001542103400101035400b402d01c41e00d03d441c988045042c4840064118105225062402d842400c0e031250030090180c4c520084a48025201c2c80002d10060030048040d0210703051105524000e40a09800b0f8020414990b00c000343ca02034010488609003148905016410200726078001c5508812040050086081200c40e020009800007040d884c0c110040190440030325100031005805510ba60200182d03040030100810196 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 88409353 1250 88408103 88408123
    0xa0c050d090806070f05040b0d0905072102060d022104060e0606060406050a030e0111072a03032a0f030216030c09090c030501060b12010806040b070804021801030b0108 74
    0x21010180007040400b0022450540c40038007842c0080b0802560f000c00e496a0040da0418903441c000800c2c09403081e41141e21040c906d60160080724203a69072109401e1003698403080c1904c03030f0165000c0400041c02e00101401c15050b041c8030140c20282c03010400c0b01c0029800700d00040603076010b82800103006c550f03c5101c26924418001c1e00a40c40d027503020508522641c801d0004010002074900200c134030a42c0001c2007200c021009110320304d200d26400d2641d4114540544840212600710884854403800d02e4441d10a0600740e140050300e562000d5030b011403a41d0b0440c101f007160404413008c0186d003c503141300040c41740200c10a450003d040c0246018100e5601405100c452003080c0007065403650640c1c2220000340003c01d0005140ca41004898055440144250708008011901c0c058110107010707010a400c21a940980c1c1c1c1c0c004055076218180e40c083c148403100c3e8049181144903403031240d44203001030b0500007007800469850a944200740d20995002403c0300040c00b119400b40868941 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 88410603 1250 88409353 88409357
    0x7020109050a1e02030f010204061803150c120207150605040506090612070509160305070c0b0a090303020705060907080c0604051c0204060b1305131e0e010209060a0c050d 75
    0x49840c840e92190340d600c0e5104005070640c07100e0900c0e450006420040000030590103400e803a20906c41e000c2c0c42c1c0c040c2d00503000c0c040c08290140c803440c20100142c00c0d00000c4a4004480c0c211001c03604c02c5d140300408412420100708040c1095518070300b100ca00043c14918403903000c40318030300801c43d010300840e101c03504400d1080e4141400d0204540e42d041555400440c11101039410f0703000c3c050b11b1482c08015030300c800d03004501c040070011710a001ca41d2402c0360b00402e4405000700d80c1d8540d403c94801c00000d0380200340445000102d02c204e01035511410449100e400d00601c0c0c08c68a8407814541041107560300003a60005d601031003007906c00d20520040c0c02066a40754102800c00000950380f102801d0f280c0c42c0071090110004c00d542d102c3d0491801001000d62459449800b51a034060002942c040c0c81d000744204490541586038034802c1605042c50300d00c2ca640540e9081240d01c014000300c4242010540d024090540c2e103956250007800e100040340c035018403102d00d924003917081401c0c000740b03402 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 88411853 1250 88410603 88410611
    0x5010f050904110d0c020601050906060403240b0a09090606090204050a030b0604020f040e040515010311010f020a0606060c02040f09030206061009080109081b1c0e12010c03050f070201 81
    0x190a900300058654004089401184203012600100603030301a1030340f0209028180021110728680100760b44d8180c40701600c141c007140c0e80c0c02d414000c291040348001040c44a401184000c428250b5500c1e00080448580c04280c0504a9001403100d0126410869110b55941443e00c10041144124001003405040c2903043c20310b0500000c0041d50f480c8806005494000300082081d543c80d07044400110214000340e40382c0740c84290303200800604480464280c072030880d0942074080310202a504a135071104044c1c0030640329a0044400054040010066100304d50030540081c0355806854003030080d99840f0052500f07140108015903e00310b0241401c1880c103808003001ca603002c03e0050344100f043c0d034428080c072503840e800c8a8010195006404a5207000300200070000142d004241380350220210300300d0400c118502036100c044220300000040c42c1e00515441450103203003103510842c0c00070b03d4002c03246100e0120a0944000c3c142800000340e03200200030344152034805840d002070561000300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 88413103 1250 88411853 88411877
    0x1050a0b030712020a170c0312031311060c070608090d0302120402010c0c0f0e0406050703020c150a06090516270303030b060705030703020d12090206030c0f16110405010501 76
    0x3030749902c810b02400303002481c040c100030b0035502c0317050040300205500010000c40020110820340c40754885130180703109004c0c00001254402416058034045c001d002560b213108059540c1d140520b5458100b8070340c100308140b26001c0001c0c41813011000816071525103426514020f103815050102003c20740c0e041c10700c180031481e60020020602540613a0a0070040b002aa2030b0510f0703030400040d50302440e40d440b0001000300b805a0780d0341b48540503a12a18050015440e190800c1e13040e0b004138180007900f540700512000d03e5080c051001e503009170031021700081042d190b1070f441095420071910301150821310301d59840444d43c008001c0010f60a05003941500700f0582c3d400780b4000e9001d10000e020075442c0c403141e05050366400122000940d11604403603a5240b03601e070183d124014034401c140407440101c0c800b03c03e05068011600d040f0303401007000c1e2850342d60b50b100100c50340000d2441010088107001c003401d6200b04c0800401800d028032900548100302100304404d442050f04810304000c1034980d20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 88414353 1250 88413103 88413109
    0x1060e070c030c1e020607030c03020705040216020904150e07051801080601290408061801060501020a08160f1a01060e010c0624060c06060b03040308130f150e01050a0b 74
    0x10883c1c10791001484450100982d541c2030f8030b071030030304029511a00005a6130201030b00402182c0e90360b03109400380c1d20303004d5503803007000105c1c000d40d10540d28105410542c00300616002280952080c807400d40d04c840007025010010844080203503903104d43e48155014001450051883d08034052030a40d08d8481c0c0d0304000256403201810320540c1111601d940210141c68101c0b0000e022001808005a445642d01e00c1d40715610201564000910341f8070450b0010088018013803a000c0d00c90680040c050883e00c1c0d07603107000d00d030b1281e4109410320700545c10f498000f0f414003d10701111409a50310441009200307601d000c0040040c1d124505200140854144698010b03035039581180d0000d20001e460b28003042000b44440e44046a80100004a240450b50540196004d002c081c01401c08001c02c030345a51a0071858402034074080c1c0459940300014603c0d0010f030614052051041040d15220886941e07508041d1912001c94840241c446180e48001e43d000d00c2116840b44410100380003512909000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 88415603 1250 88414353 88414367
    0x50915090907030807080901030b15090d03050c0708060f0a050114090402060d05070210110c0a0212030408030406020109151503080a0302040b071109060604030b06040203060f0306040501060e070c03 87
    0x108034000c200060000d51003041c02d018500007160440b00499460743c01d0314240805a2040d000d02d804039103811a100c009081607103401d400700620040d0140361019500400c115904c40102c01c07410010304028400e480441405401c000701000c2c4002c0c0711504150030b48000045004140000f040c0c034120042016100d0f80140c0c81c0b5540094413410500d03203071400801d2042c45082c044160301ca0401c002c0c484810790000c0c540c2030391081d102c0104054800e5040300a403d1290383c103100a00c0e0722200300340c0050b14086408002d1881da5400300c03464155121881425600141c0c000e10152755185880e00503c0a2254403400c0c0020b84c003001c001d420803600ea014a01c5043c0e002c0503200345000328442c8105800383c0c2c1100c1c0900b44a00940b40c40316454034003105508d000f500350038050024100400c03540c0c1441010b40781a03e0380080b031046241e444405020007900300a1820707030712810701c18004140740c40510209014500810012072246e08001c4070351080d890151401e010050600050b001299202da2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 88416853 1250 88415603 88415641
    0xe03131a0c0d0c03030b031b0a08030c060c0c01020405030615040f02040501050d0903020c120a02120114040602070303020702090f06090601020d0509010c0c05090108070905100501120c0c0602041508010509 90
    0x1010f02e0344921505086006200e40c8030481d40501c9408003c1080c1054001c1d04155804101c031032405003034640c40c0c115240e00884040446503440240803070300700400c2c1406002940810800103080680e12030000b40780c0380b01503c0e007495880b84150540c555040a010b0f1801c11400e2082c158545860300000800b49d00c03640a10005080c0c0d603030660750425100f070259041c52440207040c00d22041c882d2551588900280c0070480c8030780c00300300003200c080c4018001c012060746c402440300b000d503440b600c48a0203944643c10440c10140d0802245c07005036070b450f2405004600000c0815408d01d003500900001b200f01500040c10366000400b03d00249901c4001c5401005080c030704102c90740d0141c0340c600f5480c0141d802031640440c201c0c001150350030700001c40d001115005202400b682d02d40d83d04980032010140203181c001307101080c2d0200303c1d010b00d800050310751169152000c4814181c3e2109412a01b10390018034035110a44004a0215407010050307014242c11a140790b0386051542694803a091000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 88418103 1250 88416853 88416857
    0x31501030c051c0e100c021006060906080702010f020406080402030c0114031b0c0708010510090b010801050d11030a0c060e0114031501050f0705061e06010f050d0e03131a0c0d 77
    0x4040c2103540c0d119600824501e0254000716040c400d1034031064001740c00600c0c03503603006200b0b00230b1b509452141d1b80955011500640c0710310101c00c1c00c104d0102d603540c5009202034195900d40790f459161204910080006142943e134103180b0341030500c101070501c50b940c8000c50400c28455680c0002030301401c1102e4000340b030310780400c000c1d4034112400b04450041d604141e8690103541700000b02c080042d040288145041028141e600791a5040582155421000c09001580010041c002c0342012050a43d21038000e55075484403131f0b1050300207403904030751300d0003252100b0301c051041020b42e8210818410200c03003400c3c040044040311111001c00d01005110a40c5140442c40c0c52030b07164040d204503140e0140640381d665585026041450366010103580801c441001d0310103e52065544440f0f290040300140c0d45c000350200750366411205500031424140b012039403550f4406000404100905414944034803004540d49045000b1400031140e004001c0c20704c10070402303c890391002140301c00c485c140d01c2c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 88419353 1250 88418103 88418137
    0x50c100b04090b0f0a0501120308060607080403060c0903030818060402190e070509030c010f0c0b0603071517070e060f16170c071e0311130501030305031501030c05 72
    0xd28005009000d440070094000b81c01c09084c00340003854101a54456064070800340910b0740c2e18018050801c140c0c000140002e4041e1011030b100d49030203070081c00303d80d0241010341d00705a282e8030b40030201c48102999102003802200c0070410142c010581035800a42c4800074050040d4400b4450303101e20300280000d104005841f0004002900100000040c01210140d07a07072500e06034801a10b02d91240c080d0922921407080c4c206030661240742540011101035a0f110030340c040ea5034070b00031044e0000d032460307134180941c0c1000310f0725240140e4a1744480c80c0710380e2410141c800c50003c103d40e03007402411440800c180f40c00d03038480d035454040440e410b04018802050380c400010000700300c100d040d05401800080c1d200080c0d1841260b030805030500314040742c02d460760285d45421070f1009181c401e04100b81c00000c500c0401c0410400b081501c04407201038500c8285500000d03502044503400d070400c8001c100c0210500c5032484692680340c00c1100c003801c041018101c810000f82c8a4081c80078039000c41000c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 88420603 1250 88419353 88419371
    0x20a0f06020c01020c0d18050a050904050f060a1a03070f05150d0501030804060e0924040612050d020f0f100b061e0316030b060409020c0312010303030605010f050c10 73
    0x149074110b5150040d260021500e8450950101d0b89517030302140e494000900b80c6052101a0a8928094003181c8d8024900d8985d0751500081c0300400c18014003c0e07e15002c1c2102011210005022440c07103018410400121030f0b030031400b0b4a2407500100d0301c407402680407d030203004608020070302c941504c1e012904900a00071002c1440680d00c204c100d07946001d8140310002040140000203001130320b2054a42880e01e1001000b44646d80004550300d9075007076900b2410300d03200c11301c03512800d034140805480401d0498a81a03002c202034500c240c1101d00d580050802059603506000854040c05110b0283c0700d60b1000070020f81d85c412404001e561103c0d44d03004183c1369660b035281100c2e00301c1c1c030210702803a002e0180c56210600303800444005401ea40300300030180c92948a48280c51044000601e0f8500700703818502d08800075040604200d8440c40f081102007407980c280c03820b82e80294405e40c2c01258a07030810000400e51104840d0301c206002c0103024064a4441c00300d029002020b01c07500010b0541c003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 88421853 1250 88420603 88420613
    0x30708070c090603030e1003020c071a0403050a1b06080108121602030607030c0905010302090a1202010509090f040614040809220905030c0118050d05030c0405060d0207030f020c01020a0f 82
    0x200e98003040c442e610b407600000070150440c202040780c401c11580c5100500e01c0f102c00b075013a482240568078090f00042401c3c040018000d800c00607440003502d405060540325a2514680340f5400c0c0103407120207007100383c1844013290402c030310054225460b21410701d525042c202c0707560301d01c1d0300f000030810720020407002e50441030600d4800c150341e0010704a074154205600050010102401100700007009100003191950280c001c841340140d0140081350960700e0b0480e0992000c05512040381003002c100700d00505565000b0005000700701d000000349107401c10345401d008554406401c0704803ca8118100030105807850160742c540b8105407000135410020006006540500321152116103161a0201045c03040000c0540810b40000000300265520765480c5160b1130035016000307080d58400b202c1c891000c2e11400c05141c11005405165003001d84590015542d0303082600101c0c065940400c02c54181079014030040b2403010140050702914240100003510307a407426030060300c221208100201008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 88423103 1250 88421853 88421873
    0xf0102011e022215030e0609070509040602090a06051803191202010e010f1406180c0c1006030303020703030c0801050306070e030a021002010c110304080c010828230903070807 77
    0x443e00600e0070b0b401d9132030708004241851003504540010b03107043c0000b03180c002d00082c0140607455802c010b1211518007010010f40840040041310525001d010120a039118140f0010251420b901c4d034989440c5200c0c1d090801d0760f404150640f29600c2003808003620030b000308080c041c00c0c1c0c0000504e200703184540c109a002d1700040c40c20640c95807070f01c2c040e0702284401d60302c40c000d071058602240010b07483d6041000303540402c1c0340e50500c66030400d00110700c402000c000240101d41540342030f11001c0e103643c0c54580850307026602c15004a5000982001010f926115010f8900f406060000544d4140408a48d0700d8900622440034004007006412580d902042421882a4001e200864500780303a070740280680755840c46c07840420409140080b50038404026101070b6400c100040078017240c5040115118807004d07140a4442c0b01030550300d00004014003492041030700110011480c510078101401010300c166801885810308581448031400c400700444080c940c1255405031100c585040c026000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 88424353 1250 88423103 88423147
    0x10f03020a050717030a0b01020606060306120703080c06040b0112231002070c0311010c0807030c020f03010203040501060e100b0403260c0c03060c09031e010609060905060f0102011e02 81
    0xb041e13054140700300c3e02d000e4004502c180c1d640c0c18180b101307000e80300042ea9129401e6038490350120061001990754213209107040809450002207420326a075946810746580e00c894070710031460708560700300420f000369000440d0040004030100f156031000c545440c440c843c4160000f14410240c18235003003514204100b40480700c41c0c89441155a40224075102810203158801100c0d80000400014038071b40c0180015444aa081401d1920340443c1d070b6001ca80c038812046089034005560304084203151824805140b040f8441d8000240044c1443c000d00c0140c04002c000c91106605407000340101c00f040800d5070102c1e58841040700203160040103495101ea20300204042064000c91050300c0c0750000034882003048415010740d00c0b29210300400c0b4869100301d511454043e070100c1d602c200c01024880c421072844840800001d030054a8511900580c0c08542c0500e00301611101030005503e006002c0c80d039400b60074002003000052031208402103400c400041041d683d030106103840381c841800061020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 88425603 1250 88424353 88424363
    0xf1f0302040b041d06010804020108040809040207171e0f0a030506060403080a0f12021207050a11030a03091a070206011e0b0708031e0108190302070509090304030308070e010f03020a0507 82
    0x40d0f81e00c6201460315209a45080c440c0c915064004c503003554041d00c0d009000f143c060b52105500c1d03841e6100d041c0f81340d00c10b551058001d542040400b0101e00301d162031704401e1120310900741c3c2d41c0111280301c0e09480860860b80c00b1000003000000015600c80302101c03102060303800c011940c1e0740c0d00350001d20701c3c1c060b5a1001e0482d03100000d08404c52a4440701024801c51070741c80b09180000e00562075012801030f8000440356404101c08210b40b903001d50050281c10800c9c1c6051810541c5103c402c50945d0009581031000c01c1d12440058200283c11510301d94448080310302001c01e16203031900079919041841b41c100c540580311144c0350b00034054914800507007020880c1a81c0c503002c1d072a00c060741e41c3c4101c48810703064408500d504900c09403075003154122041d840043c502041c40041241c0d0700d885100d012000c2d84101140003d00d0348420740d80511804140c80507644684c41c45c10050101c50004045004110307004880e05944c3e0381000e04030030310400c2841d0068440420000a0315280b2400c81d000e40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 88426853 1250 88425603 88425607
    0x30803070804140a03090501050d020904142202090a0504021915031802090c090109031401090302010b01091505090a090f061e08030d0203060406150509040b0f1f0302040b 75
    0x20180340c001030807030b01451042d00c0c078000e00e00f00c1c600c200f92190007a01d0001d0001d001c1840801c0550321480141c400311200000041c07526102c40d002500700c5403800e010740340c0e1001d414108001510301001c544a00f08010342e81c6030000c100c41d070000d0300000c03005003001e90303042d1380781d0104081d9141e98a0504843c141504581c0b03503a0f8440f00c4001c9081c040d0030489000a051082c0c8820600c51891745054146d409002500640c4139004ca045041d080342c90141e040120414001000c03901580400d0801039840000159491040c10000d09584403601d41c0c80c10702c44406010008000c0072100d100e00310b089072034055210b81040c1f001034a8462154001c44146042003008080103200758048000c842c1c82207101c1420401e1200e20001109082c403600049420501c0130994000d01034000f554000030041001030026100c85044501100c0d088c0c05000240010803203031841d0030f0a2060000e104811140228003610510000f40030003020030086400503000e500d0704045602030340540d00070f0401090459 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 88428103 1250 88426853 88426861
    0xc09062105100302031510050a031a1519090c05070b040303090204090212010510051909090507030503131806120f020d0b01080f1e030f0703021504030801080c030d0503060d0606030803 81
    0xf101d0f1b1802a50703150651203410700c000420386056019001100e030701c041c1e10446080761300c40461060500a040000d40e15844101034403030b90301c3e10f0501c4640100c800c19811445d0030010600c5c12921100d01c0c000601c20208490804111640400c50744990f04d407801040c160030620202d40a0254054000c0d01721690102c1402103450642045100f00301c02c00c000d80c3c1041c1d40d00100080a0b514042503004082c0004042c8a280c450740c200010b050301690032619440c1d902d43d034007840c5034400c1d144070a05505140003805040d00191000c80d4108400c2c206103c0b0608010820080c01b081070801040c840124000c8011911982d941e40c0b040ca4000700b0042c3c1c15a50740100c2600c030b00401e0311514140c041c021210b44078402c0003a81d40025050f0300000e604003aa6a99115010b0380170b007100364294491203c41c04041d80c14030100d2032007140f083e542c800031540740550052404070403400b0940309400488494443d642d02400740d0354400c40444003084915a079080c4400240200c0d0005400c40500200304 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 88429353 1250 88428103 88428133
    0x40507050a0b031602010c0815011106090304050108011509121b080601050f06031005011b1b06090e041212090519020123120709090905010c0906210510030203 70
    0x80d5100380b48101d061101c2c0032131404120308036441800880082200721020a08040c2c10b241080001e05040c1004442a000204d00360f18140302118030418643c00040d05000c00d50b48070400a00505a40b1000440c1034115600a0034281e03032030081c00003130030070252200c0600c280018403046080d01e05201c0080329444540541e1105824010b8500507001d1006502840c24484201da20403c1844501c0d2000e40c02d10004550040c0f0100010144200003103904000c1000725403a084407480280d00101070074a8400701800c1c010481c0e10600014036004108004201f20450044110309685010080d44000740b10420003400031241c007900c0ea104480e9181c0084000e00300005400f4000d0300c4075400c100305424000064002c103030401201e030005001480003c140040116085861810078603560f9454001110031142440390607285070f91558600b180c0340c2d8100444502800070f61070440b4400082c841003460003541f0009410400742d503a000103030340c0040204450050365004050300e00d40322303442c1c02c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 88430603 1250 88429353 88429357
    0x604180504050d0c05070b031e13031806021b030115030605010317090310090f023309060f0d021303210801140d03020c030709020a12020307021203040507050a0b 71
    0x3180c041c0f0400392000380301070040c074002d5403055100e402000241c1c186450014250400340403419a101c452003640da10b4a0f042e0101445016048ad07421901822420028001030022880d4034110180c1d140602403543c0c04160415082449000021600940700c0802d00501090305040340403402414040304001441d04018100e9002d022000044000c00221803c0c502c5004110307030b0b06600c4010407906d0006a42c000920190280340325007109c01161f0041255103000d82d00441070880003e01d2101c11410034071071884e0340c075001d000880c148020314001c24103910600449014600010032086108001e58044540d28041c0d010a910381d56503d1030950032000003041124801c141d01c840b54080342d441070300454101d50350621498036400c0c0b1102448031100c42800240c0850150300c011070150349081210710002e198403080142d4842015100400411a1200c5042d01e0790041080c0000194005805039911002d0207402d0307925103031498058540a4107034003498101c1c840d440b000518400d0000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 88431853 1250 88430603 88430611
    0x90e0705030c0108070c26040608070801050319050708070803210c0301120807020a0e07110606130c02030d050a0b040c02061b39070e0108030f0906041805 68
    0x42124601030310340301090784450b031020300c082c00199001c000440a62041c250080000c0c010300155000f04030030444641c0c00c070384441800c82a2000000c0c200401540107120551001851038120a65410440001d0311004440030100210354400911740c2840400d01540b0f00900c0402c2c200c40040d07644e8101d9a4890300010900281d481e40c410380c03024500500829948078425200f1003d28582c01c0a0980c0e03101c400e140340a54140005100303210050312098180d001030b0503198190001d600d00688001c006040e625140582e54002c4030620482e81c40e45120850000c0311448080f0304810001803c0b0724501686a80c0482541480b041c0101c041265100c4411030700d0030348090064500c0c04806903030350710040c0c0e10000800003000061028182441c05490814403030368001d015900300354602042d0300006c0d1624008206034074080e40040e082042031000500488400503120b41c0352140301900d9009401d40104041c9000400c030b5010b82e034003001c490142c82c1243c4102d030091004440b5200400d8100c0e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 88433103 1250 88431853 88431881
    0x5010509090a08030601180b03070c021302070f0809010c0f0305071a01060806040b010e0a032012060c0904060e0106020102120a060506040303050903070b12040323091c02040609 78
    0x60110708039100119100ca201500720800c24550b4445000444450700b2881c810880d0440c030311001700340c20744450300541c080c01055680308445030b80340c010029810310241036000c00600c10841e42d00014410400c402c0c020345c00c07140050b02c2c1d2841c01e0041c3c84403900240000c0a0b5003060100100b0590050003400c82d00340103489184841d4040101071000c08002e008150200e01c01900045580c90305030888840200c06241810085175640c0c0401c21068082e08200c80e0b0f040c00106608070310f0880800400e411004075044030710242607401c1e940e01c40c00050079044e1503c4e00040e071080145c0f00e68029400601c04080d55820b1580e5580e1300034000c0d0803a9445110781900304001c41c1d9104c83d01d0254030243c92004111503d0f15207155010f44495011000c80d5805000b000b000103011718864024104080f40a000440945010f290083c0903030f0300c0150420030b804240071020312000030201500e0007548140c894022a01c0070804d500c0c061622604000e5115042c8800800e5100d040c7d08540c802c00031403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 88434353 1250 88433103 88433119
    0x703020d020c0a0e0711060901060303030e19080304050a0b07030509060a0e0c21030c03040302010906050414040515030d02010b0f1c030f090306062306031003030302030c0d0f050105 80
    0x400d02241c4500c052a40c196000c400064140868201c480d407154026a050a00c0003003c4210400381c1e04110f4200c034990a281d42d0fa0307900304103050b0103014004a113604000504001607910708500c01d0130406110240c2011000320009003009410082c580c00c2d1508514441841d10345000003c000e480d0888a0080c2c0d80243c5020418010950084008149560003c0c1900800002c1032101d078000d0510100d826014401d4150000c000900003045130f0032040000e540c0d81c0742140005086000035030307c0001004402c1000700900035542c4098605503a00700d5000c503c549804019203207034060700b02c2280e498003845000a0f1466015441a0601e8006503a1500d02c98519801c112501c04400ca10084280742900300c000000d210f8565090b002c106410015071240d10394940c8011282e907600900b19010000061003607a40b07248406100141040315203628614054221440e012001e1000405254021000c581c4039840b2101380d40b039406007083c04200d80d4280744c0c808405440c00303215040c012115 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 88435603 1250 88434353 88434373
    0x10608160503010c09050616140a05120309030f07060603020301230105031f0905120d050a0b06040b091201020d0e070e0105030c010c120c0f060c111c0309020604030605010605070302 80
    0x107016000e43d003d03ca032212117905160005000c4c9507480015045126468108424002034003c03520003900b40d40130380100704e0060549002071500402091041c10304800313004001040c0c0001040f195141c9100d40e450381c50f40050720b801005001140c0000b5850750811448600200704500d1585010404006030031559076074005058481d41c4161020316030310a0a1165506204640c001d05a00b51180084546614403165a0441c030b070008809030317000545550600465446900414120304021070320145403d140800c08070481c803450b914140590010082910f0b14002903060359502c04007400f040c01810b0351640c071309440700e485010701c2d100484d94200125040c1000101d0940c00c40068460701070149890315409403e18a10b0040c80812840c4d95200000808051b40400980d00c074440c00324120095900c090060390041c9460b0840344d106100705241d01c18036a964a06001c40390030001001d00c4a400410305500c200d4101401841c1480000244250300c000104070f480c0c041d500b80c4a030010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 88436853 1250 88435603 88435609
    0x203072105070204180605390406032d0b0112060b37050910020c1f020304080304080f1005010b030105040b03011401090606020d0503040506070807110106081605 71
    0x81204018005a41031050302d0042c00c02c2d0b403003411007207150200032002c60042d030b4508003520f5040324071a40101200307110740c0c2d0889805140021b5118046808951507000d8042c40f070090040e8400c0710109034407508242d91003402c8a12246074801c03400280051050400d0203d0040c00c0f00d0462140000c0c8148110001e8407000c2c032414096601a09504d464500c80c211440104c0c01d81024407413448491903000d0580480c90100004030b01e0301522525103031502242000204c9110040c224155080750044003042d580311603000d074034040501821507800c411600c0407850f601503038100151340d110004011640b04c00029020454078021801c03100c142d1075151340c0380d0941b5001e200d001c2c04a001800144050f01c0c00380c00100141501800000d1114411120044583c1c42a800840c0e042d0392004240f21460781448011a0f0700c805007031407482d40c00c03d980d40c00e80d202c500811100800401170081000d031403040007607054801d0208002c0c07141c0d544400d0180d403180062140d0030900e5000d18400a1030341 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 88438103 1250 88436853 88436903
    0xf0603150606071b09020a0c02040606080603060403030c0903050f1e0a03020a0f02060904150807060201020a021507020309090103030305012103300e0a060f06032406090c020307 78
    0x144080e0080b42007910343d50702c01e441c40041c0c1d030404e00d844421001c00b09a181d02840a8201420541d5a46403800c1107030050000300d03070f040d4100c041041b071150304200b070548000803a1078200d0ba140c0303070020382c00c8896030049500ca4601d07080141180102001c0e141d09070000110080b00070300c407001c07000208603498a440e07501c48401c0001005a000380d000240803d01007000c014040f0700240c49117140003405000202164a00c202213140794681d1b900a11a040c810000c42000d04241c0c0000c510300768420340043d54443c0d46880003014007210b200000c030068030a1094074078202028240311030343d5840e0729018000d00300900581140041c10b40030721500001c030801d01826150582c4805161900740612120441c4602100905089800303240808103100e610441c500d180081c00079040702c841d9443c10b0b40644080c460140da070941405024000310322000b0340788080310000c80962002d92120040c032406803485c6d40c00700580c1881e00a40c144001d4011000b416541c3c032441c006140e00d0610900290300c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 88439353 1250 88438103 88438111
    0x30708151302031f030c03030518060307030218090105060708070c1502061602030a17090106030c1205061503120a020a050307060606080f0c030a020a0306170a200102030a0c080705060f060315 84
    0x686c225480400110b4010001040d404070b2001841c8880c00105011803041d500940e21000006d42c00501482035050003e03885002c10343c216000101540340100044503800391038009410342c0000284401040800101d410050600100c06144840300351000303500d980d0112846280403400030040c04200c1d10101c125161200e540c0c86a844a0720200440c020801c00100010300c150350b120b6002c4042002d0035420700c002d10314002000e14007071252500c0d904106020300013006032682450b61040964020076402c1880e003a50a40507284c14040d40c00b24544406401d000e0480e000001d00b000074000c0ca078200310140c2d082600d0b54a80e82d21180c50386100c02000311541c010b0001d090001c6055490301e50020030100c1a81e25020410680300c07085281400d9820b41e00707542c103520014540e410030038070b61822207841409421022203d15114000b070348034414250000f003001044004001040441000c4d1001e19811804036882d500e46104117034030201051b1000c0380b180c0306814420301d0b0104004035117441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 88440603 1250 88439353 88439363
    0x3020c070e01061209020d0f060501080d020a0c0b0702061c200a08040303051e010905010e06060c03030402090c0412060b0328120302120f040c09050c030708151302031f03 75
    0x441c0076600800300080060001c06c90780300ca06520040c1c00302e220607250400f04d034051100050710b5490b24130501d02c3c0c810703452150400e5400c0562a0360110f40c94107004011180c900002656070b110a1001603014810030f14040302000741d0310407000f1110850352109007a040c480040101199500030400380794060441a1000101c15400140000c1c0c400e401041d040306001c4071612498850102451003001c090700292843c1c4d036100010050b20f40c40801041d00408190b417014500701c0d021031134546078403000b44042c0c02031701d14101141065000801300e5008201107c600300c01c5044929049018084400515101e4400d04114800caa010b2540c0068102d00841480803120303000d03521000c0400e030312002501410360900641000c00c00c030466162040e0100c4001044a103824503220b40c4000c001c0c1c03c0300085907d09005c001255641004881d08544c950030f1042403980d90b00000c82d5400100034041386c01c41802040c2000c1905a80c0285008501e85009020f13096140c80740c20a08080b81d10010740 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 88441853 1250 88440603 88440617
    0x7090203010b180103021e03100506070b15031207080a02010605060903070603180b070807080c070c060503040f06020a170f07050a0513231f08071d09040303020c070e0106 75
    0xc2046800c800b600074880040c1030242c10110100c17000c0042190b42c7c500803040a000100304010001c0501c0180c014120840d905824236075180c688400c03003a401482881010150041181b0319030b402c01c035084521840c00c441982c0d505051603e9981c5422524801c0055801d080002c1000d240c1441900c400b040c01400501c6003a01c0c09008034080e041c0d401078081d00280c03284491010802500040e4410820358a4a048a0602c1c4100402c800307001041c0341d072643e00911204001401049a800031903c5500c2c007140c0f00d403118241031202c0700701e4039001040b02d03200041c813590301600040303449890408009142d52640d0790301324115002070100e0b282d60015508204425509000d00007510300001d01e24244403545440303101c2a6172862152550100703190b01c01e881a84280391030244010100d030368100d180d801c0301c5d400101a1101c00d0140016040c40502e03100740c8842d982507400d603280b81c90020009240c5003410b040140c001d52008604e02414020080d010820303640c0280300314100c40031582c0c2c1c50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 88443103 1250 88441853 88441867
    0x506031009061104030b0105031509030301051012050403030e0c06160204021b010f0f0b0f150a1403012607150804060b091609050301140406022d04060207090203010b 73
    0x340200318041046420315654440f2100d000c00c0310000d403000e5442046640865418501010b181200d98110060440001400c01c03001e62004026030381101e10a45003009a029100c409840b0344000c002e00c0c02c0140d00d40001c01080c103505400c142540401c601c141c440c0c220b2040180903082c0314001a1071084043c00c4082d10060805500030f180b2400d446440da0f85140c42802d40c81d00717681c02000c2002d807141e220320f402d1441c900e151040e9048814101c68410b1040000b0707000c01c3c06040403c60f00b07030302c0c004085500c03400640104142134804001010340d80c0da968403600800c0ba440640311490101d0841c01610720716502c0005814010b48540310410000700b410741c3c2c0f00302e0780c0c1030000703000300c0e40c0546035950541141c440380344e10307800707000e00b0b02c0103401403000341c04010a084106d0740300030322030383c10000d450003610303050b60340d0a403c550401c10151b69010701c0c0b411004c1031900c0c40c4625880400d000720b540441c504503000f420549205d80c0c20341d030701c060791010311600f0380c0002c1c018001e040d04100505 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 88444353 1250 88443103 88443133
    0x51b0307050121090f03050307080f01051804210206180d02070909110a030501090204050a0204050109060e210d2309060a09080601120209090a051c090e01120510050603 74
    0x2007603c11045240c0860181000e40e51440e03405010b0030101c0c042135002c010b0010007030300203016551103010782620110760740c5040f000904800c100e11041c042c0f80c0001c0042402e001c100f881c425041d2240510011408401041c0207540c0d46c41101c2c0c0200302d0100e0b000e12400c425002c00c4001c08104240c2c010312019081044e41c034020680490200e901546200700c100303e40c1c40e403a0350b0000440c041c07000059a585140103000681d00b00902500c143c5204000512940e030704400b140c070a491151900034809000000400e20a4600444802403503c1d4030103418041d800008540300d229010740d9441e032455503840200001c4001080006802603400c0c019030f0006d06082002c2e190725040ca01d054030100343c1e1800c15a00b010800e070883c280302401111202c0542c1001442282c20121042c000d000b0039046454460b01c40100c4040b8000c180100c03220302e2a20b0348540c401101520250150310340650f03641080d1a203401c0100c1e070417a858015030341c1001c1c03011034a105051296030094040d0008007051000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 88445603 1250 88444353 88444397
    0x1020303011e0f06050301061206080d031a030a110112050108060f04081201080d0207140a09150e01090c080105010e010206010303180e0a0b1206041a06011704051b03070501 76
    0x104036490ba8829000954407043ca036240c002071146841d045d590354100000202088250741c1d41c1d00d0240e04004d02040700c95000201c400320784001b03290000d000e50704001d201e030380030070b40c1010160b041c81029017020038459244440340403c01d00340c030703440c4610080048031400c0d11000d00c107146068001500164000011084860b88a07200d0792070700d40b41241d0355110400c409403e0b0003450b01d6911030070104100b036404206100107818041c0c2c46000c10740c1b85c01c001800c00d070664041d0014150b01d8130340d01074805482440c1e000107881d9641c9c0c411015078440d42600d000700400011a80041d0b002c1780000f5a80d4021a41a02e4040040c1e001d4201a03003192803e0300c05a4100c40504800081c6800c001003011502c50014002c0c500d04002080303210440d0100845903a40b01001203642c3c001809000000c1c041a94820080035003801540180e030711000141c5814501a0307821040016070810441080404515075a03031445c0d0000f010b01c000e8082c1d09041c0c1d103840c1802840d012030421210f80b88510b4102c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 88446853 1250 88445603 88445639
    0x5031602011e02010603050c0a0305030f09040b0d261204021011150a060e0108071a16061d0705030d08130210090306060e0705070305070213020c0a031403060102030301 74
    0x14440042000b103030307100b411001c2038650000144d6484c5028010403406101d40380d158401200e50300c405d1811611869100c0c400d017806210038801c0040c0307051071515107400c0520440c10040c141d080da0b043d0741c02c1c410342d510081d40101c00c005c4400011b54a8501460003954110386981c08990440c1e5100e900380305800843d01403036000c0c000d120b0034a0300c4800b410410040d00c4116801d28407550b061a00c4070b0000c1e01c1ca59000400c081c2244001803200c1e10b00000c03071500b02c4034180c0f0f10458142c00d41d600d02580788a052443c080030420038500e0703414800d0703503000084c4164103010080c1e1081d8080039126211010340c0501030341a044144a08903080c0309148640d0012050265200b481c20a540013501803100c021610303003c585e00c07510400502945101e48401130440700d60b221214603080750003c006204d0200001c09000c00400c803036040d500d44030515110110315050440da2800361440d1719940b5407500308210005002d01c0440680c0007012000d0700e010748010b80003103003164207081c0321a8003045494 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 88448103 1250 88446853 88446857
    0x2503050417030c12090606030606150c12070510060302010f030906020d020a021e070305100903020c090901061e0317070f08030a050109050603150708270c0306070c0503160201 77
    0x1100d188010002000a5000c0d079100c0c04107a0780c800c001303050700059403001010190190000c50800c425500c000c101581d000700101d65401940342c84503940c0c02c95004010810406224240840064465980080040d540103404845090100725048030a03111640002030015102e8410312409a000b0740000040a11592025080a054a0922040f40c20070740c2c98500603802901c40c1c2100c218802034074920b0007405006082a00c1c155140c19a441100c1648501590340d5010b941c3c09043c400c0c0580c25a06800034810101800d1840500f4060001d50190032040c20741071200070101c50b1400d1494085952000444d1112a600042c40006401c90070003541d102c01c211500307100003148079000307500c60190010002100d505002d4414100c5800810150003076010390658280b40403994003081c0d0020343c91400c00f002e90382e0107810301008040b108800454222b044012140c9407000300714520404410707421a1815503c2d050200c0d941c2d075a102e030281c11900104503c0400002404c001800e040c018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 88449353 1250 88448103 88448123
    0x120d0b13060501080f0103120f0e03010518060c0a090315020c120d0c0e03060f06190b0706050702030405060d0203100e1f050102010c0e19031a0f25030504 68
    0x860119056054000000440950390310042c40700b507030072400c281d40180c4004104051581140c0c2c40c000308030b0492680ca418442091116a107903803040040130103201002d4003e002d00e0502010407102078060060906280c051080001d01c0c001b4020b0030f07a2444003440d03503030002d072500d961101b91040306c1144d4415801074007084460307004d100400892506044000d50307256108000350101c02128041c1107030381704001c61424001c0080c6da000a0003030304022044090022a00e44400181c024402050303160100781a0800c0010b2518800c8090f10300c00b8020310040c00942d6034500101d8491003107010300f5601c070030144440d81207040154040c1d13034400d2200b09651030440e100d6032500206107003280d010056000c0203090142c110200482c0000801c001c0c0002e10a500c527000010b0103130365250540b98051071110403803062204202218000440d04041d001443c03291507411003c803060101e5460080f20003550105100da68810004030741010b105d10055180c000100c000c07070180a0184c029914510780e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 88450603 1250 88449353 88449371
    0x170304090203010f030510050709180b040606021015080703080f0f040b0408150709180b060a0e0a060e060d24060e010207050103060e0c03040807050708070e0a0905120d 74
    0x30510055000c1c00505801c06012071440c41c0c65031400c100c4074000e40b48181410140004940c01006030802c3e00e115107060551a0f01c0100d050008251901c40681d001d070a01000045c850303004141704891541005003400103130290504d03c203904100707200359002e5a00811007000411154406092550030110bc818509030100b40d40c0310304d54209070441c403120140028204504c0f00108048091105000314061540c03070008005460580f20b8807a504d0036400d44080b00140c101c407988400c00b411401042c0640781d03c91001c00901d0031030f04061450003852100c07c04100305014000100b00514014002c1d49401003642020010b021000700d402101ca02154551050b80c1315550101c0203400d580d512007413466a100f000a1a250060340800d06042c5002c40a203d01090f0021040c1e2000c00111070a9603600e07545043d2072a807081d2b0b00050154080c801c408a4050004600745007128103082101d413207903c5107041101110280311000304517038010038070261195100b40207000c1d0150102000108220 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 88451853 1250 88450603 88450619
    0xc010806061215010f0807021e10050c0306090609040506040f03030902120a0c05041e0e03040f0b07021314040605060613030303020c060702010207030206040b1005041406040b0613170304 82
    0x1d01a5501c4110000f43c00d80e049140d64460204942d0418501c1c11300303c0c0d81000d105c081e4070b030141100001994000105100d0381d2030750401507103c3c54486c1c14010401380c0360101a658464100b942d009110f000048081406854400d0049000d130342c200c0c000d03069a80311540e49040c0f110074120120b05154855200d0009030742c0780324400d1400410a0003900a01c3d1481c83c2450031501c042d084144503500d4210030300c1448c0e128145d14621b0401a08000a121044064151460003181c0c07140c0040003080d04042071510300760002d8000203200361000303640fa20060312044103952500c1e0018140c0040e1900041c04107915421864200402074221341c034040c440030410b01503082542003034010030b4001801780b220b080d00700b2061fa401481c52000b142003100d10394009440c5e00c40984058550704115011940040121419100a000c000e20401103500d1889071140780e5581240c080d403040d450285440038900300340040b101c42c410181d0003d00d00c1810110b000125401c070708208c0c40709200c00d10001c90100c2c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 88453103 1250 88451853 88451887
    0x3020a06020610081b04020705030d020304050a0b0901050c030402042f04080f12030103030836010f0e060a110912010b0307270b0102031c05100b0c0c01080606 70
    0x80550241c0030b030349403041e6114840d4900380d0080000f540b043d190381103440b1100300c10002900c2c1c00c030781c0903136907002c40d041051035400790350083c8000030310000620080080000d8281040e030311603d010a030301c0c0d03107141e503003800c0b0f030b00490b025003543e00200001070044c034003035200380f8070448003485400450346805608105a41100d0344407a0b40f8800040078010f1120030052001c3c45441140106400286980065081d010610006083c442d841010420500c02130048071650754000f544003991407525010300d4280251840814242d518000c02d0144102060103000c0300c80400c1401000c20380c40300c2000500610580c028000c6050061080242c19528503500c0c4d181425114008507190b9205020503090032080e0b804020305d242e8910840780d00115140700741010030152440015400c840b400180e00754407036003140b41c1822004540740c0058641c103034069070040781c1448031040b80301d80342c9520410303611a00c518100142d000c1103c90b000d03980315101c801e5001e4000360955003803400f490aa40100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 88454353 1250 88453103 88453109
    0x30a0207062604060e0f03040302060702040c09030f240c0c080a020c150405030c0105070b15060c0307030206070f050f07081303240c0e090f04170d090c06080103150203040c03020a 79
    0x503182c0c00c401c08100c5d01001030444401450020310f20342071035540003030100d100b800d0000740125141c040001b841030044103c6001940c00c00900c165500e014541042c101010068003441c6402c08404d0342c0005e2000d00c01c0382800301c41da84402ea4104035548960000341c001151020840c403654031940c6141d19404c016001100d03800c1401038030349040904260601c0b000da0189410844207001900100d13858415113500051804210f1013504144000320f0280e10500e07102184038070001445408050b40003440c1d9100b45801d90700c455003c0c0359094101c0c1d141c800e410150500315028819103000c03400600080505051007401d4110540c0d42c0d588041c18082c0c0e80034644480025405d42e15079102c80c50040c9030b0230150a00e032440003000d01100080344001c01a01c4440c0ca808107600080030014070a50750b011071354000b9a09030304c40481c10385960140040c00c0e03045903010b841000c0011420300402d0454141d0394403941216960026a080b50001e410050042d181281500c0d80000940c591049540207 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 88455603 1250 88454353 88454363
    0xf0403051b090c030412030902100e010306051903060b030c030f070e01120b0a020d270c0801060b0405060d09020d03051206120d030e0c03060708040b09030a0207062604 74
    0xe44461088600500d0410007407580c082c8010744200f14190354041c0482e58800d40c00070700e500300e01d102018110003e19840d00020340159900c0082505150840703031442c0707008400da0703080c80303010380700c6041c4100940a0380380300383e90000c022020300001e0100e0700110714030140582203a2000340300310700007480c2c07101c0c13403120340d50076040450148820760402e0f1109000d4071031140a1802010180c4d61006060801001c0c4a110341d030105000210400c070381c021610103001c0b546a8800d22001140c3d0340c01000010200322500e1501010025031f048040c000d89080741d14030003500b400e0500e49002e10a40d44d200f043c0515509a030f0f0702c0400010390b24524a130454500a944103911170b40c484c47c900c410444040c5c0440c2c4540b01500c1903c0801d0000a180d40c42c0c10301c5450040380c030803111488589441c2411002941c140608020030800c158442d9081d4400c43c01a502d0b00f0003a100c92400b50748074420701000f81b0040c4c000002c1030107680d010380c45856801c20701952201c3c0819011152074030070720090340c045070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 88456853 1250 88455603 88455613
    0x118060f02070801020924070f05030310060311030a1509050c1c090213020d0b090906040605070f08041b0b13050f010201060e0103060e071a0a02010f0509030a030f020f040305 77
    0x200c050741c100169005806058000c601e0010010001038203202c000c3d141001d21801014001000034400c019074050329480800200e80c24018500181c0381d13001240c9007803184100c0310000400502c02d0041103540c50540300c00c2882c40d01d9820b84c40e030141c4080c000c6040c40c4002d500d00054079a03807a20440e4800c40c403a071649071303c42103501404e203c20441081d075808a28104030b403680140c1c0e83c1c2c0900c0a000181d11000590351076002160b6005009d034800840d50182c130040c1080010000403403c90f22440c4900f0003004140e41d441c40c1601e40d07040b4040c051002072542c00001d000a12404411300510408100c401002076658600c0b985039400940045441400c0d070303208012a0a002101c0e001c130034024002408054140481c015800c40148009011551221050248582c0501c00d20015002511591900c1d00030039828004551085d02901e00540c03070b01c5440c3c003e5140c0d520a01380501221000f031440c02d030000c10200d0117880c00120345c80c8860350800000c140482c60000400046100d440940 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 88458103 1250 88456853 88456877
    0x1e18050702011109010f080603250312110304030b06030a0803070f090e0c09040510030807031d06070c0501122d061a270a09050a0b040605010518011806 67
    0x20300b9919030760f0300c050a1200500c988a1aaa04024040c0303048445c1e1030070721115581c0c0c8000920308050081c0040d21502c00030300414500c41040c2603e82913a010b1480d00e0450314003680200c1d4068000c850300d0311660414007080c400100c0d002e10840d0800b00040c101c2e92042c074251034900a40d13006582d010041500000c020b41c80d00e81004461004000501c10740f00c052170208007944180c4074031001e403803240d5070f5040014114804c1c07010800246400c404902c0d01c41c400c601e0b000d0300c0354013080181c0701c2e0340ca080413590f09107240c100e003110401a4096050414949440d0040d00d01c01a84803a80940380e4a56160754049940b000c4403090b40c080c4605211285140030088a04440c00d641200075a04420500004a001010100c507201942406454000d4442d0a1000d103005c4689000c26445003401800040f110f6103908900c0c00b40f1071451041140003051402c00040700c0651140c5404a1418043e8600101c072010102c3c110040c11306028120f01d84018542c81c0c8120340c0d4000d10041810300342d4903 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 88459353 1250 88458103 88458107
    0xc03051210031112030d0e030f03161b030203070204020706090f031e0305011505070812090c100206061503060f060d050a0b030607050f13081c0305060d0803011e180507 74
    0x10306400c0c80142c81c4520380100c9a132035240c0742c3c411003548849064a601c1c0c5084450310810071603200c11000f50a0f1030316801d00f0800c2c12135a000002d4207000060401900c107a60310707005100305000c82d40c16002540b0b86805036003848060341010100742d8000b41d0712207000010500f07540b003400d60203110f943d0302c4030811100c24400704404803a0045200705454480180f11038900542508007100407814841d4907012149009041446078085039191017441c10b05101460400042c4100c201c9021284d0071214140b0480482c0e4a6104884003544501e4100e9205090b03403400c0c0007035400600c0070f0407030284503020501040c11a804441c500c50495074076001c02400800a2040d60103480048014200a041c9040010158051543d12403281d0b2800a1309900d041c000e144820f0040a44030140c442c092254681d011f80ca2454001e064080b07818180041d40c98a05011031003401c580c03006604d0b003141d09120780ca003004640114030b850b241d03640600c08034000b84120174040c503805602401042c103150481c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 88460603 1250 88459353 88459373
    0x30206120a0f0e03040504090f02030304140a051005032404090b0a0e0a03050703081504050f0711012007050a0204111803010527120d090c080601080307030c0305121003 74
    0xb0040e071035203082c0000010450120071101192021280440c0c448605d00f400184054400da00035854030000400003000018882101d900e0b00d800c44001254903906e0041c00540c0782007541440014000304005039143e8014010507004500e100d0b107100b060140c00003c50110380400300140c881c0549507007006410446401462080c4400c50080d02c10031900755000340103070251190040510180d60000b41440c40d000014150b40342d0028021308c401d082200c0c84d550305030790a851010004095444000c4503000c1405946d545907584d906218110320708001e8640d2a802c416030884440c040c7c5000840580d50320b00492880064695070380766a80a00144032041c291140c01e001d020740d05040804c002c0c035180c070b150304400c245040600c2251b4040f41394201d082c8084800c018500030f20100d213504a0905e40c2d840100c0c400c1c8031b50702201d2400c0e00c415045603190400d1160b0349035580100550700002e4402c0341600350b01c0780b01e030403c142000140c5c2c80d06c0106840403117022101c0000e81400700140130301d80305 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 88461853 1250 88460603 88460621
    0x30409050c040f0e07050d05010b0306041d070b16060f0e0d02070509010608060303370903120c0318030614010b1608090f03060a0221090a120306030206120a 69
    0x50a07915007481d000c40d10303090701224898600140890400120481c2c003403003c40380c1c2203883e01c400f00b0142d0784994801d002d40c0c1007614a030340600d2409a10329103102c00071580d1496890420003c002c2035143c074969503030a1b1b110500f034280d480c002c020b07682d00062580c0a10720340d4500205000c10440060b000880c50034042e00002c40c11944051001c00c2940c48032307504941582c0d581e10b0040001c3e0f40d240d000c64a144200140e1101d0701c451140c2c00d0f040303003408000c01d80c0700300e600d0741e5805090981008220307004d034000c1c0400b400006d440620042841d0003810040d0200b440f0341480100c0c80e010000e402c806410303992041d11041d03241c164400301500064001d90242c00848050b80c00d10300d4241c42c10600c1c10220314024801e1100090013442d503070b109c003040c1d0081c8500900712219440c115407004040d400040744160764400007a20251000220074805108409590080c108900691295004c00c1103850300c800516680c1d82d404070250301d03003034020b18402c0c42d4010381c41094140300325000202e4403518 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 88463103 1250 88461853 88461871
    0x30610030b100308090f010c0f0c09050117031204030903050a03020f1c050a030b010207080a200d03120902220203090706020c03070603020711120703030e040b0604120c051203040905 80
    0x510b040c40000d0300013041da400c181c0185c41c060301680402c80103031141b128040b07000d040a42c1c81d410603010445811101000d5401660040c402070340c0c3c8120803003039602c6003034889010f03800900c04540d001400e13000c040d90250080c40c012801903502d481d8107040c4440c0010640058022070007061003140708120020b0041c0398080300d40c4001d203501a0041080c09a2981a401c054691883c50040c0c1e00c200894005040c54005690241481c0d00e8070146803410034124040c00c1c1040601c000940c80d0840c0010724294143d1a00a0b4811007102c11070000c4c1f8240c02c040341d0010000700b841e03006100c00c61020521024140c0016540e06000c00010700e0902c40d58408000c5500400c0b00c44941c0c1c60110390142150f0343d0342000341e1641d40070b1810320b0302c018220310966007084034003514000d40c8100091500449000340c031000c50f910802400e00007522500d00455410507010403080045103003455a21013110b005000c1500859140d8000400c0b10140c134500080b660310219090084104911440d41c101101d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 88464353 1250 88463103 88463131
    0x40f0603052a1008060a080105070201150801020403260d05070804110a0311010c060b06070c0312050909180f01050901050106030c0206060d140a0c090f0612020f0906030c030610030b 80
    0x10b800a2000c000c0e000403c800c1250b5200418003c0e05e80f0100350010340300045c000d000340d20b04018002e00034840c10115004404a0580c0010100c0b13041c8211030030b0f43d4104401140514003440f80c0d0340d01c040c0300c5a0040d1060310420404280c40b03001d1040d180290070320b0756015414102810004802444900000e01c650510101000043c4e5141c411510050302030802e1001804070703040101c010040c1d403514503000000080c0701400c001d09029131170140e0707114400b8001c0064041d0002c0707985001c2c811425400290074000320380c0c50352006007148051429942100c0500c55006d001500f981d205071000c911a81d1a000113206480d0140282d41002a280c402480e503840d00c80000342c8900c40300f00010b02201e080c0092208000c100340a1104042d40028103a10780c0343e91120200e000700405010545185d20340440418442d000580711084a41c004180646a000140801a030305401030941d82d40b6100d0b4172403200e8ae546080c00024890341044080c2c0c080c4c2443c3d0b01b8019240800241540f50401078 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 88465603 1250 88464353 88464433
    0x1080c0a080103060b04090f0c0504050903181e1003090501232409100801060911071106041208070b0609070801060c031202030405010b03120903030711040f060305 72
    0x100c0351640e411660092404a805c01c426008140140540b550291035130109a01082c00d0101c0c4161480841d030040d1420440c60359110200380e2a40034907200b240140b04140d90108081ca0500e0048030b03691a00c01d114445580381c1c00008070585d0345807080e0380c01300352664058424481d0a100d1000943c840300d6906044d00801a001c1c005800010541d00d049181030104000e184000c044010103014007404981c03250503c55043c1d10000c0040c4901001076092840108024802e030040d48117680c04180d000d800c2004581d10880800800c0d881c071500702c0300510000807940003c0c8030707001401d1301800d0415a5004030342403140f03107002d0003040503016159160034012a580d02404860450341e1500c2c20f0a12010740f4902120003222010403825980e0010052005010040d0b0016101d40c2c0b04908030303480c1c0304181c050581c46001e100d0201d64541c1080c072000000c10502000d107603800c030380100001000141408003000b102e0b402c1c4c00994071036024405000001d0f1600c036402603980d605d40c1c140314000038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 88466853 1250 88465603 88465607
    0x9030e040608150c09030102070f05010c03060b0a1d061911060106080c03090a02030313081b0105031609080a0308070f030b0a060f0e0301090302210301141216080303010501080c0a 79
    0x1900f150b41115071010361000904103107207002640d41d0000e0040096655002e182041500d00690f1002940c1030751030240c5100d14039029200b008100c842d2209814188145041d0030f42d0140aa0060440c5001c096241803082c1e03030b0348030000c0802e415103140c0c00450529401d001805401c0c80e5084109a52040740148002600031080a5120400741e4140e941c940c1c491201c1810031568410094152101188140c0c801402d111a0000d55080c81e04540e40c0a0140c0074800c03e008a07241e03c00d0201d1802c0001c80c002c5803110324a07085102180c00c0c4034100a540d411454038221154200340e00203030040040c00103840c4d02080c90341c1031208515081c45034040740c0c00000c1e400e0096124000c144865124800c0e842c0d8004c99a20a4500005008102038801401d0180d12000c0002c000301d5030030561100c00d01c03920082e0003030b80c4c10b03100f884482a5041d4010014801e003c400c804074500d103407242c981c012850f5021400c03030300d0241c402440a16240d501d444005000407201400030301d110b031014400600e0b459 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 88468103 1250 88466853 88466863
    0x9191a0a090b060c070608010513050f150f030601230108040804140d0206030a0902100c0c0915030c0f0905010506090907030f0e01020408010914010501060f111002040909030e040608 80
    0x20340441400210107902c00300042c424429201c110380781d401104800075a15421031400c0c2d0480e0015149001d440c460109910100d80007102c08113030680d180ca020401c156030010061110300d10141c522041c035043d100020b4541102640011110f80740c2d88088150800c0c0d01c541d03600b0700c81c42030034010071030b08140e40c48580b02c0c000c03405a000c60742d8410031054030390b5035280609040d8903009421166241030043c0ba41010b004450400d90042d489a819a5006442000008450f507082084c032206039003018040005880a11100c03040005080d0001c4089035109207820300504601484100312031508500300d003601c80c140e000c184160028000492691948a03009030b1100c2c0318500040d03900c3d90a00c0b1346004080d040802040c0f50300c003240104015a0550009005a025402e107100200e20240100d082e940240a404005400b0240c20042c3c0d07802250452100100d0405039865048038100d40b4040341c0055110015060b01c883d40c1c1428107800c50f5100010314000e8805014590801c5000c50340c1d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 88469353 1250 88468103 88468109
    0x60905150a0314041a1b04030b0910110301031703010e01260d0203120f0c270d0c0312030e1b01050c10050105010801081b040b04090209191a0a 63
    0x600d000160240614400ea11140500d01900150300590820341098500341c00340c490360103840c1800f1004500808035001000c0d0b024914044014a41415503464885550015000b00d220344600d2174650b010004078020f40d07118007802b00141d078981d0b04d181010122024840490b5104040420050059004506180d415120070100ca00240300107201c000b280840c00e40c1200e4007601a400b900500b5650100080c081c0d510805c50f10503440c1c4804000c0d40140d2000c0d10b40c604103000c04c00c0001c003244140c3c00c116100c504409288007140b03c1c1e0f200418104442340f50b04036100b03003411400380100212403c0001d002d14003440c0c00c20420407240b254550710003001c0c0c824004080101c03500d0445a10900484504080440540d0310a1120244400113441d0a0082e1404254200008035076104001440c01c2c102d07030040c4141e0b0b449a2000c082c0300040c40c140e015250040d441341c88000c0940c40e071048180c040c3c4803858808030f483d107034047c5a200311115611402104141e240e0180790542e1810403d50076 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 88470603 1250 88469353 88469389
    0x150402090c07080f0a020a0b1008010b0103060803072402190908060609010e10030606030c0f17030703050a1704030c060c032318070f081603051b0a0504060b03060406060905 76
    0xe10341003070400340d2821758903690040c42c2000034000c0100809c0c9102220046603520002813068002c040015004d4847c2c030b02880c10f50358030074000c6030081003000c0b81da54180c1c00580701c00c4520382c801c4401a800d0340e010055000c20044464507595000e0340c044141402440404041d01c020b040c220006405948103100e028405c0d0f40c0617022400d16124103118800640c1e0015081140a549180520035a007840c0314042c00f0949820300043c024003c0c90070450113440c0349010f0340c6800b080340d0381a1080c0e0001e505500c1040100b811024031000803102c054042d50180d1641c0b00c80d0080792408000742e51888012104041c1803101400c064141c0f0031450b0001c00090040bc0059603030741c0c51510108800c1c6001030b000c0e00c0340a00c005031180781e10300080c007900c1c88002501c0704c07000705001e08207089610740300090071a480b1001040311869812141c0c0200700c0300600d242555555030000905845480d0048240c0c0b40d000420301880d031404d40304620003403040e42007085255150500003014501e854500c105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 88471853 1250 88470603 88470607
    0x1030618091104020714060610170c1b01051605160b0a1103070807090504021e09010c0c0609061206052202190509180906070f03020903150402090c07080f 68
    0x100b04200090000541c140141c42192501d515040400200002d0800c130302290007007102003082e0303051003561034004036604d489000c2810074031013503041c0f152001446084030a44c14001103010000b181400c0554046000010070241445080c0f08a0b400e0a171b140c0c1014000d04010104594140c54000cac1003980c1c000000102540c0d41c0d0320703024040c0966007808038121000004100f52281c01091443c0103401a581e0b00b8a0140c0703d4042c0001c134828017881c1011000c1c0c00d50740f2000d170309002008140c030318010b00d801a000f060b070350b490f14440c00003138010b20701050310201d0912034240d228049854244120009001c400d1070f00020034108403c0c0303250480420424000c2400c0d5032103d804503400f14826030f00601000c51004070040540c0c0003040d0381c07803040c10514029011161701c03103045030091081c94040c01d000d8036920819190400c0c84103658050507020b00040b900d603a020301420f01503180c0c84030710300b0302c0d85014410005905001051042c01c0001400200c005c038100c5410b030f48204140410241d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 88473103 1250 88471853 88471871
    0x20c011d060405060304060c02060112020f0409210f0e1c110105040b04090b010f170f09070905010b0301030212070e0f150913110d03080a022b0b0108010501030618 72
    0x406030b20480d0082904042e0000c10700c0308012040d4810303400c1c01e003140c0c00d80792182d0301c41c4e001c40070311032410746c02a5014060070060820752030281d012500c4540f103030b0009910030b250865140080e02c0410140404654599032015803240c1000607038022100844605503c1c10380300c01140c144540e50719024145980402c0a826140d0003a07085402825a003100c1d1900c0c0c55544880c400603194025601e80000c2a0386c40403090580070741199081601c0c003081d121a1950780c08810101804010035241881c8204180041e0400d11446010b018140c4245130325505e60441c0180101c14032400c089444650004a040100108102529802a00b00341600070310f6254400152101c0318886181c50b406980302c1e00780180c080340c2c2e40801001500c2000d6613103a185501d4104400101d17880400303000300b9130000006001da00b0503802009203081c10382c101180200c10444d0002d080c8948012411200c0c0c0d03030f8149000304c5d80c10524140c010703c82441c3c184602428250595034a1980243d040e011076141d15205c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 88474353 1250 88473103 88473109
    0x5030f0a0207050a0501050a0c0c0b04060e0c2d03030408030d0506010c0b07050a1413170307050609150a1503060207020d08180a0b0c0a0305030a0b060a030615020c011d 74
    0x250542d54000b400c40f01d0019490500700d0081005850501145140c081522019400b644050102c01e8108508500c0d5a445484d0a0040d0800480207607803402003900540b6240e0324410ba26101c0100c003030021050701d9a80c5440b420154244c005244281c3c018002000f1181c1c0c0042291400c0707031805400300b030903100c1400603100e02d00a5080100000f440c10100710541d0313030110280a001e00e10766902006070440344921401c0e03108450b02c41d000d8658862051101409070030281200716195000c032854a0f5003501c0d01c900300f41c41642c15910980000103100c003440301d000f182c0768010aa54034100700c2449104c0051020484074400141100d40108000c41075548641c0a00e45641e0002081e40da02c0007800c1d04c00e07030115448071a0501c14000707403c01141c07005149003618044444c08009140c1c549603502c05582c940c100900040072661100d100c5602c4d0385a0501038001002e0545000c03403114206507001e20004100302d041801c41d4001c1e01a01c060b03a0744514814001d0b1a20300341210758003c07540c08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 88475603 1250 88474353 88474357
    0xc03041a1c02090108060103090b0a1107020303030702010b1503060d03080403022d0d0306030206071b0b07080315030d08040b07030e0f0318150405040c0512040b0402030c0a0605030f0a02 82
    0x210900e40030a07101180038403120b40c00400c20080c0903641d107507240c1d0700e88005500306c0b8540c1da000307054006100d002400626036a0b00c015074011042e604103041c00c0c22a80000d146500440d45440140d4464201201f6418003100000a0b0001c13049060706500d806408074021220a60003d0200290318004c00c00303140c001d201c0300d07031030107030404103040d044003441d6500490a8081d0b5600c0e59910038207004000b50342c0700f80f00303040c1507035070041c4464074024080d1a407141b59a8094084445030050000028003820790f41c000f40207443c0b1868096880f4504140050080509211128029040b4210305907000b503009003400d0b03000364400e0b0794024549072928200c0080100c004862a1446001c1c0802900c82c00000030b84120b001090200c240c3c070901205204c03c80c4650f0460f51700e1100280414130a912b0039802541d00c039200c52130250b040805440d42c128030328405030341c10ba030450324040512083d420140480a2485d205949031000c0b1032a00100920a10009101c4064441e41c4400308809a41c2a01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 88476853 1250 88475603 88475617
    0xf07060c0e1e0913030221040b0c0d03110301051011101a030111040b0f09030c0a03030809060a05011a13050a23030a0f08030a060b04090b04110c03041a 67
    0x40b140356001a1221a01094203074168050301c62181e40001442055007440c64101072a810f5010b0b114100720640e0182c0e0039600709984003601c040070710002c944000014094208101c51000910613483c41100c05400c83c0e201e0141d0440d207080820052005446080c5107414915180c0350030105100c820b0491424014814070015082d410801c40c1c0b807888403c1001400741440031030003040003010a100c000911b00c0389206682050b0800d2100c8098a656040509100c03940502a1071414035180c00140e01c0d03400c0d9400881c00710b4560000d00050190801009030f0180c60040100129410484554035203d043c0701980010040040e0268620b2281200b031703801810060b0401c440141c82d80c003000c906101903002c03601c16191010506a041c40d00080c4511070503001208401d4030619900d0303020079940002c02518042e42c40b58000582d0700c103103034014002042c0c5144001005061038041000355920f10044403401003040c845104211800b00c2241d00715400042c85444050441040510b640a8a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 88478103 1250 88476853 88476859
    0xe0105130503030f040501030b0306010e0408030901091e1101090b030606070218090303040b0901050403050415020c1003020a0306050405060928110702040605060a08150d050a050a0204110f07060c0e 87
    0x72030341d244c001030804043d00a8031001d803001d205809020044c19541c2109100d5030104808600105011070004801517402c40b01c034100224103003e55032600308090185d604406010b10301e5140d28824410100d100382801202441c0c501d20a51401d0070f10221408090000d030312501000442e40c2c210b540d214480c3c0d200030025500b02c2400e00d00f0095940e00c9403c2182c05a0f080f020340000140b45900600c01c152250f40e040d103684d400c1034102580c14220751320044245003940304100c080916581e607000c03010b070a1001a81e000d60341e0b101d40a8000e0a840e050743c410b60003070703040c901880101d40e6840718503640481c6c02d00d0080d1801d030780003180c50490034041144000d56172070501c0120141c1c1e280d100510305203000355400e01076a0b03039500a0101c14841d0100340c4001555450110360b615848403103a00e095032004000301140d1071283c5426041c60482c0600715019400766160104505050042100e034158410b281c0e0b051510b9131020000c0742c41002030052108d40e44204102070785004840390f1005000123 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 88479353 1250 88478103 88478107
    0x91d0709181d0610081912171512070605070204020903010204030b01031a010b040308070209070905060a0201020408060a05040215090d0609050c030f0105150d110d03021b100e010513050303 83
    0x184640d0794403880c080d90441601d01020202241c00741002071b030204481c2c000150700070807883d2511030f150b2070301c0d80e00316401c2080f0402880d508192200b52140c1d0103644500e050401c0c038600282000a00910705030a640030341c1101008102640d005800e642d04a601a100542da414010000a0081c481e0741c0005291340349820011040c0b049064185849403100241d09010340d0305c03458105118000d03480300801540082011000500b03007004e4140d0441d6150804200701a199800210582c000c0341c4c8020050390701140c10400800300300706072038204504603002c01282c10603801280142007040c50142d0510800070701040b10340c944210304010729410030810058aa21071600c140c60709461a2214824800d4111082c0906e03010b1040310700a0f0650300144959400640600c180d0311020340007910340c680e808150b580540c0710030b8400c01e48944664040c0001c80861801d011480c000300010700c0c01540d55a481101c1c0642191410b81c482909003440340c0c4426070490b1040200866800068140c000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 88480603 1250 88479353 88479401
    0x6090507060818061303030b04140a021312050304050d14010f0c020d020705010815010309061103010e0f04030c031409210709090b0604090203030706060303091d070918 74
    0x4001d640e98010200f4400255001801c01011540d5400a403920000011095003e2002034001c0e405004c100b00064404108040505814030311101e0458804400c282c00080008000d4001400640548000c440e00305480c521615140d5603800307180581805511401d84180c207000740021901d160000c1880203101d00808600c4000140018159941c0580f0a5440070f91a050000c910740e000c0c1c42c07040c1d4401020340d0301c3d801c0f02200807104603c0389052650319814000820402d014000684501d28011503503940f40c062203a10341c0d080246010a0300090605200000354000301d503404168051034110280c54001c030f07040100703100e444030540c1c3c0401003021034001035601402c80c00c81d00091009862440d55261003400c00c4c0c0c0e010f032000401d0121032900103140381c60960700518090b4000b6048a0a000981d80c5c3c810031651207420a40100e0b40c2c0010070080b49690040802803812071b02d045c24130340d00b40000c01400382c3c2e0060140d034680c58540c0d0a107401c04420340d8080e08202450700044410090 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 88481853 1250 88480603 88480607
    0x1b0105070e0a060302030f0601120906050c130609080a060209010918050703060501020102160f260c010c0c150507140d0f0608030c070902070201030b040c050a02060901180f0609050706 81
    0x140c48901d5005800c4180c0000302d49000344290f0b8071610403031451003c5903907407038011034800d00e0400160680940d90854034005c03800e1413242c9403064440700c1c1405d40d2161031000388207191000c0d43c41441007080c0950180142c100200b802c03941b01d580501d01503241c410f14801070769001129085485804803101012407101c071280c000030f01440c6143c40410040c0d44480049090303100301f400140407070101400c0840003548414011000601a80440c045940c42842c59000c9102400310f05091410205008000605c20310980c2c81080301130030b00e41010030155031a02407001c110150900c659503101d00145180f0b00552070420f55088207440555181020300c414030044c280707078429580240c43e204c0e000c24800b400104403050380070118001c05d0b1083c40c04140d40302030f5100b91012810185c440340c2c40c948130780321030040d418947c8a13601d5494440d07807140002454200003c00c4482a03a051040b12081c2615031035801c0c0481c0e40100e00d12081686d2424090058810803d0040592140ca100041c041d6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 88483103 1250 88481853 88481867
    0x4140916080910181a070e13020f0c0f070803040f180608030d150e09210c03120a0c08040804060e063f010803040b0a0318050c040b030303010e010b1b010507 69
    0x522550201640b0205601e02d510985c40485035000401d401c0440d1307000c070385091441a4000c0452240261420201c00c960031001d4001b203c5100c480d9102c0c0c41c000c40c4561041c818500a0000080154100b500c1e049000c1801c400d44c2c49440e08183c455100307070038588410703007140300980401003c60340e07281552044100108003007800b5104160a80602007404000044054002e400c94030050005d0005800031340b03410812010103050000041041240160044c40035144902070405d0040c03032460400000401d80f000e910011040100c2e03076082000082011080c0c07000d0324540d00e05082280400c1c00440c00d00d1050a07038502c80d0940d554142c065880661a8088440f005840c45444c0c000c000a00059200028043c81000b42c10a1100740320f541c0680c400790004030b80b50315001c80d00e0030340b080b000c91410203040c50035100e68101c00e00c815000e003003c1c0142600d050054004524540c50305000c2e41c10000e06002d0081540000190303c80480c080511281030740c0c0e1482c000b04170754202040d001c1e002d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 88484353 1250 88483103 88483151
    0xe1005010c052505040f0b03150709180f0b01020a02150309070302040f0903020d020d05070b041a10051c030804020405060105071209090f02070b060d170a0504140916080910 76
    0x60703090406444480c000703070107401f404950141c000c00f41e54107842540c55400b540107100c0700c100f0001507800200c0480e2495203087d08042d942d00050500c030040c011200755a0111082415540152200001078030b40c0515414011040601c0540b640c8078514510b092050551000e5441401c005000c180d03400a648034441d080c1c0320b034013141d0024080318002c1e40c549030b18401030408600140400008142e10b8981c0c01d6010384200391510b1960221f111000c004d03c2c054442090200148400380a03904010108a0485c0f460b652510ba60500769075005049540060000b0f000d15244c801246076a40107400740c40c07035a5846018281d810340d03040b50092034200c0a10900307103101d007403010740c88290300244201c4000941054814a2a60300c031402d11410790f100746821101c010140c0d807600c6901d600c00c400340c400c00401744d8600307507a41d01d805014400324000031142442030200b03405210b6030024401e0b031541468101d047c0380740190303924034503213041c0309094070803041d82c030b0800942144584c0f0300c400c0e070411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 88485603 1250 88484353 88484359
    0x8041b060512060a0501080103080906040321020114100614090a0b030907050f132310030308010506040e01050112021908011712031923100e1005010c052505 69
    0x626903440f410424031403210300c119408250705c8001400401c0790000184112603024051514003941e0b40d071510250280078010301c1c400e00d400ba4240f074102e907083c000d108101103502101020750400a00880303030500c6900c610070a0124080050f5079a8001001f070302c00441d00240480902035503100b04046951003107900c4050390050321008106884c141c440c0a24002010700502141403084804900400c540240d09440080008601074041c0000d92140d1050010840700c65506241d0320b03010b0151441a0402171261400b07004c00d2104044860000d41195001d00c0c28844014078400e16400074800c100c15074052011072222446103640000350300e8103c03440e5003a4618a00d205040035910b030f40b14025240c91148007080401e444190140042c0a000501c030400550040305007030129054151059900031300301e46000f004683c481c125022001006d982c014a0040d1418003ca020980a240585414440150500014490108400c100c68035400c01c82d4140944484c240c00e0604505101d4584 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 88486853 1250 88485603 88485637
    0x6030603120302030103110607030516140d02190335010608090d020706050d0204090f050f10030309120c030b07020a1110020c040b040b030d0f02100902030c0108041b0605 75
    0x1d0791403292007201d048a03000b10303010004503801784c1005107a500514007074003003000c14001e00c40074480b172442d0030807224030076505030051001520703095042c6405070480b01c0c2950401c0d800c881422610440e6580d01ea6410300c1c115603072024140140a00f07540103024440301c0c05c0b42c041e405e20208660040107060352119100c5070b01d04d542d42c04202c0d41e0f0f21503985a240068000c40303010031245000354040c04902200303400c05810b0984514040c0c08480103004840304068451040c00742041d601d42c203190f0008509000c0300002c60640e14050b00444507440341428a41000d84100c00b0302103503a4964004e998803030301c41c070464240703214000e42d140703035004040c3e4a207942c000c48882030740392012001070200c1c0720740c02030401c4104900030003005140d005000c50b0003980f58080030520b943c00b0f002c044495021074035a004c040407001380013440d100481d40d012600924000c444005660f001070b0768a841402464201c06a03a640d1404103002005d031049c4400b60750342804c0c08254203400a001c2c05440d1a2103180305 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 88488103 1250 88486853 88486883
    0x9011503080a110705060a020307020910080703030e030c06030a0e0c06130909080c03040b030a0506030a0809090916060c2916020a0c06030b030c0f0f06070c050a06030603 75
    0x604000058440200300c04070400c808980e09005004960070510007506030b0312082d0765880400c040b0741c0320100000050700b0010318141185042e00b9004e0300810170b00c5920f00441c0c101224036a84901600014060011072155030f04d1940c4c0811200400c03102c040d00c021f171641003984103c005444041c54a0f0740783e010303001220151703040036010340d824040c410750220380961400030400d00400c062032041d030b04180104400190401c08000400040091a02c09943ca10317010702c0c2d0a04444001e80b0091082e003181400d82c0114440708261220010308a41a500944602c44224500300b40700b591038410301c2e02e1010008902d07402083c1d107019140200440c1c08986c0b403c0b407540704500c0e00d85032000a4070715a00701180d181e402e9903030088502c0040b0b004071403140c40c441d25a130707281080036441100000d8407208848500d080a1241020a01c41a1240d1661a0650340050a0191003040d9203014400104812050100722407500000f40009409560700c40e498541c0103026021900081e112000b41064035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 88489209 1106 88488103 88488131
    0x30a1a0610090302130203130c06020102030a0b030303040c060507080409060f06090e19020313080c0a03030c02070308160606050301020d060807060311161a0f0901 72
    0x51186864108100401801070381e4242040140038001040182c56110f01d04e0503039004003102584030750324030001901c00e0802844c05000059600300016025406500540c040e40c0d030b4007400d0010421a03c1403550368401070728024803003182d0345010400e0700c0c07061015200140c828203000345041e0b07940e254003027500e9050b000000c008004c0c090800c005600521070500034042d1120b45400ca15011042a11045d8a0740b01d0788032468002000421060441030408803460380800183d4503221003131182e55481d212450f046000c42d1605203407400c2c0a00004440f41201d9210300064a05410751400c500c5002021a080314410740719800414543e6007070000c0c00038014070034030000d41c05140202d510300d4050300340d01c070500b85442d1410401344103000c4001c81d500d1102010949400d1669403500c885251804240c07045124002c8003404007290101e04d1041c094040c20f4000d1140e1243c100075 = true := by decide +kernel

theorem cover : BRFrame.Cov 88309353 88489209 := by
  have h0 := BRFrame.cov_init 88309353
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88309353 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 88309353 ≤ n) (h2 : n < 88489209) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
