-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2791
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:45:07.960464+00:00
-- url     : https://prove2.me/submissions/cad8ea1d-db6b-409c-9511-f303968355f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 501798561 ≤ n < 501978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 501799811 1250 501798561 501798587
    0xa050c010810062102040e040b06100e0603181c020c1503190b03060a0902180106080712020d09050610170d080702010e010e1e1f0209130903030b01 65
    0x40140e00b410042101e003a0440e004540c100280050040c026102500c10750007520040281150303075940300c0d600700c010480202c0e400e41d1000003030340201c0c00710306100801500c41c040c580d48000c2511004000c0003142d40c00a01342c10340c5444041d094556201c000d100d8444108081c0b05088116039004401034200b0004240f1b80d44950a001260102c2d001c44004a0303510810342d60410001111a040000c0185040f01d8000d415100d130508000510002d81e0041080030b001300c561291740c1c940703c4984000f02409001d60310003d805140840c096034002d24840c02804000540541081580c00a0400b04d5103104000d9034603601034004c1c4503a00740c09038098006460040041895806540121582c03420a8150a010004100002801303207100798096040f0f2924100240b0a081950001564030340c285026040b0301100c140d038030b8440142c00034181d080140400d420340c01035102105404000d4100202c80340c0c2000d140d6100f0460703009103100b00041e1b18030a450000d001d140ea113000600c01290211f0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 501801061 1250 501799811 501799817
    0x30c031f1d03030429040605061206070e062d040608070504120314120a060f0b1305091f081006090b1806040b03010e0a05060f0106090e0c0712020a050c01 68
    0x1003001c40124010046a41c4079401030300c00260380d0210744c9501d800070101c01801c81c044030340c84240300800078142c10050050b0f101321103203c6c0c20390954000f0f94644c00305855820200d6110071881d1124182400a0441240348291030703034011041000301e1a030710b4103610841d81e1000c070016052100c5070708891039503080740980c6095418203080050705550190340d01c030701170b0912064006801400411800702c03a1030740328000c5504618200a1075040240285014048040e07079002d50108a0000c04410780d2062070b114804011060b00d030070305004541c0740150020310f0880540303a540114035003850309040100190310013899003111000140003210079503041640610700f09017090740141d8491142c403100901e90084503103540c13250741c0068000c051304003505405500f0040c0701c0080c8103000c21010f03c5c181c0194103231391f8980d03100400d00000301002d018a2012550404040c0312030500c3d00660303076000d424845824540b12064503110f00b4820300600780c1c801a844142c504007000301c10f024003104000282 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 501802311 1250 501801061 501801101
    0xc15070e0105030f041b03030c0525051c05030708120c070b0a0e0703140c0f1c080c030f04150f1701050f010507080304030806090c04180b030c031f 65
    0x44002005440f016001002a082001c0030a062080d03001c2c500c00f804004203010100c00d682da2074058550030024009440c2402124002c1013003120314500a042d04040c81c00400d28582404104481e00094a4064904810003500480050001c0000380b850714050b81d402910341825110000d403840c40181200c940c80c0e4180859800250806829500300c003d44601103a0702c2903440c501881c00070954006000c42c01c040300303040c8a10740081038444084a007a21540110303d50070051040b085000e0078003004001c0003207104800304900c580540410b21118050300d207840e00d41710410f1810b812540141c20090030008804091a411220300602550b441c1400210b010868015580c158014400c0c0743c029881000c120255078407a40032207800c9035106c10626282c2c2018100100700a004030348070707402150704001207003c0034298000e49049440d8402d540841c0041040e070340c40a0300c2030fa4101a094840c020f0506184e035002e02111584180c0540e20b80300030001043c440e0241d41314900c100305051004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 501803561 1250 501802311 501802337
    0x614070309150504051501030c09140114040b0a090509073201080601091a0301060809191205070b07080402030d090f0e1b0a03050a0f0b01021e0708030c1507 69
    0xa40c16402e2407441c00d1000003907540e00e03401d2460510091010a0036080380303a800100c100200f5619440546441680411035100d46c0110081014821300a110801c1ca083c44004914505034100c032080a4000d01074125290f076564840f03080e00c42c2510440d0301600404030131f0100042c2505000d0040d120780300b0301c16080000404c24400c4c0c40303164071610304001c6082e0002e16980d015051010007801c100150074200c10b00c1c40c07002085604280a18070001d26400081090201c00282c8070091094448424a4030f2840d0344d24000d031822a03003586414007605014440203d40c0c0760003840c6c407840312501d03840b04510b000d1040508140b6203c030a5014000d01000a0108042c0f58600c2c0007520121541d45003c0c1d102d08030710100358509506031211609000030b81c0c2007029416001680a4014a00c003800b030280c00423405402c1c0c85d04503d0f10b50042e40f103820804004149260103800600000f82510007203912051000d042d60f00c03865881c0001c0d4003848a22001c4a0022a1581e00030031350714083c0c411000d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 501804811 1250 501803561 501803573
    0x10e040b0603062b030507050d090e07050c010b0a030b060937020d0617060606030411090a06150509010806031915020c011b030f1a1201020d090614070309 68
    0x10241121340030340b00014200207200a020303241a40c0e030210000254107904145801410340d8004c010450300da01800894a003018041d4030000141e0718111201c01c00340d41e480800305e801780c104c44024802913494092121440c2c80e000750000180d401240c6100c0b080c9807040601c02100c001030720f800b048040359154044140c1c50f0384020400040c41c81c0030a220101500050b00c00b83c002d261040e40701c00e04d80400050220344103840e40105016600540c1c109a1b608804c200881c00b044801810b41080640054000d2130010145a800f000702c1c10b0000b907040c1c59201640300c00075010315540c04604e0004270a0030035a00401080d501120803401025000c1029041a103c00c00404004042c6c04007a2458202c460050301074688c9106d000c0020000140c80341a1001000241010640032a00e046507000001c24640680d001a50f54801c0d00c0658003404018001c00f42e41c1401d802040f55070074040b64001000354002c000701c190003007001049501d80c180405c0c071345603c05400d02082c189007164100c00120 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 501806061 1250 501804811 501804817
    0x20d0c0206270c120c270112031106070206010611030c190f050d0f0e040c0225030615050109050616030c0206040b0c01091b06080103061a0909030405010e040b06 71
    0x1482004280042e2002010070385070100c82c4061030b0b03000c64400f200c124040d80014110302c03480002c40702e94109080c2d0561014040b84030200703024201d11210f0041c402d000050740b150000c148a8504844d912040707260450401009552420058003c1c2c00100201c0c0c0c1c0c0807041d0b240011448010b0340c6030440e0303e8003039555044669811454001048803a0003407140031f010302500f1790707044007d440f00c440c031000005010400600e247e20229515171020705176410b080c41071901070b02054000340b5074900d6401112048030b040c5102d60300002500c007808000141c0501640782c6007041400014002410400050f010410682005000343c4050000543c80d88000c2e075082c080c2c503054102084003c40301c3c00818124826034021200a10b000242034045040c15800b070306400f8000c02001d2042490b035603071081020124803c550020307031510018808919281e20041500b44459400c803a0307401c00d50042501c2c080304442408080d000403404201e44d507004031960103640342c100c804102c500d16440000344180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 501807311 1250 501806061 501806101
    0x70c0f140c03030f25050708060901050f040b040609021f0c1103060403050f07050a1e02090c09030a15020d05131b0b040b090a030816060b090105060a121509020d0c0206 74
    0xa84101481700480900400801e0b07003e030008142e5a01c00e4950b11200d0b0751740f00a40c0c0041c0698030300000220303038001c0d5030a007030300455103c2158045a15a0b0300d0b450040e004100003070b41e2000720048440b02078541c00340c082000303494646a080e071196041c20b00000b01e041c4243d601b406a040700c400c020000341e1040c01c880342c0496498480b5103400311410110300c2d000f985400280750f040b140701c00391680e100b80d0140c902c4152086a814400c3d070f070b80355618129802a00079081d00350344422110b000090241032a10b80e9001c104100505001c4001100420340b241a82c0e044081d80c0340c5503ca000303211440320a209902c042e00051190300e4903004443c40944518415080001000b180003401641d43c800980021034000ca4080e4035070082c2003c072010007142000c1118090714144030401e4505140280070304950000b0304040c1001040801511441c8a241d0f030804403559586142c1030142d5034407072240107040303111001610b6000000b848021180003105280c190341c00841040001d002072106140c0403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 501808561 1250 501807311 501807337
    0xc0603010302090c04032009070c0b0703110c0604030e1e0d0f30020c041b030b12030a0e04140411010f120203091005061e0405070c0f140c03030f 64
    0x103036030300311649145010300d0308010300e07080328450044a47e0890b01000e40300600200c440d00e40ea520b9401080c0c0317508810340c40040800c541c0c140020034260087d80060b0b1105d106c035600ca4541114040c5a60030000109ca0880c049000da080182190600c010f0071111401600300540e24840c800c0001101c00500c003500410384192504003804025400503513561002e03201062100ca48052a03040205400700c56001c0700500c550403524440d8581401408000c4100c21440064224640012000382c200764041581046941a10602800301000104148400d541e1261180100c0004101c190340e00ba0084100340001801400040303010118050325081c000d090440c0050001c00c0255020340b01d0507524070307040348044100700e42050042040641c00604950800c010383da4181001591000a082d03c40c5000b6050b03041c05070390809900454020015060500d001011603440e407011103e600e01c2203814140d0b10090211404040050440000d8201e0103581000f840c20303c2c0307505a0086c084c0c0b00c464 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 501809811 1250 501808561 501808579
    0x117071511030a2015131704030b07141c270b0610090602060a110702102105010b07080702040b0604030503070b06240a0306051c0605090c0603010302 66
    0x21a001d00d540d19061050700007503d840f4621500007030326803c0e85900000141a10340701c07140d10b2100205a100079440c00360105040d0352034034120100389a180d1601250002034190700d00c40c07244002c80140c0003e500c61040b900541c1b5288600815101042011080303a02007440031141d2007520b90040072000c4400c84c0001020745031662040b08010240300440c610001580464041c40580ca0106108960503517034000d0314480c2100440d140e241c207118400050b0030103800710720139a42c2a0080c0307074283c509089860a00b604d640000740b249801c1c403c1d65000c202403d0f13680d0b0500800e0300c1540c0300c6201c20b810400441d0714085401c000c0d48500b110003420405c0004840c0210b41c4d072a44080c10161000d04429201c584911b492640c03580000820b4807804082e50006081c0c1c03405122170f1304450700040b010784000098540300880c507000300f48080c2c03d00d40c071003102080d0340d102e60b1001003106e140310004059000550900904690018180321150b400140448156444880803241160b5041e1080d2003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 501811061 1250 501809811 501809849
    0x7080c13090215030106020d1e090b13180e15010317091305040b0403110d050406050f1606020d06120b0f10120f0201174501050a05011707 61
    0xc60190f056803801800c52004c000031803040d078000342c641c03610340503903c4910f41035803024404402d0307440800c1084001a0700310818821400590041c0c805c0b484110014208651525002414691181600300c5e13400d9079a580709440341c00c00c02c40c8005084200e840c0601da54199100ea030f180060b130203000704140100107004007840e12480d90985038910300c880100118200341c500361080c01f1054030142d0004002c01002c10141c080030840e040540800d4540310718240c1340c40410f41b51500400800d40c4000c00505c5500412440040f1610310b60341316140042c0e40e900f40303820f064200c40032500500091a600c035a00302c001030250782c03103907000900da100c0c001440c0d644d2005040d00c1e860a400c040800c11411680e00308100807054001c096074400d032162280d1100b0348008240e00c0004032500c1249610441071140c010b03900c405a01711507003015840c1043e4282242260344c2402448a8400c0349039175650410400c14810701c181800f4018010311103080407540f55010707958500798065482d80407094144d8027 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 501812311 1250 501811061 501811069
    0x801050d150c020a020909010518030307120c0905030105040302060108060a0213051905130f0b0f030d230c07150c030507030f0216120605060312040306091401050903030907080c130902 81
    0x1000e0745c0c1d000341040502e18103800300c14060203068918420400541da880c4e180040c000c0140d0b4400c5120f0f90b1000307404485450707003801801d064240002400550407000c65262000c4c060300e0b1007240250000e000b55454144000c2c60850018200660b252052040f00310700c808419500c411a013049039085c446080c0ca00356804a0019a0700056002801c070404e0b91207030540c0d4016101031094140d003084003190b0201406401300ca1090703115456004030b24840c0900e0300072940040302c5074082d56018080c00381e1465075019a0301c2000c848500745c2c4034a408025070b586684800101426501d48245150242d42d806031540c01541d1008007402544001124290310800400c008511b60000e098120f5035249000e03c100380055206940a030300f454002103490600281c0024034081050440e45010725680f101c4000f030420600c220360b6004039200d00182c8c15000d01071103001f845d4580c080e680d40e092104002d0300c0d2404a40c0101d4454200078815151a038400d912540380c003c0c0d00d100420920700902c006 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 501813561 1250 501812311 501812323
    0xe2d03010e03040609210b0a0915050114030f01090804120302100204090207141209150d0e07061b02180a1503080301090c05040b0702062a010504030801050d150c02 72
    0x250340e00b8480424005a6981d025124504070303040800448560071105000040d50511440050501c80e0301001040d040d40c1309038401b520060043c10300ca00b101490b40844070607102c0c01e070701645006512080401d650302d8244110707405010000e008101c2201e9682d1070015030b0240780f05502c001805a24018141030081c04541400014018219621929240d0041c02500004c07002d45640b1542d04000d59841030004603000d9985120341800e0a14084a00704518400000c212007280e003030a201c0e80c40c8402050084e00001c4104001400e8050304202004295050b00e207680b6801c5a03a121104016855865070145c0c040d0f4819111422139640fa03e10f040a002c600300c68100901c803600c0c0000070700c09141c014606a81181d0070511541400380c0c42100c95014500030106045003c0003440010720b03105001b0002e00280050603100c40d259013002c007440110f036028140d21070b51640c00300b20030154800c541c1405030004450055004103541c1f15200b420f14050a01044181d45803a8445543d00811030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 501814811 1250 501813561 501813581
    0x150a1410020312070503011508090c1302070c0f09050f010e1f03050a030801090e0a03090b0a020a0c030501050103120f0206070815060a05180d02090f06130204060f0e2d0301 76
    0x16144c10a5400188250710910419081d04070b121303040303154035215822190160007400020403824244004011582440a0b0104042a801c1220f80c00150700814030500401e41c250400801900e000102001d80340300a1909522b000e0100050040e9808501d41c04d401c030425210f101095059040d0080300d004680d000580603104604051003019807000c0d6a034103a56507060306001030501c0c1c3c603c16a071036071701c20f500030003055003074609000c12440e41001c3c1c00e1007400c070300c1203901b02d241c0382c0c80741ca147c01d101da0002c1d6144d94460005000344000c0c032460640309110703807815003030716255044020346131903010700000100204040420218040c022210f001001e00502203a503032504024080e195900c408822005150070f108052902e1034040880e89802c0d8004e00070369250f40d64800c1800c0b91490042c51203030722606030302c3c610650744030920140c806005d864941090180c035604024000b100303a941c00500c0341212442c4600a01000c0070072403007000c000c12203061299600d1001034058500244 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 501816061 1250 501814811 501814837
    0xa170402040b120a0c0603060501020c0d050c040c020a0303060501050a1d0f03030307030617060f0f1f060c231903110607081e0c09090411040903030203150a14100203 73
    0x1414016443d0110750202d0440c8a220460302c16651054281e0070346545108441c00341e04507400240c0c0c242441ca401c02c10051090040e03840e510340d180006402c0307954a064070760042c0c4c81170001108058042c81554003428007420154100300c0010030051001111072007038405045500d109541070748a601581d61480401420390b5180c0c60040c030001d00406080c810811179241103030000c4580701011a816000d4404c000d80580c0c955603002d10403004136000b40544904218603900c2d001c003d04543d02a001030080c50b03035041c8a45000781005540015400180e081d800510300c21440c1040340042e5003d0391010301c000d5180742d00c18a08081c2d030071000701440c0100381d01030802003000050f409040c00b80b1401e549194052000700c032148903100900704403050f5084040406c0007509901d441050f003603009118603940e012400c1c49901007025200070903c1140420340200c05d1205121851884c46d002c0d09065403108400c500d04032940100c4001011941d00078040300320460111031090045403040f10200c0b07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 501817311 1250 501816061 501816079
    0x72414070609290124090f08100b04020c0a12020c040905010b01030e0312070e0d061a041803020303190207080304200d05150c130e040204060b0a170402040b 69
    0x802c00b4600b1000151002002110741c00c1c1da400c800d0310003030f04641030750640c10b0a079078410004000c0441e680385a034580c13014001c82e8070001482c41003000005015028000207005804013202419058400340c4180307a1013940140320325108060000340f0302d011250403100341d00040901140987c14400004074603500641000c0e0380300184181500a8104008281d078100050180406016240c1c084c10102e00108038010003c52480f43c450340e40c80280e500000c145130340305040785c0e0305c2000300c500c3c00e034046624800040100c800c1d4034187c410400e0703110400800c1040d65810340d800944921004081d80c80313050b0040001001c02c6884da050340d072620740c00882507640b410142007262452400c50541100e070054140004000d041800f01a44150340c000c0081a0090305100030001101c401072903070703030510f03801c1c42007412800d410041c050041411603503406c01c078107050061005071903407030300b060340d0b509020810102000d03480030036041204010011300000341c83c0c520001d0050b00d2a26481c540c444102 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 501818561 1250 501817311 501817313
    0x50408160e06030c180714030702060403170717130204020f130504020f04051002010b03010c03090b010515040b1b0a111206010b04050d151508072414070609 69
    0x40c518040903141c0a01c03605145039159410160f6680f44400e00d41d40000c0008400216181000441ea80040c500d0902c402c81050100c01e8404a400440c0c0140059100c2d42c203210505410185015440d90718082840780340c5846000076009040c0031080c002c00000b884000761030407a80720100008240d0060080d555020001084c820507040341d41c403a00c031456407610002d528030301442160040c4a20000303490030316141108008660314507000708000d40d503c0d80c840c18139a507402e200318000400d041c1c80014410001d420200280b80703050700070030b00401e1102c00704e03542d440c044c0b401e03107044400840800d40d41380c0b00c098040c50100310780301c1400074510515020350100012250755400c101000e44041c0d40405e0708100c4150307594000c2c0303c0c00da03004500300070612050902d0380c061040540100810005080710075600002c840901d8506e00001034410800d100441080c4141d4008001000b00c48600074803212408001030800c8001c9018810103590780400c000300309081d2369015070850400c100300101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 501819811 1250 501818561 501818593
    0xd20060709080609061302040e0c091603060b0c060a1808030f0117010b100e04020903100203090d021c21021801090f211a0a0b030114090a03030c050408 67
    0x100b40182030050003940d0000340c3d00365000403620b101d0312400304003604108541d002d00c00148000c0c1c0d0084d00d039014510501419455590003a07008191b003000c1c0074030720303807210308000e007182c00d01d40203820300e41e4007005040b98950300018242d4001c0e0090342c000610301241120b503030803480751701d500624000000c420481c41d52032800500781240c07440c42c610078079003244c00d000c1c031300329190704040581c85118034983c4290070781700d0180d06108140290005140661040c0002e150401e04030040020a40000400c940000203000410901c2d030b19000403c10000c1d45400d40c0b0710384e001008280e040000303083c400f0021290446040900c016002c5045544d04070806442c0c505480d0046c88a02140400d0400501c603400c01c9400700855100074680900031440800c1b541c4804582c50003941e11224500e49222086022100980110f0b0b80000c001407521040e4203060035030b00d107005c030380c03403002d5440c030800c4034010b40416012100c0350b1503d80050303200b060003000d075814040c030381002c4d0003032045448400050708 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 501821061 1250 501819811 501819827
    0xc1407120515100b030a0e01060f030c140f0a030803040218090c0a15050d090804350109020105040b090301061a0c060906011202060703090801020f0304021f020d200607 74
    0x30071202c03450169540c1d5030510201003464800c401c51510300b00001815500035902808840c0141800070445a81d03401910340000c0c2290020f0b0355650202c1d03802c0000c4401c900d901d10b41c013403040e1048110701c0f502c1400901c0000d1144000340c00c0f000c2c00000074045640712444000015440c04003801e203810010449581c6054a1000d140644c0c42014007042d411810010103e80032000c0d61100c0c0b400c400c20f044000640041c13181180d200d4028400880c50024144442400341e41e80d0104901070031000d07040100a0b01d02c100980c0340b6900d00143c500150340d0001c122420b0310142007001d5a500c0705a40402c0c014007541d8080e80400034290898405000c0c0315006240701d61040044031190385601960702e0316000203103d102070302e2100c1c14a00c0014200036025043d20390080c01c088001b15910b95080303080ea032107d03465030082c8000104003c2145009030b440401e5441c1206a092004542000039641d610780f04005000c2c0070034607090081c0d8001e80755940c401c0c01803e0040d10418105440090b00c514 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 501822311 1250 501821061 501821083
    0x1a010e0915040209161b0b10140607080711040c020c0f060301050a0e0c070605070804031202070f1502040f030809010f17010603050c1216030b040603030c14071205 72
    0x10085050590406014010842c015600244151440c1d00c405820300c100c400c0e4141c00d5014042010b0044e9450300d00103400c0502e45005104040c8980380218a042082030b95400084c51560070b281442d8003900c910065401e19580000c00c5a0340741e00c1400c00c5403000305941d11040c4d20a0616000c04404c950100d40100d40b0394064452005c19a031010401000b80002d01a030b68010490440402005d00c6132503e10ba0031000310984580382c103040391940f1050760700c00c64144020915280c103000405901008000b0441c1c107404085041c0b40c034550fa1415409204600680380090030b0208008891413541200e00030111401040c1130b03140d6030704d02550141c00080e070300c82c0072a02e11151b0101c86402041f44101c4d2f21607010311550245e08103e0158002d1001400e40d0011a409000ca608600801c284240c001c0c040724021080d00102440002d085d40c42290800d40168204003007040000d8004181141c41075210901402c6601080c08541c0741c0102035100341101880c6a40d540284030002c242ca070200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 501823561 1250 501822311 501822313
    0x302070501120204030515040f020604060e1503090316020f0414100e04050a06020a0201061508040615140d140322080105040f0201230a030e2b0c1a010e09 68
    0x381c5942c003503140480c0164800500385801541c02242c400020700360306940700c2e1141c3e036000456049a00411050b4010fa00044086203112003a000f49103420f402c0580d02041d1160414030f14503100074896224044c0003044174604010485d240210341d680c100500d4510f070050010026400140d010302e54070001554107481208c0c0c12071011980424400001e8031580d04240180380010f40350707484030b009601c00d1618000719540c0341d07800f10310f00c0c030481860942410555105406424213040078000ca41c8005401d2103910000300e0200002490b140e0002072081080b41c01e000711800360704000e00e2a20801009003400c2c000003030707002804e02d82c0034601001c000c0704891070103419403509500c0c1e00701c4a0581b0050842403c2c030300c03104019071242c0c00c01e03911500d00c030024400c4904100e01c4c452f070a802a10100001c03944496450320824010018204c0000201c54031810000030350030141000058001d03500104100081c2d40028481010002c4c4201e078140400c480d06580e40d02d50b040b16a90701584c90480f1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 501824811 1250 501823561 501823577
    0x5160e010e040516110114010308030a0b1302091905150a0309050f0303090f0d2001091703090d0801031a0405030f04060302040536151e0405073002070f0302070501 72
    0x403543c0141f103110b03404c9988100b165510390841c1c50b001e40680000f03255001e2242c07034030fa80c0c10762a02c41d005501955414014056241c801c5102000003050402101080b103a50b00b000030001c0d56030701c2424980094680056599a40480e00100c002c1c0400c01800350840c420511030016201d00000154843d500400a41f404440c58100c16915004c9a00002000860140901c0140000e0345804410380084100000e540ba81580d6015048000c1c515000030b102400310400404c0c000610442e18bc1e070794507103031540c0c6540c1543d4600140d1507201a02c0040900f0203c009410007004000325450307080e2a4a01644840d07540c00000c01a60150255502904c071981e1484101902c485c2081529150f8600d6803000c00c095025003040031400620449030300351040b001c001291517000310030091540c0c00100c04641c0041c00240030940300007030f0002080040000071058a181e511810101205900601c0440000d803241000040d016000c800b4003038070340c8128520200764000035020100c0d6402e88030491 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 501826061 1250 501824811 501824837
    0x703200406080c101106070e01031b0c0c1e140604031e02031524061309061e0501080f0601030902060f0307090509131b0308070b01061205160e010e040516 68
    0xc02c101174000355882c17940018041014940515562000304c2818500000e9181020b0441d44241500700f00f800c0109003101e809206000029040d00301402c45010806505035400e090300000c80013910450b80c8202d10018030301419911303401141c0042d078100031424540540401d05001000e00d440c0c0c100d02c02c2c45052901c031080c16405d4040f17071044012000c10910044522010080c245481651507845541048140442701460840038050250b4000008100342004c100c114480c014003007800015180341d40410a503a80000c405500001030b070b102c40820745442006034050300b44510025071160b80400c0e00424042c2040140d8840c20080e0f07a400034141d503c4081c820b15030425901c5580302074603421302c40d0108402c06440340e89403413840224990300d0f03500d0701c40e0129600701c00009c0701c5050200700100185644901480d41c01058202c04111a0a0840100c001c010312108488140300824410302100ea0261148406c2400050700c240035518010100e1813004081012007004101d101c48180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 501827311 1250 501826061 501826067
    0xb030a0e0109201807020a050118120c0c0e0c09010e04050702060705071104150e07021b120c090a05011a03090703031103160c1a0c0703200406080c10 66
    0x405007500045000d0400401044520310124103222244d0419803002d429551070080008282c825120341c1d01902040500d8a05039080d503003948806507020f02401c2500e8042070201c21030003100c0c02e181c101007400c07900c0c5181c60143c50030f00c1d61000c2120780d0802c08010044d2030510003030040000983e209a9000b540d9070070401120b500b42c4010340140c2c00a8001400039003e02c5c000e00145005c0c25400104800f40780c0003405540c6240e40e000510b00110b80e0401c00c4000040500e50031a041c2e0014020350364110a64002c80d411201c0907a118814540c60904002c43c01d0041e2250450701401c1d0312402d01d080c200071400381c02c00784100481300c10b0010b40100c041c1d03084c0068038081c0e001600038144591840d20700303c0d08038011100404090004000d9034451281030180107110310f00c691204040140392800ca284080a00703031038a042220708100013140f00c00041000c50a807a404090300d41031800c9030500202602109200c26042864264046444c0000081d0ba032020f07101119500c04201500e1b00407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 501828561 1250 501827311 501827321
    0x22060303030608010911091e0c0d051008060705090a0905070c020a0801020702090402060306150d05011401090b090d151a040507050702010804240207060b01030c020102041a031f0b030a0e01 83
    0x134200f11140d00303100d049460011042074112423035405c03541c07070201c40b8080510304c1c9a040c1c4081d203c82d070380000d400114031094020765a02c030422a15402c096454140602c0d00c80c50010840f4081010001c0e140900756103021002003d0b00c01d182c0201710358070701f10001a00710903603407000343d1117000305400c0080c0c8503105000702da00250b409051130113940c44c1c175400d0100301e80011b81426072110b251386010b200382101341c014180540000700086200e5150604010340e60240412190403c10046028085840104d00300c1d461403005132035640d510b80aa00340700c04010311050340c0c944000d0820b103003040314070402030746110303480f208982c00c001c41d80364960266494420844002d0201d00000c00040104c1d40f0065200e1604e1414019120b14190301e41014040340c4c80110111843c80e910300c00600b9030f581c10300c21024503d0b8940002c62a2a040403207450000329441c2000003440c0d00000010700e0680140400440e01c40020100405140c890644890a400c01c03909a803c480c1340c400b1154090b2414018 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 501829811 1250 501828561 501828563
    0xe0609060d0b032e0b10090312031121010b0310031506030602032706091e030f07032c0d02040e010213030506060f0d0c050f220603030306080109 64
    0x15080c40e0107812045500501000324000b503160040500100c8400d0f2850b0000510011003440c0e5120307010b030254034004580801a10764080d04000c2a14070009412280080903240c00003803404800010010480213064441e8209204100114204480b130501d024010081c280405d041c40c6c907681c03a800b19440500045524900f0901d90090800105201440f02061010107600104001d916074a504d010b070703442036580014020351160320a034224141d082524800300064042c1c40141008940e0581c1d8044075440b01010100c61108070003006001c004441c21004100c4003151100042c2c10040c01c002000342d041c803540d0452485480102e03020105074400400020300b000741606850302400014038030318520342c080d990300300310500f0500207002d08072005600c04c032f000309001e01c0d0034014030030000da0914519000301703100d5a5800006080d01d40c0e160079204180c1e410388075000958002010140490400c28012400d4118001d10310040d4200d8010b903400798605110b10703542c4a040c90700301d0780c000070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 501831061 1250 501829811 501829819
    0x603050f0711071a07060b01020a0308060f0d0212060a1103090304091a061206040b030a050a110a030f051507090b1914131703090d1e060c020309010e0609 68
    0x500c0140c014101450303042c04a4040361180394035070343c5060421444202d0a1260480032072034504202d02d600403499030710001e1024280c120100d40c0e0240000c003001d880300b440b43e8482c0840303009030f80310f402c504e80b004c54004110356034a80c04507801e20307191942920804203d50512081080d840802000c0764046d10761000218641468280b85500071f182c1213034503400100600700641e142da0344603c0644801c6208240401e02410010300300f00464040d00c05090103a080038600001103500070840d81d00a54100103041030040e410000590900d0841d04005c10700309281d4481001d20900141040c040a00b86040070f540c3d840760501680c10a010303124442402c00c040080300d5a040d41d120300c1c0121000302d0f050081301890706451410386604007540c001181d0070810800c0006041c0801e6080d03103d40c0c00b0010703628004103500441c1481540b80400b410b6480c800c0c005032503064601c00002401904400108407224000d00002d4480e03005c80046400210010b00702d90040c5000800c031009804020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 501832311 1250 501831061 501831091
    0x2a2101060b0d150e01060c0804090912021006060c1709090c040630020c1e0a0314090f1c080706050103021801060509011b0f0305070c0e0606030109090609060e030310060305 76
    0x6102100e01f024240c100300c0c1c90301000d120009030303003143d40181d000036441808175104400302d0101c006d240442406501a90030b0901c10104000354202040c1080550015042c44c03086130320f070120703840e139119035030007980c20100e40810001c44020800181050b900140d468907451500c00d6020a401217081c440c1c20b5018610458140c041043c2c0c1c3e004000c24001502561180c01c12240c1c0101024107c0b00311200c190403451846042550062440385451045490607041a4010000c1010858440750382070007601080d8100c40d00c0c8a4802415001652201c18207940301702c00d240c00b001601080c44201c0c00340c120030426445081034000014141c0714190303905420a00003100440d54981c802e801804c608030306000000200c1c00340c0c55401038041c0a5120503a0305c10f034514041f100003020380e0204600360041d0041c0045956201e0880e41180d0194102044103041410500010544a400145281d182481ca907071219404030185214070401180c0140d051ba85aa00b0740c1030381c00072207030410701d680e5030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 501833561 1250 501832311 501832319
    0xf0c1c080a0b010c02030a0b0106020f0105041226040f03300c090305161406070305090607150903081b1e0f040b04060509032a2101060b0d150e01 64
    0x69444221082c0b8149130152905203960082420310018001c142c0e4810000d20052084c80e070100700c544103c0e22000d000f0480c510301910344441c4441c01c0c09000e0100000310198a40c0100580b154400150030078002940e41d04180c64940651410110200c3c0032030080103c1030704c8a004c0c43c0c81000c2c030244c10700c0c0e89520000d00c01e0560b4001c3c540c5042503003c0c040040e80100103d90f0822074214142c04451b820b1500381e0800e04500c0002400140703039480340074100010700000b64000c0580d64440c0040e160342da29840306241a084000326110103c01081c40c000b0300406040d03200f64034a00540e00b803983c0b265101291041c3c5045481050000003202060780f0002d22040030250003049031106142e50b150030309468000101d4140d200d64400c20000364041201c501901d0140841802004d05c0780062072444c03564039404035460040d5007141e211b1044482140e11010841100304440c00c0b00c03c008110498880d15281e500341c12001000000501e441d43e18854071609603c040c0c140d0740c1e401c0283c0c100d6860 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 501834811 1250 501833561 501833581
    0x9030516031b0606050306010b030402060f0a09031a0703051503030f090f030a03021b0d0b0a020a0c020307080d12060806060d030c0b1003030f0f120903050c030f0c1c08 74
    0x8403008034100304040c40c0c400420762210700e6500e400e511542c004503c10b07141c070041625028041e008640c0c00c00d020400d100040e42c8000c1101c4811312100f001070f8561020000c1a10103404c0c40d03102900d156519485164281180d074120b42c07241c400c0303031030420260b152a006181c5a180c1107121a406520401c40f102e0020700703e101610003031000401c010005000701e80880c0c10710301c400300210702603400224034031803070020f1030002148050103440081301000f0507124000f100201401084205900040120945210f00c080910841d00501110302941d43c82c24081da6803038915880c0000180d4900361659041c0043c0221800c50f42104000c00c0c031a15180c0403c907115080d51011811b104c2d02c0180a13002404011400348501a2503055003080d502d9401c002c3c0c6004001072010342080b801c0f06d12005043d030070460f41001e0301c140c0c1c0d0300020340341d280d0300c2d095515124181e07410240d403001089441140c8011001003d02100200607256048109580000303030b07020555510002c03a189c80001100304070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 501836061 1250 501834811 501834847
    0x70914060c0a0807050c09010b0703050a0e1f020f100911150c070f0302040b10090b0c151501020115030c051504150305250219060209090a06090f090305 67
    0x200350070a42c0c00c01da01e070369543c0003203502881c0121816008403080101c6403400320710f16401000e020030514030308201642d004000d0701c110300385c0e9400d02a2094003810107440c0d007121072405005131035000102001425001c0c1d0b443d000c00b5180b80c840e100d640141a2092031030301a0103407203503026000e00e4036200c0d543d040190120a034418003524160a0002c031029038020800385000341b54540d0590107860031401070100b41d81000b40300a00400000400c43d030350586c800c2d41c0c2012a0f17100d9290545901c030340004a0701780004000108040c012031018000c02904031002e03c44569002d80080000d40c017038120700703002e00300c162002604225500e2010060303800c04917008250400f00d280b00c140ba054850075003485c10034802a042d4006651442001044d080d40d4002000c80901c440d480e002002501400a5032403d400c0341c1e0158603c581201d40c4108602d940590711040c1e0014603070240d41c50f26420344e80091103a44140c0d00d425040c201ca007d40d0b21140e110b008081a0513070340e05842d00702c403600b00a151751 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 501837311 1250 501836061 501836077
    0x30c09041202030f0f0705060a020f0a030c0509030a050f0c0904050706030e1608030d1a030d050d06080706110d0e090a0b0a08010609060306050c0c1c02010e0601060507050607091406 80
    0x40401c01c19030100004c0e01c80240004040092155103404560508914100009003408000b5104008031700d07190b40b45105a9010311420724001c126440303103600071240c5014600c030702c40c1c0600c9007062000c01c1000120340085c6036001031080754100c411000401001c09010b9070302620940100300140001403003074002250201c204c00480b050461068201a17034801c050348500f03103507007010a002c1e2032080780d40641c0d034250f84016600090907419100180e240c1d001005080240304000829810007415504610001c02480c0c00b0380d24102c1e695600038050400921140646003d041024120680500070b064081c030000780c0260344540d585035420004094284041e94008d84c1d4100000b6032034824090310300a0442c402001c20410f18620b082c1c4251103000d48018400003090080400542c40000d8600c11f0400072417214105080720030090780140703000314100c0b0007401410000308001d5007007001001c00a20600880d200d84e039620000310f40340d40355400380204050b03014180104900c1c2241c042d04242e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 501838561 1250 501837311 501837313
    0x1710062606062b0507061d01090f18060503060c2107020607050d1409010e07090b1305060d050609032701080601080703060e1305060702030301140d060e01020c01050114030c09041202 80
    0x290700743d5211140740c1280da91001d8001400442c084003a52004041080914021b091220304d9904002300850801c0d0240280d010b40c64803128641c0d500c80043c0c000c5001018040e00343c55039800d291480745200d60002c01e2601e06d15501c400e03910200454000c040f88602040d030701902094071084e00c00c982c258480f0300d08810017500d440810500081800f1201c0c0503521000001a50000300d201d050300f001c0b5240d0143c007180345860302c501c43d603480d030380b4958007481012a000540c4d541c41c080000c00c010b1400d000500386114500400070341c01d800000030405000019814000b0f43c404136030f000d4220300e44440140c00100000041780e525401104002e400c41400c1c100411884d441d610a4002c200044604296019280d180d400034424103022550304443c141c8051403443d8100840c14001d48001c000b440d004000501c1040140b00702d65100f250101d41c510002e6507508010304140f4040c00003801000b08017040212001640d140000f116454030364080e00300320481e5a0b80e200d10003510601d68001040d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 501839811 1250 501838561 501838639
    0xe0f0415050621010c0207230f0607170a1d0120010b180105090f131b180b130b030d1211030106020a061113171006260606 54
    0x1c98400d100f42c8641c540c504500008103041c0f5507400078948103c6a203d60071240f01d00e650f101d500081c03070140c1c6d050b1140c19580c0004011681000c9002d070b10441e400a06004c030000510740040000a00400c90065070b5550311101520309000c40301a4203100324501d02203002c50310b00103007903201c1c1308110342c8916141000184404100300441c00b810416001e0160885650005102c246002e40c400c40e0400400d814401d480d141c0f2417003103044800e1b00d95010f00f900400c0c0160448600d68401e00c0b038080c11148800804070702c403e503242001f42c805562418450148000b0140508003d031041d60b580785401402000b0303c3c00d45500654245152031043e0b420662a41f121807000c51030f0000a40c000d0819a009051109036800c1220889207202100810103108011440013085c07803180c908182c03004801c0340041d050004801900e069480c3ca25404030606000b000a5070503682c1e0f2415104040c07030361041d151045070004846d15080201c40007a800704540e44c8010b140318214001c0c14441500c06c8152030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 501841061 1250 501839811 501839839
    0x2010e0301020408010605131a060f190801151106070309060e06090607111902040e0c090412120b090f0402010c0506040b04031103130b03060105040506070c0e0f04150506 75
    0x402c1e0f90040c0c004100580d1070310760810007030425003008080b5040e903450400000c401da44940c0c1c210345200c2c482c2d03442020701061101d2001c6048044800c540020b114103000a80e8208015000800034850702000012042c40107070703910700400102011007001c001038940c7e41d850071400c0d40100750f11003055501603038a01c5401d00107081002294050202140100103518180302c0041400c0c0702000c00411075044201c00d6002500008246200c550381280d020030440c92039500a8900501040915404407542050000340504072000c2e4621a00503601c0d000700010001401080d64164641560070840d0b1800181c00e00404810484e0003e1051414400c0708589840b001d02d4004103072010b440c0108150140001c25030000414040b9080440285003850300344c504000b02003110b40720b0f25180c40c000000107402c50788510200c40140900621143e26507025003401d00001415009400c001800304010804503100d08404078400c551182100700e401c1d13050341c50100a440301805035a000300100c03c01e91 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 501842311 1250 501841061 501841063
    0x90c060f050f210105030f030304121101090c08010c030b0a030206090f0d0b09070e04050c01080703061203050309061005240f0d0f1b090504090f02030a0c090c0306180902010e03 78
    0x101440100c2a0000785556450f8a0003035408010781c00184642d00c601c540b0041d5810200540e07502542004078210000c00c540c070103903850340c06408450742551030a040003040202c405044400d491043c0000c000080b1118016000c86403103551042c0d200c0ca1801003000145001d02c01030a481c80045d000850300c2500d000416146100c69000301e0f545202001004103241e0704003c000002c0856051440442c03d10b900d42c140c07504038405074141041860b900184030640660000310081c4504031002d000c05515080c000c1c6240c100f0b6600c0c00303450007107001180305440480004030940308028045400c24000a044c41c541c0d60282d861400340c0c1e90240441c0004400c044003510704c8001d28040403c02144440b68807084880f1800315442c290003440c14003655030350040060095540030ba5000034000d40d036003480c0b600c544410340001d5040c030510200707400b00070f0884100c02c04c6500c040d81c1401440f2040c203094040d0b1320306014951034501d501d4185080004150080c1004500606225500d10a04800300b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 501843561 1250 501842311 501842317
    0x2130b03011e0b070602070c0e0a2712081806070f030509070b0f0901090312030606020f030c06280c05030105030d05090f12030f03040b1603090c060f050f 68
    0x48021000080300410a48603003034404100750040c508071840a0b41851499080c5000303001000e45001d6001c0741e08020040310030380480c081e1130f1071414001249044034112015001007071095143c0390b400d1056031141c19480012500107580b0000c01c513082c15450f001207500c1107004080b030f85c04500168444ca94260b0600c98240a9489641d5082d80c0d080c6910010382541d001030040e00d42c45d40640001c02410111b842625856488107403403544d9581e02000483e01c00255420140228040429204140c4d8040d0b1002048809039020b0351554280007082ca0348a005980410556401c130100151210000c00c3c4005200c58041c24003003034100d50050308204881c00d49202c80b0104400100500142c90104804001c0301d03000c1ca00285858010400310303c102d0300041140c2d00a03801c95242c000c2210003801640c0c50040c0000c40d039038491038a400d2161080b030080d50b0200f00424054410014607100b400b40315400c40d04a61b132032078201c0c41c1040407219900b030030b6401020003d00b4050850810001c0b001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 501844811 1250 501843561 501843569
    0x415020a02040e150402060a030618061505160f06090812010e06040209010203180a050d08072607030f12090503040509060a0e0c0d020405090406091103010b0319060213 74
    0x103014a116901c1848115030518509040f90f50144076500040c0800c03c04466010f641552029141e580c41041940600601c0d04843c401802c1c2c682c10280ca941158411780407100d0ba41964107103074028030b5041c2d07441d1090402c00d00c00885000c80b0140811800d185c0b08421504c10700002a18100c103440d5015103802102c020968281d5100040013040b6409401b41e40041c400c40d000c61900e0768402c0040d54074854800d00c02000c50781b03661a0322969075089010b00c020000584903642c05811071410443c0b951001400b202e5180040090038280d20886800240000d426120b4510741021901c0a85d502185c0344003080400082103049800c1480038014040041d208400542c2c49900700410800802d400800c4a401480300800421030b48040c540300c290040e00745014980e44d500c0000450010b071249800860f00708101100b0700081000031740c801400207018911040504900c0c23002c242c2a18400208a0750650107881400d030243e40c01c440d0660346501c0384500500d024810420049620650740c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 501846061 1250 501844811 501844813
    0x81905010b0703022104052218120305070801030206030417180301110f040b0d0213060503010602061f14011107030f0c0b03010b16080c0601090605180c090103090305041502 76
    0x656082015010410000210179981c800c00c1da09850b14500c8945008070700c51184108061506140720415100a01501d141d40400600003030486081c40d840480d0070f4035040319010f95043c80c00c112144240300c2c10740568030b41e5640340c41d241d2858003000110340001e40166110706180348848042d002490040022943c00c940d5041d07040c903281c08240c2100c540e030090040d002c5007080300c20045802c80c400c55064899910103a9260b11440c040a0004d015001000c01408040c1d4000b184250700000594101c0e02e1581c201e80c6950703108000c8031100e8201e8150100c0307074102c0c510305112582120440501780c0c2c0c0117160043d00c010009001d649048003ea0056610040440100c1d013403100111602000d0029040183e18551401c103209a59102c4c04a043c01c82c0017010342c00d40c00300b10740807044400380b2030060111030352561110001350040c442442898860031120070440159408160b242c1e01c5405004c02c0300d81440c1120005501400601c0804c030204007040001290080440f2080003450110398 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 501847311 1250 501846061 501846067
    0xe1003050115051c1808040905040b010510140c01140a0c020f06100320040903080109050a0605060409050c040302060c011e0212130212070803180105090907081905010b 74
    0x861421111000c030181d64108a800c1151030f01c0c04c01c482450808800d40307600001070030400700c508144020b208101c000c282001c0000c002540180b02c2d000640140c0c0200c44040083c0da95000b00f2851041c80304600002c0345101c0040b072323402c410030030141025590840010904e05041d184100c8040011211048055520f1030101040741d03040000300c1d6440701c404000d000c1802c214046400808840c4802044405c1e4035410307003000d4089034410144c82d070001c2e100b0301a0f880b1524015110840034098654054a084d00040740c211441c001c2608980b00900003910301400d1550b02d1001d010000c10718100348108020002c01601c56500900300e902d40000001000c0721034802d80d00c0c400310724180c51b03e0f0b040d0041c07000031000c8602d801039030b8004100b2640780c0e882c50030754070116090000c842000d5406015103000000d50380004001400e1441c01c55905044168468005543c1d07402030040d00c0c3d0308422007000059041d80110501a003107080d200081d21003001034403a00b000d84000341c000601c445004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 501848561 1250 501847311 501847319
    0x414030703091502011e0f020d02031504200a050322050a15050f010923011e1703031b0408030d0c030b0d0b070e0103020c07060203120c030105060f0a0e10030501 71
    0xb140300030f242802103100070300580000762052543c0310200c48915103255960340713008202e207c00d58100c4030175449000065480345130500f001a82640513548050042d03040010b400303c5801441040003214402090840c00c01900c5001222140c000401c103c50409040800d11000d007004850302e40254400e9009007403800c881e103408081d000450312040e80d10740c1048188060101c0b005550750544076604400503041e150040003000c00b500480d03810070060214000071864400c0d1715071019500280610a4440d07503070361000040b991502182e825920740040c00032030105074502d0a05188500001e80603400d1946a0405a040d5403010040c410b0a0b5039135881c10911541500034004030750021540b81102c5441d5031518192000010160820409018884400e6a0090781070f11158100300d01200c0320242c40d410003a569a20186c10303030210395105800980d1903080d1000302c9040e200003408a500784110810030705e956410070611041404000c000140c4c543e145c581024004040035680860b180d490 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 501849811 1250 501848561 501848579
    0x130203011d070504030b04050102070c08030406090501020a08220306150e1f0509071206140906090702070e040f05030d060504060911070206070219060f030501150215041403070309 79
    0x10301000c03104041d40c210402c1003054000e0b041c0d904417034202e8503015030b0780d4952500600a03c40c000000b80035540408c3c0200c1c0c04e1400201030300130b407405a2940d0f505252150010faa0780d800c004002001d00c00d041200140e290784550b00d408a001c1c02c030400300340b00e940343d03a1040241d901002c201a1070048915040228906030344820303400030917001081c1c1382c642d146180359503500b1503801190300801d200b40110380da8030310902d005d01440302c481404110f141c6d2160716000c01c2d0034a80a106201c0c05000020032076610384010032034022075281c0c000300402071800c459580030010003032060343e9020755025014003181040c001404008140d02c030004580d400e10341044110341d559089500c08529110702032026148400c11180a00c0d01121a1920ba1015100080030400300f404282c8580042d60f90009045d0381150702c80c08112141d440c1400f80f6a22180404240e10a0b50080e200507800340e26409000424901e0558000b0b003e07441d0808070101d401200c500e107078403600342200040e40030f031400c014042da = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 501851061 1250 501849811 501849839
    0x507170a061515141b070e0105040e062a04060c05150709050402030a0615091406120109020c010e1609050906010b0901050c030405180612012702030c13020301 70
    0xd00c0401c102d0a81c201401c819800001e4580c05081c003031298038400c0212014815107003c0c000300640c203103101d000200516100d504900c14101525030140010482d4502401240c5420f000030000300102d507038031954580803004c4080b40031000b407508040e903014522408024005041c013901e825503554400e140680c81e01c034004038000784182101c0d041c407180d503512240800860b54100c40258803615018045402440c15a001d05d80302c1030001c03100007102e80c011044204488001d02900030340c101c51002d1040754810b8002000d0300002c85001840241429800341850803010340000907004500c1100910341004051004215030902c1c90400020340d444c042d007540003211308080d02d102c0d4500702a00002d4020790621905110000c40c2e58030042c2805c005076001801c00500c441e4991042c0404a0625202515100e003d4182e2036151400c0d6001400b80145c41c519003c2d01e0f61520320808200d152441000300d0899150280d4401110762b13a50b91100311800ea1611000141e99524203d00307208060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 501852311 1250 501851061 501851081
    0x931020c0f0a0305031b0c0a1112070501090b03180615130209090f060607051207060b06070309030201110a050102031f050a0602060106080c0f0a09031101030917070507170a06 77
    0x580042c5414001030b034007a040e2500b0900003072102d078035a03030260144d001c98018200801359910a010300101445a600b400400d480002c0c1ea02e001d103441e40d500d895490349860301034140495810001001900c282000071984070f10031988458078030a840c5042c605040c41614840368001d0806a12012881c1403035141c00040708005045140c4103121002c280d02810080ca0f56000d10f210750001078040d00c0b107004a071481e90b8001c054a16825038544008440d400801041c4c51641c902100001c050826208039410107401d6160079082d1803569004645403105003250484500905140a001032807d00256004405040c040b0703402d1540e05c42c841d0090001a840188901c010709010008545c010400034150344152500c1c200a55a0445a5801e84203050307820502e600001000c214240c1c0c840c513541c0c1a24821400088000003050046041e18403001c000362161072101140e2a14040307000c0280005481901517070105580c0c1c07003280c054845006020340c019005901040e0412105224880101d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 501853561 1250 501852311 501852313
    0x30c071a0a0c0507050606040c1e02061906082521170a0c080307180602060402090f010803090d060605030102040605071a0c1207210c090803070203030931020c0f 71
    0x444403170384078150b444c0c074003903c40c9000f1555030320820380c030a1042c0e141070780c640f20703030030994040c64808034009544010448081c00c449010b40350390000d9152901038181185c03030384401420401b008032040d580b0045901b500394114502c071500060000e9901d1b00240400408554542c854002d50400d001c0d00f41c0d441600d110f60010802040764015005510540680c0d00310b00d00300c3c0c17642d9841c2000c0d2010008035904440108c2d1203072000a100c0c1d40066810310403072003500c1001c0c40b80c80b0300041c00c403120000c2c0144c412603002400b881c8240d060642c46400d802e4044c40000c902d242d034500c0070030b08a82c859042800001c0c40026510700b4012040d0340c0c500c0c0d05100c40381c1c20443c1d103040c19111806015001550f45140c03410000301c0c2c01248141007007140808807860032030300e114040b4059001046041c6852000c6203600030002104007000c0140ca136402d030040c0107540b402c03404030200302c3c1c4091844a82860f008a5017800c004d0070451a540c1607a00b4038482005903a4007075a01060310305407111900440e2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 501854811 1250 501853561 501853567
    0x50406180f06080a02040906031103011d1e0715030603030f0c05030414030f07091b110304060f0203130b04030201030b10090306020d09080705010506040612080a05030c071a0a0c05 79
    0x4400070300110004458407490007040c1611600e030300c1800b07803059a010b9161903017003a07804402e01c511001c007278200040c00c6000700081d182c2008050b090700c0c1141c400384095003003206401081004d81c40080725900e031000503035448548070103e40b102400f0000c09400083d179900380a104040c0c021070200368400007030801400d885a20380d1083c3d40c0f4440c0780100d2912207440d030034840300e5840400c03011843c0c50880d400d039100c2c0c64617800e20000030000d20005000203c1d04003240340c4064051045c3c25181c0103500043d41c50a4142101a079604256480f203808511003080031042a0046003030184c003a0000c15541c80e42d648c5903000040070b480c5009001072040508c220a240300f1500076454000301d07a4084409030720785603c00007100090181420180090b040001c1c88030070000706500180c46904112420071030f0548405503002915803404000742500020401740c0102401980503540c01056000661b00d0321099039a02c000004048640350581c8443c034081c4149040c60740140c040008003803904d41c1c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 501856061 1250 501854811 501854819
    0xf0507090f0308030606071a0a09030e060901050301030f0c030b0405161d07030c1101090809040c0c0210050d0b0d0b0a0606020f0d0e15040b04030309080606010e010305090c04050705040618 83
    0x1c49488045c2001707124600024141c0f08008002c1c055011506902034940001d00e400455540641540c0c5002c400140c0503285802042ca0b1a4080d10b20145043c1e5940b4210ba08580d5000c0c410614410f055902c4a00c13000c000000401f4814180e208600c41c2c0054941c1071082401108200c8140d0031601510740102e1000451900c20a0b84a620410301d1a022807000007007a0107641400e020034190100d9424807000b0400c1c0070300c1c0e40080c031450805517802c02103107001040440f040c0d150500029449611601c8040c00d552090007e017070603c07000140000c900319000c000071141c03e00324604840404503403041281d503403414030506004000c0381c0050103445884d4080191500301031402d01e0709110220304501101e0300c030b1680c5900d4502406011980d038507225611200e180e049484114000b484038000400c613500c01060480c00b840c0306866096007151820700560181000a042102c035214003540e0701c0c41941c4902607580903d0441d00c1b001d54550500d40000c10100c5443e00d0070049208041d0100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 501857311 1250 501856061 501856073
    0x3060402010f1809110406020f0703050601060c1509060e011d0727020703020a020a080102070317060402160c0609290c070f091b0c0c0501110a02040f0507090f03 71
    0x2c40007079454010714046501d00842c000030f0f801d40209000c640fa043c1039403080e0503040000d10651b6419000c4030000a03040c1402e907038503084e601000741150032240c0104001e42c0901c96052201d0300c0f8140151045078000009030031550710340c5080c0e0786141c4602d0b5102c0042028400c907040101d1102c0e982086000444860f561032190b44114506d4a518082c0c4c0b07004020030f0581e007442c0e208559019036440c0e40c0d605009503a1202c07000203a11850140f607000680c410305100b182d4034140d15840d20171600844046076900d102c0010100c5400503001c101d80d041c08031400000c2c011245c411140200a141012001017201805802c034803446601c40b52280b400d44c036140c0c8075025003140051081da03210040c4000e20b0070310840c1d03804910b4255401001103011402d035048140c8078403c040d2070983c074405605040359107c1c0c0560001d4101d80c00c80c001484507501c2910802c0703c0c850001d0481c0c0803940d0302c0d4081011521402d01000306941d40340c050014290303000b0f80580050001240001806095031624 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 501858561 1250 501857311 501857327
    0x2150603010b280503191403190e0d080307030e0601060e01120e160305070303030f0b010c0b091f0501031112151f030506070908070f03080315030f0d0e0306040201 72
    0x1052200801c50600d4001c0700d200c3c810318000e40805420794201094990314000c800004502c12140e01c0c140c10500343c584080001507aa50f20329222030b0300402d10305a00140c407049401002c1c0e40c2c0108058090078046a070301001540204866a0b00003084141428110304046060b00034100308600309884003110707a40b1482e0106425050350700083d182d20400e40503450075004541248a09000304400006e00801003203101c04c0b40e000741c40034013081060001c01012036549607013007070110b10402c08800214100b101c40c2e40d804400c0d5400ca407038524008104401c02ea141189680d0440d48920040c8208809680041482070082d100044c0400d1074400040c2c031240d0701211058400050b1002421758400d841e00310028905035101040b0203922401c00c80d403164800c65004020132021240080d0314840090210f0440702d00003050800c45055549880841c0c1c40a860300c840c90720424506003060b5400d0202c800e14041c044020f11315104443e9025060005056109101740c00c201d08101c0941d804c09a1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 501859811 1250 501858561 501858589
    0x50a09050c0c06010303200a0b040b270c04150608010b0a0504050d0c032907050d0b0a0f0f06110c040f021b0717031821010c02150603010b 61
    0x201289654a00403504a980150161000580300d0303940008281600440b510350746403441d541c605032840307541d8030320b81c3d4545110700000c021420403070009000c1a0703940c201c5504690b086a00288a44007007254481908982e82c00c5a6503070090200c1d6940e92416104015070058000f0b00811002d00d0208041c03d21201482010780c10000040e208a4041c440e1046030003910006004480107101410130070580e8501c2d00040b21075103120482c42d150280340c010100b01e0301400d9896016255224001182c840d0414a100304030035440741103040080c1e17600d60800c40a04002019088885c0c5840844007099256901000901c41400e11412881e8400309482c407000509a5004c11541c0541550000903c40c8186080802c7c0310b19165021580d0041154000c540306001036903d955500e15000d501d910603c00a064611100b080e812214240542220403103904101005400445c0310300710790a5030003100003036006030170480c601ea0303d40c00002040c64004006400170050805ca01c00828034010401070b07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 501861061 1250 501859811 501859829
    0x618061e0b2104030302070b0133020f0f01050a0b15090603040201092105010507050a0815190b0c060123090c0c070803210f04080a050f0f22050a 64
    0x18410000c9404801a55240c440051006441c3c9041d007802002500022170031540000e24000009101c0300300007801d181c0360070030341e42031a2a0f01d1081804440084440340d640c15800b910401000c502e5007031000b0b05400000200108252803d0900c501c111400500e40c81d00c504405802060840e80c0795080c0d943d502d2060707034450b60300d4807640016a401d000a500582e0040d0b10130741c040850910001d1303a94082c5126500a11607602d07010f1043d900f5000d40101e040c0000e22020000d80c0445603c0300c209039102c0040c120803a181481d000305403590310141c2100420900010341c9840c044400c2190600405a42c5240421a4800d002c641c0c0c3c0c06110070320741c0740f20f020303d0300c00705d51402c05500440f225241e81408a4040e00c0e543c44045483e070300416600340e1b4000d00c91980a2400640c140036034883c400042c0481030365a01c03555141a02c1d00244c0800d010402c040c410b41c0347e0781c907a01000b8841d06621410313081d2504401086c0c3c0c40c08102141100c05081c0b00ca0400300126160145004141c9590517 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 501862311 1250 501861061 501861067
    0x30f0201060e0108030c010c082206020c0102121005012c131508060604050105100c031704300909020a02010b060409050105120105070f080604020d0618061e0b 70
    0x4412405050181c1103903402040030800020310380f50020041c401074401d41c000380010701a408090340c090108541201501881a280d4540580da02040382c80c03591285100500780003003030440c00c0c02ca130401100c0384170000c044ca00b448180c1312030b5410103000b80000d01c1c04001e240b906041442c4c000040d42c14604611000000025130382da100294155142c4a0070410460301d00222110703e0303000344902c1403000300d00035040881d0306401d00f4050181a070300b001c0e044551103250040c04417080c01003082c0031340400c401d01340c1c001010485150701c24001d42c01161800c07501c2000e800240c441c2e0301d07160900c031101a030803100c00c03040b50340090100084911a0800585905580c08281e02506044e64400e91101d4001000710b0004040d9204606a070f4003a144141d619082d201700900b2550280c0381840820944880554080d110365845944080043c0002d820b01403040c5005064644a80007600300381d007502061b0244407010310440380140500e840420060605066040c42a111401a200030407000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 501863561 1250 501862311 501862337
    0x1109060301090b25030b0604050625060605090106261803040b0c0f0d020c040b06121003150c1e1e080405010c0c080a1206090f1a0103110703 62
    0xa6001c0014250440c0c480402840d044c2c0c40311124800003240d0035141c0e14142c0301200c015100e03124000c0c0321003028105a140500380070400800307801c80c414881d1000401c1002808e69030600344040040c900c20391000c5141d0382010100040000140c0010040003030704180c141180f18010100f4108107028000d008285d21008003000703a80c5144450f1a406120000380081d02000c900014400c100c014020748004c50b02900000d511030f80340420540069002d24602c01c030900c0d0a920041405070024110351034103203640c2c096124010126500c40780c0c0e01c4001420018071145461900b00170a040001304071000c112580034280c4161440c408040325640100769240341c0c0621801c40c425000c1258100101c0ea42a000400b0108104c5080f80c1d40d500b00029480c9040c01083e417a000180d1143d00c0078140464236234129081c41440d844540f01c903455100c0016203a0340e078498185081d02d0301c100800d080401026140300c516015071111304051400c0b100b10445590281656441c582c50b20f030a80682c02c4d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 501864811 1250 501863561 501863563
    0x902030319021e15012706060203130f1a0c0c0a031b05100e04020307020703061a1f05070816060507051b011b030b04022a10060311090603 61
    0x10300e800c00d10745100c110803610000764000038010360f014441008000b030052240011a140c418000da501c0c0c0e900d00081c01888003800c1414882844c555000403440e0030000e4880c075601352109503110a01503040055a02c00030710b00d481e100e0010f00b543d03082ca00740d60391610a50b0806070300050310a06103d040440d22140070320043c0918502828000c200c081030540780e08010995a0044c1c9602e010b0102d008030001d210304100c40180b4600c40d054403000649800701043c84040c0d070004140d40b0031401010004030004080b48510440c010407662030f21140381089041c00b1511101c00740c10f0b003036200708071502d5003071a0b4403608540e03203550710240c0d040c0c0300c55007101103800962403c10018404c509040c200031000764410301601c1c0042c0807840340540342681c070840e1403c803206020868101c00103060b003200a28000c2d0410840a20040e00051410000600c0c840c0401ca040702c0070306c484162024001500c100410154041c119001000c00c402880d41d43c400e01c1e0309034800000390141035950001009907070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 501866061 1250 501864811 501864817
    0x6060a03020102030d0c05270111060702071401020a150203010618030503070f0c030b0c1e070f110a080106090c020f030a0903030e040204031e050f010e060c07080418020702090f06060d09020303 85
    0x5508503108610f809044424100460000c9580060b030b41441c2e158ada204002101c5022b10800d40103048081c0c01c149842c682c0400c04494541980b180300c0c2c0d9200003603114440c906000280500c016229414003a0080c909034103002c0c52900481005d40030300115101204031103416a02c441c000c02c405500f450441c02d401301030351020340440b10550800c150344041c41f000f002c0030f65070003024018111281404101a000d0441c01806c100c1006140c40c00080c001e00c41c034845600b008105c140016540c0e170215007915683d800141810380c440c1d1584c1009501000120302810078880a14103240c00c0c920002c00d800018840602000700c203c4101901d0745a50b41110091034020901900c544e1403a81550541804544111101d02c09c0b00405107a010040c498980514400c8010f06425100c160380c80c4610740007000c055035800300804c0f0000d65004000c100441090303041c2e8000d80c584250b401005641c22005203900c074004000d104110299030b64000303c0722081c03450800050b1520300d5001103803540c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 501867311 1250 501866061 501866077
    0x102150a090f1103060f010806130311070f1e0b0d0b0a030204050901140a050705070311010b0a0e0a0c0302090d060c11161703040e070c0501150b03070206060a03020102030d0c05 78
    0x1802030b110000d0064103801c0d030515050030340407542c00ea01d4182020484031801d00c11003080780c010350046040455601524507240e8028600704a207810340340c0d0340314184282075102d45002d0100741c804001401c011580e01020310031150340040001d1420340104113903c0ba40706012040380d601c042807101681c554008102446c0c01070820015460328030a407d000340801400c4800e081404000502c505c0101c3c02035912505055907820b0900c0c43c6031b40d013071b501c1900710139540125540b10701012400e41c0f03403085000020040042070244da4200110b00d0000c4480000300c0d5000c06004200f8030700c0c50780310001c6294046030b0010000450f010309810448261449003c0d00e0001e01441c058504032903010201e030825140d000841c120254504017035555288114411003001c01440c40000e0441d40c0944d075041c407410702a10000c2001c0801d8404840a030189800101c1140004003d0000450381008403035030109003540c02e00d01c0b903401c0d03030000b07507903030181d1080d00245c107868451805800f0f10440540f0084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 501868561 1250 501867311 501867323
    0xd1a010b0309010e0d090915080a081e0a0215070507050601091a09040c030b1f080d0806014d030d0c0f05040905061c0507030b01060e0102150a09 64
    0x9586880d6514100d030310588500602d5030800100002881000c40d045030004a15151429114640752611011306203e201c000d00f400c14008000440c40c40600a0303810442c41112112750701c0000108004003418a80382c101800c00080c4a0301b02200c0d00040c0440c010314803c20305811030754404e00200d030540b26400c1c005000d0300980c80005101d20700c0d80c001012285461101c08054003c1e002881452141164060809840c9010402c00300355085031440c0c10007a50340c848074140f200303204000c0d1701c1c23202a84240002d610a00154101c0c9511010b20740d003101d82460240c98106042e200204c0d0b0030fa40b0a86960702c460b10304000308445070891181c00034011480018013840d6001040d080c3c80f0b0300500c030004401401c1c0040c02502c41d10820300d40004801d1501e48a0030075040100000c004c0c4401407005800145824003004100395002c0028620b0b8418002460081e00350715003140d80c014183d100b0390510240c2e407201403072680c0203e0b13480400d086032402c81c0c08558400f8032140140005200113814 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 501869811 1250 501868561 501868613
    0x11190c060b031603021c0308060f120304031209120b19020c011d0d03020306031b0109031a04060b0609060706270503070303050906160f0e0a17060f04020904020d 71
    0x10691000d1402c0f82100e00890301c4603003404585864000e0322980c0f802c01000a45440002440d40c079010b4801010502d01030b2014001100d480307030b01c42c039540c010780060380c0d403010b0b506054054661006c400d074040c03c4007003800c48000c9920340d1140d89503c0c0113840900f40350000401103140501a5050b5900005680020310031008402502c0400200a103c0080140282e03040c50b12002e0103402281d0060402600803e6412168400c1070096020f40303d009041000e0030070000003103808404108424856030001c020340d410940390520880300d5042e03105e0300075081808000e0441c0d550105650105400c06004251401b1140c0d407100c50205003009502e4001c85c081a00061140000242111511945082110b80c95a00620b070b586c44040310300383c00d41c00741681003441151042440006400c81400d01c4102c140107400018086100350f04000d240221007490801e031000e0410800d80c000611401450050900741c000c14550744004001074000c142e4000400100f14072013001103010308003501c00c408 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 501871061 1250 501869811 501869833
    0x180a090209030105090c010e010f0c060614030c12030a1d0604090506191203030e152e050d0809010917060f0105010e09041112120304050111190c060b03 67
    0x100030341007086514000c1d860240012881c820010301c01c0c44514058681072071220a0500445040b20031141d04010092031204800c00620140550f1001c0d0940b48140000031141c1030a0500c2c1c032a0b00700308180f154004241c824a1542c012085032880602441e050003404100b20304c40c40e20034074100c070342c9400c1240040d0004401e50b85900c0180156030403600ca407012844d0307520038034840d15140102e507070044000d664400000e002c1d90100e580207014405598980702003040c4101c1044045891420f009115000340240382c4103520a004c180700e250314100342071410030002c2018128004001041900001410301ca107038080c503400e100602d449800c0d01c028150141d03c1c01d844030402e841010a03411003c00105180d8018860703c6003901002d810003a6540c3c480e1611580036207420081c64114480c3c0504012083c0d00303001080041c480c0e003a515580e8102860210700b103500d058004403c0344014041008100f0745d9111402111350103250940c04416941802401080b01d000002d525100315117a0207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 501872311 1250 501871061 501871079
    0x5070e0f01050d0c05100306092c0d050d020a17012409030201020a0f1e1b0909080a1101020d020d09030915050412050c0901080601090e120304020105180a 68
    0xa00c1916000d440c54440c1e660380080c840b18082c00200180141081401842141000c0001e480d80454514010440a0f52240307a00c00700c1e035045441b449101290100c1501e038000c1d1001c00701c64242c0d400c00920300781a00201c001c00d00d0103507000d580c1c401a0000390007903c0d18803034040c20740031225810b0a0001d55942e1900207442c4a1042501c03c0400030009812042c1c1d400b2f22118011a0340603001341c4001c1d00991f94145a8030161102155400d0461121141c02a07481501d0000d840c42180c200f030b058503141c600d08001ca0841d034800c4001c942403004000010752400d05444c03140c1118184103801440503c600745c0a409907913014100c8510214009242c00500c3d0003080342036019480d000000c1d40c1fa407450405610100088001040081008000301c10030310794000324030f0707000b40c1c01d503001d0942c14000681c00441c02e0380210403580c40300d80180101e602521541190004c0500101074801c445078410005000082010707050003c0401d208000323941000021708042c02c000d1400b454561114118 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 501873561 1250 501872311 501872339
    0xa271b02010e0703080301090e070b0c0313170a020d05012004150801030201080c0903030f03070c0b0f10090b060d0c0f020d14030a020307050d0606171f061b0507 71
    0x85001076080c40011220307000041041c40030340e9000341d100341c95a820700345200058006460018440c3c420f0f1080020300c0306004004c1c0c0300070300310b08014503600e414541c12002507880d03070740050011021821a462000c000084d08039089641981c05400c0c02215040441c010040e85905440c07000111400c500045502e5001700b0941d48001d0702c25528950410048424001c00d0000a0115000102040c41d10003980050022118001c003117902e41502001b41d400150001d0320941e01144178001c03100304000e46581c05550002440190703000c40e01c1c1c03590007044055007611942c0c4045581ea20807482e02d0722384500300c03104901090340911004400c0c2d100144000d00c000740840c014041e035416090040e00c207100154502c044025042d007580c40340c82212000303601c007a00d1181030210401c812901e4210320b004500007001a500e40b8072000f401c4210340c40304070000605461010045c500c000c2c8550960341d040c1400ea41203842c0a180311102803444079550202043c001c1c146100e00400014600858414 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 501874811 1250 501873561 501873611
    0x6300209070909140a0c17060f030307020d0602190507080a0f0c0f120f09120605091e1c050a0c060b01050405030f03090a0f060906050a1b0b070f0503060a27 69
    0x1b0050116808030844661a0740102c4030a00040300e4045145403511442140c07181c94024156403500311940e0000307034151242c60046410a0300810f010900030b9040c491154032000c107081281c6007950030380e0b501d032791449400640004d0201740515240f8143c4240402d40e001075229400341411291401c103644480c681100100c00103080705002942c6505c6658039008076000002d65010028155440101900005080070018030a5003410910b005840006460400000000d414014035021161101d1000a10072105008082102c180c10b541d01a44840003950002000104401070200407140b52181d43e00107030341841551410b4020380c0c1e0201c0140040c4208564030000903035207003403031040d581992054602083c4050410440d4a009400170200c02c1c501c0e1500d451420342ca040d84c55540f009146090704c110010343c0400c0191900301c00c0007183c0042c242441030031480d10300d0008488400501030420141c01c6011240035005068076034108110175480f00340800000d441c00d980c400419400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 501876061 1250 501874811 501874831
    0x9100305150a031a1f0603020d140112050c010c110d05120a03020d0e0d2f010c03060302041802090112030201090503180102060a02030c0a0c02030f0d02010630020907090914 76
    0x10100d1384030700c3e01c011901121003285c107401900c1850088242c0c000c1d0806048680304503110071452901841010042d03010313042207858607030f412200b400d0491402c0c3c0100c0005040c821030120100c040b524014400154510880b480d0b91480c0c128035100c3e080902e01c1c6000d580492010595001b02a00b507005056440e0b0940d80420010615408883e0f940300d46003104d00129001c1d0079051304820500d10301241e010483c4902c000c090030030702601801c40b4960f1103048002a520881030003103161601500e04a0055140b101541c03481a13000946404410301c55041c40e0031049001c482014001e400c64a49250800103490321074500b99255640850f20f0300c84240140030704c0c8000340c020005031003564002c080b08015681810f072030100c251a40c0000060036a07040c8682491104444800c0240c0d90443c0744c1d40d40046285ca103410300b01100c8030f1458000c4450700707240c0c0c240d0201c6955540c281c2d207003590301160f00380d00d036844040043d2920f0001e50030220318181083c50301c4901c080800340b501d0140c02210 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 501877311 1250 501876061 501876113
    0x9030e0f03010519020304170d15090507090902032208030a05090f0d03091a04052a010203030a090f02100504150c031b23010f060b09100305150a03 65
    0x20815080f103030100c80e00448410702e41d0008860413103982c0550f510911642805440c00b6500454440c02c0c0c001d0103e49903030360344a00360700c52600c480f0141c1d030b00207100d1210288800d041959000d020346c040381c010301c0c11aa0340400000d8131380700c81d203e10500d903000000082e62500000d04000382c40340e10481d100211141004003140b41030200041701c504e022007120140440e01e2007120100d020f030800550a4441501070107155400040c1c138400e0340d020f94450001858a03003440080301400d0044404c00c140d44503811402d5401d5070b41c011088a030701c85089a00090a6802c625241c10b100c42582c2010303411808107a0f5001483d900728000b001624510307a450742c0082d99190086604204c6000024009604440500c040003400d40258215a11800b11007800c920010a60450b0310164ae1307480306160744440ae85525501c5a101c2c68018006101450746400c0c3d00d0404104049400d807024401c161390781c0c001900802040d0310340074030040001d10140303c865581c104a0017041c5015203200c1075008007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 501878561 1250 501877311 501877339
    0xf0c030209032e05060a052707020309060a051e07121803020d080307020a05011a0a05031c05161b05040b0436210215010b0306060a0e0409030e 63
    0x2481440700180741c1100561150010040c00f006080d01410454108400343c5e000f10b80390343e90050411350a2024030701d15111044e806440044103002905070410364004106041d5240c441e01d084450519160030326a640ba504218800b00403409241c005d08011004144201081040c404027526068183d40e110002000c81c4050002d03510070f0312000b90701c42482202100064120390107164025020300580d070b450300c40b0b51507090954a0b160a01a100c0e000c444c0c03821868544049850081c00c410b40003402030580c0840c80344400c1c1c3d0318202d0402070281c00700e0314406001c1003090103401550712048003908425001f0028a90b0b01c1c1500034544600e0070070543c0e51590a141c40341000305001d0103503000808103580d40500502541201070492051141001808102c00070344400c44850180c0c289507890300501740007814003c000b040f2000d44210b880040041108102c1a00d030002021100b02c0e660325844001a2030000002201c1c6401a052215900a0640004980e0324051081d2042340b096100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 501879811 1250 501878561 501878593
    0x50115050f0403030819090c1a030c042d0602011a0d050d030507170c03010501020d110703080a090905090109060e07081f2c011415010809010f0c03020903 68
    0x1100c15005001605100c10800f0030b20540d0b00541000078149a040c0b4203403410181c20589000c1f903c01ea4042d04000410001000041040e041c0c0c440c2c080e80680c15410041c00b010766600c201d1003080600c0d4545c15440c01d90440d80028140007585143c020000207036034070f001030701070010b080100f481e840034103200261a082801071008607aa0140140221120022040d401007901030407003010000640f4000d00d480c0d9000c80c2c2e0600940880f01126200e40c501000245400d2440312080c0c00c11400000c1c030f60b0090320009446007034a0740a0681c61300d0380e241c2d61084542000ca94000d4010905140600510380e03019072140c035050307018500c148100c41c1609030041c2d444690341f1800b001540440c0111111030301c80501030255210b00703000801c41e580072004000d0010180744542d280b10b0642001091020002d1050460354584805441401c0c0751040040b841402c10645d04c905011440d00029502c05080d4402c0d01c1c40d4189880403c100003030094000d00a40109030043e00920540311031401004d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 501881061 1250 501879811 501879817
    0x9060212070f200406080c21070306020f0f030a090c0603020a02030f0f0f03010806180d0c1b050a140103060803040e180c0a0b031504090b0610020705120105011505 72
    0x80c0000d01c0c224001c125a440300815042c00c07180c3d03545045010003200d516511401014005c0000b08014aa007007440d108001000e0b803078030200800104075000c0b030020302c1000300e03000003240d0b000480141c994ac0381840107000c901c100894030803045000000c00580030480d5119801140c0624034a064954543e4026002c078484c20090101591051003070041483c0d4620040980c10703002c002d12400c2c1103404c641c03403071690001e81160190350801820454070354a00c02400702c886040400502040141007409810381c07031140d40142c00001c03000081114242d02d485080c00512010b00510707c800d656420b03000300c0b407524030551800242083c5c00080c0e4504000240e40a441c2c606682035181d841d00902d620642c06190070b64015405510f003901501d5440b51007910081020701411580da141410003003d0208068240c244154902580360f000b03d51044103080e400b01003502c2d164042414038006034a0401568840340d88500c00c21031000101c0410b400c114103d4404c0c205801c041c00c0a208241c072580 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 501882311 1250 501881061 501881063
    0x7031e06060324151502030c010204090c1404030c03030503070e0306070201230f070c0c03150912030e0c0f0301060e090a14060108060604020a0318210e0d02040905031204030906021207 81
    0x1c4c800034820300490218400000c1803900b40e0044924141c00029002c1c2a40c12980c0042449542c42c00051b0801750070250310510000d82d034050f0392405055984003014001c031382c0400780800070701000154003e4090124544c4294005040728554580158000d01801e400419100dc0c501d28071405220301e40780c605620f0042603071038644180c03a561402d00301d1300c83c00c040314191480e400f03e000000105208030020f04444802c2c0d1408665a01d641c103100c81082240310075001003514002d11641460008500b000703404a086644144c615900c400203400350500b90855150461300c00180310400100103803c20031a486182c0942240700f0041c070a5803580024400c1c9600d58002900250701440c6c80e5004080c0f4450301d08001075114018083c2c03c0e0906400042103c00760217044210301c001c1030403074880391010702d2464803154200b200000f0900340b21361810000e010725158504817041000a0003550300300314071040e24440c00d10f028180241010700a1141d140903020302c900b656800714541085907081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 501883561 1250 501882311 501882341
    0x1c0c050f09150102030702060c070303080117060a0f1b0e0a0504020301051003050601020a0c060c03030e0c03030f0904141312050406140a11060106030f05010b0c07031e06060324 78
    0x96448014880341d0702d54088000e41140020045a00140d132400040c0c00b0070002a4010f10401d4118940075207003482c1a04249a10500d40300d0b8442e0036200080d0b4540c1c00b042800000c204485c26034880806450590b4806010300340702c40984103143d6000714a007032994411030f141580e044d5100e041c44202d200a00419070446c003441d5003500c855000782c01c06600400107104850300b1001c1d40d00c94285580950300040c0009070360280803001d05600d405000c8440758818050140f48161a001940d244035180c450f0041120215803c242544c465100703800032126901d1081480c90071003507a040e4118070013002c441014080a144034281d20034000d0301c00340d44040d210380e007072650401300858054005c0020441085251150400c06250500000b802040b0342e460200d66404500818003e445058100421320308042c8851881140009900d80031a5001040ba24141000c40a221482c0401c80e50162410741403100000c2000b11850b4107525090901c1a02400070964050590550303640403195625 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 501884811 1250 501883561 501883579
    0xb0d02032a0d0209061509060a1e0e1c06060305100b011101060302061218101d011b0507080c0703031214060f09060310050c0304121b110604051c0c050f 67
    0x3207406c0c65409000c0360b0910312941410103110304001501a030110310607000040000403070b070b070950000340c02d2040003035a2030070304031010340903c0b0200b4109824043c83e40381c01d40002c4851001c0c4000c1d0b501081c069500a42610300c044245103200001e09514403031940007600b00c0444141d03000b07041c400c50080d0f0b5401016180b0b48803000303055001240c1d020f41104100c221710a9a0403401c0c80c10000c0c04c01a901ca8440810000101c01e001280300c1e0450441c2e602e142d0504182520304101c00700d022001040c1400d00303c5d211003003410800ca00b4020b5500450b10ed1062030b41c08024907411426540c1100c2ea82e0a041c082c000c450200080a11401c0d10302c190410407002c4c21341c1440c5007034228103511040150840702c0e00d2500e0801141035800c261040506210000103000c01d015100c100c4009910342d0b8241003100041d0303040e00c058403504841d0050100030b440c03c080182981c139102201c004020042c50340400b0044600e644040850b003a40c122000c12001c3d070b00041c2e5050030720011541c1030008041e490 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 501886061 1250 501884811 501884821
    0x30103150209120a06090303060b0a0e04020a2003070203160e1501050c070605030105030111030408161b0602101a03070603020d111b06060d0f060b0d02032a0d0209 72
    0x20703400c4100b401d540580b120503c0d4000500c200886070b00ba078094240815440075071b0401070119411a000704014a2041140400305504001d0002c0040d0080d0b0700140d80e810700c0c02046450460710441c204050443c1055943c0c40c9034004060603049000704c058440b1a50052039015001c0214490070074103844020002c0c40c0848511002c40d0f14540c1170401a1402030010842800c011f419084400801c40100050029050034800c100d2912000402180b8606040d00c80f074020717018482e8245107548424070010100503864985410300607076021001e000e40c1d1200d40103900c501e050001c8000240c030340a0b204855000f0a050080c1c101000760240940a060030b200300c01943c0048002450952280da0401009000400804503007003c1c001d44031601c1081d21086040002c0501050311948050041602003082c00c8520f00c0c07440c0d0300c100d00040392408500880d6080e41340800c06540350041c0522000a0341884080308542940b003040c00c1030100d009020441078002e4240082c2d049004600024 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 501887311 1250 501886061 501886103
    0x4030806031c111203090109060f02070f0b040f0206121f05210102090901091b0302040f21020d1110020a0807080a121a040b010c1101081e090105070f0203030103 71
    0x3550f00081c20980300e441e071140422944030307441070343c04101507036584000c5030034041c0500c5640c07800701c0b0714602540340c81a40c2d02e41864900c0684009080951040041001c2221048000300740a502030012901c9040c8224100310742d8a08807900f85000c002d810783c03682c00c1c3c00030000c43d00030740300001d0076120070f1031440c1031005481c004140d550041c2d650030020442d06c3d03944e050520b03008004201012503a45d0100340000408110700725003506050042c002030103206c1c0324002104c26034040d02c07015144030010195900c80c2c1010640080d402c2038280e4418003d00000c89582c0d40c06800568210202c50aa501c089984000c1740d1006007504800b031000800281e0010000c01d040d22041c41e0800c051100b0310444401c45568079164030150480d512b0350310182c14540512200e122090805070000743c0c3c80c0e204c055003007080031b4210381080b912000046182401c4140c001d2030b687c8010741c0f80700e03914003011481d00070f00303050b200540032502c0c0b4071110460a1000084905a0741c0c0108483c2d401d000c400c0310030f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 501888561 1250 501887311 501887327
    0x40f0605060a080105010b040f0b0a0c030f030609140610091d040f14060a0b0f0d1b1d04020a15050a03091502030403021b01050c0d08040215030f04030806031c 70
    0x20340e81c0405000b00c000b4008409015241c041e014155400c0ea46616182d501c504500c0d2075841011840c1c4203110800d0103a401101e5015819054149110060719412040700281f00030340242290605d00000001070f501840c040c03a110b507509840900140320891002e5484170401d01c9016890741031403803000000d00ca1840c220f41c119211328640b000024071566543c0224648280b40c490342c0e03010750f0411694035918001e0030842201034642d19403411140011510741480c0010180001001c503659505001e80c400c0b0900c014000d01c2c92035011506a020290001003040c4c07003d81c494409100e01140d840e007000b80c105052070395a103443e4a0561421010340103131000c0d040540d4040003155000e14031a4042c0011407041e03103e03502403c2e040c9504d16141c00c020f218040b40340c1c1000404e10060020b8900011000d40c02011340c05c00c01c2c02e40e6140e1000408d683c00110607041d0594011080c07189800c0e1420950740a54400e48a034000c2e0740d6003405155440c0c208201c0c002c440c404469130031b074145019030b800f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 501889811 1250 501888561 501888571
    0x15210e0a02300d1d0d080c160b070605090304210303060306142e0b09030304180c081305060c160f0b090c0a0e010b0c10050c04140306040f0605 63
    0x821407448202c00209403489880541140154126500e165049a03200388008012071220051381540c00d122008100c407111791040042c0303007070400500e80c0f450050401c918801d203d44c1ca00d281460640780c010074122500b00030380403200d135030412010070709114003c0181c9040e920030008604a0010600c10340794001168141a814140c0d40d2350b0110101c1c4090154910305807101031524080d00b0a00f407141d1049030050b29880b03502903864107841c0b031a80303113840d5035048a000b80121a2a4019030001a06500c0365034400121101000790481c5015141c0e00b000c03204240c1c80d1030f28500340d40c4010320452940b1013548000c1464206400107640020050098040b00150b0081050100140c3d510440c40104055080d5040b07194401081205602041705141041080c0c4030300000742e10304142840b824506002c1c05812200c007054001c0d001000b08018000c44803c5c0300140103609241414a0050f803180c0106c428a015001a00d07041d8200080c01d21300640d8032080501241e02e49803610320003070502500c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 501891061 1250 501889811 501889849
    0xe1302100909112107020607120b130606020d08011508070507150603060f1a0915090a0b01020c060f070b150d03030615080702060112060615210e0a02 66
    0x40302103501041480352102c0c26862031400e55407031890b04c0c889aa40c82043c0c007401d50541d0158100300c0403a9002c90520740042c030500704140e410400c09401e101810784000810307080460403901c0b0302640307442c2d004201103558039003d0321482c074070681088038200c000b4024416640ca44090082e03259110782c0b4000d6004000c3c1c81c0c220b00b08400c9685040301d100d0f80c1040010000e454242c14070510019126013618034820000c100001724000781003541c044c2201c0f034150b11600341c0d400050030a0503a94000f01910740700070140b80d1540ba24542801c001c02c2120b400f1350041c070079001a4011402d1140c11504004064690282002c140b56110407200c100200180101404440c1841168680c5e0311110031980c800e484c081209402c0464002450044a0440d01040b520205214680307402190b2141540d10103003c617400d40c005810f118004e06101d0340030f400c00c02d00c01d411a50301950300001180c5640c41c102062010440107620071810380703242d00c0c11070a40b504024941d42c01460148280c111034103800d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 501892311 1250 501891061 501891077
    0x507031403040b0f0a08010503070f0902031e090a0b0c070231020d02040617042d02030307061406150405100309050703050a020a12050304150509031e01060e130210 72
    0x200e1804050304044c4803501c0e00480411203010183d0482003042c098903058000b0141c161410b030158078101c0c803c1c0705881741c050340080440c815090300d00741031000394081c0e0788a40841c00c03c0106035076101e07501c0006484541e5201c0c0800d04c002d042d50111901250010038483c4030800c1d5100520000444400382c5400c1c52680c1460501000340740081d1000441d00400140c40300d04d000000b074400d0b002c00d040202c0e005421420400000c03070303a904800b10428003600302050080002c00c1003403403000520003c1d5062101080150402002e81c104010182004003080950740b5920240400f0382031aa00d22012503005000c14010f5007032413880d078003020a1524000c02e4859554a9590800450340c00548854000790703580780550030101d0303481008007102440101e400f003494581c1a20780c01107000b101002b43c03007070864150040c802c0040d201e02403001002e6403e207042c841340304d50a114600440c040d0030b50a05000151421508890720b01c00c1203278403c6c461442d50598200149842a110b03031078140141c007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 501893561 1250 501892311 501892319
    0x10201091703150105030408040b0a0909090b1005030a0b0601031109190608061801060c0201052208010e0d0c171b1b0904030507030c080f070503031909050703140304 73
    0x405000c01d034162000c58220340d0303418406101ea5601c0b4441c211541401000c000340000a0480b0741110116850300400f10b03140c0195103011128030303d5035885441c2590406060405000900701030302d000d5400c034840201a90f5440041c19201e00c1201809404074170a00001070055000e0340219446090b1464454903080143d00092039050020310001e04c03400981f402030040a8000c0406a080303041152030b415841002400341001500500400003000072100b240e40459010381c050702c1c99800a8140f80c00e501403408000200f48800c0d01c2944465820400644184000400e1401004000340d035100b00c82c0700151580d401c3d4400c9003c0c1c03000680001c20803241200c40f41c06032044221880c00c080d28165440c0d8844031041000c10142c5071041c1098400e000000343c002d011a2822a8141004180550b15081c03184142c0101c003004801e40c0c0d00061041e0030003101000461050000398030f031400e00b040c92200141120340ca2030f0010000c0e8000303642030010400d81c00c42d101040740700400312480c00d41c40b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 501894811 1250 501893561 501893573
    0x5040503160309030606122114070f021801080304030201140c01052509060f110f010203161701031707083a0b0109060e0301110a0e0a06050702010210050601020109 72
    0x101c03809a0001d103c148003882004601d018003001050090207442140229441c0d4004d20000113480042003503040c0008000c071030040c174400da08480e050364899150191b0703062085c108140c0250880c8910107545000104025410302c1f98141c03001c04000358101ba046500550740c1c142120100242c01c141480f242140fa9802d0091520400580c0c0690b41d141e20210120840c00c0249040c001c00d0100c110024072105a11214950034007070b091038a104006281d14405007400d1546485040950000040006c1028048a82c020018051f0f891441450540800700444082804024840f80110360840340241c4102c01800c0d0881c002c220540c03400c48890b04450710321244111108081280c2c40162012030050031980d4042d0b22012814890021030340700003007400d49140101410700c0004940210252001d60241c5442600901352551722191440701034000703060500e030284188010100030512510440a50702c04581c1a0002c0c1002c8084a082d04060400280f00d41e04640d40ea4003100040b5070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 501896061 1250 501894811 501894847
    0x6030b031009121202070f060c1e0e0a21021504330503100501110a14071a040b0a08150907030902040507090f03081809010f151d0405040503 62
    0x121601c030301030100f00050005402c1c030203041c076061680391060000c8001b08036500e120440342503200100140c003003030446041c0c541c002039140d0401b511602100541030a60032400b50302c248402101c2e1280344940d00c05441048034042c07040d19918070185080103006040808540c00210340792088642801c0d212035003000440807107141d2410034030b064600f018458039000225800d80400380362682c0745242007040a00342419074480c444c1000031000da00c0c954031070140100b0045540c8410350400081d44030000f19500c10050044820507a00500c06813443e4160400300c130304441c4200415414012402c806440d2103038010440e550b00c4001c00c6440310240e40c2d42d00100e00c6802d654900090040050040c0011900024400028090110014080b8030618603050040303991203005903039990700c400c1c2a0107c032022031f01038541180741480081503085507002c0103000d9960441100c1d12288411408a400c4241501e41c0d000c06400040c0d103500c1410103810a551007401201103e00d002d6030601c034151508 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 501897311 1250 501896061 501896063
    0x1e0f03020c040506010c1a04032115090c090909170f130807060c0f05011b020609011a060f0a090515090405010906080d050307170109061401030c020706030b031009 72
    0x28102901c0c9900920b4144501d40d001142071030110142426547ca10400c136100064040b0f8910307000000a08140c801d41411180400902c08032420b002501c880e5070141100c0088414500c42b0f12201040403129480340c0e110b054225540c80c1c41652901c5682c400800c0c1d616015030741003030158407840c1602168001049403641403501d19590700000c1d0341354401820a5000301c030b2650000c0100308070550384000068203064000c2501d08001e40340745016401040d4081603040100c0c1e80d1881c0003009600406c03081d100d0b62241f40207111202c00342c4030428051240980381540401e007032010f110761111400140600c0d16aa04080300c0e003c1d1100001103034801944948042c0507800200d15032282028041c1a00402c3c04900074007400e030a113240303140c607805401c0e08581084400702c00580d0644c070072849107a11248500071140d880d611103143c40b0290207240100d45040c00030a04858840d40300b803066800740c5036968040d0a4003410a142140139020540c0c2c0c0c6941417041d005454400c201a1181c103104c1c0e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 501898561 1250 501897311 501897313
    0x1112205090c03061003090c2c01080d020d08041a040302160b1b030c0a020d0804091b090501020d08072f0d1b0c05060703030f180506010803040b071e0f0302 69
    0x10785084c204001d910950307801a80c003010304110341c0c800010030206400d0251840b002c039207040220f200e0800300194032102c3ca50400c084d501e90001990364030203c0c43c1c05803824107500342c0e1400c84103200e0940b0402c0080d54001e10116880c04441c0444082100d0203401030711a00c15294026059102c1a0790070241f900400443c0000040000b4480c4403000043c11000440b030295052010210032151914060701c0080c0c090300000c3c1c000781c100641c41c001c80d00a80b451880c01c028000285504219000c4c0c031000c070001007900d030080416590300001c1d414001d040c2c240d907440290760355070300c00300d075100344050a490b000e0884c41d4480708070641c000c09500000382e000e00184108910240c004108900315244411008440d40e00e600c0400ea58222500503118195a402c0e6202018a021001460902a0070030b803a890200f030360002d8040d0761501242d60b40141c0c1191000d0b40c84000305620380c410343c801c040d20120704220003c002200f41701da6440c111030001031104014a240c84403122078030028411001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 501899811 1250 501898561 501898567
    0xd1a090c01020f06010e0901090212030421020f01030c0201150b19030516050c070506030c09030c04020906071104060806090303011d01061d040603061e0e01112205090c 74
    0x9a6a0412000104120910042c0306422042821980b2904103008486402c2040000212580400d41051500c1540a86000316644480440a440f0741050042c0074603401c005180500180f060100c0d401150340041072881c12195400064005010702281c40096548800b1031079640307600014070f60000c101d010061940c500c141d1203d40c030104001d1408000f40b511344420b112090318074034025500b5035118289180c1d03482644040301d00d00545640300e0760b448003001040141d0300c41c80e01c010b8032106c0c02c250f04481c0110050010031003a0f00a0503050390700950103000031030101d1024440740180040c050800180b00303448420b42e9050180031a158031455000000400406440d01e44000724003110703c030b9036011941000c1000304055111040b4400039103a90240750710b00e917910b83c04000256408203041003943c044031100c2406030042c900d503100852a00302c104519110601603000c1c54421a0020385c54007100c590000f00326001d607103440950640a40e0b02250a8483c02c0e121030180040c0d00c82551 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 501901061 1250 501899811 501899821
    0xc030e0c03070e1f0b040612140f1f09090318060e060f0f090d050c011b150e120d0249021e0a1403240d1a 47
    0x12030106038046950296101d440c042200080c0888040e410501092034411810202e4090f00c83d6503400d5048214240800600056600d0300f00003000a000301c1d0700400d00214841e2038192440380e10464410088003003110000b803142001c0315000705020581c5035030500950b02d5201e0041110340e0405c04902182c0a00050000341d4500142c80d8002e1a03145400710340240424041392242c0a0141c0c0d013442c0300d42c0030680340180d105031070643e60900c81c084c202511210460030100d545a000c0c00e80a4046400720554081c802c48100754406250b8004401c0d0701d280050441e8000140480d96000b000c500400c004880301d119040020700d4810004080941c64802052074513002d50304601c110781c81c0d1030f0100c150745151201c5009054185034200403620301e1920320b00100001e403154100c4030740c05603404100001c00c0d110340c00140c942826195503902c03000244920f02c030641d12064811220004a00d40010750182040d01c00e59000c0001a0107011056100d5503103691020000c5100b0501c0c0031090100300c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 501902311 1250 501901061 501901063
    0x27030a05060f1e0705070f030306090c09150f0503060616050313050f01030e150405190c14040504020a09180b0c0c010e010b01090e250f020d02011b0c02040f0c030e 72
    0x7504000d803c00c2c80034480d01300305102618511680304010100610b40c075814003410302036800700c0c00411000d002440b1030034402d10010400107807801102c408494008005d01460300c04d00761101400c9064868078034685580b001c03c4070f9030b004a0401c09201d4850102100010810b1024208103544808640c0703280b4200401c2010342000d080f0003904051800040d08405400083d4409118442d00c15101c03e45e290703820050b04226014807074440d88484040e00c00c041080d1403101d1401c88120108422108011404100c01d80e441071341d01030f51220b50084103000c200010b9129052a1600c0300700d41003c0000c0d030352242c000c140215501d05520710040f504205141081c0241d100105900008000803010440040c00400c4240506c41e0039184000c0092041465450301300a640700c00a904103480258000041c6280c102990710001401490840e6803514014092074120b0301c00c006000301c11018001c401c90321075440140030b913401030302c50111a64180f0184915441001c5a680c0807800b0140d080310b403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 501903561 1250 501902311 501902341
    0xe100f062604030507111305012d030f0326010906090b22020c01140a0e07120302030d0b0418080918130201050a1e08061527030a05060f 60
    0x414044415800700b10029a000d001c96408503072248074004502d1040000c40c07035922911841003190f501d064004a0a2001c0884411152001000c0c40000e100c40b080f009405454606c001084120500d803080002401880715040806800503070010712000c0310402c00c4001800e070720400540e40c1d192414010070384940107158481ca4280c805c000d880a40d844c8072a60358520324089002c00d9804600848060429080448124136490f40100d40c1e0034840d0456000700050300e80b4000768890706074001000b80c1a140c0c42800d064041c0c015600b09002550714001410441c521681e10582e00e4000f02082400130101c0c9200c40c0c0100d1242d61101c080b181802000350000d14403100e0101504100b0204101502400b007080380c0c280ba0140d2100740c84901592054201810003941106d0300c84070200c0c0c0c540c041c031506c0c494002154901100400c2c00a16401d44c813805c090302c068900318000c0b080460702c21300c0701201c6125018003220070384c945a890341c03420088181c5101c1e00808501041c0400f003000e14000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 501904811 1250 501903561 501903617
    0x37030f0305090102120403050a110313080f06091f0b030a0308010812070809040b011404030b07090b09030309090403050d0e0c0307050a061209030c080403050105091005100e100f06 79
    0x4c51404501c00784007013122800410040030000e0014298607014416510390392540112800c40c0d889003a642c80c9480e440b0164000c864403032240c80e46681c01d0040011b01240a90f500300c0c01350041d80c03403c40c1c02c542d19144940700715000ea40c8885066401c0d0300c04112405000e0b0107940c41c2031b041d50409100074140160700a0014000c0c1007403120b8808510000d0031a04100c1040714000f6800006100580d22503c0ba40002c0402c190045400824410b4054440d40302b80078603500c101884ae155070752007817680a400300c25a01540140020405422300781c0141c3e4105029050050426201e1203850b01600c4580344040350035004884126a0f0b420200580005040222442d010b010b040841c014850142c052440307904648480030002414003801032010126000151180d40e19102d0521034083c01c000e603503450b420310030030040c2403503426a0722400b80103049541c1c0c49070561703162000a100c2c41c003018014191807540d4100c00180c864102c20300a009161588a070242007095a04c40400c9c0500c2e028 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 501906061 1250 501904811 501904813
    0xc0c06070308071e050a050304060b03010e032d0d0513020613030303060b07080a0f05070c0e15010e03100b010203090d0b0609100311060d0e0619060807050337030f030509 75
    0x50300444c82500402603800c000103a180c103030f0b00e9944909051019007038841d074840c2c045d481c0c0480b01041c450048001c1000b420a10090807a460200d006c0030321000203401c05904e5003070305000c14032007500c0f07640260783c01070b020512010310580c82d5000985194462689516140b640c40320410415030035000e110002e02c0910081404e201c125160700417648500d403010010014855803150003207010700243d450f1150442d80c081c2c0b400e0388406030961b501c072090310582d00c1880d14906e4035000e0340c030822035280c034068060050201c2c42c4000c1c40c00400b030f01c0d42001c0281035001c00e021200700c0340c03692071285201030701640e080c5980341042828007003001c00141083c2802c0705000014400f144510100b8018284192151075650364501c4082c80144030803041c20850f40590007e021111580302405501c1c002c00d404100a119034585203959221000c2c8a21a01038203ca680c0100243c0b400c00b0000d070840504461160f040407100940c0b50403421054202c0129030102c2c0810b03082541840340c2035100c0d215030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 501907311 1250 501906061 501906107
    0xc0501051f210b0726010303030501080f0c01030c0210050a020d0b0111030922020304050607032403080d0207080307050403110409110f03010f020d06090c03050403050403080c0c0607030807 83
    0xd0002240100115000f0f0102e0f18000c0100322200d20400343c080c0341100d00b042e581c1410844008249542c20203200590000e4100000403c0ca000c000c1105c20b2403110314002040a01d00ca1030044d80500150b6100c10f0541c010f91141d0742205a280c003c0300d01c01d4440301d100607680d90180e8144000c80d10b400040300d04004103a4041500800c0010460300c001a0844050342224426400341c407144051311041d1038440d0001c4280301c200600050000d028400c03545052200070800e008000400c08040c6100c0800701600c0d40400108078804020141ea2005401c0585440341c0c50321500c0f01503106958000c009a00000d00300b0034401c0c00d9144064400c0300721024402d0b9205a25542c246480b0025100e00c00d090602c0701c12a1a41c003540904950035440300c041d51180c03580040440242901d02c180d4103010b04083d210450030380320b403185600c04c0360705856480c206815a1280c91868100a40c4410144208810180c0a0360740d900906406031007135075880c445240407000140031204440740300c100c0c480c5d10303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 501908561 1250 501907311 501907349
    0x90306050c160b0604060306091109010b0c15100b3c18210f06060303030412050c011509050123060a1107150203040e010b030106090311010c0501051f 66
    0x92402c2c220260f8003d0880c007420303114900014010a62640b00400c801e1401a41904000044081c0c212008040711014840d80c0d0307441e030301d281c58400d00c1205000d9800c11511900c06003440c00c0030607008509201d44040c02a21680c0c010210350008080d00c0200281218075801d45852031520106000c010703400061200010350840d24a006100c00140c009070988034500a07921810145148400e041401000c03500c8001001e6032034446007124045580181400101070f13040c00801c80e40aa94400700e440c1030004078880c00c035408d030026212200d440d502c1c2e228081e907810a03400c200000e0090a2400121540350003045050351101c0c4000201c400034541e4011403a43d951419140d25040e00e00308080d942c143c04507014280006500030707076441c8500c8041c800413a540000038100f91144890742c0302c0a82d032503100103011800244504400500044000d1000031204418149525010b04080700714403103541d91b55083d0344046514089100145848003c000480c04207140280340d442900e040103452 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 501909811 1250 501908561 501908587
    0xd020423130203070e0d060c2a020d0203070f0b030f0105180a0b010507081207020c030a1e0f05012f0f0d0213030b040b0a05060909030304060f1506090306050c 70
    0x10804181800c0c1d002c4002403040340202c5c1c1074901c40c500140950340d564100d00d000c400428200700c4803000a500c065410820b44000c9054a8403486000050a1401c0350b5608114404145000898050180b01d50000c2c9941030b409440014054100c82141c89140c400b00f82d0740240745c160301440c03203030340a500c00c0414808d87c0c840440d0841c1c41e022000c65030040700c0005860511400b000207107030b00f06c0022041c000400d00114036002e0503a03a404d0302c007d60648020103a40d2440b94070003600d4140d80688200c0201d00201c0c1d80c220743d51003140c81d502c0c2c008094031902d0854002d40342605241025805c6080c01d072061042c05154450f40c00c10075400c0140800025403203000f401000c0c80c0d03d07a80001c1a030440c9a04242890055502c014581349624040c6407180c075001041d08e902c51450304080100304140780c171104ca1032003900c07150029420344d0741e96221580985000c0381c0380d401d8295a100000c40c0300292002400190080d515403400c40c41c40d40c6040c008596009000c005150018000c010038804 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 501911061 1250 501909811 501909829
    0x8040302062214031b070503150f0f090109020607030c05070803192f031803010501050114030a0b09011214030a050f0a051207030912140306010f11030d020423 70
    0x500a40404103660415689501e14802d801ca170307402d88074a404025041c02c9000600c1c0b030686200340e0070f6030307840d400c1c40c0204094040259203054201c00305400082c1ea1004024103d0391201c801c0c800440c1800058004c00c0d810b60140070160b002404a812500900000300005001000400c0007107241c0b5510b1031403200d40801204994080203010b00101180b651501d291003000140403a03800d440ba0f080c001110399075030045801000c01080302140c03410518040c800c4c1c904030b03403060b10784614012410310200c40d141c2c0000e00310310000343c2d560b04200c04c540307440035a140a0000302019030071000003410035a400703400500a82080380d004001625000380e110098406003001d2440b040d8403072402c20401d0341d45000300484640a0a1100200a102949500402c2c94180141220816400c1c620400c54006035856000d110b00c00b02040483c1d840e500c141c0317032030807603480c0e03458402441c9107821803041c1998807080c01c95143c141c0114051110f20841030002c0560345184a010341081429400300c0e030014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 501912311 1250 501911061 501911063
    0x91a15010509010f09030203070b19030618050618070e040f022703070816170102310302211e0c040c1e090608061c0206030703020c03030403080403020622 68
    0x1043d804c00c50f203401409603544101442d03000301a21292915560154199040080e04a01c05005c03412401c12407130003441200151400101c02412011103030b204d40020303280c040c04954011115200c0b140880b040c4004150081c90741380e456221602c40c08042105644a00c2c40c1d8008440c4104242050180d03030f600181130800c074141055403a00001e40000b1309121899002e08494010401ca240140c002d17035145005441940d240801e20311800c41c6034a00700c0c020240300b00b49007103c00c00860b428158600200411215034210700800580725404a0b000d03215072200c1d030300800c5070100000300d00c2005010020f444040310102c0c00d603040ba010b10007552002c90304004e500913956507144003c003622440c2c08a0703520414901040d040d0b40790060003003042c41644100000210080c02041c0c40d8544500341a01922640c0d00d8203062451507001c121560b440680b001c42455400c001c01b1500d544144042c40c4030300d0007a194144245000d0802900f0800014500034880300750020a5009420110320300b0802 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 501913561 1250 501912311 501912317
    0x6180b090d08070f0f0b0106110c09090102040b0a021509030a08011215060303050a030e010b03070b16050604150b030601060813030905031e0f0c010c0314040306091a1501050901 78
    0x100c00c5500b08580680b041c43c0003c1c00c0340c410208490140104c0001c8a0001e6100300301d4403220342c0ea2203000b103031080824070000f08243c101952a00c0c451074004070a940141c0003400061410341d852b0048002c69000b0b860000240c0c0280c41c45060b1441c3d840d002c1035009455a019500d0003500c15802052352505024031681405c00c16100000c0c040503038980030f084a00d280d800c0001584a04001e411b81c0c000c03520a0f00045c0c1423074005000740c001070003000700d034507005402080524140404805507030403111148010015000c10f100100d1001c001d1203008a000751725401e0704e841d0a02c2c0c0802a5801c501469002c1c0d888507004101d00e50f4400002079121110845018240310b15107400c560201c01d03580025854401e0517558a00359050959012078a030552080300c0800c004c1d11119074a035800318140c20302060121035244013090003000ca00d500d0310b400d044080d02d00340c0c480d0350f900111400e1031415074000600c4480001d00984900e445500040506098103611070303200c00080591003205109410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 501914811 1250 501913561 501913579
    0xa02010c170d0b09060d17090409080a03060f09051e0c09120c040e010e060f041401181101020303062b1a0702010c050f221206050106180b09 62
    0x41c000c210001029100030422025558003a00842602800c0b02900700c1d4414860800481c08900e05072074403000b0a40c1c001c1c02d1058451030440d1320380058000350089600036848110280000d5201c000410030f8203020344001503e213040100ca8401e561260b0032000c4898a42014007900901d681598520320072484401281c07540e4500c9921024011541e04c2908031901e8030301c9200d0303030402103038401200c01e00362010851104080c607440c0c2611801c115804150300140302160103a408503e03025441806800144841c1c0c84105080742151443d121004412020354103000400980401290900c2402d00c015819400e0030790010320000c11900d900300040b18001280115506c140c4682c00c44c0c40d411030441079960b1580d01c5000302a00b412a000b000651811408105050003001a95a4004c0440c411414201c0403071802916161064042204400082001440c20a10940105038a106240208070340d450110301a0000040e09200390100d03240100a100001d01241a100100c0081341d214903 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 501916061 1250 501914811 501914813
    0xd0e0a0b06013204090e010f0b04060302060d090620030f010f050303180307121a100b0703110c150a09080f0d03050c0909130b0112080406032310080106090903020a02010c 75
    0x2183e0312031580b00c24462403e228100c10340580641c01030310b01154810081c82040c55407010401287c1c1e0380d01000350702c6201800036000d080100d84c4000c48840c8104e40c00030390300095802c141c041d402554414224202c0c00410094111180000c10b801401e00100c1241001d060800083d220300415502045c030f91105129001c03150303810850b002c010034022803c184d41c5061802d20815030100c03408614100c603030400100351401b001102070f030211110207181c241414502d0780d0480c2c1c50051070719525090b00c00c084025000c1d69810080c100d16130382420070150b0f03c49401201800325101c65005200d071f41c0103490203405403000030031244002e00c1c0c28a40000c0c140ea46d1070324003d803030103a001001d4211540303c1c100410401c25808125286006201969460703a990040c10301010602c0c900501030349051004210440c0603401c240440300c105c8141843c4081c01c2c81d003100c2c8918048500b2a018048030a040041000038450b00001d4241c074070040c030020f542d41d18040d5499200160090400081d0040c01c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 501917311 1250 501916061 501916157
    0x311100207030606151d090615070503040611010b2202070c080d0e01020712022d09041b0518010311010c06020d0605100c0b18030d0e0a0b0601 63
    0x1c007440c0c1c01a0104104c58541140100346038455800c0030102d5200308500c5103560320040348251800c2c004107801800e594400034018005d0350348003c4420310384180032600020b401030018002070040b0f507031100140c42c0d121405c0c07401c2d5401c2e140c407940900038690070300034103d030080ca985810f883c00381005071360317007509142c0381c508151603500c90803280c0560030010007060391180c85000b4450b801d9003102d450f44c0c0c0b1000040c2c08044c500c0c5000754410000c070300014880922001d81000950902c00802c0d40c450000007180300c104084400b02c40904400b0300c1002209080c00c02c010161105603946240c003221700180c41410350f4113000c0070f004c0c602000c02491050703101d16100006968017070015502d400840c0750b0400982114041c191140803603484110f45140b0600c1554503481d00320a0324801501c45404480300401003039000402030004000e15048005c0707500521003208047e03001001c040c26a41801c0c445220054996810043c0c270240030a0302d41c0c1d144280002c24402c41d210388840301c0d02d03003640c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 501918561 1250 501917311 501917323
    0x3050306030c461401090806040c0312020d0c021315060305150603070e0f03070504020c0a060e030f04091505040507120c09080d030203130615150903111002 69
    0x1c1035200d200c00c5800e880856100c0c00d00c07605280f5400d00c8a0904480004402030403494a0340c5a00507030380101d00300328504100d449104922418100403070220344072005281030840c100c40558501c0d030b840004004020a9a4400d4400e0785e103840548425a01c0c003400070f001c950300c0c1c1ca000c0e1080c0e550420181000754541d019031009003898082215440d40c0754000307406085e088813041c040708100100101c49044c04d41c11a07108000941d03580b61851840380400101503641d42c41c45405100380000810b40d0385440c401000030440610050040300c07268a8200b040d40c080c1d0303200820a0b0414481240f0003000402900d042d107003200030100c1e14071a14030400e8550600c40e803144c3da103c1c1c2000103125200307410020004018100c80414050300610346000d450880c8203201b0703a0804c0d8404a07174410090f200343d0140d03400c940482c0000756040c2103905c0b8041610941c400300990003681c0c000030002681e140f800c1d031150802d2410003445c0140785844403400c0c002009085406035241190070340216109000d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 501919811 1250 501918561 501918583
    0x1508060103030809070602061b070c051201090b0a020906090d0303090602280c0201020601091104051306060810030809060304051c02010e073008070c030506061315030305030603 78
    0x484209603074a0400414101081c1d5481c0300e14082e03202d011600364408a910782c4140c805c10041c446004c0303e218907062a9005000c10f48008400100c0840c041d038402c07078500003d2503035000214400c0882c0c14404040c003005800660218410095107615440f0041a242c400504640d041000281424150041d1240d80d40042100e88000389074070814070311407000d00042c2c0c1d211000c803140c0c80c400340741075400380e41f001e201a0242e4040c00041107952032540142d41403103503d9000505143d5076074007040101310700403100c2130f61076100c04003400425440300d0100e41c004010091000c2007032a41e19019224402c80110034040c4a00100080601c03100b00407111805060303100c400038022420900900038000480f01e20b03001e0003000800210649081200c80c00003600094041c0103665100c01c01e41540f02040013140d400c0e100707000c20400705c1c541e445824021402107001c3c20052030000304200300203620303545507030845140c0000000b07940700582c034a900b9030f0781c9802c03e580e680e12040c0002c0e2901480d200d07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 501921061 1250 501919811 501919813
    0x4090501060c0b06010507020904111203120f090a120323040528020315070c0503030c13150206040f150e0c10020c1507031707110c09010f0501031508 66
    0x40c0300e0b036014280d112480d018202c401d00b503403204001140c90340300d81480603601a00d071802203404a5201e081000380c1c0c2200902d650b91f0740101c512908e041d41c001c480010414100041009440c0000e0003071180d2040da0721b00a881300f407105d591621141aa41002c880415546441c2408411040702021a4a0784c0a5040000030310b02494215a0f034401c944070b84940d41c200c041e02c1507a14040f0211201c001d81c4c010081c241c1411091582a4281c1c0700820b07400400c504c03065840d010400500084d4000e0412090b803079507444680300c298050140a5100441043c21000303406640d40d4045000394001e50b22818182ca2847e103414840c4000941c034034a00446894070114840c10007000456600c0c1c0b0a0651380880c40c0c804010381680c44035407060f0507982000305140000103042070100248880352103400c2c05000550000e418500c60f0b401200c1b500040380f0611542c1e0544ca000f0486440030100c1190002c250758141150b89003014503501c100e40c107140e103e02c0424104006400c40c0c1015004070383c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 501922311 1250 501921061 501921071
    0xa021204081c180909050c0402070c0303020606030601231f032003010f180e06040c14220207020402071e0209100803091c0606030c05180f0103030507080409 69
    0xa203841d0321105071111008141403490481007a05004940e0f15108040210561900070f281110210150179410b00c11078544c0a0750500c049643d42c1c91016210860041011094080c00d5190183c900f03440900054403c1d4440d4004210705801101007180c04011981850010318201740400c0c59011a40100d070001410324480f4408542c3c95400700c00720a0070307203c811414078001e0525203802d1000380190749070a20090000c4c8460080c85034010550382002c1c1000668034101c003400750500c03100b40c6007150944903000081010103062004050407800480d040c180c04403030720b00045000c0f448940c207071000c250082512025951594107644645402030301010251198403031103521130200140407481000c6200c00f048a164022100300c00762003201004510700b000101c104402032118100109848030601160000900c41c2e029000043d80f140d00c7d60b00610b81004200040d507425a443d050080c940b84c0c0400840701107503c0038904503900340c14001e44d5035043e03040051807449540c0044003520300304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 501923561 1250 501922311 501922319
    0x609140d120606030204080d030e1006030b04060c08060108061e12060601031d1b0d080a0207081b0306060904050129240307080a0b12030921070303050a021204 70
    0x300100104074840280d04004054940d14143e003240124003400a00f58400d851807100240a588085168520f0f0011124036070000c007503200a45502c0c1c0c00480e0070300001000c1c801017007001e018010003210b03a81000c110b20b00d4044002004003100034002c074403c0d0b000000f007003080346a0001c55030507144080c00c2601d00c68001c003c815a0390009440340c50000380f60040041140d600e800d05c10f280622404094041c594034a01c509000f81c4403035800c1d9034812042940e0b01c2c0002c0d0110000c2801c00362540181c00a240740c0f074986c60500c650100313410f2a03000c050113454007035035000c84e5a940c0248115151030450701e850030064010143c00c0005c00c5250300c0b418400b0402072900008400344c0a040341c000d1121000740c11644084116580d1801c0c140d0024001f143d610b502030a10b1030380c000600900000c15101c810001245901c46070b03070b0301c616500000361076200c505010040080c400040400108140900452140d0340d44c42e0b444081e08011004c00ea6040c00c620a11899030b03150b80c0403040c903854980f2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 501924811 1250 501923561 501923567
    0x10e310b010e06030304050120070b040806040201030c140d1107080a0c141b041e05100f0b04050a0e250e01110c060913090204050103060203040b010e0103050a0609140d 74
    0x100b0302a10701d82c0c207900c0000605a290000c102e906590701a5a1140110182043c2810084074a140e41e0300358024180080345030400c1401030001003209400801260034a400003404a0f080700c1118801c00043c0400c401106020340102c2d024280e092800107068515804074201c0d038099003200500303d8100003005d4400951080101c1f04142c00b0b01c43c0107806181408641d6a20b40a186410200880d61a1100c130b507454291700c00740b1102401c0c0e266001140c1c400c10800704861007200c1c0d805101181e20800d115608aa04045c1c01501c0151201d51505080c480003e0000303002d071040100f0007044e980056441621010003c8010482c01d0350070001007800400602400c441224031070020701e070b03c007540c0d161340340008029110050140005241011030003c0c0b1800750000c1405070901501ea84010b00182c0301d6124040c0214081ca07001a10790a043c54150165403041e801103994410750401031020500109200a089600c4800042c00701e00e54901451298100700c0301c10281d015020703010302d540750 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 501926061 1250 501924811 501924833
    0xd0c0317041715070c031718010b040e060606070309090908120705090d11031614010e010f02070506181e12160b0703020f07090209040501050603010e31 67
    0x41d4121035100881100d140e069a81c0051000c0018283d42031000700b40b0407402483c0a001c003034005d02e031880c046903642600307184011003641c04240c0e2500d45400c4140c0c8080c2171007901c40311042114244240f02d400d9070b103076030b45081c0502840d218040c001800340c01c05001d4000c0c1c1000340395420741440754120500b0003c00c0b41e00b10b038003041003168015000582c0d0078820800c071032141a00078030a040003061505c405614200a0702003c0c0c16100b809003405c0582c1020200c0c01c0102205402c03007141c040c09000040c150b41c6451000d9043c0101108183c40e07503a004580701003030b00c000303580700c0707489001e81241180c40c5044080060b40141078851242038042c5903801760814010300391402c0554008815819603903100030b08140c040c04540c0304007170014202c2d100050010a0085c4111803000c50b1405441c0d08010091b40f001c0d03021a400144040d19042502031070f8010041181c040e170456140184400d10110010918200410080350921401c02941411414040f01031105040c9082c10701d00100481 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 501927311 1250 501926061 501926069
    0x901090c0311011805031009230c0f04021327020a0f031407020d0c08040504050108030a0906030c05042108031801110405180a0b0d0303050f0901060f050d0c031704 72
    0x190303807103141325142e8200315414011140042c00809580580e4441351001705581a8111001e00c0c10340e0020959500b00303002c5403020844030f03004d88038807070741d8a080040d02ca850041d400d01030381c0107000300c050018840800c1700407242545189202c0341c1030655900341d856071303108184064603c00f042d00c0000315171141400c40f83c000551002c000110b0100300e00b4180c440c04a45184c010791101c5902c03e00307140706122003400135100300091030815032100c0c0050240d42003600041010750000c02c0c1c40c408258800c0c080c10050400303040803c811400804010640d103d580900d603240356a140c80e86900c1110f2501c21100290000b081507128100341002540d426410001c1884c1d96082400717442400f0a100100d0701110f60040950400d0002c101e070443c1000c0c0700034441c0007015500c80c0c258600c2e4903400c0104401302e00c80d0754002118541164000103500020b02030040582c5000000d00c8078941601844003500c100302c0d24400c10704030034030b0104107445480d00003c08000d000000960400c40203000360080e9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 501928561 1250 501927311 501927317
    0x70b01080105250f0509090702031908060d02060702130e07060905030312071b1e0b130c0b180d05030c06070c08040902030a0608060910050912120901090c031101 71
    0x107071074821001e10b48aa146100f101100d180069044115000e84100740e118205400c009040988240014000820484040c0d01507000021074002d142c0906036900032130740b01d07804c010076a1f00304000801d50561003008000c1c055440021403c0c195034800c4088a12201c0103a814000b01030320008050301e8415500c6030780c1c04210351000100e0a850701005541c0000d8800640d04141c3d69000d0044464810b25241000c0c2240101000c1011848840110410786028480e00c070010080e4035142e42500c000600f1842d1041801048000080450a6101c1110701c01910f03a510703460700c1d5803100c0c407010210f2560b07913000040c40c055a04100021029040c0509004141e60890351450010340b505d0801040c001c02104007000188048141c550145810201c00d800000310075840e413100d28901f038000e90742003038154080c5001c045d0460b00c9005144d481750f6400043c00381030110300002c41040c020710410200c514600d0000804200c0c3c25404032400c1038201e0310b0100015aa070800d000c1260070031610300c2c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 501929811 1250 501928561 501928571
    0x9020a0506041805040201090305060c0403030e0f010206070e04061203021f020309060a0e010204091a0405070f0c060b3007050603190c18080f15160c0c0b070b010801 73
    0x40e52070403000351400c6458003102500706910155a240c002d18000308128103120002c580800411420041180300e14004440503070f40d1400d60a010b00686800941d5504c2010b000441740e0050f40c0c080364103500702440e41861482080c5420000e4007074103882d040020303030145100341c40c03050641c00a071030714108000c0326840303908080300c1883c40103070301c4112848420740d0702480100799200981d900c043e0101340007000040c18151120000810b071140460b0100c100e03c1340e8620b40c55141b4140c0701d0160041554100100220340c0c0d1580540300d070103820f8019100036a1060800c80c1d03501d61f034110302e036120441210166804034900d44000c06110644035000c1510a02401003460f08000c41102c2c01001103e000d80388401c000011070000d0801910b03160100060030401e0291400c1c40c0318402c0150110070f015009190b148503080385040000c81c940c0100304040380501260004c810125a83c20315185050b03605109941007981380300100f03910a000c61140001e51405000760b00b0513042c140d8081c0070080c80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 501931061 1250 501929811 501929819
    0x4030923040e0c100c031106070c030e040515040b0406030609031e090b03063c040b0402030c0702091008100c11031207030209010c05030d0c020705010804151e0f09020a 74
    0x50fa6071000c0d036281e03400902550401c901c40740030759000c400140c482d103004d003a804254002136080610580d04800071540c058201010150002d000520100050702c1c00c0000d8070700628440b0400ca0300c41100c50141d80d0f100494601a00c3d40d4010401650300071800380320b0061140f40c000c0080d045048407000722005841d035289103502c10f0b101c01003203546440701141036031070700c00802181c44044011020105100f41e1a194001034120052030b002c4c001c007070400c141d030802506005c00c0c0d403131140945114920400c00c10009a9443c0b0a94a22903010f4440da0386076a40c40030005000030550304180c50f00d1051903088010501c00d42c004000861559541891000015002a41d60300816945241c01150070700020310182c841d901502074604140750180c0840340a403541c41c15544031460319413100d13440d0302c041c0040c181c04200540042c0428648030340e01e454075440e126940341915264a1182340c03581c0c9102c8003100280116611070b0320424040141002c01400840100304441c2c040380181340d40c0000203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 501932311 1250 501931061 501931063
    0x3040f020405090624010903140a060c02070f1703120a0218060306011b111512010501050a05121b0d0e0c190611030d02070321020a0e060304030923040e 67
    0xd028620924200840d03010138044d2003141d24a0b1000581007003102000040449c050744400c0c60780322403a0001d4402c49855060020a4030301a4544005540c00080208a407040a070409000c54080301401803040c1c0041543c0d40c10b500c00c20031500740d0605070405000d00c0440c01e5000304107503905500d0b420884d003041c000744441c0d404200c4426000c030308458101a2410540d026407018580b140080c049160005000140c90341a030300f11103170040f1008a540c4440749183c031400c6002d841c0908155040085466000f4a14800d9544c024690355200b00400c1d00300000301c444100c40c940c1e564030345464142c0580803400a012140c40c03981588181c6100044d6030500300158002030141d00d1155903824101201a68226000501000244402c02c4080c00c108100c4c405007080b00c6c400d6a400c0b4421807031680401d06444000e2042ca5050710420040f201c064000c600070801c840c06444061301e03035507141016a40040180c0c429180200200c074548010642109940280c610072142044043c0400c00c0035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 501933561 1250 501932311 501932323
    0x210e03130509041a040614090c01030f0501080a14030405030a20220c0509031902090f0702030a14090d03050a031808090d021302070f02011407050d030c1403040f02040509 75
    0x2134100441c10300d003101501c92244506501c14011800414240c0308031130f10b10321032841100d010340d0fa50015030008100e5a4540128030908544070818031003035050200440d02e9481044004040d0404103a0801001d001030054800030a00102601c11080c200e040038182c981d00801104403d07040003044442c00d24008118152039040d013403084410a44400fa1100201f200c02c4140081c030900344075210299030704110070868180720520401282155206000c0790550150071191481c9900b001c0000c0e0640c0041500c201d440149044032400c202e0300310035180d0b84900091030b81c01859200d522014190000000e19030181d00c1ea03000c001e09891000103000f00250703045c5c0244014010422420680383c2205100a05400144000f2180c07802c418580704907802f880d01101e0003418110440306542e08049000b44000e0003410451510302c00da95500d0700c40d10890030f2101410303901c0c0c0002c20307550310030f00ea00c40da8882038104840d5a41050300705032814150b04207003203200d241490b0004942020110700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 501934811 1250 501933561 501933563
    0x13020d1707021f0c080a050405060f040f08030c060606030a0605090901090b1303050403020906040b0a090f0b10020d030c020708030703090f0b070209040303020f0d0609051503061303210e0313050904 87
    0x140d0f041c0407984d0b6480c0c1001c3d9218010b404204903081c400418a079403a41c00400b00400001d8a2941d00c5103001c81e0f1440303d0101e64442e011a4000748102d42218501091145d0703c0b01c01103803038680c1c80c2c0d26210a0001004203030041c0340c106030440c1c10024080700540c45500e1950007010084400d03550084aaa0079900042008002460a000800c01404c0030200395400080007400440c150b003695000c1a5070b2400743c0d10200001c1c0d140e0030594070103040c07031055901004060b6000f401085d0240e03806544c1d100a000078808043d50345540850f4280b090050340702a000410640c0e680d4000ba040c014400c031030794003071880400c0b04248005010540b042c00ca800c503075800341c025541955203440c03d800940110114160781c500411030100d4040e2035114202c05080c0040c4000f4590400780172544200c06a245018000e40c803a109205018a00400050b0041c0c0d141c0740c00f07148031407101d1950344103203030b00e1a0b00080301d810010101b174403810100145c2080040e041c1e480740c40d20380c0c80080000110041d10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 501936061 1250 501934811 501934817
    0x1e04240209211f14131725030c0204020f07050735030408162d090e010b090405010c1814060a1e21110313020d1707021f 53
    0x8103060300305183d041c07203c100880c0e4001601000b88080300c4505008440c00f8403030080c040215070030800d1003421443c09603c01e4840d0350901c0c0b400c9400c4041046981c01004074516019448410503208440c144900396002d0015501c482c031a204c0785800f40c20519084070035004098010607400c0000d040940308079580f00301292000d1424520142c2c3c4800181d411489002c05c2002003005d003c20400c1c2d40140e0185000501d07205e10300702d004101007041c1401c40282440081d83c2002c2903884088480981c0c09904002600b0782c4100c1519004015400030543c000d00c0341d80410092210652111801c00b0084d01ca4070208018035000541c42002c6019030b500900240342da01c0140e0a000000d002c84507071600305401d80c900780b00e2602942002c203c122100048000040d83d29981074010840c4a02090b000140600644890300b01c5090100401803060f8190101c5102c0555660300c1100300c0c1b4982224503082610101000040305030721026041e4014803030704045038462190300105c012001c0080ea = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 501937311 1250 501936061 501936073
    0x60d2c030c03090d03181805071814010302040504051003060507051903150305030c010c020f1f0207020a0f0801050a0b18070c170d0516081e0424020921 67
    0x20070089211a030a8095003000810011801c4601590b20040302030720461f00341c40110340040341c58a0959600034400307006c11600b240040e070040340d0300390000199510301c0d4a48004e6154000105c00034000d980c8920b6000d41480188551303550076405420a890046030140000c0d0f41d186010b840c1071141c0054142c410391a07008488007148650310003082042e0110302604156501d443c4c2501d160852081d40350075941d1400000c1240c0d8040010203883c54180c0c02400984500c48007044c04044965411a841500060610115035603d8003000280514209814146882c2c20826000b01011141014203925085011400b40740c41c550051102d0541d081c000d40701d9451000445100320074800c1112408004580c4c0010701030150050720b11215075000016884ca04074203414140c240381e0401c4400c0c0542d43c810b210007524a0000d2080f4443c250004002644072454810501c030042040b17841280b440c0072000c80d01c5003094000b020100c504540003080008500c10f055429500c0c50007040c1603502813 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 501938561 1250 501937311 501937327
    0x1030807020102010605060304111e060a18030f0b09010c05031b07060b060c0a0c121e030e090a05040303200406110a0b0705130603020a0e040b060d2c030c03 69
    0x80040034424410f10004c18400d81d1000841c001c4c0c1c0060310300b22030004c40c48100403500e00b048900c280d0854030f07468045a50404840200d402c0744110302c07201041000104601c5a920308000d2003a000316404894038030318003928104001000c2c010b884034140c2e5401e18503540d9281d442035040c2c90040340c00e00c00b550f00b2049423a44416a41e40090000c032034864030b480318480985e0701c02015010031001400504080f0a1a19129480195a421540c041c000600035039001c5801c03000b8190b404198203255410b44105410107a0f00e8151074200340354082e011004202c441c000ca6000319005910a440c140300032b845138481401302030510500310748402414802001050300c038284400c0c8900c040c805542c6207010700c0e1074081c100c070303401c0710414003141000401100c4441c075218100020086031034118240424000d006151022207840c3e24826511040d00c0d1201d81d40300d00856600c00c405000c1004035010341c01d2441100191804031004004c03440b07081b0021040d0101c111211481900084c0d0320300111 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 501939811 1250 501938561 501938573
    0x60c031704060b18180a150917180901080309010e091315021b07030c05091e1003020423010e09011401080f0d0e01050d0e1015050f0d0b0103 62
    0x18001d981e030b2929a0f000c07003c5600c1d0f042071004002c0000f051502145014140c00b48001c4560080d0300d21640050040404140341000c4442e0124400101050818143c28204034003c074941c0c0d2a100c0160004109100f4070725881c02e01c0001109482c80c2059070b0381c50304e00544074051400b02c2c501088aa14030344810703113001c003005076205041040302400006c0544030308043c028980e8401c000203500188000c50000c2d40e144414140d00d103c0020089141076540b41c2081d04418400c903409820508040b5261002190348683e148034180c8043c0d1241c03400081107041031859110a031701540c50310314501c60000710100225080e850600107018940d1a100b1283e80d100c0009058602c00d550712980704841210b84a5094000c01d4480b0060002d081141c0e02181006070b00007142d801d02c4601101014541d0b0060251407000c020400c0001d000c0a15031901406d1903d10682c811140c1c1c6880e40d0b0510007030300c000998040d5103007645c2d050319400d052800c3c808240e0010300064845500c41c0010400515 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 501941061 1250 501939811 501939857
    0x70807030509190807150902150a02031c0510090623030f030720040207020a06050307031506270503190f05060a0603021c02060a0309030e15070b01060c03 68
    0x285a0498400b030340b2014010416280b03c00d000c845204c00011000144041c03007501c0350803040560010000201c05500048138054610344e502c40309038021032132b04c803014003d10583d03280c0d00003210280420005642c00317030000c00044030444440d518004000c90802018490402952000c440c1081d0665005040a20701d680280070140d140c440c105010740e0032031081c40070701492841540d07070415810584078651810100e03002d903240120b10600101001d45c0e42d448036074040391a80d0501302d079241c5440504901519101e000c902351181d4900000901560290b030071212840801001c0304440841c10200d245110b00b4440d45505034400c080b41d140d11a0003404901d00d0703920840e01c0d154048140e946890504004640b131800d5160f4a000410a504040c0800220628540503849460710321703a00045990007001c0020041580e28446101014010000441c003610b0081c210a04d522042070882410f611440044407007600f80d800016000d03000700c001415003545a15014400c8100c030520965a038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 501942311 1250 501941061 501941071
    0x2040f11180a030c0303020c09070f05041214060108102f03090307300305090a0803090a05191208090c1003110c0c0406080a03050d050702030c030f03070311030708070305 75
    0x82e10b2580000014804d03404040114413a0b00504100314250b420408166001480f002c140f0242c40d40c010703901c0d03030300500b00c8058402c00110310008441600b4105070a0380b190040c50344512607107002052030700c03002644281c4600840820f01c5403050f01408150075000302420400000c8890a61003000304070395010710351210721102200d044c60000e03200c20040300d4080003003240304107a107011512201c03e40341400b0170040050a00b0700450821854041d6138a203ca08040e140744c8008c4003068401505001d0704550315003040c226143c42181c8030203811a8510044101c8441c1c081e00c240317900b110300800d406441200072002802503119042d00703014640b88001c1480c02056a82c1034544500d010010103850702d0842e490040800a0b010800d0104031080c5800c0351400740e0041c0394480000344e0080031228001c5079854045006d45549070203070f1840c02110090005800b011420b52010900e60002d10300c03542443e60140214080020b0304511440305685000004480200042003d402038022a4000d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 501943561 1250 501942311 501942319
    0x30b1f0317070b01030c060e01030204031e140d031a18010303030e01090b1504050c0316050d09020a060503040c050405040f0206092b0308100b0a142502040f1118 71
    0x840742d02d66404031040000d030012160014a0003050003481d51101041103070380400e08046285c00d04503100c41c20310b40c4090080d000c5030b01140b2451010082662036001b000342588040b81c0301003020040140c00750281c0c0c4020341610900054007038084c0340c44d43d25a0340c400b00d0311841c040c0a90940c0c030300320041d1079011110900c3d0f40d01d81d220301000650700c0b0001407007800ca807461220081401c008200907204041d1080c20341450610500540860040e000c1040c0d01281c1441039840d0b00d0102000302520711180c01950103000301c0700010749250028019071040b84240b416014558841c4e0800003191002c1d10b001c0c241d8601800c048005043c00d0005010a00c0000c1514141e0400da01d00030481400c00c1c541585030703542000ca802e080640048045030000c0d00d1188400040d81450583c049230300940044908008404941c00410403220084841880541400c40035250b10954410242074040070128000e40c504602003800050310f00ca40c01c1c2e0180d50300d840714076100f00c0149000d20202d001c12400c2d84 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 501944811 1250 501943561 501943567
    0x20604061b020612010810060e06011101140a05010f060305040309180902040c0201020a030606020a021f14070807020f0103090b0a0f0605030f010903020106063905030a0801030b1f0317 81
    0x2583d5007102400c2e4002001144011039810010054203041c8a940c07420b245608144080c055040c0750410240d21500a20b4980c4c80520354801e03e85c050502d5036101c3c0100080e00d8140031030a0600d0b000b850590360803950300385156584d11070890460304211409030028641041c00d01c0020004c0490903403070084544049841241a00010f040303801c100340007400b5030340c00101103100c01d801d03000f0340000f440a0b002600b265070007500030908a103111162344541d824500c6c0c08220282c0503084101607503401000c0942c4900c035a20304000f880e0f101000607445000ca04054454540c460b00a60b2302065001452201c0c0380c9411820401419401c0701086106032188400300b800e0301d00f001095000d0388c40708004902d1000e14100a400c4441d250843e41c20044480216a101a040c51007040d80c0308034603200c16080240003013900d00031922004003c125000000c0c444017090743c030400c00c5058a0003840180d00645410162604040b017003000041200851401000403d911042c05194101c0700c1c80200e00e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 501946061 1250 501944811 501944813
    0x804050409080f031e0105060f0906030606130b0c072709050f100f0c05120f04020a0e01150206010801020306031218060c0303071103072001090f15030b040603020604061b 75
    0x18044e00102e0340102001155400550b03905c0356503c4e028010302c0c0039035a5502d002c500c20014002449080d049038001c0c90b000000c203115448120449031500d0120103508002c9888040030b000641c00b00201c90020320460710042104003500c4000022088500342c100010707039000405101404107002e0903036942c051209080e9410200f800103031a0100c0402001078960759288114040390440c550060800c5030a01010707444510965000d90014054410340c600b981c0c071403001401c09062604074502e0079038a40c000044402864050f1041444035400303503000350780c070307844164202d0004072075865069200309443d07038119075202c00400c480d0500040900c400c42818002c01c103107500c00885d80c5495032000003081001548080513a941000351005149003100b1034407501507a002c00d441c211028505107852400f03c4e03001c0d450103c010031403140e503240d515135030b9460b03001c000002d2040000880d0030b1940004143c07601e07201e62421390f640204440d041909109049a04489014807e8004214200d50300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 501947311 1250 501946061 501946087
    0x90f06121b04110a02071a0705070320010309021c03090803031509070e130c031404030801050312043005070b03060406060309050703030f020c13090203060c0403080405040908 77
    0x8030001030344003110610880c14801103c440011030110f41c1c00c140aa8111a580490080c0844413400e00a000b146031900c080465407040000c01883c40c450b01a000042100182c5880c0400b02006a00c0f00703008100d90066090b103842d0300009500c808124103a00c90750305940c0252081c98024036103104400d8543c41818559031054941129281520003800074500d0300094181e4020324070303c0d20010010141c2d02180c000140d00d607000800c0c0362501111080780f80300e680004401d150100c0b0b8010a400c2c5800d010b040c2101c2800b540f800313070254070550750348601ca0108640444905050380842c900751900700055031044044d0041c41903080100840c081030b02080f155010304103000c20f403980d0342000c0003008100d40e542c0e0b0110060509140120010401c04924030080ba60181010380c2d983ca07444204900748030b07003210081e501140402042d81c8481c0b003a8403000c1500d03c00c2c0c040300c1c600d23255108660107600803440010300141c002c11082c0550b040c01d8003c0949a07205080b800e0410300b00030310342 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 501948561 1250 501947311 501947323
    0x118020c07080304090e1209060a14030403111902010806120c090405030d18020f0d0501020d14160e09012304051e01060311040e060f030303010803180103020306090f0612 75
    0x1000d41640003013024054100984a0308075443c0e0300d403000b80a5131256000c0204207000710405280b20710000300d40a00200c0c018002d00520b0609508010f55070302d414036000c2c01c3d03001c0000400324548a0101c0c000000e503184c080c4001c845d40c0584800708595244000c104070b90104500000030760240080040d125101e14540d1070007280306002540d140d001040c000c20440c3c0803d00442c9401440c01c0c289409a1903814003051101802d6a01d01400d8a0070304013140a8820355404031081c3c1d2421404a002c8503102c0f41d8a4003e040301c2d1120196219482c104844001c21b004120350300c800307240300410207004d003504903601400111000c815094212800241151000c50304844004040c0400700b850030003500c0058007511080c20200a000c1c001894814240160b015524802e4502808503045542d440c0145140a4004003140c1d0b6940c0c50f414096103d41028040c0488205080d6a0100c998064000d030f901c41c00c0050030941da9551140c4c01001001000f8124540100803022500071240d0144a5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 501949811 1250 501948561 501948569
    0x708070c0303120b0301051905280902010201110f030c03090f0d0f1106010612020c10110405100309020d020f010509030d090f060323061801080c040614090118020c07 73
    0xc0d511189003103810380003d5505034200c0305c3c40b9034545000c000b900001e403181d050541c10709400000d0590703140b64003281c4800d0780007a21035480d01248508100240d41d80c0042c400f0030310070790083c481c8401e8940420030318040c0c5112070082c1c07441400000c00d40c01e0b0082c050b56004008104840b0580b410140c1941080406184140003a1280c0d8100115540140000c1040b003009002000700798500b0400400c8480b440d0000b03058160001001d49500d83c00304038808245ca4045010031948055802c3c048160b40b291040718000d6000b0304001e4800d502034803550704001d402402c18080700c2000d5003040003640c1c0703001300f2605100040c4218040c1e91802c00c00b61150321010788604c0d40407818a60848042d01546d40024201810614040c421f620302e006039220401d2203040782280c50326514006085d0919001034074010041240000402c4040010704c0b0503003032000d540400825407541289880682d00c5030217541c10005460040100700b8a0989654150103c407000504143e0b58040079400c201080e84 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 501951061 1250 501949811 501949817
    0x72d0603060e090c0306071206031a0106030b0d17070206041d070206060d0503040e0c040e0a051501050711090a27060b030c01090b070206041d0a2403080708070c0303 73
    0x901492002c100c00355003011000004280340c1d4041c1d0002542d0310701c000d0403101001441c10070340c0341090051f04a08060365021488441d4080e02114502c600d031024842c51000a0a01c490a221800c1c5100e405c1065030b000030580d4a0401e5000d02400c841e400b442c1d040760464020400080c80c0072880580b400c0840103156024031608003828000d141c8074000e01054428200c0e600e840c000900300100711411640104180d44450340d4403480d41d4803070b00441e440300f0224074518081115a900302d52119114880c001400107a16003450011107207030141075001020304120241d0301031549004014154030201d841c1d404102411481e40ea01c1c05590b0104c6070414110701c901a4108200190044550a4900390004c040c2c611842000801480c081d01c600c030800a0005200350554440301c1c100c1d4040e15a510782090501010300200c0c4480c0e20446809014901e0401c51146500105402142c1c405540ca0002d1085042d91150250b661090f002120605010030600c000188510b4a850003036020303403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 501952311 1250 501951061 501951071
    0x501090c090618050d0809122a04020906131e180203100f080a150203040b192403150507020303061905030d0f1704050601210b040c06030e010b03072d0603 68
    0x1409102d0248d0344440390300c607580c101c0c030382041000210208441a03000c100e20b032030222060090100b0000d2040295181d081480002c42e03244c140840c000d05411510541240d4449a811103060a04a03089029180c0102e104840701c0c1c44c884081d8001d1a0040301044028008513902ca028140d03904030f0f60721034152600304042c41070a004c3d201c1e503504014032801c10250f2440c5070903582c98102c040300904400d400c0988508800c41418542d20031710708040c0f0340001d45c2040d80695084403c0c00f00610040310034100c10225250081c0c11802003601a0f081c5800443c10b688a440420590f0f00c02c803400041186070190340082c05507803c102c0e084880246455030558814025401440d0416824a03101e400420609000004900060840c1118010a581d075989d507481c800000443c14400c4002d4a42c101d22003d2009019260048500311395468908100300021218014260741c203662506074540c020620803c9222503507840c0038022805c801c503145071036103555251400440740e50845000290b4035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 501953561 1250 501952311 501952327
    0x3151d0708151320030c070201030e0304030b0903190c050a0b061909050f01060f0f1803050a38130309080316060f06051e03011107080d0501090c090618050d08 70
    0x24521800304000c8000b60500d0740ca400c5041000900c500e51f8000d04241d40c1d51a22640e4020500c180c81c007a590042d03c000e001d04020001d103070343e0b802507100180001424030f115440c5034003030f03030710549410340c000b0217030602e4811501e0f071390480413005040d960070a2120035080501018a000007001c1c00e50301400041c0e905245440000050058100300c0612a071500b0380d148068001300300b115610303514644600710540c5004c104004041e1035200400a2154030042000c01481030340200c1d844214102c502885d540345200348185da1440300104605501410100381138072030a03c1510321042c02824040d5030b03260b40d0840a8655405805807501d090038003000b4a0401c64240200d00b0340d1200d01000744000d0307040c07000280d081004000f40900ca0301c0151540b164545082d048405400008508a6200d000b1400c110041e40d010031264841d442c980000402e032001c05104803440b00303c0682e0351300c5070740c0e060250644141809024a1100d9a03449100060755600e414241c4400c071f105d403040c59144c0300e00e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 501954811 1250 501953561 501953591
    0xd080609040b0a0f021c1a0d02031506130606030209031213064a04020f0a1110060f0501030b120703030503042a0306051501020c0112180303151d07081513 68
    0x901f0710745900c2105500b0102c4c02603075002401031100e00d0180690000340d215003000981c40c9003000040a0b0306030629600003201038040d070140405190a03016200c645640c242c084629125145400a0f0800c041c8801c0c010240300f58080450b414140160044500c003003181c44c1c0c500c0440200103064076800e54032141602c01c01941203221498103a40550400d820340100350414001c5448010810000181040d801d510802410801c3c42c4080c0c003c100950b29000100c1210483c4e001d1280482c2c00e00d035544d0010705201e0301e203000144100025103030550841c0d80468091340007030070030303100b1642c0d03500c507811090100d0300f10702019052100111f280a1031031911100f0707664000d040c6901d01c0300c4100c9411702640c0101c0e011b881005d017440e20506840382442c03040018021100004010038650320050101038040c1d02c0b45030300001200340805580c1d941c1c500804180401c1005140c030545c1400402e0718a40540c0b0b8070303908a8050320b001190b00407841c01049401c2c00082151820036180d40043c2c204941c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 501956061 1250 501954811 501954851
    0x10203060a090207080a0806130504050c0a050618060a12060e010510030507080c030a110313030207230103050c1215010f020d0c0f06060f080d080609040b0a0f021c 72
    0x25a082c029401e040003519900d105008030042c820510100c2c0300020f007030780c0d0780c0b03142a40f1001340c46000b0002420f00341000e0b555003155a1845000e622000c002040901c1d01006403a0a0010151300d00d210b10241020f00915400c44150f21080c4481036031010760101c507500030400608100d104183c16503240000f0029811444650001418542400e20409a61000d081ea5020160498950780c949070500240020050554400b800c1c010200c180300f281c90f0900c0d80344030800d000740c5c00c4540698a17a51102e200d564410300b20682c2d000e41c2c00e1041c105500a0704001c0e8043d1110700c0035803d101c01c0d2051b5001c0c850b801c84181d41c0845207841866465038200702c0105005080e071000340301500044c074001c6c142c8a920305001e4030190341c0e101c0c1102000340a411541c090522580074450b155550002c459564107001380781808075181c40300142690411104d507501c10f80d08a510812592541c1c52424010944003802020454007080b8110701800100d1414814031000400001c0600c0d5405c0c480203901 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 501957311 1250 501956061 501956069
    0x2093105060a050d110f1815010302030f070318020411030403030e0c0607080304080d140109061401050a0f120c0c0b0a0b0f090709030b1e0711071a0405040509010203060a 75
    0x280710380030180071984960360009111a400f4174000486101d0000107120200342c48221544403008208001e10007000c00c0541d4012010040c40700031078860500150203134002110071241c2c102c20703e400100504d201741c004042c02542403e51180d2070f201c2c1d030045415141c5e03807001c41c1c4a450001090004040d414482d2509900001c00a400303003441c000c000445610805501070881000400401c00f40076600d001c40d082d0148914041100c1403400f00100900c003001d00c5012141407130101d0014168001d04001803d41a050b915503103003d0304044141c4010340440702e010108140070310f242046469509c03035490000c8143c1c45038209000c0510b041032122000400b907541d12418080f44103501d0310b4101c2c072181100c000726480d20866407250021280094140d202a00f0b61403003100740155820750b03031204004020400200b203900e2f502c018007662803503201c007000107a036071002d0001c004180103080e029010040780c0511a10381a03960000800740c50050790000500d035400424400c3d24a04840444010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 501958561 1250 501957311 501957319
    0x60619050a540609090b0417030103020d150f0f1a0103060b0403081b07151d0108060907110105180f19060b04140f0106030605010e0d060209310506 65
    0x8030386103621001c9941102450403155115141407030b2100156070480d0020700019503040001651030700b01824180025102501d40740354648001c91006421411641665005410039130501c151ba40c42090400d44210464191a5500542d6628605074016003a09c1c44d40941d002c91080850b038001300f606a44c4d0b40205041c50325041040009200c40b10607102242c3e00070310160b4417803109622000319852541e0a545d05401018030101b921103030180d000c2030603041a44c4010340490100c140040c445c010b01d4a01e0b02080d100c10000d07000e441c085050a601209629010403078800042e2120f080d10001d6610341e000d04d5012045010562080204484100c403550050112100b5035000c600c9401030000c0251a01d42c0b550404110340d01c031500b090380001c0c8565880729207807030140d082440b0b5200a00802b0006420614002800e42c400c2c07140c484055802070111080341c606644940095001c5020540c00083d01805a10030044e40700d0316001c0c860b0300c880003115944030340003194200e901c010305503442 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 501959811 1250 501958561 501958649
    0xf1410060302072604080304062c09150406080d0c0b09060106210207150510050108072a0206030903030709061407080d060504110405011106040302060619050a 70
    0x705038162441100c9100180c454200b0510340e90800344e00c1d208942085007248000135000864903841082106628200f0614440803202c50300c00d062141d01c0c4014190388100c406000c11051400300c10746c42e100f60700003030002a00300e40d1080c0c0d04c0c2c20410005038040208901d403202006100d60b006440354081c50a1020300759540c10050090200c8140307492011031886400321040815500e58101c4080c4c0ba00804a11112a0b00e85038020242c40b044800304140142a0000680b0703500460780640189800c4e115100c0003d130b440c840301420018100183d40d084d10741805000035840c1c1c04000c42c02081003101a40d900d2800c0c02d0054811a00b0741d0020341000000768407003034269010410340c1c4c6c01c50360110800e41da070250300e50b940015040d00e030170180c2c0c46171400540584c0c818640c001001118403e8944100481c0e1101e80742e510b0b01003c54002e00541c102a000030700c989001e444c0141d40312100c180b00d150305912200440c001c40c10036001010702e0150711703203120f270a08103c6a006d1046d0410101400c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 501961061 1250 501959811 501959813
    0x10b03070503122d030402040e01060302060409021e0a0c0507080a0803071d04050108100b0414060f0a090504030210110910140f1801092c0a0f141006030207 69
    0x5650f10456804140f00325001c10b6489003000103014801a441d18070a030000743d4107021060301c009500984040b03106600d4000d00c1080c13800180521011650014003d604044c40c0802c88006503104884044000c02c21a882880100140c006800990780c1c42d52114020030180c50420b01d81082d07504481404c4d0f10521054000810610840e40d0160203458100940212000b0b81c640403482c00b503d09600900304000400e43d80b00014240680c120540014405102100144011101b40d0b800340584244018005840b50502e165005d07010040607240c45256950748892808444013502c0c210010703004010001d0508a590084031a6501c200f42801e2429501c600001c00d0704104540c0e01c014080300003001002a00e000042d240984c4110940d1982d0300e084418103000b10040c0482580401d0f8604e50110380046501c0081d4005605004140242c240710401807900000c002c011030255501ca0082c0102482d01c0d010348008020051030803203440c2085030700100304148941211041602c1805400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 501962311 1250 501961061 501961063
    0xb0708040501030c0507060c0c051029120607030e010c080906070305040203070b0406050403060e120f07050109151e0c120504021c031d2d01030b150408010b03070503 73
    0x3038100c030030034280000d11100b00c4c601603601d0302410300c0261582c1c0c41c06004c00e2005401600c044440743c40303402902d450041020f12901143d006054014501c91124480c0750194140440315038648001003d000700820b43c1d41c249803405000300c400f900000d4403620000c04203803003406540031001c100c0c14106000d24005040a81c1e40000508540400d034540303001c2010354030b041c000070000d0481c2140103556607848550141c1564060f00c03040741e05520300043d4002003900894050000380d00030362401d20380742c4111111031340d98000e46010b44295590354034582c00100d81e41d80440c0c25200c10200131681009802c0c895040b400390024000005003000e4503500e005502080c8220000c2150200240c261254004100300b01c4000c0c0b41e5130b1031070b84102e203001c0071f054118141000c204220466000044078503010f2080c004580c0d4817103644a110310444000d001c05c2e100c1c0b260701001c0306260000300d031074514001610010b114040100d40210000342481542c0b8280130f0150310310019002003205920700004a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 501963561 1250 501962311 501962317
    0x309060206072106030632010b040e0c0c01050a0605040e0a32250b04080a060203130c140307090e150c0d020c1606030504050d052101030803010509010b0708 69
    0x40f020001d861004010390040e590003640a540c11442c10002007252525a074124115400c2010040078030924100e0015a4019018144d6410241c2e0600309481d119043d1048040548080d0b0301d00024040410550800d105591103041100c50118a0324030340350501085a9202c030300b11500350881c9889401140c1c03042c26941103a01070280c20204401d0944524480a41c42c00d42451540218400d03000380c0e0303000f06042807200450220b01c0b03500c25920380690901d803003603225900540d0000c1ca51000130038000da02459105403800b0048011680390b65801c440000c06030030461540080d02c28503003083c00d0400002000c1c2152402c200208500c10150799940d22007002d04000d0903c010000600f0182d00000396404134003c55000c1d9110100c072002c035900c925111904083c00e410451001482d0741c42806041d00850f00a00a08044c9035041c42c119800c1d03104008540700d0841011038414100890024140298055800940c895061404103d903c081c10780c40140756800c1071100c100070a5030b510403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 501964811 1250 501963561 501963587
    0x50121080901021009060501170d120207140a050d031118100e0a030819082e0503120318010b0306010608061c03030207060b0a1d1e07020703030906020607 68
    0x907110403440004074542030041c9040700295041862200402c04940c001034140c8400309002011008065074465540d161f2040d01c800190781100c403d90400d00390780c0200640c500541003100c6210710000c20358a000a410700c201c60340c0d40025a40c916013540351007012480c0000368038151400c0a92082c01d49440d400b041a94495040765540a103007078002c4408804000000e0880801d00b0f5aa0078201240d400c0039141040100e4400c1411500c984a05040340c03142c1a00440c100000c50b1102e5101c00001454152584040d1698404500c0daa400c1281c1402100b90b07040c0c840d030f80d250041201420107464001d9902d1030381040806c1010369400b00e070f61810754042d454074243c103545038000181e81c02800700500c20075500d0b40d0710341d03401e0690503001003686a020714400e000d05c21800c028400022181e104429617400302350584440c04691100d03198000500301c9508058202e49040d13000c030307020240c6151000d40e02100040040580220851009081c5030001d09520b2901010283c080301c601e041c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 501966061 1250 501964811 501964823
    0x60306060901060c081305150a0f0906050415020a08160606050306010b071202010908120402031603020303040513091202240c0d0504061d07180504050a0303093003050121 75
    0x255000706c0f1010a2000d44c01060018002603903440340e40c04c2d40c0c5099000c044482c00107094102c110001c079001c1c00280c000c5521a5403803516241c500078681c5040c028660300030302103000d40d400c04004101024040c100c07000805d0760014141e80030703140503421207200354000c500076000710380100040d01120041c1d80090350001401e00c840c408501d000ca0040040c0240202400804100e1039000340d1411141d03131007188207408903441198a68100f458907411848000c2d0705038800c100034051400c003801c0c80080307908240380124a030a400d6807030030300d407203100c8100100507031000103901075012007044503000b1001c2e005101d40090500740c0b1040420b1103841c880d00501610390f401704042000a51091030001c5504000388841c43ca00c4550315141c40c042e200d4003000000400760344803007911a00c1614003417540500100140d02041c0d0302a13010b0800e020f03055554107a0b0310f882c5480c0003d40d40000c1c0ea0480e600d009108041c0220314041d0031a481030b04461070300b040c00c50f90743d0904000300403002e0020342c20032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 501967311 1250 501966061 501966067
    0x16150e0c031b03120403030203120f04050c0616020d05060406060b0c06060d02060d02030906091b0f2b08090301051e04150608030a11010c11100e120a08060306060901060c08 76
    0x14003c24a000789119480c0c00611002600205040d804000b420b003140408076068065140e101c50b29908400655025005800c40e405866140c58440c00510b0080d64003029601c40040700d800091b2154183d10f0151441d400600400040040b00d2141c0c2d405030401c2e5401e1403c0203071050a4071782e10b04004220500407400180500190f641da181901ca017038410380030035540d07807500890750341d1118002e1380c40a5082c840c140c482c0307200e226800f05101e0740d900301404071401501741c441080b01200a070404400b0303405400c44042000781c03010f601d0118180c000c844c0700d81d4620b140c8042c5421910010f004070141e43e03074400010007600102c458642c01681240281c031603c406101e40c00014941c40c0c0c02800e00703110000b9a03030721658000c603004d0180c80402c4000c002030882981e082e21072098001c4403440607005841c20342002550f90388000342e030340303812401c5404e40d040c481118400f0b80e02010303942021400001c20000c131f915042041c00c1d40f281040e91404415490620042c244001c41900140040004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 501968561 1250 501967311 501967363
    0x301230c0d0b0402370f05130f030b041209050a0302040203090c1c03022505280308030f1b090d0f06061212030507121116150e0c03 58
    0x281d0418541c141000f8802c44d0340701800044110031200d1214800d58004100d503022400150b00d0381030040f0030301951103081c4918040b0310300300c601d03900c40b0141043c030032406480030070740d215940e00a0010f140301e58518001410300342081d0300104d4899141608100700031106000d50b44074113030704000326541070324050381701c1c5c6910380101c1c24004c107140d4084d0829200380000404440c0500303600c0000e4040d40907180e80134043e48640010000c120800744034001155820446d03410641c500901c03000d482641d2411064443c190014104015403041e181e4000201c10301c103044440800c01500702407075040381e5031000e04403003c400050084c2a80d4900c40e0050246803c14000e0a02450f41300691100c0e04200140e20b41c03030000400c02d05104103440c046082101c45100902a1141500814040d259402c0c144080340002001d407402401c2c020f1403140501200348041c800ca074541541500c500b06901c400035010403903504542c0315114180789984000b03610703110794401140c0c010700150b140c1c08507071444940b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 501969811 1250 501968561 501968587
    0x630090f0219140306061804240209091302011d0d23060603060f1605041502071406090a09020c010908070609150605060307081f140301230c 62
    0x650038000e90004542da8034452111494605882a07401c41802e0a48400841c801d156031000c00700c0340190007074020078400c4102c0b5000c0b1050f5901034800d940700f40e9844002404074440800f0080d4000d07103250040f0740c8042900e0a0084203a1010085086012072012a000240031075041241000085414446030700039840b0700c0122a01103800c0949843e44003418482e0411000c55982e07060381038011040410054a00800c007035004000400304603142c3c0e04c98104510f104580c005019052110402c400100c0c240b450f0031011210400e50044c0030000c0c07610751030801158410681c1403103002c0070040c02a0b035542d40c0d50004150f03065a1001070301c900c0c010080f14010110307501d01812940000c6000010000c2030b0700002111032180c44043c440804510341401034620f0303400749a40c010030520008980c1e91048200d10390149490040c0d00982c000e0030002c01d41c145240d04845000c070005400e030303070050509004180304840510328000c0c00301000c0304800c000c20300113070071038455810024800008880e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 501971061 1250 501969811 501969833
    0x108041401060b0a08060405150603280f05040201020c01080702030a08100e130c05060301031e02010e120c030609030f09060c01061809060c08061c061e06063009 71
    0x2a8828100c0c0d9110602c040141907480126503071b0748038900b040c002038041d0302c0000142035805005010300e0304544902e030024a4403401c2504080c0001c4d200380003000e0005044c001d41000003465107000415090900009003400307940211541882152020b001c1030b9540001201c607210018505000c468580c512140c110400740d80c403034601300030000107100810400080d22844d042c0310704041106143c1d52410700801d40403d1001a0034903d00d1140044824803615200200d140305140c01c180703440c205000203284502c140e030a0202980000000ca500d030408000e1305400054a100950414042d920b0005081c4206d01c40c6c20301483c40820f59240e00c0748250845800303840721049007082961139083c101e00a0005180c10f071512030901740c000d500c05025000b5a4011040500030100b10030454501c1b50a28a03140b100b101c507107a07201d104e948401c00b032034100400301d10641e1010521526004000b040701540c100600002600c1d160945102c512000708940080344400c0d000c140310b5a5803c0500c0010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 501972311 1250 501971061 501971069
    0xc03210c0a0b06030d180603021c050a1a12250f0803070c0e060d0b190e0303070e150405010815030d02010b01020d030c0903023c100c02010804140106 66
    0xc0718900d803500400c0300d10741946101e45003c0d0201d51481c0300d01a0121a40d00300c1440000b010002d1034000d200c210311a4004220035101e00160b20310003202c0d980843c0840303804807444804242d84615241c1140c0000c0f80245d0351490845283d100a001101d075181c0b211100311200c0d0300e050f2030050017020f00700850400ba00400580c48201c03050341c0c0c1e07000c0460700c075484204120f80c800c2c02d01d08041000791a9003240360107000060200082d0f01165524540d0f1000f014004d02c00102d188206010700044e180100392210700c3c03040280d62241013502020b44445684c6d141c003032007003041340b850350b5222280340c003541c08582c024a01030005d600c810060002c9580c4206003240c050054000b00c80d000c0741c0540002074800020703800c8071180340003510120100c2d0303009400240041c2c2106d0b010409441c1401ca68008500d01a85000205c00001c06041102d00a50043c44075821350740a2400a464500c1192514090a0900b0900c4aa1503800249a07100c02080240075010010101007890401d61140c0054 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 501973561 1250 501972311 501972313
    0x50d140307050606011b031e020102360d02010219082809060f1209110907081501020102040302060a030e07080f010204030c12020f0d080f03040f02120c03210c 70
    0x51507460070a19103403079080795241d0108848212401000780006040c0c41d1031900350385c900d00c40c220202c181c00000000d000320a411036409000b07019000c00f0041d20001102c421020031203040301100e05a000ca0119201803d03c5041c0130a40c40016036004507140301c1c0c04080ea100c1400001d054a07080820340107266105407038202170306201c81d4000750b4448a441040301034039422601a41d48204441e410803156107280010030301f6000c0084e1030400d4010008040c4038a5179103070b20f0104000401c0205d5801c03a0207100041c207030f405100e4402d0038a02c0000f0403a400b880294070f86411074012822034030600492108169440e5140741800d007081c030810024212400644010308101c0c0d5035039000c1d421500003558a651003442c0010032010000e00a034200d517000d4564134040300008200000704248034000c1d00c0c480c0041280c02c441b004c1d1140194403ca02c0360100a80c1e121076030040c0910700b40340c192200c107140e1100380c1c14400755400007800c0e2000900300d0304140300240148011409400b4400f062025 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 501974811 1250 501973561 501973567
    0x20408060f0723070b06032e06031a270303010302010503130b0103030503180c1003021c050a230403080115020703080d060e0912031906150c0201120213050d1403 71
    0x811003c82c4010801540100c107208410b0301c0701410541c172141d155603440107092414114402c2680030351107071814520b0b05200090700395965194900e40411002c4000030003180c0004010b20791000f01b9621071081280d0010840b0418065a0199a407006002c0a4144440400010003030f9010010700c185803588203000d1800b075650b038503028100790801c1d6510011540440c111081450000440d8242400000c0016281d55605141070340258006c060301201c3c0c02c00382c8043d40c2c58001078041c590044218500000710488540003210f080d0594a00244a00039007505000c00301b41d10010542c10f542c03201c1c00c9100a03610740b1505134540803041c0d00042c00c411010804003002070845c0d001104903400142d1808450b52880c8072a51242510101031030540010f1011402403110004504003228890ba800241e00e0f40700c0c1c0c1d1020700041c4640e20000001c01115401e021542d0001010b0700c294203c0205600b410340c01c100c00c07010703a0403600070329020300b840110000601203000c90320014203801b01d0a89603 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 501976061 1250 501974811 501974867
    0x309150402120f07030209011401020318030c0a080c131e1508070b072d110a050d06020a020c0102030301060e1516080301091a090f09070503030a030e0709020408060f07 74
    0x113142c0d0054881a03108030030050002400c0342d42c0055034511000140d000d5450014040c80300c2406107040d50103d40c0500c1000c0841c1410344481880d500600641001854030303064141c00c1054800c80c000d0060416410100c8000d1807014031050704800004101021998a01034103074480d84100580c0710346814803034020009801d030007000c0100409400b17602c55220b8901d0707018031000c51240c0004030b40e40080f103003440c8102048003030041c140d03d0a402401000f14a0351500003480c607400c4a81c003552080e43c0000c4a002c559010444030403200428005141907616040300645040900030301c0602070483d0100c50310001026000701d40d0b10302104e0414130540c2e403090070800d80d00e030000d02954521510703144010441030388660900e40f180c400101010b20940e03c1c01512010701c0b001824201091140c2c040c00b2509a40c1803010b422a01040c0c0d6000030b0300d0361800c5441d0301d8458a40c0c050003030644104014003105d540484c0c443d6002104144655640d100d03948101c55050703074044809103601380082441 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 501977311 1250 501976061 501976063
    0xb010c0f0302012c0118020f0904081e1c0507020619020c03070c0501080c1c0207030c06292e050c070e040c060315050907030f020d0c11030309150402120f 68
    0x620303031091070300c006c100398000442035400340500f80708040e5100c13000e40e03001000c1d0300d40003900c82d41c040e10614071141000a200c1c2c080002040c00f5415880b0384101040312484c850705920076503c41617100405200174280300c0d10103510307582c0142c49003a5040701c88000001d18241c41e0116544074061100306da50300d5009003044d1405402d139001300d07400682c1e030a02180b4411080c1d030941e207600c0040040211088150f01d2402c00940c4104001c0701032004c403010010104045101c0c0350949180c1c5900140d50364900c0440702900f000181e140e82c0300d842240516030080301603406030345420441e906401207503030403803c05640900440071a00850f00c1107800201d039040707010a1403401644241c1c01c0fa01c0940e11003206400b070f5642d0317198a103042215840100032500c3c0c9280800d40268040c00c000400c508440c1d40c1d20240da200b20001c0400701c3d19504501a01503020342100c0e084026070340603500b5410441c494079290202e10182c0e80d850845034001c00c09541d1200000d05640240104845031a41c95429107 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 501978417 1106 501977311 501977381
    0xc01020607020d0806190e0f01050916050f031f09140a0b0d02101404030606080601120506070305281a1203040302010305041406040b16030b010c0f030201 68
    0x158402d00711061f10302a60400d0f13a0b248180d8100410b200105d0300c0a804410030075150110b00d629141c4c00000d0701c0301065000700b2580d50361a181d250f0800550050075a400c1010091800241e800d0981c0c041d0410170070b01c650101a82d0790780b035449000c031441c0d0710f040e03a0015502c40c1040014540070003205006440c1c1c0c1803515a94250440000c41ca0300319410844585070b440009000710711040002600600820070b41114640c0644d5503141ca032140030f800c082c00e041c0c0b16800b188134501c1e4802c0c580045c0d40c03200d080d42c24402c1e0304203030503000d001d5442001c0c1134000072801c2c90000c0d04001c00443c109030440c0c0c008620702071542c1d00460003031100030300584954540000c1c003242007605004442c040c6005015800c1a4203000034104030b003d01600481050502e0320300e003501c040c0d030003120404c0e65540007070b50b1608807001414140d0240081e2220103500d4000c3c0300d007600150000d060a = true := by decide +kernel

theorem cover : BRFrame.Cov 501798561 501978417 := by
  have h0 := BRFrame.cov_init 501798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 501798561 ≤ n) (h2 : n < 501978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
