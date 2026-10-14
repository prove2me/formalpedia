-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3600
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:07:55.971522+00:00
-- url     : https://prove2.me/submissions/a8c8b5d6-f09d-4d42-9d06-9a5ffff95064

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 647302158 ≤ n < 647482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 647303408 1250 647302158 647302181
    0xb07020c01020709020310030f30080f06010e01120b03030d0b010908060103030c0b3d050604030f080309030405030312040507050a031a04050c041d060f091f0f 70
    0x1812003503440c00000e40b07402000e9010344c400b2841002007040c3c4803800c8507404107407940513140034030340d00c121700700741c0082c020b0303100700d111441402c544080205c289850358011100c43c58a405101d0b6640001d2020400c404071001804035242c00030361700882d8801e000c00c00c3e03001019000000d024000b04003081c40c540140f42c1c1c00340740035580e00d4900304540c3c20104030710040c940500200301c2076040da0f400502c03460560000500b0340341a00d0129041d41c9408112004d800d00300244030346058149140d1036007085d1060062050201c507100041402c2c02c14408490036249c01c55503103002e0401607910644c0350b5000500c00d51140c0410710000c201c0e07030780a000070134801c691404004054103150421506286040d0310092040966640c04c10008420342291005190305411003140c43c0d4550501500303004004c4503090340985403400c4480700c101e410380b8440d18191040222101562000e050401065003510510540e17401a0404015200c0029411106003000b62000c54a030313401c10165002d480416850 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 647304658 1250 647303408 647303413
    0x606070b041b1e09060b090a0b070c0905040b0604061415090a1220010819091a01080304061202031003020d15050a05010e090c060301060509060910020f060a0219110a0b0702 76
    0x400c0364180303c4c000c031303806400700701400c501d414007c2d0b00041c15000903201e009a80e0201260764810f2121020300180100b28940b4180400c0c509440c010078640021580d142c030403490310102240d825418046143c00d0030014105444a40030f00c2c0710100f841c0c01c0b510000d94407030301290f00070a1041b0342900204682c0d10401a603001d10a881d4540d0300d44072400d41c80541001400030070080c01d14001100030090b1046e00000240343d0301c407402d010380d003840c0d4070840c1c401400000780000740000c4004010070407110b866484840e100950420401a03100a03174012110707070240c2c0000d00c0507140c4002c07442103da100711144070041d540407201c007080e40e004491401150790b0700c000412481d1005c0b18059072020b1040050149460520300090407400103000c0c103801c005000c01e826640e911510100c44401e0b200400c0120044c100d503000a5403007207241d014065500408000c61b440680500176101103401107180240c44040c4400c04607903c004001c01e01c4054407488250a0200d0b0144001d58000e1105a01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 647305908 1250 647304658 647304719
    0x50d03091202010c02030a141201031b1a030402040507050c120304030914010c0303020c0c031006050f09010b0d0207020409140d020717030f090d050d020d080606070b041b 75
    0x41a005a200718a401000d590610301d03070503105a80072003100d219104a040500403041c40400b042680c1c084c01e528001000001300000c000d22400c0c460101140c030000c0300da80500d40d22441c00a212a018480f800c81c200c5090002c00e0062405401c8981d00400a1070035900313154228051602e050542c510201c8000000030a101c00d06601a44010281c4800242d02e40620042d0000900702024810054101a030129104214800c1403000315403041c4010b007200e9a0000081212004000314482d461040c1540d03001c02e00103081c81f01c20103040718407100d4508d08000390070f41c0440c041d42c84043e04a84c020b5031407a0603400980882c040d0001d90090000614014080a0300640f50030000e800035800041c02e1498601120400000c036007c910036124000d1715001c560340402e101107041e050080c02c9010f0f000306038009550009061004403915503522203a0b4403041e05103c1c1501ca510000703003490b01144000350100303108445150718003034115801c5942c1c6030750341d4940c40d8695003400702c0030301041c0c03011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 647307158 1250 647305908 647305913
    0x3060f060608132310061805041205070c0321080a02180d050c0429013b060301120516120b070207180525090605090d050d0309 56
    0x41800041c050904003507000c0d040c801402c10280b02140801080d000c0c0956003441259407840c0c0104000d0044d00c202c5e80b01c5030b01c1c00d0040c00500040c0c0126002040c101461000140203402030ba8000c5801665660710101c001d8021501a0700092080d80c503d031319240008006106000000401070200c07640100411111a004088400141054511500510444202a0802900061882041390b031100041401c0c60007506158401c0f440b0365101c0c2c07500150904214010030043c2d80802104c8240351300c015140010740f4490810031a901d010212548009612580510060003078404070700265000481d14001078000d50090304184c440254480e6680200300f020006500001c408c018001e40b42407e000d880201c00e9952807002c0c0c0408800008905e001d4024010003000d4251507041c0500d06e00e13644005006443c2c1a038800c00341c6003001d801402030355002d0042d4880d05403540d03034800c449031070074000302c80a0304175207203050f03106449070315500c00210100200d1440301c03402d89000c5125401c50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 647308408 1250 647307158 647307161
    0x304031e120b0a0605030c1803030f0702150a02071505090a08071a1e031b03130c080d020d030b0f1f032313060b09094e07080403060f 59
    0x81030103020341a0f051081c0030203070304541500e600600c400c170940d071181c140100d44860400030a503156018000000d90107019200c4170018540b180c000c0e03e103045516840d210852080c407038424402d005800410040c000700402d440500d410481c545441801d00d5141c200044000d41c490380662010303401214104400030000030300d0440510f20841581c01c12083c140054251803021464002003035001000a017404c200c0c5040f610303424038039500d40e5103034030b44001e03c000142003800b01590b00d000c0c0c8001c005401000020300f40203250240e4041e01500c184a841a00030b00805050640e2000300001064100c0d141c04503400414075a80301c0801b40c3e40891607020342120036902417080750002c40d5203840c1290310081d11068210100c0080f82c2540300481c2002001490400c0b00343d03601600510a00030f80d1f050014100c4020524840d800348009a94411042c40c54808111b036030302000c03002029002e0314a10003160b164281d0005d051071030702c2d4035641d84042690041d04121107980e5078101050100949 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 647309658 1250 647308408 647308421
    0x30d0501080d021911031906090201120513240218090a0605062209060308070b0709050a0314010e0d12060b0304031b05071a09040e150c0304031e12 65
    0x42e800a0300c404010b04404482c0e8180d04580945050350f41c4c100d00c3c41941301041240488203080c0e00301968076501d494500050002206c0a900080080800102004081c418039014070b1801c00369608270200d03036603030b01500d81c2c8100d102150380752450900042c500c454002400d40f034030756003038480302d00c0c030703420200300904d44003601050341135203084802e1100e9106c0341d00315910183c0d0594214120440741001c5030400c640c58002c15000c07801e0403800400c001e043e101411040d4414a541c840555400404591030405480750070350203a503d100810114401c40e9120300c08110490002c518884507040ea00c1c60120000000d800086940c11011505410b40c850380c0050551000c49600c1c43c02c040d1002449038504240100982d400710140104202040086800070041424408000030b40b22009400d19000300710b00601941c20542e1351380c0745c5080480c001d000c0039081202c0012684840700c914425400041045050162240e04c06800c800000c0400340030034a0759032030011103440a89098143d464 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 647310908 1250 647309658 647309683
    0xa09020d021027081203090106050d060c02101b0c0f0c080d08010812030c09032b030f15034e11121e03010306090618170d0905030d050108 61
    0x10f040c00b00740056076000c904002003107641281241c5949540d200c240c010015076000d160301c50b070b43c0c0c3d0f51282085079640106030b0125898095943c8440c80300302c1c2c60309898030350b503c1c141a504290b0b28400c5070f034024480e00e1000c50140248840d95955545d41410304003060f000361115902845090492683c040d01c42409403044070054412412101c42d40300c8140409444000c0c0a4004102145c80d0341341040b80101c20f20b110030301100b9010f10340c241c1050500c0c10b6030100c000642081d0841c1c190080300d0281c00c451400c50b00030a1002407668940b0101d5030070800d5050a425050020b4581d100f042c882500802c1019241076840980514035140040c005408202c040c031012100000c45510041150451a800020420b43c0c0c0c0c0c41507200c101d946813a060703000c1070006000c0004800c1c8055036015180007482124100501284200b14803000911058000c0204005284000404501801500c00b0300d034000c4012071110b11a80c0d41c142550840c81000c244669108d004112001042107003004050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 647312158 1250 647310908 647310977
    0x10e010c180608040f080a0806031b0f040207020105070209010b2203020f0d03051308060402040b01030216140c13021812120f0912070e0106020c0105030a09020d0210 73
    0x900c150195150301c4428032461041c0254000000c051043c044800c11040d6401580b003a134070320032840050402c00054400a000380f01d90b06091500d4500c4414100e0050802030111105292004c100406948403101c00c90400030144960001070b03c45810380c9008e48424004140c0314500c0c4c80712481c014001554100d03a0014120041026841e40300780045036540c00c0d83d218010084609059806220355412140c1c0c00c2e421680000e99401d000c50103038080d9100326010f001100c40780300110240e005103064682008070018941c00001c904181c2010340035559020340d8200400600000d2480352680e0f0800b000940020302e03502828403403100382d944940304071200b419000304010304542d103520b800c050000b5520006018030210005038269501c040c802424164403a40500200da110075162088800055102d8004210b4900100f01400d5845040c1d40c1c0f83c1c15070340c41e4107a5002400c4e41050607600120240000409078840090140000905480341c14081125906c003000102c4a20320040510 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 647313408 1250 647312158 647312177
    0x303071701230d2306060d0c150210050f01031104050903040b0c010b1207060801170607121e051501030b03030d270b1b03060f04020c0709020408010e010c 68
    0x118280300074409030000c03191000c40051045001c42c0030740801440140c51140c07035031504e480c141845181d5400c9042008180d442c151102801d100c0c0356003070700308010301d03c018482d800d21580003d5031080001e82c0207841116085030800007000c0c11544195610700c12904084014424842c2d00b0950b040c020406072010000c62034031414580e00c0340568007400c03459000c002054a480300b400d4004001f0580002c1003083d451030b002414540d502c08030701c9900081090800005841040d0390384c4124808944405060a0303514000c04503001a80208a0340c6101d81c1d4603225500720300000302080d03011519040000f85420180041201c0c003e00f11283c5042504007401d0901c951804000e03100c4820307800348003140d030a000c0f1a82d401001d0680807401503a0340380750211024081c2540e82c03503000b00202030703440da5805401d00c4d031a00707240320850700d603504500801c0c0040f8050078a540185002420380303060341c2c04140c403400420117030313480b60740700406d075a44131038500501c01030a224883d1249014100303520320 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 647314658 1250 647313408 647313419
    0x141605011d010305060111010e010c0e030f120306041409012a17060a0b0d0510060c02010c02090c0c030a0e0f061611131407020106050105271906020303071701 70
    0x70240c0440c0707074101a1510b010581030790098800c003500f0603601c00240203509145081600038102d8100d80d10019041da03c11440d1400d010414030100d8283c80050404607810b85a034901c20350000c0c00d003940150b80d40c170f0118021136100c40e0440c05505600e0000c5418100d07a41c40020000031000394810303055416083c01040c540007445a082002c030380048840a40d1518005070940a15a0103040a6100058001d035510000d40c881e0344501c2c00d00d60006441d60b25135004031540c1c01c600314020301240c0c50495010142c41c00c541c909500480c042c214030301d0040703000c0205041d60442590200400c0d00341e4280c0c02d891409420090f850007081c2d60307050030420782c11641c003a034401e8000083d10104800c5420903407910f400b03400c2100c02c0001d2005200340c4000803c038070101482200c9030b4006518020002c2282e6100d0f104641c0c0860448842014610809408042c000c3c0c10110071a030201400d0035a20000f00300001d40c00c018103198000c1d503224504a1006031012448002103030341491a803005100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 647315908 1250 647314658 647314697
    0x82407050901030f0207050a0b100906031121011803031109060405130605090709080f0109030f11070509040804080f0303090d0c02012304090c050711100c14160501 72
    0x206a00920f40818001c80f0042e880d0024460500d01404034041c1e1040d4006008500c100039004568080385a8070190f91207655404840450200803c40c16201c42d40101601e0b0101030482201c120f1050300c2640c0318140390341400c5074565582c00c00d0108045891105040d0903124014410703020084803894010444002050341c8034600910707200b80554080c02401d003006071f0041c07020707090252124160b42440c0e0000741c03202007244102c0b049403040008001e030009043c0101c07100903505480c2c0c8803421103002800d4801801500c0c05003060310032200c002a9035920380000d14000c500941c4201c0d47d8a0034094014288000320200901e0f0380c0c0300304280300001c080000c5c16072060741d8525000b000c0e5066031004855641c508546101d80034100512107414014040061044400000c020071a0303c2c0103190a4039180500d0704003070401c9044410140303141c140000810402041840c20701c50694184e070305c5403070608481250341819405030490050191807021240b02505c8242000c0d101d0390b8040164030b5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 647317158 1250 647315908 647315917
    0xc030e092d15060a0c050303010e100503011514040902040912030b090403090e0705090d03030b1c02011b020a05130203060108010f180c0504092a03231504050108240705 74
    0xd0003201d0001d00701904d188903a58900206a000c02941d550b03580d600d9114031a110150b900440042220300001407a250510403140f003203ea0913545c01c48207203003040d5189801c00d100d03000c98005072030300400001a0b4861088880d8140302d858450061811900010200c070586200c59025406d85001e200c0400d411410003800c4a4460880400c0c0e07982c1c076801165540601038415801400b49800790302010313019040341c1a01032054035007c60010011103000e400d0248034078060b01140d4901c1101c0c404802c1941800c480c280050400d103141c80c2d4a20200c0d41951030f41107c2d04407580e0110604c03282e5030740000802e00400329000c41e009510f05181c18042007007640b2095011080d40c0d603169150b0136020301c058500400600d90100f1811f4804158424141005408002d4000c2081014101140203215031103a401c205460040e51074500d01c0080751081e800f4147c003840e480b002c0368444041c0d88900409018204803c09400030a4900c0d503980001d12140c514400840f50280400c0f560340c1e44101500e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 647318408 1250 647317158 647317201
    0x9010e070914010e071e0306031703070831060b060720010201330506040f03050f01020309030f0a1b150c08060603150d080d020406020f07060c030c030e092d 69
    0x1b400030048490742034008018651005100d080b41039046005041a40d000d50b1049041d074540074030365500d03001844645e01d200840044900004040c00800710b00650441000301e100d0380c0000303001401440000d500750007102c400c0700c0c1c110100303180c0c001c07126182200380d45d55002030000344100345800c00c0740e00340c00c04140f002c111401c00480b4222a40038105142c4001040050301c0d0030782e6a9118551100707401c00c5404195007610551003006a2503405108603403180c00300c030700030310b01301283d801141c0c0207540b10440c050204110250714941e1315002c0403c00043e00d21868400b003c0035554115001510781c06542d02090000000401040317803200e0040b0780c3c0c0190741d940c816000311070160001d80419280711000d048114041078502c4c04040e1079004009513031040c1c00711401207121044255443d00d0074028400000da1003048140007074000d07010601498428240b103590603421b40e0100301c030003808035481c40d400310490440300f00f1080c01d54149241c00103402e181c44194940343c041e00e03160030a912140e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 647319658 1250 647318408 647318447
    0x11a0105071b030803100e0f01060503092109010f020607091e091a01140c101a040207030e13060f291603121a0909010e070914010e07 59
    0x61001c111245a181c0101001440c2c1d0030401a180d08020306150411030f0403000a8410900104280c9001f040c014410b03404031207022401c0e802d060044a4580024000e101580316000b40100500d41c00707504540c851386c0d80da4030b0949506003040010721a00043d81d85030159000502440003480e40070058200fa1580743c2d10401050f000e00003a540341030043d500c540069840c2c08144100c07011401c3d04c0c1c14580100b40e84070414040744a058482901c1039a1550007160f00c02d0150004010780e81d0440c244280038286c013084d1107801c01021032305a81c00808201c0000e904070b04840018901000300c000013406044003000381a05142d42c114020710745001d10080500304903000042c00d146c04a400034151903100080d91a40c4d88460000c24103018600b0450101d0b1507040780058045452103003c0a4520000801c03c0d84450441400103661000d02120780075503c031344142c02c040408000c040b000b04642c42001840141c021b0b50000074034010b030000d9000c85003036028804034540c80804582403444400c0ea = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 647320908 1250 647319658 647319667
    0x60f05090a0f02130f0501050406060503070f113309070b04030f080918150907090302010309022d0108060f030705060d02070c150305090106150e030a06050c0912011a0105 75
    0x202050113900c00002c882c0c1c140540090b8111036034105034100d5070140e07002d010140c1c036000c00b42c0d040c1c08216014000102c40704105400c007071080000003810140321007643d100c20403155203d100c1450303c48034502c917070300d1100020449200c90b46400e9809803140c00541603da061403402c290603c030324403000e00319a0040c51090103104000089aa06030070081c138403640b61030806510344c01280101c408011041080400e00440e042500b042c61141800c0e90725503030402e08580c019070041500c07076070a982002c4090300080440d0a00300c0e08000d0400054200d264245041c400108845002817001d0b0040f2810740039141c40d5200011a50192002240c1160300c130703403100034000300901940d600a480181c20f428001910340802c2000385000000b550306000300d41c1d6441720a800ea80040c4900d418492071100317090501c0380b20b011540800c200c0142501d41505282e01d030760090350400c0e40c60310701c84500022103440030702d080c140340380080510300028820840c09200494500c0d1442c0e840605000c070014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 647322158 1250 647320908 647320913
    0x801031e0309050306011d1f0b1b102f0a0f0c05030a03060306050f1006030c0c0b041b05010f0504060c0f0812061302281e0507060f05090a0f 62
    0x1102800f9080c040e088450969540b02c0c4a0003c5e0003401040603581003510100d09405030048050700e0000d6400d01d0601030600e080c0d1000c0159005403c00302941754840d407222100c00c02400040c408520303081d80031a000f04018240d0068807a00c1009000c1540b40f0160305160b402101e0a03a1200e401d2410040b07500505104196400e0001000003001d40c000018500b100c0c68040e8044004c0da03001e410104540e079980e103914004c800066491081000d0f1540081210502c2038000700500301c030901c2e00c5007084001d81c0e1151041c0005440441d031039544039250a80c07003000800031400600091074036444060700c1c00d401800c90312441c02030000f0010b0500b185014081c01e0303a03d01540d43c0e4000d00c00d81d80d0307010139030150083c0941078070014401c014040180100c40c010b8025281c1c00000c80141442c06103c48171400111243e140f803080501040340501480e903920032179001900c81d05a00c5196446000b46080800c81d05464042c44c44035150500b403004030040001c944048641c406440d0050a03060f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 647323408 1250 647322158 647322167
    0xf040c0c060c21090b10080a141e150a050f01060e031606020d140f0913141617040f020f0a0b0301060302040929150d050123010801031e03 61
    0x10b0425080d85010b903e000c03180c1038076900180065001e4110300321036849031002c40c000348600f88118801039108080d60000305107101d0000d045001c001e02100d41d4032440c02d0042c0c181950681c9a100340e500180d00e41006031041224a6030311080d041400c100901d41000c1e0302c003201e136040c010343c020002d82003210101c1e41c0b0100300b174001a2200202c00d44525070703610802540c95058021140000b02881da154444402c2d070019910510030010005046c140c20700300740158025032a049003111611100303600100b500c00f5815a0042054600414001e101001c000c2c00e5030010031b0340d9034055001d6030b04200108075501644146603a040f144010551000c0001440300110b68000307042c0c8400000001601a8040c1e0080c800c2f620844801e000d48954085505807120400600303c0302118400020300c0d0600d000c10120860f000e07810111402e00071078500b05001c840c026000119112070003050754188103040600d00360b51100c01d203410b0b0840c0d8155501d400c0b0395541c4c012142d00d14800d2110000406006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 647324658 1250 647323408 647323427
    0xa1a0c071a040302010c0801050303042904090504020306010f050a03060b040b0307090b0f03011401090504030908031201170109031211040305010515100f0806060f190c020f040c0c060c 81
    0x70341480c85101544154000311000b500e00703c001d90b01e000d00d091101c0c3c0c020456079040f00c0004000d94100713440c10702c00810303150808070310132031004040c40010640710144000e440900010705c000241440c20f1b10501d031804406030003400c0c0301002c4090401c2243e0380e503070354401680e40c002c00200d10380030620301003009441da001c0016414014110f020800040c0c030f6104d0804c811045903064a0b0072100c00130f150032210341494690780e50540030300501034804243c102642103480f07450210751041d50f8500f41811508540c42c0e0034810100000100100a20301c65104450359401c4000c102d120403c0c2e40c060300c00c24800c0030040e14180c5484000d0100503086040d58001c6420200030b104902d0f06140003041c030707180030f0314242c421408808405002c41c4a0441d14070703086982d0319210b800307459050820056402108800c240c2c071808100c0011200791030254001c0001c0c4585420358811203910400810035204103415000d180f03401012a100c99020501d07100540d04010001201007000c2e0048584010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 647325908 1250 647324658 647324663
    0x80102130e01032109031a2409060405040c08150f10062c04020f030108010f4a0610090b0a03080304141f0e16231011010605030a1a0c07 60
    0x12000412000284001c02244c4248078101e05500902d56204032412001c030301400d1540c01c10342780b6001508606103540129003250207010b205a010760748a4540345016032a41404880301111001e0101d00020fa0340e043e03801c443c1e110041020700e4140341000b070101440c20071481000003920312461208004400700084042e018005540c0c880500c5078024840d44280f0400e401580781010084d0004107511540765050311201104071084e09110395aa45004501e019070a241d01681c1c601500e800074982c0110441d4100f4080c0806181012005002100d29480003102908145007480d656941b40c002e04162540b242e012516078581b0309180d80b074102c80300c0d00240e042c03041e00300201c040102c1007940c1c0c1e1950454101485a8500042030584a6000b0409900058040c002c01c0c841004c0c0102c040c6680c000c04a02c11402c0d4540c03000180710420b1031071419001c0307095440c000004010070f014810143c0000d030001e0000380026550800c2040c0000544401c0a00980210300525101021922401c0c3c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 647327158 1250 647325908 647325923
    0xd0605130b0310090b040222092312220f03111c02030a0209060f041401080d02010e0a02010507031e080f06030604210e0604080102130e0103210903 65
    0x4031031100300001055024440e80c42440f5510302555683c445002d41c0c800710350310850b484510b4450743d0a000704601c05160505054107081d0031004000003a2092414250054035008030480d6085101020041e4107801c5250f203403c04000855030444210454106807008002c02d80949204003c0000304021074000241d60205030a00100b40688402610000c0008403510041d0071108000a40c0c040046034000350076402581490b005442e0840d141d50340300c2c0020307151304500030910380058210b80740d0b3f0f8022800c585074040107000c040004c00943c4981130450008002880110658964a800c5180000e04021000801c8800c1520800c485000384440c03c140001c1071000030b4015102e000102c560303074000d80ba41c400041c0c19107000140180107035007011030000c14101c44030600341030140d6020380000740804044000b155441e02c000400007412401c0005856680d000d0703014580024551200030f04034203140c0140040f4410680b140d25030303a034803081003e42002106041d605090181d1024045a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 647328408 1250 647327158 647327179
    0x807050723061609090207060f02030403112a060d111303120518150918060406080c18070315141203030c0702090c0c0a0c08300d0605 59
    0x11400c1851071580082001c10340320a56191010360301ea2207660340780c0c0c03070000c0c400442c10411120941d004115540c001c110200e918800c6964803400d0780e000380c808500040b0300a518a005020a1000541c3c00e1407002d00d0030b81c408603608143c001040700100d0360f48200030018a620001c419680300301205089808101d40380d4030a442d003510380400b07600c0141d41d1800240329406880c1d21135021a03511419190b507150f210796951f0103015045180e40001c50004804001c0c401a0f9030381d0310024080400d1041c03800240f490040c0900058803c3d030740c8210000c1d48140c0e0012180d549400794003140150144030503006550b2070741e0803001340407441c90140702039081d901c01007094040807010880e0722000f644c0c66200c00304001d007419900e200840c3c1007031001c44144001c03801442e0003403c054004071000d9003a0b0502c61034100540c2022a03091003101c03034501001d02000090003e0102102c0c248486220041c0728855002200c2819008441508210400140190304d00a40e40c00203024120240c01103044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 647329658 1250 647328408 647328443
    0x1082a0d02070605180f240403020109020406080307020a09050906040206160f08030105100f09060c050f0601060504030b0109050403080a0504140a0803090c1207030f03020304090f0c0908010c0c0308070507 90
    0x8114031748079109010301540c403107840000d100148404017590b42d0000302112400b0000c0c0c3c4003070800007a20850071552104041e201683d514050403020713248400203596110814410045c00313038119844a00380904040411014444c045207070303070344290162400c4d40c0e51800c4ac00c810901d500c00400081540b12106100028440010302035030607940c06441d0b10400307182c1c106081d1901541e401c08000016541c2c1070a03c40c0c24810100c0b500c08511900407165a80b040307007000ba007081c1b0242c00a00001d10042408c00600c038050800d2170040119080030402400c16840081c80d800e4000c002c810b00700d4030b0f5030118081114203801044c0301c07503d1105132103240c07041c0e10b0010789903401510310010a1080800340291850144451108861181c00800d0380c1031030b56940c3c02c0b09050785001501540014400091408214011040303441e181010018500c0f0b0101406441e40140340c101801580c54101e05904964100703904540e203d826040c901055075941030102c90901c0760b01801407030202910b0300e0045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 647330908 1250 647329658 647329681
    0x51804290a23061530040204060605130509060a030501022a0d02031909051002010902041104121103030c010c05031618180f0903020c01082a0d02070605 67
    0x46210a85a00540c0702c5039071881400d001c4141c0b000307a8052048110220030880001c02884072599413807410320103414045000d54190403130a441d000b80014038080000b14a46441581c0281400c0d0810b941031003080f269400010f040c2d4042d00b4041d90811000c030b1043d907592081d403401150301030002d540d50074158030111000540b80c0e20070f07955140b10041c40755110401142d0000e92001c1c2d036000710704240320200420321061b001a0a038041c040c070841e000c103035a01d03000610b0000140580020a807044544144000c550040b503164004407418482880030b10310442d07420503c030350402c00f100540034581d00024207600c40d444140d2070340c3d813802080120140c2c10101961281600d1050724880168800d070a0707450101018948160111041c400d01031141d442100703410721814220005420400b1003040c10480e0a0350703c0175405a80540d20103600c56a1000081d9403005c0e101a03207001c21b10f1510202100301504078290403030344a010814003001d489950554107960780189013403140d4140140c6450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 647332158 1250 647330908 647330921
    0x1509030c02040e1207171201080d080f07080105190b03130506010504020f220f030305030a0b010e1302160204050a021309020a09051c0609030315051804290a 69
    0x34003070b0741003010346100c0460100d030001900221542c024904032040c2d403a6650640a202c07400321181c0d05014500b618050303c90b40c5070107000301074010004407090703000140080d1030040801c08004807400402040719400110103045801c1036070074404000100c4442d450040480c0c0202d92116404000c00c412000380c1104044628051b0307050b50000e07601da0041c4800d1303200e030390b0440c0b0b101d2804205840004089070045500d05010002c2a2086511000004c2045170680d0040c1c0c001040441070000c4001c2c24032a505050b6800d0030702e20200c60704000418041001d142d1b14030103c0740c0c041200d040410409030100304040d4001c008110503c0d104001900035040b8009406089582120205184240c2e100b1030348401e0b84d079254880c00d01d25040400200d4458076003502c00c110740d0300380740c0740001341c1c10301a00a50900c281c030041209244001d08526654190b8440c43c4201185403420900c0340d504000c65401a403c64001c0c1610b03e049902c00550300c54040328101176500c0c3c40708020401c85a6031012 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 647333408 1250 647332158 647332163
    0x1e030901030f020306031b0a0902161509050601060503070302040b04080a06052202060703121505040c0507030915111f1419051b1809061210091509030c 67
    0x1002904403980401d0200d004c02c4541e190154000c21945400c2072178040041c0240c0030080405155a44401e0484181c0c2c12152040d035100c100e546110040214140d60070081c40882c60042291074000d03240c182d80c1d800103105200a2000002c007150b0702601c20780444000d40307445000789540d10b03602d21045a850030101c0040d00c034546000d001c40c0c0050b0401d4070380602c141d01d4003400d0f401ca540d11703000c101e007651140c88100d0034000c46e10000000361303149010304c80c0c000500381c144003003d40c5068240001d4408011303a141c1004010010300c00020341228040d402c1d034032442030304080c901c1031a4042d10004444074459459118450340c2c074203200081c840070820120b07007650074003024013154401d02041d202600d1035880b02d9100c424100c0e09aa291744a16070202508003070400384080300752502d41641c0661074901c00c5035900403c24519041100e900354104505560900c00b081100c00c0c816100c600c1d60602400b45034950700b509060010760461008062402c034020030034540c0900e009040c0400d040c608 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 647334658 1250 647333408 647333411
    0x70305060121120507060c050d0b0a060f0c1703040507030c0501032309070b04080a0203070e040809011b150b040b010e01120b010c060212010815060f121e03090103 72
    0x100c0c50b020b031420104101c1d12140100424a41c86954005034090211a60320401606004400118800340220104944941c171200d5903090301203074403401d0700c24401c040c5006400b4071100300003803584680c00a03501c481a2412030748071242e91801c5080198251400c0303038860008000d000a02a0200f04141124807602e81d0341c02e03599958006409658000d007102001001c03140350f00c03000b4070070920620b0744031000400f6075409070f4172002880102e4000740c000030b5141d0310890221045090802060025191744030364420a0f19042c0c1d42c0c074044d0700c160b020307103410402003501003001e01c000300c820050115401500c44400b0295246540000d2410b05065446941010040caa46500405803564940c1040c0d550303207100810801c160001e0901c04c001141000030400f019000b0030841d01c0030b080007440c010f401c00415494401801c0c5003072942c408010303900d450b02c0b0501c4103d40e51208a100015010307110304191000c81c00c0e45a080c401ba800e4680e802c03800c1c2e009006060381d8040020188280d00342c80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 647335908 1250 647334658 647334661
    0x306030706030b06030403050a110105091b0103061a0a110a0b040b060d230c030304090b2404060e1c0c0e070c1112031309020403030e0d02010c12021e07030506 70
    0x2800c60a0710009060144c1081082021502091281000300102502414642258007000d8081421076004503810400c83e00140d429146414080303041c0e035280e41003441c3c1801200e04001c0550100307006408018414640003070b4140000340100344080001c0003d07010b90340a0182030900a000c070104450031145078109100003110343c6007012001e00c1d03403900310840c10015000030310105450015521032500354801d14000f1015664108000c101a002404001c900e04403d1000c2c80030824040170b09a051b0480c60304505805c508504c142c50442c0c281e0b1414040400d0480d0208103005a84041c05008041d494810004c1c08082c1c52034408854484408591540c0c50301d00450783d00100340d0000f001842c8100100c59107240066040303e80702e07001c6041e80e107403192646480000c411a1b0744026036098020500304107040d0000402c01154405442c0e8230000040fa0380000d081e40c0f848400100000b80015136810003500c20028091803020040381c3ea52082025414290b5aa40501c400ca445104a00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 647337158 1250 647335908 647335919
    0xc120e041b1b02150403030c1101030b240f07050303070207080f0c220203040318050303190807091701140c07030206040f1b091a09042a09020d0203060307 68
    0x16690050700080381e031251022402685019403070b000b90107069030b2108050b5010101d40d000c0c08001c000461203901c0d041d903c20294030f0f014030340e5909102043e0605181070580d8620f6150300c99160090445038646800c059130441c5e50349154050143d41d0b103865100814000c081250010055000718800c5d02121117403581c90b4241580d403c039080381e02c1c400d13400030180c1a0b1282041c03111203001410350710110200080d0040320204a070812101a8000356085240410b80381121080340050102a40990710301540d00ea80c07a460b00d42c2c40403026003048101030006600070300c01c0c0008005003090301c400040003804000b2140c040e00341c01d11102c605a00312004160007590140490310b40036410b40281038240d44640b1410340c00d10b158903041d9100da5403050348040710344200d610500038107102030000030115038880340c14045600012455000c0c0c1161424007010900d0036115480103000b01c1c084100900c080925201e0120b0143e100350842400881c1011f541242500510b2107014243c0407500c546940300c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 647338408 1250 647337158 647337191
    0x1b06050a1112370302071a131112010603030306081504020a0608190c0807260a0b06070c03060c2706050d020c1506031209010206011202010c120e04 65
    0x50418002e00a0200680340803200c103840c507004140201c50f4450a00003608540b00c452100d400301520000764001030314010800f01c0381100c0c00c54446c9042681c12031410954500f021100040d01504104403600501d8181c0c2c0c0d00480b030241003800c1c00092001d04c2d0f0702c5c41c02034064409405840058003034269014014a40c1e60710040c800d176001400c40c00308903d0324106883c0ca01c009821500004c0d04440120003015150003416070042a941c1c5081031840c001000405082d481045040540d03805a900c18180081028054029000000000741c800005000a02610410b80010b2088008003400024400d06a001c0c410030815a290300b54210312181403580d0940042a04158250980d00103100356845103001d41880740140f40c0040c503045410507468604212014840140050031041103020300b0127000e039401011265220307500b086400d100103500c0320014040c2031103419000014105680c41485068000c580080514070841c4070324000134000b0b8000424503009604000001c410078141 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 647339658 1250 647338408 647338423
    0x40911120a050c010c030930051f020906030406110408100b030c100206010303051821010c03050603070509310606060206041203021305030d0507140a0b010302010c1b06050a11 77
    0xb5035641f0140b6810702c80101001c40342c2c2d042c0340c2482103500d907498445103920380600695902603001402c0000041501d0305250104041c480c004074018840b115140c0c40302001d803600554010804910328240303c221040c6d501665000c20814403840c880608070311940e034862251598140d040d00d000c030076020107110384030380360060b41d04c01680880c0041000c68840d9010301005011004441e484440001c0081c0d81501e00956607414116060b480701e1703a4030400d00c40c04a120f151401c0c180240e01d8020000382d1500c0052003014081d03920b000c0003880030003913100c00c0c58842080012610920b40b9040c10a01200e2030240e0407602c0718078080d008243c0c3d50001507464451a405000b02e2282c0d000345108401035044503510030302d820421100030030213542c00d22283e14508055910759403102c4441c2032808102c2da513420815074a410516001010074000440c0324107694080c200a07036005850720b40f80c0710448500e0407080f02c65000103c08980140d2042c01044003454642e01c9a140881c9011320300e0300c0e01c0e81c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 647340908 1250 647339658 647339663
    0x10e010203130b011703190311040b04050301050a06081b0d08040e040314270f03060901200304020a06050f13030b010f0905060904060f14041506060f0806040911120a050c010c 77
    0x87c81000507100641148005070000703031601103000b40003960b00b04d4042c1c102c2d40004401c1580800c00340118102403080d41d5008a203034078107002c0c49103009080c0351100c1088840303101503500e86004e08420748031041010100765010074100e0740d60b5611030803005400e0040e03804400080701502484c101240d200b040e500d00020000c03c0c2107150a040510002c04145100c280c0d402000c101c11030040341c1e41c14032040b0f10540c10b0760004103132259207402c4a00c003030303561208807848a0707410300621003d6220214603500341c800a0070890b5803404c04210300c0629011341601e000810341c40741c101100300188454814100d95020344255000c80e2900c26400a840080b200d440c0c01a0080002801151082d001001000a60000040c0c1c3c800d0000c82019031100450b002e48884048408490034004288104d200a19051501c014940080b07800104040c0c0c0140c200c91080f41c0358804031091201c100705180e8816002400c1003507045070207207540d44800c800310702507910b0f02071074941202c80d5010322403c15515030b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 647342158 1250 647340908 647340913
    0x609080a0b0f0601140a0306090e011a090a02040b04030c08010b010801080c010c03110f24010803030a150b0301060e0f03011109210105070c12092402010e010203130b0117 75
    0x1d60380c2030142c01e241001000e00d1304100840202c450040035400080c11007858554000c42ca082c1010700010a0ba100d807560403001c0d87c0b5000183c4044000300c05450303581c040c1160b4601407a00c83d0290b010180c0520781081488400005d00041040049501d2500f02c0c1c1c0c041c0020300818208100540d0411003d1151541c0340d000101c0d00740c8950320814003c01800d10078105116224080050729181680324000c2d03201c941d01503055151484a02445002c81d0301a5209003001581070813030a6850b07000203010145c8158481d00c84850681407507090b280a8212200c003182c403582c2d80c80f0000c0c5482d42804c11a405003210840703110007814180070b00084103c034141c00d645080e447c941407000380310910070700b1030f801c1118440980c00c0010a0081c50300030b1825981d807080714062800d00c582d040c00105106018070414040c200200035001840f10805658100184201d441010041c1d016080400030440c040d44000308118072800c902803150b00c0980078003480d0402c1e80e00d0f600c28241140c400303102e002d0300e81d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 647343408 1250 647342158 647342161
    0xb04110904020a020f060112170309032b0c0302040618051f020a1403091906020a150209090708090d030e0a060b151303030e04090f08090315040c0609080a0b 69
    0x1d0800340c008150900c501c0c4104c0310540303011100da50500c002a000110717500740b0182d03a07200b03101600096814129561480c50719500f010480c00f03035240301391030400a03149104502e0140030003460113140d405000151062080c00c41140c00200254094001c80011910f6070f451b15158841c141a5101503170300140c0f0f02451704a07000c41c1c80403010004900c0d00d0840c41240305010000394065106c00040324184011503c13550076408202e4440c10345081c0d103440740000403041002ca42e0004d1400000c81c2c11485104c0440d064081c008042d1003040691600441c3d00c0050228056104111a12036503d1206890f40d02200d240101c0c01c0c1c0703903c100328140f950b00041c1c42c0c0c13002c118564001002560700400e100785030980311407045040c2c2c20a4001900ba003105040c10001e040c0c2025032078000c510121810011044150784003240c03030140b084040e080310804107001d00e280e00d0401c8003450400096139005060300d410b25020b0710070a8240154000105a4580041d16003000224802c0d42a802070403045103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 647344658 1250 647343408 647343427
    0xa0b040f0e370605030714040c08040b040305070201110619060b2703010b030a050c03190206030a0c0302130801270c0b0a050f0c03030906090c01120209030a02041e0b0411 75
    0x1480241d262424102d50755071000550340d0360801140e80104500e2200f81c1259003080e00b00402c54129009002c00d220381d98040000143c04c10381c0d42c1350311030b516050594840100b400105d0384808003144142c1d0714810117003480400c40c00e180b0507203401c03501c0c02c00074003c140d11485458010b010303031260000c03d44c10140d4444552100205d154074030440107400041c03800b40490020307140101100055030f09400250704111503013010300c454040c08400e480540c00c1100f02d64042100751100400d03000c1c00940e00d00c0314044092082c0c04807a10514056500b040c101d4560043d1070091079048103901030b191102c44054150354000000c100c1194100000001c960301e00b00400c1000e500c080c2c1c60004004080107404820006200034084000005006644a24244000078a8a54060300d0285c1590002d640c0110350f0f83e115609803c00340a10038003607299460000440d2900780040340080d031050402e076181c0d5410791448031121a40b81110310521548882d80144412112010103002e094070041000004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 647345908 1250 647344658 647344741
    0x1110406030f0e0610061103070b010e0a0e07081e0d0f0507060e0d08270c10200a150e070e060d0b0f010801060b0906040e060a0b040f0e 60
    0x5000c000080c002c0b40c90991540f1160415000703c451180d034805030202801300942c000c21404892903040001d5213400100c0d29042c800f04414030400c0300303010f51070001845000f1503070081c81034500f2080840e1a0540c40e5a112502d035208400d8108440d42c4c4c1d0752200d41c0000c0005083c12851860362070b51082040e110004440d9644194025105607450b680c492a07418420020444070109699407103119050094003042161003401540c07044441d1400001d80007003011822541480003111940001c460806064030231035030202800c407104041020401c018a8045400440c0511403050b500d085080e10808400b103441d1189510400d40c000036041c4440c0d181c4000b010741150340141064002c00e40d55440d084d0b00c110440d0030021096210004100c8610700340a484040d0a02400d028105240b0310701044030f500440c82000030841d4254049100c0c1e840d0305140002401400c0d01c415619074031180c2541d9003024a1140e44c020300310b0b00b1b0000e540884076401c11a400c0d0300e0504d410a100000105003032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 647347158 1250 647345908 647345921
    0xc0307031e020d0c1e060309120e150408060a05100f031209150909060f03081c02070506100e01050a0503030703030507030219030509011808070f0302031306110606030111040603 78
    0xe0f0403044003c1c0a40125060541c4070000300741040c81e01d024031104050060000c1480c0e44074a00741170a045200f0005500c000c844001c1041a24100c01c80c10714030320000d0000030b46086814020480080c0102d09007101027000ea04c40c481010050002d44c5562038030106210081c45100038041c5468000c2c000215622011010310301c00340b80048c140c81e01c0d51485481d5038041115003010403428002000a075900d405804028505801050106850b503182c04402c0d210700420405442c4510350303030f854185880c0e41a80e4146402c10215400d03454521100c0c80740c0103081c01090111002d48000040310328050300c0c0d80301580d40180183d81019455038043d00036040103080170041c5a002e000140d1032003519890342c49001c80c5680e011942c0d080c00070201d0308584410180100391149024040c0200e0b0840c0e0448203d9503200c41000d84007242ea090881c114056445150a01c49420340c0002c0c0c42503211000300da05007080d03015a005615035a08160032a42101501d40a49009103c02c2040306c1c0a0303406078 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 647348408 1250 647347158 647347163
    0x6120a03020a030e06040911120f070e060705030f0307080a0b1c0204020304300305130314160c180e010e0712020d050601091e0c050f03180d020f0c0307031e 69
    0x351b0400d920b0708886000c1e0307010040c88542006001c204030030003602c5100300c0ca030041c8402d0a641c00b1824440340c01004281300300d04003406058001201c00030030608108550400741c086111680f6810943e1004000c0b144c281d588550060801041a070ba42c0740454000c144110314141031100c811a85d802d01001e9000100281c4a02d950342000c2c00c00b201d220325006920740e2210349554501503540b0030280455070301402c4080230131a440c904400091300180600c0a20360409001c903210340b20a0044030120000a0005052a004410000300c80b603000310180040c1403807403018400d61989486080c22079207450f02100303141d480710004000315150040c50420705400504030350440801900c4080c40c124007070b401055015501c414403284403001c0443c040740c116580500b44a20072611600600d0340c011103080c200a0113000000ca80300021824411414280e20420340e500103007c2e050294990300c1c072200590560207840a4842c452402041803000c0c1c81d0b00034149840c0040c0700401010141042104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 647349658 1250 647348408 647348419
    0x903030909090a05010507030516180308030c0c030d0605040b030d1e020c06070c0807050604030b0a0513140d020105070302070b0c18120105250e0906040b1806120a03020a030e 77
    0x3c44000c1802070281d644600907030b03200815541803403108180240c0d400700c0400c0070018000801c5c0e07030107001940d1590880c0d410000081e200c7d210380c0b190503014481c4c06d4280300e6511001500a915165942040f0304842d4111407c20402e0040000d0503102c0751413101020008114140880b4042248020884d03c0070321441190702d42e116400219601398001030042d24028607422040040c20700801c21000070b41802d99520303003040d242d076459190b4594081c0581c000d56454000040c0b960050300f6104c040141c202a41490004020520380c1e251420007000c54015404c01c070015030414001c2c003c585480c2e50002c0c110b8941d990b041da010082d41c00942c036a80c0c480810003d0355010782e0307524404130150500d440002803a8101990590110405032841d052134950342d10004448175000503001e01d0019064030403d4441d82c0d0200018024142040d909500c0115480c080d414007a0441d2007510a800540303081d80703440c10303c00340940e5599403900020f0050740110407010001c2d01c66400c4031441d0001414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 647350908 1250 647349658 647349673
    0x1209110301060308030a05010603060305060c07050c06040e04030806040204082107080c0318030a0803040f051c02010c0311040b16080705010c030b090a0510061b050f060912090303090909 82
    0x1a003511050f9000742c0341d400d404014001c0880043c4182401805942010400b0302e2843e41c03051b4407400010308c00402c0c0d00000c9100800d00005004e500b149040043c2040c0c5d8542e2a0f5000700c01c280010341d000e400242c5500001211b41c01e0910846d401d42e00e0100007001080488040580d0340c041704507114441c0c44051103000002422039000c0e1541d80011405161229811498140075413008101d080c0b09500650b0500045040741040300d0b046900141d006864860b1824a90b1600031080c10179250711540c0643d1110042d41988881114405940c00340b0104400c03555603030725809240503001d51903c0030000304191380082e045d1722800340e201d00c9285041202603201c107030031200c1c10a1310a022031340760210039840d840c1a03120103501113400340d0200300605080151707541401981c021081840b8026801d8202114501880201c5a62120031104c034001810001a00c42c10300365000e040510980c0040d03211410404165030b0740b110058001c40c146000041085500c020152440c2da15006101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 647352158 1250 647350908 647350943
    0x20c030904051003030f0c110423100510022103060d0510020702040507110706030c110a1101020d080f0c1b101401050f090a05040c0f060e031209011209 67
    0x1514030070f00e000d02034120300a213903082c040d1048405000700801c0140b60003c50000402000940b40c841105950000300c58a000d0f070405c82154003000f0101502c0040301c100545126503000c44001da41007500c513400b6007284040260794400b00381070035800c186569101d1900201c4484091640710100a01d010440c007200c2e1109818480032440c20110980c0000748141507050501590303170003129910b000042c070700d8130455840d01c5000c2400b8280806450744031220a0307078411915543c800262200f980c0d6101140e290500410013030b12407160150203407042529106008500c60340c400c0c076180c4594291a81c0700040c042a80d03200c080d003131424002e001606506540100310f94070700792191400005565044102c125002001640100e214408000d9075054035203c40744116000450620041115205c514182070120b0b010f800160b031141711641c0005829038814600081c00c107040d000c3d200101d810108800d02480b0f00c1e800f55000c94042d11040d0184a02c561140c08081c0c00303108034002080140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 647353408 1250 647352158 647352161
    0xa0617031c091b030b070915020c10140f0c0709020c0319050f07151d070302060306040e010e0d0e09071d010909020415020c0420030c040302040903120f1e020c030904 73
    0x5401c05d65600a4003400c00c400c4c103070401071500c0a030000e02041c404111032034200958480162700168000c000e004229403002e40140742c00441c45014903005511a0400c4001000704e8106400b80c0c00c04c1e2044c1c540c009401031700c502c01c0322110b4203000f0107140f425481c070300d90800c51070310350282004003e010011202c4d00209034000d40240c034030510b40b04084180c6c00c0d10001c162030001401c408100c2c1e4401c0c1e82ca414400000d6840704503a07041d290580c407582d0310000140144040824041c16508010706141102d1001c150440680140d85455412061031001d00410306012030b544070101e00d8000c02c080b2044104404c070111420145008030110780c564802c2030170398016034405409003446c4603400c2951501409568008001a01c08000e8003904e00440000141c0b81d605640e8080c0d40007012400c141d8000342128099500a001800001550306d07005200c41840001843c840d80b501d650740030b8035007c41c06240f016503c86040401c1d18825284624004d50007030941c0c0d030f401e100800802a4580f100e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 647354658 1250 647353408 647353463
    0xb040b041505070b0709091505030d2102041401020601091404080304020d1a01050a061701150207080f150f070c0605220b04050d080f040f0206040e0a0617031c09 71
    0x41d41c6d40c0000c2e191070140642c003600d03840d0301106025a0001700610480d100081c0c005034444040ca1319025491f0740c4820341401030302206e0041c0030070307000003400308030700c81e5824111802c1c1d042a03003180c0303142c0c0c0d80708045c0d0300b1208186421004005101c01003008101c82ea4080d680060000340583e80c00c002641c4c0d00c44400c0c51100c5c510590900c01c1c00100410300d0101c510200510381420080010201d03001ca003100704038140102d0035285004602c10680c40e1080008030042c18008046800050030200e07100e03036a2407024403900007020030301c2c0041c0003c520821070354024402c9884074150501d660742d6801c05081c004080d880039071001c1707000e02c440703001080c46c07107980c507000e800080005c1c202030501c5420080d00e0f14890051040000038400601260414164403030740000b04000703c0841c6100140c1244500d5118070000f441500a001460b40e182d400801141c900a041c012030080f817107500742d1640524034801e140580c0415190f4400c03620b540014200c10300c5502c10040d0140c00408080d50f0010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 647355908 1250 647354658 647354671
    0x120d020a0e1905040e240411130203160e01021506120106170c0306040b150307150e03100e0c131503030f0206090616120f050a09020108010b040b041505070b 69
    0x445000410803030404e8030540080403040000750400742080010240c80700e000c651144181c1480c0c4000809100f2402440c038294003001b45020808245600703880040d4009544860f05800c41004c641c3c0c0007402071417000390345201a006480c0303906001c0503007040304500400300c5811502c15140310380d08890030310544d80a08040001181405802e8400518040c03010b10090b002e03500c900240400308102081d055448122040d1101030550700b0000321b4142501c552100c8a001c1000c0c070b074076150981003041c01b840c0801c160208c841103084042da0000381c803041340c0c6802c000c0c0c104440140c440d040c4a08401404160720502080190795801220720f901600e07802134002a1007281b40340f00c182d605100c415082820113000f40301c00d0421005d20301c02c20705140707062028481180b90382d042210240d00a00341074000b10303008209620700100004050030f00c01d01c7c104c0c00101980300200b80e0002c0d8000381c0c1c0555105469607410315041c15100040640b192040b281401070a1000e840003d10b09004c1510075003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 647357158 1250 647355908 647355949
    0x6031e0307031404120b090f0328022a060405031605090a0b1e032b021e0604080c031e091507031e090803120f010503120d020a0e 57
    0x2401401c0c0280200d4060f4488075081004010400100200000419a040e000a0a003800741c840700009803410508010f09081070001040028414241c1e4109902d6030764000d60520390903048000481e00c40d240036543e1740741c03030303444846c0400c03181d03800400c003400e001e005881f80d0700d442e4031600020325003141440700340c25815207000140424200050340f90b800003c2d803841805006504800122088809107900301d011456654650040e40c0030000c0b03880400e1408981207034030001c8200c0b0040c08800d00404009171049104004146103030104510100f0107640280506844a40d65490369500406c4c1d141e45030722050119030de0300c101000040700e803242100385043da0b500d508014088003c24030002401407042c240a883c0100f500b1100940c92030170080204541e44540080a46044203070350000c0b0b00314800440d60084401c510290340c1d0080321004401c0c3c9a40e0b0781d4074200759840d02052003541e200c7c1010f204c1c1441c0350b1042d4000d4115210241082211100d0002c082468514030001c0b0500e007e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 647358408 1250 647357158 647357167
    0x180708010b190303081306020403120903021504080c0d080c1501030c0902041d09010e03210f040f0f052803090b0405010518031c120c0e090a0506031e03 67
    0x1464002c420380391a007a2061504489465510003900480b4010003040d50404000301c04001c00c01507504440195a001d2100b90600c800144c00030001552400124000d03080d00b480e204103240b0540c180c0702142c0c0302c03000400d4112a0071042c0100c201c5400000c50f0a04030900a420b9100e4041c013183c00072035182d002544096141d424400c1d862800c940c81200c0d0f10b441000244a00000d0300300030900303d407003d030310864552102080d140c01003400503400300d82ea01002c1402c42c014407000714259030780c0300d40c42d1108039941c844580d0803440b5681a50018a144401d0303500c100044e0607029a0319455014400b6906101a217940001042d4a440c1d0009015081003040c641003540110704900542441032000d4141070401c400030340140700d10035881d1000100c060904800e5501004a00d0740340454070860650001081c0c03000c0c14444444c0100040c00b420410f109841e00c7c030941c1120131500300185201c43c03a84402d4040402401e0292a00d600b50281c1c10f585c2c144028850410f00c1f8000c145001103aa5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 647359658 1250 647358408 647358431
    0x33052803211403150f090702030a1206060801050d0c122f0907050c0a050307060b09150306040201080403030b10050310090504050a080a3501060c0209010e18070801 72
    0x1001c180410500c00d0054840610303405240500030f681d80401c00541c0f1101a0400100040c86000c112410070380c0b000c521010002d2050b400301c00340084000a48603000081030342008802903800c1c500404001030840300042204e071510710312603c070040c02050000d02a5898014486070300d00402c0c030582e080d449001d0340742d03020110002400004d00b0a1401502c45030001e00008070090000380444040080105101c074082400703208150125a11000b203c1c0d407020b252520401030040910141c1c46070ba00400041d680701c2c030b501c0000d88035210040c050b20041d42d480d4015600890081c00c16030415035544503855030b03915649400054604030352952600d03440d01805802c0b400d46640c0000609505040500000441c0042c104480552001000c1d4807965200412550811941034400c02c0350014090600d00307025114882c0700c82c200e148104006c580e01c0d9001a1002c0340780c004004d407ca0310b843c00400100002c0012039400140048548008541c0d50f00384901d080110307000842c0f00d954501d0003050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 647360908 1250 647359658 647359703
    0xa020a0311030702370f06021e070b13030b1305010b01031401090917130503100b2103040503030f0405040e0604050a0303020d0b0409050133052803 65
    0x6024070000015482e001c110340c08104050004ca201a44000c00c05001d04030006411801078018000d41c1084003180b036842d061611602928452030003d0b004141d2440249110f4141072100200c42c440100001c83c5003c034070345541d5003c48149580015001d40c044001100100e449008904111040811204906140f4211501c144099042c90b00d484000d1038610300e00d100c00c0c0d045035161000040c544855060440018420380020300c109000000c4802d40c4890414030102690001d0702102c120312803180e550f0045582c108960b90380300d569000825582c400140040158900100c1503034200b41d81ca10200c0c1c5190010b051030004888040b80a002500f0a445403440500300000148441d051540752991940985800541056000902c0e03000c40b69044c1c0009680c00400760040085007210304029008000e010410401d071030040d2004008000004d82c4100d009400c0c02c10164107c2c600381c10040c802c01200a1000c95041c00d52460b620b241500c040c2c40300660240300001050b03c6402030301d20 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 647362158 1250 647360908 647360927
    0x1021201090203100e09100e160e010605071101030f0216060e07050f0108092857080304051512180f06091015050d02010c0312020a020a03 61
    0x1c95452040c01000300302d440a03900481111178540301c20a0725100c00450368200142190030065040c200905060444000200301c0c04042040c4031640c8040c0e04c0b40c100f0101c409080c802c00c800903205104120108144031644040e50105040c00141ca010009100c801da0708801984000345807014000414450721340a44481e0030302c1000903140300c1d403c0600080510705000041070403c000500060349258041258900200c00900c01820102d111405000400c1810070200e452007428511501c2040700b500d08401c2154546903a062452105d400001c601034101002405030124401000c500009400e010070140c90307624003a5584c4d5080034103012580b5580486100031050410401e0b0244145c02d480e682c0280c0541c5002d0990840c1c601d00318640940c041c2500c01c05c1c012441404038180002420510180b21300c40140320460280e0090344025480b40709541d0821410040714005601c51880c10050500c80e0400c0440b45004002c0142240c01c164a802c000d81d0240f544401490303000341800e03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 647363408 1250 647362158 647362169
    0x509010e0303040209040303021c060305030331060e0309090c04050f15031b070204051306181a0c07080f1201051f0c05011b03060f05090405031608041701021201 71
    0x840c82c0d8100340e400b05a138420010005801c0560105111140712152484030b404000880803d028494890500c180c803540141d40001035880c1d2212030031030040000a0107801d01c5005288058902155154400a0000e01c59101d00d02c0c00204414852076851450080c050316920202c41c0e111410031040c0000005543c0206120304016813485c0c510b440108101c07a41300f503170800f008140c4a1241c00550140c00b9504000b94040c0c184003c0001035482060a000258002c1d00c2c14401c13201e40c80b00004500300c08601c00f0704114a4540b614410005141000f60880c0324420349034030f40341e540c1d1a02481c2d9002100d540f9603100d000a0102c0320303100309040c04da0142030211400007030004040f4804d1504008014503509100c0300d65900003d000703084d03002c8140c1c00400d00a03041c4010045d035008000b00600c3c01040d0401d40286401314442c1400c0184070300c80c680c488021842c100291944c000102c1d10540201c1c2e941404000100b40312a00c007105c08054a0080000360b141c910200c1c10b6090080c050308403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 647364658 1250 647363408 647363413
    0x906041e062405090d060b01020a08180301061a0d0207020a05060418050615040303030e0c0603010f0f080604020603220203010f0e06150604060f050d060e0412020a0302070b030a0f0f0509010e 84
    0x1c4e41076446846000440740e1001300007601c0c03003010300142d0409800d140040c100b08008100f08190a4418034a41d5003588114002c0010580b501c4d49164584801100c03000004400c0c810f00181080c90f074002c5c13004a000801c0440c401b0f6072100010402e0340990080000004091400651401580246ca410071011507440d03a0201c02900b440c840d501451102808044c0c40d8008848451010301c03604194030303000b81c80c031135407903031a030800505074071b1700f0321030f000390300e1510140000d8906020400c00c1c013890f0300030310140c919107400d003020001562540803c0744ca6100f40c00a20700595092140070b20031032400307d01040d0b01c0b108150960070184c0081109040c5803e06021000a45c2c41c4000c407400d032031413401d00d800d01c1c00000c4801c880030300600d601c41d03003040c2c90301201107950f01980407050b2046104140310010010346000407a01c030b80202d100200944c1c4204010f1040004e910061035010310120341c0010300d030410060040c140c4091702e840c007644954a5090210700c0c003082c02a604080c504400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 647365908 1250 647364658 647364667
    0xa02071b060c06051f151107050f09090f0102070506070f111c05040504060806060f120c2205040c030308070908150402030304030b040c06030605040603020906041e062405 75
    0x801508440c2c000600801c46a921800108411119101c88003480a602040d5110b02e449080c08500605038040400100d074a814107903960290001c0c211050b01e502600304200f000920042c009400c00c05820b41c2214023942c1041940380c0c000744083d00e0740d68001c200600850911110161a80001d80501010000700200c001000714000480405012641e002206080c00c01c1c0f5007144c8901460304465403250800300006042c14002030400d00640c403c403010803085690030200a0b0302d0114007920480c5030004450303200149001c030f45014194071360640c03d15105d02c00c500c43d8000c403082154121034220441d00b040c010705078420300c3d240d844011400e000c22814140140c0607600d507110304070000e0b01802c03a00010f003192003e209807030043d81d21107500105800c0601d00600744c0801c50042e01300092501302e0002d510b1405000d060203d98001d40406c24546030803080c00050607c00c8101e8141b404c0c2600302e500e0841c482d116000c01094010140000e00c0c802c84240c07103800b031691200108200c800d10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 647367158 1250 647365908 647365919
    0x120a0b1804031704050f0d03020d0b060922021e0a09080111300f0906090a1e0204090c060201020a1107050f0603250801060f0c170702060906030a02071b 67
    0x3540003400e01243d0000d00040d0780d54a019464040082000c810600441d9400d041c0c054241e00500301c00903984038240701d42080c2d0300c2444070350b001c2ca03100664040360740030700c10302c5c480302a050400c1a4000c1d0040980b0301030a00c680a005209000811140c00c41c0014646089d01d41c45040e4001505200b4000d2043c09021350000e00310340911002c045031198800c9000d155580b40080c0c84014496600790b80c405480c01c80c800e100950302c100c03401a200d011307280005100d0040070801d521919408004110503d60700c000c03061805000c404100e0708140e03200c450401189210481600801c0b4584c0003695405107041c008040d9610b8644041283c1e000351b409002a903100e114440140e6400d545543d16903480080680c091050980c100711449444003026400644c8680490b041c2c030000c0d200c42c2c401070f1340280110344000c005a07001d4400510340a40c1c101101da004010b00881d4001044541044c401000042e9150b05c15203500c0c0d042c2e0780c000380e444100440741c60030b190200c8451810300c150a241c007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 647368408 1250 647367158 647367167
    0x5040812070c0c14010c02120105220c0311130e010b0406060302071109041e030c02011e0207060e0411030108070f120317071704120909020924120a0b180403 69
    0x601034034609131640b00000b40b140c0d21480250600617001030201d052041c0030f43c9424000c01c02910140d2010320034034032a041e6141d004400301e003444da206085619032807841e121030040e080324890481c1c0c488007903c0300d001103d07801d02901c6c02800003003000140321010300c0304000032164198403072003c2c980140100c00114007070b10703403403c0c007001e0a03078055050b9602c51034100211621070b90361024002d800722000c000d00d0350082c0041c501503c00c0e212065820350072008411000b05d032644010069004001c1802100e20601d035400c4000c01c06400814000c0a90114805d00d405c2600a00358035031003910200055040340d46064020825050261501c08140e20010440c4e240d034000c4d488020141e00105140c64898029102c10b8814000105a50300b46480c0484440300102010000510148400314000000384201c440104008080200c603903816071928541e007814034041c2140c1341080c82032410403ca0704035624420f001401002400129402c10488101c0320389041c400005900d10803c80041e03040f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 647369658 1250 647368408 647368433
    0x60406120b0f0a0b061206011803080c01180803040303091e0803092803052b02120c04081f09050102040b0301060201110403080d0f200a090503150c071505040812070c 73
    0x40d1b0280002596064010b0741c1000311840b840d072491542d080000103110171200a041e02e2005000240020800c2d41c200421081495a0290542004101180c0000e0185e03200c607800394440c075444102080b02040c0031844004043d025951803000200300300c41044c05000c074000c089150901000d00b10900c0110040c400c1c40300c600102401390001d14407041003400200c010440c03100d00d6003c0c005400350f06902010b5040f4454905070300161740003191355050030320180e130160b8206a0003008055001c030018000507600e81c5403020f44c070342e50703200510100e442800140301800c880180c01e680e075407420f08003c1c01c460b100100d031000a00c0601086c00022011800c0b24100302d11450081459041c904102e4000c20980b20751203101d078072501209030700462050243c00c8100b00e41e198520303c196500c0626441b0307480e4000000d0307030034411030001c0d0706004000041d121041c010f0740d4141005083c00140e0023244d02c140e4083d17403411008a100c00c10003407011416070388029646016100c40007980ea4440f0510b44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 647370908 1250 647369658 647369677
    0x10110705070e0c19050d0204151805030c060f090d0c05010810031e02012c0a050414130c030c08030712051204141005010e0105031c0c0b060406120b0f0a0b06 69
    0x842288540500e4803407170542c0c085030400d000455441740c2e40d0721000442040d954140000c103500901d059120120311488004a410207030103060401d2a52040012561011000a2501409111744003440e2070b880c07144601c00d0311600c81042c110303040c103002500c866402004070f10210b400710000e00000340d010014444c4888403000811103e1107030310040e180c2c0d0390b015014501c04030342c194514100c9100d48019000f101c5080c0c5042c100c154881c424070040e1000078100501c007161440200d480e1342ea13500d914080c2c03540200c64072050517850b55030f085807903a5240c0c0410801d40c40031540b40140451400b5448032841d1508002e86001001a10792915520003407028004211418a0b02e50b940c0d020310401c0b1070301c4400441048151b8481540012041d001e004032402803103601d00c003940e0300540a407002c442009a4543d000c9000c40ca40d123095a92800070820f0340c0043d200e00d40066161401500d002c0a00d2050014403072924041e00c1c003080781107009100d0f55010f8207190b000901c3c6d45a0000b200d04c0b810 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 647372158 1250 647370908 647370937
    0xe090f100c0e1306051c0201080103020f0609060f040603050705040602300d0501080c15270901060e0f040c090603091b0807080615150c10110705070e0c 67
    0x4201c0d01080c0c03000d02d50780540c036030442c420360181d071001e889070b5001c40161407044550500c00c03c6400f0340f068000801100090100c3c441c00300504c0940380c0000d000411000040c01c861900003a1008100d01741c100d0015001e1807980424148807160300f5016242d07011000d4030308642031030702c0d00700000c3d80e4840280c41050b20086d211110344240e007180c0f190720b64020180b482c9556442d070705040e00c4002c10091190300d102d40a48070074910305c6d1500c070f40705a40754860402114180400880d07501e6500c001c1c2c03640703000e80c0d41102c0843c00300350b1205440c1900038005a241c140b56200c05d5010320884221080c0240d00c100d1034405039110782c0b0703008240e403001d8a90701c3c50000381c02011403030070a5105804e101012071840403885c00080135240092a00141c1d10100140c6a0b25128240e003000800009030030309a0010125454054109142c0c0107019020021811111444003140070001128018403131465001c400082c520107102e000c000300d030000c01c884904000c4a240c02540d640c02806829140040030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 647373408 1250 647372158 647372171
    0x50d0c09050a09050304080d0e03073006050a05040b0604150b090112060e180625020a06060303050d060b0405150a17010e0103230709020307090f0e010e090f10 70
    0xc40c0583c0b0071072880b81e1001c11695070f140c55151132035842035a48100000911010322401c064100442c4030400c81c0c40800da010580b8801400380c01281d200346d0480043c100b841104e1201003112030003418000d2000002c001400d00b0300e41440303244210020007142c001e90609000c5614420180001e6080b190380149094665003c040102d0340800050a00d00b46e42e07080020101da0109002e0b05180a0785440e600000700a1011801c0b54513414111440018529194420403004813200524024803040d0720642d280c2d5086961a03034110399880d0004d500091021618041c00c601c644a00030190411280083c00c103850700b800650f1024083c0349039102e07403401040c0340410741e0041520a40700100c540b40d80c4003079030311201601c034100c00c2480143c80d00301c05056040201000e10707100c0c484021980002c1c2944a0411400d140a50f10152104007041540e03000080d42e40d0380f90b850300010700b882ca003048079154981000303c0344004003c1d01440366900030148501040b00c0005401c4e910829184010550 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 647374658 1250 647373408 647373421
    0x3051503100c11070b0307020610080a03141902010c030b0a210203011e020c060a062909030a03021b2707020c0409050c03010509060903041e03060216060501050d0c0905 74
    0x140340f00c3c800074903d140319044000c41c1c1c400702d10020398400c401c194221041c55580c8480c0e683c0b1300c5058031500c5410b82003c540080801d202d0b50100c03030301e100d948180c1840c012407003030024076000c0d907448800c2c01030355160b02c243c03110380e071502881da4104000c03243d290005050811902588079200040c024a290300d400d90811900c0c2900b05592070f0300209050600048101000030280d4481d210b010b409000301400100464501d01c03581c1300f074a082c010202d4031054640d910305445040c40400340c01c0102d0034040300b00795942c03c01c0103182251081d40079001046440b403006207407219465110b44130f000550380084010440c401410382c2e009604c4414095522050f0080e400c200c2c902c000143c210341030051400501c000051980d1040030309900800c5240d43c0c0395482900c903c0203682d4030321281c00822081000c01c1c0070b24092402c03594104461684c4503901d98030f4104aa00c440c0354450b00e40c102c55080b00c148903007841840c3c01488240c4001e500c0e10029914440e9003c002d0044080150f03403074010801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 647375908 1250 647374658 647374667
    0x2012d03021c0e0a0303110a0e010c020a03050f07030201081608071b0606090e0606031506010c031407051c020609030d05040f0b1009060902090a0611150a0c03051503100c 75
    0x1010348401d02004034028403101e0f00d4a40c589501d054001c6410404009800300490040300c002e5511591404100010800115165881d81c0b0040e644801600c0001c400302c0c10600011000e20a1030b001811121b180d44009400150020181c01c0141443c19a811240d07401065107540110b040c5011151502caa80b0301d09480302001801400d0340d45403030740110300d2408543c80b003803114200c10200c4070306641d03807402c1695626041c41d1805060301204081080355004101184c0054070a0a00e9002c10808000b82c24881c1c00c4440165030342d0f840401c0202d200700724040091001d14091018000a02d0014070706952849080f46902245507140005028015640000187e147d40300000001900b00640c030009c0c07003000d5009e1103280c24901800010031102030b03c2140c0021901030111f0001e6490204243d0780401c05201c0070605010305c1c5035607192220917250541c450281c0e4000080c0800c4654401021260b00800000b103162850351103000a81e00090b5807100c0d4604c256000ca10380c0e012040465 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 647377158 1250 647375908 647375947
    0x9090a1e08030f060f3102040e090a110306091203070917011506030c1707030b13020a031401030317060a05030f0a020f060304080315062502012d0302 66
    0x41c00c003880032040c4071125007081c920034001c48080707410801d80c403d0030080000002c140b5500e985030300c1d203e04140032030414080c030b80304028031018001402c00e5501c00b01200329203000c480030701c101d801241c04041001100c13240c0500d0900254014211451b00440d41541c0e9114504540c160a40100014002c64400c40f0828080d00312048403440d0f040382440014044d0240030710501c0d541449246c0458102c0c4244203042d0300c03082c02c1d9111040000d201c0c100200b0802c006c0c5c010300030103889400041c1c050f00d544081340e0281c0b8a4440c0180e58102a0100404407407510401425030030319a0010000300313078821442c0040480600310801c132502c5000002d00007843c90760101ea05402084d0103845003074000310300849068001c2e24803d0040c40c207501001503034130003140c2c0244a00e00c07d00c0401c8460408018218415401074160f0b460320104a200b04035008440850300c9a00212500c01402c55a0080d552408405a540309070040c045c0141141100c01038103040380704041e804240301c201d0340491207805 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 647378408 1250 647377158 647377163
    0x140103080c0328080f15040f0209180f0901180201120b09010b18060a020a03080c070c0f050f03010c0f0c02060d0f2013090207020105090316080c09090a1e 68
    0xc030a07120b503140c2c00c400300140d03905818041005003000585164070911428804c4040001c0044400c00f91000c20009002c0400d00c00b03d030310341c00c1c02414101e82f0b800000e6060305007a184c0c2c002c860300d40034840070100400145a010664101469000000c5d81e60340750542841e07090070b1544041d460301c074007200200f1100c4401580450100000a10b124000d0000d000b40c440c14028052920640802d00c8501e00c00e5102440050f402040500d000c0392041c2103150b0480d0715940103a251400544a59051009540002c4221a0340b528200315601d81501303e4520048141d000b032096041c039460281070444084d10803820b0280c401014011980d0b0342e402c4808400d1501800c0218040d0760300c001300180003c5d221040304112560760301484c40101c405491030b08904100903480d260414040001941080340128103120060003440303501c0d0381c248050420702210001040da0240b4000310546484108107034a4011181041804645840842c91807180da070081540000b0405424644204c82e9565401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 647379658 1250 647378408 647378437
    0xe1903020603391c061d09191104050a0504030c0602090301020705060a09021504030507140f0303270a030f0605130b0a0c260a0f15080718140103080c03 67
    0x14462420080c0016040341c0403a50085004000d0801070b071320407039100d402202030800c070010341094403403106030081341c1c4184043d003601e11030368403c414400a40d003000c41c1101c20000e05207501c81142401d1090a51129403500103210509154502a0a294607040d001c2c2c00d007500010701c04001c0d10309404840d8016030210444400f49020a000e00007800010400c0744100543c3c0385a0007044603040c1920160ba8000f00a40155450081000031044001442c2d070380002100040c0c407055034007030000e013110000740700702c007030301001c0099202c010b2601c0e450b01c140c860b1032846028004514a41009036180b54400c03000516a100c0200ba17081884022400034075440c802c0e010040c4c0302155412103001000380783c43d4010f460600300483c07a1a0926031440004400f0071200181d48900d96801c000791a545070307400058900301d41c902c0402ca0030300d0b50b0005400e56101c048100944002d100c0190b200d66048441040b02d12240d08038084101c906200c050074408001c50400003040c410300807a180c0c8003000a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 647380908 1250 647379658 647379751
    0x9050d2607120815040b120a11040f020406080f2203110601170a02090c1204120905040504120e0f15090a05060406021221100504140601091806030606060e1903020603 73
    0xd060800c401d909427454003031410119420404861030003a1800d480880e141c0f0303880c0c1c0c1d43d46841c040322840000c0000e0081004600344541c0c10515030454002c04d8040e59484020182c030070740031854800187d0200c0101d0b040b083c070744d0f003038240041101100c4a41c104c500d204951070b92030403d078a44c0640d40e1444071650b40d5400784020020240e091a04508482e2541a69542d4441c04c01003100e6007100c01802d040c40030b60074040b4841c0300e0350440c1d10f00fa4008040e4220b0808400c0480c1045000c0c616056901c3c900140104036403510418a100400301207690318902030a0690013034489001d21011001408041401209c0300d141c024040e0303550742c0745038441000703140c03215000c030446109204060050786403005a8111420520000d403080307006841d5401410326005030740c40c5190000c07045800050380e904000c00050329074000cac403000300400d40c0c0b1107010802c24801c0081c2c0f2003c481d081c50341d22840d050700b08010b89030b400940c0e50003070b250344050451030031499201c0031840300380042c400e40158804 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 647382158 1250 647380908 647380913
    0x13050901080a0210020111030412110f01051803090a03061e020703030501060813020312091809010c11030c1903050702060705100e070609050d2607120815040b120a 72
    0x18504400074021070b080e030349424130410141c0c01c030303601209200b1406500f000001c000c5444102081c02c5601c0900d0111407642009071007a060101c512142c2034540d44503428450020000c1130303851100300720a806140340c400c0990000c1c0500800744401055030b5101c40030210005140c401e080c1e424242d01c502550307211000c0ca0002d004082c24092000800c0c03100010038901c0d0110b07a0740c121569800390050600025400e001006038000030440342d480400c0a510018191266800c1c6005500f460008a400030f0b40032400351044044082344120b40c1e03c20300c07c0398051580002c000202e1420b84240c0310100545050449071403091500280d04000002030381402c2200c0020300c003805903c0e0320307410080d02d036088a80503214a0b4521400d400100400020b000a1621007659045203210f955000d928480050312684c120603030709009289400b000c5403510034841010b408003101c0b00b003494200443c0c90302041e1300c1001d010f410301c00790246584041c03490198842e4120035151032280b1013151103080092 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 647383408 1250 647382158 647382163
    0xa0305100c0801150e13060528140901091e05180105060f010c0b060609030a210302031312170a0207050106080105040c17010609110c0d0806090c1305090108 69
    0x810156000800040c00010b112103580030507031204c0b42550380d0b8010b070707000001000000d030b503048030040f1030ba070b507807000080c13140e0300c41501041109070a41d40e200c41d2440954406048040c1e68000e2203540b205907003400c1190341e1403202c6030644408980014504120203241d0301221158800500d442e450401403010100c0e07082d45035921201090024402e176518401441810020060550702042040c2103c00004200c401c40b213a01caa00944142d06000303400d40000d00c0c1c100ba50f50701303940b014407803a010b8090404d8213110340024060745c2800c0d0715600f08554414034400902002605050054490f00a018482c80300e180b0341d0050904caa103490b0822030a130b40029400480201c038107602c1d01c0000500000103003e101c1c80b5580048406080900d052000d520150580350400301c50b55840c5004603890384d5610414140e005090f44082d03c403103100b0750341c600e04240300341c88205200d0000c0402c505641c2e10503030b6aa1042c241550940c4500c400d450b408000344094210a5000f41a200007040380ca800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 647384658 1250 647383408 647383421
    0x209070207080331081c05091011060c03100303111606030b030f07080601090e1f060e06240d090c030510050705040b03060d020109050301020d15080c1e0a030510 71
    0x250b0303142d00b131a440c440e21990312044041c440c03100d4540059482d101c00d0030b103100381544000e40605000d0315000b40840060a07000c0c400701c2d0300d801f080f12903900e54074030342040040c541d2020110b00c2c0d035480c608001c199045c001b651444010208501c040280924000034000c10520b1b10203041071541c074607102c0801030050b2250b40041c038001d2241c012400b040040c0003d0750022103452070017804d5240d0074240700d0b002803e001c00f180c001c0c2e8410041500c0703c030101501802c03070782c1031074003000516603090244144030b00c000508590b114100b07014982e81e400e520400c0d402c00c0340390603500e03003562004070112003405045008800b404812508000009018010a10344a41900d03620100240d03039610354190b40b1401140100025404248005001818280c47c0d404585005040401351503950768002401ea0b8424071100f00d20540b82d10010940c5401c4410742c40c00340080781d0182c41d00c0c480410100c0c803030382030304000c10304928524010708034503850350614503000c0d542100603150702043c404072180c0076000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 647385908 1250 647384658 647384707
    0x910030b0d0f0224070b09030f03011710110d051f24080702070b0309100f150603020c0d0c060b1002060403020c0108070f0804150507111002090108010302090702070803 74
    0x5008030018840425000d290304444c4486011810080503840b82020280700502800003480100510000c219551002d03600801008511044140007c2821030501c5108494000414203000036403078801e0f5003400b507540c00d80b800c6000054903600ca4009558042444104030484020319001040d1000f14400d0018940c400c005c1500c6000c09507441250380070382c1220003100607046400184038503c4001c00071600305481408561542c82c903a90f00302c0c11521480d02000441382d407054800c410b0017118190700010030301c5090440c00c0180484110f03840e103020400e41c808001440d03021200b0411140d01c018181306001e0408100401e0203c00650360301c0080e00c0580261150800c16505507210300c1e4100d22552072551200c1c0307203044012080d500359201038800c840f400920340c030200c07031200079200351442548140e9400740c1484008201a08044070f0b85840700302240108003007100c0380d800c04825030440e80c4c140d612611907582d020007241040300c950030190f424000060304041c20303458580e403400d0b8400d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 647387158 1250 647385908 647385919
    0x312030c0221030403110c090109140f04032102070c0e01050a0e09030d33050406090e0a1707050313050f040b090402010f0311120703060605040b0910030b0d0f02 71
    0x182c200c00c007030307002d19500b45500100c1d41c0810008001901c074200c4103069400b100115050403c82c200051040c0e14260440814140e541c40c0d20a0504441c032240c0703401a1a105807201c03c2e09041d00c00504540881d141d07102052421901a40d0b062041d60484800303640050502c240140c072450400c185070028420248030b8140e035640410125a88110a801001500c0003140b03800c02e03007203480c40541034031380f8001c80600100c500381100a10b203205c40700074072886809400c0003d0804c0c3c1000115020742d04001c1c0c6862600200000b40300700060500403068000c001e0342441244c00e00aa0214455184010710501000c034112104800000401043c0c0e0000c444504011080000303102c01c841c00e40e090154001004000b04015500803d40360f9000d80141c9800309a802c036203c0c41d60301c6d59010910b842000c51481e01000000b036810b00c558005445a49407480c50070346409140003503400350424451003400104003a04100713000790b1000c005407002901a1880201da424400c0854464502c01c3e0f0164 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 647388408 1250 647387158 647387173
    0x40b030a0f0b092824020d14160813020a180204050f01050c06040204090623090106060c02060307030f060e0a0b191a030603100905060a0b0604030b040b100312030c02 73
    0xf84840c12405007072403890321300e83c0a00c010752074411180156031300c3c0582041c00204102032410690009040c0b100e0080b0300170400c0344800d00000c210004c024500046a2186043c0000d41d07903100341e066403c0012410038200040280c0001080c40c817a42c0c0c44449030859038442030561307080c250007400803207404541e00c24414a841006480a1041c07a503a01c0d1a138116000080051409601c00300f141d038002c2000186d003c01c8003544103070845500202d03525007000c12007000f1031007409005400240c4001d01e080c6080000d2940881c11b180000380c507060078143c860542d040321800c0c0e544800c00820500d201060541088100100103295170b402e6140038cc80d03520800d034070441803540148115105060399a15441e001c40d1901410341004c1c08095150092041c0070660610034003338070f0882802580541940d0034012803500071500e80200c40c030701909003800104081204400c840303500c690440c5102d0250b5a81d16100d8880400c0d03900014080849448400c1e04603a240c0d100070791a01c0309800710b4400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 647389658 1250 647388408 647388433
    0x7021506030105041e0c0b0f040317131205160b070303230705090d0f1a01151d01181e05040207080d0902010912150b0f0d02040b030a0f0b09 62
    0xb0f0315400c4501915040c61085c551098801507816011441c2c01906c042d4035050b2180d42041940c0e0100e80350420001c808141401400003400225021585183c14140b82007843c1c092809680396600c1060700c00710890700b4403021311406100d6200c00480c2456003000c0c150300c91062010903001144141d0001e8640b140e20380b050140b00081401015080f81b001d0b61503a0340003002c41e050b03032100c111603070003083e1080600000b41c441181d10201c03a21414140b80300111917001c0380c0381124141d0144541010020101d81d059402040456140d40b071510204031405408006848034000c2540030300e8407031490303500000c070034101d207030311224405d803070606940e0999440701008143d001b80c08029015400811444103442d40d80c0e400b80c20300500c10304010102c44c1e0b440c1400402106c052200355010071820b148407400136114801d600c2c903004100c60821201c2e2141000c6441c4410919000f130060355103180844065a040024603042d41e40480d420b0782c07500c814540000d2030981903410900c02e12940900054 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 647390908 1250 647389658 647389661
    0x50703090c050f13060801050601180617180f060a05061905101707260c0d150b1c0506030a03020a200d0503091e0a14040f0203070215060301 62
    0xa4541c1c1018418000d103040500f00401201c0440710310341e0100e9054034018000d5404d019440040256500004076480c1403070024013041301000b0301c1401003507070103018800c03190410180c051440c140c1c2401d082d00c3d44c81c184002c00c4882ca18501e68018420189426100d00c000175000f841044111014403080d2590424000e12000054281402c0404040f050216041080c898102c06280f80350509210580e0304403012a51419500040000d10840400c44441e00310078a4103d00301001d400c45031107140805001c1203a00411000041c182d858070552a1031030740340000d02c1d0142c507403c040aa40c80c4146030001001811510544011900b0400000e12500d4049064132240390141c01030008940955500341d54251401142040e0740c0c00c005162840d5100c0114900540d0302c508000d56803440c3c1542004603403e40340c2d1321241c8041c240c01d505400307500c600340c2c030008581c180502e00c1814007103080060041c1c1680b83e040204144040200400264006000d100c44a8404c4a55045850b070070240350 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 647392158 1250 647390908 647390921
    0x30a1a01090b0708090406030b010303080912040b070c09062706120b1021060b0a03020a181409060f0c34050a05010c0f17010b0f04030c1206050703 65
    0x9010819a803000c000b140c020308001c0500300c3c03255801c1407400d01607400180440d6030326007080c1c823901403220041c000c15421110303076604518640c004000b1720f410041540410f00c03590158003110900400c184d400c200000c0400c1024110115041c440203403600c140c184014144142c00c03160741c0d0f18080702004100ca504c60081039640300140c12250720720b5a21910210340c00a000348ca200200740a000401c184a0b2050514690f0201c85010710b00606090a4003070300d400035207080c41020180c004200507a03501240b40e0803103c5003050b1420303516071030341340b00300400301c15100c00c1000340030070108445800046649407041160398129555a141c01d480240b0078082c50203200701050010700032030610b04161500017960400012100c3d155182c65a805084c8011031900b107500303a469101c08400e0341d401a4059800c65401d10f480164a0b800c00010810400180f180342180d0000003840c08403042c082e02100c0c0030b1034100d240b5411080d55089044c3c41c0003c0c007c800d4805c40e01d4034000c80c5103e4468020013 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 647393408 1250 647392158 647392211
    0x1006060503090a0602130b0406020607030f05070801050111010e0604050304081501031a1012050c1509030709051b0403030807031a0d03080702010219180806010308040b131208030a 79
    0x40580100304da90b181e00070360003045124000e20721540000795a0f100e038030092015240c99030140c5624240701c107001d8143c60324540c0296100703041c8010804090f900140c0c0604485007460b05010410789840c00b0750040414011050841c000e4008110600c02e0002c01001102c42d81403c869008007913100e101c4520400780002412a1010a00c502c4a12030004a0705d420500005074a61550344e544003d00c1002d041e5074040743e50750010f900991152521003d80e1a9a03410000450f1602401074000b0307480d0301e03090044150441d07480300842c002c013100c0d03503889005400d0742002c103580d41e8503410050450481114103000080c1172074009401c22141c40c0d041d80d03440c840688002d09080030340d507080d6680507000f0880b01c110b641c280140c100c4580c048284d0803450210b9110b0300b0b08070311440580880c20358960007002503030344040010000510403030300b210200d584485481c0d440d06891120510400e00a03840800884a4520f49034103000e081d0000314000c8000c15420031060780c405000240350000c03546403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 647394658 1250 647393408 647393413
    0x3070b16050d0e010b0a030326130813051203040806071b35130e07084203010c181806050a030b0402030d05030402030c0d060e010e100606050309 64
    0xc010350b03207294010702c400442820001c28041202d0021440e11a15988280c00041507441b04081001c400c6011500f0500c44e00c00300d07461440c0040c8076a001d6003071364030b0051500d000001c120042000410014014060090614000100300450150340384c10900440b00c1500508010030040e6020355081c00203000300d4086220741e0716480d200e8945450740259a40f070021502e851602c06107501382c543d80859210050815260700f844402d00507100b070f1039040600d010b205881030000d00b0350010300da20740c410700808030700000040800407540041c81001c45004400c3c2109820240a9a5407681070b205800c2600204040d0540204c200c0c1d510081005d40b9034102440001481940d4050494a00b600b840c00404900682d940b80071401d101d20766807003030302c0381c0300309030207020443c601481006000815440c1550a41c203040d00040d840305908140c6922585103041400708100070f0342c11050207006110000c00c003800c00b01000a45485481056a00361803900350041803c5001702d041d82c1c05000100b00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 647395908 1250 647394658 647394667
    0x1807080f04021c031b03030e0f0307020904061d03031509150109090b0f0a030b0601030c2d0c0b090a0311070602250506030411090c04140f040f09030203070b1605 71
    0x3031024145044035825801c100d01c44002e110074001c82005c08400620990380015440303031200d0b445050800513001340c0103903001000800c02582d01c0005268200d074000300001003040701001c1140700c21045a007950310300e00002c4108844000c0005620700d1b28030f02920015201d5555020030042c554015045e05d0100311020002d01c01c5c04410303400f070581c1c09006442609800d868500055100700300e680200d03010611030080240d10359250044241610481c10105002c03800300c2c525120502c52134247d54101c8901c58000310321365215540108200d40c01c00c0441d09a820308a03584c0c0c0e102d80c3c0041b019408241c4504241000c00d100140c00b004407110742e0302034070b081c1003240c0d0051680d0000c4c4002000e200a801c0c0089070b0740d81c03600002e602491040d042c6d07800c40345951041c0a0f0440f801880541c401c10140310400c4102d0003011004070450013142c0917445102d2520000d0014a00118041c140c20700d0940752004051f0000020104107020f007102e550311360f0b40d4810308440c1030745400c22240007400620 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 647397158 1250 647395908 647395939
    0xc05100f0309051f09061109130908040b0f0a02070803090616021f0503071107030f0f1406070e090f0601020d05030903041d0a0b04050606090d050106051807080f0402 73
    0x510545800344683c058079016060400a240c0008901d032409642d070380e840d000389003084440d101348501a4035003580c2d1400e08642c03100180205417030704c403840e000b00c0d2104641410800c18104690140c1011a04542c0300c100a80c00000140c1040c03050f00054400e048001c03034840000015520142c42c000d10130b9180203c048045155900d0000b01260050340182c1900d081c0300fa01e0440620a07002985d5042d02c030310703288800030420b80c3c41c4030700140c0d960401c91050011580820a540c01c0641080086020900b18a4444500141c46040440038000c803000d0001c0390703500200c01518084104c03140c108076125000803101004066032a01d0240c4e011002e0000c92a000311b019550040152098a05151360b540240307405d40380d00e5074030414070701e0b200d03080000180c102e10a00b04142000d546c01c00552510f0008078010f8407a42d405544140c9098030680c1c100b02007500900b004d03000240c0030142401e01d040710f00c00541000d40d10300e0701080741c100c00175101440280d40c461145400508045408500c1d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 647398408 1250 647397158 647397161
    0x406051e01051908160e030d03020a050d1406180108030702150f070606440f010f090b0f040b06040504022e0f020705091906030b010605070c05100f03 66
    0x21040905000c82403001c503283d9403620030031110f20041e035242c02c211842c1258028104000d214000d0b0284030502480e03050700c4e14000b40c6050786030b42078140182e90b0303441e0040903a000c1c0548d03404202d1444c18101e51045400e4000c441e5400b400f003c8d102c400100c00c0c1e14a4004018200b40208011640140f0000c4003610f4a018245964007080b00c10703d1030100c428800341c0303030751b4800082990850f407254401c1010640400c20134421000302034807802402e0041110880c0000001c0d1082040c1c252900c050800301c500b4090801046c51400003000106484d40c0c03580003134640d40b07505032015589000014002c1c02554030ba03901c40d95120422448980c1c81401704401401d024109903003056014540c0200504030442005c003408031016480c00b041e0040000901480c0400442421500104801c00058407001011500004480d01c613226001c1050b030010003c1502c1e92014203840b2400c0000a5005d4001d0000d00001e0f0044c9030413030a0fa41ca032010f015069040312130360780009044007020b0350380c41d200307 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 647399658 1250 647398408 647398459
    0x507031205180910034e080601200f01060506070b0115030902100509130b0d0b0a02250303060501090609140d0b070201023129030c1206040605 63
    0x74815489513480e22611517a0a82607180007010b401341c1010040f0301e81d842802c00c01c0c140001c18000b60076002245d82c44800ca420030703a42c0c00c1c506002c1c1c120003041c080e0b8003840240781c000030030b00c1245410300101c0078816569000740e0360f042810b519100011481d070a040046641040d0028902c09a40e4070300040c00035018078118904041542ea91844001070f41d84118403c0ba28810b580c0e40c5850700194010801f0782da0003016200003007480c00030a9819a03c07001c0c145207100703030490554038050b5243c1c2c0041d0040d11071851540c0d072443d0180412007060306400b03075410905000e80c0c0e0800656450f0801556407161a0140c1d00202e042440b0804c562450408075000c00301001d09a000030801c5942d03001c00d0031005513160000750f500031808540c41140400c3e5420381e40c00b80c14100303080e090303403001b2200c04100900480285d180107070480c1c0724804958405240c01800c0381403455a0380303000b031141280c90308944403041442d001c07000840d1851505004e403100b9940001c018140500c0c4104046219003a03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 647400908 1250 647399658 647399671
    0x7170a02181228060c05090117060906040905030c03070b332101061814060d030c02010512041b09021201090e21040e0c0a081f050d05070312051809 65
    0x20070f5010303c00150a03000e48000c182c8a51111a1a0040711001420701004041c0a240c0722407410200200d0355038551019400210580d00000c01c07070340c0e60520900b144210750701c04007075110000d10401000328100072079101d656049062094800d1003d030070915064000310b90043d03140350600c41c032030501d00000240c175440808076880702c1403244149000c0c292071155020030185a1450072007112aa810f0280e480b09002c22200407619181400024081d0110000c0240c104404800d02e101103901500448100c801c000c01c0791102d03440e15107402e8402030700c00d59101c0610400090700143c250b0362402503d055100c4002c01d80e0031a0308040e2240020449243c60032200d00c1105c1d151800902481d0003101540060607485075100e00780350300c101d90380502400ca410314500410851014075880131105070401444070300310484c0c1e42c070204151561003040d0450341d80100d14061620403c00e00041d02802c0380d02c1454804242d1070320344020780e040d000340040501942d0f400031102965103403075485d1030350014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 647402158 1250 647400908 647400973
    0x140d12030510090c09060e040c170a1e050402030d0f0c020f01030617101505180a0207122f03040608090709050103050f120405060d0507170a021812 65
    0xf0342c0d504076802600e51090064010030405071080c86030a0b40300100c03982400c010307541442242e8402ca0010140c3c0341c0340c4000320381c041502001c81e500442941208500c42e44003505000000c0c0c103002003000601098408a10902c0703800010b200890250440c01d001e15090380740d8000c4412141c003804180922008550b04055442d4004520b000d5405000c011000d841390040002c5455504564116407440303014140300004c510f020032131640d80903000205204010b4611001c0e480d481c4440010b8050007100070084030303100103103401656201001c036407c0c50011045562608900303090340c00070106588030784030941042000340038442c000c0003400c0e00955590121120f0703581c3c52070350b90101d94086e08100c0b1150000c2001c5070550000300070034034036000c000c0904c03031819113401c000034400d11652150200ca80d4450000504280c051410b90815061120b01c0206a14040103131100035400011400380d0fa48140860b04a103042240c003001e02802d8420090508112501d9624a40c8128907034450390341 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 647403408 1250 647402158 647402191
    0x180c021c020109050613080a11030c060408070218010803090f030f0610031406060906040b030a0c090518010203040f0209041b080a03030501062c0609150301140d120305 74
    0xd80359510020080a01640001200720051619900301740c000742c240811900000c0351503000c92281c204440d85020a800c00240070021407083c0d50450045405118079405548108802d00c000c400003482e00074404c6038101c0190000c0414410404030130b028041140e0b0080c010541a418151540c4c101c418004003250380301c240c000b00b031604d00b100c101c1d00310a4442c40300170200100418040054048003500d07001d85920300d4502c3c0800c86104005203942e10031070710707105203103125201440341c10711040d0860a0140480e4403101044080e0000343c8134041c0c40116041c00d03042c8060107100f6240507641c08a000d1003c00000d40800900d0140030308203851690002c8020140030000b01528801021340c2d80191200706107a09000d01180e41c1603000d17000384880311603404210004c024201c402000030407580c411203044407002c06d8003802400c0340031f90004c1c43c1050960a0404400196048032501401d24040d05c0c041018441c0d0003040c018014120442445200040c0717010b50010b030350166a030382003407640 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 647404658 1250 647403408 647403433
    0x12030a020412050d140406140310080d0908070902070b040b040813080606040b0901050f0d110604080304030b01050607150504030c2103051b07110406050d15060609180c02 75
    0x1c0010768003c40e441c4c2e0084040c00035241e0094180d03054002c0b5041c90508003480c00a0213041c10f04040d4040491120010018809103000c01c41e1002a00b5080c0803034070042184c02001d81070105900802c1100d10600900084a0300d46000300d611160748804501000d403202e5aa04030799010241c02200e040f2014070030b4a901d03c440003888001007800d980103240509048051104440075680c0c40c2d805110040f0060102d9200c00084c0706401809440c4241c22140506040112109050f00d569100c03000290014040700d00101078019240610098542c5980c2c800401c10705121303609000300103289060207a40c0309441a8000e80d0702034002d0615800840166803090000c0c5201d0720554050001c07108c0819074103605105c1d1560111b0f10300c1007101c1c0c001d074101d0062030368012900300070090121070741400b0300c54407682c0020b4021b11000d480000241103d14046600440c0c042072141154903040c0001070b81c0d44121817202c11500400740803070b5030101142540c405044240040c20543c0700b500c60000c00d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 647405908 1250 647404658 647404679
    0x1c0930051b012c0a02210a1e060e0d022125050d0207230102010902090403021c081009181a070f030b0a1203260a0b04020a0212030a0204 60
    0x83d410360314002611048515503041503400200ea542280e02d82c4044910030042c1c55411022040040742e007a40c05045400000315441c0c540c4000d00144220003403000d01e10414034000400c501c1910403001841a84ad1015070595030f1003542c84070b0401a40002c0c64030607841c0e203450154844843d444031261810388098100142c014101000c8211001e68580c01400c0c81020321840c2510f9490b0310241c902c0628240c1c000c60b02c03015007104210401108110301d013003a03000754400004654040c100ea0054502803d01a40714448001c00c404400c0f18680f505450741e1140400c144030304400451060100c0c2400e030032400401070340c40e1111b010000c0c0049080452417400490b4850491100c884546150050000301140b1203810b420003403604003805425203658280d100819922034100c0c040724004a424101c41c41c0011600618005030842c80b0380408407040c2c54214841d0007150010701c00107031000c06200491092011440058105491600300110b11800840d00320040c00390150410342c95240201c2c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 647407158 1250 647405908 647405921
    0x60a0f0b090114030f0c130503060112021017040f060e010515010905030111090910231005030402031b03010b060c010504050115051c0501021c0930051b01 68
    0x421401010070005041d683c0014400380ea0b60203003004600398201340d6164160844068082c08a018000c42da02c12001d40004030200100740040441d0484c4d6585e075641c03845e03410a004c0c20790080303443d4102520510b000320260f8680c92107903c4110b0b9907650f5a19200d01010b0020070440309076868984041c1005002d00810740100251450040003400200000d4481078007540105c0c080d904101745148510110300544002c0e10041c1c031031910554600144060010580c2c0104100c0d29030100c1110000e503041840110003601555000001c8289000544080c001203400070750503445500e0059401e661950507076801c100160001c5040d22400300014925003202e443c03211142c0d990410481840400d000302c445100314041c045500c11704240204051421170034511107540b048071011410820250b040b0340c4011003205624201720f01c001d8022000c0e265101c41501c80c4045c84a0000e44c0083d01d0242e480e01211401c020182c50103071400a59840d040b440340c070102c40b07207056800f143c010002e00520 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 647408408 1250 647407158 647407169
    0x21906080a062709020a08010212180102030c0a110c06040602030a140c030703141303080301030311011406040c1403160210090305180d050d020102030a0b030109020a030308060a0f 79
    0x4182601d007107091101101c5040e448903401140c0c0314509010020751241c08000c886640700045084002c900106000a150740e209405d00d610000b0350342c0201052000003406050b41140c60340d0104031101505081c0d00055550507450442003000780c1d8410b004a00002d62014448107844038400e142d00010611f410a074821400340c1c000041080340d00e980032441549a014501859080c0030403803030020b80d01d0198070401401d000300350720961406651602034640000c150401e188134140c582c0307002a5103070028403045006c11406801c881008406020300c42e40c000c802c4d04030510b0342e42d640c41000041d19080041e0070074003001018554003440b0f000001d41c4103c21040d100c880c170b129034800003480c00c1460042241c841e481c20a03a000001c2d8040200c8034401003140110703000060500020b4501c00d1441002805840364101804403a034040d00590702c01c00509a0410690140d4818503007070b6100300d58020740c402c00e10f0200380300090146014941041e005014400310944810101100a429030400c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 647409658 1250 647408408 647408417
    0x10905011a121b06030c0c0f03040608090613061505090f250203040b030a0e0114060901060905180702010e0a031106070306061d030c0d03090906080105060307030f021906 75
    0x2100303054202004400003500400c0300814405410029842daa055225031040c0f0404001010500051051b802c0c2da1003501908241c900181e40d0306450f581c0e0703070311501c0b40c40d0124900c2e500068404202080d410b114486a4040d586000c20f035503160401000d400301d064401e003c03404004901340c0c482040702d508c6240c0000d0402c0440c00c002c045a1082c00c00034003203401c26400c944280f032409170302000b540c0c101c803500303801c40e91a034031030206002c06449052041891586080c000101070400741201c540141810798522480d41d8840504403130701c0341607001d0039421451011900381501280607100342d02c0300d40340c400042c04400001d00d49040c000c2d80401940055840a0741800002c1e050204039081042030804001d150b20381074020380789044220440d2107002d03051400070081e440030700c401c003500b04008100e10004440da00c0c0180400390340e0300030104520314110020032071050520415000348402030013805150b05c0c0d40d441c00c000d551150012030f0002c600c0403038071000708680301d02c50700503001e10b40300c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 647410908 1250 647409658 647409701
    0x1e090c08030f1c05011508090a081903060e090304031b03020d0f030914090a1e05071206050a05060f030a020f07080d181e05150709031713061101090501 67
    0x203d41c18060038400404805518240041000f8030601d034041d0421400e40c100322203150f89180d022818424032400290800380d0000314040348855000700b21070b42e0541c5850801000e0f443e80000840039808655414490380200018030108045820b210100c104282040d17000a03188c2e804111070790000042141c4a022010301ca2080603000380c011030182c02144181c0c81c0f1032400d40009180024003818203058103039036194400c0c2c50101c580e4001c03454480f01409200a05240f500281040c88440e0120145071425101041610b45000454111400240400d042030324071080c1600e1640080c1c0300c00d000c2a401c014900711a800d030400f90007010f0103402030380c1e211565240750006860140d600b00d03184c607030343c0b4031208001060000e140d04101d015010a00f81c0700210301d00a441c1c1701101440d6506100481c08100714030b0360000244c42038a1049440c0c0e03603d00a049242d84c414054903100c25a204e40c0c100d07050004a208402034200c4041900000c2040d242e2501c5a80c21070b00381480e00005941002c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 647412158 1250 647410908 647410927
    0x14100b030709110f040602030421080f071104050916061112090a030c060509180f0c0a0309061401050a05010908030906030a09020d05010906060803090105190c02120f060a1e090c08030f 81
    0x103144160450000c088a40d009d04142e58051141c8338840d500c140d415030101c0c92806005e103040780009001d802a008101c01c0c2000001e4903070322140188880e046d00e12804021400521820740041c0c500e60700030003040300c05901702c0340100300c2d0461400c40350000c064680003c08159a490084002c0172142c441942c1c850140c0103118400c4068964900489810020700c40300e00c00406c06181d00c101c0404d041c5440d041011001c85c0a4041c00c000600101e080c07502912441e000c1d1502d142c12640100d07200d0490994800040d5565100c1c0d1207111003d4100344580f0090782800001941e010a40400c00101c2c41141d0b80080c4056520510650710360b9501d009010400049204003009007446500440c104511700d00001c01d03034441e165101104c0c50288038525002402110040ca10076030044c0307040324440000004956411401c04116168403400000c00ea0001d858481d40c00c4188400001038400a91240b0440252150086c101c5086002100015100d802070025016441c0c0c0562101d64500c11742 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 647413408 1250 647412158 647412179
    0x2190b0301081b010e220603050c1201050c070609020117090d080a0b220f0603140c06090d08090a350c01020604170409060314100b030709110f0406020304 68
    0x60350f6283c0080380419070000c0d6a00141d921702005001c95285a09100c00e800308500709868a505003e020300b00100403040103000305030890105070944041e044449880145402c0c1e55080c0c0b51284801410885000441c110740c00144641d4011304010090400c003050040c142e00c4110b40301c100039048800030100f00b42d0b10440050f009080e802044c046079503010300066244440140c0882c6842d81014920200980c50304406ca00c03c0381e18204124440d52410b0104515040313845c1030340e00380180d0f21907000b5898214160b84000002602c0036002c0c1840f9990109198015642203501400d0034a000900408844000400ca120030005a40300119600d981d9120b82414004909907000075480d002c80381d9000072940da00135080301015031810040303941c0045503c00c0d0b07003120002c81d0500001009015958201403812a400f00840e240c41043c02c0000e011a0034000c50140c2c1a0820642001105000c0d00081904c50119050700d00c2c045440814610b940d20940c840c002580003c1010850300400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 647414658 1250 647413408 647413423
    0x6030b01020708031b0109080703080415021305120a0c08010e160e16090e07020105060a050306100302010f09050d0f050706050406020a02060a03020c19060b100804080702190b030108 80
    0xa00082501d0b41c148101d0903140e02903401030317000d5840d140301d844821403800d400116030703140c00640081d6600140d0030020844142104c0a90340f400480c11103902c140098801c88182b8002107800308903079401c0030300304070450b00e200c0360a80061003410647d1000c2081c0d5201c9500821100c000090380e441c41000c01c41c1411078092000818441a03001000036410700c1504540c4000384e1501d500b00404210425212080c3c140c0100c10320100d51020401c2281e01540070300c0c01050115504441503070b48808041d52107504560044e03e81e1041030007040154010122242007441a0400021040c0c4510104882c000c00c0c03441038445924103e00903040c1b00c020300926018144e5443c045244c54200342e0f02940c0c071501d01100a010354000502008494071039030503074450141c948161000071a14245100c001c00d0414000d0b10040d14010000903240b51052401120545d25114243c890b601c1ea2503914080c0c103e88026130300030b2032040c5846088807084004074003824661100c0358483d4180b19030103142840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 647415908 1250 647414658 647414681
    0x50601050a0c0f0807080408281119091416050403020102070b0f12010905070315140925050304031101061406071502030a0614040b061c020705060a05010603 69
    0x40400800090341da010802d0080c442e04080f16090307102192428040a100e84400981071401c007003008981d0b80710216440c032000f011511190f030401c1141c8203566001c0700044009060008500c0703480354034141030025108018492480d802102e0369a040b80c42504d0b5001d05c049040d1006004001080c0c03100340460754103d915144c081d003882c1c15940082d51f551000d00810481103000b08034000b807400d120b4104c0c0e0751a20300b4034090441d940d40307414501c0034000c140d400b03001207402c00045401001040c04424102c0b905400c107030a03404840418081c20000c044c00c3c0d0395110140d0b6903003c940074048403001c51500e5103035507403079902e1801d81002031580c82100c13400c80040e410440100002030011642010100d03045a80d55612480c501e8598110400700c2410300855001204010781214640e002c07008403000e55410003446d0340c0240410084440e144610307588488180b01c0748000d0780c2c1441e0f03201148a000c2ca401860142c441d00c2d40c91600c03a00300d6907901125151801804502d41c5801003010106 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 647417158 1250 647415908 647415917
    0x1e0a020312031003031209120806091e01060f0915020601050a0801060305060105150d110c0f060105090a0207020328060c030207050a080a090315020a0e090411010c3201050601 77
    0x3c25541d02c0b90070001c0b522014082100c0d5140da502d420403182e20035000c10364001000c1840348100c0d407028100c0c03a011101d1324841c4642c180010306005140040802d032725100c400c4d84100d80c0c2400402d948103407009000d0010000d0296000c11400941e9a0304c5082c90060307001056551b2512040004042a940140e461641084400c0000410018645054034012282c034140c00d00031040310426405000007840d030035814a044040611407080040c4080d00354082030354080c07560040e80c169a85420321825030841c21040004410340346a07800b82801610040c151600c2e2010701800c40a5614081c20352804401107510440c1000914807a0040c0d81600b0300b000d600384020703034890f16195518034901a000c90b200084000c0d03041c0c81107a0200141d07034000481c10f124040900100d00039080580040b0200d04982c0110001d454801d000a00ca00e502000405221855500444018001600444001014841c942803143d03600440501c401000c010010210511381d54039070a42e840900154180f0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 647418408 1250 647417158 647417161
    0x2030c2a061206010e010e1305180a02011b05011113051008010b0a08060f0301020d0e070602070f0303030f06170c01020d1407022e120605010203031905091e0a02031203 74
    0x103000e1560416031210003400d11482c5242e0600059800c01c0c61410103e9024920b40c2c45002c8d40807603a8042c40c010580c4102c0840556408070300710b9519082000d01a012650000700340381890540c0e01c5d0154514818400030561401c1146001d80c1504071307a026a07000a00c40d0803d0042c0c2c00c0041d015855100d83d4540349032154903104c0d607900d40740319089401c400c2005003030000f01729031240a6060846c16020f4000c558400c40c04d40c040005040c07000070910140140d510000700603200107003c0b0284c440544088881c545582c0d42580107014800080f1000380d250040000c5000708298901401c020140c0030b44000004000028104481c029941c410f010f84075400c924401d410340d0582d5180c40e4180d903c2181d10030559a8004003e80b0380301081e1884000e051031001d803903400000d003803003801c04c0c00060061a48800c01a40c03280011902c1b60a81c039100c541500c41014140c00c0150007010b08815100e00c01d0310300c0e00382e100c0ca01a41030060503070b47c801c0d03030260118203081010000a24900b82610700b103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 647419658 1250 647418408 647418427
    0x30311161a0c0f07090f060b07080906160b0118151a090319030507050f0a02030604111206090f070b0702180405100207050c040f0b0102100c02030c2a06 67
    0x110419442000c011a0080780c00003010004200e903c4030100030b007089400003036482419a0241c0030000c841c1e0600707410320030001000707424102502c01c40ca91103900d05051003215410b001840c0c004a9844e081c52800b0500240826443e500060292115210b100e21010100708258140d030400700c0d403281c1c060034008041014050322008030301e0705200c1e041c2e641ea495010a0010303103030000f0404044201e883c0c0d10030707040c10503410200401c03501e44910241c0317007004042040c8989440c00750a010303406401c0900003400040600f00c4a03400b03000020b20a0a00c0c0b2404040946003104c1207455685039440201c8403a800c807000c1102d41e00030200395002078a0040c05d640072400900541200d2609500d140c0c002c2001c003e0140440c62002c0d20b600c400f15159130403030030038640e40c0c0c09414096000354680780c640c681910075805000034542041c0c000305862401e619810000b4580e20064608500091100f52344021091124400070409680422221000b021001c0810400034420622a25080001100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 647420908 1250 647419658 647419679
    0x1d030c09100902030907141801090209150a020607080114010c0f170f04050f040207030516081902010f0b0904200402040f03031e0e03070302090a140103031116 70
    0x2400009454140e41911040075118000000e6040035003040e00200811200050004200c022104007247c1144003100000504c00c0c980300d182d071450756030012000103000101240d0004c020200001c0d080303111201400d00c0c42d007100e400440074070300140c10050600555603400380c1c0082c050804214400307914658800081c01d80815140020880c04408641500f40030900b601d641c05005940c0c0e8140e0365401e030320309c540856401401070f40c2c85001ea401804015080c18402d8480c1e150745601c2d500e25001d1410100d111041800138110351050341001440303d50105110100070b610382540000c00c442c03015a0201c010703038100f4404240a0000d150800011a032811380ea000ca0850044040c26004859004500a4400e13604800011131200e50000101584500e6540a60a40820130b140024155a0449030300c2c040360001941a808107a061015103401621160440082c000020300354030032050018440030243d005401003140111041038080050000480c2000e184000188807803c2146492 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 647422158 1250 647420908 647420923
    0x60f15030509030405121027030c020a0902160b0c090f0907020a0506040c0806070309080d180609080408120306010c1e150b040b0301020f090d0f1203020702011d03 72
    0x204064032503000c03548140c800d00484001c1c141c06444810901d03c103c041c5580c401654000003000c5250402c1e650380a28090500c2460046c13200002000c035000c0e44046803d66407809040c3d80c0041a0301000038100d1040c4001c20071000c0c1040006004081c60034402034802d4010000117803050200004a5560345008503c01341c0541180d40d4a25511604800c03481d064540000918a104807010700040c0503141d103207001250084002c80d2413a9070780340c030300701c050300c242101c0200850820b002d0504114010303040301801000d062021404013a09484420a07240e002006540103c070004060003c03400500c15040c82c81603601e609071460400d100000d022142d00b000c040c1070002c0710070b84d0040000829944411068002246401031039602a80308000d00c5a581410b105620700840e0502c02e08041c02603906a62121800900744450b00080c0301e1011010b442c1101d1058041e94030200041d910305010b230010606540068036a1114030024214003884140d502c4131000d101c10b034040c990f40018094 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 647423408 1250 647422158 647422199
    0xa122a06030e150703051315091e11040515060d06050a0e010b1602061c0e071a04180b0310020a090e063717120705070605030405150708040204060f 65
    0x2000c2c0c0c0c95001c80203500701f8000008100032500440c100300c6201503042a003200303026190480050040d0f44203d5081c0c058003400500d440090032400009140c17640c841540190900306031001400000001002c5038400c4d080303251719940d180d80a02c828200700f80d010010300710300d03036404245504006d00c007c458002c2a803239041c4481c40351902821912610252182d9034120704101128600d441e1003a40980380980e1001ca05200307100c0e00061500701c4918000158506195652801c2d040c8001c1407185044800b20070784080d1540030079205038508021110004c00c0c41400103071102411f0000501898195002a031251080420b002483d84c400c0b0214414128881160960300300482d08154004500442c0441d40500b0f00700000d40c00c840054080c0c0440c0d41c080a03078a0301d0403081c00c201c50b903000b0031a0180a40e400040d00788121402000110341050003002203407610f94440c1e01c40096058116801800515050148411030525000300c8000d03042c0350100c5000c441c05c007800000f41400300c1c000d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 647424658 1250 647423408 647423411
    0xe0307030f05030409020a080609060f010c061d0312100803093106090903020c0904120f050f040303031a031b060708040305010f0606140304020a122a06030e150703 72
    0x725003002410412a0014506400190749820102c0000f0b000d0007401c460050007960141300045484c0390441c6050802e9205841d800340101182c0c41e458001e1003c10390b600135001041101040620080000d00752442c1c0907440d41c1954504500b4a0740130110941c444205d80e0b10074084002c0d5665104100150a0800318818140c0e61900c800b20028100c110034100c0028a418000300c0c20742c1d003d8021800003030080e021200f220702240280000100111400340003d104c40f80d140110a1003241c04806244483c81d049083c5244039607880c0d91a130165000301e02196032940c80b110039059484180050682c00c074040c222820b100d0b107507841d0491b601c10561340b08400c0043d60b4001c004110341694042c580210081001600c80c6408000500b81401120082007241002c011195a0902180c1c400d0b517000d41000019468185013080c0c8904494040b21007034100b0014a0140943c551150620010840c00c420341d903141c01c0380982215a043c50801c03c070f0b000415248088081e800030243c00044903c2c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 647425908 1250 647424658 647424683
    0x80f010b0304051507020c10081b09010908010f050a0b01050c0a1b030c0b130e04051c0c1505010f05030f031c1103090706080a0605010816110a0f0c060e030703 70
    0x2002130a018103003003501ca00140306410300030040d900081c0c030440e001040e00e215076841903c040540d0307407890445040101c541d656090302d0700e031805080030300700d0007406060104105859180c0182903520b0b02c0140d9100c103640b1002c202590740240a008000807027800d2851800e1000b00d0740b0ba4640310000300290001049224a40c50301c080001060029034012403411580e0f5200c03912603210703a20020300c046c0603400854001c206490701400d101d0041794050000c0c80115484607060b055440110b48520900408140600c0131942d141880081004007038400600c640c10180e12860791011600b00c06c1c003a03031261010751035000300042240d9000402d004003007050711009940c0d8003d000c50a00190030200d0210a00003001c00014104c802d0751420b403110505581c521040104641940c4240c600040f014404203051020042051000c0080e07072030440c20f00e0a00ca0101c40c5880052181210803071141c04004090103170000804000d4041d51400441ca40a1880020303580e40060101408074840d01d00e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 647427158 1250 647425908 647425913
    0x120405120703030615020f030714010609050a020c1e0a0b06120d05030a0f1103042003061819020a0506130312110d080f1b040e0a0b10080f010b0304 65
    0x1001409040c000080c29503240e569160081c09480d09104071140c40c4c00e529000d0607120b00103e055400c51514600441c28010151114842041200f50000865603105004a038599890040c1807250b10040009699181c0c0a00d4191500a1500d001c0302c0c2c18600312012110751801195515000350007144505103511000b0010b0400003080c0c0c40e01484d4440da080308064150440040c0d44210404a0b0400040360076105820541c0e43d4104428401041000007030001801c038030489000c540078481008a044040011130720300482900c4c029412100d94910000303a05e42001490900d04202c54440380d03562003503010491840e100e0180a100b0840458905165031090301201c00440d0443c00088041c048400c3c094a00d00c40302810b801ca900400c00c803025018051145280202807000481c14151355503160b42d2080120340e4844800ca000030070000900010a465050007a41c22100c000768201208003005115280140b500050203150301c10401e034500c40041041c1140c038098102a0b0701e43e61131 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 647428408 1250 647427158 647427163
    0x8130303140406060812070803071124060301200901200706030504140d0e0f12030d020406081b090906130912271a160f1502040b120405 60
    0x825200d940104907400304014880c15401210484280e081507440d034401c4642c0f02c40f00ea03c00c01c00d0103019401c0400c045496280704244156808499406a490f500200d90725811411148440d200c9003400c0c6a041c441039140070301c5940d103091035244202c545059041640440c0340541c800c41414440310702d4442e101d180030084171080222099003690403441d180c2a0240c0200000e40c0d007680c2d50080c552030308041c2800016034590a070a2500c2d00361180c1307410b400300001e01510355400703504100060205059107070704101516224000c5e800258849080c160f0080c484c4500400320258681c10300c822a601d10846400c549011005079003499903552400040b900d0b000040d4000045140340900c0d00e82440310345011501c0807416541d403e2810181c103a00400445079000030841c8820b68010100002c1d00c454140c40c048900b1140018180141d4140c02021a603604000342c920340080da0b041000c00240c11440b81b0b58600d902021801c080c10301c401032000f03004410340508060360100c04a070170f00004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 647429658 1250 647428408 647428421
    0x51b0105090a0305010e010f020c031b07050a03080c010b010219030806010905130c030e0303010f0605070c0305060907080705300106150c0201090806060303030f0411030d09060e030d08130303 84
    0xb9001c1c1820543d0f03441c1140c000c254481995080b540f8104000144078000d0089034807016818000f5414100004520010112103d00751035482c8903c003000600c603140d00803c8030085018400450b103508018400c0380c29114040301050464210210708082d011b0342800602e0384a03007600e0b00c0076444d5107903001a2041800782d042198800700500085500d211507402c130388a00c0e10700e95824042884580c60250b5030340028040e000f80d11040301c000380701d1181320b18054151140910250701c500350b50ba849607400c1400640b80544d140d08145010300c905c10080007080024a03080d078404241c00d54802480c5070059000c850441c6552071450844485d450940005000d010041c017509141d0310b001e84003800500a802d8228081079180c04001010b00011985a106000c050007551965646803017580c9200c0c2c2c01401140d00d03454410421800340c504210040400c54103451b0b00703890605180c40909914007010201f4880da100076003400070030303038001101da411002502d08012181c0481ca0b00f80c010300385 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 647430908 1250 647429658 647429677
    0x10b040611030423010219020f120309331e0a030e15060109050409110105071b0e01380d0207080708091008070212090d0506130c050d051b0105 63
    0x2424000d136461040c1001c00403000c00720907001c441e0744c02c1d0104e031081800c00290b10301a41c0410003203002e0780c2d00e00f030401c80188140311001c2580d09d0125450001014407902c1708001c0304866410130b02c100e413181c2121340500400340ca03410b42410301070120181c3c0420362400d0b9141c0094203003c95806403c1e8041e4110303589840161040d211a256001c1ca824880c40080750100e00096800f2000519420144144c103100360304070108002a141850056925500c02641282e02e0311015920445008528171008064910170002012a515040c40300c80c8100c1c074071610820084501018601450700203001c4c805550340104010f4481a002c0c264000a01918101030300c0c03ca00010701c1c608010381d042c01001c0c0f1200031590802514140e420464021408560090141c0d0101c000c11200080d40405882d40c00b200504040003481542d1b40c00e828480241c40c00c07180354044c00180c0301040880103892028040544d501505540241c8034660b9440a202406503a00c1c1e40c009541c00c2039105500722100b040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 647432158 1250 647430908 647430929
    0xc03061e2906090307030602221d1518180d08010906140a091e020706020307020106080c0f01050d1805030703031103010b0702040b0406030632010b0406110304 70
    0x1888411407545201580765004680d0401040e10540c0c0341c02d4068800f62440900142000d41c215a81c2000a60001c170048503602001061414241103010006c8050300d0f000b4222040d414800180c082e442001030006d55503070aaa4000c03020540340d005242d914000c19150020083c0c4400850840c40101415030031503030700540d07400c01405034011082c075040f0b981c4c00904000696076003004940003030041c5000f42d0701400462040048442e641c003c10b00f12848402c40541010750a42140e04982c0068411510030f80c000c410840880d80a2080b0401860548040d00c13a100d21180000c400f005101c40181c184030000c210708400040303981c05103003040c0f00500c400060f12414100165203030030001046001034100381d4070159014480e0280da049079210343d200341c1014103070303403c0001a1205406e881c3c1c2003903032500c0010100d0003a0081d00c04580c0c045000e20100d5820070041090942d107050a01c8008013444010001d4142c0a0304031411a041841e00c0309000c00003038801c0741584629031040036102c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 647433408 1250 647432158 647432171
    0x60b0f0901030e100c0e120304120303020c030a030506180c0405040e1c09180e060417221a1c0b0d05030408010c0306060206070905040b0f0d060501050a05010c0c03061e 74
    0x2135070039480403d02007415100c1600d281348240400c101c010600b1002d2000e0380080c08200328883d03c4c00300d0b408181d80310b401c02509185905690310f00c0c6d030300544810342c00244c40300140401c90426401c0e40500050b4290905031510384040c00a640b0301c1148500d83c021640c4845ca02c86040080c005402c03440c007000b40300a0702e0024044000d000780d9260140d0300c241c01c00f107500f281c41c4042070b1286984c11800140580640e40e159168245a924045001e08519404018600300e01d1083c40064981908488241001c28200043d9603a20b4000a405182d81501003145c10180d91481000d142004413010300400c6042c1d0b14008544881c01101e402000d40c030020a01080d0404103400001182101d5682042050740e60001240e03500c209540620203e2004a81400903041070b4101240e402e8000d0040311140a0000102d19084e0006005170b80303540c3d6800042c072981c40d000c01c64400401d000d103030401c819001074540e04c140b0f4196100042c8a583d640040800034500c42005103148000b228041110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 647434658 1250 647433408 647433433
    0x30304030f1e0302060615120906040312020705060415060b0c060703320c16050c03062d06010c02040509010203060f0108011505090d020d0c1503060b0f0901030e 71
    0x680120714080316003080d40e100c9126080c00d208010200660503600a1086480c0c00b01846807400d00d401d0400c20000c1c040000301400020044150b014407100c0000b0070141c601400c00811141d003980420b612180108581800320b1000618290059084080450440d000616034001404185c2c403c0e02e000c8404980010314010215086201e0301d421745041c0b02c0002c58107400021034410000c10301c2080d80c05406080c00740c900e0180c0e280c2c841d156a4000b0314081d405108455a0f2140c04022510b41e407212031404014102401429000b145000ca904020f00d0302c1c041004124205440c101e0302814560300084040e881034544000305074010301308121300d00380443d900e4040d5200301c49040c000c48015440b05440c1d449011080d0485444c0b0b610380010000290003144d1981c00340840d16800308c10022a64003581c0c90f49082000188070365503a4001030700c0c24032003440b001105490102854944082000b00148080c04c840c1e811451030745071690b50340c0da500160001c00d0017208004841c440c0d001d03603600303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 647435908 1250 647434658 647434673
    0xf150e041b020a0627060f0b031c031d1c0504030f0b010302030c0d0503090402070201110618061f0605072a1a0c0a1707050d050d0f02160b1503030403 66
    0x14101c0c00703080140081241180d817242c03030a14032440260054440d4581d83d0100f012544050318403101d0300c40103c1c180c040400000d2809110311850034001a000c0c0e418181c092b054840c148040d51003601480760500164101602c40914121047c880950784101d031255501c01c104503405141d10200120b00c00040e4144541b40400034013040b4041e101d92140d540051808009001d25154040e00035441c102600060001940010408030305201a1030007000c00c0c242c0034000144100b84c42d446a0500ca803903188a2840c0c08405403203524028400300d00d03142120000c005120031b64000c0d09140791350300b01501d4002006060b0b0303102c003000d400c0d410b4180041504800306180880e00007501c134941b00f0990604161840c031404800000f036034485204200082e14902d1002c80403903202c0c0f025400d02722940c4542c0e0401a59001400c00601c0006180c21b6010301880b503d003160320103610441c185004450300000052222030083e041c3c1c11b0003c000b40c07100304c40006143c2c001d90040c044d41e840356681d240800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 647437158 1250 647435908 647435923
    0x50708031903020909073005060913030801121707050a051002040b0301120809060c030306030607050406200f0304091401170d050c030f031e010f150e041b02 69
    0x345031000c06440181c070300c2030080d1092044002c0c2031845a0301c03100400c0d117141e03411060750b91796009007410402e04145015011340400310100b00110f07440c50140700300b1036001c1d0014400400b0400303a641c0c9401081e40a20b1880c155081c060941e00413208605200024484141d0354450b62100040c1d110100030300402e803c0f01c12441041211350610b2011030000903070145000f0f500764401c0070f1004000c0c1d0030814200f00d9a040c0100e0055182001c00b4000c2840d69110f04d81c0d0707440a40c0000244407031030030b0030441039521107014a0610f00700360500c940201070b160000e40c01420a8a100300100400c80300f44408660225080f04480d9120727a2104243d01410509424561403001600001610030607450201455007a074006058040311501003607030150041c40d50482540300034040c00c41e20280d507000450066661a031380070040f1701c01044940e4604416000203c59484036001081160303c94800b400303402c18a4104a00110282c80115009005656103071481c0011603801e088004d40110390070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 647438408 1250 647437158 647437177
    0x7080a02160807050f030f160f020a171525021501060c1124030c1c020309012d0b011803110108070c03021005040206090301060306050114010e0307150c05070803 71
    0x90380b030170161030b52050720303401852010071705000c0402003018980e160400b0102c001e8460005821200c940c0c0e0040b50a07040c0a070010107105070016400910284104808840680318441d800901e03c1c007034105144c43d0a0b91007441402c414030b2928003004078003d021031039800c0302d94030b4400410b6a690400030521103811100f45c80340001c91004090f9424a001d000030880b03165906000d0b105041c040181c41da900003404400c1810040c02005d04408040100c0101d42d0b0b0040e4025891703042c00b003522800c480b10f003628403a9004950790252046012900510100c0b4a80c14000518444503801610320382d140c0350a110001c00029008804c1003140c070b1a603c4800001ea032801550766500805030354001e0f0381da40260240e4050601c1148a20050704460390140c8044c100c1e6090400c030b0000700342550f019400031a44991260014004260b8000300c80d5500350091801e0030703c1b41c0391900071a8884500d0b01861000d206040c11390005940038060700c14403d80c0c84000c0f2800c15681d505d0080c0c0700d07005200031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 647439658 1250 647438408 647438413
    0x5041a1f030c0c05030306090c0d02070f0209070513050609040612140f030f071b0810060e0604110d0e011401030606060f050408031602041d160803040e07080a0216080705 75
    0x401c103150f4441e403e00160b803a4000e00441c45c503100e40c002c0010b0994001c2050003030103020002d03611314101c5800505891885401480c0084100c2c0c8100003644000411500810400b03220785001810b6500c0c500e0100e407010b82e40165281d54040c08500600317020b4000c01520401c0318452810800011985a00984124251400800080e280e1a202d1103240048494013030280942c80100e841109602a00383c04940e603119010303660307208181400c0b01c010707607059402e640303031410400f00f000400a158042400c0320200101d074005421034a041c091a17aa251001d0740c1c42060345c0d2808030035800b13481401c4d5090a00c031019a03591411002404160281c000041d51803a8451000d80c024400d85040d40da842002d182458000d4104482544181000340ea01640701d044203614896043d185800500e0030002030a0700d4030001000c1801002c803640128090f51040108101480c2d4115107a600700f240782c94400d82c00d48407250b40e0350103401200401c03180b50a003d504203042110020003007000c948284207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 647440908 1250 647439658 647439671
    0x2070c05150702010c0b06190e24010c080702150c030a03061409040b250513140102061f05091e0610020c1203040b030a090c080a050705041a1f03 64
    0x41078500e80140800240840c0780b42d8010000910300125007903010b6009085a4000c92140c1030242c1c2c40c030469070000d10400c076140140051040c0c106d0f0400b6402c580045803002c0c0721030140c0000d2420080030005002ca070030114401c801c550b41c1d1024071081c0b413040201c6d00d03268811012100d88a50001e01d000d8046494520001039401000f80101e1207a50000c2541e159a40d46840d2030242c000000c00403040b0034504c1c01c80c600d40440701035210a0744c03a4a035403200d403541e810a1224810401a40003140e058800c0310107084d150b07a0020702da60f805070080044441d034806681d0703149804902c1d40c0101e41c0c0540350300104801c25000101c5a148070002c440390f100980c4a240901840c0390f00c1d40013240040e0803005461016003045515070f44020b6125048a1400b50b986c00c0300be1084d082a940e1840482c2c817034104009005c251a03c81001c0d041030700161560407419030b00c0c0d030744c0d80101d449502e015545921680030355008014400d141e100c406401d0a250a0b030740f100c40b540c003182a1340c812010038607040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 647442158 1250 647440908 647440939
    0x2030c10150e0f060f030109022d0a0b030403230427020721021005010806091501230409080d05010918020d171308071d0705270402070c05 61
    0xc4003409102c050100c1d8034940c9038002405101e2540d45c00c07103a015034888485c2c80c0182c895824440e500801006481c892070306903601d01c034802000d01441071023030700410b50510501201c4401c49400c942d150410301406146080c40510100812030900c90350340e004600001d885000104029180c07409040d101e0803c2441e641c0c2e0f404a001e40700020300140c80051800c01203e503c1d01248400701f00a0040b1807021440d15440320541e1800d820018107a0881e005214070030702d08020418496070410b50703042030781d0705280f40103030100300102c80c00074810100300f000c07100c9459903070210303401c0c9402c0220541d8981c0c00d0982007002e001d003071040411107894140d40900f0700040c81c0501408c0c6d6801800d0203044000d545404292114038540a00d12520400403861000c501e0311680000300380c070a028014807071500e11200110000c50503261510303500c2008228035107502c0412510741020899116010110322007113038444401d0301c0354668110b031001072800c3c117001101800608403602281c80700320040199 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 647443408 1250 647442158 647442179
    0x2131505040e0c040c05090a081f05040317040201091d06101d1e0607050a120201140f04140708071809020102030a05030a11190e01080411060a02030c1015 68
    0x460b0b915041d40c1200c0003c003480c3ca0305030010311107810380e4900305090203440b00c00260b18010b43e42c840e0500381d0002c00060095203c00c00500c2c030a014602c000c012510b05524040d10740c1107440d2040f42030704800380008046a00441c86440508038581c541030604031100d41c00c40c4c54020603a281c61240819003a110301c0ca900c00c0122005072000fa00555840400140600a07c807020728403261101c41c034110140015226500504000c0340104010020b076006414a10054080c0340a24021139041002000c0c901c5c2205003e90740010030f00c00e602d41c0070340e1a030605400074002c6425910540c0600c04000560a800051034002d881c0600495001d05000f80c41080c211005c8000090168009000030b02c0c155010311301442d4480704100c4080b500c84961000d44034954440411828444241c400c491381840d403210741003203000d6013800d00c1c55013401c0c55103030f0012404503009824420000042e2030b0280b00e10a10540d8503088030310007120045008444048054000d6140519035407450324000038014002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 647444658 1250 647443408 647443421
    0x72c01050f0d091a06101106070f0c020a031101270e040302070306110a1b02010c12030e01181a0f010603021305061201031205090102030f0702030a0213150504 70
    0x5848952401c0e2200004a2198001040c05085035a0740c00c980c001144203d003140543c2c0391100c0100c81580792500c00c100340342e8005124002086407800b00312401d4000081c4c3ca540084139400c002c020011010005c07120300c054280020b401c41c0c810030b400405c01501002070b400780813090300e868000c81054204420160b64440d2050314945003100104a0040099000b5400c14080d1054a0401c0e0f1640c5986068400801400300d10003400205940d80070f0f444403001c54180007441d54a00c1c1d84042d078000800c0864000310151007680d00c200030612217402540302c4c2d0f030040c101c0340080c014046141d2000076015811768003a100003c8003080412800c0c1007442d40d0740f040b450002054541d9082050480c000d4102d6205400710001c402030100d06540c848000e007980c942240d024010075810b6142c0494205c14613000e20007448024800400c4aa0700882a100300740003034000b95840d103003d40006864064083c40103900315001c0340011901811a803c6089440ea022440301c401079658400d00003200c54 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 647445908 1250 647444658 647444747
    0x9020a020a14030c12040f0510120506040e010c0201091a0f13030302070c15020d02030408070302040b03160b2101050112020d0b06030c0a1206050d02130e010507 71
    0x507008001a003181e2a4401840b0810440b4203002c90740b0f00f410700c2c149203042c0000d5500341c0420700308042a00002c600c00500310565000d4841d5130a4100641940b00c01005200141d4a03480050701d40d0700e4aa206070a51007180c0000e0143e0300c0e0002000c0d00a11000d0800d507404125034501c82301002030350340340d103000700100c0303004100e10703950800c001444202c00d642c00c07420190200482800704a001100e000070300003d0780d40d60010080580041e1801d5003e22000042d1f41040c030003048910004600031085a40550b03012941d6045400001d040c00002500e02500c91501035001c1000d815800180800c0000d01d00040c69404071104140502c0d1000d01c15240000e010b114850a18800364005d44040f205001010840320404030015a06400456030141c44041c00303d0052199941324100141e0702121100030081c0340c0c01c0c0004030b00e01e66070114020b4040e0f1260030503694500301d40e500c401444006038000b0025818201002040590581c01490504414403400c5c1c0002045100040d036811 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 647447158 1250 647445908 647445913
    0x140102070e0121060b131a040908090411070c08010c171003150902150d24030609030207271d06071d061c0509210706060902160302060109020a02 64
    0xd92468442030000040e0b0454001e6254103c17040d0989070304610380448801c15402184003202c01901c03802c800448040540f0030707410502d048010030341d0941141e00c45803041d034001c21500c0c1040d11404840c800d550009100c1444140005150803065110b0700b1403508540d180f0f012001c801c603400c9150700066079241840e00e000801000000d860b21000c0e94142815640483c002d5030580014001d01c3c0b6000c1440e0414600046500b100c000c0c0b071059580c5280f85400c110f07000c0d910440c110101c1140d500004003800d50310f082c204103142c001c000f22030060041803030711602107070041c40d1b4110705c0b1540451000b5150601071410f50205295104141d50044d04009011700d56441404079080b02c84070000a44512151070010841e48901c2e00034101150420003600085620840c040121400108807164507007000d00c00100d4292402002e080e40c5005041803a00c2d00c40c14102200140a250b01c4a04054400207440c24240c054080e24440c0e940640c00342e03842c2c0c1c0c5c0e0b240022400d920030700071100c0058 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 647448408 1250 647447158 647447189
    0x1406070f180501030b1804030c023d1709010b03010b060a0c030e130603110a0617070c150906090201021005010b040504020304080409110726030c1c06140102070e01 72
    0x207504c80c0d0b100020030f04009007170400c3c3c0c0c1881c100c0b1034054103043e5826000100c200d0704040540c10b15104403c0d41d03803190303101130800420ba2452032440032a202d001140304601c0c00b0f200a00e051003041c5c4403100c503001c941c18003c070f4140584a64001d11089050b00d00170b508281d000350480c034014056800300e0405440380c0076018419581100c3d03800c1c1d110701c1c0c1eaa1260105000c01ca06465910520014520a8540c01341e40c06c4031400700b11b4080b94070303800300e0b08001441c949404450307200c4002e00c0d0084001e0400030041c10561a14500d0800403d502d88041c41c03030245c2c1c04003400f502d50007a08840b4000e07001d5a942025420018050320002d02a1003030302c0e54204001c02060800e90300840e401f40c01050403a051544401c0030b40141e450014038441951000b081100520458406068081d80100c1c0880300103007810302d0101541c00014007416039280c001c0380d4107007a074a5404a01c800e52305502c80030001d45807191800c040107111071103824010b1095010100c0c1115210140a050742c1c3e5600403410700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 647449658 1250 647448408 647448419
    0x804080d150b03150405060603131403091903210e010f031103010e010f080106150305042103230405100203090723010305150f09131406070f18 63
    0x2500c240d6400c4441c0900e200c5000410030701d41c4000d14040c040c5840c1c0c41070780d05005000c01003541c001a120342d1240c4010014040520400321100c26950381c40108150b24407201045582540140400c2542001101a03454091400708200304180d030300c10341200e000600d07000781541c2021100c8160402080c010001c60f0142d40c01031010800c410064540800e03001c0000d02120015007081c0e02c601030602c149001440ba5041d40d010400140042400811a00d49007030598424062280da50005241c0d0341e2010505000140f40c4103032120f840f020303110060624101000b40240650802e40008985000440081d05c488030041d5000b55040300c02492103080c04000342000750701c0500a02054402c4880000380304158000d0400d031070420b00d0b24800074501d001c001406031172001f801c80760b0707034484140d094202d65a098404030712a8402e550b50703c2c403030b03030740d10700c00754440e58004400b1f0701450305c13003815070040c00000801910078003403607443c82d40200c03034500240c48030000300704003108824800030306214 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 647450908 1250 647449658 647449661
    0x1f081806040c051c06060f03030f020d050d1808160b01050103090201090510050c0607030c09060806130905030409020f09041406061803030405060403120216081e1e06040b01060804080d 81
    0x101e04050b8001d0a8429250380c17604110b4005512910828403107000400602d6000b014682c8168450300281001c440c01c490300401d944a00c2c00c0586009030b80b06110002c06004005184c0780075409000350b030f27440000e904201c40707401c110342046030010a614000300c1c00e0f52090084551450303040c0c4861400900706010003c52503261f102c9c17601000010f01003d80c4e0440c2c204002805130400b5280041c8144050b0b10090200c15513400c40c41c14400400180003258440210076a503075030080c440062007400310b2806504610841d8403d07200103002107201c40361043c03080c0050110100c01c45007005032480310740d48490741e85030486200740c2c024010f10200141d02c079501e80811101070000c090381c0c54140c03250001410b5402036001038400c0b40ca4108103403034003501084018025801c0d000414080d81c644103889545107600d03810740740c001155a668060f5031800300660071507010400742c0841061100b030329032681c50804913415140c250301c82000040345405054541e0089800103601c0c1e2500c640211103a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 647452158 1250 647450908 647450929
    0x2903030406140f0d11070605160c030f02120d15090b012708030307050c0d1103040b07020a0e01080c0108150a0608040f05010905030903010b030c0604050904021f081806040c05 77
    0x6600203c00c02061220080c10700c03c1e000380c0c4142c20503150701d802880c2019400c44100506140044052400c2d016019801c90b8814201691500d400151440c510000701d0404400d440c415500d0000400e800680f0813007604500048180f0140c4000302950310141c0c00191008800c013507010a4143c0c0e4020180d001c1900f14a059280c1038070865003455407105a2880e6920449890f00040c00108004500e00740a01c800f40c1520750318500100c1030500350b00ba090300c902c55031203a80c1e80c0b0b04001a9490842d202d81c070307042c00180190b131300100341507a581c003150391180b03080a4084d0000b120f20002510000e5540d01e10b140c280000780880c0c0d88981030550507102e038900030384165000d82000e85940000340090049124081c441c0c40a1b40c0c03030302d171401c0034142902e00340c5400138441d800403c080c2c40161200383c140d80468400319940d030f5683e01c0d1400170440c01035010404030984c00b88901e81400aa070800c1d012805003c0e800071102500c03030010074468076034905981c0140790f80c008910800c07552402000c42c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 647453408 1250 647452158 647452177
    0x70314100512030f0a0507050a0b04030f0915080106120b04021603020c010203040f031b21020108070f2124030215030103110d060e0a0506010f0b07030818070504290303040614 77
    0x45942403103072b440f98030740050b049404900180b200c113044505240e111003000001d084541c03294145004101c005040c10070b050080b6001c000903805135001d001d43ca03401135600b602001d04119600c00225900d09440c02c8000c1c81130b0050301c02c141c00c15025502c000f044804503032007140104250303070440ea01e5103011441000c400c40e180c0b00c2880080b96003512461a280041c2403800103a440784072501c00505030740c100400e26024000d013900c1c10b03907020782c01285003031110001d43ca06d210b100da002d034551002020324800c4481040400c3c009129441c4102c1d40d40c0d01a20300846441303641e01d0030140c064165200c2408000d00708a03842454055608210000140b07007440317103a02048400c6460101460808041e606031216800480100051154a00c901000d0808040c110b4540700b034a031030280c40348030044d0404000a500c105415083d500c2400b2500107454001c1040c0a40c1564401d0000c1c00079401003001d845246403503611110b0b14001003203c00302c0745540c65001e4200c0200c01a01c01e0381c2c001000340e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 647454658 1250 647453408 647453413
    0xc07120f061a04110f0a0809071e0306050c031621051504050109140612030d1104060e0103091e020607020405101a21070314100512030f0a050705 64
    0x204000101d40b4042e00100c40c1e41c922620074020030346420401a21141c841c90340d201035003044013100d241c00580884084881608203c181c41c0c58a440c0f1905e00b0809501220b040b60480c035450b10021a00c100c04802c4278002c55051109440d2601030205030300c07003a14801244904004407a10701c1e4002c0300c40443c3e810910543c058841c83e2802c441c4282e42c0d045800103802c3d5450100b840300fa1400e4440c007405806d000004110080344194070300c13500040600220300c15002c0701400001840308104450f54003901d04014003400100c1c01858019800c82d0003204041040b46110381c2d0194803c1c8200859981c2000c104010701402d480b11100030f04c0a15401e0341c00003c1008a240961aa80265405a11031200300030b1003d150450f0502110040d95400e003440350b00b00b195034220401a84c0e400c0c038041c103100b81230078103031142d4600b5001030840d0121402c0751000c01c0300f004210f620020941e01240d40a036007000801108001441c1c480c070983c8010140e01d2004e021901e400b0b48a1805440584d00c150b04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 647455908 1250 647454658 647454683
    0x1509270c050d09080a23030a05040f0f050303010e0112051b0a12050a1b03081e093703031205060a05090f0618010b1803070504090819050c0712 63
    0x11042c00d4483c80c20050780d1844001480c00302c0c0c01d6000111a22050350880a580302450b140c412503440d03c0f0141001c2409a00c943c04641230003d80ca400603c0b0340d034404503000003040d240c5071090301c80d00709104502d9404900c000004070a440c0c0460304840c00e41c880040d00700d11711001401810041a0450300b0380003c0ca00d02d01155002115008200c1e00c0d0185000740610802440e005050a200d0a0220025894503c0c00c1000901c0202035a401c85602000e50759000304100744c003030300d6005541580750300188203090429034400c40407400d01c1d00048170425141841c41c22401c152a40d04c0c502c0300500241e005c00b5949443d2006601054100b60000d01c0c40d0310080e03559000554000301a907024014a240ca0144865403070407400c0c110f5003c0b0701e01d00d0400c3c5d6615104401c2c480340074410750282d00400c040303407070f80c0030b0340c0c0c144007440241a000f08100001441c03130422644980199103081302900602e02c82d0360040e40901d0503203044883c614010304617903007080000d000340604040e0455a041c83c45a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 647457158 1250 647455908 647455927
    0x180105100819030207120305041e0b0406030e010902090a0506012c2b0312051b160c0b04060207091a030604031101020c031902011505010906050702030307020a1509270c05 75
    0x7085d641d00d150003696234644541c1404483d0320403040c1c07402c90304080384140a04008010000060720211b42c411306001484141d280156405002a40b00c000e52003581c20041001005155011034003900083e03072941d001d28002c40082e1440031072418801181d2030540c401003e2440d1407083d0b00c80500c614409009810600c500c80c0c504001841c20440104001a840c4082c1e145a4402c40b80c2c4100060a528010784018208648a11a900212501302030905100c0c0902031104104001082400300c40b42e070740c650b5160000d4407040140100020345080462a030001c00340d02402401e0001c00030041d107800c1e107540e60266080740243d0812b02c075554081c040c2258019003803000e02041003180411495401a00078000c0c02c484202260200c1c20840d050248070030f99106100c1802d464290502e59600c0041c2e0002a1450060040096008000180114003040070108000a803d160385500144640703400420031405001500a000751140b407503001d407000c0080c0c100038040051030425a00d058000e1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 647458408 1250 647457158 647457179
    0xf0e0105071b031704080c0609030f03010e0c071a100e150402161e140307031d0a08190615060f0e01030b04140405060a0e100b0402040806180105100819030207 70
    0x86609440310302d80031442940300c7c00b06000513507008c1054405946048082107e1001d0ba000c18003400c0301c2899408001102c01000c582118000781d0000c00c0c5080342d4005045200220310202d601c100f4190398800c00144a130f204a0809004140913240c81943c1c0600070280300094204001c030014495106985801150180703e400b0003103914030030150314203401402c14101402019583e0030150788100550000702c3d034000350404a41c1e03041401300001c9101c1400103000d00000e60048143c81c001c00441410b4441382c5c0c0c11015503d48600300910140070320201c090001991f0f8400c500100700380880c09072504d0310400100c0c0d5441e205040000d450303000040070504441020020442841924050005100d000c02c4415408445110203016110002003403980f0b40c0d62100040b0b10642d19065031441690b101d80503103010700345e41401c0718001e1502261844540246074013082d807c0d40f90801007160034070340c1d010a0058031744100013403003d05010000203030b280540300401d400314041c0c1c4802094007401d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 647459658 1250 647458408 647458411
    0xf090103090c0e06011704030f0309030905121f0912030906060e0405010209030f011506050306030f0d210504030f0c05010915021c091e0302010e030301090f0e0105071b0317 76
    0x140100f00503e40b030a9400500b41c0390f44243c03204810b03107540c0e0811001a5009030700c2000580646000b041030b101500d01070b6161026a08426840300080c045000300e07080001d203d03140c03415002d40c4005a40300c800445411654500c602070550308103c00e5040d00240a0342202900c40d1142c41c0000d0300b541e8842480c0b583d06030036501119240d400040001c074520b401c100c04104600d4040080000b040030103545400305240b1b00c80c05050050110010b0003a039002d20680d07190a01c0c260542d202c0f00700800d00104121003506200410080070050001041814481c1c24443e07039250b110a1907a0040a0080c1e40140c680c5408883c2d42d9203e0140c24001105002e684000e500c0c001b03805616071403050020f805a00c00306200005091603d00c1010126900200200600550700900064007425003400c0f03014260b1074150802500c400800050707860307034540c0416182c40b490b1008101c9000803d1069080c1c82c0180d07510000100102c01242e41001c5100b40d108003544a401d00e00038030290240c605d01c1c2c01300c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 647460908 1250 647459658 647459669
    0x70c0b130204110307022b23070c03020108070f05040e130c14041103090a0632070807020303060a1403030d060909050c09090613110d0b18010902060f090103090c 71
    0x40240904981c0401c01e5002418000d0b5405a41599446420610482d1440d100c030401a07128200e005008450500400150290748c115a0b00c42d6207061506c0e0b40700091008038000f5040c000010f1032075114400c9030340300e8007403682c2d0585000d140c66600c0424100c050320100d283c00c1a603400f5070000d02c0540001000780400c0803000c5032481101c00b04001c03901074512001c0c0b13a140810400070040720205151154550140001665044080709420500c03244091341141ca09060b10181980e4060091184209a140c1e5008003c0d51030810482e168041a138410781c2287c506030003407000c0460304446400440026013124146500001340c4c0381a01d4955000d00c101c103a941082e01c05102080c454140088000c1d0b80d201040e0909885aa42d11a402030400d9640800c0840da9001c000500c061603031240340040c6070041c01245410080d601e03402c152480040d101c05034101c0c0031840c5060003040c8140303030000c10b19401c18450700009042a4424003900c5d040554981d078050021b14036841c2280a840e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 647462158 1250 647460908 647460941
    0xf0e03030d05070201050a09031e0905060d020d3207050c0d0309050c0108010341060910060b09010c0507090e0a0b01120f02240a030e0c0603070c0b130204 68
    0xf0b241c2c402a0071508040d00da10035150801700e0200c0803a8004542202521544c00c10b443c181032090004c07900f04240d5008903911072000158025440c0d03858018244281c03220004011100c42159107407030a09100e51035054003103002d099820742010007403041ea400009030170000c0c036208240f4502401d0602052418020a0380d641c40302c1c0920078200070280c002c5e071081c20020304c254150784400e034000e407004070082d406a07007c003604040340c89444c80f46d1107500700c009420110701080494668641e00c0071904a1928464000c182c64800e001d406070030110f40003504450314100c0103100460301314480c107105550910030780030700042c0020188201d4681c21103d0b0064441030b6041e2400700520401a03100311440e40420000e00042400c501d1440e06031541100c044025113150100f001010010349480c1c4000b01d00850138072825505600304641806464094602030b0008004010007070106456400c00a410f1030944400280c1c20b40020784c218509112680381040903900080903a040540c00c0758060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 647463408 1250 647462158 647462161
    0x415060f080709110306090901060f140103150605040b0f1e03090d0503090d120b090408090a061106060f010c080a05040f06020a020d060203221a070c0c05010f0e03030d05 75
    0xc440a00030000945400e02007486081e41460f45944c0300e00004d000e00e48200300040220b062410254031000c001e1141c481c0321400d01c0e0384c903240d40c140403041c808583d011a0400380040803046491b1007020980c0d1468440c0d50034242012100d40158002c0e09100503445820040d43e844a980f8200743c0440d110781200301d41d0760307190a0a040d0b007000c0448405500b8000180248061660086034046048580346002225210141100c1001c1c0040c1c803095904400803105000034042584020b0450303030350580b5050303d915564801120104010308121300c26400c0b43c00407070007618162494805401051400c207129230703041e4454214541c09030341d030400440c0d400603040041c4401c000301c0700000c00781c5001034080b003941e540200300d0031102080028082c1ea400800200c41201081519220100b907403014010084103142c944042103512040e50010b0000d0070005001c64410811581459442809c1c40301480c40c1800554200c031421034a6410f00079100f006c3d200584081018000106042501041c1ca = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 647464658 1250 647463408 647463419
    0x1050f0103120c030c0b070302040b12070e0607020a0e040f0b0c0702012a03141309140a020f041413091109010812070b180f0a1e02180415060f 63
    0x58149140050b090202008804000c03e070031070080384042e904104180d0076940d0710841240213200b00c1c2c0208003501d5000c00c4521408070030b00d0303d0503c540c480d80c0701c5a85900d43e07101000703218058510001d500034a140c009000611900103201e0304540f248075802d5034442d141e91803900c00c41c02150100714484012490005640e88190586501a85040d01080284c003098003034a03020854072024050002d443c1c15030648040480480e01a000340721009844580c07503c103e80081c0280c1108407142d60140c40106612130a684212055040408081d5180501e080701d18410303440e41c040ca941d40140b108080c0701c036420b168000c0034003a900ca0a54150341d100e540341080000c0b101a005500d0981c8852900d40705e80410320102c8003225007040f8007101c3c40c0d490102c120602502045040814000e420020440c060005540100c2600c2111071015034500f0221034403e807486064060350003071900d00d14041c68000312407866001801090009140c4032241180416070340ca80d8170010440c10000c208005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 647465908 1250 647464658 647464673
    0x1a070b0606040303050306010c0c23040f0203070923060307030506130507021b0a08030a020703121e080901020d1d01060503010e0a1101090905041a0604180303020f0c01050f0103 78
    0x91241046504a00b02802c43c1c60081243c0002410a414043d18003c04001d0101010903c4001c050030840c103010039121880c0303e8243d155034000a400391381803181240003608140289d85c0b1034000b680d114500d241c80d0031070080c041d20400d02c1e0740c0c42003a8158115003403074a40c980114480c401e9a240412641094030030710a074182d100103000308062600d03082c84641513021400d80d10100585405d2811a1420000602818101d62003803080344800202d043c078854001c104e14080720300402c0c0724404c1120461003a580381c1840400407000803e0820080c01040c001c2e2841034100844400040c01d2010a0384502c0803141c1c500030182044c00301001000c03052800f4081d01e000f800094009020380c1c004102003550303524540300010861018802c0113080359115210400050040000502c03070381c1094103291106540a07100f48003442103040c00100d950400740240c03022034500303550f00d01152201e0b032002c80081d00410359135820304208100403820401c09000300c034050001110444440e506d5450480c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 647467158 1250 647465908 647465911
    0xf0909051303110d0e0105030c1c0c021501060c151803090509060a24020316060b0411031303030e1e1605040b0904060c0309060e0a050706031a010507020a1a070b 71
    0xe003030f980b0201c00f00b01302c980d00c0540003680400a082c101c0e283d45034121025860700034810010b02c80a04007081101003440ca4110314101903158003500d2851300940740d00380189109005070008282c0149a160004507020b0800e1035482d00e000001840d08030510302e050b401c81078031038143c0c00102850380922031031808864003900801c0844503985c01034038100707001c1c0711950315512140141312000340b42d800044c0280300f220f00410070064807a05020051414070b005090380c01805e4016850042c015040c021942c08403030042080e5541d412000d00030340c1d03085019100d1156400041d003d0b4103850344490108a00e048140c1441c0c101a02043c0300c50b10254017070f0351040d8055072045082c081c041d50561210184950081e07000300380421814140d685c294064401c0d003900520151500350105035000000c50aa01414810360540301d1950b03440004406a51048801070790908801660301040c1d030042c00280310a03807024249145071130340c451200102105480b183d1007003080000b0320904000070303011050b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 647468408 1250 647467158 647467187
    0x3030a0f02090d230607050c0105060a0b03040b131b1406180d06060b0d021b0c0102060a150509090601061211312607150f0909051303 59
    0x3141408042d00010308102103540c3d01800342c045002e0402d030890540c80c00280003061410881d407940c00c0140004015a104d41c5500f031281d440c22011500c68540072012104941d4880d84090a54072207480b5071034591303405004441c0403001000790000281c5101209480614640b100c01d00756807400e40c0c402695801c80c0d032413174814503041140c20001d0072914203001c8421015903540c2c1d0802d100e0f14000008240c1c0b904492108640804c484100d41c00c10f40080028003070281c5107941c40384030300d01150790b60240c040342d460158100c480040c44401c01c0354400648202c1d07603e9080061507882c004503450320001c0d00c540746590021001404010f4001c0c00c40f0000340c9000d03800b0010000c2d400911102801202070010b99100700b101c504031102c2280d541c0e903181c138006000b02c8000e03071340c2c030300f060380c402500003402c5040302041c0b00554640d040040303000c80484614141c80314064003e03210803940f0b1745d101d900c400c00b400111355000c5400d800340d02c1503510800544c4413080303c0030301e5030501030804811001207 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 647469658 1250 647468408 647468411
    0x1b151f050a06050c1006081b04051005090901180b0f13050304061209150b011814060304022806020c040207050c10050d020a021b04090215070813030503030a0f 70
    0x80146403a110280710441d1a40c1c94000d444403040c0403298100b50701c0e12845a80d442c1030410110f01d402c0049102d0314079520406444c40c0d00070982c000d21081d11401c481d85400081c400720104054180360606540c8450481c3c000940400009007100002c4a01d6406803102c80d06101003040641080c80060341142000041c40c40c10115a0b9032241d0b00d1003940542c90800a405a201c1c11203511a0014045250301c00701900d8080494600fa00040014051640c005503500382e0702c104070381808080c0415a000101100500320307a04050003607030303030000d0412a001540618005026181d51008650680280a84942c5107140040081c81e10002100c020300c60391040106800058002640c52112081610562030001d0f140400751424001d4100d1061082c0c00000c2029403164080340040c42403003220004259100361800340b00c111941c0d04d6000350400c0024040d12105141100075102072441348102601d004684005614030000991040700d181c0d01c007109115000c180c0d03004002484245a00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 647470908 1250 647469658 647469721
    0x21140616031a0909030d11030601020703380403030b1504052e0f03051b121003050d0504060e01081b07020402070c0e010602071505040302061b15 64
    0xc0300a900c100c00d0218605041d5182d58a20303840a0014001e44030180080c400180b074a0036141580c2c0b40d0703118601102005261070245408540914180c074081c1d4410783c01801c41909580e43c0304041101a1100520600d0195401c1b000900d0042c220781689071049204400d41080d207406016605201000b0b072064070340d200284200c1800d1030580703040700d2040300d255195041900e001007940c294881c2c80d04080e5180d2049105881d00508100b180700070ba69010480c5a6400d6140e4482a0600316040610706040110915021a0054181e0030010085100781142d81e02da0301e040c41d090741d4440b280040b036030110f010003402e508410594141002030800d03a5035494103030b100511041a079101074224801c045505005d5442d2a4181d600c4254091321004149466030304070040510b09215180c0148611003002c2500400508001d01c00150703038a4450a15007140d0030804150404c60004100c2d05032461000c3c5103010400803c1c110715440000e40c20503044c0110640b03510400382941f10103c40d030011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 647472158 1250 647470908 647470921
    0x60703090305030a111204080306010e0604030c15050408070909060f0203060907120e010510050a0b070506010b18060712031b0815040204080f100c17061306211406 72
    0xe04803680035091113000640001c030140080340a0044201900782c080140081200f04405c4070002d50150409032128003828240d981000458440c40c0001030580d0f280c903008010241040c54200609040c6041203800c2070381300c00c4541e16080c0c007903100818064880d1456024010300b44960743d4181d64444040d4914609800071a003a00d030040c02440411103005007010042e22680e00121001c1d58680c000c1c4514107012003038030307440b200034083c80e8407800c0008030011740f2a0000b011030f00c030580c0c04405001d8070380c0b03020a0554250480c84a92420307000204003500d01340d445800400301944101000d101d1102c01000080442c1d07903c1c212040784910315004407284c07641210307106a2040111000b2800364102c00c000c01e0107070083d607200391854441c000c070807005503902084802000070b03c88020001100104012203d85981e0b030340d6105900307890300100b505404c10103080f41c0b10050b43c0c00f021403000e940b002d0200400c600c032000307040340300c009101e0300d0b04201f60541c40780b40c0000d546004090504004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 647473408 1250 647472158 647472167
    0x4052505061c0213030b04050607020d0f0806060904060314010b040b010c0b060f04021308150417130e01080a06140f06060d09050328020a030219080d0204060f020607030903 76
    0x5200c0056882c04042214403030801a01110f9000140c092100e003960b030750745130607050050262400c69590040b00c0026294030b00c00129504a002d80f40d4414143d07660619040d62008000341484c0c0d04003000f0000780006480303c1c0100001140f007900c02c94048049650700c1d500311004000c10034440d03824800c000004d0b030b070310104042e5130b650401954000f54803500c0024030b0a00d10465005e070854000700d1b40e10800b80b1550000003ca0b121307141a00d0228917003420700340ca0240120b40082c021144800d070042044c030090043c10403403540c056038040058444d1941880302c0426404510507a00c100f461408018040c01803108250041c0c0d48101d50b0308102c4800c02d486940140707078500907440442c68940c20005900003921864100d010b59680d4090002c461443c8206159003895011441c1d070b40c0c44455100050440011390154081c00034a404089000d09023040804241d4420405010f015078002d00d5100800050a4a0f15028690915001c020703042c4107004101d40249885c04e007410300800d070403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 647474658 1250 647473408 647473417
    0x71226070f030f09050106030c03031b0507030b0403020f07090c02071211010305071404090c0e09060108070518041a040c02070b04050114041508011e030206071104140405250506 78
    0x80c10042030702c030f0328140b580e0004c00100341c0107441036007800c00010621060b0f008090540f40250781d000e15000302c0120010400d699900c0080555100e1074081000c03d102c4108160460322920603600702e2501c0da5200d51400c0c040d6085900c5181da039084056034140c04120000041600785140001456551035091404242e0021641803584510006460620850088031031306000281d19403200e0300c0705c3c0e8200042c58010030040214602e00020401843d0000f00c107441800140e449550b9641c0700c41c01182c840e0020400d02d0130704601c1e000c440708565140d02800711100d4070000b1000c00b4020308820031082d81c0141b0224015034210281c01e21025000d20200c4080c1e40d02801c0c08180441d0349541c07942144525401105449103000c410400d05034844146030403902008216000c0c0c10302c1104401000030300f480300071341c2b04208015a40000740303115800c018807980100001303010045074034004155241110200d99a0300f007100024841c8040340c01c0080d0050005040d056131a00b4807010a556205 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 647475908 1250 647474658 647474687
    0x61401050415050909090c010201052503090c0f09050412030501080a0f0503070803130c05121f0e060c0d1802090f040c050301020a030e06010b09210307122607 70
    0xc0e58103402d25a00a030102c0d10b0301c18000e0070524440c41c00702012600c8441d801304460041d403c03c404104010007011981e00c0b1401d0310440c00e031030501c01d400c080d402000c121400321540809101d0001c3c90384003c043c002c00a14055101065911b071a1a101040011951148007403501e80f000501c805000000ca600e03c00350f00c1000354050800074100740b4551302820748018804800001040040c51f02c45849030345192190802c40f00b6961500100b11018100140c212407651213072565540c103c414414910004c2c4c421040010700741c02d00d4200d82c0c01d10404660030f2491000024610b0105041c0b0311818021580315035642c3c0600e00b80764002490b01c4005031034070040c400648082401e0050640c0ca00c801000003c008554409100a0140150090000b102121700801c800060b1110103041107900c140380081402070342402c59002c80c60810403514504080b0710050141200050301580f440b5140c0c1c08a0f260451800c90600c1e89119403444030444000d02220581401080f03a00500031424045 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 647477158 1250 647475908 647475929
    0xd140f0901140d0903030605010f030e03030c130902030406091b08060411061b061b04180908190e12010e4b12040b04030807240f0614010504 62
    0x300c45070b081007441c0c05002c0d0300c40e03009454155000e0800d500f641c1701e0000c4910030b0301d49420800c1c9106068080b28403140303101406030410000545010300d0400141885511002d90800b2140c4419210080380c10445003110041e954000c00403d210188810400c42141485840d0000303042c04070803529a0809040103109020720301840c410f03692850140d4409502d20034000e28204580920f50360f840d8815503844070035410a040b0541b68104401c2204d085d21100e011031507c480010200100505020b038050790190028010940b43c90b01d80c00e2250054036242d0b8400e003007003008904210300e5840c05e09002019070300d003814504060b0400310300301c001554602c412440c4885613807810440008481e1198200f440b094842e481110b000da4119124058260120b03202490f000322071122030310071402021402c00d000c0c0810030001f0341900c000c040c5288190317181d28001da40d044041c0000b0480700c0344501c030181caa001361074070980313144200b0004261044a0040c02c2c3d20100020b0a50301c5a07000700082c29 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 647478408 1250 647477158 647477177
    0x801052b030e0d11040507020f061f03051609062709060f0207030309050606190e091203071d03031602130902030a0308160c08030115110d020d140f0901 67
    0x240c002c1c09881000040900803015076402403510704510501070038502c0c8201c0c90400864040c030710004510040f0315246000702440d031104c1042190002145849110f4031551000c0840003402c2070205500c00c2544a09080c0c100c1e0504c0641c0c002d40b0860303000700c00784580e51690f00c4544440700c410740c070003041ca0b29000540c0c00001d080010150081c0107540c52000d000254407000c01d9490f0b400380d18450f01a81c2034807000d031610802c004a20035004042014041940e10a201203e400f400541d00b1422100840b040c1280c024250030a80d00304883c0400800c500e51180f000b10351144031034901c0403d0860155140002d01c41840f00c62035001c0301c0c007070b00480b14031014540700780c01a070180c100f4540040448441004c9458010b007103000c2210300301c442c000700c004000c403402d0003007210070b464960259400703013542e00300441c1e03070640c03000c84c09c1c55410480c458041c41d03801001845010b2007481141c1c094800050800d8024050342400906911002d00800903100080508001d0b2014030a0074039141c2c601 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 647479658 1250 647478408 647478413
    0xf080708012105191406010503150705042301180806070e0103060801181412030402060a0c17041401110307020909030d020c01021806160b130b01090c0801052b 70
    0x1182c14030507000b08640b041c1c83c4541c2c20301c2e41e504100c0d49030314804c845000d04e610b00000d516869010070b10030103401d40d002a280c8141d4a21a5251981c001d000c0e140c42c0b810195100961841c5803100b40a40c074041c100c502c1611080d503403154280c11089500005403068038501094180e5400307004014508005810000841e187c0c0301e9005100200318400003405000e20411000e1100c01c03114000b10703207020b9494a112051100452a5240b665002e01d049055690b15020710900d54050002c050401050541c0f20000441c0e01c2c800b030b01e000700c105441540f9903080c0000c2c0c4072110907000d96030381400718034001041c041c000002180c10726681aa01c003105a101e00c0c1800f8a180900030049000380d001080b00c81708140c2c1540a403884501e040e80f04103895240301c1c1881480c0c0b252040c0d40c541ca900d00c10345a000b02e582900c015400035082c82141d01800641d4550441e13120083e00700007803442c0c54200d102015540300e0041030140c40c041f107503113000c24503071842c00603035a407081115848000411411001e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 647480908 1250 647479658 647479709
    0xf03030c03020a0f0e03100509032a0c0112020f160c09140c1e0a0315050409030c02121c0309050c1c14070f0b030a060e0c1b1212070f08070801 63
    0x83c000d96141080c01b160400c00c9d80c080d145d40100c800300ca9542011800c00c1c810ba4000c90803082e40d4000341e80502011000c1c0c6004445200c10100d90306606902000451391044180000b0150b0b1b182c2074040b4a0151010f26008407084610781c0800038950404c01910000d0302c103420015000010801c3d030b0b9684680c03003a400101d00e10140c8500c1000107000c80c0066055425410140c104162800c6800300e42d91141d0401003191141e20019000404c41c11380040182072821000d131900b01c0341e20459070085031348200f240c1c0581c1d60400020000380c560942e101000b800b0003000b0a14482101d4401c40e210044007080b08240d019031001d1f0100101c4682400d40d801d0901c400d801a090a0395114840354565412034110303071051f100da180321464044009005a9540405809860000001440d110640b00011101800c510780d10406005680d16043d00280340d07401072a1541098824058070701e410580a440b80d0518901070702030000340410044204d50081415041d103201e01800c207040c0082048403007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 647482014 1106 647480908 647480923
    0x905161706010e13020a050a290a051204030e0306010902040e070306061d01050918011d160305090a050d11301b0a0f03030c03020a0f0e03 61
    0x20740310138040c000b8408150005201c3c000c8141c681001402d440d040768414800094002100a00703025115490707000e05414000c05814081214406095403080202d4424815100343c0010109030281c1d120805c410340203170843c0c416685800701d64000794081d00030000340c82032480c00151090b00ca8002d0f503040d11a103a031028580340300850000c0000400340043d82c1480000e000703800081e1200329040b031140d41c9006800c00e055243c00f00c0000d0458400044421031040b480402c140742d4000e0441c410703207503440d1900140940e1046161414203c4c2c00070000e0180c010f500e00000604d13841a500f10050402c0d20945030002c03032620711031103180b046d0a186603121035110003e54400981c032014102c41c01600340b010b800440450380d00782c10001002c03c2154480c101190200505501d807003140c2580100d810210702d00312102c0c401070141c100c0c42410208101c01d19040d41440c0c4c50500804 = true := by decide +kernel

theorem cover : BRFrame.Cov 647302158 647482014 := by
  have h0 := BRFrame.cov_init 647302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 647302158 ≤ n) (h2 : n < 647482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
