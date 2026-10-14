-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2532
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:59:15.96861+00:00
-- url     : https://prove2.me/submissions/7a41ef18-5998-49ea-a772-89bfdb670472

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 455215827 ≤ n < 455395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 455217077 1250 455215827 455215829
    0x140a1125050639011e0c0e0f040b0d210e06070b1504020c0f1506060301030c17191110020609071205012c0c010302041a070f1506030308060f03030a11010204 69
    0x1070194200320010802540c00621441e4a00b06a076041080005031b85040703403890b610207041c0d940400300d283c0c00b03103d5290030340055400d800d00400c44496085990740d81041041e89400c09c24206072401840c003074080d04100f01207240142035601030324102d280d55038544400b0000385040c000200701203400c0415102c503411f13100725404110442e103581c0078907071100b070f0b4810440c0142043c6a22180c0000e0303e905103502502d040329405084004800e081221056428118410003c80c07482084100c0f6030320a000f0245a04840c0100c07c654500e0b480c4005003d41003940c62426419903105000303104d980c1c600081c0f08006c44034070345540c034140d0034645081800f5142d1035004814405d130041c000601a00550700d0855a541144202d0b00e6440807000150264015441080d41c036100d03103180090a20761100040502c28030500c140b40200070113a4885080c4031001c3c00343c4480c1c51ba05d050030300c00c25070016401074010f00215003210501e003540c00060b41d2485641141030800c500d80029224028094044c0c43c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 455218327 1250 455217077 455217187
    0x109050d0c0306021b0601080316082113022107140607080a02010510091103070c0212060412110c090105010f110105041104110a140a11250506 63
    0x1556414602e5642402c03101076034a40080c5c3c0c00340000000d2801c03070000848004402d81025000c0c003400301d817a10302058028680c0c401405010000c001d00c7c0188610b103161084412810b00c40e041051801804011000140040c030010f2510170003030109000001e42c4021200340c2400701c0c8a8000700d40c0130450900600300300030403642c00401c80c221000d070103400452044294141d03000c403007551004c604042e99032000002c0920328080005c610000d20440322422400d001400149d6019075003031540b440c00004a0741516013501c00e80035a052140d0100e42e02000914400060203071091090000303481810610495040c4088010001b00d500d025000002c103d02200c4000c21103860a428900c1074809960081849245401b1415020012000a03209442c180c2c0e41d0303810740400c6c0158000c106910905900d0107109074900c1075225802c04000b41d114030083d031006200103440d43c2c03282005c400f141d0341205208000c1440f5468130285001010ba05400d148101d2442d000318821034110001e43c411040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 455219577 1250 455218327 455218331
    0xa050d1d121e070506090c060a120209120307120324120203010b1002210a1d01051603030902120607120b041b02010509060708010b0a11030d090f120503060109050d0c0306 75
    0x500500001181c017601c582202e10030b8a00c00b103c4c0c80c00700400c034429501050040760000710400000d50107680900f0b01081c016003400c280011807161645540c1010784201e840c1403445600c4c441c180e40c136000d20145115007151007000004d40c0d12143c150340005010f40354200d041800e0b514155a42500300448240001d001082540520701e0000d480d0b565161003000c035406014031107207000c8025421144070190541e1000743c0f5114181038800c1800d440c0e4002c0f41007120078045100202c4200c21a180c010344a500c0000316601c403841448030041949d0035803485500060104a003031500a841c4114100070100001810b080a800040c024200091451102e00d16050710110761178055020b103001e00322141c11961540d440e04411600381c0001d01030400c03025418055400017a01505115603165403c800f920304142a030003020048a10350b0005a80c0420340812140c1800144c110b00003c104462824078038510313002002814502d000d01c5004d0144400b8507180043c0040e40c106540655031007101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 455220827 1250 455219577 455219587
    0xc060b040f0e07060f180605160501050c1b07060507290c0711030606030c3109030908070308070b0c0d0e010509010605010206090d110703080a050d1d121e 68
    0x2456a031454940070352004501e80e9844e0201c101d00030b02040a9841e0106c241c403007400c1c1009011203803038000c00c210b51000060103100c2000144280292446040c031402034580b034802c000c3c8110300200344414080d2554006207000c3c032000da03020080f540030640002d01e0325444001000b0180c0585440c0041400c3d12030003c0502521101030801044000e00580c03503000346c0c00303c0d44201620b035403042d02c0c4140d250f8090a001c035400d0401400704440c81942d440c0209480d032040024001c40d03041d080340340450980d039138003070700405401c1941e58002d04000402000c00b14107580d18071049115011010303144505000001c0c002250510407940004800041400314415a0308000e000c0c000a545450342c9508016000c0346551000402c20310850003a001440e0404820f603069504401428680742180682c10001c404254650018402082c2994a20b0741d602125015507080700ca504040300c00515204440b240c20300b1001680021b50a0480c1005d5602c580c1c0c100c1e0303000441c513140a0340c1100307400499 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 455222077 1250 455220827 455220851
    0x9030908070e01090e160311030a0204060b0306091e0a1509020a0c1104090f0b0a110a050c010510050f010311040f0807170a020108010e100e191109010c060b040f 71
    0x10403504840c1300c2c2400b840b451903580d54294485500308020809400840f1081000c21100745420311141d0024054428014458000c50251005608040040000007081c4481420a4030f8500d502602c5c03041043c07140044444a080d444d00054042ca0303c45480390001d071249650710f500d4100500e100742086540c4c48258802422003403050a055034000e421920010031400d280c0540f5001a5008000074140e0038595203a800b40b0002038801413100741d41d681c00900700c00d10940208251051034a42d251213075031b4070500c0d60070741d840201912810100c0042c00c100b40d031a0200c5ca0a0724000c2400c0110b0400034452642d540303030050385d20244504803c0d1100050048011804400703541190728403003d81d002c2414811342d200705501000f40040e40e0407004110804030380202c69081401c981d00d100c44036540f10005808204c054a106035030120008812076140d580b03100e83c1410110003a000780c100008800043c11103100d030080581502d4840c80c031027001d039850340d110403111001c9482c1080f410134040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 455223327 1250 455222077 455222099
    0x30d0c0e01110303101211090108101a0a050103090615060e030c0907140d060503010c030b310c020f010608030306150403080405060d0b030d030e0d0504080c01030903090807 76
    0x10355041c003180118080c072140340408001c8a214440020070a40c1d01440e10b01240040c1d002100c0690303a40582c0d420046041c0e490f201d10b940240b14420041180488100c4200c00711410420001c0010f0f800c02d40e504082d803614000c88040302c2e4242000101c0b1001403c0160190031031101281c4100010100401c500342c100080582c3c0c00c906508943c511031140051050b80e0320261804d60105594a030045070f0440d4040c0107000c403104035040402c1d40c5556002103407e48034400350b1440425203c0d024001203040c018018015110b05070482e0000c0e4a1003210320701d5408001e20405001a10b585840312468003c0060381c20041c2d14500820840783e56500f229109d4105407a268490303030b444071f52541c040071400280c0f400c0d41c1d0071419483c94180b400041000c2e6a00c280568400b01d900c0700e070300e40010394040c0f00964501c202130b01c001c070f03d520080d00c2035801c2800b01c40c40078051160901050061010014038142c0084007803e0006000505040a44041d0300c59401000c1038442ca000200b4036000318 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 455224577 1250 455223327 455223347
    0xd17161b05070b0c0d020102131202010c060f060510050304021f0e030a050a030801050a0b1204020406030212010501090b010f0c02040e120a031401170c15040801020703020f1203130b0702030d0c 85
    0x102a6489007a0a480c200c0c00d134401c00c0c1d038140d085049c42009000310003031180401410b6105042500004c0700303d40e0b82e80146c4000d50b85010300c03650344420800c101c1c1080f01c0d0f44004940107191092452a090f070016051800c00381080a41c040d40c46610420240903404d800c40c84035009080302d101c1007441c904a40d40e01420a0111b0000e64100000207180c180449000142c0784214001400c02110107440702c8144002842a13a01c82d440382400005070301c59404000051401c1000401d407581000a240c003620200c0d2500341c104010322a407451110f0384080a00400d9504030f802140350709140d00c50518007002e5002040c0e44040000d0b09a400c1c4e90154400b90012204001c80c10107030baa115000700a09602c0742c80340000d03820403800c0302401d1400c00800b0f04140340d4400c00605042e00c900843d800c903044210704034056840415581d0f00c0c0c43c0e0402c6880d015205080c0418614580320084d90280384d40e4030317001040c0700037000125a50718001c0c0190b82c883c00641d0350802038003281400082c041041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 455225827 1250 455224577 455224597
    0xf0a0501021b060405061305030d0e0a0201080c03060109030f0c1a25030c0312090501020d0222050a060f030209180609071722020901080d17161b05070b 67
    0x300e001006803a001c0f850700d1003180c10601400c01582c4001c000544442c560b00121521f0004000210310a01c482c804c2e03120311b041d104010100ca02c554800940200e10141142c5140c01052007042035503030b40300303000e84180c9500c038144400f00030b01072402c62007030f6040d074008464100e920001801c0f05010030b4003810140d00d8031010403461041e0b80c2410b4401c17502114014000035844100c17000401d002c0c00550380c000084030b0000640301c2450300c0f5a42240c00100303076115800d400184d07541c1c5030425401d202e218500005d18901d84540307010b00041010049206000a0000140f4540743c000c3c004e505071001c0c07040140c101c0f1071843d10300d0408840460201c0329548543d0b0340b24003040b50b80f40300d00e0744032100e2047c090040000703443d6801c241d0407101c03480132600c0710741506406020060711b0703d000e07190003480c00703000403c03004041103030250900003c0000c00c003299440724100700186610b085a0600107139039060130241c9031000c1100b41c0501101d200081c1c941e101e20703440000d4803c5090002e21140b26 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 455227077 1250 455225827 455225857
    0x703110705120705120421020d0b010b0c010b01080108070909020a0e0f0103120302071109060a0902130905011e092a09050f0a0635072c01050d0504050f0a050102 71
    0x10301a59041d11b00032400b4100328210100700c4841540c02031b09007240c82500040c004d014030740b200d036200c1e420708100760002041200049400d4042e03034424000c058503121300b403d03c51199030411200503074400080c840c0055680c1c68040c601e003903498461a080241040c50701e00c030041d10f4880243c4058820a200840d0043c040080c400070301071080c800c0d24034540c0d00ca060306401c04103900421a426801503e204d600c45155500010808603500c01085000842060034030054a0800030b90101c420580c800c1e1540101141100c00d07005035810000241d500c03680000840740038017010840304620300a08a88281e0791001d45050325078204015504851084490140400310340040c440402c180340301b0b0b071022680b195400e4020400c80942d03a5007000c107a0303a01c0010401400403440e40898181c030b03540045102c41c25052840b081c0d80001c80d480050400a00c401c20a6080000b441417161820b45030344a40d440c0003040411000344109005528010100c8050600504095000354002e030780003c2c0400f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 455228327 1250 455227077 455227093
    0x12111070501020405100c08030612010b180a0c0203030402150a050702061204231203090a0f030c110d030f0810030212030d1a0303070201051612080103030f03050f0703110705120705 80
    0xc0c8140024555554030182c2300f410340e11480248041001c000c42040300f02d549230000d40d0540e441d11110940c45100c1c03181d24210700d0608410035411a1101c600007011500104104000750303c40070b65460134019190f0090b1b0351281c030f0400407503030350107010390080d800440000d88070071075540000142e01a80c060380040d042e080030a44001c070444100d2200c40555080f20341d0703582181d0076510245910080220030382c0d00030720080d59000e0b00d85408040450214040011000600c415007001c01d08244007510000031500082d00c025240060041d400405c011440000a91144210407890019540a0b090001400f00c2025060b00c136000100490303105460300903e00303055262140c00310403401d4060091454a0041d40045135940e1140641000d580b58040300003000a01d001c1f0795000a01b0702d543c0e40c0100f5411850024a622040b80c44c240030141800188110400f85095581d008400c0e8140000c034003041c4040721581d40151600641140a40c035092580d000da0f510050038454031800568400e2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 455229577 1250 455228327 455228359
    0x2012304050c0d170702060d06090e0d03141602030d060305010b011202040302060d0203040c030c0305060403080601030902100e0127050a1d0f0a0605040c02010f050105040b012111070501020405 85
    0x21083d00050b00d40d40d01d1034101804500e07041d0003131001900240201e0b10388443c85c0401700940c1e00c141d210301022683c8440d00c50503c03405124000d00c00d8083e02c2c06004080c1c40c1000b40840c240c0c00742c01401c0b010441000945854000c204541d180480004144841070380c3c0e081041c001c1a10000203408900a621050100030051007100c043d207900a29a606000c2e512507003100a400c018004c0300c011805a0000c400300e808984040004c0d442140101068039041c41e00804132031000e044141410309201e01c2c100142e841100c1107101d4441440c101100c2e1580d980120f80c100074080004008541c3d002d00c40d80000701454406003511020788054103007c1da641e64004110390305203984140300c4024408200a21843c44540e070708071136110b84c00310303078a5201e100203000c40e030440d0070620160b950b80484400c030301503602400d0b004250844041298204280001c0c3c504e070520510410031407101c49038001142a241c2c40703001200c440124154955038185040c90003948135006680c880c0543c071201c81c210f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 455230827 1250 455229577 455229589
    0x20105010305210403060b010c081803160e13230c030f0622030203211e060a032d080403060e01050105061603020f0102030709052704020105070302012304050c 70
    0x1072042401c10740f901c0c0a02d1512448000d1401014031810400c07842c81c844085188039020700a000320011404a030014928201860650754900c44404009a40803c000c4080000a0190720550032902241d444400c3d16006200d402540c03c2781650b6102012080c0d01c4010010f000d415103c0e0503001c43e80145226201280c0d20310003140d45c40c040d02806251b581c40d940380c0b551344009591103801160700702500c3c501486949003aa0002c05000303e0b441c81040801c48001120514043c89034910301703010300f88003021035400c1c4083d0002400c150a088508400803a040b125040c081180e1131050040d00340614001605074024441965840e04089090941d0701d8188112030489000420780741c40e0811008001d1101c51000c0f105406500038085440459042800210b10a5031581c0d1001015824041041a1200500222910402c0c01003170413100c131301c041c080c0a400580909003e621030280c0d01e8128007402400d000ca004208240384900003801482ca2204c0c0640c1c46030b0107031280c14071240f040c841 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 455232077 1250 455230827 455230873
    0x130512031201050906030d20010f050f1308092209030305091e150403050d1a150906041a04080316030f0c1110050f0c03040905090303040b04020609060c010507020105010305 76
    0x2a060300700007d2590203c0c001e501065036421021010300c4a940f9115140d821952038210074918562140200300c0511803601a07903032b2140c040c41c13141103009155200c921581c090a4121405641c9417000c21000d44401d01107202510483e15051000c0d80380c0746002005881c066404024a00c41c40744540c103040203022128445441c2d050080c442801c400f2520381003128007510603420700c00201715200311010640100b40c1101800d00324400c622503c50103000723081e148101500407220050003c040c060391080122422510003d0160070b900d1401609894248259800743e029440001445039100e126401004404d0f4003075120031140f91822581550318101c0660f000b0484400e0502c010030501d0b0a004078900b0100c00e184c05400d096000e20403441780d030707c003444101065001080030884040e80f801a00e50003009100610b085040660741c0c20418080130b413000344580310214040e021616200c1c10b580b0360503a2040248410708209001900818007800152594061540c120381c4001501606607 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 455233327 1250 455232077 455232079
    0x60f060f03120507020609030105040f0201260c030a06080a03020d03110a0c0b070e03010c0e0312090307090207020402090411070b1008151e0f0106080109060b04060302130512031201050906 83
    0x1080095a1000c103c03000d602420b0100e034051001d0084640c41d803024443c0e03921651080c60044000c050600024044c15001d410f29402c891000342d11000c6427061000e4580c00800080b60b06803251205808140608040c0e000385502c0c0c851005004241980003a0204c0700702c245460400c1000c0360741c1c140140a00c02c41424102081581c0180e00000350b5180c14581c0c031105d1031508000c3ea124140000303080da11a0fa40c820001081113205090314a000c2c451107402ca0301d00c200592400003000d0100c0d4580d0414400d002000e80e0105520303080d0f4559030115500c281d0018001c00004a244403002c0710703508800816110f06070014000b036100790306641948195001c460041c047c07000b078030340d54000c006002448068100074003804551030b130003800d0300031303000d1504909003207030381d60601500500c0b2103c1680001040d6090960400982c640d150407501541d80d9031402590b0b9060303000c0446281682070380041d40115240300d18001c103410200c0034001e01015103c00c007070586d80e10300401c00c3c042001c0d1116 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 455234577 1250 455233327 455233343
    0x60905010e09070e01110610080f0613021903051e010b18010b1602090412020d0e0603010308030c12010603150e040209010b070201020709020d0911060715020306120307060f060f03 79
    0x21402c0f85000b881c126240400c14034109000a030046c501c5424620103460b50b0007050640d08041c402e40000b03101c250b81d662501d0b8000c2c6120710b44000c80c801c03030748200f660180c003468691403030b440619001e04844000d160050121650308042650300070180e1030114003216070794a0503090320041c2c0790913807420b411041340f1112451140d0800b45503e14617400303400c100c0d80720715902c601000140c44250b0041d102c0c81c06070581600402c48030b130000e4200761325904c0c2c030410098610035481c45c82d92868166810340340c204130155269030f200c0c03021041902c9540d401c99400030303410000045e030b5a4950028000d1400520f0240011665052408500750342580e0080d446805800140b0000c0c2c04400a01900350052040302d42076a9916a800200c1c1c1c04100b48103c00341c6c030780c4202014480030001c00441502c06440c1c0c5440e29286840c0ca070304040c0610300b01580741d900000804c500340d494094400018415509513503554915182103002494800c030408000e60a20384d00003255030300e0205410441340c01c1002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 455235827 1250 455234577 455234581
    0x601141212130513020d1104030c0e0c22050301060f080c06160803040317130f0615080f1b0105090a1a28140a17040213020c07060905010e09 62
    0xc11110703500192050028912444400201c0d0750792512001103d600c44100140d172aa1082030707003000d40340c202c044010380540c00c200400000344195500c00885c1c40f4002c3c1e11a65442c3c450880c4241d2007290300c1c01001d00d840f0f4200252020b54400c01d403088601c201d00810401c1e6035040304002809082c818400c41d50010310b4000d41d141001c40c01000b520740c0c5601c080c02513419503550740380c0070703003040c0c800350b00103007007642c09000c070740d00104c1d12503007160a210515604039919555031044100d0000001c201075140c28403252031840036101c0ba0f014101352000d4480c1da1484d88615696603006c065000b109160341c0354015180c0d4010401c0320b90020700500b441407450b0400d0090502039109543c088e0362013030100000104814401c260110070103d031201034600b4445120f00414160000070564411801085001d401c1508200c1010302240b080c2582e681c2d80d0354600000d14020384c22a0f07803114040c000502080400e0020501034140c030750701d40710884201d440c3d000459484144442842d00124581c1c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 455237077 1250 455235827 455235853
    0xe01020c28150e030c220b0901090c09120b01030308090c03010218030d031103160512040302010605010807020304030b0408250c05100c05030712020a060c0206011412 73
    0x41107008440300e0410003031108810003106005100c05074460001182000c03211603160f03a000da0540c100001c101c0051544a0300000002d4914080d5140d02d0016000c080c0c5100c0728480f142c0107528804d1000b005282d541da51b03140c01002400c24035100b00d00254403100041030340b18070300e20034030400c2d500306a02a0f00340c0c0c04c41c3d03401d40c0c0594028200c800750380718030f14800c4443d650034001050300c40c05040c802405c01d107030700c0245032800ca000c00f45d140a160030701300740c04d00450707041c01501d07404410300b620f80d0240c0d900101c0c15100ca1203071590b01c0f06c28103002c0701003006250301500000c003140c10a0b82c0313140f42580c070303000100d80740d0040307020080508207a03401060121b00d88002802e0b420b58a0000c075959103008401c0d8040c060b01c101d00845003000c619404110900d41482590304c0760803981403841c031888240d614036403280f040c248010016001e4101703100c2aa8070800c503161040782d000400700b1000c2031315035001c0c5d55120244a64503c0c8200b0301a03825043c1400100c510781000c04400510540c0c100c80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 455238327 1250 455237077 455237089
    0x4030b0408092805011e0e100302040306021611030f0a0f03140304050d02060c09220b0a08100f0b03030304030311131e1d0703020901030207020904080a0f0e01020c 72
    0x803451544892958611119010150303508031500442c04921aa804c3c60710001508000002d003603032100303180314000024a40d402c140c030b144285c8070031100e08080c2541d45505800030f0107a5040a0400c52020450120455403810075203e990b004006106039420140d081503a80d0b00301c1b4a070125107401008091001542d540c040d41902071181c2800d6120345070105da000c44641040b1016512a80400b83e44500503805001d4a41c01120f40540180f40215044c00304800c04246851562200c2030800c8004c800c03403c66000d94084c032001002e2140060707030341d0501942c50a00d601043c3c406454002104058ad00c035200e4102d044034054051419580e030360f2000d47c02000c1d011b00c10983d0703d50400000160810201c80e800281c40c242040b842c5891b040d15548007840402d410080c01200c00d01e0408003c0d099a1250b241e2040303203850050303640c05102004901900502c2c10080d009608607091000b0010100094020f1002c9070740e0301405008018012500d040c150001c01c2d01682003d03005e000c5500b094 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 455239577 1250 455238327 455238337
    0x70605071401020f030c070209150f090c0d060f0305010b0a0e060405091002030903120c040e01030b130c060305070215151017040501050115090303360e0a06080304030b0408 76
    0xd040010b091002541413481140d00880306c114440d1000a05041117140c201c00c00c50300324002e8440d00d0a0b400c24000410340d0700c0362500395540715410074000620400f494004580814140804c2809100e0b518131441c40f8402050208450315402c000200f0030301d0030480d031150100c0d100024023182c241c40c1c000030700c8000c1101070030107a06030003860003604d100030aa000450040088200466035149045540000b44c000549040807944040000b04903445ca40c0346542d054a4005999608644403c2805229000e816000801e1341c00c06000000718a9011781c0158482c82254095031021000580105d151741d40486170b0110203054841c0704d1a40e4280003107203034009038541c2881041d200a4072441c164804086800b124030760344400040c00b1b40c5000034016400a091410300040705400d540d0081c004200c1e40090640c4001c20401591051014440c407070b10854404c01404002d94907989001c43c0344404840c51205030b81482400078500c40000207c0d8112a00081c481c0c1480e12142d0701e42080360300c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 455240827 1250 455239577 455239613
    0x806190905030c060c03060f030604052d0a1211060709060e0d020901140f091303080709180c09050a030b01050d0809030d03050402010806010c030e0d170a020a060b0307060507 77
    0x2c288210801503508005440c0207140e070614503a1245040004c2001480316124894020340050060000007400080e02ca18a54036550401845004140f6407520394800b580c901981d40c460385d0101c1e4140f00044000c20304109180c1e035004a4030024140c0c2c15075500c0c007030354110005403070700204004262003081107010b04500244100181c1305203070006441202d00707070403a41c8018881c81038400131703281408403070340014415141c032142407820a450041c00c50450901506021003030300050303032080c45080103402030141021101040215a40303d83c004003500e41c032600100f00c0380140412a8640f8134580b03c1140d1344544900020303820001800104c00300710004607100d85051040301d50030b98081c410290182d00c1d643d00001d0a28050000502c0d0400141005040c4032100b0810301c0841c1d80407100b18480082540c18010100c2c281c90300300a044030041d1000107032403021620841d02940800d90b4a0b205000b010140301036400761040589514a500c203000204038200500301c0090318540c215640e00302c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 455242077 1250 455240827 455240833
    0xa0302100c1412090405061c0807020102031b0606040501080304120305090621040c09181113020c010b03060a02030108070608070216090f150f090b0a121a010806190905 74
    0x105402d42071401548481110040a001c01c00c06075604041c829560b00c44021a56804c411602618041c8022a181005008031100146003401c1da40200b080351404030707504287d84104031030103070070b0354450300c090700c404d0b1165062500001e0402400025a42070341e0a03009000000e440e01c0da002d49440c0e100502d0a07800c0807040c0500200d00340e103455130401030710707070f020078102c0d42d207814039046e12034030400d8202136100362500c4907a090b000c500e01054140154403070743e04d048400c2c803c000503149040c44008070300301500000310400b12003019040060405001e07011111143c03540382c00802603000034090904190712107035007002850302c900300740b5821051600640b480c4034601000741010b46456000060801d4603016415815001803041c840381c030390400050a070303e41c102480034861880f00c1c4114900a40c0ba8000c4008550360743e40d42c41e006045c48040a0121040c901d09940186050500780ca43e145100d000090a081c1c04079a0034400c42150f440c8100580c00740a8810041c1007104090343d940c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 455243327 1250 455242077 455242103
    0x50105030c040e0c06040306050f0703060602030a030b010c0b041b0e0f130804030501020301090623090c03072006012103090323011a190e0417090604030809030c0a0302100c 76
    0x9105d000003000918000d00000c80c09203409140540702035409800c65041520b0a401040710b10340c08801c0da0342654003444c010035140b02840048506200501015001c1c4200300180010007545404109065401c614074001542e500c200d405c40d180d500f111202c0040c0030300b80c00518048824803809a03131318818600e0704d050580703c0e1500c90032604243c100c2c2c2c40c4260384502c20b000c5400040c1e1841d28040c01c110f2000721305007042c0d000c50442d42014004000c00e440100105a005009203880c214500018200388070002e42c4040c02e0b40e40b42d6003885820103000c0140c40060300d400c01d00c0e40c0010042c0d0551654200140741d0340e551407440700750701c0042c8949540c0c03105500180e40203028001d901c688202c07142d102300d4488010460441c2e03141c6200b141c00b056007241000360b460002000d9034081d8000c2a640d000f111a84244020fa10801703d403075030300c4100064080b08100070301003e820920380030342c05c0742c10184602c0140720102420380006580b000c50000800603561241d10300b8480c0e14441c6c000310b0448 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 455244577 1250 455243327 455243329
    0xf07140a03030923030a1d19030b060f03030a05071704090e151b0705010914071701051b0703030617070501120513021e0a030303020319050105030c040e0c 68
    0xd400c48411400251100801d005000c02d000e040304038683c60300340300d400988a422a0603030700d10a00b2103510031700004000e58400c071040501000694940506084604a0b00070741031980355804d800210303454100c11011a1080c20000c42c6014110000307001186499101030007a5526008400c0840e50740d02d110303903201c0d00a00406e000d031004102c8082c0109103100c400c051a401c0c400030b1410720f45a161010700b00701020310881d480059290448440650350002403c010b805000000c1c0082c241400940491743d54800008081040f14903c066241c480d4944c03100300c0e0b00b6140d041d00d076410003000c55050000c80c0b9004100600d0103a1203424001451552050075204601001d4581c0348140c02c104400c01c00b650f0071040049990315082810801e81c6880380c107450349080b5141004e8000e9220071010403082c40072560701588803100411a03804940c1c0d9140080c00b96104440c1080d09080380b84513164502c0907030042c00e058402c024068141091120284001440c1454803108140324544c98a040c0e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 455245827 1250 455244577 455244583
    0xf020f010b060f161a06041a0109090e070504091103060106020c031b011205190e01020403020d1704170d090b0c1506060d0912021627020405060c0a0b06150f0714 71
    0x104085400d14500c5c9444d105080000700c4945a0070000c030f028900b8180301c55070b0f0340000540180d8441c80d2000540c1c006182c10035103032850a400c80f90300145880d0324001800600c4811070750520007141268000d030b0300c501c012030b21303101b6900500341c242d40700c00c2ca441900d0092510b0848881d9061420202c200314100340002618401d40e2900195080c800c3d00c052000c0e01801004201c4050a00a519141c51540403c00c820401003000c1d1805c1c2d400020121020100d400b110010110384400f0600e0080705003200340c452000385124408150a40300000e1007100320815a81c0110281000c0c0003145441030b20342030004001011a0303442034003003203518060603031031042c4003d0900883c40f40030048232a01c4080e2030b05d40803a020300c200c558440020003405001d10b200e8407404030707141d0303070b001da55595941c255020380100c1c0c0146520500c00701d150101c443c0c0014241c0301d0340d405a0f0240c004da803244003d1108252101c20030001481040203500a01d03034802d40140000e80c410104845008036000c0d2082c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 455247077 1250 455245827 455245853
    0x509250f0e0d060c02012f0706020f0c0105010f0f240320040f0e01030213020f0415020604050d031104140604030f0b010f0902031e0411030303070f020f010b060f16 72
    0xb039200d80d644c0b074501c50b0a0f424401c1105c1c0740b40c482404090002021044601d5200d4100014a26100014075004100064041d550a034864903c80c2d6101c010400801d4042c6c202401542014440984001440410403000c0c3e402c550a80701d440c00440c020304e02c080609001c0da000b120078142c5070f02c8012082240c4141c0c85c10b201e60000041d946650900081440c0c00015038003d12842c1c0e404401030026a844c0b050686080c91035036801661105040d03803411450141c3d611100d40c2c4c601d038980810f8956004200365114900c18000d8034541d07101c00c0d00580450301d01c00640b01d4103807801d00062220212241009103101c400401c1c1a0519940c0d56489690f180c0f044000c490302c500340030041000710050201d0310040c2c208200258118079001c480e40345101100d40154501c8610040400c05100015201454213100941920342c0e0703140c030703a00103030580a982189100511030181413200703481040c4031342d4802000040c901881c0020180d010841508140314221415043d1100d240c00a502c81c0c0c0106 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 455248327 1250 455247077 455247083
    0x904060e0c2d040b0108220203030415030c181401170c0712030905030d0908120a0e0f150c1b0102160204060816030b07020102160c0509250f0e0d 64
    0x41401ea4541c20010700168411000d400f880c01d050900c405aa04a43c1c1142e00c0024480c85591401e4100d0740011010710400717020750180000200440c040303c1240c0c0d02c0000035030a8400b448107082c2c40b42d0071140030502d620010300f144004003060004902c50845a60307950f03814500750313005102401c8070300c098420035513104c142c940000900b1790401c1b0581580740c01880700c03404c04006801a1791030301526441078035420f49409a984600004000c0a1400d50b046142d0102044407070303103030886101004211004502d00903100b55403003146101d20009407001e0080114603003d82d0340c1c4410401c076901c1e80043c0d60711480c480090f402804884000d00c09050204101e00d010902c10209005002c200c901039000020681c01110b00d04409072482606002202c0e0b01c0074488416540d13440c012802400780081054908044104280c2031002c103034404410355000300c958007881d4584805428420500701e40704481d4140000014502600990010740b001c6d00394100810751806240016456950b082d03021 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 455249577 1250 455248327 455248369
    0x43051513050f13021b07062606060d0c030b01090b070312270c050a1a0319022712010903080c0903010914010e0f030a050d050405010f050c0a14090904060e0c 69
    0x14100d20030400c20100208400c1c28202e003816080c2040070000c00310480c0780c14031010303c403010640580b02c420803a2001d00bc00030040010300148403000f0041d00f003c0641c1c5c3c0c0061070307041001c43c0c0721542c5003c4500260303040d10354041d420408640080580300c41494074021094417001d5102c00951021544000c0340301e901c1eaa0542ea042000f00000e141894108100c2410b0545000d101d0b12170030000c0320340000170003201e9400100c010403120080d10610800c2d015914098054410f000c81021500c402c1007000c40b6400081e130b4000011703500720344004002500003038035000451546a6804000c10021501500104403018151a4209950180c50b07000c07400340c1d5121401c1940c01c04c03e0001c07244001c290005107280000c2c40c0300080c401d0240e4820101d00ca6500d0000c08c0420409500c1041141d00003001406146805403070041550080c2130041e010840c030441e900e807000c0c0302070103c82803120000c1c04014a922207481d500e00030012410507141e14440c40c0003000196544001c4001502801d0303580c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 455250827 1250 455249577 455249617
    0x80718140f0409061b270b031003050d050d0f09020603010314010212190e010e1c03020c070303020705090708040209190e0a0c0f140343051513050f1302 67
    0x101850041c076071100782001c04000b540561011b40d60b841e412035a4146c01180ca9440340402c40100d10b00d0307544024002e108240c05042c456030044040c0c600148034541c100034041c0442207010a8078041c00e4000d5029800300010300000c5c1c01e2202c41c00214181070001800c0200c071814040d10690160340e20f61000c080c0c1500030311000290b0290086010204000780560125045c40c550389074000c1030024071181c058400c249019210741d05550742c855044045603040c5c0e54905019440e15290702502e8024106c8034000b444845c01500c220f03000d0303580682040429510031403100c1c001c0b00101c145034846030302c5011815a011040001028460161500700341540c601042d030444402182e100d80516804c00048041654010402c401c0109d496121a0081e41184d40c2240d1600c0200340c81201306040c541c15140808c10541c2c048060f14401c0c0c8122200030320180e90500c2e0b900aa91001c040c00e42c42010038491420844c042d5010700c00043d04029a1044604043c030981c0c1000248040d200d07107230f00b1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 455252077 1250 455250827 455250881
    0x8211207020d090e15150421140c030706080603101b08010f0803180a0308030709050a0501020a0506040807031110061e2616080f010c080601020a11130c080718140f040906 75
    0x803270194442020b40100b4030304d40b030000441c0d00c540c11485004240081840010540d44003448911604040031200304010b54090744912401c01402c00c00b6030004a042001013904069840ca80c0d0580f120007006500348140c00c0020381940c98440c8007140c00403002140040080c540c00050b5000390708a4442500c2241824280035140003940d000302d04540c071185030310300400d1001c9500741c0c2142e0444046540d80350305007029035411003040710a100e948100405800d805609034005803d1300ca079600643c0f80403102d030342503403000e64660040c28214103610511802150040c200102c1c0301180d8401d035448266445080c810f282031682c0502e8858000c600b0b4040c20344400c5c451041c50104c241001c030709034105400000d5580e03001c4035004020042403019645070b9903400700d8808805d1210001841303a0300b54041c0003010444150340f030174040f4202000d400060301001c980c480641d004038144214180034001003010221640c02c0403070b0442c3d501d800c9500411404d004000202014042041c42d44607074007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 455253327 1250 455252077 455252093
    0x31a16030b0105040e10030506040b0f09070501090e04030905120309010e04060608010b0c0709021303030e0306060121020702060d2408211207020d090e15150421 71
    0x1846a0042500c0c111441c1196a0001c041d24240c0d04040310904207541d41c00d00c82082220917400c050300038072030b802c100020002c0d851503440c4241e43d51124419542c560420303890340c90342c2c18010107000c243e0050080c007000192801d0564094000d14290031038503900c00c04180900009011014290000a50031546503002002901221002d890800c92140342680c010b1425406018003009030f0710002d101001d00360700f0400c00018000d459011136403040c2c8000d42020700c030403510086001c03801540007501585400319071070b4401c07071040e15805411511040d40b160b551850014111881e6400c1c4202c00240e116180501180c1860080020742c1c912540110101e00074903801e0603410001c0c1103401e203d0548041024201104203503103050361710144509190803409a0400e1010500d100310070041d410358005507201c85541c203030300c5031180c564680841609841c400c45911b0425601c1e10100415810f01103400584034491300b00d99806d1689480701a15000d07074031310323640c0d4031140c80c2c010103002c3c81815 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 455254577 1250 455253327 455253361
    0x150e070812040e1b0c07060503060405090d121d0703060c020c060301030c030b10030b040b01030c1703120c1b0d09050a060804150b0303070501141305120310031a 71
    0x2a070320441c00c043c5000c00d0141d5641000b03026442d6603205080b010b95034961107064030002c010400541d10403a441d9000100f054104442040c486c60800f00490900c843c0031a000e050410b466454000340d449421540001c1c00704203030300b82c7c0344c00b150882900c4405010b0001e0030140d40709071404500d10f03182c0c0c24000c0c82c100031546501c0c460b032400c000410020398085004421070f0b03402042d8149580e00d04103010403c4241e6400541446624800c0000b04160f4a10040c1600c1c820080400301d40d03110003a04001c2c6907110555480c961081003525511040d05c1826a407024011000514001e0b908807126034050f40500100132560110b0b00e84000550001b07c0d07030018080030340315042503600e060300003030444002400142248015001d1580b550300150000300003600081c007180d541c1c80340d503e00b548c001d01580c510f82810800e81004140c280c020301d0407050026411800800c4a00f688000300602c59102038000881c450b199000080010180071001024100d4891303900030078500041150343c803000c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 455255827 1250 455254577 455254603
    0x309100c111203030f1b190206010e1e060f04020a020a05151608060102070807080c040f090b0402090a090204050103060501080d2307031103030907051e030c0d150e0708 74
    0x840100e0610301e0600000344c0343c1c000560703040341c407043c1c40c0c1c03281c016914116107015582440e400903000c540c006840d1507408550035154200c0e002c582c0da03680305110b10f04042d6005e00b18018002410310840c4034a000541e0845002172070200f51a0b507800005013240e000d03224240140c0c0048100c001844414400010311131100044600149041002e030705400c0c42c400420414000103601090240e442008400090940c05044818143c0c55403001d9a41d210200155882581005e480f9008003a0742e0042100300c03507000140801c580c403140d082117120b0700d004080078002942e40358000003581c0d5034002e003402540a010005000c0d41401c804608181c1d20302c030781070140a149142801c51840070030400703102602509030580c03541c503241f80480384003c0c01d05641c038080c4004800e011002402103910300403507104551240c000c2c44c1c607000c105942c4810041c041c0c0e054000c40512051030800704480f1100e01d204200440340100031401406c1100e81c00d0b18a40d461b603020000a20007000c1c1000580340d0008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 455257077 1250 455255827 455255839
    0x30d0906050d0e0f060106020102030901151401050a170c120a02070201020c0f0d0605040804080c01020a0503091c0602070f0201030b1e3a060609021213050309100c11 73
    0x10034100040c00700c0c4282c0d14446060703541d44150056010007071000d60001e040300429a0b4155a41d135000901070340049e40c888c0c02d55407800801250b4100c00b0020b540844000c03901d4422100641c0c401520716400064200e000c1c02100c2d85615203213060016800e10605840450b141c44014800050461403002480a080c01d441000308401603a0001551400030a04548040200040740c011450b524507255008058500740000d11080102120180c000d0711290303822640c90030300710001241e0302d05802c01c024055400400c070700f40d081d06041c010110561255003030003903241a82c0d91600c0480e0300c00081641c0007071011140a04540e85400f40c1460601e048808001d00401200384200f01460415440e104440c100808400d40d0500000041e101180911200205413003000e03d4403508502c0408507045450000d01141c108218800d4403c1c64075100044641940d40b4001d61040340c02c040d005841910044c0810b00c1d90340d807440381d060794140007961003002e1011140350144000900240c0144541 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 455258327 1250 455257077 455257079
    0x303170c0301030f0212100905030d14040f08090303090621070315060c020310060e190603120c05120409020405010318021503070302040306051003031d0f0d03090b18030d09 76
    0x185403800c0c0016205d404071044089440c000c07405a2928003200721600850b42080507079030030312101001801c07045c5049242403000d030404503180d41c150b00003200c0041a10f070700c526119011450190252400000141c00c032460f00c1d012200081040c3c119168891183c1401ca81012620758001c2c03010350018406d050a01c074460320070301002c1726004e250107054100b125205041d4199501004104c41003604a14100101a1070300b00100010307404a4a4000c00c5496240c11403505107184105001c403074000000340800780c0100c404844103543e05030195000d00c5035489032414442c50800a10007404503d00059a80c0e14060014050310100c0c22007841c0385d8551000c410250300e42c04000801c00c0c00205440e5138940d0380700c8080d4002d01503904040c1449107002c0411005006042201b41964000e0701d8041d01b00c45010501003100d10302c22050f50b001454000207030340b2410001101070050303220342003955082d500c40ca101d000a030422072140039080950313241e2440d02e0400703000d600e80300892403030300f5481c503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 455259577 1250 455258327 455258333
    0xc060f0c030504170a06060b0316020606010210050c0702100e040b0604030b0411130926030907140102010e03030a06170d020607050904090206071b060c030c12090f0303170c030103 79
    0x240214072400b04c0d5081350510099400205201c04604154004c80402605849040980040d04200c81304231894104a10b4110b4440c00045e0241c45004164002d096a58258614001525001d02900b141d1340040c00040010b80d16036000038640038003503039141d4183d14410108402c5c2c9041e41882c5004170700c10132052010030f05002140d0752040c0c1200e40c400c444c2c080310020070050100c3e04c450034183c07840d0510f02d40800c000f039400341d903420008403081c9004060414840c801440180d036014a154441541008032444000c05c603130300d003c0140000580c018040b0003860842c0d00403208a41da0555940c0300b801340c503401540302e0a222601d1401006508000d03080070b5545e0701c0140c1041d090141c045a810f40540d9070340c100c410580d50184c00f80e034a4044518115002481c83d12400f401280740c5080415030b02e109034a401103d60709950340340364003605501e44d419900d06410040303042006103200894810054024440114442d955407880f0070601c03019881610006030040a02c088108010004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 455260827 1250 455259577 455259587
    0x40b220c0902030702071a0c060705090d021e04060314150106020312040501180b0703061406040e1003020315041403030f06040c0903020a120501140105030604080304030c020a030c060f0c03 83
    0x1a2401c0c2100181d0b203445003a026441d00350994410002c581b0203903a0005c400220344050001204140b04441d51610740780340c09d5a65005050001380c003c1c01c6481c5100141c50009000640210402800701c02815404041810fa030300381d802c1a03c079011004d00e800015002044015281a0000b003a0000c95041c244000c0d03c0b40700d80383e0355208643ca0721001c602403207004c2d80102c032039288007440d1541038603541c5007003c0040c40c219000d1001c41d00c1c0080c002001d21400e1601100003c00509661901d07040c510340002c0b80710003405980d826001d001000c00141c0b0208180c851944910010011921301450000115044121a401c50b03400920512401c1c1d00c000c03e4540e003210003107602041e00a00141c0c100d0300c8000c1c0b548040e5221f000000e0010384071401100303800340fa6007d640280198100002c1c4070014000a1080340c1e05988001300040110b490800034540041c807130301c0c0903d40d60000e03400203030192805400a4a12441d86d5108016490304640042480c00e50340c01c2402c0c0301c0d9031036240034003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 455262077 1250 455260827 455260829
    0x30303220314041403010c0e1026070809060901060f060f020f010f05070e0303120a09021206040b07030513150f02040512030c0706021b2205040b220c 66
    0x140848084180c1410180140e00410700c0d03000c0110815141c6544100c11001c48192102260095103001e0103d0410361041c145254440c80280c400100807e820000b11191181e0324214420907011031111a02c41c0400c01100b401a001a91102800c0c1004401d15040c002c010f4080291390707150640411140c00c1c401da1100c110b503014103140800031003030340d0306a0410002d56821a019440d101200620800b01d500c054000c3c0010707920441c4103000d0f03c09241d941e00c135000b03103490035240481c005600f444c410340111045c144050080880d07001d6a00f40c8034501135041e102114070340207942c20001c100d03505100e1607501924004407181d491341e0310b4a528003401120360150f07025075185d4021103c03032411030301107070b0040c400a80454001d0500d002c03010f8894000d00011030542c01103580c0042d6292000501c11084401c1c2d4007481020a4050f0030803298034240141d000b070700d0241c4032a0800318003140c40f41c070788203c1c040c0501c420f59141c2030050a03a0700d004042d00d28070482c0e100034000c02144045034810 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 455263327 1250 455262077 455262121
    0x5030108100b0103091b03110102010606020c0f010306080708010501060e0927012712030219121b05070b0c0c030f03092b09080d0c020402070c03080d0614030303 71
    0x10b480c0350076400403400341a07500700141c144060444102148207200410004582c09003192481c112002d500481c240e58a61080b04010ba1001c00030707000a24001c4248414020141000140f07a959441078908089241e80100e5560b5928001000860742121880900c0c0a08650203c1d291500740000d003110b540509000395005201180030386118025405485610401c000030003101488201114010300c0c060002c50352081e549140c00e420a00074000d13140300d0101c08208641c0c4802c003900455127902000178001e140c1344c464100320510300c0e800194040c0c10f0391507aa0703641e603403055003070140e0003440c00307071482c40503007000c20078813900d607902105a924159000b1900b41da030303031a126030181c902604203096028104089085214034400c0b20929542589903450b42d2400590b01c005080c0c0300d0346807204200204103001403c0005150550081440501c43c0d508180f155480e0f44400543e900170b268612016669120f0901400552841862440b00120025032440c0b900d911000340105d6040c1083c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 455264577 1250 455263327 455263331
    0x8010b0904060b040902042c0105010804150513061a01050313051204060203031f030b07080a0e010501090b0109120f02040b060f180a0503031e030a02040b070803090d0503010810 78
    0x32112590341da04014010070301c52540f640c03140d032500c0340c1100175030040c441e061800d802c204480d0945030074240b0080d01010b220040b9020b580c030b0100107649410004108450301c0a4840e03801c01c4c2502c041c401c240c0030300d0041516a10032682464030508a420096000e0380c01c000c1412140c0403aa40207048079802110400320350764074292403800c945060290356501501d13a50100b03020560660000c05075200f803c103071903529114020089450100111800080c20303c5034075100040d02c65000b040000c0e044611090001800074440c40c801d82107d000381c100381c15042c1c4403024014113607400040c0401404141300c082445003000d9480380420340210500900075a10f449980728640e85810a4521011840fa181a07440701c22a00c0091203005800005100b840344c050081042d00b00001a0790702818100e480c44010b2201200440b2142c000400c0450b4082c0c08000211380c040d00700c4080c0100d070707200ba52050f8490420505003400c182050721902d08000c001e1004003c405000580d00c49810700740f01c80 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 455265827 1250 455264577 455264587
    0x20117190c020f060420060406050a140c01090c05120f0a0204090303020705030a080604050a0903050706091b0803030906011e23220e03181504090c0216060c020108010b 74
    0x10a82c03e0540d6040303c0500e40c0212400c21081c00302160703890341110421401000e1242d4603400b00100f40c00303507004900018009020b0f040c0e000e40107004410002c410440302904008182500d0380c20b4031001c0904903001888a407040006050108004070820110030145c16413490800c08507540c1c2c6402c89007e442983c03548000310a15000380d04079008250000113886c1c0d00d8210355400b0302034001c01d4802c01c0c040c0b490a8000351040d5424410311104c5030b4166100c82c500400c80e02c481c0046c0820300d00503569402605041006100382e000480c00411a000140da12450050075890402070140c2c000c1001100305051840600203400401066401504046090415800741c566141014600050b000f50701e0b020094400464018a690085e2900c9000d00180f090f01142c0f030b84901400b0310540c0d41003455984000f0030700e0700840c1e03d990810420311190401395039100c6001a903c1701001b1002603000081002e14480006e1040c4028188a051503010704545a0000b031044405228400f40d422001c15 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 455267077 1250 455265827 455265851
    0x601051c06150b030103033b040b0909010f0e0105010806010519182405061912110301031a0c030f070e030706020124150c080712030902011719 63
    0x100403201480702038144110541c90f6001400f55a000703000660100d4200304000100030070b540c50315a000d541c0c60040d00d081c88903074850a21a01c28031920282d1041d180d201c24107460b19000462032244a0110004c1140d054074180c4400b160581c005071001e5074117002c014080d030761000078184d0445400b50703080340c0410b2040110002022982d0407681c0702480746800780180c1c4685d5000010130784c0340d90a00510310b0304808095156000a4415a5080744040c032100720000060500310320103500c0d5051a102c18451000705400312400e02c040e4031081c2002100501c184407000f01100d219641d01101c51441d8141b43c80f000f280340c040145181002d19505000506d0b90388030300111941890007400325528640c40760006800b0700542014200b0315a41e103400800f512440d444408100c403030050f140300e02181c088204039218a0f0030001034540070fa04106d0b100019010102c40040580c8030b5400244418030781c40010326076030b0030059030203440c409101400314880c10940c6601216540c01c07000121071700e00d41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 455268327 1250 455267077 455267081
    0xd03062603160206190527090604021e04030b04290c0306010905100c11010c020d060b0d02130b010801060518120f01060303020606030106050103020a170604060902030106030911030601051c06 84
    0x85c2c603040300640d004260440030b400c00094100c0d60b22001d4110030140c50108080c000c04003201925512080d0704011074060b080c154000e207080848100d105c1c05045e0070b035800b158260300c20b80c0101c031030311500c600300b000b840303e0f0804030501c0700c10071001486607024541045070710350805488100c1c002c000001050300d41e0f000d070080300001c04029141145840e560000640104903c4400b5110b032480c85098102c4d0350b00c00d8407083e0045a00034100242c3d910a41c40308001066201c07000c2d60081d43c10162500035940e000f54580800b81504000302c0c034801c4c5040010b00a01040e40103c003800024403055003062002d900d003500403401500c0100400000c8038140d40703820800c0d0314240e05540f07411400f100f810f0f408281c1520030301d0309800900103983d560004604034443e0b03044840021f60f140c110502c580001001d5682c00c446e0082c004607020b5110702300c040c2280c0c020b83c050030100fa5199208420041040060f43c1d00460440c083d012a62411000c01c00e855050351040c8403080c401e51041e41040500e03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 455269577 1250 455268327 455268337
    0xc2a120c0a330f0501060e060706051801090807060c020705010507060b03010b040e0a031e090b03250c0b0a050f0109020912030a08060109091112180d03062603160206 73
    0x1ca8500502e100c0040c0c41c0c0c40104442103001070a41d04103800412610302401441c0c007401c81c041d00c110314120703c540ba01c000078200600411441441180e032074801d080c09008041c0d00b603000d40d6520359101d0852520308101c5000380c031040b00b03540010700d0401c42c51b03070440150703101c02d608a40046044500d040000c0e00400100c0c150a5215240c11910f5008440010320364660501c00d0712803a81c0d20600b103507039504124590b0320400c0040c0d1000380911002034844041c68000140003e03100070794032550744207540b0201032201000000c03200d0b00358000740421003004d04c1d00b00b00c10101c01c01403030410303d0070714040c02c0c014003440b0611038001404247da9240c01199402d118068003c0e26142c82a0500040ca2100c0940313885001500003000412040400c0c400c4203584072584509500c0c121074001c1e0034030030410081c0409408001c070321035821503d20600080da10440156000150070f401c004a400182d000e4070700c80100b112012032a000302c41701c00003c803100340c103544010102100091000452520034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 455270827 1250 455269577 455269643
    0xf06011a120a050108010b04060e0c0c15071d010509030c0405070c06050c091f0912020607060e010c0206100e1302040204031b14010c02180c2a120c0a 66
    0x140400c20030400b403543d20007410703900003034003c0c415984848104416202d5502900e0700945200d004a40c250100c1d40081400b2100354090b501d2901c1d0400b01800c00302e10464400012540c804500807100ca065035000b09880400d092003403c11b03030b8010101e59990301c070044050265941340041440f41e400380d44c00c1d060041d400103051200c3d03d840211488140c004400301405060100c0c0c1c03000c4080306002c030002079003000b541c030001c542d4540f00c00783d50b01c2c4c0d800041c16a0440d808002d18400b02d9401e0150b6a41082c10b040007041c0845070a5000b441d00f80010480c640040c030b501c0003404000128141550807601094000500008900004000344030350307230004060f000011002d41d44910f01e000f04000710342c0300242c400d9035a05202d0040d01c07080c100b008020345c00ba00030164003204c034000071072080e0482c041c1080c41c8e040080c0040c0310780c965100c0c0349591505025001c04440c030408104030f1000000050a0018181720f043c2c009582c3d01c17440490024160601d8507000c10b21003d034280407141d4909 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 455272077 1250 455270827 455270857
    0x303071d1207030210050306181e0a02090108090705030a03121b08010303020c0108130209070c060213050a0f03230309060d050129041206060801050403020d110f06011a 74
    0xa032403001c03907468070244000c9004200c1c0300c07201d07025940607a0a0b40d20881c0c001d800c41c590740c4503007640c1500803107004003c08407042e0a00c000001e07400b50b8200f140d210703454000c00169112181c90024200c060018460000f0f176020380b90078001c0351404a9800842907140c2401802e01c0559503200c3c000e0b00e01c48031448040040c00c859020041d6202400354103c82c06a0265034624681c0d00c011281508101c802c013036208440c040860050924554a591084882c0340100003a140341d61898107991003500302e460f0345207a5540034800380c507104000d18000c02c09906402c0300c040c0356558829003810003a4100e11209101c504480e00b070380043c012545400e4000740340396075540418854000801c0c0030f004420084044031040761540c0301d040b110900d4a015084401c0c10103283c0350803040e0404071810110341c1030752528400240704909014084c0032398400e401a01103007e07000d20091800d019980d070740c1ca05034131152040c040b0740030205000d81528061120b00107440300c003000c115500e05c03443d0b00000000c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 455273327 1250 455272077 455272099
    0xc03030e0d03060e010602030a0504030b0a02090909010e100218040507020f0105010612050703150e0606130806070e09070806062118010e0d05090405091608011b0f020303071d 77
    0x1652680c0304506440d60310b8030b040341c140d0306d941c0100e94a00a10310641c0104008110501c04140f583c03615581c00306610740003500d80719a58000c81c160042c00d03150040507a441c0c5400c001490801e211381004519405821030a182c03600721806010a06002c081d401680e07036a011807107035482444407080391200c0c01c00038450381d6515200200001c00125100428030300e020003064181d407190003210210305076030740407041c120304101c58168041030140ca0075078000c400b00109010217821418480081600d48060161840c2ca0580034041c0024400c0282c4258804000c0045c843d070004c90b4280c10250a960250721a244a60b0402c1d8982d400304000d408440d01204101e1600c00300d19004030042013030f0000788808003108101c03544c4c1d60300001c80007011403400c2c4403102043c1043da0029134010040030803a551410038226025a02210740c02903402030b5103516224a064150320009003192000d45413000343e01e519003074020749030b010282076002085000400420300c80565400b0100e080710040031a50700c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 455274577 1250 455273327 455273353
    0x405070e0c0702010f05030f0a1d0d09030c330c02040e0d0e120d0309020307050a0b18060a090b0a020a050f030c011a0609010f03061206022104080a0c03030e 69
    0x940100b10300303c1c00256103c10283c9074070f1080b0140c9005541c0c10188403a16103c1000c108090501d2859004041003206032021580c84108079480d1040aa52502c04070203041d0705004022103050b030440c0041c0f03400d080cbd80510540d09071481c418000000c1c008862004012401121460089600030758490304102003200c075503601042184485003a51103c90004201100b0b01c000861a02d070894902d07000301000f1128a4000d0300410245c510080030303036030160b0700c40d0001000944a60031811202c2c0001c00c540842c0c90040500c481036038411921603045c6001004024440041801144100031001c503003e16039130f000f00002512039a10906a82c20356083d030b0000f40c0d03280c000300520b04040d8204400b04510f17501502d10780720b145a0180050f450a0300f8280191401c60320b2070344410405a440000003190308441c41da50030a030384506405a40c80425200d061035030403600000000100082e018880014107410440700340458a05003440540c42c1d07800e00f500200000d4000d4a10360140d04100305403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 455275827 1250 455274577 455274601
    0x30d0f020307030e121e040f0801020301171216021c0302010515041503020105090a091406010e030d0c060b030f070b0d1b0203161502130603060914010e0405070e 71
    0xc07401e02d680e0b00300982403845070895921450b42401201000c0e0801c46807400e68032462000b01c00500701000d0300c0c50715644a80600110340c1c6030b48030940740d941c0400103100840c104104018a001c0400050885c8105196420320034454082c80702d1410030140724460454558410030400e110000410b20701c04181424080d000c1c003003c943e812070a0201e08510310480c40c1500c200ca0300c1ca07148042020001313041d0360064a0540c002098140d20035001400001c81c198070f4003d2507032211002881400c41d091101c0090001c505044500d071082d008420036243d410303441000528115086080800c81c00c00f51800b090038115640403101c1140a2140c0104940904c00018140804200020000308e0006900c480160340344510000050300104a60104403450034520400103018544012035012004500c10890380100c40454450031909030800080d900361150320028800d000c02030205c0f4900c080c0314a070f8500d0501980510026800200f4180f120810000025201ca03020002c03031404d0403008041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 455277077 1250 455275827 455275831
    0x1018050108010f0212010512011401090c09151b0c0b0a081503030c07120614180706030509210f160c12020d0201030c031b0302070b09011517030d0f0203 67
    0x35180d803d00c0d030b400c1c40840300d070b10031692010000d0160b1403051f400c040402c0392031052a00820103a64a501802c01c00b201180e41c654020402004002220607405501a00541203940109141032025018040c0310b50080c5046403070400048a8042c10304031454580c4009455800c039030a90400407810700c2a140d04403001038040e021041c6040544a45041010350728070079441c5000fa66003003940c08001d26112072a015103400d05c00c0c50f021540c0c850072012002940002c030b07882002c202048950710703a407410610050015102c1c5260500191800740d0342c0e9540c0760004810200f11400140d00d60000c1e6965500b920040040024540c3e507030065860880140c60a402e003c2d01d9110003c4000500c03c08448001541e2942c086c1c05200d100c00e054005400801103184098289030701d5001c2c2444084e0007182c0381d10b9040160b00c0061303c5e002d05080407849184001d05070912a03142c809079001d0350021401403011038090f1807840c524910003250f16410b5000b40c01c00300070361900303058254107104d80f683c020718 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 455278327 1250 455277077 455277089
    0x30c02030a0803010b0405131a100309061415010c0b13060e190311010e0607030914060f09012d110417010609050a020307120b150316020d08091510180501 68
    0x200500308403004230f03801c03a1083c420a1107010b0400310052006d05003a9905141c01d95941000030309001036440f00810f5441307849803143d0941a039820402c0c1880361100603140b5400070300e0100a9054103503141003100101800040341c01c441c9080f0b0108200e000c1c1c02800a503400d000541302c84100d03100500054850501c8101d0108110600880020748144640c080c0300036040000c0c00180c0718030f4400d400820501c41c0c02c1d11b12105041d000440043c08024141c01a40b24040209041c0f91075041c0c1c0d821120000c902c9481d040102684c0804101b101042406901002c2400a01003608541c01c4203288501d0344001803000d004800040103d6041d07100804460b01403000b4802541d8402ca040204d100444220740401c4610f090a207140d1280e621503d1104000b8001201c1e412182030190100e42040701c2001816026441001c1d1590381441259020310707550921001c0c90410a03141c82d01c0f040e000300141d50b00f15400000071144030401d09144010008614001440b800c080e080102a00d024004e1b030f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 455279577 1250 455278327 455278339
    0xa03090506030c090f12150402240708090d020a0f03022704060b0f040609050405070807081507020703150903020715020c240313050d050f0304030c02030a0803010b0405 74
    0x400d4100300342140e1144006000d01071030450200c00f00315000d441c4200c0140c00c84409012003100400030072072001190b800040d0301c1c4443c6080d204000c0001002000d4107000ba2200711f00340c01041c80102555103031940000d440761a40311f200040750000029030307400b9521113683d08001411107401d0f00450283ea000f541c00900040c034030082e010f6030014002c260350075100401c0000d00811001d62118014100003084034440709003a00000d802c1e5901c07504502452980d8005000c1089810001c4000a01c0701034042c111152030000041e4465250400720a4104c9821000880461090001e107000d90b5010b08448203070a40748c00d0110040c45c00d1345085001d440b071640d0108040354031030706003a81e07400a0380c0180b000b6550882400403a4000c0281200482c54101c0310380e1541640c00040e42c85011102611064440c2d0303800d05d00d241105d0500e40c0000e10104114001040000c1e6003180c0c1e0141d003606062200c2d03801480030a1512840c2003001c2e00060021002080040c0d0390300c02001122402c60ba5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 455280827 1250 455279577 455279579
    0x40e120a020f06010501171009021b1b0f0d0c0909080901020c18070f110706020a15110904020a0c17130506040b0403060e1e010f05070c0b06010e030313080a0309 71
    0x7803da80d110280a050701081d00420001800c3c0c00c4510929402001500c0d40d000082c3c0d981603000aa0308040b0103864218401741c0481104201046140e141d42c8407540c00e520809103000204041c400c2d410b03941c42c0140d441002150601c00011500c100074010f02804200c0040d141c1081d03001030b001486000d005001d120b010445500e05400c03056685490f00d444840207031a100d409a80d2655010740003030610024124102058034180084401881c00390050704a01005107480301c0280c4085084040c0c003440c0c110b0a00080b010704007502c000410030781c0c0043c2d032420580010b440c010303117445000300050140042c0101030b050070009004c0400c491150b0002d0540c64404100320740c0118050b00312946c905000800c0272508540108510303601044c1a214500d6583c07001c4c2c0710b0504c40007803a40307580c0e4441a044596400e10703c0b03042e83c010b4991a00c840e086000340d44004007400040e10381ea04014001e00c00b00150340e4180221081003605e07403401c680700c594408803940c039500c211a0660100f031881d44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 455282077 1250 455280827 455280853
    0xf0302060636090f01060b0d060617011509210209161e140403030c031202030606090d061811180f130507050604030506060a150914040e120a02 63
    0x91a071454240b54480700e01c2500741940071100610018002c507111311a190703103031380c03004400e208010182c601a403031140d03141c1e1140900010340380103a010000f0449044608014407100035000c0e410b5440601311100d07818004041111035940c250041c001d1801081c017804c40010300c2c0440c00107070510a580c5650785a6039240448560a502440803000c10749121660240000982c0c1c9034103529a10b0920900004070001c030b0003d00e401c141c0084010404d503480070308c141a00034610303141c0303004080e00c20351a52400c0c00105800b07016480e90180501c04120041080114a80081c41d4404a074450403403840f41d9400c00000c1e0300f0442840034010141d001440389080360804409110304910f00c0080354584801c1c0c42d6606a00d400c910035146800381e01c501041585d500d80c01880158005c1c0c004002034101901041411007180e48503280b060810f8180002a5030062800d20072180c040310600d4540441d5404a80903250020110a02d4090400024881c08484010b0f180e8019144d08a908043d9440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 455283327 1250 455282077 455282119
    0xf0e010b0a05010f1202090409080304050d030f0c0e060a0908030a2303040f1205070b270f28060212010f0b091e0102011404111014041707030f03020606 67
    0x1310080000e034680743c41d01407030031960000c2c0524034028200241e20703040c82e04c88044a400c02d42e01250329802c1800300d110303401d6142c028401c00c02090441008243c10340d960183c0313141900b80d8114005d0130702060900e80c5c94094031491000b80240b0045d0313503841224440c010825100000241c501e03030604005a5405803091060320b102c0c0d50300071540080c6500a407135404009011030003500070494100003100c006600e400e201400b581051144007280c00383c4640004580318031581c030744040d038404c030420040390100241440d40c4503400107001092002c98484000e03501102d810203042c442c0000b5452050300080c09626040340c3e0340818400005456101082c050b201e2100890307401084440b41e12001c00c200c0c1c1300020079200500000516822030046482c403a90b0480d000d83c0d5418004d03e11031482d0a00351403015802540c0e00e03101004942401d90884036004a01641440003101c4404000c01201007103490003070361b000f0040088900b00d503d8000c0da941e00485489001d5240e003c4103418a007980 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 455284577 1250 455283327 455283347
    0x809012303040f0f0501150f090504150b012016080f100f0212090c030c1917070e0f06040f0b0f09060103110706021e0301030f0b04060f0e010b0a0501 66
    0x400d80c0600d15165919015607080001105035100d0400c07604500000710244a4280c038407540c4241d00100030702c3c00d00942c1980307459600111109050904000004650105001110803840400a1050000c20041b030b400b6143c11114158240003140014003040300164002009800b07001641c003c5444004a94564201e40c5180b00341d03a005c14030040342080c2030781201100d65440d407801820814003e4112810381010780324000d03550071840c82164142020300c23024001c20420350381014585410b605007050110300b88980d031700107001c440c2907002d8000c0c140441e00040007a14402d0350a800c0052075190691815503203a4403491424800c0080081c040c01a2504520001c4c0aa003203e0311442c1031054591000300094105075445c6003443c518001035010f400c2003800342c1c800588036050288401e000810028401d035060406000410001d0102d540c042d400c01c2d0320444070006a1201d05c0c101024003c4018800381c8a4142000c0c0300d204e401c15482018544000c981e074a0310607035214010b40c1c3c40c002d2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 455285827 1250 455284577 455284637
    0x4120c050f090a020c12070f0b06150403020d0c120506160807080f07090f090b1903020d02100e090a09050d032007030c0f0b060a0801050c070f1509080901 68
    0x9544002a94094181c0c003410425040c00d056884940400700f103e0106c2d0300c0447c1c00c82d03800681440030001d20407040c3c0311660105003654079182e07101d283c01001805005900c0000d21130380b143c2074054100300300c02150b0001004644c01d00c0c02030810b64070709161a00012101c500c189803c0018052038284102e0415010700020f8685007029105e601d1203001f0b0f40c2c0c00400d900c05010512000107010940140040010040e002000880b2a074150030003201d5001280d9142e4605150401400980d651042c60088580d0440c0c2d2044800e4082d5030942d4110401c040050b80b04256000b084900f24090f0230541129100700241c5425010050b800c1c3d007203544c405840d290b0560149800c1101317041e142c001700354003800303800d041c04503030114dc0c0c0b80780ba01c0d10811411500707286c000003440700070b040210105010300f0a4000078082890081c1107114140528903000e42000c10301d8290304103104810454280640c400325043c4040152810b04145550144003103034000b4860b5509039400580c00c460a40d5420b81c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 455287077 1250 455285827 455285839
    0x412020c010e09060f0a06020106090c020619020306030a0b090601031406131b26011b0f0311190206041209080606060f19031e0b0d0b0a0204090204120c050f 69
    0x3044401c3c4000404000c1280381c1150041d403d4952075030340d0100d9100100115030003c907600d814080d8420030f40da22034280d1000c0d035000e0014481c81c2000210284140d4840c1c0c5001a22940c401d0000392401c10303500d102a01c043c0640c000c2c403135030b290046203082c1a00c1c0034042e000b0040c542c0c4070200e81d885100715441884035440c080380d00c0000302c149800164220410104075545a110140d02061111024551088003514010b804c01d050f820b0103603c011304d110b100c0c8524103d406642c0034182d0b0529010480802d5a5444952907140403001520502d2100c20aa280218001640603603603440c242c6054800e102d840d00050503491080d5210f03030036030782850090081901c812081c06880d030441c2400c070848a40c14801c0200041d00f000204202003582d5a02040e07a0003103001102ca980d0283c2503507258907003800c50030301036a1074200510380300da41c4c0f004001403240c2d00c4014078402401103410400c1003600000d000203041c5842c800d0120b03070a01849a03040c0c450390307034400c02a1032a040851550410307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 455288327 1250 455287077 455287097
    0x6050a180308090409080c1b0a0b03010b030115140f1815120a021207021605180c03040302010914071406030912030406060f122001020705150408150412020c01 70
    0x4c24a50000260544200003850410782a088402d04062020b201c40b207162004d01014501880c011782c80100400c48454030b80d295504201c44180244014025416130601c48610a11910711851700380360010081071038551101c41c0702c4080300084e8458034541d4092039064003e00740d0f0746040c000d40345c0400044002c0c01e141c414100c00c0311540801c020264400264203018007405140c015240c544a1006035010d440c5c01400b0680f04001140340d900b146005402100e20041c003507001c13200d9a83c0022005003280e0316035032a450103d000d801340c0c0c0002010a90485107080c6110400240041940c141c6d4a404507500145024002c09000840e01250382ea4820350030303c001c00c0d45940c001c40c0c01c18058000890f803d5203400c0110301c0d15425502c603060442524420100b40030a50810491018240703004805400d00b410000350350b03905e00e000f10703407189001e4400440d042e0185411036000700700f88415606080001c0016214062049800b0b8a400410500c10703128a413001c204814a4601610f6504040b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 455289577 1250 455288327 455288329
    0xe0705130e100e0106051309021e06090d050601090f0e071a0c07030b06130902101b0b010e0405070609030f06150305030c0c0118030c0b03041b06050a18030809 70
    0x150400507880045801070700c05000d1100d4640c0030351201100354070000f1030401c1c0341c02c040c001c02801c42030309040110b191441c04401a556840d402c11054141040760054a009000082e1071784200021190311441007106030040110100300281200c0c103850003007100610000c401c03000d40320407143e10381150300403072010700c1548800b1080c00312000c003d440c520700b0101e050380c1052406c12140c00944683d0007034401c000d40c5141c40c68404194200300c1c0018008040c9603400300d800000602c6800e01400100b15224170398880d10940540c00c0c541106208246594420030088030800983d000d46550080000110701d0a0140c001c480031658031070140008103405480710341c0244084e4204210b00c40c440d100000208608101501142c2c3c4498050304110845000241a407034031091400c01b1450742c1d110802c00b08442c4076114048855000c18550b40742d50794905495000c07040c544009064a8041c00410210340c4180640307032901d8591200400408070b40500703800b0965520004142201c200618012 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 455290827 1250 455289577 455289581
    0x11502010b030d080a060501050412020d05010e100912111b21160509060105040b0309010207020406170d080f01060302130509180c040504050a03081005090c03040302010e070513 78
    0x101014400007491a01200000c0e0030000261006800070300d00c5010301607400414030407000103081c2400c000f4034042c54848550040c51145e08080d03c41c02640070b4a01c1405404c8d0080c0c8031450611041c0c410945103601c01100030540314106541c0303901102903c1050901400c181b091035101c2070f000306400d1408100701b01500b401e0b43e0800e0340001c058903419403000480381d00e02c5c08482d00e05000e040d504c00800040d19095040d40d0000d8032400401c010311805036000001c44040d52500500e480e40c039500c05255a01900c500341009400c0f0b8a031403000680d24107279150540019006500743d4041c810b107540c08540b03841080e5060f8000810302c0004000c07690081c2d006003024440c0c01950481d02d551030001611143d01100d81e480003049004040d5903c40092000c10f007100c000b25002c1007141020380311150b4644081d20000d0a00c00c01c840401c91019000c0094402060000c082c00401d2604034004603840e001554100e000d5802c0801d0204583d0b404a080c0055400241010171901201059800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 455292077 1250 455290827 455290859
    0x910060909050f06120703080703050d0509010605090c072609120a02010f2d201603020f030a06020c0a0b0901051504020a170109091101170c0703140c0105160e0901 72
    0x1443c8100d40d030001c0051480700151505a029448140ccc0b10007440c0c000b5000d85200800451091745000414000340c2d4801418a40048445020a4646d0040d107016080c803107030081000b21441d020180041c0c0825204001d015101058a24818000b0f40d1402c0c25a00c4c0c2c84071200a02260b0744c084071034050340c4a05060030303d009040c200740f40c0c280e0913071003622400210501c84800191b19144e40001d2801e0350303034143c648070322003a006102c455110406142c01d02e1007030000074410307090611220712596003008000c4446810400441da20b11400c2e0005695485881044030080707a1140010444070042c032400303108a0b9031510007002c084031807080000135404404034906000c1c0c0303401e03504041e26604424074040e0490100000e920303411424410740800b410b060050400251030145c40290804400d21074221505541041d101c0f00e80d8603058075130480da903556060307074200801e1320900b075001500700314003550131566280801e000720ba50480308208103a60b0103800040440040260000c540d541c3c038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 455293327 1250 455292077 455292109
    0x90a0b0a030c2303060d0206030405060106090815010e06040e100525081503030c07120204060b03070c060b150a0521090c01050706060302030304240503040309030b040609020910060909050f06 84
    0x62140c91071f400101c1640050717070252450303481000148822600244441c0261405ca002002c1d01a000605940b40b15414090702940c50301580129185031900d411801c584000e0405441545401c61140e0300101000c072600b011402d4009200c0319441420f1040704000095035964070203c3e40c9414180000c17412344a0215010300c010080001c1e003035810301000c07015040e803044124520050b80100002d684131a004044111000c0061007403547d040b030f14030714120b03522440205003400c070307200054850807003141085802540014505111944000180300c10703d41c5401d00307400c044da0115072035110301c0202e0300603803158040c6141e004690700038806000114402c81c000f042268a0f540400d007980c015a001c50758800351b00d549000074601041e0782060038400d52800c5802c52401e80c070020b01d80c0c007907844064079100d24040807405011080e0030500545070003900402c0c40d4280701c1100c403603240c0c0c41d220300000241c401c0c10201e4000640e000b000d000300c4682c1d00d98076041d1144410041c009140f00d0041d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 455294577 1250 455293327 455293339
    0x90f0402010e060a0c03080604020a171009050c0a0216030302071205030f040b030f160c02060c031204080903071d0103060203090f0109150b0d0f0611090a0b0a030c230306 75
    0x40d20250756503d004001100a95442c1141001940b41c0502030000c050b1101b4440d500502140c0003465020079100036075409214022a15200c25031390000340f1200c2e0300704800d0301d0f0400c801c004440070300c08002d19640600740d086035100c40d16412810020b01140c04014010b800c00c0008000c2035081c60b070404040d030f0299003641e140282c48180380308281d2003540b048584400100400c0750760814031440640c0651400504480c607003a080c00108201301d2640c000b0310425010412204081c0104262041010000c500c03401d0b40c1480d0170071038000e401c4060424447c1c8140d20000c035404078040010f18051900c900452403590035990340d403020350401418050705108095094000b07440034010100c003c0e004412074440007051591020a0300e10700c40700380d40a03140c3e0000c007900152030082d503045855006640010804011700c007071a55407095504030f9521800002021030720ba50b4000060001e9210707034a0802918900b201c05a13201c800481031403101c21150f46c01450300301c08440c015540300000400c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 455295827 1250 455294577 455294597
    0x33403170f101e08010e1e0f03120a02070b090601050306010f140d03020c0306040804090c030504030c030e010306050604080601091a060403140a17181906031802030f0d1805090f040201 81
    0x6658211103078445400d0007035010b803681e2484582e144480e14002186117008d4000841d0310815030b03076130748288480d03d080c0302c0c40c8000250200e0b0056054410340c986c41100145181010b203200303070340c1361001c0c05003500c03a003c3e000000840307140c0e101072a421038903030500000e035104100040082070785440c5002c0d01540120300d10b00e481a58280611481244901105515241003e081900700c555920915013403514102c103000100e038001c0400c2a000d90b05103410300300e1200c5c810049001e0803040e808150019004100410a81e4003c19140d059070703280881000013243d001520412075890558150304980100300a20104019118075265207565504440490015036a5003074090080060018241000b240180070748283c0501000495000c071180307508140407030405140170391240700300000e06659481032a4200201e0a40f00c0b10aa00102540c884d0002600f4880c0c60f42c080402d50b000180c80303500c3c0d51240c6110010a60b047c0c23074000e400d9441c143d442040004004801401c1a4140000300030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 455297077 1250 455295827 455295839
    0x2010507022404091b050405041503020a140415150807180308070b060102120405040b03010902031e06070f09170c1504091d033403170f101e 62
    0x240b8604503001c92040c050b9070b140f82c04803032403c44105c5070000340c4145504441c0b09449a115040c0c03416114115030010b4200b070b0407044002d4100c031a40c002500600201400141c4170700103d00d00d8411041900c00b40b041d0008000a00c0d00c00300b0324000ea4204035031090000c89a1441076a00d0340e406111400c149081d05600c040e481d110302c403190300072580ba64001400d402000003244400360441400c0c00244140b1942c44003591650180d03001b154012980c0f040e608015913025001440708580140c1602c001d1011503036960a01141211942614410000032505c0344d0300c2540e4401e82c4052036625188094109420b8401c802854400130b1250301c0b5100f82c0d8035255849286582d28140d03100700540d80d0b10300d000b400c00d06941043c0022004a00500500c0e1813180010046583d60b074039402c4520354911035022550402d043c0794000101d2641440c03105803c054204052401d800c1001ca140c00e200c2d5240e0306a17094003182200c407404c903003c49e04402c020032850a00e041d801212400488055140c07030740 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 455298327 1250 455297077 455297119
    0x9040602210108030a031409060a0c021617070503190b2e0305100c12090c0b07050d1b02301002091309080a050a0504090c0201090203010c020303130201050702 70
    0x3e00010b226400003c2d80b1829941c0500c00d40c50140c41c602c6101c4110b10305440410f03207d940017031242c801180c6035038002d54000e1080c000000d002c000381c0081a415915496085c4841d000424a20264032448a000c5007602e40060018161001c020820807410480d98440c42c40d0702000c1d01324100c00c00d2b03e22090034542e00e244d002e103184080010065008520358245940740001c102032001c0312034900606584070702c0d4084ca03a20501143c0c014049104c458900c2c08190302201a845041200c4020414000700000492800311007091035a6500b2142460b400b00b41c1d18219035030000b9801940707003001203082911404502039480783c0007070b01c2d100701c46d1003809203050450340c100e421641a4005001c044620b0aa80045543d68207000c08002c10021956600d40310304c41d0580c40c9040c040e0104001540501c070f0301c00c44001d4040b0850510030404480c80c007078060b142c00c9600324809c2d42018120891a480001560720030b0b1441c9241c4420900141c0040d1069400f001c4140d80051220070001c46c040d09032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 455299577 1250 455298327 455298329
    0xc0709050103030c020907080c09092203020a062009130b060c0c010215010b031b070204020d0911091009021b0102030f01080d03140106210e030301140d02090406022101 74
    0x3e0302d130f190810156104100f42c17810024201001e0280c46c0d03040c00f010000ba04140d80100c03500f0b4449421076240e288402d1884460014020100b2200400c0c0c2c0041641c00318201500720310034602406468401341da2420508000310103103980903002d001c1000e071850071a0711032000d1a410000010040d07044004600305038052415002c1c241e000c40c5a440d51540c2c1000030709225030751450005074950609e41010039510000d08000328a200205102c0d0111100c242110b030b04950061085556024016402029041114098540b8480743c0c070303482a142400d014041c4107000301d071107404045040c0b522500003504003845402e0201c0d0864181c86080c3e41c00d10042d40031b03001d10b810411241d854031084500d8101c0d50250181014204005258505030400200d810741c0c00900b805070407426410381d2440c6d19030202c2080d802840c24001c890b80304100210043d41602c45021514040114420500401d103041070002900007004500007808a15240d0180c8100c082e55400c40c1d00d03090b82035000380d41070314003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 455300827 1250 455299577 455299583
    0x509100806032a06071b080d0e0409050a06110f0c070e0601110c040c05121e01050409080904051b030c0316171314030f0d0f110f0c0709050103 63
    0x251038240819031408019500311440da00a055060f0305101032645141500d0b0640c0c2030180f04045031080803c150f0701e040402d00d0b6000c0440140583e502c1d08960364441d015802040468010800040641480c0c011917036000e4001000742000320040e51050700502402100a20014003401401d0f4a1180f0a00600003040b65000a000e03040c1020f9038621b4500c3d0150045050110410480340e08007008100c0412924044800003030320200b0003400d84880c816410010a51101c540c01c0003480b9450001c6180c0034015440040596038170346040c04115a5020009000b00ba403e01c21044507103410307040a43d10080342d00015102c114995440344054000b42c580e00340a51021040224441141c1c40807407106200b403810709040ca0321100074004095028155041281d51008150213000110b030070769581240307038012299181c610642510442c4c0104080c0600981081d5040d109a12107004410384c0800d200303c814078150b6141d50082d00307544034100e0400341d0702682900043c07000303007481418000d41c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 455302077 1250 455300827 455300837
    0x405040c0509030c040b0a15030f050a020a080f01081b0307050a1d0f0408090402070201020f0613020a0915050120030a0305011707060f0e030a1b05090a1e020a050910 73
    0x242582c10181068000480a40640d143c04c841c046166251040320b4212041030b1030440396200b84190440103030012144054400e404c0c1428080b442d840383d402012154070302c0e40c4104081d19400d211201034003081c8141d40b240d81c40300074110aa011142500c28a10034024101c0b03032a19030700d4020850b904120780c000b10b508e138200c6e40b6215407141c0360703000c407a804032840c1600c0200785090355440e03009003e007080450050b68049080c20459008101c50340d00800c2400403a075040c40c0460b24462038002e1004100d00501c2a500c2c0080c10031454050185881c1f0852840302103d4200343c011103202c500f0140d03001a0b000442c502c220b5004080c0010001580c10f0791f004111503042000c0300100c007810850780c6031146e014850030000c40b544010030489017001403a00c0400b10a5510010340b500d8000003014041034425240341c210f400708100340d001150002e840030482690303602488011a4402c3c803a00950b005040e14241000901ea4002d144514060401e18100100c480103d00e03d98000110318010807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 455303327 1250 455302077 455302087
    0x806070305010e0c030105011416020d060509010b04020f0304021c0f031d0303070b010e0c0904060e09010c0f0f120f020d1a222307020a20031903050405040c05 70
    0x2101100d0780742d41c00104e02d2007051444d4034207400245121400f0106002c0240c4c0840d4441401d400041d42c1c07a202a001082840c03403071480d0074440e00800e400d40c3c5082c6550700e022003042c0281800d000707690b84124282c9040d400c5942d00d4003402012410041001568400300d5910303000039298a5490703407014040e54030300c5800d01c034001d00c0080d00c000d80d8100301e10079030042c007068002811071004241074542020340010a5110f4a042c0011400707407c0103550302504000c030100e44210f8801d813242c460304a00d8003d100700c6030144401c3e14040101c0c9580740002e068009035001c2c1d14008c290b400701e0b400c5580c40009420703500206070f502302c2e04030180c80d0050984540c290407212031403400b1006040130072a8000700c001a140d04850380002500030758006c035070b10780c80b0b082c1900880c64180ac41103030301c04034103107298540120001e4594410000441c0c600106030b001c8001848005400101ca000c0940100003d000204400170b41004111044041003001c000104080d190b03030040d0440d80103640c075110b45507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 455304577 1250 455303327 455303339
    0x12020309030c0604051012021b01090c0b0c060a0b01210914010e1f150e012d03060f0608011802031c0503040f0309050901120203060f01060203090105090a080607030501 74
    0xb480038102507106403028071084c80240d4500392a085d98040130b00780340c4d111a000d145440042e0040c4e450380c581d14111030204540450064020400f9076100742d04041440391500c0d40491203028070342105145502c8480003441e0084180c0c0a1114150305045c44082c0075415540404012005008000c030140c40f00186010070120461111920300b00d040240110180380d1095603403828110105600310600380e0b000d8218040c0c591080100205940c500b800c103d03200c800800c4200400e00c00c0700c81d241d60115544562688134003c9103100f91850324043d400c0da185864480240100580d00e15400f903851000040343e520902c90100d80d1325140005000d1000303140101801d01240c0385414811704000f0040e034100c954008112581b02e98042c680090203441030a08540a8130b1782d820858000d585007001242d88072045c100c00150a00c00c400321855030ba40c418404500e41000c4c4070703040160b803051084010329170050000d85940100079000c48402c40d51452107524290f01a216040072942d02c400601c06 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 455305827 1250 455304577 455304583
    0x1306090b030c011e0903060c0e01020f010b030601050d030315152703080f070b07020601151707050f070519050106240507140f1c0c020f09131202030903 67
    0x1000300440180950310740400010700015049a07055107044400b00245010345e01420342e0102560700b0031001c000105004c00c018201000010f030380f6025205000c04070b145d40e5814040c3c0280b00d000940600516480e241c14000d281da18448101d0034540c035605d0352103e0f9090070018500426002d50b940300d194043e001c0107042d0808051a803050000140701442d40c2c101c403049804116035200d070315075582d2401c0020072882d9000d4010010401c040040501c019581c0c00603805041c0c84914980241450400c8400d403100c0301045100050245900000b8a0b078030f000b58041d18801030752102103850540b0a0342c883c0e04100c007105007940020040304081c0d0502009100b020082c04030744001080c8404c600c0781c0c40000d600132126240c200440003c6160030018204940780920700400101c03a000c81b0b40c810304648540310103140349001c40c01c801800e180544900b07442521960054810000152810103200401400400109004032000c03040ea00094113500d10b00c80305141ca9000d151900744000c01c041c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 455307077 1250 455305827 455305841
    0x40e010501090b15030402060d0209061308150115080601030b03030f03100f0b030a020307090e0f040218060a0603110c15010e0f0c030a0203040309271b270302130609 73
    0x1301440c080150b45402502d180c0032a074010340c0461b010340d00e80c00d400a20700041d1081520b5550094004100a02c7d140c2c9510b5540081c0c400721400e6401521480ca001d03541000240b040508803d11145901c65140c01a16455040001071401042c0343d194540800d146501c02544410001400405c0200046920726034001800000d0940c8072410302e800c040d510140009020000641e5000010505d42d9008864460081c1000b11900382e5a00e401c215039250010200d41c140e00502d00f03030402c0c520b143d01c4503440718030401c401803001300e2081c28100110020f01406804440132401009581006031040205081e40e420620001c40290b04214400480c45005844544014800c106005205104c503081e294003220b01d0000507103d6a40c2e040883d601c00c00f50344400307100b80d02649128480c0c0c943d102d1182c3c08000c03103441402110b68084c1040f4030038604154990000b001415030044400808201c400000150a018a8141d0302e0350002044101c141c40401d00441c0d070b50b1410046000a40a091 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 455308327 1250 455307077 455307079
    0x30506061206130f0903091d01030201231b012c10050411100e10110a02060c2a010e030a110f011709010e1509030406050f09040e010501090b 62
    0x1504001003007040c201074003009007034244124102c0c01c540400c049181d010440003d13100c48244056060303810040c004040d140549000100c87e10440307407504c13540c0e481d090b040780d82c10b954488641d1030035111200380240b805200c801903442044015000c400709036000c08a1040c440002a0a503070500078030008920f07030bd01d06444041800300003590007801080b0090041101400400c5a959624065004260380084a940700c051030305001041c030340c40400c5c5240c02c0e0342910016481b900e00d100507205d0001240800c003d542c40003035001e0040c00c1c0000500900072240e4122420a0344006030700fa034080100c00c0d12a9500000400c6481d44d40c2c0c4500c001c00800703c10740240101d0242d541f00d01800411510352613000d190403030301c00015a441030b0704840390b0a01903881000f03c1c1c01c1002c0c61a010b068941c040112622500c0f00754884440e019902500070160880198030300b6140000a8909820051600000104c184088255503c60380501c4540c09003200001031190b050103c0700007140d1200c0318403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 455309577 1250 455308327 455308339
    0x90f24090a1707020402040801020316030605040e0601090b040b1804020103050a0605030d2001060b0702091b030a05070c0c030b040b0708070c02040b04110f0c0c0312090409170408030a030506 84
    0x92000300305081c41c404519484402e001c0d641d41494008100030348116400803000f584004104050200e40c0c4c8150902e20340c40d07680c00d0056076664002c00c0151181d51144480a030408801001480c4991703011403220b280241020a1103070600001481407842015041d011001d004200011980c0c0b51141c0c1d5032100c0050400c202ca5410440880d036940542d80e59041402100800800100d8440e009121061032040081c0152525207541040f03d801c03e050481c081c80500000c40c0b6451520315012403c0c0111104150555680d820000f000e00000f6000c5070511516101c04004980c20013101406180251040145401c0ca840c01546a0000400507803c219403501800440780d03001504411300c940440d4007141240801340094000d0860b28660302d50a507000460850144810010b803501384c0000040e80e84c071101c00b1003455215240002081c5201004001400705480c02e0340c80381d44514002d2459621503007031003407414056440750b0000348095102050507154070307605000f402d5000100b0380348 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 455310827 1250 455309577 455309593
    0x11030906100e0411130606050c150105090402061303020907050322030203041e080a030c0c09050402150a032318070e0a201909050103050609070503090f2409 69
    0x100e01c0b02c100010f40001c18004600e840c2d0590fa076141c00003039011140c001400c00c20b49580b06006852a44450b8032000c41d400303241d030b04002905141107154121240505018007655856081040d15800b0b800d9070107201070b03620b9012026031241c6066501c05c001a4a03526620304081e100001200c001c11001441c074180b0010388000a0780c048191011292160616100035941110444180159401004441c880c0841e420113151b8003c111002d001e0290b000b00848580300e44140d01900c0040320040e4001603900d404004100319207000f0069a20030746800900c113089000e1040f0002006040705400340748404c1440354000c0c04074502c900091131000203206040c03410508280e2800c0050204100558030808842d07038030560074148180c8801800d020b40ea80041c0d000195589080382d0b00400010b00521022482c2d501a214240c0612001480d6001d2955010000c503465030004040c02501d00460300c6031390342910200120151b460f820116aa81c90b507076503044d68002c110060003400c185c3c0c080b40ca = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 455312077 1250 455310827 455310839
    0x3050a08010506130302090c1e070311160b07020f1e031605090f060f06040603020315040608031206061c020c1c050d11040f090c020f01021305010e12011103090610 72
    0x121350011240d05965003a12940c4500b101e42c418010020010754a4803624660700719000c08800402c4082e11a456044400075006000303642d03415442c14042c400d807100301040c840d29245002800ca8544010103d0809030342c1e0b00040342541200d1a02500c140169024980c070310b24041c004803119861207484c940340d6a183c9070028100901c043c1804200c1038031400400c0d01511607170380307881084c80c1c081c01ca25a11655903100400035402107900000e001e2040481e03001900d018000c83c0100c0c0c80b618006c5081096441141403c90005828540d101e641085030200e8400c000720604c240c41800000103840d0001c041c0901c0c01c00380380c07800184825049c103c140c586190420280d40124881c003e000071554050b0310305110314800d681003a005c05126042c0006c0c0ba9142e900039144400455098901110000d503000e4241d010344644080010b282860520076540b140403d0180d008004040340d0700040140c20003400c540262039001c1c4203950000c100003845c501000f00c0c94002819003418510706107404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 455313327 1250 455312077 455312107
    0x203090c010c0807020a080312011406030403030213080f070320090121051207051b100e190306020702010f140703050c1524010302120a0c0c0501060303050a08010506 73
    0x10844078140620514104140003403401a140300b258054444080039803108101e035581e41140c201101c1030f0704c0171f0700049104002c640400d120844050662419a1295070707055029401c254280c80c409588004c1c006002a03042220160004110001c3d05d11181542015240c499903035000040450340011000a00d45503541c126044800480740340395600004c03841c001e0000a0414081c0051044002c4101f42404260041a02a01c40c00c01c54508105020f40c3c91014100c6134001e0394003192182d5442d0042c2d0107000c030203a034071000902d86282518a11959012240217030803d4a100f54003081100440d608070404d803801d03c5150400041c030305030380c482c0200184a410001800c02c04042014040205c04014180101d0283c281445007494481c1071280e0f07610f00b40c000032050300e50380786c40c903e1154000c0c401c650048817441701a5840c0e070b80d0f82210744090250352420350200164400380a012400a21500b006544070341c0d50203540e000c1130b450003485d0f064184c0106e8400c0c00104401c100100302c00d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 455314577 1250 455313327 455313343
    0x60801060b030a0b031f0b090a0c0819090b04050604111207050d020616051005340212030a140c0a0206040b1801020714010e06040203120c070f0602100e01020309 71
    0xc101c0204040132810003207420000c034032810311304115400086a44400407500f000504903410f641105459960020319020380c1c40c0707207034a00301044658000c54814004031002d41844041501701040b00301440e52a5440140122003d5448c0c3e00040e0503c0100700b02400c400380c2100080303d407441e0b92a50b140e4082d880e400940304840c13107003020000c41c00071902d9a4094031034540c500e001490308080743e41031161711030125130744119405241000107282c20203081c4012480c3c0580e50700d024001050140a210842c3c0c0b070707051131f1003540710ba022030103562120704006510071014003001003924200d04c00c040c194001c02410140d03403048184080544194001038099100d5040b003050740d02c1da1600c6142c034000c0d001e011443c44295000042c1c55040c0600919072482030f94441c4000c001da80d0401c1220764586134103031030003541500685020800e0280c2c1d2005000d170f02c08918143d546440d070b51101d11456440c142e0001d000358100750350a0f8160003007845110310030030f4204020752440c40c6c40c14805481d038240c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 455315827 1250 455314577 455314591
    0xb06010c0213023a06080105070e06030406141806060a0320010c02030f07050f0a0b04061110020703031407020d02030f0703120504062c0c090c0702150904060801060b03 74
    0x3020906095882d031007100d6002804100003064204a2401300e00c440e4041407090740b12585041010000b0608014030982d0320440709030392210391041c040820041c4a0384094029512645c941034107206480001000c41d0195598000f0011440441503403141230040c010003d503c900514642000421144000103030030103400c03001d05003400c46100050366010700700c91020350148940951010300c01d00001e540d0f001d644044400740b48030885a801c00c021032810f809a800d81103002e0108000f141d02561b0126080c3d106801610b840303e07950720140f8100c2e003260a00340d00180e100c1c81c58800d001c114506a940040640c80070380b2030804070060295a9220b807088001c1321460000700c86040c5482810260b40054040000340710a040909202c40685000c14003000c1c0c0d4080304a540e074401017101c22008503c0021400360405001d404200300704288020010341601c90100409401696489026041042014080754983c10301070184412a0402d80000825078942a418402c0303262040a81e607020031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 455317077 1250 455315827 455315831
    0x6151005121005132c0f0f0d0e0303040312030b0328021314070f020c0406080105090d09080a060f140a06030510291f031b0f050307030504080903030a0c0b06010c0213 73
    0x180c01784807103140070100101701c802e500550706521041280803a2a00344a1411b40d0742c030030307542c2c0d03204101900c91040388030080c2409400031101070424004d420201600d4001420340300305a45243c0c00083c1440c0460f00103c00030607404c681400c525014817480e0f5260704101d41004003500c500b40443c2d80ba40040d1100c014015040b200b094050310070800002000405002400960707982c116260203450140c1d0301c100d41c0d018150107840000e10403010390085405000051005114035103480c0e0041c14941307249050680c803241840a2032480d180594021601982c7c001640e5107582082801c00c0d0a0b82c80c80a4614101300c0c1c0e0081c0714100a03240e402c19002c607043c264100340030340c0c0019500c443c03407402e03d111480005541a10a60950310000c0740460742120028402400f0000300c2c1d5131240042008045842400801d209601c00d03800103070f0242c030a49003d8034020402c00001e107581c100e15151300002c0c003049603e00c10002d0703103464660800d40a003031500541d5026400541c25010450170710351110703 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 455318327 1250 455317077 455317151
    0x5220f050106120b0105030c010219080c030d020c0c1815090604090b100305070501030c050a080709170d090f0501020303060d05070f03080909090615100512100513 72
    0xc0401e50000c001040515000e058032522840d04052481003482814464062010f820038036500210355030607050b03110408100029110741c0c88195542103030030500394501c024002c3c000e401c0d8441c4000d09900403c6002006031598a00070014140084400c01808400c00c109004e01031440409407010741c0001c0b42c044c0490ba407607002180091483d101d01030f00310140c410030710016808582100c0d0070303607002e071040d512059142d100560603121001214800140200103184280b48541d41603908126181340008580f5030720903484260000c410018003851b0003008031000c1c0240c100764860024640341490049140c5042c0000c0c7d1680001400035024240c1004007600304071060100c0005031148a442c60b0407240c603802c014455400c03544102c2e005901d46400310b0710100b4005441c510503a07000326009004440c000c1400070303640d03001c02590b09000f01480038089040c0d0380702000e4400d038482c0c0030340d8440616083c00c129021010380114002c07685802901e070b109000610300710342003000a8021704010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 455319577 1250 455318327 455318333
    0xb042703020a0b100602060c250305090a06120f0b030c09071803060902040b030a170a171609051c06020f040312030902040b011d040504031e0c0605220f 67
    0x40b205001d00188101411020002c0d0307030366070302681410788131113070708455059442d500348403d18070400000d00880064520141c10f190b0307008204869851003840e0281c105500310340800c98810164014002140c602030082c040d051003807080c01400d9000600c2440300c65003e00c080b90b00c0c1c8881c191a240209509030002e95080d0007102c0500c9490841008424201d959003001e1005000e03100049100e5420000c02054924001580001c4581c2000903140b01680350b10003002c282e8001060081444810000407030440d04582209110b00d0190202ca00d429a000c01c00502c0400a60052441110074406002d80c54000f1391150050540c45640140e860706c0e004075094803030141d0350008044040036515840703201e501d50030249076184213860500131244c0420040d0b03042481104011700140384940500c0003842d00307800642d0894080d003020b8403041900c007001c2e16001c9015a158000c90644180d003000c220b00b5100c0c107640000c0a16541c8204a04403c48138801c03040141c018001d994400380300814 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 455320827 1250 455319577 455319583
    0xa0b0604032102070e01050f040504050c06042304052215050c0913050106050d18020423010803030118201803070506040503060f090705031f0b04270302 67
    0x55034112810b160408078800300000c61100200c005001800780c9100003800d2020000c900c1e05a41c1c004120400078170b6628240401410001c02c190b606209150001a1035102c0000400140609152100f0305000c40441c3d2003210201d06881b9000b50301e0a0208401500881c0140d140080040c528515601050600c07885001c01d54200b0601d036840d04041c085180e414200a0601e0b4000f03540d643d90310710725454030030100e6001b481140003042c01000090344022060784008112101e26001d070240c0903154010404540340740d140303100c01e1706208a216815114841c80d031801043c204004520b19030500c03140282000400c0050b41260f07407140018148880038100c2907040a860303001183c1c40342c2101001e41120b442c5043d0107402405a414040380c40d041810032141994030140007408151a070b034148080e000b4005041c0314903405441c43c0401c0700c5e80c0038045242c4107800d10014052410b980b2219008550340d10840303030b114504c2c0c88507444803200d01404400b5801c0242c0c0301e01c614809a4201a42 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 455322077 1250 455320827 455320829
    0x3042a03050d090806090c010e13110f040e09010c020a03111c031d060108030f1e0f07060f150306021305030717010c0206010b07083004020405060a06080a0b0604 71
    0x1280780161070900d01256401280f03039080b03941803c102d07510380e120b03903030f145445102010807903000843d407211014807402d01400e003000800c00305000041012001c4221402d6070000c61284031b0f10341001804100c1030850038103540d042a0094000c00c41c1e4842c0f020080c3d940c0c0d5401c2c0c0c00801b4004207404152542e00b003405010403140601c0c0c001445416991401002820f038828581061415030008d440c56640018881c0d06840075400210b182c00d810003080c10568010490402d81301c0030b03903001400f407a00d41d130000d4851003805011003902d800403440c02c001070718009101da94031a031070700c104020a90040081c40c01101e400150040e41c80a0031805001c00c0c210580105401d803082e4000041d40010340b1804c12006500c8100803c9031610211b81240c5800c82031060990b070b400140300b24004644094020604011014450780b00066100c8040420700c0c0c2a12460480d0100e140400040d41420700406900003030803541d558110b07081c250007a01901e4050000d02c90580e6803030f0107d5558440e10201e070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 455323327 1250 455322077 455322083
    0x30f0903030912140f0c010b060703121107030e0d05010209030a0c030c0f0f061206090603030c11010207122d05030a140f0a0302032a0d060b03042a03 66
    0x12005404030308000e4058008110100c440f02e400a855101c0d007407050070705055546000858a1410180c0440303250240c00000d6080d50b99542c6009400c100d40e9024020105942320f81c45040da0007a03060011401c89200e10310000e081c000070000c0d4800682e0262201c0c3c0480011150074046051701e040c22402800342c5210b103601031140340d40c4a0217014100904200301c91196a4a00b40c15840d6415034400303501c03622800d214080056414084030f0700400100c410311801e6180010205d58801c801c0c07094604540c13054022880100000c820b1090884e0360100301e54082c001040c84614050390110303400d144070000b4040c02c40c08401c500049080004101207021038400c040400845810180e0312a44a10107250100b40e148207401842c104000c00c1d14015481b4030440c500b810038110b400e40c040d5000400741c01100700184001800210303164403c0946540e03800e8025200c80e12410902c089520907044102044e0f828401c1000007650520910030344120000c48068074804041400c1c1c04c04000c0d0030007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 455324577 1250 455323327 455323331
    0x10506031003022d0307080a02270a06170601080d0309080d06031a1803090607060b1f11070b070609030c12030c080f0906041113020c0601060201050709080d0f030f 72
    0x400300e13004107a007401035281c841400d0481c5600d501010113075140c3c0d49105891a68102803001805480c2c40341e2205060b4540b04000c1e8540700c1441800c29025800b282c038a1300f05559100103000c600907070022150b1903001000240304c95410115030f9541e5800b8250b0a808251311100300034100300c030303001c140c4400040d40c17071040c40110303164601001c0d410762038a0800b00c2501d1031000185d408011000302c0c02c40b8034003080070f0762801c41d500d8140081c2d0352180c5000c3d01c0d80c07502e03400742d6515500c07500c1400d591580c0007441e0101010000100502100c4041c031500010b901070300b4180700785103400342150b075102e602040015441186140960b210702600c2400780600030614900f03841e003034040d0030400c200407003607940d0125a52800881d110008081d02e440f443d03548000c001400058044511409404c4018818003000002419082c02d90f40a8210f52000307400440041084503024010345411400c1401c0c8184480e0a01c00950341d104000c0302c00c48100300050110a80d0b00303002c0d62211600c1104c00e401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 455325827 1250 455324577 455324599
    0x30d2a0e130b062d030c0304080702011106160212040b0306062110050f01360b0c1c020c030a170d050a0203060f040b0a0e060303091210050702010c050301050603100302 74
    0x30102c201d110036505100c1c4d100942103805008456008a9210b465142001d03030554965407542c21540e00040d800301d06101000e0440402401c003008032510428603945104c02c071075035803e0f009040285001409034a1103082c0700c24414601c2c5081981e42c40035041da482501c503000d00ea482000c03d0f40300082e0b150f410f0f031380c581440f05c040f103042c2c45c0e441650010b5810402c8034903010f00440c0c1c21200700b904128081c0c1794507074a4018692544601c01c1c0c4040202490a0540c0c4a1150700000e0f8031402a03144203034010030615261452203903120b0781c8a040c40c005800201c2a46d0040382d00e030402d04100416480d05080c103041e60907030302c205440070703010050070801c4a41b030090300d640020360042d40d040f80f0480801070280b00318034084c060400c505e0b0020f04040d01d040e1520060010502c8007030601c0d40d150000707024410306074503800903802401901000800c04e50071054010030803524003800b241b08690600c400a80102d4102e0200e034111001500c43c2552981c07042100f0480b5071094000075442140404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 455327077 1250 455325827 455325847
    0x9080a020a261606090c0b180a1a070318260105071409010e1302070b0709030f08030a15030308150a050306040b1305030d2a0e130b06 59
    0x41d4007609601c42c02d0036006400ea200e0000c41c10784103880050040b140108140041c100380705003401c40d43d5120b800c000c00c0079942e643d1844054642c54210040c3e10b2000304940c1d079103001e5107101c1508a881035400c1700203c3e00307185102107400424a2480140000000c1060400d8070446080c05000a0030840c4171486440d401003410710311801d0000043c000c6110300e02042c405040c4203141c015045516289514055840414602e801121015041c003140c49140001c40c3c9682100070754100103070500590303c0c0114604502c1c21500a08140b040001581050000500d41c20300d20342d8603a08804c5403502c0360349421044001c0c10015a6680c00740384814000010140c11824090227001081100d0018440b1202842188142c034403802da0700d58856004a004a4560030000b034100c2000300001107480b242c0d1716801d1855010568100c0b10558610a00d0309010091100d105034422200c21000000c8071401c000300601c882200e4244608119034000485420b00e5100000001c0040c10143c3c98002e840c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 455328327 1250 455327077 455327083
    0x9130e030910021c0f0e0303041d010602030f07060218030a0b010f0801090c1a1b060601090603091a06030309040e210a020307110409081204060e0309030a110409080a02 74
    0x250080e07000e01111a8500308440c0041040d203480c15016046035108683d0490417240d44500d031141c101030000b55030603c12551000d2000303101500c012420a0111084060035009031603050740304d2000c6400500000ca02130760444110b03603030a40c02c03040141c0c0b903c0e20002d45080610100003c00d03454840c880c004010007034481d520314100c5074000c02c01a100341d80d41c2c1442d82680d42c00e403801410600e80708418031059001c0707014980300c40303840003646050450440e0100050f0340c80c40304404066022104129040d81d014140d140030304141d103001c0c0140c840d02e98034403000c0da0040c995a6400d84081e0001401070301c0410645014400007030044c40030034038900d281511000c1543d08010400e035911303c0398102c500c0c00e00c211010008258021403038070446468420b0000001c8180540c42034036910340e9004180c51001403d03076400a04101307182401c151400b08110760142103d61036640081c040d0b130145176004544110700b0340d000802001a241020001001400f55a00081c07c00c0408940152525800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 455329577 1250 455328327 455328337
    0xc12030a0c121a011103040807030c090b01051204300905030f0307170c0102070609080a020d1d010e0d051903020601080616050c030715052205030702010509130e03 72
    0xe0302e512000b603072203411070740540740da40750440300c440d03c042c02c202425407198441c00100c56241e4166410140c1315070641d400c0c6105a88290b80c208e9030400c003480140042d100b484490102405c015140c1303402455482d12a4900400144c128a4021a48802e201c0a651409480f8201640c10070381507104030000360600c03850313000d414002d2248207004a0303000070004c2120ba129400c07003041455241d07202042202c4e54001c41c04c01c0c441c0e540238000300001403c40d015130b5130510f1046680c90307204d40c0c0741040286000d03070a8a442c01045035250b40b2540307003600304506107000d100a02c0d000c81c0c5404036102003182c2040c1200010524810103900c0d540c40300c0d000200f180c5a5100740c0c00e455490341c1c0c0c0c950450340ca1109550784081c0010221149030014000d20003000c010b660780e8203407405c003545511031036588884040390346004c9894000b00070140202c410280e00c0545400c900904001450f29429500e0040c1075000741800000901007450380e480a030300d070b4140010900300f4408001004900c0780c40380c101f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 455330827 1250 455329577 455329601
    0x6080108010b01050c0a0f02120a0c061202031b030603070b0c0307030e100801063b030f0d09030b040309030f030509040f1b0c24090c0f1503020c12030a 67
    0xa01200240c0b150b01c2a011286200607640042006d00c40a417030b20329440d0341500041f40c0c054800f00703142c50031100030311a007041c00b4058529107a1240c80c01c80702138602c1e0068050126028410001c215000c580c8100b009220041080515181d584400200c0d00d44592074101c0003807003001040c42c0d0442c0c4000401401a140300741d0703410203005109000c6c44200c0350b03400400404500a10010b0042038400d05106048039540306240f0306090540f618803c1802c80e110b110032145416880110142c00d0402034454104405c1c00102054424100010700000190000030504030b501300c080380515105906401c00b640e00726003280b01c3e15110f1302e8081c04030350201031303014029414461124448900e912514008003200e0300c0c01425650515802c40d08580b0b88003046440d0040142a9a2036100461110500104582001414800c0c50414400c08510740d070001a48500442003802801420094016008254180540c684403e1480542031190743c105004045102104011040d806908061714000b2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 455332077 1250 455330827 455330831
    0x20d092006091804030e0d0b0615090d1407050a060c050106050904021c0204270201110609120d09050105040b0a0b04050c09010f02070801140601321b070608010801 72
    0x309506015060241035482036002030180c0c00003000d9042c10b00d40503442031091130041740002c025400201ca668100d48265020383c21203080003101c0c104602d43d40341c0c04240c402e40600b4030240d00b0014003072443d0010010014601071707040b810303c0d890411100014100040140990075240c0130000c101c080c082d44140ca096081c80c40016940c2400c4920900442e006401e604403109040b25280f9601c0c28110203c0c1c00540c0c1d412407070391b41e0310841c0c4541d032140502c45000c03401450b05d00004042270041d1966000b1030f0414002d122004100090340000782c0300100e015070f01c440d10345201000034291088090020f50034101040104007100329103a1080c00715030340c204480044002400100e80d41201c12801d0100200517004544d03004201c489045800341c130480e01c0309a200d0240390700750f0341d00c1901d190076180c640060040030340e0080c00b6000742c1082804c2d02c103c007002d040103000c8e00e40d03c2224040386140c3d00046104024000941002210f62110200c0b501181da071038005051420034464100301d54 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 455333327 1250 455332077 455332133
    0xe030c090109051b030402011205070c02120f01060911030106080612070b0310080313060e06070c0801090501050c070b01060c080d14011a0a121d190b0604180312020d09 74
    0x405000b45e0703014507010f079540d0202c9800d40f1203490040c607014040e0000c3c0704502c80341c100107a44000c42ca842d0401114050700417001855a00c07030955a580c0c0000050a00f420300f0152208004001c2d24115150741c54584140d4890001041c0101101101000326018061011511a0b07601004500683d01070001700da09603550302d115500c038000c8403414001d910117908100042d601c00c1014042d0000010000d80c6004110780d9161000041c0b98072070070b916512400c0540510000303110b100d912081210000e4074118003941c600101a00502481060180030720900e030a1001400039500510040b580820004049520481c070381c800c2481000e1013020001052807180c1855020b8440b81603454941c4003c80342c0c02800303034002d44042100c00500003030070071846180c140b0421601c0b00344452105902482c1c003041c10714103100c40b40240303c58011800d05001071703880241071010740340e4244c0520308886510880980071010744680e5071442c130038900f00881d00091140b141094811002540b100c03030303880 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 455334577 1250 455333327 455333371
    0xf040e031215060408030d0b12010c0809010506120a0b090127051002040b040e0a020904060f09060b040e0109020901110601061101050906090a0305070c030507120b06030601150e030c09010905 84
    0x10340311342e00900010f40c00901074200d4054141e00001da0800700100071030b6654101207441821942c0e03001c42c680000d80f412043c011240401e00c289904075000395011080c03035400c0c2d0311480c1d80702c011076401012003e041e800250300c88003c0d84031500e00080c0f0f8500650384250b10300d8601020300801000c0c1c0700e50055103d58991041a8401c6034111014101e2407820a07240c860658610340005014000c0c00e5004c000000a5035600e00c00c440c050b2400d0300c18111142d042840800446101d9002411091000c000a00403459200c401904440790b040000da43c441c407500041343c4200201d02c080e40144103410000c500c1c1138224846145003440c400080006540700340c0d504c0d540e428140c400300b00540141c0c42620101c0e00c0740000705070040c065800080c402d0380c0da507100c91510810368810400b41c107015045100b08001d11000507007214003100105400d504000d9211040c00b82d14483c002405010102e80320302d500e06100120b0300702001403c0c849a503a64504a802510741114000b00380034a0408820328 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 455335827 1250 455334577 455334589
    0x70e0405152101020d14070c02030619091709040e0a0c030f05150a0207020f040b01120b1903050c031603030212070c080a120306061d0f040e031215 65
    0x401d00d00c1d481d0001d201410002445100300c505100e80d14541c101030290b0440359800d0006000b007a89101e000205a03048040240381580050710300001c12076034240c40005660000740280d0005460841d04da181c0f4580200000180051a8018402407002c1e094803051800000a0254044161030910100c11140f5620b43c8800603000000c11580326540203001249009040796851441103080ba0202203003101e00850548007110b1100e44941c00003030384000c608007030a14100c0002d09440602400d000d060010308010824400569407a9451650030b280303907030704400e58031240022182c940200d9100c0c1401a100c001005a1303a00a1050b00c49a122a401d12048041202d4150b8040c10103140562064101a40b0158060f1035440c9443c0000c10b2448060040c1c10005200d005041740a00c01c075a4060300380e03000e65120740b0078000c0f40010701c04480c01440307230000c090404583c941032074040303500060010800a8100c01e0b2621000c1042140c500c204070001e0302981501c001c039600069410304121b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 455337077 1250 455335827 455335831
    0xc0c021c03032d1d06040516150806150d0603030309021206010b0313020301061d190e07090b060712051209010b011b17030a090606091104062304030b070e0405 70
    0x2109030115440c502c050180d584079015080c8110315400c14074107000c400c2d40c0b600c40300741e50a5803960022314082040c03100c2100d94000400603e400380e8074488103c500034042c1980208060b0003a5034a480342812481d041c011a10245000c0c0c034200701c03007505d03810700500511a480b001c900640b64004c01d1070140f5400076040f41210a01d00e9100e140d61303540f034030312020042d201c0001c030303015901c072007010030310f01444e00040e5694031000059060514220342e00071900c82070f0203490088a841c24203400d0b0080c102203148005e0f5a070285010802c0341d841c0c1c0c00302c0d00c6441414030140402c84080a6a00040da20400034401700c111211a00d003161901c1918508a92149241c00e010035064100d03005110280715480704802d0154551501c10b50812180d50036076802203400d850490303540c104150070000300d84260b001410b4001c1080045400010681001e0b1085000c1c40d018070552250300000340492284414685101c00e00c11512a90390f407810344910102031341c44030b02050840b0362a400c14145489424 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 455338327 1250 455337077 455337131
    0x905070e13060b0f0a0c06140703050f06012703050f0618030309060a050603030c0105070e010f0c020d0f05070b160b010e060904061a0d0c06030b0108090a060c0c021c0303 75
    0x51401c00c4028291205600024281043c040403112050100300c075823040500c05006407813500b20317500d0403440060403600010010003030369141d4800d000203640d01020111242005200c0048404200040c92510a056510013000743c4241c42e0b0710111501c0c0031035094000c03a04800da4460058088903104d0712030008640200e81c40e44843c0016141c41c500e90412a041600502074074a4000c0d8502410b0a44408488070390104010049914065901c191603440030415460407212084031540064207400311440054151424040710b8424030070240404801460b031070b04415901d04458a0540752140d0141041d2101c4900100002d41e034451002c07098403542d0300a182040346d60311030f42c410004042c510300070381d294000740f5640394041d20381189800c00c0354081d0100c07480c9540740600040988041c00100c40c1040107070ba007030180c07116000580c804400c0d4420404a01c10990130401c03130345110075100296100104070b02030168100e8920078011214042e07a0280400c25018058429070740c85807440c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 455339577 1250 455338327 455338349
    0xc010207030302060606090103060b03090c01090510081906080d110115270605130609050901020909071b0b040f12020304051c1e08033c100905070e1306 67
    0x185c492508130f000301910709050400150098540130514416001180c0003051079115400c60310341d0350b801548090040c101155080048150164020041103015040050004148c0d90301d100303207465904041e014044070f00407608926074600d07006000e001c070034071039100ca07518105041744076035401030868069419034920050340025900c01410a607451001100e40035030345040c04503e5980b15148029495000355012412030304000c2c0010440354003401c540d6643e80304000c86001034a81150f0b20768001d150307052503840c10360a08098031900141c030b030000704418445c03c20041007190500d02668030314051141c40104041c0036209a950f442140101c681c0203c0401003400b5040304c08010480107071250020682c8050300f50855046410005800c5a01040120400030400b01018001c2c16070940148502858a4464441000b480541d50305910b402c0c0298001205180b480b00c0301c00060541080c10019031400c09030007050304810501440c81042c101c0541119400f030780c010003003911000091 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 455340827 1250 455339577 455339581
    0x3191416050907030906060b0c0715140d020c12190806241603020106030506100303050409050a0209030a050105181615110a030801050103051f061202130f05030c01020703030206 78
    0xb000200a4028070070010552140012000901e41e0b000782d07001400d0400520f41c48541c000802c0d4103144280c3c00104003941a0b55481800c9036225104000004044504640d075025200103000070740720f04c1c40c0d01002071080300690588a00300000912007400c1d407607603e5540000782c80c1c040740d0800041c0c521503440131310181071100391401642c080f1008035021452078a0324801403e0820b40c400ca5500650143c2d55400c400c00c1440001e005659024002031118a0303141c1c2180e601506074003650041c44429552100010301c02806541100e40c1604010111000f4200c1c500d05103001c1d040440d1b100f0b00840242041e440380920004070380110300a10358041030792074200b8081c03244420b2564640c42c200300c0d110040da0b41100c814000402502c1c006d65840300d0740d40c142030024055132800b420307080783c900140b01c1d009801c00c04e03145040d050f00e02514001d56040c088240e0b06000c1d024981404645d40314000d80080c0000d05214010b044036800c0e011b84a11403418001682c40d030a41c2d02c805405a006500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 455342077 1250 455340827 455340829
    0x902150c030417030415020d020604030c0606080631031b261e0a0203160204110f09030c010e0306011406040306051f150c031202090319141605 63
    0x1030068200c103101100d08090341c98a600c188008003550b840700d1a0000a01888200300b40300500041d244503000900c180c0c188108001d54403000240080c041101594242c3d0410140b0380004000303241d0001155903a041a03600d408664915607545100c81150302c070390b4001c034400c90105044003038142c0c85148041007005006064050041c1c001c8400080021400382030086c05d6240980c00040c0c1c60f8003a40365031f45032903642e010112021800f0484074003071114100c40340d0300004949001102086000aa440f10f1000c0380c05020300450016a42d40040b4005520003003400c040d11800408a00300d82c1201c400c0710055a0400d100d408041e05a044240140301140c0000c01001c08061b024003c41d2a0603940c1d120b400484805949007400800041100d03000100c2201e50000036050701034041c0032424443c44041c16080709190700500348071202c0d00c0c200000300e4560580325019400350965102c5001d880e1100c3d800700415404448a22031a40c1d50b001c0742000069180180c91064201400305003004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 455343327 1250 455342077 455342119
    0x90f0f200919230d0c06031d100b0102060f010302060301030807050a02150d24090b01050f04030602031e010e04020d020d14010b0f09150d0c090203090307060f0902 72
    0x140c0e10b801c50002115810032550112036080204020141075080c4480c02550440e00c595903480c41d481049409a04008240e054081204403015400c00190201c050945403a4001a0032120048c0d4000c89450700c2903e03c03940c02120f00c4403001da003591001c4c0d8415500c86038800081c000a900000240018030024040600070190603002e00700315a90146142e0010308020781c4038035049042d034070200300b01040700540d00400069004540c8002c03580e210302c101080b118034240c45441700058903021107503c1039008008442610091103095030390b40362641040b2000e9032040d20307081d600c0540c1b48070034890054500c1200381a02c100620100c41c1d510f444d02001a40c040e01801640d0100c40010b0083c002244a051368500c41c00410012030300003062010048031407003103140c0a0048003801c3c01c20080031000c0500c50112039080b640d10110440c5030601d2400710540b9000201014400014441c0440c07001010f00140c0d03100710802d12021512000080c1640d06115009410400b00740507a51808141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 455344577 1250 455343327 455343337
    0x10051012021f092408190603050307060e0d0c080703030b0f180a0e0d0207030605070509060d15090b060304032d050903060624030702070e01090f0f20 66
    0x4111508440030400400c0060050303000d8800411072500d41000340c2e04604848507000c013131014104440d01580d0340e0143c42c03005c000f003900141d02c08081c11001c1008072036000501543c1c01004072030300d0b0394191800030003c0c03902011a0040f40706010441c90003e100b2201c002c00c1a03400340441c1c2c01c0501c0341d54183c0c06004002e01d240c0d40440e02250a030b0094840c0d955029207290f4080b180a91420301c070398107404035141030205411a81050f004420107580004030201202e078058000555961101c1c001c840c00e00409600550003000082d030800541c2054010058110701d1130501206150b4030030344582114102102e0b103070451418000603010a000d01e60390001541c0407041d40146402441c182c03420032207403045100200e0804500140b06040401c05550321140c01d172280d90141240395a2204d50080e42c1c400544000000030001e1215031083c070045005001170003607000030b543c440078031300007a041d802c2031084120714025000c0c0e403d80d00c40c002e40c51301e40c1c50295180200005110141d52913800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 455345827 1250 455344577 455344579
    0x30f0b07140706020703031a0616050c0603040302030a030e03030106140a091823090c1507080d0603050d02070b03130201030207020d0503090108100302030d050304060906060b0c1005101202 83
    0x4072000c0d0126a562000041c403400d4070401c8016a84c0c1c0c40b61401030202c0b401002414005061142c541c0d01c40d0700c0d4102103600c890000101c404441900b8681240340a40e40780d030b06074204c00013000744410075400001800f107003490368605102032a0f282414035a0380c0024410b010004500180e050460010600202031125091810640f401d8540c80302082e010303400c26150440d00e0f0790701c00c00750569550013159016082c0005a007034041c03c00c04107041e603941903441c82500c2103c581303022002c01d121403421540c581d030b0f10151694544032903000384002000688001c0d1000c0c010b0b030111141c2c4a102207000400e4032444015517013151100454540c114002a2040b41810b608202c1000560f82e00724114060782d20400040da6139860b5000018112440541020721400c85e5610a0006a802007103040c00b132500c9152003030f01c907a118203012003c2e1134014400b602452804d100803580881a00043c0756069401e0212200741880031030719011150115200c0c44910a80c520501101d4120303607400300102c4c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 455347077 1250 455345827 455345837
    0x203070b0601200601090b01090f050609060d06030b040b06010c120f0504180e0c010f0903110a09090515100f0b07140717070e04023304030303020c0f010501030f0b07 73
    0x121203030100c3c0088000a01d0094640e00c09001000000780e18001c1e10140802803a04e9424149000b801035950300300360103103038416200421100384644601e0b06556400d1120001844660390380d0900000d401d03010340e006d407544d060107800034001c1d5010f022640c00465211301070741038600344103104035600b0808605030801c004081000080c1036543c441a4002c15002000000d00355100c54106454446400785035418820034003950341e4405d0300301007560100d0744c101000a50a031184400a03080e2051038000141281c640032000f002e01400103880c618841a10044c0a2a603c48810b8200c171005544240e05008a2001c01804440004809400707214414004100c40300c0b0b18560705400c20300b003034100401d0060241c0c200030090360200f005034028204c80e100b4a19500701900400d2078184101e941d03145800b01b9104000a4020b0502c000300000c00740d20720261101d441c1e240c02800307980664000c116071320901040110801303040c42018100c0c0e0f4010401c03e01c403012a83d864414203030040c00b0000b402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 455348327 1250 455347077 455347097
    0x9060105073210150e010b030103060b06070c0e060a05150d021602180403090b030c090108090709020a030603210c021513060e091e010611030c03040b25030203070b0601 74
    0x94020800c02c150f01c3d941036000f0800d0740d80210031980018541c0d000c48083c0c0c075260700400186180c1c0003100d06494100c0000700d00d503003e103000302d003d80c45400001444481b034101d00007a40c8518040780c030b0007007500303c4002e0034040d41d8100f00304103001d51311000d64024904002d5404d21150507801001d5000e900c800c00f0448400d40c1d000103c03110405031100040313170880c1c800c203c101640800070744003a041c039000560a43c104006201154091560b21a05010315a40403503841c6004010030b03401080245410b641d503009015006010b0000d603c01102c50307038000021441180305106d101c0001c000075660300e006c481906e03000c1040c1d11031149528000e038441000540c1030f51000d0420317030016208903110542189440d40900c005c1c5600100b00600c0304c40c0103000c11480502041d03d8504440851404c203101c0d005918170b09040d48103280c50340907548000500003d007070b810324000d03020400140e0b4540a00521900340d602e0488512440280103800c100405d00000c1c00034034645410100c189080f880f41c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 455349577 1250 455348327 455348423
    0xc030206070f0201110a08030105040c051207180501030207080a08041a0405070e09010e0d08060312040f06140c06010b0706090501050a051f0e0f15060f090906010507 73
    0x6075005000690710060b03500125415540c000403920b088400e003600a0510b04ca071611003154902040c01041d1269031151602030310030f0b125405461404034001404080350400c5040a01a40c03050ac0c8900c841040d2903100003042e6000c0e01c2540c00c0e043c0c00901e0b030b40c50030f84040c20803070b203407440100f0450f1048500b080241c0607258130807a0f9480f60388208020110720782805201e6000c50001490044568107110300d0b1001e040c0c0c08292044440000e0401d4105074585000080c10300c0c41034101c10940c00b0001c01c001070761107600c04c00d42003140c0d0b182c1c542140c0c1c061a0400c0810364402c07141d41d90015482040100616405a4000d240c494003a440c00030700400d8556801c0c1c2555825244d000c583c644400a1000d84580300a41050f980075049043c4941490100c040003098401481c0a445801d1200020304103d071001e0801d42c40e1500800c01a5981d68030362002c4550f0b00000c141034000c0040c5000074101d54000c80c101d03526903400a1100380404104411a5201032102e000c80c00821814004040c0c1c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 455350827 1250 455349577 455349589
    0x611070c061101050606270609040e07051314071211120a270602030c0415021c02010b0603040204090510020409140a18020105031513020c100e190c0302 67
    0x2800240ea2800c0c10308902d0780020342918005040c1a2040317000300012000c680d0142c2c20803000ca82080c0740d800069131846d0001e49140121000d441d00542881142030001001080001c103482c403c030341d04588422203000329012a1000340030801c441c211070020800d441c0c018141ca0084004611010694940e58584081907400c40d00b0812640c14162051284045c114000c100c1c6042000001c0032100100b03640e13030b00c0b40700315018020301400d038004041050540303d08119400342c206e070034a81b03a0001601100940e138543c01071407011a005180010a101481801110000720004100c641161510b0b020000109a500011103192107040061960f461907400900001c00e805080001c0702500d000c141c0344002c20017801c01e011145040909601e0002000724040342c15028070300a9140d51711440d41c2c00e86d1540100789142e01c4062176041c1240b05032030340c0080244003c214203441124800105400c242c03030307000d840c005040d0421402d500c02c0d002205003829246026903031000c08640e490f008542 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 455352077 1250 455350827 455350829
    0x150c050909060409110112090c03030c03020d0219081b0618070e060d03050306240304061b14210a15050102031c0b2206050103050c09010503040611070c 67
    0x420008544401503203414091903600c00000e80d01840100c0c400c0d55081440118200c50b6414410b1509030900d00044540c020280680c0c090b0304200c086403a810301170015281040100e0041c03181524842100e48003041501c00c006000703102c21004c0d1816030395071615801c06060000042480010181400c004000b0f6074010701c0b44040c0c0780b1410000422450a08000b5080305007001118024403685890b61403911120075010328041e034490300c8400000d81d400702c82a0080c011520307000101181c8420880082d80101d104400800a82d110002c008905454008400001c240f04d103844140d10308091000300f41d800c8040c0380b1244a01d0001601d0401e058081d00e940381c2a80e5140003440704000c001c090403020780400d000950170f02c10a000c00140d08607803000c0741c003001070310f03140b1a15480e19900d0944942d840c0320740001d660f41c81c504441c3c03c014a07841c456580044d00301804034410b401481c04882c181001a990645180d0b0b0701e0b15400040c01d4828507161041104004a001041071660910 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 455353327 1250 455352077 455352101
    0x507060e041b170a09050303011806080a060c0816170613110903010f14070c03022109090a1a010318050a0b010609050901210204060b040f030311030a1b15 68
    0x1c101101c401c20f000f0458010400400c2c3c61500c5c00d400085003000050b170381114480361791070710070390803414441d00a850541d100d401a807107619950420081580c000114642442d9141e4015030b135002c07100b2040411100b0b4420114400040d43c0305030402040c03110754001405030155155061a13160141180c01c66104045044004101d24a582c40c081c02140b09060b0070007418402d011081141c80403001010b00254180641d4080706001c040c000d0006d214000707821880b0300d04140c42040c030f071400e5602111003203124461001c001409500c3d02d10441400726050401c51411b6020440154010403100111a07080d044080100c0c000400030040700c80c0180c8100194800d5501d010f10260040380c0c15006584225030510040c003202040100c8441080403803104410403007a07500215009000d0782c0c004180d071910018005c1040740030185140101ea11940d2000d5408502c01900d9440f4003480220200090503100c0c0b400004011111303617807456029030010301142246882000441e1502c240071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 455354577 1250 455353327 455353337
    0x11407140303090307110a1a031b1201080c01110318030a1403190206010311090c0904090503130902090a1512020304030c0b1503061602030403020301020403050106030c0f030507060e041b 82
    0x40404c40e0591b070740c00c0000d80c00ea4003001400d08240b084c035402c12440803601804400440007500040080c0b0142c004c0d80d00c02c00c182340c0d68141109000342480c2e13003401134050a00c14008900500d500c10707229032041d9441c80303000d9424403100030f0756160040043c41506a043c418400c5003008104603d5800c03801c0540b242c019035071065030ba00140090b001c0c0843c1902507410000c01040480c2540c040049454821a03690000759102c1c8007091441c06012401034009107003801200c2000000001040300c402101c400d0003082d5600c0c03d150b4181e201300000310703420510716041004540040b080340f19400c202401c04100c00011100c0580c101c1c4c20441d020740019180da2216418051059540354000311480e0052070041440301c0420340d00c0340c000c0c29158580d03402031a014505403091068501541d8002d00039942c030703562400c2c40d50217409a40015103079031a01510000305240942000c0040f2544940642a094604402074030782c080384c150016000381d01c030046144001800c00c041824031258ac1c50b9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 455355827 1250 455354577 455354587
    0x418050a05100b07021908010507020604020427020f03010204150309060c030e060412020c030a060e011a030703060c0c0b011d09010c1d1f05030108010b0f0114071403030903 76
    0x858251200a02089007100001005000e40d40300041252413083c0c0540e00a05041c4510082102501682d4001000c40d46001c0074066500c0d808a40345000314001c803824031890080743c0440010155200d54107440b00c4204600707000504001c0e545255072100200018206a50b43d990740f40e041c131000900c0c100095076200041c080058a00c11152516110b14007004003100380024290340d0840548050300341203e104400302c1844c420801d1606400024055404819180c505800644001d90305082954203200d860903e04100c2800d0301045035004004000d12480c5456410041905940480c01c20428811000209040121182c001c2a0100303d001101d0091111343c0101c1c00050844001c0c1e0b4100780d40e5003030143c3e12580450b010055440b55185d000c046400080700c4074806600c0120b5507200040b01128603030003d0180d8104d55812000307019060340340040181d01c3e584800030601182168110f81c00c948400030203000060720a03070090b000d8640388102c40d441c42c2c00841c0d140300542d0000071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 455357077 1250 455355827 455355841
    0x6110403061808070308191a01020120090910090606050a03050609060922020909010c0212070b190b04110405030c01091d13060e0a021c0b0714041805 66
    0x219414200781c001002c1c0300ca5441607910b00c25944500305000d8200b06d8404c0c04541c007000b22406800220001e030008200c8041c000841304440703510148003d01651904500165001d543d404204280303d00c0c0b5000e5107001e21110802c4201d40c000f43c200401c4145800c80401c01c200c00740b1804005d4102c1e901c400b0340741d07183c0c41401002e9031b0000701428060403141041c480e2a0300d852002a42154138042020006441d41210030340454510301c0280d84200c20740c0910543c1c110641c40a4440842d55082d41d004682c40c1d81c90b501c507481070860041c01c01c0400c10002d082100c2811007400c1350620000080380c1c410b10400004c2c152030070103444040b5113900140c100460700e020001d6450302c80303080c2420070302d807480c0c1a01803a8011081100c2c00c19403643d8030000c1e1203c52002c3c404240d1551201c420441e10304d1030054140d40f10307441f100482c000c0074a440c000420544068102c081c0e540c0c0001e00740055a1850310032610380c5000062110298014000410010440c10b11040c0d1040c9090300001d1501d0a40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 455358327 1250 455357077 455357081
    0x801020f04091d06040f2a0920030f040b060603130204050a09020d03090e0901061a070f170c0606180a0b0303130617010f0e0c13090e0102270109030b0c070611040306 73
    0x450040d03081f5200381d40c403022040c0d600c81000b1108070110009407012190f4003e11580741e1080c0318655008000104503a1100d109a841d028074010b181186a50351a0300921015100543d007664141c1280c50900006150a810244c0c2c00900c0c200085034014455000c01c07095807041108030086141000b080c00100c40307c3d899594007a421500a200b102d2800010032544110203510345600140003510744140001541da00709101d03030055081c2c031170300388410a6410343d421041003400c090040c040828030b07a1038000078125594503418603884d00c6032900c41c1d41c0700090001c00d0000b82c15010900c01a202413182c601200b00400301c94849814650a080000c0345c00c8405070016112450412401e00901014205495000d049410510750329140007034141000c00607544012802c60920314041e1030540107401030b001e4940c0000b0740d82c8403c0f05e0080b040600c8885036035080d001070400b940401c04a61014500e0340c011004808252500310b194a603082a6081390000e80c08034200040c6c02c00c01c0003014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 455359577 1250 455358327 455358353
    0x21606060801020a11071a0c030f03010b1e07030905130b040e0a170f071509020307060e040c080f07051806030a060f06110c090612010f0c090801020f04091d06040f 72
    0x50f40a0482e0600b0b0920fa003031030911403480c0314207600b00443d508c54101000c0084525032500c01b20700680340d617540e4429646540c010280700c090409103c0280baa44000c1350b040e1001503a041d01c40c51056030505080c82800c0e204d00c003290800640350107542c101529503215030100c1c91508409445003440c2401c0500380f00c00c02066075107507003104000c105000c010000954401680c49901c242c030138518111030001620880001a6050040c00e5000032503c2d044894500c1602c1d080d00c050081c803800303140c16221100c0444120340060114000203180034400c0f40140301e00f000d01d80344184d04940b4040403940c690030446030240d0b5240d8132002405034040706d640da04001c00d40d03458110400080c20903600e440d403c0307280005000d683c001020406940d213001d100c01400c20900000c00095186010070381c003504100c000100030070b1040b140410290411b008503a840c818030100c49140500e8521294020b000f40d0307070080715008a501c00240000c40902c0f2185c015401000c90203240c002c142001920350000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 455360827 1250 455359577 455359607
    0xa05030c0616030c150504060c0c02012102161b080d0e210f1f09020307051e03060a0c0f11060f071e0804150b03030d021606060801020a 60
    0x2000c0490415a40c445044504402001024201e1180545004d98803011401c1005104800d01d28009003191200d9118500c070b035008017010700c02e04100320029200401d0943d00640054040619040c0c414612100040382180c000b00044ca010610840800d214489540803102035000d0104880c5034040c4295620280c02c00c540901031292080340050080300b001580c46000b2003010348400c4024140c005400690300340101942e008594040c80181c03241074040500310070f0b0152001da8520b12109100c6e850b29694040d00400c100303401c080030000400100c0c640e4522485130110b4100c40c98400740400303805480b00040200d403020700d14030b0180540038414030003403c200090102c13044103280003401c9a0070561003060101c0a889000d002c0b200182c1000d40008144250b80c0800381e419484482030303114038050342005089442c404c03a403d040c0c51404c02c000351705606c2806203d0a0326180e80c003c0a403c0404000c4040c42c002559540040c0c0303140b175218541c26580403640320070b443e400c0700741c000321559 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 455362077 1250 455360827 455360833
    0x1f0320010503070c0b040c0b07050d090b03100b0c0c04061509090b0a03030503090a1e020111010c0f05180a090c030b030105060604060c0c0e10030c1401300504110a0503 74
    0x14143d1030080c442c2922200241521001c1004078080c03002025045028201510607141d5443d0300341070890b60354007c03064800020f20816400035100f1003081c00d03603020300204540305481d1454000302c161a03402c0305504102c540584450b05604d0b42d5140328035001001613801c048030398654400003030810070099110842c12401c00c0d9180c42960384000c2c0c8002500d0381420700f41e03100d03220101c01d42c0c540320382d01c68001c0c1038a1240403000004030161141d00c4899200341d031100c0e54500e03550116170903100c041c100e407000b00d00b540c29407050180c0a01d01401305814091014901c010040b00002e0440c00d29500140c0e00380d40d6101028031050b4180101c0350700c0e200590090089080c042d001c684588a241300704420014054200d40800990140340c400400340603007a8031007820400b45910b10300d0480e1008441103642c106000660086158a501841d401610b503c40004801404450b032b41c00c9001c0c010340c0055600780d84207148a52031052900550082900706100d01926050001042940d00320038480c5d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 455363327 1250 455362077 455362081
    0xd06150c0507245c0703060b030f0d080106140a08010302090a09080c060711060405070303050d0905010c180611030d0213030f0f05010c080c030402091f0320010503 72
    0xe076007894030b03c10024061030000d1440c024140408909243c2104075001180b11200000054051004c0090040b5901400a404990030f4404690000540c0b49100b00c5401008042002c15120b81c072500705404041c00b41d440c1079207001c1006d814401c03000c10401c040744801c001800210b92114446151b0342582c1c10740ba1801c070900102501152051000034407a41c81c660018110b00c140d41c2160700c0c1c840c1d000c2001d9403100107545400d0b071180011a1141c0000d07203201c02c0742490550024046010b0b50b0440c000e041d61600b180c404039610303480319808030030580d1200d04c4600015401d05c500400142140c4d101c004203180c080d002111100150712610400c03442140b04154900003104403200807404440050b554800d08401480c0000d0581c400381c070325481d607203a900501581081c00542e0340d10907030003040915a2171070141c0f00b03c0c41c01d61340a0207030b80c4113000190050403c0c004141d000424110314440b074200c1804100320a44007900f08035140281c01d290740041c000090704014000400742480da0440c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 455364577 1250 455363327 455363369
    0x30e0a03020d0b0916030c030b0709030c061d270a15090e0109021005040911210a090c06050a0201110f16110907080105190803030a020d06150c0507 65
    0x1042901ca000f030300a01840c0302050340d54008205001c040380f02045150803140c0c0e00d04040d2032000040c4001c2c0c9001c0241c000280c0341500c69400c2005890784400004902030900b0b4080701c03108032215090a1041d90018905c600c0e5807020701c110ba84272460303c424903641101c0580d5071000e540141c1f0b041d840e1340c104510801848a000102c03416120b290074001020094a1001805003204e520065040000c10424500c00c40d8800000c0085e07c2c8440700620051008900e0f02440e44500200080da001d0407004101d04400029038254019041031030126125419480d148051221584030f400843e50000b0030091054081c0503607200703881c010100f941409600a60b000b00c1348181c038041e40c40c840c40e0700c0c11042003000381c100842e007255018001c94810326156501405402d02806031078800d060620f802091050b0401480f4203490814000d0750840c3c450b441d01e50042d41050b0345c0041d440ba260701c0c02003208110800001151941c603038802181500908000741005070755000607070160a401d50381080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 455365827 1250 455364577 455364589
    0x504020f040c09031a0906090a0c03030302032703031b0310120311060c030109061e0506030a060810090209070903030816050c0109060c120902130b04060302090a09030e0a0302 77
    0x100040c0c5001c10b00d61490081110f001070b103074200815040844019280320106600c6403442412032400700d4035a5116a2403a076038507200384000400b12902c03004103000013880394000d55045080d030512a072501100022481c00074480f010802e007907520210412400f2001c05141050587e507117074225185007440d8014482490701c5001c0c041819042c120090201071144000340f05070039202e800e580060504011301d106980c801c2c468204e1490900c0c0010440a40c148403c40b86010b1084400c2d0945241009200c0240c1004102d00c3c901c55450100040286060180d00e1030008007000c00940d01e445841041508a80505010f01b0000382c0d100600000b50401030303071034001c514044101c4020755441012200c030f22903c440c1c0b50350b6500f4100c0035020481c15400000403e40281c032403840d000e03071002c240c108072800c901d4043d5012030400c846400700d0740503901c10b45440c5400340c400306199071a0b4020840300b0300260346030b03a845540c0f0703030b4400149035200001c42c0d00c40b20200e8160240c18550b4000402c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 455367077 1250 455365827 455365849
    0xa1805090d0e060405040c050f0711030c04020301080d08060109080a0605011e061d0f040c05030a1b02031b24040b07050405092212090911040503030f0703090333050402 74
    0xb0007a9950b940140707c09014009445a40c6441d000300b03540c1d100e061402078000c0c03c0b41401c1c24003910602e1814241840c10b802600c1c140c2e043c050003499190700c64a0100c600180107031200c0e0503c141410041040d8600340248a0418001c007008170301c1b13503d00615220f2248511940508000c41c106003840382a034410720b2119101d041c079140411621440300001d5140154064481d48186803c1110141c5904900a10701c124003440080115040c42121100014180c14810005030400c03c9600050b03100c000c01c18440e503524000f02d4500582d0421010307440b0309803140300d1140f51030020801c8200080456503070b61203803040c51302504161920000c07420700300001d00b02c69015104505103a103107919841c2118462500850708410140c0b4106000e0400806802240d5090341010411081461030310205c1c0c0450300c000d00250f1a0148c81000c818141d005603004504001241c103002000c601541d400c0f240c00300260009101203c5d0008482019803d0b524201e2205400c0204010250352072601b191 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 455368327 1250 455367077 455367079
    0x80c0411090105031b0d060302040b0a030201020d0f0c1205070212010908070624030b06030d091401030207051006060e04050108011a130f0207050a121b110a1805090d0e060405 77
    0x40d12a01c82c250070300f071400d540c842c2d01c0c85c1c141004240031218018640001c0c04030f9000fa1003c100e1200b255040c03000101e10760002030b01680c000008242d0540c42801181c16081c400e140540101c0859903e0803c0180100705c0c480026001140250552500080c5140076141c0e8000820a80013260760b038100500490b9409401d903035a80782ea5805415000074a280002c001da000d00c074071b1070b03140d29181d44801d109551090080c440c03560400603c1d4000c0c0c0500c4252076041411100d07440085004501a510504040710b20780030f41c0a50446c1c071030050046c80080c00803620340d694200c41718014402181c4c4160300140c8242c2c101451004004032030710715145010350075525151090701c1100c814001d131505011200315903200140d0403040c400d0200d01c1009040c8100c21815110780e030300c1000c0300e4042040c14801c090f00e4a04041400068416000002c5014041c002a81c1581e4514051010340310504045405a0300c0391304107c20f442e0b05001d103d41005c0c003403e1a151405940740811514050f0340903403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 455369577 1250 455368327 455368337
    0x224222c04020d02030f0a0b010b09061e12010b0c121828030c1e06080a09060914030307030b030313090b0303130816080102160f0212010f06080c04110901 68
    0x2007815512800071183c0c69980180490303800f2140104a60b550704074010055030309084020010401030100004c6449102000304018103213518400e881d40710780e01e0300914010341c00b0100020034000d113841804038024a243d00580d070f01c4020740f0010a081010f0629450200003041150415102c08413a105601d15020f41e07060201042d000003808285440403207648180c861aa8000100b100000014083e105244070b1010105000611940c00030214021103010900540000e0b1803030100b6840035035064010702003c80c0c114000c0d03da1200d1200664046a020f800000c2003220107900340c054512a008268015840c0441803010b00700b4542d4540a202262a114802e012003a54200161344040c2c05841441c42c0aa44e98a42595100c6450036100c01d043e0000200061242c0c06100380c0b101c01c1101e00d003c0000b42125990700c0802c011585c0100d03407003407110b0f4a05440c11003d01c210410340102c203600082c00c0f41419161450b001602c5c100c0e92145d07042000e11707401e40c6c20840598403a4007081c200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 455370827 1250 455369577 455369581
    0xd020c06131d09150609042a2c0105060306060c01020f031602011a011e030f05090a1b14040209010c14030c0114100e2206020901030c05070f0224222c 66
    0x344050303008044481400882d050027103400c0058143d18420300804d10044410048003021200c2812001d20486030311250900000301d09091500052152030108000103203808a000062203264006452481e200c0a9801e0b16140803070b0240f10703600b240b2101c0e481c18003c2c907401e039000809410000009040b41800c010403c1c800600a400c51751808150040502c00ca16000080950b07074610454103071040041c050540400c4ac069020440689640d050001401120b89040c000a5070103110310904028245548602080c0408030030036100303100101855035812682145030a4404104001044418520900c0325030700044643c0350480e09030360305110761652003291125500008a003550140d60000785240b0030045540c2c01401d055100740c030300700000504880111464001d44000501548080244030098039041000d030581e400307601003030603a100b4400c00d190344c0d80c0c0100480020420856001b20448651508000c000d0b00312400550003000b503030300d2130350f21112400900007115580343c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 455372077 1250 455370827 455370863
    0xa0c090c020f0f03072108070302130e040c08100b030c102a030906030902031005090705041107050c01030e060714040504050f0a0e0d020c06131d0915060904 69
    0x40c80c1c2d9142d004401c0d40c01d0403035105062912544a540129aa0035522441d02400000c0c1d801d03004078100c2581d0740485550790301c20140e0003903000317121440300001c4554001510f04c0c14100c02e1449207100c1c1c0d0130f940106141001f80c91600e40b050032050380250501c8001c1a01d038800140b00142d01000b00c0e01240c140c80c60000c03d0f199210229055004140900000302d640c0c5007071400e24410328401c0d07494121543c0d9030f80e01141185ca0954000394180c12007000700d4003001480c1c10a50301310103400d056a044651b90000202200d0b1382010101d8190408074559007071000170304ca0100b2403c02820180075008001000d00d4940000901038000e115009001c0c0000c40d07120400e4030094030000d44104001d00f00040451013040f0300f183c00b494003d09108074580201c1d0045088805201c07190002e0840d07094450400000350030281007282c3c0c0f1500c401e4005540c1c1c20f000492059030103a08896422070801c40f8246080072040070b030050b82006a00140300d6203487d940401ca80c0282c00c03c110f0100c0071407a02d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 455373327 1250 455372077 455372083
    0x6051e01050906280206010e0c030103080a090e010f0501030609020f04050d03020304090218040515150a021011032409040b040204021c061716050d05030c07080304170a0c090c02 78
    0x1c4d04d060301c41d4224007034481c1a07080303d2900c80c6084040e000c940b0b46aa07503a80034a00e841045401e8088543c0600c010000504140301801500f0700c58189004100e8948814841c2440240c3c8072940e05105000104146d5030507100b560050038110703005500c4c220841464640a01ca0f601c103d80c0140c00709041203003814402d209940117040003540540d5940380441190180c510703090040c5202d02e241401254000d04144030001114401400f000d0700d0150744104a042074000184440540c0658404030003401800e20405000106010f1207a840e0300700a00a80c58803604607010880141c80740a2150183e6030b211038951f40140e00c0391008445646603c00304001c0d015100c60b4070700380f07030405492706543e82d0183c0040c800c3d0f8507801195121031072445401581c034052100c111401070b262400034040c60a05101e1204100d0180b021a8940580107421301d01d0b007a4158800c4420350000305d003e0194002041107591070100181c010301403602691503080d40ba591341e1040345038859071500001d048a00038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 455374577 1250 455373327 455373337
    0x91a0a061b0f1b0501030209130f060e0f040c0b040b1204030302040e090a050f0118061d031315050702030607030f0b0406090938040201050720030106051e01050906 72
    0x6407801c00440b901d4a0000040401c1020241007105001404102544031340309035110001d009004d202507050080700740004012421040080a440d840b0124070801c00c80f217050b00840b10480c003841549050700b007004503002103030400c5142c400208000c00104410000791200040400c01d0f0106a4032140740940091003140d00007807c80781410200240c0c4040440c007443c640e400707142603400c43c0c5911010142240c0e280c1e5002440103007041003e4000c0307110340d448420b60750391040c0c0700303100c1203006540c07986590042204429100c5072000b052001c1b504074420f9034502641ca0030010708100c540da00003a20b40c600242000c0c00c0584d1601140704980445c0c20504101d100a001040071a4690007080c020382240034007520940d0003802c4030100d8403018000d0f018070303045501c407115070001526801c4414803030180041e410444140074600100d4440304510a210002a10020b1040c40b00002c3c18207482c040d9000303620550420080010020300380380c903d41e0f40ca109182c8903070b80340304080000c6d0440c0a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 455375827 1250 455374577 455374583
    0xc090a030501090507080106120809120f06012c0a0b031002130302010e1203030103021512150906030d0e06130306060905250f050f120907091a0a061b 66
    0x504400000c0c010190b10004003d805001642d40700d40d05c2ea942d0078240e411510610401102449150002c90860009000b0303198008081462042011103110b28000c1e01c1a0301034426080040108904184160841c010301d0304003940c0a4407402c0030304c040800700e03401406290307038940310f03a040302080c0c1d018003499019100ca01421902c1702c041485298008419000803408100226070703031401c83c42d0007000840c003440310b80c0c010b51540e800c59003441440001116400395808041c0005e580c5000384420141c480d00060220420b038031100001c0001549001d40100e003f6000502a001401c0d4852200c81c0c040c1c6050310a141d07103001a46440811a10035440500413500e4210041090000d54108030f004c0d50b00d5900e4004c1407000e42c1c2c1c0c0b240801030302d40d0251002c16411228000c22500400141404882c403050f820700f04040d002d21048118012100b00b0f8070368218150a0018400c648194000c000102c11007869481d611030103c0c2850400f40240001d00c64406030310060710002650020707450758 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 455377077 1250 455375827 455375839
    0x11a091e0702010501080f0303010b0d0c05070602040801090335090309030a060c030c140d0911060a0309170c190204060807060207031703090c011d0a08100b030703020105120c09 78
    0xe881035009001304030a0080d902c060080c020711455400000081d00e0590314800314042c0340503a42203103540181b102c8031491081c403005000f840f0104941d4130141004211400012a0780c1c07146d0316000f441401560010031441e507c20013825103406142e5481001119901d02c41d10302e41d1280740583d40756001e072203450740c1d0500c1403914000030040749803c14540e0000b1510140003a0b0402d900644409070800103410060700d0500c00e002c10420705803c00d100380b40c0603000d00840498000c01040301036100d1034401012035103a0781850200b00c071155100d101d0b80e44950f115810103550718445a100d404000188000126418100040d99034a82c403100003000750b08216100c466440394042e403140074500c8240c80c0c0b500340d4018844409421000c5900c1031004c2d40c044e181d081360304401540c049180010880d08400c44021132000c9071203098120000e04a060002d100c14602102c3c4503050b2456805030500070703080943c0030401070b41c00205581c0c100c0e181d6000b2400c2683e5200e0004540c1c0204440766074020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 455378327 1250 455377077 455377081
    0x60504061b05010e30040503031c1805060702070501031e020717070c1703040e01050103021303080f0d05010f06021507020f012d05070f030b0a08101d011a091e 70
    0x803090402c0c01700c505100c280d803581413054550202c2d00358000c80c801d039500358000b044010907109400100c080c584000d0307000011244881c81d00d00e0104481200229410360018040c0820ba540402410000304030034602400002c41c1c04d402c0e076840036010505245400d8000ca017560400030f000420b400500d646503183c64495050f0b045c540b5822001e482400c603291403409020300d19440210031101990b10720000b4092591070080110002d6024101500001400ea217012000071043d03030040c4029140078030050b4481c4044600001201e074181c0c8403004a80620f1810800e064001c980d002c2c10b01d03101887c5010355600c810302a401e10103001c05807244c0c1d500c3e181c0d0000080c02e4564454005050308040700c40f2071401d840e082e40454105541060200721050f00c4210f00a02c40e03040203001c060040d01c2da580d0155220241442d2558680c54030325180d44441120a09903441d840206c00d0080c03000003403001c4c1541c00b40c600c4103d01d06000c0c01d030003000c4260029000b002e91648546c090707101000350090324 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 455379577 1250 455378327 455378353
    0x5040b01141801080a1b0c0203031303060c020c010c050a020906011206030507030b090318090a0204032001030c02030406090b130e0a1d150a020d0b090403030204050406060504061b05010e 82
    0x51403031014154003141c11300c004214810b1a6100f88012031051150000f10020500000da49121000004030fa0620041009540c000c101c68003100046d4842c04005c10311800340302c4082e0801340d0300c03141541048145605400410740010f081828070b6016100c2e101662160001251122440d8090418003420013400000300b100c00140b01045034020380241ca629220f02900d81c0d10791044140340d500c20080d6200801a510301403503201d0b044050240c2c01490140d581d620040414102c0d00750119840e90780c40c000365156098016003009406510107180f810303080c024041c1c05c0c000302c0e004034080600c0c08600708508010080c0c011018000308004400140390464000c009408810b0420b6508200c590518200c40e00000b2152000d862807151303400d5039074401658000075005103000d43ca06035260b010500b000c0d103c9800842c002d90003980e001d41e6403804c140038801a181294402800c0100c1000100300040c0d000780310140a00711380115240040d00e5040c4503000d481c44414103400382c011507601c0054 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 455380827 1250 455379577 455379607
    0x1020408151609030506060f041b02011b14030a090f020619090b090307030b04020402040f030c091a21010e100f0f0b101112040603020322050705040b0114 68
    0x4140c103a001210b400780d1401008407030f0075150384802451503101c0e80c0459081d14044641c401019006800054150040e0305020a6942c43c4000a00940d645001140100569083c031690003506400c040030341440303549121200d484020042011030750740e403250004003c0710400c0651841d4001749029112100f10700c00210108404c0801e10104440c80b000168409405007913030b0b0034480060180900500d135849511551000070000c81e40298200000b00d8007144251070300780a10f0142c000680d40d1410140c100b0103d4000d80a600d24022060780e40b03486954a040e02449022080b0907240071644441d9042e034050207020140d01118000d0f00e81000e60508158084408070720b0407035040c0b049004e00c0c00000121040c3c05a0960031076840c45506084502a82d4401c200600001c00c071007842e000300d01c201443c4e402640040000a40000c03c2c403001e03540306844800c0030346258008448150441d5075507a5941c24034850103000700d8403201c1550440c0c0c010b03080d003050324400059850383c4131101c0740d01c000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 455382077 1250 455380827 455380831
    0x82d06040c0f0504090f09080c010605031501081c020f07060f17010305060c09060c0304080109060b09160f020102120405071703210c220e150915030102040815 70
    0x80a1440d0245603004144a4000c42c5810a020348440b460b050400c4c80910140ca02d0303042c000090303602c0e80c100e40c002640700401040031841a00c00041c1c1207080c041050f040550110400440920000c01070190060220380c404070740800c0680304800d0420b00c402641807a0327407100300103000d0090305d0b00061440d801140b028a051300315030307401800308141413401c41402001c6c003028200c2d80c80f890008800300c01c89001045001c0004286074107191901000d58179552150300500406d94444115004020050240305000e01c3c3c00c81c0c9501040c0303003600c1c00340307141c0041c1820b090801c5500310302986d483d0700070350468840c008080c0c04d41e1074a1419090907584c40006100b907944000d00170782c0c0c0050201c030100030b07180851150800034440300d540406000800001800d400c2940c5810400c10316403103010404003507440501d11102d07010500d0071128400c2a00c0003030010050300844016003000399503001c070707607980030380c0d19001883d4101c50f12020900900a540021829119401124a550050f01d100d01c1c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 455383327 1250 455382077 455382079
    0x180b0f09130311032a0309060d0207021804030518040e16030515011802090316030b09150c090402030a0b0d03080a06050303130501030e1219090510020d082d06 70
    0x1030103414014100e560382d20810b0610341d480100c0030441003076017000840034901305191404407801d100d41c100018001e40e20082000c0340030ba80c0064000704500300980350141d012554141000180341c56140640140304020861035903440c41c0200104580c0d8a61022005c0c0903420111414554007000504070075805000a03601b40c07042c1c16003508142044168035041c0d4148103082c5080300b90b001005006034110080c0c3c0c540c140150111450945410b00000c0e00941c0a501010480e0400170002c40c03c0030010030005055081c08000c00c041813603140221042e500d400d440050780da98802072220010309242011941c4020800c900c24141075010340c0503406050360601c04c1107226074030800c1641d20f01c5240e804202800c54000200100c2d07029500c40800359030a0700649280200702e900c440550b92100c1d00381e408030030a84201c0031006900c022520040e10041d241c1110018407118042d43d0380d00b01d81d00100810100100041c08a4000403c3e178404440c82c4016000d898400380c854002071900311401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 455384577 1250 455383327 455383337
    0x6050f03040627023a060207080d02190905030309120102040b0304030e01081509190e07060201150501020114040602031008031602041a1003050c04031a1e01180b0f091303 75
    0x803001e20200341107103060480d68040030204140d500390300781c2006178080c806552842e4244525400300c4c10207001020031180441740140e5070520380820040102c40c1e58078040c03c102c4040b406101a4a00104407a041c070070455080300d415520110180c0a032240781c1144141c4c03075020050100305034010a42e031480203400d0301d07090055500c05d03030803290614420401c02d9110040300089110107000c0040010003164100011030000014804985021196840f410042c0e555540102c03d4004090010700900802d100074000ca213900c61240c0801c04010300050b01140c0c0c0000030414a0210303204450041403041c2c02d882c2ca401c011280b24099018600060b805241481091603c2264140d85d07111224001020603a07528031082c01200141002414041c3c81e82c0708000104c045249520980f411105400340040c6501e00500d4038400030503165240e6031115605c0b001402401204810080004a00000059104c482d00005440c0055000416070005006014001600040031080006501039116 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 455385827 1250 455384577 455384599
    0x60105040e030c030c3901030207060204030203150f07030b0303040b1b070f05031506030a12230c0c030d02031806090a09020c0d08150913082106030706050f0304062702 74
    0x2601c0c94001014040301c602c01b240440c60074a6020342d010b07040350350140ca00141010b4a95021074078200b01403081c1c445d02c90020b010400d001240c9140d00358804030500d0180007038034814000c65901d000c3c50194010900300401c1d040d40c0d1050107840f19850319003603400c8400c11903540c101e09800c254980115800b03802000351322050020481d241c41d0080714003900400c0911100e4441f480f49641c024090800c020003083d007070b40e44030101ea0944561892242d1100e0740c0c0c0040f02c00451402d80c00e4400304d402900890100300c00113070003205881d02c1d944081d500125007840308000039603511540c0c1415902c00090300300480c4181080d4042d1481003254822581182032890042c1d9416030110380059401038038002401080c2080042a50828084210760508141541e83d088690700a1142001110081b8024003802010074180c15000101500940038180c24035400800500c612045102500301c0040070800b007000c10741c850301880e03465800780300f280d841c0d66050181440c2e065005904c40c00304014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 455387077 1250 455385827 455385883
    0xd050318011122030c030305030a06081c1b050606090912190e1509040903120e0606010f050423130c0e180f010504051b041d1602060105040e030c030c 66
    0x4810f003500d030809420012140703156402c640a51008080a000315110360000030b18103c10040d41801c0030005046400698940c40020700103410758803000b410841400c0d101010410200300281c00c43c03410f4075540c106594113141103140c107550076865080d0080008583c41e0103100005623008003401703550341041e030840711020005c45640451411001c004100450550340c03505502c8500c04a00c641003680310a00926125003c0314010300248031580c01000c01c000c104c1da4001440900b0700120b04056007007d0900c10342170030805c0c00b41c0c070310807108002420346040740c0c0c1d88440781c2c188003807155814082504a5000109004605003529026490007a4450102560403090610406008100e005182e2074407003000003810001d06401030750040d0090038038001c10303810010005026280003e800c424004803000d800303510000c180081c2c5100d90801d44031402e034040745003411070300201d50205e031b4030340011103040c2584610480d1410750711000a4440d00e000000c1880180d500c00c006600c0c1d06105554 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 455388327 1250 455387077 455387137
    0xa0305090a0e090607180e010308040314120706090f0b07090e070912020d230114130f0b19060612061401020d0f200109060b10020d0503180111 63
    0x18070b18030320f03541155000850580c492803140406015943c007000300c6940d114001c910a4100b84c0059650310400142802480070919950302410f001d840140140107890031303090064000c01500800c1c0ca030311035101100703001c84240400160b0f40c100c0300e0a480b50508050141000900b0301c19011503e00c080c00040c0010700851002080750807510140103100141d508001c40320031605822907000b15103514940200190079071008400105000024800b54514150b028900b002001c800382c0b20443c141d07000c002000305800301c90307040d030000c4d14a0241d00d502c140c3c41000209000b500701d0651070b1400010f0b02681c81200340b8202803242c0744c1001002d488000d603c01511402d200b490242e404501c005004034407441c1c154004860071700e805501503050392000440c58508141707081540c5e45900c104011310030316205540458500b01ca09c0c40d00c1102408000c0c0d200d4811001c80c20501001100241042291100b00c15158000000820400148c440e0041441e0003002c3d0050a0901540b411058540b02e2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 455389577 1250 455388327 455388331
    0xc01060f0503120309071a0a020c040902010507060209040b090a090215121f03020402070303021213020901050f01140c1f0c090902030712060303030b12061015020a050a0305090a0e 79
    0x280160200340b0000b0700100f01c6604c060402420b0f841480070008559a2400d81000c051010b544c100d80c1d85c410401000b4a09801d42a03002e200e14034000007440180c0e003080860303000d01d91102001d038451070508002001407034011440c0d07401c100e091080004422280d840604210304c2151106408625100c00300c03018002c6030b010340d034480c0c6902d010890b454161498000a5900c0d800900f641540700d90100382640c21006048010036004900c40040030100d401031a8030026090460043c100245c0004600d140b040c0700f218014070396094005050303441003e418441202069809a8540606040301d542d54035558945810126402480100c544580902544a03007203030f40b0340c1c0d01d9504013144013009600144c03400084c072280b041e1003228100345008110003103000f0744002510340950005d2010504066003425a16003100003000001030300861058196036081940410040c2e04207400e91811242d00c0002d0281d1203030062200c01c040d804002050b180c00f0035240c0f1016070f42d8501c4803404040e42 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 455390827 1250 455389577 455389579
    0x8010918050606210304090603030801050d0312052205330708060d05060f0f0a09080409110f041202040b0405010e0f090304170309031501060c030305090a02150c01060f05 75
    0x201c0804105a442c045014010314001414a80003030000c0445051171036001c1d03405041030f182c5401c4208180b680100990380140740070380d400205400996402400c5049691404084a9460000c80c103540040f0f0b0301e6010340480e5003103d140d20b8007541801952540718060305420b03c0020301104c0c100c00000400170700c0c070000101c40c100090b01c965806440c03002004003156042107142c582c200100c0d00401c0f035540604448a0880a6030404c0c0c9000405080d005003000c030000e040c1003400c00002c41d0034003140e0860b40104d00c0081d04401c0100120140d1066980900d6250800310f00030445100f1050040302c041d2003100c0421101c003e42d01030200342d6600344110703500360691000203040280726816442c0d10040c1141528509500c40c54003009050709840030800552002c54420814101000b105e0802e142d202c110034420340c9001e0b4001c00f840e0140794000c003095151404200b58040c100700b11750040d54024092804c41189440c2d403140d5401506412282e9030801c40b00203840108411a8819250 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 455392077 1250 455390827 455390833
    0x1306080a030309050f24072c10140d0509070812040e070c080405120c0907170105030601080618030f0a03020d0b04060e0619031205090306090105060a090c020109050d0801091805 78
    0x1506d072944000658020b105070203101c101c860850700858038448030780f82c500c04400006022000c00c0203000f22860f0300c522049c10b002c1c5c45010b4a269000c0c1c1011f684290200d54008110341c2c1d660b411140c20040560310246c0c0724491000c1c2e101918840402520540f81c0e1119560510754820b00100c66815603a0340c06032403141e00308001e02c140d082004034031424048440444150111042c041800c51a0854006001440c3c0c0e604507421081500105070040404500400503541803030062074503180701400e002d206a51000d04058004c0050040d9501c141c80001c0a40c0c8882c100350b40600030398000d0310030410b52440d000f414480f9191a00c00c00c800d40b0350382e4281b03481642d100d0302401808041040304900080c40040000f00080841c0c2c0781c221448510341e40c040d200c44040c07091502c0c002c80035141c2101070f41170100300102911102c055808550022101180124034024240d0050440300b00140c4180285002e00650b00d4200500c01e0490303000c042c00f00442d0901c07100c915044940d92000400c02d030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 455393327 1250 455392077 455392123
    0x3080f070507060908090901080303070306081c03200c0304061b03080411060909090c030d2c01050d0c02060610020a0206040b030402040605060a030b03070f0506091306080a030309050f 81
    0x43c0f41a8020f0010742e12070300e142c0d813900180800042c58004242c0c002c1c80c481c2d000008100c2207a0b494000c18008040c0c5a0040c241c01491013841c00d01001008040f0003019520560050140ca1110520484450441a0980c1c40000c41d4810f81c480d8400d0050310b010540400780c10100d010342e00e0a15a11580540d5400c042e5284d9581d8411110380300d100c2654403240601850401c2e039100120390340148030080050180003001c10a05050150380080c3d04e007071007071a032002c0320305803069000c04d40c074004c08508c0710b01001180001610113001d14424181e80328038000025840a40000740c0d54000da0040303a401c0e014074120392003281c0d80c45583c4402500188188020450046041b01440e00248005c0010134056115400301d01d45801c00b03414a40040d0312060342000c54182403002002802003c4903152070b00e41000b010440e2485000a1a03011301d221a840c525207004550141003d45283c000703030b5100c0718140c06d008010701440b0b501614503008050301100c415a0001ea02608001242a032041078 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 455394577 1250 455393327 455393333
    0x2a0a02031c021b06060a09020c03120601120c03090506010b03070f08091009031d0d03080105120c12070801050f070f0c0312021b0606090c31030f03080f070507 70
    0x141c420112022106400340104100c0c000d0b4010f8180c0c1030004400204001d250080170030082c1c00d00c46e48540e81441c4108000c01040c1d038040121217801000e0b441042d410348690004031840182c41060448461808a01c0303a032096054011611041c0643d00721000799032100c070283c500c1c1c0b0090383c0c4600030511300300201c44400e01400589038802241d6054410043e991138651080e100500d00840c0007421003000c103112041c03200010700c4021025111a4903484182c2e07006050702406008141c0705145070500511110b100b040321007960384000c1c100c0042140c0c00f00950341e441004c0c0c06504080e509000002e26000022802c2e0741c41000c0390f0740c03182c0c000c410b50034041d1021614000150108144401c14100c0181507000900301d07140e01e19420341c0794464900c4035074200140904201e2142d42c42c0c40a0200041c0071070240d0744152070364071031001500702c1c4aa851340d030350550099581d90480c00315000428402200300c0d220302a4000d0701d030032259648003a4442a4108115034030004514240300103804 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 455395683 1106 455394577 455394607
    0x60d0c02070f05060405010305251d0f09040206030403050721121a121f1410060903030f030609050a091203060b070204090501142a0a0203 61
    0x4900f07001c0007841a00c540d00c145c5040507100e4011400c00c080d09036450501491668481c4038171104603202070300b0100704400d0b91000c00440c0d080000c0e1802e0100c0c0c200c41141006008410380c3c1e80710760801c50242c101400560400030184240d50008125070602d074000961541c1c00740f021151a0802401e0040c1c02900007200b0741017242c1550744651148011100300c400321003a501e20a25406003514080078226030070344240350307038400d0041d25060380e22105261b40c41c81c1c07510050782d540b03454008410705a44525000a030340302904201281c8200f00e0062443e0701460f001c690595200d440209030f8800b960302079000b940c0c0718403041c2040001012050089040d0400740b103280d1500380000868052038101900682e112030103d42005000c1d8030058a00c00c04140d040d595007400000c00c00c10032000b01104403002086074100b002c24a03180261448040c451380110304c3c040e83c1c0c1b000316070 = true := by decide +kernel

theorem cover : BRFrame.Cov 455215827 455395683 := by
  have h0 := BRFrame.cov_init 455215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 455215827 ≤ n) (h2 : n < 455395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
