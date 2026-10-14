-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0146
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:05:49.066201+00:00
-- url     : https://prove2.me/submissions/6f1bd812-bc71-45b2-9db6-094aebbf468e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 26079142 ≤ n < 26258998 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 26080392 1250 26079142 26079161
    0x6220f020a18150806010609170c0a060903021011060601030b01050702060c150108010504080316021603030801091401150503090a051603020907031a060c0a17070b0702030a080415 79
    0x20a050070014108440310351028003e40d071401000c0b10959510f004403604c1c0e00d401d1142d03d01146e05110101f00e081000d00c2c0d01ca09000d80d810a5400c0d00e20480002086034409402a170b0024110003414802c500f88200803402001c82c90801456900035405c0340da5482c20018040703810540c59500c036a0950340240140e07080c840c0d0003010b042c1c4402c44c201c8865a07504000031460078544910000040441040c07055901440c3c200514516583c0d41c04862100c0c0c05814000008600c240c0004c0208010000c00440240d440790303845c00072551400603400c0c2038944c3c031048540da190290004004140b1000c0e00c4009200d52401c20941f66910048180d06005030484e028000d80030b94403120400f806400d65400035240700300c4900340b035900c40100480c02c407014030a400d1806140c020640352180b6101b030180120040300760454200354155500e01001e0003462203500315405010070b80b08200110010a603a00601c80e20007582051f40040000f4100d040140029140c100c0300307018941002080e030440c090380d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 26081642 1250 26080392 26080409
    0x302130e0406060e190507140310050109051c020d020105040b041d16020a170d0213031202010902030a030c170301030807050c01030c050a12060806010303020d0206220f020a 76
    0x40e9201000440590121422200d59140070408298500c134880300e10702401070a03e007590892601c2d001c42004100181c010000c0c405a0032400d400d030030040c00150311840c50300b213140c800c00f460b1030005052101d0302e41240b0301c6200002032a036241407a45c4640324040342c048880c2081c0904074001a5140e101c1c0c1e420441031494002008a04c0706c01045505c4040340090010b82030a43c2c2d0300b9150032025110641c582c00503000a20f10740e02007007a55030030551951003c41c40c0c62400c1d0064000034101e034403280c00c08940d41400c100410901600007981040c01c0740d240001d21a42c0d07010f03400a522003a2201006060100d120541346c18010303810903181c01c5207240300340349a03030b544c49041900c8642c000303c000b124644074048901c41254405d0140c0200d1a103591500340c140603900100b0f46666545c2c08000340c0b80c65035a680002c0e0b5a03000c02001e40258003940240c00b41c0d403140d40000f1b041c0381008140c075034202c45030348000c0003912074103c000a0040c4c0141680d81c614140744001035008000380e125621 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 26082892 1250 26081642 26081677
    0xa0906020c0703050c0a150302030601021606030603110d05030a080910020301030602032a04150201090209040c2904030807050a0f030e100c02060313020109030c03051006080303060f100302 83
    0x307410400240c000680b4001c000700e40503a4500740c00c012442900303008660200060041221f58103002e0740241d6041101401500c05e6600c0d500c160301115040e0340d00c80d200182d1110f408100b400810b001c071210f50340042d00da2000c0f103441c0303449050382c074440c0e191820100400100010890031040c0400040c0c03000014041d0358950b902e08209002c1d400075110380e00845030350b441410301e0040311400c080d04055211b01c11402e081c0b0301203c45018141090950341555200c5810300010f03070f20312036020310542c420540100040c0c10410004506541c0e00038000b1005058007031300c0c80042c481401d0700c044a40c40b081c0103036143d00d81d103416420700b8640c91008004041401600782099004140203483c1c41c2d054450070072000c40407004032040701d0101d0001e50001410070124031301100d0440c3c202420307030060520f407500c55aa40e40300000300900e9072040d941c50b0001b01d040b000c103070301d44c0c002c000003800030708021815414030000143c0082007140ca504d100d14644c4901802d8180a50180e4240d146d104002c0c5d074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 26084142 1250 26082892 26082907
    0x31e080a0e12010c0215060105090904060c0f0203030114060f0f1803011113030609050114091501050a0302010e090a2c010c0203030408032d0414011407021002030a090602 75
    0x4090285007404248030b403403618202e81c009001442004600003055005141620790b04104a4440202500075410824104100011343d00e407204064052031103a1030000700907540341c40041c0039191a006081c1103420030001005084075000c804800e00400b04d800c01e030b8401c080d040d141042d1250400ca908a800003044804520012540d04840300c0c0f01039000380328007944048060340602c9845213400700341618440c180b010440c0356000254041c40f550002420b021000714200070200201e42c2d51507150b02980c0c2000020b030081491030700424040e20f04406c40341c11b580c00605800707200a05640103261100000b03809040b0b03a004034051030b1001c83c440b40001f607030100b81c8103000c2c490400301001e50700f092280c80001d032001007120301c944e403c0100c560442c0c407038900a030750703180c0c0b25400d4940c000c68100a2100100d1650900e501480c8141a28048c418030725008500b5601c80144011088405038204107010342c010802046900c1c82150040c0e883c0e9402c2221001000c09000240a0703610100341007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 26085392 1250 26084142 26084147
    0x703110f09130302100c2f03130f0b0306090406020d06030209010b040f0b0c03070f0303020c060a1409010903020316020301200a080f01050a05010509040f0f02040f0e060901031e080a 80
    0x10b0b11018080e50a42e0043c0801d00c146406941d070a106500024141e1000c50050401c0390304001030369500e10016141c0c29030348481311803641d040301a180303807403078502c01c0100070350203208200381d00030f20745840c1280c25403908a0000f02c071084002c0016050f907800003011100800b1a601040103551b000308181040d586492645015030424000c04144a001e40b501040c1d44280905990740c441c510710040d4a00000766503402045a170485086007815000d1148080c415401d0001c684a901a55000036014407550010314031180050401000d0381d160542000110342e010003160341005030303041c0d00c8400303c03418804607006084900404041d2111101092440054000205807018640c0d41d011159201d140c0300d115401400e10640754840010f030310230001035020310081c141900005200043c03540080500805907040031984140b11640040c00340010301d4440c00b04009800101c2c6803540510700040400c81030f40040c040a8500c0003100d1003104428022841e0381246940100019100c4544007000b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 26086642 1250 26085392 26085421
    0x12030504150606030e0f031303020f0a0905090a0303060605160803060307080303090105060102070609140904080c03070c030203010f060303080103110a050d030203040602060708040228080a03050c0709020304050703110f09 97
    0x114171300b40030390b107124001c59000009441c241031944010805a51859080004a040f08095107070003039109040041c180215200b1288181540340240c83c0c061541e141c0101140c045420500921109100d0014061041d82c0801b0807150300140041d683d0300c0301c10010b0700d0009952b10000c4030b4400001003101100d41900000d000340000e030212444039446060a0341e505005010322a00b424003654010700700d26001c283c3c01e0b001030180c91100e107440d2070b12581d075042da03001c6001980ca1081c020000c104604091148049880707000204010460035039030028000b000602c40500b41c0040c5204450b01540c84280c2c1500071b09c8000e01c601060251792501a4498104d0301c602009070085100103101c5134050b0200d140b18560080c041940c0300103c1c80c040c648034000700144d00c030351140e0180c00304100c5801c221500c0444c1c02610707210b031200010300c403040c0b50181c00c2c0c1019641c580148140000980005240d206076a882014800442041004038250015108803d5031100040050021031181c0c0400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 26087892 1250 26086642 26086661
    0x5061f03020702040605040506091311100e030601090506030705010507020a050316150801060e0108100f0b0d050c04080d05030703090803010905040204050906060f12120c07060810031203050415060603 88
    0x1414440366580d24101f104903041101d030a5008002040000c0c0540300308a000b10041c0e205007400c0c103514003001c0108140442c0b10f403003503010a85003072400340c0b83c0c17404200081c018081a18140440c0c50034102084d11000d4901c2103a05014001c110b00b030031552500e4415010b0721000c1c00321440090b1070700c01c10805804911400346c4561001050308515803045043d281612451b4503402e5041d01d0500044903202401003100040000d03460300401c04905400750b50340100f0f982403d107507c1d50059a4084200c40c00641011803640b401c0100f0041458042401840105942400d5440f5540c2d00000e901420305074200405042d000000840c28000c1540301034080c500075030303040003140e980c000125900c4200740c4605034081028041c0c0c1c6030038603001c5060071000507540182c4805107500030782500039800c0450103100b960030100d8140300d070341d502408030359200c0c9045055211705032540c2c45506200d0711400e502000c150302e84002800b072080e00c251051030b003608a8801c010066072124010000e119042 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 26089142 1250 26087892 26087899
    0x11103030c130602010504050606090a140703020309010e011406040c1101020f0403060c050a12050903040306050411090709030804060e060712020604030e0103060e0a0509010e030309010b0f01050c030a0305061f03020702 96
    0x142c003042a40c8140310340c80c07080c0c0c0c0c00001880c03552a0703501000541072009090508144c0c03104d8000c10307a0300d80500c440b405020681c401585900306440c205081d6480040c1c6a281c80c3c0c9442203000181d00000c0716240c00042c160740019003c0c660b0b40c801c51f83c44410b10322200d400d600000310b000f20f520403a002002202d000e040c00700804001c403801101c8a1050446030b0340000c214291600014429a00442d00000c2180459251507a00d5481209490044078180c0c0c07207400f800d50500850904000b525402000f0f0b00d80405160708503500c40d410360041d4042e50080111340c3c0c480c2042c60703c6034421030740d0554208010030480c50021000a50b035010480303080f00026040b1400e103080317501900810003505c0141c91000350507650130002030020309000301a101c0c036640b07a220702a8240000d00c000e6018450307080000c83c8510031002408a0307000392580882c1004020807074942c0744040403041c3c83ca4402149000714141c1c0321780c40041e40242c28011040c0740400104031200300c0a8140d4002c1c0078151003034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 26090392 1250 26089142 26089177
    0x20405100c06060f0e04030f0915120b0103020403021c061503050d0f0201110d050a090f0b090c01170708130804090e100213030f2901060305090a0c050609011103030c 73
    0x5801c04074513580c161181c1c503100c41306100400c0020303000b080e07008110121840c0c4104080e03541c4100844500703a9244600201d000036046200140c01b90280741d03440b003402e080540c46c007861580032403200c3d20a0107000e800d40c520350001c042040750701c0d0402c115011086800e00c0d8416101d051290f1074900b84500b8002080901c4881c4d541c0a0060003082e04440000e0f03c9903080c5181828044041c00c80100948000d41d56115107600107001c4122440340c42d405001c00f01d02e14a81011824a452551f4007180c1c144400424880602094207610540c884403d242113889900c03000090180d00c044140014a01c20340410003150300740c0903901c50880061b485049601c0d4800d091707100d0040348200001d0362507401308000c062000c2480074020010503480b652503081c0c82c00c081c0381e1000040190001494200c0075210040100d580d16008103604007125a02403c0e49071180d540d4144c0482247c0f02c0d2900910002c02e040095a01502c80311300c00c0031070341e8180c035a24074241e44003020303030b83c404c030307000c01a09940 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 26091642 1250 26090392 26090399
    0x120a12050601020f060a0c050c07080a0506010602060123030a120e010f0c05030a21140402040c080603100b01050906030405070302031629070206071a01050d08070204020a03020405100c0606 83
    0x14400584c0c40b10401803d800d40350200390324090515070542e8411300c1402c000b620005103081240c200144014005805603000c40d107007907800e01c48180d10900465005000501c9244e280f1481030b1208204075480c411031902d41d02c08682000b0030308102403d80080750500040d42600040304600307100e02640c85106040e81030303400303545d105400b0f1707c05080c0707034000e020b18109207000700026001c07904c0040a2881c1452070380c0d0064290b803164001c0600c0c0614510522007141814000c800301c0b1666810209454507001001c00d9594034480034164000761540c81908050f4001c1003198101800a010942c0c0c03840c041c00c000b6620741980c84102c8c024800e403031600d1711103001051500151008a510352080041624110000c51045200301000790020030191006942c4c0c02c0080055601c60700007042140c6403002641140281603200074003820760010321000188410080f0b80e8001c1d4100c40068941003d081c08400a0040750005900500c101043e201c0e1250007040803040c2512414090001945 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 26092892 1250 26091642 26091647
    0x60f14010b040e0414070506030a0e0d0906050d050408090a0305010209030714010f0c050c090103050d08090304080a031206080a0507090b1806010e0102100c0507030e030f0303010302090405120a12050601 89
    0x1461180c983d110648401281c0010600c19032100c910584100300d070300c05521040040d400307600c00d0b02c052015543d240844a064807041c001903007100640d003007407081e0614000d405000c1e403050b1442000308036500c4001400f0020350304103843c111390015110303000c42034032407500c54001e500103e241c038402d204417840002d00220245000119030f030306946000d40e500044200b80c4a1000300d41084685019030b540e0000f254903000782660080d4000d01c02400303c0f00103043c001e000840701401c0319030aa0005c02090020b2080082c2a407000b43d40f41c0b40c07000f072429424007068000d042c55080141c16005182d1078100b44840040c900064458007101004001d15000c20009041e0b02e885228001454110004000350f02641020b402110b042c0181ca04e8400c405008008030f0383e6080111000c1940880d000301856849000c006a0840940c000c0007441c101328401666400144402031003203120304001401c104090004007031091000c0d9040761140c3c0d649201800e02c0389140c84012145150400080710340d803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 26094142 1250 26092892 26092897
    0x3010b0901030c0e1008010207030507030e01020a031d0f040905031909120303090609230c040204030b180709110301062a030509030114150a0605030c0a030c0c060f14010b 75
    0x9610488903c0224589000b05403c00e200511500718490360900c00110b20f4820300060410501c6940e44641e924074614001c3c0c61000c50007015411580103030740101c0060f8001d980d03c032192800074810200d41041600240741c2d0706102042a4009051110b44003c100000000e0304840094240c5500342d075070b01500898003d0340381e214503000700b80d0302000600030034001d138400c9003010702609010030794a005456001000700203070310044c13112591200c140f00501c400e1083c0000c03100c0c1210154079142c6152503001103810043c0c2062a407a0705551190752851041061100601031000300380100551854480340030b400904c030704000708402c040d194090fa004403504081d00044e017500044d4040d810345084507140c000064407038056503180d0008101080d8098071610411440d2a0b054010000c0700030f001052445e40d0004007844000d0041c0040301151303400b901c0c4e205500340340009020307250a00460f6801000000500780302d28140f20340b001c480311504900300d040c0789001380c081e859a0344d1a4080c4070b0b1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 26095392 1250 26094142 26094149
    0x4120309230d0c0509100602010b01020a0b0429040501020405030106090b030312100b072d030903140a0b0106050304030f08090709020309070803030106120605010207150302031e090a0203010b0901 86
    0x125014010609546070000701c0c2e0001d5405008140f291588400c04a20fa140c0180c6200d000305038100020042540c4c2401881608c400c203201401d40c04540d03039100000580e0280000f404030118110104030045444592102248440d00341c03a070a003001e023003440c002d40c020301525000754200039000c61810744901800c0503202024000b58940b81640301c100b0701c15030b00540412040c0002c1d40c0001042d1001d03402801c5464051000c43c40000319080c00292421465031405400030751500c0000007294100342014212600100884500f20070b20030068285078079020000e2a0150782000499142e034080055032199101c0d8503031140385458404280c1306030104aa10030981da01214061100032010b40207903410444c100f003150070b0240c4802d005402d5410036041074000482c140b2200c4e04980f2140503a80080c1400c3c00580081410503400100750b420103880b034800e00d034000010072034003d1054005000108020460052418030030f5140d0307200c8101d400264469030070085c5001c0140b4000307060354101c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 26096642 1250 26095392 26095439
    0x1110702100e0103060302040c111506060304020105030a0e070e040b0a0501030b060609061c1e05010509180a02030706020601090614060702011103070f06140702010e06190e0304120309 81
    0x2809180c50071a040c1ca4409502070404d0744134000040141c50310b0040015460051b03c0b27048494541205180c50074003040e0068034600e500c0428001c141d101d03a000c4a4000c0d8081c038042d55680e03903c01001d0090000501c402d0898400c500e40018806c4401c44074600030b52080e015240a6111641d03440d090303a80a0202414107950340021681c3c43c5890b000600084801030899402d20390711510038441d0441b2003040c01d003503944481000000400702107200d105686a02c504114950410700441d001d510010200100c111500d0101c801950741040380d562111384c0181101d2101c0e46030315000703494100070302c10b202c085d6080c41004110720f4541e0406074000c48001d00b10724108003260f00119a00039542c1c00b0207031a40000c01c4040302107601c0000c4200603d01507100410600460041e8402c0444000e00074804c40e490400d030700004520100e201d50304a0b400b1601481200c52003042540246504884510b0b5840f0002d0002544581c02c505940c00701d00a490350b88000d9942c000d101007101100511f10403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 26097892 1250 26096642 26096659
    0x50303030420010e030304080106050906030318090a020702100f030f0e0a0b06011707020a02011202030903030a0b040605041404060f0c0507030503071b050a020a0f0b16020f04020f0c01110702 84
    0x621103441da00c880c540c554149030050f1381c07400c03d101080c02d5034080e80114655035101c0c401800241400d010fa207030000740a8005601d082c038642c20180d107045c0700000e500d21488021021808084050301a9840d15400a1031064410301501d0090000c50000540d080804d0804513a95545000741c440d0f003008508180280c421601680d503030301d00303200e402041c0e1818010310000740c2d0041d91544007002c1c0b003480c09400408071001d1500003d020880002044854079004004020201e50007000341c03070300031000da000030800100a000240151000d600080c1d0014034040c500d400807400f81540d40e0145004800410681c074002a03142c00fa0341c0d540f144280820400c2140800203841030380155441003151034401034016001c1080c030394600c000101910540d2101c00b00c0070540c9070401d941402000c0b0a0036921415250003008085405041a0301e146003480110110175511114548525544002c0c011590b8040c0384660714810f4126034003c2e03455600e8022281020040d4008555040350010540386 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 26099142 1250 26097892 26097923
    0x703050903070f152412030e010e030708030d091403070206041a0d1524080a0207030311030109061d0c0f0a022d0c040b060d0203060114070803010905010503030304 72
    0x607031801c0310307540440300f400713003221000464001407140c200d2000b264070251001c0080214034200007101070f00b0814000c1c944c5c04282001070f03000b20b9281d1102c603003070801428010300440003c1c200250380c0d220751401d02001400000806080e4000541c462240c140361400d403444400d06940e80c001e0080081d0882801c0006208401c4e1a0511030740c81850074000c14034084a002c200c0c816216a807103042c0000c00b56102c18441e03803036800751001142c0d440c00300e1440c00802c216002001c0100103030041140365030000e1290180b600c43d80014007502c0742030580b982c3e41d59494040c807008040341d2207885031b494003480055403003a20f00c80c4083d0180388031f41d2020703007480d11400c2001d00542c00f001c40c05055128841003000c402d4408004160340030040c804c29503240b504d403210181420202528a031181d0b150004e0f0901d1b07541e0702c0080d81c03000c0294a90058481d0345600042c0c510b140368104020108a0111b0314404102a410045058814404050160b03980e120305150750382c0810355004042461510124 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 26100392 1250 26099142 26099153
    0x30b060906060412030c0b0604020c060106050d020f04080705010201140f01061209140606090108010606140d060b040803041409010308090d0302030d0c021b030f030304080a03150b12070305090307 86
    0x5a42201006010528143e0b0303501900c6980f0707150542c00c4000c1154a2030201c00d10040c7e14090f944a40d06503801d6190122242c442e58841505000708804d106003c22020f100c0b4507980e040d00da03008071034600e03180c3d81d946804605540d0f61403071203214015806d00c9061001511074681c10360054442e44400b40c075507402e124050714482d0001001e0740300c0303982d5103c6c810080388580800e141a100c00704040d11460a0a0007480071100b0140c208169580c14100104500d0340d1100310105800b010050396130300c4584520100c0080c1005510403000150b01160125100d507011004200321880c0b120407100036101141448203014003440054812542801089100d0601c5041c03648894880d10540c1d1a200c485c020310350454456044000c016423180c1680444820020701c0c6215461085000b0069a90850501503803444010801800d030040881e122410300e00a40040d03405106003c0310f591465103d0030560080e030402d1500c00d0b000300c04035001c80c2d102d07806882041e00440526014600e4482d094a40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 26101642 1250 26100392 26100409
    0x302120703030b0a09050601090b0301050a06080c0903061e090601050105030406020a02010f0c03061a030c0a1b0203120a120615030e03070c1401020607030b0102030d05090a0f0b0619030b06 83
    0x79000e0545440c1c0140307859031032124800242c050f800000801d81010000108000020381241100c084100018001940e0700e440400c12900e19140c90540c2e984c942c207150400303000340d00144c1e40512a0900f444082000030b00040d5102001c0c0c052001a50341d0041a16900c44c2c0030b00c0b4070fa02180080000c01d012400036001408510010700011800003001900300c0212921071480600181d138810b800d0099100b2000194100d003081c041003403e50071b204520200704c0c0320b20030441c82070214512800b4800c0e01492250000d00341c00400740c4803a02002d80c00b80303415500000003500010140c21a480c01013440c1c0c4110300030380e50003180f00244032600100540080807014400e114034402400380000044040c00f00350082c00e00f91420156822401002a00d0102e0151589061600b000080030590b640007017640c4900c280c0c0a000f04441c3c5030390078614200902c1ca00c01500012224403503206100c0c6500109002c3e4109441064451043d42e01403c0c1c03c110502000342030811210104e942450203500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 26102892 1250 26101642 26101657
    0x1b0c1524100f02010914010b040b0103110a03150b030c130602150412030204090504060b0102121e0702040b0904060e071d0c030c0f0c060103150908070b040302010b0a060806030c030a030212 83
    0x90424032900d1b01d081c026600d941c8000c140c1c0d10341101c60350302d082901a00011400a003801d0000d9240080039540601601c40c100e030826580f801465502c451205c0c000c80182400403005036242070490380402c00d544000344040000260400005056100040400e03920010024000c030a883e0343d558244645585a0a1301c1010307001d210115611f149841524003681c4a01d200041c807482c4100064141035188000240300c0d902403080007000711a000b0843c10840c089480c1b01e030b40740706c030744000340040042c03031000c60f008150318041104210881d070015128401c3c400894104031b035250750702041c6c580e141310032a102012a80124039a80700b1800650740055500303103101c0c00c0180d60440300403990043c0d20f00701c1d4240c0c445001001802940b011441741c0300c0c2065001e0000c040301d9202d0440e24400e03814000d000030024400601498801c2d4020b004005004100321071340741e580c210040101c0f0003a140e1622034095401c000c8894a00068120845075154014003007044450b042c000c1150448070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 26104142 1250 26102892 26102897
    0xa02040506120106060207050916081501022107170301080a0b1305060702030d06060e1008070c020604090f05061206040b0c07120915171b0c1524100f 66
    0x42150300028013600000c0c090703d81c0103020251030a0200a50000d001e080d0780703803420740c0a179601c2d48160b0200c61305a000c4504c9030b1825180c01ea0f000102e15001e1041604407107160460318110081038036400a001c1c01d8010704c8480c107080f44005041409200070302c90a4181d80c000c80c0390000160014000f035910008218101c03000403131903102d0f0f43c2007000440d031400058000140c40e5a05452600c01c000181c0300a26103602c0618800c07002c40c4003529403174010001d01c40d01400003216980715001120009901500d45030301d0b03903560204200503040c041d401c0c01c012030510300054620f0030549110788030b07200034100820080e01c940e200c80201800140080f803035000c04105c00404030300024004800855140d840e006070328940000d4800f42c2c0c403c25094010030000c901d0038440d440744c41c1c010a0308207000b50f00398603a0b115040200c5e6800d00c20780c155214980510100148070044041c141e84c400d07100e6041321240b081b04094500c0b4568422982d5175480080ca4980c180041d02c640c8204910307500b00d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 26105392 1250 26104142 26104159
    0x307030501050403050c1005062d0d0c080c0904020a030f210203090108130b0703020306040213181107080f180418030f05040308090f0418030206040c0b04080a02040506 74
    0x3600e8450a40c0c00464042c1e000c1000000c40f9580781d8070070407031080f04031444a01004542490b400003034203000241c4011800416070300c00c0d01d00d0204135488041e10484005e207c03900003d60b17460028001d0281e4820b0700d045000c0c0388a82e031000c0c1051303c030740703442035a0007014110400d042d69100e840c11001c0c24000d513200380b4140e5110388030724204107600310400d086800450701c8400800006265807401404000034402170448000015000d07900b8580200241c10056165502e000114000b0701900300d22402c1c3d00c0030000001110081c4545801c100075010701e044c0300303810281401500c14820035200400040702041010300c3c004501001e088035210700411a05402000b100150944040410032640001e1148007101059049500201d00b50220b0400c181450b15640751a115401411030035030103040c403101c65418941d00c030303404140d00700c01204d07104500c40302d1814020b40d90756084404442d001e42e80301c00410109032a00c103a03003c85803468002d000e1030f00203500307203c0603040103402907401260f1f5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 26106642 1250 26105392 26105399
    0xf02070b030c071118150d0503030604090215070c1503020405031c02010f0509010c03050105040c0507020118090509030a0207060201090b011e0504291f0503090f0d080403020c0108070207060e0307 86
    0x85c0030303290452445400300300045040a9207042046013a0091041c803590051504000041002c02569844139007142d00041050b52800440c45007000240080c012403030014070041005550228201a126007102199a00758004400e404901c107500a165042c5d100c501000d01c41041600141d5001c401031002080603ca90b40510090f40d005854019490b5100d50100a807a90b052080700c0c01880c0c103e0342845000e24512028005114205020381000050a2801d54040103c000c41e401860b02203010071003462700d008515245d03005560a030300107000700d21001a08a1050080b2000203420540703c519503441c01e002e49050100d40c4075402d5889102d0000000e40790f48510075034000d04d40001d0700e41510504030b420004c1242c445080240b1946d000703202c42e032080307191005007104005a41401513513500d0f1982c3c0c00d4504464508042c45501c5032151035800680e0040d95076000d24840d400b11860301c0d00e1003005480d0314200b1243c581c0140e0160804000e032610851201c0114280a02075032a11903c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 26107892 1250 26106642 26106649
    0x2030403150b04020a051c1a12010204031704050a1d0a0203150a060908070911030a1e0c0207240e010e04060306060b031f060e0f1215010302010f02070b030c0711 71
    0x1603411700441d5010404019102010101c0706155003070003000c01c40040071071062880c103040410305a00410a030151200c51040950403100a076801500001034400c4c80e14860182d80d0080c05014020305d8403c01c0000e5031043d400c000031100036140f115113101e64650311600000c0d0402070800c040c012400d0b42c1c1269071388503072154101400240d0b40345000d031b40c20207003d1481c1440b02e900085120786005070000100d00c10b038069a80210541b600400d00000300c0d90f200c00301c1490b00580b940d583d480d103c2402d1200e500010508201c0c1d040e900c004054040580101d01c000703409a041a000c03070cd000105211703c0d03104001e0307107001c624010800610140c481c3c0310501210015005034107501300010900502440d012940100030700c444050b840c51906020b0002c00526080307200c10300410f41c600c0203425035a2111445ca01c904081011601098540d1aa4484400d000c2c4016400702d130820611403d5607201280c40b00665a080300024a140c85207002010294028401540d604005010140c0c007540c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 26109142 1250 26107892 26107897
    0x60e040302010f0b0303070f0602180910061209050319050c0109050705040b0d0c0603050712051303030f0614012d081006090f060c0c0305010501060f110d02030403150b0402 76
    0x28003a9000040019181d602c0c1c03030442d5461146248240d000348854000202c20078102035416a00080c05a100c0040301c062443c184240255194000b43d40020404119000c1c50140110b030344540d070340c40140b42d08810076001c0300d000d0840548541c01c00c11900725040c000381140d803142611860700500d0000f42c00300c0e65085500544c821121a04402410440f43c9400e00400c000c00c1c0e81110452a001c15503500c0010402c1e0901c520001d144c0c4079030024804130b00030324400d4140c007440a014002c91030004002a00194130500460100380381c07501c0710a0341d251034403504007500d000d00644120182c0306001942c40d242c28003151020324289868044200412412a11001c0308079194521503051010031001100d841d6048a0104280d50504011184500340d103801107440c02d043c200d80703004e2303d4185070f00d07003001681011349590b0a0000004485130701120b085414034059460005032400142a1070f110b400f00d003060710040e0300070310060020409101000f0042c01c401c040007e5405070306804078083e41c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 26110392 1250 26109142 26109151
    0x90308040b0306240a03060b040503070e0901060b160308070804020303030a0f020d14040b0106020d02070b0c01020d110d0f0e070302100507050a08091314011e05030615040b0303040e1306060e 84
    0x440004c00c11185d1035406004420185c004c100000d4141820704012035a141a1071048410050060000c1195400294001e2024080406405650322070038183d401c8032121224046000400c0800042d40e0248950000b03801360754000c01947c650f40390318104401504040342101c1101e0381c02c00c40c41c0317256849031080420403100056041ca8501d428100a030198a051380300e10295002128802c2c1c01c1680032a602c0140d5a11000868a07030000d030b11400d009018200071010041e07e040758010841180c0e00c084e100b0140e0485061083c2c0c06001140b0013612007440c004110303076100790424801844c08401e00407034901c141ca070013424008942c031841e1030586440000e0320040000a01904241070541800c034080c1562103050020010002458a03c45014818080e0725001424413001580c2c2d910301d00e40003007100070101c804a00b0442200c4008000b01101e10340f20f10316105812015046c0842035400b01e0b448004c1d00340300c03a503c030070401480c42d00340c04013250385030390300d001c081b911060000f0214000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 26111642 1250 26110392 26110459
    0x100e090106170a0f02011404090c0809060612030306090604020f030403030b030d03090b070804020a0b0a0e031b0a0303031802060309010e010c09080a0206071103010908070b010501090308040b0306 86
    0x41c03510b000c450944102c0710440810940e0001500c40f0040780709041d42e840140d50a21f00b65031400184c2024000c60f0060350012000103041c210043c1c14a41c1c030400b158020520703201502d2a40c2c07246402c1011540714800d20f004980c0007400080e11500d4a1000198059005803015180c4010280000000d40c0b080f40c00b28081380c0d0301c501c0c0c5500c50a040260055400c0c076410704000305c4140f0384699014120003009042007001000000f0110b450b078000d1440106000a80a500d0305950f82c00a00f0080340000400e0080c8554490511514041c5280c0041d42c0301c003800c480020340c01c40e02c049015168004054124605100b440340040e180e4000a6204e03941d2400002444001c905009080d5a1042e00000411041e404188004140820111035242d41202ca540e171b1a6201d1901800b40402150129855440c3c180e05a080c0500e07840100700d800d119140d4844503a072101c0041d03440c00d0081c0000b40035541c050205001500103000155007001000744520301c44088080021011080304104000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 26112892 1250 26111642 26111651
    0xa09020a06050703170f130201030914010c0806030d050406051321031101050103120c020a080105010b0703020d05030f06060c0a0510020409060902211305030f040f0b07030c030503100e0901 83
    0x44c55031080f442c0f440d00307000400709801030030610804941028041c102c3d0380544041c0420800b1a030203079012115440d409800754110480600406009201000901c7c0100710010002140b5103404680c0e00b041204540303a0764101400c008040b030310f0f904120500c0b60403a06c00403022070f401c01c0076106801e2894925414030103550151071700406503100078901595580c188030040c00000e000703281b44140d455513840c00110308203036400018104483d5070701c852074035442c0c41d00205e2001c85610042500030700035000c56441c54a0b21408480900c0212402410400900c0c0070502900d01100100041080442211804022a02e0719410b0a008901405299900140410901d03605016040082400740c80841c107201c012401d03044880100c80000c0e00400440c0005001d0b900c60004401c0002d03005800c0fa0f4489055a00541ca103070f00034000e192240049140000ea000411070440d12402d605030349034440f2000581c1c0070f40d15504040d244081c00003100307801241d0941e401d12294480c2c0310301c0c070001c107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 26114142 1250 26112892 26112907
    0x1b080615040615141c0603050606010e010c030806060a050d15150e01140903070e04080306040b0d1e0302030c0f01020403110f060412020612040302010c080612150a09020a0605 77
    0x104a64440e442400c1081c00000003c0042d90810203044484001e0341c1080d41e035503203e01060040c1c1144096a100c064900a404010701c02c000070750342d10510023a2220b042500f000401940c02140c20074000f070010b421500041d10900b4100042e00c001492400c0c50b504020008100d4400c1c0d80d03c0681480315600e44981c01c0014404070303a600380d41d0341c0090030822900070345030000805094000320107004129000070044100c0e2400c100c0d050040690350304c6500281420328001086500c180c2c0d146110302c1c20529042128544180a4016580e0106240319106040600340021800703148050f420b500042c0b0601321100401e11004060001c40000180d645041d80b41c400e84600c0c0341103080d4010a100c1130166401d8031080103e406544680c903208100000500c0095404e100328400001c41d5180311091104050301500802c2c2c03242199200c96020703580308000d2104205c24002c2e86e0006900100c40003d004011468241d003000d51050702244080a40d0041900c80f080c40d130004002800005401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 26115392 1250 26114142 26114149
    0x31101020307231e030d0b06040e07050301090f02030f13020409060501060926030a051b0d0e030c010809030a030b030a0c0f030b01060c050c0906010c0606080102030709090209030a1b080615 83
    0x2d6448050074050005129181385426500d01901180c0150707103544800c0341c9440e640d84410b9600816080ba180340e460b140001009060350003c1c402c06080e60704000c3c0341401d21402d802560311924980100440a98030803407a08140d8840d128140d80040d1360341080804034a242c06924045c24080d280e07810200d181801603414a208081d402032a004a1111070314000f001104803410035170300f45080c98880205082417800c802c102178012840d8807600d10b521070201d4102e0410120300c4400c50580d0b42d040c1078030005480d001d05c2104c030a14150010452801884e000364010350345d0100107812102c07411040d0b0303500c100f000d484e50480307800007d0f0389508004200408982502410461400c2e05030542d0b1340c3e8815589502c61a8400e100c2c0b98a2030000345507174440d03454a0f0000750072801c01c0c00355650740c01409000350700c180d0f0800001105958082030044040c02160354131300015006040a001c1030f16014030354502c107100c0390300749010000009514070f0200a201d001320190807400c00074034010707003c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 26116642 1250 26115392 26115403
    0x1605011a0604030b0105100207080708010903030e030a0807030f110403140c0d0c06030203041a0a0605042007020d0302010b030f0705190305061812040801060302040f140103110102030723 82
    0x59840341100300720a0002818044401c5d04442d000e03510034816240c0000268205555500000218413600d00c001901c170300c0c1500301d4804540683c81c00c007c1020710b803824503213910405040d4004284d000380403a4850740301c0c0e803090400c850700720000610710400d82c44408250380103030f1042c0c4603200030f00c507070f280d031840f0a2249600c2d508007180d908085040c1075407001003582d014842c44052540c0400002c0a11005900081318040320f08041143c0d0300d04480c11070000c0c4054007419006500d840d00105406c40e030b44000d0b000111442c1e0100d8100b0705d03207500300041101e172050224119505e038070b40c15040c1e44080152903183c140700b0303001e840c40608000521040318214072030741900d09072940c2d040003c59400718145070070000c0d06001c080100191400e051903c0329015070800396407030003d00040d2900c010760128083e41d200b10717000e00000c0c1100801a0a80e80c240c080500b1200449004000040c1807000101d106403040c0150f03400c00d201501d4020b81126140c0494400c5629540c051113504c509124 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 26117892 1250 26116642 26116691
    0xa0f0204050d080a030609090317071803021302040302060417010e0604030503070f0c0221060906010302030d0f03140123030d05030106140403020303030a020c06010801020703050915160501 83
    0x450415250000007402c400d580100640386000000b10a00441e00c00e410400180200540a00030308840340380092213560070800b0b82e050010440046a0703080d201d035540c062000e0380b01c05203c2d4180d042d60200310102c0c0030501ca01c0021582080f0010050315880041d000030284d028000c4080e003c1c0600b80c600391640341c0e480c5242500113404010020350800140c9412191074602070030100c01464040c1c610010201000c1d5002c15040a46241c410707403415644034030461007007036500d00e4950b213000c250384860a01000358142c000803a074541480c0305400850303102c4028030f40803441045c8182090342e542d1007a0007148802000c654244046a49085842d603c1c19050700240303a414030184c4000c21600041c01450100f00580303100800004600e82510041c640040a07295281040340c8054001e600c4280307001001e0207000300008117071006100b51446590035489540c0303000000810041303480c00c0700c541c035140780c0c0f010b016207001c03241d0550300354220a00c100e0000035100c042402c40301043c8503008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 26119142 1250 26117892 26117921
    0x60317040303050f0903010b030a060209040608011e1512060906050603150406020309070302040e03040e01050a030507060f0c05030c1f0e03090616050a05010603110d03020d0c0c0902040e0a 83
    0x1c00009920204885020316120680e43d1222000800a405042520403d92307143c85241030000c01d1007131303075030041c003200d4022102000314a64407540346082c2c0d907214101403011000080001010300241c2c0040d000700074110900d10700a80c65106008a203054114281c81c1d40f80d0320703418a420010700744941504230004600402403401d000c01140c10403200244018041c0742c02102003000e083c3c00700f00304805140d0041003030014020100c1c005603a600544940034070f1000703050000078a41800880780d4152900203015080700fa09000094550b200c00820404c104840c03038030040040366091024080e12041040039050801c0881d5002c2400c29540e0251421030740ba080708408580b01c00000c50390303010b10030f661b0b041d120b03c09600701c0d01004080c84800f400500454141c04200131041d0312007825244948410504216000c080c070172100c030030300002009a48400e82440c508d5000e2100c94080c0f500c55003405401a8465000b074051740c0040e48521003400200c0180104820720340202900b41100a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 26120392 1250 26119142 26119147
    0x3020301050607020103090c05030a0308090709050906040602160206040b1c1e0b06090904150f0506090604090c0b0f0a03050105030109021c1b06050306030c030f1209031609060317 79
    0x20009085110f080700c001e06041d41e07903c003d0b0030000c05e1140c3c4001080c0050648510381800d0030040c0c81100308550040d107a00500d00045903035030040c41494050b014080041c007040c1d03180d54900000394040d0810826541c03691040100503540c90004001400c04182c110b038403101594074910304c03030440700c0d142e04050741808091070f16017421001b50026038040b00404a1802000c0010a00a02c204041d041d0070812181c01c100c00d010184148200480402d0001c20140c0d0300c18200e401282e5095442550040424010070f0722860203070003400c4403501800102904a94031031202e0940d40c0300c3d80c0400494100072401c400365540511440b80104015070023032124003600d0f40010b41107000c0000402c920300d40d61649000b403042c4d0242c481012005603070800103c0d41c403018042c010341c00c200c030f1161103481102e0a0030040d0501290000c8550b04c04c000901151030000000302454210000164041c400c83d0b0000341003000780c0803007400520007020002401415402c007103a030f01180442c00e20750074104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 26121642 1250 26120392 26120399
    0x405010e06040f0209030a140d0302090d0f1104090605060102240406021b010c08160c0c0501030f0b04050f07020d050406080a0504030c02030f06011809021f0507020a0e040605010603020301 83
    0x20903180540c000300465001641c181c410034120002e002d405002c0d501481926284410080020040650342c80c00008990790141c2040d0110281e10503e45542c1d000b02c500d442c0040003880d5071001801051240c1544940103201d440801c0480f16400d0f400c0c1c40c0c258076081440120750301031000c03a4405014200e0511109001d00c4103142c0f46134054802400c0348d6000030801c82c0c01000c140129904d60720703a0028004403030050760003050b05805882c41c00708604414140c91707956020b0f40008010740c0c0e02c0408804140d24210054001705a03801151100303540b10300d08000165070314441d06105690302d01ca020f0759400c0040c4024513104210005100740f00040100b407000f0ba4100c00c820740d00440c07508000c03400d03995a04d4115130804404100940610906054020200020400b04d0507032308c00410a00148040c0c044d054103a81c0300c45d10203034014042c0403543c51100d01115001d414140c1500b48a450035660f0b6001c101c03148950b81c00041c4034a030003010b020070407515028043c01002c0c1c5180540c110f504 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 26122892 1250 26121642 26121659
    0x406150c08181002060405010b04061404050402030309060403050102030a0b0904050601170c0a03060506040e03090105070807061409061f0e06091b0a05070203070807060801031e05011d010b040501 86
    0x20201601040000c107102c0300301402c2401d50002250060043e2080040d40341019664000689003201c865003800154600380c01e01c1d00c0740004940112583c56035046060080c000180710141050340c060104000388907035a103803a0001e0005501c01d0300010796900e0207581e0300d01201d00340015180319900b003005201c0821000210b00781598220700c3d001d00040f000b012103c1c5131515402c4441d4110303281d070100000340509940b04520030300c0152010301c0800f4500c00c0031500c80c803030f01e051580410800d000120100c0c201c40050020648540760000b416080c103190700c0103681e41100e498015921444c20000c412500160340018a586902400c00c0035007001e00d81c810040340100201d000f040040000f403e00311124581c10301e040420021183d6812582034020000d52080b0804d0303019205803d000039202c000055000101c80540c2e4854000b6420740e5076001500e03040e8141d004c2e14180d401000340c045542031203540c142480340c442180c00c1c0f0019100031400e4942441c1385a00c540d140900402400c46c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 26124142 1250 26122892 26122907
    0xa020a140d080d090b1003030e010801050901060e0102010e010f0204060906050301080c01030c0c020a080705010e01020f120903031209010506131802120712080702010908060c0f0a05090d11040615 86
    0x542c00100152a01096401ea8000304400440501646515800d11031400031420260054034042c3e510325410098100c019541000280705064110400f0001000091b103e2000701142107814400800c500400c041094251b0f2007007182c0c100550760018040000c540c000c00840c00902003820824115803400341410344502c0c911040c50f041c1600d035980c400010313219a802c2d0070324503802042140c19546070307441d082d40c1d070945019030b80c0860b8106554610942c00001c00501001c440b000078442d1840301d1150007150740060010640521043c844024030307803111118188200d1520000141c1c41c50080208031107120611a2110030b146003445810090711204640c1d0034081d01590700a00c0d55401c00a228540b90403548024001e1811402c110200301c012802062618001da81d1010b000e0303202c4110716141c4509075005a0505020000d40090050920280c03401115900b4010f060400c0c020114910044d4000e003203a8440c0c4135205ca11342480d16101d0f840c05807031200c0003480d9050141c2000340100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 26125392 1250 26124142 26124169
    0x2b0f02070303030b060417070819080d0e030f0307050a0306090b090f060a1203030209120d21020f03011509080d090e0c0d0c18080a0b04030302070317090a020a14 71
    0x3584812244c9115280d510468005007148880c40b000040700410b041d444000d079000301c200c5405602282041034507440460b6203d00c1c4c0102540c0c1c9021540310f40007004190155005405000a01020b03030080b40050103184a001581c84941e680c50000c44001c040b60f540d07401801e501d628012031880661510b450302640464803010324141511340900140c01c0040caa072014031144850541542015815000740455601c00c0d504404001c1029407059114020b03500740300001501186080c070817240d0203407a0800249111401464032501d50000f0842d0ba10036048098451480020b00401a030700c40c030740ba401042a1405400003411040006007814500d02c11001030754071100c0410760843c05202265045040041c0c10821800224005814400030010b040020b00310f605000988460102e40403e580351f00000004e00c40c0d403070b81da05800031b4004071015410402070700c000602d00c000c82c4058038012107450000300800c0080f481003080b69055504032104040301007201c207880351200300c4100c070318 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 26126642 1250 26125392 26125397
    0x13031e090b03060a170109061109150a030e0d03091401060b040b0915070308040c09090b060103020f0d0501140310060f03020d020312040605040504050105010c030210020a020106082b0f02070303 85
    0x12516050300280742007009400400d2103a1718016603610302c4a0541c004140740c0d1240c0e0041c8554400082c20380b0403400742126103a0072201d4544880740d90120203000745a884054140003c802d203000c5005440d000d4102c042070042951500404c0c280010001107181c04c4003c2002849a0360030300f1244000e83c0190310403036111038008034803200030344d5a0800e901c03403022103264000e4a4405500b0b0042040106403030544802460100100301c0841b2030060128203900000d05c004241c90318001180290b004500b66010f43c201886085116002c902480c1d000b04010828025440c0c80381c3d04260404e540d001b09000001d02d8010100324042e1b02c200071404690701142c2d8400c0041440c000f0074200081009803c0481c0300001d008254a130300407001e8410350380140c0d02000301da030329800150b80b44015500082c4c00342e03000c1c00310703039103000d0b1242c00800c0201114400440c1c62a41d03818440d2504d50f151500e4000240048042c0c054041c1d200202c1004010310b1405d038101512400b400703910741d0030a0001404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 26127892 1250 26126642 26126647
    0x40207050d1d03010504060b010905010203070b06010f0908060a05010e0604020405030c0907090b0f1c050402030a0b1005040c12050a050f0c03040501020f07060e010c020c0105040512070305030313031e090b 90
    0x90380b62001c1e52004000901030003d01c618989403a06600a00005031400d01060401c400440c46500c000183c405072a0f20424444540e11540c00554400305406045403c2158804010540610601409000300c89400d00071420b541002aa010020001021580a24414441006a6a8005020416904256010b042644481d1f408880000003508411a481800540811900d03580001010481d0340303541141a103840560080c1c06440c0f003030310f010351301d80d1004003440e0225010340d0b030301500141da804104130038650301c00200781a1407074604060301007201540b03800d09a00103030041661180f1280c070200700ba0318240304610303515032019080c0c68005c08040b001504010f0258100c40d4446540d0082c1a22651546800300150040300c0d1035250650810740c00b100b40a000150400504005131640c030b04150808040c40303401e211a490005080c481e50500202140b8148020350003060502c074518002d16080c10080e040c0100000050502e04600243c070421350380c81003011090368034003201941e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 26129142 1250 26127892 26127917
    0x2010e0f060403230105040b070f030c120203151201060e0109021312060902031c030f0c02060106120f0501060c020307080d08060405150a0e15010302030103050c010302130f08070e0105040207050d 86
    0x1d1090b604d0780d1136207507103000c050006004844076a1485103909a5a0b51a40e8840420442c01d40d0f0704001c2c2c52012030b01904081003540900d4020f95800360800350055560b034805d0b0002817806e41c0c2030326030001903552210f05200c000040c842d510f000d04601c580551800d034aa10716460311141030300c03850701d070301303480a0881080110356082001c004c0e800074116040550b100c0140b01d141c104040c2d0280100307181c02c0404501101600940c8280c28030b0b40c014040c213a10b81403085c1d500001d00a0a158041d5640013400e1301c4900511441c1d000e813049640c0c4514081c442d10605240490780d030450141c070740c0000c0000c800164014442907003c101658042203540303450b404600250f00d0146136641c8045200c101003400e500b4280301c0341c030030300d02020254084c49600c8019001c0b48420301020303290b50001c2400004550098006141825282041c2c203d12903850800c051500c0007030300418202d421540042040480700807400b8050b0104960840c5449000d6907100d6444080740d510700c05100c0d4180464 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 26130392 1250 26129142 26129183
    0x10b01022a0d0606030809010e04050601020c01080612120307090e040506040201031806020c06071803030503010302041a0a09060e0703050106080f040809130905160501090603150b0403060902010e0f060403 90
    0x94080383e02035800e00a654803450140d00c2504181c1c281800036420b00b007903c00615050040f540143c01c1a00540055180300d0011202000024a055003040b01c0303c4010312502810058580c001464450860f100c0c00c021a0050802032681d01c2602c1e10f0074440c06101c00b05a001c90700c25041a42428002a1051503c50032030713228296050180ca05440032542c006a500085201407003800b96641d14126008100c0c0c0300700c04001d5030700010b80040c07001c1c4010b000500341944004e481240d8040040300308581500010481546a0045c10450351a00c0040101020000210b900f2150a080c240840e60501c0c10040c01d115004003920030510f0340001040a1141e460112060031001425040c640c0380001b000c0b00142203000001c03207591003002001044880da03010100140d0348143d5903000d4507803a0620440c0a003e94603003880720106c3d514800107450881c030000340700551141001080e03403440c600000d000814060807040c000c6201160340402550b490007200c09580e0b10a103994071544405006 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 26131642 1250 26130392 26130409
    0x90109080414040506060f070212010605030105280507050d0216060204060306030b0603060906060d061803171f05060c070e090c09070215070c110d1202010b01022a 72
    0x1800346940000c010555100c4008003500303007101610144101e071641c1042c0019480382d644032600b40003045c0078810040c80c20404449440c9459030011a9050f12500040e084640c151114403201603c0c18090190040c2c15004002e008800c81003040545041d04014000d03214996031741c0381d101e90029810b08201e080c0f0f107404170701c1c1c0c1e00804110340381d6458410180040045000a540c61804080002d5081c036001a146201e001100041e020304d85406051084990b081c11003203c2040d1035503514403000300e45504880d0120b0282c3d441d00f0004410500031749002b030f0040d240720985081e014042c00031000300b0160701d00f199025107201d5500e0190081d076900b1715006411a00180d90504240280c8082c001110381206000312144181619204016a52040c0030040041310104003400100464040d4040d8525107001e9480b0446041511000517411080030030b04840240c0c10b0007546043c15424030030134107031500a000034500c41101302003101180800101000c0c890785010b0510140b912003031903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 26132892 1250 26131642 26131661
    0x3040f061b03060f0812031b18010908010e070b03070513080c0306070f080c03040204140412020d050403080f16140c09100b270604060306050f0402030103030212030901 74
    0x203080204400341c04a6040c4a5001c034078040009091000c04250700080d500d402c0215108400240342480c2009101400381e08010070305880c4c09202c042c1060710f03049403070003000c0f0b10200e07608412060038140d001401030a159041075140303a241c100c11100f0b41c5400100030007500c00e024803d6440c0d5490a0046a00d40702e00954034090540558001401c800b000814400703821044041d0b480395a1500000c683c0d06043c2d0f41c5110009101c1e8000c28565841e00005640150014201003103510009000354804c0740c060300c044852035400c00c83d101c40144c0c10700c401c4140200d01c2c604549883c2c03454031410310a014a48400d040804005500c17288030b51142000782d100c0b80d01c50b040d001e00c0f09118901d15110840c41b0b4003a400b0300102d100041e1000c14803013420090703803c0c80711b04c2c600701201941c500c00c2a00c10700c3c924007400900002d50303408642d107001c090401014560b03000305d00c45090805201204020580c07044c0660300510060000035000b06503445104000c202a0f5280ea88104450340540f2a450 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 26134142 1250 26132892 26132903
    0x803070f05010b2205010b0307020d0f02010f05070e0f030303010b1b0f0706050301060201060e07090b070f0b010b040306140709030f15020406170603070e06010c020a09050c0702100c0b0c03040f 85
    0x14290103400c82d00c021941007242c04000805c0642e1f03840800c68014482110b4450060700135200e481d41d050b01a400b074250110b201e100019407003d2000829080342d0090398104085210a040e04501e49082e40d0032000307545c42a009107080d5494100d000183d0f0082d41c50140140748550010243c0100c1045032484011424088031445079480a000c0c0c02944280694801942492404240085e020709401d01840340e0b0340e214504149071a04079402900501001c41c0c600d403000c0f946201044440c20024068941500c00560710f9280d0300c0d00204032000010008140e0f42c41d60300300854190850840b00c204c0303410815030b442d507284520381400400132030340360f61001ca40b0105010a0b4141d001c2d0049501205000001e01503403100c60070543d49003506c1c4507070b01284000800040c0d06510554198a44510140c80d1550b43d0703403682416800c1d108101c954850002001c40c8070400e52400142d0442c03070b4182c40c02c100300a0030007034036007195a0800078540048c400000011901304200b20144030405500003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 26135392 1250 26134142 26134159
    0xf040915090f02040f05060a090603020105091020030a0201062c040309080a05060f090c0d080c01090606150807080906060108070e06070c0303020d02030c030412020a0e070507020a0f0803070f05010b 87
    0x400101000f408240c0c0c07c1401010440004512103190b880b511003560340503100c981c1044c619008100b841c00c00782049004103c2c41a101060010501d40b141c1403000402d4043c50716901c45100c02801c50f045a070100f0018140c82d001f11030742001d401c0369008112041c104c01d15550751541030a03540c40040f5440140d1502c03c2c440e02c0814020049080d0380101411002c10045845800c039443d6150218010701d507210b07658885100001d1181d500404801d2071000000ca003075101e91711648111801a4000380c107490400643d42c020315440303443c540d401403080c1030040007802c02c001c1140e9503060081c080c5051101c64004180c05034000d030b004120a14000b0890b45d80c900240c60f01010142c4144400c40c054071444026458a03800030040c0d84607100350100444c10540303004c4640260f40a207000682c0c00020035640402c2c0c040101c5180b500ca100d440d11096603c0c0c0707091050082c8a10705038081074000c0c42142040c8030310300c030110444803110380125149040b011517080141c010120755000c01d0740000352 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 26136642 1250 26135392 26135411
    0x6010b040503120f09120118030201020c010509240603120c0c01080105040b0d0f0c08010c021c030615031a03031819031e0c0b04090b0f040915090f0204 67
    0x110802401580c000350140c910552990203612034500480840d011803501c140100034841c10b007092080003881d140c0700041420f8141da15800e440820041080d80180d40000d0f0b80d00b800e10090181030341090501008014a031800715880c13a04500c81040720307241c0c640d2100491340d2940c00b0030944841e0030b80c821506540310342c1d02c105a030360f4401c41801d140c0410745100000905240070710845442000240400540308007585c1e89100e000000c0b903003180c0072100303aa070101c2c0301d1109124011268501c0d800400019944400e44100360400418007010503060501c00d000c0d1115004101c1c0c490501428042050348854201c400410010941c03d1740610000c5a80e00100304080f0108006c03000a40c0d4031100c8446100080d94030b600306000240807107151146034800080b0550005031b075079001e83d05805286444150a00c9154029482b8003459625103a4082940c504401c1000c03170041c080350100481e01c034076a034407101002c4100ba8140e10981c1c69100509001d199900c01e04c140f80c0c0200200500d401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 26137892 1250 26136642 26136659
    0x30c040303030b01030c20011b020c03120c0a080306030309040908030106140408070e0402060f0307020601210b0a0b010e03070305060708060d0b040b060604080d0903020405071404120302030c0601 86
    0x3840240c00003801c046980009501910a10f400611070355200119015140100a0b40c400d0b11422441190b43c0d422004400e40145a0010000c03c125405000440410800c2600d020784100080b04115000c000c1c802282e1000640403201983c040000e5440741c1d0384100290542c0980714142c0d8109003401c00381e808000c1d1150085041c0c03142600c1c0c1462040d1407015024580c040ca01900a80d540400402d04c00c4c2c020f40e203040b540c050710042c04c1c284ac000c40c20012042e183c0060310000b0150340440e005205156081600720346007400c0f10081d41c0e03520000c0e21081c004840280501507030310394420708203155034450b24080c282c1c40d00c040c0c12104260b55925000c0d40d1440200e60f113500094045c0c0c00315000f40b074440d520040d116001041001c443d150381d140d0004400010300b03440d603c040708000010303004070144041d08905000343c03140e01c000e0340380d8010700007903640080c5040200841402d090b658501c0c410141e0b019210700c0800b0010303a0096182c1a859445206000c44484c85500e000041c10391 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 26139142 1250 26137892 26137897
    0x80703080405190804120204091506050f010507030f0f020c0618090a060302030a1707150507030e030a09030f14010203090607030b0102030412060b0f09090c010305010e100b0a14030c 80
    0x500c40c00403070700c0e00070031902080189201c0810081204804200c201b241e81c0c9207100007600a40000d00025040390300740d9504881498141c1d4042d0b109490300c004010350302d801040000c000000707080c07503441c2c40e080d40d0740104140800391041c814081001004102175100b00b1050b070500c4009062980d68003e41554400900c0d17080307016030b114248010014034101424041c00c0101c9a000d80103004209859881c51200c54804414094401092110201191115a240d41e20075040d106c00180b40c00c003141d0003801d85400c4100843d581c1e004000c030f54a91540314202c0030850780c02113040e1800740318a14240c0000d071a00792410350700f58004414002c03501c0000c25018002c54168070200030301024180166201d004030b205951b03070060043c45e40004200e10b0b8020310074401d8010030340c038000c400f201d0009889080540301d21019034407291050f001560944501d078090450036030030030140d16101d1840e10560182c0d0050000340403001c0f0305240c129002d074140c050810840b0803003540368504040c14402d40e8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 26140392 1250 26139142 26139151
    0x1090c110f0c090105060a050703051612090303081008060129030403090501080a1505010e18040813050d05060105010513080a0305070204060e09060c0a0c080d05010e0709060806130908070308 84
    0x1903e100d00002030910b03100c0b0880d030881e19541c40300760a24607152400d40e1241c0112070208203007044040c245000903400544942c07000e0a980b1550109819800e00030503d182c01410110005c4541006008907030ac0001c40c030741180c0e80700030b9a04900c0400d00d9680c61200807441d0048000d200032050000701038000e208034040e070b0002e98074611141d803001408402c1e503000d000000990483c201080c883ca51141840d0140755001518502808810003903880303071140e0440701a1345023100820b42d10300440c42c2230b07003030300c014801181c40390102070150711010b0303c404042c031506050003000580d03019002d07804211280141a8102070387d05140f403600700500702c0e6000319403c0340f207185030007000300300d50044018080c0503643d4003008040e1030781d60800c0d00c00c5507480344441100740207031011200001481c050007828610201c0101088039494140000305c0001c0107807856090003445941800306603442500590301a0048455007098003801800000400d04400701400c0c1c840300040e40382c245500004a18001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 26141642 1250 26140392 26140399
    0x40b0607050606040c021b09070c080d1506050909010e040219030b01050310020c0616110d03020408190f08070204060b04030305030403080919060509010f060816140901090c110f0c 79
    0x1480704110040780c4400d400003070301f45903110900d141000d40c03e00c113001ca680440c0600300b80085014544030b503420381c2c10200c1d000b807420b902e9100c14110080d1030540700000384054101b041c180000c1d000001c05944050199451140070040002d09560f5080280003180d0701440316901001c0c0c481c00c0281c080f8909015090182c4600f9104000c0b08045100312010b09680b80c2c042c1000383c0300c074a01000d0901c091713104d00080112649a00461900604c00314400d80c1141d1001031741e03585030483c01810a101081c0400300004440035130700106507408551300c0e401d82c4c072001c400e0380e881d1a440043c0082005070800c1c0c54102010a012003090b4002005600031406602c1d659082d90740d46075000d90350000034a1042d4940008040080018400d40104e03070021100300010403048401c1481c0340c1250302e160311085843e8400030113503541c0407212000300094840c9014442d5030001350300100d548004184581440b0382e6450460051852081d99000c05c5901c4c180103880400204807035495841c0c0c15030030000d20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 26142892 1250 26141642 26141651
    0x801050c071716120309110904050601051507050304090603110a05030d12090611030105010f05032701090f150c05030114041d2407020102030402031506040b060705060604 75
    0x11854203201501c4419600140004000c24400e054845a40180d049143e501141901d5100001d04001c25080110400d5030300084203032032800c2000b10482c204e00c0e9507004a00380c40c244404034001142c9181910400d0322500562010345c3c5281c1040c0c859010050664000400c01050440c0e1380d800c203e044902928110498006400130404a5103052054a42c5079001c044100d80c102c0c0200c3c2c0d034001a07160040c00082c0601a41c480c481515a010040f5800140010040c0f2403980c110301c0141c0101c16500d480307825440e1144a04000d4404000424004210419083c0c1d82800c250800901030f6401085130089184178546030403015003041064100c281445051001903104030300b07590407903043c0c8480079190941d4605120081a000140200400300d180181c0002c1e501048828100e100c080403403c0040b0700d190701d0442400740648080f0459004000b0b020159400140b500128450061300c0b84c0344ea112400010003c4c0000d03d0368540040000c40c0c0c0400740b22011452921901040d1030501 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 26144142 1250 26142892 26142901
    0x30606050109081f11070c1401031104060c0b04150e011a0103020a0e06030c0412030c0b060109050d060c09080706030b090604060308070b04030203070803040503030406111603050306061e04080105 86
    0x343c4624481c26580c082040a0131074034400300c0c054102008406603007407620326103003603504c0d91211004660884a89074004a50410304da51341442031072440d082c8000d0f0030381001d0401c2c0d0b00500c9101c5010b8042d001651700d0300850140015400801c4407442d01000401030b0000000c800350203803240100f68511403105089000403540a0f000b01c1d42ca40000e0360b03a030427415180808015154000fe8103031718000b01d0138000420709501200c00707000001d001c6c2d11601c1100030246820204241e00a01c4141040076612003042941c440c900c00705101a4010710115040b0a144821030f1000c000340c0c0170b003045200e040400a2001d03019403104160f46400d0300c02118036503403030003030209658140c4001415014100300c40c50100312071401c0d40f9000740c03092040c2c034903145641e00e40c00201e0704207441c10b40e003603007000040c0810000d880c4690180411142602801c000001c011800400e0b4902000350038841c0010001d44580d6501cac04951034140c03080809503001d031031010009075079003050040145640c0f82c0070226 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 26145392 1250 26144142 26144159
    0x9100203012105070504181403071101051b060709080f0d0504031209050d110909010515010516020d0606030b011e1401121d010612020a030b061207030606050109 71
    0x100d040e07424151120038060b541d40b9100c080e0307804462080e5102c0c040d064010074142c2d200d0007083d5112004c0b5000308105c454500309400ea081201c4680440c030350007001001c001034010800305a0083d42402c02d01d0700d80c4a081c0e03041c1c0481c00801c8000b100c45c06268100311034180c1042e8030805a0300304408840b880d05002c25555619014414a0000310b00203000401c00600702c4201a5541106441c1c0784c40a555600007042d00f207841d6080c05c54442c120141c801185040c005902075210420b01d000b84042e0801c0c0c4440190050350320400c50400c10001804403045c588065520115035000e805264091610306140c00148400c3c0421510900c10000016441c003c0403099019030322188010400e0310701c1c01907102400002c1041903070603c1240c042c400b21000e640e21032511901c2c0712801500100085020181c04c540060b045a248245040082005a111114400c0035694418101c0c401c50315400002040c442c3c51001040f043d01c544580482082916040107085503001e0f229403411944404d40c9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 26146642 1250 26145392 26145397
    0x902101101110909010e040206130b0d0e0a032007030503030a0507030e071406071103010509010c030f0c05090603090312040804030204050c0f0712030b0301020708031f030f0809011403010e091002 86
    0x40c4d1311071030000061207507554881d8001d0300244003c003814a001c1541118190445455005400740c0c2d0011808504456850080c1d032500c152440c081c20120380181d80c0502405d80da01344610300400d00c0b8108000c0e03400300f0042040035581103c00c4944170300e0b00c800325401a140c12074003030000a080948040341c980c0d0000302103050710b201c1c1d122040600100c2e000d100c8180c029603000c0c0c1d0150807000480103245c40c01e120355405403501800100758102e015002506845110313034000481d500d0218090b200300c2e4000b05840c50140c0445800f0742d00e894901c0c03036502c2d502810303081180642e05030381032008000940c0018003c0301d1081e0740600050303035214008016030154488803001d1200030080703c0c0000e281000b2401460710b0b54200022076404003000300742240c0150303c04070b030300e03280c000107122141e01c890010001c1c01e80e0281d0720f503043d64103641c1c07482440b01440c0401803450301d01041d90b8445030b000703035801014481705000507034596030b440124480d0700500b0f844480d0703140075801c1c0910038403210f4001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 26147892 1250 26146642 26146657
    0x21b040b13090c0503030a080708070309170901170705040512070503070e01030c050301180b280204030519050c01050c010f050c0301050111150115050c0a060e100b0109030b0703090210110111 84
    0x1300d42800e603545270003e484451004003103104165543d00070b28009824120585081402c0510540e203618000001401444840c4100c0700366104140412194640c000201e0b01943da00b61303640c81c105000c00c00303403a18041c84ca030171665240c062502302240d852500d5200c0c504880c0542c1c5549103007503649060500300c400b500c5504000c4107145070f6010200d001c0c045220303000034071524807000215408400010b2651002c0443c034030907400080c05c00600c1010400d5450b41e01300e03003c020080034a65980c0b25a2044802c80042c18010041500601984290f0000200c0c0440c0e12061000d17190896030076416034024000c450203c1c40150004c60f500d000040d46040d41d500402e2510183e07402c1000603000b443c4a5030000040250030003100d42c0c000010301805410502c1205e01082000f0b0300020786061028009004a11a140c280750200e5680d10061080840b5000041002d090b00c1d08038044014015400e00650000f01c2d0740001c545065005004c4095188403000030040c1c0c3c00d40a0000c0d00a10401c203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 26149142 1250 26147892 26147897
    0x405010801060e19060f020709111e04080a15050a09021302090402070203030c0304050102060c13231809010506190b0c01020909010303080103050705010c03021b040b13090c0503030a 80
    0x40040c05914090029400f901500030440124580c8042005289003e42c1d0484000070ba507107442c1c4211076404205802c0030b440382c5841804030311a010310000c02405200c0700d104c0075003100c200c7c18011000604c200e0380a800c005050316002c492608100540100c030030380040300d483c130b8a0000f1380303840058440ca91485074001c1034080044421110030019400010f03200b0f5026900300310140050380c0330001003560300e06001c003031030b1079a180100190070060014101ca081100c1000079445003010b84101a09440c800b13000c80d0901c03440040d003101d030240038100140e000304107050501c041112428410f80304030200c01c02400a5540c44050041e101303007000d00318540e6a0412010720a45443d02e0240c003000103101d00050500651000040300e02d1006c0c3d10a0f0041034101b401481800340c10b01c0840007422003802e1401ca200380f180d400039a240c103449010690322030300001c2c0c00c08903510f40d040b0200d40a0014541400d200002c0c44c244014400084116001442c45c100060181804410756801e02400e8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 26150392 1250 26149142 26149157
    0x60e010e01030c09080703060b0a060504060c061505060304141b0a0302091906030f05060a02030618060d020301020a0f182904050405070504050301050702010501051c0f0506010801051b040501 84
    0xa0015009403c54a241c182445105580810114001c10400b4010750140001040c07c00c03070001070003c58144c0f90006420481c040005001140e007060705500510790182c400615001c40c18200c1c070000740c0e50780150340e1160000050000b4008084004821040c000d42a5010400c1c1146030b45c0c00b1040701400c0b95080140f031a0100094a04000d0742c039805480079420f411095520700c405000c03079889410072200351540c449500c05200d800c000f00c03540085101400c52540c103181c00000c01c0c03501d000301850304940b00d85000508540307070042d840ca005603019009640301c021500d1301030240040c480c82e0200003130b01c40d005240200315000101007110f948119030032800403880031100c429810842c0e4408180800c10002455848500c01e281c0700f86c2c0d15581c0c20392103608042c100340c207440c1c1c0034005500b1a0304040040c801c0d580d5202e1180c42c810f5840c014685003c4191420500c08458860017404034000c4000014804c201900010302c40c8c40048040c03040350004400c1e02200f4004c034040c0c05e0008240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 26151642 1250 26150392 26150417
    0x304060b040606092303030f0a0801060905090406020a051207021e06010b070308100b04090b09061f05221202090f0108030901031104090203091e010e120f040f0305060403020601060e01 81
    0x2111184070517112050500c400f4801c819002c41c1c5148d101b501400d03140751000400b9160158404409809000e140c90403101e2103240c000080c00508011b000030706005c0d800031b0f60100c943c0c01101201c2c5132a0000085400c545009400a5100c00710012103000c60584a42c0c4d420322180c003c01c0490599200c09001400e1540c244c808840b450760003440380d174590070040c03000703d41046400c0107440142804031000c00c1c204482c0c007c2c8070305a24082d09880c040c03415182225104601c01c00c1307480000c4141d150861300c8000d103420701040b0003402d0700c01c0343c05086200c1000c070381d280c2c9a52581c00f50b28000c1c0c40d00e01c02e5403210fa400d02440702c000d202d641a540c000307100045040d8840c2d08505128483c46001c41e080c203071140341c1d0f01d040342e10580d03001840d41d1007660b141c98000c581c2e080c42d404150f29000204010b0114031110703074468a0154001c2c035a0032000491161601419056501030010700c11b41d941303116102e10303059503641d02c291400c8c0d015100b4200000740d43e03807041000c0c6004100c1a50356014035501c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 26152892 1250 26151642 26151659
    0x2030d020123070c0503030108060a060e0c1b010209040e1b06070803150a050909010b030c01090b070f0219030c061101051e060a030b0a060311100f120b040603080304060b04060609 79
    0x1e86000204001c04d151100410720800103180a03090440191840b4200300011100311081580000c0e0200d000d02c0810040c00c2200c819078a00d0b0400d448040040f6000c4581c3c01d009114010343e0341d40c024a0145030149003600080d030f80c802d0034035190600c52200c804900304001401505002840c00340b0420000b0354000e512841c07940c041e40c2c080d00d00712405407101e002450340e5030304480d02503403607540e020661030714a41001119140345007070800343c6034a82411a04101e611410001500c50794802d00000d0031034681c0c4441150411510503026481601c0740b408901c00718040c410700c000650041000c60002a041c40303010700480101600200440c2c900021783c0f410f5400402140d0b21620704080040494400a00e891203980035101c000b45081c00c529000071001c20309103000e0300520000041b00e014a4010010030114403060420f8a0440b4841490001400707080d000150094200309000080042400107140120f104480a00102242209101c101c070399030310580d8002400d00408000307505 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 26154142 1250 26152892 26152961
    0x17040e010b0c0a050607030212130203060a0c020708030703081b0301050f0405040206070c15121b0516060204120606090504020102100507090503060c04050a08060705030a0c03021603080402030d0201 87
    0x407081e100340c3d4103000403611030302c2c00c00703a0444c0c51001080d000104424540e041324405a0701082c4103103410f0080c081380d000320b0f50712500245426821036031100260f407002d008100c2071008050700003c0343d945400c0e5140052080d41e040d102e020620b10812801c4401784402c40543e8140c5002501c0c41c514038125104200190030040c1c004c0c0e0708920100500808a81c100000d4005001c03c0070045103050756a0300002e00c80600340f680018500e103001302c2005283c3c0c0e84540c1964607142803400644550b00220841c1c804185400c000780540d10001d8000b5502070b20b086480007050165100700320080d6540d5881043d104100c0b402030058001c542d84c0140c000041d44025001291450200551512100441d00d00310050341c90114034100480e00700311500c0c0a20544001d85000c001a0000e070030001c2000c2c0c020f020140150450b5604c0d508088003051191341546e4802c1803001c80003030a0089801d0140c814071040c1c400364000e000b27518844020340d005004078000c00e140b164020030720460004d920785504 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 26155392 1250 26154142 26154157
    0x815040f020405060d05070f02010b1305091c0201051510080610031104030605090f013e1204030e0901080d110705090103030f02190b040b040c170a17040e010b 70
    0x1141d0030b210120b05911502c1c060101244844400940f038100f0040191961003000d400d0400c5a04008440c812602d94018a00d0280c0700c1c00303004151038440031612404d00b4002c0c81210600110501402c80c4c0ca681508084e000325140344130081d0510010081c82518040c5100c0803001c5110340003c00c0c2d07181040000c403016454141740004521340310388a803810640c03259100352102911a02800290701c01030201c0e9151a0540000300400400c20206005010f17020302d91070907044001c082189403452140300716560300180d900c5075640700030007212001001c01c180e81c194001a80d40ac241d00795403e0070700420341030718041c10040c03843e4000d1800890f00d80349880544031365030003480c50000741a00d034907001d1406144280c030744010381c0f000c2c1c0400910308494400203500d054040403030b82011a0961002542094201780700140d00d0341c4500704044bc45c03032554062001000d1014144048200c04121400310f60310441c80c6062501040503540301d20300560050a155044120040000aa0034001030000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 26156642 1250 26155392 26155421
    0x60f0309020312070204050a020414090a0225120804080d09050a0204050a020301030b0f071d030114100602010f020301140409050f1002070b0606160303020c0109051c020607081504 79
    0x904000703a000c07038180350881808400e07001020510804500e05070140c1d560110364000114146803404110b494a582040d01d000c1c000d0031050041145d132074003901180c222600101248004042c4a0428082e00c440f0800c1540e0441d00708090b00b13484e510824156005a0304444814104100e074140c3d5002040501022541032003581e45031070068985004441c4604800c1300016220b6246043ca086800c0d030040c204a00c40e14107004010301d00f5086084240f000b032003c0d40c0c103a25401e45401003030040216410700100036000d0700400070381200c802c4000b0141e4151360300902000407030307008520990201703020700040c5a00d6880c8098190426910102c1c0c00b80c01142202d00103503080350340b42c4c146152844150082030700002c00a040c0301c506910f072900144c00b958103510b07140740031418414520010000504154000600c1c08071607600f500003d9102e5013240907030f00246004214004101c8201d06428054001d00d00014038084c01180001e2103421480c00500511101c0010800100000d5110030030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 26157892 1250 26156642 26156651
    0x50901081b160b010e0603030a020a08030a020403081305010e01030608070b030c0f0d05040c050a0602030313021201020c0c031e0d11011407050a080f0c04030807150e0a1703040b01060f03 82
    0x3040342110580380860783c007402c1e114000303506040c0520816131005117a14041c0e401045114000340d0700203540600d40d500001c020340c907901d550200c40040e228560000d01481d202203141800c0070450f501650448109032101501d40f03545030015805c0d6910b81c07003180001e402012007045070803540402940e00c406490041032418240048148442e04210705a89616907107000300002c104040c201000903100403130710004403903e40a40256280300042552203003e12540c4030070f00b1912910500e00c4640f10039802035440d040340c4580c081e5907200314040648603100d0a680c402e00c8140600c0c8881c980680c102c060b040905c001c50090b1407024000410001542d80c0d0190780d2021039001d100107015204070380d0f629984d0791f00f01c6001400c22102900003407801d82c8620500030840741c0e8204480440398011003140d01c030740a07070820003c01e0031004941d04900b428403100741c1c100384000c583d04031660b20880040f00c841c03003650301e40109800110340c0146001c203160018813034103001d0410303d0140480c40c43c000c00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 26159142 1250 26157892 26157907
    0xc010207020d0302070f23060a030b0604120218061f020f060f01030b0906010608060d03030f0203010605030103050f0705060706020c0a0f0804060e0312040501030c0903170403030f050901081b 84
    0x442a02c600c001c1640180c00070201070095000e030080710320060034909034040411a2030000103140f2a082c0140b1445034800048058030140603800420080c40300030690f80e12540e03185800040c4e24101c6004a1191208580361807910114118090168201507c1c03003090001000c00003400d0540913812031f0640c071948004800c101d01c1080a94840c90000d010300b10f9035451440c000707102c6031000c0d00d0001640c03c010300512a49503c0302c1915800a41101c01e40c0c1d0a44d59402d00f2b4008089070500400b240d8000000070070000e8200380298103c0b48102d0803100c0d00e00c0510042625240280116a40300504102403004101e20303402030100d074403071801a90450191a520403041085203401100c5018001c02c04004a54011102004e4100e05401405906e00c1d2060304e03090a00c078500400e03040c50340d9a0004040c45100b02004000f45a014490043e911942d40340d5440ca600075200442c001140b001c15522000d05c140240c4809840c181c50f8140a80c441c82202c5a10381043d4111501c80c030b005003c0380 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 26160392 1250 26159142 26159149
    0x3030f071107091a011706190806100303020d050f0706050a2d1a031c02010209090901090b060a0501050706050a1107060204030204050108070e0106030b150406020c0108060a08030d020c01020702 85
    0xd000600b80ca000014000110b8004804111040346544e07045c440340003c0c060b9014070903442290300150884458124068400e101ca85413102c83d048200d04d0722552040107011981c0780c108209803402902100c1540d40100c5048441d441001c01d011421001408048001a40c7d03810980d00b0141ca440042400c1c1095072120b03860041c01a20000e00500c1c1040f1044412a41c2c400c140c410340781a00c503484800b4010010039a60f103800b0000d5110b550b50441c91220084c030030350607204441c50092100d50a41401c2e80e100380a03001d603c406444520030500031940603c0e22099000881320180c44007030500c146621810018007000b01002407403500c40410789130b0410703003030000c0040d544610300060700c0d0307411350041c04119071050304626116800910180f001030204580301d41199428070b0007150100d05030011908618108650344803d6201050104100d0b8002c100349031129820380e038400c1e142e6181c0c4200107410a80b803040030380079007040015610004080d00284041d1220701c0016281003ca540031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 26161642 1250 26160392 26160403
    0x70509040e06060405090d0e120102070c030b0711030415180b03070302130905091e0708031201150c03050d09060207080408060105010f02060402011e1b080a02070f030503030f0711 79
    0x1c07410300d4101008100321407526100721034110540790010a00883c1c01c110142c000d04001c41a284030307900e0325850522400c0250100c41440750b1080b09840030300d54924080300e80c201e068400794003240c4440350b2900c1d0040e0000c1590121aa04550078032900f44888050715041a481c81d20340c001c01e19010041a01a00c680c011402884e8036540181d42d00300200d400c5104045c683c2102a115040505108200b1000100001e44444803200b0b00c400c0e68001c0032040c680711382540b002005020200b610101100b84a000504942c04600700d00c1410b42c00c0c041c2101c0a91310707070310002d02141c4103001142c100c0c01c0c5c035400300504500c507002c014079000702a1120f03003050300141c0c08081d4a0f8040c0c0010711081d43c0c0000740714105600c80c0010001ca050035800a0481c655604090404495180c40300c071600e441203080302c115641100e40d040c03d10342d16051885256000d041d04c1005481082c00c0003c80e0081701c5405404c594002c3c000c1c60664031603142c2c815159034040e220400b040000c0c100e0300043c88080c0031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 26162892 1250 26161642 26161661
    0x1060813060614030d05031b210702010b010f030902090a020f040b030a020712020601030809091504090303090210050901090311031212010608060609100f12060e040b06060301030503040b0307050904 87
    0x72151007441c6140201894010480f1140382046002d0041c0059110100030405400b081500b0041d182c203527007000800060300d040d4184581c80d0b0b01c001407000d4035406500c403581e152020303690910121402d9030203074192851003c0007034100a52a000501400b25a4050b001c14100c0c469054540346c0d41e1f54003c6640d0f00240d40342035101f580017594004001c0d0308180c1d0540503c050014100b03079807654444054900034425454040e0140e0070006007242d40301d40546101010091041102a5040c20001c3c014410000100d0180c0703000713021140c01e1230240d020340c2e04111050391954462400c541d90b0090b81c114020314640c061103000d03d01082502040007815800d41c0004060007035603d880340c01000c46030050301d458000c8008201365141929600d403034880f080316074106429a1866071004176400f943c540040c0310300342d1908001003450280f0246c264052806150b002c989a1200130401003a44000e01c0000c1141c0c0c810001086490403c0d00510703404482400c0140c100b91900e00458151444400d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 26164142 1250 26162892 26162909
    0xc0a060215070306080601030f02130204060e04060503010203092a03070305160e0601050706020307020a02060c2a090402010c030909050a0e0d09081b0604170304060206070c0b010608130606 83
    0x1003201d45003a070070204803503006480786001c0c04010720b810b5982d5103480e8180005014040c54451601c1591102c44003001d0200a00001715502d40d035505009281c09a1001d00c41e11a905100740001c55203014001d03280140705220140400601d243c5081506111602ca8550031009103611a1515030f4244002c81c0150f0241010300360040310b1002201184000d50010744034001070205000300380e43d20000390340390140d01c1440181c0e240c0301c4071800d03440c2410745203009601200005400300c000314042002090b000c40300d4076801c00ca2404640340c60440300c8105610340c101c81c20070001401f540c0310721050351044d4080d04282c0e5041d520b4460b4903054601c1151030100d0581c480664000303a4034100f045440700365048c0741c00c1860314207061840d82c44034484080003902c1140180c2c000e005580b04011140240100b0102013001c0d44222002d0ba12a0040e114040250252600003081c00f4003440e80c0c101c00aa0180444040360b00702035069440180c00741ca8080c40c0c4164542c40000078400d407161001401941 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 26165392 1250 26164142 26164153
    0x70c02040f0219023007030e030109080c150c030606072904020918070902130f03050604120801030b0408070602070b090f120705060a020901030e0a080a030609020f030609090c0a0602 80
    0x5950191400c000b0580d51460b1182d01e07884178a0002912042c8490500b480f00340320ba4815003130400701c800c802c4240c24903500d5460300510008000f50800103101014400040c0c1e8045140c01a01200090084903100204007042000980514221000340203c501c0352002046401d10620740240600811400b40004003900060000358500031600c80d6001d4103501250841c04180080725031101958828a142544c001c82c11000106060000d1400340201c40d94002c0499074900340140e41c1d0105071001d03114201c0ca0200031144034869420181070329040102c90600362201d0b51502000d42c8502800d864440e402e1103023100007500d400314140110300480080440c4c04502d00c00c18104038402c9d04014094008001010006501058455001020586c010b0b2030350700010058002d01040451065140100c007640000c100343d800c09042c95205568040210301d0303d6080840817840303890140380081e4000c0c80000d4a030702d0f20005051307000035103800762107400d00010007161441980d50000809078104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 26166642 1250 26165392 26165437
    0x20703060c030924142502190303090b06010801050a060e030a08031306060509160806030a0203120301080606100c0204150b0406090305060f0103170706110d020c0f01050609070c02040f02 82
    0x102e01581a03200e01c801e4266005c0c1c1061144084400b1400103e401c608a8020b440800140284041c504400d4214034081c00c8400310f28004001b842441c3c800c8400d080a2004070b0403e500c2020302a0503070301c0140042400c907080c103a0990750703892074244407a03151003580c85900001c3e210201a40c09040036008003407400f070042c54010143d41c8140c00c00c0307004110003001c00c40a4048080c00c00304c0d441d0385040041460302d6100211381000c0f84d4184c0a5058420503c241c11324a110340000c5040792204010b5402d16102c1d241000000d058600780200003a0703034400d03000c0242c5400e9001d1100c3c07a10160247c120180d481c4600d03240b6401552010001c01c800c54010030500c1420300880c0e5011b4040f0302159019130441ea100ca824100e403540c03449540c040071130385a0801c4400d50100c000040c000040c140c0365280c101c042800303540903040070005401008032502c2c0c0c08030f0501407a401401e005010300000d55602070101c0d4061880202607900075241c040e0f290300401284002e02c0503484441e600e40300e4951 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 26167892 1250 26166642 26166713
    0x603060605100c080417010905030a0f08010602060105030a0b071e0305070f030603050712080706051003030f0309120e03030906030c03010303200a030509060415080108011a01020703060c0309 84
    0x111001e030381032100f0002800300013a540c008603026603010003601802c450110400704c2c01081e000038000c18601c80003554201d402c2c0c1151925058403440d54138180f80e80e0300d8280032601c3c0c040030b214807609540302400c0c03080080c0241030b2640d40449a03143c401400c5040c0c40c042034036074040d20066404070751b8800038088500d5000b0b03483d00b80204241400d1022a00e569281070340c2d295a031041c980024402e4414804001200c01240d06141e0001424012803e011860301c2c0003903600e21088002c5140b1202c5004102d0007401499146034000d00200700a418914041d514070720b00315492681800104080000c0f41e5a50020f0740c040c140c22030351152658111b2030098024a0300010300340015612040780b05105000040111110b40e1520344a600da00450011608a00481d00b081c400740004c0100c8552079644140301070304079800d540c003c1c031212603095a200318411200b10441e00680042c8014404150700e0307008007803c408149800605102c50f616038111078620a0280594118609480085401d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 26169142 1250 26167892 26167909
    0x30507050301060f05040f1107080406080f0c0304020904020109050a090f0c020c130207020a0f0e04020306150a05122415031b0909160b0903070e010e0c030907090603060605 76
    0x10160000c109150130310389000d96521952041c684510303141c0d0354212441d00c071504081c1080110101090300d4048500d03258001c5d80150181e0b9002a00e50000a8600003c800545008102d08483c0702c1c6591144c1d024131014110091080c0d042c051080790000c0c02c0c4d2122800840184a804030015114481c03150000036142c90203006011913000000d0b8000c03030f40d101140800e02c00301c00000141e5400c01c907c0490301582c02548203001d00100f0010000c0d145850b503882502c00c0d4822801c1c2d0325113035200d0440e00c2104050750311154114501c41c1d01030125043c84200d000f0000c085000700d55643c0c1074045004d08005103031503409000c50f45c917018800ca0508007800d00a0105048014000d40300780b59040c0c2c8029000f040c80584180c9020011030700031881800075240c05801c240c1d40d0b050f0641c58008140442e0b10003041d40c0e0180c416032100190068118a000307040ea001c240c0c1c0d010b0309450794808800d590300007070201210381c0a00403001550b01014450031000314401d250210381d1900d040200030040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 26170392 1250 26169142 26169149
    0x1020c06030a02040905100501051b010603060f0207021809031c0908030a0608060a020408030d0203071b050c0f0306091b060c0a0c0515031303031e060f0503010501061e0f0c0b0f01030507 82
    0x7c1215450501281c0c1c3c0000c02c0d1100b525205c0103000781c5141c8503c103a4050210340d400946142e2502d00c401c540c1c000288c00403c2054000e5031117050099451168105d1928111601c040d1504280500300181940c2d40c80070362803840e09400810200d00c5a101c1e01d80c654419603d0390740e8280e441404003c3c070a03040c4191035002e54070240442c00c162604400030386a02c60310011380345c01f83e400400101000d016200000c00079a5030f40464448205074600b0382da4503044071040b10b11451521940f9815480d002400781d1180c0180b42c05062010b08281d403d0540403584282603900850610850062030300c01c1045841040c05206184201d034078000034064a5502c8009a03130100d401042084454504000706000003945460001402c107146c03148481d5192200d0811a1b81d83e0034524006100800d407000b43c81a140100c1c02046140d0f84d420341a02d1210400100314400d013101640916440d0041540c000c0050f00c43c20720b0b40b0112416559072030349001c1161005406c04141d0010700510204001d1007014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 26171642 1250 26170392 26170411
    0x4060e0709030308070912030806130209030714040b030d0509040f090b0402330d06060c0b0c0d06090e06040b06120c060c250e0a0501050d0f0201020c06030a02040905 73
    0x141001000240550780380d0102a05104541021601e160b21445441006140da98003a0100f10140d00d8020070b88641502c5403486446900c101006800444c400c54112403002401807030000d1402001680c1e120f01d00b140191300c42e9503000f003090140c605000100c1c14040030b581740d6a40c2e6076541d080108403120780d003000c1c2d072070f61410141d08001801d000106400a070100c80d605903250101c08404000c0755060b80f104480e80100c011440c0300c08010001e05512081f40005100154a9150071241c010720903002503c0001392802240184011034000e108514000c200800c100f5141c1540c002580c01c0034107415901c0c0c0c031070710802091000007004160805000c1303030f480c13a00d04c01103101241d0700c100d01c00f400d6219400010703074200c2c445e03020481c20003100b201f03105010100d55131518860000710f051003604020300d00d210005040700b950740304140c180d0385e00501c03403000c0070a1030b1241401c03c98501403c80c198400c0c1d81c000401e55850030041c61003000c81500150b604d5081032010801d0f5180a0142d554 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 26172892 1250 26171642 26171669
    0xe0c0d0803040606210201030906090501021602031002030705030708090109050109080703080901110a0e060405090f04051b01120b030309130e0d0c020d030323070306061713060c050906030112020406 87
    0x3440755001743c1d11005809107404a50320b00c07a410440300400c041000180303158030000c1c2000f408000710001410141c000c80646d40e84052607000c080681c4002c07140358001070001c10006211078002c4e450160041c02680001850b0704007581c41508480820704c082e85e0f8468003044000c20144e124014070790020301d0100900c40b00007624a2400c260141c200703600c0c1030112207403107200142c551005850040c00c0042000d180c60510350700302c903404102510256410b000d41c00348841c4540800001c10080d12060307541110316a00000c2404c0100380300699a40d141c0403c1094080c1940c82d40142120051094000201002c10410091412003000c0303007001440f0400070004003527901c460ba0b021a86805003808109000784a200501d1480e03110100000b0f642c100060140c815816884907003950b559480d00d8044880401c0b28400c0c900b012a030b4003c682c02c0c0807407400006819074000d500000c01d81c0c20143c5c00d00c2c1d035843c000380890300241c0021035020985c0030705c04203524003405150001c01d9000b55141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 26174142 1250 26172892 26172929
    0x415020102090108010311120610030b130c03030c020a0905071d030c0603010504020309030408120d0c0806100309171b15192703030b010206010b090307090e0c0d0803040606 76
    0x20f2082005110247c40c3c0c0d0480e40703414400d9268058031044079421242600c501c1e20b001d003186e000340c4109000c00e84180e08654005602070792031000da40311540e007108810007040e246030740480d110010184220380001541d0b0340054080c9950150398021355640d22043c1014080c50600e00b000c40104a0b0a84243d100e420003510988541c03086a054034416680940e0f00c0d5074010b1000c1c9135201e07a6004011600c82c07203042541d81545d41d0003600c004107103c44184800800d030003044070310303907400e036003003580002c80c0b4205000d080d000307a1058200c5c6100f00105d54000b91801544c19150700001003140751507641c10004400e0301c400784020600204029540c000a0030b11200c40b008000c11031540d42601a9964100f65202c0200030341b480041d96403480030f10740008070340380060281014041c42c44c0584070340700c00891001282ca0075a482070358090002c0c400103242c80301c13002c0078218120410300d00303001c2c2c0030846007503441301a0105112800b9503401660307070602c0d2804070100c0d882540720090505204c600c25 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 26175392 1250 26174142 26174147
    0x6030b010807180506030c04050a12150605090c0c0c1f020f01060803030105120106030203030406030b12010c050d0f0608030703230a0e1e280e090c0405090a050a060204150201020901 80
    0xb402c0d15010380e03005da200d940e00d50a9a18902c9541c00a603405410710100080c220075110032a43c420b44106850345280e880d02c650f40d0143d601502030b043d40500700e038000951907031641300501440044082140d80d070031400404070305140141c219002d10600d64030000c1d20b1980d010441e00070618080c0000300401894294030315180d00060040d1480360446104a01c011042500204041d54005003560b55495442e0000340c0100704944085005900713010031150241010b12610030700301c01e41e45426140081c010300e418010800040c0007201103554907030100c1d8284080026060715071103034803020743c282c21395450030000200c004035020070801d0810019007001d078446c6101c11800001d40340340c00904058004405201020a000c540000c1540201100500304081c01d850f1101c0d850b003020110340e02c0ba240c1c4c0c3d2040108950061040e4000003906000d81003e034000c90f130001c01c0d20180d0308011805d5940fa8240710300c00c0030640e0322a4010900784204201305115081c4848617000841c80c080e00a00003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 26176642 1250 26175392 26175437
    0x6030a080304020105120903090406050303070b010902030604020d1802041b0e0103050a02040801020c07030c0929030a15020405030c0105030103050a110f120715050f040306020c01090c06030b010807 87
    0x6058240c040041070441e401842560180b00003600e44441510700b41d1205903403604000705a900c190f043c0b8000040c1c13801c02004998040b85c1058036501168205800395010790310242c00c6c00d4225500704030041d07000506124015140390001d1015038200420300402007610340210700110341801c20b13a5501c544a0300301c078510b0301c200340a00340031850382e880391200c80090081e980518281e500004040d042c612012451400b943e110f20345810300e440c0c0b41e000081c102d0b01c981d00e40703102144400c07501c1c0551001140c001c13038882c03900030100c0f07131604126610b00d40a400b50040c40610143c01003170520aa14003400b1080c036802080c40c150303055600d9074a07219600c100c0050040c290040760ba89840d500d813101000c990384000d02a100c043d1404d02c19502c0c0c0c0d610309042c402c02007044040c061038140f8a1140c003c41d01980c0b16424101d040c0b9095843d008002d50001c80c1e0042d16660303448007000011007101002c0700801c0107480009220202000241055000804400c00c00058403202405850140c81 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 26177892 1250 26176642 26176663
    0xa080609010b04050907030b0d06050115080a0e07050d050f030f0408060c0306010f080703061511070801060f030b090a0605040c14100504120203030c10050117120304030302030408070b07120e060603 87
    0x21f011034035095101c00b02d222800070a001174001400d10001240b05041007401c50024450b0380e1b51003120341e071a039500c641140d48441b024030064002c20402c11840c50080c8410305814040c206a0712842c0d020f05495207160b104404039548080b0108007001039100603c05d2651141d551a03640340b5610340358000a0203920352044900c01e0185110105801c10b10aa003c440038042c8494003000301c18090001501042118032191034510503164003262002040c0103082c2107072459405041071600315529080f041d032004007265000d2003004c03010804142103009aa006500404034100c1060400c2078891001401880241c000d04458031046286940710f021141105c41164031495085140d00c002406e41c800c003000c06800e441115110040311040b07030301842c1202c2e45e052401c240b0b0028850225143e40111101c3d024603481440014080b0b400b80c4c0055500c41e1094030705610381a0700b075441d0551041d050b50744100060600c02c52460803403180c82481c0c14007000300003c108030310f40140007030795441010f003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 26179142 1250 26177892 26177897
    0x30f0f030703050c03070c030501150807030b130311012405010c020d060e03040315060603180302120d0603020301180501050c16020d061104061d04020418090302070b0a080609010b04050907 83
    0x1400410131000748240d68405500440035944d00e0703500d04100d070280090041205c2d0900c4031000025041000090703034000c4990000950049948840d00400410319a1805400b8031840e0300801088000038855400341201314aa94400052001020040c042c3c0940010741400044c00d4102d015980b14018804180d07031084c408610301c0d00c0f10507580c0c214043d03544000c060101c2c04289600c6039241d41c0002c0b050703901544e01000250580c1d140c44003292401d42000e00960009101c0b0004c2c1c3d0b074079900600c1080301d0030034041021996940805e00b10b80c010103c9084940c240d107040c00810000b070003681d80150202d1403041c1454000c0204210f25880c80c1c100a1048060383c130740c01c0402600c4d41000a4295000c040b035902c8541d2403c015140202d0032201109042c21400c1e1600719103800c0c8251384c15902007070b860602e0078080e5010702c3c0080c541c0300c6003942948104400054014091001081100c2056540c822641003c105203c8001c4060300b014074005010f010a0000d41ca540123059840000c1d032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 26180392 1250 26179142 26179147
    0x7050901020c040b0a0801230a0c0f050a02150403030e0c0f0f0909010b041107030207050d030804230709020406030b04020c0309010516020a030b04020102150906151f02010902030f0f03070305 84
    0x550036a1140c1c000f050650a103404031104190070507086080c5008c5600f01d85041d51007001000c01c4400306072001001c2a0921522050b051007035010303108800a0b030040310003020401d55214613080e0222000c4002070f03190f040c0900c41002c24081608180c6066800004c0301c54200d001824503800502c40303074000d90b000000606041025040b1488010b40980100080700c2440d1025542d648086010782c0980700301d0500048030300b01050f85900d120780590b58051746417200c2d95110f8091100c100080385074040d80c40c0e0007003404414410640148049100160f440b8545903014003500c0740007204510507031040c409080360700750100850f0030707903082442e10355550f810000c0c40d111002c2145070081c0d0000440100481041007008025009030b000b42c0844d400ca1840a9084c00400003c96212500d80c12031130104000c01c001342100c6090b4003008181c6015400b440114800c0645000c4050700180c1d11544503505600b01072040d0a50800f403400070f444602d1840024964a2140100080c20080700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 26181642 1250 26180392 26180411
    0x304090e030904060611061e0c18040f0b120307020303040303141e04090f0b0a0303110309030303090c0a080a110d02040207080a0c0b0a0b01120c05070c170607050901020c04 76
    0x184202c0d030074060010020002e03642c448200078142001e141e590f845503c541c001091203800e80c0d980d400b07060140c8107072500a42d91850381501998100181d000c000740400381c4a92115500c50280e01c0c2601445080060341c580600308025200020b1036000d400340d0001c00c40c1d807016880110071541a240c0504090f420b560103400144094401e505441c4080801011049142d5044d04010812186048424424682d04c94011821220301c44d4240b580720b4611182000003a01462504680c1045c0740d003035905002041e404a0f044d41e0040b01c80d01c6e034540103501360805e03c0c6003248050029204000043c5608000f80e5903c00d01a03000903212440380244060340c00c115580e5030100c0c1c1c880c40c3d1050300540c850700ca001020b0803541480c20101c0702c0c80703503020016001200324807400074031880503035800341031001c1008030000801117190074104222040125070049510800350314001d18014029078184c0a1102906041905c040c100c0c204004040045850341d82c7d00043e17901002404460001700c03c0003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 26182892 1250 26181642 26181671
    0x7030503040f1b090509061006120507181202180402030a03081302220c110705040b0f0d2315040803100810020c010609060302061606020408030304080a170405030409 73
    0x240f2105448004503409008582c004e502e800043c00340300084122070660703d5215403440c3e600e80502440d0300050208070b600b0242812030b040a9000380850428188010313454031040031152a68000001d80c0900d66421003c6052489004107224509603414403941010b80c0000d403201c1710050003808102c40701021400810010141000481d4000c03c100101c20406500d0b90150790b4089848109900d060720f2504a0350048130858030281c4440d016000c3d9a080900700f100030000022800e070020a4082186203545440217000c3d0324030b0040303c55010110340107400030b0340d43e01c000301c54900c1c2e9044028985080720505a01c142c10a621400c040e840741d941c003002090412a41d40115840d204014200d807d0070803d500030002100c11b03400a01845846001c86400e0300c2040c84000e400603030410542c440f07260742801400c3c1c0240b00381005490b2550f5070640600d10b070001c2d20f050359801400503040780c100c0d80015111101c03a0308080300041d1442c250b20303203039142c0c0114422002070300e840354403010710041c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 26184142 1250 26182892 26182913
    0x70e01110601051f0e030307030305090609120307030218030a0606050a0f08030901120b0a03030806010906093008040305010b0f030a1203020901111b01020f061302010507020619080a0f0207030503040f 88
    0x113502601f100d44500042c10010003414080d85d029042d802001c0c04205086004111340070002882d043c3d4900d182c4428400710000d41c03000018811000c2c8003410ba201554061102121681c058840850b402d0301300000c010101203560b100503540e0100e403404100b160404001d60b5070a0009080407812854500042006810a4010154400c1d44a4008400c25810100e500d009020a03641e90001640720030058230340d000e0600801d40e5001103401011800084c113003501a03400d8108030504581c442c1c0381e40c0c5c11036039042500101d4080e51145025291800c09a40c0e0412a030781c11001010280d607180c40703100c10800008107410405800150401140c0d00484042140c03019102c11100005c5207113400000911400c80202e0060280a240302e40040f40000c1c1e203402140d00240c0b140005990341c0c01910035901c0b00d20b049801413018841c21090b0303e818a200e0311003080c00d4807800c040e071401c140c8000485136120762406001e403050100c40042035000f01540c2c2d009500c0b464024460140b400d0154103030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 26185392 1250 26184142 26184167
    0x60915050918010303020c030a0302071502070506030103050c032a0f06041221050a020601060c03031401120c0b0408100f06090e0d0e040605060a051c05070e01110601051f 75
    0x1c5851181c690b900118046014100c034000e5080d250010703480420981c90b10654100600140e011351400c2c8420000703000940a040c1c003d0046640159503031780411034681090b071003500c2d6504169002c6055080c00d10060b0f070f10076490310034a500d83c241d00c00b9007800781d4002c480c000c3c0a40c1001100d07039807544502040310040c1c8607180800480742c2c2c1c2c0b4030308034a40d900a90b603080e00c041c0c0c8660b68504118015400e5488049042c0c0140106a080c2041210314204003d4190f0401d0703120941001c0c1058116003290107081404050224100c0a041c0440c0002103a4468030131030b482003000700440e840c04100c0da0030b0310007000c402241c2c02000c800f05a015001c00d07080200c078280b0f0400c1166004c41b00203074800000e1030580b540c85290148500b00700449400e03100342c0f17420500400c41500f01c94800c50042c4058203c5003401e0300c01001b840e030240215041103035000046080c054101017590307045001c2240d00d604550090201e9810440480c0da814098400a203017244c81e0288102a180190b9280289 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 26186642 1250 26185392 26185399
    0xe1003050118050c0409020f060d0908070f030f020d090501120f06090c1d0a1202010c060e0c040f1a06070203030708030c03060a0b03060108040b06030705060c030d0b0303040609150509 81
    0x38188400d0340c000c0d144510b050200c072103200300c4840044034102806100c007020f80081c00000e04d40713680010b20500780d004414046645907100f00c140700044029014003040780c0030711540c80705410a450003030185807840c0c41d103400b0755014045103410603034051a02819107500780381084400c402d006464000c0d160186540a07001d0a14401140103030040c1e0000341101229660240301404181c1070002180c400348807207407c00301402c018401c00d1f034040504610140b0602d488410000c0c562901801c4800700100c040f144d401178034607501c4903e401e01400c8040805090108002516100c00c404001c080b560114010607020413603109565060094900303058219100c0c030340ea49410a400c14060b441240c04e648100b908a40c046140008281603a00c1618180c5610a82d510f0f2501c845541083c01081c203070341032007003900119483c0c550740044c09608120350011512900004040b4081c3c0c1c2d09180b10a003c0d6006000411050741d2003040d410032a000c541440c10902c0310b144e001c50b400d00c107641d0902e41 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 26187892 1250 26186642 26186651
    0x17031f0501030b030c150f07150c0906050d05070c0203030307020601090c02010209010818030723011503080a0309080405030708010509010b030606010f05030a0209060a120b030106120b0901020405030a0b0a0507050301030c0e10030501 102
    0x6109c001c00c6103809a16010204021110795071078103440495240c007801000400c1800703040d10360501588455004034990621244261b0903030b000134910f038011142d10005070030180040208010500960b50503400c94002503007400ca520000a001a1009180c40b80c64819440448140340d814407ca407400b41e000740480703081400d1040e02d018142c040702c0702d240381036107014002c800c0311200c03a42c9030082e00c0d80049642d181c1205804124040d1462243c2603031021b0707080200003140d40d8100000002003200600100d901e1400744801800c55410b170880c0e500a810180411803e030381d101802480011a60030304545940b44d81580e200240900d0790a1a04410001207114409030030010000d0442042e80081c020802c280b820315027624114403400c601540c0d41015071000440c10360801da8443c0c401400141002d6032540002d00e0405030f0719003655180140d0052000c4c41205009503540300c01c00381001491540b4558440046243c6840360b205d81c01e009202103011164440400001180c00100174803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 26189142 1250 26187892 26187907
    0xd020607050a0b0c120112060e01020307030f110c0c010503071b03210b1302161b03140a030203090d020d150507120605060d0917031f0501030b030c150f 67
    0xb0307500e4080314400e461810310200051034028107002140e405d1503034810f5a220701c3e4030300010041c049500c00812643d1a44a42100400107800d20165200d5042c554000c1903040900f03a0481c02ca813864610a8807442c8100000c2c03144110008140e04107000a01e406562596001011031390030b0b80d02e000c9401e440c00c2e002e002005050703220740e8100b08440100c0850030081c0a400c550000c891104440a4100d040707510b00d140700301c0311640580789016200f541c031500002c1c1d503900c0240c10b4035050380030000d4103021401401486061005980c01805000084c03032502c2d50b0707880280d900e00540410398450440040c12030215156a1040c020340c1d94440309994507400c1141001d80500070032509c41d00010780800030000115003d01668044920207858945481c43c1d80c420800030b04149401030380d002804c054001c4920846800541c8074211075840f010419190765152218100140e22050400d810070400c0882030340c011426540c1030204444c1e26440031040500040c8602800d20b42d004445008595007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 26190392 1250 26189142 26189153
    0x9040305190906030507020604050d0e0a0e0c03250801051c02040f0506130612060c140c03040302030c0f1c03110307030305090c010807090b0901031e0b03120c030a0503060d020607 79
    0x210700380ca03c01c0d101071040d40c1d1540d104076a580c0c0c0844001e406130340701500c400c0c1c8103401141c9403e410b02c0040c2c6103403038150f200c1d03075403069210013554005020308000007005000190380c03000d05054004051011080c3d506050010090070040c052107104a4401410104140c009543d60949980c00703041440140700d0349010740000e05003240c013580109100e102c100c951242c60306c00c8805690821014054003412902c41c940100500d451003024480c0d070110702c06411408102816015000c4001503680e03d0540c8145414800303075000da40e00039074074071222980980d2110480000743c80303202568403500c069410200e4002c070905c84104003d000000c0c1600600d5410740005100d03480e10b00032940d0f0b640140c0b00440d031140040f501400007480094040c0708240e00c21000b00440300d07052402041203500d00781e540da20003183c580400041981e500700c5c802e03141404e00129000c6010342c07031030504107090844083d07228804e511b4400e0402c08000002003441e03071250042d51140d9006000b064aa0140340b0f400c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 26191642 1250 26190392 26190407
    0x2607060e0313050a15050309030c07080d090801150b070201090510090e06031b120a0209010f240504050d03090f030b10080303060a03140c040903030501170304050904020904030519 79
    0x8241d1075103140c6002244606100c2440000c0f940e04c881201c801c00d0b5182d40031182504090201023103130004000072003013140200035000140a00d000035208182151401405245071075004c00c1d4164108003840c044480e01c00e034034100b1511024540341d510402880102d50845843c1c00007948a07881602e1040e850740d125961101303036440150f0a154548900080603071320012125000b4143c11001d0f0440702030700340207500130480552541218001300b01540054030f00c0809800c07120b04c5503080a000c000c3d10103241c0e505021440b0580300700b0400c400804005040d4415401a54000c0c4003000c250810036204060300e00080030040c01c0140c20740d8170303072511090210342900c0c8001c501d4000c01002ca1040400300403030340142002442e0b11625440d660fa03d00c1c4400075404c907102030707000301c4591040603229402010051442a500000c1541c10915000400007803440502c025500521090009032200c001080e005501103074201150384d175038541100c843c03040010541d01031088140d14049150132120 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 26192892 1250 26191642 26191657
    0x100c030b0a08030903030301060c0f120314180c09070504090504050c010306080d0509040c030204080d020c0907090b0706021e07050106140d020f0f060c0d020a140601032607060e03 79
    0x841e0140190b80b840300941d030340222458141d16070001c00041142600420150080a2203100c040001d5009a00c6409090700b0003801040444c5c1c40340e20301c01d1142418110345e0303413294500c0f03107888402c1ca4008180750b441e461208514024034034074012455860165090354000d00003100c1c10b000c81d140c586000c0f0380b41d18100c504640400e00700030000c1030100c00414401c1c02031601760784040c20710602d03404001c050420448104241a400c0201241080301800001005d226a8008003003400c5694240104000018450380410581d21820b10600711030804031881141c20210268a95103c2c645081043c0c46182c6100100180042c007902001019006402110240804030070f030150a50207000780036690000096200c00341024040c0a8900800d2014030400c020b86030605100015031858500200e004d40c0d10302591010048104000200d41b8030810301140001070641c1b5450740e074a98410149040310045201c0d006158040c10300d08a505a65030603402800502190710031074481603e07603102c0c0302d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 26194142 1250 26192892 26192899
    0x1b0309040e060f07051303230c01110a02060306190807090b03062707030c09060e01050d0b04032102030f190902060d0b010507020d0501020c061005030606010e03100c030b 75
    0x940441c4003040071803040d2040301e43c6001240956940c1c4412240b030341c081501800d04008991000c00400e0848c4984903210b0a002e0101c580f9604a1401c1c6151040200c05141008408140611421004200c43d802190b056a00c2901c980b1514002103011003c81160030503800007900005201d140011003808403410001c080003400c2c103040a06448030811210800e80030018010140d052280701c124554500b90001501c45180e01c0c0d07564804c18031402e0340030640580d20f4220038402c2400341c0f41c0781d40c01414100da500341b040d6895550081603040c020400f03400c3c8218104e0451604554507003050402020000841d502d00e07004001d00c06455007944c0d4a580010f180c5d0080340070080500c9821402c0d90024a070038205502d02443d07802401c004d0380f9060402106000401c0140c0316064a10400d9205100260f00c1e80e03500c048041c68084010075041c2c1410140c1001c00c01501c001c95500e400410a20b0a01c11000d12180400d00d01030280544004640c5040300c0b00c80040c0c4c2c1030740040c00c10704048 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 26195392 1250 26194142 26194151
    0xf061b02030d1e02070807270f020c0f010612080a0207090f1409030a0c080a020c03030403050703110d11210d030c020c040608030f090f0d03020703060b0603010602060403030c03021b030904 83
    0x10030040385c0c1e8201070701403210160300401050000804030803510143e40e8000c400340e80030701a50414201642c40c4d5440c0d0210850b00420390066a50b4140041085414107200800c20305144c8460500400d9113007102504003000052140d0032030388280030342c00190450501c140501d440a0620700000d0090301244098280c5100c04a540c64401000700d81f075006103641d402000070000d0b1180e2500e035009118940a62250b5014500c0640341070002e03000460041000e458000e18504114000c004020b0f2442c1c41a0302180c41c607000154007801c000d140c008251581015a000240f10700d01100010038800c2c407610401880d4106542e041d0005030400c00103501f9a02d2078600391042c042542c0c4a4050742201390010710030f0011581c2e011001e022000b0006050082200e0040045000003040420590040e000000c007030003401180d002d8299446000d442082c03466241c564001e48860001d4001010542c80b010f8100229100f40c060312440040c3d40c2c21070750800c3c0501c84d600d13907070707401202c10a000742d091 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 26196642 1250 26195392 26195447
    0x1030b070c050303070807020705030f031c0e15040606120602190e0d020d020a051f0207060e090627070504140306042d051506010e09010f061b02030d 66
    0x1c0d005485003540c800d0086003541c80d90345059403c0a00200000e0840c400c51f000041d90340d4080000280001420001d180c2d900d04408402403607601d0704030072020349800c0c415020340440c00000c03000009004440a00c2850715589030000c046e00d07c903444920508501c002c1c60302489a99401441203a5032900743d454401b9030041d0581d245c58445036070681c46040e1002c51005170804a056258480c401043c6006064a4200160394032920303030b4070380051600032003e420304190100801c4004e4500ca0a00754a02040e101c0041e9480b03100900d0b1501031440414021a00070007450f500156140c03a1014070030a00e4100001403c81d08280310300e90600b0508000d00025050205655004640242c1d2061030304150b002e031b5a01400007a41515410301803000101c1c0401e4042c0121030700784039031400c1c408107820100001072000c040203400314481c02a5800400071200356046a80c00c50300c3c00d0400d0711141c4c0c0741d4140503081d007031104070181d0940a40c4e54042c1c009544604803148000c031000640094404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 26197892 1250 26196642 26196647
    0x110604030509091e010b09120303181603020a090c05090d03020c0f060705060a0902031005040605061201022a2109010311040303020606010e040608150115110703060b0a050607080301030b07 83
    0x140052880340c4c000d0401801040d040c0c20061801d07410241c205840c03141400296880c660080b901c19a4030035001d00321311030304030043c040ca43c440b82d000348603005002e0458001511502ca24414032158641d00d102251343d00d4018015102e148000504000002c1d01a0034040c6d1901c03c54440c4510179510407000062a103420019558030700c0e0040c006080c00ea544001800042040c83d9050342d0500c82d030064400129014083d261040703114003000700340c0d41005400c0c0081d090200f16084051790041c0280302202208103114100d0f0b04840c401e5802c580001324010b400e107480d52000282d114105558440121089001426120008e98040101c890081d00600079070285000040044c1c01c1480440c50035880780041c030380001e6004000003452561703200e8040c502271100a095501c0304030140104040f00000300c4180c02403200741400e07190b09100000d00d40d244d1203280002040c0c03542c0c5140c4107119485d821034070806050054095a0383d003120342441d103150f400901c8220b402c2a58100021031861 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 26199142 1250 26197892 26197921
    0xb091f0906030f020f0a030206030a090302071208070f0809040c050301050a050607020a09020306011403010306090203011104050117040c1d04060c0e0a05010c02040b060d0f0e0606030a1211060403050909 89
    0x20f4000701003842c0c0c0074543e13081000c1106040e201503803002803c280800580c2d1404015409040080740010711120780b4580603081c00d0082d804001155100e40b01d50780850040b4049401c031945c404120034480d5060301e490301c3c0f240a20f400e82c41d049468000c5401c0c019410070015070503a0012100200d00d00c0d607500400c40780703101d03102000303422090b90702c01008503103100c7c0c010b5138003d02c050401a0700341004241d0703070085400c260310076503416803a0504501541800e2040750032089100d20404d10385418400041c15560805490b900394500c0e000000303007401b0300c4030400400750000079045680750102d03d40381020310344140c4095481500d09100c1d480e025001c1d812b0042c1040c009010324500e140341c00c005540c00303400e401c010383e001901ca034046005070340d999006020444140c007001550303a40c8440c03c1001c440708030703400c55041d42c441420704c003050341d000400040b260b03800901c11301400c1025408030390007628a4481b81d03143c80f0310f100303000c10160044042c01c001d00003901c8000550340ea006540c1c5004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 26200392 1250 26199142 26199149
    0x3031806150612090a1a0a0506011e050c0309040e0c0a090204060e01050d0b030609010c1202090a0509061c0305040303111b04020f160f060c080108030d050a0b091f0906 74
    0x2c0d0301040803400300b00350b00d0546a4401480c0c420764000c0c4055407194410300c1c00e1074030880362a020410810000d209184540c5400810a103042021328825202f0144590124003035941071010210700d2220300c0d40b0407c00c540c10107501a1090118400ea0481d80707a94400c0300039600d124000f07180c0081440085031003a0740860300380b5a100c134083c400440054420758011602070b43e049885a003410045e4034104070b91405502c8440000030100c19914005010030780c610745512000303004000100890f03079044400f200f17560044540c100140c54200006406000301200c1400001080119106054102025100300ca000b41c50b2010003070400c407101d684540038800003000300500587c0f00d10340d908042e0f01500c0c2106910a0207407518141403800ca00c0842e0400b0101d0b56040200580700401010b0700603101074041c20300b00645c280d41000300064803402250420f60800fa52400041c0040da259001410903082c044c0c010000d9041000382d03240759441095a50080d070109180c00200b0804510404045 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 26201642 1250 26200392 26200399
    0x40c050a02030d0b010e03010e0705011103070302060f060f0306010b040302090a0c0c030c030504090f060504110301030f0303020702031006030303090b091b0105030a020915190507020a0302040c0309050303180615 93
    0x400700003583e09002044c03440000c904000d403080c0c4405164a0921500f80e80740b08585c000c080140c1341c4000146800b00c0004d001416801c00d0084000080d000a403041d04401c907a01c2c020807950311f00006c501600c0800c410700358181f041e02d0000820f0140f09000340140ca000395000324240e82c40110b0714050350b111401140018104040314800b01e4450400d64048601c6490880c3c038041da00ca0515056482088050f0002d954444080005103072030b00c030b0720314400c82e05000141150b02d036031140f000c00c1d40c02041c00b0b401d05400180302021540e05004c1d2220800403840700304001a02e82c14014018000e40804882c00d0301180b021030054003000441000003043c0c1c03113991150b000c0003001150309030406006521304c0c580900400325982d0312008a42d010010700781c0303416220002d8000c0e00d5000c1050300002c9080c090100102001b58680c3e0208034180c039015640410030202c0010124002e1004d000f02034040c1c08048140447d0303d500580c4142e224905804403089501d80341810fa003090a0702001560 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 26202892 1250 26201642 26201647
    0xf070512040b1206010c06020c0127120f090b030703091506030503090d05070e0702150c0306090c07021c0c0f0609080d0c0201091d0123030703080c010f06030c05040c050a0203 77
    0x1e580f02c2e00420700d82c0800189030003404404540d0740c2ca01a600911078400302a511070f0903103044161250b114500000700c0300031540004c0d84988400c10786000c0e03e0b1186080140d40c600d580b00b0603000d41c86107001481e0031900540d40c3c0c030349900014000c3c91330600440380c242c035055003000c0c108800d0152005894001e00958900708000c03040001111991001f01c4035405254400501031080c072501c18452110741d0054041941a1903121321700990042c40800c10079803c0c020b000450b00c4c0c440300940c0c0095101034070b40c0c2c1c50026000043d00844040003103000944596901020001803c0e80102254901184442c1403074864000381c1d0340d07504e18010b0b50129481000b101d210940720f8031340724168034018107190400c00e490380342d100f5600d203003591000c84050190740104505420810580041000ba040101d100014203000039260b00252001600c00c907030200e241d045007002036204401d0107846050801c0007940c2e80c07914065003402c61191501c190b20349515030341100c0c0100308507905030070954051751 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 26204142 1250 26202892 26202907
    0x12010305031308160e0619080a1101020a050601030320031c0b0103020702031f090206030705030708070e010c0221250605030f011e05040c02060411010e150309010207080f070512040b 80
    0x2105c5030002441640c0c40344208048616000242003140090800c0c440600802a0541007007020103ca0a05590455204011000c0400e40215009064950503d03080b21a041c030050b4112a0044040b40c280080c00005003151241c2c4464002c898125410760051040485030380c015000c90050000c00794142c0c0102039075440072002d4081000f80d0704001480020211b280e600883ca0907081100d40c000814000801c1c0880190000781c2c2c01c0d4804400c0c941810f40002210000780f0a00b801c0c24000d00840b00803c2c2c040d0300303c80b00c184070404019503508461ba07211140596146001440049030420160480007141ca0b40c03050080b01d100d001c0300c540300101a46080003424610700f400712200c415402150012a2030781c3d603400746140202659000b0481810036080807144481c840a003d41402403000044016444030101d50000030181d0140f04d0701ca1fa10042031902920035041c000340101e8000800c9200340100201030903146006000f00d810480b02050154802d00c01e40c050161190414440070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 26205392 1250 26204142 26204159
    0x10507020d0506010e04060b0406030f080c0f01050c070c080312060d03050d1404020909010506150901140a020604031707020c060705030702190501020f1c03050c1201030503130816 79
    0x1091824400707885052030824945075281041000e8010b05200800e50041c84103100c0350740121004110708131410085180b0b1540d0704583c080c05c40300024003a0401040c03c0302d0191341445a2040361b42e07004000c2c066031a200d500c5543d0f6500c0b890f4100c844c01c54010740480c040700000141c62910303464400c0c0001c1c44d100c820802c540b4014208040341000340c100b02c01500103140d8000c0d102c0c0e100c00c0050340100340c01c192042200d1210001c0210724182c1c075140401c0980d6540400c0003e20b80801c00c2040e03994041e1200484002c46000a0641001d00001340b10340d141341e001540c04e200d14003990718070080e1040114000c4003500199005801640320703080c200c409103010300080c901648a1011203103001410740c00b10703003010355001e841c0c00c4070904c0c11010002960144605018260b00602610300344005121780c44031040c4003e01c01c41095503030307000188030302820000c4039140701945072050480d6a49203030065480d800030284201c25440d0740f00010780302c0000036604092400d81d50781d410b592810300e01136 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 26206642 1250 26205392 26205397
    0x30103022407060e1b0607030c030e0607020406030812090d05040603020d0b03010e010905010f061d04060e100c021501030f11190605040503010606090e0c0a030209060a02060906060306090c0105 85
    0x15600c01e0402c90000010a43d01c40e802c00b02c24107078050040c081c0389030481c4040540080105001d51000c002c1800040d0b07201446041c03265240c00d000b1071140312000485c43c14002d11000941003440c1210100c2030080c1480a08031805c13501d03e00b0801540c0c3c0230b01c0d2036191200c52803001d0100e501403105000c114007a801411102036071040c0042d0003207514000038252040c111512140341d40d02c0c000310060020a018156401038030180c184810341ca049140392000e8206003100208200301c0300410300700500c0c2c0d000442c0400c1135070121010701c0c1110368454024480805140c0240c820540f040e5280100710f03909038100c0f034000181100000b0f07644c43d241074464001c1c030707010f902500c41d40c141c015241404c603071000604000c5d03035129240d0707042030141070844110390403140901c080420100301800b404860740d80c0c84500038000315140c0402c01000d070080d01038144140e6000c5c501040400225900184151094800f001110f019884000905450310b9082d00c500c21a40c000c0b08800350194082e000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 26207892 1250 26206642 26206699
    0x9070501020a0b090a0c0b190e0102030702280609150801030b040212070305070602010608060a1506050c03040308030a0b030d080f061018080309010809120405150903060421020303010302 82
    0x5c2d2100c890b01c0c0c1e52800340d40c103107a40000e42d9040d00444c0b940b00307031514030313400884605990810304600784013440040d64038001d4140c001d01c10000010380d112440c201040c4414242140e0446402403038a822010701500480e0140c503640c200002c6500758101d00c01d04506040703e13005043c020041c0c0312502403001d02d03e40408991000c2c070910340c0002c00203200f006600010070311980001101410710340344904058005c0c002031041420400785064416121402100300ca015081c107a1f6107000140c601805c3d400750350300c00f504800c1d010081001408bd01c1d0801d48240d4002c8050381c00100d60200191241d80068405078000e00c54a400070702507041200b800019200141081200317440311480c561580242500408010707000403444001550300041e841d6005003e49002d855081c8581c02442003034043d51149520940c26503144600300440002211082203025043d60700b1403409080100c039052140b441994070300f00701c81540d0203807803001c02500c0c181c80c1c0c0100101c50704112405a410a031000c480c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 26209142 1250 26207892 26207911
    0x314070305040f05060708070207090504050715090b07080d05090303070c06020a0306080318040e07061d06071505070206010506090a0b0c19060c08010608011805091006081509070501020a0b 83
    0x1d90f5003010610411110344624160f07543c0344418030341844024248200350303222a030a641840c042c00001000403803418203903203042d1403d0f4807a0b000038800b164400e11660160300101000185102805002c5000742a00e4514080911030b68464040b0180c1c0c2e44021503840c8005582001c54900041490300106461007141c0f0b0080380079521005002d055901681c800b0941051980c0c1440007030406014068040400d80058980c083c40d294000d041010040407100c2d110b003010041d0741140e5600300a4410445d0854504030640c420548150014201906d06002501c0313a100001054030303102040f10702d291409030584505914190310101c0c2c0b40c1050140700850b001d0100142501e8800d40d40d120510340c01042c002c5411410005d024080c4038040e000a020488400c1c010300c501c140d940b0b41004210481c00000400341e4913480c00b0340c100780c80c1d600780820321820210300140228000401d0903007603185505071101500d400002c070342d47e0800380c070510b400342c5c004010120104e080060096404141e12 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 26210392 1250 26209142 26209163
    0x306010c020d031809020301080c0a0501081906030816030908030405010507030c170f0304030305010902030c0301140a0806010816050d050c130207021009061101060302150a030f06170d031407030504 87
    0x1c502e13641c40d110150808582c1e6640440104030401b02008a148001004e80700700302a20b06182c00203041000c010300d034198041c40903260680011666019000543d00150165122840c0c0345480c03d0701c2800c981c050b8006813a548010a8900020040301c080340d00503110b0928041d41641c059482e0101c14000360303481824030703202c030b500342407850010200000c6001ca04c598074a450314015048840c10303045810b51520501c10000079894000071203055822114803411110618030000340d04404903045100640035410000821620025845001e00741554806840580b5001403108078003d40703501829a512407014600c050070046031258280306841005440c100d96a000b240782c001e2510a00000120441d00421840da80700800a0b81c0003c040f001740300081c41c60300080c1d640d074800707142c061501c075000a40c0c04005c3d001c0d52020300b03480218001400441d5803440d040d0f240d495007804094090282c100303080c03002032180c8035101e0144c180d01c40307950642e221410110001c00d0001c004541c0c10181 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 26211642 1250 26210392 26210417
    0x7030c1b0501020913020909010e04080702100f1b020d03050a020f011406010e120c040513020405130512120126010207060501090608030f040b0a02150114150306010c020d03 76
    0x18103299203030140110700141e900d0150b00248a07450202d440000351040c41400550016591100007604541c286020b030142501c0d00d0034180410700c10358900030b601111f034992034587e02d40c002c5880d2554810319110403045040b01e01e000c00c0120954103009602403042260380c4002401040a4950f035040c0d8411142c060380c001000600311003c042c074007900f4400400c200700956a010300141c0b2401010f42d50080c407070007500395040d0345141c602d03c0b1503c03e40d03e8900003440343c50680d0001c1d40300c036001031090003142025841560380e19048401518540581c2c044514041220300c1100c103000d281142880d8180e03c0c1203041111440d00c0007100080c3c0105032512503001c0e20900191500c40c2c021240050b0329450514142d0443c0e07c10382c02000e40c4d82062122078155091a42a542255070560413250b4447d030304407040341084051046010002083c0002161540e40e083c541c0c0c000c40001d481400740e040c1404c844510034003041b00c407c0c3c0040c4240b180030b0014101141078004040c4242400c0c0b088282 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 26212892 1250 26211642 26211677
    0x120a090e090307060501050609031024090905070e0c070b0903120c0a02061803040501080a060806070f0f0c02090105060903010f02041401021902060403020603040c1503020703020c01021507030c 85
    0x401da0304405a9030010a2003400e01416204103401050111602481d1454840c046500e41c416101034089a60741c41c4484140a01c109640914070b22100104da00090744400d030301d000603c0041401e541c035206001001c1018003800038014001d01c0507801d50313030401d070f1281d55101034440b0040c0303503500c1400305220812270144c8001c412406010440340e01c0b500d03071040c150024074005004005002805000251140e12350000c4101c0e42038400a207007601107641c2d41410540a403c50b580008001d224a0007044685a0f01010652990345540e6803001e00a40c0400100d0b04a41111f0010350b003c0d511030010405403405c5030003041a6800a030000c240000c4010204040360070592100304110507490141103d5a0b0501040d0345d2400080104030000c0c09640204005000d070707002c000c1c05504000046000c6c040700c0c1082e10010f000d03d03101c0145d0300090810040103034000c000120054814903d030049a50300200c1c82c00450f80102e2418042c5541c3c81c84228003405000301c01c1c506100110340f42446424 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 26214142 1250 26212892 26212919
    0x5030105070f1106010f090b0a030807030203030103050d030e1507020a0605010f15110606060309030c031c06150c0204152c01080610120206090303071407050301060305120a09 77
    0x41e040d201c0e04418500311801403c0391488401c0e0440c5500a2001880040e0010306410700390743d0040d40c00607055030b10902003900c0c201e01c0e40002d00b06540c0415450201070340000158140c070b01c282c05039640d15030004003d5045c3c9680340c03c030512a0b00030a8001c040014031358a0980d0000741441140c0d03d840b074030b03100c0b20102c030001e0f041014030040040c401c0c0801c00000e0b03505000310002d4981485070715a505041601d5500c0a0116407269000001140d2030b65803c00c2a500b5a0031000281c0e643e40500c2c0c86001d225181c01c01c10031031910304210001429180d26102030391002943d440d60703a8281e4003035003040f008007021302c82e80740d1785240182c0c0401c1500e08803120310120b040b40c51504641c810300c8400030303600c150144d10580640d03001c9810080c9501e403c01d416400c031101600e200f040d42e0401d04c005465070081342d04442e050b2101003000d80c1480300d16421440301624200a80d00d02c1d5441c0c038281401d84007540009861360744100c9810a0340300301c81d0004c14400840d8905081142d84455841000c00d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 26215392 1250 26214142 26214151
    0x5250e010507081b07080705190302040c09050a06080108010510060e012f0102030906060a0602120c030d0203090a020f010f05040303080c0c030301060c05060f04110904060b0604090212010806010f05120705030105 93
    0xe074020385d01848030b05400c0005402a010032034a00000b1801001000d20604141c08000c0c00344ea201c424102a841c0a014044080d10009202c8440309480c1d00f4024540d450920540d000c541c2000040341d2641030111256054030107a5941c0350080c03000d24015101080401e001e10f0320310000011031704001c2c5582100c1d02c4c080b0000320000d0396030308106200526000c0302800440c4615174007101044000d400041245c0940740380034030191548107440e070142c154041e070203d0400080c000001c002103010f020407603e18603882280c4084420070910011074605151004075404500208401e1011a00910607180d0001d04450580c0c0740c0855501001e056070400c0c0e1004001c60240c0064604001081c041640d0203400034566981c54038141e00c86404120040c841c141c01180e0b000045024007030143c0105034038941c083e241685c1c82d540c9140c1b140080d84080030340c4149550400000c03030540b002054140c106e490080d03219030502d081c50b04205005908440501d007521030b00e0400a2151400c0c0038482c400c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 26216642 1250 26215392 26215447
    0x21020a0207030501050c03010b070b041e06060302030f0d12020705070810090201091e030b180105010303091a03010f0b0c0f06010306020904050606091e0d0b090105250e01050708 78
    0xc1d42c0c5189085802d540c006018205132003000d000600080f0201410b0320130203030300640c0284164699081c011040d444041c2148400b14007200c90009211180d080f14044074803d400b03d800c0000b2014000344c07204034201195001a000401030020500260040e020181c003480503510300c2039070360020b13902d0060a1106829110f454506800039507030401804001040e0400c000185074010541c40403c62040e270000511000d60280843c4008100e160911181d0382c0c281e0003005156124180030b0009031080c411400c0e01d01d03032100342882041000040c1c0f4101e901a00c901b86005062075542042d0b5045000311b2021803152001e4a84a920104080c0c0c0c000e42c00f41800690303a0181d5070602094a45c002c2599004540030071061030381d80c45e06500c3c13003402c240150028910144000016a54070160500074200030b041e178003885584801036015038042c241690319503031196080162140308501080000c00811143c101d080103550154008249140c46204410703d0240c000760b00305104c0b1000c03d00c5115 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 26217892 1250 26216642 26216653
    0x705070e070c08030402060a03060305030304030804060b0102010204030203060c0a03091a090706051207030e030405100806030708071d0907050402030a020901080108011104090e0f0303070c050d050906040621020a02 94
    0x55010034203401d0704092140703050b90306501c4944585181340b00c0900f000703000300030000b403056005200c0e62100c8040c55014007525607905190038003d25050060710706031070541c0b918140b00c1c2150700500c200c0b4200d80c1d024020780b110740d071103003490714054104840c00024035450300004400a83c290050818045211100341c00134200481140e02d4011250080740c00d010301001055001c02d2110500b5912058900d004a0002502e420650440c0550361106400022044000e00c02a8101600a20402040d0116503503160f541000d141d68105911a01801c1080f40340c0d685c035400d048508040d0b04c5540b500441381d440e0750311070104041340e00455907030400c1a80030a00e9585513911841e40c0d070040540800034460340e00030768202c4145206a01c68419142c0e034503203103150540380c2845038080c04090903003541d07100e11709070b04042c084441d41c5004844a018900540ea0f600e8000c00568203101d402078071640c209800c102061b101c8034600040d0103407441e2800c1e111021103085000401410034a81c0c003519 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 26219142 1250 26217892 26217899
    0x14040509160f0f0911090904030e040f0902190605030105150403020904080301080f07080d050d060504020409140a0204030809060d0e1c1b020d120512041b140108010302090912070507 80
    0xf0320000140e04000303038503820709003030b8401442d01c00141d0b800100100c0b1003000383d40f15450700ba03d001c4480400650007a09200c18949141003070390041d01003900a40b408a40044508100c1e1200351550280e940450300900040c4a10300745070140780308542c40c000001d0302d41500c9800194680e00220350851380d00e01d0010040c402d0782c0b0180103000360071285000602c4182d0a000c0d046c1d0321055940f4101d0708001010a1510300e101c2d20f9005040100300140045581e59100c0e1010005808903051f0b41d41c00380c060f000840d51042181c805c940c1200e0304421442e007408089001c0140d61b40c400e49140b51290303100c2d01c0840e40c03401d040c0b003d070300700000103600d1080e00d600184c4003400803001d10303c000c404030710f5884025002d40c9640780810741c06503024203011100c1d0038191040d00d060042042171038401c0105800c101c10044080342003407400d030b610401c038172103181c5d42e0a000d1040450310000342c1c0060306003001000142040f50682e50000015019541c0ba80c180169282d03142c0c002000c192001e9100c1c0d074040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 26220392 1250 26219142 26219159
    0x1b060608010501150c020a15120509060a0e031303080304170d0905060105030c0105161406010617010e13060c02031603030911010c081b0304050a1401020705010914040509160f 77
    0x504046804d41041c40e04c245981d00091610380e0f1a01c00e4401c1c41c9007200d110303c01c10b44625803062992032904420840750078a01c00c255036840c4110b9840f000386141148101c0c0000c0c0001c243c44000003002ca002d48828259503030600183c0001c2d004503034000c4c0400402480c1422140075210300340c0d01440001d200e1206051039440d015040c5e100c18001e402040b40803107070b6603001044070303040080907120041e100024900905c86042d8464503001074000c10002140c4580d0145172405c070318076030701c1441c0284c1c1d80b54100030035400300650f495591404480000310000d41240c2189602195030f005036820030f061441185a052603000040740002eaa03044507200300f00418a600007031610078a40030711540070551740c5485510806400d02042611014402c0700400c00301300300c1e400b9141c043d20311109035994a908440070162000140d0141c0070341140440e140d440f900a0000300c0301c02580b42c0001540241c1030000424000c0d1040c0810b016080e001c40038445080c45880040c040821116021441c16024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 26221642 1250 26220392 26220419
    0x803030a0b040218040b030f01060605031e070e0f0102121c05010f080a0b1003050a080304031106060102030f0a05040911070c0909050303070f0c05060906010501180e0103031b060608010501 83
    0x1c9510951051000030700104000d0903c00442c2030550b40001d03100b0303001001a00e49032a8415101042d803c114010424650100195000b01100d814000600d102900c0b03035282c81d07500301c4060b000101e540c0302050f101e00e0809041205400180107480c0600c02c010a048015444281d0240c1504800043c90011b2942c0c0d00c0ba0900510030f20080050389401e0034129500c075079480c00e002d0085040840401c0040703120012003c0259400700443c4d80c2c515003882c2003030403600119416008a030301d064508080c0741e00821742c0d51051300140e024503d00564119001c0385604086d80e040c003041000d12021600a0162103102c102e64145000951100a00d1a10000c1d0101d1a00300107116400d101340200000c7e0000180c1c0c0d002403035400c12203984901044103c42c41409800098038500c112003d10510380720201e4141d06035403080e070712450380000c2842d444103103010368428010392091030001040442d00c515500760714031148600f040c0c6401c03002e440f03900c00e031000f0f504460070356595280100111040c0010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 26222892 1250 26221642 26221661
    0x1d0708070e1003020f03031204050c090f16050d2712090e0c0f0c1014070c0309030803060609120c04060501030614010e03011b02060609060103050405030301090c0504030803010803030a 81
    0x8980300303640341c0050708109041240c44000d020f1785540e03a400e441a0b41c03d0080e210384c040c0360031040d03071203141c05c2c02c00642d10220781d6410782c02407a030800440c2e000006291000d1242418401050b4901541c0d8800c50b4260f22819000280503a80c43c12540100c001e04241403607103d100c0c0080b0306821090400c1c0e01302c20041d01041060090ba06010009900150b10813617011648d00c000544803080b103441c2100a00c200c1400d0083da002d45400040500c060b03621070079101481540d00c0001c2d07035034104251502040010007401244003110704000040e5900000e650042d0702400590420701400003040140c41080c40344003c0d42c01401c1e940400341040d11645000f00002d2905000c09885d089070100d800426555a40c100b003500711881d802600e09420201d0000304040d40b0720200380d01828000c1d00c65100f40d4000c0e00c01c2c1c4800001c517032258401d02506005a80010203549941d203000c0b0b00200030503a0080c080d080c004280400404116102c0203180280494006150740303141240089080740c881c0d81 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 26224142 1250 26222892 26222909
    0x50a140106060807120209060a0815040b0315130b040f1104060f0303080601020c1c0b060411030112030c02030307060501051c11010516051b1305010305120d1d070807 73
    0x81040007041e40c4030b0f0752076030002c2ea6800c0615034074005e40c0a0002901c03070341d007509402c1200001e24010065003c1001d922403080881c0080c0d05502c8541044295510101620340c0b691242c15644010261081c9481e00310b40110038150301c0c28030716034520111400846040c2d40c0a11032070003440a000d801c40c018480104200d0b81001141e003000c07044404064030b400b0160400140794005907880e402006041201ca40090004003c1001030039800c3e01240c9618046440b05070201c0410101d0405008003075000d11035590b1242180c1c2081050112a0400384050342042409484000543c03000d10080003e61702401e00814698103100134451130750705811001054071045440d08011807031040902d014032000f460f219a407941c1103000c10040c42002030002e4114061203210030910f070039400881d01115800d4442d01c046041aa4040c01152000d00c0003030b0964200c02808080009850014268040c0318840000c640032128003010440820428010031766100305d0050085c00d408100000080c04072a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 26225392 1250 26224142 26224151
    0x20c06070f02060109020d0e16050f090408030c0309071205030a1106040f150605060408010509120f0d020904090501090b010501090803070c0b03040503040e090304060e0d02030d080402010207080a050a1401 90
    0x904000303640d00c90510505035003a1b4045220100032901d40c01c0110102c420500325180320020740392030610301005100e1240308800400300d002050a001d44441d2103a40c115901c5030a42e42c401c4414031056000414281007030150702404180c2e04051040603440e0790140300159160205188050014003124181d1445a0701500c1088002001784c0d9140010540c88402000c0c80515614480003804991b04010741c0310b80040360200c0c030000158410383c0708030702c19001c89541d2442800f44100501c6541e59499406904011a4070b00046c0c030380040444910203400000d003009161101421146030316812141c2c20318a0004125940e88240c1d1a809000ca0788091840e0020703d0341d0b101c140b03000b107200b45030364080302200042c1030010a009440c000d00700148415664130740440100d490303620500894010807040030b040b401c0c0341004240f16111b503a01400508a02200a030103859020005208a0440c0700346440403071040b0341031000215840c4180c7c002c01300c52a0300d19015554a800c14000d03009680740 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 26226642 1250 26225392 26225417
    0x11e0203061309120f0e03100e060c0705070b03040512070501090317070903031b02040207030f0201060f0f0506031008010f09020315060a120602070b010611010e01110301050f0301061503020c0607 86
    0x51004154064680d0304001c90717111032800c02a03446110143c440f641c14004d0030340d41c03410910503401c9543c80042e00010349159540784042c0c0003540c0601c0802415039070010f0000d00080034010000d540060052040f61002c800422421803503074080d103412210340c0d450700508001c060b0080248440e424000e110344100345004e08005000840034800513040007517409485d0008040b07090310b48012500580250f41d28036050030003810084403011640e00661802c0e82c0094101c1d074840450066905020b40c1640e5107181c08108615030f00007a0a0b100418894000043c0c10a400d101b45d90608640b03010208030100207004041c240841d001c800c4281c200f410b01003092540e2442040d105480800d00d190318000081d0a15800a010f40c140c01001050180d001003070040e04140f10001202009000340280400c3c1400c50b42030b652400c1c42c04500703007000e00c0180814500f1040d090902407001e000010101d90354052900c00e0308104482002103580001e1101c01c11005110701035000d4402d09012611411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 26227892 1250 26226642 26226653
    0x90604060f1d1302071401090809010f020313060f03020d0608071a09130513050307060914030c060c09030a0605011805060a06021005040f020d0506090f0f03160302011e0203061309 79
    0x2e0001c3c401d0101c541c0058050108a50100d0f00c50302400e01c0002040020414501800203a100c03071700280c0810340301220304c4c80a92000048612203245c00000c43c105500d480e00070307103200300e882c0e0004051503001d1040c203422846034411500101806001004128030b0041926011200d25050101c0602c08010f290348035150090f0442c44bc0c00c100e000010f081d514075404181170023079008010454040001c18900f44803041c0c0001021b64000c0c0c50a40d03500711071031302c1a03070f8134424401e000040390000b42c0040d41c00c40c007020242442c1040030f000d484551015070340d02c5003119026049507107900403d0820f1000b4039032a01c121640030340b06540c1407070300c2410107a01a590300d0b50022002c0b03c040c1c40e04000790402480740207505030700c0c0c0c1c0a0402c0c0c50070440c2d4542940c80354400c990781481031250303414407a410900012000e41d1510604007444c50441066404042a50081401d40540d0748588079078000391143c051f140d20b035a1a00c0780040e22070030a00c003084900c21607421600c068038100b40c0768001159 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 26229142 1250 26227892 26227909
    0x10e0112080f030709031a010302030601150807210204060210110c030f0a05090402070b090f0c0114070c0b040b0d0f06051324080307020406050405010605030f040602090604060f1d 79
    0x400c0d80411910f03540e450303d00712924000c60300000c1024160f0703176800c070000200e086842e058074400c0f01039600aa03258a000b4100d002551940c00001d281000031905844c0601032000c90008901e115000c000100c60060007640d1169200d400103a0010341c003205604140d11509404100307501e205464103000f509126030300e0094018110380c1c00e000040c038091503070040045950000001c3e206540320b400600b00b911b142c80d403c4940100e24001d00c540c24103c1c102c00302c2e0704804010142c5405520301008002d00942d900011000c0b18410703140c030710201754020703410080c0005101030104103581e845107481507419203014510010800e4240b01c0184042c2e40c40c040170000f0320702001e1000030784c800e0000851011600e92101d041038048098404a1100f001100804200f0300030303982800019a0b400c10301040300c40921402000031024000b0400822010a450350014006c81001d800c250650000039101e901c04e500400c0030500c540d100c1e5840a400180d805100540d148080780501c0c51131000c40d4011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 26230392 1250 26229142 26229157
    0x1b030c0d022103040b090a050a290405191505040501050603070e15040207030219031d0a0302060a0e0a0911030a05180709020912012306030d020c010305040218070305010e011208 78
    0x15a0860000300c4286c030030007540c511a40c100c0e00f1541c2400d07030750500500d010405070b034003050890f9030a0702d000042c460000c911700440d8441c0040800048510502030380619048080340c01d03518a81020509000500a29000c0ca0082000040301d0625604061502d400e80e840035132244505010812504543d14030345c8510002603d000d030350b40e8040c1c50304a003400d1100008041a080025208080c1a844410040210b18910001500500c448200904280b00388002544140c00700007001e000c0d44200d103813408500000e0b10021111f615110000b080c2d800b0030100741e092031790110802c504089180a400d03088201441600700242c82d850a030340d200c40003030007001c1c1181c0d000030b01d80ca0240c0f20b003040314603484030240c001c00ca6440b198000c61050108010102d00c040480c6c40815010715011a00043d0300b5015001000c4010b40300e40154003804004009aa20001200c9480c00307418030420741c14800c071210394002a4030740c1031026602c000744040c1c0040b4005420320030307003c00242d100011104030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 26231642 1250 26230392 26230403
    0x5060106080705070812060a0603060e040f0f0203030414010e010306030f0f03110111040f060219030e1503070302030a060f081e010204080f030409060603050601050f1b030c0d02210304 81
    0x2595003801c141d44921134441d00500c403400014504896482a4458500480080ba20311000d1390346c90b1801c4050754044e0041c803000f54401d101080c009070814250ac040180300343c03905501001c1d6038001900319001540080d013101120f441002e03840d03030f1000060340d0039402403c0401409045031a10744046481c950001d0200701001e80d1213081c507005070f46441d810a01100280070b030096196104101e50450300c10744100701c40800003c1161800890715803251103902c1e8285520352207507141102e0400740c1d5814950001c0f91291208003081d59072000754071500341c41d200560f80307082c1050484201d414661000200c0f20101c4002c1c80342280c017041110b06100c03585402902c006101c030459009110340d078480d9a1174420a0240300c10080080054000c0360020b0300104042c654401c0181c080ea00300b110708600140c020000b0301d80303250700c11010300b014101c0f100030040541940c0342c0940c03841d84103692019107644018641d8141c0c903410080201417180f00c0351080d4103148001c070040640d00015200424 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 26232892 1250 26231642 26231657
    0x70201030905150901060302092505030703090605100501120e030904090201030204120b0405070b0406020303060103021c06030b160c080703080916030f03090e100504050c040f1e1205060106 83
    0x70b110082114a03c440803901c0c03140c0b00c40c2402c120700c5008007a2480100d0040c25200001003003142a5201c2400c032a842d640400612407106500312050b40c4000c0c0203909040d03451301c82c0404591a48141c2d84500104d8102d40c0c040381c01e0000140921850a04100c12070f420040d08104a803004000c2e1410a0300035500440d40d0903c920041e0081c0c01113402c1140c0c083c1d0b41907a0401072000380030446015070700803410b4030792140d200c00c00c9403c9486039001d1030700542d0041021032099403081e4020440c8400840b2603a0007a0081c107200f1055504542c02910020040030601c124008204690030030402c0a05111201045698540d482400303a644080c1c10302803207800244142c802400a00201081180c060300301540305d240c03100c00d0002c1d40406500143c0fa0301004181101c001d1300140c020b0440c01060000c0f207140c0f42c20070000e000018010346841e102404000f0701130084c041104090721004c541105c4d808940c500210803c1d440b0380c40656108004920800070480c003180310360642c8d03c00c0c50b040700c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 26234142 1250 26232892 26232911
    0x130b03060409020303070609030f021626030d0903120204060903020409080c07080604030801061d040507020c150408010f0b0109030809011b060b0a06020319031a0d0b07170c07020103 80
    0x140104070b82c04020750103010001d2017504114840e408a46241d10030380b0707450050f0900d040d0407641c6400c561021482e210303140b44240b264034081d103c910a00314400303000e00100a18581014119080a605075140c140c03140403070410076800c0321034422120042e1108500341890320350010515001c900c00640141e0352440c0340c7d070034444004111060100301c3e10840320742c66620302c6156501c01040b103040c0c2c0014010400800c980344284054001a59081840100420b90008001c02403101510b41d0081d4841e90500504a4032640000c0c5d00c2003020302c0e2056140d80c50050304d5401c0d00e401d00d402c000e180d0b1400c0907008141c0c0c1c10417006001c0d82c0d002800b4648030322481c00140d0703041d05030302503040002c117186155804100042d0405258020b0a0700c140d00c2c07181e6100e00c1a81d41e8050705486202d2170780054076007005540701c2e0340301882d00f0046004031580c0c0507013000884d1045508400985065510000300000160084d5000d84800090b507100d011500d0007110601a90041c200020704150b02c510000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 26235392 1250 26234142 26234149
    0x712020310030203070b0406030e060f0606030a0608010501080f06090d0c080703020a0c030804051002010c020d0c020d0206210106020601032001021e06010501030b060f0a0305060d0503042603130b0306 88
    0x4001e50383c0a011100c000f030319441c036441503402a00c607031000a814503080c2c0400700700220701d1394092924400c1000032038842c0f6040184a400c01000140060303076402c1c001407503040034081c1034000d003440b00c060980301c9040382e0070504000d0700a103000d0040d44481d5040300a55440f114482950b41c1001196031900c1c4179140807414800000c40141c52031422103004030074068080300400c11a001121303e81c5d20602d820340c05900766000954000b000d03802c914400320840d80146004441c3c24070052014280024981c0060b00942101d20b102041e81c290004440001c140c04030594050440ca00040410b50f24654615a20340008043c04143d049a4076409825034020028a00c00748410007004030120400c0d601d40d555620244038850009051048058860901000720b0f01b0414440c8111441c0044540c400d5004e010081d14403a0041161a88000418000d0000d0710203031031a80d00490344071513159049205490041107140040d00208030121920020b00b003100101e9181c5c40c0c2c020f450382da440000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 26236642 1250 26235392 26235421
    0x7050603190509010516030b01020607080a06050d061a0109030c051003020d0e0a03020601050a030819050c12040e010506040b0711060409060b090312070209150411210601030507120203 81
    0x141c0941800c1038140315000e00103400143c402c8075201600c03030b042c10440b43c084007510741c458256030143e0081c0000c40c1145219144a41e03104200d08008a081d40e60380000c00c0e003160000c0c0d415176910b5034810020900c07243d0f42582c80489142460001c01090458449800400f030a01c12035101c0c441c261080c0128a0080c0c042e140540302001b000c0000350b20496003151170303a507000004c400500401c1c2c0041000d00e0900101c4056a801c061201d0900e0b00c40f80c0b040051550700764010b0306210b0b0500100700f605004114041c03200c2d00c581c00f0380d40c072246800824941a501038115904c0740c00240000e21500044000383c1d084690080c01106001c401c0902060307440c422900100c160074201034022841c075540c8002045034000503012609450b030b140b22000082e000d11034000b54400d0019011440c5040d10103c5c41e040070b8802040001c1101c0710b2205910f940d0701c1807484400020814250244514186007070552008081c2020b20ac140743c00e502c010000004c20b8408070355641d0200c086005490b00e4030f103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 26237892 1250 26236642 26236681
    0xa1d03150114012a050d030c050f07020607080313050c0409020607020402030402010c050d050c07050306281e050106030b010c030f0c08090909060f0c0910140904060303050307031d07050603 83
    0x20044c4403c1c030801d0031109400e500101a192885280e6024070158860b200740341c2e1500c2d01d0b54689042810808a07640281c0c003940c0141d922900034411800403c0c01074004500078120ba840424007000380c0c0c500181040910302416115038a0441c454026171502c00442d035140340d0443d001aa0796841d84010b80710341c4c00b003000c060301030710950710b01d41e00083d0400014240602c03508100c0307608580d102d04150342d440d01241c20031114501159404194001040d03840c0c07050300c42d9440442c1c0f01d00750f007407064030340c101c203100e0000c0498651004101d10b980520400500070300038601980c411415440107422403034a074150380104014145500c05000d01d000680b2803132031000b09200710300e041c124020780d83c0b214241c0d00e20070344201c0d40700400c000202410881d5110340700903101494144038620291a440600500b80f901030404008000240c0d80314441c41004d1882a11140e440341403c0d1002001c4a8061207062007840003000148850100090760004840044031226541d035100010010403010000b03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 26239142 1250 26237892 26237927
    0x1050904141f020a03060801180b07091211010e03010207031707030204030203010212040c120f111203070b0a0c0509060405060706021c060602060f0403050a030506040605060a1d0315011401 83
    0x10540c4814000d40042840d01303e1a602401402e4940c0744850880310304120044034400d01040300c20005500074440d6501c412581030141c919642e81005070540c5035916000c0f10101c800c0059002e5a42e00318081040542058001714102130060b80c000d450a02e07480c40c45c0210105a8000070000c900c0f80d0100c03005198054005e40d103890082c3c00d1400c0071002610210b6a80425030300200f0141c600c016511402508043c0503c1d00b40019220034906c0c050502c0d10541051401c252001144020401000d01c548030f40034044a034503011000d00211030340d01901d142003003010020010159110000d590589008407042c0d40d84083c185007440091207290307a80e03107414484540c9a811103402e035010744201d0b501d9800380c0e40c103a07403018140390390002c0c01c6400030f0202c0e00c03d01182c40001d109030310142d8021005000042c0c1c140d142c0001502c0794202018000c005421404240d144000500c500140c000040d4000d241d0b078445081c509449900500404052035210005c1c001140e00c00c046d1040220380c0305 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 26240392 1250 26239142 26239183
    0x1305010b06040b030a05090a030f05070219030b0f060603060d02011103090406030506010608060f090103060b0a080f1f18020108220f0b0f04030207060f17010608061201050105090414 80
    0x1014886561340040340c5800f22240307401d00091f5100070116580c40020303030654500161001c1000142e40c40c0d040302400740e0f0011080164070b00364009010381200070714014541003285291278513070f02c1c1516100402c410b00842c0240184811a00c4100e1424034090b424207000450310141c0712040d2a41c0107081400380d105043c2480002840b9003c9031030340c1a203170306540740c0c85541d0303844041c0308224450601090b00310400000400101d5202d5014488000001f042c00742810381d200b10041c41c0031250000a200d43d000903041002540f22440c84001007102101d0a01c049612021441d5039210141406070500405100284070718a2010420070065881584141071034030b1400c142d41d42c0010004101c540c0503c0002290a100240d002c20348960b5155000340f43c0f05013010411031340145044c03402c0d0280807002c416840444400f03005d140c0139104540d145411850701c2c0d02002550240040b900e1410307450f1400600c80c1c1e498600d0513a40c06070b00301c80c2043d50a182014161f24042c42c0b101009002c0549 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 26241642 1250 26240392 26240399
    0x91e1e01060f1707050a020d020606090a05070210090606050f01080f010306050c04030c0f03060c03020903100c0c02060d0e06130309060302091201050a050a050105181914040c06091d1305010b0604 86
    0x3014103c48a80c0d031f030848040300072075034060b80e940340281d030425804460752000236802422500210390001940c810340340d0b0314840f941080240c3c1d00d02103045988586644042c84182080a0b034070b003103d80c09181c10f45481c180316208120b1603c060001400e003945440001f148503d000c1c013110011640102d200c0051560740840c5002c06825000c00c880341c504002c41d44031030380e01c030b402541c0740c04030000c02601c00c010206038a10010032845a8010602070201c98100c00360341c03803034042c103496003200d007001c5020004040c8103410410014440c4080b00000054000401e501a44040c2034500c04c0c100182e586001000242118a052260070225820711003004150b82160300f015004040080381802147d880304208041ca10303da01d80c54200091480008032181035464120070805400e11000030400e84018611780d206808540645418201c524100b000a6100e1a044010010081000c4420010112003105554041c2440009120012003101800303020f50162100080007040305136107595 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 26242892 1250 26241642 26241647
    0xb0f0c0c090403021c0f1e02100e030315010804081227010b030c0a061b0c0e070c050c0604050d02060a090e0a150801060501020d110a02091e1e01060f1707 68
    0x10341741c030080d03196002d6141920740d190043c2e248a40c4518a5100c4002c641780d00d03e00b0700c0300000520240d0046210b01c1802040000451040d80c05101401c4040c40c1d40c1d141032018403100d45281241c05041200c104200070100d034444d001d403625481015002e68558aa412030750380e82c403005018004179440300f142c0000c12900d05501604007000150291000c603d52030b001c1101d481c14070b10412001c941212181031801180c8400407080368032070107295000c55120825961100c1c400c40e10318001c035994509020030b0080030403082400500880d42c1d185802e0410b00810041e1000500090103010b001c103900e0140c50243c40468050680c0d590303040010302d0840800720180051a801040d40509824003044840060044409596040e002018440107041d0200c1d010046c4921070060303400b51190290040e0b5801d113246000c0d94050070340f68015a0074001d800c00c00d01c8082c20b441207584c02050902c400b01c0f400042c142c11660542840e08030360300d525205a8031420b111069103ca150b0110400082c640c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 26244142 1250 26242892 26242903
    0xf150301050a0e0f0a03050a0f02030c191505090a0201030b0f04050703061802031e0c0f030c0901140903070e0a0905120c151012021f0c0506100b0f0c0c09040302 71
    0x5038004200c0303a03100d216220880d05c404007144041c0c0010820401103002c20301442d045150710030030340b0403640340c001d44051090401d182d40c19022040454101075074180908400030319003801c500303482000303142056a8181e0380d4041c2503400a0502d51101d581002036a90000306611025018209100300d203481c0000400900190042c240210700d070750328800c8040418401e4030312411401e241c403e00344440031065900e901000b0800b003a524400c2094041d0390302c004010b54090781c001c801d0181c9034904440098028000c2d101c0e00e40e01c0e20400e2107810500d950000e054400c944a003004690719407036030003228010b40440c04000c2c00030b11460310f214001703208803001488510a404140c8540c500894544420a141591001c16000180724244510143c0404d020f0700b0500c02400741c6500c080030119031503a01d800c1d0001c0008103482e5550501400014820150300bc059503002d0001942410042c100900800f001c41102c04c0012400100035a401c1061759205031005003005e000e494a89402075940 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 26245392 1250 26244142 26244161
    0x1805040b010309061d010606030b010215060d02031006060801060c0b0406050c16080c240118060f090504060f050c120a060e250219060c03110c01020a0206010807030201080f150301050a 81
    0x540c60841f000071403d1007031040558100050f4040c2c042c4240c13545440f03038005400352035580d20004c141c00d03003001643d04222001800340080303404102c0724a00200540680c50582c08681403000b001c0f0300500042d422048103910941c042000078494884242031b48080c0520940058091120090342080c045404082c280300c04440701116181a80703190305506058030503ca103034508110000502c0340107489058505800c4030440005626592641080088a01c56101c4516aa980c0007440140111401034003803c0b0001c21060005040100c2000d40b60721842c105c1030548030401010030b800d4511070304008000c1221003004449400c0c640343e40055035068840038107600302c003060420000340c00411b0a00c0c080c441940c5030a0610b10a86603440581ba020b51114205543c3c0c052504400a03080044c0c5901c2d13200700300041c2c55005480c000303807604034181c0040d402d0b540f000104000507030780a01c990380e0122407406502810784079004090b20383e00a0f8540c0320b034503500382420481c03144680d07030200820303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 26246642 1250 26245392 26245451
    0x705100c02041d0c060f0c07060807170f0112060b040501090c2007030f03050702030609031306110d050a0908060408030406050c0c0a02010f0c0b010b03040b01061805040b01030906 79
    0x10440364020350303440043e50a1100140d0008000700b040c41c44c0860203080c0348401004500e00c0d0519038102142004450b4105170b02140007001400341840c1e025070284c040340a00151f402041c103160004e85140c620500c240707410b0750803a0b01154100401504039054810001d00107010710f5840308603101c00f80c0302500710140001c0d034420314800340314520070f012111740c0c03c0007025003106070540d2101c42044084103001e8040c40420410000123890030098a8840c08011001c1d5072524400308140480c00318650003072041014520401c480d442e408120f8001e2468503042041d5601c1c0c0440c4255400a516480f00c2128015030003000140000c0400071481984902801c100c0c0343d56103801c601e00c50050143c80d070300c9540903a00001c010f5000e40c404400c0008541001c282e0f01c8055074030200701c64001d80181d0f200d2000402070000300000560518058a080d00b4641a4240001d13580d040d6156244181441640c0301e8101c81c1041c1d001c1c0c1e01c140f082e160800800d1000c0e0900300ca0f07648401060a070000c01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 26247892 1250 26246642 26246651
    0xf040b0123190903030807030504170a11010b1008060f030a0c0b0d1b020a020904141b130b090a02130b041706070f12020904020d05090d080601020d080f090705100c0204 74
    0x181c192064000f501500d03890745074408240c5030740c0300072030050500030300495003044d1800401826100030006010801100c0c1d88107031016200c00707411825125149951400345001c24580780d00300381c000c400a076224405a0700003a002c9150400203150030403503507016001e480c030260041480d614681c001c00c6484111a0140726004441c0d0303200461700d40d4039403030b1700040c2c00041032a001881c050360503540150181c0c000c91200c0b208401c2040c140303107007003203288008006404070014504011281c00f42c0c805001e1001c010b4500e03420041150030400805e11840c865000460b801c4514460342c2c2c0c0406440d540300714940381ca0f00c032040303810300c01b203141400d001a109400000c0c001c103108180d840d50540056554664202d0344901003406034111003074a40d030040d02401310701d8001409104091041d20f03408020207000c1c240440c0580001e0025003801e04540142a80094460300441a15001440001a000d039a510210120306014850300074650180f041243d0380117007030788010007981a070300840f010070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 26249142 1250 26247892 26247937
    0xb0f04090f17070b071d030601080d080108010c021e03190e01021b0307150e0303030a0b0a0603020909162d090909021c29070801080c0f040b0123 64
    0x780c0e0003511001480d59003041d0008100611580f0304d02d01c0760018011b0381001c004080c00283c2451030903002603229912040d030154140e40d22099082c01803034114020031000184680081d1545881c401e0400340e862888800d00d85144200301703e031407030fa601d56014401d040c400703c002007202a1103513441d0b00501c501c00c2e0741556614284007049400500400400c61186880032810303a5030140b4440b001404403a030b010740f0640e1000e100861040441d024005086204c41081003c4280641c001200f003501c1801603100a85642c0c8402d0341050059200c440141c0c030b6090700320707407000340018a404d440d0b902001b1041c1d0103c091022a20980030b6444d0001550b0315460750b0000c0300c04000e0081d40c00107040720b501d0300040320700301300340041030003210031031483c280c2e03041200d1000413411a041a080c180900300200740f43c0c0400218090b007202030180480011034400100341c0d032042d0310584c2c4101c3d03481052074042da0044468a0340c58040d03428000303070001c01c0850401c5c21707042401c40241781a440c1100da07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 26250392 1250 26249142 26249183
    0x15020105150f040f060e090d05040b0307080a02040504021216030c02070b0a09151713110405250518090106020303010905070e0a0308030a1d0c01030b0f04090f 70
    0x1d10807000c4003008801161003400304038400c02c1c80a40703260019a9940c07091584082c40c044c0c20041c0c140000e2030500b41c184007018a25080100e0301e180c00f0040148002d000b0911284100c070340081d40c0d40f0708003515403580e204440003841698030083c3c0c00b5100194810419800c6041d0610504820480394080307980c0315011360a90b04e8101846006804c1103809105003822240a80b18040480c5442a10345848848045d0f408009502c2840400c0d40d848140c56814030190b00d856104c0001852076202942c02d40e10714040020a5005074807894a07040003d8407140341903c00580e984d83c40d654400c0803a2841c0c2c026103c0d1344203c0010b2108502560001214180340c10124109c0729558011461a071a04c100b600c02840f0240c02101000380c0039031108005c2d82c1348a03050340554021190301c1e40c2e03030600740c1500d41101c0d81c1c1c00e400c101501203030b07104000d03500d80411105d076156028200411454107020004201414000c00140d11500d41100070781846100404800d0315403144d85110117010144031038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 26251642 1250 26250392 26250401
    0x30c060509010203010807090e010b0904150e0316020103020706090210051e0403020906010c11060a030e0c03010c0e01030209060904060906051201090503030112110a170712020a0506030705070609050601150201 92
    0xc00fa05640401f0040050f1112a48410850000e6100001712820944000340b40180144c6040e02d0103c1d2001030340b03103809694490003461000440c029450a91005ca031003c0607004150081d040c07550224135642440707925000782621a90040c1844180540306201030300503003150103620860030640f028403000d5507201044600392500101000e1284c2d48038001101c00001c1450308580b41c4880140900050300c990001d001030300310f580c40c003007001340301d200c42540382c14003004850740720340e051200e80501a030f04110300c242e10365421719015a50780428000704e14103110320520302d0342051600b00700068041300c43d803204081c3c070002c8803400807400b501950310303003629a07040000c1d02c80e4008000412800014288580303d003407084e0520440e501e6000e00060030004d0540c00300c01103404142b00030f80048018807e0b64050aa12840101c00740756540118580c81414014140121000030100307120314010000d44122583c007240c10b0000c5445440d000352114000c1c403c44643e020a0250f568025006004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 26252892 1250 26251642 26251649
    0xe072003071112030c0606040c0305060108041506180608062d13020d0c06090518150103020403050d0c03030b01030612030807200a050c060c030307030207150504030c06050901020301 80
    0x1036041c05100d488504400c070b5441c2c403142d84105243c03030b101440141407004d03100e074146940140c002442e240301400242d8516a040c0420945020304100f101c0c1c1c0c005007419001604040104803005034001c58a00400c40e40d04080c1602c1003000c02000d41c1c414542144054905503026251540c49015001a5411904481002e00104415051480203011541c8c9500c0041c00769000c02144445c0c012a402c071041c0c0909803500c40d04008107005c40c54001e24800002d01c42036680280c08125414031100c00345001d818802580400304010100d68070980540d0099070300042a1400340c6c4a12001401900311940101c000c281001c610b499a03601900c40e6000700c58101150040810407a6000c540398400181580c0c1405210740a50b080b02c2c0348481c40510fa411010010f09901c0f096040840c5040301230380c4441d100d0081000440b410590201c00c1d01d4000708a4240580c0321035080ca051a0210040e105c0ba2504030315000801c020305901036022400240034450400c04c6031203140d0090700343c0c4000d01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 26254142 1250 26252892 26252957
    0x10c020705011d030a060603060e1606020c060d0b030d020601090c0c030507030810091b030f02090f120a06020f0a030e070f0b0a031803030506100c0c06050f0c070e07 73
    0x80108150083c101e40103c1d00001801e96452850964443c41115001d0700286c038103da4414408456000812486510001c903090340f20100d4607001d4000d5035240b442c004640501c0d00401d001e1140e100d0750b0408556903000800382c1e051240d948000039581c0c0300074451000301d2800c180714070001a00486083c00b6040d05031313694624103c04c9803000d86482d44040c0075001407010040e030006500c2c14600c501d802005a1307605000451914038402820703510058144144d0702c0c41049001e0f140c3c2c0c0c40c4482c11011110580364401c229404200741405c1400c40000039100600000e600c014500a10005241d041203d85082200c1e0920054095039035002e8040e40781810200c075804d022245c0b09401914007402d407880d01140e4050509002120390035034400407000300b0b46940902c07945142a4104042410281c504000c01e00c49640750388460002521410303003486400218050200015002c2760a98032103481129217081c1c0d0754807001c9200301d08403240301c00035014903000507542d200024100840722003103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 26255392 1250 26254142 26254157
    0x10f0305070503060103050c19030b0a140619050c01110a080f04050a030503090309040e01090c050616030813050114010f05040c0509060c07030b04030903060b0d05030706050a020405040914010c02070501 89
    0x2030054000707200c042c00e80b200307604007403042d0403044002c0144140d0002296401107006404be00500030310140c11381000c20441039020102c080d46e11101c0c190345603d0201640e941031510088000e0b00c50341300c2c0c81000c850a50812444801c40f0f003001c802441d1501c15a80d4205440c2e58000b02c900840c3c01c1914020401d8004482a40100c1d00c05c0010719000740c0c0750b5017502d251003140303000502120200d4000b846581d4461442400348241d002e40080200704c02d969091604444003400c480c1c0d07150312003004040c05500780100302d6407079607102084103440e0702c103000b000001e21504c94224455401d11490368003507203030030010405052600440d0821002d54540a0070226420100a020307004002170441740e12440700300001041405031414010750003516000419420f60030440152003074010510702651a40c440000041c000204480041d80c11001c0058241c40d5010b01c900a8401c2c0d5200d55841800d0442000501c81c0e41c202484480c0c00c144000c02c002d0900741410f0343c5500c00c61040b2800f25540303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 26256642 1250 26255392 26255401
    0x7030209030d030e06190608030a090306050106050301060210020a0e04020c0303151e28240203040311010c02011101050a0c0e09060a03020d0609060c050702010e030c09010614120103030c02010f0305070503 90
    0x4c86d8519007040312050001c1203164581d490b040c511740005040c00c0001d41e403c01c04105000c1588209400b4281e0781c6070251940d81002c50207942d800600740404e001345e50000300d1402c402c0c400d00340d10b415094003d02c15591456400704540d41c0e50419900c040e0031040b00010000c0e02c0c584403070516400500d00540c507024807a064104090241c0e0034843c4050100110000c0c040c950710b82c103604001c1c0480d00c980c0c0580b01030004a40b94246001c006000955000f008180049405100300055508007442c01140301400741c401211210740c01050000300c1e40c01e00c4103000304040c190b000800c0c009426a100000366400808025080d502034815940001d15084103002504149514500c032a024aa01044402850380c0b940100d03160b1407480c00c0040c0c000308103201190382c0000b10301400c00d0100e00602c24511510000750a40034107224072418800295130400219007030707000b81d501c000e1440442c100d06607900d050280090800b072500300d00003032000c2902d003092030180c8580c600400880e41c900d0300f075a54 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 26257892 1250 26256642 26256661
    0x80f0105120a060c05030718030203060103060c0219030206150109030f1112030a0206010e06100f12090614010501080c040e040f02011205041401150602060c0a05040b0307030209030d030e06 83
    0xd141c40c00e194540948100d000120b552401a881400750541e034580d5a0301e030010000304164598901e00c1d0030004040010005030b81c0010740203066075005800080e1001d10f21000b0380c900101161110161a42da0111a00341600410003d100d00c4010340070440c03120428004407030702483c0c3d0000600c0e0760111108080425201c040e04000d41da00a09000c1d000000c6c03880e01da00e190007962001c00144e016030014030100810021150308100d0543d020389442440e1240030f003214110a4481080245220030309035004402c2d045142c4031900f0460402060349a02c41c844800d40003406101e000c0307a2408041000791180034201c034100c903990300c540041c4e900c0310381d01c40c5c1205c0e04860703040e410440c8400c19824454110702c140d0f402503101c0e41c940c0395aa840742505500b990800340300c0c1802042902c00030041103030040f5101c1e0f841810081e45079952070001c1c0c415100c40c0103035085120240c00200070800280d0709507004210201c17040341180c6090b080044102c0036543c1d100030500300354210001080203d40c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 26258998 1106 26257892 26257909
    0x10f050d030807080606090d08030105040b01020a1e0c0e01180c021c11030f0c06010602100c0504050409020a05030f010c261f080724080f0105 63
    0x14032a07180030b010008020080c00911000360300055199485008039402e69200402c1c0499103052800c01d541e031368109001e001d00807413404980710480d40c00022403405103640003414100c12074200596200d001c00d06202150740003c0307400701003402642542c9940c06402a0b802140c1840703044140c0034191101e1450000964205416200342030310302c0c01491107890b0071414818410402130845a10b144164540784d0651000861120403984010031054100c5d407058ec2103510410501050000701c1e0003103800c1c4030101ea42008200b20340c3c100b40d049000c90500091840508e580d6800210b820001071000042c000c2c0d6440e144d4000e51a000005201891240200c4007102144c4060300300012002509801005c428420460703844589407200c40f015003800c0e801c2d5210340c1e81e1b486404110340b10110810020a04600808030b0103445116003030702c40d89034495800d0069103003006221091 = true := by decide +kernel

theorem cover : BRFrame.Cov 26079142 26258998 := by
  have h0 := BRFrame.cov_init 26079142
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26079142 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 26079142 ≤ n) (h2 : n < 26258998) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
