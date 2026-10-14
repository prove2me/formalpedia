-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3382
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:30:20.586543+00:00
-- url     : https://prove2.me/submissions/d3e408c8-f6d4-4f90-b498-dba5e384352a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 608093525 ≤ n < 608273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 608094775 1250 608093525 608093569
    0x61e020f07060c050106120c170102041703180609060a0e130216033902030a0c090e0f01090c05060a0e0901090507110601061b060b0904033605 63
    0x4111600140407440150001d0b035900380300080da90034040e0a59140350004030040c0c001078961000141003002060840d0350b4005e45440c0c2003c4200450b00a010326800104400c4200c0b05409100303401100903c42c031340d01c0c00c01021950703207a0410f000b4035020b52610305800a00030840900b030035008410340400c43c40b00510240d802a00c400c952005c0c0e0b000b80034040340207122305801100300740e040085034010038031140071080d40039581c20030384104903141c840203810f821004090100f95101402164040f6400861010b480c50703444400fa001010f1100f00300005003c2d0b00c0d0003c0d0300d00018001d1040c81c0b42c0000f44800424100700401103640c0c4808425402d208140b81020095110305100f00e00070b01058034002990f250041d00039041981003815950306802083c01809130b40d40000701e0304031611560058a03204d400c1c0d4034050f8010310f404140c075a03103c00c00004000c00c045d84951091a01c0740c80c448041d058034070350308039582048040210420f569000700024003150030001180034042000201c0d507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 608096025 1250 608094775 608094793
    0x70c050607030201020c0d05090a060804060231060e0a030209090a1502031902070308280e030304020f01080708060d030c06151703040e0c07060605091504060f061e02 73
    0xe495a101600480c003513500410420381098080c0183c040382061800c1642c5001664000264a120280180c0090040020204003445640d13810f403000c107003140c880c4899510620641007800c90880c2403204090103284000703c0c00501c9488250565003021345500045400d41e420481e03100c2c2e0083c0300f4407851043d642c0c0301012681300b204030403800400000c0103949051400340c08101e504281c030011801ca004010107000640c4c4103229961001852409042c200503d11785160030002407141c0e080150308207500b11090300c00c08002940205d10071144000081410001554261000c44c1e1107004a030850700000c8071400e14030802d2a00740d2081c504451003412594401007120b031009840003121380c0d01501880a1882d0400894003144001c0045040c1403034403e02420425005282c00b19440300481c1900411009811441c054100100001100d00c0c0111095122600c1000300d1071107275050a00016113580c0702e44485003615565960000c8100005072043c00c604a5901d40004500c100c000d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 608097275 1250 608096025 608096029
    0x903060b0f03031201050405180607030c02010209030703060b0901050d02090a0c2006090d09180b06070f030c0317010e01030b1e10030501050c040f1a0403050106030308090f010b010e06070c05 84
    0x410a04c61003103510800c03941040103120131200c005250109030f4100c00030807509000300290b2a940042c0c01d2501080305440071400300e001e4003940444030380601c1416070200800440ea0841d0aa0034410780d000384c010307030b40c80040001d02100c07010007942202c5640003007260360a2503040740c40400443d08211403085001d074900c901082e9000e40c02c1025400c00070030300048110501450078601c030350b8a00118940d0510f0b1100c04050388040804035020340c1d5001e07054072034440006403603003181c00c8003084071800e0720380c2000740a40038a80005c40c0052103416140b421401e0000c00d1390b05844240c0d4181d82c6a0b070840d5600c0e13031409000f8002c00c1c10204a83c03150b6a404e0400320f0703814414010490440c00b400c0c9540b5219007500c4000c2e0250141810502040c0445040c20011204466220303c1415200362030030004403480c4500c0d0400381c101d50800902006043e0050090340c061003420701282c444510401c1e1280c202e0b0588071907140096000300900b241840d0010181139080c1c0030f4903009011942e2000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 608098525 1250 608097275 608097277
    0x60604061410031413031b0c05010315050303030115020f0a05070e0c0705010f1b020f3c0109023f0c0a090b09061503040623041506090603030903060b0f0303 69
    0x41c0c5c0c9a4000284a0313960805a20203040d80b603c021118101055131616034604880c03100c24010305041680c2c4041d6480040d07810300620b4000d010160a40f5681e585880c0498200366a520303149015100740402d010f009000010340450103078120300584401410410036240390340c400f0308444e1001c04244081c0780810f02c284100d42d000c9030320220010b52214800c070600c425040581400007950880790402c0b202c0400800c0c000c039a455071401e01c004002d03c03401c501114141420105404d0101083d10901011055114141c079074022110913048941d280e804405001c5510304d100d440c015030b04035000038a80c1c40a084c1c1403180c1c00d14107540103050308001281c48655683d001c03220103902d421100c01d09003001c89015800c01401c2c2d401a025006200740700032903200241c40144490755850340300040040c100b12072004000e0815004406040900780100544000d9598003100e0b80303000300c0024481d429204400032070b903258036080340191540c2c071010300415205160941008420414110350380c1d081c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 608099775 1250 608098525 608098531
    0x302060c07031e0519180501031e0906090f03030e070e04081e0408030a080a0f02070f080c0109060c02160608090c21010908180901030327030804170606040614100314 73
    0x1550311640340c0700b070341b542c1051003406a009506040c0b0b011600d004201c0c14403400c1004d06e07007600e0017107804240c1d4a01840240350410010344070b0620028500101a410380244c9405805481102c40d130340c0c1c80b11480b25080c0d0b000d80300140a61004c0003a9025208481e0b81038103811901e810060515907108106403d651000c2039030720004401d4000c10420301403d2003000b0005c02140b03411414007000e60f6034074088561028000c1c24000d00070070104041d9409400c080b07005a80240c05100310700e09140e01079070310a41c064405000d0341e000d80010035000e20030700c9040e10400024004003018888207080c4010741c00107222001806440074000c4980c030300240a0380782070611400c1450365841c0b84074003d48806440500042c0300700d50110040010a511107254030328800200c1c01d01c1105c1c01081c01d00000041c4503030004004113008038000a4040b10003110740048040071061307030100d69802d0104800c442c00f41c000c0b01003003000c0440f01900c0c0d091003080d04021103003908000800c100d01c198083d00d490021 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 608101025 1250 608099775 608099777
    0xa090c0903050304060f2003070807110604060c050f06240312030108061b0703050702060c1e16050306010f0618080604050a030f020102121b0d0e0106030302060c07031e0519 76
    0x10011080c0c0c45680a160b100045641020480700c2800307c01810b07890b44141d44c400382940d10089002e00500c071407108068080d0000038940c2d6075540d0703108400b8152011149040d10280145008180c2802000c5282c0c2c0c0b0a10480c11500e200300000d8102c568030303070805146140c2601c518684240301140120055000e40040c070010301c2ca91401c1c003042c5120704400d550084521409000180c00250814103441c0e101e03904503070035504c0f42070000c081c919000100c00048a010300c01614000040e0002c036000b403c4800702589419413035103480505076100350a00c14914410f050079410440684182901d1101171603c004002c81e00741e0340c050542c60400140c8041d241d580005032041c1c00c00d0303000f000501d615844d40c0020760a04407100c1d40070301d0441d001840100c503105121030305403c0394504c404840540d008543d04000c0c00c0b021008050080060740811009031107200041034107900700c00183c5070410344c5aa035826a070307050840490180b02001d070309201800414088240d1038181c11070040344408031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 608102275 1250 608101025 608101037
    0x70c0206070b06100c11010f0c060510050109050d0201050d0b06130608070f03060b09010c03050c01020d060509090105010302090414011506020a0b0705040b0720190e01060e0a090c090305030406 85
    0xc00000c0007066011300440c40140440075a080c3c000540420419a0000003420445040003042c1c1d401e44070187d82d00402083d86151800700460401400f00c540c0940390203a0310308000f282c50300240454485108000303400308e0414403d811840d150703a0884103441134013400321800c00e00324004405800707241d03400040c0829900b40801145660028001c0c000c550b013403806211880c0307802c445d09070a1242d901e00a040002e40ea0302001410300480c100c480070302d4900b0013195100001d1400400401c8240603503072103491ba00000c6104400c050040d24143d0341c000346556541e40362035482907045200c1030180f18041d501c2e50711404075000c4040c0110024803154000c2c155103002868400024a0020f10500034000c0a210910840e5640000e551003c1da120752940ca0345140c11a40310000254241480d5001340511101411116030a80e03c43c01c407a00380040405590325100d090300c0302c00400d000150030048481003004682802d8100500d000c1c82414120b0440340c45e600e80a0443d8066001080482c00c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 608103525 1250 608102275 608102281
    0x1a0d05071505090d02120f03030c040f05100203030c0c0a0203030f0d0f0c120906020c0604030908070f1d1306050405030a0929091309060f061403070b03070c0206070b 73
    0x41018014490641e6032a1480c83d00d03d400000a502c00701d10000a070003120030f04c0c124a041070b000c12002c0f5815070300c08120380e1030f40340100614410b588513019804003001c105400180906220781d080e02d211250b80c0145045039980c402c84000da0b0080700051701c01c0e00c101000306006d43c40500042054894940d0440da55068255021b0291020320301140c3d4050704d4044601c0304203038070541d8408a03c212903030210f890900d038103000001c3c1c0030340696000f1a000380f10a100401d90400d5640c401c1390b00120a031001203a466510294620091003460700840c40500030050b142204844036600c541c100000b1030380840307551039180803210101e800701c0350381e27000292003007000d50010301e20b000401c0b82146a809020b01112107080c8901c100881c120014400b190f0548d80e0758910000d1404200d1081d01002058085d00f003070700141400d00e100361105031420501080c0a40d15016983c0103481c0a00107010b014500328800031203038402030040c020072040c9106131005a40360300c0240240b50180303c00080031f003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 608104775 1250 608103525 608103539
    0xa02060a06120f29010b0a091a0703200313051e01120c031d0d17071b0c050a030606090b030d1b0c0f030501020d0c030608030403061a0d0507 62
    0x181c000d41024080107104003503100080c40039111451140c1e400b40403004251030052240c9403812003841d20302c03150120343c0008990361003514050040c601e91035462202850b6140340042180c005040801c1c0c440c0350420482e00420300440c00308035241c0400003c4828155410070300c5080d0703040a180003010880c0b504040100746003100340c0440b07031044d00d82c05803590400000060000f0510968540445803546601c1c5c4080f4040c0d80108910b0800039010a548103103400d000f5183c01c01e100035403000c11101c03c000301e0070042c1600098400d11154442810314181540308081c1b0502120007201d580c5119400428161607512124000313510914000c02c00c54100803044054486040d029406540b00b40103005045611143c401018400d803104441c184049040000d5180d4841d0041903440e10300c1c0b5000010488150300401c400c40507105d0810070045212000c80690700903100705803440d84248014000305030260b000d0503402943e411015102081c50010400399505000265042c0e000000108208 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 608106025 1250 608104775 608104781
    0x20a080f0715153c031212050708010302010c060504060f0f063017090306101509030201080106121d07031a010b1c0b0306100501020c04020f030f0702070b0a02060a 72
    0x740014907240c11425045100d003200131381e851540218030b40b108500316642c1980e071000d0f42000e9078105410740c9a030450100090710148000380007808207482d05c0e00040502d4800d00245050341d0f4165500750b01d00c0c00c10b40303405018100242041c5c035070300e40d103130000c84e01900c10f41f02d10340f84280200c03004a510382c0b030040758003900300c48501c08141044804050480c14000c0302800560594020000d94461070070000c800042e028007031005405203d10000e02402401d41c220440c00c0301c400c0c80080101909107441124007081a103c003d0102e4a007074014840c60340241d01018801da1040030008845101c8952640455800110418a034103d0715003441441520004040c0c1e41c008200c1002e00d5500d0541800024484c80b4011194100402401f180d01e1070113800100d200b09000f01202d0081c2880d00c111032900781180708444c09440b4021181000c1d003840d000b41c0e4401401045420704640c0e90440c1a00803071001880601140920301001c18800d00c1103014010704a0795900a20341c61421820941c21 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 608107275 1250 608106025 608106029
    0x19062d0905040f030305191b110c06040306020705160308030a05010b07030206040b0618010b0403050c09070f08041112060a050610020601050d1e080c0d0c080910030f110c01050c040303020a080f071515 88
    0xc50f8010b800f032b4641c151141000c40703007203a52000d0010780c1d4590b141003950800d9182c1d1101c0745940700c492000000c0c0300c00240654069001c0321020001640d99032164a040d04c0307410b40003000340e0043d0b000680410300351042c072a070000024241903074240b81e441d0f58800c03011098004912421b07011509209004040108001050781980c80c0b82c01410031034400340c0407d07070018070041005001c2000034200199083c0301481170740c01034800c240d079820f000942c44d200d0b01d08665622480b440e0600040852818104000d0295095009020647d00f01818400383c3d8000001c15602002c2c019201011854101ea0303041045024104081e2030b007042a601c1030404d07080c0d0b03582c43c5c200b00140c0d54420228003814211801c2000844240c014103603000801d03005441c0400369540780c2884d12441160f0341c08a00004d08103901e403007008100e01e42d02c00908540074040c41c040500140e03c851420300001d2000b90040082154090f0060700703017155030b40d4a208004c40607281c200d54588801c00603031001e55007039072440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 608108525 1250 608107275 608107307
    0x1210050901050108060f0903040e04050c030615130b030a05060f09010c08040305040e060f03120a082d0c0903011d0f120319062d0905040f030305191b 66
    0xb09501d400346041d03a426020300920008000760303000c10074040d010000c8a0041c00e090b407903040341d4603281c20210b40382c40051040c0b42c02405044002a80e50111220242c00e010340188000300040c0b81400210007031003002a01d80d0503100d0025140d001c01c00c02c0047c2441440d04100070f003003a19240510f103082d181069003100c203000a075030500000a2b0042c064405460003440c1852403130ba6030100141d10881110316030b0340c01d07010302c000c1c240b9040d01140040c02c0502c429100c85050741c82c0c00250504513200d056800c0702544d418010482003070810708c580c0d600300c50803c4e0f099040280d4000001e007103d6028011500860f001105111452428401880300406500107085404070f07050301c000c0540300060005100ea108103000d15444101075008a020345902c1c981c0b07141500b2040d03400300c00e00d140001c20341451080b003100092070b0011070259501c1a50300006010350155035507020b0300904009811260882c00c40e0800311100c000c50301c920341d50144034800480d60740b002000c001d0a00c050b1048204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 608109775 1250 608108525 608108531
    0x130f090912030b0d060507030b1207060e0607110111101503020112021207080c0f0408010f061502030405040f020c100501140d051c05040815010801060f03120e06091210050901 77
    0xf1282c0d660541942c1c2402d40001e80800c080d580c10340110010101214030951090203642003d08001c80007415a09aa207180c9a81405212440c104400c50288900051400700c01c0d00c0d480b12039520a143c1198105411400c85283d00410586034050b607000580b20001c41d10580800c005542e8070510b0319042e00c1000c40b08616101e0f4000d404a00780000030b00303a00600c0201e078041024440191308640d515801c4110307542d15603880f2041d40e406001c0b400d8441001c1400c1200c08140e0740c40316001c0440240c00d03030b0029072030903140005000c00342900002d1528166404d20450701d401000380b004496150b41c80720000b405606005c808050740200f95200781c003401903a100d40001481c0003440074205840b055000b08641c5c02c000044031244280c1d0002841c1c0d00075201c1100e80c45011060765810788441000a10031113494604130100c1d40300300c2c070003d4280010700402d140224000c8580404905010f094070346013000d0180800c200415628a210066225105c3c100701800a80300c0d0940090084000b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 608111025 1250 608109775 608109791
    0xb0d0501050618120c030a0602120c0c03030a0b030307080a0807090906052112070b09070815010b090103090602040b040e0f0108280506010b040905090c0102030a05130f09091203 78
    0x404100f403102d0b54200d01860b4078150308070002208002034810b2060041c11518440d02d145005c40203504071203072100000611002260800303c124054684443c4590300071400e583d82c5019840140013120043c5400d4002000090046100307000240007120054070f9402d160b00341010000c000305015403000d11510b203442c00511159580529003a41114503045054108034001407183c1014007d040d110040e02c40015003c04100c01c5403507181c400d01d40380003585d40c3c0566a10090792160b500d94541c40d8507218003c0140800b0728440050035148038107242c0020742d1460350342c0303e2040360301c207400940000b00b010030200955601401d800e5030241c9090a1a4110f51500312119520310301550000c40c0e580e010140c1e00c0c0d80700b000900c500d032919049406c842407540e5460104c4803a50060180e04202820300700007440000000628400e074200603401146401d128000440741074000803680c0002a2550000140e8020f0080044d000b034140c0c210000345038420f5141008401400c1c0c0c00c0442418103003d08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 608112275 1250 608111025 608111047
    0x60503070603020904060e04060e100203061f0216060207170c090103031b05030d0911030f0714011403090d0207060f0206040b042f010320040b0c0c03070b0d05010506 73
    0x95101210750908015840b0715589001030090800c1d0340281410607a15170410003880480c1e00000c90b403040807416103507880840809030090b403104450181d001100c0b081c1d041140054035000000b1001c05c2c5c815200c01c03594400c0c100c1c0c100502603000c400140d0102c1ca040c0401c034146482038800c04c401070018808000d40c0c8021071410b10b8140b02c00340600100349004030f0300615030b51311000402c0c0d03c01c040c0d13599680c0703d40480d0000c00d100241030360030360300c0c0d030a55500d5802d001405400202e9100d0042420030710703060807042801c1114201c141000000701070800c0000380440550300a03101103000d0080d4041c803040c021b1405030981c0c81842040a04483c4a42058001c20b100703812540140009246070340f01d061400c0b1284158484410010045151203100d0294607240804407034240d0341400508540600b8034581d0483c0398003c050360707004000c100080500c0b0401401c01021031000d0303544c0c50003110006070411071a6801144c0412002031281aa1507480c89440d024007021a07440d418210b2002d8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 608113525 1250 608112275 608112283
    0x60c040f03110a0b0c15010b0c030304020409031e201204090e070506160b011712090a0e0112030f0207060c080d140c0705060a0504120c031106040303140a060503 71
    0x4409000c01c251900c44890b2a00c950080f08003512030a2001662514030402007652411407040e102001c2030241c0020030306000c0081210030031846103000314115141d68003004010280500114103002e155007c0c42411044826010000203c60b00c07094100411031a68810b180040c440d06e00060b0000c0391032502581003d000d0750152400e1030000105081c800c0c07001d903d00802d903040715520140111b000c1a10b0617221822000040c450485107481da41d8801125035000d0180620028603040744c400800136030030170005080e540c8401010004807582c0d5100c04111154280c0240100400c0000010241a0094190300ca00c420520052080d540f82c07940c0203101e001c2c0c4090040002c8000100ca500c84803083c0c10a02c00640c84019050040c00c0000b4000c140da0f00c44403045449014050005052451511415200e1034012034110348580030250126205c1810040072000c0c0700c4c45126481ca801c2e010014684181d1094600155018074032140103241e00d00141081c4010741410401d000b140c502213 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 608114775 1250 608113525 608113529
    0x2030402012307022215180b0f0a0e0117060f04080f070b0c030106120b1810080106080a142e18050102070c0f0609030b04060b0d0b060102060c040f 65
    0x140c81d40c2c040301e0754198480c0034894040040d41c4442c1c01c42a0144201d81d0500c0550080c44240d02003103000d0501c0d0a200190745203100c1d5620802c14018070086c0d011032900900341181e0300902c20962000c8180009200c03030295045610340402e8600140b090750a2820076001105840303000700850324140c0c1d0300041404004000902510002c12403014403000402030b80e80b540d902c0701490400d417904c0c081c03140c030700e81017440340d4000501c0d10520407078010794a10650b41c490f003001c0d01c0d0060a0b0003514480c40c074a080130700003040502100030005101c03032080c80350344054445540900903014850410480810448044980a42001d0100010b03030542c802d82034200300701c0c402580c09440016402c1c034000c10200c40354140d803031041c0f5800c000b0401d06600800215100e0644603aa8a855054089092405000f084040380c12001e00340b000c1040140c1980d4010311940000c14400000004504400583c40341200c501002106000c0d4079a0140091944010003c00250416140c81d041d01440c04281c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 608116025 1250 608114775 608114807
    0xb0f010f0603090311030705060702070f030506010504090c1e05010e0405090d030e01061e1505030c031504020d02181002030a0219020f0d200a032001020a06061205010f0203040201 79
    0x214070403000c140c0590416810a13031628150703904c0e04e15505208c2d4803408100c032014018000c1761804aa524907948268050ba6000001803265072b00f070a0502c0b0041c15403800c2031b942110002d01c00161036403210311098500b04459401c0c0e0070300e840c00001403d01580040d459105505160800c194880002400f4200c0500d5160114112658000542c010301d2160882c103100c50703140c00e1100e8440f4640703603008102c070342d000311091054840c0e000c04c41c2d840c0415125403440c484200f0210f01c51044e40e404c401c25900d03006000502d0160440e99800485e07004410704030500d0385030381d07a8403102d1400120000d1010420300155180680544000303481e4003510300418008540030040d035040d5220b51840d05407401001e0310f0203001c850b483c201641c2801c02d02541000240300501c0803989030811a8440080301c2d0f020b075406034282d50240d5011940303c000b0307d00314110b01c80e02c1e0124000ca000c0d07006803001020b82c01c820010f8415941022030a480040318903a1041f0b0040050100603680080401240410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 608117275 1250 608116025 608116031
    0x60605130f050f21030c1e0106050108040f05120301170c030f07091e020c0619060303021009030e0d030509010212070b16120908130608160e01020109020604120b0f010f0603 76
    0x4a21030303003a002400c1e04d0315409511000c02e420341c800d000007031520340c80302680401038140c10801e03d8441c01e8504c1c6010340c1c0d0000300343d603002c40d00088200071a09445407040c1c0a440c1281c1c05201600c00d56042640004010000c00700c204080c00020300021910130310039001ba001c9400d6407541385513270b001d0340d1140030b0f1500e0b03441140c96813003490342040103594180350b8400d6540300d02052882d90781e00415140d0320100312002003088500b01e418851481100d6040e0050f141d044072b8140b001c070060405070f10503414041000c610001c95036580e021310311a83e1003610f990742ca0340700e04000213180c24000d032003030a80e0140402110300800d0f202c1c0400d0340d022200c508036440f85403492074100c810283d0b450441c5107040c14155402d042102c003901902040040110140f40c841e40c440003203c2640f000c0e070f65004400c1303444200d000c06922480881c07031114010700003c20202070645c0400c45542c8164061404192250a803104212002002c180c2003e42c1e411420b105504040070420403100324410f680c10305513 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 608118525 1250 608117275 608117299
    0x1080a030e120f0604060203101e03021504120c030c08150103170c16080c010c03050319061d1f030c092d090201090816060809030904060605130f050f 66
    0x601040f110407600a58010359080742440d24000000e034000799200001c076075003031402251410031001404450911400090075142c6180c081c0710801c0184804501840710401011500d02d0000540c038418910828104a03910b00c0c5d0300300004882c80f80e4100c0429500400030340540b4407800035080e8152604400ea0081441c1640ea00b822140b0034803159000c4d0340111141c08440c3ca01c00c42d41c84045a03032000540380c0800902004513504858100300401154040c0081428107803144200e09070450321000000310b80340c81e1400301c0d07600c1c041181c1d44070800003000d0400000c8c00150190342151030002088407005400c65640b0300c14481180208200d8075034889049040c1020785002607030207580010000120080681d10710042d001a22040c1d020071120840021701d1100003030411070300030280c1400030100d03003090b0040b0782a04003d071217400c05200c203100000407950f5611420004001039281e0680c1d9405200c52300610100c1944040018600c0c0d00040115031150385040500f503908680000d0208 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 608119775 1250 608118525 608118559
    0x290105031f0f0507120e01060e01030f060e120c070e0f0105091e1501112107060204081b0918070308030a0f0f0203011409010305121b030d0b010801080a030e 69
    0x45490480b00030035904090511406a404c204ea031200742041450a1000e20030b4503403541d081e15880c1c1300d01112248088010800b191000301c0e03030052544500c5010070000d008280d02494041c1008070814802400198000004020008200246000c226244451a06c818058800441482036901543c929800541c52940c80d0a81c01d141000306a9004158148140505100e10280007200d01084024203450354440001844000340100030b03c0e00d03140f41700070f05010071035900510011190940c013840081000e1005116110510b6030040c1c495a000d1001c000704814403502502c1e850103e5501890b02c5c8a40700c02003840b17800e99400020040d0341b511403402c00401440c29501140801b45401c8010b148401150003c504880b902c0b0006980e2900180c00c00450807000e01c4001e240364030048484443c850404080c24840942618100601c243c102c0c850742558080342c10328800703503942c6150112541e0040f01daa800361003504c00500080e00c0b25580a890109101186d6224100342c0041c0c815003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 608121025 1250 608119775 608119781
    0x8060a0f080d05071b060804060606051801050a0207080102030f270615010c0209040b09070b04121b030206030103050309040c03021804052d0105030c03011b120207080403290105031f 80
    0x707500da000d4105d20440c1e94000c000c000700741c10b403001c0300c21301d0424800280c131911690640301a96050b450007004117041000654481d0700a004610640c05500c200080701e03d42840030754445d080785000140240b50508940007028802004006d1440d104842d800c0344040018160743d2100081000c183d0f40b10100005880c5401c101e2030095000300000104010800200c03e8140076807204070440d25040e4603610104903d005a004240541480c030f0b040c44086400307001d40320b0f10001300500400e1601d032039401080b56a07001341c006403030075071000544180d142464481c20965090310700d02181007601082d118403101e109289603610030340c2c5820200d07480d04000c061140e0341c500b00207810303041c9900012079940954001d2007514841d000d041d00c81042410113010365040051040144444204c07881010b481284101146c0d14600381d0a000c8640000e588400a001450060000000c2c03001c5100034280030442910781c41141200c1c010040103180c03070014401044040400d125404074442c11110402 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 608122275 1250 608121025 608121053
    0x30a081504050108010e0f07080c130e0313060e041401050607050705032508030a1710090c05030603060703140112080d0c0f09060512060126010608060a0f080d0507 72
    0x1100b40381c10b000154110381540100d0903010007005503901c00f406450400c0e00c901b414403e51070260050508020310b4034000f4035914010040c0807001500c440c1245549155411076002e10181540d4180e00b40601c035017008000b070812208540500c0341205c10114081c1701181803080f03d000d14004107068080000500c03c0038040c0401600b102c041c844070002c01035600f14041c001740212954601d0100c0c0101740441124090151500d0300c3c03c92408100f260703024400028001704458a0a0704042041f2100d4000c240c1810841c3d5150341d268244001010f0801ea40584000185880c1c5118500410054031880703044511015040569601604003410b2a1090001d0360024034500b02540c0251b5810140b07120a00c10250340e04034440752101d0081d04c0910440260071202c102250001e03c003584a0304803841c03044102151485240192740d606200003200303030080d5000c5840001000a03d0410580d440000d1109030170030840c0900c0d242a003516032068896240401400103580d805010390150400c4e5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 608123525 1250 608122275 608122279
    0x16020d02041515030b030c0d2303070605090c030c0f0a2606010b070b010e04030c080319050604150e1003020907030905060f06031c0320071101020d02030a0815 70
    0x1111860040000903602c58000d0700c0d0155090115407035814441d1086804591000e4001c0596818140400c004030013190011100c8048285081c03400d600015183c0030032140307210045840d04072a24206090700c000070100b400f07640c4801100d50f0076079000248003500b410b060711074050000000780030450320328442d00031030328400300100000041d511007400384010f030340740c0c0701079400b1640c88240101076841000c2028181c0b044590051101055602c038564100307110b41001544861181e4a400c4c40e2782048507c1102e03118100f4450903801006e0003043d84c001001c030390402510b800003001c03c480c004a4024022462035400000e201c9808603206100036640091030349441d0701d860903004000c0e2282510480385409441e001c140ca21784401315060051200401500c040c00e0301d030103d1007031880044615000c05890342410101c1200c00c0c029107c034441d0302c408a030340c2d078401d505110480c03138801440141194420b07410015180d80c04816525010036910307060513144c41e40080e4410501240b10301603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 608124775 1250 608123525 608123531
    0x21f021c050705060a060506190302070204050c0c010b0109061706120102040314121303112e0e0907080105061303060513140a03020316050f0d0e01120e0316020d0204 73
    0x621600240601a4940b2443c1103910b075540d030b50748581c00d90b0303240d00c0b41d40d8201105002d00e01440c0c00004a01003030610301d2400504007840740d00010706444003590243c007040380005140440036000c1c022541c0019080c20010713055490540020602001802c0c030120010580e0082a510343d200c41c032099038800004004e5480359200d0812081c4807a005002440601c41d5030008200c4030148400d03180444454111411481d1940e210f080e25041000c8520358402c3c83c6500b6004103042c0040b900b413412185858071722001810390000360400340800a883d101b114a034041140d15540110b0b0541583c800b41c034501c0d1110465040c030000c0c0c0c9016040107081900f040c08000125511020440e110342c0603040744040d28059061940d2140c040a10140050b0010401a65280d01d001d50303440034075102e14200d80703002891945580c2410329181828002642503480c910032076034080c404850044c258802081031544c4508030959a1151903881d54415000b10144c5d019035440758401a1450b8005d0428 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 608126025 1250 608124775 608124823
    0x1027031704060204230109060f03021b0c03010c0206040f110d08070503031009150b31050103050702070e0f1e091e03070f0230010506031009021f02 65
    0x24a02030341045c001d0203500d07082c8481040c880b900d400511340098006071501c50060341480b0045544040c8030121a042c550204032070305070101d050800304444403070000500b503550496020035003515080c1c103540c1300315400181800081000908000704003640860319804d910341c0800814186041d0140c0605058400f050507000e20a0100065214101010440b16215100c0c0b140c04120b45900c148404040c0c001441401071020440003010700380100300704590340e201c801d040c0d240b544028074621109009203e008100c60758160044a401c1049400500449420b005d08140807810040030314106d440d0704804150078040c0a55900c030720100c080380c000801d01c0c201c440603694203400e034100000d0384804e12241c0356025009c819a00311941c0055513400c6202c1c0c540800100030303101d402d54940c030084006070190724810503171840340f8945004004a00d500c2c02c44200360800081ca4610701d03642c0d05001030f580040c1c0c1d98a041004414103400c5520b888419444101c1c0b602d181148402984140a144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 608127275 1250 608126025 608126033
    0x100c02030c04090b2a0f0408010b0a0303170a0617070f0522240e09060c1c0e07090e16050301060509060d050c0a060207170c010c031215030c081027031704 68
    0x100140c0c1d1235013000340400101c1710103200c0600d6491201400042030070f51000074a944802103107801a003001c402092a6480301e40b00e100c8150b10065041041c1c1c040700d01008109480d01070640105403c50b011280c008100d080300c40007034a00b41e009120079554031a90499640b0100525445108403942804c140c1c1e122800f10f1140403080c0c1d0151241d01c60000065401c201c000202c440f8500303045008405034a4499074500500443e03d0426004e0050000200e42d4034541d00c10212001400001001c2c1c010181d450b2002644240d08071030b0190341440320510154440c1c1c12400d4110f0b105441007110313412241020340c14030300460903050f40300e140a031000680303681c001646815912074240d015005000e9040055442e030744403e100e070110b450700d1044008240602d070344103220038001d403020620b80007002d80e000c01c5902c82d400c00c40301d0480e40c4009004480081100c40d5400318184010032a0b0007a004d026000c54099020700501c1c0c1301064a03074000c2603c12410300041100300d50701109107040c1403070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 608128525 1250 608127275 608127277
    0x60902070803090f120405010f090806040803061e03030a050f0d0c020105011d15010c0c0b0406050316020321060d050712050d02121215100c02030c04090b2a0f 70
    0x10200582d12400410b060003020104440b000004214000b518047c036101c015a030500320014071000b4040040301c0001c005030b003449858480da11804a080d0f0301e142280c1004441040d180d0413600204c4281a00a01ca4500100f240c0c0400402c1c10042c3c1c48262000403c40ea0f40326040b5034000c800e040900105c480c6805401c00c0c0d041e00e0884800d1a200d10203801038047c2a00d044881c0010b4490b100c460510650080000c1d20846001f0881c0400e8241c1382c0f8001170f055030040c0d01c00c40c00584000b00304a0000800841401c20300302a102840c0f80a00640d1402400710740c403502402d1440d445408a06c4594542d4031800b8410ba000042da010507664448286640d0741099054641e03003e2540c1d030511305440030070822203042c01103182a0a002c92a215011340301801402c0002c001d2143d000030307110ba03880000112058000707960780c00703041c0c002c0e2040c5810030074010034041c05181000481e4001400d4544096031000c034032505540180501004c0c115414040d4081e0360607028000395805142001c0c00c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 608129775 1250 608128525 608128531
    0xa033213151d0d170a02011112070e01030e250f0f0e010503061312051303050d121b0c050102090d1a130b04060b032803030b0d02180a060902070803 65
    0x7580c00418010410705008031440f41c020000d00d00791200c11820800c0d144000500200b003414400042c848035005082d01c0d075980300721080000e40142e40100300146502028001d0194020711b02400030403840304580790749121219003091840704030b4400d032080c10b1140800030010104030045109956449925499182d92070042607590f483d580d00100703481c140050341c43d0054084420902c401e00d05501d07607030680d0003007011007410420100712802c91b40230b0241186000e5401140a0007190203101c00c0500103408440d0103903000c50506480344920340140c640382d080504a400c114041c402c107480d000f4020702c42c04182d2035120000034150f1050012a140203080242844008141c03606c81046214214404078001441d90b0001c00000700000d1140d00607800035070001d800c40d41968140f03030743c4403070303110411000407003c00d42c0e1802d22061540c10b01030180c5581c010354a41c41441300304e4010070560f10700c120300c424000222001240b04800d40b544524001d001d020400c40d1107854a160240d4194425 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 608131025 1250 608129775 608129807
    0x4022116050f0303040e06090a0b030601170c0f03190201111603031404150e0609030609010e01060e040209040b0c0d050a29090a050903070b090a03321315 68
    0x101001c0421400e0004c21181039070a40018000c1b5596203604102c6e040d01c00404198243e500e81c00c01c140152001c000140c007800e0707100810855840140083c52400d400f0302141440f50074909141c254036100400c3c1c1d02003058020034200025020782c00140e62090516003186040c2c82000c14120310382849884c0842902d1003540d4540e90312100300d4a9605600850046040c0d600d81c2c1c2060408540c000c1094040709200079010500300b0032039900017070034150116034260169440d03118020a8200a20504000d461020001c015508054012903018003005000820f44a1483e02068400414800b030754801502100103201ca0f14001c2031450242c0a814203101ca40c3c40c1d0403240003540c0704042d40980a83c4005400040607030b603005040c0c00541400740013448580010480c4074045a0103110b028031900c035480c01403061031610300d001400f10402c1d0441007040e1541c2d81851920000c0c18a010300e401c4166541c007911b450a00384088030340c5000e41e008a0500c080742200443c101c2e00b03c0e034003540c64181 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 608132275 1250 608131025 608131039
    0x31812020f15041407030804050118030615030b0c210c1207110d0f1b0237140114031e0f0a06140d020607060609050c0c0d030903080402211605 63
    0xa03510050340c1d405d041c00014204a014001270119510400c028880049035150003a86140e4940f02e55003200e1140301a00c0000408500a00a0080150035940c0008504e00c08074500183c0d0904c4010101214824181200134480451a00e022180c250b0312098401840101a410f0007007002d00a6083c807070700540c4a01800e0350101026002c0c0890300c3e21a10b55481c1c9008107040201b100700c1c4540d0340c820407a8095100c401c08602101c102c0004210744400541c1701c4442c0d034802070111903080710f07a8010344207240001c1400e1644d99004044140c00c5800c0040140c0365150b007901d0303801c40da07400b03c00070031058895010007a55402d2203000c280942c0040c80204080b6440310820b0100816001600350052003041180b401401d1420081c22481d000b5800010000d0f200d40a00c1c003942c2044c2c90700400b0394008904191003520501c1441c0850449040410070403c0079034010b055110002c001070302c101c03105d0441840001a560600f84016080700586180c071399569002410907074075025090051203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 608133525 1250 608132275 608132303
    0x50a141602100c0807050d0608030c0703060f0203090c0108180616080a0b060913020f0f04030b0708011410030b1201021305031504060c020a08070809010807031812020f1504 76
    0x124414281c40f00030070307607075a0001d075502481a52150b12102121100f9aa5100300040e40041400a06543c1081002a1640900e11300f0101d0640384602c13800c150142c8100240301203080d00065070b59100200b801c040445d41d807600071003608001446888000c0340159010490041c5c00d501d4214190400c0d0f031200d90954640b00000c10460302c0c0d11044a4010408002c500900d00d041400140f0350140308e18090302d40052504101e00ba03800450000c40881c501207030520030000e0100b10140c4c04404c40c80c000c410743d03141445c03131045911000342c01401040c0c0c2a098502e9148607070880d0820301006080100c1c189940c80c0e086000798412900809076801c684030101d01883d01252215007100e285140720401c0c4c480e42c5942004180c1200d1500a500c2002a41b030b00040c14003002d08a400c2c0a400e907191105085800584694001400241010b01d8a242ca40048841c46a54522540c00a40d01512490026801e030b140c00e07503c201c0001e0360b21a030407000c8024001d0201c210301c154800e02100621075 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 608134775 1250 608133525 608133553
    0x1212040c14031203191427030a0309080f160221100203060d14030307090e040201020a030c0204200301090608010b09010e060a050d03030b0a0f1503050a141602 70
    0x101ca0405040d4150460b078082a000c0f40f618001d10341055491000703006114003408042e046641c442c070701c03091b000305100030800034040f031020035240711403918601110b504011664585074031810924006056075000d00f801880400015516400f451007200703584d1360b0704040d000a24440031101240b0071901703234000500d406280088540b41e030220000078200200c0b05203030708020390801001180c0010134191070b000880c1c0040700703a030100c0740c010380034590383e09003c00010319034015500701c5900484404103010050341e00041c103566180c0c0505c3c200903a40d881e40300280141031046410110b592107401d15007000501c143c002c1d8101c480a110410201d0b41d941a11800e8556586407140e0041040e0010000c6002e00261954425001060000651b8580d8001044480c03170010a0780025640d018130344440c1003080c07101c80a8540501341100d003a00d040744000c104001200094200f5851f0004561500d50582064980160a00d401052443d104400c035072408407540b6004014032540b00001805 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 608136025 1250 608134775 608134799
    0x20d1425050f070f0b18010b0109030201050f03041b0f140a05090105130e010f020403020108070c05100c021606021c09080c040c021608010c110102040f14031212040c 73
    0x4008151241401c00105100c2d00c2c215800207001511105072088601000a01c0304440a2044500c3d144940070011403811044c21141c0c1c012025060000128040c00035030f0300682036402441d13403503204603030704d035110b1800e0340c01a8606d904003050250341c20800b1a003894039200381401d45440465090200088204000c0201a588281500170340711030010301c01400e000c1541c15410b0003031100429100600740c100c0e0708480c8041c8188600e01c1d4003180500441d13038819a050781200141c54a0f0640800c0c41d00c0700340e1036120401028800c00c1e510800050902c0c0203200b2021140c01c03000b04c02001a59420021751640540f01882d1650f803024001da0744a24014032418060b0f4103c82c0060030148001e506000061030a02c0302c1e4001e40c40782c0390b114883d803130144031280c0c040d001340d10005c46d145240240103000e91a50140c40c14259006110174001500c40c0d010440445e4203048407944c090004001007401e1411a15021005d001c0c00191500040c900c02a03090041c1c0c461030482444540e500c52100b80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 608137275 1250 608136025 608136091
    0x4081b070f03060b030a0b15101110020d1d070f0e0915040c05041a100c02130c180f08070b0c1b060d1401080f03032503020d14 56
    0x400640c5420b00210b00d695000651191018086426034001522683c3e038044d01121030001d003468909940780942012080e0700740c40f200c141810307003648103540c00554580d1100703c80402c585d640030529031019107154000d0b0080000401402d005001500303031080c0c44403018003e034200c4120192001079060500c200340c1d44240320507005041d41c121203c0858180d0f0030007030420f8032840001c038008109a955440340003100d403408805c11600702081018021300001000c494014011881d00003005a241c5081908802008000000d40c0d840d42c244140c5804160100d00c02002e600c0e100c020448525102c0f0701e1054070395040407105900e55544410059210300000007589401445064058030540c015496904000070034107428009002050360803a0318040314060307142159401007002202c148044850180400060f500d54a07240b010341c0702d00b003a804090881800b1540303803440340610950580e80881c003883d0092142c580440840d4411150a83d0503040d1000300c000100b000301601105069 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 608138525 1250 608137275 608137289
    0x4020f0436020901270e0a0b0c271302070807030207080303061807090b0c0c0f0f060a1b0606090b1009270615020d08100503030301141804081b07 64
    0x43d00b40c0c2030900740c45004846000110701c2d81c1c0104c152400c03480e114050f11415600c0d03c4014480111582800b0803584006030104a0490040011003880121703036202c0d90100083c0007800d00c103c0301e10004515103900110400118a20220b44a41005100c81c0140b9505029600300c905154851170150b0f01c80c0b00a5811070340c00703400905410784174200000000e501803c6414029801540c0d0704010f8059404280c6403402030b0402e9194404038034012002603c1c411040c0c0328503802006d001e010400f9072045250b88e01c18441c104000d0141d50303880360000c0d0415940710310300b44560340d590382061006c2d048240c40c0a12a228280c1402050391042202004460149524041c1c05400c403807169110440c0d150b03940c1a07540c0b01d50000c40c02c421400d500c40100c809030360040910340340c5a04020060200540115844681400108240d94001050724152030b4450100e1440080322400545108804202040b40304030a604001c00d001088024104034419500c00800150340c002450361100d0311030161403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 608139775 1250 608138525 608138539
    0xc081b09070e01031d060702070801150501350411040504020a140a0314030310051002060402060f071a150d030801030809040e070e1005010f02100504020f043602 71
    0x24540ca4400c0c0e81104282206060020703805c070111400c03110190400f1040042c5070b0203501030100c07403681080070800419640008000c80700740342031804490440b920a40e810003a10b8103900c84109107840200102c4500e80c1001c03041981740c030310402c0403860104d170b05071424184500e083e11542464083c0c82d103c1c0394024010755034203040501c0d0324200231001031026005032000030044001180303281152a003002c2800150b489150800e922842e2005c0d42e00820b0285104c01c00c52200d898000031a80d40180e41220241e80301d510510b903e0105000d0034001070290008040224910700e1780460302c50081504101d203080c40e10bc41c10a000e42c40345846030050020314058010000700344244080d0400210051010071801cfc44d41940910344005604401200035694003401450134082ca003c1008040a0800721041d000417180a51a044565030071045640c80d40006021943e41c581040c0a07058010700c104a4140462400c901e49a80c0e404040a108010820060b80104288402c5000d0b54014115 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 608141025 1250 608139775 608139781
    0x6061209020d1b080d03020904050c070b0a2a0e0301060e061309050c0d12020c0103150b03041410090b0a1802010f09050901151e0f0c02030a0b040c081b09 68
    0x390001c1d540b59810300c00442000c000c504d1000920282214811940d405a1210103038400c1004446028000125101080086030001101194403070390010301c4144c0054000b050045804151440071420550f40c44408410001c0ea074116510070003440c8150020402c0c2500c44c41b146d03001500c241c0ea5261b0007407800d0165004400d140e00281d5481c0e11401c00d541102c404040450a89080300300201e5182401110010525a0400c4030b01040c0c2d40c2480c080c00011220059500c2c0302c1c400340203c51041000100041c2802142c1e05910100700d81c410840c0c0010300003800080051054640448000400d039010030f03d080c0c49401480071640c50141d030040104003940c01991426216501c41c0c0a0003880200000c00355200c1c1840c9000b0711103006040c13003c0070058801800d0b8071924541c070b010009035201c1820002e601000b0441c260205081c402d00400b00760000030701e05100c11100401d5014200104020031829500400072140b0702d41c00c0741d41080a0345081d80e022005c0d0360286400a0381c1c0000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 608142275 1250 608141025 608141033
    0x6060e0f1b2104060203220308010e180714042313150905010f0f02031e0702010204030501181b080303060409020d0b04060b010801050109030807060c020102091306061209020d 77
    0x20400200c030035080d65030540b041e034050307180c0e000d0485040d901c10b58080200103000201b014a440c8601d50710304d00301019100d0755400b525110040c01504030000b05400002c50380901200402d0000f80b2000444071180d43d14841c0b0003000032140c1000d4056800d1590700080c0049101d20b540841c0e18a403034a0110307680d0701c1160910923040120649035425007140d00071180d0100c1c4207101f00180100000700d258070109800f0000c0c4c1d4524580c82404501c1081004680d41580c03210305c0c200c0280028020b07558413600c10480c06400360380c00c0a8125481e00103507200001c808900c0801051207040942d2002800c00c801104c0030007603103d62001070700204001030980c075041c2d015801c0c181c401016a85007000c5a10b500601d060220b0301182c1c865502d500fa00b0007580c00084290042c4002d2801440c5c0d40c1c2103944100b07003400b480100418480d02d0b010851107850003074040e51030301907000c0e00d50388801010428000250816115120100e101a50500043d880c1c50103070b000b40680140a034040101a0b41d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 608143525 1250 608142275 608142277
    0x1050a0903060b0f0607060b241603030219020604170307140a0203070c03050c0405090102030601020a06020c03091005040e1e0423011d06010906050d0f06150306060e0f1b 75
    0xa4059000051100090031661540091b01e1550b002e0351000454030b03005802e004074084001002840e5064954400302c440c1030080882d56a04a03410110320b80355054903040d000f0340114440c029000410803829101c4580c0010203512071805402020b4284659500120309440145c42103400202e08414840c2800c2e42000188006850341c412070740f80c0700498492511000554000310b0340e80d0080c0d4241d580c68a0300f809840d400c00307510002149107042803000030b5070795854131200a107519000f144000c101c100c14001e03180440346c00380c4100000201c1c0303e402009903205004207040e003188580821091240400c101101c865030380358000141d29207846030940103013020040400030b242031403030300b0040e030b42070095183e0442032082103034290411105007818008160081d100700c40c6042c104002e00e41c0c4045c0b4906200ea080800072581900508044001d02070030380e2002c0b807204a51000104108042d4410802c68046036100140c54031241410580030340192401c42a00d12011113032011030318160 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 608144775 1250 608143525 608143541
    0x201050c2134021c060f2c100c050913050103140304030b06120a1403090424060806061b0a0317040203060412030b0310020408070f030c09050403030b0603040605040201030b01050a090306 82
    0x1000007030500791503554800c01c0c0c54012540303034100d91f180c0740b100c890750501d2203c03048030030040d10101c1d40d2038001000b00f550322808510080c003c01d440d800c40d081100e00440c1200c0e41440060501c800074a1040c0034a00603007400e1004135810741e0a42c0302039032401000300944043c0c80d441040b07904d5549450040042c0c6030055009241c0034058100c6401c0000c1d40210700c0c5030b803400c02d24091070301c50f40341c8000c000451384100c0307c0718591001c1700603905400c0c0c03000700000161100e41c2461001e503203402d40895020b025000300300340707070110030420020320700c000140c01441c0318070a40d03c8101d010341c0d45403d801e16640030381340250980d11400224000500d001000380b0317002d000f4039000811442c0c090021b4584580560b144510f140d0018040c03280da08240000f00103080301c182e050140380d180d40d0710700c2240307007040c4580d81c60076a803440030408140c0320350014154088014080d90701ca080034100140201801d0354101c1c003107840c100783c0100a50184041d105105c000e034480d04045850360b01c541010701041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 608146025 1250 608144775 608144809
    0x30b04030c15020705010e0c0a0315020705010615080f15100e0f030d0e03120c071e05060403030e100f020d030e0115030c0e0a06120201050c213402 65
    0x4800c040042c00c070301e480a4030142e0b00500000c02c00f020815511410070310030f01038050050603184824008610701d8101b03410400380c00c440040e991419410f0107401450b8580101800d1110400450107480d031200a090080888a8145106480c0c1c00c0d500080c04c2e2090306a0754200c9003402030000d066002d00e410b628503c01c050008440340e400341c0c0c006410210f105503014085802c2248902c40d07820104201201f020300210850301d0003070420300d41c81da101042d12031300001602008000e00042d0750340044000914024100a81312900c901e0054690200722400c0381c014507181f080581140e1060604100b180255009007000244940c1c08402070500da030107640f40d5640350aa0142074114602c1c0c074400450040401c00744450a00d0102c2440c44005030081e1086401c2000600c5080300a5508880303140c1e09080196644d00c050070040c3c24090707171361190b007804a80c8140c803035846000d0310001d100f0131560b540b10104030300c3c40e0361031848035000c070011004038907041100c50780040c1042e0603484034160350 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 608147275 1250 608146025 608146043
    0x1503080304060e06010b070b06030a0b0c07050a081912060609050402070f1a06030d020609120304110d060b0312040b2b02030c04030303060510021c0c050a0602090108010f030b04030c 80
    0x200e00390b4213180c0b88082c2d108610b0b4900c00641d64041c480f01c0108681c01034000c601600a1607240e80b18038010400c09072800d0050203001600500b080001c002005055030b1006a00f500c0c2c818050005140001c400c1600000c1048825003404a002c54455402501c3e210307101c0d009030034100300500000750020401103e0000da19680c8002042070710003040c1c48005210861308540c030380b450030f02d4204560b100000c8155405034084c811107440105003223251071025400d0a07201d80d16404d204008a0094003100d03040780c000941e41e028420541c00c0820000c400f501115500715040486000f28840e41c820034071660030521209402d00c80e20664488509400e00781400c04c11a0061140200c1c1c0c403ea50355550312a00003400c000f0940c05002e03880c02030104807100e248035040705c0006034403500300d80d40c0c01c501d01c1500311018103107d0003240010395039038001d402c49414001c80d14140000703601c010580c4d07003c910007800008840042001400c2540d40c001d40424068075035603400e0752030b65402c94040303a2100c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 608148525 1250 608147275 608147291
    0x90b0708060d0b040809040e030c07061412090609011a01051804021207110606090f04020d0201020106181a09090706050a0215040b07111b0d020d0b0c030a050a150308030406 76
    0x4814140705001314002c1c40d5039643e8200000c2040104c642580d5400d00903081481454288000401d0784030456296060100c05c5103802406000c02e442505c001704403881100c01403100f158030020b0000e10034a100c0e03000308202d00100f000003138941e112107009070002e00100301c20034403030341100e80e008034142c0003500c00350821031010142203031000102d03042400540c804400800c54001003100c0c07900301400380e548412b1410039005030b1003a004010000707800781290748141421079200354030280050031a0803038100706201c42d0342131101038800032411a40301e900300e0500214618003544054060b044607802040d0491070724000342c6807070700400c50140c00d5000b000d4003151a490700100240c0315510030601d5001300d1a100d0000380404000550740280c542c01395880c106642100504104100c03800c8820f01020b00071480020780d40182c1c80f00050440204a09101c1c81711440e201450280000b0320091142d0307a9690121802c40301c1000091002c404a10010400305409100458100303000d1180800c01c66 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 608149775 1250 608148525 608148533
    0xa2106060b070c0608040b040b150913020307050405010803090909071a0406020d020604081c11071a011d010e0a090507030b06041103060a2105060708070e0301090b0708060d 76
    0xd041030744068100314000906504004141e103441026000c107040008042c10203032110700e180b0744010f00003465171112502103007110a00180c0c1340308115000304108202d1408080a01c540614604224020711444101003880d1400d07002c0c40c0d050726003040041d4108442141084017514014200c41074900840c7e0003c9000d0300f80000544600900445e410f943e50719284000303240208404260b1b007103400400c00d100c00070f41c80b50111055140c400950140c01107100c0002c030020200400d40b01101d0b480094442e042145502e08001c828820a110200300da81c1c40c070301c403400d8010740300030030650783c0c5e0200050024500f801340d12500305502000018040319940d80306c3d803503c1d1a98100780d404003140e5081190524146c01261845011030f00140e0175070030320328003045030104207020381044040240e14100e000020810214203254000c401c4030a1400d000c034018085076001d540c20741c000703006a08451900d04050090f0300c078850741b020104d502a51003450803074a2071030191885038000e48030b10f056030101d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 608151025 1250 608149775 608149781
    0x2100b061206101b12090602010218060d2301080c0306070f03052e0e060d020a090b04150902071703130308040206090d11100f0801031b1205061f050a2106 68
    0x40743c810243c00900641c03805d0040c1000c0802d9200d02c04581c01000001c0e110524124002d841003010349089860308030040801003c5c0c407001079074540003510428209003484144503100d040b5628601610a41c13140f00041c161079100807954900840e82413000d0ba2604c502c01e500603640000c4912060b08803000d2005a90600c1e82a45034502251041c5030080c0700c003440c0d088800341c00c01d45c125213400442a0980c08900d096640f03100b030b19507603965841620366a450f90340010b440e944003025100c00b070355241c55028000390000e03102035400f10356000c00030f00f001050008136406028003000d01582081e46179802c444003800180704030b0b04034109000b060f8168070341440641005100f0b010342d40c4110b40c9141404911b0a5126940b4100042064101c440c1c40d000003026046d288c03c036a42d440c2c0c3c214825824072000c000303640002c02141040300800c09014000c50511b004000b003d41251100d50f0152310b202e21000e950081e180d226000391820880d410090070041e0703581001e402e5084038852a80c8404040f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 608152275 1250 608151025 608151077
    0x50106050604060c0c0905090a081e03240a050a0b09150a030f2406120915020408100e2e0c02070806010b030c1602120d02100b06120610 60
    0x4c107044141c0701081000c407801401c041c20401c0700400480c6040407445640e4603102e000905074120000d60300302c2540300c0d203240071030081c641c00a00340e80e410b18400c00e045501d0384519000c0200e1074100040f04610b0800810021114010a4030b2006401c2405034110759008001d903a5010004100354800800307130340301070002c65042c0e44000550000f000791180684114054001d0b000b01d0070302035141180c036440d0611054807103e01d018a824075030844070100510350a00d024100b0001001c02031010405d54008200350781d00700068031b10641106080c0410345026a4841d251038100300d181d0b51050002035401c0f111044d9203d6000254400c0710703080b030203c41400c2507200c0180c005107001c0c8030038801002a0340c014590a040b00f851803500864800031401b481d4951001d150440007100e0555842c280c4500d42e01403c0c400f503a04011514074040d540b101e911058030883c0341040c82e01e003002d01d845401e903013140c099403040d4202940c0e64803c2082d00d410b4180307100c0c10b02501500da810380c4044d80c03030300d884c07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 608153525 1250 608152275 608152277
    0xf09040602180d02101b0b0a150603090f1205130b0304060b0d030c12090e1503010f0b0306130c0b0412030216063c05090a080106030b0c0705010605060406 68
    0x180d1020100004001e44010609140c0561920490b910050701e40c00000901c4080c2481c018071b01010340c0801180071411040f003c0d00846010080c0603004440c0c0e44070500c001c0e41d4a031076071460395644134164291242c40a0140c945141c0322090804144c11201780c6603503041601d48541391841c100702040780e5030313003503003103400c2140c4003204001c07c000c8540714144004000f1651034203480800d680c01080324003401c10090002c03110141c4840414014280c45c0e0207080c03400040000c61904002030300103500c290a40a20941c02c10318880c0c845265441000c40c090405809003e040d40c0d551040240c01c0305004017141d10b24204c190006440c2120400b0380007400e4104100a80c1c040d0328107009180c8a441d01070302c424500006001c002c03032501300e14541d012040c02d2001c33102418880c0303448400820b40c0b4040300c03e900e84188900c0d030480e6000c4014968000e04903402010b00d520350010034200c0e2a9030000500041c201c1c1c1c04180b040b070564000e040041c0c8a20008260140c4a4001c00d2135600b00da0300100c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 608154775 1250 608153525 608153527
    0x30608070306150503060f0a0e030904050c0307020105221b05060f0a020c012a14011a0109150e2209081804090804170a0b090303041703010f090b0f09040602 69
    0xf80c28441c0403007401000740012001040c15090400078807002d580301170608907400b5910580321001030001e009039208458014810441850040d10052840c2c1c01181c58400552070a000206041d0403040c8040807544010402512902e850303440c0c0c551494a0541d503441c00c068640d00240544d034000042c1007520040840c0c5449400507400a07150031001c8011605015040c07484507a202c002030306140380c265101c94402c25441041c00c0c00e1a8441201281722803a50902d500200d100381c50710300f035010541080e0b032940e40e0242c0d103842000254240c82c500308001064159112a54940045124920903c144141250110030b83da008126000c00c042150007400200c2c40c0032001407203000f02050b480d001c1d58284403000c4c070365990040c140724a008034800c03560040d2030881403280c10021803038420340c0000341555a04042004a5683c0c0049400710395003100c9508103500071009005030f90481d901028000700307207400d1060120103440c10350000c50700400841891012075aa00008500540c001c2c1801 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 608156025 1250 608154775 608154791
    0x2d0309050a03020d391b030b180a1104050403120f0506100302120604020a0c06020f04030605072a030507230f07030b0105060702061603030b040615120903030608070306 74
    0x103402940e82105040401181003110380052003d003281700500031207480c80c4c0341c400500f86040e4818124543d28aa218081c0c1c50780841001070f00b0711410b001c0c3c1a400c0c080d210074070304202c0c0700340c4d80c2c44d4015004103035011140440c00303036003401e4000b50382140c0710b42003d8200202c500300035004c55101444000325661981c0c2841030038182100c0090b03044519240c2940303000d40b881a0755003d0000070301704502850b800144150010311070800d40e201203611001c159515000c51340e0281c2c1c940c0150000b074403502d107050003203079003035001d0f034402c69a21117403814900c0700001c00042c0c80d9010348035002c15130070300100b00081c1002442041052000c1000000c210701902445268189060032511f2043d90759406040309201140001e000c2c1811102e0407160300da9030b81090b1010a40d14004c001c103094000504030040000c054154020a258450a480400520f6580ca80c0c05c3c11004160280c0d0f80441c40110700f2450407000368000c81c5d080c81c040d040110b0703e03580c2d90110500d481442e510030386045070b445100d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 608157275 1250 608156025 608156027
    0x20a2f150415021c09050108191503080316050427090c060f48050316212a020a0b04050102060c030c0301150216090207060b012d0309050a03020d 64
    0x40608a09005d10b0001026401d042c00600750740780103442a81e20241c02028415044203540254008002243e2500801940e83c5015040e40d0025164880c00b040c3d941c803030b81102840f030b1080e00c08540090b42e0403502d81010407003010244d60341904901180da00c50f031590000c110003684060007005a9540c0075031041d10b1101c018842030100e2540c01002d0100d00030f11002c01904803000d003000025144c0200001c83c03001d40100040f800c250004c145002c0030500d41d60075415036081d8440c2a00411404526405480d03140418001c9440c1001c003140412292440030420108800b03000c8940d0740a88a8090450b00000d086865a0380701110380e110004050200d541d0502245420641d110f100509605140c00c00485074001401100000040010040d00d1a0320800010303450a2201c811110317110388481030303c00070b91b11030b640c00e8800f142044a00f414035403007078400130146642014681544c1d50501903144084e80f8502c884010945c482c1042004140c05003c4080c3c624801c4e0001d00c41441d950b80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 608158525 1250 608157275 608157313
    0x20402030c0408011b021015080a0302060615070506010b03060f1801061206210c0b0d0603030e0f0901091d07120203190f020402030c0c0a03020a2f15041502 69
    0x141c04900c0b11030401034a4501c540007d20b41112070380700c440100b03245101c3d0000b2000c50240340d02c050707a0740c4500b180e401c05240e008664540640d1090301d40c0c1c1000c00301964800090320408000601607070140c0c0040101d402181c0281d50401d0000b0100d0b0001c4c40d45c07100080c440c0603100c840c0c2e0752200e0f0000040040541040e1a800c4039902c3c018184205450310407420100880c420201c3d081c00f2009070301c003080111244410010b0484c1003495038842c4243d01202c80200800e000440c0490b542d15441401031928515070b4040080040c1001e50036030030164044050842245080d0040460111840720524144400800b60800c29802c020b41407031401054035000c0c134492100101c5072200300990200c1e40100410500c1c80c1c06a40140c0c6d20307210485045454807501001407003030300410700f12808256000c901c2e24500b03400f82c804240026240d810fa01ca03100740c00f010aa43c21401001102c00754208100080220384000c00354174105503035840e251065444580001c001600700e05d444410031079070707a4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 608159775 1250 608158525 608158541
    0x7111c0e010e0a05040f141503160e070f260406050a0506011707020a0b0103150609020901020a15150b04150f080403080406060302031c080c1905070c03020402030c040801 75
    0x1180507110301c210700b0b012400000300790141d60300482d21405801010700c070581107054445482e802240032854140d40301c100800c4500d9045100c1e000b042e101d207090701945c00403a82510110000e41c001034981407015591000c140c2100400d000c4501d100301e003011451381100d61174003d2202c034a400d620b854504001100c3d0010600c3c10342c54600801c1c00701ca0f9910021040a03180349048803a0907854011007645000c0340800000e100324090b00000c0200440300d084420346000c03e100030f0210640340c020302d40070ba005004d0782c18010b0b0300c00250340003ca0040c0b45100310500392550002130313082132284030503200b500d1504448001c0e00d0018003049940c8040b15015810b0b4030918144a418144a000034605a80500301a0410074814046414406150b2180b802558020102da6803d48504003021005240400308808900c5017000a10040d903400e045406609080016410694a0a6044e1000d40120a041c0c0f500701480314003000503125803000b980140d0f400c0c5d8601d80c945150140c400e080d91051 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 608161025 1250 608159775 608159777
    0x7080102131d0708040f020a03080702010206060f0306072d0e030712080f0d23060102070509040f020d051203010f1a090a0e09150a05071106160807111c0e01 69
    0x10204100302c1d0000c40300503822200d5468990b959444034109401c900040082c00303980804082c01c00010801e1007801460018401e8013503e4540d40e480701001200c034289080143c06411100000380414411040d0411200104d034500060100100c07440301c410100304010004200e80da201c8038401e20301041441b0041808040841c0604034030354502d2100d0152840c1111040b4001c40d03000942041030300102041403c00c10103030b0031661411901d0348070300d20036520280075000303180010078141014200300307102d40c2d0000f00300420b103000d0b5400c0c001d0b0700d282b4207026101c50003640c440e06102911080250300030301d44410407131031043c2001403085088084400081343d10303404014100f41910f0b2140314100311100d11300061840e6443c01c12640c2000b0b20b0481540c1c150404108100f5810303402c1e40302501442180d9100020f66032010030156894000307643d4584a02582c4008552540c450034410381d0140081c507002d0003c0e2848980e06141281800ba04c16040e2002102e00c007c60794805040c0b40c032501c0c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 608162275 1250 608161025 608161049
    0x30c030a0c06030b0d02030a1a010803040501080f0702280303050115021c020f250b041a0a0212030a021b03090d060b044709010e040f02030708010213 66
    0x5545100001d44907119507024141c43d1080c90341d656a0369110071038002e4024060b9105065a46081404100e8016181e460016000c001048194000045d01c1c00d40300f042e182d8006a03205d03401201032080c40204001c0840c45440318180f2010b030b40003101034442c0703085031075181099203615014040d9081600859078140c103240e00307660059400941d802c5070f00b602d011403203101c508075401241880c0300003180284e18803078440c04512100031031040d42030b00103043d02d10015807912005101c5062040384148034000005040345454880b945001308104543c500441d0401901000c3da0307a5a41c0003140c00e090f10b5540481c1c0340703c00d000b4102c841d9902090700e1020b10300d003185810000e8130150038003102030511a07481a158001d41ca8983c860702c030301c4280c1d00207070030708000d130140c2d1086140f11b03443d500000e044c0448820441e40e04d0b02900700e101a10003031411900d80e0900742d0b11800ca4500400603240e801c16501d108000d61400d1242c54041c100c0307440003682e01c108022014000034181e80c0301000d1074038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 608163525 1250 608162275 608162293
    0x408100203060a1401030609020c0a03030b06040b092b0f021002060405031e040f081e01020a0e090405010209040f0204231e0307080319170402030d12020d0f0506030c03 74
    0xd10b4003542d001340c484100705074001e02160310048000f4001604280c0407140f0009018002140008010081074420384d01484000c0014052001b140214030400090903002d0002c01098a48000800701900003c17503100c0340f941e000e403d142c0f21034a1550065404082d142e04100c07e50401480800080025000400c498141a500c4030b0740d074440d03888103542c1001450b140b40100301500c3c00300c40040510080808130305448144154a03446554148801502c180074841440c40040c002d803541078040e40c5482c42c1d0340d03001c0000d00014400007082150595800c000340209030380c0302d100f0000480c0b400c0400584550520020200109443c00000d40303859001848486a90302c0e00c51010060309030b2201d01c03c0444c1400302203441c1902913040040755000c08646183e1003404401a0740005015a03039201e0345020091840402c0e410540e03010f50190001c4803103241d22401140104031502c4d4020006180a5401509100300c46200f40408a51a21401070003014601008032810f680c1085002c1c0868030303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 608164775 1250 608163525 608163529
    0x6060314040f020402090301060317040608070f3c03050a0c021b1903020904050f10110904110f04080a331104090203040311011b140d090203070605040810020306 71
    0x40c80342c442c024440c90700003030040c4198800f0342192008550042100402c0d808030070100486400a000300740c005455800001d0300b09208035844c0101203480e403600307444131030001058140301d98440f21400501c0601c90080fa400c010a01c186040309045079000a618240620208166000800e0782c1c021903021241034446c149020612004034a400ca40e81d09841039071400d0000050404c0d48042e40c030000440400042c01004904184000001c0d410350f1650400c08004904442a080c0e0644e000311003401482c4103070410b07901c10080c8900410b02c150400f0101e200c107071080d5009411540164002110130340400006003031020301d140c107010300007140c08071600c00840c204800c034405841c465114055603800e0400c0008a4014082d00f4100303540d46d29180c2400703000032080340f4000030306601e0400c00402d040c20410a4500d080015030364160740d2255100f20524642041040f0103400d5902c0400d1001664100120002000d03180c48440d190341ca000125420f10303d03104c0482c0c114500410800400b5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 608166025 1250 608164775 608164793
    0x30711031c1e050c0a020f01060e060d150c020c0415050105071707020907090320011d0f0a09061508370c0221040e0a051e04060606031404 61
    0x68902031400041c0211010114910481214590b0701c405241074213001403905110010138407002a9001c54000622203441a822154144a40c0240d050080049600c61030700401141101d030082c2403194000c0500c004c008100d03403043c60382c080580c0c8000c0380c1600038200350280c030b60ba19000c030ba1541080d0f860400064500e20034101c00400c100260010500751a0000040d10200354014168038024540b952018165003824003059803200442c081c5640c0d800c0c1d04280780003c070388060f9034904a2050311401e08241d041c10000007980b00035031310440546500d503000050001c00e2081400f03d8100d12300380748425441c40c405566400c0125650400103d804840003d000a0101080d13449200111808011090740030884403e4140c1c240310f84815150f50005841c0f2031251003400d5040080d401e110640f08a00c100d1007012050800000015071200c12540300070b600c101302d00f11851030301c58540104148440115402c41b200c907682c0c9401e006032079140c4200f0361002c803458000c000d1800c15440380d14030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 608167275 1250 608166025 608166067
    0x180d080c090607080403051213080d020c060a0903050a06020d0b03030c0a0803040215120a0b0d0c170a020d050d0e0d0206071b05040f0b040506010f0c17040314010203071103 76
    0x242a00040090400401c03101715030055400c202030b5450428041c0a101c1c0951151500c203071820a03005020503050004241c4881d4410f151f0001c04405c5031000603c80b9a030071035000842402109100000418000e00040c41158810240180d680070448030440855030403506e114020380c824048885243d4001a00740c416540003030b034050b245c1c2d0304d520004401c01c1100491490550000c07603004002020302007594003900e031800060250984901c01e0160f28407116001808085070b020042104001c03250444a01c201c4040581e4a01e1035182c010460307240310f0750790450343d903800190305050b05503100c82042c03080b800032680d51840440c6500000c809016040703001e82284034160103c1d1101e103c4910500c010030f00503005200b4610724803500d9005084034555240160700f400c0001d503466103e060507040079281074483d110345d04241d4455000d00000c2d80c905d0b000c0340d00100f20100108d00340d08012103004402d1400566a0310309040014807182030013054000c03580c0180000c10021051424040c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 608168525 1250 608167275 608167279
    0x1302010804030c05030f07080d0b1c0b040804150c0605010e1303030e0c04060609140a05030a031215122901050f01031e060303090e01211109180d080c09 67
    0x4820f03810303400c115055224400541440242c00034061082102d0b4501402142d0584102004500c0c40031081c000c80d04d040a80010581c26500b0407140000c116000300c0d90064001e101042c1001c0d143c500d011406446c0020303d00114040340c50250401842e4062070307000d0812200c0c1c103255400d0130f00e0150481628020011b00303040e2a040d080800c200100030304032888400600c1841196901c08000d088000c0f14000c6505040c1452040f15450810080c040f00b107400140050086042e5610100c40c072082039200d100c1010340310b4643d030502690044850000e440403010344802c0b040e841c075007242d42c14a02840c00c050505040180074005100c4c01d03101c1d046820907260f80180a004500480042071424401803480080380c0c0791a5990002e58400c0c01030781e1094490035015900d038059040e485000344154a07842070041c2c20a80341c0400b14210402c00c500c01e0312580b00e448034000020340503031000c5440c884e00071420030700445003c0007001070705000c0d681d03810105058140342c02408021f02c10180700078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 608169775 1250 608168525 608168537
    0xe07110d0c0f0b0f091504080a0e01021e01060612180b0c07050604061505330c0f0d030b0d0309122d020f01030203061c0602040512060609130201080403 67
    0x1041c0040d102101d0075070396000304950f41524028a45500002c01a030300c03014144942807400303840007030b00304005005039009001107041c2081503070100d4403440750214050450103034049862240d002d030003000d00c058072604008128981007660052022941c100c240c1c072039900b089420701401141107600080b040d00040303401c4a96489003241103030f41c800c00d40010281d201d0142000148040d960003403007c0320040340c1c00c80c482541c0d0010800c0184504010b070030307902000c1402420394151041051301082050340300d07a08140c1c101e1002800c1051035540c4601941180d0790400e9495494494140200340c100d9009041001c551001003298980d40584c24060040c00b607104144410010361421000320031040607802c0030000c0d00c111300c06001d0407003240686050b00f0030f111158040d009881c41414043c095441d0001098681c840641c80e03044185d8145500300700c00708468a6030301c1e4003118125200004d2107103082c00418050270441c004d024001c0300022060b0100180e91098a6070b800541500d810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 608171025 1250 608169775 608169797
    0x21605060711012f16081209130f0c090e0c0a050309151e01090227040e0601080318030c0303030105010522060801030210021b1003060e0406060e07110d 67
    0x6844c0c01e05507035058540c080000d503c00c40d80c00104810301c92020b803414295a0210310f00c004d45048840c1c3e5000340b21003504000f1917145603c200002400c6401030091072020011131050301e00d0201d5502420411746c03280c5079001290555045100f1000034801102a2400c07494100c0702c0440e28003940503024104180040402c1c40408100040e81808148000c1e0301180d0800c041034081003100e40c00e030b044070280c0503400011882d210b8401d40396190711440d0150f010300710349194000c0c0c080c104003186503c21ba86840c4c0143c4542d0030890503000e89405801150740708040080c800c014000c064040d031280c1c0c400b02c0720707810035107012003940d045403000c3c01c00b81d403160020120314060340b407204001c00c01c1401112001032030075444050740e412a8000c1d150141d041c101d01130101d0712224840d1411116840d02c0609504604103071540e4040d014040c07800040345d0b034440e01d580300e040b807098030305448041c0c4480c024800c44090019103034002c40c090804c00d5412500307440d102d458058071500d071800c1c08208088 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 608172275 1250 608171025 608171027
    0x10803040501050c030d1d072718060615120615051e07060c080916030210110609010501080f0607300207060c1e0c0209100f080c0102160506071101 65
    0x68922044400c00248841c01a41902e0b80010074287e40340e00c4071740300e1144001070b074a01148140c00048001044042c012183c141040003800200c0c1a0650547c44e900316100030801074030a12001d008050381c10004d664280704000c151520704128902e41c203140100400800e1a11072010744462000c1c00d0244d11444201c000148001e8014a51101121300044000070010213510100b4015025184d0110580b511f10304155600500202c550050200b01c80620242c68103c91000103010075150240301840c11048c05410184291017888950b910741d0014404980705000203500c0380b01c0c1c0b0004050510b401140107100c441580414034480110440d04501e807200409206451442c8400542d6a5100c1d4134291004205148800000030f00885100081c1c602000c800f41c1740f40c81c156030702c8000700345a80030014403010107401d80042010a400000f2840b841364030102c001e0503400f01a09110000c03500290030140c1404d41000ca8070080707003041c4000d940d0642614202500005007010030f016000c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 608173525 1250 608172275 608172277
    0x712020a0206071a0f06030316021908070f09050c0406080c090607030513050f0d0305030c16030504091a0d0f03020a020915180603280b10061106010803040501050c03 73
    0x50041c0d0031803000034080c3d040c41070308800b03030070781c0030f0003215107143c41e5180d03500314039600c0741035910540c19041000409150b020841444c10a503000508035082108410449c5080e08050741c85a000e90b0001e900c10409040e6907441c0380d000b090908824000c1d864000c0b01812144078a01800c0f0a111a500c0031507004007000b002d494003c0380280c40c0f5a0340740d0280c20050503030341101c0e0100c0706000720888045054101042c0210060001074040c81551100d03540036507207030304010243ca0050f20280480c0080c1100c503840301d0481406030300c6840d81c0da81403c000c0c1c41940c080c40c0c400a04002598042e90003034940f40c01c40200d00d40c102d00b481a28210710300d800c07410180c01c002c0103980062582c0c18071080c800180410604400708662240d0464004032101c0d54203c42141c13440d0f0f254000c80c3d000c13501514101d168585484a41c0703d82c000c46802680e6520804034151114400c0f03100c83c050a0004540049440694a40308402481d20350314000c201c0da50303842603020b010b040241c0480d0220380303150100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 608174775 1250 608173525 608173543
    0x20109150203040b0409020316090f0b070201170c04181811060d1119030b030607080613091a090606090613020c010207152f130302031b040606050906071202 69
    0x1050142d955a46c031001c404c06500152611010340c0b00032100003007001d0061080c8000ca5000c02039090945142510701e1400b50000b11069052080015186030611081c1c4081403158908500c01500e8500307180d0850b100301a00a01501d6440c50051a000041480500b5042032a0f11483e140c2c110090600414202c0c059180c209074500d05240d402140142000040d01041e44821042c00f0007602d0000d045082d241510780d03aa4050f0095030210b024607214280150b88884050a200300400d20301078480212050034000744d8445080303804c1c0d001d08540e107500840d000140303130b4014103036400c2180000340001000750200740b180ba08080e510201c84055015250b4510b42c020007103481e0001420051101a0782c01101c0840c5441c0141c500d840c03200c01200132400000b41e804c40807406402050790100d0f603009184003150082174010010041c1d0b42001000c48003d150031204507075003003100601050381e2460308001c062100034012030846885240c10385105075084405042681142101641400c5101c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 608176025 1250 608174775 608174789
    0x1050f07290f0601020d03061a030402030c1215010e0103030806040b010e03250b130303030e01200910030c141303050a030203120603060c04090f0f022a0a02010915020304 75
    0x100301008510849801c0140c4a454280c003030f941c1b05000f02c041241107500d14095100c030079100c08103058000c000000030790360091000c3c040760112810900082e040102d6442030806a50040d456150b95001d195455801800c0214101d0003030b504540e0090300e003820062a01b80110307924404440168455085407400681c060240c4219202c1d074042c400341042c01043c060511150b55000042c2d20003034070100c03180c10202c1036210b4072803419503038110003828554100b070f452507480754910605054a0940c1d030301030221b944204c07a9214040001d00504c010300c04d01e4038080c5494080d55103160350b00000d21100303103500100800d0782c82c50714140852900c5150f0700083c01910980f01c00d1000c03d034000004022004442c00c405010b070390345008143d65180700b281c6e0802603400900c0100400ca8680d04001caa902784414040340903040d9040321012a08020343c2440340314050f1105c00409001030000440c8412003e0280c0f40c240c00700c2c2c0028140041c5032040c0c1110841007152006414424402c0e0b401401c05 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 608177275 1250 608176025 608176103
    0x1d062109070e090303060d24020412110906010504060c06232a09040f02091e100201051509060a03080708040303090e09070b0d0e031b060601050f07 65
    0x1036055690315641c500406502c4203006020940611000081d60302c1000c0042407001d0318500c2c1d6a0700104000d40348259400300c54a041c1807807104d20140040e0018002d00007006440400d81e04050540b4804160098000c9614070140070403640d2010803901581c001e4100311401c0321003881c160b002440b00b514040c0e43c032203810350440b0322016440a198080c03403052034401010410040003d01741d98880c44001d000300020803046030142000d8020800d03203500c2e0180103003044650400b1a8207034014014446000d03464182c039808620b0030155003c1004e801e44007c120a03d04440c1a03030550003000c5801c0d200d41c00010008041c0d03951550300c8009075502048054450149240015954110f8001140410781484020640606040c0301d103104500300d00042110f00d18290030f2148035030240746402c4409454800300c40003004100b00808003984801e00c0c000c50316649489640c140170025000034100310b0100710100300c144600081e00d2459400001c0c19141140d42c568040800408512403480f50305 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 608178525 1250 608177275 608177281
    0xe0f0904124d2e0f05040f0c091a19031b0e0f0705030601110f0708060a0c0201090804180f050c07172515090b07020d1d0621 55
    0x10454040e075031414500850000600d94a4038954540e1480070501c4503144410100401c007010281d5010940402100b0000c0d0000102400001741c850441c0d05882c80c41e0000c01d22010450754030780c52002019421000c110000d200c042e40e01c4651041c00303071203125003031502124001c074928001d054011a1b01c20550b03189030103011248000352446200d00d030908070303e0b140010070001c24100480c1c8100d4a550301c01c3e24507611200150b417482c0321802e40419500c504414a205500b0800005011301408401070155203030a07400a001d803010104002d04590409000800289000041d80c080c0d80d0030305034003000e000d102c0b5110300043c8104940f681a00782071500f40140d15400100130305142d1b001d110900c401803101502c004441c40b854540002c00c0381d010440209a141001c0c1d01c501043c400d0106894494038159600c00350b550000c01640e203d0040800c0c03105603074040150030f400307019a0801c80c080c00a01565262900c9415411034080d090000c0c0c040c0d0324000c4032000e0300020901e1072105000d41 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 608179775 1250 608178525 608178617
    0x80607090906060f1403041b0b0702030f190221010f020a030b0a23011101020a050901090f23010e0a080708010b040e07030f03050d0c0e0f090412 64
    0x110544104450140341c030034003140c0f0501c202c541290040b11600c82d50f909440c035107503402469000910549500740141c0b07900f905134400860140080001c070500c2611250180105402e181024081d5240c0750b00c494a080003076a90048104201d503011151044080d4450080703145110402001c6070b5a540390685c4140014040d6000c1d00018045540801c114078455007444403e501d07900501d9a00b10144e039900e8030580c05209441810072040c90046c0c40d00399440001c50a90300300c04902e00100341c02052400c600d5030b20020000003000007000002c0a545031002c10804000c042d0309a001d503090844607030909074080c9070407980002016103104240e035030301c0507241c0c5c88002c00d000354000c9500f4455001c0c06450207009444542c1241005041014a03680d03130183e02842e0200704405110b4180000c00000509101b019038034072103911403c801c0801c420811004203440d210440c4540054028400810002c10081c84491041d080041c0395000c044080710054043c0982010306c05c0d10664120031031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 608181025 1250 608179775 608179787
    0xd0210120903201605060d02040f030c090e07150302070c051201060f080c060d0902041e020a030c110303060d050f011109120a0210080a0b0402030901090b060306012d080607 76
    0x43c0c01e43c0721107000c8480e01d0401c46480e8404001000c103074842144013803200b441c100c001801c040d96910401490142d80d030000c40d200381c0e541c0d402510300c0c400002040000341c0c168000c41d4083e44414014014090500c2070600c0c9110661213001304041c1c2c080780b4442000200c040c00d05c060070707005019130b1900d81200700713543c0030b0300b242c0c02a08450400641c00041030079000640082c071940040a0604001f4004802c100810b034442d0f0a03a4007686501c0e550001300c0795507412009001000300f000d40e80c0d180b03201c409410349060380350110230006000030603064404088103880c1c010000712088141d031011414003c1c9851028003402049518142680381040c1c00d1a009140020003561005261140303101c80c592544900343c0007030b4110008002443c0f17524070840c0ca41ea0700403402c1900060850580780030804070380040324010340702d0b9501c004840601407185c0616500100407002009190304101c0d00d8182c3da0005c0094501c107858960068600a404003070b05400740c45500111080752030515002015 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 608182275 1250 608181025 608181047
    0x702121804090b06011205070f0309080d021b060705070b061009090e0c1c03081b04080703150b090114011b150c17040b071d090a150b090d0210120903 66
    0x1054880d48918070048947c040c2c0e80c0300b1a450748810042170800242a00a026a070104075500c10040149020029151014200c2c00c24041f41052140f0106000301e450114044c0050003489024811600010b9801d140a60711580a58070340340f990b055290180c80304a03041c1c00061440741040301c0d11407440000550314015500844294203005540204518440040e170000780c0000d04400000341c100249a428029040761605c43c249065941d0709401d0030b12180360011500d80b405000491001d9955001c0c4103040e071412281c0021951401201d5040d00794001d200b6414842035540c50503d58501200c4078142a0300281c0d07002c0d07081e001da807001004001100c5610085141608040840740e9044401c0e0711079030b0700210200072500c0c0c61400380e44100b5808910310801216a41e5216251525041d060180340c88070001700345209140c1c0361100c9410690001401c4072000e00500700c00ea51655540018503030141c403030908400c9528411900507900e540c020505030700301400704082541c07000b800740d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 608183525 1250 608182275 608182277
    0xb120d051801080f04080702180906040b01060810050f0604030b13030314100e15120c03011a010e0d03030908030c07021905091803040f080304030203010f050702121804090b0601 78
    0x2500c50200780043d1034030042039450b080b041e1450400100041c00c10300081211500040100c0e0850901e60101507003c0c0046550000d0f54001400b4001004081400360703016000c1e0f4101000c003444c2145014000341c0e02c6201d4640303d5080d0740c00712941d81d103074042183d01440d0400300300c200c0c0d490035225003034080210348402c0300080c0c54000b42400000030055030500910180b06104155440c3c01c4c00d5002d2440060542105c03140c3c00380c3c00c40c1555441d65040424500000c01502c40201440109802c41d4407040310100740c840c4241c1c1c44401d03070780e12079100c60071044101e811403182a461306003180100848400100400320000c1846815020540034009807482110344540101c10a5160400d001091241981103040100440c003c50a0200305c1e149040c081001c0f2410a0b5a0b04d002e00903a00b1260300c403007801d402c0002c0c140154103081c003c5001046001906100310f003801d4100075543c103800c4031022284240412000d6042131069108a02410018018000709105050650614405445c414 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 608184775 1250 608183525 608183557
    0x708130503030304081801050d0c081006020708031209010f1d0705010c0f03080910050a090c0e31060c03052508060103090c03020409080c0706210b120d05 68
    0x40e09240000483e4881c9610414090400d144134400e03520684001c14140d05205050205043c0da096602c05e408280a8a41d501304032410140b04040f603075542e40e048401150003001c0203120054000007203c07010503020482c9500341d9202c1c04a68014541e100b00308131028203107003603965041c0c041c00a030004c000c200d41c01d85002d1a40c5100640d440a1900030041008410300302190100b03010b034241580c0310031600c00340c40807101c00d10700d204202e4008590102085660310300d001d050180d4400c0200262084040380042c6041024045071450806030815039010000c0d440085810720384800a410503034802d82c240400c90380d101c80035000d00800c481c08888001e01119400e0ba900000503881c070051901d4440708070390b4882c480114094620301c9000c2d522440303120000001070301e59105007032420340a00003035902d80d549440302504000c003680c4460100400ea84203041080c50711046001091351078000010b0114189020a2001d50322400075103650040d0549000303030f5038000b0002c0076100580e003802 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 608186025 1250 608184775 608184779
    0x60e0607050406140f0d061511010b0a2c04080901030e0c01141b33070206060906040608061326041a0f030702160f0b0306010f14070813 60
    0x4698a000b54810301000444600c94881d0f55500d04000b071a0104100810b685440046040300c0b0503a15194404407428111000100720590700009a1012481c07000090000d10b07440c00c009501903406000e440e4042c010b0440b4005030030041e5014560101c070720f41e03030214a4540381c00d0000032504000d07030640c00700341801000880d0400201d01002540341c161180c203548000c4681c6103207076420030042c0c9155403215081e0032509000401030701007000380d80c0e44110300b03882c00100038031580681200b070302003100c0121042c010350f13079004100f2980c081c5040e6143c58140d42c91030006400b900c0980e000a4a5001d80c00500185840c10501c00c14020b001d28491a20001c0c402e0300c1d1a841d02460385e01701d0350300d44c0500050280658a0b14090040c1c1040c00c5024144440c40c00c41c00303110352040e5003150240e401150200042500030700c0940060031404100918149858624032061000804845c10402400052104503006121000030070503e108805c0c1ca40c000c5d0f1400a0695125019080242c8680100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 608187275 1250 608186025 608186027
    0x5040507050405130b031617070e0105130e010908121608070f030905010204050a0e041a04172206020f120306030a080a110102030a0f0b0906010503070f0c080403060e0607 75
    0x102d9040310350242c00301041d00d4103110310f40c00401021541d294580282041d45160204c5400c1c28809851004602c00304060b41c0c0d24158500442c3d540401510304521380100425550140b5042400300d00c1d0300041210301e11403101d0390041030703600c1c00240003840c00b0622030541c8182a40c205d12600c0d000c1d440c03650b411401c0350141c1d0014012a880400100160840c01106200c6d40010000a110f540054102a15513000800444598100120140c0340204000c02e002684032090480110716201800c181029220071098008012020040380000668103603202d0380c01c2c1d6024040e5084840003500b55880c0d0360002c1d11045a03440404162081d4145072000c050703010112402140010010b00b004a99a620070386a50803240c131040c140520507080400c10b00d02800114030403207600400060340701d1010b00a104450201c010305008916400402801e660000304803a046103890a18000d02c01d9003110032121070039146801032080801050010403c2440e400c203402841c984000e8401c03641d10076030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 608188525 1250 608187275 608187277
    0x2060d0213262802030a060c05091f14070206070501150503010c11071724010302210c01050c030705070b0d050603061501053406060b040e0402040c030e0f070504050705 74
    0x100e24540505010310034003142d4540c01d030b100c1d103051024080e11101000b9440d0f84003100d04588c1180003141000400c0140341c81c08182010b206000501000d00e41000070320028002e102080c040d030704540d00080c00800b0365540e0401d454080742c3c09802030000301500700c604d490319030880c402c1ba4003135800d108505110398020025010180e00c000c00401c8518584800104c1c0c509690900e1000c3d400b40105500381b1a6540c4070b200441d0008c3e403d80300c420f525500c1400075400c000e0f920031980300d03441000c000c0401004a29175925600920708a62242e031260540390943c0315000005100d880740710000101c00c0e41e0383c0c001d0070010058003c1080699514028561507003003c40d003101d11907003010103400d595805031016040c80009180300787d01641441503003090018030381d02030000c0c05c804a10b2210801c5450302401020b04038a00f40c0c141881c0c44c0c154400300c00c030406040240701e40d85455044c00001d12039403048030b101300038070202c07082070341410f202c0c40c0c03207010b9401500c4c0520304050001d10f1450080c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 608189775 1250 608188525 608188543
    0x102111041e06080c0d11040504020f0a03030c030f03020708180a080a0b010509100b0a050c150106050702130605060429030f10060807080a0c02071503020d0b040e0a02060d021326 78
    0x70040f210259a00800c007c02407000070400c030b030700100c0d145ca40000b0391a2181d840010714400d17204c1544a44e000d0602030124030020000d0340030507004000f1070f000200c03050180e4550807900d8400c4c190b62988640041c20a0489130442c1c5c9092041c0d401c1034050007c0880c0d01030407248151445090340d02c0d100a1442040d6190141403101a01048038903000c9215000a15000100c4003e4503420039400300040b11020081e4400c01c0040c034041011020741c45c15005400070f01845d40f43c100070755880c1002041050156100754102107000b80c00c0e40e8001d400c1c20f1082d0500c00a0624019a20703e00300940070038801090303802018562110704041100c07402102030b03500804442c3c0301c07004103540e1005000060444004024210300506400044a1346800c4226071030f900c580d1000b5840303004982000e0112002c984495100340d0401031300c00e01e0b014020038040c02550301900c91555898600c12000f02170703c90a104403c41000a00c80002d00d03c015034940407003040440c2e929201c1010042400c0e0f44d85205d070b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 608191025 1250 608189775 608189783
    0x6030a030509092503020a0e0301052e150309030207060302040b04140303070b041424010504150f06030207020108010801020703210e0f0105102111041e06080c0d 71
    0x3008003060a1504500950307110144922040c3d0101e904401c0001341c544d001a20740200b6000301ea1185800e401904010b101141034000304980d251851480080c0308031404e4100c1c0c0100d03071500211161029281003006000d550003410200703854494005d00600c0202d80683c01405540404103010340300b80200d50845007101c002504281c20210384031070005460381200e070b240c4020040d020000d0740c40e0b035582d44114011141c6108003800001403a092424411390f00c610b0015050643d104030204541980c15a2020780c0d0005d403400f40411543c03030060f0260440740000580d5400000c50913416002052101c0c401c0c0d0791031881d41d81e140002400d0f400344100082c003085440d400e0746a04010f140c851034165103080004505034454605a606000756119802d0150b51a8810001c08032181150007000304042100d041c58811060480c03c80f51101807402015000c03606000c090550307450700095002e044040741c04480f040c00380c2c0a130b401054140b040d1002c600132410088214a406441c2004103604 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 608192275 1250 608191025 608191027
    0xe07051c08040e060f03060f01090f020a020a0b060307051c0302100608060a090624080118080a120b3304060c0f0218191b0c0f1a070203040e06030a0305 67
    0x304000640c1003d001080729412101624130900996810480d00f8090080c40c58083c4031941000c0440059680e903040d080303e20744c010019046103581c0040c407020300319003100c0d02d40d40c59251100000d0a2418a5000e15880781285907407000008aa40004c01340310310070740071154601051410f02c02aa08203109600c0131b50020800941c080d0415048124482e1044500045203610f100089405d402c40744058035130590414003c0c45540b6003445204a02c0300c14603000d04103ca260b590301051071244d0b000700010440503071050b40310f1540303940000d44420402407900306401c00d08401e400b0070070f4190f840b000100e00c882e07403030202884c00c1c1800c40b01511510b9a9503403403501141c44510000103544030403600443f2041c4c4c035085220205080714000c1d2111207501d0846044007682405031590180d00da17140c2821441c044e02080d4200701200350710769201075400c1c0c0c0c054081c14100c2d114121211407031440c1110604009803550b010004205482c0011018106038403000d007450750b01c181c110801070100344 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 608193525 1250 608192275 608192279
    0xc0d050f130807141207032d0c0f020406140f180601032d09120e06090405090c0907030605010207080c210f030a05030f070c1101031e0e07051c0804 65
    0xe0094001c04006000e1103010041e1080910703040c4c6040452000c02600d82e40100703c0004142e80903000d06d004c0d004100c1223038008103200042e124500d9200003000c0030300c9108168a0100020036481c0d41e100b58000b0400c009039541c8030030303290001ca040e094043c0702d4a14802400c01a10f881d594584d41c510700f03d81620303400d5450b14015401840b00c0046410400003084c000052030031802d200121801900d40e0107d0340031100e01e08200003442d0200c0d0300b800e03c02c0600c0e0010b1140c0303e007001e0381c8034208100e1f000700d01900e4503038a950400e041c01d100c054112180001700410107826403c03134412070f242a400c860920741e413650840c1e1204880308001d94001800048100701001c250307829500c0c0040e40062741d580310450183c0303d02c1c681c000e4044202252001c01040040d043c40901c41c0c2d801142c0b41410306040b045c6554000c21403a244246c2410305640368010300d010100002001107002000c10100020210a4000c69031400d0030f10406205024920303842c64105520541540d0490780009054140343c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 608194775 1250 608193525 608193533
    0xb03150106030b060408011104060f36080303270307050627190309090e0a2a17071d04030305061c1b0506040506040b0f040e0c0d050f13 60
    0x1c400f9008007980f260041c003002c00c40d95001e10442081904d010041503076186001c2028089940311082802481502d02603031085810203070240e1203069251400081c0c02000c88001c0075541e036070b504420000e120100800c1a00c1c0d00c01c000c5100c42414400c52085102041c004042d039910070264010a59044000400c1c00003580003800d440950042c01c25040c014a640ca8031464482c00c2421080e04658442c1000181a046030109024048405050085042c90f60714246c1e10380d0a110001c01c503d5910070507204094011525103450107078a0440485195510b4800c0d107604004070150201d4000d4800c0015101d0401201c09940c2c0400d0201010355503032502c068004010060481c0d0f00502000070380b07280066203840810f1858072074a000750602c503081911829000c42c540146010f10b17000c110a20142c1c0d14002507030101d913440c445c4580e417807c40c18581001c03130059520840b14082d0410512000a500350050701c01e401124204201c01e94914000c007000c4042581c50344101003140360024081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 608196025 1250 608194775 608194781
    0x7060203070b1302040203040b220804150e040c172d09010603050111210f0c0a1413062304051003091a01080c0111120705120403080a030b0315010603 66
    0x200f40440307490241040c3c25000310b02039038001c17074046542481a0081003009045108582c102009640028a068007156106092407196004080d07101c005014000d051600c00c8416180018028205200c07801c00004058401d49148100e81e2582a1681c005480c0800c0c841c0c050010b042c0c500003861043c91004a2021070000182c070840c400d540300c80011011a409026032800d00101d0034029665008905200402d24051440c0a5406940405001021707840e441d402d5001181c68514540d1000200000c2c1c5004090303040b0425400008944015011410003c1000b02c030416103407801000f41114590343c1104020402c408886c5045c48180090704006450b181110510b080c0000d00d90050707110340c109410103c0b21014880c0c0504010b00100605010900c1d603581d003030801d80130303801c00712518a40f6036018000804c0c01c010041900c40030300808022038020b2078240000c4a648070b4480c200070110b64440281240824180418031030303c0d0800148100424072942c4d210045e036424030790f007140a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 608197275 1250 608196025 608196031
    0x10501170907060e1f09051e010c200909030a03110313080a0c081b0f0312041403041e0501020c0a0305030a27090902040516020604110103060306020c0f0c0307060203070b 75
    0xc4040004042c800c605441d280d299611443d40f01c006c10f9030310b03100800c4007951b41000291000442c080c240303201c990b04000403859517544400082d07840001800300740c110902e07441e20ba1340e00c00c0c949014031040d054003000034120000695810720021900710304d00e6980c0d110980348051164012120a40803800c1c01010b00010b82480c589615840d4083d20b44002e590420000c02c208003022003017070350784000c04100801c0070305d20b100065400d203500050f9a02d08040000c20103002c280b08000702074030342e02c03051027110054095070016000c071103400d82e0380c1041d4035014011031380544980c0000508a2500030445c40032207521000440c0781102e41d05040b2908100d407a1900800200482140781c41c840104600000c6c103124070b000900290540104400e881000d0001c0c800181460a000380c0180d0106605900603040340320381c9040c45050700100c00a25840e03101414a41c80460700702406140419140d4002d550301c412141b44000120415484440ba072042102590080100000140800900a40c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 608198525 1250 608197275 608197279
    0x316200d2d11041a0a0302060708090301110301080105011a07031d040c0e01090e060f091b3f15030106030b16083909040c08010501170907060e 63
    0x400090060707421070480907110811910700e59901000b01541c1050710520903260440002640d41c44003c0c2c020501030462404080c1c010540096400e041c0035807041102d8401c0d0b00a40204560800340908660310b42003802020103c0d424440001100040100300a941c542036600092070a6550381e0103a48018410f58100c0d5100c088030f415191030350b01d40c40355618000d0203071a821603a000d8580014031504054008620907004101446071940380c02c000300981040a83d05000151036005104101015141344801e001800286844540241585101c8148090b80d082d801402d12100c0c103014407801c2403403003a03219900d400000c0d03203134001e640d211a02d00f80246c0001001520390310341c4910540115040c0c0a440b03554802190042c3d88050040d0348011400a01c282c940c50070900d0404602158001100c03148460003c00f61407400a0102d50802400810800070702401401c044d0052700f003407041c140443d000040100c24500c000540e81c0c45121104080c2c5580c0d810075200759400d524100c203440d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 608199775 1250 608198525 608198573
    0x6070503061c030203130f0b0708030402030703060207050a021f081f0b0310080706050406090b070201140309060402090a09020916051308011e060e0a050c0c0316200d 73
    0x942c8101c1400e05480181e03009030301643c3c0e10310324600c242001030342c00d5200c25034000d440102000b1428148058411180e40655100ea0301c0d1600c0c00000c1c6040f82540001d88620300c00a8004100480002d486001034802d5030542c4c002c81c101914070118448055208c400f290744840010449030300030840941c00c80414800041c2c2c00d4403007100e0445500221802c401c150b40702c00003804008000c1008100034403103460710510306410083c0c010301d009900d10032414500004103d84045a029582c82d81e59000800200c0c0c2d160301d050902596150740640b8141e0282a0f0400410750211140c020f8244450700508010b80700d8a40d02c029010342071141407190304002c0203000d04803080610050120081a41320000b243c01e020302003100e040c26281c0c00d4240d00180c03800000f08a04241411940d9100240082c009501e0381e605100140c1c034400d21302c405502c0e0000007000340072408400c075420001c0b401403070b00d081c0b807800f64078090100b071400090b140e5200f048a138086002418161504151551000c0c4c42 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 608201025 1250 608199775 608199799
    0xe01080a05311103060c071704050d03080406060b03061014090907090608091f02130528150e15090306012408101e0506030106110607110607050306 65
    0x1042e4100000000c0d00450220503500009009000e40b41c031180100840290045061004810f002e03407244400007010010a035001501d4420884291001400064013a60103d00c442c07500078014102150300301c50403464104040f031603004200c01e0364400c15018014240014404200359882505040308650b101000c0040817500d80b6908540c40c001e0402d9111243d40b43d00341310340588041d038010901290b40d0b21104940c035843e662088075410a001c00d4400603607034030032400c5820790207106400194108000b038482004400f19020722640d20006841c1113840035441e00201d45081c00c41c4071070180020100c030142403492410b4075203580d02070085584e10b890902044082800c3c400c00360303c00c41d098900c410b00c207900010140e0f400440c1905500d030541981c0781140e1407204401160084515512040700c5e0038401e580e00340f00002c09002d00421450b1071b9030f07403810014a40f4407008941800e902501d400706240b00c1c01a0403c03242c600214000c0e050690342d500d030403102a040201450f620071070784020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 608202275 1250 608201025 608201071
    0x31b0f061b0207090e012009090108030c150606090306040c090c020a0b0115050409060b2a070e06010903060509010b1002030f07021c0f050a0506070221030901060807060207080d0e01080a05 83
    0x1540102d8040b182ca26522340308002c0400101c0c01c0164040c00c442d40041004004955011903081c0007a500001c1c407445549510b000b242e039034003038164281c0d0580324101c1400203012104e1040c004555503c1000d001c103900320340c0100d0b02c03803024090081030350301142c0c010b00114842e81040b18541d045880d01c2424070395144500c070190303081584002400400003d01e6a0010101c00c44c89901120904241c05a01106050a03a907080d42d880b81522421130701012400c668401c15444006503006034050040d070030300c400254000d00344032a80c01e01c500c010b880c010300e8071800031043c0d400011140d4010360401030140c007441035080b940d1540742103d8402d914110700068014070301119880c0910000c02000c45a480c21525180b07000e4021029944003d000c000da0041a0041044041d601e22809031a0703219140742a014040f50342004003a8023070400e0228105a0024410307088602001c00c944044e21a95003d13241e15503400461800200e04100054040800d80c001c143c100c20390403101d807c14015140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 608203525 1250 608202275 608202311
    0x711040b28090605090a20071103061b03130206251104050c0409020f1b1609181217071101150b030f04031b0f061b0207090e01 56
    0x201c42150391010a944480034040c03200315000b034229203504102d168100000a0300c1440f000300900502c030b40350448811900282c9550307034003960402e07542c291200054541030142c3c180060341e00e8080c2c03084100080c50743c03410303058102c00e05944c400c25500d161a010945020100812416604210200480c00f90000c000c035070019040c403a0340040e404011107151950206440d12031040c841d6092134180840158258210b07811160551070043c2c0d6070540d6007043c481402208040e42107014400501c818030790011403900040c0d07014000c10070005403140d0450041b03903502440c0c80a400c50a51503240000c0c04448a148603000a04206110b410716040b01c06030400100c0e00305000480409081241c21403d02690042d0a80700d003d001c9101d080100054003408020702500700308030480301240070b0501450151605280c00814942c031509241001c0300341c080d49000071505240b030541c81c000108000424034000b002c041c0c0c0508a010700d044110400343c1641e03401f64001d9581c03200d5091080704084 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 608204775 1250 608203525 608203549
    0x90f040f02060a0e040513021c02040f0612120206091203040320030d110301080a0305071a0f06090f070e120c040615030c050a0e0d0c030510050103170408030711040b 73
    0x4e0380380c002c01d400441c14007084e03540160020035101020f140c82da0040c0da884040c41e160301d62010108407020b0040c000030b4060b0a10103400c00d00d40e0b2804101242002d03060a1079086507008410042381505410070483c0d4418017103e0240c1190040e0564101c8081500000c54016004e0303e0202d5100d5403203401014692210b088070b01e030540c000038418031540324602448649900c040010781c1958075045c274003501e61000b503038000c0411000064540400688802c004480c001204034100d81d4504109170040c010b4065031114410131a10b1b00060201b8101d05255101d07410030380d41d41c01c0f2510085c081c400d102d2200b1244644600400442d004203445034814240141504c021314aa034076a10711004d000c59101070403d101300602001881c400b02d800c1102c0c00012001911002800c0e1124142803400316100d400041c4240901c80c0c00ca05128201d4201d941038074002d18802096485101200a5034842c621448460f900309002c00701c00300f5007001c00020744403030141c004503c0d9001d49000030101060f032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 608206025 1250 608204775 608204777
    0x120609130f02010309140d020f0706020c060a05070803011d06040606020d08060111010e03090a060305010f060c020a030c06031a0306070e040e012703031104050f0d050c060f1b01020306090f040f02060a 88
    0x101d01f5203006604000202c0905c1c0840091b00c6880d00340700000392607041405903036000361000200e0740715261203a422103000742e4104051580f00d50311480d548085c8000c1c1d94481081c64403040108103a460329200b6201242c3d0240c0003071070502c40c2048189e880100c0242044e0620072080c1d040000c0c51428000c2b9450001e100c00510340d5840d60031b0400c40014103030b402141c03c06151100620000411207110030503107520f400c241c404208a4070004940c8100c58100800383d46c0c040c100000e80c9501900102c40b81ca00440300800501c001200f456a684001c0f54131000140c118031030982242002c1e880408060f403007600102d00160074060f21031903040c0c80b003100140d0248011a000926915100d18a10700d00c94120240c9840d25041c0000c0271000c00200003882000080000700401c00100402058010080d01907a00c2d46a8200c96540540052640901000744402a008001e5041c8210ba00c600b00040406515482d400c2e140f0324011030051007150061801c011820145e1340740700103000b4035803e03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 608207275 1250 608206025 608206033
    0x51002030c01050a0b010207031502130e0601110109050c060c0327010801140109050909011803120b0d0c0306020f04030f1217101401021e03120609130f0201030914 72
    0x1c0c0e842074215000200103129603840c1a00f106000d03a4007141c04404c990700f01c070521501c94000b41c9018002c1c8101210302c3c2c0035508108000424869100304c4903c83c074000d8840210a09814480710b081e18140700c401007080c0c2103510f1020313840c0351440c040c0040c040400e04a07801c045840c00010384848003d084c05101ea90320249144241d03078030241c03035801740c440d0542408102c52804000b910300003080c0203652203541c41400040650744250f000880e201500c010620400785c076400c001d0b01c21910111a0226641095414401414240760450005910400740700352146142c607940002d42140f0114490240704110010201e107800000518180c00750461010354112010054902c0105c4c14074618801c0ca0f1004100c2d40c0400361a106084a0350f07019250155450740380100d00b00101d1002d0441d81407002d00c070744024964008040d00c2e42440302c401c0c0400d10346444007002102e20040743c0340c12809003030340d00790800501e1000c0207601c2c01f03106044c00310b000b0340940e440901009550301c1d54441030780 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 608208525 1250 608207275 608207287
    0x7030908040b0723030d050402041b0e040501061d06070f0b04060e010501050114180f060a081816140301110301181415120a020a0803281e0905100203 66
    0x200b13003045400c3d041ca0361300c1540030700c080340c034544d40e128011100c8402ca0b050340d88000401b55111504810480c00b0100c1c80a0411112194090038222a00e42144e0103103260200105225000d00308011a4011348001d540705502190308100156200000480e4034680a5008200066001c0c1d0180d02491007101d0100f444401d80d00d2050071624168080d0741008003600315200140541d8088541000c0700501c0440441030007008580c1400100c0c03699500500002002c044407548542103900405804104a19800c0308a80917a45c441d41c41e0412400310343d01d0f030700401101031b405e035110207602030107000407490601c0081c0c01c07900e0760000d80c8040c00c0c44141030502c2180e9540351148118824480301007910b20300300304501c052981160401300340034441c5074410703a0080d002005020b1407903074000c10040b403003601ea45c10389460790002101c0c0b0502980344440300c2c007007445030903500030b440a1540d6000e00c1c2d80c489151040f007114150400505000307440c10013040c6e54550301c108101110321500115600c0f1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 608209775 1250 608208525 608208533
    0x10f1b031b050418150803090406050d0210200105012301020607050d09140303040c030c1202100e010c0203250e0606070f3e0d05070e07030908040b07 66
    0x1e6201108001c841d0340e0440040c08894114007901d041d1054002c840700c41000100b40d600c0200340c101242c40320b0080c030080000e40e4201c00001810300c640240c03001c2c018541c0d075100f4403945200d40d0000075032060300d060300314001078424a806000340060280c80800503580790115800c44200b0780010410519090703485051101c00e1843c40550b40083c4014040d500c5d180c030008000e8002d40303400210280c2c071440301c0001c2c85124039100440e4580c00050f240d890034185003406040d251440101e4000b0084200055420b540407138101c075081e0054107036032990305960011544107500d200100d052203041804030002d82c8082200c045102154002c3d001c0c01c0c010481d03100d8480c1302c2507002081543d03200f420054991202c070155000a503010049200c3c420540c603001e80c050088200700801940c0b4080301c81e0140483c0c91650244a150459045c1c4400004040c0242000b080c02d02500d036920421041200d00080a00c15a025445140c001040640d40c0d90f03d000c180c0c0164008040c00001041c808180 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 608211025 1250 608209775 608209781
    0xe03031b06070807051c0b0307030233120a0b0d0803040f03090f030309030611221d0c1b0f070609090f0c020601030b070c060501060f030c0219020d0203010f1b03 71
    0x40b031300c1800c025050003500002c0d01c2c03062420700300003004e0b15203581c40708a4980302080040080d503401401b02c2560040c0b001607910f4002c01c44c078114405081d00890701d1402807030404595118502c0391010702299200350701c15010342142e42410343c114140c66019000302e4090070185005910540701001c00c3c03c11750400908100c0b940d00314024155001008200203908007000300220307a809440800d075103941661400c410f0092104200c40080302d1050407081c40413a12198040e503001c0c0b80f11840001420303141041d2044200c5203014841c0041107100c106091400095102c1345400c070495031104004060f080c1006034a42c4240d0200e0b800b1760f0103011240395400f52000540200d4001c003c043c00004009603101810711014010400100205403024442d400322a0310a4100c1410301003540c6d15407000b4070308141c2c00c001c040040d00e4803002d41c1a0354400b281c01c815040b4042c0304003001c20700701d400300201100c6c05041242e1642d44c03610b6800c03c2a81d54010041000002d8030821090391200c40d002e015 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 608212275 1250 608211025 608211031
    0x804051f0e01110316060209060301080304090e0601230f06130302011b0308040305031b040f060e220c03020d050a051b19050d09061506031503080306010e03031b060708 74
    0x14003004410f00f00c04001c000081d80d01ca609902c0c4403440821460821000a1107100d03c41303030708002d00100116907031000200610884e440c0d13450030031080c120141c015440704001e000703850145c2d1601c882c0806070f4450706040c642002006010080b807081c1d0400080056022205200441e2943e850400942d81c001c141c00a080d0010061701800700e100c0d5600800d0002d0003000202030100100114400c00d880e000891040c1212841071b580e5981c0f5080071094083ea140700d00310002d94070684451540c01c0828002441a1052603003c018140021046020f0250b003090102059428172690304496082c0c003a00f40109500000060785081082c68071144c2102040e000b049003004000c0742410007200c001c101e41011143c03518584960340c1a8035800540181440078003402e0404060106540f441108102240e8807a1020403000852103840352100007140f01c0070b01141410700014132a54000d9441c03c001c05801001d481ca010500c1c5502e00c0e08200e00000d09032617621490410503c0c540029175150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 608213525 1250 608212275 608212277
    0xf09010e030f070206070c030503030108150604150902030a1509091a0f220605100e07020705061c020715020901080a0e0a0f05070f0905100f0602060708040804051f0e01 74
    0x1203400c0c150b001c0110584a22403009000d2076000584405100002060101440c0d0000039650340e540d466040582d90a4040f442c4c5403042d0700d000100701140707424410303801100c10540b8403407809413030310070408000d4000400800000e0f480c1c1c00c64010340040a4555000b8215041e40080ca038034841c24254088564030707201c208070f414507100344103100170b0038042e1503404002d981c0000760781e058a51041c0c0040c40000c2d0018080c605240c10703c8040b1216103003e5095039800c1d85200e060f40d17544032040342d039400f461127840e0b04108100148501c0e03502c4458013058421003488058a00f00865460040050500e2a102d50043d07001c80e00030030a40c3d208200c2d50700302582071018022007040c43d03105903c500d00341400407d0f4450151143c13007000018440d0000400c52101403c10142e540c0f04c01d4005440c04507015080801d0001c00810320840e51441c8400b5290705034001d150a50310584140c1d0903010180068075050002d020002e015941ca2160b40c1d4000326850440ca5103000712a006001e030128a6001e034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 608214775 1250 608213525 608213527
    0x30d0e070f0503210310030602070b07110303160302030606130b0703120605090c21011403060a020703020606010f1103031003020112050405031e0717090a0609060e01120f050f09010e03 81
    0x2032200d034001c801840503c0c4c2a0000c1662500c482c3c080944118250340700520343d9002080760b00600c4448e11505100c2d0025407110440490b085d2100ba40f44c1c84100c0f05000002150f20202080500c00d9000c0e41c0c2c4403001514541c13070080e14000c40442c240690b13200414a40f40040c1d81001c040c2e00c00085045d003030b6003081c207009103030803c00040c01c038000080460101d40000304281d441049001400900600c0010381a003455860b403440c400c116000c280f105000c2d22404021400d08481403089407080c58043d0302800c40c030349955004441402146245030200240e210307194402e00c505000031030007040401c0e0b449041526620014141040002c0d05140c1e042c942001c000c0450030200864820074014200045007140e40c06848000d4000c8805c0a009850400c0b206101c160410000f4a51030204131008800c1a6071680300300c850107442d02481e8001061020000c2155001e429030100b0185115404540c1100e08803400c01201c904850100844818105101c04441c0c01e01c40d410002802c00061 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 608216025 1250 608214775 608214793
    0x20c070605041203030e25090c080609010306180803010f060306050f03071e0b070c061103030709050609120d08060a05010e0f09220b07080112050606090405030d0e070f0503 76
    0x4900c3d07a09084901a05041c0c94400001d40709400707010003040c034903910140c3c050759240c02c9044c6150710264090202840c0c54500c140014a00901e40c40340b04100040990720180c3c02d594510000c0d04104403070b8185211040d2600002414440145020b00342100d00c41c0126490040000e007034070711560049015401c1464032604a45002c0707103110640e00410ba0b407012090403240c0c1d5841224a0350b0040302e030382c03101280340401c0080390042d400c00c0b9492991082003000840184503100c1c40182d0b00070307002c41e03d20a0304204c60708099014000701c18005004004c401001d0050900707040c9110700070740001c1c51005c10011f07140313041c0c0d52920181c4020f182019071401188080f0303060000300c4403403030300c01c0c0c80e80800240604501e03070500d00c104c02d812003c12908502481c03d480740e00802d413442c034045040b04001095200120254050301c580110041480d40c03180707018007007541400b078030543c3c21340003c0141c1d40301c6012a010351510405048002d2494501d0302d41c403004124195040700e0f12035040805c030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 608217275 1250 608216025 608216039
    0xa0b0402030d0905131d1b03010c17041127060108090d02030d021308070e100b1e0304050f06070c0506010e0f1609181a010311250206030a020c07060504 67
    0x2245500d10104800081030500140201c02121000446c084103214285d021001100f018400440d040c000390700900a040f45203030f0075511807100c2034880e1070b4090701100180c0030401e02c9814001d403840c041d021442c80a403204030b0311152a010110105441440d2041c4411940d00c01d01d80b0b0b81c4440c3c000081c016521601c20003d44034400c0c00241695560081a02c4500c80d0001d074105005022440444058964420b03000180420456401c14503024140380041c80020560031510307601b2500421261081c000e1b41302c2041074001a0042d18a44103840c8617a484d26020440c1c02c0c040d11007502c1e00c2c1c41c40440ca140c018500710381608203001c5404580244240401850300140c3c1214010340c1020709039606450031258101a43d0101c03140d00134043c10b555082210381e2000082c00006401070400c0d0074180e00550955103c16112124900100000350240c1c04a01e1501500004c1c000e90540b011405d80004840d504142c035080040e55000507258401842004031100400c440d0800504091a01403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 608218525 1250 608217275 608217289
    0xa020d020c131d060708010e01120305090d031101060609090e0109050a08030c0d0f0f0c08150103111209010209010917070e10090507020a0b010801090b010302061b0a0b0402030d0905 80
    0x90120010380e10f6911400ca20b50410000c6010226084101c50b074914101d400200140e41c06e2103012450b00c2d28400109402034005a0f11243c15019240e0600d0404100188610b05078445004d40810901120944010720280643c40061080d584d40d480401c0c01c14221008640381c00283c48640c0e0b00d404030500000e000070034555030007904030406589030b07035400350110a5845003580c2265607914003d080a400701d0300c1e42c8034514074018401d041209203c01503069540340e0098440d03541410300303d5010041903100385c00035101c048420f80c1d82c6d41403016000512a07401c00a55030010703180d4000c078840c0342a503404000e0740700402c0a000403281450b94601900e450306840d01900d01400002400290004103145000000b0500b41c0c40030009841c10102c001d480d6000e1503812a881a100d00001502d480140148881c058004640e0f4086918543c20410154070502140340d0300340000c2401883d50780103000c02420f207401100c00b40c1031864640704140c05e00d102c1510170401d020703102e0b80c00c3c0004e441e03181c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 608219775 1250 608218525 608218549
    0xc060604050612100905011b02071508011d0601020106051903111801030807020103090b090307060f0e030414040905032a0a0b0c0307021606030e070b090102120f04090906020a020d020c 81
    0x40c5000444180c10304155014010008007295220700c00ca48c000e0001c2d070b00080b200c00302c4101c04075010b8540000d4904460b228070a00c680350803954220402d0110200c40700007a90000790500000442075624004181c051815070403442589101030400c00500c09001e4096445040803144c1d00c1c2c030b4442401140e07100c0c42c410702000e840c101e008244441164000da000b0039a080e04860740e000c05141540005940342d00600d4222101400d00112460044940c01060740c0b500c1072502540c00c1a0030440041c00e00d001c1c6400c43d81e4040e46071044440072420500040c40c07947c0c0183d0000d01411010300c2c00c802d4514502d100000d40d41e2203c490040810302c0310240e0758105081d0007607550b40e500c40710b800300c1c80c0400d90303c4400c818041c03231940020743c4c1c1d400da030040195144610594040654648030900d6174000c0c500407601507000b22a0200a50300309000404110708100034960603ea03c030b1508504541040c54119140c580c0000c83c2c83d00c00760100305c3ca04117100c40388018603040501c480864050744000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 608221025 1250 608219775 608219803
    0x170a0f12030b060427090c0513110309010209031216080d0905070902030709080703080d0c1803030f0e0d1a090a0209190e240c040b0c060604050612 65
    0x461030041264826001030500c041c00400158456071664688040300f114a2180740c2402540054a404036071180690041c0300d070055005180c662400040c03040c5185011103404032155903e0300040180300c02c8021303500400940b0300043c0ca1380110401d15240080411500014040604c40c014401c2e002d402580c00103644014055110b1251300201c00103403110b510000d20300d0181040108240c22254003035440388905940342c0504980c0c0d4003580d51100d04901000e04103c4040105104020040d04806000c0c103c40c43c02c645100b07403018074015400c1094000b180004c1c809034003100899030240f442420640200d45560b00b045060759024581c20310325910f0440d0024110000703102c00c409000c0c6110f0399401408070700c0c0d685060800e00340c010003078007a1040c441e4a442c0b4040112203000491000c080c48541c01c0d1401804065081d00000b0b8000703084254044040102040462440014020328500400140214107014080000b5150024031103400303241d20149400c01c1407000541e9081038220 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 608222275 1250 608221025 608221043
    0x60118020702040f0911040b0d050a02042c07050103110f0d1d0a0605040501051b0d180c030803250905040f0b040e03030103030e2205090a0c060207170a0f 68
    0x49440458080e0401340c401c07584c1c0c00c0c9448001414040c41454180001c0740c112020400002140100030140725008409440ea90010321090014107180c3e00032071020318110f80445003e104061200700c0b640702034801d00415001000c0412695800d4092048c40980b001d120070300701b03030920700c8280751401403100441c0166150b104845143d58541c2400f07501e042d040e01030b208500003a04000c80a09400e5408603078035840d00000500d0b00460b0b50304113100c01c1c0d050352018641002c85846501a1040380b22040254030044540000222141002802148500061078076441c1c500840d010b050710982c52a605000d040d600e51000e01c0d030040340d090903030743c04a6001038082d1915200000604640c40910340087c0341c41c004200204000016504a13031281d83c485c030465202000344800c100d4030802025126400e5900506070705441d81020307500448400032a07036080b046480e100c2001800d40c0c48100940c00c8201d0500c0000c50b0080400000d80c100b00c014441c00c10642e4030040141d075003140c0a072600c51 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 608223525 1250 608222275 608222287
    0x150c03060111030c0a022403010b070c05040f0c020105061219030311070309030203100603080315010c020d03050d06060e030601090e07030c06033e03180304120b01050306011802 78
    0xb014101050b00e070114441141d407210982c07080c1030399540d15540107910444130410190203c21100901d035030020b640202c0c16040d81d190901828203604a035034101d81001c0b0302c0b000130445484e24402c06000042110340415080e020386000303400c556014124500410040c0070515645600042080c5001101ca11401c007500e001d00b01140148000c1c02412004040003900380280340e444007407a0240c1c1d00840c161010399507881c42c3c5208075851440700504007441400028002c0c0c940040e6080b03501010b0501410b41d504590000c3c0d050401c2e00c1088020440c00306054501c02000d00c141c5014003a18140401c0700c40c0c5060003c1d50300d42051003100003907500c2c1d40501c1c480000a1203400025503010382004d14254a884011f006865000c0401100540c6e0303100039503800b581c0745004601c481c0c511250007030203018101d1003201540b0040004c0c0c00c4410b008000d9418500410051000300108565005402a1454203014451060384801d200c2d50055005000038103410321f02e601d021094905c0165100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 608224775 1250 608223525 608223527
    0x12021f0207030b0f270c130209030d0804050d0e01140a02010605060703020303010e22021207120f1509020105191e0e010f02030c0d14070f031e02150c030601 69
    0x9030542c00050200e01203c081c003411000910741207000e043d5403205040103100d820b001003080598103100480319070210462450500b012003848498040b600b0003d407400216102103450011541d88440000311103030208070602106008003001c842d0503142c9401001c580200003044d600e00d860310341880f4840000d4060240e4000d501200041034050f1107540c88040c00e0802070b403070381c00920a00041c002c807100003d000c00408181403814400c4c483d68101c180c1555000c0c058402810310081600b48500e590114000001e64845681d00b4461940d00d9258101072808040444100103031388110383c00c040b103a00050303800406a402c640106401c007040c4146102d0300300c0d00080d422000722814564002c0380310030590300c000040b24091080e01c60340d003100225803080b6500d00c20141c944000703800c0500904001841200d8610788a050000054100350603034a4004070307100940300403030108134070740381c2c0c1075540b11180b0980c011401c50740040c11040e0241e10b103030002504003c0550032080d0f0000300250450b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 608226025 1250 608224775 608224783
    0x110f01020f1818040f03030e0c0a030b070e031903030b0a06170702101a01080f0f0a0b0d05070b0909010f0b040608040f050d020d120203010f0614070b040c09050112021f02 75
    0x81c00c24103801d03030442c04d05040550101c0c0b0680030a0700002c1c1007991801c1c40d00c000140c560074140c8041c0001c0601807450300c0c1c45412040182640c0704020708840c00c20401d41d0100610b09100c3e01c08144400d1110261501400f2a5003005e441c40c007900c0d02d00801c00c1280e070002c084811101d21003d40b5541c543d01c1c50f83c204d091080000b40d1440441c5400c1d00320f00800a00e5000c00f114483c2a25034488603240c8030300401ea0341e14100e03421117201062800090f1811800d811400441c00d01030040c4584621aa503200c2c100340960f0400c079562080401c400c003442c0303042440c05004105401b54802c41d107003841200030451007039009045c144034212000c0750400100d00c01070070b00b080c0c01c4001d460107000b040c000203480d480c600d004000011590354404402815a20803681220110010283c0c2c0901c2c02800303440248039506c01640401080c06100301103107210841a2003140302d402582c07082070a000c012000c83d001030b040008450b00a401c104016202c0300f8000104840704106e5407010b0f50704032422460 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 608227275 1250 608226025 608226049
    0x11090103020a12050718060c05120c0115030f030305012304090f080d0c0210150e100b0307080f100315410c12070c02031c110f01020f18 60
    0x4100d142504000d00c5d680d0007100d0402ea03c1b5007004600c2520b039115402c45920030710000141c125003280d000d10710011a00001030071041e400b8400481c62203111004a1000c45140e80281c0f00d41c4500d442442c00c16030f1502c03030103000d0b1910071700200b0001c0a03800d040b0010300501c00d141d4015580d5548600074070040200d200350099100c400259103101d84045040a0242003540e8005803169142100140000d801003440c0402402c1000da886464900100304080c3d010b000c172402d46400c40004254001c1d00c00086200e1030150301c0c0c2c200182010102d1301e541b041c0040466403625900d500501c00603e60004c0c08000c11410903002c1509100b0007101c0c40b107410203141c101541698044a002c403d84000b45001e0b43e000b01e201d0340701140c3c1d10103407110000e101e90352042600c8041e8030001040346000340b001d150014000f070220345210130120955460417400c0044000400ca05103045d10302030f2010420301003614000002036007401e60f80442c16202d8010b21a10b0540d503d5103a5110500e9181c0c0450684 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 608228525 1250 608227275 608227307
    0xc0a030f021b010218030706050d180609050d170403050f090f120a0c0902131809050a061d0d09230303120f010b0c030702060f09040c0906030f11090103020a 69
    0xd066030600c0c2000f03000703611800b51301440c0e03140840043c0c0c0394540410084e0846600762102403170020142502002880802400c0c5000c43c3c100083e0784c0881c0305403050740500c6105200410325806880405442c10b00a03180ca104a8900c200400001a60000903501840341c045c55540c0c079170700d550000400c9d6501c0001e4041d004031000c80100b4104000040e0b910145004040411003a5151500d12081c1e21851400003203610300385604206d2040184242c0c01e0307900603110300090400c00c1d6501d190405984581c240e9283d5142d1500200c90b030742c1a480110002c82240c002c00240c0320f00c62006c1c0c2010040d100d04403030b02e50b84021000300c048070440c140b81ca4103030007004d0700e81c2c0d4900e803510307028032180a0303070700c400310261040010038901046000c0302c1824051000542c00e02c0f80320341c03c0080d0b6038450500d00c072107048280f10f901402e46480c06581c8444002c0e888440c0342504000000f400c43d180d64075103514181c100020b9440d41c840c0e2004030781c00ca40082c60050b0b0b54110220060fa071f16800051024 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 608229775 1250 608228525 608228557
    0x20418020301060c030e0d0209160f180b030c040e040f0308010b130302122d0d0c03020619020d020705010c0e0a1d04050a05030c010203011401090303050a031a0d03020604050d0201050c0a030f02 85
    0x180020700b031f52b01c107000080303103484110003428140004c0310361000b000c5c3e00c920040080d401c2407101078592005541c2c01041054401d2902d5201d80101e030455800b600d088401d0781051442d881019081080e06002d444513020721070514035001000107032913038117210203800b40c000e442140300d00000c00c0c8460040c10318143c1000941040f011800600c5003a4a0007c0c80a0b00400800c050424801c0d4400980b075505a8028500b54132103031311070f80314150418081010580c0c00c02c41802032805a0024001c2d00b03005100000f00080b1080b0040c10440d40540701c1340c0310ba91401000d12110b8400c0e003007940c85e14108411255155594034010f85400c900c0c0e2005442480040b85e0541c2008d0150001c60503980d03000059170b100041c9400640b010300782400028003284052044809503031203544825141c2940140400454000c030f404200c024203002020350050300148100018400b0800a032a00c2c4503071440204010310304200d0001035030080400340020103490f4070360a000e180c4070380c040d01c2c3d40034448290f071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 608231025 1250 608229775 608229781
    0x801020a0809010c050a0203041502101e110306100c0611030f070f14160507030b0702160503030c060103150209030d080405010c020609120f0c010609020418020301060c030e0d0209 79
    0xa0301d00c20080711000015801d0032400c464041c403640603a07903080003503001907003081d08040100c010103800000040841c811444030b0741400c455030107400703222034203844c3c00317075000260b5088402a03410352800101001810001c0c4289601e900249504040d0789150400508100d4540b03040903000c110150850300c0300220620041035205031001d4010569074603001c1c1300140b814810380c2d910411305410307124407605115441205010b0803030084002d100310107407400301c0e40f01c0ea941c2501801c00c3d254000141c0c011348001414411200b02c150252404030300450034440040303801079940c081404003c190418060708413400308095015210f07010001000d403904251445002004201c0c1220240ca6640c2000302c01c0110f14008104540504c44040c00b03845c20410400e21806558820440207100c40420030504e041003500388154409030410601c056500c17460300e4071120100b0440700130a8251841000104081c0d80c225448141d80c0e0341c5400c007254a403020000041c40300c8807140c1d010750091416010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 608232275 1250 608231025 608231027
    0x20a0e010e0106081807170a060e1b010e0a1a0705030a1d09040203120307090801180501060e1302010c0c0e190e010b031203180a030c20010503060405100801020a 71
    0xc1c07141a200640c1e02c00c130075a40d030181000d004030301c3c450380f10040e0b4101041c180026038a20402800d0651b04108440e2660038a80d500400c6814005c00094941c21555440080d00800c44244488480929003662405080b07000140c07191400d101d07040c0c0403c03d40b40e00065034407800c02920f02c860741080507039840325400300c00a4241c000704402085240300b41d0240964070700e020042c80d4041c580203001824440450b41c503c00c1280d02c05420f1100b44441355000003000e007030900030840320344e02022040b04035200510b001c41c250780d03281c2c00c1441c0001c0801c003080781d80405500989482c98092070f0505404205040070840e810440e0000011000c600c001c0000c2d410014030f100c074040c010400204250f260443d2510301701d549108040d13905070030001c4920048000c0c5da000d15001036600040301d0400031200c058904e0700301c01440480104458449070424460180026514000c200c07020812102400e40001c00f148001880c49100741e6036140483d155040a81d007032409411051700855590a1b6250 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 608233525 1250 608232275 608232299
    0x131509021305010b0d0b010e0a1211010201020c0d080c070215070b010504020906040911090d03021c0504180f0b060d02120108011a01050c0a05031201060e010921020a0e01 75
    0x2416070240004180c100000c400703601c0340d18103e0341030050841c00c04c600702c0f0566010b028410390b8a410400b1203c0096004da0314030010340014040310750900f10b18040c82c509404100319100c040c0d03040d64418407005c2404d42003c41e80000140084c5094841c503034030f11000c10310785e005408020f500b0800b5654409403c0480c07000811036540108000c12660703a8940030031040e4824080441d411030001d100402030840c40303800204200b00384d241014100300c400c0c030102d540c06000e40070550060748032200a0254035012100c40c0042c2c5071a1a2052034541000158102c5c2e940c82200b489225554110600a45407590b001c0700044070000c050541d1001940c41a030040e42000c0c0341c08a004444000000b00700070144554518140c0e1400c2c2030b4031400005005555a4000f65035203043c601410040344000392091001b440c00c00c2040e00c0c01c84895040150040c0b5040203c0c219506100420388240046200070090880d0b130b04d520394041c225005144042810b8240b560705c030355400c0c1c0134600007060101c0c03061 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 608234775 1250 608233525 608233541
    0x2030603060907032103061a030103230717101a01110303061c02120708060411100903081c020c030406031113031b120b010f0602070305060f1315 64
    0x1001c5980c41d485407480681c55450700e00c4000c0899803e50884409030700c107107104020016940c03e000515541c1c3e081c1201851340c0b080043d0152210000043c020003450118031721000b100900c0c1106080503c1c006e0656480007070049503010107404800708000704080001c407190444145c8180080540380c580d1403517462004089134089a01180e066103545400401c2e00e2107500d0091040324040d52060b1900c90b80e055810003a81c10080b40d06480c1c0e00444100642d00c000c0c10408000c084614181c2813108001001045080c45200c0400e8070390200c80c2d21012000c10b507600907141702c1d60b5001945161407081d200940c4c5074020350000c1084845900044080d0084800986003030040700c013511a1185c03d8495024440d071074101c84c003001e00c0801d88000000b0040c03407000009121540c0c44030010580721442c43e5080ba0420499801030040b480d112824900400d9540000c007422421030356010f8a030b0300300421030001544400000794400040792541081507802c030046003040200d152407040609090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 608236025 1250 608234775 608234779
    0x3190f0b19022d0c1c0e122b050a0e0a0909050a0501060b040602030f0d180605060f030c0d030c110d08120c090105090405130b0c040f14060702120f01060603020306 72
    0x40512a10707500c1c260000c450350844030744045c000c40c07070301156151803a00c80c0420200800420242800c40342c2c48045a0840180c410b000a00560002c4001002d02159a070700030480010a4811a003401c0d80110941b4404010b509042441c0741004012490401043d4451338100d1b06245140c0240b0402007095149580128003c1c0481c0b134603092104a01d1045104000060b0f004105003113403018588043c181808402c2000706a19040c115030208aa20f4110b080d20744035612014008649060f40c030900045006a000d030100755511300010b12049036a010140c00d12040205803401c12088481b01c024200c2d000784990b0a0000504112107141c20240002c004601c03c040880d04000c025426210040c805130740d803501c0d0121810a000c05401c01901c10074094001c862840006805946020310a0448074000380e2150300d40b40c800d950001490348480b1021182d004016540c1d210002159865070301030711380c2c01417202c96407a0641b03040c00c1d001008182d546400404110140c0c103800a600405003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 608237275 1250 608236025 608236087
    0x3060b0f09101703072411030109060501020c0405091e01180f140609060406020c011b0f030c05091e0102070803030c0a080108190b130f0503030603190f0b1902 70
    0x1c0c007a031031540d034445d414001c3e02d001b51090071200c544442e2031b091040c81c2e600c5a00465101518401c4c22002e0f002a0890750721a138852105220559040040350785107a8111010301c0b00782050b085007510341d030b598001c8005010205e2511a85c004007500002401342c514140c6420300c0050f8280800195070300300044030703c080908524a101d034000202140980204005440030761610b9841000a40c850740c6400c4041d525248100142c1e4032460080e50f400e621515190101ca0301140020115a4121000c80070300100b0710a017421034803184079a00055000305210100400010700503454499941c1c0a1031031032000008004049161601a100c08840303901c1d840d2850340c0301c1940e41d88460001c40c458100b02c00410031900400c141c00440358104903108402664081d02c0c3d12080358807000300360255426440042400918201003250480c1148412003500040c202036440a1440c041c01c0e0700517102412103008a28046411400c0000c1486400c008651f190702018103081d042c3c030030710000500054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 608238525 1250 608237275 608237309
    0x9070c080f030f16091202011205160201110f1c020f03040303150b0a050307180b0a0507122c010302040509090105060f0102010c022a1810050301110403060b0f0910 72
    0x60381c11007649900380a4817403682c003a05000302e6000080003002d00b44d0400c1410301c5c8204240006220b01800f540400c00040200c03891940041d084d2510440b1031140301e1300c02c20000d440300c845801a11a2442240242c48030701000b4015200640103c00c50004076000000c1400300300342c1c00d035202e0001c0a203141401c0d4421a5a00d40f900304601a0154140105800b000015036282c414820f0250300754909900010f001d4440355401410740012a40001251000900030184030060800382c9151040b880c224806070840c10030040408200b0410300100c0e40c800704079030380c940c1c02274042d9009001c001d0441c011500e003104003a8080c010540710303540900c0c884142804294418059a242050213800911403002c9807041c00b040040c4420f03058415070380b9030710034084a585600c103401801402510445007070401d200480d18034000340d40000d03c26803402c2c10f1004a16084d00030303a41141c0e0000300c00203400403e00c4c080792041d102d06151690000c0c03404100710a60301c000300382c0780a0b50300194240c17607080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 608239775 1250 608238525 608238541
    0x818031308190f030818190c080d0207050d03020f0a0c05100207051c020a0b0d0903140918070302071b1401090f0e040f0501091a131109070c080f030f 66
    0x10b4070806000e0005883c079401040424000c002c65604a52000300800440c1c00c00200c450918000036000000d00081c94914401e02070a601000b020300a0540a41810050280003070360300c52141c07040034000c0c0d0041e400002410300034004a5540c0d8503110170b80d08955041d00c0c0040e50700342e05000d11442000400b4000c004d0314400250729040d40e0010384501840074024040120000c2c061804030fa1040d103400e030108010306030002400341c160201001148103922440d01600325407a10400040a5400748000e5150b5690f803c1c4a0032001b889800584c030729141c100080f030203403003503e60244c0607419000e9800c4030315038001c10000803140030080001807005c01c00700444540100788902464801400c1080c050b103400520b9550b0420f104542d21503464006a403190300795001840b040d1052901000102110f1400d005855440a2140802e0301b9450985d80d03100782100c00c942e0f0103409000f0a1000921040c001c0e082c1020060704440001e40321510400d000515601c221466080c40c03182001148100c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 608241025 1250 608239775 608239813
    0x3030c020c090a110708070f1403071205070f080307110c030708211c0e061b0a140418050916060504030b042303030a0b0906030d0818031308 62
    0x101c04010103103022920343d031001802804500f0805a03018100f04020000281e54100600700c4034444c3e14400c80000a9082160b001501000c1022103a0800c1059000140756038011140418103803e250740ca8a4031420081590584032000411031000041404400c82c1c100112070206000581155040000319040c50b841d51000d2080c140c0c10341c0b0101178200314074008a121402d65612a202e20b003400e0110a912101e510940c81214512780d80c0c40b03e031240300005200d000e41c020540188250720980b240c0b000c480501c643d04c2c04004001d10401c5c03026800a80740216130080000f19800e4801d00c000c51042e9005000503a0000c42138130a145904c500540b04240131b90407205540c80e02800c00f85941c0b62100310920080084980e4010710146000300b0724201c08514500780c903030b0011512844c00019002c1100d40708a240b5101e11028001c0240317641d0300007445003046650386130900c169142c10041c038040105c00f880b540f009010201c0d404024403018024030080f00c000200312500c0c1d03a03c04500d9454 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 608242275 1250 608241025 608241043
    0x50610020d050d02090306010f08150c2a030a0203120f010501090b0d020d0204030f1e021f030f060e06150f0d0e030d09080301060e0402181c060c02030703030c02 71
    0x140c1c10045184071a18000d1000d014400c8210a000d49030101c810002410500b09802019450044c40c6040c031164070200400324130101284540400c0c0d0030042c82d02174190040302106030790030090f10100411040c0d094010000f204070003045035114808020040e403a9007003420071070b152007402c20010b402d600114041e00e0403584180c41e24651542800c82e881196841409103d002035001c0112100b200d2080c07004100540c060001d41d902c491591600f0300ca000444011180b020a0710852100544e9401e2500d84070f01c4803410740300c003a079a540501500508442010416040e00d0594001442c50100520a100744811201c020074a0031540c0c0d600e001d8012a018100800018401030102e05100d50050110310540c90440307050a506038680d005076a1112421664681c020004000c10350300700700c02c04e410f04400c49041d418a0824040584001c0d01d0b09152071080502c0540c803005000079402e440900703508120244100b1400e00c2c03003c1e650782e20580088000038605000034005900c04950014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 608243525 1250 608242275 608242277
    0x2a06162d0b06011b0b0a05070306090203061e130f0501030611030f0402100908012a0518060702061e0406021009050c24040f03050d0c02030607030203090a0b01030303020d050610 78
    0x11036101d01004403140341c10400101010800080d091340421032080802d40305900441000c43c40345040b201c01000d0b900140d000d0024580180240011a0f480094410703100340d01074000380b0f070201c40342c0004c0c02038034008200211107442c008562005118a401c558140c070b0140b101440400b1035514042c54500c0101c0b00403a203071441c3c1c00450b00501d441103001c854038201c2c1c60301c003100316110543c2500311442d0014502d1a14192242c00a00d030250140301031710940d4500f001800c10b8036140d000b003e55052544098402c4000081c002d00b1544c8110131b072010042c1c58078418101c1c010080d030b6000d444d400386c042d44d005031041605203410324031903004419070250302c04040e051024981d4180f20940720010b404040c540e686000044050ba0751602910040c62507070454140d580c80c50030401d00300034168144908102641400e880503850004016030000114034005070b07a036840780b0700ca40c203085940c0c600500e1f201d0848000000e060380750700580071342100c6110400041d00e599041001461042e02204 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 608244775 1250 608243525 608243543
    0x327060516050f0a0309080313060506150403061508031c0b1c0204020a021c020a021503070206070528030506120105060f0112020903071203112a06162d 67
    0xf6907034114070350280010344080d08010400c0c020f6661150580d8204644103601d480f140c01941c81032241501034550404070540300e0b0104401c150341c0b8829244114040582010b440b100070742d0300b030100e032442800101040350907030384c0340c012410040c101824080340c40038041703040c10780b1a82c3c0d5140240d5030000801c0900105150b11140b0f41c24840030350009840e4030254007441c0f076030346040310080343c181051034015406005c44120030720421441140c0020035100c050024010480f2640e0000780b05074100e4200c0c11300c107481c1c45a070900c0c64100c45580c102034544125a04514104503003580120740500070440f10b891501100b203250310b0032101c1c1112519032004c05040010059400340c1200080c414411801618203584240420325014081d400021104003000800e0300b80341d4482c04401f01c3c180c8410243c80c104041a80b0301c043c88070402c00807550007040000c0301805544800442d01c4103041074518800c2c5168900382944580703001d22660b2100c401d0703d601410a0750340341c2c402e15110b42d4044405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 608246025 1250 608244775 608244787
    0x25051f0b01050409050606070f0b060a0b0c030d1503063b0c01180e040b0601031103041a060406030b070207050a0b1e0708040305060405240601050a0c03032706051605 73
    0x18001c0d1030003401b400d4004204200403c0170840340841b0100c818000c0c07109000f40e017880030600001c1c010036400746034404401d12101c4030b41d2002000710f52040b102c1410102d000070f80f8a407060021401544001c00b414940750407045d08030540725841402803210000d9454690282d441000b841d03005c5000c0865a4111800c80c0c202903018180040c4902000c00d100d540c0607454030340444204400b40c1c2c040d54203800120070401c07207603030501807802c0c034900d0202ea003421400c1560340c200c50225041402516400c0d4a00011044c0e2200e0340312034011508084049082e081c07805000c0d494039002d02440e801120a00008074010710000101d480440d1291a58509000d901c038070b00103a5041001c0c201d4101c3d0b01000000086041002020b0007103000301c0c05171502c3d809905860000000200b01e4020003482e8804115460713801c0001d80d59032401900741a80c0c080002d2400300c000741542020340030000f2100300c4020305075607810000101144150360400c295198a00c40840d0464500c088100240c020005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 608247275 1250 608246025 608246039
    0xc050a20010e010e15060117070309020103020f04291804050402040603060606020d11010507121e05150310050c070305070503070b0415290625051f0b010504 69
    0x11400414240000804900219140f802d556942484803840c1d8002801c143c1210740080140703400a80900303000100c05294a010300303000c0c000410070b00516583d1030301c04041d64000d030102da201007004c0c0070342c507a141d80310100171860b1103034803079030040d00e144442011010182a80466440340003580340724460000c0c0d1010840980801401240c102e52030340310010008020340281c05c0603140310f4002e0710b902101c209004103084083c04c4034401d1f0b070f81880c3c103000c052a0441c080d955695005203001c50075055526901e2001400c4a030700c3c0ea9560f15001c104400721020a03034400181c0c00071019036128139400409401a00c3c825500e00700c1d5140b00300072100010303010b0030003441494880c0c0c007524141000b0340c0300c2007103520b000c031010348005e404540400c140b064203100e800c0701d03946103805280039007a24040b4503051a0200410600071180020103c07510030b060a0510f05081c0c004c3d005400d00a0a403a0060321191703501d2074000c109220080d56a501030f55400b401d641c030034060351054101450210 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 608248525 1250 608247275 608247317
    0x11d040b0d140319092102010c0209010b04080c0108041208060d060222050105070c05040b0609040615110f060f070905060309010e0715080114030f10050a0c050a 71
    0xd0256000030000d0700d1500040a142400303070080e902c4005544c03980241803820090380e04440b081c0080100001080c00600c10944821182c4011140e0480e030740081440140d4002d0b021f020b0103035000010000016100c00c2820080040c1c1d4000c400703581e82c1624083c01511140c03000d98004007d1810038820103440e500c10204241d1040c40200305402c40403a9844000072a0b200b000780c100e10050f078104181c10710400f649003030020300d070a01e0035a14140c143d441c2c4450441c00d40c012648242d0303c603c05048566102c80944144200090040210a503503501c07404000e41c404803c000801c0d500014020f0b01d94000c074091101d0b80b0500e000d003400343e030340c0307150001301c044020404c0050058020700440e4686a82021310710450200703000084254500c900e2a2a20f042d80d40050501400f0308400c15036254800e01e401c0c110b482c604103419211500c1d40c0003900b00000b00d08030b40721078420559403403c071384047e0304614003690020400304072113601040c5c2120f107480780d505103a004ca0540c800341402410400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 608249775 1250 608248525 608248541
    0x1e180b0a051c14280b070e041e0b150307090b07061b020c03060f07050708070c2d05010e1804032307060b09040c06050304030309020a0b0403050606011d04 68
    0x68584121400c0e0b543d482c480d0201480c52a0007a51080c00451000d001c010604002d82003005680d4401c0c1ea210360f40d10503854002071043d0204814510803035400e8503035410821019820300301d00c01c4c40c409500c00d2140240240740400d449041100003650a442c46070b4103d0b802039609587d8901c440d402e0031480303c41903102c0b030400c86803560b0758401d4080d1001600310ba003241110343d501900c030000d04502054503182c0050464284030880a081c05410b41d0400112a02c5591195003036072030341540e041c00846401154414005891040e905001681d404403d4050b8540301c0311180740c0c070546640045850710000c410300c0390801501c407051180c00c403290b00c510341c2c010311901d48a02c40c82080c850241d0340d0038441e50390b44041c13080850040100066805407403095001039403840c0ca2031500c1d443d00100d45840d445080144a40080454141807003608400403643c1c0240402900944e551302c0241da990240c402074440e8010207020403250740c464020480301d8004510010b40c414000010400100304403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 608251025 1250 608249775 608249809
    0x3070f14040611060601030b0a05151306090f06080103020f1203210a060914040b0907080319080a0216022b120e0910030308101e180b0a05 61
    0x810042000a1101004001802407a56a4050f0510382c4408a1400304040d000d28149400e00d50100b11548600e18007808039030f001c48500c01400c1d081b0074840c46038803641c00d0f041407090b810200428000d40080226044a41001501707561755550300303040340d60708028007000b580400c2c1e1140211305441c00048070b44094084005581c6800b0011600c80c0f42d050311141018038820303030282000303603e1004d44035801c02882550350511582542c90f101c441034100045c00102102898000700c0d11071102007203d24058072500041302e64585030014142e09020309070b10030f032002600100026040122500a4544212b01ea0f028040703031000c19400c104080a01110004028a044803945000c4d80f110030030001043c0141202c4100d01045480100988292030b40d1364005d681c1f100c24801252406600c0c102102d4052924580303903150b658600d440701015a100392540c040c146040c0075210701490344c0c030044030303000101e0306280c40102c1c08800a841d5003019044d0304c2401500c081140341050006000c0c0081a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 608252275 1250 608251025 608251037
    0xc0f08060a021812151e1602010e150609010f05060714010b1c060e01020405031b01020a1202012301080307080f040b1b0d02011e090c081b011e0503070f 67
    0x4840d001c60560f41407a42c01c50f007a540943d0302c5c48500e4046451040e000461070000390341401c81e50880b2040a00e010304200b85489560b012104071510039840621405440070a68054041c5a4041120701c14203485003481401d901d000042c2c1040490070300412223001030300132414007030742d92900c1e40030020b000c204542c1c6540300c511a601940d182c044001110042060000000c80d290a00c00216541b040025026a10421007801641ea002892580da03030340b851707902c00c1125071500c0101e00701464810010f00d1a9a90040c00d8040b0380c040d040003048240c581c102891001c4c900030801ca04480170302c110501500108152408140e505005105e55030032404250700e400c1d621520b642040d88404440740440b042e504c1180b0102105005030300341c50440b03100a011220b0b02d4000d4800c1c1c8442950204485aa11340d041c0040203020740c03299004000c8541603070003003100c0d100000003622046c080c41d4006003080d1615094850f01006044084071a9500c0d681181d8a0140036640c3c1da862007503044c18010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 608253525 1250 608252275 608252317
    0x60f0709060f0c0501200a0e0402070c0314070b12061e0105030613060506030907030209011a16063e193f0612050a170913090c0f08060a02 61
    0x1450591715030710404032145031b07a47e82c11054020141c0758003d103000d1040f0b004003c1040459420481082569080220310344908501c517442460402c15520017403185102060079001c00c0c02c400000f80c401d034000d640410850400c0000301c610b2034001d58040c2d01043c01400490301d070307040c1825003841d945c2066400140268503400011402e41003140d40c2540c541c000c440a2046040200d9280d004044000c8442181c480111540b0b00c580140041c04290807511030101c0f052140d503810854641036500445094400c4200c1032990440038280d03086115214920b0710500840c0720411101440009107090500804545040703969180d140141d94022900400100003424540700100c030a405031484241000103004211003580c5031940003000304004250b0321000b2a4020503e044d600e41c3c4007a4001200b0b08801464402c3d010b070840c1e03d500540252000b0b003100103180d0000080f1070048134502c1d0402d546d407404080c0c103042030050340059008100072811071a40368005d032024800000014500701 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 608254775 1250 608253525 608253551
    0x90a14010e03070f15020d0903031d100c05010501080309031506010e0a06050c060105093709060605030733050405040f0b0a150215040212010e060f0709060f0c0501 72
    0xb10098111110f1640040d40410080f407045400c40c581d045d46002601d060000d010015103240041c1c4070240c2800364840d03550b640e4200e8103040d81121100141208614216980c00030050148844111643d600e00000810403910000644044280040c0200810018084010100200900000d05003c0d82008402550703035411000b80c041c1c07106950b000d4403580f002e01680d01c1c0c0780040e80610b0041240c0ca090280e0b000c10784043c0e41c0d81d002126400288a136880d016500c800b40302c1d26a040e207544c40c080d03000082002030742000007150821403c4415581d02c44070701812503500c0d010040c5288140c41500c10300035003801c1744200b1f10805401e01030708182d500d50228094808078460101d4031030350303002c00b41d100e85400c0ca0864003900c42c030310555881d0101400d01a644042c62810491a00042e4000508565904025901404156000303104405050000700c0d81d400d000e075466250303110101e0025120511841000c4120741490f41c90f2305003007481200a03141020003d00544941d502d40050203c60 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 608256025 1250 608254775 608254783
    0x32709040b0901060f03030e010834080a02040e0612150a09140f10020c07051903031d060901030c02011416020c0402070c0b0313050105010803040f0902090a14010e03 73
    0x4038001c0400c0c8429240035640e041c2103950301c3d0006001e1702001c54050010a501814009a844003824408400c3c0c40b0b1828050507140602030450300c045440b074103508001d0310714001071440821074503008850f45031040d0800070b80c05907005081c0e01c0e00e00301000485c0303443c01c81c212000240002c02680c04840342c9020f1108c00c520121007020703995450f54001e00403c40c440c0750300314190613100080c02c40c4d0b0500c981107503100c51007400d41188241c0c01003900340e0ba0790010720204004100c010518036924942524902c915151844180c011444e421b00c100211100066052284000113203036074989000703034005400030102d416400701150b507542c1042c0c004135480c40340580200c6255514038085801c0d42d10082c500300d00c812006024070b0051203540001040c42e038901341580c503032003000b079220355800b40610f0300303411040d0015000d0f43c281800012805804001041640d95101d01c405c1c5450300c421000090740704410b104e5410504038a0108105200842100076000d0145846c10035695414002440c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 608257275 1250 608256025 608256031
    0x1a0103020a11010f1e0504200307240e0a0605040303030c050f0310050f0d0507150203071a1504020c06060405072003030115170c130312020a120201020408032709 71
    0x4566036a171504810841c950350206034100000d0f60078032140c03605544e035400c4074503600711442c0b100c1e074a00a91400eaa80030300c0100007410201c038072064050485000120003c0b9144090408200c42c10404041402c20345111030a075002070310755500d0170340741d0340d0114000c02203c2c101c0020803001384054000f13200100300070340c0944d20f50300401d500582400e040100310051141e910b4462030024071400c00080c1c0100302c0404030f410a94015664402c4007100741d0543c03042c000003c00410902105125a4648004075400f404c0d88040c89501b8103503450a0108034440c803112010207501c8603000422500d896049994001c40350700d04240443c81c0300446401d584218803402c08141c101000500c50400780ca80712a0386691f40b0315000680030706021403840c01000142c100740340280d000071110f1502c1a1000003500a40d80081031460740f01e040c04009448016000040314500485c2e103040c0301c824414000d650554002a02852030808010503070500d40c8041d607e00705441c461525505480d956002c0c1c1284 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 608258525 1250 608257275 608257301
    0x12031205010b0a321b060403020706020c0603040c09020c071820070206040b0d02191116080706050c011103010f18061a070206090a0311131a0103020a1101 68
    0x2d1210904140644032a44003c0205001e101c00d2a00002c0807512440400381020090300700c50f50340d105c00760610001e081c032040008042c482c10050004041e40001d0b000304440055081c2c074548000d66041115030f10081e81d001e070062041200c00d011208055000300414410318013290b11080da122540c81248050341c0c0044065a501d00c45983d408a40c16a002200c000e0302a20034130700007803031380041d009008030b01400b034070b02c0000304554141c844039604903001c40e07103070810707100c13201910580081c0f1440065a9904883c090b54660340c070303070400b401781290030764000a01814115041078812038258101400340301d0150740b1041e07111114042480158060a1413258035000701e03040030412103404115580b02800c807841c01c0000c0010203045c0c0f500c1800c038086a01c000d0b50354106400000c2041c0203844109502086040d030000400003000d480e60340c00d5405581c0241c21403c2503118108464500280303100003c141903c8a150358825070003019040454144030840b4181e0b00106800c45181c1035240c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 608259775 1250 608258525 608258527
    0x80f090f0a08010e0c0604030512070305070615031a06030c10140c06101d04020402030414060906160504030b1303031407090614030105030c0d0203010f020d1401090b090112031205010b 81
    0x10251304000d001e4001d20020a9a00d645400d1559441d0703071341d17200c5880321902005004140201098451000c80e2421604284240321044012600d548001464441260745c2401075400888007582034520700c2c800c10300107028000c40c01c02141804124444401c44004105180c1c0d594070300c00c0d41030320240000319500d4004180d60324201545030580007468114405071549030074481d814581d40c04500e940164160740151302c03911a403800c100040c0400004441c907000c4e08041010142c4001103940c400c69188454003080000d02d0350580e000e10403400042d0000041d2000900a044148a90342c4060322a280001c0d211207010040c1507142c01c103131129000210300c200308202c0c0399071010045020082c64070314117186514205c00260f54660100646015550040c00d01e015503a00303501018888032408025965287d0031b540c1f03c0e00812080c0d40701c1700d044810b2000400d0110f054440d21f010f081d07010f440030795181d003000680c44440d460460704400f00030b458011080301e4030403800b5141c000d003104501c803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 608261025 1250 608259775 608259791
    0x705060703110106060504030c06030b0f0a0902031b090d020625030207060801080328020f2d01060806130807021806030d0f08130303060317030105030f0a080f090f0a0801 75
    0x2c80c1c25140715500a03010418140700c01d00206064650391001c0b80c816050000b0f800b10460003040f0203a600c102c00c070368004040000000c0e46002e507001141300d441c04600c1c0c844520780304407030342e80c2501810004680140210741c6850042c00d0080040640a956940701550000314481d14004049170070011001600062410002142c004844901500316038001e1820503000418001c5240700c81144036004001c0c8940b01c48046000b885481070301c01c4158151f9a2001c00d02001441e80d00c0e03001e103600c400840c0750000303035165001072080c0011307604030307102611664444506a0703000c600360340c8d0141c03002e2200300441001641ca081c80041140804560f00c1c681780b500030201401c103101d0b1140d032018804809060a0300b65071164105502040e8080f440c415042e240c10102d0040c8001e40004100034002c0106a001c0c0d240a4040c50484000300e0460f540c0c02e00d000f000c65250016841c0041410b0b81c140031a00100d444900038024081000d851446030100300c10019a40200382c1e48441d40b0341e5940e80e00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 608262275 1250 608261025 608261057
    0x110d060c021005041e11090106023a080402060c060106030609050a0b0d17130902030108010b0118060c240b040b030a03140d2a0e040507080a0504050705060703 70
    0x40851441610508104602d071a444c0e074074000302181061207205c1c807050051020804095644c2840c2c11018080c0d03915503850316000396641d50940c11011044032445c600d90908140d0880c40d0040403561500301e0b04010b54008280d4015034040d02c100e9001800380680005404100030580c020845035801168135441d2404640803514084c081c0740307055080507079861032601c0d424080c0700e88a0344001e00c84425030740b04c81d00d0701c614003030f444503914500000000060700040c80d8000d035050b05d01c88002040018600001518104914940c0020040e000d8902b001454002d103a800b00942c004e00d5141030302024009203040025140c0e01100b115507442d1421000e606003441056030144043d002850b1b001d034507850140650030b00110035030410b500003412291043d00e9420a031283c01310f02c68511807036820400409840708004070039070005805512901214030345801624080d58294035920f040e42c945900c48009440010300a270354034441c0704800a03c40d1640d40c014070982d4080da5804003502001c4030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 608263525 1250 608262275 608262283
    0x212010e01080303060d110a060201091b061e09030605040605270c09041b030309170316110a08101a040e061602010608030406030204080f1c0c110d060c02 68
    0x8146054100c00522054400001300d83e000001100d401c6140041858603200e411210044290418404130780003038070b16015000300d0702107440741a01e0b02400f0ac03501e500c03421010301c5101d8030b800101d20040800030b030011401c14280c007006628080a41649a03204c08040d03520648003210a00d17940d004002401e5045401c4140894142e02d568291030801c0f1500303643d41d5038100845104141d420045002c0011607000100c012450450340810250b41e410080c4c071244540c490b001100c4220500d0003071160001c0200d8880d4040b0400b940500811925100540200254201d8104114202c0410f81c071204012036041403a805c80f000c03407011815802c000090070010241c60055080581d14251118041740866000c009024140089042c60400320b001d0041136000069901000030003181c1c0d107915400070020782e01743d03504907010208040c0c459a0359600138042210142c461101500d4400e11440440740c00d83c0c01401d1558071072125500090888480f40411650150343d10141c210054041c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 608264775 1250 608263525 608263529
    0xe22030504090b10050a050f04030f080702100207120308041a010e071b05060411150c1506181f17160e07140901030609020705010b0f0616080c010618021201 69
    0x6180c030725001c02c0c44c2c0b802030500c2c002c401c0c41c0014050003103000c803d003035118801e4400654201000036001c03031440c20300390501c1e8809a8241d02075200283c1000034540001400ca044440c1d054030504c0c082460f440c11608100003a20459510050006002049805200b0a800780204190081990818601c094180c140e08801910080d001c0841c1e100440c0c804170f0043d50040e00160b031201492010000201c400e40070b041c60014000000c81c1782c402c81880002c41c3d89000203024120704294581804000361350384d81071a404440c901c41d200151001a1903108507a03255001102c403580c444c1c407603071016820b00c07140d80d0003130b0381d58056076440c00c0400103103540b90014803901203241003a082564000300504024140d0305d40341140041c1084040c0d01c2540070358020258014115240c84462810b54041e000c08100c0703901c54046030200d09c2e880e1030f01408a03a8108148007180802c5000343e035035042c2d80d41000420942c1d40d544c0303000c0007500041211603041d000204c4c040c01030b0f441c0004103000e10700c0a01a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 608266025 1250 608264775 608264779
    0x90d020f010c050306042c03030406050a05010e040204090201110f0a052e0c09030209010306050609070806010e091302151b03040f050d02220b0301061502070e22030504090b 76
    0x1051031812182d8010f421250400c000381e43c046414001c1000ca512100301000c40c03611050081c20b418a0882d00100203907009900c0b521052041fa12110f454100341c5800380601d8001240400104005140c82e512800b90684103040c4a501c071001040da00703050a001c2d14502c8000d802c520304040c20003200b405154160303e0f400d001d2002c024a4000049507140300725420b0030609a07940b4000d108140a15540402582d00510603c481d603100c5c41d03d00041c040564001c0d01804180c1c0125202d00d002d5070f8100e101c0d90301a51903625841d01ca000304403c001002d002c43c1d100b10088000480075840701c150f032407030001091802c0381d520350b032000032612000030a044001c01030b002800207020480d80c8014580c220340048916035244031250000808112240038005501c459145c44110400c1d00342e0050707900b0440031002044500e95074008061114861082c40c070041c0c0000a0074807100d0398410700705030800c145003419841c0e480b5012558440290818080d000b28501140801401c1414050310f140f080d01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 608267275 1250 608266025 608266031
    0x2010b030c0420162003100902060f090d0605131202010507120c030e011b12020913020309030708181f080a050705070f0b011a040b07021e0603090d020f01 68
    0x10300c1625070389200442c5403000250700020707003001200c040984c0070415600301c26508865018004900903018900076894028050030104400d01c411070300c100307020503801401c800e18003500300103414500e0b40300307208450313014001000810200b0761030702c60540f1441c4180107000c4001c40c28105400c2800452403040c0c110381c10841000342c83c032761246100100b0b01a4841c003041443c011101507002d0030202084c20419841e241000078015005140446241e600303031513231000c070381104540e40c069200380350595402070f0300c000c181401540d0076401164020007103800d40303040440580d981e65031580b1005041010300b0040f001c1141c14a0515900c190040d44681c0c141d01c0c1c0100c0c00310140c501c010040010246c00d40e100300240c280390042085444050784000c4481485201d450029851002030094500461103207440c403641c4c03c91441141c1c1030b01d100c0108281440d0b00c950170400c4a030540c00c0c02c503070381c041c40042c9400b05446081c05180101d00d01e8000e058440280f0400910b0800c0c035402109007070381 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 608268525 1250 608267275 608267291
    0x1104200307300605031605130e0610030308150618060f0d0615030603030219140706020a1203090f061e02031806061e01030e0f0607051305010c120309150c02010b030c04 74
    0x1003007031b80700d408660090344c5106290424070a540020074011380d00d860140290740c10080110300410801041c0ca00c43d89500c44244c64100c0c1c1c59850b007009140c1d594100390100700082111f03480500c10b007003440000340214600f185222084c00386d50489811080c00ca40c4031700003030004210106450410030036030325081003201e00d1a14000c0d500c850804050803290015030485040c810f58004504400108a00322001141c0da540300950b0b405015105541074084802404900c620038051100310b16080039400e419403419465640007442039482c02e00040c001072030041d41e80a0300d80040e42c80340034118400484405800442400c0c0b41c0001e203d244030300d8400c18504c000302c0c2400d007241134000081c600020001a2003d009141800c101c00040251041c00c08114800303a000004285101e811318080b0f052507035030300c0159404002031500500d01c42441e4520180c05100e07030b102c1e0017a24094400700d24900d000c80c152004441003500c408005035110220150182010040754203219419102004428 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 608269775 1250 608268525 608268553
    0x30c0b0702060301180f020c1b19061218030c02190e0c0903070503060901150602120d020d021308011a01080f0601030b030f0d0309110420030730060503 67
    0x110050140d0883ca202210320035601000640c0310013006e05600c0011595000c6420f100c0e607580028005051111881c1c242a441e0717414003101d010410030030b04200c2484942000c005644454240708001c49140d9074041d0f00705035018001088000d980a0380f20f039010210b0074010f01402001c8194007440c00c258540342004000381d0a0001036002041c0002c16071500081d01c002428003207990b01050b0305200d210148400340704103501c00c80103c3c5188000b0000140c0d1140d0070f0340c82d505201403240d03503090f0a1003281444103d50300102010402000014a4030701404202c1c00340c03040300d4000c40c03242d130741d03c260308200c58540c4040c1000e00142400c10030064a080b9214030000c0c41e00518070741c105074030342c40c5904040e1010045520f4007502c00c02a190b240028080040061103206403d0b901c01d0030360301160220b82400d200304100c002000b07041d0100c11142d030524030303166880900040c0811204107140d018041c040007070300184011420748040101358042d004c0050740c07561b410841c82600444401c0b0750308 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 608271025 1250 608269775 608269777
    0x9130c08010315090c0b1216050723150109062916020a03060b031009081204020a05040204290a080a0f0b06070b090f0105070e06030a020f13030c0b070206 68
    0x50368850f020000c080c4050b042c40002d4021510000e00100403800d0110310200894007802034011032600c0c1c0c50095407030342c940031044400309812102040c800c101400100c1d43d60290311004491a041c07088400d048014a640b900d8407000340c0003400b03c0954018080c08005005442c002c241500d02003c0700d0010f90300b41805262159070598240d4030019000c125140c261014040c031640040c5088840740c2c2d40e040441c05840601141ea1080c09901101a180c0f4080e1140040c400d801c8141c0c1800d00f40159401c400800000c0c0099034040d1308485c000070f0541d9240000c001801c18100403424480020008240841c10b504103815036140c248080034115510640742507200000c86030203c0c0190300d0201e500024420040341c5500060700089200510000103805030250340c020302215010071078254039070700301c980c00d8850000051245058080364913100001e0741e00312800344001440d059031142c1c4801e84ea03000c40020010308000400420500400c4808100106002201a4a8040d41c1d500107522 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 608272275 1250 608271025 608271029
    0x310050103380a08150112030806090711030307110c091e0a0b06070317130507090c0e09180d050a0203030601120f0c0e15040f051c0b0c09130c0801 65
    0x251800d29000b54200311001007800d446400301a090b0b00000c0d46540315140c40710310300b043c0342d0b40b1071520100008001d00c1c441c030308240303136038165a9a40d041d44030082048400b0a000e00070000304403140b110058602c1003440198010b81c8030707403070350007190700c0038048a820b14404543c43c0d48070300c0c2c048042004440301280c0d49041c1c1d044010300c1c40060b40e00c0920100046c4003c103405a00000042180c20416030480d203080d51600b40e02c4450a6a41d85098118140d00c2c10050020401d8004c0d001c00c020704001d0b6040600c02c2c0500741800c241241e0054041750384040102c80d0b480ba241060001000781180038020301e24a000070345000ca1034551117150284d13a80c40050305103410422400740c2c0c05004800c591000215a06102061001407006040108203506c42c4090724410400240403808440e0344000f141e00326001c0502c594556841d00041110f1354410b030307441d99400c190004c194000299889200740c424040251303030646541c8020180050b424619594604281c0340041011019411612642c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 608273381 1106 608272275 608272331
    0x15081f0e010c09030201110c0402031e070809030724020705010e0f010207020906040c0c02060d0c031a1f0306080f06010302150f030a150f0603020310050103 69
    0x401c82d0440441d00700803908080007000154010340e00401813011020513101408044800708051341d10440e60800b0040e01a0070307040c8140e410004041d040b100925011000f0f2030004181d550b81d100d0040040d115000e065141104244031203000103143c000307541c0c19501c545851a0071400b03000d40d00710240a0340600b55007280c0851052080c2da04081c4c004280d100d00781c8440b01030000601c42541414200440706c5c001c3c40160b21610024070b40380200700c0c4001411480240010308407101d40b4031104a40c1c4212100515503903400703140700101103554981c40e00087c50b005041e8010811548080300d80c0c040d59100f4110b00380007045841c100c0c3e0007981c400c80d1041c10402c009807507224213101c0c13603141d000502c00b06500301c2e4694040030405009000012000e521203280341c48400d5652312800009400004001c0c00d41d079109003010084c44282814084c51000f92403182454914200c460 = true := by decide +kernel

theorem cover : BRFrame.Cov 608093525 608273381 := by
  have h0 := BRFrame.cov_init 608093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 608093525 ≤ n) (h2 : n < 608273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
