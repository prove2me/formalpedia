-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3743
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:33:10.684686+00:00
-- url     : https://prove2.me/submissions/aa0278e2-e4c6-4477-8a7e-2ef99a51f47c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 673021582 ≤ n < 673201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 673022832 1250 673021582 673021597
    0x5010e07051b0106060203041d040b0a05090111041202010807021603080f09060c071809020a03060e03210702011512140111040f09050a0501080d11010207021e2103 72
    0x20100180c244218100c82c80703000c5801d0707503100080218940b2007102a54036802406450351002d00d00c503c00e2820130b14a01254855540003ca51314070b511081c20300c031301900014010002075500c80c0c144900300707200c20018100820340c2003a00d070b400403c5800058034501c00905280c00315004125442000c10610300504100c96024003199a03580000c3d5881d0280d00072042115405040003424200a0000280f9031040e10b5095014100843c1e4080404d01203d01c000702c0250841d942d501c003000483c00641c000d0851011110035a1700c0d00010b000c554501011640d000703104c8a410f4000d021250380d0910504000320021084400311070308202e070304810b000317032200c00400c0510f8960003040d50700c80a400c000e0050415080c001e071110703211854030a02081902480744110b152a0000d4a03001c1140502812074040c4030107411030381d040f004212201743e004d008100703003990200402d000684407011515a5104526003071009403c0071000c1050407101c5000201c0141407103280204c60303907000300445004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 673024082 1250 673022832 673022837
    0x1b0e01030f080405090112030306090204080c040b060c03030c040f060305040215070303060314101b0905011116090b01020f010b0604060c030909050405010b01020f01090803040b060418050102190305010e07 90
    0x3210407616000c29544110781081781c204064100028018544c0b4288407000d502c00c0d1002d212158581603003404900840c46040349961100303025100350308255111040e1008064040c506d1700000d08038082c5140c0c41903903526260040040d0800508148200240182080386003e00186c100341c2c0000300022404051504840000a4100c04040c000d40c0314000940d0310140c0100d031125501c03c09500c40350b101c132a04c0000b0f410104400d00c0d480c030416003481c1c034054940341c1007001c85c10103004440400050b034601117180700d0f00c010100160382c40e40c000790003000456404074410000c200020b051010682d0350f0308480c1e05010f00a0902d0341c071841600c003035036401d160403c0324803590709089500e1078960b0302a0300110326080c10b000a04c24103402990004800382c08540c00c010281160b6400c03142c100c44013502d5604103202041c0010580d0403000d411510051010070851500c51886845040e1224100d505a6002071040c0d40490700c0d140041c401c043c503044c02c00840d03142c00f15002c41c1d014020011001c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 673025332 1250 673024082 673024103
    0x80a030224010e060d020916200d03020705030c01020706020405010306051e0907020c0402030f01030501150f03121e09050102060105220e1e07060219050c040903020c040f091b0e0103 80
    0x103060711424114176519400900604460a101101000105503100c100740060090008050302c002006000c601c0104000300601645864600480094201e10300840d2a80010407510440b10030034005031042c2400740d003006aa9a00e0032001404440055208600542c0b040d141b115558202c03020346100028285c98890740ca54551300121304050341580d0450784988040203001c840d540101c00f031f505981c0f094008000c5001e01e010580c54415040c0304030900e00001000c144005041030328459980851810a0300030490089920121504076500320800207503405010481c80d81d041101600502c1c060301c50360003102c20300702800e40071071300080801441038a45c0794501c4031000030060000321060500724aa11280d0018803152182c10b030b446850010300c031300290105c00110b08003025200d05d5018009000c4100010144800790244000980550049440418482d00c4a000d6040c254441850000382e484007031030a0803000045001200141006000510190043e500c0441c152a0444440d45 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 673026582 1250 673025332 673025341
    0x50c090f04111c2f0a03090b090604060b0108160e0f0405010b031608060f010c050c100302120a0c0503070c060605030a0602071a040c1419080a030224010e 68
    0x1c01600e80501202c41642c40052010306904101e1000c50500c03190701000e000e0840301e0380c601c880715001140c0c0740c2d00c00c01c1c0500c040f0610850f8072009000000e4103040215030480c02c3d07100c01c500e5110440e01b6904542180040100b040700d01c1c42407440c602c1007404c20140c2c60810b181c1031f565041c00140134a06102ea9010800302d1a503c0c90300e01010008000c105124035a1078401c004d086800c02c0d1660402c9040019010180c40e0042c3c4500740319400c082c02603007040700d101c0d0044500f10410320040d0342c0c90141281c5642d00b078940c0350102d00c401441c2d03100560b50310104d481c82030f41440002c01d2074904a10b030800b489443c983c44001c6079088009860114504001814038400901e41548003d500d80f25070301c411810420150043c2c01194001c0300c03a03002d003200070440c0800040c012035000303000d040b850034240030f00700303031044050680000903041c20003001c1079905100b41802c02d90402c0c080e55024000e5a0209941004111003e40c010741d00c0303400f070845414001400b07034810300852000e071080380c0008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 673027832 1250 673026582 673026589
    0x91204090c170c04210201170a020d050f07141201031101050c03040f03020906220f020d050f0907060f08070503060f131401090e07050618030d02160603050c090f 71
    0x60804003496894940d2410802c800302140d90181c41051a0440d00842c00c244000200c428490303140d8041e1901c6002c800100c1001c4d403141d08c0240010519075080c004140714a4044c450580f00314250203a4002c0c03401c101001800d1311350348055011414200f00b203038102a11440c24500e0440381d215051000300c7d010400103031041d0041d0800c1071b84520001c100044d4080c020401001207a00a540046454a40708184004640351303900e002d02100044034610780c20800c5034000c00d109002d00e50f00600308041e00a00c038003515410f444902034a40300c0303000d10080d0401840864002c010a0400c106940400040070307101c510020040001c2c8040800040d0054946594a070820351004224010721880410b0980040c20700c0c1c4610407480440c1c2d400854071203158030807528030102c200010840d0741e1402d003c00140360300c9041030900701d8460541741c1200d914100484000318443d5001741401c11410a480903000041c0c0c3d010070101420002840418003041c402c480003020700350f484940c80f01654011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 673029082 1250 673027832 673027847
    0x11030a081c09050604030c060c0f0c2d2f010f0315090507080f071803020f0a080a031d01021b060c0f0601060c0501150303050a05160206041706091204090c 68
    0x28199000e000100001c00da1f0002488600610401c01002100002c1e40200c03000c0c6c0300e49012a020642c519116004a46126029641d6480c4400300740d40070b2001005142204504110840300720380300c9010001c1240c45111210454692604c2810b80702000c0707070000742900c5507403541c4424507540c3c0e131200c1c5030310b0042c007c0c14020b17001e0f202091025090011006081d050215540e401515606001c598241d11401080a640a070180200c00b554190b40804c4072244e55419050742c00014002d000400e940c0600101a00500035100c48503028114820005190050680c0c1811504070388019005012038040d40c0e240010140d540315150540f00c84000e18115004024400c1e610075000001800c070751061015007501e01c44c0d802800480c0445540410a44e4a0b010080100c1e0061042c001010720940c0540b89110320011300e4000e81105030041600c07a403150b04403900780314210b000030712081c40410030240c11002a100400c21a046c100115509010754007a0180300384d215051200d80501c11301e01d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 673030332 1250 673029082 673029101
    0x2040e01240f15050403151b0507051e1b121005060a1202101110150f050301020f031506070b04110f0906130b01020a05070807080f070b0d0f020403050114010311030a081c 75
    0x23040030414031042c001402c941c000c01000c0b10b040c403d2000d00841031031610102c2c8844c10fa45801400e03020030501250114620b0050015007210b40034401070700088003003002c1c1240d40d1654500050303c0c1441d8040c0100b121080d0040184810000d0780c410041e1224a80200343c21301900c1d00080c44100e486505050a01c6039001a40081c141040c0080e42031a0b40f072003a040700c2c1541c5032400b406565509050a034001c0c600d030001501414030018040c0588800580810300300180700e5840c003449a80c800100d07040c10394094800c22600b00d0340106a00700340082e400b040300c049818642d2803400c140001c400808030011351900d00e89491005980303074001c120300c06031940e00c10b0544400c1c5440794020b41e07540000340300310b1045202c3c941200031064400b0510b030041d2002640c0f05498180681d0441018218044030f522909608100000120b0000e10428040e210707100403e003825459418040e54031050211014480d410641c0303e8400900c1500403070703180101018103103a40c0d0300e00310440340c0104010741c0e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 673031582 1250 673030332 673030361
    0xe2103042f03011b02060112030507020306040503032205061b09120c0f0609180907090e0a02030717030a0e150714060a05040206040302040e01240f1505040315 70
    0x3030140c40c0e480c210041c08920404168001c200c0210300040880000c00708440c1c00303002da048100180510b401500a4451550007821b000b850714180da40828a401d40031a42610a41c0010041c0240000c04500301004200501130301180704845071541601c0300b0015040300002024248241820340b028820741c3c00072a40100561003075820035100c56201d08400c00414030402c0b07a034440d441d43e898994203903401c04002030a481c10300c0c07003010300201000c04068407070022840341e0080001c1071011406541110b81d1440040d14078a090fa106162602c411a00507008000742d40e081403000401c004250f6404411b00d15001820301d00310808604510440e03072041c848000c2c00a00395062140401d4002e030149081d004a5080d5600c80550408451b01540c000790300c80420003007080503103016045030310b10002d550000282c1c0b00b0740343c003032148441280410320010328280a042200303c41032a81c8000910350000d0401d80360f80000c000a0082c0304a0000030043e105407555045044295400062400c60f000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 673032832 1250 673031582 673031633
    0x130c0915020f1501080a02060313120c030806092a090a0801060e0a20280f030606020303010f0303050c030c0706030b120a230c031603060e210304 64
    0x694000b51540241d1095014510580980301c0500000c10740b00d82c102e0380100302418482401d6420050300780e20182004522841240d483d5020964501142a400c556500c80c40080c266618000d02485c0380180140d210b42d40341000c00990b4103408e016012a0310945e840301c011940c04068a02a902034602100e0f04449040d80200e1640b205501442c00d5911012000d0419500c058424042d941d048403040010504c0e6034071080070141d03084c00340030601d01f1050345140191051030240c464008035a40074000640102030201840d80510441010300306030301c0650320355814000318005803034032480001c0030410b0025190044020500644100c0c88603034065611003950390030020060030805074418840c4c007082140c0040d104000131800149607004221503040401068182080040c0d480854001d000300070041c1d030310f07640600240e05901e1280850386665411030600c941100c080003003c05d81030340200d004201d0360501080305616008010360990781c80d641c1e81ba01c0100007142e00f41107224072001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 673034082 1250 673032832 673032869
    0x31104090e0102030906090d02032d07030806100f170408190305060a06210f020d0e0f0f012c01021315170105130e121207090e06130c09 60
    0x40d00213501611143c000c0f9400307034407400368654940040c05c5000001d07030f004000c42d49080c4013481600307d40d484c8540289902c58189461030302103621407282100082c044600308080c034609007550061a03411f500d0442410501214080c1250269001240c1340640100c005010001d114045500c541c00c22200140d1320510503101501600007600d2882c81072030919800305000b441160901e4501352142c800e4201c0d001c7c000000c200400c0b62100c1e80304015000c011103640c006241c003c0680b15400c040c010400400c1c0d140e0f1032814004199900122641007081440700f042c040000c8000c50f5059908411170460401d520f94024803c80640007503010b005940020030f0f90142c20b441c1c3c5809107540720008511400c003184241540c00740607455201c42101c4100d08440d070581d0080e010002c00c9030868080020b101c0103100f907034210034036011040e4502010054007990000000004001b00044c1044504080000443c00449100707550201075a50041002035441412244010700805480034241c041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 673035332 1250 673034082 673034111
    0x803040807060e070f1a0406080a15060203090406080102040303050304021509040c080106120e07060315050402280e0915011b230c030717160e0604050f040c050103110409 75
    0x540d0f00c51142d101d410100002480c5072402d00e90046481b6480c9024901414030b07005403100000901840941d80d41c2d907098801600c20220031001030319003500119141d000c41010807003698226048602030b64011300c41000000d0f009070640e908030703030304640b035180301c01d000400d090036406214159540306003030040d115140d40e001610f281c140c96542d03031040554140e031030301c2170250b0745401c10b1482c40360320650040000fa88240d00051001c000f44054100079680e94000405a0f080305003100e02070303407205602c05280c40310703541c81c409811240d050080e0307034148017400182c4080c4001c156220798480540101601d0303100750030003840c0d0020000d8041c0c1166490400000c1609403425028010700e440008030380b0488000790042c0c0d1984018004c00c1c800d07003460100840c1c00c8070681d0310800c0340301c0c1c007074506a008041c42136000034081ca180440000e00d080303420081a908080c1500c4081c900100034400403500301031405041d81e4080c01c01040008446022100d203100b070764407805000340f0f0003075414001c11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 673036582 1250 673035332 673035343
    0x12160b0c300118020403080c010b0109050111070603150308160308011d01090c1701120b0c03040807020f011211030108070618060f1e020c04270803040807060e 70
    0x100c1421403001101880e40241c8400080360488504078080d1100400102e070781080c0600542c81c01190143c00c103a507039070340c1c4402e5403c4841072818070307510b075414003405590010301c420050909291134010b140e035817046562aa1301c0e6000c2c030b604154aa0b801c4c04d407050f03901c8404c2d80055a11081e51035072540455000700300503140c03802c2100000c482c07500001c3d40101e10303015007401920b030340500750841e441c02c52036900519130100300506209004002402088540c11060300814442c5111442032880349020758020350002c2102403903501c10700900010614031810b55221950544001e0b111404000c0103a40c07051804108000e42414001200318040214014604a5086000300ea09250f161502a20f881480b22000019120341c01030802403d4030a201058984040d810300e04001102504031405020b05031110001607804416000d0711801d040c85000c01002c050242e80c03401207401858903010703a0320800050003150740032001ca07041c081d56808803005035900c50010840d5486001506481c0c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 673037832 1250 673036582 673036597
    0x90f0303180b04080c0105070609060507051308060c040b0c011e140a020307050f0d11070c06021608030d0911091f08010c0813050c040f060f0504090512160b0c 70
    0x56000e510005100b180d48042d03405075400d1001806142006900455542d000b00d10199405500d5125410119000d0f2003124000e01844e038403a9550002c074450800c4c1c07082260320010055224000700300000300004151810740d80d50ba513105a58864442c0c2c000d01510000c180c031102005480d00301780c182031065000306524800c401c1408502c1c0c3e6420780c03003c2280411a40e41010500401802928086c0c95001700719890001d60b0024044501c518246100c0d080040201d0352340c2c040c44014010760313070100104e21812440b0b2146d0400d03181006080c903128010031000540f030a1321500003008104149401ca410400084d10403142032500003107003000c41d140549041002c81c1085d034003107080001030082007003446a030344a81c102619071408515030b480c000201911240603140c54404035542d2030141d5050320354802c60200b10603040450310705035140c1c250301491240b40303456131110010750086a203130300b0142c0d00c803901920b501c3c0c0d0703880c85a00c1c0f104040000780610406070070052168040c501a0000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 673039082 1250 673037832 673037867
    0x30507030e0a0209060d020d0c09090209011203090902030a1808040e10120b040f050610050415030302060a0f1e0207050d051c0c0201020f27040c05030a05040201090f0303 75
    0x40d003076010307056111801024065080100000043c6581c01c00c158107624283c80075084580c544110f8031000c080c6001500800c040a450b088031000f94645000c1c0c40d805420f031840040c01042660380c014ac00da4159100380780e00c2c150080005010703170701381c5e80c8000807030f0001221030500420103160400c01c552007400307410b04090305178002c2401a804038080006031918880c12080002594407100082070008100b124881c0c181003031304001600a00502e170040c0940290070402038104001c00042e107000050901954080c0b442c00c1002c25030005440c1d4210101400002e800700b112610000039000700e5012000c103040100c82c41d2003944240d40103001850261040d6500ba245210046a10f84568030700e081c8202c1c0000045400040241d1260259041d18000145040e0302d0f8800d012080e0420300740031a0224002c608c007092104d0303440d90103c6415003103038100701e0304c0c100d08000340c05800054103034140380d65224000340459004d001d071304028103d8542020702c81503403882d00803d8101c5c4d400800c02c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 673040332 1250 673039082 673039091
    0x1d030d050703060f030f06150b0c060108030a0203121b0703050a0e031b0105090a0906080a060b030c030a031d030a06050628120606050a0308190504060207050609060c060703050703 79
    0x3070a12038400c1200f5035500100182c00c081ca980c884c075114401c000e0b02610a13550314040e18044640d40220f840c02481c018031090b07110304140d42d40500342141640810f509800070404032002c55400300c1150b110f034226245212a0b40c903594050241d86044801d01401c000b000a03011040c142c220019098180311560303071403907552041d420301d40c40d0142e500d00740c041400c41550400203580584042e09111070081d00c0c10014a41c2d5003140015038a040d842039099400401c10360b003d0200e1740c01031a601940c00d40040c0741c0c0703024210100765590076524001d810004500507000e1a5a80c0302039038200403100408482c0d680105040c03a030300414003902c4080c0304081a40c1c1c00388502c4441c281568201c2c404100380c0314118030303000c80d000d601660035008a5080d80c0d02c04010844d42d6980744050007840c021245181c850250111150114410500300404c0c0241400700b0803070158001070020640e01d06548c5291284a0316010416a01802406040754003418040001ca942d06600061280545980030300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 673041582 1250 673040332 673040341
    0x5010323070f0b2506061818080304030c080a091d060a03081803010e10150803040902090f0d0b06010906031a04020703050f12040209060a080a11041d030d05 69
    0x560341c41e1288514110440c10020421450b00b104001e800c41c408007189540341081e40450504520070841800c0341d402e82d80341400e00904e0f005003028618501400070810001103c1c1c1c5c0c0a41004403881d0005007201c02c0040090100740c45400120152680201c505803201054500178141c4000390003464150725146210011140e1105c802500482014110b064003900b9521082080e80c0192041c40c103501c02001c409415803824071132100401c1c8040054040e2164400e510300a03950030100b218003101c2d8007038040c440d5001c04400c840843c1c1075000c005035180610008169038040320100113a1140c070040c650800e0203003103904248511401d036609030045854450680448040c09021040f0056081c0314003d070703042603402820310302d02a0a100303003800402c002035851540038882d09594272058005101c11400c0004030190491412101001600d080114590b40c41800a0020342411240c2c80301c900c20b525564048640030515001c80c0095000400505a072a8044600030403560319100019 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 673042832 1250 673041582 673041653
    0x120d02070510090206070605100f03030203070c0e070207090b040914211606092604150923120613021207050d020d05150106080106030c18180906050103 67
    0x3c084541d0082125040590a48404008110062003091071500b9945e0204914500c0c2d555840118480da0045030b03629480d1401070144c1071141c0c0400c0034040c2d81e40a101c030302900458a071050f070300e058800050130412035002074054280202e0180022102c60b4000300843c001141a072940299030306101c48121403a80580240e103e0b0007012441403c00c000350200180090b0800000341e80a070390100c1c3d086116021007031002c2d02e25180b2005910002404005808000310074034035540090400003007451034012000f9050704292a019140b000c0020b62144a40cad175139004103111608a021159540760901c0003503c0060104001d0f449249a030032001201c07013000800178161240544018403c80c15582408695602c0b200102c1c0d0501130000e516040c5420610058000c20203580c1e840c1e600e5261a02c060200c903504400705007005840c04181c8088402c0144402c03c86245035038007100c010b000d815000c010709010f1002440c40381004000418400301010302c01c162000c6d0741060030840c21042e00b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 673044082 1250 673042832 673042841
    0x50901080f0609150f090f0f09060906010308300a0f1b0c170a020717060423031c0b010e1813031e021501060f1e02120d02070510 57
    0xa50354030626039000501e1140b610542000349000180c02e1051480741000003440d0300c0c0d021107400e21001c41000c02c01416231424031295400081c10b8000d00801d04044159035142e40b81400040d0215000165041d000317a61800e01e116440c0c2d180d040740c42180040f9400160010f000c2e00d81c0030805050600d8203405142038803510241a5a14031950840c9000c81d5040e01c04420310181526811241c1041e080680340d10300092940010720f60280c0402e6007001d401807031080c5140822565580117504010014407000304807181c60681c48070042c42c044035084802d107144030300850040030000907414569180400d412a00074090700f6201da901c56800e03030052204000c4a010b0450a1031030303c01c0481c82c01a5803e021503503140c00780c50b2201401020340c51202d01c4500060040b001a406400c14400600031080d80c6405410145455410323060003010040552401204084e8900c20520001ea07a6600811402d16041e110022941c6c40304ca01902c900001c1d04088401d45881c0100e01d010410150760f48107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 673045332 1250 673044082 673044091
    0x9100b031c1803050a2006070201081f0303031506030c020d05030417071115041406030a060806091c0311030c070c05040e030901030f0e0c12150106050901080f 70
    0x90202400841100901100300700d0350005000e6580c0d0164003a600191110000d18054401044401020b107004403907048500305441e044804180c0300407440e07940b20202c8814030380903e2b0447e425160700180c054030501d101000d452441d2008070002c20160140c2011180014007420400c040750f0340c4c1e1094098950700e03904800140c0011001c0b1040134080d40246400c04d0044580e80b1100b540e002340082e2541c889202600d0f034070443c05c0404a0780c42e0070343c03040d601489210204c0782072a140029804500100c007000910641020000609201482d40b2210080291000b1181c8a0400f2407000751685840c0a100e02c9440390354500c04400b500a01601c9007030103e030f954040ca03507621810f0900c0b2a030010803044034a14903003200061140e540780500100c603002c0030040c640d1440800009022030b441050405052400c00040b05140e48020444054a490981d04c40c650f100d640f000c2c142c00c0c010406407808403000420300214110354420041c115102c020307264440d0780e07242c1e03642c07000300201d0840e0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 673046582 1250 673045332 673045339
    0x25050312121909060903082403070603020a030b090414070605070b0105040e01090203070b03010f230402090d0606030804090e0313150c05070e09060c0301061d0a1d09100b 75
    0xe0120b0300440b400480e0400c2c003040300700001000c00340c80d5661420340b00804000c0e000201c13a001132000403442c003002d600b1982112507115401c0c256050200c0e45860007485180185a03000c10f2460318680260000800810000c140360a40e281c1031a041c00031030760801d1000090f1154880c08507095000d0b02c1210111500104040303a079a1070201044050540d11910300069500c81000d400142c80401c400c0020300075500e40c46449605101d0f00e80e0000405900c02d805200e00721009000b082030300b101a544484054402680d074120000114403240040d0200500c003918158000040c40140c4000d00141c0390003036810b010455800071305d69564025241d01e2151081150010000498500b844024400c8203090640c0e2248454440c58203040240c0d00075a006a034a404118825030b003413040030382c400d1199050034259410410000c1c240401d10001e00c0d01d83e0043c01c0d402c1c800e50340d901000c034003e200300f840b20f550740e291001407141d5180007611f1608040c403428104003003490150081c10003050014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 673047832 1250 673046582 673046617
    0x70c111305010b0315030318190b0a020619020a12090f02120c01030c030905061303090b04090204150302040f4b0f140904210f020d020102090901030f0525050312 71
    0x1541000009d160366808600306c0314922400043c0100c4140c054100c003c0c040e0080c041524007400028401c05a01601c0c940300703441005000380e4150490004299084d0010000400f03604a14015030445c1d99098065849040344110b15000e20000801208440b0280d070144120110a00150709079980e40200418030f801c20030020305080d8511104011203406407824540c0603030307241c0741003007684e000360045031301e0540020707003804442550b18200b18140d945142c110300c1c003032425822801040840c02101501c1c4800c680040300c5208804a0b104850020108440354212500391007413a10b9000021000d0444020b00000f01c4100c4655044212130341c3d0481309072890005000c028805074010403c0710354550880f910703100c5040d45898500021242e40340c030200985281c0029140c20301015240c3d003103a00403c1340d03019946801c0310a0341142d6000c0000310900005280142c20928210140c415040001c01e20150380c01d064000002141c500303505440346000c0c080303900042441000f0001139a007100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 673049082 1250 673047832 673047877
    0x90105010522090e0f15010e0703061a0703080f070e010e04090b01030f0c41040903031e050105090f090703050d03091208070c111305010b03150303 65
    0x18000400910000c1c1201a940402c0d070484156908039039000195102e81d1450a10301c0208104240c03d10518498014007400d21107440b109071031203050088101950310360000c40d4485006c1d401182c080c00d4007000d60010f0321510006c50045811101c000d40000d1142804500c1068001011780c0c02001545e0790b41c0400394031780006550100301c05250b180c0080d528091100410300b499410341c0610712404505201003120308214200d502c1c15000501c0c043c820390311003070265048038401c20f000c0d640500040326409100c0019003e402003080110b81050400d800703171080540c15444140b010950074500091580024860400c44d64240035a54004400d00c005c43c55289d00311100c194041340000c1218480e544903540d80307041c045504503084c082911013511400300310505100c5c1c40c1c411050f01c3e0840c458940180010101410300d01c1c0a8424445078003d040a0349800460316691340780258184040d50b592808403c680d842240e1480704414206405807943c907010044442d200b2404580b40f00c403804 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 673050332 1250 673049082 673049087
    0x7061e05090d061a06071203050f0f06101e0c0203100c0518060f04030503070303050f0f0f070e04090c05040b1c12020109060e0a0501270308220c03030e060909010501 73
    0x1000440008000300c013122500b10b540e110b5009250710f510400b940d14000000380e4014040d10400703050742011410b15010020402c1941010a030300034401c42d0f032242da0340900c0105a908d10a001843c0c5010200080c0704800c583d04111025485442901142c2d0842c10415642040301e1000410400180c800c100c54005002550740c50030720380d580148105c7c03803d0168400c0d0780c1c0c1c40d07000350301c112055080070840d80241034140c0715042c2e0021f12444141c84626003a800b801080c6401018540e820101002043c1c0c51841442000e0400c10003070700401102520341031450109800d4031030103201d203003011801074060070f02c5d056203504840032007640f0b0901c0186c1e545962200700701ca0f00c4642150360b111f02e00f03008180b20703021741c1c100031581e5405030005180e075040c800d080d05c4410042242440307102410b1011480000340004000c0d805180204076600c901ca10850000d140343c500c000041c000a403000306104030802c282d01100d21945800b03c0c00105001401114010015442d0b84946102d004008650 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 673051582 1250 673050332 673050341
    0x20628020306060405040e060103150501030201050a0c05101107051b0114070501090519061a100f021606180e04020a06030504050c1203190201050f04120c0507061e05090d06 76
    0x80d0000e00c00c130306007504d0300041011201c14030b1081072280d001c01b00410a1050094144900740900c00e010300c5550705540020b481e0b4461120103070104805000140113001082c4900300c14425801c200340100069041d691445400c00f0b08282d515008000300a4600180d403d00000d2644040e100e5030108035070056000c4542d0040c800c03e035020b549411b11200051002d200e603070308e400c80d20fa9544103009030302d08060084400c040d07607400d41102c0704006500c003a51214010341d10f51000d450300c1d0a8940034000d01320301b001b207040003408000400501c0400d850b5040703039105070400502c045201900350b40d0f03040c03804610000d50700a5008084624140802c520a4106d10f907c540148200c0380c04503019404602d512060110210164001064212041e891450a111600d080d44000d120600307101c2d01c0c800440d080940001d02200ba10760070407130814080c2c4a510000b030340040c00d0b13032601c170394134080074009605401c0d04664410f400052508003a001d0025254040700c051f103c1441441c1c0c81c1d64401c0200b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 673052832 1250 673051582 673051591
    0x16030510050f13112109070b13030b15100c113f0f01290102010b060a0806041409030316050d060602030d0609050402100f2006070206280203 62
    0x1801424000000c0d10f401e01036404002e4942c40c88aa07180d004001e118a007040e1585058000e10180060210704880042c01005546402031055034440090b10451403800356031340010302442644040003140c420008101803034110a4411296541c4d81c02d40803100e00e501404010072140801140340581d06240300908070f0341300c00142c501032090105203514980800105483d030b010360400d010014406091100220903c0d800c2c00070720034421020b120707803c0010641e0804200501000c42d0030001d0b031007500100710300c140182c4855030341c0b08a608000d05c0414100c0d2064062070401c00c444210030800900140314204003406981941c07a04140c3c0c034a80a200c940d0703031080010901c0908842401403141e8001400705030001d45da20051000300303905640d42540180c221510f07240401016031510252803803480c7c03461505910a044008042d00d482c2c0c5400d2200c0e041143c104811010200000f8510780200019021204a60349081090301d41040e48889e91344040c14400a403120080781d5005903800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 673054082 1250 673052832 673052839
    0x9020901020106171c02010b01120f090206030f1b030c070803040f08040b120f010549020906030a02010906030b0f060a08100b04051f030207060606030516030510050f 73
    0x11613a0310100c01d01c09081c0d10070714001507001005801001d961216404c05440c6080c0001c0c440469401c0028060b043c0070340140e100b080d111341d01e02c0345440c100c1d800381005a5008000a8590a2000001e90b0103842150081c0e071032039994440302c1c200c5203450107880c403c507001c800b020310b080d0301c503541c0e6240d83e00050310440308005804119000590501c0140000d41a250f0100303895031441c0300d032884009070141030440b18210304001030160f5102c01c1308001c0d0280458207041c117078540841504841c3d030380010140040404003034035030040c40206810071880394000c6442c01030a840760420581c48050200c8001d010500900d000c20046000e234101500030300000f8049100302107100c000c11010b81c880c4080720300255403103040100da0b00881c544000030341640b5045505150901d0041055107090034010b0700400c01d02c10301103038080e10030b4040310300ca00d5011400384a01c0360396440240141c6004d0b02da030441d05032180030313174030700548030b0b10505115000380350300281060310b418103000f40034000e102071641 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 673055332 1250 673054082 673054091
    0x809160f0b16051f060501030b1c03120e0109020a0603021c1802090f100b0c060f1b160204050a0e030910051210030b0703110a031d0a0308060a0806040c090209010201 73
    0x700d601801000d68401401c4e1820300070004440c0384200700c1c3d813141c022605042c40c00c00c010348162502d408070b03140c44120b0441114040540d0034103960790f0404105001c4040d007400260080e1000c190045001c2510030365001029541302c55080e03080e4000c0f82602082c009400c4440c100407640c64102c185000f070505410b902c681c240d50040b601c1d00c00120b0b10701190048040502501c2182042003d006106861840e4100f4503081442901c0c0d034009001408081108400700d41c05168078404070420101e00d00e03400d81e59200a50b10b0030910b85580c202a84158602000140a03070b40c2c0d030081c8009803908202440c5404441420468000398064140b010841c0a100c95204002c000c031116006071074204400b150946146890340c004803000b0158020541080503a0300465602401e9416001c00d40c18041403210000d0900d8041180303d0f1125080d522543c180141072581000100d4020002651741c034198603258a00b01d0b5882d107043c0c0b40140000c180d0748041080310802c2e80034240c502014800400d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 673056582 1250 673055332 673055377
    0x70f03030609020f031009050705070b0621010c020124050112060306051003050c0d0209161101020a050a1e08070c06022709150307210605070809160f0b 67
    0x8100c1c0c00c03c0b421145148400000d00090340503000f000e034014447d050061202d41303451000145140a060750080c110440f0030017191aa98555205100448107640d003500855004040c06001e820500b00d1880507518040c0344003c420740c141d5806200144481c0d01c400d60f01d00d00001100c5240200114501155a079540400025098003505010305a10400d08659605501380641070400140540d0301c5402d40403c0c140c0107840e114001c5500c05444940d4032010441070314141e4401002c88402c1c801540300007150441d207504840942406640c1c0d0755a440b07262211031891100b000c0c249800d00c040b510020010303102a10442d0743c1840c40c0d00c241c0d0054281a11103680e4052249843c038005080215209405003a0400034090303640000050002403580345a140443e8403a030745405072284801003044103168540702524507042140d4850420091480c05007030080c003140c4144c40040c004d015940b030410521000d11079120503a481c0304d11080d40d0340e02d0316101d010703590302105441a41c2d08030001440c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 673057832 1250 673056582 673056599
    0xe22050403090f06020613121101050408041e0503030f0c030c07030309060e0d0b0105120109021c030906050307050f1b0307030305040228090c020c030d050904051b070f030306 77
    0x8a01540c820b441e000c048a04103800b41081070801d0b001103046601040821020451440c6801d4003e0f0f0000079590707445e12524000c40341d082c8000e540c22030a601301000d00c07042040c690000c1003110205804084e000e0a441072007440d822080c860680d0541c010f2184902501c6940d00a00602d0600b00c01c43c0d01c1c2540921403141003100640c000c2d0f001c194107103030811016800c0340f100225914221401880343d0f4490781c3d2121003e0341801981e0113090070740110390021100758800140190010030000e40101446140c01e820600041c0c00c8001404185c40002c1040c010001c1d01d01441c6146c9131541440d0003d008649140c00c101000e100c1e289482981800e000828802000002c3c0030f80d50201e11490540140847c0011031861120700540751602c1141c0c0501384099441030790404240814000c81c0b0210407880c003000904195818020701540c1950107420000605286034152001d000700c1da203848900260384c0307912902d2030740c500c0d04102110000e00001d621f240160701ca804d002031256140c03e4030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 673059082 1250 673057832 673057841
    0x609040b04090f0602031b160311071205010218040b03060a090f080a0f030b0a18320703050709030218100f08030702010e060403020609061308030d05040303050601090302010e22 78
    0x61314003d900005000c040d20358520b00d40f035034010000c4c0302c1d450210421104c0900074210b41e0050300700901003003100b2050b00d0600c0461300806043c10600c03001c2d19203050240c001d50200c84841d102e1804a00c0503141800c140c00303200c1d481d020080181c01c05680310000d02d00901a0608100c1d41078424041d91000640d580e805040c0040695807022010b860151000e0201c0304000300c402d12405002c041008a40050300001c82c11150041011503241e400d114051203202c401c1c1c000842030500ea440c040740310f0006448181c401d20050340c0502450721007020a4522030500e000c0070f5001034400050760113480d44070003d90341042d03100c3c1c0388001041d500c80c861450700c0302c0b541112341c09410006041c03040d50303440306aa45001400301c03450b41c9014550f0b4001541842a07000440c020b080c00310701010401d800e044c0e490000e02c450800d60399200c101c05009401040200c80071004031f803801021600c40d520411203481a2075040e1981e5115001031800c00418407401600e8200c0c0340000142e02d44003807054000d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 673060332 1250 673059082 673059113
    0x11704050c130501050f090424020409020d0207051203100b03040503090a03050c0102100203101a0f0301030303050f01090c1d12070305070501091d0601140f2701030b0609040b0409 79
    0x42c001019410107080009000399141c2580c4200e00d68800d000200340355041d0351526040c00c0620319440c5814003a03c0002c0e01995020012072032021030102c01900700e40c0c00810809104005a4600a4140c0c4046805000641c1e40b911409800481803000c0800403000b542c000740560101d90500120000190240e5002c0c0c208541c3c03900440c00d1004c403940c04000380034001d001c100d000e40c110f1403e2911401c140c08180f040130006007503d801107100c45095002c07a23441084480307180c1c2d81e03582c403030074080c01a0200f9200910815000c00002440300454810414283d401d5074500841280d020481075003001d485034030369070002d002050042e049100300f016400035440b5801910420741352100140604143d580318601012819200342071031000c1e0104c140e403110007401e00c1c5105010a45401085004004440c8000c04002944d0712100e115212401202e200307603401c1040992007240118140c0f20703001c0b1181d030070020034440d4440034034264000140c12030740a04000b540000070f0700c0d40d0050000215 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 673061582 1250 673060332 673060369
    0x203030c070f030306030219150302090d0b0c09060d2009030303150a0915030506090304050d080d021b06151005040608060d020306130b10050a0314070906081e0606011704050c 77
    0x1904000392741c1c0141141a0344089804c0031810a00c00b04045814200c1e4500c00800c2030605800080801c0110007e4420354503028001036120350210208400501030305900456038018200322240740c50b050421103002600180286082d5140d0b054003100c0383c09041c00d92544a0420760021803414480c5c41030403044801c00c0030381c41d0844d2850502509041c405415804140c0041105000d95180d010040340d0b100d03841141c3c0d540d103282a0740d05030000d00840440b01c2010103241d4842d07600da9030000c0c100307006004040041b140c54445404014400d80f55510b0000803440901c02003001a0281030070366400580609125804e918540c0020304010f0100e40c020900000b400481080c0b044119065074800301445040345114100800a03060121710b1100130041c0c07135001c5032904a4201840018018075090405100741502ea812050b04c58141c41040300d8190031011103907200c4480010301c28028001078445032101003c110b11486003200092095580d88985e8025010f03545407940004042c00040b03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 673062832 1250 673061582 673061629
    0x19020309120d0605090c0f0301051e2e020106081c020a020603090102070c150903020d230c011101110307050a0c200a080a030f260108030301150203030c070f0303060302 74
    0x5010007809845c0a8805403100c001840910a111078920803030f819a002150f0810a10140c459440c01c0000700ca40050b03007001420000d800842000784000940207008048056000500001207003207604500c01e04110f58000c100c029800c008680303504010482c10310603225072180c035801103615030344143c85040c0300740c0d4009140e006000310601c000300641040b00c80740e4025034001400404400c034500001e4480d4400e01414070800c007100c42414601c06048402c4c045030284241c4141d200c2d044a0b69039404038903080303040c04590783c0610801200c04101a8154110303102d540b4100c4e8075030030071000d1406102d8400c070428003007210540061030007002881046081044542802003040c0c0d0340d84015070b82e03407003800c20400080c1c0190583c1d00e40070961070081d40c0903603010312038140100002c00483c504848000081010070001c401107040e5100c41c3d4064880b944490800c0b650380c0720031038084031200c03170074040308c00003802005004640a0007440c02188550b20380d0000380030080b040400d1040241c91 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 673064082 1250 673062832 673062839
    0x20070c06020708150f07111606021c0c0f02010201110c0a02100302030903030f060f100309061503030909020726120108070b0409050604180803070e030619020309120d06 74
    0x1040b03408040e00b180340c080c00b10107410300558040d4640150542c10091500400202da8034410010342d40c8541c41c5a00302c501e0442a14810002c80004d40550305c0180200010140c02070340e2502c1c84881c102c2c0a5890301da102c5440d0726030548001d0010005c078119525007070800e41c403076990000b40007000070010203408644043c6c41000481105072842d04141070041c0104900b4040c0401900d5000003131000b4404a40c0d100c0d000298213a0103648900e512044605845402d290300d41e06c000200c0707224220400001d08114010b014083c0c0c14400100007a0043c0024017512249401a240d914458055201c5040758840200007504488003140f0780e4010110f000003580b08405c041900410080c40644460750500e00110b11030300c102d000305180981c40308041441501c0c0e644c800040d80750ba00360305240e22032080c42c05113010b50013559140001081c400c500041032402090450042550540d40d00800c0800d01c1c01c1001394000802c454001d000e440d42c014860444480100300c20b40b03840100040e000d04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 673065332 1250 673064082 673064087
    0x1d06010e060405160e040e06071206140a030f030507061109010323070c151802100503060d0308182e051005041107060912030e0a03020d0320070c06 65
    0x14000c000a2040381044140b00440014802603032000e12545040c011040510b00810041c1500112071103651145404112403254061505001c1c5200c5036001d03c00950b961781021084503888200951103942000100001026003f086000c0da209041070350402803d5110b43e800c070390036150b5030340344403200068500c41983c2c14403e800170081440079803a0780b444040d4840c4c0c2010f40c010904020701080c40d00390b1041c40310074a402d040000f89000709018002c045000d0721440c110b0b030320b0100e00640d180e0a46242c0f60303000340241ca1145002a200c4031100708240c070104c8800c04090034802d0b80e0740d44c0100b00c4807210410301c0311840001c04d4070005142d8012030340000b031900383c2d400708403d0050300d000c00341b25014605001395030454030201c0b0049445d10601170003100c0c5100c4c2d010010700040c5400078030010400034150768502c0d0f034100e4808000b0082000e26450700d940c0180341c001c0c0140c10141e00007c00500a030702c40c40f00c0880100c90406045502d0600407410780c411041a101c040c03501c48100101c03035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 673066582 1250 673065332 673065359
    0x9150e09150a0903090e06220902040b10120f061d060310060f05130b120a0201080703111603360602120f0a03090804030803040c06111f1d0601 63
    0x40903039000c00002c143d6880090400006000755000f40c0400004503203990f856150303d1003954030701650000c070f2040e001039030b0700103001c070130002c031300440c01d1141d04030f0985403002c8209104102e40e2510420542107005000080161600700803100b9903c090100b0060090524150112240ca448d03411038209542014a400804001042c810341040b00074404181070740c085804461081d50846050b1214141c0c840180079084120340d04042044a0215040c000290070180302c0d0003038a031049544c03204042141610074014031b116010310100151410442018841001c00f4000c0c5040c071071071060300b4091440040e8418089114148190000c0000c12403a03260784020522400108604000b611010005009410911412aa022402100d0a0301076000355581640c044102e595641e01e038a401c0510340c1054074141c4890b002c074000440d00f103000c2c680030803032041580010f005a900c1c15058110090300180c0c01252252542201c1c42084d41a418920211044c0c0e000b0704a1076040075040a00d02 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 673067832 1250 673066582 673066591
    0x120406050a1505011d041b050301060f0e09060d06090510060504051e041b030c0e0435220e07020d030c050304020f0303090a08010e071a0409150e0915 66
    0x400d02c00c01001540e821800d035124100001080741016105400010010001000414207281041e03454500c040d500c0001181070f2020fa032160580e120704542d00b11031001e210322020b0707000000e510119038989081d00e0203912443c0f045201144101566543d941080791500746c0d045080d8940906111790b20b4a806090340c054018400809000000300007103403242c1e07001e080580920804d240c0b41011800d800000c0010307541148148500607581d0a1000410500312015a00088611070a500c0e008907231140500303c03100b8950b000c681d07125400e2940040e6009001c0e103045078030003422000014040d0380380c0800900307500c644081a480c0102c00030742400502101c0300e0805292071004442582c020080c1c3c1d070429010b9030003d9083d1861000303c1e00c1c603c61900042c0d841080c06800080d550700c15007080c502d9200e0f00098444c2150b42c0c0e5050450742e074032082d07584900003052105004440866102d04640441c060407c01043d542d03204080d50710405880001098202110750030303002044c0306245800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 673069082 1250 673067832 673067861
    0x5030a110c0a0803061516020a08010c091503270b062704062403020f010e03150c090d03090504050106080f07080a15091406060a14030c120406050a 65
    0x144408484010784514002c03a00030044003001c40814820b80b80c20282004400c403001000340d0f60214603012800180b2022022880345102000118800c1010301655003480b00e02c2e118032049038145124a903015080d40350400416540301c01d595107070403c0d04150800b040003c0c840741181280350424100000d0000d04103805402504503c1c1d50804420013903c03074030038440d1390602c0340c1e403164642100605002c000136250140049020809011200d00300c0c0200c84c4210f030b0b2030544183e003100548a050660364001d40c5034011030103034600038590149a952000b4030b0301e0300626003503140c40081c0550492840035030015220f02020303c240d060503c200c90141010707080c0041c01d40f40c10709032113003100da0062044040140000128803660807580141c1401c01c02c0719401d0f60b480d40ca42c1001c00091013000340f010301d4100140b010880c0d07410520111400480700ba51028510703406284c8104d055400605641c45c5400e041000c8410030751070268075401184642008540d600700300d50480d0035650380300901c480 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 673070332 1250 673069082 673069087
    0x6050c09060318071805091b0f010e280e100b0f071104050c09090c0f0412140106060e1207060e0418080d06030218042301150605030a11 60
    0x1034590351041a00d500070070100c04154408014000c00b4142040d50703008184140b40302c51780c0c02058580c1c0d04482c0c0300740c1c40b03e002c40d203940f01d450415511241215481076000351003902c40c540d41354441d484141e00800003407c02c80c24019043c2400344000100c201d0b000c2c10300410201400074404c2511a55000049061201d0085040c4112111588180d41e800203100e40001044420416010201c2d090220000e008014a00d810241c044880d0702245401d40f01c0c545010000c0c0032400d10758181c64600d07402000150600e410401c000c610448107000c141c03441444d40c0203686840409010341009401c0b40ea40f00c600f416143c034107000d18550380c01a008a582c1210805100d2281e00981810028400b11404104451017490302c0c40380d47e4411401034260b180000725103014040c0c2c0c0d0003100403a032095540441c00c031030b54100484140016038006001400214440c1030000d0308107000c540301d039511400080c80109261403c010149183d0002e1702007031000c4200184860607214444408031030304051072 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 673071582 1250 673070332 673070347
    0xa180b0a180801051e250f12050415020c070b0309010213054f020903060618010302010807050c010c0e0a0504090312020705160303120b040b060901080a0213030f06050c 74
    0x500304048480040ca003817014000209014003080710140406210719441841030665180244000c4550101c403003c502d03100c4400c0500101c51090600c00c07508041d03026100340210280c000a5400003044005c5c2d03116070f030008200300448800950140d212807000580d43c8002c440180c10b400070980c03200303100380c844a0048060321803c11410740894030003102c0b501456109040c4541e0010039400c40d00103100150070541500c042a801800c550394202c00306c074050782e942c804012450300c0c440c480404e18a1418010401540261080780d0005020304085040030030301e021150843c1c54140c85200042c081c0002441d1500744042c415005d08800d0300c0070301002c2d900d030300c01410b95108113408280c12030f0700154520900105110400c0c0003440b540c061010555a400e004001c115840c0e80325243c249004c9068003903161034403900701210380c0600b42e82d04001c46200159100c000080024075544c0d000c12004030300000c840d00074030155104048010560042d81000011113600811200d040d140800141 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 673072832 1250 673071582 673071601
    0x8090f07090b0103140c0d0f02040e060112110a05040e160c030804020a0902120610141b030d0e031306030204050a030209070903060513060e28030c06050a06051e01050a180b0a18080105 81
    0xbc5621440a080c00d60507502c0c0d001d000802080304c030340d000c0d55507000494404c0c00181d21500801c2112040030107400315840c3c171041000c203000e420301020b020401c50410100040d0040c1c901035403043c00103180e41821aa110520010380c2c0c000c03484110200d40b40d0b03007040010326200014070034033551407400702d0000da8a000c480c034480c0301c0c80040d814410030314905042c010f1020003c541e804004031000340003906154854035541c0c0c1000d81d80341003021483c013010908a110b031081c1d5044a01c01040b500c1c2c581c0c03842d000c4c010504000380141c0100701d20700401101042a6001d000d0144200c0d01d0404110b015900344082184c05050602e029030f000f02e2081d5100304123400e68041c07a4800e6100d10540803c0920342900c1d00802d0840041509091004100d0724200e164231503022581c00751f61810f00c80b4035002585c0d103162051192503011a05c01e002d8030742c05512443c07004544c0005010488140d64454120005e2504031a01000009040c030052030f8140d58410105001031110800a102504180002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 673074082 1250 673072832 673072859
    0x90f2607030209130f0614061002150708060105161b0e091203060d0c06031a042003150405042a03080301030308100314060708090f07090b0103140c0d0f0204 69
    0x110480c4410f071308084018448400b0741d2840181d8031140810050056850a500513101200d500d8804c0558840a4000c68008520003d03258052803540c0c0b0940d80e2500305450903040035001e0f41c100002400030028070780b04503002c164500d010b9040441c200241c4d94000d284004542c22118000c1c1d04041800303010000000c0c00c40301c01c50400b104a0b244da0300c01c004035081c85c041ca100039014500b403a8002490300c0c1c156108160400300c3d10130f0b07072418410900030702003500c07001d0001c1c807142c03c0c0801c0228541d02141d006140c00c5181d81c0d00100d600348462000806551081c0d0b016100c0d002040f101d134610114500c000d00b100c1c1003034401c0b014014907540710880e80b03020521002d8280a00a0000f0f10751030300c02c1d0003440c01385a100701412602c5012030f25240d030b141d40c100c0d03144021444100102e10580000a43c00c607000500308024002e071070500e0304100141400142440c1416215240030521144080c104d520400341c00160a46035612900a001503804001220903441e104010500044905038007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 673075332 1250 673074082 673074091
    0x706051606050604090f06050f0601170610020712140c0312070f02152107020316020f1f0f02010b0405060d0b250e010905030106120b07090f2607030209 67
    0x10700044a03035800b80400e003d0042e10000400900039107421004204a03a808180286159850f041d40e07940c0b1003005403843d02e4580d6410003048442d074000f8100d45400c3d003504c1030b0003100b4815240030b6681c2c0d100c405003405006104842e1803110900c1c400d100074040261068100e801c90082180d0811512a0f000505c100031000e080d02c15079142960564661421520a0b40030300c401306550b5013a00f500503168081c000c00302060f1004040c022a000c94800429112000c101200b041d17107200240c0c0c200528000101241500b10112808800030f0340407c2d00e4075520b034591a1034603004070b40c074503078024211000b1041180c4901d00d01014400c2540728a031030440540c0d40a5440003040d114000011289503440500d81d08440000c1400e0403856401100c0e00000070080c1c030395618050311841010b0030303103083c1e0244c8940c0e261014203410100b44c0c108605030300b00415041040203242c46004601c3d8640d440c1e08807211441640000403c08480303984c1841600118401910055045034006864035078081c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 673076582 1250 673075332 673075343
    0x60c040b0f0307031b050301090b0103050903031303030f0911120d08070e0402120a02040f05060301120609081b03040303090b18010e030c0616050706170c130305030a02010e07060516 80
    0x100107a03070b15019601c000002e400718600880c8556450b100200701e1f40c02400394500f0307a403e1000301d00d555406402200e014108035805036041d5501c900d0000002d4208100a80c01c05880e80c044d0103940150348504180e250040508442a500040600400140300d40104465611000044001c1507110898603080801e07803802650750b01c00600090302900400d042000c400b43c40d0024000b50004a45c010800c589052180c0300350582e4850400159007c00d00c600c070340c8160001d5612001030b19541c4201030f040c2c4510f44040c03c1200c4170000540d403900301240442c2c940e00028090081c1170b00104c09000030048030081074900403000c4925030001c1a040501030602145009580340c9560600002d007010030040d29140d10343c3c0e040610030401028aa50988a50064560208e01c07184641b003000c0c40c0d4a8070304072101e11070310343e100c00519076800703180d072300150064074140030000a0090006000343c98982d80040350f40c1c4501c40c0c4850400303200f039102c00c2c240030b010400c01010349181520a00000e4114 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 673077832 1250 673076582 673076587
    0x7300f05030406111b01050117150103020d1b0b09034315210c1407020301060302040908031e0601020a14070f06121401120b0403021e0f060c040b0f 65
    0x50600140d940501c0c6007800c0d410303003059104c03014179a0560055040765480d045600b04406800c030038588541a03071003a20b504605400042c009400c1808414020078411218520100c40c00202c2c0e01ca685055005041780e800b000074070f003d41d40b42c10001183c0840340074450502d007501a42850070484180c413500344030500c10010401e041c01002d04101c00400541c3d002e90059810810003e00c6015907500b5600350a146244110401d4103a01c00e00c403941020303449000001c0810582c1071722541245074100e80c19904d950020005071914011601514032038080c07d030701c0b4107001d9640329030440e00b44140d1400d06408401c2003031030707a0300007030b8110841e800904444820680110090525100d50000300d0b8014003400d00288441d0700041504d80748210380000c00a4030f000d00c1c0440300c00b800c00c0c4520720007804074040e020042041400001c1d005440383c012034030b2014405070078070011543c40e459081c3e1500142c80e102443c603c00c0c0b0130603504c500041c1d095071030181803a00f10040e50003000000910404003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 673079082 1250 673077832 673077851
    0xd021219030c0e1e091b1210050d06140618180705190503060106020c1e1306090209040b0307051305180303040f030e1c060c020307300f05030406 64
    0x106205424800040c000d502c0400300340042c04c41035400582e5041c02805500001041d4108004217940781c02c50f00d12146103047c2201d004550001c0340505500030700d190b100c00010f2155140ca0704c0c41c0c1410302c62880411804652240308400e00d100528090207400459000103d10100400ea070b80d00020b104002c0b03006da80010700703051400c1c03896002a41c010240300000c00d5540154146502194003c4044032141e80c0c8800e012610341e141c040300e282c1c2110401c04248106280500740c00c03860320024045a0a418803040200141c1e2000e6020300d01441e40010455800c5c1824001c013490b84505400410380c2c589050007240c1a6490040c3c1c003421907942d030300403071203945e000c0e400c0328030b107004c640304490f00d9091908114129400c04503044001c60440490000c00b41020310442c0c0c403021507900b910a45148549614010700501c505900450104020341400180c84220040154a81811020300c800c075a80c02200c44441c68841c40701400740c240d4010503000d0f8020f080780c2d03025502034030124103501c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 673080332 1250 673079082 673079087
    0x17060f15011e12060e0604050903070506011401110102191202040b0f0310051f02010f1a040f0608012901022b0e06030c03040308010b03012d080109050d021219030c 72
    0x204019000c0f810f05050340014403e0b608089903003e4070741141d040000e17413102c606250356441103040c001d1068000c03000410451000501280e520003041c1842c0c26980c940d084100d0890b40701d00d02e0f109003a12050040c1890307aa2243c0c07600200108001c0452805003080c62444082c01004102c05c0e12040020005215052400f280310003008050310008007261210100b0921001c3c08407084015860714284101d981140e01030800d040d000403000310b044003000c5003484040c1448103807801e80301c0d40f25078000410a10901c96014059a441c843c1b524030b4145d0b015401c402d80409044604642c01712406c900c1d03944420400f4003212004903020820320301000000e8038085140100c550384070002004000b94030520301b0086202e14460342c0c1d441c056a0302c4411a100a010038090244024100070780c030743c0c1d010003014540c0889600c084102c2c1700c8595604140f400d450400008803503c2d0080d45181c649180c04100c0d40c0034400659030380500340b82d04603170500f18048a01e1100c004060321078250146190 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 673081582 1250 673080332 673080347
    0x1b0f030c07050307030903111f0302090f1002101a061b07030215040e07090303020c0f040e0d020f0d0815010f20030405150906030f04030917060f15011e 67
    0x2a071040980c0d44800150030094580082480b051720500401101c1701818074214010500038949c040c9128141502600b040380250460068260004612b060180d0259201240241d403405154014044024080c0002e0103984495450180030320905d0019821a600d50003a9510012480c880e403d0070400c801d40107162141c0c0780c2c4069048588420850107010712400200107444030b01c1417007141610b0b1041c0c2165507131028030001d4010f0b0802c2945592920301030908290360b00c23004002050700d00035240c2150405010842c0e103400369002c1c851080c0c60360803e000100d000c08a5007850911f9103060780020f030703541c007680301d00604004546a0000200c0d00910a4542080041c3d810103050018000c003199242d0290203145d10a8607800343c074040d2402d554045589549000c0c2075141076445492203040200300140045060186054000ca400e5140e40c125664003850300d8010a0340d81414160f500d40e0120142480b051540e107400c100030b807660440a03460400c14036000c0d6004003000c3d40c804a0307508 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 673082832 1250 673081582 673081597
    0x4110f030a15060609170a08030603100e0a030801081203070c170a02160b0f070b040c0b07080304020108010b190f0905060f12070804150506210105040b1b0f030c 71
    0x4109003410b8803035911a51007001078420988502c01403a03200c5c044075003111491513031144154006100e030000a0042d001031600102c000d0103c42c1046140b420365026650307820801c6c0c1b800c0c0d00a1710300805055219a0042c0106903a1001d000c0100c66806009614031005102e801446420038481c0e0420400d8042c2078111400034125544070100041c00035100e02140001c0c1600d120503060100707020902e5800c0b9445013041c051424a001616a2a2003205600500c203450300324110100058903e00d2500420391b4610500b0b00c10341d02c0c070f8a071001502c981e206030001d608102051080101d1248160004500d51070541041c10f4441132811080740c52002503088282c128502140740e14140c0c002d8006840d0a0000b42150442542e9040e8121144441202c2c080c0400c050b03240c6021074200260f006981000000c0c20f03170342d143e001941c82c01025a485003841c01c4160b64400402c006d000c5600c03200c0d40c00800008010b0182d8494081d43c01c480d009039500c247e10020300101040d8003a40380340071039218 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 673084082 1250 673082832 673082843
    0xb030619030b0f0a0506060a0e0d020d03270e06060d060b040902040f08010506031f0b0603040b01092337060608070203040e070c030e030129040504110f030a 69
    0x840e10380c80d081c4402e210964040d40c0c24000c40c804500304084a004e11032042101038945428070340f00d0101142d4000c1c1c0c40a0494003c046521040d0168449150910241c1e000f62628000300d000100c084000300110941221100c010b5031051040519150b03a894001d00c084a00b5622604840c2111004007419401a0410318000600040c5a4001e030041c0084a02c0300710010080b56403601442d0a0310b00c202c0e1040d0340f5800075011002007050800403060003140708040042c1280c160004141c00341d1003542c013520042d20100c010031010020b80281c807903c054411048110011a074598034009402074241c0c60010b0304448664501e0810b041d00c0707152100451800500040c0e0a48204010011402540b0004d82c1803000985110300000841c0e0803503280258103049580d921070100d40c0801c0c00303c000c904110684065801c996403d00400742d101418011280203501d180f1542180c40103d682c459000d2800c00f41004040741e0380c0b5202c82c0b8141001e6034081601c00c101c40000e414000c10b803c00810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 673085332 1250 673084082 673084129
    0xb040501080d17010b0f0c0f07090f0c0c03090e0601020c031b030c0a06080c16061a010807261803040609050306010e0108190302030417010f1103040c0b0306 69
    0x40034800001c030010b108440340c032000b030301d10142e00050010207030900500040c9001040140c500c0c00168006000d140e812000f50303034044106060903030400410f036000c622919100c90070441c40307042d2441079020100d03180c1007424105114ce5000350808103148282c425500c186000a4400e0740280880b04204170001c06442805107a40c40315040d0980c00640c05002c5c0c0308e42284807c2c3c03030074920404020b1390801d03240c1440319618640c070f071030301c0391b020300380d1104900c46111007500003541c14054201c3d503c001800340950080140001441f14000528102c01c01254801400146074010841000301500c1c0003020382d1581c4d405d12000a894a03800854454480040c000910f25031111001043d00c204806031000c590381c503140c041305c1040c2809240c0546d00140915000f4031121491100c1491007401501d0416544050720500070075040c1080a650351602241c00940715648074800c01041d214811500318240341c3c488c4145501e0600804680b00d40c004003141869444205800340c4906121181c4c9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 673086582 1250 673085332 673085339
    0xf0209160f0f020a020f191d070302070803040b04030e13020a110303192712080c0f1611060d0f0b0409050606130618090302060601090317070611040f05031608100f0b040501 76
    0x6803c801007492014403230030800d000c90351841c8203008640c45103811031a02c81c150b8407a511110342c5118058001c809001881440003540e0302d80d1200c2c210b4034a119200142c845d4400c40b0044e0040d50700004011340b07034100708100b081c05810801e00402d00744001e600003551401d040034074044495445c03e40003481c40d89090b00070400419000d98100980c0e99601e80401d80c498002d4841203025040c000d00c84801d0500400c030306084d08401c07000c141801880c2c0d007519813410001103101e9600c80c18921402985401482840f0200f900401c8140c00081d101000070034540e469080d141d12004e042d1501c5401d08007030b1080b00c004d440d04480090039401d010030901c0044403140704002c1c81ca0300d808030054010403000070510741c002c0764200110390300582041c1911550940a40c03e541c0718000454080b60380d040203c074120580c20290001d002190060241d8a040404140c03078012012070b1568182c1c048031090010782c13404a001b6010100e28240030640101e161200e0b0094041889941d42041c41d060001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 673087832 1250 673086582 673086599
    0x1c2007110307080a1a010302131a1002010c1d0303070b070c05190b1321120504060e071703120a020403050f06040209100b0906070f0209160f0f020a020f19 68
    0x120b250300c0c8140785c007554181403400c00911042d4240300280d0300c0384508044005e051441e0f00310106c524581c00d5000b1003204210700040d58071a00d000c040380180c0d0340c0d2008801050700022015082c250010120030318814180000e0390b6442070180081110098801042080780200d20094040358804295040c0b02d6912a5020307001901210a654002c40074010900081d001c6601042c0c1c503403c41511120440200c00e24544001411484020071015055803075039a0703010301c03c2501451241001150300d4900031030482c6484440d80141e030350740d03000080b111b0020000004071100041c0450106585946a055042c002c1c0115071000c1d05074010403101078100f000c00310b1036500c2903102312284107554540c0d96910005240c3c1e400b03a0388200808100002c0c00e03180c81400f030503402e4421128811041c40d10b074046030603504180d071030490000c0c0c0d049075008804e400403418200c54090f80b03070400300c0001c0500c0080d90742407941000b0b8010754014103074102640320300811031204418414140b400640d1181c50703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 673089082 1250 673087832 673087843
    0x2a0904030809010c0507110f13060b030a110a05030103260a120507031109010302090619020304062613020a1e080705030312040209091504081c200711030708 69
    0x25220b81d4a07003641d40080030f0042054840198100036109000326502e8248520b910b030340c3c4800c0d81d200070705298068205140b409a400a06002142079480342042c0107400191542c12100340351403002130140340c0c2881d5025040d40d04407074019001711107494002040c512009440d00c001202c1c004000340c40a500c681001e180c0b110700b4010b0804101f6070380c0b110412030454180300704c0564810340421000d001e03584650090105400c000b40b01510b0044010a2860f11030000d400c080301503040410204051500f1089100c030920080e8071005a03000c41503028900076100070503881c02c2d00e60800c0c0c00419500d030604040e010389142e551400d5070356415612003540c952030f031040103203501c10000085110309000c01540e610002007100d180c17041d140e0b903007080400400244aa2803500c04e188055040e20544551180214010713425143c0d14190518a00d0034242000a0906242c0c10420401203e088240740028400c03540810140c940b001f40c601030303001305010070605a040c1728203079000c01c041401042 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 673090332 1250 673089082 673089091
    0x2010306050a060c020d1509111f0f0f05091008040c090b0a05090c091008340302310509010b0a02153c01083f031e060d052a09040308 59
    0xad001007040360715480c1c0060381950070b9281c400501580260303003109000d041d86004000c11810f040d42400000070100e8035075009404541c000502942c24413042c44040ca04200c05400710003c18800041d10201003a0b016800740b041a01618100c0c00040d0041800000d03075000c8180140b080384c880900300001024150265a0308201e070703840998419560410308800001c1c05240026400041103003403054000303400004070045822560100c0b005c0140c101c0d0000100b2241d8407464441c1e483c101b400307100e03003210142c000202d1400d0030041207080c40e40000f120080c205601b0900300d86517030b6920a4403000c0702c091900c40070610600307200700078252030024070502c40d41c20800344a800f40e82e661000f41d6541c81e017011412a91205d070120b8109201840e003140c40c404092081900300b402001d1480d070701d42e80215035150b4986680400070381d150812050081e08988110381904091900351101c41c0c07504641c0c80310810100d0784600069200340303180742c41010000024840c4540d4036107424083c028050446 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 673091582 1250 673090332 673090339
    0x120715030f0f0c0f0e030c0d0f0f0302070f060504080c0405060406080f01021b070501171f1e08071a090a0e040b0403020f0d051218031602010306050a060c020d150911 73
    0x8126041c03051054010540009005005011042e11f030002d10801c214250410b440b0035440286100102d011900c220341c450f0300c04d80c0180f107a01c1c540307810843c103c40c50307070003000030041d0421080095402c0050054603010082b240010aa251100000c0c014551584188824080c1810110700c41c3d1040d03010b46034205886840301c2d0606090300650303455450b2402850302140c0018294481c06c0c140040099103c0c4901d10000f810b9046401302c07483e50f80541d40400d009805014042406a6503480d1090080004800801e1054200305168441c01198484900e501101150301c0005603079090b50310b00101700c080c036a4810360505003454108410125010303800340c8968010502d43d02800900c80080220b69650700d41017442c1100924228500a40701c0010681070044021582c02c0501c0200344e00c0c0d4a12500c013038181c1d001d10025060b01d40580c072051041d003a00000700506604060362190352a411074007446024120300d0840c0050310038142c55542c0500d80f284000410102c1d00d00a400000100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 673092832 1250 673091582 673091597
    0xc03060602070902030907151b0b01050f220207020607140a0314030402011407020105070215031b0c060109180506040609111f05130e0405060a0b120715030f0f0c 71
    0x1c03d00c607010b0b0b100a8801a80d540d001520800461840c03c8402650005030f10b02400054805482e9096006890348151006610440100130701c0c98407040c0c1199041c0b09850a101c802c640c100c0c0120701102c401018a55150000703509e000310f6841508698065034801980321400c0341d00c1140070b60f90044900101c0106600140c0410600e07000029284166816559210000400e04031116182c01c8030741c00300c1c10b214051220b003005a0b2881c0c034540e03001c00d020110341d49910740b4000011103144010484107959104002051000001082c41c5040d1000884042000726856508006006103481c001c0c055020f5031061104002071b17074112030801c60080c1d40d4118461352440030025440c0e81c1000c40048002c103108042140e5000740043d007071800e00c121030107102c10781d103100c41c4030982c008440031100390f0080c81c1008400d007414070071410000b0007900d402c9901140858626901c010700c2c0118100390448480300d0005e41d209400500d0540c1c11030405000201c0c4a541c0c1c1c10281c66895104008030f40e81 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 673094082 1250 673092832 673092839
    0x305071805240f040e0613030f030902010c11010917031c060e1504060810090209090609210d0e0f010e010c2106050303120103123f0c0306060207 64
    0x404840303041615511070042c000e049100c04010114210341d150681080d1561103116042c0c0c000d1114a00c0307240300310403000b103144161800400d911001d0a031170041c903180074901c0000d42d80c0100d00d01107e613032014039620914030340001a1707070b2880e10b5440720b407103218003000d003100e03061002c4081d0468803543c0303078010a44941c0601950559005004d254080941c07000007a103086001c143d5000000c40150000034810380340c0c0006410210420861030300c0c151640f089104600b000ca010560004800015203941c0c1001001c0c140c90748944400002c10000c543c0c2e81d181c1d114500d0b000ca90701005c2490082042d4255211010303259500317080e440c0042d501c0c110700034502c0201800b400ba4012099034400040309a00e03089241c022040d66a1542c005aa0300c2000c515614200f0041200c5044020450800d6241d0b20306000d161800a020004000f07003400d20581c1440003040340090481240300c18203c5019040300c6070808902100c0c03480c2ca0f64103101c200707d5403075016803107501a0354450307003545c812070748 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 673095332 1250 673094082 673094101
    0xf0f070c080f061015050d06170a2003030a05030405162c100b1602090a020903120406020d0c062c0106050105040f03020d080d02040f0609060f09090c090305071805 72
    0x2180c1c8103941c1c1401c3d034400701480d07a030f116000501d08003108507c001141c0b03454841118004900d080718041c01e91298a00c0780074000ca580c0c0030b00b4040760400106d05c400401c070003c2500d0b4081c4c3c60340c400a011000c00410200b020600c107503204044483d05400906a817032403440c080f80e40020b03100044901c12591f0820341180321554501c05d00700d000300920668076004a254145d84844041407980d072400c003d031801666188402c1e40100800400962128200d80c01c060421a2100096240010411081107401e401103400d40c58a181c60403c400701c00f00300c0c2481d4018082206035800c0c400d8146503c5046100d02c841056041c8420030000c108168403500156190b1095002e86802c03c1c440c41da0800061406040c0a0361662181e0400703424260882200d0040c1e07001500304202015107400c05001a640c4003a0090040c8030a18150300000c61010f0301900713200280c0980d0b040242c031031070740f8500f090191014070f00550307008048440c00c690f950200c1d0064030300c01c401040402c0c2000f010501141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 673096582 1250 673095332 673095361
    0xe0a060203070908030a02060421090303050f130f14030708190816120206010807080604060c181d0c03010b0304061a031905060c03070207150221090102060601050c030f0f070c080f06 80
    0x100c540c0c8803400281d0a6480039107032500460000c02c0580e0342040b050800d4144300e20f01d1802415819003130303a24a03040c0282c80d1a42255800c8581c06640b11a0041140c1c94000600d4007580c00f4002c003040d42040b8070304200c11188030300516040c0c400d58181c0b0038170401c426000c60111909180d400e0b25aaa62100340302c1391101494850303020258000800320700469802e612120f40c2886500b0000100c0c0620f03030440006148503031019140c411562000541caa12030b1050960110441d4001031079503040401014841c040608040c01103583d03201407000203003401c3c8000c0d40d140f10040c1150511180d8418803903210000c80b000300c81600582000c69002c07000d680c04d8a01a101a0300501005170400c10108210070006c00070701c3c1140302d18822221b50450108901d520050412041942e8800350b00000e4500301c4090181360401000300480e0020001c08401d44510580020f182959a4a01c03419400c1c01d00482002804458048000180044000400580c10b2f1808410742c1c130156200303003411042c003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 673097832 1250 673096582 673096643
    0xf0c071b080d1805012001020412030c0627030c030903020411040302040e0c01051c0b06040e0403020105060d030518060f0c030c07140607120c0506010b0d0b03010e0a060203070908030a020604 84
    0x540d410005620750b24040b0746c0030100705811400142042d980c2d07020b54214205c202c030150b012a0701c00305000d09012490007455281c2110a4402c100f030410905240401c00b4a1540a03081207096a0030504142c81040c800c402550024803d0203014a0030740c00c012690302c50b1004a10903407070030800c2e00c003003a4040742201044805840d21800c02d8040e102809009200d904065140c136914260307030940c0d0f07840c1c01c090809041800740303c028610f02850082e0031554040e001314441c10400d5804000a60701c042240c6144009803401a00c04001c0f001003000c5018610712a03550100101d0080b2041c0000400361024070000b07012035200c0b564910604920100150445801a0b002c03c0034001081848482218072001c1e0b24021034010150f484043c20310100380c01c0942c807050002420710700360700f50b070041c2c00c448042240204905d0240007100e6030340307003c3d0880c0100b0310398001c800a40c0f014001c0513002d004180d500181c0742c0d20895030780002d464103c2294100c031100e41d00c140800304128481c00782000c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 673099082 1250 673097832 673097837
    0x6030c02070308090103050c120108010213080c0d02130609410105041107060f0b0406050f010503150303070c0603020d05251d0d0605090c0102060f0c071b080d180501 73
    0x20070136404011806400c00500b28081c00508011030340e810308154000d10300a1150100050319841c0e08501030203030500319400f002850b8045002f11000c0d036100103541c040f09034110b904012520300403118401a00782c582c4500b62a505d49090114544000e4400702602180c612043c0c6000b21109006040182e90f080440c030780245d018014045401c09500c40481d0901d4480d0150808500759a0f100540e510781156600042c0c6850000846e410f190260b200909400c0f515010701c074000400003001c0d404010900c3c018103000707030140c1c800d548050040343c00c0c032504800e40305090f546581c40940a1340c0404000c3c10460701d0700000400d58440030845403072905000f2039219502c1c2c43c8090491740004400c120740c81d0103c611001c01020390b0ba20a014140d5485400d020800d450246411418070702040c00d41c41c12340d0400020062540e03100c25150380e22107080c21800e070f08d03081e0320308141d00c1c20040401c0d0002850513048005c54003030350010304c943c0703420b420b0f0351994024040841c05078500125403003010702 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 673100332 1250 673099082 673099087
    0x1e0d0c12020304180f050a051905060406050a030b0103030908030a090311150d0e0613020108040f140115081c0e0d08070210090e0a021303030f050c010e010606030c02070308 76
    0x14030290300d0182038645078812607003001d03210380c40c4044080d44102d41040540c0d0300c44c00d00100358544d00903154003050714441000903181215580c20709030803a03054921140d03030780c40000b5444d41d00d80e4042d80150030040c0881e02800c1d100e2800c0d44903580e082c041540840c25507500041d807038000004603512404c15035681c000c00703480c650380c000340b030101e048800b9070101c041481c040403800300d40050582c1d1504020b002c1a00b51001103501d080c080c02070901c0401c000d10003000307000361f41c01456498205a011a60141070301460428024a845496211783d895003801d20441c1c0341302c42100c2410981d018071050751a0ba02d0f440c0074041c840340c0310151744000b20301c1008104043e45044400c0c900100e004007103480c602582c6034009009100b044034040080754800805003e802c100c00030341c0d80e0095031039070210710304041c02d060500c0a42103444024100700c4400f90000c43c2c40e1040b400d42e500314840e007000303200203012146801d0180a580c012500000d1404051000315407001070640e01312a0420740e101d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 673101582 1250 673100332 673100357
    0x3030e0a1a072d0507090c053108061302010f080f0a0f020c10050f130b240405093009040903020f060a050a0506060301080c2b051e0d 59
    0x15500310604020300448410003010300504210503d03000b1040744210050440c1c0d03410f007401d10701200c1e00100601e040003014088070608000000800d80140d48800f00c000328064500300000690324180c0006019000b00d00502c400460b40596108407980300340c0314503d5080d54001d0458003440c08860118038462540d010600c20803003907004c4030f8105141d2402528120544001c2c616084040d503925a030300c1e41d524108440f52030314260168104401942c052600303030090701c0301c584591002d440060a45002e44072001e0400000c224401c228801501c24002e84c0741c0000656200d10050f045081d04001144200c40744826601e00c4031441030201031b519060400b09400d0100a001c0104214198407503c806070510340c0c410042d503485042c0142021505150083d103220a461f00941460700a900500040c8081c9001040750081c131746064603005095070f60703181c0074144001c509141c82002e0001d0200d0000780702020550081c00701d40c00742c485110103401803410750368103007590345000003696581c2c010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 673102832 1250 673101582 673101593
    0x2129060409021903140607050903031b0c13020903121911031b03030712090b130c0b04060c110a0e0105060714070902030601030c03060602060c09150403030e0a1a07 72
    0x307a00c402e0001c3c1c000803159100d003146080c180c2a40d0015a850110040602261001002a9640304206103040360900c400800801d0b56806002080b9400078010b00581d2600c9504010104020200a244084804c0301301d01c000029032200d140c1d00d010740502e08803a06900300740c00884800c1c1084c0c1515400c210106507040314818100d807180030113804100164400c25811070741c0010961000c1b4082d50f42e07030a01e8a4042d01c0010310031501c4500c0c0d03049c032800b41c000c507102c01340c075941c0140c580a440d00c80f9051850000c03001c1843d42c100340d002030302c08100071038031075848128103010611421031025007214a02c20000c0528851042051841c040c3c401030000d03040c03050103003440314810081880c0c6807464a180034140800394100c0c4c2075155020040100c2981d06005001410495090400c0403504100d0000e40301c5900a0601b11001000600c818090f1220582034159410082c8200d4031a41c40380750041002031040032051007590182004030b002581c407024007591007044455145008103075543c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 673104082 1250 673102832 673102841
    0x12060f090b01031b090e0702240c070f050d030605090609010b0705030c060411130504151e02031317120708130f0c0e09150105060903030421290604 65
    0x41c50406031a2001091030003039108a100361300d100c989818603028180303100d140b140b5100400c0c1c04119880400b45014541d080c040604c1c5110803c4000e00305507807290b102027564031844000601c1c81e03040006060a121001c05d1172001804955401d212265885007004103910017512040d511207062401085101d2414004002d801e00ca0700a42e410315040e10b06441c10584211070680d100d02001c0804072140c07400100080011041c120100014142034170340d81c41c3c01890001d00403070b465031a290000c600f8410240210302e220b105c2c20070340d92440c02207241a591040c490702182c40950021a00000488240070b543d208a0b140710031404680d905601102e401d40c01603e44070414070009812004101c601480340c03842406482da12003c1c0d8542544802002030003016007070150404a41d81128500030742015045900842e1101c2c0ca416010380020304520a5520034082c1e010354880c8030009049020311490764038011140104140c003000010301e0740310b0094030415405514480047c1c01444d29a22 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 673105332 1250 673104082 673104101
    0x114071a01060302310b16151e200d0e0f030c06070302070309240e0f030c21191115070303020d090c1815050a0302090c0d0c0f12060f09 60
    0xf2a91032170741c1d601c0d0401d041c2c2d03201d00000320f520010000c0042c180032444080b25a18107442e102003001c90602141300000d011b42c407504542c840e443d0301403500c1c03140380d94040030355031001195a1690388600c20701440080071541da100d15180111000d00c1c1262401100b60703501c0c074040502070080750b65620411402175000d0700c0c0071014002500c00c0401c0c00d07201f0005040f43d040680f4408401e100d1165005442c92051440c09842100c0d1003001030455103010403a10903111003600c04400400c600b10341061308000b803840c030103801e1003030b4000503811015071540c3e401e00f680280444000c01c880d40d428043c040300341d403001030400082000541c0c0080c0c842e034010404901d801d8800241d855850740c4903030203250164000d8000d0302e102c01c0c40c0703068070409200380c8555211054072000c0c003605e40008201e1001d41c2e8407000e8460781203400016000f8641c4011500d150320103c0042103550007103a000b0709454400c2c005480011803040ca42c0c07420803064400c0d8800d8481444041c0400c600c1d01881c040079100e6581d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 673106582 1250 673105332 673105417
    0x8010e09030412030f080f040c050d050f0109050d08130302120c19050105071b0c03081308010c08010f0e0708041203110313021009150e0114071a01060302 68
    0x300151842140d040c3d00c207990310a5035200300000a214001740a03000180900244641c030a00b40030000e00360404100403208240c419030006200c3c0e0405904124000101902135400c100002080210206e0020a80300782a01c0c3c000711a100c040402c500d1010700b6100901507405440381c0640030300b401014000516200e001c840403000600c8144511105040342211280e4441c014404a6500316104040c0c0100d2040510141c0c58242c0b10400d0011081c0b1010700b03a80c20000309100601411201003001c0c00f4900001d000031001460003c080d218240b10b5605040240c0c0e402052034a0f0440b216802040b860341c0c1d0401503260398030340040b140d08044008040c5981c59404029460740701c03003d18407e00403003444207503004451c018007060150310442c2c1e504001f04105d06004600246140070a075040c140750541c249118040165030140318501a81d19143c4041440300410140c81c451118080c00b090600f081c83e6641d00c000d809074002c40c04001407002c0004801200852075140c060185d00811 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 673107832 1250 673106582 673106587
    0x2041e1808041208160507050f040b0303030610050408031305130209010f18081e10020306030304030b04020d0602040b0307030f0c02030417010f060b0d0c050a12020c100c02010e1504020108010e0903 87
    0x117600f424401a50b4800855164004c29001c011918110030050011030041d50240401c1880c2000281c42c1d10005040c07070b2141c0c50700016220302c00d00c203005a030080c2101070300701c80c3c0e21021285090f44000e510302c6010310908012800341c0c0082554000ea4501e44010b03110103440030401172041e90030942182060751000760500d0006400d110802c02d10303d0000b0140305400900246580d10f41c20a036540d0401d00390320303004006020540d1000421a41142d4001c504031007551210310001c0d04141040c04003800340360000c1070200e89200d40c540114095030503a141005401d20b407400c1002034404038092000941c0043c4420070000c151b552880034540c217104000265044080300c404215401908880f118030f03408180702c55a21074620807050070781c08030305050313040103c42900244038520b100580070003da00070546910120081180a440e445048000c1c0414800e084e0028007c02484c60701e00c00c80c2c4920014003e162884103030300d6000341d070180e450840503800c2c550404105a00580200601d2004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 673109082 1250 673107832 673107847
    0x20f1302030a140f040308060d031205042004050603070519090504030207051302031b0c011808130f120206091504080318031c03110702041e1808041208 67
    0x140c402984560031144000070550066001010000001010104000404000e0001082d04829010b0b8030003804c640c41940246507140440e03c2074540c0302c0200d12141040103000c1046103803011112152024041024030b0004401000146c0b002602c440b03405401882003403001381040c03c000711524041c0d03588904241d0341e44a09004070347c000c0307809900503040590140510725040c50446c1e0b00a41c0030301c0640c29400e00d080000b070503800800d6041c443c50000581843c000c4020340000304c1c950b036041d002c100101e03882d05200c02c80d40d0003e0482248540075180216070a02c104421006580b0450000c0f85089031b50b5080c081c0c2c651024502d203910040c40180c03941d100d85008001e001500c4a40003554441d240c0740924880005103003207280c401d41205110407404a1803036074070012040b03d49400300e00100503c1e45081c89104075100a03410904180609d4800300b80314200c100d403070701c10b48002c21405039500e0800c1c0312151040d50080070740000300030410a41505003e4403c1403400391003890b18241c41c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 673110332 1250 673109082 673109119
    0x612030706061409070f230a08040c05030106030507170a120c12171f050d03020307050c0a0f18060e0411030609070510032406080103050d0c020904020f 67
    0x40000c41d10390b03440303450600c8410b5495007980320200b401d031980007290500400c05010040040d69071010089260801c0c6101729606400ca0164004001d01c140e075061000001040c0c050119000c0e14404110b4000080c68203051255004480c0c000000c3d00d251070400c16010082d460a400180040c4107000507000824114441c5642a00054031207038072080030361400780303003203e00c50100900340a580c800e22800701020030322040e070280c80f41c0904945c1d0304c1e08000100d9000301507000113400040d8005c20100b0180c00100501010740150211100419100d040103010071507401480205030711405c080004980c0341040202111003070001142050300c98030304506c0100c040740c0580d549002007070f03441e40d0750070305014060700030124401a01c001410074004c42c0e0762a4403003031440d0800d81d4a64080c41054110404000c51304504401801c0c80c2c0d030350f000d004141e0308083c00141e4090140316224150b450003441440005a809400c6840c40e83d255000c001c5100b07054041c054020f84e0100c000000483d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 673111582 1250 673110332 673110337
    0x3031209030301030c12121b170a080f0903190e060706020711032a010309050604050f0607020d0c060504020402070b010b0c0c22091410020a080c12040b061203 70
    0x40c4400110307129891410205201141540031a48a5540000301800314440c541c103140c0400d0035003480d04801d030100703604005801c4028001f034540c00c00c2c0c2d880b5040200400000b850140c4041e0303185041074587d6a00c14001e01c5042c0c0302180c40d580104440c054801c1402c4140c3c00212482c01c00f00d41d45440e8802040e42d613070110344111182a80001c0020406c01080b40342219040309800801c1011841e00e45412440094650020031910281594a0f07503803003504450080c1d03034007009542660800785803a958420301e40391540460701880700002c08091001441c5020031150fa582c00030350174030503101d00000307000c0580103a03081a000c01c0001c0115888411030341c001c20030003507010743e0b400b1801e040900b0861200400c0e0703c20320b0444880b501d007030710b01c2c0105911540c5070310b00060b50f1040d500d0900081d030b80c0c564800466008800c40700780800c070164040c2c822500e0f1502c4444540c0c2d00d071800d8078018882c0e0000e4192440034480031a0100b0201000581e010380050a000c40038003503040301c40c0c9540c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 673112832 1250 673111582 673111591
    0x60904141c0206040611030907170c12030306030d080c090d15020c0c04111602150c0a05010e3309070b0f0d0c0302040315050402010216030605100f08100b030312 71
    0x1a40304006104c1000310500c41c05201d103241d420350307a0860a04105107034941410380301d50041e40414542c00325512001f400480030700907000345041e100c1e60301251440e840b50030451340c840c824003403020302c05219800707265601d21600104048924160041080003402d2004440a5603400d01c1c44036444e415200c00e10080a481105000038401c4445030001c000585048000c940002d060500814842c504002c40c0c01800c10750445100307440aa140c1b031641c03110b000e0001004054403441940c2c00501c003040d400f5007080b83c2e030039086d1074080c20b00c101c00c08110030324408030040d01c18890000c4a45c003040f04000c00d401c25610825a100980e50745600e2107d07400294480e002508009441c00c041d0403144200540b0071107a090550174140b560700c9480014216400c1035404075295400142161301c06c1c8409071080010000f01d0110036207a0a1800060804588110304900304d104089418a0740303542100480720050002e14038000c10040c400080c041e040802074141c4024445101c01c030b0b000100f090300c907 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 673114082 1250 673112832 673112837
    0x311280203010c090807090221010f0f050906130b1906020706030501080109030e1c0204050c0301090f05060f04180f0303270507091107140d0f08060904141c 69
    0x8106a8010107007100d4400c00704030140240c6500c00c11507114007155800c1200d6080c0401030300d41545d048098099041040460204260b071400803900a020100107026150f440381c131300f04030301c0e1540c0c140050302609071030386640140407804a11852146e9000011001806800883c4807030010b0754540c00590f0035000780c005600a01020300c0a039038035100346401401044002c0c00300c0c581c20785001d8000e0400c1d082071401f854085030115102d034004401ca13020175a0262003040315140c00c1819090540003030185072411810324055920703001040c01343d54091440100b81c1402004030394100300091a03a800c41c01d000d858000070400100302d00c0c1a000034581d01940380854403001c9041c8404840d054142d0150b10720403440c00f0000406c01c00111030050340d10003940060620110172603103180c1d02908200034142003085618100b050b0003c2403e101800d201d4684101000016006492591b412180560400305d01000900803d0801c05100e1a101c000003c0d01e5040b07005424600307502c58991402000b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 673115332 1250 673114082 673114153
    0x2040509031b060f04020402070c2c060117011707080a050c01020601061701060e0a05060a030b0f010e151b030a0e01020c0405040b0a050c1c06030c0803070f0311 71
    0x40b1400c802090184401d40800070302000e00c4c00f8a50b0300c01030f001c00f5102901460b40826050100324200c000340300a4400e8031640898601c0c802101e05041c1c4c0000140785600c1940d50100c5c40341e5004561444181d540a42414001c4e070030000a100c0020822890f0a014400c407400001c0c405407d00c11004014001c001420680044000182c40e282d8181c0c4804c0810040141c000d458880c50107000c1c1c19201c00e4a06500001e40c000000345104005410041e0701410004a070b003c9a130305940000b220302c40a0706c04030740f64684000151460301e0310600071500000019401590344449100902ca4801c403803401e00d481c501c070315450318510b801c02146000030403020800194103607010002c00700c070340d171084030300f40039030710b4140d03180c0001c1d200c054200480b480c4c0b100c02266000400c40e0a43e024000c045c0320713100c40c50240c0381080010b84200d01c42a030b03c8040c94031000c00d8030301d0084221000541c1000f03081c41d0fa8250b564080755903800354800381032a4012207198490038282981e0510a00400c040200d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 673116582 1250 673115332 673115347
    0x18130f06080606090f0403030c090317190302040602120d0603061409072c150402030c1206030a02030703081809010603020301030519030e300618030901080406180204050903 76
    0x524085029200130f106003010740c03c10075245024110300341e1040d81842c1c042004200c204003034850610a400090a604001e035000c0d001c5840d04019210002c1e8121180c144c1c055141e806030228883c034020030f40142c112080420344813240e88003c0405012111002540d95a2502e8001c1120300113115050721203060030501c402c0800410180e40509022103076201c540c5c80681c00440c1000740c4600214010180100194200380c081441580200001c1d009554a241a8030020401d234011240310024041c3c48011800e1420001150000281d0150050600c6800c60711041c18035006101900541c40060b0312451039525030138903c9000301903948000d038407541140b078124149258400600790012071081000c010a034040c40c1d10302110003d542d0341800c1400d601030901c4c524240b1310103000381e4110b289445d000180000b890340c03103008840e048180d074054500b550f503101d11a9034900740c000707011000410302180c00c1e0741c812222406030781e41645003820194045401d403401262000e42c00d420116448 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 673117832 1250 673116582 673116599
    0x70c0b0307032f0d050c190e120f0d0509031c05250c05010807020c0a15140c030d050c0c0d0801090e0a02061c06030219050a1a18130f06 60
    0x62408281c407400103c00120700d99604000d0780990b03070340c2043d00b030b4556022484046080b82210078684c003040591802d01c0a500c00a03001000303425406004400122811100c900049940c2c040c1d480c4200c06000c01c010a03400c103c03020b80242d0309141e0706008840800440c821000801200810640c5a0503160b900158007c1043c00354445200000c4000110000020301903c41201c1540d109003441020b070303101c1d400100d00d07281441c60381c107030031500908000c1030070b03038070b00b0241e1000800341d5944070062036071242c00000034004da140c0c45400394410700000c0c0601c0c00e1034021643c04405603081a050a0a2031041032a10107882d00350004690100b0041c00303900a03500a06c540e6084c000018407010007994085980d81c40750101103900006086141411100701303411042c0255001070070103400c0380d007004204241e0603103441074903c6014071980000d0440141d6105043d13100d4081800c6080104102d1442c49100c1c1d02404141d100d21902038612040440d0b20404c9241014800001031150600001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 673119082 1250 673117832 673117871
    0x31202060a020c1f0216110a060e060703030c05070b01090c110d0f14040503031903050709030218090f0102030a1a0612131b0311040506040509030906070c0b030703 72
    0x203492185004000f918140d032400030700c15018410388656505090a05810781e0001d001e1160b91400e032840c2c0420350400e00501d80e90f0065600c404542c0e07170074055541c0009851118440d41c1c41e0b500700308184111b9000c00e000e5488907003179558030f00b00b0918061040d610300c140202d090f0025004c650380c0da044043c809a20524400401e060030001700503946a41e50054000740b88910142d080001043d0f8084902460105442c003d00003d0308407034503a140784640b2000d46100309189000285040000340341c41e8801d052000c00c80b900500309000042001c600d0278903010004000d005640321b01c0c3c0729019060000d100842c0b049480311000607283c0314801d042c40054100a907900e2142c1030038005180c04c0740516012a4024610500384050b00c1001e00e030802003115024411112411040800803d103c9110151a01e074003044a04018aa84050170442100c400381c512460707c0d8000d2001300b046007028401403c026015462100ba4039a440200500701c0c9d00890b0b2141c0041e440700c014028a000104c070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 673120332 1250 673119082 673119091
    0xd180308042003060a0f09080a02060601020d08041104020702030102090d061506140f21010b0918070914010905120c150a0e15040510031b2105150a03120206 69
    0x11441c10b400c03003120000c0d680c0c1c030024240c40c2d00555520700003094034610b944020301c000e42c480304003511903445810180d01c820048500c85d026029105c411410148a0b0b40e92a200d107502802544600d03680d80f090200940003048226010744d800c01004690f03a0380c0300c095080c018814240418001109002c04a0320b0354154044024081b02d0760b908001070655405075120710100041043d00d901c00d041000d0001401c0c24004c000e449600700000c50188065001004000015140e030707800b4038000080100d141d24202c0e0b02d000090304c00c500520001d03a1988848843c0081454080461511030000990070803455030b803205190f2080b140d0800c60f0400d43ca00b099100350350703100e103030030b10000b01d070090300d203038001042c6501c034590038010851480380c444c054902501c0068240030030324501d204068000d040511078040011104280340d2415841130300c01481c00d01000c0741c4140e80b00021642c82010b40713009082100c100c6c01072411200a030b100c1c0c281020080d40100c4804244052020019061200251 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 673121582 1250 673120332 673120373
    0x10b04110a0503010e1e07050405030607090308120714040e0103050d1812050a0804080109050f031306050d090204140a0f0c0504060c2604051c0b06060d18030804 71
    0x110802607500042561304480740032524010310381d5203a40d0b1440c040035003525079000750a400d050068040e40f01024205175003064007101e03440d8075070041c160344000d00c1e4440200300103010030602c022040700c01201038101d500c0f41030014000e10415000c0d10140c20580003015803090100c010000d220080009181950302803c1034038010309003842c5554000402c2c010004e00d104d007904100b0401c0410807022810a41111203e42c6581c0c590704020702a00080005442c54460003a080b9903260020007142d03c0040c8d0b40800c00c23031061400c80700752400d8120780c0100381855515000c01e005600c0721b00603c0c5010f0180303188010700c2d19169801c0c800b1281080c03004c04000b85441c49481c071840d0030204890540389582042d050190251030000391103100090f90190351140e0240080100b141e83d4094425240c003180c240b4101c140c426002100c01a00b910007802c010003800100d03d59007002002000b600a9440c004100c04009840445402e4505c00d001c5000501d0302041200b80407800d0450f0340c8202480 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 673122832 1250 673121582 673121587
    0x2130f06080f5d1801080a0614011404030501020c0d1722050c0406060f0f0201020c0601050d0c0b070b01030209070804050c040c020c03060c12061f03111605010b0411 73
    0x1241210700510862100c2c1c4109100d0050a144118a10760036110b0300c03c1e48562243d0700c050545002546071251407034240450003660110b007440b03e20b0f0040900780d8000056211400541100449110300030140341072640d0010400400440c1d000e0009100102c1da1200902c0318202c0c0920003020010f620701c0c00c510708801d21080c1301c065001c444c440081c3c43d2160081080e050643d0418509010b504600709a10a10300324001801c1034001c0c5030001c41800304d84034a8030340e1a411005034281d1080c1001840c00350046401440382d403601c00c9484600c14001e8108480040d2a40f110b04d1a40d8001501654248000030041045150401308668010000d1520f00782c1414644d031240d0b600c03216024611f2041d61203845480440d48200a51030004070001d0480c0c07a9810844c58258203944025070003180c00645100082d11418480c0602d1002d004d5000c40c00305034070050300114001d100400c1e070003814080410000c0f240d0411018260045406803000180300c40c050400c00c02115200c01c00c045c40310206 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 673124082 1250 673122832 673122913
    0x140906030a0b04020d02130903030e190201020a1b03050303070309110a0b1c02090a060809100b030303040f1e11010215100519030f21020a02130f06080f 67
    0x40b1500700e60003541c1178880c5480c0c0e43d00c030320020340710f284d00c001f911004a141c6540300080c541d26030005050035420b00241c40d603001424410305081e801d11980070380035074403611030f04000070f11403100c14008a08500c4800c41e829282d9580074116407003940d100001a45a1a1a4051105130030924121203012500c8120342403500202e0440e50103041d1000c4017109001194a0321480140c04861306070f44d004080681e240d40b6540302900c080400c1d1440c684900c1610708110703000e80c4a00c1418841d413002802103003103540300d03500c00750f108146040444500540890031410104540000481144500b070707200742420140000a240114007a03104401e02c0460b01400f440198000004082d02d0303041d2940d070410712802c1c5810000c128298001000d60003048590014003110800354402c17100c07110340d10011402441c0c0100c0e5a1511348901951200c00c02c00300109a40942d0b02c4801c0e002d4440c94045895561060514200345441c1203c40389904000c1c2c100d0b001c851441c400101500480352003841e103010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 673125332 1250 673124082 673124093
    0x80c041b0f020a05070807090b040c0813050106150f02010e0601140d02040608060f010510020c1c030c0b04080309010609060308090f03160f140d111005070c140906030a 74
    0x400100400c248001c59041d429071034401e000c110b440541000840d5000b950301c4007803540d188414410700b80f0b49841d040000720140341c0b85c005d80000a12070350350004551206e2101403c0c456000707804807402c0d035840c4400100c601c1c403440b4146100c42203480b00080003420701e10180c2900d600303000880c60b54001d500140420340d465800d080710b040f8199105801200e051011500401090b0029803c621500c02000080200b484a0350305850060b501101c99040078203050742d4402e5412121603020104158401c1c407665030b0216801e01600a280461140f42c039074441105820058a054601d0600081000090720090040000030050030100f0080380d131070364a54040501039012460f00c1440982140081594200141d480e6450303401701d040e41899a69001400c5036403280b0034034455002056601303d440c5480360318240810342000001c4100344039802003200445140d0901818010180518000b042801c48036a0240020591544010907900c040040e50840103044610a074004001c00300080d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 673126582 1250 673125332 673125371
    0x90b09190816050708031905030108030301061d060705060402010801060221030711030d0c030506011b022101020a0207030606140d03080709051507062f09040207020402070c080c04 79
    0x2500411082e40701c0c11046581403201481800282451040c0000410a0310300840203294054024500018691815600340d45c0303800309108807078258000344010400c80b409a015100c3c0c014042e003403da042100d050002d031040c3c1000f00141d130300e540160304200455820103003150160095000038061f0b68441350380b0a590411001c00405d1301c00c03001c4041364515018030045030704c141084090300d0301e54164010403401846440150381c000b03030900000c0b48095000d4104880070307207903801e520100c01d07001c3d03001d00002e801040b0001c003414415031119507100c0001c3c80608640c0d0011790141007103038030310300f400380517100981c112444020b5455200d040c9941c2d4040b00544040c0c0c9414155056668400180d6880440e5408076801001e519a0386088030b888034003e00e412882603c08102e1140a00b01d002d000e0300d0540d1034990400310400e00300e4240c880140250012a00044c00075242a030b6aa01040503600f08070001c4907200002641484500b0003400080000681034a04000000245488640d040e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 673127832 1250 673126582 673126633
    0x1a0a050613140a1203020f010f0b0f0402091914032404031808061303020d0c020f0f0402040306020c010b0901061106060d02010c0b04030807120b0a06080717040303090b09 75
    0x10402c005005580307480d54a0090300a160007918503003100018100030307403901c103401440c400c6540f800c61000f01103c1a88603488200c5001780450389490064400d10000303600c000c20b950313805640c100030010440d501d10320310070240c640a041c03030282d82a80002d1511341040840b00c04242e108194a446020f030840d001698095011302d0402403414a01d10036018086142e04403c005018803010030041034604c0c1030003880d0724840c0e0b08581c04520024001c80d00c0200c1410020740c44072910805204525088035881070100b002040140303020307902c2e91454101c0c1c7c0100781005590b511508006410300c3e002d5607050041006090045003c5d81e6106c11175110100241841d01c01c0110495003c15a4481d50b80741d00c0d074507484440c8076010f0802d0306010700200d400311003100c00200001c462b200003010600580383c0d11b407000341510600d5030030240705441d101002840c10f8100b101c1705824854080e140100e076030140c5c0c02500e00240355026401c0200064400419620340d5074404003110700c0300c605101149564 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 673129082 1250 673127832 673127849
    0x112d10050f06041806020a030c1e090303080a02120a0e0c061c051003082d0f18010212130e010b090d0b0c090a0e06271b040302041a0a050613 62
    0x96801c1d15003c10b1340745540900a0030035031020643d81c0c6010b8144d44442c07214281919154070322158900755050480c0060980300025141000820000b802010301e035402c50f4801d01d0150801404464910040c0005c83daa1070b41d0545861803010300010601c101000d01c401a540740d413038500000b802c403a007070401190800455968500003017040c400c04105501455105a000b584c03690184100c0101400801070100d460181c4040034144100c00c00c1299079103070098907007600708440040380c03445203810000528194001c1c40d482c11001e4400c54001c0c000d0010300002c1c002d0140c203111418004c000141c01c25940303035034200302c0c0d2503491b07680e80d0440c044194080301c0e01d41c81d035541c480300c1c86a50260044e02074111070716240c082100740c03a069449109500940340e0001c00c400311490006040c50380c2000354100c41c102d4011418030f002e0054450440710500410510305640e81e40890101d070028034905044280702c0582c001c00c1d10b01f00884900800080795030341d0034440d482d086080c6802e128031910a0707 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 673130332 1250 673129082 673129091
    0x30513060801060507150f060306020d06050109140d110907120608060417030a0f060f09050a140f131a071803081c0b040f02041a03040f03112d10050f0604 68
    0x1744101b41e080600440b038208410b020060f07991600b0780194004051220f041800c0a50114055200e51422800c58100c0b0036244400440c1000f8804680b480c40d0713055907112010001140c131500c4085015001d41c0700c9580328201c00c5414003001e0203d405542101000e900082c0c24400801d080400b118031158000340784035501d84524a020008044070103c8141c620704044001406620712104001125030071074042c0107035a24139106204980400140d072114501c000c0c04214079a101c12001c2d40e006003081c0c2d409000c4005e50302c803562205450420780c2c0b14403c00c4e10800108950007800508041810308181030305904680d10016280580030054940058402c03600101004517044114012400780c0204000021400008060344c41030050440f091104100200603202003000c5900c2150482080c0500645543c3c0807100007802c49042c0405204030b08900d4107019400703c0804148202448a00a401400302a00e042c5224040780007a03a51505e800c101d030041440e0f450742d0340a00708440025 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 673131582 1250 673130332 673130363
    0xc010909050c09040e011803200303040b0c1c1503061109030d051305040f050f1305030301140d050105070305040c06180920032a0a0c03030510080109030513060801060507 75
    0xd00500520407016443d50380c8a00c7c42040c950040d4542d0454003e08628600c0c5591544125940b4070041d10014100c50f202c1c0000303048041c0d400003404d4240020f030b2b00140e150f848040000c06071034130f16100c3d200542e4519030420401259210700781800c07910068040c209454900000e4561080302004414010700040103860050420007450241c1302c001e02c100040042007010400801040311802040758844020070001c54940140690391640400150b02e540c1c2040300c1c1c40c00d840048c180700c5030099504c02828000070820b02803035200e1079480d9400a280e10301030030b00101509051b40401c0610442050007442540c100044030705030703442c8400102d401107410b0f80e40b030401002c02c210300401c60b41c04400e01c414040c0c184846980102104041c400c4030383e00c211007041c0d5118180308032001c117940301618000640690406684555103c420b042d02c2d50f500d1911a080d104001000c600040c00000c900445d010b10340c120070054000e600c0d000da40ca605200c0b010b0050f10902c5800b41c2160792954030718 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 673132832 1250 673131582 673131611
    0x1050609250221220b040315141f050103020f12060607050313061413120609021302090102060a05071b06021e090301181e050c0a080c010909050c0904 66
    0x61001041c00002e0f10401024044605030b04003001820501c40c2124400800480c004140c2d003e407041101d100780b50074170715660021a01c0d480a0710420f0a47c494969004a01c10701c0c40c039070712952405614620800001000c1140c26609420907414103105001d01c0351204900e00907201c0301c259650141c0040e44034072001400c14042c07868024250f20002840c02c50b45252401603000701c031001c4e29200002c0741c6016000c4164000c00304841d400d0084240100100010314030341c6c40046006101c000780c2100c40e44c0115003841100c42c402e03203402c6d80004901d80156070420000c0d5101c80c0d00c5600f0011420710300f00040c1544003c0088c405e4000c1007a1100341804402d81c119030f0100c0c0d114000744140e10380200050415003142108a00ca946070051000c0203095290000618039880f55070140300388001c2643c0e002170440d111090318507101d0030344c03540150b481c0d0403020006440294020821404e050000500400541c0c2020300000c3c00c0c0028000c11075420f80c103481401034201c501050040b641400d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 673134082 1250 673132832 673132843
    0xa050c09040f0e0a0c0e07140f2a1b0a120807170403050109021305040b071404091509061502030d05060d050a0c06031506090302040902030a0203030a11010506092502 73
    0x80041c0103140100b0200803ea44041040b01e1050480c1e0301c06d035490b91016031713409001003d02c02c00075030b017004100c044644110052501c50352a03542200c600b00b040c0c503e090002661110461643d01503401880e09490020048060b5002120142582424080011140b0031400c070010901e11021550100300701030340110469407440843c009071240d81c0c030b0402c1030103002c2000d800d9025200c00d05040030301c00c1190240c107100da500600c45107215100c0c480d040310205405030084901075070610012401e419a40203c000360003242c114950300340e080000c41d2049034203542c00407803074131111410280c1c1c040d004420b0310304418082c0c8001034581c1d0707a5808110343c0b85d01440020110300a00c2c004008205c00d289032801501e0090303900b0010784060600c0300e0b804001c0c038050fa03004a007507814204014035242d080600e07183d00c09015502d0042c60350f40840d246411030b41a15011411040001c2d0300c03c0024844c150780140101e031200000c0c10901401414200300070f001c1c00c01c00045110b0f44060074002c01c0f2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 673135332 1250 673134082 673134101
    0x3071b050303010f090c1b020f120114060a0e1f0302040507050309012403080306062215020a030504030320030a1706040902060a080a0b04020703170a050c09040f 71
    0x25800020415180240d1281d209000b5100000c8862a02140003030140c8202000c00c103a540b1494080c45841c00050070500c99050104d03030002d503403003c54115031240c0e9503d07040048208004038801c1d0b5804045001d81c0d0004200500450300d5400c10003484654610441d00038051841c040f07442c070318038069189440d1150300007a4010b4104018402687e44c050001e52007000301d44001c0002c0060309080c00c404207a00a0085c2d4440640030040c40841c820500458024000810551030030018800c00c0060042da40803054940d001e170303841041070426114041610150b02e00c007510410003da58007810381e01850102800f04220503c0d0240b60213418079104e00051858000c4a4513075002400091100c034440180141c6d10034260045030150419002d1001000d5004010300d080c101003420031116904020078079281d040e01c40303c0704125510741e84002c20002c1c0c001c1e80e4402242009001400c9081c2c0007038401900c16240c46c0c02c0203c19440300f0292100c0203411100032402d08074100075a40545036001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 673136582 1250 673135332 673135367
    0xc170c19091511100e0303270a0b0108060901150e04030c021509010e0321090d0c0e01092a0e0a03051b0a0b040b0a0c02041d0109050f031e0307 63
    0xc0740c50b0340701900000141c40b80401c030001c8485140340d0022600640740d505214034819402480030800d214a01010b02c01c850090021030500c044131040810b24004880e80152030944da2000140201e400c1400301c0c5a112140da4000c1c820a07003464981d80c10b11200388a5280070b00c04040c00700c3d007010300ca82926010903030020b004031080b09901c10072194540c0038481160224245420080060402107106000070700c0040b88030340d2084040110f01d035103a01c1401580d41c00195103000708000340720f4181401c0644030403515012698104101e04040350f51035803026000c00b040d210b6050400c203240006003180c0c200c514059270025800c03004656800c0071a007005207140540d0f10300300100300f40682d07c100106011a080d0600c180d5940030040c89128500885901001c01c00c003d00d0a1406030300d030700c2401840540b0000f8400401d9444e20301c0440342c0409a20140d4440c1140c1091000c1001960050328109026501d4203541d1510800590210790341254180310110002d4821400303141311303811006850 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 673137832 1250 673136582 673136609
    0x6040c0e04021c0c03110306040203060f1807020d050403202403041b030f081e04032316170c09010b040305070e07140705010902130c170c1909 63
    0xd0003d6043c00d4a810942c25840c5400c40158040b0712a006070100350314441a038600e9034440e0740074403001e0340c402440141c10220343d424044c020f440b02100100e01d03040f0304140b40003e06000c00000d01b007005901c0b6070010881c00348010f002241591004000c02011001c40100b0341900c0c101041c011107604154400102c101c0c58909960000f076001180704512400600201c1501003d440f18101c210703001c09011445891040800034001c4401001c4e132a105a140543e007076000c00c00210154007a420840d0700701654090782c4003680907840f41c0c01e030f2200540054584c051240c2d003022003054980c4250001078148468032900e041050000079440c1e50043e20b400101c3d80c607901903e08aa000e071204030b800c1e20070120f0021304860312090703090140b60340360b5601780c070103409099841c03640e0842002a42c1ca556250f08960060f901c81c11004580d00c000c0c5000309035107000050282075031300300240c61007121820900700315050003d0801c440c20305403080400c804150407898100c0310841d45070401801031008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 673139082 1250 673137832 673137847
    0x30b04050a090308090706021e030c010609230606090d1407030309170111030a0207020303160c17120909091207080316030b10030c020a0c0b0414090f06040c0e0402 72
    0x2d410141c001070082c2c40f101c00c03988660350a682c1d01d584c14420720005807c20100341d441c04126588100035250283d084908003541c404119003110140d60105060307666404482c2e0303550800c00713001c030000f0544c0030341d8411038035003100802c8907841102c2c0321910030501c1802c15030030011210008a19904c0302e83c112260603890f85400b820950030b9003c0c1036000101019102034800b01400390705280f400f00b03282c01d8211788440642101a4201c6903049a050206005004109800140300780500f8020002a544907240410350202d080219020040c140c01c100c6115100081c0b42c4111620400141c4015105a80d4003030a581410b410343c00d5007042c5500040c0316014490f4083c0a5406080300e100940401e0403c00819400c9441c0c0d14030481e00024080c480510150280d40201c849840600580700c280e00c00380e9507404041c06a810243d854100801c062120189041c0110100c4000b5210b481103400c000c404952042c1c401080180324544400350411944c3c89111511a806006401036454004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 673140332 1250 673139082 673139101
    0x504030c0e040218010f052229042d020f070f060b01030603020d0f0305091504140402030606070f032c01021510090209120d0801080733030b0405 64
    0x74299020b070300c100c8101c3c4407400b4402414019030304848005e00316181c0b042c40c03e41445118021070320852004054542c006807000443d0064021081d85c4a0318544c0c08844d09603644540b202c01c41c1c0c3e2a008903d002d00b040942900c40a40308540c5668207441c0081840d20310200340030744101e104213035019030049141c1c1c2c01c00c00c050505032901072064005000401c903c4004408491003480045d500501d480a21008650f111042c08002402460032500c5c140707001020802c81303008031100c1c0001c40b40c0080d003007042c40c001170071080c0031503030803a030135895810998005210750103a114060602507406406d0410907028012201403190300b41c03449030340002c00701d1240300d801c440c031500c0c07034058022203c61074071405d05207010b288a15408080710103102c0c1411415002504500001604014001c0d0500f00c004400c01801140801c0c81d41c1d000210340c18601d007581440b0007980f0000d00c0c05914980c1544011341026a8030010041c3c2c0100c1c0c0c4150b20b0103000301d02425042c1261904545000103020082d103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 673141582 1250 673140332 673140359
    0x15190603050a1e0b06060705070e070c02090a06050a15050903010501030b01050909010e0613060617030c07231003090b1501020c030319030e100203070f0807110615010504030c 77
    0x40c06203000c003120805081ea0300c0c0c1a002c4801e0f0040c8501542c0c00003406515210b00504846030181046405294403404005102c03002603407050085440421090300b14580750300c1740356001140200c1440f52034505008035500506074094404030000f0025001d80303a600c100141e450301d4400500070722907540d4904044034841000c0c00303140d02035a0050002418260140035484030101a134004002c1c80d40e40d0b0380e620b000380300041800c032202d944800e00020030004040c08428001c00c603101541d0b0b65041e000b000746c1b4185040e846030034200c550302c403d0000c5c2407100c95a10304c007110640300c7c0b00c250032810008030010003034010014030741c0482005120a112900e80d50b109104001e800f20340c1245221010560389000e117070f149034456085600e11883c00c40c407a4100000d2202840112501c0b000c480c000705060f03030000c4401d50005012001c0702440270390b112650940202690a095000b40b115a44050311040c004000003080d0644400e214030591241003114025a0403140c4d54001c0f9807100d1646000a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 673142832 1250 673141582 673141603
    0x2031c050a0c0806010903080309030f04090c09050a0f0308180303130512151501140d09030801050a081c180603050901110f121b040e070f0f021519060305 68
    0x803440c00b02c03810049806001d20b54090403058580004241c0b541e038a6205070342c4002d00c0c4c94201c1c0418090590380d4441d100151001e0f0004240110307603140da058000349401c166500807440b030405024101b182d40d480b5400902130300c0e040300c00f6070b94030342c440c800c030b05042d0454048698240c8000141c1c5161440c001000c00305a4100f140c3c900ca19202007a825030f5500c88511101c8103c85c07070440030035110347c80380021030b10411041c1002503c8100c80e00c08071003d6003080c2e507011403540d04c0d079000300c04241d480070a641c00360100b00d0780900d480c2c0c00c0c090460354404a420b0322080a004500100b00d00d40c0c001c0c210313869a030072004480250141c4800005000d498203549001007503003411041920300a16a06071a44c202d86a5400ca080100301c40110300841009400c003001120200f4144039030301160402800a0018a200e441060410000050900c80494501c01c10020b0305000320342c42d503502090403050244605c44d000810b132101095012528110520b051000f07203400303000400c22201040401d80c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 673144082 1250 673142832 673142851
    0x7141606020f0d030b0a050405010e1909080d09020a1a0c060108030c0c100909050a050702061b0306011430010609150309140f070527070c020102031c05 67
    0x21690300e120590340c582400800d24615001542c00000c3c030b621a500000c4410002084032041c640c0e6080450201c0e2020307040b001d4480000c03400c1020310901151032103c440040c00c0c04100240035a1a0b900d114056001e0390b4010a403641e000d1070955540b464000d0181417640c141105e9000040303e0b0004e00c0d880f41c02e444082e80511300001898a00c0441a5180c0c0c80c0070102514004110f001000141801c20540800f8403100c20b901050a2505200c0c0c24881d2518290000309030820200191825030002d05451402003852150082e80500c10f050301c0c0c00c42400c0c00d00001480e0ba01c0b44e00d4805000d05d81c50040c1e20f0306000302c1814100034286201d9484030031702200400c3e41e41c907101c0440b24840f00e4050011045001902d514505100381c0c000c1075080d0264400f44190464222114100056814104929800903105001516114041042036000c041e1034085280c812010740ca10042c00405000900842c18100c2e019a4000e204880050200d52035000c0c1c1c4104844001c0d0003403c041c0e802148 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 673145332 1250 673144082 673144123
    0xb0108010e011a060d0c051c060e09190209070909020c01060905060a0b07080f0f0d050109060b16080306030a021807080115020c09060a1a070213090305041503020714 73
    0x4103e40031038080c0d0f10034006002c292400c01e5242a680107040814100d0040002c00c0041c4441030040d81d80d042040341d004036012980e54074003441c40011040c041c080e0749180d041601d20881241312003992040c610303416100407001e507440c1d500170b0721400d100c0c0c1e100402e618000540c220101006511a4040d281c10303034002c01c03841e21800140600401e5a005005d5185010000e000102d40c080d400b41032402c1c2103900d110318062002440380700301e800c07045035100311030380f54001482100000e0188001500030050120300b4000b1102c2e21000e04203002c1c5000c5c00311080080400c5440d2014040c10f80915005000c001ca070590044880070b00c0741045580c00001000f5030004102d00340b04152071040b9980c507a00400155402d0820091a0740000c1c02e40743d400180c0d8800029150500c1d0440c040d1303480003040660b1295210300500413070f0319a00d00c0302c254851170003140c403001940000554050310f0094100344608084208290024841c401010700846078014138014004d10004440344000f07807800c009032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 673146582 1250 673145332 673145351
    0x11e0b130203070503040b0406090f0311060703020c0d0c0809060c0604170306010e1e030709020c0105010b04050d080d020408070e04140a110607020315070503073f090b0108010e01 79
    0x8101c2c0002c0d83c2d80400214100003041c082070050024941090151100251010403581e9500741080030391812401b04400b09101c0281c15002d010f40c035407080f03041c2815440d1031002c04290382c880d00203200f040103100e2500408414004074a0996940144c0901615039034425200c0c020f030b9440046404a41c24410454440d03d0015410207480c00350006031119900c5e001d205041011095546a0704c0b0035005034004001358903a41008160002c140e24800142e595884901c1c813800c3d9801600004811401001304101e140c8900d01000b12950704100c1c5540c0741c81419021201911460780701034407605c2102c80200d600d81d40381d80f00394000e900c81c40c0110480940b05042680720b046038100500300f03002c41301701c020481c20b01b400140101480182941d1458400e510040b401c1a420f48031b00c00010000f10800c00e10383c0d000300656203c409070005403100c0c412090108541a10051341c1c2d005000982181b868031501c03540c000c98500c0e940301c43c801080e03603110000310340245004620001190708104402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 673147832 1250 673146582 673146619
    0x21903020a12021c1109040605150328091b0608040210120b030f01141008030a0c11032e0e030d02090619020f011103010501050d090302011e0b 63
    0x44251042039122007405002d80440c1000035044440764140900c4240c903050380d0084a882a0144c0103010561541c403010141c0500040741e216801603400313080803c803403416101c44002500e82c088100390b0092486100c540c503d100030803d038524084100c0c1040300450400902001c1d510f101840008100c0c289a9110800c50f5080c5041c2d401940105030401c0d5210258800c02101441003807561010542100010104e8540407440b150f118559540700c0040c0d001030807803051141c0280345512404070840c1030075001034491194122032024801c01c002583e08105404551292803003004065640c05420b2009450240494010201900340c0c5408100c800150314850440e0741c0070001c00660030301c0c12042c0366400070b5008280f455031090003407241400c01b541181e030054283e08035238058951904100318140c01d45424100b0031031000c40610051010340d92140030b8510441c403540001c030710808203082c26401045210305805415076844d8071140100704941050360340c01c0703058400040d280c115a030079 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 673149082 1250 673147832 673147837
    0x60708070e0117090712050106090e120a082a03090d1d01030b13020f070b060604030b060d1b060203041e030512070c08030714011803090504090303020f0a0302190302 73
    0x240760100d05269003c40c8112112682168440144011110626103e03200300b0300c88042e00f10215150382d1110410300183e8494040c10f04420050030080443e209010314600032401050091403c012501000030040071182072500440c0c140903100d0440700c0e0103a40c04061991003210007500390301c05c0d4402201100d110b4075141d0090800d60f0b031f888000d1110080110003406103003076160342c0f19041e01c1b07480f00e122100d81300400070b0084031007031565209000d2030616844600180003e2080c42e06100c104081004018481e90000d0111b03905e162000c100d00c0c161918040c5505500c160180b00c00300465480d0b0000700500aa800340d0811600658082141d2201801c0d036002c024103d4210071000002082c0e100040e054851003045038803001d40e2101402c5107550403e400a035001082400300b540c0710642807245650785014040d2200522030b003170701c0c05000f9962354802c9a000e240e45461813018948668151484000c003003c1059441c0d0065030010080d421500904004000100100700303d980079208 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 673150332 1250 673149082 673149107
    0xb0c190806030d140903033004020a03060509010e06100807051f141903091a13030f0320040504050903030f1303030209100903060b0a1409070207031406070807 70
    0x1008403d00d07800e8100c0b504100c51100005000c01801080c60340c0d68140041c1444e5040d0b24258100080b40f03c90004496801900340702800044109100240e107590441c2d406982e00b120001c1169120600c09038010038419050b95503501445044c450f880100464040131208a241250400b80d00d84080180c0e00c100c041013040609208040182c4040c09840c0c0710f0040388000d240c0604000d9103a000440c003c0742c0070000800290340d030706500c0402079070f0746080902c00345404003551030f4540303003111640286141c0409020702c240c0e1031044c441a4031079001000034140120f80111500c1540a0070340703c5c1c1c0c00c54020244282e0410000036010500001924496201d090380404183c55828241003e00d40c0741c0c0c02a02051740801880402c0e03154645c5030345103080150703251a042032441c00c000007212000542c8501c21409250304004a0018400c20155110100d07002c20301a150000140e141864a030710003060306840700c280307420329000803034414811076041c1c032621000d60310301c081110340e0381e407941 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 673151582 1250 673150332 673150339
    0xa0b0d1d010c081501110a0c060f0e0913060b0301110909090109050a030c0302071a13090b031f02040e130615030b07110708010f021b010603020f060c07030b0c190806 73
    0x100007501101d800e13181182c60180604007055a50030610029041403003442c0c0550344009496405c001c030581c010b120080d403600f10714282243c810b008001500400010f800d042c0b1414012400d0350900050794003441c0c001d20010002c2168180c0f24a00d08159041010014482d514000001d011703040c041c025882203c0d031100143c0104c00361640d06075031060150a06508502c101d22012507641c2e41120f07075441204c2e8103048180c8030f09030074044000c01c10302600541241030030000201d85c1d98400140c10100d42410340d0380225903c500c020100b000b8056a8880e02c19031030b1290034044800c20044101580764091038041c01410241e01600101040d04d1000404a9106000140c9058030072a1020b0149842c00f0a03202c4555440c0380e0b2a094900d8400d54071010b9500040300c02600c082d0720090702640c0400030003400000d25640005241c8550300d801140545e000241c840e25441c018015400070715440581c660580c200088503c5040d0070400400b00034408000390b120b003441c0141c40e103d01c80e60008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 673152832 1250 673151582 673151597
    0x108070302010807020c04140402131a01050702030a02151e0405091902120103050c010f090b190203160305120105012c03070b04090c02011b0207060e0a0b0d1d010c 72
    0x5900440e041c00e0004c283c0b80440c000d0307402c00745256455000c1c0300705030072411112801c1c80c2000d00401000c83c2288400c41d60f034510f0b012284c80b041c80c80d0880b103d11100c0902340161643d4041c008030b402c01b0341d06400298403100281914111b0310b03c880180c00c003c0c071000300301d05400c4ca0031030450103144203a01030164403129020010b5101c50500100302c405000303040005d403d10070f103044210700001080e081200c02e500304080307451903940d0240ea140403404040c82d1000003030385400d010301180c0c46469841400b1541d41412655820700800445044101c4000c840c0340301d8040f4200144260810240424110f812100020350380d0701c51745e9160b01520004083e406141d040001c00703880c0060704d0711407e80501414000088640306000034000a000400c00800d08100c803143c0242145c8182001c260300c002c640700311611181d80000c03008141c40050812a1208600d04d001a041810f2680040c0607103000180791409501e06400141140c6408500c940c20003407d80d16083c280c0749805100800182d08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 673154082 1250 673152832 673152839
    0xa0b0d17030c04050910090c0513030f050f0609010f060e160e030c040f1b081b031005120c0f0609010c06180b040b1e010e0712060b1c14010807 63
    0x2002503400c0a484841140f80c96a600003040349400d04585440c003821007002c00300084112405009043c0c0c00502d00249440c1d02801454030f0b0011900000d00980c00820b0100100001008201100c031039483c202e50389440e0408105010f00103003c0381c8425203051040020f90b016a841205004441d1442031a40e4124141000c46d65103e0414045506d881100c3d1003440ca40c4440c82080303c10203030154046800c002035201000140001d1035560301300311100342000003d01025014070250842c060009581c5d4481c901c1050b80110250880d540c00901d44206031040380c0001072000841c1c9041e144440103a5020781000000d00401c0e0959020903491100600012210782c0841c0e10303000d00740800c0f01183c64585955541010484040320050210f006005040188a800c9549804541d07800d110310b606060381c01d40c100343d0141c1400c0501100320b01c0344009000035081080944a01c8842507140c84038020321410350740090301900100303440d10111881c2101003819040c143c40c0d09000501c1130900e0b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 673155332 1250 673154082 673154123
    0x609062b06241a07110d0c0b030108030901110606011704060e12040915060e04020c032a0f030304150b0d1a01170f0705121f200c07060806030c040e0102030a0b0d 71
    0xd00e106d080f119100325101c0400c1803102100518040d0071560000d5450f07102d110f002500e118840d441c1c2c15040c1d403102041005076a44441100e684d410b18484031034003a221032501070090003281151000714050308848056800b00341d0b014008868050348288510300d401942e005a0500d40e0161000096107414511900c2c01c0c5034008007801444030040b01e190000d50780810303d80c08130b18500010009a1010800c1c9002e0041201440000c1ea20000d10f02c2e43c2000e03034901c440008a013504007012a03e0303040b052225a1244614524250030500280a02c040340f1440b000001e0240544000707051107004650602d1000526039110b01c0c281c0e0010400b55080404000b41c408114164500381c1c0b04421101841e240000507104110740500d03c0422001202c1c42e040310803174806440f14072030140c240644050360a00040113000c50704103080141807501c420000ca4104001c0c00358580d00181082101c0e50344a10550017540708014403041048003000041c20407800705c03c81071001e0240b001c03000c00c1d40d04030807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 673156582 1250 673155332 673155349
    0x50a030b190e100305010f0207170307050d0b0d0f0f0201110114060402180a0602030a030f02120406050702010621050d020c09150a03060c02060609062b06241a0711 72
    0xb64403160440c43c0c0350b0790b540c2e45030a41d040031000d144203580118480c0100504039005100035281d02d02d100d0300718a4420001030450082d943c6458045441e0400b290f66512000a0100c08640080030001000f1450412004411000d4000c074006610381480c0c0301180410312a8685580c0c601005a400341c98980070400a500070289202c400c01001c0400003440c3e998100d14802003501c1c1d00516104c880408000e82202d1171100c8099069004201e0300009d280030303603500783d0b0169001900044945600c0d00c12401449a50000110102d84008400c3d10201000070144418412021144022518802262113100052803103411500c0c91020a640c10b8a00c0e40c8100f07064000740021a049650303403030300810b444043c09040301503003003003090003801e0070000e407140d40c401c50507030f90890044500b88a4242801e2507101e9240d81e030100300c181408008490b004100451319001005080030381000c02403550f035446204210104607020400a00e00e40c982c030a658007035802c400c00c0e0742041c4900f410700c550003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 673157832 1250 673156582 673156591
    0x270a0302040e25080709110927011d0a0c1718060103030306090f0e0709020904060e10080d0206040201020c010c020f03070905070f1803081b03030106050a030b190e 72
    0x500a0034240f070382c0e003240e980000d142030242100c0309010b14608041c550504140f6044902d40c54100208801000008800c6800600003560614402d400307180c00320300346d042120030b004500180a800015010140190792010702c50300c3d024000c06855041000080360744940b0f40c04080f07000350031803c06545d004400581d00c2080801e00a4401c1003d0700d089045c07400981049000c25910034040c0132801d180d00c5404504140018200607042181d02005d070f4812070340c401c1c4020780d600018507081c80c0d00c480c0c0001d40201203040c0f0954807801c2540217030307180a6242c01465100c2c881e60615034140381c4002a040d000d5501030300940001c0c0482401110207603202c3c070040e80c20404080c09c403071032a1001c221a03401419100c200181a040c449002041660803024800030000790461440b40910f4458800048030b92061a9603520311520400b110310f500300943c2e4043e5804048000908070303130410010b00000720303103a4003045000700c00b804012200c95440e4103052000e8a14409003d600007072021703113402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 673159082 1250 673157832 673157861
    0x31504050c070f080316030c021531051c090b0f040e0a0b2103040e0a06030c060207050a05150a08071404090902120307030206130305070b010605270a030204 69
    0x914030310307440e90b103408680e04001300c1d506a0004100030110b10365042050042c080307890188042c00c00154002d40d0754402c6000d188a8083d2000800c18100c0200529082d6a204032842644c0030800c103100300c040b1000d280240c9182c003480ba10084c02a030003003020501c00003240c45243d1a00e08060f40462036030465042e4403040030b004c000114414036492041807098004c008007080d006449018009241d601080d000304915102c2d0b51b20034082d10200c160b40507100c091100e080360365100031010018100c20740c4046c01c1002c5030900841c4a550215040055032000ea0318400441c0d520360511078001001c8070324242c11101032006c400440e1142c51003c1d000f00f103601d06240410703800440424583c0c4035511400419594407007810031410010354038841400e0b650091801c00009881c080d4550000800c034500c0f1751b616502050416020360306488019801c45003041c040c0da12080054059403054003c1010901440000005010040b031084c0d00c40b0350180480441c0c5103150700388400b415001035810320 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 673160332 1250 673159082 673159087
    0x6070507020d061113050321090d1712060d030f0e0d020405160e0306041208090a0605010605040e06120309041e0c05090913020a03030c1506060806040c0302031504050c 74
    0x3c5040b03070241000c030b401010203003540c45078645040d01e4038041c40e82c0054002d40000228100ba201c0c0140110700c01c0b100720080b290780d202400d00050003600141c00c01003184040311002842a202c038000352000d10400047c0d891140c1f6844100298030780a0440240003d8403070140040c0c603445080d03580d0f1550005803002505102d1f5900140030740c2c40c2101c0320010842c4113000c003007015900c0211542c990703d080d4040c20302030800340c5030f00c0c2190b03800024090074020f07000c000c56401d043c20086502c145070000e20411044d40c440c08001c120398030034070030b802c081c46a4030045050f0745005d5183c92221400200110718207030300c20003880040e00d41c4d80000a00740c0440b141804c52012580540315011003c1d07601c00782d49030078081c100020108083e042c0c0c1c1c010902c1d1421000182c55a43c0ca007401c3c4c0b034050400c0302001d021450075034108050012810781c0c1c28204003001039500e80000c00783d0700a0300110f40510000201c80c100701c04a0108450509000104032055040e03030070709030301140d08202070102c81071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 673161582 1250 673160332 673160359
    0x20a021006080f070509130b10030602031302101b0b07121e1d0304181b030501030b0108150610020102090a0b031e010b070209060310090f0219080607050702 69
    0x100c54103503001a4039600300040c0f2021802c2d007070058038040c0008441540c1c25041401440d024001500c0c0c004082a0182c0d022525201c04c46142100665001105650b2441c02400e0800c403c142e0743d5041f400f900c4003041028500d4007800b620f0803000c250380151030000059890300001c2c903030098085018007680c1e00c0c000500c165140141490408603e01202002e05070078100340c102c1e044003640c0f40d0300d20b60041b24030003094404800c4070102d60000318100b449804042c00302c002401c4001c0303080c4003d104000705540d490b0701074000c0c5049a029107481c8140b0380c1c0e00d011003074603507200c10f892554000d42c00c00007034118500044ca0718401203107440018100450b89002c156401d00c250000586a14040208a4074000790700520700100303041d4244091952400c0401e81460151020083c070402d03201000a086480400014003402e13012001445414491705211115620300103080c0d00407084240035086a804442100040f45c11481c000d12269440c003204035a00d800100e004ca038400304a92050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 673162832 1250 673161582 673161613
    0x61509080c042c16050f01140a02100e0606090a0213031e02090c0c010c0504060e04051302100c020f0901060905090703150e090c040e0c060f04090e1c020609060a020a02 74
    0x14212104040e0041801003516614030901d029242d204a1046c040e03049500d813aa40d10224948d03050441c0c02d40191540c1c9880010307402e203070302c03486421489864139038000d48050340000c40701e0040d10150b4102440e6283e00c0d402500740d02c29003001e4488640c840d0710800000b6800440c11a0550141f05058405141c2d076001500200c000da4030a50002030225504c03030814170038413607103181006904100749441e1400300081c00311a4882c4083e481295100d002402200d1510841541954028019580301e102c0c080044c02d44562044c007a40280c1000c07556481078100080001e0585109807111103083d4601001c0000322103006015000b0151503e6000c1090200d610b4100080c1268541444491409120f203d160405000b070041c403c506140c0307901a800c0c4040780700724440c01c044e80e1584d41c4815080d0103924130303c1141e00c8a21718034640601d40442d0940421081480c14041811500941001c4002c9079100000d4800d00c80075000080801c1030304d0b0310350f4002e1036800c9050054030740c5900e01c3c581c1e0303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 673164082 1250 673162832 673162901
    0x603210a022d150112112206060320030c0a18030605062809021312081803030c0712022d01020d020d02120a0908060406061509080c04 59
    0x120141a000c09280c2c9512024807403400e07810528645100d096140261030324170b0ba4400312000e0904541e40e08032000360303200c08004451011503005940603803003401c0552001445144100b41c0000c0c509110100302c016060903031039031412400615811a200e1b503100ca540c0d40c1c407140c07011085c00b0425400854044c58014100c000714020040010545401e01c24001c80f1955801c840c00c4504808000d90200c0213000282c07800c3d501900070058541003146203a200740a19a00a20514605401c011040182c481c00400034440d1034001e40d64a200c0d0042416500e0140781165002500322000521240c1e8900d41c0d11031031180014140d01c2a90b8002c0041050020021228120004040c3d0700e03503940d503010040b89034403408510052500300b0400400030b403540100354824220840000303d00c18614443c12228000c0c01c02d401c2a40c4040c141841c0a90040070b04c0e00c50a90f06041091080c0e40090080c0554402c42e40d40740064641c04c0c0e15601000000c141c4103034144140b910a041031301d0280040b0782e4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 673165332 1250 673164082 673164133
    0xb0a090f0b0f070813060b010504081f0e030901080a050c040302131b052106061312060b18040311070803370f050304080c061e0603210a02 61
    0x1002407141010044000c2c01d240c01003041d024840c50740c00340032580ca08580c5020346540c1040002598000c1c00c00101c500d441254805029440790b607054204803105280c403185d0b20410001c0c1000188801001140c0b280280f0000e9400f01d400c41c0001400480d4640109900190303d01c100303881d01d5101c1d400581d400150904040210380d41c0c1b49000681c2c82c040c2401490716005042c518282400f1000d2081d03111240c0e044101c50a02c1d01000c80c0030b0740c50314400d0f28851003907030305141c4d40d07540c0300e6034200d08900c54088203070350107400e02d4400c0b007103800e020008501c03840a94031803840a40d21510256103000c001c2c44507951313520a510b0001030303903242031014003d400d00b0052524108012242c0f61442c11000781e0150442c070507c941d07039814941e0089107014807403507e400c0250700da0340c89040c018518020805038602c103000d41801c0001c40200b0560203001490041c07802c0b00143c03070740300078187d41e1801030b4025000442e4402240550b220000c0146c0040c80291040b0340c1808562600309440014400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 673166582 1250 673165332 673165343
    0x421080f07021c020a090e011514180f0714070605072003090f280b0d061d011e03021903020414160c06092306010f0b070b0a090f 57
    0x30610700b1454519003084402c4207100b01045803d01a07000124101194420041540d42d03908218440c07401c20340180390940c035000c03502080310f543d8500407a0080361819546100703c0c0380c1c0300003851000240e4250313800b440000c00030103502d517075118050354100240130110700c0700142480020000b0b219030184502c60b01e0603070b032082c032844074415031904c1c3c1010000301e443c403507002444010402c0c0c40c0c140c6407900c801002c40d803580c05240340070b9112003048019005004009801600800c812414000800001510003030030020300b039455481c6080c40880040070365000301080700410070f15500f112030307002c80e030343c445980c40b80c107940c0c1c1d40019a08003442400400b900046c010410940c44d092003006042044014015828506030301400303001c03804c8807505000d01c00380041040a03c80c0303d030700c412015076000300903030340c030003811003030750822100303107440003110f84106400404c054241c210345004991201a000b401d0001356610710b07102540c0141703040360701030342c5000d000041145142c2000700c45000d030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 673167832 1250 673166582 673166587
    0x19060c1b0303060509060409030210230408040501020606101e020f01021318090231060b0714070b04121406010b07050c2706040902040e010b09060a0b0421080f 70
    0x207070511911500040c0807c1c8201c3c5841241c002094011503134202000e40039000264442042c0d80880c3d44c88040c0e0b024850108800d8200401c1118000040c420b89800343c08a0b03d80d43e681c0340412200b032124a4050300043c550708204058002d20100001c032032002c5005850030400b9402c0000d0072a0000c80140807055200042000301e2042803164010200d0845c40c00d0200350b2050300859076141203001c030140d0300300020612001c08560b100b02c3e40291182081d09000c01307a602c801000300e6402c5860240c4c1c0002814403d40600d640004004044402c0c0c14000d40c2403502d48020400904811a425030f02100c1807110503000d4041402204e010f407810303644051b1180650708050340340600e41c03661107000308403205401c0031002e03524038078404454548104414540c4c4942c046009000a0364000303410505048885180220641084415420070740d008141540c0e0030040100008451151a401d080c04110910981d032504040c1122010318240b10300c041c0d500343c0c1c1c0352103081e440741c100c80740f60b134034003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 673169082 1250 673167832 673167839
    0x7020c0909030a0807180306060905011e0e060d0206091f0f020f030405040c030f05040c150813060b010c0b04080a030b061c0209010c020a030507060201050919060c1b030306 76
    0x6450240c0001c1000011070030100c81c03200103400000054680b106001110803c2e442d00400300d0540030141d5840002800801c2c2d0b03402e14580079040a0080200034044201c441c2451060184103400302c403140c22014541e03071078050500c44940c4800c1426600b0079001c0000300c4050302c13845841400d03005660482461130a00c505c000b041540410203c0003150460b041400201800000380c1d010342e076048500080c0d1270ba4038041a001002030303910218010381000104004d100d00203422904595130711555001c0703200c4201040b0b5000c2012a45411110303244500000410181e9011003000001810040060304c101e48451544510846003210303506400030310110000e5240c00b070b815010406482c07560405641c00301c14141c40300b004610350304107076001c070308030100b41c2c89117900031400394014141c0301c6050307101c0c100705480f003446005040140d803c000c08580204000101a00d41e000303201d07820ba500d000c155075190043d00c8074403602030410100e401340020390000801354811040c0b1035100010760328503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 673170332 1250 673169082 673169089
    0x90615020d0507050a12050d0c0924050f1815070c050a05090f040305041802041e05090c0703021e0c0f030f031c0e070303020a0507050405010f15110607020c 69
    0x4414007981002024003400000030070000d1074182e5180d110240500c0d45c080c10200302e40390301680c41003440203030604c1607038484c0640003200d844c103071481c49008120900071502c95524000b0a01103d01c001f840c1040400b42ea030000c48040c05101803144841c0d681951031200080910262010030515420001000c00800c1241c00590000b0403064800c0080c0c1881c100004d07100702001070284030000b40704000142018880c0e011207014141c06035a41c08a814201000c0c4001d41083c06074032002e5030f0881c680009862018125000ca810085c03652100e55101c5020642c0c541107003000310298400c09441e002d10351950602c9580f80144100105a40b01c1c02d401003061480014442d24020303084982500b16540001c011642d080000595800d0b0341584180d210300200408080401070303004e80e51002c070070076070702280c00c121a83c051b80803a48810b4407801040300f210805e105607100e5011044042050b0070400c3c2c0210b81c007000c1800c0c40603082d5115520030741458000c4404100582045c81503607020314 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 673171582 1250 673170332 673170343
    0x303080123010503010611010608061f0b03060d1709030102070b090d0e010807030c1404080f06161b0f0213051006020a08030105040510170625080105150409061502 72
    0xc510910398405000840001c3c00511041c01504100844141103c02d014002d410002c01444403d086a0711340c98516000e00300c09024501d18031300c00b03a1200c07001812000500603a4002d2900078039038220710000e50740f40540b01075030480000c0c040505018a4401e0750303080c4090f00c2c2071409608803440c180380c1144c1d80f0342030418840c200428000719001b40c042c140da2126480b84e1001c1c2c1424001007603051510192030030108245420204080040d022601d203c012030014820b81c1c000b412a100c03900d4200162090100761102040015184a41060071141045023600028060040800b0540362600070803002001150030280490b15001131100300091401000001c125a102400342401e080d5039401c028407040c8501d521540d1110302042429940b54001c40040140d0000190b18407500f031003141c0c03034240c201c400844041c0e0b101004040c2e40d04031032038400610100d03964503200381c1c280800c1001106030074184048482041c0b10220f0b601103e44600700207403403ca10110141c0d000501d00a1609 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 673172832 1250 673171582 673171619
    0x31305060c070b030a090803010b091914091b0c0703020a091503110438010f02030d0e0c03030708041401050c0a031409330a02071e0f03030801 63
    0x494080000180602010035402c0c02d90b030606181d19981e480720340981d4043d1280300c030040c207510380000000540c0ca45680c0184100c16042d181400807000a101e9036180303158030301c1440070f4010f07446001c040c2407500a14640d8489150342e00c0401e9a01c280c8040c40c0c01c1d400c6029044101d610699081c0294a0110304180040101200500c204c0442845508000c582840001c04210901d9150003040c0c0c0c031900304105941501d42e00034641c0c40c0c6500c140c14000303180c50319010003001e04c043d0b00c1301a5100d0103d50160a480d600210b180058008100f00145501112100c950092900d07591240e50140010000e10303000701c008544942c01d01138541510f4400800e02818000200080b01069502080c51203025405060101410f284c00d50032114500c40c102005921400382d40d10501512075080c14841c40f04c10300c455010504148142e04500c61041030a004096032101d01c08022100700c50a0031b213112a010000e5008050b902d41c85808026407640048010604a0006200c06c200300101031150 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 673174082 1250 673172832 673172839
    0x19051e0c040602070303030f20130b090603041209080f0d1812140a0209130b0a092001050403020301020304050f0f070302060910030e0607020f010c020609060606030720031305 77
    0x40510300302d4040d54801141c40000c0c18580c5030350b210140c0c0081a440000036080d9113511007002d0b02e20303a4102c442a0f0010074880b15007416400082803050400c01615181c070b0f1b010385180d01c1c2d510755071545541c0c02144a955000c0201e030013404a180e20040c071114100a000310018a010740816101a001d910031541e804d40303186d404c00c0e0402100b81c400401030103864202c0c0e40e00e581060404161350501e02c5192000c0d4101c209201846502a000c094118042c0e000c0c0205d051503440c0c002031030055441a05000d04104041003c21403c0758052504084440050400d1482d080d41c2e80e011902360f0700200c0707050742c154000c10101c0326100c0d402c0c0701600e200240314018090362801d581c0011041d00641e4211070144403401940410785000e039100748403403015001100d14516188000a40d40e00005108441550a180c031007002c0c40c0c0001011402002c06001500d01951030f6014000c3d5500300034182130411002c0304410314501d42c101c2c0503070a043c1e0700c8006103540300401d0010810300e0241e41c2c0440d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 673175332 1250 673174082 673174087
    0x312090e0613110408030c0a021807091404061a09010306121a1918020102010c051204150b09130c0506041805040507050a08070e06040603081219051e0c 67
    0x600307039500d03035050b490028082000140d2444014140f02c0768020f035002191513100c001030702910f6810024a01a40780c0c4202c0c1d494002c410100c1c0b801d500002c00340c80080111700802e0003440280c03046c108950b1501c50181c00003910940d00c00b14240701c8900b000c0c00028003200058040243e503031600170580902503803d840f4110010135900c0c10500c100140c880c0801554400115566621400c2c94808488440900740306441c01c0d50880030b107c0340303141e8089015600c2c0200000a540c0507105460021001441a07466580c030758950510581da1078000d005400c0d40c4400404640d070391031044600a00c03040c115043c0360480d518000340d00c3c00160700041d22a0b0000d0208101903588581214041c0080034408546500d0300d240030b902d08100c5402848e40680a010081303001000080c0d00d004480380b080c07440b58030f5205c4d1000d004c2103d045000c0506052400c202540450b40d950b02107580202d1100c28292140da250134200003125000d40e1025110007000303c4a4010f1026407040a4025850f00049031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 673176582 1250 673175332 673175341
    0xb180301050f1501210c02010f11040504090501180b01031214030612160902090411090a03020d080705070611060928080f12041502030103081803160312090e 69
    0xb215840040c0420b06030701c010051100d00740d124402504000043c641d40030795060f070b80310f0510302a03c070a41d00d8500541c80e00c0a00d542c1c015241c040e02c003e400050352040d2030107061405000140002e40003c0c1c0c0d040d922581e03000196140400b5542001c0c0c041d0354200060350640c908075a15400030b0504600b00045030a080d40c1503a140000c50b50031010440340c4034a0303088040189818152101c1420210307042801d4009100304407600202018002213408100302c995080150095004029205400c207404042c24001818108071850300300340102402410b00b0351559170700d480e1105540149000844802c0e0803a40c1000800c1103503048500c09000d03015003011301442036203011032400030401490500348500b007440807a03c201e0b038440300f110422954a83d81b150700000c606005a03011141142c0c04c07403844610000d2442568181d0703030b2140d0402e29188030301100c1440d0210100c0d031944c0c1800b40344204403040020f8820a8001e600c0b541079003888082d01c04000d0040c194650080304840f00010410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 673177832 1250 673176582 673176601
    0x120302150c030f180d0801061b05060406050603030d020d0209040621230f01051f14040c0e06030403020c0906040c020c0d03020304030b0403080109050117032a01060b18030105 77
    0x40e6030141e0002c016460f59541c152000c3c01101d030449509000307001d030350080c0b08070660080045059a40c035031680c0400825484c01c0c0d0185200590001e4825000400480c0000d1a00d4001c47c1d001100101100d043c165200c032803000720790104404188841e40050254031500b0b15000e080014001c000640010340100d8520b003031022040701c0010208540f9103075541000700c480400090003180030007207404d8680c1085030240284000d03549207130080e07640d00d011150f10301052041419190310b41141154140b40d4810300001d4030240d416142400000912101c4a8a40b8405988aa0301035401051541d84000a03c907641c1c401600444c081c604082c881c9100344e80010354240740401c282d989240855040c1009c90850080760001010108a003080c4006c1c035510801c0c06060b500c45950801c0f180e6a10722089442c4001403c0c250015042030042200c00c2c1c07600c40c0079055008101c0449008440f008440b14215030480d0006003045401041d100e01c496501800000d1000c4190020070090400010b271 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 673179082 1250 673177832 673177837
    0xf0e06070327080a030b01050409021605060108010b0a140a050d110f0f060a05030a1b170a061d0a1b1107080a050a140c06040b180d021309030201060f120302150c 71
    0x41130134552192030a1556902c25000c5030300502c0400021500c8004500446001101e00c440544051041100100780c2c6d55043c03265000545000304504003091030000354050b92250300c402d940d4842c81d10b160000d0b1036221503a28a00d220b11038402c5030f8000041f0400c002a10360011031103405410700c8010607070b0343c0d12500201c8280030000e0074a0b030780741c2d9144144800580071807a80301e114054444401029583c120614244481040d401c51005a51b0100e900b81118000d10541d6401c030507060170312440622120850360410b104034030105049665150303010506481440840004480d0705600b180e0080500510024008440140070044d00a80365550388840001000d40b10003d80041484101d0080203d185900c5c0090a41500d07035580340c1290b00d01d90001c0480d03000e48001220300110074580240c40b69191540200b0b080e80c200d032611050801400703e1002113040d50f40c0c503900850418600f9041d1030080054000307958424045141c0281000450080070100c00d01000510040b564000b09 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 673180332 1250 673179082 673179097
    0x709050a14030f03040b0703021e060402061c0c0e13140f100e07050301180504210e090c210f0106140d0f050405010501080d080402040f0e0607032708 66
    0x10034000c401d0070394002400d220a401103410a44030001780042c41d0a040005860344900070340a541811000012600c411010700701e0b14807880c2c02042c00640145401d40141a404a088809000c40e160035402c1c1807c40314a5402c41011446800c6603062070b2900c21140542c00c1c406d030009000c90503004031400c842100240220380000c1d0b1200000d104418200d0401e402000d640044003c18142084003510340c1c0c0c0207000d030240441c0030604807014551140100e5000740d0344404002001200c450b03908183d098151103520030882003079280c0c484c80c0da8200c00c00b030040554081c0c00740c3e032302015002c86030440b40a000c00c41d4600464410007805454070319203141101c1e46400c01400c84c030030300c03201c51080e0b00c0f818115041c4a0702e0b010071440f810304180d000d94480c510500c005c0003180d8139442110f5031600070701c10f01000104c0c43d00008d001402c00750415528441103840100c1d039105551941428040c00306c0701d07800002c1e9034110102042c8030404014840300740440c903e180c070105549400a20748242034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 673181582 1250 673180332 673180349
    0xf0d0c0204200406050405190617101a03251403060a030b071112090303090f0a031a040b01060f080a0207050c031006051801050a180b150d050709050a 66
    0x42040e040301d40b0b510a1180c42c501401c8035640d251502c41c0a030075500a4000c860040d2000203e1607a185410f490441c1034034810384520250200000180c0c2c03100f10024180849581044800189802441d1100708082000114079440e86000f918442a48040c00328441c441c410b5210024011a00031203611000150070045a03a02d41c0d400d004202c88407136690009040058910800a4071507100e1100043c0c03500c1300050303650014980503802d90368041c6100056140c2c01c00c200c2d002281c50400401702c0d0101010b08440007050b940c1c2c94903013602d1081c2c00d182030300c00e0100b070800080200c40601d032809003582d82400b51021404100052050000425865165030300040040c00d10404001102c24010010100c419000159411001a042c27600c50580900c860325036240c071210500e0030f00d80c10707a08041d020161151034400f148042c0c160022100148030780e01d035000240e9071120351048500703828218009595507441191241203e00040008007003107143e200074071140e07840c410080c08664100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 673182832 1250 673181582 673181591
    0x30b040603021011010e1014070212030c07060f090503071401021201090b042901021002120406111909050a05030a02180a1d1b1f05160b090604050f0d0c0204 69
    0x8004c1d0900518000c204100c035032144041000c0700860310f4100c02c020030341140300d500c00c5441d01c400c160390b40c042d100c444144460b010b00000d100b00d07100202500201e40101000f040680000b040d20040b6402480c044d01c0a4100151038004c0c03100803052030000d030f071103000210b24045100c0c1d0100800326060182c41022a1900704c942c0080d603d64200701c1d901241c1c0c641c403540d68200301124000800e0301c40340301c5000d4020082c940401c400d00b8804e54401c215201040e1280f540c03241d035100000d00402d04500c240200a0150180c210f00399520f20010300141e03206c80035030714249070410030b99802e6540322510a81c0100410760060320380c01c4580240c01001510704580382c44a01181e4054220240401400104802c01511180000600d19400703180ca210b5544aa404c5406202030260701d4512400e40e21a1400100f417018400e03001059402d400441c1018010381035a00c28640210944489800c0d61044043c0028840c050001400a01c81c200003810003c2000380c001c0c01807c14424007034491543ca = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 673184082 1250 673182832 673182857
    0x509030f18360415140601030510080c060d09050303191103190b150a05030a060806100b07032f2e021b15013816020619030b0406030210 60
    0xc41000f68183e0710008140480c0140541003100c0c0300c5c0803540b00b40068103000108802c440140c0414080d11000c802602c14101041e081c4401035000c0d1607400c2d55160b0b24001c410204d04103001a40c015105440060410650604058107030354001100c7c1f045450b080051044400346900e04902c003802081001c507045030904e001800d221000c444004411a0025605116a40c4140214030559420400704035007a180c1e14101d5803086c0c00c41d280f40c401ea03804402400315560075030103032454a12a02d0110b140140260b0070303204090400c0c07181c074401042c411241c41c440c40b0034480c2105489071070041003001d5545c0c40306000503910100d01450710660010301800c00b9003005007990b4500701442c040700d685801d20307103000390070190911403a042c0e1603030400202000180d5203856102000c1d03d8240d84009201e0700c01c02041c50b1b011180c50096842d2080f0110010786625000d03000000c2003011204288000f0b4101400307031a120382c3d5462140349811424001030791803e0000074204d2551400c50001d41d40d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 673185332 1250 673184082 673184093
    0x10f0e01150e1002010605180106090314190308070f02010c080a0c0e030106030803041a04022d0909160902160b0601090e160905010f0e040509030f183604 68
    0xc410303840a803c2005615124215134054018204a40c003e68040300301500ca400300350608075084c02520001201000c0800102e900c41005210540500f415541803020006c203907500601d402c00120b0100d012802004040c607000703003080ca92050b060009100c09175101d80000c0490b68002c00d0344842d20707034403030364180c03060312030802e80d1000c0310050005c009081d141d0034110155002114110740030564032148580b000781680000f400780b0b9020b84030035080c07422440d102c44102c1e0040d100c108650f4001c2d07002103482d03032503041e600c0c000d510b95009000c070005c482c1c0308000040c0d06900b246441c02e004005d5109448030041c2d0404034950044020b140d66200d80004030f40360384282d07005114680b130690600224840c007080385aa00308a40d200d40c0741840d0b4400043d00c4d1014040d01c0e003c00321f00c40035104100c50606800907584804020162898020380a100c00104d800011014a0521410302c2020340c0e4105604c85d520186440001d01c003684003003d40034502c441c514400d01028010b0500070404000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 673186582 1250 673185332 673185347
    0xf0103021c0506010b032d010e0a0207151a0307030c0905070e03030403030e0906010f080a0504060b062206140406030c0c080a0e030d0305060d06050c1b06070206010f0e0115 76
    0x29800010b0356041c0d60b441509001c0c0e600140d0b1071f001a00c56600c41d8081d82e18030128640ca40680c1140045080d130b18109014031100702c02003218074141d800f040b1450000300c07684150f0403425100b400024030721a540e89405c1206404112090080d8000300040c400f0a5480035590102c03030790110046001e07940e14004a50300c403006034149405200c0444c0200415400241d0b6601d540b5090b101050300369a0100116030700100b450900d0085a100800b04420850a03044a03500c98000c2b50082680c4408001003030169000f021090354480b46680008100989580100c0007032403186450440b01020b0f01a400782ca101d248071f131205155540c4c02c4a4442409040d40c0031100703401203041503c030764a0a1024001030781c84440103100e0301404074040f0f81c0307500030300c07a240c0241e00190242108214564945c001401c0c0940f06503189001442910741040b103100444241d8140340c0c0203440b403030821300c002078038055060700000d00c002a100410701c84103440002d95411141c800ce906030000b074108409a4404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 673187832 1250 673186582 673186639
    0x906030a060e0109020a12060f0204052b080f040806011a030c07030306050d060207030e0d0519170f070c06030c0206160507050615010207053f0f0d0e04050f010302 72
    0x140c100300000f61f82c1102546c100001030058009010310805000d801d4200d100b1400341946c0242400c413201c0444c2d15504c00b01071179060440212030304002d2900c542521383c0161030b001c01c6a140008042c41402001d0111900500c8a01e4100c5481c05440001501b50b0000800204645001081d16003c0c075100741c005c20001c01000e803000101099a0600d00301035842100254046201d45c851611541000000101903d4002d0301400c0c2c802d40001c480c52041d028124152807010500a00d421500c403244001d151840c88598615501c005500d80182c40106c00e038000302c2458542401c8075007964000c583c807030388400e01501002100e1180e010589881c02801c0f40941588034600c1002240718401860f001d601c0c03026022254610f81e42d00170400010700a120206074800c10002c5070a0703c0d900d8904d488800801034844401c64204000440d03d40324600e21120042c2e072180d81d40c1fa100302d800600d900406401a5000c0c000e91074990b01450b00c428062100a00840450086080212100310700d601c50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 673189082 1250 673187832 673187839
    0x20f180103030c060b0d0506060108070201021201120605010b0f1204030908100c030b100534061b081501080c19090509060a270216050303070e0906030a060e010902 72
    0xa5616818010040c00920b0002c5032442d10301282e03200d0701d180000700d900e40154064000c000580e11500116509c11000e014481559000d014450041401d142e105010340680c84904d21488001c0c208002951410780c854151544200034003c1001102011103965000149408003551039078501201c10302600d600000c200c2c040c502e200180d640fa2900401c0c084012564240002c04d541c3d02001443c0880601200104404124100160a040e40c1025140d040f0b01c5080c4800b41c40003404c0481c01c14913110840300c03030307030b99911402c601c0340d8292103810041898906101039241904c89165240300c61003002e8180084580007032402429401214502d0404c6001c02003404001100940300e07440901400e8800e14030701c40014168100b145900046500c0c010042c0703074801400510464039008003c030751024a40030800303403411860121402da01207202c0d0300151754914100d24002c00d46c0c1c0800d5162441801d00c90144201e40d540010380f44295900044005040b5445110841c010303c0b144100a40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 673190332 1250 673189082 673189129
    0xc0c0307142a0f04050105060a121401080604031701150813140f010b0f030303040308090708060c0c06070e01080a0213030218040302100207051c0201150906080d0203070203030403020f 81
    0x1070340d10301003420203841c802e50f030004103a0510b00401055038000d00500350000824001e00707800c1403180c04034400c001c11070b802c006003851400000ca960544240c015400b11b81c4800140020503900c0f41d1685922300644025242c07550404060020340c12103814400e04010900001c10340784022000101d5045501c206090400c0c00c0b444821340d110902004a20801d500e0301444000340d0802d403039000b0b003480c0010080d41c9150b40c7c6035400e031500309024041448a1180020105582404001d903501820394070112a844000001041c0d01e413900c0286040708004500e01005c410f079800245094029244650160b00d801c0011a0b5000314050741d80080d41c000c0c020816a50314004102e005800b07140070398245c0c1c0741c0c0c0d10791030310440981c440c0000041c8260b00c0305c0b00d1324044500d065000c210860b62440041070300b0055014005445140340c01c65403076545c3d81c440820860900f000020b11011980c0051410075185030006501c80c0a00e01c0041e00902008400c0401d07030b50781814444031800340340754288 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 673191582 1250 673190332 673190383
    0xb071e05190210052e05060f0c10050705070b1e0109020a030e0109080405011403091b01110102070b100503070e150415060e04110712030f06090614090c0c030714 71
    0x20080c2c40c0f401d00c0c51420045c0b00d021110000341d00560310640c0e1014019915010b02d038120243d044e4030004940e00280104180360000c1082c074002e1a000c1e04603036490a49030001420005540032000e001a411079001d2002c1e40300c810810515241102c5400340d0068940340e001c803041c0d0142ca400c0c040c618965103400e46210800c0203503406882a1142030b03071a4800c0c420721660303246107031006503600d014550000c910a2401c007960346004e0201c11040c5040542005420b4655084e600440022903141454408205107a405c0003400001044100c00410202c1e10304030301940c0307074640501180d1195160914441c06601c45812004403400700e00e6211403807654031f4900401108e000401e49101300d0505240385628800c18054440b01904002c00003a50300542070140d00801c400c4251402d025150000002d9585251169600074250312402082c4004040104a0380103002400b0354800d600a000c00c81c601000003090300c103d694440190400001790604152071710010201000c038040c101021030307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 673192832 1250 673191582 673191601
    0x6010c11030d031401171f0f18060c050316031802030a0309140d02010822080c07090b0603071416122a02010e010e061201030b071e0519021005 63
    0x2210000c503134040441a43c071441c1d03543c407510380505840080e078010450b06031481410481c01d41c040e5602040000e0740e403620801007050740c251201844c02030200071819000e0254071b0150050740706140c6030061851406141480c2c480c6c16420440b020159207501d14583c0161203012540c50f283c00804440d034819a510700204400d629014500049240d030039098038905140d1410b020540c0e0507100c0c1c22440d40c505d448942c241041304480b21805880d44c085a003c40c51180c020315181d0788200140008030f05000440040d80d0748104d8580c05010308000308140300d90b2064001810f5002c10200580c0e8081c4500b0f120031465072000c01500c0c01b8442d60f828400d040e0800c484000142050983c0083c81d103820314a0610740c078050704064041410505160010342c07140c040814032200050250b810310340310000982c5490000d81049650310f0703000d82070140107034000354540d06820070303000c5408000302c900400420600078840c04d4a401c03d64803402c10040e6000b805003051703007544143c08200900d811442c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 673194082 1250 673192832 673192841
    0x20c0f0a0201090b0a0203030a02030a180803011d090c010c0f060c090e0105120d030f0207081204060518070608180a1b15090b0f091801030501110901020606010c11030d03 75
    0x201e003c82d841100c0001d20400010569603084001c0e0040c6055580b03583c1250041d60000f80900c51050741c6804246035581d10301e4040000c0e41c0102c469540300c0d030416003401604140c2c0301c10101c030b41208204201011900041000c0c00780001c0c80c1402c3c41d8880343c40c3c81c40c42410442e400030111410800311443d5680d000b044034044a0b90b1144081d81a60798005204103500c101080c0c000380e40000e13542c0e035480d030b020707411105440c1124203005160075002d850b4590309070400c42c281c0c407448c05180e00b84401c2c0242d5005007504030302800303104004002109002c558a403402d1103444c003804450000651b84900307a1000c88506500d4005840e0700c078000c1d01d88070440c07818100000301d541600f144085480c2041100403403400d9600e49850341c02609190740360b4000d4005100340c003568034080243c0311031600c400c101510110ba8801d40c901a650451a01078251031042807819000c65017400001d111345c0e40060380a40282d4282000195120541014903e0340d40c50442c1d55094424440076840f6590305922 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 673195332 1250 673194082 673194103
    0x9040b04150e0d360e01060e0307030f1e260a1704051e0d121a09100305030f1c0c02030f1b010501270519090303020c0f 53
    0xc1d80c0540c6045115800854000000d00c00841d445408003441480c084c80155070b004800c0010310f80004c482440240c0a42c5031007103118a03021654904000812000088174050801e03800c0c0280345610040c0425510b031701900c4050446083c101e030364828070128036011000391800c46510304620a45081c002c80c0190060980208096007401018405100c1400d8030800445981c0d241c280c030000e005124a156006081520075000340d0a59443e00030203180700200203402078016000c143d09400025005148540f5203100c143d082903039044c600000300700b09800a10080343c986e0942d440c2c601d454580d003803168000400c2403000040d0310900c0d100e2400540260700c03c10f42003a241801c58003003038003515803a00a00000d68418000c880500f12510301030b1054030300c052004805034203501115400d4a2087c6e014205c984851a0fa02024907482c03002c198101201410510540c1461110001c0f2003e20944000009039120f410800301442501128444c0c0e0f40c01c8200c810540c1c82e880c51585030030020a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 673196582 1250 673195332 673195343
    0x3150903020c0414150f030a0c0e0a06080c06030414010903051b0a150b010c05010c21021204170c0a140105070c1707030c021c15060302060405060f040509040b04 71
    0x20240301d141c0c503103801001661414400d11484c107440d10003490080c65451008180c3c080303000f9040e0300054404104030540c95004030141d0320080d24200c01c2ca2203d09003e80300c11146400d014050003080400190310150a9042d507405641e9a00d60800e00c540c0c02001302054015400c0440343c500341540040989056000c00361680d842000d501001940c0719059940186948190b40b10015004503990180c1c42c520300c10305051428040300d80c0e54600b101d2800c1e0000c004940d181104e2000210380745051b00d5071021003c002c602d8500d0002080c00350b0403009000401c910900c2058840204400f41610721540300030f41100ca40c2c0d400e07454500e654590402d4030040c60340c41e10b00020b07402031061103102d020a07080342c881014080e04c1d0080541b294441c0800341c4c1480f0121140000503103c028800c1c446100801c0d020b5800442031800c0007004071aa0301ca484c0d040d04007074050025982d00c80488086420031075946a640c01144648817650003258020795015150361708000610007191309007486948502c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 673197832 1250 673196582 673196593
    0x403020d060b270a0908041703252102071e030611040609030f020f1302180301062d09020a090905060a0b041502010605040213240c080a05040315090302 67
    0x41c200c41e0484040b03c20202c0440b2400d5000c101109102c0c0d005d4031100b0301501e2098606519100c0c1107911525000000d0101e500001d21041c00e80a07403003401d19010383c000b41c0c4d00c00701c13103007501c4510b400c50310362a8058440d900b09081003200e600030040c2c0d000521a00400423401e4002030000d0034a200140300c283c89081c107246907884c03d45010412181643d0f21a10341398403043c00c603200d0307032781c0120b849004a800c14011003180c1e019965007840607010320584040035a0314840c801400124105129207a4026070402205110181103840c15061040d8002200c0030084020120090121038a80c00801c1492001030240b00040d03000c3e00b04000d4410308003090140d5180c54060240b5110548691904480c00340414408070419803803403950418688000b00d02c00d034569001030120380c841c5444c02024070b03a10000700309840c100440d0052130010801701c0480b04164100180c02c1c13511010009000c61000140000400c2c01003041c2d9001c2c64201015000d45108407414030010210070001340c0c058400e6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 673199082 1250 673197832 673197859
    0x9010e0f0307171c1e0e0c010221040312080f22080f0706240603050402030d08100b03090102040e13050a120c02060c030909090d02060f0c0403020d060b 67
    0x44078480d90307010300d000d50040a1400380b5000303600080c45031300107014030403190480f111035401a0350015031000070322545041904110001c450324070b82218031030382050680c040e2503a00031840c1e100f12005590504880c0c200c0104a00241c030503504028800d844214044940540c03100342584901c0c1c0c100990030305511070300700b129011a29101c180c444203120408002c00182c0d00400380c810f840c500100300f81070070795650ba5034040e84c143c014002d1341e801407150358508220a50050000805603400c0800444c1040c4e0040b80d200c6040c4c5203268280a1844c010176131481c2e12441c94002401442c0e4100d440c6d06001d44201d01030350042c440e0003071682509001c204c0b0303100f2000145506a40c004024a024030680d03451f80c0807034111000010904c8044882c13500941c0740c0380014401070400002035a0346a101808120510001504209042d0301508a43d13407401d4000901c0b980000c1e405480180c0c42e0358440d0380714210321594000941108405241004000380c581048941480072900ca414903002d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 673200332 1250 673199082 673199113
    0x916020d052809170a02010905060a0203030a0b060f0706020a02150106021509120d020c01060602190b130f0303020a2a1b080a08030403020c01140a0503150909010e 72
    0x20040c0350b180c280800981c1c1c40300c1c411000000c0361100c0d440d0504200ba15503813140c0e6414004011007800319600b20984074002c541e4010301d00170140a049034814180603100c807000355030b400003c1a80002c1c0e542d601e101d074503560301d010503902e01013801c0031040d0762103490345006006074022001e1240548204c2d00c2444100c00103441050580e1015401810501c4030881c1c1c0f000b58010103040142c5a000d5051110081d03820000180525109850090394070045090881e08440007544035204640160140405d040341d070105507102290090442c1c5100e480b0104a84280da44410009200d4641702240d0b0040503095005061501d0041c0c070ba0f00030004408818000f440b200d400141c04110f800302c54040002e182501c0203072207030104090f40f288551200e04151409242a0007541d03104000700c00c100401d50f0400040103c50b4080c03034070000e81907440e000c040060194900c03020030301101000240c00e4849620380c4202600c0d0090083d0b0759410301208003030080c5040032614003503010700c4180910580 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 673201438 1106 673200332 673200337
    0xb040c030c0609180507051b151305010b0a141318240903020309010509011701091d0309100809030c0105041b1409070e0f0916020d05 59
    0x5060101313403a10366000440b00d540c0039080800b08481c41e0340c0034003903a90107501e0403210b2441448010030b680c01c0110b2001110b08045006040000e449003003c040000c450082c0c00810140480ba07042c000010203078083c050480f0070b200101010b03410000300000c418005041d00081e4604801540884604500f8040e94103510000118601108981602020000302c0c00c041007031864a80e40070b5220b004003030401c2d05009012039000070f142d019103840070300d070b0b909018251000d40e101c1c10310030000c150070000c010340f4550a4181010307121000003103c01802008000c1c50102103584401c41e882040144411842e0100340f08078140010240503550180f4070078041c074000040900c1c3e03596080c100580c401c05107444005220202a101c60750304c5500304056241440300d00e050040880c1f00c504109a82c2c5400810310001c1000034515400500c09041469083d101c400e24a08811161030 = true := by decide +kernel

theorem cover : BRFrame.Cov 673021582 673201438 := by
  have h0 := BRFrame.cov_init 673021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 673021582 ≤ n) (h2 : n < 673201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
