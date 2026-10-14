-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1676
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:10:46.702658+00:00
-- url     : https://prove2.me/submissions/42ff0e78-3c31-49e7-983d-44c4885ceeb0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 301258992 ≤ n < 301438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 301260242 1250 301258992 301258999
    0x80f04081206011209050f070b090a1401020313140a14010206070c0804050d0c050301230103080901120203010902090f040b0607030305060415120b150a030807050111030a02040e06040614 82
    0x3141e8034240100c41c19403600844501881c28100781784d05100380420441081900c22003580d0020b07443d042c00c41c055100b0f58000503000500701d0000c110071108078404c460b485805105480c40c00102c003684c03500a1480307030051050b91a030110001c5141c58546044001000c05440751a01142d0900010b900c902c001000301080c0301d0340d01c2e03c110800c0103590440c0d0182c8001003541c5010125401c050005601c24041c0a01961801d14640b207424100e200c0c01da034035041e07002d02c00c8840c0e007582c3c0d03a01d0260304a00042814040049080c40469070035001070340c06046102030040e111003410081102000383d54403481e01030761a00c407400031152194001c45c0c441b560907040c085071589030400460010a8003003852400d1884020000c214121090014108a80150038540c0e440e00c4032030400d954140c80010095118001620420008540101410085005100028000c1c074100000141c1d40c1c003c850201a86071300007002d0090400c2d0f00030641d04404252401c004450400601103842220384c03400c00e20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 301261492 1250 301260242 301260277
    0x903080a081008030c01020408010f060305070b0d0f090b09061e060d110d080304170307020d0f05070218010503100e190c0902121005010309050c01050c0f070f06080f0408 75
    0x5265100c5030702c00004002d0601103e0380e43c42200d60281c000d400c540111105942007482c4d00d104d480361806064203403908100a003083c036161003d0264650700c0500035045035510f071200c00350003001600c940d1502c42d00031f40c1d0170403652411203805400e19038018000b411211103030400512140e03002c0503165001c2e200340d4a14485880740d091070703400c00030403500c0ba581c000c8600740c20108001000d4003541c080d5210300d65002901401e0744100e4180e001c00c480050040c0d10284c03145906038400c0c0050050401c0a0401c3d9180c030400da008036060000441c07a403d9121220401000f0500381080b2031400416201c5003001a4032507840c6d800d0b103440510f4800083e9480d0885800c0900103000c0c0040001d1240f03120440d030b5841c0b5000b0b10b0a040000b21100f40252030768500000d2194024050790b001c2c0d5600c00068280510322a0055403150440103030f101c0e02c0c0c45200412802c2090170481c14003c0d28692a5003501c151404100030201600100b084c0c401200074028800012000010303640003001030f0030b9401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 301262742 1250 301261492 301261501
    0xf070216030b060d170a1803080702010806040f0911090919020907170a0605041104031119051c0507080c0904060e030d02030a02132903040501180b15010903080a08 72
    0x407070446001c0009081e030045ca03100102524184c45c000d01d880140c41e207442c4003d90007001050300c060001d01c00508612000c20804005610620240b03600500042c800101820f00c041c1000460f01c0d81002180d08814460704080b040c0b07000141240c1c03011074400149078420560780103412014554200900a4460078085040c10b401103034000800c0340c9642400d03c1c146031551140f40038040a1040030b00039840c1032000204408507100300c0d015240c00c140344001380610402030206042140000010104403039002241d40d51760707180c8850860314803203003000c1140c42500f4018104400c07a84014200d6001e207140e60f200d03441d4261003c2d130254100c480051150240b00003142144036081400c03880901c00801c00075245019030140140100008040740215110110450b0300c0f0821041a0301c110621040c1d982d0103100342000359031044c0b00700e0002c91140c8007500b890f46825080c810843d44070440d0000c000540f865401d03000d051072003d01c0c0191040d443d5481c0c0b50310318461907010713004002178030300040d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 301263992 1250 301262742 301262749
    0x603060a030201121b08071103310e16030f06030506060d060b030109080a2003030a0c0309020604260604020108060105160c030c09060605090303040b130e0f0f070216030b06 76
    0xc4840a150652034048803084008000d11700491f846004551041c2ca0388804400010540f650400180d80654a8252260b10b01c000d918141c40c0c152848202d103030700800e0681e1203142c2a40941107007001c04c00030390100c03117020f01a1490010350b05402442c001c001c2000c1a00041d240780c03c481c00b0b0b074010a5094840c10b00101406840c034402d84c1540c01d20303018500304023500740108116400342d60b441c0040125a41c000b2540b0307c4070041c00386903500c280f000c01e000304860b42c42039801800d03074180014010310035404540b09030004e5000d02e509403054040f6400300790600d45480171003800f0302c01400791890f0039030001e84200030280041c1d04000d8046480d071040c46a07d0f00742440c01340c002c41c040e01525a01d240002d100c0040313000d041080c0781004230000c1d00d80e01940598030416001009542020304080b8241001d0f0230102030ba0121040742c41c0c00060301d1000080150060303880000c248030300e152414090941800c00b03051402190b11030300c0a40c021251081d403100969a0000650445450b0741001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 301265242 1250 301263992 301264001
    0x150c15050c04030614011d0702120a031d030d060605040e010b030411090411010e150d0207111504060914130c021e100c0507020310390305060603060a03020112 70
    0xe0130180707844540002918070500d10342c101c52000c0500e16a001100480c003821401c00d80c1e400e40564040f1107210818801c140c0a0040c40300103141c000f035100007107242c2e2076040000a0015100b6040080c020000141501800002d402c0302d081c00341c9418170f042a64131002005114281a022010010500304621800c00c0041030070000c10f54101e03403d25060020383c498051000d46e000c2000d2540c0380c001d90030210a800328a80108440303600301031501240301c02035400041e0490f92640008502c90b4141d949032204244080200c0b400d83d00c85040c040d024100002681000c410f0b8a00003941b20142d540c0c9401c144a0460007003408510300700140420b92504201d0712000d0b184814151028620b03d000003003e000002c80441d050103000c161a209440c140702d9a03074040d4064000303410141c0b40034030b00c1d00034000c400804890310445003c042d000d411300080d4150b441e83d0002c43c980340c03074007025414003500d500b10034100d869074558105180018101d4a917480020f05110159141c0364218206610 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 301266492 1250 301265242 301265249
    0x509010b040f021b0601050a03020103180209090a03090b090a09090606030c0b1c180305160c0e04030f020c06310b0a0908030a0806091f09020301150c15050c04 70
    0x52051104a0b8807120180d0032141e210040110041e5280303aa220001900c40d040311409813400c021f85003190011000f4026085294129180e5028807100586400c02c0c81c511400040001c0e203503d41c0d880c5001000610f4030fa0040000080500000306a9901c0c40c45000464400900c00144940286040c0c006064540e20280c45c548183c1400100c1c0a10040200b00d601d0114100010b60260340f0282c23012201000b40c41d070b06040000360707103c001a001d280103141e00c59002001208000b83c42c0e5a52804c8d9086030400744594814209220405802032012141068140054a0404910707400719005010340d034080d40a026100c160035143c421010204031003910700f0741000d0100e980301c00392441c042c0c0c803421030100002c0b06c505002503010b4003c401d17103c0c0700000360340d02d00150b00c07240d041201201005c2c0403620302d8015000025600300425200800400b1990405a26507246c40001d0b101d1451a01d045000d01c0700ca03480140016050ba2580b401c071300c4250340001410f8942c001d460320380740110740 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 301267742 1250 301266492 301266499
    0xa020a0501060b040f05040e12070c090203090d09050d0b0720030706020c0f0303040c05040f020d020705010c090b0406080109050702031902010e061510080a150905041b08100509010b 80
    0x41000c030b03958144200078801c0c0c490602417075a0056884081c0011103600c00c00c1e1020035004800e10130642183c220040503154044d04481711b0054a1700c2200040781c0c81038824001c6a401030b0b10402110b500300c900c25008003000c0b585000003a44ca52254a00d00c00021726440410055940e20303908401c0c0c0c03000309160201c18204407502c0302c0f03040ca040e50003980301c0c20350950b481c4155011185000c0d4000b045a1203558026000c04000d0b1810061001410315a8090101c040d028060f120580481d4070103031a6036805000082945000e8640141c403c0182d0380010820400400003032100a400001d01c90448050240c00900c5030ba1b07d0030101c0c01c0d8000c058011009915004000d50119415001289000498420fa13280c1c0e4851041c405014440c020b41d03143c1001c081c03c91002580d015120030f070f030711200d0312801189804010342205a411126000107500e02d96600900081c024003210283c0c010081c0701055450078101b030361041e91001d0b0820000c00a984510000744811420b405c04c984544025 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 301268992 1250 301267742 301267751
    0x50604020108070302190504030b01361b080a0b09010b0906090307081f05010b0a090308070201031d030d06090507020604021905130b010f020a111507020d080a020f210a020a0501 78
    0x1c031b8018111b500c20711060340c0c1544030f1400030448015203115030103001c07050f410000c1c1842c0d0054148000ca05580c55910040382d954098040d0003028039060a143d01c642ea0b1120f0340e42c41c00942290840300302c0b0ba062030090754140d0051000e51028000c6444072007081303889030f0315111a034000904d40b0442d900041c41a00500c1202c440c1c000a0ba0035056184100b814244a10307038a0798843d174124041c1c480402d001800c03802c01080412030100007071000c540180b4021400c1c0326005214141d096024000201542c00001c0784e8042c034550744144805080070b114248403038180701c0d0f03000350f031007102801c080d104402d150250340002e0401e03003c0e00000c001c0034110100081080c0000c0b03004101014003540400d15480003000c03401c0c808143d1700c112a41c4088021300e04031520051104403c005075001600003020020080981c3d030710170300340d6119446003580395910020034100034180f1128548840481d88007004161080b0f5001071361404022190403425251100e4103412440d00c940c056014189504e003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 301270242 1250 301268992 301269037
    0xc020a03021b03010e031810030c050403081b0a030914010206010f0b030903070b0a0c031416030203091609050402030c0612070c210816020d0e060f090909061909050604020108070302 80
    0x19074107010006402c035403108c07400d000a0003e40540b071848110100090040205200264850300130300880f480302c405002518040c0c0a8051030b2019413441680440d40b0301d001009181e043d2210700401e60070a101500855241400340c42025800d4010b0000c0e0b10008400038030070040800984120755000b400407040760814902c0c400081184c0101c20300001e01b0020a410001c401c6100140600f1030544804102121460110025040030f04081c01074001c00c2c001014054000380c0c2c51015180e2440d0000700fa04080c4101413405018025650084c0014000b0040c1b602d4080c55140e071100e038604082d8403051881c40d21211018442d04815140c4614501080c480e940c442c0a844c400c0f0100102454000d600d1a4103981c2d07070403000d207520b0021725080a42d03091070801101502180200c00c0c5860300b4202c000380082c0d01c60a0845240510380e00c0001001003007403400e150500001c0d83d12804014245240d05c0d00c1e500c41000400107810300400c40d0100312464403da048400d24086180b04914443d503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 301271492 1250 301270242 301270267
    0x209030619111305090c03060102030d05180307060f05011502030a050703020309090f2e05040b0a08060c0a030507031a010e0d050105090705030c041401030f08040e0a06090c020a03021b03010e03 85
    0x40780c01864000c00c40d1700001007444611004aa0180c07005030010b40c00c0034038002c0410081d0000404500300c01190041c44c1c01030714020070252182902c108400704804003060044800c60300140d10038200512410340700030b0070380d0300842142c03070008440c07420701d6403014513040580c510b22510301d0454102001208101869080842d1a8024030324810a100c0301d400d50301180149000c1a00d403810100400c1da170401c11031520341d000100d0900c014103500d00d00c0341c1c0d41000b181010300c204d0304910174110000e08103e0f400da16204031036000305d950070704002085400003c00e80e03840342c4410ba1814800c0b2400c0004241d9a402c1d00481c503507500500a2186242c1502d10944990700ea11a0714040d00c236540e0090070a02c1c0500030400400400388180780641c4c07a64032400c00c0c255490905071811542040040391a1000c1c0305042e10070250036070042140e501d400300d100300302c0c1c0c1105a00021508400385282c0000d17804512404209003502e1808004060540083c1c01447c506004c005c56200c002161200e412 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 301272742 1250 301271492 301271527
    0x12070302091003150902130e0702030316231c0c02031804020f0d020f0c0102040608011503092f030303010914010e010609091d19060609020903061911 66
    0x3000c2d07a1541504140503000d80c10745181c007400002e04c1e54106418060688075034040d01403620b0043c0300d542490b658585a25410500395440b030010b07000002003018105010031324070b090706114586280c000000b181c9051480742d606465110803a00050300c1038145030451408000c0b15514901008507983e41640030703643e0b9104450380e1800f4040340104d94406e02d42842952010110326070601e1405400400d401d00944c0002450806450180691a82a442480030b0000303070000d07865031101d650401c81e240111171600c031928010075040c05492000542c09001d003c0c1280c40d402ca102c0080e00500110010312000900e00c2030b01440084000a40c0000c03540080520604102800c030442e601c1e88520b9003600e40034050342000c251015020403030906654030030b10790025410103403500c05818103801ca080440c1080d150740f00403a000500e2042c0021482548000c000412045180c0041000400c3d00c40400501040099800c0c1481c9544103081d60000c0c4c9500c0e1041107240e03070342c195402d000983c55 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 301273992 1250 301272742 301272757
    0x39051c03060501031a060306190f030c0504090213090312091b2909010507020d05030c010e06062808011506020d030911040b0307050901060f020f060402010507030503090312070302 79
    0x103410020001100c0d40684191410400c036017800c044d070300708090180310721584003800c02d9030031402c0c209051695030460040000500700c81031008031030311f1440c144003e42d880907401c01c5200d189404030220041e540c041140a1140c40b54001040d02640e0303007010341c0c000304000644000181410117007010040008041004c040c48101c2c2c0c0007006445403502d02087c0e00884210714048580000c06803150110006442a10814502070b890b2a015901154103290801801c503856440800c0e51240340000f030081c056a41d840324018205071038a500000c8000e00c80100003501004030040d105403a00c4041c0324100580900c00003072049000e200341800104649204080050154031548a6054400d018003c212034004d40358151004020f000c100003000750500b81e55051041400000b80ad444840c0c22034000c09032511a00c400449600c1d010703081840140303071001150406402c11005030780210649005980503c0d08549a07602c014020345148660342501c440c0010303040400c01896403503001091038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 301275242 1250 301273992 301273997
    0x1302090301060e01060f0810090615030515090a0f0e0f0c100207060801090e150a061703090d110a361503020112020904050a02040504060639051c 64
    0x4159450030f0800d4240030a000c2d0100266449500c0c1a81a1103018000e030080340c24110020b14540d45c242140c2114100e03807009240302c00000784005007640610541d503000e60003402c20032200304001c000130403a4600801340d044582d80c03110b13030305802000d95100c1c0001c034115108450100c5110030b041d658421400f00e2040c8030342d0a0003180c1d00c5013480401c8010071601c40ba111808207900300403841c0051301e6000d003404207a10503400d5180c1d10312002880180281b801d04400900241056689600300703a8484580980340d004000c018180c0e150103100850007074002d5400c4029080840028a8000f1564440d11040e1100a496485c1c80541480e019001850301c03c411001403850a040c030544280080794816020041c004001550060107411121070050b0b1006207010071002c0010100c86040d24004c8060307a0100f01400f407030810f8886c80002d042c0d40d06005a0f08064100140813240d030960b095010700e03216896000d041c4002001000d03100e680300d401e03280741e4425038001081c00100c02030075000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 301276492 1250 301275242 301275251
    0x70906111e0c0409111c050d26070905090606070c0b0a091d070e01030b03060411040e0706030207060b06030906040f150c0e012c0d17030c070b090c0105040e13021302090301 76
    0x4010010751824206c19845806041300d0940a04291806001542c0c00c8410300b07800f00d00e4014038417858642c41d104046603241d9804040c28042445038040c0c00816107070040104204140129484090b40c004580d030b0f0449165541d00040c004841072034a40d03104542442044007180e1045008160440c0300728500d940d40480030b100140110280d60729481c642da0941c000348041804114040100f0780c040ca009480454062010b070250f41c40c095566205100107580800c80c1e5041002e5806100341901080b621b150450a1134050151a501e010340001c20031100c107410202080a851441d180c807a18580080100c0c1240d60000380003007040300786540c000703810240c00d810380064804400502010700c00c00c280041d01a1801c0c403282c5584554159240c0701c91001c01404a8400760046101d100c02e640b216490380c10324605801007103c00385c008074440e0070060394023020b6684201660215680d210200b0403d4070384980c10008044070400103901300890780c11402035003806400600226100b03a0003000b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 301277742 1250 301276492 301276519
    0x607050118060f05011203050307200109050c040207030f08040c080102040b1804050403020309010302131205070509090606030a0f0204020c01090303240b12060a080312070906111e0c040911 83
    0x8044130310074054040d200d084200d0580c01709120b0006103510040c1820100b070600340e282c02220548900c4081c0394010b0307440700134450400000b0322025101e04020748080d03080401a95014102258544001e010401e002d00050b00b0710070613040c0e5000800c40c01e802113544544415507101d05502c003560100003c3e203c140c0b054100e003024400d492250b5010390180d41003005050044010f07510100d6041c401601d07452020601d03400010741d040041e441100141105031a200610050b1140240458803540003482003181380d440200f404c11915510560200078407085100103002805401c803069055840c0c09020000c041d0036a002c15500352003000701c4001c0144038542442403110600420001000603c07801821030780e04562107070041001080c1c62007035a200d00800c0d2454020b402400c12424031241840141c0b6001404680035090610f4100300340c04080940a5403062120f2080341200318480200e170703035881d05203c6042d00410040041c001011541061020003044c2c0203458404e559914852 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 301278992 1250 301277742 301277771
    0x10e0a0b030f06040b031605190f080c03010c1707050a050f03090a0507050a060516050307140309011803050604030f0201110d0917032e030213090501060501050c1b060705011806 78
    0x2600c8080b00491507c03a4503080c0b0040c0141c0c0c4081c802c1550042030748120104120100d55100750144c10001c00038901c5001c910109401e6610000300b0109010502e02c162103615484100d550748071034581001e42d0b8840070040d00301d4091050a10307140002c2e00110510161320070205000da01035028000316203225440700708105040d5068400c0c0c401155003000b0700091441000c030249034043c000c0c0143c0e810800d183c0c40350300390048510101c04413500002403c11056821064104100e100110164030305401c641c0d40c0c42d0740d80b2010700301409000c14a19400c490368400d401c44d02c02055104542c2c0c0d01c4ac2c030f806e194500038010702c0008903a652450b411402c0815055004e40788521150800302041c44051180344101a1164400358480b40160300e010003d84c5840480d40343c41500580005032020f1541410307403c40e00b040c0c00c0705040100402007460b044c0300004017501c18509000c08400301e180c40c030001413a40d00c00c00340010202e508164104101100408900c00d0250040078103002140c102c0328030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 301280242 1250 301278992 301279003
    0x20702031c020d0f020d360602030406031a0d030e0a03021504030501110f04060f0504080303010609080f0705090a1505130608060f040210081e0412090801110702010e0a0b030f06040b03 81
    0x5000100a0800c110940907c040d00c2c40c1c1403036201000380c05444600c005c0c03007105991030308014090b074030008d01002015410b1096091318080080c051901c4807006c00001c00d425040340c0c012b403c110213800c01e031000380c0d204440c13031008650040403003000b040c01411460440d00107100c00c0d5125403800c02c41c071580c0c03602d490071600d0440b11014010700d41402c01000395010110206000301f0001c0600000c01c4440c3c0410043d40a03101584074483c0191600c01102c3ca09544840340e44429044104100b285480c0c0035103207a0030035000040403c404541070042c111033401a03104a41c8030f280d003078858140b504039a1184050700d11410555580c0e03514140f54420249003a50020b400c1480c8412603290705101d07100c52a040414011305c0c5101c0e15200400002070102a41c013a00c01c01c012400c80e001311134001c0825801001080020301180b04090000703d458054000f01074180071101d1008c041594a65240d44003801214841586034100b04941406880003240d0141c000e91401c068070029140005d0b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 301281492 1250 301280242 301280263
    0xa06062604020d0507090612140c1806030313030b0702010e150a05070306241d0109050904020a08031305010e1c200d060902040b0411030a020702031c020d0f02 70
    0x120041161281c0d400e003c8181e4124009540d0390140510120340029980143c500074644540058058803540c185001c003443d0083c402e010503400226980d0003034403203140304070f401c240203400791519540312004242988610503c241c00170028a5000c410418644903840c080d1085500030403094a4103904240d8640842201215403040c0d1800644212601d40006a0003c0b50b49004581541c1d25290100319605a421030741032650f9021a990a01c0d51000828101ca10015451090042002c4c0064403100060003468003590348940010117544031020854002c000300c508480e41e610300060700300c0c982d8019005290020702c803824003016a24254120f1005054224204107003000b048c1e0b074206003034500360b60740300d000300c8111075841391651390384401614a80901c1003c01c40c00080d20410084500318000300d13220f0340c9011030440d0002516020303207900100f034540041c0c0c0c034440c0703000003450034140b0b0001140e01d44240c40ea85990540c04148070070380d03030b0b96501c3d000804507018030241e071160ba0180c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 301282742 1250 301281492 301281557
    0x3021c090b0c0d0902040e1e010203011208220b040812030402060d180c0b040617040f020907140304060902130504021c141c022404020906040b04050a0606 68
    0x9010482e031105050007000200e80344400014120040c0c2d02043c1940c0c0040d0510505401140c49101200d800300b80c0c1c0c00358490307044001c502c0c40d230402c41d10382001e06440ca40980000c0e00418003061419035540e41c0c841112080002014456860a00c03015540c028050400e45000d91807030004014002d2050f03d004550003000107042034051144000242040c1c2c43c44030712141607040100114000200305400303428112a80d590700c40c10010042d0041201c8021007070b041e0501400c1002180007460401c0d080b0303a040720701206544401004030b0b00108026441c8084840c0001804200461031744440d400710300c01e8803a05401d040c0706948901b1920200c6000c1e4201c850741071085004c0b446d120b803c5c000641314014060040c22004802840c201c8030b880380e11107000500e200b10061580410900d8505030541c01d4030152140c030916110141000640024000c000c040040794059986d41c0220071004c40203402046685024139041000c1c02d41c91207440c1c0450a4041428905180900312030315525512 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 301283992 1250 301282742 301282763
    0x6110a030c08030919030810050102120a050f0c1605150304020a03060e0304091a1f050a180b070b0601080109060305070509040f0f05071401030c020d0c02010e0a0603021c09 76
    0xd480d04082d81d80700074054044e0b4020001e000124080028001c00100e0013a6a40c514929188100710b00d0201c45420680c19584040b284001c1c0c01c18600c02c5a1403860140742640e2128204400501c403801025420107003030144210160f1a03001c42400341e000c0712002c4919403444031584040302298407007542e029400a01025080c00850000d402055814880e00101ca1170540e83d000b01d001102c40400e5a1700f50700101c0018038090307250a102c03004070100100c4000f582002110030140c580d1245a45010a2044aa107002d41d02090303c00318600600c100242036584246915106504c008211070075400b03e200c0701c0c008a001c80c4240f158000307490744100113141c041c1c103000802400d0380740100111048056000e9420000d0385141c1c1440406109100525147d818400325505000c041d055050405103404002c0b55503550004148810f08080d041074079a148950004032a4070070303080300345a00407604444c001150f5900d58014002c6510b42000a003441074500070403030540d105900f010302240d500b1b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 301285242 1250 301283992 301284017
    0xe070519050903030a09050310060e070c0c050d0f060515030712080f12070906050909040b040c0509070e0a0510090b1b010c0809011506021917040f06110a03 69
    0x440100d03848540150030880d041c030400c90300003451079004081807400551009810000d17400c00700003034682c14031444c0003030004030309100341103041c3c15008045504001c082c861800a00c08102c04003809040040c00700c20401c0c01c24104030305544a103400458865103403a001816007040032400da144004001d000d002258606080407580c0c0440d00001c0c2c40c440700404c105004000305000401c049012015007000da450a0171000d010180d1a0307201205118007006940f000d6912240e1586c0d1140d40104450807070380721400c041d008000603030405a0032407240000d01060310b03001000c03042185001c881c60441140c40d502484010480c600808004c0f610710b00090000041c1000501710350070640c0a601c00e00f181c480c014038251341c000c80401c40424050700501c1030000081c00f50711055104951425001454900025525100580720f076201d0741403240c1c05d8003040011050340c00640c0079080d02c3c944582d2204204401c213103140c403900c4080340c1000c280002c00c010100e04c8850380da0305500c600d1040200e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 301286492 1250 301285242 301285267
    0x317090f12030313050304080d0306050102060c040e0f0a090204050c13050d0803160507050d0905010306050118060807050706150533090105070f200301141b04170f070e0705 76
    0x100c0703808492901087c800400d801d00c003005000401da0b07841d500442d00624203c000ba00f00384000c0c0a811010400300b1060028880401c0c4a80c1c02c5400d6450502c1c91b6990701440400900082c2d02c003c0d8020300f80801d101168030120050881d40da948142644401c0c0d562040040c9019000c6004080381021300004420600045a00b80e00500c0f50601901d043c45654400e401c0c900091840400319114180c14850355074544600301c042c2100b03080a0303001002103819224102504d00c58202088080d070000380d51288608261030f10b280e8442000d10800050401410103243c260281c01d02640c82c610452140d4281c41c0749116060580070f800441015000400d01d849602100301036060080811007900011482c2040c0c210b40c9000c1d80c00c46000406c4010751444a1540740380c03251203a030415020040c0940b290a0090f0007d5101d04125000d0030f0184411815016560044087c40f2340003d15420300c980c003003a6085100c91140903540042d40b02c15050711041010b03903000c80003420030b06c15512400c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 301287742 1250 301286492 301286521
    0x10504050601020723011b050106030c05040c2705061201080f06040305030411011709030d0e07050105040603051b04082107031413170a1a0112080708040317090f120303 74
    0x40600d484058620724050380c9030301f030f4401c400455890395954400c005000e03003a88144003a2404480c00e000b0b038060b040f4000c000301c3c500c1c066081094421900e401d0408030a400200040c2030160401f6100e038007040a2055187c000d114100f56401415800c112000002c1991031040798941c94950444c3c03196180d4052100111000302c1c14020102440600d0340031803801648612903d4006507030350052102101c0c1900c445a60307940203503000040c00e0003143e81020136242038421500d00040c0d199141000b400d40c02c526442a090100d000180108810344042846404180032003a003080081c01d04901642070300c2274290240015100d05051000c0100501c003d00e0701c600780c16402d071215501d8200040910302c05046c08551b076400b102c0d0744801c0000d8086c1c2c6030007010000104200e6580351840d02e07010700300d800c40018444031000840c44104650401510040c3d50842d0301f17158a0007581b00e070004141d00000382c0e82c1c0304151241114a286c03808000341884d15003006c000d5419034032100c0500340d40302d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 301288992 1250 301287742 301287809
    0x403020121060305030f04090e06040c090b0604050d0503040f1d06010305041109090c030d081e06030a0f0b070801050301050402010c11010c020d0819050301061b080c0a0b0105040506010207 83
    0x1c6807500c6002010031030030005451003148200c280c5036a40e15110101c012191240180d0079190415410000801d81400300c1508690201c0c5001c2000178651000401c07a00c22030704510341c000941d40c00741041c044004081d00688000660005c4500d4607481460750541c0c14101c511099038800000900c11f5109400c0260800e1248001c20400e400001c0082c510050448031070545074000c42040c04589410010108945c01760300306280319040444402c054695165643e28490401c18045051902c040181801c0c041c4c04c01c5002102440919084140c680c055680c40009002000045a2442e040c0b0030305004c0d641c1615403010703050140d42c07003c10300c24001c0026418046007114500142e2505000c00801d248a0404556a84200c8884003214401080010704000041c0010300007190040003501280340502241043c00f0090328000801d031055075031b48412401901010420000100c40c0a1306894040710240225502c100c0120380c5c42d9554891201e05003420036140c00406498243d00124 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 301290242 1250 301288992 301289057
    0xc0103180602181003020f09040c23030712060b071b2610050127020d06060807020f010c05091c08030720010b010f050c010b0406080114090304030201 66
    0x603aa9aa1188022030f00200c014001504030340c00d40d101c1c2890061a80380c030079542c40c02c0440c2400d280e04400d0400d0f026441050f80550b2303440404020b00c034010b0310381621508041d030340c100081000703c40c411901c1d0019100742c0085245005400c142d2440c07402407406503a9003201d924200a060b403100860041440e05050400c40e403071001051001801d0030301032541591012496042c051440c0c6140750908121080b40030b2443d0500510940540c8012070401310300002100c5d2103207040e02203800081c401c0c4113441c007001c5e25080d000a00d00e904214400e22502c401e40964441c2a40400090f0985500f26100383c0098030800041c1603034074102c1840c5a81000a400c04074069a055a6904c0541c1c0241c0d00040864482d26800c824502c9110100c10490b0001c0002d002d50810840040e040007078001144050003c049040345071000250b00c2100c1c4403500074001c0c004140d4078640315009003040415200c0da8918000054902c440010446007107950603510142c1069480c18040e080300c81b0350420546 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 301291492 1250 301290242 301290281
    0x90614130218060a090617091207030302281112030610050f0c0106030c08030f0a140d0504080d0f0513020d1511032203020c0909190606030b06120c0103 67
    0x1d02e5101e40001e080b003081940c80b8000381c9820140003416042c11002142001c1c0784100c10030081c0d0001083c0070218055907074406445101d10701e4240c001c2c1c017480d242c0001c69800d42080d9680d60381421035103111080c903030300d44609040c42c1c140d09079100c80710b000b8407848080e000c201191160a1104001080c0107051400e40d040001d00d240e5006554011802500c940e0b4580205000340700b068920300004001c444020761a04131900e00a054601883e03020400340300380c150050f14071038500c1d421920380b042c00140400040c540342c40c1804564002d0700380c9038622443c050240c8800d5102d44182c5018085092280c42c0d80f51440e800c000c0201c2e00a13008803410565420040301c00b03440e5001e101d10781440902000d032079140c005190b24803a00c003ca4608074920b00944500c001c2600030541c1d510076101501c681c03805a03983c0d4a014500758014000c1800715004a0024050240c5039009805480c410710031004c5580f120b10401190000c95800002e00d40c12451014019600940c80368846d007034030030b00504 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 301292742 1250 301291492 301291537
    0x4050615122815060f05190b0913050709090507090609120503120c0405041503080702090405011803020c030105011d2a03070e01090e130b04020612100906141302 71
    0x48400c2c9011040200180c80340000e00403480d80e1203451014090640c1c2d50030307a00d5601f590301d5070f1001d1940300365006440001000340c0141c0380c024807062400240390040c40301d03061210005100e04010b1003602101c43c500b501003050079100744808030803600720f076860055207810829a03036a06e142d006411112403101b00411444011603094a0b840340003080005901c1d54a0542400203448504c0705402102d0314a000500000381801c044e200090780507a050700d40d559451400c80d0051100520721004514424070182c01c255002900a0100340150300038456642c1e1800c141c2410f00e5000e49855444400d0030002d40305103c0024108800411941c00c0304042c1043c008245803548150b0305d550020340365101650103540c0054130000280101c400c002c2151800440042594030742d214003d1059a541c000714080d555000c00781d45c1070304c01224054040d4100303100d0328201441d081c0700e01040d0a0030150009090348460740d04401700c4a019000c07a04a4508030201e400a5000e060f405003020b04e4040030a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 301293992 1250 301292742 301292753
    0x70209090102130609141504090c1103030c180a0b07080309150412030c11070b0703030e1e07080601050d02040513210e03071503020a120203040506151228 68
    0x1070013140c0324014441e0800c1d048050b6403440300840350180c00708503000000b00004030200c80c00c9803114503000641d80c4c400c100c00c03503400d18070300c03641205440301100740000d8101c3c440003408122003150544400d906a44d0500c84983c40c24480d51100103c180314100108108400075540300081c0400d07550103e44e20403080340d0a610544041d910b85020844400e001501440f0700b10b0b07942050b00b800500800c030b40b030005964002c140200408000c0100d042820140030750000c03402109940180c03801c0300001e0001c03440e40d0003480300c440e24074803402038006103000303010a1030340c1a80c0b00607010400070549078080c00050700001e401100c20021001014022801e010301e075075403692842c0c1d1240e0768200d652000400000549030010310030780001b20104903500b040300c6003984010090902584030103c2c4442566100070499441d00c000340004104420410301041c0c05102d40740505e10868413072032000501011041d8000b201140e81d220310785003052a008408181840c01c0300300080b4050f01c41c1541c51 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 301295242 1250 301293992 301294027
    0x207140102030106090608180c010f020f07120309060c050c010c080c1506040b04230703151203021005040b04170418060e07020606010801030611190206101703070209090102 76
    0xc0b00015a40401840f4090b03000e90704907044020116404848c6015000d42601d400071712a42e1414001c9001070544058024801180d00f0101c00c8180c4911540d6949031085001100c00200c1c00130325010000b04460b40a1180318001582103802000d414075402c0040d241c0f0080304a056034800010f2012101c50101084114038071524800e2181f0f07075041c1320090105441d4090b21482c400c5042c004402e8071310b078502141c0303050302445080e800403d44441c00c003900280075024000215462422021a00070041544820418829421100c040569800e80801c8070001e0324010034440c501004500466040340050a0403809a18514540340c1d0750000744009006c02c80ba0086100c0c0c071448100019078440d00790b194040316500181440b40782560000704503003130500000344070b80e0b5954100c4d11460044400c0d140c2e11007450301c0c18038441202e250060360b140b404590314a501400008041800040b41048441044c402c03402541424695405c00040c40e100400c0710a0a6500744040840105243c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 301296492 1250 301295242 301295249
    0x22a01180f021f020c041104030b041212050606070809040e010606120e030301050904200d0c18091509081608040609150f0f1e0305060a050301090b0a02071401020301 73
    0x795500003000c0c03050140e1440c3d00407040c1c0300800c24404900c0e40d02c0c1c010a0540d64844122000103250303c1440800f00d040c0030b03030381014151800d1581040200070b0641d51041c0b0340042d07511448640a803c0ca031000c00d8850880e9115041a414801c010010b141d10010f0b01208400400c0071400d80b880750021400c40700180c0c8101c0000300000c80340021485d0a11691411015a0000c2c514641c18940814091a000ba0009203810100e44403543c44603440b52540810354402805a56411114100b11007007410900070f220140c00c00c20303003403600303100d003440384503207013a4011001410955086c4e10b80d402080c410000307544c02401007000e00b00005c1041d080d0310889100e8680152502d061540040030410f0b1500080600240e43c4520320a140d008543d07060340196030710f000494410200011214400003643e0345005101e1840c058a007036805410240c442c40c429a020000385a0b40c0d820542070751129003001e0511031b0900e0100d81041044d030024075140c0e0080c00076900b208040d6103070500320b0340240e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 301297742 1250 301296492 301296503
    0xf050a120302090a080a260f0f18041505060c010608030c0f1513020f0406030b04050c01020607140301180e030415090b120a1e09061d01022a0118 64
    0x141c0c000f00b07031502c0c0c013407000039000b410b0040010060968034081040d2480070f148030300c1c140d924020940c0c07188901c119101540c240200030b0325552041703840038072600120b0316003c0c01c205101c400840c03810144a24a18081e5010040d10454a00404d0012a6100e0358158842d9501c6450100c5c04100400c01030000106010003400c44489105505080209250b0f44007047c1401d5014030181c0e090700c2010b0980e194045885010f12031100c0e000500400440d80010400c01d0b032001080240100400d01410100c2d081e025640155207200045803040d5400742640401070341400140f00f209070001500311001c045440000314a4407d03008207186800c20340c00303040c2c031061080c510300c0c03042e40c000d10090007029540d92650410b41349a20316040f00000400b203400d425034455900c4c110311402a540d01e80300420036000c0240071440e040140241140b8204800300000410003041c000364140300300c59007007007100c440d4050301e0050301d041320b1040800c0100030055900c801c00c8d80c0c3d980401c0142040e0151042 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 301298992 1250 301297742 301297747
    0x1202010e0a0b0906090c13020d0f06090b030601050102011b080a0b06030123060712030b0d0803011403070b1303030c0f0507060306051002010c0504150c0b04030905120c0d0f050a120302 81
    0x1c000d86240180081401d45c40f0b4000041c0098961504480c2d031490711070f182405a150f4600c0c0341e00c0340091102c0811004904d0400600182000e0658440482c0c101c05800340e85a030307a241d1006900b62541d4001c5c10607807400700c1004060951045200e550082900784001c04c9611458002406070341080e00048628018881d00004848040c2c0c80c82501050549206040140648034540da002e818600042456103d5450424030fa50382c282059400b5446056103480b56160700c8200303580845030320a035029111b800c401140d042d4080b4140c8403a80c00e440c502000950855400b100c510603c3d160403101004100d0307a2100280f400e02a09020f860035030350010b0101d14000410408200b00502ca2095915010088400c45e40c40011034041e030703c417041141c842c051009011100c0e500d5072a0054001d001e40c2d03007403000f05503105600780102e03841200c4641c001c00d21a090503807540105c0c6003640d8002561048480007400262407410150b0051081d20301040071134854103d1005580c800e0030010307600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 301300242 1250 301298992 301299001
    0x70e010207060306050906041a03011505010e03010218120703150506100f0c1101020a15090516080a060c030f020307020105010608010602030705030d0b0616030f08010902090d1202010e0a0b 83
    0x10003119000303080b94078040c4801031405012aa08600c0944014011600c492090080304113001e000d00036120060020404440e00c00c030300f4002d20040c1d0051900040104500044502e8140250b5000302c40a03050242204a0241009960881c00d1000c05c9a4020720300000f002c0b80180740c2110101c2c400110200f00c91504e48108225071151525100600c8030300c1811440d42a4066102c0c905a81c1c0202c840d0741d4503488a0050b0316002d001e10000b07011110006252000c40800d8005114492082040f1040d4400c180d05140009406004152140c1d120015400200e180e0350009004400c1d40e04000400642d07a4124400342c1e401182d00001603034403080100690303640700718898010480780c40550b09003140c6640c2c0545a1251500390ac000c1034550300405113580e1b9150842e078208070f408126114200840c9000340c0450303000b0103d0720106220324000202c0c11042d00071101d004400030511118128242d44100c2c81c6007104500c54219035a40d902516520130030007000400741c1c020030010b2240d190 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 301301492 1250 301300242 301300247
    0x10f0306050c0f0720150c010b0102030910050a2a0203060703050c04170c04090302060f060a0609031506030212101104080d0804051c030c02010f092406080105070e01 73
    0x50a070785107a001c100b100c007105110003425075540540c041d540110500800081d030a20700d64005d8200da00c00c030a104008040c45039007005003010254040240451070b801d10044e82c0b28040c8400c695044103018140c045841e11078030007081c200400d4141041c00c00303111602010b200d007001c100c001c40020007030b843c0c0e000d5103010040c3e2980945103203018025032520208101d4603004a101e17502d014010030300c078000c07030200c20b1044503104a8064000c101c01403150038020350311203040d54040104034011000c103e55003000120281034901c00c0d141d154140d0f00c1d5513100c00c0c0c5400e8a11000d000c1c20303501e00c0041700603a281c20750118400e0340c5074010000f980825001e801107903a0081035401c520b00c100010004440d0200e40b580701004c01d802c00140a641d182061410269851200c82c6030100c0c2800314100250180d010b00107161003135008020307164034800340801311080d070000541448c0a03806a105140403111303101071405e65150012a00d1940d49041c02c0c01d4900c19103031f5402090044807608070559 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 301302742 1250 301301492 301301501
    0x8060a020a230f0c0a051b090106020c01230d0f20032a12040b0f061207170111070503040e1b091302071b08070f081b0117010f0306 58
    0x851484403152450440a89002c0a2240c28100028400041408580c41c00103000407480b0a402c00c00752000c1c2013113101d100088008850106104000250000c510648005103503400550180c4905070044154540855030424080310186078030002c211034024410035018020400c0c49120001c508a004403910f2403400c41c07030f00c0b1142d030300240030700c2000240c2c0911542c055820110541445090040364030a8a040c4113120b0185444010101030004124a0356956841000b005400701959201e06003080301d00394030b1007103000c00c90f40104801e01c240d00a107900030100000050000481d014a5015201c4a402c2401c1c01d4038540c1010404011122103108030300da00c01810702014503070403240075001050f4040c01c55018094a02c03c10910307015901c40e070450350019000100705c882459803128100c225440d60282407803501039a0000240031014520050664039001c01030090800750a0404840600d800740351410004070394800d212140340780909038003814802071500388083c01d504140342501c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 301303992 1250 301302742 301302767
    0x30a031101062702030a020403020a030b01080114040203030a030e1c020303060f0307050d2607111f14070c091104080712020a06031d1c030524090c0408060a020a 71
    0x7103040f210f01c0d1405084101070b9010b080c0b00724010b8507510b4900c035200080c05950402508005840000301c1400300d5403403854100ca4009000740106144620743c0203a01d4015100250146c0c0240310101c5064001e400c0090000092811a85400206941200780300440d80380300c00540c100109210441c100500700103c01ca0f0194000e0404500d40408551240b20900d000f4082c403411801c0c00035400811324074103442681c4000b500b502c0d0207150400c110032900011480e482051403015901c00850540039114110b4007980341d01340c0c41c00c5069002640e903407054004581d42a80c3e424040344203881403044500b009400c9924070388441c1400d0f4500d1900c5082c0c1c0004680b103004a0005006940d000e4551003502e0482c030740030607240045d81c441000040d960410010900030300d5410b4461181c05c00200900003416503080c85962500e03452051f05618402d0480800f03282a0300592650510014545d004240c4d02859482c0c80e0303031050064284a001d036549114542c000941a0000d603201a0781b19a5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 301305242 1250 301303992 301304009
    0x21507051603030203040e1312031406090105130209030a020a0602060405061003080301090c110105010605091905060a0e031e100614090103060b04021201171c020a0b15030a03110106 80
    0x880c2503440103566809140700d0208803450500000b048c0b41c4105580024460f405180400300c0b414110015000e031a0311621701c00300f02c40d0140011560314103100382e181220030240810b58204201c14108000c1e501011540e82c0600c030b10424000161641300c1504014070395a8098180350405142280c10302402a0145c15040c021040500c0800c100700220b84c1110362040c00024240d00d030000c15207862242c0d0115240c0c6510740400041e5168111006112a900880d440b03003030058400030b07845292006006868101c10248003a06070280540750101c0c90081c01821a0a401c11504c41566122108500c1040130780000025410400c810300680001d03024410340100c00c4004d071008501c20b0041480007802c03558449010300110745a684c1200c40401d28080744912544c0c6825000d6120080800560018419500140e00e542d40350b044141d1981d09640c01343c84a0b800b80c0e12026408200580303001403c443c8007190300160344d410410003c0480c0300c0c0e250200b41155101c5c036582160820f5118429 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 301306492 1250 301305242 301305283
    0x1a15090909070f0e042a03020907020d0905040c171503030d0c03050c210406020c0d110d02060c040605030405010b0a090509060708090c2b030c0b01080703030509120a02150705 77
    0x14040211040c82d4417040765090303500c0c800b82d1b032015a1554940e1019412000701800c1c0b01c00c895010074490401140e544940c0841030b1f130ba0084c48115503034080900000b80001d08070700f03416160201d10a8000c01c0585428102c0801c0d640000d0546d807060300c0842010b940c441c5c000d165030340c141c090303503500c10305074180d4500301118028441c142030100700b035000000035142c0016040024039410303619124140012070340209045400a080910b11018510203480b03412510141e103480040e050b0710940d0003e18150820b407805100380e9043d080644100e07038554980c7d00c01c1807103440da0a8a01c008048015003c58141061624582172840c09050001007116200800c101420001361000300e00405552005c030300480840e840ea823541a130b4100404d04403107414036505160b80b100c08003130342078010540340070f280c0d07138688480f590b40c083c1c0e00c80100415400d0101232480c0c5003034108003001410740019200006140e6002500c0f0107a000c0200c188454040b50745c00c1800010060001d003003104031200034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 301307742 1250 301306492 301306501
    0x15030f0908070b130c12152d0b0904111f0206011505120403080610110a020103020903010216261c02070f0512030a0b01031a15090909070f0e 62
    0x2524812140c02800c43d600d1034012131040703041003030181c1056400011318076040303450b12203118141152450a603a42242284602c40951191083c0b42c00c510166081455007001c80400303c100c1112010042c0f801a62094816095183d60f05600c1c411031044070005141441181040b0034400e0800c901081e8000c074030041ca59150300015854155a6001720341040e4110845040301d141c410302d0b0000d00c10074142401d0104140e04221002e0043c407040710303862120071004404444200d002080c1404030791006400501650095004004480e409400549881608010307490301d51614841120074104e411110302030785500101646840140c3d41d2402d213070894402c3d001d11221035101c2640282503000400001f0072802c20030b0b14540642c0701c2c00b6500e88020110102e19541c00460704200c080b0704110000b030341036209205002400858541401310382c0c8440c01031100f01481ca18060b841071a0030050040255075040241c0d104074005002405e01609000c01c80951500c1c1d6807108002030141014003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 301308992 1250 301307742 301307753
    0x40f0902090105040f0e030408010903030c110706080414150103060b01021209121f15050f28081b0a050102012702011412060306060603100603020d09050715030f09 72
    0x50450300100c0300401c1740c6004003962002080000a00e103180d00c130010340059540b4042d080710001500070784003004800f861a10036070352103c01904030350b2190009030003805154000c0c0340840c0c10030701800c094890b6071241c1c05c0b001d00e0310203034800d0700042c40d00840c010801c2041ea406085109a402c2c0b0240c0355201c01040d0300c2c1064064449440e00c12031303601001c50a101010010721290b00401c008240b140014180341c00001c5c500105146001c51405ca0007181c5410001d11816690030040e10034106442a846400c50609100d0b00003070541445000003e401c0c01d0410204224040d0200550302e210741d4401004184226070380402e0541e410301290040541011318207018101d844407440e0340c1c1c400141700495150070034500071506d408000ca45500040038445440d4410481039046403695210101004424001100d441c8185800d0070303014070010344660041c1101e42c80e91400800d40e14204d41d03a4605201c6190000340404001941d400c1c0459450300612a0041c0c0700c0808000051154485 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 301310242 1250 301308992 301309009
    0xa020c15060d0210080f060303040e0c0c0703021216140a0b070501060b0d0905010c21020d06120b07200316150603080301080d18170a0606030c05040f0902 68
    0x28400c480240c0c00050003030320b44510341c0308100da005141c52006401a01c000d00500c20542c1c503a8100725050700064128100041100c080d030750143d000c2110345c1c0d0b0700b0a0a208690011a488405010f882000001601c4805035500b0640414000e4040c1c158105c1c43e00c1c140746c455500194119240190080880d02e54410020a0f00d00c09803845a64042d581022401341135a584aa0785444000a1010300d0300340b25807007070311820f1040e070007400b024081d08400c40b89418007461b1803c090a080224660410040e4002c1c401c2451052000c9425981d5021440541902c01010350b04940c5d200200140c2550260414246010001601da00340300c0c0d0b0a1810350741d00a842e250f4945c1900d5010600600012407290410911a50003d108203600e034034054016800030312540c1c03428402c000070001c60b10b0103102c0005d5040795001c180000c1c0f92400740460300f403000b40c2c82410843d000d60300c1d0319008a03a03140145070145009190b01b003c0030340b4103424003007200c1600c52804d0b103540c9004807840060340d51012 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 301311492 1250 301310242 301310263
    0x41401030c03020f01050f1306030c02010c090608060f06030c0c06130305040308030730060801111207170c070c0e13060b0102010e03040f15110d0318060c170a020c 72
    0x210343c404c00800c400142d40d02c0c46003003000c411a2002040344080d561925894070181c1d985c0c3d580c1444a4035a01000f41d0a844c502600c070340210700030841c14410310744a003642d1980b00000401c079141d841001d0002c601e10750301c19164003100c403400160030000b0080c100009038010b050200c481090440c5514002e0941c012400028120b050000201d4103c80c8102c460b149406041c400356900c04040c0040030311810403204c520307060142425000503040d941885160700d5408054142440c02e01c280c05c80b50106103008064400313004040f89040102540460318504c00c80d4590700b82d965800d0507082c12440c0020030340c80030200c6801c04081140c1d603840d5919130740c4803542c0314501080034247c00c00180c0c09130202c4082c1261900c80428005800228400350308222040111182c0c2c091003507030003c4440d107488000e0100c00d540210ba44c4031415119510140d000b507481003a50283d4130f1075503203020503505443c0740b030310008492407005004851500d080c60742040d001c0303204600c3c01e0307240605192180400ca9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 301312742 1250 301311492 301311499
    0x1d0709050703151205011b0f030b030106080a080d060b04030825053004080304050d05030d020706060825050f030703050a0614090a020105041a120411041401030c0302 73
    0x4001c210030074003942101c407400c61404000d055940c0c0321481d0022807524500d003500c0c2903080c00c4a444901c9103040411080107036507a5117a98001c01d03031009501030208114900d07051341d43d84c00c3c00214004241302d014110b62044a12035038038110164034100341c3e805600700400d070707002c1044204001015501280c0103007929a10040c4440010407018000030703c140009400d500525412120190403521401180903442220001c000b40e05e82c0c1544150049015074540765004110030300081c54980d155291640c40740d0308692401d0071040b00c1109a07000704104451541d00e914003440864018802403141100115104115108100016480c894507105840c051910b0340c0351219162014003842014640060890b080c0700700c40d280c410021f004460a4190b004a03050102d4081480882c4149496030160359403802e260070141201c0a50403040441c000d04071040011548905459178203502c83c038095880e10381e480d25043d0520094545002411070556100001800000d080d1278203402a2034054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 301313992 1250 301312742 301312751
    0x12030209010c0609051609020a0f0e180405071e03021002012d09081801020d050406090e1005100305060901170a0816020303130303120203091f021603080a1d0709 71
    0xb8100a07040c01b007034140600e450b05101c82c000c00c9115540e0014455165240d9680066400c03c840407103680c10b2481160b41e1011240e100310140b000e03040303442d40d045800340c020b50700804c0da83d002980100d881c001300603550600e80b15041055140030144140e503410a03000034441c040d00c1c030f9078203c505040013a02900b0341248000240203c66140c2c450341ca00fa520650304c41e0754100610341e2148420003c00c8080c0180701d0070500b02c0c6403610440c141da0480b512a20b4150303c46081640180303000300c00904a442032403400c000040d155542400510b400c5070191000601810007800b4420028416040010000c400710424107044a00143d1042e103940c00c140b28544800325000400e052403030124020b50f040c0b01c040340d8046d41d8003030b98442004891180d200c4000c00840c85040704184e0004803404c5050340c00115804503607564500e004210b041802000500d0840f4000c01c00c91100302c4102c1c15000507800604103c42c5002903c00c0c81464010f404c030170a070b140c60f40c50008be07507540300b809000c030300a80700c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 301315242 1250 301313992 301314011
    0x170a1a090a170c070b040807060e03120a031509020c0607050f040605070c12050312010806040209012306030c090f040605030c060708070c0312030f05010e1b0f040b0712030209010c06 80
    0x1c0c000c2e11140301d043c03030649810a0f9128202d0060b41c0250203500c07907a020b00c80c40014001d0040901ca0701004001d009040507002010b0760407030b01d800c022300a41c2070546075020384a041c00381c2c107425400b900d40500d006841d101406c00244c0b0b4000000c2206083c0715080280b8565184000160303002c0704d0007403400a54603500c2d4a0900301e001c2d415400713000c442c1605111441000300100160010344c080c0b07aa88941aa0307621100c9035200406c1d40c2c00f94001900a0041c0640d072105031280c03032030207076420351030072100701030804103e042d0310450303480300d09610208856180d49071500c03176000303c0241100e044c440d50742004d0000e5180d80c1341860b41032140304002440c104108040094601d0142c00c80391510074a513a0342040c0229000303469240f40028178080e81ea0200c0c0740036100d914141d84404800c003a0b0303950f40c25000903000000c030034944032507003080c843d983c052280300c001400039102d000794403070b02c0e001545031482c042100107822805060051190030400e0343c0c0b04851079103040c0c01490100e04140c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 301316492 1250 301315242 301315283
    0x1021f0207020d2a050a1e0e040c08060c0406080a0f02070f03050903150f0f06010908101e0e0c01050f0d1505100903030219020a03020603040f023f0304170a1a090a 72
    0x803a5403023584619002e9041100780891700d8240001c840303542050b110a81c1d18240000314610540c0a9240845c2442011901811095004402c00c80c4246401807034142a174a5203540b070700c0403d0382200082c03400a092001800d0030300000c0181b1010203566411800e1442d16201442002804c0449042e420800500315038440d6441e00300410031201035600c1d00640d50243c0c005841d405078030b810701c1c0360300341510706410089100d0b00c940c2c18000009001182c02c030000440d03241d0300044000150540600244146404520451851388107500140c481c8924004c14400d510740a805500c041c094101010400320360081402c2c2000380503983d100044d003005100103504252207800c082d4208002104210800c41400c0d114034140380210b0f90b0864254a030803142080e9880c0c416600a105161210808402a100d0491140c6005201a6424a903c030901b5a4a522801c00120890342c06210340500317000d04803480c241c481c00c0c900d003e00d410b0b02e007202c445582c1c0e080e01400100305440480d4801102078 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 301317742 1250 301316492 301316549
    0x803070206030406050702010618091b050d06090312140a050108280302190302030d0b030c030a03120b0616110907090e07020a0507121a040201021f0207020d2a050a 72
    0xc46040c0480074071a240060000804114504440340700ccc010084100001c40c203e050402c41e50020300300b800014090b5500070180c01403040c21424030010003066a25904c00340266406512000c0281e5041d1404440500594506070301c0450f054001d5601c034452008452260301c2107000111400184200c0c40c507040345441c0d00c014040141301d00003100701c4101540030008103651410028203000c481c051b0b8041584480d80c001c403c50b815400000d0b804002070080e000c07054500d4016200040820f0b40700080b03500d560182d028500c44500700803200e410862b6500b40b00284c40d9042d9410743c02442c01e003202a107186240d000706c1c21600d042c5000070700f040703100308074488a090f849410754480300c3e83c3d00c60380c055071914000c04691000c1035501c200b1203294043d09041c1f046405900070700246412000004020828005d150344550302000640c0140c1c80d07204149002521440200a0003111528a02025a208000e03600080d403a010100042d556849101003a54002c45949581080c00d18900c072100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 301318992 1250 301317742 301317749
    0xb070c05031201030506061504060e04090c060513060302190e060d061502070b070506150d12020c040501051e0f01050c0601080303070f050406080c070807051b030708030702060304060507020106 85
    0x1d1000041160380d10009418241c100c038421001c840d9180c5a103c06c01c50548811300003880c145805001c1001070910443d0440490700c000b41c0000f4038016079031181004038109801c840d021400000d0b56043c5040b200b4052030040c84549002c6003031000c1d080001151800400100e01002202c4030300318070581d104000c0780e01c001c450807020030640e40e440d082400b82c2ea4010301080050301400da400a1072204040846032100d42c80300142a0300d03230341c0001c950715145d28006401d0b0400354102d10b03900080c481d9240d229240b44203800a00c50114500200800c1c1c3c0c0050700701d03d0140607484440d00c0760038010364040c089071101311000701001c048180100c945000d9103084151501c0740d5000020140c1c5c003c001907005203410781d1907041c80010407205813000c1c0700303512541c40000c035080d00054824081c00d01400c0e02501ca6500340c0c1c68040c0342c1c1c644038170700755602160211500c0e015000d030403036240401942e0020a100c2c0d02450409001c1e0300051003c2c000100050f040c20f0301c2d9030000700b4051003036000c007014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 301320242 1250 301318992 301319003
    0x3020d051501030509030703020307120912050c041802030619110a03140c040f0317040306060b0c10050705090618030607050c0d021629030702010e06011e030b070c 72
    0x640750682268014240d2812600e01182c40c0c4408180409800b008503100355425400441c0342c942c2c0c9545103200e40c4910043e01c010820a91808940002200c5000f4442c5000e0401030081f160b040003040200c591410400310308452890111006803004104a68001d104c1294662147d11940002d400f501703498810f0001510006100c080e902d4059220344039600b850074860607181da0720b540b800702da48198099a0412203045c1c00401c0010324070170039101280d5003100100c0c10150b481d980d50003070b0340c102e411180780d282021a5080480404109503941c004a00c5c00c20701c5581001c4074090500d11803440e03003a00581d0002002411003220030b42e090008240901224118944076070010b15030b030421580d4042c04d000e8002c440607401d200107120754148600c0a020b1000320b1400b254655415001c1c0f0724000e49400702016448120550f0b00594860744980e0004107001b5000c80d0b150b410a48140c214485180f481e02c060504c02c00c19418400035a603105034031130495244c22100b42e032a500408001042c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 301321492 1250 301320242 301320251
    0xa020918070b13030c0e0408120a0216210207061d010201020405060c150a020403021e030109050d02070626010506090a030b0403230a020a08030a09050613030807050a170703020d 78
    0x10748a841d041e160013200d000f5005028025191031011806c100d0079100549030302c0d000d0061015182c03a201e00560800c420500040c0340c0650254003001c02e485410041d100d07800c00d1540c001c2046607807140ba40c80c01c500c901c0940425401c20201805081d100310b01d20743c2d41d08038020301c411181d000f541140c010303080040071692100790748200d103035460800d03030512103030082d07001c0101761a60700ba0300945060b03980c0100080c0c40c55000c3c1034582d401e80446080c169042d0740314400000400d500344040c00805040b98041d00a071410484007600851504407080000023510110340d40902513104000c0c1503501c2110032a0744e45843c0800640c0b101c6090b0805440d0700903d80c1401f0400d600030f0001c1007000c0d4184a103001e66074445820b640c00d8040c01080d6000360f04030082050000e041440203603480600500300281103280c607222646007400442d84441183d940040d403000f4150000b9a056018a60b0304d48a8901000c0d04c01c028005c250300751100500160990100c0c28550094050340c4081030945420003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 301322742 1250 301321492 301321507
    0xa0b03031c0b01031b08071206150f020f07080601050f0d0803181005060d11040e010609050604060906081207170c0318091b090d020907080a0e0a020918070b 69
    0x1c01080400703880c601183c074045d240b0314180c1d500305020b0000d4540340c5a150307240d55a80b03001da8080074018a0105400ea40e03805c0030880f03198585001a90700f2482d611840087c00b00310300a0301d00904900074802c0c5502c2044100f09008000034201d06403501507641c0c80c4650200d07404a6444040310380004e0000f20044104061001d280400c117000310540d070304039041000581c2804044544c01e65060303400070011004040802c5289105142400014000050031940040700600315049508070b11003150f00e40d4180201e51415003d81406400c03c10300400c8558034101d40c0340c1d0b170303180c9004040150ba44041425014000c0c6203464854410b146504955a031800c4611a07071603a0100d001c0e039815200901d80380384075052603003800f881815001c0c20602c500016071100e8496401c1003440d507a000c104642c05030010703180e031610207005010795181e80c1032908100e40d8000c1174071000070305200150710406042000d6602d0b00d6480d40c001a40b4994501c0b100c2c0c0400d460340c145500c640103406180380018120 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 301323992 1250 301322742 301322797
    0xb070f08162d0b060f030f0102041202040f0c0507031d0a06090509150306010b28050403050613030e010507060b0d0308090706080412030b010903210807170a0b0303 72
    0x100124800120302100707001e220801542c1c07404a10151504200000250349814403039080308040c14000c2c101c40c11046500e50b91070a992043d04100c0d001206030901c48118245400b030100d4829940c4001e1003035030481c08004141c0d0040d40400390030000c008c00c0000000110072580d00400d0b6020782142c2c4c0054581c04050511302c41c0d885404d000b00420b00006a911070300c8403001c420b5140042c0541101d91070300729241501e41001c1000b2088003126001e00111171420080e0a102e00455211192103c2c5182802d07070400390000e02450344802c81d03010b5000060b070b121911441000090900380d464000600703140d0010001410820781007074020000105040e0485501c500c1040d2800440d81d0940e151a030482e440c84081c3c0340140314140000303501d08100e000350082441c000042c5085000b860f540e0b00e0f02c5030340496040c09101421444156440403a030702c1042943d111000c1d0070244880c1d403498440401c2200014001045107542e00409501ca64007401140c440441740528541c0d0320b6402d1800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 301325242 1250 301323992 301324013
    0xc0901050c1519050610120e011a150a02030f030406060306050f150d03020705060d11040b0d0b0906010c0b0402010e030d030615080c04090f0908040b0a02060606040b070f0816 77
    0x6290800e01e050300a0158059903004d01d903c10303d00684900034803042c80034181d841c0c0341007081a07508951108404110794909100d40c2c90510303c88400d04001107a000c06005041d0b00c5440280c203c08810001c01d004507800008440303104000c00301c126500d64136410318900030041d9810080401d4241810301504c1c00c28001514041c125001e00e00408500030420801d4602c0c144400a000d0b800130130041044e0315156026011190f541040860303080b540d002030301901d07403290308001e918500c0030a0110940341140f0072541c3c078807029039100310382e42800d600280400d64503034801050703001c0b00f000040440e481802c040311001009003c49050101c080c1010780540498040e00101460501d14510028810442c45004e090f4691000b483c1030305004002025040200140002d00c0e1940d441b030000035440c070b0050001789181c15001e030301ca003503103040203083c00b10181509202d000c05000900040d00d5800031a10780b1540800c1c00310600420741341641d000c0c001e01c01d04100a261600040051000e40c030340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 301326492 1250 301325242 301325251
    0x190602071b180e010f110a0f050f070212010f0f0911030703110904030221071b05102102031501020d02010e0303060f010e040606021617060c0901050c15 67
    0x1d120a0248100070442025491445440d2245980006075800000e0740d50101000c00c0b0407030000701e000d603c041901c2c4280d400c1d10555200610000a15505290707103c1c0707145e0803200c2680b4016280009841d000302c250300031a40003900c20110440034220203002584210885044600c0c20700c44240704a00304402851901010340d100d40e4040c0340c0326a913190221b02402074950040080d403045601405100c000a0020030481c207600c2100c8030b5031025074660348034003440270070000c1413941d503081850800202c0c842820542030084884100340300c0c81d030300c1d03407500240d05c01c0c549400e90280c1c01b185800410700007842d50400d941480002404182c0c00b0180701c411071f4400c203030211509000381034012422a01060000d580d980c1003407000c6192841e005d111346a1540c4145000c0c80e05884401c00a0300f200e456604c0580541d000301d00b0300d03c0c00c14000d90090000c169528405030a0b56000705c43d40d4035908010b1900b449881c00090790000c81c2c1c041c80070344400e65806400c4416030b149030144210012011384 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 301327742 1250 301326492 301326503
    0x1c06060609060212040e040f0206161b091509020c0309090c04080c031b04020319020a02250612020c031e070b0123090603031903150506071a0919060207 67
    0x2c491481c41511310b0840d422500f2040e0514070300c0d46ca948803046890085d0a08980c003000400000c1c00d0612051405241035002e0080c0080320820300750300000141455010305495801c00c4261580003286464034811a02e100354050b07500c1100051041c00c500c40c015006034805000d10602010b11012005007054540c6501100c40c94443c0c00101960780001c40384c3c0c00d5800c0d85c48012089135041980107960004202410a00d0a100110384641640c008017044801680041006601c1100e1040c048407918a112300074143c150030480c00406030000d06608085283d000101c6102080007001240c41007000500b03610304ea1049122010426803040009849801002d0000700d03c50308d20a20b480c21300c44007a25041e500e00460740c284042180001c2006038180028005070404c2821030f1a9600100f015607400240d00342d5050010908810300e4221a00904040c04000001240e4607641c07002c48a04412000711079441c07003041490140c4a04a0ba2428101512101e0801034035401509100c0c1c40b91 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 301328992 1250 301327742 301327753
    0xa090c0c0611040b0301030816080403080d11091005031509070503150103060501171302090a0b040609050903071e21030b041505130905030a050301150206040209061c060606090602 79
    0x5007841d1501d004030b0041390003c080400c01080060441001080000b600f1100b0b56004032051300c0c2c14010ba0403542c0700350f03108400040d00c5404980341e44250011104101032940c1401c01010201d0800c9101071140740512200101080d0b07030740c180120b003e10701d04c0000e0540b00946000e43c1c0041083d0020384074929550101c5840d00078541c0607006090903143e040e56001ca090f00507828402c1040b001801143c41482150a0703403015840398039440d41f1802841c1004a85040e14a042c8801c990366070f030000c4202d91400d4140203006501004490f0680d40014511041200f03503c0120640a000130000b003c054040b006200462800030801a206100e5101082100b499000340025034222100301d1150704190178041c003a515202407140780b400001500090303503069a03900c040c9564004504031000c11004401000303051080f036580c10f0030741ca651020388210305080e80072504204000e0003140c41010f84002004010044048803801799812210601c0001c3c0d481c400034000901d1801024014004c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 301330242 1250 301328992 301329011
    0x110708010507080a050c160501061503020f040306091a0f04060501080316060f1e050f1b0702010302070f02091005100504031e020a0305030a0206100f230a090c0c06 72
    0x41c45594450400740e01d40d04420b5541c80344400080000400a161041050104a001c010780d6070043c0000341c4108000502c150a20b9082c0c61003424094003034040600420000c2041b1052800b030368112a841400801c0da010035280104070100505600203a000d0000300708210241500f0760a0700440c080c030380800080e6299407810741c60380f00b054007840103062182c00020000301c00794014105891140000601400f0b0380c003400d04131032190701140290544039814045e0034000014515000030355110b50301c4115031405601449030150305406418180c0c085000c0b03051080100d4840380f080d0380107200200c1e614204041d9401d99105000d00c07405004e10880d8204400c1c020300c21501580c4d00300d0203000c1c03059001094030500840b0810100e8004403110030010000d07408102a001041c4a600682024900b03203114410260803a0302002c650114044201b05500035007a0f40c150110b180018030b03101c0a040c1010800b107400783d40c02011018540911150015841a01c4242140c4980010301c0350084 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 301331492 1250 301330242 301330259
    0x204110c0a020d05010b030d020102070b061f0c020105210f07032c0304080303160206060402040b040e0a060f0b0c150403202103180d200c03030a1107 66
    0x10a1508040e9911800000780980f0300561441c919510030701c00810179205010120381843c81d070300b80c000d0243c1e401141590400061050195108500380d400110101040f4021148010303402820b6040c411600300302003d44e4441d9088130a0b0400d1002e4400a2100a403030701c0e140c2e07c60854444020900301c001044202d4401c0c06104841007030185400c055846000da00c40800301c0340018101c184c4000c101c00118040240081c40c802c9000d40c10140c100c00a1500190602c00010045e038862841007100b8003100300c0b10303810756041d1004001000f9113943e0702e0100c48010103d582010b40385460049001070045a0306000303081001d4260b0940d203c260002c0023034284644280c4000300420348180700c01700b281401e001d28801d030b05021412141d03129464000d200703030329940c403820014000700002000704441b124100b103e2416400d50043c1655444080014203001450501d101c00504020040818620801c403c8000580003015243e49a50307590029109164107083e249090040b410000f58400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 301332742 1250 301331492 301331497
    0x2060103030e060a030608060c0c071703070b06040902181b0306030c0108040f06050108070303110a0b061002030906041805091b01030216050d0f110f071e030213020304020411 77
    0x2549602d070700308201545401c0062503081403442504060740c488001034040c908015460051445407200f07a500d4041307001c07190030107489400507449008070810105851900000300c610721174000c804040315803a060005406030844403006584101071542461418140c030801c0360040e0451070100003650107600c7c030600c1500044a03450b5140e003040d02113084950048541c07550040c8180c400304c50040d055a20141103070801e030030042541c4d01a080610816030045525189221044000e240c0c100c116601d0f03048450000b44441d0040c0645416880510b008209641e88440c00034401038460b502c0d25a011360b0840c088001d52070650070500820720304d031000701c6ca040007a50b0450303c440c0002c10560055000e5445001000780c043c07241031900d0082042408048500d00241e62850000c41c0415001080090030402d80740090b0805911000080070000700e913030440300c220800340704001c3d0102454502440c2e03035101035004190740503820b00c04903c03a802548528070851313041280e04000c283c9100b860 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 301333992 1250 301332742 301332749
    0x9050d0f0e1005071e020a090b040b01080c030432060f13020d081305040614040e0313061803120c0c080d0e01110f01180b0a0504030903030c030e03060709090c020601 73
    0x440c200040404141449017400c01c6445114518071030010303550124210119961003c1041c03503455030841c0d1689020f02945000e000709103400c2002e81404c80708081c0e144406480103100c05a03030041c170501d005ea006008840c0454a034826504440c00e14512503c41c0c02c212107140100d0740800001c3e4842c002410558022900a0f180d00c1000e41540d8a1408540c00b64500a4000050910000c1e0a980381e003e08009080340d8482c1d1400c07980352006200665084045405031a0030902142c1d00e5040c0c2e20040c0401c0311514030701080e60408255024800d01d425401c050450142e101900c500540c002c1101500e5a00c81e1421541c03907541d400c01144c9490011240b0000101c50210b501c2c0a907110380c40081d00030003028150f1b818141100080f0f0b08481d04480e0804101900144d8002404100401150701012600c406d100500d4150390040800149020040521800003a0081403500c210104061950b0240440f2007070704006001522059551055850183c10071095160b281e01c0400d005048 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 301335242 1250 301333992 301333997
    0x708010c0c06060b121603290102060a050f0a1a040e010b010f03020a0203030a0c0509030d0221090a030206032e0302130b0d2301050c0904050f011d070309050d0f0e10 73
    0xd42c440b20301100404080065010030140c59881344504803941d1072081640d2454020000c030231b00811000a810200018850703d001c1d4500070420043e60018100c00e588040e19160000f06001495081d4a45083e52066960403501c1c204018050365815889512000c130b090326603e37044488490118164031076000400c005800c02e00c041518004207070041e809412082c1800744c104686500880e1506503550644030059000f0b000d404c1080107a030384001a40b20903d100c03940b0b030000e0580411074a0002c1c1c400240102d030b001001420807585008283e001c050006961444c0828040d140d580c240003034082a07110300070001c1548c0039000903115000d10460301330001c6429200d55180c0b04075482c40440341d0080b0340d04101c07a04082d41d1080c480c00c0c3c8a0410603c4485e1540384d120203110840e84000c1c00302d600068107000501070020200c10340031401c0040c840040540d62014400c401a0007088001801c911941c62011589500700260b4440302c0596641c5851800011040003003107400c60346c05201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 301336492 1250 301335242 301335277
    0x90f0501020301240203090d0c030f0b010501120207170304020103060b03010e0603100e0615041b0203130506070c2102150702330c0705030601030510060506030f0c0702030708010c0c06060b 83
    0x402d820000303055400c0900034081d6050b9a564bc0d251284d03504425942162075040c04030061041d584c000c1c10001d01c143d07500c4011410144a03a035000c00f900b0181109064402001c40001d0440e032080e00b0072005802987c59480c0c89595440030340e56800819551180310340280d40280110224502c00d00c03951a403d80d00409883c0c540c00581c0074442c91110a075070b00241c58244003d944200d1803402e06026265500950f03591407080200400d58500e030300218840c403c20064000070940302d402000031340d16801d542e28031482071616036000d8521690340c000c0d0406006c249960b80d40210700c0141122070700039070711203024a078401d580c0240c2407000c0c9195a5099a4070f08004907101600000d000301c90100307021070307071200d882d8000280f51600076403003151558050084050188014045c00c001400141c0d1001c1c21820118030000c084800203154814290022a1340015075401300100802032480000800c42408605401403141c2141c04090310074a080c80c00c0000c10700c4055086450b078100c103003442c45 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 301337742 1250 301336492 301336507
    0x2030c01110316050a121b02101b270b0301030605060415060e1809061e0c090402180406090614010207050f0609010215010605031806090a02040f090f0501020301240203 74
    0x104d55420000c1440204400400304014819031407080140108004840220440d04400002c0c40c0850480d0300030415810090302b905607040008030b00104000d00d041056040a07041c009102c04000c1e042024562113035000c4c001540d0709440000d41c140c0780960000e1010345c0d516424802030307400401c1103600b40c282010b000c0002d40e03c5142580300d8005c0090540c80c8644503603038042c1c000d44058841e9002d0f0b42010003071081e40c400d01668007080c03074600d0a5101075441c0c108683c3c03880e801000045030080ea0002034010701c007420241c15070340c0c2c5900140304200030303a1903e202c04020305490190681903055142c03109415800050010220344000b0400c203404c154041c14003826400c804a01c505500c00e200f410845210000da0b4640640100e0380ea423600d9142400450f401242803611444080d00b1200601000f80404142001031300d4041c3d501007405217a0300f005100915480501030b011030140b5001703a04000c410340084d8100c460408599800f44000d10b10500f100711682200e10160307000f08402c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 301338992 1250 301337742 301337747
    0x4050711100b060f130e130b0105210d0305100501050f0304081602090103061406010f020d1d030a0c080c010e090a09031704060b120309030a150b1002030c01110316 72
    0xc075003582c0151903207061070380400241c4807130741052102ca0840200d080782071010150660390154403400114520705c4064880d214801c41250600480b0b000b00700801c40d8503210010920301006d045800b0040312401010100b00030020b05054820540d41314060000040f55031050b0305594800c41d50140c82841c50300c0c0c6a0b5400d41e594805480c003011002e0b00d4107800003583d80e00c40d1942c0254000d10010551a8000100e0070022000800d4541400500c806d090051a40018140512a0f884c10076422409042400ca9807280945107400d500d48551030aa10800a5084060701203070172800c1200c1d00c9102403030042d0f4254a1159025030070141200c00170b401c504880e008810464003a003032010b28804040b100c010f881c003040754140c0c3e646894401003e0030342400e030008100300c5014409141841e40c001e00180e250001d0401c0507009810003a0b0a10441c4596400b4480c0044001c2262414503860140a034490700141004641540303040425072500c103245044a10483c0814100c2c03540b080581005d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 301340242 1250 301338992 301339001
    0x111211b040506090321041d19021819090501140d0305070f0209040308220b24130914060106020309010c05010f09051006090e03120403050708180405071110 69
    0x109a0601ca1b9905000e44c0e8021001482c0e081e170b107170000c00340c2d0302c0d400e1550b400c0d02505109030744080d0300008010003865003108103908010b02001c81d00583da40243e046500c0c0c000340020000c640c17004110482c80d403819143d00c0c4040450b000124180107070381c3d031a1401020040328441701c0e50460070612400000034424002803124074490740480307a120501d5000310b00c0c0d0200c1200d045001ca41704c101849444e69804c400848041c220b440d003402a103031541d40720700d102c5074060507085c2010601c03001740d001d0070106408003265020140000001c41e41000e803000c0a040b920406407600820038642110003140841e80c14141c1c0c509400a503d02210b24004607500300e070380d0009035415503032104202020700040c01047c8943d03008000400c1d500140ca8144412200b503548661001c91a0100ea05040c032030100580f085003c1b401000d404a5a4030304042d5102e10a030350004107000d400041c11303000602281c000c07844a0340280c404200d10354801005079180041e030f0811010359840340d0406032a40d4010b800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 301341492 1250 301340242 301340257
    0xc090405120406050417030c0a0209130212010906060f060f0807051b010b0306061c081303050a050d03140601050328060902030103110a0b0403060e0111211b040506 72
    0x896620708001d5500800301d40141e0480000900b0000e804c010454090b030600103020402d40c05585400b24011149984120010b0020f000e1081500012048280b185025012a030080c28440050702c0d10310f0007a0091501c1901200c0503490024007041041c40c003504101601d460352503e02c41e11320041d5043d0307203040000303104404222040105a05c0c207100b00c682021420b94600002c600d85885808240c00c1c807030000c1005006a6090100c40c213540110804000050780000449aa40450b0100e00d20f40d40742e01d030070142941c810072809108010f80000e8214100719140c0d42000780c0103680d19503d00321a000c0d079080f40014000d102047c80b103034032145460806c480119540c080c04942c940d140c0d06076442ca5018040e09503003c0010000c0c8100e0b51030b2210211400c55034040c1d1780c1e06050700041d203401351b4000a000955a1141050715440075440308030103201d241640b0303442c1c00311104005071200c001d251806020302c1240109a001c51700000380c0702404010340480382000d00701428002660007107074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 301342742 1250 301341492 301341503
    0x130e031e04051e12031c0b0310060605070c1202010e0f180a020c010e01050c1207020c0d0809040c082e05060a0e010f0c080301052101050f060301140402030c0904 71
    0x7000142c00c3d507454240305110101803200c0c86481c0030320410031415a96800002c074207604200000310001e035031306a80710b101c0c42100000080e04180304011a10f402c950440f1424a5480c1c0140800c485411101a040c0705101c1c00545100c140c8601c264915600c88840082c003058800d0440c41d018a40380026000c0c41780080e2240940305070003000203003148401c2e601c04030766950001c1c685442c10020300a000214070034000910850a028921702c4070391244131180c800d000d004a0110300300380d2090001501680006154120304c00702818866916800070340140d219a01c2d0082e0700c42c50500a009081c403a8003014051018590311015059119500300b21007074500640b030030b021566a5034140603009580465075090f501001410014100c19014003007081131100c4104c5d8500021000c50460b410f40b00e0a4503118038101e080078121070008041c20040016500b40010048401001c080103442000304070000e0155811584640341030180c1660042e4054001c88440c21180c01d000003110380152054 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 301343992 1250 301342742 301342747
    0x260102071a0a0f2a020c03060c03040305190306051c0c031e021905090907030f120e120c040f0b0916051908270d080702010b040212010302130e031e 65
    0x15241e0080b03a0f4013201c150342c80c1c40c1684803046500d00c0700a551a06102c035000400701c14165100080d074030700008108070200340e0000001000c040c4600b082e1211800750b0315035441d110703403000d01c058094071180c000d150180c2d03034111941a055905001d07603440c1c20f42088140b080c5500315240e0320040b4a02d5038044060b0560160f401c2d00684940844100b0240070320800c0c07a80360300b8001045400700000c1c103000880e03809400248046608031400c0b440203548250940803807a0078400946011915030340190348012140d42d403500c0509c01042c90500f01e0f904843c00c00080c06040c00d00c20459018600603500540058001022104540d008580701d5415042a50418214401c1801640b1144e1100c2c2c00080c2c213501840880c2d004d900790141c1d8000b9006052980c4400c070074a4079628270404824804000648021542442c001e50048900300ca010f4400d65440e118603400b0140d684082c0310072405801b8a808509041505100383c19018100d070024601e4284140403450305107242c11103123500745408 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 301345242 1250 301343992 301344011
    0x10206221b05060703030203041104060302060d05100b0403060c020105161d0301021e0703020601050303090915190603020406020c030d1b0c2102040f090c0611011104260102071a0a 79
    0x80710044c0c10400d00c65030703016a40e49860318016400000c141c80c0e03580198205402400140c2e60142507840300500c400c0000b405035240402030044140d81e500000c20741070002004800d00445401030b2170b151130b242c0c00a01844c3c44600e0903503035041d0303040c00c5940042c1081c01d0044101410440196070440000c0001d428170320322070a14820b2050940344c05110701c0000480c00109074060180900400d02140070b903092031441c03000f02c0c5c0b904500908140c03801c070182c84070007082d941d41c102480b500751020340c4083c145500c51102500039071286c02504058070406074940d6039407900052410044030ba540c2c039504c0c1c04010044050f21600c4c80c00040766130105c181030100b0700c401024142c160062443c5180a5048210300512017120080e1411105007400d00c8000008038021003504412114640b515079000403050003418010469020030400c1d9041c00180040c10b400d098503001c0907800740c114090425414440c40500300e20a400c00204001100260801802c1684a03141d0b03201f490344801050710b100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 301346492 1250 301345242 301345249
    0x3161a07060f0c020706080c0301060503040b130f150b030c0d060b12030d090b0a090c03030f02030f03150a0503060906010e0703020d0f2f070602070201030209090f06010206221b05 79
    0x11590304200181c0c0214020000c642d44140c0311508400c40c00042272555050001c002c14a200080002c0d004220090225030005801170a4440c15900f0004402c101c040c0c51078243d2840212500450542e41040e000a11610340403030078104801c40182740c51001c020717961319400508411150160300090880449165980a00c001d020b42545860001031001c454902603010307a40140141d88000d240000100024210400c810150b80c8c060038027480f0050070242c01c0780355101e05071800708000310200c14001d249075002005101d68a040f00e0400300103485000f45035442004032891102c0364011401007000a483c6e0080d01d8000c0802d16002d031812501d4015042a00c440b101051007443e82d9120001400d0380200c1d07004810188502d950509508800014525010b0400003a05180d070000c0c0003800c581c041e5044601040c0007401510191400080301d50b005142216414003500036000010806044d82d044a5036206082c40b424520481a803503030300140c9564140106000780c152001b14203a903 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 301347742 1250 301346492 301346501
    0x2190308040906060201110f0703081b12011706070503150117090c0901060521190516030c030903090b0c011401090c02070506040f051504031208040203161a07060f 72
    0xb000031020a03028940b6000a08441c03240d074240f002d0f414140040c22500090308110740600e900f51a04400300e440c5d002401d04100e03801d1a61000640c4002040007410003600b251034100c44058840c1d0b03410071400c52031580c551b00115504800a0b400b04001414112000154001c0c0301040c035104414800100c120130310b000050b075141a2a622503490114a40340c00071089002d03182c14a001801e00105c0c50b448210307904001d42888403001c92a0010f03541421121407580c80182c070250034403090a0a1010b400b1001981c0300e1500040e0905550150701400390180c030350440c0c0c4c1955012422468043d040c402900202c1030300c03242d55200c1e4500c0c0c0d0504995a1058064441c080b030020380401014000703407a002841d0711403809000140400c1203000504000c0d041100c105685c04280049884c4100c40c0c54851508000d199400144007940b506900c11003961103070b84280c0440c0e100d444201c041006a011600c40e00000407261a4941443c000d03210103420190710a0f200444c100c00f0804204040c1c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 301348992 1250 301347742 301347749
    0x1b03040b04050f0d020d05161b080d0503010f0501140c0a050f15160503190905210304020a050f0102031e0307031401080606041a04090606090509190219030804 70
    0x200d40328001e00c028850148110788400811900a0070241e05101d40691520310700d00a80d014442c01244030602e01110f54030840145a2080c010030740082d21941521004940d03005050301072040f030a40c070604c18060401c50b4182c50f0b29291800c004d03407902c0011988005c5841036180c840c0000c2c002c00e19605010421940700601c140050f10b4601032810b0440c0c0b810f0b4940c3c000300d018082290602581c0343d004100c0c1c2c06200043e11b401a0360303546002402401c00081d502480d0814602403010003804400b2883c19216031400055101240411514001c0b0340002c2ea0040d60009195004002a20f4001220401c460040c0180c90a01c0b44c1100f442060b00040c0d5901c0c0c440c0c0100100f0020f00701d07890322588416000400c543c00080d41000d81e1959a40402041d007070040d030780ca11001560a081710107040b2080c40040c4148001c0103540340140107005a0310400d0021410030003c12802d41000c22000101c101010040400c828a6020404050050b5213610060a0030b08404008502c90340002c0c0041c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 301350242 1250 301348992 301349003
    0xa03020735010f2003060d0f0206070804051906121d030c07050f181503010f020309030d1a130b0a091103100f14060d0f020a170a021e031b0304 63
    0x500d81e15500c8401580d640240c04c2403000310000700c940d0f6202041d81500c3d04035500ba1491060020186050307164110701c0300020394001030214000041014003001002503400036500c0c0644070441e02c0ca03035850000140224400300708610b0901c080303036800341c0c0705c1515400c0e01d003400184040e20f0440181154002c6030516500d0304001820701460a0000e80148031100c182d5142018041035480c80024550103020380e040c0c02045081c119070b07035500b50400681001030080031556410509011a45c0e030b4020480078030030500303001c80c3d420694600b541c0d030310035210040d00079900d40c0710141440d40181a80c00c441a40000e4500c0040742e0b1b240e65102d1000002000c0080c241d4034109281a502400040e0340301e1403400c0b0102e8401d12041002d290b10300f80107501074420075100c03180c600d90780029125600000701d803688003060f15286284c2c8928000d5941308444094600ca454a4003018141d1183d10004814508100c0c07000c0b0254810400650303204440002800410954008a11140d8420389003500c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 301351492 1250 301350242 301350251
    0x8070e1f170a02010e0d05060601111f0912020a0b0c0a0903062c06010602030706510e060607030207030b0103030e0913030f081b030a020703020c030a0302073501 71
    0x11540c0012850170503034000c51b1080c0182025a44060b41d909005050382c0c10010040c2c0c1aa000c5031041210b150008003288240b80c401c828520b201c4020041074405403510f040680711b24100c4ea0010408ca081c8030742065440c2265554002e15040a07400a42c039002041800b17030300003001c03600170301c10b02e1041345000e903004141250301642c0e00f411081d0300c12011699046080100812500081126400340e4441c1c0c02003003254108107902c4a40101c1c60040d9003078202200349003480003440e000c5481621034001002d440c8254102c5144218500d409054441324500b40440c0052030f1200c05030141c0e612a10403104200e0b2659a46401d40d68280d00440100305a00d84401c041d00d080d2111580c441813000d190002d100341501c004207040440061071040c045018041000000b015000381e02c414500403d9035980e003801c225820080d484a0000d8005004694104060b8036001c100d1040c41a0998001c00403d4100703c40d0b03030145041c280f44070848850000c00c455160400558601c0c104284000001d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 301352742 1250 301351492 301351513
    0xa03050709150806070c0206041211010f020c0a0b0c1212190207081c020d1a03010e060112320c010801050303090a1e080102121008070e1f17 62
    0x4080c0d8075500780708402080446010f102402c400540a988403180340780c10819442e4a00106806218982202d6103008801140b54103000d051201112401002c0c0d032000c01d01002034100f262101d13440e1005550141d4021000c200c41c9180c0303c0900308428968060321908181200004803660040c500f8403000401d4070b007041709400c240b4000078400d05190000f549045070a81c0c0c3c0e18030511400482c0c070781e540070448004200101c250b06a0b1034842e03074280c08003c49804400040038100700c0c00500c501c2582043c80102c0c2410021648030304850241299458840d219907031a00010704210008420b01410840c00030080b07140d0415241c2c4c08a0340000d005494212070004004100582080b406907004200c41495034481492200c11100d803141d205165184034011035107201c20503071240e03020358004108c40920480480c1e00900591030b0a000908813a5541552500c589041c806c85400050364400070319102c840c2a030154005100511032a40903031035080703040326640c110078101075541c402d0f92000d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 301353992 1250 301352742 301352759
    0x10020703200303100e0a0e0f03071707211106072d050d0209010203070b0f180f030703110a050f030d060905060d140304030b090a060b0103020705070509070e0a030507 73
    0x5800c0001c0710701862640ca8030030400040683e55209414124030240000b4058110381e620060003500000199a080d0b100c226040d0b6030f9403c4402e040d42c203001811074010890300e01104490406600680c82c20141e40620950712000b00040009400d2003800740c10103441500a00081d440b40d0314540700e10841c031080b207200410010801c040d00f803911300d221422006244d001026581854a16940581e0f590541c0f00102c0c2140901000280142106014418010700070340215118149009400b10320f0561412629540e0040444a200e560020058075010910070a0103060b124240c00458010308101c1e0303a881e00c0d01020450f0f103100c1d030b0404030312140004000e00804000307103a4000c1c144030b5401c00d0300c00160780840400004054461880503080c40301410f009480c011500141c00c034032545040741e420764407500300c20400c41d00d040c07902d482d10041d507009209490302542c100c0c008000190409050003042c08000d130111062081030b807510605035a9a41940c0042c610070f00150981c1440c2c01100c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 301355242 1250 301353992 301354037
    0x10f210518010203090c09270d18060509010e040b0d1b05010e01020c121501080d0f08150f060d0e0102070209150105030c1827071d0f0310020703 64
    0x2240780700d90040040c4504e83d14005004a940301c0d0881e180304103a203e000e10800920342c0700501000c104080c09401550b4400460414403601c02a1120360441004074038001c910940e07402000c01144051060340c01c0c0e94819080300741c24100152000a4071341000000032400382800d0822a0560000b20308034110b10302001d12080201020300f0715448000c0300000103912100032140040c018a080701041d0703e003000030420624800c01c0342204508950b1140381c156100d44a40040300d0108413910800d8254512480019106032600203120303011131303d890100050746e80e040c051107900980a2202481100e00b500c200408100810001640c2e08043c1c414800c2c940c00051070306018480c800c401003c66600041142c0d0b0120710410026940e25008000460518440c0b00c100d0704118907001d1348991418220049290030380f1a4981c005550f502d50f42100c5089c10842104d030034940688900700c0c94140b4000c041501400202559440c256520a40c0c0c1280c2080b130043e00041c44031180c00030694500c016 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 301356492 1250 301355242 301355281
    0xf0e0714121911090d0c122a06080703020732010605030c060909040c0803041d13020f01030906060e0a021e1201060e18090c030106050d020f010f2105 66
    0x414044066443c0f08000d140c02030094840c018a00380421034104040744840b0b00c0903107200092910b1900701801d160318006404075145248241216203604103441e082c11407001c60f01c40d80da6220b429035410f003080700070350007042086404450400001c64101c0399200354402001c480c9801302c1807454a481c1440c29100180d00c0903010790840701c0307105419101c540460b03034002c005407a00025a180da181c8603154591662040e1801d000221f80810500080860026450080390f4111040d03200c45840d91101807000310025030140c0f02c1c580d00035207540641c004207001801841c00164990366a0f0f4a00342c1c41000b240c0c003010403a400036042c400e1314400302100701e121603461403144c01c20111044014080a041c066981440076400003407605a4400c80d54418014081e4243d11903424803200003581c0300d0828203881d10950a118020429007480c22204141940050040e03403030a001c88019108080d410a14400b0002705100710b4104040d80b10f100401d071000c07000c00103078a01d0001d20842100c980701c81e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 301357742 1250 301356492 301356541
    0x3070216030f0305071a0a0203160e0904060c03060f09020a09060206010f1a040b0a110705060724021b0601030b070306050603041101050d060e040b0c03010f0e071412 73
    0xc280701203541c1c008409400d55040c20a1540c078565410300121100940c07018110071042c0f0002c0000304910b40d00a54000d8a22492500640380034903001e84800703003d8049a81c2154003d00003801041c0b064212040118041c1000204203444806080700003403550407041c021a00000c6142800e07610402d040d0041c1540e1000e07041039410300110704001062840750648040d021129a41d000e5060070485004041c08a66144d40d45407005020b85801c4141d0841d900034000c0041c001911300b0040105c500c016030200e040088006405034035901d0b0039440b468030342c2c0241d081c4802070394003150402c020340c40c0b00800003e008962440c42c081c2c83c9441c0c000d141504040c2440420071040c0c0321038054079006644264505210040e200040780c0c01d0203880d005405007418208006030001e00d24807194000e0340a079600f52002da031403400c0350030030344000c0c45104507840a100c0d00f00500c4801c8030710281c01030329074588883d4101d28a01c1c120b0040d01f2060300105003e0018062064000038080380c84600003413034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 301358992 1250 301357742 301357783
    0xb040908120a050106230d0204230a08100e1608030c010c0504030312050603150a09020102071203082e031a060103110301150c020a08060402130b100f03150b030702 72
    0x108005102c2140c031b0021914040c0450040000e0400c500705030b070044012440c1c01c54641d99500008a0712043e50884101c4500c0741c40301c0004075041c440020b200766041880101002ca400c245050000c4c60038402d00c0809001310f08280f95107003001c1120000601810340110748440051483c107003100c5000c0402c205101041108000194001074081d1142c0c401080001c0c4130f5071141d011074201613030b401d14040c542ca0384071300700290b40c1d000358050030109000382d00b1101910348030800c01400040b0610007034049a2402d000500400030b550300c608005003440008084d03241c0503611850712260315001114030a2412188038022051421550750001007407800b4407082d42c200d82c588081d8070041c0903115085102c03200a030318581c0103180c018516503000c0d154194150781c0e03503689602c4040070b81d002c03407061944165035490b004081c02000102c003c003d10b059250041c0c114143c1d41b848400c9104c4090513201c081f000d0448070303c0070781040102030949400d0782c0d0740ba142d84000c0c14040724030344003600e041e0403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 301360242 1250 301358992 301358999
    0x101202030703021020100f18060c02120a020304171507030c0201020702031501050301140405060c1c0510030209010506040b09280807030b0f04050c040f0b040908120a0501 75
    0x35003141141c3c0c05903a1010541c0c0c03507910888200d0011903000d83c1a450411038000072000c00039441c0358015803540c040120b501040740365810780d9603400c01100503480007261840032908a9100c00c0d202ca40c58011969040e80c405c8643e0321680083c1c01c84005a00b0104041009000c00e0440707001996200028041d2040d405681c094110005811801010390314071001912034002d6040b80d82340307a0000c04507540d01001c5100042686c0c42409858003039403c02507007544401104656900a6500c400540030720740d5810075030780e0310b600048001d110701c0c2403201074204040082d02ca0344c1e0003113204d041d0a8035020b081d4010700c100420103a002074040e00e81044100301c0715910070140c802006d4101d404140340110902e01032200344520700e081020b20040e020000314000005082400c407481008040d00c00e81e0784800742d00c0540d80846014006401c03184013440145060307445804c501040b95000909a45040b0224040b0f5030b00c2d643c2212611400074140d110000c81d20b0701b69920003c204002c0c00a90705 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 301361492 1250 301360242 301360249
    0xe010609030c2c0402040605060d0501091103010b070b1b0315150a0509150f0c100b01020109120c060906022706070f0803091f1b020114070c1104020a020303101202 72
    0x848034000310440f4458004542159200d41024006141c001c1c01142c0703c90481400c1c00c000c00c0f080c0320703405540c0e282c06108003142504d8015070b4121280f202c0c41b80d08108403a218910b500b14010001e61200b9034400364202440a020082c50003140444442c03c50769000c20144040724403050880b00e0018030605c15100b402d0385c040100e59103503409032812080c00d03484219030001d0740600304002400c44000b040c0380c51140c00c00200925441783c3c405080c85080305040c0168201c5210520140000907560001c20104d0b000e1450041e00350300c158070001d406003040d16101d049070011326070b81c81d481521501a4400e18049105280f110204940c03c03441d100250351006030743d49401000801034a000703c0011620b48081c05120713010a2003140304040c40340142c0c8200e00421590345000b81c1410b4250a0100d00380c0f0502c5114254040d19000ca4116103e02e030f0240c480c80149101260240710800d0138148540b0b450014041207030705078000715203900b0803500c40001415590004607006c502e02007408056903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 301362742 1250 301361492 301361549
    0x30b010903170d0e01051303021c140c191b17030d05060d0606030507030311030c070e0a090f0c091107080406030c11060405070e071107050402090a0e010609030c 71
    0x100d0380c068190f941c100d403104000a00135290b00c400d9194640300400106030801e800502d1260311035401d854070340c0b5052040340c0f41da006070702c0e08000140350701c1141d0f072000309048010300c1c40e4175540c003c43d080100b0084030301c0030003014610115680d40c0c803445103407000681180150b025112a00982c02c040d0030040c5c1e0203a40b405240420f410301911540820b40684400c0c014442c640d4000400f03200c11a143d04201c4d41d100d046210460001d901560911403580010040d5010148120050841c4900c0d00d84043c0c901c00c400b50000400075600d45c540390029030100e190550141c1b140b0503014180d0f01d044414011904c00700c2c011107127944200001e000003151f070300c211800d6401906001894201e181c0342101e812944040042441c46220240402d00c08001100421184180c1401c8405d58034040c040781c1403500300e040410f00c3c2c0e1210009025601c1c5c190003a101c000300107400250519590880004080021b0388110003103401070409100340308403001642e000c0c03c1041d00c0524901201c2d00401c0504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 301363992 1250 301362742 301362773
    0xa050a02060f04050a0b0a0f0e030a0f080408030a0e1c020a0b070c0f09090b0903090a03030e120303071806020114040f0c0e070f02010608010513030507060b0301050c0406030b010903 80
    0x5060000b4040094440c042c152000382001070070504e0034540340c0500701419030080501501061043d207884490314464181442907160140242c04081b4069a85900003500703a601210021b00600000c03840e45820030103030180900a50f41e03001c0600d220700a01000d010915981c800d11780701068510056210765050808a514040d08156161014200410f9850b07a50b000300003082800b16000030307030040d580c00403108540240c2c52a00e01c1d440d0185020b660b403280c1014940c120542800400200c0d0003004907903c445400703043d21981440c482c001a01b1944100c0da048040f44050030408000540342143d440600f1060000300102c50b5998034120300140d009000a0052614107890701c20080c100708214000c2030404451040d5091402010300001d10001c0f4200066207040c03030006100005001e441c1c0a49005400054441c00701e46040302e0b190301440050b01c845840d0605501c05803000d2003140d200e0605080010346590500400030300f0345034401401e0703040002010007070021031449403209401c07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 301365242 1250 301363992 301363999
    0xf050c010204030f0605010305010f0608071505070b091f0e1506120109031211070c090908070f05030306040c030212011e0b030f040c06110a020d061103041209080a050a02 75
    0x12051905001030182c42a500b00800080c19003201e0010051540c1006041ea0310990007885412007901e00340045070301781d00c112501c0d80d208180401c410003007241d940080301d81030314141e4900203e98842e4042d1080c16103401d0603da100002e19000880131407200e50012030710306030a116444c1007180081e514521986600c150080c4980820110350390071030030042c145125030081c0301d180e0040c2000f622130380004402038480c0307040443c03105611201c5000c41c0c06580d0700101100034641010864801080000000c88101c841000908041039184803040b0783d0a04c034070b00941d600d04d0a00f007800b081d01e6240c5104401e150040c822540007034111110a810340354060180724024004203640c00482240780c0c01007075081800001d00030180c2c042071225120b00c0c05800b80a10043c0da41d0b0003141e000040c41c605000030b40002c4c10040043c580781c01641c100c140650303c007046584c540d2241070110b0b801542c084811402c00700320910b440350445030a900502e01800500402c0c0615226a5290542c502d4003c1c0b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 301366492 1250 301365242 301365247
    0x15031203060e04260c0109060621020a0b0904150305030a02160501201c0504051002030c070e091c0e030d020111090603190c02030a110109030e040e0114090c0f100f05 73
    0x40c40c58000955100202405c02803042145d241442c0c0000c3c80c503409000d560454aa0190800040c004201901d403a8003514141c840c0c7d00e805000000b9400480101ea4059155500082d0410101101c00051405000a5a51801e1140029180c005440199860301e40304040401c5036a0300660041041030804a0310300c10074058021050400e145206082c10b010403180180c00801c0c0d000c000303401650410746680c030001403210810b03640c0b1f02071500700f000c080e84040700500c1151031207000981c00c982d1080880c0d5845100349a040d6101c20f130700c0d500c1400550400844009480d04001c0c00c003244050780000c100b0140700c0800321001d0b102e01500310340501c000101284403003e10710002c1c1220700c00d20400300b141b849035a800039204d078810702c0f0303480006441c941c49006081040c419018000e80c55121004160b0004d403c0c44054803460f450220345540c0d4041ca203e0702564007028611408001000c0c10b0901a100c00300030301f5101e024510380c0200e01e214601e001164102048889600890800c5038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 301367742 1250 301366492 301366553
    0x6060405040b040311012901090515031b070b0c0d0f05070806100e0346030c03120f0609060b1603181707030c060c03170a15031203060e04 61
    0x3809042c11f124a000000d130702c11010024401d5414010452220903038070b541d602540c90042140141c0c048094a00306c280820102d0100b0b900300140c1070a401c2c1c4e543c0424100700c200d40740d881c840f81086841d6059410002005480d0075414403a0b03500100302c1000400c000e050455000b00700703501c010026802807492050070081035014a8140c40f110344003d04840b1105c81d5007255010202d5104c0e204208002507840740905d444000d20410b01c008149046a42001c88a860454401080f210306400340b1003134000110019685004a02840101c1440071440d60f182c00007031800c44507143d00210643c0010321071800c002004410322084550540f801c0e840007c840720031841c0c006a2944541003c083c910360810900e075000c9206801c4a01a14011400541d42e01c000c6d10a403202e1380c0c00a00044030b41003801c41c220168102681c000100b50000511188800c62024900200390800c2c1c41c0302e90346121b50f40e5025450302401c00a001c4a005c1c141143c28a076952805c882e40d00b0811010b011450807005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 301368992 1250 301367742 301367777
    0x8030705040b0304120e0307230103061706090705010e0904141606020c011206060f21020a031b0906050d050714071b05030627070306060e01060206060405040b0403 72
    0x22400380240511043d9a401d16240510340328400400c090040b4081e012190014540401d411084514210302c40c65001c0b00b0003d29100e1135094502d150506560b0200402c45a124a2091560300321080c002d00f207a003441f10300d10345004481c2c1c0c4298100216460020700645819581580107070313002c03040d6a0601030346079101c1e091181c455054106800760030000900c0645c005580d41000000b81c80f001d459040400c100410b861040c0103a9021501454813440d640740b044110300000b69122005410b030305c0004a03100207030782c00400712000083d00c91400d464403c00040904145010500300030075054506000a8034502600740038681c02c69403880064085809a0324142c81300003880340103540c5079000c0c54888111401c0342044403516011200200d018240080c210740561007040d0b1b100000b1000728800750302d06080040100440c0144800040028050b0060301c010304481b100c80d60140d030502100a00d0f140c8024142c510450078441400081840980742e9500103030140b80c00c24007030440012b80b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 301370242 1250 301368992 301368997
    0x5091c020c1203092710030206040312030e06131b0e19110304031205241903020a090c0f1e050702012303060f180f09070f09140a020c070308030705 65
    0x1001c0c5c212021040610000050700c400b40b800701c6414800c600303280c030b9240c85140b0400190200039007010742008284046000860a1400030709585004242c00c029160040d060640a40d030020914491076400070420290b2000030186540060200c1c1d140c6182203441d0036040006801c1c04814018508070444481c0160040d41c9840780e414507695481c01d062800400003003144d44241e15441c6040c010840c9401620840d51280c440fa00e00e4128280391071042026100a50507541e500803001c280000040e01e40c0440c80c0c0050400705c5000811042a20000d80003030b81d002100070130420300c40414581c503401ca02501400c4151494500e840301c0040c40165602500d032507034030340c942c0402e603110800c10030700400451041c0d909466105030311f0400c2007400440e0078218000c1c03400e460504c00144480c16014035055114a0090440300040c0d40d0754144082d003001c5402041074551034a68a00380c04c2c007104029500101c180404514050011010b2034441c20b140c000105a0400080403d03003c52082e4103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 301371492 1250 301370242 301370257
    0x3070506010f050418030c03030f0609050103150506030f06190f020318010e010902060d091707060f0b0609090a0b04060918060b061e07020315090105091c020c1203 72
    0x312500c80d41c4074441d1002090315403003403030300c00ca0600d0166140c0c880002101c094040c0c0c161180e40203c2d6895506401500d008081111040e40e41c0600160080702d601580d40214042d5640e44000c80e1500070140a50740024603a5009900042884e1f880743c10001c3c1059000301d0344001010001214a8001e010309031503942c0440c44c6001100741302425403409511444032f00450001c000000390088a40d090300e44c400c401a40c40101400584100303146500f000500c64070070445a1500600d0610402680c0c20401065074007968070041030341c4042c1d081c0b0400c0b144910480b0a9810a07290000165a1650040076a030700240c5031203007404d8945841e0081d101804090005001410070010043e8000314818001c0e0350807800e010440000b41031100841c0c2d18100c1845060360311080ca107418018540c0144812a014410102050708820821a210f406500720000118890516050007460143c1c12003044d02019880003805080790b400107040c04a9131380c260b0700d82c0443c801400401d400c6010314034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 301372742 1250 301371492 301371503
    0x5100e01080319020c0a0311030102040b04030320060c07080a030603080c100506120304170703060204031401140907141207030302010510060c0f060207060e1c3c020307 74
    0x81071026000c00903010303050350101041c0d181e92491404a9490307289551150700b011001c54107001084040b150380541c640c0240c00549405d681c1c44032941d259200c0e41c400d60008000e0016290388040008619080040120042415007044640300000f0300c502c110041403800d00042414016000307400a200440e00300039484c2d22801c1c041c00d919190b8080b48003144100f840e0038005855481c144500040782990000250705090408a58520301c8a4405000a45105000d800000540540010405140b14003544028010b11000b89804d444901000151075000315041081000b40051003004503200340a5007000c84070100c020031203041002d01e68250500508001105042d01504254003c90808800319159030f610075044039058a2080c00410822880100c2000724a01e41c0142900314002e50000a5855170075010034070388024017100c0901000c0c4551a00c440703a411050301e09800c4202818103560341070712030703814400d9a444003000b841c88088805650725a8820029616003a0303210 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 301373992 1250 301372742 301372769
    0x30f03030606180d0f21080907030b0705040f030809090f04020f041509020c010203040506011d04241806060b0412200d060e070501030606050a14091026070903060510 73
    0xb41480101ea0490454042c840c1c2d0031b400e81049440d1080141500c11201e800c00340131603600f590f66200c0345420141c09501000701c01e0001150b00f10f086480f12006500c2040020350320341e41a010b01c0300000c2d00400c0071190721840d40401001d40c40d00d1002e0469001c0480e40060350b00d0304404201e8880d5016000524028030200310102c8480d015401036010341c0c0904101c1e50325a9a0780a08102c1c8101c820400b4007616841e40418001404140940620b255148070349104060842c8600110307010040007440182c0b503000d15009008071403007850042c0c02c1d515000342c50107092510a000b425444007008100c0c174080344030303940200311403030750105c00e1007000f04149205101030403d10301500301240c510545d4010100000b40ca0745c040d104500441e88281c40e5507042032010482a1000400b00d40701c2c040c001400c0281007065525001c3c80034402c0540c0d29104040b038200000d1110510318280d4200c2e00e8a1032905100740d030740c3c00410034000c903688603d01080d02e94403403030310000040c1c035a440a01440c441c07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 301375242 1250 301373992 301374023
    0x10c12090b04030c03260d02160f030215150d140106050603190506010314150f090a1e020a0e0d0f020405100311010c0c050d140f01060302030f03030606180d 69
    0x1c444003200311313401001c071514000c2000341d816094003d06c43d5170341d000113410040d20b8400000d1b9005001c000c080c00f032051901184a894851044502c000304a0058210041500d4070f00c0320710400c50303000000c540742d80105842c15004120302c0b0380c058101900e808101c0f1002c0d41031b0142504540083c25004e0481c940340c2c01c01a0070b8003110b03041a003413980010704201c0010300703a500c00d1040d03070400d00c50060050081e485559040c2e64000e03040134803641280711800100410384800c40690700070180382800060b100d20840046070f50f1076001c5040104280100310b100c00d269800102410000421036400e44008000c0c5001da8402060b084e0087d0410b0400d0300300040d0343e62042e00e541c2240e02407500b400410303482500441e032460402c00700030000d028401050001c1d02f40707843c22a6407144281e01600409072401005443c184001d81c041d62560b440d42c070107008504080c4120039031000a203004505600300b04c0c0c0040c0040c000d00103140d0100905404000445d0354a01e070b9000041d8102c008400c140300d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 301376492 1250 301375242 301375253
    0xf0c011b1101021e160609080408011808071407030c06050415080f010b090111030403140d0c0b130303060e0f060111030918331e010c12090b0403 64
    0x11608450008214012001c1c01c8501c418000c807945900720100c080d80768040032a03003030740c44c2e0031408031155000300140d4548001601445080801ca002c1d400e11901c407807501003130509441c00306441b8800a0b400500d8100080c04460550701c0f0035500540e004a903c0e500c0c42000d15040159001a0094450140c00180a900600104140d4920046a1140c0c1000241c1038800c40300075540f010341119800300401c0350340c0340e203000b520b0440c03814541422698039514001d440c54000c2e4001307558000448510100c0540208012101c18489040840340781c5c040703071258400000000c055a0070105150740f101c0405100e0f43c0700720081c1070303000302d0b6524900703008003d940d031804103da1841c00701e1911540311031048400025a182ca46c00184170001200c12181c1a000d0203e001e00021011024071005203007003825510f0700c1c0d200b0b40c405403071902d024442034100b0000d683c03015000056154031140f604401d90703014a40c00206600101201010000c003082214400041c1d80180e40402c4041004400c001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 301377742 1250 301376492 301376531
    0x3070309051605130504061d101826090a0312020706030e0d0e040209040903110c0910171501180b0402030c0307080c1c0504030219050d03020f0c01 65
    0x50040085a15030421031518002d401280d000d8a5448444804001c0b04590030303170070850f4428860140840e5403103844840b007041240c03000c090440c54000b003600e41d100116504c00c2072aa100311909204122141d038680018003124003200200d103902d4142603060440f08001182c4001c1c50140400c2c1c81c5903501d044c40c403080c08003007003a02d0050082002c0000c640d80b00740a51220001054040c0c02110040d40301a03804078291104544c12a80910420711165103c0c030801618070302948030b0001e54102c00d1017250400c0782c1842414403c503e024103101c0030506101000c1c0568800303d210103428102820310b1458200b02e41d8500226581200020800d001c0c1e4222030081c116441c2e4080c880c0703c042204002c02d9000868941045903030600014401600c6040c1080c1c00004140c0700c1480c1c8501402c55800e0039203045100c1c0031070b54079102804101a8108950302081f0044002d0680080042e66420740798480f4055080400d82c011422100000900d022110b01d100ea100007000320100802c64001c040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 301378992 1250 301377742 301377761
    0xa030804020108130c0902090103060305010e0703020a091109010305041103010c1e0203120c0304020a0b070506010f15080627010f030302010510060207031205120f040c05010302041208071403030703 87
    0x41140f00483c4041018241d039001050f8030403400c2143c2810000c03034000075008021001d041680f40c19000002c60803e01c100c010015051012b803403041d0942c018404003440b035600221020f45040112690040d0003415241005000d2030080342589890601c4140c2030f40070700c080e03030303140d4a00900004032075000a61050300c503801980602e01c0015010090b0f80300d001c1c0070380065000040a00041d41c040c142401158000d200900c4038003031a84420490301141c10003402182c45034041001405483c0342c202c031000040110070206551851400f800802600b00942a00c0c00303014801e025140041e0311000410213010707044444130a0b51707901c00380805600d0301803005502651804001c20107810b00b0843c0036042e500c8a4005001003869035076142c0f507444014010000300310041c48260340c0750744001c001034054640f01201c0d40b00c604003418031380c44100b800d40c805814903204020412400311030102240207035030000c41260300c0728401d003483c0b440101e1128001600340000410000c546070941e00c104090b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 301380242 1250 301378992 301378997
    0xc060e0709051303020304050d0c080601080c1309030e090604020d0e0304141f1b1a0403020705010f0f080c07060501030302060a06090908030c0c0705090a27020a0302210a0308040201 80
    0x540f285594480d410a1812024005030000c002c00c0c816410071032006a109403041c142000c4e91980c03804243d003441d0b000c0c1c1001c06140c2040109182514007100c4001440c40c1c8039a0410084005650181107034031060000e500804406000481780c1e591641039030324280582c9014000c1c840c0b46000c140c1c0300e034003501601c800191401032410041c02e0a8888600c040103940c52080b11843c040c1c0e00341ea810200d81c2d0122741c810070b1001104001050407890710300146003100c0515540c142881d010b4200b44250f00523504001d944115000c0207584003200082660150502d8041da45074910560030741c3c0b003091805800c0504000c00001055400200244140310031034003080440e0b25440d2803026031703c1c0380001078a02c002c140041824030408200800c1d4403246070003201c2116070b48070b010660040701143c121002a07a1880090401034070b00e0440780c80209400a0400c0d10781250307000628640260001900501c4000b108890f00101c0264202810103060b0441b00850007a18006120180481c2c00320300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 301381492 1250 301380242 301380251
    0x110f1509030115030f02061c020a030603020906010305071d0402090303040e04021c12081305070f08010c0908030703050c030c030304060f060b07050c040f0b060309010606030615140306010c060e0709 87
    0x1a0342d440d000480541754461000d8020b031025408001480d00f1000c0400c074001600d40400d00100200e200911040c05c442d02d0102d0540d25500401c2002031006040038140b5042c1402c025116a1044820b4014200c0100a00040100b500450028006d500509400d440005401710310043c078030844a101e0392088841c02c25038900c481200c141c4500040000300f510000501c203000300341c040c4040c0c9600140c01c0d41a546403803c1c031303182e861414009500130005605140790512004000380200200c541c0d15090400b040e034503200d540b40d52440f030702a01808011022400340d219030740500445000c00c4281d81120345a003880e041c2040102080b1840d81140c1c2e18081c80001d0f6407030300006887c00707607801402811034111140e041c00058803c2c801c82c840c005958111040d06907036000003440c040c100b11300000400c41d00302940030b070882c0c2603134024202200c4010140b0740002c0c0d000104039110308031910114ac1766155000141c842d80340d03450000b05024100a81802c01003000a051b4040781c050b41c50910 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 301382742 1250 301381492 301381511
    0x3030c0c030123010509131a07021b090f1b03071d04050903090405040c05060c030c0f01060e0a0c14070515160905063115080f04110f15090301 63
    0x840280002003041c01854803d40104524034000d18501e5003c41409200789010030299283c8549002d0040b001039143c0445c802c1c8080d8940c1080000382c1c0500302c4080d041c002c00c8550000b4444640144142c4020701318000003900303e0308806619964045001c10291242030454028020031414400d00d201e4445101400051303103000d000e60740c09841c802c1d01461401c503480c2d050001401005205554800c15000c1c00203ca8840400406409282c0c1001c0c2d52514441007100703080c4610091605250380c1031100c14450042d002c40c0d2542c0200906500050300d60300c0c42c5003600c200c10044e0320550b0440c07011844005010b40403c0d038030102d6130064040070096840c01d6141e02d100e200010760b500040ca00240034422810042c1c002c0a480360744003480b41e4145904044c900008901515444803c66444400c0000e45c58218031b50107441001c0c106020949003504500c011a240104050401d0f80c84c0d4082d0501a03c452194031161a0040c10103891003480400c200a2a4000304599001c1d600e400b01c8103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 301383992 1250 301382742 301382771
    0x80a11030114180f030d060f08010504050c09130606060e031c0504060c15050103030c140c06030c2d03190b0a0603020901050d0515092206150503030c0c0301 69
    0x8000ca60101c4400c1140e529051905640310400f041c800400e40315844407028058804c2010f410b00070b210701c0e400b01d00c160401203a0300d98101b4541c00396a450707040809004c0003c0d4003007451071507843c05562052056039111070508120202801c01b62005141240210701c6030742c000801d1219283c19000c170345110b500c4c0c62020080300102050780002a0040c40240011407041d944a1001c0340a80f505500a10080113800d0444400780c0c001c4001c40c10603e005820065244c90500c2508a00406401290500c0b808290b107480000c1c19024401400218481001030008024004003641e000220010502000002040d0b1064401d0400c0f106441c15101c0c83d03115034042c80c480410054103102009261000076406034001140c058180003050120102c1c02d009c034804d039803040103042801140c41c40c40000380081b42501510b419004040c031126a40e0264100d508102c00782e80c48400044c0e44200ca03090802e040d445030704806d600d4040001c003620b00c2500011442050340c400c034006c0203c2c50b0b642c031b800c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 301385242 1250 301383992 301384001
    0xb0409091103030c0a0209070c051504021516020121021902100b01140d24060806010c021f020f03071103010c020303240109090e010207030e060405030c04090501020c07080a110301 79
    0x800c0e00366005c414550018144001c281d60031803098203103180d2051465a645040492000c619210400000104401c0d0328024045070800d031110b201035403a04e40138825080c4591030f09100641441001880500c44280c0006001c2440d0084103045498004204aa048094402e030b127250052154400c1e10078014810b2082d1243c00702c0584681c41403581c0030000b2510b41c0c1007200200c07003c42c0d8071040100c03c0015250040003405608803d141c00c40d007070030070140460384080c041c0c0d410031034400d00020050702c60b106000319038508515800380c01c00c42e80c10300b05d1400c0f07950748034912075002c08500c01041010162041c1d505400450092102d45018902265240022590312002c640890007000520603548030319402c00506151128041c0e0f01c0f00c06902c1615009a84856160f5000840d201450351100b120500160f04442c1140741903d01b40c000f0ba030703840c005401300b40300325554a407807020400c0960488040800001c1a1401c4a6441702e00c140c880000c04815100c00b416080e40010b80c0c035043c0719 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 301386492 1250 301385242 301385257
    0x3070b150a0e0a02160506010e15010503060d020301060807090b0a050d030219030c0803010e011d01030302070b0a0504031704150c020612070203090301050c1c0b15130b040909110303 80
    0x160340d251441c26031211001d09025141e0f402c8241c0c20400041d03400c400f0b05020030800d010308001c0c00c85514040094404203c01000b402c001c2d003500080c0301e4260380c800700316504420103e5000c40079204600000340100803c2e8402807103841020000900d01c00103070003003104804202d8280c0c0d0620368910500c005151411401030060300014040460303c50048440400b050085c80c01d5858a40e060f86d0307510099000781c0020004e0710504004100340e004009040d02800300100107200c0d45e515650f0081c0d5250080d00481e000100b010401c5c1c07000f58480c105942c0210f03000140002c100f4110720707204040d6070050064181120b01003800c07889141c0603180394210039502a0030302c1d180c8180c03d000c4402d9028041c02960450008220040c0c95a50074040d441c059500020341039550388103156000070b101880110500340504048804035180d681a01c2e2600c10300f8116000d0390b035080307050110000d031215500000d480308004200881c151295a102c106d4483c0b040500e60221140c56040503a00d014800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 301387742 1250 301386492 301386499
    0x6050603010e06060c0f010f05040b01081603060e030d11040906050a0605040b0f16050f010c1103070b0a0204050d050c030d21111c05040209060d1703040f0b0903070b15 74
    0x1002c20a1814041300501480d40709800307885d80a2a00341d4254259080f500c01c550380c2644030003e001c02d00c5860b6403604c1c01807134590000c00351000d085040000e580860700c00500718039600d589800280c1c0f801e00444004d03040d071207c208001031380c9070701d8503206800034000c83d0030b001d241203804101c50030241c0004003618400c0d1106801c080c5440d920381007560111604042417a41400311980c881c02d81948154004e2042c80903115510078184200d0131150605800020040c0440d180c172a508d00120807914425000f11003120b00b956031803c0100680f05580c44140c0110b241001241407040208041009903821801d4903891240050f08659400300d008602c11074007201c08100c108001c85a2054080003e207100550400c0c0010300c124000c07000c004507103040e15484134104030462405501c501c2c2d02c1401120700a810701c120361914040c00c1c2c1c0350111100440d500101140900009100ca05904c3d0752001824185180120002d0b0304c0341c111940c120b80c81c18410300031480702010700241110406015 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 301388992 1250 301387742 301387769
    0x10f0812041404140f150103051512071d0106030c021c0804030207030213060303030e01050906040308070207030803070306180b030c060703110706080718030302070b0a2606040605060301 82
    0x501c0742c5000002c1440320982c003540d03540d100c2c2da4480300303004001c0c418010071480700501c1c64100140b005510701c5022441c1054541810481046842d00e28986d442c101581c2000095012076510307840d005107078002d4040140d0310317800a10828802d0310f905040e0b803201e680c04e02c0801c0301b41c41c05a0703030380d5240d41008131400c1220306221a42c5100b003055a6025010348111508940e803900419091a5680c001003c0145c450174203005242d01401156640c40b5031030001c0050745004c1200c80c7d25a20003070001030412120300040351019208102190185411174100e0f40d690901840c068010002c40c0708020810106880c0c1950b10b40051065841000d00540603084150401e403c1020303603031050780d0031014001c0c41c941c017255080c0c0401512000d8500d03030320748442500f010036010700800d001070302c0190000306001003800060b078042001801c0790b0314040e1568403140a940150741a202d4925503d41014050161499050155600382d002d0310703042c0d408100040e00c0e141031009a2100740921000c44020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 301390242 1250 301388992 301388999
    0x70e0f060103020c190312112502131e180f140f100207050610031104020a0509090709051002070e0c0d060b030106020303040b0c03160c050c03010e0303010f081204 72
    0xb03600240a16100325007074444034140c201040c0c01108280c04150005a0761850780307174011803244a0b00c1c200481c400110790804a02d982a034200c4d5a500501e00643d2402c0007585003151106030220b2102d54005a0a000041d990151043d9038042c40c00e51440d50303810002110081035605240b0709025410005040403d82c00d80c6900401e0010700214044500c6502c41c941c81c01d0318188111807600c1000580945c1d070300b085040440c503101019090406515503254100300140045485151a5605450142c2c80e064800d506944a0142d9008a0340010244080100e9140c1c00119842a220b0803104414080b44414040340d035140349000b45c800340000d800109425a54100142007004d1200001040c82e544441e100c2c8200d070802c0c0c2c000320240c0d0000c424001000686032540d035029180300101401c507c2e145d0316001841c852100190107110000303e460060000a10a1641001e00a8000d00118085082d4a41d03607078800d218503d020700360030034046807008000c40c0c00d0940e240e031030080a0a007800d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 301391492 1250 301390242 301390247
    0x50610080403020705060f1809090a031215090917030705072a030503040e160905040213051903110402040518090304150309110a0b1c060306060b070302070e0f0601 72
    0x9025006805510501e40d00050a1b55541c0041040000c02c0400548503428207040324a003a003244290352180c5600010094410b800040c019440c40c0c05140c1279440d000300e04200b500134070043c0714840001c0d002880c08252800340c0d030481d000380d40c4118100164054900102c81f51404169592030000b42c0c1000440702082c05a0b000b6a6808995030545491803400d001c54800b01c900366000f203660740c001203010420398035903071001540103030352400c1c007841580b10040081801001c3e0090511a650100d046035080141550100103010003620403554407112703d2007088601a248011940824040b1400c40305e41072900a6404036000900800f0703450303003c1c2c6090510014001e001540b5448280000a200f43c0010301070800350300152400212110b4905006500f01c042c131100a01841103620208401683c2c0350855902c4540b000301440c0200d45d40202c20081d0045610207443c4505100020600300f01400042c6285440f039021620380d1030751025003030500030701218101000d81c882400a20303d0b50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 301392742 1250 301391492 301391507
    0x24030705040506031006084614040b010b0306010906033b0705010311091c060f06062007050f04090b09030405010905090906011509050d1202100b03060103060b1c03050c01050a050610 80
    0x648124103008d4808039601082103480c00c4441e56a00f1a6120078407003480290aa52390140c07900720016031075468a0800a491195907105010801d03035503000d4044145a1480c03072402061007507412103181000a6903541c0d2603e520302c030079861400f034000c0004036507010307110700c05001000148007401c180d41081003001c032000c82240b60700d58100c160f0b959800103c072031044c0c0d0341e1031006540015085060510042844c074004407a81c04e10720b6800c260003010540040c204048036411180e4036407482e1003c01040140c84c614400903d4007034140180b1255040220203842511400e0303039409200381d80d820800812103001e803080d04290308040d0040c048200700c0741d00103031501d220b802c1900640b9a10f45c041401c061110030203442c4950b201d020780914542c18800c0d01c0200090100600c03005a02c1d600203500d80c981844001c0090b5a41c0c3c0d00281d003600c80181e061014a5113a000d1400350585050184c603941c0b224880150651800b0b000440302d446502c0b03114003c6001816449050008a40c2034480a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 301393992 1250 301392742 301392841
    0x50a0e100f09140601031110020c092a03090120030408210702010e01051503151003060608030307020f01020403030c0f020d0c0b09040b2403070504050603100608 71
    0x141c0c40e58000703008030f41198214403160059000800e81d41d072560400786a8002107003400c5105041590b102e48c50180d002130b180b1181c3c881150318152684078444210010350200340485041143c8091001c0850b942401962003030020200902c1a2180002140b02c228008481032444400900c01714005c112a10003522159203100d000715400c00c1e440d03500d0301000000f1900600181e441d03241012222200b80076064000d403800a42805406c0044002030321041c03124101142142c031600021000c6003a121003c0046401075020041c654640417403589980c01180e80f05c02520640d070540080d1901482207804581c0c15503120b01d2070010f01e5555030342074001001d007613910072132100c1c0c1c81d0086a000e0028900810b0a0400700c1c1d61499070000780400d83e0381011241d8450fa0544500c10804c40e00800756910b40303030400c00d20700c1d0303641d545400a0381c20780160340015411007030100410201c924000030200545015440b210440d5441444030703118441c494660100b0049550301c95100190002000800d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 301395242 1250 301393992 301394021
    0x16050c030d02070b01061205090309010e0612100602150103050d030c1214070e0d0209010b091311030a050f1005010f4103010b18151c050a0e10 63
    0x42107002a100e000b80d0b04855401d4480c040d0280042126542011b0001407840b00e0138400d0005c2d207081c2550540b240100c1c1281410301000350800340242d0340d88000c07a090f034000643c4032421400c00741c3c90340000b007507240120b90140c07180442c0740c0400c42d008034509040342d0f4804000d01d0320b5071165600310007824501c0795807428080c1c4400e9200c0d074400a40148100304c810f6044400b030510340294020b01010300d0f0400720f40603004600407140561190040c1c00e0640304c06860081e510100b04003c00c104038500085c5901551030488840b10304004103000798082e0500071030600c20b40e240c00c050741d00007120a56003180d0400c010a010080782d400b07201000ba0b0051a421b00c0c0483c450800f106000c0048a030355501d039401d2100f00035041d1241260031001c548008984420b007198188802c4400e140b04a00004018600300c10542c8a183d03204058481c2c2100300030705040d00c034090140c0240742c4039a40148d4100203400c0000050380080280300b00c0800109100c018210f401244070104014407061800441 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 301396492 1250 301395242 301395247
    0x24050f04051011010c0f030c0e0d1e020d0f0605070503090a020d0203030d020a2307030219060f0207110307061d041e1107110307120b070e12071a0316050c03 69
    0x100f081080c840c0320084880d03615000802c540340c000040807a01c40380880800e00034114920f802d1500c5920000b0604c59010351401001d012000044248505002c00290f01806600340d21003000b41d1241950300ca40c1c411750042c001034503080340a90b250b0004643d02000c030350024050034058036161640b01040f17400902501d2900c003600f0380010903680107001e0301c0049030706c80540011400a142c2948c8000307122903c0d03d824501c440c0d40094659401282100603503a42d88003010034840194411008070300410030466440c401868440071503c0c45a246500c6070141c480300003074481c0242a8200910307105030918084c40300b000d082000500c41c0c5005030081c0c0c1074102e031040700044140b04286a113000c2506590300c038104e03490850b0140008444030f5010750010003042003119510b00c050781c4103030303841000104a1340c0d51803c201d0702c0d080c1980c14580d200e0404254030041d41000f05003078050700c0160003800701c200102d400900891105640051201c4010b003846a1060710034405040445840002d81e031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 301397742 1250 301396492 301396517
    0x4020d03080a150909031b05030909090715030507111c1107090603030503100f0f0311010201020903161703090f09060a0807030b24180c0706020424050f040510 70
    0x3c03c030005a005214059a03400080044c1a0046907540102600312007144880c10729a80da180c60f030050801c900c0c02544280b0106620a80600c40400501146624007880c1c2603042801000387c2007d84042c004166505100b400700100403c44107000c84c1442e0314a5000d0550744022580d1001c212210609405054400300b10314405d401100d0003075010759141501c0782440a01d80060140b2540007007007030401c41904201c0040d0258103001242d170001c0c400003480c00c40d800140e001e03200e10120b071507160086201e55081c50301da07411100d0944a0100700401c2c5400341c444902d54070b104002a09a0004422a074510a4a400506c0c5603001c00c000d0004500990740742669864500e8680088840e00d07140010003040d0846450f90441d0007075070625005041841e603011450b0b1407894441d2a0b5080905400241060450822590030b036900c075200710b42d5242d8031901c8005075081c06900000f00c20101c00c90b880c03064460011b9034240f601d032504880ca003e1919041015200a00c5902802d02c00d8407401907 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 301398992 1250 301397742 301397771
    0x50d09051215130c08010501030b0f04030806010e0d0602191b0507050603040804080f010c0318032102091c020307080102041a07020d0f081e0307020a030e060c01060305031c0504020d03080a 83
    0x13003008102480005c00e05504502c7c1170b4591140040c011103052103100c04001c007103075108903101d41003a13083c2407200100b400c04000c0f40c0f10ba2118078014100900000b00c145150507042c40540c66003556942d01c5d20803030310fa203005180d02140d403c805413266102e040c0601c40c07854000b000350703002889040260314290307031030017424100540c2201035421655140743d4849415010301490101040d1304032842c01687d132580e0041c00302030b80100281000003003041d2419411056504903100814001c1a002c60f00c0c0c0c40c1208800d0708031070800102d002c0e000c1d03940000703507811050003540c0c151000b014414014503981d141030741050f0032488060b68401180c400c80400b24001e240340c1c000c2c0398002e145a0303680d00c495040700c1078410310900715070a40703d20802c204a0804da0210f4001601a03241c0b504008141d100000030f0424020f280c04071a10f5442d08800104000c000002404009170b540c0761444007480707201a40c01105c00c00c480294114a8030304140d00024410000c0b140e0060303080c5c07000a8000100c0060 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 301400242 1250 301398992 301399013
    0xe070b0306040e12130f03030807052a0703020112050c09151e180a061e090b040914090303071704022701061407020a03030c0203030c010504050d0905121513 69
    0xd400380e4138800142e07440918102015800607081d603140c0840700c140746030b0340100307001001002e1a08008010401400ba01145289107222902203444030b200d81d648151510b464840c0d92208a011a5130405503400c0034a5500409202d480c0d4203103400d0a04c2d0707414040c08104d0110700302240c054581003196002403030701901d0b0442a003420844180e10b03182032102160580c00a064000e1269402c034104115495015048071030a410501c4408825038001c1c3c2c054941c0416a000400101e10204001c510030800b60b0003080f0031507500306007190940316040d585440344001c3e40c581e80080e5040d8034030f01d018110306550039007051024000041d0000c00060262910308101d10511400302e00388010000c480e030260b0001c00c80000c80c2030191602034180d00103546d01c9541d11008040c483e2101554042d0b640520544540b841048000e0100d46054a0425240d1242d5100c03e00403884074400818103081c18090b0b13211105980e8000c101d84030844d41c205400600007045c085e20140248001000503464540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 301401492 1250 301400242 301400263
    0x6091507050403141b0405040b04030e13020c010c23070201081801180203070906261906090605070f05030f100b04030602030f0708130f05010b09070c0203100e070b0306040e 76
    0x504000514a0003404d6031303c5031034094510647c200014800420041000140c00581c1070602c001e05520510124042e051306d64080b0011307a1000c21001d14501040d00511b411100715034a5451802490300b03a000300e902800c88502c14007100303010400065000d8001070f604641101d01c085120164030390201d081d103e6120503801a410901510740450404014100103803021120074000300d41403a0200c406903414400440b07000082c91500c8420070f00510078401500080092541d01032520b05103807001d8442f8038811120a482d001c00115400e214904101403e00b05654603455900c401d985c0c03003401c5034050206c4108001b101c1c00007a0041400000700000d40c80307404c3c0582c803031034409102c6100d01380080800007800f0b50103080001800c40e2484441d480c41d406007002600302d0150408500501030061506e030884198420f000384680c0000451030380e10310840446021440c0c45604005492644140aa9950001d08284507840824000d0742c1e220788041d20024900c980d0241691501700d4080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 301402742 1250 301401492 301401533
    0x305060d0215090111010b03250509010608150d0807080d0608070f080601053312010909020405070e030601091a04050a02221202010311090a0b03011706091507050403 73
    0x243d80000d41d40c10980001c00201060000c01042d608100465258288192030116400d045100c40c0070140034104030304040c01016001550b55071b103600c17001c0c061036001e90340c1d8080010080103841039454040300e0100400c2d8000345d6076040140c6030b0b5034205103030401e590104440d92607071008140003004010407401000c40f0319400e44040d1034044228148081030b000300f8060842000f1051341902c5003051074400102e00030041400c2800c201202c0554000c1300780381d0b500310360800000030381c4003c0e5030005030545000302c03400c02081c0c8aa00e000d45103c24180d40f0325400d50407000041125200035800702c1c0030070300d0329448a842c007a00c070700000d021184104c80b454080b540c08668400720050450701140121414450b0315810360401d810b038241c0308002c000c002d04040e104c44a40c0c01010340070b02940d000a0005d81038400f81922500c0100300c9401c240a43c0d03048544911f400c21040c0ea0009100d0702075840500a413296244030030301a10340388401010382044c417108000c00000070b804280c64018451190 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 301403992 1250 301402742 301402747
    0xa050607030c02060906011e0f0602030901090506091305220b010e10030503031f080109060915020909010302040b0103023c0a05031314010c030501030212010207050703030305060d0215 81
    0x40d10140c100c41d01c44824000719407100007001241800040e66505540600082c1c0001c0340002000340c07178038001034004484201201c038000400b00c3c0c00201802040c5400d03202c0f1951a52100700f401340b14000c000200340d03c01d07038200150f500848107a00144e00002c485a4007400080c2c0800d685665144c42c0500325441c0e030342c1c034004000f0740b03440f6204607130000764240d0b10300c90a82c03550f01c68030390300e0002600c0c4003107a4041c1040c03c51000c00301c0511700000c28214000380808406410460002c00c2104170070f40c2d00880c107158109116981d031080340c10341f01005244114590030343c0c007400002e141600943c0c2c140356080142c1c2e20700c1d00b5150060101c0f04030301d901e074201c03286658544c0c030a80403c0c289410f04501003417002d000c045401c08241c0354001c07000300351441c4500701410507019410305a140c08555518242c40511400d625402142c1038034000c1d14120700d5454181c1c0d1403801c07480f85010103071450f0403c1200303000092080c0c02040d08800003d003c602c2001c48c0c0d0b0001600900c081c640d500300103400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 301405242 1250 301403992 301404001
    0xd060303090f1502030f031e04081206010f02030d0b030c091602101a0103150b0a021b331306030b0f0a05031e01140f01051908121b0a0506 61
    0x89140b99009085003001a9100380003ca801035600e004a030144064898003000003120a0f04420801c1c07400990595115618142420010460b0380403015941c0303a20000d07000150954001c0300b22403501591640158640310307110300110b00400401c0401d59260003011188089540c031100c40c0d602543c0344850700796980c0d1410001071301d04642d104281d0000e505211122076104a4076440c5947c8400a00340030031494901498100f080910703400002c684d14012400405040c1d001034640c240c60040b408541030310008408001c3e0101510952070407001200b16681d1001e005617a4142c14140c9902059050242c480c031286100b801c00c5c1c02440011343c0e284504100c928007840d000c2008102924004115424840070070b44400c642d64402104894080035006222400d51018101019000340c6100c10f080c01010000912800e1145a01c190b400c030240c03001501d03000203d442100c141c10010140d8400fa450112450380100c4101c8900c0d00404241074424402441105425442030028141a180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 301406492 1250 301405242 301405259
    0x1603200a080f13120e030a032705150c12280806090f13050723010203040f09090305120f04020901171207020d120f120b010c170d06030309 61
    0x4020040b89a18040000b4018400c0342d2a060f40b003902d0304600303040c00411071290284d5250709040a12038041c458014a00149940400c24030700519000d801070b0b20850030b511003c0a1103180d4020194025072030002800ca040b490001003404140000032b030342c0c0b0b19080c50905121500515203070041400014400f21200c400490341c8442c120060520b030406082c081d000c00c4600c4001270814004202d0840030500c4800e20314074843c0100d03402411545580e441300141c40b5100c0107010340c40c40440440c0f040c08455800031042da01594001401c03040078900d04194880a018451816030511104002c2e80c005030701a1460641b046044c46107040c40e905092052000c2c00405070306c8141100008407844100302c10115800042d020101d0245032070b41800e00010301c403440d0318a8001d180e164241c60142509400403c0e102402c00151900741c100014548214282c45008010600290000325403400003619401962103c1c101c100700142060b140741512400c95103d43c1098003c501c0041d010404503c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 301407742 1250 301406492 301406507
    0xe0c13020c0d090311010c03092c060d031b08160308060a051f0513171c0203120c160506010f0515040e010303140d05160e0301090503031603200a 64
    0x309281000b20b41c1d00d517840300e6251585010340941000a0300d80e05c1007d0501c100011400742c850b1441807110baa00d0312446d14071100c0000030521403030500c90001403132442c000d00044c01a070341503200d4000d9140d003030100c107542a6610f03504590544040c00080c0346022080c20300711301d8a1094881034150304202c01040b240e404207500c0688160030524250091010b4a040740b203021200b401c0154a80f52042c10034180c02145130800000c0d448800090004604009040c8074600300740c1403a280f1500a020b4200e03128030270350141c0258811a0400301c0c190004c03001c01088160264000b04c031802e07070f182d43c0b1a4103251003a403101c1d2010080300018442841c0444c079807840400070029140c501880c1c4440904940740510000d403e210300f580040c203001d01c0b004101d8400c1514074038200709501d00900480c0c0c1d9014400c00307035000580103501540c500d00341449100c0d80c441c4c010008600710b0707940b403041d00040340c1c4501d451410542c659110f150720344000443e0110541d07800d6211500d51611210080114 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 301408992 1250 301407742 301407763
    0x3121e08060301140606040b0d09020310091704030c03030e1309032a0b06010c0503040909050318032409012009030607080705090402070602070525120b06040e0c13020c 74
    0x8214a045c8601592518102c03030898040d104001e07214600c00011341c005041345080607405029414640345021010390001d0340c96031203890090032068100b46107903014025408010036500744003c0a00c0802c2c040c0c940f81098440043ca0f0507910140180301d04d058036156003003240803c1600100d08240c1c06130b806045800c1411106c1c1c651056469195016040800341c001c605001c05000000300b401000d0080f03070058520140c042c044000d4a03e4410360fa50301c40b4088030a001d07400076210110f85000b04402a110380300c10341e28103054100c0040c007410184040e040f40c03181e40d070341d4a08850500b00c08a9003804240106da42d5038a074a000000d05040c0f0324001d100a080140784002c01c83c4850b0810241c5000200540d00141c94884a2400000034460060301174100e100d841d1600904400c4104403002e40d10b81c1e14132640301c040e915a40840503082840008088502d00e5002882c10304045d0f000200543c155800c44207407010440208858640e45c60301d0280c0c298001032890319440d020031011907003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 301410242 1250 301408992 301409021
    0xa05070b07031205060a12080a0801060309080a080a020d09030329090708040c1809050c0f060d050604021e030f01050109060e0d0611030c07020a08060403080103121e08060301 77
    0x400d800765800030044160003c594900070781e90070201d0b00c140c81c0c0030a078101070030000d0b14810345105203041804140d040a40b49500007060440041000340c842d020340780450350f0000c142c5061441046060310704000017403500c00300590900102040300320074000c203800140a52000100e1100c02c4045c000b49040107450a015030291200c450565116000c08a80c8102a803078000b65944035031a000c9401c1040f0380c0040700c2944400c0f10319110342c031160f02c0109490300c0350302180c0e1044055020702ca6400e00000c0030701d51052040c0320510101445411030f540c0803000520040c51b2042c1000404c0903002c000030200d107402004020002903540b141e44041c054102402c0c07000b0351502c3d003107005003418403c01d00c06000340140700c0752404201c0d59802030600b410305c0f44845c94807464100002030040d00300550603407003039405440000725140c1c0412801d0285070180d4550302a6804c540b00c0300103151840e408a020000805940703c818400c00b1518001c4054554544003e070031300740109800d490840d1100d050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 301411492 1250 301410242 301410247
    0x1212210b131803050703050c031902060f0103050607050a0908030a0c0209090c0d0204090f02030106140411040803040b22030f060b01051c15080601030b0a05070c1e150e0a05070b 78
    0xa4940c034400b8000b85807580351404036174072221131404a820703024541d40390f462880045072603c098905050810100a01c1780d01b1200075a54500e40b060480c80c00307102c098081d40044c8007080c126407007040100075809041c1807168500d41e580100500c0d6a0200307003c500011040c801c44001c501d030904080d030704582c0110042051521070400034400d81b0040e03030000c3c4600d5658600300708000b456202040083c0d0020000c01c206039989200c0b584a00303800b00120310480c0741c0510000c10700c1030360098a0a98204000035810b0a003484140030b415440a5848440315100040d1038640a00d5030075000301440c032030140040000c0d0540b1b48442941e140720002d5041c02014003113508180f080307040064909150200c0800c0c404e1a1001111416040b41c010a049005140c0084180105041f50320700034820a40100700b2555006821a811a4229030081c102100d0407401007600e80032845d0504541d00541c01a81c4400c0e41410351012200440040d241c4d40d000b414200e000e2040a101c810000c0810010b10341c07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 301412742 1250 301411492 301411511
    0x10f090b0d0b06011b05030304050f06061903080306010c08041e090204181e09061a090103020a0608091501120606150917010207050312090f071212210b13 68
    0x55580c0c42c001e226a0400402060f401d080c1c81508400d04252078200003036035901e082c41c1c200340313407550241034801d50356218440c042035040c204500c1c50207003c44140f0716480e034581180d0340c1c0c0e0740950001e06418100f0600e66907250201d8000c2c0f0042004018035000c00d0b21088988150a04521060b448610305071301c10f00042003417584e00c5400f4001c2601000c00061822040d0054074504040c0320708000070b01c3d14049101c0204403455104085160045171100c0c2e0b0100351508028482000b40002504480c0200042041034011140140c0102c80d07041034900c020403061041009103001d90250303103134a0803a41c015060128500c1140040d024074016481c4125950380003819003100c3d4441c070450720a007480d102540c403000b035045e204c4195010007940d6807521050074807020720310151040420b0b801400e1085c51101c0b00003a1901c211401d00300c1c00c071031034402034a68600800882502c0c605000404814210300180403480414041c155200010782c0102d1505000b18080c40440d10300c1034624204800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 301413992 1250 301412742 301412753
    0xa0c08010204032310051303030b04020f0a0f0e18010302120106081902030f03031510030b030a080c1c1e030e120703021005010909021201150e070207050603010f090b0d 74
    0x91340740f49a5408202c07550201c1c480c0386141c00004502d40381a6880c1c80184003070254600d5100c2d524030301969043c4000001c44003080100d10440001081c41c0c0d0040080d0b26945018428603820b00c000c60401c4203140541c074000c681c00c20740c020001686500e221005204502e064903c0004c0c05031400020045641031a0303500d5598030641c558035000c6600030340c0d00c070115a000c00236029009070003000d884d00da08000340c80e5855850f9810f10303e803180c00590320641055100f403007661440b0744001d0042509841c143c55101681c0e1004120a2081c000c58100482104c001d401050441045076200d0700310450030300350b602200d141400e03060708060401d52403000317480c0000781c007501080740c10410315690002458241d140040311a1403200c0e0504101c0001040d25540d840202c40034002d4a16000c1845402e03512801c8038040801c121800700304200c00c0c402007a00c1c2d24600c0d44039546004a903901615100042d4a82d0000d0384066441010300030300b0700c04401c241c000e0901100c0e003070300c843d1388a08203550760 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 301415242 1250 301413992 301414013
    0x1e0b1303200708010f0504050d08090d0516050109030816090302090402091509040807050633010509040e0105180304030314030a06030c0b0703022a0607140304080a0c0801020403 78
    0x109071026000070300c4070307103001414082c1d41e00038141540200003829081d25010041c10040750165514041c00c03540324640b500a81d8a944030351080d102401102081003030544071030b0010000c10201041448008000501c00d10806440ca4000d854228440c07800352200304003100080000800c208000c079003080107031036001e095504a0381c12281c0581d15516071502404400500013110752040c0e8200a000c103001285000f0301300b0900910684101e43d4807001241d00d58543e1450a400701e030300f0014034040071100300380350120a0405140c01c03880e0685150009094416080b00d0508030b0355180184a02e442c400300e0344001a402d0007001e5803d0526680b4080d01240a0454092a0341c200100107402c995403030b480709018540c41010007040585918180c59030790041c010803005441a12000c01541500c40c0d0b040445180c0070706102840301c400000e00c10650050342c070407903400242d4204c62003800414000340c0040d21100e0000d00300d60242c0d084c501c81c220421b074050855644100001e10106100002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 301416492 1250 301415242 301415267
    0x32406090a090b060910110706080f010501030b0103090611040801060509062119140607020106140616020a03060524010801060c0f02090a0b03160f03060c0c1e0b1303 73
    0x240003c03800c0c0348501007401445000e06480d80000903041002e5041d0b04500f41071071030507484007190181929041c058450314800d4510007081990380700100b05561103504204120300301072401003001d281c13954580c01a125a440c2c00124100041018419034400f40302e21401028100c441005070700b00400420074140d01c0070703410381205086079040052000200011542e0b00103030b400c030010150103410316581307442c1c000a04024078050350010440491050103100156504022811450002030080181c168803540075407d12070b4010110402681d80c100b040da00843c000e00000c02c81d03280071060b04610420400d090141c008c4a552100144c2e60300a101506651690030089240e140c2030030641d801c2c5150400080d400450401005070b4003600350000a8041000d40880d00540b05c15001440b2464071402074016943c489401040800d0380c40e002102100c400d81865603000b0b105807a040007099a80500c40301002003622100104003034901c03c1940300e46052018a400d10b210795000303044505108 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 301417742 1250 301416492 301416509
    0x6090513051501030e070b18120109020a06201c1107060e04050a02120a2f18040605130b030c0f0315070302190201050412030c14071106032406090a 65
    0x16817654510404100807030103403500030f00458030b80161035440c0180307161040c2001e0251401002411442c041405040c0030340e0b40c001c0c0708280c0da42c2031800480b407608000818200e122030400302c039500d80f24240040c441480403949580c00c24095406c001e00b00c00b0205244069650052008100541d40280c1082c6400800c550102e02d0303071139140b0f8020190003406010902d000300d0000b40030003004943e00015441c000c00740413140710500c00d24500c0c140c44501c1010355002c00300b048050031030489070f29490b14100005200207030b031503101c3c80401c405a0702001001e8142d0781d01c4540303d50b146001c014030880c5607011255000c1d050030300e5010940b15125070000d28420780c0c1c004c000c240100e010f5015124504c240480cc5c011816440340c000340603050644060b0707080ba0111402c400c81c3e40c400d014404801c01c051700c4000204148c1c03680036103543e2000741c05540300552400e0000340c4c2d03030310000214003810b1500440f0601144245012440c14061703510548941c50400c9500b034903854142d0304400711420758 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 301418992 1250 301417742 301417751
    0x1060e010302040902041223031605010608030705030c12070305040902090310111b12040302190e0109020306190305070506070206040305010c0c03110f0c090c0d060609051305150103 80
    0x20050380603014603000b10880d140080b80126014003031a889070751030340c002d90404542c0d242108104520b100805880f5000c0d4004200c0c0c402c0916040544208040c03081c000002e980e55103641a904642185e036084806030000103005100c2c40081090041605401008a10389485950301030b125100380d120b004079041c0c002c0303200d010550303050081c0f01100912040070b01580d000c442c03e0000540c00200b8500b5000c0100041e8107084600044204a00c51035000d1a45014107540070003602c9040b81141c040c0703029091134085440058458914001d0600c2280940c40742010400c00215400350a070001079002c23100c80410210350009020000c03514207840c00c80e610003c1c1e001050f228071890b000a0415800d00880180381e90b80959405005c502030361321100e00c029134a03c1c007a1684a0a9450780d0164400b0102c0c500c103242c04102c154011185a40a9180c020040424010b0b251700740d21000c0801e8800030b003004107040c030444200c2c410804207070404c054585521811417105210003030303e0405545 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 301420242 1250 301418992 301419017
    0xb030a0605041104051501180f031113090b010303080708040f0b07050903030f0a09050901240e1020010903120509070314030706110a080403030e0709090f0b0705120106 74
    0x3c0300b0b4040c03151030f0301420502091034400f921401840040308442e0014401402d00c580c2006004154020360780059900b610b014910303210701510301c2945020a50000c40f6581a54007441940309401c100c600c17565001250b580b45040103480c994004043c10306000c0c0300820800050584016440307040e5000c00594140d8803080e4084456000300005d8641502c00000d002c80181429000342030480c0c3c2903503408100d66285c0c02884517000080c8180c190902c481c3c03000392054188410000012030140ca00303080381400301400109030006907000d8a010607010941107490700f80340005c2d0300b00441e0080003070041d201280e8004040200900c1d04559199940002c9910b0764428040000196003100c0d02e080b034444505041500c2c1e07440f001003202d1480c0781c210183e4070428800c082e9251041d2a40b54a481c0e0f542e1928184c02411031444030030410700401c00b0101e0400d039244a2520040d0003031540a00c012028070b004902e0540c0900a1003c0c800b0a000d41c030805840250000d040d00e00b2481d160103081e00703 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 301421492 1250 301420242 301420253
    0xb060a090614010c032a051605060a031112040f03030c0302191b080c1006140a05190e07020132130309080601090e010c08010605030c0c0a02061603120b030a060504 72
    0x146000c1d541b007444600c4000c0311844585880c09a0240140305650101c018041d04054210040c0310b407542148007886034046481c02540035018120344004c5141c505024800001c0156204440c00c075611030880d0070344424540d040c883c24142c282c19060841c5071000102406420311000f10b1520304012903c0d249292a0551200c0464010b900400d4161101143c0c00c0303072a29a00c044081500071403410000081070b44000c1c500307100e2f0071005020b18078450b0501041c0401d060f4550681c90080103000c10000b07402c013004074514482c0f80207030300000c1e6a2000781c40c08108070184402c410030240b0095204024040004e460301d0700169600c1000c0402009843e050f41c3d40c40c002c0c2c0c1f00304924001e5000004400d441508906010407030380008015160329064140d550104c02c0c090840000c205000040c2c0000604000300001d01900742100c02c4038900d40d0000b089a80541e200c10f480d100740c0c078948801c1607040440014014402d9800380150003070000400d81c1c03100d030030001138402500c5001103800d000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 301422742 1250 301421492 301421507
    0x20090c070f1a0708090d080c09190b0a09060309020618030a06060303031b0c0c09020f070602040f05041103010305150604091202061f050d200306040b060a090614010c03 74
    0x2540100c100c0803802c402000a050028101d5030f9601140c43c40300040c20b8907601181d200c4100d000741e106c0401e0358880c66505c144a8001c003a0003500b241d05101c4008200c07000d040380c44024640780021a6454203a094024042411980600f00b49030400b82800c0069803080300ba03804402e1b070702d54241c03010350b80c040020f890a564501e003d004285400c02c08001c2c554181c01c50074001000380d07030f103c0d00382058000c1121070315800e00c00070b0b1014410140900c065400d980040c490307020400701d42c50410b5403d441c2c641c00c80c0d2103a40001140703c8441000c0000d420107000301d1542c080e0481c0024110340c0745441d03094079955261542172115240700c001504940da20390201c0c240c02c0e007181651000f140744031401b03540d0340c00030f844400ca42d20410000c003480c0440f10718004282e1320040e200c2c030341400c2e16a465010107000c1c05198003c458600080100d1600c08001842c070550241d06030702000c2c1003440502040781404c6d00904011418010240070301c43e21710001ca4540034003817030a500640c1e45818103c8020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 301423992 1250 301422742 301422773
    0x4080307080708120405060a060510020a021002071d090105070c020315070918020306010e03190b06030a050f03030a200301030f020406051302090112091205210a0920090c07 76
    0x4c1c0c1669003800180303c000254640700320b00c0003004001d60b40d00d5800300300340c6000113a552401a40480003c50040c1005024070203001b83c030340125204a0303210b43e0070341c0c02d2030340001c166a20115070004008182500340130341500050f2908001200341240d0300480c0d16001141a501d4014032600c0c08101c5440c0701d00d002070010108114200348a001d0040114042d42c400e8a00c40d00140d1628646421031401140324040c03a4290310038803404004540d42c2026048000b88070399414010b020407600413031002d00ca6642c0e240075000145540f0704c0d0a030342e001c0848c1ea00c070060b015a01c80d49008031000c0d215410459065a070450b03040c01c0026a18400100a81203640186030014001c00340003568000603000707490500800d0300e03a000940070041e809400c48030000301c084c0408802e40c1e05032110f0360140c0b00800c1c031641c1140c1c804524540080810304524003e860101d600d0740e81c0c40054082c0901d81c401640411400018090016403001c000341d070104004d00300411071540042d0300c0c420030984080341d0303144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 301425242 1250 301423992 301424017
    0x60f0506121b0412030201290d0809061201080f01201c0f0507120b090103020d0c0e07170c0c0a03120204030515010503070b0f0708092b12030204080307080708 70
    0xc0e151901d94607103903d00c4d40c00b001c4006d90308018940e54400e5036542400940c600303404400d1007046003c010404004c90108095620500400c030f800c840b52a600000c01d000303809203c12001c41e51500150528060404094401e036916010308d0340f10b4600300710300001c0c880c0200c401305500c401400003a540c242203a90b10100140b8a00b5270329582d4258541c101da4403c0040f074685800c0380c0d02c41c941d20829204000c1e9019800031f102e200600051400402046286003d8a400154a40c40c1c0e800340301980800d581d0345010542d4003901c0711704000040316a507402000b80d400e1908044060070a1549d603002000c1c01820320043e00c00014003c035143c2e064400031b60b003001c01c440010000610128003e0350a000c1d0078043e0042040c04102c011784807040700d10b8045401507c0d803a2050316212034034160880a0102d40c010b60b8200701d41810f0302101640c402d9403000001c4c1d1407030b07503001e4540a241d1644560007501850700510007000134110100a480c8000e0700481c8096488030745d07142c0490588641d1108400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 301426492 1250 301425242 301425247
    0xd121409131e0606081b070b0c0c0d0509100e0301150b090a210f06020f040612050f0c0d0f0e060403050c010c03020f0f070303060e070203070303060f0506121b 70
    0x10403403a508280c0c814001c1142d071001d40d04090142c00d082e108640035a401041280740415890003d110381e4207100000c0c20041c90a10700f00d5520040c5c5000192040d03c81600003003600d4100e0b082c14130211984c0411410500d24142e480c0004c190811050302c0300c6000c0c0210036441c91030a440071340103d8600702408010945098403105c120b138803500100c0032a030241030400008a41402030883d01d840c1c04c560300b0401242032200e44d0300c405c04e5000040d4201c61282e000e2114000c203c0440340504090441901c6801c010121346049108445008200c0352002e00302d0f02c28400c0c40c091100494082d0902900d010425505090982d4090309a440307010b01684a000300308018168008042d201e10400080240b008ac0343c405402c4044e400f6070303900050049001c01880121200400040100301d2090402103079455490810508030401254070750090f8000041d4041010f83c1442080e0140c01e00244c156401070800f40800c1041c004c0701034042864951702d001c141380c801021980170740388a00d401403e5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 301427742 1250 301426492 301426519
    0x20310020a03060806101d18060f0403271707050a0b070b10081e1606120c1e0302250309030c08031905030709050d0807020a050d121409 60
    0x7002071815110b548480d00940c00822070214021011204075041f050713440700f900a42c0c070781581c0c15645c0505045800e00c03c0c103404588844d014068248034212084114140e4036217410f020b49038503686940b020300034005400b8040201740d0000d0800540b9810545120514101b184982c0782c20402e41005a00010880000601010340c00c014100544a03c40e0034401e9141c643c0741d8907011030036000d0444680c01081d162150100c5c42090500c0d04015230044409070040744440506121301a00314100083c40180a50690f0002e4000e5210006442c684640e55914041d1000c0320000c80349000002c05400150740485031140090007031500c111507450455100680c034000d0100401d0b0f200889880d0740c07050000503614000300c01d40d040400c03401c20a0f00a800303440340071140c0d68401005142480141100440d45444000e44a404580b20740302d4203a950f4480d004000c908070740c1d688064443e44504c1c030322400054014900c1000601d5a05148052088540c8100d04c1c9001780e400b92900a1200342450 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 301428992 1250 301427742 301427747
    0xc0d0e0a080304020f090403211407021b0d0b130602040302030601060f180302010f140d02071b0806190b03071512051008030a140d02070507080106050f0d060504020310020a 76
    0x198000c44c400c07101882000800300c2403000400c000c6402070082a2441c8022104602c244d03000107031103042c1c2d440002e101c1e01400f03041180341d81c1a41c103c00168030072401185080e803c103500c0d05842c01e085810201208240e602c4119508000b40308150701e15120030707814100086501aa0051540203055402c25a102c8400a0805411050400000f14048020b0005031584900e0a050300d0b010380d070b140c140001c42c201c1600c102c401200801940c0b40c1c200a20b8401701c18510181c0102481a00c3d40340e03140b04043c0180094a40c2d98110f01d1142d0030000034010700d4094441d003d403000b18096008181e0304210030000f42490103a901c403a91081d11114a101c01550011a1031a2510110420003051321481c0304081100c180d030240c440e9a500c100704d10680c0318021a143c4110982c1e01c00c09614012030384805505907008040c04aa8540c0410024030120b00b0038041c59004c0c20007034444801c10341a82c40007070961450041c0140c19141c0d5400840c0c103545050029174007171030148000759650080007000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 301430242 1250 301428992 301428997
    0x50c03151509010608010302040e15070c02031506030d12110414131b032408010c110109020a0506070f2f010305060306060f06040e0c03010f0611060c0d0e0a08 70
    0x7500842030040000e801c541c5070600b00c150580d800740c3d0707982010b682941d007408001c0800544200c0584200c0c00412490020030041500c6160070760341c3d9040c46046071061602c0d018101c8014841c4500b910104980307600d00040c00098082e0320f00d4444c03a00116289a04001c00300c41060039400d0b4400200410381c042c0801c0c3c108550030094801d42194903800d0161021130f40d42c15102141c4c000030304009403629200c0c0d00003070302914040c4015403c00340800c801c403809000d03d86c4111416516803c507032284d20b400c203080e50081d0944500138090b08106900007050140c15010f1070344111004a0803009108003041500d04181c0d110131109800d030300c028012100300000091b030404000910034051407a511900401d4005d010180082019480c1d20b020807c0e111480703080b0300e410040511000030600e03061101e0601951a0740d80c0740c0c0e070303c0d410104d840b80440c069810507400d0007100c21010a0841d0300284190384000b800b08a0740d1528031b1002c10030041c014142c4260340520840c0295414010034600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 301431492 1250 301430242 301430251
    0x1a0c0a0b06060f030a06031e0b0c03060a0806010801090b0108120f2104061a060f040308180603130c060503130605090c0406080c030d09150c02030109060c030c1103190c050c0315 78
    0xc1402140030300c841e100e80b03548e80161005102490a0000c9100709140c0009950030880c014180e074503458440d2501b500c1c16000360300452f0160344503170038841405198460b00f4054850079002c0e240d16080c0c0740d424a01480740e00d54a0607188030004112005450b0480d000004040901c10400c0c0c50070f00382481c3e0090804c240041c602043c0030003c1c2400c501d003140441c2c160082c0c11802c541860300d192160b541c19000941000300503000c500b02040f0035941d12000754410840c4018516034030255080513485044990016020300c01d080062012100341030b9641200d1690140020807541d40300da4016051640c111400703a0081d0401c42e02060450020601c8481e100d0141d0858914000c0424116034883d403e1017814503240c0e00800b40001144207900c00d20b0341e140094000306400000f0351301d040c01c440d401e00d240c00000390313100d05000c81c103544903001040b245c582800460030021080d0036007840610466042090041c801c034803e0410200740090644201e0003015500305510003051070411307100494 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 301432742 1250 301431492 301431503
    0x5070b0711060a1a0d060b060a05070501060b071e0204110309010c0e0a0b1605071d01150e010206062106090c090a090506131110091a0c0a0b06060f030a0603 69
    0x40000f207181c510b0344280324003000078085600040740700030184607482c0d01a03201a90324945901c6c0301c0baa5511548020f08072825a5500c1d503a0310300c02811b080f401c4400b40e8000c0503501c1400c00156001c58503020000c20b0303100e9002c0329208801d01620008004000305502d8980d062404000c1003203440301980000729000c42600e80e50000402801040100340b6035002c1c0741c500041c14403810000c070010b04460308429200b04121070541d51a4000b4144802c008050340c00d40c80c40610051120200008552280d0815414801e92803c8494000f07900c8001c0100240d026140da40c48401d48011100396144013419458255281810300c1d08800e13407603152050105002e0044080481c8201401d8810184003a400202800668854040403c40c411f80c800003076644142c4610120b02c41c3d6a0b070b120408071046a5111049200e15080440e00d00c3d0b40104102c101c8144140060302c040c01021440134185c80e0b000c506250f050f600c01d00003034080d0041c14031505020300c2c00700c00c02051590b207601c0b0740c003a01e0160 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 301433992 1250 301432742 301432753
    0x2090117061309032705010e09070905060a210c08070908061911130e010504090f120315080d0207050405091504020406090905061509131205070b0711 66
    0x161450200458107403600c5821054420740711441842d180d10070718006201e07142c449034800c10605003450168404007100c4582c82184070401056801030b40c0c0b6202d2140c02e5900381418074003100d000e03124000c0c0e0b2207418081c500c000313410040f0030b00c221100169a240d01c8001d1116003d280e0002000340401212980811144004908072a0107034840c01c0440d1011001803503180c0c0c64807240030590080041140705291140d243e040b586541002803c0300380c03036800d00c4800552404010a0010070180c0c0040d008a142c42c0c0c2480225420009500c40550094030004900c0790301e11088005007040c803810100c01e000250082404040403640460800c04c907408c40700b00d0798540b002c0204940041c0c8070800e00d070784a0180709941c0c03640500050740c0f00780002c0c00001e845903074070754103c240d44614000b10f4180d0400c01c104240e00e9031361105801d204401f0b84042903149442280c0c0820f001e0410301c05805848104009003100d03114004035024264058032444e01030030840c0000c3c0060360421045002030080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 301435242 1250 301433992 301434017
    0xa1707080601030b15041e020a020c011107090b06041a0a030f1506081008030c0706020601150504051504080d050304060b030105160f02030d020f070512030603060a0b030102070b040501020901 84
    0x500c00b8182c07900f0084803043c41c0c035010900c0001024030b800e144d4100c0e4a40071058201c8051010b034122517246500c025036200c10425000341802803000c41b440c18000b0350045180c11100015040741a11031001c8009415490b900004699000d194801c0070b100c510003030f0074011603440300f0190900100e981c40501c44559402c810310241c4080c1003010f000445078a2003000b000d440b6503080ea40203c070f0420890303035072606d80303280c64210350080d007019005500c135403800c1000990420050f801454103e146802840d58240f004005100303038450b5a20072000b4222480c8041d20380030450b4002c044685c200c50f03048100c45005007660b081190143c451600c0c1c212019041d0606001d85442503c001e00200c2044800040540342c2010f000401001c600c400c3c401c02c1d408003128030050010140c586a020348550403072070018034080d0300c09d40104c030a070014402d0290b941c41c0001d446070448030101000c82c6c607911031000f10740280074508000c1c04e9407002100780f105100042d4010302d840002a80c46070032031040d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 301436492 1250 301435242 301435259
    0x40c030c060f080402060714010f0222080a0b060111010905060402090a140f0a021201080601031407031109070e0d030f080105101403040501090b01141003050105030d18050a1707 78
    0x45018582c00450151000034006152240c01018040d20030b0413481450785000d51401c1c00c68001c1b20404a54aa0000d880c1c81411032100201c0708408005800c43c0c0c9660811441c5501da050014001344113101940110745281e015405280342803d0100003001500072070700b8000e03510402070780c0070303030207544000040303400b02c0d680707010340c1c0c0d031200d0f007008130542035141c01c107009007845002080024a80e03070912481007485019030f003443c024000b090040283d5419820007a001001c813152030205680408010800642400c485d03403030200041740d41400650380d00c1421703036080c50521103050307000407481908002c040d0401c040d415142c0720f581c2e032902c0a070388401c240405140000e4102c000310301840b0300340e15951030001c02943d00c14031400001c1804d21440d511401d592100380c128104404c040110001c26050050003110410090315040c00b181d490500070035128a0285428030410030f0341c81170084130b10b03007106400c00244009408100356030354030510f500d06d485180d5440a0f4a000c0e01e0030008005c0d5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 301437742 1250 301436492 301436507
    0xb06011412011d1e07022410050405130b04082110050114071704050a0315050601020615190b04060923060a080a0f05160e0102010c020607050a05040e040c030c06 71
    0x12a009805800401a10240f1307480c000602000452080301440641390084101c032072580500314040034094109082d11000f942402e40105010702e1a0004010540200d60342410701c8030381007006c02c000c0e504e132824023400c00d1050074040011401d0340c0da40018152411b0302c41c1ca00c2401c0307a1914441d519190801162130070325100c0c20f400c56410501034800458044100f003803041010040a030328250391000850707500c003910f9106030b5069800e404400e000300040d0140a034880720901c0030b02480c1c80c0c141080300c141e65113409050b00034500482e210b501d0062000b0b40101400381c50406075200d03640d542000706043e4260007032001a84030245459042072607100c0c3d2001d0a440241a581800020901215140d20040203060400d864580e8141c01807598800e05000d0380d848500d640c44403152580140c5001401b10006045a142c00156000390341d01007061a0031076214075080e80d030780d42c081d9000c5413280219000340702d96284200611080107466400c00c0200d0f4450081c030110190303140000d80f03284 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 301438848 1106 301437742 301437751
    0xf031203012d06030c210501290405091f06050d050c090907030b03070e010f06080c0f0d09060e06040f0b060411070b06011412011d 58
    0x184035404200102c1d0000290b20305a038044038002d80c4112050b84220b000b05a03541101e040114410301c0b031454003d080301c2018580d60481c2e8240d800410342071141910f45241c8204189100150034285111101c004006070308041c6000244044400020710094031140801d107140194010b203103940c0080c04041ea2019242c6540c240341d10110390010303200381809a0103000d9504986d442d00482903101c040c0d440d01050108098012a00e0885141c100f156980d0880380040f0f1140112544070080b1415035032181e0aa0b01c43d00ca13080032602c40c403c59484641c000700300c0710b545c2110030740010030a648109130000300102c3c48a0b0f40381c2451030035281251881c44202001c0244009185202d030000b4003100c0c10481068120300700c0e01d49205200005105580e980c00140da140c1c041c00032060010301c42003030b1a17500c1621855000307032030500340100c07180c1c0d84002c2c100074000645589002d00c00c = true := by decide +kernel

theorem cover : BRFrame.Cov 301258992 301438848 := by
  have h0 := BRFrame.cov_init 301258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 301258992 ≤ n) (h2 : n < 301438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
