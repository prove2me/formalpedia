-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0710
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:16:33.415685+00:00
-- url     : https://prove2.me/submissions/d7c4f25a-e7db-4f13-a9ae-63304cd0fafa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 127517985 ≤ n < 127697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 127519235 1250 127517985 127518007
    0x12010b2107090c09180908030114031c02010504020a06020a0c06120b040e030a0f180b2512080601030c0e0f0a08150604060506040b0405010513120f05240103020402 72
    0x100c0001050302c90300501c003500c64900c004050301d000d0300034404420340c0c000d01000091240c0c4100201035a014040c1407441e4244100a0311a500c1941c240d80c2c184541075030741d0003211101800b0250008980c001062500b014810000b0b0540150010300c1154004d0100d10702050700115450704540d85400d00c04502004168140c001c0d02e40394268a4015007014110a482e0a001004004500c660790b030b0b440441101c00300848004001009032510418007400030312604ca0503800030212b010650420855014038441c110192200f258010f48a4842545074044415005080a580300c0800d01c1c08210202c0c1083e009402060700b40c00c45809040801c4840c029905c80311071400150003040b040f2003850001e41c00030461480b045070068021818020002428200001902c1c103070380308026040c1c241070905004444d550400821207034100809240020034902030301410a1841c05401444415015030400602c2d18600e0840e41c0340900650000b2080502c009083c0c2e030640350304550140e5980301000d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 127520485 1250 127519235 127519243
    0x30c1e0402070303090b0906010306060f180e0a0b0c0a1d0916110109050309030106050f01020303040b0c07060c050304050c090105150c010f06080304060e0901260a0503030a0b12010b21 81
    0x20042c1200c1d104011f2220405000a20604903440f500d018021680c958000e110515054032030108003240d095140e00c1c1281c2142c002c0d06040c002e1400301c484081003512031104901c426500103071040c04c00105401d07465401699940381e500900d0134451104840300105078410390040003805041d9028a0201903c2c3c03042104c020b205854030b0003440f0310809410190344039400115110322070740c6032410000740703400c0948400c818100141c001d1410b660301c40e10350804441000b059142c40800401540c00080c8562007580f1882c15551b59182d00c2e07141c2454030350703d802c01c4004c0c1144951050401004695107842040045c030041c221441d407629010038070b02d0b01500110003001c0d215406d210021442c2d0310000082c00856005644001c411903840051200685082c00381030a2020651041c01d034540c1e1090f100e0345d00c81144421108050803e884c0d507030441c2c000b510300700d86c1c95480706060b0360b0b00e10741030300210b42d92032004c4000c0268100c030100094000900500c0341100d01c0b4002a0102c3d0403000384 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 127521735 1250 127520485 127520501
    0x902040b03032a0a0f08030c1309090b0f0103080a030b01020309040212090709200304240203012d06110a0c030503030a0501080c010f03021608120402030c1e0402070303 74
    0x14080740e40310545402c89004801c11400082000c0d860601e040b601c0220000c0e048404ca90003d600d100507100a485176809988000c100f00d05529040007203a200c0c40e05014002d00070800d01c0c8000a0844071441d141964281c06400318460501d071200600200c1da9190131130b04400d0aa08000514424003030050303095000300e5400c0d41d4820301c0895140110900040114801e10b110b0003950350301c0c2d8440047e0300455507200000404520441d43c0000304492200045030003600030341e504004180e004042d014507280f900c15602c0c056030040010844907a40d0009030940b0003002c02c8032200002ca954258124500f203215120400011031880704100d9010b1040e03c200d00d030462102804c864903424402d40d40d80c0142c0d8220700361841e04000244001000c9410200300c2416501c0c4403281b002c80c00c0c110080e4100004584012410581c035400141e502c0b001840f01d0071480b04200310a00c4c25004150428000c034115602410520000d10040c0a1001c0100c907842030403100107840e800306003000c500800c445 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 127522985 1250 127521735 127521739
    0xc040e1e0303010906150804060b060405040e0d0305010b04031a0406271506080613050f0106090e010c0302090a060305090705090901050612010b060906031b0a0504061403070c060902040b 82
    0x603052415000c00400150305990700001d007030100e10b03614607000380300d194a4194000007444800200d80014110780007548403030001044203007801c1d00c9400050865003c80101e005d81c0c0e108201c0f41110365094080c643c01031000040031400d01c0c0c61a01e490708018400c4884240a400403c006010050036510001c00449a0b0b90041030001c00100414000c061507482034442d91084112000c00d55450300854060712181c1d07020300300c1501c070054000800c2d103c850342110240920b507000c0c02c90b100c003440384034000c0140325804140d0340c8103420940d007141c012521000c1014010400d0604c01e40700c10f0304440803681c151400142c81d42e41d0008050034041960055a0700c46410018050707840b0054109074003401088035a520001902040700c1d080f103000e180240c2d0428001c0c40558140d00c1e09802555028042d011008010030010740d194116134410940b5002144002c142400b0041c0d0082801140780b031403413621445e509100b24041c12000441c0e90003054140c507960301c88215251a08444018080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 127524235 1250 127522985 127523023
    0x317040803040f0f05040506060405040207030c05010509010614040e0607050d020712080a0f090c140406050a081c02060106020a060903050c060403200a080d020c15040f1a06030c040e 80
    0x3141d0094800c00b01c00e1098400441324071001042c00c0c9000d200b214041d0ba8014101c1d40b6003860a410302c4042e4001e15800d0302400a41018040400c0003030055600c036594020000418504110012007158100700940c1c1c02140b800030380300034011000a00c10707000030550a0081c1ca0b40241d0704000c01a205d02c0100510640c2203950040c00c480e082043c150103400704610a200f0418220903070411203182c01d40c0130b0039400740c9000403c1030b44249662003810f80700150020a9080d100c10115406541943c401d2010b82d02165040c40242010705110b841060244054030300c5500d0101c0003556881c05840c050a881c1d5038240d103c08040c040e000326000d040303029040e2110703441c25040c003401c2540381a03003000c00041a502241c07007240c0c012039809580e9a12181480c14044241c1d9118020f4103c507004850030311402041c201264440516a0303c40d92181c608801001501c1c0f61000860200740b4000340312171200c41c20b0104c0c69802003002c2e001031a054070005074030200c210041d464032041c0c41c01c6404d0212 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 127525485 1250 127524235 127524239
    0xc0303131e0803010f081f0b040b1e090906160f031d0a060b060f1c0603020a030605090106150507023f0c0f130e01021c0f060b0f04031704080304 64
    0x514101440c1219052690500b100d680c03120685d445002c4040c2c611f181d00040c0100400c0c896441d03001c84900c900103031002695055001c003081d803c09501c84c188265108a2204603001d140140300154050110f030090b101a0030120810841c01802d0b1006009000001410107100361103903100c1219949140c441d010220841803c05449841c00c0b041912442e003040c007843d601e03013408412254142441c84000c1c0c40c0141029031800c807400300b40401c5a00319201c0c200000940d80760340b448005140551400156410b00307000843c00c5500e2035100181070260400c1c82080e180d0000280e410260301075407009480300c1510b80c030303d406a820032900b5400b00b05002025241c0700500c1c0c920140080301600701e8140810702700400c41d80034040c04000c3da0029a00d62201c243c261960010014a03540c00005800d21800700306e01403204540e020070340581c076030300c00480c3c0600c201401208028180502a6464000e00d00c501d801244a0f901000c4c0c003a41c41d030040102131401403400c403001090f295050700d81742c507 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 127526735 1250 127525485 127525493
    0xf190e062109030a0e090402030a06050f070e0406030201120b04090c17070e010509060d0804090f020c0d0e0303160f0b0a0903110102090a06030504030c021f11030c0303131e 76
    0x3508000c801c4140700440000b980b003820020403035041d5002c1c0c0d2075191200140c01d00300100703001d00400490705405101401c0002610a0082900460484122400900e480c0000400110405072400d1065040810800160b6085107201d495180003050100390a141540801c01a2481542c01880980004800114201079042042041c500e034001d562a141c0d441003290740900007801041d61206040d40400c02c1071070003c603134005040c858127042d42030907902c02c41c00d0101c804465035036107860740001c5c170000c2070082440891508009410808036074400000405d0b568003607000681d8004886107481c2d010b00c010b04113549950b680c003801d080e03124603015407040702070050711100300e021840c201c180a82c0110107000760b40e1550301c09080302c440b0518200c812009000c000e003040d010310240620784000350700d641d55042e034110b024410303102000301e800c1001881020070a074034520b160400d01c4800c807040c07800b10403250003ca6022542009000b40e042615081d00316040c0034034002481030001c0200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 127527985 1250 127526735 127526767
    0x1e0d0b0c0406020c0103230612030c160608100b03060d0501020f090306341209031808011503080306120312060102150103030507121101111e0f190e06 66
    0xa42d5003a4296074108814400540948507006941e80c2d24084c481b820071800e40d1440c81090340840018034248001191400301c900f142c1c000020000180c102c4030106000400d18144000104094500700d82c0602c0c00b5410b030494504e482c0140701c1c695030f00101080302c40c0c1d03c640e180b0b104150414001c40d40d4040d024030398600c41e0f200e000c00c00c1c001c0c06200005100b80c003440d44110412030081100680d20611050a21500c0188094581c2071201040c81c26014032200d10134111704a10944407c2c0d0b654180c2600d01501c100c20b40c0c000c40c51a0b041c201261010a101007580044aa00c1454a601d070384440d00025500048480da500c05031001040070403092000e01c2d401e50288200f030f000e803000f2200003e4a1000c0340d509020260202e403080180300c1c0018061498040c1a2510b0310b0106104001400c805003550350b800341051400b40085000c0e0480c401c0c030307100c5003a011540303149a481d0015404c0041000d000d810840144461035a0001d0411805416008038590004011541c0e03180302c04203800344 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 127529235 1250 127527985 127527989
    0x7050303041202180601051204050313061110020a0504060e0a09020a090911030103030c080a03110309100b0906100809031612030e0d08010510090305010908030718051e0d0b0c04 78
    0x20421301c520001300c8000c8031404030f1740034034810b075160351134000c03a19920010140043d000300d42c20304c002c020240c00d00c80a07500080191889585405424010401e03a40c501a081060086071500c104484403410350010221412240c090905c0d56806a6020004040c1d20896110398501d40c00000d00040c4994004400000d90f512083c0c20020454000d1081e00e65003c01d000050115030804490008208c2ca00043c0049130801e15000c41d0500d142c610b0384c0c455420540c1c0b0070304140d02c128440e00f80181a4095900721100940d2400081d03d82440001d075018040d0034924103000070900800c89124060084801280926000207602c0a031845c21101c040742c145e61f5103001a207004a050040306001c510008601c20940d00d812081c1d007000b04000310034451607099818016040c0d40040003030002c0c001c40b1402c501030321031680c1b02c1c03a0000c005061003801c80300080d00081c0802c01408a1b5851240700801200d0703519a1034161484400401e141e551010310250843d2003541c1000741080f003103001002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 127530485 1250 127529235 127529239
    0xd0f0b1302090102030301050103110d091101020c0108061c03111b1509010c140307060e030a02060f070504063009060c1b0b0403020307020d0507030201081018090507050303041202 79
    0x1403419096010200d0041c0c0d080c141c01a00300308010401507109400c902c03403402a101216241c240c142c0031110454410400c111440c09100c0304003005981c040c04860018102802d00301800d2424400198407900d81200c0c01030f4055040040ca4285845071340e4031980141114201c880035080401e61101b8110142c4003288900c041910450042da011010f0f18090728040c0c58450514005036216131400003d0f400d170312402c0c80f09021032004691540100034904c4c49000107181c1c8c030012150005e00701705d40140303022002a499000d1000c110740c49000c8804039522850a44507549250b00302d60004a803000d0a2004554013415540209400340e11090450784034400811800c5820348050b1408104000d1b10003203032219001140c0403c0704800010360261081c030541c1d2030150540e000410b80801c021050740d140d400350005104650b00070034030b0390300183300b0545d0704102850b02c903207010400f03d6002d00c50070b440e8490240c4030800c0340400c0307000302a000003400e80340c80d280c842046022121161000364 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 127531735 1250 127530485 127530499
    0xf07140c041104050108060f0f040908031021141603120e0a120807050c09010b070606050612010909050f030a050c07121a04031202030403031b02010b0f0d0204020d0f0b 74
    0x91802da22100855085400c103131560071003940c6070010420b2031500741d00341c40c1e001100280204807980d650310410100318402e40e0078a449050641c0728100c0f00856800070103062410340384500e4041d92142c00611202d60041051a44070040150103091081e81e05100d03048040000001c01000104810b094000a850742c4008101502004100e800710003403040301080b0552000721004030300f15500801e142409902203c801c1d0561001185d86440241e000004c079010105000041100c240500d10040004403101c81c01c158008480783d9201d4411f100d20300d041030f541c280280401c0b03410701c040203a80329150207030790716580786041c080c11552000110744402d015140c0007290080c0116202d20000d500204180004104000c100281000c003420a4040c85050a100d4204890310b00007148101e20940d0302056015154010111404c0f00c2c4080c1c0c0c0079641001c03d0b400050303e0300c1d04100080030040f2145040c080150021a0080c45803d40310711026042115408450340541c0126417100015150343c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 127532985 1250 127531735 127531751
    0x3020a030c020d1e03060506070507170109170a121401140a180c021006090906061706070e04090b0406060503070b252a1e080709020f07140c04 63
    0x3207844036040200d66000c107a40c054a058400400c0c1654010104d80f410300255241d1502e00140582d00102c00845240c1e000c01428407a0b9270032080341c1e08070321141000911032002240d85107000012000008406400c01080300d121240c803400e035010074600c20440400240070940d2000c2e0710703030200b401501089001030031402541c0c1046d050101c100e40803692074800002115400c60702801c0104000c004600c1180300000c1c411400b40303c2d00c0002c180e803920010360f00c8010f02d80401910000e0f8000e441517803c078519816880d00109085034003900901e01362001004000c00503008018480703001d0045c0d01c00c90700b00300c1003100030f900c1a8180d600440031548031594410741954030788940000840707040c4004030b03600102d5000741c550300c400a1007000c2000411585021a0010100203070b41000a855414810401c00d40c43c441ba00e18181d60303450505051a0419841e03075a2101c003446034545440c0e000601031032541000c1e01b030312440e99000e4401c4440340c40810311940d550b08100c1c400381c45540390800c6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 127534235 1250 127532985 127532987
    0x10620121c05131106091c0212060109051f05010e01081909050a0b01080a0f031b0b0a0b01030e01060501020d05070606051504090e1612060f0f090c0f0b031311040203010603020a030c 80
    0x46e2803440740c008100200e548403010803640e400800b108100e07004034109460203a40c042c03e1020074040c10400100060034540342400420302c1d00795203010b10080145480a0203035903401a041c030502032080c2050100781e1030b00202d40c00007800484c04c00405614040309402001004101000c8142c02942401066600c0e407840340d488042d005801002d07100800c00f107038006801410340e18003413211800e07251a161040c1d00c1e1500051400c643d5656256541d10b0403105568051050075048401c1e078000b085801d0628002039038a40c0360b45c10f100d00344100442c00030704028441c1c101c60003400e40506110b00741c01e03801c6102100b41d0054003402041d86d00300b0761540403039100007070b84601c0080002d50803030ba1103107005d20191400d54180c605403001a1200082d407096103480c0104800c40181000024226800b81803210459005030003180001c1e002c644200504d07020002aaa0002140703591a4585190752030200461128081150740040c000300000960a4140c3c2c041c1240820b903440a00c84000d41503c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 127535485 1250 127534235 127534237
    0x1020a14030709050904080405040c0e01080f04020901090e0309040603080a0813080901030f020c0d11070501020f060a1104080a08040e01090b0310180c0b03010620121c05131106 78
    0x54224000b45040c90f0802c41c0d480c01aa9103604180113034081803a19889201083c25144009500401700e45210400b81c06540e0203020300c0d600994041051030241886d0380011880e140605c1500602034607901003124504041c001c40341145001007003000200d58a103485c1d20140c11040017503003c980f0000005503031190260813504500d605c4402d0600e040040701c01540105448041d444c0410b50900003030807074020411481c01540d00310780711103001541c1c01c0c1c9954075103451508100c0c1103402003580d02880040001e900f9030089903c040c0414054107035200d03202d9030302076540801c44030711401443c103003440300b8a0300034815039001210001541e80ca0301c40c403105071851287c1c01c5c1c0e01a0700c8007a13003500e8a8034550204e04107001c5040d40c2010806d00b0388540758058944d0300155100c210000c010881c3c1178001400440d407400f5800c2490b048007440d545180c646100ca141510403110028001c0368401200c010340491000c0c0c00420031403401c100140c1001c074144a0002c44501c141c0b20420701140c94800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 127536735 1250 127535485 127535491
    0xb0d051005100f060f030906050a090b060402091806010203162010020a0209060411040b03180105070c0b0603070905070203071a1003030e1824090114060307140c01020a1403 76
    0x612540e040c3c03450402c040715010a0b00c01581e04041d51200d81c60001810341c000c07036000b100c46d0440030030b40c4851410007120226018014034421072040112024546409510441c1c2441c0c0d5440f42400341c0e600300c010703420743c852459095104101c05000d80104028084000c401c44844000d0b040244031000c1400b480419070906074000d0780c0003110000c010b280545c98150b00c00f02c003400205418910820803481a082900b003e02031620100c10001900008845130300c0b44042da0000b0b00850a041901400b200c0c0c0c203c070044c14620304200040e403152410001c03070b4020030001c041044280740c1140b0080d181d03046038104441c4500644844140104082419070290242030000c50195145503000c2d40c1c0e158540305950f402102440c0208021043c907a0740300c1c400c9105d42c0044a0492104006c21b2086c0080c66800e4403a03110000188004007604000e800c242c9030607517840d0f42c1c07920390100a42c2d14680d01002002071032000140044e5400c0c040d00034203044001a101c04920ba4010180030101e40422 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 127537985 1250 127536735 127536749
    0x60f1008071d18030408030c0c040218100309050a03031b030603030203040504090f020607030906121107080a03023a110306011821140303070206040201080a0b0d05100510 75
    0x1400350416a0b259003480c0030740201c000c0f415071000d500e1401481e41550030a9000201541011441c01c00d80c480034440e04030064021941180f9007a0620728540740b400c49502c2d0140036154014811072001d000364840002c03035810108417903040115140082c0075244001365034003016104058218094083d003e0f603000d503503054005d1801c044c20101440000c1000d01404d031900ca907030b1b83c48080035031102c000034110305000343d4078901500d0820a0180c0203801c8030540349903643c07410389084600454501a04c40c0703182c2c0400100d50718904078904070040e002c0c00c015100c04915008103d440c1c05600b00c200c5400803040c0c894030b6201d811081da5101151005500810042802c2000919943c410320480c101c03d40b14502074130074203407180030303500c4401a04500124501860351401d000e001a00710080908412880294554500300c1d100071346030714020340300034180080d0101180001c50580c0001d461120094900703000e52006007000d0740d451040c403054442c650300d48004560f81c03e40c5181280306076040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 127539235 1250 127537985 127538009
    0x606110a0807411516020a020604080606210a03030218040f0e06090a0c030f0c0b0406030b010909020702030c0f12030d0207110406050109120305161103010b10230c060f100807 77
    0x9800c90340c0c00c103541000c1e175103000c601400036a440182c0e00d500c0a00040c1140c640209003a2515000340310a9092100074a00745040c00020010154000510f40d134405500d450056207441d0603a40d180100601c084a09600c2030610500c02a00c034140c1d030124880c9000c14080750700710745840254545070444144082c2034038840100c1031012604842d901072045215000030913100783e4446015965400580188002948500b0312007011342e03112020101400c0104000c500d40702030341c3e0002e50703140c4050910600403100130500c0150b6035600780c400880b098660061b02e9230303031207203e030100000e501400e03084901e4200d150a00105050500ca02d505941c0182c466456141c2820b6070321060049032042102040001c0000044c1004000001c401c424800c1e00f640c601011740c04201820b44443c51011070058011840e2090010740c801d01100d2805c10b9441c0c000c518003d0301c0c0d42003005224a03411000b0301d204100034481d480040082851003200d605103800301450315003a01c1500c07815035200c2d010503048 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 127540485 1250 127539235 127539241
    0xa121d1207061d121506090f0708040203070305061f090501050109060c050106081506280612020f03010b040f0e01030809101b050102040602010606110a08074115 71
    0x4041c0841d1006030041c3c00c009480842c0da0790000b00002c01200c008a050780103030a48a80e10642e22031425003042d02255503c4243c980003110350040500181301000f08401b01c000b050664a09100e28005150020b040d60030a2810440d00c14040702c00c1d050b0049200180e403400192015144101030507131301b050b0755a00c5800e260400465041e002920203441c15503032110009030b900c00400415040e428400c03c080c16a241090801090754a42d585075030f501c9020400300ca2010401041503800e660590400841c89100a4003e20082c0203034504007205ca8400000813a240c800140980203d4001d121a00a00341c2ca44030481040c3c10281b000a00b032540501060316145041d41010b400000d0500c1c20007581c00c2c0c403150090041e820f4a200313803943d9500280c24001780d0380c28001d240c09403a41e801c003070014031015407007a43d40c0e54001102400a803000303d1400200000300011540c01c0c01c1c0f4120640c00a0350300e050b081160211600b4841c841040321100b40c0380340d20040b07251805804a0710013801c1ca96 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 127541735 1250 127540485 127540487
    0x40908030112140303090105011d0405060c03180609160506070b010521010c0309020a060c08031603110a020321070e0f0a09110301030b06010c0807030e030a121d120706 74
    0x1c04012400c031510b03c0000045005080d04001540c8120300c500004170f00355141c481c81941c850010742c0040b500111000030000801d6002a090750040c812820b07941c0c0e1390703841001c0c0360381c01c90032000105a240607040c14800c4181d400200c402403110460007840889664038200034891007071300380007006820070b8001044145020240320f8480e6410742c802003503000003009030034210b485880700000841c2d900c031002c40940c240441c814002d004a41021040b510b0a51580142800b000340200c0c5050501946902554401d410030b907031880110503041d8441442c03401c0a5281d8100710209012880b059080803085100c410710036000d6001038071001400b142c0f12040c410102c034605d640c544c1190320814002410702c07062050b800010100d1508549a50640c9040c81c50420041e080d14108401c410190021900076401c44116036403504120305041d039840c0203e82094103444000e008802da1107151690f050f0040c40d040750802c40f40085003070040300d5204124800c07940001c10f00c65030303200640600c252 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 127542985 1250 127541735 127541759
    0x160b070201050d02030a141515030c0405270a060f14030a0203071409060607030206060d0c0312030e060702070b0a0e04020d18030f020c03151512010b030c0409080301 73
    0x490061512a1403c480c00c001d0100b41e80c4151514400ca030707075130410b6040c1c1a1030700200700c2c0c006000c050280c003284946000101c80485034000c275186058000f0104c0c0314000302d00d00b03d0b0010308001d05136002504880350701301c580d4065011460b02460383c0c0000180b440e2641d1058000b81c407000301d680e65400341080c40441000e5642d109164040c4100500300f40542d408000b40401000308125041e00080c0b0202404003042d400341c040c0c1c0c081c6000f4480940000c3c1c0104050394032180a030b0710b458a90506061404881031940d00180c40c0942c00b452441ca2942d242c0c2010345079042c0f010444685488003582240c0e283c01c0e61081c0710038101e060001c00400ba01c40c403059910b68a00400240c140520806000101c9004183c1c02c10b094400e81d09031030405402c6480354003c07100700d002a15041545a010944904840803240d56510012000500b0342e00c250281040b0076a02412003640d498081e414a802082c007440080e100388141d50644401e41b4060141510f1143e026106909591030003e0745151 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 127544235 1250 127542985 127542997
    0x302030d0f1110050106030f0e2509050901020a20060f0c040b0c0304050102010c080c0403060203040206040305030d060918051c0c021503040b0f01081c02100207031808160b 76
    0x80000200b00805182c80400c4980124800804001074a501d00340e0040e04076034a82c1c030206c01e243d0500244c4e41c14000e0200d40700d10340021503a0b8460380d80c003849401c80320141403034000d005228030b0001806a6014154040c210440054580200c0c810001032501d080d2040098106407903880440080c00064503001c0880d0031000c0c13410080d0510343c440e4040303003081e000003510301786660010801304629039090244061a640034140044c550404650720403840c455400040c100b02d4002021508548880d0111002140c0040c10303243c480d1071524200d00504051310030b04140e1401d00b41d0341c04104221f2603032944407a40c041c1c024032913540301200411643d02c1d50f0902c042480b01a034200005030b142c80d0030742c5484c1d01600010fa652441d061818981c5844050002d042000015005105c07400000426140c800300c50503032200010041071080f07182040b180c9c1901d2602d03002041c220304141d0040c441e0a4a0320204030000142e9880c0c5480d076590b03a455403007083c018036401c1c000300310183d1034200600c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 127545485 1250 127544235 127544237
    0xd020409080c1b03070e09070603020702030c0a06030b030d020f0307020910030206070803040b1b0724020c0a02041d1c020f07060f08060406080c1302040e04050a12090302030d0f 78
    0x20070112030520160400c1201102440f1040f00c550384148189828420785010780100d501180f183d0400e07003126039403641c45019030030034540c0c0000c0180640d90b00f0465841100340003024645410b444010050151034508030450080c851004a40850b5002141c03401a07000c480000b5030524509408101d5165009088540640305011003c0050780f1140010011540609480b998a0130145082d0012030320081c40c1c1c03506a2819680c4c0d100125404003140c3d807040d000100c081e901c400e02d1241c05141c00107000640440f910009113007204150100b02258902e000311000c02800300c9400810110091076400c0d000a508600c010611146a110070101c40d00c85610454401420005100d0318080040c3c12200100381ca2640c802107032640a000035500401c169424415030f031414101039941e80c120b90b0f00ba482080c102d540e440b0304070b101d681550014040f07510000b1940c1090305105031210084201079600103000d43e42c40a000c2d0003200f441d0b085039400360041c030284442410171201882c4405d4200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 127546735 1250 127545485 127545487
    0x51918110f1302070302011b020c010f11151006030b030705090c0708041a13060c030903030e0f030a060207110916030f180507050a060311030a050916030302030a0905040b0d02040908 80
    0xc2c5540d5900c09844c8840c802c0d000001c0240c0380f0041d01b0751201d044c81000d03003150b205120110043e41c0c494200303807004c043c500b81201410b44400200307050500512007940000840001c00514050500e0100308550040d18108484c104035005d050315100300d40229600200c46401090051a5240c010300347c050040c20380500f01920394129030200365583e0441d0048150114030a07402c200c02c080b098009000340e00700404070101030341c2c0c00751140910740b0003d03050100302c49402071103481e10340c02010701718002400d032540f40c46c003850190003d4002410686400001c40107081031410401261030140a88606880c0035062540040700540401c1d00000c000070340b03506900701c24000b41d0000c485c8070340c45071007d4501036050505003c0f4281085d131181b0109030800f0030702c0020305400c0e0202e941200201c072011a0f941d850b064000d1030440f13442203200d40148694000401d00d580070014000524040d034501c5a9640d4034010041a80d210310039403a40302c03004500d100c2c01441e041d0f1148180c035205211003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 127547985 1250 127546735 127546759
    0x70210020a0803190f090210200d02060a0510050325050d080904050a021312020d020303030403110d02120f070f02100908060903030411130e01051918110f 68
    0xc803007660025510503040b0013000c84015030b803c2c5180282444030038000000c00405400750009110840603040c11014081c5100c40c94a01c44a10115083c10344100402c031294500c03c000001d50f00c400403241c80c0105854503011079000740b4010080c004030344009000300321000501a41c41e01185680d00e8880c003d681c074540010745a101d100561a4140c01541000d85449d8521b05100030394a00400c1e580c02d0078410080700025207000c10b00e00c01a1061300c0001900d090342031011a521549200e00a541440007004100400d60f0000d600f9880150400c01c0d00c01200c40c440c0140d0fa20f805e401030343c00d5020414070184910754050000b409907a4001c0001c03142c0c800060b0046010400c0000d104000182120002d1107200c00c03c116698203300700740c004515615003a1110f007982d03003403400e466100d51002c011070840d8081b641c10035000740382e03601c000304402d0804100c452005102d000035000d07482e007003d0f03400107424620351710036681c80e80080e810902904c0b45420000002c1210401f20380c066108109 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 127549235 1250 127547985 127547993
    0x1c050105060a0e0c131e0501180620010204030f0602190507080304030806030c10090504110403080a0503130501020a0c14030307020709200408010204260d050a11150403031a06070210020a 82
    0x86c440c10002c81042c844c0c0841c10100014030390032940c0c840e013015040c001301c10007000c0d40c040030300800c8515007002e28840104103012580a80301e030f80d001500c451441c098520034030149038000c2869502d404410004401000020394060107080c2000e400c009081c400280802e02492240d54011340013019507a000381020002000881d4122450000601040080c0100c1c18144200c0c2c0c0d002040909550409203542e80f500918403400d080d94003000b41c0032010400c2e0741c0d00b88202c082c009500c0700c000e5440740c04000c001800104940410703500f46004529181d0301800201c2100e001c0c04aa601400259041100340c0001e0300051050102cac0014070401e5078500600340e001f4102410080c8000340c1e5131403034540c0c13113a84039010003d0144102080e480c401001c2c0b00005081d18500b40500340320740c8540c1100310a403802c5016440c088400d014890a0300507080070302107028400c2c0d20a48007041719031842c19802c450041c0307000301e1603085141042241c01620340b2188241c1c0b4042c035441101e400c0512996 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 127550485 1250 127549235 127549259
    0x40209040b19030309080a0c09020d1d0a0204140421210204050f10050307030b0d1e02030d0503090a0f14070602061501080c0702060313021c050105060a0e0c13 70
    0x42100d12070b0300d00340030038010941e100d05c03c800140048001070070040c2803511009400200707032150340901a40000c80059580098000990300030300d4950110040d003402106a0301e40c1001c510807846289006072107040b0140c503004030b07801260451440c00144002950b058001c100c40ca207840240120501000310740200d851203046170700c600c1500907894500d0300040c80140c102c04540c2038820545e02d8285540560b008060340e501190301d1801080c41c0c3c120a0201e0541904404c000e40510280c0c0c5411440358000103105c41e10500c00c0c1c2c102c0ba0025a0340d1811900d602094605c507101341c11203040480462514a01070881030701036080f1345e40b0031507941c50f070a01e803007041e038062005a0446020040803440c201c0500c00010000e0802880034500312015000c24800c001c1d000784510b5000c000f2421200c00074880842555026000342042c80c00b500c080035003e40801c3c000c035015824480003d03c3d504244c0300310303001c6a000201141151f21800c075188820780000c2a0f01a204844c08000503104407461 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 127551735 1250 127550485 127550509
    0x1a0d1407050901020c030a051519020f0405190e150103140a140108060906070f050909040302101d03071415010f061403160e010516110907020604050309040209040b 72
    0x901c9280e5249204000a405d0907121062940700747c00055200010500201d410312204031404000c1c4030680c0c46e884851210800b1310008081e441c80810100c04403c0c200006000383c4504407001d0840c0f640f041040d0300c11a0980c0078446844040801080f088004074120310200c0d1014100410081b044800ca10302d20320044461110568640b03c0e40041070840c41c0b0b03018003410004010701361928100f21702a54845015000104110072004410003040c81341060b6020440010300249550615050080d92030070482c0c000040381d031900784500c00b00c00e401c4118540d030003a020061030402400c0d858511110020f4a49200700303028012002c4032407019a84800c0c064404101c002c40d2030350428200800215900d0b4202d206594208103001c0445100041141c01078030500e000040009080300484c6c1d240200d0642d0160f80340a507100c103040118043ca82e1444190945810140d9928801c08a980308801e540207803441d0800c000152441c05c0640040102203009400806c2d481031303401c0810600d036100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 127552985 1250 127551735 127551737
    0x509030406030506010c0305121b0703170105030106060c06050601090e0103061a120a0213020c010c031d030910081f030501091a07091806050d12031103011a0d1407 72
    0x1001e00400750548202074101000307103050652850300f0754000e80f044c41400007503544290010005400202110060850440030b101c1541c1c5a104510b0058002c10900301021417041c3c120380040f600d8101403081c081110a99030740e60800402c9919140c2c0101009020305041000c10f46c00401e01041080c002c0d80214414400041c0606001480c0c0701e1901301e20910714428409604004006000000d25030074298045400b0360078203c510082000910607119282503039400d050028841035015482503094803030f014902a160b01c0044a915100c0c803c4581440c3c1c0a800038119425007440352200f01c2e80b02e0310b038856400c800e44c11449070a41c1c011041e40119961780d100d260420410bc00b0216140030194500d03840652400c1070500a4408600703030003044101c42d0754480e0b0b103100e814a50010401060301170300c000782c05070142c10410340c50003040002e43c021078100606641c3c80402201100d04071401c41d131070101c240064482c281043e030b001c410000b030185d0b00c96090050542c0c0300400d50f401508a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 127554235 1250 127552985 127552987
    0x615091e120506071b02100807020a060f0603030210090309060507081e0d0b090105090711010207020405010e0601180605040b07060e12031005030604120c05070807060302030403080603010c021002030a0f050903 92
    0xb009009005c06100c4150310400c524030220200140c84529051408080905040e02c4c0340d51241012846d115090f10081c041c1802e042c803606620b48a07500c010305413806682542c00c042c0c00e204080c8180c41c03c00000400081c0b02450030841c1ca0b124002400c44144903622003450b280c3d001c510b1518043e0b214950a1f5201c40026525402010522504407600002c8c0c3e440e007501c1d0714100014181c030800504000900132000603502c0c82c08020350480d405e05034020400c0015584032001e4480e02e81c4102c5a860208140c032010500710180b800744030040710800c5e130b1060b2820f400d0400e4141c054001403c00c5600c81c0e1602c0e551f1542000c144a8140e5203141c40c05010b45a1401d9100314040e008580d00850203500207400340000b0806400d131028295045080000c1c2e0031149181c10b40c503000f8650300881d624050040003140095154000f503001754020fa0724918680c4660042600301c2d8203628100001d40d01c041084d54580d011500074640c424154900010403241f41c0081c001520011a414949600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 127555485 1250 127554235 127554241
    0x40303020c0f010309020a05190b0412020102010c0912081318050417040302010203070f020a0b1902070501080c03040b100902160506011d04080921100615091e120506 73
    0x1010a100b4004500901c0c0910409031300380c02282d05820180100d41c00303807a41c00d1040381400d01f003034803080050402031596076640780c1e240001598a492903000f01d00550034000749480c21446001c641050b175181c41d104140245142d50ac90205900203240001c1a803449180011000d0700380c0c140461001c02c50b4404216440d0600d45069054003507031080c40040d105100070300140c0d9000040d10350703030f941c014980b026810032400040e900d0421603100c03107090070000505100d0b1f80103020101d80010600e808907000300f916500192030522003182d10200c40e40c8107100240c081001d80001d10341015004400d03201c0182c41c1c86c2a801680e100941401701c640101c4094010400208480d81c0189060400a10407280d0500501c503a040d01600280480401064142542c1d40d14003500258030781e4040c00d401c20380210320070252118490300c040d060b07442c50600700083c000340051154141041954585804070301340184c1502c00e4140444c505d403406105100400c414030403e4044492900076130040009103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 127556735 1250 127555485 127555489
    0x1603030e150315010302090a0e07021b0a030b0a0506010c0501062616031514070e03010f110901030c0e030a1b0902070305190201091a09151e0408040902040303020c 72
    0x205450440441140c0c20010004951140d40c400c3ca43e60009203000b41c0d41d081c00c0e1001900c150340e1071b0030111010080d2800c0c011056000910344014840d040e148829655800e000c00456804d0392101414001c140030004809038103c0d8011540700781d050400c1b07413000003036458480c2141d14580002e01c21001055842c04420151110044480070310b0006141e0185140303024a02042c0074030000740b0a240402e00c01080040700c0d0000c1c41c0c00b501a8a0088407450031100050034480c40c800168029444e0401c07100c0310750558040c010401040040c5103103041d282c071004400400542c610f0b541004018164810656030502103080c81c1c9001c0c000d9041d80c110652100c0100320299445030103a40d104102d4000040c0e088400d90300984190081c500c52002100c201340d0250403409001408403900f840701007182070075080c2aa004041d458121000f409042e202400301940544003041e10754410650882100c91065519912030f204041441c20b00b603580400744143e81080e0012805a041200344041d64 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 127557985 1250 127556735 127556749
    0x102040503100e0a170c100b1305060306010501080612010603210206090703060f0e1e01050606040e1305030c0303090304050306100e1602120a02070503060109050c1207021603030e 79
    0x80c01c1140001c01108400c1050b0035511311800000810031188401c100d44602c0040c41034031020800201901c0e1415180064840180701c80b02c092071040c040000c1e210f000c10780764400c90380700d950301400030101f80e401c041c01510070040c020161584601181c05640e5900b03c20700550b001540f00b82d20000b040b2807100480404022645404000c550110040080c81c03c000651041103c2d0030450006150155018540190400c007058424a02c105004021090500940c1e403154513002c00080002d034607a00c040100511552040086404112000c10b84104d50903c484481e6440b540c105c07880c105001d189c0c80e013180c20480baa11001d400114040000b41070900400707902640848682c4042d50030041302214203e00600034500e9040e4035a11000628000c000384501011345441660722400840c100944e80e010303601580f03001e40640f40c0001011003580c01064060007800301e8460512500080401c100d590003060703034046205a401854810310b814000502540c002e90780c2c40b141d114103900780702e0307a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 127559235 1250 127557985 127558003
    0x40e0a0609023a0501030b0a0614010f11010b0409030c0c060309030c0b0601090302090109090303060e06010509060c0c09010b071e0c12050a0210020f07090b0d030509210102040503 79
    0x464010007049a50310410300a92400040656100540703500346210b02107211059074810b9101071a04c400801488803581069104401c0e41e14103102d00d1307840d803d8150040e416006201e0104154001c1007201c18010913403565854260310000a144200b000054199100d0407400e03400300d40004450f6092000c2040c8540207401c15080c203000d506456039000f04803108510000d00554140008039a89a1003502110010b640003400d40009507164883c2c0c40080100040407000f0034508080013441e804040800e40c40b0307083c140c5806d81031000c82d0040c400b00fa801a0392005d068001d40900381c00940d16260441d010302541240030342c440207a0b10302070032248104002d5406201d201d440b110300080e03500c29940d09407800804e0340b00d21080c3c40d00d4032502e00055000c009501010100449002c00c0e80080d01405010041c02180c03007541e40c5c0e204d501d04a0ba581d00c0c103290030006a11150010900403002400b41c0a80034080056100584011280d8003400307885034042030350001410851440c0070040002c03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 127560485 1250 127559235 127559249
    0x6060e041b08030a0c110a03080c01140402030d0302071b15110c0f060901020703150207020a0e0c031b0c030a080a05070908061602010219020106060906031415030111040e0a06 77
    0x9102800e00e20500d989020b001d04003010000341310422002c01c40c20006c0c10900e80005000108116201d2810480d40c1c4c01003155803c26611f007005203401c05001d003144500594000cac015084d241c0c0852800c502a501004007a40c2c8002190508482d010700030800100418140080054a5071000780050440c001004030214a50051b00e24024580c0c825180c003451000031100700355078590010040c1e044c011181d002904004074a070002107500c1d1960018480c0500c01c64850800d035840b96021040c0c0f140c25642e02c43c1d113401c240001031150350f120701a03007569000b644815040a0300d420700545994859001000000c1415042c420448018050150003070444c6c180000d6490810340c4117592110024546000c401c41c20f030110580038000e504aa2003101d14100c1045c03440e6a582d00a80680002d1192100040e5140303030002d01c403032091080b04180d111084d100360260304ca501c8000b858088014016516559a040342c400305000c0030300600c024884c0c03c0d030400d41403400424403411164140e2141c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 127561735 1250 127560485 127560533
    0x905090c04051c03030b06160204050603070b19090e0108011a03061506070c03020402040e07120c170403021c020115080706020705150708030c0408010b240901020a06060e04 76
    0x40090703600c01000b042c480d010100040005400c900302100600b4807a640c0700d810090003d02201c5040044010b10235550082d81c0030301013500c6100034140d8980e498031130b20712030480521612046d04000030515007134540074a0203040302d035126000016184c0d021b0b440682141c1d525034403000c00721038441215451040840141c4845c2c5004008032580203d100c1c01e00303204090009a003020044403124000c06141c01900840d20340e510b48a12280410090f0b8450707010070000d40b0b010b19500355034080c600280000d41e0340c82c06e1602144200c404c2c00e91010380200d0560040c0b450040c0344024072000740f00903c0c21940081441c0d2248400e107117260301240c00ca05081d410480062010036000030b82e02e000c5541c10350740a08000d0301510520018024544000d0405e00c00109004a907142803010300181d0b2091002001a06480810016003511100d401c003590f00e91442417081600e03140010340f20042044c01520800b86042e5107040854106030400703000c43e03e0300014042404051144c1d1001050002044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 127562985 1250 127561735 127561739
    0x609100510051b03030117280204091a190e030c03041a160503030703050c0c060a0b12070914070906050412030e1f11190b0a06080d0905090c04 63
    0x40381041c01810036800070300c600040d1950605003824400341c945454601a00d40740e5846000b80c1c2d508951303032640c25002e442a9402c3c000c4111420302c440c460000102c1d6000d41080d40d42c0d00f80000760802d50f100303485203500203e00000a49004150610070307210340300001d541c450018403020031660804202c00c120781c014000003c02a400000b100c0c151803031240c00d018680c03112070722a142c500c50b101301d010071740740404400810810008051800340501751030510180c4d44810b0f00840c64000c4810a0055a0014001c11001d81559200c50f00c103903c090050b1002541d4078000e1450445030b54401039040e40d9a0f1034250080303016004154002c1400d150801c101468428001c06034050f5002d00e000e51280d0303c0030001014050484c2400382d0342c0141c1425400c0540c0200c491100d0041220040480e051008100f002c01021a0642c40480f501c06240590300c0251a1010500c1000700902c01d001d40d00c00740031602d20b20030004131343c0e050f51581e101d00c21642424203003e0031000240c0800010b4009101c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 127564235 1250 127562985 127562989
    0x14120403020114030603070503190302010f2304022b02040b0118141309080a0207060e18060d05010207050723091501020a0b010605040305071a0717040e0a020306091005 74
    0x1c051603c50b82c904000c0d440780c4800c40001d0400c1410b80c4002c0e030602c5800100404100c0201d1301012140c0a900200402d0080c40d04a0054030425024112455652030043c00c042c0a083d000301d1704140080c0168039001e1841c0150f0072124016500036902442c2401b03c54114606400b03480600c074000c2c60624084c0760603d002e1000000315008020500d00c5542c1280c50580351010405126052690701b400701c1003403820f120031a40c0c08100860300501451801007610390160140c200c6038000688850f0b030a40c0d400700d0450030300304050807d83d07100c607220310540d0101d82c09001074598a40208058000c1d0703031506412508202024140e606029812202c1c04100d0b43e520b919142d1050f07003040c181507041030080040f410320103c81070040c02c1d41d4420f40049000c80d4820007030000e8031701c204119a402ca40701d202c500701d150311151202070000702c01c02c81c1c900000c52810244007411410002c69040a84441419240e040c00316504192964007200b0054140b5101d0981500013503c0c03991440510f080c800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 127565485 1250 127564235 127564247
    0x24141308031605070f0b0105010201230a0b0f0406060203090a09050610030504210207180207050303181009030804020a0509090c091f080a0203010e0312130602090607141204030201 79
    0x4000d040b03000ca04070b0300c1e14055008400b03c40050394440c03d900441c0245140020a03910b0a0103440d00561a08401041540c06110352054041099050703005c6a07441c10050f0003e4401084110b40128410160010b03c0c7c0311401140e001d424190080c4d81c50755400428820007041030341c4002505414103003880200d4454a60720010b092031494041b40a60707550070300400313014040d03603800e000c184420031120900307902241c1442529030202c1460751220742c1017546000e0780a0000060b089420030000328000e03100740c482044841c11200242c2d0200320031109820115110300c001a00070a50781d00400c070451500c800b00074080d05049984201606020034040d544400d5080124020140c65002c03607403031300300d1100800c206038880811040107521841c040380c8544c8400c8040f40070b50b00702404a10241404825240284403044500c1c600d40d50341c0c07136100c0103c0003911007501d01d03c0d0708210807002a240e00000b08880e0303000355100903500c0b4040f64003a10b80f00900180f050301200500c400d2006031f0b4060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 127566735 1250 127565485 127565491
    0x30b0f0f040f110d080d0608010c020c0102061305070f03060b030105060103020720011803030e120604031727061008060106050d021b07150905040c050a03092414130803 74
    0xc3c10f004003140c001d404120200b1340e103400605055004581002840d003103400102c203a40200b00240720071444640c0683e80c55841d54440d5000da000180014909002040304910701401501202c1c01c0c142d48800b402680c80194109550140d100e0507200e040d030800740074064203c8030a00c0c04502d4481e080e01c0c0c0400c940f4690030710f0f6980700c04030f103160080d07680310761215000c107540a130601d8582c6549180c0a05100c81b061041e500407522406041c01080f808949184150307056181c1c0a200d0303c80c688101c04401e0010540c5c410f4640115420f08040009800e145542c600c85006040c01c1c18548924444060503603c42100350344a0380c011b01005902800382da445c006c10700d80258444a10ba03414a00041c030154007500c0e1845003480c00104e80e074810890260481168861142c070580710403e10040d903491450382030100380100b000021241c82030b80102c40081c0101011030040c0340c80310041c45c2c0c1c460740c0440e12200f140c5400310b96401401282480d40c00c11901106552406075035545c00956000003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 127567985 1250 127566735 127566743
    0xa0603050601020a081306090e011a030712060f03110a080712111302210624070605011404060603020c0a060c0203040911130e04020306160e0604030b0f0f040f 70
    0x800c08551140d000304018030300c031035114004ca034854070018040b00705c5035490700c00d0030002104800300050000300b0346584d9040c0c64101030b6102c0200002460351034580d0000d0240000c0107000c0b80320300002e85491003800302410043c200415083d00e5414445014060000594450160424100081c0c0f000080f4082203800c1c600c0b6100303400b80c650418418150310015100d8008482da14010850030340e41c0d0080c22620440490203403c8007406207008060901200d50942011101655200c0c3d090009001180211103141c0701e0318082d140c4d0f0340e1000f0349000381e02101e41181c051100f0781d41d620b4035010b4070000d00000c0c03408505198031200c8540d074900f040f0ba40a8155641c0342e66010226101b03000301d038050000c1410501050107940c0921008c0d0748591301c00854081e05860103e401100301621a0045030001c00820396500d030603107461008801c90740d024050200e14086044503445010152000b9070041c0c0ca201d425140010700410804d40050100790f0086100041000181d080e000e010703101508 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 127569235 1250 127567985 127567991
    0x1809090a1b08031b0706020d0f121b020c12010e0a0209070215090c0a15020a060b1c030804110d0309090e070506041814010f0302060f041203050a030b06090a0603 71
    0x103024031041029060b81001c1154000001c003c2240c0c11201c03245a007000c5082d0440b1800ca83ea00c00890300c071360b0380c85140740002d40c3c0c01c5009803c16210f02078880e0116550b544c0058882002c0c440070050070220303680c0b036025130081201c1580c1858580821078041180000a10501a41403242030300c0d0121003800034407840200f004120064401c00000251172443e9840030540c1c10710414460355001c6014909200322005280403d0000405000708103541494004003503062160752424040c04c070710801c0580020040298030540c0e44080c1242503000c0c000e440b44011070400341400c0d454900030b0039045014020031140d05001a41c0400c1e060100d0310103003800105500400b549074200701035a03006e6507102c3c002180114040112010000051038813807020080391000d40201e109042c4248180303003c03c1d041450400160400c140144400a161800940b40c19160059103610501c04181a00010f001041b030541c40f0360144a0000403000407202181800c8040000074040b140d0b5004170390800d51 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 127570485 1250 127569235 127569263
    0xd031109130207050610030b1e060607020102010b041a010315030309060804060e06070e100806150d06030203033004020f01110118030203030a0c0e030c010513030b09031809090a 78
    0x1c40d5064800d115440404e13a0110b040c0000c5441ca51802070005548400064020030810348000249642c00982000c200d000f9945003402c10040340c02c8030b00c041c2c3c11b6540350302001d9500c0d0703500d01c01e42d01c941c1800c441504080c1c0f60034000600319182c4920900c100001c000003030010a800000c210300319116440c1a0105580301e14142d0080d04001c1d110348194410307401445407064001030140103044040c1c9543d03c258081c4081281c02d42c0e0f05850483c2c000c584c0d00e10f5120344283da1300c0206141c1400080110f28241c0c0e99012a05e9036115035058507044071413100c449043e400d11400e10404501e10804040e55003802e40029940030b846054944c184a466000c00751040303429008500c0105010000c402102c1d21418040e490364012214280e203e480c10f42d000c55550700418072035441541c00350041c2880100340700191100d90081540c0141c070081c041000002440c2d200441780301d00705000155486014825004c0403c15080e04a40d2042014800700f004c201d100154208007190060554151f01e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 127571735 1250 127570485 127570519
    0x5150402060d0204080c0103050c13170a140d030b031b01030513020d0f150603031202070c12030c0323071506051c0209070c030f08070302040f090507020d031109 71
    0x3110b114140c050150003c0380008030090003103501504542d0a8806007c3c66131107111404440c401d40000d804d400420041c00c0c085080042c034601011801c41c01162901909070300c0b04203030800c02c9282c1e544103920108a0611103a41070003106601c801c143d0080888188103040320044048600c20141016590b0700003402103060b40b03004101c2942c01402d40c00e40d803041810100c6061038400b205071412070710498406e0444582d07104410803a605959103d81650b004640c0d0300196000410580d0303103500091000c00c103900c094210340c486030312a48911000d0b01c028a40503110030f02500d8050000380030700d8010b680d0314404e0012169000c0e403229515140110340c0710914001d1030a0b401441e006a20200142080b009000c03907080028000c444106c56a0784818080700c5a9070580801400121036010a9240d68000c418a42e04000a4103015003010303211110712224090360b5014000c15600c03181404006038051080446400b03640c0707400c0c010031064a400d8200740c440c091500b8010705101c107400c030070700c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 127572985 1250 127571735 127571737
    0x90c030717150c03070338011103040f031103010621120206010531020a03060e09061b070c0e0705040311010e1513050a0e010f0e07080103030305041104290402070515040206 76
    0xa407840601c140480b60400e1f0316100214501c0403928041a010b81000180441c000280c0d000c854101707038bc0750040b605655071006160302c2c4d80d900c1a099034039920041105200400d141c80b140340a0010031000911904089920541d5219401d041d50880c50060189484104c00401000c000702d60130031000c05000d2000c40c090462000d5030132068800b20300046119415007001003141c09000c894070145d164120402d40364841a00d01e03424600c02c1c140441d0041c07000d034010300071607030040b02d0018180782e4994480e0800c1c00c0441e40b4034001140060103200704001d0041c0889000020300c0c249814181e00d0740482c0780000c00c00750030014440701042041d40da41746072401101400b0050b0030000800d984502078400c0b648213000b20710505109001c00700d00140340181070f030710030078041d51405441c2e440c5071803d400400003c1c10a41d4001c0d0340003403d020720341321401584110004810f114144074014104a8400d150552005110714010096100428800101d0700c41c580c1c0f440e4815015034075180f00290107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 127574235 1250 127572985 127573031
    0xc070b06062b02130905010e010302041d030c1507030b010e2b0602040527012619020103050907050a2607060201020307030c0306030b0708090c030717150c030703 71
    0x62209915641c420382c80c00b50054500c4d400e44440111007a0307244e03494081a11824041c641c101490000100058a03080d04400c078501c0c660381009c8003541403c0c46450a6500c4038800d001c4e9948a03640c00500040081d85003a402001c91a0030090054640002000e544080b0306451180103410048155000c0142c40e0b100440320001c0007030b9003404945000406500144200c61013010803402c80707554084003541001d0700d640c0e664a010a240e0a02841c0280c8841300181c24800c1d0303000c4160015a03c000300100c080e44541005c1f025108003041c800101a40c000408011103500200401c0000d903e0f0b1541e1041950900340d40300b41d031644040c1c0b584801070b8142002001500c00c203440020030940650045025200c01e540502c03040030246019070503642103100c001c21001201001403c6588285100d0760840c07901c0f010388414100b03010010307162a600e900300d041c01c03d5500a14088418081005190780782400d003074401d091034028501c00c4039000041094082c1038a405000d24a14104110300c40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 127575485 1250 127574235 127574287
    0xa03080c030705121503070f09050121030302130515090907020d1209050a0507030c180204051e030106090f0e06010e150d080403020315071d0a090b0f040603080a080c070b0606 77
    0x100f80d503480300b62302503409140c440d25085e2443d0600205a0001e040b17140e08009051211506414415660480080d80f1041c021100c190801d103010400d503076041c03607256650885905041d1208890020031009200103460901554010341d80020302e40c0c1c1004203c0f1202000d400009404581400c1c81410015a220014224000c035072001c01000544800c103015503040c1c1400b00c80041070701480c403003244201e01425612200301c148902d80c8096103c1680c054400180c004074009030f42d408100161500380d001d2886098803159010321001c42001002c1c010001030b01c1e5010303542400501c90000141c000c5410303005103404880c103020300058000b01c4004580c041c084500011030800c621003192001c9d80c10000060140d92040c1c400c0d00c0c882017141c0c1c074400003400c00c88003134606504500140719940340a1341001054400000c1c550707032407042d50000c5011b01522640d665500f54020301c0500c00074100c0207074402c18031003c40810142c0600f59488402950f245684000503103d242c0c030000f21240d410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 127576735 1250 127575485 127575493
    0x60c0706140408270102031b0312090c011403060603040609020126071e02060f07110f03030a150b04050904030309021f140c060f060d12020a03080c030705121503 71
    0x10080110b00001070400c00d14451511861440d0b40c83c42410344d482c0452070b90700680c024080c10007000b0f05514240061410f01089030700c0c5ca039003006802c0f901041291045207580102c40900742d9941c200c10301e1080c260b41c04103403510314070f4131340006005ca00000c0c04c003801059680030a4002c40e4000d00080a005500704510030200740ca461611700300c503c041310000002440140401d07130340040c0403c032440728002d0350040c004950700c00c1c50200502d040204240300f0000c102c0d00380440c1207405d000744049000d103440690351320710700f40c1c000500342c0d84041c1c0ba40718204c410090421034810000b09440a41c1e0041700c0480c580d07151f90a04034050018600c0c081d41c82008031880b880701102403802049074424640f5101d40401d07510034504414014000382c2941c9400440c00641c1d0549001c90b82588420010306c1c145440ca1940c5404113020104113410025900410070a070502d80c0000341c00c2d5001c0700181072a4954030380070b0002401d03801420700c11000401c2e620041403400c4c1030100303100d850340c42c050121 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 127577985 1250 127576735 127576741
    0x1707030c0801120821190902030d0e0a0b0a110c0108070c060b0411040909060506061602041d060c0307020105010f050d121403090307060b030105010e0402090a110d0203010302030d08010305060c070614 88
    0x450001401e8031b81c40241c8140d62550f1007026030600860061a070020091f00309000301c0003080e5502d0417904142030f8885010031004c034240c0310560290066070000e5a440c0100c003031040310149841c00f481c0700c1606014242003040080b50344440200c02041d030001c8041541106440030070003620490f0b51f03e6681c0c0e54007160101d060784007580540030f203d00500052040f500c444050145d41e100b0b50061025410156044002504003500030b0045000000d84815201d03000100306070a2910035160000030f518004140003103140e0902469014260800c0e4030040d03285030400040c0501054500240102e056240c040b4030705000d80d442d00e00090800040325a04d1070010301c03144d120703805a0000c8540d907103001c440101c04c1c1414402d040c143c1e03050310302c00085501c881d000c00070304c0d0600514480c81c960722a00540c151481e024080c22242510b40b0300540c5030750451040504200c130710300c2d500b0204024000100007154000030883c1d0810944d1289996610b01da0800178043c000404c400900ba07485803040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 127579235 1250 127577985 127578037
    0x1060803041d16081803041a031b13090b1201110309151303050304080f0403032a030e0112020c0109050a02041b0e061b0d1707030c08011208 62
    0x51100d0310000d50781142031541d43d20070030540d08406801d42c00d001070409000642c1503403002104000d40c06001040728101030b594080c214522030388410a003d4035034080103001e074040061032590451010160f034181030229800c003800502c02d9038450640100e4480c0c4a5000a8542007452455107050328001c0c0002034900d01c08203103503441179900c1910351207054600300748144603004240c06403881e0b8003091012101501c00b1159900040c0050b5400702082203d28402d815030002400214800d4907001800d4000c50402d800d000207070745000f60203518500301100041d521034000e88480500f42841104042d401c1080c2c03000b402000320341c1c0c82d107601c6c2ca4011400d000e40080d803000494802c813070034031243c40d50a85292016000083c507001280c4a01c0300715610745440d034068040803072181e020150b51110104081c2c80c205001102e480032440600c0044180b5614000c0c4a911801c00d0900f80004050244001e00b540c005100e140e18440140010f0010880d0110450310840c1d80d070700c983c030440d11404003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 127580485 1250 127579235 127579259
    0x100506220501150203130b070812040c060e0f130507020c0d05010510062a0f0b16080c090f010c0503040305060c0307020d020a080f0306040603021e031e0601170106080304 75
    0xa12641a840340950801d03a480003040b5501c81d4020b41701204403034a0240702c47c1c501e40000c641100c54a4050141070068048070034070320b20071800344115402092030000007030607607030718564080d000f1156440c1c1882c1d152036011802501c1100b00c2d07030025160741c510100302d0900b40e00c1030350b050b8010580c1c0001c40c1400fa054201c1c50280781c91020b131100f00ca56820b400d4a40c0d1600b51580744144000b4500c14452000001940785800e02401300c100302c071211540c0c0d102c440041218095228103e0b9075602c00150350201c41564854011001c20b49803100d8400000d03000f02d16121290b040104607029201000420b105031b80003190300c50211180b42c1482c0710440c2036504100c0d41d54005104401a40305803600c0007840e4400c1540040b1074503c0c0200c64400c20042d580001d0907280c2068803250f0003c01a02c40a24960824558900303c004056102c801c0505000e400e0380315079a07c0011400305940e00340f0210703101e41150701e6290300c8541030890036410f50240030503a10003881d60101007800141404111 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 127581735 1250 127580485 127580489
    0x306090d1106010501170a02131d061801090f0207050d0c021801031203090302010905070602071806051c0218100609091a1009050616020306060303070302100506220501 74
    0x2859005069a0000c01c1030b40ea11401d1080350f00013000b690380041110556410103800c0400240058a4041004020050311020354480c0e0081800d000000f0703030068140d035119410090440e881800750300c50010704140071106001e292941c0350f84a000781c038030000b9541155500ba9100f001e9610400e00b044001d413900c100c43e1000c0e03000b0421629450f50340541004014141c0341e10428210740514408011002002020000c03400d640d0303545203040105004000394070007170580b503000b821800e04010484e00143c0c14501841074090408105004a64403040851700010003000d084407400d4060002800d10414075036011041080c1c40103001300040401c1c000002d03941c8030f495500126030340f1890402140d0302c0341003c501a062003207000c0000d1130410704107921140c0303a03c1c0c210301094590b0001441c1c2e601c0600705001d10440320b564030046080c00d1000d40e5008600302c015508140450710060340b20034400e5043c1da9010751700d60008501d503941400e00c0d4100943e9201d078100c4910b03d030f4000c20040c40c0c28 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 127582985 1250 127581735 127581737
    0xe0d0c0810060e070203180a0b0309060603100209130c03140406020403051920190b03010302030106060f021525030905060a0b0105070209090c040207050307030f020303010e0c0c0c0306090d 83
    0x5020a103841c03d0055680a050307141e00452416a414080c1552070800e4840e281e0301805e00d180c000f4550301c00303101a5020310485005003540d41440c404040c0741c0300843c1441881140140048142036403102106105601c144c0d0f004100109442001c4000300101e50a10340d5041c94442070006020f280d5006e041a03e02c180100d0703e43c1c44842042040d140b031005401011200281e030915450b044a405a81c0a04800b521001c01c9801381c041c1202c0e0b01e08142c008804141e00031004109518003400b400e00280700c41e05120300d14801d1890000d480b0b603126400006211600030200c1c8400c0b03a00e0385000d20b1a030107080c1e413601400c01ca54004029200e5003200b076501e40310300404503400380150b21540a5041e0705848003441c00149a0901640901c01808900c450140c0800e07080c0f19100c900003005d90311f00c00c0e000b03940da074086407501811100305c00541004540c424401804ac24445030016500040c90504980d21a41c4071070300d030340c500180c3c1c1501e96007501170101405012040015000c00031035031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 127584235 1250 127582985 127582991
    0x1106070c150b120604030806010801030206030c16080a0e13020a02070501180504020f0715111614011103011701020a020703020622061107060809190201020f03030f04171303030e0d0c0810 82
    0x1488c0011181c00c042030101a5015800300045445000200000c0c040c3c020990449402c400041d191040d80e60880b200941c007081c4202c407804028641100740249488000f00b0442c103105201030f000350741d0503641c00b0321818003200901c10320a890007840341030020540200195501c0c425100070f039440e600442c05c01c0303800400780300e003030616074505005520401020180136410320700340c40100d481e48401010b0960304135802c0801048100c80030301404000d00070f100c9800b65294980490072207100351703000408455074818009c0000c00760303000c1400e604481e011aa450303115001200164100a009030240c00c0c08440294002441a0086c3e12034101d2894002580d01c0c0a9480070203544c00401120030356015003000a03030603901c2c0c0517111400701d40c60040c03048403031010b21880e00d10b185600507103a02041c0350300c500800007040f0048450418190f43c0240041c01c0480c681800301080245000c01810f000b2585020303205034462443d9410b0240e0403000101480ea914030b150307078856502d070328803a442e0740c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 127585485 1250 127584235 127584241
    0x40501080307030f03051e01080f0c090f0106080606040b13150201090203060604180f060504020f0406320d030e03150105012709020711011106070c150b1206040308 72
    0x200030040d0381e00b4070342685615918204a40d001c030b0081c00014128024060303114810104100031604041c0a007041c0c4005003044582c4c00c440a1911404003d150b10540400042050b4408a011858110b50042c208045d042d1100030004000380180e40040a90070310110701c000e4a01f04010b520421146000c601181da10f0f400b071012400d07500f05250182d0150301240c042035480c10154018401828503942e103610001c9680e441943c11001c03548161107940c0c44400340020352a004100e807204000c02c54042240f585880304004000c01006448094400d50004807001d043c42003151041c81d120051061030505101c0ca0040c0020903ca035040340a4820301705007403d03142400560078180d400584480d505408500301e001a030818004846141440105001441e0703c9540040c00001e84140307140c0c003202c800c50340018110010003801001c85d0f40a002844401900b050b07204d844150004032010041d018807440e4805086509411504039600e0009501600c034080350365406a41300365102c038490b407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 127586735 1250 127585485 127585499
    0x1605061b2b020d0203010303050406030609020a080c31030c140f060703020102070609060506040b0a0317090414090303010e090a051e011e0e0f0a12030c02120c0c040501 74
    0x80110741c1003000740305400403028444010002a003007066500c0502602d054084403002059810a901c00c80200d00d01140034040660140120341c003030582c502e4114140074031103100a00501c406401d00e441c2800c00210307500f20360003040340c3c800c9100403040c0070100d030140d254010724041018802614240509540841c0c110041020005401c600402c040250000d000c1000782c4c603403204100b1400d56600b009a00300040d6207000d40c401040c010f0400103064504003050000350707800c04500510426a4500501c0045c004403560140c0301d800481080d16907400201040040525000910249501a082020a1000000440c1603801d2070710700d02d50030b89a0181c1c544ea9410403010051007500541d407100708203036100240158411864002203400c0c0d0741405164070140ea442110b560894607480380e1603030564200249075000d4603000081071065501e0b21180c030b052141b131000b030080540f55039600140318400c01c600b9410441203510306a598100303401f901c2c8c0e10032030090b42034007590034a03000141e12 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 127587985 1250 127586735 127586737
    0x30207180b030a021c1202060703110a12020d0f020c1c08090303060904060204091a030c0d15020a0509031f050c1612020319170f04050703030c02061605061b 69
    0x4041c0680240a148110307402c00022a005070000007000a2203013051010a03400c6000d85030039002c6401900301030405032801400e482c444000c04200321401c110004039254482c180000c03071868024010384079a0710380480c50140c02514182c2c2949070020a000205c5040032840d001201c000b04a1030511006c0d808081e00c135100f080328001056041400010510300f8000207042c1c1c05840303400300514017611180c0380e0f0b08a450052410180444402084c00c0e41e090400103003244600440d280e130b4080807070f55100342a4810f40110203130103940100f24890403a0203181910381014005042e03403210104007005141590408003e070b0180784c240b00104e0b080b4044001280e40150b00d00d2124045a016525014400c110340b0000b038086200c00c210900800c1d0340d043c44d12580810076070740c210118140800305071902030060b0040079070802410900c030026500142070412250305080c01410310b2030500005a6034040c05d00c4000343c203075402d0000420000045881c6200703000c10917403203800c20340c000f800000d5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 127589235 1250 127587985 127588001
    0x150109050603060f010b0f0d0c02060907080714011b020901060507120906050304030c11060f1e090a051003091a04050d02060408090f03030c0f060f0117060408070602070c0303020718 80
    0x40d26051310018000004400c0c0106822001000382a01e042e140e41180f80031502001118801030700070700140449074405018460080c803105009041c0c182c200242a1800401740448506011810980c5c900d0001803070410840c05030000c21500c0d0540e0b50f03d9001d0b240b640301090484520601c0c42800090314055801d082c15920380e035540f04d00303660315581d00340c0d441a00001e0a5948000ca6080c10b2541d9441c003004001030f81000c4860f544030b102d020b02c4a400c0307040c0584c216401c0d20040c000440a82c852240d44811208115207411810000c00e80035002000f03100d50180c2a8482c850300c80000d000040c500c7ca000e91b10a4040f210142c0031a00101d0710741e00f05540040c4526400c00540d8800d1800032060101d0b03010040903039245c901c003280900c1c64001200c2060780749410036003c22040d06a091446401400740260191003003802080c4107498460040000385480c03404242c000038020250b041da0503c03070340440c80005098403428065039a5102d0b01c6040011140c4218046080341c25001d5400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 127590485 1250 127589235 127589251
    0xd02060906060f060c0f030a0f020f12070804090501080109021002061e06040b030f01050402030c0612011a0706020a030e0709060f03060e0c09010f1406031e040303020c15010905060306 81
    0x10a03181d242c00c10a000740c030b0b00d102540c0401c080c00352008854041c09a0181aa0303010025596130740904006003103100084046e05c01d64006440d441080140800e054609504140c0343ca039031000940360501c1035000350f03045118414682400807516031015031141c42c500e4000c41d403c40c0d03019100101203a403044101d40c2002181e05100b41d411030504035612280d0010001480402c103042c621010a24200c0001081c5009030344440c00d02c004c3d400c09000030340d902e40c07080c0c80c41c519182c0018000703042d0100c18801c4401c80681d60203d84406044001590b440541c050401d642e114406c020083c05410821154034060188040000700d0840b28820001142c51b00c4001c843c4c07081c5035131a07042c000e03c0000904945030081c04600540f03035407501c0c1300324060600e4002184103035041044036600c0700101500c0c28081c61080061004a85551a6803c903d1182655140e036076903d41c81c084010b405840940c501c01e10804c80003201d180410f0700e03528161512031904210350fa88100801d0303030310801a03900b10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 127591735 1250 127590485 127590493
    0x906070222020703050d050108341701050702010b0f030c04050606162001020c01050409090c0324050c043206131401020105071b0c080105070504080d020609 69
    0x4001400c1001080079241c00182410700080004207915040ea030107540304a000800000346400d011800d031240d14054000c3c00001e0409049401040c1c40703c0c03d8000c2e21100100300d10034065072041c0400700704000383c0b00c030700c0c1c07001c8201d04202183c0b40600b1007515014059401e000e0717840c9a40c00c002d994101c04180090040c0305500701102400024807004e0051500040c0400c420200d6104196101c20030794400c1c0010a00c101c1da0a8152894080302007990b811500107a10700c81403682d04c94181c80554040030b03000200c503070b09450100e01c403040c282d01c000c04110f0352904d06240d018000190552102c0003910a010301e41c0c8800c1021003e100e64003600005a003041d000b40d29076000a0034110040307015a012001c07131070800000440c15008070600382c2c640031413008103010100f00000d503113502c101d081c002405181455807000c0c0c484065000d00c0008444400a500144542e2200d80e8006000d090001c00c80d6003080c800c0201164018005d00383c0c1407140746280c0d194640300207800b603c00ca80c0d20002e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 127592985 1250 127591735 127591747
    0x1b03010e0a022211071a010807030803010b0c0309030109060501050f01081905070c05010e0c040f02031e06030a0204090b1501141903141003031107050d1506030b07020c090a020906 79
    0x540c4551240c2c1c19511000d40d0b5903416130b0324003004000074002180203140d124142c04d4128040340715440d050b0440c5081ea009294100006080308040e41c0c15100303c405140d40380c220603644107256000340d10355a03a15601303141690050280030303849581a41c030250b4403141c103d601d03140159034000302034946e4800c102c568071a1090f0502143d100c00e40110092a1010122807191151070944119809005003a0410703003070805c55180c40c0c400d1041241240e94190301358600b03240312880020310003031805031307100302280042e03029a4180712400c081c41c0d00a10400003c900d40c14032101c1e81e401210354485500034210164900c3d0302807080f03800e6404c510150301d860102c004041a02c0002d800550301c0030301d0b841c2c8008a5101d28041429441000709051800409240d41001418261016000b641c2c0741c10808007403100383c44150540d1403840d04a03040310b401802d00c0000744020003003a4000341ca0340c0b450f001070000729607000c83d25184001040300c001140b601c07044418412480341c84119980701e1410011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 127594235 1250 127592985 127593019
    0x30209030615190801020c0c0109061b06111803250909080f0f0d05010b0a05070b13021c030e0609010f0f030e0d0504030303110712050304050f1b03010e0a02 69
    0xc1d82c48007a00103483d242c0f01c40c4003041010100760440e004090300fa50003040b2505030050402000303400f91070900c0d10301d01c040c0c41c1840180116182d9180145003100d4514130f01d050141e181c02c614900c1c540b10600d2980e811890014002c50780700320256a2203400b030301811501d03201082e069008400300f003d801c8034009280c00b450800034922240125503000050101b0401c0c11041400381c003440703540703424041d03803580f101c030105081700c00582010031001c60a01c941105954000117546550703601030f00e5008203441c0c0704c04040200c0e65032000250b11403100080049040485c510440100e4840d03150300e0b140e100d410003040900e014180d00e00340020003200e20280f07098419030801e00065403074180011030110f40364006042044984100002c02c40000f400c01c2055418031404042c07030301c142441030911a0541d901d00381d05c06400c0b5080f0420201102140910109006c1c0251040b5804102c400603000760480301045035001080c14030951030001e00b21000c40c0042280064580d00a041054110300620 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 127595485 1250 127594235 127594261
    0x5040c15110313080606010903050d12090f030512010e0420010e0904031107090204030b1b0d02070501061d060a09110417160605040b030703020a03020904020d0504120302090306 78
    0x4090300300724118840400c10401400200f074035840c203018518202d401d00c00d00c43e18148003e40242d04110455000b080825004612001040b66a15000c0c152102e1040800050b06090740054540580f090090040582101c01804d020b1425022900075030703030b1260a0700c0d03441c104440203030180c03240c0052011848081840d0304412241418050741140c3c1c408042283c2c2402183e044012624089d62004004801c01c2183c00030300c40500154a0b1509654610f070381c18502030100800c0d0001444003140d4045804192220002d18081c01c40d20744100e4100356001c0c09061181c8040300c502c400c2c10024140d05000001d20483c1e014162292a601e4903003048010002c40c840140b00b810107110200700c6200070603000c070540c1e83c510000c2c541c8034000d514012003017402d54403103403d000003040f080008800b4401500d5001110781801170321043c104d401500680f00d03403407442da440341c03000940c1c4450144139804103001d5402188028500d110001c070641c101c0c032a204d0a02e074954031610024100d601140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 127596735 1250 127595485 127595519
    0x90a080406210203090106080c1e0f150c0625081504021303060504170307080c07030c060507110c0922020307090509030307020105060a060905040c020f06100807050405040c 76
    0xb4050b40e6040c040c0b0b040440898005890780c80090751644810800014208980c821001d0111000010f442150000e040440c161800107030042400300c00441003a51035204607469031440402c102d50b40c002d54030031a03031642c03804c854450300281e190a0400b0b9924807107050b10035240054449002a446c0d00c80300c140407900c00900c0c60343c026002c004081c0f10300003c04401c0000c1d1321469000c20a420135103009411003118004084c1909814810008250380c403070b820a07040341840030b01c650f45100908007243e9014040c1c0002e45042e00b0501030046841c0e1000303000074880200802d440b013101d441420010240c1094607907000130002401114800c0c0701483d040070340726100404503000c042c0c1c0d0304089015180700f01c8080354290404010844c0554080c010154020320841d200104142029030140921425004aa0042d079540d0341e00b41090b80200105800c98003100300b1a9490b1400c040700074540301841c000d0800700e00404000044505090040c280120350090b1201076450134018510620700c24a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 127597985 1250 127596735 127596767
    0xc0c010608010e0102210c0307110a020301180302102a020c090403080103031805060f0a02150412020706050301050a12030c1b03061b0c0809030111031e090a080406 72
    0xd52000503016509104003168012800000b507250b00c0500400b08110b45000694040003890000700b058101000080341e40c0420142080d02040700c2c800480b07854000c00d540001c3d095860480070840a144040e520207405100f40d0895052860b43c038031440990f08081081400100d2082c40f10030310218990401c40e03400190b10454495a0040340092090603080d00c0c00d4010481580061003031540c01021a000c500b072641942007110328041c0800e4452160301400800f14101290620040d40b080c4a6210450440c0000000500701820250101c1c0f61070b08a50016100da0480020060701070300959040707480046c80070070041c2c90401c0b102d8005040d01011070401550108500000301c0300c44482e550208aa800703010b84505524000c070072288203503000300a2401e01d04225a0156126001e0b130a00d070752140e42c1f50b864403007040106e40548800c00c507000c0040404010090141c280d40c00e82c41590711309141240c01600c0d41d00143d611914402c0e0060300302c140400040c0181406000740b140c1070010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 127599235 1250 127597985 127597991
    0x30509030c010603060b01081605070605040f021e1905030a11010201021306030510090207022206051c1a04020916050f04150e040209180c430b0c0c01 66
    0x101c40d5070305003141c50030f07001102c0c0e2554031000d0f003541e9640048c03240d1b404450504001c0c01c0000c0341c00084d2250090400c02403280340c4910016080000c0c0400c00c4400690141c039003d100c10002849052842e001f484a500440541c48102c003041a029141c0b0100c400c0074028104a0040352152014400d030700f104117042d5034007088201c94072905d10354010000d00103545c001030030b8101403801c4c060308211070384090402c82c014406070001d0f9450002d0744850300e0280031418444108900924054040e5501c05507128500c44001d200a10b585205480760a07c900400300028242c0c0702c481b2801c180076203029420440000c001192203a00f0381c02e81003c00b001e8205541051204055405a41e00503040440c5032284240e08041075508417558001c000e01c1100c00307604141e250b40c0400d100b00c504100041d81154950b0128441d81c1125045400c40207002c21858a0320007204c07207015800c0c1a0340d190006544107003590ba00c038100030383d17024001d0540c8680c039000c0c1c2e600c6544546550ba04841c8860f03000c1d541e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 127600485 1250 127599235 127599247
    0x160201120b0303070c1a04062111040b0703080c07050601180902030604030f031b0f0c0f080708040e0a02070506070e01260108010e010b060405040e0a06062702160303050903 76
    0x41c040000d45280d41c45003900c44051810b1050018144641c11381d940f00c50306c0709020500106800c500280107402c1c003c00c0e038404507103000b141d600107810040084071a400001401084400c1c45400402d0707401d010b5101e06012391241400104217204209024115400c480014031100e2002207104c0034040882c003011980144580001c0c0c1084400e03a02100031840101c400d101140d0580100900380d13205540a4604128100001e4032030018081e4880410880800060070060803d5a071010650003400d800e44854007440c3c078048a5001d03010350541044440d001844000050027158410b13079000c00074100c16115000103490001142c0030180c140821529400c404150a281506c2d000c55054094500c0b5450812440d0846400300700002007641061944020b6403600030880301201d1007900c00181140039040400d040081d101c20040115050082c00180031000e6813007224000f410854500d18002540c1000089114650403189207640040914010901a5001c02c0c0d0003030b640b0b02620320b094 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 127601735 1250 127600485 127600489
    0x7030914010509030405040f0b0d14030d0609020301060e030d050403080d0e030a0206040b0709030222020f0307020a0b060f09042d032336130b030d0302160201120b 72
    0x82086420f0015a030000c582001145410b020700792054621113400c01100500001080f00215122400343c1b001410106407071100108100300c03030b040102c06008100c02d5444d580383d40080d600a1041c1c00c002680349084a4891070003084850406035a600d0329031802e49940d5038014603801040c40c40d40038642d550032141d0008020b000a2002c40c882e80c0c00740035640b9040c504094400b402400010401c92001c105000580f50b440301d00d0002c554410380030004400c00c0f005100a840b4070000c0c0540f001000c0300303010a00e070300024510700315407058901038426981d41040c004100080c0f0001740d4802c520340041008038400102c900e01e441500d0401c81c13448030601002000304d0180c508100e0000311004040c130b40c1d4007603031910300d90091041c807a03481c540898058210701050709040c0c411703200c8141c003034a17150240c043c41c1c00281d0307548050445803400750003274030980050151900b91402402466040051244240700b10b0720400c0003101d00310300b04003c40c1c004507140c000c03020820401c02c1c0e8904dd011565 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 127602985 1250 127601735 127601741
    0x60a0908070609030c062f1315020f061e0c13050303040b071703040209040b09070f091e0903200a2a09020304030503280903050408070605120703091401 67
    0x180d8001c5e201c80182e8030075440c0030320440d90b0000c2d803c00401c01520901507a5140c0090048201c20b0b01012036844503662004040802032951000003d0170912182100043e00801c500503c1034042c01582c05941d01d04083e400c400307c44c065801c4150b204400052a02200344001e80b0030b0b139441d078000078110ac1d01d804c0400c3c616405074001641907072002c1000c00411030f2003840e174200c52000054240c00c50500c4d60100300c030030901400081c043c0f04c43c080001c8144004222260040c444111300c400000d41d560a86002010080c4c0c2d0010060303440d41d6480c0c5404420b00074039101c154103507030b04490070b0f8404501a104e03443c5000031340098041c541074500440c070040198015030130f96650a80781030810b2201d528020080760b0044071032600500c208004030f078024080d40d500400c844980c1c07103d13030145414651003000b40190080410300e083c80d804203242d40080170703100765031309031040b1407050351035410948080c0140c2d00000c5004104000046103284203400442a40d4400d000024005504002441c25 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 127604235 1250 127602985 127603001
    0xb070302070c41090c0705010504060f1a031507090e0a0b0306013212031803060c070f06110702031b010207050108090606040c050d06091418060a09080706 68
    0x360044450280307042e0741490051041c0003c2c1e800412031440c040314106481d814000403440d01c034600c00d20024038941d1203502261242c651110003000245024502540106140468a160303940303010700b010224542036200510200c00240240740740f00016200c0004c0400090444081003412034001410107490642c10303000b2082c008002c154607030804249494000140e001c9403010250300e41e810400011080c0c0e0103090b040c800e182c03005c0821500081000d00101e2101017030f0f54800040c4041d506075139907a1055240100b1030a4601c0c50301c804080c80e2060007085000703022002c07030f0648000012869402a4843c100182c3c4460900015400090900401e2804807032a00c045500044081d07074103015180c0905000d003040002d609084541c2da513030340c000610444c01a075a40d005140618064019121007c000c49010b008031501c88030020003802520541d1240c0e0582000403919840115020241c1081003070010009a81c404540f0300c040c210022042c2d40c4107404000941c0890064040c10103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 127605485 1250 127604235 127604249
    0x506150d0b01030209150918220f0b010611010e0606060a0c1103070807030c052d010c060501090f0b0616030807090816180603050c1905060310080f0c010c0b070302070c 74
    0x10b11f80c0d401e00244503101002d6a40b41c15949500030800c00c114820300c9205901b0300b03030480d1160202a40340f0b07085559400004000e0000c2c0462000056041d0340170401e82d05450180000f400001043c0000c40d0383c80c842a100d196201c2814819400d0861103401a500c41a000d0811a9407440c101d0010074140447c54005501e2a0060142841413000d401440c0e00282020b0b0f4490b948070906120701c0950204001040a000307901c2c00484ca182d031b1050380c50088450704044100100c3d40d40f406223800605020004140d0b86040c00444201ea03d08074056840c580100780e0501440c4c190341c2d50456440200819140900205000100350848200a07031410705903d581d0480d0182d0034000609100c090b11481a6070240c1848003d000080300070880d0840700f20f0603190180302e01c2e000c01860081c139a6640160390020004010000c401c40c002d803a54003100e0b840b00c20744c1c40b14000030005907217070000700c41c043e07021412056111001842080d01c055210106180042c240b650650f03030503c01c0c40d601d510000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 127606735 1250 127605485 127605487
    0x3040f080d260112230d110304030f0210090306150609170d050306040f1e14010f0e070e040203040506090607020307050718060305030f0a030506150d0b0103020915 72
    0xc20240c1140d4014551901c40b00003890b040000c141d1480000014044e901881c005025a8010001106601c0309507080381503880746005181003210750780d0b042106103440001c60b034048402d00c503034002c81100c05136900708408681440300c0e902800403d00749000070408002c4500c08c0000851201d02c102d06102c41403c80103000c403480c0c440010100d0619412810700c401d50880c0c1201101d00020b903408010316141405616640c0f80342c0040d00402c840d40d40711541030300384003c402c0d46003404d00361034000f041105401c011041c0981d584803c2407400b40200c07041022009000d0104800000c5080e40c0100945065000e01310080d010800b41c0e041960111204d81c400414001640380c2401740c0352380000c50f48011420195903440d11a43c80680b480b541030f0f050031100c0280c440c0103c1e07400c03040c003454100c0f0440751345200309441005580d0080c121103000034030700713800304001d407a214940d240c6c4200c059080c5414148100c61540080905030b282a051550030050362000c0d440700a9607000b0068150012 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 127607985 1250 127606735 127606753
    0x2060403080c07060e090403080a1b1206060e030a060207020a1a070c1403100e0c060703080a110901140319060b040314010204151b1502041701060e0c070503040f08 72
    0x140b45080055001013081c031900000310081912094401588070750145000729071516002606801040002e07042402c0a1564010541050308410b5070850b450190320100001c0f070783d80c102110320003119030380070b41c2c542c02034070b400d80110303015802038400140000d202a034135590394900000781e14262140b00d8104103021485009101c00071500e1001071110f1075800710068241c0d00003940b211850b0800c1b0201da0780e25200618080300810002e8240c0c07001401c0e10343e80d03c805042c040c100c0c2c0c0f012a01c2c08404c3d410700005061400446090b556820f406031a0f1144010221108ad01c00f030704020f0800b07032038a00360502c0b01c00b000182d0040781c4c01460355114060f83c85041d41030450700300c48410010300c503a07070040100b040f010041d14895031004041c0d01d007500900c1641c9019901c01d81c0c141030302a10b54020030709080b0001a00782c0c000e0044814203100c0304c0c4449040340d00381d4241c44288c8240d2000e00c1d00040011654403084004000a601c20000d6a00c0d00351119843e203941001030308500b00c290311070707204 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 127609235 1250 127607985 127608007
    0x1031101030c090b03190204051905030d0c0320010f06060503101205211201031a0906150f0402040306140414060405070909060f090506070207060e0604051203070206040308 76
    0x503058102c401d480c00e080c8480c100304040301c0701d1001401c000444c0710f1000d902c201c07140079a07043d94040d0500811103808000582400d503d010024090a0301c03d02814120060701c80c00b54003000c0110391300d17803501d80c40308481c409504051507090a400d4041c0d504c40c9440c02e10700e41940f1981e8040e00003511015283d083c191002c62000c0d80c1600203014140641c0090740c041000055070b141d00c1e035081100c0304114051440d141800b802003040b8141e07003a40880000c41080840194100d81c09000f00070405242e40d0300b8000703691034609271900f11a5480150350b6203c0d6041400344100c504501810140c41e0644d03a039544c108841c0701c10688035180605e0703424001000f51411012042048031001003401d41425251280c45103294490203035020f0380c4801c900c0030030080350052070442005110812003046c49081560315103800721040320040c060b00502051180c0142c14030005180302500c01418903050106100d8611400300c01421130340300612891005a0780c01c002807002e1840b5006454840582d00c030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 127610485 1250 127609235 127609241
    0xc022b03090303020f01020408191a01080102040305060601030207021c0c050a0b03061201090803150d060e010e0f0f0703020603060a08010c021011040311010c0f020306150a09060602060402091e0103110103 90
    0x404e21806c0e4010041004568400039891001203d5010309102d1501c141c41c06500d188602d0025020500c0f00da0000116a60706501403c12a4055001e480150707960000440491186050080d8000d40410064044140e016110f000451250800c0000107440d540020403052050b8026020b02800100301700081c14181402c01f401c2c02204000c2c0700c04115907541040b01d01008000d1044480b40e0107420b00d0b281d43d02c00700f9003241ea4000108008402400903ca40640165500d0f13041600c00c0044a44400200082020750348140401510300c182c1181c0c00c009a50340302500c00c0c0d62041c4815808100e03004c0c284992480d1b20305980041101003c440c40d040160303602c0d015108038a100602080000c501d4840b4694075201c824649001185414a442094003078150b402075003500ca880100308041d5046200840410011103014071400e9440c0c80302c2c41500c41e9030007080300580141c40070130018100156000d4000b82540d08234500c0050b040f00000d25400d099105030b60040d25818008450b5030144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 127611735 1250 127610485 127610503
    0xb13020c0c0a030c031202120f044e0510050702060f071403220308060406080a0206070b0c190206180d0c02010f03020d090b15030d0c022b0309030302 66
    0x245040d0103980c919144c02044852038030024000b41c4810300300015070352080c0018070158208078207207a01c9503002450803090750002c1c0078903103108a000c142c4070400308081c0c032540e481d101080038200d030740300340c4481543d07040480160302110401c0d03001084001920030b0001c000310346030605000801e0f00e0201c80c0280340030005461210801007110034400200d9000110056a1010299160744c985404101c2c3c40180284c4e9001c92540e8116180c0504050340901058000c482c05c42d428011641c50b074003501d8a031030000c94000e50104040000d50000741e0480c031140d0b070040dc4141c03160f007051a00c0001c100d0340d50700549680b0060b00041c003003107003028485034a2030390114000010705615412050140c9580e0403460040c0c140425111580000d52003501118188625481e09200240e030354039185017544029109002e40144c986501c2e0480e09002402c6c0d01c00200640d0360804000700b54082c00701c6035841c0c060802c030348594511180000300c104907050411a00c240d03201f0a40b03918604000341400707405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 127612985 1250 127611735 127611739
    0xf07020d0c030e011d060309060603100e1b010e06030c03010305010c090303021f020c0114011802190c0204090816120e030709111207090315060b03190b13020c0c 71
    0xd42401d9000c41c0d80200202044442800d0605c2402c5402d00340a14401690060f41c2c4e00c004000700700f24882d0004224140207000c00da08440111901c009000103443c0042c071041d8185c0c0c455020b12020040d44c0d04000350785101030402c012454645008101c0315441220407415100c40000100104002403240c241d10300b90a01d4403e1541c0d08543c3c3c000e485610080076441004042400c0b0a0251000d038101e030000107600c1c1c0208516a100720303d42c1202c800910401e15200041d854181c0320403258000c803184149540510240307520743300016601d02c044880141d801c25035130052400040c0b06000102250f541c00b03901400280c0803890300f403020401001e180340c00c1081c95504108645c070001008000d071075412078046120214910012583d0282c0c0c3da036030090800f82030070b0045854000704c1003020782e40101010400c07130003100005010f68900348a245109841080060000492644101541160b0302d45c0499001c0b80b10300000c600030113490b14042c0c140da0001e003090943d07001b04a0b00c6030366001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 127614235 1250 127612985 127612997
    0x206010b070206030105040222060c110402031e07020304050301092d110f06130609080615030607030b06131e05040902061b0a080c1005180c0f030309090f07020d 71
    0x41e507010603114041031050a01a54000c58000441218000c4040d036a020150140c043d0703980d515401044428014010383c0c51a02510542070981802d0007103030301c40c0420f8003031044115040c500400c010000280f14170110300040c84085115502805800c0b0f07032502906212800c84003180c40307004046036000314005c9003640b82121800289401c00700100c074203011640111803410600100d8042d00c56008140b103c0c1c081c03100d001c10403d801034103920a40b0002c2c011200c2a40d034106204041484034051250315611000000d6100380c42900000d50606015101d241030000b10b4200580b648280d8100084045420705420b242501d1a40400002c04080f070301031104c04401c1d00461010300c01c0f45c8076400d000070140c48681d090794080001861044d482040d465031181c003400c400303403241c60079207a1890803404c000100b0818080c2e404101e11906010f80074003440a640d208001d1002000100142c0501091180c1d948076038405901c1481100d8034100c3d84240d14003040001d0410300c03075034028004c1c4a0b03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 127615485 1250 127614235 127614247
    0x209010c0210110a0c060806180114040f0c03060314070506040b03060607020a120c05090702031b01060b070c050a0603020f0f09060d0218191805180a050d0206010b 72
    0xe48419421401501600c0101555542e09400c980d071080c0e840399042a41306a840d0402006581c100e12401ca07105035840b040d0540701d0f1001c0040c00655000d441c111490018014095a040c00344000b56074100207200084900c20394500700c1c04d5610244641000c288d4070b92040080c891840480020140140080d0982c0e03410640000d816000d40c0c000c0d20406080400000d0550729240d084030038041d001480c00b1a40355560f441c0c490207560100c0e0131900c0d400d08000020755400d007801c58500420458010b0f5080c1400c14841d01407241c245550a2010742d201c00c0000340984149004259260007660700320040e60070203061003044203ea40c818001c1510402000504120603070a5607603c10030740c1142a0703035556440006032103000d007005128240d0301c000b4820366450a0341840d003483d1002522410450403070b41001200021892280f404981d00410106003d190150b01c030a900c9104400d541001c0200040308610b080f942c094100c0e40c590229160751036a6404200c0ba50041c114150300a1901d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 127616735 1250 127615485 127615487
    0x911010503011d04060605040618060f0f05060c011b11060903030609011802040519031209060509210a0506041704060c0b04031b0606090c0507200a080601060f08060301020901 77
    0x301c3d408919460390307150a00882e04022050300f0090007804002c0060000940701c0701d02c0c46600c251680c2320302d89a40741400000d005404140c005049604150640c807540d45001c042c880c241d4014002640d4a55940c44800c10000c0b2025084000500503552141c09465031603105140c52406030042420354014000c00c0f0407699414491819510038841c10405001d1461031070000c0e028940001d9806010f2504d807140210b020516035080ba401000030301c1024465074410380e043e803180d003c0d200014104202d00706207400c0c1540c144807404013004400400d000f0f0721405030304280040e10f088450307422480501051090604081500c41120040d407403905280000140911000c280000e100c42181c2e00000c1c00d050081000c220501410074080c205205507183c00c200030513180c024038920318034141002311034620a07002c1d595800c2e8007503004220780849666201c41140341c0845c0c1c0754402041003000c2942c01003407150500030302003900e4070b140342c40d605000a005907100a101ca030003031784140010a05a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 127617985 1250 127616735 127616759
    0xf0102031e130305090111010204080102130902070c090e0a06020403060212010602070b030f041509150f0603030c081810090501030b1c0b18120903060a0e0a030503091f091101050301 80
    0x102c1ea060902503030380e001ca00b0042c0c1c0c42c0d01001190342d0b119403003c100014511010740090030703545040c541c810500d40d203c0720903004a004070600607000c5441050301340540702c0c0991110100010040c22a48c0703500442e5565070030b82e0b00c980c10860700ca40d00442e000d40c0210107016480e000d4401e070300160142d142400210419404005c12001044c2c1e10b09000ca4284800300100b100d4040001c1d106004009050804a6058003000d1400b030105281c060124009185880b580b4240c83e410b6a44d0030b1041d445444080305074201c0b0a224a0110007003114040d03a40c0d5407440c6240e0f0321526160568028609030024040b03030003850440780125410f031484810301c242c030802980301c168050b1203540c0c03e4a40c0f0200351000564254407518501c15034201064640b0b140014040c545000c41c1252026031390600f084082d01d0340716441110325803008120500090084000e1035000c0480d0341220a07061180e904618000b607114018002c0e03d40d110100d5090200000c10584501c17000e00302907145501d80301c40c890351 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 127619235 1250 127617985 127618021
    0x110405030d03090606091404120302091c0212011404050106080c0907050d060f0f1a0903030a1b0c0909050d0c03081f030501020301030809010206091c0c11030f0102031e 74
    0x101a42c0740f8502d000c122181c0e20903170140250484c10440c0c51030f21201c034041c00006072810f4400005015084403a544a40201d038904200603081342444a0001c10030059000d451404a030302c4000981c0801c2030320130074850404142e01a02e04440030b818141000c2e800c403100b680102600d07410801c040d0000d03480341c0c4007041c1c10902c54030b0141c1d914183c1c030700b0450041410380c1000182d07040c40c1b00d002903c44c40fa0304880e000c4d1052195a03032041203880c0c80f989114403036103030764a40540081c420070181500555841c00c2d060408003004013410303c5030740c0314440d034400707604548443c542d110410000e2000c00c004205011a180c1410020782e102c64034082d010610040044880302c8480000040d407042d090030610095a00200954481d42c503483d1400494001e4444140140f0030100040d041c07000c00200c64000303004030100d00e404595140360460f100c243c408010f640b40380300202e01800985080001c810558509000143c603401c160100382202000440114040344844091145041d009010384403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 127620485 1250 127619235 127619237
    0x203270601030c05011412010602010b040b01030b0904031404080109060609050708060109030b190e030a02010c0503250306050613030618020609060d110301140901050105071104090302030f070510110405030d 91
    0x80c824002a101d45064447c2e0b0742d5802d1400002c8000244c01c0d901504440f4039500102c80500580054074011401c46030945400b0780d110610201040100e401400300000508144841901d0aa00e900c9140c1c25102028400c0321465034030f200c1000540003e10440f44c2000d01407a02e2005d40c01c10724002020101c003400301400340c01d03040002c82c5013000d806140c3d0708400110503007882414410b40d549512504030740803601c05542480000c18030688104204c81c491100c03040724040100c4c1403049828036182041c8890140755030740c3d1003c1050b644d04c2e00544120304903040f01d07140c80c50451034410140e48030380441440c0c00d94010340c80703001aa0f64500b0b5440c2a04241c6605488501c020a103c001c0c01001c070090b00705440c000000703c1c0500c03040c49621070091080e1600c000a03660741c0011102c40c4240040507010b6041c0b031451200910701500600340d600c0c00380c0304a904009000b0400346075680640c808844641c0100e220480224450180020b812804c0d0340c2182440d1819000c070b501c0341e90490703041e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 127621735 1250 127620485 127620497
    0x7020112060b07031808070b0d06050a080a0b070c08040806040314090105070f0c0506040b03090d0810030308060117070908010509010605090402010503100b030408040504052a0f0705010203270601030c0501 90
    0x5c50001c10800303243c0004c1404800301c80189984000000c0140e101601408015040c4000884c0700e0524410040440394280c0080c00054451b4032041d01c0c400b40075050f1001c0100550350300d00481c6048010f080500043c10241400d170925150182401250310703c170703054212081c0300d405100ea0f084426254200d400c50383c1d03a6002c4046140c140100035140d0401c076800315010030045805a0b5500c040c610480d0070034111402d509800c2005c1c0c4d0308020840e004aaa010340103010310019100e41c00098000d001030400c010504444030f80c040e1412421105480041c52006003001403000074001c0d01d4020000c54003c2007018103240105059800c020406814444c0000100e0f2031031038000031800060a00f000314646905007480c044da580c0d80b0030310450380300d1801c02d00803c00c003807200b80c4a5544028540e60341500b0142c41101060385402650b43d5150b112030900c40100410b100307000841c8206d80707412501026807119030160080710100e10041c00780f03078028401400040c1400b016102580e00c242840c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 127622985 1250 127621735 127621757
    0x4030806030c0901152303090102040501170c0912010209042906032e1205010b091e040b1302040509010b01021606080a09020d0f060b01080919060513021507020112060b0703 76
    0x1041501d400c1030300d01c01b80c43c40010400c4503906040d40940300703494003607803491107191011000c5c00d92646c040e101054807000801490005280c003401c0055a4008200050308165030b001c001342c2165904003080e12201048050f401980d21403221409400d0b208503181410340c20020071054110901700c07611000c1103050340300c1c649190ba01500a0009003d042c00b084101c160f540f810314080c0c846440035074084c1c002c500100f40c242182207030581e00540400043d400950344c40d240d1601e03c0402403e031400b0130912210007405a02e8a01489103d4007081c0d001180c00c000c500e000a00d0700f0142000500b5211201c0424441d80d907006426030b81195011501080304403003800012110041400c000704441141d400040400409411100d9000d109803a10b48255a8520030540c648541c5c0800a034052084c00c0d40100081440e0310641d084a66034200c01c02c00c0c80d007903001c40c2c15040c400f20030003011b00380410f44000315a4040000072099180c07080a000c080e01d00140d0301054041e030400101072282d40004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 127624235 1250 127622985 127623017
    0x10b0117150102070f030302010207120f051e040b1201080c04021611010e040203090f1e0d0c26030406051005090105090a0915060f0e070f1803020904030806030c090115 74
    0x102c501401040d00d103250b10590b2480d01078004cbd44104000c60307032500011600900c26026001c8542424055256240307840192941010400c008440d00c081c0a030f002d000208459503e240a0000310804280c0130741c940d410442031a26101007403452502c01c5004000d10540a0240b0156100c002c0d800101d030321406134607c0040e22400d088011682c0c000780701004100c450500011100050b081190a403161401001c2d0303100e0340390940d003415102c5513014103402c00840c0e11540c0d202000a00408201302c10b00b0701c803204c0811403180c43d81d1400007600c003c0140820b1001c2440b075a40c100ca0902103070040d00b031810000c0340002e101441014450f4020f03400003502031005070881c1800a078044110140d810001c4034201c000e000c0f500440007003254040010800d82010103106008107400d498116038024500c03001ca0f081e044000d8241e1101c90ba0741c50010050301ca4000236070003180310361141d6074103107048810300d403405009c40d4056110350140801040750401c60300a1001040c220300c0c180d4120000525 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 127625485 1250 127624235 127624243
    0xf0612150310140f0408041701020c1c0206070c020a0303030504020607020a15120908030606030912070515090105040c05060901090302030f030316020304270b0d0b0405010b0117150102 81
    0x40c01a01070244078050101d124459211070301410f60103a034943c01d51920411449092030440c1d004100800c00c000a00c01c0790032640551f0102010710002503d40901c20810900b009520340e8505240c0c9000004528203580511156038408030030318080091b11843e80005505007014440030b002d1640d240d01180642d2600e400322011950054084001941d0f1070005030b400303c07406c0d501c200002e2220103000780384d0b05080c015002010b4002c030009003962101c0c0d041100315400601034414034400e480c15020b04a4221003c1c01c2e00a01a0002e000544008000d00848503801407151220780d15020030840096600103110065a5050700c01545a003620b90060f5112903d940000c0d501d44a03004001d040d03804c000005610078003207012540c04a0204003000da980e8081ca0040401d41201c004861200d0903004215141d140c44402000c9810031480d00407940d1144078810913a0622900c100704418010240100780031b43c0402c1c42c0c21410700035071504520b40d00b40701a0652069480541d116441680300304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 127626735 1250 127625485 127625521
    0x15050f1305210609010e060604180f052a030a0303090804050303040b04150512011401022d010c0519031a030102040b1803070501050433030605030105060f0612 70
    0x2e031500040c16620850328211012912101d549403043c3c030000f50300070a0601803c041c454007040100465180c000c200030242c5588400c46110100042c82480407a0b2a030b003504c12168015409454010314008480510303a10952420400744590018030045031000100c0500b89505403600280c140b509141c101d2061080394403166040c44042404070f204c00040300100210384941412103000200060305071554024200e215264100c1040100944131410082c4040c0b102e0500c19518103100c001c3c05001141ca2058410a40451040003c01c1e03002091083c1542c208035800d1450078042080404080455100c0000d8101038030b4502c1110390340d186003041c0f0386000c0028000d548a540350400f010072600400c14440c0d8012006c0b000d80002d05011500500340c0c2c1c010f9403440e19003030900118800d10308020b031036005075030007030210003080403100314103a0701d22403461750040398252800c4100744c2590000b41c9018031401c103110302600d099031100d080720f00065090440100641d60700360760580480030303c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 127627985 1250 127626735 127626739
    0x7050928031b05030c120a12020f060a3c0f02270a0e0708010b030c0904090503030601120204050a26030d0f0608010b131d0a0c0f15050f1305 62
    0x40850190041002400c0000303030f4400350121001e501c0b0400c10009240b80c1c1c1d00e00003046030400b1904601040ca40c1a0780540305a26004844400540d41d01c40b82c42c1c8102259010708076555150b09581362003403507448104000700d280d0b580c264080603140314508040c01c4502010300c5651042c00e540820b400b501618000a404510038000048481032040802e12418000b84940b020030004105d00351240301d400d0140e01d607503844080390303030802e00f41c80d070700394409488150b110b0003e100391700d6295694007074850f40d50701c500c0181d030300c070305000d400502001d9041c4803466500740188414812901d030740002c1e80440da800c42d82c0e186401e1880005096040b44464098441d0000150102420100c0e030000e1441004041c0c0800025568204403801c1700c14020030700b540251002c0da6040e0820f60764208130701c82e1201404901c010000d13190980d24040e480a01100c904040c400104000d4041041d44401040c6110032a00100c0c2071090041c89441528071185840390017052000c0a0136444413100090080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 127629235 1250 127627985 127628003
    0x70e07020f0f010606081305060105190305011802010e0a060e090a02120a051f03050a02090402060d06080a0203061b040603020a051b0109060b0102030a09030f1514040b0705092803 79
    0x1c661140b9029100d94020440818490008901c843d42d00550726800d903a005006021182d080604020908074200074554403e8140701021000c55421b210b140f240308185c40d140d5644000030310025144801d405040c51142540c080104101c03504586208156041294014203560721040580000e00401201400c80000300040002100c45035102038041c042c46142c00301c0c040c498a06140001c151030000410b25001000a0001414160101da4115100a0080342003020360242c0e80d04490095000c03d2160344900540e4065041c03c0c0b0200b60444480105914440b0780d01000c000c09100300c0c420301c010140c1c0001d041c4a900e01c50401d407a4411a01590b03800e11006a40c0118060404440305941c61480e24420300c45960000044841c40585600c4140d8401d1071511441c003980d2050605460030110f898100c0508030300c034881c04025218440c0c1d2718060382041c1c10440c404650042c000380034420200482c4040d0f64800d0541310220400c62841b00400300c030030009622910941e40000c0080d41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 127630485 1250 127629235 127629253
    0x1b14041214150129120403030b03030c160524070302010e0106150809010506100c05010908030a0e07090606120f18050d14040312030b0114030c070c05030f070e07020f 73
    0x101c8101c1142c129880e41c401400c1d071000410402070700134030b90540c0b240400f03000c05c20000d40c02d8602c90001e500c00e0207400e001a92240ca40b020034190740c03081051210b03d4010100454411070a002c55501030041611b405041c50300008052045c0d8a1810111421480c00b20358081018400d4001400d111504030003405807a54801e034442486e4100702202e0b001c50104800550f1500051140b148960380040030842103040020040c7c0e05120041e109881c15500e0b500d4020105000700700450042c4007010300042e807030141494890030098140c0000f01c04c1803c0c101c0803c181540442075400d03422040100140c60b02880d4440d40080594403c00d05880340c0c600c681406108001c078840401241c1ca03111902034940041412600b840f0700d000042c45c0404a030283e132040c5100764005800d4507018102502216500c074281022500201c480b05001c01000400e40c0c1046581c547c1800140310a43c01400c02d0b50145000545034221030064800b820a110002880c41e4400c22003001040d80c50401c0d0b6407140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 127631735 1250 127630485 127630513
    0x1b080a03030f0c050307020607050c011418010c0c051f090f0302160f030f0605040c0b03011e15050304240c0e09010e01050918100f1b14041214 63
    0x80402d140b1640050701d000b04540b261401070040703d00c1031407150301030203265031032904c20303079894005a12141c55596a41d0140c3e42e4215003007001d80c080c0f00c0204001601041c401d80450a503075800340500d0400c000201c41d4000120000340d500348100704510248284603188800307000038640b20102030206a1146090020701d6000b20742c9036418917812030020398242c2c40704082804003074148030003004409030f0000080864640d07801940c00510074110840219901d0440c400184c000ba040308903104010700700a5100c0c070030601c820f4000c0022421107800709001e00780251080c040148042c01096260041d83c50080194826a00c54042903070200940010808003d068a02305045240518444000804c1c04001d079142c6c00d0407a02e0052469802e96940c2c0c81c0050701c60300d500c40b91280d900c540c05070b18003043c0c01405940c0980c00701c0180040d00700c544c031410101c070021a1043c24107210f000760045507100d120700200e5056403059250030851700d14524080c810462064407080d4940240e1600000c66 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 127632985 1250 127631735 127631741
    0x6080d1806120b06041404050a0605100315030b04140d0201200904060302130207020406052e0e030613060c0c02150711090408072f010c03050918190204080304031b080a0303 76
    0x5480701f6101000180d8030300c20450101c1e607040c091983d10600601003070503103a02ca03401c0604651090b0902c03400d15552680e584040c10b1090701e0489008030700740c107a6131000340f080120846409091000340310140301c5098200c40356803205009420074000094405441d1074a420000040d030740545030002034a14034220704000e4200c0b182c22480781c2d0a06030f00240a14090405681614600f400100d0082d07074205000031420020360001d080c00036017141d5000380d640c00d0007164403840c82090b804400949070300e044000c0720f921214000c20301c4404183e400143c0c0b2503200084240c0d500c6051b20b582c2c1c0d035080c14005400c90034400102e521030424000c01c8200410071010b048a80d124214203240104001100700c04d40d0b80f025036500003982100382414a0b90312400400f9a9503000341403051078000500d01080244002c119074601030001581400000b03004029060304403003036240d04605090800320312545030f00c11072201820b2698103904a01c030f00b00459000310002c001600864420005d01e140103009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 127634235 1250 127632985 127633019
    0x70e060102010b06090312091305010b03040c090c0e0111030d060f03030207080a0803061903080309010624080411030f0f0a1203020306220e0d020106080d1806120b0604 74
    0x65003003005810484c02c180341030f50803094000300500010034041d109030300281c00c02c21a680c2c1c84000c540b03480050103101d05c121400380c414090351a640f480e09040040e1189800d92003030324114540310f601c040855006940c16461082480c0050f00546085035541c590b018616042c1021840c0140002c1c101032091042b00c00c40f2320075026951250f03a1140800c1e150104c01e90060880318040000440900c3c0c90396070725401c032405545002030103850344c03070b00300c3d15400403200d0380f43e5695650028049001e44c4524100c03c6030381100921601420b0810081905602910042140000101c0c507110743e83c090001080c280b102208490728841400c80a0307645224148080d5102d4043c03500b44070f0b102e8400d000700c80c403400014000c8010f00d8160300319103010301c13184042c501411f96501d01c030110840c014007851184404903070004c6030b82401c007058642407024004280040c800101e90000840000a06540407502c03582040503600102005031f0300a0281400c995038005000a004181c0c0701d422104000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 127635485 1250 127634235 127634237
    0x408150118020c030f09030304091e29010e1f05070618030f27090b030c09070206010614130b04090c21021606090305040e13020f0d0311070e0601 64
    0x1041c04898215000c07481000b18070b4415130403c00502c2c2c50106401c0090a070303e18080e040300d00d06540c1c1c4800004a860303584440c2d040301303100c842803202c43c001c9020b04a9401220038030303500c08040b00f038400c40035a43c945032a1418400048804d120310364420000316044c502d99122040803919001d40180385500078241180d4103490008942c80320084070034280300e071640c540c032418a4100c040301d058031060351165900203841c0401400041080982d0400001800c20030000300b20044c1ca40c04040c1440d0203c0680c1e4010001201044151a400500c80341120f1142c20080640080c26a031050184161011600314000e5414009103d0300c0c007200400845203940000c20241280c0e0b10112103006070001818807101c1d5004440080600580c024103005187da43da249002c41c1b2665071078207032011a403064010400100f8100070030801c501d4680c3c1d0040e49199008070305142540010032032519000041d0290506420b0141050b0284900c0c60110485000302c488299590003080e882c13601c2162076074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 127636735 1250 127635485 127635509
    0x818010809011a060c0f0f010b0f091314070e091b030303040f030e030f010f0e01060b03040f03050a03180f120f02060c071e050102040f0b03010b07030c0804081501 72
    0xe07214a60622031031850b00300120840059036100d00402003241c000c0c0340c12488500903164001a000c3c82004041021041e002c00450110059410014090b1881001c0e038080c00d001c00400040007203100840700440d034807008040f00e0050603040f003031800c013464101e803204024070300c180140004d00049645107004070060b50595a001002450384a020a84000f8094401d00f090a07002a00810146901003800b404491007050000c9689003541e04c03640710004899590111644400300a00a20010304401c80503039145007010398502004811f503074400703002c1010100d690750b201ca2294000502450703030b84a0003041c000d05800c0c40c1e41c20341014003086688d0032030300702d912040e14015500c8050700107654000d080300d0ba44241c2d80c1011035019030070855185034490351001400d102019410642c5000303c00050b1100d0800c1003210090105401804c02072400344010000c00c02984100c50b08141d240c501a0a40f00312403404490900507a0021103080c01890241c010001c0000341c00c6048405403c108 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 127637985 1250 127636735 127636741
    0xa03060317030a0c0504030b06010f02010b0a1d0105030111120c04030602030c0a0e100221071a1005040209090610090b0316200c240307080a0e060115030b03070308180108 75
    0x1501c5e03c0c0300ba803100611849126000640c0c0750b00404211501e40321900012800d5904040058008120ba0308146c0320f401404900000340c24100480314050602500204541304200d100c5506034043c1402c0c180340100f000c00001c41a2404d802a02e0080d0382c03100d01551607050180001d0095008005000c2c00500071140514161030207040640c800c104a402030145101d544d5280c51000600f41025a0341701001c01c202e900041c0303d00b014409010341c008a000403400d00d40c1003031040c0e40d03043c1d101512450040c000c1d0039843e0f803294030064101c0d40c119413886041d0b0841c6d4090f12410801d902004248001000700148030f0914402c66240b01c110355945078603110020810b0255002e20300d9901000ea112510300741081c21704d260901d610514098131001004e4101d14000465401150400001080c40040c0603080c0010b015840c42007485501034503a640c100326600180c2071210284200305525416008500e8406012210255422100785580d80480c1c00303d5422600020003050700080c070b10000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 127639235 1250 127637985 127637987
    0x32c010314010612090303020702060a0305010e09070f09051f0803030105010e060403120e190f0608010503010207030806060d060b0c01020a0809060108060703110d090c080727020a03060317030a0c 86
    0x70340d60681c1d03560b8032800f0000c6000445030000f444030900440c1415400c0007208096500c24024007104030140c0c0e00401e143d0704003152003200500c090900880c603880610244507108a481d140380c1610440c07200010035565006c0400480000305811b0380d50000b600b200402e02490220003981a00c5c8280c0754164140100e5003030003254400c6200c00b40240001c01410007101d8130445100c05082030060a4003015050923441d403000070195801300c2a090341d007040402c80160015507442c01440214000c509181d00c6460241280da00100344502c208000245186003084607481000039144513500c21340c03a110b80170075050007580301d02002c0340466042c000180507254001001e90680f8081005806591149907060f4081c0603c00c00020850400348000306203002e203441200603135070190030401c40030391410b190142840110303045802c0f0041c0000034140406043c41c2d4540c110b1130208801030784c0703084451017100100050b800c005d00c001c00180f0600c880355141d801a40c000d00105004000d09041010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 127640485 1250 127639235 127639271
    0x2091008070506040602150a060e13052415061608130b0c0a030507080f070609022803020d020a1505031608070f0804020a0801050c0c060609060109050607032c0103 72
    0x40703440c0051f440443d150803440c4444207040d801803030300c007000f10701181c4411320342445840c1141c50220903200b0740d0290090101c208419524088e07a264200002420928142007030705000b8062a613050038500f03603903a151030350012260300580030b51005d4132500061410f00040d0380710116003060444402c02c082201100c1c0412164440d0b2844000c0c691034815603000c4d1000d800000d03050320000c41c280800d40341c00440c1401409814441e40d0f0005202c182c5204009000c0b861610f040c800b0b01d028103903649044200d01403001500c0e0103c0320300c440200603200099141c0410b0304942d60b00e6040d02045805560000f000d0f40c056a950f104801540480c104200d82c0103400300c0d0380d080000c203040703494076045004409040e00180040e09400f91140c48a15450a41e04150340c03201c0c140400007480c910600041c00300319000035003200c045c0f90340e04058000030320000e4940503040c414400054410101070061082c1d48031159046c401d0940300c90b08240800e20588045406404241000e85050700103031015 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 127641735 1250 127640485 127640489
    0x150705120306012a0c18140c03070c06090204090b180f120d02210a060b0c120a05071a1801050f070f02150f01090c0c0503190c0209100807050604 64
    0x84e480420342c401146003002c000c0c0c048051416101c0d40503601c100403400c0418510040d05032681080c0500007411710042c00c80307180e2442001c031341d580841070081100e00d80d02200d800000c9403a040600e0503890802070020084203200070b500510b030030308940811031550b0707070b00e4850100720406906d45100102c1d0162616030504200c0f80c0b0382c1041d22900407019100c0041c00b0040003a0300c0041c01c089c0c0c2e59120081228912401504162131101000307410840d0380500c6d405014520900e9061290103082242d481c4001454030601c42000320f15900b03914415010307140001d41200800d4004641140c2d07107418643e003921160f49011002481d04000201402214051060141c0503001d0741d40d0014210740300f500014142085000c0e541002e460809906952800f541d40040c048407075516018008003101c50000148050021615448000c43d00220a55280700d18140005410b81050360b0308851111390254001c0d4058482001c0c0055401c20400103030940ea440421101e080340c0b5281002001d010300c1c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 127642985 1250 127641735 127641737
    0xe07090e0405060f0720010b090619090b040e07090b03010c0c030e0f0604260f0d02060708150a0b0304021011070611031201170d0c0206040506090a030215070512030601 74
    0x10b602044a0760544071340304e68803201c60318000346000f03402c8100a140003802c0e1000003c0703039103840494010780340c4503548070b0f0488000c80703400d26a4150702000c05550a00c502c0b41011850355815044613580300c940200a40d90381e15000d452400d600c3c0d540b040014070b01004294001c0d0b10f0300c65800709aa0085200422075a0182c40324468480e0050800442c19040380d178141c4c00c21303800c0c000002c40303440e095400d05002902c007080c05400c1d81030982c0756182500080c0800c00d00c0d40145810b4130323001d80114030310b9044100c9190540343c6076102c0e650f10039160403190040e500030b418214005980101d04028601031442146c1848241c02c9a600413034140c108d10000203001d4004580070003442d408bc84c10321a00075000f02c152414802811101400074000b60b010411004198681074200b031018803c01481c2e00440c00c244404201580200d0224011030240ca401100002902e03d016510202d0050003598020f02959422016a049008a4100b0b04089680d44074858100e0721080345042641c2c858841 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 127644235 1250 127642985 127642993
    0x50a110306040c0e0a060306031a010608240907050901030e060114040b0a030506070c05390102160f080c09040b15120312160201020a020c060d060905010e07090e0405 73
    0x50404000051026400400902c4200d403c004e01d1500c80e20201c8004040b142c40c00110503145061900c2d0f5441514503c6441000748801400929003244545410146072044005481c8400171200c007090202c00070154408541420070503c0c41c1d1000040004c80360030798050181d00c11400382c10340d584d00d00b8040e80f2000c862404240b10181090b602c070310385900000b0403000c00f0316a40d450711404d2583c05c0c6e0f40940021110b807508000e10000b00300d002c1c0c400c5442090109040319501281c51010b40307442e99500310329140e0f094251b10343e1007000b404000c003007080102500e10f82d4075800a00040c1080c418060540142e0f22400356030b2a01381c44040c400e5401c071244e842d159a518200e43d000c0c2502e411800e0780010440451500354030100040c10484503044140a520708000d07140344202c0c2124504c002c216801004125020769020803800c410b0b1405440c8140c560100500003005041241c00150590340350500000e940b14856040c9405001c0d284c03903005070350307843c6c3c5500f00e1140c0313080320050005d0780 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 127645485 1250 127644235 127644241
    0x14120d030506180405030d05060a081c03020720040f14061306172a03030904050403030b130b041b051e0403020d0308040c060206090d0806060702060715050a1103 71
    0x4000d8024a030301c044024015050260502183c811205060b201910280e00104000e038400300103205440d0006000c03a0b2013456a468800259680c004584221314245800d40c0d0b9080f000b802901521041c50b442401c04d07812031040c03501d5000e95803810301803510440c10400a4400c44090388908aa009001c002c09101a515035051080d2250020540c2010583d01c920000d006c1064540140b880d441041c003501d40e8170b840010821140390751421161040706041e034280032641c0c3c0002107883c2010151004105980d81c1c0c1030a030020302c90303407607610340100786c10458a000e032071154040041042d00716800c22013001c0c6040c0c243d040d00412461040440c1040100b11116928480420090500b00c4001c518241d102d60100340303c201c6042c000c40100d41008140070810440049a0024046501c024486841d05a1085580b11042c1044500b4020080049921619030b10126206280c0103012560344a010b882c00e802143c10386154400d40510300004100303c25458003884500e55890b2611500b592 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 127646735 1250 127645485 127645487
    0xa150c171521010501030c0e090607090302010c0f0b090a1716031101020f2703120306010309020a0807030803091002031306020d0f0e011a0303120a0e0f030403060614120d 75
    0x16101c06211404010701e42d91802040800d000e041c0c040c500c00d07503500c07004514051034030706803043c007800901130f0350000340420502e1759010b404601220b409180000e411041420302040e084a0303990040c0c02c150721307901003058600b00050403440c0c2d58440d03007035480f000d07030084a17504060003006c45100c01d4044020046002c640303d42100199143d500000506d03141c804403001d100ca600580c0b0012000c840c5000380741040c0c500c0d150100e6081030540c05401038065000c45d81e0392070321000340076a060580e0b8044403070954070740b00504005800c018040f910340d1607c83c109441c50f03410407501c031481c070f200d041030480305c001c020b00a580c002c1102220351244a9072950300d64010b500402910380c1c0301c03540c178242242001c1c02800f03032811107261600005407602d100c2504500d405110064240a507008001d402c29402d030001070603900507124000000c08410208a840c140040c128803c110340c400801d000c01401b605034800c00803a421581e68840803d04802800b002404400344d104c110780044030b01d80066 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 127647985 1250 127646735 127646749
    0xa0e01020f06070810170601030201030b180423060901020d0501051002060106080a14180105060402160209040f0f0303060f051f1d0604090501081002030603030403140a150c1715 78
    0x100c484c0080744140c88840c591000b200c05011b04e0f400340d0080e8010011365815100e61b80c1c41940603a003070680b0381d81d113000301c81580c2c1020303200030510340a8102c40591445002d01c1c060540d000e0609070742407410b002440364041e4000b00c900c8440c451412000140d9441c00e0b2500c40a42081500070b8041c44c0e1800b0002e071049140100807500842d00c5686403402c40c92150320140c8100f01d404204000c56a8044019003182d00062800e80038a00c108801c1c8150700d080c6030b0750100a94111510700040d5580e162168145d005840014485004200b001c4200b41e019001482540c2e4413200441c1d0440c1c0d182e0821001311004085020114030310340c4801c81803481800072100c0010079203081c42861a1a002240c1c89501690007401e141d0750301e0f00140902c0e18140414101b0a0b0038100035415401c10400003502d9100760310004003600306060340c0384402c5805111102c14550808009080d80d60000b01c03090151000b030071070304001141030a02c21200d2542080490244100303920111079081e11070148054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 127649235 1250 127647985 127647991
    0x30915030a061703031609050303070206090a0b16051b010807050903121309110301061b1115030609060108240d0203010f1e09020609150705060103080a0e01020f060708 74
    0x141c592182c00108400003415510a1003140b4140111340d0f0b403510508030281d03d080c012607107007004017020381040075603000001d41e072120b034040701c810307a48450480006006001591107042c4003480415107252120038103201808460007442618000700c8034102c01900120501d000c980071031000000b007002d580c82440034050155000e002c54544c194445003a1000e9044940c0000910905e01c20500c842111030060310210708200301e50504550420f0409803091319005035140308041444e0b03501003440b006c1105c0090503180500003040e041d0805c04900d405a00c12200140240d68420102d499948a16001403040c00a018507604028003400614111090041c00560180c008001040035a4080c4a841a007050b078440004284200c030b521015070002860b14840c1e107900e401e2035200941c0b109001c03a240c003071048905000c00340c40c0c5c0580c890b01d0b00030031002508074400d10001104000741c04000f01006122074880b03081003400100126910341003080a40416040000801c05076802840f203da0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 127650485 1250 127649235 127649251
    0x30b010f031d0a0b0a06090513060509150108010906051608060f01030207020405090604030207050627040e030c0106050114040810111909050112020a05120402130e150903091503 78
    0x1c1032100c150210710f0043c40b08001d48440c6980014004059801d10131400284004d41c81400740c1d18104110b146c0d00042d5840150440740c0300c1c40000d00c0341c0b0040c8105c0380140328124001e600c035615804014020070ba6498101c031450f00d81700104021860300a4410f403074032000e40c0c44281503030b01ca03401e0010071400107a03070605260702881940010380d6280140c40c81502101c00404091030103090092404c441688064001c020400c507004405c85000352403111118050400046c041c00c9a000c01c0080c94050198880c5010110381c142e02080c0640051003161000d90741c2c107041d04050b03020710303a03c0e01c141d10840019902441c125040300600c0e420000d20442807614050411041c20310300700c40e80c106441d04031300240b0101001d01c420741c3c100450070303802401e00300114104080104050214894104203207a08035189000404540c0c401d0510f1040710b4003041d0078455103010b00c4202d80e079541c06040100030300d603030540004e00f00e64000068411104000300074440c101720f0b421044059901c0501038507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 127651735 1250 127650485 127650521
    0x90b030601030c11120705010506040501051302030429041505090304140a0b040f0f08150703151e050102010608031e03041704181b08010612021b0105060a06030b010f03 74
    0x204140c0d20a005c4184404d02103626540c0d07901b00ca1401c14215000104102d2085190000600c0142c44503080d00398007514401005940341c480741088040030700c042d02600d40089011044a124110511031b90b80101e01c6400c00184054280d4001c0e0103480c0c0840303d05006030710034001007240c24a8044540380c040005820301106988030b220f1105a640a03400c04110801864000c20907560050004402001c100d4050a200e82010f8007844100401800543c105621504800c7d070f4406c1103000d10700101a040440c1c2c0f2a2940c0c1c0381a51408891881814055480c00b800040e01210100032079058014040c5003154008180c00700d4045504050000d5076000f0b45080c41c2d082d868007410040000d000c0083d000c0c07480304d901c0a04502951100030060740d00c80c020079451884181c10500c0071341540d046040032000348400039141002070050140d400708103c441020302c043d411040d4810742c005c04041e11443c0c2d030640c071040d080e001e41c0c060490803400100d022011080e5140300303500200790f2044822241c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 127652985 1250 127651735 127651757
    0xa171305060d09020907030605090604050c0d0903020606030c0d0803041410061d07030b0a050103050910060311030607020f0309011805060307180f06020601050415030b0c07060c090b030601030c 85
    0x3042a50b006010302081581c0e4440e002020361814801071507114039549824440507080402007101e56201600340d50140740c6a101040e400300a81040d81c10751080b4840030810138a003418000c0d9500c1d4143c0d0018024001c225000742d160825243c25016241c000d40458a5600d881c1d03603c0f9118418410040a2809110281d080b0403000c3d008240041650f900c40741843c040140b8090103414002d044c1c94141807030700203a4001600c54141384c1045034800d00340000c26581e0001841e08040002e01c40b09001d40c901200401000340c40440c41c000b5a005030115410350f5600f0009aa031070b0f0030003440c42016842403124800d5507100300381c410340c0f18510481200269948402088060300709680407030100d615200d56160000180803000018071511281d40045440c040b4060344422041c003440d03000343d40322200020841c0e054010b0074000c5901410198281c80c001c1526116030700002d404403002414079400150b110704c90350048042d1201c180d009440d40d02e80500640003032070020a44020312000e0105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 127654235 1250 127652985 127652989
    0x9150105070b280621050c04050a0605210c09060a09051504090b0601021b01211401080d02160323100e0c01120203010b030402190e01031110020a171305 67
    0x1a00d001e20f041c0318010400d54105807143e1992100f9906611441550341c18000c040f0360700040f003c00084d0705540024044d25594581406091a07402454000300841c0082450940044a003080c18031504140c0d50b234602104100081a80705480c00c0f54441e010040900006005070720264005810350389200d486085400464107032025100180c41400058003003120950b014007244d4980c01c001042071075142c081c0f200191422050000504500350400480710411901e0707440010f03440440c50f68a074181d0394400340b141e41d8028411500b001406554080308802d0024207400c400c0e2503010b14504010903080c100350b500040d00d483d10942a10034102140d50280071807056452025880020b0141c105410002420181c2c400c052139103020301c10801003100c170080c0010f603a0003641c12200c03c45400f000306190726510390300703402640b5082a124000020851001da00140319002a01c116003103401c2400701740d071a01031120014146040b80b0540d02000040140100781148003183c1a104140d15140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 127655485 1250 127654235 127654291
    0x62412090f05010c09030c090f0e0703080903070605030f04060905030d0f0b0a0605030906150a090f020403060612020307030210121823070504020d060302130b09150105070b 76
    0x1520159600051074091000030302904042c800307541000c0302060301e50f5941c403584003003e216080c40e45940f0000d171060b1600c60f40010b04940a000c04070340c1c041c0d40740d0401c1038040d880041410710a104803040001c035540108280d03071080b45000d6034110039903201e8448001070651010121031601041080481000c168450408406024840001c4521031034052100e6540d180d0010b009110040c0204406440e00144040e400201114501c03008400303000031504c407a41540012055904103503038a5076200681e405401200e008507c03e020300c03540c0c0c1004a843e00042c2a0180d059000b101c400d2026042401c1280d070860038074a0001581240c201c0394000700e4402000f20044490810003003802d1101e40c2006049024046d0000c6074070560061419684508500c1094052900070588240c0c849140d0b0111000350b4014054030080306511400100806422a06510990001e0045066908003024103101c4940c180c50340c0d403600c41d5035120308801c03d0f070080100c0e90741001e6150358800150042 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 127656735 1250 127655485 127655501
    0xd05040b090f0f0601171603050309040c0c0807020910080a03080108100c1d0102010207060606030203250e120a02040c05360d061b020a020f04062412 66
    0x1603000100d906010a6142c1042410080041a5444a99805090700c004031300c4030704586001c0c3d11851301c0c14001d4170f11802d140500d1258140310508800000c28001b020008000c01d00d001c40b4108510000302d1707800d65036404801405481d83c40d05001c5d5000505242290703a4000d440c000581b40c0080e5548134007864401000c90440c00101440c00400024030100910b0300004401c0c07005100107602e5400003407024010740003400d16204090902000340e4000e5044542e03143e0040028401c4a4690341c01030041d51041c1c8698004008920b00b0030301b0452281681e1b00c03140c4041d91550b0743e000d01d20b0108010303510441041d11590048a0300413006903160302c04e00c081c002d103e4031401d881302040100302400381440c660001024034101c03404c0400040c1e001e03c1e46040786089490042c8040c003400d101d40180440c00b100c25030702850303840e0026541c0d0002040800d042c400c64031400340310350903c00d0100f0744030f06118190800080e11940030607001d40702108000e030b8280b45440b0f0043e05c0091031400568480d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 127657985 1250 127656735 127656743
    0x606031f021315030f0b0f0d1e02210c0907020706050706020408100903110d090e07020c030a0809040608150112050327040501080309090c03090f030d050708070c0807080a050d0504 79
    0x2605c4200215610340121900d0183c2200c0c3c510305030318820041003c2440c07124004217805507141011408814008032045010340141c6054507000f1100c04009042c025102d842c0581d21600c10b000780c1034900f90405921901841c0c1c09000341c0c0c1d15007841501c070f50b0401c0204680e480d40902012500e104200811080c44c00850000301d00c46106040191041c00c03d032140f48104c2d0004075400c1c00040d00242600c1c100d0b0b08ad000e500102e9502e00004a0501204421240e4940580700c000d6050040c1d12016140b041822a420402c6590780c1610a646820042c10f001c0a12030b804010400002c22169032182c981c05241a07034035004e44040d00511641110040c034030150f041e80c1d981c0642c1e060038410203000d000354500851a16003644002104000b0081000061920010002e640b030350082c001011400c00450407603446000b03040200000d480202c1e80400010740420000300c2c10b900c200100783e01c0a40100301e15260403465100c403042035102442c0c0005015040098605010355071207468851405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 127659235 1250 127657985 127657991
    0x3030706140907060912060902101d030102070b0112050f030c100b060301121b170c040e0d080403030f02090603010602010c08010801060501050427050c07050606031f02131503 77
    0x141d248a403050740003424650181e4007989041c00550b40040d070f000e0a4412480003943c40801c03910b4114042d201c0104c0080d04400d072046480c4c0c48680181c0011144914003103003040d00e20828040c10300300e001d0325802404413240d06c00100114041d80549103082c501501c152560440e4001245243d0380c44800851050362010122401a0801d4851202c80c43c104076003083c50343d49080e48038051340c03882d00b0016018052a0039641402141c03990b030107000700212100b1480c070140171401c40b0384610060703001c18011803c0c4210403030700d0180480e52a000769540d84940c0c03030940301c948084008001101e0404e10381d41c0c3c00c000c0d4045554410010354000c1078186d0001c92400d0b00c81c20002c107182c0069002111980c1024800d200c203a800c8001c3d2001c0c1d61148500a52505400400c004110001112109080d00d000300b031003a40c40040c402407112030301038030443d2001d849a409144c0c1e0f031000c0c4000341c055200100c3d005480d00900343c006102200e8080301500490f074030740e40c0320354421588001280120b42c1e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 127660485 1250 127659235 127659251
    0xf0d02060408070f0602060411100e040c0207050108090604080703080a02121303021e1b010306090606081f060203030a0b010c0210031a01030213060302070203121305010908012a020c03030706 84
    0x4403020a06019217281c1c4040c000a08096955900d09585000030900c030b210000d1a5004062042d410704500d48402041030001145604001c2d4a80c491800340c2400103010b4030014006041c00204c90b4012940200546c2c900152a1001c40350524003401c1031000d65001c02c4160800c0101442c1280542c3c40d81c000d0b4403070305070149006417034000b00b201d0020404070301901d501b00f20320002c1009242c00160550750301c40020260012802050035801851840740f40c0000841e1540c1e005030a14170820181010340c2402c03012031504080358020307210760b00c01a8020800182080015084929040c81c10305104c03c60600941c00542c1c0544003080000c00039039901180c203c4183c0c0016071030151502800c0461400076410014544e02e040781c080e46052580001d016021500e0821004101c00c504d04d0340760740c496014540d2000e04180380c2c8035641c0096104140420600c0c418866000a850b0b44090425081c205181244807881003c09400a50084518965568074240010003046100780740c0058404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 127661735 1250 127660485 127660499
    0x203010501080f16080603071e080111040e1302120307030f08071407120e03160303020601092901030b150c010c020f0d050f1e090f0913020f0d0206040807 68
    0x8400108070071070312104a070a103c2012009044c000701c201c45441c00c0d0344140d0b59000800c4ca003241c154800ca0a0041950486008001306545070042d120745000a01c90200c88003c1c030803043c003483c080c914990704440d02243c0c0d80e1981600c0d164206102400d1403070b1050700700040f0345c00c40d084180d080e40412001c840391070066a00c80401c40e8461520705000c80200545014904a030040701d0000b0072260b0100c1d0401d00250140d031219440c02e0300142114041c49100d026004245003d2104030090b108110011901400f98011044840400d14410b6025050042092206090b01c00118141640c500559026403990324000320b0701a101d20305180e0766500c5c080050b0868002402200854200c4401150b18840210f4402d11075486841c1003a26803a0580030039001e40f24110090800400c0e26190004c661500317000341c42c0c409c0b004c90301c0c03a641c1101035052208000046940740c20010244192200500e030000c1401808007005e80b10b0145490950f010030259881a000100f880d40019001c210304 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 127662985 1250 127661735 127661747
    0x2010e0a030602092b0318030605041505010f120f0c091503021c35030717090d0f050a1205010f0512010209090a0b06070203120a0e041107022205040302010203010501 73
    0x448141003110b21010620828a0074aa01d00d01d0006c08101034451101000c1103e444003402030f60300650f0400030340c2001c0c03500c5005000e00340100b80c10181018000110340b43d035040d100c4212142d17559032045540b555621200314101045044603088441034001c6410b46030f07031154001c0780c07030590104280c09046004002e01d0910400400c05903c2000d800039000842014181d01c0c1030f5038442002d1096680b0b01288410601d2030143c00103e032030044200504103a2020b42c901c4019841c0e01106156111030701d94540b80c0030314074198804642d0100191602d2489100101003144491500d01000c1200101000c15118280d01a10b4041e044030703410300c5585840001c4541c0c840390000218900f40c44080441d901c0d1000910010301555100c045c414140c903010100d0f007000b40d0060550394040600d680714402ca40007020702d6000205080c106450302d040900c200d03000041590101c909001d0aa800c100b803211000b40300c0307d051801c00300110391550b150b0040d64001d5100c1d400140c1c40e50704007000100300c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 127664235 1250 127662985 127663009
    0x809010b030703081803030408100903080717040201050a050d09080d11040f05060315041803081008030d050a060b18010e010c0f060b0312070b0f0105040501060f0c02010e0a03060209 80
    0xc00d4000000c01c2001841490031a00480d9401c17105d406171010030000641103018651009805005a2401c040008078035400f421445110341c5404210382c654401c11100760070051070403400102a40c011502542c05040548946103861800e680b41c0341e1100d003a001607920f010700031540b14401280c40c0000c074003c1d0080c80b442d00082c80c0050305052030b00701d07509405261441298059403000001c200440e1460180300d40c400d0014000f4040c00c0d10845404c0840c5040000c180e0028800001003103c41000f0011002200c4442008509003a1000e2072000144000781582c92103a6862200081c120726120241c84242010f20f072494408202d42c001400303000c03005503100d0402038055815000100c200c4400910340782c0144000440402890100349040300c201544a446680400e00300700f0010030b005042d224444a18079201142d80e24414007040e00c40a000d00380126600c004c01c680c910744561f00313507401c0d0341c014034160010040d100c000c0b5020642d21780050352101e400103420550b50501c040c030905 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 127665485 1250 127664235 127664239
    0xd0c0501062d090e060103030c030c0206030f0a0e031603110703020a0312090824041703090a0204180b040b07020304050406150f0c05030a0509060903030406081b0414010f021c0809010b 81
    0x440071503010042170b2102d00500000b07091141402d42c1c6014036115014441c1d4469010b88525624104529100c5081604640c020700d01820848a020f05902c08030a9807200e44a50102c945401071a64064441551400885080b48a2020b00201581d500c3c141180110b02468035100c6400c0700d9200240035a24607042205541d100c0b1800a45c0c511500545000c20050340b0b404e054907843d50301d045048041040749000343e0000110601c0045c1c2c0d80071408a000750302c203c030108034604001c4003d00e0203408414006e040c4488402c0000e021406100d0b2440c1e02c05203600c10ba910342a20f03000003404840031a00401122400489146400c0390090003054200140382004607003c499541c0c0c15030f0b00d00c28020003608220b404240c2d00b840e6140d103030595418040050035280c80d5511100c0091042c1c100b100d04450202500c40075010f401c416101f01d4055400d80d980e504890004000195224401070091004502c101d0261101c55041d00243c8540900c65a41e0207155003040e5961a080d5451580c0282c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 127666735 1250 127665485 127665491
    0x90507090e0a03110c03060c0d0c0e060403080913020c03070c120f080a12060b0702040b06071208070c050604050a020a0f260109140601180504050d0c0501062d09 71
    0x7403004000241803516141c0c140f810003c030014003242107041000222442d40c044c4240c20a000240d13900b40050b02d02d0048042042142c2554001d0881700401e040b8445a008001084180040b0b03051000410350a200500f0062034000c122104104070b03030101a60f80c0300c0d908045004810015840c0c00304004090400c418401403c1c5501c4000001c0340f4003500034010780d000500e81c11058010300d08900c00c4250140c04200312a5034031000c0d030326513220304ca04911031450309140c000b407440d0444c20780d40c141d500104070055125002e0003e039102e072000b030085001e0200c91190000000c4c003c20240c0e20403840344010f000310b00c91910500c10042c190b6041210288000c041c140071620380480340c032460b044c109501c0d60a415240038440d0040c4104070026050200d007401e0400f000c800019010304854211013041001042101800b0460700e05540c000c1842c0c02c1300340c00045440c0b00d0212504458044c03000069250398510114030303d5a50018000b540d5920405141a10b891040c50000103119600e130134 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 127667985 1250 127666735 127666751
    0x605030406110a170a0b0a030302030301081005070519030b0d1a01150c02040b06130f060e030d090905061306080f0c03030a020a0305031803031003110307050105030a0e030f0d09050709 81
    0x2800f80c00804000c50b13010001d05001865402150f04030007003084c0080d00342c200041d00d07410700a4490b4000d01800744640f003144004a000d4002d84a1544540c150f59036840c108a41850500d00d02c048220301c1030105900c64040200d45c1e42c404c0751582402e44a54008002c05400090100590105a02c182400b0341281d0b1040700c07040d040758007012140d604407000200000d1142c0010164050f0100c0b5540605010320701160a1511031200d40581d90701e500c4a021107441502055503410b5911729a200044400d041000107125641285802c214018000034804000040700d404544265000800650107480c00544030b0700c00f0300c1419880340c41940030350301e041841c0c50007942c0c1c0d58101c2d10003802c000c000400107003450111604505041901d60035a95203003003018000c104500c9902003502e04500c0000c134a1180e00e4005058011a1410b84489045540d800c1074103000b0100c0070107415650001300201e00102e02c2141c0140300f074200081e4002a541e800c2d0409e1450040a0340003103900920708500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 127669235 1250 127667985 127667987
    0x90d0801090c03230906010b03190e0a120306061d09060105090112020c07150f08010b0c0a02120105011a03150618041a0310060614070804050a0605030406110a 70
    0x1456040d00c140071808901503901400c21001090710500c8240d08a031141c02460345650b601c6a018041c11007541101c1003645ca1b920015031620040e2402980c00c02d8100b0112482a6640c01160810641109413800e4641a8850b86024031410007270100090f43d440c004c0c4001d5400600000307608200d24800b011100655020620040000e0880f6050090100b00542e45a05c00c241b55144aa0140d40541d00d881e042000107940c2c1c0600c1c000d4151034090303110b68803802481949030840c08415695040c500c0d9180060b03403e03a41d80551856030b5103000303c0e03070258050313180c0c21304182910078540d0001850398580b5040c3d41740518070030420404240c0410500c004034036007201d0201d00e030354110380312603456a41c9001d1400c1041c00d140c0c1c4030f80081c01c00c9008080c0c034130100030106201e2025800e590617000100e102d8421101c09002e480041141e10203480c0440410340702401c0c03808e05c210081c5103080d4a403070000d01040d20070750010300010000030801040120f140580c419008040c085503007481d01e2030b14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 127670485 1250 127669235 127669247
    0x60603210912020d08070b090d05090108130c0902280504050105181c050d02060a050618060a030506090607020d0804020105030f100321170705030402150f0409090605090d 75
    0x200d070b00e1000c03030080001d106564a106030f0180c42c0fa80445195a500501d1034a02280507003160801d03494050b050140d80c45a020341c01722400b900c0142e40703140003503407072400040072482c100c6420b5a000344400404503140c48a840101580410000c1c44441054038980c50099402c42d0312060b01000703418002000f460741c010040d58126045041ca10303010204c030401203440301c0c020280081014108440790703030a104001c50030603030400d281d900b0340d1320b103503076005101c401e5490954260b41c20074503600901203150091403003140c0002e0009d02c00c80d5100c0e665100c16242c54000d42e80e10250741c000206100c4601d804100b00d40040003030382400c18a07460030360000390a41c0001003000d40040d2855000403c08000051030f0009503030720140800c210001f46006000c070502c51110100451a03182e100e60300202a09509803081d6103a40e181441c6565550900091062101c5010310710003007800745100140c1c003180900f01400480d81e000070100c2c00d90030200c094072009040446141c01c41e948200d2401c1c0c0c80300c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 127671735 1250 127670485 127670489
    0x4140a0501090e1816060f2307050a050105041a0109060b0316020a1a01050a08010204080d031d0a03080a0f0e1218090109090512040e06040c1106040606032109 70
    0x249030000141d440080340f00010713070034100c0c071000c0d070060102d007040b1131100b44608815200c260313071183c185114032a0306590355402d00304a00d011040f0032012500d080c00c03420040a086101e80150341c04002c4954840b03094900a840485204652540c42c1c608d0b100c0003003039640104100e060511105103004a0032500340300250449024041c01c0a0307414007180204610b10f10681e20506000d0b21203020441280028028025240304178500a40000d11706814020b0f00c0644810304042d2802655042043e401403280207502504002c10806c02c19690b10244412800039002c1d484d034031074900e0101c20f0001215100c0001081e554a132642ca0701ca0044000b8810341d074104208805a540c0200a0300c058640340c804103c10341c0245404000300e404406a04502e0456108204480b21980029140503890042e405403103510006a000a2454030b41604220454000d90614500328888040c9507410980100c3e000d0700c8a030f0702c81c40100100b14041c002880c60304030303407841855000300701600100f11401034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 127672985 1250 127671735 127671749
    0x7020f0d11150c1b09011a031501090315091703090c0d020303192003030402030d0e041b0e0f0108010f0e04061d070609080d05040b0304060905060c04140a050109 71
    0x7a0600d01c0a0b204020071038030780151010445040c0701810341c00400403180c55440da4026084080002200d000085011035644070340011103003565265a21200f611402000160401007658130001c0030940c0300101e1400611641c8020031610303220300b0000f0811002c0b0400310386804040080100e11000803c034007041c2d0904403880312090b030304c1c0c0c00020f11b503014800308883e02040400c00342c50500e8012001c1e01121103449088420121181119074603400304460203501904024140e0f890140700e510003040078800180000741804094002c108035180d50180c04010611160300000c40d0301e0604003910141800746425002507040c44100d2000034081e229441000c034108001c0f40c02c101d8a90454001844a070000b00181107400412654510700c81c42404007242c524403000c01c05000c08121007202880c26100c651400749011010b2072180e1009100341c1e069a0364000c00b000041c01846028085c0c452014144d4940741004040181840100e45851161102e480700708003d90704888070404407018 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 127674235 1250 127672985 127672999
    0x30703020306010c050304080a0b01090e150406091203091a01060e0f010c050f03120a02040b07030c1a0c09040c02010603050606101b0305031005010206060310180804080307020f0d11 80
    0x1640e00513510102c000300010114040801c0100b4402d00004024000d14024166031040d80d0340c1c1c6002c0401c80b4400d40007212580c00c480120401c080da110480c07034006204481c006000401601c500e900027110581140001c0e880c1d0040e181405500d450441c0d100051580038a41c03549400e0000e040568089d04041c000d0328240807002403603000398501060541c111003074405d4100070800b0705031258803034480942c1c140c42c0000812444081403013510b06942600301440d02e8000703da1000d680482008c1c10407074003008050203090714951103031011030065040c0c611841c1c641c0901001c0000b83c5800c0e4079100110782c58150104046940044c085400c030744c0030b9401001034510020111202086115500080c021407a948000c2550010065204141c0c1e81d800d00c10290b00c2d074004a8998034103a59042d4541e000c43c4110600030199400071110003c0302d00500c5074003401d035031600c40e00d401c26804000f09400124610003941071810060040d07071002c5032a94007206055840c01070150050302e00a0069030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 127675485 1250 127674235 127674241
    0x30a1106130e04021207031a0628060e01020318040207050f1506010206010f030f03031109100513050604030c120c1701050702010c080603030403031409060c070801051b0307030203 79
    0x3152012118541e00e1494403225241e01c80c034215051890030380d030032802030108a00c1c0c44082c43d03010840400b50707580403540c68550041c051204810140283c00d16512000d03255203030403070717550401b240c002c001c002d441d50407802d40c5840350145c45000c0e8020b00a066400420880f0101d100d1109224881c0c0811100162500141e003422890084c1c3d80c1068183d81c454019101400302070b5185441c0300307810980c00c54510f6070b02c0d008a06143d03c40d600c0000c001c030304866000c000090003a04051000c03c4030884560407c11480700203440e80060300510340104400003121aa05004910604e001e4102070f50100d14007851a944c00c00403003100d108203409107800d05030000400c030702c0802d404000e15001260301034581c00b000d0050f008190070b640341000b5600e003404800c189d0740640c5040d403040c3e900034051401c0502d143c82c1514120b200082c80c2d68904020007000f441552035070042d00110785004002c150b818100b040050840b4005001c04440788041102c0380410f2040408499000e50070f4900540c4a803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 127676735 1250 127675485 127675489
    0x1020d1b080d051003060e01020a0f080411091315151703040e07030f0b0109050609010c02010c02060a0503011d0c07020d0f0209010332060703050603120319050114030a11 75
    0x80110070588407002e043c00c0a01451200b085450810740e4000d20f010009446c03021419401c0384110320080740451040300406440c0c600803188558014080c020048040d1103440020300400412940c0380b86601001c074071070050103130303910a441c0141000d01d002c1100181c1d02c0001149010030340305010402100c2d00007040d1300c100c148140e070f000304408544000141060040540a0321440305258059072404400c0c0590b9031240644000f100c4000c2c1049161007543d10045800c0305500009034140960305001900603102d0b10b0007425603801c00c0d51015220350422124204207a0041b184000001c201028040144000411a1506a4100c2d44041c8000c100c1c0b07400f2403154807000001c0c0d48032032190b000106000d04122a41c80042c01d0540c0c1e00260300a90151058180351142d00d00782e198880303000a0b000d98066840b5a8001e60010700b03d51105030b0311440e9541030b40c411103000702026144041140d41544a00a0343e01402486a000c00c20001110200c0d9490201000280800a15100144c955 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 127677985 1250 127676735 127676737
    0x91107170c160b030601030e03090d031206080a050319020d0e010302031801020304050a050c1801050907020309060f09090c0705031207091703071a041e02041b0309020f01020d1b08 79
    0xc090389a00400b00c0c1c80c0e4404612285400480e501e40c0400e003042c055445031800442110340500c1c005108611603021600c1c111a0200c0b4428000d0700186c0e66400031803103030002c00080d07001d50b00c00c0e00155a5121101c0383d00582905c00301d61141594003516072006500d4000002408a6000780780041c1c40380da90108501e0485000c00b80002194030010520050210200d800d2031440e00450071540307040903d50900c5032950000203450b2903582c08000610081c40c2020134a5045201c520440c0e0400842e400001c18039440613400000b882c10001d4030881c24284814a207034816070701e148a50500105407030385922803154210888009800c03100240c52503008a1105010303201c041c0c01074107000160706000e59a80e008440688456003010b00800461100c0e218280c4035540c0590b41091000c6000307011501a502100d00b240c0c400d40304c0c1e8501c010f10410110b9540e2107101990080340d106504d0041c411041e010120160454100d603044440240e042401008910201c501d21100c0b52058289501d031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 127679235 1250 127677985 127678003
    0x3020a0806070921060209030102070b0f0906160f0e1f02010603050f06061f140304150e01050402010e1504030203011103072a1205090910091107170c 66
    0x8404258000400c01000000301c5610460a50301c0d604900b6884514562960703460055100d91501c9809102e000600940c002c5d110303801001c0c1c000340c01e181c81c55407101c611210498002078904041410016490000c000040d04907001c4408030074503007103281005283d50301d64030040c0c05010542e0040f41903502c0f40c04024940c0801c2000403084a000c2c2d2900034041c100500c81a03440c1d00c034040d0440820310300401c1c420f020b841c0040244402140078100c66580b0307482004240180f229030446a0606d1000e00021803003540f1406000440c0c40b8414040c008a90000c21640c526a1400d402c010050344c103d68080212035044540500450030344c44000e0243c0b0890700300a4240d428144500034000042c0b0207076004072890745500355040c40342c3c1c07202400140442160045440d440050320042800c60708083c44401251070420701c0c0400c00c20200d0700c5c00c1810f5410401000710080708212030811442803240c885111030895150504948501241e80171150142c00c05d03002c0016000030b40c940c01c10560107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 127680485 1250 127679235 127679239
    0x302060f0d060303030e07050306010b0901110708010204030c09110313170403050a1a01081203160302071a09010614030307021e0306040501150b0316030e01110c03070611090a03060f060302 83
    0x314283d141c0c0340090280c206403029803014411801c02150f00c5c1780c0411003906031101140018200081e0308011146035a0900404905005540c00815160000e000802c050742c096220089000d107400746c18001c44880c0144462030440510500003144138441411800310b8000900d000201f05601a0f11514465607000a1051240c01c0c107000810030310350756034441c0405406003066641e0780e0741240c46e01c52a803001a005055410800607840c4000c5041c00500006145001403e040307995654600e101030040c13250b45001428002c02c42c0f414000d010b15009450b003405004d80203110346011a64901443c0c000070b200329554050040c854600ba40e80128812006003240c0442c00c00c0d040180c000c1c0300100200b500d4210701180850304100c2c02c0201c9009008001e40001900c64280d4124001d24000a151711203540f6003294000e20405400542030042d031610185907129124075010046500b00d4064224001e0140401c011a43e0707482d1150302166040600031030700c034425002d1036000704402c1e00025 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 127681735 1250 127680485 127680491
    0x9020f03070603050411040c0507080705150a02070605070f05040e190203040c03030801060206040f1b050a1e050f0d020907050d060b030601031d0d0f09090203010b0715020a090302060f0d 82
    0x1411030f4160421801180601c00c100006c40c901c009100603510308440c03000110f03000304901c400003a810790040c0a190f014400350f03a854824140f004004441c20b41d0f0003420703950045017071400e002030351044a13000307405801c0c001804810100c01402900452041a0004200d4000582d404134980041c0c407860001040031546e80c034051070b06c1214408140000c1e000a1804000801e243e0b0002803000d010f50f41007462800b07014015610952880050703d245450345944400c0011181c03540c0c3c80350303405401c0f80c0919400c501026040142084c1041d0711040c82210321301c0301007140703450f106c032143d10301a0161240709444c1e03034403107044e07a86114406d1400c1c0e08502d42500010702412a00103940070f01c1c402d0360180040c1c04461400e00780c03014440c6240000d50050030030b0f07506c160302594400d03166a240b418150000c6a60b01030120403a04240c2c041d003000c82c40024007004001ca242020b90030b00080e110118280042d03550001c1c213020036400300a0103081e00040d40e2040b0307039607842580c0121203001018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 127682985 1250 127681735 127681739
    0x903020c0604150908030423030309090405061e16051b03070803040201030b01030e1b0411070b010f06020d0e010c02060c1b13090201050f0310150f1205070e010309020f0307 76
    0x141c0e44141403c0d20040000f6120f100100d404c1c2c401204850481d44582c8986409030300002c1c0452111804501c00343e818481042000d80710b4450814040c0b10b0f900400c09008031b4504114090000e000e101d0800c507100384010200034104400070500e03159400301d0310702a40c84240070030300c02c10250002540c3e81142d1002064040402c0f02110081d0f00c150300c00c0c0d80a000d4450158019000c0e5640e1030300c4090144c000320310031030700084c04c3e81c1441c0c6021001040428038071403280c110040d1750f0240b4401c0d0b80300006c0c400140007624481c00c940c801041d061008108108940d5801400c0c200c24100701410002103840b84001e5542d004151080b4000020030742d40402c241d44146610140741556560240356003c0510100e841301c2e05c00ca00c02550103865280c0b405d40c40e028102503980c0f00904040d10903282d40317400308090b0341910022800352042e468140d40e03401042c0018154070b80080100104504100410002d80d0b846650040444801e0030b01140e0103c0c0e62001504601b01c2d406183d4241c801c03c000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 127684235 1250 127682985 127682999
    0x6070803060f062712100906020405040f0f0b030303040206270411030a0b030f0a08250b1905010302010e30030a030608010603240e150906100302130903020c0604 71
    0x2020450804c00594004403059003082c000d00485036046040b864105444420a201d2141c1002d402c0074440c0350010f01c1e1030344540c0085c048038101708941461542d00d102c0f400c150201442090200c69044005500718a0654000340c4140729071602805011101481800545052004441158402002400000b0040080c10701941040b26064445410700000708441d007004a410300c4540304810242804da040f5072200e01c0c0d01da00c0034020f481080700307410080c0707070354041001c43c1540c00384900448030b001d040104411240140c802c0d15111480d180c45c00400050303030401c14288180400799070799404201c160012084100140c503429800d50140022a014900e012008201d1102c80791000c200940d207440d401800c07102c0034007000340034003041e0ba81030000310141c00e0b400b1411040c100011400c80200b8125070704014656462035485040842400300c0d0031401d0211a07031040340b59240c1c81d0070707500d55000216030b600152161202e00d135844070030000b1301d4420312621181c044054402541c0d6591104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 127685485 1250 127684235 127684267
    0x506070c0b0d0f2004141c11100503150d05030702090106031d010e060604110c010e0102030726040b09150108070503060c0406021f09060c090906060201020906070803060f06 76
    0x105000d03400c0c42c0038a045000c40e02c4504c0071580200c0b000115040c581407440441503000083c0c00340ea40711010343e0402280d039444103001400341b07200e43c1c0c41240c10059082072142e6110102d103501c092010034402c105064841640e8914481e03411106642c2d00d070254100b40b070940c41031100180d0030442d528000302e001e9806801c60160001c0700303564106900c3c3c550666500700c880f498480c1c099904244003080d541d141035041100000d100b5802c451030a010700104500b150003000c09040304d40d402004021178590029103c5030181048000205201c5000c0480130700d210001300000c0141402d90042a040030701048a10501d005500c0d000c101541c58261080e9107100724499144284901800141c000544900b0384044680e25002480b9100e6858951070710100002900448142d440d11a0004959503010301e403c00c00003600c1e8500d01e54101804030317083d60b01d10742140080d60300400941d410b5841c1c1404079142950840040c43d200d40300c1c140014010302c400901c03140d0062000c40c0b8901d000d0f056103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 127686735 1250 127685485 127685501
    0x6020a03080606040e040606030b01080a0b270706181403030a0c170a02060405060a0213030311010908030c0c0c03030f0d1104090501170d0c0b06040207051002030106020a0b01080102130506070c0b0d 87
    0x2b041c12030f0390f5a406150f44005c1c0800060060780503502068520b1400301141e222050f01c519100104050f58284a240410941c481c2c40081e0f2600302520440b500c0341d10710130103070042a405407500400c0c003011170fa40b4402d1810f4042040b222121031424400800081110304c025032500c2903171200200d9009684aa080ea01600c050040c1c4000c5018541c1038402c550100522407071f032244d900d1550b1020346e000c004010700e40c0300380c0d5290021840000c0c01c1600a51081c2c803c42556611005030044440c82d2100725005203001e60b208101e80b030481d00c1540203503108c40c120760a0114900b0100c07440c0500a01481e401000028203140020480c1c0342504034062140e11044200c40c4c403103802d03000848404c610703600040c10301352510001ca2664242a0003c21484d4000c50071248801010038500c001c91384264031040050b00700200c500708001640340c105004084c55030003507040501d0a03480086942030361040b46d100b00c400090f030b1410001c148105000520720725514030b8442c000010351901a220314 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 127687985 1250 127686735 127686743
    0x60801020f0c15100611010b090a1b090f09020d090203010e0106061205040b1803070c06020601230906040b012304050a060309050a1b03020319030e010906020a03080606040e04060603 80
    0x1d40e075840d803005400f08441d4071512142d0109201c06160440540e001280000400541d540740d801d992001d0305c8101100d03014504001d000900c17a141002e60180e4410035200300d82c2005441c00040121101d8400410165900f07031600517030710601c51070302400034007d13158001e415500b80f80c1010380200040d4400b2007164130580f2080d40503020080c000003260000c03140200150500c0f40070804029078034011849150300300080b280703000c00540b50500d0442d07555020740016804040140080080d070700417440c80c2c443c5400d0008800c1c02080000f070070f6400c020030560250380c1d00ca00c034400b203a00c6055045500c401c41d880e8401084610641548564042d002d0ae50080d002e810700014900c1c824031a603000d5030b0f00040a480c401702c8540d40c1a030007200307c00c02c070100e941d1004400301c05660700344092294941c001500010082003841d0141503804222840341c14403038041c00411002d07401181080340c4591500d01880e040d65120300160741c5000301d8020202007580582040204100f551155003907d000e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 127689235 1250 127687985 127687993
    0x305071709010f06080d0906031d0316060b03011a0d08071406060102010b010e1008040c0504110d0b0a081e21090916050702040b040f05091b0d0210050904060801020f0c 74
    0x646002c0ca603203240040c1c5c6c02000401ca89420001d2030b100380d00403540410b00019299000140c51140b83c82d641100d40c088a901c2a280d03070310000c001c141d20074a030320803030300394003c1c000c040005107807129508021203118025001000d50b05c081000300411a80e2050340039100c6064500c03d1040d0b0350351070708100c450324055842c20203c25039941c004d40c41c0c07585000380140a400d664044000880b451139001e042142d40d898968002700d034684d2540203850f443e4030408400b07500c4503000403aa00580f218014113038003826501c0405e0160010110343c02c2185000d041602d8401d034140b0461918100c881c9110603030300760000f00415840e1801100901d103450084038100301c19190f0004096105403503400c3c02020510030030228006042c980c204103042000104002504603030000b0042c16a201150403000310b42029440d0690042415119001c085098034001510030712603020403c2c0e4140c1d41035402c00d100c0041149901079a50707030002c4020303110000095468802c0000c130000f05800c031540b400c1c11401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 127690485 1250 127689235 127689239
    0x12020d060e01080c010305220303060803032a030103050601060522140316081e0102070b070305040c0602010212070503061f090807050301090203070608040816050c040b031603030305071709010f06 86
    0x206c41c0c000c03031b03012303544007002c400b001c000d190003040050078810000c45c00c2c142c864000084100081c17003d03600c58004030503195031403036206100820406000f400910021020310061010500000300241500c80c14103100d0341d6001d04000700145a51000c0e80c0103507510310369002240589039044800404001501200d05000c1c219807034a00e40b211a000b0903040f5800f10610758500070818044441c0c0b0f02c440d00c0014940b012a0f203c94400b108100d6104011a855806010402030740841070001000c4034030085050520190303403480d004d80050140c0c41044804800b0504a030b885462403503401c05140c80c01c0014194603400608088a144111159405144d000158504060180281003580100540780c0307503040500603100f100d0082d0055450070030511004401c011030503451000b0072300070001081d2001655003000251071804140e180241c210b10b010b07001d0400602c4485d41502ea2504000c28140c3d00c0c010111000d406080860514448038001c5c80900744065204240c60030a81d0b8083c44190b03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 127691735 1250 127690485 127690487
    0xc092709022103040321320f0a02331e0412031d0309090a02040f0f05040605042c010f1e0b0109030803040303112704050105150a12020d060e01080c01 66
    0x14108042800443c40301c7c40c2c2030003107800544429064020112008021048882030016540c0040c489030079100f10000d03109080c5030301080902c0c00f400d540740744400210b50b0b003c026007600f81c220342d10601c400e51440200703042d4050152496440c448035007134840289130604008260101321112040460b14060064a150300688101002824010011440d144d20002407001a01000703200501c019402d101c0031800e80c2520000500528541c0902545142003004020855217a03a1145101d10301e44400442c002c0c0142d1000f01001c500d4401ca80c5c00b0041e08141c550161500c00c512140e0640340a08101d424111100303081184d42d2640e0040000c10f80d10401904d0621942c0400340c40b001d820310014000901c030340c1094082c038080c40c105605250200733011a100e954a515007910071905801a00a03a040ca8800c2e80c0c01010304032030b083c403200b1100d09a0030241c031039a1200300803c1040103003d015848660120b4004240800c400c121407581c880041c501c0300400c2c09650124014240e402103a5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 127692985 1250 127691735 127691783
    0x31305090603150903070606120302060901050114041a10050408010b0a0308030c0c070812030a050709050a17010b0d05070509070509090a0b0d05060108010c0927090221030403 77
    0x351400360092042251180e5024030f9103200900071860740c13204100f0200001e0060086800811134100307011139042940ca00079080c040c00034044d00450380341000420801170050b2200f1001071054400003880807072822010030028000d0809908040e080c010130484541c00303002402120911720082105180002c00c01814401c188070140c0084ca0900100d01000328100c010541c1c0458078003210031051343c4403000c6041035942d00369130941c004007004000c691119401096400412481d084290608007000120032400300d0040c400c03e2080c0704400350161009600601220780010889134401c50246405641ca2140c4e01a8600985030349001c14003140c0030308251090b03290001c0c030030f07000c80c1d40301261400140140326400c0ea0280d4503102e4000800c0003404494040c200d4640040341010601e6805040900700e503002e29030321030b268004100c1c0f120f00d030002e00310211100080403c80030042c0c00000d01e000c0d0104034100d40c6800241e01c01c40c0780b10002008008491240c00741c2102c180211f1400202 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 127694235 1250 127692985 127692991
    0x60e16090b0d0b12120703080105010c02300f0102071101020703150f020403200901082103090309100903030305070c08031303181409092e060e04030203130509 70
    0x140703100744181c44010000740c00c01449503402420300740c030500c0303035071021441c24001e04004000e110000034403c3c00d05601c03844080c05010282403540003145541c4c00314034280d0380d00e484185010300340e054548404810040404030501402c00b128404440010307500d00035405440b088902424101c40480103500100d12081141e401085c042e602d660b6052000b8058603007160101080c079420000070000400701d200001c400344009208120f0700f20714005001c034060040e000060581c0c8111001c5141c000c3e021500d8540b00c00461685840c1c2c1c441280b454a940a1400b030141e120043d111541000303a84010301c40c080341c0c0a983d0500103611002e109507031110404030301500305001000010142a000320000001c1403080c500408000401550060100d4080e0040c10b04c01052210503051031800d001c4681d0401d484502074030341c0105403041da0b0104d420350000b114044460b02c80d0f0704080c0e5956801140241450070b000d511514103803030000e41321303403040d82e565840c01841c21000c9003504254811500c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 127695485 1250 127694235 127694249
    0x8060907050a02030d0c0e031209030c060904110c0d030516090302060702010e04061e080f03072603010603060501030e010618020d060902160510050609060121060e1609 74
    0x64980c5404104a465074002d8035002c003907101c01c00102c040043d241c401d24090a40599800d104c44580604043c1491441030b8094200142400340550702d64020400413008c100c2110301e15a0782c501e5801040c0a00000120051181c0b00810910910500410000e408100540c0c0401013965400031881c200141c411141d030000d01c42c28418070050070403038010100b29005041220007102040001819521a900020189442c80c0c06011a003280800000301400d0494007038000c0015040b040743d03880c002c5050162121089001d11500084141c502d4081240081c4086990303603140c5c0d50103009088a4801c8500080c90809000300c1c2c5501880b8803000c0c0c45103800c0001182c040c94680401940000385405201c958400e00080c1401c84c910003400b0080401c3c1048011224034100305007440001942c20803950700b03100400c24035a6604504982c000e0090034011380c44001901c00d940d880d244200c00289103454640c0100d2f00c102150f0001d40309949914105500e0309410800710303111802031058070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 127696735 1250 127695485 127695499
    0xe010215040f0b04050c09041104060f1a0a051b210306010c060b012105070f08090d0c031205090a11010207030b060f0f060403030903110414040308060406151e0806 72
    0x4000500f030090450341241c01581180d1003030400304006400303907900303030380031111102a084521301c4c41c1403900500c0c0050809046a100b1907107000341045c500f22501012100307002000482040f4140181c0550340c1002c1e074401824811400140c40a40c0d4000038a403658100340b200d04907034003041800c0200c0c0d100d2481079443c910321550766030307071034014100c4e114a01e4140b007014030710724480321044030510913980d8150301c02041c1410300090280088041c030040c9010409007008001880c00001022030700c1c03219600c4c2140740701c00d441c00d00321a40c8403c0b40000b480c1505110521018210004100c5400741c0a10b0403a44410340d40401039941d04c9041c071008082c100c3c150005007e5141603c03100c6141000138200c581500103290000f04540c0c85900101c0100b50101404c1c0309106a00307941012902040d141049900c1400d08240300c1340c400280010200130070900001e80d10388940e04100c00130070054000c2c0b400014419005440075011041000942101100e50743c04a80304107852802250068489 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 127697841 1106 127696735 127696763
    0x1e0a06060f030c060e1504080105040b060f0a05040b150a020d031104030b01090c1e0509040b03030301061b0f0b01180b03010b03060105040902040905010203070e01021504 75
    0x200c4074101c4520040c0005425406681c05480c1c150400005000104001070812034901050140400b00401c0010b8624015080203000e58822400d4044681d1124207015000a11a5140703a000200c01401c00c954103140d400200c480e4000740848040a004200d102d10300ea02c080c10356001a8401080c010a00d0303030510070301080ca0b00070303e03080d40b0301b910756100c2c40d401e20418050610003c1d6141007414410740151a9110b066a001b40704030148010804003404a400210000340518184140c406562501104403416101251180c4c0802440321680c162500c858000840d02601c80c3c03030342c0300b003c52000b10145000341940c4601003105000383d2449015a001c182d00107002c3d83c1007142500c61030794045151419540c007910001a800003c2c000200600704102c0041c0c07a5501c004180141d244c1c6c0704440d01c0c607002080c0c08854155400c050341003201c3c0c05c00c07103000e4161100c0b6801 = true := by decide +kernel

theorem cover : BRFrame.Cov 127517985 127697841 := by
  have h0 := BRFrame.cov_init 127517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 127517985 ≤ n) (h2 : n < 127697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
