-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4032
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:22:52.804408+00:00
-- url     : https://prove2.me/submissions/0c99fc32-7fd2-407d-a478-6b2b98cbf3fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 725000000 ≤ n < 725179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 725001250 1250 725000000 725000033
    0x90905010f0e0f0a08030901060f08070f050f1e1224060405070906210212061804020a060c06060e070c20130c1206062606090403230a020604 62
    0x9801c44600f00c40005840f2020510020480e001c04404128100700035800100580a21446940d4240c0c948449964a0f041c6114510a51003a440c1c04540d0b070411030005e1a61201c050010341c80003248008014001081001e0144c000340c2d00503000000150801c8840782c0c41180c20243e803070340b41c60f144503245a640c00909840c0190300340028054219408900c0c5d000316065807030055201040756803035031846400c0300c3c090130340300340080b6a81900301409000c043c090602100c864280f503242d01c0e075110151a0456010394402501c10b000c12581f80980d004401c680d11800340080c860741c0310181c0084640d401d030303495030001341c40c1000c803804c1142c001c1050301410028051b801c1c10185410010303488081c890720090903103484400d0b1484c001c0c0103408122803004010024003600b911028010412408203281003613028041040e031045803210580c1c2070144001030004015991252001e440104603040c485c0c1084040c2032401c0e0340b202100c0082d001415955019051504090801d0300d41c040042a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 725002500 1250 725001250 725001253
    0x1b030b030d050a1b21110c240301032f0f041d010603060f0c08010e16050f0a0c05010b0a0b0d021e0c030706050105220905010f0f020d0e0a081210090905010f0e 70
    0x140106c0e8414002640e241c0712104541c80c40d0300d0010401150100c0c90030b014a1845204048000300401c901805400138503030b013111151040c030044cd445458420050240d0581181404142d11000c0c1415080303044203031905218480c41200340c404250846980c0d61045c0c0760395550343c402101c4071000b40201e010b41c02c2e051402c1020b550402c45140310f9104080c10300d08882c0c0d80503112144040c003607415101d200c041d001e50280c40315a907510143c0b04003030780a022280d5510b001010b46407403801a5254040d1500d0800e024144188a42e84100950140180c207414110410a04190b40d000c0350043c94003550000186407960f00c03a00e030030704c160360060b0481403007010b4220100030008011041c515400c4c10340c1c2e101064110060401c44c2c010103040e4000d4220724200a51105140c3d07030740d0000c100d90f0b401c0040401c004c4080108a0b6120350f19110000c01c0044e0421040c680c07207006108580d00030704c0342d0301440002903442e8200f2085a03841c41c401c580d2039450b4860b0f000d03032120a120703e0842055210 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 725003750 1250 725002500 725002517
    0xc10050105150d090602180f2403090a0606080304090b060702363309041202010f020d05160f08060d050c090108011b030b030d050a1b21 60
    0x80005484000045846882c2440422404a425102c1d041400100e030841c40455840c002c01440c0c503041c00503211054000c140041407030401d403c103080e400d4030794001402181c510307040311507881469078005002e04400e8881d001140020074010f00c201c2009140d03c90045540b17501c1c00014800f0780c5c0070340200600c03d0380d0130300c00200580c450000e41190200300c00ca915403621122a08074800d0740c9a0094824200c1e440d800304004062420401796021140300b00d90700c0010080d0490440d500721040b01300d41c10031000350106000541d2440501c0c0d0101c220300010440400100101040f82c115125820f03a107a110410301c10169450412510443c5242c03804a90090b00d40001802c1c0e901d000c1d2115025a00d440340c01814810140700b803210300c002c000d00034041d0b0350b502d14006010700612038500d02c038842500d9228100c10f020340304002c404000540602010a4071000540c1c40d0b81229442e60b0505c0b844084620243d0b904c03a244e004228421000a841c035404100d40071010716502816500307000791103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 725005000 1250 725003750 725003759
    0xf0c03020c01080a0f0c030509010e07050a15020a061118010503060108010605130305073003021c0e19090b0103180602071a10030227180102091003020c100501 70
    0x1c541d840d201442828a0b082c01e458041c0128001c0480c050b905c4840361500c00d28416940e8940c00c010b01849443c8001d0059002140f41c40fa155080c0f8412150b2085040c901044010280c6a07507407008030050043d15103865440cbc583d9030a5642501000c803000a0001c0c40300c2140c03ca8560a80110800b03103040c50851601c400040c05039038040c0a050248040422400e400e0502d440381c0b440030b0740e40071041d10070803550380c980080070602003002271000800c0c0d43d02c140f20240c8400340000746079416600400e4210220f0051400c007000341000c0700104034030000c54104a0b02c9030000420070010300c00d0049285441c0c80324402c103c814854100381014108914600740240103c034100220f500007100594444c0ca51038125000000342c0e001030007a04590007041040114090f02800303d0f40242e07043d203108181e1018011311561030070600d56411240c0f10104000c045440c10041d607002d196000146058400d100098038100c421900000083d0000340350300046200b400000c20b01c0070213480034000e03941403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 725006250 1250 725005000 725005003
    0x6010b0a2106091e0f02030708010e1f03080c0d030b131107020306042d210e1c0c0803090d0f1b0f21050d0e06090603010b0a0f0c0302 59
    0x420003030301840c03149a06101081c24540c0d010390300512240204001c41c010303041e1403c00400c1407040f030513641454440c888070f01e40f035107000302c86c894a50396480b0300c5a40e00f04612255025030103400b1501e81c508040103844540c10794100c1c040174600520115032a0795880c2e08040c64080c88401074010142001940300da070f03840d1a09400007010031103102051184900c02c03a0340c1e85000c0e604d070103989845180c00344014804107000b282408150016032004000d02403e00c280018035000000341002c20750002004514025062242211074030318040e0b20456100700040ca42d14101d25000494803a42c040c40750401001c28450002040e90101075804c1080705400140104109807000e0320552030701e20320307000304486800300445900b0ba006295042d640c640c10000b1900c1035600641c013000c2c2205000b04105d110010440700a294410010240100004421200c014028407029048681403010b0200755840380302031400ba10f142005aa2240d60f0903400401242c910030422041c0100e49a940c00440d50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 725007500 1250 725006250 725006267
    0xa0209101a0919081e01110d1d06062202070f11180c0301051203040e041a06090f0604021c050406090c06050a0f03020a09090e0c130b031902030f0a0506040506010b0a 73
    0x801880074012604070010050140c440072000120741f28001a0401040c0711991005040c003145c03d100c00c0780ca9070b6141c3c035642e0346c0030159025580640e1001d0741c5942e40c144080f0041c1000036640025003410590303942c510341b8801040301110785a040c13004c03900c55414440400f1069984c10340359040385080801c0b480105102c18019140516400313060b000c06100104126001001c4a04042c0118901070030f20300c8080003400c0480d0200300080780032407220b117402c44016007c2c02e07086451054544403103041000940c0200c1403800c07452128407507000006228400c2611540c0503900105801d0410b1030030201b264196003000d02400004e1052503403050f4015814141d0510b18140140c0d6103a614000361040340960307100b903081a007080600c00c001c01e0085080703103201000351102c0c054120304944850940340c0280040f601540681d03e10130215508a1034020414009170594a080444030700309030509a07100000e898076030114050004003c420000c45004140a0000900f0b121503800b00404642 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 725008750 1250 725007500 725007523
    0x150a090f1214040f03150905160303080c12070c020a05030a081206040603080d0c031416030e01050106020d140906121501030b06030105042a0e03010f0e0a0209101a091908 75
    0x780412500100d40300e0340c1d1f002000c5541c101007200c94501e003020345240c408445000c1100021040e5002c290540001800e0310410600303c505502d0b00d0b80c0b0100308070340e540c141d000300303903405069424002000e481c02d00101020f18051803100d40d84258034075914a0b80b810141003d401285080020004585803100707175032941c241943d01003000c019910045000d00b5624103411024080f90b0280200c1800d9400034181064040e01c080c410034804031441c0c1d0803030b2024811080582c00195032000803074440d10604041003681043e00e810284401c0c0880d2031074025480408080c2a49800c0c01542c1c0d000d0b151203000b01034246000d001b0201000c001c299203020610896000d603880301c5442c10014404008922040040100d4000c0030031010001000a0700380b0b4a114029440c0540303402d64072a441c020034800907840c400800022000780d0038800d0809006000d11003d000b03a100107c3c0d81d1520540d1804809443c00c462a242c2d420941004034000280080850041e02d6030420020f032440030515420f41d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 725010000 1250 725008750 725008763
    0x90705060304080705060f1f050907140c0a03050909090a0c140f0d030f0e180408030c07050307030f0f050711010807031119090503070305150a090f1214040f03 70
    0x740c40728580b0344198054a20024a6805074a04020700455520702c01f13031103101c140c0d01804039216595a0f158084555001d059009400e0f10001402e044c040c84804240340c0340c07038064505e00a50081c0b46400c02c100304c02c046000440003e8144800d1800009543e0400c02c00c201518000149a583c4c00406005208038081d080c03100203486d01c650f640c0c5960020034000a004400703191a01c2c030b00140300c0310000390783c140814481c1104407002d04042e888603090110031601c0000300c9d01c0f02d80380c0c00429040241310f10383c5954200f000a00094051014040b914407039140e10711000c05c41d40000d043005143c05000410000709010400101d0110710510724000000e080c641c03065100d07450128003030844016520080c0e8000200c1510030403061103000c50741e1500d40d03141d9100750b0f01e5004044d100c41c2d0600c809401d0f60b003e24010718048600c2d0640c190030103500030b0002090700c09681c0d072114140c0290000c1e51700f4400d8030603101e110361300042c6d06802018801189480e240c2040043e188a405a00000c0d020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 725011250 1250 725010000 725010007
    0x1060504032006030403080412050705102004030501060e0f0c1902120c06041110120c12290123090a0b040b030714070f12212309070506 60
    0x542040b911040841c2c000740030705940e13140c203040c0078010100039103007103403607095803641c94440510a030b054402d00c9a05c400a0061581c3d02041d15014084440705401e540300303a2564059846c00e280018802980300b0700001c0f424529241804422080c010100030410452000b0858100e01400c02c0321402500440c0c0d5400c1c1c03540c2d88208929155200a0070405003400299020310031400185152083d84607144503646496a0b40511580e005190901070120b00700720000c4441c02070a03042400c6940c1b40c0c0c50a010402d9050301d0030f0050310a103000600d8a40085001c00700340340ca803050300007103e540a080c0740c122001c1c2030020310107000702e1b03040c82a842400030030b00300c105e965601c1003200100389071030446844603140d2414801640c000d8503240301050440e5110741da13a1600e0b0003614010741e0000d01d5000095410344031801d90141c455240e8042000180d604c1c0c4405420300070040340e4040d05003000810340064a800200640650710988081803510700300841144001505c4ac1941c04c1510380b25103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 725012500 1250 725011250 725011283
    0xe09060f071d06180909070f0b04050a050d0602070501020d0906140601050307030c0c051501150305090307120201020d061715160f0c1a07170423070f0f031a0106050403 74
    0x103034221304641c0540e122410760103104d0403480009070001660016601030214039a2282c01c1c102600c628031540741c006c491000c00b00032514020740c00e031003070602605000d4980303662b5559643c2203a21000705c03103030307540d82d00c001c41414850704e845182d0750f0907280703100c1a000342004000a071450000134895010142c981c00000442442401b0364618140c0c80b0003140c0c0b401c5078800c2c02c075504000034050000f4a21007803400000c40c51080c015903000300b100c072014518100c0a6110b802000c0060000b0100350343d020001d041e40b010640c0f0542000f85141c0e5640074810f8500380e00c003400c0c0482c40c02002e40d041c1d8568203110520020f10114a6034180d1401e2040007507030569800c0c1c1e01401e08a030090b001620141500c82c5440c1703406401441810244c2c0c820407030a00700e02c2c00a19681342640d01810414111074866408001221046c0d00c25081d201206c0c1211f69031006160300c505282c003c0c100c040b6036180c0c00c1042011800c030401025500000c0d0030000c1d81411401015402280b0001d41441e5140c0c01450 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 725013750 1250 725012500 725012527
    0xe060c0918040b0103050c0307030f080d0b09040c03020a061412041a0c0d0c030c0e0f040609091104050a0c1e031b0206060102150c1c060e09060f071d06 67
    0x119001c2100c1412440d00d030a0600440d102c800340300035030340d600951040f5000c0d0b150210719a020b0700d60041c05901c4111035611480101d40241b00141c80c0b1680e244225200d40d40c40c02c1c1c3ea0741c03063b440b40044008481c01c40c81403040300b04140d0322640501c22244c0d4464010380c18881600d0340036104088640c0c150340c2d107050503c0011540d072010f1000c0b41c0101c0a000040240d04020014401c405006200030100c186d001c07000c55200080308800183d80d40da6151071450484500d18508600500c04034081d52241008000c90303d0b6035004442e801c2c0352a488064900b494010b860344000d090f0002c0281c010000405081c0b0750103c1cbc001d00a0001126201d900e446c000e62203139544040001e1242001d185031785001e55548019200c0394058800c1d038007071a04405103001c040b0f202c0e04922000600b8030103040c85002c080c94810490340c1010740c8403200458800c00480c9094440c2844070000c10a6003400950740c520706501420701c070100f060800b040a000d08001d03462020310b6400392040c5580d000c01ca450007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 725015000 1250 725013750 725013769
    0x40204020702040c0c030807080412030e0c030708010c03140f07121404120e0a210201021e030702011e17180d21051519030b131101030e060c09 63
    0xb50f02c00d1600034454402c1c2d0b03012036448000380c800e89a408141d00e5901c000d98020324115402408016803030000510f5038480e411803014001200103c0b4183d10243e0006414a07505820800040e990b601c8011100f030303410300070f0034040360700940b203010b8600306060100b03007608000700030354188411054000d52604450f0b11080520510007110002410b0518203007a4140d03860b1941c00020b40380588844080c941107803040112500000320000d250203010f4851070035170010006034194003030f202902c4485030001201701031500d1550301441d40c44c000c51001402140040c0b10043340922081035941102d5040103803d200c1c40580781c0300394416a15200e506e8019003c8940341102e40c0105800c419a05400c1011708008000101e200300c82c2c2440d4014010448104a80305071039401d00341101c280509008109034032000ca03c0c005520720b02d41326180c0f004c0b07020341983d0322606005410b40070070038084d00c81c856000c00b51007480e007402061125074607030390b9030343c005800003000c81030009005026a40b040110f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 725016250 1250 725015000 725015003
    0xc02030d030e0307140d03050601050c0a03080c04030c14010f09080705010315090c02011d0d1b0314030709151106061908010c03020d0606020705060a030c0201021303060f140601170402040207 84
    0x2d03000340717541e108101e03290350603c4004d10109090202007002e03503003d00309035400d40c90003000800003144903480480d600c00020340023680c2c0704810000800170034038044c0840040d000c0d050b086084030000e0070004000703404100508080001144c0148065100031482070f049070024600411512904201e504403585664010030115152009000c1140c1c1c040d00005111304d0703036852030185200001641c40c0c4889400c1100c03800642c095508201100401c94000c0d806802460300c50703001001400d400010741e20944044000c10041c2a08201c80242c40c2c1d000e960800ca14a40408100ca100582c9642c070100a84114410800d46070301400c150030004125004150440007401b49281d03403407000d0000e503c214800f016041c14400003041a42c0005003280403038002401892801240c62400ca00903d010081c2400b155020004d4607400c0c0703c41202d5402540c06a400055035140303804440040b244008044101c071110030301044a26030f0805083c00b40d070351180300482101d907120300c0010300a01c0760880 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 725017500 1250 725016250 725016263
    0x303051c090f03030606142b05040308010e070207061706030115090f0f0605060412030c0f03050c0120191e0e03070602070e04020d0f021201020c0705010c02030d030e0307 75
    0x2410b01002101041020380240c500700071054403440101d0b0646e400070000c1c01c0344941004858038100c00b00d00d40d07128441850a00389000b03e0108241d000b5143c06a40c20b400040340000140b0042c881086c442c2c0c1c101000e80024200309140c0f02e0041c010404150710b2114002e5114009600c0e52001e41000d401c040e84804d441c1c500c140c507814048001c010401003849010326155611601c08018801c1c90250381e4011320303c038241032401e504184820203070402181000f032805c0220f0005450605241301d50752003506c3d032644841826019908440c9400c154884520540f407800d03022030701840842d1014440c42d0b451100c0381e000d03410f080d1050540c0d00034240c081da246840d000c202d964042c0c0c52880010741101a00c4206903100d0040f40c0e150b110313000e040680002c50340440c0040c900b102c446140d1030300c40c01040010b4103ca0f0009000d4100c4101c0e60903180c1d400150000c520042800182c0c0a00401d00705160301c00d074240c010a40e10315400f0400c200b4140d83e5001e100c0105c0303040081c3d902c02c917440384 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 725018750 1250 725017500 725017511
    0x6020f2a031e0f190f0212010c0816050304030e092a07060606020a050606040f1b080a0e0106140d0c0807031202070f0b120c090d060b0f03060408040303051c 69
    0x1024194115020507000345a001d0340c4208101c059001ca0791203989000d05010340710000701500d804400b0b00d003205c006c0707078403404a21100c94800002c1c05940711010441c0c440b011146840342000c840d00b042c006040013004001c200300400a500a45034416030642622421510b0341c0380c41d046042860a42120552440b45a644a500416002c003d202c46441b645c01030091035034811043e41e4926281100802e1600201c0c00500a410aa0300100caa000300341710100d1541620005020701e601003820000c0010f1007002000501030250003440c0d0340701880002000400c1c0f030a910b8a650810503069684a1049100300009000c03a0301050b6014040d407400f901c03021a40d034688a44002040740c6084054014003000003100c1c880b2409010441e81001100c0c1d01c1e210307003040759180b8144010310140444c80113001c10203254079082c201e60301c024481c4100140c0c1d07624032400c0202d406420b0920794807039888034013048001904207040c0e03000c0f2039050900545411440420a0a440b0f005c0805a109480c24 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 725020000 1250 725018750 725018773
    0xb180a020f160c050303190305040c0b0c030a030b10021209042406090911040501050a1701180506030613030810032910050f010e03010f1b0906020f2a03 67
    0xc1c07900c160b0252154404000c0603a494040c540c882c01380040075901e4000c1e8003d5854407070f000b504407a9000d03200303442c12064152078150301101030304981c404800390390020541810454043c807401e140701c08121340c0e44e114148003a000940e00c15010940341e03088200410b9181c082d442c2c0790028100f6818413038a0300d6030030450b101d03403640a19140c07082400207203103070b000041c400c00180b0400355140c5038071882510b090f081c0001901c3c0c1c1e601280081c010400300b1208900d5498004115034068007603544582c807a0100001004165000035000300d21981201040c000380c004541940050554981418221541c84141c4d03042c494220f40d0001e4119800030002d04142d1481c81200c9090f00b1240b0184011500d0302c10400d0110322190054507040380c4c146c0c2c07007d4482c1d130103002010354040c402000891640c401040000a40d08a0520716181d42004c124108042e600088441d0117400a480106101d2440080d52a41c07200d0010090401400700d100c4513035558114003078003031125400340403250311900c603 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 725021250 1250 725020000 725020027
    0x804030212210316080402030a0c080708070603021804050c0d060803070b0109051501081f080a1115030406050c0c031b0609070506270a0b0d0f0b180a020f 68
    0x460000040c2e22407080c2c50a00310340d00c4280c2c1d02801140c05810803030500b009041c0e500380801b800c241e0f458482c0c0d030b00b0000001d1001a00745c2c068084003028000c801d242c0440585808050b4128006040c014419040ca00280300744118800c08116800300f110b07191610740c000d5030701c507031080180420300344800810512000001020054410004003030580e0340e604102c405c80700150746030401c036a42140f60302c8075584a55502a0424000a207000c02800220000c10950205030f005c5542c03070704002041e800744242601101c041e0134040d10004000211803070401214800240001e0400d540c51010030001281740d02034682c00b850040c2240c0e0b6502c040d1040800352104001e0300e0340d41e0301c00c030800200001004100041140c2c00940120300f41480d1180d0b50b00c8400a070a08044406503040351034075595503601041c4014022100001d81e80c11000184005840d12101403890007802e00102c41e0150303c0345c81c070703809448560101c0503099454265a54002c2d02c500000b952944402044c500b603c14803 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 725022500 1250 725021250 725021263
    0x2e0e060c07022d01230a0309020301180510110c06130501020d060e0a05010906051507060e031303030212091005181f02011406010906110309060a081503011b0c0804030212 75
    0x4244ca030a145d0225002c2050880d000240300745d5200c250500c202251a800790b00610b0040744020004114140f00c01d82e004402810501c05840c0c47e8400c9040c801940750b03030706c2142c058022600d62325107810584100d190340c40c80701400001145401200500034054294195000014040020702805666a4004100c110240e035070003c00c2d8030340000000d201d41d182c442da6080701d0f4041e0891260300640c2040d2907464114200c19510b02e034807000c04125540080c80107100d00340c2001c0d0401482170550030002c2c50900306c01d0030300c0104c00080000103015514000f410505c03000350315242d55140b0503441414400e102c0b1a401e19081501300c034030180421151020300001200e158000c0004d07020740c0b80681001e441c15500c86000c50f0407603505018080c41500d42c0c07006851040c040324138003041c4201082c40d507407181c80090f002410b0751080c031460503a03440c40350510702011802441401590381c10481b5041e1041c44110a00032250700e403e080151707031015280150f1700241400e400600581509403100e2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 725023750 1250 725022500 725022589
    0x171204020111010501030b0c180418051e1905211b0c0f090c1b01050a050c0901080a0f0b030f0304030309050105130303202e0e060c0702 60
    0x10401c42442c0020201441201c0c1244e0b04107141020b41c0c0c50b00c504070031840d44490794002250703046c1c003e0008940c640e4011000c8040a02265034803801e540d042aa0500720071464a02412030105900d00080c42c0003e81001503800c83c0d40c5890000c40f4501d0003d2138500d019652b450103128402c0f88034002c03144080501a004824a08060811221a11130ba260742010b4072103503000c45205001c0ca06804d0480540d6400040641c2c0145400742c280144a0407200140300610181c0d194000c00c04003070380502600e40c004011000c01070504072181d00280c4031400082c0966125035544c0d88030460744501ea00444401e2101505035404956090311750782c0c03283d1150105401043d6141800185544604101d50b18417486101c08a08181581c0d01101c00c280d00045000c0703c0b05915074001c1c000e1409000c1050400c040940c20302c001061140041c940c1040040c101d240680b6005091094450104616500c03481c80e10340c0c682c7c0e40c0146c0c40040d0342c403980d503002d610b80714440016141582c01c4407440b001091 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 725025000 1250 725023750 725023757
    0x150b06040909050705120d0504150507170306030d0c0f0213060f080a0b06060403050d230316020d03050621030705010c081f05180a0e062d10050d1712040201 69
    0xd154980007541da5449100030b00001d23400f00010802462501c4d446d819055041c98100d281020b0b540f14020700c00c950380081c5840010001c14030509140401c400d46c00e2079043e0504618000c41a00c0b0250000d844800107809600958041454051150321010150441d010804400c6071902d400e1a583c40041c0012104110180007246a038a040815201183d0748900100200440303004210b40c0c501c0c846102c106402004462201c200ca03618000d5840781c061499940620010400020701d01101c032046c0e4814075140c40c09010007034a9910308901c103814401d00122103810340c1078525195110f289005801e035445d003c2c4150107190300465081c040c840380355500c181d0b50310611410721a540103104240e88003d6404808041c921440d0810386e004601c0d44002448407408141582440c0085401b04099540714508002c0007c01e26442b019090702485841c50038030f015490b403001240c40c0d01485100e440807006010820014851810070301503421a05620b944406082e200e596030161030480c0407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 725026250 1250 725025000 725025019
    0x6050409180b1e0f0408031801020c030d0b0117071b0309081c11060c0417100c08060102101116140708240f1b071428150b06040909050705 61
    0x80c4040703000c4c00c602880e00600018030716128080840c2e81540100440078441d5000d1000d43d944450500140c845008a04400320f00400c4d08000146005c40340419003110000078014000703e25070003008104440c0f00300c003845150f030089040682e1035035010750041101e4071906410311024440885c0844a0420f01d03120809050111390000d51265012600365120380c400740b2007041556054451084002c10041c10394070f403840c1c14614402655035401c40c41d008100c64805101042d40d04008481410340c48071030802596000f4400707010a413164030018280e12011281c21410b1084500315011010034600489016950703c2d12219262005d00a0300e0b4190702618607040d0411109107249c078458103020308010b40307035920300c2011041c00c0110b0752410070345582445040c001072651f01d5103aa425455800914810301a580345810864170300f201c66848100b0f4011480000780845c140d21111484102c0100713400079580c1c0810024020780d4032803100c3c1070034a240e0105201300414241e00703442054808410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 725027500 1250 725026250 725026261
    0x20c062a0a0b0402010509010c050607021c030c0c020f27060102010c0503040206032802040305161a0a0302070201030b0d08030a0b0406062012030702160501080106050409180b1e 78
    0x441d41800d4001802c00341c0384400290043d80303d0750013040e801105041502c0300310713425120b084c5440001c55694005da0300c080c0300701c40404104106a022a00d440c603081c041c1c80c1402d000140361200009000b030040c0b00b0500109040c0c1d480b144c00343e0800003400c11608114008070040a0f180742e003900d5442c059440c0001e06148240700310101c1c1d204903006000e03e441d588640645c08a0a40760715403500400407a60b514038507080ea54001800114001d100a048510300c01c2c4050111740d400342d00104103407594201410554885030184e554585107818010303243c20503400140c010b0040354a40740d41c844030380300800c3e08001e800000b440c040c0c0300e000f1041048010940c1400121380ca6401260017140d8203000024940ca0a00d400ca050940c1480c00e03205480780c0c1a5052265410941340c600c0940c20448203958084801880540100f109103068010395141420183c498450381c01240065034481040a804000170f0318448522603004c65114081e02c2d2501c40700604501031180c408183e1440e501084 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 725028750 1250 725027500 725027503
    0x60302070618031808061b03070306080d09030b0603192d03050403110909060a18020405090a0b0a0603030801050103020a110f010b010905030105040512130905074a01020c062a 77
    0x14440e4000152048487c45111300881694200604080c02c06451310b101254081c4d05210001400d4196203d200e1030900b58680380000d00d000504c0139002e5800054600c03c0182001401505d0391b800202d0b0323a40c00060340030b24803c074100b40340a04085410001d040303010164804018401c03130b80201844246502d01c582080520303001035803030211540c0201c01080c0701d00351580c4003c07901c840c03d07101303030b01780900d50b6002c04e05942c021603200a0942002640000f40b01280d541c182d88040003d03010003445041d50341c090084001801000c0c10103501056802c1c50314001c4c0c2c0c4102107560280304039901e6809001074280646400020140020031001000460742014003d5501a5030703c40050300704105080c0d640410f9400042e0300942080490744009420700c481d108403030255101c0c0d910110800e100c120702030030310242030b803080800803407502e0383d8105c0c5007000d0090341200c9080b881d000220554440100e10b002410701c2c0c243c1d4040000174003c00c0c0e02010228801c6012014194100710000010696 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 725030000 1250 725028750 725028763
    0x905010201020a02150a0b04090f05060c070c14060c0303090d030e030406140a0923030c1f0e0a080d0806030f0106030221011d01020a090f0609060302070618031808 72
    0x3c000740e88045035030400e030400d004241d40c1c42010f080000a000701100d0024095541c0e884080d12440d00c054604024800d040c450305030304c54101c51801d854901560703141078100241f4400c80b4a0015040c1054610340d954004880400130300b1000c682c0c0300c2c00c3c81180951202c0c0c00802000209280c01c4203450300220100a80301201c8040d00c1d00c0c280034581c0d1a5106065000d240da040401403d4140468113a84120781d40c1400031a001220807041c20715802d052403e0400050581310f07006040c0c040b6041d55001c1c8a00250920134500350002811140100780558003e8021903400d019490f104000d00307038401c00f807d10a081c118104d442c0f82c42c080c402242291180d001c060f4100f01c00d940c507513030b80348404480d04c4d5036101c622000150341c104113030b0243c59410903080918026500000e0f801c083e59442031022015150642124450a02d0140c000d000c040c3c4030f2081a05150300420380505012417a40800b0400f00c40a2054880825905d0000d180e40c6d608104118110702007007004c42c0005000441 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 725031250 1250 725030000 725030017
    0xa12030e1507170a0603051e01050c030f01030212100c26011d13021518090c0912150c070c2909192403020304080d0e070321090501020102 61
    0x20003a0f020b6421940350034000c030007800e000e4850b03181c000010000e0703810803c901030303040c0d210345c89080c46140c91011800d484010340a031007070040c01c3c014008000c61904095044a90403034042d12507070a6464510700f0441c0001d00d059410b403501c1e20070504650084540b50301c0e0b540340e41880303404014111804404800078084c180020640f40c25003030a424400d40c066402c80b044003000081036500e98006004121040d03141202181c0c0880c50301c031110303841d020403941e021040320031054914003807a01880c0343c010032024502c07498000481e0401d600f0244044540d810419907c07805520b0100941c0c02181e0000f4421140c40200e4207000a644402400c0c60b46002811624001c0100041100101036001a96100c0e0700c00000d88a0303518221481580707900500b80b034541910f01c07014011040e980c44226000303a10515004004010010301c0410450340700400ca03240000f800f01c0e40d445002d00d401c0355500020071000c816403400d002034004280d100702d0954940ea40300d141c01d40707440049003070b40551480c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 725032500 1250 725031250 725031257
    0x60a080a050706081e01031115120a0f0e120403031806020d081017060403030f060503070b03150901080c090105040e0a2a03110a06020106030c170a12030e1507 70
    0xb41407000b20710414005400020030400c11501d0005c0034140103541c50281d00840307402a4503094031019050100500321403603501c0c001981003d00c00d084041d1400070080011549a5840030307000c420305100c0c0e010700c0c0c02d05c2e000c030100c684421100143c0c521650081c0002d60202c0c03a00705030384225a050466200556140d9400341c11400b910b008143c910190182008803400ba0b011004039500c03428144000c1203400719001401641804e042c0617046a06c1422520b5203039007400014005920000340c500e04480d0b103c1031460f56507036200c560a004681d89003c050b4000b0b05c00f800080c103054002b5200309960b404440343c0d1120f9a8800420003151246100f43d017887d0030245400340420100941c0364520141802c0310310000010447c60303400c040741030b0000c80785e00c003128180b210700d800c04059510103005030340000c119290850312200003441c0f00d4415102410b00c0c3d03c4418480880034014040b10aa219424844013000910050301808003200c064109220b91801d002124a24a01d0a409541d1a46 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 725033750 1250 725032500 725032513
    0x303410405091b0d0c0e040c27081f0204050301021204060645110c010e150c1806040306090b13110d05070f0306050f160504060f02100504050105060a080a05 69
    0x950000c040c03c5c180e00c10030203010500c07110040545803030060382505405540d620004144c0c0c0c82e5821411000c81e10010425404004107000754240050709040744602204421060061a80c0c1000030784507d070803c0e5015400803812110801350051403134002c511843c4144507454480c3c0807903c20022100d100d51610a8050f00240d07d11005102d0b0780b2460f142c9050199151340618418003902d60f5407005540299001510042601d02889085400a140303c0981b041c84107081c5000307262400900300b00d01d001400501039460484078640d4040b1420094070981d213481c0d40e4103052008000316107003070b141d050f00c0f04001540385024220f41c218065000e0342c5c2010203107011051280d17000b016242160644600318012a405840b08a010000c40c4034085c0400c051515042469a2450107000703030b800c515180040c03001d510f802c9030968042d00d209180c00d032204000c0d84012032a0980100701c0c175080d030349414244400d000d07064105c10300c00e8100307448401348a0b503204130a5a8900000c1c030054100c1d000344 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 725035000 1250 725033750 725033767
    0x10507021e031903090b040803091e0a02060a0504030507060305010501120b01080114030a0803131101090e0406020703052505070b0405060f0708090613140a0303410405091b 76
    0x81210034443c02042c540059a08900e035605101d90b081914152440c80c804000c100300314804000c001c98191603900120b144140450030640e9401c031109001380306450109114400a100e1000d80e801550001d007110585669444068000c041c2030140c2400035040c1281d0f05640b1049020307910000c0b0041c0d481d1581d5a10b0400d080310402c00100100b40c0c03602a000074a4081840b1700081c1d4041c8a070520098112040d514040c99030280c440d03415410b2000681d8208551014020b50650060700b1000c0907a842007545070440e090b1051341d00c0c4604d069282401d001a0540061000d86628446c1c0202c40455803210300c403551901a41c03241c2a03000c401088915501d0f00c204018001403440b0302c01d050705106e00400091841d80202801c45d41100292a0400541041c4400406161010350f5080811070464070000c290754000f91000d50f5500c0b030b04502c00d2490b8030484500c9490814074800b4400c064044140880741e40c0a885003a210b103030480b01051003906c100c001380018100d08529145001d201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 725036250 1250 725035000 725035027
    0x91e030c01080412111c0801050414060a171504051e0712030e040605150c01140403080708070e0a151202160f05100f05160e0a26030a02010507021e03 66
    0x300c5003031129010300d040d070480b685603081b02d403080240903890303100b407560514052000b100c2c003c610100041c4007090910803507480d0110381500383d401c1c07025846101404111254a800b40000300c0c2440807034894100024440c0204403100c100e00e402c2626a047c102114502d503039a070340340c024007400c80c405000c5100024003030080c0250204000d17001041b070a9980740010302c0c801c00c03d08541c1480350000783c1c800b0405420300c0350b005420089913140c01e89042913103000300117010052070207042c0482da0000c202464003030801068100c0e030040000c5045512104103202d801045604200407407001c40c443e004441443c001d8614a0849123403907012425261148110b2a442c04001d5426009840c0e00d0705046405000e0182c20000c10341c00410306017400440c664001544250030010420000d0704541c40b580c61125000858460100381d00c00280c87c00030040718088040c0c0054524400040c40304092501904007078441c0802c0e400b40c171000c0002c1c022456032098940e0240080e40c2003001001d050300349 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 725037500 1250 725036250 725036267
    0x8010303201b0a0f0807050a06020303040c0b16020a080f15040203100c05041a130803090a090209030102160f0b060114030103031d100305090c01030207051e03091e030c01080412 78
    0x1c0041518100d40d03601c0c0c0009030200c031a504000c0c820f800c01c070000c1c441f5041c6142140c00800c501d10055156140c40d40340c9024541d828050302e001c1c1c130000514102101e00d07401e018034040e9001004224030076a10912127035900c40206504540e4003444a280d02d182c0380041402d84281e4010b0043d0980c410301d401098024101204451306100d81032002280138584101e0034404070a982101c107a507800c07941d01000352040b41e0b510164055208000c2c240c41503c60381c103178408507031007021b025881e02c14003c006406809403d100048200c03154400038103210480c00d0396070301c45002da071981c810f5403039110044a01e0300c0c150810302906403041004100280c82504d40c2160544001d80042d101c40c240c40028886540c8040103e00007a04c40c0144102038806200f900001d8009003801c515100c03250307642645039107840c2c1e41d00d1a5004406481c84602c403060007201e1a400000380280b0315000c000d20521400114401745c10300910814080300101e50050444502603030308000345020f02c0d80151411100b010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 725038750 1250 725037500 725037553
    0x3180102250c090522050f0a03120c170412170c130602030a021b0d170a021002090a05040504020a08010f0e0c0a0509070c030504030b0103030801030320 67
    0x103608100100740d5070814111414220500c2000081045007410702403040d5070260001003580b85403200f030014a22281190034801100d0802d515596074490403c5c0d07082003801040c40700c1a00a41c4800d90030150703c010f50143d400030030203080281c0d04a074541101c540042e11902c511414060020401054031035281640c0028a880c01800b05944420030703440c50350f070a950708940321034040b488014208521041c403001c1c051510065090a983c464000e40e40c20030305403c290348007443c6000c0360f20b585031400388240c0c03543c0000800204c0c1d072641c0c0612a00b40d22041c03101006008290486104d00c0071130003210f068210051040d0140c0d0f091000304801814040c004a0784440d5503080041c1c441e0b42801429004070b0590400600d11205002c0c00d07040600100c0110b225480c08103042c00540d81d444410303500f0030300900c1c210060296524007038566225503000a40780b403803010000010154050710302810707030344030f562120b0198400d6207489110420020110301d1503003100018507401c1c410000580903c0c2c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 725040000 1250 725038750 725038753
    0x607081b0702062a1219050d0c02031332030109060c090f210809191215020309071505070b0a1d16050904020a09020a03140108030f0318 60
    0x310280d0020fa05680101c60804042004222036034054022500c0ca411130900301001d019020a00c82842180c0e1080389000901200c01c2158220307050710420645d050604091001c201450107060043c2da242c02200d1000000c1802000c046002e42c0004918000000042e911000d800c028418030a0240145041150590741e13030340080340455400e000f4030308144111740360141c0b4182820302c156025103560300860000d130f10406614010342c040175100e00300c0c240c020150b603031600c034603600048543e0103035000540e400030184c002281c61418075028000b1303a8454808420442c41200c44802030740070407150000107402c02030040080b107100306203100d8070020f0340c030704035240a05603550820558801d031038040600365554051080c01104210b0349000c086000e0082c42d10002c002105034070017400740603a40c0290b81d20720100d82107449460201e0060500d01d201551124012103005000b41404010480c220240000000701c0320000301c111002d1307480842070b0b6881c5a45013120310302030000c050383c0a400e5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 725041250 1250 725040000 725040007
    0x3020301061e150e0315010f08070305030d02070507030203030f12010f060f18090f021801030b060711010203160615050105040b040909140115081506100e01031b0e0406080607081b 79
    0x15035500340420040c90046c124003d1455041c007107182c81c1e07108503400071101903214960520203e4800020b0768803060b090400983d80d50340518106041c5403403070303000079014480403074031910841c588800381046078941424010f4980c0e072804c9800000c2d03e10702c80c0c3c1021030b8041004006c450b1040c120f509002d007142d003600701255a125106030032100b91130760046900346c0c0845e8810310301101002490030045e09103002d001d0580100005000b610560070002d0584070140d40d082d285900074815525600490300441602c00d00d1410400050031801c1500400c400003003401150540c00384040c4d030281ca800811680c28a8104501100204100ca4013640c1070307540052a40e40c041024000ca5812900300c4450806041c60100369901c0d00c10f403100765006641000c0b040211940715505d141d0069241803038224414196200140d0013001c800d0455200f08007a1441c103174035581c1100c01c0101560056404002143d9a00540390f1144c8041e100c04c40042c2813000031074611904002010505040f91906918 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 725042500 1250 725041250 725041277
    0x10b120907170106030b16321b0f0a0b01090b0a0504020706060e010605090d2301050406050106170903031f090f0c03050a1a13022203020301061e15 65
    0x90b0700c5002c07428440300d0380d192101802001924170005410800000b8803441444400b1f002601912213074042c00d070004080c0b2100144042d103125000d13402202c0da41c2d1203a40f4401c1c1080c05410080e0300700c0d40801c5118194841c0c511900004418000c0b030703004503800c5e003240d090801681c003501d81c01c00c1465020084010101d20b0b41d580d8801001298400c03000014000d142c02900021410140c5c8480305000742400109915100c2040301890260b02c070250303220900700041081040080091170401d15840d100c00c210401006620041c140c0d81e054445020100c5000012003170741c001110000c0050704240081007400c545081050101e840d020510143c40e078507074079507004072203140034140382c01c98a8010b1084413075014418182c204803a2401031000d5a2421111a849200061118024070361000403060000c2d86a05540300d8061241804201000c081e500c0b10781031100f0f000691095280c84000905450701c5041d8032001e1130000942d00e0141d10301031001005505070b03290300c002d12512504401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 725043750 1250 725042500 725042519
    0x10c080d05010927151e0905010f230c0903030a0306053c041b030b09060402070c0303120204151e091d090a0b042108010b120907 57
    0x52034031000e034005030740d601d4080703e54240c1d4102e00d2100b502d01481030b480b07043c0380320b4880901c01142c0c1000b0402000d808450700c4400408181e0041244180c241c12040d00100240d041034181600440090000d030b84445150012101c1c0c000400c050759002d4403401d58240c0176000141e90020318036a0003400c10390007001080c1554404a00100001e0f41c410050000346041107151029421120301a5168032000000078107140034080c1404014031102c0303d200040ea2103800c00da441d0318200d4045600740b40c10340c9015015214181480d40325103404400998903040c188241c691158100401001d0303c1d16644064600c0031900034a03401c01c9408010110b034202e610408180008011759500003814050b420044c500030f683e03810700040008c21642002100d40c3d203a08811880d61440400c40c0c00d807185140503207001c24868000b00032007210b2042006010f801c0103ca00840030100200c407501000d2041255441001d004801c500f45083c85100c0104212216281d07000e1010b108950541d0380b522202c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 725045000 1250 725043750 725043757
    0x406090e0a060e09030a090b0405062b0c0c2913080705070e0708070c050303060f030f06091e01020301050d03030b060d0915110405031e070b21150d11010c08 69
    0x4140517400052450303000c6a10040440040940d0441c81d030615003400002600c900c520020350304095510105003840d2010440111003042c24040d003003080b000103800c06000d0101c1040300365484a00c20503007417144200c10820359480640c4210503411960b860400b65a4132403072490640e0000340501050700003410400080d80070303000601101d080c91130030610007411100002c014508104030050100f0000e8400010f90b0b030844007c03540000103108100210b850141c1c02407540031140310356001d000300420041004030002d003090f40e00c004417029100b64142030348420312805801c01e00c0d800d00003010074840d501035002910010111464034007882c6941c2e09450b071484013541c1300da00c0a0301041208500340700300300c21000c0b0180024202498a80041c0d295140840c0c0034140e40b4641ea04804056028041e200151802401003030b11000d41c40b80341503521041080c2048003110340e82c0811462008500c495a421000030000600480e503640c1c1d02071110b060700261030510950750386420004401030040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 725046250 1250 725045000 725045011
    0x3030903170c03041709090a0b06090607060b2b080306130515190e010b072102061b0403050c0d021306030b10060305040c06051e07050309150406090e0a060e 69
    0xb640d128100760400139000480b8a409400b0358900304049901c540340c0c918035a90046e05442c1c0010410203240c0030500d00c4c800c1e070709080c0d40007400042c18000c00c00305074051050320360309030b5400400e0000003200d0300c612000c1800c120101c030b03034071301c029030000310391000442e813002014068500c0c2d2028a00e65406072042500e55111a800a0a903005c45043c0030f24032100c11400602000700c050710341401c4d00c000001c18003403014820800141c450030711910502c20654415140b01c0d54064507502c0000035101d880546494a200e60341007620481c4040031015034061b282c101003d081894105000c0141120600404917080b001840801140700e4081c270800008500416258800740788c40c035075000381d260481c0c00030010b051900c400e20000c10010541501640d2150810a40d114203500c81c0400c28241085403070b020000004002040002c04009401481415143c80511114060104100e8011030150800048014000304141c203400b01c40140c1100500f40002031840c0c0320358541000d0f040c00c803003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 725047500 1250 725046250 725046271
    0x20c0109050c150a0c0609020a0f1410090b0315060301061d040204060f0c1119152a0f0501060b0705100c081819030801090c18030303090317 62
    0x15180c14440c040c024080c20510480c1c90403110200684401c0060040b0805481007226100400c403c008070f03179001c3d200280d0002c1240c4010744d519404a411a980340c0a01842447d500610308030b1400c1081880340b071f4440c6a2140f00481c0d00f414406001608000d268155402440c00c0907580c035194400107601130103c5560701c414500405002c9240c040032111050b000303d00c10002080000c0d88511403500a44c542d11704609080c0311410001d210b1320480100603071100d801c00044902d1031800c0524012111200080c8007281c0c100342080c2d5822142c81c2000301c0b0082c443e8415280c070405140c19014140c0700e490300c8a0301e83c0c1c0c0c1d0b4441c2c03400c690b900d400c00440382c5400a50841807190400019100c3c1da800007007405152454000200301c2c41020f084181401985000150041014071030134200401c1c0c00e81030140c80c8824180100704400030300c605a221407400d200c540f02d05203d51006619140051017004100780345035800c4000307046070704060f41048a280901d080e102c0468142c0b60052450340c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 725048750 1250 725047500 725047511
    0x5040b091908180d0209040803070e0f0f09070504170a121e05162f0306150405040f05190b0105190519050a0f080d080f1311150d061d041410020c01 65
    0x50180bd50925910a06d104807100d10104019039a640283d10000704190390444040e16940700c10745080c0290340040e01148000d0300600d40010000819043c0b00e130150109040c02c2c120030000340d50b43c8001c084028107440100c2d0343d09a209004800412075025121001c80c201d02c216140c007330860b4149110022068259410131003407040c401c00c21345100c20124081c04560030a4990b40720000d002d00d8840c1e014a840760001801d220340d800401150325002000d4074403401c181e400c0c00c94800c5031004101c6149880380000300305804e2409000c09425404ca0000d02c0150034041003141c00038009000c0403a00400907000b1440c2d846058031180100205500070380902d083c41030311401c04000c41c40150420a2a4007004500d50510f440190070191800c2202c183c2c1405080c00c4454018913103800340c0044448405001d401c20310700003000c601e40b0f0305030f003004415240c1c014504003481205095880381d0b4000e0100d4081006407029814505a41302212404104100c4180603a00034240025590b5500d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 725050000 1250 725048750 725048761
    0xd200c0705030f070f0e04110a090f110c0a0611090406030b09070b09010503070f030f02181804030c150b180a1a012a0605040b091908180d0209040803 66
    0x400983c41c290790031002a08803d8200a2511000e490ba4071842030488460008102409805d9081300f0000d01c010340f00c0456103454070100c401610040714850022483c1455400102044405481c40f07850341a0151881c0b00c1d55842c0c1101501c00306081c0c0000700e81c00c10018009560702e04c204c5e8021403240c2ea038000c4518005150a040400c07981c4a030070650010404140d441e0b900c0801c6980c41b8600e801d080d28010400b00c0114010310402e0070881c003240c4000f0304500500c82010b001030781c00504842204401e042d035416400c42d16826140200030a425207400f00001e80301d52010034103440420350001d908000800010b00b200741902c40d060340040c1d008103100340e8100601500303040a0300081c0c80d000c21221000000c0c2443e0001307607030b0303500340c01c072000d601030320407030281183ca055900000705000034146400d02c041c1101c42910140d615100707104480411000d094050031245070801d0502e030400c40300342c0030301044d070303907201842030340310044014000c0142c1e5124000b81c0500e01502042e40c407440c20707 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 725051250 1250 725050000 725050003
    0x1d042f0d0f0b120c0a0510020102072f010302040b0d051b370801030b100b041502150709030f0c0905070c02040b0f0312090301090c17011107080d200c070503 69
    0xc90f0b403045003d82004107504100d45845400c141210020385213400d8403400c0f203a0890081c003950100400c0110608041c0318101c00074030000d02886411500c0680c8480d11300300540c01c074032540c0b01e0108450410b00540381c6440c40f0b58030069006042c120104001c0503140c0015039203601012200b40d40343c00002d43c1d12411135a000c0c0311600300103800300125a48100d080041c292210500c8024407040300400000c01c10ad40c00110300c001403011001d41c1c1e03107964403100f11040032081d680b5a04014404c5035075120500410140041c000e6203181c481a001c0340c04c584448101d004980b02c15200542d800e400081c600e84a0321a1070321603584c9586a03090041c15104010942c1c850440403881544402401c01c000e42e000b2903820b401034500c81c1000c0c0d4070301c1e01b04007103409014030034405401c1c202c105c8070000c2d401da124003000540c0c0d81504020840c25680c3c0700114564061118041c0003e40e05104903001050158420f1804424045078043d40745246d000d550200ea000200c40f00d0240c00019003080981070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 725052500 1250 725051250 725051269
    0xb090f0d0501061e08061f091e1b051c02120a0f06141513050904140d03061802070204111303030e150304030c0f0803071d042f0d0f0b 59
    0x10b41846013925403900d002540d503118003500e0f0152070300394099a2000307804501c0c5560014880d00302c050141d401020300310382d1441e00080103000301e107040400d100e1810310a00051700b09661140c0f101d0b41000c0344205961715121102c11100759581d401c00c40f0208034800e200c5110311881d8158004a11004030034041c10503129680c0c04800203941054906c034807581d84920f0520315401d54500b007600c42a44015861005419074007158224286106100510500550340092003241c5000c80307044e0908804120212007042c4680d6002411440b10240440100e800074201540000c00101c0c40041e0702c10800100d5000c03114040d040710b0f400b40d041003003603040307002c2d150860380440320711090b105d5140700c144207417100410007402c2182500c04542048650701201000d01d0f00402103603220b10705000050300c407028980340d00903840a6003140c072616182600903040b4002401703c882480c0800742c000c1840c54040d0160b0781d0700242c0144505085010070303220b10b0030203c40801c0081840382c03030f84050096594 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 725053750 1250 725052500 725052539
    0x21070e030114070e060906071b0806100909150c02031b1501050f060d050403200d2a06020f092e140705011a090c040e010b090f0d050106 60
    0x1d0400301400d031000440141c0b1035000351241031585103140d04500080b0184506074903954040004944d45003441052038160096001803d80005002d07100c45502da03442e1000c0b00c0c0070080c03901c0c1702024410b034002c5170007411a4501c280c810001c0d07160703501c51810680d6115003a42c40107910102e4503802c45022402889490340407000078103004030f0907255100741581c2c140036280c010000d042089500c3e4850070103d4406072586601040302e410517280041a50ba00040d110144084140395026050130119901094405584402c0030b8411440002c1036440400710f40268540304040405c408901680020182e00c50755000155803481d072901004088402d00c0e80408684800303041da0009040b010f408600300030000d0030001840500c00c0f1800e502c911803007000900f5942013050801401342105440202600c049918903141d54424451850b9401184600300342c1e9044000100400c0d0755120061001070000790000c42503214010208900e50440f0108a41d541e40d254000c1002204918102140c107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 725055000 1250 725053750 725053753
    0x9120f120e0a060902150307080901061a0d1d0a0c080d081e0406181505390c0a081b03160204020d0f060b0a081608130821070e03 57
    0x103210740d444440da01c0450311401010180c0e03c64048042d592520601000904000b410039604e25003c40c0c0103001c481c2c01d030b0701042e5640c00e000020840d80440e0b00c8c60311240028105090800014440d23100161416007003d51111580140c402c06040c000d001c441001d40c010049000102d02d030800312172034040960290420040b0490900140035000700111000d0209004681a00e031901d06201009002c1104d0350307080102d4902c1d40408002ca01f5001d40780c500307068103003084140d85a43d2110402c4000030064140c10900881c80c0090f0b440481050b030100c880d115080d401c00582201c45480e14100c030b61300b40e46005010800225404052031401e60030700d000c10140d414001e1600b400050040113440007440340d0f80104009003e860783e9400010104107080702444040e5480c203100019501800d00100041d407a240040c0c4199218104210646c0d09540c82c0300ca070f552510083c0e42307208195581298090020000079048841c074081d580380140c2c981400b0001401d040708080d022100c6405028003d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 725056250 1250 725055000 725055011
    0x4110d17070b1b072901060e040f0902062d0c011b0c0503070b0604020d0c0e04181203050403140c061608040308070e030708070b0d15180f09120f12 65
    0x14103185029200300b071340e02400030000a071100d581d00d004403c0c140c002c800710b07124170380000400d560300201d00d08940c0b800391002c02005403206c0c540400c5e039103c05800381d088038003081450110151680340382e002c400c45815005541001171030300c50884c0d116032642c2c4c00d140c0d164000240c1503110130b10001002000741c1403110b842d00059856646901035040060640d5041c1d00c00030711075851300e40407142c0d03c507002c80302085070300800b84005d4a1f2101581420340100c1c6092104090b0303510812009640c0c54001d942c5c0242900100c400314007510006004604104d8401c0304500d001c4800b102500c40c5501003009042035160800011201c9084900c0f803604102d601c0007440080380c1c00c51181600b205091815040c00701200012900e003505e070381d00c141c07a103220701c0400003200c1c12100081c140710f101c040014031002c80084026420388480e030055120400c1151241146c100c996801038015079038410740401c00307841d55294102180308a1031400301054207018140700041e8445880d80700d081080310304016 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 725057500 1250 725056250 725056291
    0x509180609030c1009061d07030b0a200a0507080c0c011b030e010e061605010b0f0303070203030f16020a0b0d0e03160809040212161d01050304110d17070b 68
    0x82d200c410080400740c60355a542076200340b140d1b607080084010105207000b040e4000214038a80d480000784000d94110000401091b011001806008141c520600c1010074103c044002e4004e26400308c010a010b201007004040000b1380020042e00701d902050001c1c026a00341c40d8000b4115006001d810070543c12080108c00010b50000c4007590b54030301c00e180c040340c48000540400c40a110720100321051b540303100160810004150821035800760b050300e01d00d05d110440028142d4070302501c00f00a41c55041401180400d0722404081c0030b2145841d112681c8440e404d4001c0740c407020329a00080000178001411030401d01060007540740380003400300158a00844d01c0302c501201660b980c802403110400180d581e03250b0390360350141e13240c0415030103e864070390401c01380008102c01c0b01c402c504045403a100c0c04588050700c03003581e002c8115040c3c440360302d580e031682e840000c0004200320541c1d02c0010b141c17240001c118490070300211200404581591606a41410a1070b0b4900610480062142e4031030840d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 725058750 1250 725057500 725057503
    0x40201050f16060f06060908031201180b10081f03080a03090203100e0708060c0301060215040303091407180b1503070504150c1202030a020d0e06040509180609030c 72
    0x2a16026802005500e801e0b403040b41d14503a000000026140d142000d0740300e0900e00c2aa400003003110350644801120603a100402900d900603541c14070020b13912440100405410314000d014804109100081c03410070b01c60029042c1e10310f03500c8000015041c5030030041d8044680004840c1c441070705100c404810701e16500e441c05845048510010503403070308244011920208006000b50300400c03410b000c7d203080d6201040e0394401c0341c40b8990180c401d0101060404d01240c049034141c64155018100011282203402c01c11a8054411004c141d03407440c0340c80100c0c000a4030140c02000c1e00010742155464401d100480e01800704213860441d00e440344403201903550b070402c1c0b0302070a8428281500c1e951010429107481c0076680c1322003c54042c541c80c0000769603120b004d10a0991103085540308180ca8280c00300d0340c2e4001d0494440143e80b04560602000c0e000d221346005855008005a10303041d110b030040740348003000303485550307515128000b0000904428003140398031115150056040004000c0f0b5507 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 725060000 1250 725058750 725058757
    0x2031608130204230109020c0601051804030c03120e061009060e0412030b10020303090d0906081302040e030c0601080106080f070b0c0102090a0e040210030b01050d3603030b0904020105 81
    0x9120b9a030b2100318030100b0a80c601140508074200021381815a9180e060201039888102c00d5809030246400101e0103242c0f000058801d20204500c00003c1c0c1d455035010380f02040d196031f059050008510581407510f26074052500c139424800c3c00b508050a000c51509a07040d99a00104152130030001d040c810814810403443d0302940040c40e1110101000b00c06800424000c041d00c0e400401481034006096000001180a8420f10301281c4010002c0d42007100c2480f014010100000c40b0040030850420401000c0c0c0515800104009200320144505a11f5a80701d885a19030780c1d0000d01c0100f114110a100741d100510303022001d06071050b014101580c481c1103502034441c1008010501142e04403095041d01c2c95503c0161011080b551540100c2658003003c030b800f01e10031440150f09092440c800d0090089403e01a16810305212224501d40e014001d804141001907205918041ca0140d000c030083e00400c1c1c2c0c044203110009501d050040070b44140000d114040d0300070340c09000060341d11004a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 725061250 1250 725060000 725060003
    0x70606050619031d0d0207060f0c0c060503060f031e060c0415050c0c032d15130212070e1902030106091a19030e0d0e0907032403060203160813 63
    0x700c82ca09640c13040f4552984150002c5548607642c10b10030019000100076084d20303101c1d2100c484000700e04004841803450082c0003000c42459000030403281e401340c0003071600914018030100c00c0240482c0403d2414502c54003804121000c03900303035550300740148803d0303070442d014000c2b1900d01400c2400c09505940598900402c1280c00116031f4046003050080680d00300b0000e00303660103054940944c1140d1040040841c2c02c60a115000c07083c00203002958901c030304094000d6600a58800c140890b000f080742005036009040c040114600101c02c1c42010701a0070540000703442414800342c0201c440c0f07500c0283c014420310401c018001540c0111009085a19050f4a101a8010001980700300c0c0621004502030200031191908019010f4001c880c03204041d0044440110365418119980800811442e13009000c040128000c14801d402400401502101d00300c2d0b0b007080407030510303401c500c164800d40d2150fa011060003051445c0030780b00f60b8212030500e0166903c0c103041c0c1c84c0c800f0810810b2030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 725062500 1250 725061250 725061257
    0x311061c0e0619022517070602031501050910050a0c0b010807140a08060112081b101104050d0b060a08030d091b1d090708190b010914011503060b0a05070606050619 72
    0x64110400070a042d210303001041c110a40c1f0740740c610354a07146000c1d4106031030345420b00003507d100c90f049501c101c00752196500000c0114802d0480708a0503a0280d2003061900c041000b42265040400e0480d48101c2c020078004e401000b407145001034900305d4034010204548218010a41004810744c0003440505403140054041c50502c40d615000f071451081034130200c01368100103201a0410400b00780a1a803200842c1c0500c5110350317410303040800f0b01c29030103010742c0a500c4002000c0400c08085034140c0c841c1d40035000c1c0b1403094541112902d55013101c0000b100c4540c031707804024200700d002c1e92401c101c04507884240901500f012118140040d8540242c400201f40d4400507071400002c10100d00100b00c150283c400d0b2007001001a01c40307211541c1c0136192401c0d041c00002d04541c40748600001010420b102e00707440e90801075400700e0804402174040401d0f440b500081182c3c52200002c12488000ea00e0307a55071201c0914104c4107841d15940814070840043c2b00c03601e48078018044204240300300c1d01c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 725063750 1250 725062500 725062567
    0x1407050a03090c170d0206221b0816050405070c0b04050a020a14030609070501020c1009090f0b040f0b011d0111030703050304031106010311061c0e061902 68
    0x40c000c6004058002c4080c245611503180000e504d02010600406005140305460854254900981ea40c40003030303464900318117881882615400b041200d045040c2d1144241100c2000c07056200781d0a004207400c244101c1e080321071841000d40014005100412003940c1c18065807a000c200a4192152504098407482d003000002c1d040040c02d004030702c6000d5005105040042e281c5150701c4640c40b00b801d8490003441201c0224181c9900029040c1c05c55030144e004000080d8a5400d1141000780d8600440910400960101f20f40607a0f01410070440140d0750001582401d84080100faa10402180c000c0d141c941820848070740d03030161082030003d001183c0c00c0607030348020300100ca001002461010081c040440c00b4001c041e070100056010301e0007a911050813002680241d51584000c0c4001850090303190800348a07030030300d080076090b80440c0c4500781d0303a02c2003000400b50039100800381c0808960040e130704100c04d14207001c0805560302c0390048210705244c03500c403012043c1d14008446810005001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 725065000 1250 725063750 725063767
    0x240402100e030a0c0510030207110d020316060c03030b090f061c060908090102151303080406020408030c070501030606140d0e19030207151707140415090e0109140705 73
    0x495481c60345050140803200100e0302418403a01d0560b00b40240b604c03801c42e03071071502140e5201e40281c03a02c50b90414004122003020308208906003644640490700341c02084e0b08915000388031000040200702c15150034410f40450700c0d00404440310074460920510801c01404070389150f403949580c0c00002900c0c8558078450074400000001c8000303200614090a02d035840e01003120040107404000f41c00c0e000c882d14110050892400d1a00c1110b0200404241e1a07440e40130034480c48040d0b41003402500014a410386400c0b14038110383c0300705000569544a14401c00165a140c41210010a241d03d0110064540009601a540b01c2c09080d26034640e212503460b120028103204a07021040700d58050031110a05140c00784d210303982403040e00380903a0008902c0040c030b80961a080207008110150884594680710107803800c03240c29404281d2008140700c01714110f5541d01003034154004c1501e4814105191040c0c250048405800c1000f165042075078400d50541d81042064000344d07142000c0340c0f101d0f0003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 725066250 1250 725065000 725065007
    0x6080604110d2c030708030a09060f0e06070809011a0105090604051c050c03070b1902120d090b010f260c0406030c0801051b19050912010e24040210 65
    0x180c85040000a00c3c000c02d040280700002010307022400011140403003208842d0940c0d4490003034107005000d40b40d007000082c0d04080d00b9070100c00503510402d000105004c0200d03c0004480d4803103800c8800d58410814000040d8001e07102ca9840030103580203011070029051040c00d0b804540d02c50a0601c000401e0f004825516a002c2d500506400b80c0380b19162803c08903004508103603407500303980394052810301d1411402c2c00700341030042d9614001d0052502e44100142182040203440d0441180242c41e080c1c1c0820301e180b4000c040450001c4004124815a41420f00c0c4002040c0c1c4031240600c40700d402000541420900d40a03005c00f201d008445c826a004140ca040210f10f3304003a40c042c0c94141c000c0b04101d02e00c4c1c2210182c0348000c008001d56a2029003c0280940800c403040c000101804021100122a00c5450200e1961324041c0c1c104810320003c203040150410f030000199450724036441d0788203800c000700b034805180c0504100d10720320b000f400c10484040241c0003074003e4000d040076087c81c0b4003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 725067500 1250 725066250 725066257
    0x17060f0111120a0e1903030206071101021218070501030501050a090213410112020a020f030c0d1106070507080a1e0f0207050f060315010e03060703240608060411 71
    0x956919543c051141c001000b041c0600038051040e42c0d41c003058192012880c0012064035855001000c00c1d07225620282c41040c5580c191062641d001c0040704103440300925a0f5003e440c03c22500e902c000c2d468000e00c1d00300842a0000b90415160800400003607407100106402c5560750080140d4895003030000b911240c500d60801c28903c2103c100846031003220f4200146494215040c1032060000092684c41071004000814001002e00c50541105212540103003880405401151000c100c00c080d024215041400300c004640c00007040c090345907070450034020040640c4406801b03140b0348050013404502401801510308200494045801e03400b400441c40c2c44074410746884a600d44001008065081240448006000b42c003030000c2d043c28100340725508190004c01d1103040d5502c0200314106d201191000b00d040040c0c00300320880d1501c0501c01d0174007074555950082900285149622240a2543e44808250380d04e5182041915132041c403294005004442c003103002031050848440c07600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 725068750 1250 725067500 725067523
    0x203030c07051504030e0103060b030c030a1e0609140903030402011d0a18020d1a03100b0402070b040c030c050613030615170102040501020105060a03081e07050114040317060f0111 79
    0x15150044c0024184c2241c400414000244d03810b0258a4581078002c00501055503041001c5e4420700110303d888240d0b030442c441950719410071514001d403001d03003502075500c1c40d40324503c01d81d51140c115509000c4c0d007c1d4143c0c010201c01c0110701d50306096000801040c1107080d0051690300702407a582059940b04001e44c011304049100408119000c00040000d40c4100120000a490006401b1000c40384104401079404000c0140c200040001001e03406801540c00c401d80c016400c124160003c1e0001d960580901d0090ba95209802c0c150300e0101e00305a4a500201c0c1316070418011684801180220301090b40d40c003107404680610309040c140000303030150704a580b00041d01c10003249030060540c060401c80708240e000303000c00d03103426042c0560405036000c0541328010400148100105100d2a903c0442035070140514014158480d01e007140e11082c0030f1300c41181c11009120505911452580c5041c68940c82642c00c0e00702a0001030708c040e5030581413414814160600d406e0740409010705c2070180c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 725070000 1250 725068750 725068783
    0x3020304180603150f1404020a0501050d180c030201020d020606240903010e0c04060b0913020906040906090504030324050f01030209091e130b0109050c040803210c0a0203030c0705 79
    0x186440d4132900a0321031103888018051501c402e0013120306014045900a640140c1041c0c4420b003003100449140e8056103034805a1a10b80102e440d5040804070300c054990300070ba0b010500d40c1e095100086c18541c2c0b6002800866004d0414802c41d540e0b4078407a8030341102c0c440d11403200c0014091001c000e41c05006d100d203134154604038040140c4000480c8840400b00125020000c440c0c45e001c290700d5500a120300240c001540110142c0480040e40c0281081d10000f403240d801c042d1746016103025a403141c0c11408081d501d8805000415401d4040c02c2005010011101699524034031075016541c21407007068070520550b015808540d01990485103540c0018012007081d203043c400794012400c0d07144034089452010300000344406800c202030342502e54010402602640b0b4000d40502030800a0042054450100300c005a416010002481806e400340e158803110012060b94500e100f500810203096054108140041242c0c04011a544035001e4a42940c03030343d1250400e24038100807108514410b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 725071250 1250 725070000 725070023
    0x7050412112101050606040605071416060f0206240108060402130b04151b12090b071b1e030f14060c0d050709030b01380c0708060403020304180603 65
    0x40300c107460b4169820800c802440f2a444190520500b40b1603886140b000400922038080090261a8103034402c05126003111105402c1490604107002d4075401200030404816034491074580500c100d80e448103c048030010f2a840300d1140b982c59014051402d8100982840080c00a660760381c1a201010300e5400803c0c500d50b00d5007010a40c40d03006004222826060028252075907104e4000309240302401075099103146d0f482d40c2ca0701a000d59090700c1d01c040c0440f14801141d000c603103201408045000310806540109808802109400603820940baa2000078560181e0000000d1780a0100c03540040500c5019032142000502c00d44201c1010450307000c1c0c0700c14080607502d0b5102500b40716400d440c0c20089500c64841c00d9404601502c402405000e03100010004404086c2d0326009080080c0c0f45441e1491380910002580207103a08441e454510101d03084414a1003001984041e0001e00001e0a403424140c13000780d84d034043e9208820300c0344203c801c80444005141c10983c0210f502c00742c0345a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 725072500 1250 725071250 725071279
    0x803030901020703020f0102090d0b0c09030316031b02010504061101020d150f2301110c0307030c1a0705060a0902012006041e0b160224100e0705041211 67
    0x2c3c0d031120320140c00500c202400c6203046803040c0300301c0310f513803c004040300484a015030f80d10b080c20200804400e02c0070410700c03d8031005c0d1402e00003000d01d9201c126034952600602c0c64003601800071200e00320041d45025207481c006036084011142690f0850070907511001031002c8550180c030506c0400100d183c1040b03c4250301141844844094654002024800648400108810505108030b8046d14510310010100c0365006e403440400180e14130301612000b540031404689040c41d16881103e45004040c2c04105041c0c2c040041075602914003c01890140d058540c01d9a030300d0040c180000d1030f56118510303001c684c0901000c0c000446080030420070b460a4440c407603180c5004071025100b0040e51000b00803020b074030308030300341d0703000e07401164659183c079401c2e007246030b4181c0041c2c82003c2d44280b00004195041c020704620b40070500e14042c1d44589010845440b14141e16030150350350710541d005109a0319000003d880644c1c00000c10300300405024140b100081081e207410b10b8110340345015140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 725073750 1250 725072500 725072503
    0xe0301061a0711010804200a030f0f0201020705030d1e020f0d020f0c12100b0103060513060315050126120409090606050a0819050a1e0c09050c070201081008030309 72
    0x2001d83e010b0460540c440803800c0054550b1081102c0040c0f40844807110110344062144682d00b8100020300708510580c1c0b20780d11100c180820300c006881c2800c0801c046421507034100300000103460150b010300385141d51120098941545040e1004001c0d405100c42c99109100300b08075014204608d007268900081c0340006900c500300080032480b54040d001103040c3c2400c042d403e00c52a0f2400c44000c0c10310900d148108170050030ba00183d14105070711030100140035500d99072424a02901444e000403090320350310307040c80f0403411008588001810600104100d18240703402a1111044000b0705040c0020020000d081c44a0b80ca040010b07100046804980755955500001c40c0500c103000402000392550b0401c15280403d1141d0b031080da21240100d82024842c1070100318880c400c00072650008010b03643d8034003641010f0428200b010300f0704030340c0092003140010040101406141000365003801c2d00390f041c1c2842082000b0703060180c10008210310180103441d41c0c00030000300c0c1c1034130b8480c1030102030300303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 725075000 1250 725073750 725073757
    0x31c090306020c0f03190305090706090b091f0504060806090f0612100609050105030c0307180f060314150114030304050f270a2d091e110907020307050d0e0301061a 72
    0x1b40c1c0028a04800982403803c0001c0e2041550b910f503c1d012682464440340b0b05841c1d01c02e4012039002140c1c04818201e640707420021403c2d80741c0f00c1c0c5803180c13200d080c802d000b81000c000038015449903411000740040410101c601541140701071f01e05203480d0b44210102460090b0040503074502500c2d02e04002004001544200d0681340100e0039115420020010565204958014600e02220364240f407800d080030b96020394254120780102044076a0b580d00c44880d10070202c40410030340d400000400528450800b07009002d080414010081c18103264042a6039005078003078140200702c803a54800c0c490b959a0b07031109907550003c201c06011001c0c3d11b0640c000e21401d032043c0c0610fa0410854041840c0c0f030000d09000c403010116440400070a800202c1c001e0700511505070b0703800320f107030202d130010b0703003d485041c1c15a03406a692083c41900820174040441001819481103400905c40f00c400288045500c1001450710310f0150fa10301503400c0003e00503c020361140545040e5076144159034480d64014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 725076250 1250 725075000 725075047
    0x51b07050d030605011d10020a2114160b0a021b01090611160213110a0806030c010305010b090d150603140124032010030209031c090306020c0f03 64
    0x10f00c602c96a4200540300c0c198581252400315044698015a5041411a0000403003481c811200a540c03241c40d04a00100910302c5072030b84100c401ca19450854000d88204e202c1485060118a4a0420b0080d0744003603072204c034020301c40351070000451746101081c0c054070b918103829074031481c005080030001b40c02400104800ca80441c2040802a01521200103680510b0380c00702c0400041c9480303900700000c903008002c400550655590f41c001c01c1152460190001480300e03100c0100394103119003014500161551481c7c10507080c0401070200c0321001c0c081e00d01c0d004094403240b09607003191504440100c0125041143d20b45040d6001050000d011443d048100e4404001c0014040502c0f01d11514031201112202080043c9400c10021302003048030291005814a800d10385000c8400091401d0107016240000a402040501e51072034184038501c010320000c4a294400040200c01030120340e828403024142c00d6010a07200c14541d002d200c8210030001d9401525659821660111306644c00c0010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 725077500 1250 725076250 725076257
    0x319080f010f23120102030106170606071a04020f041803031a22150f030203060a14060613050d0b1008011404060b010c050708011b1e03051b07050d 65
    0x1400c00b000c45810010354103045051081c4420032003032200700801104400e80c00400b86514440d12203000c1c03000d540640f400c0d0395070b200d40890040036a07503140d602500d40f40c4540410030243c800500d21540b4200c2c1641250084a02030383c0350700008110140120903640c105d401c0032450f98000e407451f140c0b015030031702c251420013289940152910001c10280400c541200c080855048484070410000f2600c0c08001800f0507011404004000d1705a00d44d170104a486c07503045824011407609009165200b07013041820801040e0300c070014451084054a0f080c090000056492403640c030200c1e41c013001d84009420908003200903e0400f20b00d46044603814880e0410300b001041c0d00134180550410351440d8072007001d281e03d03903848000c02481070030f45103414064410742c807400148040c00424002d1035100e000044202410309803210280360014070383c0400411000514002c000b91046000010084c03800213030960322000c050320490720300c0003400a5020081189802c0100016403019120030941d0f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 725078750 1250 725077500 725077531
    0xc030105011514070804050409022d0117070f1110050c03040317040f08090a15080a181505100b070c1814040204090606150503060306010509060306010611031908 71
    0x180c02d14500d0013070820017040040c08120070005460b150700404a401c0c0010301d512002e06820b07070741d20305c8105034480c0300300ca42d14410004d0a40350b801a10400f030313030002c054101d00149080500103104841034100c06040c4034114a00c0082c1110801921a000380f08500810080c2004c3c071000605410807201100020040e4a4184002c000070702080c0c01268401c24000c4401020398502010707411a0300c03440e421200d02e180000f0003e05150040c644207030300c0d03241e410700d034140b8002cac00c0c003030760a00c044882e4030300c1102c0710101c0081ca032000180e0120a00c1d10001806071078042d041520f24099900c41075140070041b13003a10500c00b001c1c50100489d20030070400004018403080741e01c20384061005c0003061100d00703030005001d810141c0005076128896100000c0b481d441d4034142100c8050f148010000603004410080c0718202084282e01510f13003140c0701003451401f1000a9503441050054004102204040da03084000800580354138040516005c11400340d2103800421440044903800580c00009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 725080000 1250 725078750 725078777
    0x1d0706170a060308030a1808030f07090e06060a030b190b0c06070801060f0e0a210203060112080f0c010905070923091b06090405040507030b070e1c03020c0301050115 73
    0x5210b14011a80e00070740b13031420f59460141c44801081801c5121030711103002400e0340f000444100c02144140700c2d08850820301d0901c041c00800c0d00d1201d820172002c00780c80700140600d0740d9600c4140d425100d414500800c40c0070000b07000c00c00200955056880b4034050f20f80c041180c817000b00c060f180712f034040011140c517681c0b055012162800c003032055001040403e0164940c451164048924013840501051103690b900c003584060f0381c00002c1d111041122502d02081103180034001240145400c2e10a0844440241c4030002a4414144515600400003414001050081d009500b4094210080e215000d99859500303024002801d4589400c03000c000860520814400e02140150803210003400490501203810758601500e2100950000c2c05021000c641d686034000c261013248100d0281140718a10b04c0c180d107001d28054902800d000724014101119200c1d072401d610080040a100a407101240c20182c0c20301420b44040c94040d400c0000110b00400c0c248100d200101e010303a1a00003a1495 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 725081250 1250 725080000 725080021
    0x60c0304020a050d0305071b06030e010b0a1e0b160b0702010c080604050c0405360118021602030109030e0f01020c010c080d0e160f05090103050a02041d070617 70
    0x1200e000354401039054007480142005400380c03008911a040c207a1400e0b413592562224119083d41c02440510324070000d11001b585400390300108940700d00203002141142000941101ca64002c00c00715040824440c01400300100b41d800080c8209a140c5588108241303820400000129042e62480414400b00f01107078414810700b025036265a4981c07100d42c07108001c1001070038000d45107070f03041c00c6d081c0004200d81d51038120140b0030703044070350017440303d9001003e01211034070000550b0010240140c00400600b41070840311100b2800b80c44e030040c0d46200c050001c00565154140107509580383c00018400c160b00000a80044a8201d800c1d1102c8449600126610140316140500280c0030720400780000c3d2540015198130302c0401000318039581030400700f502c0c210b40040202424032072031504100c6180d03194100e801800c010380e00341400b0340c15034076650354586403944024002c82d540d2190a0b203000301054150710203030013081564a03180d40e507200140042081a410502c40101d4004150450030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 725082500 1250 725081250 725081257
    0x7141c03050d36060b0301110301030215190c050102070804060c02030c060a020a350a080601091a0c01090206180f0607030903140a08071a0a062306090a17060c 70
    0x1c1e42c03030903c500030180c040f803450b188550603800c0303500c1d54503040608602d80c0c0a004070301c10322884603840750700c961450040000c1980d080821001005c01001041180c24144407030180c02490f50818064205a074940303140284291500503101c25000315000c42c50507030240514140e075000302c044802004920003000281e12440c1113410150b030006854500050369041762503c8020800074209214241e521403104000d1803060b03039041954001003062800340c22a851580002d420329000c41d4041c1009140c0d2100748215602051004012039807130f001c1b0000350440403410f9805070031a07465007091081840314541010740c41c1c1c461009241310b06441c0c04c0030800e407120581c240d540d0407078071455501c900e11036500c00030000c1028096180308101281c403420082c0b0000b03125645882d10042a03003d0707100a020040c0450310340c2030810700e04200f2914600d9132501007800b12400c946006599400250340c03403080890703040d0440781e01a40010311002c061b281000c16181f03002682d200e6914214865498032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 725083750 1250 725082500 725082551
    0x2210907120203030c03041205060112050d0311390111162d020915031b0613080705010e09090a0f020409020d0b0106020c100207141c03050d 62
    0x50000208011506259a10801d00d9001400b038901c0c20b1121140310b81160310907000580311402c0b41c902c90b420071a082107000c1c018052495244030781c240d266541500d40d030022a110003016120000109001c00040403207002a0044d40c0c2541544030041c64541c02d903041e80c924201e044498803684050480c10300480d04030503100d8001519001c04100b00780007007519002c0a6605103c2c02c00320450300b5042214a6082c106404443c82c440d208a01c1000344c1100d000380841c1081aa002d102070294600084245d195540b03000f05114240d042d1010806034001c18250103543d040c640030000305410049604015a40c0aa07602c1d41030321000302c2032115441050b2601440ca500c20080c143c0442e540500441039184002d1020072016101d8000a98500c510002130350115030b040c00400001c0e4040040d200c41d1042650710009c4888500e001a4490243e88a0003424101da0020b0a450740d03101022000041c0c001ca00c84554030510382401401a08400f54591100385401404104807800101c2200d145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 725085000 1250 725083750 725083753
    0x8150303030c130b0f0309011125033501080102040f0e04060b0607141c0c060b060f07030908010c030207020a181512030806040905060f07020708030409022109 70
    0x6441d000c0054a05500150045018503079407500420000696801045c00d202c0e1000070b15124104489802e084030110f1407007801407841002241c02034060304a2010201000840046c8030140609080e103400c070720341c12072951100c80b02490303030381c0c2c14564084581d03290803130500d03180983c0e00c51740c40134207e21540c0203460f04580c05440c2000050805440700341d00a00c154004a070042c5101c0110f40c071908032a1085482500107110206800420010561000741c803010501e924a408000031348a450440d0020384003645800c0654500d4654000719038405114944c0141d031100ca500740105402180c0c0145410365090400c01d002d024441e0003a40d03021760300104554115442c05c0d225140d00c1608032002010f054072003070500780c4a0070400a50f00148001864045642d041d458020590140140f80510540c80c2c040c1c190041800042c0050b0310010391003d42d0400d0f112440c0070781c03034921a64006d840070300c030008001c104104103030040c00d4183c00d000724501043c2140c90303800e59410030448013246203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 725086250 1250 725085000 725085007
    0x703230907170f030406050c010e0706090b07030c050a03030509151006120b0301060e19020304050a030305070c050106140916020c01180f0801200a050a03052d01050108150303 77
    0x1d220240c82c4a185490103085074203070207a80c2405410758005602070070100784003191030100c501c000e0060781ca50780e4120307001e1310905041c884081e03c2c908490144200d222000700d402c1e4101030103911214501c94101e800c0f94401f5010713190060150100f02c03030913481800749441d2441040c407100020303405403a00824a6590900b44181141c00e1986051050039080c1c0300c0000e01c0064400388502030180001103c00501447c3c1020490032501064172084807581c410000c01c030200f0004980d400c013081d454a00458580c07115042111061020000682075520b411070000f008505c40b40d000c9030105080d139a182c40c60303880c10040c00700c0c0b4164140080150308840c4d107050071b41d88120b1342c158100103a05000c404094640c401d0069491954104241d10382d5038082c810041c6103602d2012204544041200380b6081007c0c500070524025044a42c0a054460002c02c0032071900c2a2001b07203d111603107030044940300310003200c00350344020300c92540402d0f00070010564200e4034a00c2141d03400c4014004518 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 725087500 1250 725086250 725086259
    0x21050c030d2c06030406051b040b090f0d02090c0d0b09040f020906060c03120603010b03070b0403030e0a0306050405010c0810050d08030a0207050f3d090c0503060703230907 76
    0x34030a0688080400100b400c002d9039950b44120141d0700445c02070000161a00d05a424440c0c00300b0102c6075000340d0441032108115030a6194101c507000c20742516070121100217079001c1a403801d014030380203500082c80000c1040704401c00b00036009000c40c0750000c0c05010885418000041c1c020b035070181107101020300f05405410305240c510382140c00501940c0c5020303140900603085411620007038a100c1140d00504c07556241c02d0040c41140b15003100a8125a031a00012400358402c2e44402030030b11401c1022015607030f075010060001150482c10602c56482c00b468000d000300a0704c0c041201051156000c6858000042c02100030f84c0d002403d40150071200e900c0707081003908000c1c0003440341c603020000b490028609000d9401240100700003850b00600203941c440d0744d102401503540c0103040000d0920a6030388041409641c115010b08001084e01c52410440000842608034035010700c108824004000d61580c40b0740a4114603584541122a401c040000d2404042e1040050360b44002800d01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 725088750 1250 725087500 725087537
    0xd0b04061d1003051c082203080702010e1902101d120a2909030c150406140c03180303090705100c0b01030803010510030209220621050c030d 62
    0x2038008000d001d65400b016501c0c0e50355454000c0e801604150704081004100c500c9410105039038210a9002c800c42014000341c400c203009000e012000b8040040d000086080c45000390b200d4810041c4942c04d84004000b4003c03020b006030355081089004034a2400c207407030300e240310705a800540700118004174200480b0701d0811040c01c1b9a03290500c076600481740f003100000d49002155107040c2c0050b9901c3c00d4201e906085c0007034000001e00c0290250010040d06072a50303008625003030301404004002d141c5460380c4c10308000824400c80c003071503510007507000d1080907201c00c400765114100703d9101c03080407002c59106940380d0205582c80c11980e400310b0381c180100e1034040c0c0480e0303035446907140454132641c4603101c0402801c0280d0007035569020003c018460341c00e20300901040da042d00d00f001c0d8030b007290078804103048080c84600200d0700701d105103c016103407010760800401040c034001d5240c1c18101c00c0c41001c5510802020854a070f114040603a2802d05003c12210140c41060320350980b400d100c41e4410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 725090000 1250 725088750 725088809
    0x213030f2102190822030b0a110310052101051f0501051c050c091003050108060c18010c230331033225050a0b070c0909080d0b0406 58
    0x181594000c0034050185c83c0b0b82458120045000d454141841d080014094080b00d90301071510034009000c0042045a45144803c101203441c2a5001c50b240d00d4840c2d40c0b2480f20288099074445942002d00340a01c0d54000302c60b22020300f499410f5010200d03911801500d6038891404c0855038407910001c4400b4002055202a52003030a04101c0303880c00c0c2401002491400400c11108d001c60340d02e00c018000901d003001030a5000c48040e2015180c010380007900c80c1102d0801c2000c5040006218403c002c010700ca2031240b840384140c09600100720015504551240c210b003054002030305a00050300d500071020032105200e40c0c2c40381da89694880c20358a411080d03814a0407400b80f42c0035500d0030441e0030300b081072052091030506000350000209000100b84040416a509001882c020034144916507034210200c04407020440e0701a61000540341417045144940c1c42100b04034a406c80700400d00513440001c0c40c0b40c0503400380c100f041aa20500300011140903020321807035074098250308200e034500e03001807 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 725091250 1250 725090000 725090017
    0x5070915021e070302030a0302031305060708072913112b0515010b0403030e0f0a05010f020c180403020f0106080705040b01110a030909060b120a0213030f21021908 72
    0xf41c981040c0c898000c41c1c902121080101c0c016440001d502006001c2c28445c840a49002c4907500d2401a180c0c4850034140203400c00070381921b0001c2c004040b190785025900d11340e41101941311001c1d24004e1022110044490000d44801064021005051514209032402c3c0410030901c1140004600c0c1a403000041811048520f4031800110802001c005041c5c14004d0500c3c2c500309a0b90350941c600103203210400706990780180f1040d8110074007550344210281c1591028600401908030840081b0301d040d89800000342c100000c14001d20390100000d4104d445540a03400300e03800c2c200707490a114201c52241c03003811101d4008075818085440c042c0c000641c0c60b01305141c01050f02d80122052410300610310320450100b46020020030002c8800d02030000140210020a0304003a440d083c0301c0c074896402082d00710712960004860364140170030a8488040e50f00b2000d003140704403851074000d05c070f070341e241f01c0e03928400040d0040b541800781700040d007a4071400990303184078031010181d03100e401e0b60700003810 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 725092500 1250 725091250 725091253
    0xc0d060e100504020d140307150615020a020904110a09051003050f0a0b070819050907090c0509090a110403151e050103110108090715170a050f0f0a06030204020d05070915021e 77
    0x1230580070404000c100640d04804410000380b0324503051142c102d280a0100101c25500301004039000b41e030701d0758481648140c01c00c445107081d2a600001034032540b5250003018441e450300080c44020b25995000d401074070b00c01c03c02c44110078203806040c1c0c0c1c0e80f500c2881c0201161840c0d00040e640ba4451078110340c02092010403450f510650302d140c0010307100102e80746141c1e58400c0008000d076914034007038481c501d0000c0c109645024050f00201e1601000103008450003601c807460303045551203810895000355001040307840303410107901003003016060707041000000301100d000030724035038250b8070030f250480342d2040314041e0303044400005554042c3c1c01000790f0103600071145d0020b0060892810031130300300c07190740e246a0301d018401c11031200480007800e160601440c280c200440c5400000c100c5030482c440344000f51544d5034505140300980b1458100139003007400172800b522000303060307004240990115200d9100f465103030b00e11104000a10140c1e0801640243c90442c09044000e01110000d9030300350 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 725093750 1250 725092500 725092507
    0x503160e180106030c0e3a050a031229010e19060e01020f15010b0f07050709050a0e06150f031e0a050d020a0c06110c0d060e100504020d1403 62
    0x40488074482001d03400440400d44420540500399803060201c22036540840c0c4600a882641014410005181860388213104c0010402203410540502c03808a80d0341c400c2c102c03900c002c418a4007c007203a8001e421480c4050614590420341c1c0c5040560003005a4109100420351004d54011900d5803128a26136411100c00400368540c0c00d17680d1000e030083c105036200c000c000d443c5c81000a00d400c2508842c2d160a4000b01343e1031a00e43c0c00c0e1107026044130444c061954a40b120f62991600d9481041401421449581000103030140e01750021840344003118010000c0c80c0d0409003864039000e0032901c03006d140fa5030019a056915140d0b5001da41303050003600319180c0c2c43c020840c1403a51710440800c3d6029510001d00d440810404214452040d40244081c0016241c0c0781c1da01666074125000715000e00c521400c140c40251010041c845100900914640c1e015402c0d040450003000b15510100050080200e81114284940070300c500503a4080e05011410032079440c1c54042e04c00e228a40c15440c0400c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 725095000 1250 725093750 725093779
    0xf071211041e0615110703170c030c010615030c0c0201020a02040e030403020301050c1b0706020304060c031707030615030207020d1202010603140d080714120705090a0f0e070503160e 80
    0x14030840000c1c1c0100100380c1c81070310182c40e01800707240842401c200c0c035034801b40f81880040c4505207c0b0350004150917509071100311a0700c10500b1801a032407159440d41c42c0810004140107260b5640c180c4000640b07042160100b1400c04032012416410b010f40540c0c4528040001814140d10810410f0baa0758160390510b40c5960009003914004d998000c0301c0c14010801403c000d07041d42d203103d000c0d0032480040102625009020f51240035910611003407003803c560001c1814060710b00f810740300348580c468043c50f03e031218ac09401020b0307900882002840984040003024004d108940d9a160001c201c4103c07036100d0b68a40c400c0b841d4808030407045540301c0d02c0010001f514600c2d17101300d46010304064905041409401040800e00400e54410803014410200b0010b155000311054400a251844240c1d42c88420030340751031060711500c3e6000b42404e207002840f501c100c984c10782550003582c211641a1110303501101c050009032001d26003d2181c810342c4600500901c181c910f181c070090300150040192 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 725096250 1250 725095000 725095061
    0x118080706051b0309010c031b0c180606020c0d06021605060103030c1b0b0d0b010c02030d0309050105010f05210a020a180c02010509031801090302030105090f07121104 74
    0x441d84800302065001c2030100d450085151080c9200b0304010045040801d4080000d050b20031044000e0b0501141c854400c440d2000c1070080c4442540106c02c1440c025580c804d0480181300164010031038618010001c42e0403071001c0350741102c00c9001004a4034045160b04e03610025848804404107441d9015002400608240121303402076000307880b109820440d50405d039460541c10210b104611800c9038080c404039131038030117445040c500060001090084d41005131054414460081d6051141155900c0e01d103a054001c420060300c910b00900c11a40d0700c4909169210f1240a85544070035505105810203c0e4003907100c0750000e020088490040303ca801040800c072643d005011002c040c24503c0c2c4010300580242c1d00303011414402045146044180e550312401992300200e12034050000154150707100328045005144c0040003000340341040c11101c0e175186e007aa0341070360030f07405038810014202001c240d080359100d030800441d881d1141c100342000000c1c0038401039440c5112200d1a010a001d08 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 725097500 1250 725096250 725096263
    0xb0a021606020708070e011802370909140426030c07170304021f020c031c0206010b070b0106081314010b0102060a021c0c03021624020f09011808 64
    0x29a600900843c6040c40316040c14861a03400801c126400d40740100f080c03030921f600e8640e400140100c010788030500440c00c1c4020b0f1115000714445050003626000b10003802042c4c60a4003151512810b0100d681c0c0c42c122402c5d240011034403418218481c1c00640440c4131072120503001760500303404070103405500e9010b002c4c0303030000c0e5083d41400c1c002240704010091a40c41c408607030b007107100895003189400d50001d810300295195650804900e102402003140c000c1000c254400c200030143d074000403c034205101c0320881c180020006108901c00014407048443c120f40f410b40e00300310400001d82c24404140c038100310250042040c05031070520000450350b4080d1140200ac100030010407402500c1c0002850300e038000d011460300e244108022002c0307080303000e89018002c65055000c124038179100003d40081c01489014032000600c00f8081d0100010402d006c07070f06440c5041070b0441c0d00e0600d1740ca04100d018a40140b10003450400641c1e0040d801640e98208e031f81e128441858420382c54200342401d010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 725098750 1250 725097500 725097509
    0x50703050a080d1406030606210a03050304020411031603020711060a050711040b06120c070602070b1605030f180a05120c010b0f0d030c060f020304081207030b03070b0a0216 76
    0x841c00300000380080c040d000440031070000001c001e00300f205c0003a07180c5601030075040c410f0740c008191002e0086548502642130305001e060728545411400d025055600c01c613000c034841c9141103044605c001441060b40d014882d90141c5200d007034441ca00650007540104001e0720740410040c0003050a945042c001c180c41e01c60f540e10b240c1ca540d0586070010065000800c1c1c2e501c40c41c2002c0d00c02500d500c401d0240d070b080d001940c100c0195034580c002d125039140f08034007001d40554000204a02030010542e40113018003d000c00c196003030201c100d03048030f06010558090ba10311003401c002c50a4513201e00780d1404104c000005a940d69946070740e445203030080c0481c040f50481c4002c00d924503090303000e114150f04004280c40803414021380100003612007000c64001028442d039a4803501c180801e075030000d10f00d0452200304668034200343c01c0c60307400c1c2e0b0000900840410381110015201d0780c424090907040803070280040c03001c28141070411441d80c0004d543c020451060100c10b00d11000000007580062 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 725100000 1250 725098750 725098763
    0x4181e09060b01080411150405150c0607020a0b150f18070207050315040803100f06050403121704080d1e0515010f093605071112040e04050703050a 65
    0x2940e1031604000b61400740c00414184468203041202142000e241e245601d03004440ca41611040c00d0303d0900907000f503400058001400c90200002415204010100c200f10b141c211401070380e804c1c004998500d131074003004202085040100307c0103240c516504000200c02044c0004001418010072501d12009100e00e90f000404414081c0058043c085030014100590103044200c0e100900c40c568010060001400c00e100000000c0c1c1d081d0502040304007402c0c00d400f00a14083d074401e00204950090b00041e2144421005054001d9020348419a41803070700c151681c0c25a0ba448d240c0189603040703c3c2c10b007851a1f40314032900c1c170340c03074001118046510010b10b0001028100300d040390850b400380ca4a030a05106500c451f100e400b0b504500751a0446030b0101040c0001c0180010145c0c6a0b400301c45900300c009030001000445c2190b0342c05c41c5126151a90321146a0182c05c0b4500307985032441750f0280c21103c07003040144021100402c6459019000310105e408641d620f07550285408564801600e40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 725101250 1250 725100000 725100011
    0x40803090409030e130501090e01140c0a140408070e0f06010c0609320606030c010215070903060903050c12091003110909010f030b060d03090b091f02010905190804181e 74
    0x83c08c403d210f002c6004100000070000944501da81c20040403000d8810f00511101261040c0c07264031640890b1800528400b0036520380b548c031010265034070180e01034010031030780800006a44a528014440c841d0005a503800d004076210749a0758001d05480c50140c0d0080800c030358498149458082a03040d0000d2000380d890107400c0750f0007190610fa800b4000510a030025101c4a002d03030303070019685542d01350420070134007103032601901920108811fa000408050030012210140b541050191a54040c050180c0381e80c6070310740105600300e204902d601c5920603010380e55032503402d220350310000d0b1003c0ca032076809103800d03800b1001a2489400341d21600003248650011303c10402002251504040240d680000b2103d0a40c2c0c05451803800d4041d01100c4c403004542025541e64445c1082c14030004424441c082100c1610001d000e8201214140c0f6148071b850061a94a205c001000c03c6254215021034201414154203000c0d405410040881b81522402d9040c081075010004c0c002d091410240010f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 725102500 1250 725101250 725101259
    0x7090504060b0306010504050603090a0f030f08070e0105030a15090207080a140414090403031b081602031e0c07080102041d090606030a08220821040803090409030e130501 75
    0x36501e0a8102e8121541c00307005009a9076048030550342a204119079003512590792044140c0342100c91500a07261008025442d401d050b040041015030000c16a20101213580d01c80c4181c0306a40841c0700940014000c00c00110140d81a5109565401d0413042d405c001654070307000d40007a42c11850040c1c924040020781004210741240c1e00c285e04804140e000d038281403400400d65030318041c2960b614000c01c426000502054800e60044001d02c038601322241406810b16002811441e04491150121203031100c40760025000000340c5805080b10000c5c4103442840003000002a002000c81c12070030f21491401088021702070020700045c003c1740450703c2d000303000d000a43c2550000500503031413542240b0103100c00340d2808584c2d81d0405030420702d00e0f581c84484414000108000010b188101c0d0109000403e0517100803640301c0030030062016682186030a05d2141034144180e00c00c40074583d004102008050806800c0345408500038200b89401065010200368100c03060a003203c40f0640d51030046c031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 725103750 1250 725102500 725102509
    0x4050303010f0e04080711040605041404061d0a020f0118090b0319031715060a030509010f06050a1403031215100201061805060f0a0e0f16050403060f14070905 70
    0x1c0c003c0502501c841168245511500e6051151070b1024001c040400d0b035000d071070340307894100c90000c2002810801100c8805000d00056540c19503040b11030906002c0410940c0010f5030407498001d8054015102c00c0480e5401c001e0140008050700341401000703c1180e40b00030060070110024040d400002c2840302030b20040608003150032401040060103000c42001181d071142c0351f21002c0d240044507405540700d00c0c0201d41208002c0003410380c032220000c0c85020055143c3c1007240280000070003400001d100300444c1d410303141907010341364110565100800007040c141d00603c220200180541e458981c5504104064200445c2e01760109000c0c02944603003410280b460b00d101c01746a10007041803504001c902d4040e000b403084603400c015210000f142041d0f403400701110070650014031207180e6079075031a8180128201214211950744010700051500c0c44802281c07862030403030381d071550302d094110340d2010003e188600080c2e260035507949504002c5c40c940c05507035003e40202e0b200da0403064901070400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 725105000 1250 725103750 725103779
    0x304050d08011d0601090302120a03080618070c060b0a0626010f12140a030c03090801020a080604090f20040e011107060c022401051206092d060405030301 68
    0x404200001c40104010201a14a9540f04101501070710301030b11108012144003080d6000603610a00850019400d0f17500020404072084c0b09440b491200d5544c501004040d03040a58040d1654030150001001c0318030562880c0000380c82003400185661002c000f0840104054110b44085015803012070200002c400300c0b5108514212041c401c2903042045484841d44148285105032204203101010000310400300c07458022030008982c4070107150705000340712081802c0182c0c0820b10140c07002c5100101802240d28408060712152955221131041c0001007030400c0c001c1e01c424091348084400156000e6004528514108803d039140b5100741c100001c03680e5403240404139030b140001020854046c0000d850711280c116100040000703184205909003042042c800e020f8071a42c02c0044034040c00c510312507058841c265121421010005140b5980302003e0b680300480b58440e5a801c043c2c3c4400502030456080403040b2840001d002c0302c0d03458981a815a4102c80503080440144544001c100e80e8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 725106250 1250 725105000 725105023
    0x904060b03040c090507110307050c0406080706081609030501140906090106050102070b0708130b0a030c090b031812040e190506130c1704050115050405071d0406050303030c030405 79
    0x22500d941016554507010300602d110701c0444c65103e1001480c06801441203650000808084d655544e055144c00350300c4580d4221403d1003280341040c0424080400540a0300b550303482c0c0c9400807561030783d02c8a07141c00042c0402d00c0c01004071102c004000244280203844e0244001d460107040303810200e907040c0c2021801080307108560700d084004c105903a80010704008482d00c1c01c3c1c00643e10030003410444a507200380000729034401e840c950005041150440100708001440c2c0d03040000c032120500c02c4844801612940107210000d1000c100d581c0d8081d154120b45003543d2003211944511342c2c0715800242c01a0b400503404450600402c5080c1402c07201c001400301c0119010000d0b440d0030300000d1141102108920100e965034080202c03110f0196110300400c403a480e00140952070703d450140d029204401e0f0314210f5550f5458000b50a0600f0b000349c0740100300d682c481c1d11407801001c44050310f00d8001041c1301d40c01900c0e02c80005150702e00f80700441c0280003030102540e0b03a15050818500d0072850921 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 725107500 1250 725106250 725106269
    0x1f1502060609063a0b0403090f0609050108060a03021e040f02040b0f0310080601032a050f010e06090607140f03070506070f0216060305090c12070e10090f02090406 72
    0x3c21a45a8640d01a10102c1e0b01d242d8122200c520b66450001580140044030850003d0615a0038140810b000442d48030781d1003075494131a145e49500100080c07032418031521003c2281e0001c1072042c1c1d07003d031040d19030200025140c1d080b0300d07580390000340b0340942c481045026400f04092404050a05008003108035000c02419454585820071451040c4200280f80a90350300120205d006a06181c180e50010f00f83c550444a46585030700700007226005d0700109182e0101d6050000d549219a03d03034460031100001c0050341804280f0006580d80c1200d81c0700c16500190410000d0780c82d5640d40c024004003070007128070f1542505000d401c00e1500131403610b440e01950080c8a018002100001e2a070b41c0b02d01c00303241441010303034039180a80c0351480c02ca201d102e0880350214041a4140d140d4482403148020b40700721800120342400b8030114891030306404502d600075180c02d101c105034140e0003507004800380c104070000e142e5890188041300c4219180c282c1035070300000d103214145031074010b0b107015100c242c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 725108750 1250 725107500 725107519
    0x4090c05040e0c0a0915080a0f05061806030f0f0a030f0c0b0c070c08030a0e100f0207030609080913090b07051c0504050708160906080f070e1f15020606 67
    0x1401002c15481c001c08140c40501c00283c04140301d407140b2843d900500300c00c0c07402c44002a01c21005454920125025028145001c032401942d40b02070045d94020039018040c00380540c0201000000d0202c0100090b401d0300c50164010b82524040140440800b1007801511030f040c800d02d0000d01c912401c0b5262010050a6080040800d07151031803282c005218041441d9a45040e1926034511072096002d6442d5000c041a4000741c5ea400c003401141d00350040303c003c0035041e107801041ea00000b0381c401000060740912028800980d0135402000c00701d000303a40c0903040010541c005500c40c540e141840c406c980e185c94a400410661790441d0350800d80c1c0d41042810000b10b40e000c003c40b51513103884400e4198444000c90b0500c8824002000039083c0c0e0400c1e00c2800640f240400240c40c1c1c18499030180514111b40058120408100303042c40e070888001821106140c030310b052160702c1c00900440410005044045032000d0201d607410010302c04a0019080c020809801030b0400d00e000303200d28001d0b0001e4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 725110000 1250 725108750 725108759
    0x30f12011707260a020d081c0509070608090307051e0f03031303050a0c0b1f050d1707031107180c08151009091104051201090213051905040804090c0504 67
    0x80743d1240054640050420568a0001d8000d241c2001d000e40a900111400304800034031082e08001c1c04001c0044a40070408151b450b100341c2114021140c0d68041d030000c0c0c0091060743d10030f50322550411521800c4a0500070151262414481803c1c103549111400741c41000c801003040c4009150800110040c41c11031400340d410098651014000030200000011140c40403401480c140050719040181d68210386080742d000c00c503480e11030300130f0003000d29103410000e4146014800c21114903803080501c43c00c0e58032026402143d820500084040c46201c40003581c20440400049000302002d111209104183c28030500c1115580c841741800c003c44501002800400c20a542c3c6e82044152400b5041400440048941c01d0403a00b11f81201070420244014502000d8060000e0b60320032a0002c1880c0f4604501a003203c05424000790881c4400c40805942e03036003a40540ea00c480d8120b080c0c041d0b040c20411100407140100c40403200518045410300903100148034080340300242d0705080345080e041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 725111250 1250 725110000 725110019
    0x201120c09030b0a1b030501260c011b051009031b03090302210a0c03140318041104121202010b0303040b0d181b050108060607111002030f12011707 65
    0x42c0405018800140041440011540d1020014000400d8440650001c01000501a00082c440c446030880405403080916600c0c55400120307090003c000d0105580020040d14070304011142c5011f10000c3d140f90b4004200c09100042c070a0010a5000404801070b183c040e103840f83d000d03501b070800e010b150012000260017200110980e41c040354041c008001205030340c0c0c00150780d5075035035116003c0d05d10420108140ea0f91013000b0780340b06010500310340b081c00d1101592400707031681038052110411205042d40c28264003a410410000b0182031806490b00f8000f4188c4d51485801c9a581203120525080142d081c4100140b0f40000c070081c518003803801810340b1090144074040c0310788a0390b42d440140c00051030960807028a500c040d24010310130074901002c0d548102440741901145410000641c14a070040449041c0c81d800807051900855401c02d01003001440e0782c41310150b1004001c0e01c0030503507007440940511040040329071082c0d030514090402030100c510360b14415501c401000e002a111 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 725112500 1250 725111250 725111267
    0xf17040201051605010b1c14030c0a080705100203131709010c0209060328063c09080d0b120c030303130809090f0114010f0203030c0706020f1201030201120c 69
    0x840e40e8a0b40b0f00c0380181406401400401c5035694800c4103081c0840d440c00200840c45000c074001c2c01c00c40410001d040f12903403640b003002d00d0402c0541028001000040501020301100c0c0c0c000da0864001690070f00da01812a403065070301c818442d840103126000c001c00851309800c221204d0700c086003425140000a0a40452600c00170321408208001032542c0d142003008525400300d1168115640c00783ca5002100f070b03282c994050301c0117800c10701c5182441e190f0081c000c401141c0d06210940c0c180c403126101e2270700342e0600a88130f803480d01c940100c03022410000142c00040306064002491b4502d4a04100b040c1c1c80b00081c8448581080000007055607001c8203403944180300d906d06040000080c0341c400c03038a1003400303481940300c4116428800700c80074408030b49060340d1511907410510b0741d5600041d41d60094504004005a20800c001040c024980c406411101d125101c0941018003095840246402a980b200300c60f4602c0341c01002590b0f88905180c0031281040b50404c1580521480141002c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 725113750 1250 725112500 725112517
    0x3160f05060d0f05041109010f03020a0b0c030903121804050606030615040e040606090501120b2205030403080a0314040b010302041d2b2d03090b04030f1704020105 72
    0x201d0201d2080c002107900e4228140c82801e00c8010811441d04c5d1408403009503800c0e40c0784e400307420441e0010846c444a10100740a90ba00144009402ca190a000c101540e100300c0246c034103400300f03000701c10007a10100484003002d0415005540c803060b40c0c3d840441d00c40c0000c90050310450400d0103101d0341e6200c90045980100068503465003034062000c1441186c8510740c4000780d40e00c1400208400e0081c0d80e4007801c26140c6429050110ba42c1e1100701d0205000c2d403c502501c410310740000306d0840c0000d181e08414210305e4042d15809449a40c40740c5055412507481a5641500010003400050b03042c86200c110840301d00c02c0380c10394105a03c03414060501400001d00603540e0b15030b5030340c02c0d510189400000c00442e00449850b188100507281500c8806400b42d00040d2902c120840e049018140b01d0004801202c159064200400c1d1f46074284e500302e100b910245903482c0000ca002c15804c9686a200b54000d0319224404400c0c014001c06002c0481c1c0080c10914001090000607070f0b0001c02c0700d4182c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 725115000 1250 725113750 725113759
    0xf0f07020c2d0604090501031e150f060f0303020f01050c040602151b0412060e01051501211104082406010c140105011205010b040204030f08130315020903160f05 71
    0x780081c1d4610021080b0320300c5260781c000c1c8081800901d040301a0007482c1624424001680106591080d00604840d40d6800400080072600a2030001c10305900480e4403802200000c030b4501d50340c10003800c6080844c2c0082e001070304011b06c00c0700f07140400d018050300440480d6000b4601803030000000d484078064110b4086c0030003110081480034520251149a052100c2c02e280c2e550dc3c3c1d03441788080d00412000c41281c90314142207043d04041d034184565071250200d9485000840e00540044a01803541984d61440084140c0c020003030103e04c1c0700e00798044031003410726640e40d400c00c26040c0c5000613040c609c400d0103030500c1c2031007a6500311011150708404203003000b181c0f513041450555000002107400440544c0780600010301c3c2c1d0041b40201050314003842c0208052841c2d9014031050f8822400050201010041e00c4400502c0d6080204105400303c5681303107030035860740c0e1003c3c2030410016048000c0e0b90046140c0c5110702e814490a81040303d8507001015161074118035160000891248503c03a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 725116250 1250 725115000 725115049
    0x130e070917030c030406050403050c030601180e0a0821130f03051614030d0c030905060402210d0206040308060916050319020c0102220f14060c060f0f07020c 69
    0xd070381e000c0041d944a500400103903070700c4a442e40001859031f00030703200603256841000f0407081d8505003ca80e842c183c5d102d103c0310b00701075459a15007401400384683d048007a4480d1440d06030114180e5005016091000103050840341c1d1040036000040c5e80c042c08080c840c00e08080795000244548038000c000680c507007412503c42e01801400140e081095102504800305880c0f5001100c5000c0700811070503c42a004201101c0f00b50001c80031203041050090540e07000d000454054944010300000c6000d294061045042c96203041a0600f1350b114100740143c0c2c45001800105504000d1050307009405942c00d807050714241c504003107641c060031a40d90510400101245600035101e0404007585c8915200b9035407a801036028a0003503000d2092000060011049600c4c0f24002c3d00e40c031030440d05c040309003018960400540f00c82803102c02800c2d03540001d00f0090b02003039000500100b44200d1020211145510f424503580c1e400900080c000011900540c241180b90b0b0340c3c0c0308000888001550030541c6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 725117500 1250 725116250 725116289
    0x3160504123003090501050a06080307062c0c090601080405030a0305040c090e031216080f0c1314041a0109170a062f1312110a080102130e0709 63
    0x11900c01000b0307504100a05403000480c42d505a081580340f42c2c030840081090755074810a131400c85916000d07000301504100010340204180d60040815540c000321089a08040c104410760000c0d4102c24003c00c2d078000200ea060300b07240c9204041c0d403001003802c0c000c2079403405a440783e0302c1e48125402c050916035110301040c14050310200c440007410601c0b5040100300d2039540881c1e40c0c1d40000048030808000c40c000515005440b0100400082c125141c030341c155118003848004140c1c000341322031902c1714184010301c0200c1f14201400010300d4084015070303a5400b00130078441036405c000d10f00f6600518010746400f099038000c80d40000c8404400e08006944481c8002a05090300604041c05690030101000d250998141c203480d03102617580e016000703a48400b10b041c003103402104c03140e454403544c0c5a810000707208484540f0821501c15201580140284000250742d403519030021403040c3c0d80895400f004020007500d01000c1c0c02140412088c6103801c06000b0a0155140104c40d141d40244400c1034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 725118750 1250 725117500 725117543
    0x31202070503030a122703050307050d151806080c060717130501020d080f15012c0a08030423190e060a091415010c02150316050412 58
    0x541801019669070350440d940080005445280481721541b1700142d0048a010010300b00c0c0d41c6a030303190303035a4001c2d1032a6101a24150801000d5106014041180c8400d0541503c28055980c40806140d030712181800c5509560003580d01560300e40d5450301000303001081c40043c1202c41d84104981e016524021440c0411541c1005010b0308a000008990040050320305103650041c3d5001303908581050280d070100b00d4a144003a24600c0c040b10302e0741c001c5402e01c0441e460802e44100181090a90080245003641502c1c1e45c00450b00801031210301034100e01e180c5215030303000511080d80210b0605003010a0003031071501c40f403160440c1249208003003031161101112010b80b852302c14041c02865903152029080e100045a8480c4240400580810507030518031a40014281d074600308000c42d03442c9100002505460081103040c05030707094080c00146c2c0d5082c2a20a0440711012440d100d041c103160003800191494071003000c1c450140404d00c0b0b1402103001c02a000e903000030856801448911b0381e007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 725120000 1250 725118750 725118763
    0x90302090a020d0608060103060b030a15050403110a05070806010501020309091302180a060518010e1303051b01090c080d080f13020409030e1305011a0c012705011a0109031202 77
    0x3d182072240c0003070031803808540b060480e801407a060001149140802d5120300300340340700030480da03887c1e110b0207000302ea00c0c0d00c20341d4058402d09001140c03030740c0e50103518584040c4040465aa52041c101403042c00e030306010741070041c082070006604059503980042c03108403004060110f0030700c804c819801599580b81800500300c180c0c900000540c2020b4598002400ea070f0701401e80035801d19030541c1c401155880c1824101d58202040c4c80c5580c80d09141c507101c076844020203030208002848020a408004110921084810000080c2c0b40c002440d0401d13807404070341e01002031500546c441c2c40c00700b40c01610440d40003401043c0c408803607444d200103200a045404020f0341291030541d030001010f800c00784140b41000100d0b01e8500307148407410751a0640f44240250351a01e4040c4661850610311100540f89000d400000410400c4101d18088000e0701054509940c103171951041c4814003a00703126264149d950000300d00b8400e60081d001070b01c170718560b20006110544420040602030b1081c00344 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 725121250 1250 725120000 725120017
    0x7111c1d0a03050d020d180501050d091b050108090304081e10050a05010509060a2706170610090b0f0f0d0f030521090d08180f01020d060510090302090a02 68
    0x101125600c03401d20f10b58441018010342d01501c0741140080300039025141902d0030380300d0000050f59a1341444011075098000640d100d115130344035412940028000c3d0303c0800040c640301c2c90140e4844c0350000051095201814105140d0402c100502c14608041518200c044c039071422001d000c41090810303850f004611083c16040c41c81e00043c010101c441d030f08914102c81044803182c0e01a1640010000c42d415244114004104010b00d1845070100d0455203445218244200103040c56981d01600e40e00000c00e480070381c5e180c00501c20801041980d5500d64050030004508028a4025202040c0a610400412071003070381e520000400684e0740c038080b00401c07907200189070520035003464003602d25000f140404113a02181ca080200d0100380e9440c1d87d2040c0729080092480303421445003501c40c00030141c00c0c01207250412044464646081081440000070440010b9550640c690980101c0d4100e421151140031100018142c2541c40b00418040d01d404443e20780c002d07101d81c0504002403158164 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 725122500 1250 725121250 725121259
    0x90801020403050318040e1b1206040f17070c120804030515090c19121b0b030a270b0c1314041107030507080c0c1807111c1d 55
    0x340401000303c04006040300c243c070210300201c008035a40410040d206d298100d90721a60103401480111580001200e0102401400c081d0f48195000078050503e001102e00388c80411a00c05410108240603005581c07010344018002e080820075620540400c40c0342c816841001124001841405840400c680003035a0040032610810070341d0503005240f90045032006194003800c0b40d40c0301c45050403054200d00c2c0804031801885181404940c003000141184107840c40c141a64617420302d800f02d80012000b4184000915859140070280c141c2a25400f054000c444010f8001000400d031410000242d40360744078141c0c00b5143d5400c00c40403c40d024480404141070310402c40001d0050740c4461040034454155818004030004071030015280c442c401000700040c404100103004103620384054900c2100400584a64a0201d000680251001020400480d40c82400d002040342c10504031200351040701d002c1c0106800c62401e410140d040f2003107440600c6070302080d02034101d44101d18205103580040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 725123750 1250 725122500 725122507
    0xf140c060304121101021c02030c0d0c180f141c021f020636070302040504201e010f021c0201290319020616060507020118050c040b0109080102 63
    0x3c2a09552540c502114086483c103000c21071102418003c8418000500d2060300c40e40f80322441c0e500080d4001030500151030313000e00c0708002501050003580010f10f450303580c1494400000c034a20360740c00c540b0307405204640d003801010000729882c8580300c2c000d00c10445002081c00c109110302444205000c80003548110340a100c6440c0e1045603100c030201400c903608407101a55150003609424911601e414400040800c40344200c51044041211406541d429166201d5407a4040b40654a05960444001a851032103240c203170071103019240c0c4940c1c101c6d42840c0540403600d44547d00a0f055101030704218a0005100b040c9000b04100c50290f913010090350106121804002c1c000c2500718158900781407642030900003c001450154040300005001e4031806105803900500c540c403514040340c00c242d050000f056110380109035800410f0184502080324034125270021b0844840b0313240a00030206085010000c0303000004c0d481409082a00c002450340b0640700141c5162440350301c084607660001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 725125000 1250 725123750 725123753
    0x30613090804080d0207030b1b0c01181401090210052209020909011e30060c090f03030905131e020c0c060403020603070819020c210301030f140c060304 67
    0x200700b01d42185041e1030000c944c035401261503886510000e4a00c00701640410040c900004000302448801c05200c1c0c41c1c041208203090175500162920030003d06540c0c100c000340507120000941414a4070003c0281d0b4a0a60009003007050020420041150101d11240044110350b421000c401d54125078641d01a41d0b03142c00d201135800700700d0444c002d181500c0000340c420404203550082540750341d1403070f100d5420540310b2100410b02590782443e2410007807400c104d40d0954401005124010640415140030f0f070640036003086441d50012205140481040011941c002419029134000b180c256494a0b580800c0002030f041e112184100001240d074480000d501d141c4c010451040b050b02950804521041000798500507484041e400c84810000640708030302c81d071002d90344562204a02140010710303510043c101d801c0061010500d40c4443d03010401071910181844441c010140c100d40303190304507a1540001d1000300c030024156409202c0d88448540b0602c848004410003400c001c1d00c038a0076 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 725126250 1250 725125000 725125013
    0xb1c0b040f0515120a03030e07091b02010e0c0109030809030f0d1805061c09060603050613030915090e191503110306060306240604170f010209090c03061309 69
    0xd40e0780300d40f20000c000c0101e200342041d03004107615101e407801801c1358000c0354405030040e003052001011580604040032940c00594400d4115507000c508100d20058204540a821103401c40d80c1001c0340e6000310100b103856a40f18204009032548030302c0351a114040c40000c80d00c1c010b0016228079041c0601c242c0810180d07403011085590120b03518491203041e0b0380c0c00034040b840c89600780b1030034200312680b0398801e0f0300401d820a1041520403200042c0700350341c98071503030304000c1c09441c2c510540400300c01071002d055004c1038010151030302c0b00c3d1f9441c201c000d941001c0c222a0407842050100d54281c40000c01425154001a0300e91200300014000e100079100100c4141030a800701300d4240c64038a00381d081034180010803911641b4040d0090105031954055641c440c024074441c0b9007002000141c6110b1784c1c403600c2c041d100803c03c514400c0862103070506180d040202540890725183e206001483c0195146175500e0b4100c100d280c005a07880d102c51011821a0480050040403241031180840c1045176 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 725127500 1250 725126250 725126261
    0x616050403210f0e100c11100816260403090b070f140307150203220b01050f03060403020a0602090402090301020c060a060605070f0602210a1a0a0b1c0b040f 69
    0x71280e64480c0001d0f00d40740142c1d8a840c07200d80d2030350051604108501300c1d03401441500000c9015200400b00500010000b51100403c22400b4001501003001d21003100320180b100194002c990034221f088101400050034140c40c00b109007200d40c11220003040c185402545944041c0a0194106503215542d0801d910801d278482000c0f41c98083c01050443c19100120954240035406200b803012131100109040280d00080c146110b0b4112070b0700081041c080007208820340c107101392034000007585001c041060071600401818000e8010204100000f0b0b4003084a041980e404080181c603558650003240003409030565450b0150700c00900020341400001d1402c0c410718007040f0034040340781c884404940a0060303000003031440e5000100310b00051641e401078181a06003549065804001c540151b400300815512801e510340e41d10794400c041c5103540d4410004001c1a030b40c2d2061a882d010160035070340f11300300340c10140111404150300d454042e6080070301c0c03020005006001c81d181d0500807100400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 725128750 1250 725127500 725127563
    0x316030308160503190608010606170603010207080d09030e090103030518120c0f0f041107030f0c0b0a05090f0d0512060301060302030309061602090106031b0804050616050403 77
    0x901c01c000040c0300071044046150082d80c0366503550300750f445022042005050750b41c441e0551a031655400702e4801c0c400d00c00d041c000c00c003a0352400d44980303450707418103400000903103441d001764010004480442e8046040750001013000d4400a1640c56a050807541e00c100002d0503540514140000801c2c15801009082c0030023000100078448080300c0b0802180c504042e242182d00d400801d00c80c0b940346003100b240c03009910003405a841003500c50000404a40103000400308604010481e0b0040c107503c15211038500025003003400e081c02036522180704100d0001c107101241610342c80014803945013031250001c0c07002113004680300c01c2c200c440003030001d400c403041d801300341603000001408902d0140110011260090061454105418140074240e0700a4540c1d078840023441901d01c0050710b58860300b40c003c00c495607000420034070a60011070018600d06280701044114018071021410115295400c02c0c10b0a561070000440380384180c60702d0041d0740c0098404014031072100044e444204a945012 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 725130000 1250 725128750 725128757
    0x20f030712050103112e0302120c03011a09040f0507090812030105060a0e060705030c0c0f04150501050913020d06030506010e150f040212040609140f0c04051503160303 74
    0x548508050858400b4400688a1682416640d000d400d00c45100c10011b00900c00c0304c841d025901c0045009404520b0710f44000a900003445000b040108555682000a05088514651500d0590180b084510001c400b407190009003800c0550b030303035621965110381c6019081c03140349413008014020204902c02c010603402450042c001682203101240d0603070714000c00711402d0000c2060b04176004d21400c04025008a410003444000c01d0080024200b050f8a080040c4400915030040c8490100c18450a034003a5052126000c448140700c00010191003003031806030780340c240340b0000846c101001007010700f032035100060034120100c0580100091f80d010b03204550107a6038990036003500e444100c80208888040c43d9000045182c1040e58115998000b8805420151259091000803c046d5021108140d981c00c02c20304000c000600d00f050608040d014080341002c0704c503400c2d140c860821026203d650b42e080040c9110040c017980800d00300e030140841d000d0b402d0750055550101d20a0101380d020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 725131250 1250 725130000 725130017
    0x50a090e1510091d152809020c03091002010605061206030f160e0403140d02180a050a0522060807081002180f040905011b120606050301180e01020f0307 67
    0x20980506004400c80741c40306900044003918904040c2071104c058611880c0807080c0c0107088035641d074000c404060b1500004003501c03040d030307003030480f03900511035030101001c00c1c014003040103e80030101c01d440307c882003a07902c42000c00304800100d00500890b007005501800200b09011070354511085148640c0c1c05504a682841d20710100590300c4925000140c103d4a01c1642400460300c4003c80d00e400c24464204141c410060007030b101c0d4103030405500100215404134030010340b15554592018041c8003a5800c605050410010a08922141c090f640c052000c0c05102941a1030710507007203030018120b003c01c01c4039503250b042481e100d104510400c0950700c68104008528517807032080302e000700c130301c40b6030040d084101c04140b00140c0340017062180d02607510b0780c1140200d03000307010300009560802c001e559100c1c0346840103006400300f0240d013030780c651074142d042c40801e070041c0c226815210545807103101701180c188014081c14110480240950003c41c0880354918040040c502414464541500c2c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 725132500 1250 725131250 725131279
    0x114100818101a030a0b060d080c0a080309160f1a0403060c02030c2103040b070c02090a1e020705070605220b0301060801050613090b06040f0b04030b0115020d050a090e15 75
    0x25180c0c5c8609014101d0565140410540d19000c807150b0a0302d40316081032030070b0002c04258107051018040080da10340e0030000401030011001d000340d02d15071860705a1340b0102c4d41440015034484016024000540742256062204158040180c400841d40800284002101e9880082d2290030500a01034648104400c030360809a600c2c0000040a940711919825552140c4030120543c0c405000c41092207000040caa02607110b07484010300c030341800e1501140c220001f245005402211810180c841032042c004000003070300100e8000f00b22180c904d01680c603030b03100403244070200c131070859403500c1c0e00140038000030a01d800d000954100c41054441d92039681e80c0c0d10911505205800d460501d0400400051103940f407517500128084001030200360420351141c030f900b000209283c000c18020040801d04008001460200030301420001034000c3c1050400140a0754074070138400100309001d004143c845000344501130800003000541b0a00500e403c00e10030082151840030f960713034010000020101c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 725133750 1250 725132500 725132503
    0x21212040b04060831170d0e12071a0c0417060709050409020d061104080102210a02131202041506030902100206160311070f1202060114100818101a03 66
    0x105c04003400c007003040c19041c110303c1e4290a811060360855007800c0304d0604e0006a00d03884040c06081c0f1441c0e0b000104450008881d030b140010604114204000c02c0006400151031f400041c0c4c4003aa080c030241c400c903183c90f5140109405650410350020b1141c110072030345c0c40e40000d540d0b0b00a5140d900d500400a8845e0203110030781f86580d030040e40001203244003100241555114030700801203801c9160900da03c6010741070136a400074107091200c05a40e12568411000c104620340c01101c0e541003149004e1f107441106a0020b464030403404001c2100c0011000e54880d500803180d00d1420700c200741035158803070b00090018200d2000c264007031040ba81043c0101400001c119004800da00e0f210000c84a00d9078040f0083c240306c0e65401d4038001d00380904000034191150403210f581c495450080746161108009240c420141e01c0010040f041c00d981d0f60082c0c503070001c040c1e000031452508802c00d40d42c070200c03110400b010501248083c412518025014030303096100288070301084040740012400f420406 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 725135000 1250 725133750 725133781
    0x3021c0807050714010b2d04060518090a020301020a032304031d031603030201290d1518050f010606110601090c02070b040f1703030f04021212040b040608 68
    0x40c0007007181001001c01041c0c000c004099503021800000c6010b09034480071544a0300d140380184900344448032800f04120407941f4140040e48151020031910b8940380c006420404200b107219001d024a0380412074010003809241101c9801800035540ca00380000001c004100d003103900041c101c001d514966141c0e0751162800d00075038159a4024060045044000c00c0300c014014140d03151085282107441d4285092091004600070b03000010301668041d0124220484503a1124207180c3c901410119985e410000c40802608908041011081c201e00d0b00c00503c881402170705007c0621380035004009002445d403c122004070006c0c0039055a401301130700e81d825440450070706600118014004615250301c4460160190b10480c2c584944c6c940080c0b4980d882508802075109001c44c00b44204030344107810302141e0b1a1800158078503d05800d010301c64540c0540000d200b10165502007900560800190076180440d108881d69941c0d29620880c20354014403403000810101000110742c3c034007007003070b1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 725136250 1250 725135000 725135011
    0x70e0d050d1103040e0412020f070315050c0d02031003020f06122e081011120a0509032104020913080d2a0f030f060b07110607080703021c08 62
    0x203207a40c49a44409a071102c2254184030700d02d00c402e1200103100c40450018a01443c02520328103034031520310714001d0800c0c44003480c803101a0f12240c020000112151362111034803403410303800210354441180102c41c920420035141c00d51800442408035030350080d08410100ca10071100760f03814040328800c0c860280102001d46001d8600c11000880c0c003080151505003282c0120070391071404a10040780750810051380c000d101240d014100700940200c0b03c0c46100302c0307011011501800e0221050025005000003000100703024bc031440403801e180e4042003991603460742555020842c00035180100e002c450304079400e81c401c078844804681309462101c2040da80541001806250102025100c0050a40c454a1060641010580d59080344240b03007110070b40160395440d201c0e10407081000605441c0398054107030030a481c10b0b404100d103104400c2103524641e4845a02c202404014000070321f240a400b8014141c103100041460030141e001c1400c0000c2031080c510f02544039030b02c51048a115408595 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 725137500 1250 725136250 725136253
    0xa0618090618052706100801020322030921030909020a050a081305010c11100e0303070c0804090504060204050307170d08041b0e0709080a0c060302030402150f03070e0d05 75
    0x75044022958014030343c080894880084c01c02030005920101070901d44081c025074001000b400649245080d89200411900c4025415030800da0100b04080c000e40c101092100200e50811040500452800c401080400400c101140d14a0200c00c5201110141180043d1841002155058140c401d450116881f075441c141420f0354031a0584016102510107546c480c5003100f02000180b003406a1101d0940365920320b64640c11145600e0320b003181184d549180c103030601d81c0d6850003040000640c0c0d1b0000c51032800e103540440c6130400300154231503034203c5001a8105010481802810340041c02141c100342c00b00c0d030350385039110122280c5000c0d80b0805035040e000040b00405c803501c2a0350981e0000d00506401800e4115020100a14110307070b03002c10303802507a02080040b46600304000f070008100ca5006001340c904d50341d907500078070040d500858050550201c081020b64032204812520001780055580d0b442016002c0c400d000e8000301d03014030024091070a000b00c1820301d1121141030a80c48030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 725138750 1250 725137500 725137529
    0xc11060103080307211a01022b110f07080c100c030c06060b0c060f1e0f180604050c030706030911040b061c0509010c0203072604050a06180906 63
    0x41c2c80205990020303045000308481d440c010307a415180e21404100c0300501a00008400b840c1c20383c0c1e40050312640903d18159001020000e407a90320514030802da082092840c202d001100d6441618403403004101c909240c401c2a20150000a0008811b82560800400c44441030402800c0245031084042035000213100451918006809a40d5200d0118850704012426a4550b100c41c1e466410039040d41e101c0c1d60116040c4220b60101303624260f0411642022580f54445140046400440140100b0710054598000032940313800e04000040c40202e240c04e50b20703181003500346142c0c0c4400d0170410500c64010710000144180c083d2240120075540104c40c04c05561803402040000d20403080803682050b81004400c00d0201140c400d0406041c0000c0b00007042d040200710b017821030700714540a0301554070402c070303000214540c1c0c2c8d200007281200c010280406040605140707054029640520342000b403020011903040d40141030741e51500d00c5102023a601c280c1d00c10301c0d08113840c00b5101d501d00e01c200c0074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 725140000 1250 725138750 725138753
    0x140409050706080703140a021b0102031e27030403171218120d0e151b180a0e090d02011b050a02150c12090303160e0f040f0f0c11060103 60
    0x18003980380d002406090020f4000f100b524404411b403021103480441c00da00248200c0424000b40a0b0104502c05ca0300850441c64802e220148501c4201820268840160009410402a000c4440c48109450350f9425203105c1c5207007440d540e40181c0400c0312065094500c030b00e1800b80c1c41058440400e45116150030fa07403070306545205c550713250240317000b914000c80e1080000d100e6050014603160302ca0850000d424800380d1034003810880190100030700b02e0381003c03e003d09010380d071a0359807614043c18502503861041c1c00f020380709064030100454210041e014005801c0380307140d002c2c502c50102981983c01820720801d04a003201c0003a04d405508100c00c41030b60484034810b0002e440c4010160044610034800440e0240c840c0c94101c0e610611007100203802e001d95101c1c4091943c02a50303c0008500398200303081201100e0241401c1901001142c49804100e81e41c0c203421100e50420280c005c00c06a4007500a44000d4524130028507825820542c0040e1000d20941a00c000f401410001d410141d080d07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 725141250 1250 725140000 725140007
    0xa020a06050d140108030d0e0105090a0b060a0330021c111005180706050a0519030f0e0d0809300c030c030c100605030d110f16140409050706 62
    0x46480c1c2c60302540d1001d0140405008540031400307418440e0041d5103c443e41401203003a40c8044030200ca05034180303010b1180d260300001e214181c00b07078404994a402da58000c045150348115610241c18007201001c8001800b0450000f00a240400909420b0300355039814183d9a407545c0882466450051780b07104c407015445041b01064400d00c0005942403450031010610a95205580344e41c02040981c00441400700c080007a08010221401c0007814100b020078041c000d4020003d12100c040540d001a0f079400303100391300620342e4818130300c0704000e07800c0460081c942e45e003d01c1100c140402c40c1400445c0317000c1c0000864a4507015009442ca4000b501001800c14000c21141c10081b000300600101c07565040034806400d554009000558844000c020550700e003401c0911118034441c9801c4040c03103151804600c00e0356520241c10800018000e02c0d28491a0005680144a00f0b01801220405100b031900381c1303c08882d0030001503801021002c1c100012a00e0008000b01180d02c0b0701401c2009600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 725142500 1250 725141250 725141257
    0x60a050607031817031902010b0901150210230f01080d1107030c06080907090510051c0c0f05030f06100608040302150a0509010c0e06180f03030a020a02030f0a020a0605 74
    0x2d1251048003103079442100c03d1180d144584c4250f0150008030301c4131072500610601c545500c200f440240040003181000c9103a0030418052020428901c81d54907503824020404e81003040200a0100301350ac170400781d0b880700003e41403440501200c1c45004101f1200754049183d050b960460040c202c905203603441903c100004205080b41c500880d1800004940c5600d80b0700000d0545482c1e46e1406c0c500704000c00c0c1014482d03005180901d1403e4103110184140c0c2700c060050392416a0304034203203d8140310313108c4108140c4500600c0f02100c2c1d040030611107903c0300312004a8005030112843c00b040509a545c58020483e0440340c00c5050350030800203144654205508240280190744901c84e240c655050346090456291025071313258814000d2004091089141c034003401c1c0b030070401d02806080014401e10800d0010010382c0ea000c0000c0149680b500300c000c0507450000c1c112660392004000c0030352101c440c25001e0b0302c64000c0c030f881113038080c4001c20004007080d402004d001d01b0a0401009550503007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 725143750 1250 725142500 725142527
    0x40c120911060706050403021014040308040303201b012f0d0911150a0f050a0302130f1e0b0f0d020f1803190809060a0c150501060305060a05060703 65
    0x200a0a081031502c401d801001c200d0302581001c00c25103001c0c24080e10b0803d000c400e203a40d15250604415083e078459568603001645490094070740e44990904a01500420455502c15880d01081207096041a03000740090791405406010292508003042c1c01c0b20303040e08541d1144071303181c40a60b0000d81e800201d1040400c170300c00d20905003c00e400904007102c0e80540103e500d0760150010041529210101009203070303e081c185490142c5d1103500030648030883c7c100009000340070502c070040a000360140caa120014182c0010785503900c0100b03508240c094819179541182501da901030410a0241d19000c2d1580340c80c0c11403403c0750340031107d1000d90001c116480c10a80c02d10442e0044400300c1d0081c408000130311000408181c03c0020541071003580c6503c00075407005410b50b0b0380040e0085095400850303040f40c245440d1010f1503005d5442000c802e00081560310b02070725124910202c0d0344128141c800c0350741c00301b00d6651008103000040c0e040703000303d80e40b09206110a0000910500c3d2502256 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 725145000 1250 725143750 725143763
    0xa02040207031404060e040f060305030a030e010b0d0b16092105030417060a0f0c0c0215040503070806162c040f022a0114041514010902040311040c1209 67
    0x120980d18103c01d140c0054020740c00280010700740e44128030305070040468580200d02c08011143c9181d5405076a442452200c1040c1600c6103d5a00c401d4800c0d40f00303520581c409070010481c440c4515051206001c00c40e014a6201c00348007084805034442e11054064964100c200f0402401115110301e0000c0d10b0a41280c00f880700300302c04140280c88460f07802d0b081245030020985d81c01c0c4480b02c2e00964400050300c244052038100c0d01c0c290103611541482c42c2c42d40644e2400800f0060900b034080b588150342060340c0500c2040000140400000384c02ca00c42d01da5400c10780340c101894041143e00d03000c080172416100d038407500c1c441e00c940e129161540300041d00800001d4912110391002c000d9030402038031aa1900c132001c42903401c410040c466080e680494100802000340a4548081561030182010f84000c03004101200040c840742d000803007008140c00c0346201e540e5206003050107540903000855450700b518107008034504042c004d0400c4c450550311003054268104900f000100718040059a04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 725146250 1250 725145000 725145017
    0x501050304150f0c081506030612010906090302070320150318010608070f0501030e060a110f0d051005061c0b0102070302040e0c09010f060801060c140105160809010209030a0204020703 81
    0x640030503c1100880880d84101140107607000802920944005041800f160040103c030740c03060340d5910880358410022100008044420080c01d401030516030300090113585400340603801d042d0001003945c1103030b00c00c1c01780c2e800c102105056808a88107a80100741c00c02161008011004030703983c082d55020341c18014030721901203020a042d094480e581d0256009802400c07050109a5034030b070845005c0c04086c03c040c401515030850a50f40c8003401030403e4079031a07803401c1c0c52007034403e80c8007142d034603a4241c0652038850109861000c000d21090b80e144107106045440040c55040ca0f07015240c1c0c1c2a4418404480c11152001180207451035018050450092000200059a45101c0c01e0b03250407554004100716170f1840e0a1003440300b01a0402c0d01d0010744480100042076010801c03a0540b0300c03a1030300842c182e00038545a991a4001c0c0100a0720394200803c0100d8540b5825a8000f028102e65600100d9240c08502c1c500b00d101d1000440c1e09500a211584058105500240011882032820720b08 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 725147500 1250 725146250 725146283
    0x40911031c0e0102010c120e03070b040605070e0907170c0d090303060801111c1e0207060c0e060c190f0501060e1b090d0201110703080c030a0306090e070501050304 72
    0x30180310a01c0c920810124032007900d0080d034007031880300c1d03181c1c000e0008110807013080c100902507ca042100000c601c3e110003100c52850f005100740c030040d85d8000ca0a00450809151140c080c020031200c00e4002045c00140c0000c0b4500303144201d002d1856529000522000d40b40003800245008000d416600020040c980001c0c0043c4948074429003c0d9800050403030508448909690031100701304003901d402e110b4140d03003035514007041214075590b00000130081d04481d50000000161100038402910100f5038200340016a000740c2a440c0c800e030340d07040e1a02804c20403c002030180100803180e90f40729412032020303200200d2810300307501c2c0141d0752445510030965610f070a49074650882e9286071404d40034441000c0901c604d901e501800300e410035007801c3c100404100030810403070020b4104018442c00642c3c00105011400155402c03a038016a9014100411940d0360b0140c60349100192402100041c2950f5500c15100300d05040e0014100103464a401140c00f03403c081c006031942091580c5200c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 725148750 1250 725147500 725147503
    0x40c0b0c01090209060d020109150c2f010314240a0303020a12050f091c0209040809011b0203100c022e050a0c09060f0903150b040e190204091103 64
    0x32040d0220002003a8240203205101429a002e010140a00100d841d0080140c0e005442442915010001c40d07201900160046030b40d070b05074940c09090121031884007008410a030980c002841c00c90350791441c2c0c80c100c0c0c2c0011800c40364140c034a60039070247c0c3c50224031044a29054480e03003607040802032812841410010340f404d807281c8d1080300542d001c121494100110500c10541d00141c42c248241800c2540304a060a803050707882403481984d84800c80c504d100d0024807e600303096006800c0c50340e24905440d00102c1d5a20444105d4003050b050014030122488031070101328009d90241c05420344800d0301e54000f01a0020400040035400b900740d282c402e000c0140195800807080100036901002c0400d051411580082c0125910074180b083e4840380a0300214520300303c2d01c15151603010840a21800c45a9440c0350b08002c0c0900e072079050102d512900c903005003085042c11101088615000e0782c0c4140c3d2451030300c442402c0b44400c07500d044090701c0c059100180450140c4802c0464040540010703 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 725150000 1250 725148750 725148757
    0x4020d12021608030901020d020a0309050d020111100b03010b030d170c04240e0a230a0b0d060810060509041103031605060f01050103051b1e07080c1203060603040b040c0b 75
    0x340c0390f9910100303001640d0340c0c0c10000000b00001600107008140c210307850041c00707400ca900586002c1c0508000d030100310b9210f522444585101803043d14601004403584901501d900c9907403902ca5802c090b10110ac1e0315002c82d402500300c1190b00c03983c4035010342d4101c0c0d00080790028503200006a092100054140c800301668028008170300c940308485209900107021600040c1d803090080e51040302c00c0c40346802c00089000c12400b42c41c0e81c510780d45441c00014100401d80d070803401941c5004500e112141d2169044070f02941c0648090390b843d000d0f0524050304070b50b90752141c1540255120b0200c0c4c0460300b4990408150b410180a4a03c0c091003007440008106d1103420440700703907205c0400c1240700c007240409103000d0202441c0038000ca00300945001c00741d004e00003461158250000b034042918a2134103101041070541e8445540710720590802c8845500030b101e0000c80e45c001c1001c0100090b0f01241128801c0d00c00500710303400d546032070b200d01c620242c0040085580a0043e035004c20440603c6014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 725151250 1250 725150000 725150009
    0xe163e03090402160515011202010516150b0a051009061209050307030c03031b140f0c0a14070f26030d050a1a030705130207021c030c0c0e04020d120216 67
    0x501401c90f45161041c60504595821360400d886c01005101d00140981161036140c0c09203071440c1c84111b00c0b91103014814410100070003010030b03410341402c185402d800010254200f180c2842c0325903a10018081e004518560754000181310203001d000a038018440c01c5080b02c8580d1000404403000d940701c42c80c6500002050340403980100b640d10801d41d250050b10446c3c020813442c03a48032a000300c8003404078102c80420355841c0780301081c0040d00750080c4050300c210031411030441d8200344007428003c0810450318002d4900e03020b0071a000c1001d1a40900030021240824480c41500170340382111040c5d801c0340c3c008440e0600080004025419050003028000e07100d0440010b920454420070001200c1a284043d0103600640001c0143d5940c0045162044030300002c09a520b50b404e02c00a1011440101001166000040e058051641c4500d2039240d0301d211f8610382c004291039100e2404865001c507402540581c2a500c40d500051080d040b005112442b0b0040380d401525200030034200e481590003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 725152500 1250 725151250 725151277
    0xc0e25021608070f095f0a0b091617040b1501080103050a0b0a09050618010c0c0201020622050703030f08100302030a060f0b1509090a0203010b040306150e163e03090402 74
    0xc1c46d0000c001d071080d403a085200c0000411890071600042410340000924000060561410031201076008044841100ca00010b60241c0d924040c505a43c40071400e6070b00d90001000c10000ca151540103404941c1a42c2e0088004c0c03200750419580c030740000b140103142d104060b0b1600841800603204010043c00394001c002c0c0b0b480101c1d21a0106d070300f100c0c0c02d80c2e64602004074030902d10002d44d0300800c10325000103100d50220700c071581c5071804080403c00c2c69801013051041030340c000245075001001c184900b50558401c0e40070707100c500d410041c0c0d80c00c60101a506070041000500020416804032040700171216010564032104000075407070403410181c0d440122400a6004000e1629070b00071a03001d450744a0450965040108030300d5507014600005100b640c3d1151800c1c0105c0c0c84004003c0140f041a104580760310f00001440c01c034191a1f1341140c0412070300d0084d0000001c4050040700c111030744400c40800560102d20743e142100401d40c40d080c0710701040005600036142c6000401c4002606c80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 725153750 1250 725152500 725152661
    0x91804051014190510120203070506190806030106060f2006012606090705240409020702040f0e0c040c11030301120c0e25021608070f09 60
    0x444903d0044040b0f1400e44085160100b08403010080c002d400090314a00c00301842ca40720548040392030a50250010f40e80400081000c0711841c29140c02c03a80070b180180d0394800710b5211581414240c80c458021200403800c0c009900c0782540c4500c0303e0082040c1100c4030156184084014941460313020b8200e00c0000e40000c110003030341c00500207000900d006000c0104140d10301480403986450850099a10a00b032070280d101c0304004c150010801011411200b941e19584c40100000075448014228003803414250503180510750352050192148050340581408407144041000070042c8041440500085010551035400204040d50103010041c003201d095802c04d061070f0700d001d03803198455200c440324001003013090002403c01d031a52508031492061010a0b401c0140d050545000c1951514070056400040c003104c000303010000c070b0b128400b04e2054035407290284015141d030759503184110101620b2f03407110541440c80700c840e0020142d003c42100c2001032422040142141e060781c00e04034801c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 725155000 1250 725153750 725153761
    0xa0204150207030c1a070b1003171201031119120b090f030f03041a0916080316080306010c0f0f0501110304051c1b05030d050c091804051014 62
    0x1488545645500e40010955145559603903030001c4401c0c0502e50600311464002d4098407020780c02d84c2c0d250390303003c42082e416140103100700000d84400d201c00d03a0784000d00e0003011813425411044851509003400c1c8001c1c0e0b81e080d62542e20086180e18a42c45e0004039111006251000052500d4050310516805441801080c1000d1010711405081ca158a81180c6034814070404000200c81900d80401d0001e5144d655506008031000500100e2400d0f1304600b10821849000101d04210300b00d54180c00c0d0a00c281d140c0300e01030b80da0700412200e1082c0410326031603040828481d2003e0341e0300850514207983e10318182d640711a0440034000d0100c90043c005d844907410094207015907108014a4001181545440d440700b503a0f8190a03d84603051900000038246102c1c0700d1148480c0b1200c079016007074101d024a141466903a80100c104d5600a440c01c1d0110700c0b5107104004546d0503c030010081c003907a070103400045e4180140984212210b2041c60200c1000740024000c64046107a51890318000345001d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 725156250 1250 725155000 725155019
    0x140a020a0218130b0c04051e040507030509030403032307030c060501050f0d1b030b010b0d1a030304050105030a060e15011e02061f1716170a030c03050d050a0204 71
    0x1001500d482c001002c1c04018849201e0085000b0716500311058030380381d456215400c015031060303400031500302c00c0004001c00c08188112100040003c180c40070459503031810000c40c200c0d4410744002c4034030b4008010400200e031080b0802526103285000001080400d40c8509807039610841084010613448054002448400e11803a4010401640c13100d81d041401400100d4403907603090000c0040c2c074050982c2407c401c2007070a000141d60301111100080d41c444036010f4141d0040750054000600b8501a9050640b85101c000da00000190045041c242001d005480d2604018030603c00690307a203100041c210741191441e0300a00001c0d0140701000c08020004000c4008485958407a1030002c51a4001941c0054603030b0340f00c01c42031402c400c00c041d41c10114091824650100c00303a4851540c00c0080a03402040194031403c0d8040c041c1d03845655110301c114541034040b42240d40e5045002c000012a001b08000f03880580b0a182142c54996501281022110281c40f41c0c3d10180c0d0104090050204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 725157500 1250 725156250 725156269
    0x9140403090f26030903010c02010203100f12020103020c120d0b04050a020319180f0606050102010509070f1a160506040203060c0423210105060f01080403051603140a020a02 76
    0x2c500c07590a07141c03414071140d1420716840c54480c500f0b0907001e034060385031524103000751180960018001d01c030420359410b00074017075001960071511101c0f200100140d00450f002c1e08800300e50407203550082c0602d142d001900250080700b11219140600c07890241405007800c020002038600440c00101c2c0d0401c0c01c207110484200802c924040c0c0c0c810402c1c00200b60440c4410251003218401c00300340c024884a803560b41d440710f480014801c042c42d40b0380904101c1e4a41000065032001c0e030081055590b04c0c0710540e031710300140c440d48002c000c440d0380c1441a11030241d29085959050100b40c0d280815512051100140c2a00251441d0304404140801c6107014843d17660800c24041c01e0504050410142d280224048000113003017011041050005440c2c00c0d00341013089040c003200f000e5003854840c0980c042c1001312013841c07082090b0760b41c009541d802003017881c0c061501035442908024602e92400c1034081c0d00b4406406020802200c040c506031070800900020f80c03140e000c2d150021003441031203905503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 725158750 1250 725157500 725157509
    0x10c0e040f093005090d020f06040f23010905060d09032a050c0102120405090a090b04050d03050a051905100b03010807050102070503010207240605030a0602030117010c0905010e0a0914040309 84
    0x140170031505c81c10760303150080e001c901501110260542c100404c0007807400d104641c0840011001a000025001008000400c00886040b4846000c140e0100119880403a40c050164424024044905800d0302903014400061003800c04076172401e40325061440425a02c00d0003010700b503901a81c00c007080014404485040028002040c11880b8101c0303200440c025409964081c0b00604d00241c10596903030803074001e65800100403032803800e2030309015889608003030041c00481d0a220100d03d44024134440c0301d00c602d140b414042000d8500da070141014010181402d0200845004040342c80d06448008500070315511004008180c074020001e41885099488544240d1048c801c8801080106041941c0402a4030114803da00c0407030410001b400c85400c610303010310031840703082e003001107540c0114103803036055017208000c10000c1007050a0344c0141403940b00240f1621402c100315401440d810805000081040c072003d91144525812a4101c2400301c80240003a403c2c8070501d0b400000356000340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 725160000 1250 725158750 725158757
    0x31101060807090c02030d060b1e040b070b070e0909030c0d020f03040b0903120a030506011b02310f0c11070b040b130305190212010c0e040f0930 64
    0xd4034140085490700024490001c80315141ca0f5462101e5100344102c4100b00340c0b001081020b180c440c20040c9043e003110f00c0a540303240c4442107545034140d8100c2920100ea11102e00e01d0f180400c00c0d51a80c10944014103090244000010840001c0e5076569a4600c40d00d200d6009503120101180e05500d00210800b021040d50880301c03a480407607102108640985080c0200c05030350b0402d08000c40d00c2e0082c0c0910300c003074010007c12400da81070b505400050141d0002d980e244c00303001ca0b6400d0f08441000c02e05000354041d0b200ca4250705400d8511480e08400c4688149428881c00101120f009442c8000c02c07240d889030362128240700a90f0460300841c181c201081c0103103001030900400891600c25030107810030701e60740410200c81c80301c0c4014680300916804401d91785003083c2400c10583c00340c00510100e10400c42a0b51a0400c140e0500c540285100544d4644810005e10424003000b8900003028003021900d40400f040820002006030703c4e031001803075230303a40d4002400100d04013000840a105040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 725161250 1250 725160000 725160011
    0x1206090c0403051b240d05061e1e040608150a0203270709091101020601060f0509090c070506090a0605060d021021050a06170c28030c12031101 63
    0x215200040c800016440101c0340802c1051410003e04818014558410f4051716401c594081400c0080078282072000c024040c48aa00c84104000744100742c0d40f40050179040c004a1101103283c0050005215106141c41d554200c1c2d400d004182591182e401a08455001001000e0140c4100c02080d601c50341b4200110300b5810203406c09441120300001d80e1018101d0000c0024040c0003c0c0000402013076524400c000c1c4003802e242881c0411940c0074840d000d8000c0c03030300014240c1e00414400c200e0b501159281890004810200031a0030400742c10301c48000c0c810320455002650400446002da4403640060201e0183d500e0440191180201400d014850440c03107a00140c490f407032070540320486424207543d0500303040c14a003001005166841e010500b801c06000b642c480d160b011a00740d0b50450f00403013030381d40400881a51000c2c40d1201940000e80812a01680c403046940328003191028240326150556a440e401d13072003d201d801c90300201c058020000c04250b0404a4003001c200d20500a011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 725162500 1250 725161250 725161253
    0x38270a08030c070501020906300108072102100215100b04030b0c1204030917060405031204030924030b0f010903080f0c061306200d090809061206090c0403 68
    0x40e02000d419206800390110f034810410800303405a81541d000a41415140c210b42551070020014410648446040074136140312180d81d42c810040c162800036005020343c0f45810100004d0307550f405440d591a24203080c0c11001a0b5411f50100032401d0198010100344032603009103c1c40302c00c007500c59014035600c500204820880c51081c0e4044036006114120184d941c00250400c510541041c03005040d0010108010950403220950a4402069400b480303c21001182551040107407405080d075842441901615120801d11950051080c680a40150b030ba800300b030110405080f01414210300615132a0080c10340c10312840c0003440702103e664801048080004c0c1928035180000380642d180000c1c03900d40080c480c0304071a50711010504581d6942381c00a2082a001c90b082000c030340e01d50801c00ca1100d032090100c242409401114092860310119030303a080018404145c0403103103a0424040c00d24a80d417010054040028403415108281c42c1c000c08000110348020881c0d00055000d100900 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 725163750 1250 725162500 725162513
    0x70507030c06050a1e03110c0d0f1803020405100e0c0306032a010c1707060203090d08040b0c0706092003010c21110906030702100b0d38270a 62
    0x500d414504100403140300c90085c000c8010340703038500c6400102c0030f000440b580c0c4040000385400841049603078202c000d010020040302d02d14000c441c2038090072a2104207101601d41544903580040d41014084100c0340c1d118100e00080908441407204a480802000082c1c02c040c88221501c0c11300301c0596104500e4071080b54900c805880205040001d52001d03402000141c000070301100c05000c100ca0303100c0b07100d841d2481c040c0d0f004450b00364642c041c04500085407809503080030b02959020003d2501075807000d1403428180c026400903109141c40700d00070808114075103038009014280d82d45050a141c2d00030141030070354407a54040f90410032050040040c14411694010107902d20210201e0695640c00340c403ca07502860b401207602030b80000501404039000100c0700107032608103078240200c084c02010800c000f1407080d00941180743c0e0740040007d007000000381c0341070010300320303114080600001c101c050400d8048410481d41003480d181284c40c007006403803455413805d4001c02810803407102d60b07918 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 725165000 1250 725163750 725163767
    0x19030308070c080a051305031c0306090603170a02010b0409120e101d1311032e0b16061d0f0102030c16051c090e0f04021e15070507030c06050a 63
    0x4041103c085880303006c15074030800d108014600103041f06d0221030320b00810751024040808200c0403901d40440040c050742c0318042d05040701e8200507070303441400082009658551016950000f1950385284010281da1142701d460909030081246400102e03007810042c001800114105205108a02c00390242d25031000b400241000b1031824101c030052940003240680d00e612000c1403c032424413400c801210300100146100701c440f452190304138030200c5054041c00074142c40b92a0b2042101e81d0601580075002c0040100b020505041415803096403240811241080200d045444030380140455007c001c22001100c0c0f40410b00851440c14207043c0c40003644600c01e5069880c1d0b18040c004024403070240000000700a0518680084001c0030b00c0061501c4070601610100c1e82c11480030030104490003035424421640a40794031040154854035281803002052a280d0002c00090080c03101300b018405045005c0c0304000804180e42540f07055542c004c40f5070402c504020084c00303280443d5903c200300c2c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 725166250 1250 725165000 725165017
    0x50603101806050c0307030606110309012609060402010807030b030c240a0503160e0d0b0c0415030504020a06020604050303070507050c0d03050c07090528060519030308070c08 77
    0x624620640100504076410000079100516040812600d84007142c011032084c11156401c110540d25101e0545214030340b0406800306900603c04046154060084502c000407416984006181740c02c0d15040d4071901111032900c035811100c14041107507008030842d40c00a48508062218116110102e81d481195502d0380748620050f0841c8500c410102d00e21180140210210b15a14850040b0240540d4001c0d0781c010b00100f2052080079400b4410740d032411461100030010154081e00e030700c03415040e01e0007418000c0882410800064030201a0318145142041a1008038262900d4010450b444140e50b1000c0c065401110811000840202c11241c1c004a5418965219102814058600800b16294603000014940f1700d90a064000d40940410107241e001c441c8126211a0300c5026514199000c2100800b00340302c120042c010040c901e84526914900029002d41c0c03000007031490302c07160140300d0a05151000920500d58020342c6154807640c0c9007008004003840d0303980c00c0e02c40c1c801c0c0c40a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 725167500 1250 725166250 725166283
    0x60f040504020f0604080d080106091a1e031513060b040b0d090b100e070e130c050c010c11060c1612020109141b190b0702010903060204030b19050603 66
    0x1002c5544241500c20802c1c0042c1085449a4440980950750791072030300d0840101c1d440000000c1c901e07114510080036554039480f24446d540130017034070a140e60001240704882140200d00081d019130201e0146211f201041040c02c2609110b105102410641461910f20035040000c142b0404489074204c3c0c040b104401d054030b0b5070b00c009a030707101c0c0100360100c001481c8c2074103501800b800380041b04c0d854040d17400c1da030b609905540794400c080da01200c40402c10b40e0045400c10320816134801c2c5620240f403100380f9060803031402d200340914500b110f0101c94160302049034440300c0085d102d01005107a40c0b000e002e40c50103240c511030f568034410240d0403c2000300441c0f0760128840455100313401407500141d0111070703010544034455600b41c44440d0142850750060380413110f1960342c42c008502d00556a404031141c40c0d11414500b2556599100f20004d0341406640400040090050f1000300015401054400d007a8103180c1045105012074900c000d0070b55080005005450303501040d071160441c400e04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 725168750 1250 725167500 725167511
    0x1506110d080618100312050a0e060c01020c0601090e01060608041e02180403080402011d010e04050a18060207060501270915140a1d07170307120c1703060f04 69
    0x500141c0c0f84254001c5060342e82d601481480001c00c104140c007000d072480354491400410842d4800c68290286110680000704481d030212600d0421200810a20000f64005840d258031a505540b4000080c1e0101f880d0507940d480e0810a0030080c4505809030034203182801c1e55082c207482d6544601e00000c03a294142d600f250010045564101009400b030300b1100c088c01b0a0f107024180a44803807012903083c4d002c5424400c5006020b81100c015400341c7d10140c5400450210310001d20004101c0200402045c541c0c404000244900c1c50345d140382241d118a20143c0e5070074403850150140c13141030b8401803042680040b201460703048880510401242443c0c0081c0d4010303241000307590710f25003002c031203105c81c80c2401d40120119450101e81c400c000c40001403101f008540481505038820713900041d11034101070307010311404440c01e0010b00200d404008480c00d04000b47c0710320605104c41c480e240701103a001c1d83c50008008618102c21083c103100e8951034114070308400031801d11500701c51820f21450303844 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 725170000 1250 725168750 725168761
    0x60a0509070e070c0c060f09050f01230714030a090b03010e2a030112020906090c030c070f02101106100b040501030e1513030818030406031d060403031506110d08 71
    0x400d100c0300c000790485c14001704603581e854003500c2d19040c0c9010b1000520103550205a138107183e043d40c5100c1c2d8040c0d44078401010200040c8540c00308804a410131507008100c0795006c542c100e210304c0c09000c20300b03020390741d140401100500070700d100d0750240000e09028001045041c2000d62119440340000110b0700e2244501e03120305404180d261090703400f4802c040000316150420341c010a520034400d650b4521035403580020002720420854038a4607003101000058040b06031240030f0408588500c9481841d850568002801c41d201d0948001c001303420540c50f91695101041210b41200314a0041c0644905001e03407040544511702842c0c0c181900d49030300c189040801c000d49503030310403c4200c0403160304120b881c0150720481c883c01030380090000400305070007105004140103a0014840151b140a00d401001d6024200042e41000707410342c000b05180380c4040510138141308601c250340008030044580e2490140703e032103030031841c02c10520340300801c2d080070b00098803c11807949080c000801d85d00d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 725171250 1250 725170000 725170007
    0x7050a140c030c12030a11120a030504020f01110a06110d15030308071d09060105090301050403090f060c0f06051506071101090b0315241b060a0509070e07 68
    0x604000400003145000303410850000407070320710581042201965800c05015040109401c1c03500441540d40e0820000c10420743d00441540c0710b184200010764100c0001c3c182090065082030b07010f4000320f40c50f0001c002c00c5180020216915031000d0174035141d4a40401030056855000350001040a90f031103141c80d12030110381c025141e010380203801c24815120705144c11590b13a056444120f021901c1c00300482e001900989480000103281c21030301c1d001c119440c0400ca01000b000c3d040b2030501c8010230030180143c80c28020981319a0103525100556498447c0110081400781d0014040121740c4070b02c84001a2808500325071a81c100b880454240c82d10740c08502249003001d00c06600c46000500e800c02c0010701000041c00c14800d803030740c0d41c06582d10500141301784000c5410f0080c445079045007a10314038003101580540720142c1d424204100000008080c103a100804003c2d4131441f40d04141c0711070108101c0258003a10880c414801403c201c00c00300c1c0c1d601400c3c081c503003104202000080e4000c0c070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 725172500 1250 725171250 725171263
    0x101a2b0201020c0a060507050d2a0206040e01030b0411060c10050406111c0506010201110a030c02100e0307110f0f09180303010609140a18021305030d080906090a12050705 75
    0x4014500340b603250741c624000c3c0447c0e0000c0c004592038003a50f4030001d480d9004a0361018003c0d0f5210b09900d06c003c004014083e6040146400c07a4403140c14840803d0f06d03500e0385c129601940c07144e03010701e00c1e40c1080d0926514111100107220311880c4c04000303c124465020901003083d03400c0400c045400d46951401c3c4000c0c180d0707034110082030040824604580214140201a14501e030007007003109450b040300481c2a00c21040130419548001c00041c96514486c0e482281c0d20304c55841582c1d14103604c2d002000540350024684560b0b40c5c0b0126154052000304030000400d01001c42d09118141e03c0500411910700504c2d80c00d9115071074100005418011840406420803800700c1643d50720760b15040058002e20039805004c4e0b007101b0a071004c04650600f071402c41d042d909803803034030146901c04001d07000280d40600421450140f06000000e2952020091613119040361744030150589488400035250402c001d2095203150700c11460b001c0030035403901c4452a0804107280450381ca15103400c22a14014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 725173750 1250 725172500 725172523
    0xf090316050f210d03150e0402150a0509130606110a0c1205030d0e1e0307020d1506120803010302100c3f110d03020a05040e090c03101a2b020102 64
    0x10b241800d45003590305070b00400707074001c9180700094143d40750311f06040c0c03107102210000e4019500d00c1c01c030204215058042c000d404c4044c6049840c10f14946c0c00308461045103181c69101a8440009202460300428030350782d40c0c1e13001e0000b400c44070241c0d00e5a113143c103014840d0000e018060f0541006015003441280c00000400f082132044062164280756100d84803200708400c00142a445089510003004840035150010072030419403000b030f2280c40780110740e001121201c0307650360800a2040b000000d200c4880340540a0184c50750f14600600c40686d110480b0a010040751402c00e100140c5821100310501060002881004100903001c1002e02d04e41069032000c14085008108803943c01107507240103401c1503041d43d4a00d240500c041c3c040e806407481c02c03000300305e040c0810311103c0ca242c0790321988041141c040300d410001800200781014905d40391f1444141e110413401d0030355000580881400c2d40180c035001c140040d8040a40154a03590403038490a003003103101c04095a01c200302c040e0044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 725175000 1250 725173750 725173753
    0x61509030f0303090203250902160210090f1205010506030c030a060504050a0c18060b0a0f0e0a031719020714090a0905030d0e1216140f030f090316050f21 68
    0x4030358401f1036000e5600c078080c0d62900500b10403000700f00740f4400c2c000e4a0040c0030303c1c4d00c0004200ca2542c2000310f030070361180c0035104000c0d8400001400ba0002c94480d0020400081c103100c008190b42021401d44500414090007588410004c80040e00c0015010f2840d070b030840c00003e000c2e141d43c50001d0070180400d001402e0384454000c007042e40c00e0354090000c0c04650ba502d082180c60f0b6035001052281c0200072668021909241c6041c00031402030104022412000706004402510fa9940c0b1240544107016125100b20110f0034850803c1c100c0c240000c16400303800200841407414042180072440c21010900130b400440210740034981a4100418550344102901d48800748805142c00800e95003a54030100d104010841c0401651041100c42c0c1d61044154182d0308501515042e0081c001c92006908522510b0502c0002203000c0c006400e40c00003090480cac0e034841290040501d0100000d40e1030380010000b0300100680da6940c0410389280703009640480c10714604902c2140800ca0101c203038081e5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 725176250 1250 725175000 725175013
    0x705011b0e3f1902061626070212030f070303381c020904080c12120f0604150614040f0b0703092c2d010603061509030f0303090203 58
    0xb012490909a03407403007000740c12101d041c109041c011503004142000603401a000b00042080108915000946070340202d90301c0e0410a01c00708800711011010280d54048100420070504515041c0607050203a0440303c011810541e0601d05148103200c1c580f00182071661700e2b6003983d07903e880c103a41c940d01c0c014483d0350f11150725048821240c84200100300340f8852140b00203065504060a90740c40ca8407038024041081603612987c499001da0702a4500c03d00510a54600c0341c0441868801864844011100030055040484c03402e5803101028114601c550304101030413110303200064854049503140d14150118070070200340c51190f4410380d0001d82000c01040c4000c40c0054101000b045080c0c400c1d40c8249036035645414420003881c001587c0d015802041003804070315095220341d6038010148003200055490001d41c6030301c00c03150b002600c3c5420101080108071660b0140710b21070003032080c0116011000e61100c8010108011808001e001c20700c2501e0000070f0600c00d5001c0000a41e001d03044803403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 725177500 1250 725176250 725176339
    0x40212060a060602070812040b0c070e01270216170405060409021903091502030403051605060912160b04060905070b031b0414042406050705011b0e 65
    0x1420143c003804015100da401d0010b1a58400640f4807960714200c5002d0f410503003402400580da90100300705090700d218a26001c0341c2e9450411640c1e008043e120f207560300c080c9286d1503200c100b01856030340c0143c1030310510110b6108040c8410301c0b101d40b680664000c020002150301c2d512540280c1d0449908502d020902184866140e4010403050014004544600000c07480c22802d84001d1000180129841c0142608801890f005160801e110741011410000e000c29140600307000711b442a40e096105005100e2400d1b03043c1700007400e60404031015450424030083c1c403000002814030041010346403100250610100c0c0c0d000401c541c2e4000140d9a403d03954044614103074009803402801d45c4403101804001c001d0110480d0100e9070058600689011b82004120007489803c0c5080c3c1c000e03813408103189880c511010100003500294554540700c000a062450842d00b048240c94008042006280280c0ea002460400101c41c07c0f60141a0095400715105e031110384425100081e0100415550 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 725178750 1250 725177500 725177521
    0xf110310050102010b1c0803090c27100b160213090b0412080f010b030429073c02030d0612151a060c010b03071e270504021206 56
    0x50807608264000d011003e10141005000e070900100d010600a40c50b5008002504c408061035110003a00255014188210080b03201500380510400710b104800074005684000c2041494019440700081c02c020b40c2041902c052920801035035410104c3e148500313604640d9588115010701c0d240a80030301140b5428903203600c0c402001d6030110303402c5064038858100d00f8401c04401d4807560381200c0030700ba80c0e444c0c03001c280341c1c0e50700c0540183d42100401644442d4000c0e0303200d445400128801e48180d039840d050720010801811f60307089210010024418000c0007658140c002190f8000462a4240710071480c0c2c00e03861445502c1c040c4003500d0a003d4000340c51a101032815610314001c00c100d024202c1c0350003111040310b55000309428126400c036021030750b508103580a041410b4402000140c100141d1000902d06111548400108011980c42c81c0408109000360790040c442d04a9051880c0802513850f10f0409000210a440070350310300028096580c0e4000014280d102501600d00340c1c00d0840061 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 725179856 1106 725178750 725178781
    0x3091515040c020d0e010504080606040c0e0a06030b100e180907170c040e0a0b1306020d05011409010e07090501050c0f030c0a17040f03060f1103 64
    0x600d6807154031801e40303806500d8000301212050550000c0075950f9a0b103500d030412070107010800440d04000b52054005604880c00300781c2030b0780c3d20302c103e43c584005046c484d840310000c10b001800030342541c8009021396080c1e44811501301d5040c070603035103035464048054005074421504900703281c8000100350481c0c0c1c0282a1418079a0741c1c2160400d880100c200d91009070031005090581e464244146c1c0d01d20500c00019207070441e00c42e12040110704009050900d104240f104007001c000b410350440f20341c1307840080100881c0d612000148902041500400e025000c0400040f0710101e801107020320884641e503500c42040c0c24040116510b4202c0c0c61554079620441c078040e1000c84060010300300c2c0920f00c90090007480c8050030504140120908400030005042206102d81440c01c101101503d1700711201040d1412035030035000091501c0352a44d40300b02004801d0151010f91010032 = true := by decide +kernel

theorem cover : BRFrame.Cov 725000000 725179856 := by
  have h0 := BRFrame.cov_init 725000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 725000000 ≤ n) (h2 : n < 725179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
