-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0137
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:03:28.585924+00:00
-- url     : https://prove2.me/submissions/285dfe17-019e-4164-8160-269d395a144c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 24460437 ≤ n < 24640293 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 24461687 1250 24460437 24460453
    0x1020a0f0804120c030b06040501051f02030706050405160b0910120605060a0503040b0708100311212401030b160302040503010203010b03060f030a02130b010c0c1401140a050a0f0e03 80
    0x7104000c91542224006c036916103c64031520100012035a080c401d41d94000950f40900c51079600c1d03541c40808103082d900680307041c9030b940e4a800e42924000c0301c0454107900100180200700342c0d0045070b44040c05a040c0c2450421a0780c0021940381a41e4100400074030441e42200c008400d03468205002501d0302400440e110701e009000a880c64109603803c661011a42d030000d0141846541413a02c6005170f100114640e500d1901c07032070342c1c0b04901c1000e541c00241c503241d007041041070701130700b00c403405140d50041503ca40003840304400d4042042e5001c2e900003400c0f00400c0440d105240154100581d040c07034080c44550640190000e10550740140e40550001c000061400f040754007441c42828291740d400b0034114046c5c101a1980d614980013580194980740448801099900501c0054018100217200d050f0316106c01c5440d41d1103901018000002c1d103008111540d10000d80f144100100c40f4190a24803c59406400c502483c11040c0802640320701c1d42c50001e119240d928800d42000d801d0b9460380c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 24462937 1250 24461687 24461693
    0xb04030b01030b070e030a030e06360607020d030305060604030c08030405040605030114070807111002040302010f0503160c0c0e090a02010201061d0105040b0402070507090209010f030b01020a0f080412 88
    0x240b1081d198071030408005202039024061003010b03510300901030710101c1038558040e40e03c1c203841f01006030132000611999280c4062100c192034041c06500042044908014102c05042d200c0160f80b0701038802441885c005840e5012112181507050401041540e90300c40403800c980280d40c8081c0c4011030340346000816840100080c400d4840c1918140442501e490600d42680c0030f850408901c224180c00041c80309204250b1b4a80100306441e2515070b0445c0440b01c00e00c1d240000c4552441150300160400441d80c00269040c20b81c00c207418070b81c0c11481c22030b070108007030b84100c1110024003202148000c104510a01078401a141c4007001c600c1c0c1c0d080100708155181001c8404901562030014013050f841c1440e10040e64140d44100c0d1500c90b0380c20041400041e0140300d040b01d420540a014440020b02c0c148030301130140c0401c140040c0c407182c80500040c10042003074044000e00d8600540121300740d0340402c087c41e40c00c1d0010b212204040c12440c3c1488a440703258401052029003402c01020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 24464187 1250 24462937 24462953
    0x1090f0c03060c080103030203071106090411030a0b0d050607030e0307120201090506010602012d0209090705072d031107030209070207030605010b030702250302040f020415030606020c12070b0403 86
    0x40d0390280d601000390305030803070041d11044d100380005800b60b8403d0090500040740c1000480d8198000340216084c40106e0000c80d05482d401c81d80c1640318000032007040001400c0d407041480b1402c0c22036003100d001c401503e03056202c02d005810b1408241e1603101c2e611104004104441005034403030042d20204035003201c028002d1000410841d001d018803400055031900c14017a482e00154100700c01030079004005a100014246880d01314400c035001e011210256482806141c407500f403a480300c555a18940c94070034041401041e01000f441240d1101c0410301140d0503072078040e03560500b0301032001c81038040624580409907000a62140f804001c108100364007151800450f403140e0300c14000c42e40c03100c040c140702d804100c0740d84005a102d0700c007071141c000c0d80e400d0040c4a50390041042c240c0320748a80124090320040011440f1407900060300300301e886000320700c542c49080180b808000d500d0910f035009440c1c500c1044814440c020b000b00180710030f8010300500e801890000c1c0d000307685035a24508040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 24465437 1250 24464187 24464189
    0x2030108060f090303060f010e030601030515070c0804030602070602070203060406020c1203090c0907140f070c09091502031008010e1b180105061c0911030c0102010b010503040b060301090f0c 84
    0xe070048501140d074118000c51114010841c00e0080d40c19661410180108150700700d03141c0d410840040e0000e0344540f001d0001c140610700460241c041000c8201d034a80c3c20b0390020b0114020440c850b800c070380115180d4010756059079400000966a1501d40c00d00c0400b074024960060f503d0b000750000d00c01041166401060042600c1003a900d8441219000c0f00c16070004403403500c850340010403015882d14000f4441a070052050400702c5079051003102280b141d4000d01800703500b042000612200384281660180001c15440704148030000c0c55a403140c007101018407600c54241d4000c0b002c0b4409407900c0241c18040c1407843d0080120081c82c1d81416540d840e0b0890f6121103842e840034a05180c1040f03d0840d022545a050700c01882e40f0f0302c020b0004660103a200059030b044105010f24040210b4003c10300140d010302c0e0003642e03c280c0700c0c040504040340706001d107055a141c1900811984d8000d000d907076010380c0100c5402040e6464401180c0900300000c00200b00054940003130b130410070146d428034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 24466687 1250 24465437 24465449
    0xf05040c12020f13180b0105011814010c1104020c010603020a1406030403050703021e03030f0108030c07030206160f0c0e091908090a0f0906090b03030f0703110a0b0a020301 76
    0x1040300d036852008810304021010003940003206a981c9910b6420a08507800d03078410100380028034195180350710058030341d124030205e400b040d40400401083d0303406814440b054103540c012902451034024241540004240402e0610410301024002d0080b404050002540007038419036035110b6a0032000e0081c03040303000480c402c18a1000c049010700d8407080034860a05c010300414039540322900c080e01d03550001c1004604510850006a8801d00c040c0d0381140c0c080d028400541c3c8909040450800b28001600601001d600a001c0c050f02a000003a2010072072350181c0300b0702e654805036103400345c80035034000c405080000b40501c8041000880c0c2091021150203200303104003503d48401940e11107031101c04148204440d5440c190204030000c2c01481400d000030040348070340750303503444407001b0358079650054008690741e2504100c6c2400d90700440b1500b80c4120003441ca00b030304040c03408460703004c1c05501504000d17030a00600b0f003541c000c000031100c95070880c03044140c1d403810000046c007030b5200340914 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 24467937 1250 24466687 24466703
    0x602030d05090c06090d0809031605042405010c030507060501060903030207090b09060906030a0209040813060206010e0408030714040b18010201020a140f090d0b070f08070807031a040f0504 83
    0x640b084400b04107580034001c0103004603d8038031010f040050006c0e101800390f803162403c1107541300b665002c0100e84099140300d01c9c070003115803400c41004200c42d40c090140c1300e4420b0200030035086540605a1200b03443e02401c000d040010700742002c132014041c44100400d101e00c0c050010410b59001120113080320b00c00e03821138180302d44a105020581d40c03002012508900c0000210340300c5d08d003410001e58000006421104030a106400040910b04151070a03506804009440316100e90316280c8030000d0040ca00050100d0b514103120002036004c000c0000d488079101002264070544100c5400e81c8070443e0440c282c1c8c855495204103425548911500140701c0d8005002d10455401030080d260550095110380416072184003072503079594001c040c50b60303540c20308001082095690b8000654114001ca01c0d2007128940224064480290640c842017808000001c201100e030780984200c0d48600e40740f40100e1405d0003c1c8040c1e821488881c10390346d0043c24503098281141599000c01d119038010a56 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 24469187 1250 24467937 24467941
    0xc03160b01080c24030a0906020310230625050a0c0503010f110d0b061317060112170d18030201050403181a1c060308040303020f0102030c040603090f020a0602030d05 73
    0x404c411429102e0f10070b00103c09140c07032100d032000740b0005503034000a103a1010900826039900e0004176401142c401e030b51802002020300c10342c104001e1b46402914801c0c1602c549440f04800141a8010428090081485400000f0348090094110340d0029404800c5500010b141d15114010400c0c601400e4041e43c44d00c44501100a07150140480e505071f05c400c2c1c03d24020300070340200041e10364626070b150044400c2120300c15030b0906000d680c00812004c0c0e0103103240c0c2e044000c030509043c8181c0c454044000d0212801001c100c2c1284000307043c40403032085698030308c241c020290142079207002100708144202c0100c1d080c140c040d040584520300c290307900120b80c00038603600b0308807041a01410000f04001d0b01c0000d00309003900f00a000500040048100111000740c0c05007e5407110780040b6088000403404004140d0100082100800c0b040020f50462810807000b8986002e2441518101611018050144554500300c007403003540181c140c40c800c64554401035036aa110340740301c04186140c000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 24470437 1250 24469187 24469189
    0x209090424140402121c090603060504020a0203040b1e04060509010e1e060d0f020c0102040f0e040314070609050d08100506040e0f09030d15051c0506040204020c03160b01080c 77
    0x41506100860040030310066201c07502446040350150040f03401ca81b01d200c0d048840350107815500e000400c0c46a640c0b50343c80e4244800103003070701d01c03a0303114034011401440383d64003240d0040140d900392401c0c40d444540305c03032103a22003074201d048610b000461101d0004000c11650741c40300003041403a50a80740e200c013840004083c41942c500c03000c0c0c80c4480c60808003544c4102d1514100a00b081060882d0101d6280f10b0141c16000301e910600c19034500f69070000c0c0c104264030025030000300400700c0c4200c10482c2e2915850180c51860308013521240c520001842038100402640200e0b0720b640c0103021210b2a40403120003406a08003034664104811114500141c1c500c3c06800715819075040d0403541a554443c84402081140040d182c000c480c082440b4490300d00c485d0780b141041d01001040642c020500d44424040e9042031404103011140c90402c0c1c420101d034000549940165054030700598848007005003d06500a0410a000070790200e403e50090001c406440b0b03040c0c66658003070b03a01d040e43c07482c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 24471687 1250 24470437 24470441
    0xb0324030f0601061107050301180302010606110c010c06022209061a07080703030e100f0b04050705180402040909061d06060a030b0405070e04081216020307060207060209090424 78
    0x20281c1c95290b0700c601c0061180522407182c2c036410540700c80803180b040351103600003829620104003903840070307405590000902d603090003a140104040c6c10645144503070007503c20b460f1110f0005450500c44218000410010143e04844202004040302175401740e01a00c1d982e501d5509200b1448c006090010110b00001407241c07803503408140c11581c41c5043d07020307030382c0a10b40d400017202902030558070840480451000d01001d401c52643c4807000580034814540c0008031a20380304030b18000c40c80c1404010000c2d401108a070300800705412201103844c0b2400014010384107075000b21018a051034000001c10029402600860a007417203403480048081c109246d49080803201140e109003031003001c0000c142c1d0840f032103810038010400d60b61901e0710f070300c01280c41281c16981107862000010700841400070504c0040c0d0001c00700b89504a2404260a00a581c2c1c058064090a103640c002036050421a00c0d0b4100c07000c0c0407024100051915240c1030034240680c0b0341542060711800a0207200b0004014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 24472937 1250 24471687 24471703
    0x7110105070f12020d050f0f011d0a020c1006090b09011a040e040501060b03040305030402030c090403141b0d0201020903070e0105030616110109050c0114030903031f0b032403 77
    0x580d44000d1042400704040300c0f00440045200b203c0c2d582000321020305c14290061038881c0b80c2481c0401000e0070001d809031700200050744038400200e1011480e020513000c80040e00c0c1c00046103140580c64516803000e160a0640345048808900d203080c84c0002c00344c1c1c85402030f4800c50740894888205a907140050440b0a0126085500c030b06000c000a01c074480c144161250041d000b000001540e5444420120440c3c1c4103039030640214101008000451404005209a00b00c007501c40fa4120705242d42d0203041c40080c10801d0500303903008180c2039528038180c0c0302c0080440c818000c907409880c031194064000d50012010038064003401002242c150580b0046904035003000d8010032981c0d07110b07009242e11413211010300c01080b1103200e0b84100b05c00240559240c11380200080d104d440600d40000d49940012001030301e03141828020014004030100950f030748884000c0c1c404100200001440c621070010380c0051b4204034004c41800450042da4503008104100c80d24601c80030102102010364a1401c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 24474187 1250 24472937 24472951
    0x51009060e09070902070c0312090e060f0f060a030902030a0b0901050106050a02070303050d020904050f01080601050d020a09090206070b070302040810110306150408070801050411040504050a030e0a09060e07110105 94
    0x1080c081013180d400d081e4001c041150051880c4100c0c2912647c83d601807442c2e0010403400212a21024003d50f80c03030365641030704280b044512074041030925010480c0311034442d43d00c9209401c0441d62281d220b000c0d0300003040441c0e0040039a132010b486454201c0f000b480903125034202c0e41c0303804000710320741d13008808a07107a21100b0b80081040c107146540c100c4041d4051041600b0b055001c0c00110100d85942c01400e0140d8042d0785003036100c0d0704107419a4a0158142d0220303204600c0c08604030051b0302c4100520050341d60250740425509000d0001c501d580c410354100800c1c50402604000a0540c50b502030f0003551403402c1512913010075142c10301c040c3c2e50049040a000f034403c102080c150319084444640601120b2005800c05640700821380c02c04001e40d02c03a140301d075103690403c400c009000c81040b01c1074908403000c20446c103080d06d41170b90b07035040d080d001405d00000082003078099594200440c010200200140a15a15040d1942900e0320542e03240340440c0146000c200c050700180101031084e84 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 24475437 1250 24474187 24474193
    0xf050a0b0406050d06020304030905060301032001030c0e211203040b01060509010f05090a03020616151518090b01061106070906051602061209070f0819110f0301051009060e09 77
    0xa84c1d440303110095101420850501441c1800041e007502c1c2c01c405540210b0280d4814182c40e070300c2480200700e803640d1014117410145400c0c2005c5032140c004149a1031440c042c0d030380300051921021b240d180b02500d9013101115114030100d40450320720b9080154070440c8070310501c04540c0d81e038100989040c00740e00c42c194042400c0e000700800d528400c101034139603260014480c0043c0b6903a41c0101e01c1c581c0c060322444070685504c5100d1400d221030241505102c0313821117800c0003c070f503d01c40d81400381c41c050f0113a80c031012540c04500c955501c054100382e01c0d4903040b220200e003550751048040d000310101d84070581103024210014440b140201d00d41d4040f90301644545240c035501c010703031400c080100b4108a90280091101928044c031711071501b445000f1540042035641e003072a022aa15280941c08030905030f004551510184001d1090000c1d210307400303d160040c0c200104001101483c45218403a059887c00c410414005e00907644101100d01042c010040d140c0c54103803041144200701c0d03070b0601d00e80c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 24476687 1250 24475437 24475459
    0x60201020a0f0c110d03020303070f02030906040509090304090e070512010c02070314030f07050309090907080a060c0c02040c020705090c0412120203040b040602030d0c0905030606010c02040608010f050a0b040605 93
    0x80c0907800099155101d248001301c3d00035014002841403440010690040e4400b1003000540394008000d0f40c0c00e24200c0c0000d60801800e0000909144594010140204218004038100b48010400e940140a5240c0244000d846d425007403a542e03000351042500c80c141012054081660600c10717a84900041d6000c0c2c25070318110344419001300c20b00314010000c0e02c0204110f0100001c0d1401610280c2c0c820340155607204000342c20025000c20280068525030003142c810041e03020006501c0f0781c0716a01543c0440d0744009858103503001070000e90080d40190404611407001603001c40c81000342c41045549030304a446912641e6664001da0095044c69102c8659443c041040043c10107074044c15403044038074082d02c4a000c4111a00281c0c803d6016138004101c4801c1c40030240075140c201c04c124607040d5400ea2170480000e5031000080d05290510880200000542d155074200304c0203009440020310582400710307042d200174001100c0000702c2c00d10300310034014a0f00d0306010704012150014000c802c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 24477937 1250 24476687 24476717
    0xc0901030b060907050d0903120606050a02070603201908070509100804020607020d0c061209080405060c0f06070c0b060306040302120d0b09010e040302010f05010509070309030302040f0b040807060201020a 90
    0x10401130442c1c0705000050110b41302200540c0510440e95220f6aa011020b4094484070b800740c0e401900000306200052104402c001d600003207101c11500d46280c04501e18224400044001804000e50300d40c4060010b400758910207800807418900030b041d41c403c0302c00e5031114021280303405010803883c0d000c070322001c44000142c490680944c00c50300041ca1145089a5a400192800c0840b2030031600e1b4810a0740c100701c0140c2004600c1c03055286040c0c10b000b05105a42d4078015071059014491260307001107444143c5080802c0100c4115039544111011821322440250962a42c868101c4600c0f480c0c20005900b4240812801d005581c540c000300300501d0602c161890382e800141240e01243d507a5640881c09584842c0524001e121302200c9103114181410b00a003596030401e03021281d01c0c10701e401044240c580f045081d030722a09919001a1104841c60110040d12681d440041c10a07114240442c4407481540148111180b0500f162015a921032082e8240c1c041c1e4940000841c07041840c000035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 24479187 1250 24477937 24477949
    0x140a0903170c060a0615120f020309060f0109021c0c0c02090403020105011403030909010b03070c080412030f0c030c030e01050c0f03040f0608010608011215021603080711030306040e010e030703020a050c0901030b06 94
    0x10047e100c0021404e10140d40042c402c0342c00880d54402c00c0d0740450107200701c100c07035411032502400b5402e0055182886510040300c161040c14209420165949002c0804e94414503c040010354000c0c0000d85605140c00c000740a40340c2030042c034006d0350000801e408a480c00200701ca0f2803400c080c1501c9030503840c103210f500309a00002c0242051050b4038151000041c0b05400400151190700318048400703001d424010700c101902c101d00c0d402c0c80000348500012a0304000c000030f640d03074149082d0300071408020049480d40140100000070384520707484c5a0701d096012002d0400d4460280312140740954411040780c04003001c2c440c14002c284110f0060040c3d02e502045946107500805c81c0304604c442d0a0b02c3c450032644126a030307410b40301045010804050780200b6080d081410380c506507201543ea070910703036168800038020622966846400200950007034000543d07041d20901529107484a60030043d40f44c03032070204103c43c64011201e40001074a850640300f8103894010104402d203650348014048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 24480437 1250 24479187 24479207
    0x705010909110906040603020705100504200613060207030b06060f04060c0503160605040c05370806040b090d08010b0301060c060603050304061d10140a0903170c060a0615 75
    0x40e5002d00f00f00160658482c20b000700000c0c00a5a40165185803904010b4100704000000701600d5040405000c00b00300c21511501420488400809442d990140010785502c41d070040e10342c0c4527101c2d05001034890b03001710759041200d0140c2000310f42c0c1d68458003001030f0740c440e0300e5a44d030003c0c10500c4184540b07481030030360300d03541c500c1101140e1900c3e114195500e800107241034100c03421034594041108001d19000008000d12041e074201030040700e41480042c041e401242d528100c00a001c24401c400744940c40c030f14004040f00700035680d8508060074171901c0038008a90142c2c4500c40c40c10000c00c030714441c02e200c034101c940c403580c99030070350742084000c40340303076a40e4941992000d031103603400301c0070501c244000c0c8010169a194111040f4402c014588112101c0001520816070150010203444d0490b0400d04d600202581e41a6540c1040307005071002501e40d0409441c00300500d01207000517400b50020515000380c0401ca840540c0c406003003400b641c0b054044c0300f040715280032030302910034002c03901d1103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 24481687 1250 24480437 24480461
    0x11090108011a090d060204060e0307050a09020f0708030403110f03121602010e0706020606010e01020f03121b040612050f0613020a050408010213030605060109031e140a05060403110705010909 84
    0x180f40002050000b1518265098103039801c0c1d5000908110854010740510f15081c1c0640160003494681400248030346820702c0307585149500000d10040ea000c441d0f08030340d54241e03c0340055450b0f0a00d0309005050103581e80070741480784181803c2000c05600001910180c500c044c82c0842659a40c4103c40c80b540c84003c0864190364031410307010b141640c1417207841e0107052103a00a1484e0300e06a400123040c1c203001c0c0304041c10340d04003c5420b0107104010007222704840703030044801c00070384030888445043c926034a01c1c103046000124007c26160f07400306103017a2401c83c142062165485241c00e00f86080c0701642d030640e00c13441c400c40d5200c130203845030098240c0c0001d5080c00745c1010340c0d07001d0003801e80e4080c0481c400129110002881000041d11459420107402c0c41c08003006070950396040c01d41060b0500103072020200b0b003080b20410003101c054004900841007076a481a80c1c9140081e902d1100b0b440c1100800c520b04c101c0c001100c1c00080c040d044500503940c0c8140e891400070080003d01c2005401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 24482937 1250 24481687 24481739
    0x30405030703031d03070501050f07050406051602010905060c01020a23070b040602130e1608010b1605010603080a050903151611070e090d0806060310150903060f0c031109010801 78
    0x5044c5541d050000d0201a4055000414a8600051642500e07a4020030080901005000902071140d0290580314220a030084400c0e140a007400180c0d0130b441075501c00c0750301030000195014040419000381a00703840b2070315a5140307150a0b900b44146000f407048900c0741c0340c000340300a00122307010781d2840b90400d0058400501d070450320702086081001c00d40000c0081d81c800310901150300f10803134001c0622041d525140000e54103103030128603544100390b43c0b9100d8000280c481d1092120a40c0014000c60f4051403081d5286007092010380b59409c6414064424005e152082c411184a80c02e098070505c0d0342c01e4541c401c40c01c840c00680301c1c00004180361b201c920800c10b01086da183d65020042c008d20065008114007140d0324401000c6041c01060341d8002c9074144103210880c4418034101d010346494020482c00381400c0c0c1c0003150008c0b85680003518860030080203051200c3c042c0d21101c4c00c1c3c18103907000e00103440c0d06c03403054500348110740d0f0860004003044010400c0340781c10107000d0112081e4200c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 24484187 1250 24482937 24482981
    0x30402040b0307171504020d0b040302010f0c080402040b01020109230f0d020c091506040303031a040c0e0102010c0201060509040b0601051908011410021f0b0d0501020d05060603040503070303 84
    0x401e142100c66003000f004d030521240740e03c680070010031085200b4008104130654914065003c13592140e11300c1c400030440c0c0303904400700e81010300239040001c10100785c460400400e0b038000001040d00c0c4050328180c1c02030303151925905040d4810f0080390035280e00800d0440c1c4200d52840d58125a07540c80c100003503140110a541c0031860030500c11820807180c298002e00c06803105100304090150040d20800d0240d144118403022520b550003500d04a0390107040c005030417508038075802c20b02418a6082e44c0c2c402d00e015041d8003e81e0b00003411142c529001e90080017041c41c4400240d08842c8280600c036407049a0200027400280048a031503030002c2c042c0340240c1000158100740f111306844010301004150031034014010343e101404240c1d9510130840300034103c0c1c005803a0103902d500e2145415280544080e0006c1480300035a00a01c06800b00a814030030001c07003a0070128000e4002500c0b1605050a01012404a140030000e5078002d0f03802c82d010358542003a07a42c003a0024205010005091039020720 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 24485437 1250 24484187 24484189
    0x30a0606091d011406041805040309120f02010e0f03060405060a0f0e03030604110702090c091005030106050304060b040b031509060109021c02130e010306020706060b18090603070b0406110c0d1205030402040b 91
    0x3147c3d820250b4500c0d07020540e42050300e0040e012110303c1d0884e016105a811000c40030900e0302c404a0001c81c0c084c04c0c2080c28101840115100f11804862990144903035410b010812100280040c492241184204104210643e00c241660b0100c0da0040860b4801d01c081078580c5420f5004c81c802809503442c007440c000f03440d4040390140008460415040101084154003800c003040085200f0140f4901186150304290b005491801702030800b0300001d54030110580743d42c0b256403105515640090481d45500d00c40d030780354200540111600422801000c0c00090001541e00984a000084148041c64003d013010060021f401c2030135850800c03400d00344002401c0350f0007220340e40651300466015a0710780c1d1900380300c070590f1003070381c814189840b04100d42c480d070480d40c1003031044196040b13071104019240e00000a06c1c1100a811540d0010380c00a0006103031034125500313411806089007605d484039080d0080000c1c08400c400081c013000e140d00b8800726100e11500c021680140b004000081c2c542840e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 24486687 1250 24485437 24485459
    0xd0e06071202030706140105010801120213020d0209030106090c0503011e0905070e010f0e0f150c030a05040501090b090102100f0e070303020714040e0a02040504020114030a0606091d01140604 84
    0xc28400543c10024000701400070701d000d0410740c4604852040c0455144c0400240041030502c07400540c1c00f2004454400c40d901c2d00c481d04801030280c0419500c03450031042d042c001354400d80f0081d10a61828400007a040c100303000d00d042000c21600c40500703580c41c0c421801c1920300c1c3c08032007000d1b08040c86030200b40104a8801d150045009503980740f02c500e504000502008461a0f0b20b200b4000e00015200456a40035801d4401080660355166003008840341c00d003031409044c2c41c0000d00e01002ca50748000d0b42c0c1c080058070403908260b8545111941d1050038000300c0c07042c1018240140c01c42c4407580c42c9070505400803404070700c10324000503400304100c41460400550f0b4000f1401030b0045081000a51406010140440801c072020001d52800a0b00150f88561800d00240242d40300c0001038156030040554141c2c040c40d03121050b50700d162010742e080c000c1020b8082d07034000c00c2c0a910080344400c01c0c2075401010548104a1031012b90a03d591b0444d801c50310603500d43e010700100030100703040c1c01907 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 24487937 1250 24486687 24486713
    0x90b0315010605090109080c030c01052506020c060105090c090906010908150103030206010501021b0907020a0c0312020d05030f1302030709090303020405030d020307050714040908040806070f030c020d0e0607 91
    0x5594598981613580001000808550311034249648082a501c0f880e03540800c0d00018001e003420311550341c2044281405040c3c1c00014140c00d0866070681010601040d50001c0006030714102c01d551560380c8403810461011820b48100300043c40c140100361641c10605415a080201418030354060ba5490a14900e0f1035130a00048906040340d900420815404105036805880240060301210795240e0380c2c1c124010710011254415200800400c00700c2c1c1c003e01011240d80c2d080080d0b003a650303031242032038944110258040c030014401d580c1140006d51086042e03178024040079203407103030644400d03c182d07100030034400c416039140c007a01c24001042d02891064403042d82c880e03140961900e14000406041c05171103034040d03082d50000c008500000313901181200544c1e01034001811042c1c4080045001004d0f07041c001000100300180104d01001c0008400340300d84040d40d034442c030306414500200c054801e0b42c440e50000d80d004200020f5030600842603004101030251803141003d04035240c01e5040202 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 24489187 1250 24487937 24487949
    0x150c120d0f0207081b0c060a120b0424080a03090905040c180902031204030206030f0702070f180f060f0b07030309080409090b01080303090304090203040515011e050d020a090b031501 80
    0x700c171010409083d0079002405105400743c240512003002064071031007000384100811100c1881801c100b109640f18001e4003502600400111841d03803404590a07800b6144c10000c1001080001540e03000010380a0782d03aa0b1556841990a01e4866464050400680700f00e54501c00b103c0c0100d056014110111070400300c0490100340c180301401414108076030111141d180307102c100801e2003da1107030000c481e000905c0700c0c079988569850060483c1012000c3d0062801300707200f40030002d00300b0040a5441c0b44440381941c20803c1d0354602d810759045130302501c10303a07459078a203510030407044017014044c08030a8060700b03012400701050355078400d413a0f01580103c40d905503a10380d10303401d0200c281085030140040800541c90b40c100140c40d996030340103d06c0303840c1704140c002000070100b00d014881500499015510500340707584a107044a21446078411981032501c00c810001450714000d441c003400950040d00080426080c03466460141030781440903070305445008420868809080d40960003029 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 24490437 1250 24489187 24489203
    0x31c05010f0801050c03060607050712030c0c0e0402010e09130b040803090717070311210c1302070c0306090f020306040309090b010503010e16022a150c120d0f0207 72
    0x2040032107560382081c2a401075000e6030b25007000c200a078844c1130112508407404481c0991a90340b1880c100b841c0c031030a500600494524446031100b0990004481c004a40c490502d00342615250b61584424800484002c0d0005440d54200c1e15075003441400740380c010b043d510701020b20405035200c816030300c0d0341614211060000042007003050350092018401a10b0b5508190020074048405595981d01901019080f0600307044508603a40e40c41c84001c40d0381c50003540031031010030034041654842c11075032003040c0a040a8444603034400401d108460006170b002c01c00d2000d003801d41c1c803988000d00c45d4a000319000d613400d809800140c1d4040129501c142d10130790754020250f0070301000c0c9050b512203d07801818842c00317000600c40e080b86071500715440780b05079600c5055904406000c9151007103410340012094200340f010442d006108040b90031284c0140e94007200c61070b283c14840210311604901c612036420503c0a0020000d1081c000c00443e10031050206107421172500c4c00040380d10204046038032075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 24491687 1250 24490437 24490439
    0x30a0209101a07060f0213270e030901030b10020a03050f16050a030315030b06010c020f0402040906080606060a1e0203130f0303110703020603010501050904060909030207061409030d0f02031c0501 86
    0x112071800303a0b031004403500d03400b5400d0450001020903415141c1c00307040c008502d80003d41140c6020f9050148d91003131103075002c1c00707009100300316643c503640030b43c500c0f500007410002a440c050409076802d070058052075004001561503510115401d401011100c40007000c10803072180030310a100151540c09010300017500350300d000b0303141c0a01110300c014411004200d040b0010400b1408007050320b42d008400382446107110b030007880014003c45529080b0707035004d072000c540814002400c0c1d000c00e007561540400c41e0f489444417405c101340750182000e4540041e11500d1811096100311100c1101003050740107e900b041417440e030b510458049a0400381d81c0c0d1102010400a240c2d001d0180000c442010300070344001c50541d00840e010380b20501807181480000506070b10217072920750003203004105017070040000b00c54502d40251100841c1c41000e000854002681450038262000c80e0310701c54004001f031417078142150003601c4103101038403942c0541c007003440380c483e0100a00420101000102000068039 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 24492937 1250 24491687 24491693
    0x825050d05120708010b0901030506012105071209050c04090c09060902030a061d1b0403020603040501020a1106090c1915030608010e030c0619090f050c0a090506030a0209101a07 78
    0xe0b04001c2800e0300300203110b0b0042200c2d212400841d60305240c2846c01041d10703620782005884650b0100010140c0300c80090302116000c908e43d00c980c0c01003d16944800003e1003102e00702084d81c42a42c405086174100d19200002c0b40f078542d12072080e15108001c901c9140c0e94a032201d030105d036181e9000400d0b064002003003003c907034202d10804000c2c00442d1483c0d050041070362250542004000c0042c001c0c0c0d104c0300482d10102d20042c061b540150b50007001b460742c0c1d1030180b91075030113174020194017030218100000712080b498002c02c55038071405880b402070044d014581c1c100007590300ea220481400c15485000030803001041081038410600644000c65400c1c90020305900b1280d00322030a402c40e410500940c50074040120f80b5903002485254045900340080d00e08000030803599100900c103d500000000420001040d2103040800442e00d00e02800d903a4444c810545030101c8104d40d16401c965038100041c603000c1111500300c0c40340d0040115036a251031105c0e00d90790780044503100314034003c11200c0030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 24494187 1250 24492937 24492967
    0x10507020d09060816030e07030503180109051305190c03141015080c0d06030b07030509070e160c060e030c01050a0b010804020d0303021c0209040b0405040825050d05 73
    0x4440d245141450209280c45001049660042c2c00700511707101080104c3c0c0b01e00e01c41d03003006204940d404141c2d0041a5285882552640300c10007500d400481004a00d42540c0140440021120064003160141c21850b40c640c00508000304444c401442c07100c1c0c4541c4250702403083e11644c40061310000b9881c40d111010201d240d10041519504030300d94042481950f03404441050603512608003501103413a80c80700c1d41c1c2030340180c01c08031840c9850200d0001c24440c00070140340c000c0c04192803c020035150404015216091400b071031500e0340540001c14240a910111038449403100d00d05030090040d01d40d5000180d0b64964544860355102280c058a41d8000703100700d0340c116451120400007800580c1c00608801e40040c03000c0c0c80384119800c1c58060501030f0b012a101d010045d002402190518502240250031900e4120301030380c40c00c41862100d08144c406c0c28069600074030030a04005240c0041c03541030125503115500c941402021400185080010700342544a648a8a0f26640c0000c1c03003101d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 24495437 1250 24494187 24494203
    0xb10031103060705190c060c0302030106140a02030403030c0206160b06040b010203031003081605030c010c030b03160504020c030417010c0e091e040812040f060c0905090f0405120304030201050702 86
    0x200c00d0b0041d005200485421600300c0d00c41c9280020303010101400900240c1e040300b4800806000302d0b05180b0101c2142d44d05500660503510a51503001015810303000c210740324000c80d200752000d6441040188042801000440200703031005200c1032800b03001e100e000e005482d150200300e606422240510525103098061000705001c00c0c03000b14214501060346c4121134009100240160000040082603020000c100d101c11a800004884d0703111540c40485008001e01050807000900d4280018694030300440c1c10f44400704c00c00c10801c03d0741d04040402c002544101d0611503144010000001e4928507041550741e40e4914800010320a010008054807000241060303a118031801000c01004602e084a1243c0c02490502d55401c40d44da04d00c0c0c0a850340c8100000954244c104001704001c004200d0004c0b07011612901c0140b01c0858544019542c80c0c14038065940d0280c2c40380000342082d0f0040702c0c3c07181e1250280088480070a040e001c0c0c0c1845a00580702680140d44401c2042034041d0100701c0d5079 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 24496687 1250 24495437 24495439
    0x12020306280807060c020303030f04060e0f06070206070c030e010305100918020a08030306030d1b2a150c03030b030c0910030b0c03010b0904090f0506090a060b0402040506040b0f070b100311 83
    0x403514082d03940041c8c2ca902c4010881a10b440d0054003040c01d010055000c2c03045000e242040328181c01c1c0c2100e0403a0380b01e201b00c2c4c0c05401441030500058800d0b1051000641d05036054a40c9140d2451080054010b0324000b001418808a980000242100c1034059001070301a480740302c60901c003803401406040c2c001904598410b60040003442219200001d05030300e041d9003840c1c00b45510740142c141c49a000c50114000d000460000c81198051f48014040c0c900482980d08210140342c0d02c4403200400c10081c1b42e1180440c060725a03c81c04030b03000b07402c0f580102074001d09842a60390302200140c881d00081d21025850081020207000304117000e008950001c1895446c0ea041d0740c50300104069600c03c400308603010703079100c40c24035080280341c0d00205499179001040e204240341400006540300002c0405039500340c01c06881180d142018400c0710246da002800c10351800d4140f0f442810f056019214541040b4010003c04011455201206000d0018071518074051481c600304020400c400c03208103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 24497937 1250 24496687 24496697
    0xf0d0905011803050705061305060f0408010b030106060f140415080108160302030d05220e092401030f031106070e0a06022406010e12010209031203071202030628080706 74
    0x20701c0071440024101d01202c000307d0301d030744d91001c001c014a0900d824070f03442140c1100b004520005e0303401e0024050419504190000c000c40c0c0448000c141c00d0706c90342c2c428000424415070002c0042481410b0f2045103152641405181a984004240d140740350342e8440000161008014410040244424211030a820020418a40c10340e00000c2d00d1326810404071050000c00a00b200e060840c004c01a503c410407002c1c000701c0c00380c3d1080c8101d0b0200c000c03925034a0601441d840e01101d0140d00403140f03642d441e084144503071070782941d40715001149092030580a07c0b820f41d1080700c0a14040041c40e114520558491b0900c0402205100200c491504403100b903400000441140100315100300e414015014034058207512440c00503038980b4910340416805c0080c80191003900b00b415001004030b02c10603001c0740d44e40c0300944520621400141c880c0070008005405820100010f0f802468001c98010803502042c9000704040d500d40140078080750b0b403100001410450b00c0301c24042980103241d82c0c100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 24499187 1250 24497937 24497939
    0x31a0f070203040b03040c03050307060504060b040e030f03070207080601060905041407051804020c0d0305041406010e13021503130c0b160303020d0603020415080d031404060902030f0d09050118 85
    0x30b900d0340503034011000100700200008003400040c041103001941c010060782c0e036442c05401c2020182900b250f041c1c5005091001030344003410b0602c03440000c4100040034609003035841c42c0e45405640007408050441c840c1c0180800c4516040c015a40289982d441301c807095450700003400283c2e00700c12a06451f9a403160f04201c10a07410000f02c0394175a81240c000c817881488000064000c0c01101c1c1ca016003071062001014015825600860040d8010358043c86090502c03d01942c0d910307000d0007002d5841c0404c0011641c40c0904001441020f84010000b4001d14030007142c000590300704507007000c180d101d001c2c1d440082c40040719400024101d20b0b40c85c0c91815a1201000300c07078801c440b4005040507400280c88603000c0c0c103030340420069a4020810f00c1941200d01007201a41c24131301038210385010f101415001540244151400d40200007254010380d902e585031100103245c0013001382c1c0c05004000a4445050050140070200492621101c284a061600042410304031100c0e4440324904008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 24500437 1250 24499187 24499201
    0x1050609040807060608010612050f07080c1201020d05070c02040b0102010b0105160302010e0109050c0112060f03020d1a0c030702070812120c0f0c010506091509040308060613031a0f 80
    0x28499019802c2091541d65290300d2800d0001085241d100c4002d6519010012035092200895000101d001d4001c0f43e03136045001a2490300e581c0c09100d001e02a600c400d40321003081c1003c40b00c03006e0620b1a5000181400d9203e07000e030042d500201c4003840000c558024070320031480c00b88908407030b0a03000c0c802000314082c100000b8004d44910411a07103860602d42c1c0700410103201750401541083c04d01d0003401000c5940c90b0a0341c2d61103112001a011408907400e1020781000f9108401c21145039010441c000b510b0f41c0c007440b056010301242500c50f8143c003803821100b100c0000b07503140584042d10055a50b890410f100a061201603080340c00c3d65000322603015040c13009001030b10000d000c0141680015200d061a0b01e40520071280c00e5000b58401003a5a6028041036000c527114940903202c20202c2e40d180d1808aa61013003100c0070b2644aa07440c008070300402d20601c070f81c50340648007604561910300c1d100110f64240c1003a61003122442c0136003640501c81d110602c0207503001a40314100b51780b1810400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 24501687 1250 24500437 24500449
    0x305160215090304050d0b01080105071404030318030204090b0103150905031803160303032c150703020f0708030402031207020603010303030b031e0607110f030f070204060302041107050f010506 85
    0x4480c240541c0340060100e26a0b0320248111001040020901d40035206076180ca0500d01609110740031a81d483d000c0001c402078010ba0400450a90060b003142c582411a541660b40a80c0e52510f03030801c180c854400b0005844501c10080d5181c00384080c840030398503515102c0d02001c0c80500d00c0d01d00d50f062020000000d2030000985948148180d404200e03803000d100440d21b005401d0b8100d00140e01040000002d058040c0d200c102c01180e400110504040c0518000407000344142c0720311119071000140c0c0100b40001250640c2245840ca005403030f00b480b0091784400c1e40c020110585100c0b4000050004514081100503a080e80d4072641c50f0521045400103800c42c0814030018041c50384480d0007100554090145220408120f81035003408000c030280319075200380c202c9149021501c071840d000c281e542700107070419a0483c2040110319107801d4420182c00f64100711002ca0b00309480344800306c01681c4a00501724440d00d2807c89075125100750400302d00c0d0121100d5135407100d074500700901100c5c1d00c0756 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 24502937 1250 24501687 24501703
    0x30a1d0304140613030f06200f07030201110d3201180e06040303020408011a0604090c0e040e060412080f07030e0a050106080c031002120f06130c030c03051602 70
    0x1048200b494420108040307241d92043c8180820221402e01004c01008174003031041d010705006201c100654a207120302c1655407035028004540340c480c14000468520241d90040c45800d1007440003003010307201e80e420080c45412000b107240348182c44421425940b418140f032603079000c1307501d448918911000e80340e20640040c1800b51542169041d11512040b072901e030000d06080c503c0c00100d07241884c1030708000300290030900030b41c0d80759401c003841100d0807004d4038502140564010500c51500c0c0c039040c40b0500402900c8201c40038060500c030110720540e5980700b08190f2011100140ca12840c0034a00703011444141c108441c103000b480003d00c00c0c1c0900c4101160f50104071400c00080c50301005030045d29215a04100408641c200035000c230341038001140715403840000344c1c101c805142107800084181c0c091414084030040c03030300f00003c0c100b121105d900d42e00721a01800804800030800c59010075220140180004252140341d80d0070155410b100f8a54840d1098001007000a9441f000035100d1100d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 24504187 1250 24502937 24502949
    0x22401050105090d0f0305070606050103020c0c090a0b130507110d050409020d0207020603040c08010f090807061508060a14010603090203030901140d0e01050f06010203040e040f06060306050c030a1d0304 89
    0x30100390700741d054844c440c14420281d00032042407095960ba107801030240c1d020200881303525060880000e0194020700a0700c520007511006030000041d039005004bea0310008041d003852355181c110a172203d4850441c100340d4000c4c0c00c0004a42440d04083c003400c51b0841c8071100b8417544c440300c0d03000903003540181600d098610344980583d89000190b40c20029004590011307520100c0003007844108010002a070303003160440c4000388200d9909001c81001c480c501c22015024000400580d800614103a004104103166111034854840d140c0c0c2c1110b190080c04c59820007900e45ea12121421340b0070a00820b80104950300e414040c80c002680403944a0041510043c1480001000885d150010300705a440c0c40c810120300300082034200d0a01c5010b081c040d110f00e4402c00e85a4080f5505510100869041c2c540c5a1085031032901d031135950f611605244c0e001510001d0742c940c00400080c4040c090540245454051036440b42801c01c03d8800702c500114190000e80501c007161004003030040300352421030744 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 24505437 1250 24504187 24504197
    0x10e070b0f0307021612050609070b04090b130c090e060906060711150a0302040501080112050d05031801050103120206061210020a02030c010c03090c0e060d02040e0c040501080309010224010501 85
    0x440d0303074080c0d1a05010b903003070302c685e42c00d020004130340c026013200c0e114100b41c014811100c031134995902c0c950b00c98105001d0f289520000708414404126181c00c0031840000141200010708404850742044074003c10143d0005140d884040142c1c000521f12560070040403661904c090815a0015010340304e07205004180701881c9240142c550744103c140b5100b1882c64444d59a03620004200500039446402010702044c400000071601d00750b41c0318603004880e441402402100d41d90542a9003580001340011400079083c2ca005608020a000e88c138000c5114441000501020200c06070908000030030545c0500220072545091290009851216241880740141d0f2581703500c0c0100c2c1107108a18000910f5801c103c1071a00103035160340003001d094001c06440140f2030300c5407910820030320140c0d0702c66030120f07690070b49001524251b4400545402800704075440544200003040980300c00f40c0c802031b0640c00205081d406942c060000c2089041850f481041f070b522584200d9a2801c01802003904107d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 24506687 1250 24505437 24505441
    0x702060609091c030c031104080307021c06060b0a030b01080f0f060102070e09060f010b0705060412030905010912030c09061706030f0304090b010915080402090405030f1803010e070b0f03 82
    0x414040c41a40305044401001c0d4800c6902000e000f80c520f9a84010000c0d21f080c0340f10071541c2202c010383c0c0649101b2801786142101e5502040b0791104503080c0c1c007546080307480340d400c0040e140741b1407207004201b4400740c503480300d00c60003014084034212a02541840310360300c1040b800140600035243d0041c9148441189034541d000103c2c9400d03282c1d0041c00c2121130b004140000f130403001810b54070a0003041c1704000141e803100654101c1e4060500010050703442000401c2c00205100022500704200345400200845a40ca034182514610403055506020400e0800d00b1182e25004044c07882013541081c0d0403440c030b00a4020219880d00b01112a030011282c0402c55070381d014403004c50700e85100d03c00c507134a60791200c1c20071009006031a24540800e0b66890002419510303011101c10303c051540b02ca00072542d4640a02407940c20080c0215003a0000b00998810600c07000083c1c64441ca19030300340030b800c800c401b09040c02c50b00801d0020307200c3d602111040012030390700401c541e80c0802414480d5169 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 24507937 1250 24506687 24506701
    0xc060507030b0301020c0102041703070b161b0809030c060c0a02060306040b0405070906020f2103040501090209010f060806040203010b09010c0302030405041806150f05010509010908060106091d0702060609 90
    0x1070030b006640075455400001c00901c8000c05402034019a20500425000d40584079205940d80c814007400411aa00c1c2c0340018071210500902c1d020030400908004100a0b440c521139100e0104000f01218503074008114000d0f9420100590164808180c80040c900070340400080d683c0c0f10b001000a02c1500004002105500c55030442030b001c05001c1c01c00d00c00c50610b2100606661518042c040c010311070742800301c4525100213a0b40f40d800c00300051440401d000d58104528645c0010415900c0f50340b14940c100040e150343d40082e0082854040000100c0d0030a000140810000b80085204500510050001820780c4044071004002420b210401c40414a4264218040c1e0f03808907600c1840c1961480010701840800000984598070030464807000d0194088005070501a80403080750b044010300080d400341c0003c04034960141052003d03681c1d6500002c0c5020800d070404400194078500030440e007080c1c0c1034041550b82140e07100203a1850002c500039a140001070020388249440e0b404a801 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 24509187 1250 24507937 24507941
    0x1709040b130b011403070503161e090602010e01021201050f01210204090f02070308060906180a0c020106050a030803040b1003080a0e03060a1503020d0c0806091005010e070c06050703 80
    0x40c05802610607035260116941450061010802d06804a00071418445403c4030800469101391126100e0382d086403905904210454280d1044a00703018002641c98110300303160180e00c00f140c085a4800d49440c8c10003034003e00395640300807445001d80c01400741101e108000000581921000e60b610950200c0110040b510f50310990210032000422040c0d5200c034003400c0e002403065030141795040c80140d0002000408030b01c142c580160008188502091451510a161070703040000201075956510045a03070f440c3c2e03c0c03029110b80c00040c0d5a034180d50511034082c000d0307100411040b201240d40030f2071901c2d401050310000300020088e02901c0c2c005507444e00c60111880265800074140b5480f400100d101a0a9143d0030102902ca880340c940041c10fa00b0300c0d40110b21401e030380c001e0b032010b03610300d580e00303020740340c5d20094007101e103c00b052002050400003040f5061003580820001c22141c04d05d05005c81c1141c0068000541214038403003042601c40e00007000c0e80106522043c001080d035141501280 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 24510437 1250 24509187 24509201
    0x100c0914010917070506040f081b030a020d03140a0903050c0402071a06060d05041b0e01080312180a05061006020d0e0105070201090e070c050c04020705250b03010308040303020c0a03170904 83
    0x3031b00840208000c20300030303451036200040e2201541100c80c6403084009070141000c0311055594541d1240c242a07005060490065044603c281407040d214032221000640c2c0f50008480c0304001903c002041090140070003840501040507241141381189a03110075960301c0f92155104050b4210502162298a981e8100d81c1c08020140d03040000b07040c90710f0284807001c1c262000c0303220905144004a550b058107091181242d141388015860541e0081004142c440e000b4024141e00104e0500105078810038481049444d10850141150b442e00c00312045006055820081c119404000c0341c9052982001100f100c680090038407030303198030003840102c480300c0c0b294018a00001e410b1040c07100305a04054001c98081c81032040d10b036107140d0039007400124000d488015005500c200c01c587c4c040d50800d40b00f07140480d82d441c1d0034005507842d803203c0c0310164000ea0046446400000d800c20505605014607441480c08171a41c80c0c80501c1c64407110441102d040403070020071400200749210765100c0c1c3c4140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 24511687 1250 24510437 24510439
    0x60f10030b040b06210d0c020402090a06090806071112030402040f0e011a030105040f020d020d050607020c040e011505011103040509090a05010b0a06050d020906040305100c09140109170705 83
    0x3035210700d41883c0000000c0d0003511164020300340d04044514080d990180ea114192203140100580071514000700e03440440c0010a0340c01690810404883e274540d82d80c454058002c6403103c000d000d02c0c1003025403030110014900410070507200303c0102144404038602642d5100b03d4041510307900c40340002001040114903800202d80f40112582c03205406412015800360080000558000700c202818207858088600601c181c1e270010040d0018500340c0c3e512184103001030588100359080782e84481c900f00c400e0b5035200140c1c2c020001c41180b45000e0050007001c0a407a00240815054912080d450340da11f13000b81414070231005030166040500300103403030040000401004603810414490b5494000d610002d649a500705500035400b41403111541c021a8895520396103002e0342040c1c0003009410814046510440800c40000410303001c200c0710140103564080000d054401020141c064a6079902c50102c4a03880c0181c2c155503a005079118040713410350740304100902c061310120390500180341c00103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 24512937 1250 24511687 24511703
    0x30411090702011d0703030905090408120c07060612080d1a0411030a050f0c040303030b0604050405040b0609070e0d0f020d0b09070807060905060d0e1002160c051002060f1003 77
    0xc04080da05410141200c0050562104d00d1451a0300940d11442140000340100c0c201681c00c11980c1000082c859000380200c50a41c100030044035030400300102925810003080d00414114144040d0b0710904e00188040c03106000101c01c0c03556020f4032400744081d87c00c0700550300d401050102d505000401c58980303004100f0454910304074132040103908280c406800c0e00f803402000a11a1aa04840c4c07070090300d02030300203401c0c6850b55400303c001c1c1034104400d5070003503400e0000007019291801818000c611803000c1104500d000750034030198080c000c00c502c0c100708103a14041c6c600d49504001000040d08480d01c1d2407080d5280c008661007000c101401080b1140303580400c814480c001c1241c805549100040c1c40c0c03015a01c407000c032801c15960180039840b81c000c100b0505020b2142d0f00408602030320301d00791007041081c0301c0c4e001c04a130011010350540c0c8050b50010020400307050304441c05490201c80107002d2500f0741d0340c0250390707040050480c240f403401500031403903030390b144406a0000e6a100d030311 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 24514187 1250 24512937 24512941
    0xb0105041a0307140d06090b0402031003020d050f03190e010e1c08040312030203061207030b01150e102303010b070809030a0b150a0e0405060403050901030b1e030c01080c0a0503041109 81
    0xc1c1008100c6d0b8444c07412100c1c9000310181304d6152034001c4070f009000410f0354601c84d9003075030200204c2030442841240c40f44140320200220020a00181044918145101a4125400c2400703071a0710240000107040044481d12500e03150788001c145610206203441c80e021180340c601d400301041c031440e00094003022511005214072030349600298880c2c00241d07041400f8040056106a58000c1404010001c426500062219441c150347c00000e0b8011442c2000c1400e032110089035083d000948a40300207551645ca04800141c0705240481003904190543e2941d0b140c43c0e1740c140c19000350f400040c1188400504084159010000f03404221b0300188051007604023500e01c040c40301c0d1180e04650054000b0100010440598800d05210b66001805844541d5844e1740441e29070303002d0401c2c10f05141d0b4480d80c4420b1902d800800759100c02b0140c540d02d40f01420403003054a804441d01540e030400548604000c0c10308880801c0da00074102a00300700d40c583e00c0702d180850503407240c03a10f850f41112403c02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 24515437 1250 24514187 24514207
    0x30b0d080c030301051207060507020411040518012606041202070b0a2703021e19030b040b060301020403050a060b04060506030906150102030c0c01080903040909050609010b0105041a030714 83
    0x1c50480d1801c030b030400718068001010702c1e201d0107c0e2003842d020850612140c009410310350009101d900c0704068103844d16841e08000b411946141003040c11944c01d030001402061661007038a131401c13040010707a1880b000100307021591484001c20007000c4140500800d040716000304901000351914404850711000c01d081c00600a5802003c1d81c10f120b2a0b419080721690f15008000060300e80140200c1c0e50b811842a105410700e000c07040035900b0aa1245050100205000c40c0c00044c6100d5080c0c5212801e05003000d0302c5620025158074400c0c5d1040108000040c00065901c107030710b90200b404039400300c0c813a002400404060b4051a0046e2000040002007803000c0340007071241800e80d00c0b29008400c00d1004a94a000715074122003194000703a80340d10290f015550999001c1c0080d01100c0c5010385400c0c412040e510350140440e100c1c0d01c08400d01004810a001d110021a028038143d4105807405d124203540a01313103001000c08110010125401e60703c20741e18484409025a0704d00e5413515448 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 24516687 1250 24515437 24515443
    0x1060306051807090209010906051803070909031106060d0b040503130311090a0c081306020f0a0f02061806160e2e050403020d0602210108070e01050102010e0d030b0d080c 75
    0x40701c003660b00840ba0003107840200e520030780311b036480181e4402c03031890704101e0142d0f61a1b2010585502c00c860440360084590740411118010300205034001c2120382076440e0191040401e848080d03641c0d080f100c10880a9190142004511600300020711025162420124154440c00c545a0040c0e000c0040110600c4075010b840d40d0b00f81c20540d05031015581d2583c0c0034041310440c102d0080000c1e68a0081001c1140558203100403030b014060040c5032140000b0303204404d0340001c089101041d07150018044051301840780c0e550004541c0c030322038011800c03a1112a150100288038800049a034001c0e4000340c0e00c04c00bd10030a00001030000100c00a400c040407106c4d450402d040f0032820340303800c00d42e0305513403160b803d40302202d0380a0003c540d0744d021580c07140d0294201c42c0003503d5042c004a044a00722840b0000305000b0000c43d0044d10141c0e00b4981c02c1181844143c100906583c10034105c01150a4001846002c0400d103190000f128511a80002ca80382c0e00c8449c0900381c85004561010615004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 24517937 1250 24516687 24516721
    0x18061803080108011a0609030709060306050a060503030301060f0c030309051e0c01020a0f0f1703150405060d110f030309061c0605010e09010b030a0914010b01030507030e0705060c0106030605 84
    0x1d80301c680340c5030b80c0e55a60a00ba50802c0c2c1041c80600491040c00c822824040050300c1c802000a05640505445001030f07401c1381d1080e0700c29101c0d00d031640140301d074483c40f0f0312034280a0102500610320b55810284060305400000c1c00d04420400c154403040141803080d0310000410b40d0220546000c402d01c032500148031001821845124001c0d101141180e60001a80401440d40940142848012a1280340342c1c454031900560300c0020002490900c030802c0c500541c49004020714640785640c101c0144021520010b1941d030040e20740c00c2d50040801c2e03080c00130740d0003000200d034174214400e0500040307400d50280c070764141c0c2c000320046400708071500b47c413281313034248000c107041040615620001142d0b940d103003020742500605048014414488944000c650100e44d52802182d20701c2c81d941c94030781058407412050741d6039554540d00800c540c1c1c1070091a402c1031031480d00b4000c0c000e01c881d005403940154400d035480b0786400035444180ea00c2c00e4001070300454200c50208170920744030034850072074800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 24519187 1250 24517937 24517943
    0x160203010608070630020301080f0607020703080f0c0a02091003110906180901180b07020118020907050a11030d05100605210403030b040c020c01090506090310180618 73
    0x90807808154010002810003c8400070364908024110548107000e1304048038071009110016603405440e440f0480c00118000c0201c42e005100003d0126440390a085015000a0854000040400210351008241c80e503464000e10f099607100f290f41c02d07080c6459201b4030004c0d00700d8995030402600d40803201250707048a0044a60b04400c2c0303c1c0e14104148204111009a8080b01c607080026220840c10a00c41d8000038110000440801000403924404510b90007100c03034041e00d10070807141950a00811080100c28840d19442144550004d490307414000c2c03040040140226000081ca8440d203092007010b80d41e501540d569485018205000d030004550065a84040007400914148904100e4641508003100920010f252558040c010400500180c1c10035445101e5050156618410787d0944002600100b5950580d02c002410220850780920f11032032060062100f80d031030100d20550310780b001380c0b80010741c0c044004400d000903400c01c0005c0d00d4103241140ca041c80c2d10b0781902c51000c03940 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 24520437 1250 24519187 24519191
    0x6080a0b01031107030c0c1d01061403040c09020d020f031602010e030315090c0705010f050601030e03070c090507110d0801030302280b27011a030c030a0807050a0816020301 76
    0x1100641c25545400040c11158030100200c001181c465826140511f00c00c410440c65140e0b80e0b00143d01a010101210507084486001081119000700007050b00c00342c000056070035468a510f6010802049220f43d40e260364002805441c0f12645034100c644440d03c003440d86441c1c3c2428801c008101e099801d20318099880e10413030705a400e20000990f4810241c2074403c001e034a1801c400d0060040c409130202048003410b010300c0303000850a0103a40020911644005440e00e0010001030980b42d241d0072584403500200181e40100f9001442d12055a840d42c030049a5921400000c072070014410f0352a040074040c0c030700c01405583d480003801d8101c0380260b086500d43c014010f4900c0c2142241e080e8480300b07021160321200014613540059911501d03001c031407010000740c00c3c03c58000940d02d01c8001d0b40d40e5034030042074000300b19403000c071034100d5419801080c1c105540c00c0400d0ba80c00700908050440c10000c100101007040070421090203d07400f007800e94851502c3c24000c3e4243c0840030703040b44254 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 24521687 1250 24520437 24520451
    0x20405040c020a021f03020405040c0c03090501080112060e0f030c03030f0a02030c09040b010e1f09080f030406120204080a08031e060901050d03020c0307080d0801061701090209010201020702030706080a 89
    0x26200003a2030a001e40c0081c00440503c0c2500c5c106011724107405040d83c00e00d03409010000f8a55a01d10840a61403815201e00300004040d180050043c0b001d034000d03a040c0f11240006205d007100001d003200e80a44d00940018002c1411034000c1c0c0380102201142e0f469200008a07005410000f1000c1c600416800026000648811140d2000d034002292007465110091000f402a40781c6a004108069010704002401d4003907440468690000f01d49002c242d210b00c918070607a00743c0e101807240c00608007a8041c243c1d2680000c001c40d101d10940c4180d008100070410041d00444035076044500402d95501154031511580c038280c1401d8004030360320159107090805200d05140355100c07103449544018800303a89a1309000401c0040c01d0312001c03e80452087d2000940036442c104601809418000000c0c004071107480c400629921058208104004511581ca6520010304036042d064903021100940c44040d0300004078028002c0c1074000e54903101d5201c0c000340468002c400d580c040c0d4210300d0b0a10200e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 24522937 1250 24521687 24521711
    0x2030c1b0102030a050d090c0906170102090303030105010f09121a01080a02101206050a0f1401050a090303050d0f020307030516050c0a08030a1b0f0f0f0c060507030e0f0102040504 79
    0x142894201035001da04200403204803d8031880043c0420b4401620005000d0540c0d160b10304503a41a8005d90340b581e40c2c45109002c5465071405504c0042c0c60300d00294a000400004203450740410f20a031414800c0400209540714040c20ba4030b8054840110304101e098160b081005040d48812144003640400d0030010441c0321011900300d41d41500903215580945031480101d6407014094145442d440d82c416022907540d035040502c0c0020300344118641c512a0030a0034485540c410600d48505014082184180300e41c3c0181e0800101c942505013039444a218103840c0c0081e0036511038040d1a1440002040070f525059071085000e102004000c1010166141c0c003904c4070700c5a008460748660040e4804000148803c4c02540d01c18401840451000d14041c0740b8001d100e5080011800b140e509800d902c41c8640c404440c818400c1c261074081341d80525510043d00b0420b80c124080e1240d511100060304882c040c2d0040210040c2c03080855142e100c0040649000350018042c5510490410384c1140d05 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 24524187 1250 24522937 24522973
    0x120a0b10081b0a050d030c0501060b070519050111070303090c06050a020304050d0606050303070803011d040c030f061401061101060906050906060a0315090609050f04050331030302030c 81
    0x340c9280030000c12451044081e115440e000307540d21154400c3e1401c2001c105030720b03895809910355220341c862003415010341ca80542520342c3c03900010f00350b5005020400c041400003922034001030030340004031317070800d1903040607030140c22143c906403184a4001101010554542c0c414500c0324000c40310030310b42c140c40700c40c1160b41e4801c002400c2c0050780300380020701191400e400d0784244c003132080e880011000d0703490700400d0442c0c0082d00c2c1070314000c0010004000e400d050080070b020f01c5500012846903850266200c0e03139902028040a4140e00c0c8904240040124681c07147c0c44180505444018a40e51800003c0948480003c2c0160550134010005500d030000d01542c020b95000800c804080c0d921042400b0707070360f0005120707202056200c03011303484240031004c1607901134641208049100d034180034150080c0d41021307011072407184207201080302061000c000d0742d242c03c3d041c10704000740c40460340340222204410a9941418036018600204041d0004020401c1016241c242c5006203540c1c1c01c1820303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 24525437 1250 24524187 24524189
    0x21e0103182105040503010504060b0118080712060f09050c03010b061204030c080403080301080703170c060105060f0c070b0a031b020303070804031b030e030601050402090a0504020306010905120a0b10 88
    0x80700c0003401201d100410701c0340b0340a0ba14001440e00e03d007426a541c00103030030340b182514142c900590390f08a11041d96408070b1482c1c000318a0035940c80d002d0341b070225815038a034101e1044070004060800040c04010300764011400c0c03882080402d2002a10718180540c958080c3d81c001d5100b0346c6014480d1449092031001d41315904c0c3c00f103480f0b89544c0c2e03031a1004d460410810313200300c0d141384003040007200041c261800f031406090a00000c120440c10f510307120901401806090341d00d200240000c900e0100009102815030f10165003035511902ea007140b8001a0060580d03980903809200703404910b0b000b80c18003501c040c52041d039041c06440d8800700601c0c1c4464401c056040142c00030400507662030301500840350024428a000380d1944000d0000007800500c84008174006211040081820726042082c0c0380580b0007104d0451a0510300d0001170000040c500c01c240c0a20307000b00005034141e02900f800d4004000181c50503100911044082d41c0b02c28003094111400703400c8001041da030610b0344841178 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 24526687 1250 24525437 24525443
    0x80a11011805030d0b060903070f03052407030e0106050a090203040c0f080319120c050a080106030e0709090204060f06050d050f040b04060203060d0819030e0a02030d0c05010603021e010318 83
    0x7610f04502880fa24005c2c1590845164000d00100000100313901e007044410002d040074503600c01e00750b0851400b070741440c0c1c600042c40920320f4216035507904404030350300450b008000c50800040150311040520301400d49130303108075408201201e001038901426001144510710410020031100d480c1c40f203488241d4900d0241e4105980140602102c2120038850240b0000340c500742031f01228000790344001590b1403003170301400062011440c00c100035005814a40584404c0c20144100c01004903255910b801a1140030121a12080004259151030b032001c80076000d042041021140c407180c002e0950ba000c0366000c10020316210004400d152000c602c039006035484042c14501d1b450300c0e218040a034002410f407551240024955200190030716005002e080c40ca410b10342c110580300d580107800c451038441040810b8021400140042c0d4020a00d8041042541400c4845003800c3c180030b80140003980000b908200001d40300400e201c401110040e031b041c026a401e001080444040304c40408072a1002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 24527937 1250 24526687 24526693
    0x4020f1603050d020d0207020111010525030603050d03050106110a080702060c0c180a0c08150103050c0f03010602010b09071b02060c030903030d0e01050c0406090b090d080a11011805 80
    0x61000d4064418080d410303402450200c1c103240c0d400d45200102d82c003150710428004c0d400179000e0215604480f07405601814140208000c6c07034000d01e030a80990340759402c802101d100d1503114201c40e00035884040995040000c44640800b40e0901400030311b028003824010585007101c0808501c030000340b200c6000d611451990070b02d0b0090f800d0051036001407104168a004800310460a9100d0200c4083c6001f402594642c1c681000d542010480344076044980402c4116410086a0200d428078849140b0007860009950758519a60010700e000f1800c158502c04000000040c01d9a03054100d00030380170040b1881402c68507210341c2621403819003100c12582c2803c401081d0701520b80b21000d0844843e8a0090300d28200c1d6010004c1d0855010b07607080c0c00c0b0140e41d0f902c1e502c04004240f185680c40b000c5000003074600f501b04107000c2e00140c454407518105c180006624042c0e5254002801c1c131407944084002e40340d5104203c003030f00300c055000c0745802c03540c41d0002c0a0442c007410401d804180b500300000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 24529187 1250 24527937 24527947
    0x2150f18030c0309061308030712080a0903080118060302120c0a0e190e0c060714070902040302011202160c12031202030712110f03010f14030303041505060a03080309011a04020f 78
    0x3407149542050b458000d410021b81000224500107000816110f44600391200141451200191071144c000c0c000c070141070729285005002030780100c02541074410448441ea8402551000180a410f25400c000d401180410740c4c0700c01001d00081c03a1408502c111004007d180d280c0740d418103503281c00c40b54900406819802c0301c40410881d40079240b2501424251400704aa000128207190b01800040715102c000c554000b05110003400480d0103040719140540c40c2914540008001080c1c2003a895221a400030304161040b0300d07003404100303450303000c50622141607585c0b9481c0a50503986038290040703006041c5042411000b482241c0c841e44107612440f0481940d21404e800515146c80e1000c0d0015040120400020228003c1c500030031824006007451800c0550000b00b0213918600b107800f0b41e0003801400b001800c48107141c0c43c2400c401d1800902170307682a0000348400300c250700140c100440001408440001034208441a5002841810240808000340030882c45480741446110303406110b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 24530437 1250 24529187 24529189
    0xa03080103020f01020f0f0307030e03060705042102100e0f010c02010503181006030507170102040f05040b011b03050901021e0a06020c070b040b03010e06040912030b0102150f18030c0309 82
    0x2a074010b80f49010b10484506a004005203450724018014242d01c42e4804a12041010b5000440b00451603043c1c2c05400f07503040852019229014601600309a0100c01c149500882842e000100c401038004040c6182d541d2114400340c1160b900b194800c0c056181044409400d500426020b21010381c1030303482600c0d40c3d039110000450113501c4030142e2907902411005101c00031490058034091402040600000ea02c0c208130b0761f1041c84601800e10031a40180000c025401c1032908413421160306850115001800e940103c4014150111040380820411008010b16a01c100980440c1c0803c3e02102c1110343c0380c400321652290306d00d080ba101c940c400c48406000074180d401600040c484941118411600c507220190203400c56013040300300740340101c010894154910600c039007204003968104006002b50300c80260b0104c1d140280401d240c0c9070501e4100b2b60744204080079141e03c9100f030911040c02c00c400100c44030741e820782e041c102d092004111550b420002200b15044600800002d502d07151080c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 24531687 1250 24530437 24530449
    0x3010903090314010216080c0f060f040201050d0b1903020307050102010605150c0703081209060f070f080601230301080f0f0322090504050105090d050405010f0e0d020411070506090a0308010302 85
    0x2c0f40d00b000343c3d5020b0215041881020284000d0b45201d4806542c840440c000040d1810a404448060503803010f400d010151494004440e041602807900075528000c0c08001c4014000408801d034100c069124110716290b850002101076078800c40c00d0318246603894004900780c0c0c41d5401940e9102002407120048580300d24000c0840d49402410f4401440c0e881e110303010240c00407080018405a01c0041284c0e83c2d10911030203a00858450000c012070500c41c1000700000003087c240702c00d100034180801c209a0007648061805000d5100c1c1055a0803101c0d05041281c00a200700080d903c06c0c4041515100c5000c901d10281060050040d410b00040d8000411040b6031843c0c0c10078500040b02010490a8081c05054815401a00042143d040207424149131212102c0710070b0811100307000600050380c0c0400c005000c14850f10344004290000e00002c2c00700c80f00000002e51062808903003400308400d080103007540380c0c0543c00fa5049951070200d107540b12845450002d000500600c010700041c60f00c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 24532937 1250 24531687 24531713
    0x901060501031505130f0c05030a0501120c12060b04050c12010503010c05090d06020705060a091101170a1a0402160b010b0405030d11031b0705240406030902060708030f0403080105030109030903 85
    0x103090041030306d12021076402c04488201c1c071000c0000d4400420440d0f0070566024982c014a0605030060303440c074903030300d4190291440d400349000d10070b0b03c0b00c0e4081c2401803541001105480080c030801660500c08000007450340040b074550002c1c400400001900e00d0180f01e1207030300e00d01d1619040d00e01800003080001e0174201500c201c0d6915424407402e4007140c010428984211400c02002800b10101c2c2800000320312882074050401051042d042002600c0c01c00087c0c211070383c0032011400b04410380302a90880340d0003000030b410910204181c00030390040781d8407401d05c5001d0b500103400360340c07510704814991241c2c0c02080e8140e40000203214840703115440e2070502c0c8800000340c1e4149062644d070703d1661800c803c0d1605603540144003d20075403502c182000342080d00828201c907190207070303406d41c1e10354060742c82020300345507445144c40c0c255101d2004135201c09034031654280d502e02c0e000009043c003c40c1a02c3c00e40c0004d0034200045800e040c144603561750031350503880e1071001e10f1542c0c0c2e62102d02610 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 24534187 1250 24532937 24532969
    0x905150901020a050604060b040501050f0d02090a0603081303030305060d0804150e12010605030d0c02370306050f010902090102060a0c18120b0901050105150d02130603050901060501031505 83
    0x5000f0b04280400c1040c04854001c5100f0030010412000d0030781040161a01a005244214102d2001505aa544176548100326a0650b10340e16907950300710b0410014000d550015000e05d000041188080825102d1042568842d8034104619103408003440582c18401e54010703c003074000c001c240700740d801040c204060010700e0324001c06100c003081c0102c0d844480f4104818000d031345940f0140120b14007401142102c03007886c9483d0820f44990340002e44048001035138900c2050400405041515020394600ea0600c0d03c0c00e01055410364131728042c00104801c6a40701c080b14110800452120f41900840d0072242059009010070744070413030460018046003040700300788540e9142e801400c1d4500c806d8180246036952451490301d659040090900b4001002c3d0b400d9a4501801071016558216030038600b401601e00f02500d501c0a0b94a0303078024469041f84101e01e0321500c20000301d203503040c1c0201c1d1003002598000d019443d508d400650030340b09055030200144100c1b0100307201908003170704001d0740d01da1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 24535437 1250 24534187 24534193
    0x80a0f0602040b0c100b0f0d0227070503040501050903030c0a1209021e030709020313080a0203070b04060911180601050c030d06030309030c0b0f04050405040501020910020609010c090515090102 85
    0xb5032603060465a50140003000c0b01307030b0030403400c0800d868141e2082140540301a00d08021141d140030004200e00c880410092240c6044141d00f550040480b01340300f0400b02d4040a00400d052202000d802030b001110b00303d625600f4200000c921840110035a4050704030b4100140c242180c80314195100c1e14030501050030b296540010502594803020314118050144512503c60029101071600b4401c00303401081c0c0060040083c4040301c403d4900300c9645580004482c0c1d110312081e03804a04611a4180c0a400a0f032400180814080c4a0b07200003030581c8108015100002d1b0340041c00710a0501c0a58071144008030340018019501a6004041008880c0c00760303490050003051100403510140c00981c00240b402c00144200501001d240700a030000e404100c0c00e111a06002000910442c040c3c24000d5450700e020808100d8250169040e06c2c6000386500411841c000000756074000489140d02c4075030a0541e101d4000780103400000544501420034a85100c080c5541c0c100c6a0003658080d0440c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 24536687 1250 24535437 24535439
    0x10c0c020d060e0618100b0a06140409050103080d05070807200705040207061508031204020402071a04030f020115080705090717090606040f0b0607030c0c080703080306040e07080a0f060204 83
    0xc442400703403511031080700d01d42e94400480c0d091722a281c1022565000c0b4007501d4040d1929580e40c403421144100c40c11445c100c6108070b044405507010707008076400803895508020000c410009880080c02607500760f600204050766440d2404c9551b02c000b80c130400007080220501e40c0c0030a0440c1000c48041c0d55803012190b8043e03580010404990020b40d05807a05940c1e003011501d690500b094503402007000400460801d05101e0400311707180c1001c0c00081c820b90b0b00180c1d00f4104000103010145030b60682c00364100070703d45401e01402d858945642d00c0015440c24030824400726440381080150307000700c8020845641403900b03020710040090494428040ca0403d0303440c007203100041c07407803058070108058066401c0070781c02d110039640c148480540c04c9050100004441c0c550f04241c03500c864161800d410110350302d04100300b90200e190000030840c06101004030501000e08011401003a0983d0b08015201220000c20344035626400b50018030b0704144070f500c021903019080303203c0c070600403a0014609 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 24537937 1250 24536687 24536711
    0x12040201090b0c0a0203010605030304180209040b10020f10060f03080c011107120e0105030c0a03090c03020901090903080a0902030c060f040e04140f150604020d112109010c0c020d06 80
    0xa60041004031070113074041046442141400e00403840200026001142014104040500c1102040162049050b80401c0d410195510340d00b15400002025140707840c640c820300700003500e541d031200c0003100d01c1c41001c0b240c40048509100b2001202c0303068141c5500c039401c2d69103c0c4174690bc2028078520039900d41c0e8013281196040e8000b400a1441100d00070450700c496800501800310320080e40381400760030300410840c6000c0b0350448444808518000414030720381d20705203101124681010390001480000480c105a10754001050b075070007500e800c01142e0f10020341c1070540d406c9000080d0103410000d5a030300d4034208900a881c00080c0c0c5051181000c1e114080c601c0410307021502581e02075840b20264114000134001800b0410f21000540540178548131120000080600301c0c41c00f80c0d6000a410a03040c0d0598000143c00c1d2540307011303603551804405621441c2c0d222280d4200d0002030b900220300d858a0502c03e101c40001e6681701c0c0c00c4107101d82e4007003100303003083c90400391030031500c94626101e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 24539187 1250 24537937 24537959
    0x602091203090a060809030301031211060109021305030a02030c0f150a09050906060c06010b0901020102040306020310140306130f020607080c010903030e010b010206040f061b050d0f0209061204020109 88
    0x222840c250000c40d10303094031904001c2d00010036889081405018801e04c11041c90200c12241500e4101001074025404410308440e04003c2102c2840c0900498001107644061b0350000c10b804210750780054611905c403820140c48408840d002541980075482c66091400e0980580b2003c600003071541903c4480f00c4503d000503808036544400049024109100d90b00c1e2204020b500300304145e900c181004403141e54603560f0401070140d020398580c04166003496030b200750100c4014542c06101992a0705003a07002075859032036401492440c0320740b5840e1411505001501512621600c0c841d41c8403031041d6214120107900080e020f9030084000c0003280c0c00314100d003008100f44280b8000020b8081403508004040b00c0c06117928154503414000d1904047ea800620980c1103504000350346c1035001c261500c94002e20920b800b8100d130a0a480c80525940d0300003000d4031542c511003000340000224514620204c0c41081c04032580183d00b4082e2100354032000c2c50403070b8003510604040c4c1010b9100d48840c49 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 24540437 1250 24539187 24539209
    0x1061d18010603140607080709030b1b2a070510080a0b030a0b1501030e0102040602070303200105010605030403090605030105130207060e030f130b0301080c061e030705070308180c0409060209 84
    0xd241d0b8041700601c2441940990020780c450300c60329141c1c07883c1d82950394440d0a600040c1c0907a801c05110b0030003145500041003196005165100c80b1115006640360f404640d4240300410300107030085000001c1c15040141c841c20640c0c000d6590f11000c1c4d0380c2c44400500904400d038220f034040c458403102e940007c600313140700c50094034845031070405c01140300001401d85041256141280c3d005010400c0911b80000c0e00d60284c90b4036041942c0c00d0141c015043c0c4461201d001141010340c00c020001881d40c2c3c00900640c01503000769592045291100001e980911007840740b51f40020010f00f0004d14403820b98064440ba0348154030205441e0481e40036145140c02480082002d10000901e401100c1900d01a030350007080c0ea0040c80d8119850200701c5a01c881c600407000d030040c00c00042d4000c0900354503c240c0c1c005c140090f0100e03100c0c140f4010042140c3c01c150400c4011448010128070750320026a801003100301c0920061040665600c140f02c080c22100394200c82d00303034086c011000380365103002d040c038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 24541687 1250 24540437 24540473
    0x903070b04080d0624020a051b01050c03040f0608070c260705070b04180504080301050111120c06040204061e0911040f08010207020301050f0103030e150702090f0901061d18010603 79
    0x1130610442180c8100d00500c5c80c100040c195800b204800002801c0404d03108a8001864a0807441c4008403005071040d2160042030516400002404034110b007003803c81c01e069682039626030340e80e030344c6011041e180e802800101030020542903200019203004e1222440b500040002c1c07450400c000d0366103407860401d03d500451074190020500b40507400c80400303085042e403100e00c001d12040c1450303141c0140c00d101c1030196604010300c070211010210010001084030060341c040107541c4241c110000c40c0c80d07038003d690481c440c9041c48000100c050420b0441080e07420aa14190000c40c035100f07280c001003210401200e002e000c280000036008261141c400d000b08600309c005640c1f103d0f40e2041508403040101000040ea02d04801800460380c4010900881300040c1e41100c0d80f044004441039450184640c0258086507240400c00c0004485105d20f000d40146030081c0150f549840c01c900c1c4449103036210704144042100000c2242403040d141e030300001da8146c00011441e449442e11111611105d2682c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 24542937 1250 24541687 24541709
    0xc0d02060103210e100509121515060a03090201020f0d020618030309060106030b0d060203070309120219020409021f0903120305010f0311030114190e03030903070b04080d06 76
    0x41043c0107209848900c030040c0708481c0030111810308005400d2610007140a0302540f5641111507401e800b84c0201c07000100e004003454604100301c683e00d680e65044110408103406400c01044420510503d444c00010005100034201201000103c0c0105003d00041e8111b11403c01c01c0002c0880c14441e4149031000d59010304154948883e010051203281c141c00c2e143d50b4400c07c1004070b01c8001045460656440d0b2a010074840e010b0400140f0100d00e002d80501800c0c4000306000d4020741607070142103514440c0c40e42c4548450138500a81e204c240743c0091204400310080300200500e02540210100c4c4d2000307060240e8000240d8620141030440030210303010900780e80c0e0074010710408502c01a0b0031023071717482d05101300c1d8100100d016500c00c0c0c0b884010540345450140a145903000e4101c002c103c01c40c083c00c0f04042c685003214010b80740b440800d540c1e00f18138280340c1f10804800803003128450001240110310b8500d9a0303450965800c0020401d480100d01842060f1080c0628001c120082520400c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 24544187 1250 24542937 24542939
    0x40612020108060f01090b030c0f040902070218040b070309050109060207050102090a0e01050303040504021b060406020405010906050403020d08030601021002030708070306080d020615040f0e0105040c0b040e011a0c0d020601 98
    0xb500502010748030074070030381409008012580c4d02c100303001c06581c015001036480b502c44450a8507180101110602000c20110f00450552907a41c05410b110f40200c8260708041c4101e060440118000d0314050070f1071500c1d900240c0258086c1e001400c119100700d000103003844075511203c04a812400044807243d40020b601030203850081c0348a005082d40c01661042c65141c180004d07900d04c40c40c07145901071500400e0100e015800724201800101c00a01619080e28042c5070800c001d60060282a022401541703021990324822410348059990240140700c03010131540340d40080d03800051056045214a404084022314a800a1801044291241559030030302c454040c094441e650000c404036408100b0700c802c2203130b0004001e500406544a40e4220f4411040810003a0480c03103103850015007001d01d49102d41005606c0544614040d030104d0303141a03104c400441c1c0500c26880740f102031500c047c0c0140700d441d60500020b62090308080060f071030844001c0c103150500036038446070030168100c140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 24545437 1250 24544187 24544189
    0x906050c0c093c01090902130c080403030e0f030708070c05031203150607030e09150d0f060609060f0e1003060e030a020d0203190c080d050405030a1206050109051c0204061202 77
    0x1042c000d44034810002548012000f403010880d05100c0c565819032a228031030195180e000040300a114040700034814114200f0001d0304620064900b140024901021900c0039500440c0501d90428948040d40c94080e840d110802181c0281e442641c41556541c4001459a810030480c5840588403200b5600ca1070000c4929125206d120200ca006180420803000041d52000015070001400c41d00c8080700d0702c0c0c0004c503000714150440143d801c000c00c0c400c40c800740480b105000040c20700c0382200384289600ca01508060b12180d00c03d42c69610310317000c4240000b040c041c1000740d0010305501c0d40044166aa241d200980340305000d1420707103800000c0c071901c4840e410300c489258148a80001c5190850001199607806404d410800400000700c0316402040009011903101c43c0710800148441d080500f4034988a0303000403202c80204030b90908018a00c1d0303140c09a9021a40d05861340400c807441c2605100d008024960b02d08134022140341c3c1100103940d140301d008050100030308801e4902841e48 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 24546687 1250 24545437 24545491
    0x40e01080a0510020703080604020d060503010203011d090c010f0f020c0301110403030e0102010506012a14010204080d0903020306010312111c09140a050402091207080d09150906050c0c09 82
    0xf40d940f0141a00402c9000e000c0f0350003008503a04030b40d05841c01a6039200303410010000b44644d4000381d0f415400000006034240122103807a020024002c4070701e6003a2507850b4410b030743d200d8078001e80380401c40700c1c4000781c0c00364000c40b0076410400e8980141c0307946032102d000007801c60341030110384918001c1c045800e100780740c0e0009413184501c40a00080000341402e400213040011300b14034a43d0b02009081081440319030b0b0001050042c1c1e0301212041d400310034840300030302030340003030250f0b074914441c0b600c101c00450700c14404c0104803500034000d00101e90840c0c460051898940005d141070103000030500745252000c0201405003480701d80e4000211400080c010400c0786603520410b01003035240f0a0f082d2955589a141c01180c00c1142d0050b922050360000c00d20b00345100e42c080b5114014244000b4100001142c0d2075103c050982c0ca8200d891f40754142490290040209030340010781100052091600480007840c030313040c0701421110b018404c1000214a45012030b0032030300301c1041c3c1c111640454104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 24547937 1250 24546687 24546703
    0xc0406110303190b030307020910050405060102071520030c0114070c20030a02060d050105040b101704050c04020c030408010e0319050a12050906090c0102010b0a0e0c040e01080a05 79
    0xc0c801071859401c003441c164021101c59200042c4490360750318212600c2d50108120b0300c06950140c4031640c28a40300c0d081204082c400d2191601490421001504942c03010807a501520901d444603001011030000480c0c00c06c104200e805402a10410322584001341040642156441100003041030f01c00c00308040514040644040103100315558110005140030310000c28200840654060a10140e00042e05d082d002040182d00004009a4403401c40801c0d00024182c034025581407005000c15428001020380105103400018000e00d9031140300005011310a412074004c1040f0350440c1e05440014041b83d00054814403998400202081501420b000e100707400494078000e1400d100c0d5040030300d02c40c4092103203680e0401000140c00e1803000d00600c501b000b4194143c908000d64500000d007156660b100360745050075403007803030b000f00f00540c41401104810070000c0d14601816141c000403541c825000b40600303c0052050001107101c6400201c064002c201c03003001410202c0c45400d00f00d0810602c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 24549187 1250 24547937 24547967
    0x50414010b030c030717011103010305100b0105030408040323010c030f0e03040b0f030718030b0f100807060e030c0306040605040201080109050103080f030705070c030501051506040e070e0d06050c0406 88
    0x7042040008544c2c01003846400c640c1043c441c9a1800364880505004201403c404050b9040c040300200502100182001000300c0403401003141c0d403c0c0100540342c0e40001c680c010400e2004100034000118000250040c1840301900c40e80b000c6400003c45094628003411440000d60310a1342d090481031a00a031440300b007142000d1440c05041c0400c405c428407607950a81070703a000000c0400c041c07e1080b1030b12840501e07a80a1100003a440346000c204881041c1d405038a03506c00300c1c0c04249400b106505d00c10446d40c0c0f541c010001249418010744140c10449441d0390300d4020080b03500c070f081c0c82c1400007074802d5111300f80c000307200c4c07419100140c11640f0680014039580e14010040c00047c1c5a58110385100340b58080060706c0e0b42e51084115030038031501200525512560a0000404c003054102c01d00481c10044030f08030b4bc0c8a030500380007841c0124480d50f0700c001100c8c130210301ea00c3e026001c1400c0040c00640b081c40d210100e600c0e140141c2e40c069031401c51600b400182000000c1c0d110581c4009401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 24550437 1250 24549187 24549193
    0x3051305010804081213050d0210060b0306010207090f0908030907051c03020307030e120a110f04020a09140d05030a02030307020d08070804020907020123010311060906040308070c0306050414010b03 87
    0x915407540035181c01080782ca05082114100458541b060f600000141ea40c1d0003400c4400402078110029161142d014584850300e08026010804540480c1903070721508040c1e0090805501d4410414080c10581d0079174002c455540302050007142c150b4000b18452030f00c1c807009004541c41c00c0b090001c0c200300e0103148500e0903480c00708040060780c023000302c40038a030b094078008a0b104c03140c80014400e043e4500502c5031510520740341c0030030801c2c12048940f07051021100f48402024220074442030f4030800d28110001482a20180140050000d00e01c4442d0b40281000030799892a03514980703075500c83c0501c032000d0790000c010404210760410840c001d4040741e01e00003da0741400e400c0504000f00182000307201d13019190020302c00314400d50000c00d4503030070401c44a000c508500c0b01441300060a0009851070a4603c1c260394040c20704004840034440d0240900703140a1544d151000181c00010045503c8500e00c00000040f0b0724502445006a0040d841642401c0102d000c0f1821160300c4d40f00300d4006c1d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 24551687 1250 24550437 24550441
    0x1107091b0f0c080f1b0606010806010801050a03061e0c020304090606210506010311040609060e09010608060d030507060c0801090510081b0307080d080106020f0705030304120f0c03030513050108 85
    0x19400110a040c05a001c16426190784111401d1544c5008070a910030210300715031174562100c0000204103004041c2030320358074050f03150300c801110710b44024080c1075040328442500b0400500c03164003016948a0540f50aa00700c90300071000e80036103206001540041e40080344c148921100c1d841940c0080101c0e08100c0d129135a040d5071110407644c45260100002d03922000105a64000c3c0c10804150b06008a0586c2e244e4440c4001340082c86540030707030390015003c5103102c115130412905031070681700d4544030b0012950310801006640b5000c100101c1c2082424404400041c20358003c0c0012030800d0780760000c00358100442c40046540c001d10911000d80740e0a0200405030002c590741049000e800085825035070710202082c03414200c0d0744400464070a41041d1450036510004240c180e559503401d80c2d2803200c0d0341c814640d072040d0740c0c02881c1d81500104800c0124044403460000348510034040b141d80e9090b141c8a00e1000c00242c1d205030003240c0d001400b012000e5194003040094102401c0c480c02c1340c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 24552937 1250 24551687 24551717
    0xe010b0702031506060706111306030b0306161403040606150201090b0109020a050c10020702030d020307110105030403030f1505010f0914090a021b0307020a050904030c020904031107091b 82
    0x140000841c0940f0144840c0c001c50403c1d200e0600322050650803800601c4550700780219000b1650041715940c000000000e80400e01c90b20030300684105640084c010580e0307032691130394a03620b88114103120702840f4540c9840305508951902862299024650002d41340e89004c200e0b82c14405081c078000116407600701c200000440003205241910078144006072034403041d00d815189441a01c841e00058410444040c0000c426030f0014a5003074400d409a866071b0140a10070b0341e5a0150340030051004500c4a118500c40d40704070050366000b402071501042000760005084112440b5050100d61520550f41c01e01042d600060544515a038502c0c044081903d03110f0058450046591031a218422074030106210071215015945801940f030000200342124280040c1d43ea441000101c1c080e6485110024091510710078280c407454158503090f10b01c0d62242e003002070100000f4070450600001118400c200b8070100040400f03450640f500040400718a01c0030405420b00c125950100a0f02500ba40c0807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 24554187 1250 24552937 24552943
    0xc17010b180406170105061003020304051005060103110415110f0312040f020604080706090801050103030e0913170405040e0d05040b07080705060709090f0e0d0c05010b0310060e010b070203 83
    0x3a80492504003007102400d00002005003449500c072198070703400181d010201c0d0304194002805580b0403245e4920100360b045003076003a400120f0b40a007035604002075891886903640c1040c2d51081c5e05240009a00390f80c075130070640f6504580c00c022242c01900c00c109070059000305043d110b05403104014140e40c5200c1000c50b90341d02c200e01d002c00ca04224800072030204400c50b410004040d0307000380b0994840e500ca2140680d20145403150300e00066191400065180301881018180c0f0b800d580d07840c2c840703a2200d0520814075030141860742c00700d041c4a001c0000c1607038584451342d000e1100a060307030307200e140c034042005a45030225100c0141c0c11a101004c50307150800e0444040b15032034550280ca400301d50400d4801c0d801040009003680c00b0f040108241d156101850f481580d5821a040080c0040040c456045411842d0400b030150b10966402d241240203581001085205200102d40c401c00c4201080c1441100040d1250860315003070144881d0300c4802119000d4002c00c408135052555907000259 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 24555437 1250 24554187 24554197
    0x90603060411010c1b080105090d0309080a0c1b030b16020f1902150a02060412030209010903060b1203041202120d05030601080705040b031f0605040b0f03060a08060a0c17010b 77
    0x1050100544000b01004190310070b00004616589251502c1d81d035581b00745010300812a2000d0460054003440e80e4500c0c000e1058014a94008042d00e013808119076040e04d00c0300100c0b100341c0d10040d410950079412585881003d000d50b2040c40924828100310b002c141e90843c1e074100b2a8107640241000000b14400000d41c203d845050f402c082880c0c0e05507001164540c91310080c1c041890f000080e180100030340010305d450107103210701d00c2d8071417810000c0811412402928009800910241c0080002c01da841d0490000510010903c8071000b41ca655894076543c042e510048c2c545407895803d44c2540b901100c0c0307020502d6900c000d000d40c40e00340e180003800b51000804c2581401090700c04943e840e0320400580c0c000d0050420540e80d00d0400808008002e03100c02e0a001c03406640c3c2002042c0380780305034213881c211101c0103109810200c00054059941e04000c04544d00b008243c140010802e40411595000720409a40024600b00144000300b0204600302c1040b85c4060801c0104028545603049038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 24556687 1250 24555437 24555439
    0x20708070f02010c14010b09061509041e06120b10060f121506020a05061614090402121801050105030109080a0c06140702070f080a0c030b070203070b0a0605090603060411 75
    0x125000380c1480107840d1008416005040001172080004240b1015800303005240011a07850b1302c655660b0701000443c01080d0880309040009110410050516170018004217602c1100070b01c0a81e6142841c101700c412680c04408280b44240c00c09041c00907180700281c1010380350035134100b65420400041d20300742201c9038650070050114040c005050b15640700c000b0b03400403441c0500e113640d80c440b0001c1d5101c0725045c00360307064040d11010414540b100003480c1d8000615440b5074140003000c006200c01c5401107286d29801a408204161340700c0240c00031079101e140c43c052a00700c2c0c4e90002440d50b08655058015a00030303850704c12488003061504081e58422103903858042070076000c0b89450406000c100610f041e07200c641e04103005100e600130031035000740c3d02c240d00000f200560f6040529562144800c01400c0301c50341c80c5040c804541040721060f4004420300489140848540c1c13280241d001c22200c01d603020750384280900c140c1c54404129030304000b0440090503207080684944042c0140c05982d2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 24557937 1250 24556687 24556703
    0x204120b0403050f04030c0504050a060509010b0901020f07090c020f061302041a0315090f070b0301060503040317130b0903090906040b040b0d050a1e0804091521050105070302070807 80
    0x2400301840743d4200c41000301480d1021341c03115520b24159076040c00c0c80c004da5100d5170902c0002014411548215411154010000c2c002c4d0b0b4640441d40001d50701c9100c259046003d014a0300b003039440c080005e14001e0001c6000025034110b001802070406d511155200c10f03a40003903090020900200c030747c000249404903000611500080401c02803016501c200507003500404030021000040f01901c140300d0488603050780e107400452400544c0300c00c110f001e480b08000c03050005006051090005d940c0c014031900746801003403048200b1040a00e421200703420710300c00c240b00000800c0004190290058440b0340214240314613100017d00d86480201100c0c0910fa0380c44107403059540e141c000074035a05002d003000c80100c0050902d20344451802c102079480d48484030301c032441d0701e09817186c241d2800d420103020360800b0306044442d0007a02c255080e82400c0a550100480d1208502d40154040803543c0541e1890140515219094440040103007060520520405010072002011079629951000701 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 24559187 1250 24557937 24557941
    0xc0f04140a0504060b04090b040b090f1f060e090d110c040c0908240c09030c0a060804170405010c08030604140c0a020c0906011b11120102040f090204120b 68
    0x2040040c6000040c1102044404080c0800c0c00510341c0020b003d00e0040c0c0043c01a0a00d51051005031010300b50000e2520200ca000140402c241e2010150000c0c00c90b000c0d107907518800703042035161211080c240a0320100000c00803100340401d100f45001001e41c06100c080c5450071a50107034884042d8140d44081c00001084121481002c0c0840c06191000500801024255010003481e0340b005010b40c02240c0b14090307803c4518400032104c0c01c4003800151418032aa80c0c1e590007440c131500030ba046560580308484015020303a441c000002c0c0a0500c940d1441b2507031a0504082c15440201050105215400c11051040313903032058803010340d00d4006c400990769403201c60220700207042c240f0400494181c3c0600f448201d040f2203008054200195080ba594846038074208081c0700307015500a80403484800c61034040a004003414408a4000c07800600400c0420b8045034a60583e488941100d960024080c4040480d0700c0e4008040c0040361400c5003401d0400381d0161403035600480203440100a040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 24560437 1250 24559187 24559189
    0x11e0c090302150903011b020322050f12030c0102030408030f0a110a0c080c03040902090102060106020610090e03211b0c0a080313080a030504020a050f0f04020d0f1a0306010510020c0f 81
    0x1150000c0741f0030307800204d21021400402500c2e900000c1024408a02400d005d200002c451011007040e02ca0003021307070900300014400c010740302900307031660f0b910b600043c8820202141c00707101035031140740034502d80d0740d42c0c0c501404071b141c050130b000b00002030192500d4045d003c20f40340041682c900820360304210507611030500b400c840321b008980c1100b190788000140402c021250740c0191031240000e03021110f2590301c0b0f080c10b84e100d81048581c2100341d880c0810800502089402890310a02030700c0a49182800054150580708a1407010600c11071000d0240042c592100d0300485800c2d203c05000350418054010740703600c2c1c02d1007003000703040c980f40403000c1441360b111860002040d9a00c0003200390340f5121080058003400d400c40b0b050b840303140e0b0540c00181c5400c201100d5822240006c0007000c041120000f048000d4101071209400715581e003003d009404220701c12100c904107200180010803070094201441d0400c141c1119001d0158061100b07102600040c1981c0c041c00304880320041201c03544 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 24561687 1250 24560437 24560441
    0x30601050904061706070504080a110604030204020a030b03070906050d200307060305041e030c021e0a1202040608010b0a0909030e0402030403080a0c0504060c0215070203011e0c09030215090301 85
    0x314565110b4500f0800107001c0001c2000c050701d841440064400e0b907607134980e0650303541c013492107581c08642040842c80d001071036041000e0382c1e01d0001425a814242c9940104040340c200c550700c080402c0d5100701503c05072404201c05402000c1100050000609203000f20b4090600340c50020b05070303211550002c207100990a4424041d44002d403c50b545159540002800390500b55015504901d017000c940c01030f19242d6450404580c3c160310b40c075044d01000c0c0d00f800400c14989c0c220054108a4080d08401660380840c060000c0c81e0303111008903c000140108411202c1e194070441c941e138902601010b40b83c45904c800c10890345001400a0846494203040d902e2407270203c8807940c02840042040100340d003000b82140a402050403c001c103105100301502c451040e4024180407070302159204005203000d1880401596420f0815824041c00740e001c20300396400001c01104034010314000040c2c0c1c00c42c41c80b0f1100b411000380b400c1402c2c5440d50300801c0800b10210000d1525003400140240c0c2611b0035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 24562937 1250 24561687 24561697
    0x19061505030405071d0406060e07140c011d070e060901060c020d03020c0418030e010f02060a0c050c01061202150f0706020306031c0206090c0109030b010b090307030f29040b01050603060105 83
    0x4003403454800030252a02a005d0303004413002c50310146403000224803481c03604901440360a8503124240d0701c5484070b881c50701030b401c0341584002a648511284852580b2004e00c02c10280701c2c4401812018140000c2100c07000c001408580034140c1d03c0010410035502840700c422246d01642c041e035441d691400c049090818240450750420700b4050783c0d000c4001152460240c550007599040144084800110780c6103131020017a10041e80260f021034001f45440d40410780359000c500f00b007840c2805600a1900351a038580c00b02d60603450313051118056091280700490985e14294026150a418200d03408450044480142183c1e502000140e903a8504109451a050f0441c94907070b00089507550003580c031a01103070307040414028402c2005540d4007506140c01502c0c2e100d50000e90aa00708500d120342c0c1c1e0450040c031070381885400c1d4000089940ba20b61001c903e405500480501c11425401d2094403143d160f9000e8000c200d04200400700760320ba402ea41c10349804559184c0d8a850f2400122054003135 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 24564187 1250 24562937 24562949
    0x9060318010603050d11060f1b0c070f051002010506010806010e0406030c080f01060b03160804020f040e0606010908010b090105240c010204050f0a0b03040b0402040b03030c0606040c020606010f0c03090b0a081906150503040507 99
    0x5202f00030420145481c0647d0803214116104649005804012801c1e550242c42c8240407500141c00700d4041d600910340d1482c0190007030800980d07683e0f00e031651407100d06554000120b580261440144145c2c003805408040c003420160785286040022001e240e10110085d81000c005e100c038049411951012420307411000001d1092244403003020200d5150501030b51418041514280300140e10041805a01d507041c000504040540e0f00c7d100030300c0701845e1001e800d062100318900741d6038403881c05030b006041005104030005803282d09180511118180c07005040d8031403070080d402040751408950849070701540c46241c0c0c003110344070761012401400c1c1c0380c07142c2ca03418000442e400c65011000910325114140c00c640a114440d071201060380c072100182c03115070008200c030400c140300070301442d0402c20540c400e01c0d00c2100d490761400d06005581210622a0000c2d12040900055102841a00c001501c000c0c0701000054901032a800e0400382e544214020320101000003410f20100340030309401004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 24565437 1250 24564187 24564193
    0x20a090e0a0b030d08060d0809060c060708041106120a0f0605040c0f170606030103030503070e040c03090b07020f030d0f0b03010905010204030c140609060318010603050d11060f1b0c 80
    0x1410901000900200b11500d8000d2040814101c000c521a15a0602845010344402409801c0c1e8441646660290300301e50b03040340c0200250741c0e0050007000b44a01c00d9442e42d03a002c1550500e817400e5017004414080b01885103105121002d000403590744020341002c151000041d110411b41c980c030000e00720b6035024903841854003013018015504901030032040205a03584a03c90440446051448801510411341001c0107000520000c0d014100440d0019003604084000000c1311000605940025001c1c80000b074844811000708104000e045030001150700281400fa8140307141d0755601e0003032642d0480117030344030303000c60b0f03840c8007250700c01c220f100c90141c002d00c9000454242a03010754818807041710b5040c1d44100002e0b41244144203144190304c000c2100346016003107000c00031a500040c02c0e16011184070051042004001d105404c0254401c0000e04030803c0c0311035010700380083c071020f45d6101e0b0b0009010050300450045004d5884007502c3e103070b03048101101203403075030901560f000110144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 24566687 1250 24565437 24565441
    0x15010306050106020c010c050a0f2d1202030a0806100c0c030b0105150a09050108060406050d050d030c090303080f070c050f030301091104030809040b03031e190201140a020a090e 78
    0x400e50003903410f079420340d02124944000700c8011541c0315007040c1c028000383c019064280000f150b00c22210602402100342881c00485211040561020001c0b600307289514019174000304805208001446802800950b0601d103011401402064000302207501c9140d141151140c40c0780106030a000396a000b0391340c04046a101c2ca01291202828001c5a20400070340224941078000e00080302c100c090342d1f649070040b00d4646001580d505001400c1d040e40700c0d0f2900c601091720303241c0d4180d035903006000741c4c000e043c00070000d84043e084801c0d80d00b4035420060259410b00210fa0801c02541d0817108280350452250382d00f00d0b08881081500d4402812030107072102100b058040040a076041e1260a60100190b6800d03078561030052145200c010540d402c00d000301c02c840c0c031b8658800c401a14000d41500d140c0001c0d480d81c0d2081d2002050520201c3c00007150500303400400c1031269a61103102d000030000e010b0800400d80d0080c00003081d40001907000141541c1a03813040001600400c16450740085034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 24567937 1250 24566687 24566693
    0x1020409020f090307140105190302070f06050a050a0e0d12110412121d0904030c08030702100b270403030f09030c050d0207061d030a1217070e130509150103 69
    0x3030b0344140c3c03034548a480b07401c0c13002c41d14411180b0080e030303010340503156140350403186900003104124904048046c99824020200880c5501c402410b103184900000519440d201e00c1072000c8070300240512440511308103c201040c40c000400801020550601c10030040300140da61000d401c9030100503160742c0002c0307000188600e41c203040030280780c070600203070b021140d280c64100c0c3d40c01c03403404080003144240c00454021f0f042c40c602d095049402440c10452640d9261215130f902c0c2d1041e070f030801c01640101c00c542d0903003001d0702c42c02000b13401c00c0355203442c03a07040299070f5042d00c036105441841c0c1c0842c281c04581054081d80c01030036108030203881400740848a0802a040e81c44138031060f140b90003840c451200c5584041465000d131000e541b2400c2000710440034000386070320f4204449806100c1e9040381800710f40200681000035030382c2d5499240d40c0c4c1c0654010107a809014200740113019401c0d00c11080c1c0c1ea210868070050041880d00050350f81c4d10b07890300c146020005c425450310f03004000004403c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 24569187 1250 24567937 24567967
    0xd0606090506130c02031e0c06010b030115140901030b060c010504052410151211030109060602030403080406081e041506080a0b04080a0e09070e0102070504020909180102040902 78
    0x1098100301e812001c0020700c0721203001503071441134014005810030040503201c8082c0300d080f10031018424038842d06061000443e249854000c1c0c112194009002c0010042d40d800c81643d00c40c8a0b6262904d682e68030f115100d80e5a2501840f41954107150310381824807800d448000940d080407c0e1138000740030342d080030700b401030b1141c4c00c072890112050340182c842030203907002c444d01c00d00441003c10012801490b00a41140c01080082c4040420410300742200341c2e40464003d034441946010f20803543c03549420040e8040758010340c001421b40d0018842040030801c980180e0741200e2560808034120350382e41105043c900d4981c0e40688901e110765080c4824819668400d00702d0004041041100301e45440c003150342c4281d100401068010b0800014002400c0600501041c1c400e600740f801101c2042000a180b01b04101d40380310004000b18000e036800d6a040110074001c10b03064408500d40102e20b401710704400d80040036400a41d03042800708522040950440300200240ca50440d214850301c00c42c405 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 24570437 1250 24569187 24569191
    0x3130303020c0f0f0111010b0604030c14090106090b0c0c0904050a0b010f05030d030e1501030b0708010f06080c07020a09020a09080c090f07081005090c0406030c08010b0412020d06060905 82
    0x80144580341c010303415400c00c0702040b295128000e15100c0410104130044400052880012403155224081c0c22420703110345003e040514419402942c0e10b40c2840c10864501000703511291007810300000400c05e982e0418100f60958814241060340ca5802e409402d02c0c0c060441384a9401503895806c00081c4000458040348580c800e00428805036a154050249104640101c0d64541c00c0103403008c041d0381c007075803080b0840c150756400d031803813021080828522054242d1083c1d49a40610f410000100d601101140c003600d84105401489410400e00810703262008090280540300007402a0a55a98000178001881c820302c09560f100050380c4000d00008480c4100701c09489000c64600140c0b6210f400c60b8442c0c072407140411156501c0400450304e052000c1d250390480d4200c807101145030f450304900c0034404c079500300e4456038503490404d004080741c02a0008100f044400801800070560703000442e82107500c0c204400c1e03850081400051226891200c0c020b00061911100080c051010f4100d58 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 24571687 1250 24570437 24570443
    0x4030822021302030a0c030b060d0213050a150f17150d050105010b090f01020601030b040303090c0b0a0c03080f0f0609090304050301020309150708040f02040c09080303070c050c0f0303030a0507020c03031303 91
    0x3024468051031b0650954442825096118505200d6802007400740d07809000d2098040a114030107540c1c40d00442c050030b5141e00000038010010004c402c4c4150020614440700f0a94038091031b03840b007200a031205c0d040700a00f012084a000d9180560182d5911010041c0503030010001c000550f550504803070254050540740d800750449120b000d54030b600110b495070489030440711101166072580c0e0200c2c014203040e0380413101c24156540102d100d030102001f23401291065180e80d0020896410081c1540d003008164500304180101086040001d045006070045004c0c1c80480103074171045207460460141343c0005030035610101c1003287d49940003a4200c41130072102003107002600d07444c03c01c88a1400894000d40500701c124040001030509600c440c3c0d0242e0946000c03260180c4414001c1d045600680d00080000c0803076062905200052200c95500c0504485103119a0b80304d5020a859000c0240b910924980d0350b400110f00300d00a001d07080c08018000c0540c0c3e503804103451742d40750180140c0829 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 24572937 1250 24571687 24571691
    0x6060f01020307051002070206040b03010f0f090207020f0f010201020d090503090a08121801031509021801050405010f0e040b03031317060c04050f03120409022104030822021302030a 80
    0x2416500120485411030b030044090300700341c0324801d400c0001c0c0d4070407001260004000c1000180c0b5443c45000345002e41080700748000414545404901000f1040e0400100144108951070050341e85a541072079400081d0713a240f0000e141480140c0c0240602e0203581011400d10f01c03a0004c000b004001001c0706901180c0c00300705680c50700c4e00640e507800f40b01c2e180059a48104901114588641c1507042010014034000c100d9100c0300d034050941503085d9004d44640d03a0040b8203241d429000340710581e0500420302c0c0040c102450140000c0101c5048801c001c14041c20359140e40c29601d89400074981c0304c0e8041c08480e41c48500540181d58200c141c81180c0711020b1080b18094000d50204465014008409815003814202404c01841808540406506105000e4550a1032000001620051044c2000103032211500c0c0b015400f03030111000114a002011810800026000081d0341d80141503419024500301c030b50b107410f0100301c026180295004442c1101204020000d4000703500c1404400c0381 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 24574187 1250 24572937 24572959
    0x1020c0f01020408060c0c07031a01030515100b0f0708030103110a060206040f020603150406030c150801050a09050903071e0201110316060c0c060603050f010b06070b01090903110105090606 83
    0x1500b00d00840c040c4107150742258020070700314002000a000c001c0c0116043d142c08603683d9442154240008001d46403140303101d00100207018040c41840c0e60305140000c42e00c00d41c608000c1c00700105040c1c1c09203041d5030401013907813040c11100b1001d40d4001c55201074681c0d80ca584a0900e8462407070342c00c09861141c006040c01140c01440850602c0c01103030711004e6507d000d815a802c0240d40d8000400013481c3c407085c440d00038416600c501940c80254060700d04140703500c0c10040001642046102c10700140030703d0800400c10350b00c86074400c0c0704846503568009429121100301505501c034661003d484c0c401090003c480240c1009c100d000c01a100b40c988021700d40002d0030b8240c5a00850260343d603c1b42601d00b8260100320709800c1240364860901c4c2c40c0c085034400390742c1c0f4070488010707400684040c3d100050300101807109126003480008125042824404144d64602c100740050095100300c0d6144c4501108160003162085140300600c0020301c40c2d031a0103094541d443c80c044a206100b02032482d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 24575437 1250 24574187 24574213
    0x30804080a0b0112050a0b0703090b1003050d02150604020a020304030209070536091803130905010504060b070303020a03021201181a030307030804020a05090408030106090f0b07030c140d0201020c 86
    0x89980c004da80c41406800305c0e8135207032038102c464000141560305240d102c01507030002441da018914801c00034113618000c16030131424010310740705058840209640c45550b1158221900c0461654003000440d8050b03903c1081e06412421406543c2c402034000100c20284216607400101502844c404103e0700391071068000c503010304084050480c001c1c13940110244111900300710440035030041e034a0183e101508089c0e0420342c40c40e404a800c4048260050350709200c0010b45014035801810300700c90900c5803608000341d02e1118031070600c0c01800e06500054085040e4041c0e0180c80c00464141001c00d800d60352061044e034590b50f8a0318610b941841d003402030741c1c01c0807648002c1c000d90001500950502006541c20781e060600034000b6070784050840d20000b1250340d0008018811403103409020303141e51400a018200d8691074228844941c982c00003030010ba90007405460a0302c0e05440e203c10500180d0400c11880c00c1e8450388010b05002c0c10603d080070f250150010708100514104036a003c4031504 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 24576687 1250 24575437 24575459
    0x2010e010204060503060621130201020c03070501090e04110d0f030e010215011503021605030714061e0c0c01060602010204050312040308040e09030c03070501140c030f06100207030804080a0b01 85
    0x700400f40403600078004a112800c124018004a8083c580d040010100c40c25001d030804100301c0f2000c08108500800c00c0031941c0c188400c010070301c0250020200d02c0d06020010300354081c03601829880341c00c1e1a00040a000c030031904000109005020314141415a04111000d10300605082d0049030f4012101505948000f0384190708401001140409900301a0078250040c0c403410401c003016000e2082c012552070a205010100384a40000c0da0380b403140340b40c8404e20030321100400c506900000c0400090031a15010511904400f601848903aa90201080703000e01404005900544c070f011808502d0341d40550043c020fa85046084504001541c41035231800d00c107600004013001014042049400315032088030742c205640d18203076400c0404810240d07140d0b07000704005840580d19215000d814102204480750405181c02d50180740d45045103000361f000901400c0d4902640c0100c0718220014401c0c05990b024650106800f41c0d036960b607951090350340308460400e1340d50526080c00000c500ea960 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 24577937 1250 24576687 24576689
    0x40b04060c08060906011202070506010f0503010e0706051603110d021506041e0902010c0b040609020a06030504021c05120c03030105031608100207020613080109030212030709050f0d06020c0601030302010e010204 93
    0x10a071680c195210801115204000d024001f5021340a03c09900060030030701056000e441c8554510812600d00410103082d2072160380b002c03e180c2c1049034280181c0e548401200c2505452100780200c1c1c460380d240464006035408000c0b05640110340214014590210b0700b510314242406130088191244e8040004442c01c45221303810b4007811500541d14401543c011030300d45801410300c00184901e07615441c8100e141160100c0780d81391f50b11801e03000c502c0c0041c1c64201a00c03603898100028a015400700e614440140540032541c13040780706220030800100000e507002201c280b5165118100080d5103943d982080c00b51a02c079005040301c0e03991000100c2d03100d000304c504903401440f81d2068401442e00039440840180c4c0c002c201040002480d13004402c20400400b51100001600001414000d0405e803c101c4440b1078220f0800c00e00400a501c02c600310151202101c03040000039400c000144120042400103116038004601c0b08e000302000300c0c060b8100d901036002030201c4640301140301d08038826 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 24579187 1250 24577937 24577939
    0x40c0e280c0e120c1c05070803120c0315190f12020102150901060909030f030c0908060703020f09090112030f0203030405070b180306090706030608120301030303090f0b040b04060c0806 81
    0x216095440b061400c0041e51007503d40020076115203c04400200b040e480c1c40101c00c0c034001c00c4900108082201c2041110028150039000e941007050019071542c85400180034003010f00d0011020603c1e40101c5c030301109804030014610310103280c0300b070b0b1441d4000000c0e10400c014200905800519420780c4400841c440d54140e01a1038135a001c90811040160084c00c0f09500c0e40d81c40c04003003031090040c030800346060b0190711041c3c02d0929400e00241640c0080702c1910410400174810009407000042890704070000381000f680b20051241c02d51a2030103a101c409500811000c000140e4010034610500d00a000340d84402242c83c68502c181c0e030364401506d001b045580300041c2042148022405081d040790000c0c80c107558241c1420009292030700c10396a811941e08066020041c29826114400007049510080c1288030015020152075000510001c3d00341a140c0c1c120108229030204494a481e0f03110f080f40e0801c2c280b505004108420441341115034902d41041c441025002d00421481010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 24580437 1250 24579187 24579197
    0x40e010504111c21090f0810050c0712031806050a0e0c06070309050409080403021009090b01030902090105090a11270405090a020d03031e0504020319020d0803040c0e280c 75
    0x1d030507050521211413405a020400c01d22030808991420428400c4d4001c00102c0000d00311000e80b0203030b440807a20702a00c1c0343c0c00c0c082c0c200103100010301c0d062130051300402c050600240d584e1100790340143c54201030b4402007009282c60200900448164050302180140108662103803c0301c00a000e550300c102031004d4080740105a04100f1403400350010f01c0c4440c444d400440c1020394a902007500b04540115883c04252030480c01c1c80f800c00184544040a075003444d050003110b100b500420203501060203030380d0041d04c0c06400228901455003101c80d4030180c0840580da00c4420b10010040a0b049a0818079612500c80c00c69006141c140202400740b941c240141c01e41c40c555900b0000c000404540890501d501c1e0585034080318483e0304c0c40d131107a80d21840701188501d0644105030504c09444200494202180718030000760311001035105245d0303805240c580d030b241c803181040c0d8a2107003103034008100340099000700880b00281d0740300140d000355282c003212030344c0070a0342c020404e688180c2e044100050f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 24581687 1250 24580437 24580463
    0x3020f04031101030609020c030307080c04150503090f070303050d05010605030c030a090318080d0e030a050d0c150f020405010e03060403021009140a080403032615040e010504111c 79
    0x103180c02101150b28405041c000750381940c0d00e40c0303001a41c20010150300c2c1c80e0400300c10080748640142005074080010f13400c1603d0941440810540001e84400ca81c0c00c001c800710015009442c20002c88000001c290300b2240c1140d601e2600070120342c8503c20b2685114288000000d0703aa016a0549002d1042c0418042c219520710403101c0080160000940030000703118600c240c005080d401c4040904a018003070002034002c4030700900b42040e1220003d0007944500c154401060001c90005501496071403e000480c4403400c02804101030b1102c1d03c0c940700d00d4203032405070452a0364001c00032510203032100b8980b0020302c410144c580380101d070013402680002400150300c102136805000b0080c46480001161501940810700d007200c1040b080755601800502807007415088800e5207074038208501c004032080a2680c561035601c90103800380b01248100c1e417482c0310030750740c80e04200c00214140e0300030001840e01c1d0030840600c20b40c00b05190f02603d0010303c1510b001140806045a280c0c219588203030355 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 24582937 1250 24581687 24581693
    0xf0403020907020c090c040f0602030f3702010516050702010905101206090e0c1f0c0807050f06010906060504060e0906040b031b090106030c021e1e0a0b060103020f0403 74
    0x844001004102103010b08009602c1c566174148449008001c1d0341e00c013a8460f4181760200b101560550080c03015580140300048800c04c005c2d0444628444003216000d90a9640c1c3c0503802480e262064417000b680c02c006201d0609505500c51481945a40031800340070104200c01c0c0e03024400c1b414007370b000480e020018003a07070402c50120307010f1074094580003c0c0102a5080310003200d10903040510f0803034882d950700c0381003201007140c401e007858121005030500030204c6011104c0451301a80b1804e11010014403028801d0000650300c115420070151410740096080041d16443c090040400da146014000300f41e507482402507074241c0f40c10303131030746c0c407500000904018252400400381680f06071241c503400c1842d201402812100110036003c2080d040c1014100700244005030440c00c1058504500f03c00d03619400948907004070001200b0103d8181500181400c00003d841d90f40f454204c403880c9070608401c009002c4078894020b10381200180c0f00e0b0f20044050b44100c0d02101e2610070203101c14404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 24584187 1250 24582937 24582949
    0x90606040b01210c1b0605010e0c130e04110a03030c0308010f060509011d0a060c060f090201140c01061e0302090907080604030f030212101d0415020d06050901030b010f06050f040302 80
    0x152404d03801d003811890352400da60324034404100004c9802c070361148010480d85403504042a003084198660500b008031003200c80080c0340b00c62041c689103400140100d41484040da42101480c1406001415003513100d050191011400c4401240024011400040c011144021000030303a2a2030751545d18001d070070001121f2200802c0c154540001100481200701d664141505d001019203840d020b0714000310313085c03620482ea0850640b0841604101b01000182c2c0e0048644040307104904d4030644490f1040d101c10300400c1d4507049000018a201c090320100441a01c1d40c4080743d200700c07040c407910ba550700c4501ea05c0301402d00c40d40080c0c0c1e0000b408a00080d0003450710070b00140c1c503450014100b010b584040b1401e4407041d2100d8208407203036041440b5480170310701420780c0100b001e05940c0e00342c109540c664103041c514203080780030b541e4042401c4643c0e03c1d02d0340098006000080141d1440e58580c01d00c03810001003841800d100021085c4005601030140c1c003562a100900c40059040078659000c2c800c2d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 24585437 1250 24584187 24584201
    0xf100c030e040606080906100501120903110d1d0d02030a12050d060f030201030e06060d060209120f0105060406230405070302090402180102010506010302040302060912070806090606040b0121 84
    0x300340708480e20071103515155485080001d000941d01d030411410034010f040d06140c3d0144c100542801d0080044c4856608003544440e84201d01e000000d050380e65081c201c85490b425100c4409078040c0c2c0901c540c00c0341c0d1207982c40150b250403101c2c148000e0f01030400c000c2d082c41903174030007501508440301c03020210303d08903040300225030716040507454103101c0382d0300000700d5240b0b070008034005040d060144255685071050030152a41c10f0009c0410b0304012700001c010b0002414020031b0702da000030347c0007819244d02340c03c500320015240c2100d0346441c2110800b806002c0450b04240507919042e80000c40c0f0300d5841e02c0040e034126203010800c090950005200140c8001030001c0d0905030200451070f595180e610042c43c0d1001020300c058400885500024203552000d0011410036005002c14000350f9500c030111602164101d80030303d11302003517800b0541098403035480320401d030040d50204010810003040d280e1040304115010040c51220500540307120403991142c0c800e070012031440078030500c15a4004c43d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 24586687 1250 24585437 24585443
    0xf0e06010c050a03020619050123030106090608031209060708040b040201030605090c09130515040207140303041b0603060608070516080316030b0301020306030a0b1504090602030708060f100c 84
    0x1030500e9407107031141480c0400e021011001640201b0070840c8441c080c50340361041814198081c002d55142510703081c81411155540d21305903c14a0349a02c882d50254003650040403541c0f001c1c0f200300d0b40c806050b6204e41025103214524604100019484080401e10900c65a00c50311303945070301d842d03540300e4a0851100510403814156900743c0411b10b036171400e19186c82500c841c40c0780c90703a411491003800203910f0200e10003000300e0300342000d002c0a40201c2d00c0412081c0d106880050700c401c00c50802d4924000c0004141803039000000c148028451194010190340141102680041d44c1d110800ca08135602c0c6c0c465000041c000d207001c075424601c614020142e4104400144040304800e4a501807654019117510241c4c0003030184007040541c00d80288051000110021401d51410b440402e40b5401d942d54000c1003202030000145190310105200b0910303d00262040222508603c2c00c2002540140e03400d102250425000403070902d04028002040c50000e0040076410043c4402664201d80240c021 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 24587937 1250 24586687 24586697
    0x2030a230a0827030d0f120606200303010605040501031d070605030604060501140403020919050702100f1e050604021b0a0212030a020304180204031208010f06090f0e0601 75
    0x40c05402400304100c500e0203000d0300e1101d03a501c02c140c12400d4014040d2103558044010111600c0d116680482c040400c503445050801d0150000a42261607054002c50008400d241c401c0109065500801c0d407050014500880702e1000d0419429030340d00c2c04240300c0d00000940400041c407ca5101e234205580711790740180c848076a0f117920310001b81008215044840080e1022080003014549405803900800081c24000d0f04400320035850505407040f0b00019000382540404110361006039281c0074003d041d4580304000500b0071060007901c2d440054801c035101382c282602c49540c01ca05215101e130728604114182445605580343c03902a000c0140038070707406a0f081c80544081c83c003844040c030f200b03840d40004d4503600c5103a10400c4820f44005100d00307101d034401d20a800d542c5030004115829036840303011070080e040d80c104c0c094010384603d4000600d02e42160b01c010b02e0041e080140903041c1ea0302c2c403070f81c000030355290282200c54907820b1041da440f0b40c0c40001c0070840e041180040c96000541032500d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 24589187 1250 24587937 24587993
    0x209060403080d09060b0409020a15021606050301090c050a0807140903010f020301151707080901091415070e01090603050903040e040f0302010f0c090509070215160905060702030a 79
    0x1041207035000403481001058031803004c1400c00026102c5c040340710300200c070700700020503842d004100d0441650080c1001030500204504c0418000c008900b0607468811100b507605440d95002403141d082032140d880c0190402c0c40070030a5902075130540f1840200c959515526130b44101003181d22061580042c20050b07410006800380c0e80b001c0c0100701c602400391801680d01c0d45400d0501752402400384803003003001085840484130400c910405c0e40c229410346401c440c0c0b81c40745086180108108080200b011394a244181c42c84000810204205210030307075442043d6031410310a44d6103c0c4030400030341c0015110403051003018003030740c03107260095104030071a0f00303194035014a01501c000c203650540720030b800800c003442016424000c4068445100c1c00c148408400c049020b003a44001e0301a60b44642104400144041e01c2003025041011518410313003030300e003003d05043c200c4105207045000028003916001c19131341401002c903040300383e0180c000c0441215940710039180842d00b100181005110b144 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 24590437 1250 24589187 24589193
    0x307110102030901060623040303050c010b0303070f062a0c050118030e03070f050a14011106071206080a0803040602091903050d200d050315061206011808060a0209060403 75
    0x2014503c108840000003a54034203040019001c0e46a90030209030051072000c0e59241050382406840c00c803641404d0268403030102d0008640503140118a4a4140c0300105d5000c00340a44100d02d103110700c0c000c503000c22000700d590340c0040340c0c0ca0ba900052840060401241c400d618411a5161803040c06080000703030601c1491400c200c0f69500e224160f0014820700080c4640b80380c10710001005001210b4000c605501c0e00001c20b180310440c0c41620300d12885d8607400a5903074004d9007909100c2009900b503c400d841d144002800740500b07100d00150300fa141c00404654514000b903008003042c2c00c003100f80d0031940d8030390b209030103035000c4040c2c2a000301c40c000d41c1140c0c0c1c0e4446151030024504c1040681a021b0781d20324010850301e02200302d00d8140d200d200310700009074000708010322012601d19001303569594070100310b500c4507205820160070650000715580b0004d000e6031601d004200136078400040c0781c501045000684a40e014041842d000700000c41c0e1946200e030300415071600d016041501f80399481e1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 24591687 1250 24590437 24590441
    0xd050408040306111608070c050303070f0c0506070b0f180601080303040615050d02040c051e1801030507021506030a0b090303160504080307030e0d0602040f030311030403030f0503071101 82
    0x510200c44003280401c041c810052140035540c000010889805c0c00c04c0d0861780e06600c0002c0c06240a0712000f800544c910a0050103410103010300b0000d0104c0c1e0740e454a40c0780c000c4282500100a4600c1a000000800d03e0b1418030b045a1003550841c404a00b1600c4030741c110701892001408100c0d5081c0751012901201c002889102e0090030b01c58003850310b925203030a0410641d009141500780e6254600400d2281e46d0f034148442d00641d0701610b0000d01f025507110141d42510403140300e689611031040400644003401c0c001040f1095104126220780c210385001503058820540341d03403005d80c00402d00c40600d13040c0c0b804100c1d4040346c0242222940005030301c690143c0c46003500d00101c103820000804c0140c0c03090300c0d07407103902042da40b6025151501d0405500e0302d901918800070104403141e1041001c6a0301c1d0700c00c00d002e10750401d10840d40e80d5914010010001e03054403046000c00c102c0ca030410034560000c001d40d01241d41684030070300c00e0300300e440702212550300081c4050103101c414144940308040034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 24592937 1250 24591687 24591691
    0x406110115080307050c03010c0c060203100509010906060311040b07080d09081207031b02060106120920100309020904020409030309060603110a0801020f0a080c0f070302070323070e0702030d05 85
    0x200001c3c55450905013402818000e4010001d1f000b681089901c0045a81c0034112041c1e83d41c01c083c0050f00c0341c40d2a0540200305215511540d80103c0b614000300388600c4a0b0b202d0b5048500380d4404014508440110054a0040d071040500031201030180401140c850002020f410940c148000342d2003170240e072140491b80240410a01000c050020010415014800c0d060400c00c00c000c01e140c81c003030251000b551514140580d008224031502884100005a008005800d41c05103c2002c02d90003080701d10b8003000c4801015102da100c200c2008440f07400791040b82112070300589421103580d03554080c400070f880d01100403810180d0307800c00c4402182591040344080c602c124410343c10001424104420516160048030207a4030401c496034880901c1c0d42101c400340c40c94100421107076503001d180902400740042603d502a40001d9510426501040039020759200c1c1c0c0d00391001c07100d035a100c45000c445012490541c2c2d4028a03050080c6810301e0103480c0e20041520480c0e00d8540e03100200000c2c0c13081 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 24594187 1250 24592937 24592949
    0x9020a0801090b040b0d1101140f0a080708010f0302010503060112090c09060605130306150b070b090111070b062e0804060506030c030a11151c0f0b03030406110115 72
    0x308500500112205000721500203404850620141d44104002144112100002040100b41c1c0d000c01c45076034040d4002c02d91305540440502c6e12034250304044a190b5114150b0440000c0c0700c00d00243d089402a284203040c0c0d03074407202904c8890f04550056441d0307440548864144080440031480201c01c0340500c0352118811417810298a14000111003616401d400c86d009104017480000c080366440c00343d4108994012201080342e8003203038412101019160401520004005002c40034802c1207440070380100240780003040900011800c1140c6409601c40c0100702e140f0240100b0001d240c20141848035104624a00000c50818289184910701005224020030420300030001840030b1841250792008090303003c0c0080071500b500003501e41c11800b0009002c000c0f0059500e0039521075030301c03445449122400d1140d5915518418030a010728822400143c6030401c9000a00300046016003040c1c600064000c40c2000c2c104102a03800e40d4081c11340407001e42d40c88482050942c1d8086100000b03240c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 24595437 1250 24594187 24594197
    0x60c0315150201050a020f0d0203060a08161401080402150c010b0604060905030106050d1109070c1203330501030b0301091209030201080a1401140102031308060115020f07050103020702060409020a 86
    0x2840d81c0190a50700004c211644843c8180700c124a007100250858640d40580d1f140140c0d20b81c4d0700e60000b0040c9249030003004d881e124114503075001043c1c010441094032602c5c0c1c42c946850320031500460b1102804c40b002500403901d02942d5448a00c07440183c80c90f01d071060004920300102c2000b00d00ea0b50060b92254001507242d070300c200101d080a101d100042d02081d0fa00300c861500360b449240d42c04c12100340c0341d8042c4941500050410307214be00010201a0b2003095501c4030060488000c000d005004c840c554036038049064003101c00030b1602d410610b0038003801076000307a910705001500241f000142c10354065407520740f004c00142089518419490301500c4e0302a20500790700005240d1030700100140310b0030385081500448062034580e210304455825804042e1842d080780100d04600a113219010f078005200d00105002e04040380300e605861400043c3d05204802038000c90f515100e2a081140e80d821a00060106501c20380080901d41d0018014a01d01aa1054440b0803a80124a0040021 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 24596687 1250 24595437 24595469
    0xc0f05010f0c050903030f070f060501030804030b07030b010e040e0c0306010914090a0f0f020d0206030f0103110d030e0d06110f0a0201060e060f0111100c1206050901080604060c0315 80
    0x70240e20407211400060315026040040c3c41010980e00d100d03014841104600104203103040043c03007044000210340c000030500280d6900c0c50180f0450300140000c88030303110410001411a4800d01c100044102d05950b0742c106890f08209200c000c003506240452240a801002401030303e042200700c0c000c01403124001843c8000841c1c00c0140900a8242c1c021500049180d8000c07814004000c0b4403240c10115000e603400d4580300081c2100304910780250040c8001c403c00c4005854140914102d070300450720b80c00d14a1401080020304d04c09068000d0100c1c0745d00d0142e01c0780d410603140c04003985220303840c00120082c03003c0b034080980e08007030034000040340c00180303180c01e599080c05061300500890f401d013503c074103003500001c00d4000408007150401c4004620034002c0d0408000000c04c050000204101905090380700410242140000310301003801e02000190508000c0340301e41c101d49507413000d01402e0b2a0399407010040e101d0300d030450303041503214103032110800c2c49088500010032810410a0b012 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 24597937 1250 24596687 24596711
    0x121a0f0a050d030908010b01050301030b04080d021608030405060c09030307110303071a2d0106050304030c0204060f050f100f0810030b07120f060b0417100f0b03060a18020609010c0f0501 82
    0x240d21f22401c0c15040010500041001410600f04250002d0f801700c080c50b116100c01403d01e000313005141d03080c002e10000141480601005000031402a0b0003403090310b030241c0c0d40030340c03920240c4a00409580c01d80c0c400c01811f0080340440d1401540200d0083c2640c0c9414866241c0d031410b000304070511040c01e0680d40900050301c1080c3d0100c680e854030748902c0c0840d0610404000c1000b00305104002c1400000800201058811030f071003000d00340c0c000c00401c59142c9a1722141440c1c5421b02a15010341400d0002e60302c5440c2140c00c882e0345080c0c90340d40140400c141c0200706c500c0c48000e841b10f004610412008000100c400800740e11440141c0e40303024440181071680c50580c0d5000408009480ca004420320101402da001c40e4281d0b80150510031610a0b4240d240d0301c0c080e002c50440da241c074580444002c130402c29400c1202c000380b0031402c446039900d5040036072040340c0d0000c03080c026031582c2074550030042c10140d000e0603603200141011000003000d602c49001c038a1417040308540d5650364007040144 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 24599187 1250 24597937 24597941
    0x50f06160c0803040617060306040b13020904050d020f01150308090105040e0705030a0f0504050a080901050c07090b0f0a14041d010207030305040302010e1f020c1219121a0f0a050d03090801 83
    0x2900380340541800302401c0c001f0110351100f4001d0b1000c1c00403403d01c000920b00029110b800c1c64038960281480000386403e04025403142050301c0140018020600e5891392001d0500458489014032882014030f1851503039400c3c00ca5211440603030511000707020025800042901145c802d60541e110941c2e40e01d880100f80d0121040020011440c40c41c010038000828030016421445590090300075541d0f481c000010b88060240280c1d0003d6480f0399040401c00c9030300398015901c8048107840b40d40500000100300b04031441da600464041442040da4400075261a07001031030181d0440340200c0c009820345c1030590990380110019000329441d00305100c01c05038244992820103802d44080c00d00c0c101044d119030110b14640c60706c00e540076000301c0c0100c500001070101c4888500b031080201d5558030b1b0304c0ba40c00ba541421100c0c007000700b0404202c07a00e0f61020360154500342004210001074890001e0300300b01c4241030071011756130030010b0440013080781c1c1c07a00d40d400e82070680a91901c001a03807405640350b00b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 24600437 1250 24599187 24599207
    0xb060705010519090809090402060c0f161212050a0c1205031801020c030d020702030c09130309060e010509010f0309050102030a0603210503040308090c1503010303030e0106050f06160c08030406 85
    0xe90300d450a0030340d1000c00c80301811b440c000d400071038103c600340d100ca0000941078082c501c0d02c01c0060084140c00030301107200040c0405000d1010305d01c001c0e480d5444c0d250300f203001c480742360181040748a0060700c14054400e00090074100350f1410f010000c80c1e0103403076201e1503030b80c07861100000c1000002480040c0c3c0c204220460210382120017546001c0d00090b210381c5900442c560420310039004504141107642c04d0042d07441e103480c003a110407003500e803c0c00248080e00d03003214142d000c500d010034041100d40c4100b540301503203041a1142c0380f51407420070045800d505500385410415990b080320f8030000f2020300080d400b40241e4180410311034190f040451340201000c3d001c00a20910310000c418107038114007680c0e0f1142c0c06003040085591707820840740c20002149803a940c040700d01000035008000e010f0145041c1c9009540402c40d10004080c01808c0782c90501071540c0c4008481c20b0520540350140c000d024118415541d00c0a412a554031103034408074a400403099504049814028154400c40d110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 24601687 1250 24600437 24600481
    0x30503120604050a0c0912020a080f03031902070302060103080904021c02040602010e03090306010603020f0d02030115120507080406020d1401090b1f090302041a0904050708211b010b0607050105 85
    0x8080201d1721000360010002d84104910144200041c00556980620b100020407000381542e00900302900741c2c0d03889034422248a52080c002501405024855100755108958190001c16680e400c5450b80c091940141410642c802c5d001c1000c11102c80304e9500d070102c01c012041025885a0400302c0181c00d4800041c0603103420740c0b0902001002c0c0e0380c00180181101e269050060395003082c1041c0f040316100f407009550f82180000700008101c1090440c412100036166190702c9120000c000590980314280d070480002862400401c020902641c010107400c808400b0001d00c0d80044111900802d000f680200c0c40555100341582c640d0802e8070b15030110902400203d0004480c140010786002800e010190042e07070380f1204c0040d1020300c0c420700d043c04200280003003040d140918244e5560b00341400b50200b617010305849620264100d030780d00b60a0048501419041041c803440e00c00340d06c810400c200c44c0a41d03c51b0039040e0b10303489003001000d82d01d0148001080c24900ba00e520910840268250 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 24602937 1250 24601687 24601691
    0x110712030b011101150b1b0307050a020f040e1005060103060f0314060a0b010503040f0224070c050108150402090a050d03050301060207060905010909021c0509030a0e04020a0807110304030503120604050a 89
    0xb06584c504040011720956603816801502d4541c2c505000031200c02d031051b07480341c0f440001541010310200103180030200784207c901c01c071184102010310064a001d000392800c60381c80540f00701e01880f11034010940c00348041c0340010b015075030f5800d04121050583d01c16540c000500c0c40000300d07028140304d02544100190740602c015030200c0002032462100400103020046407400b56011940c412070b45901c0c803041b0380309080b00c2c140c0c410501d02140c0d010403011240000301c19000070b0b065000302041403042101c0014690500c4016042c00702950009500b5540150342c0500400d20f40c1e945070161840c94041c1d642c0c90b440e90f0510001030300e4030006401550030320042d50b50810261303034801c8030071080d01c07080c3c00e015881d4040345201c82a0780e8411017242c1c00090602040020100d00000a040f01944c1551200302c0119030000344803c074171075440d00100092240c0c000401c00d901a0f4402c031800381c40e0a04607450140d998840c2411900103501440c2c828200c0c0043c85400d24240c020681c108400081c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 24604187 1250 24602937 24602951
    0x1060815091617221a07050a0e1e060d060305061602070e0c191206030305090a06030204032109080604050d0905030606030604030315090f0204030302071a030a110712030b011101 78
    0x10240400003100d002a4400158854070013004000c02e140d444205d041c01d402191400c0c641400303051134004038400c400003000b074200002c60345400ca504030b4910614800e081c0f40c1c1d10b6490188113040c0e100e0315180b00c100c0c0d1141400400200204181440350a80500c00340c0707690200400281031203001d501c1441c09447e03000c00c4c80003102102c0b048a1950106542140403606242d0080e24082401030100c143d0500d0444008141908403000f0300d10311108603a9600016192941a800c80c002c0d03005c050030b000900d121541110810340503100b81c40d0f00a04043d0490340e41c40003030038580300d4100c1d030444283d0401a800100d103500204000044c2000b200600214900030703004c00e54850300203001504154546501061140d0039010704e0300500a400c07800e02c030045144484030041d5104d84000c034014418030100003040d02c0007070504020806040c1c0518619140d1103440340140241c52240030804a041007160001049010a18910010350300e0114032404018005881c0c00c1804079040388903410404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 24605437 1250 24604187 24604201
    0x2130b0406083d0602011506020a060b010c0b100504050c04080a020d020f0a0e0f090109020a1406040902070501050f0114131d011e110a0801060815091617 68
    0x74595503c440280d45280700e4002d24080707465114070100d01402d069080050340b81e2100004000482030300c0d0701340c00078001c42c0407540e40c01a070203c1030700c6200700503000417010b0000682c0380c5c0c110b51079040b0145400e0308004116182c1007600d1800b034a19005d01c00c8030b00010003a5041a01529a10903104582641818500f6801d66180c101c0390350001e04c00c40c00032000501315940c81c69103c0556001800e0090b81544a045465020303d0541c0c140c0c81030442d040004c0c1c003401050082260180d4003501c0141030901d804005400415580c11a952001c1c0911011604401e5413000e07110041c0160000314560900440304400700b60306130000040c070b4880312030002d282e44403a8400c0078541081000000c90213402400780000d400b510388200001d50810701091a50000701c04100d10111f04454200310070049040310072594443c04925502003401040104400381c0548007441c1c0c0b2000440d01042d4034000f034400200c0c440401c1300c4110304105001c1d18840e41c00d5000c0c0c4031072801d120000759510b041c24400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 24606687 1250 24605437 24605447
    0x305071e06030513060e010b0315010302030a230307061a0306060108010b070201050702030d0309030f0e09010608090f011b030b01050403111002030d060f0510050307091a071502130b0406 82
    0x20041070145601c0380013213490000c800005a4140390001820001c031032031511301c0e030301910034082070742d1003842000f119903a00d5190941240c101c07a4002c0007001000825503994210b010503400c1c0780110403c1d45903800055809000402c84980705100000e4001030200d00006c50011100c0198065413040e0304010050760004000d0341564000d22415448004502c012074040c89450f0000790103001c6d500040da8115055046800c1c400d2203034a07001c1202034145002c642c84048003600e203500a000d1401000780d980203010043c0c01900c15019a400b800c0020483d82c25036450150750003e580e1201c448802a662500c19488911000d1030054034151454580601c85c1c3c984419036445034614010a040503030081045501460500c0c80c144a0340d0b40d0740c10312000700011445a07601440030072901d0907125100b801100c1c0701e19441c4c0c40356070138a8102410f98a0380c90755107542c1e40007401c0401007507011800780414840c00341d0230050050ba899490403200c0b01ea45000782d00c1101070150602040c09096041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 24607937 1250 24606687 24606689
    0x703120507020a14100e030a050703060e0f03031501080a0b03030a020d0905010e010c0602030709030b10090b04023903130f0503010c02030d0c0903140d1e20100212010305071e 77
    0x4d1030005020a101b50000b800d00c421014018200d100f04040002008541c0d0003820241e0040c40a545111615101494981c40200e84036003440f04001d080100c00c1d8000d413003035134104960143c0003650545c81c0f80487c0c9180d20041c4541c01583c001050174401650001800e4050030003032800c01c4039144d4800019200d481303c01e030020046900880002e0380184110148802540c02007055405410200411500d0f05018001d0600050a0840459142c06c041c000c0b42d44000a1070801c00072091031031808000c000600c0140c804050211119021340034041001d0152407220894070b611403460f002c1a082110000d44c0f0a40c002c0e410700400c01c0724941c0100603190703600c5080301c0c04180c0a80f1071a0031124031050390002003046521a09074030001100250b66050600d00b81c8581c684007100c02a28161070001a5040c0c0c001151300a0b1481400500310034460421009402c0b0740140c421100f5001c00e0781c020741c040d1000c02c01c0e1140104103121040003900018030351442050f02c00c405900c80213440c4070321 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 24609187 1250 24607937 24607969
    0x30105011e03080f0d1d0c0f01050d1a13020406030e1219090909030905032407030207050102090a090504030f05040e15061c0209011206050f010f020703120507020a14 73
    0x1000c10041d03d0f500c1e444e400c6901001c0215410041e002d030819030290b861030a1030245403207200d52460842a41402c6250100c6540e0586500e030402d80c202e401304002c0c08421080024120040f0400c40d019140c0310b0070441071807140140541c455060413001421a0852001d081d4994000111060406048400c80d006d941c485103130220803010040b400e507043c103503c2e8041d134a46850407460106159000314001c06541c012800d41c1c4580403030a024030b1078100c1402044039002c00c0b550110384018002d9008186662241c0005410000c020b070014181c0e000ca540000744054442c4108820140e110b8005464019141040c6082a04180c00750401c010000c015900d210002e5050781b1180da52402917903050300303200240076040200000b800700a90000034680303011544904000d41d020728580254030640f18041d0200107050750b41001103440c2d0715690105030035070041c1034010011981d19403003008001c1e0741d52139141e9182e034540705000a0100e594814208000380b044200b14030740c1c030f6400418070000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 24610437 1250 24609187 24609203
    0x50d0201030e07030b0109050403030b03030705070e0603010605060c06040501060605120103020103180b040303060609060e0102060c0f0c0a030f120c0e0f04110d06080c0102060907060305040804050d030e030105011e03 95
    0x712030050b2840c0c00c125400103002444007070000105800b0a4004601c9203110b81e070188084440c56040c55070700d014001c001819904540c40602c100c1e0300800009511a50041c004105184d1b070f0008a003265002c1d0f11846001d801c07920800c014070100b40503280003031000d8a429442c1c84003480c2084007002c018040203040685510b48003014921030072130032601a4000d40203040600741440c002e401404140b007000e012484010700010300d00e005060203800760006070060241542c80403010b1a45500003224110803202c00d000383c00300b181c400c02460303002c00c1c07090303e07800c00c200381b502c1c005089811034580040c1007a007890610f143d5285d100d05c80c02201401902c0b800035040c80500010701400715100d48603280e0002190f50f0b0040752003130700004216043d0708140c402c0411081c004986444d0110340780318066100100400040344268060f50744940100c003203a041945a50000782034000c000340503000100d01c1c11074103074249001e200b03660050180c94003182420484040c41130160540e8800030b09504 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 24611687 1250 24610437 24610451
    0x601031a06130212060f0f01050a050309010207050708070918020f090a0f182f0d0303021201060504050103230c070602091011060106020105060607020f010507060504062301050d020103 81
    0x3448000c1c600803440b29202e800d5468180c50540007103c64002c0301c815215814042c140c030020b00308000554519a0181d41702441c02000910a64080c0d201808030107696501300102c101080c0140202710160071030074080d2504078a00f40d40c1c00c084e00c90b4459180c0c010001e41c0d1a65006a541c03401c420070540064a5001d41a66504229030050518960810b03000d070401e50510028403120544a003514410f1b50342d2031016078520507400948401e603e285036400041c0303a01009518080c000003100798807030314025280045000c400392080e602039000c0c40c04600045002e100035070301809400d292a1234228821000003c40d84901413908028007520070200001418105110894044036401030f0013400b080000f04050b2002007408801e0882c01c0c1d5540511000880c07511302c180034031130080000405090900c5038680070400b650301031080316810b01c00100007640c001801401003512540c00780394006002484150078075903425010949081d10000d44c00140000e940351110f0701056502032030009648 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 24612937 1250 24611687 24611689
    0x2250201021504110a060507020a210501022a010911132408010506010207060206010b0306011e020132040807050a0f050105060f100e01030509011e02090f01020601031a06 75
    0xc2001c1010103590b030010001040b081c030040e030000448841081d41c03ca41401d0341c90038202c1b411300030224000d521402441041000e81d02c0003025225200110b071031085840315a549503400c90748242030608058992050800030141524250b096400d95030780203006030f801d103649543e8000001ca800c0e5103d043c900740008524a000c0d840b15501107000540424100d9000815444c40013180c455000702c1c1d802d045c0017481070352010568504540082c1c0040c1250f90030074074010f0283d000100024104038403074080101081540d042e007400204e8039000000c0e100751901d142170010b07420070302c4245140c102d4915406030b455a80280c950040e0800400c5484449501d00181070000d40c0c80040c1480213940f2072a014804190700007400703207804a0303003421009266801e0200d072444440c1e48001041ca002c14011195009400003907010352140d000055003001c0703c03010080c1d0413800c40540380302c90b800716540d41c007402c0010100000b04000d0000700160741c034565926440d05c80309403120001c40c911030f02103251 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 24614187 1250 24612937 24612943
    0x901020906040b0301031101030209060a030e0a06020a0c0506390708030705040905060f0607020904020a0302040c02030a080c0306030703080a0c050d0e090a0902031b030c03070b0307120225020102 86
    0x202000030000c0360b585a98208049058000f0300095440250300c800400d520741c041d00c00c0b034254850240c2403d060001d280010f9004190b02c0340c81182e180580502e40300003501d288000e004c0e03118152981401c95a01d400c0c0f140c60140000c040c04152034560484d60b038001542401550208940d61070100010718000e000c041e2802040d100500004001c0144040c0c5500700c1c000d0310031364001500821040d518001004019079401c1c0b205500030f8410400d09002d0300309100020b0340070f400074202c0340c041135495001c1401c030750498900d0f000681002c1001c4030095030010b03115400c64640010035045040c0315000030b4071500c4a01c002000241c00041c03080805009130740c100300d02034100040d10034103020451701a141ca034400c0d2000b403180312040c0002d050002903100d0300c541c0c580c0140040600d000c11403180d260520b01506955030511802c0d80400d202d5070708200d21b80103051940030298a0341482940030b400b00c210f45108911075401400b540d040d202039102400b400c103080c3d1a6038000ca403640c0c00140d013 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 24615437 1250 24614187 24614197
    0x303031611030406030b0112140a020d09140304081005061507170a0206070314070e0609030a02030a0501020918040f081b0303070c021309020a0506030405070503030a0c030e090405030a08090102 85
    0x1a400042000203001c1d4065000c0d6140c0c01b421388a0045061a00c0721031400c4404d6100f03651704c035031214004600807001c90b074080c206405002c1070007d0700c2c6050380c0741c138481d14840580c40c88440d0310019060041c2d50040c00320b2411804119014042c609010001402c507940c14030340d00102c040e0100b080f80030f101e0300210ba00c010081c044035032555420f910750300035264101101c0c04408a800d00c10150003048040007182c2c45180503644031908412909c08000d4140e00c000d0b40b0941c98800c055807440540e80a0104100540c8201c0005039500684c0007400200010420741c0c0c01c24050644c10800030a03001100307041403d500420046e5940c144040360b000407408004103003900d2201000b0005440d8205441d080000c0c001c407220041c0e85c8001c110170064503101c2c40025040904100b007041036051000c040c5802a2141d0b054803401c54136070001c02d10f560405000320000039442c1440c5e03000d043e0070900c4804030000607a000d03d02458240c443e43d589201e0316001000b0030926200003200200b007036043d54 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 24616687 1250 24615437 24615467
    0x604170702090703090c060807050a0806190815060a030b01062d050c0708030f07020103020c03091504030b09010606080402060c0c03071d06040b0a060c080f030f0f0a090203030316 79
    0x2c265801c040c0da0040080086280c02ca911403551031010860740d008240711445902e03180d48840c9000040e0700308694600000d041150010070400400c04401e294040304409002030100410810045021099503820080c12481c041c4240041c28404501038185d540d044d150381d81040d5042c1c2000b44404043e0030719828088030b01c005075045410070a41c2c083d00030b00001c20031400b2214a0f0307031101449900d070b100d4000c0c2c80d407542108000d0300b401035000c0c1c1c0240030785580c031906a83c1818292404143c0c00220355415030f002402c00036080c41044105510140c1143c0c01000030483c072401d001c0064001d07440a40040d100e80d00106400341c020381c0800540511410140a84000341d5031074007104004c0500000b400354424104000070840d08043c0305407055550010310000d078042c500380041d188212004000c1e240c488081045400300c912050046008010290001c00589000e210303903408a20090300a01ca260704159068016a0f00082039a400038044000b401519100c250305441e00c1320700322489 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 24617937 1250 24616687 24616699
    0x1051e040218030114010630020c06010609060203030f0a0b060904110a020106140a15051e070b010909152705010b0108180706030f0b030f01060503120702030604170702 74
    0x72610b14030200e0b88038041030010b4000b40002e4000840c0e0301c1c0500024040c5030000b071412880d00003005a500ca40301245d08504980501000403071403048180d81c8050b0602c40503a02c440c0040000030352100031180284130310310145096040850b500d0031820f2024100c0402680c0b41c0499142c6503a449044a014140042c410481c01c85407010607556900000c56035000341d440d18000180e98035508404c4014403100034655400b040c201032080e15a03aa0888070030301003000921040742c04004c0e07400c100300f41c66240a080c039100c144c2450a08100703c4142c000030001818010040002400d2001014003540074401c0802c0941c2846000c8c00340c03070400320382c04071008000c40441c410f201040d40300c0350b90b0354001e03a80c160302c0796168a0200e201d42000040c01080764000142004014805e0b44907040707135a07600c4000320314200d8101c0040e01e0b000c940c2c0c0302c2100996488104100c0c502d010003020880c12044020141044520b8000075228003000f80050b20a9000d100f600d500a010041268a0a50f0007003030b07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 24619187 1250 24617937 24617947
    0xf0a020f030a0c090f080a02040e031e040305060a1119030b0a09020c010612031e02070e0a0c0201050702070803070206031f080f01060b090904020f130204090b010915050301051e0402 80
    0x140281100c0c90700784003c505103884c0480c40c406960040d005a030703074070002402c0c0105682d081c00f0050012001c07940d04c0d400240688030303a44aa00c8584074401d11414550340d111420340c24090304265015003074204851400c0348815400340c01c801510041d05031503030803071249160702800350094080c0c0c680c0c0c0b41d41f0a441c1c1c0d2001c40c02d64556405845a078500100803c4115150812415040e10502004d0007040d41000d008480c110800340710361550480c2e2059984c000d507201104440b45c4802e90300400e540d42c60f42c001031900d503030910030709500c00741600c01003182c203250010881c1c60744a8050081d000e040008009a01c5134003961034841501d1040344018a07060351107034030984440b0303d680b41141c25400d0140000e00e0701022404d580482000411032001d42c2c43d00d600300a920546031514982100600048500c0d4451901c003503c02000c0a101c0414030000001c00105140042d4101c1e940000551020034003143e1b1210549041d140d09030780e0340442204d48c0c09480303c9290039044240d0b0003800014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 24620437 1250 24619187 24619201
    0x260609040f02220e0f0d020c06070c08060403050309010506010c03050a0f0203040b04080c03070f03030e040203040203010b03010c020c01090509040b0417070501020c010204030303140906220c03060501140312030f0a020f03 97
    0x12000404132503003000c0e101580e1225881507101c11800c0b0000f8010381c880c03071003441c04d4580b6100a1154500c40c4802a1201359160045410801d04850560100e08080100488800d00b07019041c0c1c4100d007464050202c2c41959009400da02420180c0410416500900c2c440755000300110b401400d034045030992500c1c1e0342d80c00c0d20345c0c0d16081c21401d80280503400300001e00104901411050720b616443c2c900720304010714240b00085d000148160307419902c4041181d55901c0a11459031542d28a41c083d1a54a0078280050103112483c2d10160040e2909070400005c10919040b440c1c000390f001c000f4040714041c07210030020a000f5910003a215510001d00f80305100815801882180e1081e00c040c40404018803c080c0698412220612160016400030300e9106262542c1c1c0d10320008000d07941c0c41c907815601d610069002c0354100b194501c0d500e2005001d0304010701c41d03500c02110103c000f0010b08003024480c0c141800090a030380c014214180104199114680555820660300e052482e00c13860818 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 24621687 1250 24620437 24620441
    0xa02100209010c061b1106101a09180105030c0102030c0a1506180609060b0c0a0f0201090f0f08060606070f0f05100f0c08091c0e04060e0403260609040f0222 69
    0x8140c0e100401ca0b504900c4254131030100f58039200320f00c1f102140c3c10107827411012078890000d5903600c4142d03a004214102c000d6a0343d0f408104548420300194000d0360510060500d40f4800b5410641554418000071034600030001e031681000b60f1003032203a90004440c00000f805807109170048052040d541c0c0d2050504000350b80410111400c40b82c0502c201680c82007105e02034400d0445500f5190030000340c0c03c0218030f04400015505106140400d503441d5600721b4403040c440d260308150540c00700720034100f140d032408101c0c054200703908072046440d2031580d0f903030070241c40c550380c2004007101c1c4284106402d000d4107100c0b5038404804204240001c0c060344190380024142814413070042090000456020745000030381002500e0051102105400c45000581e110440740c1c100c01e5025468050100d003d041c0d6450306801503200f6158003400703402e6100101c403200e080e010768a0340b66020700200303c00b9644049440d070304690042541d2001c0503990000c00d1a40c04a244500c3c40c01c0111400043c20036032039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 24622937 1250 24621687 24621731
    0x3020a0e07020607031503030804170d060f050406060e090a02070b040303092105030c0c0102070c030501060f0b030c040b03090a060501060207080d090b030c0a09080604050307020a05060a02100209010c06 89
    0x80c2d4241c6109544803081a02103850809900307801d851801e03410300c0013a00450701290001c4c00b4000d03482026002041000c040e9014290586425071148010403000c0000c05d0101c000d450210b5092080c1801e10030003c0c80d036213800c414140308840d082c01040c41010680c0c101d44940d07800c01c4038240b6520b4030b814041d02804540b401103c08002801100341000050030400340c0c032080d503a860514644940079500100d0308061218441951b08111050000d180c8642032002148144000720f1562300d07080c07407000d505a040d0b0005c5024441003040004c50b4030410200c2e0103039803400d4030503a140c1e00c0742c43d01107141c0040044020309c0d003498000040340d425000100f03141264841c0040740d1094903a404125400411845441152002800464032045c50500034100c1c5003190b1424100307165550002d00d20780f810503075041d240b5801c002168010750508071030300c070050700c402d03902c682c40c0c0707205888002e5480314228441c0c01c10f10390118042225070300c50300e11140d0140d000007040c003c20b020740024104620300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 24624187 1250 24622937 24622951
    0x1213030c1e0e190507030608070905010e07050703020304050402031302040f060509090f030d050c0c0a0809011e020a02040c11070602011410030b011809080409150806160c05030403020a0e 82
    0x102190008420312516100b41c41900b00218250b007100c84056400042c0801401d59001d0503258000480c0c1c807001042440c0081619400104083d4501950f001e50003001400c00780800408101c80380110780c0000445003202c00c141c0c0c00580c0da9648068203c0d0ba105840700083d842410b2101003140e00c2980d0308001d0a60310121500000c07a251100815075464903a08040d056400074007501d0740c034210316800180d0040d05000c081e07142c2a0b41e5043c850a0103060002194104000700f03402c503003542d00400300c0c04c1400c0060b0200700c580f24113400c041c3d07450038080002842162500c02845810380714a00d8007200600c810100e80c00d003500c500020740640901c1c58403400540340c0100080c14600a4400d0b003045a0b0080303421507403039003000302c4d041583c05014550841e49880e071170003100085000c1c0003040140007004001a1400b102c121002051846501440b203942c81a01480014000c0302a2800c0039800c0341050310540c00146856415409950310296010403001c07800180b155948076640d04c5441 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 24625437 1250 24624187 24624239
    0x90301050901020301050d08030a1b0503010f050105030402180709030c12030212030c0f0a110a0f0b07020f060604020a110303090303040308090109030203070b0403030f1b0201060602010209031213030c 88
    0xa1001407403401c030702092150702c3e840080e4007515400b02d10b90100441d0040e100340808114580d010901e480545041c2c0269400580004010481056207120340b03405001c0903c2c1141c82c604003a0002444080a50700442c40c01c0b038500003080045004c0d800d804019503110b0700c20b91403543e0301c004441c0c2901040d00309501500441382c0c40c003101d07419030301124890206031300c40c80e04012405c00e401c100b6801004050085c01803408465070901420000030843d0b5108101100d0040d880d0b180503420a00b014107400150b501409150343d010b2004a0b43c03d62014091310010b89802020a0032180590000b500d52824000001400354003040403004600c668080d8880701c4075903c0c3c1082c03280c2210581440600140c0080c0103820000e420881225045070281c0703000300d4001c42c0c070781c0040120340c076800c030314045442c0103602030403002e4080c010040100060f00085007024040b001103520382d144841d0304418418002107143d5120008180b2902a64015171950562505c880b12114141c41409071149500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 24626687 1250 24625437 24625441
    0x10060b04080703030305061305100302130c0e012303040c080c10020304050616060f060302011e0e0f030f0d0206060a05040204030201020307030c021c0510050703060f030b07140f09030105 82
    0x22400008850864007041c0c010b040c40c510b583c50840080030040d20007580058120800b58810b0000d0040314040c90120442d40106491841003005160b10542c420340d1090400d07844282c0d15801c541700341e02008081c00d0031a4446c0e203760558403803580c102c0f03070183c24400c08010302041c0000803194401380c0762054111004404e02004004032603980f90107040060340304000510003401c101d0040c0042640b00040c1001000c0c8075034400060b508803030b203044e848998070b0310108155030303000340f1056000895147c100390010030800e0003801c150231812458012480c1c00020f0040c1d44080211160714209101503e24402d07030901e00135100c0314240d0341a4458400c41c10302180341e02e000d1080f14100c81c0c0c160002c502d000c2481e0340c1a500040b0380f0100740c5e4048000c00a9004141c8400f00e80101c0c1d512600240162800d400851800c540c4040c14240815140100601079020b91104800580c1d0b00800c8100e55a6103401c012114811040d031100311000010035a00a98100407019160004048009007e10f0f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 24627937 1250 24626687 24626699
    0xb090309030d0314010f1203050d0f020403030c030906050408070e04110306010608160302131509150315080c0d0206030c040503011407170601021906110307090302130603080304030e010c0c06021006 87
    0x6d20150054404145006c150000045e00540043c2451201072601107010401c1111a00486c0c20660003900411010681d10b0704040c0c0c00032002c000b600980c2003031800c140c10102000e5540d005806003403110350055000c60140401486104481040281243c20a68403010010883d013401c1d50382e04844285044070462950190083e61014032003a00c0002c0150f15003124005d4001c071182d107800902110500c08580950303403040481c10040551008221011303c20481c1c108101d0b540e0211800e50090103d0348a9551801700c101010383c0c0440e841920303502c03107009442c040e00c2182c0c80070b43e1561803c0f481250700706a00c1c502d203114110303607122123100695821203001482d80442380d050060300a00994180350607591040419a8055440061042104140682c180d8801c0e511000400d1300c0081c104214134019480b04a2038008003801e0000382c2c60342d03a4507086408007400003410301c240c5408440d101d1b4440c641d4010115000300d0b03004170042d521030000c0d440d500307290803500032517040034004a45 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 24629187 1250 24627937 24627959
    0xb100f0e040812070c020907020c0a090b06040902070c090203070201051b03160f0909060e010302030708070e060d060b0616060b0102011401050409030306171c09030209040b090309030d031401 84
    0x708a4015400b02c3c6031803000c000100501c1d10041c095014010300c0101c58000d80c4401183d544600c003a9001040398459240800c03c080402d039004442190038142074403000d0711343d4002c3d1004c94461142c0540c48030b42c145401c0c1044106500310642480c804420003d007250b0540200d405074074a040c4041041081c2c0580c40003e02c0222001070700c0100c8416106a9140b04203600c4110300010301e407143c1990f481c2c0d80380300181d81781503011040c2e010304ca03c0140700350320b4180b04200c02004030a0003051902e113042d00c0f418821000804092103808998a40001d0180390b8000381030390305c0c6c0280f11a903610302c441074811a000320701109a841ca4174226080340c09500511480850b4150040c5901030b60303180404000c09080b005e01c080b0101030f220280068400402c105000700074190002601c54402100c1c0e000102c1d40c060850038040011340c11040015031030720100341c2d8200b40c110200d14415683c05818520390304c1210403080c1c1520a09410015082e07140c1d0000c1c041c01c13401110520283d82c2c8184080c0303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 24630437 1250 24629187 24629191
    0x10e1003140f0105060304020909010e010f090c05010c150207020a1802030417040b0702120705090903030106030515090403050a0201150b0c0c03010b010e1e0a0b0c0c010903110103020708070b100f0e 87
    0x17401020400c041070262070880c00c0c0c2c0760f10803840340012071a444408105420f65010900000a5503207441d507107410030800001030307806004203180c40250403107252150410410444480c08005500080e01030642d29103041c4140134140d0880c2c3c01c4600c40010503488000c1d4401c4905031104c60300d400c5010510b1b08200d0850f41102c107400421070522003e9020016074990401140b001c9106c6d01c4400030715900c56100f468801c00803480515100d616141c409400c4d110000c140040040d07150142180a60366140d240340c10540514049840d0519540c1c1640101160070440108850a40c00010400100c0c03004150fa83c40007029590452640410b040c01d8480d115009800b00710107070070401c01400e12241d012981102503022a424403180804144402841c1d0070041c0c1109001a420704581c0003084400003100007841c0840395240703103071194403010035903100361810190000354840c14441203905985005400404034200c604100c03002e404900800d1044000601410400180300ca50b522080342c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 24631687 1250 24630437 24630439
    0x8090a0209061c0609060605100207080a0f05031c150906050d03080405070e070305040c12020108040206030a0b210106060503010b0f070201090b0a0206010e01081f0506010e1003140f0105 82
    0x25a541c2c4501c01080002112150141d00400016020034003003003082c000d11200d1805070303c0001c0d41e00d080c2030034001040c44140240f001e541c032406081214910000c0c09103003c0382c00100e00303441c0700003e02d0081e045d8402c5030a00090908404d146039001c00450384141528011031254030041c9503a0800181551400e00c0386a81c000e40f59018200464007900c441c50303009108a082e6041c0c80e448192014424405640400000782c0c0c0c0c0003000100506144507001502d03c2c0b0141c507098484076400200807030802400280207400100c0800d000d502a90041070b140c5100401100d40b090703a07040c02c94694440755866051546c205240024143c2c0a40101d0781030300d0707403142d1262500101c540030090941c8500c070228100001040005482040880540240d502550260680d5454003840008120341a046450250000c00000881900301c8040300154042d911010513280d4564006803401078103210115003040d107030000803411035415407108a001c8800340350704040e07844034681d81620910074000c2c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 24632937 1250 24631687 24631699
    0x909030e04020c010209060d0501061409030619180b0f07090602060c0a050403020a030602030402121f09110d03110f0c0d110a03081306080a0e06040318150f08090a02 73
    0xd200c1c00d068004210103044000050b1a01186e1404a03c40d0352002c48000710b003980d00c00040c4480383e8448606542c41d9a40c0d030a503400d1001440c002901d40c900580700400d4000d04048207000030f01b040c1c0040300c89540000c0c0c003500c541c0340340c10500d0400c403040b10407440c0c020b111000036041600501400090b1140d50740208035941e988412080079612000c05441030100600001005075104803444020703620407180503031641458414405e0305402c00c06026a540c00c07090b866246020100e00c040c090b446e0b12440421049202d0419450101d10486800c0d0003d11100d481014035400500c408101400134045070846014a043c258070ac6d90744c1801b89901110b041c48420200d145e140c01e030341005d40000c0c00c10b60f404d84d0743c1e40c0300c021941c080e1035030000c0003030847c00070490103821800b030382c2d8403000803c82881030025141149498a400070001024008070020b0010060300700190000909480b5070144011098100050044980840c000c0005003600c0002000240f010607512035543c0c1c05410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 24634187 1250 24632937 24632957
    0x60414010c140102030c0d0e010b010807050714011d0d18050907022a0f0a05060714031b0601090e031903020901050c0a0f020306070c1e080c06090115090903 69
    0x1120a20389000c41655540b00c02d2110003a441000e02c010f40c01040d8952115554042c3c0c10082000c0d105e8402c3c10034507a9140184811040c0d0f04416115809423030b519000d6502e564521f00700c001d50120030350542030341d8a005c034001080a4142d0300040140380240450f02c41035114801151440c0344984480c2210100b42802c007d14202203009581000260042d19050b0f001d0082d080da012000f4004008c8030307400304005a02c142050b40111031400350543d0488030143c148004122035104070f00380202059901d0315448802142403080d2440e130050002d08540d8594500601035441c0350a00808045502d014000401542c0000032240041c9204111301c50b2481d9045042d0001e4000140440c1405000c200c000d0340e03100c091003050f15081c80b41d000070218105a00625150220046c5100d013406014504140850203031440b0304400401c2d44001c05400c1c600b032074205400d020741c000c814981d120707203001d21000d03001c190010001500d403c844841056903c600e04004e0b00c1d0140c034090040707101204 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 24635437 1250 24634187 24634189
    0xb1303030c061b0f080108030408031903060302060318060f010321140a050705010b1c0f050304050607050c030f010b0f0906030c0604030b010608060409080a180e07020d0806060414 79
    0x5407006a090184000207403d0402000024003840c501c41c140c3d000842a00c0a150100d0300444014050810b40000310f08140c03c114070203a60b80306008880c0903c282c10350000074014800c0e0070620146601a00194690900b080300c0d580d00c02802c4940216402183c001406000202d10602d041300d420403e1084816030b42c0c0858205404020403c10401c00c01c1011440d4060401005203404035166690950740c1a4904080d401c490100078010b01c24650038085d503c0018581d0b0344110f07010f40000e101c0402407440d2421a00d544503603445140c1002010407100f040c4440814030700d0300c184041e01a10361004c5141100c0d4206e4050420159000307400d5401c212403802c1617540264840405030446400300f0380d00000540d503070070a620403500100e601005001d815070003126581c0040c0c0507101445092141d5036482001c0c0105004042040a00d540103084103c1a5007003100404447c1040391060610f1031000703440707014240841005c01d483c3d030b0105480342810002c40b411110720000407030600360058 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 24636687 1250 24635437 24635447
    0x504090504060605100e04060f0807180b0306010b04053a0606030b0c0c120f0421020414090705010c02030d08040f0b07020c1203030403021f0e07080a0201090b130303 73
    0x2420503910030381d40c0e00c0701080d16104c0d03490907000803506851b0803901c10216020441900c1094021103000303500c416040190b001c0004185058805d40d0203203290001c90464070740000c107402207156070315104100c00003403040c2c031000040040c0e4074190b9940c03070a0400c10030403560682000b022004201d90002c4180340c040607080ca0107108611400c401300b4640e039691502c041a103800d1b07402c41c801d0341d00015100002c2208000030030440c41007010950070320b903400120b136160740118031416180101d5611108209001800d690a02039401001009000040100c402e544c8a00312050b0f0030740d00c1856804178840d070242e4035041c6040d60040003407040c6201800102c0741e0340c50280049030142500000d140014688940c901d11801d01a4020070b41c1c900c1c510104035030481d031030f005166543c204201b440082640031610380c00c00440070b1500c120b41401006131380020801c1c06100e400c64020a50042440c1d80d0200301030100038000d80c2c0e41180241c440c55851000d10640c1655980070b1420202000068094 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 24637937 1250 24636687 24636691
    0x13060c030209150a03060b030406022a060609071103070c03060510030809060a020102090607061a04020703020c01031104080114190b06031506070c0b0307021209011d0a0807060206010311010206040305040905 91
    0x1070701d0701140c0c079966150246422380054a00301c83c1541c0120304e4120013200030303a100c40421101d19401d40a0501c41096586400000e00f41c0350160401c0c0000504032400741e000c4000000c20102141d42d5203403141032114900b0401c0c00200c0d0250b0411004c91003031148044610181c90300001020f142039510b00800c0016030001ca42d00c02955020310070800140d4a03c006400001e004c2e20000c509a5a2468860048140030f210300b0301c00d0f4414051800481e038001050b051040e803c0c02c0000c2c0d012a10130f40c00499014580c803942040d0309010007440d013812200e80d1603000f0140da016400986040b02c00281c20394142c001400d401480a000050f544250a40a040b50540150401d4078200e41e0740c43d91105107026401c410414003000061008d031541c100302d080311000800380500d05100100000a0007160b103240c001100c1c03c492141036410b981d811072598000c1c80050100d400c2107540d144040d40703a0f4824032058900c3d98110751440c80c00c4d4004100c4038816689583e07002e15180c00e201c100c00c0240301c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 24639187 1250 24637937 24637957
    0x110307050f1210020408070303080f15060702030111030a0f05010503060723190305090c041b0f020f010f0605030609030309070b070303021908010906050d020f01110a050613060c03020915 82
    0x2184102446003d0b030303200400182c080e0f44040c080d40750071800e015015660243c940091403001d031040110400d0180b4030392500701002c94440369984910b00000f030141c0001d4260388030b07044000051102e0b4100740d80c0107404214401b141844a40c0e03880e1700300358440b14210f07946800308402c08010011b005071202c0350b5036400340c040c4140b428000c100e010135805440e50351407030740420760b41c50900c030101100300880c2070340040880f8240a80b0001300205c6140e000c0383c0303040e90140410311b8004403106000740f000c0d43c071444640c4000c01114023048014400303001da074401d460080c003c072808a04810b00100071244074240540091203c02d140c0039800b0142d5204038000e504050f800c2c46101804804803449000307010150391980744550501c400d1404640141e408248a00190442e10300162500750061028100c01d0910f140c200006a8846040840c040f400134541e0040d1420406e858042040103911035000d1041005079105121007941284580e0f80c469038025054070b003030b01d0105102e2009040c000e038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 24640293 1106 24639187 24639193
    0x60d0210030b0301022506201608040801050709050a0b0c120304020a050604170c010503010501081302040f0e0109120905100c170403080304110307050f12 68
    0x4050640420306464180d9030040350303000e6042c0c4080c3e100306c00003802001755241c540c04280e80048801c40ba2107140002c00c186d0030342c2c4075407001d40103000500518a40f004c080c0426000c142c002c030003100c0c1850200004603041c80d080c041c0354001c03981502c070f023000d0f54201b500b004014030b03071604000207505051202e0410028006186c1c11103441024000d0350300d07211800440c044401c00d400207500701100040000d501c8500c00c0351010603401d482c00fa038101019180c01103406110a109a900150f003040100e03100c80e071555024503100340700400004070031805003812010f03102e003200d03a8a56650f45a0240c003c0c0074211070590004c442c1071519242c0c05043c00c0001c0c0d05803142c0104841000382c0040f042c5c040010350481c03e03002e14044440642c545642c0d00d4034445941c421a01141d440f11004046080c82c200005c0d5041582e00040001c0c03042c0c114101400b2031820704983c042c41c01d00c = true := by decide +kernel

theorem cover : BRFrame.Cov 24460437 24640293 := by
  have h0 := BRFrame.cov_init 24460437
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24460437 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 24460437 ≤ n) (h2 : n < 24640293) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
