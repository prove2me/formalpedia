-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4025
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:21:45.380348+00:00
-- url     : https://prove2.me/submissions/89dd93ba-e36e-4a54-b092-41df4d6a000c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 723741007 ≤ n < 723920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 723742257 1250 723741007 723741013
    0x20304050d0c03120810052e031517070f081f090209070809390a030c030503040e0106031808090613090507120e07090915050a06050a080c03 62
    0x4021034240304055644290103211402d001d10785aa907009030100110401c100041c10000c02d111403c050b00c15940c0040400b115582d1040a1030740c90a480b904600c0310209001041e60003400d03420303000b0f81084001d60442034044460303d442d04070003c1c1d61102000ba85001d4402c01c00041303594101c6184460135030790203138010144980d210300703800c00f1000c0415640c0902c6460701031b101d0045c0c03102c625160150419444060251401101c0e6629007416803414a610a41d40c5134034095000c07920401c0d09620050603409000c020354900400c031030040c41d42c00204016410840001404008030190040e1101600d16200c142d9907590110280d4011151580400e05500e0310800040c4011340100b89071907024006a05080841c143d001042503d0352110f4100d64490040041441d804242103401040502e800c1150603004410b40d665a0214029081416500d2400406001d40e41208100d0007100c00818000b520340301402001a200d0340c07140b28040e16944001164058000c82c448401d5807003e001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 723743507 1250 723742257 723742259
    0x3060d0222020c0d0e0306040b040308090c030609010207110a0f050d15051906050d080304140a0813140d120e040b03010c0206060a06110304060f030f0204090b1002010c020304 77
    0x30041804040c566100010080024618008086001030f2914100040251000390003200c00603015880c9580181c0c802c1c2c102001300310004900ca950307150484c1c0c140c500a801b0f41d4528620350b00c8e00c030000c403d00d58035106e14410031000d114150010150240b0071240d980290004006100305404940031b0b04001844080c400c0c4001d040c07034282400d00038010132041841c1004d03d240711080724015944c000c983d004100184088289a0181200030003040d10381c04030a400c152124281e50001030002080040510840c0743d41501c10068850081d80149030b19a07603407449003049240c1c0c030492290440400100c040d600c00ca180900420300c01540100d1990310b5006240d10403103d540c683d64941354411781d1200c5243c0d0a440074403c0d080040751075001084241404000c1107018a100d500c00343c10401c21262055a9900100c2520201c0d41345040040780584820401c0e0301403d0109488001180701080001d40503c654000c50001c10782980c140b500c0d07030b0907040c0407401e9502d81601c00703001d42d0003008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 723744757 1250 723743507 723743509
    0x80102311505040504110c0d0509060d1505041e050106080105090705090a0816090f0b010203090603040c0914060f0108061c0201120207030810080f0714120f030c010e010203060d02 79
    0x180c6004251114500740d80f401d80c940e00054210707155408008250000428000880182041501421021418064200001400040d01d42e101d2044900800c6459940341c13488040014151006860024401e006d5003c90803105080c04007288803000f02da40c24400001005030080549034103980d000342c81001c2e40da4981c201518070f5401114880d0f0404201d074000500d0701d9040c0304814150f40d1050700c004017189048098000d583d02071044a0a05107450414805603800008481155405031151500c03652582080c50b80d25501d81e000006640c18071000c0d030140e00e00c19001c41d22440c0201d0f504c00240c0c1811004680e4140c00b00c880981202002070202c00004000080c8511a4814035104010701050301d5180242c1e0071541d02240840c22400500c500101c1140400c00507100756401803200002010301d45036035500c184a000c02c110300c003503c08001c544030030300e03a017081d00042e504a42880300b0001d43d840d03883c0d015a1043d00c555180140102d507292042c02180c0c066100100010444d01d8150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 723746007 1250 723744757 723744779
    0x3080a1e14031513050a05062d12101e061203090302211507031d0303011a04090e0606030607050702090a02030606070213051b0403200307080708010231 67
    0x454026880083d51303000a050441c1c81c0070f201d128040710310003c1540e0a2850500040d0039154101015001034004945c050540039079102d88a0300049590390301c0c0c1c0780b1406101e401c082010300c1c41100d881c02c100721584601c40c131021004000303140c44410440d090391500f0000100840817001030026800c85010805841d20021100084410301421041c066030880c02903c1c00d25080e20b2200164049001c000440e5054031504d06614108600e0f03216a11091801680701d00c41400b138000300989840a00c40080701d80b04c07d49001d0700d03500c00100856031140800ca86c2d40e9000321000ca200c0d104000018903d20701c61826070f0f071003070b6000d85205225103480840c0d402a40008042e140c10400c10b00036440540d540e100070038180405824009100d050000003002a410800c0c1c000c04622010001000020108044211104e50b1062045011fa03100400242001c1300c81d07122a000c0e1040d01c03008684002c0c1175004154030403181508501160410034602e0821115031440600c4060b88601009018051 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 723747257 1250 723746007 723746041
    0x1501150f2f03130905060301061a0711120609011506120b030c09040f060e0a0b1305120c03120105040b0d150204030b040309150e09070c02010903080a1e1403 69
    0x3181e484079124503100412451070300208044202200d040c80208241006886240d420401c181c4c001d0103c5400c24050f0104110400043c09041900041c20010312041044e40c807444e1030001c1a0b41e0700300d0349080c513883d6908025600b00d089540b0f080d80341500d0116060140c401c440240c2c4401d540042c1d0040d8240040040500c0b458041c0590710250426a480c035041d00e00c202d1155101085620090411104503901390f131203a00703660301c0442500d011036500809540e1003212250442502015840c006003801903008414450100210301e22040103008400b5044541d8032240c10f903d580e0341c820806c4169100c803c142038000b2014808007010406d20103098031030071200d1801600e4999256103070000c45e502201d0030ba002680c0850140f041c41030348200070784010003629003034900d540038100169034518050710707400600490900c0e180071a40190180300040d50442c40c00c40d02d03111010b00183c8601b03e00044030041d4402e880c00d006a0354026003038002803004101da80741c02c603a120700c11243c21300c800e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 723748507 1250 723747257 723747317
    0x6040c020c030d030c120f090302060a1812020a140d030b0102120301260a0305070605010b030f1611070e160203070b22080a030614030f2d1501150f 65
    0x42c2c4c0240183c6c1a00a0080c90003030016034034001132146075421700a05180c1d014102141041c05d0820816455001d1007804a400350010503008015a029606a1034121240b01c000c0c111184050885410350000c80c4203140b010701503c0c20321031103600c10012a00c40d00f070402490007543c4184014454203860382811140c680481e003001c0e1021848101c007929004030207008074001680000c2050800c00c0d540074441c014040c03c6140ca00714100b401e5250a80d41c80204200400705550056442451003080e07200034134000b20050301e0781c403510307942e42000c02402240e641c10f0300031b83c1c8900782c907030180f00108485019401c03001b9000151110981e00207030101d0083c00c41d0b42d91024400c40703800300741e2480c000c204980c0e80c0d48000511614004403200022840341c01203200303800c0350300b00820b50032011a00c1d6065000345400614840e040c0380c0c0b80307442c0140716829100e0f5445218044181076064002c0c5030b043c2c0b107102c1c00c4018003003c408011204020380f40328500000d10001c5e40d00b801805184240760350115 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 723749757 1250 723748507 723748517
    0x207060b0312030108010c09030305070b0a020d1d1b010203070b13022d061c0504020402040801090b010305010e0a2a09150f0f030206030403050d020d050f06040c020c030d030c 77
    0x801000181c42d01091000c0e8440508000004101c11007091160140451560824203085031a54a02410381e006a001c040c0109168100151400510364100c03021484071400c1040b281d91110108010504030b2070508101c0d11a4041c0d03103d103580000c2c14200302050580c01140342c9101d0303954800714010040d0418203908129400400141d6801c118000680100c1c000100b22100d00a29400400d000e10f4590340241d000b0480c824001e4250349c0380b05807604045902103500d07240c61010a00900c5660f004286551800120504000c1e620346254120307030083c40240080317080103000540b0b821100c0c03c01840c1404002d151652824184031039510081214182c1403000c0c1d48040030703002e990001c0c02c40b840e030040d00c5106014144401004c80050101c410036449000c1c1550f001c142c682c4000b6201409000c0007080e12482411141c04889120341062024086420b00402c03501c0b4402041c0c808520403403d000100300407031320000310701100c0c100060090038440300440c03040d0000c08803031f00b505003000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 723751007 1250 723749757 723749771
    0x19060504060b2b020a030b01020c2d01020c0d1a3303010b0a0609150203041401030216050106030f141614040b090c0406081b04031101030608150115030606050d020706 73
    0xf142c2e900c090f2080402c1030b03d0224042d00501c000a00b04040c0d078913007510032040e41241c901340503c42c100c40d0554054000500b25040403c000503440d0102800407658000d000101440811229400310b1900001d4800c000e040b50f1035030b40c004010680c4101e024940000401d15a1120140d4006074410f05100500005105a8000d0210350100a285c01a00208a020b1410480500c10800017104054240701450605090508808a5940c1001b01c00e040540109044101c3c03400d400d103540d02160f00130002c1058640d07034680b5440b0300040c40030541e112060b031042001c2d1003101003104800200044440c03400d4030b00702a11868240254070b01107400ca40d07941c0c64540380351506000140241c0034046203c1d01e03a0318100c0300070607454004103180d2043c6403522200302e80c404004c0945040c0d0360311407015040d800c028001240100b181d035018901511545004100c40b007065960307541a41e61b015580380300301d00b03202c40503002d0b5030061241c1340001ea4208404403200c0c000340d000e0820640700305008a003031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 723752257 1250 723751007 723751087
    0x30504030f1109061e10020705030706110106050f01080f0c040b0a0503040209070302160305072d060606140d0e0c0d1209091103060d170319060504060b 67
    0x38414120480c0c10600300708081c4420710381502c0841d40040120345d4042c0c007550341c90000880e11818001c0c24010005c50700740c001403900a000000103000003071b0403100c00c0c030780d1850002d10521002c81d940c400ca51820501040c5da00346540c0701040c05078117850b400740d40c0c0c680000700850f108008146241007a020f010119100c80b40b180101000086691389984904150041096522001e41076409040c41000400c00310b00b81e41642940c0f50381c040c10b0858541b100c50030501490003803103a5109151102d40d88040050403501c21100c00640261000c2000380e803070b42019220503481800b0349410340824001900012100e030000d022020030201a501014400c1c004510543e120040880b034400301e105040c01c17140e07400b1108000404003004180300348203458912413070510005c1d0059028214071300044051141a950740e6006030b01e500c51245da2881d01c2d200d03c009440c40c031090712210030300748080041da519040c01801c0903a20b043c03032254500041290304800300c2d41446401040001c0180b020520 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 723753507 1250 723752257 723752273
    0x54207020a06060b13050f030a02101124100f050d0201050702030303072001110f070201020c1f03140903030a0b15070c0306060905090d030f061e1d0c1603050403 71
    0x40c416924415205c8010b205580b01202194101d14021605e4004505e001c0d0b038002500720b101070701a01c05503d02c1100e00011255206816901c0645209110404035402e084813144140b600c0b9100c86042980c50f401c092544242d001d10840f01d10f000d007128103120b00d04e000300e8160b02d118814100580303002c10f690f01003070464008851800c04500040741e40004040d844501d40242e604001c0208000200c808100d43e042c00f0b8500c0d5000d01840208103c0c045900070401503542c82c90040240540360690308034440e9945010102c130002a0401c0c41c40ca040112801100b80a100008080c5003950b0300c100500009001c0c40c188103611040c1c07280c6040000d40104d004188090040703105030042070440c03c0c01c4007607503070076030100b2251440c02040044903040800c049065028500d0080741003601d000c0f254001c0d00701c541001045403401c0450070f00103030341c440250007180c0b0510010780c1e2151b0200d21105042d1003c844101044100b00107440d8041c3d011400307090120701c6400e000b030505803651070307400d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 723754757 1250 723753507 723753509
    0x100e0607060912020f0f0d080601030605030a060b15270103021306081e0402060306011404050604080f07050d030903030305040503190f1413030f060612054207020a0606 74
    0x2070364120320f500211140f0781c1800700c0c2c0c41951000c07006211840106d801075503104010289030301000507801c041200c80c2e03c00d81000000303000090460311450b0860401c1c500804480c050b551042d411009140218000368082e5040030201240c4400d1030203d10080c082e0030520b5940e124109507080000044104810502102600706036803103085502e49100d004002c4400490b040c04148022810000161b0f114401c8a03030040c000e180185503503110700d40f0000a4000da800050780b125010401054a0900081c680c43d0000c009007200d403c03650b0351050000300c8184010150000b920181c040c4040381c006d401040d003041c414401c40385000725200924504001c00e9000c5400909011940c2e01d5031944000003180d000c3c2e41c0c250b01840c0400c408061007064000b0700c802090072900c8100001401160781c400e41c0104111450b13801c4010b0340b880e2070b03602c03071000a0001c00b100d5803010b10078030038946550700000c052001803881400144070392080740e4542c200034440000c510445042d480003c0c42d41c01900 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 723756007 1250 723754757 723754763
    0x9040b010e1507060b040e3f0717040902070308010902090f01141e04030515090d0e010219060204030c090605060304081b070807082e09020d0b1005040515100e06070609 74
    0x10300318503046c0623201c50420b41240d90083e0481d209124000c0b0010082804006848608181c4e11002458a0030b1414411050034492103004a00060243c500f40c00030402a48681d031516101c0c1e07203d240410813400380003441d54000004004c201c101e17500801e09012030003000c21780c0d40d09000c4404001141070860400842d04100c01140800801000300000c000c01070f185031045042e80b4110b41c1d107550303840e058a039410801c0102d0062817841c2c0d00900c1760f10380c2c285444500b85032640c11070030402d005c1c0d4050700c402c84850900f003200081450141c804d00c030590340014501855a00c99845801040d044920b500500b14540304250392803e100300003140082104101a2442030300d000442410a4100f031003003091801c06941175544140c1d80200c00d9110440e815001414441c60f0020580c2c03100410001481c00641c2003d103d45d240500c41500121032044a052007580e694181c01c0780501c8518202a400c01e25414030fa140f0b01c0c0c09860301a010b0b09018003101d081c29001d8513400240c5104000603 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 723757257 1250 723756007 723756013
    0x1207020d140102121608220804260a0b0703021b0a060e190305040504020c010209090c1e0a0c0f1e03050304021c03020a1104060506070809040b010e1507060b040e 71
    0xa2050fa0201148070b50740700d00f4a02451031950240000070b45a81c80061140100c200c008070685640d07000851600f030159000421395072172750b1302c544641040394602c500448800310211042d9221400006500750800d41c0511202183d4032064003d0300a904114240d0410720442d0000a00048040198800090181e0008100d010f08102282c0c2000010381c03401c0703000c6504909084c0400d80010403641120020340703005a40701c81421801d030090044602c0036501c00022803d0111000c2c040e0b000d00700c0c00a00610460b42c1d203544804c01d03205441904250744c0401d0100d40c9200c04254500710010b200d1b0300960320a24420501c02c1d6240d03650f02c003000d00300c010030f4000c402d11080d0705082e10980f40602011001100c0c55507a030302c01a64030883d2050007010921400300810032a191030b04154000e080282544d91503203c10311300318034030303801000c90940180d1030816904110b61003040380c08004078024254070350590711a40c0e0031034150700440095030324030f032140d072291400e442d24400c0c40918154400a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 723758507 1250 723757257 723757267
    0xa0b040605040209010906140c071205101b0507020102010e031c050c03071403040524012d060c0302010603080d020c1c0e0f012006011e081207020d140102 68
    0x41104454407604018000e80c414480d220740741c0d03003044580081d03880d1810a0700c280305007505084460b1080080c5405540960000040d801c082500c00c881e0b082d02c01c2007547c446489194007001124030050f5041360000c516824007050724001c0c00182000d0f4018030000c1208001c7c1e506a81c0366502030b01881c0c0d04000b42c82504d0101e401d0b9841015001509402080e14609080000401c0d03008030010b03062a040001000c00c00f001420004ca0010042254440a00300003001180d000d42c5001d20035003501031580c6145d08221406408502c0c40d1841039a00880c0301c50901d9411112a4400c2d94120305642d40c6902c040007182d040000f40c5401c0b0032804026a540400441c0c51381072501c0f007200c1d088803500f2110081506234000c813815a00032810b48400402c4400c5100481d240940b90000b04446901002c48012030200411518141e9090150040141e880818103900c1006603204a112680106051080700c110110003001124001040f07a8002030080e240c500e80c0d40308015002801d0ba41c0052 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 723759757 1250 723758507 723758509
    0xd03030e06150a060e0907030e0a05060c090108010504090230010f0b0f0105040605190525060e030c2d100c0206060a150e0613030303060e0105060a0203040b18090a0b 73
    0x1007843e0181580345000d07140580c586003c5468464040c0114080c5521600f00300c92458080140000b4036400c042140c81500349089035030415445060280c1c00203041c0b034000b01c2d41d41404d0056813070b50750340603144450b149041c4c18003080755540080d410908425249202141070000d009005081640560000b401c0d0654020403001c0040e0b48821410700000380410407a10380c101c004d4415403101d14450302c4c171840c0f1944003141c0902c149441c100900c0c901d20520601c8519401c0449529481840304000129074052140c0c2c1c2e03801106c1102606900421441024050040303041203410204a030140b548483c1000180c2000c1c03c18500c120540d036100b52042000760f04201164225005550a81d1640e0616010204802c0c404200c0000e11010b0190003030191115411104001c140c90049200c01da1070b481c0040c043c040c0b510034507c161900400101d054038281040360700d04100303034008600d42880d000003502640c1111080031441c11002c005c07100c0c9500d6180e200b40c41048150340c00200383d02070364 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 723761007 1250 723759757 723759769
    0x3071211030d0908030d1e0f1d01022b060b0a0c03080a05100303050a090317070b0c16020111070b031503430914060102101a0d03030e0615 61
    0xc210040180020f410008120048100e440b148802c00c1c01080c101920302c00c1c280700800c400e005206451804551068004565001035280c80100708440d40c41403160803058240d01500c4990140c0307450217001d400c00030211101001e148801c1e0800400c04950b24980107002c0e4200032001c81c08503850005601c1090351003219282e218002d100e080200c4e0510020304e582c41e00043c080142030020014500e0b80b401d000b04103000007107500866a41a010301418000160740010714103c5075195040b02003908480000d013034400c00200041030020704044c6800440301c94510f5051110747d40607010b004070341615401700851055a0705020341400810201c241840c0c520207038010f26a50204030304d24560a110100b50111500088070060019611000b01a5140f41307070f54081c2c803900d494516904880c444100c0700d00d2046000f40c00796101220102003038415100700358000e04d01c0c1051030f4411760182c0703060700038008010302a10340040c0c0c4121070703421b092030000140c6911408181601d4004814a420 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 723762257 1250 723761007 723761023
    0x314090d090308030a1409011a010c1e0201050f12040c08030913050612031602030606011119060207051b0a050d1104200f040603050c0c1b0307121103 66
    0x2040050510500d0450001d10540e40d90000801500d030010124007800415084101003901d42c84a0b05094100a180766000300b8801e200c202c1c02c50440088410f03550300800c40c0f001d0341c540103083c0b900f0045c1600108561000d03400030482c10f0010a2001d5080041420b01074826400071341c0b001600d60401d410714888440c0b241d885000c103548104000012511500b103208100300041c2004030303413a185c010011709051919420448940710200d0004907000441c40000b580c140241c09803042600c90100440320320480281042d129400070000b0049524882901100d85029610040c240306003079071114208250f40c20f10544c4200702c260382c1106403030909071882c0140400c0356014200c21140e42c0f40250342c0b10920246100d1581d030a10b60b1880456690b50b070020010f507250143d5103400c4001541015006405000e001924080001d480e04941a0840d1408054a070080c01c400c3c001c110503405412480c1d521540501840d5400200305c0d400e04800f02c941032041e80800f160f000d5403c181481c10002c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 723763507 1250 723762257 723762271
    0x20705100603110405061c081b0601060504150c02090c09130b0d20190f061407022205010603020a02190f020d060e0d05041d0108070506090307050904030314 69
    0x140c107104000090080c0c5611400301400c4d100464141d0b10b5500203401280d030048551404c0c031b04e2221440411402000a04916902c031805900c111540e100c0d040e5140c1003400b62801180d0100000d20080d040e0000c0d0700106509481c090090311f640d0341c00b044103e0700c1624044814000845c50403aa440d03c40030b05207848841060402070182410006040e6a10350b0f20040c20f80200c40c0688007400c1c008220f410a01170018103011051030400018002903030441c840c135202c4010009000c20b0302c500c14400501c0705901941c0c01802d000c4a07408002c900d440c00013005142d52030b41440304980b000316003c0c2c94000e0410745c0700161186462100039003060140c040301440c000f07131400b00c0c03030010b4030300064030703c500790140c0c5c6048c00641d0920b4000c0040243c5118102d1521550300c1800400e5444401081a01c1c040100b4070312201e0440464070402d00c080c041c40807140c010807414056414010054505150300500301e0350107030746d10008962142d5095038242c0010f9202e165200034a00340180c060303008a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 723764757 1250 723763507 723763511
    0x1d0105070909021b06040809010f0f0f051c140901061a0a26040609030e1816020102090a0b03041a070c060203041104050915090c0d151401060302070510 67
    0x281480e001400c1c21064002c54442e03660100d00c0416000707400c83c5800081401e10300b19505401c1c40d0038040d82c640c100c600c0706030015410304030000d0182c1c480d480160400b9a1501c4140c241480003100303907a65000141091915007000320440041c0c001c42c0111168004a81d08000103810801a024203403a02d980140e0400340c0003440070b10b0400c0e01c5004541100c074851410a082501c090714000d140810f140002942c481031070140000d1213165032001d90154425110b0240c8000d0440030300130020400b0420301f40c0314408500142c4040c1c000700342c0711440503041c4001442d00340f9240008241d54180d410490447d88040100420410315041e0000324407d42031074024a880d0070b880003080b8194041c001002c060b008000310307081101c00301e0250007213500100180b10f5803800b5990320b55100300b554500e40c04054014085860800c0228148804640281001110268030340f1114415410908103c100c650707140400d4080b2040018002d010785595640565604468140189814410155041c00d14 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 723766007 1250 723764757 723764761
    0x30905060108030f090d030306051201020a02070e0708180705031f050109020c1c03020f0a05030402090705040f03020f060d06170f030406092601060603020a08100302060f1305060d1d0105 82
    0xd12011305441407841d0840340040318246510b42280604030503481940c100707000ca008000b0904040d0040d01008109600300ca00187d0380d0034110128100a450310004079480300080764200e22008092200d01c4001021501c0d01c680e11030129203000b900194440340c3c5160080307000b030b60103454028180102040f03030081d818485c801c01600d031221202c82085640441c2c211240b6841c034001c0d0142d41c070000d02c68103941c3e2188580c42c2e014005030301c01c950880c41740380700d20002807a245c002c01c01d50b801d50703451701d5500c0591030450f070a02540c4080034801650092060019500388030250180c08040c16042d184144042e40d01d02c0b0345803800e030700c2c59401d0365603820038402030000541c810010000c81d001e80400034449070b41200d10780c250031440102200319509041d0040350098240d00100001d4034035544e10038142c0e440c0754041142c400c050100079440081004250754501004000d00542100c5c0500000076a954900280c1245e100c104802e802c10788407512a01c4480031401c543d90270301b0b4540300a20142c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 723767257 1250 723766007 723766027
    0xf0d0803091e030c0d0f0903050304090b010f0c08090409080903010c020106031202120306091906141309050c01050327060103300f02071d04120504060c1e0b0703090506010803 77
    0x98503866170440104101c1d010400b007000c1c4110344c1e0000841d0000192580c603a222200000609080b902580c0401c03070326401d0f040f03524440c0d4003501d01950800011802c00c00c10034100f00240603241025190351009010149031740c0d40a10501600c9401a000007034490302d145094042c20885410420a640021501c0d045803a030f403408803075004500b268007202583d2509444040c840c0c00c0829998400c1c070701070b0041130142c800d40c0d50050100b02100c010b658108414034a605485001c00014803e4001d00c80c2d8082950090015541100700c03520302520380407560703002445200142a2441d481d81c8103000400a004000524040f1907142c00328140c02000080d50840c0c024880e015074104215400ba00341c0c071224420311600016000b4800d28104680c4504a40c540e421802d441c140c4e00c031107034089900c914500810803a0215503254442d100110450740340c2c45120040303401410300903403065800400140902219a12513000ba031000584030046007085490b00d41c05812244040e0300400819a038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 723768507 1250 723767257 723767263
    0x40b03330d030c06020d0b090c040609031205091210051e0601080603012003100807061205060301020d020301030f03090f06050702040f060801111e0a050301050f0d0803091e030c 78
    0x111406441c1201c0050a500d002c50b141e190140e805408180701041d450300b10f10365600032040041c4100d9407403a00c0d031614404072580f48182d101d540089010030004000041e07510200c90040011818428107148400000c54800400800440f105802a44141101684e54403034103410584c5c4c0b0281d0301c155400350b80400c541c0040681402c0c1480001e030000744003a90b0035001030064500c4840300707803141c1c1251189001142c005a503d103841d85034485000c04c0d810000513020f011141640d4032507602c030780c8000845000b00005002e070354065400f0019002c1102c1d05000850003584200f402d9540702c0c03001d040050940d02c1030707046003400d400c508404021141e80901540e00c00743d0110390005042150902c064000c1c940741d40500c0c904e50900407010380c90182c001c060043c11b04a048140d040081c5071110100c00c3c03240e5441c0b0000700b002400103021504000e0000848084060301140402d0380649500c0e1060b081111103139075592040c000d0b8060715050302a07812162255000450038103001d08400c6072 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 723769757 1250 723768507 723768601
    0x4150311030f0106110a05030d1e1406130635010e1e0106050a0f240c0816020a0311030d0201020c030d0c090b07051b0603130201050903030d02040b03 66
    0x70801180f03900c0b9005080e8188841b2840651101c200c990303401c10359455101811030301c14802c0100d039100c0446c00d00302d03461340140c02c468a0b44d220072103040c0d5611020800f443c2c04182e240500303207030b032a0400f09290381c49110645c603c24003640001200480b1001e107084943d00ca44110b9460f074140b000481001c800060b00402d0020440f95a883e0144484001e038014401c43e44115444918510000b5008603160110801d885401204070461007840124000e031800c00c107040f80000f500400c0c540d006c144040064454600100c215041011140d00003c00d20942900180c80805079400c0440452808000f0454001d669000035801c202d48052419281d00440346044009626554059456803080091401a20300d1228064031401a414565aa680b00394103500c00c0c1a0b1b6a0200c3c0c031140307030031001d580c03041c00041c0c0916205c042e40d50044031550022521a500b506c0705204103580d6550a00251000d041803450840d200e14100350001101d003400d8000e4040044000346420301602000b40c2d00c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 723771007 1250 723769757 723769769
    0x72d02100f170a050a050739060c0f020d0f02061b0c0a050a0507090b101202090406080f10090b0408130e04080307090e090a150b040204150311030f01 66
    0x76205481410180d410011403801c04040c15203402c00c0081c505034950007180903000c0c4400c20000c6549043d41540c15240740c1c0029144856100c1d4580308540b11025260310346805090a010030b100c065544605840e0402103d5000c544440d080b41d80322a0b0400c04128144880d00e800e0705001c12406010791a500c0290085020001345410401e40724000401c680c4500d0314030046a04078051402c1c22921280018801c942074021602c00003100c2840c2d004440304c1c910000c0030b0041041000310255030308964012614050b0780c00384100d84480e0740314400c0c00005c0900320050103005205060490030412040c0d18400b00c00c0c649403424010480756007001d42d1003035025420680d07403440d000c00034101503001c0d48101807404082d000c000803c264a8041d50050f4510780300c0d04600d680b40c12080c1c03a098021075100d03e25502418a00000c51440e582c4140c003c0041440080e5154580004c0780c1640c0c0300b038000e101e1400341902c03610102a4503108144150114a844a04504040c85003c140c140188600c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 723772257 1250 723771007 723771017
    0x11401080a021308060714070c0510020703120c03020601080d050712050d050403030b030c0103050405060a20071a090106050a030204240e0712050c0d0504031103072d0210 75
    0x10401c401690445420344040d03d500000540d0b103c503d599901400c8409000181c8124100100041e11605641095910409a11645092009001888251400702000c41c2300310710000010841440c03005401000b41c0d9030b9400710f018181400391130035a040c0e002c910705078440202c08045aa00805950146a010504800404603e10116024098030702d40260191405e0180010103405500841d6075600c141c0640c3c3d001540c1d10300540813246c00f1600508140c00820024032411410340c000440035842903800924420ad00c10340c10855009110102d8101c801000b00c00c148254032600740d940211064024422541080080354034440c0e40c1c4002402152140b10b1004000b080450048411079245c0e00060507a5440082e00c94412065800700c001c81e68000c025881d86800340211480b590b10700c6e00e83c40c40c0041900700c48000700701c01003058003013048904d08801c50a005000400296000d006140c0c100e10515800c900d011404032844003514813400e810a00580b1340580d0b810b0504110300b06 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 723773507 1250 723772257 723772261
    0xe13240812070c090c050409141003241a040b0901030c060c2d03120c0c080306060f0c1501050906031c14070303021207051309020304080d0903020c100801140108 71
    0x310301080f002d03803c00300040d41003c08101c0050707031000244c0304031422407000b840b980c114010203401a04080d595050104411602030011407003c0c0380000c80c82d10490300f035404a004011000f03084860039402021640300802c5030000c58600b9004500c0e2865080318000c102c1c1d45107a42e0205000e1540c07046c1010300c4540c54003c0188448510420410301440d0341e40d0000380c10f0004040d8048000603800c60100d1861b45005201e0000c520480034109030070307141c00381620f1a580b05c02c0e0054000401c6154400310400c00e172801e03600300f103019012519a0500801e010a465444c03e101d51005800003402082840c08000050b9400a1503060141700e0120060140102e030b0404c41c0d1403440e24100303100d1603800180100405501d82d00501c003500c0c0014654107a6180d024084901c1d22584c2d00004001e40348030001d00075000710b40c1c015500940b083c860300b40751016070a52001036511004042c1e000da000041881d84a042c00c140405419035141b4100b0150747c107080c01100030b0940c01074aa8100952100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 723774757 1250 723773507 723773513
    0x1501050403020a031113020301080a1b032307151403070e10020a0b0c0f07080a0c0b250f091712071b08011a0609010e1324081207 57
    0xc540c06190050b21a9200301d40707070306211082580310310f02a4060016000140304003031992007507074180c60190000d0902a581c0e9101d42e403008040700c008284035100c12900000095010214001440d24103d40180c44142c0c021294100046580f005400b01c0c1c4400e8140c0c4072950022001440690250741c0b01d84a03200d44008580302c0d4808070100382c100510ba4402d8012603000144071400c03d11640b54080c0c0e42d0341c2e403002c90003103020720fa0001c084550203225002c00140c120002d0710038103100d450064845101504c40c5091460181c034040a9804120517030001c1c0640300c5541c4100092904088604400c14200184500114400c19500c110021081d456035801132081c0c86039001c0320924107448850700d080451b008900d20300090a005a00c00000840706418065400346c0e03100c40840ca1201240304042c00b5003603016803c02410841d00e40d40c1c60441e55610f04951055012a02e40020326039403002002c192040058240482813009200821103402d0001e50403030f0901d00d130b403c003944030301c42c900d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 723776007 1250 723774757 723774767
    0x1d071d011b21201c031e09030306030b010e041703060310021801110601080a1707140a0312150515160b271507090f06020307110f03061501 61
    0x8018141241e1460340a00b204540c010003400303560180400e080205000405501c3d0b544403e07220110304240d11140410306036003c0d620104074940d6201c11100d820700c440101340201d03814076100701c01190355401c0030f03c1400340350034209016051a150901c8107081c1030711030192100004410042d403603030020004406403014071050160600a0740150344418144840d1070071070091050050024003001e44200001c9000a0118100d507458000750424080c0354850f0a40c0d0260042035100c050010040d10307001070b918403e90300e02d444e024009020a0307920351070010b00c44900c0b1007002c0299070810450200344444803481d00201c0e203003141c00d14110101030310703401c0c103a0080c0800c0f440c080c603482300b1500030b110b2690f0404e03100780803102958096104400045007880c0c000d081d0040c00e54030102e4503c66613000e08845940114050030030094140d0344501c44032072100380360407840c010f030404960002000342c80e1400c0d14803900100e6200c0901c044080109945240c02001ea12203400d0303000000c08207034000c1d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 723777257 1250 723776007 723776033
    0x14091b0a090911120d0f03090302011e090b060405010b04060c050a020909031201120b06100e0909030c071d04120e090109060303020d020a02091303091d071d011b 71
    0x30052040980b1814203500710b020056410f030081180b040801d4603004041843c00d01a00c0c1629002d95440c10400210001e0008080803000d40d961059501008038900c14035030050000b41ca00031810035801e10308800100c1001c0c5c0014000c0c4d04100040c040050044161010743d1000d2030012024400e07414468940b07840d80da8044e4002402c0010303c002c082003c401004071503607074141c07490281d0381e40c0c0d101c82a141490b4009401030700100c0c045003031461300b62181c103044c403810f140c0380403065001800039950510035140c81506510000d4030036500380d41804600018101206c0c00c01e0100d40c2e01400740c413038120040009116602c003240c12802d40d4050f0840d1a0904030141c002c503010368540000100034512400300390003500c101902c502c00f20348005400000300d6405403105200391100880782000b40d200030411000c0c03011414000c509014802481d020001070000c0450460410070320150181c8280ca0036a0741031111031800340c07103503600300ca01d5010b200f42c10312a600c000c44190410000030008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 723778507 1250 723777257 723777269
    0xd180c05060d061a210103030905040209060c0615190f0603050606040305100c2d0516200f030327040f05041104110405011209050a17030a14091b0a 65
    0x240701400d0a0382507840c1c02810002d11018102c5c00d03456140036424000c000c09200060000780041014000f0341010b8025162518000c0d00c10350030816986040c606260046071001d50f01010000d05100c3c80c03400d20680b103594542c0110306c0450b2030820042ea600c0d55100c2c01000240340c0c5a801046d05034075074070101c900660308803060300c1800003c1d180000203040e40141c03100c00600414103002c12000710341031201c0003403840300c50322104486100c0241d8458005440300e6090607800c10804002c17890311064501415818001b090003001d0500410001030344a501c0786008e0ba100303225208010f0402c1c7d245018007408091007496030a414000500034020681c5a05a42c0381480e0501c0304010458902c40d5160314122414448a501642604200e00480c414540018103a1034580c0c5000c0c00c650102d03846c640240706881c001030142d01c85101032440d4202c030450b180e900204000018005100304d0400701d0b1040116042414004100c039901c03510480320200000a012800300140d80d001f402c6402011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 723779757 1250 723778507 723778529
    0x1101051b070f02011e0f140405030309240409090c080c03060f060d6b150304030f0309120503130506090c03010b270406020412080d180c05060d06 64
    0x1070f205c0014552024584418003284060417884580e0f0405000d0728240ca40c040d00a41c20309240390100900442d48a41884180c0601043c0665900d4898001c10103080b01d400041544010303031070201703030840031a0710001c4c03e90064251002c0596011411581001c40186000815265040003500b82e4124140040615042d00c0d03e40d80e100e110303208a01e000d076031441c503c200c680741c9958009d000000d5540345224030008424041d441503602c1c2e541c0d00c0b03060162150400c03500400c48045100c0040940005c8141a000301c104030400da44108001c6003148180f03014000c07191240e6030351440c01d41c21000c0005100001c0006598082100c0954031343c4c0303401404030b0703449007400114942c803040e100c19020f00030350070201010341d5410f18445198180410307140416000c0f0004c07107150640c03007000d4003c07503c0a40802c000900301d5038040390004440e0080c8250366442414802080c11516045828031815406541030700124003800c071244d01311402910030b196070701e03a003028500040040c0e40180c0d148003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 723781007 1250 723779757 723779807
    0x10050f160e030321060a0501120e0c030f06061309020604050f040f0c230324060403142805070b0f071b03020301050702031201060e0f101101051b070f0201 68
    0x80c80d21110b00c0c1002c04c1c20400d580c56112901400304500140c003800f40403940e00090000a2000740e0700c034048541c506000e4503070100c1040002414101d8050585c541d585c0064240301c0c90380307000109480c403d4100e80c1c0c00c01012a056001c602c41d809103120b0340c1e100b8227413201a80e0140c0c03a103412084101d04a04010881c11400e510054070b0b0306d0940c085241c80d440403c160082580e8a40301b01c80c080c404881094517900c0c400f440724110132826100d05070b0032030000e204c0000000c181c81001c405a0700e01002415040c06010905001c62138000b881010040c0d90121800101d1030100745042510700c40980d01d40c0e10070700f6413040040d51055150040a40f40c0140c042603900041e5010001600d200704c00a00c0b8503150814100ea580c004d10120300481c0025030010000c007030146140d002112405041b42032914a0a400100380e4183c01da0401e010031042140914105000c7c4640f542c8146651600c03110601002021505030080e0080180310f000d8000424065a0064000302c02480314021600009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 723782257 1250 723781007 723781027
    0x108060a120c0612091a100b03090105070807360503030406110c0f091602100f0e010c1412040c0b0403050312070c1e060605030304080309010210050f160e0303 70
    0x2c00302445004002401200107511440c002e0040760805034000b02c0c0300ba40200069126216001c006c0c000810385401c8200c00100c0707a075110007841c81201207500002d074628040303030040c00c0c03032030018491020408206102c042c1c8050788260b10020210358142490580b418896455600080d86c000039030511011a001a60690081c04280c0410380c0d14142e0300c90180310418040080811300440d580300400c040060710680c0d100345c02025545541c41120360103c0005411406c0780c0c1005a1440010307214192012880024011020305040914040c0c5110415032a0180b0034014041c0003621145da03400840c0c01d12038000740c7c40011700040b094481d504d1360350749056617480c0d1002030801e00c00e845450019151500070a0050071594000e0408807028290108000010350720103c1283c000d0b54039180443c1613241000640050840c1d00015640d6481c09000a4900b2210033546c4400b182000100480d440b44815a0780d001065081e130030b40034241c0c41d0000d4480d2120640b0181e05448081144035407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 723783507 1250 723782257 723782273
    0x9051006050f040e03071217010909111219060b100206010302011d0d0312091704090e01061a09010c1a180607020a02060a02070807030b0f07080709050108060a12 71
    0x40707640880c2d49070403400340c00e018030050350900100301e5802d82040c00400082141d111480b440342c50a0f1520800c100030000c0d4818050b403083e044052030f5680ea011349000c104a00020114101c0b045407030301540101d130203006540d200c5031594034001c524560020341c1007060f07541044034080801080c0b2610403441c00e400960b40c2030248000d030b000905040c10490f03020052544041d880c4030181c0807103041b504503141a144030714060010030845948144000c041005041d500024001c4c10700459078a502d080b283d50b050310860349100116915112040040003a4102c2c04008149000c0486803100c02080050398000007101c405001c400070701002e45400e480410030180310381ca0707581c0c0081207036810101481e0f64003000c654440142c1d00c02d0311030202502d07006001d026070184d248101c58485884040590522120303034401c8648106050601c1200d001807003455034011894134050802d4035103c00001c000401e684980c6050110700004191181c90300c10401026000106003044d4030326042c682511 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 723784757 1250 723783507 723783509
    0x3061407080f0f220f050f01060b19030c05040b07030c051209180403030e06010e1b0a05070611040b04090213050d02060a0c0503040e0c09010305060103150b0913090309060e0306131509051006 84
    0x1403523500e00400072902075070481c10f4440d04480310800761112414440203038010314150032103105024040c4030003c0d00700301120040c0941c0c0d00c00e84d255038032160780c2c1c03900c0d52900d42414110190540d0901c0311b6051610b40601114442d08145c629007240c0e00c513410b054009081181d0f48005600601d0000f18041c0b0f0000712640c0200d40d0300d8501c41e5400481e0001c841103024011010001401c100815030100381c00f074200703154900d007510001d4907090303a42c2c410302c4040c1d02c607601c111030961700807a00c0300e00c0c040c22075250f034010101920107680840c2c49a00281d1588610b50343c060a2054048000040c0841082601e0103030003903011003803150509480f64902030700f24407201c50001e070038400011003035403080c094842066490414082c10780e04043c40c1900c160082d0900942060306800442140b01c124000c90014074040e4554007005801d0100044c0328640505509019034003401c2404400c85280b8100c110a9410003104400030301404480c0c00644240b046c098401c1c469000d241d003960241d544000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 723786007 1250 723784757 723784783
    0x18380c031608070b09071a040609050402030402180703061a0c0a0b2a04051906080106030902060d112701020309060a03091203020c010e210a020703061407080f0f220f05 74
    0x450041e92144250f04123114601500b800102002c20400c02d43c1080e402440d0400e2005114004204c86000b00c400448804c490b0303040069201c450800a107040b10781c004940c20f200c4c08115152422507481d1039500c844203000144810b44800002e040119440500003440c0d00c0e00d000070806820002070b411158016001d164840c0030006800c84003290009840c4080798050303200e40d50140c0ca40b040560042100c040c0c01c3c2d801c200b082020400b495007501c62001080140c401654413000d040c41d1500311402c10004140e0031a16041c21918a80c1e00042034038071700c0100721241541c641141404401400007644001d0581d0849510415041c0d01a0050888a500c1100801801c460300c1591691400414003c401c2c0314407014480c807454003000c0c01030171000000e00407111081e95981d039201c1125849001c40711980540014400030355404000c981d00a002003900074400e0404030841c5590210207824000c05c40300443c10040d0074003041181e026825000800e01d1540c1e20300b03040040d1114080c44481c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 723787257 1250 723786007 723786029
    0xb13050102030c210f0106080703060803031906120f080304110429040c270b030702010b0103060501261801110304020910060c0318380c031608070b0907 67
    0x413030911001d02c081d1911072100740c6402ca00c96440d002c010b455103040503000b03404142e21030f0310208007810200300441c0280c1065849083c13400202113800c0480d0a540c11494019010542d103901041080c25020306c001d41260080d5602d403994030b0b000b40c44d001e48400c1d00c0d42040c207000c40c0c0403842200040b005d40d01400c84d5000c1e41004100002c01044500340000e4a000c41c020380d81501b0380341d8408ca880301311071140b000803031095511a420652940c00c11900710b80140c0d101e0132400c07195641801403d004110030300f080e14401e6030b030700480d1051480355409541a0401100001c9440100030743c0c0d0030750310080000030040c861070600d0f40042c0354001c507070589c001c1d00e0000105080301d80740c54501040b90065980c205111510303035401c4802c0a0000320444c1c0c15050b00001107408100b5141940520b0440c2050101202004001400706006044c581e25140801d0081c6210600080f0466240840c06010360a12407038a1911401074001ca0781c0c003030210260704d003c10500c1c210024508003515000090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 723788507 1250 723787257 723787297
    0x40503030417030603120318061303021203060603070f09050a300203060f091609140714090103020a03091a010810090c0e0402030a060c05130b090604030b13050102030c 74
    0x602c940c4002c1d68120341543c041e6890031040204800a0b40d0001c60344000e8004080381032403024540276007561960000d070070082c444010140c04000003c0c0c2030724861034860451801400240903400300501900a000381c03000c044003103d20924aa002401c00185070110603074403440c0d01180e4a949904007480080044042c030040e030404d0a04440395640240104a0b0b40d40b405125050200c01900c2c80220b032190584c091070074001514940041d2900c1c660000c0c0c06070320b1048013420480e002e040710007401610036100348010411811110511400c0c00e0140e604e00062008500070001544e0103010b1500c00c1501640f90029000064100c5031584100d89500054580d480700b11511004010701650501204016111910060713680c000e000601b1ba1b082c1c1010341c1c84880c1600c2008000800082001034141510080c0305180406848807a22203420443d001010542e280700b60b00024082c65081310000e1a5102103189918400d54407400a40d1641002c003c008400d402440c0c01184208031019 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 723789757 1250 723788507 723788543
    0x6050a09150b070203100f0219030c0c06022101181b120c1b060b0a0f060c08030c130e040501060509040506180f03040e09060a0507091401170405030304 67
    0x1c1081c08481c00300400180780c94200318075102c0e40300007012601030280e410a06401e030010b1146520801003000c1c05a41d42c02881c6100e212900c00307400c1d0382c0605181c900c0201034103500110903100c207a8802401680c904030002e460140910311003c01c0f00ca560442e0003c20b403021180115441e42e824000c06004030702d0243c24040100f05a50307440d0780000e0007181c0303466031000d1640013009000304506008601c020039035440d01108600b401f0944003581c48800d500964200b4414110040c20101024030049080c120018070300d0b040c00d81e025046043c080085240122300c0411501c018000d903003540012030f9545240f80070320200700d509440c10751230550000b840d400e003034003110300c0707907501c88040d1255585407103109403240c601890703403079191007241e21901d4044c400308010400352902d5400e071003140c074250f01c00601e421402040c80300001d080c81c003070081c5150800c407a681502d001111003210b0490b02030040390320120001151154128040900091100c08001907020750702030f004a0050502041d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 723791007 1250 723789757 723789761
    0x31b020a0b011d0c07020f0406120b01080609030a05130506040617060102031e0c0a08030c070606090b0102070509090c060d0b010f0905011209020d0c090e061e04080c011e06050a09 79
    0x5003541c40c4a00c004000031640135991004012491008100c0b020040c1c00c0400b00b82121150b4209601015482800701c0901280c2d0064500402010004288034a407202c003054480c02611240b4017802400b2461507400000c00e0541809031001819080e102c6982c0d00f40200b00210280700071070b00d44a03070408504194070200c202d5103802111034440184850190520780f0b9a440180e20308503900450202a0005a9140046006d00c503407649454461046003008011a00c2a6004848181c9000c05003005a40c0200b003140c2120000c0f101e600c90750b0755000d14103083c242408629a0b10050000e03010b09003007403031751140349031880c280d0740c2c2500489541c0c829502c000700b6020700d50101d034a0040c00c502c80801900101d100d2440034043c400784440e0381c1d69201082600e42c00248143c0e0700d43d490384401800801c41980e0103c15410003516100c12204107100072540038002500d0340000244021400000750441050315074150408114090030121102c010300c124010301d8400d69038480001640b400728 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 723792257 1250 723791007 723791039
    0x71101060608012303070305010b15130905060a09050a0510080a150522080304110d0b070818250f061b020117090601030606050a030f03030c031b020a0b01 68
    0x181d2214a0b980c0d003050401090703040fa035801e042540c42c9812100740951010305c04400250311440000c620f101250040100500e4480d00012407140d003449216072075003031804820708a40c1c1001d00041c072901d910000c640304420b141c0080c5902410803003440700600081e07001030712501040a0000e00c00b522303111500d03140c580049010b45500d11142032403941254a5018a03004503c940b05d5030881c030541001c00c00305d900340d240c086e00c40590100402060040e4043c2e08194401d08450300c82c030341400e5039100c410300580a0100020046050001003030111403000c05407950f0b681c003040318040049112980d8014200703013402c0c4000566444d002440b42d180d80803070420360320b094480441200c0c90706500e06901200200c10b0713041190061840780e8404030354000713a01500184014060a60550030030005403429540030380e016000e041410004560700c0c2d06072080140d4949004507002455410841c0079210780d200e00e02e4016901e22003100040d8000400390242032155412043c80d070b903030385c4107401400c02e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 723793507 1250 723792257 723792269
    0x20a0b0a0e13060807030b0a060803070302070b0a05090406172b0c0c0510081b090901090209130e07050f030a0c0b07030201020c01020f071a090d141902010507110106 73
    0x4490103001c0c0307028074041480ca801c110b4005102c0e0b644041035403800003d0342c41a941c448122060041240050103403801404080300154903044030745d60f0082d91142103200d0160b40d00000302e540400c0700e1007402180c0907410000d00a211294982c00d0603c0c110036001c0c44400240f00d15081c030030903d01104500d0510350141d81000100c064030000c01d403500700310711400311782c2510043c002103000c0d83e602d44820b5400b1003e40e03980c40c0920b80030002102241000300344429902c4103020307100d12555802c0d01a8107550b0754481c0513072213034030b80004120250680410b000b500c0e403d0070500000900c000a003a0101c403030449600a00c1000300b01819100c02000b8800703418002c0d42032040c031141880000030b21019220780f0006152494100009003260880c82000101110000d120030a1084081c0c0408003030901e00e80b100000d00704120300340e5450600d04800b209002686005400b00c0b880d54090381c00c0c4461038042d040c42e07140c039114000d00a090444420000c203130030340d6060302810414800c1d0030944076 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 723794757 1250 723793507 723793517
    0x606010e0f0d0f150e070f08060403050a0c2003010b120d050306010c050d230309150606071b030606120f030c060b0d030c021203090a03060f09050d0804020a0b0a 71
    0x180301c00d01c0042012034005482c07030900d10700c08400080260030042c0749015100c80025036241c00314229801e00b070726640f1007031403480003c0080c07004803004114503402941c1802c10340d50f1030740340c030314180c0702c0500b00c20ac044d00400040e440381985a18801c2a041c00f200d08900801c440c541000400801e8041260801482e034010000c0c40740c4940984000c40c0c1004c414105003440340314030382c0c03181d00d0005514032640004000e0381c055a10310307048400c000300b411007004c1d0050443c0360502203e0341d1045a00d2113035096603e24070204156440b00c00c1200d2500e034108011301085000b444104032080c000c1d1004881c854500480002c1340ca04654aa110b403036440b0b40c0b034401c0019143c40c21640c800e005841a500c00380d0b01d204c1d541d803075078a03402100e040381e1103a200e5199a0b0098010414440e401e041d024010b80c00810204400e50340d09082503050300c1c0c0c8600002141441015040004c22011000038094819401c1d5540c03c140c000b40954422031007110907003001ca490743d81d001c207507000d42a101c0d404a1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 723796007 1250 723794757 723794779
    0xd2001031514030a0c030809030607030212060f011202070501020316030b010909020304020f0409050d02010e0106060f111e100606050711120111031e010509090d050d06080303180606010e 82
    0x10802c416092500c0c401000c46200c0041307602e50b0700c0c1802d130356070044941440002c1c03008080d04041c000070703a01c8001400e04505040c1106c2442d05c0e050402000e02e4413500072a0000c0c10941c0c0a100f0054042030f054504544510340382c5081030003540244d5003021062208810220312a200f4050b40c0c102c01010380d90020300074508080710001e50005007040342d00040208500034140c640d4820301203814001e0000f01560011010080d00310b56005001403c0e41e410036206100c50340e0000c4151603114020b1030112480d02030451800d040c008500350109032081ca4400c82d81066400080001144030905420019180d542c00103544600c10301c1c40060803035226544007800c0e49000d94040521480300400410244d6061420112541c03084490102e00c0c0b2010580e070032004520181280544001c0e115138a0604250100c280d450181c0420003041100c002006500c400312500480000e0403000300300c1ea100d0030801c40b100944401020552100e10803200003449641c840d2400c2c441981003c0d001400302 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 723797257 1250 723796007 723796019
    0xc121b011103310f03120f0b0f1e190513051009090809030604150b040203060f0f18070e011e08070e0406030c1202180c0a030c09050d20010315 63
    0x2415032018000004500700035510101340300c007100100c21803281e9205801130041c00d503c00b080320060f40245031403a00d00300c4000c12903140d14250086c0324070f0440386802c10503500c083c0052148488144a038214900e0003402d41c2c407104213113118096400845840301e0070300c01d03a00103070110b030011501500d540805620800c140062075110740e00f2a8091020180307022507500109290080654080300d945040d09034400a070402c600c1040b0781c20703e0440781540f86090030360000302221110035076070344a240044d2080c1210341e580d06100e40c010a10340c90807402071070300c203a02a20742d01031518014046501411500790220200f00131141c5100c068841744016114410115186000100c0550304503030398600100c04183d01c2e02541d0000c01410201e280503030b0a03481404020342d030305980340d807201c0001001c0c40a900c008000f81c07004c0302c0483c40d000440d40f50030f1900b04d460808079409240c20040e843e4180d020300a043c10a130300b036031000100703072070340b91040c03400440480d0704100001e00ba01d0aa24010702007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 723798507 1250 723797257 723797311
    0x20a0c140109030828020c01050d050a1404030c1a01031a0408220911040b04090b061207020a06061710020c011b050d0507090b040306020c121b011103 66
    0x1298010b02d0000a490344a68407400c1c564880d2442e41c04910301c500700d000500021100f140e02050480c07014098021603280040c02900510490444054a41c40015a5000690b0110396120582400b0384c1c62410f29040c042c0024102803001d4540d0180d00005194207282c40c4c4a40341201d07444008540c08100c0d1501018020380040d004503441c072800c00c10398460b030101011700280d20f00504218100ea030300d001003004c102c0354002c1c200300b43c1c01d00603c4200035106030b99045e2070844030184c1010038401a010700007110781c407070b090195406421510a206682d640010142c24451040c2e40804c0f106850b010340b03000d0343c81041000200d0758400d160481034181250040d0804014040001ca6400143d02c0503078030103141070580e00700289010581c210105101e004040d0440c0301800d00920481c10507500071050711a038040680307119000141281e1000c4100031700c40c00310b0340c5880403039100c11418104401081001894100c00c2d82000301c800105022002201d000e850440c00060740b60400e8103100b01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 723799757 1250 723798507 723798539
    0xc080d0e010b091008060615090d0609080403080a03050901050103020303040512011824020c0601030602450102060c0d050727090c0f0c02060903010603020d050c090106020a0c 77
    0x4003554a032100020a6111154403501070300307106083d6000700d41050a060329000700102402c0c81398002011a0401e10303040d10031544840380a40da1480031220300e050142c007034001c0740d4008205180000e400000d0125040190030007115540e0305001075180d40d40c1c0f00c2c0c00ea074400e002c0a94107800c104020027407480c15403200b00c0d0803901702001090070000000c0c0d0410081195000b0780f000140700c003080310b011100345800486152409421410240c1490605a9400c414000108103e60015800141025400b85030072070009001030070140f41700c4456009088031080d040c2c10210f0a9030301c0408615030021608511900d2240e6866050088803600c0a000e004060200414009461410fa946c40050850f5140a2980105100c0700510b49480c4004880300c1310381d02c030200815106800308059004021a021070b40496840e626006000c00203030042006a05c000d510104401102d010480085032400d82c580084985028980e40d0362000e80e103400e00d201005000e81c1700d07007809000c1c41f061481080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 723801007 1250 723799757 723799781
    0x1c020307120908030f0f0405060705090d120f110703020f190b120601020c010c050c041d10061a040b0d110913020c07151205090120190c080d 62
    0x50031421090706000c4070018141540c00c01000002c015400742d00e0b912480d00201521000d8005107403d0f19141d49031080507114070100600096107000300e54524040719003070703a04407800d06070351a9101c50142008805039940004154403810b07401c224070700401c5100859030042e04c0c3c14200131f120020446401001c52032581e80844174180070034418602000f50104001c010302404041c1018400a4508139002c90034034100170f540b50b1008000f40c00801c0500b5002025240401c541e0085840340c1c00f0300c4102000e40c5450703c10400da0181103102c603080401100d1805103a413a07030f1004d190040a59200e14010320700c50150810806107140005d5000020400d2822131003810006804000741c07041070b05150000701e00c0c1e000314904005840c240300940003880b07000308200d19034129101c0a8035000443d040b0000d01540c910000340d0340c040c2034011a100d0003110380384440100000300100b651740c1003840c164002c1c90540d5100d0841c1307406003a1542007960880445820b1581d0550701c0c60103007500c02541 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 723802257 1250 723801007 723801017
    0xf150a080d140f1314030a0c1e09110a08010803030c0702120102040b0711130515010f030e06180607030e100f18050c010e1c0f0222020405090901021c020307 69
    0x3c451a07a00c0c070000d00028012690780003101454002c0342c58813030701d24020301c500caa08141804000180301c80c8030304045400c4d80840080035080d6044850658440f035100c89105420468070400b00e0121000822000d403135a00d58840c06e98030f900030940d40c0d00040344c00b0120703503c1c200008805440c0284840b8102e60b071810002d807419803580000c21240c1c01c00c050403a000031020011110a107041141640780e545080d01c20000c0d85000c1000030940c100c2c43d0b1071141030016014091040b0307403003030f0000a4030200c078004a58080c10082c0d10200c0741c05a200c49217032513015032800701d00c4051280c0620042e1507030000c000d02d202a0004141801002e4419007104015618001d028882c001400c2c0740111b80c1c0030ba400707003851155440002d010090ba1404c0706102d5456224180040c0b09901c1100344403d411400c8901110203a02c007041d50752141c1391444800c25405442444007032059002071007511001d691840c0183c851501e114243c0c0110314011411104d40a96140710f2402a405154403245078546 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 723803507 1250 723802257 723802267
    0x12060f06071b150c0b0f0604090b0f06180702060408030705280305070905090115031e0926030f0606090a0803190903080f0c0c06030f150a080d14 64
    0xc0c0d401c1414180030b8035041241154010072856100104640140704030f418441e008034040d0751003180e01d00d0002c100842d0000d03540b010981503102c580c410b07061103500940003402400d00c8202c015030040300700c4585201d240c40d610308544a150502030240a4035840d0020a802e440d81e41e6040095000101404100700083c45507421504020402c11030388902d461030032100024041c1c00a0a0b214010240703018440b47e01400c0002d41c07a0410000d04503000d108060315014a045021005424200312070010403440f00c60b6850082c015078400c000d030902c540b2540100e070000c1a42800c001c080b03110b07141421141840003405114074002c196901c0000100550700e810f00040000d00c0c4008660440015640041011400003400d400e1060707100c551030500c00145403955036800c2d054410306404132803544020840c1d298005040200452007a0024a182e8032481e208202084081e8200c0790980380621014981030030b030a0031000c0b41c042d50481ea02510714101d594400b600c0c1e20300c1035071f4051410703041009 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 723804757 1250 723803507 723803513
    0x903050909010b121b0f1e0307080a18020f010305070c0c0906030309080313060c03020307020d2d08041202061306020c01080c04050d0303050c070b0108061b12060f0607 74
    0x41c0c0240a03081101c819511040d0541020464560040100c00e48105012043c1c50900015058501c0d84004101940e9516125044000d00d07020b018100c0380e03001c074003100784030101d80c201e007105101e0917522900b0820396015030b90300307001400003d4019401102400c002030b0994441e4020551150007030624007400001d655036415121400d6022002c5159211b0051081552001d4920010b01e045402075082801c240201100041140300f000c2c01d024150f4040030416009009840080b41c0040884219008a0600100000464030140381281410f41c480551400b10107500500e2500304c18180c1c1001d00b024000201414404020307070b8003100a00400c0a68941c00d460003000c0d200b9903016100d401c003800d00141421401038000780ca0180d003400306019030303200c141e1201000c40d0503150120306500e4216614105205074000a07010101800001c02c0c0d000d0001000b03030003181011099000704440310461040d90060603880c021b0440d40d00081021072401e24088600400020f103030070700e0801b2540e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 723806007 1250 723804757 723804769
    0x1051801140639010c0206010302031005040314032502030307090b0a0306050301020c0a030906080c070308181504031d0d0602070212030d0c0e101b0302160e0f09120d09030509 77
    0xe503d0118000d010815085840020300035101c2c1d401450004181035410340d400661941da031082607001c2c8543d11030000d0103141c4203032501d50020b020360030b0480c0c1d00d050002c1600c0d50300c0240d8080e0700100f4044621454454400800c880c030506181c2d4510201a0500b18400c2c084e038001003075041010344410011906640030300c0100100040e0a0082405888515000c0c064544580c44682440846010020042030740c000700c034050355051901c3c03001950f880610a105400c1140001003505c911201604441c1c1040d501500482c002d071121100500c0500780d1348841d0110803c55038102d002804084000750303e580182244c01d100905000804030000c0760546142c0201104524903030704c4940003800389821000c80300c4d072050199100031910030602c0000c0c0070130120309a00380c0d40c1c01401da4080240352007070114882802e901c5c10020030031590794081040402c0f0a8400c0c8140781495000725254507070000d141d2901000b0080715900b402c05129100c0e0080190800503024814100440c007840d90741c0c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 723807257 1250 723806007 723806077
    0x1b0f051008010819020f040c05040e0c07150f0923060a050c0d0905030906030f01030b0627061819230105091005090406020d0507020105010812130807060305010518011406 75
    0x9649e90585982c5016a41d166a9001400b41802c1040402c10003021800d11140c08050300700e01e1001280c02030041d030500000b4002c1a40c06006514404041da21703400e2030002c0d0815008007507080310703c0364550700a030b0700448200b554000340042d02040001781a21981d0480c0f0703c4c0034001c00540742070807009004a0820381c411125982d40450110051003000b1604611942010095804844050303c007000001c100c04c003070002c6003c285090300041e005a42d0324001d0014035540400f50513850520411148840c00e884908080c66402d0042c02c0002102508545a003c240000210350782c4c0d203010240040b2a1001d40110a401040e07900071880d03454071441e190165124010060f620304c050b208003403c0351005460181164102001001a5240021083d60080c03642e40c0b5a5075804210714030800d4114141d01c036902c503000381c98002819030b800da84485c4c100c52041c3d034400b000003410039a62003400320902585040b81e5046042c00c00500740b10340500307011f142d0040a190700356882040980d04c2800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 723808507 1250 723807257 723807281
    0x50705060304051608030a0503010902070f060c050408070b032e0f0b3006010311070204392118230d050d02071b0f051008010819020f04 60
    0x561310f0b04480c03464110f82c9401085480040c5040001e0280000c08510043c070482c0034103a0045014070a000c40840c0c101c109030b5200030f0400480c0314550019210341c11912455034240141140091505441030403a40314103000035007003520b1b04080900f070380b1a55100351066840d66401c803000c1007440b55110a6001391242e82d0b000c0e1384420036a0090207001c64070544405088604940c502800c03480c61380d020350030a00c03d08010440f80124003a240190245c504040d5003d07007411840034024201a00011310107589142c407003202c60028016142c5003400d40111800075410400703101410f00015030301405005000404500d24800d580c07a00b03840200c080c0140c0310f42c0e040194640421000c181b12100d056005009060104020107014140d07008900c0310708019a000103111081200711250340c01c95031380100c000ea1b08207880308035082e141c4840e4000c29018407003e200d00119030340118403660480d21379130700500741070140075003202c0c02468001f0106d0304015000030341004da50302e900407a00c400070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 723809757 1250 723808507 723808513
    0x9040b0108010b10171519051305060105120603190b15040b010203160c091104061202070b070f121109030c0f030601060518030a030e03010e120a0c05070506030405 72
    0x1050200050854000f801d10303912072441c003511044c1e110b41154413112a0134010941100c0c1e60341c1c0c480c50051085035000501ea01848290445030701464401940e010740300c06840a0380040c002c115a0b00c201c8005403405400301c0c4080c080134518030020541c281d4019405001d66441d10800c5020341d200300b803000411200c418581c404c02110600b600001880104202c400344140d10911001035102c0c03090714408901420308400500501080300b008000a0400305000c0005a0070b11005119039000b1703002c0c034800503540c11030103000340205000361504243c2003104070707041c0d0701c071000140c4044402d600c4840030700880002d080d4050000380303c2c0f422124100c0c071556544820a5040504180d00c0c00203151280b0f021072a141c8094500040300e43c10b4174a0303401c0032070b681c0591101c415100d0040805055041c811030340341c030080544c003a400f810140001d07002485250b01e10f030910303622100c0d01005c00c21002c00900680c0d08036072060080c000e51030301032030035181c0c0c2c0d40d103610116265500c211001c1d10300358 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 723811007 1250 723809757 723809759
    0x5090403030f180b01090b0307210b1008030f0d1401260a08030129040b0d050a201602030f061803040e04032a03030f06120819030b09040b01 62
    0x864000c550b492184141031415500c0d407903880e040500010b0144400f4561356203074a0309203231810031083c4042d00c804240d04a01c01c0c0070308c0040e02d900c0310b4003c08890603580c0f84082510741400d613440e141034030200380242d401e20b4411204a0000d0700a00410200b454488940c00300c002000c2c420180601110b04100642c5207408120700c003100341d904000f55141d8010081d50340854651340560703054410400001040c60302508404c0c80c1030784030054075503866200140000300c44c102a0020301003001d80c0307682404141c3e2002800d204071130b07103490103511024481101c0440b596100b0700800c80110040b81810048a454010a07d8075019100210095000409000c0c0c130f1100008000b0103030501a000b903240a0411b1100c1c5c0c0003c0f000f07007004040c004031813a41c5036002000030104681c40d43d03564a2a06441d00350a0042c0079200010071070140a240100104600100420041813039410260151078040d48170782100518180e25001002c240d0755004450265507400200c500a5014407007222540d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 723812257 1250 723811007 723811031
    0x6030a061a0c03030406050702030405030303090d090b12130204020c07120215030402150901031e09021009060212030406020c031605060105100f0c140304120b06030a11090702070509040303 83
    0x140c4420100d490078084140a00c5240b5000001241e901507405030380403400c1e480d0240c05900d18069a081164940008010010300300c90019a20012070b07100c1d40d0b130030741842d5110b4428129100c3e0110710011144110006050b2081074011100190b102801c01071034126801c00340d50400307099030000710103000207102d010194900401045000c40c0223812852075820f10b0350010b40505c0300c1030949151041c1c04200c13002036a000394000003607004020303043d403400320700b00b0160002480039541c1244162030312000401c04900c80c00f6200c060705c040d40c00418980100d600a0712039500020801c80309603800300304c1403c100c1d038140050501b001681148003050441841c2850402c14160031260180c10024000034541d94062550b08030b04003641880943c250703c0d402c08180d0404d0805081e4100d01c000100007a240240409422101c2d0050200b01015141c0108250f1035980500d005420b4812050b0010400d2511103040c2e40c03c064107004a0349482d540b03601184c1080741c1101c00b940400c0e07a4402d90001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 723813507 1250 723812257 723812279
    0x11031c02010f0f0e210d0614120f0606060c030904060f1d04031d010203070506010b040609060e30010c0c1e02010c14190b01140306041a130206030a06 66
    0x4000d49083c00d10031601e913910099030b14003040a0440004440003001c8100101010480310359103407021092204580300d09010203404c2012a100b401000c02e403039102560300010a403154100c0320180030707098948440d0204152900b180aa04840340030400140d900c0d50340e2807123000c0040c002c00a031320b95401e117840c1203905403030100c036a070301d40d40d424070f40811001a034810300c80031800c4a40a98601c144090100403842c41c094140018080c0c4160400420160b43c0400900101e9640e59210303101162596012038141e0038000400382c1100788030005078401013002c0d12107201d0304c030000232402c554031210462500f51510701c580200401c40d000c40e420f05212804803008481c0882c640c42950208803540000d0046a07a0500a81102da00707000b2407581c0c078400e00c1540e03a121042e000c04410703182036041c8110741d4402031150010702110f044e0100b800e0b0030b000c18954840c5400c007a80700854561003101711095030000b000204078502c0000302000682c3d90001850140c1c1c403100000079410300305800585 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 723814757 1250 723813507 723813521
    0x40f05070306050a140d0f06090b0103110111060c0717041205010c030209031005180109030e1e03060a09150203010b0d15050f061803030f0c0106060e06030411031c02010f 75
    0x800748400c0c44c414046401c0056580380701e45020346d590861030100b410014102e83c0d100304000c0844d03043c407604401303010043c100c05050724000c5c002242005045401034444840c90744000301c050b00b064000590040c5000f0150800c030303019079005020b10503201d00c04901c41d80309400331891040446062000e0083c03d1042b110f01e00b815040c2180381c401c18000282d81c81ca030040b01040c01a0321035000801d9071100200d110302c1c4091040003030241801c145005800348600001c0c541c001d03284886054150510018986c14003c005405441c0603102d03882500c0103050184800d0b903c0e00354501ca240c05801141c4000d6008010740f1120548072000d044548041d64907810f80622800c1103000c0a10843d0b031140e240421141080380c0c0d403692007601c007640421100b86210035581c58040420018091a0980000c103980381d06000200012a21094250b85401505411641251080c0300150010307141d20000c000c60b4400404441b0b0340c2c01035111800161418001c1080185d441708010040540399019100d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 723816007 1250 723814757 723814759
    0x2062a060915012303061905060901061b1a040b180d09090b0307030b1005030d03050c190e102601031104051f141203120103021e040f0507030605 64
    0x40d07042940b9804900404180038000c0d8405015000e40b0740c0854000303140d54020005002e40b101c41c40c00006e0549006071001d0403140709414100040d030340b440d155544505941c5c9035103d0015a0100d8011034481401c1140c0485d40c215428440c4401426003d425074031842c4903004c4160039160070007030541040c15244901c80d60b540040b140050031900601d030380c0250340041030300103440e60100b030000e8a8031000b81e001404c3c513060309090020715000c41700e401c000c0d10026408c8900300c004110045084500440e27400e408550300b03010380400700b2a198620f441d503800d10300c2c2c20f010f680c9407080040c0d454040e640100021801080d101c40d101c10704e001c0708001c0425232203075584a07036245440391958040404505403155940c5d000088800c00c40511075010355800642d004451a1a42d41c030705644100c008441d8407944003046845840000001180d07565030004140c3c0d207880c1d10b0340d800e00000300c60100541c0180490710010b2411900c80d0720032a600c1680012001c42c2e80c0c14188006400c41301290001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 723817257 1250 723816007 723816013
    0x60f0528140324030a0c08010f060f03030909150b0a08060321030f04171603020c0904031b03140705010603020a0501140304080d2003090d110d080402062a0609 70
    0x290121004034194001000c030101e607030380300f0343c60000341045021032000700036210f00c6001080b591780c154800d10409120308002c2103480d8458803105a804984c0c40b00070000351006409100801090304034050301980d100c008600d441e210b42e00300341d46410103281a0300041d060390404c140d82c5010400188080d02d0711414615050b103902004541d1320005000001d00c1d0494004079080110151403450588400184a600c464002078054441c00c4030304400d0300148500c140008035071800f001498001c6525031100c40280e80e0f804030034050841d01c04030507014400d07503c446403040b110060090090031b20400001445904602c1000460502904128101305101804c1003107070341c07000704407031b0019040f400f480d4481c0b00d40001754000e0000803a10034800c003800c1c12080b50303099445c00a1405081c41c030041d00c1c808801a0011241c18140040c131040c19400134404400c2d0b01e000d079070000c2c0c02600180080e46021089425051801d983c9501d00824800c18065030b0103580c4288411900110000d000e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 723818507 1250 723817257 723817261
    0x3031514060f0c190611190f0c021917010b09130609022d031204060e040906090c06170f06090601020f060403030f1505030601060f05281403 62
    0x321200240d180506406144005900002800c45100703442d0000040403c980b0280000c40c0c60120b0b004040c681205c210381003480c0b580114103440d0503145400c0c42c0101801506001b10340458681c0c45586241d0144546000c1850160301c58406a4001407032181f415805e4030b14060251000c82c4a240d82041a64036042803210b00c4d86d60054881c0d00940c200c1580b040610305400c019000782000000250320440340d941c244d94204d11001c15905078246021949003942c6004140341d101d220b09000388044000410040c0f00b82c60195150940181025000161031a101da6403501190038002040d2400d5100e07040800c02a0b6101c940c50000800403041401030b42042c425a1b0666100a00700c60300c146060f500246c4580d00c00c010f40924000300804490203801e0504024005058101102032a1307410050030250511200056004a03200517005000c03d03031074030030304450500014403080108082007190001c200034400b60b115045110040d0f1a80c004280d00000c0e0400410303810550383ea03402441 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 723819757 1250 723818507 723818519
    0x211401091e090f02010e031e0c2106041704090501030501020d0c050a08010909060b06030a0501150c050a120302040b120712060503100c030b030f1506011e1103130b07030315 76
    0x3d11400150b0a0070a0a10300300c441c00041c0c00c21188a40e00c0305090b04e8124010b001100026103000003100070340381901e001c822902240fa5041d4071000707581d1513900880114002400908c9d8500d8429002d001ea281825140c9628000b950380a80c02900c0c541e40200350001c1c151700b1807061607940026070a025141138003010026202200500c100c800d0141c0d01e0b54200c3c14005203030402c0c1100031000301130640d2450082c40060041000303008009100d007c0c0d03085480c04500940600c500d04d604200246000e0760241d850f80c200c407803040d0112007010340a02000402400f02d002510b140c414924209005103840c0d200240407151640d85815068280b01041000da28046241e0b0349800302d00d440490300543d182026005007002c8014180c142c4600c135045902c241d00032543c03008140582c0303d0501d660302c4400c01107407108007900c1012000d000d000100c440550142002d885420b41c080180c82c1007500780440cd10003c196544003501c501e00004902c3d08050340b51080408556000308070788021400c0032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 723821007 1250 723819757 723819773
    0x806070305010837141b0105070b090703020303071a0f0402010504030821270a0c052106040c090f0c05030a0b0d06020304060204170a03211401091e09 66
    0x503880381004130840c501581911000d5001d164001601c201c0c2101810345000c0c56007403180ca0403003001d401141c007045405201c45031100086181655080e091030407948903400d410401501441c2c43d44151000040181c0f003e2018181e014021080501c4003110615145607a440090082c074000b0101d80401005030f030003105031390542e41c0011919850300c110102c5100000c051040d48207910f00320710100701c030000d2103070510490441b6104c803140ca00001803034031687d2000765001c01446585020414041400c000300c0d61843d000c4c040f0f550b2800e1001c00c4103000c0c10854180d40c113980010346442d0038045422603002c0c003180c041001000b001903c00701c04004000d800041d10341d075260f5458260b0301c07000d0380c1d615914202207904003004555034285854514004e5009120b6506065042c8000000340f400100d120040c45400d0740700c144403614a03c40d9800403100c85c08250181d01d94841c240f8040120880e001d5029090380c4400241d42c004540c1e035024139070312040c00d2070381c040c0c100103000002807098 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 723822257 1250 723821007 723821023
    0x60316030201120221010314300a02190501051605070c03121101110a1418091902030901060f09021314031509060f0a0b06070209041e03020708060703050108 69
    0x120f0b4016250314000f075260f080641d0600c446410342c900d05c000030051180f82d02503070211150002c00c50300e09002441c20301021803850040025000d0f040720107041628260b030000d00d000000d030f10540d0048032069542c2c9c0301030007400384192250703035541d41002014006d00f14240340e000090b007015810b082a0f1f580752000f503003d41c00000c0000b10f44143d9200c82c54010b040010361203034080020b2120400307004c41d00c501500302c483d000000074014140302001c50700346001c0700e0480d1514a5118501421710b0148115010080e01910451044080c00c4080880714400b0310301640a880001c0390a502c1c100c10f607801001c1d543c004a42043c810004481400000c1d5040c4003210b44510400d88070300402e4000a090802c140e00c4900300c600ba02e0200050050080751040c4200060094030300c0300d03102d81c01d200c0115980c020081d90403000400c6240050324100440c0ea500034842c0090160f2015100e00403080c6861880c800c4015030301c024814488000d09001056200c0304c43d2408000b55850161020703594401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 723823507 1250 723822257 723822287
    0x71502120a0f1104121104060609090903020a02092706060607020108040c050a03051c02120f160c09090213050402032e06140117072c0907030203060316030201 70
    0x682c0450507422110341d00407000414002c0d6001c0d40316666aa801c00d4150017080003203440d03400225402850f440e1922950040e00c1c1942e0380c0b50300c400d081c040340000900b06901e058065100d504000c0b001039850780003d61103404454602281d5046026100f14003644580c002038858101000700401c1e40c80310401e444040e502481c000700c0c0307500d41e0304010350400c82940000b03422640c0040040207110300000c003417140748101181e200401c031f10740204903195803154000c3c5141080130090107490001340d030058002d10307070700c207611792908205541c03480c00c0390b00320f513000a0686403980d06280940c6001051816610725400e0140300c20300d02036000035160410000701d42501d610800c00000c1d48585158010b95000747d0300300800c40c2c0c0e80c59160b1031100f410406583c900007040c01d840102c4c0d411241c0300c583e0241800343c69030b943c40310b080c009100c5c1402c140c41541482038040c0031401580e03520a030900d0b00850681d1801a41c9080c154145402d040f00b201c6040e001c01c602c0c00003000180d80c445052420018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 723824757 1250 723823507 723823511
    0x30e04090b130804030f050601030c0b040b0f0c010b0301060801060801060902030f0c031e01060201090b01060c05060f060609090a0203010f05150d110904051603050907050d060c1106040602071502120a 88
    0x242d00d18003900d0342c2c0500c1d00003415213221103202d00200240025903030f058034011122460210364404410a4511850080744071820302400b92101100070f02015140c6444007e00224560b0052000b00b421122550300170050fa070344035202003001060138030a910203064401310039440c5250940c40d10303514400103061551514000400201c004004240c407a200851001d4803c00c1b659503030100030301a00f405001603a19003080000002c61a00401c1e206150360343c07001c054a250b99506e5104100d9450080100d5000181048000c090351740300408680300f0122100016102e5051015448580f800c41e00014040e0001c004461580f16084c0181c40e1401070721240070490440c00e64541d5420b00172001c003e60007a0070041484a00c40302d81c01601800301d2036590400070b0303035500312415036642610f205036034104000c44481000700701e4540100030151024244075003101c0c0b040402520b040012030b01034444603070205426007000300c0e0405003888104402c00030340c181503c1c84100c3c801000c0240c060003500b6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 723826007 1250 723824757 723824791
    0x120b0f06030c090607051b0d020306150111030d1e020a0c080d0603080a0e0103051021020303120907090c08040305092404141c1a0a0e0304030f030e04090b 68
    0x42d600c00300726071400001030711413a01c2e80b40702e14206565042c41706580b8205001540c1c045031504101c00130241c2181c0080080c221512040c0c00d201031020341c0c8404c9070400200d4140f2030100c94041000705035101d400b0a0005040c3e03003049418010510452540384468010018038450990000c2202d00700d40e005401c20750384000b031900c41360050805900c000e14410001c62503480160f0000c0155032a14802c0c2c80503c4560b84508458a091080c1c0c0550700000c4025190440807450340c5141c0e105151000e400c0b40d203011500e518800c0031000131200e80d0303d9036000d1601805460740c503000e0710880c4801c0d4104039003103090587c1c0180c4917000f590085406400711200d0390784002c00b01860b9452000c4a00c0e8041c0d071303454a41644000004107456154013030070991000c1460209248400714006400280719507804612032840041194040c0802c520252181000d4200d00400e00c000c00086100e01214004000549405031600552803140340c840d42c0340c0300311900422064070300c03140c3c8940740311840c00b810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 723827257 1250 723826007 723826021
    0xb06070b161214040303150305120d14011e0602070b03011503142409010e0403081e0106090f0603021e09270405010b100e1c021f120b0f0603 62
    0x103042c45000e45980900b40b8a819080e00c038942d4005010300d009503070910400a101900c000112910300c03004200e984454908042c070303e0070b60060b0100c1a0a198045006a040044814504020f030402d03003c002200e69020301d498454964078009200301d0015050040c0b52620401d0640014451496014068400159403901c6a1300170b5a020070160501c80340c030304003044001c8405001c40607010030a1104070900005281550301c0604941c060003072114a50740300d9404641042d005018800c0b146944468240d01c4800f698031540030f05010b0b84d032201070518003010f400004032180c0c0204107240c070402080b0883c0c01a4249590700d040454101951542da080c00714201d400d140c07c4070361a884010141070410ba40c58075425000d240540c000740410041d6004010440181c4020b0f0030204d18240c01140040c2030803030003094500314640c1150402101e03600494400000381c0c010511900011040743e903400e40000350200011210801002000000c00c00309078881154180540304078400300001e014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 723828507 1250 723827257 723827267
    0x15030618030702011808011401050109061b020d02040902090f0406050c190c0203070b0d02130807151107031e0516120213061707080c01030b01080c3a0b06070b16 71
    0x40000d0002005203230560029040405000e01035140042c4c98141d0000b00d55100b1070610184c414551014072426685508000c41d107014a07404076002611002c040000d60b450720407040c4258008680180245410314010040f11001005001d401c00140a004420201070b4402d041010440c10150700800707480c00040d186c100c20f50720180d00590001000d058812442c0c01a01c40c40000c040003e2400d6211035105465a88074001c64035107800c080101911184904441813601c050203040d582c80ca500c0c0d84030b448540840203034011811290705001ea0802104110f1800c911010702d900071100360a2190445240c801341c500644a6040740703015030a5404d9951004004146050b074400c02b01c240d1141d0592071350300d6846108001d0090608000e010750007030144a074242416035410b101aa40c40084400682001c12100400b0358081d45c4210b031049881400c1c1240c0744000403403203907000318110074400d60349403000080c0511028030414000400740941542c0080c141030fa00c00000c0c40016045032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 723829757 1250 723828507 723828509
    0x305371119021615050304030905100309030e09061f030f0e06180c010804060e01020705010c050c0127230706050a030f180b090c09150306180307020118 67
    0x586140c0000d20800340481c0c0d03824000c005051a0260781e185010808001c40d4010030303204c0d0300c5032050410200d200d99880741c0d0045922a100e82005000300e83c4442c0860301a014402400e030120707a03030788451002d01d170f00022901d41c7d0400c115441800e61600601160146411003001580341404281c2481001c0c020340010f072140b10b071000100302c00005100c506a130b03090240c9d030b10b918954101e03400028450004c01e2400d452141a120300782192aa80c0d218001031424200541c0700e550309104001c0003420a01031105c0e100c0380c0d991a5074a0303036540400075003103440284e18104114a41c40c1000d022201d0050200c4200e41c00401d402e02c02940c2520401e660b00040b00103002d6800345050101d486a04440542890803d81e0f03402c10090701d04000039030407203080501001d0700c8a03041c5208000a41d409035159404010301040d00c081850341400302c0d00041c0c041c1c1d40d1314485a204030382c409490404100c03980e030140342c107001d0018211f8000c1c000c0b9140c0c40350f4030010b410001607020110000203650100d030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 723831007 1250 723829757 723829781
    0x70903021206070e0a08060c0a0309060f05070f0c02030606040b0a0f170d0903050c1306050d0302030405030f0604020a210206372106031a07030537 65
    0x1c0003031600402854440804850340400b1401030b810282d442c5c1040ea4001040c1c8000000405903034407a801d21030043c0d086800110304240d2945021400510b541c021540300440c007080106440c1007480c40901198141e4004500700300880a015015035800501c00c1c1e041102654000b0301e54070840042981087c41d6048072400901071400042c074504408114403075586c6600c29030350121042d0b442100e44082e00d00c0094215481164000f01c50301d002c40ca50910081000c0740012495556070101d4196004000140d0141e000482d0403c80d9050030312482d0a9010520050b0881e0315266001030031845040c041d00f194130003003c6074009030700300a07024202c0980c0c00038030194403a108607402c0600000700000d2601a01a064490074403d0152680361258800ea0b840e01c4003101d45601c0c0c21040e440403017114911854488200102044e030003104d00b03220f00e1140340854200c0c900702c40083c0c1075131005030203002c0420b00c0c0500500395107134501d0454640302455500090700d03010f06c898480a064014000e0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 723832257 1250 723831007 723831019
    0x50d110a030c06031104050d0206030601020f120c2419060302090103060209040b010c0201050a1d130e160305030a0c1b080309030712020906220504080a1d0f0907090302 74
    0x4070500035907194200c22070f00156070600028030f4040829802d030241703100d8140c20000d148a107200502e0508091070384480188101c429081012007480e14103400c80c51800350340280015400040da4045c4007005403980b1844001e0801c1c0907815545140400052405c000c0310304c50020207550403010340040c0015500240b0b0548156160300340360000758002c0345024451303460000d48801a50242000c481c0301d41d0141c66080c104025200c007503614030400746130000040401d00000000f0b070313203e07420740311401c0b60305900043c00881c0c0c2e0110ba1038101410507456a45000070408c0002601c004120351f041c00d80c0e031604160128451411092032052143c8442e00001440400b140629000001d803141c031108404450100780d80c1c0310708410051032250041c0d003220380c3c1c600085250805034110000000c480480c80600394000f0710000455406840454042c0f038000f846c4400a603102c00f80c0e440454011101003001c04001c00051201c201c003c4d41940220800c50024800a0003209440300840d005040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 723833507 1250 723832257 723832259
    0xf0e010503091504051228080f0615040b040b030601030507110709090c05060c010b03070605210606160303020a02012018190b030f0c070803281a01110313050d110a 72
    0x1003441d0b54150f08046c5090b02400c42c1c0e8110490f08c1a0b90700341c050807018040c488a0b4642006014009501e40c03c541103145040000251003500c41b8014001031501240c6c0d075840c1c0c10715400050680b80064007a02c03c05c44402085403940030f0105043c82102c1c004140050440f440e840c00307a03600c1c00c05138040e0354080b4001c54406000d07581034004401c0e12400301d09a41d809a1103000549441c02185618034003c140c1040078800b200720b49900e10b42091000301154100300b00002124950101510f003140061307000302c0c00302c801c5502401681c1500c100d51010442048003a001c4000a004007110300a00055021042c4c1840c0c4a941c0c20454810920880d000c240340c4485841000e88e00c00c0d200402c08010b01c80001c0d8400d01c065007603034516540206402d180d51038060f207540c0e684620034410305440b45481c0d40861403030303514030030304030f04440e0003840070b02c0d000c800b10001d0300d034100d024940e034656003040080200c00340b941c844402c2502c0007180d42c04030ba0703030003401c001030003244005c052130304280ba02c84 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 723834757 1250 723833507 723833527
    0x60301050603190b150706060f06050f0d060e070c0c0501051602061b240a02091012020d1b1106071b03050d0504081b0a08030708040f0b04030f0e0105030915040512 72
    0x170060500c42c2c050b50702030201603070300c0c410402107410724802c80340022014400d0300740105107403001700b009440c803520200d000c0740c80d10f49860640606451000204000c2c8203541e08025200039030f10000e00c400d09005090a0680c100c1045240030070000034450040041e03020010b081c0e8a1158917001413076001c90300d902da444410321a0415612400701002a4194005030400b4014002c5425610001d043d80b01c1c10155024240d030286825280d10f16803d030203125541a000e00d03480380c881c58042025051540034a1500c001d0b00c2c0040d0714a12007601e400150402c95401d03080114104070343d61004440b083d502090030115a81c0c015808056079013401c2c40c081c0700c1400b00c1e038400340a041082c0c0210695840c0724403c955558401004020724220050000648160082480030b5000e4011484012a1801769a4101000400301c9045000c548441c841e41d006c4e0f81c1c02840c0403070070350080c249140b0358100072101c08d40d1603da45001c143c3c1001241d000404004040c00010384002890701402c3d22078071949 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 723836007 1250 723834757 723834799
    0x106080d030e16120503040e04061b020109200102120c0318090702061906030204020c07140d0b041214070b012408160908101a060301050603190b 64
    0xe0310000080c240300c2010180c2102080d20360b0a40414148404042d20f0300d0120001581c040c0d9098a441c042440000b40000180c1c1e03010388958403840b00058100c01103402c0003e603902c4000c3c0d45085a260104c0c1e8000034809902544101019040c401070840c42880100c0c42c203c110206000402c8010402109075030000016220543c10322049140b1842c100041c4800080b0403201c0e100140c1c80940441c0100c28030902c442c0784880b503d080494a592a0b4000c1020390f844145480703620780c000101000700024500c960150180100c440080f060001c0d00d82d00b16201d0007400c058801010007180040312402600e0700c000702d50020030465140c070440e08003034007040c80902c55010013510240d206898845011016840a00603485885550315140f043c1100000d03a0302d400410b0200d41e074030100e001c0c1c10400c0340510051203482d020400d61100340206da0444860a0360728003d030f0702440140801c0d5981c0058a0303004000901e5001c10012440021000c1c00b0030740300031600481c1d8070b0f400f100d42d10120 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 723837257 1250 723836007 723836023
    0x3130315060b03061e0f060a1d3115030f0506090604032c04020f1b07080a17090402030c250b150a031a060112060b040b07020d05010608 60
    0x216401c108803075840001c0c0c0c00601c0211031451740050b0302c0c090b18210b4a6100c802100c0e1850240c00031080124041c0420b0440d400036500c1c4010402c240310380080720401c14001c0170b03400020780d4669421021000b0344a86114060000881070070071061110309520f0582c0b102107905454081250010794a0070044814804158241c0d041d005071000a00c0c1003000145042c0201c2e03159031103981c103104449140e00290800c0940600420f0070300280003d698941c00076040841428414559070704000c403541040c2c0c21400350410561704205001c001650001c240300350400e0300300c0441000c960005030140701a1280d2000b0755842440441030102001c0214042c1101d41c55802410200100010382081c035006000401000c0707003a0003000605c08144240310550030803004d0100d900702c1e6165602c0503525280803c2c03441c91001e0345c41c108015907900181441c44070038501c004000c96401e00081741e05070b04c035501440103c900000f90850464448181c02c03840d098021000b00710705a02c44540586031058 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 723838507 1250 723837257 723837293
    0x7030e010f030c05030402220905060603010b0a03080a050f0f0c0c011b020f011d03060a1406060c071a0f0d0603061506020712032a060507210e031303 66
    0x300c6422100c41c5002e0302c121825440310b526030a00350342da694200a41c03610b5000840c000320075400f0402a2041e004d0141482c1181716001408103071424005060840c3c2090303030064415103101c0000c0002c510b1020495406001707600c3d1903580d8000d80c000c0403c00d48188200110112400105100c0501c00402d1001800360242e035070181d02d00202e0718182d071a008059019500c01c8403404004110760040d4203007044d40c989103503482021040c101c0083c0c100801100c084007082d0b240d1103034180354031a0f070746459480071084403590b017400c85c0785007999a0b94005024a100d0b590f44804542c0e1169018025181944402c4002e1a6544042e000034405003805201c00c4844d0780c1030250303000b80d120798804110107407a042e600400300b0a1030110002e091010070324042d0140200c0b281d444841e04801200886411410450f1046880c824941f480c105d540090a5900700540b030b511a0314001440d6040e11507641d580240841d040c20200381d00c07070039881a8001d5280b01d4298600000030003600032440813550f0f05c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 723839757 1250 723838507 723838517
    0xa050105160e010f09180204080c040513030311090d120206060a05030a06110c010203010305151f0315060f09090215090f01050309100501240c030e0d03120207030e01 73
    0x21500301c00e030400040040c082000c00d440350201200d0b5489210071415211440c5407040c4403682d11604000c010343c80c125605105500014107100c190070400403002292811ba40070480382c83c3c0b44514200c6128022401420961903848c1c1100080c1c02c0c4068447e510002018408a8030040c07903d4100e03580300300c140a0240c051000011520701e044144080ac4807806409403103801101d07500c0000610700782c0030800a801c414042c2100f0a5000d20240d8040c6104000500c1c2420b90700f005031548442c0101208a865240c10840802c1c1c2208031010b01100e40c003a01022081c078002e50080c0c00380c40c00340c0080c415000210800a440d0440c2c0c0c20504000e4000e035080314080c0710350b840c941c040b441411040e5401400c0c840d84803216512440086030310410030004e4407101070386548200203584082e4414114804031024181c01101380c0c803030076089552241042c00d031040843d6005001d1201e0491802c1c800c0d00000c040c00d080c9401a220685a40c04c0d8a80855070740c500c070f00e40074200307040c51980140000c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 723841007 1250 723839757 723839761
    0x6010206060a180b060c010903230309120703111b0a120b130206250309140d0602030606040801090503040905070513050d060905030706050402041104180903030b0a080a050105 77
    0x4205000d0902c19039040303880c21500d840c103642c44440540881502e40390448004c00031580140c1d1b0a11800507003d100ea61010305a0501304040c0d501d45034400c030003015100080040c4440c403900081d1203c28204244401a03ca00407802c054880030020014181c290181d038179401c8104000114003840004101c45032950640c944c00c4411503510708035401045501c10602043c501c1d040c0409124a0f00c0c0f00410f000c0ca0030310410940c0402c1c0407e00104620000030452200030150085000d4000d03040040707803280c0f884a40e000041c104022840058151503000001c183c081e250642181c01402c548802401024040c0c580196a5440307407182545c103e240c01e001c0340156100e0021070305243d94800d60b16000600381001c1114414031404100c801c00e5803509030340b000503000d101401c2c0c52400707031100042501e81401407000b90783c915402e1013080203040004ac040707c1d4240c46083c20551125100003903a82d51840d00313800405c221404282c1c001c5440d2000030300304200103400450f1610500080c0916 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 723842257 1250 723841007 723841009
    0x501060f090b0d0b0916030b190b030c04090309080d0206010311090f070513030c0608041406070f0806030c1f1805090601050c070b1621050702090c090312030601020606 74
    0x19803440a0080d8851503001c3d10002144114843c04d810081c2034044c0c5142150742c1c10301c400401580c0d801248e80441040800442c61000c1c0484200412503c50a0020a0b81e00c0300283c0c80e4002d1880f02c62042d95240d5590060610030308042019041807411201454505c072006540c0b14424402141d42401910503420703541443c000d49401f500440e8001030007500c40302d60544071500820610790051684090020101e803102d107410300208030a807a81940d40c00c003400c05001e030400318005000d03141d10071414042c0580d071012485081c8003240c40c0c40c0faa9900c8120020741043e400200480e407002d4046031400068641000c0c0021369a1180ca456644810b80c3c400250070701d100d40300d4654006841d07400654654020350042c00c0c8180000c0560b01e0107a00d03a519948140c000c007101c28401c1c0c00c042c0501c000c0240625040151082c940a614464600b9a4009190744200d81c0007d01842d90803000c10b2512036110181c0340b003400d000b025940e1030780e20300c54a0705890300121600b0340144194400300b400723 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 723843507 1250 723842257 723842261
    0xe030f070b010b092d04060609030203061f060e06070b0c09011d0f120102070b0108030c0f01060e0403031104080105010b1201060c1211070509010816051f0e01030f05040501060f09 79
    0x130303900040c10380b0744081d04260021100345001c10410300b5048136014014510396440c407070a005000244c80e1100a68110b00605140400041000024a28200c15510802079525542084a03030504d4614004108240482c0c9680a1000010800904901030142c002d10020103880d80c00800c0c0c2e20090f40b02c0c403040380340c0900d2102c056240d41001d807003e1540d00c03a08003a08405140c1c440003001510b000d10030f0340d920356819401d0344041c030715070004601c91510510a01001d00c1c240c0b0030710004d01c512801d0182c00b0380010000307800241819615101e040c054180581600c0c01440c004008201315a92180b20032210751062000ca03d0b142e450000200749507025459039003101d0340095a00a880d0100c00040d900d811a850b9501480e20800c1c1c000620b5076034210b00742c0d000c0d02800c00076000d400c0c035101074a8505410380e08035902c00d17010003055112202007410f840d01c252103945800e26000c095840183c008041840c0c90010300342c20001000140a015002401103d940304402c032400f66070b400075001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 723844757 1250 723843507 723843517
    0xb1b0f1b0120160f08160201030f06050312130b0a0203191b06200417010617120a1b060c110120090f0d0b04050f160b0a030e030f070b010b 61
    0x50004000d110141402e80343c402500c4503588980c1480c590341c074441c0c680000c1c3d83c003c0031242552082c1080d41100f196414010720054210116042c0452410b2900107a141c45142800100c0f0b0381011805441076002c02c21101c0050507800c01e0705030b40340030350390000f5140c0e805400c491150540c1084070010492240318070f500078009908850904524a03650742001d060010003241445080f5055814100a14001000180027580c0140180c043c40142c250a4620710744c0241220b180f41e000030050383c440400c1c40c00000f142508049d0392541c1034101a1013500c80e03203030071a51448c0601d400c0e40030811036601c25800c480140c6c8848040c903200c989107900382c50380750142e1516401c00c808030001c1c0800a0025001000000b0101031000c0c0321400400c2c03581092102c203444007155241030005102c41400455114102580901000c0195031080c1141c28003c3c4108a4805000184041c03510710aa00c0311406404007425640e0f1001004030085640c0c11084003a50806115000050403040880440f0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 723846007 1250 723844757 723844811
    0x70c08120301060f03020904111c11070b060118030c060c050f0c0a09151206051e010501080720070e09071202031e030d090c060e04090b1b0f1b01 64
    0x24213080480710040707000c4c0d0400d00c52950050b84802e150100059401d000d0500d07134110050060314070200071103020036a02a09020601402c04101000c0820035000b40e207907015500307080c030420020340d44885442c04100c0c0e500207409800304800115003123601484984940c1e006034100c0b42800e4180d085691103008601850f540301c0729483c000c10500c41e098005c1032001c2c01b03c00101c415079a54103000880983c880e001114195500e50402c04030341d5000383c01c407481403028480d50030698102030000c0c1030703800080c003c20203001c01202400e584030202c0e02c0c44032400d51010241d40426640d6510b100c00d03000c042e5104034140c0a410350126044006c1c0034520222038006000384602030b0805c4021b1410303c1c2c45040e26074240020004e00d40110014024441994441d1041103a03080c503094000b4000aa05014507200303a09011110780030503050890507401c1000554454603007100c42d440c40c015072248442002c010300d0301150024901110200c1c0c4000100003500034001100c6013850902c401440c0000c1c8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 723847257 1250 723846007 723846017
    0x905100f0f140705190c240302070807080d151a16050f0f0f16030f241a09010b04081b01050d020711030d090f060e03030906070c0812030106 62
    0x1040c040752103207000c1100406980c80c1c2600d8038405032601d600301003a072001002c0003403c81c0400e0b800c010507044040f00404500d0300c2c15048035003c101100080260303c02040401d9004a0310405010385101182d500c2c940c00014660b855111080d11000f0380b6200400040d1441041000108082071605208200701c105004034900512011030070070085001d24282e54503c2800408500507400700010400101c61100030a0f02d01110300c0300c40e00d441a58252a1000d0401c034500f0400500344003180c500d00343e400a0444c4010318a240c8119107180c6006007080f540d410420031041038801039410b041c18002c180c3e807031f09241c0c3e01d400030090284158481e69405031b0181c254a0302c0d0380000300c0860800c40052414914008465070407100740e0300035040582e98141c82c411105800d140030013402521904a007845502c80d40b60006148444000d48588070900403005444082a50203104580000340c00500380f81d00c403c2d0390300b82190480c1c0740d800b40e030031184154101c0200c1c180c900c1054070304845040e524 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 723848507 1250 723847257 723847277
    0x70e060f04030f14060711251211060313020312160312060803030118051f30050c0307241d040f05070207120503040e040c080304060905100f 62
    0x41c050501c103158004d0714694103888004140c40c80500c646030003004540d403038003034006e91100120300349840525803422204454025100100010500d007044540402500750310000742d00300148080c0c802d5140c0c44c0c0c0300b54008100702c48010154515849240242c04440300307036003683c5003500c192150f061a15024082c4a02404c00640f042a90040c0142002d10104c2c3d40c9a407094902d01e950130a8000e220840c0122588081c2c40d4200c0c07007201d500a074589071001c2d0a803040941803080c12028050340300745a10b0480300001a4895658101c0400c000741100c404554490810325111464400c0a030310034052080d000400c00703035210101d40240b2991044c5040d119500d2010781c0c1406c1c0c9a21800010200c00410308800d55aa05c5281015048032a001c9450f15001000038185155500b012030001c014400690220308000150703011b864800c0445543d0703813500d080c01c00c00f1070090b0f031041020344800100800c295602c82c48150403260b007522007075070030300003084180c5140c100340c003100300001c1800c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 723849757 1250 723848507 723848513
    0x304080d0806210a0c0905060f1c02190812090108011d0112020a082a0a0b03011e0b2205270c0c01090b15030f060703020309030d090b070e060f0403 65
    0xb0480d10f51401c07941200c52503510342d80c880e810700c41c540d8050300c400c50b81c070400c100d6541040068060016000c96459604040c90101500d204072040b034068090b0b404801903c0e11000480b0000d005410401d040740c1ca64001d0302c5180891340c2c002e04100b40011415070002944180c0203280031070f020084a00d03204541e080c880d0704810300402002c10790303110528480000b2140000e00568403c1100010a100f125179819070ba088000d211031070031402601000f4080001c28820002d590640360503a40b4134441001c880e159805001c8250050424070000088440e00601501166021803402900071180700c0d070b03241e007000214804c000810540110380d0013003204403840a8030150b440900c1da80841d08100c3d20811032821144404c8040700c1a00d5214117108a014400b00c40380300104044005013180c2003202c002585684010704660f060540101c0032413109101030003541c3e00c00b140d18104000d0142c41d0304104858034402e5800c1c0e40440e501e041810b94030300b00b80c411580150024000f2602c2d00b881c640d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 723851007 1250 723849757 723849799
    0x7030504110a0f0f0b04050a12030e13021902030c0a020d050f03030906040b060a060f08100f1508060312120903040905190c090b04060e060f0706240f33020304080d0806 74
    0x540071002c01c180840d010a0356600d05a95224cc0c810242c4010f0302c03000382811240b00c0c284180381000941d0300070b00000034525000101c80341b04540c1581c107080d400c101132521900d000440011006036000120070868902030000358140320318016083c0404588600c414441d10980c0750090000080290710540e10241c0105852034000c00814071030b40c0c1160351020301080b05142c0e504101d6290b03100c08554101c3c0c80e48840c4064100e4000c034050300c03c01d0030310564407081c0c0c0325900425510725403d00000d24041c1c401d100792001014030040a001900c0d00140c1070b0a0fa44402000308240fa00d402080002103100d0400401a105041c0d202403820f424204c0c00e8810040f0840c0c9540d0005c0100208165100c1d0b500c0582800e03071240304049406401c55450703062014401081d40070748100c50404008154181c40000102e0700054107061070740c0c5d14600004c00181d281d00709442e104025214681c0e030a0b6000004204652aa070161340039422801e5044507250010745506600642080b10021600c4100d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 723852257 1250 723851007 723851039
    0x5030402060a110a080a030e011e0e241008160e0603030d0905010905060f0c0702010f05090402070f031202040b0d18210e061207030504110a0f0f0b04050a 68
    0x5090812036030504101c0980350031310b042000c9500020100e5040d408075018010380d0401c80a58000b4803424165a40e80410342c5050084070002c15110200260841002d00134650841c1036807801401414400702102805a001c0d83c40003a0203d000720009011319011a030704242f113030070901c0d03000d1040c5882144001e1001c090041da038140001c02c040c402c803100709c7c40740140b064418070020859050038107040f4140340c0000d210303c0410011408001e0400303001001c0750340c86942400e10428101c2d00381402c88180c05a451070f19006403000501006000101400f080d1a0740300c2d50f216621490205890014ad021f28411202d52040912444505d42c01c40e420a00045641904642a070955511000c4113a1040b4003000800700b031168002601c2648806100c0848034144c5100e480c012003100d4810034840d0040c0a00201035503980850100603e4901078100341070014800d42c0d50030707281c00810f25004803a22078020100b4103d407000940120110540d42200c01c01020b08540901d0f00c01e50000c1d02d114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 723853507 1250 723852257 723852277
    0x2304050108040318171b0d0c0905090304030b1302040506011d220c0908010608010902010c024e0607081b0c03030705041422020f0903030a02060f160503040206 70
    0x240507800b080c085c4091501190a850010080400c422050000c40c11102c0b0301603034500940c46071a108011031100500f1b00100c80c010200010705980301c40c01b55045000e00e400c01024446c0c4c801c00d01042c00044400800124000c80d4100300c0f580f207030001500c0130840601d0340036070301c0620b001c6241c9518010b00c0c6005e4003024600a8401100d840c0c4201084440a070142400704000c80b009002d50343c0300f403060071b010b0100326000304004411f41c0c002a00c42c1e68580300080c0703c0c0846020300110182c2c0000c03094184030221150b500900003100308540e51220381101100f075040250700e070004400700003416a016003d01c0d100c10139181c40703201500031040b1865580c0403010703030100040c4400d890104020b52041c1c80c540e540c2500c40341402c2000f6403040b1001c0f0300510135114010041e910300c0490711907404a551064006035682c00c1c41e41000d26074003881d500c49506020208920101507000308225100c0d030300c07091016080d036540b84070856256072040a11000540240005001401c04000810103880f0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 723854757 1250 723853507 723853547
    0x8090120070302010b1f02060114130e101406010f091a0a20160b0a09090507030e0304080105040b06031203040602030628090c0905060f130506040623040501080403 72
    0x24000310700c203c40740318104c1d1b19244142104284540d070601100380582605180380111000b0080000c0c0345146204500751804d94440756030080010400241c0c1500001741c0e818001d0040d007084846050004403140c1d800720380c10b96220544984180486025207480f002164000c40580740304036869045404c3c1c80062240c42121608000b407420190b0164850381402048014101003440c007444074594480d01a948050020308032164011803002c0c03e4a565810004d1165907510f411005007400c0c1c19104103900000901013280001904500d202d0382c0201990fa6154541106243d5529820030030580100001c0c8080b9000801540095410400c000e01c02040c00706140307103003840007007507203d0741000c400c40301c404000400c0a4000c6a4441c1001e0408002551400c804207015102e40d001c456881c01000a4040f01240c1170100c100c00303060094141c40d01da6803075650240105541d5813605a032490729003224500080110200d8040c1d80b0180e541d00391603280d903681a102400e12181d1030001071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 723856007 1250 723854757 723854771
    0x18051002070c0b161214030f0405031c0218030a0b040303200d0507020c01030c1d030106080d020a03020c04051302010e210a0b0108160303050c07150309030809012007030201 76
    0x1842c4180a0001141c1611401d0b1070b0314130ba440c0039228000000d4124081c820340170010010503102078103603980a00e489600c0c1e14141d82e03d1500c0c9055118403100300040516541103a079299000d64083c00d44405007000c03c1194041440825903139400040d0002c0182c1d18550000303001034480d42103600365208030f804554402100c2405101140c121807003004506940f001000411681041035614424081c00c080061020082d0024202410300ba0782000000c414681c404040d18254002802003101c0003d4032101d0000304002502c44440090540040c401c1c130000044524080c4212802002c081248002d0307024a41d0064401c02803801c03070a40e2101c0c0081502610030141390581140c40c5c4240094100b000503441e00801d0400706030483c040c0c591204070130765607512250b5209010b07283c0500307045444510107030680c0c3c64003545030401007a42c40c50030b2609902c103405400240400d07100745c07103091a50740c6050790a8221014507800783c218151008000c4c007003941450003421083e0003440003080d85 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 723857257 1250 723856007 723856019
    0x180d050f0409020711010f170c09010c06061e06020105150906030102071703100b0c12132714091209040b090c0d0b01020f03030c090a05120109030318051002070c 71
    0x3a0004c0205807a19202014281d5003903a01c00303003207560b4152604007010101450310380300000003402451140f540ca000282ea00c3d60740e000e09100321480780d001d1405c1c04140d841e1030008090b504080100c0d40b01023080c480201d4400d0041c00b90503c584140e51508461003602400c1082800c400b5259681555003004101e0205095250b0f950741c0c050b00da001541d81c0d05040070400d1b400c620580c419214940213004102405501040f00e254440e003800b607031615115911002d921a80d5140e0100200250715205042d01c49405170404041c000026420890105a8484200c558000305c403106d04641000741d0403903550303644c0000f0300301c1414041c00000b2491a502d0100b1301155099030030260703a540119900380301b0341c1e00d0f0040348840c4c4400e2000e8003c003120078040e207a90380809803519100e40008107030403225880f00d4807880b0050400800140e462500c4240907030013042480d0069000078101461840c1c40c443c0c8030004401554803000420205128891800c000d40040000302c6000780c80800c00646 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 723858507 1250 723857257 723857261
    0x2091215160507120f0e270a02160f050c010806030c1002010f1503061b0206010b071506090c021621060605220b0301110306090402030c15070506180d050f0409 70
    0x3e40d040c0b60721407921a8a80000107091b6000b4095200d200312410f05140e410005030318001c44102003802d0b000241600d8038010a8083e006000e0302c40e42d50701d50362100e00140620704082900041c0210159801c0311948401101d40400864031250507511000602055040c61a204550841c0034800001c0600100c018442510070402d41c2c00b03040b10714182c061041c04810b00c2400303e01000380408202e21114400041d448520522514007601000300b045414880300c600c0e158080854518204480c584500d00d0340c000306030500d01c11005101c2c80c11204006849842440d06a8075840072902c40c0803041092200100c2c42c4420488007191155000202e64940a104410540c4511840005400e540f2010381c100c03449681018803e03810417101500c04e40e010000c99030440008d5aaa07689603643c1d00120f03141890900300b443e0003041c803c84020a000426028050040c8664280d440c00e03100d4903c20300d9a0040c8070b403400c055800c05082c18880b42d018400030001d411810b9822810942e4034111101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 723859757 1250 723858507 723858533
    0x62c0d0501061e0806010e0f090f010903090e09060708060d02190b0a0f0f05160f02131a06040b0a2a030503070905010305090705040b0d0206030a02091215160507 71
    0x11415420f001e9800b19038100c48001001d0610103000380055854180800e00c8010054403401014507510f02040108109000081901801800a1100150929008054403428030905018100c1200031440341180481e109003c1c5c420f41d0348020f03842d00c41c28200f0021000b4024100e0f07010f2408040400052880d4118030020086090703025250310702c2c0503002d400d44408200440c01c204003003c2080790700307400c2011750f8505036107203482101c000c44901c2c001da0191500200079502c000b2500344007502c03c01540101c0115842280112041d02c07684c418014140964000c0b4804030300144062400248510319202826100b1190160700000350f032003218a14401c0310050740010f60000c10820419040a01c501c02443c080c68200300600c0e1140040f900d496a901901d4440c0e0b440c1c40702d0020680d52000ca1400c0b650700280101e6903410814440d400a5114690701070217a00c8d01d1410091441d00132407140c1c00504015100c8600d0341d10201c410309150321989000090003014001d403404150411039504d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 723861007 1250 723859757 723859769
    0x9050d05060a11042102150d06050f030a03020307062c0a11090c0901030e100e01090203010615091404020d021c051503030703050c010902060c16062c0d050106 70
    0x1c0354140100240160341104800d1144000108030030000c004030800009036003060f080e810300d01d503140344c0300007200652a000a015444808221524401000c0e8440c5007100e004407202001103d14000b0302d52180e5607200054003580090211401044594201c1096003c044441d051910700000007500c0f0401801d1808019510107103c0c007081110030054141c0c0e80300d013154424240c0c0340c4529038120b14803851040504054845081340494101041010505580740b0414800721078511300040c020825007000307a102e90b080420004011103803985200b1084115500e40d4982c904159807150884107400309650021390812685021035410f2000c0c0c83c455099170918001003040600240c10764101528500441d0340705142e100b660b80d000030480c2c481d1a414100251a0740484e4171150061402400c0650032041c00182c8008040c0040f034035400300440c02800403140f50320380c11704a54500d403050a01c0404410007907040f09032001620480c0b00464002c040d0780400d0040d03a149429900c056101d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 723862257 1250 723861007 723861013
    0x3020307081e0606100513030b1801050f0601080c0a0509040606030e0f06242403010320030a02060903012301050102190807060504020112150e0703020a02150709050d05 74
    0x118620307000121010b002e040340100900303103030510100182011a4881a031800d02038002050703030000e4030300f801040003160812038200c8503180c811550b00d4541102d441400c00c951a14000607100c0389401d52075801102c041e95a141c1c16655200840e95540c00303680c620301400b1052258401c031359124007a210203008565030214030641c9507680d03685446c5411890448680083c003c1005001010001110515260142d82d848540340404200520380004402880d0800c0e8034034450319010000080d8100c030f11864210900340e1094416091100c4401c000b5941a048420508054a40030000d0700040c0e000600004180766000c00082d0703014002c80d026118468500d0040000750307010710100a4050003081d0b0341a201c5880e9540840d24442d01200401c03580da550042025039220789005081181941d41c02c00c018100d00022100f2101c2611074400e106141c5000202414868002e80e24861103c0e00140702e8448d09207901410702c2001040c40d0200909580c0005d4aa03550b21840a8003602400207 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 723863507 1250 723862257 723862273
    0x1c0204060203090f0301020a12020d0b150705070e10050d1a100509060105071104090804030b0c030402040b010e030307060b0102010b100309120306030f030c150e0c030d081b130302030708 82
    0x3401601c511300765080d84240d206101386041150020101444010764082c010399840d1076000410042c04080e6403a5007244120700802400070380c01b4010040140100c08440d2403903551455441400d10450b5800304034940c001c03040080d42040702c000030040703100e02904c1400314440007000140c917404503260b070310740349454208201c41e040050125402c8042032074620715040854503400300c410001aa200d001c5c1d035039290380200f48060300003600c0c0034544c02154070810f4240b11840300d0040e00103440a0b4131a51401400e00304541c058004c0300100440034028505120698803450f00806044503e04e0555480e2648405a95100c0c102c401d60080700d620000b6100100d803d00e20500640c90150005041c46e001c030520200f1007078039114022540c103103405503082545240803900d108110078540ca0090810103204000340d404500c00c00d00341e0781030b0115400040c40c1070702182d00000a50700d0700e41c080004041c808010098200178000030f010043c2042d0001e40e20340c0030a1800c082e035441004070b0f41001030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 723864757 1250 723863507 723863509
    0x60720040e03032716062601030b0c070c0e07020102040906090903020705100302070f12020f0a110f01020c06040305071814270a0602090102010e011407051c020406020309 75
    0x220303544541c1105030082d0f0842c80d01d541898102c40036484090f1408140c510034034110f42040040d0450b807250403034110031595503000041c0012820454110150311019564452203107c403030414101c9411007a076110365128a40c40ca0503e5000e200d00f52504642c1070380c081000e94000000902174110f95000503550391410414001f21070a0b50886007001d401d0231202400701e68005040c00070b55208480203150241015020f83c020320800c0001800140094408001d11041c4c1c45810045c6100740c0a45100c801c20381d05164031900c50b08402800000030000c0008a4240300c03c0700c82d003950341130040f00e61305850340002071903d8115a2040700ea96000300c406106400d140e00c50408a000140820320158000711510300100742c00410ba0518140900c60300b43d00407600300e2001983d400c024003038135403404240c1001e2019600c1042600c3c0550b080c403521114154052040f5100071004d0001a0801c0d2039447c001c0b40d06a200a105032200e582280e080940200984001c0008100d160011603954180340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 723866007 1250 723864757 723864761
    0xb061605062403151f0807090614010903110319051b061303060b0d021e090612070504021e1603080f040506061002030d0915050a0c1b0206072004 64
    0x91060031080041d40020199140041c1c20309078248900304e0024144d83c0c0d003094103880500301c050b040081c48036a03400601d00038045001c0041e121180c0003804265111402c423140500b448040c2400078840322020404120304440ba5048210000c06903403c3e07542d402d00c0b600b428104ca981c1134500780c003d0605100f42c3d0601100210f1603880965416041101d4210f9000481c001444041e04146d103130051840140d9032007800c2100c660b4010f041c03111444086040c805480a0142c65502070b12201d030100da05460400038804000241500234402d150400040c40041e4000103280050a0f0b0303030103400c01c3c05442c247c001d0700d452909041c0a50041c8520305009011100252511094504d004103000c0810404154542e10450507640c0f140302d0044031000700d03c3e502c54020f50b080218908100c142c10089203000855020903800c406000b1501c482e104601156034004201d40401e00804007107003500c04410010b5410340c001004582400c00341d41f03450346540ca600c00c280c100c0740c881c000c500311180350134 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 723867257 1250 723866007 723866041
    0x1507081c09081903110f07060e0718110f07051b010513060c03020705030304080c01020601300c05090a14070c1707020a090e070f0603020f0406030b06160506 69
    0x411401c0c80022a076894400d8030b0311034034800b000303406400303291401e0b414080d0f0408143ea012001c031241e0780d48101c1c1d10b80c000c4c0f900010002c464150800e10205080d910000b0400c00f80c0c0c2a0902a260380d03180c1c032000c1c4c001031000090140d100382041c462601c030b01c402d4002030141e07640290042d02e5161121b010000200b000e240213103061080c1800f0100d45600c145811209881031402c00071048509801c00768030700100c590110364540300000d0041154440481e883d01d4900b403c0c1c007210403990300c5801c82992840d5807210340040544444d4200c416144a1551401150150340e030482c0c0e00e40c80d80040360b1049401c42d1500714041d118149180c5118010004a601ca400391400030901e000680e0b030040d41c91038060f609010600045102c105655400718580300a00754070000308031503101068400e4480c1c006108401740391a10480c00229a07020b4000c0b24003680d6070211151415007010790980050200510441e00002d007440340b810f031102a0400d00b030440340540f008002624007151001045200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 723868507 1250 723867257 723867307
    0x20c09043005090f01110d02030a03060605070b04031404240f0305150402031509040606050307170d18090c1709150105090a091a011d010e0402010c02150708 69
    0x106010300d040c01ea808010345040034404c0340c0800009114a00498000024451780749150180c3c0303840035002da0300080100000d00041c0c505100041ea9000c0540b95405810000b40c076490f5810b001400280c172640e03581914400142a0302e00f400d89601d00c000303222003003108041e42150800b80c0c0345040c580001241c444070125242c240207902c3d00f0300c20300c0900303001664403e01513500480403034103c507a080c0d00700030340c001d001e0302c000c02c9480c0c21300309000588242e208582c0240105040841c0d415101039030300510340308020050044000588040301c5061b010449012507580610020513000000d0081c0c00000c0000d5803000802500b05540400d0400007414182040d8403c11444030b400818440030750444400300c5442155039104030400000c0c000001005004810144165072000c004400440c143c80c212003047e640260903540b06048814203000b0362680c51403e000060041d03215424842200d403014180c0106010841500c1c3e405800c00f03141242d02000100b5654800324640000c9690001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 723869757 1250 723868507 723868583
    0x30e120405030a15060909260909071b020405071d040b0d0308130c1d09010515060a0309050d050c010b040b0a0b0c010612030c0b060901060915020c0904 67
    0x110340300010f42d40c2c000f0081c0003040d03080c60045030024010030340c1c881e0380100b100718024050704c0541d207000c1c03021082007040b200844101c0d05540200882d82c405495251801612090154682440c141c03a106152440344034103504030028040180c8030ba010b190300403005030301e07044400c485001003e031143d50309041c9180501e20300404007030160796461008624980609013050340e82c071a00400c0080c05c0300c1030f01c00b1341407031801000003c915608841503002d400440110401503252105031a081e103c05849418100054074402d844520b4404000c194070782d4a410001844c0c2d03000e59580b403c01da1a1161200401c00106145501941c01c1c001c1e6510394408480410a64106000140c00030002c1d0154000400001c41c21510f60a42540000098116929820854122450001c04400814008450007c02d01c4045140c1d4101404414141d6595845500c004d50614048141e604050a41c03038045110340300d18881c564035903514450043d80658401d003221401c0580740110fa01c00e141f03c054280c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 723871007 1250 723869757 723869759
    0x714011b0e100e030d140c030a020303010509010b03100e1e090c0109060311180a0315150b0a020c1002010f0e0634120603061401030b06010c08191e030e1204 69
    0x190b004200c400c1d0b41c3e803c1d410306c0e40700260186244c030007e01884025140070b11001a10b07482060b000409507040303441c11680c01407603a81f190182041c500003922500e00d043c0c0040000d000301c0544400f0385034002c2401984440080d17915103565840c100903240c042c5150040403d60f0241c0d42d00880318406003200381000c0c02461180007100840d40f01d51090840d003070b501c00079010810b80d20101c07880010750700100b4681e139a034403403200040200204030311a0f40c1600a103030b001401e500c00400362500540550050054540c4e03140610251242a2541208655940328820302001e058400c103489040440001c2c44140390424105000001c0c031099101d540e000002e42d00b40a044084903030302c17011550314002d0002c1104500c07140280010b0b0708001e05803401c1c580c02001d02e01a0141f000d0480c0d0103800340302041d481d504015662111038607805041000100f124046030341412040c406000c1a0349031103907030044402e501d822112444421440000e1300e4612241c0c0c0c8150804c400010351545041241c605 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 723872257 1250 723871007 723871009
    0x10515010909090813030302030309070f030201050a21110403120203120c09010c0c0608040203010c0f0e09040516060c110301140612011401060e090108060403050714011b0e100e 78
    0x140d07407103100d48514181ca07685002d081014440c00e85543c001e01c036440b4025243c580c41c0181d1207070803c403040e082c14030541360002207040c80384d000c00003243e4040c0c4440e490712611180c119003c0360480700d050b0f1a010481c0d14041046128801c204191210b2441e02d51034a040d803620341d8003c48007050a00455006202c40b168000d0513000f0035030400005000503985140400051f60040080b600c06003c002120704c000961a0300280c445204031700c03c0b4001c21503020a40400d80301030f000004d400000a187c0400b0140c00d050510b00c20342c02600441c00c0b105008401d1518084800d80d54000c50005540c09c4040300c1084802c01c0c2c92406800110000e000600503075500e4100e8401c02088180f046005090b44048801d00b03501141a000d83d6000700301032036854842c00740001030403000042c0210400343c000590508046110303401554181d0351a441c2402d940c94002800b00b120070072044a569a0000c08508140701c0301010204165464612001688404001a440500d100342c0107020182101703101e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 723873507 1250 723872257 723872267
    0x201809010b0f071406070f0e090408040512030403060507020d14070203060a0902040b03161d0624040f03111807171012080c01060812040b07110405160201051501 71
    0x184112400703425207590f00c5040481d00304050352140d40c62400351a043c4540c017644240c0c09114840c558655403404406035052010042040b1406081b001702030009204074600324100d81d501d80300401c1124100350301c0f0346410f42160b00a840b00030240c0d201283c074034080b0303410407501d0a054814801203030610041d038010a480303500007022a481240d91b10003400455849511080b014800035003112511300540c41c0c2d00403403102030300403410080d0500c100d07060703550b0100364a40e1060030050466070103480312514600000014084201c040d000501000c00c0c3e08808401080040d4080c8607400041a0140e090084240c4d000d45a0000019400e0401800c240c109003c6400f58403c000b8220650741d070b08040b46042040d07030700a241800340c1014030751300b84482c841c003411070403c000000300070b240c1e84d1f5034060b65122122204107142c0c201c103000c10000c1c400844054a10349000388240c01d0503660020000b02180c100304c80c41d00044066002100702664240300c2c00c0c0e030000c81c4021560f04003401500281c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 723874757 1250 723873507 723873517
    0x703050a0f020d12090e1503120703170a021309021602010e040615171612021305040203180d0201200706020408030c060f1e19201809010b 61
    0x4145080780e04448210b40320b02885600c819005143d80146055560700181641c2c6144503a049072801580864140540903040b10309000c801801024901d48003516200d064100c0e01080d400d0006401c1045400820a84c102e407080300704002c0140e485680c0310804512055a0300003402c014414001c0180310800640e0b1411751a0b02401c00403c019150400500a408142c028030840d042c1c9043ca00759190700038514000103051000919074a660706400d03218201c0c01c2c02d040000080b004802c007034080c0000d500404d941040182d0004680380c4401c082400e9070300965940a500091a86485040340c046c0000300c41140350f84000c0c403100091540c0380c0840e4620085112181c240050801c007086050360455000f04106000d42e91074041941907503898000494040f0f003100b460b0400242080401c2800d45211040b1011460298039809031404940300c030301c80d41020450b51a1042071082d16417031503003660401c0d010b011a59601c501640c0fa000d482c1000821401801a00c005122440050301030b18 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 723876007 1250 723874757 723874763
    0x30c030c060c08090103151802070606120c1502030d1a032506050c0319050c0607090b070308090a020306011502010b1509120307140a031d0f09090a081b0d020703050a 73
    0x42807c039410000c0c2042c44910340c0c0401c1a240228101107801d945c0d50300078001180c0a00360803c421940e5402d00d12202081c00310003000108034240034002e14400426000391070900c1d01c11241042011041307441200c02280303660440d22544c0c90030f4101c510f410407440301e00c10b003180158040c210180c0c0c50000031304d00c140a8207040c004003142d100030713b2108200b0340303c40d21181c80b0840d080003442034000d09076a220840203151401100300059149014490580c100d0b82d0b02640140751903540c1e1012501880c015041e400c0d40c1c080c1560100141c0e07000c0107040d0103030410146444081300e2664000e0300315481c15052602414031840c45200441c5d030f40c0140c64003403c0650341c2000708410340a04506500c242d038401003075032071745e88074100e441c010021300609054441c0c2c40d81c10081015048485c0d40c001c00c0c440041d44200d20850071002c50034281501c50704603042004444100041d6a00c605242c0c200100da415403c821010180381280200005071404100707002a096050540e181c10f07486845000307003e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 723877257 1250 723876007 723876011
    0x10050a0c24061401030b0a062705030f0114010807080a060c050c0d110705010c210e040e0a110a06020303070e06190201090b0f10060e130501030c030c060c08090103 72
    0x1165244010903040394111200038002c001c01e90312554907030758010b003026803240000d00d049a514420b00300741c00d0307032810b84090b911600e00980000710014914032110040340ca5507050a500000c042c5c60400c00042e20310440b400224803840810005448000140d002d11140e602c1050200301c10a004601d80001e160401804600109000d00649251180c49403102c0070f48100561041501c1d0b0028114800b0100f00040e030388015503c0004480a20600304060459403502c12401c402034005815801460f50340e0904242d0151844006011600034002403c92030300000c00c00c5c0102f0102412034114034008460004200c1e09080c0001c1d52408001c0c80d43e41880821000b6503515580c0700b0a56441402000a0301c04508261034024044c0c41c00740f41c11900300840801050480030307001005481008103c000d007101c1490520100c521805002a141e00b00e500c003a59280f20890a01a00f03000e540600710742c0d07060f02e01e103207841f043d0720105501620400c9840740b01000019031174400c48480480910340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 723878507 1250 723877257 723877283
    0xc0105091512040804031b06210b030d030b040f02070503090613081f14070219061e090b090d17061207081c140a050a120c090510050a0c 60
    0x2844a40b10390070754103145504440401041008940090040c2d912485802c171a00a80003c40c000c1d00c43c00303001c2d400c085010080c1201c0c66022800310047c0c503a21b040008a1600074810100c0e00740a03840e80c10400081d01c80d1082141360426000302001c805034050110300d0203086440b401d8aa0007041c0040d840b41e078001442402801030a0380d840040c3c6090001d984501d42c4100c188101c40c1c00c41e513000082182000500e04c6402000101d882c4988001e0300545207242c44140003203003400d024603017103998640c0c61100884403503035000141c21020100000241c84002070608203403035071000700002d0081e4030881ca116226580310f00311801c0458005c1c610003854454200068441c50314442d08002446809000240140700080b004011a0050152000304464500444442c1c1c0e9071400400c07003240801041c1c1e061803042e00100000748113071400406134890111220191392000f06d031800000c841080500c998507064000c0303120301c0d403d030400510380340005274040c0004120380c0003c1c04244181360 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 723879757 1250 723878507 723878539
    0xf010503040c0905130201091521020d02040b040e0c1c050a0f0c0c020a080a02010507111f020705090a0603110114130f0312090f1403030d050a0c110c010509 69
    0xa046000d04003d420620180c5441100500c0f00380000c0344c1030307000840000000030098100c404e1a01e9840303c50355161044d0b0311125202d098140b0448a004480b9420400d8500c00c0d0315506c080e0000c0e0800d01151952145030130070344445201d01400d07034804030768104555200b10170180140003c074004018007281075503035001c2c003c000701030300c0c0c89084100b401c02000031510ba0380042e00f490103038800c445404c40d01e80c460807107654901c442c45009010481c100400d02c04200da4001c1d900200c0001010040c40081031020107101102d46c42c00c181c0560310210083c4080d1500030304060313101482071b004029a500e075403103a03c00514010249810700ca0341001c0520380001c044200c1e0740300001d210304a40b1f200d0b0346501c0c41d0b007142803a02c030030f55050b10680383c403c04062250b2800300c01ca942e00c0c0c200c40c80560504c030031860f0342d24500000d50b0b0725200400215400f07940c9402103030710a01c03d24200003503003248058050018902c51a030130045811103200e88207a0f070703004001c0d80c2c8040d80076200c43c521070130382c0c1c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 723881007 1250 723879757 723879773
    0x10f0c08192306130b031005091213030b070c0804090e070506210604050906180c03120405040e010902060f0a050c07080106060f0216141909051605090f01050304 71
    0x102c4000081100c1d09010042400150302c03401100f05481074864000c02003014012160304030a07080d45a046081800d02e04420781e00410f400044120945071005010600740c0410361003811280a040050b10080051004c00d030b400d81d620144508100c0040c00e4a5590040c2138442c50080c484055a1460595403504042011601800d800340160b50345084074111405281040d40c00c4a00c400d15500010300310342024000ca0303004072660750007000740e030b19a4405480000c0511404462a10803507071f01000c0c6507007c0000d05064519200800e40e19814041808159a0ba001d400d1226030b040071460001621003408403401803410002d0769460b07062201080382d15106820740d00000e8800e0b441d02145080066020204946a075100c0c07104072110361200380e031134143c100a00881c80d0355100d0f0802803440360140103c50f408000b0002c0f0001c07054600d05030207074035098000350045513440e401c00c6130a403030390041400c0007015030070011300b0188094002042d5904000795181040408408201080280 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 723882257 1250 723881007 723881021
    0x41209030830010303030b0a080a23150a0603031b0203060a05192423060304030507020405040506090d03062111030d031e0902010c0b0403180605030603010f0c0819 72
    0x1603400b56810703596905005019084008a440c420a41d481000275a100001452a0742513800450f00d07120101c07400c113204004802d884040c225004400c0340c15090540b084a5620812040c2c138001442402c600700203002001c61032034420340c010407241c1c4a015030b0b00010706c164010340901b40818075685d1003a0381e00344060307540c00303038200a41020046c03801c0c3c403075040b0031400c2c80600b04942094581d44060020583c840750006d0494400c480c1c45607107030350800f00000e40c0d115001c0d0410914240c9580d011500300c4800322420b0359681c002308288001140c09004094a03408689400d004d201e040c503078a411080c18040100040c07962084c80702d4100410300351000304000001702a140c007410210800350190004280c89005036a02c1e203041d2901f15504d110303e290954041e52100080e0b403d540d549600c1840142c030940a10240301060030080520010301e1015220035074840c2e4480c20118149425200c102c0c0f08414280e05210b000c42c45142e210421325130181850000d07180007108010390704001c21103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 723883507 1250 723882257 723882337
    0x30c030f27150c13030818090a020705060a0b03030d0b12010c0513050a031208071404080f120301150503070519050301080c0d030e040908091002060412090308 70
    0x500c4000c0c40308601d000c40e211915080d00310074400b1954400509540c00e00c640001208090010002800850034041c040e0100b080703001103032100c1071480c2001941400003200da40450980005401d01044001e01c6402c0e0442600072043c003109a141d0300090f207900403080d080c0c6404d5070b1001d403004240e80d040000d00840310014020013050118000041c0194440c40e032400824440a81c00103890038090810021690010022401d1810b40d81c0200c07400d0030301520032401c00c15640d1101c0b400c2807400c001000240040030040001d040005242d50821442c0074412084400a02c010000d5041c2a01c04035a00d032904d1170840e40e04e90701d80c841917485000d20f40e005041c0d03801c12101c00c00d18030341001c02141a1950203040741c84585090040100f00100d01030001c0004800302d220442c64101600580301880c82492410700300403a82d000b04001c40501810072005038070800034407003070101a02940d0450481850500c40c2c250640d00c070030b1100d118450300c0c04804813030303c5c4510011019454001c404200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 723884757 1250 723883507 723883561
    0x6090b0906071b03020a0e01050943030f0e060a020a021f05040312020a09062f06010608090a0309140103020904141f180c0c1e050106050402030c030f 66
    0x4400c90f04400240c01601089024000414021403d5411609030301c0c1201c000604050fa1aa109003d5444600340103480f1541008941c0d1100c2c0d801c0f002d045200401c6117a8007009a400d0030012008040d603003520010810b0502d811111006c01401048013030f481008880056560034601d4001c900d441c0d03901c0300e0b008000c141084a0036900c19640c02260080d4001d40d01c0018138000030f07e0a000300d00c101200000400d00c2c09204004480c0640000c0c44403482810300111105568011141300c0d04651346a010503820100043c0a040e8001090b039403c80c501c44020000d85c2040d80e00509a001c41d409040482540f044001d00b56031320a070100e868682018000303101c205001480145101c1d0b06440340c42101d1a8051507096200a84030404111510b010b0070201c031045110401c80181b412400120401114070b40c030002289000b00000d4000c0800341c15062440c03074600f000e40c01c483d403640000d441a8010000d0000200109054035045101c038109101c0c00e0301d0301c014100c6844103003040315803408 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 723886007 1250 723884757 723884783
    0x20402160f060b0907030507120929090706050a0921170c0f0c010c020f12010c05030a0605060f0d0b0a09060b220321031503080c0d030606090b090607 66
    0x1c42c2e5034002000e40740060302e5110745a11814400d0702a5841116000c0000b11152003070b0306500c80c260040100b450050040301e264074100540c44000855501c1040000d810b043c05010040c00c04012410060881d07151803404d04e00d901500070220b4045128240d04540810f408591262611205440403544040c0303403180c810510501e514287c1101103c11458043d00505113914840803850701d41065050b590802c6c1d8058503420400012640c0c495031340c00c4003169141c1d84001d6001d01c07500c0300141058490f1034aa03d0200c01034029500c1d9504098003c40341070000b01c00c2c502e841c4064400c0c4411451011900206007004500c5200d0305510ad02603003030030820001481d001850060408220426480071040c0354600503010380c0d4161700c802010085000317100d5400340c4929290085640c2c1e80e00d40400c80c03102c445545d415585160300309448464001810000f550410440115000800c0c2814090b0f1841d114015100c03015a10134420f100c400001d0f03002582c0d550108071401250300076005200c907 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 723887257 1250 723886007 723886013
    0x1a040b0d09050c0a050603180109050a111c080a12180c1409010b0a030902060c070b09091e0604020f120109150b07081c18051501050d0807020402160f 66
    0x1d04416141aa500d0103645030004581c14154055030540324080d200c1c134a5906d52244030400f564004140001c43e550358090703003000410511400409a015040f5050007400c2070040102004c04400021280c43d0b00b1100b0310b001801a0041c0c0758111a00e0814480103d030060a8401900c02035040b01010805100810100031501c0065020f071030450f9205240c0310040f03070506c04491002c0c014038800755014041500407a103c2c1e04810341c1d06e88007411150a088100a6240c0b600401e0f400c402d4a41c3e802050302022403c1035121030760310002045d482c5140080c03590165400c0301c800780c01d06008680015007a080162110704540c0c41a1030500243c0096039600f607500300408480141101800b00001e00240445020090b550420f030060001858051960012105454000410404240c460340d0b0800c0c0910944ea88001081c00344c0064504203d210a40c61003048058006038420303284041da88000c42c0900d000e450b0b1249d419540143d5800e09003140c0b612418044400400520304030b8148410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 723888507 1250 723887257 723887261
    0xa0b06010c05030a030e160503060112030311030c04050f09160c0819020705030d0c02100804061103010905070e10020c061c0c0f02010b090708340c050c0f0306011a040b0d 75
    0x100c04035041c1503c41081c2403032487c3c182d0741075502c00c081e45648000b0051141c40307041d020b2a041d00741700303050005280001c000383c030005420840d41e00c451030a001c20204542e0400d8110380c0c01407401251030070038603e04a02c0740000c941c054a0070100300020400d00b0300c100500c1c0422502c0405804a010301191031041c0e00075912009801240c0c000d00405580c1000e540c0140b15031680b05034000c101c04a44640d400d0204c1e084080200240c0b12030b030f12200f80ca54281c06200045011f8a460180840e02e4500400040d064141a24580c1e019400035000b01c0c80d85580400c010259940454116039501c0d110312425042c41000b801004600d4a000042c0c900e040d00540e014042d42403580003403100b070581c04100701ea8120704503101000700345d151000500c48a00b18910440d142ca0300d0b01010031391007a007440121272120001020010500c403d030f048092000400c8503425400c0219007030302090926001090304ca40b01803183c040c2003c1c81100c00b11602051200362809080e4100d002070700c0d00801d0183c100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 723889757 1250 723888507 723888521
    0xa05030409150b1815120408040501030b03071a37020d0908060109020a050705060705040f050306090a0b091f02270312030702011e0f0e0a050a0b06010c05030a03 71
    0x3400301c030b500500169a050000039143e030a0003542c0c8060b001800d5000740000342c0801c0c10000c1d94640204080007000c2c6415852a0095006889554581d400e00001400701c41003450024881e5100001c20440e40600900c0d81c42e03181c0440b441c3c01d4440310340f00c1081008042c9403842c4050f6a6020091f5012210b10041d01c200c45002c035422a9440403c044055940701101d009040c090381045006003c0d40c5426001000c1d16011840d04910f03204003900c0c0c1ea0706180c0265414000100c001504200643c940101d1030040c08003200070380390324240324500d0b82d13481441400c01491070185000140265005107c903c1080200c01003003c440402003130402e00035071002c4100c107250310214401c95140d03160109607031500c074409002000101c0a1011120b240d400091000b800c40d92212400b4001a0505103084001f01d480040800e440204044035001c0d2a0a400001041d038003112825011440c0098035440c03440d00424410301036140c40004880032001070202400e01e02c00021aa0001c60307040d84016 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 723891007 1250 723889757 723889781
    0x30c0306010e2e05041e0602070f0803030f060f0a08060a050a05060904031d0a2303030310030b04030207090911030706020d0f081312112811030a05030409 68
    0x100400c0e280b0810241038040c000c4400910b10310030f140c0003180005040d54584116a0404030306103513441d2121102c0f400161005140a0040682001001d0b010000c50001c0d001400d42900c02e42d0802c0c8c6559641e000c010103540d6551040d101107145501c0703a2600032200312020309100d032401c1d12040007641c0c800b000d03540500701d145080c0c00a40c1c81c441c1d03072103560302400d4010500c0001d074441c0c0c0c42c1213a100541c019204081e0f480341e03600088a0303444802880007025442c284c83c1e1140484002001e04012542c8098041d400801c10440a400d1000c0740d03a05580d842100c0310b82503151410202c0c50050700c0d400000340c00d450000c0100900000e40300c1100e10713100440440c2d10076622800300303d841d004600788810124900b40a445132103400ba541c49544040d080c20f000404400c19180d1503202e00d180c00058000c10a8020540402d01c024009902e0307680140702024500c4000403013480c0d40d0340e0301754409045608000d6900981c0c0d50180b200c4409c154000084030340315070703d030f108003001850b000c0f002c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 723892257 1250 723891007 723891017
    0x411041511030f040b091801141503010503061f0308031008010f06030809010f0314040b100b0403020f04020901030b1206060a0504181e060203010801060e0a09020d170c03030c030601 80
    0x190301c100e00001c11074114180c04400b0b5410549030455a4003203801c51b040065001c0c050410303905090320740200050081610341c0c4015a248040c00a0140f0b07443e40c00109084d4040c2000103010645001820031b4000100045810360a80e1401204c882101c44c0c1d000140160000000d0050302c00b0038070090010703500020b00130810804210ba10300c045600912004050000030700074070b24198015250440040c82d14207010891181100c883c00808400711800ca0320744c0d003201c0c103011030000d0035044003010b0940d000756286800e0860700013840111017003403428803131900000d1501469100303801007840d030760001c2d0112040d081003000140d114101150007038050310254030002220b103410f0080b1910a8024107020750340d040b8586400030300104109110050800c4002d44400280c1e17039200540c0245080e900005140b42402c003101d0b11030b100030300904c03203450900c403001c00540c1e07441e00c0c480f4440360b004c0100c82c2c001d00403411658950103554000c007450300020003001105021180103500c82c200983e10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 723893507 1250 723892257 723892277
    0x115090f02031005041d190303060e09060c0703110a0c0603050c0f0f0c0304051e0306070e370303080415090f240204030f0b0105100e01050904110415 66
    0x204604900084444200f0a030850000b000541040e911112525a003001c0010b00d101600000c14581511801010409030580310100d06145d03043c890300016086803410600386042c40285c46030b84d8070016080031000381002941108042c05500580600b040321070649142100031f00740008032900c1c3d0f11803074002c0307800e04000030710070341c5403070100d03103605401607003182c148840f590440b425a008400804603512041201140541d58106801a089500000708101e05001c50505080c1003000d00740320103100c103401006405990b44140ca8402188440540d00800406130440d820034520400300d40e100002070b41c011061503403041c034031881b980c082d80c0501200a59010600304640d0442405401c2070f003640d01c0040040c844002c0100310002c4001c202d000c01000801c090100e0380180d10807640000c0900c031110800c40486099801004119000c104003007043e00301034541ca548450b464100200042d8030308c255907580d401880c110a0b8451050b4845803254004a058503030705031400d0100d030007000c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 723894757 1250 723893507 723893531
    0x20a14070510030b030a0203061906080a2301060302100c05070b19081f0e041103010b0a061803050304030b24100507230d0f1d060714011509 62
    0x500c04200c5101401c80c401020204504030000d000c4c0307202c19540350282580d0740d00565400c001c4a1301032081c1c100c034000d0080c8001c0784501194081ea00c2100c1680145c4003090204280202009003c1c013014142c0a003070307003c84950307801008039420082d804440a910300c0c0089900c9028509000d210304100c400d0152185414a198000c4160829500360080200c0c1020b6220b580c1c559040741d40c02e03c52841c003d6484d5a0701100840d00d070043d000b8801d184080000344160b1903100101c50713070250020010303000090082102c1550701d00a203824803501d1901d030200380b4a4070550300300654003c403e0f03d0701c842d02d07843d299083c0f440135244000c10039201034410301100003030140c41071080001070586409000c5500c05840781d4010715003d84900d006a03034001c10041c80f0300b52481245d003d510140400205030b40018103044038100d814400c021200342c00d91040d02420130244035001007102e08540b01c02c02850300240700440402c140c6181d50a140c00c1480c051541034142080ea078078800c0a1100b010740c41 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 723896007 1250 723894757 723894763
    0x8160809210c0409030207080f15241c0204050c1e0f030f060a03050a0b07020d03061d042d03170f0f040203030904060803040f0504020405010f050d0b0907020a14 71
    0x418105280e00710900d0702c01c80d450b0592107029181d2090041da004243d44000c8103041c00d100d42c0e0a050b03e9084640744001640c40b0309620344d40403005844282348400303d030000300c2004000c6402c06016034004080121840c1401c6010079030654010003e001926101001801a0700310010300340424115260a00043c80480c042e9003c4074142c1e140c1500b1075544681c0c06c4050358000c1c0c82d107600462417540100200f142803111580c0c9034003e09000c0d8060a0200c002480c00180c000200300b050301c1d1400901004100504902d00c641c000c100c078450a07211800c200313404500406007419512054500040f540e094401c03081c0394103000b42c41c1c010010f0100780669142c80822682c649190002100141001c100030701140d0304640083c04517418983e101e00441c04840460300039056030390005c5070400c010320b03c8460103c09440c09850940c01d282c078150018240c00f9800f40c0f260709120010074403403400c01c81e961011103080310003845074000d802c1442e006500d510402d801600d8540d500701e003404c0e0140e800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 723897257 1250 723896007 723896059
    0x20a090504060b160b070327050f07050612090709020403052413030f210f0e01020703141810090603050a0e0d18090c0305071b11090408160809 63
    0x40c136502030020b03103c4d541341a0101c8005010105241d541c4c0d4204c0803041c0310f41d5008050000c0344600c800c1400e028204140303002c00307141c40004140d2020209200303d407165810b0303465480c082c0c0c2c408107003612a540d020b802c1005640040200c2440410000180000001c8440e1039464402c09441c01507481c2e9215254a40211208c0c3e80008080b20301600180c800e282c456054040ea00c0c0c084940c41c1c041d80f010000e00640f009088102d51100300c02c41c9140105e1084440880841000314a40912a82c014180303002000550024200c0402e0202c2d4400c0c14804a040e00b85004140d0000c00f2502000903141c040d180c001c5c0780c00281307003500045044000c1d10601400717042d0b050041c4260282c07128101c540150811a00d90369800303060b0b000550907468080d0442080568501052034a0f1000000b4444107400b0741c801c2d15605158441008a110b031007000c0b004800640d1500650340d607a0815040a100d2401d50041d0860001348850078040e4250203041960740482e0f03205001860000b64410000032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 723898507 1250 723897257 723897277
    0x11808030d1d0615060f19020303180a0b0115050d091b061d040e0a080412030810060518011106040605040308152b02030d09030201090b0307020307020f13020a090504060b 75
    0x5000c4d844070720701000a810400e04559010f0b2404101036180c0c902d00e420824040e02690003c002e000000c3c980d000034980700d0b00200c0090001a2070780e00e9010103001c3c188a1a841d40c1080e02e0320011840c0f09070125030880b64005028480042c0070715010080a80c0d060355042405070544001c148544106c43c0051000241c854015250700b41e8410803008000b0402d660b20b8903c03810885000090300800500020425141d00789000c1180e0b04001c2c0030108010142a10101c103040c0c1440340f40d82000c26141c164040344071030000c425880e0010b0700d00844505d444515449584100b00400000e5040584240c1c031a50b0303084001c2e1214445181001c10142c8004e0b84103d41440410b1506180030f034001c00740c14540c010300c041c5813903a0040b0f400c01010610311000205012414401d651300710140030b00500b03e8000552039460b090740001d46900504500038842d8200b11134000c5150750b00c020f10341c0303409144882103588815a44014103810414030526000f2401e0020020351030340044140c443d204e80d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 723899757 1250 723898507 723898531
    0x160914010f0e01050d11030406051e0a050405070f080102030709091a190510020f0c09040c050f01110106152606090901090803040807030e1e011808030d1d06 69
    0x2480a0701a9519030242c05003030304014091065241c0c02c1d800d800b4581210071609501a500d0510b400c000b016110300502d603104800d007907481c140150035090b80c1603910150300f00001030981c44925010b41008031580c0901c900000c010008600f000042d8010f5019401e00d03122081d80981d0743c4000c0040e114030310214010554190b61419860500a48030444030140f0f881d42440c0304d840310700180440e40726007216401a401200d0301007034a601004007a09940d4100d94050881c1303005c4d41c0d4031032820385238021540560700300643d040c184c4e409400344c8042e40340920001d0001a031584000010140d190300b251000650030462060f034040340d928606520115019200d801c6e50f54030040c0f03c00190702a00309412907503160726510103d0f010002860240b0310030130165594803442d00f801400201c0342150b0310b2140d90045409041c0c1b103544880303c144d240d400c0c2011920305203031412010280b049075000200a010010340c075170300c00105512480ca03200800c24464101419914243e54a082c11038030054910 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 723901007 1250 723899757 723899777
    0x7020601260106090c032705060a0209420f0a140f0a0309060e1f0e0c04060e091203280902060d050a050c0c0a080d0905030316091401 59
    0x214a60a5500d603035140701c400880c026982e002c01c10201c440100b080c0b80041da5508808002c40400c0c01c0340400c1d0078030790503020b81e850219290b5a4403040b02400c2c0c0e910345075001030f0f45003440c0c0342e001c2040400b014078070006a014104083d40d007101075484c0404000f0070180c150320b19080f000c5000362881005171441c0d0a040c44080141500c5055003c11040c09640041c440e4002c2000c404d002442c0e600c04541d00800c3d4401c180c030b095001e032229a5041c1b0490780121520203d000d11184012084242104000c03410f01d40540d2441c0c1015030541c00540c00600301800840c901c0a20380f10503001d00841c0c3c00f15200c2845820191205000545070044c00515a52404e1441642000c8501c80b420004070000703030302e501d20342c0060aa035000e04a2040840e07103980070040c2c85011072154540c882c041c2007000d0310702a0540f40807070321440000001484588045a8455100516030112002c5540700044a50320300300b820490744800180c0c1e4511001412400703002c501000603900e151000031060f182c908100b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 723902257 1250 723901007 723901049
    0x3050d0c050303060d02031207150617100b060903010c02010509060603030c071703120702100c02030405060d150305011e0c0311040b18030303150108060f0105030103120507080a090e07020601 84
    0x12510b090003a680b40c07023141c400c200038003407a00040c00b240d0b200340740c20348603a00b104400005440440d8003040350151021541d03070840d200402d20300c032010b40070580098800300100000720203000d03080314160107600e031503160348101e40c0540c0020b0281d0b400c8411520a5a80c000402da60392140740f80d4001d03035070000c1d4400c2005082040003410155004001c0c1c0b07040c0000104160b025080484004005904c114262140640785100c6c0c00320303031285480510710301800c00010942c54801c01c1c4504050395030702ca0103500b035400203080035000b13903034864024050321250700c110300d550044604030614901c2c039045a00100d107029200d40300440705001d840c942407a1410b524005203800c1100014551800c0d94400112030340c00380001c506c5000320301e0006000c07034070381000100414401060a8081c2c0c4c600c5c10300d01890f0303801c9025030f4116a80400f1703c3c081c0d00c3e0030b101c0c1200d0500815400410326940407500a1034140c00800b42c80a9500880400c009030b030b5080343c01c81c1e0b158000e01c220030705850740c2c3d0440112 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 723903507 1250 723902257 723902269
    0x10b0a05060f0a020307080307030c0f02010e060118020c0f0102040e0a02131715040c1703040812070302160e190b0d02131104090204080c010c080a053103050d0c05030306 75
    0xc48442401a1781c200040c45d10340c08101d50044900d240001d0741d651984840941182c04140000d1503480204100c00020706807651f42c1c0e1041c0070300c001844520712607081c11b000384d8040b20402441c000645030410f1b01800141e000c0c3d0491f000e500c0641001701e0010f8a0808588241c503407010421403840c046520b815542d82d84680c41010030500b6021781980c501d0031605001965015a2140703495100030303031500e04809000c007803103448403510350420041005000320020711041d443c81c00d2107016650314000d1400343e10b401601c189074024100c90202c00522a0248800759115000c05010300d0040d5419a80c00e0301122001024140d01200e000b80000160600150320f5a0044507800b001610f4003641a140c100c0b50882e03400944400e400003005d0192076824020351201c2103080c00d1142c402c40465980024030302407001103001304071021440421401010034003503000c94403109010601e0340380720f40300f000c400c91601054505208407015150314621070a40d08250320740100246044d51101c0d410020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 723904757 1250 723903507 723903517
    0x307110a06110d080c2109100b150a021612030e06030402030d0e030c0d050102070c0e0424180807020907050f040302040504080d051e07020c060d020c1006090b0102010b0a05060f 78
    0xe10000d1118503e0700e08030440561407801c1b0741d000c500a0707140c6491006e180c540c440a502c0440b5041419041c2aa255100100108a0020b00319a00c0783c0d0034483c04ca1902880080d4442c0403141510f00069000d442110b8054960003a036500c034491000340240311080c801510029015441400031003440c40c0b0421a44921400c000c081c4d0300441e090500264100200890546641e5030004080701000f9905d2190401001d080d080c403100e514043e100c02000d043c01340130104800d640300008640c403440c07a0340300b1940c44112030303040d2004003a07a050252003600320702c40c101d0142483c800890b40345800380c400d540e402c00d0001407603840c140c119800d00025020180049039001418001ca011075000c034000c1a1144980b540c88030400d840b079014040403c0b034040d0415055402c0b40c840c48050b6190700c070440710120080480965907000c1e0060303152400c51600c0110b00101c0c50202e0128400d000d54215a00c0d028090340280401400001003103500c401d18407941d68440c1c820464480ca00b402c047c040d01d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 723906007 1250 723904757 723904771
    0x207080a050c011b0f1806020c0d0f02030105040f0b071404180609060603090507061e0c05241f120212070e09030d060e061318050307110a06110d08 65
    0x82440284e02e401911031802c103000140c0807a20000420401a50200d806044c11801d024100c0c0b0740b503d4a10043c3d283e8003440703001400343c488a1013200074807000c1d0342d0412169901030005c101a19050030022841c1c00d002c00105c8118600901080707039248140240950208514140c03844c03e0f150012031201c0601d0400e41200c10fa44580000a078180e41f03100da00028800350f02e021505074003d00d4410300701030442c0c00585c20700c007495642940741c0428180b0740904000c941400b61a03e00c03139080440c6001d0301000c200c50802a41400500354075440e4041b14000c1503500d401d8040502032409081411281c0d004400c040d0343c014000c2d00c00352601c40420582c443c40704003034071300e599242c4119145045044650310120343c400200381c10141c4132846100c00400141081003618205440010a100d948540b04041581c0303504070032100d8102c100b807500f22140d004080720b5840713606251000341511207007580c0344103800884000402ea070140b1000346252000c10050804041c8043d000ea407407070000340200c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 723907257 1250 723906007 723906011
    0x5030901090c08010c030c090b070b0c0c0f0d0908070315090602040b03041a010b0f03040f020109090e0601090614090c0a210b030c011d09060f040203070c110102010207080a050c01 79
    0x8001040010b490507001d0311107080007043d4821941000f0f410703039010000407000c10074401c41c00c2029070306400582c4c0070b466002c00d070354090f5240d1410f1210315025040c4100114004c1022004080e00c001840d8146481280c441110700c1d99070728612500c0b040d452101812a10380d242100003815556404a0309047c821640181071a4a4280f10001da4001b1507044550502c02504040c210201c801c00d58010301039001c0341c600e01000916400b00500001d440242030300c1e036680303504046a01030910000602140c08003008621000050565203810a00c6031000c41ea1506001082c0c60ba13900800400c050000350088195803901c03c41c40c4215030000e501c0000300070b900e6001c40501e54441e804469a2000c0c00c0000c20900b5002d0101810444c040d800c06044c049031200d412450258004a109800f030122000d206ca81c1e80c0b0804210000c000c0551554820b10010801c1300c4503800030340703d0031018060b215180d20b00b8001001a03080303109001c40034201040500502d091349120300000c088400c070502c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 723908507 1250 723907257 723907271
    0x307030605062106071e1b11061c0e010e0a1211190303050f101401030b0901030501020418021c05060105090301060303020d260103081b0a03050a0e03010e060705030901 74
    0x15141c00500d58002e0f804041c0c2000062000d4658041c2c500340a400c200b018165160178440e5010302998040e0003008402181c0f909407100380300c4030305080b1440d000c0240a1586c1c40b402d008007072900c0e040310300107110300b03525110040513604414030460148030824001004102110340714940001050303207440d010803040c0c0b0601d1a000f40c0610110704490310704440c00540d00e48601d40502601d500824285010b4947d508100401000e0314001088a1003010400750000c00e1000490141c4560b12a003904043d4041c0000b040103015030007001110442c8580e20f00d00e03600c40c410901a4031511242c41804040d02410020320ba20302e6100302e41041c8141002403903e015540407d00390b910a5009a0242c0c00c42186900980d4200d100d580d980111401c1251841e9180700c0401101203060201a0042002150404680e00c1d040710030182c201c6001c5c2252440c502902c0c3c01421030740008582e07400101d840b800ba520504050190500c122084000340c4215920a04211800d4000401d0a8559922600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 723909757 1250 723908507 723908539
    0xb0f0c0f040803030a0623010f031116050114071d04180c050a1d0109020a0908120307090902030411040f1b0921170a09030c151d030703060506 63
    0x300910040114030702854407454500390a20844500d907029038660b0201c440700480255248072004002402400d011220340c1c14114100c0007803480c406000c0c500e80380002d200100000b001910702109106000a21110300059039003003000100b0b646190209269031412004600003440c2c22041c4031020307000050b410a00e4114a5910010890549501e0301541040c00079091006510001c0c20308940c003540c00b10325003c042d1403110030502c0b1707280c41e03a51701040401820348900168001008850112201400650110007040c2c0c000e80d0050042005841d0000e00e100d20740c020360b0301c00da4000c0c140c22826404c0ca003d00014054600d41000065621445d514000a4103910350100c1c090a5990000c440e085c800e0281168180890114640d90300940d08030005010401082c4110761221811341c0320090b414007520350b1041d903007000300710b40c11a980200c0c50310b1042c40c1c80da034815043d0350f89000701601d0000e10005014aa0202905904103031002d0000c606a0b0b00141c1d080303400582409103001d407402c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 723911007 1250 723909757 723909787
    0x20a030f18091b051804180c0620010b0f09060409080c0a1505160f020c0603010303030b10030e060c1c0608240114130e0d080702010e0601030b0f0c 65
    0x500040d10040e0340c0d94203800b10705440f09000600e8101030030040e1400210144240701502200e0019110300d403590f501211000e001c1211f9103165902618411f0076644424000c2c10740c4000100b4001d2404829041c0b40b030b0450140203011100d100904001034003035007031040c8104e00100424240d00561240c000400043d5200020120f0311645005003400c1701d03003482c0c55035500c5c0c00031131441201400d1200780f0121218500c01c403d07000e280ca040403640c4002c01c0710300341d0601d83c019407516400b5a0110001051580581000003440803c48004421f28101041981207404480084039658003120014042c51140c5000304800d042c52602c040350400401d0450b401d5401c1504006283d400c6039040041d991840501840c0c5e0f0092480414510b42c100701c0b098081c00d40c83e8140038032030001d022100b4803a00300c1e9404100d003401408140d900a1080c84405080810700ba42d54200540c607010080714240004214141030325484040d80e61161125003c1212240c009890400c0d100420800c01000700464 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 723912257 1250 723911007 723911009
    0x93c1b06020f0705010302090a0905060a0e040302070303090602150a0203070e0d060605030105100b0d111908060f011d2106130314090609090a020d090510050115020a030f18 76
    0x140c1d00402c1c50581c01c40d1a41e040c0300c900d40c42103040c140107018104c410354910b02c621064aaa10800090540d00c41d000039203039011035480980000c03151018001490307070100d880c00699000b62075840f045171b6074060480c4c1e212445a05080100140404a1300003000c0d070300110b4012203079251884005c0480c01c001150840201400c603006030380e07080c04220342d09081c0078055000002014100c2d806140840b180c1c40c5208074074229495503034031124035420380c19250030b42c4d40544030030039400d140751510100034210b8036054815500c903140300450001d845d0703c43d4500c0c60580005000d924408204502031005d544c4801021114480340034100095003401080402d11a480c6c0c90b8042c525001a828040c1c0540508141c10498100170417145503140c480f0f80440721041c2c401e40740c00b140d950301e03c0e05060003800b42c401120303000740c1005019001c0c054005500c8070110303000d91040215136030310703160010980c108035130384000340c1c0285a800d40400c0c061100d4000f004014188001c0b151407604440075802d81d2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 723913507 1250 723912257 723912269
    0x30e04110a020618060106050d020d0f0504081305060a2a060e07140a03020603040206070f020301020c1f05010501020607051c0c030504050f070e011a0408030706093c1b 74
    0x720100090035454032261101c0c1355000028240c9541040001401403040c10101c000c1c40340c0000300c4ca100d040e0142c0c8401d01c10059500104140d081500c1d01001540c000341c1216400313a04003001084a141400440301615000d0b11415810424101c4448100c9010444803030201344804140c00400c80318020a07801c4070001018000807400d040340e2001c3c040f4080c80342401100031a1082c40180c072240e088a40041d011144a500d0b90b1852401800941f85c0c800c00075003650010a50740b487c0200081e8143c0d074884501c5100f825031250340044e808a80d024800c1e0341c0103038045008950b5650080c0c00030841c815044000c09146041410001c040d1150042d0050029030b0303a000701b000348801840030300311389100c1c2805043e0315031401c1c52002e2040c5042c050810207802c624200c0680712100f004440c020600c000a07607484e10410700385035009101c0f092064070800e05001c4001060b0b0303c50003103041030008981c0025550301480d401d00034030b02407552084682c1000184041090406001c482d0000c0c08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 723914757 1250 723913507 723913513
    0x3061e13020a02120313140a0c06050309011a060f070503071b0e0a1401060f090e0a151e090c11010e07030516050105090409051f05010e0106080112030e04110a02 71
    0x8005000780f44c40b8a0300031107400c00c4002d0041c4a401c5554500e11020150409500310071003c030701040034106045803c000b090120445030005000390000061031080408400030001d822a4130b80c1030780210800107102d80c3c805410008840c0b07207685030014040d40d5000c3c0048074280f401e660380302c03600303a800d102000301d600300b100300200720207072008600ca9072260034100c00744141d160b480031a11601d43c040c02100240302009014108180c0b10f040c55500900040e42e0181e02c9050602e0404010008030b101c2c5680d050401d01d010a41351044403071088115a0011f01c00b00036840d0a01d014000e00940b00301c4010001140440b0050850034040c1042c0c50a044000d84815451403038824944841036041c102905d22000041040340c0e0000161070004000fa81c02144821035440c0040c181080d40700040c2101e5188030b50030f407001e4070a52165050b070320f6010202c141d0ba40c80c6c00055800f120244540501040901d85000c002842025602d0300907101170004940314841030035111207500281041c3e00164 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 723916007 1250 723914757 723914767
    0xb131a0a0f231504060306240503190303061d0906090c0109060809010f050f040c050102010203101202040f05130b100f0509180a1a0a0b0603061e1302 66
    0x140900c108940450114010003010601e601c200001c1ca007030350b6000d4280300442001544200081251424140c030040040110540702d00e0558000d0207508189140507607001641c0c404403440624210540f440240180f0106400f8425140c040540701d404400300754489100103546000c07400c04010f207003007451604561340b5200c0d000c140b80c64001407841c034a90388140140c00c083c0c0d03040321004040d107580c1e10700300d0655036500785602d02528144400a40d81c0780350030100988020300c100154055882402024801c90f5500012070a0f0b000903550b8041d1350302c0c910b01c1046034580d05030704811140d201403c0070a8110345244071404a5000319061107458031421f80c010100f15103185120b610a0290781c00000441c1002400502c0c92200c2c00741502645c0c001022440ca40c00b84105840d12a41c0c4100300c80b0300000a19056032800b218580d800010030390100443c00307912160048044d1640040d102906580e01d030401c109110401c002105070b502039201e110007458948601031920000c0030580943d0310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 723917257 1250 723916007 723916021
    0x1c03060302030a0614070903021c02010c0803040b100603090c141309060b040e010608070911070f03200f0a08090d0506010f0e01150e01050d0b03030309070e0c090307030b131a 77
    0x21500c006c140320108402c0d00e5080c00182d4030b20800e01c41c0440303844103540ea1552984010707a140d41e04130001400607603003c8100000c1003180d01e1800c0c42590140c0f02010340b6544c0341d03010340a03030300360060003801004085004d02003040c3c0b5400081040a0060405118110520075801240c01000065501603142c00440390b043c10107004042c1040c10080080001d1445c0142c00d80d140c00c890b00aa500e450780f0f405002c21400020000d445542d0f4200e000905e140500f460054228914481640507541071900190f0b0007150110380c1e94100d00075403019081c1101103580b941103960064a1840e48a0440c3c0380800114208002182c0640a0403102d002e0080c18001e45141c0e40d081680858107141c9100c600081040e806100e10030000e20070f0a0a40d120741119072114003500c0f41c40400c61f09484040304000142c0c000042a5048800510921078252110020b02a15109541110f50941d005007002c00000e094001ca1a0744141010b01d02d203003603880783c0d0f203020400c0e03c044184910950b12006005507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 723918507 1250 723917257 723917291
    0xc0f0803090c0306090a0812070302090a0e090606120c0108060a0812091309080d0b0d08120601030b0114040e090f0105011508070e0a0306020304140d02030c1c021c03060302030a06 79
    0x2c01708001c001e01a000c2250741d1300d24503201d40c0019014010540011962690182d019140c2141009280d40e03000d036203610070070a1100702142e104e05944500ca0105445080105c1e01d19001078044001d001c001079444015203802d81c000c3d000e45c0e00321030200c50000d8101e90a201c4010544202d10240d41e80e98011000c00c543e03035102d460079042a61428281d0800240e580c001c50351a410410800303d08011050000f851216400d480a40081c40000b0000c12100040b440c0922400007601c1c1000381e01d0700803004444103203070820400701000c000c120038001c0e903d503c120345038072020001c1250020072610020f14250341e000e0740b00c150130900c0e050f09490045d4001c40c0c000e500c07006ca40b4001107100d0602000620245442c80090321150b40000810103005201240304803c1034480215030414500713010007562603000042c0400d0714012807104c200846a2901d0414680c4c40c60f034014250800745501c500c40c0400a00c040209041c3e642030000010384050204200d000e000e0a00001c802c1c034820a6820 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 723919757 1250 723918507 723918511
    0x9030e09091f0e03190306091a190f090902040207021005040e0c0903030318010b0d11101d011b0f030305010306050c03040302071503110c0309010215040b070c0f0803090c0306 77
    0x7683c1440c0389026002000810b40e0141c0c05009105e4034400c03e01c3c001074005081c1038001081c01401c3c16041c120501c12a0780b800741008003500d036402d9900000300940c04006060041280320314640c003081045c030140c0d410094031180002c00041c1b60180590014a0112142e03e0400c00b00d00046020007081d01d92401055009030a280c4030751514107900c00286d160701c00103020800820710300168000b000d01c2544070b04215540a00114144440740c01c241e00791030008070941c0c0c814034102c0d48108882d0302c82c50869513820642032100d24000043c40042d20b0101041209a40d20f80030101c03003c3c003040d9a00c1100c940309009031000911075045040075030035120020180080340c1410014440001d81c0001d03000201c0341c0c10240c0a100c100d01680850140182e10040c05943c0700c00315610741d03007070382c0440104141130f0b0903001c40705260455015808008822100a483e503401c81c8002084034ac0191541d0625a100703607044003607401c171035031440c60b590019074141c000781d03200a0640c019400c080194a17 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 723920863 1106 723919757 723919813
    0x70512041704082509060303090e090f030a050c1504020108040f150f0f0605040c12090302030d020309060f07080c1e07060e0a0c0902180409030e0909 66
    0x8040300c55202043c4d440644583c000099440452017440120396154aa5400e0907241080d100c1581d50001d01200c01402500356000840005100030985c0d00520340f1442d84840e450080b00b86400f92003500e403491002940184800760303801c4084681e0169015200030f081003500c0c9800ea2040d06249030b0003501c41c0c104608028800c1d0ba80e04080c0449004c140e08000140c0e540040105487e11030040c803010907030403088100c0d014520303008605032a001e80102c0e0f2421842100000880e401168600b52a802101c14800c0c0003041d01d94280d00a200c500d040031303c5040944407000d940c41203008800701190103542d0303011280c0d05442941c9490360001070800100c6204100141c945030608800c039240d00e80b05002083c00103880c82036510303048106138172006d16813610040c04010110711000386c044c4007201200c2c520310383e603801681d8401c80b6150040c1030407000e60810030341c2c00c003010202c84c = true := by decide +kernel

theorem cover : BRFrame.Cov 723741007 723920863 := by
  have h0 := BRFrame.cov_init 723741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 723741007 ≤ n) (h2 : n < 723920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
