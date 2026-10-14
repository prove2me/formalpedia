-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0179
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:17:44.039935+00:00
-- url     : https://prove2.me/submissions/749d97d6-8993-4129-8a50-a26bdfc3f86f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 32014393 ≤ n < 32194250 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 32015643 1250 32014393 32014421
    0x5031b250b030c270a0902040e06190b180f0603071409060d140702070611030d050c070c060807020d030603031715090a0605191a070302071508010608090f070603 71
    0x50609a500c103040228080325004100007456a1108103403802d00300605c00740070840011410241030100200910001401591040e0058003001094138000104000070700784010000c1d40300c041230381d04071801100380742c403152181c4151004a54942808010350f40b10700e900d9900d03165008140c00d0b80681540c03080e503049070010000c000710030450742c290281c80c601040a10403000c19150101d0001e003084040c0d0451410803a4158110803080d1000065601040c070003100040c840c5c64001000c60980b00380c600042c51782604480020703400ea04500c00da40b1404a41d0203841c05111003840032001c80300c29000080200d003190102c070820340020f10146034010001c8914100c442081c400040c030014003103c407030615541361074081c401402c2c40d400c40c0a000300100d000076a80c0742070040d4100898120071490051203404602041450701c00c00480000b0281da031402c016261080000415484090003158041064080801c140c010005104a034a41030300001e08011070030a40101c010380303494014200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 32016893 1250 32015643 32015647
    0xc0102060f04110a0308071104150603020c01060906090506010801060c0f1e020d060f0e0f0601060813080d02180102030702030d05090621090f070303090303030f020705031b250b030c 80
    0x1019449040034100a035000d050026150400340c90425061000044d034240103c1c10300d15608500c0302c40ad03030710344103490040c10f000d038032030b4010002140140041c4d840707504031608120380044c0c05040342c0e00c00ca00540081c5e07603600d881e83e02c4802c2652541000030004011081c520b1081010030003503200d5181c0c05010401d2410414829000a24569064030b815204a40d450004013000d0b0103a220b0b00854450200103072480c104690400b0303403100814071404003030204100008200c44051440c007207590758404245030711041c65841400003500110010312040101581c0100700c0d40c0004252494280d0080040030768078a03215080700d25801042415400080a202c00124070002d403041407000c100040a51001c0e24054018601d80004410100c2540c2c01503c02032000ca54494a041d050781e8040c10f01052413843d413040c038402441115005446808003242c40c44030f0081c101304090032000704404651520b10700e211140c407103542c0f5901100110019110410220b1048006160f00102c640e031814 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 32018143 1250 32016893 32016923
    0x421050903010516030c110615030304081209040c09080607030e010b030a051605040c080f0709030b04030c0b010b03070c020f0d06051e09011806090212031809090c0102060f04 77
    0x1c1c2c00e40304203958003034803490310301c00040d0425450710882446000328980b0200601407841d41c02d4965001400442400e610310020361f990741c9041003103c00908480003200c150400683c4907003800d802440300c0318425403e060111618a11881c40c400640e281e000c081c02081c0c641c91030a800030020701d1030340382542d501c5082222295800703120580409002c5d10141c00e050b078407005a85460b41494002c07500c40d82c60007800c40291680019030b1903012000c4000307503040d031325044010f8501c8160340d0300043c00307040c181040108241e4021560f111043c41451408540d2b6203800d00e1080d6408110340110001d0075046c88034000d032400400c511403540e0302504043c0201d00c2a1100010f4900403560585e0702014a0b543c611800c03446084180d00c0312400d0000c01c1940f000c544060800302c10880701612a6448090340c10655039001103004848455008990381c030001c0015401c2c0c1c001c3c1e40d1000d1031190324050001034031000e0100c0c003000c05a20580c0500385580c4c1c5c1d86c01c070015008028005032102d00401401e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 32019393 1250 32018143 32018149
    0x201051b0a02070b0d090b0c07030206011e030605070509040f200d06050406060203190804020a030b06011101050a0e07060e1809030d020f0706050105040b0f101106040c030b010e04210509 82
    0xe2000c1441782c2e4010952810508080340b40504c050006015034074104403660100e41d000c40c486040d41c0c00c0040d000f20306d400e00310001c1c0070700c4415000509070305d25000501c0811a0018010f2064032401c0d201444510322100320481211101c20028500b0000c0c40f5403c50300c04407040042104031246000042d906880b03001280480d07a545d080075000da4400202402c8481001802c050328a509103041d1502d860301c2d901283e400005440010600403014001c1001a0700662482c4007038200786008009619007011020082c207038411400c1203e02608001045162080c002e900c04000042c103141c080d000c1d1490031400f11000101442c51a02080c00201c54008040c0010801d0860082000341c403881c2034100441102e406903c141c0c4070300e107403891103400c0f604c40394103171502d03400c00312140c1038606011842a20900455600801c403030280300100800c1042021802099030302402081001c0e0781c8a0341158407403038090303402512030910319804200e06400e00114000500c0940f170701600b84150030b07000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 32020643 1250 32019393 32019397
    0xc0c100506040f0e0312010e01080a06020d0902040203040c030b0903040b04050609030307080703030b0a0510020d08180a03120e011e0902040603020a03080304211202030a1104170c010201051b0a02070b 88
    0x1114030305820010b0005005007090386c045000d8101500c0c0f804242d450103480c0307580c07903061110040c903264011400350302850f450b80c840790395240c0181c8103650743d241901c0c0c000b1054045d0700045822906c45400702c0e0440000006403000d64040036121817402c2c1c1000c2c1086003a4002c00c1003e541840b04101d26000038062034041c1c10307064803a4501254219610003080390361407003034024038051000c40e11107030852540050603082d410f4060421859036160000325884031080c0b2008010700b0302c1061014001c242d44031210a103103100300803003005680307000c2ca01c0c01c0c01d861141000410f00540b0b01443c03140306401c5d5008140c41c034130081c000111203941e03901040c01d084c039513401035400000220030407050044082251415401e552000d401c0000407140c0070785441c5002c4055003490b0343c0800054070fa00b07041e43c0861403a0502d002001e0b21241e40700c402c111320a0340410713042e840e40103440d50b45000e540140589806030820160540c20b00451034050710a5030440000e5408500c200c0000050345028800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 32021893 1250 32020643 32020661
    0xd050316050d09080109030f122a0813020901030b1008010f02030402030d02010b03100e07080a061b02010605010207170319030c090501020a02090f070c08120a050c0c100506040f 78
    0x1515240c1c0b040c0602803c0e140860f0b22031440750341002007000010754010424000141103003419000520740745214002000700c00e0080c180100340300903078000b542c0f074640380b181c038020160707242c5a03d680c0c0c1054841100000f10402504400884014000280080c09083e0300014192040400316a104082d50940e024514102c0100303a00100380010b6040c207102c90341241205000034040d5601020102c0d646100c9402d40ca60580d030b40702d4043c2054182070201000411385032003260740b00c8042e07051840c0181a155103040b01c41030340c48407804889006005000c2100e80580190083c1440c1c54881500c416000240c1d121500040200100d8030301340081500b44001e1a68001030300c400a0b400c041d00914894010605552005254100681e1801e2409512128480c40310a6940350420140d07201c01c40442c00421614002c02d01c003a420b440c0c0020b184c810740c0d84070b006105a40700c0a404d50200d10400d81481603a810280807140903078181d801c1181c1006000d4800168140344030016401c0700d94140e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 32023143 1250 32021893 32021903
    0x71211030d0c1d010c0b0105100509030307151b0806010e0a05041a10031103010b090a0503060a050405060f06030613021f0302031501080c0a0f050909150406230d050316 74
    0x10242e0f0b150042200c02c6101c107910203003032000640ea61074035200d035903601c148a00c910a404204495084611a4042e1214510050b00300c980340c40c000d162003c25049080c600c469940e1501400c1502d080070540c2c00d40c882c20168444e20842d4803204011945070024030142600000420b4000469480d1482803d00c070030f244822080b00404244200012110048081c00826042c44903048040038000c0460b030441d849110182d41c0c1c1e05006c3c2c046000541281c0c01700358540140d0007000011032554101e240b14901c80c400741c07152513940c0a0300454828082d100c054040d4402000100e0380d00003010f84000c0c460000381180043c041030322503442140100001900001d8010040c00342002c82c9120b03850b1643d00900341990541b03081780036503116024900140041001c00a07510b03c1c254040c10844991406c09040d03208603141c040c85200703240c10f039584460b024a1030f2190004082c00c4002126154068800301c09040f541440100705070b89100b00000c1d10f00340420090781c040e1480505920354114410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 32024393 1250 32023143 32023157
    0xf0c030e0901030b07080601050423120610030507080d0c02040b0f062109011107020d03120f0c080906040804090b0a05100206040201020d02030a0807030e1903090911071211030d0c 79
    0x85c5001084440050002c0e4107220b0244002d228545106a050883d115046440f5880e84086400500d03c036007820b691003c140544410702811030802c2e0011002d6901036400c130f81209075110700041e42c0303442540c100d1000401811101e001072034035400c0058048002040c0703004441c888070014440743d1040d14100f8481e420b00e983c11000c51050111180e200c20210000c0014400603442052140700c2c0541c02442240d859140d2410140182c0452020444d10f02d000c0001d03540b07440d0304600030b205052091000c00c28800c000b039980080069581c1c4680c0d0310071100b40c1051300d84070194000c0e040c0401c5440c1c2c001e508000c04245911115441c5508540c940e0003000309080c64000a0b040c110b100c2d01c0fa03800c64104204000115802080c4507400c421036190002c1e00303255002a183c10410b00001c40301c1011900c4a1010a140d03004e0009000d86400314400c00c0005c0c05002144501e220f9102c000f40001040034400b080907004080e080303a1002c400094918105103002035004483c1804030940200d011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 32025643 1250 32024393 32024401
    0x307150306050f0904080c070f0e0709080c03070303050f040306022106101e030e10060f05011d060a140301030501061d061e0105090a0807140d030f0c030e0901030b 72
    0x858040c0900500707058910207244648000851307078074400104081c000000001321074052503000c001500040500b00070070700740d250b11400b03205c1842c54180c8960b800500c400c000403800c005d01060103411020020024014980b035507406880c2d607003000c0300020700d00000b0300000000c5000307030000704a1036003041c2500540a9580708401c03422940504940d0180c100621061015500030088800031104056a00e00041c1643d60450151809510701082c80c040c2070035480d0207007c1d40c2c1140d02a521030301001d50b8800d07218001164034030000644500103000700109068281002d000034146043e4514011a078984030000d610f000780c3c03080e070086691340e56034402086120264041074061482c0f05e1a0480907042c40c80000d00c1095040006030220f000c044540880e680c080d5046500c0c00c00080d01a4200d10781d15001e050b00e9480314410324020111f45426404240b5191b081841d0459154440501c65121214200c40c1c040b10444101c0500105810000e100c0e0ba03808401790095114071884421850 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 32026893 1250 32025643 32025647
    0xb0d050907060c020a030b090307080a08040312051902070c09090c0806130c140f1315080c100513080718150503061b0702130501050a0605070b0610020a02030715 71
    0x1c690303407045082103002040c0b240180c1d96980507070100c0e07400c96032161198035031103101d034150301c2180ea00400b41c2900090500250340c100e110144200d000b512010703204003121035100300b95982200c68240b12400b001d0000b082035085d80c00b0300417250248010710f14140e140d09a0804a40e8201016180c4000d8040304104540c010000c4560203200c0743c903010500c441ca952028141c003041d0080e102c3c2c82039043c00007481500c900c2c51074080b00302c0061802801154080c02c140c01080031a003501d1003407920206c0401c480c800001c10407669440a004603d00c260034500860b0280c21189900180302010240010340d6001008030780301908240540c8445a507280208000325001c41080c440b00d094000c04c100001c0d07901150959003da000e8860b0703000c160807041810381921030144e0083d0b200134500604401c000060b0301c40c6043e2807003540d1140300709454200540f068041c2800062850b0070520000d9543e0400c0fa6100b0154800c50044440c4000140d00007410f08203070307030000c1100c0c0806050203100b580d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 32028143 1250 32026893 32026903
    0xc191205090604140105070506010303030618050105030a0210021c02031201050f0f04050a020906030f0103060e0303160e010915020606030d030204080705040b01050408120901020d0314040f0c0b0d0509 88
    0x114250a0892400101e100414024001c51103120541d10942c103c0c5900e59011b071040b1009641d2040075510ba175030312864003800500050089044030241c1d12056100404a4402c0d581690001801840d240d0a2a1300304400020720750360100c118000d000c60280c00404d01c5803a01a420400d4004e140c9940c841c441c10403071803805178009841400a5204001030783c45554040021000a035408100c6588507001c0c90041d100300316009410220001c100080942d000360228142d03481018244030071040302000d181c0d640009e582c4003a000c2c0e80b10040001040c050641c2406800e0306040000704140e03201350003100d0004c07190881c0d0144c0c00000030000070380303014400f5110302e40c0603050071400e1a050112099448045015480c01a0707540c80d0510426030044058400400403801100c60f0366614582d002029000f070a0443e0151080003e004c005a00038083c81c0d22019128080030502d560b1610759190b01c45078500195143e80030300d40d01044402d04203004001280d61001c02003014241500510721342 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 32029393 1250 32028143 32028173
    0x30f030402100801030b0f0a060510020304080105090109032c060d0b0f03030307020a1b031b0305060c030c07032d0f0e0409121101060902180f0306010614070501020c19 74
    0x2200c200140300046d841c1d080542c00000b101e18030034007035640448980023460640c02140d4441c6507545240c41c0650300000510a88607100c0082c0030306c2c0c955440d5036080e141c0051000b00400c4400c40e80e4501100c41104905405200742d00464a25000402042c026442120394050041c0c0700c014480030b905107c5052000440f090f00294510314050070000e40310554000c00414880f451003a03020128902c003440005540c110358220328103101102c10440c0c0c14403910081300c190264200081020030048152881500458009850000142c2d811146030003140803c0301c0350010b25424400018070071542c00341803299a243c90803030709150300c0d01a10070030010281d54855400c1000800c0000c102d8800318618640904210842200303800d416805040d01e50090591349102080f443d00c800c40301340c1800c9900c201561424040c20126017810b803900c01c2402140c0118498920840208042200405405000700001814141c8048040742014200d070000c40f4400e100c1c0800c001440b404498818030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 32030643 1250 32029393 32029397
    0xc03060209030f070b030a0e070b03010905040b0a02070f03111e0705010207141c0215070b01050a060c020312030604061715090a0b010b030a0905100911060a090506090a0305030f03040210 82
    0x31645042170043c03040c4001886000f4030f503190003031412114400c004d40c4020701841d4403503949a6844000b06402400c007250141c401c000134902048403514107200300d41c400d0790402840c81c00d08495403820754803007074003041c100340c64450350081c190281e80b144440c0d80401030110181865600d0b0400092818074103802103003da800036136604070a5600d0201e04940c1160840030042c0d00e00c182e00002e42404103000c80c00d112410001424010040d56880c0107058410480e4942c100c55110001142e8003100040025050350042030321500da540d561018551011004002181c11901e0708540d032030300048000b440740c071036006c0380041c010b1900c208102c1d984400001c00400714400d59484135040b680703040c82034218150001011801e8590260441c1c46c14a8004003101c21805141c5424401000c0518065442c0c4865209144561804004580c0040e515564409030035081c0010890f959010200300780e409000c0700e10000009809002510b45502103421083e00c81c580f278014006001d8800d400340302 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 32031893 1250 32030643 32030653
    0x2d2313020f030d05190302040302030d02010c0207060c0203030a03110405030a08030405010605042903100504050a0b070801080c0103020f0c07030b04030e03011103040809040608071401090e130201110a0c03060209030f 95
    0x1c8044e4031006480d82007107150052803540322080c9099000b44103a400107500b500560182458054054201828410b926422120a5a07030b40d40101d40840c260b42000758590400c1003078090062080e00301a141d0603412481a14156031940007c3c508020001c0898140001000304030034080284185802494284c030b0520011440005800c91400c00c03000c5503050b021014070441d4180c40c200300310100d6040c6407504010500303003420000c1c3c4d10303082c0040803600b9026100004031094402c40d901c9040b100c49500802104a0748401076000c0e401010803d003610400f40080e0f003075030700100300d403c0007580900305003401d070b05083c10010124910100c01c24000d80c141035920440341c080c982144e0340640c0010b03006403150741030800100079004950160710141b00381c20020502205001a104044c00d090301c5800c00541d8480481410035000c899010f0424942e414800141d40204120801050810241c4103203174980e903503000d40c4079a640c006440729603002c1042c1c2d1031030404000d086d02d80070b140c0000b40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 32033143 1250 32031893 32031913
    0x10050a050108070302090712060308071509080301050d03110a0309080f010b061603171006030c080411060f0d060f030618051b0301020915030402042d2313020f03 71
    0x55452201307202c0240648205400144900d01c203004552149007000c40071b000c0c02c2c3d52420001100d4201050940b0f60310a040c04c41c4c46500024400c0051207940040c22900356840c16081008155440d1000c1c0c041c0004c01040c0c1401d2042400b2500ea01d5209071204488542040da18600c2c00c509282e00314000ea03d03000320440c003541c3d0001501c440410170b80b01030725017603490f140445d00361b419100c0c18070881c00500144601c0300d00607171f503443c1650328542d810481c2e036020034000c94000b403083c0c802500d060b040282c203560a05045005000c444001d50b041850031035003120641c11620700e9881030030038940191081c0201306040c0a1031130041362440c10003006001756103c1c3c0791102c01510a6810140740c60484030381e661800c1d0160b07441d04000411940c00305000031401c1041d42d008480c101d00c6035150400300200d048142d844072a0701c00710018001c1440000441240c010500d100001c0465040344915411070030407440150300c02c5080314100c000281e80c620501c0100980006928440e81200c0f26603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 32034393 1250 32033143 32033159
    0x50903070b0103110f0d030e041a060f0304020d0b070305010302010f0521100f08010930030c0203041502030c061b07030309060f02121f0b07080c070b0c10050a0501 72
    0x10780c15070780c0111800340e10800c502c00040038a180162a603070801400c41b0a80309040e0040244c0d40100803e440c14825103002d41682d0b6001810b000c0c10540c040070910203100181980f40140d98498400744c82c10111030955200c3c00e004000440b00d10001903102d10040c0110359000640d52440c0e0518107101e81819100900c458010602c06042c2c1c0b104000c0038009601111010041c00081c00d4203c020007481391038509041c0038108211060741c560901810703003d800c010444501118a203521005090401e100340214090020201707280110f2100b4400072500910b4414140c4c0710440603001550344e06135001055003486c0e8001c00ca080002543c981c2803080000780c2c0e04668003150305280c001200075547c174000c8021700e0100300c40003c06101050395034081000303800da82d000340751001c55520082c054a005070b000e00d44501641039692005d00010340058840380c040d003408000d503400d80700c405485400c0c03c10707581c10281d20980d1691013111802d000351058820f00f0342123070f4001c0f420b001646c184452 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 32035643 1250 32034393 32034413
    0x60506031015090e07020f120a140a11030a1706010c0b0705091305010605090112060b04030f0204180305030601030c0804050d050f0c060406060501080a1404120507060e0105010905090307 82
    0x149160401d500b20601415a1140b0b0922002d04020300c076006140c104940025940d1080c41221407407841040c0d4250010f0050805403401c04100b5900c00ca5508040c0840300c485800000e20101840948200e00309144c006001400709112070f99030b00340b0b911400040400d42c2000c0039102c1c0d0f0500034002c0c410004100307607590345d9a0200d01c070b0a1082c0d135048850045407000c003409900240d414584000071401643c044010150714401b6618260720600ca1805802246e00a06c078542107100100802c10014180410311405103000400015003040c4511284c00b142210010072000940004100401907800d8840c03c0a2001e1503d0103040c0361a0034ae40b526a00d550005001051140103c3c04510022412040b9035400420360160b91582c10207150540150903140502408143c0240005840401a1103140c40c0411a5000a00c0e00d032180d813502e808001001600104110040014401185040c0590025a2024030002840351f251543d00011074030090100c02060b001001030381e001c1280d00c42 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 32036893 1250 32035643 32035649
    0x62702090f09090a0206030405150601090806060409080c0303090c120a030e060304061805030403031e0f0c08040b16110603071d01020a0c08010c0806040e030a030b0319050d030605060310 82
    0x1c041c0c800f03448103141a4900815420020340c40308000081100304000440c201c0c845800075080c0c400183c894000541f00300b0010f0096103140d61042d40000c3c2185880c3d00003003c036a01031002c252400140c040c00f40e0550340f040310000c54551007a0301e00f616508011003101c031040300d13120282520743c0d4242c1d00240740080791101d2500c40c01c808000315043c0f00066001c205445c400d4903d141480e01d440c079205440360000d110540100c0c01e1050102c540346100710030400b000030150b80da501160f401130410340f07460740d00d404107403018241408003050301c0004000422080700c20b980c503450b030301c07003130303240100036101860700040c00380c0010310034003400f41e400c692a04108590071a0200003003c80000403840d003458a0000780544800c03480000e0100c0c019400303013050b80d8807640d501c002d5039100e0092006540500308400307040c1e4420481b00b4286403280e0300100b42d800e00103060312203074500c0c3c82c07000094036005202034440e50027404c07401d0807407a0113201e400001c3c10155201ca00b980381a0840c8803110b00340348 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 32038143 1250 32036893 32036899
    0x806060f0a080414010204080601061205150105031f0b0903101b0c0f0b0109020c0c0a03020108060103021b010905030a08070f0503060402070213240b12011a0706062702090f 76
    0x1401003000c02c03607040f512141511340000210f4580d965005407507a2510f003840381c400401c180c1248c5512100b09030160501c02e440140c807540340211101d00456850303000030180401c1131075001041c0d00052203203480200402510340f8054071070359104105820401c14188482c51306162400700c0748002c001a8486034265180e003001c1d0121201410700b00c0e480c03004414000d01400044001090f814210340c090109905001b003105c03a4030581500b030042c0c4040d1030102a000c607007041e0026010b50f11a40003020880f03800b03403a000c100b096014481d4207540c1c10b98811510b80d0404602e040055501000441d80021a40303040c4140c4111482c0c007602a00c0003900080c0115000070700340055494054481c01941c09511080110600b840c1c3d00101a0003030390340300c5238000820000000d16811b00001c0d40d0fa80300c8100801e070800e91078000c030300d00501204004064a10b03810700003e40442c1e503a02c5004001d00174141000400000c0c540c1d076425881ca00b0081e806460f205201d400c1e4161180881e80c0c0710b0020503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 32039393 1250 32038143 32038157
    0x1290a150c03090b030c03010303030b040e060105090903040305070b0a080702060f1303030603051005010f05060a0e09040309050310050a0b01050403080a1128050601140d060b061308010c0806060f0a 87
    0x342c20304580c160296080003e007080000140614010041c2c02076040320f0080c0e42c10010001d4104c10002510b44a40e04d51609602c0140107115a18114a909402c04130300c10859207015a60b80c2c1c0ca034100503e651001803020408142d402c8010741041407e944228107101400b814603246003030b00c80c80740002d03081c032514404030b8401c90201402980314034043d540103001c480103140d03406405006070401b4003900520007810707000040c40707040c51015510140340701e8840c6000000784909104100c800248190100120300a00240c107440510150509982d65400881e041ca003c403241e03025600207803841410490100010808070b05210144ca00501013484e00300c6c441c0c51200041c0c1c2c58607001002e00c0302004200e55800c602c824251404050440c42401a030b603040c1c0c3e84808030b04100804039021604404182c85c0a400100e035079002002c51038004140500b408040c19002c2d003258071940080c0b10980d900d030300c00481c8036003019580758050000c4072058601031508002d061075005440c0d000c0140000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 32040643 1250 32039393 32039417
    0x40f090c030b0a0204260d0e0102030a0804170a050703030b010903110613050901090609110304111201020d0207140f060103050d110102041806030c1202030c0d02030f01290a15 77
    0x540417500109544010021200903072190589454402e8152800d1840342c408804100307070050b0700c010080306050700514108101c0702d005580c00800204201c815281c0f541c1d00031118120480607029100c101e40c0e44039180c00702072602808640701101400d0510a4200c02040084c00d4405214115035080d00d0b401e480e10004003c01ea00080d090b00500d5000da080d00000ca803200c11544060222a42c0c041c05102a00110394514660f21042c4c80c040c1c40741c100032101c101903080042d61001e01d5403c03800014545a102d4014004a802403102280c00700000000740070104020001e0b601c00d040c440d8080e00c01940345944442d9620100b4040c002448100303003001440000070340c160b034010800009100c1d9981da1115200c00244098042181c480f10341d86404505100714401441d18a82d0180003080719400d800f041103401e4000d400101c1e41071082c40e00c41e8214803028010012080c142200320121220b24240d071455904440141c64014206020200485072a41c44041410106810082140a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 32041893 1250 32040643 32040661
    0x201030e0f010509060a11040f050d081303030804021008070f031805070b0c150c0409050604090204150305010e01090b0a050601110d0203220302010203030a0f02042102040f090c030b 80
    0x20101c0d00039070703481d4a420200224190f01060740c81c402d046621040190415070700c0414203e0046024410400340c580c00c040c403050424030000d5203060f0244140604280c928414a40700c107055030012000151060144821828490706055030700c0c4a604041c03c01d4a41300e44014800810504a18101626500011b00207032280b50a0300c032007904103007a0303000c1c0340c0c032003c0c05851a400074035249400e1081035100821507003000e45140c01400981e48031031806181a11103406444090b00080d401070307a42410000680c0d4034443e800300c42181c08041c0b810a855814001c2c00c650040807110b90b0742c1d04100122000440c0d00d48a980e20891003100000c50f81c4590004959000d1940702c02000307881468400800540c0003c081c1210200540316480f811042004100705d49002e44002030150b8020300211b0014035403600301c10a03004040c4030050500740d841030343d26080d2070031100002042804141c0c00c425800c15009a09002e800d682c401e01124095943c0d4003030900380e5100250040300c00c1e80114040c3d02c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 32043143 1250 32041893 32041903
    0xb0616060f1d0610060206061309080d0905010c020706020102042105011413170a0f0807021204090603030305010918020111031c0b01080609040302070b090a0503010230010f030201030e 81
    0x71110300c1100d82104030034409582d0b40f001902c0105141902c0c1c4d00c0018910310006401c0e21038071014203000c0300c3c0721690b17135104058614510201d03803410060103503c4c08007629224010b41c050150740007103403030703296581c01908180c00c54015608690042009211454918a000402900703440000e000f10f449030400c1c84c010304070002d4210000c18044180110940070240300702015010701a4a003040341c0e10608854031748101c00d1080c0c0402e00040c4002801d41c05058156440070403401514000c806941c41515940d10903000015459074800060041c994188030b11070140044800c2007100c440b5041d2000e903c1162400020304000c01c038080d1416444081c016a904001810398948800e600000440050312a4600c01070001381503000003a07041c501082e420340100d4058015040341410a21548080c1d4400003c16030404c03591000001d00b03480c2403001301203e142100ba03840040310740c0c0c08451002d8845800c41d881088640006100350f0480520b0241281d50900740011010750020f0b6140c204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 32044393 1250 32043143 32043161
    0xe030c09010605030609070306080c0607020301090213050a0f0506150c1905061803090901030210050c030c01050a0b190501050703030f050403080402100504060e09040302012a030b0616060f 83
    0x120000014001c1d030002c004d94000c80084803030350b03510340d81c3d040114101c601c6403003002402d6014180300c2426041c0207009000c0640041c00100d1219041d4000c16814610003804d801840c4e651810400c1d035040300e200e10b0402440d8020140410304000300000c0395611900700036520312f400091240340d4600100849690440810065114140c4908195460f03a400f1a0307915a840724802c03074000001e1002c4100d886591b0010018081a4210340a110381d211006950f03800740002004409032681042001d0040104200c1c00401c0c01e1500302003900c10380c1c0d844682107008070902d0080100650954080350f0982e8001c0c0780c201e46515442c241140036000d00e210403116146810180300c01d15a220142038484c81c02980c504042d10070810084600d486a4424100007030429055010a4640002c00e07030740041c0207100202d034000310011041109243c580d0110800c1d000c500440c200c40313426000724090500b08032012403d2204051862010722220440180b45655449000003000d04683c02035000d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 32045643 1250 32044393 32044399
    0x3101a030a08070303181509051f09020a0b0304080f090a0302100507030305010b031012020d1a040b16080a0504061b050703121b0f02010e1b010f09060503070e030c 72
    0x9081014100b2414035030004030150002070070100384034004500d02122858013603212051349900140c443c03108005001070581242c03075004a61800b04600001c103900e1048150320000014890036520401181a01075400707a0290340c0d09100b000081220501038501440f14040c01d5507413001a03400003071070078180c0d400096000344000c40134409103a100e000341c503d891207600e0800299072120010600d9000481b0144100e07500940f0030701c00b056039440e05000d6a44050716560382c58400d0f030f540880c0c8424250142d092840c200c010041402086c800203038103c00d8080b00f2000180c01681d00500a030b0008007011400c3d0b031584041010048540d02640b10151420b038609540d00709294010540c1c3d1152500381c001030f2020a8013080c0c41d500788103110201009107510b0501611300f4909403441c00141c80101c095550799120908524018410a022040141c41d502507254840001520b00c6c0c150510880400503214018040503800808603504010700d820900b4219011800203458014210078641d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 32046893 1250 32045643 32045653
    0x4021905150409050f040c1205100203010b0c15091527060604060504060e0103020d031e02010b040e0c03250f080a0201020708030c0703020603040f05010203040b0402030d0201090203101a03 83
    0x40340d03850100240c000d07948240800d020b10740311300000c01d085039810360300031f00010b410311002c10011901340c43c400310052040e404c0c0da00742d0201d0284032040360001d0788940303082000060140d101000034003801400c2032440c00070fa40582840c10001c2d9032030320502080004040c400300410441a0540c0d004100742500d800c407a012a20180c0c58503441d48019a101801181484804a568074241c015601170321100c280080180e072864080203015942f09005400344018400444000c0500d100b00002c56522500003190f0300c2c00311003d000031910191544651900038030400c1d105607601103002c0c2001240300601d88144200a02414058021a4818111040c21101c000b60011001c03c070b14031000d000740c081c1c40351a541c03400e016440344120107a100558101250a1005140140c09150054000c20050414050f80d95500d822a80180c5040d41c0500701d6008010031450100051340c3c64410b00c1c402481440b0890340402c1d603c603184240103490783e07200c0844c0b16541002e08504040303864000c041b99 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 32048143 1250 32046893 32046919
    0xa0807060801030b0712090f140c180a09140a3c0206090a0603140702060c030115140301060e0a0816030204050a090501051f0603021206010309051606181202010804021905 75
    0xc00c991100411127049940019009020034085a001c503e4079002e000c20002508a0103100d110f0035000300000910ad940700b401d5000304d12203c0c1400490380703100d0010300d407008450600d5960210000d07a0201c02030000d40c816000507041318041082000101c0c00d030142c540c0544000f401d18041d0703502054000324007040c0090400d9045c2c1026110b03071019603c846094039011001c98440004503511801f1040030001000300700d41f0750300703146000c41c214070704080307030224281e21400a0f910a134411800102104000c000340e00e04090440000c04030032004102c8220380290440361440c843c0f00180c8501c0d030ba10300103842c003401c0c3d42060b4001071340300e4020003035031801801e45c1100000c1450300d0446112960808a003441c024803c9403543c4080e0072040c403040d6903402c01100038108100003100c0c0390040032109010800b0503a441e0016004031340b111100d0071300c0054524110300d4076134495405020844030000150340c00080c00d41c1c06c20707010740d290040c05040501c6c03015280c1c01c5030300454018985070b0000b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 32049393 1250 32048143 32048153
    0x5040f03050c0c060d0218030d02070614040906030303060503061006021f090501060f1d060a120305130602030c0c04180201050f04030b0901020901080f06090601031e050a09020a0807060801030b071209 88
    0x5010b180003000d602503050104100b031690341d00c849d41800002d07a200ca1030500c00c0c10f0250301d13510101c40c4e010290600d85510b4000e074200307a4207560b00880200351661001d008514051041951000c5007000c00783c402d0b803410790029540c01c0818003480d0074110007440003102080355001550b10941010080c00030654610301c4541003a92031117180e40801c49a01e032144481064005103010b9400142001d80646c00e0a4400200c0c2d05404001c5040c41f0303041044042804807001c19100a09154000d980c13600041130000f41482c40e4109054800c81c03418081c81e000030710401c0b10204a40e02031030300a0321031401780004202c40c8115040900105008400c0040300d5805400078071040100780c0c0d07149020384031348013610302e2440207850159104000740d000030525442035200a038540510a0701c0c4960407556480c09044a105403004c2c0e220a4481c4038110960402c00c68480081032040024880d41d03161100060206c041170000611452f501d10214450f140f0828122100d076045000400c00c0401c58604 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 32050643 1250 32049393 32049397
    0x2040306140121050a060b01050903061509010b1e0d02040f08010903090e0f0f0c041203080103020a06020f03071101020a020901140306010803091005091f08070306050405040f03050c0c060d02 84
    0x1201544800703000401c140403601006a03003d1035000340141000754080c2e540e81c0141c018240c1d41d504004091243c06000e81d001c10031079018002d010209451207c4100501180000580004035050780410142301100102c1194000e00c810000407141c5036000804c070100a4032030343e44189000c481348800861a840103501100d40c0c14825150000002d0740e90090000401c1c08841c0844030410010000b030968409070641c5501007042c0c581c1c40d1034903440d42402c204c0360340303102015800900002e0041c400c5007024a1540c4c09002d1a00080856080c0900d58590380e105805005103038075520201074080b64000c004510403030307900411a460a60b10780303910106c501c0c804000c46d0310901c542ca0000a1048011040b02c15008001d420086041218101900d8a034458090365070410881c20f007400009034003074105014441c842e5140045410a80801425900386400c4079101d9807401040c840010440c2306c41e0720405500d420020b450303090088400341000c44074510107401020000c0c1000090074141c2c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 32051893 1250 32050643 32050649
    0x50103140606030c09010b13030606060c0308090a050d05130e07050306030114070509010e030703021807020d181203021e030d0e030f040302040b060705030c07090c020a05100f020403061401 83
    0x41100c81d00d60324441010ba079082d68419140d0080324810051005140c4400181403080f0004c0c0e956400580e01d03a03801d4100c8900740e112100040300030700c42c9070405074454542c6401c070301c20500515142c4620b441c2c2d00e4031180103040d0402800000074200c08100650766100c0024042120b001d1000c0c50580c1000d01158001c5507018841d510380303000c0c201c0e0025403050303480c0a08295510300d0b04080702c0b8030041d14050740c905150b036818401d041002006a03110808551203000aa004030748500341001c010b45410303c09003001050054500089040d08551074091049441040c948428003590b400c05034181150004080780701d190f07441c419418a103000004040005500c042080500c00c0d90680340e40b07034003440f40c1c0030008103810031040000d8906a0400f09041c070005003ca0729000d81580c42c2440d540c4070f03921407883c6400545081001601c0e5220381c007804c903468005442e0301c2d10555507498407035400303c4440020941d50404a280002c040e41614007a5a010100700000300349404001c4407000e00344 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 32053143 1250 32051893 32051933
    0x3050705090106020d020c040507030e030f04030303060f03051207080c06040b0f010b13120302030f03070801140a05060a0c05011805010e0705010f1403040213050a140c031005150409050103 83
    0x5400080e06900c0045c200d030322003105030b002d4060041c0685c108005064050440810035441e801c500e604072105100425514800c1c405c00c0359602d281d40380182c240c2d00c0c9039002e10340c40800c43d003007040402c2c408100030307114808803041c490f41c1e91290b141c03240307140c0503017044440c00d44502010403007005441c034000c5004218200390b4441d540c0c0c0c0c3b0300b44010140301d00c5581c01040c03174918808105450a80c60b18001741482030040e2400c060241c0000d07189508112500d20008251000400c04c920101c000e00b150719000b03940480906003494040340c0248200d044200820066040110a018003948030030a408004021081800690b04105029000c07c1c9048055401041e40c0045c066009032009008010b813500c802901424480d1042c07119040140184d8000c1c0c000d1104800c0001144102446003880035000107007180c07130401d64407407100c00a000134011303001001070005103581b1b440031038100c2e1011112a212140002240900d07805640d000406490501e00048200114440c000d00910016 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 32054393 1250 32053143 32053159
    0x2091f0b190e060c2e0c1d0904020d03050310030203070801090209010f03030c081b060c04090c030c0509100905040f09050607021915150f0501020c010306050a090b1903050705 77
    0x40c4200300c002d00c0359507000116580b022101a08071003040700c08040368090f0540412644e01c3d564880d5041d9001012188001011304407c806c0300d040e80120324003442000d039032480c03580c9131990105000600d05000982404004000030ba9225101003c110103198003030160348000750349280341c0f806018100740491041c008000007041c0342c100f00c40048203c2e501175540b4444440309444420303040c0c5c4018080780c15011b040403d482c900c482003103400d002d140b0141203940d8482c90454041d085502c00c01c0018201400c10b40c690b03600716401810780f200c2020483e640c00c946ea084003030a84881c51940d021a81040c1805030800100030594813415407103004400b03540d05690f40c1c00d0105d8840314016001081c1e40d00c1c00104201088c8500307000c18811002000020703500314505541c039245101755120020101c880d030014840c40d40d041c0b2840136035081c20708040c00468181000559103c60b64020a0300b45950307181265003640c3c070a00032005001e100c1503e90441a103a05006466412074080c1e203001d2284 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 32055643 1250 32054393 32054417
    0x30c0c01141e0903030105010806030a06060618080313030303150306230f07050708070201031113030516030804031403070f0b160512040209060a0b041403010e01020702091f0b19 78
    0x2d000d40034400c848541c003641c40c6a007000b00640720400058075941d010301c075885290001801074070030702c00540165100c0607905c2c83c0171900c11000c4822a00150450740042c8054004e4540400302030080d280d1508001c6003114181402d0400c08101c1c1d80080c041c28184101301d06000100c0c4203d441131488502c4c00d00031590b03003110005240f0303029a10100018003c00c120b8011882040161202d80c0c41454081140100e4900d5504690484528510201c4a51000b0070803c40c0401c1103a041c00c0f8158544c80449103161100c0f6101c0c043c2e0b2001130040c419544922036906814403c40e00000d80c084c0d480404501d160408022018007140e1010041c66860236200d1407500810540b55600ca1140d01203103261341383e5080c00701881c009042c3c0e0382c0001c060800412003d4250002d4030141c00b0002c403440030807610700c0c20182541d10f042c0a140041e44100002c0c005a196810090b80c01083e00f16095949491128178899220942d84042c50812021030020164061604403801212150f134030b60341e940403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 32056893 1250 32055643 32055691
    0xf150906021f060b03010905190b0a06081005060313150605060d09020f12010209090609040b01170a080a030506040515130c030213090501030201080a0c0206060105030c0c0114 77
    0x2086014100160b844103581d00b0801048403100e50703a42146410205045a0384c4404182d5078000781c0000c4155502d500070444099404861285488410082840600e0f500301c04610011000d00401041185140010341c860320165050b07001004042d050741d03500d140141c0d00243e845003500045030806002c4a03a59003414040c058903080d13460040c0f18924244209407050010f0803006001c0303822031b030284174110a80d43c1d00301011705c0d000340150015a480b80f0031020403922003c005d280d0741c072601c0441f0900000c0f41c00b0f0701c00507065030070684102080d480601c41c0300340342892a1130020010203000481c40ba00ca030b4140c01c424003408003920705005c19198000191441c86100300ea140c0c121102c0c0d0300b01e0301c0382071054200558641150800500d0000010282d000c2c5401c2500400c003c0342d1100010000c65074000305190388624501002c03c607101052800130b459001c05000380d410000003102194400c05503108031541c00c04001c0003000350000d115000415218100c484602e4660040c0921120007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 32058143 1250 32056893 32056907
    0x30209060409021809070e0a081b010f0c2a080102071205090a0e04050a0308011a19050f0307030606080a0c05040306051b07060615090e0403270f15 65
    0x1400d15040c6420306160b10000e401c40002c580306400384541d039042c15100c40380315500522041d40d51001c240d1011040c0180e40d90f50380d000500561244403030030700c0b414440c000301c2800902440d011528010810b81226001c0380720401070050404000c4050f00756509032042e65041041702c0a2520a0b580e51030031600b00d00a056016003e150110703905001c00e0700c02e41c010040d44900030160710b22a41c481765080b0035480211021105503010150340828950041391480c0100060600711030070901d0403640c4a00c9000310402428000d89950074007032003034098000c0c3c80003614640e01490f100d141583c00200138000b0742c0b19040100c1c2580c0c0c0441e290807001d0050804240807074645515161842c0d60b05401400d0060050390a0440100303942403600305a40103000d285d00414000c0b80f003a083c514098080750a11302a1803d21141d40820041e040d0030700c0020b81c1c800d0f0982410303402c400885038850f100011300032601c803a0b80301072800410300710601c0c0c100c1030681c3c125010207402d500c0384500c02d0700c1c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 32059393 1250 32058143 32058157
    0x201030b04060b09120f0a0501020414040c0c0b0406060306020c060402150c030f030606070602040b040e0106080609010902160501050a091109010305030313030207050a0e0105190308040b0c160803090109060302 92
    0x100c90100441d28460400401031845d0644030000c0f1019250010316207404d005401004440d00c0e5000107041102014125250700310755000c440820880102040150204400c1c0030018400c50001e0002014000e0303035030110300210b411010544d82d503c550380080780c4a0900b00c034103d1140c403850840b00c1d02000110309880f08046200020362500c10b82c160403643c3c5801c000c1c81e441d07000b0f03020460080000e80710300242008120300c50100c1e81766820302c0c0001510401c160455000c0140c146e04101c00780d6100700d40d140c11a491f1000c0141c0c1c4207280802070001034000f04c0050710703079030030034050109a0005500c003e0740c00740150403031507044500c0000c01000d85000c4c40043c0482d13005001141e40c4100040905235650b1281c0101d071750140d503982c0850381811855004070101c250840c0100458200520111083c1d0404204010120b00755915070340c40380903900820510b014082010f40c100d1401f00510301c440611b000c0c13203140f502d0781c994a42d5500c0e40309002583c0010071040000500701d009000751090 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 32060643 1250 32059393 32059409
    0x609010e0606040b03010b06190f080910020a2c040b010c0507050108090f060a06140607020a030312020904090507050f0d03090302010e04020706020c07170703020108010e0c07021c0201030b0406 85
    0x410b44030501004043c1c1301c070b50412035040d5030742c07c008200356031030500500a4001c106201030401d02d8000c0701070944009820880b0900c642d81040010a0102045010048544100040c0c840e054050101d480358003411074258464685800c8010501800c002856181e4003140d0034060b0400c2e000c0111030700e07605950010400d0b44090018001c960003900e2055000d41224202c0c0c0c00280008031403868060107441445a45644030720500c12414100020f0807140005d9502c1890200e503a4041807a43c10142b20182c2000540d000340c080b2080ca03030701142d4603400020401c0c8801c10030350070041c0d02c0d04140d1084030300c508181009480a8109600007054003605511400411460743d0010343d020902000342662095081140400041841c4007400440d205d000080c002c07d802d01d00010055850120640025032042c0c00400050782c0c4070a105056850f010f00450445c1c58207580e25200b8054624001c8d4098654113824110030102c11101140340c0c000d0ba010310840e49607038240003c4540c54050054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 32061893 1250 32060643 32060653
    0xf060e0103020904020312030c0706050c27040605360103170a020109080414090601051806070c0e091506090c07020f010e0907170a050c040501120b0913050609010e 72
    0x409440d00b00c00f0700c0d6110f800502541d4528030700c20540c545c1507000f03c90300000c000c0c000c00c40809014880c4503940d0b00080c8040024608940b142c03224038182c62034071440b8002c60007404c1040b250303141e6800002c01880d005e8150244103040061082650742488070715901c00714038021032a00f40903006c03150340c100c0c0d4002c0d04594901c0900042c0351844d03803041c03448805664a9440c841300054040e401003000300003481442240e075440d0410031001d000d003e4046030401c0b00900c40c0c0740d00d1120b04a500080340300100c4d98581e40301024541903803006190f0b0320100d11043c4000030072400c1000442c10103a50316800118828503681c1404220064400362a241c00e50f2805002d40c01c01428030298251200505040c16400400d01800140c101c001c00c80702d210000704c001129011404040740556041480c1030070a008501e00480c41c0c50550150f0f06c01c0074100803c05181b513801c40804d44c010b021403480688801841c1c9005003800c1940841c1c20030484240c8036000019000e90018030401c42c040c0b8800700600 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 32063143 1250 32061893 32061899
    0x50606160b040c0b18031c0203040909020307050a0303020304080d0c0c060e060913020a110106030b1f0b0301060201020417010c0206070e030705060c01050603060f1302061309090302100f060e01 85
    0x10101d0100200300720350210681c03402003850811440a0b00c000c01a20b50301d408402c0c42e0a083c50f040074169403041c602d9400781c0720508486a000310039107054454806002401200b82c5c00001d08c3c0070000ea100c01c1d006280e9483c048141940400180700381c031003107001ca400d03030002000304503590f01c4003c00c080c1079448600028010b0511404551500f1a4010442030605000600148005800400c03601d1540e60010b0301c2c501940d08110b02d2040c2c200c102001b0800c10f40f443e1180c01c0c2c1070b00018104040001c60380c1c040d014141a0060030b4014201c2c140f44542c076584c4600c0048c0c002e500902850b0004000d48802c8140c841c41401071a01c500c0d5507501030a00307a107810070300352000c0f04170410b0240c2c1801541d00c08500b41e12010094031a584049001155600300722003490301b40100a4136036071422024004004048e5002010340800b5541070b190b145d9150b41522a82204441d030340c201f45d0500b418007844a00340355000071100c5d0b0b86601c12604004131000200070508641040c0b18101051850380010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 32064393 1250 32063143 32063153
    0x4050c030609030715020405040e0c0405010911030c0d09050307110a09020f0a030b060903150406050a0e06040b06010302070606030f03021c0c080705030c0703080c0c0906090f040501090b0a06060305060616 90
    0x20001c08005e0720000d410b040d2250300003400c0e114400604405944601e622a01a03e0305008107030044c20041c100304403850049420b6821071000404178404624000f510b10341e403842c607502249105410500f5651292040d2a0000041034842c00d03c51082050510201c3c0c0d5482e28400c03242d9001800340d1003072400c0c440c07090a6001e04416010960300c0381c01408403130f2440d14207122104030440c03419001061440c0074a401412500054804041145000c01168218000046454100f41c1040640000f99910030048001c0d2041e440c00601c482e0400c3e1000041003c13504d101e9403054840e4003621580b104003001040d042200345680b0001404c0d004903800452800001406034901a0341520326101400700324510300b18807a8800c583c070700000207850008000500280d0401041104d102c032040c240301000999000015100d4809440008007080410a09502072072010342d120030742d250f5929111001100a000038403551740803d04000024800f440c05a040320440054000058401c2c59142ca034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 32065643 1250 32064393 32064413
    0xf061806030c110106090b0a0b091008040c050409030507030e0d02010905150d110a11060108070e09030702030a11010906020a05030f0f0417010209040b06090f100c0204020d0504050c0306090307 85
    0xc42010b100c90407103d0036a161082c02480d0140092003c04500c480980050040f95a0641c3c000d20406505022104055403210601041328401d4900036003c0d840b641412441d0741c9080c1d21865000d460100e00740c0c01c0507040805412620701a0300c1c0d001c8109510002c0c0890a03122201c000e002620040d0280018a03082c1044011a40c410803814100310240c0388520440340910038040b1080c101048440c14258042050341c4580b0040d000350606514041c480c0c1d81e15040b5000c4d000d02100100b00060090302e0400584019640007011510306010909108049170a0b4291040c00074550060104842d400000c00c401e030168800f0003546410824226010103800108012400500c104000524101e03d501140c040d1182140010b0340d42c2042000c00c0200e030b2038445801e004400c140070700039055075100390b007444908007035600500d00140c207141180c00c40b0003180003e5010b880421080403032034150f800309116500c04c0003140c0340c1c0f02d041010503075192011180410250f208100000010301c1640c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 32066893 1250 32065643 32065661
    0x3040b04061e020403111207150302090f040f06050a0503030c0a0f05030405120709140c0904090c090c0914030c0d150603080c0a0b0f010807030605040f02190f06180603 74
    0x40c2d01d50045851441001680d10503031046d516160021001c00c00c61a20005004084500000a110080c60a955901c0003501000070600f4190302285500c01d5881c0da60030406040c0d00200104100c40c010116031000b046079004060084014070b1010849080000840d401240c07400014801c00d002603a55900715405110300310703054081800000b0b002c0c1c840110012031140c680e0060280d142c10206032320211114540c80c802507014040a10200841003004c98182c160b00740d07000306c0c18820750f08218148c07901c184c0c00f00381c1842c03503d00b402031504d6100c49030409a0786806140808683c101041681d0380d003242440e59840300d20700c140b400001d510042100d64030720040300c000c0340b0b855994607100d034113400c4907000c8412a00000001000c105c45101c8155021042135281c070515410048801e5807004c560200074105035a45001c5000e0001ca02c04203041691f000b00910a4040076407001c049240482c40f0b201041904070801060f298007030620b000072070001a80da0940e0515150080300940783c020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 32068143 1250 32066893 32066921
    0x1e060513120c09110d0b0a1203080603010905030a0e040b0402030c0a0507060902060f0c211b0c06030703060612230612010903050405150f180307081903090b03040b0406 74
    0x80800191080316004d5040300610503041e140e200c900518030320080e221b11070b8800c2d220703042d56802031002c50011507205481c990546040c00c040d0303680c0000b10b401441c000c00c02800300e11000c0760b15002d29034003094102c16007005903024041ca0723144106000590105071008401e1510038000c02c0089403180010340080c0340900301c0400e00d140642c01141307559104440c004000c08000680c000300c0c90f81080710101c00030800307101420002c420b1015031a54001c0c2d124804078042017094458034088200002018900020300f400e50f641404103000d00149054807030750740070821616413100350340c1c50b9128240c80030140860316440075150303a4207500e654000804450303120248000720180f04c002446115017052080d01c0720ba42d528100710800c81500c0040801580da02c1c010407100038001c6441060b0782a0a4002011030355194aa100207403d00c08180c001c05550b204030805050642c44003036041c0a40f500035114402c029403a20011030341c40c4012100508030760213103004900020f15941c0b0030101c2500203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 32069393 1250 32068143 32068163
    0x60b090d0510020c06040b010518010501050c07091104061806020c010f1403040b06040509011a210a0302010f0c030b030d0809070b120a0b090420031005011e06051312 73
    0x1e0742c036010481c1c20007050049558015400c020800c04003004080c050901101d83c051101c90120710702a6601c4140a0641048404900c200b07500c00c0400483c009480c0345035050091000308030019401e60414401d140008212400c14840301480342c4400d020b031811a07002e80b40030b80302900190b45000404030308804105009000c03c02554140d0040d50041d4456882c09001d0f05156080006a8602501e03d4140780d15189070b600d10a000c2e400035101440040d100320450900045080c0d2006111000070034940c001e10104000305a8198081082107030940c208100381c1e05d0506c030490407212179006031a01940451030540303d29026015281c0c0c044d0164048a103403645400101e40c480d0001004000c0084108003441080c043c28054060310381c8085d1380d80b00b9a850540c40e07e40d00451010000c00d50842202c200701d060741c5040c414a05410b0003c1001d11a03540d490f0344440000c102c0008110071140140c0010034528032a00488803038038911040b200700d230381c1004c502210900c42d660701203d130500c00d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 32070643 1250 32069393 32069413
    0x903030804030203040b1902010b010206010518040503070206040b03070306090501050f040207050106080712050c06071e080705011e0c020706020607210908040810020403050601210b0411010f03060b090d05 90
    0x100001051007518001c03510347c0015a045000e0b095400c6c03101e42134155000038005000649801744605000840085003403260780312814614150b00c20840301070b4000400140110f502c441c0280110b0117098141e504121860b910080303030741181c030203000381644402001c4d5065824a81134028141d064010400090f015a5400d0040c2c940b240e254032142802a0503143c0100f840f505001d40b141074402692010314003c4996075a110340c0ca5040c41c00e40080b40080d0303004080c0554003043e280042c1d409070007000404400b9a1400603252015448103d4a09000b901c41070305201240000c100c03150f45d0020115520703044800d42d9030002001f0105640c0d601c0c0c070300076000701362030703024100c00e00d030181209943c0d86050406090905054403042650a801003104100180001500c02d0441d01500e401e59011201803411030961760000d400a042c0304144010320082c080458102d1204035801d8036030001c1117407801800d40a0b181c1034807440b417020b0010f0084003964100a001d5511861141c01587c08600e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 32071893 1250 32070643 32070659
    0xc060f0c010627020f04051011060703020712051206210a080307020c060c0712062d0605220504030203040305030301081c11060412030b030d050c010b01050307090303080403020304 79
    0x341d0b90320542c500d4080500c190707019103158107031003920383d0511802d41c41d08600c2c100c0640ca5109504c1101d004641035488070b560300d41710702c8080e01c00040c0a01603421600740303008010302a402850080e600107034054881c0c0062030003034086038407070600084400744550b036444c108007826807940c40c51240c10070440c0e1800410381c0305210303a010780d921941c5183d49074105480020700c0e00d0340c403545031800303682c0411042070710101c001a2581241d40140e5003d60f105114507000010f0405082601b42c06c0403004e0b4036544032030050000080c00341c0e83c0340007004030304e60b41d50401010740e200703450b80074405d0040d0041000300003160704a00e07809800b90044a02d0a43d49545103461940264404805a088020307070414031164a01241104d0000340f03400001020711f503142c0c42d1169005440209a5800703141782c018414001c2d0403442c00200c0040549507120303182c4ca005007a560000c00c60301815442c100c941c109940c041d600762405070300169101c80341207085640645014070050000e80651000f44000681030b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 32073143 1250 32071893 32071901
    0xc15040b210105010f05070f0302010209040609020909070905060405040f0b0904051005010807050a0e07030609020c0c09100b03060d03030b090112030f080106020c1309020a0303080f0a020406020c060f0c01 90
    0x1c5040c0402441c4400740c480031440c40a0180c01090411584e1078480580030b40c0201074a02032904099080744450b000e24040c0c1c028852007080b00d4005080100008045485034090205850255016035103566002011a801c5c1d070280502580031005020500c854201940905034200505c100001d107041e0b004002800070500311012541603012601444440400e4042c03032303005081030b40050940a0401c400500542c03201d0040360310400e460000550102d10a420003401403031444021540c41803401c0382141c030b41d001800414060840003002c038804800124070502207e00c0500300c41e04540f02c00b002c00c890403c00d103c09404043d11040c4104841e84c0364607880d4002c01001503154110002464003400d5408090449014440e040300104040740d00440d06010411080701e035030150300d413640880001420000e07006500200c840602104045d040002a4040c0506082d414459910040c0000c01d13446079010b061700580048812034910b08000000e001c0140882c59401d0070148207000c80381c219 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 32074393 1250 32073143 32073157
    0x1050f0a0c17040c17030f07020d02010e0d120306060e030a0b041a0907030201030609020307090510020a051501060206010b04030804051e030a060b100201090f1106071704030c060c050c15040b 84
    0x80f05202d20b0400c00d60500d00086000d449510002c3c2d0b081401d100b1011f2054090b4481c041e001e0140e80300180216032045401d18200c4200800440511400f41450700c0703200e045c81350000100e403401c0750101e02035020710315900d9144c0d002402080300207200e0342e0306514410040c100b1104c2c01c14503941c03071000e0034141000910034003070300d030043c02d0162030b41c0001015139026a2007040158410418400d0050340701c10301105445066a8074810014038020481c0713021a1420b016140e0f000c1c1406500c2280c2c0c40c94004e0b4101c408a50031140c4590700c41120120302c0c852880000c1c22000e081004002c81c1c20004110007514849480e6459a40030080103e420204030b04c00c12a0000ea0384c0b0301c107501c680381c032a480c000d441c5a1880200240304581c0c2e1000c902c641484000f40801c0740603ca01e480e544d1f0b455048600d5590301040500043c1c544440380815a0003d010445031014040d9000c1900e52148007012038550304040180009010340003404070403001e068682d405c0c1071042001081204a201c01000a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 32075643 1250 32074393 32074403
    0xf070b0910091212080106090e0a1e0207050303010302120601060207140307090c0201020a0f0302040b04060c0203030d022a060c0405040203040201030b1e04050f1608091903080901050901050f0a0c1704 88
    0x4c036500300b070001082003505030402d0040c003019540600176a081031141d03c3d40201031344d0f8001100d40c02c0720754109225922229010368070740001412020088080040c50407a40700743c2c0d90105103c0621005905c2d050300340560401680f220030300300101006190140d40205010341a0b4411941741c5414030291048a1220000760390009012803c0c5030340b100e020006004141740850500e400d01d0100c40c410310480c4203c0c010881091102e0301507560a00450f0800c410f40e94085541d03810304a1010424031144440840a1010300ea141c2ca41f20b0002c900b05101300c0d80103642a1400341400e040000a42004d07000383e0400d0b50700d17201c00030180c5aa20041d03500b040d4000030010442441820002039400c001c0110403000101824030510034142c0c1c845a040c180d460404c990742d983e40701032142ca0446040030111082c100d4408044c20715030003403586c07401444950000d0081d6501c401d04c503801e84000b65541080d4101301c070006011030300c0c0e0b07910440c050106032030051030b403888400403501400400d48064403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 32076893 1250 32075643 32075663
    0xd08040308130209070906200706050a1403130201020709050402100c0305070c0807080c0114070204110d02191b0308040219090501080105220305040e0a0f1a030f070b09100912 77
    0x44071541290f445071440f0008d1110200ca409040ca055032110300c1c5100e44414040c002c80c7c03103a0104d01440260000c0005103000607100d140480c03580058140c801d0081c4d016005e848800f0494950078040c5500c07542d0058411040704c044d90400303c401d04074a2000307504001c424040d4000188215100c40010b0694a008100e00b82c00c00702c140341885a4103000605200466103143da2114800c0c1c1954109a0103c4000a6041e41203100418a10070301c146140c040d440059058684120960038406a6101d50b80c0c200352003141540c404800443c03920054041450000001c005140201c420000e03050b500007400304071742d615160323981a281e082e040302440340d440d1000c00004403e425aa00c44491203541001d8144205031805461441103005200c13080c20640c00017170101c0d07003680100980322900c19081104051080758540d0303821070a18440d210b40070710007030380c0c9410310300080300c2003035504004400d803400d1101010017400c500042050b90030b10001010008181c005040400708c030a01500600c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 32078143 1250 32076893 32076899
    0xf13120302060109180c03080a030e070612050c0301080c1002030c010f14090a230109020a03080901030b0405060a05060706060302041b1112030408090d0501060b090f030d080403081302090709 84
    0x3406507105c00140c0400807044444c0c0b000801c20000c1030000700c9800150315a690400d10608a01601507410b00400c903228158002a009901c40b819210300340100c0c80801440c0c1b0b6511001c5010321083c0300303140e901d40c40402c41d040b8520f001e0001c01e1a5000500442c1c1c60201000f500b2429604151a1160354541c0c0d412540408000d11600ba540940864003070452880c640d41d91030507440d8841d8640b504c00300d1070700b20026004025840344042940040600040c0c5030303285083c051070785c89013103000d001a04200c0042038a0070140510340c0240402480310b038801c0d0605003402080c0d04000c0081d112241c5642c00040980c643c1e101395104641040e609503403464860f00041d0481c0182d41009215038084003048285000490589401031790140000d691070788410001a0b21038000c000180c095444c2c0030340015000500310040076100760075550203a080501c90101034840302d2a401b00c1010810703017000500064071030468075501003414071440110190039008203040100c1194540007107130080100b8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 32079393 1250 32078143 32078159
    0x51b090f041e0e010b030105070504151b0b0105100c150c0c0b090d08090303060306011203030219030c090501021f090203030408030a0e040509011509020c070b0c010f06050306010b0f131203020601 86
    0x2107400317400207070300a100505155000502d2881688140d002c2281070309409800b007403003002540c6400c40c11103002104031806040c4212907910a2251600c00d64000b60041c002c140940940e460240d00621590301c007011000b00303040501b0380341d45100e04100080c12007400003210442494080c0912a005019034200705030054100800a8551000f40d070080c01080981c2c2c0c3d000403140d0540c0c0c407451030700d18103280520381600130780260340303400589564035500700c0b401c554503501164020100c0d54400c2400c81c0d0342d03001681c80e605000d14482c42c0f020307403818914051200d42c1105801c50b201a003202c3c0b40586d107202036800c64000350b58050000340402010701c8140750034012a030700100300300001c122100c000000b4041a20551080601d85038010a44184090007801150028201000015035032a0704a100c0d50092110103906840c0500c0c042011601c0d050006085059032102505640341803829401d4101680000c4544580034140b6440842d0b000089809840524400e0f00280083d505200304 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 32080643 1250 32079393 32079401
    0x501020c010504030c060e0d0b070f0207090c140903150f0609061002060f0a060f0806010503120405010207031709060a080a050702010506060901050d0605120d0201051b090f041e0e01 80
    0x22030304010043c0400c1c00440c074001d0b80b810488445061144441903c440400c48540d40c2500150a00380114100400a5044249421001002d42c00d441d9955107404001c4112080c031b0511700005010200d0817803200c904a8010909450018110ba4501034004001d02019608480301c004c6000008140003080c1010b07100240c110200302c80e64005280702442c0255540c02c003c2001545030440c002140104900f070f44080090302c608101901e10649070030600355242000e10400e030003485000403201e94240c0000a480982d034050703001c1c0a0032842c603154a16402c1d180a89510460740030081903106039154402400c00a40c1030f04c40104624200401d101210001461b04095904210400a01d0ba4031202155039250090a11030f0719074450b00302d81c80040c201078000640200c08101d0503000740300e0005c2d10000040303d0340e0007881a543d50003d0425544c09048100f641d101042c40507880c28648000352000c1c104020b440000d0390f0701c0011402c101640d2142001345810b903039a00e440310218003801 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 32081893 1250 32080643 32080663
    0x302070f09061503090c0803270f011b050102040f090b03010e07060e0415080604030e0907020c032109090403030204061211030109050402240414090f0406020f0c0a080301050102 78
    0x41c040020a02e846010030141100c01009002c16641d00d05150411603840005005840d014007203039200d080c000070f4030b001441c084a040d0305a418014030440b0624003c3c49031035045a06a44600481e400d44140b41d5007c0c41a000c01c80703d80d5002c3c803020400b0300c00700b20318000901c41c0d0300d80498000140e005250845160581e0a4115001503c0a1100680100c0c4d03210301c507007080d640011150660b81808001007802d07000003505010f20780612040c55404500708803207403c215007500d081d8032070a106a80d11512640c2854168102c0c461040c546c01d60015a2240004803802c000e1400d0b07030010005104400c211401c9004c00e82c0410188109a444100381c1c44900603024100320b020a5000c070310a45000500c10210590340f507000080c2151a00a81d0710f400202d03030419074090507008450b04491b50006d001c0d50107503600c5140d03511480d20346849414001d61075143c055080e503c0710b0712400040d40c014282290220001c1104a0200300100003880c40140030700c03450340e00c81d41860300080c1403a4140b2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 32083143 1250 32081893 32081909
    0x31e02011b111203070903080c030315061201090903090306091410020405030a12090f0308071208010b07030c111815040203010803190201060905090a0b06010318030c0206160302070f 80
    0x190804208030003d1000303c6007090074041526030303403103d004885d0403c50b500001c1a09001082d2520071110000c05180908440aa003003e00c080a5042c42882d010301c120101c82800e50a00401440400ea031003004a0ba02070b192922640340c0341c2d110700c0e00740c0301c401c1022141c0354040241d101d1081c20601010060360418202545060315200000c0d5450b0344aa401400c1c0c440340203045025180644d00c40d10050802114201100b42c0c0c0341480400713600107044c140c1d2403030b018035200c0f00803521403900c443c140e07040b803000c00f420521030351802c0316903c281240807102d160003010303100d54550302c0786520118060713040c0e800072007460701c04180c00300c403400c00d01c126010b00d0050006100206c404002d9840f0500100c00504810b141d9400880c0035210b01d600001e80e41340b4140610001c0a0081906103849002c7e44003a05d803901c41e040110201e0b10008480170059500301d0b19100020300c100c1020010380e000501580c10b00d00003010b02202d01d44502000c82c00350f40300240800c06490031864110040000ca = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 32084393 1250 32083143 32083157
    0x60b0307020f0609120f040e070504031104020a0c0f05010f0e010b0a0504060b0403121205150906030a020604090c1707030213060e090a05060d17090102070e090304060507031e02011b 80
    0xf580c2d5642e02d0360103501c00c400f00760340130503052006c00006095070010302003001d50303441c070b4106520013421650040c0400d4404100f0000200307007504140c02100c40010043d03071200792841c82d68441c001c030603000c80001c54247d52240c0c401c0e207192101e4083d04001003007110001070001b10b00000c0121003035480d0306c210300032810450100078100c0034030152400c50340c1100301201007004000c01203c1c04c030f42c40c401c14441c4074a00400d00c481100c41c0d61041078103030000d07900c6000c640c5071901015655440004000d5000a0401c030a01400c8290f400103001c01c489030a00e600c1206003e1244584c0010484200340066800b041c0b001c2d481100544200040065050804c04850000c000c80c604c02d40003071200001303944400114009844540c220800036400c03a514900ca01d410041d140102d6101080041c010302c1069800b140c0000401e2550b0301800c503c80081d031400340b03070860603181c94210500640c14008001410061000007241111804007141c3c00040c0080e00089507480410609103448204111 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 32085643 1250 32084393 32084401
    0x17030718030203250806090c090a0212180118060b03060105010815010c0c08060a0c02010e07050d110609060726030405060601080c0c0a05010501080601050301180303050402010909060b0307020f06 86
    0x40404c00e07202410100c00321601c20b102d0740c1800b01e240b40c0154010b20b4140300d00c1d020480c00610114a26810303110807100c550f402d84400c615030003039000e1000d85001071121540810010a400050000a001ca0070008903440c451500c0c08611400d240005031030b4162904060500d84c9418404540940070074282451913040c61441498018407200d00641400324461000d41800500ca402c81c000308920303021551a4a81034492901400d00c0707000700c602660070500070811000d008120801682c802410b124019040c6480c2e46ca030340908038184a42044d02000014115207402c4001c03c01d0900031403100500341130740c40c051004511011000ca82400e014024000090302c08586260040301c00d01c0c19102c80d49411003000c030302c0d1017421010f090512420002c4420060103420180c12602980c0990301d10785c0e41c90040c1800c0c4c03980d820080c410081907503600400a4081e501c0309800c00c1c010300d025221b0503158010301d4212291074000540e5800b020080042103903042040001e5100c2e07002c060b05103824 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 32086893 1250 32085643 32085649
    0x30a23070807080309010b041b020105010f05030c130b0303070305070c06020c0a0b070c0509100e01050603040201081b090613030605070309020f040f0e010204060804030809010507020325170307180302 88
    0x611000500c003d0f400400700c0da114409400c000d103509401041080b031001c50340f541501420f04541d4550240d400d143c00061041122101c0004440024002e800800300400402017a011030000c505001580e40118011503242000507001d40ca119466035641d41510b4281102c52900a6100b40c0c119440300850b0a10340d106c4440007405c55144400c0c00d034803407449140540c0c048400d604045c0d0005003c10800000c4880b40c8041400c8940111105034143d8864040c00719a05c022900680400c052102280d995034440385c4504446806050003801d10003803400043c155400f0001303542c0600d5008806000780a005d00c030301600303c059400c082000401a901080128558015461055030b45c1e1040072400c1416070007170102d0302d0102e4021542d4540f43c50380078103203c8050f41c0540c0007030200000644400014452a80201d05d1900254107149042560381b800d0184112070581c4540d80f00404d8001440e40c450528064071812040f035228606260001d00c804071070480340943c440e4100c004c02c090b807 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 32088143 1250 32086893 32086897
    0x714061024120e1005011e14010f020a05071d070309020d06050c070b01030507030b010510120c0c060f0e0c03070506070807020f031504050615030c090414030a230708 73
    0x41100d04003007219008940380c400040030040140e07502c500070343c94104e03042c11a0341d002a050b00c0422038100369405036240074043d00303101400750a80d10114030700114115030081001200f0f0340810b1040f00c941080c141e41e1107003400910785c4440d11100e0b07241700c45c480005010240e03580c0006c242c03808200e41d60040d000941440080ba1300507200c0380c0c0c5c0c0c3e00440c01c411850400c4030720742a00001400c03140e507528941181d50b070042d03100a40b0004507003c008515031a00485801d400c0002c2c4d9101c2e10f1800501c16110700401d840a0710000707002c500c50030301c0001990350040e0088105002400500c81c170807080c42900300b01c030500e0f01c10300c240c0164905010710740d101401d80700c119401c1409261110701c03a1020408480c011080560f00d807080c108407414040381441c80d40e2040d88510240c6030141c981a9404554544e0310300350982c0754006601050039420081c0c00729911901a40b40c44201861242100381994402c0c0320b01c50010300d00000c800c0640c164803481d0040c0000365001145000c49980300e504841c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 32089393 1250 32088143 32088209
    0x30702070e0f04140c040e150a060506030c030907231014070308090a02061201090f110901051e0d060302010207080303010b16050c10030b01030b031b120307140610 72
    0x138440c08440b51403507004020104154401030300400142e12002c44240e80c1e0030114002da80c400d60685d000171040c4140340140411998041c1800c0d0031a02ca0000ea0b80c510782000b403010050b803003898800141d220004041070140001220044000010b9005005080c00440c0c0108103206205007041040c03030449013100c260b6500b41ca005400c5445034010541003081c0361002a40c0200003080b8a000c0d5001c0c0300142d0704a5648840800604080c06203103801e071804070032518001c070b20501282c0c030075500440040a0301011000412000c1c2c40e03c01b80300a0503044020b65a4510355280720920440d41c0410000b8060703c1190021400c5624010307007144648142108044190184c4070204104081000200d92841004021209040000900500038006c401d01140028100100221030b1304000c15071070000d03503100d140754920000711414071031900b262100701c0702e035440104100b00205030142c514901c80841c0c000601140c0c200b0b070a030540303401400e40049081400c0440d080001003000031440340c1d2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 32090643 1250 32089393 32089403
    0x140103060303020d050a0212070b0717010815040f02040f020c0118080717040e07031a0609010905011d0a14040c09060c0209070306030b090a03030f0603050c2e05030702070e0f04 78
    0x2480c1d01d80201241088c007621040c409600000c21200c0410000e40807152103841295030351100d4584808020698290038440c0010329002a10320b03600b0301c0454071030305034403d001d4201400c5003005540441e0841b2503043c0914402680411a00300e00c100a004848411b090107040d40f050185039152000c203403150040c0182400d0788500b0712400785500a0980d001403102c031204209505c2d024001801510644060741c0c0d01c904541641e9025207450b405940114906941e0330311500e080070015900082c00c0540014012a0690341c043c0c2a542c079040c50300070b440d842d082d00200448000c00d010035204141000401d101e0b5001d01403052a602045000c4416011103940d81d46450302c140683c0108120341000c4d001c1011201007004201c8002a8291618840c1d901000340111001402040710702c0e5000081c00b582110b20b01c0c840c1c0c0e02c4c00ca101c80107042035908480960050303000c0042c02c0740041c801400b005c1040030042110243d0180181001031007211104003040c505045902c00d020b9004000600d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 32091893 1250 32090643 32090647
    0xc032a0506090705150c010b0d050708011404030c12050d0e070e010501090308032d0403020c0f030d1b02031e06010906120206030f0711070b040503160e01170a02100801140103060303020d05 83
    0xa00c40c00c0941200e82d5592340500076440c580b10340e0038241d8a40c42517004480d030799820082c7c0301c1d4000b1300300001d0318400c075010781d100c80b071410341e590b1038464040c0100e0210301044014401004840c60f54850700f1421800a4001c004481c0b0700705000904a10590109051007002c0c602000030032801e0b0122580001c60460501d850146c00d24030821084022780d505410a0441e0200300400d0b400081c1040805011103031210001d9440c0209070348c0e17400c584141d00014204555599800301e04402500c2d20364070007416140007000f01c02c80103104240502013184958441401000142c3c818420705001e003d800742541483c0b409600030881c035203c094060310402c0352140020300410300c10585502e5820070003046d1480300303a54850700305443d00b160213a28407074041d6140c0070341206a4104040100c0d801e101d004001d6a280c24010205107803c0c2c44160118054a101c2600503030b070300000b50544407000d46075100301d94101030740d683c0003c00201d00f584c141843d154091012075000210100d168075a03241043d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 32093143 1250 32091893 32091907
    0xe0405010f03030516080d060e0a0b01051e0706020f0316030b030c011407020d03120c0203030f010b0a02070b040602010507120b03060406020c01020906030f06091609060c032a050609070515 83
    0x80c119601e0302a000d88580c0000c1942807c401447e00034004a0304810048591074072500328141c200c80c84030b100140401c004100340d040107140120301c4641c80c1c110580041c149415911050103a070b000000c1602403120001c00c00c0f81d42c51000b0081005c101e042d03c0c081001402400c04603a4410f0418405418003e23010101c50a030300e002d03011500081d42c0030b4646035404d0031514014105005040601540500703200d4032002561000007038a108a0003800e800103680d1928244011079440004410210b002c0c1000200750f102500740101300400351540002001d1810103001231050080e00c0007160003500b400d001c194190380026030582c1181d00010700683e6a4000307511580203104620016400800100410032203012800a25100e03410a4030480050b40c0c030500340240b04149180c0b281c010a240c40814002d851180d4900c0c0d41042c4a03091039603045200c038030070708060301c02001541c0c4049806004402004418000641c02541d00300061141c5404c03c0c0000e0342e1104004c01c05110940045241 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 32094393 1250 32093143 32093167
    0xc04030b190218030106170307060b0f060301140a060503070522090c0e0406080a05030706050c16051006090605060d0e0a060623090403050a05030403020c1507030e0405010f030305 79
    0x2a00e0803900e00011907688882c0100b00d41150400f08040f4882d5103071402c00141007a861107481c24460803880a103161841c1d0340ea0b14802001110300c0d454004801035010040c030f403075050055018291078103d1483c2e00c80d14004014500c8000d40199040010a1051040c0303140c0100070782d0a94901a1007400d49400458050345900246038414016941440c00742d2500a41158a1100503c0e042ea000e204031620760016668844021600416030344c010440d08020a8403a8403094010807001c0c005440c0070b0b0b03242c06802c0300c0d40c078194040d120350b0031004500302c10208902c510360041264480070b004039498480002c0a600680010b4032026880c0e2104901c1c0000c148034488800f50700c403804205041d1a4200c41c419120030b011a08458085818500054602880b0491040754117640d010310705045040120345907000a0030840a61140160221007070f550f030340c4010301d240307000c80c01c20351030705881d040052403001c80c088072038007840c07070400148960107103440311200b90ba81505000355110b81350485 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 32095643 1250 32094393 32094421
    0x40311130204060306080601120f0b0a0905030304030503010602100b011409040e030c03030915040c17030d09050c100c050c06071e050d03050105180f0910050408070308010602060c04030b 82
    0x180c100340620015021980d680c16034860340590300e000d0110f40d142da880f0b104c0803210440ca2080504140c10350301c00140010041d0b00b003143c1c0540c514070041205002656010303d1604166070440c0420804001440502d40c100940900c81601402c140040302248002901091100f4a800c601303020000f00f58485407116001650707042c0321117007100d075290300e1742c001542c50b41c00a56480144c1e000d03450030a212004950095801140c0000001103401d00c0d0207115500c05034100f02940312400140300000d12a2014441c4036038150142c0050b040d0100300c082040b402131181c0c035244041c00041282e12011410004100d10134400c240c505a81c0e03401d00381000485440c1c0c2a06260131550700d03004c4032041200c00304156070292140c2c0c03020302559032540100510710781c8003010345c03030700036000400251603080c01100980c103c80342e1826100740d40c0040d061042035400c1140d065910400005841302007641c0581500d0041c085407020300b40a0170440036a0440b0302c21480003404031a80c40000c42c05a00403045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 32096893 1250 32095643 32095669
    0x1505060103020f12010302100f0206010915170106140303040b160201170c09100305011809020103020d0c0e120d050a0e0418050a050106060201020a09030b0907031a0109051b040311 79
    0x1100c1070720b4031513481d508440e10200f400100d01446400c9030711381d403141c01082d6905203028990080c080b82da0900d50810b005184042c1d01078031006008400159881c0c1450460000164500c0007007859410300e000e50015882d003030141c502a074010403081280307001500c00e4030040041e64550994841040c00121403c2c5164414092101e50800900a1034203c010013020903103815149030742c5e0a480000142c0c04c0300d400344501c0194940b0603010070f00c1100079a0200882e140705040040c100b1420030401c0d0111035509417044085104c1940c0040716103851004c400f580070080c001001130050ec000b00400700c0c003c90100b8424015001c50744140c0365961b8106030b0650b10640c00142c010380003410a5982c4545800c0c0130398003940f0b89407000c07815900c180200d884010003a00c956845600e550323241006032200805907075690080100c040001139130718006014001c4083c01d450740a505220742141210030191040007840107541400e11a03000d0031055404032034004003014440c141e0702d0302007030350301c0c03517403e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 32098143 1250 32096893 32096917
    0x801020a0801080c04091a07092615010b22050301050c030a05070e032d01060902090a06020304140607060e0f0106080f0309062d0403050d0f0c150506010302 69
    0x1140144003181d20801c0207040700c0d40c0704200d941c842a50414002110707118080500380f07000340400e401440d04128041a040803d914004414582d00c3c2c2e6030040700c20711607220710040401401513041c070000030049802e43c0300d005000540c83d5403404d0f81c24116446280d082c0400c04940801c03405088241c080240300900000e4024816440c02c0741c6a0b9030140e01c01c0310b01406941c6488040b80300c2d43d1241c07207041e164240c0031300100703203020390451136400725059141c1c03032003a1420340002c081c6103000a0190f4001840c0c030010241e203c0c140901017061b440020f4000404542c010b22080214007012840c03e0000281070b01c50a40c0c1c0d20f928246035002c0c05111800d84558810880007144440d030550165045a5030042034800180c4c071941200d0712441038407400e9a0000c414041c0c80f1600c26401c3c03a0000e500c1d5280c1c1d44203450380002c0c044150070f4105502c113880f03d41011250380101030f04200500c60400e620702d4175034403080e95960741d80480c04440c014a0300c3c0e0fa41d1200003607503903401b035812500a62140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 32099393 1250 32098143 32098147
    0x10306150905060307030818180601030606051306030207060906020a1d040204030201080a050603010902030a050105010e06060309101e0603140c010513090e030405150a08060604050a0b090a080102 86
    0x24240900500386008203115400580c0100280c40c01451080c6070140d84002c01810007a49161500c206a81014074021004031414500039425a211039282d40c10405018007407100d8507080b00003604581a561101041c0441001215000c25200300c540b01610082d080050702c610807810305a0040401002c0140a5880002e10031541a04880e0f04a502e210b00507a0304019810302d410f00c010390056100080c041005500800d000c41180e8001640c00302d0050f0001030716920640010f0700e0900d43c5a01515541d40d00d00050100c4c544984410340c2c42030041d10060b103175090402c50320f5601c116001d0080081d556810f0786211084405613051126201d405e070a209a644a007001d4100040f034030900040c0c0d1060030011030b0294010002e40b12990f00505582480c50701d040c580303038040d00021030114510f000c00c20000c120303a692008817244002010940795156083c05e00060010003026045500c00c1c001030008201681d5440c40300000e94a81c0440203807039541450200b200d0040b650000c020319400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 32100643 1250 32099393 32099399
    0x5070c1d06030106050102070b0f1b011103040618030503060d030311130810050f2703030709050f01110304150201020f04030f1b08060406020309030c0f0601080d050f09100507080301 80
    0x403403a605030148204030003c000b016500c0005a949044a00c20f0721b0381e0140034001c2502c0c840501002d4034090340d00e0007a0203262f00a02c00b40c142118036400303891151000201c00c0c031040c818903200d61000c000e0100c5035040f00e46026103016240f4040100b01501c52041c0c00d60b54010544244c20411064045142280d11100e1840860007000c88901550b0406c1c481c000e61022050410b000d0076019a1040720404115103811b2074207031107252044030321880202d130000c541e4001e100420055124100d40c0d5640c103003960400d0300304506100490112410851880144c100d150404422142200e254014103d41c541c00800c4c180c0c0039000c0d0b004030410101f008a000024050f400440f001c12611030700e80e00e510801c2803000140502824015005250711020004002405aa0080d504080c00404886c00c0140f101c600c81c1c80e02100003901c103203507007003440100900c86080110b008503e8103810606e003480f80c0d06a041000e4001d010344c052007410b444c100e01c035489000d001211740c10b54000340706a90729a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 32101893 1250 32100643 32100689
    0x803010501020f031204060b01050708030a0207020a091b0509040e0604080c07120314070206070b0406060807090c082a0301080c01020610030308130320100f091205070c 74
    0x10900c51940580910007090039031600c08400c5808182050580001680300d0b61214001131400619090510604110704008100b0410255105807400e0703d0150b9245413501c14003548019a074003145a0300c0c141340c0a458145403d5040c680140c0c01441c0030f54942c052440024084d0868100a030701a004400600040c04544002481c0700074510b070448140da03944ea4481e640c400f811582c09400070780065030340842c002055009000e01c90005000390304100041c2c4840c03a42902c180c50882d07000f40d4a810422000710309100400091980314410040c80e42c04600c0034103c40300c01050320b41e4520402d41204030f451643d0b20b10700c0200e12020340c401c4c1c40c0d42c0c4601d0032594076100100d03483c0c0584078090010340000100054441640d905650f2900c2ca500c07100c142411081c2810400c800b404184114421400400601031f032101c07540c2d1004102c08240802603104031507034104440e8860b410041840080b6062001c1007401c41407924280d683d495060502d80881001d076004030403000d0010748004400c0b4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 32103143 1250 32101893 32101897
    0x902040e1503011803020f0601050d020114130b0f13090b010e0405040510020a021015050d03030209030a05010c18050a0f030308040302100f05010608100602100903120501060309200303040302040504060b04060308 93
    0x40d00e28003290703002d0342c80f1410054bc01d4401c04000b030020b02d40d0610761504c01c9500014041280f107040310448820b841d2001001103421144111420301c0c40801d10042c40c550035079071040109886101000744140e0600000d0541500f040c4140c015922040424100034080041001690281004540710103090400031349a054420030a1a40e9003080312202084020a02d481e040310001048a020640b07141c0d02a0040d400c0700d180154940114181400492028010303030030b20764099610a075108541800303c4401044d0342e00b049009194240c400e00850f403032125a003007640d030141820a0185e40d82c0c03408928140c042e850b807031011414541c0304e1051080ca81c0102d4181d07a21515400d909a8a80101711200c613814410742d80164010454002c14180540c8030104090081c68800b84007035551003505c1c00d8810a038886800030766a0b042d62001c0c0500c5800d01c401030042d01c28003c034181c0e4500d00286c2e5038025030001038800c0341d0b03483c042010010030380e2114111180140052121383d54a00b05202e1b95 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 32104393 1250 32103143 32103163
    0x803040b030402030d08010b250b0405030d15030f080c0a0602040909120507030c02041503050105180f0304030b04030e01030b09090105090c191e0f0801020c01060902040e150301180302 81
    0x81d10583c80e6245c2100e018605c010306075515514228100400040b00350540200e03010030f4211010070104420101d5008241c0d284114011402140d0b29070034003000c1c608a0b4424903215a4000180c203060000500800d402042260002c0e605034646074600a010304160310341c0002014203200003000500304409410001003030740030b107108a200718440c0301e09880b140b007003441c000c1c001100c3c0104480140b8040d0b220a002d080596a049044c64403a5039090031200241c400003150361041c0f1b4006440c220800c1074100d0303200341101550030305282d036440348448032015000a040c400c14440300318199100368001c05038810000e0103c46036081910027640208019500d0714801d0081840101150821403441d50340301303034002c1c5482c2031580342c2103224500c08084412050700501b1901d0020b0f00c1c04800c8048801f0380401000144e0310b100f65140d003801c4403101c2d8009860240144810008100d030300b13450a60042d00c004054800d1a82400000e0040c4405004520401502446801450750008080c080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 32105643 1250 32104393 32104399
    0x1080705010e0109060e1306050d06050402040c020c06040b030603012003060f010801120204021b0304080f2103010509040317100603050901050f0105120705030d0509130b0f06130803040b030402 85
    0xc0e490b14000110f4400e94240103c0c40800c034040d110b03800e03505003a0000b804010742e0a4000485548402c0091b1590a1154003910900c1e11f03641444290318041c8560702803010b49000030000c04c0d0104000c1039490207a44a10070780b020000c0001030322510b081d00a49281d0340c44802032450800c3c034010a404a42043c0c4d6050300503890026200702950090001c24141d400100e44848019510743c01c100103544059960107040303a910050b5802201300b0406000949807581c0544000740b5220529480c010501c034080a5404d00b84003080111060705044078151041a00c0c006419a00c50405494260010302d0f0a0708200c0a4410004003009030806001034a209580901c01a25008429801d0b01c0c004d40303904040e61402d0f0300421040c5046883c8104001f84901070703c00300e5070340710b002a04107a02c500d1808085000003a403c4100d02d0720210341d00b100c2e04514410410311600c81c02140e4031250b4001081c0c011800005d0b032026103e07607544200000d020410840359655102c04846e00c00d030b002a503040380 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 32106893 1250 32105643 32105657
    0x3090e070504080c01210f0902060417060a0212040201030b030a0b0103060507020708030c07060c02011707050301050f090f01060509011206090207060e0604031b02040e010905010b01080109061d0c0903060108070501 94
    0x40e50f40c416840c0c803c0e062000c01815000b101e0031a00e1b14020900d00d001c0c066410750f02c3c120000143c0741d00e00504001c0a42a80c0c2000e07040d8800d014504200e0300803ca00d014074410480740700007440140d80340303030000d8080ca0000351740200c000210340b800b404d001c805040d45c4002d600001c00c1001d141c12580c440e544640c290b0780030541c0ca9800540d28066150b60748940d41001e4018403466115a00c0081454014074250030b00d00081c00103440310a5003520a0000154004010b00c803078140b040715000040010354801c2401d25151240055102040c080c1204108000981d260603a2007092114031880380380d0020081165070b807501000035400102c00b294900c4c140078680182d0500401c4041c4a10340507150030b9150f03040380c0d1401e80858281d0004990013680c42c400d0850320902482212030862080c3c00000701600950001f50030000140c0c081240c1600300b12050004210000c5101e80c0700c4055201500765440328450000796004d5884843c0d0907108400000034420f0b4001170940450700c003a02c40704 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 32108143 1250 32106893 32106913
    0x160f050403080f030a0b100302031005010504180f020c0d020708120304080313020a17030a080105060306010507080702040b03010e0703030914010806010f020c04020313020406050409020d030c03090e07050408 91
    0xa1440e005034840034107000d40c14890700c0c403c0c003462001150f100c108408009154540c080000700018091120034000039804820032400707841141c82000604801d0130018117191a01406603201851070800581c016281c2d11210410ba801c2c1d0150b402074040305040d00c0803c54010402503480c610b40c8518180b501c580e5491002500010301183e0180340c20000c0346146507200895154105e0302280f007260400802000041d48124003e01e484c0c40581d460003543d6a8588020000c1011006801442c440e550802c140020303a078025085521450707100030710b1038403100140005002040503e2407240c055007403110601c10044086000c901362442601c400140c0c503111715607106518200c42c22940411004d102007101c1d0b6020390b004c07145407804c2d44129804408920046010b80e0000e1b1240c5001ea40c00301d408104614060054001802c0203542c02c00c00000d141e0005843c5200d02200075003072000d085900c6043c548500c00c544090000b41403e007029007800f403801441036101c2e109040b1a406001d50b41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 32109393 1250 32108143 32108147
    0x2040513080403290a1d0f0607140d02210702010c02070536100503060603030702010804050312130b010e09070605031008060108010609060609030803040f0218160f 72
    0x500600e0703401ca20001d0410b4110341d0349042d24051030001481d1084d041c16840d03001c030820400540300b103071001c00100740c40d512010124a64584120b08121540013940c21000032500044c840d03902140394038101c800752990b0300090300c4522800404030895800014042e00701210860f181e0040c1762400300342601656150350483c202c40103140c946006811940c000c1065140c0896074100400d50240d027502801d1000b241441191141c43c00c40004120182c200009440e126550340024001603002c0c0505261010010703403a441040d00090502403040c0104050000401c242c03079000600d202c0e610701c01d080084103400c01c51401c101c00c44152503103030004140c424040102500810b41d10004100e03082c14000c0980c0d550b08003c100c3e00344006580d00025004604210090080054800004500d0304110108043d1901078010001340b001014040002500c8034080f00d80c40750b001881c6c4443e803c104c0c070018901d142010310310601c0544410034020424808140c02064204e0794941001d008020324003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 32110643 1250 32109393 32109421
    0x7020705060310060302030604020f070309050307060f0203030a05040c030b010303020a060b041a010e01020c030d05030604060b09130915020406051207080105030a03030b030a05070b03010315090c05040c2307020405 94
    0xc05024943c44003800c1229500a030041e40e013081004001505201c030651140c24540c210b04020b5000500d80e5000b0002c0741824400c50002d442585400c00c110140503c000c3d503240700140407402d0860f0340d03100240c1071028002c0800042c60b841440d1801d156901c1c06c0c000e69400400030140c807500e21b0a0a200c0302440d052240d5440c0326001d110b0106079040c1c0000540d4079046c4846400d05500500c14252007660f001d119004c001e01003a16030316100e06051041c84100c0d1400e0300040d03a00307101045803540030b40d12005820f104001b18440400c10000c41e140c01c091744041500701100850003c2000f041c0303190018050210030f21020380314001e942d03503c071040b076a03030401303204003070301508140300050203e4070a07004051100006002c0320546039890b5500c51070030086511411202d10084014030404c02a0880715410015074003040c1314189054460f4a070300240d41c421144200c1e651700c071100300c1e10f000314010103135941c0004400740000308000c1001c5182e4800e40089200c2e81c64070000485404800d21 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 32111893 1250 32110643 32110651
    0xd020a0b0703081f12030813080409140a050105010e100512010b0a030c02060402100309050a020603010608040c060f080a0504060b030f0c010e0d0b0115020708010c09090e060405100b04060503010f0203070207050603 94
    0x20000c01700003241ca05841da2a4003030100102421b00d104104007048119005000400160100042280c44440522100c60003c0c100c2d011303960400d0010800ba0ba44540d40581d0000e084452100a0004042c2610b0a12846250480e00d8210030000103005520b503018020409094605100c42d61103070b039041380c0754401110002c1d84400520704e030f104864826031040390081d10400458401300c069800103189600264010000101c00404000800a15585500c001d140b20b083c4681c00000983c0058100345000f840b00398a180e07a040054180003960b0068079074100007a054442c2d4490b141c070301c251101210416540070076604803500080b400e0440f23071040c0040d00080c0400c4540d080503040d02e01a01071060110851080c9000458200400c0c41040a10a19921802121480c14440c80c09640902c202d00c006500042d00f0800850404150803210001404c0005240c90001c00050001d1900790049609523281641220070040c041e40214080c6045400301d42e8181d07030750010060320b071004403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 32113143 1250 32111893 32111909
    0x5030105040c140409060207080a03110c0a06090f06090507090c090b09120304051507020a0f0e040204150b0c010203040b010909050d030b0303040b120f010b0c0703020d020a0b0703081f 81
    0x500b044040320f40d106a8120802c02400841e180f1000d490310401da80221758144c540b80b50004200000325092301c200300360b5040540c4039902340701e8181c2c46961107a982e200040d00203511031030608100a0001c14404400d6884401007044040307e090807655010580a5204690300e13100030800024080d001280c102d03050042410701e4081080188000c0e18042280c0005611040c000414141c2c2c03064036110000b0103c1012648584441c01000702c841400d42c00340c40151201d0b4030502010300b507000070a522a8040c2c0b80841d920300c00211004036031480307a00200c150701c40801c40240a0406400950051740038040c07810150342c135108010126010480300400b990700c010703c4080000e01940000845420007003e586c01c00da610f08140752143e100c0358602100c0c1d00c1440801c40d10f101040d018030b02402d00407906c2400d164100d10300c4c6544d0b00b12404060301c5015402916011562400b0203072000d006c0c0c1404a907140c0c0306a02d0068801c400554070615415135500c05140a0702e502203900003103800c10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 32114393 1250 32113143 32113163
    0x110307030c03020c0a030e03030c3301140d0c0e15090a0507020303011203050f0d0e100903050d020c0c061207080711071401120c0e0307050105030609040201050a050c0601080a0c0503010504 83
    0x11b560650b4600c80072216079405020900440200c1c880500503069078001048000302c40d0705400390818602c00301005510360010541d4014090700384640ca8942070244240e880c582ea0452608101c0501d40c5580c2c05810a0380810b130800c8032070b4070042785049400b042500c200e070b001d890341d401e40c0043d540119150740050713000340010803915200c410102c002c0f0f4020304109240010308078040721603900102c102d19003151101c261900c203400804c1007890425056000b0400040c03e44d80040540c81007041b01000e40d03801150715400b843c024005541c10100080003260b460820440d1079151403c03c540b000040780000000a03900c034060103001c854110070b280582600c41c00e01e844000c0c1907240802541c100300700105d80c80c01000c0c0c10b110700c002a40e040c1d151201290200e4082520303100c40358000750304002e82401402415250008040e803c294242000d07a1501c030707011022500d90052800141c0544203003000010300a00114000707400502412015406a442d002030500b82d58007981c004203440d0304 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 32115643 1250 32114393 32114413
    0x61a0909041b0806010305060708070206060d0821150a05030607020307020405040f021801150504050a12030311120403020714060702040903090b0d020d0c02010c080a02070312110307030c03020c 85
    0x404122100240410700c03901006072203c0712030345842c0d0301341c0080f103055103c441030200301a0404081503219032107100a05552501c90007080341540c4ca1000106a6640450542440d00900d101c0c050300c544443d003000610b2034103036a508860081c21103118010b91400b8004501c40c1404120030f407183d81349400651801b9200d509102c000d000040c419144105240361000043c1e41e8110700000100440c0300300703000395043c4024121004c10340c10001052000c1000204800d85a03d0398000c210307083c1e04982151200746003415005024070b0381d001030300002d001070410389014840d00c00768050f502907421260819100c45a08282c4c24285042d150304c41c40500188005281981000b400e0b80c3c480d00c2c181301d200e651120b200d0940c2d081442e000741696004190025000300a00c81d2103104080340c4000d1041e41082c4402403c1200041c2c01002d00a03000546842494054000001c4070950703883d007041030702d0720300c100020250000c0c0d400c200040c0c10005141302540c80fa00a8412a81c0c01001519881007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 32116893 1250 32115643 32115653
    0xf0b03130f020409020904050109020f040b010f0c060b03070303050a02070504110304080a0e040e030c0606090601140313020a03080403020f012f16080105011701110a030f0209030a06061a090904 85
    0x15115049030b02a8684e40c64a0050302c407501c0490145105c1c1001242c0d00305a4170401000400b815180390245160100701030440c1e038841d06017851409241000141c18a8509200014084881f202d0350981720b102d4001040591043c02003014807581c0c0c4c01d403032896407076004210555074955070301c0e02141001d001290229203c00c00404052031142400e0401c00035034000315068442d10311a68401c0c0d00b003c00c0c4403080c04424000796500071030856107102249800f2001910717040c070044440b0907500e00070000900030403109014082c8507400800c403048543d568a0411100d0703000d0b002c22030007880c4440c40e440140d400313035590058103402c90f0721500100b899904100010755000041103418490104020210200350320403201502182c2c00110302d9605090b9001180f101390070045549a24000c44121660307150020b603421a40d0600d808a0356003160001c01020f0b0082c200000e6060144040d076004000d0140c3c002c7c1c003110201244981d1109a110a02115000740c5590a410100b44400280020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 32118143 1250 32116893 32116913
    0x10b120a0c0e060f120a020c100e030a0f091707060f02031606050c04030b100303030605101b031e18050d170706020c0303101a0301080d0e03030409150f0b0313 70
    0x400d501e0181c02e02c04854519070205c1801d03140407062980c00204429950f1003404402d8000850078800d010200074000c1160380d9110300c007590400c0155003135000450030720605528000301400400003520300012000c42e0384492a074420100801e0900b0b102ca00480d0000c01a0b400b1140703100f51204801406469440c05090001c140c1d8401c40c204100c0480040c840c894601c0c007450303a280655645505600c2c010b02150840c4d00604e02c106140f1a96404e220b601800502a005031002c24200e002494642030350162100c0900102502c1446034003840a0343c04425030303075104800d07040807141c0741d582c4041c402c420201e0f80b0080c10741007a0b074905c0e40861007a4401815070520900c001443c00f4006068281540c1081e18107200c01e4103458000c00908100c0303a01484a4100b126165140d540341a00096480f10051104410f02c6981c0141d0821668244180d9000740710030030782401894100b90030481071540398000c00310031a00c01007000c501d8030401e0b000e07603103e420408403152098906455040c0c8007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 32119393 1250 32118143 32118157
    0x3050a060c0203090307080f0705040b0901170109021e0102060c040f030b19020a170703050f0103060b1201021801020f03070c0b180307060507020405090105070203161a010b120a0c0e06 81
    0x588004c002c90384841d01c081060100912105d00a400d80850184245044c03413840d40c807003441903040008041d86955450406811905a41550342d103c0340d01e009101d002d488440b401951004e140b04250054084403294451125000d900340e98850b07031000380303c8010340594041c1c884032685050f030500c0040c518500d82a04400302024545000510703d4518043c0d90100c41504002034032306110f91200404c11900d00d401103c076060510071440d140418041c000310511000d8503007516802040202c1e25003044041451040c000299a1008803800c0c00c2d21800c7c49910090040c07003258018192000040140c1e4a01c60388030341e1b807868091402c500d85609400001014070001003582507102203039801c00c0910010301d0903840309038440f01c0600401c411500c0003055141c10b6418a410000159408030444c0d0035600c103070307500c1e43c0186070b141448060003219030146100795069100101d01144e1050281070024141320304100583d46002c0b1110551359603440c3c1070013240e0b244104401d0340c80c0a0024001e4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 32120643 1250 32119393 32119397
    0x6040c080c16140609070303091202030c0f0d14070501021506061902240712090507030206030705070c080a06150303021221100503010e010603150506060c03030916060903050a060c 79
    0x2024107a8142002130075101029503500c1444100304040e00640f42d0f00c02841664500480c903190703a001729446108a9038420320408108010150640e90701c01041c200c1a00440802580201b14400307940d900d10780d001d658058031400042000c4400001c559a01c0343e04c003d000c4905040144500807030441c000d01140081d4042e07092294400f8200b8102c064407404128507610403818510b05c0503000041001d0604942ca0402c4906408207000164490480c9e60681d50300c1d0b40d82e920508100c1c1c42c0c1c02000301c001e03d440d950a40000c3e24101c0000d07102801070160200308550807903076440c40042c0e500342c40b000300580c11801403aa8680300ca8005421103003003850400032640c0d01c01060000c441b10841d10700306c080300280720600c42420300340308440f543c90a4070020485035095442e5044030f0005a40005501e41e142c40014110307440e69003c1d43c0b80511040b04494032410100c10300d5499141c0d44548903007030040e007800014418400d510110403240c00c0405032121180f07689070140941400302072402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 32121893 1250 32120643 32120663
    0x20a051806070b04050102120c270604090e060103170c190201120507020a050d02030f040b1b2e14040312151202010201050115020601051c08030103060506040c080c16 73
    0xf1a5452110034801ca01c01c1c0001655500401c01842e105880a0810008541c040c0a01000c8400c3d18405590120301581154481161100042d8851080d0b4110888942c01e103000011565070004519044c0c0384505654410030340c00d000030082c0d41c02280c000e60126845026040840d2011001b0183d110f401854500d201001c00700e9031348183c0b48140ca0400c0144d001820040505c501403040c0e940903503042c40a140381c040e0321400c2c80001d0040740507108110000095260458500d0100c0c1c0140240360b40565001c00311281090400b40d80201039074500c40c550708040e40c074840c1d02d845801c1c144010b40000c440726803610b403000c9502401010000248543e1512181da4003016200745200414845c44031035000c0020384002400c2d564181c2c030060a10b601a5103504d0001c1c0c0101e0154151001914004000044c48008081e42004108081c11824000001109121076500b2552040e2030523030301480f081d180c01000300c4005104031800d14203151300f0701400e041c001324107001806150082e10440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 32123143 1250 32121893 32121907
    0x10020a0e1c1a040b0a05090714240301081002090112020904090507030c1805010f0308130e01060f1b200a08030c01020306040e060103050c0103090c08010c02070501080a020a051806 79
    0xc90b841d00101c6202c81044548001c20042180803081180d00c035403400c0b018042420854020741c0d959805009130350602d01e94005108135074603804152141a000e0308a83e005598000042d00e41ea684280075200b028040c02d44525124003580c000c441c0309a006940354001d0326401c01480300290000c3c144e40c1e6216071528540400302d50300f0080034000d140141c038110741040c5850181c041c49000035580706965402c04004112141484000608807034000b038446644070f004002100c1c8001c07282e002105070100c10340c000304029030300c40c600019902050311400507a13541d60710744194001403424001c2144804031346200c401e060010041402c01406000702c506540c540d103580d4290b40000d044400e19a40c00b0042166a00d02802015007550945c80a0912941141c441603214482c0e40c500906068444402c42d04104180c8d98040c014060701000700f00b0020a44402500c545203846540d00250030003001c5038001c0d02c607200301c404195480c0c88440c03906010940c0c5140180364548684d5102c4000e000c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 32124393 1250 32123143 32123153
    0x41d0d0806062a010c09031e050111030709060206060109150e010201110a05070204200d0203060d021008090d031a010c020f0a030b1b03070c0b0901060f0609030510020a0e1c 76
    0x2515501c102da080300c3c0c0e02e40f10f02c81c2c60a801c6840140c99407080151404040021840070b070503040364051511082c6d100d810301c60411a0160020422866140000000f0040714507403101c214000d071101a801d441c080e80300c0034011a0809424028414002404150388a090340600610440c40e43c0c1030001080300d180b000c05200307054201040c01404a20006040c00031403909104100c844401c08480303408441360410403414038010104000c0406600001141c1c140e0384405080ca40c2a500a059408942c540840204074020944001110b4840e20226032084d600074016030103142281c40c0b0501c05090000011a0030a4054005a0300441c90502c00c0c403480d154101020007443c05102001094103100950030074a0100a00311407014400b8003d001000b5404040c640700c040c0c000011010580311104114014400d91340120030520800c0b00c0006c8482c1c010710804120707400340041d40d041c0b110030fa82d100c003607110300da00420001d85451190480c910300300300604078080750882d6648200c8480da4038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 32125643 1250 32124393 32124427
    0xb010f0f020c09090c15070308060d08070203010603202b03090905010608041e02031e0102091002010c030b01031107032001050405010f0b0f0d06020a050702180402041d0d080606 78
    0xa00c250304032007042d44850408202808142c030812181d1447c000c6651002808000c01503e018840c00210f0550720500180b0340656001c0c0390020b00801136540e917481d0145131416501d0341c4a90306004c20300e0038006850118005030706c02c1010010350044035180c2c9035141045035030a00480c10300c014020007080c0840c3e40e103e603901a200d81d440d4076400e800d02d030400c000d42c10911a441305030303690480050001a140496800c04c0321100001e803c0714400284101030190090041141d0800300440c4c1902c18140c0c15081081103087c103803070411a50006800450580e02e02d81d036604d40ca031408001c0b1800103803185416070003d140d1100c2c1514105428103035a420f54109480c191a85da44907220702c4010081071141240441007158000c401020070320100794a00c00e07900c4050301c059130106100003954010801c41c5c00c10340d03004040a4460302c4ca08009410981c068400fa8040c41c500000b49500400c0e941e0000d100f151054014960031300c118030700b03c941117001002e00c1c1d0481824400c5120400306206 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 32126893 1250 32125643 32125651
    0x30402030a061e150311100518010c0501020c060105210712030302160305070611090108070f230d050f060d0f061401060206040605090105060d0605060d0b0405060108100b010f0f020c09 81
    0x284e402c4250b1071401c0000c0e070a62980ca0040c400c6050441100c4056004000c984060326040b6079124141e02d404010ba0740c140791000c014215500004070400800320214500c2c0c180d0b50304a4269280d14000368803200b48200c4125559602e034400e00c001d00c4128020750025525a119281c05840c6c5001c6500c030010881020b18114040303440401c0760780806c07200d405402400107000d406942400c03000d070b00003841820080c280a0a200b001194422443c0c4120600000708040c5a1112821540904a0031050f40000341c4084e000f4601f1020800700d402d03500300c190242d0320007061503200c05007075100e066411031035040890f08035036182e203806c074203014102c541e600801d01600a48a20b14080c1030200503a40d004100c00350991505007004040d9441c0e030708141025802070000661941c0b0300d0040b81c4014812240944810300070820030080100008031075058900c1c0c0300c1614041b0a6609904090b105510006804291400035154280e441803140018454552041310610201a0045482080b05403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 32128143 1250 32126893 32126921
    0x612050402040b0a03030f0f0206280603050106060917060c091201020405030114060102060709030302060109110c070305010204031b06080402040b0d020409080d0c08010b0a0503181005010e0705030402030a061e 92
    0x1c030447d010301c2d4100503400c6413011f00340082e0404d4900900d00440240d0f04050317110312074100724802d03100282c06502840245610030020050035403102006801c0c03294038410340300c02c184212140501d051012a24a004a0f100c0c0e0031035042103800e00401105403444100c4038600d40d800e000000711640c090040391040c0c0c80070740d0401401d04050000a04201000f4007400c10b000b1005c1342040000c4d40050b1140c1100d11031701d0005035013112280c1380c841c140700b07151080300540305c3e812022052040650041c012a40305112808200b11484d1788100103290611408020030801c1d00010b000d42415040f81c6d811040041080700c0303410440d4002421114203541c00d840784000820a0345600d89148200c09020110b4109101e5035850014510040e1040010b0701040080200110760108a129800c00001303001c10103480d102c1d60441c04450060000344900b011000260000c200384500540440c1e00541d006405420310380034586816020702030480304c24140803954240f011320303071a841c42050b116801031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 32129393 1250 32128143 32128157
    0x705060702060d06141e0901090e01020c011109030f060c0d11040503030313020f0103060e13030c120804030e060403050a1b0b07080315121b01050417010209040608070612050402040b0a0303 83
    0x10500f88400070148100049602c0c0c0e20356081486c03541c5102d00740d81103446001c4049200c4651002090281c0906c0203900940d40c2809009420741030258042d005010064080b0703850541d0300c96605075104002c0c0d8120350380c10300810003a010102d1941241c4a1070440c2441719280955860229245131b00c1210300c06040702c14000c5500440c5441c003a00305103000c0901c2c050041a007445080314002101a04103a101240c44100408044c05281c00d803030325640143c0010302203116507001810300030b002c840c200d00042400d01607250134540320041d501900d40040041c0400644c540e60b1200511541c03002171525100b00c840010303540130001c001d008a0344103500031920b0341040003140e6918442c01540038400c00c80705112803581c00c00002c0315400300b0400070b8007201c10480100113030b50500c61608030040c40e000740000c217105610305400030406150141c40030048942d41e41d0110751626214020341000880d6a03030b6908a02c1015005584c000d400284002411010040025413400c0513510450100310342c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 32130643 1250 32129393 32129429
    0x1a1c0507030c0201020c0c01030b0312040b03070305010614040b1e0d020a090819020d031b06020c1b01050415030209040c030b03061e061002010902090a05150409050705060702060d06 80
    0x1c1801440d0450702d00c1e00080d803c0500c1920385036207400203c40124101036544800d0012668100203405034100c851001603034980d201e00131002507a004484803c082414880005081c1d44920030501451005000700e508041c100217030610303c1d5000312105403070035201801031200c55440704001c10640001c802e0050742d40c01901c101030f20004c0158031400c0c054026000c8107200079108044480140d6048503c21003031070b504d18060301d2164050143c040410301408816040002c190b0040581460b41402c49900748400342e0350383c604c14600410b83e40019000c0c00300f0801002c0c54007071781d50030f00314030706004d0700340440403000c00d045030f210a0700ca0001a0300d42c0c03015203031400c05000d465048041d50004100c2200e0307891000c0b02400001d440b0502400000c01103d060b0351003944034200e540d50090152001c0c0c10a80b104001800003911a0380005075411030b8040c50b0302d0184100d400440c0c3c40005418000e252104008464021110680c2c020f07034100012100d00300b540c030442020b40308000d541901351107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 32131893 1250 32130643 32130647
    0x506040b040318181103010f061b080706050114040b010e040b030708101407020706021207020109120c0503010c05180423040503030901050a020a0c0b06010302040807030b0a0b040212011a1c0507 85
    0x1100e05c60118441c002000140000800c642c2c0340c0301a00c001d4144020820a03075a42e041e110383d02e200010f170641c440418483c0030401c4940049040302d5100f5030a51040c4815020001190000040e003030128402051550850401c1e800c0080e00c0720005040d05d08407661402e5403420001c0c00d60b0003e22043d6110a01d54480d19900c001c140c0182440c03000700b0f00e103402c040002c0c2d5a400d12641042d902c0e14041800360441e8820b842940141403001c1902201c044240707403075044038209000c0c0314883e5080c004103060301072081094407a0b50082010002c0d9800d80d02c414031008201c259050110681c03500d00b62282c0b08800c8001c9805540f09100955581c9040d1808501310380d4040c0400c46c2c00c50040104100456001c0c1c0d1655000b50032060f402043d403948001a0002d1203994031100c07403802025800000c0c400c00144461250034003039000e1001032940030400041303108218030b248414042200501002204030708124061003800b2260b0300d0192220311f82e00104201103550743c280354548081110481e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 32133143 1250 32131893 32131901
    0x90603030c1e0503041e090c0507050c01020d05040e040f02030111190503010308120702010b0a081b0a24030207050709060815010e07031107020d0303060e090a0506040b04031818 78
    0x100c01d02d401c510b001d8482ea500d98607446584078140744c10b901401000d60015000240000a02102c1410001d400c10100040c00c9a004410244c030139008468612030b0550000c1403e0791039240c166a42d034542410000c191440090142c4150740483c8044120401a1000d1060a482d01030200403507485030000400d002c554401e200d803120401c8428001040000c10003020349081ca082c0a83c0080c141c3d503006801c82c0100300079400030754050030311400040d20101c003181008507208214840100c560380c200c140201a1218450130345102c1242640d048840f02542c41010140250320380986041d0051f100c8603e4070300190400b014141e80c4403030410410108000c07010102c01c034149003161940c5006281940d690006000c00305150301c420030120f10078558411140b00e107034010304c10418074000d130034001d0062030706009030526000544082000c80d0000202250030780e912100809065545580700d400441014000320140302c01100003035034100340c00b540c2c04042d00e500c41c0c180130301c01c07009042c0c40c0a803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 32134393 1250 32133143 32133173
    0xc0506070201060b07030c050c150c0f03031014060409050c090a05180106030b060706050a020405030d090305190c17010504060c03020c0615010c050d020c0103110909150a090603030c 80
    0x15a1403d54100501004001501d030300360f4040c1000030040311a41401c03030078402000364456000c00e50460f68001041d0020190007080011411590f002d040c10000698a210130f64915864840b009000c10100082039130030821400007500c01401c2558a0b8183d4090302c0741580c0407a4500400f0811000a0900605840007480102e80d11603686030004070320305119806004403010992103c2d00d14945480340811602c3c91644031000704424640301001a00030741182c054144a03001f001d101c400c000c1d00c21224001900e41000c05040040ba100030003900440820740101d440d80340003800000c5034a519007c00542941320070010880e80340a2800100304c40312000c001d014148140610311121400040030396214035403081c4108140c24040060300c1101725840e000304144101c1e200c0440b40d80e80410680c02e01c0000382c030288203401d04e02298141038040c1d280160b4003c8222000907440d820380c00300701c880400e005407140d1600c64550501c0400c2c3d603150f400641c08503140b03c80300805c12210306000d40700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 32135643 1250 32134393 32134397
    0x9020f010c02060304060e120a0201091101020c090708100506070b0406060608130f021203071a060603070f050706060b0316081005012010060e09060f250207150c050607 74
    0x1a03072900340d0001d41030b80006080544410345c1c400b182c1c03000040030440310f546401d02c400d020380ca0344118440280a42284c200c01c0311030311281030960800d0750001681800d4410020001e443c559582002244d00c80b10003400b030350151064040024882d151724008103021f5010b40a40203246c42d050034480252a4244c0c80f41003080702880400400180600709800c081d507001c8a5012441540e00000d075200508216904203030100260180400174507030243d4083c143c003105500340c0c0d5030b114010003c4070300044904601240d0803c00394909640b00d080103010343c1d445203400092003903c4124202031900101c80d0040740784000c3c1c045418040d0030407611130340325500c0b0484c440c0789818200028500e00c06001240150b50700e0030840912080f0900903419183d94808041010541e01e039852030012406841001c000e00407040851040600115118800c040030407c01506100703280e5100201100890204214064020003050f42584200010400c40007603607011900e06460030803d0a200002c1c0500b41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 32136893 1250 32135643 32135657
    0x90f060c08150a05010c060b04020c010c0f021f1122050f030703050c150408010c020705010f0809060f0c0d0203010e0a0c05070309140406030618050d2d0201020f0a020109020f01 78
    0x40300c0c0e50781c0f4110b405490080c40c04481043c0d107444d0440251179440d22a5034043d0011420007416141580200b21503030310347d650703001980c000510070381e00e40341c51048802241d000b20b01403ca10003800e410a030303004d0600903080341c5030099801600c4a4440c2800000522148860013013003a841e1072412a440300500b1000340c82d00320729542d00c490340e0302801c688590003a40c550869140340b20a110981e8020550400240444000c40c80000e484052601419021400c00740981c3c0d0400c0c810003690344112000d40c01080c6a40725841d140c0a048001000001445410400003080100c540061402800c040180f43d496041c10740c149025100c142d02c0b14410000180311600200b5030000d810000c50b5402e4840c880003002c100041000303003d180e00083c04a80c01d04624811110f03680610039035450055055900e0344c0e1000742c00300c3c0c0d4801400c000070000d80c5103039140b11043c40c0009810044e82d1407800010710b030050340c00e5444025008910790602503551011050191b003000307401140340140910b4055 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 32138143 1250 32136893 32136931
    0x5010807050a0315020910020601060f0305090309010c0213151a0c0d050f04051c02010e04060b09012601030b04030f021603060207031110091712060d0501090f060c08 73
    0x241d02c0e410501c0040d010044c0f58150f40c0e120081355045441c3c81c007000d40304a107854610000650b0701c640030712401d000100748a0307144000764840c0c400c5901520118010f50b2605a14900456061010203800e03a4841d00b040824000b0a03c070344142580e4402c001c90301030f5107516042048003144605140180380c3c250030801d403c600d0b800494007551050583c02c1442e1210140c0c09850300a00507504015000701c8464000c8070800031805540c003109200340e86002980e04103c05200a4a0091081d811020028031220000350700642d4100368074000c034411034100f1f40800f248003a10303950a0380180da25511140901041c50f5100952004001c19400140000c6001e4808c80c000e80101e0310001c0c0c407079030780031030700c1c10426214002500ca040c070210222460b06044020440080401e154201d61384020512407804011014080d80c00001411075520070564404003400303000b14009400711440e55903841c1400001e0001c131100808180144e50009050102d00005000c034030300500130603003131006a5003034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 32139393 1250 32138143 32138149
    0x201062126030420060a050d0b0a0f06030b18040602040503060c13030b090102120708060301060801090203030702060309030c0307061407020a0507150e0405040807030822080a0507021e0102010501080705 89
    0x80e50041d40c413a14403d014404000142151a03110301c6140d848400080d681c00d03101e43c004050080806001c00070400042044204441c40c01d0300d03c01d40c0c0c104c0d00710755401c110a038041d510202c08014003401c4501150980c000911071050125030031240294089030600c2541401c001003540111030960752443c06028461903a0240c0039880014590307020440043c207080002c1d01070b02d030f0014005610148905000401400240084900c0b40c0650b1030080c0c0080e40e00014020086d9064000d07001e14a030420603000d1200d540d000405402c0d05100c1013102d451412001c00081191f10b00800c0001042c224000200d552a04050803280c02c5500503100d00c004510302003403142c2200d556000c82d041441c0420303404d84208a24940c0e140d402071404003000203210040d070050904901c660f0300d01c811551007070b106a03982e0842070380d07905000405981035800658a075004150320940381c101103003003500e00d03030000302c00c81040110f10a0344a01d0305084d0001d035809003d054090040c03240902401c50a01000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 32140643 1250 32139393 32139397
    0xe070503040c05060a1106100510090317030a0e030408010f14090303060f0f0a03030801051314160201090f080d0c0509031515030303040506041e03050403060207030201062126 77
    0xf94034424000001c4454003a806104005403840c503440a8411a203050726140c0d814041500c03c40c0c1c0102e4807a00e000c00c046103d500f845003036a501c0001054800c181c0d0002c480e040c0c00c010020206c0a5455240e9203016100f000504000c1030100000f04540540340c505405446017041250070211041007071128420001c400d030b03507129505032040d00b464011640014083c940c40c00140b500040112000b00926034404119411703a002034444c0d4520609400f080740c100e40d1400c800265010070540442c0c0f120744601c04a201c07400c401d1001240c2a6030340d032181c0682c0e04036064100c501c10400112014080600e01419100d5402414581d0038012a100443c0e01c90f0b114565201c10403002800252005220818601a898020341220f0700c5e0b00e002d00d041a523501c41600d0a48080c528585800191b10804916104c416495a00c1500f018550f039116406900070040032415552602e402144030700381e101c050b0141c8040540d8841056825060400340300034514110132000c0519640080300c2e8041b201 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 32141893 1250 32140643 32140649
    0x30e010305060f0901090b18040201080601050c03040306060b0403050d03060e0a09050a060603080703080f1302040e03090d030e010f02070f03110a080a0f03080f07090612020702030a0c0e070503040c 87
    0xd02040d2641c80400141e41e4030054100701da4081046000814801000c0d405415240d600b9503044034003d030060b5810004940484009000425006c0099070325403040c409805c0d2269020704490400351250b99240c162012a0040380c141e00d0045010024054200804075a20115003000c000b01c030708102d00d070b0030365000c0140b4680a40b41c88158450400c00c080000700719094101030100001c9899246c00c0304658130050301070740060ba0a00c042119600c1c0300f00202c0c01024412924039001c1d01a601b40700c0605140c42c1c152070380340400d10403c82a5216000302c446054401c1d130fa40800000e1800001d010700c40c80608090031580159010b02111240b11448020b030b81d00f100e6112204c1c00f006000076040300c41e80c3c005034403602640030010104154906140300c0184240c40d8100360351741e0481032400d00e08007190300d02c0c00031b0206401000302e17078000c03030305290088003289002d031800390540c0109107414001d0f0421074803413150303440400185c005410145e41001c01031406601d5814152501060303200280 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 32143143 1250 32141893 32141897
    0x3050f010b09030703020402190305010f0f05040506040e0a050706021e030d0902060f07140606010302090d0f060e07060801080706020303061806010504050a0b0c010b030616140c010e0f070501020a030e01 89
    0x140700c0358650783c01c000b02002540d0060055542c0c0d1b4880d0101040b0000d0090b108011074180000800c3c0741c08803c0d802c030140c41a02800b403e40a24010400c00501006020250081d68803118400c0300c0c00c040c02814003050040c00185807681c9400c0000f85017605100d0342d406410203038a21421200008422103428101010000c03e40f02624000100320740b0424607501040d0300005192001c200c402c14542c2e03540d0f02002c054502c150b440200641c01d030b00c10380c2103d41c1d100b003121a0220010b8583c50405000c580140c100080b1076403d04501460200150810000b0540c15401000120000c2111401401046c400765041d03080c600301040b946c0040074000c1e95401c030300800103401648500180e40050000410030159540c0c0c41c4925141c0342c0c82121458015400c05246003c182000200b05014201c052843c00c001d014a2100b10303003112901840c9200503401b040b08190002c030034001c80c111600b0402c05481642d5012800c00d1610310300e58070641c1950005188440442c1e000260030303da8107002c1c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 32144393 1250 32143143 32143147
    0x10605030c01050304140102120a0b0405040b2404050901150f0311130b060f071209050a05060d060306020a020105010501020f15070f03020d11030114090105032e020309061603050f010b 81
    0x107403409901e51455011b0349038a661000c58011240c4031401009070050700301410410440381c21009000039181c0444000e000a08501c02007103802203007800081101c021075010050590840e000501920015101c0703100a039143d1100e0700300208101d2001c4024094440101f00b014a5640e491540c0f405090300c051140d0003850b503080d40c440480d00016252100101107982d141e1519154144c00d401518060714542d03a0101d4815900e401001000b00780c036002403101104c28a008204900781d0b0000600c030ba1007688070754000001911074009000c807040719400200d260360418000910b0326026481c0540709900c104c1503a02400391007060190001030fa4540030328115410b4400b507004c0c4c42506600f15010f4680074011885801200c00395050f1005110910101c5480720200040c6400c00c8c050346034160081d03010b03140c4a200c2c03040c0081c40c0e2a4020f401c00b0810444189510880e00300b03c2e100006031b00040d027080060400101d0340280f10340c203402d0030400c3d410440d484107a0028140941c007051000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 32145643 1250 32144393 32144401
    0x7030305211303030c091703030a050106020d020705060a020f070b1e030c07020405060f060d09150606120e0a021203040306110304030f030b03031318060503030c030703050d0204030f060e0d02010605030c010503 92
    0x1b044c0404005807002d00051900a801180135a07540d038001c9800d414514500000032031103038804180c80c060f03030602d68000c102081c00c03c0100111a030010305100f044d807242051030002c0d071100340300c80401003581a5040303071903410382c1902d020402000d4a2410107902c00700108190820000301380c4110640581e0006030640da02404504485120744006501039000720f1243d0001035030f80c00032648584948604584840d008441000f0759045001c0e034004260034130210041090603521048940000d60119490a0301980201759001c4400c003040700303e42c000080070310600206000c0c4a490b403804079078851a5103803603100206071500c2c2c10b0742c1008050312080301e0700035507408000f61a2102d003002d00b0340c04042d40d90b20405000303600b5060b4190394982040e800054a10700841980c0510402c03001851030444144d030120f07030541c801203100800342da0902000c40410841402c1d0311540d440365034000b895505000705145005100c0300c0c04411681406070601140c2c43c041010602903e0030300b08542c41e521 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 32146893 1250 32145643 32145647
    0x50603010f09080304061413080c1006080708060708060d020d0309030203030d02130503060f270313050f0a050a06050a050c0f010615020d0212030c090307030305211303030c 76
    0x40041ca001003410700542c00207000082d00103602a0f840f55108000e0046101c484841c11503040300d81121491031038000c40c02007007690008050030400441500e88401901c0308140440b54146c000c200c1c1c0c3d03445038000b8810040f0411106812050b036081440c6189000000030b19016440c880007401041c0d03030042c22080600440e41980616401403c0c2d80d02c2d1000c07180c1c128001e400504d2160000700921400103820704000c54450300481190204a00707964a0a00c3c55032203c03111020300080024194042400a00610281c2034260030480c003003108901c0c0204100404c940f00407050301c544421041080607603261102c40f01243c0050810070344810000b0402c0d80d842c046c0486405050180b0342c20120521019030215090301d5062030000300b250440202241e4070b942c00c00440c00036903c2240a999282e140ea0065a03014501090181c42c050014012034245400c07523000b2408120f01141000c0b6980b400f0903420309841070000150441c1c6043c1c28a0131102206500142c02d0565400504100c24 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 32148143 1250 32146893 32146901
    0x22e030b011b061a0406080c1c0506010b03010e01090203090d080a0b04050405010605010206090a03050301050d1104020c160501050a05041406070203060708070f0e010806090a061d100e090303040605060301 90
    0x800c2d01c0082d601c1d2a9240c1c10074001400c400040c1c2c9008004400710b80ba007603e420300c507031015246120001c1c1031281070341084c4422012006004a5058803100b1b140e8001042004010b0181c421420200d4076549840360340120741c4410f810842040f4010310030014144000144507031080603910b41440691285410f000042540781b449a8200303050a04000500605421107404c8980c2030342115010b5035010502a200e074828800100065801c03c010003c5151041c061480c3e03070701504c080c0080494000004c1d0890340105190011504040c0382c9680b440c00d1980124010038082c2002443c181c42e24000804030720550242210742d807041080240307603072038200c00c2e1030500c3c1d0b02030212203c609100401514102c41210400e00040104080c40c190b03510440c1c00130b02030322040e192000c0d244c480000700034a200d8014201222076540e400002120114460f44031500c001e40302100d0050708003859041c500951640250b171110038040c2c20f03c12441c80002c00c1b41d5000780c10400000341138462400090242c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 32149393 1250 32148143 32148167
    0x610050d0c0c0b010501030b060708031909030309050d02030a02070b1b070602100b04020403021021060609030308060306010e010e090f0a03030b090a0e0d0c2d022e030b01 75
    0x441c5054030001c84250031410788009140941078400a50382d84500440039100c43c1ca0340b4030b8222301c040c81100000350b05940915044203800c201400c0746590b8200301d00880350000c0c020380000e038443c003c042c02c0c00014051420000c1492015500d010001030005c1e55411007482035078a00440000c40900c41d17100041521052141c1e1001d8882d404d84d1800d000795601012122801c103203242c00710020091600d40b085a045a178060700420004041000c1030340d903003104503409620000c0741003082c51240400c0c0b0500004d000300c4d1700c810183c3ca04500340107080a000174005c500070f84c09000107008001070403400f2411201400302080d0580e40c1c807200076081072101c145e02140b501c04c07413041c44101030301a000b55000550503525100640c0e1401003060070307140c002018145035080707180890382080c410b0b08041103550180301d0300d02c0061a0050b0801c0d424040f0317480d040c0140000c41c1817500310300e4014891030188400e401005018904411180c00e841e1400d4511400c1c9940c80c2c4038806503074001c015041070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 32150643 1250 32149393 32149417
    0x30803061c051e060702030403020d0602070204091a07030f020306030601150903062309010c0905010f03020c0f0102030103120206040b0f0a0608010c0f020111041a07020a050603010909020f1503061005 88
    0x19501500c0680500400f615002c2100d014003000a01079a2000042e24100e03a00100040003e83c855118580217500190099800c1071b01d42081fa00464a911000141146415801c02261030804401070403550a05a865185801002407040303960f80000d90134159055056070b0f5030061018501aa000300240d800100240d0902d5810040782048840c0c410345c01c01040c0320305080341d0b15071240303600700e9844890800c0428103c2805000d6540714845c00c015031501424014030381f00c5075071009407429074400c40da4801c6a400000500030070449016280b0f4804440c00200300b98289552150710072480109110754040b01100004c20301d60445d002507004005c184005c114640d072240c0c00401200c20304000710003540c24011a001d03000d0740403007120101e4040780100800d4a6404407080007a500c10303002aa402142c007840030905603070b80340043d0700800042800140c491668818841e0010700c03241e01c1c0c0d02c84e00000c840c0741c804d084540e0841303a019800b12407104102a4501086e620b0340940e840c0344031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 32151893 1250 32150643 32150653
    0x605040b09030319030504060507050406050a110115030609050d0809190204231015050412050705092e060503060111014a0a080a11010203070905100801030803061c05 73
    0xd541783c2644c04540280c1c01524148a1a91030300c2c020345061060384200000190100a1308008501c903060003600080b03042c1c004100650744288020000e451508142e405990701e102074800c0120402c0a0f0300b100401d82444040d80c0751005070a03131902e480a00c10751a07010800d1040c401c5690b581c1c02245110b4581f080d1151409100c5039684810720100c0e03000284080e6400c0101d001d502070307940030345c2488042d03032110b10b000e0400003003030045003078104221200e00c581140450a5501c0e001b0407449602c600e0341ca09800241d445410301c0100c0c0b580d4042560003209101801144e03171010442c0e9104400f1708003444447c43d240e0b0103034010440d42020001e030100d0304410f180000c02d0310080441e1000340748001505c9000113a441000f400303504045165039404046041c002520f80c0018021240700d904042c4840010a001d0500b039900c00c03607223040050841c02d0b05000503c0e02c072806040ca107180346131444156041d80e03183e440610014050030b1099070703000c40c1d2021200d0960040d8440c60f03440020386d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 32153143 1250 32151893 32151937
    0x3080403140606090f130809060307031b030207050309040515030706031d0705090f07020a0c080115080115030b0a0e0304080a0507051005030604090c0905040f15060605040b090303 79
    0x101404801c07403501026400703200003250070762501c0000180501c005031074141d803549814494808510340005d08591222083c8401c00382d6a9a01340550700c6884251030116450151026809076034071036651590501d4814420100481d2000003543c040000940380090181c44202881e27601e04090121035606124580001c986142e0540254115085c54503284400e0381c000f50105486004a006481d0041a850000740509002e24200d0b07400c40914010b40307450001944a01481c0700c2035401238001a9140c60703030b822018005007442001820042c0003002004414680300c0c100120612014001d5488840805e2100200c1e5011854504040342126500c035541e101a83d251054000262158002e40100140a0500a41d510b40c4166641c1e5070b00e1442e9503160420000b0080c1090991b8003040310707180456040c6080c811140154056041c002014a061500c3d41480e40e141030420034080c2400020058103420009030740031344a0040b000303521f1309850302c0402c0c594003032012044a6000c0c501c00e08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 32154393 1250 32153143 32153153
    0x90106020709020a050f0703120f02090315070e060304050703050601050909030a0c02033309030306060d090807140f01050108030c0c040e03090613080c030a08090409020301060f08030a020c04061a0f0403080403 92
    0x100c50b044410140620ac420032400e94442240a40035101d900342e00940794407802100c44581469106800f0b0414204c002e0300100891500d810484048a2940c4139003c18010b12400700507a600400007143c03009858035000c00704544a0258200d0a414080c0034052807003159000e102d000c8200f1031412413142d4401c81c802da491000a00c0f5100341425410440201d011803030044126032203050094445403400c50ba000c070b0000107004880d41507a0b8620244a8240080c10840381c02c015441800c000301080325207840c810307013140d5040c4c1c40544603510411124031385000211780c00c0c81d1294210f80002e031a49444500c1c501350301c9400d0340c2c5540b00d0400241d01d081841e4900c17000313086d65034803401c555149901c10300b4569241c1c80303140007602c0b80400380f003003540903c0e140c1c100c0300c4d0300c61020303001050b020350fa000740d14242010742d000b0307420300d80004c105503c61a60411484014200444007880301c149465440b1b07408544400682e00b0b88807000900c0f5000c2d8041500311170007183d201c01d115079920390380d04007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 32155643 1250 32154393 32154407
    0x60a051e011805030606010c11040c03020307030506010f0206190204031203020c0706030b060301090207050a050f01050a0b040b1507080c0703030e010f0305070e060306130e03120105090106020709020a050f0703 92
    0x41a804a10b0400b111014a50315180701c4003510070140003080706494813001500c0b10b0b01500d908070344210003030340e50318001d1300c840c041c3c03000b03002054801503100d01b0b00c03502c00b505840b00100207034100801c10044000c01c030750010702e541c0c108080f07402c64580d041308020840060b21540d0000307000b100030718080c4080640d0560040c02103141000503543c0c03460311800110155145402102d9205000784014002070743c40c2d50040c0f01980c4244101c0da2583d003030307903170302802d048040c0b02c0c49400d039543d002080a482c441b4020018a0001218100700031354110000039107060211040f411010f601040c107008104240c012545034281d260100c4441d256a450001c0c00c2440804090380060002d500441085000b40540f90142d810368440356488001b050a115068000038109503001c2030300c00103400c010045214112801004902440c0e5030308030400c0940103903506a0001d03004039820340040214a82c04941d010944411880140e61010b08280407166070040f0341c030a41c050400065240101900f00d20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 32156893 1250 32155643 32155699
    0x130f0b091e0c030c220b06070b040f02010e0409020105120c04030507030b040501060b1c1e1d01061d0406050402011e0c030201060812040311030304120f0605060405100608060a05 78
    0x1c0313600640d240d4050101002024103807802c48540380d4904000240650442c000015000d070000e81403001549411808440c19201a41c0e031980f0003002405559000b1601c3c10404070544081c0f2545102c0c5d80000c0407403040480350030002e60303488046802c60b4140c0c0e0031200115002000c403024107441e4100504008400c1d0f40454a80d80717001070000f200070708034050b142a001032141c04040340c03c4030342a5002401d003031200070b05420b410316400f9041000f0b5225400600c120b9210038140400384600c40c2d402c4a405404c00841c80c04803194410350200c92204d03080c0d01950207132003c1026240c602c011f0f640c4400000c00c1007503c2a516148a800c5640304508150352806603000b401407a0b5038080041d2601e040300140d50002e4410441403012900315802c0f2810404054112441d2583e602c400075540102c210044586541e08100101801554060550480b078216000c00c101d00300302c40c0c89002d10046120740001e214804e00014400d58030f00d2003000080401810b0040c0b482c8480012100464030a1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 32158143 1250 32156893 32156899
    0x50301020c0607030e1501030f02010909050903090a0909020306070c06060b041203081b0a0507030e0d08190905060315040e01050705030a060602030712030e071a030f130f0b091e0c 79
    0x455620200f03900040120740306e04240092102c503401d54540180c415031291042e8144640701000054030300080c890140b29501e16400b941d100c0b0b00705c1d403c000c005520f46e03004d52070840c14000ca200150390041085600040c072810700402d110040e24040c2e0290400f0390241201000c04500011001507000c1516040c9100c0d070780c0e8403060303620981010b021090351391481200190611a0000a80c0542e00400303049020b81400e80c00c90380c0e00b0780001c000e00003c01c2c00300d64010001c16141407a4281c8000e41001814504008680e0360902c3c010440d1400000d100f10025001c503a03010300582c072640c5c0b1415036031107818024080c40c40c200303001a01070790058402000c000d24203000001e1b00b52012003920041940449142080000350300d04401804030b941c1007503c1d40c000c035240081c0081c9803559a241400d22000030ba500c074585145201c0034002c00811402c100c0e4120404540081c54500103010169030000780082c4c1511403010040c0b61030204641c1c1c440d001074210300c01c01030900016580d03075850411 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 32159393 1250 32158143 32158151
    0x303030c1704051c09032001021203010605030a09060f05130b011203020a080a11060103030f0801090501030228050402040906050306070c020a03030c0305090603071806050a05070b060a050301020c060703 89
    0x1001e28404404102d4015000b82c01048001c11200418138038080360740f9061500c90301c0c0c3d54481d1141c0c0002101442c04507200d0841d01581d600c2541c0600c44034440c4403040e20303114195894160054442e2100401038a030060381d8501e1441088100d5001101003403040c80100240e1404080024130fa44400e01d042d40c0c1c907084040006450407040760035249a540c1079010b403001504558800b00c0c00c0d0400d004102c148003101c1c0d8400309227030042090a00030b500954481c1e8418040c5500a4014401a0401034003d03051030010300150b156010f1507100391240c030384504c0c894801c48000b644038100c503400150784603000140004581e60240c0182068882c2102980d2070f503181c2c07480548145403c807000a4003d101c0e24800c02c0401d00401d208924607009050080c84d00c0306000c0003610030307481180d000c1c0100b071b03065007030000c10014034080030003800c420f04106180c10800c0c603000d01140a02000140400c44a000092072512501a03580041101030000e5445040030000f4507142d04080f00c15100003454 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 32160643 1250 32159393 32159417
    0x7050304171306030504050a020d03171015050c1507030903120c14070c05130c0338040e0304080601080d090f0e060607020a080105180114130f0501060303030c 70
    0xa0408440100224402d407600e09443c040054000e000020003e0303a05000c2c1c240b00e040540c54103101102e20134403e40d51445485051610117186031805081c800880031501300512244c5021001c11112115900700252507803c400c1c00c061510702054901d0301100782d81c00034450490b030144c101087c013900c40e80362103650b5622450329a00301d0344003415440024001408100c070400003000100071081c01041500030107a2590041281c00d01900c1d03003103020701e642e800d0b41c6d802c0e1541480b03800e607280c0d5444401c4050104d130003424a0307a0386103c162843d554003014a014060791711a40b190f80385d02e00030001d881d140c6d582c0f054410340701e000900c260341c0c0700d009000c2c40e00500c1d8451510a4107880c141c0180301c0c525818030782140a0301070018485508000200000d402580e52004800e00030915400080b816181c000c54061070740c4602e851a00c096814560413414450700040d10300d610244244c568400c001481c00c002440a9050784003810652801d640030042c140d240e04001c1c00c980840d280c20303900d02c603 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 32161893 1250 32160643 32160683
    0x10c030203060a0b0a14070305031b0702300703050a030906021c0810030b090f07050103020a12050402010905090c030f010b09090601140f040605180f1f031407050304 73
    0x44111850743c1d000c40f4420301800a048284090075521520f4a07006140200c0c0c2c040e6500d0743c0c0d20502d000e0b80806d9020040200b400d0360780c00545078401a8038102c0f4140714a90b03011030192410076030041610083c06442c8200d8000a210000400c0218030450701007940d681400d0342c580c1e50300300d01680043c1040a0100e8114000980941040c0c4001c0d00345000b0300500c50b040301c41210107001c0322244032001000101144484868900440d11000a84100d561041d282464110303d5030015061600500c5000701064121031810004902daa42c0813842c6c0e40e0300c2c030040b541021941c008542c000700c2c003c103000e100744054000e94400c0040181864840c0d88410040070306008440c03840d54001c18400000e015544590100d104500d044070515042020030090200d59030030541180c0d0014a000c41c60f0022400855400f048500046d00c020707440c9060180490000d6020940389405401c18030800080184264070a10170f120911407011351030300700f1210003003040d40152000d0f204140702030028040300d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 32163143 1250 32161893 32161897
    0xe0307090b09010324021c0506040c050f07021201090b040501051308041e03020a060e0102010b061603080903071a07080a0606020618030d05070c0c091503030309140f0c03010c0302 79
    0x824020110b1141d0b070b1941d540c1a890448074404100c1c100d0b1180c034480e00c1c081d25400600039680a44541b6581529000074030802c0b03035001842c487c8103504045c0107001081d004021203910003400034941743e8071040e0340080380ca607210b044400e07407096103440c491a061207000004a4080c5200340b00911690b1a43c4841e2024003841c804050305080b001c0204018040400c41c50760903e20700280d0800c03a00f6500e800103018141c4640c00320740030485c641d180e0109980e082c4036081505800301d800300d0422405146503224000d046030000c0c1400807650204400780010405e5a810590019180c1224000f83c010070310502d500f40ca58102086100020680ea440580078803c10b40d12181c0c01071507960f444449100c00300201078a1284580802c000040c40d40c142401140d1188145e40c440c2042c0900d0340c94051411461640320400152400c02043c0c12070001800c80d0f0201d9406140110311000c040c10614981c03206038810040034440d842d60340041d0003000c03480700f00a04088000308108021180103070181c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 32164393 1250 32163143 32163161
    0x106020105150d0221060a060e0124020709061d0703050f070e0105040b0409140702031c0f0605041404140307020a03080309030417010204090b01050a081902090307060e030709 77
    0x210603100042000d810001d0f400303e45940002d00781902c0720398181c03941001d4055040440b04070742081003088118100750080388010086140102d41c1c9601d001d410b44040c0100307071340c00040f5200065164544610030272891015141601041100f207603260b8401c0428007508040302c2210100c0d0300001e40190280c03041c6442100251489171440e80c40e2401101d03003080c628a09418401c050101240703a0145d8805403010702100c40c40010040c0629011a201c420020079440440d841001070094541841d00701e04030140400310080307001003841c1b0519024042d10f81240b50064503060051440300b184109450040d4090b1088000003010305061541b280316486002c3d420a8400d00d0800000300440011540000b40c1403e40c0c0c04c041d212a4019541d240d1140e507102160740228080c020f0042a02c07480c51011002d081061030000140c00260030712000a040301d401144410501010f40007903011105404e0f402000d480e500c907140c3d840640305444201c4440e000c2d1068a001245a1100748249484 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 32165643 1250 32164393 32164411
    0xb090703090c090b0108040204090201021e03030604110403020a0b091f0e040b0105031e0402120703050a05070816090f0e031611030303010b071e0605010e06090a0501050105040911070b070504030b0106020105 91
    0x181d503840c8c00303002c06460800001c90451240d0506a11031555072103412403940c08000c05075580c0e00301042040700760341c0101c52004580303404110400c01a42c82c1588042250203810f01d06407203100c0f080008040241032a0007041d0182c6000c1052001c56001c00304802c0c0c208110740c00c00440030400d004507541c2c04120740c07480d0084c44e030040e80d040c1480e240f1a01a40507100030b0403050340400b0101c0c40c0303017030407107a51084a0a44c015114442081001e2003e0009440081c000b02204030b1040c0324941508403500c107460103a0313500e10b6419481046904014280c0194004032540c0746140d80103c1c9011000400036a5000c0744504042803d183c04800c8a0480d03000c049080d04106043d25010342c10040f0050b0a544001e0070700c3c08200180003806183c1c005c2c01d407548a440700c0d2504c0401d006644d003004003080002c904d000b006210681c0c014099505603445002c00107801c124080b0307000018400d0200c06407905150034100300c0402d50041c010010369204445600c510f0f641c1c1d2500743c0c00daa900b40c0d4a600 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 32166893 1250 32165643 32165657
    0x80109051003032111070c1d0f0103060e0c030a0c060e03010207170928090b2d061e1b0a08040612110a0c0201110a03050f0307030b090703090c090b01 66
    0x1a0500d082c8240200300402000300145c2003c01e000c00344055404030900b05e40310600c1000c00c02c80f100130400c0d000d0344d1003001c2ca08098240307089a021001c940050000505c0c003991084071b412580d100700300b103500c8520054100d81004455003400d0a41503003500c41c50001403260341e2600e8032403c043c00bd6444490344400204189846001850002d030014410641c1041d681c10310042d62071595401c0036440b25106030074100581c2030180c881c0075100c0011102d401499a000c40031010018152000d010740040404030340349000d0080040c10b5485540682c42c102c0f4420140704483c041c0c0d5a00a0524002c0f00f24624440b89440880310b856034a0848040e140f80e03001d00040042c1405442541d40c101c00c800c80000b10016031441c0074602e40c0003504442c0004006422110855802c0b0030458085080701000380750000b40c66600422034030030a440b10726003050120110707030890b0080d0401411440000e094420b07a00d4100001001048031240540700381c2088400012480168400ca203040c081c1a91008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 32168143 1250 32166893 32166917
    0x140604200d06020c1f0c02010c0305090606010f030209040e1605030619050a090b010303030c0e0f150d0b030708101a010503060402160c06090311040c0219050f030a08010905100303 79
    0x3000079048100186040e01424808030586114940c1c1d603801c845d10391600152080c0b866030001e08480b01c603012081403624000034425500e82c00580c46034084000d00c0c0072080b0a800780b03822400b038003904d41481c1d00719081c4652104003400205043c0071113403507440821111036a9178200346d51403c081c0d507464100c00c16601184900b68603500101e030301006e40743c0003084c41c10890380c806501c2c1509034002d600003992500d6168030b580d40040444180041140d41c1500c41600d0300020701002c4003501d40f4003180c1e8002820080192141d00301d520b0003100101501c500316902c21003591121542400c03200d8052404002314420034818105c1204140d0680d910750440c1d0b100d0f01404000d5020080602010010300440c1e000249090400d8000d04000d9a41c5081e071440c40c507090000c0c2c0f000f500d01030302c0740c0c0c01c0000c0150106e41c0050903442c1c0c0daa12030000002c800041c10194180084503031080e81e203000010301e0300c0500e6001120a8101c0c0d59140d0204803a9913060b181c1101c10b15035000003000150005620 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 32169393 1250 32168143 32168153
    0xb0f100504060c05071d0901150b031303120203010308040503160608060105030402121c02160302060d0b12010203010e04031106090601060302030a021b0d0201050702190803040c03140604200d 84
    0x41c01d0f10a21810858810315101d0307443c8192504001303201050401004204425401d00b80150380c1d144401200e10f151090600e284581a0b01004150113038801d20014500c00380340c41407038100c3e104001e00070700b1035503540c6038208040740d58814060b0f1802441442e50100d003492a07044d03a0400c603070180c1c0c1e51885079182d00004581c7c03944013810699001101c0800d86081050a10500364442c0d0443c0e0800c0c0400b14a12010b4240f0074004001c40c0c6e81d5803100410009a20360030100c6081e00c00c50300d8006038115203c8001210030a082121078240d40c408000480c0b485101c5c001180528001c2e01d582000440d89106d1a50b03d8104a0f070f01440ea41090004206103401703a00956001005288090304282c0d448105582a448020312041a5808010070a807050b4080c4201500f060381c80c80a401c2c2d1510318042c002d016600d444004003045000000501070160300c3c090708000d0355100c0b100403446511a440c0030340e41c18003902d003590407411090483c44210488006411100340141c1200c4000c01c8503121 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 32170643 1250 32169393 32169407
    0x10627030b0622060501080c0406090902071707060f060e01030827120c0a0902030106140702190e040203060603010216060203040204060e01081c09030201050702060a0210050a0b0f10050406 83
    0x31582c024103000d00101c14905482d60b07240303c82d409002e0000301c040c81e1000040400324042d0a09603030760b60401c018800a503206d6162010b94085042c00359407902e0071314140c4001041c00581c9100d644010a038070301004200d410600000346d284009201054036541011003280c1c0a103c010040e0b0004c21845510403c0f004498111440307540d00008110051408140d11000408080d80c0c0c5821595217402d103460304002600203058000c00441c1158100a0003804000403480071040a06000c5818011591041e40d0440c4521030605a08420ba0f501e0000302c18072007003501c0c22440b078014100050424127051094840003900305440c010f1800c11500c1c1c01c002944094010b13070b0071548400c0041000e521044505000700703004801840742008200c555280000c18850500800c08504010130250b070f8032000b03503090b440e01101ca4030750722119120264a0410745c01c07a020090b42c02c0c102000559003040c2d029404a05094032088000800b40d400c010301e00419441110100d9420301c014000b4034401c940b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 32171893 1250 32170643 32170651
    0xe0108061201051009050a05040320010905010c0903030e010309020a06120e010e0604050d140706051801050702030a120501050a09150308031005040b060702181f030b010627030b 78
    0x98107800c06a01d540799080d0f502c1100c034003a0341d102403c0304200007811842544c1e032016041200700503034101907400401049003100011045241452a0a1803075003e62155211952040081101e907087c4040504a80d090744800c1e00481c035442c03548200365001e030140302d200302e500a09002d95141080030035140c611040c040080740c40e41d2211180d480030b8003481210201011b40b030082c012803a09140891920003900d49090400c00407414900304a43d079101580d950b184d103d50046010358503420f1100c07000b15800410615982000107000c6d0b260740100081a12500035520410000bc002e61260300740c9400b84111134028545041c10002001c25030722041005421141c40350000350f480e182c001c08ca40060318003030024900c02404204a2405100d440b98000041d2a900d08241c11600002c810b000c000b4004010034040301c0000304030941c40046071407558180440c4244064590030403100c041001d008140104180f5645603c40d011500040c0e014541b140342401e2180381542e9903d01e60100c050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 32173143 1250 32171893 32171899
    0xc110303120601080c040e010b220303020c0409060e1f05010b0f1801020a08031510030603020102151807060203130801110708070201031d0102070309170309011b0b01030302031308030a0e010806 85
    0x1b101c0807401c0724003503025034024100c2207a03003500c07281807010644495001142070b00101c425080304200180e00070a2030300e65600c00700c40018004145090040c0075140740c028114031801303407085401c0c04904500d0f1032a210315151600300700303581e01c501c00d20704248142031100d4008070040c0319514000300700030308070480c1c0380040c13041d40e40f40c011a41d04c0444a40040e283c0760140d5144203881e00ca01c3c200400038a01c00001c03860280b000a2071500041d4540ba0200602d8602c40d01e00000a0b10014886005400840b0b0140c2103680042c1e444100030744a80151320400c502104401000800601c140541c00d40107284510040c0740000617aa160910743c131888003281419140c2a2544c1d02450442d0b41d0004c1100010025036a4800d52400400381c0c0c506410981030801f0010b40c203020b980340001651180c00c400c0c204410405140c40c0e00c15803200440c8030091042805000220400d907001c0050100c0030398151804d0390051703c1c3c1c8101c988a000d61011800010300201c130040542d803080c111550042005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 32174393 1250 32173143 32173147
    0x21e0a05060c0a02010c0503060d081b0601080c0901050a0e0624070606051212090d06180812090706020303070f0e04060305010209010e0105040f0527070c110303120601080c 76
    0x99440604040c022680c010b00e0700004a245455030b90280111000410a8030740a0320310300d04640050b640008400018002020124110741c403054413030042c8071031400e143c048036415039556001d41e5603400002c0d0258043c3c07480c2800082c85040c19a04001550004030084580e592001c0522410561441c4100345213001d580140905030041070080176903500650b0003255041c01c10307042c0103a41101d801d280c080742c0c4c046440c000c4402582800e40341203250444566102c00980c0c100200134241c140200c0000440c0600d40508010009004000b241d150355640c10b0a40d40e0f840c1308903100c00203441140050b0b00100001407480e803140b144020f29000030300701200d400006001040c100d60f4140c004171860b03035000030282015070300106519003120003460520b1a29080c4050342c44650f4040c8100c40c0a0b00e141e003103828051003104107291380240300302c01001c1c80d4601001c0c024070031280d1400c20f07110040c1242e8002602e05000c411101c241c48600c05131246926201d00440348442c0082084d480b9003c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 32175643 1250 32174393 32174413
    0x6030507050d09031e0f08040210020f150f0708010602060606070f12020d030b03010c051206030717010203040309121e0804090603032c01081b09120d020d02010c021e 73
    0x800c0c0320380031205019645100d915072181c03d6145050358545d442c0350620803519050103003c1d078481c0400e54001d40c19201d00c030124150401c160701c1c1054209814443d402000001c40c1076621007a8a00d211b0752400b2081034281e281c4800030340750314500b07009000060300000b00040071414400010441d80d4850041c400b0304103000e80300d00070a0007480c1c0b40980140c0144008003601c0da41805594200b1034114000c000351801031802520310310441c1d03100c044100800000800a560600c400310083c01c40c20124400d4001401115000f98800c030b804501184400c1008510149c1c2c10322070110707561740320b900a100d41000e14203641540c140140c00f1039260604210100707411540d80550401184079807540070420803555482c0c60301c0e0181000b08444000c80c07855401041c0e0344a40d00c1e5400030b1b881c3ca40340701142c8041b00f01144521411a40340c1e08810300c0510b800a0040001c1d074501444038a0b0700351882600c000b44200d00341c0300903540010045e4441d0700c1100c1102e11014400a04101c260110b0300d41e610 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 32176893 1250 32175643 32175667
    0x40b0c0f0d020a02010b031c020706030e190c0f0e010b070605040c0308220b07020d0803070302041a0406030c0e0f01050d0902040608010c020f01050903030f04022206091808040603050705 82
    0x3c0032819240050b5118150499641002c01c26010503160f01c00140c440711b111000001d54551281c484e41c0105034807196503100b1800c0906c50700c200902034039058100b18140c2c0c1400c42204025200b0b000281d05c8881000485a658420142c140d03050220714074600012a15141d014010182090f5001c0b2000500040081c170610000d03d401c61030224440d01407000000947c031854156030116032404400c2040b80c0040e941d44500a070410b0348414202d8032900c07240000c500a01407a00314481003840c2c640a00b045140610161013181c600e80d809000c0114566012101502540304841c1c118205080f82c4d401c56000320023800a140d401d400005698035507400180a45070548d209189070b035501d000c1407400a6040c00182a080180402400b507820010364040e6284070040480900b654002d011400315502e1282244061516060b0010408911072441c4020500d41c8103a0390250320b0919004803081480d03182e8185190000020b5040500e0700b0070950203800d004202208008080044002c540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 32178143 1250 32176893 32176897
    0x131103060406050108071223120304081305010518010f0e0406030807140d08040209040305070f0b0a051006120b040209031e0c0103050412110f0f0303041505040b0c0f0d02 75
    0x20300806000c121545170545150500301141c01241403000c0f804140804240c2031062580d4440c00506e6100407000321020702428804003c43c1600c00703c0c8004180400d0000c0040580756501c40c0320501c007a5240c0d21030054070541f05409409c14801a070142000066014040c40203175465076041640c03090207030310f000030100e601980007101c98007804074821044c400ca82c5031495041c031984009009811450070081c002900041c002032040f0781c80170001c1c007010b120b00b040d2041103a0206605120000b149071504000c4000c817490300c0301038a00000501e00032500c599281c1100d4154843c0f081c4035a484150602405140d045190800d07003c011f50a141c1d101008041e42c029451610403491400c4a20110f00308181d00c404c0904050408013408007056000750030304000c002d02e0805144e1031400365044e40c10300c0e4484106050501691502a002c624080011440b90740b168016114403202060700c0011510162000fa25038408400040e141c00741600080c03241d08405008182000003600307190042c1d13 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 32179393 1250 32178143 32178151
    0x10204030507090b06130b0c0a0f080304060b0f01050d050604060b0f0406030b0f1e0409080a020d020f071409040302010204030611090415080c0105070809030d090312020d020613110306 81
    0x298020442007080c410385104500307804c0802c40d01d039840d000d010721042480d1030403400b41401401d4000b0f50351400c298200000c2203625840000c00c10502c0039410407144503001200c054400380c1c10300e0800c9105140140c20700b600207905031100303414400d0707503e2404004e100c010091604555140d0b03002c10b00760401000740c080350082c0605503a5aa09100e401025650400d034041d0080c5807881c0481000d98401075003158800082c01c078661b4003404080010b028003c808405081000001134003c4480d50218031041c540845808a860142c0320740c44040d6038514620660b407501e28100c03610302c05071402d1185035820600920002d07043c15100e403501d0301180d4103400035000903d4001100304c8a07007898000ca85824242d0f1030385007801460b01400b29215065140307094100000014080700300b0800c0420f940b2129006000c50381800c02540c000307080c83c0200d010075210309401001d8480c207144001a270b030220000c6079001d404242c841002c0c120380c1c1c41454200700c44d090000c11035040307943c030104030321803007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 32180643 1250 32179393 32179403
    0x20d0b0108031c05010602070b03040618050c040b0d02060403031b06020a09050109120b0610030f0e010603020301180c05010c03090b03090127020a0b1b0307030309030e040c1710050301020403 84
    0x5a0074000390f070012505501d4901000181c10710004002483c7c000c661030b02100e9204500590380e0f5102c1c5807134401040c1e5020751000001000d00d03402c0603c040081c00e02a0b090065804001c40400d501c2006510743d144900207510400411090000a100b0081e41c2000c50300441603244e001d250b0380d07510040e80c100e04d001030002002c4400412556900c1440000140720f204044c200303001303854030390710060f4100030002401403040ca206801c80c1071003540b181c55043c615800c02c110020300745129074041c2c4550f2000383d00c01e40c00c00b1300c546041003a840b41020765a40c4044c28645d203e16020055800c4080c850f0290213101034040c0000301c5070300c0b200046121b4000d01000182d00240c0c1440080780405401c070a20424000001510050303c5415401c0255a41c00e0165502c07080d1515030110031400d400b020841c54040456264201a01a0440840d1610903100e0244044000003030000700c1d441403400c000000d00b03a40c0040444c0c84407a00003908404206802e10009483d040802c0c01c2e03901c00c1d130040361 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 32181893 1250 32180643 32180647
    0x9051c05070506010b03070507060c0e030706080a0c050f120703091e0b16050a0e060c01090f060509150103030305060d0b01080703030215070e011202040305070303050904150b0a0309020d0b010803 86
    0x1c100b01051141c40d0140c50089145415402c0c01c0c0b0004005000b02003004001a585144140340540115211400700800404840a207a156600202440c400b659071244117828001c3da01c0302c2900800a40d003050b44070301c4d42c46007400c2c42d040b101d9418020140c0380c0c2d401c0c10380d00c4a0020208020600c038001d611055011a04042c0752860310a04540c8020f04200f44284030000d00c051640c2c0c850101d550762985450005400d040803800101a03124148031240703030b0361800c410101048060490703500c2407400742c002008276075102c0c0541034480095041c0d040848410b0001400003a00039400700341c0000d8040c08200f03100f00240d032005020b88082c1c1000381c0c658803115003041059070402400c00780100e03107089410395082601e0040c0003800641e015a05202c41d507580b10000d9039030b0754103840c011500303c0104c03480c01d6620300b000307040c1e540300114590149080410b6075901c054090f408100726910048604d140c04990b843c218010120041c00301d03440030308116040b011440c1c00b84820b000e003608401841d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 32183143 1250 32181893 32181907
    0xf030605060f09150d03090b0a03150f080606040504031704050309030c1c080715020409020910030b01200102130b0a02060612070303031a03030a030e010614090103020409051c05 78
    0x4802d80d045184901c50301842c8100182a812045541c8003104150307a10080e1000c90725080c3d5a540880e000403031044001315031900501d9040e040801040e4241d100c0d04496a240c0b0b680050140160052007820340c04000410080e0415521065006000f840c007810390754036442112220000580b41686e00c0d034804241d001c030900d41131000400c3c203842121101210f0301e4040c9481034070040d0100260261a021036028184104120001007440c81a01c1c210350b19626109400025040310306030601a610690341d07030000c00e00900c00c8016800d0305031600c4000082d26291407128050240350001b195400f881104c2c80d4041d4604010050162484099100c0308040300013850640d006024070320682108011640c4000e011682d5803c1d01d80520300800c90f600e003d401381048500f0455165003501c000260341b1050360f031541c801c2e0342070100034009000320390f60341b00c1180c9540248810b00f43d1111381000100018070b032030352040619500c100c068031503c12151041500800c041030148010690014680c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 32184393 1250 32183143 32183149
    0x80a03180c0e01062111070210020a051c02031623010203040b0a0207170a0504030c060e12010c0210020c0703050102070b0f070503041707030c0c0612110c03220f03060506 75
    0x42d9000d001180380450325001e0f104090000d08445504690420f9900c1c00300c80e1400a03090200e410742d680150401c1c20117001000c00075a2401040d80940c0e0500600b4621644a041c50300c1c0c030341c5c403502d80d5030040d8140141030b0302460410103420300c21160031000c80340207141491100907a0030b45035540e000040e202d103090300703207030880900c01000000c18610400124001a444607404da0303490461000441d11f9850302c3d4001d98440c85180c0014100c9940b0090000c0c115501c074a0507003c404094038031112034515421094240c540b1203071454056000341d0350410f4031000c035901401c000300c5680300300c1c1c1d1095500d0b00d609089a1200c00c0550706800300200300704405503110f0700240c02140c03910b00b5528600d840e44462031014007064285520f1400001c0d0709e003e05214203008020250066010194030f50703250406041b0200c0d655010061504201005400030301c41425610080c0b0013802651508030707800348030008448040d01e40c1c180c5440c1c20b03101003540d8810200130b80195101c4d1000052609242c010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 32185643 1250 32184393 32184419
    0x5060c12090106050d03050f04050429040b010801140a030c060c021503100308030a0f0c0e100e06070305070c0e0903090405090d090302040e010f0207050706030e0703030c080a03180c 80
    0x71244030303a810480e0411480d2038101c0c680e42c01c19010301d0000e446880d07242011409201e503900031540a401c00c81000c81450b90500045c03058001c4500142403040194148410b45d980e03c0d220b580400c60040040200300c03000e82c200c54002c04002e0001462070b48980d0b079400d190819030014400904800c0e559411800d215580700c09960b0520700305810741c940005c00004a0946000081c6808400f001060034005580c00690485050390010702c103492103c5002024000c1001c00c0a00c60119212030320380f0750b4003c510038440d896014181e07500c0e0030303621b880c00e0781c003070b484044100c0e524141e81c20002036039001d5500d803500a034007040c0030b107076580c58440c00c1005940f00602850060b8002010030001260022558005c1300d42c190303404a008184604050b00600d41e0582c12510300e03000140c0c3e40d04019002c160720b000e944080d1004c002c200c0c3e06000f2595140c4aa000041c046620900020040f500b148080c0c00c041c4d002e407a01007040c451400c240c1e0119040b07000100d6041050700e20500174240281c803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 32186893 1250 32185643 32185651
    0x10c061d060f010e150d080c06071404030206030105060a1e0905180609060d06110703080603070b0304020117040507050d060c03050109021603050f0409020f0403030e041104050f0d05060c12 83
    0x90b03007041e194101050441c900300c000e07100c107030074a450300d80b42e4405407125103108040c55040f44103181c681e01c104940d10f40361041204c4c1500007034461540320700241080b80588040c0d035005003541c0d0840c0c0c01c041c1401032592050521405009521030b0810300a5403105600101c0030b903d995070b155541c0f81000b0300148a503010700d4566204e80c48420000b86444100b4440e600c01c500300c840d80340829003400d2150041454808040fa1548000368900c1815002482103025030010b50450789140d64900005440e8001900c4c000e0000c2d00300320408040704c806c403a405400078050f10964800640d00c40c00200800030301042114a60b864000b41025140c00d0b100300c50040002e00c000354076007003954654180c1d580102c03100406002c000304505a048160005590243c10390660440d91402c0c10340c0341c010250000e2100324001401a1100382d058100742c081c00070300c4112a0f4409040c14140740030403200408218906800140022407000403802c04c0003c01e020344402d41f03042e5038413110381d80c030710300c00c104024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 32188143 1250 32186893 32186911
    0x22703070302090705090a0906170c03070303020706110f010c11060703050c041707091a1e01090504020901030f0f0c020f0f100c05040305070612060603140411010c061d06 75
    0xc0c10800143c0c84290003203511081910f0025030f00c1806400103000b121064100042507485c0040204820301c50f10000190b021000f001c4034140b10008080550712140e42c000180140c100010801c0940d00030f07400ca0410301200d900313685a1900030071180c0c0c2143c114031504030000f00f4a13201c03880400c1087c40380b41d41000c0c05290034445031038130081851641c41039114110601440c900b81085070441400050041d215142c0c0921918030340114841d50440103d5074944504180388008014031039686d01409410010b84541400340e01c0c0204010094209128840c1455180c40d13440c1c80c10702051040f40300030f02000703800054064030010001d240005001c0b0f0204681c0c40708224980e588070016040c070111401200102c0d104003c21400c6503180a1584002c18030302ca040c10119070a41c1000a1300385615540108010b071943c1d4010880949002005003810903518802050100d45255035030380d552001030400c02c0c114180c1f41d075030608035202c460750000a91030440295414900a100f081e400c6642c80b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 32189393 1250 32188143 32188153
    0xa050103060f0b0a060e030c040e1c05160305160b04140c010905030303130501060302030313060e0607080901030b01030b150304060509120a1d090903030901060605040f0e041104022703 81
    0x79201044d8181d090b03009650612403841c1c04e60741165400c02c400000f0b0b0300054800d121130010091a10742e144011201e6815900d91a04e107004400c3c0b240f419501c0e0350f40d120440103009001d81e20240d5080e40013030410481002c88141180104000001d076500951044c030400d0307410340c0050740c4282850306a80d250fa041041c424420130080e54008280d0350080100551500200c031149003040c01006180d1000350980004070ba209a000c0514050204540e0981c84507065600000100042c910998030000c004000500ca0142d40354441c0e0310030301502106050000315908100c0004480f5491903e2186076100008200802c02c10705004194200e8500d000500025030301105460311405240400d40c20088131203000185c41110b007040c0c800000d005415100380d0309081c40d00903100d6004a0301c075105582071820000f0380611036011035048072140e03410407e01c6130500314038601304000584280c0d034140018960303a903e9a01c83c80100080c0d000d852105007a0a034000c4480c0780c1500200c042c0c0e20a03040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 32190643 1250 32189393 32189411
    0x806060a0f0627050d050d0f03090f0807050f07090903090909030828140105040b0919020a020304081203090706030506091308070605012903100603020705150a050103060f 75
    0xc2105a02d0512890b101d070b00b03080b9403d003000b071204070456010950012808207060288100417a50301c920224030354945110319402907080e8191303005d0b00f0004040c409000c0500d80400d20040240080503c03c0d0143c600506403030a1440c41c11160350049001c40d41e4465410003090b80026000004011070482480405c0071307524042c222000c0100034140700d003460941e40b40c01c0500e145180d550400060002c0000400041c0445011182402140d025501d040e0103407a052030402c1149209001104444450400c3c1e1907480300603420500441c402d6200904c8007080c0f180052001e01c91034400010340545900c2c2002032a46001c0a41e8001c6052500d8a41440559101c2c1c441040d817115072070340c8a1900e8011450300954a02c1070715009460740b460030380046000c100c4070142001c1114081030302a48020400a203801038481030b00c25182c0c040c8810030800030316009802421600303004400391810034451203001080000201c44da00f07502981c900c01402080440e200341d0f0003c0d03440950401072419 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 32191893 1250 32190643 32190647
    0x40603031107080f0d0507050a06090605040b0604090f022107030b09011103041203020906090d0c03050c030c090103020d05031b0601091d0a02010e130c1706100207060e0d0803010806060a0f06 84
    0x44410b20080084c0060700747c0070304c4020800200c054ac0d1180040019241c9420010001c01c0182d808445c0b00c03400e20003242076480c0601410940e00d8009528072540ea03080d500b000312403440b100500700a2000c403d01001e081200703100b00d0b0015400350444020b145090802a800c507900c1d20300100640a040c01444046020b0813401c1190000c1410010ba40e00c042900140e081d010b0030010940c0010001050410000d030010300408030303441101260307880080c1c4000c2603120024420b0240d00139500b41d004002519120070364104c8280036006491411445c240c1004a14450902070001c1d0340c440e4004101e5200d0070b01c107a008100d004014004e5001030691215200c011021010b410880040d6416119649100185049500308a0100001c40f05034202800181c9603501001c4006413080c00141c003414504800c0f03a401489901800489040660586003c1c500144540d0020210080c40c800603080200560281c05e1030401001585800002c201c03075049650003030a15487d90001c100003040d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 32193143 1250 32191893 32191903
    0xf03070b07030f0e0a0605070b0a0204061d060903011d0d0207180c110f0d0e0a080303130602070203060f0108060a110313020f09150109090b03030d0e0309040603031107080f 76
    0x1603240c0f400900029844204031090104035000380c0e80101c201c0800603245400c01c0042043c140b1501400e10f141c4d49401c4620124003480c82154003040d4101801540d05d10540d40e07940940c44010300c000d00700751090003c43c7c03c407aa116900c0c4000d101041080f4100d80040284c0d00ca0f10b03072148011301485080010901c4168801200e11000c1504d43c41440001d070b014a4004c90110b18440c21101584038095640340c0d80e11822800740081403c0790354481150500c003a0f0b110a4031000340003107107540ca9150090126045018090790903035801d00005c3d00581e070034000c0b0b9024480d000b42e47d00d52035060640482c01e00c0400780c200107109241c101c441c02c807001d07508140c0c0e0303200c02c04466410031aa05400840c01022030300850b2a8044410020402c0c503482d01d0303003044010a8280d0302e11304c0e0640c46548410440c0c7c000442540d042c0c0c01442510307550702aa401c1042e05440d41c070196402d00e0002000b10b020340c0c90903041140424070001500003a400d04004d076000a201c80e600500c901c08868600c540c9403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 32194250 1107 32193143 32193157
    0xa0e0132220605010c0c0303260c03010609150807111002030103051c051602060906040b0a020105071128050102120108030703120603020f0906040b0409110f03070b 72
    0x110f5204003e4990151b034072070348002c10f890554409960b501d986811034004001505582c011188142440798010036042e203443e500c030350400802030440e00050f0412000806c480f4070452450b540f000205410203e01d05040760141004880c0904000031000701100f0140000000070400500040c0d2040c040043e14400c40d01c0c80d9652001c84003842081c102c150009a107242da0b10151409000614888000404036807800b5030b03880298485400003100200035075560b4040018054200e110040f41d1010320002d4000c50744842c05508040c9020440402240000c2041d0000c1160960454141300c2c2d541260018030360395071000a60300d50200e801200050f1f0036440c2405d9441543c000c040603268000c0c50380c51303200700b074078288079800400900850303200f915804481b4164070341d4480c0300c00150040c04148003c4154805220a502c680341c0c4d0300d0301039032222504004008000c02610a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 32014393 32194250 := by
  have h0 := BRFrame.cov_init 32014393
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32014393 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 32014393 ≤ n) (h2 : n < 32194250) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
