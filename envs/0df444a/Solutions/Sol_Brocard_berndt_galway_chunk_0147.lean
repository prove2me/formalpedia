-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0147
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:06:27.347568+00:00
-- url     : https://prove2.me/submissions/1a21dac6-681b-46c7-9a59-790f6de203ad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 26258998 ≤ n < 26438854 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 26260248 1250 26258998 26259019
    0x6040b010c11041107120c0201020601080111030f060f04050a05060a090608030406110f1603060e010203090a11040e1b0906011103070204020a0e1306060305070e030304120f1a010f05 80
    0x141c1c00c16500e80342c2c0324141c60006130080a80e650712458000c3d03400041c0080784103841780428991020202049500c05e808480050740c031840a242aa11070745034064545a003400002c80f4003903200519500140041c1c24001c00d841c55402290903110102c5005a41c65141c4007440707190704107410310320010010b1180c20800c003803c28080c0c648074400da12940003013140c0318500c1e10180d2405d00808401c0200002200e80b400700c0241b90020703010003840252031851521040640800041c000c0741d218240140180142508a43e603022148201c6441980c000d56a040040081c07075080101148140c412a000c419181c1d9410420042d140020302c0141041511071109034009400016030700e03850b81c1201e0160725a450b0074021a030340e034030441d4004d6000580900b802c08500e0203900110079210b02c0d81d800c3c0a00e5a400a0645410940c10021501940704200c10001c004400340c5035088288207001b008020480c0d9200c1c3c0041c0000700c3e40b07a8a01d40b0203c00100303c3c1600c0c641d20f81000709002c0d14011042d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 26261498 1250 26260248 26260253
    0x3091c050705060f06011b2a1701060501030b041404241517070e040b1b0703051c05010f1a120106020d0906020a0812060f060f07050106080303040819120f0506040b010c 74
    0x1d044194840e40702c4410230442e07090080c17003100d010400341c0b04072010000000710014185029001d1885014003181c45e0400200c250305203400f4040f400320340d0182c814070075107460391200803d5001e115040705543c50300e0340e40c090301a9a0300600a2003003c0300101c0c0c24484c101224091460052a05c111050f44130a10030051440300100c001e0f030058000c4207040d4030343c0d100c0c0c0c82d000324055643d000104d01880020044101900b240103492026898540e000020940b49480801ca58080c0100030620101900400207407206400011550000b64001c0f03003002e400b50810074540c0390a8100c000542c1000e0611418242d00071649070060203070340f00a004450003926110304a02c01c3c0c20603ca0407030b1103000019501e4440e00d203891500c54000c0d12240d61082c081d07100000640240c00115150f5090000002d02c814000080d030b07000304c1d00082d54070f1410000c1010b02e1800f801c0c60411030240074440c3d84004d5800900d1180c20300c41c2c1c00b070141c082107500d0410100400c89507100c910350305005019454002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 26262748 1250 26261498 26261513
    0xa03021005010e130503040b0409060311030c0a05060a0c05010507080618010506040501050a0e0904030305150102030415030203060111070b0406030f150506090f0607050109120503091c050705060f06011b 89
    0x10400e0713100e521420b00b00c0203428418110321450b000000300c0b650020340010840016403003002107900480b000c2681130108420140c9501d01c5202195201451034024411440c00400401c13540f4440c0c2840c1c1d601d4841035441a094071003c0b00c0b0300b00030503809000c100c03960410a409041c03510080151001641c1800000348242c0900d0147d40d04125011a40800407800340101030400c01e001081c4100342c2c50149001006840c4c201d955001248880c40341820650000059038240c03044110a105006c00d141b070110003d400003800503042000807007050700440020300210029008044860382d403582861405401d688040700789014062501c4038445e003407404030082c0425a1421a64155949282c0c400102d00000c5041c01c15400326000800c0010080154480040c0510030004516440241a400d4915020440360071400d41c100203107581c501d40c41c40f1403e8424003c3e0382011030402d00107440d00352501c8012540401410058401d000c45981c0054400c940c0000008400c15903615690b907216 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 26263998 1250 26262748 26262751
    0x30c03080708120a0608160506030c0309010b06030103080a020d09050f040507050d0608010222120609030302120c0714030412032012030a06140906060d110a020a03021005010e 77
    0x200112400304040d81040310320750880b803c540703104450024034103210405000418141c89096594400c03c0c41e0008010b107880080c50032200c004000303d065aa8411a040d0070780d000030312841c025569200c15858035521400550302850040128075220042c0c1c0c08007030700e45031154040300240a4002e400304031903541c44258450b9a42c06450114003626040410b0b0342d13a004511a40d29200e003442c0c3e020034492815400791048419052100d0f20401c440035402c42201d600f4051020900204120039012410f2034100c011440e05c28036005140806e4480d0b1000101001d403008500c40c1c070006038980502c451307804c0c14040b10b1a0340020318a4030b840c4c074040080c100c494400080c02d000e014003200e4080d003000500b1041803c00c20054400070011601c1420156000326401c1804510300f80b40440c0740340f03000700351900b0110094030a2065480d104208002600203c1c40c0c0e20342a52580f50100401001602034803500c0b031103070000e0a2080e05403601a080988190241c2000d07854080100083c026042c0c0302d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 26265248 1250 26263998 26264003
    0x3070c060c050a05010c0f1e0504170703021305010e06100f0e040e03030109050907080604020307140d0c030809030114040209010303030c020304030f0809040c0c050c010e0d0c12020108070801030c03 87
    0x8440008546081030030103e1011000c0c049520b000d0a001c0c00e41d40111307a4100c130000c642c0c0c0d4900382c5407075a92085c1043d50034140030070000b80140418000e016060807020b12002104003124116503480d0700048120071410341400d0016110707001000348003041c4800780c2d0000340c100c559110054a01d00020400441c0701e562008019044000700c1c07807074840780d00ca00602e40005054a66940e16880740f01e000c2d0800750780c00849881802e100055040c004640d02e401a0360041c06001c01610b001c0090841240d5001010307805540d58801c4000102d0f03020b02000118850360444da1104080c1007010b0850301081c001044207510001004010f0b0f6030600c4450540e40e26080c001500d0203001d404a02d0360003140c20051144041c40044000d01c00381c01d0140000400c201c0cbd040c894120f03c280304880c1c0d5602e54000800d41c7c0c0c405c4612000070760069207184900071018001d00d0901e50261129403500c00a41c1c0280e00030b0102c42e881d40195607201c610030350b1214440c24612102d51642d03440f0f41c451203491201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 26266498 1250 26265248 26265257
    0x12130f060507050c1903020406080a0b07080903030a02030414060414070519030206030901060312030605031209101d04020f030109050705040806010e0406022701021005010b04050f0402091009090e03070c06 90
    0x12102c42c51802c40c16a17018640103442000840c4c6c80f001c2441e503480707002c0019141c6440b40710029203910701c5450130500c1016080041c3d81141c0300c01ca4100060341003c0e204451040000c464940c0010042002d01d204e0341c007410341000192400281c203410052650000e900469200080880e0f100007050122b080765410b448503507582e070710700a0090040205401c000c20040c0c0300031052041550540007031040e510100c0c00da8401c403880d64100d001038419000070b82c0c0c0100e0030000c8060418094428a01c110265440301780d5104407200014040ba4010400148020307000b000501c9580c14910980358004228284945094140315080b40d540d081481860904111400024100601e0f50103887c00d0200b150050400022403c00041444100c0001107006203d000340c04040500207000d802d04881d008001245041c2c03d140c1400f28401d0700450103030f08035808000f07000042e02e4096103c0880451a07075881e0740d0701e0070041d0900684414100000301e42c0d005000c6103021070040582c180485049040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 26267748 1250 26266498 26266519
    0x1060305241f050c0c060301030f020d06140702010204090b030106060512040305071a010503060604050f0a0b0120010203010f090606120b010c061d0115080714010212130f060507050c 80
    0x20b190945103010b8145002158010850119001800740894220443c1581c0000455406002e0140001d11000e00103180c0394842201608108030b540101d9802400040783c20b458920f0034500062084e078900c80141e43c00030701004480c04074443d605614004400910820303290250080c00d80c01080140d4003182c0e0003101040400d0b0280c000c80b4011640a96500b090001d580c029041030f6000344100c034002d00900300014910701c0c0a100712440380b03030b02448000007a01d40252440c0244034924907281802469103402d80308030f082d004807010040c110710003d40c0d00e604209102c5c0c01e000165120041c103031705043c030502c1419000282c200101b40b02c00300002d0304421410040318100d090740d5020b8400c0303203001e21038183c0124601c03106000007007130f000074030280310804022100008184520f02184c1c010703000078030070042c1c52001480381c0c0005104032100c1c401c60b102d41c83d4140c0c5c0040a035030398040072440d0800450041440301390040c081c500b855418141c00d9211a41c0740c4891000891260040e4072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 26268998 1250 26267748 26267821
    0x20307021009050304030b010b0325110f030406030b100215060a050607110907050408030409020c01290a060c05031b0708010c0503060f040203010609090c03090b070e0901060305 78
    0x40202902007000e201440310003200e081a036103d91081c0000d0f18240003400c0082200c0c0b0040341241c2c000d8144001808941950324001c04582042c0d200c020300b0031004510088216200b08245030a03510711303501540e81c0c1c82c03400c000031f41140e200318440c40c0101e1181c5984a8030702c1e000325020600c0400b005da00c40d0789980b210000384025071980c0045a021001081ca9020b0011585004c4100c640c1581c1440c4186c66200d0156007034040e503c1250303030b20740c4108402c2c090280c50790050034210744d00d40c001144140e150820080d181c2910258181c48102850182c0004c3c60700e001075100070b018600300708114607082d440c2c0a40764498180880100525420440351000013040b4000082c54400002c0004000303221004240e64020742303105110760080507a00f074030391a061003228126416600d03081000b0f854802194080d0409218010038503584071002804a00c80361000780c0300c0c1d80107690320440d9071a65810489034082c180c1000c8101440c200800a410352040c81d00c3c0220f00c07502094448840c400d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 26270248 1250 26268998 26269003
    0xf0302070510050304031710050d02210d030b040b0d060e0c0306190605040b0105030609100b0a0c020102010e010608071206110408060121020918010b0405010e0601170f010902030702 80
    0x541c00329810418250080001903803250155002c0c500c61f0b600c0d4150088200c00d02c40c502041a00c81040d00d00c05842c04114901d004070051440074409002c0518070030507400c1040c4000d080c00c00d040029000301c44081c4001d40e1501c64641e0301d00c0c044508004106450300032a01c0114041700040c0096560794200582e400100659540030800404030f4140c6c0c0340801261145080c0b00b1003004001e400c000001c82d0360314090040050399401a5503481c2140d403400100043c000000c3d002d203c0c400032111000c90b0810042000303001180080e140d14503c07482602c0028212400c624040b50141d01d1301409101c0c1c02e0000c1460001c4a070480581c03001c1c10854200900140410448420390b0790b8005000998a400030550310704840c0d4035841c116000100d900c41d10001604080c00a40c0700724200005400c5801508403070342245601d20000035200080c4c0c01041c100c44003a080046452003034402c015080d030303000007070803076400d031030b60055229091400c4024040d001c103024803d55140c001c0300043c0c45a108 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 26271498 1250 26270248 26270263
    0x3060c02010e06040302030d110c031921020307090608100b030c09060301090b1903050303070507060204051002071403071406070203030702150306040c0305070c060e010209180f060108070c0f0302 86
    0x2c0314103a5040742002c1c078001e507032548030b1f007400c0b040a802c180d1900e106502d500155000005081c000e5031416000c0000c40f00c0111312400740720705200c10b084d910a0f45102d802d00010421003041001a92810070580180c00801503900000c01c0000d03010800148072030b02414041100c083e490307181d89035200d0074014202030241038101c2e0b402400c0480005006400c580003120706020958869107030301103503006003241014502001d040d070b43c400c1002c1071030184650000c6c54107501400d0018180390b180e80004061281e5450389500591120300c081c81a125842500c00070f07a1001c40041c88442e150041682c11090b4003042240f24032408911002951400e200710780340954001c2c45c451003100d032400d501d02d1540003560110300951822821680ea14007910070039000710b09076210912071203135542d03a06000d010342c80d0a4400c0b5540a1140c1280c40c1c40300d0600c00e5103030488a03200d2100e4a4100145580e0300c1c802400303241040003140c240401725410540183e4441d03048461421000402d00303042e4a8401ea = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 26272748 1250 26271498 26271521
    0x10f021906060306060503241005180601110304060906032c06070305060604050a0e19050901020901030b03030f0403030516150212070801030201020c0409150507030603020901060f0903060c0201 85
    0x250914400100141944240240c9100d504108101c86d10341c000c0c1980e90303006840d010324a4080001d0102680000880e840d4000c0090401ca8441c0f5291004551080919024500e030f180440c014490f0942e08020000e44884010000b503007881e00d81a001840705400d4071408050582e5210703200300492000300e102c03a0502e1840b080c07124200907c0200c590701c3c2c004480540021307241c0701c00310347c2920780102214101c0703000408a9072a40d00b450700c41d200212020701100d60320b46403644003c1907507505000d02c40c80b032111b2400041c3c646000350005400c0e9010440014803c0d041007220800308940c002c03c0d03a0036a03806150581c0c45480400000301d0744c0f030383d0303003005070100c00b040c0b2600d02c0011031798008050f1110107040000e0709403030b05002514051802e00009000d41c0285079080c040303080a90142d07803100c2c01800d4a01841c1071500c20a41141c405888000020b6103c0c041401542401c2c0001d45c010402032522440700002c0740c0000f01004650701000b0541b41d22583c01c44080392003500008000c12 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 26273998 1250 26272748 26272783
    0x7050d150b220f0302010e040b0405040308060a06080c0a030c110a05030a09090c090317091801060305010b03090d0509040609020a080415020a1704020316120b0c031302010f02 77
    0x40d1506000728482c0c00074081c0450480301c88220100341104800c1d00c200725200f009001400e24115401541c04100c1000580d821580d622601440d41e69940a00c90040e402a00c0d480d010341070940600181c3c40d517a412600920a800702031240c0e003940c01c070441e07a40401624000035101c01e9154101c1da00581091101010321840000c201031000200040800004030380310481d466586002440a9403c21140440810030310130003000469030040c1d0b00c0f9954903007410294580b49030030300010703034600303290001ca092119204010700101b900b520482d80508031480700141107180c4041002c1d40c59003292921420400b02142c680140e48071600301e0070260580c102d06548619459000034184c207011035041c0d507642413844400300780446d07074400c0f1402001c03030795200c1081040055014545c1940504120307010710410a610312409201240c03840034107a103240c0104c1a16050401d0f040300031002d001c000d00104100140509450641c0350001c2840c1c2c2800d021b06940a1240700781d08100c1910300300c140c1031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 26275248 1250 26273998 26274041
    0x3030405070f14030604030c03030219020c030d030920041d0606010e010908070e04020a0801020403050609011407050405101101020a0909050c0708270301020f071a0402060307050d 79
    0x30007291800690701c0c0150807078042e540d00d10000c80348000c121076058144e0807880101e030100e40b06221654016010703060140c5040303000380001103c940c00006250050b0403032a8460349034681881107450000080c40c042c0115100794550040c000414064414031070600c56a401c655203a6030402d90559420510079807034028043c03003054a50304115000c0c1d00190400c582d0114540c00f822144080c4d8402800900c4100e003042280381600c00040c03c00d036881b858080300010411002d00060001e1849000038200a0800030465401e4899400440900014150422101c2d40d030040c2505d04031003049828189000702c07083c051b40c5d0000b0f108681c10040d40000703070482c0000c1d0040007000c1116010042000aa44c0305051000300d400740180061000804211074400da040140c0d550022040060103e084030944400203800c9a110150340000e084000c40e241052100030020b207184040305100c1e2104501d0940e0000c0d1491100038420400d0050100300d10f5903104c455071041e206601c4005000d0141c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 26276498 1250 26275248 26275253
    0x9062d040603050105190807060309020102010b0307121b030206030a020304060209030d02031902070b030126010c03090b0606030601080f0a1404080c060702030a020c0906010c06091101090504110405190305030304 93
    0xf0344030901905004410350000d0318861342d079600c1e0150803125054081c048090a041007200544000740007a4110340d200c00c041441c942c0c00340700c00300c000d19202d40e100072040b80502d0118050348010300c9a0000e15030031282000903850303c00860b0f40c000d03102c640041e96540c80b07217003100007409026101c64141c03281d04205445260000000c02146840b06003044201369183d6007240da41400380140c240c52041400100015019401c900f12450a1030340c03884c4802e03100c1080582100c0400c202d0b1030020b62107072258810b00c03a9075048607810003c10fa40040c5145003140000c2e019460180c03401c00505d00000002d22103681991228691540303059443d80c190030541809011760300003500402040c0076000105840d1400001201c0c042001900900170940b01a000c1020204000b1310482c107104d41902481c001407018400d04282750b00c21032a200e105201000010020262500311a0090b0b20340340c0c01190b030303140000503a021100107c8038120341c0d0320012144074842009600052081c400801403004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 26277748 1250 26276498 26276501
    0x30304270f15030605060a1412030705030310060f0e0f0f0301061a03060405070c02030a03030f060e0106030c0305060301050601171003080a0c0501050903030403080a0b030c0a060507050601050609062d040603 91
    0x40f01d02442c011303c2161546400c11031740f40d4252040ba141408494210403603410440050680182d8400c2924201581034440d0740c02d69108603400300da0156041400d00c8420703044006600304400e6460701c000d20303200010209140314085070385c0034441e2031880b5940c555503074250880400381c4500b10b480040c2200e0310050914a401c1990381d03034415401c100010315103500c1030b150f64456640040007850740c580075403801c0c0d008008400c003040307100e500c0344800700301811841e5600d4001c0000c0d95001501051012004040f00d1010300000c4c440c1c0d05007000c2c017581c0e80e440078007000c0c81001440703078a4040c0c40e265480c064122883d8001442880089070943c9180c0d000550009814000d400a008a079202ca2a06803a0b20003100c008000c21012000702300d044103642e20581d142040503045405503c1e07400d0000e0708504e03265205100240000407528101304042c040c90b4010441940e1035030070015901c00007012405140000c1c094400c1d02c1040c40c400781035084100c148003884001c03081da6980c44000c001e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 26278998 1250 26277748 26277791
    0x100b04060903150509030304030c0807020406030b0105090717011503091704050a0b0405150a0e0a0305100b0402090d08032707030c14030d031e02120106030b030304270f 74
    0x320500701c050b03c034048030a03041c010107118500e201e0266181d40d84554040c0c403003007864641906c9000c4107005020058549100310030155004106001f05c0717601d4001048990315008214004010014040142c3c40e01030030b041506503000c1005c41c3c911401840030031001044c1490000d0b207501c008980390f00070f00d0100401002a90016100c9000864441414031000d20440c032a681c0c00074504110070354682001e90140684c201c01c0e15000500c00500c400040c00916550801d40d0603401c02000e46694980602c01c006407000117590660610a00500084010425410141032003500000242402e040002c00200c00c54291122290103403c1d40d6400e980c400f682d000442c0c3c04130500c40080707200b204001e00902862002001060080460f0000f02c0141c143c0081e05680c607200b40c11517040c2c02c1d82c6070019108011280c900c02c1c110398900b0600805540d01481c69074082d40080100f44903500740030007424103038129000c641000d94600c1602d50300815002408a48241c601003080c110100c0700788050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 26280248 1250 26278998 26279003
    0xf0513021611042c0f03190309060212160206010f03031403150d0302010905070504090807110406210203150708180316030302030604150b04050108040f020d050d0f0201150e100b04060903 82
    0x4581a04018800361b66038400c066503410407038203c50701341c110540f090b0010b1940b00c0c400e030409400c10400d0280c40c0c04c260360641d00c0c004505481660100d1496040180074010184801c40600a0b4610303200034041c0c10751522641d010000c0000003851080b144050b081c40d0103000391400511a0013414001d00904080600302c4080c042e21000240390700e00360207031545070b507080b820051510303c4555a220481460240b1260860303101c03000024500c03100c03060903074084000e051242c4600b61a2040504041d141420a18103500c001d084c00841c2d81e00c4408a9445020655182e242c1d07820380240600c0c40c06003a031082001482281c4040c10158180c01950040344140c1d020300c000c5d420306540e0341c003a0240d401440d101e05001d00082103d503114585013500140140b843e421402d0a607000308000c81d00740ba05c25a0268881414040f1a80c1d0009000d4000c000380e10003042040800c910762007490f20a40308a000001d85100895810703814140d040c0018030103444200d588956840c005804403810340b005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 26281498 1250 26280248 26280253
    0x3040f030b010303090f0e0612122b0203090a030c03020705090c07060f050402031009030c060e01092906040e1006080d02070501050c03040603180c0f0513021611042c 73
    0x150060000e06c1d44401c1e5008024580b010356181da0511004070a444240100c070304c60130300100c1e040554003005000d410711460280600410b1550110004d26030015000e100c20700c1081003026691000c20712406007541843d05000c2c4000a040132460300702c16410103a0321850203400d100c21000ba5200510480744120014000008031048500480b041200e01a4064000c01c510381c204546603031141d2691842400e0106000503d40c071184200c0740d102d10b40a490743c1d50f035031966081c06041d21102c41d50240002c01c00c56000f02014031601d5109014044900481c0c032041c121039146c500340807550070009a18410000300703030ba585100340c0d200c5c0c07550000009801000b5002c18107501c1141101d070807081400086182610f44942203009001e05040c01420014a081c13510000703201c50610342c02000a03d1031420a10704000c20452003100010851080380e01c1000a0455002050090101103030802134414070b040c0001e01280c081c01c090b008140507207180182002010710f1490100d0b149800310000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 26282748 1250 26281498 26281517
    0x5030604061203020c01120608010504080408061012020f060403020306070207030605100f0b0901020102040302060a0f0818150718170d02030309100207020d0b040f060b0603151203040f030b010303 86
    0x20518100804040140c0140c110071104d1700154050304924291000c0c6000005142c0d46c0d40030b420b421603005550440c3d0f0303154005802c0111160400215402a0300e28000c141124a41900800c4c1105800c500034040c6602d1400850540d490500340c60040d5000f4042c5c40f031900d030822000392103040500040307800a00d0800032401e040008403160065801d100c0800b0309503801c265038056a80c00410b02c85045640030403000c4010b80b00c10020f0480d10f07560b61528900c080c42500050f00c500802404003021408000142c81d0300c41c0300007401000d024000105034450b8517406011a6100c0d81d902c003102350382140d0880014007482880c502c1c034441c24090f0945001c3c418000040780c980c8000e0341c1c1450740da841401e8100350100705070b0090022030720052265070103c14964500c00810350854040c2d6144810f200140107010a0340201c3c41000d40458200b45949071034030300c988140c0e50310100345008030b844000781110000c08008a5000d0080d0440700c05003d556880c2c403079542942400120000b0743c40c1603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 26283998 1250 26282748 26282759
    0x2090c09011205040f051204030b0a05060105070318050402030112051b010e090c07051c031a0a090c09030804150f050310050607020d061109040b0108010e150a090c0503060406 77
    0x903691031000580d503100018506600920141c58090400c0d250143d50392080c00024408002814a001d1040025515a891402e241c10381030710043c015070bc3d1904010800609a89c0b0000700c0e02c401d54142440d8144a42a1216240b00c0c038894024076002071002001242c400712500e0211701e61441394041b540540c40c041d0031130301c02c1070061000303501040c40038948482515069540c250710030584031480b41040c810b502c07014580200302940d03162000000014403111350340f600401003291081516808140b1504010542c134100700e20412200ea640e07011903030052446001050010b640003010203445039140c0c000821800c91160200c404039190044000c00d480c0500c1c15284503d84450a03000081c1c0b4040907ca660b60104600326840140c041c040702c00281d8920501c1d24028881400030780b40c80da0345040c001100c000206280c140035506004010100c42c0c00e4000e0783c04135a40c1660100030356044d0220340200d2064003c1e0381e03450300744056412465403200141d4403d1208441c248942039888 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 26285248 1250 26283998 26284021
    0x181407080102070b0a0c05070503031003020901080c010c0809010c02130606080f040c05060d0e100501060206090313050d0201050c030304030c0303060b0f0a030b030f0a150c020102040506161b03030c0209 89
    0x4003008094603030110004105c0c00711a4095040d6140d50709041d844c01200f684d070582168811220011018242e032014404e50400d800741074054402c0b0002030402044400000e003900c003504400031701f03072a0000380040099219800c0041a83c3c3d015140c42c2141e501c00c05406d005e41124081c800c0080d19400000c0e0400842c040e80c01e0041f500107400003081e07400c0c4000d01046900140102003400d4569400410351b507020442d0b101e548000f200e00007265410000006d041c0360700600f410703c10350b00500c00868a82c444a00301c03c1100d004842070f460800741880166464010f5021041c036034000441080706064202000c0c0ca05a4801c6d54200708140e00c0352208401030080a04203a03a50f0b40a00644103c140242d01250707680d20014101e48243c000381411504d0804030030004c4801607030541403440703400306500402c820448035000a50500342004042000c50081e49828144210844645803c0c400031402503500c20800b464508070380c588904020b0511070402400300c3c003a0036442d00240b1640d021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 26286498 1250 26285248 26285257
    0x303040b040902030c07021f02010b03030c15060d0501060f0608010f060e04020d06050406081f05070e0904060905060a05060310050603070b070c0815160809060f0406181407080102 79
    0x30418200d05103800c11031500020f4100a08001960808204600141e0348c6e0002c402c2c60110175440c40303140c0c12440c017002402c4d600411a032a020f40d0041c04940000c0c1c1000c0b850f104040895075644040e561340c10300040040300c513080081c00700c0d40f80582c00310b003486200100d081611310b0764807030700303840c0c0da982c401d10300040311503c40c0b0400205802a58190307441c0c0b43e00105909100c245001c1041c0f5103e00004086806561041d0115030001c0700d05031004519519001c00040038800c20800d500e080400600f800f04c9a1041520403000ca90006081003050340c04118090341000480d4558505800704400400c01619018402c0c890f0300541030a80b100790095900c40c00002d0007400e402c0c0d01d00240008a034020660031583ea910168020680c0c0708100314803680d09a588041c02e05a0404040c0758070030806020400042207014010030441187c000369054100c0c0d1824801d030b2850f52207041941c003c1802c0041c00d6649480d03c01010180310340c2c1a0201000803009050710009a5950501c078204e228 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 26287748 1250 26286498 26286509
    0x621040c030308070503091b0d021906090902070b2a03040c0501080108010c0210020f0417030301030201030b09090a0809010c060c020708060a060614090d0c0b040f050108010e160905210606030304 86
    0xf214a01d0950902003030140c8d6283d40010b441942031080075800506441e200110311201c2d4000360404001e16035115050300c00400e40d204046150031000e450700300141c1001405500c400001e0f039110650b424040e165403015640d641c052540301e04081c905030026a01500c41c042c00916543c0c0042003440062103261303142d000540052030b4941e290803a05029410059459080507014800051180101011132001e5413488010b1a03903507055100240c2280c03410403d8901462032641017044080000070074001e01500071a1040d164840600100e03404d08103000010310007030400d81c440000341c0c1c0000d80c11058a19503800d271400e95035070f001040c04844451240c0301c0010039503010820101c50081c01407180c014081d00000b41c0c86981c2c0c550320000704003984001ca03450b00014007089804d607031088a5020305800d2900f8005540340c02c00a0a01c07d001902d0301d00707490142c0c0c07400d0760164041c0000030000c2c440136154502840b00c00d40415203a12440b00c8442c0e09028160002c6c40034600801110103544 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 26288998 1250 26287748 26287753
    0x120203060f07081302120109060204080123010b0715020403050d0806030309010c020f180c0301090f021e090a030204051305060610020d0f020309090c0702010f030603110621040c03030807050309 85
    0x761614480315054202240a03a00546c0c40e083c0304100c00002c2c06140c50841c001d600c090384c0d0354a40001c00d070031a0001c1c082c3c0e0410104407e00d52404001c0f11180300d0448040501080c5c8520302ca041080c110050151407002030781c80014000704100d40450905c00c0d101c200c0e190a034103580c680b000e06807203224000e40b86001880041d64a001032900c19001c1356000c0014141c061100441500391104032016102d5a041603008030041022940a024080c142c111442080d410030320701550901d41c111034064001038981c0c02080006480d220b501c1c2840c01142c0081c800e10690501030040e41350300d11807190a4800b402034100080c2203007000c10a0500c0c01486034000d06c0122400034048803100040d0b0705007800c5000400c8582c0f0103540390400f490143c0d001400840c0d807451280300142c0b24003100d0401505140c00e1607000c0001c590090f044400f070070002c0c1c498030340d10040c05041d411484049d015079400d00f840f80c010b001c18401d610f400c4006407480307510340c402e4544030084156000e00007124017a0895 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 26290248 1250 26288998 26289001
    0x11e080d0f020a050601090905120f0405040b030a060c0806040e0321070c30030b0a0b0901020322090501060908030d0b010306240306060c02030c06070c030c120203060f0708 76
    0x512440c1c0700c07102480a84161114034405595032070821400b0381c4460003064980e403501c414007509010110541400d00102480c00d494100b141d21b05005601c1642e00c915920070f8050300a031001e000381040305034014010080c1c17001440707018019010540359540124989103106560020000c111141c900703003000d10115103c5407407a54595003030000c0961040208140e5280d0000748003007101d24084400c40713a268102003121007001404c04071210320100b0541096061000b03a110706202c90b0565a0f40e4540380d0b9a4a0392000507440c5109441c80c0302286006611841b2456600301c070400b003500c00360541484542d036514030484007018180039100701c035003081200700745494981c0e20004c80650b06040202d8010703a02d181c20042071034420540585c06071840d101200c0c065241c851007002e800503050181e030f90710071a004683e4403480005114041c010002e43c5c0d1041c450620703c1c003001180d00401c4680d059403540040c09006400c0c50080f40a4031440c0c01003261036100d0185144141c280d0750741c4c1d1000c1d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 26291498 1250 26290248 26290273
    0x11070213050402060702030d09030201030b04021603080702120a081603020702030303010e0a090b010e040209010602120904051e10090501050102150c1606050c1b031306050d0609090605011e08 84
    0x1d110180c4102c0e4001010000600141c8040c484082c03880a15240c421201d0b16600001d410380ea9444d80e00b81c420f61040011014001d4161022817440e901860260202d9450990907454110881500c0d1094000899020441a8403143c42e0b44504014500d1040030140c40c001038090780140440294550401e00060040000400740103a010300b08840129100c161a150300f80c0c83d040c280c00045002c1600d208101c15801d04000e114010034a82c8014421442c040e102d943d0603000701d4036282d00c80da8584000c141200d207444043c013101d50004043d034038541804a252200040b441c41040c1d800c5040c1400000c01d50f00102d0001c5642400000086195848242d130800980c00b000c400c8100001080c0c034000801c0a81c85202d114001c0d0000c465581c801440c100c2a0614208050350303d658400c011007641041d03058030340e808903501820003580b01c40f40c0b81c01c980054085500b1440c0003918103d03041091001942000d41201d02c081e85510100100c0c2d0030301d2003011828007035428a648070480e40d080d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 26292748 1250 26291498 26291501
    0x80318070b0703080c0c0705060a05030f0f04030909020f040317030103031d0a0528030c0f0f0302060a0e1c050105040b0702010506010f051c06080f0c182706180111070213 75
    0x18546e00c03a0144d9114503280c100150042d0041d100900000d0404004c00010740d00d43e01c03296400c640c00f414034a1031441d00b582e0050500005014101d15107401282c114400b020b00d00544000d503070703c507039043c501c250011800e40e200e40007440290001243d0231540b00c4100190300210460400192002d40150b08081c24413214140c070000b031901446002d4a40228480d02034120700240d44a501e000754060702d09410544a0170454000802d507072066801000140e55500407103400d00702034101020f080b02c11500003500048001030321180c0c03560052401042000640c001e9218611a803044400c64403060012400c89504894807800b103000f00000d65165801036002d004440403c0c6c0e440048000316101c94010b454075507001034040d40c04031040b145002c1e010300c40d8030040002a42c0c40c42c45807a640c42007004080d006004900540208004422010302c5083c035851a1030908007241c5050411640000901240d00d04014070703540f8103a40c04290400c8a02295035054008140c2180040300d05900e90 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 26293998 1250 26292748 26292757
    0x120402150c0d020a120212040e04140a0506041203180201030e03041214010501080309090c0904020d0e0318030c10080903070501060609090605010306050607080c0a080318070b0703080c 81
    0x40c0901424080c60503441e10800007065040d0742e0340d014121401140c0b80860300b031401c14281e841036400c1403d01d445101d5128054038104c0b00d040c0c042d074415071100d06000e08144130154500400d802035402900c01d020b800100c4e5402684551400f00b01c0425081044007200c010811b40c2c41100c0d500c00036000903600c80d401c9880002504420740c0d28003a80c40410131080200f0b144c0441c0d0111991490209030380c0c0130702c40d15004151110295182c83d0300b100004103500e10040510305d2400000c10102c1080c0c4856040c1e400c01e21841c0000c200b4218910f513a00e07640c0d000b060740b05902e10304520f141960340c2004100402841c10240400d4418015203000341c8111200030106413240c0300511130407021400c00d0203144010581c0b600d540010a040c00307140b10035250183c000368107140c14a00c0c100825113590b01111310103600134005648078203800e800302d410000c9884000d80951004424004029445100707042104442d804880c0c6c49030782c40e44005000e018650380580421090400a0310484682d4000d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 26295248 1250 26293998 26294029
    0x40303111e0a020102070b0405030304051c0506130203010e0d0807030b0d080a030e07060305040c05060a170c0306030d1b03180b0406080106030c2c0d0c080102030f0c120402 76
    0x50304100961156102107460380750008840d0303441005118103558050001070041e12446010a107400d05000103e03a991045229060203200741c0c59200590b200b40c0c0160302c082a5019058442c5c85c03d00c03120b004d0700380b407001006034465481d006410311119400034061004108603110b0241a0b503854100760010700e000b6464070f8000062156540c0040e51070001006010600d4500054415448820314038200090700304c5020f0500e00000d0001040d0065034050031031301d046490507954175585408945080f008550482c201c8450400c2c0320f4003800800203140b083e281681151030341000002d00b210031400405403480c40c2c003040c52100001ca03129044006c50421f9035084030900642d580303241040d03036000340d002c0b60010b130000005208440d41070103460030202c001e1500f102c0300030760701e08010b1000e450700c080c0d000d880300c078402c030351445403505110400040d40040c0100c10b640d43c2d61180d98040e610858100e051000000b00040d021005081940c0141041002c1c10343d1a40d6182c1c28050441c8000106 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 26296498 1250 26295248 26295253
    0x2030c0904061805090d02060c1b0307110108060406030c090b0109030f05030702040605090601121d0f0309030d090803070f020627010e040509031c020c030a0504060908030f04030311 80
    0x10380040d121802400c005010306161450840f0f2a580c041089603005843c009042d00109403007010b59900040c13042e0042081819140e846601c000b0304200f4490b0006c469503a8080441c030681880141c40f07403007640d40c1b000e803910480c640e07400c0c3c01c01003201c440307000c010540707405000207204c960002e81c0254618103040c10b010740c1c0161a80c07502021000190300c201d0f0b160384006904000c50805001d0f0400a00341581e40c005241050350000c1c04041d90300c00b14a030042d5031208500c14a40c80d200040c1841202c2400741c60319180c2490540e44c90707a01804240e8002c5c401c44005844051190190702c080340c888002460405a4666403000d805004540680c1d003c1300500264540d10311000a410034a601803034504005d07803114002408058503070b00903500c610300e014204815045e01000b110507078640413804211101e080701d2600003d00440d154001c0c5440b002c2a003003500c5800400074001ea074150f40751116000d98600c18255603200c0c07400c8107443c00e4014401000002d009055000d6200e448400f0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 26297748 1250 26296498 26296507
    0x9020d0203010203190b060a050708161202070f080303010803120405030918070215040b070c0203070e0103110102061b0d0c05121501110109050c0f0310050106030f060b0903060103020402030c 84
    0x10b400d9800a0b603980280c070b0154508003200b900c161184069104080d181d960502020440141503402102c0e00074044100014951001d40000510101030350792064a0300c4583d64401c2d0025650300310f1703014614100c1504032011880c2f14001054a040381c2e80003005500c1c242d046402c054030640068802c07281c0344402e003c0c03c0441c0c0d480c041d5090403440352001c516103030700d002c0c28000c1c9020044118603529900e04010b00c070100f100d800c95154486011b0074003410b01052440841c4c586030241c0e001c0c0044a01500011003003103540c440c2d0303204e1610243e08075103883d1100351a1181800389110030007030329a000c1114440c040415000300d1080b02440c14400e040031140d080756230316104211120381ca0311080f200511215030b004444420818246402004061084d90b2480d680b90782c0100c6413485110301c00d1200300729130740402105020081e488000c1c441540d64071409006011041c01c0011040d082c03482c0481c401c11030781d064890981e401001000d06074659000c0c03000a510185c10138144560130070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 26298998 1250 26297748 26297753
    0x90801020a0203071a0402090a050712020c06040506070203030123010c06020a0c0506071b150213060e011b050d030504050127060510060203040b030606090a080309040614030703030309020d 83
    0xc081d0126007840c0d00607503580c90305442c284000044003080c0342c3d809075864090001586940ca00c060f030010b51050005025250580c050318801c440040000c4603a0002820090b6a200420014082c2b4811000c82d446a29144070a988901090003402d581c12031041c0e2040e0342c2400b2240142e0401010f04101300c00f1078440d15a41c0581e400010440f0204141c0560002001410030003560700030303190300d40381c2e01402c081e10b01d26001c1e8001003030203040c89000b02805080d00e0002e0741110005500d980c54291070b40c0c4d5940c2e0150200d01e0341744c5030030301180c00201000d0004030069040305000e6401030152207107c0144005500420340540709039038542d65525940000c40c1c01007295901e051002e02640c045803000c0c6800f400b56400100b8070104c0180380f043c100410b6070000b0540d410754101148480d01c84d0b513110081600e5018400e01507510501182000903a0340000c8004d0100075400d58003880340316210104404041c04803100d43e900340c0d1144408101281c0300c0d500550700c0c03a00c0200552025811078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 26300248 1250 26298998 26299001
    0x1c050a0f0c08030108011505010915050705070e09060a110a0804030c030c0b010b120604020901050405090c0702040603080702040c0c030f0f03020d0c09050a09090b040b0a0207021503070306060c020a05060703090801 94
    0x1d801171845a03541c3c00056105240740000c200c0102424070b4440103642c1040401e4002c460f103240fa020501401148040c208001840f4070405000040345892052030201c0d00a41e43d400140d559240c03417440d14510a091120178011203800040344d40380d400813500d8560b001c5401402c01380c0c00360100100001600005100e41009500030201d04443c540c584443d01c0b070300003503030002804c0d441c82580b0400030301d079150760800251001c4035001c850300200c0755203120805d1000d20642c18001e500c41d28121020013000515030203003108034001d640c10000c11040006c241c4100c0510b56014011560b912600c2c01810f2240c2c1e6038079440040d6160150414507034a40042c1a076844c00e0054011414854084c845414403c0828005191000045c000b03007a07540c0711511680c2000d04003034000409100001c50701805c0b80c048500d400d0740503240c00c0002c0d094004040c01a081a5140000282040c10004c2c8513031080629003402038004101c4420b1034038010800c41c92703510a090445c280142c45a000800600a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 26301498 1250 26300248 26300251
    0x14060909180d020c010f080112140a050a05030301060905040203040209010902030601050c010f0c0e1005160c0302030d08070e040b0f0d05160e040302010c03140403030c051c09051c050a0f0c0803 85
    0x16600206594a44c541c005444180d0060344501049800e000410070900032650800040341c101050b48513990302040c1c1181451120113020308240700f00c490328410000008000c5041b07032150399407080e4080d04d0f441084182d11083d28003070741c4005104014800404140d0045802c42b0b414100140b0303102c1d6041506082d54000b801d0040c01c05d0780e440d0100c02c52508041c2828040000325290f08000000304009403c50040070f00d2007414241c0380c0900010440b0820142e40038540041c100c48030b048056100500c0c0c200c04540b89000940e080c0340030400d50401c1c0c00b801d003003000014186a400702c1c603502403118000c1040019a604c1c400c1507041c0600c910360310a040041c086891801c203103031800b4200a030135030b80a02c981c01e00701480c00300c092703510031000e60f003040d0016494030300855881410807080f40e440c025811400703510071002c800700c0b04c140c0003544070302c8101e440f54007520007440c0482070200c0e40f582608246004201c04000030544140f01e07a54006120043d4203050020f05c105440d00c0420f03800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 26302748 1250 26301498 26301523
    0x1e0d09050606040c0203070c0311030a02040608030d0b03010b01020a060b1804030f14120408031b0d0603060b0613061404080a0605090c120c3102040f1406090918 71
    0xa400d101003401c1902944c154000303280025460604241d6886070300424500c03015000c144a07100c01c0c0c10b2954203104844005030010402d0000d1505d0b596419201d40c444000712800750300e4040c2c00d01c2141410b000752400118160094108070a458503203034060240ca0302c6136980300581140300111423a0f02e00080340900d0181c0e130307130003c0d143d83c2160180101101d04c0c07418500420030b000b09007520380341139106644954800716564a0303485500d542003040203e03d900c401c411601003035050f100030f01e0380e2101086034081c510621000c1c52107010b00142e0b01c901010300d5038502d1145d402b4050640107000814124000d0400e1610701a950b1101600b091000001220303140d40762020700c44e40510411400388445e90440f580400c0700c1c2e40d02d0002c0d5950300900b00310350081c0035458070700e68140100e908500d5038900c4a2a01142105503c003d480290300c2401942c24030502644086142e0049100b454000c00c03010303000b03515001e90603040100c040002030005450380c5c0d4070400010300d0481070000701103000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 26303998 1250 26302748 26302753
    0xa0612091713090501030c120206070209010303180f1802070503040b03190e030a080403080603160e040c080607020a02133b01020f030a020a02070b0c030a030506040507051e0d0905 79
    0x34080d40c804020380050343c00b00c04610b081c2801031002c203140710282d004a5410740749903400c01d051440810658041d01902070f600040010000080c507820982d00101020384100d0708a103151500c01000c2000d80500039070602d0304404100c001c8540d010741c01058640c0c0600d0440c0c0c00c16998401c10401030344111280804202e0022402141004501a00c00100301c0305000c1c0d4240707010b401004040c014014009010000b495003c1901600c05000d900c4800c0d421603000044641c4401c0d42008428040d9800c039601c5900120008032420302050081c042c00d0300e5401b400c0100c84540030001b8810000b00c4a00c020b664452007440030308810700c003c044404507204044444a04130042c000c151072241c5201050364010082c0c000c240504408580d8000e805000040e00c07031101304400c915007490743e005400c42c0400003402044001c2d000004e0005119607640c1405541d4a00c0180f0041d47c034107403421008581d0600840d01e100c81c07141c98081d80c0d4080001d000d81003103080042e0f00103a0329248025500c58 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 26305248 1250 26303998 26304007
    0x6100e0d060614010318060507140d0e0606090105100f120501090b0a08010203010605040902070602040803040b0c0f01090c050904111e03062202060c0106030209100806070903020a06120917 83
    0x204900d0a83c80c450003400e00b0000c001340c0b010301d16443c0101b4040107081c00c0c0d94400160107039019400c0c1d40759140300700300c046840c1c0c03441600110007000d00c0d6068078828401d003400650382d45003581c01c59044e03030000741032003c581900b20800d03a080788980b080d01c0d06001c0000c031081407400032403003a54020130000c1c1e404120b000440e81445045203039600003a10030390040006100581d001421a4100ca0300c0d0140165070320000c2c01c22000034081c1d03400c07a4113540000a400902000082c001d2304061104100b66920285110200350880d85100e80040a2030b20222040040e17141c05040d0583c03160003046103400d488042c50024030f0480d0b621680c84003440202021020394101042400e5104240c550b426411410380c24403811107010800c0e00030312805c0d002890510300d40007034020900a40c4d014084040c0c2d0304010b840780401c4040d60049042c94441c1d480000d00b85441020008100d0fa0050030758544031781804412a00c80803840d00c1d03001401d44401565001504a61484100c2c0d01a61229502c2d03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 26306498 1250 26305248 26305259
    0x20c0607200703240603060204030c0513020304030206040212010f060b0309070b0405060d1107151a0103021602011206050d050102120c0c030f0307090e040c180207050606100e0d0606 80
    0x1200c50101200c4aa40501400e0000440e035120400e0710105484c001d00c801c040300801c03140a042c442c0c0006000c0360001c035001040003c0c0c101d0b13400680c1c000f160b41c0c1c80e22039a001c1c0910100e010072900a001a030081c4040b4015042c04407a2024149005001040d03101c074110004094403100d50014554000c000300f080395002c820303c078020143c0328020b040c6107064546800150b06000d040302143e0340d150340c0c104800c89880b8840c11034110640c4145c0e8401c0b07418040c01722000a110756142401340c03180004c0e50701a20f42c0f013442181c10550a0540d107003078411040d00119845041c040420050030f0366050041010b50328008042c000742c0c420300000daa00c541d410000d20105d80003804100c5004000e2181d4400801c02000b0348250400c0d1942070790f00c0b80c2e9001340c111110070031076100c00c134907002030030070300c0240710700181800155040210880e25030060511641e04a1059950103002a002100416440e281c1290780c942031804902d02100d02001c40c10004401d06102001294030380c2d65120304110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 26307748 1250 26306498 26306537
    0x706020304051b010f1d040e0d020a1e03020307060e1603081c0603080f0304030201020f0309160806130f020a08061e090a02090c0901030f0606050405010e0415050105030a020c0607 79
    0x210001e1a0140800e4a03da40190245042c20803c40c038018141e0030300f01b00d648540d440f2036403081c01101120042c2070541802ba484003640c0c001a035007002c1002c40350300c40040909689040c268554021481c1007880e4a41c00020030b902d18104500303028417016114100e80d00d10641c4050350054603055030b110003405c0340f4290503500012542c00d0354141042007020811407026549030710b1400d16082c0e6244e4451030200c0c024460b05042c4072010f0004814040e90000004c3c1c0040e400300d486915403005501c1d03c4195170b44d400b00726040594009a0010940000d8000c0d165000962019042e401c03000d0703c884650782404011668021108000c05018038105801340d40c403604910001c02420407550a90081003c5040003401040040e03000120340310030f64880e900c182100c030620101041442e0300c0c0c0000030110ba1180c45964001442c0d8005424189040d20440000f290004410b070346080c07130070300191076942004200204207582404910311000041c02080c1c17081c09280d0325601c100d21000780888 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 26308998 1250 26307748 26307793
    0x60501030501080c010c120207050a0612200a0309020102030c03030103080304120e1c1407171002090607060506030307060212010e0a1407030b0d02030a050303070f021609090206070602030405 84
    0x4001e6409132804000c0e03641c000c40c0803560140c00c0303100c0501e500d02829042e07181822541c02683c02c4400006c0c0058515488030994440c11010780c014030400956607140c02003c0203041400c2c81403942000002c0300c0700d004c1d0740500301651040c01540d00b04900000d00d40d055400990080e80c1000000003040308005101c0b04100fa552401d0800100c4100c412000c82e5900c0703000c0e400003400610031400700041c018181860f400980d40c0104803800107850720788588452074801201e600500c11f5000010b8040303128000d8401c000320250045041c2a1151210b9001e0b05000d000e003500b60004004940100c0c500e0f0001b040b8100700c030103130824594500100c0c035002030802070a080f03009152a0301001c40c2d8100c80c1c40b041e00011540340c04201001170f440096821415210001d40c18450074007598200540032024503c141c4040c4c0300c82c8100d0300d25080070f98542004180401d813400e51020300f0301c604000d88d48100300c0c00b8000341c40c4604040d965643c0c0310490780140c9069030260700120b20310310384c0d91802c0c0e50304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 26310248 1250 26308998 26309009
    0x70321090b010f060e0919020304060207020405070f02061b1606060e0907050f06040501080a0c0e100c110a060903240e0604060c030608071415041e060503010e0f0907030203060703060501030501 85
    0x143c0e0744e1f1420306580310f02221f004006207a00b5800001040c00c1c0159601039980e680e4004008100e1803c0c40f8502030000824054008050701407407001401d8103d01d05c0b02c0158001b00710f1401483c00c00c01d41c50b10721152000420031545c0c55030380e2001145409454005910a2041c50020020181808200050002c100d81e4051085034200002e21050364000d40c80c2e40c10805502c3d0220b4801c40061003a21140112032078030360402c8030703040c91544c0346038490f40540780039014140c04d0407110320607410301c84524614014500400c41d04142000080d000c000c440d802d4070703000c0300040721940545520009172007000388541005d9124100340030610805110346c0320001490b0804001242c40c0c0f000075904c0d40824400c80e21490106080d408a82d141e80c01e05590206400c0c00003540c0f0f980f280300e4545005801c0e21261184a040c08020644038021400c40e41070360300e040d02107500c03a0b5624441d018a840c00a092800074040e202001006031404c01496001c0d0f4010b48020500901741400181112380580c0700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 26311498 1250 26310248 26310259
    0xb0901020a12090203010f020a09050901080705010c0b0912040902071209031101050a0302040e090102031006030e060615210a0f02180616080703020307060f02070321090b010f060e 79
    0x200d440150802c640003181030380ca000101c0c1038070b02d41c00040e00400103109031120b40d070b000048500711607903c1945141541d00031115110f0700e90b269102c0540d5582140582c1d400b0540c06034000001c1414940000d5000b0301c4c400842c1c00040d9040b034424000d4000e544600e092540101c0c032202044800080003550312000d19064561070320f503450b1640c40c091003080c501d0512100044a5036168440c0e0100c901a21920758014003038102495918002d52046440c940c1f46c0d003880b0004a5490301c64040c020017250032000810700c0303440300410010007100c0d00d40fa284190b08100701c800107000c03030102c09015a02402e04080c1d02898508424000d50312131804802600d48104800d4154040261400a140e0803d8980c240c9861140380c1c141441c616810002e40025408509182016070020041900d00d106140c280401c1e0383c140440c0050340103400004000c00d4029410b6400c241e03801c01003800016106001088066032619400c00e9180e080c0c214462620724060140020b0b600244c24500302d00040c1d40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 26312748 1250 26311498 26311507
    0x1f1806091803030f02040b0301150e0105070309051509030a0b0108060c0c0a080f041e050a0f08100f230417040608070503040f06020c010b01110118020904050f01090507030b090102 79
    0x4900d007400710500008041c07658030440c000240c0f074254140c2d80641481726007560b40b940c54040340501825001164400604600c1c00d4403201c2d48100d00b90b610450f810703203c0201160a2800300041041814080003407400700784007031080d40d5000c000341c3c450305000c0c41c1800c0255050641d0503003030480040541540c8034040003140014480052111211038106180700d459000844000c07185100b60b80c40030140742e49412540448a06002c90003003151412100c840005944848041d952049440380341072641080141c400c142d0584d40100c081d0002d5280000350084090799000c4101e00d650b03407620350304446a0100410002c079446800002c184080b078890929107840b82c010601e45009000c0001c000011011408010345d441110030410783c450360030754542004014890003040041c000b02c1c006205c600a01c00307020700600c2a503210025a00354109081c2003a024031024607030240044600f8418140c2451281000780701c3c8080c254401c1d0041c5c182d103407441c01c1c4040520030180c16011240d10401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 26313998 1250 26312748 26312771
    0x80414030c1914070b0d1506051204062004090f05060d021c0611120615040902070201091a0c0d0201020a020712031116051002070e040b1f180609 64
    0x585060070031a005044039200000d143c1614040d80d080c5101d0710074459458003144c000d07401c0f400b4169003118030a00304404000ca00c0500c11048661191034041041000340b000a5506141000c0d8400d000d0b4201080b0040440c001c10215598042c0c86100c4142c041824003440c1300c00d0080c40c208103110b810a01ca5400c051000a00c0768142d450028441e0103d410b00c10300e0129108e0340c24120f96044202008805951203000001d90700103815201800101c8000440e64039101d9000008090030021280c01c1c9030400030054002e42c4a240c00340e040c040c0000d400211151058001c400c2c400d44001c03407030b4542c0b0b0700c1e800311440c000d1800c104100396401800720115060703000039010220380034020a002d5000886c1815503085580c1e419941c0c480c01a0019a2407000101800400311401036a0700541c521022000302d0311140b041c010745d840f405011000c00d0110301d41400b510342200c01c030180d0402c1e00303d03403410300d8110403890383c44107410381a03101c2c03640302c601190300c40d80004041c03c1109100c1c0703a4216 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 26315248 1250 26313998 26314003
    0x503060103080d050403110d02010501060e12060703020913020c010b0306060a140f130c0305040309150203030606030405070b070f020405060906010509041e0c020606120d050304030e01021005010303080414030c 92
    0x1103e00140050740c0d01300207028980f00d000848040901c00c000c1d0750810702c01c008001d010301002d026680c08540070b503100c0110390070623280c0c01a480b9425400f40101e6160754500301c000e580030448055201c1c20b40e850950b103804e45440180448800d07038000080b802500801e06060150040515110b000405004c12880082e000e40c40c2940c1d40c01c0341c41c80003001746040041c2e400e600c24440381c2d403030030714100c9401076454059114a0081c1c0c0251114074131180e0381d1194004549401040c0c400581003030000c1409410048043c0da00b140c0306000340d86040780c90741c0d1015400c6d0400c4509503015a0407907211360035403c03d8410950415001d60300c5031098500b0f54006802e5108280300a0300a40d6030780a1003034002502d403121420016003500900c0030f0303da40700d4001d6441c6020364036a8400c5041c00c000703620030400081c5150142c221a1a44c5081d50f0319518141d9410320303a603003000d0650040504c1d02c00403401c80d1048501a600c261114405400c160400354030181000300000c500d68070810210aa00400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 26316498 1250 26315248 26315257
    0x30605070c05030d02031003200111060c040e06060708030f0708011202010503070507030309050709020d05060301060f03080a02070801151706060901120807020603011502060906040206160519110a050306010308 92
    0x1540f8000d41d0f05d49403841f034089501c1c102d500140c403980300003448134a18114007015100c5280c00740d990322032a46007100e00d1030301c1c3c031020754404c426600200400c00580c40c03403101c1c090303100900810f002c1c140225502d840c816a40202c0e00c1fa0036113204541082803403a0409803642c05401140001000100d03250300180407480003030b04060270301c44042454002c051023074004d0a400f69010701912442030307a490669001e90002c140010181e030501002a259044c1445060304440041c0c1d40845854959120600194000b404c1c240850003070613030200d5080c1090248800416900d4151080c25180c105154001c0048188040568200c030081c00015030307440700c200c0e06440d01e100c3d1902d0b40404601e0b24441a101300703200207421180c0440005040d031508040c0c801034441e103400380c1c0d6950380e40881c01519101d003110029071141003801040842c500c00343d80341c076080348100103c072242c0d5500d411083c83e00317066450031203003000701800c0c0994078203009101e0f800800080c0c006003019411360b614001207004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 26317748 1250 26316498 26316517
    0x31b040608073f0c050c07090c11030a020a020a08031206041806090b07090b25060e06191d12090102070506030a140f010311040b040b03030a0504030605070c0503 71
    0x2078070030892080c4120074900c030210034414081c100e00c60598101ca81c82c0c0e465900340f000d100342c07820b42620082c5000e00101c825240f200d00103018030600309400500200304500c80102040450081080844420002814542d11540050070402c0140c410000400307078070703000f6102c41c0d0001d00c043d0100080201d80c0315040441120b011400c680c504415060b10303131a000018105a0406e890581402152483c0c1c501030040c40c1d407900d10040d100c08010f102d610601045017403480708008100c14490140790000850fa204510200700103401f400c1880c9803031801d64100d0807460400b1050074254203241300c4e40c241e03070440341c102011b130001180303000b6186d00c641e0241205100e00010b40e134266a1081c40100058a002000141c9900740804420000c3c00c5e07180030310a61520160114505040014146040340c1d88510381380c00745101d50043c8400f03056070984481e00262a10300ea12413654090000c0c00404200b940c0380c0340c90b246141411016150301800032418070160800340c801151010003103454262 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 26318998 1250 26317748 26317757
    0x2010c02010203090303040b0c010606030c051e04050d21020601060c080903030d020301080313060203070f140a1e110a0605220f0303111501050f0f0a030206030c031b04060807 77
    0x2442400140d0451140c003a455500d0b000c0014040b401c04c0d400005429500702d658003c02c660340c1c59800076008c82e2881ca10b80c8010600501120603a10303240c1105188070607000005078145030303954000c90051460100d0880d100c1c400f40100e0180c01c9a1602d030710146841e284001c1401d5450200080c0c8801040a4090454400052440f1168034100103c8520603040d0708119525a074800074152a604207801c101c21007081007400080040c400420f46d514190441c2031688407540c940e0f103030142403040e0170780c24819010301004030012402030040c80044411071141a00c00603003d140c031241c03011503106070380e1280082040c18000103a201050f183c0004950a40c0140e0f541241100b183c08440c5500082c41c84809400120815500000a88c80f202250044440c550030760055020304103002d01405820100ca0100012245840400040310400103041e1145c050740300d40104209a204403482e000c0410b001050001c000c042c403845800c04e4170502089800e050400f40300800c03e2001814400400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 26320248 1250 26318998 26319017
    0x20a030f151403151302031207050309060304020d050a03020c01033803070e01080a02010807050c061906080a06020702030d090305030d09060b030f0d09140109090e011e020d05150d0201 81
    0x689042140b00b90041d168283c1300068500304078110303030018070740300c040b400380c080d9007031000703400916809031103241c0d5200000d1410b240c005e04c103000c240d4000a01c141d034000561143e02021a00c10b00c824a4240d00950203000c10400b9040050142c0d401003c0d4010541f140300b1801e1083e401c20042032040720203101180481240b0000020720f000c0c0d9a8003c9805075904c000001860f410024000c05800d100ba02e0380c844540d650300b03080d202c0c0d000308450702034140c00402c0041c0c1c03d0720401c010220a00c4200d400041e070682c03110741840c5131400f04001110713500c0c0d00041440c158038040050f420a503140d45403d40c2d8050450b83e610391a4040e0000d4004c0b0192070303900d0b00040160a8102519010014044800c18140d60f000725a0391101c0c0030740c3c20080b803607490340864000941540840d403070313606031600b200042c50050844000d007615904809595030720400305140c200c01c00001f003121503443c01c3c09a200c034100c03481c0030111900030f003500c40c5004130905a0192038688801c02001503809003441c1148 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 26321498 1250 26320248 26320289
    0x5060a140a1e12110c0c12011506020313080a020307090203060d020d030810140303041a0d0219030605060304110409020307050301020310030b090307050303190f02040603020a030f15 80
    0x19800e2000075103260400c5204a070565480100e591403c0803c020034000c2c0c1000406000d040d2054a4040040c0c0e08950030302c81c0c10342440741c2c0841c2da8403180c1d40005003024100743c070410a0100f54000d0401a000040d40820206403a1070041c007034840440134021306480b650000340d4403000c511418100540200003c1d0050303031a5185016401d070003505240801c09640b4001b00903400c1101c2c90450100760100c08101c903400320300004580e610180085180a007040f00d01e071900d2900304509503200d0010802c42110000038006841c10104402400d2500c800031340016042d03030003541100340110004c0c010040410703031a00e0103d003045815500058208003600210f41007000d03581009030158000002d010070010035149003421a4054030091000c2d86a1080840d01c80c412410080c0c202c1e4000c0c030204480b800c5050310091072000d40d500004151500381c01007410b98210750301800100e0b60120b420410716400d802950910715140f078040040040c5080c8100d94656103006242c3c01c1c00405688014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 26322748 1250 26321498 26321507
    0xf0d0f03020904090f060e0105040b0601110708010c08100902031003080a0c05070f0503190b0a0b18070201050f13020d030809070b0d050411031b0103090f0803040302010e010605060a140a 82
    0x2404000900f051080203c0c1d402d01040c69145810b04650151414103e080002d00c103100b03403030141760f00140c00012a202c01c1d00448002c8410b42c54900030b4055940300080c0c40000340305d40000701049842e541e1552618160803240410540c5c40f040c0414010003c01240103820312101e01680c0d4400030841d1900c245100032140030640e1a00144184078070500403c0000c00b0301c0707540e0102c5500310300301c81c003c0030b00d1540110350b40c40321100141144031420101ea040441d40e0803050f00210050720400c800d4001c070584100347c50302a60103a0150359110140804803c9074074800b60300222050303c01c0301c040f0030795001c40c648120201d4090108901d440229401160900c011801041c041a0300c40d01d41042020b05001040d09582c1111000035180030358840d41008682000d43c090b50640100403481450015000b80111001c112214951004c0b900c00091000000c0c501650080e0300000b5085a140c0c1454212101c50b0840d902c1000f06200c030819443e80708003584148001600030585500d46504141c6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 26323998 1250 26322748 26322757
    0x30207050f011b050a09090911090f040b0a090506070305090c03010905030909070201050105060d0c021207050d0806010206060a0303031a030d050304050607050310030308060f0901150e030f0d0f0302 87
    0x8009014200380c01815a070150402001c40541080302c048070210590f05854034800c14480d40d002c40d05440f4104000c1d4a84c0c0c0c00020918085c0d01440405902a000607807640300031500000900c8840d000c0c4428825840026984042012010090207150749c481d155035480051041007090f450301c00103001540288500030004074050000c0c13209060034074085459030400302d02c1d28000c1503a04005071005105008a604030f0310050130759841c009040b160700001e80300c440880c0040d84240c46020701c082013482c00800d01940200e014211145201c0c400400d204c0c0084d280380d0441d80b0000074000141d4400401000b125450b0400140d04009071601e03a50708aa0152229494051002a244002d4001009510541c402c4090381c0340b640e641c2c40140c030359000c04d0b01c1100081c0c002d800180700280c01046d903160002001064250b1602c000b40004131000400d0b0450103a18480001c2c07880c9081c3c01425500c00c4460441c00340841440800c0019900c900c40c610311001c00c50400703000c0f403025000c0c1e4100ca = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 26325248 1250 26323998 26324003
    0x415020a050d020c040510050a050607030504030b040309090f0605100f020f030a0c03020f0d05070602090103021c020405030d0201020c0606010c0804030804060905010807030905060406050a0605040f05160f090b0a030207 96
    0x4030030100c0c40000181d2251188412039000354100300000c7d40c2c120506040e10705848004060521081c200b00512210383c000200072401c0c40020403001c000f19840b414040c2c45248255200e480e41400c200054055906103010303056901d06100c0700340070f140d943c40450040312099141240b030100ca0344c0300882c64250342c680c02c451903020001d007100b0281d0b48140000203090103602106d080b030f0700d08140c0c00d45d00c403601c010540004d1400d0101d080050702a4009060b80b4805150160030600c00381d58040309806046074188415900050420850034244140030b440742c91800210b05041c410480b103901c07030070000c1c1114104240f51111404101505041c2c1d03001d560000042601d0700c0c0c551401410b01c0c8118020f850120342240d00003029a0320901401c8401a4000068440d60703e442d42c440010702401f03440544160f480b42804100d94a6600c11400080e0308110301103424101503180e1490345007501040e4042026003023032201d42d5600304801108465104c04031650f28021224210001d000300d4600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 26326498 1250 26325248 26325253
    0x2070302090604021605010902030c010206100501031e0203090a02010e060403030504030204020a030e03070c03050c090405100b120a05100b010302090a231f02070906081002160f03020303040b1b0415020a05 90
    0x20041841b805600c40b12010340f080d02207030481c003a0480107a94a02c400c8811b5060f58000320b070244401d512a0300100411501580d042000040e122200b00503038004982401040d0303c40b000304403d40d0782c8504052424038095401614003411620000d00b14841c5000180c0a9500090510240f600c02d40c001381e01030458400b92a102c1e00d1502e4508000c1000384070070390309072084090144061600c1401580240e52100c02011103203807101d6148090100307044215405103070454500001c0381c0a018201318140300d01c01a00c1d43c5181281113000b111100d0510030304051042c031241041d031b1114081201075511088483e00990b0907188160984100c0c0703204203801c00409188a803521051450720711821035580c00ba00c8083c1d0b1607108440440385280318540c0260700400c10f41e800407140382e0041c400031107000c0c102107590001d502c40020b07e020320501140182c0c0000100824041c1c0d10f940746403c203100b100071030200b103400352089001d030055006010521030204460300d0442d00802507960001c0c1d0120a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 26327748 1250 26326498 26326537
    0x206040b03010f181107030e0a0b030c0418020f0403150b060708030a0507020105150d0309050307030302031911060703110c07150f0e030d080403180906140d030207030209060402 78
    0x443c031107a203001e40700310303880c2901204400041c000035010f01c002c080d254040d0030f4244255a101103030b1040c03122038216084000749502081d000c040d08001c522a07001e15080030781e11440e01c0341540034500d4083c1e60b003a0080c8140808149410aa802c56046a80001064000c1c80c0f044240d44010001442c0c015070002c000500d04c020070241801031845068880400c00c04c641d41e800d01a0300742c540c08c45c2e1003401500b110603182c60030301d030940441621a010f850844203840e29600071a18080c3d86401c10f402603400071401e45070f00c15602c1c81c00900c007240340c5440028a0b80310241d5a039102c001402c9482419225411609aa2030810944d80701d00320f0041200d805580d104409031508001c003003158009801e80c02c1c000700e62406800d40c03200c04000600146070042040b002110b456401070801ca0801c5035240d41ca170b403800d00801203100508254900012580e16140c500c020350140340c1c102e14002c5404804c8500800c0c1c02107014000c480c6c040c5d4103442c5c140d1f101030001c2d00922500b00140c40c902c10020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 26328998 1250 26327748 26327759
    0x105040c020f01061d16092612040f05061306031e0c030e060112020303070b18030309061009060602031204080c0a05031b031c0903030f05040302060615030105010e0d0206040b0301 79
    0x3056101d0701045c950030468191200103400d030541c203005d0b4440c008a4005041040043d0001c0780c2000d94140700c3d06240404602c010030282840c402c280d840b030b926203002c2402d02400303039010583e100030031003200c1c2c581c605024040f144454850b40d1044400f490f0b90750780c86141da548051343d4450654604242003101460040e801750040800006c418803138420302c1e00120b58441038014082460350000c2c0114180b40d1207682e00c0324010f400500320003035806030004610ba80c140400c05980200b402c640501030743d28040001c0180c4607580c0d404a40d0440c18408200503083e004011075101442c00a141c00081d03940e0708140e4510311030602054268460315603a00184240807020382140603c01200e0030030600e044441c0c5550f409104d1070b6000480302d29020300c01030790716a44201d4100d07120f0b09021800440c8a400384c001c8420440b010340150300f0a01c10007580b450070040119042c1d01301a0450300b1541040002800d402017000d5171402203101207541c0d0199640d0324151001401100c260540d40e68541 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 26330248 1250 26328998 26329019
    0x1030902092403011806050901060e0405060420100806150a02031305041127030102070b060301051806010b0901020a0507080d0f02070803030406050402040b0a1710060305060105040c020f0106 84
    0x40c22903190340442e0501e101d02c0341c5018019109031134050380408844034065100c0800034100178218009641d61402c00181e40e1010304c0035035114602030009040c071450306003004000380c0740104c1107100154400107030b503442c1d0380d9800c0c1c000c0d8205014a4442e2072a512940820034101400d908007612100214151134150340c008020b001c01c0d02d00542c0e81402c60b80c0d40c02484299803d40d40b024000080500c2807100b0701e90050b074132040c54441c841c007025944c00c007240030034220b9004207819100314103400204501401d00b40595900308900121200f40f05c11030414082d03d5001c103002c0c40d91112000250700030142c3c8208105908250003805403648284d0b00c8811690b44e00751030300d1250205010b000c901030494008a2110101e03240c00003c4e500d15541d81e5100001444000c1c003c0f0391160b520458a0301e0f41c2c0715050303070340064501d400c4c40500c40030492410b2480d01c40e9600340d40311100c0c100b04003400001e5000c90000e0441c1d006a03008140402c02840581c24801e41401700710981d0701e8481c00198643d0003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 26331498 1250 26330248 26330281
    0x1204080901031a030a110607060e010603060501050603090601090c050c0f06090c01090e1303170a060e06040902150c070e0405030a08010b040602030a0f020c06070309050906010203071505060103090209 88
    0x7601c080160408a0b0240d24040c3d03500e4032903951641008611744041100c800c640c07007000c207005001c41d16040c1150b48903000c4410700413202c41c0b203079912203040c02000500c8c80b565000d0481264003906600d0401806955180e050040700609600d510544036514050401d680d41c8090480a441000503007943d210f503640011103200311207100e03051072008294082c3c00c40d44240c80b40541c2280b000d9441445040d14864540c00c110704100325844d039640c01c94010707603603580244500040828018603006108507410806032030a0f224078500650580107176500f94020100400f10b01c41c083d00c0300c0e0110f00c40c0307041c4900c2d940001400d103c1c0c2c5040008100300800144070400300d0752036070f911503600c032102d0203210b004034000e001c056442004007441c0e031360040103824003074901c902c1103a01c4000c4040214155030403c18044000c00d081110070711880c03030031010030741d070098080c0f008509105158440300300700d001d03d03101c1d00d41340d560390400302e126a40300c1d070800440d043e00a485e25060381401040e0301f800541 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 26332748 1250 26331498 26331517
    0x91509031002090d170d05041407080c030a030e0d0602030705031f0311010c020d080d0213090b060f0d15061d01090612020d0209030708070303090801090206030c0304050102120408 79
    0x2518840c20445a10792080d01c100c108042e1140152480d5941e0300e190002181400320081300c01400001c0340e240042c0a00c0e440b95100d0b0150501c80d01a40150500d0107556030400f0344650004484124142c400150742c00301ca642507e003a0640c01850000b08814150780600500610f000100b08900280c01100460284280464490710702c902c100450200c00541c0c0001000180d00300d8845e10150300c5031001071501070005102016a06665451201c01e83c01084403046080d004592101600e2018403841d0081070380c1d14083c45100600300000320b05106001e6142429600851410070318010b5911103564000e10109201c03506450300005403141044540080d210308040c0324080c100e510030241c540445c1c019441d48040400c076032035000080d421225218454550a0001c0b11455404001000007801d050300034124072402c6050003481700440f03402181c856030400c0070103001602c80303c0031030343e014143c8600c151316a121440c04901a203c1c00c036807001030b000ca0341e00344014003490301c00900340c2e40d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 26333998 1250 26332748 26332753
    0x2060d050417070b040204020703110114010f0503210c100c03020301090b0607050703081b07030c03030206010f0b03011505090d0b09010e01090308040f020d1e03080c0702060d090809150903 83
    0x4120b16081401d5101d070450050219200c1004900141071135000391202910904190b1144100c421013282181e244412110b03111001800400008e00411641006000305a01601c01c040c00d4800070f0f0707100881c8219a94852900240d5148515014001d1448080b0303440740600c0f10714402d82000780a500203001d110304561400381151407901d000c0c0f00311040e455201c0007500300d103851526a03400340d800051050102291201c000304100c00d01b03001c544007540c841c400050302c85085040003032903c101600a80c5030301030003410500c0303064039a40680c0e04542d60701000702c0b001d00103464222083d02486c07020a0f000601c0c003040004222901c0038083c0705a81c4403000300507146001210307030b00f40c44100d80c002c0c01050281c004280401d402d0200000c2d800c1c005003801d40f02d00c0c1590b8a04481109400360004603050340b990300410180e02c1450950044a6840c00c241005425000a1198400c400080b41101d41e40d000000420458a050702d0241e1401002ea14080e03203c040790200a90141d4056031003030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 26335248 1250 26333998 26334023
    0x60a06050a0902120714091c0b0a090b0411030a140a060b0901060c08130f0e0702010501080105010b0901080703110c01021210030807080307050d091101020607090e07030b0103060302060d0504 84
    0x1800c14400e130303540c105190305400c4036621600700640c3d0410b200004603100d90b90421409544c0c0d22890100c0c80401aa084c4400080d50582001c200400d000b500302e8007014144100440070416848100b601b01b50003d074140000c210010000345407094102004141040080b038500008102140070000540510824441c0c0840300c0308100700079609004000120700c00e500248086040d21004d84500303441050180f1116440b055030034424079059000c159281c0d20701003041080e03542030240341c2c01030080700700a001c0b81d41130071408029400750601c6541046402c0001034000ba1103074200c2084810744407040c2ea80c669460503018042c0d4006029130120800820104050601c606101000c0341e030070051140c244000b981d1054100d0340040d001c141040b40a005003e40c2c00e41034803800c0305a511940800ca518a841030000e410014002c044070180070004d03d0803c007503c60000003039071280c00743c64002190412a00181c3c014955a00081e400c20b40200b6100c0713880000707511030b0f8050307800b070007840404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 26336498 1250 26335248 26335259
    0x60102060906040c060c020607060204080a03120b100e01021510081b090109090201050d05071d01050306090604020a030603150203090f030a020307030c020f060d0c030506102a05060a06050a 83
    0x960b04181ca005000d030210b10001c00049115000034640e5a1001b0203143c07503c0410f0b142d20b01a03801a8200e041c1c0c0390480c20540c003c25070024540d54508080400a00500d5800700003d05541660f00d190401d100d19014441f0725030384240000001d0800d1007410070584d0400500724401d050245c002c0443c18810460b03004020352918116060742c0318014221001603003010044009400d00c018224103004061022103528090390041d01d219500c181d0310003a0403061000003030003003000c0701703d11410300c0810014041a138690f0340140d60b00c0f01080d640540c1cac403604058110024078459002070981a44a40fa20b0340e04030b101d4004602a5a402e0120303200e00d000711301c41d0340d00c920a410b00340025074070030096030300003c6c05090040e80c00ca000902004080c2800808194207030300400c03403c0c0c480c81d642d03d0140ea45079014462a500b015054840400070401103c01401000e603254060607114115140c88501c01c042e402e502800c15401002d440130b904108203104081d144600443d480342c1811100841c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 26337748 1250 26336498 26336503
    0x3020d031a03120d110c0606010f0302070201050313050f0307030512060406081009050313080c0103050709050f060d02091807090e04020117061207080a0605100e0403141201030b0601020609 83
    0x1c002030000c016000011022181090a41c001c0365942025910745440640c1c0207540c00c054201d10b480d07800601403034681440018240341ca190302c500281032040c407013100989d9020b0203403035020f0080400007d69191505050707140840440300d4034040c0c071001480c18101075200014184d001d002804080298580700708105c00e440e039500036441035034081381d10b5111620b030b980c01c1080d0b1280030701c094034580180e02c0010003007001c940e00000c2d05a4824490b156295034184951030380010f8a1820007502400c28000a00c10722800d000644640070105a91071005116412900e810030300402002d5645403196500184050440f0b414003c44c203511800503548500b2410588510b505946040d81d590b0f9641d080316903e10050001d0350003002040301024103840401845000e0110b8800410240c241881e201c81503540c010071004100e81c030075004001c49a1407400280e001549070825040400f088408204c06005051301031403184500c0b80004240700c1044c400314001c120a03420b40d591581d500400c07a5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 26338998 1250 26337748 26337791
    0x40503030306100c12080603100c050d1e18230c01110a0f051b040b062b02031003060507260601140c070618030b01090908070b0403020d03 61
    0xa415800400000e40c0364580080d00003500000341c00c11894a07850382d02d6840c0c0c20a02c18101001107485941840803038a030820114081c0603d64a0178042c0d821740c070400500d18040c10342c003003d809840f4036101e60f00c0800300040c485a00b42011040080d02d0130005850650580c000040c0c9422400d0216203500003000485908043c040400130701003a44a80011161800145c614120074005d5018100019442e28103045000e401440102030701d0700e0401382050840c40d41c0360b440e4451460090340540c43d0b111542610a0100100d039801281c0c151402d1208500344450074a80116200104002d80c1440a003c1942642d004100c200181d030782c2c42c0000d60360b074810451816070710300d034800d594540e0110f880030340b59000b0010301d0b19096516050410301c031660464000042e03103400c0380d1000c0c4141c66012000e0a00b503603200c200744540c2484c6440d41844588180a001c082c10380710031003001480801c1049603c2a80e03c0150810689004c1c1002500c070a1085490000282480c403040e603480005180003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 26340248 1250 26338998 26339009
    0x51005030121020f0916201015180c090b0a21020f0703030509190b0406020f070f260c0c010305090c0307061e02070605040b03070201141302040506040204 68
    0x103542c407107226149540d070601900d402c076840440c401c00e0440c3d0b030f107a03d044a0f000310b216003848607804e041450094aa01c0c4e000c4030340c05258081c1380b0507040088000850800c080c44c6094000b907150030700d0780f052020f095540c000d01540d11900301001c0004070310303511a04038101142d41d400c501c242c42e03034902c81c0e040c03140081c2c0303000240b800003e03020460350440e1f0440034201c0d95800103260045036050050990040c90080c1d002c21f039503500f00445d45c2414003c41a4501c040503206c2150300403940c031003c00c0400a00050880340e4041480c3c00750500701802c07a02c240d42c00c5820f41040100130315000340c85680007050024801d40f880c01070802c403040318058039045800c900280c0814624000114020840101040364600c14101c0c5000540c40a00c400300c0548030903603030f03072007446003010500c0e46030089812035100f103510080c0300b00700b050351001c10b0700c003503401743e01c201903503502c601c4000c0303026049a10b6070740d4070040d03284140681c0342e9415035800c03403003842624103010995a0078100402c0380106d1054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 26341498 1250 26340248 26340269
    0x906080f06010f0c050d0905040e01050112141f050117010b010210020703030207080d090212120403030e0f1206060a050303070f030c0311060109050a180c0303050d0207080c0105010510050301 84
    0x201e1000d6002d01d14a9400000e5890304440154060311150b06d000101181203020030401c08042c451406c1600aa0041d080c131100241303c2549041040742c140c210091000e044034010404802a0b034100f8481c602007250880004107144c02001c1500c002003100788075034a11410390074810b0900c1c00b418020501c0d04030b0144c001e80b800d0181c0e03001410180d03120000032000c0542c20051480000c0035003001e00320700100d40c800019040046c1c814860850300010400740198015080204007000500131202601e40c90f1601490700003040020030203040f07100f0801503000300e1481c0800c140000c00141184118811161481c0180d50340c802d140e00c922401ca0080e001d8410700c40a5004039006214a0120030f119180070340c222034002c10603c1c280700e000c2c2c00c00241c454585003070181e0700009001e031300004614080c41e9004c0b18181d541b00b5909001711b02c00202448400301d92242c494441c3e505503080786802117405690784411010040c0208824001d80d44100942403000c0c2e0741034131480c16681a02c564040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 26342748 1250 26341498 26341501
    0xd0c02010e060c030a0b060304080d06050604030b010311040e06040516050a0b040e07020f0f0c18060f0d03030b03010f2003091207060207080f031803030705090d0c030b040507060906080f 82
    0x80021903000400945c0c0300c648a2480c05419150140158070035030048200f07940300c2020141100c01e503441740e40010301c1400280800c2c0040f030980d01c142411a0f5101614145d960461400710b000b500800400005901801c81000300340030b004151815010400d205401200303443d202000f41d0200c8501684804a03001c0c0410700080d0340f004405604420980100c41a46603000002c03440d05c0c4504010240c55003201145480f1810320540081d036020135100101000c0c0b1300750700800d641c5a02034030b80d10f2040b00c0141100c42414040d41c070000d40000060024000140000c15400151201c003000d4030000059038030f0309240005003c00d03203000d0a82400035060b04100e0b00045242d0390041981a11110f50070401103002903400d00c02420107480b80ca29158032440e01c20351204000d109445880b5058108004102d0392070f5114040319207203401210801c021041d90304150301d0902640c6c0000f011241100203010500c800010700408070780705986c03441d5889454400407078202c4420354a10500480c00070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 26343998 1250 26342748 26342761
    0x5060301110f1b071e0504050403050d0c0e0a1205060c0307020d111203010609080105090a0507180e0303011215060e0106050703032c07140f090613020307050d0c02010e06 75
    0x24030034101031070200e61030015103c0700b050401030a40c0c03244c940e10804d150601c04104d030781c1034590024241105e0420040c5402d0310042c0461185a800039203950351100010038550140f00610744d5258090a403550051b02d81d449031801541c0100c0955062003404001113140c2908021244075002c1540580f405049000341902c424540140a0050f4010b0400040c1c0e400840c030055030007081c0e40c3d900c804013140307484142030840d980905044400c0c0c1200c0d503030001140380084c0103012252000281e4040f49140c60910008109104c0819550701002000040825800c0342c40e90156001e40d0400681c42c44608072013040ba4a940f08401c0c484814100401100e401000900007060082c100855504498560480c9409200c3d2384091454148080002c08100402c560005001ca064564007070084080006204480141c0c0c400e12a48500c4001a00c5071211030038000540c01d502410f54890411080203481d40d00044850416289031101400102c0d20500410300f801510030054400ca46466 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 26345248 1250 26343998 26344027
    0x8070b0903070f05030d0506010813030e030f01020d0606080f010806010e070c051c080c0a020615030304080607090504050606071505041b1403151009090f02060d09060506030111 78
    0x8110080a00042c804070010500c1590340d40b0401e4802e50145594a031120703160801c450003c2c00407810071031100c0420081d400c10044030b42815805090503042c003144800040d283c0043d9076441d054650000c42c420403c0b02d0b940d0012415581262203400c81540d8030b000280c5002424440d40c14030f43d1140c001082562019080f99030424910b2074240700303001c0039071269807804040b014984c0500842c05d0421158551040350325070402c0d2442000c52806110740c20080d80c410000c2c081c0d41c070003811100202040d680810880b001050a4402c4c0c44103442e0140014002984501c00c00f405103040000040c91403030550704440c22103070701241c2c02843c0180c0d040c03628000d10b00280100d84803039800305260300781554420194001c0c420250180e802401c10010b1508018140d000b070402c002e0b0240a0150a0301d030301180c2016203056070341c000f41c100c002d41810b044c002e80e16000690800030008031141b900c01c0742d0b0085090036001d00340c240900c3c0c944006041c00ca88840c00e4401008a0071712418080c140c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 26346498 1250 26345248 26345251
    0x30312041e030908211b010b0607240c0e12070801050403020d0e01050901090b09010c0203071205010e15010e0702030403081204061a09131403180a06030606020304030609060e0d050c0f01060308070b 87
    0x50400000c400303042c1c8e00411515401103a09907522145503468460100260040f45a0340340c2584085c08040c0192101903c082800c0c071005200744800005108081c40403ca1180102241c070300a01041c03e10b418042d46070300034074160380c0000d15030080342c00140d40280116a424501079540342c2e4131a01d008115416500500b80c05030402c031040d01c0c118003599040000c0344c0506020591030311046410316007282101e6624008589542190640903000c031038858899045540701740c00d42c2e80681e41e08a00300d04610454000502c400808141400a001c5890300e66100d40d116001c2046040413061030390384081a207007610783c0c0c001c50200020710044419404980401e2203031061001500c02c25a007103055400c0194002071240c0e41515001051401d450304a000300400d06040211508200d0b0007500e2340701301c1c08054440d5844400100800c125503121816695811003995101c01e06071030700411a6000807136041e4a132140c81800c600c5c0c03402c10303c14141201c0d1f01400842c0b819080350b6402401c50300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 26347748 1250 26346498 26346547
    0xc06090320030c10020303011409010b0a08041401020406030b150324010c0204050903070318080705040525020706080106030e0714030304150504080d030b030312041e03090821 77
    0x151000400594481c004208201613054001c0c1d61030b58101110703501130940031007030300d445040168010007809803040d084980040c0289000405503907581044e80d21951402c1c0c03094000c0d07200003030000d00300b0b601d64042583e038041140c0800300b055104110241c9804113031085a491002c410310006072580403105003a01043c181481519415250006402c4550440e030204490300300051180c2010391106800c030284031000242d030041030402040e0366913498240111405640d9a0012405403011001d001a00c001c02c04001c500203407521070020346440c0c1070b01c074040104010000100b0900c2c000d00841881405020003072200b140b0302120050135040c10603100307803d40010071005c03410801d4202c00344280704141d00c03140c2d5194508458540b0b4038044140050406207810761514280d613001c000c42c0c01e6100b000c881c041d403e0300c0360305080810800341c0c200c01e400387e80040843c40405030001c90354000c41c0d07403140c140c4118070f90b0700003e101404220000c00390b8141d410040c680c25058489030f034035204074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 26348998 1250 26347748 26347753
    0x30806040c0e101701080106030b070804030c0b04050309040b040218010c06020d0c0c0c05060a050a0c020a051c0201260f0711060406090510060f09020901030b030d08040c0609032003 80
    0x12000ca021414480c20143c40100240c00324200c0080d00003481080360050000c42d00803c109807450701d40f20316640380a048841004a81c00105041c144922050810f180d0496140f18840c01c0a1415031303526401540740354000c13420704000154a00e000c0c801e27101080c4d04042c0103a01c4090b4000111112506140d007210090740c00c0c408c07001a48110312134400220b02c00d849507440400b00c0d0400c00d090000581c8214030822b020000c4481c07181d070107001e40e00b442c0c00780d00f0001c0c428034681c8000740b003010043d00029000801744d451488512107003a4010700181c005e803604000d0070f000c2104580782e05007081c0003801a64001000c19004816040055449030079441c1003080900408030030b0b41004000d40d000e841854a0743d00820901205002c6580c10004120003004410b20345004403020032214420f9803180360b400302d98140c0e00e90080d040744203540300050076510007020195010b00862410368080d07032008044440404c000d8010407401d420b80e5000228400702a00740440c03842215501c205c00754050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 26350248 1250 26348998 26349017
    0xa02030c03070c05090a0e19020402070b16110a0203060705030403020f0d0c03090b0c070306020a03061d090706170a050a060308070b01031209050f060306040b0a0306060608010e04030806040c 84
    0x90200748050050b10b03114243c038400b602c0c542003c101e0102000703015400050300d811094031341e40600141e004024200c6210303081c104a200c0c00010028015030340007401c940380d64020000d0200300801d80f40701d1040d5940310341d80d181c503904081540d0b4040850000750141c0c003290100c1c4007140228065a0b01a01c00e20481d508402d030405545c0c00c2c84412080f07400801d00141240040507008400040500000001c042c1010400000c15a4a403003912026154590009010000921a800c20345c00340003410100000d00c00080301c2180c1c1002c0449002d00640100070004c54460703c03412501442e13401045e000145a25034006e038a008280c0a48102c015640d54940000003541c040054040d490090342200501c0d0324504140c12007405100b00c0108010b100c00e414401540c6c1e0900f01d295410701542e640f51030707a40d0740b0013150040c01d07003900140d8054000030002042120303a40000d000d544e50b80e5074218403a640c0d11101200d100b030a03103000f0301259a01001030480c0c1096441540c800703405140182c0003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 26351498 1250 26350248 26350267
    0x150a0e03040305010c1b0506061011070602030702040f0204030201091e030f03030f0621080c031b0706022e05040c03080a05041e03050d050d060801061403100506030d050a0203 77
    0x116070007a40212a640d4403540c81a82c401e4000003502c219003c1d1035504250b018071566160348400d0003c003824410f0003109003041009110f0400040c007011440d088524160300c800b00a541c0b9084010100d125a0400300000c400d400f44c1e000b03450031642d068403868901428181220030840704680340b41d11a861941c00000481c50703001048181d640a500d00003a40a42d811800e0140d84440d0425202e03806000c155101d04c0000e03908101030550881072240d2560758602c00c8500314481e0314000340003d0b50002c001d180403031020030358000311080794003100d95a246000b41949030904645410a1160026405804900c0103811007071303025100d24001c100711038803035803000e2598016110140009001080510050030190404145404804401080c1a1a59603880c3d55100080244c80c02c000300070518403801421038000c01c6c003801d000c41c003d2003c241c40d0061464100c001d540024441d10401318151030b038042c1407003582e001e000c024019214600b982c0c41d0544107584042000d20031071004001c840740303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 26352748 1250 26351498 26351503
    0x507080708030106081503100f02040e011d0106080601091503021603050c07080307020306060621041b090b0a06050a0c0b01120308010803030c03010e070e0414070f030207020102150a0e 81
    0x20610644155440b941055402052620010031808040406c400101550b550006410b05000c0c0040c00118114a04001c50300107070280341c0c445e000c403001c2c240001c9800c1807006141d1100c07a0503004100c000741c1e03991500311101c0c0006c0d03c01501280141c17805000300c0301000851624801d0034240540790042c2d81001c0301e4980c40c0010141c0000303c0c081507100c802c2d8002e1041400a260540040d0704054080e00085d488180152a03280300740703000503c514002101460400c01d00703000c009906028581818071080400c101601c40c090717030010076004650007441b441000c5031110b0140c11002c002d400d01c5415640e82c0d0003180104240301001c1070442c002007016000d14044c016116159a1a550915001d4162081a080b0480c140c20a0040100c186a203000740c90448401f20b1350070445403030f01c3e00306942c040c003209422900305080002480040401d0306c0d01d140200d9041e603402d1000668582d00328200d02609100a0040c1c0002c582e8414452a0f4002c3c16040700c44444002503014040c2e00031031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 26353998 1250 26352748 26352757
    0x3020f060c030a0f110c0112050402040914030304050705011706100917101503030c1104110f07050d0503010f0306020d0f09050d0e06040e01170109020405010f0503061b03070f050708 80
    0xb0b0004280300418029107900010305c002800812000740501d82504001130300341082c0b05259960665100005400d40d501c0390851000720360003031038024894030190032541d203e500440c0c0c2541d29114900e80000c29501c290b00780111020b00150a950b02e86680701007040c0138806410a504000c1c0e41000410300b10962000d00020090210042c21400c5040c2c5442c800e031086034071521245424070b5010800b10360043e11519000d50b201d8a05000c00720b4860005009101c101014400c4103408180d00e00617200780b00040c2050342c0550b0458001514840c001c0b2858032090103210460f0524000810000b811034011348a084540040032880300c3d0f0740380c445421107460003401d5405a200040200071240c10450300b0354401ca06881c982d01e0282440c070040110641031241407030440d20744602c0b08001000f035029003a10b50f13000300203005559503021001c480c0c240303034010280300e40200800f240085480c1000c0d08401020350010a0035644c82d03900655000c042c006066081c0041000b2020002c0e010780d0050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 26355248 1250 26353998 26354017
    0x19030b0102010921090819080a2604020301151a0703020c1009030b01080d0c020906031911010e010c0b0105150403051203180109030e09190603060603060506060a0903020f060c03 78
    0x80e41c18070a680e100412040280d40800b026400107074107001490300c4410781010b008d030040c82e07869a60b00103d10407547c002400201c443d0b000001c0f4403943d00c08030f9104020740514000c40080c46105000501c3c0c09020005116070300640002d041210107001070a80035043c9140240155007000c049074001ca107046080075604030018082407402d1003000403428420b030142090b18020480744d000503902900c200322303484c0e01074464194080003c00c03d035010401001d440d002655420307101045842d00212940c488071001d8045921600c0b03a4032075500c240c6181c28502d82000040075164030301002c1c40b00213862601500082c000422021010030003c20222000d40e803152200d96a03482c0c46103da4005203504640f07115140d04003030700040400e0b03004000c00d80c88041103940c20407030784480d003900341e26140141c1e0100c142401c0100001c10310000b0307404082105c2c0903071b60500440d515403081007103e1058010000c0070491001c824000350415111160901c080540628a4603900245161840d0840c030030307c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 26356498 1250 26355248 26355293
    0x90f060e040b04030f1b080315031b040f090b06040209040b0603180d05070210030509010f0e011a0402031014040209131a010206071706030a020a0303020a0c0b19030b01020109 77
    0x40c4010903134814150200c0c2200d61400c002d0304000a031b950607070500b022034094101100031010884421400c2903003550800000c08030b440104003520a00000300c010a03425201d2413070720304109943c40301409a0340d4043e43c00114081156200030421000390401c01859402c26540d850740e60036a1a030000450040c05020003100c00300350920009482c108010840d4010002b062102d580180c0f1090440d1710395418500303003ca0b003541c808101e2030042c0322180e608444d8606007246c0040901041d407040784031070ba07c032404143d030345070300c806010903407100ba1092400b0722250341c4104455500e0014421090f20700820141c41d000d0010000f0320b008007500001c8806940c3c90b05500e4207d103180c4a8003100c00000e001401c0d0924140714040d005401c40445080075101c228006806a5002c0c810044026402000005490340b641802035550540b1481180ca14500d4400490034800b600207407103005112203a00c0c01d40119000040300908081011b0310305542d00c0f000f40300c00046a1032211604500231044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 26357748 1250 26356498 26356501
    0x3080c01060e010b04081c2132060a0506090607050102071a0a05070305040201050306100c05030703030b030607110a080a12050f060102010b090906040f03090902040b03011d0907090f060e040b 84
    0x281410030300007250b09001f03910401001c400d074a400c146074070004072960080700c145001404040010700740c11881c00320b2140840e02e10901c00c140b18403890000c406400d50030f280c581d03250014000000c43c5c60082a50001c010b002a1642d0300d0800f00500d44075210300d00150900e4226a90070600242c0c00203a01c200003203d0040162026407031041a602211700d1405014604260b0000380061001805881c011202e0944880c00280900b041040259112080381e903a40c2107800d00500504d41680c0440c403901608000c203441c180705000f91003d0410341070291000e80030a0381c03505660b0303000d80b02c44814490390320588450008103114051280320030440d030907410300e0814002400c5501d0804114401c0c60300009000d035160000a40310741c019400f8554a0841c1503506041c0c07a070b41c40d29030040c4d29841c0000340c0843c0d101071180146040350004ce4a00320602002d43c80c09074106411903c9412943c051301040121900580059921501140002802d41d40303481d0115640d0f1000c03242a40c65010303900 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 26358998 1250 26357748 26357759
    0xf0602010c0314060a05061b03030c030103050c09040327120303050901060f0e010e0a02090d0f0c05040915150b04060206010302210a08091c140607020f030403080c01060e010b04 78
    0x1505008201c0c2e848200f80518004000845a1419003d050b008400124852410340c20244614812520103401ca039101e24111082ca1100c0c3e0090000310b40742d006400032403506007013002e03030030340113551585407100200107a29800040d009104202a4103103501c007000900410f41c08201c1950702e020f13550100d601d11380080f100b42502e041c0d03803141e15100b04140c8104480394120030070506403107001080c6041d0303403202402c5001a0203034916885c0c2c01200300801a00f0080440b81202490707120b8510703881810b40c0e400400089480044000e02220004039081104032000c2c0d011040c3d28542111402e07105840780401102500b01d80c0081e0b000d82e020760010b1056250106810206080741c61010103e50180010103031204070003000100315a402003012001e9a441100301034804000e1403038101c0c4641a81408185c1c01c0071660030000e240a00000718010030705c0403c0180c0070740880c50046280602c0c683d01e090843e404040603460399541c52901155030000100720a0007000423100366a21203045c01d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 26360248 1250 26358998 26359001
    0x1401030605040507060e0102190c030204021210050303070809010c030c061e05060d030507030c0809040507091d01151101020403060203070908070f0302180402060904050901020a090503070806010902030408040f0602010c03 97
    0xa80103d0300307010a00c1c2065841c7d07a400960703055180078203020741c28400007078038102c0c5003030f80c0a820080d4818004229a0449090007441910440c0f41001c2e40e41000d035204103040c0c40c0e00c22480c019023410800c11410034654003030600504d440c0e1081c5085150000a40c645004903005001c20384812009683c04901021082c011641c2100040300c41d4510b240c4190b034050a607100b0000c0041c03d0001060040041c85030104c03e55020150161080c00b803851302c804020120034a07400303502e51400c0c0c00c0002119040410040074140c400078440f0a042c880302c003905a0701c80c44e150703035680b180d903400304804000100c0c940050350203520103881c0d4142c05c0d4206078840d800c015031600710410075641104c0400260b42c03601d1180814124a0b14645141d4907580041748030343c454608090b8000e820075040c4102044154010044101c03565038018910362a5010162a01d0142c802c07081203a018500510000c00f2a50085800c40d01c10000076150555030545000a50050790054016035900c00a29401d585c05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 26361498 1250 26360248 26360263
    0x190c02100c0503010803040e060a0b0a020d03050a1404170c0304030c0510081b030705040305060f0415020c1506010908060108060105031002040b070f02030f0109080c0f0a0812040614010306050405 86
    0x75041407030440d810000d07903550320302940c8140910394000f98046589078480d80040c00141010810156480e004100301a66900d1400c603a440020700d8140094003401151042c3c0d040d203200d00e910988a0b488a032610b4034510400040180d03090b074100301c410303d4454100014801940b08082580d500b0340f410042004010201c2208001d12000800f00b1964107500b036504440f05080380c03120340e10303900c1b6041d04a032103000355000109144107000600c4608280014003510a51148008a20100520103520181d00030481c1d11202944102540800c1081752418280e210304180b40003d1007540c5c4804152403c9001c8c3c1c8940300e5600444018044d83c101808400098195100154601494450300544601c0b802801920b40500032080c00119074080c07042540e4170708100b00920201d40c0c03074100300c211a4410072842440d4480e503000034404880c085520098190021704650400081034046030211800501c2210301035611142c3c107940048000c200c2c0e0180d40580c9001805180618106140050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 26362748 1250 26361498 26361521
    0x801060512010b0d03080408040506040303020c1f0e06030604090b010b0304060c0203160308090f030d06091a09060d060e07030b0403030506190501050c030412060b0a090510030803190c0210 83
    0x5000c0c400075141c88844c0c890a2442d814130f0448296030740c0b4103201c0e289005a801c0aa8040340000f030000034568005981c070308008007200c0045019081c00b642031840400070f150765020410010140703829250217409568000000340011441c030111f0390b2015010b1000760031540380104044140000d01c00140724400c6c590542c0d00040d880d110a0103040c18068030303a10300007400c1211030800909500340620418503850b589100301c9803611142552400902142c0c024000030794901820034108e805410032003680d44101510b0084a501c44005101e03000040c2d0b070341991001c1d140c0c08040d80900c070421040d00190301803494002c5904062500509a4002803c0075201e0300d109180d0100c80500d4075400c004507042420119070702d080d041c010508500030b0b503026a403070003500c04040c01840324540041c1c0c001e4004440300c016041e00d030000001115402e80c0e1072200c0c4440741c04240006010003005581040c9122500e08510342c0301c2045000361040b0108500041e006099480091400c2c2d0103010340040c6c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 26363998 1250 26362748 26362751
    0x4080a151401090203070c0c06110d050f0306010315171e01020a0f05031302090103050d0305010605030c0304020d111c0b01050d05030919030f030306060207060306080c090903040906080106051201 86
    0x4148a03a262070400d0180240040c03d94000302003024a400f032602600640d1340039080c03074901682c0d80805807190780352102d03551207070060200320303001e41c0c1c851000c444410402400d114216119000114020b0003604405100c94449010205140c40e20b64044541549124020210052181045081d80008a004a107660700520119038800d8010b40e04540c0c18166142c159181d03500c4a54031440051a8400030750080403401c004010310002003200400c181550b10301b8130271a40e96120440341ea210031181c0700c0140304140042001890007000d04000740e402062001c0f200180340c000500144240c0e01300100021140c0c81442c1044a405000c90042208455405074007400c0e40350302d5280d20035440a6440b94030f415520010b00d4003411b40300e502840d08032a0310b000582191a02800905040c041d80026101d0398000003401ba04c40c0c0a0030050303c441c9009070030031310404401d021020801401040c628081403002048012092007520f0041140c040042109460001801111480e030380c43c0507010b9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 26365248 1250 26363998 26364011
    0x30f0f100617061605040f0305060105090c0405010807050304080d050f040204110a0207030b1e1f0e0105010e04020a1e030207020f0402070206040e0a02070f060f0e0c031c0c060204080a15 82
    0x80c00d000c80c80c20780c40100c5005018562042d07001c111451b1003070341c00031542610004404000c1c0000054001d050360015541520292039003070401200380564070400e0300050408001030016031084010756049032003511551b050580102c10b14041d2001180c100031040750243c204800c2d85003600a8014441202855500c0d03c1e2044800a4075034195010140006904001180000520424000c094445011505602d0801408211950f0103854107058a409203500205018140c0b0800d03904841c41611441801c000e0311050102a4105810748024403000d500004044c0401240c0d074005503034241c1e40103030b6440c01e0740304110820189040c4c45004510610407100143c6034002100d05407402688000080e039100e02c0014068800e00070014400f07081c00012508000640d00b000b071900601200c180955010b0a142660b501c0d03918407041da1541c00501c4150a644400d2400c180381030f607602e407900b40303840b03541c450400740d078447e50145c20b580e40410310450900200d500f10f0341c80d0405202040c400b2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 26366498 1250 26365248 26365289
    0x906050f07110303070c030905060705070e09030f071401020c0708070501030c1403060d050a06021611090403021b010306050303030f04061410030b0703140a0902010318150902030f0f1006 82
    0xb0f9000080009080c04902c0506209040c01011098001c02d0004e1a040c0d07181598503050762511010b1003a501e100c00f903907001c00c18060380401038440020041d0b00b042d04203c81c0c0d4458038000f0511501c1c00c038403950300300000c1c0b078031120902c90307080a06200c4008000f0340d45481d00040469510300c080b00d0412040c2c005140700b10304c8010440c0d410540454408100300154213042c0d0a0441c0c0c0340d0002c0c2203510010f40c9035103024000340c3d00060301d4003c02c4401804900c60090180203030003107134000c005800c110309440384010340c40305c0500501c1e018900014180d440c0c42c04a40f85503c01e507061307407007070090350100000c014850040c0d030f03480707010409a000c0b00c0c00c18161a140c0c400150000030102103c00001030301251180d4440354640202d8120780c2403030b0421006900c000c101c0860140c0c002410016000740015400441919840e0300c402400d0080f1a10301d030701e6004000d00b0102320ba150007028442c4800203070800601c40d00d003410301e0250400c00d5034010b03502c08907295a0b000c480d58405018aa414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 26367748 1250 26366498 26366503
    0x30403020f0d020312031302010905040506090a050406060902070312060503010b030607110c1017010f061202031b0309030a1710061803020a091401050a0b090d0f060906050f0711 78
    0x24001c800755070920144060344006424a500c078400c01c13012240c04820000d00740050382155034820b000303894a100103a15001130005680c000c449194024041c5804504c49000c0b6038091a8003600070480010400d4840041600743c0e401202c00b90006403000740810700a00003481041d004140c210002c014000000f40480d03152600204580140040c2081003a0300c0c800900035800240001014050b044402c0c0b80040d1082134040c4a041f08141d4580022908000c080d100d003065502c1600d5110b0756015100f980000fa43c00101070070000300910071044401c81c4e525001e140a1903106019513140c4030007070001040c0c1141c050a008028800c04280154010300030010030680301d451401c1a103801c840d100b0400120159413000750001041e9030001140c0c4845d9001c0c0c6a0703400c903840717134254990b83c54041050903115800b03851007400040041d440c49140c079032482d1200600c65030070b1440c5071009403603c00c112060880c00740c4480e601e840801100300b400700c81c0700b40e111896082c80901038100c04a0701b503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 26368998 1250 26367748 26367769
    0x301061508070201020403020a030b0a15210f0b01091415091305160807090b01030b030c061c0504050102090109080610060315051e0a050d05030a0509131a011103040302 74
    0x105001050000c03402d02e034401e4041b103001d5078004c1c01705c002d0b05950740350074900507204a48103410390b45403104454020b55601020403c4460039600260802660000701841010f84001102c400000e9583c081c0007036091078032580203004100e8005015610703004440054040102100301031204600351a807203940d0b222007650804c0011115800385503084c40c00c1407404d441594031002c0d03402907810000c1c3c20703000003071a0016240070f8082445011030300b800560070389049091301641500040010115400c1c41c9020344040e40d4482428101c80740803e05070000c44400355000d44041c1d400054007101540c1007800140200740c01c2d0f000306081d14018100c105000d030b940c000c0c0c000701611b400c4403040654204034481c0c003910f001480d61581e102c1810460000300e0400007554003a84074110000703060b150107900140416044005540f80c10340b1040c00729000e0f806a12620f07030003d407003521034880341c0311442500c002c0b811403600f00701440a01d0f0f0014002e00100324a038242c66000300020b00c016115080c0744d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 26370248 1250 26368998 26369039
    0xd0203041e050d0b0402040e0a020a0504050403051b010e0615060304060507050f120402030124030803070201110a03050405010b122116030f1e0801150c1203060e0105030106 76
    0x5600c501281c446a005401036500036640112a0f442100502c4140d03080b0358002d920840e000c000700148500b54079140c841c1000040c0d03001c842c42c0d008005906054004592140c42450305034034054102a4803a60360b4401140d803003040e0340d41e1103022941001000019000700c01c030640c200c0002080b40c0000c0d150b22008000a0691b52100c02144065002e071068844400704216100d071266506031030b83c2d41005048a080c1d04c43c1d8240401d034081400b44004080310340c0b00e1300d02501c2425082d0f8542d9181644041d0ac200110341d030350040640c102c0c0f803040140102c0b0310950741c08149400d090910301c5c252105d40455030301c0386440072000c030441c150020b142590030180150070411242d80b151482d84a00940f02d9840b08034900c11110010198032800c2002009041d882d903040020001171207a0914030104500d1010513421001408040d0400056012102203440d140c9103c0a0543e02d41080038510103400000c030361902d00512502c190300c160540506030540081104078a0041d0813000602400d10310b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 26371498 1250 26370248 26370269
    0x10605120106030b04090501061712040e070804110d12110106051f0e120106030201170c0a03050903070203070b0405040c0e030c040b06120c030601030c02192301050108010603050c01020d020304 85
    0x514130161078036000003920a801c00300800c10380d591001e20031003004400c01800001c0c000c0529512242800d04182d400340c2d1286010b4503101d69802c401515071a40c09882640c441840000010103a50384210341214144140c4420f0300c94039000c500502281050503049100340d051410a02c8a0745903541c5a020311202e04240030030380e206070901500c508002403505500301c00201e8921210f00c2c015001781d81240d100780d84107011038013050029042ca010503203400b1001d1000f0070170800580d1103504800e8000b103030030054929000c52940001d26000159005c3c59139054045010041c0303180c00c0c801c0f40800c502501342581c5c12505170300001c0d102c3d840000303d503200c1c40c2d071420222010345500041d0703102100047c000c01d005d8100105405c0c02504215030150020341010104071000317101040707921034200441040314800141c2d40c0c6c2c400b030051b40b48809440340745103045080e0720500b0900500e03000b041d0380000041c03818114204181000d21200c0c000741135510140d0042d254590000443e003c1303881a07003c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 26372748 1250 26371498 26371511
    0x20a02090a051503070801020a020f03131806050402071101020c060705060f0c0405130b151603030b13090c030512070b0c090a030609030203030f0603070f050103020306040e010c020601030b01060512010603 90
    0x742603825910300f40e41d59014030480c400410961015130060003954207a07021151101c065051165591082c90131203402c003038082c1801c020704c2e0103415641014030205480803442e10740b5600030070101e03000044292007107422164001407658040c41905882c1105660b180e02d86121a101d10b0765903140a442308090021075400601d500c6040c1040c1c03805800300800c14030401140b04078a401a0118014207440b80702952804d0090700d29a4040303031030041c0740c0d8088540440080c2c1703080d00100418214a90081e000ca500380c5131800e91441081483c7e4441c0104100043c25420700300e292860300c01c4205510a41004520003085201d404a80d104001c0010360396140002d0011400307141c940d600080c030207420921703680d013050340120203548506a60741d51212603927208001c0541d160328601c05c5a00400841c1024080395120342c0055a10600280000c145000070080e01303402c40f1080c0100c280160080d400500401c05c1c80b00e5030a005140ba4a071407800c0003941c030803034100c0c000f040c4192414150f480a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 26373998 1250 26372748 26372761
    0x60f070c05030f030703030c020a11040c02070306020318121201030b090708010f0c080a0c080a150b0a080403140306010806060715110d0b03061003141207110a06020a02090a05 77
    0x44000c0581005800e0b03e900c0d400c0c201c000f070f0381c907000082d0407004039090844115a043c4006958002250440040080c030b296210a01005000219100382180070340703034010021a11031b000841c021100071014152404121007080e040c1640c4099010f030140c02003040764108191900b01d581900d8000518131220349071114000d107002d034181d000407159400c000e1110481303192540500c03081d03030b80b82d1100495541e134120110704942c10605204041a80d4001150582d40141d00c03606010a04603090300c03c0c02d480d403c406150703070440c80031100003d034920100810198030202600d0518402d451003030850904d01c0004e0420b420051165000708008281c04090001819030100c98000e481700c10000441000003001a5a001c641c0c0c001d0039904003602400103080000b207491091010714203072143c0d44e042d075554000300541c1982000c240d1140300030310418556039034024444144503003103500d0030041003004c1c072010f40c166174441015908010580d80140e200d80c465194000f82d101400601c0d40e0f40c58 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 26375248 1250 26373998 26374013
    0x3020f0102031204061a0616060f0902030a080c011103040c151e02150105030f0309150403080a02010603031704032001020d091104050c040b0a03020c030405040f05061e060f07 77
    0x4165200344a01d81003884284886a84081ca02401b000106001040008280f01c55841044808400400c11204480c007060b0140d01c60040c0e1741c1c111348007160110003500028602030003c0300c10f490910000561281440c802d00c1405207100348214054110724003512401b0329100715115200040e0540b410301d683c0c96100d408a882c460070200110350000f000c0c210025a01d1901c0e03001980e054906000101e040e20300001c23402040700d0b44400961811040000b8406a07582489d008080da16090002000150350310340a03202c0080c4c2580006441441c0d81001401000d1030140b0144008c080b01c24003001c00d0740054442c003000030760681e0701040d016281440c0d00a00c00c08810b245823615200880040094054091040b013408840500c404d440310081e00d003e61240e4840c42040e07240400801413064001c0c1c001d800c891070328201790780c00c0603920408181502d00c02c0c44600c88a59489080103039030b1070302081703a82020790781410528018182d01d001c2086481104000040d4900100710b002c10002c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 26376498 1250 26375248 26375257
    0x4020a06050d02090406140a0509150d1106030903030f0a0603020a09090f0804120201020f01060e010e0705071211160b0318011104060804030206010812030c0c030d061e05030a0b0103020f010203 85
    0x68010482c1541c7e52a4104001c000f0f24107031407090440100c009058a0b0400e505030240401140c14480c113240241000068412150201c0396041c42da503c0030340554507480514441c804034005181d43e0302d0480c40100601c2c1000700101c220034035003030301403000d61550010038043e02d40d00c09002449c0010345c1015044603011410041007400001004100d41001d04040d1032418800c0c0c08403417500d04035981450030781c1e0482c0100446c1c404c1c26801044403d61114403142c02c120030707050162500c4100d458070130101c80500c1419000c03030044050110200410442c104c0344880800c0c80c11817072404d240c4100c1c080d11020f80100342013507040041c1d6414280a510100c0d10b0010074001c00c1c1e072181d0726907000e01030000855081d4054041d00c400050f840902107000f00040081a4484d45542e0350658422101e4020752409001403105100c40151440b10740319290141200c2d003500b0601d4038000c0c0c04503511b00307400d03000f0901035003003c0098800100d070010841e0550f9412214070700d1400c0c203040102d00d035005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 26377748 1250 26376498 26376517
    0x604080316050c070803130605031501050a170901060e0703090c05011404090e0a0201091703030c0a0e03011a09010801150314031210090b0405040302030703110c0d0b0117010504020a06050d02 84
    0x5500d0b000505e0010010090a40456806143c68000e6940c042030381c03240800c40e40c44c042074120b4044901190321560081688841074200341801c6555541d141c0180b9504030303800030480e035485009200940c2040034003588280507103418040095180c0d50b240511107988501c0d41070250b20030b00300c80381e1141c0c102980d010f0214013108100803142a0012035481710440810b83c045000148081460040c0c040c101c0607140c60100154031316242d00b8085200781c0d0040078004100444909000820382e000e004a15040040f11007140d0116480c4042109801d01a03001e41c013642e15140300e5190640040f001c2d43d040700d403c464868100000801454150320409800381c0d82d104001d8100022041040801c00640d00400c2080016118200c1408104c8000361406030140c0d109009420000e03218018032128030010500b80c0d144001c40c1d0380402c0244800314411a4102d040c1401400a500001182c0c00688840d130000d008138100b40d00407603ea08844d0190108010001549032090811030b01100e0480c070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 26378998 1250 26377748 26377753
    0x40e031e0c0a1a06010309020d0803060402070204050903030402040c030605010c0206030c12010602030406030f090b010513110c01020702030105130201050418110301090902030c0906150a0905060a0903140604080316050c 96
    0x451070300e025040c800302c4400500e8007000c00c41c0410200c1d41b082c841da0300d00711307400b400903020003220307440d2040d00303070001031a5030b42c001c0c0c0030030000d00107031a01d0045034051280a0015502c904007807040105842001c0840002c06107041d004000c16030344120407070407058040e600e0f181d803a103c50851284a10880c0d40c8082010100c100014241790300100820403030703440f583d040013140d0301300c100c0105641050340c0140407094040014085894050ba000b042045074840001d5203803902c111040458101d40003e041903540400c0400560400b802230030b511081446040100c5039480e80040c0090141d4090070025100c1410f0038402c80116074410510340c20021403e9071a5070303481c5400b6001d021000022402030003083c14501071400c020803098001c9030001d10020f41513050345082082e035001074104404200142c200011a501e8079001010360940d1940e802032100d086050640400d0b41000d01040302d0ba12113410800455075600903a601711182a850343c10b405400b400803202401114540645030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 26380248 1250 26378998 26379013
    0xc060e030607020d050a05090303090307090b01090f0e010902030618040506060117060a0b0d091712010b04060507032609010903020f01090f0b04021801090b0906040e031e0c 76
    0x454108091940054045044454960b90b48500300d0301c80090640c07000210701c062020080c11030080340038081103040901101c2c00d06e081d11001a140c00907a82c0907900b003035070320205003945507070002103a4090141010b2400c20146816544440d40c0c005108440c0cbd500d6001c004213440707954400d0f02c03040440a0b00c0e030718420760a20303062640e15070700203441d2035000c1215014111020b50004800038800c04004080611882c03a15038000d01907482080b19080042d91090040c00140045d8000c103607009441c80d016032036040390064080d0390501a000145a01c1042c842000f2403a804022101c10540c07500d8114441c059414880c0c00341c00b068807035400c0c02d071400341c10868603200544c031240b5280d000350f007180c1c43ca0074120440d5088030030407040075054081801107100031841403000c081c0c11a101402c60f078558880710a501e40c55403000e8008203800358645855a000d440c003100310a811040403a020030001551000c0c450f0b032485641c07a440c8107006448034135031400e1a00003c0c3c0e81513028075400d54011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 26381498 1250 26380248 26380259
    0x50306070f020606040c020a1203020c01061202040c020624030102041d0f0a05010f06080907080a0c230607060e0a02060c0c0901080d021f060b040e0411090c090103180c 74
    0x10100001c80005100e9000010890320b1316005100f00986d481d000362804003407949800c2c1c0031054aa003000145a000c07c003034071040800b442107100a0000242c80110f20f036241c41000140d8000e8016a011980320788148103020340c00d601c08010f440d41641ea0019a0382c11400817901a02560b80b16450300c141d04101940c0e80410024407910131036040c415000d0075a1441c140b40100e032000e01840e50302e9482408140101401001c0c115001044281200c010b80d9480d50160b03e889203142086610640440c001c01031462002c1c103074101d031180c0b41030081c1c605000070041806c9019402c8060325441c0c075041c8462800c9003d21103502043d401a2605171358102c0e09100503501d1300e01d0400303140101c84010002541030004102c1a001c00d0195001d42100145d083e5403055441070b01d0707800300c000c0f0341d00d001c001240b21000000300300401401096030000d10f414200541d03d00000740c11a8001e4402c8010000e0040b000000c0355190320742401c001511088502d800301040900c1c4c1c90040007180801340c041607 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 26382748 1250 26381498 26381507
    0xb0f07060b06032701060b0a05160b04050a0c060305010e0c07020103020d050403050c0c040e0a0803070908060103050d030c050703141e0c06040b06010c080d1d060412090501020d020601150905030607 87
    0x5401c4200710645805003644c040c090803650a88590051100d0600c4120351191007400101103462070806035414003801521421264401075030301f107415611111004081115901c0c00702c005004509080129600d408404a000000240584c07014840051541b0841e030191741a2040c180c110f80d0f040040340b40500e4007030b0460303010b0030381031005220b111898880c138034040c0035910702d00c141240944070341400c0356181281904080c0c6004180301040402003000392003000014000c600131801046522407084024044070b807800c068104000703040000c540440d42004120716001c403d000c1c06642c4444000311748020041c10100b0b5144203070002014001c0203c0095410b00550084600d41c0b00303520b4040041d20b08603055480280601c0042c492205034100c00d83c41041003060102000e200c0403c10f4054a06014080b201141c0002c1d801e00030100e5240e00400e03c40144c44280010082e9200e030b110080d60f604414480d14106400c3c031569000030901c103071140e00c000d10001c0d08549440c00c081b5005403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 26383998 1250 26382748 26382781
    0x120a0b030c0d03090504051e071815050702090403050c010e070311010e0901030609080d050a140105031207061107020a0b041a120103080c0a020907020c0909070b0f07060b0603 77
    0x18400d1040300001c80492400441c01d401e8075030305884188030f440c60081404080c2c1002020b0f00180c10490b10140c000e070f0403142481d4825102541c55811058070307980c0c1011070b6010340d04111803000317000603022849034014044684058045a4110050f6240d180c200d516110340d0b01c030000c0a50910320000da070143c001601c2e8003900e00c12030050309001c4e01c00c0011034020011404090384111311000401c0070a1059000c90344150003525110300e44464003024405a80080e030360201e50755912582100f1844034020414007608003140903107203c00c240010f4100d5030040b5400900100da03504610f0380248650310458117103030350141c010960540d541c000d0041540091203100781d1020741c00500c00710b10442c0d00403901d420964004001c59642151241b50081d04003041d840c04a21414040c0d401503601c1e0952039105900c1d40d401440745a56110500400c1745010300010900d6011003400c0c410780022070b00f910207500008460035161286403c0203c06842c1000c8441d030408400400c0c440302c40001c01840303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 26385248 1250 26383998 26384021
    0x60f0d1704050a140109170307020604061d030d080c0a090302151201080303040302030403030f02030d0608061503010504020d02010e0109091b0e0d02030c09070c060509010b01020d02061b07030302120a 88
    0x688482d9141302c00d441d000100309aa034002090100305001d07214044003843c000740c81090071a8105500359000c510a607000da0091004103100c8424510021030b00045030000c0038040c0d02a20f600c040c4140c018060141c06042001001d00100f105020a07200b01c5240004680091214111045240c44821560302010035a09200d00342000850140000400c8070f00481e41a0b000b907282c0381c9582c034219560003407074801908500041000504420860184102500180b170151031241401d900701c7d0046514254083c0c0280d0400c010000560790b4080044030154080c20808807404185c40125940e406c903400c41c2114a150095041050207404000300e03405102d920b8030f854003200c0200300251484026002549a400051041070506060310419086251404c000800da5aa41e81c3c45058482c01c45001002d60745d110041340a070340c1e0410a0703034050041070024019504212810100004884000d031224a500040120815100c5d6040300e890407201040052181030008804010b0a21407409 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 26386498 1250 26385248 26385259
    0x30411030601031101050717130807080115154503050604110301110a020a0606060816030c050d020403121101061d06031e0a060f05040b060f0d170405 66
    0x442a080c0001d01e02e05880d0025080341e03242c2a0382004603455401000304aa101c070366031003040708252120303002d0300c908502d00c1a107198890404aa083c58914668802c0909a040c4802d2401802240724030a0036030302c2e07401e619000c0305030a560560f003440c4080200340c1c0742c0b58000001d00c000030b40c45880020030300c80c0c0000c0c010040b40050042414004601020b450f64110030701080000b203a459062840301c42c044c00100d40c4e826100c241c158650003181340c250268110165a00401032580300700005800f6030f0070306030803908204400915050301e04c1c2841040c513a480540ca482d8601600c1a91070010b0500c8040d543c540d100c1c40c1c0354150034410240388003c50714556940d80e105c081805018255581e034042e41d9011100c100391030340d508401412082d01406900c4c00070b0305900c0222180b650000044008004075465403605008450210681040321031400003804002011195042e4000c44100c0380d00781c0c402200300000e070841c81405401860102803a103111485000c3c2c001506c03c9807000c468 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 26387748 1250 26386498 26386523
    0x20a0b0c100203010501140304050705100f11010207080429070c0503060609061c081204030203250f020904061407020c040b0a050907050703050705030c0105191a0f06070204050c0304 80
    0x1080c500b680002e004035800714140000d4285650b114902450780305000c1c00441e01d199644501081c1000ca0001e0030070000307000c440c01c0b00d50701c50f0040b80182001103414021031034800b141d194001280620301070308400d60002d15189003290007020400da0a010740c00411a03650001c0d18000c010002c251003401d000380035110004505141c54210144074071405804807144081040469803c0c215030502290340c80700510419120500300760ad02482181300303800850740d42c07400003445051012110b41c842105064582c0c0c1100041c90006002522a8140e41180c0647c4491400c08040c000c0c03040700500e10381e502030402c403400d92b00203040c9440042c240c0e020014150540f09025140c0114010280c0200b0100c0207d2203030740c4114020000307540a0710b003180c1401e80d00e69a2500315405114002030b5a9150010b01c1100340c50245032482c0920444800c20801c012040185000c20341c080d00740c0e208000608022440e9142d000132200403a07030050041007035207007550899000b034006950680b040b103d200e0303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 26388998 1250 26387748 26387773
    0x1506030209130b010504080307060203040302070b04080d05031005030a050c04050a0627020f0304050604031704050616050c010c05070611040302060301140406090905030c0d0519030f0207020a0b0c 86
    0x200301c030540325010b0006290240064128809070005294450402c0340420001654100910140c02210711601c0096600d05007801d0003403800c80c00d0340041c25000000c00c010814500009004124419641451078070790742c0e00b40c0004010000d59002c160540a15150f210402001260052031002d0440302000141c4407030311050700b00d44031401003104a104080326800410209000050b110547e41009464440c064407007410941060324201c0f5550711030002d0004240d0082e841c0f5404030103a006080440c0782a0b00c45641d41c03a4007815003140c68100800c0c440701d02e4403c00899440c004004000d0000c402d0b52070000740b203640310101c01d4075540c0ca03080309000272400600c201c0c3d08598008001c035044d41d08109201080500d80d1303000550041e40c40e140020180060300902c406c02c3e010b00702540c0c460202181d603500b0800c1e0b0244144c01c100040010071984048103032180981c1640e03180c00a1120654203d580003071245600c040e5100c0010080080e141080c480141000d0640c0ca0946001e8043e0703c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 26390248 1250 26388998 26389001
    0x50a0507051c0209060714150f0c0405011107030605090f061e01030b0703200702010e1206070e04140901020c100203100603230c0918090a080a090b0c01150603 70
    0x145484141d0b20344642e0600e8890b00d19005003007200c00c010110703071070000565110858103042007c448129048000e00401e1900d400090651000d501f0418080600e0445030087c2070344100d00821741804802810850102ca04200310000345030702c501d0420060510140c0c456440c50500a000c005205110004602d00c40c3c02010a1969000c01007000b103507420342d83c501c0300b02c10009000e00d04043e6125241d112200350442800c1e48001d030740812a139101400d0000600090794000c44034010410200020701520f03000810543c89115490240b801d0320b0f030800018003926017841c892140d90200d0027030082c1c0c42d0040d0700826a6010301000c9412001d44c4042003030a90100700c131540b0001111a204100140c025000141e1141d00d501c013801110401e90f01401c0a034100341c2d411240028085010200340c108446001c0004c0c00c0038000541c645000341c1b00c541d890b0035001000b003034840701094131000c0728080c0d9100e401400e84010125210030200b21114002d0000c9008513115001070320b40020424001d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 26391498 1250 26390248 26390257
    0xe25050105070f06020903190609030f05030610031d0f010b0a0e040309060c06020405030a0c0f3011030607020d02060106080105032a0a12060b06030112030f0201091203050a050705 79
    0x200c3c2064201015220300d00290012403080e50940a00000d0200d501000710400c10f800703119030000600780700903041c010720214800b1280c805001c02042031026a94440c0125600e0b422940340100c0d12514a0742850021180d8036040d603250301c10011140644072040d008013000c1c60080c1c54410b04c10781e403204911484903060b200a0003084080005100d05071041203200d16485c09190003500d4681d0b108042807428988071019200210b154070280303c60040700f541400103220003a500300361896840ca00c4152180c41601c41d290b820150f404407410002c007007285810307900b002400c0d543c00385429240a525010035406c00001409440d00200c0c2c800c1c020034045040c0c46000e03000742070402480401b140410a9002210070418400e1001805076460403801006410001ca00d040548074500d07140003950080010184036032010700050010007042080d2200b03903070701403401c0440d0b0b1910040503030040040941c05854200c900f17840280458164111900415080c2020405030f0b03038408041341e06008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 26392748 1250 26391498 26391503
    0x6040311090903030c03041b0b0d0203070305060a06050d0b040b03061003110907090510030e03030106020a0501060e0103030206060108040f05010204030f120e010801050111070e070c0c060203040506030402040e010e2505010507 99
    0xb013400030801080c0500c15070308e940181d10040715819a1030740f900c515a5000801c041e40801e400104200702950702d40100354202500369440d0141d6820064003900c103018800030400384640c1c0d81c20003407480d650341e08030302101a4007409460032030a1003440c1c484100c100340005ea4958041d40b0044401d818500d809070304c150896601c000b041d60070304080103000500022203c0415072a1842c05881e1403042c002507000306215001400d410341e44d80f5045003543c0c0780f98402c0d0882c0803070400400200e50042503140c0c1c407000034a0300145a40d02c85ca40002070402545002d052588003280100030404002048c80071140100c0b0500e40c4022111070031a41c011a0048441c00a00103200402c07481d405840c06110f0012000c0a644d40d0503100c08460350850812956000029213000b007810511400f0814000a4061807000d94541030801e0041440c520000d40000d000340d0b90b5a0f03494015001c01c0d0f205004500c51342050780d07a0000d0705180296246d4070030b40342c109040b82c000000541580188200c800349507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 26393998 1250 26392748 26392771
    0xb120d021b09010306020a030f0606020607270608070c051002030106030f0b0a09020309150c07170c0a170408010212090c0102011806020d09050d0302180a03020f100e0604031109090303 81
    0x282903507120305c00f0b074000241a00505888810384240340880b406000c02400041e80104683c1c40c01000040c00c4420b081138501c00c50401020100c1c040d011251180c05544d506c1c02c20880540f1492012119840b0481c0060103e01504003040c40b110181d4004504a41550b074080c42150b009503000c50880301c505c5040342d4045240c001c100f20002c40c070b030082d40d40100c40c0c078140c0701e01290b011051a810756080355096201e0704005036030401c018125000456035440f10314500d08040e20000c03141c3d43e4002031800980103403500c000300001007128100300e80203490010001d64407150311124841e45503005940b80d000500072511040c03000e5105220300b584c2d0414110b114501510203842d0200254450099140090384031071042001c60000c00c894545a580795400681d1140040e03039004589903e80b420500c00c402101080025175180c8141402d1590115048107030f04c04050801e441e1151100702803030700040041000001e0100307907400e003200b1003c02d0f24002d0056a030010f0035601c0c0c0c0300072902418841e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 26395248 1250 26393998 26394001
    0xe070f1409031504080c01020d06170109051207060603080a030207060606050906070b06030a0b010608040302010509061501180905010612060504150b0f04080604150e0f10020a030b120d021b09 84
    0x240f4001c414150400c0c050f841c214500440c480d0b210342640d104241642056441c3c81042180c5119510a603610703000300002082007085c0c0d95100364650700100070075070328488042144424411290f002100550f80540c07116034540802c10702a02030f4001c1181a50303058940380001416901803004c94042c003000070700d0700345002c03038954480c0c40782c0c10060041790f014850340c01ea89000440540b0228040d001c50f4903252034a10b010b1034000e0942d5030043c240c6003d0f80004003400202003820b000b26840e40000d007420343c80c003012229408404005603028921042c10800002229a080824100e032005218003d0003407540314807d01094407001c4003115162040c880c010020201c3c8a00940301c8003c40005151619a03100f40891400c2d0041e201901d240302855845d01412150344140d030400048007014101090041c1c00c41503e0710f00e0702998802036a00003481401142c401d42c811410f82c4002031072010300216800e03800d540c3d403481805202c00b61062455140c0b8015130004200c195800040a01809 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 26396498 1250 26395248 26395273
    0xf1a0103050304090c0210050901050f090c01020307020f2d040c03020310050415090510051f021203070e0306190b011e03020a09030b0906070f0e030604020d08040e070f140903 77
    0x80c105c003078a0004502500300711807040209401000c0c00313403130554000b2805092185c20303010354040103040c0d06c00e207600c000286d0143d03907004002e44100c2c3d0740498456680c421504042004418540ea0131032006010400700c15110391b03055011400380701c050707504015099500710306400702d100a890008029034941c5041080c0d18080c0c0284114824807241c440c0c03d103613140c3c000c8d415030b18180c135016007117080c0400c1403005003001790100c0c00c0e45c800d00e41e6a0500301640307240a521038418451494444e440000095543c5008508d40045110040c040324020325291a58030b44036001d0324280c480316424033545004540c071503800d0801d095642c2c035142141d8401040e05400039404025030f803050204150001012481ca0303c2c801c0d20840802f8007810035440c240301d0003030400342c031040c00006101d4403103e054a00d840c005065513201e681070b1030b0450a9069410000482e0080d50311034641001c2036010040415030240520f1018403481e2100c40001c01d074500040c0380c50140810043d0158014501580c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 26397748 1250 26396498 26396501
    0x302060306010c05030d05010305010f0203060f0d061803080402030d0c050709150e090309030c0102010203070507110402070807080406030501080307020904120908070902040e010905100317160f1a010305030409 92
    0x208007074141803c00361888196645411074000300040340b4031594400040003440000c0c0101299030300500001c525518001000543c01251403043e030380030380c410303c030000304000961f88004e441c10404000e03000454000c1c90004c000b1401164100d020340580d00202e99014005d0352540186c075401000b4205080c00e01505200814880780f6240001d000030350300003200c8210b446906d005850070406941d40e1400c12040c14a442502000e507411a0b10400c200078129510a080c0c1e03000700e41c41200751504c01a2240018041c1c0100b00018107001c0b8006001410068500c0041049480c0c54800f8082680c1c0e8003a440c0d00d83c040c225000e50044500d04c00940042c1d001c003084001d4111508101345601d44a6121502d42400f40d00801c9605500140c14407004840c07011550040540401c00e021618000e200006882c1440c40010549801030f04107040000c41081500d1000d0059221484e92640609007a01e00c0c28104500b80d07503031341c0107500049201a002c1d07481e6040e290014011850a480e00b01c03880c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 26398998 1250 26397748 26397751
    0x60a02030403021f110c0a180608010216020a08010504080306010c02210708251202010215040c090b04020703020715020c03010203040c0503060c0c07050d02060d09031e0f02060103020603 82
    0x41180001c1001000580e1004201040d5940050006040302038021001d07140c001600c0c240d00960340321400d41c800607a03079408000c0c155501c2e051031030340103241c043c040b00180c14141c0080c100c0b5400803038281c000700030403048e0f03448640c001c0f43d900803283d954928543c02c94078242c601030308030780040000130707215400307840c3d0908a10300c05446610b000d440072044500c3c1800001c00364002d500064010413a859003000b840040461500c1c01c1c0c03092001e0001c51208800162281405407030450381e0002c156030003070108440b5419209880b64281c1f9052900e8000c0b29011700410040c01d10f0610403040904051080e5115142c0c1500200fa42c2810300c0b480030114002c030481203007148a61801e5292544080c0007850040b44551520304005061004040c1409001000011f048009000c1d0000406002540bc400c455040c0c501540142c041c0c000300d4030b181b2401c407440303003c5401d000100d0200341d44540c0540f54a00c2004502c1143c5c0c0143d10b04503200c0c000084c8520040c2c0c0150018009840e00e2401103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 26400248 1250 26398998 26399017
    0x1e03050c07050f06060301150f050904030905031b01020d03020f03130c1d040203010e0c0d110d08070f260d02031f060906020609030a050d0504030c0b010f06030e0105010501050906 79
    0x300d0600c1800e40d5160b20b420b088049801c0c541e08001d0600105007824014501d01d01c0c1c805c03414141c00c47c201312010320810014444c8a00c606443d401007010701d4001d440d090b000d80005000d44042c0d0302c003109a5681240300900480c0144605100040c50701e2091007503480700041d0b02c0c10b080c0f658841600c082c81894040b03800f0b5448041800000480308050303424081d00360401ca2600c602032419004240c21240301e282440e610b5049203021040680d0f904012100c3d480d441042d42c0440390401c004145044250f0304018030b100b23000900c2c001804402d03100d10100500c1780307080c040c400405100342407500c2544090545098000c0c0444960810160041c65000f50314001a49104281800c2d01c400258a9440480462941c01e400d0050560500005034012030034401140f401d070000200422510030030381c1c4102480d544401040405d03102e901e400d00c95a42000c0030b074495507150505d580c22581c85210380c0021901d4190302e00150b040601540b812148161140c5080c05032000c1131002030342c07080004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 26401498 1250 26400248 26400271
    0x5010c060f021b06010e060d03110111040f08061609050409020609041d070602010213030f080d091101030b0102070312050310030b010e01050f040213030311150a02070c05011e0305 79
    0x403001052218800f5003078040c0740d0028903060202d0060804d04108040c0c01c03000c440d6800f0380c204140340d00c4034540b030000540d01d4a0f28010300720700d000c121401040f40054114030445c00040006072001c100c04081c00342c8071100141c8400f0789852200742207094004582e40003084c4180c5081043d4640b03031307105540290001c0c0c00140344c8035a000014085502c9000e080d8010b401e100040020210108000d402a0603980002c500e40b26080b00b20152619203440010b0030503600f020520b0400880c40b069981450a148040c00075460341c1c43d22021040070092141e00080c601b002442c203540c4009031100490340c1106e015004661119402c56041d4001480900101d007030700c80000c00100f000c8101c82c000c141c11880c0340f0443d41403c080007444001050000c2c801d0b4014421024644000c2c034111044951505050b503800e84201c0c40642007005c40e00e841c01c0d945060001300194116590000c100c810710483e00120700d10344400066030809000c1c00c15004221545d0036021280b4080d611003034008002500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 26402748 1250 26401498 26401511
    0x100302030a060b16030806030d050706091a070f030b060a05070b0a110c01020405030709020708090907030e070807030b070201020301060206130f0b0403020a060e030c030f030c040f030308040c06020102040b0405010c06 95
    0xd90741d1155000d5030a84c04682e00c0900f0301003d0551103010280c1001040b0054520003a40c4a002000b60180f100c1c0038044650312001c1a00300503a1000a034200200d07083c0e08815464041c501034840300407500c0d1540800d080042c070035054a4540704581c6280300a4454900b4983c0540743d105a04000a0030301002a90b682c2c08095008900009005030003021400584e8503824030042c18107120b0701340d001003049401803110000154582060310704c5c42a068840c40c2c09995880307000c03000782c01144402001030058040100d80d00c4400b140003001e40e4010a0380100c07a0300d03008000c90803403209104490050700b06002040c50030741c41d8042c00c4807503405030484100e9840d07652070303d48210400340ca0480c0580e100c2c1122100f040351038001c0b0f1403d0044400590300f04000070805503240c0c8500420710740c1c1c2c00d00000011322514a090306860203030001d0319441d4051034680c54041c122450036601601c031082c2080d000984140305000b181d080e00d00000c0c0e590f04003803501006581c00c5090400c105c3da110745400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 26403998 1250 26402748 26402759
    0x90a0308070506041b05010e090702010b040f02070b0c16032001050106050a0809070302060405011206030f050307140601030309030b06061b010606030c030204140108040c08030a020c0f030a02100302030a06 90
    0x40c100740c80c0200003074030b0316051a1400400d07000500510600648903e80704014a070713040000c00041b070b01c0964600c081c42d90b900c6000c900403c0020304041d030085c6001400c001d684c0d100e602500180744680c02150b0140c40f090380700051406002a091407001c1b42208640000b0311840030741c06181444640c0c42c210686000d0040d00f0b48000341c2103200050408152074a80c1940050030542201100d406001c2032400c5402141c81882240a10390511000e0340000604900039440a80115005407010400340a5840c2c03e6490b680310310b80c02d882c1d004000c1c402428094010404504995250325103840051031560350025444008004944c0501e041c00380b0507860080090080100c007000c0c00000329542000c00c040d0072594541e90305010184107100510500d501070340404c10103002400c02c07008a039201d00d0b0000d5040b06a40003610640004038501301141e40000700d881094001f00ca1480c04500c0300c10506541d00b0040001030340c40814540c22080c00340c0203600540d0050140900400c9594840 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 26405248 1250 26403998 26404013
    0x911060a09091107111009030b06030705060708030601091706040b04110301050a0603020a0b04180504050304050604030302070603050121020d03020f0d020604060509010203070206010b0d0912080a0f02040b0a0302090a03 96
    0x80f40311619500b00050441c00c04ca150b01c200452902c04070f50540d969581d0020042030f484480c08014007411541000c24890381d02000710310001c0000600c074a03a6002e50b407500003000e07001900c10702d010a1402d2004640d80d59a003800f2103039400c1810003003c8598580c2c6400400e044054400d0310101c0801e442021180c03402c1c0241c0f0700c40ca80c0a60046001403842c8103011842e04a40c1c041c54000f8814442070200c0083e030031a01da103948000f5400705054a076402c100381903200e15407100d0350228000800008150700410104100ca03034903201006181c2c0c0c3c072039000000340d0614544802c00b290040d581c90042c40c0c01c0e003800c0c92090007441190600700207098a03e103400103c0d080007002d6072200d82000308118a90052580c041e01c003c00960540c1888900a50380302ca041c05110602e41c000b0500312030a150380c0d40840881c0d6000f4003c0306160121300c8001c1d150460684560500d41d0078407041c1b40c080081d038021101116050002a4035240c0e00b41801c400a42000c9080c5a1000c248800000481c022 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 26406498 1250 26405248 26405261
    0x7031202071101020d08090c010815030106081e0c0f01050d06030203070807030501180b060d0f12030204151103160204090f1b091103160e1002070510030911060a0909 73
    0x440342102d42659a0740068504845200803208000034201044030804001c181440102802e00303056405032900705040c031103080344942c4142c0640c03030000e0004072001c0000d0310015200142d1140d030308420502410315200c0c840b800400d60071482400016440c1d500c2a0010031481842100000f121501c80e40000d04040003070b4014400b50303200040900600a00388201e001c002190705440308202007541d43c1204060b0003c180c0d51188010b4000d860500c00741c01201c0b24080d070700181815400c220200c000d4000c5d00319004041a104c03080154044c6903005580351441008298021410080e00d985281e001a0049100700e0300103440c0c4000074001005c171007600c0c05841c0b08000d86050070002001d1100b00355065480205064144150806002c0480003140c1c2c201e0740d00c00003c1310078441c20000780d40d03403d80303454845e81184401a940040950110300c080645804482181e1281d54003a803c0b401d84040071409004000841c402118601e850b000401c07100c00d85d414044046a610203001044496 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 26407748 1250 26406498 26406503
    0x41509051e06090a170d05040e040204020f0c0a060c0806041401090b0402040e0406140c03040b04120c050d09050109060302090303030115020c10080604060e04110f010e060a050c01060f03080f0703120207 89
    0x4a000200e00c240003070041151a0034180747c2581090b01e4042001b284a03c00b500c0680550340c0083c40d04481c280b60720440e42107215607030172a400201145007030340041099400540024502c070001c164540740601a000100c0a40c29288105900f01a07040d0b00a00c0189035503540150b0030000000c0141114800d203100c0c601510b40026101d60b550b100500a140c000c010707000c021020400c10000031b8810036059000358000002501c16400540141c4030605100805401b41c8500034030800441d9000520000380c85080e0b0700c0d150503650f100f606a00b030303026658030130364190000c1c001440040501e1150201c1c1000302d01c1106c4100700c042c0c000c0754090090074540b80c00607800344d080081a08242c050a401130200580c116032600c0d00da107d224003040d0000b01c1c944a4a20012443d001e40e2207604c43c08500d43c03004100d503075502c0305000050010f5101c034140c40155404d0500c0003512034a942d603210112900103070442e04e49500c80d040e41c003096010030f401b1018403100a042070396580503480540000e51 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 26408998 1250 26407748 26407769
    0x60201050a0b041413030e0604090b10020102030105010f0503250f03111303081803060a020d06081501060c06020c01020d0e15070518061b03041509051e06090a 70
    0xc01440d850103603003110329034501460030851600e01c0103068554640e44485c046040c1040c070085d51804480d8090b40150885e48460b004c5808100c0f1007a41c3e2145500e200c04691407a000301c0000700c283c0c281c1c0000d102d0140801c140c90b0200d1140d500960085a0107003032405000354000c100003044401c8107100f8407510010b4030110200020b6605441102c0c0e2100201040c5401c00b00c0751007000c42500c0181c04010b05200000c01c031500702490b080384200810200074146d030958541081030b100250007040304071190604150001401040c04150520411022038103480281c1c00c00409035241d4031490b000304c980a03420010402c4222083c80940002c0c14100c801084140040307004902e0484400c400c011145602d07030900001c9a0000300f103130000d034030001401c02e6018038440014018000c0b00c021001e145040d03a44460190f10110040041e501a00d850703444240064104032016400c90107600d40180300c00545406561882075000b00140c0010b040e585030210303801c00309101042540c007582424 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 26410248 1250 26408998 26409001
    0x30403090503100509030a050c0115060f0e0f0306070e010203121306050903270301060305070923071d0406030f030201090b010b0f09090406090f0c05040f0b030604121806020105 78
    0xd02c0c041c00000d0610049500074010f0f41000742c4c01e02d8032403007100461018072600141d4070319404000e4000000e080c5859181001d45680c410014003203100e0041442c00003171070420001030380d1030729400300b6200c1c01024004219a81d6055401e4414500c620521410344c030003804141002072509003c640301c4c903107100098540e01c90320314042c030543e01c018001070300076007042c00070360700020070f06600c2800b400181141500b4010418046070061541d5080a0080d004842c80400c841545400c01c020190032040d4600310303891040c0041c030300e400c01607941c000054550840502c0e0038807402c0c0710440515000f800050026501da5410074164507074001140940d448a00040600840814490041444d031000503d04045a001882188540049980702d21100c2c004201845916032000341c03060741c001901046e9402d68200a03640501c280300c0c00340720382d0410700d100c5e03a40642c03070091440441c00940108482d444076610b4409004140280008102065040d00e02071544281407500800c0da42d000051107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 26411498 1250 26410248 26410259
    0x30a020f070507060207060810030201020c0d0c090e0304050a08010902010804030e150406020c01090501030b030703020405090c09010b0d050a0603080d0203040204110d1d0a02030d0f12091101020c0118050f0609030303040309 98
    0x1425402084400d81300603409c03080002d80d0b004580120281d008403000c2c011910035182003000500e0769000442d296140904121150790004010003d450b41245d404001d1661180c28a00b83d441d01c1078005e0000f45a038010800090141c2d440030500712005050f80c00c000248030320300203650071035030244005902c0340e1607114483d60400d03d40d901a04003840c05000d995001808665144441e1000034040d07981c0c0c00015004860034029000000b20003040c2d54281d503075441d504d617556007145801006483c582404224110f4161081e6421654842c00c0c00303060645406078000203400c028003e82e0000d4840404080c0030000e10010702c0041002400060b405807952090303805c90725800801e41481d4000c20307003000560340010318031200201031310b0311291040c410310b070446800d0f6031740702084101801c1407841000c010322406010a000070a0f400c0b02d41c0c26800b00011151084d02103803c17001c2c20982c0000f403009040c100c00b0320200c4071020305624902010103012902d10340c0100c8040c1c0018407805c200307102 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 26412748 1250 26411498 26411507
    0x306090f030e09010b030106111507020d080901270303021c1d010b031207020a1703030f0c090f04020a051e0301060201060b070b013005010509010b03070605030a020f07050706020706 80
    0x10b1040050302c0500066043c09210000ca100601821051082801ca01070380c0b4403003002080030144840e201030f0040e003003100002c2c2d43d40203003150000101d00c1000c0010303005001480342a110b0000d11800b01c402500008510301c0c1c02e1081501541090707001c02c210280d00721404010000000d4540000a166201020340f111b9003640703059207940360b410828180c2c150343c1d000401010058494001329039829443c80029800b1007150301080319410049825500c2013404005140b0491807100525601d136038110102c0100e1040f0f40610b80d005032100015001c03810203a0191001030003905050703141c117142030220030840108904400c0d2103000000184040b5078207020f0103005120b5418001d0406860b9aa0403070320300c00501038100303500601e803d807000000b00709649141c0000d84a0380310340c0b00585410514040c0204540342402c41d800c1c0340c091999821f000540d002150550340d00d290541e11601e8004c0c02950140007071180c881d10502c0300d2404120700303006100040c205a001042164a171410161 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 26413998 1250 26412748 26412767
    0x20c03010e07050d08090402070f03020607030b0904020603070305070306050a0b0405030708150c031e0c0a170705041a04091803030b0405010506030105040905100f0c0e060c1504050102040306090f03 87
    0x180c2c2c0100c1420807a03522804041c0600503441140540c555030000040790090250320b0001e01442e0341b12031800f052580104045001c0d20095806000c0b441c4014140b11400b50309441c0250409000c00004204ad480307a8061604005540b44c003050083d650400190020180e8100401d060030025040100b031408006202c018822480a000d00781940c0407050280131000f40342c2001d0000010000e40e040140310000c031644101443c00c6440340c01c1c040814415034100d0607008012034014940e4040d812486510148100060b964151400c0d0420700350000310240003518010610040c40301040c86e02c0980141038201d0030003040e00e03403008035500700141a03d1039001c455014524110061200d0385580040700c0c15180262008034840340c0f07600d8100d05d0550400c5d0289100740ca080e94184521502e500148080320301c641e1480032004c015400c21034103100703260405205034040f07c101c00310710340d07800c80042d0301900420006060030354980394241920080001183c002d810b4071018020175410060b80c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 26415248 1250 26413998 26414021
    0x4050a0b2101140108030304022116140102150a090c0b040b0a0207060507020a061110060f06020c030f0c010c1a09030301090507051306140705030d05010503010c050a0c110103090b07020c0301 84
    0xf2003165140141251700c9120181c0f000c1e0048040d200110a083c00382c0310010140000c40d0210b03042c490912140c108900c3c0c540c02504140250345109911662000a440c10004c6203030704404103d0303d030104010010043d9008c21190f444c02c0c00c1000500d0b4281c80041c00003080505000b0355203035100d23080281032480343c0e08010300b40f01d4180540701c096259440381c103080e88c01900b0152071680003070888a02c0c0c40141016120032600303103c0085080c44420b0488400c80742150211480d026000d01090b0315101c0c81401190a58880c0e60007810759880343e40082c4069002d0340ca034858111002c6800c00d41c0030002c88203052140e20000041002c400759205150b03104401b0700d0070a041c4113030301710b440d00d903504507200340b01c00c000340b0203e14031540100030100d526190f44202100e99441c401c100d000c014120910a0700e10952905481307009246c001c100b1240d245080d640c804001c0070f11961181e885405100c0c0441c10140d4449103240003400107101d95004440b5900100070b8141444105429601d952181 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 26416498 1250 26415248 26415281
    0x30506090f04020103020a05090d0f02011d15070204060e04050105040c0605030403021c02030903071d010603020405060a030e01021306020109020306060303041809020411030c03011403060106090504050a0b2101 92
    0x10880000d100d40a07090b00240c0c24a00942d403424440400c607800c0c00340000040d8000b60702103003082044040028224586d1003071b2200504e800b00400e0019403215138060450b08200d41c01501c0e100c81d00a88010440035100031310000707810f501c0c3c00700300d0101c1d00111030494880c0c1d502c1040c4400e11004243c2c0100070701461810314558a4980d400039194440504001004401001d5411140d4024415525071540290071501d08983e10b410748071000100300c052a03403105040c1d0000c16034611a008984c02c3c0c8002420144ca07002188800b240181501d103080f1900b95420f00035600000a65101e01004184960010031035055030300405051140c0600800e20a0f4000c1208220030801024806c24800700b800d40011040403c1c00490042c1c80300041c03011105000204101500c1d0f0722001a43c10b903402c960030420507060341e60600d559406c080c0034000104042c181c040040345010b402c519400141102e002c00c805040c200481e441d00c084e01c11802c00ca583c041c2a000f0640340c00d1044840c0000100c48 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 26417748 1250 26416498 26416501
    0x20304081216050a05030403031b0203180f0117041e0c030203010b181812040602031306030605010203030a051807030803060f010201061410090308040603051006020c130e0c03190303050609 83
    0x8000c1e245101d40e0304c405080c80408030002d024103000e94450440c0304421110650007500400009450f83d101c501d00c95540b030740c3e90308501e8141c20413086c000d02d0240c040c2c451994500124242c84500180240100c03500c0444079098401d050316204800d000c6841002d5172000c0c5801c5104142c2900d10300d082c024000c0103480c6180c4011850000442c1d04034800c1801c03420341c25800c0740400d0a0024000d032000c40900000340c0060200d500000070038144030541d441680041d1525011000e0b64014442c0c180140d0003400811006205030b4401e0781c02c0a0030551035440f140f032000c442414541c4542c000d5072040004403c010741400c01010344034240400344002c1122908141d044103106190548060064848500d130000c0a401049044040d640010819865513501c0740300038080e100480d110304c00a0900100041e6003400002c0b0101503840c01440040384900803120b8400030028580c8a03441c0703109884800000d07441c28131440c1c92000740c48154020702080c3d401c1c042c041c0e4401500b01c50107040303281c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 26418998 1250 26417748 26417791
    0xd1e05060906060a0c080711030d08090303070f121a09060103060503190203010b1c030e0406080606091f0b090a0509040c03060b060d05010e06031c050403020616060203040812 77
    0xc44142c0e1065080b0f940c980c5030040c51004461100490b40010000100000c821083c0041c100b080840c19200b00c0490b803c85180043c216003500707007664542032960090010800d600d0040018900c802c082c0d142001041c1c48011422083d03945c0200380d007042501c00240d104081c240a801942c3c400b0017800c051080914020200c0d40e03a0b141101e5143d03140031604002c13404c6550039001384125060080c03800b400070b40c030501c4a00e00410080001c6001c038603040803860325401c2c18000c450032190b08201802c5160f43da5030900454240061207400d4420748010384030b0741c5c2800c290107030010f4548032405589030303030801051002c042c0d0301e07400480c49468035030f04000000340c1e81000030080e41d034084008201122410301003080d50142c1181084a54109400401c0001c201c01445210301d9084007111007009100b4010240d011070104001d0000d00d00b004107001504104009040840302d8212242100042d522018100c1e0400d0782c04480c1c0c00400120004c032402c1d0b10790301a4000302c03203091000e800320201 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 26420248 1250 26418998 26419009
    0x30105060a05040902041103091005010806060612090a17041403070f060513030b0a0b130504020a06111002030a0c020709020c0a020909010f0507030b030d0806030601030201030e10020d1e0506 84
    0xa00c00d0500c5940c1320041c4508540f61500b01480103100c40060b140c50381404514503440e006000f204e441603a1500b0000210306100294050041c80c02503c0540742c07a2200640c100d681c40024000c800e14410040000c0014440c441304581c4950802005a219420301c0f511243c502d5442624500c01e0707221010510a00000301541c00031a800f6041465842c0642c0214061081c020780c0064082e00b01003040050b2074041d80c000d4441c14800310b444820071300c2c2000582080340c1e410303070300650400d00c904020300c8942d00802512020301c1042e01228203d05c40c4550f42c0c070a03a8401ca034410790300c60300d4180c10712006804100c080040c01c8503907130a50800701031450990b501da00d6048064840c44203074004c01e00340c1c5820740c0603400f81011b0380020b00c018500001c001d0041c00c0c01200740d078024803422560302c4200344036914980c0140c40080142141e80d123146c0044015100b4142074050600031018100009006031004103c0c401403203c000c00c041d00101d0f8513407038818042d48844845d606140c20001143d840 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 26421498 1250 26420248 26420269
    0x4080c0f09010b09031219090b1305060a020f030c0c011107061403040804050d030206010f05040212010b1b160503071a0a030e07050d0b01030b010504020717070203011506030c020c03010506 83
    0x180300041391200160b400083c580600c2d140398104101c0700107a084101c0395001c0150442140603240d85420300c0c0c0d030700f55400451054a034003450100e01d0140500542c607048000703180340c6080c1d1040b11764400c089400d560640e400504041816400b041c081e1030656085002d03205140110005000400d01d0554080e098502c03408070500c3c052000000201088038038400da9010b060090b040c02c4a1548520b8040c0da50b19080c0108012038180e550001042e00d864001c44072070074505401c002490b4a4918040340c540c00c1705208a03080d505140030802101d01c10000c2d4140b1f007411014011100c0e00d410149405c02c50300341c000003010318000c00c4007100c140040c1e080b81c0030b040f9a407400081000354401100c0c00d1040c0341e0000d550100d250100c090600c502c12002c81d0580c0e0140c003681c00399980e10300420049202d41b0400400100305402c0c2c0c1d44440700b161020300000e90001d00041041c08407000800c0b000c80d226000311020036a00c0203210f0442d98104041d8845180603070007040070b0304081c400200001c0f01d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 26422748 1250 26421498 26421509
    0xc0a060902130c020309010806031f02070c03060e100b0604030b0103030e0a0315021809070c02090a0902040501090e0c01020a0201051e0f030a09031701050d110102030903100204080c0f0901 83
    0x49400300c00046445181034003500d070744a01c108000f10007040c0b100035220740c0a0703042c040c000747c00c0c0030100e500d52134007103041c1c60340c070b002c0711101070000400380116806074000d0350040c0c800138100100040401e40c2d80c001e0040841c01c0b24043d10344c1c40120b00c0c02c3c40456409040b0030b401080c09000500000303440c65a070606490b094200368400e07121144c0010743c1c00346a80c0000b000d080491407001e1100303a0b13540150856950341243c15201044920500c003109908944032400905400e030007001505191072100d07048801ea0001090b11140790b004030f429036000383e01480407a0750359030310001c1c05c103024480c0e03500380071091010341409443c1c1e4000030300600035181c0388010a1022244207034040c607000d0484251002c0704000702d440c0e15041c60101d00504d4075202c00d401150703440c1d100501c0d41d68000b0700e85043c0c44c00205104240031103503c46282000b5006207503815880100000b0105503020007030413428000b41c1e4401b50303940e401c003111203040ca441c21918901804182ca2409e440e50b88044800f0b056a4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 26423998 1250 26422748 26422751
    0x30207110f0301020c011407020f1203011202010c050609030315031b0f0103060503010e030408061021020418111201020a0509040f0b0901090c0905090702030d0c020106051903060608030c0a06 84
    0x80741440041e00a00c01c400d10b0010662a04000b400044442008070348503010319020f8130143c110890300640ca5840084403001c098800704014400802c100e81e00090b580e0040c54130040e4500141e070b850349024000d803440041544040308110602c0d0174003c060070b480c11300341d014003958007c044003181900d40000e6443c3c85040181560141d9911a40c81403008107801002404241021051140c51340d00c140141d82c802e020340000500c080781d42c24600c4084600352450041d100c081050003824940c1038034012a8443e80390183d60f107140d0300030341d680a00140181480510754a68808014400403e6612885640d005101610445810030240c944800040d200800c0d00e41c441c4000d08018900b0b89101c56020150900115101343e007070780105050100e42d00c86c8042e180c0c0750420401000d00803200c030001a4801c00003403094582940004c00406814000800d0554640740040e000402c1c1691000c0302c10902d00041080c40740c0707805643c00038000c65000c0d6241082e245485520384203100e00160003a03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 26425248 1250 26423998 26424019
    0x2030114040e1b0111010204030b011503200901050712020f010c0e030a0206030a060f060503100609030f061a0307080a11060405090c071103060403090311010f0503071b1e0209010603020711 83
    0x1364000c0d4030000d03c41c4541c200840d611510b91500584010003800365102051001c04002c10644c000c8c890700414441c820049000940016123014590303100302d9106041020500c041d60000316200e2558003034171884c1d0040d00e00c074900407024900b1541031f6102c0340c0820241804543d516200441c690340e0454042e50060741d00e039110489807020b041941e210010303c000701c400c0001c0a0b94080c0142d402500702d0711000002a0361034004840d000c0142c0405040810105800300001c2c11f560700c4070380720110152410107582da1000c00613042150f01d91101c282904412214020450921a2078000d560101e4040c1d0919040c54049080048002c104010096000560344240031540301d180c41f181d034005080b41e0b0306190900d00140801e54901c802c0b0307549041c4600c4840e140d03005005070000844103644660071582c43e103408442c825518205440c010b41018031500101e113140d02d6209507810725240d080c01841052051204103001644400708052052159000003004400803100444048030442c600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 26426498 1250 26425248 26425303
    0x120506070207030321140106020102030106140a09050603040201120603140106290901120c031b17240a080106060e0a0b04060c0204021c06090b10080f100e0a02030114040e 75
    0x5161b2100f800720791140e40000020510750540086050b02e500741e6480d810f00da0310389030002d500e014000300c61021508200003032000d42842e8001d1940940140350210541172201c7c0184119600d940090760303240310710345860b4180c900074040e640052207035410400e200030748505082000760805250b103040c10b40014014000d81c1c420080c0d0480300203134030000c00c40c0e503c1442000c0e00800c04102803000b1001160003a4a8840c040e207041406020154481001c90f507540d001034006031808020790406240340b00c2480c081d511400b07002d2015101003c00040c56a007049400381050140ea080b10b88600d801c401d090140349294401c0d10100e4410f410814a10402c40c40010064000e4650022003c6112000714001c1ea4081c0c0181e8215641c00d8010409620f855060002c028016032600c1d000c60700d0030000c02d0007000305110300c039170050110083c9401c098448801c0c00c41038400340ca02102940e0080014030400d80f000c130034075419040c100c070304000400e640c0c80360b5921046c4165100360804c4402114805 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 26427748 1250 26426498 26426501
    0x9050f120a0507080313090b060306040f0e01020d02070506100503031b010f1b030b010203040f0e09010209040c02070905070509010f0f02010b03030408010e06060603060303040e090307020901120506070207030321 93
    0x78500ea00009446902d51298450b81c0d407904200080510980d41410001d8001010b1040410305a40581407624555650003840044c14030100d40c2280343d90fa481c100c1d201c8a4003803024260b104022500541d5a0742c60342815441c0c00310252064084045214041002d9500081290494540d5500180000041c5000c0780c1c01458403400c0700c00b000e804d10a0300d4000c40001b850000411071691001c0080080103401207036a4026801349441d01310030b404050041006481100c1c5d44400032070300140c034001e0088041030681e03070507000d0940564801e000500510401d0b0203101c0d40011185415410325841c540000c12401c0b440002c1000e0082a1810310f032854803e4000d0034a11901404890f039440e65030202038028085500c412885010b20381c007080c500e10b0403200310703405150010015800c080c1044c08880030800003402d0600c0703d01c002c10000c4c0050301c40b008164002d11194070469505030103820030600304500240403a0441d0811142400002e420200709441540c00360441c040521031007009030f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 26428998 1250 26427748 26427763
    0x10810050a0515041e0510080615070f1703061c0506040803090a23010f0b03030a050c070f0e16050705070e0c07020a030606090e0a1203091712010905060109050f12 72
    0x202c000041154501c04100382c0c030704078400c5400587da010311410b80b2010403a001c0b45c1c282c2e42d01350301801d0030704030302c4003071600d0343c09085a5400340558800c86c0300681d03904001c40314005e12030740d0100d20220801586181070340318034902440219040b50b03c003840359101a100c4100500050000d4000700114040d10700402c41d003600290312400c3d07030b0f0403071451480e141792142004c1c4003d8601e42c24044540c42040d9180201100c80700068010b40c00c05002050a55880d0811503405080b80301e10300c00018030400314040c40b402000c100b003002e41d0031700700803040840084030818290181302c01008090009400011500121480b105000e11641c42c0c00402081610540102035442a00c2e04008400d2068950190303040310240f000412601820265482c1c9801840001130150340d1401044e80509000e80c2200110b0391040340f0010740744004488029842d0004240c00d000c15050200500c40000e076440750507088282400c01e400c145191000092602800300031740341c0601d440e0b66801260620400690 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 26430248 1250 26428998 26429009
    0xb0f010f020607080c25050106120203031207110601031a070807080a09060f110d0e06060d0b070c06020c0a02041d0703112b0b07080f01090b0315010b040302010810050a051504 77
    0x6141c178980e94601c11500c0e4002c0e4070183c0d240c8d442d0000014458502100c03107500c85034050061402d04500c48101c80268000030801410301c03080040c2002c1050b820700810780610300c0b80301154141c5101500d80740b01036031b0003003495060101c42003e000d499078214107025488009850b01149450342171a164026050003a078007051380d41442d80103503d90071081e000e4600503407021020082d21030b001d003400d1307624081034a13142d42288800210300c000c40c0100c2c0429902c980e45085c014110504d075a2010201d0b407044825004642004040c481185818016808011003052030032040249128500c1c2d1554181d10000b171400400c0301403401c2036140d200001ca28a0b1440320000070b0110b841640040900102400301c0e1030744031117400690841d0181001030f00903501250b40340c01b2a0308007203d20000384000c1102d16854850794a180c2030071220f44581c640640f0703140078440d40f00c52651002601c0200041c0c505011320541c0c140910140e180d410b10b01084500031a61302c4801e40c000c010a1310315100300d8108 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 26431498 1250 26430248 26430277
    0x105041e08031b0f0a08030414010e03030109090b060103050c04140d0602040e01181a010813050604030e0102070b16060903090306050c2a060f06060f0d0b0f010f020607080c 76
    0x4a103d83c1c2800c100102000c80c507105480484086085168032080007810090030304100b400481c01040030984a080120344010001030a034000280d45490341e00300b688940c1d1903544820844081043c02248145c00910070300b0180404e041c0504501c065008601a8032780c1e808150704860555500c036001c044501d600900115a120780707444050100030024060000d83e00c050b95070100c41400b00744a940b444801c02d203081c00700345078803c00443e0820806040080c500d160b10340c0d0382e4007040741440300d0350260303200380c5900f41005410030001e41040c01d586e0003220f441809000c0410880e90401400703590b0782e03020400141d09840c900e0203807401d0300c1c950806807000c3e20b8202001081d04042c8000c1c44681800943c600300015038203400d29079034015058800850700101d0100b0b601ca500301003920f4120800400207410900000c1c0380b040a5040401e40388080e50700d1700305d000854104444034112100f006c1c039181d80301e030001d00800303541d076600500000c04010590001600e04248031003690203404400d1071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 26432748 1250 26431498 26431507
    0xe06041a0c0d180618080708031803030f06030705030a0206031501110304030302070f050402030603031204020f0409050c090108030301030305040b18060d0b01090b040501171503010c02060a06140105041e0803 91
    0x1180003865500c60f400c9803c1c42c64400a1802600c3e4031406815071540101058640b0b0079a54a0803030540000c0c1201c41d006c42c00f01c41036581d0030070034405944103070390010303016600345809010035140c58032a6000c107020340c101c1c0c5908070140c0c0f01c0384c04036075220410b1000b020410041000417114001c0e12a4900c045020205005c000c0580c08180070044460102d10443e5085d11801080124401905c2051341544100225a040d41081003041d600c50300090401224151100208051380d495040490307458100829a0100e840d2802c2058090310a80c00210709641c19540c01030321714491402846110720010620400c4405100005c001c407076406001c0d130341c07a808483e0051001c3c010b06204140482c0e000300000c10040d2030350080d1811110140e42e012071114249050900c984030150100001a03c1c822070056182c40034050045009481d600030300c5946403c4051000700c45c00f6812426001004a04031150b50303038481d09650030f403504100141010240007811828a22913940f041945000215 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 26433998 1250 26432748 26432771
    0xb04080a0515100303080a2403140307020a06181d0603011a011409040b030a030c05060c0702010f050f07051b010311030408070b04020a090e0c040e06041a0c0d 70
    0x14800401442142250007182c000015821451400c50700c40d18810214241000400c1c4103408441c0c00070100e2000080340c204000501801e914070141050b0505180041003080281d812504056000e201c0301070350504e0010b5000680c0000c01c0e110b0401001f12400e03044a404200c5864617004040c00d05010301c280c0256252401c030008200e413114402d5290040030010752408182140c40350405945543c04000301c052084001d03080040f00f90781056641043c040e07a03483c10486606058000e880700c412100061070118544031008100040c0d02c0020f0022000503600410000388101950501645401800e10801d181e401410005001881901c00200c3c201d5103250515a651000303030f070140310340e4484d51095100e520060350000d201c081e0400000c1c000c60030740c1c00681c2d001480105100c400320341d0351107040160703030403143c0a09094200b000b00b00641d20380740c4540c0002501c10301c0a0001440c043d142c007a41d03280c418029101c8920014000340c0180303201011100b00110400c0100415000035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 26435248 1250 26433998 26434003
    0x90b06040816140102060402030d111002072001050c030306010f14030a0606080106031509020901020703081c06050a1404050a02090d05030712050f1b0102040902031302090a0506010210020c070b0408 87
    0x30b104480403c520b400c0d801c2100d5202054031481250098006e0501106103081203d640e000006104120301500080c01c801e0300840c00200081c502503075403803440d40ca4403c443c3c5800c605a0b01907a05029040180c031010050100c16268440001d080040c809007a02034180c403907843c0080d00e84000c503000410404100f000350b10620603a00c00c0e50320898030742c2e21104250120b680c0399210107000311580d201003014800c02d4005002d032200610541d02c1d0641c0c1c0c0c0e5542c60a60300880307100c8240034808111140d0104540c49010010b080827590142e0b09480c0c0700e01c3e000900d00d0b517528070303000b103407520001210540c1d16011942084400361480f841c0b001c041c1031072912500418000c480d4600850110350145103e10240d4240c41006032904c5d10705004501111001c102d29070014880355001d00c40010004203d1002c0e41c410300d00403105428050702403040000000d00140041d12061400301401590790340000e0360303c40110b01d1600140c2c3c0d026503012043c640301b00c5601c090f01540c0001008515540c1c003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 26436498 1250 26435248 26435293
    0x40f0b0705010b040203070221040902120106110c06040306050a09050303072105070f2709020309010c03091502180307260703030e010c1a0103030e0a0e060901090b060408 75
    0x1d44001c1090800080800c0140d00c410389401d40140d000240307030b1401c03540002c4000402543c0240c035603c0d0943d03c1c0ca5030016a00440494011000350030010002e01d90001c07407603035410300c250000d02060110a400520035009500014050a81e80e10015451441030741c004041d19030040210394491034242c00091181503c408051740e0300b0102c034030940c0e251001c1c1c000c1318010300e86502ea2485801e050101160905a0070900b058070241034040500c0c1d490000f040d01c805024055809692450070000c650b081d1445a04c06a040500e8409010085042880d290800c1c142c0864096503580000e840c245000040c4080c150b854000e80c500010142e600050581c017854030000e654804a400008a6842d110907100290200360b4100e01840c03250700c2800c0007000584507810003400c80300140350a040e6160700b604101e0106040303e880407003e18010f10450000d00d980600c1e109180340410105461510610034604800d4a564440c07807540c0d100000d83d00503040b85001c50300221806002c01c40c0320040b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 26437748 1250 26436498 26436503
    0x200f01020d0617070308030903220317030f011502100524060708040b07060612051e1603020d05011e14010f051c021903030804050f0313060c020105040f0b07 69
    0x2802c2d40001c2c52204460703a03560181105409080800d24645403c04560700042420b04640000c001118120301d44080307158920002c000b00d0513502d42145041c083c051008410341400100510810540d1880c55071040e0542c4d02031071000003580045c80051349407040c0c40c910b0903904c9003054200108800c1803941c0d104040c0d08401c50070000c80c40c04080c0805403181d40f40c040d25040c41000280480540d40b0700421303001e4898040002c099940ba0f03c1003207546a2604115819000602501030703414200f1807501c1c1180100008d0140a00020f00296480480b880002d00414540f101c8405208003035100c50300c20003038540182a00700705094224018940d56031130b845000100000465010f04c5c58000c90700b500d4000c0d0842e00c41075401a103c0d050410f200d002241e10400c0c0348504010080c6180c1890001c501c25155122641841d03e0440d08101c0350b0110501c86900074000034040d034420100c0c08045603601c3c01e0181c981070b00307400101c9151280380c20051401030034032800651147c41d070004054150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 26438854 1106 26437748 26437751
    0x3120c0405062803060f05090c0c01020a020a1511030402120a02040e0313080a030206040311010e06070504180b0a1a0408010c020601030b0c030402090403200f01020d 73
    0x600c0302188011040800f196802001c0c0456508034440e252400c0030b000950505200c8507403000d0f68420588100d007504007003001d51800d402181d0052281c100295a03401c80a81c0203599284292800c8560b01c0300204034462841d131510440000080c0d20220b145103440316002c01c10001822000102d042c01204001c5005941c0c0e80706512032601c041c4003440e240c503c204081e90768500c951780300745210b40001c19804006075000c2040c0703a0059150030302c00200030700e0020260040c05552841c1500344541814040d00907040b0000c0c008440c401501403217541c014440b401c0c02c0d2400c1e1404217400407200d08080c41501d616010a80070702d440750501e5410507030354001c0300782562212800400543c00040042c030034000c2c61017419034015050008240346081540c0442c54040000304003508214041c1300005054a908624810210780b0004842c101704d00a520039000303600030048012241e = true := by decide +kernel

theorem cover : BRFrame.Cov 26258998 26438854 := by
  have h0 := BRFrame.cov_init 26258998
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26258998 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 26258998 ≤ n) (h2 : n < 26438854) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
