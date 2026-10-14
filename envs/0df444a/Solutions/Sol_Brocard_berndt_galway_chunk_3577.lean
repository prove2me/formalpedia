-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3577
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:04:01.214884+00:00
-- url     : https://prove2.me/submissions/d404dcab-fd86-4f41-897a-3b6f14e3d86f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 643165467 ≤ n < 643345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 643166717 1250 643165467 643165493
    0x8030408060415020c010207240902030304150c060c180f0807090c030b040905010f06080a05030313050304032109080c09070e06071a09070b0705030904020313021c0c12 74
    0x3c20079070380608084940c8840c0d411140105001d2000b150703904a83c0c03a0074505013410f4000354010840200380580700414030701690a68036801800307107213042d040a851200b0742a048007000b0801007001c1440002400500c0343d03006030321407a103640a5840d0645010021818107400c442912028440308102c450f100050780130075103821030804944840d21394012001049001041640b05e4146072020f4140a0107500801000c1c691003828809030b502c0d80c281c1da03a20410810010309543c020000141502c440301c1d03415401600c260103030b81c5425a42d44940b2030440814100d11104010701c014103210036005000362000742000340242c4114201d5030009000501c1c010003800034040c25000782a480d954400450f0203027544a02c40441002e10303e010020003290440d0034402c0c42c812603c0c003050a515031030541d140c6c50350110045140486d10014400a90001741ca900000401440d02000580d9058101410603401001e4452240403d0400e0900000180d00004c800d6000e680c8500101f849840380b10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 643167967 1250 643166717 643166723
    0x110714062a0702092d010501020d11420114042f191e0302092124060a0e1b1305030a0f0c060212220305030313050601080304080604 58
    0x700300380e038912980c045c036400d4248444894016803000d4110b022950350301d09069840a90031100754040034101521542c103815003030b1084c0d40c0840104446800c0c0000e20800694555582c000001030028015a005000b03890091600401c1e100501c070845021444000a2030222424000c02c1c1c1b1542080058260000c007482d11140004006401030080c1411151b1032283c400700c008000e0b18010005000c2a1b06040c0815802101d41400340814402d0090750507821000306031408840400400700350101d150414034009005016000519241700d255411641602800c075100b1132401a007000b5060b0300940080c0baa000400d4244000047c200d0344585903450b0b0031106070360b00c80010103641081507455008507030600c10440c280007004400e10064450030303c40e0420b4103206840300c800740d813280403403088400e0080301031144035001401c0140c03c1491003502d80084c41d12075280e40710207055500444010407044030500204c810804104007540c010200c04c006141454241350407030b901da44000d8409 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 643169217 1250 643167967 643167979
    0x5070b180c09010906030b0a0501360212011e1a0f121008100606051c0b0a03060b1c11010e0118150e0108060d06110714062a0702 57
    0x18001100c0c003005421480e541c01400802e0303d42c1e444040c6000350005000032240d41012001041e09850a0f01413541070b40d0000380d55126409515001c04d103842140d030042c018503210f80031804a1106144028202c02100c82039030b0b103071981005a40d10506180d14120801c107038000c5410003101c50082c2680414106a0402664907900741c52a200c2c45c0c0940c80540400d0030850090021100c901095401103c00d00829104a002c4810412084582c58400e2201141040040e0443e07202e001401110704204010001503040410300401c00036049508110b54035680c420612545180c01d00410074411051140040052096036034140c001c507200d01aa4148010889100040d80c0a01d14000299aa00700204031195590b8200300046203100d410fa404120341d0300700e043c1194428044140f20301c0d000351000b10781498aa0740c2c3ca005092802140c1c070500342c00e02425002034407501442e85940900030042c4054200741c0c1c0022500440c2c0166010707800840144c4105100f43d14042c1c825043e011542 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 643170467 1250 643169217 643169251
    0x1933021501090507111902030d02150606070303020f130302010e0a0501020705130e0f03180d0206070f0302031b0a020a08030327010b09160906020d050d0e011b0206010603050705070b 80
    0x405d582072400c020140d001c0b030245603c1103160700d1070030142d0046207000702c088409070102d091040c3e85900f030b0545809040403211000403150309182c0700410442d03110f442c00500d01501c4010094490300300b1301c2c1030000f00080210400c155a40003c84156000c01240c50140541c60b003c0080d41e210790f41d2003000d02812070080e0381609204541c0c095148500101c0950707101000c4020456265400101e520700103d07000201d205c040d0502ca00940c030340c158083c001034900710540d100e0790841d4040c81412000c5220030032182000804103040380102500d45c00003018903800500c1046841551500903000c580d0040c410042c1706040c1d407a590741001c403810340b144403000080b509240500103c501c40e6401041d01402d101030704080d10040f000522040d9298074030342ea103800c03041780c0b117038034150202c00006c20a11204421481c01c1d84040e4640c000c1c10000640c6c681c0c1c401d060301e0000800060400540c001c240100911505070044c55408480741ca000da10340b2042d5aa0900028409092a00c0b00c03429009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 643171717 1250 643170467 643170481
    0x2010c0e2d0a05040903080a05011e05092509050102061e0117121809060a03150c030e101409030901140a0c06050c0309010f02090a030219330215010905 67
    0x21411010340f40180003031058142c05c2c10040d100c01030650740d41428a1030300000164580c1c045a4902804895214501c002c6c2d14000401020850240444002e054041d00303485030317400b0800d0102c0749003181d520b42861003858007002909005004080412201004094a4180c1500c405140c1503d1544021400a20810f801d40d803420400031002c0368170070000244240f41100b0031203003801c03d103000c4480800d680c0e220014001450744c1448000d100381030081c40400303488000c1d00881407a00c1c19180002d90380d40038101d000e28040454100c500c440e5910748620790040104185503034040c80b44001545400e034620300007018904403001047c902c5101141c100d114611810401c040141c01503002c0c040b90415100c68031096106613040f6a0961800e1001443c10741c090003540c05c1d007400100500d41240c030b19020f0140000b200785200b21518a101000f2980a0301180c0e0560a0b0000d41103460500841ca2005190384d05880183e0302907601ca000c40c0c2480410354a00a4151200e0010200d80e5840e0700c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 643172967 1250 643171717 643171729
    0x50c070f0810140f07200c0a060c0210080919150c1b121124070e130b0d08030403020105090115030209180304120605090c09040c150c060c02010c0e2d 66
    0x5c00c468122040341c10f0403a140410009551f100d2502c1140c64044450b5034450a5801094a8500a400c11900f152a40d10746005050701940b1140c01010760b9294613485602c0e0202100c41d6074102e403107a039020b02d681016801b030300c6005c43c0c00789c043c1000e01d4030083c2409032840125604100500b10301c85c00d40ba6220081c490b070780102c02e400d211412680c3c403403891600002842c4000c0c60a80140e07000c500010b11640c800c800c0810105006490303442240440718100d000741110130f420580100070810400c001440c140001c43c0309502036400059103042610a039405c0d11702c8145e503200702c0302c01c402050026136120002503030800c82c0410342000e02480761142074294040c030b40c807009070010500302c1b5000384030350703604818490001c00f0103a80c41c0c105060100142000180c0700030300810f824000c18801d4902c100d030302441d0090745050900300340c100c0d0342c4ca070700640d40c2c1c0307084410043c2d460b004046881c0750000c440100c0800c0031220544047c202130300da220200c000e8248042d540c0c8550036060f41e542c40704 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 643174217 1250 643172967 643172987
    0x1006080f061305040b090f010605100309050a02030a080304050d0f08061201240303080912043f0b060d0302100b010e060a230403080901050a050c070f0810140f07 71
    0x40380c2c10b00c00c0e071410b402c00342c0002c13008032115070719409040d0054040307a07410311840054070401002080c092a13004130072402800b981c0030031102e80c4500380c0d034100965070801400d40000e00c1641656500e1902e07241450800694003111828030584200540c58103030020182c0394444801d0f81c00754881c3c00c2042425015040340c101c010360b40001b611503219944130310300c1a002964000d1b220742c803458a031700c00090765401350440c548420b0070040c413040c001d00c2041d45001c114060401540450328456070422840f80e110142042400e1909901103805c01c4441421180c0c41b203c110307250000b00c2e4054401035214070300c8801000d1003d5441490b490700380e01a010001d80000094512900c84104020180c0030400e405e031403880151400c1c0b1030001c030648003002c480503607034410041801c00c0000720055899030806400141401010b000703c4400e64003c004100081007460390f00c0c26007a2030321114a050000d0507070603d203c0c5007050b40c0000005100400301d90050170fa840c43d001240e0710590111806281 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 643175467 1250 643174217 643174249
    0x30f1606060305030307020d1106130c170312090d09090e07031e032003040605031305010c090905061206040809180a0b0a1706150f0a030308040b1006080f06 69
    0x1030716401000f40300002000c4c0d0f00c2501d0940072203080b00c0305203c0c2510a00202d0404480c0d0380d0103200013803000180404c0d011009403240702003c1c540e036101e002100d040c0590240003940faa101107400e02c00d0804c0c0300c02403600700c040703c00030380340703511242c01d000340350803182d0285103500c0e0749980d030502a4110410901c4d0007950404101c411300d035000d0550600480c03c0481c00d90004400b4102d01d00c00c196129480b01d103811001c0000c47c83c040c5401010384040d00010800c0040345180c0e1a200007103030003806030404030b04c041d95984001a0518030341004540000c1c0c4003d001700c1000b90030000c1c0b0240000c04070b4005400c04022074a40c0d181e41c0c00202940c407042c41c1100407020407400d100e412000c54000301c0c0501011500955107075150140100300540c001400102607000e10040342e1807941c1240781000200c40640b032000000d081d003011488810595100b200001c0c2c00808100c2070203820584907800121002200a0301803800c00010104032010b00841003003038a09002c40c240b90340d10303c481c001c4288 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 643176717 1250 643175467 643175471
    0x30e0c06070804080f070e1306060e090a05010f02030c0d0e03040909210c0c090c0e030706020312060d020901210f030306030204151a09042304050d050705030f1606 72
    0xd40b4900b40d45240c00503c101e9045100740652804400e40215456098400f1100d690030240d0303e9003130500f148894000c00340c503115550f19020940c0d080841d109445580c0100c000d0203800001d1408508441280c800b040e012413040c410321039608010b404a45901142d0500416005000c0c2e847e641140b11310f07440612018605240030003084158291707416440034a000d03852810800e19011b5400c4106021300070034418141e0810b01414480ea40807036107900c2d0615000e0301e1041c003800403925114682d04910056070010504070b000d00c40307180351564000c0044e10082125030303880e03001c03d685510600400000c40394081200300607500030548000c02503000000c1d04d000035401e04000d8024107450200360701450900000b103084c5664001c0c2c0790308680800c00480f44101d84c0400704001600000d410756809521004141c00b03841c4401c050001c040c00c90210452107050919080b4602800a1080c81c2800301c14000760004c07a00100030b40300040140c0040300d80c0d840044410401c245245000144128 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 643177967 1250 643176717 643176727
    0x15010e1201180f03020d02010203060105040509071b0b090c0d12140d15142e050c010906060501090e0114040908120a050703060f0e04020d0602040e070f090f15030e0c06 74
    0x83c40319103d1200e036000781c00303484403a407010000728281d01c021249540440c10821040040b41064603120b6441001e41c900f014140d24030f01081010000b8042060707500c07900c400c0501c05640006d00c14550002401c0b0343d0f44c00c100c0440d65075000100340c1848440d080c000c3c14182100101e90030f01c1101c41d40150481d04001401009846c102c641465009000400302c402c8100260f40c00c1005c00100441c6071152000b1010013810540c002c010300c4400140c0c03c01406020f001c500702c030b0034003031004003520410020540d00c0c202400100f180e12143c0c0814107149101c40104041803040c542200090015203001c181d81030b45041c1000944500e8080036428241d03081040105590782e07000c2c0740541260b65051100365520b0600400c502e11900680303222940740c90100e40145480390f080590309102c0c02c400350805603a081d0040751070101f100c1c02c4c8041403400f041051101d502840c00b42c0680314601c603c000300380c1011a2200208003c035506000c1c9a501c03608181008420001c021500704000c4c07031a6650 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 643179217 1250 643177967 643177973
    0x20a02010e0a050709060501080106020c0d03022104090f02031021020d05100b03070501050904020d15120b09150c160503030702010608070e04080f0d0b2715010e120118 74
    0x3204d10740704541e2164074200010905610499402c4d040302e9030755000f440d01403e440204050b00003040021000d40c404c07201003034085001105041c0c5900d0130780300d0340e0f0b80341c0e03183c0f000320700a4808408000d20343c1c0d8410410422000f018886950a0b1100d80301c290f8101080340000000015040c9000b03544001c503004c646003040300005240f0000620017a081c0b107270f4101481455a5200305000c0c0c6404a076041c0580c0070242065406010400100c070008580400a04944101102103410440f810721040b0305440c2032102d20741c6110b0700040c0b07440040168001504c0d2911b00d8450181c8880c4900000081d03081c0000d10742c3e120b0000807600402508d42d24103000700d01034024101ca2107031040d60b000b029400101801c403040014850780d0072181e00d500d80600c59404407015888400c82003815583d80500f42c0c002c4c2c41e48420070084840515107c468840d10b004100420302d00284520301091561030300c82601c1c4da10142c214401e031b005580410302d803400c1000c0d06000d13240d0010b0038000c120f030403d004814 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 643180467 1250 643179217 643179223
    0x2240103021825030204090f0c1d091302030c031c35040c0902040f0f050619030507031d070302190e060d031707120b0307060c06020a02010e0a05 64
    0x120307442210040b02e00241c0b40100400c007402107514202c0028030841944880c500d09008080d031501c0392400600d8140c541c003800003140c0841e001e882040d6920440b0340d00d0141c008155078001c410021421003a90003030781c0003450b43c0d8401480300190000052001003151810420210000d80040680b0880300341000c000c0f08000105051400060308030707010084079140032085402e0100c411040303400380c0c580030108a075101000b03841150a000c510400281c0e1800350710190020740259450591138030300d0080321520703100701030b0003080c4181800c002e484544d02c0441c4000b03100007101e0401203042d17075403900d068008124403020711480a1f140e4480450720440480e414061364030846031036030380c0200c090030b030045040c03903009200c1074450740700c003180c0c4d14a42920460030702480707841d058604c842d480e1406c45100c0c5d0709690003000300b400030b44502c031094280d0191b16910b00081c1d00405505150401c020b1501180c16009480c0c80ea002031b032044018402c0d00004044a00724040340c24480700d0349480c6a03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 643181717 1250 643180467 643180469
    0xa05040516080a0905030414120f03360409151a040e030901081b040b0a020c03010605061c0b12010204081c020703230724020705040c0519022401 64
    0x51008400190903144034400c41345100d802000850401d8202002e4070301c01503c056040da030000c800c84001494400404c1f071003544500c82e0020311b40b00d47c2030010424040e02c8104106542c4401c1304140d40d80c0070360414040030010011503003c506c050140c20044548001e050300719a2103070821103110400b0721048071031082c1c5c540503079080105c5040c0c0381099031280112080940020001c8001c50584a03480d41c000280100d004600d034178099440d80c480030313103030b010078648401f43c3c00a50403c41c00c2d00d020311440f070080c68240d4200e0701d064901a580366108012865150074143e46005805540d124101340d44005100b0f070008550381c030f413945081d070354510070b501401449055051003500d11a20102e1098116a4000050480a46407000b42c0e810155111190310f03039440f034040001503111070340b00c01e5901d051103071742d2036107054189950090a16080307410182c0114148201903140c2036000007210729164015080c03091400750000304a05140303800340070144008191100e81f5946000c411618 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 643182967 1250 643181717 643181761
    0xa0902060d02040305060a14070807140d090201020613080f130905090604142e090f240e030405040e030408060c03010e0106021f18140303100e040c050f0a050405 71
    0x86c4666407400741034020f80790b03880901030b03a10038030102240715140143d912a030002402c0c28400b02d04090b20501c0c5035070b42c02401720003c115449101800555070140601504900458024854070032251036125070362140901071411801e0020b080241800e030b05580c030000c0c1100c0303c81072002e0b050041060b9a00d480640e01a1444240c0c1d508605072107000280380ca01800c40700d107962010a0901e160700603464200d074090003405460f80b50741000150406202c4030040d01c40c0a4a8804034118040440c621103240a5070940f14a4002480d50030300000050320100d580448021602c00362030b403100f50641c0281d40c451075152080c0010321842406034800342d41038800d8180c440605a0365080c04076a940d241d9143d01041c043c0b004080c52666180c0c0e00001c9012150304501003402c69544e84041d520719007a01140c40682010092020114421130b45500408445064620a0801d915400e0a005980c0b04042c410b040d0201c140e00c42d91100c1074000000d10740103100300141d00d4059964041204d03004652 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 643184217 1250 643182967 643182973
    0xf1101020a0b0f0a110a0207060309030905100c030e120703140703080a110c09070c1424160305101502120a0e03210d0b04020408030c0d090605040e0a050a0902060d02040305 76
    0x103178403020500c0341502c81d03400056004207201443e0920a07801010640d82c103408202615402160b9525094494644c08010350388502c007540140c10300a00c40481c0c80c5580d8407d450100540c01c51010000315001901e0300700c000e8044082c60444880e03e40460b45e4001000b0160101d00045440d0308511910642c95600c01a11510005a020840d406d10103c0d00240826030000034503010810482c042c090f035920540803600030105c248007100c05441c10710b401d0301c2000075900401c0b190054440c034460005c1941d050030320250901595200f0004402d00440018001c02c14843c07504503c20002c02e5840b40880c10060f546281003080204040c4a021046019214010300c2e40307050813205110404400ca0484d0044c2055841d000410242c0440a201e81d8025003d03c4089000350013400140400c40840008040a000d14800a0000340e11640316205214040c8010411b030b400f0702c200d5a510150300940024035681340d401c064020850344101a4000901080845050105a0040c020340b4014021 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 643185467 1250 643184217 643184231
    0x206031f0305150f19090303090204020409021b0a08030103200a060f030c090b0324041515111005421c0305030403170405030414030a0f1101020a0b0f0a 67
    0x107000f401c54145c07010051243c40d1740000c8007806080d402021500d11a14010841030660b40005013680c216400110540380c1c0001c83c03110342e152000c0c16051180c1180043c00c03e00c1307010303103079100e1602051001400282c0c02442d054211071003251750100251000f4030065a407511004028415118640428013091402a01101d95800f03505240c0c00c0310b00e880e00040c5555a1000c142070412010380c080140c50701d241c0c030a000c0036602d40c001d2200c2a03010446070300019192604800c030140c06180b0850a02c2008080030340e90703003400704100d5668400b0100c00300c1c0c541c42d465100e25010b03800444403017030090400c0c442100c10f16486050060354070f44c10444c001300d00c07400007008031501e005016070026000c1261154000f80c00f801c05594001d01038200030100ca000d0090816a0200440d000c84250700001818030040d120300c07419070680207054004080c60307071280d56028600f0141c8100a0301410351301c0f0b0201c000f6803080040f1000f8961000c096145403c0008180241220a51b0071364041c07070030060 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 643186717 1250 643185467 643185481
    0x1e17010501030209090a11150d02030a2f0307080c2a07060f0801050d2f011b03050d0510050d0b060f01020d0c0b0712060e04030e040b0d0206031f030515 67
    0x10300b849006401406110507801c0882c1089002d24010503103e8000e01c0c22710000c3d42d041000d00c0950303c1051382002c04038401400044980c152001e1036440e903044002c5880c0700d0139041c0810280d83c0d1083c10707428194400d0312403d501c40400d00071071001900300340103800100500321840417005509500030040384c60850b00c4030070a40d054049615886d0024941000402c45440c101101c0300300c2c140140c5441c90440440b08207551500243c2030305e0b041103c210b40c9040c0780d65910481d0601880c0006a462144014a5070010242d105100c006008180c5800c04901c48200c01c003100f000903d002800c80340114201e14011450004c1111000d200b00300c000704101b00c1b94000308191052070015621180e8002c03a40e47d03060014040581100704102d0004070420740350480740f040001410143e00d04000c240b61503e0014241215400c2860055080c20b94022003500c1d0705040f080500c0d41150303d02c0c1c50f40d46802c0c00300c44144400714410000b60b4512400401c0c011302040700000d84e001300b102d000d50b964440c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 643187967 1250 643186717 643186723
    0x1c0204050d053f0f0c0d080412090f0504090204112101120b130f0503030c070b06040e19170414130207120804020f03070605130801060506041e1701050103020909 71
    0x2025010f1010b180c0c2c40590445080382009100f4658001011814800310303203010761410215003501d8004c0b0707410788240028400990701e0310035000c80500c3c0c00c03441581803084e010000c6500b441203a0003241c13502450811580c540d0048100800035411090b118059440320b100345149414204500100100000c180b42c00540b4545aa02c0c4c0c0210f0300c00311b10b4072001008405420340c040d095a030403103180561000541c0c284020750140709803204540d02c684403420210500c4502812031480b440c40c00074034914598012030605410031100c02d900488200b207051400d11588039158000440400103000f1580b140c180308840b45543c019108a10b9540581d5054012440303240e501900302003c00c0440c00716140302d01c01c1c1079400740c405040f40c40c070b4002d400c0c08a443c0c00d140c3e0f04240041140403440059003928524048010403013040240080362601c1c020824030b1180d805540242586040f02081a45002c0401401007200510220000c1c1c2140d0080c1e0081c002170000720702c40c04400b000b085040b6000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 643189217 1250 643187967 643188043
    0x525090308040506130b1809060d0b0103080a0e190e070c0b040b060a090905060f1608040b06061b010209030115051f0e0d0b04020906030a081c0204050d05 68
    0x100c80c0700c42c40d20f810b080820405400c0508038010100c50940e0106407808008054160040504222100116441c00300645888010a03041c050800341c0c0c1041c02003030818141904494204803d00e548420400080702c10241082c50305402540303d9070b10b940901d48002946084400303a8480d0079040d114400304903119003020101601d000000c50208001c038032200740082d00000003c1c009403042d80d960500409aa049250507121500300104100c190780003154100e070f20103400000c82401e0000844090300c1003101030800b40c4030407203180015143c2e4442e1000c84205881440024100250814545010b94401c40710240254284405080d0400c00c8448100c20ba40006000214a602028103a800f105485840a08104050305601a561200f031115400d181c000c20f0005000e00d86801804040b50014080034042c0d8031607000e04004c200190140c818115460211810306841380c2c112030060f0140d90032071540b10715802000d03400c00c100050300300551a414140040722080310042c8480d08415 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 643190467 1250 643189217 643189223
    0x1103010503011a060403080a05210f010e060d0f110616031206180b0d0624050d030e0d08040312090501020f01060803040b070807060603030504060809011514011205250903 75
    0x520086c40015940400b504482c034451404074100b1100c20100071000c004480c541e41030440400c24802490b4480d02d50502401d014000c03644582495004500c4001403008081c0030031400240044c1000701500701c22008200040c4410340310305016962800700484d40c001107010580d16003080010800c00d014081c1110788402d08207104007d05200700015101c0061540d034044110401d04002a10500c11b01200701000c641c40000940141d074050309284554001c1071040b2036504809002991044080311091300a41e400500240c8920301410b61307004540004005042e058121102603a00060000864000341c1c00c4560906404006501320341940c0a50351168004020600502183c440207010310f85c80b90721120700d4007440303444d03400490740c0f02c4e00100c0020f02d0000d0708000c45540b1582854000d2400d100801c8000e2015203042d036012403900c92540e208400c0c44011183d62301940405408084001c1d042c407540c80d044640c805c3d038220720710400e54850744440540040b80c0c401d960f4141520342c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 643191717 1250 643190467 643190479
    0x1513080610090e0a03030c021f0b040c0518060703050f030916120f060e120d02040617090d030b0103090b1608010f0f0b070206160b07030605040504260405041103010503011a 76
    0x91245c604030b0160264800b400c041d0f2151184c0a4500a85904100510220000006400710300d1201b0001940e000c0301000302040f00511448182401004d52100c4180040700d0440e0b440c2d4044c60141c49032f020355602d0b42c00044000c0f082020403c03002c2846a607003d406004c548106449803074401f800100e07841c0103481580001030260004403194031900c040c4840c20129038001c00203400301c3c0c201d503005062400c1c0c0c0303503000f103400c0110682164150310420310303107210315900d464a120540d0ba11440810003408058841c4640c0c52586d019600c6204160341007a0080750a1030550000641400040c0010b400150030100020380030f04488005002c0c1d81070f8140701100f0629000c01c10106170051681660301010401c60040440701454807020010b100f10264845450161405000c80302d103907210a000e1801c0104000016079070107190440f54070b0020004d03c002c018054281840d001d150130040d00103180c0135031159121040b0010354100c034811002401b4004405a40100140002c410035070001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 643192967 1250 643191717 643191733
    0x30f060605041805061207061e1e0f0507020a08010e1203091902030304120b160309030c02061308062a070b0f04031115041a010e061513080610090e 65
    0x761584d040f50b50444c01c028600202c218440d446070b4180000765005501007403001c05000c61003062103400b4031404446090062001d5910b49c0e10702e02c00000c91080b08200480602c000c941c440c001c000351550950050081c5044a48030148a802040d400d10720540a1160084001140002d141124403070a0b5040103000036090089034003c140e202c85d08120780c540418000451405124184145114000c003501c6240e42808030040500458100843c800c05003080045401f00e90080d2501c3c0d46181d068441960320040c42c50381d000300f40102d1304540c900c2d01404061000300700001c0c180078410600001c0070400d000d040740000c1d4130380c4030b0200000c028011440000e11080024020580e2150283c2000040d00700e00c2001d0f2401d00c008800006101c1c00075005000138821442081a16170080e45080b400550402180110b0b80d10000c210510a01107039004450030b280d080103031500980c1d0814469002501c5004403611600211000070b1034902c82800014004000c0c00340d404011582d1010701005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 643194217 1250 643192967 643193009
    0x20604050d060e10050f010821030a0e0703080d0627050c0d020c0d090902031b09030c0a030c03140d0c060b010e0d1a0c040506090d050c10030f06060504 67
    0x900d5018100742c68007507440c1e60000c80c425041c030009010500c19030303002460f403a00380e0b0324070390404040e0408000c50b80070720b405186840d5000c0d221083c00e07140c0b040301910f81d52901850b001400031901c0710070f101d006099001040100c4140905204102c002003403005544a514070705860301c000803600c8071148802894110300316543c0c800d607000104207095034a0030058814080a0b6030010010400316800031808619056104a194024103500d46040d40345041901384800b162200c9512a81c460800141034a0150f80400c417440307880c000500380e111013079502e05281c1c51003c0a44401d030307002e05442020700504000484c001100c0c141c6074581d00b081030100d403a0000248032440005050081d8405011800e03641d40f402502e1007482031381d0300150514501c100389001003010707001c0d1060305030912081c402507848070305031403802c0c8084e01c330090f040300c40b41071061900c0280000c081d04a0100f184000c03540c3d030306030000210740c2c10081042c40150b5035030074100c9061099200b23607540300003056425151 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 643195467 1250 643194217 643194229
    0x90b060903070b07081e030402030601050d0f02090c13091a030a0510020f09040203160216051c170a0c050f06060607030c0203010b03010507030c020c0405060d0807081615140402060405 81
    0x46240180717445414143c3c000368443d0104000f1900140007036001c02048111b107020484180505816542441d468072035507a13000000911a60007482800700c100050b1854003944191040c84003900307800b2410aaa907111704000340080d0014182c2200c0303c02c1030000714280094404192075010707005007002288410b80c04025082180f10a0205c4410010400640c0d0b032800918054080d901c040300c151486004041c1c60003400c0040d0b4545400702030810010b0340d4a410512060003c510242c41e400440792403c0f0b01680301c107140020080001003049416180d10066201a240c4a1412a80c007045c403031046640c0d03014110350980e8480e40c2005030030002441103c1900e4454405000031480c100c0b000002820b580c030481d40200040c0e03507a15000f58641c1d040001d0380c0324070001d840800c6581000800706140601d60705024200406c005085400c0103906022281c20080308d00344807180306d400b45481e03550510410701c0808464240055030060881c45441207001c1c60f4002c1131285011314100038094 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 643196717 1250 643195467 643195477
    0x2120d0c0816021005041e081b0d060e010e0d08011503020a0201090b2e0506090d020111060906010f170c0f01090b0f090a0f080303041b0816090b060903070b 69
    0x11a1406004000d001601d803c0044c41d68107180b43c4400b42c90301d0400551150312a51400d40800e501120740c010000500e02240b40028658590341c2108041c0105002c03c00d09070004600508140ca4841e1b1013503004411342c0803141c030f0f00e2450b090310b20001c2e90400845041e0000c1c002c400381c0811005e00c1810890081e4020f094490744ca000205600301203440754500d0407021640c0000100c0c81c0592801d0000c0c40c082c0c100100710180101a503041c1c2480081130803405160845030084d11007440c03c0080d6030242d403c10043c000381100320340d060b240c2082e1941e110340e4284114010801000400b00f80d260b104441b459902c002c4400418008420204012000c7e00340c540c42da052102010020601a5907038004040070355400d400b56958410020520048030380a50040030512100ca9051100b1780010049a4000790802c9641d50311250140d04402e10b120b8960001c2d50520403e405c460380158990b9140382220b03100c52003046103084d05030501400c1d210352100e02d42d02d504100c0c000d1150302c850700d011b06 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 643197967 1250 643196717 643196737
    0xf0601091802180907050103150b030a0b06030403030e152a0c0f0a1e03020a030305090c090a0c0306051905010302071407080f0c03030f04091e0c0c02120d0c08 70
    0x1241441d019004038480d0307201c0303034a1075080200e09810481000810004500100030a21f42001f0240c00140c40807a9451240501e60300f0210000104400480c01c1d0010801d40d000240301c255213080c030f0301c1d02030014a091243d007030b01c07030080041c0d08a03205103803103525100380c0340c00c2851280c0d41e40c19254450008501c04081100c982d003031051176140d200400494200a030f080c00200f2000d0040d0900d07240e20640d04001c0e0f88603040502c010300c00250701103030b4070b0080d0341c0c14240824161503c80309542401e4a8801136600708410070100500440341d60484101c400d60754408000300750f1502c00f8002c0c25a41c14003544545514204100406d521030b0b801404114000c2c1c0c0b060040307a42008902d424944254400c540c0c0d42d2101d00241d420304401d0002c0840c01408600840c81c0602100300034002c9e000754898138090a6aa14400004c04052840c10b101e800310001d04129044141002415010590500768020300311380c0c20a21030180002013490380c03c100381d140d09010039001e03580c41c41c243e40b02000307003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 643199217 1250 643197967 643198001
    0x20030a020f0c0d0f020603192d05011401050307050d110d0506030601031713090603050c09160801090c1809051914040f020111030d050115030b0d0311011401030f03020606030f060109 80
    0x8510358030441c03080c0c804083e002751820001640b1481540c083c21500318008003028906001040200002d0703901c030b0052503081c200681c490340c0311141a0341600418084886242c20300010b0410b50480d20300500b54501c58000400244e11040d044c56030310303042404002d003542d04468480400e684203e0240c103290168414904c80c42e500c8000900654a20303602c21200750b8400c41e840c52452818060603907004100040d050490b0b099500c004052030818407500c440b155a41e09400021803240058601e110346240d00c80120380d603035040c41001440200c1d0410344055400c03000c030a48203030a0054000952020800e0b40740c540380c0b51510603d40300000c80484c14405400d80e9045450810b00140070f01d106100c000207a03541c07400d080050b01024041c0c007182014a41020032400c4c2d61010704070030100360945481c4002c1264164003d004242110700d2660340c210703c1d4000801c228858202804261180d400d0341c1c59921007005050b6205e1040b658002c0a411160050151141c00d07484a07006c28900c50708 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 643200467 1250 643199217 643199251
    0x20a0903170403050a0f05010b0907090303140f0a0806040f020f09040b03150f0907050a0501050316090f080a15020333040903031401060f090620030a020f0c0d0f020603 74
    0x750501c5c04040502c1111395440005900c024444e003889101445a020350300800b0916280c00002d141400c0c5000c001c003480322000114010503126000d5a5002d03030b00b5010190b81e6002030f40060f1100c0c00840c1c10521079418a00b2501e0b00940c80d00a031184000312019003400d00203000304000181c500064803a405d0b1060001c00078504a0b01c820031405030180034a007110506045003503d050030025000240a0800d580c010081d07070768000c2c02c40e0350050760848036014450240b02c0480340703042a54018006154180008642c01d8008a0a5010548180d0441218002c5075203608142d0004035003c00c0b1030698114881320004250803140d400d142982c989100f0945040002812604030074001d0b00080e07514110050304810307907400140507020b5810448412400307080010000c4010b4061042004100c0c0048a16030040c03215011900ea005010f030b0742c4a09425030029501c4130440e0804000d84661000d002c206d00b09a003803c0c0380b0907001005d50100e85159001c0c01403652016040d1418001d16501c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 643201717 1250 643200467 643200473
    0x9021005043f08130e0f070309050a0506011d1605040302010f0c060f1a09010503100e070506071202060f06034c0b04111e13080709050703020a0903170403 68
    0x40201258440d681c50313a00d80001540c1c62034049080c1d0029454454080244280c041c10011216400301680ca804140b202c804d00d4018200f05041800030040e01c115000490038020f44014080303610b200802c0341d00c50781d0707503181a070f0704180c00c1c0072107100451002c000510165214013800ea007102050f051041002c08030f43d45060403101c040c008a2103059903000150009070b00c045207241a0401281c421701c180d410880003980360000c0782d8010a0f03c0d5038034000e036824200244039a10040130000c101035103408a604040b28084501001840140034642c00110040301030440c41e40121000f4005007110795240500c07500300f01e43c103000d121103002c01c1e4101451600659000b88404e40c96000d040803c01000c881d800140c40300101021712840c00d2401d08041492100c050f01c50105000240003980c0c0b00211f10710001e40b01c0c0410121400010b00d6004c1102c0d0000540e103811200c2d290300411680d583d0001c101e01321300408004a000540d544810404182001d8448503071681c0c3e444a030f8541a5655 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 643202967 1250 643201717 643201829
    0x40b01140307030c0b07110103020c100b0a0506040b0a1e080a020a110a14010513031407030c080d091707030203031602010609180501050106050f0a1202090d05010902100504 76
    0x5803105c1041a00050180c0c10030040b107012203020310081c06c095042c1724030070140607260785152218140d216030754298090aa5102109507005140242c440c0781d84580b622916141584420000d8006c2140c01820011110700c450030319454241c3d941d940c44251b05c800041c20060352292070100d0400010420b55050103106000c40003800b4031920300d10312007140c680d03050360940c0c0c0300600c0e5080900c042c0a4190120b030b00150305c1030740c105008442e207684001e00d00d81070315844003d2030003070300d03c85005c1040300c0305410310762007907804c2809501450350745214500c0d85d101c00d1003200d20080043e0020b0020404114585140c8018041240000b140c10740c0c803101104100c95610b00c401402c440851b00c0001448420301c030750380c05000e09190540c036002c4440402c24552090030601010003d020840368035040131581900d903100b40052020103200030724100580030700701d044000d9120b00101c45000d002c05005008a604071800c55070007110034a9014040c0c91080010b000d10440c01e120f1000c483c4030175200c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 643204217 1250 643202967 643202969
    0x8101a0a09020927181207140a051906050c030c0901030509012007140c151c020f04030b0610020d0c020310020a09080706050a05070206181e1008040b01140307030c 72
    0x10204000c140c0703040c413500410402d0100305502c82c1d41092107114143e5956208072181c2d150801c151042203488d04041c2c2d03151844800c0027400b00d0042c0810441d0002c400c03000c81d00c17110b0165030140038613103401020001a01c0306407015841400204124040755001c0e0f0060741e07103d0200b20000820100b681c0f54440030595032403da66020400140364010406041200000c100d4100c00502500c80c982000c10180a100420381c50410404100c0302c1401658081280c0c40100384501591a4030b80b085840020350854003049849103480340015030355017056917001840c86841e070300402110120003416501c007514240266094010003034071070780b03010040c001014002c403260355602055182524844c04e28411340c11070b50410108000075002140d005060700c002d00e4040343c06655509201c140400c1c6246070f42041e0360802440c21844458440e80720a0f0700c41c40b041594208503120305101e040340d0300c1e882241e00034030300c0544c84014081d807640b081c2c00c122072007406821590840e131691503103a404445 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 643205467 1250 643204217 643204279
    0x4080d2718140405280503030105090408130b07110423090f0f0c03010e030721030204090f0608010c0e061815030a06050f010815090405011508101a0a090209 69
    0x5c03010b0403e00902c501c0715140c107007100041c150f0b81d4517420303500c05841e40b00602c9046d10450076580400c045c0052041101c0c2c060165200d080e0b00f0036581c410004032034010b200b00340c0f0026080300c1c21b6010303401d190168040c09403040700c80d40c0d20040111722078002c0a401424004461244181c0140250400c204401c080f0300c0c1c2d1b60050200d044100c04050039240000500010b640061201c600000e40c0203143c450400c4d075201e407040718030000c1c80c0110001e000d6680607420744e40c20900c90f50058443c540c01402a02d00b20310081c4002007240c44191224003d21581d1504964104841880a02000c1d0300340d141070030040446003000c0340d41c1900549904156201c0d8001d03980e41780b0801ca2494030b06040b80c0602000c0c00d21450600d8034964098a541d40544418015901c0d04002401c0280030341c004041500c0d00b400251609480340350845e078404820303405100e098500118081c00011401d944c00302030340020401c44409040409030000b81d0046d03013206402650781c504403000d00e0150a103080390100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 643206717 1250 643205467 643205473
    0xe0f0423010603030909050c040b070311010b06041e06080601020a080f070b040803070f0807052a0106081f0b0303030615210a1b09050f0d060204080d2718140405 71
    0x4101111b000c00c844c0c0152020043d04020802046071410700c20580e071070383d13816041400400d1303070340e19245015003481800300b41d1100d0006008103242036184841201e00c08005090300455803186423b4038505800d8802c240540c0c454061744c00006e4050000301286131141006900704451540c442d450341100740c604544000001c400c07c490f01d035114400c035030300d03c2c9035280a00300390411100c00740c01d610500001a00340310308684404401f0641d62100d580c000f2042d0020861155981c148075215101d00718180024503d45044880030075403409160805034005014501e551550001c100c00d8107002d40400301401c60074010702c0450301034020032041c074081580301180140f411a490701d080b100030042c0340074000e03000c801e07462440740d10407000002c0d00c10655151241910420000784c20100f01d040050269000003400b099105000c81c028129000c15100c000c000100e860720f5212810701c201403507482c201c1c0810104140c201c0010380c456403140302a03000502035625040c1e0482210203d170142c5140d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 643207967 1250 643206717 643206719
    0x211a0109060e0f04080906030702030712030b040c02060c0d020c070312050712110a0b06031204170c0d031409270f180601030803062d0301060e0f04230106030309 71
    0x212100c4002e95003c01c005003000d102d46466517034040c41c1c2c007840c02054041d501c0400000c0308680200220746070150815003401e1100702c100d00050240c120a484c80d4040c50900300d000100b180009a10b030b0054241403100b03030810002c8031a0304002d40107910504450b214040700080404c5611a0b50003c00c1c07410740d2140c2d529800c0d03090680390903021080f6030003004400c4403143c0c0c40041c0403a4009420f44d0001007981d113a00c0d0100020314121522080d000e00ca000001c0005030012014031445030500300c0c0e03055410486191003000144803c00e0005800305a181c80603592665440e0b00400d0f05884c010110468202249032800b401404405a455481800c0c000d101e1b02130704050100340d00070598920f05070300000c1d40685136260307401884014a02503011000c03441950301c03a0481402404200d08254102c04200380c0d54855144c40055940a9441c112011480a203003000441c816201c681441e590358980b51381c0e03850341102103141e8804290f841e5080d60b804440a0007504001c41c0030703a403005c2e811 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 643209217 1250 643207967 643207979
    0x51201142a040609140603060d02040f020417011e11070f030c080a021e0712060203040c12050601060807020303130305131e03061b0c170409020712030e0601211a010906 74
    0xa6030f0785e140c0c280e208190502c100903141d80c1d03142c100c1d41d4a1fa0705403000b10301050b03a07601c0c1c50040d0095030030402c01880d041418181c2064154066101800e0f2400510906ca03140b40035581140c4150500c400302100412070080496030407000380b00d90920900d0142d00c00d00403038a49000035080320301500c0058000d01034107104000c00e2040c0d001800520005041c4031743c03914241603141882c43d800205040d802000103000d000303424100200406520240c50080b00c6941307081c0d61281d0090081c000031a90303d40105a0103480002500e00c10442d0210354040400785484c107580640062007102c002c2407010002054030030885440411290215504c00702040c150b1a0800540740d100103c0c1c4008044196046c50079075103c00c0c5010140c1e0440386500d1154202c0002d10300300d21840c0c120001e22400013558004021600794901c3c0c0c05d10707880e6000c001c44440403c0b2035456001c20b1003100854581540081611100041c200c51020304c03458810740d4454038903c01c50081c2000342e00c40606030f5a0780304100f2034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 643210467 1250 643209217 643209239
    0x40c0509070806220209280b03090a0f0f141c0507080315010c050a23061501050a05040806040c030b01080609100f110310051201142a040609 62
    0x8a0760600b00d58524041010400c01803810340050034203408011320040510300740d41100c1a00d0380142c061840301d4804054413441401c0303a0207c0c400a0182d2200003a92a10307038050b00d0040c08844003414900045484149000c400801c00f5580b6220301d103580c100042c00125254506081c0001134a8510410081e01500114005040c414001c0401001c000240d220080300c1d0701156a0980c2600007924100403103186000304801409442101103140c28441b00b08415104000d4001c40d10741a0012500c00396140d020949220801040c80d907100e0b9443d40c024800341c62a20980d01c1c2c180d0034035617070b05145840c1036801e0710117a5059130700a809005016005c10340c18050000140105058100b035084259102c80c0460388140c0e869864000009941654100001040c07110b19007039224202910130700840301d00780c4181d40c407403262203a20243c034036018004c401c0e0300740201c0300c25401d030b0340c8040d80c5840034080b5040d00c0e400c0605500821040900c400090f20103006a5645d00390003078103148000c40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 643211717 1250 643210467 643210471
    0x1206060f01210507020a14151e0402090601030e010204030b0f070504030b0f0c1308030a0f1112090d0b0c130801060b221a0a0810030309051207080105040c0509 70
    0x2041040700d05200602c40c010b580c00c0c0c60a810564030004060341c500f076040f405c08502540003000e5000405100319001c034006800700c8240600030198405481e031440c074030303560406495250060000c1000050162034402c1e07030590311071010b04000c1411019036000908a0b4010380085607091040d07814403048400b0207005990200341824050301e01030468581c40350141006000c00105c80301c3c9800219000000000e6440e401c414040b03402406460380010307070b282d800100c4030b400040c0244032900442c5e44194151491910f200c0040c12400d04030f280451300d140e202a000c1c94000300021b01c118005442040c0c103d00c514034101c1c0312a01c490241e00110304140322036000b400c550307040c0613061054041da10200c519501614180925481c1d010700740d4400e4003c1c3e035001c0d01c1a0050036540d8a40203d070000202080e221507030758412580e03114803022040040500015000503c408010710950805003414035201400344200c0b000c3d280d540380014290340013101c040310300c0741004200300a9414007214442d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 643212967 1250 643211717 643211719
    0xc080c0124060801051c12020a0b010905040b3402120a0203070c0f24020f16180509030a03111903142802090a050303031f05090907060315051206060f 66
    0x3912941043ea0406c1d4000610b035003e00b05c0030648086050303903402000640c2c09150321181d40d000a40c1d44500d07240080c134044905407006018080000d1500e506842a841e1140c641d03c10b4451103c00aa465071903c600316014009522070580c9008904607050040c102d450701980c02917560b04101e103000300d400c00c1036070300020301d2040b045030521a031171340c8a64046070160041100802101441c404a2528078200b900107a2800307075a040100d11042800c85106840c500341d0190070015946003c4405c4444c12a8142e01541080c00303402d01252090b0400034081d91071244d42d600b0400340c090541c00c142c400f40b09410100382d8034504000c80d8488266050b030b1007008180701503300301d060068016510b40c0400704007011940010000c0756983c0d40401c080c00b402c80035003281c0e2249000688014030001c80e554400710a1311039903002940340740c140111441204d5039009008960702d400350a4024002c04001442c2d0001100c10114040e01c4220740b450640030f546d0000c11040c28a0418001d070002c040340340c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 643214217 1250 643212967 643212979
    0x6090b0a0609030c030308040201141305041a0306130c030506010b03061e0d02220e03130f0b040e0406022b0f0507051b030909040c1e060c080c012406080105 69
    0x1080440c120180744c1c03007240d4160070680b5041c2d1703d901c01228514040190440c20140c0850020703044903849542c2c2e4141c500c01d0b5410840c000800101181060070405c5465155100a00041d90a98100d100b44246441031151400d40d64603a900d19090072801d07049091186e10210420140f440c19140b82c0c074402020080303e44903004003a000c16803030005040040d0050b107504d41c03a04c030305e02819551a204c845003018100211a1485822500d0340d102c5403502c0810144440045441c03107401c1c100800704c850a02d21180ba052401c007000d250910014410364201e0b50a001104029802c9424000025414109221314a01c4020b0700e4040f02c00603850103c50510700002c221aa0f0b410108980f41c2403000e000b500c0c924804c40840600c2d61055000d1341c4d81104044c400d20040000780b40030101920400c2101c050241400d9082c051f40c04007902c90007001595207400e0340007103210341000b002e5007060740c400400d000301c00c8500c1b4505800402044e01e90116080301c20008c40c0e503c40090f0307015060890b21 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 643215467 1250 643214217 643214219
    0xa031b02031c0e09271c0f08090c1f0c0c0b0406020f01060e0601050d0b0d06050103051e060a0504020f0a03080418050417210c0307030b100f1b0606090b0a0609 70
    0xb02030b1590240d604840c1ea40d000e651105c580c444000c229101a142c0d0b440540c0c1c060700721030038005010b03041c215181404160300001140d44110007140d5100100c40c0500034030301100380c44280b0341c9030100941040d001d0140304500c200c0891800398039240580840040c0d6075480e868140b000789010045030440704181d14101c0c060221401c0018525008602403074140e44420751942041c00a0003809040e81c2d000705841508810440d05800c0181200c1c01340c0c069511240d0710b4030b05000502c042421a4142c2e0300050001292a50694801ca42240c005451041e401042102150040d60705400646038900046020004007881d0b50081c00350441c4481c05100030305080d50307410340229194100320350307145000c40c0075408124001c5000f42000d51600b241107003402c010082c1c161035032064448000081c10180d41c1030403420440030321810351906999412010301e059400311100f54011082010000d00f10301c0e00d401162031030040001a042d07035100011040b4500003085070803111a840340d42400b01c0c030030f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 643216717 1250 643215467 643215481
    0x30a120b1e0a0b120a0e07290904020a0c0c0602070311040c1e0306080d0305251407062306130b030a02060c010504060c110a031b02031c0e09 62
    0x10000312100000d01c00319408407540c001806100940c00290000001040141c1d5102e6503011060107140000e0040040c010400807043d1900254041c9025035510110300783c0000c605a4098507050196620007400c00b250400001d050340e0040b800ca6000492102c0190203000480b10b4507001051a030000b400500d1a55440507000003070112074a100710f0343c884491070700034010040600c0880392030300f82540b10045e218010780101210700501200d8400c00309403d08030707802403003014000c040584102120102a8442d0010064135074000b01c10014507a07460502c4d44062805002c8282c0301ea00003051142c003100f100307036518440c011880c6550030000c0a0103580c3d1074126a03014070941407800490015000000311740f510384c003008001e400c580c000030304102c00c100640c40240500d114040500122848000440c1e05d014481c0c0d4205454210880d240006030003400140802219104c0445041c8000c0d0002420119081c243c120034000c400c0418039851750000c2080081d403c1115031400710f08040d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 643217967 1250 643216717 643216729
    0x901080610050402090a0b0f041203080906090d0e041a0303040f050f10050a120b0d06020406110a210311030103080307090803031504050718090e0d110d030c0917030a120b 75
    0x48284c101d0b202c0000303188c00e0250203287c1201d024218100402c40304d40e030f807481c0007001c01c03000700c85200c0d0034011100815000c0e04007103403030540c41c6202c1e030718240c1c220045003c0000800d444032142d1501c117008161041c06031400d102030401000d4103114607012620340f0084c0070350b0481d9580403a100c0c00b82c000d00008801d030820190b915410492408081008814802500400c1911b250562001c0e5072500c46081090a40081095515039070360390f082c500d0390055890f603540743c411000b0000030226a08500c04030b50b55100000c006160310380401e09203079135064501c80b940203800580e0310035400400c1242c9180c01c401c070000201444001076142d407601d0040c50001c60021580c16110300d0b1a103002ca450719202d29044c403107841c4032400700d035051542d49000500400e44500300407a2401004d204e200702c00e00a85120039140c424001400000215a10442c0100400040c0c48140259010003250103810f1a0704100e0074110a001540d5a105010002d0140140301110a0b00d5074104a0301c01080e4581d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 643219217 1250 643217967 643217969
    0xe0610021212061203182806050a05040f12020108060105070c0b16081201030212070f090c090807060201060e2202090c0c0a050109021002030c031803010b0901080610050402090a 78
    0x580b00d5105540f0748100195000c190100700000c10b01c00441c1c81150f13034841105011b51114201c9030025500f00103011081075102c4c03581510b010351020002001494062401442e1640161a01d1071400b501c60151030810ba00c140c01c000d0045d051280c002c0110b5801c501502c1d0070035130900348141846000d5075100403080d194001c0d801641030118120076031038004507105c605c03541c0c40f054a9807200350014108003610000d200991003042401e0b4515a601000304a1200307482c4040d0000100c06e00700b50301e43d0040c0100031040d0302040003d42000408010038001c507800341c11a9800428400c0c86c00c060324101c108050030a990292000285c0d82800010080f0510740542c191104129503070b800c5c0003620340e8081c200d032890710740c0070b000004010050194800b4117424804c890010124030982e600300c0e0380e4000ca100481c0c80354000c01100340c5d82000c0300313600041414000c001003036018a940204602c503e082e0701420700e40c0d00038014011107800044408010b00b00695046041003404000104c41c0f00b82 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 643220467 1250 643219217 643219237
    0x10212603011a0d061206060b040521250306050702013606060807030308090307050d08041502070605090c01031b052a03070312060614030c12010e06100212 68
    0x41480010342c500c01c200503940c034402200d4040114641c0d803011030105510ba00000c9a015140003c00708a202e407042c142d9094440c00750484007014003505201607403a00541d2240340c10310400c042c3c00c0c100c080d813124180b4a01c0180002a00a619510701501900e0303010b440034065904010413641c49050360780d0406615000451ba40c880611543d403213440e0b200305a0000340150b8100080422600b000191074030490384207030780d040314641d42c5c01100340e02c034058001d00502c180c110b8aa48903d1310306c17070b40200b500280103c800c00706c800303c501c03030140880c1e2100d0b074102d98840e15502005261801440314041104080c01c06108007010581400f1500c40c1418a070000c0c0200440c00700113043d0020208038a21281c8400c107500d03603004100c165030300d4111120842c00607200044105034003001b4081c3c0000c07a0a19160304a1840040111003456003004011480d105003c0c405c00704000e9060314940d00030044c00020504a04203401400821000c10052605650211451840710340b110304c02c54080380700f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 643221717 1250 643220467 643220489
    0x60a050705121509161202040b0409021b06040c030c050d020102210d0e03030417070b010306180515061c0b010b0c011401090c080105090105181021260301 68
    0x1a0307152108480c803400c14803e82d04000706200b04140340000d8174051025851603220480403a00504143e000c0c0c0c450b80c003c400821006000801c4041526006001c1d03030004922103400c0c2c46844000a89890b5045034142d46521041a003041801405c000e90006010161001d4441d00c2003070300080d44d038008a000701040d214061000c11010801001541d030210002c42341401028038501045070b4039001624103681d603040170a01d1340002080c41044807041c3e90300c842010341c560701e151101d80c002c24803198030903c00d41116201100095043c07003151182442a2a80d01e07941c145201400011000d0780c0000f10301c83c0e604a041b102188114038060304503807048003d00d680b4418001c0351800360800224080d22000988004280b25070590030528403210140c0d191900c0f46c0c1da2b60208441d100c028490a41c00a403441c40806500721900340c0281d220758144641c1c40001ea840c0b403461000003403000e00700c850034860142c0b0340800c0b00b101100c06000c1c0401d6042c102d40001446d0403100c1d4403040c800d90010703c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 643222967 1250 643221717 643221721
    0x804030f030e0709060e0a05070c1707020a090c0809060c180a090608060a0b100807050702120d030603060f05100e280203150a0f06030207111011060a05070512 70
    0x1078800e03000124030059020540740141e58032540780c40544458003d940c0f102010800162000301e03148103140c45040660341b00011401c0d00d80701c14800d442c0c4590f1001c40d00c01b003002400056280e4001c03d0000b01102ca03030020391b41000481c001c0c4200c00140c00c0d1601c0390040c0c0d080c08035401c403c07801c3e0340c8203100d44101005070b90828030010359580c0d5640d10400349a030801d000081d030004040340580c8600b040540c1405080c29a1040200660342c20403c4400b00d1020804110081d103e80c0c0500300a500c042c20f41256508104101c0d850030301c10156460001c2d8950034203104211150080c01039403903120781e0070300c446c0c100080c103011102017501500c01d0f41c5002c00000b800240c849205800340a51110600d540c981c09001240041d40c01161500f42c040380c840c5030310510303080c10114101103c11252802d014a401c0210072006075103c3e11003039680d0081d40c289111190f0fa040b000e540b00c50001d8941c8a00700301900040c904201d0b00501e14000149804100a8500d400008a40c058591980d06240a07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 643224217 1250 643222967 643222997
    0x23040506040603020f060d090f0302011b020f06180102090409120f051c1806090b010f0605030f151206090312011a0a0305180f0a032c040c090b1305090a05010501080403 74
    0x2400b107104c01a105089e2204007205058040d48941d04409504c16036a13279400060710705a9580c003c210342100306511602c0025031001e119200072031100402000946084e80680c005415105d0181d41030f11450350101203010215041104e0001c50301290415505020310031020401e081180407070203002585800511a09150001002e806c1d658130400c100311b020b038103050000b0b00801c00d018101280145000100314540510309032841b030302c0d000d01404900e07641c03040b02d00c84880d40421a40e400101c0380f1014100c0100510403d84505102002551504064240c8401d00d04c0d041c0d00542080911803980c3c1510380b0088110b581540c0c241c2404221a1038904185d00e1244403000012441e000d214413003040050003045076441c240c06551600c080d580e40c014a1042c4d5100710a0402c1c0107044642011504c2c00c0035044640156501e04000c200c81d95180c1c6205410783c402100c2d40c641000801007030005203000083c658110380c810b98100107942c10700c000a001498040c0014081c031803500d64003900 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 643225467 1250 643224217 643224221
    0x20a0c0314151306050601081314120d1e0b0303030109021e04150f0306080c15040e0c13060305070503041103070f0801020d1b0906110723040506040603020f060d 71
    0x22140304aa42c0d01080e103000350004090000c400e0040700d00d2410728002ca442c3d980310340400c1d402140110b16559982d00c1d40d42d2110301c1710f4600c039090102c40c0507401007070013500341d01c1025220811209a012410301188001006c406090301c16042d61289040380c5c0c2c402c1510000180e90540341e010340e0050f91100c400414410181480302c1c02011400c0c0080d011403903290b00102085400c1054940c02580080c00360150203990481c0034180300c0d54003000d05001c03107180443c50f810202c101444600d150031f8856400105481c400c9540c0310800e440000c0c0d04903104031107061407004041e42c0c50101700d1801c003480c1c010b08a2001074005414070080100509440c1e0307060140c00000e004030051b44035a40d5407401041d01035080040290012860b00d1004886034116104034040650990b940c4a45241030140c01e542c203840c4100b00040394411500b000c02c640034140d1207040c10200603000e410102c3c02023020002600c8005210900550900347c0c2000161540f402001840000315016600c50300300808d4600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 643226717 1250 643225467 643225483
    0x31107080109030c06151503110c070608010608090d0906080c0d050106090519120b0720031b0309090a020d0227090108070605271002010c0f020a0c0314 67
    0x5041d442d0105200416401269a00e0564812a01840842e00e0800c2102c2c903d202c034480c4014000c240450704a00314402d601416103607204070b0708a400d18401e014090b01c0c1900c0780c2c10060210f07a4110040c4581500202401e0b030100b0540000d0064101d4000300411003507491080d4024420440003069440380b4410a4488040d00c031300c000c001c0c80da95040010202c2003103104030b900921018907420b91f445103180819041d00c40703000191160042c10f40c0c0701e601c0550010071203800c102407440a201c84504009a00034490350742ca00843d1101d90140592803202446109a5080c0d03104109505043c1c031091420380d03005086000c0145c84d181509100c0000e8800c00004075840101c0021031194400d0028030001c043c4001d9448603110380e220072403da03450304140245004100700707009e1101800c81001002c0004c680480e0034004824815002c0b610b00700303406119030050313515502c0c1b000105034070503400d00703807100c2c18401402947c51305d0b114201c9403c2c05000107070031404496000074600c0c20811000c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 643227967 1250 643226717 643226729
    0x609251b0f061a060f18061201080706020d3f1e0f0209010c0b09151306050601080c04050409080415090e01050906180703060503062406030c07031107 66
    0x34005060701c0c81d007040200300020251a1180204010307014a04184e815190380b9032403200c0403850078002010011803100340410855016904100b0078800d45150424103000380182c0c001071428178100000681012003410540080181c1100c40c071004125045048608640305400003124034410300e41540f1950b10740d81900f50480c10300c020300a40080004e150007504411400c2002f110003011000c2d4141d00c598a0b2880c0003a407018120000304401010041e080b0803070344100c1c1c80d2110390003264185078400b16224800c0f0b8001c440c0c4241801014000c941d440407003440c6c213643c14501000c0701c103414090380c002c03907000b25910741c000010030041208a070080c10340c0c0c065100c51201c40800c0140031075010300420300b065120300c2c000211824510f000ca809080004d1004280d10710a40d40042c4d45840100284201510381c9400250385c0c9080c0603160240c4007909108254608403050b2074075854020b50302a010f02d20801c00c03c80c80800090076142000c1e8545008200c0c50900c60450786054445e40000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 643229217 1250 643227967 643227983
    0xa1a0d0311031909150e01080c04050d031d09010b03190b090108030304050d090602030a03110d0606200604171303150504110405100504020306040f020409050609251b 73
    0x2c040700038240c1800d04900c042c140e843c2140c00391175080003424951000080c03004078654050000c42c2d0342c0510201c1d41e0142c081034610b4201951100007400c0e41078410b00a40205400101c21100c2c0d520329011914229010b0b20f00a029514220aa100911005000f0258003011103c0310046080310307000440c8460000700990000d58550030001e4407a0300984080354284545810315030f4282c014990340c011105140c01039401c05ca209081980a0045100d2440203298200650881140c061164201030032180d6180081c0c8031455402d110420403400441003540d01c40c3e42008009000100ca581a0b1a03c00c03000ca41c0b11503103402a403d0a414541008001c021410081e01c42071300150f015900c110300810354541c4801e124030900c001c80d48141c1c0c4404680e00300000601890910390000c41c0c12040240c8002406c0c1c90030394141003240c20540055030301684034003d10540f031406400707264100302d05841d803820101c4055107900f01c01c2c0c81446080248185030300890071050405019025580e0402a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 643230467 1250 643229217 643229227
    0xc030c0609011d06010501140706020313030f0203160f08210a05070f0f0c0804050d11030c0a0f0e040309090f09030809030405130b0607020402210a1a0d031103 70
    0x105600d50000301da03504140d6180c400c941010202d2800003030a503032030a401400c1c1d50703403d040c011602141c400d036161602c118100040000070700c0c20320055108400f41050090310603214500180280f0500d801c0d04210344c8240035910310f1200d8a05024401e6510254a051000151801c2c070300c1806180f25484e82c201140308401a000402d41c00c940c460000c0d6042045a5a80c4880641d1042400804cc81c0000c01020034001841e00800c105440103024401c603504141d51403000403201140204100c0b11a46102503669a9090421041c2409041100d080c0111802c1c643d03144180052031054245410f040340c085428140540e004001410410390103000b0740c045000074102800e40d00340f04030000785903900005d00820010040c2c0b8207483d4001d2845d448548100b1b004005025a8038295a201c1d00c100001d800585c0c83c0d1000b072100503a0004030000c0c640c0c0380c4100c02490100145080c01e40d90404c00c1041d4240320300144607004220850300702d0b40b22119402d0407564500100401102c61100240c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 643231717 1250 643230467 643230487
    0x20304061107080f07061107060e06070203071505090a090c0509191a071401050118020d0e03191407150207030216030c0f140307090e120d0c031d0c150c03 68
    0x5215002e50301c2c941c6640800c4020307d01c90541d1807840b03101e04030005840c00860603081ca070100081c85964001002c440d1001d849202510703000d000d030f0178190301154000034a0a224141081d400c401002843c03401c0150895007103002e401e621408440900c02d00e60b40c0150300c841c9008914840292210120300841c040c00703101d000c0035990081c3e5055030b00316507202c1c00d00601a814094103060741e4206041c0610780e485011040040e40000076490700c0c10781c4845198081e44400c1014042c3c1008140c07150042c600d1551001d0300b80d0b07003600f4248070645010814000032890340d0b400c180703982070b440c880181d9030780940c281281000e00c11041414440c542100003c00d101c40001e0302c2054460041780c00711460703554600b2003e6210318243c92a0181c0090074100101c090a80c08014130ba4548010345840f031b5094101404c0c2944008520b600d6240c1d5005a8000140c0c0b41c0304a07498150100200d6034400005104260355600903607034948103200207419a540c91110105403006000300708112629020088 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 643232967 1250 643231717 643231723
    0xc0706050a09080102161e150203061206010803090d11040e0106140105041d090c060c010203011a04080a170d02181e0904121704030305100b0406020304061107080f 72
    0xc0c4050001402e01c101c045000da406100702c07603420201849040101c00b03566202c0c2c9400c190001030500014a01d028400850310300700c5810400281c0001c01a92807400d0307070411150113000348000040c0d0b400000140203100f0000200e410100c0c084510800d04d4009203400d41d076020384401c0182e00241401403c40265405400c418141e60305050024003012054004550f80d020f98426444074608010404545002501c015900000b20809403a4596155404501f0551111078560302c030769400801041001c0074405651000281411660310703151030104115034801900b4400b40190030070642080d8200b4500040780c4030001d0322035040d5211112108400304860890304424000c0c42a241c0e40c1d00d01ca60024107160510f03400410024144d19640c0b101803040f0700d488070002c18000e0b800c401450112800080c40d114900c60359000c1010710708400e02c0703c0f115050b6030000c29101e40038842032103415001300c00c3e41c0c00d50700c2c0c40c80c0414107100000009890302001e544511401d019001001c1c030665004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 643234217 1250 643232967 643232977
    0xe0607020607050c07060e06040e1008121806030604140702010c14090109031203090b150f0904020306010501030b0d0209041a090a02031f0e1b150405030a0b0403050c070605 76
    0x35000da81d015510204250750030320840c0414820b54008000c184201c1d40200004124584050a4181845c1e150f0204804c8007006503032407000040000010411101c040288400320620140c50701d0505074000d40f056001500004047d118405c00b000041498441d68080d0400c800b640100c02c2e00ea00304410040c1c002c00603140e040c0000f88841c0414a03d25251000310340c810101a5524040203246899809909003440101c5c0100351300c8141c0e2601058007808110700510a03101c821224110600400400500b0462101d0185800404220159074040b580e941120000e08004c2592100140011310030540050020340c40010301044c401405004000d0b40c281c0100c0c4d000c1c450072500c42061050356029541c2000b94583d00c07141e035280ca0404000b0081c40041e040d00b2003c940d1307114240031242031003c11450320b00711030303440844270120b0318284401e090000055a2124a081d003040c8c0443d4a0f107240700380c05081c10200102282c1011712820494000d41a2201030b12441f42c1c403208020f0940c6e104e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 643235467 1250 643234217 643234231
    0xd060f141306020c10020c1f3c0f0218030303040b0a1a180403090f0b120403110706081009020a020303070309020303040815060901150f0e130e06 64
    0x60101a946044038010505008414810001c05040c9059440708069401002100001e0007248440c007100522400a45021350600d4003408210004001c48220b0100366040c07203036998249821403100c1b5600c500308c1e00e443c44920000300c035070301a058001c4070b4038003041c1c1c0d400744e250f440c000011803911486d90160491448540b10040c010110904240e9a0300080d54042c001c4240103001c0740d0814241e901c100c0c1c020a5141c120315460b4035081c005072580c0c000d01104101030203100d040200305036110102e80040c00058504d480d0306424481e211a1b079000b82500d800b081044000418123150003585101d440094010449101c9602d4a400815070300080da00304c9180007042001141b494640c1c001d0340c8403080036038019030965a4001d4128068040e0580981c1c2500080201003816402484070300c0300c3d0004114822840d083c16014040c4c0c0c40c10503844211000006400c20300507650140a44580480502d001c100071041000080e8440304004841c1c0505441c00f00505e180c1e0a01064072842400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 643236717 1250 643235467 643235471
    0x5061e01140a0c0c060f081504140103060e0f1209011107090207080d0524010e0a050306010f06021204080d180f0f0801050601090f17030d050f01150e030a060e0a020d060f 75
    0x907407020161b82d595818850321010a26200001d8106600003000c458254001000070071080100e1340b10104d0440217800586180b41c40346c41c03040110004015606030040b40000600480740362a682e5134035030042880c0141000140180c0d103015440811000000c1e0002c1c1404540c1d0703201030b00d01556a03a0014109500a904041c0000d0300100c840080102e1015000071104081520307400440340840e59a410aa01800c48500454a91410042070303028000203a0440c04103801c00030b01070700c0c1c00035046000e10342c403074200424804d0f2200440d0000045015040209046014441103054000242c0100c401c2048210001984001e00d034400300849500344020400c0c0d4603210011205807401d0300801c804000f956104018514080a02c1809007000b9001c1d642810314071000c1d4030680c1c40640e0f90382c1d1041d4006c001070203a9940000c103000022510f0034030b44803030308203d00800e840c2c0c0b92010780501066900d80401b131280106002d60f40711103600511200700300a07145031a42c0140070050020ba40e140c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 643237967 1250 643236717 643236719
    0x51201090c1d01140c030d05090105100f050a0306050c0421020f010c0c0b090d0501020d1506051c05062106070809010b0a090f15060504090f05061e01140a0c0c 70
    0x2152000002c98a04042c2e440100b4165400408406540b1800c16002ca0384420040e40e1442c2015116443c0500310000c004209410880b03407078401200250080300040d10480c0d01003120b23544001c1c1e0f0340f04a81d8000008656a6a04968800c01d07001316413243c0503600009504407030850145a24600a610898002b00703080c0700c401c01103401c1400048010241c00b0041c00c280601500c04018050b4560002c080f280c00c0340c001e5841c03500707907001841c0f03048100d622503621442d0300c0c000740c4410000d007003c0c2c64620306080c1041c032610140780c0700b1406030552507655004950b103600c074078400e4450481c0580240780c10f80510744845941c0c40c02164810000390812010801d082c8060081ca03500c100b005024102040c1841d0010303005081780c1c03412032806559488500b416010a60f50303040102a1a01d0f00e0340c03160f00d82420401a51030032042c0586403840c0804000740da81e00c2e035441010285c43d501350000071100300001a5486003045003000c3c80040003080c61000a81d20851515043d44121307603244c012 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 643239217 1250 643237967 643237997
    0xb1b0f0a1205010506070f0611040f0509010e040515060607170a030608070503030f0318010606083913090204080f0c19211707020405091c0c03051201090c 68
    0x1c640138002d45510400401ca504003080c907544002861a00410001403a0b200b8210315850561066001140c1641a00d108200901d08010136900519100524031841d16003595100e8130380010401000e11102c480001c11420745842090310b01c1543d111010032034001101000640b203411003c0d527100020300b000c8000c0b60800b00800d8032000c807031000d80210308004003040d41e10010f40000308a075013021252505a07042001c02d00860009200644481840303090400c0c4148030200d046281207400303045504500c0f81510007000400394850000300150f21160f0828441c20038009550146a040d40040390104081c000803900804003c03100c0102c4880b0030b60f00f014052200103403805101c120203071290802c070194070503880540e81d10340100441c128441c0c0d555581c0392555082a00c1d820132030042540411420644210381d08018254000c1c4a5100c80c048015048081143c110741004401d07041c103420140a80d0560707c011b0f880c0c03001003005607100c030100d000501803510210001220300201c8410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 643240467 1250 643239217 643239221
    0x2060d1b110714121005012d03080306130c0306050310091106030403021006091418120a02190f021809030702010c0218040c090b01090e040b1b0f0a12 66
    0x1e2290410050080701d440c0544a00c80003242c0e540315900f090a2129640364007005010b542c644808082d00000c4550401c2c00d407041c0c40414015104001c44807004d9240d12a40c842c01c5c0f1011a0b500a1900ea503a41e9000c0114111240300001030704041d0608158150a0390103400c85825030b50145d0440c1c2c0300300300c03100700a029a0303040030300903095040012040303545003401e81c0299030042c0640101d8403000d50580115046540580c03086070380d10f58422541050801c0c6191561300028485108001454030100080d105c2e040309111041064001032a641e42a00a10507104104454050740c9410043c1d82010102100080c0d4124451000b000700d0184414480c69114050fa11410003141410300a84c015645a0788115041e603100400d5208403281041c1012014419031082c5000c10351245400c0046c1d043c3d460350b03802603040c4010710070140300c9a4510807280394841d4204944803404d440e060740c464031030118124801010740d00002d4814145141d4001840200180d56500d02141542c0042c902 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 643241717 1250 643240467 643240487
    0x1027051c17041202070f08060601120e0c1e0a0b0408060a0203040308130f080307020a1202190213060e130b0f100b18060a03090501140f04080c070302060d1b 69
    0x1c061200c1004100030506518203440900c1c542e0040300c0b40240c4481d14203050b5255940f04540c5640310400708005964000d42e04160001c0242c3e0901c001441c484241ea220012060101d0254105000704004012100c00da443c2c041d0000e810300e0881520342d03407c41c0d00b1b54001d000e41c0c4014802e10011501305c240ca03100316031155405580e8503010b0303201d5a0902d00030b601682415503e2910f65007203c008603801c14003c41c004d0049400a1020212504e00103010101c40d60201c030070740d04142c10111764008001080269145d04407410b48941c0700c1201d80400030f0540e030700030900ea030b01500204031101c00c0e030703450401c100e1f40608100441951180700d103058191040303030807000c0a02c91110070042d40c680302020340303284440e2a82c190194076080c0081882ea4219070380680000e80c0718205503003401020b200f0358100e0329000720718500c4d600c4e14071801d450064000e0001003082c600020f6070400c103101480102c001e9580107081c81c2d40c40b9403403013106018040b41310f07490780c1c01d42e640c1000204003030003480e80003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 643242967 1250 643241717 643241747
    0x160b090d122714150f0d0b102a020303040308030705041a0307020d4e050c030c07031205190c0e01080a020313051e0d0f021027051c 58
    0x14039800d0910f414030581000c1801140390540090040c140504c000b0409004e198040d0040050080031050030005014000300c1550140a52030f020200040308904120072015010203038540d030032003079201180c40c502c600e501c0a07000281c08014445050ba0280c01042141e400d07460000b001d22007048000300f248004d8480e9005a44240072a1082901807100d80c030000100b100d941c007e0074030100002540c1c04418800096050904068118800b000c41c0d29400d10030291071308010340c1c80d02003055110751002510748080720002151200806219041c080104500c407841070260781050740c01020480141490640d01c141450446030001e840368054120041051750354003406d44441c40c1e409c00035403014001010030380380d1a21000120700d0402508144659100301c80c40d000480308002c2d414070780f03451b0142040101030034035600e0b41940021004200000c90000084600a00c9a88141080035a06500c0007d5040c1700f140e0500070003280d00700340d03d11400c201000610b4800c1040f13502036400640f0b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 643244217 1250 643242967 643242989
    0x150503030f0d0b010306080d080a050703020703020c09041b0b0408010605010c0506060f06090a3b010b1c232217040305120c0f160b090d1227 62
    0x402c0a04140c0101e1620101030400041c42500c81c1c0406080c00ca982c5002c1c0045140d034002d00c114001c261182c540e01c51241c0c5011410a06a660003c1d20390341c1d0710188900c0303110748402103024441815a03008a13410864901d404181d03640700b102c40a40c0081c4070750000e6501e0040b001a0550007610800c05c01c907401009044595500b0040010010401c5102a00f241d002c2c00040750305d03102ca144840207084104652614524040045903000401940d525041c60505034000302c0b049248800a040d900c00d60241510b86140d1300d0b44541c0a01c520741c14501240c202040d103544551041318441e80000b9101c440a083d07070711840c0340003102c0141c0261440d4944000c4c114000300d07502c6910a90b884400c040500d1411f40e80781c440b98900380400c0c20005405400140c070142c007590070408174982c02e00010103007010701c5500380c0980200004e44a072110082000604d0b031819902d408042110560191201c0202d6a8502c8010140cc003c8004e20031174002c03408040c0b204041d80f008940c2120318a01d04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 643245467 1250 643244217 643244227
    0x703051210090501060e0418050a0f051504151b02070510032c070806040506041103010b10020d03150b09010507080f03160e04020309060f090c0603010306150503030f 73
    0x4940103018010100e41a0744500314020500c10003d004580c02001d0300da03501d055981c0c41d0b10420044800442900707035050500c034060000600086010404035400c42c07074081c00c0c1052403d08034140200f803c03000e21180204d00802040002100e890101c04800b4401040071441c0d200500301024000303250280913a00400082000340703001072511029000e5450081001603030403100a8041c00d0280304410802219203200c40c407105d04000010052600f00010b104600302921a1034032904040e1015220310000c6200c402c07140c509401407040b56801900408003801420f000a40380d01c0e03450088000a420940041110241d9010000c01d644000020600d010a900015587c641c81400f0455050009003c43c9040d80c284c140a1803081088001031f41a910503000700034110030440510b00e1107244140305010f048100029050b42c058400422041c1d03a8481c0440145010690507030f41c0e500c650300000200070803520360060000940c00603c4000d5180e02c0c2c800f019243e000d030030f01012913410f040c80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 643246717 1250 643245467 643245487
    0x102031b0319060f06020c1903110406080609010c021b0f0d140604031e030504200a0504020c070504050108070501021b01120c05190503010506040b03060402220f0b070305 75
    0x10741c0c101041d0818103406000e28140307501561029803084411540750601003103080d07010b201c14030009000300c1e107008139912550340d45c022119807400080c0c40c10401d251844015100d030392200019002d0360040311424584500701c9400ba01c01030b581d490040c003407440080c01c0c2d050803180c0d100010b0300041c084544090301d40c0612045003807106c0f050314281c083c0550860070305810301c03085003d68044da594520300d59400c1c85030f4945078035507907061003007602e440c0822002c6a280080300c1d40c0440c0080c02c0b1403000c883c04000810f803c0c01034010340d038407510018040b04030f083c0001d51401268130658041c49a40c0c0e884403a25124940c0b0b128450268002a4480010040c200c00c15541c1c40d2050400c03e030f0207020700060b00c04440c5043c00c07050110703400061100e034448a0306c0c071122031030aa52819614540c14800810140d00851203821100d010100c00709030690340d5a01514074442c0d4010b1004240a91a01da0b070301c0030092803154030300c09580340c04041110038a00003151403540d00760f1140d61400040b58 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 643247967 1250 643246717 643246771
    0x40f0b09030114040311060c120105132d06140f1207180e0610140d0201031d06010e090d080417090a080d020d0c0f02010c0c0f03120f02010203 63
    0x3400c003a5040d50382e04074040c80c040034090190f000d54040c0d0341c1c00d0304101101c0c140c6d514040003c3c00040201c04280124402c45d06803400c0706040d9041500c214840036500d81c5200c02030001903046c046800002e8030041c0302e01d48801c03002c83c00ba04c40008144812940c0e61402c0d040e216000c0d102c540c0146801c8040c1155007080038082c00385188840890349103d503241800300009100184920741e0a40b101355400d40340204000f959040042c408001920a00c0c0201a0207001000300000c0d00500b20a00f01c0c5095a029030300031180103c440710000c4a901c02944200e0310354209000d41201c0b49900c8000c24080c0000213032a01c0c00b0b807042d4840c422207480301d403190301190003401e03a40720030031000700401c0720306464000d00c0e02c00419010300204801040300c00c02a06011042d4206e90030000000d2100001c03070000d41440340442c0d020f08051103620f0036802d1a1412845170b41024200c801e468200104116505045a042c0b948559900000b41c0d00b41000b28240d10055031003d0b0441d0010804d403411000003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 643249217 1250 643247967 643247977
    0x70302330a120614090c070b070c020f04140f07090806040c050a06091232070608060f01050d1a06040b1c050411010f030e1b09060303130905072c15040f0b 68
    0xa180d06c0d04140b2555582ca55050040320711600003a4505004d10460500300c03180f00c191801101c0a11070600e082030900020300d002020000c0c881038130804208503d000310400405824140d0a80e046403815090140301c0080385e20909020302442d207c0007690610610030030080e1080810081700d44003417601d61a21a1004101102182e40a2000110213814071a450051403421801410003940b6024001e481c044004000754018810803d5102c3d0a0781c3c000101c51800f41c6d5400d00041038080c0508041c0449055201c65400007800280801c0c40c000200117084a40b540e50b8100d41d424100040610550341e0136500141809038030600c141681d030182c6107410b0078a040780b80000b848030341209035619202041003102c0032100c0101005025082151100c1d500640c01d40c020751400000e07420408400d00f1a02c21014000d40c0c1e803012501e13051080c50840c1040b440e10750301e000d040004016160402c02c0c01d0100340d02c14034411580403513600c8100d040e92b08458140001c400610324002e0340745155801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 643250467 1250 643249217 643249231
    0xe0601171504030305060301050a0b10081509010305030309011503020f01050306030109081b07120803070c0f051e0d0c0803160c0b07030e100e070302330a12061409 72
    0x6140c41003103441e4211104644114065074000c9018141841031500b110400f90031100721508106000fa0a0388070b04141036500c042c075190244081d90341001c440f8010788034440300f45d0702080d01800001071013030010295001d080140c001b002100825400c1c20b02e101a1440b009401103007900c0d03d281c6d19800340c1c0266510640c040c0c00400d0040042d90b540180d81e2244806003941d0381c10040100480408100d42c501030441c106194214045a0315031000c50302009054400300201121110300700074402d0340e5068401c0e801300444100301c40c4030b2544508c8088460402e2400c2c4500100d043c03c15200364030b0203241b036400040440c9580c8034a02001d203440c20001c0c1c002c0501c0808003e0900041030390382e104bc03040c112030303400050800d801392045040c000c0c0c01c484101540e0a10071004001c5101240c810200e9604542265640c031580004000109501842c201030907020001156401d40b800c004021041351030356046110360051000000312a50b502801340c00d02c0c6015004044c5007014008181c02401b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 643251717 1250 643250467 643250473
    0xf0a0c060c02150d0f15060906020304050a210803090a0b0f1603050a11120a110f0d09230d0e0d05070e0a11030406061427060105090a030f05100e060117 67
    0xd940c40b15001d45040307607800203114114640401c00103600c248c82c1400381041d0b2018601c2c00d881c041c0015410090780c000c100741d0144c03840c40003540f5403030f2100404c039695108081702e440c0e1a25141c03150b2560100d090a90341c2c94131000004052103403483ca003e12a212960b42d0245c1c03403005071411002840020b02ea95003403540c0b4040d00202d5484000a000c0785070708443c00b0340c5240760000c01d40d002d681600c6580a2519018081880404a41000d580581892000000d860686818008407207034401c1e506403003840383ea03401c9402c00207020130120030000d00c036100c040101e541e0b0002d1140c80441350001a0541e0400742c418000b150001201070f80140f02c0c5140460b0b41c80c01203140d07030f11962050300c0449a541c0d03a18030400c901080103510341c0e4110011280c3c00c41e014644800b59160406805460185000507030000d6030300c0e8010015104951401b42000342950340b680b9000d00789035505076040d1203601c5484c0c02c0f07100c0c1c014076010754804140f028002c0c0185034600035148091040c80404001140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 643252967 1250 643251717 643251731
    0x12130b040f23100b010804021810180905011a1c152313110d0309091118090411120102120f16020f0606130e0f0a0c060c02150d 56
    0xb207116101c1a2071a000c18007800803408401484012038074110792582c148000e0b0b6040101503030301c4c0200c5a1600907030b42030300800d5644003290007818851139004601620005511004202d015a1010078454441c40003000703003484821800703524000d00c40360554060b04085441e600040804480c9002c544284c016084840c400e003032103010780340308040c40c9000246200441011201c850901c84d0421088400e440c03201281da11107020141c100041070703001c5c5020907210b1003014465032a404c0280000c0d4420816011600c0038400d895215a04040c50708400207289041d83c600610124047d03a44416205007460400040c404000e03886507000c1c071195401d00561030104039803140c0c0d601c0b074060800301c0000e91510001e28000000030018040c21507005026007401e1038000900759410003821136250044500d070000110191842024212150050800415444c00e000401c06005441480c10b03020583e21600c080b0f402070300911000e9881412408260090701c011001404002d81d000c00220b152 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 643254217 1250 643252967 643253003
    0x929010909030e060f130e01030f120507020409080a020c01111b030313060f08010605120a021b01020403050102070c05100e1507060e0703020a1e05150903070b12130b040f 75
    0x40c2c0c0005003091a899000036809424440106e001000383c0700b180800e61807941151a05151003d007110018100ca1902c800d041406010b0340c2540d40350381d4000d2080c803070102d070b0389007e07825900602c01200162103103080c010350030760103591008031020040c402054581000f001c100b030302059090001da01400308000d0822400a4890300b88050401501c070315000b201c003520024255001680701d41c00300002801b81c0c88442c4a000d45064001002e06805a00c0703071207181119010740d00d404800d030391940c40014004200720f410740140c00c04a0045c15a020200e42d200140400201084e04180010341c644902074040d1400110798044031410454441c1080e000e5507840701282d488002641e001e50100c0003c008502d081c1241801602e20682c00041044480440c5880c200d2907010f180d101d038484a14030290102102d054400440c2e000b01140d0619035642521070640e40588207100300c0c1116000000d0700e02c9810000882c1e029480300d02ca04165856894842da0b51103c81c0d02147c500c40c20309a08554 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 643255467 1250 643254217 643254229
    0x215130807050a020f0402160311070b041e080d2703080a0206060f100e01080a0e01060611010b0102070b0a0c11040509100b030606010806060d0209130929010909030e 73
    0x81c4540c00a15803c0d0480c0100901d1000381c01140d4450ba0040008902c0c5000e48080c500c0c080758981000807102042c489114240a03194108002980c004180064140f1288481c0c00f10f80f010601c03036040c441d4803035002d04e440340d00c00ca400e900480c1c3d04014130011201221180040281904c0403c0038842c0c580d80c0e0410075030712164503000143d01407824008149016282d00c00848012100b070305441074203400c090a010800f40e10507041c807921400151041030b13560403040301440c0020080003200e0701e54002030300004000c01110003075842c001c46145d60b5400000c012080e00c00c4940c1c0f460030000300f094222014a166141110007c000440392a461380f80c600400c0d00418804021707220080143c80200e04a40d175400c002d5100707034010000e204160b6008030005da00b10405075802682d030000440140e01038494081e0031034006000e0203401543d4141c1b9407003950118030540030a40103021000307200d00200c81c0300459807509514800100300810b2264081c00c1c00034420300381256813088400025603 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 643256717 1250 643255467 643255477
    0x1505060f030a240519080c120115030b07080703020309123006040b06041a13030506190c030e0c040209030f01020f07170403171e0d0603060b030d02151308 68
    0x4142e449066042c011441c241c0c0b17583d005d0840d17001003801980c0c40c00a44c20f90703603051a194039000b07000b4840c030f00444e035200390044901d4400d5072100c0c4100527030f01d21303000311a01400c50361140043c00000105450b2442030003103d01855046008101081719034035005603e50140c400803281c0c4009003440c0b401c06030700200c52275010032150408401417402001380820f0f42d40461045204010400c81407200c001890302d0304825118441d8600c0e118102000c020407002c4a44d04080c0617480342c0b000300000c51a0380e40f5072079a803081007103091100040442c0705a05540b17a0407999245034018010840e00c0341080c0d40604003038140101241d100510700c0c8500c9007264010b03004241c0c100350004d04001480300c0701e10103809400309040c245242c1413075500d44101e05143c003144240f950781c0002d110421840d0100100400301003060015035500711101811000700380c203100484225040110030045440c000c0340c0140e80400c2a00607201103002410500900c4100810540500c22198000c001160038500586 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 643257967 1250 643256717 643256771
    0x2033a0e0106050f06090109090207030c1a150402041211130f05150d080a12020f0d020a0305060406060e130e0d05041403010506130203091509101505060f030a 70
    0x3903094100f0090080756003516000c00d001c0c840801c40104142d038010308a07021103d140d1401601c4d4102441c0480c4c034890101405001e03020b941c601000c40d06810316a45008a044420100041c0c00c1801403005a001d8cd1240c00c2c80354407400081d03c04102811005510040002d2016103200c042180c4e400444400d00ca103070075003070340d078208101d030b11900b5181c07070b80b22413000302c803140c001074200d030b503020018418140a00304200616680e4203501071181c050302c180540f01c81156403074543c0030101e1402500280f0500e4002400c2101095150425119140a0381c01070340d10f00b003400001600740044108002c4420b0419541c1c0d00c8445030905040c0a05101030389150388003a5540c3ca02604d10f4520b5441942141c440e914103414444240d68080c5003882d92213070880050b8036692b03040180c5040044103218034030009003810800801d0240031030600c0c2c0c90302c11807104124801600700c10942c40e440702c1c002c050b0040d80801402000440e42d901555004410400101e180103c140741c040062403c03044103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 643259217 1250 643257967 643257971
    0x1e03021024081b10030e1203191e0c05040f060f0f0509030d0e1206040c08070e06030d0e03070b0d0603060f02031014010917030703080702033a0e01 65
    0x20729440d0308441c10500038049040148081810b08120f016828070314180544a1000048918042c0c0c0c0243c024103600042d11003540d9060701d50030414240c550080355036822840444c031815a99030500e102e0302c80b442e145812440224506d4480550003071503105030100510105100010301710710344510010241580b80d4804001c080c0800e0050004030a00340c0c18410700000b4860101c803520001080511003080340f52444200c02c0110106540c1004440700c103515000780d500b000144170541072080c0c115a41602254442603a403d00418100019103017180e168000c0e61440c2141441383c124000308200c0142521141551625021404d91154842e0516503413104010414440030380f1914052280c0100c0540c030314034050308102c09281040c09030071600c41402143c100240d00c9140c03501b000c1d0401e540140c0364102e800c0c02060b620f03082030404070f001680c8030000807462407000c02030702c00000100d10702050b19030182019000d450020031402008100313120100c015503c050042070401c075245000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 643260467 1250 643259217 643259261
    0x20909010b150403030e15041509050a090c050f250b0708070905010203030f070908070b1902070b0f07031407080a0e0102030a051218010e0d09090501031e030210 71
    0x51002c00700c40c941d566104940280420800b00fa04602010070850040f06c0a00c10f0b80300519201201e4041c40d000082c4488152084d4406c02d82c01004040c1980c9046400308800d40c0e451a0f0907041d81d00d007684103000500c0510921045509040141184c0c403500c14004003600382d080d048203c2240c1c001425150301c0300000510806581000f65290001840d11300302c04018188800030b9a61300c000b40060b00301d06440000651018420f2105802030400002501c4c0440c0d61403050080d01d4000b89440b06400790140e001141590000582c00d0484010f15411030030a517018401030032a400c0b082c0107400340300842c11a502c0740145e400090403058480c10400762228101e01c030041c170551140768110b066500800140700c125801c0b609480322482945034401c0f00b80c0d2805044442e04c0e01c180700001d00343d030905c0c084c1d00000c2008120900401035640d19070741c129a03035003455030940d10207200280c1050400c030f00141c0350540d907000b103070310b01402401100c08600b5184114021141c01c0480385c170910f102840 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 643261717 1250 643260467 643260469
    0x1210080609030a080105100c0b19180219120f05030409020a09080c01171302030a050a2411040902070f0c08010218010309020303040611100203090601050906030a0b0402010e040207020909010b 84
    0x134038540540016600b4403002046e8190140111180b140054918130540001802d0f45618111014600d13440040c00d000e50a24201104228120810f0492040d2410310101c071810341c1000005040b50700c81c401c400f490b0400360312880c1e4180581c000a42c0c16010030030000c18220418001000d56802c04c0c1c0e1095146823415070107034100000c88030324504000c0d52154a244412504c44d034280c1040302c20300742c7e1400a280e440001d10b8010a24001040390081c1542c903028031001c2200c440750411f80440c56146207141d11251000c07601c40c02036922400d40c09000920441005a002d01451885101c107440f05c1e042544030f140c888019548200240e030f40002d40c81803004079458898448031400c0c201802214800d40c0040d0720f0740100e00803202000210f95062008080401409801c84d5400104550703a05201e104103881d45d1007405050301135032a40011031460b040019186e898690481906801c03515160300440380f00400d9038080f03600c607030288000c1d009a950048000e0180a07610000614004204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 643262967 1250 643261717 643261727
    0x616020f07080715021914010f06090c0201050f01080a030f1116031e020d0206090303040e150a05060901021507050912010917030f0a050603160e040201110706051210080609030a 78
    0x10300d04c0021500240012014000c480c80c00000d40ea0384212801d80c1545214811360041104c20958096079080c503c00059003155644030030700405035680280019503802000b80b400707240a200d51b52240c0d001c0240440842d104044241502c00350f494190308401071218100c2c5041501d41c04140040d1148400700304208101c0300686140d0400b44503002080050740021b1240080ea40c00030340113800002d00185255020b100b140c0290100f000c840443d8100a40f800f0340c0700740248801d41c0a118074401c0030031140707400000d440741e409e016402090380c3e8280304041c1d1010040509090103000082c44103007150390300da20352800394105400002030745103090304190600e00302c060002d0822101c20028088500446039609074021200c81c0040741a8690102080c0b03441c00c0b102c0101030b0f035001407001003400c8103c02d108501881c001d81c0c68a9246a00082d0b10b82c8a10080c8600e10204404020420500c0c0704e10742e540b41e2054178940c0d0a60281d80d14082503003003960407180002030fa040040d40c400d02607045 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 643264217 1250 643262967 643262999
    0x306060b0903160f090218040c09140f0d080703030b0a0b0c0115241803060506030c040b01120c0e0d0b06100c0c0504020d0914030306031209030616020f070807 70
    0x1c1403000054514150303c1c051300311228026204410303000030751020240c01e035804440c0b50210150040003145910040103150014a01880e101940070050036810342c80c24415151600740c00038620351003017400e0303503500c4202d60003900f0440c2815203032008407075142c0d42c1e0b801ca20003d008800c0351540c1c030721103481d00500319111044034030b04403404c00300c090242c102400720001040c5028103030000304100002e4180c07107243d05644080a4400107160200810a45402c0701d406020103400b156203a4403014100404d440c0005061030018078840810090400b15420140f080358440c200208081d00c0e01340030826007a82290b05542241030a030600c02c840c10022550b00a640640c5407007003429402c1d5a44007400e01d0140b081c148195008a600160080c42d80d0080c045c2d40d80c070035a08502c1c604021501c5403a5001110003d221307000b6500010501010f240c01c40d245264018040d04241e91068082d2a4002e80c4400040461142c5099070040c03220402a0300042d01d15040181401860070504000550036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 643265467 1250 643264217 643264243
    0xf020f011b081e0108030706050c0703120c11030d02030117070e04030807050f0c0105060301050c0403081213020907020a0b24041a041404060f0204030b1f0306060b0903 74
    0x242060008002004501c403400c00d1541d46400001c646030001e401c0720070514107009000c6102c0c2140000361002c8000004d1402074424602800580e980f8002c10001d8001c0c03101c0030340454510b00d100546112140d001c406840c0b07442c20402204007804c4500392650300401d46a100d2244c1c00070050000304102c003040c005407c1420014a940c90401c400c0f52808a409800141444210703c0400d2005000e201909e6035484011940364462400306c10460203094140c031034030300952034200860700c000c0d00002100d080d25008003115140c0040c1400744954440c0041c1141d200d501220700c95001030307852111043c000e0405500401080302c2030f00b821b001101e0058021451450305209030840041429051508010222000940c01540c0b94000f41d03642400c85000d94080c0c0362885103000c002005000900440c000d00c020030a1442041e0784100702d11840c040504068202800200d03015681000c6641c5280100f4600802a91381c3d0750301c000323a80194010840040d804210007025040801c003134408044 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 643266717 1250 643265467 643265471
    0x8030a050f070c0b07150f0510031410050f010f0603050f060108040224040608011a030c0d09020d060c0305072a1a0a0905070e040804090b180103030f020f01 69
    0x11504000303030051060203080d1008000200d0b0712000d0000d1070070044010407410841681d61a130364640005c4600b01e0401005110380341040f1680c03031851910070284600c08812820703440c3c500315111521170035944880c02140344541801104086154000c143c0552102050100c0a5050410aa200a046800c400c04052501c0d003040b00c40c40782d0051482c2c20100c2800d02685507103981c0042660880340c3c1c11505130030000e120080b001510948001e00032031f0040c1e075072021980d0b204d41c41c4000a8040c8502200c89082c00d001240480600710003c2603148903520001601403001c1e80480d1892491150550b44550313245070004030aa0903003d01d40e80829246002c441810481131040300c8181e111004c00e007206282403541080100c40072690414003141041d20b2454905040f880300903100007a000c68481c014004002150a92103a44070b009951090040d41410f090020440080c01a050056402581144403006030031b1943c00050185000395074180d003010320b901000c0e141900300b0f201e07183c5c168 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 643267967 1250 643266717 643266727
    0x203062a1e0438030f13210e0126070c050f0604020f04020313110d0f050105090d0c030e0603060d0f2f0d081810262512090803100803 59
    0x38010200b00caa10480786207805038903451ba51080e000b049030052000308210b2101d040c100e030b4a045849005101079071940c800c51850402001102c4250382e9401c80120002c0504880303900e59096007407550700a809141000c042006500c440b0719040b0003084460303603500558144410342c00c01592441211100740c0e030a514508084034540742e07007502044040c1c82404d218140c1c036032a549181c0081803141d01300c00c201e00a05c2a03410045e00809040c1c0f000c20140c070034442c44449850092070030302d413500e802d07480b465801c101e180e00744030056100400c602c0e484001d0545040008908030341401c0024000c1d52802c0744454659030720840c0c030810302c5100c048502504011010b0790b40d8903642c85e55981d409905161200075000369408042241d90b00c8a41c04491103003440c4101e50b0100102e03000c0f00c0c0c42800005031a080d919041c20a040c1903408070045040e080f40c40314120344c1300d030505441981c1171400c0740070100f4030b0007034004540c880603084818540000601c01d0000c0105a802c0161200c000030314941 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 643269217 1250 643267967 643268069
    0x10b09090d0806010203091e040e0604121d0904060506010905030316080711150c060a09031706011806050a02010e0d0504120c1d040203062a1e04 64
    0x14904031101ca810024008005480c90740b00b4001e40340e21320000307070011802c99503600b400505440904200b9001318034206e04105503460000364940582d03000203140604107045c4800b00c074a004d038034079840c13881981103190a0711920f0b07880c1c0c214403903030240500144070b040c80e200060407049580d00c10b0b40b00b580148038000502c1a1858032405040d4400005951840f80d0b15182e5200685d00401d035500001c2d248210304014440c00081c0301c450305200030f5900c0c40e070b03030f421021044610741400500003d0300e041c1600b0b0718039424000103820880c1414100340c420b0b103407110406c00500030f0704580d00040c4049040750030250240200c04050f40c0c0340016002241c1250300040685c0900d2043d88003000308000f00c0300c1440010003462020304908204207400d08919003c0c24416042910101d020b8860b1400103844485110000d54002211143c44405c1a081c403011001030381014495114520700d00300c1080c0c4020010000740014034081010000740004d51902d14074402c030006041d90b06d0b04050400b91a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 643270467 1250 643269217 643269223
    0x112081e0a0e030c031c050a09170304050907050c03091e0d12091d0c210108071a0a08150a08010509060a111e070c0510030e0d0e0904140a0f060c02010b0909 69
    0x1c034070342d141c02e40d10740308c074442c0131074220865900c0300ba8102001c5180a50300e4502000900a803442910710108076284c041089034240300c2d4074403030841d40c1c01c1400508040d00c0d00c0b5a01c01b07844465510300c9002404004005001c1c81e80c000c0d030844600010f1342503a4a5160400584002862a941401a195000525040184002440f0200b2040000752104010481441d0594404852040ea0342c00d0b40c0c40f0500300c1c0d554200da000d0500346981840404c100011807408075000f01c2180d69604115456041c1c049940c0001580d001e64003409040c804680701e002441120710681d0b101004000b1030406017003510840342c48601b44070810f03c0800c002108152004910144001110400ea0791003071542415800c40c000e58201ca5400b0303080f121010390303140d4140c000811070945001600c02c41000c944003620204040c032221900300d680d42c030001d400706102c1210040c950440000380d64581590365103241e240700020104682c5590358260468580d0703424480d4525100c42510b0b01c042c24102048010342d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 643271717 1250 643270467 643270513
    0x1305060705070302072d0e0910020406051801031e2703090b071502040608270c0402030604230a0f0504020a051207080d050703030e060112081e0a0e030c03 68
    0x36a00c030418601c516a0302d13402240e0300584190201b08001510341c410441103000951362140d851240c032000e0b40d4800480e2088034201d440c4c68541c1e528180d980329245607284083e8510b40c2c180742da80da085406000010004a000391410100051058802480740d904808440c964403801481e8000c10320000350800502c0c0191000203012a80b42c5059290046103011601d05142c0503e0010500003456500101823600403070b90540d1420302c0b0f141c02100c5409510400d404403400b58040030200000d0b04180c2d00541e000103000c0c102107007030103003900c4030310049181584c003100007058101003000700c061074805c03410640100790f0140641e040c40d070001458842c03d4080c4520070cc451444c601401001000400c1c01000144180d90b2019440300002d03000340c00c200001e4001c02d0400350312065140c40450124144e034901d00c0b82404598103602d410100d504400310070110001c180c00903584a548400c00b030300c02c02000c0c0c0d646520a10b1524213150410001848160107580726070001c3c1da0002c2200e900b91 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 643272967 1250 643271717 643271729
    0x150b040b0d0b03070303090e090f060718080102210f04050d08071b030801051512010303110312100f0503010c1d040b06070507170f10050403090e130506070507030207 73
    0xd4440e01d50016038001000700c00e044603070500c2045400400c041c0c2294644044406040340b11140340c0e59074071015151580c840300848650015400595070b18041ea55000c4481d031002800d5075211b446000d8107089902800d4002001043c0382c0e0300400c0c0c0000324131103603030041112500716000c0c1090f0351116501c3e4942c1e000c4000384000703130000810791481818222100c8003140030740316a108083c2400340040a0a000c0c0303d015914032030404144000030411900d80c0c000c42c20744145143c0c07850b10104c41144070402c030b0840902041085c524030382c0000c5140c500807000c03e040d106c4000e1070440c50a241010b55404107000b641040d414030311080d001001803d040c0d000322a911801400c22001800030900000d00d9540802c010420800740100000c0c0001a140545406014130b19040d034203598030a40200c1c1c1d010158030000d5046101010342c2c201e260024403a05046c101d01d602c5282c1d4008074081110b1450b13013075062900d0b03d800e00200300480c90b040002410010700d044866200291624801e000b45 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 643274217 1250 643272967 643272989
    0x6150315010c05010f0507021002070b0c3006010906090501050d09060b0d1113050121061b03090b060405070c06050603031b150106090b040603050a090203070b040504150b04 76
    0x2080c4280d000d035915006495004008111800460003094001c00b800c0d03540034018030480f130864002c003085100725084980c120281d840e8503501c3d1300103d00c0c41c2e40146c040c41c0b0042c0101107192840d542186a52910b00102e0341909402e280890004000c10043e40c0042d0401c2001d13842006141d80040440c0e264658200000c50703810203508040c0b01800c0d07050110341e0003c0d5840c58050510030f03c0e00c0e034002c061200311522020015511800030640760b0030b019500c180c030410140540e138050007440340e001c468401c20011a03403000da0f8019040710070701d4941890100783c45010400c00c2261904031240c0c02a0200c03010410340c240003400528182d4000302c004d00c0b8580d03620119201d5901003059800c2c106103c01d00c8166a03a00c060342d107484d8034040110718202d240e20300020030014055022001a00c00030620b2a040c1494503204401604000c3c0c88455859603503c09140542ca051025102400200d0103032551b4900e4a8140000c50320101038840c1c030070300d200905003d236140e5a82200c0458404881d9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 643275467 1250 643274217 643274251
    0x1e091401030e0a140307020f06030c0a05070507030b0112022827092f0d0803070c0210050c07060c02030304030b040813030b192a09090603060e06061503 67
    0x215902d4020f42d2140034200301c0d41010308800d204c0c000002400c00758800d94858801b0344070f40b014000a40425203107421061024020f40c00c16901c500c026105d1035003e00102c981070b42d0360307071501e01c08441d00303801c01e5001403071440c066015418124042c0c815013025010401e07000382414a1071001101a01428501509002e43e5402014802e400c840500125075001c005180c00340c913007080601e500340808080004100981040e18030725080341c4044000103441c440e20765045640710885688000c000d68280300c0542c2c1c2e00c901607218001c006805559030780f11f9650b58887d41ca80d03140f800c48a540040300f04551080208011789012043d43c040340d42c00740e050380b040e0321946004a850b0007401c15096194010401c00002d0040802e41c450003003580c0d580c0941401e2028100b0740c10360304078140281942001e4100000000700f4000c0c45003580301c141c904688080d450380e110b41c003540c0042d40f0a039104e0741c440541da11115803e200aa41008084580ca501032946402003891800000c00d48c1418400d2144 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 643276717 1250 643275467 643275491
    0x1511090904081b03031024020d0c0830092b050f030a021306030908180307180504120207050907080a020904060e070e0f0a140409020d031e09140103 65
    0x42c504140c0d0f894102540d84034540300e45240d042c45494400c001ca00d080440404410510640c1482c22040443e4060706c1c6083e0384080c15981502e4215048450304002c10690003203d00203401840d07108180d01c0c280004141c400d20f01d1400c03002c083e210407015001f100c462408030085480100d0007034248108442d070640030460a64003405100d2060b528204000100b09640c001980107001800928800902854172260102c0c100c902c0400000c05100c010050404c1c54182d0000e004d001900083c111a909610756a13546212410b10749034030010781d100c0c070a00c010010034004050310140c103031000f0a00700389000006103503160082d00d400203100717052000c10340201c0c0580464100840141c002c0c4081a600d01100780742c00b5080303070018000740c1e010410f4505403514075200925000c000708400c82c880d003040a91300c500c0588811a580c06a40c500e002c400586a00c92a42d4250340251140b41c201402d8003402a00c05c0648480f1504004481c4e1080c414514000000700d02ca10007881c0018180150b18 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 643277967 1250 643276717 643276747
    0x903030108031c1404080307031a1c1b2c07050f0a020a08031e070206010303050912030412051f11030121140601060306080309030a0b1b0304151109090408 68
    0x1135900a108040c1d4010801409914030085004c1d10741d5503400c22103800350072000481c1162440c0002d0340320301e4900805101400d011a0303a2442401408038107049105950a1658034046a20254040c1000d800103061400000c030303641d864903102500390080c0c3c50510802000c5100743c01641d442e03a5004100c000405200304035014405900400203903503414800582242c10340f0000d09603076144055800074210500c0841c1d581c0c1203d505441e110704082d074520802c00c07051891001c1101c0c6110034440050000040c6820841d024042c102408280500c10349042d10700110b88440c0541301e0505103408424603011007101e0445d0b01c140d140d00503005801d103130026118032012014120106070001c92400d031001243e018100c40b01b5440c00c128455455500c1901c034003640303c07102c0d8950421070842000c41c5410f00310340e0b03126000207140481910f40803070142007030704203030340a5a1150f5070084031050144107200340c030120400340d414681048034810000300248001040240101c03804501c003031400341301c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 643279217 1250 643277967 643277981
    0x60304021507050a20031b09090316140f060f0a090c03121701050307061710081504050c18060d05010e010905010e0c01030c12020306010c140c090903030108031c 71
    0x4081650002c94131410000c481c4c40e4200320120300746800c07410034002440c000555114142c0c452246500681072003007040351402006002c107103240010030025a00401c1421000d00c550b2240e411103480f080280c080c1460301564130040b420380c1c0d2050040c04006070250b00c01030b83c451509200421007a115251450f030081190344014a1041c0106110b0203e0790800051241040d50b09915401e03030381e944e02010b0382c131a114032841020480c0e40c092070700c1901040d802c2d258001d01d1301144032911951911000c2c0f800c6203034203018040403061000d01c400c00000303100b41a2005811600c5100e0004101c05640082c50003a100e00e100b0b031001000700d41005003e410108401440d14001c1044c40018107201d400780641980c159002d0060007560402036001e481140e6140e951581c030741600c158075511703140c002d620140002e4140400401a103000a0b04c032071201540b0a030b004041d2070b10000c4103043c00780d030f2440500b04001030f40040c001400706a01c00006c1d2103000f44190024481c52800211100040c205 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 643280467 1250 643279217 643279223
    0x62705210c041109090603010614060705070e010308182409220905100c020304050d080c01061d06010f0f03020706060e01090203010302031e0601050603090f06161706060304021507 79
    0x400710010f000f501c5140140180d90425500465641d54160806089030710501403041c00000c0e01e0782581d820300700301e8080c00742203100c1d908a8603031684070102c01c0701d84402644201d80c0001c00150014000300e00000f44c81658809880c5149446400405805000180d901c080001100424800c0156850340c55411500c40d032414a640c034840c42940920181444250542d80b41c03086030000e0403250120322030318443c90040d0340036504090400c0c0420440d141c80ca0000d4401d401b05100d80700143c5420302c2401d0041480c928607030104074201c0c01e40b101c80d02e0700900706414840c00d080303078905980c2c02419084181c0114a070050340e80030b45161040003480a604003901840e100400441d405080364001c5042e00e001b14112490210075144412000505540705d040b82d4000c2c034010030550400f00051a0448036071402c1e5004804003441d0350b07140c00000c440e003c001c40d10140f800d1006036000070b1100006200306000a11a251000c040768592002a1000707009281c40804900802c200030f042e2014607034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 643281717 1250 643280467 643280471
    0x1e0b0a0f0209042a17010e040201110d0507020a0b070309030b1306150302011701030c050d170304030807090b0c03120a02090a0e010501091d06010c020402040f062705210c04 76
    0x200c0d610000e0b400a0180e04a0044d5185024460b510107014206042420300300300350013044c5e40c0c01c184608410b244090012414020390300c2a5140e002c0084c0500d41d010ba04640d61a6250f01c1c05004100002d60760b0381c400300600d4000c104c060046035201c1040c0e42070329005108444075488201c020440540c112101030300380c0f480d081ca115098a0780c240742c807084074001d91300e28a8258120b0400f0f00d8180003032000900e0480f10001c01c020314104951000803c60003038180b048c807001d12034240b00f041d034030071035049000030241c808100f0f1960300304089102070480d60551604114003070030401e55034400c072041c0b104031403040000118000d2043e01200d03e141c1d00074101c014074513a079040250080d00280501404550040c0c00426202c8403064124410240d0440c0f03440340380c40346001580c1b0902c0980040c4d8109800f040007044102c81c010544000301400d90b540d40b0034044410031010a191540c48415240c011341100f00b10303d60b00c04000d030042440c4180307211418516124002e1401881941d6260028 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 643282967 1250 643281717 643281731
    0xc0b04050f030408012a1d010302160b0a0c030c0512040f050d0801060201200306010c02240c0105180d050a2307050f0109050d0c0606030c121e0b0a0f020904 69
    0x10b8410340001c4941180070703504a804a40180c1040c1105c6c1c1c100ca85180004d81307600c541c0c03442120342180b2800791a4103050044c07628000c1c1b80c0e250b034800c502030001d5a0110f051030610080c480c1600c01c2040c040302600e001c02454110100c001c119105200707030043c0c81c0c400c400c0420f092000d40d103041d001c611303441002c559041d100c0000c0586040c809205010240d440c002c580d41c0d110490900012103000a11981032850365840015950b000d500314081e81c01608030808124072606280e1180468442d107007120361036860a038903841c25610010100005801000c00c907a80e0004c000a030242c00c1c87e05420420784070708111004440c45040030107003504601002d0b00b0819031002c0c48008007600380c024010703201f04c3c0031048042c1c0d0030b80b980d0007c000e29590002c020880154800c600d1543c03601c0c86000041007156a0751100c0b03a0100003900260f0001c400031560b1000c00c1900c681c80382c91080b40750000040c103240c5407035103503010f01c0080404070b6131604c13945440c0b684002a0b04844004000400800c806 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 643284217 1250 643282967 643282979
    0x30705090a060314030403052e090b22050304060806191d07020d09090e1203010e0a1d07061206080114070305070908030d020c0f03070803060a0b04060c0b04050f0304 73
    0x10780450310098580005800f1100e29804d408001c450a8070b40180080900e004695514030039000c150100d80300407400c5241d400440080c07030040c030006500400b903c0d01c0605204480c9006103001c00c2d00100e201000c50100c2d8005180071081c0d900707d030345c0c509141c1d01a40e038200c04075082c2800c00741c0f1048555a040e50205c4c030070f4000001d5002c541f80070314805e11256140001641c0d5100354840c0000414840c2c0420018005180c0280c0386841203d0f00303403100e00746850600c03003107904203820919601072000200001c85a83d88038100d0440b02000700c1605010784444500d0711154180255070800484803103072540d0a44540008005010a400810000ca0700a000005a1509030784000010b420500403441d80f030703c60040d0000750b4281c0e0000e10720b080c1051003008020741c080c0c000548580601404041c01c03003003c0c0b0160500ba80601800d659a244c00800c1016002581c0c110445611081c0028080c013640842c8032441150b101a20303080316102c5090491400c4604900707804548030008001c240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 643285467 1250 643284217 643284221
    0x304020607080d02130e06010c140f0102071505161d150301060c2a051903050601172b03021608031f0f030f03050307030b0603010308040303181a09030705090a 70
    0x40500813980141d82a4441e07490241d0b1031400d60701c20f23000842691400000caa04024078422a00c024012900c40164540a403400ea07000118240c84d01c442d03d100c1c04402c0c40480c01000c0c1d000084040d065400306d1400000b421403030880807008039401d0f985032609000d4451000c109042441300340302a4032503944190090040150380c80c00c4800c800c0b0301d10454041044101c402a00c020144201002c8506202c280040718009007101c034400b042a10001001c524240142806041c602203201005e82140120b0340ca002c40654201d02c844102c0c2c0e00d501c0e1001d202e01c01c00f06082c1501d19000d6914440095005100c01c104100540500d20001c140002402c01c00641400120920614100542d407a00070355039050383c0780702c003511024404000c0e80004e8072903801141d001020741400203c0c610b035180420709030b8209800c121201c0b03000240c01d20500d03400c00200409000c410319085501801e1440c1c251100a21000c8000901c0c004035103c3c101ea60244a504090700700a4110f001070f107003001840300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 643286717 1250 643285467 643285477
    0x70e07030f1a03010c0905030d110a0609050106060212120a0e0f16090f0213031704030b010e07081f0506130308030a0207021c110108130506251d060304020607080d02 73
    0x4804c0d0310745203901e510701c1d020b080c440c0c0c22514014064002003414120940d92820a10440d5500d401030052010009680d4450203403c103004030000110030b0b0600101a282008201007071550729000c3c003000b20181d100903c4d00754040340d1418080761240981c84401d01c3d1410000c481741345401000d01410320500201081d00440c0c035060b40c10300403582c40075801812403145400b045600807103000e0a00116100300d100c840d0303180540e04070307501c2c0550b02d448403001c040003a0050011140d80000707008000b503112480640004000100181c4d94071103510b00040e00d44113104050064502007201d041a414500c0c0b00c40c001e41e0082c1d0003580d80d20780040c140c0c0007903000482c224420107489503000c10000081303094003070060784401d143e03203414054030040d188218001c4c42d400b501d000081d0788100040007440028003d69100220302d43e1030584840c101414014280741c00b080180590742c010b140186c0d43e088051214040c0c3d00c0d42e03560784850001c01da05100c1c0c180d0142407028009050700c0000d4480d07000f00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 643287967 1250 643286717 643286719
    0x170403141f09080316170f010806151f0306081b0406060201050f0f1005040903021609110a11070b2d03040f02040203090c040f02040e1305070e07030f1a 67
    0x1401c1c624440601030100c078244400540340480c1031001402c840786400f0912501c4010703040c060584c81080302900f024031011280c05184422100042019480401c4101d400c041d4003140010345403116808503841c403040044000100001e01d140c003054601a80c0301030040c0c0490000c0e500c0a90100042c4c09008101c41003c1d4022031038501c9c000342c107a20611509010304030150b401000d646400c80c001c0583e07a006440c076180d00f0004a40003600785d442d031040301b03520382c0b10350054040d441c0f8182c0c400248003401e600c81c01c4501d0808130102800031050741195031803592800d000650301d4586102519040305600801c540b0040022421043d002d0140c045180d48090f00f2411840c10606640c1ca045000a40e03004003400d003042001001072a01da005103610820807800c03554050355800018064500a01d0302030404c0e580010b0074024229907074805588074145448010801403947d990603130300d461074420311140702e8081002c5004076209802c4041c00c0f906403941440300c05944c507260700c1d0700c409225840b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 643289217 1250 643287967 643288003
    0x6030b030f01091e05010e0613200306070c050f060708010e0106050c0304060c020f0907050919030503030f06011b050d0e0d2102101503260717040314 66
    0x450301d018014040c80c08042d601180320b84010000c0c606540314180032900c02c0300c080d529a00e5181190701c040155901c01d07071004d4140950302c41d81d81001d0365000c848842c25460000300c42481c07020358800149080d004155481d0007000c10b01ca0741011410a6403443c40d27000540601c0003441070300c9a0103140705059801c0b0043d81d28469995100c00d039154424401c503501c1a401c107200810015004090b24000c240c0090010868500401e000400182e812104440825030106109100303040c5582c007540c190002d80280036481d4115140c2c240e603400014194003d4a11200005000740d2181c03039000100320500c040e904540c10146855902d800180038030500040940100c00d0040c41d0480c104010190448026500266045032a032400300e031071901103055208468a411883e0303450702ca40051a60f02800000c0414154a04403100e000aa05054012414910780c0e0a00807650011070f0842c1d0f42c410ba460100211014800445006a5101034400d00c94005a00020200030030300382c002024000749 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 643290467 1250 643289217 643289233
    0x20a030518210c100f050d020f1b0d0e030c060d0e0604151404030509090417040f0e01050a0e1807171c020718020c120705070608010b040506030a1e020406030b03 71
    0x3072003c0403154200d0131300011700007070520328010f0041c0e00400c00c59005880c058039150b403e8241c40b509510005600d00703171078012442c520310142c0502002303020341c055107032035a81d00d00450001b0b42e880a1300e01e9502d10403c0b0010b00c1c1c521382015540007015000740740b02565013914140c10320070601c0c1104010908413904120040300e0890008044500c11645a1901f504201d241410302043c0c2100500c11102d6800c10218800000041e00180009001801003288520b09045010142000c10f80c80700b4081c200c602c100784040c02e00f124038103901050402030043c035007002c403070190310b0b100c1a03a00007014071211140705003907450082088040107035a000e003804800400802265510580d128000c15001482510304281c1d02c96002048540c00b0b82040307504008803a0184901030b88600001c580301d0b4441402013045036044103070980102203159101e800c4c80e15000c04240c4512006080401003503680c6083c03141204840400034070010b03000740442d01c0381e0315110060300404900c4401480380c4103141c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 643291717 1250 643290467 643290469
    0x305070e0a1a010c06050601090522150b0301030f05120f190f020325050609030a020d0305060d060b01032c010e010509100b0105221401050901020a030518210c 70
    0xb07164940a80d040e504c6140b14025911420001c00c0c01a091170304000349144002900c0d600d280300c0d000e210314443c1201070030440b1341613220b00300d400101c641044402403510401001d040c10007130b24110703900729100c81035464042c03500d04c1c00e000c001543c4040c441310100302d440003484c1113400b40c25800d02c5200d010000030103e140540740507841592410040e8010480e0b1810440c4280c5240b00411340c028420b800b8640a0351905d0404004407203803115070b030010a0125081c2c1d41001406048841820700304098103211000c51540301d05580c2c0035101030b445101d0404103074400d904c100d1801035030100c90b0440107030407980365902c400401c158899960a00c2501c012005040c82224090104440280498182001e2910151000c014240c0c140401440082c00a1002641d4901d8803102840014045401c00d680e501e0400d400b44500380c100311091000b8182d60342c00262041c03805415040c1291a85808240e4401320584602ca154005000484d2100002c0000079030104d10340e082c01c00d581d036144000b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 643292967 1250 643291717 643291751
    0x906020313030813121b0611030d021b1f0c09061709030f0d02032203051815040305030d0c030e070b03070509061204140115090e070305070e0a 63
    0x1d4058400103a00c21081001500100c000e000302043e050041c40701a80c0d42c42c991040240002064407a562091005244000d28015000c043d00203400d01100d686898060580d40c1d00512000840ca10b40c00902c8a11021004651440010043c01103482c001031000c070305401040076255400600341007851160000307014000200a039001a515030720790480c5008d030039182000c00707005001d490204001720001c1000807001020302c64000c440160f034a081c1004407202c107000c12624280c280d80d1640040d030010364414100d555004132505580200d044e2500041c90800c4041546800040c000400100b002404806000360644080003040840c3e800c883c01e170240ca2002500d032030942c120040074080114542d0285821080e24034000341846034000c00300741554041e81c440c040e100148006c0200300301d40c00700c80a40c07d109440080c0701c0039605161341032010015001e0702c40c0e0030f5156445000c0d4480c0c100000001560480e0465034459940c2c070030301170001c4003582c0f482811401c000c60301c08416441 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 643294217 1250 643292967 643292977
    0x11e0e1e0303070618080a05031b07200316092a090501050708070f060218041e090f021008010608221113050405030d0e06040507031403071403070309060203 69
    0x24001c2d41c0741102641d6920000c0c505044499041c40c400c8990302c011818000150440400540b42c455070b07810805821010307944001d1344425402d10820600c2d0000e58088800380e4030500307000725880e803440c220300020300301031380d8404401440469140018840d8816000360300326401c1c01c0ca1840e002480003070006400c040116100d00800c10800003041a94800c40051420350300500009003800000d55500301a241c5030b04054402c60b0700418604c11404000d1030800000300221020031681140e4035047c6d50951507001c0121019540d4881c240911041206801040343d00070013090071a00840806048100c080c0591000501064006a0901e00190541c83c81c0b103440d480303540640200c0d0f42c0d002c1c0d4a0f5501410300740c12030b5000808883c000403d005a81c0901e1084001d940c4503224900c01e00229402d00e0035081c6194040c2c03082c0030200d1804210681501d411107144100d50304c102d0b00301482d42c495000002c01c904080c0500c4050040c0c00303c050b08210b8441e035180110a40d0303c5c07004907502e01803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 643295467 1250 643294217 643294219
    0x80a09050406081c0207080a0804051c11130f090507030c050102030a080c0a110f01141311270a05040510021218100c0309020f06040b1602011e0e1e 65
    0xc034200c0d1a10031030b0720419856862086104846e4080e0b01d0303000007403c0c400003d130101d80580d80403405218901d8101c2c110421065a805119000d8481341c951a400e442d000000900520131401c44000000c043e4106461388441d001e400d11002d02d03146072a076551441c03440142c030358100d0030201180c550f01c0031088444014295445503015261107141c00200c0c0e21071903544050003002c82c03585405207801e108017046c00074000c0001852004e048800d05043c1401003011506240ca0064100000d203001036000d114030054601d041c40c4550038400c0d0070500000c0904598a44954040001070b003c180c0000313204511400c240c83d1100a920000816402440e00c40348000800c040094a4403401210b00c0714106500c004403404801585c442c201240d994940c0ba03000a6154500f400035424007814400210a06480b450301c1c10b0300e4022072503120700401c05101d00380d2039024070742c0c000e5a02c1511142e07041c10030036a080b10000241100900040803041aa0b80582d5052050340070300d02c1c0c00d66a000e0b100300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 643296717 1250 643295467 643295473
    0xf1e050c01050c0304021e03011e020c010606030e031c06090509070f050301050c0a110c060a05120c160b150603070e09130c050f0a0e01080d140306010203040e060f0409080a0905040608 81
    0x280e00b2050701100540b1f082c190340c0541d41c4031507442e09405581110701181d00c01805c0140e075251054112820341d081900100240f60130504104c8609200008840940011550162040803104109805090a68805900b032810305007031241402c03002c1400b00454908039107030b15442c0d580b4800c1c036003600d030b084460480d299800c0c000303460b09034020202c0310b070324035440801c0c1c41c104500b00c40001c00030307003016840000203031000c50301e028009440300f00365800c642e444007901e0400c001242c1041e2150f5051030000d005661300c0c00880c1c0001c200200c080c11481e00200015140d1030040e00040c4004203a1502c540307c0d01c07415020901810152401c1c40c109500040d00b0b040582c10001440344a00248080641102401800081c0420703442501c901900c44032010b0449030076031200040010301110300e81c02d0301e850100140001a80c00108850840d0a028450415680c400c070024484101c18500d0a4000b800d01140d82e04011100c002498581c4058503440003180d154401d1104440d0340303001c1c3c0090340d8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 643297967 1250 643296717 643296739
    0x5090f1e06010e1905040b120304090e0a051002120c190806030c1306060f0f1b020f0306040303060e0c18040b190e01050a0905160f1e050c01050c030402 67
    0x4500c8925032648401c0604203292401580008a000b21001c22030384015050401d80c180003515081c0118039005401312018140481c644c114030b42c4a01c40c3d44039901c007450f99001e0201c0c459800b803052080c20764000b4251507040c0003001e0141c001e9400b07c0c88070391800c100e210000c3c0d407041411055495004c01807403451074000044109a980c01400f03411142d0603c17600c540ea100c207994007101070201050192002c101680b43c840003400f0903058420803810301ca00e46c450003242e0f03907014040b45104a090b1007440f59442542c0046040c0c030803114a21501802840208028503030107800c102c08132707080600d00070016520b00d003800300c140c040c1036130500048080f2400c1c0750703907032416030810201080000c2146901900e804130450310080154007083c5010302d00d90040003640b400f65131041c0103042c8104180440d18017405000c2c09403c41301c01d05028041c44040d100180c604c42d07511842030482d02401c88442d50b003060700182042d0418882240f166013070100081c140180802960b005503400f4140140071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 643299217 1250 643297967 643298011
    0x2001202515060f0315020c19080d02040303020f06010501030b030c0f0a270c0c030801170a06021b0705031501030f06140f180c100f0504090204060905090f 68
    0x40311103518107444000c41d010400800da9881e00c0303031000400480360a00c5a4500d14540140745144001111545601c1449004051000811038509110103040c08001801d8189865052400340c0c00031003050a10100d0040704140e0001484803460030100d00719141681e0b144011010354102505164040d0040394401446007420f4000d0407408000600320011140c841c4100b0b000344824898402c6803103085801040c109403684258054a8494a0040580c03005900c0c05028a48180310700c0248030404044050300d40300034048560040ea0105003036503281280889040e019040200030079090103850780c00200d61a0002d441042c040d20f5440444a5070f03c0e50f2151024130701404001d0f0340d441e440d40b01c0040700b042490500351241441c1c0a8040150401b0455400307446a43d5a200030740340d0105004000a594902c440c905012562030008101d1841c208100c9250045a000805117800070401181968014042e2020b45400b07030b66601c8655070303036600403090340c6040e2461000c05e40d40500e24424 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 643300467 1250 643299217 643299277
    0x15010303050a030e1f0b280302060306060706090606081629070609060c1101150302040c030e011d0d1701060309020a03020d0b090d03020a02190201200120 68
    0x40055620980e00c03c00000407a05042408a0700d0000c0c03000e50f035030b06c410300030704c1c060a00f203035007100c8180d4525064100003440c078207103962400041d00ca0030002c4001095980c03090225489590701000900200c5080d1400b007016201901030f20f0040d0150a036080c20455000d00d8400850707041081c206035503030790038008500240c064041c2d24018202000160f0204c0c400340240c041d00c922032a0001101800b00f0401031007507a290fa4400c4060b414218447c85800ca5442d2900680f60115400503008400320030680c02420140d44e0105254241201c09803010402c000035040408824240c0b5001e40d0075410031200d44500308620090080e48200601009200c0da020071032551014240450340c0e500e980000ba00182842c000300c461190680070410460014002d401c0401602d0034103505001c0b00003001394032250b600c90003950020799440d10f0015a84104450016001c85424920354115601c5040d400703040c0c0301e40e840c41c820118840c0301454110703810444060702440c04110001c15500024644 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 643301717 1250 643300467 643300481
    0xf070203180d02060c060403120b01171504020c070e040506070c050d050c0127021806061c1103040b100806011206020c0c030303010b0703030e0c180702121b15010303050a03 76
    0x81c01410030301a15005e0b510800c07100b0b00440c041c1e26480b89052881d0060401e42c1c100c0107000d810001c4080424482c001e200990940240c903000300314501115010100b0028060710056103414440d42e6400a0514080060300780103034001c405845c001d548490042d40e9003021a8001095540107101c403200c824800c1015000749665280040390030586c1444110004803038103090250058018800c108602d89960314820000004101892621300500003c103d030040288414500540e031247c020b014405a11032003030000d460b440d44e9140d003050301340b10080d9003007146e04200f107090700003001c103a1401c0029281e040303402c2c404584081c0c0d005039030380c0e0019400040f15401c01c0d01c41c20312081c226030381c280701941c0603015200519031513412a00f001800e54500d01018100758000c0b00e280115a114140d0600c0b41c08a5066102e070300c1d850b080304c103d01e400e00c0b00308140e20f203560104160a14180d5080310b1180e00f0800e130111584a03115000308681c0c44820b01c8001c0205800308481e000c214000d0300018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 643302967 1250 643301717 643301719
    0x3061602010e07170c01080108060c0706090f08031906030209160221090312040e0403050922050a05070201020a0e01030b040b1201020a0215010311040506060403020d06050f070203180d02 82
    0x10452107225602c1601d04002500080d55251aa50001883c0c1d14200071100245000b464092a01e51501c00c00355103a000c06800300f240d014000590350f0600280b1340100c84903641c40207002081f80c40e00d0a04039115001994032100f01440340d05480c800f41c840d8004c2d10252500100b50400701d44503a9880c0c0f0855030b581d0103c1055000390003441041001d0743c41400c00240d00050100d80d58000f1000305802c01e0300380341c50326560345000c1c4000c1c01540e00d00b10300075a000d5414100a55514500800580001640c2e0503d0007080b403800101030180d0300135003141b4000c54480100707000b16101d043c03040e4281d0280b07100f61070000d03ca00c1c8440078503600c2600031982c0500058000900480c03d000813a905080401411100b81c0d00000c40500c1c0a80c10440d1035059800e16200c0c402550560741d82d003d8036032074264024442d07038482000c58001d658000441e00110303402801000552518501940030380412582010001450000995068004070031184904107001c100d009180740c1404104088110120a07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 643304217 1250 643302967 643302971
    0x61505091c080a030501080d05040807330f120915150b0d0207230607050d060b07060e0f0c0a0b030a060909050a060c0e0d0305160c0b0919050306160201 67
    0x1201c00700e01014002c1240e005a0b039800304403581405c03440d900e0060786005040130080100b004201d080c602154800660301410000c40c6080044040c807000c01e920b0070b240c846a6a031541e61840f0300ca40180e00e8154881058071120980318a605001c0201c070720205d00540086032080140341d00202541c01642060782078036070f00b00e0302c035250417036890a0707040340c41e2403030025900040b100d0502c034a034070024010b50503034080d44103003645100160f0b45501007e0702c2902400780125100250b03028981054001c0c0100852498440c00c03141020f2000d0301c5044554200da0250301d40c003010006001c0f649641076031001d08071030f100e207160101c607201d1548010990a1016a600808108001d81d40070700a00c59001e40c0040401c25200e042c4a03003100c60200d800014881d0704211f03000303d0b0302d4074005524200d40501b041911000c0401c00300811851480b402001103d00d001d002c80c0b90309109001d0a006c040541d5500003401400358000d84800036801a030707a0650088001454945006510950100d040d00c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 643305467 1250 643304217 643304269
    0x20f03181c05090a080a080f0313171b0c0a17010902060304030305040b0721020a030e0a03050309010c450e01030209070e010804321006150509 63
    0x2a095601c07000020300c40010b0070002c2c800343e0520b090080d1801410303036a80a40001182d42d540d840312445114030000061201200141105603402044032070b890300b00c650310065501c1140100362680c8909000d0400301901c42062440d41d200143c401108000a00031100e00d90810308103812004c101d0f004980e0a40d2142c0c04200103072500c101550145210f5100840d843c2010f240c041d0941000a004600b0001c401400381c0c03202c100c1d070244400f4018000700048c0c2e03074114107000318081c20014511b81003510485d100c9604143e0701100540c030848540380200840c94040c201150880202d00c0026900404040c040c02441c140007900719a104617285415010b081c0074103c1d5a0505480d8825040c8030326545c010000c1d41054000568841a6884d220200014000010748000c2e0007a00c007034a640c0450010038801c085d001e0030180502011010f8044201c0028406580c07901c01e0041441c415081c01c42c000b407140c5c00c107006460204203d444550400106905009507520f07650b291031409100c1e121 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 643306717 1250 643305467 643305493
    0x109050a0203100b0d1e0c031407020a1b090e0c1c03080402310c03060506090603160504080f03040f0609050108040b060a050411030a06050105130501050d023001050103020f0318 78
    0x901846d03103d011140109403007100980c060300300da20048010068280c0f02d02023140442d40400d101300120740c4070202224010708509000400000c0ba000400014135007070100030644070019480700c814508450f512000071008941541c0c990070f54400074041030315580410010702e0041c50507118290841e050b2210300c50803051210300c0e0b111588400d8021580c402c0000b0000e0341c14000e6501900003510094949501c40010901c10302c4020a20041e884140600c0081e851280048400420101e0111000c0400f104030b601d0301c0c3d038400d1044894002031000c0000302140104d0704041100c20503100d8516517540d6848005052034002c1c80982c3c030844046010929503580d1088010000c0c4070203916032613103445480002100c4842e000f2070305202060050b4407148611107103442c1030342c03400e03e485a15141d0603058480a800f407044641040200029000445059040c0341c50411082c1e600000c100c5e40d803203005404901c80c0e00001804200c04000060b681c04003d00009800210034088804d2400119 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 643307967 1250 643306717 643306751
    0x16060504210c0602090f3c0a0501030207020f030106180506120a030c0c03020a12140606130e12030f04021e100f0c050601080f1e0319090f08060109050a0203100b0d 72
    0x601d129a141c1030151041c101c0b40c50307c2c10b849070301281e2000b0310442040001c0001c3d86a401441074904061300010441e0464417062041c180020024000740145911242c0849010f4181031202d4040c0380752000080c16031030001c43c0062000d168a020f01541001ca450480354107074500b00540781c200303118070300100503150f40504034000e011440c0e582c50403032110301c0e01c0d1018a4141320007100c10346c8104148a01941d940c1081c4594103c1041d0010303144014143c49402d01c4e00d55034000200389030110401000e980c0c3d10030302d644124421225451007040d50303420450501e048085171341e04046400c0705002c0c0180a214803c00510890904005545195507000e2521609802c911442d0b003019034900c41d188000c0140c00d030040d1240e565400708100d003094580da24001c1c44000201d09200d001c03c18001c0f030142e1403100103004002c5850a0060312081c4880d6100300a04c40d1500365450100041c1d400c910714800c0e03e011b010345010000c0d0282c500200b943d1f29401ca02c6403209400da49040c20000c600e251 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 643309217 1250 643307967 643307989
    0x3030a020703030c02010b010905091e190506060f09060318031b120f0d022a070303020d03140604050901021c06031406090304150516060504210c0602090f 68
    0x180901594944091400070169498241c0c503000756814024205416070b00a14020180c0ba025030320300c0ca841c1d40303080c0381104041c04c205e154400d0400c444280440404e10701d650703d982d90368600040c84140c580200303115281c815240702d40390210041c000c088052401d28001d40e0030064610101d40b91204421040741140d0100d404500c07844461241742c203031104284000e0b051aa8200b00e1181171190410440382c003840340f1408480303010ba00160180225500700d40000768040303002c403001358141c00215020b5881443d0b0006030098841c0b0350591904910a00407605036030180c000e00c502503101c44007400040c1a001d040303480310b550280705060390728410040c041c800807481d8901055691540c14880400c8840901040990f0801000c001c19150000304131011210050000c4c240103075400c504032030601961948000e680d0100c0400d1041c0320003608106d0213540a01c0c601400c04030031804214000c04114010ba0200302204665408204580d0180c00f143c01c014102c00158200782000030712034910 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 643310467 1250 643309217 643309231
    0x1080c0a0909021b1204050d020d1a010f1701052202010e060c0c0405150901032303040b0307030b040603020102210c01050103031e050403031b060f050a1d1f1d0303 72
    0x41907403a400c40ca07030200503142002c0d0345c00340d140d0710385070400c00400e40303a040c03000c806401806000c1740c44040001c90403001c40d00c1d860f5810a2a900d58403800d100c942a1194843ca071a40380030040c00c80c0c0002011721540e401200400d420304a000030a0000464414a0f034800b80d043c0036500c0300402281d21400c0082c0805c0001d030000d442d141c0c1084080000311040580b03202c64000d981100c00c00181c840d8880241903940140c00c290402c2668800407010316008100040e60b0300012034001040a41d1501850140ca4207880c1406140740c03440c240400c450303080c800a070050740001c0e010301440d02018142c0030800080c078102860000c9500006094600070784c800c900166444a0074030b2006c07009600c80100310464030700280761a180d6100200500074500c5550031030200c14840034200001d503481b003404020100d10521444c0382c103120800007030075200100c81d001e203610a8000c01c00381c00464000443e10a016039000070140c8007420318014141019281070380e080030381040c000200200095442252 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 643311717 1250 643310467 643310497
    0x70f140115032301090311150609060d1e081b1c1b051b0907050403050604020f01200d08070c050709180c291c110d0c08010312090501080c0a090902 65
    0xd08151f01500d00156072120048a0801000f448819540d0800b50758009008032508075803022141001d8540408150087c41103542140c0c1c0c2c5820400603102500070f415148840449100d5000c21a5844003500030746c42c3c0903e00d40504038810180101d0314004480c400b00c00e0509460581d540d607601d400d010080d01200b846116031844040d2030126003c40d4003100519109080ca4903690703e071943c07481301500080c071408500c40a0021130f441581040500002c1404d0500140300c0c41801c2034071481c52801c1c0e0700010740c046001a4a4038041c100c90306003281c1c00001803244c186400703203031b40007424503c0c1914004406026100007003a030815140d4003900e8040007504003d2103520b407000f114040c2643c5003810200622800b0303902d52105440d503040307445030306001c10800e4592000709600c0c4110a102c2164034a040c07242d040d00390740215451305a91240d00102c142d400a0102078035000c5030352080740d002800790b8000824506194003d05100726480c18103403062616000f248040c0e0308010104501030b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 643312967 1250 643311717 643311737
    0x3180b040e06010c020607060e010b090c0a03061a040909110301110c0709110a05130512010f1d1e0109080406030e0d0c120e030c0303070f1401150323010903 69
    0x445040701e682d0000d4007400d000070b2007070b000c1d8003040c00c070301800d10050501e80d0781d000f60405140003074007d140b8000d401410303d049032070a0b40840400d600301210050000e850103c02184940b2085145418103070658191811726280c5510708000d0203080000311041d40102501c0440380d1024040c9035402c41e001505141c58014034040e00386080104d500541040d401c0404500d603241a00013210340a034203902d00030b42d898403a90160600d004240d40800d400200306006e8010180044d400300c0c2c03419400c0c450505c0442c1a2110014496040b25046002a04030070600b400401500405081e001d80c00310010410700c41c280c03114440b5070003035031042c00482d03229003a003c015031050040311f002002505144a808010f511034216a410100c100401c0c004a110035070550b40d420001010075440c010100c951b90207071460035000b00f4030290300444c2d03042e07401c2c00680c10844d03041c028100907040c107264540480f8a15114000105403130074041ca202161902c84203e0801c0070300400e00103d00a03216080c0719 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 643314217 1250 643312967 643312979
    0x206040b07080609070305130c0f05040c0305060a0504050712090c0f081b0609030a02031c0908070b07060504030309050a260f0f130e01060c050601050d120c03180b04 73
    0x9034004010303108002d544070800c4016514005200c0d000101841c002038169694200301590340300340d80000c5c01ea10007403e000508103640b11004000d81c1d001761800c3c4010301c0c0c1d0036000c2e0705840381611070640c4400206424440d84c00d0a0788241d52041c000d140018004c1d0030038042008440404005807240344080304180300c5403a441c542080100000801011008102c900075072100603d03186441c0301d500d00080142c55a5410095a1110b0b45c00a0a0703882090702c031071400c1002080d040d44100841c420960000d280c074804295a0120341c50140100e2a001c040c0d07407403100030600100200c084c15600e801110100d48204459200a8826652100d00300c17800b1195040b040f10081c806032441d8020030070344800c000420140c4610081184c2450b403a030b0708400d00030750b02d150380750405030404203103800000f121540b00e000c1306003150160081e81d6143c0d0300d88003407020703070038110740c0152410006034140c3d00010311030300c0100c42c0d86000c0e1800c840f910410200404486049500a01e04520042000c6c451 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 643315467 1250 643314217 643314233
    0x2090a0f0615020a060b130f0b040513150209040f0207120215061c060608011104060f0801060903020f030a0b13031b0b0705071a0403120506040903050409200a020604 73
    0x60000540c10625100d002c0400a40e1045079103c020501910b41603180c000d900e03071104561030011060014040e00061020000050030000078043c031032030401020907082504c040210310b696402c915070b01520481c0c030391008003035444503424a42095884810054511041c405014114411111081141314240000b442c10303040042aa450900d85000e004c0155282d035203100c2190307003c000349102c02881d070800e0700c02003003154400c091039400d01040b244810202402081502c0c010744580350108942c8000319400c940034000c8002040e401d420510240c82c2018030400007290080840d03e940712150b866a4a240c401c0e1441c041c04003599001008143e088488010b10181001c1c500314550b0040c1c4801c414403074080e1040c030622000040b06070034440300e01c2140d40030b50760002005015045c85c0c41c009140c11010f81c100c90300c4a00d0100451541d2419005030145941c141c1d40f920b0401d401c04582e01d00070520792030540c074030140300300e403c2042d00702c52405040e0601f8650090156460241460302b1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 643316717 1250 643315467 643315469
    0x10321093209060f04090305120a050403230f09060904110d0e030f18130e0601170105060d030f0507051603020411031b071103030d0c020c1909020c010902090a0f06 72
    0xb1146461008006498841c52052042508102c602003041d1590341401d0f84c0303d1203003a910404010000301040a0b0100b103401440c0110b07c41d41c0c44801420080103800c813a04105280940c0802c1c04002c00c080001140b4041d18201c0c01c0244060304c0d04da1900005411186d5118588500c3c60011942c801000c4c03187c860720840d0000710028600d402440d00351b45645205400c040c00f0100c070360018000440d12802c1009182080c41e4908102807541d12101d1543d40ca000d200c0d48042d0809070f007810003c05010700909004000c0500100c0c00d245d105ea4083e560000c034000f0f03540030030030244921000308508200c071a42d10612044e04901711821401441305450f0290601810504100103010118420510580d0b43c006050003c5844400c640b4204590180501c84660315220100700169212140d41c0449201003041d02103643c0c080c0e210f000c1c0952841014440c003011200f0340c2c6c040204070815001000100400c000018211030f580d0300040c0c01410960360a070f0071950345c503440d03d0301c00554411a4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 643317967 1250 643316717 643316719
    0xd1a070e150418020f2502030d03060302011d061e130b031006080c0d05010305030c070f0b070b0415180309050103060f05040c140f0a0311030103210932 67
    0x9103094102103d04606405100700803000c0d41d800a030300203640c407004041d91810003c40d030240f54151981c032008030004003c11400c0c0d100c4d008003001118868028890141100d906850b4842c5d04504031140302030003004102e8040c0c010208200c03050703200301110540400060024511a22002800741c4d4050059076038011100000c0108181300b0500c44c542416412501280341030b84d120f507035543c80d80d0300c00c2c02819000c1d484107080400200800002201410705d03490f80c031003110b10303055071040011002e0040d881240d407850b0041001c08003141412070101e5210740209401c2110702c540e00785000c03c031003540c40280304410480070303510300300350b03020481d100100024602031140381d09043c2d015510f140c542c400c2c03501c1550350704a400c420500419003685800d95242c0815100c5004c405841d00e580d2040080c0b0001901d403410faa90340213104400e40341600d41140f003902106940c540391425102c1055a24007e100c24000b00151142c10302a95400171040040c9818400c0c5d800100742182062080a030b03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 643319217 1250 643317967 643318009
    0x90f270a0c050d0c05060703050408060c0d0e0109020a050d050c120f0f070608060f030a0203070311030c0607120503072706030e06131b1a0a080f04110d1a070e 70
    0x1c400b044c0b403000350b00e003074417400c440743d42c4c0d1543c2c503240945680c45540d1140d170306801030f102000f02502c2302c0d1002e003d480b0840d06041c8100040c0240250883e90108402988808980418002410494492007903a8800c0c0b0454042c06040380014203140c12140e0502101e92002c660030300c0025052009100161540c002807440324208031016166400042c21140034005043c0700d81e0182d40c01300900142107030040c2c00c0d10030080c4c0b41d042510070306018a1103980079204401204525042c110f0445c3c0c1500e4011410892103070140808843c0380e8800390864040050444642c0110780c110124071403500000740e000c114181c5001805426a1140c43c10701506400050810a08690060b11108141c4d4032000b454100201c0702c108500d185619001903000c0c5003811090061512884002c222000480d25203840070b0740c40194215082008490040c00503105007107014007400c03e2a80800081d10801780911a282240c1424206213002c0340d807400010010030400c607440c240000c03040da40d500c40b0a14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 643320467 1250 643319217 643319239
    0x60c060f06010e031b1005071a060102160e0609040609080f070606060f051c1d15060a052103070f030503040c080609340b0406020d050405090f270a0c05 67
    0xc48201e014100e90011b00881404e500c0c444040c2c4280112150b4a910541d10b05640b040c10303007800c440b0a4100d907020b001d44150940b201c0c0341503010203030800701d83c10801401d02a541e0003040c070030a00d00290044030201e07242d00020b8002400203000d458481141c40d44151122604e06211041d11540d83c040d20078031402341d52406085a10208558011710242e111541c502da000a88400810b601d1140405418074080341d14210800410100c441d03c000d50400ba00b140c881c1004c000e82094240724040e840624084102801070110701720081c00340807413040c0ea040082035103400e1040c101203c2e00f1170002e08004104001c01040c3c01b4800d01800f9003034001c007160728080880ea40e5034841404401400041c8005003141c101c16101c80500095140b540703800541d64a803005002c64120b4000c50000d80520281080c009126209940c200d50000b020a2096103502003c0c803603855000c1c00d82e10458640c100d51809440c01e019040c1505003518008200c02c401500741000b50042030703000759111b802c3c1046 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 643321717 1250 643320467 643320493
    0xb04350a1712010b13051c15140612071203082508070302091c0f0b01060e0102210909090d031d030304021c051227130b060c060f06010e03 61
    0x22228159922552051755440c818000411030085503800300341d2040400369200001035030846052822403044d265080300e20166031b030100c213a030210840c60042140c10700c00540d491800d103ea0740c100140b0a001e031002580c65003580344600d001c50304141c0200300d01c9824012001204000c0364a094140344240c9003401400000824030000540843c081607004a02c0612542d242d10305803003018401101c3c44080611032070942c402c3c0d2041c0380c01750341c07443c1c80d64000140c250280101c150f070008164054050a10125484240900382030503030f4001d420144010803554481e0b0240341c5c081c000e502c00804a0002140004065070729000e1094041101101e44030041c54002040e81e4200b68121040e42c00c0e030a020a00100001140714040d0a13441140b00d019013011503d0f00030000300114814031846904c4190182e0440c91281c01456007050008030700e160321800b01d0b030040e001d143d4000d150900c3d028020080070b15004043c0c030b0106a2000d060300744640c968104204241400d01540a0700c0c14180c850 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 643322967 1250 643321717 643321747
    0x140a02070902030c0c0a060c110a03080f0703020d050a0f0e01060605120c091c061b021f1104090e060f04020a03030c0204020f0406270b04350a17 64
    0x710403036503516004404039902200390f070284c616692403401282d0607a00b050824402400d61015058046107240c0e4440c2c05000c00810024110358047c3c840355030030748407038224051101c00145400c08040d824400b030b08c0340c0c1c0468011140900500c07000070038203c0200d031070041121000c249100c1640c0c174040e0701304501d41d00401031320748048459910300459541c2c543d00344d030715200d2072041950000d900b1039000707100041c40b001c2000b158080c8901300aa0310719400130400341401c0c2c43d04030340940d200802141010081b0340480c0d8022a11403004a0300214840c4020030b982c00c0764015000158440c5100c09075081c08100d0144d2089030f07051120003a040c41e4000c24001d490600000c0c1c10030034025090015034540790103c0b10000f01c80f60101d80d64540e2403400038082c00c0c2d0b540c6010100d1300e5407096201107544000007001030f68160303500e081c0342515140b540c0058020301c0301c030345111700803500c10143c07000b0a40601000c5403907100060314441c201031034500c20b8400070418083c1040c0050181d074164131620 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 643324217 1250 643322967 643322969
    0x331031b060305150607060b0d0f14070311040c090b16060b03060411010f02010209090a0c0e030f0705011803060e010c1e08010302040911030109050309191208030c0c01050115140a0207 81
    0x1581c1450761117206d0309000380a0100025050f81000d0f0760390b003002c200a8031003e21061140101c0d43c1d110507800710010b10351158190320000d040025403a9800e0344610302640b00c04407003407c0b0f05044500d03583c0c80c0080026900030090542c403481582e050b0006000803402810520101103010380000d03e42542c80700030150048080e13904100d4850143c2c890700c0c1c000d504072982200010042d80d81442c0030381e0260082c051140035440003503450800d01c011030800040f065416014040a00119801c200044441d241c09410907080c0c5c800302800017002c6030303980c8130b0f00f1250011640045404101180050320702d009075154450300005419600040075070110903103055030780c1190080b4400c203060405103d01c0b920094820f505500c0d054805040140000040c103d4080c20340713140783d01e04002c80c1c90350384135440d0380f2850300b1384081405a0300004003400000c5138056422002c2c1410945004006421507009800030b041c06034038071020b1440690400d01c01608201c0511030745140c12110b41c4029150582 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 643325467 1250 643324217 643324219
    0xa0f05030c210d09050712060209150a0c0b091509030a0806120a0320010e010c08060a05031507031b0201151a190302040b0d0209090f06030331031b06030515 69
    0x71360482d1104000090160b0350042010411211309021141072040c0254442464144618164102e10a0020ba40d0342940e00300c02c1030780c503180e562201d6034a50101c460001010300c4418011400300340100107511041c1e5026683d46402152212400c11028241d42c03030103081a482820120140c0010800000320607825507030501d0581501c2000304042d0382003513021007107002203509006a44401d20015130110007150b50300c0d51003c1c2c403510740009204a001c12401001d4054204a8880741c10310b12005159401040900e4001101100c0090058100e210010103a005075103039206004101442c2e0024009007181071151a200c0491070700c1c521a520a42035440d0240102604241031140258140d500070300072042040d5540d004007081c04005c0d4042c80d0154459074240001c00c0c0042481c01141d0711518001c2d00951400000703216026240b0282c42940200c2800c940500581100d6411544021880f4050400e11385203100080c4c007540005801030310405143c00c040002200c40d000c03160361801c0c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 643326717 1250 643325467 643325471
    0xc010c0813060b0301140a0c0f1b060902061b0a0507090c05030402120f060a0209090903181e060a030e060f0411060a0c060e060108120405010806040e0a0f05030c210d 73
    0xa100e804130340985500440d50b2180c4040d0010016400e0080d00705510b0861259101014980350440987e01e401d10039600c408070006888000e00082c1c965400074030141e00050100f41824041c6895412814a640f05202d20350081d5801e04100441013240d54064000210184051122003034000e049020003023001e8030516a0310507030b0428800038002a18849000c0d02688c0b070b0340c500004040040e50145c0072490103071001c1c0c1c000480520003c0146d6141c45d445000c0d0b000c0201e400820401d00c003036610784c00c080340d03058000110901d59403040103001001c03540d1004182c0c903451900c05400e040c00100410648060720040100280000400c200030200440d9059240c100580c401c9501030180003008003450b140420500880d8800245036048881c0b4404550750a2440b8600b00c007140035910030203001c503181174080390280c038054001301500c030b024404482e440303112515403c110303003107840040d105074000050440700c00d4014000d0600c581c8c030103114251b2280b00400c5650f0203100c2d109240039010b03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 643327967 1250 643326717 643326731
    0x801021b0a0f1e060c26040203031e041203020a0314070b0105130902030712050d050a02060a02160b0f0a150f171507020607083d1206020c010c081306 66
    0x14460085043c81c180d0014030400c49108545006414034020303d000c400d42080306030342848910104051180300d0359004e0061402e040e1083ca41c01a41c80c0c6030b12908650392800d001c007040a5043d80c0c45124124040c1d4001d140c00c0c1084d05015005462032000c0e000e41c01800c0011001040b402002a81161802d55800c1a039500c211400b000409641000a506010b50710002034158001d10070044042d02403015031304120038a000c142c0d450301c21441c04e8005a040000000c0d039640d02c80e07025140051003c642110140700c0c1e0b58a110500c0d20456000c0300b425440020700c2410310f240d104100300107900c095001e01c100c0c14144c80f503041961a04ca5916000312038480c0c1aa1150144450014200072060052050420400103901d8203000c407194400a8520400500012950340075441e8040b8500300280c1c1510080840c280d908142001d4481500340d031000000300c6d0200e01000c600c031180a402c00580310004100100e00b03440b440e8083c6c8003049100020710240c0e05000c1d0070140c207a640800009115 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 643329217 1250 643327967 643328003
    0x20010516020a090905031b19120e04060306020a08070e01020304050405130c060504060806011805060a03381002030f0c071a07150603080405010f02160801021b0a0f 72
    0x9282e054102410079030030b041c002010410000060520000388602440c8048100d18079542c0e15803d11064403102c24070304205030301065035980c0003080200300f49413028818032100c004c034060720043d9104940700da6000481c00c038010b5000f841c40b034201d1807138038060ba98800c000c00002d65138003c5001c2d0a12980ea03a0b00421075041044140c10001940a07010400e07040e620703036014255410502c01c039004582446d0005000790b11070510b404001d07508030030029880e807e101c18005541c000310701e43c0080c50380c2c450403095030612012003403d103100003480795a41048030307503000d030303100110364025501400503042031501480d00441509c50191203c5001074a940c16090440e1904105610003520000350307109250142400100800d003441c043e145480498001404020481d6094400a803d02005000c02d000075885a240001381010500c115203044820500d200d010801591100140f40e600140040d1100c0c04100c50100e4081064050500c5060725141c508a004070a00d0060010840030058221 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 643330467 1250 643329217 643329229
    0x706120c0509040f05063f100905070609060201020c10020a09030b1e15010806060a09030c0e06040e07150c0c12110301060b1c02071e0f2001051602 65
    0x141400080c8140004c081c02c000d078000401050320146c1c000c0b40440040c2828180380c0114100000120031114036038000012810302c3c5203080c2c0d0420284d4060801c4501d415030650040e40002c0f801000075084052034808003815280e1517034070402c25a4010300c8035074001c81c404101401036000088000d130340c82504030302c12101541c29400040078240c80600f803060f100e1509011442e2410b40c103003200201e860724508000000d039800f140b1400603181100058003030600c0005030842c050240cc040070303c1ca0f00da5a5002d40d085070b58200303004135840c100400c401c42c13400340100d0000b44040000741902da400c08140b003a000804441402c01d009200c08042d0801c0b240030b10040060107071a007003221108480c034060900c4601750111902ca0740c20300d180442e0062081c0304844a003940c03d00c0c07484403600600320810103504848403e40304c20600744410710030781140342c00300d642c254420140015110035a00e400482200d41c24998440056001c049403410f903000030445a040c100d0301101d10407030400b4800550 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 643331717 1250 643330467 643330477
    0x60a1418120a050a02010c1b030f0e03010903020a02030c04060e13020a0e070f140a0f08090307060606020d020d020d12050907080f030409111201120c05031501030b090706120c05 78
    0xc10740364002162019030b644400a08038140c03843d03009200240d0301c2c400c1240e107030050808100810880780260400070303010710303041114038003d030401c000352040035030000e0f003141d050080a6000d80c00c441c48141c1145401d01c40c3c80b8204504540c20440142041020b2002800c0141410050310480841c4070556885520480040900782010a11340c0783c2540300030075007a1080c081c03401103800318480e06100c15800007900e104020f01d54504c0700e900c049040441d40e01e030000e8091480d50000f045500082480d6000340c81c050602030300144200c8842d41c1c0c0080c81d008081c1c07034000440d007004607524083e0340c0c082c5140d0034064940a001c1126204c81e8a040c1c14610240d00405c081d2080e081e1034082035801101030802c80d0000ca1742013007c0341040101200511070400340101401c1e4910051111100402109080314060170084c0c0c05261520003003441c024280703520501e5250540010000c11848112042d440f1400c0c81c043c2080d103240c1800030f0001e00c0c1c10303031800e03c0494a5500441c00380b031049041d95 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 643332967 1250 643331717 643331743
    0x40b0f0711030307031a1008070507110a15080a050910050705090a060e130b10111002070804030204060902070b0402010f030e031204230304030602030601051c0b03060a1418 76
    0x10f5a2410301a030b000d40182004400c2c00040d900c85040442030746050904105145407640360141c05981d11a02200c80d980007010855030f1502e401400081c90302c5078001c04c1c9c041d09110000903559080114041c245040050a800304907081c0350030001c2c80000440c6901025104d07480200d8a038481e55826a01c0d4020642a55080f003d0103030006101c0c0c0c0d1108500da08c008050714207010925030a0007010580c0c0e03203003004542080d400321414800b5489400382c82500d215550986040454400c24035007aa07200342000e0324590b4021130140198a058850075005107180b4600310319000d003564602107843d4008101a0600c04000c5428405078000d401500c0e14402040c00d0700d95a5401c4c2001e050040021744007076540b2071410290300c40300c0001c03c21300d00c03441d83d44400650410340b55550703680217076000402c0c10f07040200521801d403e482141030b40c5007039140546c4002c03642600030014940b401e44002c119070f1480d800e140e00c0d40320500058154907005070301c0c2c40000b0b4450a0b00c001141c60022100e00c10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 643334217 1250 643332967 643332973
    0x8100b06042c090a0203060615040b0a030c030f02250203010b060d15090e060109020d06051c031116050904050a0b070504080d0801050a180e03040b04080c0603040b0f0711 75
    0x44070600b44507444115003032000302550b0b454580c04541a80c61118010003901135104070082032442c586092180300c0d00c201c0700034070340c0ba00d6164801303148140c10091100303000c69200d0030200056a014082e5020600b0074103811030034190384400e444035031144010070103554003481498200750f480a40109a00c1e490240c021943d614583c9995001861036040c3c0320900d041c3c01c0d00c08100c00859014200c082c50050006003102c1e402c20740e500000f540050402414913545245c0090503899407007040c011201001648410031440d818040c28660361445819065000101d0310244d086000250740142e400030344413404543d803640340461070035002c06070141c90006840c1c02c1001c0b82d1303442002070094844101c15140349024056003035130180c60038051160b020352802c0050020781c105404401207800102c002080c0540032520181c190340c050342024030b05000000341444801c00c20040c015640f04c09a44c0d05245141903111076030360860103801c3c1800d10101102146095101d030740302d2400c2e0a040d00076 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 643335467 1250 643334217 643334249
    0xc03050d02190c150207081902040f0c0c03050c010e0604080406080709230a080102030c030415060302010e06070321020415021b0103051308032d161421010f080708100b0604 76
    0x7071160540c5230f5008074841c6050484041010480b802084201c03101d07a01c80840e4010141c3e003d98407900510070030f0171690769654a080f8800382c20480ca80c059405580301d250341d14204800141700c1c410050802c3e0900500c9001046401c08580500c45098481c41236108003c1d4240c001840320a803583c000c06582d800030042c405240724220080d40190303c1548a42603400e065075840043d900c3d20321020380400e240002460650910400829040348249010004800d4041041640103051601388868940c08101030042c210b1242020107000450300092000c1409401c8005582c0900b1003281c0c10117480c2c4000c0b0b800c429030114020300141c0e0084140d0703143e1411020308a500194500c1d41403564600721a40310403610401c1400f402010745c00c41d607040c01c0c00360090645070b50142034a1455101001c010402044c1c90308030403003024504a074803410035035140028440c0c110300035800c405150b420100d020028810001616034410a101c2c00c04100d5102900c0003819600407640409030328582d0801c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 643336717 1250 643335467 643335493
    0x18090606030b1807120209031b130902220617031c09110d030e040e01051f080304061d040c031e0213031403070c03050d02190c15020708 60
    0x2101040d140941d4041028101880401c00c0300305804005008000d28a80482ca920b4800d00210140715040386000d840c018020012918046141c0301d000381000c5100140b03040c5150008045110703032a00f91007030240d19481c1c0c0005a400405842920107010090540080340005400c484000c04aa09605404600380419546c40b54800700744d0202c0280c9183c0032a41070b00c514450b5145281d000921107410b52807060a000100410b00303410341c24044501e109216543e100d00803502d50301300400c00424075040003501019200309041c1090074402c0d40d03190620050000005440032a100c0345414007070340d0300e00e001090b02602710151140c0c2060030b040e4440c0b030003a0181c21880304900000c43c86200c01d2602c0d0f501004034001c1400b0240000c0c4400c40810200301c00c001454022003014046d41d107804584e5440c8001204698821a0681c2218a034942c0300740e01030100f000071140e80b24140554080b50360300c18014901c14054180104003064150035041d200f0000140500101e00445907402c40d44c1c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 643337967 1250 643336717 643336721
    0x717040f1b030c0803040e07030209010e0310020c01110a0813060b15070b0604060f1701021b011407050c07030b04081303110a080a0803161110050402010e030d09030308071809 77
    0x201050b500e03e0202c1200240b00e1350b0000c2218111040d40140f1480b9448a81048021351300050010307040186040182c06580d605010310020b9104501c1c1c0143c2d41c08102c8800c6003915299041074021110030310800c00390320741051010340e11500400c492800c3d00d42d5490428014003030540d1594000f00074086513030049101d0707002000c41501034030b00f0855a940d040700704000c0e03030307500d015420030000740d180c0800c41c14640e400c05d94030604d642d1002606010110b1050003810300c42c0440300000e270791a48030502e514144c100300280c10180900d0503030310b01005042c40a03a00d40b0180300060030790f03000070001030500c1052400e4401101c03060282d040c10540d00e040ca0350b1000883c1001c5403203031080c00c0d000509884d000609540c0c250344288024203564540b05118041102c402ca0701c0240003841c4030000600c101480810b440031010400006e55050a000040180c0c441c10269030003544001d501010f5541c2009030a400c50307905103007100c4251380315242201e41007080030074106208003001002c51458419 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 643339217 1250 643337967 643337969
    0x31204030e12070b0f12040503040e010605040b070209071407030315212616120c02240d020c0c15131701020f0307020606010306050402030717040f1b 66
    0x180e9074044084030814100071010300c01850003651a80100020400b8240901c050502000c0412140741001051440020a2401101d0885007600005414088060144035141c05032240d403500f10306260403e050105280704260001e882400c5807000107030850701c21031344061540da50018a80d11103d03e03141c003402400540d80000014000c402c408180b04040301c08010007094041d400044415654480c0e01d0411400031110a4440740c006400d03164000c044001e098030381701e0005c0050040305a080440f44d4860f903e0701c40e03041180c80c240700d50140c0d481c62041401d900c4a02001c0c48003a00c00000340712641f2642c0c28000d486800810342c4030b4480404039190003a81002c0c2c600719a000403500322a40c40e4425203a4807100050002c006000308511070003040e01c0c0015200c00145018040440150550002c55107080140d0241041140c0d65a040c01840c0c000e10f0152020b40c21400d10440203440c01551884042c5100e04410001d403d010340b003030f10400302540000001000e20005012000c0107011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 643340467 1250 643339217 643339223
    0x4060e06090a050910022a0303070801150f1b02190e010e1e0907080a0c090b1905270108010603120e03150402041407020c1e090103060b03070305031204 67
    0x70600054800545801031a12405083d00a05955000d20022100a4010400b030b1141c0c20780c08480c0751031804031b4403c81028091010f000b5512823611900061070803905030051402c65100f40c0054401a400c44c00c69006840c4c54109011040c5049040ca00311440300100070754081400e0b500042015816824032080e10840c0303800c000d05a80784c02d519988580241d5807511310518203031841004503050b01080785c0143c0784506503542d02e43d45650341850714480000c1654000f881b090100325278009440341c03074550302d41500e000b416031800011030304070224030f2b200700c030301030508035944d4040d40c0320f01114003841008041b44030080703507100c0070424024486800100e4040c203540003001d8109010300d8210f40342c101c00400801d0305d40c0b080707501d4031003240d0f01803c101d810a4840c1d02442c200b02d088040c0c40d01c24403030340c0e006020401411041040700c6402c86040d501c40c41d8095107204268850b02d000c035043d2500300401085c00d10188020900e4120140c0c4080c0c024000400d05d00b1070494001211030080740 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 643341717 1250 643340467 643340479
    0x2714040b010c020f091008100506102c010210020409020c06100e060103090807120c1101030911090405162c0606030403030903030b030a0f060c0305091908040504060e06 74
    0x880c200054070300707045601000e5880416040611058a0320400c22584084062002010240d440c1c0143c1e1074104241d01700c01915454500704192418100c644006802d2a80391680d195038005110f14030400020140f90201c503600d500d030401903402005801c0841a40030001c641d00c940e070340503220080d04040844483c0d80100e07000309801d403034803070703c04000c2c2c03149080405000e03200d240054000f001405012035040380d090001d00d02050707040d600c0c800c5900305910f600700c4600c01486c200b08075140002015042c10b10700308074180840e0038800049400e070401e07900ca040315291414541d01d41011201070040d4440c0c40b00b8042818143e4904e01d01e50b003115100c001c5042103140310f89486030801264007a8000c1001d000150100307109800c060401c074064200002c0804500380840d04003c8034400a64682c101c9140741000c2040c60300c03410801c6051464200503e0400d54103486c0c80d500c086030f0120420300390665036000e000d8450121001840014020003620340e40e00c4051440b00c50482d81e16200b14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 643342967 1250 643341717 643341731
    0x2c01060c0302030d05060a0b0d0b090a1b030b060c01060303120f0209010f0503062d1201020c0606011124060f010c05030306060706090206041205190210271404 70
    0x5000c0c0000604869140e00510304004640c2241c44c02080d005054a03801700d040c3e2400544070049400411007407000110205140f111002032044040010382000303441483c10f5400c00c5800340c1c050304291840303c94900801c0e1401c417000050014000c00d43e0720b0004e54a002000000c06400402c80200d507800a44140502c41906d880c40040b8028408014045281e4440a00b2550712400086da4801002088c8403145800f070303c1740ac0c500c0c640b484204c584a601c1c1c0d250f00c540a10708906400c1580b01c0d040000d44c54001c500e06e0303150312800c01401650600140c9102e400242000340450908406c655481ca04040c828603e42400b80b01c0075214140140c2103010300c06d1255100317040404d121500030300250b02d940c5604c01402100c0d0701541d400c1d43e14a40d180d4007140140d80c0c0000030002016401520a50882c007801c09500b0706a9810300300703603080c04111401c4010780f11140180e01c03c110310704181402d0700d104944450702c504413000395191030b01c1e1104041360b0ba140f41c8058140038102a07900704051 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 643344217 1250 643342967 643342979
    0x60b031614070803012612180405010b0d1d010e011a010503070e010509040f020f0706060f030f0f03121506140f180f0d0c1e030f0212072c01 62
    0xd80b003101c0c03002e07020441c10401441040b80e40c0c8081544103038214070254480320901c00b041c1c101420144c034011856070004058a121183c1c0c6020340d034442048030204103951508882459601c50b21000d0303401d990b02c6100e100e8441d58501d0500814140d030000034040f10740382e20f10960081500d00d2070020225030b20445040e90703510070000e44e882414581c80c1d5a44250f80d40005680035001201e1403584140c031000000700b15005400500b0301310203406612a2912224a801e6041d00e82941107050000140e2004001051100b03043c20907058010141d442c884403242001c444800d940765809001d10305141c0b84000080c900d2801108492481c0d0b140788440c14000e60030a0544502064550307044018401c059410145502c0d0600c0c00c0c1c801095103506201c000d02080d94090b004406a8a40140b00c2d020480304404116034146404514103040045045070f648203d020006400680102c180d4840050240410070400e00034040c00101010702400b26800325555600f45010201d40710030031800010f030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 643345323 1106 643344217 643344257
    0x8062110090818060705120d020d1107061401082e050106020307110612040308090a05060a27020f0d03020c061903050921070303060b0316 61
    0x50300c002080c221201c4400c00c0b0030901480017044000300041d404070710500700e031a010302481d0300c856a40c4e43c0b980c028011840605003403450140c03129a2001100702170803806200b40414040c0120520040d601c28400388100841c5501044c0f082482403502090b6651442c0c1c098840615a24404030ba17a00f0744800380c0c00440980c0001484800b403101031050542c1208054403218a0a5001100181034043c000c001504211100012449140c41803087d030820f00d812104460540c182010071200400103240034074251080191880c0d500c030803c040550885800030100540d05130f0030400d0003104038004804030114000ca17440b001c60750b6652400780600ca07202c4015100020030011000e001c68070042c02e906d8450340002c240d10364a0103024020b06058041c0c412050704c8201625055010b40101d4002c0029080048100040c0c2c501440c1010031041090f03980d801141140045840 = true := by decide +kernel

theorem cover : BRFrame.Cov 643165467 643345323 := by
  have h0 := BRFrame.cov_init 643165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 643165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 643165467 ≤ n) (h2 : n < 643345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
