-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0658
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:58:52.336794+00:00
-- url     : https://prove2.me/submissions/16f3d104-a2f2-485e-a3e8-4a52396c4623

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 118165467 ≤ n < 118345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 118166717 1250 118165467 118165469
    0x30e060103240609050702010608070513090c080601030321110306040518010515030f070614070302151005120a0b0c0c07090e1606030504020603070c0204021902010c0210020310 78
    0x860888203100b948084440c1d240c01c240798442020410005a44191340000380206560080140d4030b0840c0208200401154100a4030300107403a0300b0b9050568000d10303005000480007a14185001344021801c0d030f00130b0107418004d6001e5540ca00c010040d900e6009607400c5100c2c1d0101c801840d02c0800140c80d4020419250321007003c0700d001500340c0d19a4917000250705110521700c255440d00c820440d0240302c008900619443c103400325009040d14000c09590346090b070040401003001008100680290762005254451080c4152401100066000700405200781c41502110360180410b010600300044000001030000f0000d00301b004950300c03260340e40c0c1d001074000c40785190009100c08900008211000013405504800c101c1c0e00d888658003900d43c000e403410307032400350455000040c05603ca4000d15000d036030001c26840c51900c503200c0c00e82da26403251384c0c101c0e007064081c080c0e01695448a2030b83ca503641442d07000400c4c500031111000381481c0c0041c3e207034401941f052040c85220511415814 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 118167967 1250 118166717 118166723
    0xc02040e01021911070b18060c0a15020301090e060601080402040f090803040602030f01050a0b0d02130e090601150f1b0c0503030a170601090e0601030c03150603020910030e060103 79
    0x8840c451182581c0c007900c511801014903c2e802450400b03507681c05031901d04000e000c1d8042d10892502c580c5004240e104002e080f1514503040452040c46241000003000010b00040448455031103540d2269090528415113002c99907020004019450060045012014040c000f03070140785002d60010b0001503000d00043d0141d5615810641840c445901c4071101640050031151249041d2a000010b540111060a450200400001400c3c1041a4043c0580307e06003e002e04106a030600d800003500020840d00030b81c10f50740400580b5000341501c41c1d01450700311016120541c1840316504070803803801e18a03010421084e21100111364444182d501d650702803100c407640c1005608080c0700740d0000790091a81404001002214241c00c440c004030b060301e0710034000141d9a5400c0040d50009001d01c240c10000000d240080c04561096000c0c2c1c80e055400d080002e501d81e110702c105049500250400b8020030390000f040307141845c080319084429201d03486c06224201c41102c65903141c4c8010302c801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 118169217 1250 118167967 118167971
    0x1b0904020915041d060a0c0e03030a1419020d0201050606090a1802041d0702010608190809010201110a0905030601050604030c0303080a020c01151508041709030109050d090608090606010c0204 84
    0x50355581ca41006221940501c20045940e4954490940701d42091b80c04e03546061130f00d02103814890084040201803900140558240b0030248015200980040c5024000c901c4c104440313043c0c2c0d411041c1d40310b80d0b02072544c010b103100b810030380d40030b4212000504102c0c0b00e00070034484600715079680518001612106544500c501d0011074141c40603001d1a0408610802c803442d05803500c50401064030712982d8035038024480c3c1a62100008e403900800d8900d0001081070302413001c0030855400081c44007041c1031000140940502d03c0c0303005542c020030003941c0001c01c0050100070710b1a003004514090303c0e08444003441d040c41c648c0c80460034900313840700800b4060b103540041c000064a9065416480090001303000c014400411280b0050700c0c1c0c010003078088a4200f03a10703a150310804040d40300f0340c0d109004013640001814400d40c01d42100d1f000a030716640306c1080c5000910144076a05044280d51100950b00e418500050500c9000030605811a0321140030043c80d42e0340529403c880701d4043d500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 118170467 1250 118169217 118169251
    0x60d0204020409020706022d0f07020111070303050307031d1b060403060203100603061d060909030c01060323120702010503060d05010213050906060c07170a0c06021b09040209 77
    0x458041d000b02d51142e880a0301c00700c0c10f0400d100280e0010190b50003d4500525a41c0c00310f986e02160840140c811510b601040c03116180344204140140003950050402c0c0340c800240c92200351502c04250011000180040203100341c040c1c2501516281d010800d0f01c8a40c0414100d110b01c1e5a089251074048030300905640c0c044061b1030b06070482c1e0140da0802c01c1076641e40f4102d45401031503411803146030002480c00c840091220004224052400d8040d50000d400d519460108000080d0140c81120a400200305ca103602d41d500f442014001c40c4103030700c80050b03030208d070780400d040542d84a1f4030240341e0040b04440640c0c040840840d125075034242801c640305c3d100c0c6004640450350016005000d076200107010481d00586506140440d00d08407900c03611f50342d41c0710901046015038402d58000b90300c113407400d01c461810410440d0307003040d65500321200307600c140d120548840403d511000140e0405501080c0050a5003158507401009882046040c1001c2d0301141e15a0b100401c0d6003021051980 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 118171717 1250 118170467 118170469
    0x1021b09041403030702070305160b0d050402132f0304050a0b100909050307060c050408030403020d0f0f0b09101406090601030906050106030209010e030a020604030b040c030c060509040510080303060d02 89
    0x75200c010b0305a031084075120700e0142c00181d030358141400243c40b40e2217907852999071042d00c002d448050304c01501e00607041909508041001d85000791040b43c1c0640003003911410503d0b10312454525401400e580000308010102c40c1059150390201161500750030020080400e0b000510f045406601c120018007a5440c40309406811100d070700602d002d181080604400e019000010b8002640620700070048030b84d40c05000d2b1041d209512581c0340d550024001000989050fa01010030f09015190354840f211142d5280c100d0384075548421680c0c0c80d45007007400b00d01c01c0c04010705810002d1000b410407071100c200c1601410300900416440c450840703040099a0b1342d00c681c0043c000b5650056050140e9610707240c0140107904044c4070240007031010b60460041e4035000801d03226464001d03090500d01825a21400319070080140140c9141c02480070000c005003246203108010b00c850f80d00c3c161913041c003d0400c810b40300003801d0410012114482800340b60b001000300e9420240495803c00c003068148 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 118172967 1250 118171717 118171733
    0xc12010b191116060507050d09050f010f030b0931020d0204090f0c0305030405151e030417040602100c02010c020c0108090f030409060501030b0604080706050702040f09060e010b01021b0904 83
    0x200340319040c0c0f5201100040031a0840c1c003401400d8412020344000000112003100c000910348503580c3d0040352a82c43c160194058100540d06020a190210f0f96180c0403001c1461540c0603184000301048403810b041c140c0d000740710040081000c003500000c0c1000140c0004900c200d900c040a44641da4941c4d5000c00c016402d0307200000c4941c050710003c141c5907282007154494101e88038403402a800384502c0c1c0354040c0c0c040308844107400300d01c0c0d4040c0e81070001c81c603065003900000c0c422245c4065050030300144103103240240c070040500d603000b8041c500ba5109e0407420340703581c25849400c1d68186650404265004140709800c40b03400c0ca4200380c642d4444141c14901a80b806c80082d00c1e00000401040010540d041041540d0003070b00c00340220302241c070074803e85100c1c521500c045034002800602145116000034143d16000074000704403c10151100000c8983d800c4007111080c3e60b03004000300070002070103824a2017909002900c1810002555900800102d104451041c2d1a1800240c03c001c045 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 118174217 1250 118172967 118172983
    0x15050d0b010c02030d031b0c03050304060b01110a1b0603020405061603030f09050c0a0b030408030f0601090f0803090a050907140c0a06051602070b0405060702130e03030c12010b1911 80
    0x10110745d045600f191014005041e0f60789030162160071540340c000c2c2680034101510203641e050b41e907286076275115241c0000070010124087d0400c44408000c0302c2000e4200058001c09000d054405072140e446c40b031003501c8003540e500500905006000c1081540d0711710003130703890703c41020f80e2041d030785422440c1c200c008081940070580960f10b001c03103080521500142190030340d0b20590b00904410388842c00c6548600044400031721840003000050444941302642582000b410b051100903144c6480303070307a02404215044003041e607002142c0d83c0c0300e5103042e1000e00010b003401d071342e41c2c10242014140242110540503000582141c0068802000803081204401c8690031207000c2000e030601a04600b01e003081e80d5179501c01403082410110700110b810046400f1944010402c524142d080d078240b250117600000310b218a141c2e500d00d0510220404c1c80294814009426400d6649402d981c0c0800e503060182c1000101c80c009200c0411050210741e000480000181000c6c8800c0000d2005a4541055 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 118175467 1250 118174217 118174219
    0x60e01030b2115062b17090913020f041814011d0102031005010807110111041d04020d0602070c090c17060f09040204020d0204170703020a15050d0b010c02 68
    0x15690390301c00b820740610b5104a485103602520b501042c6080c3c4030a0031107050702c807654441a0f2220000c281c042c0100130412510071004d5078050640e203500c680740d030865401c0901c00001e000084043c00351400d201c2080d40581420781405610b0015008610b100c0040803800d40107a40d82d214030018241210a84408240d012012880c14003000380980d0280c956402c8054400362040c0500c035810006009880c0b0030607114441503071091904004442000c0080e10510500141c5130101104160a000d100000c00300842d9032983d841c43c106013036400a4603a03034810071581d0072100341310042c0c0c0c40e1100090542e800801c0981c0307421080c14641c509106681c0140360b11403500507024140c0360407452542150a40c04100c94207035403498284500700125640166201540c0780008005141a501038105a181d110340103062507180c21a055140030507409101c51988240700c01c200714070f40503042d0350140951407080000c0c6803444034058030318003400150a010544840710b40304141d00c511500d84480c0e130 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 118176717 1250 118175467 118175479
    0x12030e030f1809070908030f070218070810050406060915020c060a0e04140103052509060609090e010c1b020103110a08090c01050c0309010305180303040804140103060b04060e01030b 80
    0x114121020700b00000c241940b40102224000106144e0080c80c0e041e045400030f402940c030701410349282d580e03580e1100f2070491b40800861220310f6800c800b60b2849200d0307c2561902952801d2082d030210b0034100703580c0100d00c5181814000c0c4112603001036024119201c280581035298007229059092070342028100c0d07040240499051849584a40d4048805406403010480071000030005502081c017404003030020303801841d604c88107080e0300300c885040e40780b00ea1400700c10b80d0701c400f45002174984a6000c0e000050540009019201301445455400d000682c001c006900203440701a040a8244141c039546201400304e02c001d59000340c102ca43c606148010041d5180700c00031000d0280c95041c1e418035414030507418102159405a006c50710603a0460000b103051a90141c01100a4500103216580010034030f0200c00000750108051802144608042c0d91200c4c10201c1c00b0f00000f98000d601c50402d401c100d010081c6503403110858054402e50724145007500183c00058000d04000c6000c0f54110b1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 118177967 1250 118176717 118176727
    0x15020a0201081801111306020c01080705030709031707060b0f0d03051b01060f1d010803090607020a05041b0f030c0519170405070510020105040803130519050318090412030e030f 78
    0x400380d00040030b4000c00c1291241b15a51212412a558201460620f0100c2c48000c045600d15008001465200d500c0340b5000501c507032260307543d030455a0112042010200f0210302c0c0c404202c170b00d01411007540800c0e00c101d00a11461800500044001d1402a0600030700280c0381d0540b2040303903094440408100000d1103816a10881c203900c00400f03104460503201c0b92102032485800e401881ca0413944160020b505100a5404100b1142d000880c105c0e40311424800c0018592600e014011090104881400d5203460b00c40010703010a17809004a4201031800810308543c541000c0ad4442c00411006034289070990b42c03109850078100b2445480f10002c1103000c100801c83c00181a105552084d41d0640081c018a0f80581c240d80041e03c000704050020b200241d00c840040b101c1c250841d0060003164484000d600d401115154100416211034100045000b00780c0e089800704090a401614120820700d015115004290812002e18041686800a00e12288001c000784d481e10035800043d241c4d00c2d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 118179217 1250 118177967 118177991
    0x906070203100c0c02101107050915120105070e090f01090207020f030a0f0c080d0903060b0102030f0f2203050a031815091706040f0308130606080f01050115020a0201081801 76
    0xc1400f0080c202e00c101003034005000315038807032105001c9406104000342314041c1400100044c0e0b010040c051020f03442c0b0700c00041c1c3c0980d203080038940100c04802c00014581030124008144c401480d04032406520844c040c80700621070020480e0448190302d40042c0c6a03d480e10020300c01440e04000680d1500c5400342c400c0501501904288606226026800d042a0b8178102141c4445d4041e8880000c50380c5001c081000ca011500526074065051065902c1c00c00e010000480f03c2d009810048140c4074003007400200c8201070b4840c02c11984184603480b11141c07031580c4007980c404c41540010304000090045912030b014034020300010b0030074910010211420210010a0041075101d848814610442c0c02d011100e40402e003240500d4100c0100c40300c00c5100d403425107208401070a02082c0d400994500e101181140c03003110081e2403c600501542c40b6a61703000e5080d2601038200080d00a00001c3e0200801d800240d00800680d0a003411102541e03140991120008104003110071035003804649188 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 118180467 1250 118179217 118179227
    0x803010305030a1e0f08040c030506010806040c060207050a06120e0706030f0f0506031908160303020d0e070b19030902030f01020a0908120301060305090f0f0d02070603110906070203100c 82
    0x11400f05507900407194008101c000b0200c0100554000450990500c1000b09481010415031180c01544a20602540d070b6075100e207000403d91141c1c41ca50007040c140400c21589020800040495100030320000381003500054004151f840382c002445031071a4041d003d880103412056010501c407081c3d524456071804041c01405c90704500b225040d00c2e0030001442c0c0802c621541e401440094010420b203590031003000031281e2070541c2540c943c401800109031510204030380c1a002e51080d070780940c441c00502c40c1c50048c0ca003a0705050700305400c222024000080d121059075031180c041c50000c0600084400250020710b0780702c001a4040c0564502910300c04015002408001440c0d80d8819583d955101c0e40707a12440c00416100040c0302c20001046030902c41d030800350b02f2080040c1601d0710036840c1050145840b000076504c40c11600400d83c070710107154061004400070206410b00340250041c106000516104260728603101d0000810326000f591803c012662444c981c6810400c1000c24502c00900 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 118181717 1250 118180467 118180477
    0x210b0a05060f0402040b0a031d0706021c020c01020604020613030b040606051009060e04052206051009020702010215090705060319061d1303051e09030d0c1703070309080301030503 79
    0x800b6610110042d58207040c2842201c080b143e210403018188810203004070007a0404415040b0701380b06440c841001c0303480a11100d4000c1040d0b400400421040101021042c8429448203041d500400c0b180603280c0d8020a070640d0090741200c000c0d968101c4480702c64140c1d13885810160551401c0800c2004120982e8400c1c0c1c19100101d84080c091420034a0869040301076000390030001d81d50084941107410f16400c01134102c07004900c07c00100350143c80454900d0700c5000240c0d6803949460030300408164a084500180803000c20561924415800203035440e0b801105114000040b2400603a04100501003680a0003005215071ba8034201042d800c5e00c3d0150f00c00801240c203107020b000141c1080c1d0710b5440c0c1d141108481b034074070644e175a030701c1203c5040c00c00903820f800b03104042042c0c4032401c480008001034840d51400641c0c840c03030100103061404511403c503106006106400b400428251012441030726210410381765251b44443e01200a404148401841000044004810090080701402c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 118182967 1250 118181717 118181719
    0x604141f1a040203100303121b120c0201060503030f1b010204081b0319061a0603090102040602060c0f120c130605031f2108070b010806010e090304080601210b0a0506 73
    0x1281e200003103042008a1209446101410741034400800000340220190300300880c4000001402100050315000d00e2484050f4100c00144882c0a501c0022a640700d5807410000da0301c020800e26051101003641e81c466085144200c0d00d011604405030604040401a2542c29600954680d175a92982c10750f10b40c4c1c0c000803144980c030010f0062140c1d05000554805840b0041c402440801a82c0c4840004020315500d00e031245c40d519000c1c44a83e26203200460050300c58038001a5100d1500100a04001c005030151003144c42c1081000c444150310410303030f1400801d03441040241d440d0703594221110f10070b451052030503811065000603041d42201c041c2d0b00c1004071451181c0b00081050030004034445030b0140c0390340d40402d0041d45241185c01c0c1c00da060358900c140081450315132203459011121100741c0c0485580d60042c00103100c002c0c4245185600641e507c40213609043c01d2002c2c062f210001402502c2040949049032226110318000003140c60f904401e80000609001e4105005042c04403105 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 118184217 1250 118182967 118183001
    0xd020c19050d02030a0906050c0102070506150f03030315102d08150102121305120303011703030f0402010c020a0e0f0a2906130f0f090c110604141f 65
    0x42082c8500210444049103a03555425a245040c000d0940700390304180003034482ea660034000700740001c10801141d8090f1140301508950442004104405041a000194000d0b0000c3c0180885100400030b03591601d07500320b0350408000c1d0310110480b0500f110b03a0140d4640649025030164a10400c1c40030003401100b41e035400159907910b032102c00c001801c611003a00582c03040b0b1549180700d0401d0050031800400b00c03a2190800e40e01d43c001800340a08444d501001d402c00001000844640315040c1641032042000d10304502d800100440e02c800010800f9040c00a030001080c11556243c0c400000b6003074469400f2171a0400820036140068111100700c070a524042ca60040e000c1d01d29644100600007810042032040d81606100054010903921006001118000704c0c0b03403c0c0c0210303d04068041c107880000708905d00039109096400e1107160b001880b0740b031281d0006015021800f19030181c0c1190348100041c0d048942a071405004001214100c011042c0803280b0b803035183c11442c90420888a1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 118185467 1250 118184217 118184233
    0x7080909041101080a0b06030609090c0d1a06010903020a090b030a060221090c03030a11010603050a050a06200414180a0605090a060b030f0703060e010909060e01090b06060d020c1905 80
    0x8481e0440e290000034a5101d8810f10025109d446c01031210341c8d11406110030b40e1190500c00c004902e40e2858404111a400e01078040c1103510a00007000c1a4420340034a0086105482c640201d0415085401654038880d154810400d00d500d041221003065a80103504568584c030004103449440c041c01a0003403522054000720300c08180000d450700d440d9070020007440c40c042510000f1381c0d40c41c0d000c18407408079540300c0c0710010105606024440c41580241c1c00b520000c0c02510f01b80c82200e010030071050805610821021508101c8410b840944403e200c0000360891a600083e07090788075648850f6480060104200c044c0d0401d8001208545060b110200c3c20303194800d40310140e42072070240b8080500241b0001b0160302d8004005500103116007000501c443c0c41b58000521564240c1245003c60b8680031088204032649c0f06183c0c11138207905c000c02542d4015912400401030143c80117225980200da00080208030340d044071004e103800300480d0905051142d0a00e04000116026601400f500030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 118186717 1250 118185467 118185481
    0x170105060a05030607050919060c0515090706050703050d06032004110717040801050408090111240c0f0c100b0d0b0106080709091415061204080708090904110108 71
    0x251100103000d46005d41e141c02c03080f6a142c1040e800c0ca680000505c0d5504140c12030200d840c00949503a81e47c1d00482c06c1181045480c120010080000080070351040001d00c00c00401c901c030940c0c05610706250b81e406207081c225200d010340080c1c4101c0318039203103000080144002e15015512003030791502c6149468007003008101d4500d030280d40140c4204101c90740016000700211210031091000d850b0410340c603002400e007100c030b00b11811100d000e400901702a1a40c0c020100b00001d5032020010112520340b0a05412070035030350300c00b940d007201c402d401040c41e08001c0030640b0071070403c0011030b5486003c0d0403095071b51201d03521a46c00805150032508040750828400345110544c00111640e411f034178001007214010001010401003203410900450744840d00d00400c9911200c04100b101c40d42865075013901a0500c00e06041e20035582003104898a0700c01c0c80ca030303a90040e004080c46446003458240764106d44a23110556078000c8100d0100800c020b500146090703952820f0f0395194099071061 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 118187967 1250 118186717 118186729
    0x11100903030c051804020f1903051e010315050703020f07050601150e0d030f0e0607060c0905060301060e04090602040902360a140f10120e1501051c0c17010506 70
    0x11815115948510440c4e482c0b070509800403c200c0000d015000e2519008100b29040d03100405103080020703885005101000395162000d0b0300480613503200604a514503950000e26126085418650684840004034000d0282e41644c40311443c403c04140e45900ca803078816182e444c00d01456240307a038110040c818192280002c0071032150064100c0040b118252001d076080d507850305c001c00800c105000d901d111b548a0700b01800c4107912071403000c00c91580c0100050702e02c2046400490003503905000400c2040e40c04508070200c0740c400d440c00540b001c0c160403d10702900c1f81d9042055141d0000a247c4d002208080740003822818008041004995540b40e90a01c01f40007500d1540c060032002007800414072151a02d003038017038000e100d50790784004a00451026805140580d003c1602c40f070600c0002c000c5805841044500900a4205203c1c4048000320354001030003241e00401d41c5060320660880032a4694413400d0300080e450551954504103402c1c00b652002200003103509000100d40749040003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 118189217 1250 118187967 118187977
    0x3060e01030305090d0f0f080d0c020105090303060d1b03080406020f0a0206040509190e011b03060509040b19060b070c0e0f0403141614060708070203070b0711100903030c05 76
    0x355580524000c1369004000c1d020850010542c0e000b01000c0001001881040480940701e1003145040c0d250031004942c401154011b1040300c0075a4145402c100d4420300200489a010310100d590f95100710340e81c1041803010031f140e81d402c1c6c29600e9288011007030000c104064021244140d00b1540c071031203602d0140f521021000c40080d000070003800140310070724003202200c0d800807000304080018200382c40c1020903030f40b513001c0d4240382da5035540300d0101455101d0f19000036450f040c10284807903460400424400034004101900700ca00c1080850083c81e102502d6842c94120050140300450700c03550120825408190222900d145035000000c101a1280040c0c0c0f0500808000c0c071180d17a03c5813810342c2c07041c1040f282140210b408101c940000114001440d6034140542d04001c030340765259500b5454540082d2076070050100900400244581c000200c82080350301ca0740040403a10b030380b4015600f11811a0f8801c3c99406441c9150510050580c4403050700b601a542c03d00c03140607004010b466610a1b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 118190467 1250 118189217 118189223
    0x6060d0b0403030b04110a030912030212040f020f1002010605100c031d0103020405041a04061e0605070201020712080307020d0504060903060b0f09070810050603010e070c0f021c0303060e0103 84
    0x401400907000c00e0090740016010b190107000811900d08080c82006194417902c1407202007036881203107001384160951100106516420308600c0c0c148940128410800c0081004010f082d248010740c0854540582d12241d00d2005080c3d09a01c00b030344480680600f405004035401075035a8608048043e00c544587c041007a0540c40307611996008a0342e94400500303000300981410740030030000846858500c103100000502601c85401815441e08000540c2c0d4154083c44503482c0620801e800c0e19070000c010012a8120705182c1e0390341c600307880141e0400150b503102180054000641005102080009602c20b50096098843c8000310318000e035820700483c000d69002810800c420301c00658142c0c0070350150007000345106110321b5048001a8040d0702114014006140142031000108450400001511080f5005400c3d5814541003000d5140c0c002c0000080004000000043c421407640030007026130054109210a00d0030340140b2211410414114000380c60f1034000116540801c586a041e039038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 118191717 1250 118190467 118190483
    0xf0203070b04030c020a0e0c0c010608070812031806240406140105070311030c0304052103070807020f0a0306051008070312030e0f01240b030708040b1305060906060306060d 76
    0x45079201100c4e00c0304003440490b0001c103003c00c00b29548400444a0b440796146405d0295100c0640d00140c1c2134412581c856003c0d503100000c1806045e82c041113148102c40e41800250300c96540c1b203420204010700100d20030f494014141800250400540090b2190b60300740b01d48440420840300780002c07100c0318030400b000c5000e0f044030103079558030410060100714082c2c940f41d060308500718200c40c01c0d5440000c0c400816400043c04001d64109401c012920040020009052070039008000c0e4491140800081040e2000194081107654000b0300d2106128060201e00e00c00c2c3d02d070302d80a402404240c3d40d00d41000c0c40300034002000e8900042508c20f80b03510807000c8a9070380b5005420342c080d0010140b0f074081801600c00c5850283c00c24030414400b0540c1112181c2030b01812900d850b85a0380c80c4d004140340f044100f04010401e500304031002e0300913278409505031072940c0d01d10380007a2808481d50000d0480c0034080074818286c00028005000d0b1a00320190b81903a1180070030040790b01100d91004011417 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 118192967 1250 118191717 118191721
    0x60d030f11070e01051009030515060111160315060b0906030901021210031b081f06080106090504020f0f010f030b18010801050a0c26040507050405160f0203070b 71
    0x2034030841500c100421a400c01040c140e20075800907003020101e03041a40c20b0000c40340100304500c4c281072030000102c024202143c9550664031800d44940d58070a41404821002c00410841c2e40b1030000101085030386400d581c08040c0d101984900741c2d20380d100642c2c1401c0030b0314580c6c0124080384111340c00c0328481c840c1c00340341031441070512043d500010010b8005540c00c1c444d0155000c020303990300b0310884003101204030541c114030381100d0006c1c8181c210540206031503c203005507440001c0071041c0426940c10806120844030b60f2001030450782d00001050f500f0107000082099154100c1402684210f0745049075510000502c959045860b01d02c40c00201560302c1c0d404501d000e50b110329180200a0030070048045c840000104803942030703206944d281c0d075a40030041d0b480310912815410000e203140007210b04030b1840ba00485100c1040c1409261000a00030a003088410410080100700240040c46540b6100c000d2030403c0d05500c400502040b00c0c94103070f0019034400300032542c100f5444210f822a80d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 118194217 1250 118192967 118192973
    0x20a12090c030602030705190203040e0106050306030106090f0b011e0f18030f0b0601020606190b22091509090c091a0405040c05010f0507020901060305070c0c060c0308010e060d 78
    0xa04003208098072124001c40011001ca00c0c0341c002580304401c1c1d91501e69817410308517050b00a0040001e288000c54206000900518224040680c1100c0d01860b0558030b0f5210740c00041e00520741b5521918130186810980410016150042050b840090b00c42913814030704402404102044500040000340301c041c00c1c091594060030f03080315101544030000510a849a42e002450070b00076030150391500c104020401150381c10481c407030b8044016241144051080c0c02c070100120a40c0c090007007140c034041401c407030b01d68071110064030740140c0710031141e2040d03a42c203054002400c0c0000c00143e81103c1c0c88011414101d540261980e0035405950710078a141f40c45c00d51070050100c407940310180401840101c1455036180a494015805108001c80051403c0e0000d408c1c0c841c10b0f036849050200a205080140c1c0d1560f08007411581075080110303c99468000484d61140e90307880040443c00440b50128801da400011681c50314481c0c6c03105c0d40e8698807059018400f41003100c0d0281e2008030160a4000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 118195467 1250 118194217 118194221
    0x1050c03040506070c0801020a091a07020d03120f050f0402030d0503010f03061503060c080a0f06030312090f020a030f0b01090b0d200a080604060501090b090123100512010801020a12 80
    0xa2401740c2c0c1440009078940c2000741c2a40c0c4040c50010001d042d5800a2001d03601074845003e2000900d48034514012195000c180c02402c04900070381070100c400010900750b040b64004501c3c040e022502040245011100020340b00300070b90b801c0e0300034410b1020b000c070b825019404880c1a80d20f900d13260762440b031441e17503641d01030250340054000e03459641da40080081ca9a02512080c185035848007050b40c039296140e201220100ca1030103115038140310080001c20f800c003000b407140e04c03084000486d091f2103074200202c9184075040001d40100b0024000028001500c8034000203d120b01c030740d224142daa90003010b0555003000211075101030301e142c80c00c00049035086070300e15440400101900e00000240050900621a804588550004020802002058411240981030181e010413400e86c43c00e01240400c81c0501850f02d01c0e91194000310101d44101c08101540800201514601d040d20b020041198010f10304c6108402c041d00f00202d4108818000e44101c0c841c3d9a0b01e04101e28078820341100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 118196717 1250 118195467 118195477
    0x151915020f060c0c0a1a0601020c0301060b0f07081917090105070806100923030f060c091c080316020c0d031e091701240308030609090c0301051008070501050c03040506 74
    0x841440b0b2000c2c9440002c40c9506c822100076002a01b054041c40c00c2c84c00603080940780701c5d00a01c20307450580140040c108000030b4480245210103000d40b505c2091412244501c108140140100700c9200f4031100568800d4075021a081401c00c0c040c815111142d81600341c6070166103040200b20414005480742c106080d00c44402c40d11441e1054241e075484040000c00702600c48541d69032030320144044d019003401c11007090780800742002004076140010710800c00340a13071100c0b03520400c03101c42100c00541c81002442a0f0642110007640e0300d00703107203a0391403034104185051030240c010524462a01c0c5045030b8030010690305a04d50303080b814000008210000c0002050300140005201d010545003090310100c0340307000104000082101d00180f461000030145000320f008000800310a0000074198400d498003c0d0b0103858550254860040d0242040110a03219030958a840c1c02c01050708000303501081254100c10584e054a0303101ea004480701c0c03062201200107580208001c1000e801d00b040240f03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 118197967 1250 118196717 118196737
    0x103080406030e01090606080319051206011b170304060e1507050c0106080303090304061403070203120c071401090201081b0313050a0b100603060506040302010e09151915020f060c 79
    0x240000d801e6846c14200e03100350304030394880d500100d60009008002070080c1d072b118502b81084d40c104841d40700034251b044070040c1503070f040010b241d078041c910204500ca0518000c1d4000840014a400ea6080140541048500303035202c506104500b28420000300e80b54980d40408002041030b80d0f45c03828107455650103255411025981c4110003d00f01c1c1050000d0350041010303101442e82c503881c06a00a0171100603890349003508004205024420341c00104a0780c0140c0681d00083c4d16039030f10800c81070180100700001c1c10f4a0040c0705069981304040d4000e00c14540300740c031141d08540762241290a41041ca401100000c1810400700c0c1d035030a60040c82c28840c0340b140d8121018499180d6400c8400001516080e0652102040c10b102240d00350103102c01400081c1c41d20f6040500c1d5400080c400000c0c002c00500a00c5040c0101c5c028201d424000c0c0c080c0c40d409000886200c5184070440c0641c0d12034400c480c10f2414a981480c50030b40301060b465698140140204060b8a81c00702801c00d40c0d124608c92 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 118199217 1250 118197967 118197971
    0x603030f1602040f0c0203031f051011070801022502030a0f1a010b0307141b250f0b04260109120206070c05120708071a0403090902030103080406030e01 67
    0x1600180c40d500400805060411005810440d44140016104820b0308a038115040c85d1a0b07401c41e603400015642d0200c0c03d0341d182000c21081c6000446800300307640026070048440311405165030b4102c07140e400758052074800c442446659500c1103080380610203031140c1b503881002d0002e040540301103201001c0d500040035279a4100e00b036500c000702c11941440813502d0201c5c0c06d030b48501102015441900401602a041d4179628007000d0041c0705800c050390085200401150000c1c000741c81415800c26001c108040701c2c01c00114a0f0340f1400c511149580043c007501c03000c40401c5015459150204841000550504160034070034125001c28103207081c0321250410006027100c1e4902401442c150f03034001c1134000c1c940b992121000b424840000c0151041c45904401d000c0010340000380c40f20b0b0303400f02015444d01c8841c14171b41036010344074004015000d0301c40c4582030040758002d030a081d80200e10944076500e1079540d5601e448141d000910001d440d4070300c203004c2040180c0c000e0b000312085010903000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 118200467 1250 118199217 118199227
    0x80f0118110409091103150f130302011b0306080c06090d02120a061a040c05070c0501030509030405090a0f0b010903050607030b0d08070f1205040503071403010e0f03070c05041b0305060303 83
    0x948801c80f038800c2d1003a168110002188005c9040a02601c40d82880c5c601c2c41c103410307103085a03010641c494050444a00400c14080c2d10090502c00e5004442c1c6484842e004550300440b414024054400c0f4000c00d221400351000aa10311302d002c2c02140e0701d41401a146020703c00403502049101c100211860b02c445c05409803400c0010f905200c0c0e00018400442104446100c1d1030078041224070004a420522004026010121f07508502c0042100c10910740421666114030000b4194081d580c0a1500725000d03c080c8032031156682c2100c0c03a042c0c0120401c101400e60308004685010031444060b0160700507078046000039211360001e020418001d08022003418480c0d6442d00ca1f84e0151400b5941c8840c2151400704114440205540619240c5072682c242400e00c000251600300d40e110307940d10000f04944174581a1030a421450300011501d05640000641600700e036201d50203590221030303a403c04100403580b440c0600c5004480d4410724100c02c0c0d0003508400c254000c100140c40c9030303070600c02404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 118201717 1250 118200467 118200479
    0x3080604050a330b03010506090f01050405040c1d01050702180a1808130603020327010f020a320307030e0c060c100e0c06030609040303020408060f0403080f01181104 73
    0xc0e007800550f803801d1206018101c0d500c0d06a1800903070883c600d8070908000400c45590348400365250040102c0d0701d84c09010300c000050381c85100d01c1d4010707500310741402884252503800510814490b00d191041d075100804800c01102d55101d15000254082100c0c106c90100d085d00324052940141001030002d0201906044080e5894611100702c820410010340c07180ca41625002840c010a0305090543c11810a000404e000e202e88e90b0251500c042440315904070f079a03094110b80c0c5501c030080d00856559401c246d0040c0781c00b401050000303c0304000000030940f10103090984101074960a9542c3c256100c118044004d030802c814aa0640e200300412010660b4a8100a02a0000401c0244100c1c03620600b000d042c2c80030603160290030341201c0d05c82401520ba5100b10382e800a4101c4501382c0c5680c0b40c5c0303000d83c0203002e1500018068421681000341d0f142103c0741041c050741c0a616180940c1c0c3e03070041c400c4e01c0d1050074000d410740070501c50b500100580081d008000c1c0405042240c0f401d00351035003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 118202967 1250 118201717 118201751
    0x2011107140d02010c0e0411041a040510080405070608060607170409180503031519060e0906030c010212090103142706040302060705070c03080715050109060303080604050a 76
    0x40c00e840090007400404048042040268030080700c0f0300090000242c10309000d0030a004134a0068090758903003000000b941e0300c44007140d0282c040e00c03000e00040e40c5c1d80b420030050380d045400703090701a0540402c1c954940c1e0183c901541710300c3c1d204000305210741c1031440860342520060301d0a0b4009000b80503440000382d45004900c1440d4910a8180d200c503d400c060205641c0541c0030050780754010301c480070100c0c40c0442142d9100e88200d003c0ca005054030000b25000c620800d074104010003600b08042041d82c2c0c0801018070035502220f4501642d01c500f010903840f040036029641c09644440d4240000020308005010620014100018010414000c0741c2100314120780001ca8007001c03040d009030702c00c3e650102400c2d122408c0010030713141c0303000e030b4010b580e4410252140d4103001d4042499030800c80b00206000142d07511642d0b80341c035480140703403c404040c1c124400842c1c440c1040d00204221a4a10132002226010f64074480291100720134040245000b80c503100c81c080e15001000842084a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 118204217 1250 118202967 118202977
    0x110d0c090504031e0c050304090e030f0a0f3b22050f10061704170f0703030b100905060c10090305040303080f1603020c0a0605100504110403080316020111 68
    0x20348500714002c04e08a41d51000101c400c484d14180b120001000e40851400025101a00d40000700024400c1d00280c6080c03440c0244480fa04402c800082c0542c0119030014196011880b9a12007044111150803046800341034800d4a1400b840001000400c08502d43ca81d00000308000e0403220b585255007100051070060781024a030307100c1d00c91041c8030b0100003203120366070f008002205000c43c550504a0051070241400380526040003004046024801004201000c00d083c810041d6554803442d21042c0c1d42c3e07001404280c0100349410000c4050703040c5000592050300841d691051106e0500041148540250890750018403941c65007208145143c0301c0c04429074000d07100c01e07032628503514008111a10080198042900540520061036100702e140c101562180c2030158a51405926251030108844400b400b22803c0400384007085c510800d144007a28416078080c0050004607414104600c12072100809150003040060000250101440b5204141d840082011034029112055680003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 118205467 1250 118204217 118204223
    0x904060917070302060108010504050d0c0c05040614040b182805010602150c0901170405030c1f0f06050303070803040804030501020408011a03010c0c0602030a0b0d0c05030106050904110d0c090504 86
    0x1201403d050b0104212401400d000b402404a03142c65070f43d00b612180d181c13805100f8810400c178200200030a08d940d08000c0c1802400030004556200305a855074803018820a01851030f01044803158101462811950003c10300310000700d4440e943d1074040420003509482d030100b00c54016050f0200c95004160007480b00764020010005400b910020b5000050700141c3e40b03d2041200a0302ca0340c10021014807540d62560051940d40c403414114218824291091041c4c010402d481215400c01d0f07207943e0a00c01c0c40341c4208001c4900d54605404c8900034007855a1544c020f200304070000e80100029030303001b440350395002d04003a601d40d159400d9070000d030000b0015944894003010150751140b40713010180002c8000b80214172103110050001c42c1e110382c014190640000003d0200307000b82d04028210600500414a103c600342444006640c40e40034252081d420044001064a48586028010382c0c2142e24805500088400c0181e51043c8200444210200301000035a1800a10440b4400c0340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 118206717 1250 118205467 118205513
    0x60213050f0a12121403040b0906160206010b0705030c0609070515030f191503050c03010c09081b0a12062c251a0703030c090302060909040609 63
    0x400c140c01c010703021150840490081c400c010040120900c2c00202021054101201250602c403100c0119102110003d00500ca45000014402089103641c90309104401410513070f42e05803039000e9030b1001010104c07105070041e03000c1d8006010084440c802041a2441042207030b1514a0084d80b00e410b0200480d0b03d02d00c04d42205404110303d0400b480705005016040320702070720b940361005010307202100c06084507200a42400030001d0b106e00381c1c1c2c0a24101c1881c0490a00d040341d4a262007991840035462040c00381d401e00895240160180c05841d064070a4000a0402c100354034007200d220141100c00103a101c1c0450710001540341d1944558070354280142d8012406408123902c2c8600e900341c900b000440045c00480b00c2d40d4558010801c110000c0004007040c0030741c445102040502c1c907542d0084904220318000140440c80d5120080c11721500c0794a050200e290701034000c0e00c071440b41c2c0c40060b401030000c20803c24945801c0007036641c41407085900140c0703c20503443d01400844616200d0407941c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 118207967 1250 118206717 118206719
    0x209010f081509010326070c03031d06031006030e07080c0108041703010e150a060e12010b1302030403020601140d06020307030e0d09060e0316050f010203071406060432060301020403060213 83
    0x11b180300d0003030300306d0300b02c1c1600861920b0500d40e0ba00e4203034505880083c081190309400c445520280350002079000b080102656100d08020381301c6060144c4e580b0a60303020074988450703007800420204502c0700325500207010704070f042070610055801400007801190424203201c440c2001a00f03082c003540c0038060504440560317152184581908101c641500351040280c0c0300308100c1550f015001441c940c01c00c0d03505400702c2c000100ca03280549035421010364861080383c42400680c0190303010b184110701940c200d40507070341c2e200102031040503030741d8605801004082c0c1c1980800c0d0281c00854010b01d692900081e401c212103040360400d01007020740000200b000508110aa43c810072158200070114060091040080520103500c082c80c403645002d100640034550b640d030700900584051a410402e010a120f00c020341e0a5116a41110010310803441c117694960340200d030700c0c8012010f0014131403e00b00840c2c021020700403120010302c07155041d9000c200120029402d800030b01890b2111130705a207a86 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 118209217 1250 118207967 118208003
    0x303020109020f011806030e0f06010e0a0b150f0a09030219171605100e0901170709090302030703030509070510050705010e030c0d0804020103020409020c0f100209010f0815090103 79
    0x1051210009410402c6a40e6900103805c1d5810b103500440f44103040004407072041c070f099a401c152058840c012540521000056251401d1040320303c40e210706141008000000b6080041c1c4010812032544052828098000840c0545009001c9900d16040c2a040b680c0d070307a8000341103c40d585034481c04902010002f00042907402c002001341181c1800a0020804442d043c3d40200000b8440d0358440c085044180005601505007003440c0240a0800f08031581c4030f10f5601880308c080340b007101c20b034441d0103400603114000d4401e480c0100d606902940c68190184c0342200580006040c40480380651100064255076030f0940300b1403440c841e2035040d12144241841421101b404940710405d4108102441a0101c0030850404421135400d041d2000d840d43c0c00120024020b540080500c903100003212034000d480050807138401c07000320301201c21140b800700e107100c142e000e00020382d4081104041104e090600400c8903941c4614480034200034010008001803214200b81e00a880740ca071031500c11415 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 118210467 1250 118209217 118209229
    0x5070c11040c0c1127011401030b0906040506040f181506030f021003180c1e03020105161a0a0b2b080c0c030d27050f0607140106030302010902 63
    0x101100c11902080000c1110350003400d41c80101d0001418608074100d00c1c1e45503550400c598040c1841080344200148403400b814910702d0081c0200710340801540400c11a0758401e00900070159000b0b00104501c1c2c82c1c0905100103050301070581980b003600c40b070f0056000fa6080c071420300420640716094601a01604010322031101808603520260705122003840852200c1415101269058030002410410f02c2c50440040003460101c0c0d0001c03544585d90400d0082061108043e0b900741030a281000c640940d65403401503035884002e012134010f10100c2d01c1c2290341001c601c02c40d030180080b9000d075082500c0030000c98404031640084d5581c0d40800b00d6807404c1044150030602d500a01544419087c00b81205154101c504014401a400521607401482c00e00841540e503401070100e070b40b40a041003000d04050020101000107040c0901e01039003502c140c0010908a49010309104164801003003030109961255800b600c0c071110f028442c00d048402480303080300450284e0b000090445261041000d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 118211717 1250 118210467 118210493
    0x203060c0d0b091e0606040807030507090e010209010909020a0c020d0807061b12020a032705010509070501090e07030213030506070207051f0c1103010207080c060901090302030a08100905070c 84
    0x2000f40c68000400ca80c42c000804140700c6220035903422010ba54030f00d40051414400d94101010764001c0401c000100600041c0d03407400d90380e499606101e170f0208122500e00300d01034100443e0000d040a4002c1004059560081c01143d44501c0c01c451004000e0b004141c0d9601d0040c03085418881c001007600c2400b07001c0c40b4101e16070605090343c1452181100e0010084030345030b40141c1000354009040807074a0b00940c85900c6242d1001414000e595288281040d10003010809641c8c650030000040d1001d10301140305410350750140c64070410641000c510461428005000b4814941e080009810300040205180c1c000c51094006002c14500240c4c0281071100590165024030401245021210340503c01452445103d00d04031030040d080341069012a0401030229426520002d02041409042c5004068409240741100c140d5198400d0310f07401ca07480042c0103001600140815518688100180c1d5006010590a40398035a200d2101c0c40c02c803032043d5603880203d800103000904010f40441002d03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 118212967 1250 118211717 118211719
    0x121008010917130e28050910090507050a0b040f090506090a0203070c06020309030d0608151602030405061201080c04090203100b040905031308061312050708070203060c0d0b 76
    0x40001070a640e1150200e001c912450b00b15460003040503200308580300307289002049200b00305003540c2402c00304601c402e000104a00750a028100103010388610b1030007028041c1070b140d80140361149a006c02c0100a1140d100d04a8076400349481c00a9141e0700c000742c2e04054550f4415180d80ea5144c080f004d001c041056021034400c07810001006125a11790741142d5014401a0015980c1c0d541d8100c00c44182c0d080020040201d440801404085031b400405000480b01c0c042c0200705240c0c5490041e0381e04c010030008055203800794000200340f25581c402e0040d011680b401100d08003526400003900381c2d0001130b050401c01090400410548600b0000c0c44048101038034200100700d0182c01294845da5001d80c0c90031525110f0b100b00c041901e503039010f8042c090708003068a880e20745108c0e055010031118803d024480c070409012460042040b040500b25550002d83c0200b0080b0488083d01d0030b400414040e90340c110706000c29809a20b09115043c485c042c2040050b07511299032501204503032503a0041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 118214217 1250 118212967 118212971
    0x10c06200c061f0b1810030e010e0105060f01030b15030c1e0a1d0604030b2d071d010e1003050108210403020d080403050a03111b01020a2612100801 65
    0xd481070700444200001d0700c200c0446103036074000b005080440301c05002d0710550010010340008010a030b065104500841c288c10080c072082a609007980e090b1a002d5800f035070700031442c81d07409445600035881210076540141501403045881c02885240350401c840080e0104000106128500b034100e058800c81c108a044050814860b00b00062a100300d1584152240212400c183c070103541c2c1c0303400d42e40210343c0b00c12541e01510f1b1003d80b0000742d5440400d0325081900000d07802d8075094003009001d00ca22020381c0c410300810b001110411118001104a906111920200215588031a1106000c049003500c1c007044075458204000e2810f44110480007141d8030400507400c1c2000290100d4003100c0d0101c41d9080000810b0801807618421540000c2c540c0c424140036104140e08103000b4100c55a1881c01e55070b42c074100c200b1441810466001c42e41c0141c0024ac04a400150043e01c08403801f0191400c1000402c0c406040a619900c20701c00106c2d000301600c1040001c4030341c0740220004d40003407402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 118215467 1250 118214217 118214251
    0x30c060621030313060b040c0e03060c0307080c0a090e070e0901060824060d020a08010801050a09110631030b09071a03070c0f0c050f0405070e010c06200c06 69
    0x126101c2c003004e0b080c448804010009642404015008607248150050081002c0c40079000c0c0589051500251980a80203040c00180a960240f090741d05c14001504e0b0340200b81e03524114032801d0742c0240c80003028000a810301049441c0207050040c80390b8055240d80004011030750421500100c141c0c00350702045662030170800710908020420806101e2169000c1d00c0800c41d0001468500070700d100800000e1003c500305100342c0d03020a2850484450000800203900d82d1007440c0151240c1c240c020b004241034440d248134904201c4010003a11100501804924000302200304140b4400c00100000a04628040c424804003d40040e080b94000005250301440d24140075640b40714141c0844104e000030001030005405074210000d0b656002c0d080c03541c0e13440c3d90b03d0200d2014905020741400b42032001c420b20400d09180c841c0a0280c0025229860030341c400d1030045548580c2c8103021914a5102c4000c0e00c407005481c4404140300e81400381c0d0035129001c51401a2405134010041405860400e032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 118216717 1250 118215467 118215529
    0xe010e0a0b1e030106030209092401080a08090f0909010c020c0306040b010509130501050f01170d1d010504030b0a06030201080c040e01050f01090b0d06060906050703020c0f040905030c0606 83
    0x4007541018031400715454042c1e1441c1c2c0002d00400b8194800b9400c00107680400280035000701d510b11500c603840300f601d40c81d9a1a01e035804407000c424001c200543e8801c40040b40440c2403200070780400340c8001d000c00380c50440c18002c2180070109450300313801a910b0b02095202d8540502c0900311059042d8024841858180c8520424000610886001d111050007051114041489400031150800000d10403400d101da4400e482850034420748050b0104c00d0300a94808401103017502081400e139860040580d8084151039a86a030003801c5414080c04000000003e0218003a5a02c1034008141c001a468594000980240e60040102004981c10801484202c050801c0c240c15201c0c2a00c134a00e41504001c01039900d0741658026070904131002c01c0c08948030301c168000c1030544007070b962500141c90b50740c4000d442a01503c54005c000d604010082006030408101c407007943e00004101003400c4000341c4800d402c50740032151842e0305800c140c00308000c42c2002140840400031a190680c83e80010705 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 118217967 1250 118216717 118216729
    0x601090b0a05060706200304020109060f0f1d0a06020606101e05070206070b010e04021216092304032a2012060106020c041b050702060c03070c0e010e0a0b 68
    0x4007031540300d54008a041310038007801ea80440d40a000404080441141112030054140c00485049000420b40030340810003d2240c0900500304086890352250350a1910045d40c10030085000f0803030791100045e040b001030707a4000303418004010f0358003c3c101508002c018020040120714940c0b09001080c0ca820182140f8243d101c1c1d0340118902e4140d4440310341d4400595140b080c008098240070203600027141c10303180120844c1c05940300b00d40d03046d0080c0c1d081c2c01090b207500041031820080304c5d1040b400c00896440350825504031441d2403d10040d1010501180250b900541e41a0006a00d070962211404201c64003001e10210b01065104003aa1b199544a040c0d440301541080c0e0b25000343e64100c1d0b589511a03040601881a01039540d00e607190507009654040161000d031083c0d0a1080c805201114101c00c481001480d41c0da40e450000242c00748243c41d0f100241c0380f81548002c102c020003080d10704001c14090030183e5845490b0f54074144611111b00409409242003030314014030b1200607680d41c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 118219217 1250 118217967 118217969
    0x20a2f1507020108090a17181e0409020d050102040303020312070e0d030302072108160c051e1507210e0d0e03070b0409020d18050703021e030f0f0601090b0a 69
    0x91814192a0742c402d07018074140006c000c80142007031200c132425603a4841c410060100c0000c1c8904440400c4421005c00c08040b90382d10301075440c5842c4003103210960520380c00c12541c160018016841004660381d0791402ca9100b0390056006800101d070160090041c16000f0b0781010180c80e04105807407103003001a000810388000241410b500081c01d5080081c5102e8403428500d030042d40b0b140240d03100c4000790120100f1a03075a18008440c0000d030800900599503036640d07542240003028103c040d0301c2e000c076000310300240d5041240b050444c0c0c02c101c1c00d0194100fa108600a0ba06c081d08581c104046c00c942ca101e0032078268000d4201405800a00c000081c4c500030340e007070351806a600e100e055003c2810710b02d0382d40081001c810f00040c04a04100c00d50000e1030101c250300380801c403400a200395000c0140742010020080d8200020400c0580381c2000b03aa14000d4400c0c00d86916449280002860004008004072558000240c0b0f5090f0246c1845107074018280d001e0180185aa290700180590200b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 118220467 1250 118219217 118219219
    0x50f2b2306150103090f1203060b0c07030b04050c030708010b090703020301080c13020d0c020106140a0302010210020c010b12100e0f0d0c050c15030a0b0102010b0d12020a2f150702 79
    0x3000504000a0780310f6004441a150003681e4a4480134907030800201130007c0c525100c0c00320b41013000010f10802c00303104407a01c020b92803002d020b03a20b0665a80b5003404002a000b51590700c110300f05d5005e180e9050240320000c0c41178030000516605614240306444e24002d0000e024580305000400803124081020901604115080c66148506c1000c0700b000340a02c0104107012450148049240c03030301544803000381d0b01c0000c401c03555158500d08200380d0078410b0000a0042e00102c1001e595000380e44c0152089400384800031407001c8454000c1141c2c0c44500038502015488101d61414a6500c0c2c400c440003000c100011344200c0c1e080c2200e041d640e281e512222020030411030115800c0c040c0920220f040304034028442143d94507041c0000500d03801c183c408400075440c001c0c0c83d80040d801407156140448015142c505003415a84032201c0401ea940014801c0d03024100c1c0020003e0b20020302600781480080082c0380c000b0311494225082000355503080d0003544e100b84910a252502401d0b070742074981c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 118221717 1250 118220467 118220491
    0x80d02031e01080a0b060d051006060e090a1529190f0c0b01060c0503070c0602011b030612020d0f14061009140406050c1204030504030317040c050f2b2306 68
    0x1810310f0f10500e880e200c13180d0034090910b040002f06045d0b911007401185d50b001107070030390141e80fa100b1485040ba074001c04080a0013890000c204611112000740b44050f200340a08040b0703e0340d084000c1c0c291984162011480d000c41c2030304000398660043c4100109000c60724018030010301c150341d51110180107000d15814000390f800c03090100101042298090b945c01800030058a55030138020340a0508001c40701c151507600894020a144684502c3c8210f8905c201241c07e540225020300c449030901e00c030309980b88000d802d003103c00320700d00040c01d0840480b80002030185142c0007500c0d800d4850503422414070b4030b09116083c804070f00f101c240c5603049a0020000100f6840e80a420f030010b1041200c0000300c841d001c000c00050680000180c002c03640640c4581e1141b66070020340c0454103104a40c01420301644002c00d00950800c45502803581c01d010700200321100c000340e5140c100322104480e0341213984043c1c0303400003040207204540b4825050700c0c2800480428000c40c1c161a6540101560001d01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 118222967 1250 118221717 118221739
    0x4020c0a080409050108150f07081b033105060411010203040806090309011805010c120504082a0301020304033908030403090b0412030c080d02031e01080a0b06 70
    0x88000d028400c00964004816555140e8034030400000e002c0c240b0941945001d140070062010303100007030b41440340c0b0000026011070307a590002a185c20901a01e4100c1880c8102e407015030340f160703e000950103041200384501242c910040764517100c800e03101c0d104071518400d00e040c02c00508000340881e040713544a512502404881c100403885d5004030b03400f0b201d06115400038040c09010102c020104450280e844014500e200035aa51038098640f041c1400208154900c40201e0580301491884000d02d12303209180568a0343d01c540b6101c6a48804030300c02d901400310288454441100100d16501640298110700c0c241d20040c20510a0000504001040c6e45d41d118644080c128540d5070300344e00060010f40680d0b2403c00d031f5001e4004a40460115000711408141502ca06c8117407402c480450b1460b00529400d66000ca4405041510450b0700c41c000b0301c4140d030610f40500207141300303100c07098007030b01c44000141071149030500691056005400c0205a400807a140d004091b070b20183c242d500e01150 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 118224217 1250 118222967 118222987
    0x9090a110a0c08070803010e0a0c090303090b090d080315040e0a0804171612030f020a05070510050c0d0c02010906050f0316110109080c0c0604180e030705030c06010603050a09110402 80
    0x3d8031907520010030780da00000c00402c1c500030a0010901440f00101c081100200120055901003040d000180c0840c040240c200701183d1120000c100495000c0c4c425104074585680f80399168005030748a00151100e04e0741b2070018100361140030010394406005080303c4030552a40c9101b403041e80503c6550b00c14144040700002c408012002c0c002e24035900601c002d0f42e444000c201079038448423040b000600c07080a68044144002807491200c1d8205001d014110300c0d01080026405800d101c50b010320505011204580d41e0074000343d40c00c141c20307440e201e2941d1018400100912031580040c4140681488107074021028202542c0d408001480640c1c034800e0302410507a04111f8034411402c2a60800d80f6840400121b40054444104410100c8001c10000c00420180e03008501038480d00301c854041e0000401c80710f8000010094202090300e28001c00c5407151429607021200c0c022080d4052001040b415030715109695008641010410985240b40d84000c00c001440303c0d45072240707070041030301044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 118225467 1250 118224217 118224233
    0x40f0504020a021e0a0c05030c01121d0109050a0506161b030309020418060b0301020708030c030403181520030706050c0418060503060a0b13151205010209090a110a0c 73
    0x101034403815013180c04000807081d59031342c481000080300c500d28514000121801c000a6034454200140c40304040d0000c8201004c000305058002040c3d01c0080046042e00148203104005407a4000c0c806450311a40900707029280c0790000d050090390030861031820468991102900c0418900e90601d002ea4030190f0804401500000c81c01a501601e01366014040c900c5c43c109020f06a8802c013400d004c107610362807c1600302e0045580290108104000142c5910b21280007940e0040c4030b17003006c4554079125000d0074200c0302182c010034031205441082c11081600041c0380c1890b401d1080074107400d2940307645484d4903800340c03420081c18191510b0101d036070b65001c0020346000c0c001441c490165881010707040b20140c1194468a4000c0c05500f011420310801c84c0174103c0668005080c800403800c0401012000b8910300710203a4400300030000c00b00d500400074244c8205d0f01d010b280090788903001d440c200b00f2030602c081d04070000d0500e4840d00d44840e400f00740a80d45000c0603401c148030303004c03414108035034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 118226717 1250 118225467 118225483
    0x705040303082d250906090603020f04030506010e0703140105061909080d0f2303010312140a120e06010501210b03070f150e1c020613090e0d020102040f0504020a02 72
    0x241d43c18000d0104030641020710000b168903201340319a100c07102e910000988001840c0d002e9100020f0150310244034540c047c0d00101142c103d45041d50740340a5032522203070f042400030303040f42c0c0103031000b001070054150f450300401d165981030750800035041d49410300240072842882c6d403102c01782c0320b0102d6500e44a40142d03922070003409014185d03881042c1a03032009140030038000b8400041140d0b1104405140400014510645401420245145d085859003030385c1c0c80d0346511580411102e14a81d0b100382800c080507181c00802c1e901c0f1944502c10002000068400c100e4107580783d41c3c00f250040240340ea1001804403524010003880380b0300f0420112240161000c42c51003a0075200e44800061400c000d01d0100007200e420169442c0f0300d5a0a00c81154908400510103501c15000d00414035030102c815100c00760584003c145501d402c10391031201c1000c1342940d0080203000e90700d80003028408400e01c05501d41044610003146031030704001240900204900645001d10f5000c01c6480e0810300801881c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 118227967 1250 118226717 118226791
    0x807050d050708061305010506070311030c01020412110d0302150703060b03040c0603060f1508060109030204050a0b100c030c060506060c030c0c030c0a060203031b1b07050405070504030308 83
    0x48290700d070101c405890760200707807011170007281c042161100300c13512445031a0607260010f0a2915002064804076800616080d0940c41c901040218501c00c030f1091006000034404c0d868408046255030a00c0030001c10a9820030380a88001804180005d601003100d82c7e5182100310052190f0710780100031030003000c55030480750340d010b000004d00c0140040c04245904680d2555810304c00541ca480440c4440380680c4501c1080008508800412901680c0c2e691350249061400c115450f54980000b001d603401500d5030040c10b940e444c2c1400041c10305525001c507243c01400d0002d40c81000d50707001041c101c00e4560280060382e4031004507046079505802c44802a0352001200e840b00d40100c10030b91220448461948a8400c011024400e8140241003004895443d0041c6086276182e075203614468042d50000c1d088900100b200006121b105590142d100781c0c00c0700280216400c1c10213101c00ca03803000d0408010710000380030800003e64001a125401001f011440813000c075114645141c9a4046a282c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 118229217 1250 118227967 118227971
    0x8180f030a0c0b15060d1a0405190b0f01231905030901060e1603050604060302040608100f09050613050c13050402030d171515040b09090c0a020a02010807050d 70
    0x8615020b9000c066000000d001c1c00d40009107841304000388002100450f88640c0011060201c075900000a40c010360300c80a0b0043c101143c00c2c1d6500008046440455900d01c15140449180b178207148903200e59041c20805403400b00178054041d00203010032000308944c00b0003c00c085540f4542c44944c01c2600c010f04401c80305454580c502c4032014115400440380c50040d50703c3c0c8a000580f009100100d207014a038000c140000d060751191088000d0400100300300d81141d00c5031000001602c69104c1d010003451120301500c04a4041029242500c034413440d540c1c4281d00302400c0f0301c0801c0012030740701e4114609000c048003030082840d056050020401c0303650b610110001e0742c000340310140e412043c8128422015500c0c07076660004240e07070841e0501179031410f081071840002d00c16442d841540d0040070b40145602208242cac80e034580c0940d0300c10340051910780307800301b080c00c2941441a031070b0b07030088a101152402c21303580c44030080d034840d04904064104611f4a0100b002c581c0100102d800e101104001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 118230467 1250 118229217 118229227
    0x40f030f0b0f010501050d0903021509061005040b0a0b0a090308030f16051204031409060706060603051b0a0c0c03020306040302010c0210020a090b07020a1d010503120a08180f03 78
    0x40003611030859065944600d000002025056103030b002a060382c8058440508092100d0000703002003003001c100f1400c0d88503050303c4040030110080010300c541500c000801a5140200e800035480900d90321081c06070b4244800c0700f100b66504003004098941918030369480e101080c3c0202c0707031a6802e6101403c01500042441848500700701c030980300341911540d00f145030030004011100c0e40302e404298061190900045000680b290070100100150b01ca1201d040c000860f00040305580814022180c1d1540da080c1045030780d4140c05480d81c440c40401058041d003030109845907a40c420210003400700b000c581c1202040006030a6500040c1d60041c0448104d0324040c03802900a02203a010900035204e07001c444c0000d00703424021a200505c20340d0366526010300e0120110b14513000004101d82c80300481001244111340d90000d18603001c81c41e0000c800d154505011b25081c001402ca00145d484070070044c42851981010030981c003c0502100441e4600d80c202c85c060602e0b4034072800d1840c03400001a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 118231717 1250 118230467 118230473
    0xa030302010606030b010c150f06090c03020315090105060403140a0f06020d05100f0302060306060d2408030703051204050a05010c2303090606090403030e0d050307030c080f01090908040f03 83
    0x40b1400640703089072010040d450b03c000043d1740740c4030034030030081c141480400c5071219404982c000d1205407800c0c07070012a04a440b90a00025110001c151500283e0302100700005804010403902101505a0700148954100000b02d01944654000a800c442c207089504202980411042c1a01c030f4000440362125402c0d450a00080c2d800000201c0340c582c00d04011171f00110080f00000b084a5a810780024941c2c40c59090280e560401084a40d20000074400c0d07455a01c424000d00109416008102c01e108655640e01d4801c211103400402481c1c3c014441700c000203400004880344041d0324851641160fa452401d03600d44114000002e10650030504102c817807580241c0900000d95929a0800504e180301c0d651840c240401c40e6181304641c025404540c880c01d01080160300580a460b012410400c00300304203180c84a044907080c0060700002c100074001d5403503c14034582c02da0b54503094910b400c22503604140150180929044a07644111280822440100b2500201040c0c8540c03084140e90381 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 118232967 1250 118231717 118231721
    0xa0507060909050a0c0207060f0306030c030c05011211070303090809041514030f0d050708070605010e06040e1903050c01021c020403050708030313060213082a010c050c090a0b0a03030201 82
    0xc0315000700381d0f09040200d0b815107094003a002180549a0060105501e400011601480717000b40f210f042c50742d41c14001c804120000100e101131801410802c401900d841e0004207010210503c44070907618101c01c160503440f1400444100603014507001c5132100103070400c03403610b02c10a5419a8440d16285903613855054017582c040840c4e544105402229040e5020300d0303201d8060a22049041e000403c03c140300c18054800b90240c40e01520401d400c000e590360b80c1004660302030b040142800d00c000104011446c2500690340c0d0101c50314003400c171b00e00c0c0c0401241c050f0b00b80c00c00010140039012a241811020941c16500c1c0200100041500d900da640c9810000f9400f40c081aa41c90040b0b030800300d940900001140e016080054994002441c1e507110a00250400e0135480c503900514280011246001c0007180d0561781c89043c0e03801c900c000804010030044840822134103001c0c1103000d040210308007041c0c7c4501c9080c143e03421403031550342c4210000240a0a01c005078004000400802450307415 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 118234217 1250 118232967 118232969
    0x6070312020310030507080c131d1203010305010f020c0d080403030f02130f060f020304060309020f04110a090806160e040204050405040f0b1b09120705092a04080a030f020a05070609 80
    0x1881506c280b181c40f05400c94440c40d480d00e40703940010304481000d513020460361003070071812004a810546050481d80d00c504019090340841e403d0b1901000500c00e100c400e12410003040c0074000210301e070803204407015469410104520003442601c1c0c0001e001c0c940240c103c00c060540d180e00440d03551081c0401c6c900031145900800107200e640f0074020800c00d0041355400c20350400340d0010b506052804404402a00c03e0751422a00103103920400380840d00c130f9001d6011b0368805040c0b041d84a0011080040801f2440e03882442503500c00000d002e01c981c0c6a0391025040c1d015460200c0d6035025420104d4082e01c1142c0c411600180351078200802d00040801440b4044e104002c44d03034181e110b00d00c084984400c01a0041d04072401000680d00d1841d08089243d18400c041d01a02c004641d02d01c00503a81d030701c08540c00001b50310440b0000e80e03050b505140200c10703010300840d21418282005100c1c1d580d946c1000b802420b212000080a0b201802004985601e5500508440c0281e0316184014031050341 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 118235467 1250 118234217 118234223
    0x2130606030b0301140402120c061201181401051504031a0f0708040b0117010f0c030615090e040f051203160801152c09040f02010809030301140607031202031003 71
    0x1a140c014109450180143c1140345441749000c0104e80b2680c007002230040801840d00d01610400245804946448028054580d4402d0b01a000c540c1751a9079000c0314501c5030b00f041c4060f4980f410a820200e914021907041d51002e4461004007070b600035070404540309980010305130440c91810348400702902440f0b14070900d00090001003030307200c515060300e1484090b600249840b01030780c018491880c84e000705080103030480001140041c5180108003c40e0b020034100800242c07222814881c50070540c10803c82d221140c600035011074a03140c00d110740008064002028115205c01715014043c0400c000c1003014919401d017540c9003001c00301243d0302004010070380b000c148110f00029071411903024411507181c1d41d032100d031100010405025110f5440e4104030b01016820029524070303448605103144264400e251420044009000240070620009c02e908080d80c403c00041c000c0b12002e10600c99042c0301502d440c0e440e8180c41c601515540f00241c0785c1c00c0c0e064408002c000082080392105021240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 118236717 1250 118235467 118235471
    0x13080a021e2d070306021e0a0f0e120c040b030106030c0b071505160c021c030e041b02070605090402090607030305190605060a050c160305030304030806030d120b0d0213060603 77
    0xc0e800d07030003040b02c0d00d40014500150b00b043e101040032440c0780e00182001000c0981114019607001502c03600d6400042440c00003550341c4041c00c09c040d0700070b4542c07040e410080350b44801c000d81c400c210541c0c5800007113071640100d4a411415030561400d40090000d5544880070408940c1c0b40c0c0700c90350568000810644000d42070740705503008009540b00d03075401340c1c40e121920a45d150b406102a00c0072006030804030380243d04a12807403640a0440c40c00d0000d40d101755241903a107010f59040000740c450205101c08074103103428001ca180c60b00001d40108030740e92800c0480d2a156807900050080c0a0301d1034250b000100020503408055040d4840c41c030500c2c0c1a04903250094029042108691303041c040c4641100c0308008200e01140100042c100e043c03481d404560401210402c551070700c021941c000c8610342d2001c003d1004054101c80c4076036000600342d0060101110300341000f850b40140000c0e4070a20f55070b4503560f82043d180c3e070040321003060300681880e080c20110304940008101030321034040000c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 118237967 1250 118236717 118236763
    0x12020601090b06030105060703210207020114091f030e070b0702010f17130503070804030813080a0b041515080313051507111314010302090105010813080a021e 70
    0xe81c0500c20202c0140d0080c00079400c6a00f00801e00440340d0041c0021360074010500c400c0d0f041c5021081080d4012001301d038001d6106c40061001400b0740e48035482c0c1c9070b1814410300c01c020560300da2031b0810305401ea492120310420048441d05074010095071002c800c45000721031007c00e07280c01c4240107044492003030740d803582480c5d6540c0c0121288000703aa01c1408051080c0c02151100c41d844400700c030904c2c092400d40303150680558840075a5400b41e44125402d11010a901000170b24201148000740a48070180c02b101e4000d0b03a4071a040000100000c0c1080030791240c42200da04075521116500c0801d9803015400ca41302d9220940e2504508480c842a040c61080400c840c01d160340306000c403d0341455418140700186c0d58250001c54042580c6400c1004e485400b0940c468038028121001c0240721410203d5044d401800390342c02d0144c00640c140410107061007550400022181c0c01e090704803910075114500940b0403420f21082c054144c620603200c20000010001c08144002059064a0490034103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 118239217 1250 118237967 118237979
    0x120c0306060e180f060111010615080c03040c03060906022a0f160506160c0605040807090504200f03030703021501090903021009020102071703090315060f011b080712020601 76
    0x300c1038800b00f00744486120b03000b01d001c10054580c03254011005040c045265543c40c203295003180c0035036000009400c0040c1d20b03021044d4101e5001d94000725446402891440c154031003801c036803d184001010556101100300a11500e40e060340c081101300541d0000944580300415035038145021907940e00c0c0141c0600d4985000300040300c0d0103c0796181c1c4030136100fa00e1b00c010400e00c3e800204038203418a460f08661b01c001400b50900b500601500d0700d61036255030034056542d00d0068a50000600c56107840240001700781401e0180c1040c1501100c10036000440d5000715030688444c200090701440041000010907401188150b0100030400007000300382c0e80c2e00119415120001c038042c0150300810310341041c540e142c1c0c11420032940180111048141d450030071058008500c00083c0380c0d9000400c2102062806101c0710650343c2e8403842406003801d01c640080c2c9204105808641400209000c94420400310b0080740c58180e008207400340c40b45010f00301090500040d0300070000500542c0e0020400c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 118240467 1250 118239217 118239229
    0xc1a0f0f0a0b211002040f030c0806010605040e09011407030905012403021207050604090905060a0b1e0a2d080703030c06020a0216030606080c06040e0a050601120c0306060e 76
    0x380400c002c1c484540f040040400202248407281c41d0302c1030740140d07039003002184081e00061005040d154200008079203141800c1010307103195040030300190080001040130f642e1120542d000d460b001d248103103c986613502c2c41d50051008680d035051114060b8100003847e6090380c010b007440b500a000074040d088091000c0e051065a507980705d22410960401032000d820031050802c040c440107402c41c5c40d646c0d15040002c000c0d1704558401c1069503200c0040b4020040d0911a458020340144c10910054140d10700103940c40b4a5038100310002d80602c0321000c001c0c1d03240401980100031440820700c01000c220300d03410b00b0708201c01c0c099440c203203c0c210010314200000380400c103c0350140d40d0700c3c0d84101c0346e070340d01d070040c0d4001400982148258003100c40c581d400102018000d6114900000e202480c10304d2090411000741400c5110321000d00c800c01074696071034519075010409600004ad1591100010703281e9000c410310005059180983e007208032034040e44200c05851442d2602c0d03403002410300400103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 118241717 1250 118240467 118240481
    0x1030b01060306170d0e120609100c0f14090103020904090809030c0901080c1309051f0e010e030702090c0f07060603060f050601020307032d0305190e07060c1a0f0f0a 73
    0x1300036030241c41d440640340d100b103068071801d500052602c0390041c0107880c0d5600c0c0060590f022400c40c0c0001c52003800c864143e00c5454421081030404841e4034031440c102804958a0109100a644000a00d00d0681c0e209904030303101040024410440359200307040122071600040441c602a00ca112003100540ca00201e182c0e0499101e40020a43c69000b1000d102c202d81c004081038100c5d80e104e074048070000f5020701101c0140302128a03075080800401c035005e01030f281c50710045882c1d030b454000340c00701150020046a00168050341c801c0e0f0030b034458044040c854410000c140c4964400428080108100d0750001000c0304c1c014038060110301c8813441807608803201034601d180580d00801481c00042d0181e01048110600c150b0032411041d850401201401503990b6003000081e520340800c40034242070822210001c10050301000340b82810521b00366180194024a400d2100c1035840720100320782d0610b140c00e020540700d820b01050402941c1a4064031069074403810342e02200c40061500390007481100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 118242967 1250 118241717 118241759
    0x305070801200c01020d0903210507021002031909080705010b040501062a08130806150907050c0f07090c0807030509102a1112030702060a0f0209040501030b01060306 73
    0x600d04440488180e640d40300c900c120343d883d50240304119405240b440344504240c00398942c001d04601ca8242c80c1c9050010200c0843d101c0e180c0000e0107400c5074002000405260000d500503602e440d00c003004500d000c5150f668801150030140007034200840302002d00080c40c4108000d002c01e0f81d035001048250354090040c43c2c00584d124003c21015000003541c20b03421683c4910b400c05a40103501d89103074903400302c0c103c4010398049090401c514581040059031001900c441c04004001c0400007480e03010001c0c240d80200500841c5000c042d41d028411590040c2c501c0044039602680e540040001e8555000d4407004104600d0004038240d000740078180c0704031141c5000c0d15120b0308910b5124000c010581c900810648035101c07000318100c410445080c41d00c60307601c4003504941d14100103450203e180e0060500080d0900c01c0c80141900090020b42140b0000808641e000509442e44000d006091025520a041000000034482981d071054142c5030380e940c081c0032454481c2100d052000701240d0b10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 118244217 1250 118242967 118243001
    0x2070e0702030315010302070b07030617010b061801180303020a060e16060503090106170a1101050c0709050414011a0111031c0c1e08010602010c08091e160608010305070801 76
    0x250130344078034a01d442001005050041c20904240c0310f9106001d811500e1b980800e035549000e2110034410403001c1a0780300c108000b4000c41000c9404121280034640c0340207a008410b5160441c942e0140c01c080b1041490311203810f003056a41e00300250765000310042a01c820349064180408400d000c00c044000c1d0352a060000c803401e1601000f15003a5100503d4121503540c3e42c0b20218200d00300406d0100a03000a000030208409030741401500e8906441d80705040c030004221001ca02c542c0820300c0e80468000c070500284569490900c0c4034882c411024802017540703000608600a000302e921205111030a0303031281d641d00070460b070306039881c4580045c080c8412034120350030800a4264101c400d1711503a0b80381102d100c0000e140d090b00450440c2005a0201c2c2c00e0b00d0061121690900c920f0100310301628003c61a0b0521750203803a104d00340c0e141003d440085080010546e0b0208220040031100005213403110f650780c0348001080c1800170f00007150340b405045400070f0307000c1050045864404e058060 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 118245467 1250 118244217 118244221
    0xa091103180c040f0605090f010f0b0309011b0201020717090117060d14100b0d020f0904030c05031b060109020304050613060603020402030a0c0806031c0f23070302070e07020303 78
    0x40c2001191100d1032240688984000a1400c0d1502d00584182d903c08510120301c01b42800304002280c1e0004103400b1410f460380307004201528083d07809008981012114503540e44404ca81240902642c540c8010b40724001c04c910304c00140d0543c028403034180074240c80150070751150b440000c00c0c400d070541c181c0040c0d0628942c0c144040040c40744c54004d14014681c2c0e10504803a035489102091000b0b01140716000404d15a07040c00d003e019510200c00d0460340302c030304070074280e00064020109000150080007c18001010503000c0d480c0203141c01e0f04141241c0d11502c00740700b103541c0f104010300e105620340206800019084098005e5070b001e681d00c80c004c0c0420759602101040d030010150029500640c44006c00030160f22944015406156042000325040790011405801d5000107060729000e80d001454140a40540074852040004c0740e1604d594203640c001741c11103d240724803050403200d0400480c25010106032000401d00c2c1803081c1c0965402654401800000306c03401ca4001c0056081040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 118246717 1250 118245467 118245481
    0x150b03063c19030c0315020403081b0c0409080309011d060105040905030d061410020a0203060402090604230f0907030c0e060a03080c010504020f1504050d06020c0d05090a091103 78
    0xc445252010082c02407104100401c0c00c5003451902a070080d0360629202000384180800c0381c85019003000c8605041d032078546942d6842c0030380d2244910041c030002a800c0800d5280078140003a2101c0100140144021051410039045e01e07807054031517080315840c00c2c2da00d690151a40846c0300614030310901800250b0300e00303400d00c005842404400c813081e00080002c80c0d4035040a1080c2000340c8442c000031582060480c041c4030000091504440030765106040000050b9400242250700a80c19152081c440d00e455000c9009030040c401c40004500d00807400ca40b21612021865110b02001c030015070460b22140c03920303621020203001c09007200300c03501000c0c40005001040301d500710a0240c0203088040e541d88800b021078001042c0c9400300d9440758107002c10340ca0070f042032191204c02101c3c8001d5150344148800124840c0e8414180120140e80705902400701c294140d40c04c3d40902c0e415100400c0403200020559031181c03a886104040414011a503c3c1c6a882022440000c3d060010b2554440d02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 118247967 1250 118246717 118246819
    0x40c09030818030703081b0c0114030403030c020f0d020f010c050c060c090d0204050127021317071215110702010e04020310360c0c1203150b0306 64
    0x70800b580500c070314031000001418000003400d10591901a074020300403040040390401406000c3da6040183d250f0b1400358070b15203801100e0f0004d41c903041c001020025480306a00301405120780118a014422842a4241d008507441d000c844941e0002c000031701c10200d05a85a01030810b0045d1254442000901c418003190000c19607040020803610240b1840e6002406a85091704014400801ca41c03000d03103d0071140801707844034416041d0030b41c104038650501107502c00040c0b08044114102030507408024805110b004060a5030ba181c80300d00407114180810344460707489400030701500d01240d0381741a0a40300b094500300d40d4160348000280303210500300000382d00050140366501c002401c0000c3c0c4a00150200e109085010803240004106c103150180070000403078a1141c3c842c14000d180e140f05501c21800b8540c4c0d13038400c0a101e130402403140105c0c010070714265441d05072180803101241c0003080798042d51069800b1031728496107254148680309680c0300410b03010680d800070503481804480d07170 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 118249217 1250 118247967 118248007
    0x109170a0e1e01180b040f05270a090323031f060f051b0a0b06030d2d050708130f06030905060a020d0b180618010b0a08100503010203040c05040c090308 67
    0x503204145085e12022240380a034040e078040c0002a00c1d021080003103051014940f041410002104000e099400d207500840d071000600203c5450b90b914285002c05004050741040d00011710800341240c4125071240300340703900030399244459215003440303644442640440d80e01a01d0305a40d850000340b1004c8020b450070b41150802d5180d07581c261a458185860400c51030360694044c11908101b814640249403c0c0081c0c03907100c4080214440000150050510070780455981d0b091822801c2040c0c92401c880c107001d002c030000c051020000f4000d401a280c030000070299000c02c0c0e501607050b030703940d17605900701e4098981c01015904a44005810080c0e207034007a004181910801240ca0342009000500d2440310144c0b0404c4d021041c014003100342410a1002c0840340c0b12480f8a81d6541082102001c60003141d0080042001203000520344e006078020050041a0260081d510380c00d080c0780c14a15005d0700e014503402207250005201c0d140e4442d201450440340c00034003017850701c9c2202411241551903 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 118250467 1250 118249217 118249247
    0x90c0a180b0a1502060406060b040f03170903030c0f12031e0a0209040c0305040b010f0f031407030c030b0405060901060f060302070503130b0c0d0c020907110109170a0e1e01 76
    0x120050004011038440f0740700801d0700700380c0d0181000b0714081c03401c20b084403181d40000d0071202c02840140103200200d09540140c07030300a00304203005403845030742c0000751140f000c105030503000104054406810014000500c047c0800a5500c142c000c1003610307845000444030740300c60404090301844c200c80050003140d0001003051000d403030988840c01280903591049a2540042d41c0c400070001445041d0500074090708203440842c403070b01d203032050001e846066404041c020124a202c116903d07081049800001c5501040d442d041035601d0426103040c8104407801c1c1c0c2c05005082c00502104810300c6020190740d180288440c6050801108030000e41045c64200d4182c4800c001c003031560340c0c3c64007003175008003511203c035580c0351100000f10f400d01040710029000d0108078003007070005030b0b80c180700540e100c611407402041103594030503800d001d080000d10187ca038050400303004912440440003410201c009481d540e040c81901000e02c84000000d40d1500b80403490001e22201961140541d1308031160 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 118251717 1250 118250467 118250479
    0x306010e150301080709060b0a0c081305030706050304050d02010b0102060112060e030c010903120b1003180c1509080c03030d052e06090e04021509061204060203090c0a180b 76
    0x200c1501980700c9034002c2c0c0001605030f1110a0400800e4010702800018100e00200039040004e0701e44003815003819400000c001d40c5c0c000c10748031003802100c248072000b03000041c00c5500c1c01e507507a107002d4143d600075101a51140180d1122040050050080744c0c01440d040e4018411070b841c00e50800c2c290204600b080f00d480345c840d102d400c8000c41c100054142010700100010354070002d4a4040c050711b113401d068041d0b0342e0414060908680c0c881e00d40100c0b9844904004c91440c43c02c841003001c02c8800d800c018441c0203410400304098a00c05400142c11220b03803a052452600c4000301a0303603510148001e9070560007001040118240768105070b4010010b032403514412003440400f00c2c080e6240780700440c0c00011181007006004c0e880404a8014900200000d816040507008100c1d14100300225110341d520010302141c05403504422038100021414101c589401c103850100301951051352102c4207445801d04000581c039105014804680001c8104401003040a01c0080907044103856582d00070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 118252967 1250 118251717 118251739
    0x10305070c08190809061005040504140d0810091e020a0c0506090c03060106090509070c051204030b090105060603010825050607032001020a0210020c010b0616050c10050306010e 78
    0x1c2d2120b0280105240c5074500034072410b41e03010014061030005080150a038419424028451042607024050f01d0065901140c155600c0c28413103088040c07450780740c48910490200d094840d50000d5410301512001d61008100e564801102065626250743c00c014980400e2800c0f000c01c030b07151b00800090b5800d041c040c203134109540b10303242010003c81703c441181e00501301007206450180101d502512a9091440b07045081001088a209005180f003050042d2910500180141040a414a0309034102801ea9480c1c8074909034407010300a486c001041e60828011a51300e05d000001c0d2810b8401d590f000782088910388100070095030b40480800f4240c102010003051a4440780c00915555000361107052214010f800900c90300c100c2100f400e103050744180807800d55a60301090100c078011a81102688403100494514010302c1880c1500c0c0d4480d000040c040a21540343d4000110980544142c40f07402204200707108111403580e03158400141c0401c00990031b503000b403444c06003a01028181060b50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 118254217 1250 118252967 118252973
    0xf090f03011112070f090506090a0801151d0403020a03050715020d0e060604060302090c070305190c03020d030203070804020d03020a06050a05090c030f07030303020919150801060c0b0402010305070c 87
    0x1102422000508004000b845240116681c81d00c150070100c14030740240d1740540084001e0401c9640e005191054000154000c941c0e521841ca00000c1c104000003004545203014100b001c0b211140b29406a94010103214a1820059002e00d0310a0b501a0042d00300001c044c0d40403141603000740c500b1281d00303041d00781c00302e8688064405040108036072240000c14040512400c1e02d0204020501885281000c00500058840941c0b80b504502040070301c50b01c42543d440c0503038480c000c02001459200c120030000c990f0ba0b40c050030858101d8085e800359003030451344560031410383c442104c01d10045a520404540141003010001030943d0003481a80d130801410713520002078480648007008404d03118400c0c03106c0032005110b10710084100f2030007410f602c40c0002e00c094a40b2003510020b802d0543c00b1810500b6500c400c0f00c01480c102c2e043c0c0c1e400a05680307030101ea0150341094002040010700001c00891003500882004200640001607208155650b03401140a071000034240b070b003081035080c421000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 118255467 1250 118254217 118254221
    0x9042f130e19020309030a0909051308031806040b0709060f050913020c06070909050604020c1b0a170f010506090103050c0d15020403140c01030507080103030c05070e040b0a0f110f090f0301 83
    0x441c0c850317003d55030320f01151000a1030210281c000345016841d1600741300100750409410404903900500340c80e240c0c1e544c0c1d0920041c0c0d10202c91400500d000381d108010800009040c0035128608a031a10311f156519188201ca2501d40840381c90007140c010807002605d4941094580aa040f480e1409031400088501c441d0400100340c1d0185c0102e0512141801000c2282c0200c9611040c160380860414240c0300960303564135206840c186400b1041350091616464a81d401400b030017003024124090529142d19659517140c41c0d09019055103803c000c14858648080a40e042303a400100418590629404120601c0c5100342e003100d00d8a018500351041100d1800944000c50082d0b210078a0b00e400020400c3c00e001d01c20095504040c40d20781000009900520900e054941524141150817030301c1ca042441c0400a070040e40c00c0800c54400c100420228a201c1482040b10a009000c01c003500c803012416034251000d042c1348200140f0040c10400203c101600013180001c1c0a0800e0700c081d00c0109013 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 118256717 1250 118255467 118255471
    0x30a02070c090b01020c19030b0a11031f0501030b010816091e0801060509040b160201140c0417210a020705180403180503060408030402040209042f130e190203 70
    0x901c01c0c1c0c403490035038841c0d0b0f0144802946c0324000da90042d00200032a8032203480f03035014040104290340240105102c00030b00e60114040203400d906032a070700d0500c020b081c0c07449664183c00d00f5580c901040c0c041001c0d48a4040c40210386410b03195017034140c4034200300c030448403040810482006100200010355440002c0c03030031102a03481c0808608581001c1600b4255040c582140740035100c04801e00000890b071440c8160301a003118012101d0b03000d4104228090300c480034034900383d100e01c0402e112103029028010f10403100840c2070300e20300415080e0095114140c8070341070000140c4050142c051002141e00501032140248181c0b81001d0700e82002404e8074201581d003000040500040000b0036400509040740900c110075005080c0f80361000095640c00c004000030039080012000c03604645464055400501004005006052600c0848005500c8114054100c07981c0083d002c2111041802213640010100c440c41d10b440741040107000300e260300904068880200d0a03040b450419075440554 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 118257967 1250 118256717 118256729
    0x103080a0e0d3806010e03190804050a081b0910170a0c121707020f060d0902010e1509040b0604031202010b131404020103050411041404140a02090c030a02070c 70
    0x883d150320041c050104048082140e80a401e0541e0b000100034508280c850344a1005d1800d1101400024042400d04402c858421007a020a0100c1010081c03c01d014106903081a10600c4100d5070340c51000b540c4400d20000c0c2c50703100c01c5a440c07020700d600717044c408160300c100300f5202c4000803a030700c1c6038402a0110a13036102038182c010517600410000c4541003c0000c2040c00d00c1582034100c146ca800307200c46072400d103da080c0070000990000f19200c16103408064a002000d10340c5881079008094007030f0078031040481c0061502450b0f01e01d5443c090307450703061a142420419007032500b0b0710709020081c0403c0c0390003544200c05010000000726050741c8151040394590020a440a640007070103030034102c0daa5054100c50501c0555012044415402c42d8000c1e024a00440d05850b6401c1205942c403c0000c1c0700e400ca070800400010300280445581d0045e48284d10407442030b5040000a511413110501c0203622188100200c1e007551080005175404c40c0442900600e014900d03900c05140a000358403170 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 118259217 1250 118257967 118257983
    0xa05030d050d060608041205030405011407021f0c05120a09052d03070b0a3b1011030103030f020c0405040c05030f010905030306010f1407050a0c080309090103080a0e0d 74
    0xc4200c1c565401601c00501e00c508000d041420296a44031030014247c00d800100700f004400101801000d41200c05000100182d00c1190b050440000307403034501c500303a031001c100400c625030340301c076201c500c19240300841ca65506400c082d218441e0aa600300064440d940164860364164003044050019402c2032030541800204154010700840e500745090103105001c0d0428081c110104018410f01075101e29030f494001580c04046819009a10540c1e0420800c80b03011503502c4946080c0c0140da100b0030800c03030308a48244540c5090390094905c1c1441d400e403541000d1004100090240400700c0c1034019034016100440041c00102d030487d28101c900703403061156000200003509050120681c91140c1e14000c1c02000115103420741d40c0e200c0682801d04100b4801c42c0700482d00d11a060001c52079000741d084682d20022410603c3c1e4401480d4400d8a0152580c10000f5140d8000002c803071100c4030203071103c03c260b0b18644407060103410000080050140383d07480c8103241d580c0c525000070789600c1080c2c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 118260467 1250 118259217 118259227
    0x20a0b09090f0108030706052502070f05060403171c0203040809100c05071e03020307030501140c0715020304060b031501065003010e091c08150a05030d05 68
    0x1c008458002804034081c012080c0010300489034007104581ca0640c000c080482c080d224171041503521285040e00503d03501040700c61244c038950106480c07040340d03180e4104208140d29001084818401c84c40001e0403803140c1d140ca8400211070364094029294201d0380c0840341e500381e220040599004603000c644240e0001401c1c83c2038a07111400087d00d003900d00d40842005195620559200841c0c024907083c01c06a09501c201703000c9000303412003d0b541c040c0584000959a20300f850282014010590a420b20000028100d26802096500b1150001001010700f01c01228000080d407000e0030907280103480b1420302c140c4d601d0800c01c01820310b80c0755801c80002c0d890890020b0254846c1c1405143c201c04d00186640f02503083d030002091410524055034070030300507a54603180c200035021103801d001d90100c000154491403003400c0f4401c040a105440c84800039104d003c00350300300140c81002182c05d403004a00959601e6400c4010440d000e00302010710b5440d00002403918040c00012800200c00081c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 118261717 1250 118260467 118260469
    0x6090a110d09030206070e1e120f0c0306060303070201080103030e150f03040302060109150b0f160c2d2d0f061707091a070c03080d050f09070501030209030703020a0b09 74
    0xd003651240007850020840c4581343c0002c2c0500b010315208c0c0c685902e507441c1c404019075440070442072070080303030382228640075110b0704007602c0344c9401150ba440b0b40034450009106040202c00c641d8216416540e00690340c0c2036075419281c01c628000090b0b0000030361404d100b0300d0032403200103090407582c01184a4882c0342520b402031078108140c00c000c18490418400031800690800258242c03a034141c1600d8645e80d04008a0700c030760280c1d0000e1080c0380700b011480001e0001c00004c003015a03070110600441e24504d1100014105401ca030002814001d4100400404007080f041c1d801402c03a4101034201401d00f61039a40504c036280e0040b0300003400780c1c807080040b550440d000501d000e441a501d1902071420340000b41118003031b8810340390303011071202d28401000071810032a400790b907000d0706401d0155160700b0141c4040c0c00005890b05c0c0079140030049400045298544c906c9941002c00030310b100c90500004501a401c41100160944501800403006941d011070440242c1550000151108441b41c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 118262967 1250 118261717 118261723
    0x10b03130303090b0403173301120906050601020f0105040312051801090b010503010c020c0d0b10030602070b01052805010f050f03010905040c0506070804030b0408040b0c0a030f02120306090a110d090302 89
    0xa040f100480541740071080391654042e00151058202008c5141000180c0e40180c0d400408011400b0b4102d180006040802c2450b62119002c2d00b0280e003107542c800b028001447c200c0d903046c0e0b0301802240c1103035002c0c000103089801103680900f500382d0f0b1a06800a802485003980c400c00c9040351480082030050181d810240b10b803d54a0300544002d120550a180105882219203403002d040c1c00e403103000150001e4149405d0708000d5600840131036445142d801c08030340130b01c0c0c03c2c011544201500240c0303004c01407141c802c0d00e6040750b61601c100c4203a407501c1c00564005601d08101000e100701402301d0214169030002541c02030046000104803441c040c9031541101040b60460b0344204c0090003800081340340d0030107940907280e01c00308407907084e2228140160103010359030101281c081c002414080e06180450a40c013014860307201c00303226a0a5103401d03600d45860510182c4914020f200003a00341c64004c2115420071180c04001270741a8020004400702d62040d0a81401103807194110410182c1c10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 118264217 1250 118262967 118262971
    0xc040b010906081f03050d1106100503102a1d0a030803010603020a0302071502070c140d02060d021303030c0507060e01050412060e2e05010b03130303090b040317 71
    0x34070380901010704101c40a844841c01801a0b2000b40880007a40c182030306030b0b0b000402554100e8115200c1080f0b8000040031413813110002c0580707004000c003240512806042400940308003c01030481a144d208001c001401111171013140e048600841c50b811180072090110f1005407036450f12011180c441090110030544075000340100c20182d000c2010607402001d40b1b041d07030624580542e0b60491101c003100640124171015001c20200d010b00c051050590f4004c20445106a103040b940e5542c0d1584060b12500d402c0d14182c02c0044031003942e0052074014001c01e425410381c0380050038145400b180c1d01c151440c035001140804d041a62030024401d00700f02a50051010f881c14605200d2100c0000340680107500c6041c0414010605140c01c0000c650030100c18440200c0c1203a05180340c14241030281020340c14101a84c1d181f444007032102024500074581078581c400710143c5191255018480350301481c0ea03055042550380d003880000a01c103415424002e9020b6076a04950701180c1c0300d840009040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 118265467 1250 118264217 118264219
    0x9010b12011d0a26070818010e0103060503060a0f1401090b031c021c02100f020a11030403080f0c030c1209010318050601050603070e041107031b0b24040e0c040b 71
    0x4076075004006410165040d400f04c0064241d080103070581c082c1c1664034000c08600500950010508060284008100c01040c0000b40e82d010300546081e00107404030348890003043d4240c0c02402c000340d030152003038205c0e03024520180710011f00383e034142d01039588440c0c00780c0107550f410391902990703c280d282c1006031400e90020f07984010149d808400d4007a544104880c2c00107042d4040c484010385c018001e00c052907076490a2101030002d0030707030300710441c000390701100840000c126040321400460308000306890035280e20907100c0d8500a0310100d204031079000308000106a01c401c21505d00c503a2414810001002c5440c500700341c031a15001d0000d0207072555800482001d0005808100c041440001e1090440710144c4400e070340c03a1500c4104448040303442802c0c0ba040b504080000d100c0c14414001000510300035a00c1032403403030202c0d80240360803507a503001400814440d070100f0706000310340d0392075251000c180c28a00e50f110010301c041810758228050b41250764000000c0841d090505000e00035110b94 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 118266717 1250 118265467 118265473
    0x70801020d050f3309040f0210171512120301030c0902030402030309010c050f0a030507060c0e01050a030f090f06021905030615090a0302030601080607090909110909010b12011d 78
    0x24045070304000c440c80b003402e5121020361405091011441c00c84140c60b422401170b04148682c03034107080c4440070050002c002c900402035040082c460501c5a070b02c0c0c3e1f251112800100c9000e485000503c0101c1e00600303042640701c03490704540403500c481040305007802c0b8404101192650300d14100b0b00040505030b4001e0300e54600400030800142d030048211242c454003402c11310800300c19030070054a41020528861350a20605224000341604600a01106481400280503d500c4e51100316000000380c1e480700d000c02c1051090018003400394000c0e805180d0000301c0001e10008946505101c1134075070740141d03030059000542560003040d515000d0511051800c2c40c0d450750515a001c030321501d0340c200c0854410800421424420380c1d070101180000c680050445409584405680e52500c50503a03864001c10020f0000203495030690051040d51500104903e2000c40c070304051145040004210b807000d550782c0d1601c0b0300d00ea503901c14040c0c09920700707000001d420b00e00d104941040c40000103404026038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 118267967 1250 118266717 118266721
    0x80708030702010e09150604060c110607030e011413060908011a010546020706030b0108040206030a14040302071d100306090201051204030203030f0c1606020f0705070801020d050f 79
    0x40d03002130551804e104251004405603444020150f4607410300c0d6203180e800b100004001600a03441860b1032680341c0a120f0300c840301c2d040780c82006014802d1716002004102e41c4401c0b407440750300031004e403150110b04007841c500d071089601c20707407228800b950818000f144a0480030301500b0424851003804444110400310500c5440c1c00184c42800b4046140c800c062402c1c40c1e141030a55070074101a6215801450620403004d218940c4e41e411813810109001442003490004280303100b40550000090107846045241e103c42c0c00b0b1241a510040c0a442140e4079002c0d034105440400041030311a901907400740c0b042c2ca082c010300c40b41445945c80030100c00814002401011045800084101c990100300060301c40c40501c0144d9450040f0a00008a0742d0030400300310602d80c001c0000c611403107000b4244140d43c4c3d1820100007440c020000c00034240351800420100050140d401040f80d000301c10390f07060070034000c0d96601d071070202d003500050380e280d401148041c540c3d03a031030081942004c0480501c1a480c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 118269217 1250 118267967 118267969
    0x602010624080f0a060b030406020d270b13050d2102040f1701060b070605010504061a1c1e060e010501020a02030307080306131a03060f100611030910020601080708030702 75
    0x2e00140071001404203401c041101d80c40c007030f801039000740f03100c0d10300c962a49054205080217401c0f000090156504010840c814288400b0f074103218a000703068400140207003920307150131000c0014417250b00685d1088908001c91400c102102e1070700d02994036150803154501001c2d090749151128800011b00500c4148506052011400151001103042044981d45545130a024041c2680400c40d00e410000e111804d10441d900010305840050341d040c071030325641e040c109602450901e0782150f001010700c0030154110001d40c80c4c81d486642d02c00040f034000490200111848001014908480d076a803404007d83c1d0716580c03011b401080c00b40050800340c10a50042070b03c031b00c0b41080c01090f1440c00400030b03e10755203603402489800b01841c41000000008203104172003082a0719541d10038410382002401c07603070306484040d10a10022074551401031906105481ca40420304182e110ba00003404a003c00f40c80c0c02901e202440050f900030702e899490124990b0a280c8c66402c900d0700e6030810007030342003d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 118270467 1250 118269217 118269227
    0x4050c010e0307060e0d06020a080108010e070e010b0903010f050106030b090610090509041703010611190c0b0711030102031e0711030f0a031d010b040c090f03020621010602010624 79
    0x100d40031801e0100d03800000300300251b251a511000100318500c04103900142075801101c00303041e250010000c00000041c240351960341c3e002c900c45c5403004040080148010080d02020f00780f0341801900103d850b030b512215002c19a40309030002400641c0d102181201440c021451303a400520a4501e83c2c035440521400800604060050602030010100464200702c1144180e04640164001a0fa01c950312544000c080c1501c6030501c101030300c42c110341610010214444550415401240318520a00d001c1c602503107908a080d0a071420012000503221507142800118030459001100c000300b210042a40f086a18010b02a03c0030080042a00440003d0000480e910b281c1d000000310f496001c403800c11405040204100003681c54555801f0704034010540004884240c215401d111030b1042581c11181c00d0014492000141c000450800250821400502986a46419040b5000c040761000e042c0b0f184283d201d440145e42d50042000300c52820f6241550000c502070001c00e10400081c40204 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 118271717 1250 118270467 118270469
    0x30f060329010e04120c0501050106051321021e0d08040305070609080d1b0510050106020c1c060905030412050a02031207230f07031a010f030510050601051204060504050c010e0307 79
    0x65680804110070440340540461a1b2095001000380440e40e11408000e0060708034549152100158900228211407032100110a00650000004080205402304480018641c8129118881c2200a0f04164075030300755410096004568142e9110720b5031500c83d240041c1d9511200810902074028401030b480407403d644107140310b00d046081801c0e4169080d400500f06070000700b2511940d4486103d81506401c036030304036030940d001d680038150104280070200f00c40351036940724220016010f90020f203150740810780d1640680101c82c24641c5a00107686240350459007901c0d9580080030240031450104184507114416030946030409800340c1d03410498010315490b4060101d0000c00c2c4000c038520400840c6042c1d601c500851344059600d0401e510450b042c0f41e014614001800c0000c03692014040c00c14049a5119004041c01c00c3c46c808500000c11000d801070741040001c00c0108450041c542c820360045001d4036000030141003d04c2d2031441c0000000b15907050085c100f120f880f03980e40202d9088 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 118272967 1250 118271717 118271723
    0x1215020301150c1b090504060506090606161106030c0d0c0201021e090d0611131403062202060403120813081b0a02030303070801030b07030203100b0a030f060329010e04 74
    0x11000600915108180404c901c4010700030500040c40083d10844030342105018900403c401c000c15155202400184130003200d80c02c1c1c005004102450301442c411a603c110240180800b090744481d140000740303607a00c150307405100d440020038007d0294081348207451700114203000031032034804030180001210b401000e181911f5540407079810595191b50401038001a030007078003002169000400d02c0300d42c4d08121416904242094070105a8414580d004030640b4030090007040035640344400c03064007060440c0c0020304103503002003180040e191800500701a510920b05444010b144030401084d21100600d504d07048605000c1401c0843c0400d011288000742d04420606807294100055240a81202d07000b50144000800c114040350700055241c141c0e40700d11100d181710746403258200c041e4002990301c071301c1010341c8500c00c200b0030790058010a4034510b14103011070385c009444102800c80e0300941c000d86805150562040c01840b80c41e03910312100481503000281541014002c48203c03500030300003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 118274217 1250 118272967 118272977
    0xe01080c190e131a010f0f2306030601230d0509012901090f03050d110d08060405060f03060406050601020f030a0504050603070512040503120708070e010c0206040f121502030115 78
    0x2480501214130700740c1d0840000c0318290302c00795035604807203011034074a4130031150125840140030840060104514603540145664510308850520822580b5840a0101030611581d0303c04480340c1c440309c07040300c00007440030003005440380060500c039003c0d80d03001083c8004c141d00d840308490f41000c180300710040380d032112a55100c400c4800001650b01d40d031680c00500311203111850010030008001051407a13190180e07184030000110000c1655544100601d4001040e01d1900040276403c00780d00040d80940c004010012030303144d86002c07a05015003950140ea078107885004000712541c0412602c85806442801545400c030321070b030014010700860003280e02c1104000081141e80380325200382c50200c040c046c0d4544582c24a4a8015625401060400b99400c4007070b00140d5040e0054103180d01c9031150307441d001c40513001e031001100c1e103031030300c03042264048420b00000c24403010128115018101c1510707030581d004420b081c800e06683d8004e01418960340104010b2113044e5100d0340341e1106c002d0354144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 118275467 1250 118274217 118274251
    0xd0c121101020408070f08151003060b13090302030309010b0f0a0902090d06020a08072705040207030c12090503120726040b0a0c02091005090714040e01080c190e 71
    0x1800d4064800c640c49130200b0310490b0004600d01da22010341404840102d812100d060700c00108440907901c0c22a01098030790842401000801e94036040382c92241002850013070103062100c440300444106407820341c0140d0021042045d881000d20a061a408045400d07008040408000400f101060300903840600c1d004142924180c450341c0e0000703540c9030312150540d15105040001409060101c0d5450005509090003005200e00075801c1a0009403901188402c607040005000180d0700c2140d0460800204000b005c010690500c0e0200d00750319103550b41c4000b00d00c1c140406242c0040012840342c0b01e081000b20704d00054881550a5405096014000c140c80003a81e0211f164003e41d80b190200500c00540c4158155002c8026888244202e402d10035548605801500c040d1300387c050660030402810100b2400343c012001d140c00300c824542c56900e050380764040c005201b40280d02000c010ba00c0201c2094841c500303070b03040d080c1203a90840a183c0503072802080a01843c00602089035400303603846 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 118276717 1250 118275467 118275497
    0xb031303090e04080a09060c1509030c0204060803180913060509071a0a08091501180b030a06020c010c02030307140a0c140d12090b0c03060f0d03050a020d0c12 70
    0x4108402888109078455280c0b40504180304540c5c8000807440c00100300d032401080e060300038160144016003010406180c0400e490012008000a2105070240401501007400590707030317070050002074040f400c0174548030303040c10150140c500b11521600748200c0d83d000421560341c0ca0034a40c401e107150411404242c1c5d884240f00641840b065800c021034089480d071078010382410b00001080291032031b60b0350225550304c58042548841c40c12145010351881080101300800300640c5200010040c40c1002588030750400001b443c1500e00001280c030240c000c200403403070304400c0c45551815281c3d40081c5146140c44d48000f868460180306c40380e61a40081441665240f082202c0c3c0c1249030301c040711101808400380e500343d5801d0607002090024090408203024001980030f03480352607070f201481183c02e0b1141c800800050304020000d076040600003080d90120b50b90300000d0a0018001d444196589140c2c0d00b0003801c5c940810580410301c07088050314000541e00302804000c842941c5490340e07010410721 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 118277967 1250 118276717 118276727
    0x301051302012f0f0a0506010f031a070306050d060501080c060c060a021602040609051b041406031f0605071406060f04151e060207090b0a15020115031a100b031303 72
    0x30180c4641072003864014501000001171680c10103004074122170890b81e842c14030300040c007410301005141d61044440c040748004240001a0400500d003001f15100d0b4542010850b4000c1c0350100f81c400301e40310710040162140038401c038520840c05840491425941e05100ba6640c8009001c40080c03a50008810840302550814450801c0c0e0080c0140b0034103681343c54a0001d001c1c107aa40110035070082e0527550050f441c1c881201d00715180400c032481ca1102810030884180c2004104101d01014010141d0901c0c141c0ca602ca03000c1c10940d15526120842818511200300d8851507015886d03002c40d0512400780e46009020840140844000c40c4101030504100f000c030700380354402c1c0811006240401440941c10420300e06882c51344c0d0031506441e581c0d40848080e9044881403030313008001c1c900184a0349030704900c201860906400080f4481024140c83c00007080b0941c016038003a40d4444e80321031602c1c80180741642100c407401104061504151150700e8601c000b5122a0042403240e0505040500070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 118279217 1250 118277967 118278047
    0x8030c15130b040c03020915010e0f240301081e0a020904030309020a03080406030b09010f0b070f21030c0c0309060302180d301407080f030411030105130201 69
    0x100c0416402800c140c50807103038001d8580400c9109444050000701c0305409240d4440c4e41800503525001e0490400b8280011a02d04100b2f10340c100000d050b110981c040d003201c20300c2d00c903451110302580e250f24109019041c401103122645001240303140c00d41042d4000644030004640459072a0341c207490710f00c0c043c1d0041210490080d0440010280001070080e40c101500c119101e607101803044198600030030002e058240240040c80c60803890600490154a001e0543c0790310030002c8000020007621090b5222071038980d41d0300e800026500f0300070b2103075140c0551000400c5904044c807896031a542d000c1d02004842c010341080642c0400c01040e03100412028802406000c2c081d05c410801604108804010358409844110303a00c04003000c4009900c40070300356214190b510002e40d008803c0d8021290b40c0204001d82d0b60341e005001b6541150b15000086020b00e00c64026a20404c800a00340340c25078000420400d1607000c02e40039030700503076080707010550707120001c03408211540009041d4031024140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 118280467 1250 118279217 118279223
    0x10e07120207140705040f090f08030c090603090706120203070503070c08041505070b0105030a0c06030b010c060c02060a0c05040b04091104030f03050705070b03060d060b030a1407030c08030c1513 86
    0x843d5580020780a000c214802912003e0314248100d9803102504010740e1445800181000c4403000d403180450005c0c000340da040280364080c14a400264000134803107400030340b08445240c00c03124003008029000b10300018100c910030b00560451408100160241c000102420140b000d186080d10030012500202c03400f0309000000e020794074a005200800c150040036040392460320003400881c2529002275590001a40034543d82e0929040007030807400790150980c0d583c140a20150110001000f034050703a4180ac0e9664000d02892801e04402e50965070006540c0c818040d00b04000c0c80814580000c1f242901c0a240001c19680e0201c9404041d81c42541d10103481e184080c049201010741c440c0003402c00501500403500b02130b8841d00c50308034030311040e524203034800020404080090340940114681c0403000301550300d8110306072122003041c4032407407441c2001d4009020510401c00d03107403505005000040000d6040c80904611255540b00302c0c0030030141b050303c15001a0b0f413108095003101c02541c1c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 118281717 1250 118280467 118280483
    0x8150a090609050109060e190906050705030708070306031205091207060203070c0e060a03170c0a060f060909350c0309010e030105040c180212130c0e010e07120207 72
    0x140d91189034008100e140a0101c07401e040c000009660b8000f400b1701010750392010b4500e10b25403200311045a0aa241c4590000280d86074407515000c10700c0e42c8220740c803c00d15601c55a80c0c80c90054002011000000d10310b9003410310b81031007800460b5103904020060916810035603031300c200f403800040910400d80d05c100f5003403040b00310129810382e01202405549100304a0440c81d03030b80b0707880d003010302900440300150088103500003000030560303541101c60344000711040f0514040c2130312000c9040224a00c1e0070303240561608601000c0c91700703a00c2100d0041c00410810800f03003807a0707680c4018086a0b0800d030b10800e100620790440740d02c214802003009100710184030360768032443c1540707a40b01d400102e00e00c0e000c41d03070044d05c00714982018012207110b42e9111824440050401e40c00050820050184914055003481907000c41060544180c4c0030310012210090a100c181ca0a40c2250745140c012064142c482070041080d6202c110104e500000a402c2000c0404410a8084002d018101d00038107200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 118282967 1250 118281717 118281719
    0x1090212070e0d050712050607080417090609040c030501050109150c0803150315010303030507090608071d030102070b0a0b0f010804140c0d08071101050307051e0d050906072a0308150a 81
    0x603a124103a40781a511a03001d448503540c416006a079038ac00210750140035460f0000c004981003444000400a13080f006021505050302c5c0c2d00824110b034810f200c1e10303000c84d588000501413036802c1040e0700e0007004003203428260354441c00001410b24480020041c02620003001140700020003010640c40084043d00b01d8440c00002a0030594801080c482a00403d181001066207580f05490b14029a031203070f02c4404131612210700845845c0000045c60824119107007261496940070b00050088030b02600011045050607034141d4221104110f04a1103690300c501c80c40e03110390b0000350311503000d0b800c503440090468015202a0400401c04e035244d40c410f007042c0240080006000240c00014010b1488554541041c0c0065030a40700c00e4a41d0307400b01d1814446d980d1004144400d45940c502440c1102d07082040f20060308081d1103040d50204440e4220408006446030300044043c8090202000e484c0781c560b0f0f0340700c2b0050300418142c3c00780070441c1c02e030700180441a44421400c400b5030701a11182c070312 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 118284217 1250 118282967 118282979
    0xb06030c0301060e01030501030b06010f02070306021b010b040e0a031d03010906050a0b01030e0606060c0c0303160b09030909160e13060503011410061110090501020a0801090212070e0d0507 83
    0x540d01c01d01403400484c2100780000c034079511070702c03c02e41a82c0e4480303d1240c6544030b44006460304500c45000c40c08502c140b00000c000a1524000351001440c0111180f642d0803001c45400d0940b04412a064041c3e8680f481369000c2ca80001384403a04140c040c104542002602c60401143c3c0b14210b5407150550b080100f44c0f0104505c1d684158800c1a44c81c0003009070880910045041e50810100304903240d1015000c01c18619151001307204103281c010888100ca201d02c00801d05603000301c81c0c101101c038181c420150030b21080640300c551000010340034500e4040290005098000003608580c0140c1d1141c1c8400005030041003507242090004041c452008003018090780505541d00605000c0d5092480e02680040d180c004540607001d20b0890800042c10324904030f40014905040312030702d1080140f1803c8552080c814072501d14000c030b0005d6616031140102a00090060340a070612900c10000442c0c050141d003032041d040321603031402d01d502c4035107000003490b684c00511014107203019410000441c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 118285467 1250 118284217 118284241
    0x2030408070e06091509011403030909130b1b0a210f0626060411030c0a030606030615030f0b09030f0c07051507020a150c0b18010501140102100f0b0603 67
    0x100341c00132a105142c50b81c0f2041407000004840d401e00c0d400c1000c80f00140b004a09406006901d14006811203003030140500c001030b06840243c48400100c600d404006080c00016481903500001c003408940042100d4100000d00b880b0f0030345940304001d004816101e032000c514141f90b0780070000e540180034482c2e465030b0b0400188142d1095038040c1c201ca68540264148410340e07114a400c10f0005043c2c995242c2e150303030319414680000c40e60b0501908a40030556036608001101441c044c000004900d0309500d0f03c28101c50030301207441008415441d0400001d42e0321004d80c0a89940a1084103203903c54159043c51800740e00003205084c0d0000c00c2c1d03410710700c00000d400021954101c891141d201080104110a8840e0940c06908621440d1042c0000304250b00c000c1d0000700c00d8503110460790800d03160025a182c05454495203180d50940c4401502401d015003805402641110380069a40380300107581c44c5076081c100c0305c0300c548440700074080398072a5010a9034000058450780e5286031101d18105 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 118286717 1250 118285467 118285471
    0xb0d0b0109050108061c080733050c03130c0b041d060402090619050d140403020c030c030607120209040e0102030103020a0b07110d0809030106140f04020c0303010902090102030408070e 81
    0x100091803680000ba8a40c4103c030b800d80504009042004002c02c40c2c2807080002c0c0140005480c0c0703020400c146030009001c50303200182406200b42a4900c1c902d494600104040b049001d07441403070405080c003480340c071600100d0b9040b201c840800354948919103000d41c1c031070000da84062203101c0c0200d80020301c00c520100d0b106100e21030b18441c0e0503558550040200700d01904a40c0e540220f01070128002e458240f210495480e0040c0c00c3c52420101c0c01c1c100d0000740c8000140c00e418041c1e1000500c030030540c0410450340070000813406400a182c0c004003080d55000020b00710010071200c40d5180e03101c6261681103c61104000c0c0040c4058580c03652901e010754001c1c44204c2c09a101c1c0c03580011810541015604851b51090364071006074034035404c02207081180360f01620f0141042054500d1903609110f0700000304041c82003142a20dc0b07510420210602e0302d521107010780c1c01081541c010b5003000c82200d0548502c6540143c0790500200102c2c83d40c040c94000b14864400c040001c01c0c81c0c960b80070024 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 118287967 1250 118286717 118286719
    0x3110904031e0816020609030403060b010c0501050a0902120a12030f0b0d1a0c07080904020a120f0603031e020a060e1c02010e01051506030403080a020f0f0711091e0403020102040b0d0b 81
    0x3003900e250b6400c01c031781d01d480441f1440905d0304140030920018010ba0083d41104034149031081d94000300e5243c5500b140c100760b42440700540d03515050011400c200c00000b5280260f600a013401a4080c4c58808201c60200d0300001019650120440e4805503a4031901402c9000752100301c80304031a203450601700d8101044c1030740e4544e02c100026aa150340d00225966244c0c40503a007400c0603844010b10000c0c0d0000c0920005020a248042da80d00c0c08521a182c40c0901905000c1002c42c80c1d814094055540940010309500704080038018a030380002d1710700c01e520b510680c00605a004036503c0350070690a03101c514007184000c0d44140c041a415005060800310642c0208419280d42d0070300e02d2040c0401841c66001442480024082401450420750210308981c0c05441d140c82060400100e52040605c41e074114408940d007001d00180d403580117039070b00c01640c0f10f1050f8184102c5e421030301d150300c04200c104408800e00041c1058400c3d0103460050800c0096203841e240b040c64210050003410401c9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 118289217 1250 118287967 118287991
    0x2040902030f09240405150c0714070b041211150a030614011707020106080d0323010b12070e06040e0114010f05180105090a08030405090c0403110904031e08 69
    0x200c1c004080c04940110b044c0c0d01d001044140c000080d2954001d94401882a0f4141c0070301c0c0700302070616040020a9100c5c403606140750395030340c84510349481d1085000d0b205081c1395115060511178012a801200d041e5801c4a0306002d1515103894212400003145010b160051800404003650080010261038030941035101440140d86580c41c83e901340311141d0080d0700040400d00403400b807028a442c01c03908800244008282640ca0355a82450105500512000207a803400302c0140011801c00c4013a0054203584410b900d545080203140300e50155001c80b008007100a408600001c8c00340304c5c01e181f0000701918141e20342e0381d03400f80030b004441e09216500c1c00855000c0d40340c0c00d662013001101c000c0300541d15403e080c00240d05581c2070600340000341c030781800b20402550200da035400759460f00a00c142c0000b1596103041c14240860040b010700100c00d15801408240000f030002282585040802d54401c801d0355190308048804041080000c4208043d051195100a9000038003d101e84d085800d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 118290467 1250 118289217 118289221
    0x120106031b03201309050c030d1d2d0612040b040605010b0309060a0c140301031b060203040303140a170906010504050c090102061504020c06010b0904060905010324020c0102040902030f 81
    0x10902120726040d0b0340ca6403003001840a0100710b03543d03500c0012406e00803004c130340c42200201c0c08280307000c00d2582e0100c0410078002c0049240b04002c0380424a03508152000440c2180391070182d400c0142182041044080101403255152a00c0b000c0d00c002111a065880e240c2c107041c1440320180a05031002da401508005c0089089048281260b0082c81404000e011540d61030190314010a0340d030500608210003050104c1d0000d40c03242c00307140654012a05210700080240c051058a81d4643c011400e5400030321042004c203410501c203c05002048400b00c1d51101c0c00501103a006a41c0303c90500800301c402d0510850240001c0c03828107031503054030100036075141e80c07030609501d0160340311082c010b034050360001d22840f410745e201c007404180207000541846084141682059030076001034114178000309010840745440d01500c2c2c001c26130190100865419900c500c140c0001c0000c9224100e00860010036030300080354100c50000d80040000c546498480030508080e40c001c0d00c05032181e0a540300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 118291717 1250 118290467 118290503
    0xa0b01080f0105010c02090402040618150806010b03010b030703150b0c0c010806060d0e0a0f0302060708070914010807181401080606030705091207080706050408060703050603060105120106031b03 86
    0x89840c2c103a074416100c4034810700181d42040380b5005c008104070b80264a0740400135460413500c80701c1010317540724000030030107882d58550303144c104010303910618460340101e0040001c1c0012404a90655640e03220090703032943c8950003a00a821080c0b0305090482d0481c40c00101c464503040900060417a103016140061613030300c0115022074040c1e901d135500c164108940c614129183d44a103a106aa40080d038400c841d8030f80352203180b00308140094000d40c0050701000070780c039400b038006a40030034581003005100b0f04104401d113040c100240d415040c030101c41c000c031326658014441c0c00a1382904001342c440c240d4403000d10a00e205115801035012030401070102c0d01c641b40c00400d0703034446e90007541d034181440558000c0110100c080b0810010a000d00b02c0081099a0180a407501a00030f503280c0d80c0c0e640d4901070000b0301c3c0c584024100410186000284a5140d50204590341194812149401001c4240115900401684e0300040480455010100b09c4140801d0b9160403240141d8080324000c1c0160707 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 118292967 1250 118291717 118291741
    0x308090a080a0f110622170c0a140f0a0b0c120106020705030111040302030606012303070201020301050108090d020c10031d0615010f050405011d03011409010606030b06040b03090309090a0b0108 85
    0x16502600022110041401d6406d40b52121403006001d000d40711a003044081c01100e065101c84854002070300300528039014032000410316415040514000d040b84c6041c00758860700ca6400145c01400e00c4c1c0e40300c0c04640d0b9050034009407054004407400f03c00f01d6507941e00303020303507030304000d10440d0300030750800088074035600b4601c0c00c1d101143e8001e405003009660390310044035659440581c01045184450070584100c0c100c1014521400e619000145d80c1d5041000160248900400e5418541e1009100364090796001c00d026651400075a11501c113000b0310001a000fa00c11800381ca44100003d15445101c8100041c01901a504031010b075141c040c881001110b84200100e00350700801c20803c4100140d501c5005408441c0010b8800000074503140b0000900351842c0b40902c615000516050041c554401e120780401800f56060400601440c00b010892a01640c41040840b82c0044000b403001c14007481140e00c890001042d40c50350345000181440100b003c600000e00141aa100040c10b2162403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 118294217 1250 118292967 118292971
    0x141006050d08041a0c030c030408120c0d08180102130f0905010b030c031012060b010305010902090319080705010501060c05160f1401090b1305030613030c0308090a080a0f1106 77
    0x20240b00c2c0d26060410000d080b015140000502c0c004400b0403581c180c610003480500815203000c00a16511890000070600c1d103016820f036802c90340c00c2001048a6904002004172041c0f546050410059030f40d284140e081d08200422400c05500000e002161800e18003075070401c1d20000744640c03196076201d02804080f102d00f40a8261190010404181c011000b54041e55204000c4007080c40140d8864442100780126031400f02d0b869503c032004e8180c1c0d980c043c0030f10350141020070801c42c206240c00e80002c1d940e000701d070b0b04a100903900028220030700407941c003120070803508030009014950f074841d4020540001c490054440340660b00b00d504440c0f201d08000001c0f5280c2c80d00d504102824045050f0700885444a05030601010100000b01c4112040c040c1030800c600490000c92689400145800c024000300180320011245400d0000650884100012550146881007083e900c0803110340c50103010042c007800031107000c611803004036801100136400c204165225032900c45522030340c40d030341c1d241 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 118295467 1250 118294217 118294223
    0x2250c03020120030a050c1b0609010c0c03050f0309100906021527030414010302030108060a020304050304080304260604030f0f03240302120d080109090f141006050d 73
    0x18090040015610598441c548460038540145440038600021441c40d40582c4448010a03000700e29025001c0040c003451014000a130028068008443c000980c02d228808046050290160001d010700003041c004102440d8403608440d44040c0303d0b04000c0e80c940014132254420892041d20311070a51151003400300f2584950020845601003142c440314483c0000c142e4041c60000031540c0045500c1240d462010701451800745039643d081101d4242003c0c00030204030705160042004201002c1c0008200b640030041400058076521141380c4203085105507404041d203444042000301d9154401c801c0151842084218846035042d005c109907112642210050081805510700b140000e02030303151190b00f001d10340740c0010342c0c8082000800e05d078000590f610703010340c4280744140110306094200549603129400100f55100d422000100040414000e680301d1503184c4065008120301c205240041079803008903c0e50104801d1101c941c0c81e20040100e0281509090000130542005142d84c4400c0350 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 118296717 1250 118295467 118295483
    0x60e0c0711010f0c050303161b1106090102012301050901120317070e150408010f06080d1b0b190b01050c030f090a0b0408060403120605010f0305150a08010225 70
    0x2900070054800b086142c21040900080e05110400204180000d51003448610640c420541d595000141136120900c1c288414400fa0740c000307804210880c0d0300c80d0350440c0c112941a520080b090040380074001d0700350074241c4100040701e19010b198450f10424140c0b0402e0700d11545036a130702c0d03008413565400c3d401d000c0c010524014040b40c0ca40102c114940c0d2004050418008050b1407a020860000182900c490740e03040c086420302041d40c0c28080d0703100c00d403609801401440e040c89005d035100c84400404c1800d101030203105001c10310043d04004411a0030100445141c40c16007850041850810a000030891074070301c0c3c4009560180096034888010100110304190702e54050712820703800704206c96449142c50600041d80c40c00d01e0001e10140a910000e8080d074105841c01070011107007042d0541c0c0c440e080c0001846540d90088000303c03154020f04d0085980d85941c1442c80740c0e00009a9220b4000e03d42000c0401c603c81c05400600040884240224010382c400b50302800350941e9990003041c6607 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 118297967 1250 118296717 118296743
    0x100b06070c030221030f120a050708190915050603010b0a0e06120106090603050a12020705100c030509030a05010608190b0114030708030a1701081606110c040e01060e0c07 75
    0x2044c0014a086095107001202d1003410103064800e2840e009901c075480c0d502c0002440f0035491342c0c4030300c0b0a600100744400c10b02c482d091500c0040c010400007070500c5036001032119540030303916031504110b02c0b0315044903104100c405c2076102c4801803c81103e480740a58204000350809040101e08441121860007242135540c90340400c0154088c5914003419a9648400e0040783c0303c40c0512814008502c2080244040951032802407030303141307121900d8420364000e21410025a01c900c4904041048180760588000115203000e4605009030345110780c052086e10207400030040154000070a880c3c403081180c80d080c148110b5008010b80100d8010b0214141c4401040b680002c43c80035441450000c00307607981e442c1c80701d211500e10341101c410301d400200d800d0815041d000548801380d01401051018008600c9003a10001803510103114a072704014403901503078a002018051003000c458000d000b800a030302c03d01407a5002e0a45402496140e00003400800d1075200c64004840c000c5500c0180c0c54004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 118299217 1250 118297967 118297969
    0x62a09050603060f04050f012c04030e0d12020618031e070f08070b190501081f06050a0321020d1e0203040905011d0105030d050d0b130509100b06070c0302 68
    0x29040542030641100d084d14004146a0f01c40c051a48100703072000a0b082e5642c984000301c1da10301500302c070400d020103254010003102059894a5a407044d09420f00c05150b4407214040741d0429000303240503140b00240090b000f4199400314a1900515001c1c1040c1240f43d4136111640c0c89110b07023440d00094580105040c4010440350000d021520b0040c118110314054548801016610040b030803112100c0c4041000142914803080704a44102e40d43e0810040d810f0100c0d01d40d4501c0b0030303400d44000c80d509038444500c0c0566034001502828000d0449104030344e59180690440c4010407080810513140e40499009610004258041040035580c5050b958503510705951003030003028240086000c104004504402d250003000d0003880a041400b4004842d00c15095070041c040e0021403080e0000100700c06103d52160669a907201c802c3c00006070781c00110000f0f2400200e000000d04e070750f401d20042040c2403c005c40c40c0050402034580502c007203000d850810280c0e00c40c0d0350009201c03050846083c405 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 118300467 1250 118299217 118299229
    0x5031509010f020406120c090e070e0f0a0b090405010e0408090d03050d020f04090c210b01090315090210080403020304030303052d01080c1206010311031009062a0905 73
    0x111003140000740d440c80382e0002c1001e0340d216800a101003045000c0141000520b40b00c2c050031244180f81140c901030404c00180c080c0880507108004004140c5540b01030366403030034105001c0b00304c000c014902065403541440310300e070481c8414030b00c5645071200000e40c5002050b00603229660003800b0b14a0031309408100900b2800358042034080010610410b01075100910080c061703144201440d40d140c030701c1c00352840c0c00e89010541d40010400b010700c0c1c044c48080840e90713200c2e0241c1d50680204041c008600100d0741e0800650015151075001d20100c0005003995026290250003a02c0c40307100c1140d842c0003690510010340300200145e204000030004680b1a9002641000c804105d1030800007016070041c40f82855107088641c64841c0c3c0004010001007040000e04595056403002c1010a0b5000313825182e110511025000c0104400f4002290354240030b942003105205000300401501810001c000700b40c20303110848400303507005200001c0e0040b6070903003039041310640c0c480304c0b59403c103020302c4a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 118301717 1250 118300467 118300471
    0x6060d0e03070609051609020a02060a0c020307022808030f030403120e03030f070801140a0504020d0b060408030403050d03020c2a030304090b040501050103020a08010915150302070501050907050315 87
    0x24007404140301500005016004008245029900900001d54062009042c5507810742c8900006481003005222054010403941d501148107032000642d10b04012090b402c51040c208002d5126028100b00c0050030181010b076151120070303304848030f054132078441d40c1da01c1c0f289140c0d5a10110090002400080c46031550b060b0f0101181800f1801c49403040740070f0f1031034009441c2071381403410201c01c000c14680d00030401401000303255400c042244040740890004152809420f00032500000d20750b2070100300f508440c44860f0301514042c0c3daa552411540d407282c00c42c0c001250680034410490725118407034020ba40b00c24081402500380000c002c08020903411000303a0781c127042600c40354190780950b01400607100804103081c01117090250881080110b41c416040241032501c1800800c00701c1c0c0d0b1011509045d142400c0000444210b0341600c080043e01560007001740384ca081c2d4140004c3c0d03034150087c080c41449100240207940f10404055211a50390242c0c64040c3c1c01400d000250030b01e201007280e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 118302967 1250 118301717 118301741
    0x1517100b0a0308031302030c010e0f0405150307230117010b0c0a050105160206090d090b0318120c010b090603030d0c0302090910030309060305040b0106140d0912030e0606060d 77
    0x1c0e960b203956a00654204076540340520111040b890150704044c45a0f4104903001d10309031850a40600000e40c080e105119268015039a80001640341c1c2c403c2031000038404002411105c1203613581c50223820a0041c0c84a025a08601307a000030320035402074025407590101556500c041e40e00300f2007560a1a08000818001c81c030800e015900880c000b0321503140545000d031411801c0c01000200617150990203054000c6c81d512164400000980c001c403140c042d14041d000d555900c1e11001c00c45012980c1d00d001812460040417450290103118030020108c4654030b0000b4081d10404400b00f244101c1c0c201c03662501900204129007040485074442001e82c1542c1c280141030801440110302448021035540110401191042c0185a0000d41c0c076402000c41d0b1406001610f81992410b03c03045041c4510f10501641c203207040d0240007003000b640c0040008100c100100c1c213007420803070030340c880948018001c02c0c0342000c0c0e00000440410010b2181e0405400c0520300440c1d005c00c01d0007059248514 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 118304217 1250 118302967 118302979
    0x12070201030b060909070302030a0c0801210c0b0d02070b0906040309030b070203130e090606060a09030204090206041205060a0b0d050304030b06010504120302010504021e030613170a031517100b 85
    0x121310f5544144590064807036030b030300503102c0c641a007804046488200780344081c04842401000340c8600046904100300010700b0b099619241d40c640010a0070283c1c00c60400b002001c1070340390442c000703580605800c90041620740425210088a25107581041d2405000100303840c000748041078006600b99006521841140c0c60025121007040e0317000380d150003250040100710180b00f1000c0c810031070760703400c824100c0c1c1030303840c12030503503005800000039101c000d00480d00c40c04000d05543d181400e490013070410f41243d0600d4103041ca056a140c0c14100c0e4085005031074000d9080c00341c03c000044000c1309502070021490f05086880d840c0388020014601070406c042048040f810704914846040ca440c8a83c0002c6964186841000800d01e100d4484001e80f00c00140c0e8819603941c0020842c5d0411589c0320701c91000c1031907041c811604141078012444807040082c00015181d807580c00400701c00700002000907140e484030700031001d50010030860700c81a802400070001149096000024140005105c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 118305467 1250 118304217 118304227
    0xa030504111e0a08060601050d0b010201020f070f0c06020708100f0603050708070303030f0b061801021c0f11010212240306010906030b0f010b0423031902010f0212070201030b06 78
    0x1e0b0001d450012580d01c0c0c446084000d0140d0f00702646000d01030028803000e8480d91030f114000800c2d0380a411a141b041e075440f2209400164004e5044500548222200743d60b00c2d80c860a0000580302820000c079080030305c504e80001e0092001c06c1c1001030b2200c039070160800c4621040c40b1801f918122007000c08590769003100000040c000c20400006014490151043ca491410040c0c100d450324103203a507071030381402c0212850b951403404079200c0c10004010480d140a560300102d01c0c1100c4e80c1e040f441c1c3d413003111520100181e0440c098030a181c02030b0792010b19003a106002c15090307002e031030940c1c0c40c6861807101140f0f8101c8190750090b5000d940c1403452402e08045000240783c400c0030303405005c0050740c401040c1f00388001d0010315540708013040303c021a1940340080d502418496441500a03110703445100505807902c1240c10115218000c0c100e410141e2003416000700d1080000040780842d07214240d5140182c0040b030300d221070910301e83c1c01506040640c3c00640c094400e0130b109a92068007003003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 118306717 1250 118305467 118305469
    0x10308160501060f0e0108061f05310203090c120613080705010204062102070b0402010e06090402070c0617070f0e0a030614060319080409090f05121810050a03050411 73
    0x114000421000c2014170030780d45800c00d0142000c00c050445c0c000307031a4050b600b003107000c1c0811070002221030584400904180c1148803041501c80c0700404401405040513080305a6580e4014600440030300c0192525040b2240c03c100c800e8501500643d496003148000400441120f03480c505106d00400d5040e142007410b560340ca089911136000f44012407210400c0c41720259900541203d00340c0c403201c0861828050f600d03114036561000701300a0400c40c40e02c3c4500e4940c0c4401c000d5800608001c0c0040d03490b00030b00d280050f42d0b802c06002d0500003c158444840da20200c90080d40d0040f91b032034840d4949400c1d62042182c0810143e0700c02504400381400c00400100785200c0c203080000015141e001a041507010107040c0709944080d8048420b201501c0b101094907002224203c035903946001900c0301152400302050f030388000c0042c007623010700e00290010a403000028070503180c2000c0d00b40d050256810802c0b008440001d24000000d000b406090300d0035019030f0016801c14000c030030450480180340 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 118307967 1250 118306717 118306739
    0x1501020708060708160813060b040e0109060b04050a020913090203031303051b030313060507050c0303070503210709090c0306080f030d050a0501060f0c0816080c0f010501030816050106 81
    0x903c4143c0080d0920b0100061008200340100080324985000f40755400d04040004626400c1100074090a942e48484440d580c1e41d03270300000111035104000d1203d41103c0c100030000785046501540150f040c0000544c0090207442128880c0c540141700003100380d070f251400c000400440380100d030035200802c2102c110803001e0f0340d48002507200700c00401c20b0b00410304068000319115400e040c0290720034800709040031009989407007581e1492810316120a00c6040540c6011602d007911a09800006009030a02c00c0c048001c103da428040c000b080365010420704204801c40499010001409850b010f0040e100b06411000c440c203807a00c0e0108429032900c0300c00d03090021103145150590f00000386804440c1060254961100920340100400e40c07420001904100b4040360b10b00030082d000c0240000c11621805440c0f0340070001102c14020f0010b481c007516540d0181410000c68031810555110b010014001c0b103060707a601c02c00301c505255100c0e0310f06509030640c01044400d5500c07130101244c0c0305084 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 118309217 1250 118307967 118307971
    0xd021f0302070f080910110303011e03060903020d18050907030513140d030c02012c0a05031309060506070f020103050c0c060c0307080609130b07090509100807080114150102070806 79
    0x4c40d085542d54464604010207083c50201040038000300c41c1682540c0030f4003109032030443c2c240e2902121103100d07031062503140303202640004100610b084603140616a0000728030003500302c05e0311008800ea41400b02020001c40702d01c103181d0303c2140354000481e464804c0e000140c20012556030305402d049180c0e180c103204240c100440c030032944000b40394a5003a41c1409541c0c802c2246000030132131004504441e401407144480300f0b24203101c0e01e0020b40760b5514200003480c24941c04c041500c0c3c03140f815014541c941c0c22140308400c0e0307544c00c05001140d1803800c0003c4031035181e4032a480c030a11410a90054000c0c00d07004190842044041c047c02014070803d00c10f0740d100d0003410a1040e541d19066901030182c0c1000303451540280c8105040042c5003d409500c01e502d207400507040c403455031716400120b503080d1140e04081d41021111051029000a4020075420303038118400b42c0d01540e031038000913401c842c0b0240080c0c09910003000440c190059004109402541c1803044d80d80305901c4086e2540f40c0581 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 118310467 1250 118309217 118309223
    0x60417040315140604090203150c1c0501050118080c1002071a03010f08010908040e0a021b1c030b031002070f0c180c140f160203060c07030801050d021f0302070f 71
    0xb03035103c0c0c2091164841619601c80720883e0200300c00170f49134001c40d58452081c0d00c125400c240e1140030030124001c0d001034868402456004a04a002039002003000d40401e00c10395010078800c451404908400c0c0c51414180d491403401400100319407010458000c1402d2800b10550159820104018400010407441c840290080f95982c0d490400d681201e0041a4000c01c5641d1524403148000b9900200301c40c100c80388100d000320f01d83c4031085218004d200384403040d101513040e4074000b100000041a180702e60f50302d41000418415101c2d906800703590318200070300d0307141c0c01c4085d0184c641410b42d409896514003d1380701e41401101d035561100100c0b00c42e00002009d5109800303803440c2d003d0328004d10303201c045a0719003e00d12590785c84254040d8016502108481d420100c0c0341c0c40b040980803402d0403880e80040807101c660910641051096000b040c013a00000d80d00380c0040340394106603a8003146030303074043e1058100c101d00c4024034210307801c03440303180b002c1680801851000c60001d03041c048840b40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 118311717 1250 118310467 118310471
    0x40504151d060a0c0e06040f03030f030209061b0d0c0519030201020d14061306050d081804050f1e010302031c27090e060f0a020a02070816060f020f060417040315 71
    0x419400f40c08426030b5000284611b0003040306008003a0b440e40300304222030f41401c01400354540071809902074081c201c4110341001c0e020801400f281940300c0d007045540b82100c150340d80200b8403413003212000310b9040060043e41c0442c0d1040715516500c40d44400d014040c0c40014200302803075078944295000f09410414400e021818000b65150400c030b408501c0c98624000c00040d4a80130114004200b0083d02502016000c240000002e03001104450765400060080065260038150360104520685000461403c400400c1072046041d4019905a80d0000c00a024210b0582201e5030504620b841c8030301000302d00020380c100281015034900a040804c02c030410028201703a029000c0340e441c0c0c1001c4103e40e10040a204010305440303129a004000d40401590b5010710400c140e2a04075241e00540081c441c4900000c1440400c15031002500e0791640e55440d80180c4100490b611414106c1e007440b96008500810001081078000d08001a60410132500741a92a12000d030140014405a070880d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 118312967 1250 118311717 118311731
    0x3010204090c110708070e0a0e030703120b0d020f040c09030203060906010801140c03073203010302040e060403080c0d0902060307020d080c0c0a020904050a060e0f010605040504151d060a 82
    0x154004010000c0c0c00080801005920700d011041c680c0e40380c1b9440b40340401006c0b8800704101c1410707500f040801000d604200daa89603281d28000b404138000780302c000c043c43c5c40d010013404c680c40c0c040304640010742c00a00124102d0400020800200007400040c0280806031400000503102440401e10860000b0702500361589000c62290030340d40181030803200700804104100308401000c056940002081c5021218a20420f814000000e004148030310742070411918030076804801d030029030581c0c0c802c1d0360500511106040f40c075501d000c03c0c1c40080100710090001444446800042d00b8095107a400c0814130180c590040742059006803030403001a00b10504410059402550060b04583c9a0b40d40900d442010002207464044800d130091150786401c003c00d0a00c14100105d00c0d18940104080040c628039000340c036a10b9000c00540d03005942003000010f0503103014070695201d5a046030490400121152010000302075035684404505255540d00181c040100640352141c0000c40c8001004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 118314217 1250 118312967 118312991
    0x1a040c02031b010920010215010803040602100c0c08030a06030b01060f0807020c01020705150f130f1413021c09060f1103040807030e12030705060633090f0301020409 73
    0x400340d0b408005509070305182c07110b0b00003a1403914518650300c2001c00da100362416080100e0504040b071200c845003010307810007c149a0341c040000c3c400c075603082d021104450b40c0140d412080d54800c640e0200030811085071140402c000d01c0046520002e00c900003d805503c0c0da03035140900c030080e0800000580310035480080181c102071015080402c0d070004218981d843c1c80000e545820901460780185c1045050b0008025960709448251001010b0030b620b994041c0e40501c0c0c805424481e42111443d07810001070612076009100d040381c040901a240e0702e84404a142c2e001e9130113030480c4508101d030848040c1544030a4400c40140e0762140d8004569250200002c200303850513041c1c0c0c0e6080340e0b0100148400511050120346515515083c081840c01d8480700040c52104c00c15121201070200140c0c0000300480451032621680307007240d040710f08a0a11030014503804500c5100c440c00e100400308107643e100404060032902c41e0040c030f0207480306010004282a40c200d584401112038407201402e02c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 118315467 1250 118314217 118314247
    0x8060901090308180606190806010b2a06010b1803031204021f050909090f070f0e0703090f1704090e032502180417071104050a0b060406031a040c0203 66
    0x2c00703822820082003440c14400d40d41c51300d8000d0802841512042804801c90711003507c90303c01040083c041d21159a51100460020745c004002282d040d201040d21380244003100030207690b041c0b80c5a00030039041e0300740040c2900c503612a46102800280201c15a0020340d400c100401901c001000d0710321150a0502c144800340c134002050042203124500c1c00d416860303100c020390f40c1c007900c1200c941d500b03521801c0c81d136814400c0c1030704450200e0050080100b0407020700344550080360840920700e07505558104080f0f0440780e010070002c28490404042d040412170310701e04174001011542f90145070581e41c01008080340c0d030310030444100d60408240502100000f840400c2c03001380c110101d851407222079001030b404072803614054010000c0400802c0911607424142c1034010f80006103150780f580a400c1800c6840074080902b40f040342000001080006c29028008015101511050400b41400c000398054040d26518400c266100364541441e50b480740103d00050040750081c550b0b8282028080c02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 118316717 1250 118315467 118315471
    0x50d060609080a020d0606080303071107050f090f040606090515120a1106030c04051809060612120f1303060902100e03030708090103090209090105160c15090203030408060901090308 80
    0x1e005055408000741c100114044000d2036049540703103c9400d0300d14001c0010152508000c070b1501c07000c81089500b0390400044915504100c0031240034960b1a0304100481d032852881c1600305061a0118080c1b5455640b82ca030030510682c03001c0382407a140c0a8000441d41c04076100503002071183c011002c541031003254500c2c0c2d48452005061480c5031a1035a50b00b20084214944c0038000000019511003106020346001d0000100a00f0110180c09401c0352000750984149010b805448041a400e00d41070201552200c4003401030000e40400c3c22031441035400003481700c2d80c56002000b480040100341e202050141d4811000000c1c451650300522002e0900840f1aa0601544100911305550000103654840d9440880d8580c3c03210b0460048001e0181d48034025044014013081c4020103406420803071050b80d00800c8070065010015003190000d0041c1c001403e1303e683d4100942064002d80c01074004640003504981c5440d584500d0107107401021100c0782c0d1035956900b55130080581c00b0510340c0e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 118317967 1250 118316717 118316729
    0x150f1505040e120405060a050705071d18100506030a020d0c060201110403110f062a010e010903050702040510120501050108070f030803240a080c0f0406030f12031407050d06 76
    0x43c2034460841d02030769100b01d01642d4861100030070301c01521072240d011240c203140d001045c2c6050f96074801c2c6060380208010742c2844544400c0e8002080310b103420800080d1001c8242c02002c00408081148006044c00b42040b41c25000d4000c003c2c01581740d18042d0121503104000b40c002645c5021002402c542c0340e003480589090007000104082200d01c1c001031a800c50440d1714181281020300001c40a100d50054542640c40c03031540d140d0b0042010301041094207042d0000c0c00380703040e4903191a08071580070038002e01149080c404d0f5405414160301559110352050b00a19080341c840003000047c4034048411a410380d1200014040c03d401801624002e110425445241c1825a80c41c02e03802d010080c18200302c3c0305403417200882000070022410540c04007030b0100245075240c085d03894591460101c1c05018a48001d001031a0741007a00c10441202c0e0030489540402c01d9658410811b03581e8905080101903c42c00c41c1144138410201071030243c4941e403100782e40c80140e10703590400e4512540c00a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 118319217 1250 118317967 118317973
    0x706051b1603060e1e0a0203010f11041404090501051f05090f0103080a140a020714060c0601030311030d0f0614030a05030a110f01060605090108010e060d150f1505040e 74
    0x35030141601000d0710042d41c2d0f102d0400f007038100c450040c540c5007030f00d007607003401e01c200d015030240700415404510750030700c207000354001d000c0c0307104020009050b1a82d2868030050108100410080c09084441c0c81c110040010b001190250f803a844945c00c0d510160b07544410114030082059401c010101400e00600080d80c0e03140c903a18001400300d051500520020b00740c028006440205540700d4040c0d110564040740c0c00e140c46116003940203644403c81c1c040c05501071034004000300340c2e01d040c1017500c044200c100000c12040e0f080d035030304480400003060320902a100a11802c000150b80e400380100b085030f0740c2d40024550b881c2242d000c0c1c200d400d101025020b5004444c1060105801004550510780c43d0308041c03040c00d003650102464500c00c0708600d8001d528003000402c006502c00014550701c00309907201550f0b642c0780c0d0140c043d40902610001c0c3e1151070000d4510020740b00080d082c6c8042e06a03c000904070b02403c0c0680250383c00c0d11760002c55200c80543c20f000be480c09100d5245204901401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 118320467 1250 118319217 118319233
    0x50a06180909020d03031d0f01020a090806240a0306090b060901061b1211011104050f0307060225050405040f05060703020a1b020a0b0c01061d060d020d050c030706051b 74
    0x41360340d00710300b04400b80425458100344041302c201c0c2001b5405843c0e451088400d0b500b10414018000e4000844100010740b429500150000c80000c1590140d50391458a0309070081b030f0342032106030105080c00755400000c0040000701240b40c511800340d038070b80a11001985882c00c0b200b04050020140c0240c001d00c074400c0361220794a034011030608110395100707600b14808044858240c0b0141c01410400b042c43d030802c100e0100e4841c034500034108803501601e801401d440c01c00d0405886e40441d029040040e88003009441d10440380c1454003010101240c40066550784400101d4255042100d060391010300f501c602900700441046542e9000150f85021814144088401004c182080511040031100c0c4001103055564010130203008240d020903460381d44201c40b590602030021446509481614a40325200740b0341c0200702940304480040940c010b200b4580c0c03c1208140d007209080e500d61113401c0030300400e40c40400284010b00041c1c0c81d240c1c2c03100c4440030a000343c4105501d481c5156084800c6c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 118321717 1250 118320467 118320469
    0x30a0206070504290c160302091005060307030203070c152f040603020306030c1801060f080403050a030f150801061403010c09051512011202011e08160504050a0618090902 75
    0x180e81c43d013103c00a0044100d805a400d10280078913841c0a01034010002d004504400c1c00d07208200f100d02c242c85c9220240d68941e0101c002c110b0301e220740c80d00090100001040c440c8242d000b907500c07440500341a2080340e5145c507a000480d024400d0250041e0f580c0c0c400c0313901035130300084041e0b00d4540302d42c503c80040950b81101c507050041e4815a807d058010000c5005da90f410701030a90110070240918104441e034070004c0b2850344080c4030b5a804241d0a01d41c4c03a2419201703045861186070162205032601c2141c1004a0080860f040c20740c3c14107603100c98149000d4400c02007240240303501c000205025040022902254000c500d806100341e15001407207180b182c00c200c9500883e01c088400d00c80e101c00c0017a003081c151040b01e801815201c4140004621003003401405c00205000303030707900e1942501c60000035001007816688a0301291801c2c0002c7c4004502c2d0141c0a0840c2c11494103d051540c0c450109101d082c0c0703030304064085440110035240008240200000030a0f411406000004070340e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 118322967 1250 118321717 118321739
    0xe0a1e17070b0a1505010311040b030903030f0106030209031b010e030d11010b0409020901090903051201090204241710031506080f030a080c071e0303050f0115050405090a0b1002030a0206070504 85
    0x40310300c0e41410389a40c42410030708c03d100c0c15a801082d80684d0b413a96442c0c6503141c652250b00071a107000280d400c000021644c1c1c4c0c42413098031481400a40103001c00d03030503000c200d09150901104030f410040c0b50101c095040c0c074248005004884151103c880468011411500b518032211341136000307a15180310703000941d55a0b0401c50440304444c1d0f00098a00090070308451600ca0700c90346407903810103440001081c0e48554001c3c4211480401c40c0d211001140504902c10314229010000045e0004240030f40c084001e40220b1f041210b000090740300c961faa40d80c0203240d0180ca9841e00c01a41c1c0d0310000c22aa00c02404158001c845220107540350030303a03089001c0c1c01c0348005400c1082000009c241d000402140e5180b481103042802c40400390b1109900c2c004002d02821070346810420000c0d070002a5403c10400d512805c5846500e99034185130030901400444680104226036542c0c58004010b1203440c1c40003600c1c01c42001c0d074041d590303c805030803029240100c003500700c0080000c200410070000d1049 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 118324217 1250 118322967 118322969
    0xe03221d0c0c0304050a03050609010b0402042913031a0903041505181e040b041a190e040b040611120c070c0b03070c020406090e0a1e17070b0a15 64
    0x7541d2120384541030362544914500454104e1030300820803c1011061060014041d445030a6001c000d01000414100b400280d000b0b620544450007a0070880c00d5071020909000e10b09582c40035109818102c0100d05d803804525194030556803280f03100d030002134030781e0210a131a9208c1c488200840c686840c0175812461070342004020800c0100c003040c0341c2c40300f010140700069500c400238900d1102c41c1590b0110707101010740e000094412442c1c015070442d9800c02d8000c000b40e1500080500c841580464140690a200149244c2900f900030a02084601c00400450b000d40d02824100c0f40c64a000c1c0303810340c1143c80e00082540303295014400304046502ca1001564004841c2c4d60f015165100d51030300140d003c0c165003003480010404020000d1455100c611090224000c4405101c41c5039644003a0080301c440d0b0000b0f883d6900309040a4000c0341c41c00c110b41d40c030a02d40110f80750304d860950320f500c4020104214040b900e55000941032003031001886070f198102610800c204035040c440c03038a41c50b217070181d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 118325467 1250 118324217 118324231
    0x20105091203190e0f18060f04021608030405060f040f11030a050f010f060e0903090d0206070c0e1e0f0601110106240f300e03221d 58
    0xc90708205480074091094502c0440312500200c038034900e408014200ca03086030596030080180c0f4200100c07510b024100380b03c94021444140d40c01d501c9090500040c504040c3e459a0041d800b007020140600c4502d21403000c00340602d00b07045e241d042c1840c00c030b41403407400b4018680340300c1c07044240004601c20500c09102254004a134620b8030241001182c1496600a009040e81c09405503e074440141900a000100c140d00020868292560503500040d00d0640310344003030380d00a00000d0058140024204035040c0004c01250920f4641d54491f04007103040e8120480111500060085544c0300e01c5608241542c4455113040c0f0f0702c1d01c0d043c11250008010005030400481403041c840d26102903118801400c00c000141050705410345189000001e00712180c00010100070940b201940b0540d1411203100c0c40c020690380c0a40f4818058980558511895444590b50115204041c10400051048002804421140080d400302c5006095202d5000c1d00311450000e5400c82014110003000e80e000316 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 118326717 1250 118325467 118325479
    0x180b060409140f0c0a0b0a0207050f150d06140d08030a15090903051201090b030d050904060513090209010603020c10150b03100f210609060908030109020403020111030702010509 78
    0x25509001c07000b00314590320024980100056041850400b040d104400b00e002e4410b0400070750f4034807401107144110f1014000580182c14288003d2400c1c01382e02900d80300082c040a2104011300030a1200d5014081100c48070741e40d0f4408104001e81e14141840d03440084400354003002030368070b80e4105840010080c400c000ea45401c0900103219201600018202c106005c200004941c60080e156a1140601201e410320141c000610b400c01c5028904d900427000d0080e029228400400b5a100d410071031549070f0154440b0000718064481c01d900f00c03a030044081020900003810700500007100d0040e008481054010410a80c00100000e86e070300700014070b4240010103220980c0e010400f01d915800640c42100c0000a0103844203500301c4507004d50b40b20944044c40e1035a00d0358600d282100040416403802c1c58245c0101c0407404560150007480d0060201060501482e80c8410303455000b60031081c0080e034042821f00039940d019011075400c203184401103207415960340018206000d4003e074035115003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 118327967 1250 118326717 118326731
    0x1312110f01060e070f09030c06030b120105040c03021c12090302100306031101050912240f16080a0b0301092003060c0d1e050702071a030f0121050703120201180b0604 73
    0x9441a01008007e40d0840161103583c1c0c0c460300c004015140160407075110380d01003112584d9808040c480e50780610791050903078910520316402e1044119044845800c0d42111042c5400801e0000e540c401890300c4990307130b002c0035a0071841003100e9441400011000c01d407400c4020b00028640c512440d40c00c203400d017041da41300c80b403890001e1640c412403104145207000761030a84142649181c940d0540c8100143c200a0503a02c04040205001d17040f0b88400b01046001c200d0044680244a426000801d64502044c1031303020a01003829100d444008a4100c00b106041984920000814414909013140505654249a0f8911400d40a20f0030400a01543c2e0051002e0040c0d0043d0b5100f040c900c0710005102c0352400c100069242c00c018441c40341c512100e0325009000c0c100c40788c200c9200d07801540349008903900f441d01d2003d25000d059401b04911200400711408500c3c1040940d00951046020b80d1a000d60303808002d0070b48002c10b0f1481e03e03403011007900c0000194a16007295204100303075400100c4c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 118329217 1250 118327967 118327997
    0x30f0106050f041d0f090604051009110d030c060c11060414010b0307030b041704031a0406060f121407080a030c11090a0b0102011b171312110f01060e07 67
    0x180703d503038041450002c00044000712403074042801440741801c141004001c2d9907480013151035200c22940240150014503014018401d980e0200d5201130149075000c0c19100e002021591350028001d081c0d01281e113110f06407040210600a0039402c0625140032001c44402c3c1c01c5480d49c0319800f400040c11346802ca510205008001d500000190200034125812203a90b401d100461110584043d00c0a80801d0001c4114800d05011601101e43c4201280040e41c190f941d003040340e29028208491b07180e1142000280c0c001c400a03198017a00c50501c1054034481640f8140c0305e140d202d05490300c420303004003004004507200030910841d03e070f405050160015041d45088002c08441b241c041c0d40c060081c0c42407041c0b400d01507104045c055000e800800c0b20905803040340c403a4440c04000140001c006080c0c0c4080c500301c0015540e0840380c021080c084c1081180e84100e081c401c40e00e402c0c000140d070f682c0090300485042003051004a0610001c0204c03e042071000003c1c46c1740200b01030203000088a80980c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 118330467 1250 118329217 118329247
    0x402040f2108040611010b03030304080304030e030c09160801090605150d1e02120f0f01090b060708070305030915010503120307020a020301110a020c0a050310230103120f0302030f010605 82
    0x41c81c0d6010049660303c07911800d0180c25241c0d585a540580d619103a1094800d080c000200d0380561303000258682944d5403580c003190b14552500c055a0140a80e920404072030b10342a05c0c85004456420898101ea4108140100312001c140d108018031410041c00308820740b100d40c1e40420411502400300d595080c50604c80c0d01410300311450100980e19008112581c20260307020703140f00c4c01d01c4943e031117164445c001c1e503140c8201c05450b6a5030840051004200c03c0f41c440d400002010006044035040c01d2f040c2d00c0d007042c1500507040980c003082001080201404051001e100141a01c00c0e030700c4a01d504002c003007a80c400d880f5001540c1007070008003144e1401c1c02002035130001a4018028006c03d5000f25201107150403502015003d8403e01e21036503058540b0002c00300503034601030001e0520390010060b150150480d11040a00000a83d04400000c125000c2d068041c47c0115451400c800094000414803d107403200041003501c14001e0009001c2c2942e2691b044921515200b6180c1c12020303040301c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 118331717 1250 118330467 118330529
    0xa080702062505060610020d09150201060803070b1524070f02060c011a04021602060310030209040506071403070518010909140a1d070324020406080a0b0402040f 71
    0x505641c2440c0c88800f0080c00003102e601c03420007540c0075000f60110364020703a40c8103d038000b840081444c1032000d100010303161540f40030344000d030b10000c10440d980c0e41a0500350f6000b564140e524001080400a41004904c511078500c20150f440201a910030480040d030300300440d0003800d10007030000d0408144900c913301c0e44001360b0002c2c5525515000c0042c6140209201a045020b490307654402010030321705403094500003c0b410031007441905080d8200041580018601584d080c82d103140400503890b00070000e48104e01c948000d01e042d08240b00c6c09041e4141d81c8a184020b40c03001c20400c488161b00c401690b15040c034101203c0b6031000c040c1c0c0162980113164220303040182c60418000c80300b00c000c0c1c900c54041c802e0714400b04588075107031030901e8030005080c4104009a000c031004100292041060300da40f0ba44110044010b0303c960f914180603a4459070080e00056600c2040c014426200d11031f01c19817060884085103003030301d0020304c1c0311584030510444421616601500c44030002d0422069 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 118332967 1250 118331717 118331767
    0x4030e030102040b160b0f1003030309150507051e0306150703090803030717010503030301030c0303050d15090c0314042102010209060403030206040c0f0323100501091d0a08070206 79
    0x20342c6483c2d1482d4840d1070002602402d076522140680843e028006007050b47d4040c60079201121044e9043d52170a9029000e00c070300c00c07100300703050081038526040b092040b00c0c019000d03643d44175901c22050317107220280000c40b204480c80e00410418801c20740d40e0415250001082d09c810180c49504505054485408940c00a0f1040c0000000c1280c031f00e6104040805104824500740c440b42d07290000d00d070380e0717000901004050740c3e51204140082401080500340d200340c03091020403000134034600c004807980c0a51104005a40b240000841c1d55014015030900f2281d204941c2c0c0585001e0311021a06c0c42d644442c1030041c0890329003a01494400e40440e20203c90142c44e040d078642d6a460029541c2004036010341c2c0d9401041400300d10080d01c0100c2504913508000d01a51840c103241390501e00c2142d40c10804290712a8901c0e44900c0119406002d00070120b1010000300070020300035021000310800e260b0755003074100c5014100003440d880c05903512942c041d5a81a15151102018842040d40b00c5200c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 118334217 1250 118332967 118332989
    0x706050106120e0106050306060d170f0a1101021c0203060402070b01030b07030e06090703021e270106020c1c440702210709021b07050108060904030e03010204 70
    0x700724203030400e0240708007090508040001d00c1c203805403c0c2c05c8800c1c5000e0194550008400310f800c900c0d02100d0381d078056000e83c0c104042c80760076100c45081071307116219100032500c011503400003094000721004200c403c3c0304029407400c3c000815001807143e61048100485601101140c0d481e00c9540c10b49070815441b40c94a00a540c49040510148000b122101c0c0000c1c20220018200e2401040d654086c0546200405d41c8600359420010300d800d001200000901a0050f030f103103507985061614020501804414080700c2c450320850750780c840140c00850542d4840720483d0700544602d50450116510600d41c280c170100c5500d000c80c160403005146010ba0080b40c003e1524000d0051618101540d2a03042c2d22848136046040c210940103900c80690b0140800100ea10302d0401c00180150f00403001d002d43c0c18107030325686000200d800c9849520494044501168040c0400308068000740800b42406035891900b070001809416000700010100b1560f16041000c50700c0c25015100504101064 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 118335467 1250 118334217 118334219
    0x15031104050c0c240c0f18181305010c0203090315090708030c030a02071a1206041b020a1104060b041701110403030f030f0b0f010e011107060503040b0f10030f020607060501 76
    0x600c000746a4000c005086030892000454800d003003100c00c5403031400750b94001a00309549640040e80c016010030b940c7e608501c0180886c40741d2030b840e1000b40d104d85640c1d0b0001c0030b01c442c1420840d0071140381081207410355004100703800d90780c0e0700016541130f0031141181d2003a0a9031144c81440c105803241d4840300240c480491070040118011001c1e00c5001101c0d802c403643c1b207549560726401034560074038a15280c04104940d5940e0f02440765802e50010b8040c0000c21200c040c0d80450048041404034800140c0103c003401c1d04105074081c013155174000c07c0302c0500c002070904003c0c02d103d100f907104041c0d02d002070310342594001c002900140e41d0829904003982d180ca41e24100035011343c0c074800a4030000b900e41b910070700c440311003403240144005014120703030241400080156000d00903400114140714000800c0d075040c0d90200606001f41207070307070340355034aa007414030f40400d0b012005881c21a421a03508100030b2030300c0c03500300751408898020740c0c00780c54500caa001040d0148202180540300a040c000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 118336717 1250 118335467 118335493
    0x9110d0212030a0f11010605130e0114180708010b0307380a092102040b1503011202010206060a030f080d022703120a050f03060f030d03050a15031104050c0c 69
    0x2213011035104040d1581c41009000030401400c850550094a13408404012851050320507603008607035070035540300001140e5800c03a94130160b0384011030300710340e40d14800d5042d15840c042c184079540050075200000c0c06400428000251108164018940c20304030600c2c19084100000c0882c0c44040480412008050b294590403d000c2d80003401d86808920324100004600c6103370b0410b602c82c030508800b90301d50b2500075400c11010701aa20f0246030b01a6046100700c1041424030025402080320302c008841d1240c1c1880064103001c4020141d40c4a8030401c482040416500800d22800c1d50344100202d41d104006c0115100030b020700b51102203051051700001001501642a140c0744000490803201d00503218450245c95208880050000800034031010005c00c401c04081c60b0824002041d036a520078000b40800d180c01030304c1c1020300000b0f498009114440103603101c0d1068a032a02d4500d03400c031034115210002d40f602c942c00c1c410f00480d030b11000030340381c45240400d40da000c1444406599481034100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 118337967 1250 118336717 118336727
    0x3120e0d050c0306010501050a1706130e010b041401050a17160305161a12040501021e0a080a05060907050a0309020316170c0108040f06061203031a0409110d0212030a 73
    0x42e003040d00911912001007250340c003c00135160840010380d40c0151064203a101d0301c012403005000150801000c3e5141909032440e03005031261720031003d00005003449182c00b00700540300c000e200102c05410913001840141c4502d2050b1003500d412080b8010a40502d4080500d40700200c40b41582c0c40460300c0d07000c020408d000c25581c1c03489100c4420310b40c0c250f40310003070111140840745a0250f0240c040009403c01040c0f0f091aaa205c0d004030001803c01da10702c81c1141f214450398415444102e4005810501d444c0c000007615000b031002c580c10007252920001003040400017520100501101048840e0224171075013195034500da019054031202201d44c02611003c0b501c40c050703c156102c000c2c05050040c080090101e041c140140d6400c4225100c1c1d44544a084000741c2c015195161915808220356644089140200748243d500158080c45200510050121041c4107403182d400c155051002c9040c81140d0000500c0842e6190a0031a951002584403500c1e03103c00c80003400b0209550300150382003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 118339217 1250 118337967 118337983
    0x4030602031e070519170a05010510030c08070c230c01030b061204080a02030705032a0a0507030311070e010b090a12031e0e030a0c090f090b0103120e0d05 68
    0x20308030b501000c9401d41410100000725950000034000f44022825240c0e0500c3c115460101c03402c02e242010a0000c0303042e4010802c480302d1108503200c100403c42d504002011030020083c030b1a08102c5c512144200620494000d407106040181c03602501d03090140000780015000001c2d041104200d0120f40d0b01a11000b030141c440d40400d1910200300540c0c2001030441d0400d540600804241da5611390382c08500e50440310300b001c1148020b00811340001e10820007810101c50051109102c1c0c01c01654940c441c1481e0381c0c6443d515001016444001040001c00700d043d240e150421b641d0b513070f41c24001640307040d419a000d00c580c4d030030100000480840070401070021314020b072100c044251319801c0700b24280c40007000007130010740016225966428000c07102804604245032408415007580c0000345004401d06040e96006034440d810007401c8400d12660303080e003075915418084c541c0c42c1c0d01c40920340e440500c400b60480d00c00c041d413460103038030903204024081c100402039110213046003401030340c4004d5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 118340467 1250 118339217 118339231
    0x7050f0a0c060b041a04020f0c030a0207030c05040c050a08070201021921090807080309010f0c080a0e07080714060909190b010206041101030b1801080a05010501050603010f17070b0403060203 84
    0x28200542000b410203001741210001e00700c118030045145101400000d40c0103121200c6089001d2154642c02c136414402054010001d6000706811800c0d410820844a40e69102c1481503103022469050180c002d0140c0c1c1d10401e9a041859290751034090603400382c810310781750380088910b2410b1102085e030400c680c0d010410700180410202541034041c00e04031021544003a0003240184030040c00203181b2801550700c162280000b01e10110b040d04d5030019110901c100034040b40f1000c0410214041304e12446000720584070040c28554a0312800c2034031a0024014101c440d40e0742c19030b040603a00c40c0c60403100e00d0300c1c000e04061450b10700b080001e04030005891005560710708140510301c4640c800a04079000b00c4c0c0201c071a44150b0104030041d4028205204001c1c0c02240d107403500031250f0b25400025000344440780180107801407a1038840d00f1101c05800ca9441403005000610802060610500541d0111143c81d08050080c000703c902e8100a544180c050400008001c802c001103900a1805046 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 118341717 1250 118340467 118340471
    0x3020a1404060203030103081c180203060a090215070606030c09090215030c0d0e0a050109030e120118020603090f06010b07020f03010b091b090909010203010f0b07050d0807050f0a0c06 81
    0x610484a090901c1503105590050380103000600c0030a02280040910f480c1e0303100c1c580d01c034200c000001d500366160b00b03807052041111040a6815410b080c0645030f80308407841400c000c2611030f6030010f4000083e003100042c814401187d881c0030003009602c40780103160440a4005190766031240076000e4561100308900840c031028500003410300c01c405403400303021441081810005101101c01c000c00390384022410a101d001d952a01080c400e00c0388080190207130b40c540520300c0c030304020700c990003020030905051a071510000e00d18024403001031a80c3c0329411100103560340c079071300c9040340b5210010984504034000d090000407078040c10360081c0314140c42542c0311101d02c01904c04040c205c1d119012045c2d00f2150180000b800c0881000745010410010400365003000c2c00400070811603042210114a00c1e9030000042c01810782000300980104442c180107407134800f5a5640946503070300340d0898820b101d41c0c003010418950042080c4e0703c0013003c0a50040c0c81c0c8069030f00080002e070800b03000303549580c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 118342967 1250 118341717 118341737
    0x50a09020f09040812040309031a06091008150402060712052205010e010c08040f0303110f24061807032313031d0a030b0912030601121805010c03020a 66
    0x420010b40030781c403950304010703010305222142c0341e000c010150040c000c40820030090400301c0024500030b840311120090040d0140c080c64510b091060074803029001c6103401912540400031000001035404000c2481e00308905a40c480303201103451801042d0000304070408601e0103101d041d51000c043d02e14035200c06101d29401441d405a10b0b4280203d0158a0008007107082141265014118880e4100c0c80741035001d181c01d0b6200f2007990080c3c2d05410440c0012581c000742c00b41014100042400442038070301401c0c00c0d41c8420741c800c4001020412200904641c0c90010f911035440c5004588450a8081c40881900e04403000400170280d07884480088182e403180c10400c0c2110200d0988078040406115000030500d46064071203440140c2c6446201c441003980301a1619082034182c01144291008078690404440306030900d84401c5008920003801d104100f1140c1e8021280c0d041584071000008240c4420000610480d03802e84001e0300c25800d000810b804164160300500f5041c2e81607035090701003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 118344217 1250 118342967 118342969
    0xa030f111209010c17161e0f170f01210609060209130606050417031b070312020c0d0609050a050a080c0d02070b0a05250b071409150a030f050a09020f 66
    0xc509250381040d540405c5000a0b12083c1144018803280b803641020001d060f00c1c251110101840010003000150030444000003c40e04601e800c4c48042040c0307442803141c90300d941d03081005441442015107d405a0450700b00c0e41c02000407080405401c000c0c1845030303940d1401c0c000040c1d13022005041c0608510302d01c0204103002881810f040e20a5550342c68513091030a0001801c54041d40900c11881c0000c002000301c0f01216100355114090a10240503500e15604201c0500c601a0300b04500f076400215840000d07a8a49800701c161540c85840090b006c0c0707985c01c10318900400300c100107145200d402000700c1800781120141442411020464018000d07210089031240058031690081d9402485026442805080a80314480f030b01310f000451850300001da5512004004416141500c0354000c1c49000c0742d02c110301a4031500000001440e0120040100d407131045a80545da004240100d80ca5030b036984a50000003203209442c00500c078504080380990000c02413407108034403580c02c0c0b00600d246 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 118345323 1106 118344217 118344227
    0x6040503010614150a080c1b15060a090b01080c090d050d0c060606030605060a03050703020f040e01180e0a03030509030f07080306090711030a030f111209010c 70
    0x10f10507005001c03202d40c8205460b03034130403010071001000301c4d08030108a411100c2c0340b0005a481c1c860003004002d807146001011618081c60020401e8552000081401a6011034142408603520700c2400c00312201c0195403404540b0403000111004880c0c0e000d000444c8000e00f00c0220030341d00b03559090030010112051008030f52048009001e220951040303a002e0562401c041291508220015101d4001c51b00c0301e00c2011385070400500000d1294040e0f0303015552014580da19075403284140c2c25000024001c298403a00c0010b21541007680e1800b0f18200c2d108010064600444039880c00c901400340182032802604c02001000072000c141002890540c0c010300c00ca9807241440c000b00710030014003814800030440541d070040b03841007002c011100d4038601414001440440c0840401c0900250142c034008034201061008690701c8544d422031160011000801c1b00b9035001809680e = true := by decide +kernel

theorem cover : BRFrame.Cov 118165467 118345323 := by
  have h0 := BRFrame.cov_init 118165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 118165467 ≤ n) (h2 : n < 118345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
