-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0739
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:30:58.542091+00:00
-- url     : https://prove2.me/submissions/ee8e0e28-84b8-4dfb-885e-f78f4d93c15c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 132733812 ≤ n < 132913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 132735062 1250 132733812 132733823
    0x703230306100c02090f09060c0418090302011b0216060306030809060310090f06091407020d0f0203040e0a0e010b01111207080403081911010605030c0d0302070f060e0102070e04 78
    0x20501c14034011080454403802c50401070116102c50340070500d400401c59031b5040c0340f0a150108007011405114590b400415005d2003032419082040001ca881d14001101505039034640580c0700300350007540f21032288140b02c49100002c850301c0e030f002540c4115551400300749801c110701c0064030700c5c001e0251780d06490380462198100f4008405200c0c03117400080080d151280c0c40b40300003da500486c81000d0030707030104030030126540c0e0030008001c0030ba078521522520f003203101d00c00704200c0d07a5002c2866140a481c500c0c00011094102e03108903d58002d0303420074a401c4003181c040c0402c504c12944100c03000c180c0d10001f404120032070342c01510007200000500a060300650507940b0545404c074010081d20340b142c0c043d60706060700c030740b951160303500b10110140c9120f9181041408160300300041d442390044030030003404550704110100f502ca05046031748a000703070141046030702094000e01020f400f0b44215100e0150302d0345c2e2044028084800884168054000c52001141071ba990090580c403641d0040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 132736312 1250 132735062 132735067
    0x141213030e01030603170705010b090a0b0405070e0603060d020307090e0705040c050c0d0f020a0609080c120405030a020f060d090b011505070809060a09080d0f1b02240702090c070323 80
    0x30030399a0f070079032010b6012100789d5610700350500140d84003880e0724000d044000300000e4202180007808100c031006440d60b0300b8410110b020807056074602d400c580c7c2c099000e0f500c0146036039083c070109140c90b006402c001c0d0001c0c200149000e211000060b807008440701290140203248080e0380a4409218204524144e900044031950320346010b0341100a21105502c12603812401e0b07515030000710b4501103000c484003d0001209000b05000308030140c2d0401001c4111840d0030b249c03800103a500d1016401c028028000b0200300305a0350345480642d48214685003050000a0f580e1030b0600358070000b4082d050385c0c4090800032036811441103042c0c40a4540c0207a041d4900055141081031075000f19044000b0080002408961075900740444800221503841e01041d428a801c4050807503000c000852a00d500c0c900102409030751000c03010880c002c40c200b2243c0c0c081e000f1301d0a40c803c510415102039004210001404882012500201089802591501031000c404014020181c2c0810301468101005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 132737562 1250 132736312 132736343
    0x106031e06080a0818030601180e070807120201021006090c090801090b13150c02031e0f030103030806190617090d2102070b0901050133141213030e01030603 69
    0x30001010b044200b50f9050001c0e00c249000203240c20000d801100c2c038081101c7c07403103684149c140102c103d155072450142100340d08110800340d491240344900c00040b2000c0d000f89055900a20441c28032940b810720921070142c641d4646401303031042c610000c00040f5146400144860103100c2c00002650260a600322622210107503412085044415201c01a0302004014000c00d50321070b81c00d0781032454001d56241c000d124001d40807080420040080d4900820400d00e404030144d007100e0649901d418500120f403a10030103d02050020105040c0c510040c01000c05d226410000242c020080e4002904180c1e80d410040c58076010f9140058000c200514031003800c4040c0710004242c45100d600c4010304114980c0c0341e5691119050341d140309585d550b48014404034100c5000c1090140803072050f03146102031010700c500340450100c041000c00a0038007040c0c2c201e01c030714030480e0701d80303680400341c07900d1800d2062000380504000c040c2207022036528508468554013a01921003280d030414040c041d20102c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 132738812 1250 132737562 132737573
    0xc0f0304060f060b0309070501080c0c030301180204031401020c07090b330a0908071703160312020a020c09010e01120f110d0b01061403130602091302030106031e06080a 74
    0x6440010060540d03d4a00100d10404801e01035841100c8000c005c001c07035880c1c480054060700000d020065420b500308004003541c2c0000048a04540c0340b8201c010740a6a07802c00e00009000b40d420040c060340982800050b5040150060040141d006056500ba0340c0d0b1600079100b102c04500b0703855044440c0300f80d01d001034840e07015440102401800e218624090350f15105003107510030b9a411000c41c44180d002e21896600304000006890000e41740c044003030315551655070302d000711142c001800a030740c414031041510601c6141513407000748000359100c02644601035180c9074080350340d900440714400005503884003508210f040b1000d400c1c0140c5226130a03190741e00345021200d400d031078a01110524030000c0c0c0301c400400f10030303602500d0360044650402d4001410f42c642427007202d000300350078418004503040400e0700880700d60b03204500580c6c45844030086204500d4005c240a84107101200001d0615015000741641041003241610150303444a140f03003c90b845401240d0083d0321403500c4400050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 132740062 1250 132738812 132738821
    0x15270a181209030606080f1504081611180609160504050609120f01060806070807020601050609030a060e01020a0207060503040f021519020a12020607080f0723040303080c0f030406 79
    0x4540340b0300114900d449444d40d40648070315078080689a03000d10749039020300d2014008000421500705244800d828191208074890080344150f41c542e90056613200104072440800002e000000380070305801c020b14441726541c0c4807007100c849000da402d040c006841a4510401c04619101e50340325141854200401e015103604044a02c60300103e84200b4014400402c00040c0000c0c02c0040000c50a941841304c203d0030208050a1034050085600a000500d90041452415544140c03065516080600b002130724002c0e2943c40984501e01d80840c1c1407002d03506400400940310540c007280c070140d60b104401c43d69844210340241c02c4204048042d0010318121001c40440000e00d0115400c04510b01c054042c101d914418210150340690725860811402034920b01c1d114070345002400c96841c0c900c4000c2d1000d04000c10309640030700d0030000070f0007407406241140c0e83c4403c111340f040040c50003078410b48003d501c00d01090b00030400325000100b503c4406021500300701102c011840c11b5440310b54640c8040c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 132741312 1250 132740062 132740093
    0x3120e090a1d010914010b0d0f061e090b070801271107050d050919030b040f0203010e0703080d0f020327070e0708060906060f0901050315270a18 64
    0x915a182c0300c0d05200c0424000c00031064000c000740c007101c9822041d41c1d82180c4e000c07403029014034558512310700401c0022078101c06d40358002c031380401e03e0012065070780c02c8a249000c60302c03407081c5089007a030188010301c0d00c890311580b1320742c484210303503625032416918035008259020344d4884d01910346000942c1c5600071010460600721082e04200c47d66071418140711000c0346038000075001041003462842c112000b40000b101406103106664256110300c4401d1800070006010f8070394130310301d0341c00f152002d5100000e011028019104130b540c59283c440c415503c0400c0d05c42c203150414024200d041214402c9900038865488200d0802c0003c4641145286003085047d1703c2d80510341c000207602810008142c40ba1215039108038061501c0010003420709406092140038500c1841700c007114100071022a508640c003424181e0f140d60f252050030b070807101d0030400305401c0ba990031413207940803090801601044607140380d0f00e01c8070f80d1042c0f59642180c041e6203400302580d080f40400c7c0040740b00b103000c0b10400b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 132742562 1250 132741312 132741341
    0x309120a02060415090506180402130b03010f06080603030306090718081606021506032d1209121506040203180105041101120b21031c050103120e090a 66
    0x503846a400184940d08140c4c41004020014420300700302c19800190800905411500c1c2810603e007050701140b280d40000c00d89001d241d000512010106003072020f00002c080101203542e581d03850f0050f040f10300320b040c81203c02103054035000c9061490040252803044001a14984845c1d4a0040c11100d80303140c10402d90314940110800710740c0600c00c1c403c0c0780d001888014079840144c0362613002480e0540c01000c41c04910f00c0d00082c41129900130580d03280c4501c181c2104500302d0504002c1c0d02160092010100240c4a2100300c1c1401501880141c82c00000c00c592081440050781030254454414440350080c45003144005102480e00d5405107401c034483c90206010200c0901e411421940243c406039002c69000110450640c0e1007124174440d054004070900c0501c1400000c01c003c400d005160540d10942a0300003452a0010025940300156090891400382540c005080c010702e0280000d42e0348007845a2300b00c0400d80207160a01910030042c2c81c0103055507a0350700090060141c141e00d2804d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 132743812 1250 132742562 132742573
    0x60e0405040f0b041b030b0f01050d20061b010902090f0c030403030c05070b10260304031e33020405030a0b070e06070303050a18030909050a02040f080d090501030b03030912 76
    0x45601c032000300da800b85128206907e02800e101c018030205c46016800b8503c140000c4179554000b07013074000c00c1550180c4003c80030081d082c4a0002038801e014401045408010510340c0014618054114034286402030301c00745425201c8040d0801c11010407100c0e800006410404030700003038429402a024510545441403e1030042c2c0c2e202c03d0103a40540c4d02a400d1703021380c0c5050000c0711000c00d0b00304924105014407400e500c04100702e140c07a8003e030f1101500208482408466248214060440342e603800000b020440f08070789c0c2018507100000c3c20b502444810b01041c2c01c03038100030340300300c42c103480c4010020500e04071a80d681c814846c10082289040008400b22102e040d120400540302c034034483d8601041c14a0320203500c004403210482ca9207420890f1800740c00109070072488200a813610f1400100f13880c3d43e60907082010b4483d9030302c11102214540400103041401180301c1d4100c40846c1d0b0307940c0c415640c99004500f07541301c1c51000c0e5416041084031120b0f500d040c10503007000951781c0c4141c80703 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 132745062 1250 132743812 132743843
    0x120309080a02010506090609090a0b0a0e0102030c18030105060f0d210302090424050907020114040309080606090123010e040e03030105010f17220c030302010204060e0405040f0b04 79
    0x4801c1d00035028040140c0c0d12002400302610304011026884503050f10748001d40e00e86140e00d9a40c40f050b0f1400500703104410300125060003c240c100044080d440c600a55590508141e45880390f480080151070500b40140a40c202e442c0c103000d117a0240d42c00414030f08008000104015402c1c1c11040106d40c4240c50608218143c3c4812a1881e21000c40303450060311000c88801b484291440340300c000c801003108030402581105202c5c5100192a002d48010456545038001a401001168003031200400c1e58820482050740c0904c040d8103503121703801507480944503a0148032034400280600c80300c80300010a802d00022211249498030001403401200307004660300418103c501c9080d003030940340c00000c010701131035800011100c0c80101e035181002403642c00d003c0c2002c440402503c0c004078249d2041418141403202ca940302260707031300986c408031056900e240280c000d5005208d03407804220881e0780c43c1064070b004d10915100c1c80c0c204206140d04491030f641c608a03420020000c40d50990941d400c0f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 132746312 1250 132745062 132745073
    0x106030c140609041e06050409120507031b050303070908060727051309020f060705030f0d06030b070201140c160f0515090304080c060f12060a1206021305010318120309 74
    0x304c007030082040705602001740b0042c0c0c010030303540107400c190f0045081008800c00680350140b030f220100344901d0115200e007010700c2c04450343c080180048181c90090b03a400030034404044011801459140c030366000c42035442c480141c951b84215010301c0412941818046000109200082180360600141d280ca64503140022000004019070700e600341d940350031100840c10030901010151600f00c64940c14510180e4030940c0c2c0740b00e2846a10b01c02e1401154403004080107400503c060742d40420b05c80d03024030f00004e00900030100c2600b000c50007003003940404e000d00003140c1220800180d51841c0c9181304800c1e00c0e003c41e07688150700210391f184560341502c9102c10050181c00e0003144001d01840c0e6880c500074609144c103204a0303d4a105441c00c01c800e1404408840880d0441c400b035040c00e103126a20003001030707020307281d56112501c4400e1582c035201c1080310075401020804181b202d85a9800e0f1224011821030b012200c4074003400981794000c0002c1f44500030301d041301900c10b01d00030444d1502503541 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 132747562 1250 132746312 132746321
    0x10f050c0f1c08010f060513090609050a0b0114121e090318090105010c06050a0e10060305060f040206041a040902070b010509070e0603060d02030c04091209080106030c14060904 78
    0xa89080350000c06aa0156500604000b060400d03140350500d00f03941007400341c0542d120706106900c10f0000c00103c42e481c61120002d840024140303000e0070020142d440e42c00c48084c01003100c825102502c2c00d1200d00c2c140d8020703030304052010b45c03082c150750500402c0d031611043e14801070312005280c591860f6825808540c003000d40d00c00c2c0c0300800610b0701c0380050710001c061500d5003049288510300c40d00040c841c03039a2003c200385625030031030070200e00c41c1c4500c16908000d000b0511500f80d10300070103c5c16110540503401c1801140e22810448074a236441d42c2d403480d00d410701590020760141081000700500803100ea4024020740d00012024a801d980c1c04501e012603010401c202c900c10b01d5840100102e1800f002c0459001c0020709050030103180910014859220041174030703119860720880d0109648080006101400c405801000b02c000b007424001881c4c10685041400900a401e0101d00b00c00180112400c4035802040607001d1401c00034038084e0034140b0141c1031741003c020301c078601d40c039501c0d03025 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 132748812 1250 132747562 132747583
    0x60501030503190801080307060902040b0d0308010f060804050a060e19060501180207150f060b1b0613120c082b0e070f0b070221030c0d1d010f050c 65
    0x119030324103a0000007000003a400c520f440500044500401059502100719602e06900c10b00010b00c1c80a640b0001d402000303644203698100300758000000c01c040d00521810706a41c05404403121055907404210b6605c0e40032140200503412105124000038565001010140080410364168500079814045004c07050441520300750740b100c0040018004044007290320542d18002545025419218a4205013603030302e503041c102e0f5484070074001c800583c2d40400080d1002c1d402c202d5a40468103003042c400b88030402c466600c1c0c0a0000843e00d05c152111300c1005d200d42c010004494405102d6065403c18030685080e03c030702d03604001c0ea0b80d1400107041100528079a050413158240040c0c058141200c2139048241155031100c803082c00302c9480d010300d134001c4031b800c4011550303500070030700c08200350300c4a09440c0001c0d140a01c81c4500701c18008000f4100c09465a401c6036014104000110b8001103080040000d030b190781d07020500b15501c1100600c2c01c10019040c000d1074548400740c0185008246072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 132750062 1250 132748812 132748823
    0xd02030403080a0e0307021e040608030c0d0e0117040312091208070e0d08030903130b0d0b040614061605061e0a0606090e040309030629030a080a110a06050103 70
    0x10422080640000c002e0303800c1600c1510420601407440c10705a5688182c4071301070300c124031004004031f00850501101d19000d10207001403008542c1c1d200b4480d940d03008402d00028500901c0c511004080c841d50401c00a400140d58080b0b241030b400c6c40c41c8c2c10341c40b00600b0a40401001c0e00100c0c1c1c8c0034840e40110307800c01d442401c5851480f0407030325008201800240c280d40c200124000d6200c0c8540d20045032444454202094941d26200c0e1480c031403840c4036107507061107000f42c00c41000a0440b6002c2c043c0c2080c0c80c03046d10501590400700c0400007103039910f0046056440304640191050700f0906c0142c211185944884842c0c0846c0346c5070186405001c071110704003500c42900d102e0745246140400e5411440100040c41103c1c2052000340c141106402042192000c0ca40001e05240c850014940110341080040028030a03042146500b40243d42c100c81038505c00e8444030001d0704000401c40b020580103ea4103092100030441116003503070750a2070302c80600c105403110340442c1081c89007500070752054 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 132751312 1250 132750062 132750067
    0x30a090b070312090c0e281a0904080307020f0319030f1805100f090803011a120c04050a080c0901140103021b011407170601080a24180207050a0b1503030d02 69
    0x560001b206500060490381030f103803061704807148400044814101c14002040100780c012960325680c07040300c12422640c1e4040411414407041c040c12100a5029011079401d4a5504809850040c2c3c0c91103002c4803014107208080310400303502d200b64003004c1500194140441e46968149881c00b00d104a07000a560b690404d126002c2071b20454444c020304218404000d0123000030546840c0d41a000c144650044910900d1000042d82b2040e82141c3c861000b0b8003003580701e810441e00c423103683d4003c1e000c0c503406044592000301d00010001681c9a0641d00201240030980c200b5041c901c0c00c3c1100d030f405605068090010340c48100e0303601c560340705d0541c81600005404a221080800400f4040e051034203000e0310655202100d0011858541d0004080c01e104103980c079041d82100c000d201003600f12000c00c2c45024541c04280388000b842089400c8000010214100a1901000c921807078400a1036940424181380004043e07200e2a82d20600000c0c1c000c03a0303d00c4040110b401c60b84800444503990750300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 132752562 1250 132751312 132751319
    0x1030309031211060415150b070206030907032301060501050c0d11010b120c090105010804120509030a150b100201020a0203090120060705041d060109091e06080c040509030a090b070312090c 83
    0x1841094080040070070b47e416120b18020900c0c0181c411504041e00881000000a202c0c0c5c030200900d00080d80d1040c0200a10030303a1030b6021058948007590300d09a9400d001c80080c5a42c4503c0951340940c25440240000440d541c2c0162640106618130600c0365403640110700c07036079681c07444a040c00c10f0300c00b000d4290b150010040081c4081d0581003981407000520034000842c5041c440d00050820700e0420316512002400003a15140403040c0041844820040c00700c100500ba4000101070682a10114140c1200300740a070309034092040d071384d00141d00620048800d980718015221107140700301003100c1d450801c50700350b6080a004564201c00b049002070304111504500141d09038034104001030000c0c40c1804030009141c00828862001c00c503031100710369800941c1117844d41211071001c10040002958440001c2d0320350b00400b440510462030000003890551010080710708a100310303542c6015890400707140306902d8002250070340130004c1002419100c1c050602c1380c00310b82800744007240601c45c81c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 132753812 1250 132752562 132752603
    0xb091810020304030f050a030603020405010b0a0807020105060303340605010503100603050d120f4709100305010609020915071115070203030d020d060806010303090312110604 77
    0x58444103568040e1040040101007640640c12201031441460034540c0d070170090408402800c9107403c041d501c1481d03e000000c01410740c200a042c11401511001c0d040d03a83c0c51026401c031030080794400c1c1c140d007007044a0b244088042c43e800e02040c40c0ba12440440100c16440150440ca080c401100d071166100d0043c007203403030308000c001d03034422010800f80085811030340e590b61a2040c0751820320500c00000029030003881107030003001d421000c41c403040041d050100d074031101c421545150b101d031152224480d6000d500403c2c0031010201041100400208400c0f0140610314000410110101c0900a40440000c0c428010440144285078026032154102e004000508400c00f00803c030041d401c2220100140c800d00d11040300c03900071141e08101c401041c5080341e0074443c584000b51306020004031010700442a5020b001035483ca03900c00c020311a1a860f000380c0e00d61082c000074000c41d5918400708002650301040c0c0c1071b8007040d45480306541000e000050300d8154140d41c100c5461546e81c2c0c08416400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 132755062 1250 132753812 132753823
    0x102030f07110304060903120c150906060603060e060f120601080c010e060307021b0a1a12010b0901090b0f12041a1b040b07020307050a0e0a0b0d020f130b0918 70
    0x102c2d8014501d82850075601030b00c00307001480024110103d01d0450070115010b060b510100750b170000d5041510075080900d850003000d510000721081407401e500820380500c80d00c245c20650742803a400424544a079010045140c04440701076031300644006444603a00d00900c9040c0c000c0800700b00903e80800810000f500c807c5c2c02920981c040d2805104106075607a0004c0d1102240b00c0503a9031040d000d0040e4040ba0035802240c1041c0200c103503804c448a42803011000070702c84080d401d1110002781e6241c3e41450054494100714a0014100c5801440b007e00f86000804070f10400554a600d0f1030359000d09401184d10440f000e03034030207403081c040718545040c4040c4564481c01814404809004580c000f40483c01117020306199084045a1300c03013151400c121001c06008001c120803c03e66688071031902d0020304480c6100c689003001c962001a0600301c2c1c20711001c590081c442421060034070203002c00d20840c007030307100303212900c4140707c103141c0e1560b00425000f50590706c80c0380601ca460040962420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 132756312 1250 132755062 132755087
    0x6180a0f1a07021008040f05030309161d04030f09030c060309050c010306060f0f020307200a090b03030409021c090b06040c020f0309040c020f030f13140a05040c0c050102030f07 78
    0x5042020350010b0b80c1301c0520920515250514a40f1626142410b07100340300c06c1e85004005110010611000850001e80c1040790fa031103c01901308103031101403031105414800495400f0f0480c10300481d00180c0100e041800d101c0d00c624207829119078945503002800484d0380104040703507950081c0814414184440082c2400a0909012107868004000c00c0c2010703141a100420040c0e4022400b218402e10464204680000010a1112400401c0060b04464180c1c140c0702c2c3c882c4540010f0381c003a080c0a01400c0e0303a80180554182807510942401a601c09030080701803135100c10715200451158882c40407080e000302070803000c600d400d2007130004a4103191300d403d00303560000d0005400b0881c000f00b140c0254034240c03008602c0c3c0b2203d0b001070340f40610041e40c22445000118042078440c101e4406401c854a91090808165568445040804080480c40740d0005480a020300c0030f4205600401005c141c10300d017100340c21016442c0d072400c91300140e03250340b4000340540920811650101d41c4601c00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 132757562 1250 132756312 132756359
    0x30e040f050411060904090c080c030f0703030503060f01030906050f060901080a0b150109031a07140901051b030408160f09020f180f0604120611030702070506180a0f 73
    0x103a0400d9142d86490303000030f0704003510918000400070b442e83c507039070010b595055001c040705003182c0d21004910b84840502a120b4021310a1120f2803899000010b9442d0480b6050b45600780741d501c0b00004e0145004201c0302107814544c8920000b40000c1072445464441c0c01170b1111a461420003508200c1043d806a224440300c0d404541074202240801344c03c0b0390066040700e0304120340c0301414016100d035120341d400601180030082c00d0807030803442c0307801c13851007103070741d0342e2412091401d80c001600d05005071104180080c0040c440111060a440c074484903104040007244c1c00c056654441c03d240000c20400c41b510043c0c1d2400070801c0820001c615806081818019820b0010b909210886809031640b0f55204516180c00000b6549401a414502c1e207006807101e980c0d1910380c0c1d001da041001e5640100d40d22460024103254078111070065034000e02641d405010010b140c002082140d81040e4410025505001c008001c01d66a03440030800800941105a80191924182002c1c04801c0c03210203030f0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 132758812 1250 132757562 132757571
    0x11010f050405150d0e0304060c05010b09010e01031b15030605040b04020315060313061a010f0801080d11030409020d0b0a0803070c090f02120f180a0206030a0b010c0f030e040f 77
    0x81c3d640b00d507468041070400c100c010707407a14110010080501203a40b5400700b54040050081401c1e03506c0495904224010030003400f101d0104818840504024400c44c000000a0001480020450a903c054840d2018031203c51a51034140261100003600380482c0402e0f47e98100b0800f40c1018050810001012a002c605520348400c84064451007000c505205040000c00503440b403052000074440c03190050303000c209107249841c0c80e5840729160004580817442c03a18800790b545201d44801410b80b800c500c0a0720b4070405030b800c203a9000c0c0031882c1d07250aa00042c0008102030b085440545010648c920700402c030503100105014607078904d07400c121a1504108041070200344085685411030f100d50310001503051000030340d80d000740501c620302c6c010603100c0001e100001802d2601240a19060b01102076000302001003203070b40d00d00e005402504800d0600c001036070424a035010010a5806050040c400080c5a860031420f5400010403800304000c0005006142043c0c032404244215044c020807 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 132760062 1250 132758812 132758819
    0xd0209010806060a06090e1305030f0a02160909030c02010e0a090905070e0106300b031006031103031e0903010608060a0621020607060504050c040207060603021005031303080411090411010f0504 85
    0xa0490130007010044001d1809001030100f04042048031400c1c4bc032a00650780316814150001e40700d610790341c0303003030702c4080d400001040e044c1e241c2c45040003031075140d1500420004150300666000024402680d444000c200000510050901134010310a1064014040300d82c00c0c4410720810301810f0f0419030801c101480c12000f04170301e0591408503105000700d6a428080ca00040c0d90240a10200c4c19415004032444030024102a400000c2030740c1c82000d901c01903613200e40900d03681c0d0182015420058590190250003070465030020103c5500240000c1382d45522001e2a030728203441904c80705c40e0955503400c20000c80c0c0b403104070260703d000513042e505503040301900020b015000b200d901600712540c80011604001c800c011850309000040c00542d01d82d120f50078000300a021038401a4040c9800f121080d41803031040d8112403107041601d03011901c046142d201210140381c0203100715050840c04849800c5580c40b9892207110b144501c2c83d15038600d08500c0010824040c11146e081401024041032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 132761312 1250 132760062 132760079
    0x3050f250b070606150c05011a0105040302120f010203010e0906090a0803012d08010c090f030305031b091c020f0d020109060f030b060406020703051b130207020d0209010806060a0609 80
    0x3041161918111651104400c1c205030b00100603680c801045000c6415030010f5a54100484420780c4e0300803c0200040c09625003100c0072030786e00d0801e150000b60100300034001842c1540141036100c2081086940c0c8a1403816002d0880c1d000f0b03085005140854070410100c0030007007000c1544200b005016005204050b5a8180940418044c28801c10281340031046802c403800c0d800c1c1c2c10750a0340c03002d00340216500c0c17180034002c10044071540c00055445102103810500125100103c07541170342d8403861a521303185e4155100e00021400241d14804002c08580c80d80e41029519144807180c1031080f841c03d09d841080b240402c045011070080b00f40c0e034000d80140c1e8104040c80c044a0703281c10942c16914104104074024034603040d10583c40f940c003040105016500044000c182c0344900112124400c01002403001c5004440d40c449e4401038002000040780c4071038014080251000e000300b11840601e50015140b06401d0300030810725842138040100d00d00e0700d203880034014031803030038510709203030820300f02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 132762562 1250 132761312 132761383
    0x2a180c02070e070219110411031303030e03070602030106090504050115080c1b031603020105060a030c090b011205191802030a061109062110050105120a0f0603050f 72
    0x21201c001280c40c0008442d40d0090050b0710f40090301a2480407410141c0c5041c420b1b0070590303070456014a141c060134141c1d19040301d0469000c0c040d1800380b0102c2a510340d4045000c0c1101e03203504080c0703000a000020002d00140007940c080c00b000d07141d98007154188018071040350b005038040c52503c0c00c0e80f03d17049541034001c18a01c4d0440a8140300d41ea4442c9918001001c54142d800c00c0c4100d80310000d1428503d220310500040a81c1c483ea0080c4041d40b100d000b00204504280000740510702080020005003515074803507081802e043c140a080c3e18126007269085510071543c0083c1c110101c0010f00e21512580304807181e032107005582411071809a008203503200301b02d0390300402407540c98030b1040c030398020242902d000100061901d603a6031400301c079002c1440300c9201d0b071507441c01d10314000c1404141d4000c645003d8070011b80d550383c24a11207070386e102c1c030100001e08200541c1d42d54840c08515048640036007030140d0f005000510707240c404102c10501d0818508a0b540a03150198081e0403c16550401c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 132763812 1250 132762562 132762569
    0x60c030e040c05120c1e0d060e04031e0201060e07020a11010315050f0d0203030703020a0605010503030702090406021b030a020705180907121712091e0303060402072a180c0207 77
    0x1d0086660783c1c1d0302a40c02910640343c04c050594102200c0381a0410110007c0144545104003840b0b41a0354076070000c0c1c207241c140d8005003c0740b0070032000e420303035101140c02c014840c480703100203d80581c1c1c84400d082060f80c2078400c0d50058020200c20024407140700c2c0c0001d0a00c0e0300780780401c58000e185800d010001c03da80034030f601c00d1100ca90410141d540300c0404040540d00101600e680d0070301460301a6a0300590101140c2c0c0318100000003800d8513010040d41d00a98001d0001506903880356161002540400c0c1b150b11160740c18801c01450031800c0018020015140c0c00030f0500e241040c04000d442c0c080e103a1581070500a0303030104074000902140c4601121000c280741c0c10180820316000741d0214030325204414124020480f414a2540711082138015180c100c11385207842c6010402c900c0000f00582c14a00546c0104040b484904013130703008044a6010303421030b0007011412848480c04081410a60f180143e82d4081400440d1707181c840050000c02a220400c900b642c5003101a446849510 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 132765062 1250 132763812 132763837
    0x6090b0f2802130f1d0109090206070227010611010b0a0b07020d081b030d11070b06012003040b0a02070b1c0518030a03050103060b030f120f0f04060c030e040c05 71
    0x80c803d4000c03044482c0d04030141c918001da01da1511340b04c11443c0070980d503440c15032034400240d40000940704810b01c14100c1044d005049689040e225400703101e408aa49884860303001501c07241d82c0300689401151501034007803581c07000d041e0404681c1c50b5096840407801e0714401d443c0510b007001100301c208116803243c3d6040d11681c1080c986400c1c0b80302d89006800254243d001071400c645800e4801000410246030214020404840b07042c1011002c1d005001d4020130301c15a40022981c00e42c00b41c1c5d02800c8441c0e6512018141502c121541e9085800c5548420300940700400e04d2244543c042c0883c0c8060708840b8106030800c030065a071186420741d09181602d10303035034800204101244e450108152807c0303100440347e55003072041d002801813800744801d544076440c0145004140c035000c0303450b80b0310317040007401232000b07903100780381c80107164480d100d02c4a40384010845c00c0052170141c0040d00c0100755644441d5611481402d000d0600d0001c000c032184110718200d49045099000350075036076101c000a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 132766312 1250 132765062 132765067
    0x10b0306131a01030309032d0605060a080a0b01030209060603070c030509031009030f0305010504051509060f0301060f060801060503011d0621010c0e06040807180906090b0f2802 78
    0x10b0401948040809494241c4440740c50000310034160410012021684241d091001010421949040e0b03020715603d2940c0c8012252210404540d0310f80009030000d1008000c5404150381d800703054900040c9900448440000074010000c0d441c01c0d84071150702000640306103103149850800105240c0601500500f4450045440d00041d14200202e200c3e07900902410072001000781006071085e4000e02100000909180c008505030820b40182c40c021100322122686c0f10400108001413014000e0030b071600710a03641d00c001c0f06503809008110083c82131180b0300d40143d050000080c20010141c100070103000003040100000d201c07041d801d699403040140720110b04d07103c000014200110800c444207620742080d04036059950f040d44500c01c119215107900c16860501c505200560040d803140480c02d07000300300d00b00700c0041111401144081d48250025151100355a09030458860f500290745610010b01004241da00a03441c4580018100030b10008042c0d401c000e0a18058404021900042c2c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 132767562 1250 132766312 132766351
    0x201e12010b0f060c28050c1f05180603250c0c05010e0f030d0908070602070b0702010f1e02070315020309120c0106240e0a0810110c2d010b0306 63
    0x2e11085d4501c811562045054051030350040e21401034011040c1c80c24052899099064a80080c05050544d0040c282da104514a40002d80351500107510b11100715421460081866985030700851040c6681070b0880070382c0704490140400200900184414030103082d00701c50210317214400303034011581e091130544d00c03240d52140400c1d00ba4403003050098040c400d00307072a01c00e619001402481542c01d1b49044074589595250202d983c1d0f503851181400c1c4002c2007102d000554803d8181140ca1600d80c20300320500d40b079044400c5120181c1920200050308501d0040c02000661045c1e0300355087d81d00015415801c0210303c00740c40b20241481c0800803a40040e03404442403080d0040381c0104494441c1800580d100c401e08030720013600c400c8800c0010b68603e40d402051800307858460903603658a006004206401c040500180000c03000d003008124148100d0b0406402041001107030f070700c000710300003a40d54040c0e04071019004401c2034403140d9042c10400e080a40f000680b95a000791490f12440c5200813 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 132768812 1250 132767562 132767587
    0x8040302040504060c0f410a0507030807090b0a0815120106030b0109050f0a0b01020c060a030f0e0f03090609240a0f020601060804201e12010b0f06 65
    0x155400290003600b03080400060003142da110000d10f0340c41c5e13221801ca5008202c0125408481805460512445c0c18904100144100204040e941084044220380d40d1091070010480c1c12040c02480010030008020003010392008182d0703004115418200d200604042c071011a90044030f284100700120000010b04e000303110302d5415074594001e8562051f035800c400c4650701800c0d01c1d00081c0c0300c220140d000013078030002901c1791a01c43c0700e26500c1c4002a856921070706014182c100c100c2811842001c14569407661258000c0c0703c5601d89803000a05610f102c10b0440a03580034020000c0782e504107000e11200210003208451407814120b81c081d655650a500142254040416226040143c14030040c0d010b001c5034010802c0d0585525000040507501504a80d201003d0249400150f001808140011b1103881b03020a14108a013640302a07001000c04106440c4459230004480f05150400d8401c40c1850701d029800c2c006150000d101b002c4500c0b0100f00d013440313100031160103820000340300c941004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 132770062 1250 132768812 132768817
    0x70302070f0f0311090705070212030d051e0702010b0a06050a0306120303020318240601030207141b0402040509010b071b0801020a0e010f0c140f0609010929060d08 72
    0x707405000e00408036190044207140610900007280c000d078640304101542e01d400d8a03010310521259440c0e40c900106030b400d02910240030711180f07040d440280030b03800808905001d100d1044071000c41060385014100c103d0b1080140192510b01903915002c80f41e1060f45841e09840c05892a9043c12555003903101b4045008052139880001c0d04031009410328105a0f05030000d500580c06601c428450a05000486840e010360200b110540c0d102110200200c99403404840c2c0d21034014103006003081616218100b84061411040f880b64201c440500c00e00321444402c510b89030300a580840c185401c0001043c0f040b181800344003503500000c201d1004008020111400c901c4180c3c240700c194a5075400102d001c0d4000c5040700c40440c01c44558a24654840e00d090313990300306665540b0500001c2c40e25807001800703a42c0000320710b90007080d4164203030030410416103000c0d44451000080501da541405940d088903074904551003500c8901c0201200e0003600e10a401040032a00b0100014091030014a2803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 132771312 1250 132770062 132770069
    0x50c07050109080703090b2b020c01020318100608030d0504022403010e0a09020303090f1314100e070507240c0809010c0203091003050901060503060c040f0806130807030207 76
    0x29800c1030080410400e40fa0050820f49110307460b919240381c0c40d107448022a01602d8030201e0083c03030017095507410410611880f021040a6040113103408041c171040c609a0b4400c07a2158094000b459003802000000c00502450302d5200c001080b0b014207000c54151070f44110360f0b2984803240c4030000310b0250f580d021510f6110b8107040c1d8050841c01da81c00340211054009120b000214034000340055101d21700c6010700c46403a54014050751900c0f01540422a08021036210203030884030103440700c5082c15030b5200318502e000145941c50894a0102500c81d4110740a400981e9088120001d00801b290071006680300d41d6841480e0030242c0e03281e8a06841902d80311005801240d081001480701181c000310310724001d4840d403009002c841540301c6c0607039a0b807142030043c5810001d00182c2004d4184aa84980d4001c0042d90012038900c0d0395030000303482c200040d03480701d02d035000c006002c00c004180002401c0c01003040f503025081500c0c0000b0b41c4181e040443c0c7c8007900c184400110601054824040d46019 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 132772562 1250 132771312 132771323
    0x71e09052212030b0d030e04090f08030a140603030405150c030c011802030d14160c03060207060509070f030f0308070201150620010204030818012d030c1b06050c07 72
    0x200c0d812424602461598101480086480d1081c0380c004c40c200220f841170b000790180c9480103c14221400e00c00289079070320007500e0280740001c040e8000352104004600450700f85101140045660f41044505a406880d00c1d110b030f8000c100400464807003629400c0041d51516000b07844078081d1030954110300c030701040e00300a5442c0c818480c4440445980d443c241d14029002c681d00c00d4003e1030243ca02c1020505a80b020704030034440640815010810800e03036601c03401c0041822652a960700041c0d800156085840301d480710100b154216082240100910555020540080c91070325055409003c070b090180401c01d0b00d03170000e10124001d400208000080003044035001d59900d800030310402c803c4a600000500c01240b48490355414002e46040d6904031030a80e00c0d0440c140d13020614404090203440c14001c05400c901c1000e90030341c0d25401e0100c8400c048070540001c002c8000d00301c4059843c1c1c481440703919014110150b401c00115a20075a21040000341511200d03003425040c018070500610 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 132773812 1250 132772562 132772621
    0x5071506060c1403120a020a050c0a050a03032d020a0521240f06090f10030e010b0a120f051905011d0106052d1203070203071e0905 58
    0x41d110703440041820740c180940c02e440303054108800d4598480c4202c49032203603520450408142c80001941c020004140e142c200300d0b10b0009040800e07800c1400590301030355213400a070313000b105140d00350140c2403000600c0c1d101c05c0c1e0503078800301c030411071a0310441003101f0055010601006c4c1a001c0e104441d640310014440c010520071030003040e4201c1104556006192008125900d0000700c909021945800018a41c04800481c0418000150091f031243d50b80300000c42c0c10ba005a840c2c88080c83c02d0f800c003a94002c40d040104110280c25595200412402000c00400c02c00c0002c0030103402d800e51503807150b84510321a400c6d003041d41c944101441318001017a8503035541000c03c44154010310a0880440c0440d144040b0911158201c0300721b03101e81500840030301140400d90281500f01991018643c490041c035240610104515a680c4043e544450f80000f40180030752a04201060051407070015952100d0311003030220030054828400e180e4004e888402182c1c15050130800c4a1390320044020030f14 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 132775062 1250 132773812 132773819
    0xb0a05130308030a0507020c010203031b1e0324060301031e0507030c120c0e013606180506031f0b030a05010f091415011502100c050901090e010e0705071506 69
    0x13002004c0c15038003040548a04624000994004400c2e40e00c2032891740340d101c0c0392240806407100d21b540415060980e68811041e01c640c01000c10f000b660144000074244030b00301742000041c59081c5800040c0703500c1100b040c03004200252407003540b40d2543e0003641c00d00f00301c06660303d0500e24004540c1c10003800101440004900381c40c800000714152409609024102580c420300611303161403c1c0690b82c03548907590103410707255401c440075003a5940464101d90900d13804142c0c0038100e0f400341e0050580824841914121445d0324001c2c150000c8080700942881041c02c1001400760f0b0442030717030300f20b45500c0d05c4c2d0030006960140710888846420200901501d010652850000c103401f0b0300031103ca400034a8401d6038410000342444038601005400c850a03402e281e02c0224050301d6609030000c40c8070303510b076542c400075050269000c3d025403a20b90f0740c0c455906074009094000c1540044501c003600e040100300c0c00d0741103010690481843d01b0107036a241c1540c00c01038000c0500c0e10488011904144000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 132776312 1250 132775062 132775081
    0x106030e191511030108151f06080609070f120b060d02040b040f120b040209180f0a150c022802090405070305150403080403031a03011104080d0203040b0a0513030803 73
    0x46502070340003c218a03c030b241111100d80c0401c0c0901002c640c030400035840c40c407070384812181d00290805485000502540321b03102050280f03400410002d00014240aa2401c1032410b1640000ac2800c00c1050b04041c130700000d2140207465030307241400f512805240d00700d44801040719040f80346180150340d9a910349081100c15070052044c4410408040e10000c3d40c40092050301c4c41469110720711b00607640f00c640800c081d04001031300308004066002d14a8030140c0e01080460b0101000d0740180984030100d0400080910584003c2c5628908021440d5140342d07021032052900d98014004010904101440107110000b0940003500b180700c1005000520000040c0e0304200c0703202d00d00301e41030101050740c90112a602680c005000c16105804280064026044100e80d101030070010320203a0724080002e0300750340750004842e60004001a09000501c024896110b120465000030340c9054540754180382d146c404d0900120821a0124002d015601020500d0000b15040300c0c0c055101c0c1884101e6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 132777562 1250 132776312 132776333
    0x201092102100503040203030a030f0f061203020c0a0609060c0501021201030f050d030207021f17070306050f0a080d080903040503010c090617060a14010318030807180e0106030e19 79
    0x264400d000054001100b244140c0480b48102d44c050051130070000c40c00c000740c02a10308944440c080340c0c0c032252a52901c8845125074401841b49100c115990410707400d0281c2810341c880000c3c0d0142109040c01d019958010070035600b02c50441c030b4150204911803c043d0700a0007982c08400c002c0c0c0e1030100000a028a88423951101402507040d10f01103504100c0a5040707125812000390400102d0040400d121050030a0751450340d40c5d030410348500300102e42290707820a13003150030801103581d07890244441d0034800540b1858a00c142c0d507004030a8100f01c0365035a240303440400716081005940000c0d001d10828001ea03002024080e0003484a4681840701034006a5207001d020b001450580706914605542d00069000f4807000d00140c0003d42032040f04846286d42c0708850303060686902d14030020091110000d031605000390f452005c2400c042100400d036800781d01480030040720f13034401405041e0745d0750784481c110348580c200007980500c060111810700402c000207240d440c0c4c2c2c803c0000144510641c9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 132778812 1250 132777562 132777629
    0xd0806090f09071202031009031d01020609060c070c03080a050d0f02090a05060d06030c0f060201180b1611030c01060f051801030206180303031006030c050703020a030c020109 77
    0x18001020394909141c0308106004035600050380d0b2148404021a070483e00005000b07a0018081e262810410b00c02c2006451500b80c04400117030540780c040100301c125140018046900344007030901d906120114a83d02e040217801c98450400010354003041050207201c002c010b40d8410001511070028000103845900f10b091081c80580c1840e940251481d4544221010490b004000d108094140b205010551700041c2d403081100c0c0d1b840e00e000c00480c1d6000c8044d4010303c840c224281405081c010020300303507038001c11001c40d40e00c04070308800c000a41110410313500c0103060202c00c5480003280d1084844940c981d845081c6c0340030005400001c2131040d0021015a8180700340e8001060342d0b20180592441c80301c01b82017000600304014001450400c004148960010600d0a0005d49002c002810f650054030280b060500d411420081ca03905030240d2510081d5a0820074100380ca5510040c0d210208400010708000814001c04216801940801d0151030003035030a2110030740c0350304460622600e007036 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 132780062 1250 132778812 132778819
    0x3020601050d020d120e06040f090b060703171e04030206060405060f010203040303080606040f150e0411040e0a0914010c02060105100e0603040309030b040b0105040b0a06140711030d0806 82
    0x14000301d654203000030200041030b4054510100394601762504c200c2e03031400b02601010004d80a29440b602d03568000508080c060341c0388040d0031350713280c003072100704448030400c066000c1d98040c003850700860303000126012507145603a0003c000381c0d14604482035002e140c117203010091000c241800141a0b0026080b886150213840c1080aa20384c481040280c80d49405201e0060344200401d000003403040d00e5030342e04002d0240c240c0e070805403145208061442c00b41c01c050310803c80c44c20507a64150f48040b52041214040e078080100030301103021443c0b00d2080f4015a10580c0750a408240e00702819030050350300a412080d90136044144013007039406490091407000042c42541c00100e06031410a14040110140d6100c28114a141c1c00c148021908014003d030203001c20a500000407650705868248118801d5801902541c1080f0070030080700c0c00300780124041c1104007800d12240741c100f9400364020113440c00e41500c0b08001c1c604001141d18035440303960580a2890340e1401260050b417858001d64044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 132781312 1250 132780062 132780073
    0x1140a0b010309050606040903020a0b041b230423090d0906022a0a030f03030c26010504050a020705012307020604050703080a030e03030f0a0e03040f050f0609090705070302 76
    0x200d004405894024001030126003100340800c1a519081e80992410b92190055034100f03107040e21003400c1d50004803000c0c0c4040c5c8103881c001070f113120407030761000240010b810300700c2803c140d2442c61082011040030301401a0380d6201e0007245030301210022110101c4107a068070140c0340155500b900c0724091003180020412406020405074004601d810040c80d002903004e0010240f40c102a01c0d07040d0800c1d83d16003280e4076030400310204412a2080078000c4c041d0f2400304001d946184010001502c40440114102603408540325401418201c241120012103010a840d211000301c0303002440b95242c024507d40c6000305820090310340c5175000c80d668400302030031486542c4403d0103130303103a072403c50f0010001e4008840c14800205c1311400f5004807134043c80c0006421100c0d0500c549107500540f144060060000d00b0003102e4140c900600c1c041c0000f50340071b142400d2505085001850b00c5000b282c0c4180e600f06001041512200103482414600408849031810b01e10405009a03011840550040c000c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 132782562 1250 132781312 132781331
    0xa2915040501080a0209040204170312010f150f0306051e091315020708092805041a1509030d0c061107030e040b040905061e0114011b0309030501140a 66
    0x898199011104182c40c1c0322040d0303072501001340c029030104114650180c1d09000104a0107000325a04c0580300e0b03060010f50341d074040071458203140b0105a02c07442d0341c5c42c1c0885041c090083c0f02c4c3d03c018003003e55070400401d00409950242c0162007a500465000030101c17006294401900c4000c585030710701900c030b050b84e640b40c04408114249032198090540038003910501c142c1e0006900500c40d4234002c028003030928410500040701c40100d40c007900028160300341a4201140354495185c000c0c5401c5500704010f004407020100010b0111407203c0c410004812034a144204440032100c4a00c402402e072019148040d00140a42110020940322185841c814000300d007810782c121150759416071215001410884100400361a81051403038109494007086000100200003007400750012094044c071301e00c104000b00501c044140d010740d002c070b105141d08407401d03608000406055a59600700c0f0320380d40380f42d080948811400342e01c01843c5601e0b00c10304c01d44003d000d65480d4024400082c041c00030309003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 132783812 1250 132782562 132782599
    0x1603030501050d0302190501021e03010e06040c0f11030c030a110d0207030c030204020315040504050601060f020303040c17120c0c0114090f04020c0a081207020d08071202030a29 78
    0x1003c04006001d41c0c05480010003103104103071080e004922980025140c03083c4500034546609041074490350707450b0f0220050100200d000c42c4950b020130240c4042000c022071400c000d00f43d0900012410a001d40d55100e00e00c454001e0013200c52100b01c0b4400ca903954110752a00800c641c0d0014030b00c40c0c0300d000d10340f110480341d0300c0403450000300c03030f085601c2d4651281141c003003000079172001e801c844140300b4186034440207483d14040c80c0d225034043d101802c042d41c54910040d1601801c2c3e1801d0045400c01c0003003100107101c00c031658007500c02480304108103551601d40c071460003903020130780a03804101081e00041a0350014080342c0078102a60b0380c1c141100828145109030040300c0c40c02c1c2d8002c0c0080051340c01420b280d40036000a41d5000b08840780082180c80d00030b682c0d4480141c800364091401c1c2046043e94042010410485043c0b0b0100c4c540d14155170020414050001c2038100c1c2500000410144030ba40d4200740344940a0410b000f0521002030a02c4c005100c010242030b004450081144c2c01081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 132785062 1250 132783812 132783829
    0x70306080613330903090605090307170a02060d0603050c0925021c0203040504050f0601081914070c0b0a02180105090a080d05030906060406030818040b06160303050105 74
    0x2400107102e0160140e55281c0b810102024400c512070741e80110b40c00260102d0120440d81d21160010000d13100542c0d040c02008102103030001c409001c41040036041c1504d0003d50b150486040184102959002c03114560405220350750180d4000701c00b144508100c0003d600c0715040f28428800c58004103e007605110745040c04480841d4044075400100d40c01c070101c407401a504140c107105072a020044072040070700b440c082000300c00040c0d001080900241c1071078896981c000d50003a040304441e103401c0c00028030707440e0010032040d100c0030f8041002c440d05845402c00300c07507500d106040300d4503490720b46c400070080380742a03006446508a140215030f90400ca40308032845944124400c400c0069454015203031944a914202d41000b20400000340700c410500506092601170b0382e910340d60f4100000ca062504c00054010352155117000800c200060b503140403150844c10302e1089464034450980018000c000305066103401440005210810075500d0008808103442510104242d90300c0d442408402d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 132786312 1250 132785062 132785071
    0x9100b09040201080403090803030a0605190b030c070c090f0c08150906190e090a020a0806070e040b04090c0b03090f011b031d01020c0c010f0c02091503030408150703060806 76
    0x140c80c940454059403180030000e500c0f0340642094400e0564841003186154011030b41c0d00b42d0176555040c14001c03031070241d00b6181502c99504141414501300178112801d07100c0509201d80c0c4410001d0490100300300b42038480010305807003004000a05942d8404c0014051410081b00041c407440d001841d103ca1811603540100c101030401c1d02680c0d030741c0c000d000e00301902081080d0440d4800c60001102c0300046045480f42c0000c502030300d034901451041c003502d9119038110881c02e4006008200035258810424406018211030204200d032068004c10020041c01c0342c003826a04e94408089a40380808c4011401014035000311440d04c01e18a05560890300446140700b00003800d4403107020a144207402c080d464400d194a00341841d80e480a07040d08a070300114121890790041200100c55603004185500120b015080200c8800003d900003820500e00412003049400810000c0c400c3d41c50820030344000d01141c2c1c0446401403122040c1e50713400d580c00c888800c00642043c002280e90400460303c1c5004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 132787562 1250 132786312 132786319
    0x1b160f0519060e060d0f230f0703110d0e0109031103040501050304060908190c050d0f0804030f020709110c010c1e2706050c010b010207060509040506030307080f0309100b 75
    0x41608140b0111042548243c0c1c10798441d1050000040e10b807502e1051210b00407901d440010a102070f18070321520460400c0b0714100503000b2100f00200900866581a400f10380341c500003075042410010803e2a0103540d0450300781c01e1a0a004c1082d005056001080d69802900c64046808802d00b000d940c030301c12070040a00051042c030126000a410380c0041a100340315074403c0742480c0d0001031002c829103024518000140f2a020701d0010711409000303448245c0b94174039050403a9488010f02821400010700000d08200d1071700340e4408018402e00c03100b0b000d0076020340d05109030710000460b03030f00340d0304900c1204601c0d51800d07a40a02481c0203862240103008000207142d105440c004050324882c1310b40318006001c503122041c0e15206064068028050076041e1280780d19030b101c003200d0900311096403030200e0642d40088010300501c0d03041002e079819144100e4011840c1d544210203c0e055001c3c008001704a000041120105d40700d001000e144611030303103400c40b442c0c000e2001308001030703039280d1403020341 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 132788812 1250 132787562 132787609
    0x90105070f0f1407090c020312010512011509020d0e06040b040b0a0209060313060c230a030b1504030317010b0f070218070f09060c171b160f05 63
    0x40e10318580c01d240500a42420718000e0300ca468011040300f020140c1e00181c1c1202109102d01000c0e4803848080700f050b03200a40c1040c41c0b00c580d03081305a01c1030080c4ca100719001904000e51040c00d4004150b00e4a21102c0c03224543c0e600d0350444007941000400c241224101407034481203c00008005118075046880c805d81c6132619169881c040201a11490030160200076603102621214021401008544280c12000c0d49505240b821503900420180402811084402088060f0794140511904031044c445d510340325100160300030084940003076000880e446181d0120f82444028104980c001d48130440100407003007141140da04240240c50030740c007042c8040c02e0119000d1003c0d1002c0e510241c42c484d031032440d4004e80041d01a0440d46040002c02d503045264001e0b5001858100800c03843c204038004101c10b942d00119081c0020250300c00d100c0100341c1c1c004141d800540007803000c941000b503542c6444e0a55841090a0050080d9507075100c800c81e0020b0f072410041003921800c20075240d01d00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 132790062 1250 132788812 132788827
    0x90c06021002130e06060f030f0f0604052401021911030105180703170c01050f190204060503040206030a110c06100b0405012c0a080f010f0c09060c0302071203050310050402090105 79
    0x480c10b1601821702ea07003080c0203100d01c20f131a20710000194041c64291169000f02e2034000c881101184000305000d0041d03007407105001e01e481701d200118035094892016401d03480c0c6107400403480c19407003e804c3c19072125100d90403030038400702c8800351b40c82203420b038003d200580e1840000d2a2080f0306540d078202c071b9485000200302240c7c400304240000c07207421440c83c0c5401c101c0500282522020360301400082080000e00100034a40d550081103000072901c1542840d28101c1c003d049800b004002a000d114000006136810745070b94800c03260705944012280e00c400d2448400727a80c40c6400c68091040d0401e4000101752440720a0580c1c04540c0305075605c3c0c8100c10007400d05080c5500c2c801100c05072121b5203004045582d110440c50b070151031a80300406c90903410180c49820341c1e50301200c080e81300703107800f550390101640a440102030b40e001d81480e1148011a11b800ca25107251070f03218240c3e00c0c0302000c10208041c0e00c2002076029807121400a10100c2e22041040700724813501d420180450001c11010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 132791312 1250 132790062 132790079
    0x40b19030b06240d061a0307030c140d0504020402090301110a03061e06051803120904110304020108011703070501020f0c010e15012105010606020706020d0504050d02090405010b04090c0602100213 86
    0x281603007591000c0c0855101e03591034886c8084a100c0051140c00c0c81d0120812011a51601c64100350003680e140c10441c103110307041e800c1020700c1441e581d19081526000001c1c159100d039012111588800380c000c000003040382007035017840e800c90b61030f110000741031140c00030383c3ca034000d50301454040460b041006507925001058a05500003c80500320340a5501031080c266030074000e0b00031a00802d158250783e050b18504100807141e0310f0420b000034503814030a010152343d01101c10307030541d0b5000c0459141c0b0f1244604041c518042c03a18002c20542c000150050441e0b640400b41c5140ca501c90000d0182680e02e5040b03a4a414156440aa2540003280100113607a03c0040d0061400100e17120031900d030119844143c2580c002c0e40204015902c10f90301003040545c10040d07950303111201d03c4c03c5c0d410305080400046000013200b00107482003a190010406024007988405206200140208469800c6141610904449119a4000d170040b00211090562180200d6450002c80d10340c0c010010300b0061b00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 132792562 1250 132791312 132791317
    0x1d0601050901110c03010606020c01090b1207050f0f030408091c0f02040b010c02060313050613051f060e09160512030301050918060703020c1c1d040b19030b0624 71
    0x1011038420040344c40302d991002c4c031a144c003800c002d034094a82d411201e0005082a00158800e240c1044200302c058003516140ca20b194010255290060f6a0503041444285034000c0d4540e82d8064038000061100700220b00b1300800141c00e00b41c540300200400100d030b6000780044c40e00064440084138514200501d46940000d40e60181410041c0c010002600400c2c42c81e04112440b500d00c1845d05000070a02008210315540842c255107001c42da9601035a596803a1000502c4090182c84d0b2280c007844501c41580011f406070400300c0140009180c8104103c1d60341d40b03101107110101c28440310104441c20300c90000d04001e40c000d40114610f900e824280000184010b082480e0550200b0401180903004d00109008140075540941c951031003003600c0f802d145000c2000c1f204a000f446440b04000d80128524070503000c035610345011841000045406040300e47c020540c0b1800b10150010a01400b20001050700c1c041d40c007450f1103aa600707060011068241444503c81d4841c82010b001201c4020700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 132793812 1250 132792562 132792587
    0xc020d060213030602090a1512052701020a18050604120206040308070b09070b071a13050106081005010f030206041809020a03200109210809030a030203041d0601050901 74
    0x14585000c50b42811058821900111105500010340e00a14545551007801030004e0202000130460341d0070000c0c0480040d00920144142c0703c0d40010b00390398400ca10b01240e144829807038084081c03024010350007503002d2007420001c80c122901c100071444100c43c3c0b40050390000b070043c5242c40d04118000e030a11009003402c0340d201804210200c00604104042d0881500c03900e800913590070030284a03802c00302190015400314000b0b020031004600100c1c00000041c240002401c1e0765140c0c116982c0b03400c0c44101c6c0c064615800e101000603d49000604214143c8200b203041026903202d4021000082541c030000c2e5000c141800144501c0d145002800014181080f0015400c000b0394045000f66456034800e840001c0110807000c80c1e40a15600d105000c0c0091030115002806c08000b403130114464154000c550301e08141c00d4042040000850300740c0d00c8028201c0d42008107916009649038001d004024042c60b090708a8040c0c01a0109003500a9205845283c20070701c000d401110b071040d00c4070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 132795062 1250 132793812 132793823
    0x100902060c100902030f0316030c02010215070801150903050d030c02210403060b03030a02070e0c07051038060304060b060a0306140a080a0b070c050706030603060b040c0c020d 77
    0x20035450007401c100000241840700303650106400300300d40105420515528003d89082d001006004071028541000300e80ea15814100740c000c00c0b0316070004030f1601d0103491031081100b500c9000d1004558121604a040743c44004000f000c914018030100c3d03035010341d4800102554403032401e4002541c0a50000c42c41c0b0240d9104541e4030720200e010f0503045c2c2c8485d198195800000181c180280702e0035010300d80720703840184d0042d490b0400110000395a41d1040c03203140c043c490380c20301090301641d080c01156450b50b040412a105c20799541a007200410400126480c20700800262502035444004058940d07204104070344c62201e5481d0034400f965100038401c032441d95079099420200d82d00d00001d03210f550f209950010b945420314180b0412986207081c0c00380301d003500d07800c101301104c400a81c06001d40d030300c0754018510781c8424000313807891010080d0040ca54040c3d2000840c00075410351080085034014501440440301d1070081c4001c1302c0c410100d0400240000d592000541000105201c0452041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 132796312 1250 132795062 132795067
    0x509040f15030804061b02210708012c0607050703030507050f07050c0f0109081905030705010e0a11010507030f110a060510050414011d04080904110d050f0910090206 73
    0x180340c201261001d50300216441800072a090010f0350340900c400e040741c401081c100d8a6044a41c0000d2850107190560b00c466410030071816590200a00c0301400800407400288042c00b90f50310fa0301990070f0b040c0d65004c180d030700b2411502502d0700c0000d1124055170107031b2a80e41c40c0907015202107015020040851080c42410017980407403002460003488054001ea01400f2810104000c1040342200c401c2001e04111401805000381000842c0d0075080308241c02c00c180d072010207803130074030300b18050702001a106500c0c00c140c100795001c010441420440c85245032888400000e0015280b901481030003070b001600b15800c180505006e160308010713081015044480c3c4501a60b9241c0035240100c400009002c3d26030b400700014100380c007910b0029101004100203e6040105003520309c140c0c1900c0140c2002038074003113801d06c0703800000c56440c224080c00078810142d00b0b560386a00d5900c131140c1c18500030300d8140040e50204540c04e482c0c1c040c1c280000900b421750f48054044001e0200300b0400d03640500d04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 132797562 1250 132796312 132796331
    0x40b1e060711030d12050f09030d09020a030219030c06111e0a0b07030b03070503070b03060906120a03020601140f030a151e061e060f2a030c020a090c0509040f 70
    0x800c130044050a40f540e83c0c080c000c48100b103000a4410103044000164559810f010407240040709441c40d171151250000b80c544803500000301c40c2415030784081d4000140d41d0b01c1100d200c00e1007442c6000d5a01441210b82c60b6599074001703d51140201c01c0710291034004898042024440c1908a080100c4c0c04040300c49800745d41d211911219425078514022070f0b40d4080950407820203020b000d000706030480c09440c2480c9800c6000c0aa840f008040600c036014040004a0036500c4040d18900d40d0100c0c0300300d0324018510300d0043d64841082c0030700a00008800c13280005071801803004540307540043e010701090b000f40d6944c0d20110000c4040b503000b15854040900d041d0000c00c2100710765400e2290040740c03451902034840c40c0080d84459407000324500102c14043c11341c01c500c50f00c0003c5100e21f445074a03000302d400a25101b8120b82003400ea4225003841c010309155204244482581c02103e410345903030781e00d510940171218004d0308040031900500407000c0601c0e213a07020707047c0390914250120340c5c000c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 132798812 1250 132797562 132797569
    0x7020d0317070309120f090b0903280204050a020c0a021e1806090702010203010602150601021005010e070806061303140a060615140306010516020a0504020f09040b1e060711 76
    0x2011a100d02c002a0b80b2204a07080c000c4222200a007007000341045081303810401030040c800007080c085d6900d000c40005a20155403010400421070015444d4500d4801900706540c2d03c3e0710280e444264070450510740400c8604425100300c0d08100100d200800d2410029070030701000c214100b07182005910103c0d452175107a25041d180000000000c1c459030700d85d2a18108002c640d00000d0f0508045a10500050000c0ca4000500e407422811000b28021140c0da40030040b458405100c4103282000d051200000340e04400c254654000c0e90030351a285400c0d59080103028060140041c0d030200040d0000e410408103210300c10000d0211001401c0c0c8044518a466800c217803400703584a0412000b80205440701a82d100319510720310034803000d10707619504101c03000902d18059040f070354003001a296401011076544a41406c011300002d030066450f804a4601c480c11380d040590101c0c01907040c1242c02001e0701d0f04040d45aaa03000001800130f028040c101440481d801c100000c8440c1501c03507038100c00554 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 132800062 1250 132798812 132798857
    0x20a080309040515011b0804030614180a0b0106180503010204170d02071a0906071505160507020306070309050f010f1d06060109060f051209010603060b09010b07020d03 74
    0x18214009696a030041d00c244021910700a022044034a42000c0034149070713034010541405013540b820360751111902030411784c00300d21407680010714640c0f91a07185612040494202c0e8401c0d50030103003204c0045140c5080c030352141c4204600800b10700714100188003175405000d12030800c00d0f050402c3e03284c094403900404c0c2280c0c480e4002c03040204007204110f0204000f00000382007062144041c04649180a01c40900816602500c041940b030106288400b61511815207062a802c04460071540d8819848880244401e8a4041c980321140d1030402040b4021811076031003541c007400505142e80ea40700100e000349400002140c041c0507090760544411030134001d448480c200c1d000001010510340b1150b1500c9110a041200c0c9500302c8000c106592303030440140703012180941441c1100d8030f603040b001c83e41489103e4161040c4204003082c090b039200150704c40c41c107480c422441004841c000c1c808000c10f41300244503020358400d0400c110760050414800280c0001d01c00c2c1070048009003ea480010a803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 132801312 1250 132800062 132800069
    0x605091009140705120d0302160f031e031104050405060301060509011d060f0f01030b1201060303051308120d0c0302131805060f01050f03130203030a021c0302030c04050906010c020a 80
    0x25040030b809001080402d010000040c103048445a1030055100480c0f5210a088030569051650100340c5400715240e01c0a095411903105910754421a058078020702400e1550f200608400c0d041100c2e4120720780070344280b200b4050141c189508052401d000c000103440004e00c51134165407944c02c0043c603525090034190207000000e01a0201d038018102040207154010002d0f807143c103240a42502c1c03601c0f1060b503102d0112080c80c01155141070540410302e81800c0b40010341d5203600c0e0190000c240342e4488d010f0710a4134843c203040d141159803001d4032a9546c2140240c2c2d82120381c00c001000c402e02555005008100746410094202244c00c06040145403095000080003c031aa8243c2d0301c204d014440c03164000d50440b02c0845460001e00000c007540500754800f40e0851000000c141c0560800402059070b0754010102c9a84010000000392a040401c014000904011802400e154024000d036171107902131400c20790a0614041c204240440003820340c85c1401108805100541c40e040140c1c0c019 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 132802562 1250 132801312 132801323
    0x50c070813140103062114160603150503061906030c12030e040c050f090604030b04140f01050106120c0302120a0c020c0105180d02180a0606081e040605091009 70
    0x540745490181c079802000102c0c40380c105850310909000742c4041200ba105843c9441100540220581c03400d00c078014803001665240d4401c8884900d0718002d105070131810f840099606004002a2200301142c500282c051141c1c141c1001e07000030303080901070703030340c82c034216100d01c808220316640c1d45400b24000404e40210444020008a030014145c010183d24410141518100840c401441000740240122030a881c20110300050515003640c900b0709032400b86806c6038a4520b10b00781407030416400e00c002d8410311814042c51900c8000018184201070403543c2d03032348070300c81001c480c00d8107000180440740040307040c564203002007600c2c0382941144610038400e9400000341c445094401a01c0c1281901e605410450204824107011010b548540310001054a0704250601c0d2072000865650f14205450340c00c1e2842800c101064030581c200c401281d0154440403100d41713076403c4100c000c1000403110520303228040c01090006030b01e580910b80c044201c0d401e981d844e0180d452107005407544150f05940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 132803812 1250 132802562 132802597
    0x903050d050702011407230306011103030a091b03030e0910030b0f18070522020915030a0b09040201020d1101150816060206070903080c0c04050f041a07020c04050c0708 74
    0x11034a4541705ca50000d00380d080003030625070041c1d60202d09109044003241d00180c044007250880c2d008a140c030003404280001c0e00c0e200d261246c0f6a0005041004d02a55004104034912402c940d078000c0980541f40c1541c1c98983c100680018040300300700107020440e421a44020002c0070807442c0303800e80d024001540c0d00b0032240c01d21081c50040b040702c500f500c1c61241c108010400041c0d075886500700b00081c4590b85800d58902c4100c98000078011034410030f421030958030f20f1083c0701a0001c0110b10888110108102040c000b1060090001c0204c6009015910060458120501a118184800a249002003003c5648440c840300d5800c580e0300100b071035401294401080c0495035036910161400c0e20040c80c0c1c616020900510495180c40090010200002d1129917020140481094030380c0140041c825410320900038208900c00315010b50700f4521b0306c02c4002c0481d92036000c40e070042d0041e9004000c00140d0b441004010407002e4030032100e01c90704100300c3d400120710402500f0310240d45c081011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 132805062 1250 132803812 132803831
    0x2030403030b09060f0111030d0e1c0906140c100608030a2d0809030904090f030305061005030c0c071d01150801030c03080307051e0d0c140901030903050d05070201 72
    0xd007070354450710300648a00621020001c4c941c0b0b0301000c09004080c01d1a1406005001e043d1040c20f520507898044801c90405071032010420b07000600c1702d410031060300300d020308002009c4111509495070003071000040305098203640c540b4104000c8d040a18030002901c411200d6042c2c180d0807242254000e00150308040b46044d10142c000f0281001080c4011038042000c015140300c040e464034504100c0180525400855280f41c1c0800070394201c080041c104110f0300145041440c08203a81500413000241040d00044680c00c2600080000c0c441030f41340c07541181c40e1034000100317075006001c0b00a07451180c0200000d0103000d04030014074528030982c2107821941050310700038041c04203c41c031109018000004000203200c1800110443c0d42118403280c49465250003200d040c894821541c01e00018556151107035040c0710014010906003013402c0000c01080e920a90f03094460b080c009180c41000d02c82c200c0340754025000005420321901d00385140c00c8080c088001214415071345400180e41d16002034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 132806312 1250 132805062 132805067
    0x103020c010f0c1206030b06090c0c1506090108152805010f081203090a060207020f030319020706023009061204020102190f0f0c0b0d0b090112031d0d0b04050102030403 74
    0x813000c2c20303180345082c000d40341903456003030b4000e90107010280204410400079400c0508401175070381100a4a003a0b668541c04450104a600b8050719070301d02c2804940000581c5010002d040004805030901016295a55149008006032120804800034010b16100c054620062080601130418a58030340c0f03819042246007850820a50030a4505078800c2040c8030241e4070002d207400314241d1241c40541e64441030320120309020b1038600110b81522010540c0320554129941c048190041e0303a00310382074140d0300e000890f51020a00036840031225608160740c918030072181d0303200111150002c031501e030503036000c04147e10354840710346e02c0340c0c402e100c105010171580c3c180460403019400c0c12100e035903031480352035042040c42e0040005003500901e041c004200911041c0b11002080f80c40240ca449200240c020400b41c14103d100c00d20942c40c03140080380221000d07090745040394040d503400c4040d90700f61010010410303c24500c00e500140703c10022000420082101d803044d881880003589909091402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 132807562 1250 132806312 132806327
    0x7090c03020403020105120603070e090d11011503080c070506070f05011811040b0f09090f011b08010e071e0512070809121605010e061015050f090103020c010f0c 71
    0x258420140100710810150303030301000b40d801d84508241448055210350001a217040c5245d40f02c140c44518100c10086a0750b004108140401115110180c0c3c851340500a00e0885040d1a00c00601c548010024000b0074044005400c2c0d035490752003192005a00c46002400d143c0020000b2107182c000881d89078104002030044030411039007e20b061070b1300806965400111021050b90071b000c1c90380c0f8020110b140c1e88a03c00000c003003501070520241c0e81005c02d8440d0301c03a04a05507140256003000074604200450000c40c40a4070000d80d580c140590030490700a044042c05009802040102c03030308001c08651030500b8000700d41181c0c030794079640c1113100c0b441c0d010301d9001000c80e020301100130f08210002201041a5854551003043c1e50743c0c414243c500c1d10000b10310030310090320661034540c0200c09140300054040c02444803680454152742e8801407002c2015a8031481d1300003607000e2050b0050210b1300c101422900710141009401c204400c8203407030031a00e0b1032081683c403640b101d0705100040d801200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 132808812 1250 132807562 132807581
    0xc030c0106030b1611100905160b041406030c0d0506011e050301060e04090c030303020f120a0b030f03030903090d080702060c0c0103060603060321031805010603021f0f08040201050d020c0709 84
    0xe0110510045c00c94031034884444e6520211000e0b12100301070104141804606803c4d0b44c3c00c00051281074403071950099940240c0550203440002c6504c0300e00c030303140c018256031203441088101c518021041c80d036000035110250a1a061041c0000202802c0e6100c00085182c510203540b066125850b05100a102f00d211481540c040c2d46401075440101c0e0600e228181600d405d03080c05640c90b5454849065248500901550310584460a100349040a600012030340082141280d20045400c82d4240c0c4038801074071482000d6000300001c41032410011003182c50280a000c90317508280140e00411042d510960015805030004220501c6961301132007464007500c003a1404100503411039880c08c4803120200300702d0200d13440c044841c44100348a070704203c180c1055903000c0c110343c81552410303501814480c08224030401540c0d132881040f14610190280e50040c035507450003c460000c9065408190181050341006010040daa031445900d000400301c0d00c4860005000091800840d002156054403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 132810062 1250 132808812 132808817
    0x17070b0106080705030412050c07061106090102090109090e01060902030405031b0613060b150f0d0f0b060301060e040b1906080108010c02120309010906050c030414060601050a03020c030c0106030b16 87
    0x140006a0b520130250b90348980d0120317982c540813400381e07801e441c81d001c0e4500003002481a4000400c074154030a00e910342140c0e009003252419203845984a09074000c0289090018500c80410008485281c10036040c003913020b800000c410342c0340c4480c02c007170703a00c00c40c0c05072480d900c00100b08030752021900011000c601c8031405801c0710f042104001d41c042481c050f000c0c00d415102e0010100e5956206046149a2a00000180d031805d0142c0084c1c40340e00704c0d8178030402440c03401541210f03540326806801e00c0315500508203071442e03092420642e0201c0000c501c0f55040b641d0707801507046030f44650441180785015400068151031030f0110050403e40d050700120381e0340c0d040c5030310381c40000d400081402007901e80220503604e95a500c000715004080d4628082c158900302000d100801501c1801580568064100d8180d48968001c203556281030a44889000560801010b01224443c1c1c1c082c0520010380d40542e0300c0d11141c80300c1d050a4401c5a08107940c61403001c000e1250340d00c0045c00d034891200e10350 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 132811312 1250 132810062 132810077
    0x30f04020906090c1605150a050f1f031502090a0906080d03021306080405100203041203050105040b0d061508010203091c0c0b1303050d02120105040608030702090a02090d17070b0106 80
    0x484c6042c18080d042e152401c084800d6040070800c2002d0107288110b0300c2440b104507040ca4410462130252000741c80050300040700c2c0e404205d401000030040501040103402e0718103c0c0b032035170381e6820404020200d8031135642e03400d0040061680c0c42518020040c6441031001c04e04c1806c01c02c0e40e50070800200b0041050520402c0905116000c1e080d040c01103902e00d00b400c0d038042da0b86080460400d000504507818440c0b00100700700400c881d12448108107482030307030100200d0383c8500a103c112001e0301c115540c4032880348201c07800038109030003003040c00300700482003001d0340c2d0341380001402c0ea0410740b2580140d400601f940480613441a44242d03c980403483c100c54204403540f61100401e0018200d00104009043d08506160052040700e4002a4501d070840d601d21014400d106180000c0c081c0c07520032030421100080341e030800019101e0803600100700403100d49a582200b80254460034459803c00c281c0614880480c0c945406011040c844003801584c1c1c0d10070745002c00c1800c1c1d05810880902c4400e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 132812562 1250 132811312 132811321
    0x30f06060207050a0e040303140703061a0a2c1201020304020f060405090f06010e1018080d0219020d060c050a0809060709060c1119081006080c13060902030f0402090609 74
    0x444c041501121036542c1440c40a0310b460504402030b1005039501d284000c0784a0034007580541c1075000d50f0440e010648101c000080d8003070310760114070a0049001c0040c0c00c3d000c00c44030032400402c1c2101207180a40103580c044480d80049240b14400e050650761a07580402004250705000394440080c48045407868034040c1414001150207101501c006080ca46442c00501141d0041c50b029160000040c58800400304081005112590040141c2e00b82c048400002400304400103240b0300c081d04540250006a0880a00501c500300301030050703a00c1508150b0f003a0107d80b41d8803d072800c0904643c1c03199500c03072013110080c051030720113040e8810f5170380b00e4810010400c0e4082c0c14201950344a103000d240568480c1040781602d00d2000d0300c1c0c0c4d03018003a20b2a189070703034a01a04140c01c0300c0c01c130000d440c01441e007003408108660f00c5200c0c1e41c035150807081c0d070320311a85031401602c40c0601500b14000303003c4e902e820043c4102c1c0c0040780e44000519066080c40151f00e801c02c1d1881d400b03a0205c5a000b600d1a1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 132813812 1250 132812562 132812569
    0x3070221010f020f04150c0503090415180509120f07031d130c030e030702090c03060d0c1203110c010f0503180604050c0901120b01120819030f0606020705 68
    0x9004500801415032032048120030442900711002c401451903056440f0b00408002c0c0c82e45600c18459481898030110b48501d405000d007801030009500708010f1420300c040e030014040541030b14655210003c9601720041050701c041c0d8603841d0202c0399088006400e10b0702c1c940d518070702070102910001000c07050020241003404130080340d1685515140400841d00e071114049945108909810382c440d0b10405607021080941d032019040020720764081c0404442000d03001c5c0c4a100b040340280d040301061000030443e10004000319007080e00584108080c00300f07074603001c200e001c807030f080800724254202d42202490380c081c0765080403082c007001400c0100b60b1100080d200000c2035003201d040c844003000041c040c0d40192014003001a81e041910103900c1c061070040e4844c0e084580e90341c46003100d0000414040700190040300d40a51044204890741d08086020b00381c2414000120342c542010460300d807200c100082820301c0100691004074039550320062a1040d038000c2e401c00e0f82107500200e42040943e8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 132815062 1250 132813812 132813829
    0x70b010303030b01030f09050105070e041823030304050615090c0a0c020102070b07030207091a03070e131205030603070b091e04060506130305100902011e09030c060203120603030702 80
    0xa030715003800240840300100617001740c40342040d0312100c40d141108840600c041074101d00d11900f10384e40d030800c003280700100b0007003110410111483c40c0d20444111100091102c296428001c06600c195041e2910041159180da4011202188d40341c0219007030200015002c040c00706c210404842030f007030901d003448203462a405906183c8041040714011002964000d00004c40504001c6141a83d600c1090501a640d42c02c20702c54404020b2800241180a45040850689400e4004c01400341d052802000524000014040c1c90407009521a10070010b0b0405111204ea0000703134039103907201e10300001010b080854503845140240010410310800b5600c402d100e000494940c100b1000140c0310380702050041c03410750412034100c0340004800704034014a80030307901201c1c421400c8403803140c000890130301a00d488030130080c00702d8a0742124281c0c5104012480403c0140d602c0e200701403070354984454400d903103282e207c40050703040095080c0081100076400b5600407800d50041d841d1207030680c0407a00740c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 132816312 1250 132815062 132815069
    0xf0a03290f041e05030a09080609010e0703020904060b10030504031701050f2205070e03070801060e01030809040219051c0e07060818060103060f0b0f0f1306051503070212070b01 78
    0xc10f014100b404060b410301c0c20071031078a401100300c80d100c1c0526000035040c601e660240d40841e11030140002c44042050190350701d07890704140500641459a403d0021a850190040b04c42d81d4850b05d90b0300b100d4403080802040c20100b07a0f0041818206410040c0c000c00c0400d0344e4015118940300184141d84030002c2d61103006000746c4040a00300145180c0410903501a017050382c035507040c0380a0210040d80940f072aa241034049080e542c4550740e4010701c900303c41e024800d00d450400718030010000314081c48054950708101030400740c42d00e800504060441c000903842c20012036004148440ca00229040100c00d1044219003008001888603203155282400d01c1403000f0820385400240400c000d0109207042d4101c201d0803107240d07584902e420000340c031145000c0c1090b14a0b01d00380254070316014420955469010f0800c6041c2074000741448203443d410514594055118000080c05494817450307082203602c4c8030074164030383c1000c0c07030000c0c203005031a42100c091810912213000403503036010149044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 132817562 1250 132816312 132816323
    0x2070c0501051804020c06160f08061003140906070305010906050a1e0f0b0706050a021602040f060503100e0c010e1e0418140601080d02031204020f0a03290f04 70
    0xb03c82e43d0380001c1c41602020b480b00b41d0098004036144d00e400c1d800195150040c2c5003103803175883c80842e0b4442210f1a50150801000043e54200420841d003002001205444c00e149000f086e04828903520102c2004291001c5403e81d00c80700c10041d09d0750b81445200d0142c040721509102541c41c01001911442582c0904006450001c48401c00741100490315002090802c15514486941d66109030890700022000e40b4154140720020315038180c1842214008002c8a03283e00d401043c03034003404000c00c554000700d512241da485c00811030340d5040100310941d061106010942c0c85500000500300310b80300c100a4140450b000da404000d684030300200340c41010303420010405140d2440010081c4c42052213000c915410703528a4410300c814511244450804602103444070b0360307030344074403a590385030000a41d0050304180001c3c00301e0143d4450154229000804c4000d810b1201c10000b04418065402201c1400b20342050040005005002c40380038808d2100240a0f40b401e030107003403a07401c0001d100a08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 132818812 1250 132817562 132817567
    0xc03010e031c18141c05041203110109051c090e07050417030415110c0d02010f0c150c030c021207021e030f010c080703060509010305030403060b0604120501050a060902070c050105 79
    0x3081031000c0101c0c03689039089070355280200c003202c1c4ca00383c40c0c1d04104446100e842d8071800710000c0900440440c0d00700e075010450b0000c13646160310304990515000e1284800e070354039620f01201242c002c02210700c244c2c01c00005280c044005000140100ca091b030b000310401c1d4880c904000009820005440c210b078000500300000c1d00e424101681540700c0c2c2d400c038514011455440c211656071041c0c00c808101103031b0085503045072920080040c50038544030001c0c001403407241a0148984100d00428940e44540c1d2002100302c1645102c10a56403041000000a0303500c8201e406600c0e4100500c6000600c024046c0f0318142c003940110301180c840d0b5500400042c1c64100c80002510100410b032240b81004000b0426080c084a0042400030250751900019003040400b16691800340300c0941280d61050055141504e950b850a000c0d00c0b00701c2c1180d50015043c440014038001c40758548400c0381c840c000000701823a2a9141c03c1c211440b6820100c4142c1c4103000c400c0000794100f6841003610024208641c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 132820062 1250 132818812 132818831
    0xf09010b041a12070323190b0303070b040b0601020d0f09030809061207030504140d1e02190b0a0f051303031a04020d021206010206100e10090e0c03010e031c 69
    0x940b02d2086880d10021003a220003001880f983c164003103d8403507000c0b00d8484002211803040c07030f061001600e8030603541619800c0703940c10140c3d950003038150a9006c0c00341d9040c40b0305034031804c4a2100407141911502031020070040103603414442d6034003803031907801c10401005500c0402000428075010042100b1b0000602007201d55a50040d5026440424210a40d0340b601000042c060f010560b4121007005100c400c01300c413100003151100c61400306a4410b000100c40303020403516101d4031040301055005400700003900302c0c1d40d45030f8120b10350b00500c04a085410b04101c0041114160300340521124944028071000b036510001006c6055010315000c40e01c0c001104906c9061404500d049a0161000980d003c4c1084c00c0d801070841445662140038041d0340340001641c41e250105c640800140e81c00c2400c0c07000c1011010b0b5550030200314140c0101d019242d203072400484004818442c1945e0043d020846980ba09000d6181c0c54101078024605040a07401401101c1ea8080701c544c801d907441b805d034103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 132821312 1250 132820062 132820109
    0x6030308012702360102030a050706090b010303050a111902040e071e030209060d0804181e02070b1e01090e0c0612040b07051806030a09050a03030b0f09010b04 70
    0x10761019940e079021940c808041805000c0504040120796001c0c0480040783e01407134a00ca03e40c00c0b03000d41070b00650714101c5240c0c4101c1d619488100c045621540d14036020022803600100280a14800d88441e540d17080780c20700203010106c1104000c04a54460201620b14240b030300b02d4803d039103505070b5002c142c0c2c4124001640c1002c0c0b491b0080008030f600c03443d4a108044008e600320b03085a0003520112401d45401d020b0100c9210000740c0502403541c1080100272a40c10700c070495510b041001d100040c000701804070466181c4090344203500175600800d080043c8010300c1d0703210b0b81060082508070896180c8101101b45150140701d5074031129520800741d812032205100a03031100c04010b105540d903111040d2002d2030010305071000e075800c11181c400180894007030003c840140006013950700b0a40604400c00100340c2c801002c00022075101d513028030001d1000c009444409119072070200310707409680d0900079040d618001141c421103500c2c0041240c000b10104483c1a10f001400e0700b10b0b9180105001e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 132822562 1250 132821312 132821369
    0xf0a0218010c023111090a050f0604230a06020f06150a0b0f031f0b04141c1505060d0b0103020d03050c0f010b0405070e03031c0615120e010603030801 66
    0x900c40210305110b1102d2001d0381302e080e1440c1101c0080c100207006068901c55050b008020107250810b10011050080b485c041410030440e4400034852460b15480d4503441c0400d24402035070401c04d0103c90b0031918a81350071071041e00900041c0c03004000351a189080140e130759401818128140c3c04003500031030a0745511031510040d0085040559440a080000794550361080f84c1d42c2207040590803207042c000500b0340407601126144c2e025203052a0500d56a086190b01007000644e000c6086404c2049243c41161070f8105d850040041c2d40c1482030340f440700c40130740710000c0c605c82c425401c9411a83c001000005294107503501581c6070ba80d1864146403d072900d10803040c00e07400920803518005c10758801500400c070070800c25103060120351641c40058500644900c2074682c103400a004400d000d403015003101001da07000303941c00714249559004024200903c80d88090019002440140c4007074400c0c01884000c09012008001e15891918003d14038401070151420141001400c860340c251003840 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 132823812 1250 132822562 132822589
    0x906030d0c0602090607110f0a06050a0f0e09010303030906050603160b09040204090203042001230a0201110d060801060f0503060402091902031315060f062001140f0a0218010c02 78
    0x40d80d81c0c0610709103003650001c0d0309011031080d030323100b140319801c0e050168103a003c841007500d4140c200840810245e820112003045001004403280780d151a503a00c00c3e40d40d50096001381c03030014003c06207007060380030390700001c14841c0030b640080300c4100810040a401e5084a400400158991070610700003406407040340d00c0740240b28004400d200503c25019048441c02e003140c502d151858505600540d003444d8484100044007a009500301c915504070002001e205026100010b5018003800440c0d4558000300c01010106903181803e0000a00900c208002f40004404e140149850240042d030b0303488000700000e00602c804804207000c0e00362001d103408040000d160540d22498007000e2041c0380ca100d20303002d8030018101004000c850343c0c103210702800d40e040a083d120b80307141082d00903103101004085603980c1c1240c80c01c1d84610503400303202e440c1203141c030303010303040c119081c0006e811030825005460003410a204000b0b01440720140c441a5490410a00b055240c4101900025201082481 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 132825062 1250 132823812 132823819
    0x7110c060c070e0c0903060f010303120c0c0b18120405030d0c050a170d1b02060403030b0d05120a0f020d050301260607020a03110a0b010e040507150f020c0906030d0c060209 76
    0x3000c0c851404c0291015125150003501105e0700395440d529089001e8600b0711000c0d000c5007144180c6d6445404a80208605000c0d608000000e00e5150756035404044040380d40400d600d905601e400035a85061000d20820303804861090b081ca42040b0009444031071841080041c004015881c2e420803005000900500b030700586514450744d6600e032070701160f52001c200200070b80d140448034810148103040e2140444e001d5030061020b607a40d59001e070f000742101007440e940254034000003130000d0410880005109064200e40b82c4540840b00040c0120700061400c8085d0741200e01902d11980c2c0c41070546e811100c4843d40c1d00c000c4c0d4980d200b40c1030760285000748010341d406002d04001185400141d0301107a01e11a03135405000000003421291501007490380141800c042d40300401c01e0a1841002c1c0760002c0c041c000f07542e08c1d540c0d2460313250041c0b041c414448011540031008010856014401642c242c1429038441030189400310001e42c443c03059210000c28400140003007024044075606851003008090b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 132826312 1250 132825062 132825089
    0x40302120d020c0607030c0c0f0c0503100617030a120b15160219051e030f0a0308011d070801050d0c080d052205010206040308090114010b1207110c060c07 68
    0x54960000b075480f03141c5501c4076104040c0810540c0c0d00c24490984d224030075a07600c0c9007060030b0f40c0d11403815006800d8203907035981724160003040e40d41e42030003425580e0f0b03c18003002610350710f03001d030844c510720781d411820b1015002231011450350340c2c20034204c22055000303c4001910381200b600043d04800c601400040300a40852001d85640000e241452a136008071809043c900030003920100e10512405200d410600700820440480014001003615000017001c2d101d060580058013450030b010700c5410341c0081c2c0b0040041014008070004000b49440e802c8c0ca050321840c0801c00542101810b20601d0700403007036440354005208002a040c0302505002082e200e03403035100c010043c455004060550703051840008042d0400700c040d11000c04403841a0060241603036603803000c0c5c0c0e2090008101103125502d0380c103514540c030750060805010308003204034180c5841d10f40409402e00c100040014050064490100216000001700c9600c005012510103079a10035034210306041440c19841107074011400d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 132827562 1250 132826312 132826327
    0x70c06111303060f09020a0504020a05040506030a090201110c010206130305120421021c0302030c07050106062c1806010210050a0501080114010e010501052109161a0f0304030212 78
    0x2201060000c070b03030003484148160030405040702d04a03410710764000d610500c401c02c1000181032a0f005040c1014143c1485400c040c1d85502250465000312880013800c1d07a10203600c411036030081019003e8400c0040107040c204503480c0040d5403448060b08a01080c101521207400305032140d1b08a840305001802c0c0000d00741046d00d040301600e01c0c3e40781d034400400c07100031000c0d804038400030789004402d002911038104400810310035402503101401418440500b0008500810300901035040102442d58850841c008071000c000d10314142007080d03c1d41d040203410b0542e0301c1d80d502da0516940d501d8065481c0000d8843c00010303450002a01c4515501c2818902000555049030b03001302d0480d03503603000030300c00c88640940840305030f202409180d0748100c26400500c529441a805816075041c500c4601140210280c108444000c0459000d0280c2d40088509040482c50503801c2d0014141f020081e400380c1d40b200e000c0c40b03041c001c184a11001090110008003403501c04c000300c0d10907400b1034080c19a16510b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 132828812 1250 132827562 132827587
    0x1512030306060f0e0303070b1506180103050105040e060402090c0d0e0109110402030f07030905160806040212030f070b0406020706050115031b0806010f03090813030c0504090b070c0611 81
    0x81d40c85000d020448520010400c140100551940c10b080203002c0c62810712079135161115030002030207100301c08605100355030301d903104d01c4010420785100c4905410300300c0e542d00c00101540e2058010500903410144800c1201c28002000c030f40059045a140c561075440220740c442c1802041d0301c4049407418403008542c452810341c0000c2d03003036010b501340c3d420200c031101c01d2005a100030340d9903000011000300081c0c43c40784a0f9010303464a81c03240c0103035180320508681c1c405070070840790070000386504514148801c502d00a01c111070059031f41b0002c6e500b04010019100002c0c0205000034188010340d80000c1d00304422a0704868545501200401c01561900548100b803001c07644c2090100c1d01d06001010308040f003503036281c1c0c2c00110303507035100c01640d1702e000456902c1940c86c1010217050301c4910804c00103003140301078040d20000200b81303c0714504d1402c001050202540c0424025460407102e42d0210700d6180d0a158840003070306121400000610341640240003092621484500200300f01c0b0b203001c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 132830062 1250 132828812 132828821
    0x3140114040501050f06030f070e030a030305012108030109091509050c031002180d060207060c020309040c0e030303040605090a0501051509070e0a0e0c0c07030807020a0f030c0915120303 82
    0x208240c0741045141c1c0c850b0b003803220190904400c2036000c6424400110800a20001264000701a140c03150402c1d00070320102c0d140c0300c3c40480403008251110f0040c021580da400060540421002c5802d0560166803200c0741c2510060040c607005548441010003441001c0f4508025040c8055081080c040c860800342c2c2c48400b000d40d00d5100e401054403c10400c07066009030341148001c1c0c26050b0801040504025800ca5015000c9481e0382d020f01c12030340880c50301c1c490031460500b6500a0741d507a4601d0307000c10045903d0081c0502c18001c00170070421142d1800002c0d25449a8010800900d60f2102d5013404d24041ea401c0c2d0040c15507007804100300c0e40c4101000ca070078490100b0790300011592600324050720785030310341d0840ea13411541011003005810012082c0d40e4010801340c01c1c0360328201000c1255405c01501e034100786c51007480090500114100080710400500c21880d01041503400c40d81c07884143d0b00b462160900c101d4940040c4240125510302100050101c00b0035009010032601c0c0160150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 132831312 1250 132830062 132830099
    0xe0103030212040e0f060d0f03090f1a03011707171b0f03060a0515030f0c24040303050f0d14060301060b03060d2003070305060a0e0304030f060903031401 68
    0x180248288205110700000640e004d5071000525042c0f030ba0b40e200d50300441d001c40289803d602a00c00700c00c007008036510351943c5003628004d036541c03d0710038100030718102684a04c2d0b0006101000c01c0b05a02c0741e0120000c1683c1c10b5900c490300950030b0b603003810f0005241040c0c0d42c0050303002d50f00c41083d24034180d82c00100d443e1080d0b224949900480c810004120201e40e510141d07e4054201d0000034040390650382c042e6900c49a035403143c4101c035030180042454011490500b80c55507006420340f40c1903150411500c503c10681c3e030180f2108400c40f10f1464518012448000c06100c0049203000482c0f04201c2560342074100702a04101002092400900b000c0054400c41c1c0a546481c03030100366840c0000031a03105001c0a4000c0f10740380d41e290340e05800c880c0717559440741034994422989012981c0c00d00413007000b180194000d0081b42440d0608a04850b908003e020190b40100700c2000003680070700414800702c0d048074000803031104906094004e80b41800300c070301568064400120f2180c00c00d0390101c450 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 132832562 1250 132831312 132831317
    0xa02120f06060a1d0a1b0905011704020d020d050f030f03160c0b1308040503030c0c0a090504050607030c051306020f010f050c0304080a05040314070314030304030f1803020a0e010303 80
    0x940c54000a1041d480b40f0f9010311007152000342c107089560b0746581002508580ba14100164014101c20058071000e202e4600d2400a00c01c42c10070003607503034007451040040d980c080c2040303010b007440d50008981001c5240002d005615090502c42840380a10481d483c41032408240c941e200461500b02e9001d1f402160480b140b84260440160a14852400150304039444212540c0644424681c0f1814001002c5c4c22144801c04107c08200c0f40c5041c800307407400b13035007800080c20100002410800343c644582c10551030703207203007508000201d100015141d0b0006014207000030184042401103d10784218008120100c5140900062260b030003c0c125404080d00c00c0204540d8107a01212001d417001600c0d803407850101407021a0103c0c858000904c641001c50414601d050b42d41d60754406d0302c6840341401010b64002040410501c0b41c0451048030505d5942c02961440c509a603010740707100b203580780c4002000041c0008031256060703803614001554008000400499591054950f403074401d0004400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 132833812 1250 132832562 132832573
    0x20106030c150f11010e0f0d2601060309021201090b1b13031101050702090c0d110c102f031006030204030c0308130308030901051005030d020d030e0a02120f 69
    0x4014821406214411080369034010940b101031008444c00920320b00c50201ca5541c078203102103003e100300f010714000010100a0480c00190400c040c10240c83c0d4004c0c0080c200765a402c62038444500c88645042d03d41c242000604003001d0b00210f9500b070010b003c9031810350320b00b200d0b507800c0c0510f1a041d18411040007030f100c0100c00e10400d1143d968090000210494401c1000074400140012008000c03040113150075410041c0d9500000c00c40c2009941100604c5400142501d01c500b042c00303400a0251074942840c07510758480e07202580d482c2401da61710b12160b502d5080880020b48050441100f80700c510b124014100181c040941503401602c00358811070044800042542c002d0091701d048035001885042c107140343d52a059001d074880c0424071140041e804c000301c000740c0c2000295004030540b000000301c5e4580350040d80d03102e201c0303500110321950026500f400150360006000811240c1450041228211485407625143c0329440c025440008840b11607d54031000a60b845074502c0c0508560 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 132835062 1250 132833812 132833819
    0x40b070503190f0f050904020d061203020f0d0906030515130b010210090c0b070312020f04050108070201050609010b0c0307020d210503100603020f09030d080915130f02011707020106030c 82
    0x8580c24881c0d090f550109160310524401c29004601510322114003030000761401d003081c0761720000c840454002c0030044807200c0d2904d050541c1002420301e0250003000a01e40d04a50510140c43c942051040004241d00c840019a040141d03130304603000e550014050702d03c0e001410741040701425510000307500602c5408884248007500e0b00412407a2500140c8000300d050a1141180e45541f00d91006c0c2e00380a08141c22401514884c40103021605000c3c7c001601d90f13050400040416101500d540116810700d420310008d80d4030034580d141160060754040d903076213400203600e07415401902e0f8040d5001a090001c041408074890784003030030411980d102d02108028810a98990009076104441e0340c800302402d000c8207000b035000b80181d117070f41000241840c01e1400000e1400e00d212201c1070001e2990810710010f02820060020342010b20107550040d407506002040d0001e07601203004c0d00c841c26400c0d498095900400c1c0b200540c0008060004075840c060102134043d082c02e2104035130030300d6503c0000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 132836312 1250 132835062 132835067
    0xe0706021f150b030709030506010b030f180616030b03150108011401080307020f1c0501140606070809090c090a0b090a06030b060a081914010510050c030304120302040b07050319 78
    0x40d1211240b11044800c07050400e078050403a500014400001d1142446020010807410030099000300f6801d0111507403407908540c03822090902400c81140400748010150105101041441c1e1001d030694058900c11443c0004502604141000e10340500856404000c1703074a0802c0c600d03068036aa070000380980b81c0103002c1c1c40c0303000c6000d00c1081c8507034205110000c0107141212800140260050004001209001c4a800e41c806448011207180c0e40d15045c101e00e025901c0001c560001085880f0340c24049035843d4644030f88503c007020303403059030104001851500c4210940e0071001016000c1c458054490818203142e41c030801c8010300c51a200940002c0b918828028100c0032100500024108011a0300690b428107001d4904501314158020700b030000b5a081c89146041070039140c006031594540814420010702c2d43c2840c1c0c4c10000300b0000801c55240000840e42c01031b5006180b000c80c0f286900c022002801550006c00418900003025810302c44008080c01301103c1c03508140c0e0b401c070404d0f44d0030f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 132837562 1250 132836312 132836321
    0xf091205070206070f0606050618100801080a03050c12030405070305070503010c050906030604060302100e190f06080c1c090312090c0b09030a06050108010e0616080a050a0e0706021f 80
    0xc3d48400104600303400200c4400213951610300ca0308000c100c0e903441f000060310a40248a11024111481526000915043d40c1003a02c1105c03500345107001e54181401180c4411000c5000b80510000044072040c04500700024408440400034080d00c80c2002c0ca480c82e20340d00300d448140c0d491711442e400400d25140c184551150060f0325103440707180040030401d01a403904010402507000e40e64040010241e1a1080750f01d862035001e82c1c1d0800300810301d030200114140c07400c031084101c2c0d010a8040c814a040c40080005417401070400c0b40c026500e16454024601c1103420441c280c2500f400b586035001c40325080142030358400e0f256001b60039141d0b40200e084030144100940030810000041100081e0000206040d040213415a41181041d0b1101001c3d03400130b0740b0920890f9510444004d07800402c1c0801904500c00c164081c82c50031451034010000040a0804400c4a6541003c10b441c2100c235841000080b01035003d07100d54683d03450001e912041d0107000307078010309011004c040d1035017524401d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 132838812 1250 132837562 132837577
    0x18020a05030402011b0605040c21050a2303120106032912100e030a11031305040c05040e1006080a060f0308090105090d0b04150e0a02220f091205 64
    0x5845041d6595a0011100344464040a400c9210058a11004900c840c01041e10031030140d00031010b85842e025614041140c00c2c3e10b95115a9a103d07941400600c000c2444101160825140a100b1024520885108220700f246c41010321000035198142e069003051030f4103d84840e03c08005140c4021010980040054041e01c000450480f56091503c2e00b84040c10f5a00c901c04110f9030080c444100c040c0072514100c60402c1c10f6070004c10b4031131140c1d900c0a1104060180403002d181811003908a1410a24440c002c3e80d21454032441070715452407141b01503900500010f20060914100450142055551f07409590700042d80d440005409600310b0042c41c007212042c01000c0300c00c030710b9502c5111040e088a61018104103041045007400c2d0b0340d89000c45045030056807112490b09003803505e100040c14000041c60744030704060400103e031901060b50040c0c0b9405450000c01e61000e8441c1c8036241400d21044018286420107201c01034026070b11aa0815102d06001072940346159400c1d03450303015014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 132840062 1250 132838812 132838817
    0xb04050106110c090a11040603090b1302130b060f0a0c060617030f130302031f060909020d0201050a020a12030e0f06091207031101050c0a03150605030c070515010e0118020a 76
    0x38100003900300204d00326440070091034001041482c3da250070b146540036500c414000385d290481300003444038003c100f6402c00f581c51009041c1003403076800306e0340501142171494400c80e0f5490031070b002c41d254101190000785c400b5088544d40d0f40440710140c2006e154079400e86140d0300e005c0c0c0104150318481c4130180d20031107500096051044080802c012584100c0042c05d007508989000001601c0c10001811440b500066603048444d000501e030080710541e5012882141c107054230345016856a50550200c5a028a40380c0d640d001801e106924110b02803000030b18184c1d524806e2448158550f010a00c138080780750585242030300610380307150350b0b4a082c0c60213a00d5410610150a020300c0c1c0e903005140700f9229041079480105604842c07800c54a003103592a4600000080e00390300103500d807180e80c038188040c4bc480c441080c14100020701d140801040e01b000c910000501a0600104111900c00103a44140200484d0b84664040c10007800c00e20940e0b503407120402c4800c2c07043d1002e0090f130345002080c1d03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 132841312 1250 132840062 132840073
    0x7031b021b0d0c0f0e070f02010606050a050a0e090405010c0212030f010e041a01140901050d1104020d1d010902040b011706010f110115140402071104020309070e07030b0405010611 79
    0x10042c11540c40b410450b0007001d000e00000703501c500204624024001c4a08505144c500380d0b0010381100403954003401164500101808610f82000594403032228526001e51103d07507420007a0b45165001810581c005802010041080815000701360724408650999aa48000c1007051005000c1514009200c081d03810041c841d4000d41d4211550280c00b50740f802001e20302516000394191000e0b01311043c02c9041c519131480c00c0c1868440d00c0e004060541e00400d0000031a1911a0300d51102000c0504c6544c0028010040803100e030010140300303464081140385000820302b801d009000d41c000072030145051141c41d0030a0f40c041c1d2001000785807044c1c0c0d440181d9807070742c0044680d0f454100361801403192142d48030002d220b0903c0b0f500801852103942c8040e07107013817a51040d00f100c4035400d094030560041080d100024411440714568400903a005a100d803101041c013401c0904e96000300d04440c190104100007254141c006010012095504010590f01c500c3c00300d1341c0c10180d15000c1c0b81d03984207 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 132842562 1250 132841312 132841363
    0x2090604110403080705030406081308180f060c0709141012020102010219030504110a080706030b15030907060305011406180f0a080a0201030e0102030919031707031b02 74
    0x94115801c4003544480807468652070b40d0340c0b1034035504181c10548103a8804075042c0b100700c0d04600c880d80c20441ea62201100114103944401e854440c0510103640b440274404081c101e0f44480c42a0142a14001c015036158501c0f840076664540c000e108007000541880501000307159604100c5000d4054500302500791400d003501c0c00f5803e210400100d0441d03500f000360b0070781c0483c02da42040351028190703000f250b02c1c145400c101154050900ba500d100d8090240104444400003411804441079410082000841d400000720310071014403440503810f800000b041005140454504240d40c5552005c01459880b100084641200344880e1900301c0c0c0308103c524900c07000301d14545001d040c01055080d001d0b00d0310020a0b140c1c0030035030050b0303510b80c0400745001c119a003500900580e071090030002c42c10b610701441442d40c2d814400108082e07900020080380705052041c0d82c1d0710300c21403100010128500700071000070003c00c000c154007100c60740300d04090b0548520225041d0201e220909140703144884 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 132843812 1250 132842562 132842569
    0x100c05060a0e0d231306080603010e060105012601090203160905010f080a020d0c030b1008040515041a19110c06012d03050a0203010e0712060906060e09010603020a050409020906 78
    0x15a4081d0048481090410643c61300c0048002d000d84901001d2a0301c01c07524041025001e00d0000d405584283d0410042d40e00c0601c00103170050445800340390500c0b030700009840b540341324400451401a007845800c0085400d01c180d800540c00380741400034601854661400840b50880c15029060025661000c4440c5482c4a042102d8003c03140e55001841e18081400c00030882d03904c2c2c41a0303000310b03440d910b80261500d80724061825038992420001402d01d0190b8800d602e401102d02090100c11181c4081400c1c00f000f580c070803e80c0c023281c07040300d60709080c03007002c680c00d40382d500000814060800342d036990340f081308005941c005c0c00d15200400030390742400e030703620580c840c0250000180307070703103072031000542200280108011030042028000c00f05681c0181403d45444103043c0c8500ea20146080040028030802241e40b150417550004205000c0e00d03104c000b07044254030002d1210a010f0a00c003420384103600c00c20440344200e5101c428559941c091000359958910042c0d8882c8d04000000d00508 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 132845062 1250 132843812 132843827
    0x604110901060f02030a08220b09190f080a03090206030103062406050904051504060b130f060c030c06090b040302150906070c02060d150f030b0f0c0306060a0e100c05060a0e0d 77
    0x14540c00c01d82019002e401d01230070080520041540c808804405210105400707102905812680c516041200c04883d1904040b07980310f00c0000b090003c0000d003111590303129512036120268002c000a075696564105503001d0181e4420b402200340307d02440c60812101d900310001151400d4449506045003481080700030b050003042e0328080f0005a180d284a0b654500c0303400060140c4d0030300e2a0300c896458071010000034540d08002c40d50503240d0b20501c038580c1c20a0011180700e0b854949110750304694501034003d4840520018415080f56060000300358020941c07403819a03121400505030342d41e01040558071282a101e52000ca492103501c4005400c00034020f1000e450070401c00300f22003211140078189031101e603022031803609848006004210b84016542e030411071000203900c040c21700c0075900c6814403029025911807500040e06410316402030030042040e400c028004860620021005005040c0b022805c960038002d201c002000501030784501d0b01d056103540700a00190100e10f81c00c0d0340f0103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 132846312 1250 132845062 132845071
    0x120c0f060b0f0301151e030308060d0609120801050f010806090c2b0c1407031b061b02060702010609051317040e070519020a0b06040b060702030604110901060f02030a08 74
    0x100080740d0030380702c94030240201192110403c201c00312152600d5000c0d84820f082051141425034403000070008650f00000d420380100b011202150050322614002d0002c1540c10002414112805620306070503403c20000741c1203e00a546044c0390444080c011100140110b4040e03034020079800c0851680c4d8200e5001e40425005107000200c408005c03200e2040f03803c840b101100348103440780194504543c0c4500303401020310301085000c1c00d114a035500074040c00520141d0700520031401680341e041c0440b5801400240948000d007002d506881c1c031000391100822100f40c40958240400028414094032030389214440000030010312928540d070b60740810240440f03a6500200900c000301c1c144152800460188000380c03030300c0340d603107a15603140e001d0403150740715072410341d000303205e00c0800f18081148050344108102c80010b2542004400500c848c09410310180d014850001080300304007402002c0c550308002140c0910560f1303600c101c111541070420b100803005030400c3c080a800c1501030301006030403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 132847562 1250 132846312 132846319
    0x1905090703140c1e030f070810051b0324030706020a0b0601090807170706113018030106090204060c1401060b0307051e091008191404120c0f060b 64
    0x440c0036500013100030090044282e000041c003444021946810804810b0f0441c410019024481c0741900b8251288803524100000740d4441c00040c00c2800b2022602d00c0d00641c8800ca1a240e044c004041c038807030100c0030340450a609400c4144107083c41c0001d00b80f0103c0391150f00518202581d039994156400b00a44518140002c00201203461a01402120007030203c882c8042281e40c50708601615080240d0300c4001400403403140344ac000000482c507400e2006c010611816a803009098444031001c8103441c014988801040200c02c2051400442c08806000c400038400300752541d1003c4100d10440c030404000c80c80d8014020005032140304100c101a40e540000126180e613145150b031582e000729141c10006400048079510402d5090900c01c4c003203040c0950904105110f0301240380207880f8200c000074010002c0c0040c01044462803080c140d0400002c09200360901070032200010300d0151070440310b16000e10030380c40040e0311070301e06201100d0304516021100c0aa50300d54400400e0540c2c1c4407500f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 132848812 1250 132847562 132847573
    0x2040f05040908040e070507200a0308031b0409150503030910210207030302030a290d0804080f01020403021002150103060903020a05060702070609050916050901051908190509070314 80
    0x281500750092992240b1b4a54807041d03903c64603032401c58641c0f0314000f5032a0303c41c0702002d0346800c1e584600e592501a00c2c0e02800a940d41c3c1c4516036104042d1070162426104120001004030701c006482c3c0044581d02c03014170b004e10700b041c0c070780081545900070b2010311900301ea58007078203403e41c034800d03c1411003c125000c0c140c025200e1100500c010b0b82e0201c00141c022a070004144503803134165204040d0101004101c9800360190941c0901c5001124000e09100d680c1c40e8010500380082401110000c00400341203c0c420231040300c855010703400510050b03108104200c00c07184080d00101e100380690032600b500075900e82c00c5a44043c02408000010380441c41100d02d0000000d404100031406401142c00a002c59071614074002e0083da250b411843c003d0070118207028841e01000c0c1c4648450110341400d40d15051030f0030048840b40076418180ca80e01d80301361500226039070082c20440c0a20015030300d003801400000c8c4003809032481550760414980c0242d000304013007a1501c1c0d40c441c401080009849 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 132850062 1250 132848812 132848819
    0x2e0914061e0304080304031403040308011406131701060b03010f09021e03070903060c110316060e0a150f020301140d0201030f06091517030a030b010e0d050d09050402040f0504090804 80
    0xd81c80d40046408950041e0000300303200c203143d044040328171258105d41509145241c41c2d40c000f803082406200b0010050310585200510b0390760740055810110301d400c1d00042d103540e107502e005064210b0340000a0254641403000c218900c1c03030001c5a050318420a24405503c0c03522050304025032015000d250420014007400c00c0ba21085402140221b84955612100c1070650078800700311009807880b0380074000c22010b200c03488940401940c203104800c140030100c0c03c085d420241c004d080c0d80300e1030b50800c8c010803111804100b4082c812510148003034501308418200f020340b1800703d00c801e000c1ca17900c20b80c1c58001401c25103850614600d10350f106150201c0d800c100230701d10f04190f9069402c841180e42e03c490f6950301d400c02c01900100105038882c1e4242c4580090302e200790301d078801c0302d41da001015120f00d19080340b41d00a190b02e801400018000000b23901c030310b05040c0d0319604410509030010388200e0700011545414001c2c2c4060320242c00c035009003a45450100401010724103000c036800340c000d00000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 132851312 1250 132850062 132850117
    0x703120b0a1217070c1205010b06030907030201030e030c070b03040605090a030804080d0609020a0504030212070605031807030807060203040b280e0703051203160314040605070e2e091406 82
    0x2c02401846d444512140c414907081d13080d1039410349007501400d001d004015000d00c0025041003103980a01380002c440f0b0300081341600394858a21000d40c00c1c070581400085811001c00114030443c003d0707104001d580c0702c0310b07156502c942e105080a00018030007400b08010450200050882c115211070000d1101c3d55112440c040c0d800400c0000c0110b040850b00b0400d509140071031080c1000c0d07a0003d010300310b04111014050780005000c4019a81243c140e100514208101800140d904294a951039010b14034255020b07501c2120100d584145010205281c1c0d0315010310500301c00340e650f0704000d00051100042000340450030121000348502030300000420400e0001800b0085800c415a59030302d01900000e00212807890303580308043c0b4245e180081d101c0640001500507a000e100450203823100d40048680054074882075621a1002030070071550150510002c485040101003104503010320101500d0854041c414488400c200095804107490b0200042c11135082000074241070300c8410350b00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 132852562 1250 132851312 132851333
    0xe03010e1e010c020304080a031121090a0905090a030503270105070f080c0406080a0603020415181e050907120c05040b0d03020c01120e030703120b0a121707 69
    0x16289032030724a4690940c940002e02450701c8280c03150009515003441d21286a580d0000c154000d010084801500810400140164800d104501c502c1610218a04138206001d5100c00001031180f070038400001250401401500e104001d4030340030707140007000c6860540b0f142d1b00c001c0c00b0041c81500303407000c2e11880311081c1e544100300903903400000c0c141c54515000391480d007452440004ac0402c0e0000c03c030301494001e00b200d0942e502407514240a4a9107070f0368034040c01d45a04025442402d107403040c48039940b290058400c0b600d800c9034001c13901c1e090412000481c0c51342c414050a907220402107510880b0b031504040c0d0080d030044103d0780c039181c0d0341d1100609141d80e10700c1200c1031030001804000c41d28050103072846148086a80d401100e24075034010b555264140244c5050121140000e0b46032076a95020324804614081629520005482d00800061440322050304451070080c0346405800c0504034402903030028004102c8082054442c10a001d100445003800310380b00304003400002d6200000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 132853812 1250 132852562 132852583
    0x50409080c0f01142a04030305070201020c190b03060a080a05030304060c09150f0c0212030c1204030503091c0c0e04030807031e020c0a050102041514090d02010e03010e 74
    0x303165032100010210346080c03a50901488203107030304248080c45100350607002d45030002055864003101d40300c519010044040c0c40c0c41220600c0501040020916401c000108441d52003642516102043c0c030081051441101e030015000040d125024003a0850a600458200c80f0080030501440c1d5120182d41c5082c1c4590402c8030350390004418482008298010700031101c066082604009051241c2e83e00c04448444880040101700d200c02d140450041d048540701d141c019203000013001c0c3c040ca05541c0c03a4806601240c1034850312150130415171103001540d00783c81c0e02802440c03505001c8410048038a9040b0b40014407440a002c030314000540170040c04000f007640721001d204070b141c00d0402511341780d001401e035020b050802c0c24020341c980425000451000001a0040c3c8540e0f0032910b542c503140b4080d40c020003562001501080409603c0c0564468114555404548100c1261140814001c10356642d810040c064104c0340158000c040400518001400006040c880c0c054440e18103c0c0030203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 132855062 1250 132853812 132853823
    0x70603020c120301050f040f0e070603020a200c04090312140714030618190203040b01080c01090308030105060306010507120e030d02010b010207030212150106121d0303070c0c050409 80
    0xe203020050030502251038810042c0b905141150f00d04004911580d503410017292085603101c64040351078a40b030f808000210100070403500e220361103420280003588040d910b480402e4214541c5081190076200860340d5000000160080b00c40e98018040644001541181405800b0000b22004001c512400352100300a487c41c440701e050003000502203c00001c0202c903842d01c10410420240c542d48042181090b900b00030000d1070703640490355504d6200550307494187c0b500000910052018400b1500d040e00c40003030a0307540410b4081c0055441c200140700040582000348010071551800b20061580803a060521601d45020b83c0d9405105401e404850004100c02003680200750408200219000350070380020000f823090070001130750719600742c44001d03c22204100d44080750001809500302614406141e4000703961641d00c090301500304103050306c110740c0c035000010981425040c0710300384007006e000246280d070701e070804d00b101c008403100e1054605281c02c04000407540c540e44102c1030f06500a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 132856312 1250 132855062 132855067
    0x91701021e130b090d0f031b11030601120f080a18080f060703110714011103180d0525031e05040504050a02131e080607110f0708070603090204090507060302 69
    0x146000342c0007041e42d00025400c500074030240241c2d4640050180b002030f0840703081c81c07150005140c01c49420001e0340c0200202030f007101010040101541c08091892811410703030310341d681c850340400c50406440308080c080c01c19440c4048041071040000b812040801e280c1041e10926041c0303082c0804103582c5c8081c43c5980054005410741034244495070700000b6a19040c801c014403801e80c0401030080c9800900280d4001d0900200c40c1c400354414901e01038000c2e00d0507101d1a0281c417030b4181c100d5001c40080c1078050f145000309940c0c4144110f0704100300d80c130405044e003000110480c44418040e50103d090050403042c2002d00181002441d24a1906503074442d561410310b0141301c140c450107071140815038014440751910101d941000000e03a9042c4818485a00d001c10701c801c4203e185a115940c00e00600c0140020355a1045000803003521301c10444103803001c400061903940004e8803408001c3c0c1c00c00c20051001e01d11035040040784900090020a0008803501c45908010380c5501180220703a00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 132857562 1250 132856312 132856327
    0x30b0603010e0a1d0d050a0302070c030b0f010b0c0303010608041b03060f060506040302030606041e050a0504140a1205030901021b030307110a031706041d1501090903091701021e 78
    0x2607008002c8440c2100300c44c50b24000100d00318594074858030103c0e0041c03000200f0301005281c441c0c2e06488095030003d00070f034030032666030400e5006c801c8107540740c80b080d403c80d00000c83c040019108541942042c540110720b16032038400100d8060401600480f80300700880a99202181c80b20421000b845c040c01c1d00050811410700c0d54030456181c0c1d8400c1e1f019450a000030005650046140c9500c00302c155004900454120002d20310300030f07948004a0014075010038000d1701140369001c0d6100e18800c0d40b0246000b01052003031075940222000091010000320810003910b80300d0310296800c0110b4400241c100504180b0250506100140c814041c2d8000320401c280242d00400300c003055030461028100c0b55140b0f4900901c44102c0d01021000c480001d03002c907419846591020380040000c00e60480c0c40c00c241c0e455030340c0703d0300c243c140380481000010002c03840ea103461081c2040541d1540350407011364500035030b804d280e42c030f40005840355542c00e0040c00303081d481022050300c10041254005c4d03580d859 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 132858812 1250 132857562 132857581
    0x31902030702010c09170a060e1e01060914060d240207030809070f0b0f0a0203091e01030506040501080a02090c07060528020a120e0f0712020a050405060603040210030b0603010e 78
    0x2046c4d010520000e0030001903124100041010049141c000401042451414500a1400303070030711a40380e0501c4c000c0c10381044010065004005841241c07000f03210b0803030340c044101c400d04801d65480740c1c424900c10300b800000d0142241481081c150141d042070a1980c00c20f104102e0304206c106a001c50344c8401080382c031100510881000c1c29480752040c0b51030341442c1e074540c59030180c00b005500c98100040c010b41e03118001c20582d002550000c00440c2507000074000b4514590540040e14080fa040a022a01e0b40c03038030303010741da040c2d8404100500d80780600d9000c02403030180250803d020b50404008501c0812a54002e00d44646000001d1101c0890020030fa8100700f9498504001b680f84140155040f8a0303010030420102c4240034008505504440038490601c22007100b4200c081c41802d00004040c0501c1800c0c0030628000c46121821f2550b0380b06200c15100111401540400104005070041ca410324640a0940c040c0c600000d00056038400726445030f000307030071139a00c1064040410103c4c04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 132860062 1250 132858812 132858827
    0x140d09030809011a120a020901090204180e0606010f05090607030908060a05040c05010503090f0d02210f0a05030907080303270f060106080705090306040f122102031902030702010c 79
    0x807400208061900c400c141142c10240a1105101d61041c4403401d080d090700b0080010200d4004148c0e0903196999010a80250f1007072040340c84522030009040500d000e9449000c00541c1c50700c1c00740110752342d01e000448c2c28281018140060003001d01155426031120350140500e50300c652180c03005642050f0020749420030080c150034078a403e00c0f00700400644c116042d4001c44400303003096034980e02c40001076424040c2d9440380160522442400102d40303a400900700c440611000405050741c50f40e44840c21643c4070300c400030071281c40c040061840a902c540001d42d4042d480c88181d501c03481e2070310b8a03070381583c1c020307a111810401e000404480740784c015800010603c3c6c0480041490140300c124041d00d44505200d481c1c1070200590000301410b019004031802c0050003002e4a0042c1340c07600e040c040584044400752030107041c1d8607403554000d000c2c03c01d1103c1540b40030b82c18800c030340001410030043d62008210742055001d4031000800307081d40b400a980101ca141d0000300d103900420a00400b8135 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 132861312 1250 132860062 132860071
    0x8010b01091205030403060f0b0303210105041406060703170906060a0e01030f030c03181d1509010b0d06050a06050c0d02030922090f050303010f0501030603030f03020307140d090308 80
    0x40c950540c0c02c20010300c0020460301140d60180c0d0108442c0d08004030480140301200ba02901400001558081c1100c41c0c0d01c03070001c40c461040001c0b01c698070b5009000496840c00e51041c05000348002103081d500d480d002401c802031080c50f03c130300180304100f03070356051a0b001c3e903050103036904c00c1c024031013945031111540d4081c00301010520b1440d851915102c504401300d040c090306001040348842c0515103d400e0035005241c01d0003008811a603030b640c03100780201400d0403100300110590041030301250b0100788202180b000410280e020390030603400c0c1005900c145e0240c50b4042d6500400a02d81d214101158000c000c1c0e502c031151580b1440070001c3c01c001104c3c1011b01150001c00c081201961808100050140703500000d404448031b5185810061450400140002c40740e4140304080000c008000c1d81a5140c0340840c001196449006400fa42c0c1d41c1e00000703010075460050200490701c254051503120304d01c0c1c6002d1010790880c00030b80071158048601400d2103a12456a142030582218585402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 132862562 1250 132861312 132861329
    0x130c180515040504050712060b07020909060601080105063009190b011e050a03140d021504031d0405150411040308070f150c0c020a21120908010608010b0109 69
    0x209441d04030310802074840e034003840c0c1c8155560004a03507030606c40c4c801507012642814082008544410365800c903901301240032442594410002403a0744800701304c00d8001c3c181a100c5250590a00c6c08000315a000445524444440341d041d682c90690340d50b055044041d0880c060364140c0c10b154050600f0121000d0011624a50500d640c80000706441e01d04d90469104150700c54080e040b02c041d046010805911455008004d02008000e001c03482420140b8070008200b226085522090281d803600d458002c9072606129050010f80401e00414061100d61600c40034400c440c00c0e54000101224030583e02450907031600001d40000b4206489811070b01d514840c076060030075145a50345282846103000050050200c0d00030352007046a250344844003c0c0c1c602034248100c0361501030041c6615664101a4490100403a00054101d14800c41c100c0e200100c1c110441e54880c10b845900007105013142110802c41d030b0360f10010b003050003031081c0c102800b803806c008034000900c40f00040031030300250400c555 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 132863812 1250 132862562 132862579
    0x30d15062d180f080c04060f0f0506090103090b07021c1d1504080d111203162d020307050115080318030a0b0a0c020f120409050402130c1805 62
    0x692002680441d540c0030461424664080a0400d0310302d481400340e00105404003190b60120303501d280843d42041500703040d41d040150a54449050310354100354810341ca15000030380014080c40c01c00e4070040c11961410705000c250362883d0b07034815440030411160980141c00400c0070000e032601d06031282c280c1e08014034218042c080a41d003103448078203802c4005440303040c4072110040341010300810f440082ca40d42007601e1042101c4170014010040750422100c42e030164080b0442c0c02107050003501e0268600342c0899030380d40c90000013620969004a2605d0452030204102c0b076290006002000080c001c60380515100c501c030307203002429288040c0346c0c140d81a8140f0420711110200100359150640200446c114210354071010a052804a660150128001c0800c1004104185c2c02142041100d0303422111005a000761b5640c079090940d529903540c00342040f04000b00e9000d03800c19500b0500051010303070645050190501119132607418000810802145102000c00007038080b0001c000c182c82682 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 132865062 1250 132863812 132863867
    0xc0906040b0d150815060d060e060403020c040501060801050108042105070203060f070e0d060237020106030201081603110d05040b0705030702070918020a030503090f0406050609040e030d1506 84
    0x6850382071405000c45c4099059000801d0741d40c0e04100021440c0d00031008000102c20100103d480c0c8000f150306801611506907060013505040c400e260481c1d03a40d944122541c0d09040c0110703401d00003c2d00c1135400003101c2e4100760403c40013041501c0e1601aa88030345030386507168814141002802001c000d5640d17000010400411b803c006145004c1c001111900c0001407a440c024009000b96202030b005481e041021490001c0c0c1c648494002c00040d144813040c01d01c0c0701c1412801e0380e005000080c0014444000b203000404440d650f5040c515103420082000b822000c032a2880c0d82100300008006034a900c14003050103013240400b500540c151610928628203041c01a50f05d00f400d02c00c002c040360343c07881c0082c210740d0010100880c80368020301d03801000e696420903a6a03500020b1941d840707800f00e50403040700d034031b4544030f00c50827180c020300782c2c81c03c0108110800000f0940d000f250946400100803e85030400b0611a40d0304401d550340c5240e130500e041880040c502d444003460120140e4080c500c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 132866312 1250 132865062 132865079
    0x90b0d020d110d0c031a09010b0a05060a12050f040c060207121e080a03050114031b040905070f03050303040c062d050c0109050102030a0e010606170c0906040b0d15 72
    0x1d403211030700900703a11110b81558001c20038000070f00501801500f203044001c0204600a040c84034502140c9000c82c5042d116140f0355400c80304504000b42e440a50010304000d00e040841c06444072100b07500b011042e0f4a0401054029580304941c80380300282590200404c0045508080016004030701c0240081800d24070001c01058502501034803060928020642c40c00d5035206041c40150700c4402c0e43d03200c80140c400540541003e0103000a081d03641030303665441c4c2c2400103001c4481c1001c142200d070442d080f80b05002c000c2016050690f82030040d0703000442c0000c3c0304d180e0350000314032820085030b032441d007410142d51200c6141c100a04120444070540ca0b1702c0259103100e00f24100c40690740302c4c1c4144050068070380d0311580103902580d5007001e0b019024844198003551007030090580c08d100040303800599034204c03041406000f01052521a05078450181e0101d2541c0c807250031180546000107105c0001c0c200d030042ea00a5295080c00503005c2c19240040c0030b600c50924610701100e01e22030410226 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 132867562 1250 132866312 132866329
    0xc0302030115110307081b100b061e090301090507090e1605060a020a0605070207060801050901081f0207080706061404060b0a030f0b09041209060807020d0f030e0f07090b0d02 77
    0x4100708100d01d11401d640c40e5080c0304171210700d9072110b142e950b1901c4010340801440501100d24519004070007403010010307101e01900700000340040c6000e140c8a41540c1c0a24500340b20f070640c8010203803c0c040e005c11502c1c00d200380300c9070b9400380c2c00070040c0d00d16240030390f4282c50110080303903000d81003c8074859000c240f5041a81c15541d048600c10749403080c40c9030891501030502005040603040000b0b100031a500406c1100584000b940c0c0d800d11a13807281b05200f103040082c80313022a141d200364500307000c142486911440c01580010054940035141c4c940c103006070403858040d43c10b00e685010030019441040b10450091100760b0701404158a00590642640035455030a4245600d810041b01002050351004c051007100915071403030b50400741400c500761480d81c011900450310004c001700b45a8007810b407492040c040c0e0f40c020100700360740403400c480c155148130010302416150070200300189820b010040103100310304020f10140b49011081c8059544c0e40000724002c4413140030070341c05610b80313004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 132868812 1250 132867562 132867599
    0x20909012715110405120a020d020402090a0b07050d0f0c1101031a0618100c080412030c050d02010f0609020906030f06010c08040b030601020d0f021908040f080a060c03020301 77
    0x61110300da09505100700081041c00c80101031914041051a0030350f10310002d401034501c161081200703101840f4006942e0303055035001075405620145d02200500d040e400402c84080044d081064403a6580f001700c1c1d058220720ba00311901d40219421494480d4442c10210b1203450500d402000b01e03000c0d441c0d52021513420920704e810580c45e00e00208464a400340340c40390748a40502607507176500c030f0320702c160050288240d4481d00c6405105002c804003845059030360b1540d904400311078600f83c0f0382096a626541503400423818485020168804a6418403401501c821a80c00106240310034404503000c4414a8203c130f5207940c41845050b01350744a510a4a900c8212044004010f07118000161007110a015008002038800580812001c0102c0c020b980130341d100703800b1103420680716402503a40c00540341810005034840c0d01e050000941c0940000d004500504103140303810b4607840300e0094036040340c2249500f5840403a6080c10005140702d03115150140e440c0450655040c4911038401d9000d894 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 132870062 1250 132868812 132868871
    0x309040f0c1e0504081906050606070c150212070803060a1e0303050904060f030309030606060c0b060105030612030301080f06010905100b03090102090402041202010806030a1110020f0d080402090901 87
    0x5600c2c210900600403130b8081c281a008654015032603019984030011743c0d0f841110440d0400740401c0c01070034404181c40384c1d241d00540101280341000c507031564003031403440104114441d10382e01502184030310b40202041c0307010707401c1e4a90b42e280180900000280c20340c0f04a641c0040080c00c0d1810740d41c050410b06c2500d07031510303007981c0d0751082d0400a40030b0310080d04012115070554400104154000385400200e0380300d000140407283d0390b00029960b1315001c100280070511107200185041d0300c11001503034469070090070b46c5451000c000149186030001d0304a01ca0550088000005100c8204401401041c4150302402103103001e0016003000400b912a00084050100201300003150a4040e03484107407000c7d1045440d00e54071000d820211280c000284e02054101c00440c00501b000b2503811403e0340c22070790300009401c10f08207010b07121007a229884114050188038000d00f000501101103090b20a075240a05803c05004125692101411085160b85003510044000c07091100a00c40f080340d14 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 132871312 1250 132870062 132870107
    0x201050d0b0a080337050d0507050d05010b0a02010e0613020d020d06020c010c0e040213180b0301020c010603030215010608070e0409080307020615030718020705010b030a050309040f0c 81
    0x2c200d01942e250000c1445003c003041c0c18003001c03400601a46000b02c1c08480c0f51040c4c954000c9400c180000c2e02c2442c0000b43d0811441c4203101284c0c12894020805251080c501041502e40c107086030406c0e0000040100c0010b90701c00d1350b6909001e040481c1885070090704407030a1450110f400b103510900000d010710290724185e025562120101036030700b81c1200c404d55580381c2d0441d0440c000c00ca16a0f040d804a40c1940a0240c3d5041c00e00c01d942ca00201c902059285605004001c008081c03a00c0010400913190b801c5807840703032800e001401842c8101c00000c1000342c1180740113400c080340c500344044605880341c01000000c1e4007401440c1c0058803420081d01c3c0044172004103000d040300380800791503000000140225181e000840601c81c508000c40305030180000c07030425442c0c208521078035980003100c8112200003071641d4000c0800d079224000000700d5909060200313040c5000d80c007040d5401e420206802401c0c1c2040d0084544074a120a1300b044031508020340500b0a00c00c00d05030024030b103d003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 132872562 1250 132871312 132871331
    0xa1b240c090e090309030d020102041a121b090409030c0204110f0f03070c0f0f110a08030a110c090108150f0f0c0a03060e092b080705070302010915050f0609040201050d 74
    0xd00840e0701c0245d01030140da4203c44060400b80c040d5000c3c1c0300f1160144c1002d1028003140000405846003200105c0c841c010304e881e114a04000c0340c0791145099000c0382c0c20402a1a182d881d4800d00000521131f4481200807443c9004200c00c449180004070340b030141c1004090252160002141d20940303a2841c5a43c9940399044121108828110300802e000d10240da0542404600301c5807031513051284451810709103d81c03090113080311852180160940c010300054244d14041c03030000c0ea803500c51038122134a09280400040003800700b07030300503080da4000540d00030000940b844866804142c02031040f0281c00c05080304601008007c0c0070001d03410000c0b90070116588260410304c01000c582d11104540e040c46844141c032689041000c001350803002d00d00060300b400b1403403a00c100c42129200c3c21603680d501081a2a02e501c40d140c114115503032560380000050501c14109189403010800240303070b00d0704c0c40300d43c442c2b540041c020500c5032040b60b08200060307030300c0313411a0141040c603240803404400d2b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 132873812 1250 132872562 132872581
    0xf180f0605160c030c080606040e0304090c110303070f0207120201020307032006040809031005100501050f220311121216020409151b050304080a1b240c090e 69
    0x410042034030440d10f40c000107010380034560790b09541e503044c29664580c54040402048907801c4484039140c0c0c10130b10003002240c603660300800310001c4504040000042240304242581d03c122500f401090b540b0003c06401a810441c5502400c4020110783d4140c0291300003035924000d881008040003500e440382040c0180151082096204c0401210302c1c5084c10316100ca1980c101d20b40060091040741c2580508010354081c55001b411104442040117040c4001124913500c40c0190088121342044000309000e40a40c0303d01540e210f0800681085007145449803020200d072000520401140140c2120b09a0110300c40c0782c0a000b80e0080c9a4030b141d030070b40c0300c8845426940069401451701e2070003402d0202c20221482005140c490030004410204e405984850501a4680c0040d406100250008400b0801843c40d03640909044c007490b50304900d0749100d8116440211400042000c9880400e800c5010708050314a9514003400f1900045d90000c0c5078603040c1c41690900268140031070003040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 132875062 1250 132873812 132873847
    0x31308090a1d090d05070206030406090204090209070f0e04060b0901080924010504150305060c09011704080a03050106030509030f1308010c090f0b0909040204150503030a0f180f0605 80
    0x480810202400706112024260104100c0f401c24540c0900041d062a081c8101c0031110480d03030003044a421900e450311000002c00805008980095540b01d407140940c0d50541e14034400c02d2291399425136804056030003084c401c1c240315410301441c1004000e200c8241c5080076a9000c0c0801e2078505490340c1d80c0c0341140c0c03516503a9aa40701c1803183c00205400c403402c2c0ca100f0981600c0050341d0501c490b02c50034020169858440c8406845500100e0100380700c10308400c010030100ba030525128611001080001c00c140c0d10981d000c490030000003a5082c0c3e11034050041c81c5c0188a40d0808102516210340f07541c0c4c0f81d2141c401c0380005010006941070b00840c0403000d030301c05040c0b0000200800801c40a001c0d00d050903501a60f20451200c520009103d20442c0880e0361982e030160034800141c6442d800d010140a02e09042d43c805a0810f80208142c0c60810103000c07114043d0b6102c50b000c0303908000160003413500785401c1e039400ba14103806114400c80f56541c01c00726511440c080780e0f5000b442c004460101c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 132876312 1250 132875062 132875069
    0x307020d0624090614100206010605071103060109060302030c0f03070b0d110301080705030f1c05030c072a0608040807171b0109060b040209010c02040b060714061803031308090a 78
    0x40c0c2c1c40012419800a40c032020907a03826807032145054906008000b46090b0481240c001a03104500521060b4882e001814a16100309000810b58a0b070100003070404600360059240c2c0b50f0340da04e0030070561038100b0005a09540560f442102d103010100030a803101e12030701039030303460b40d00000c1e1400541072294040c1c155082c080c04225103958503040d4080d2203007034030300c01c19101344503c0001101d2030034049502c200c02503090507140c9880003d4101518076810082080a42c03413130900030000480d00d0b440680003a11130580c1100c19040ca501800641312643c0d40040d004c0000c1d0004020004920001716480360b07401c215000940013074141070074000c2c41503416013460f040d0140d45102882105420821566104520501c414640602408120f010b07130369510f030004004003241000342c100b40c0d1020001d100080c1a00b4500480f5882c0d110040841c0ca43e03821403a44400200440b4044850b2224620400400610b155040c0f60580d13400c4030f0410b9101420480340051141c0d4142d9403d406034006 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 132877562 1250 132876312 132876371
    0xf1206040501050106020c03030c0d08060f06181f050301030f050f0a0c0e0a0e100b010e0a060e100203030705070803070905090906100503210c010b0924030307020d06 73
    0xa500d42460324074040c00c1c080c0b2038007002d4803c848407c0708510b00441a100080a590003c104840c0b0f4003400302c800c000c1c051b01c80b640000543d200c85166407141c8004055030040d80681440d0014102e0034000e1201500300d44180014012020f89481070717104040307a045a0300240c00680294540c1086410200e6400e189100d42c860000604100501010710f43d00300c4400c03208240c950394075210600152138140324808101e4000701419800a00700c3d51007080d601c034041c500707810120140008140c4d10fa140341c202e400842c0301c0003d110060311308002d4145944149101440c1141055200500603001d00c990003007101801100240c40700d4400e83c0d17200020000100483d2650500e1613403d61140d80c02d903100b60b03550900b041c0104c0c241c01c1c0015010f6500040903003070303e075585020b0038020207274100d00c010703038159503e6a141002c3d56950103500c90258008401c9070025211005c00700f4030400000d60000e0080c1c00502041c80560f40f04074804245641000000c5214050404888800400d1401d01480e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 132878812 1250 132877562 132877573
    0x504030906030c020c0d030f0c050d03091106040b04050d1b060f12050c040b07110415050a0602012007060e100204050a050603100618150c11040e06060f12 68
    0x14554005a814101c54442d18108696000c04604903100c040d82114560030101d140b03c6c2c02e0002e07100311902040f0f075403d440c0c20408040d19540b010304102e081d60311480007980341d000c49018001c02000b4010b500030100c0300103140c02d00e82000081117004902c201885500d000c640360040c0200a1450301503e601e8007510a2890384a2101420055420181900003a050035011240c6d09591103501d004140002c50f0380d082921b4600c44034820388c040d0000711800a803171103500c03001d47c0703e90042442a14a03000d00001d0380b410042030150360030300340d1301150442e81400302c03490b20440b2103a441550036518282079540c440c0c1504010f03015002054612602d440b0b052003c06007101c25074090300984400305d5a42c0e40495480e010004540020b50f01307922080440700042140a008a55241e2056404440303c4401a0344021404580c056440c1c0e8101155800c03001108014070507800100082044508008400384041100d0b0b4a0a00070b01c045d001d079096942407000e664034a5403203040409800300f06d03203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 132880062 1250 132878812 132878821
    0x503071107032303160b0a390801060f050f04031a01080d020a1709031905071e03030f0f0201020d0608010e061608070806010e04020406020303090c0a05150d0f05 71
    0x202208824683d15a05807025401c0ca0041d500c00b10444074450501030a039102e944980d116035402000107000340961a607114688413103142210500700500d07842e00c400740344100c0503290f0a1058482c060801c410030550b00010712006d41c00003942e00042e07015140c030645420120a0040d000e00c1983c00c081c20012040345000e12040c0510020740c140d0342260f00303884d500c0790304072010b907a00c105007000140010703034140c0b214502004a002034004060000c044500510412001207411101104155141d030041201070100422003048200045000c0360000025031031510020100c091154010f801c0001007641003c07564802d40544122070124403042280075911143d10740240110f11941e0030600501c0c0000d8080051170b0720700215004507403184101585c1e940b000b1284040c0003403681d41031101852842c0c9294071548094000b13010141c00960b940d0415100c0d8a10b002803031046144039102c044418021130b210310a942e1400501d00c804580c8480040300c054020304030010720916024501030802 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 132881312 1250 132880062 132880073
    0xf17090303041a1303081302040e0a030e19050918010e010e0f01151a04081006030311120a110111130303080c09030a0f030e19211101050307110703 65
    0x750b0085100e054008030100d403090b19108801d204560715070103500b4401510340421300440c041c6a104007000d4190200c44026030000301210204810000700c0e9003c07a900c0000c05410203690200307c0300031242c00c18009000315134440c0c0c1d204c560003079038000c00240c0040f034121a940c508140b901c200900c02800220000c0c231541d40244048501c0d8076080c8103030704240001e4441880f0f010b40c2e02c905021903a40341420441e544408504006612408040403c00001e8246050102020000c040e5030b000c180e040c60742c01c0007403541c2c02a800801d619046000f11310040000001211440f00e1a410450b2540c50307001d00b402e0041440d13a2402c5014840000c10104041c000c1e9100e1090700e00c20b46440e100d41c0ca072801c3c102003502600c0d0a8903055400000c3c100c1c00f00c3e20040e95054814807038030f0300303101c029080c201181c2702c005400b01050071647c01560510041d207282d00240010080c1c48181c0440c180307e919800564a0b000322402d05202000010401c034078820741980760046400781c1240d4616a80e860039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 132882562 1250 132881312 132881317
    0x60c24060a140901030305070f0b15090703020a1d04060f03080a080f130f080702040f060302030c0102010e190f050a05060a060b04060507060b01050c0a0803010312030504030207060f170903 83
    0x424031489107400301080001a0b420407000c0c0a4001c0c0411440c0c1c0e09580d020342d4264004142914006a00b48050340003d64112101d4404c0d124842c2d181d28204044080c402e141c04050f00e02d03001d040c01030180d40b90b210fa21040c200221102103103504503403800d40011074014290360300700021910b0038078404030a00c41c6c00d400906801c0e117039560304d00040ea1040c01d040c1010b1019030318030219243c460300d9080803880206a0f0880c5900480c402440c0559590014084485d450f2035001801e8072031a040042d8a018001d1078245242070000b40081007003c10910744520400000d00c080c3d2414200c050180941184103145035688013048410704120342c24620f80d11320007110f5607800c4601340400402c28004007400d850071500c0540721030782003031002d64804020305840510a070401200b4030154a511a08001181e4100e015842d5590340c0c0d411402c1c118490780040649405050510f002c0c800025400540300007150918500100d0281c0241030450700540d00d1046452500d4034130041c807103c00e80c00f000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 132883812 1250 132882562 132882571
    0xf020f0409090b011d040f031707211a120319051b030f0d020306012705040b0a0503060106050d0209100932010509031e0102091201110702060c24 64
    0x1464207241e03a9400e0364214804210104005c1c154003440401d00080c804611f203c0c02034403a08004007108018455418000030440d0040d0004822058604441a10030780c0c10440d032005110a00001c40b80101c00c4081c00320744c07000d00e40141014000e504c00c050051050300c540c05200d03030707204400d40c19100b001452074104044862140d8010035540c4c44a030340000071282c0d012800c4c80541d003040288005d403c001d4100411203810302a80e80548100150600710002d482045c0103610111141030809000c1200d4801840302c3c001c00d4136030014041c5079000142d050450703a09151581d6100300034031184019000d0100c0442e049000e16000d40501c2e90062240b00503180340f0f0034110a00131040c3c0c03000c0c001480360744145660941c0e581200320194072a400501c10301001404847d44012990104420145600c600100c00d035800320b0901d030306107417825014181812440c000d00000c031204000b0707002c6120b0b464000b480350304c000554146480f01408a503201c9008090300603140d84501124602c0400d00701c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 132885062 1250 132883812 132883823
    0x61903050a08070212010c0807200607050c070e01050a0905192909040b040b06030304030507140102010b1807080417070b0a05090114130507030c180b0406030f03030f020f040909 78
    0x245d072105040414032661f440440c240d078505110752586201640c00c050030100014104007407048181c0302503020440d10b80241d0f415130711030750b81e050f11901c19824040c4603000307080000182401003059a8854020b001600ccc85110005050b031190309a100310003501580d421007d6080c800c890071100c502c08a454203143c07501a0b04820542081c080103030301074040361300074030b20b10520010601149215140d607900c100050201c034034294894a569107466141ea00080281c02c000c8400c082550342801401c005c1c1d40d0545041000c020103410f6030702101c00060076a400c100c14040003c050008480007101c1c3d02ca904142c90b9590361690518040301e440c00c6520714015410300010a204220522800d1328100b040c0c182d140b0b058486c2c0340740801d80c613010380301560f0780d1142c0740010011030014640b450052001c0d5030440007402c04d00c403074042910740c0c2e940b065104902c1e1142c204089050309100040c0390342c0c54600040c8203a02000300304001d010b8400382d03004c0158040360215510105a1001c2100c501a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 132886312 1250 132885062 132885079
    0xa180b09010215040f0f14120c1903091802070c06050306101e0516080408060709050d080301050d06140a06090f05040206040e0403030b030a0b01090e07050108061903050a080702 78
    0x740c1c000f0085240555008000061001a0b040801c80310050b14150522900384040d010484030300305441c01c040012001c6c4203c800160310a281d5800b080b00002c42e108480c1c913a0a900210740b40502411030070300c00c2015403040c1c24421072400a1070760440e175540b41d1000c01401441d413111001842c039042110202d00540c030500c50351001c00d00502155001019410300d480704240c21001c122265080786824400481401c10702000103a0140c0180025041000c001c0c9114504102d008055020560025000d40080101d44001c6003140080740d041d5407081d115500e84d03040c107280060083c00000c4160a80c81480002e029100f100d5400010442d0301c51201404290f450400d52002c40c1c1d01500d000758040070800c000c01850024800d3300c1e038418003030700303001510055010100c0c1c1030201080044580e4200080140b10140181c0310740c22400c00440c00401e21135007084006400628040c01c414400c404034040021441e040c12814405541d0100c00d94091710581c0c42c0072645500060422849030449 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 132887562 1250 132886312 132886333
    0x60302030f060103060b090105092b050601060f0e0f03100c0f030e010204120219120b0f220b090a14030d0e0d0c0201080a0f1d010b1c0204020a180b090102 68
    0xe4003845c1c1c2590005417041d071400f001200103540e26071202942c250024a451100e8a40d60028982c1c000f800c50301c142c1050304007002d803405600705001600701000b80840584142c1c4102c0c0d1100350149446400d403484041800c1041c0001e140c800aa03140317034282c60a0051221041d40d100c0c94020b045281c9840c20b101142440b0100c500780d0180340900340d43d5101084000000d440c02c14429001c0030840c0c010310170340c3da8440d01c080341e1402900742c05482a41000d0180041c2400c1c1d01a003590051030301d580400130034090705411061010b541070140420160b400485e03040785003802005011680030304c907641c00801c0e4080c04c0f6180e41203440d400c0c04491400d00f9600041801046d048280450343d03541c207421072241d500648600802510300c3c0e04490703844461101201c19445201c040400c10700003050390a41c140b500d1801e544000000138003404008460788520640b180485840b250704481c050385a0544410403694443e4655207901c0c170082034a000108105032070300400c01c01c8020307400c2d03804a844 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 132888812 1250 132887562 132887567
    0xc0a050d0b190905030c0a03080703050c0702010e1f03060311010306031e0501020d0203040503030a1109030d260c040f080610030303090501060305030a210b1c0f0c060302030f0601 79
    0x289000280404120100140071005400800007002c1c0c1d980c1c1c0c00143d0480749440301071440e005a038044049600002070401495044008154003002c0c83c541400780d80344c914640e82d828000c8c024003c0c144039100c40304464a0381c40790792010040c9900d921140d188109010010058003c80c030003074480c80b940804a0480d940700f4054542a0b81d0480f891381c8a004a80100d1101b4110f00803080e503c555007400080d035644042d00003107000d203014400564807400e01c05d0171001180c1d100d03601c2c20b111500c2003256084079280801e00102c80d0032981000c05650b480c40c400b208400c101c8109c40000e180501041080005844000d08243c0b0b0082c0ca500300100e45403601d41e540c415058400410075078100400704002442a000034402900c500004039541d0745d660340e079900d55000f034040c000104085144951114081000e4a486001c140c1c0d42441510b0044021070b1201d0b0704280c400d001080c2d00c40d040c41c1030203100581c1c40e80c071540c098542c8400b1956004018000d4109075036800cac0060a41010840d29171 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 132890062 1250 132888812 132888829
    0x405011401020703140a0c03061e0b03060c07030c020406090207051903140703050c01050703020d0f14040f0c080a0f021f02060c180301050406200f090d030c0b090c0a05 74
    0x403010780042c43d040d42151902440043c14900203c96480b07594100300000c0c4141c030402000318498080800d1f4602a5030548031114240048400006d05c0c01179404003e0740c0000d0180d822070014040c80340d8440c450308048070000c410715000303904103040050000d00c0010326030050400c4c032300071402d46201886920071046100701d68a400b030f001030f01c6031680502d06140322004000c0302d031003810700f00c3c0303170580006600d800d50f002143d02c400480c0c0d0100e04504100601e0040074142e4040580400c2001840e0031401a2028003420241010032074442c920104041c0c5c08040300a0300c078a400315000d25041e854855101059080200e005058007540d614004a908000080404440d0043e29480d5600d62088403250000c245003205201850000c030340685003031042a015a00031603012818020078500020303502d6031039220040f012020010411301c0c1d200402511442e82c0d0071907034802180d5041c18101d940c448010130140020150406000708402d00140208001c1404e86042000300daa850800c250350 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 132891312 1250 132890062 132890099
    0xc03040503070201030b01030b130501051201060602100b04021e03071704020f010311091002030405040e0d05040603020d090614061306140d0c0f0602060702060606030c040b0711130b040501 83
    0xd500030b002050040d802608030405440040c540091228807901c001014030101c60b820b481c0c0e4030394420050186080059480c903242d04100000d002e442d01e08000250790b06018810340b0519a82d801008800d540c49804541d14041c0e0b044000b030307050724510300c60404c40d8010381d4640040344100503080014010500540d204039002491010207442e0302e001900584000d09100c3c00c6800c0c20400c881c0a03654031904002c407030b009580110344907414801400110b40b000942e8494030303400301c41c0000c003080c2d210044070203a4a10b454050b03114005031200101914112000030201c60800c0e50301c5044030502007000e44550000c0380e8281d2000c94008050048800600031502c015441c281e40c5691805d0695040790000d00c507400440015659030141d5690500a402450042c2c20032018070118903410013803643c1207041110150b145040414204401e4406ca104450b4070300c00c003140d02d80a20031394040340d5803240e0000d811840a042c1041151004144c4e00c1c205a105620700b41c0040343c0d4140f00341100640 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 132892562 1250 132891312 132891323
    0x1509030b0105040207060608120a120902100f02010908041203030b0a0302010905010c050705151c05010806181f0b01020114060d020603040f061505010e012c0a03050a0b06090c0304 79
    0xc0d64203203010f201c080e41c06150240d9015440c2d00b0700042c4002d00308030013582d090341070111701d4403102d0100000f020b6101e072400d818901410301038601d016030f4540703070710700307000c0c4040c1c181103040c0500090168007601c00740c0310103819908045800101c141c5110000b02c1100c1c0f0079130701006901b03c04070400024174003601000e030020b003070400140700741d5005845140d80703a03018804898009030b460780040c0762158125208103001c03102090ba080900c405034405010401250014440e541c1005501991000014025102c3d003c19555511507142c060204d0b1401446070701020091120b03042c00d1601a0003c0840c841c01503103889058120006030340c03603e074080d5900074014420150342c1d8081005542004c4d00030390351090018030f1800001c9081c4500a01028140150304a9038946400074100040c89031001e41402950342d03400480702d08400070304861403040c4510180f403401080118500c85041d4100500c1ca1155200101c180400d00100c0e030b2044a04079250400d6598220006c1c1c058001035038010038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 132893812 1250 132892562 132892583
    0x610031a100e100e0a2c0c010f030e010e0a120215130804080a0c090f0501080a02090702010605060c0f101104061128030f0305191109030601080304150903 68
    0xb014640c00c4160060003050841d0080f9485140351180c02809481032000e00e0f540305a440040c070000d440840061100d050500382d0800324242c1e0135101c00f440441c460400a407482d042400c02e0103548540300d51916007000700008445c6085040d995031100d0300a4a0f4000e6807282442800c0c40051004a62001000e58980d07645900040e0350310403102c2801110740850a20021030f41c150200060345030a801520108101442d0045070000c035000d0900d82d410081c104001072103a07400018082d6032982c1c0c141d490301c50503680d40008070f00400064008503403103880000e81c1c4960100000342c00040b5007900c000d8481150810340c2e104111000440c1d84401440305100030080e00b4002c01f210b5040c0703002201610310710103134036908031240d00c40080c48210b20200141c1c0c01050650100000070540780780d050070450303030914062500718110aa51060135507502c8030380030210a0182d00945003500000b800301c80340c03940c5801d03543d901c03a0460f009071145688031a2035a6003092044035108101ca070007060740c40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 132895062 1250 132893812 132893819
    0x1802130c0c080c120c0a0c060206070e010e1206070302072a0e180319020c010804020f0409020315070503010302180601120e0c15040906060305010312050c0a050610031a10 75
    0x140c3d00048041031a83c05111400050011102c0003000354005810140c0303c680380034074040d02039400b650410421980f0602c02c0180309038006030704c0d01503040242070018400d11004001107480203000c0064011340114000d1003104e60b0150040c003401c600c60300046e42491a52589041003502684165080c407010075020001900501c111681080c04001001108a000443c0a203544d21000c25220f603528017118032405c3c20340c1440486e4403100c0c24038006102d42410780001d082e8940401c0c80307521803941d552000b402c43d50104810b50071044281c48108540c905048050203030342092206074020072600040c01400c040d030131201407081c0d030144c4440040342d40b08110b400c01428107070700c3c0030b0f01403248618401a43c0d48a107803018040c1034000b1100d54846c1014009005d4540691107141418248001480083e6010b040d0b4030b02282c41d803902c19280c06010300c03864904007900c4000b4116009030000e02c010101520706580039a402102045020390424019480b848412201e1400c1100303902402d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 132896312 1250 132895062 132895073
    0x61803030c1112042c090601180b090c0a050705120919030b150117090a06180312020c03070803100f05010c050c0d170f090a06030e1209010c061802130c0c 68
    0x52540c001082c1a40e00100d03030605000c0c0a845c0503210441c140d8011401006452041c44416500341c66811080c001c001c0e03e400820903a41c4090b040701541c481c04605a220148076a00340d500c8550080125010b10240c4240110f4591145140c0c50143c007400008100b40c0c03d4014001040300d5001b0001d072a20390302c544003090410940c8078120b041090040c0101ca9094840394054002e40394200a0404082c40d450990100d40c0c05d4a24038000000905a0b030300404d0304940682400c10700c001c00075940f205116520f904621501400419048011045c05480c0481041000660307039240c3c042414142c40c1e8006581e40706d561131000f81164012078070b006050070b2180303801205d58810504410860125400c0343e240c2d0300a00039021902c000070440d42c01c0b51402082020007841981030411144219042e01c0d5100c0c0a00707080941c4440f0700041480b402e91150314a00c940a4200074104014481102020281051000f00303a10903403501100304004011841215000170041d140c5065088041daa0b8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 132897562 1250 132896312 132896339
    0xe03030406020f040e04150c020d0c06020304080409020406020a03020105011d1501090e0a0b190312051605011a1003151a090d030206010509010f0b03070c061803030c111204 76
    0x140702d0400d000f13001c00100b8001c03416003030340118410103038240f100780c80000010442e00c0d08080d2004661141105081d59504020b2a01c40e80307030000070241c3da0355034a083c00c102030710541d03100c80c4030340f40700080000c0c0c0b00750f0200702451441e10940c001d0001da640c4148032155660f000e84161030069441010522104d0f000c0380200034814107041c504592070362800c0d450728418044642001ca5529424038050514041c1080712942e180d030020410b01c1030450320303544405403070001008240540010307a160402030000740b88076021b41c0a0000e0120158450030444440039800501e0b001c0c10460320080145c60080c010805285001803078002031038540400803507004d00000984c0d15031001000400351079250041da00302a58080e400070105545004107000603500d0581c4020504040760405016264106003201e400600c103180c9480528194104a0000c0420b04c0c20190b000019207018410950160010341007050152100301a022580080d50b4941ca1020005100d840e01004148800442000d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 132898812 1250 132897562 132897577
    0x901030b0301140c18030f0d0e01021e100506061c0b13050c070b060114070204090809100801090b010906080105060f0c060f090c060a1e050d0f02040512010e0303040602 74
    0x704000c1040b072000360f00e654044d10513440c0a98000340b044100c1c0300400e07505013881c81c01e070010301e03440ca4410704140c0c803040da80380d0b204200300d00318841040070381c0300301700d0365450920507584816010380d82280e2039681c0311000e5003410041d0414000810b41d2a01805596284481c8540c20a80c01c0110714401d00610f000b8000c10360094002c00d040b0503041c030502ca220f1050b0303504022191344142e1800c2c081107102d0000c240314100308042002000304002001a00e18241c0c1c16100403645c400c0600e04101a80104d0b18400d801c00d05940313802601e0341d4030a02a81c100c600464040203d4500d1000444819025004101c0400d122200400113428201c005200020111400c10b00b0040850101400c0c1401902d10743d074070524030000d100c2d4240e000e02c40518000421181280380013900c0308040d19190044417010288416204134442e107900a00844060705003120f02040010750500d07001c0001c0d0080e026503030190043c0c030040c410001d01442074001450a2200460071a90b56941e40c8019510001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 132900062 1250 132898812 132898819
    0x82409061306121b0902040302150a030f0c0c030f02071511010b041103011d040f080d110c0a150203090c10110610060810050906040c1704080307020607140901030b 72
    0xc0b00090a01a82004040418031036444860700c880381440c0c075144400a50441011248100001c01c0103a462000c0e15a400f4061020036442d2584054103400a005041c02e41d5409820842c103113824562010706c04503101d1090301d0b40800d80300351a908aa45043c280a400000346202d0000714046000b90b4a60f03084001c444c00120300c000300000400d050b1004910442040071002c001405a41203c4031545100b461007080e000c100c0c030b481e885d8845102c5410030003507d10b83c4000751301003610b025604141c0e4030201c2d07140700030381d5400c912000035510101140241e500c1508644050381c0000c2034001c0341d00505421000f000c4510065042100f803074020302d076800c20301c18038403251034903231009102c6540302c1c40710120804000c2d8500360b03000d403580348020040c64140c45c1030b40017800703d40d503405011500020240d80000707100c031000c0701c140c8450300110f20410752000c0180800040005500c002c5119540907403c1e104070740c4405c9002d44690b1507400c084104814180070380244c0754403aa00103501c0e0350005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 132901312 1250 132900062 132900071
    0xc010f0e0406030f05070305060a02160b061903050c0418020307050906060418020307110307170904020f0c0c030d110c1c06050907030c23130b09070824090613 70
    0x20381d01c4c1c19071502d003c10300b2517031074201140400510000b402001d510404281081d03240a112041031101001c01c950300911100046010842c01d4552040c14840114100340081c1c1d5142c032402e18a039035034648602e841c4100d00f8040b80c24407110021440d107401c0c50340a00104681c034109400c10000c030340d00412094010006010000e629903142212501c048044000117a681c141031100621448410558070401d030702c104000c00026400d42d400a088132031031030742a07880d14680d07000600a40b084030710b0300044c1400401c003522802c0740030941c0c94105104908480248005003400d559000e82141d440d006900714080e841c0c15810180860101032101100031204407441d50f944108540c41070b2500002a0f000f00320034802c010030b0381d060002400c2e440c00c80030f5080056506020070159108905400f503400d1804a0000581c40e0704840f881c508000e000b89898a807405000305803610496800000382102d2858a984070145008425024406482d07030030990f85072001d1107003108696480908542d41c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 132902562 1250 132901312 132901319
    0x32a0d0e0f01020a15020408060105011b0b070504120809040b0a0e011202042901090501030e0c0607020607023a020a120318060f030e0313031212020301060801170c010f0e0406 77
    0x5e120803440e00d2101c482006072190f0503d0002c43c49c205058100ca81401968134100303014509892a035021b0701d0780003500d400280e46109041381ca80c010350f8030165450500080c06010054140081c159000050324100000ca0b83c00007000303041c03212442600d0060700154010310500030000c40d0402070b14000380000c01c10140070301000d1607103940e909411384038a011b000c0b00c048645c1d005e40008010a401d2900b40100001028044d451b0701d0007a05041c0300c0c002c001140d2046448440954118030f40040501040c1d903803040f0001c0c100000c0c020038001c07074002200c5601080b4400403513000401e030060719041c400f41c1020301c0c103c0c2c03000d0380d03440907014840e03400e1020441342c4d641c034020009030030f06503544048c2446840000d0140c1c0c0d40082c1403117442e0401e0243d04200020184200116608482050f91001c0420b00644c0c0d01c0d01e03a0380300c12100340c0c0000000300d070443c1c00050450403200e80c990441c0024040300170703041c0c41d030341d41080150014034410054103020303204a1004076005002880028510f54 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 132903812 1250 132902562 132902573
    0x308070f11130c081308160201020703021008060307090e120901030e010507110c0301021e0307050408030a080615120402040b0f06070605040c0602070f0308070311032a0d0e0f01020a 80
    0x907101c030724034042d100c4014064095004803a0380d000390305e0914088081c102c0703660302c0e0106d01405019030044003007030b000007040d68400c02074600155000b030a46d20252800c00c100600e03910341210098001c1c4507051001910008034451240180150000b90103c10345801c0e05401075444160780c0c0d410076494440b080c01011080c807405005030007a803103132120200d0381e00c400c034142207010182c10b01c40d03403050000450702040c10b50740341000350031340c003000d03540c0e6036009015500750189410894403848040b44c100c00c19034110200314016074045820b200c0e191800340340001030f481580f40e150f9401c5000c0307011a00508160300123000710350000b01015803455021010415982204e64161480d07a10b99003844280701250348541c0103028144058200075080c9000b00d80c12110521000f880198002510020b041c810610408504410380c2541c1d9900307000c01040480000701481e684403800200f19014008100140351101580a0340320301d00445180020030910500c2e9105903415400b400901c400082d2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 132905062 1250 132903812 132903829
    0x6040c091a030118200603010b0304030302190c051614040b0f04090303020301180204030305030420120d020d022d0a05120301030b090a08160302010b0907090306150308070f11 77
    0x1c01240ca0000307804003802c1000505d1450f8029807143c0003016004155511503108690654051f10491642d039200d0b0301d0700718001e00c0362428500f0300c04610507a8280c2c076076101042e1030009000d00100c1d1000312801601181d400214410404010000c1010060b2030074a5040480e0302100188181006c2250f68041810348a0000c0100c000035400001480301c2d505054455445c0301105004605003070640c2d80184c0584006013015140c0c0e805a01d0750003682812280c0380c80c0342800904030100030fa644540113a40e42522502c0039026010b034100d084d00e06032000402c601f0f40c0104c60103800151038035280c00508100034a40c00079a90285408200201e50200203022164120048143d0343e51b2641c2810402d1050141c0101c810b43c00c103a81000c0030401d030030103450349a400d01d5103018441c510b030f1070244c3c014055000d016401100c0a410000e11503041483d201c201c0e80608424082a0a45d00d08185184000d0200401c42c1c24140403003000b0414112802403030134030800840c1140301c52000041e2052 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 132906312 1250 132905062 132905081
    0xc170a0f11070305061f030813050301050703050615070501060801060f030507080c0306010b031503070602100605030c10051e030109150909030c021302040512010203060a0806040c091a0301 83
    0x40e603504150112990000d20012070945050282003900c0c1076075102501c0300409000d06818052000c2e1100380c13500d88a40090096a0019440e0341d90821402c1082089209119681c0b095190000007540203000340125445060002d24000d803a0460140d8500c20ba044107009841640d660f03040414407400901c549009082304441b100e43c001c3ca14a0f1081c41e0a43c180c00c04038a03a008a480ca14450b1000510305044d182c2181e007040d01c0391390300340c0702c030018603640300c001c0c0ea0520482000290300c4c2e0700030906084d1040303590030034845a5201c40c20306070340d5158111095046031180080002040c810406402c0844864030110030380b20001d03414400f142c0085c2c00c000001683c0c3c1002002c10410401018002c06a403201409040d80360388000d0201d5074102d0001c2c0c01000030103094600500d5980c103ca01401000b0301100100b80084e605034000d41040352264040d0724076141c082000100081c1543c46180c1c040b1280b03c1a900f04100032025021520682c01c1c43e107000c85641c0001da50a00407910071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 132907562 1250 132906312 132906317
    0x280b04050601080705060406020705100302211f05030304152607080a0b0102100c090503151803040503190f0b010608100b090f09060a090509070303230a0c170a 70
    0x1c550500c0034803401c01180340e1180d0711402c002c000800c0701c40c0c0c0114900b0221041100c4803142c122552005074082d104d908104078a0366450310790b0b510850000c0450502510038030080c00007072200c0d0b0400424500d0b00b401810ba25610500c800c200c00005080c5541300c1040510b482c2c7d407070041142940d000d21620380a000c10440650003001684e0f548903400070b920040080042c45405100d2001035200c04400b0ba40107080ca84903181c810049029100a4005080c040c080352107070000e180840c1441c20301034994800e031341d070180180c0000e80c00005c1035605840004000d01400b55800e8001003004071010022501c0600030401c601c08034a06c1d0028500801d01d0391a58040e600d40b040120359030500310740041200b94014400f050036034440c4070a4100a903400d41da2007445880b01d0700021a60411075002503585401c0208000071054003080c000b0803a88039490ba14441030404140c0c18401807403460780e6058070b02c00e00416408610484401001c1401500c010304014245000014551300040c003c030007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 132908812 1250 132907562 132907573
    0x605010f021518010e150601090f03020603041a1501090b04030c0509041104090f0b0601030e0627070b0a0f022415120102030117070b0307030203060102070807060e0901090905280b0405 81
    0x600710b00c0740d2116500020910700134050f1400d12b48010a99603160002038003400001c000a07040058402013483c2a003400000766116142611183c05c40d024030a280c0c5000400f619000550143c0364000d5400b500c0d401005244641e0402062045d1071030010015100040356410703180383d90b169841001c0741c207070242e0185141c02405083c110414074025284a040500d04004912401000b1800c65080031a01100c141281c00708a000048020f03085101100383c0185080002d9100f0198000e01e1290103030340b64a114608030485c03e9031900c650940000d01c04c8190a60750000c0140c6040c000d601c00f01409103800444812400728021078030f100308504045e03500200611075031007000326500c014842d0000421806041007030303603c1c590001920304070a06401001040b5030303a000b4040b05000d00140c00450702401c0d50350301c0042c000f4044500841c0110003800011131003900c64001e609860f60000f00802c03108a10503803030107010141685624140e100500540006502d00f01200d0003507002d00000c0c107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 132910062 1250 132908812 132908833
    0xc0102031506030f0408160b010b040602150709090c0908010c0c02090a02040302130b1503090307170906160c05060d060e010b0909071112030412030605010f021518010e 74
    0x3100e032100001d8940c0305140c24410000e050b05890082d41c5d2142c2c0c441841602c90810841c420000307076064000400c1500710b0b1001040c1d205451000c1c2c400c64040391708460500d0803095220b0340101094a030000000c400034014000480140c1240b22289154036211444035a100045400c490700c0e00c1003000003c480060101c19840c000400a40140c0c01d4041181f40c40e155030700007004802107200d170b100441c0d11012030012035690004403550341c40400b00610b80d03038039100b020030341c5943c02028112441200000024031440a08098a0710a00050501c1d4a86a1303203040c04100b50158400450300408900300c040350503100c0b48050b00b4111040e4001159813400c00354002e041c51816004080b6058060003003940c607541e509082e58200c102410000e20594107408041d040c160305034101c1e12600340000610040016020420040800940d420407032035480764011112501c81d00346210040c1e104400405000204045050700407880742e942c0d0110017034118a05007540d4100c1c1507070039690003640614 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 132911312 1250 132910062 132910081
    0xa140307121806021b040e07090504050a1506050109090f0b060409020a02150c04150c12080603010b030d0801092a0905031b090c03130506010f050a09060308030a09020d080c010203 79
    0x84041c03e4180050440071081d42d0810300505600d000f11440b980d00c42c00959003550007030007448054221210144281e1501e41882a600c201a1400715482440f0f1038283c034504607148521804d03a40140c2d2400125071801141c1d00103010341c2c81c5001001d5659a14045035a90780800500040100700d0700541c1b901b442c00e00c0a07040410030071b2010007041c3c5d02c0c0d0401c2280d103541c800701e4003a91a261254000b045492000320390144101600034200030184044c0000c982c7c00580040c4200d504030001e200150b290410b15803036000e400d8029001c602828014400302003503400617043d000c44110a0740172300352440c800904602400601402080c0305250a0144c1d00b014810089507240f5100d007003442c0da40d10b00218401203c010300c6820442030100c0810461403c00581482c81500714045400e50b503103c0c44001c1004040e440b445108000ca09000640343c4a180200300032aa0096251406d43d1307a01c1d8100d0f80541108401282d00c603c03205082d40c0010800406005490003c800050700e0b0700c0c1070304a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 132912562 1250 132911312 132911357
    0x30c060f14070611040905011206050702030a021b01021908070c05190b07230d0807020f03041a041802090108070c0206032404020a0201020309010c030e0a14030712 72
    0x120000c000c1d08018049040240314111040a40e2140707002a00b105030b10340750b8003580120f40080d071541d410840002082460328551410751030242c901080030ba220030328140d9980c841d4426180141e0048203102c4980c01081e02d0b510498203060041d10130225440c00751007540c082d00c5408948035080841ca50051081c030341d15030380c0035003c1521480101c1c08200e8000080c560035204e49100040700045210401c50303110718a20346a200320708181c0844200301825a00c9900f01d5803210000b80c40e0310001000c040c4001949000d905419001d50320300b9040401c2d1000501d40d00d2000d00ca00301d010400050309200d0f0a4107a40c18480e480d00040c0c0711058200014030200000d0724110030094020391420240c2d40d071b107040343d401c580d00740e0b101210164001035440d5007540035000c10b5070061000c150a102c15070103400440c401c205050082280203140030064080b41c04492591080b603000c0d550300c000094110380d030008210345a408403030070710759543e85121030103c03103c804d0400901101e0640311501201100b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 132913669 1107 132912562 132912587
    0x50d0204080d030b0405010605071506080d0507201e01091a04090f05160807030e031602010e0111030d0207140a050a1509030807030b0102010e0106030c06 68
    0x115a602e9103800306101d40402d007008014102c2e03281a01c00c043c10b8038120344946040601c6500c071440a4600b120070090350700e2380c401c00860a072100700b116000c3d484441da2074590316092490600c511024034880c1d0707100c0001402d461440340e03452141c500381070460304101c094000300220040b0340c0014554010740040c080c03014861148a080001441034890000c07013405a50510281a07003191011034101c030101c8c50115444260612400c5203d80003000f920b00802e4190515500794119800001081c8098112000f02021543c2040c0c3da01c1780b0007824202411518001e050386500ca105940318070100c030790300250704001c120003201148450b01e02c4a04a0b4400d0310580303085e40d90b03040701c1e80090340c1042c240c0114404403441c9000e56a00030390300d030391091040d8031161300c02d070083c2c040c04e01204d0540d500c0702c401c000e81c0300d4244180e10045006030308001400380342580c0500380400d1201c = true := by decide +kernel

theorem cover : BRFrame.Cov 132733812 132913669 := by
  have h0 := BRFrame.cov_init 132733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 132733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 132733812 ≤ n) (h2 : n < 132913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
