-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0767
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:40:14.323981+00:00
-- url     : https://prove2.me/submissions/0940d44c-b42b-4f1d-aaf5-40ca3eb2d06b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 137769784 ≤ n < 137949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 137771034 1250 137769784 137769829
    0x30c02061b0105010f0627050105090301020f0f07170705030711210607030f05010b040302010c0c0b0c010c1d0f0f01111603050d020706050706020d020f0c1c0509 71
    0x101d549a4a0303242400d100414103600300300022500301480c440e0344041d00c4590741c2d1034404600044244a40070008014440407410341001440103510940040c01e035858054009850a0580c1c00d1702c1c0e0582e404140d02641a000225900c020403003114842c0038401900900703e4201211502e8107501c920a91600070b01d2908401c0c5440c115889a9a40c3c20138070040aa5888402c0c9140c00d040ea100c0c9021200d441c00a442c00841524007582840307518166500101640d00f41419607005440c0d60800040a403010f08a4000c0050b20655010080589890950011400c0ba03050000039014403008824884a186000903010b00f680302d0400f06900d0b8803007220f003800341e003900c0030050700e642c96040e102405038020030004540d0484040d00900890344210101c0e08500c0781480101e8403000356018202c00104108280303000719070700340c014103204003150303400503d001c18404111116611122141c0e002d034006100958516480904040042d80c1c0c9080c0140b900c01d138140014500b03982d86521001c0c1d00d21 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 137772284 1250 137771034 137771047
    0xc03071b05010c0207090b06040609030212010b091005041401081c1809230c07063204030206071d120a020a030b01080f010207030903300e0306090307030c0206 70
    0x5521400c04010390080020032128480490003912900d00340038081d1814103040c9103030128101902200e049038020781d0f424941034155070800044e0340040f10081020f42d204c2503900000e940e032a120f540500c40b076040d0000e4a42ca84020700041c1c509560b0100341c07480d0714000400120202080584c030880781840081c0b181c5540310010b45034032200300e42c0c0c260061080c001c0820601c8059002c1201d05080345800303a502c0c568840070205210341100ca56a98160510521001036140d411800c41000300c120300200540b07051007030f0034005030b070103066404001c1510140001d254041c8503840c0c005880d03151059108581103900814441c0a0065034014005041c030100c008000380203140c907050703000308405182540c034108031034000801e008174040f5008100030400f134170700144203e0b00a2035260711081d151525649035442070a410003410707a080454a800c200d0342c0d61480b54241e4201d030300c81c0c0382d00f00c11107001001e051810341b006028290a0388100514030200313400080c12404558110ba420307035601c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 137773534 1250 137772284 137772317
    0x6010321021509010e01060f06050405060715050c030a0e0c010203042306030702010b030708010504030e130207020904150b190e18070803031902190e15070c03030e090c0307 76
    0x50a60310b80a40401e100c100703002c00c004041d000001540341100003444120740741e103c020050426481402e02244041004010a00b80000a00710181c05840d403180c1100d000071044040d40c41c101c444101c45003000040052a070800d04c5000e01442e95000101200e06c4c4620020b560391007503018101c000d510203800c0310000d024054200e040e2003c041d2a164a0f4101140c000c1c1c040c003a4444403900c203001d8402c012071400d405114a51141e034140e41c6000035001d6503414807011274280c0c3c00710030001d5003c020b400c015031140810140100e200e01c00c02c0528282d1030184800b1204900d15061140c801014004c0b800030b032542c003c105589500c0400c01294540510401401400d0100c00c1d2041c011108001541c110205c0910f100707988080f90b01c1e2030990f010840c14103d104a0035030409014030f01c1c01020320300b407080034a070b0b0740500d010340a081d040c0e001914114260304000c4084a400d105803a042c0109030780002c8041c449502030740d113840c040c140754800c503881e400000c011074100060020240c0705030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 137774784 1250 137773534 137773543
    0x80c0405030f060103120203030f160c08070b01090b0402120604020a020f0a060225033e0a02100e03030304060b0d060606050a08070e0a0303050313120504060206090601032102 77
    0xd01000342140d4641140c01101600c5002c240301c2959642c80d00540f003062a400442140c0c4151885640309845580d0801044206000b14104500b044140440d00f0002920755004118803405007203900015850700c404039054819514031f9a0080d4014480321450603d031810441e0000421a4056110311318524101c2c07401444082070f2030184030303401040007440442e90080400f00d02005c200310a061150b150b20071403030710142c80180042c2210b45a00084035507107001840807000590f244001c80d064038290458061003024903440c6402034000700045117402c407010111510700b804d080710030707003269400280c40e4000180b01070070580d01e0303181e074001e10341e070b1071401520245d8066010800c00f911003030000d0454000a000f43d002c1081034001c140d18038000ca41503c44040014903da030001d085940885058001a02e940030070710307140040c0d000080c43c1901c42e020780c200969915484a01d8010000e150038005003500b501c3d500700030018008951882c948404008a00e6110705e05100105c5049140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 137776034 1250 137774784 137774789
    0x12060303071e0309060807050906070318092f030412030605150c010509060108030307120204050a140102070b16080901020a0b1f06030e100518030a080402130b0307030201080c04 78
    0x2104001c80c00361059102c0e01240801580a03940c2c8140309a1a9403084e90302007426203030500030070414041c1001c41e1a0201c002c00d5424441d182c0808603110001100c940c40c0c20641202a03001e480d4180c003d0386103420740b01c01405e94011140c4511000b40400d40075428440070b0006020011a1080d0b420901d01a8004000600c0c0c09026020010031641400406401417100b8003030550800012601c2e040c0006003050595451201030751450300c4160003619890480c61156082c0b91302400009041c2c1e44080c200310040c06501408022b262541000a040505642041075915424045030f4aa00e40c0302c09191344080d070000d0b13401d94488800300140e150040c11000100000c050a0801c030541c81d144402c0b4504059804800d0038131500c50b0029000c3d5482d480000340254011690b03201d0004149d013186403c0304002c0350b1003e00c1200d1000b280c0c2541c0c490413151000c25159810b010440c00c0c0141c0c2101c0104080d42c0400100344000c1c002604d864251001030f0410407031001040c03440b04c01008a400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 137777284 1250 137776034 137776043
    0x40803031509010509041101030209040e0a0b01030c1715040602040b07050c03060a020a05090f0d02030f010b030d09050117060a0801021602030d02070503070e0907090501061e02121206030307 84
    0x4503481c004088040d20001401d46070b00502d440c074000580d42c1003401d6843d01031580510344580d50414200114000d4015041c040e42c000d40300c1618200580d014059070400700d01940d01120103605601b0107680816095201300321000f0240072058038010003203122540440210324030748251301c8905010000c0d0103550002c19032090001142d2041080003d404042070760280d0070b0fa0090769481a28908034041c1d080b820340031680070030113031485180596040c654110b004103034241c0d407421a0040382c602024003080ba81940e54594031a082490b0070010075036030307550034036009181906000000b040984402030540310a0307038400214141d9514500070310017406511300210344030707488034141b604008001c03807050b03000307008000c180019903101250032030a89034080c0040c1400c1d0f10741900260059802880ca0f80280903020021407500034500400d4001c040300e99038400128000c8001c03000d00780b0103041d08030566100003140581610325209803031202e841f050b8400b0080c0c0d1540f02003030852017140030080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 137778534 1250 137777284 137777287
    0x10b04020313020f04020a0507110307090e07030501180c03060b04091b0e010509010b030615070c0608010602060a1a0103110c0703062306010c06020c0c1009090f02090f010e06040803 80
    0x2200c4a007150300d1015402114032104813404141400101d202c0c8078100380008030100f060901261070f4180703141d241400038040f075502c00e50340c80940c8200e81d00c12002e0010794228447c1001402070074090300030407240c0300000400d504400d0761146d03000fa10a2000502c1d694440380703040c68550312a804048055000368002c001a030324a80085901d5495002d0101c0080d060400800e40e420a028814142d9030190603041c07035901c80b141003100001540c0050441c10800f000208001009818810014070294451a0b60355040c44c40181c2040c0b0010000302580346008407000031100d0b00c0d680401000c40a00300003903d4854031103100390350320400c152141d00313200c1c6803000403c010007030784034041200039522814510701c0b03034000e0481d0720041692090700248100807983c01180c080e80c0108050b154403c21100c5500c1e404005c202c111100803c08404144a40801c01041301c2ca40601d00c440c86245a00311300d018010800a8504c103600e0381024100144844420200e4581100b260068910300d130803130307 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 137779784 1250 137778534 137778541
    0x70e09070801060912020f0411041d060f011b030e0a17030408060711071a0403050f010501030b10450605010e04061d06040b0a09050a05072f010b040203 67
    0x40c150001c01e03c50140042e4403210b00203100c070765803c10340703205580c02007291801c2c803e100b0401002d808814800307049204d0400000440751000440341c40000a96221411907107059000c108081c80a086100c0c107103d503d20301d0b1400258214000b078240c1d41d05003081c0041e42d00c19404112000010b4104c0751100e070130440c226100d0300000020b0811140e05008541c0030365038500b07007100c00b100220503514880d40700000c140300d04181000c0992100c078104004500b45552a01c0c2c0602d0824641800242a555038005009004d08210503da02c410b001c844179000d1841e141401e10100460102980090190036890402078251030700517151404000000300e0b0032000314914030060010344030b22800f03d8007807408000c85003071502491084034a400c3c107519481c86122064400080300604c0e15a1103541c0741165005e95803035019150181c005030400140034500314a040d402ca0b540030740030400340013500250b00c00d002c060f0a102d01130426035074440c0799801052040c50340940090b10714203034424004000c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 137781034 1250 137779784 137779787
    0x1109040c090c020729030106030c03180b060108060109050f010507210809250b03041502030c091201020c030307050c0a0c14091006050d09031112090a09060e060108070e0907 76
    0x301070544144c180b40c10f0a4801540d051940501c054010a4440905100412600380242cac400094080b443c28080382210305607240010803500884210b600e0034000d030501c1001c0d60301400450b0300040030700b041e45c12141054000313a0b0342b03000010700e00c1c1000000980b400c02c02c2000c1041140f04000d0341010718001c0325003036000d04400c10456840740b0741d200301c401d2042c0c00c0a00700c0b41500e66803501154091000d0600c03c010105030720080040d10720310842d5a242c840d01c40248003c52091071244021912000038030b00b0441e01c240e0103200c000300c80e030050009072b6400700c02008403a000901400c04a5031401c01c8089142845004540078011011501d00020041c2c0f00c0c40d11800d220b0401c84411206958800c020440a25a80241d40c005842448080b40d980d02a601000710319000c3d0400b143c00b0310384c00307480901d8401401e2910404030b1021480c1d00030345c2412002c8030003405034940140507050604103c83d6503140c0c010846410004c05c0c502288010740150009082420702400c10341491801980 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 137782284 1250 137781034 137781043
    0xa052206030f0b010e070c0c03030f050c0715020706050702030705040903121b03050f040302071a071704140d0f060504020f2d0a030503040b0705030c07031412071109040c090c02 78
    0x5501203a0341840001b0000e81c4942400c40ca0581c1c800c442a040c2415500d0454480e5000c4011130305010041041540e060400c0029030010100c0e10250400505140402414072400ea4004802d120b01400070a0040c0d902040d45000c0d14400c1d100010800a1410215400c00450032a50011803501d0961542d081484200c0d4450751080c0d00e05006070745905c0e00e9205c0c51402200e0280050300309580030321240100d418542120718441da407490801c41d4689401e82c511001c9074800040136000a810440d100f0000d180f0307a5094021a980b1100c0205138a0b00680380450a50007403c942d81c4070b002501f10346d02c0103c09040d014020f0112802c5468980691f03407c0d883c2c070b007200101d012680851140324034000b507810050b2680440510b090500d040880019508625011581400184208150100104a440010b502401a68800410155109042070060711450103158002c0020f1b0b40817903100d10032042c0c3c194059452004503500c90420f400c0241498006030340143c203003218040032550004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 137783534 1250 137782284 137782289
    0x60c06010801060501090302100305070513081e121801050f0301080c1302090d020f0307080105090607081e041e120302130e060d120c0203031c0b0a052206030f0b01 72
    0x40007040180c4d04c4400540f060900d52200039803100d041e480c0610854440c0c0c0003136400c4801c508000f82048040c4403d0100440b441d00a4990341e400f81000d54641c0b0015844001d0b10020080500380c0f40c496825a9143c61191002c641d20620b0307400c2d8100c0b10717640b2650032a020100d029a500e622561940381e401c0d1510342201107180307c0c01007005030b4441101d151080f41c210f007600400c00146002d40741c0c00d0201c100e2002c501c00c1d40c140582c8400042e82c0f1028001c480c403880c0b161002c0c0a13980782c26440508032101c0603106d180415004c82540101c1030358041540c0e042500070b840b66031403003142c1074210400080c0c42c0c001840d900041c003020311010340503000f4010b005180b04206822070303280c5030007950402d0b0407100d542d48030590683c1c403400b0031980200501d036001c4500d400b040000c01d980200745503600240c00003818040200140d90003a2561003183e40c0c2c00000c840842e0031915100c00142c509e2a41000386054100e84400041c4903078081d4400001907620092000034001c0500b0024079000091 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 137784784 1250 137783534 137783549
    0xb03070f0f08011802210702060a0c0e060c010905010c050c0c01021f0203090f06070512060d02011224030503220f03080d09140604060b0a031502030601090302060c0601 74
    0x100303640d101041c050300200c0302000315030b62140740c50f81c41c14604d04010fa240b580001c0000d6400c108012026003501061030000d40c4000d07001c81d240c205020000d14005000f0405c110b01c6180c58007810b441030f0f200c20b03c00301e01c0c20111060ba40303030015240e60a006281d80400100303590300c0e08401203000e682040107044002c1010060b600b05100c1440103989410041030200e00c10040750314400100070031907018540101095084419240c82a80410701d4802c0540701c1c0808202c011400c0f1144601e0203140944c000c00a40b84100b5440c00c5900107080c4420500e042c1e000305880d01401c6028079038462a22921059110800002660381c1c200161281c0c801c02481401c98039801a160454020003607003403c5030803c1c04002181442c0d0f80b2034100c1070704002805020039441d100c140000c281100c81605542da000707070107401c0c03074101441d1882c210303031440c00b005e8000d1010700b1042002c90b000c040031203d8506405000f580d2582c440340101c44a58054000a5002001046a58000f000003074614181c0302c84 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 137786034 1250 137784784 137784797
    0x6150c0d0e0103060605120c09060a09090506060c060f0405010f091410020a020a030c08040506070605090f0615010507050f0307230105060a0603091112030909011208070b0c040e010b0307 82
    0x719004405880c51400b0b0314010035410814901c0402200e00003641c0b0412414640e0305107130507040020a182d0180b010407000402c0307904240940e001a108003604410b04591562600368940b030140c0c0c440c04010219051039218600081c00d0003400e412042c01c4030114503080141c103006140020008000c11505115489200080d0140b40aa0300c00c8070329915003074004099a080700c2e03a0440391500c14050880b01c81c2424000001c07649c903810040c00750288a04001308551801002d2540307806071440400c103840e40130b5400e01c44010460a1100407140e000e05c6c106546c2d03881414000c0c80c4c0240707401d5449140c40001180402d20130150580001ca6801d1f00c20700d248048158140381c2602e0007078640c1c640c03000d2216400c001d0346020b0790104500391300c50b4800401103050000014042150200720100382d400014180c2ca061074050b6520740500103203128030240f125152200c62841c02041c000411085c2080d005c2083c0d0840c51064800804080b61028459a10b41015802c00e4105580301c2c0d0102c3d20 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 137787284 1250 137786034 137786057
    0xa020f0303070e10120c030b030c150d110c06090c0108070f020d050a12062c040b0412090306051f05010e1018030807121b0503090906150c0d 62
    0x40031080301c2c058805540d0392600340c030516081190030701020381c801091000340b842e2070b0710341c0815005030701e5411195280020a202c14109060501000b5103115100e0b070038502443d59030004a80554407482e101c150300065051201040321180e21a42c1d03100d01c11407264000f00603800c440014a241008820380c1c41818a4031600300903528a43c2c10184903026030015000c0c413600c5031041c409444d1802040c9421840800340e1624101180c040317400042080d0500050702003001c04804400009522240c0c8403c0603103002c0d160740300031100141c0010030000b50814400c550b240f10b503030740402450708003a0401c080e0408004c038110058000441907041c608110b400140da41c00313210346d4628214040c015003070002d803040303046840c81e0340c0462208840203454004400300b895440540284c92050b801e069031a2000e4101038001809040c42500100c0c0d80f9904100043d0040141d8002c208250750600a40d00d0704400155140c441c0c0365801c40088020900340d03000840092900d40e509070340d0b1070b8401d0341c85 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 137788534 1250 137787284 137787313
    0x15060e2403070e03100f1401060509010513030204150503120a080408071109130203120a32040303031a030a0c0902030c0729060111151510050a1115130c0302060f0a02 73
    0x20804d1027100003258060105512950048004011000704200915485130726540000c088030f44000d94042c5e4400b0310340c0284003504040180c20a148045003050b424400c007048000d0041c040180014003803007010902c0c50070040c840001e094540710043c4140c009280a81e40c1500040460400740c2c4244541c80500b84003070146811a024203203e03a84035181450035500c8034610602500d44400b100c900400340015104005016202440c407070355010a0700005000020078148011052511940040070180009040710b899001240c0b500314000d81c6a9440e2503081040303018105026280b010003c00c2c4c0e8089103046d080800d010104046200c1440d11482c3c01100c0d410a00720182c100d0707511a543c0d40b04914403549969a1041d94900030075030682400c0c012075240401d980d21013000c2040410100704a40d000034000c664007000d030004004185503501629007001005e040b15500405050218051260a190380d40103103401502c020b50380d03050784410110740e9004007990300c01030040d038071a5071440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 137789784 1250 137788534 137788571
    0x7120f09090203130201081b0301060507030201051e010303080705040806100602060a05060a090902030102091e090c07150c0519021606050903060703021b0115060e2403070e03100f 79
    0x507004444ca0240810340d0342d005590307030b2001605c801d0700e080c01c002c10058122031040c01140030f08015682d00b92110351518029096072000f80000c107520b000c01d1034410340c0c5103501c03611504581d01443c022205864225060b219407140c0d400400c654007030346080208400300b5003512011256140d0844529940d08010481201d6040d110300d5803250a000e8104134203e15500804451800140018900301643e00015800c0c1040302f502c0032581800701c2c9407061445d1108002d41d001ea00302144a01d07040c0760340c1ea008000707410704442424542ea9481c400c041503110b40241c0e1011840354013051041e4600150182d0f0300d0b0703440c1030140000c00c80c030100441d40c0c80c172440c10b039254201c000d0010b00c1103898921064021f50400303a03041a0b0002c550f010045130f24400d0142d00c680c40d5040004c481d9690034908010611024449840d024010801c00100075140c1c500f5070424030a0a148560344035203031000b0441d1056600d0b44070f10b07894400c4640000820803035500c0420341801000342001106d04020050501 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 137791034 1250 137789784 137789791
    0x60907050c0a110a05130b030c010203070503030c030709080a05070305120a05270a12060c08060d060b121f0501120b0403050703030204030602031e090313050f040207120f09090203 79
    0x15400041a080000302c266000e00303c03400c1c00a160301c01103a01c880101d000c10300ca544241c400c180d10313402400b183e0b007001e02044512000a1000c0e51920384192502a540e210203030242c0d024210020003e50524855030560f40503105400644030700c00318605007956a03004c2400f05071440d0003010742c00c0300210002800c403145801288ca806061458104d140702c011254030140380d10308480b4a01d064450707690880d00708054900049110341241d60f90600c00c04807402038802d64103000080080c01059611a800080c4042d44000c021880000440108101d9402c00c07420040c140f007540d45c0c0c0f01c520040305000d2003805e03101031000c010030303030303031000254198a07624001901840420000c1340c0400d11480041c440b4074000e09000d49070586d2584c90034220f0744120b64005000c0102c511144582c0c03601d440d40d0f508042c40782d00650600d109601c0781c8031038450600c0380d030740b04400c00d8440300c82c079450700d4062b90a02038200e01c440100b0448510050081f43c55505400000f4404103004580c5410520a8a00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 137792284 1250 137791034 137791057
    0x9010810050a03020409080f07050a030207080a08040302040b18100303110a030c080c120403060b240d020a020109080a0c05060a06060e0402070303140709090b090919021906020606090705 82
    0x540c2d40c91902800700071305000c1c1007502c1781c1c0010404400b40040000060214502c5080100741200303190800078144030140e0442c91298100604030008600f490095070240ca40458000603107000304030000f10404210702c1c008005810000c02c00c80350100d0311060104032070080c0c4030304081140c08101d007038562081e0180240428500b049501c040350000c1d0141900501000481782100f4109283c1d41940d0460b03403044842d00c1e12000c1010325814a10722140d050b00c85411020b40c2240203480b030711135a01071411000005030340403405400e642d01c02d4021254240d00002180e47e0307403402c031100402d110361226003a0360510804d8041008a086da104050440b0a95034070502c1d42c506110030807001c2c0d402003905404054840b210088203100501c0d405000c1e44540e00c031142941c0c600000241600c43c0b10035814814003000b402c0200784180400c0c0e4047e080c580c06a040c05c4065944002022108030750107508100c4513141c004200c0d0f9800180c03ea000d0030003210071450343d035262682112a0322500c1201c40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 137793534 1250 137792284 137792299
    0x4030803040303050622050a270204020c010b06280f0906030b01050c0f070f06020a03080105060a0504031707060506120c010f050421020a0e011a0304020402070204020408030901081005 81
    0xc010038401c4d4013040e00070078010922864043d840d4080d05903100444d9112039003c0d61001445a540103621540101d01c514081d21003080d000300c2c0c0c42483c0b50b40306d654040d02a6800044502c0042e900f944514a0300300010100f80e1218544841c200c680c0108080c296003000e00c1113a180d15540c091300a020494504c1d5884c10343c480c1c1002811000b4101c1a064141403040501c1410b0515201b0f1001000007943c540040c14200e11300403480c004086aa0720040640d04428a440007196009003090305403601a204203644028126045655114603400600707503015071111040241c2801008040703e0b80611001e000a40781c06040094000d2030354150f0100e9480071084604075400b9000c050310385201c1d8203009081542d6a030816450489410a041d1040380000c204811031800049038005000201d08940096041c04030414900d81c1d100411003009102000003070841d660340c3c04880d100c590241c01952105d9403652030782d54a0b0403c101c1180400e1040d00013510a80741442000201d540080021 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 137794784 1250 137793534 137793541
    0x70504030f060902040b09090d0206010e0709031e0203030408100b1509040507140c0d02150f060d050f070b0417011103060d0318030b010e07020303090c0103110702030706120b030304030803 83
    0x1100103010b4031108903000384d110f01b40080076949080c074640c0700700a0304001d000d80000c2104000d040400c16000310a01c0c5012105120780940e014040c0c1082e242d1015408644d1704800c2d82c58590074000003402541440002408039130000086000314403022125002d100103400e0b1420858100c45080c1c3c81d0740c6681c018002270307085140135082590130011508043d5080001c0300050101a03000c2c02d26400c155004045a9480c1981081a00b1900c408011406024280700c2c0081c07107050800b8008a20030f035007127400e81081c482d0900040c00c40350000c4045509595071039103200c05030380043c429000c00d40303140242a00c54030320600600051045656110345107075100010001450781454041d001c000140d0024000b41812f44040d40c0918054254400700d580360814842404c0402444403045400c18020300807448070002c0c1c40700c4522000d0801040710302e14050703a406240038014001e235241c0f1804000042c4243c0180b0348150b01941ea00c1c2c2401000d07241401d0503600d104a04c002000101d040000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 137796034 1250 137794784 137794793
    0xe3003011202150702042c01090b0f0907080d020115120c030b070c02040608010b0f0a120201140f2b02070308040b060319050102090f010c020607061508010e010f05070504030f 77
    0x8a203000d0346a0f914a070424182c1c3e00400c085421031802c00e5240084014102d41d09110210b0316640d6080000080c08103e0b525905c9000150010748190300d5500d402c030100b00748078010300082028100c040100d038946002100028080c112048150010b0804940045103412010700e00d840529085000784001c20b145a85540c2d40381c40040c030300400c01800070a030100607601c1303009041c0182540400132540d90054020000340c007102d0410b00e031080100c003408011030059041c8540003180c0900341004441c25048610450f842090020b2150b1100003807490600d42c04c405c05030002420440e0381010380c0d10600c0c6900124841c1d084003030b001c19039420000c0c0010307080d91202c0760b0061000d03041c0c50500038000740c18ac0300c0404080b81103506940125541a41e0b080c0601d8901d240d00302441c00ca0481e00e401d0b0045461481008000f60005071500c19114032410410302844c018001480200726107502c1e070008070700a26461202000c0213003041c02280f0400d100b0340c16582900d410480707462107003150b61b44 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 137797284 1250 137796034 137796049
    0x2a0524010f03020102060412140f191e0815041d06090609101e0207050709050604140c0901031d0a020a0806070813060f1401030210111f0e3003011202 66
    0x23482410040f0060001d087d258005004d0031090030000c081540700d491030140c900012144007403004c108004410901e40c90310700100c003e0f01202c150304001149031540c00300d0a003080e19030010190480d00f0a810050030002203100010411040000c0c0d50441c0c0702c15200c0b42e00c500040c1c511041e968800450900d104d6501e074440100165590000354403400f000d07640400b40d0704a0003055516402190301044551811b000e440c3c0e0000084408200c110b80150f5010b0240c080035203100028100845c4c01c1c4201e074020340c0480040032581501603520880b10302080da0b01c0c21400780407401107803400c500040c01d400008180340945c441c1d4854007155510041014180700c1d48010907910252142601e40403610680b08030038151104c82d05000c450360460050140340114450f0719800c0080442e0042a010b40114000e110090308012880200b009003078044040e0058042c81d502c82e0045d81c0f40c02d0050a40e10b070324034a08015500580c60845030682804413a80424814407215200010711030005181c0701c803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 137798534 1250 137797284 137797313
    0x200a1809050f070e0d0507090b0102030712020606031b0102070308030a1e0c021207020a0b0721050d0b030c0d081b07140102010e070e1b1909030b060d02012a0524010f030201020604 79
    0x1044033701f820032607220484402c08002000c0d0140c2c0002c002d02c201800c05004260050654110940484500500003541c030303000c91101030014031010002c2109114540c004da13100e00904501c0c0003840081e000e4910091154a14020140c45804107280385080101c060350003040c0c001300100130240c5409560107040c0d02c2030204403840303030200031503401c0c100c10590300790f00e20401503950b1a15134110036803400446003115151442603120344018031044d9a0302c0c1d15000d0b8281d2010783c040d12414020030030728030f4000c021500121405060b0011551210042003994010403d0340248104032010300711503210b10485c0a000c0c2c52103c3d81c0009681c0c120b40340362181045520407559032619285c01e40308414a17050f1a0307418006a0310080410030301c01007200303564010302c0445d40300000500b00d90000c4c2102188001711085a00c04800c0500202008034160664075000700a46211100540e4203120102101035640050320b6000e0002c1800c00d4900105400e40e64180c0062000c2d0701d507611040920840c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 137799784 1250 137798534 137798537
    0xb06040312030b1008010501090f0e0a0917040618052d01020a140303060301060e070c030e0f04060f180204030201140903010912030906200a1809050f070e0d0507090b01 74
    0x41045003015150704446284c902900e680d00240365040c4000103000101075030064108001c80c6109000c81d2009003582c0350010313407060001801c403200d85000000180b0048100c0c61518012400290040c1c0208130440c122541d000e5018845844008100076003000d841e04840c1c001e136511007241070214000c41c5407456a014011104400016598513426886202d12920950008400c0c031210341401d008800242691650a0456107401c0070024850000642c0140c2080084c0700070b0006500c7c0c0318540f44800348040c0c01804055280d04503103620100620985901000341000040303000024400d503401e40c0e80c140d40c0d0f002c032000e14819800d00f5410400391164155a2007a140c00054602154503455620584003c2003900d103d007002c604540c0704c000319060861121510710342940b800d000701c803249402d908100e0860821000440c0c0100340c680c1100702803070b01d48020700810307003403120b1034501ca22020b5440c0c2d03002130078140c1844154210448024003951007400d05001d44049600701e807107151010b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 137801034 1250 137799784 137799791
    0x9021206060304030509060d09230c06090a0f09020c0f0a031b02030c040f1b030618020a05041a04030c320f13090308010803070b15010e031c120b0604031203 69
    0x201541c2c40222342d5201c2542ea0101601000309007040e840c3d8040d9600d0902c81840841d442e99902c07215004851031250f02d0000d1200901d035135050584010b0400c00d0b441c0009283c468890b20029401401180b060340300e4143c5285030b40000107203440b440c56240e994089014103184203071001d080144800c0b6458041d5414581c22606d032882020098280050040f03800c958900310080191150760140082608000007400060440324080020030f8011200507604c04080000326130170b000341c0d04101000000051045610070141c4045c1050320700031221001e03420f0392001090401e00881c4000c0022110740101c03540c0c1000c0c0c06c1201d0801e00ca010b040c00803551608000540821106034944102039a1400001c0030b140d03100100901400107803000b14500061911071500d0444000d105030841142d040300300c1c106900c65900324012400c0a8221100b2804040d150098440032005d5540040c8192084c1d0300082062300501c4008030024204510f010b0858643c06120390742e510b442c405140d01c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 137802284 1250 137801034 137801047
    0x3120a060801020c160f081509070e01080f0105070f0806041a1003021c0204030f2904080a080708010f121e05070303030f02070b0a0c0207050909070906090212060603040305 76
    0x1400c0c002010052411303c0034010781d07041c6103040c1c103440045070031100207509042010300c180500085c421480480c0c1d4603800c44942d40f900c0f40d0b517282c02d180303030020b03030800007881c000085e0100d0004100d2044400d003c002d208503543c2c803000315803003980b070031011002842c5100480d9117800d2950082951242030704503c1c4a0074080d00101c0d60b0700c2c3c600c42162000031786c00510340504078125403c03418040005801507243c04d2558441c1d00d1460a03407500600001c41d40f003a121500003810740410101d030580c01481d0205d1806007094111034000f4189038003c1030544000031540c074410480c80341680d403d8840c1680c43d6051a0703407402d075002c130034108907200200583d40c55000c0c9602c0314181c03d5284070b02c00402d1280d0851030028141c40581c1000807995005000c800c0000e4004d0b92540e0344081c0f1032800085c82c000a080891800002d40d1156405c05890414064210000704a103010ba50344040c081c080340e83c1e94040c81c8100d2080306046501428000c020ae00517203008401160071600919202e8100f60 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 137803534 1250 137802284 137802299
    0xe030a06020a0504030c0905011409091603030c060c0f020d0c06110309071703040b04140102190309090b0607080a030b01021f05040317040b0105012703050c03070b040803120a06 78
    0x2e201c1000d02d00030400110703080080200901040c005401c40203018012540b4000401b50086a803041403131003030426400149419004000103c2c4c3c09056901556040da9281805480c0f04400402a11b405007024400c14000e401117216000f007070201d5000300050051036400b2542c1d01043c031000c031409030f01d0301450a4802d030540051402901480c01a100c00741c41e258003668000020300c1007c00c140c1040c4401c01c1140c103020300703507001c50b0491401d0a8681856000403070a103244201101001c1200d000c518050560000b031440c141c2e10848020010314100400304040d5028820008040581c2003202c00d08403842900941d90518041c01100c03891a0b072030341084403541c0304a1342c840801e42d94404000915a02481c1d280c2c5002045140d0141400c0c0b070303120041003080c14020a41400401580142003070401d04d84030b02914403003100f5201e2070b6202d01e80140c0394115603403410321901c240100400c8000d12402101c5c121000039001358604903441c0c800118001000f86107441d419520940090590b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 137804784 1250 137803534 137803537
    0x1e0c170c0405040e15060d0206040305062502120d1a03030301060320040605121005150d060506131203140c01020d0c03020903100504060b0307080a140109120e030a0602 74
    0x2580030016035900c0310b04100501c401c03580114142d035000e6001101014107180b4048290b600040103441703c2103c00d0345030011404a2140380d2008090b8401c240400034650007103004244005c0b2113000800c880d00c020901281d030b640300624211411a4108408200141564451303c0351f02d4880000e040e040205c10000303030540d0001d90002d00801d4a850106004900c060180c48001417000400f0b0700342820140000d269028130020309480519200104d0718591030000000002c0400910341104860305038855000c0b5041031803060b01681c14810007158030301d0b10800741d80c1c0c404030006514032083d14040130b071000b00d0744a031070507028008142d81000000700b0803001803500d20000000942c0e00c10155483d00304030313004d4210310000c16205020040f4180e6010824518200c52030102140c1611396040901c0142040c44c160b6500d4850754800144e040313008944079240318040c1141107116207442011900741da40380c0354000d050040c0c000240b40220b0041503851001000501240c00d0a0540c1c3d4640782207 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 137806034 1250 137804784 137804791
    0x603151502030c0d0c080f2206030605090a0504031b0c08060406020301150e031e0f0109111809031603030b04050a050615070b060f190e04020109091e0c17 68
    0x40c0c0000803160410f0f40c003000800701c08665880c100801c0b010517102c108840c0203440c000b40e4400e100150081c080e0490360a40d1500c001a08200115140d680b0000750060003540b14880c05543c0d410000341c44081c55100e468030035a0152141c03030300c00e0b40000092416540007207003200c410b0101c90300030079915010000d06108a204210050f500e5060400c554612810780d809041084000350b88201141c0300410f81e9145030024410350551560307078101850814a100c00e01130407641c60280b215042c01045040301c2117000b003d407403440703032060b401c603112592880807922140c40380d02c01c01146011515200c1c668010600a20300003d212410600003019540c3c2580c00c215030399150403d10040307251040690101100c022186483c0c4500303641c0f5215003100080240d80301d00400c010318219911082d00c031003140e441c0c078440110059100d0b080c041d442541558140d00144a03143e0102d44d00000b40300d141d02c020f4981c2904043e42240800c641c0140107069070903010014010b91144041d83c50910a501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 137807284 1250 137806034 137806037
    0x20c070f060314010b18060c0a0f0c030b0105090c09060306010918290a1202060c0f010501080c060a080f04060608070b03090f071a03132102010c0302030106020706031515 75
    0xf000b20302561580010030040e0005441c881e020040001c060f1582c2407800c006201c01d80c1d2264a408411500d141890003064010708208401d40d5108204101c2c4000542031b0380c0704003486901a600c0e40c00b44060001c04903229032100c4d070100408001c614105018507800b410502d04568483d441d01d41c1c0000b14412502d08200d05502c4451090cc04034621200304540340c0c004006600900b200c17000501d01590034803e044c10f1100074090582551220001c1ba030f41c0185402c100c9503040510848903009100034030405030301e8010f00c0354003905440c03c0b074121012486540da440039036881d0550314504c1c1c51805401103030740d0380c4d43d00b030300040c0c10b88140044d8000f0402c091003075459160103600c0d0381c2401c4940d90703040d14507009058284001d0305420082e03040304408440c656207136540c03a42041c054800030703d400703822080c180400d280d0b00d2051010503011284135074028014862140c0301036050380001e0140300c0241e0030014003803007030905c03c4d404010280700c03440c807118480c0d94030f074400e1881042c040321200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 137808534 1250 137807284 137807291
    0x100e01090f021603020c040b0103020f04290c03040617010521160f090f0204030803160c0204050a050103230c1302120a0203180c090a0509031b070603060602010b060d020c070f0603 79
    0x1b1081c50315108000d40c041c400c2c2019441d00c00b0b0a444858680301d580180b2580e0700c0303000d4980d4400c0503003040590040c50241c113880c1d03480c0d94008049681c2d410501c11100055007080703042d091110f840c124203040b0341000e00400c6ca12803d0070034144501c40705082c0103150344103003001d01d40e81c03003441c0c0b40c000d005181d550003180c0d805007404600401d445100c000c1d00001d500400003080081c9103041129401001200e5403d8900c83c00c010448000c100301501035805403d210a1000c00f05450340158101c900c6150300305403550b00c0c2d90350807080b61240d40c080d080301d030400415000b072820460304480700c40750711160044c07070078108201c021241310b4251850716a17240c0c0801040038080c4131040c405640c801000040924178601800194180740061040c0d0489450700003040a8400810070b8800e244102130490b502400040100d50741c41ca80381c441c060000e410580001040e034010b109810702224098a4546000702d261000c10207540000c1008001d80f180c0304001403160303800550359016008698020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 137809784 1250 137808534 137808553
    0x1603060515010305010503190f0b0c040e090109030c1205070c0f140a03080409020714010216110402070209010e13050706020607090b0a1b02031e01050a05100e01090f02160302 77
    0x100d0001d4203804100d818185840c005015580d800101a084540b4445499140c00c2c02ea140c05507500340b15500082c104c0d00d107a8140031901b0017580c0508141c540c0c45186d0b041070342d1503c80103400d9540d02c4070060007045180d0708201c0880c4d8602924445445941400c0e8a40000d9954501010b03a4a92080d90460034814090004040d9802c0380c50201804581404840b0300316100c061040c0b04620561410320b43c0000c024041088a000d550154030b4203c0c0219181d24400b546804610000300c0d08664001c90700c4100d00c900d281500c01e5602068000d006030303c2c1c6030308049180000000140c081e21040c0788c8034000313100103a03040140c00003502c0a9809000d9504003558040e002c0f0f09690007961007000b09114405030341c2c1d4000802c00c240f4624119400e0f81881c140046420301c60b100c0310000b8044600350906040c3d0605402050180d1140b01c410860b43d503585018507501d0305180541c103140b10b81200108603080d295000300c2c24602c0380d40390040c40c18036840100c19880010490880141e00308c000b41 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 137811034 1250 137809784 137809801
    0x7030203010627050714070b07030b04050c0906030c12011e0515121510050a2604140c22050f07051b070906031a0714090f010216030605 60
    0x4607002061030914041079a004110481d0718001d030150090300c859944c90011712128824403000040c0368542038032554610032410b20180e0000100c0315031000c20300340103107130006081034030405205090600b4583e05000020040001c6640080c040d400000d2041c030041401c079281c002214000c041441710392014080521070101851259401203104002403942c1626481c544e41c1202c5140607102c690200581e141e070000c02403100000c44868000b4030141c948521190003070700078040008140c0303d0090a04024003082c4040c4800d5007a910740302d0f104c2000c2400903000b03410004242c040c81040e0b070300c441102004244005442c0c465078043c031403280c0d40d24040b41c1180c0708075500802160407100440ca48000e02402a10801045030341800102d03040b0312000350705214000203451440c8050240a42d00c0c2400443c100c0311004541000c0d01e46800306030110b0240c0390f00c007181c0008420780f60404d803800c0d003080980c51282003da41540101c2800804450000c44420003440c850b07a070015190801d00c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 137812284 1250 137811034 137811041
    0x12050a020a09091404060b120d02030a12111204030c1407050f03010b030d0f0203070c0e070e1f03021305090a05070e10080f0406110313060c0c08030610030b120703020301 75
    0x108240c03d83c6001041c903400034034902c600e6030150f000741012510720f40c2038002c903580c0d843c1c1441d4000d89024095003c1d500d680c0c0400104404006075032203802c0301c0d6680401030308403500e45600c486a107200300700070700740080d100f052598400d00a062400045e119500c5028004500c0c12040d2000e4004c00c2c424010340c5002c1d900c1c0ea481940550082246400300c0000c01d81e501031446408040c050740d00c10304000d0300d02c01c00403500140c0e0b102440c031200c0e1323a8030300c00030a0350142601c203103002c5018208100c4a40c140031180e440000b00c0710a0303e0712000b03250b0a054009500503105841402603184d80800c640e203a115046005508100300014645844900140000454502c203440780340c48012990403071740d000e88001d820613003403171085906841c1da1a006c00100b0b48126220350740340c0c0100c03c00003020b0099520403111f50050f4410300a2210981088400c030390f416500500b102003c2c804503110781007002054500b43c240d4240000d10100600010300e01d409000b65400d0664040c00c07051085003021701 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 137813534 1250 137812284 137812289
    0xf0a1502030f071a070903050604030305090f0703061a100f03020d02130b07020108090c030d12060306110a08010e010608010306020705010f02220b0c060c031003150e010e12160312050a020a09 84
    0x6000c9500030300755a48c1617100d1001400140c00c040d2a440801c4040d40c0038000012002c1050084644850340c914000001e08032084000c1d805400701d030039021a60030903504103200c48030541d90f050140f40168200f50000c0d0000c49003454066428004030801071070b618ad0030300c00303070a44940c100e03203400c0d403407000509400004000e00313002d0b00014040304c01905c0014803001c641103141401003141144042c2c5400400f0154070192100d400c01040300100d54160008100b00300d45581c585410341e88031204815690303400e119041c00030314a44010800300791190302a240c120700c10300000c00e9204440c103011090780c0080c2e50300186004042c8070f040413903500450f03080051000300103190403c0d10b1000c2c5e030794851000900c0084401d0000001030300c001e0003040302e0b20145910944000804107003040c1000185810000800070350728100303102c5c40040d400038200040d40098110145407104405400c41c1c2a00128411001d2011520802201c0045030040034420210982c0058461039102c0c0010400704090307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 137814784 1250 137813534 137813537
    0x303120f09010b0a09020d02090406061e05040501020604080714160f1e06080615030a09110f130e01060b030903070201020712030905040c050706020a030b0f0f0a1502030f071a07 78
    0xd80343c2001925a88840c8040700d08030300d001612003800b141810b029208101e442d0b580645400d1001c100c40750041191041c0802104240c0010214040151528800c1d8091240542d118000281c0012103590003000c50303038403e9a490500342c0c0752191440c60207074100f404c7e141030240018284844118200641e0003800d40c2406400752400c080c0100c50403a03000d003e54400c10040d1000203115448005001180d291b550140d0b03662071404e031240d403000b010030b100c0c112405624140808882d180040304030a481c1740051605054030039607403803140200b203982c440440e55501c60a00040b580e003a500558462103d01d0050369940405100090619030103401c000d0000c10a0381114012039480b0380784505440b03007034400290000c00c014089e03a03103001d2100c00030152400010200801030f1305400c0010b08103010340e800910140b1700e0b070401040a60200c1155008004501d0070007240d00c55200e98110046e071401507038500042404610344c00e6111103c00d4410300740c0d0954404410f0074003140fa60340803d00c3d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 137816034 1250 137814784 137814791
    0xa021b152409041a010303120b090103080d1a030f03090406080106180e0c0a1206060608060d0605100e1e06010815060c0c130609060806100317090303120f0901 70
    0x44994000a01091001c01c0c01401d80a000a040101c800105840c07802801c41ca5002503940303180052109002ca0079101d600381c100664442d4504047c6025410f803580b1081c02410003406c3c042c0d05000f4804117629040c0c0251410000002c0e8038280581150141c0d2100a981d03648221406e100503680a9403140801d07030304d0950108503078611001040c0c4603040c0d03c0001304d05405c0381e07912245841549010250722200c3c0303d50000304002051640c0c41c0d45da204640a00c2425560304054900e41802c4071015040051900790384009801a440694400101003a01100d1a281c0340021490102190700f682114001d6818043c0366040300001e0381d010500f46032404452030140c103040000b900040d0342e04d001e02008951a00011024060b01e4201c54001d80030a10382d201c9240e00c0c5c4003408452295125643c5880030103d22048003244561080c1030080c041503070640345980c1c0380341c1840c03007030b520480345003041c001404203903024030007030145034107080d04142d0314101006086105071001c1c2a20400360315 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 137817284 1250 137816034 137816071
    0x240a060c171602010c050102040b040b03060315040503040b070c030c081f05011a070519150c020c0a0e06120a0303090b01050f090106050318030f030f010e0c0f030a021b15 75
    0x4205001040b550350a10f0082860a000d1403c01d01a000b01e4200c0f10700114081800b0800c0348000b0040c42c4680012812150001002a00c15503c404192405007240e0400c00c414000424004010828140314540708010556240c660706941c1400340c0041c955908607206100c1d030169002d420b00300c0981c01d100204840c0d450024000c9991007120b03400d2500300c20100307008040c0441444107218a1701d02180f80001e50016143c50703480702da40a00e01c0e00ca024a4280319101e40e42c800181d007100608003410040b01c041c1449800d0301c81c0500240b04070780c0404e11043c00c201c00302092164a00340f5100c0d40707010523451524a091102190160403450160083e0000c6400a039035021459046801a06016980b5101c010071103658041e02400f16081d44000248449015002c0008610940c0201034500480e600c6e554910324181d01924000344501051050303000000e80e0000460300110182801813405a403088034000412900364260000c2d000b03501c400303400d21040c000c0c0035071000360b1030124030ba00320 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 137818534 1250 137817284 137817307
    0x90212150306012702070b130212070e010b2805040302180f041101031d060405060c0c0a0b1f0b0309010b01080709120c050402190311090108240a060c17 67
    0x742d01c0b186001400701e69402134010440164100d4401039048400c4600c1e9103403400a43c01c1d10292000700300d020300c1818030071640001000c030f45502038030740007501c1e40302e5640b030301d502d41046400600082004031076040c40c0da07502818141d441400c011a0703031562900c41c0d2840c01004000c1a0180c00c1c940988008010040c2d01310500b00d40c15405584a02e03c0e500070192240105c0c0104100840710503c44811131405001c2c0c400003420314456849001242e400340c3c0c5510014009024503680810b0a41c03080400c0000542800481680720544144103461103581c890720060307081c1d903035000810f003860010901c03198100a014191542c6804c2c2442c0c07400341424100180004440c5c843c06150100080321300b0308009440c40000700904000708250340707480042610034200c0420b000902d022070301e043e40003060b1000060a60f107803034805840b208401d0340c0c1c245c140300c000c1c00700074a2094814298803100201e41e580007540009081c2e82e50755400d03160480d2a00e80340ea5019a04038100c0383c042408030a0540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 137819784 1250 137818534 137818559
    0xc06050a08010506071a010801020c0609120405010c0302100c0c0308070e0609040b04091406091e03040608091903090510050f0a030b12010627051501030b01020709021215030601 78
    0x1102d0644e40b8690f00e48282c1400f0700c601840d011410a09961403000191880054000d0310349075104030103880d1940c6600d545103680748005e1607028101002400104003960241101030480c5000c0d0054601e410b100082d65812109009101400f18920700342e07540500d80c0c0405e0107030344421582000040340c4035840002c0c00c94050b180b541407090f61600c40800c202d84079600000c501951040c14544451000c2d0040750310b48204650441040c413444919000c0c8400d40b04c0c10040542c40749010354038050804408403504030006012004a11a20b07844d031501c0001c1185d40c500080c000d41e11140f100d801c1030204101d04c0d044614900c05c200d8244003139200f10380108100d031094204c42c1000510480401c0c0881e200e800c40400501c925460403074005402d0042d40110360100c0390307a0501c008081003400a443c2100c20503130b61880088bc1d8511403030750650082e40809043c0205004841c9a1a900e01c00708091f42e000305c1d02010141d0364034042c0268500c111089180c0c400080703014290b158140324284000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 137821034 1250 137819784 137819789
    0x1a0f060d060f09020301050a02071403120c030a090519050105100303020712110a12111512100504060815010515030c0f1603211517100203070801030c06050a0801 71
    0x200d9550352044040400c083c1d014905166014000f40461307d0101c84400c000c1d0070034a01900c9000e554078003201201004412112203507001e0200e00780d182c0362a030016000d600000c004103140c0b50360b200b20401080081101c110707032500040004541040c10720b071860964201614046407401810414030000360080707192030a03154581c1400510744518285254941c551250f000d0b0000c0b504c0c00003103982e51340d000200c88082d00030b4000211000e00701003071104041400c01c2006034a0400c2c4050002021142c81950304001070612110810342c50388002401c4030702035840215a9400318039100302c40f03000e1654a0340145400c0725600c012199400c034032038843c07000502c046221000000c81100344030040043c6c40000e031301c1e030302c14070900403142c03030054440500020929584d00328102c40003c1e8031668019280e8000b983d07038007410054507203c1240041403c5451500c200d02880d90015510049403003e03600c0303400f030340d5074010b503039451402c1001480382d203608410204842004240d58403034000044c01d04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 137822284 1250 137821034 137821043
    0xe0901050109090e100516171e060a09020309030901030e2b09030c03120e09010f060e010e180711120f030405100609020d0b03030306031213121a0f060d 67
    0xc1c84580a6600d45c1890106404540e02d60325000600402400c03002941c1012401030306c40c2c0b1100a0750307145040d1080c3e01240c150442c81305107a1650080c8643c681001c0e0440c0019100803a0746456001c10020f80c1c10440783d20025502c08a50700000f0341c3c0c540109803032110002d02410f5242a00394400f1004208090200594048114140e01c0684614640c0c0021600030182546071a1170b864100e248810050428000921031301108141f85413015403d4100c404804068071154540001070f10900441014207050280a403100c501a07201d0000d0000a00042d003a041c00b40c4c41c181c100585207034419546454550310046031a20041e10f40c8084811f00110620003a46a607118500386280c5024550340c00f0501b414060001021011500905400141414240801c8184209040c1d99000490348a41e00d50710060305596a01e044800405020040c402c40600b901d0300c03404004c43c060315080003251105444502d1000615010b0100c13a0003403808141c0015904052001410841d840c95000c2c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 137823534 1250 137822284 137822291
    0x90d02010c05030c0601030c092903031201090621110108180a030206090105062d01050c0d0809010c0509010f200706020a060b01020c011704051204030b070e090105010909 75
    0x6580c02140510700160b400002c481d40c0341248107000740c850100784801c6586c561800d0703001c0f40d07042c0180501d142e5001c11841091142900160302c0d0141c08844400c142c0600003045400c90740580c041a5602810b000d07600415a00d2a1910801140c07642c0c29070302c00c0802101801c0fa002620a01e0700b07082c0b581091074121110b4983c410341d25098502080c405640b071040d40040000c0603008a0060f208030600c17402000300b036a4010174030080c00750030144190306800c0c0034005101c2c43c041c03010803580d446062500c141407d490345680ca140a0304010baa00200d8030312000c00c1803140003400b139140010700c1480c141e803c02d1200b0f400030b00381c054580954428030008c0c001122500500208000340303d5404021a50001d51722207000c1d4a460740600d09845040c14441c45003225400018824821801a540c0756030418405404101920014108031340320b01402d102c0244080b40311010f00003039409a64080064280310401070071000850644900841c231030801005a6a08203010100b05e500c5280f001c0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 137824784 1250 137823534 137823559
    0x304020301060b1902010b031c03020c100c0215010506041409041b060315050402030903031b0702030a080a030f060602030d0e210310090e0d1b0f030305161409 70
    0x2400341c140c5401c0003c603e075010540d84a112072460701c09a942c4503640003002070080c1c41042c140c0b2032742072648000109102a03255031549200c0d07401001c400d0b4042e8251245d5100c1c200702e44050790341c00b085080050340042200360510b2503403200d503401414101d8904d0302d8903240480c01607a120001032280e204401c101d000605100100c4d99a0b91415110030215407282d0700d4020180003010000c0c090780340318000d22008150750505100300c038003400c4402c0003181950750300c00b4840d0303d40e0840d114111071300c03405022030f1005031800c00c01c8041d036510488075640c41c0c02c14901e000302180c40a40c1c08100036414540104101178021040b200380d1201c8103804070b402a180c402c6e69103050031141e00e540d0b41880300c2c142d44802901d42c13009503001c3c0384422966040c0e01e603202e0000c015a980c202d032170f20181e00400794004040740101030810800c408943d2480c15403480e900d51003d08078071944140c002c203450300c0420005040391032602418814508145a00c4003c0a883c064030707006001a640c06169002550f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 137826034 1250 137824784 137824789
    0x60206010b03061c0204021e0a0f0c0f0f03050d063003081b0f030a0b01030c0203070c140d20010201150e15030106051002010903020c010804031707091e0e090102031902030402 77
    0x48411440120234200c0240071046e00707901c2e10340c3c00480c1d5400003c5c014450140c81602c07035140c0c400e107a40c1200941e1005c02e0a5264902070011600045080c0603040004400c2e8003114003d501c0204a41d1600c000c0800c0120b04411510002104048900e8048004540001c0d04501055005058450000469010442500414030400e005074480310380c08020003c0c035040302d800c500c001400a03038062061603100b03002070f030f9280503070355005184404480c41845040101c01040f003144100805c0010080303480c1e2191488031003500d07100303190b51221403241840c65030240503c00141c00c203000c44071502440c0041b078107030040c0d000d403000302da140000a002081ea6001d400c1440a098024490f1020f03200d108006802480d50031000c902500400f5000e00456001e036030028031070303905921000000303124141d80704041b503802021141440312005020800c400c02c0c800140030719450303c00021425040c54120814107100820391040341c1c0c01002001000304c1c0c0048030000080c3c0000015071681c480d40300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 137827284 1250 137826034 137826037
    0x1080610060512220b06102a030c08030108012406090509100302030f0601091107030905060702041401061101060b040f03080f0c010504060504060c2f1c020304060206010b03061c020402 81
    0x481220141084d4000f4081c404020300a83c050242203540344481382900d642610001400d10034420002030300000718900741c0342600074200151107860040d8504909a4448160741c10a03080103001360765681d10b0014181200c5e1880a580a01e1340164416502e00000202514454000c00780580c01c03001c0421007000030640c1e51005964010181c4800c8440c1c619290b5480000344920003c2604001303d90841300103070412100c090381c2554480c000c107814034050080f15800500c0882c0c04c1966042640209183c000e0303043d0113030410b50703503e40e01c001010050070300b074074515003003041882010001007203160140d2004074101c07940040d0b0316071101c81e03c1d03004450300d003d04201c043c0a1b500782020401040034035404503204a119000820148410070f204175004807410f0401c03580c1039810840c850103400c050901d10115201142181e0003000305500d2180c031421240e1000b005070380042002d022340c5406200c414007600003081c465040d46020380c0054203542c0c0100144007501c00c01c003451025501c8680 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 137828534 1250 137827284 137827321
    0xe030d0c0807140a0512040212060103031d09060913020d0804060c0212061303140f07080a030b090403020a060504031e090e070507020f0603100e0a0501080610060512 73
    0x41041003582600d520180c1040c004584400004082c40452144074850310191a51101550f940ca402c02d20311240726146500080c1c42a0781c0603500c0c1d8024880d440040010354040d511a035100c51450110310040c079280001018002d200b0300d021030030000d10342c480c912810b6210340220007a01121a0500201d580034004440282c0305900024000c20610f4012100d4400c0d13034401e42c0c1000b07118104a00f295246c5500ba01e95441c1d800c80c0c981d44c4d001291203010001c0c544450001c9031440c005d59100c0c3c001940d4004134088801c10004603035100000d41620554505203025074080019140582e0000e48880703080100624080d610310208052500c00c4030b03c00008240304034000620760304550054400e030168459100981510380002d80220710402c1554080b6a014000280440090007000760f02c0d0001071290081c443c9203480002c4140e0750318590790180c44a024000740c19418002c01a013888002004c2080c4415560f0f800c001e410b0307100c01200d45a01140000b84041c0c1c9420841401400c500c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 137829784 1250 137828534 137828557
    0x403081e271302030708070c0302030d060e0411030703030507030f0513080a060614032109060a080405060105010302120601080402040e07080f060a0c020a0b040609021806030d0e0a090e03 82
    0x44420303014014003181c05028500c02100d003181545206000c140c00e038401281c1c081c0c0021030401c0070034181e81c0110018641d02d4030030b005480c01c0c2016043d41400300c0350950f2045980a126106220900c0800c22105001c060b064004c2c0c043d19080d031320041c10500c07841790000c003001424460300118070311540665980310214122100b60b00d43e81c95115a031020459004c2d91014070340380f40042c2d82c80181500c0c0c805804080c0181103c450310407500e03180b041203406402043c200410612409660f41001000c81c002c03d0713200d9030f106040c107003407c0c1d1400c1e030140c03c40e40c1418410886402228101e040c038550240c401d02e09091a03594510100b8050480501c020402c1e1042301000f082401c0d010501d1008101039604588456440451036001c0d90220307c801c030050303004030301d42e000800d91010610754400c1c09840c0114141600d036010a11304040c6100e220b00031030758002404850301e0148000780d454000d52622140c2100d4400024441e00e505205000500d980c502160400440603c141e81244000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 137831034 1250 137829784 137829817
    0x70e0403080c0d02180f040c0e0120060708010611010b0102060103060e0c090403050d1401050d030c08160503040906080129130e01090209060a0303090b0d060305010207050c040609020403081e 84
    0x19008a60017005400d00d21807055007004020402170a0900c10315140c1c200e240c1e102800c180c0c000b001540c1100e1059807000c88811380c20644600798004101d0903028045584e40c270400da40c54150000c0400300d050500754101d0f410f1003031001e556030303002034414103686e00315100040c81412140c0007031030302d203c050400340c0054400342000f06154114018090404071801b080c00313207a008001406a01c042402000d901c0b032003684c4644c2c04244180314614030700703200c2c0035a10b2815001100c149003002514201f1540b036400082c09000e1b15425008410045c400e01c030083c46030000031610202640503218169072b0750000703a8151032095803242c0c00c01c1c1894009030380410840c5440c0980324081c04080d0400c5c0e004605843c0410810308051603a902180c1c0c042c0e80345050300341400d42928103a40003520140004e03031980004800b160f020b1008000e843d00c14001060074035041005d20082e80d0b043c0d4041620617206020810101d0b880408441c22205610414800c628020403480107034050505001d00040c0ca = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 137832284 1250 137831034 137831047
    0x8060717131a07080901090c03060902030c1e2b0f05100f02090415031a04030e060301081608031c020d02040f08061e0705160f0b07030b0909070e0403080c0d02 70
    0xa0b840124055995a502d1411507500e07100031500781ea1083c400180340045120041020a05503032101e074080b0b100800b982c0c102c264500000b0722040410100030300c02000343c1e12801c1d440c6070509030518100302801611924043c141600c031440921100301501101044600c281007000c140010400c0071010364040200c1128150201c00a400c00b0610354080c0c0d1411600003403540700d0808810880e0f0740515984118901d070150b440c060a4040c000f1014406010b0703c484a070782d9010040c50103001507500410001286581c180b05505251b4070080d000d80003041090390340c0c2c012104100000a0a04016030b1706c031200d808810003445160b1010170300d5030142d4400703d802e80021030581d000d0b024424901083c0b103164100300c0000c0c68103569090102d4400c000d503a4140080041c80810940a0a004056000c0c00d8440c4a410203044404400080d030b0341c81c00b8007141c40c041d030700c19401c0410340c401009500e080c81c5000345076400190002c0e05110001c2c00007229045031100315010500320a006540303406 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 137833534 1250 137832284 137832323
    0x30c040504110705250b031501030531110301020301030501061502010203190f020d0c08011a1303140307060908030103030305180c060f07060e0a0209010806071713 72
    0x10020300505105a0504060041c1e080c40300c1d0907a644a504440900200c80d400c1780390722222210b00c00c01031040c0100d0640000e044070000082c6105908a010b91100c0380703114000142110402484058164061120203094117040c5d440c01207040300080c880d450000c150b041a82c40807030700951160741580004000f004100064024904a40c82e404180d425001c034071009a0913030104440b008004101040410f00c03120300c036000690b05d0348042400600d0485000c040300142c507951219a000b0480000c0104542c42507800694540c01f15241c006d82820000341708210011158130000e0083c10f00040402e02100c000e00844906a074441010842100c10b40707082d10040e0002d11081c0c01080c5401d0025103440c1d600c941c0c840d1000c4020000e80185805c0408101840d000303254584030008050140200142c2d040c825000103c01c004018540c20216104108507104141c02c0341030341c0d810800c1031102664100fa4512045548000054a00d0b80e944030601f0540c01802c0e40030302801d01c400b681c500880b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 137834784 1250 137833534 137833537
    0x15050d050703061508030d0213030204181209060c060c200615040525020709110c0105060616140a2103050a0e0c060d09050f0d030b01020601050f0607060e03030c 71
    0x1030b480f81da014852804400d031601102d40b420701c101291600208469070340c0350740940c001d000040407219204001da440b0307004102101c4000d001f000d051140008050700340101c45a007603003120b4461400030000d80c00c00500504407810108004e00c05a110116554914000c0e444416152030007182a49600304040110b0b94500302500c0f2002c42004032412941c01d42050b025a40c82101000701008107400c80e01f1180d6070301c1d042d013504101140500540400d03d248a070044032400840307100078036129014081c5a90840d000580030501c94001000200312101d540842c10340d007103400c00881d121200f072001e0560304204080c000206074241e03040c05911399803421070800c03c1c0089250b82c10460b036a940f400c5034040350710301256a400d90740030108515042c940400140000803182d40c002c5045131003a40c0d680e150050018200308250020403a0403605585489103101010b401d20003404a540740c2000f00c0c10390b07842c50600c41e00400000400e08144050341d0041000107a400c404c0b203030b036480c004001046030f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 137836034 1250 137834784 137834789
    0x306040231080c0a030f032109020f0315040f030e0613080105060109081b030c1009030b07210207051e011d1605060c0f0d05030a11180415050d0507 65
    0x103481e0041072624001600351102e80b40900901e2569003151145c088601c19064128104810903904c0000d05242c0ca280301d417610a401008201c40c41c0a02c104440f110300318405034040d500480c17448234500250710900c2d400c145c11003403202080125050890b0540243c07501c1d0303600f110340040c1d8601d800300c1495002c011510598000c0181d5101c00004594195244c81940085d902500208030040c0048a480015000003002c403644140d1801c04a4101c03e1071910040108880031020010300c90419441c60348900b179454441840d51b00c2081d40b1110040e00140d695101c0c2e07010420804000d070070807001200c80040c42080800c202d40b1190240680246100d000707401381151000c2a441e6000102051a4104220000c0155040600780b0040e50065101d032415446080c1d50112004c00611410040a4103035403a944d49107050030058080c0c075000c0300c550030f18042c10032400195101400002071120011600411400d480a000303031103008e003036003040b40d00602124a102c10800002a0b6404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 137837284 1250 137836034 137836117
    0x812040b0603030c060c0a030608150a1b050a030c09210501060603020f091c080f040906050d03050307120209030709050f06010309030903110d2015030603100203060402 74
    0x4160707203800a0603101d00403804d028507198800004145002c80c0080501a4a501d81c07030300140e1141d69003425464200c0386036290720040c11400078012100360500480c0e800c001c0b00c00070120300c4041d808005141348101e0100c08100b6139101249589280b00318070300da004120ba072507821a0300003200e031b100c0d1807440f04c2c17002100c040d0f1030400001071240c0240280c0e58092035036480c00d070800c48210107200102103036004051040340004807480003c2d6861014181c00101b03118a9030701c81d810144840c1c21144280c2060348101050110f280003c0c0d40402201e81c01170303030340c5406445081c401030303001d0180c020111510747c14018820701007040c4006510a600c218041c5007525042d032a290b005408a80c000200900061526032081c0040382800b91107100c00000600306200401643e220307103080c9c00510341c100308410003910294809191585810400304003001300c0c10325604100c1c001a9582c2550605403101c2c0f50048001a2580d98030350540f800c48510100c5a010a01e020001c11040c80c4030040320103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 137838534 1250 137837284 137837303
    0x2b0b060405070c0312061502011a031b0409080c120304050f07270b1201020901090506090f12030f160308090106080714040b03100203010e0c07030906080a09120806030d050c0601031e081204 83
    0x30000e10f00002c03d0cc41a40264002c80c0b41403090710140805094a0142540d480004124410450208120400c2401c428580060f16402c3c5807034010f04003060001c110314146c0c00b0030024401114a1794ae00c0154204a03070400000b2031215540c5400361a048000660280030540c40c90744c82c10040d001000320003026640d45070344c41c0d00d907003c000560060422403600410640c0b07601035541010322900100d00303404001c41c0e0414071201c9503000e555104140e11002a90402005401c054010a08540152680000b4010141000c51483d80c520003842209a441482500700980b078842c0d03803005404070b40140c00c0d507030074010402d1341d01c0103540f01707204001410040c3e100041c440ea00d01015a480340d9415601c1c2c40300e9500c0e03c00c08964440380540707155207560380d9207030100008002090f81000744046450755185840c11100f010b081031102079012003408020080c1003940040030400301d0550754840f04150102400864040c10159024001071141100180402031501070100d1244150b01c01c14501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 137839784 1250 137838534 137838581
    0x163516060f0201060b04060809070b0c01020d0e0102030f1b04030c0906060f020f03191214180106030f020d08040b030903070203010c050403021008062b0b060405070c031206150201 79
    0x101d00700c03001d601c038088000c403046c4800d0000a100b2640c203600b002d085000c8849042e2210420242a801896200a00d039800078250101d003055000d00403140200320000c508510f04600e03510301c0cbc02001401e080d02052180c0b00c8151546d060300070b41d00915001070005000b20344411280c00280918002c001c04030b1068403808440d244005403842102450501460030154200d081800b0751065001d4401400000c48200720605418800c85c0181490720440e02080d04040c46180d0380a420888800c2c10f43c0d05018003840400e42900348542c00781e078140e42226030245241040c489a0140da00030607090140003041c400d00f8030f00040500059030084000700100e10b85098103460600c124400250001840e42c043c07520107015840707803903001c08050314401d180c3c40ca100b4032220410340c401e03640c20090760059a040500402c105119840380040d1f034104000d0808240103001c00c400000004c0c20040e141162000d0b1281d1a00824018080d11001140c0c54900c0c140180c0a07101c5004a00301044404081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 137841034 1250 137839784 137839787
    0x204090320061012080403030e010909110306010f0503060a0b03041407030c080f0706080c0c01090b010b071506060c021c02150301031b0515070c0e1305163516060f 72
    0x541d01c44e9501090491401e0319540e02958545070545003503050001d25240040c21002078010600c0c0c4043e8102c44540d680741c207078005052201054005010803000344200043c54030740d44161410354002c006540d45036504e40ca41049100d0744021089014001d54600008000800f41000d068a040c0c2d026110400301c1980c0e203aa45a09922604001402c000040b5142e84050300003000c0d4090124004900460341c3d4903402684a42030b07100c40701000000580c0c80c01d0103100300d0f80c402080851381080c850a498040000c251080c0348030701900c103d034842c0e40500e0480751084503c0646502802030300b982c0700c0203140070000390024407042d1071030514900300c0020304402102c200203407075001f4000d91000c1500c011080d00c5d500301c1751080354001c0f070248010a0b406010a20a031080485600d4680452503500c0c01074109050101042050b064401080c0000600079031110800300820b02d80c4d2001d090805002541880c83c410540045d01034503035a0000c00c40b00d0b003a804c1c1650703055240c1080d4038444940 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 137842284 1250 137841034 137841059
    0x102070c15050a1b061a040c111b0105280e040e0a0b0604091a0a06080f07051c060c030c090807030510020a11070b07020f0d020d02040903200610 64
    0x3501e00004000304800c035882400350f40c40d03803500703610000119600700f155a1020b0403224807466901044201e201c4c0d040b43e520b0310b4021b00c901d94030342e480c0a5442c02400141d00761340c0d0b401400d00701e40c212080c91840d4101c0e48034105031510030300c00a880c8403240b9808592080002c3c1580314540000b00664030700003080c10700b4051424100d400c100200100540790311006190f6101604082d40309444000500100b2a0040646021156204501841e0505241c207604560310350348288001c0d001021018054074000c103900c4c0480300180d44401c054403002003840043c4041140040406160003005141c00d64164000b14103000a40c40c0c0401054603501c209a42d5100f03884028090b5206070380d0050398000a802a0406001f681411002404070020072818122590407912044102143c0b50083d850301600345104205c003901d58500c64005a00400c810404e2104042d000d0f903201d00c4044201071040c0d12298603040001c920100c49100d1400c070646449040c2c680e1550418a0a400710b2000507440c0e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 137843534 1250 137842284 137842319
    0x51b0a17070506010e190b010233010e040b0a051302060307020307020405010f0f120204270b0a050606040312020a0605070c020405150f10090e01090504140c030c01052a0102070c 78
    0x2281603d14a0042c146d5501a02074000410f045001d0075800340000380307003544410903000401c20444222850140e0032440044140c0c0070040101c07102080c07101003809504107a4000110203404140c0d641e40300299507842c00080c030000d400c41c00000401990340c0c0c0c08805040c45610032074051080d41d98811264100c6491030041c1c3d2005054564100407020707071100402015071019101040d290304070071410b0144003c50b0241c0020f00500d41c0008100b00b10030883d1a40064590010082411310b00046440c5004134000240dd030b002d07110918541c40d008000000b165a480003081c8894a8000c42c01050710038039000c105e0141c2d060034046005202c03011000012814042c00c00c3e07900d41d50750802c0010903890303010414240300300c440020807054650300c0c07454041c050619000c6400e052602c0c01c240408402c603402a11500503c032940950b940203d041c40005000b4608107440d840901c1c0c802e602e00714070810350f0425040301c07140e25080030010340103415a83c0c0a11201d5003019174aa00c16804071501c80c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 137844784 1250 137843534 137843551
    0xd0f1103060105090406080609031b01060e061c0b09010b01020c06161118070f09090b010e011202040e040f0c0b040e040b15180a0605010c03051b0a17070506010e 71
    0x2030000034950751299004d0141800300420100741c095449011500340b1406480e20482d03600009105d192400c6484c54000160350180020444613250400720b4958090181001c0d209041c0888000c2c2451740b09228080f5580e00000b68614a040031417070b46008111910310507025000d214030824141c07601c00c050f94041090216160001c1c070840e40c803014038010401c1e40e80d03404503111609004104080d41000d200d41c515846428200f03500c44406006c60b942941f242d00b8043c2411022903180c0d9105549440b103403400c1c2000700e154101900214064002d94005c00043e0501038100700c223003e07403410012246402120075141c000d880341c0d016490b921587c010031820300c000d40c0110380007502d00701c5260f41c00402516020815801100007a5082d10036620b208030180744481030200700412482004000c05007401e050440841c155009030060003003070300031110740c505804d14450004040c06030b080322030761102805c00b004070b64221040306034228040a07070b203503c43c5200211b41181310700078160203039990 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 137846034 1250 137844784 137844787
    0x90f030c05060903010e0312010e1005010c0b06130c020c1201020a0f0507020a05090a0f0506010203091003150302120312010b0a0914240a1b0f020915060403080d0f11 73
    0x1000d050003410342c090f03124690559621030520050300e0302440940204101008030709000d51600210300041074010b400607451491a1000700032a030717084a10042c415612a0311210140d03126400035601a0a091044c03d0b564203001001c00195408a000c0c0c10040c030480b990360f0f00d82440d0241508034014540030311f01280d2802d413001c00b09401030019000007407006100b440110784640200340f5a44090324084011602d400000454001c5801110717840042840218204001480083c01441d8044001000c1c1662442800c08964150310110040e40d0060f0003215403c0040e40f295640c1d82c810000c902c040740c0110004174031144220708503815000907690300c1c003a003410205880c100040002c521907210070054024107a03141d0a2440c1c1c3e1300044d01200d002d4495080714400b40102141e584040d1060245415800c00105050000c0042c55015624446113a803603200b40040103005020b100c0d0f2200c000f260002c100a6414007c02405031090002e2003464101e51021702541e88811014a01900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 137847284 1250 137846034 137846039
    0x406080f040b220804092703050a18031e050d090b0915091e0112060f170312090703060c020d080c0a021006170d09080d080402120102130303090f030c 66
    0x50000140030743c8003402d0092040103516950f03080b40c0d41c80b80e03100c8074540740c5810701088080032101c594080740a17102001c0c809001c56070b40082c40c511507080e280050000e04804000303281c02c5410900061540b0426140e61469a100400b40400417050708542902c24007070b1003603206105682c07035811181010345642c05c2000480820510141400c20f254003c181813255400c2c41d52555402c1c2340603003100107205102d89000b8001050854044402c01c0c0690402a0400c0300598140b5280300303d0380c0c201d48600740d40103030004040c10361140516041091508a00b41f200702c00000c1030701401c42c2e109003001c204407505148240c3c0c482004030414070201e83c00900269264070041c009160803461032042e100c059500100c94011502150080d2103040035001d240002c2c03000422042080c2901d60414882091030300f1901696450200801d0f4104003070100441c0c115264821081d003110601d100079529015114482040044e05100c20341c0014a0000e001481980101c0404260ba40105100b640c050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 137848534 1250 137847284 137847301
    0x1b081810051204030302070203010c0c020a090612290109060e0a050708060906041803021006080a15200403050a021305152b12020d05040506160303060512030406080f040b 75
    0x1000030819130500d5000c1041d44c0050740c080c4a03002158029440b071004010150051120800560f00040700a9240010030300194641c10803814449174809020300021400d4600c84583d10050854903071020500f10011804c81d0345500030b0303810b54440c4030f14598a503540358a50029600c05690b4440030511000106485003050341d04103611103230240002c03840170140b4250310003e416203042500107801884481c0c1100042c1d009903001443d0100c024010440e903a101c03070903100054008081860b80e1182e003488c868000306055058003400c0c42c00141c5940d50780c2003071503c48014403001c9104403410b03aa140d0a0348071030b100c1c0b2406404000000c0031007400344e00038410340040701c0c04454101d442d4408048000141c0f40d03146075080b8440c14440102841141c00039107040100c84400041c80001d00c82400a510303142c0688541a441072014902c040c40360800741c00500060300f040b0703002005424a51030258001005108841b00b07941c1b588996503928030785c0444102c0948006040100e4540030a0488 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 137849784 1250 137848534 137848567
    0xc0b0c070f08010b03010b1e060304051c0e03060f0403050d0207020607050a0606030b2203030b01121406030c01031a012102070309030b01060c0309151b08181005 71
    0x500a1404458500d40c441807140403106440c1c0c00641103a4440700780441c1d50800380620b0100903001d0710301568440d286440700c2807401080824502800c800b100160501c0744c100b00041f01c140c41c00c40c10040138003081400810700036159800600134840d070310201d80c1600041013224481d642540d245810122242c504601950020320183e9020409011100201700244051602c4501c144000245240b070341c6805c071850300c401480070003041e800701807820a040c0e000d4691001d483c1e0525000504d582c0031801a0f81c41000c07111080003041c03030076455100800c0e00b1004070340220b5041f000c450100743c1c0c500044054502164015114a9103402850801d502904400c0000422030a00120714096070003220202e80100c1d900b40c000894a143c2003060080f0443e059001d002c081c40c2c0b215086006803009020611135216511f2600c0d00403043d01040da00c030300d0a4900384510205000b5802220f41050407817900304011014030011b1004210102d4a0300700b040d40c0c460740d00c98a40f5410501c8810b4042d412 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 137851034 1250 137849784 137849797
    0x307030c051801050a030f1e0606090b220b030702010603030e03010b0d020d0602040e0a05040b0f1608040312020c03040f060207060c0609020d0b1306050a0c1d0414010e09010c0801030c0b 82
    0x1890b1f2100c2c0078041e44480c602480800714186540f0896050684a52100756155640028140401c50030709001c101d20850842d04d00480b0b400c8034482503101c460844c4070a003001d5001038030f174240c08802d200c02503a06410100440313010342e940903030014400302058203c4010313012840d4840b40d88118400141485850b01043c240906001410309035219126800300400701c40280d8261b03a40c804000070411a07036030380781e00000d0300524881180b80c80c10f103075074100a50040500c14000e0410000b030400d842041c1d03480c4a104442ca0654450342000d105a503240c0242c0a8052800710344040410014400910030040310300e1580c0d2040e440d8126181d01c001061101020f036008408114418003044a40308200d01808050011051007046030900900b2107034040c008415031383c200b9050405045d032102c3d000e4a0229a240c90041360000040094002c1400120501071000ca020001444e0140c03840d01600c035966060003807009004904007242c0c0400240402000c0d0800464240030341244107018080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 137852284 1250 137851034 137851037
    0x7080a1a060406140c070803041d070e040209030718150b030c070b090307020307150807170711010e06130302060721181b0617090c04020a02030d09080307030c051801050a 75
    0x240805c11440700f420a210703034000e1540c9900000d4100440101d0900446041241440082072401d04150007400350b8103644117188225004240340701e0b140c0e02481100010100700800e2144602020010009000c2c0c4d19020304501d4520ba10019081c01c00c1011242701e0000200c080b07252003510794900240c100003038241c0425100600904005880402c2b02c070002d84074103404a61980c0c0c0c3c040005101e0348008040c4820401d032904016920040c0c5039803180c21000d541070a607101c20304d50a842d0700414040c072400b0b449200e402c0a1140a1058961901850b03000741d0a070385c450340e80e11100380c6598895a4500d80c0c13120140d002060410000c0e802950318010511004411a809403035103000301d40c404880d0101c446080030700300300d1160400e11400b00203522003486110b92410f40800c82e143c1c15408060b501a0303030009404600e83c1d100b4403c8801c0d0751302010040150b24450700b48050240c00448503900400e1a01e940d42c54a00d00031300603176260090304030b154103101440200445003600543d16490 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 137853534 1250 137852284 137852287
    0x3060f0d140303010f0e090f1203060114030f0603070803070308130201121506020c040c0507020d020a03020303040b070318081b060d1404050c0103021e030402030a060507080a1a06040614 82
    0x7004a020300c000c500030a1000781d180c604509007181e003564040e01420000b04da80c031650b541106030201140814000c1002400c3d1501d0f03580d44801650401e007004594516017030004208046541c0050b0254000c0b50250219103459440e10707a02c5580e845407840141c085100c2000241300008501c1c40c3d40801c03407040c982a4052805154903406407500c81500c1400118104800e00542d40d040281d0301070304904840a01c200103901c03001074218864240040e014100200711901551240c075030031401181d000d401c8230743d40d640c1c54600c502a40c1240c0703812800185846d05200c84070903212900ca0549854102600924015150742c0c08281100d0740400d821800500a40412401902c03502000000716903003c0c806180c41d1078440d007805071144001b0305162061185135020112039000107005040c0754040e580c0c0781c84500000703140680d00000101040d0400c002c1110b46a0f2082c500f5025402e00d080c180b044c4080a40d02141540042c03179800c0d0003020510003040f2551050103079071202c140c02d20805 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 137854784 1250 137853534 137853563
    0x110a26010f1b020d050f180d0203031c060b13090c140c010c0e092512090c180b0303091005040f0323011811040b0a090e070b03060f0d 59
    0x20382560316250031002075000c042e2041600d035406000040002c1e0061409910340320181ca9600418055802075441c000a0807944a015469400d1900d08a0b030700242141c1d04d5020381152103045482001c919044282800d00010711200018142d0f0380306609403100b44646410324591600820b180000f600400c014000d02148141151006000340084140081861100307203030040c0c10840c0c44007040b409201c116082150411034000400d151100142d505010412300103001caa1402c14131144107200f174600031281d010000d0b00402c40b030840b0788844070403840400607420340e422a80c1d400003064050b0002c00846130b1524241c20001104801802c1150406481e0321044d208a44603410844686104151486050250491603070b904c0c0c115500034041d5022080c048055038400c282d0041c40100b9440110f0803d80c0e590308a00491400500704120b610307a030300c0e030820240100d440c034200b85000344540440c1880030302c000c0b00c1c0b099401802c0045e00d200c1110a00881215441d0103548120007100c42 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 137856034 1250 137854784 137854811
    0x9060804111203040501020f03090a1512020f0406090801090302070501080a060e0406050a0b0a08120904020403051605040608010c020a081602060f07030207060807021507031d0307110a2601 83
    0x2891140b540074000d5440b0380c1400c002902d808643d0294500d107910134081940390340d0319441080f0580300720110100700d0342c20340308068a0254040c4120000e0358004195200c1c1411400050002c948071540da4030407250391540564200d41e10014054010303000080180515406a414a60005000040014100e940303e20056148100ba50200d0300240c840c1c00348482d03049907000c1c0c890703032400460303c882c03c0c036180502050303a81c3c0e0b14100d0b4404501c00801d00c04150760b11507056500554000302610711450754a040000c49250324007034203100c0c0786840e2001c01c070400140700e020b980c0d4103581c000b4820011240c540c00e407160000070b52411030741030750209403005031a900054440c1010f60b01c80c00d0b07141c01c1e492901a081c01020341000007080514004c110000ea8001001e07020300b0501d02c4151156260f140342100580072918507504918603840c1e071481c5040d00007000340f400a02a220b100240b040d2042003000c8422a131140100310003455645500f403020048440c1c0a107841d4800008880c0042c140c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 137857284 1250 137856034 137856049
    0x50307030c030b010b0906041a0d090f120807050406120f020f030714071113091b03060e0c090711010b0a09020c0c04050c030705090f09091c030603030906080411 71
    0x20407105400329600400c1001100362090340034050900b10700d410b115040300031036002d0150348155400c0b40030421011001a02800c1164102d212120040c413003800f0701d0600801c0c00720502c8040b100b207003c00350102c44079407103011454002c9905030703500c520702407a1074002c80701d140034004540d038542d5a400303412060000500c000c1c030661070902c403019120310b0400c10103811000c1e22a104e01c459242000210300056401d0061500c0400c00c6a800c0c405100401031000201a842c3c0002c0002006840c103500d1034045440c6038040301e11071082407142c000f000211b00d03110454080c1641c0c02c0101080883c0701140038000c00c004411840d40002600d5040d040000c281c3c01c03042e48803d00b1103a0025059111003403c0c040680640700c00d54040c03013241844d4040068a1000505080c2004808a80d003101652a424000700424004140200300e0516000d21901d0b17000554045500485c0c400f602c4140902a000709011a40c02d51a40d000151038010280c0d40000020022a030407440300c11155481d50302c078071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 137858534 1250 137857284 137857289
    0x50a14240d142b05070302150a0906060e0105040c090e04030e0d150c141201210c0b03090f1513060209100f0207140d0f0201030e06070c02040c08090604030e0a050307 73
    0x140385900700030065002c9910010350f1a1403808021041105e040440d0300040d11804c0da03007141f44103001aa980c81c8280004244001008204a08040c4001070380060505c0c064180e8008039000c008d070f018004000e5525107150321424952148610000c0c01003801610089802c08010380025140d80c4240e5907a4806c0400c80c458504441d518030096a906038032681070003482000c1b00030546047d00918600ca09414144140302c0302d00e0b0360340c1850001d6140108090403907540400a40302403500c03010300c00050f400869402440b840b40c0c10308003680050000e15400c482413545e28900c550f0721381010526486540f80011313a1016001c0143c50f0300380d21404141c5240280580d00c211460704d14440c000d04200196009c0c03098482125000340d420350313030b45030740314069a4803114021070403004c2d01c01030700038240300c44400c0c10034001e00041014194000480c04440c502c2254104021f203418070007664045402e941e0302f0340301c3d88040c00040000380100b84c200700699005200c9800f90f580c45000914107400e0784c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 137859784 1250 137858534 137858563
    0x90606070b070201050f06010504080c0d060209100903020f03030405130c1713020916050a1b0204050408250b04030f020a08030106050d051003080712030609050a14240d14 75
    0x201d0800071119480196640c111f402441d001c1d00c4e00e4585250142c1e62002044610312510842d0840302c02c0200580c111020380c4005842c07040c02e9801110043c0162220303120a074041c61400d06d000d07085107000310882c0c054805c010104000f42e8415400305005080741011101880b1002c16040095011802001d101f00f000440700f90004407075106000d4102c2c800b4096002206002040c03400090f00304064910090262802c3e115081da406d41443c1c0d21003090310007a401074900b034203010900036101c0c004d0181040c2b0313079050b1800151550307804541d045044000b40c58070317401384007080000303118000ca501304124504c110b89244490741c84413041d50b4001c2e070140010403800120340701c3c42222400782982c000e45c40014003034034910350b8690b1001c40c801c102008205103640603408204034000c0d40300c00c0141c00020b10401462070305480000042181c0d00c00070302040d20301030014046140270001c1c080c802210b142d00a4010501d170041c0006001d00ca40304031082444500b240521907800c1002c0c0310180600d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 137861034 1250 137859784 137859791
    0xa050f07060c02010f0b031c09031401050106090b0c03041404020c151f0f0e100f0801020a08090a150c1103030c090a05030a030503041716060f0c03140105090606070b070201 76
    0x120348001c0c4c02c444607010004a440d041045400f40c0744e4000c038080d040e0b0010016601039004001a0460700c03040309410003008100314010103120803005512150590759240c684078115519520a607070f160184c10004412640104014860741000403180600814090f00150408a00340d844504204413845c0142841a040c010411000c44ca4001813848204030b0703000084031402c3c03062110708240b050046105412403203021410b082c1100200d000140782c0d86441d02c4206403200c40c0107010794440100c0c00c0000310a1004a0420300700401c8044502e64400070f54001c0a2484100f24050030b200742c17140051120482444c0d8582c802400154800d41c41c5602d099544c10301c000401c01c1c0d500c015049540664000c06044001940050880c1c0d0040c0e041030411605c00d001c2c4021804e0f82c030650140030014445090103108000341c40d048103906a95121091105541c540c00450844805110443c81041e100004000340d0811031141600000d015000754a408040d4845010200040d00c00c138005239034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 137862284 1250 137861034 137861051
    0x170706060308070f0c090b0603040b070908060705070201020d090510181509150e01080a02090f1503160503060d0611070c0e010305010c080c040603050603101b090504200a050f0706 79
    0x142403141038094040d00c14100042487c01d000f20700350340401080106a0301c020350204004c0f40c0150369400050104200700c40301880c00c40d100070456045400100d015205000c50086081e000310054025920f010b0600102804250070854240002400030030481c03a60a10100f240803002010301210358150311812259441c141550074a0b0381180c01c0c1e6401c01080108221490303030702c8800183c005202a801688038281200000c0c8141160040c0783d910050500d05043e41565442c0514480c504020328291904c402900681d1540320807680315500c9035805030b006001880c035500c880714111000131180e0404605039181080c400b000d40024100c101d0301c500401c1041000d004410003100a0701d0300040a08041000e800540114080c20092503156000a12107440400c0040301c0d0800010040c403401d803002c1d40c0c0480007150300c0d504500080c3c8201000ca0503041c00d0083d8507045041800c0e10090401980341805142c101075507900030840700700000c0202c0c66a40c2d0290401c035014100020701d160 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 137863534 1250 137862284 137862293
    0x60b0a020703302007060806040f05160c0602090d0f0c2312030d0903030203090c01080405030703050c07090f0b0f090906060f010302090a030501060609060c170706060308070f 77
    0x11006002005064103000403200d42050003501c42107143c0c0c0074104011075802c1c10340e005840341d0310b0000d8821030384985d0000081483d444450320340520300903141040440f18000400c41079810885180395182d94020345094414455241000d03402d0240c400182022010f00004140c0d0000180980301d0f0b21400445030103100406070748800803c40d1400150b103009690000300390781240090214400c821110300c41c1d04e01201401100c0200f0007841040000020741d1401400a4100383c82030309803441414090400355015113206ca0050390000d0041d4100384059508840360b40c03000c0580c0c103540c01030400000305400180a5074610050700c0001140502c4c0110511a55141c3c14003840c0c4181c00a00034880088408900d40360800415103243c240c0034203040060300607100c5c109100360000c5103104000b040c01410760100c2e00303441856580d151510380d100022100644000405440822801c00c0880184014030080084c8c902c5a100420f0b0340f5600e4030352134400c0d0040d0100313807005014441030b0800c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 137864784 1250 137863534 137863553
    0x60509060a060f0e0a0207030c0816050f0309060f03040302070e07020d03050a0b010519091a0310080606060d0e0715021510060e090a020f070f060e03070b06060a03060b0a020703 78
    0x2005440c55403d00c1d24504400110f03082d01c003900060300c5a07400a0380c4400c0c0f40c40f500c0159055900700c4140c13641c40040641000c0701507200706040c0c40c107001d90300e500f0540080c084225007030000028007260814020035101820741d4000f80045081d4494000000f0b0350721f9a201e80248984030380c0c2c0150421010324900903058440041031107222500d007a000e49140e80e048001d40d040c520031422402c1c182802c9110595082000c2c0d002140061803004280740c2c104406c2000310300c0b40c42d03004902c1d0312a6940e042d010b0354500c2c042e20403030350003001408400843d58269100143c00300c0d04208440c0e4507a070700c1c000600241c0210403188016080780d401454200c080110b819009411f5400480d10b0a28111004014500b0b45a009104882020106650100c80d40546540e030240484103556145289014841900fa101d003c40d001400c2c8041014405400310036240d2140d00700d03d04074216550030b41003060307a6100040510505542d20b4000c030715038070944040d00001c0807c0d001404000d096003054002c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 137866034 1250 137864784 137864789
    0x9010609090308040b100b0f07020a0b12010b07060204090f050915040b010b0d020706060e0403021905100518010608010b1914100203040e0a02071104051302100903060509060a06 78
    0x4241030180c900c00180d4410718880d4040c0d080145d64410b038a070144180c1c50724509620600880c10042518195800400028503010340b00b20790350000c2a5441c0c1c0c0d14400743c001d0003018684d80301d04a0040008000440c01802a03a100b0b400040c0380685841010317044480f40035140e0f030503030303582d008001d1048000c01900542046e1150708000d10316150740c2d60024444140624041000041016009101d4a8055410081c0e0104c01401981e403142118903071020700b140c05800500c1848800b03042c820041c031200c2c0800742c2040140c400e032a0041c01070400f9100c05003021080c1c040d0011a44610502842110040c20074030b00007080f9841d884040100b942c4501c8030142580707142e4842003054102251000e1210b6106440d944200d109491040c0c1c03e50180303603c540402e80e19a0304210400c0c04540c001c10001d403054444884180050080c401151011602c2900c2c0a0016900b43c0c05807074101d0a405900d10700c2c2c508810130b19200c0c0d81e0102075480c182c406d0007899100e9024400c4070346160052201 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 137867284 1250 137866034 137866049
    0x2060f0c03181206060d1202010b0d0f031b030c1113091a09010b06040302040b06070b16082d28020c0c2e05070b070e040b0406060c020f120d08090106 66
    0x490808000140804440341c4004040c3c154035487d80111030300039045070700fa01c50001c01c141a942414140110003402c06001180001d04544100c07488290341c41c110000180c0654580d02d4141d250795030104040da4510900c2e1b4086070b00b00e08104d00915134007488046520441614007000c200c480c689150080150400241c1d03410010310500e10b8540401740c0b0201c03601110007140c8501c0820114195228044014141000190400c441104407404a50550545544004581e594140031820425074590340ea4141d04108660f4040c880341c010942c0d80044440300710719003d4000c11649000c61080c2c100c00750b05c80da00400c0d031110010040c40480c11000050714800e60401c20020040d2060a104c4d90390300e0021043d81e42060f00502c5403042d0783e03086a1120700c840080c03c00342e8002d4a2000000b10f5607104038207000070b0008500781030281408841e100c0d105c200424407a9801c21032108031090902d504688520800200b40000f040941c403855403075211884541000000d203400d451981c1c00c41032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 137868534 1250 137867284 137867293
    0x90c13050109211511030906070504050904152a0e090121060216030306031e0c1403100504030c140615010503070509030708060108150108070302060f0c031812 70
    0x2076041490400001e603c0303a00d071030003505400d5140c030415110540406402d220b141403040468109240000c43c06461800c08a4413250764200e01100d0070300c1a8000c55820440001c0810009400b6007002606045621408100455150040b10004914184030040b40f020528200c0c0e00e56000f4105046611080d5890b1420b503042102c00106a04071016000c4000001e01005003402440da060b11081c00403207017241030002140c28020040d00c441c3c002690b04070390303c4e050110b89003843d0341c51001e001d6200700300c4c0781810b1402c2c014501048020b5011074150040780e8043e1071007441d0b4442c4a204034869141c1420800701410240124164109900c40c9a801042800340d00688100020400102442c00a580e5510b04004a4050107901d00703064240c4291038010514100115030b860580e06030784103c03409400b0b44c001c00c400c0c00800388140000c3d500b1064080c03001d814000e008050510580884510f05002c1b1400b0600d10340c0840b440708000c981d035913462121303031608020f1601c0790402c080080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 137869784 1250 137868534 137868539
    0xa05060903030a0b0d110f011407060606080a0504020904030e1507080a020606060a090e15090f0121020a0b0a03020f0c0309030705090601020607080a06050a090207060c2a060b090c13050109 83
    0x104c010341b05442c10513124618245c0d403030308070fa031251103024152015a80f00c1c5446400a150400c0a0140c50040c030020503c820000f03100c013902842840d1090360010a511265160f60302d06645440c181c1e0526034100040c071b103414082d00303502030007850700901c02d03080c16907107820914000342840c0740542064440d0b00c0c20401c22480547c00a1040162000c5031000140398071202c003c2d028004000850a0300114400e0800242200410205049500a4a101e140f403c1580480841c00b0760345000258483c0c0164010303c03450150340c01409070091542001440d080005007100d401d81c1000c8294845603000158030b00d00d030b040c2400614020324060702e025643c0d0410b040040c0d102d80f00201244c0c00c1001200002e42c0c9000f6036041a0001c14020b024081c400c3e4a8101c03407006513028500030785000b400c10303010580c00f500c07600d41c4811040c0303000480c0d40502d46445d050362a28010203400e9680c0d0351580c0045801d030740c4440300355001e04040d10303840b59141041c00c41c6040d1021240d00580c140310b03180d40304 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 137871034 1250 137869784 137869793
    0x1e03010605240306031e0c0f0a0b07140c0a03050706110120070309090606270614030a0b100503040201031d0601181e0506090f01080c0906030a05060903030a0b0d 71
    0x304211546a000745600d0703035180800300b4a4041480ca0400786d0102104200300070311008241d03e03006000665612070260340060a01060b22001c0c402c4104002c8208801c002040c50603a10300e0000c404403054441080541e400180c2e865003d800603150b5401c400401c1280319040809580c2c5115444028017100c881024588040306200e20209040100080c1c007008041c8544000030103012380e0081008029200d441c0203110740460a1048006a102069840c5403550b803101030040700c1c0d0f00d17a00e00780b0100d0a20750803101508046d043c00f800700d49a801c04d418598a10681c4100048941e80340358407403401c0d000040650300c400c403004404d9071003140382c901400c0c1e01185041c10350b0317800d0078130001001c008441c080092400358110000c40342c88a000d41002c4940380c00050181104664003400c031f8440c05100c2882800038407440c01e0a41c01603107403041d00e05150710101e600030750081c00e441c811350450b111141000c2084a559a59400000401140c07a5103407046400c050002d81e070b60311020040796103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 137872284 1250 137871034 137871079
    0x31903090309090e0313060f020d02010204080c0d02130903120b010c0506010e0c0d050907030219150c06140702060712090b0c1315030603050601050904200f1e03010605 74
    0xc0c420704613850385058044140304008031400703040c506070b40c0340c0460ba40705002028030501c8107036031005001d00350101880d544140295402c3c3c412074000b40000541c044201702205030011000c07604080300020b80076241d0003612841d4005c41c029264001801c0c40456a14202c0c0d6905100d641400048010710002c21400100d050540d40c1174210142c0f0f42d00c41080e8034480e0b0260280c0c181605080c0b6040051441002c90840c04492003510741840c0c058145c202c494a64525005440b000d006100c200d60107130344513004049100d80150700025030311043c00c40300340c002001240c540c03016900060070722810561100f203040489000400401c500800d030340d03034006041000341903507a2040000c107414407202b05041c0d80500a00d03510000c03440390301d00490b014018000521094a042c0100000051641440000c2900c210fa100850000c3c081c0d285144a006c6601000203d42000c0003141d01c000f0703a121003e186100d07190a0000520124610342058207440305a00241c2c003e808180b1100020b084908 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 137873534 1250 137872284 137872289
    0x30b010519080c0f0f130603050c060a0503160509060304051501081908180901030f031103030709030813030510270314030a09020d0b0f06010905010e060a051b031903090309 76
    0x202c0410104c59a0300016201094602040c1d41c080141441e007800010141e028804891152003a10450503144080109501443d05104003081c42040052103d03240c034013184080380034a04000c0c0c184a807540104129402c11a03040310b0651004040c8812041d0840b841d5006040301802081050b4203003100d030b0440403c6040041100c440894514000001d000c14250301500146c00c4452540e50313030038410580c1d0701e01c8600f41c003c00e11310880c151811001008070f921800c8070383c45601c00e4030301d0360350707002c40b03c3c0d0014450a000303900b40d80020000540911141d0000c0b101400040350100752101032860420101403000c102042c400300200001790410014040e00d00c0207000d80b42c0b00d95a08490101402403208003d50082540980e41c040140070105980244d1a84481c41302d540d1b140001540d01e5901070003054082030b04a805404580707024401407401d03070480d1070b00034208202c40340003000d030303201c00141c1040070340010071010381c20b81107807000982540c100d29050010392079a8030003802d81c90b282d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 137874784 1250 137873534 137873539
    0x3010903120b06090d030c0210020303061f0c0605010806010602070f0f0605030405030c0a0501020316020114010504020a2007080d080f0606090a031407150e1305061504030b010519080c 81
    0x405550815569072021340300500c40207061002450b0349464001c00718200c50381e08a11a5001c4414152060b100000303607407203a600a0039900030418405508400d140070740c0c0409040043c0c4a42140000b48240100d074001e10301c4c3c0307008010319418208042c1c02c1c12200d400c600130121007188108408548402c05004803105e9040990340c03512603040040c00c5124071f441d88640c1c0d10550684004101c070541c001d45c0302e51420351130032418903140d440c100e00342c0301038034a10120a1807020050041c1d107400d82c020048606503042948100200111044d02e024401d40003544a4210b40c1013007001850600103400544002d01d02000c140c9004500300f1101d0b20f015003140e004040c0071510700e480303031075101503280910303041143c808900007440ba01c150350b200306002d00798941302c6000c51080c0841c02800c0070022088010030312188864200110b4004100c0100b206501c01103000d0003040140300d0600900103180200c000d00e07111341c1404107006628025141c0c40d01158408001000202d2000c5441d010a0204 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 137876034 1250 137874784 137874791
    0xc020c010906020127020f09161709030a0e040f0e070e010b1204140a0f08090a05121203060a0510050d0605010806010507060e0c0a15110604120c030c08030a050f060301090312 77
    0x4900201f6501c04075004001c1e0070181d81c0c1c042c44030340445120030440c00085655034040780080784503c1d050486c42510302101c250b000f4442c802c89140101a01d90400c40003800014480c0ba422002d90142c0f00020001e1085412070f0340144600e1b6048a01c90740074040850300c4500d0a0310200700049402d10082001e460500400c1d100c1c541c9030000d201c028042500200d8040c040c2d071035810402c82c1d991250411b10b12569103180300042d2424100781110010040c50040c02c5d0070010300c501c00c1a1607000510055024292500210b8581c6d680c5038140464160350f90f5180e1101c00e00d03100d03a0100d55058000d18144066038003048541da91090883c0c9641d82c0c04140401c0c0d0b60401400075203008508001d080d4403a0f1003400205440a0003d00390103803003540d0b5604d200c00c2051015440c0c80740030558024107003228860740c00c0300060049021410b10b40c802d24040f0181c02e0151202002c3c3d80040d1181c0c82c030700d5150414490070114041900f074006504500030040c02c1d21680e000703000310140c056101d00b000d44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 137877284 1250 137876034 137876111
    0xb120a140708030307090611010522081201060e0307061409060f0c010c030e2503081e070602030f070e010206010e060a17030904150f0b070f02040c020c0109060201 72
    0x800340700d140002e28008080302d480741415040904940745501804001440240150a6400c014061a8018400300d880d025200945984100c15143c01c4c0c80d00340c44400c41007204040c20700d50781c15258024019076581100c0d207480c2d0403c242c01c0c0039031a1320020820088501d10460004500111038454204460341517030781c2d11010081e001c6001d021043c0b499035207084040f4500369050341000c458480000c091354090700b820388d444512074030780e08080340002c6100001800003400750002002d030804068006518800c0c03c480300c502540c80700710304980d80e640202c18448080402d4800310f07005005401c00c40c070f20b0400440002c5d5180d005100b00c1d0404210b01c0040b030032542342c1182c4031000d4100c4242204d111031081d8812a036903803004c11224022385c42c1114004200d40340d0b60164041e9120701c81008030700fa182a5203140503070001e03079003543d03500f0901c0701640050350f9912809280c040260080c000403032114001402c0301580d81d01001c02c0da414018040c40b83c9100185107a03030a04c0d180d45411a451 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 137878534 1250 137877284 137877323
    0x9060f090709080d020d020c060a090f14040b0117070806010e15070c05240c10060e10060809151005040914010e070509040209060d02060307030b01030b120a 69
    0x14001540e4010000800384580c855001c0d08210940380020100c418140304940c0c101c1c0d569500f00d0030400160402c00914100e071401c0300040c800700c10f05180001041c1e0b03c0304c840c001c4c2d412603680400354080c0300c2141c0308201d0501d801102e450080c00d080401050045901d008130100e4014491400c001d811000100113a006000c50309d100d5101074004070103041c089284403d16440b07400c054400c4400703058001094546200c0e504500c03182e240743d0401c03100300100c45180641103408580d41d2800b8003109485c2c0c00c0c0c224410b50004019960807200d05051418400b55420313207075000841000000010003204110002d240381c0540345203110160304e6a40c0250f24103410f0003c2d0003103640f090403c500181408100a044143c0842c004000c003c01d070000100c1c42d6888005200360303500614810f00040141c6030031a03401c0d9005c2400350451079070a0301030380010000d52003101c0310004a40e80d404004e0055078540308184a15a0544040190340c101c5410036580d4040c8140c010018080211910000c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 137879784 1250 137878534 137878549
    0x3090f06020406020c040b0406030f0311030c030d0207020108070201050606030115020309060a030912080105090f07020102091003270803010b03180102070f02120d120c020307020d150e15060906 85
    0x100d4121600719242d40c2c86603030003501c0e40075420800303100d41d003000710030015071425121f000c040340d900000c8604555415903040e541e180701b19446a06c14001404403005c480800e0000704208142c05ea001661a04213100142c0301c800c001e4041800c40e894841005056100c400450341074a00e20104600751001c65002249944502c08076980c010380c0124072000500e4041e0005900c1074401d00c128000c03600c02e03607002c5550120034464103610000340c3d00440d0003e52550005a004106d9100241c502600400800c5480000d00030b40d2001039a60004030342000607071040d107908a000c603010413160160b40c0e1503000c858041070054228285000000c00c1c0044101400c900b500c140a500075900c03403c542c10300050000600b00280e02400440c64021700b00306001c28800d9440303403075480742e09611031001c09100041c058500800103500c0100041c8000d0f95410382e094180e07500c01c0c6480989a2440c010010035109500b81032000b6a00603000f2541e044000d0303042a80c030007410b4400719210369071400015543e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 137881034 1250 137879784 137879813
    0x4050402130305010501061b02010305181c120b0d1709090f0f01061115090c13051909080406120b12060402090c09181807080a1101020c010509010309 66
    0xa403001501006066401c000042100d0056000300000c1c0c0c0e0300c003410f8502c0b810780320303609140d10741c0c0d102c00c1c0d00150300941c0140c1e00301c124a040006629500f4080e03d1038402c500d403050786000090505640c40d207070311100a1504a502d040306228142c000c1003c50000da006105c024042c11900c240284044c0001007030f034000600c000d14102060178041800c1e0040c41080d1200007182c60386800121308180030300e801031b2540c5440301c020011404a03640c43c00c4000c201404d4119607000e00c540010b9955141601c2207540e8000705400101d030304260712640043c0440505800049041c0640b66000c9115501039a00701d91107810710800b684c000110400c020808442ca1076440005004042c0212500080c16442903200382d030080115140d80300f80d00518002c1c2d6001c260b00041904848400710b581030503007600002c3d089120003103a2405840e070342c00c112035600180d030941c3c44241c6801c1484007100050360080d1085c0050b1017002440000246a4420802240d041c103460310200d10401103000c412140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 137882284 1250 137881034 137881039
    0x30804060e030304120306140604050f010201110d0605090117073003050a020606090405071a0c01020433140304140a03053406050c07060501030506010611010515150405 74
    0x680345030514183c041c90903840c3c1d00d000001e103000303004523940c10825a40405200018203c9090a14140030060a59114610b03681155214501042002104070103094054100000424182d082600340302c8040030591151080d00009480d00030810004960001a1503603800041120000d95031550115803600910710039121081c11b003503007807540c088051f1039012460b0b401d68286803503060801400b01c0c2c095602030495000440c0070000b45042410000c40030070405601410085038214007404c9030016481503a40c4003420891100c0e4501028502c00e1803a415620482102c160310300040a06101c0c00810035002d4001012405121442e8600f02600c15240e0031144207121914004000307400083c0c4121803004509284d09207070f080404100747e0203039001c3c00d5070a540c01948917031014240150101542c05420031801d00410228042c0d60f010b5030141c00102400d500d0030b10b00400c0103c200030704540da6407422042c03000400d55540a80c507071600454190201c0f0215010138001ca2181c0c2d4441c9a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 137883534 1250 137882284 137882287
    0x9040c0f060914010509030c01030c02100213031e030e0d0c0321080c0c0a0210140c012306100e0622080c030619050c040e0403030f06051903030804060e03 68
    0x54038550085001050342c10f22a00a01980c07811070041d502801a5104c06506800000c05d20415500c030b070380700a00201580c8101c82000480a10f104126032080303d943d00420203225043c8144030800c18100c460a001003c12050261b85440c02000130f021400c0a134403418a20582c00e050050910340540510b402000034045200007510f40c24030100701181984c00304200c10002140450340b04103039a0401d02d400702914000d000e6030300700220580c0014222052041c42e0000e83c03100900880644012401d120000490b481d42c04000280304010740510716000342007e041101a03100c0441a280103903c500304400140c00c0c8100041da9401010200e580404003502c03100c81d134a0248040030211740a083c06d03981d110744003409068880d03100b01c03a815420a18040c01c824080420f512031580140d6100116041a45405031204554019141500001d44070000400340003541e00c00c2c200140030031a683c640d46207500c040b090340c200c0301f4030015003484110720000781801402d4000342c6c10a0f1400003500d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 137884784 1250 137883534 137883539
    0xc0c02041109041119030f09060e0a050c0a0b0a110a0501050915130b010e0406021909031a041101031107020405041a0f07050412030e0301090305030a20070209040c0f 73
    0x460203504042c010303d00c600c0c03c1c5101c103800303915248201d5501500304840301e5807602c55030005402809440d04500ca009640c5c444090100d04240308402d061021034001d48003607041814028034003012040e5003403040400d141d0405c100c42d5440103e0b1708080d03850810410801e80413800a0800c4d0200001410950030a8100411a04c002c5081070a000c1400703a07442149e1941c1444920300f04441500802d4030180c1c02c014062001d0020040754000e101d00b07000340c80c100ea404c0c5015074650401480d440840e884002c01e204014060031001201603200c10684940e140c6902c0381150480440100ba041c9581e40302c11668a983d05021108140d801401c11b0010b07040502e012090700c100b1701c0720b6000c0300350303001d020425040d100c1c0d501c540212010340d0f900f4181401c014041450080c002c200b2401c3c08201c00740c10b08192400e01401a00c075000352a196240d00c0d101946070280c030310302800503045000409041c9200d6101800b910989074040e19102c0c03030b40e99285000400401160082002c40c0e8402000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 137886034 1250 137884784 137884811
    0x40f0f05030d0c080610140408070303020c0a05061303060c140f090301050c0c0718020d0c030605040608070305100203060f0d0b1005041b0f0912140f0d09090c0c0204 73
    0x1000c0c01160402c08104180700504116030301d520a07103085500400c80c0040c0d80300c1610511701403040342031680d9a0f84c600740d62080880e00c0c2103076562088015030030200c1036850710301d0008000d000500058464516043c1030130b60800e0b00f038080307000041c407140c6d039150b03c10306a921684491001e03041e0300c1011075440c1481c4502ca0910340046100c0c620945c28138001442c401d40310410b5504201c0340c0780c020400142040500038003450050241011070b540fd00520700d0541560040d003500d904280c4000480b541407806000a80354141c0065120754007805041000482c00103603002c090b0b83c92140140c9a440381c10005e541c00039006507140d4021214440f03001407092584406000d1569182003080c5584d03100306110541d4200003070403a511070381c0c880d004442c6000e0a080c7e01049c501d0314188080c070751280e180220114110300705a6000541d15804180343d402000311001c000f0028009011007904410000e001c24098000c108505448100001089002e840440240395000f00140400c207900401c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 137887284 1250 137886034 137886037
    0xc03090a151118091005090a050703020910270803040e0c070206070503040e100302010c140a0501051006030f020909040201050c030d06321f0e030a03110d08090a030305040f0f0503 79
    0x10a98031404004c0c011139012506034280c0070844001034000c0311260340d4105124000c2000400160030316808106600003590b81c005543c90781221502d8500c2c9498001b4100743c2c5000e0690104400101860410b02a42c42d001050b503085138854684c4819598a0b00c10085c8503014004009400c150041440410060040003400036240d0800100005649414400c0b8907051948000380c0854a0041c400e00416145035240315412411803c80da1031b1840c607600d880c21104e0480ea22a61107802403400d00210703a15002c2d2070700420b100b00007507060800a00000e084403a0143c4002c2c14013a00092100c0300030010308c265034074020014010880d6656426540000d4840c9250120420000240000e4020884156400040b60150403001302c0545110f0803010344440354041e1040c8494031203c070307555590400c4410701c014030903070710b01c054006003005a51802203500145001d1064a00400c03a0356007000030006441e907090328010030581c44a090140b4400001d50000d89010320752840901404030000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 137888534 1250 137887284 137887327
    0x114040b030609090a030e0f060910020309040b010503060a0b030402031c030504030f180b0d0e0304081513030804061d060403020a0b06010507020a091a09090d02060c03090a1511 78
    0x190315080344e07601c011000ea250401014020049655040084000c0c100100740b2125410040c03c01c82c036005c905d40001d03100e694840d80c0000180d200041510442c2814001c05402d820700b82001401d40c00d0000006441e071510340034102e0110300100000e0250343d410030041c2c4401d0441025218220180d10300140602400c450640200f114050f00440b0b9034410581107042c10b41454200b584a0709200c021201d0368080c01100500ca0340f42c0040c042e481c0c20a10042004044400c01051410300b440e034049440c1034010b260740907400760210307640046034000c0c120b154015448000010300d00c981d0380400518943e03003607095030580300f10401c200805030000f940741540360140c145484103070f40c2c43c001191175200d42e090003508404400810000c031902d80d004403140381031604030165460743c03180115961500c12103000c100c0e070b0300c4080c07400d405a070140406504140800907880c070310303c2c000440079911555410010400402c4004200c03914005a00002c60071800045050b40c8001c504000026010b646 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 137889784 1250 137888534 137888539
    0x806010206010b04030b180709060609050909031603050a0c0c120611030606161401020a05030103061512020d14070807170a05070e04080d05010b03010320011b020114040b0306 77
    0x1c4001041640358a001d0342c0843e0740c07244220040c0c2d039490600c08007058001801408034842c800c3c000c1448102400340001402141d50f4601940c0d14100400c100c900d00236004a02640080244050a6500188086500c0e805062184d42c82040c01c200710f52982c00d000c00034043d442101004503000f00b00e104403000c62402441c090001c400d4401000c6254030080da45c540d4801010491440768400360851141760601402a0303001d5803040e104280e0aa901040d106400108000010300400280e84606140c10000e810341c800b003282007504018404002ca800039106081c000c03810700805c241c4042c0c08001d11560410b490f00c2e2540c60032031560b222024050601d4821740e07142e13010100000044d90701922604900241489854140c8422002c14064800d5600e8001000004407208260041c00c5c020200091141d68941c13442c103200f40142c0030554030b1100e01045003030b02c0075680e0344494000c0700c0f44012003c4440d00c1c02c05100503603411412110400d40c1c0907000c1800078040b0b5114000d1442102c05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 137891034 1250 137889784 137889793
    0x1090509010e06101202010201150801020c0f1603060f09020d05011b020a08220909030f1e0c0803130212030703090503120712091707080c180f040203150708060102 72
    0x8001040e07441e1502200c41103244c12800d5070421010034004183d01d5864010b000008814502a0341d00022039419081000e040c1c0d00010640c01d10041000800c0301074007043c1c09040040b502d40030115800c40148000307400703644c95121042c80500c46901c9460850f038002c1010508214a00e17025020781712615480c1c007060406048925910700116030480358940c050350381860310400440107441d0300464500401d01600400f00898ad100c0c1d0751080002041c066100c1030200c15080c40010a141100755103a440240ba880c544526242c2001c0b0365020070b0740c080740300d9850796920740004e01c0c0303811211001f03540302003518100c0e5982c1d40040001c1c02e1950107540c50701001901c41307040c150360300c656594401c090030040011001150701c201c032240c0c0e8558640740150000b5074a0f0300c2040c54400d00484001d181c1c1100380c0401c80c200c420807191844d4003090740c00030301643c0601000910b49900030145504450114005401c42d1340a00c40e00464450705418105c150905000080c5000e4080b41d2043c0940318 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 137892284 1250 137891034 137891051
    0xb040506061204060504030903120504081e0a0201110c2211030919061b020319020c0f0405130b180606010c080306010f0e0405010b09090a0b030a0209100e0109050901 73
    0x50690484022456042e4042001d4407169184070060200400503804c100e5260008030005040020b51610401e180ea04c2586507420302038030b01c0c240200c0410034002d401d03030300c86028800d40340400c0b40d04445409003000075500d24541c06460511481c0201c0075841010380314034031400804d0003441071502c544a5010000c0b104490441d4405220035511188103070300c00032130130901c5c40100c040142c010748982004640c41003071489109040d0701e03080d00c10002d070300041059136003003030b04c0018140004003520003400034081c02000308401020003c0c02d28091a1190005100c1d10240f082a0f002145c1c000d01c02c80c2c6602c0c0c00700d4280480c03030f8401005102c038060180855080c2d8842e8409a1400d500495200d141d5118200151010240303250602c0500c1095015000569101c2c481d042c0208040d4455a130b661a40f00704021181d207000340b41e044424984802050a5200040c140303040c02e50688031140152a9200003100340501c0b44d2240e07424600400c00070425888503000107010340740e80b200074000d00c2e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 137893534 1250 137892284 137892289
    0x204061205040506040b090109020603070509130504080d0c0504050310140f0601051803010e2d0307120311040801060f0603141303050f0c070e07020f0304060912080c100b040506 78
    0x114242c0340a4260742c000c002050200383d094205a8000341c5000c000200f49815a000c030f134040e0000c58121022800108100406091810a07442c400410400421042c9820350b29022240600251103d200c0d070f603000311240f001c0c0124102c1f405003c006007100d10041e820b103000c8010f02000754036850f000100501003401d510401c4229401104142c4070b0a0519581c06c41002c00c9840e40c0102c00d03819920340290210102f01030003014414043d103402014400b4210074200340903d00344113000d40960082001101142e1040c51945002c142454042050f46100003601100d00960700b0082055282c00000140c8581c0006060708450039914140050200150801103042080b82c0200c0000c0d8201c81400c0001d20400003440c1030711020f02e40505100040368902d01d0840907801c10341451404c407040c0154550104110016480d2940c006d51402c0e060801c000d001e4446489002104c0b050103c242c0304102d4840c081e200c200915000701d582110345155400f0140c071014844c20b014614003004a507150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 137894784 1250 137893534 137893541
    0xb0409080918151504051306050405130503070206130e130b0609011419170f0c060307020d0f0903060c0203120c21130b0c03010e0606030601140d06080f0102040612 72
    0x9040345039060343c2e50203030941404010441d03002c2146078090308201c003091a41d5140320600d0901d044d8040000e0060901d001d010403100051f050802c0d642002102c0000580d000085400c02d5034142c4a2544a80412584910042280d00000156103903103040202c1c144144202c031044030301a4440018644a410501080f410280100d0680650b52640941242411003500098141414801080a07030b100e6021401002c43c80242c0203d810440380010f9000f4100030030342803c242111080c5c42c605040d00b001c2c1da03950700a1214414003801d0700b002c40065025245d0a230046402c40c5080c4510001110025120792000b01d07406900c4e280c0c04046204050011309030b9900041121000c43c85810000311300050120081c210b010040c0c601c00c0d050700169503017140c0f034000d454081800d626941000180d51417894010300481c00303490284100702031a80d200c0301c40b040010041c10b1070b69880040c410800060a01908400282c1c4596a001c2d00c07c824154010401c070f900c540c1d105207440e05200c804100b42e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 137896034 1250 137894784 137894791
    0xc05070b0403050f0613032c030f0a0201090807050105041205011107060903080708040b181908031902030408070209060d0606080d021006140919090303020a12151401030b0409080918 80
    0x41c03c400c45003903030740000034403141050240f2a070708e83c001c0350100000c3e240140000c0c0340c84040d04010549809c55030445070110103080c41002400080d0b051800081081c000c610403416008038028403034091040c04e6100c00c0302e0003c01400c0c5a603405203030900c0c4000d014803c10441c0021103500008031250b124851050082e54050a03503007140e00e4400c000241c2c0c0190030f0b40030700d81c0c1c000d803a8400e482a80c03100084403c0384c441c01a49482e80f030407480d02410488115070007400e0706d004004000005228401316408a40d044604010720781b1000086880e0a0b1300c121300170002440c1c00d401141501c800290303c0c0e00c4d035405500322146045901014010345205c0d2091420840500710204254a050040c0c40e40c044200d2003502500c00c52180850280c0c4d0440350103402080c0d0001d00f0340107451380282282000c0c1c0d11010207122448100e2292810781203144514402d1004803105604160b1280c0c025541014005006103c03000e1241040c00082d400b07100080e2140c9140c5c080340d4000400802920f11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 137897284 1250 137896034 137896037
    0x20405090a09030f0518090a0e06011e060c0c090207060e010c020a0203061302060f030a060801110a0c0b060103060503070306060e09010c0807180905010603020306031b0a060c05070b0403050f061303 87
    0x9113034080c00c0081c1c0d0302c0d410490344400c608218801e11601911043e00d47c500c00e84c182d040102c0c05400e0543d403a03081084c1078001a912100710f40d8000410789280c2480400c50309140381c004070310702e45420701c04c06d0f03403041c6e1b00010501c41c00003503404140304150b0002c031900d203200c5000300402e40d82c1010603652183c0a41c0001c0d010741242000035a00451400c0f600c10a9001504051030840040244403a903401102c0403030a465a580d4240801c030070900c00c1c04201442c1c845500d28081e12110060004070040d24010071810150000809a91013604560001d02c0e020701269410b41e1a89400000b40c01c50340100480c085c9a4400a42440030500654030586c4040d1242e1185403510901102c03191020480248094428940042c022a051240900030701c081d640c0140c607070034a2002c02d828001c0c1d9440004e0f21151640c00c000166071010100750888509040c0140b41c0d40b4170303243c02c500b040038982c041ca41d503040200b0f00009000c004110235943e400000d094035141d584118058144101001e0043c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 137898534 1250 137897284 137897297
    0x50a020906010e1e1f0908070b030402090f1305120a020111120708040311030d0e1501030819170c03190504030203030118090606080c040f020301150e01050c0709020405090a0903 78
    0x1158050342601654144d10060312000240f070504040603c66542000780300700003035584008200001d41404804042c000c110700e4640745003080c6d0000703a103055019050200110394000415050340340f00a19aa00c60703404019075080e10041c041d0514a074002d150110095401e101740c580035040c4440c01c032641c0482c03203800c075881074961140464010400800890078000095180a1524000c0000d84824881c4100120780e03000b42c400703034604002c04408001060f0040000500000d000d40003581e5007100134409900ca00c0c0d89810044608600010050800b08001410700501c414030030300541c400c1e10411791100707444142c2d031040c1e000c07138404440c00340040e04148014440c580c10a0440c0030000041880880c42485c0c41c2c40d0f04044481d5a4001c1030103070301010f2283c54608180c028503200c815492001c50039507140c0f24248404220071920207003048454105039603583e0141e0182c55455007240d0803101080d0f120380454000358003600070713507200c0c07c15400003400800e49406614034081c4e140d640c58 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 137899784 1250 137898534 137898559
    0x9050a03021c170d0f11030403080412021e0601050f0315060103020a050702040218120f06060d0f1a0103020310020a0f0c020301020f0d02070b09010608070618090603050a020906010e 80
    0x60b5250181400115010b65128100c48004200031003e849070805060b40051000d8070f0607030440448054446d61040b0440a004100119400192059200707030072411f050403500c070b000c0c4e04900f000c0c3d10014070410541d20340500d00300c03000002109410f903401956032b22042c08030072080550f030b0150200c01701c01c1042c6800018007654407035005423003c1c40c3d5a040c00d6050039210b600080a90f0000724135041282c0000240d00100c0c50400b082d9058082d00401518403075107152a07041d103070040100301501402100d140340040064400712605101c1d0056030156418178000c03400001144c080c802a44a841108030002510700b981c030884007802d1040c2c85007940304a88080aa4420018800903685035500340100940d40626500a11000f009070070f005945001c140703490f180858000c0c1030b8490344d130301d004420300240100290170003e0300c211342060b5020540f201012a09003981e03406c10721040703007403030b800004100b000503201500b01d1003194400a9a610900111240c4520803922070740040c01c0d07080c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 137901034 1250 137899784 137899819
    0x3030a030c03020d020705031317030702061806030f07110313050108090f01051f0902071a041b0303053117010209031b180403120b0409020904080a09050a0302 70
    0x51450748806003005400c010004841508980000c4001e0301c8940000548001c0070189040c840090085046408220519181440d039240195603000740200130010750741580d4484024080340780f080c0101002e079a8585452598500c8070f05071100780100b010720200044000002c0706032044043e81031031360900c051900f0f004441450002e0200c4005001d00d03228110307462004c0c05407034881c130404c9070314100704044014021410009540102807803403051101b200010045140e081201c4030100c2564007540740c60806045986120a40b46d031f507046070340c1c030000405030400050b2101490542c0c0e40c0e0030840c00080b4006401c40015000c0750700f45558007050100b89450142000c2d41c03545000018107007120640031070725241c1d0814001c8041d0b558410040c00384e141c0741703190b003500b0f40b8040342c4008a0300303095401801900d48048801e0b12243c8400b2032100c1500c0e0365121880f5240c0052060855052500305540d85510010000c40042d54070903000c5568101040e100003140da002d011071480082c80d034076 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 137902284 1250 137901034 137901041
    0x80c0f09011b050105040606050109050a05030a06050415020a02010506040b01050a14130305121e12061c05101b170f1b03071d180a0e0c0d0320060603030a03 69
    0x45071800301c08030b0440c040c04228240300740c1d840b5130311540000450a00f00070015100ca041c80d07120074070481106106020540300031408001099120502080320388452070243c0340d2604006203e0b40051020440801c085d0741500200d004d440282d4041000302c2501004403507510507040c0e0803022645107403c805810300d514005042681025000c441c5140d101c0d981c050178450a000400000030780802c82003a5888142910016003254280c4146810003842001c42462401003c4a110b9000d10f55210108004800255100355018041e140c815104601c034600602401040c00591015200449255405208206090f4010210401481d80c5109415807030010081c00c41c240d0503511032494400800c000050750154080e610b80d4131b6070a100000303000d007451122210071b11400c16101d440103001000501107401101406020440400a6201a240c030418280071600700001050000625511a00d5000798103e400440f01100c041c0d03040c10351766004180c03507056158008000012102c2e00036070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 137903534 1250 137902284 137902307
    0x40209130503130914070206010305070b0307120c02030d1506021222030804080609030313030f030b060a050414091e1e040c03050c01030e1207020307050a030c06080c0f0901 76
    0x70440345006040020b14000002c039910140405460b075240c06242c440d0050a954030100d5031004115a48c51074890940d100307601e00c00d44484100010100314824403540e2040c04940c40300c00240616800482c0003596580702401c7d00070440d15110728801200c030402c1041080362130540c01000145101300000e0700590003001081c80529a408041981040104c00d0704000c50040300035a885502c1c00140a00742034000b054480a504100304000030614040e1004502030f070949010b813079025484d0020b034010400e0b000520750044011030030010035940040100103440404d20500803103151542444080001900d40c0441d9500d000c2015810752003040300150f001a1490200301d0001c0e91080079a07265000703980541d0362070340000e418000d01c9403c01c007100c06c0e90f00a09e030410402c56041d0382c42d41c9854003c0001c00c8040000901d200079541c080000202400004010900c1075646e4a000101d0340d290b4468400810360002c000780d090940c02c01654019455890450318010061f00111503104135030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 137904784 1250 137903534 137903543
    0xe01090f0c0806060f120723040e040f0204090c0b090a0b0c030a0c020a09230f0f18010e01020313050c01180308091807030c03050115020a060b1c0606050405060904020913 75
    0x148646d41c1c25980100300b05020306065142c0041c40c2d00420f1843c082015030744405400c0c840c04010411860950030380643c1c7c4950000c810300450b402030720020740a040e0300d001c041d00101000301c02052900783e8900800e95420110303181c400c195501c1224402074000d501814034a42c205214590420780100c9203100854401400c002c103058a8442c0d103401c4400307045420300c4c80d0400d156500e940c210985017054100c0840036800150786003244011244c5240140b113070b01d00303120181c00d503940814250050481120104000d5440e03151148520300c0280768004103417005c0c814414119000d501400940e0f82140f101c804041589003192100c3c1d102d603002003103580e04072890303c81d0050511050414240034102c50750700452113011015004090300d4061b00003076980010080035080b526000110903400b141d1105000c1510702001e000101d2842440381c6035820b41540c1002c030700800c4000d40c490810b4030001c80d810403107526180b092261b800000c480080d00105082c2c08074050215410041c11034501c607 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 137906034 1250 137904784 137904787
    0xb090c220504062d1d03070210020708070303020f0d080105030715020a0f060e0607050901020c0909071508011502010501031a10030816031b020a0522060e01090f0c0806060f 76
    0x2d001e02a5550340007401c00807962480c031500c11305483c04034050721800800e010030307015044095400141c1c4910602c80000e104804440d4132540c518003e028030002801c5c080240c4180c60f41d80d040183d1546660840440c1c180aa0200d4034200ca005110017410380368003030014022035040c03020342403000080740301c01d8081d8890075001c00300140a0403c090105071160402040b81120008502d1a00c00e01034210b4017807100038480703602181d0f40000c504a0140c000c4814580d2529512038082c10701d0100d42181c01801012501c40345100c2d04400f800e8101c58042c60701c091000303010b080c1242294400c0c08020301450420301c0d0700c03000501800c4404d8001c20000c92000800340e40b80d031031941546c40404042c4528140450714018160803588102e900c191b00081079090040c281c0c00a0420174180c0a00d034412030103030707c11030844024080c9004820100700010088103031280c01074006181c0c00d102d104003a50500b03102d00d04055042c041d00d00c1c00012a00d5130076903a1140d60400a40b40c000d25803e0407901e10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 137907284 1250 137906034 137906051
    0x2304030306080d2d21150b0702010908010c05041502160906170604150e030c0303070201050604050c0909010b030a2a03140408030a09030e0301090b090c22050406 71
    0x1024000c2042c801c6041d104c4009500c46440d40d40700101840240310f03a40b0500440c501c00351a0070204043c49044c1c141e00c04a01030115414550017441c01c10110312240ca51150042090101c460080c44a98001d8035030114890b92440c00e50300341c1c2c0c3c7c0d04034407400080d010b1000304860030112a5041810005005070f50020008001500070340301194024175001e625803c2c2080903450500b402003000c400c2c8005015940780545079101d107042d0041100003019502c4a2508030150144142c891000c84803098940d40c1c204010000c0c0604015a10300344241d140074045440007103502c040720005100070b0903090403a840c100303a0f1a41d076000144220201740e295220381c01015030a5100b144105111a90600600c007429801800c65540c096031100d03080f601c009008c08516101c0c00d69900040e0440042000403c130316048a9007100b00c0352030340e00f541c00d01001d1010030810f5004144aa00000300300c03242c050320603040212507541510b1419054030002c3e02200705440c0c64101942c002c8c0107800104082c01d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 137908534 1250 137907284 137907299
    0xa060504090b070908120915040e04030c0b0601030501210219030503071202030c0a0602090402040e16020d030203070504120203030903030f0a0e030a020616030c0b01060201020403050c042304030306 87
    0x1510010125440c400000c10040c42d04e0b00000f002014143d000000d2180c14103240a180300c920498118a00c1130121154078041c44000c04101c401174880a010860242400c0c6002b07480c001010a0440d41003100c80001121540300c5d03c149812904101c500d014514210390b100051140240e03810398010f003c150401e00c00c0c50968010500851082000f140c0e120041d062080c10a9480041c49045410030400600e6241d0005903c1100740e0b000080103945040b4a40001c00901c5950300180000600c6801c0010f0326000c0320440c9203114050b0282c6031420040c00d0118100e1108403006004101c06000034440110346c1c201c0c45903268409800ca901e48402400068075581054403815140d200008140281650020885039840c109070000e1035a400180c0c0019001d0041e0100c1300b60650007021803006051260000b80030715900301c40441010358481400a010758481d01055070030f84640d0b989a400c609041c4900303070000c0202003c03104d0220030120015107049000d4003d80405032600000328080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 137909784 1250 137908534 137908541
    0x708040f06061202040f110f0309030d150905060a0513020a09030b0a05060a080708030a0e01020a02120c150705070312020f010c020115080f060106230c0c0901080601060203070b0a060504 82
    0x10208031041d0089a81e01d8410042501c0481b00d4006195090a200003030403407070f07201600c0f0107418514015849a07118000949035004441c0000380781410300b051b204003203480303032007500586418000600881e9909000d0150030304041c8656030304140000940505051580d0290903d100d4520f0312130b9080d5905e4407001c01d000420f50340d007a4400d6494091000c18a8000710300d2000b01103c0b070140030060315000c212604d074001c10084000f070150040c45032103540e1081c008210100c0d0b0052518002c50322034a40b05a40f00040200903000700040e011035002c2c0380000e41030740c01030780d440001821014210b40d03913184c40d0f4035000240c0c01503216006030055400c80a01681e11036860345d43c0009900814001d12198403800c0c1d502c19220380e003114980d4180b0001c04141a41503400b1801e2032800089082c0344401a0b041024a40c255a2004203081d41030a402141250042008489800403a601d8101c0c2903140c5c4000c1c46402e000d0b0b803041207202d0015100504850b48070121100000d050307540c0b032011406a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 137911034 1250 137909784 137909789
    0x20c01090c03080d060e070503151f08010f0501020c0d060e030702061207080c0309030901180f0905180c0307060305061f030b030f0d0f0e030709020f0406090e07080708040f0606 78
    0x482e404121458030000c4c5100b208010040d034204a803250038207074030240041c8800f40180c4120201102040c1840d06c9071980144542000002400b0200d141880146850400e0083d10404900100c000076036601c002207134003503504010303c0511844000c0d52210010300000010308a60300050101d0740169640c00042c00b01c00580b0110781484d4a0140d20007040074000a22a24201c041401800300e20100001600c18446c82802c8c45d48100504030b8140020000503802050b0300e005501004c52280c41a40120f80aa084c8001040c10980b5644000b074035048d8290600f5010741c0241403c2108c6482a0005504040003501d080011305035003202d60f400d02e81c020610004241c84e0018075659060410207080702a001c8070280100c0410703208001d0400e03650f00c009070304010100324284140e54040c40400010481603e04558030840120110043c2e00180b0407070000c1080f00b8400a22882a5030304e00d441100a50740711101650342c2a015903480c0409007042d40d0105101c0d242100040c01881602d01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 137912284 1250 137911034 137911043
    0xe01121407020313050d030801050d141209011d15220f0e240f12030309060106091a0a050a02031b100609090b01050f03031e03070801141003020c01090c03 68
    0x15240145100500100896172040d8010401022030b031000c280c0c40144141982c03c2101c0901e03909140d418140454011103051613642c0c0180c00c0840591604800244011107081e00c2e640401e1f038103c259082d4070b01c404031007650010030004d01c182e14840003200070141115001414400041c444100d825982a6604400a981c001002c2849010b01040e4025400381c51002a40d01c14400800840d122650800c9864040d84a1095403401070b6610510b0315240c2504034100c2e43c0700d1401901003603580c80c00303105e4040442e17110400880c81c6040302c42e05103440c60540e1200c0d40342c00c040309422110355000d2400b4000b103010600c004142c0004c0100b8120041c041d900003040c41c44010b040200c111340c000c3e03010a81c010301d02211000019148603007541181c1040f120b60080340c0c28800404d08522070310300c80940d022030b08602c07003103a09507110245005200958440744035a03203503096446a120140c4a06500090395840000dd0600c00e400501b0100085000410180c0b00da6590454803605030f0402c0340c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 137913534 1250 137912284 137912287
    0x4051f090c080105060315100c0615030308061005070b22030906030501090c0909110408060109020403031205061804021318051005040c061d060c0f0105070e010e011214070203 77
    0x41c1c415900014907409071004030340003031031820b2110304002d0b0200440b0049018007261240f0b0807031036005416402c1c1d543c0d003210003801a0440c1c07000418001000c1d010417000700b6900008a1614181a01030310008002600d41c1807400d55107031200310416000601d100c15a400c40403588203400492440600300c84c0c8a511100000b0b42030400150690380d05070866201d10340303040030b81000580d000f60300790111840030300c0005002c00c12003030501d442d01c2581c00680b583d205001c000107824805500a100306e80c0607a0340c420200c4c0c0e0914071032080e02e2051b50040c0c1d01c42413028168545040c010011501701d072006240c0c902d068a004044401e0700c8152040b00760804a0801c1d80e420f1010600114100c4000034101708510b103025550648251134901424040104080010b0004412400300f00d1810100030b2000351501d95248445a0310078407070300c80c00785550800001c10b0013140601050300c0c4400d4140c56070103000000b1001100d600d0031003400c2d681d003036448108000a182e8404403090150210b6409035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 137914784 1250 137913534 137913551
    0x4050d050f01060509060d080904020f04030312050a140103061d0609210705070b0a020102070c03060c110c0109050103022104380606070f0c0f08071202090604051f09 73
    0x9401c5400a90044e405120010200a5280d4071030031000102648204016214942440441e009005000d0034180c1164005004824581c0080c04a10f148849107014012581c9e4065860207407000909503546c00c041c0c1da80148002281c0e41c0141d04003101c5204244640004c0804882c44c180c41500c44140340e408c10203a4207552000c1400400f9440004440e95241c203446035034183e42e07482d40f882001d2212002103041c3c61864800c0d0129407070290820f560940b2240c4904054005040229400c00801c2e068042c2c0301e0312038004070364110f02c20740507180c1c202e210f8270b40030040d4080c0d88110081000c50070300d8810f85045080041c200b0707008500405002c4020007044c3d280b00410320800c0940b103808148483c03014102d00c103841645501503002d031481a2900924640f05101c1c2148440041c910305070002c0c0030403d10380e0f8003caa0122103030442102c0f083d59680c00c040c039000842600c082d4100d184940001c02c10b080580003650054030015848919481d260f484038000d40ca80d40000c0001e64031110013 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 137916034 1250 137914784 137914813
    0x41a010908010b0603130f060203040813140d0b070302090a08010501031209030c06121131081e03120c210603030304060c0e04150305070807060804110604050d05 71
    0x12000c1d100580c0208010507190000828600000b1300d6110a250715100090400c00c80303420b10140194085801e54903401d191400100d00d800c4000d05100515101400180b0081c0d80c1029403c5000c02804c0602c014502d42c44140b21008010105824103808206540090321031010241c0200001000000d05505510300290b007902500100300c1003000c3c8550603c042198204905c003215100d00744401c0e20450303d05204050010700e0455100c01e100869424002c0b4035941c1e00f103091700800d66040d401c604906104480000c0c0710301524405902c0030302d020b1007402510265159001d07405003268180b29041402c0141001c00725210041140c3c04514400ca10080020404841d82c0c80d4055041c285009404207503203010051014150548420400c245a070003034504607480b07680504244503032858100b00c0c4107010841c2c032080f1782030b105680340068245004502e110544503ea66001d4071501c4946880780101580b401041d0b01400c10000040d4983d07072080003410b55072085001e0024119008134 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 137917284 1250 137916034 137916047
    0xb0108120301030c14010c1a07090801020a050904020903030405030d120f110f090a0504110a020f070b07121404030b06030c150906180a06050705100c0c08090102030702041a01 77
    0x14103540c00c6003803005000050541010340c0c10707079425032000a580b0710408012070b101c046c11000680341014010240340011030850046210720b0071910f840c0c500a40e903515035400c0340309014610300050800c2c400c42125141c550000d040d80f000003400ca81c1041d896a001a0604032075035043e90200e04041d01e060b910303200c1c43c01101c81014049200300a00b0124125209042c840c4401402030320030700140d0810356075100708040b40a0b04016000308440c071010316000302c1c1540002001c0c009842440301079071003948002211002ea4403e60380c52400c00c7c0751695581c4101c84404a80003c1c4401c0b0745104416a11460240c402107003d081019400e003403d4040c141403040d4201018002d481c4131241c80c0708155180200e400c101c4054035030b1542c40c000c80300d025540e4403807031031100c2d8807810036070f00050500d074840050101140268161059a040842541c040f9180e41c4542c0c0045241f100e24035001c03410840c040c01440344107006903450020540c1c00038040fa400245080d504441d104003011003542d1112 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 137918534 1250 137917284 137917303
    0x9050f0702010b010804030e01110d0305070219020f01260702030702011d010212030a090213090303051303020d030c05040801020324060403020d06090203030412060b100e010f030f0209030a0b0108 86
    0xf0070580980400080c20440010009800d12034000c00031030aa921400d00c6403043c1620324281d82101c440d00718000e010346420b03602c10005216200c000000508071f40104e550041d0300034000038003c4e24880056842e0b49840c004c03518201000c40c030760420800c1800c030b45c61203070145a01460383c074441480090148000c2c85030340b0900c1c2080740c0c06008580d0b0005810340110503d2419a07440ea0343c2c01d04800301620410300025045884051400341641d281d401c90350116109450030300184d980d0941c81103a203000c1002c0500143c0c0140500032696000f176004503901d05280c601546020303160702100703099a10903940083c0c40702090f003400c0c6070340c04c0040c040c00001e1012689a460540341d5000269441c94000c0c025118a0b1348059410840d50108100c030000e00e50100400c104c2c150310b04290004100b591841801807002e68441d402592068081800800c4140c4030303503549201d4500120000c0c1800303038203142e4465007045140c1a5550800840c013605106142e43e1000f503041040813410a400003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 137919784 1250 137918534 137918537
    0x150b12060f0613030c0f1d16021c0503040b15060409110c01050f090c040c050d09051204180e030a051b03070c09061d04051c09080709050f07 62
    0x510452102010014850390040e80854420318000300305800290288522041c0282c100b103c0c4100000300200068141c04840c51001d40000705540c8041c0e2086961070315626115640600340062140358400440c082611030500c12508070004844206840c00702c0c041d00400031a01c040300b04020130242e0100c072030740b03d40680d541e10080407004021501c60301841c00754101d03103a1280030002c0390440403400e0301c0e04908481d00912103420403032401c2c140d00d031058402650711300540c001e0085a0426000d142c0d01404d00b66a1a894542c2102c005001400c00060403240703800b51340b0103c03a0300141880500003410906076102822840190b503141107070301c0c8010200c0c483e0024884480000c0e0040180d0301d044080911041110241c0c03402503040d03106a020080ca4600c4510012602c2c034415401036040e503c0c807881d03401c01c0c0002c900e85588480c908840c001c0980d40b001741c81490fa4076000307501400035100390a202c807140380c4507801a410035107035421030882140d603101040350108252403943e4205106 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 137921034 1250 137919784 137919787
    0xc0a03020109060e150328050f060906040f090303020903010c08040b0106050309070e01090207110d0b0606161403070203010c090e01032d030206060a090e0304030b060f09040303150b 80
    0x21940064011040741c0304510030f001c4034007090402d1781c50301781a0103002ca00c1c0d40166680c034600502c602140396486411400703502a000d1580c001402103101d55405402c0e041c0123080e07241c0c1d80208100c0528070082c5002c3d003003611900e0799000c5030300600404000a129880c096101e000c41000e140c21512103840150400c116141800301160700d4189041c151251440e2043d9650390301d42c3ca06107801070550020502c0d24181000040030b08060380a4000c4030f20030714101d04080b40031810851010104200a0a81481d07440451b481d445d0841c010824480440c01034245d0a0140c0c484120301304064815480d10b810015420086140a00c14010b09184c1810305022660802104520403801408007e01c0250220070b200e9a102c5000e80100d4007400b21011006000071a10b80213455200581e03180740110001400400c03400d141d070191101111007000150300745072550f181c9944401e00544599000402c5500f04601629640e811f1403203039000751004960042c51020b600080111a4041d0234030010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 137922284 1250 137921034 137921039
    0x20613020a0b0705061b07110d030203041a04060914011d040e0109030e0907050f070f0302150c0705070b04080a0b0a02090d12090509072007080d0e0a050409020607030503070e060f0c0c0a 82
    0x110740c140380b080800c060310a080c00e912270b45010380c654419038020814003190903c1c001440c2030641c00a001f0b1f20010303610324245070350380c554074001c151407a107081c1e002c41c03503a410010f0204155000018000300083c07010409400d400300040c01c5034079072107059000a140c44494050b90600229480e0011079520301140b03089140070545500d8025030340000c010007a500c99006c20315100300421580c42d10800441211414043c21461840d8021641103c0d01d006030040020984001000e9400f11144a805800d81e0040c583d22050006002040c04990301e03030034052030700e080e01d610390800c51840c4030300c0001182010682e070240510b4141d600052141c8841003c00c2013a56000c1416200f0183c06451100340300d05c0c1c0c4e40302c81d060100a0b00160694486c51612946241d480490b01c3c1002c08280c40000c0d0135510b440c180000d460840202a41240082200000107803065009503401102d615102381d5a104410000c0e000354080350300140403140219003103000420500810303450b900116018121240b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 137923534 1250 137922284 137922293
    0x12060106050405190b040905060906150a030f150f050a0812160302150a02030718030c0b09150f040f0501050702220b0a080a03020c01020706020613020a0b0705061b07 73
    0x10882c0211401820144c103c0500918540c1c0080c0c044c08089480d55203c1e500d8803d800d00130034040300d00d41e2103903580d81c01044403402c140c0012031540c0b55500d511494200c440c0d405501820b0f0b9681c03220700456441014200e00460700d0201809040c0323517080c02c01414a00800c00c035200c48190000c00490300040252200d44142c54110b491049141d0510890519541401e0341408001314000396659600700c01c014108000d54021072241216485000344a0079010344d60482a01602000380085603a0704140418034800000e040c1d031000007441000401c60940e003100381c0340c001080d050300710800803e05021103544814000c020306020320300a820002e481e00000d0114001000c54403034003944c401e1412102d2a0303600098107031000901130b001c080d55030b5000c0f03030390700c0400300002e40050003000b0b6440f40a41c03011415400f02d5a441d0b0080c0300c25111040f011910310782412040f41d101140b90030004003802244060081c0d607010740003901807072038081441c0d500d056000c07030750b203a07140c0e0308010070030008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 137924784 1250 137923534 137923537
    0x302011707020d03090305091c05010e030a0c060b0418050102070510091a0603030918100504110304030e030a0204060603020a020607020c1302130906150311090d1203110a0203091206010605 83
    0x2003c142c0703400300c0c4d204918242a0364a10600410b10b4100301c525480906010b050005100d00a00c5500204810a01d020041d40c4901a45140c02c00142c000060800400e40750307001600c0c0c05100904c00501c1d02c9540840c266041000001162680d4004c0750540078040107102105103510705107810711040445544a04c21048040707510300c44192410045901f075101001942c0840b0400381070030040306a050207503851000c0840c1c3d48800f49030440008962030506001c0c400f5820550302c002420741e01d6540d01a241c0b00080c0905640610034501142e001d6030b2540039140040401d62001a0b03a5407042134024200080244800c05552002c542c1225079220500301c2e2550300c00c0d031746006803100071b084500200d18040340d0190000500b801c10111303070310700c5020b034118819045071800c1050340071900d10400d49000d4243d04a80c8981c13801c1d07403900811000c030444c00090f003451800007115034200529044503007100902e100140d00101d5070112074101121407070714041c040e0b030083c2078a615046009140307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 137926034 1250 137924784 137924803
    0x340f060806120c041509050c09010c0f05030d02130e060901060203030a1505100305071b20010318030e180c030a020f070b0f040606090c02070303050c0c0306010f030201170702 77
    0x503500c01254040703440c2d014008a038103880f00400a1154411110704e60703200c40c4c00381c0102c024032032a140108070f503480f2410071160342040684903d0305000c0c2e82e48401c02a43c0c4119410344480c0820040303404010040d1006040a028156503440100c2c2044941000e4800042110380948908001803100c25000401e4a60044500700c0c04200c036100303006014620041d42c2c5c070058200034449441aa820b07019002a845240e041d540e110545984030781200085d0b810400280c10389140c0b0b04d400c6140380400034200d61350300c1c06040104220002884008a00a160000781c0000e0001b6071142100d00e08903501c043d0100640143e01c103a4200f2101d40c0c0540d01c0050010680f0550005031444013081400681e01d41e5a00030380d008855152245545050300c0007102c0440e1410b24062300805c1c162168400c0c00c83d607071002c1e0700401d862400d5541c25109a44000c1a92080c1d200d0859040c046036010000c49002e8040801818041d43c5188005841036003010795011030324083c817003080450380d0b000815100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 137927284 1250 137926034 137926039
    0x9050606060901020f16170607050906070305071a010306110c0303060d02010c020d0804080105011703121005030d0e120d1b060f02030106081b091809340f060806 71
    0x1901d058040040c2c2c5001c2205e000fa19003030040308100340103221b40b00194811518401d0a01d0f42c00c2007a8504148c0f2010100c8803840444c40910803010103007450006020320510900f4400d140c0b0b1115240ca43c05111614260142c8a0200c001401005500e010b00702c0c095948946880c104201c041e60241c4038040241458000c0c07001c0440101075a00c21180c203140550094490400e00b0014288017a0950203805440742075070a0a00000744178000305448143c06240368050350400506c141d14a0140c2e1018000000101e00010041410795050280142d82d072046d03194020011002c07400c2c844021800c0205000b65000902c4140750250040d0303540422140c03080107580000240c1c40d00f0001403484c803245000b5030f48084004120507030080350540c0101894408480f031400a0101403886210b800c80c40c40c0c2004254050001829206500341e0b000000b00003501c5c401203a04078915000c905000c24801030700030300d030001401922000700b1440a07040804040411504000c005009400041c21450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 137928534 1250 137927284 137927287
    0x601140705240412020706050a18090f0213050603010f0e0405030d0218031009150911030a12080c07030903020d020f0d2405010503061f0e01060519030905060606 71
    0x1003080501c00040b502d481ca01280e1403032444201400030386082142c040304d652245088500549000041000445846944a924082c00090120717080911211001c91440780312a0104880c421409404040c80e40c08200580ba000301d5603078480041d000e50f0029018000c00c200500681c0c0341c1d910740100b517981f0b400300640f1a44451405900d1032295050003090a031000c0b4410500d140d9201060310b400d036080b411a0306d901c05241c603820072562112001801182d100c0320307604448440d43c00441d200d0703005502d52104146c100c0003080c202031410104440703201c1c613008048030f0144c00510441d00202c6001ca0382e81094071903a0301420380c4c0004d010203840f0f42c80d80f80010302195600b101e0050880b00c09000c8109003001440c2c214080c680a22404803441c0c0c4907150104490782c0c82c03040f28102c54000b00100f02544411a512150200005000e044c0c21618040440c2218616203c54000c051564440d0703511040600c800e614003141901c400101403c0c0422200412800110030f900a101203c905 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 137929784 1250 137928534 137928547
    0x2040b0d090f170a0906020c01080610050c0a0614010f0f1412100c0210290102030c0d020c03070b09030d140c0a050a0b010515070b10171c08060114 65
    0x11401c69036088002088101c1855002c00214001c001504640c13515440700c0c0c803070a0325500c0903a00c0d2921010003d0020307002000184441c0361a6588003071070f804a0521510300440341007014100808000d00342c0701c03d51506909a170f06446170a0150041c820b00300e4000946007051342155144c0d503180700701c1c03002d80142d00f881041c1d40e94084866148800490840d1200d01c0d000021030041c0070b1080b0980054010020035030714008a6004154041c42d07064a018103d21120340c2c0070030710000a400d541d0440c03000744042900110200090b07980c0d906240c00401011251178101850a051a04984c100d080203029652058500041b000728020a500700342c610316044944200c01400f40c005612114864101110f01740310000c240910014003903450b00606a0300d40c01440a80c0140d40807d007890001000f8550125180b00b48084d000b0f04190710032100d482c1d035500382001d50605003510542d40d0300104500403419040d01034008000e010745c1401e404503e0000d0000c1c1003003030745001c0160030a0001031003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 137931034 1250 137929784 137929793
    0x6012c220b1002071211061308011b11031e0d050916061805060d0f0501060c061d06060121050f0901050f010503030301060507050111040e04050714030604020f01031b0503070306060302040b0d09 85
    0x144c03280d120340508c0e201109651503152a020300f0301e652440261554003810212410b101d00a80385030440142e004500d40360840c0141d5210b61507840301c1e100744520a200b24000c4009600556010b00c4031400140580900201c00c210081107990062040c00001c0704ad1040d101514040001150f104540f07294489501000580207024a8024400c1403449c24001242143c1c0201041074444d0096000f000340301a1040b9509200c140c03400100182c1c0d00800001c2c0c4158460b2914660b80021041249024217840c050801034881c2a525442448075080401c21800e50074400c1c0d07035004504405d5240d9551403c0c0120340c03203104c180103c2e01080b4000480d181440025041010701c0030180303903071300c0e5540ea0b11210740c0fa20308800d5800b25200d00503d103000401d02c3d01c0507075a00e42c1d91001800b03400c80e6240d582c2046114015420014149a282c0783c4128003042d1000c00b0350403244042e01c0c0c15a0346e00e041e05004040b21401e8000c8000d0505c180418403007511210245c0725089200f400000e88440345041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 137932284 1250 137931034 137931037
    0xa082b152112020616230901050d02040902040312030902010c17040e01080309150309101a0d0b06091303050d0c03020f040303051206012c220b100207121106 69
    0x5001d4000600456612803a9a0000c0c440d1721038505003242d0080f000d4400400c407484103100d02c865200c805000c9403071011158807802030608450505100d482d0400200d500d00590700141c0c02848a03940c08101042401148070311204110100e24042050203016400a001d840d403040d800303403940102040b00401c1810100032a00a0084030850612569485442680e01c1c0d0000500c140101101c4460541640b0a84c040d640074011840140251504400d052002046201c0a01e41c290b5113281082c0340e991150002d031640d1034001c1803000c21601e088024041003c8014202040c3c242c0300804000100c0c0c1e01c01d09036404050800e00200d90349803150380441c042d01070308859503803003040040d00104054102c0000e160b46144100c1507181c1c4e91741c10006403a4031150360030220741074442c0e560120003006d01c103202200160340103249811031490020891034003500359501101c4640e03644644032a6180c01c2c010121543c06031302c0145030703950900803420a0b039a08843c000340300c10b6481050b40d015544510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 137933534 1250 137932284 137932349
    0xb01030f06030b060310050103050d0c111c020f0303040b0a1407050712030314011a070201031506051309180308180607090306050906060f120a082b15 66
    0x240501c8529107900303050300600000d0300c80d0344c0f280c4a08500114a81954080c980c100c9030000050124070f29801c00a070780c00c620742e14085a001da444503502c80300d60b8941c0840c0c50b10180031440f150344446c1c40d10501c015030401900c3c980c4264000d00040020842060407039048581514000b426003611040481c9140245400141315001e14540841d070400d08034030055456019035800c0c01039041e44080080b04060a01807440e82403080d4100c205100c202000504100d8410b24001460010344280326507200210381100c1c0c00038500060003001900ca626108000d0300f00d080e0104001d000030941c1400322000003d0060901c454030002580c08916400c4000c44c04000174103440c49440c201600802e8000b01d800111035161400d40420303204003001807618400c11000d015a04030082c65010041c5400e114203000f2501c5c4035080b18107000511a001803c0700c040a0020714450035001c1d036004182c500080c07a82003441d407800a641050800c440740010843e1902141e2240c1d0000700c008014020240c50b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 137934784 1250 137933534 137933561
    0x7111b0a150e0319110114130e01050f0406120b1306020a03021201170a030809010e0106080705042306060a090909030207080d11030304080a0c1a151c060b0103 70
    0x51035030025500400301c0b07000e00c03504506513034501c80d0081c0c6040780c504489101030244140d42d044840b443d405906940509080440c0003401c1c198014020040703107049401a0031020324903c010400360800b035081454450049606014080c1006203a0040940005001c0c1c820498003002c01e00340c150300c58600d10b4064020074299502c2140447c043d000e9885411100c854101d80400001d8120b00128002c00110f6070300064518400c0c503840441e06004068503100c840c1d5610003001c4e02d40c4609210f010000c04048028195030340c90311040104941d14131310301c0065800698040103206203192041984201c0854156884100307100c0b08442c1c1d92140e8202105d80c1c0d00c1d00d0005030500d900044e00790111040c00044400c0b4008200c000c44887c0c41c40f4110001580c030600c04280007840c5203014141e002e0003460039150307517000358407100004140b1110101281d07401805000c030084e0218101d801d420710680d12640003036180d40c031484e01781c1d004030005401d40d60f46500441c0641c3c802d070007540c03200106 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 137936034 1250 137934784 137934809
    0x403020a0b0423090a0908041e032306040f0515040605040c0501030c0e040e0f030f030406052202010c05100e070509011a2d0f09040507111b0a 63
    0x1c8841e10003999006000750040e10490041100065403a22190020f900c00600070905a41710b80d050385002e8650030b0700488a01e4810710000c622400b600542c20860b8045541e5002880d1660030a241c50405000c0d000d846260041c0200c0c99104e400240c09400c40d61255074449254802e043c15400d00c0d1645503908140e40400041c40140802608120301890082e0400c101c0f00f0f50307810064048480c100e2241c00414015492139000c2d15042c3e11248000e1130120a8074101041100c031141154000b18181c11410700100c14002030140d03600c69158080e2440d082c41c8202c1404c8195281d407105003210086c10060807414060400c60b0911031580320120f49001440302c260311590300c41e222112809441d004030030716400003030300c83c81c1184040160420800c1061414050003000d50340c000034400294407601c0740540c4c00227a00003050041c0f55940d110f1038916201c0d4440e01c20082590405070807041080316490000c0d5580d800402d40c41741e21031801d9101d05242c030311900800d03100a03644e44485242e946 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 137937284 1250 137936034 137936039
    0x601180b0f0304110109051c02060f03010e0403090e060303030a0914010516120203060d0807030c050f0607080702150a0b010e03150708070507120311070f030c031202070809060f0403020a 82
    0x140700301450107540b14a030240c814004810045904000e02d104881d8030418000c06400f030b561011151540050015000901e015000030341403038039501c20b80c000b040051401c0200300c14164060070305005000359000900032402c18200295603400040c1400c031312980c1e80c4070386d041005900c80e1340c8100490500000d01261500141d00c82c40c5900142220011135547e000106110400c0d1003101d20a010042162034003104c036859000d1590049017046050103500c0340300f0808036204215840700744914200400103482c052600900076440034201c1020f55200040449001d981d80c0031440d0700c00024100041c4480f51180100c070201086046550180141118008010900d0541502c5440c0c00c3d101d40c0f0b065140c1c480d0480b1a031084660180080c0050758000705050311035004444003076a001102030511046848500440010140407008200125240010141c000350542c5007090300c81401c60030b1005540b00c6100900c03070503110030b10840f00020390104400d580016180a140c019140102294 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 137938534 1250 137937284 137937307
    0x70507051914150a020c030c062a040302090601081b1b070605040b0d0f1d010207020307050906030c09040203070e010605031b0f0409020702010c02150d1508060601180b 74
    0x80400c901030b01c0c611050705a990307040000103101503500b000c4483c00d608a9079071641441c001c0d0031000032960a0b000030000b14104080412803540500514090181000c00e06503401c41d100c43c0d00b060f504441c400c18071007040075980e240041c0758419000e0800f440d42e1303560412071a0b844101c44c100a510800081001c80124600c1100c0151000014044448181d16080159a64016489403125140c801c0008003030345412504152081c410803100400c03004044660300c5031410241040340e84030380d03002c81c04900b58902080894000c20058506001905003040465268480c20b82c03032038018414031011030215101040410010411440740a0044d6113606000703005034400d944a004000303032110392500100c20b0a0803103461035140040103141c03914216400c1d01941000c00203a040c020ba015500015880386507070011810090307582c65540304000441030003243d402050030f0500d00440b9000340444080002c80c0340e002542400c05841300d0390500d0803110b41e500035030020106400f000c183c8500c0358 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 137939784 1250 137938534 137938573
    0xf0203011a010306090506332107080c0f160b04050c01270905070216090605210309091f08010614031c110109020603010f0f05091003020907050705 65
    0x140c070241d906100e11035035100020143c0d041a107480d94059003000b1000030111615506034204028800500c15610038000c402220b41c004c0c2c500d4540c85920a0300300e610800c0c003070540720360103009818a403503075041c00654440344d4041d5040e07a03e25003c001680c040e0302810358a000301d885a021008541500d00b5141207a110210302656902181c0504200c071014001c01001140450800e940d26440a240114040152034040d0200d03081d401082d0000200d00c1d100840f480141200c8000440d203203280400b0f1204c69101b0341001000200016950b609a10010086512720401107904002c59214040d00c60742c40056804079040b0002041e100290703c28040d013120b1300f200c1c044103022404034408809d050703e0704480d80f01d0041c900d1084299415071405849140c0c07090125000020350481c2e0b0390b020540c20380c000c3c0c0200c03241000c0f8810401032084012601005040d01340e90700412404c1070103480c41d05514500000380308900d600c000130461072003001621242904070044030b14a012a4440000c00e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 137941034 1250 137939784 137939831
    0x3031107092c06070206041b0503030307020607020606060c07030b040809060301030f020411030408030a1a0604230f1503041506090b01030b01050306010905060c1606200106050109050108040f020301 87
    0x48400c682e0000300015804194244202d4850300034000568644e82c4004440342c40e00500740d100042e040000c28107450800c051071003070b025a002800e04c3e04180380080d02d4204000c2c01144a89410440700e0440203011606508032607001091811580303c40c540910030340204a2065004107012000205100281c407840c0002d9009a40800443c1c3d0f421561500741c1c4000c075405410040c0400c0841c3d141c080f281e010a801c2038078036000880d00303007500c40000c0e5907a02c07560281060620403007440000005011442582d42c000701c0e4109840c001c1100811001024a44410f091200100001e414800b80f4528410380d031030452010031449855108a00041040c50001400645032042101711940218100c0f0b006a0058590b400040d01d8072041000c945e00905050105000b203280d0302912001e84083c03a0b001e0980d984039161198003826400004040800c0f100400d81c0c1010000c1003940d07003100f11042520400c1c40c0c282696540c0c2d0600550392901e03100003c2d0550300e00710b00910400c400e0000c00d8213 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 137942284 1250 137941034 137941091
    0xb041104061b02090f0a0e0d02010b1f020604030f020a060c05031e0108071404021303030c0b070203040b0306090a1d01021b01090c090b0a08010908040504110a090303110709 76
    0x21100111807000580200451000350004d810501203501c8041c10000b00794481464a8041255920a0100350070b01c8003054426003d40e46030180e6846074582094108018540c19411107407001a11100941da01c1c13001c1c0c0060b06100000c0304074490305100384540b013600c5400a00a00020003820001002c650049881250392078020000510024219034814100d038011001084228104a180c02c040e03050307018240d17849a0308005003001200660031440040d402602d40102003c69800d0565116030000c0180085400801c400e0001e0b86036401a260081002c0d54440c045540743d411080092255000003410560350002801d40010150028108440102c80d621160b140107810700e82a2203c0c2c040040900100503418800b00c507440d400340384d101c00003c0c01407400d955103080301801c540000700c05031040319000074280550308280c040e0000107a540b076403039840d00107103100042807103004c1d001c01420040e0807a210303001140304000c0000981602001004402038085103000c0d1060300c11182070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 137943534 1250 137942284 137942297
    0x30a1b090b030c0d031b0f0501020301030201030506011403040b13050f0c01090503010c12020304210903050607050304050d0e0102070f06030902030d030207020a0b0c03041d0915011401120b04110406 87
    0x51a0304010881ca2460100901390322013083c401d94040d5801551000d00704031422040c1040008582288007684000b03004500040e52941180001800e5505c0101454144041a0309400f00c40900c042107a82c00394008145043c142c450407040c01404000580c00b51052085410b188960070b404540003803101801d88480849603074540c1454240c3e202e180403400480c03541044881c0890054005541c054030440010b80c10302c0122001030340c1c0160041c40407000440030001441088410000b080d00400c00c1d0402c141036142070313030700c0940d140d142c070300300074104914080103600a900030820348002d0300d0916680700a160b11990010002d2445030001da109100f09560352a40600038821100c5054020342906501401c05c841d1004aa0042030302d605184410400050b0808646614411085003032540c5004c4d401d205031701c02c3c58250f80e07c1a40d03140d0662103004100c82c01003411a2942c20340c0a090030360040909482c00c00090070b030740c251a900603050040110440b400c1000400564070103441c1c50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 137944784 1250 137943534 137943551
    0x15040605101722052824090519111813030905030d0c140106060503010512030d050115020f010608030a05070602070510020415050702060d0902030a1b09 67
    0x3092115440240d080800c0c00ca414a51a541010b20029403280c1c150000d030302d940340d00e500603803560760341441c054805402040b403101c1401e9120170004561180c242403410020001e85650702d42e10541106444c01d025044e204001c644c6071038000c168035030b03000703015100c0d000002d4403861328820350500c0448040b0000c14464000d450700200035054100060008042540d410641114103581c0384400d8040c80440781d80004d0341c1e6030400c035004420000c0d680b05001152140303095100a1500c180ca003441c1e90401f00140f01c1c1c56407010507241103a0084503039400301140d225450741148240c40a106006080c5400410200b01c0f04641e4085406207034215060751180100307e90813a01c450041d8005a0010858104d01074414070252080d1805400018900f51203641d07820f01d030245030051065481d4003c9000c00c40c0040000201c04815150b0a185140001d50360000b5103034450010900c48030b40d540c1d0042400c1d510100300384032000c1c0d80024001003041c5d12504010a00e480d5124030041ca50412589 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 137946034 1250 137944784 137944789
    0x20c04060e10080615041d010507030209041b0c12031d1507090305070e060109090c0905010f02010b0109050411091e0a05010306051008071803060e06150607060c050d0515040605 78
    0xc045c0f00e5806601d03203290729881d0390104005001c4401003500e01c410121085040b0780800e204140c0180d100341c50059807001d1403424070003641c0c0c507a41d561050054503002d000c072094221641e88070450707205010801540f55181d040d001802900586542000c540d80d13101c20300b4100281100c1018080342080e0344544c1c50b000d04a4000c41140001407054200394000c00c03054412010441e08120141000301c1e004c1d4031020448102c44514a2800c001001c0c1715007007207613580084141102c0b250510081c1b054400000000c0c010301807511520303015550b2006003020955400c000c0e5840f001c0000c05a1540c82025510507000a560b035501d41c0c07040d00c1c1c0c0240001c0d558040d00c900c1c1c045480c00352075044c0c40d640f0701c034068a0341c8200901000070302080800400030340c1c0d085103e090295100380e5000482121480300d0600d00306004200780c0324047c140300c00c07002640c1c404044d47e03807060b8081001b03d5010304100e0b0480e41802003a80030340742107050005103c9503544000c0407410400c0c05036070402ca640e175034404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 137947284 1250 137946034 137946043
    0x9020d05060f1f020c28230d0f06051303090e1b03090a0506011d0c0c0721080307030b0405090109120309110a150206090309130b01020c04060e1008 65
    0x31040c0d109440c0c10102c00c003c074801e00000c0305003900f8015180c0300b070724480108000a8a000c108014120b00c040400703103000c060901d038000b61140c446514040056800440048256604114402d170254000401004949400751032030b42e52210f401c1c0114105014807040100039079404902084400c2c00c0403854100c002181172050f00b540780f20070b441c5c0c441a210300342030733070300107829102035015031285000490030130090a802400f000030008041d55a008034008040c1e030241040923410741c100903215000c0c1c0001021801e5840e64030f0009000340203490038200a030100c94000b0a803010100400200387d402d94027031411640103075014030043c0d4590002a0807101c0302900240b01c4040030300c40303c0030341d4400d038071842d109c2c1d200d04000c5a03447c0c10000060400c41f07a940c80b90380000e0304007001420071541030008030303040351a00300110b08103411070000030b02d8400c60440ca000c55640d1500020160380c420400c015410101a1003040361035220115280380320030440354007440c6060b880001070341a00004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 137948534 1250 137947284 137947309
    0xf0602100b010e13020c161e1d060a0f08011b05090120070b0301080102030402030d020d05040515041509030201020d2105040302210306090121141609020d0506 70
    0x1d41d18040c3e281d00400b042410194540000645542070029035000c1508100810302a03141d444c050807514507000c001c0c041d640c1802d03001800362022100800203880d48050384c0c00304442800b4000313001e50f40d81c0d002c503085540d50b1f40207080e0000d404500080d03020044d8001a03568080b00b800041401e12500c054030203100744001395000071100141c640c02c2100410084008885c03001c01e64403520342c0d646040c441e81d00300f80c011a8003654000280002c5140801103c00804998000b80c680054802805805c2c2c0c0542d00c41c0c10301900011040d00e0280403224219030250603007900b030008810704210000d0181119000403400b603c01c100304103851030f004210b095103801455050742c01e969228003100c0e020b8800600110150b2054589513000d000b04902c803001c5103480c041209850b0b1030040104145040180d10030000d550b120900b0302d4a0881c0410200c0f40c00747c004800035106050104507a180c24403552214006196000000c156061190010300204203803001c10b00c8652640010012111642c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 137949640 1106 137948534 137948537
    0xd020303060405090a02011205070e10050307120203100303120213030b040b0703140a0903110f010c0314070917070902030f04120e1e0d0501060f0602100b01 69
    0xf4440c1e20b81c132910203401003076845407540010b40b404175903182c20000c550f100c0000542e030b180a075031841050400038282210015400400400caa041515524009450a00c2c1d052401c007140c0241e82c001c40c0a180314940e41803466900703807550750048200e82810340e020707c07080e170403504401c000100940c01044460717607903e001e18200064420080040d000d2524140c1c10841c02d5084d80002a400384d000c480001c1d0018031780c02d0030b440401c0c0500000e060b52091444c04841801c041d04082961007846c0ca051016042c1030492021952003250716030005481100104041285803100400f0000b001c1c0940d542c03e92a000c000d81a0f9100700e03a0000038600d0030040c0010000c4802400c10b66060b546809604405520300040c0f0521034040c0c0c1842681216203184031540e42e0801083c106603205001b002030703a54401d55140c0c422400d200380b40141c0580a001f285042c00c900460a084605 = true := by decide +kernel

theorem cover : BRFrame.Cov 137769784 137949640 := by
  have h0 := BRFrame.cov_init 137769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 137769784 ≤ n) (h2 : n < 137949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
