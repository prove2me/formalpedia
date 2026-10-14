-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0555
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:25:20.681983+00:00
-- url     : https://prove2.me/submissions/fb76d4e0-469d-458e-b065-bc217159ac02

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 99640287 ≤ n < 99820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 99641537 1250 99640287 99640309
    0x20303100b13030f080d0e0d080f0c0408011119021207081612090e16080103020f12150702010c0507080d050a0e07030807060f1808070302010605091303110c010509 72
    0x7080c407500c2e02c60760380d4440400c1051410001d0b1408140013540d41203858050040320944803603640200300b82c0c4903001006114803c01801c4a81100729507010403248203156044400030905407000740b00303030340448407003100702d40c007901c81f507501c81d0b040085038481d8038001700d42c1214030165050500c2c200081c0303440d82c1030260f2002c00c25034000304c0d40e00c800d41c0000c0d1404c520125841000e5035160600c82c00c01e50b07204116040949580d41040e400e8019994055000010a040d83c1c0e05803800b501a2845a012405030110440c02c40514024094415421511103110520940e100d034000e21100754100c006071080d11a2030742c040c1c00100208a090304541c1941c12258002103601000034a48183e00ca9243c10589580c02c1190040c80026002c0f044c005c0d9030003800caa503c00307010b04024108400b5030100d40198030b010000e10034640441d00c1c00906000b90300120040401400d00901032500c2407a40c1c01030365880c04214040303185a09400d00050b0b0000d0105000324043e140e89242c4180f18080158003081 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 99642787 1250 99641537 99641557
    0x509060f0f0106050c0c04020706090c091b0e03030d06120515010b0a200304061205010f050108070f090302030106060e040e1515150711030d05090f090703090b010609080d020303100b 80
    0x60705407035500300c4c1c03280c8c40107140a602075040015030000624002d0140e2001e0f91000c14000d04100c8803035081646880150f8004540d410070b460000140c0b03010908500401280902080c60700c84001610880b1001d8100024030036000d94068000100d946000c409080c02407440800d0244100c0407241e00a918243c0412024841c01c10740b420080c0c0554035660040e0840000682d00c0c0015410001c1c283c002d040c0545030304410140b20b10b08100c0020309451000b003032802080003c01341801542c0c012800c250155030003030000c3c8012078903a20007504818944241c0c6000301d04e0009140c1030341030007203140d401c0090f01c41005181902c1c0c0111075040d841c0c0299005034000328103a60720902c440d0500c0100807843c0b15004a61401c040e1804040c00d10a20341c10640030321108200e8040301e6600da81703481d070f04014126100c0025444400044000705411a4000d1941108500104905030004162422100d45c0c0c021a00703c01c003403250880e224042130315500352009641c1d40511001002e03002909010030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 99644037 1250 99642787 99642793
    0x801050c041a070506010305010b01110118020402070c09090c060e0609010f0807030e161d07020a030804080702090406090c0504060302090f04050c100306090506010327020f04090302010509060f0f0106050c 90
    0x640f81c0b13820782002800e80c0704442d260340d544080302b03032541c00c16403001402e0748000c000c01c1220f90581a0b001c4443c540b040c000c3c481c80c2c1c001070348010802030555510140021100401c0744042d20300c0d04800c0b0b81e00e11301942012960815000340d640ca01402140c038a0f007410381d1501050084040c042d43c2c200409006001455281c9801a00300c0100f0001ca40302e0242c4800401d80f420300d002100c0c1c5a200f200d1034607040303d503074000402c00010340000e1880400390741450b083c0c0c0d940d9a0f50516580700d0042c020001d6021011b4010300042c0039103900b0440d00a805601804515660345040100300e560510000b900004e40c00c0019001c860448002d43d4414000c0701a07840030045000018403401180a4910100e075035a207040c4800b04080c850168011001c3c00c08102100b401e01c02c0040d035620000050012149200308402103445680030f00e00380f010082c0081c8585080d614020b806800100d89050185c410000001c0c40b09400e00f0b05240141000456140242d00700101200c21f80d108603844000341c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 99645287 1250 99644037 99644047
    0x52205070e10030b0a0f030b0f04050a14030318031c110d06030803040c0801150b1e0307050d0f110a1d030307080703020d020c130c020a061b08010801050c041a 70
    0x20302d0790014112215900c0d0740c0040c803007200d0010855015400d400c42e0f10030701c215100610005640091064024000441d81c0f480707541c40b07103811460700d02d001e14014492940c4000000705d1480000156000380b125805081421091504242c2c0d40d01800a03860000031201c0340d0043c4401c030326840140b00b69484010940340038401c20307800058801e240d0044502c0a0000104001e100c44142e5500103024514024452400c05c2d04440320254414090516602d00000b00b1302850f50480c0c00000e29804071002c0c1f0ba0312440d01c90009002908003804ea101d1043c140340860090005038400d100141440d00e0107282050307510f5004a4072212900d40c002c00d00041e4041c2100507980402c00340504621481d03103959980131a103802030410103543c400c9010740d4000d01030702c0110780d207a240b03900c50704140020000d501001050b040703282c20701d0206d024002c83d2034860303109201a1414488100920b01362100ca03c80d907a80c42a03d400c03207404807906050b140041c44107208200218440305d030b03058030100c684c030304203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 99646537 1250 99645287 99645289
    0x4051303090b0f0903013909030b09030d05010807090e0307080403030503060307030c0b0310051212130504050c0c1c050d090213020c0607031112150103091203050709052205070e 78
    0x10303103622040d8800d443d44100da0a2061007004104044181c03541c0000c664112601c4019081240c0b0740002000001103174000bc4540804000340c07901c041d41c070001800341c2d5a54852181e00c1e06414011407000c039041592a81142c100001101d00f8260300c40007003840c140c40c540f012515900040d1083c2d50500400c400000410700720181d020180c000111425036a041c00c0200f1010080e80d46e2001d8026044158007441c04400440c3d101d00c940301030703124a50384400d008425501c2c0e0909400081c4e010b803800041c0209142144041d050202c03422048900c00c2d10b00d1040030f00884820080700001900400c10300d40307840c0141d040952464409006131a00316440e071182000d80e00a1102201660300400400a0082c2c0c5405011103c4107407024142c03500461a420311180c1da40100780d0141c04416010b500b1680e44a5071042c488250426a000328000300d183c001009040146e41081c00542200340c0482c06240c05584c1c00c184036003040c170940c0310843d03100301480031300780080c074031014429204030003021 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 99647787 1250 99646537 99646541
    0x50f0307080a030504050a0f060c120509030a050a0204050901050f0c0d060f03080304020406211112030f0d050603071401031a04050a0c080f130311030705010c080604051303090b0f090301 82
    0xa00ca61604ca80300c13420203050040e9040c10341d04c01a441c43d4103c504102541d08a10b41c00560740c1c1003039a803880d41c0f282c40c4042e00c00e8850102d40c960507209901d520014450003143c0c549171a48203c4061002c0c0e1500055a4241c54007520074240c50340c0c05a001c2600c4869110003401c60741000c0c10081034013a60380340b208941c900940d000350b607081800800c220441c41c0c584500405000d081d0001d81e0203604044103200f0741403129800410b450104e4809004565551200120804541048950b1480307000c0e8117004d5600419900d00017141004003050491501003074503402d44d008400c0c00185d52002400441c00f808181d582424050080081080a900d4038040c1611038402000042404501c20314014416000108042c040094203014800c91181c602c00c9808195050300d40310101c01c0c00f03811018290700c145d8100030070039841c007032a000c000368109081c00c2c4140d5044500300030958601c1c040600c007244048005000892126080c030405c04240054503044440341c1030b042c01c2812070004030782 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 99649037 1250 99647787 99647803
    0xd0f1b06020f03150d110d02060c0a060c020d08060f060307030b03010c0203040f1a07020d140f150105030a0b0a0e0102041a0d060f0b09090a0b04180b13050304050f030708 75
    0x460024000100480d008920903d1800b00c01c056170284440c1c00c60f5204d010740e00781c1440500b1700ca0140040c040041d507a6080070740c0e10389054034054507120401883d0034030090800030070a2002d0b028030012440811b0181140a10941c0081c140001c808032003c1000b100e0751004020505042c1d9806003400c5644003445110307512031281d0001e556990800010011140155014610f1800401c00b0041c0b140d03500c00c19158142d9040d68241915441e41c0381c0034405a44c10000c00000703219546400170703d41c10019502c0800c100348805604a640c070b8030103060321010401006030400308010007259490300d45034400e212038000d400006003010b4a036000a24494800420b2128111010428045480301c0c0d1054100500512980569051a00f400c15005014484041e44543c14000001d1106040382d004048000001402000080c0317410400049180c40c2d80c506580d05400880003909074911080e50460342d640050046007050b15110800005c00040303441181c040c02001c100154103041045021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 99650287 1250 99649037 99649057
    0x90712090b040303050c0406020709020a091a090f040b0d320a1203060302010c12180b0a020c090709050d080705030703170703090b01050120061806090d0f1b0602 71
    0xc1074508207800c00405440f0054655414007804110411503180c0000b910710403070f0880803025895098245d01616a4900790340318841800d440e1900f075028404100051410180c11501c3c0350309045c0c075005100c202d44043d50b10301d0b04a070003003007010302040c0711340a010096030340003001c3d44009a8904c1e141180381900400b0000310ba100190260400000886012650440e403804008591a5400080410a40c824041c000d004020940305e06c50384201038021000820711102c035110b655440c0c2c000f81503445200b9000044c0100000321040b85010020349015824130307a101310280f4109020080b5510f0900360071565507004018500020b00184040c0429501a40390044103041e803101c00b41c050600100709504041c0740003400e100252106c01c01d141035032001c2c42d00a01c0341040580344142400c611f0712524240c41520100302c00045032208440003890340505561098440c1e580c1290f44044e4800141c000c81c0f003411203501c48a00c200c0000c44030034541c04807840c01c41c1c010380ba0f200c12648114200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 99651537 1250 99650287 99650303
    0x605090603040605280c170c040b0c0c030703140f060f0c28180e0606030406050a021303080903010c1e050903160603090b1f0501030f020c031606140c0909071209 71
    0x81086400050410402000c00340261f00391030180141070641c4102d026860450a01040c1100b00c010108625080400c01038104c420542d100d040c201000041c80c0060301c082c2c401d0f4140c40d0b15020300841c1d554000c840c1803801c1006900c902c00d00c030700c1c19040707a5410007115100034000e1881d40f646030200c1c48a01c8603912400c07004007001040c0010100544c200b4803050b0018410b01106071a22002c596000740c2000c0000340a8440c004805d02a00c01d00c036408809452103c401b0081c448120700900c02c800c4110020040e8524041e010703952a4044000401d10b00c08109104400c02d010341d0007001000c02c02825100071540394444208a03011603001000081c0da01c0d03072000100113101c04085d4019840c480c00314080c1e0742c140801c40040e203d900886042546424840340d00220fa601558000012801901d460b28205042c0b4070714144024420340c1e15031b0070203881c00101a00d41c550a030158102d00074007442c00e441002804041c400140256081201c07110010303c11424500c00c51698030b22402074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 99652787 1250 99651537 99651551
    0x60c03090312040509070516080d0b0919270204050402061b07080d030b0906100905030a05030309010506060a050a0f0c0209040501140c03012303010e01050c0a0207060509060304060528 81
    0x610140105c010403160038032804004074031041c01400907a01246a000311003507a0f50a42c0a5a440070704401c59070390360400500802d0210803441d9403025541c84071039803020000660318490005045807a8190045030700c00144480007d41016000175520600141c50030346002551000c9401340751010445c0c6069800c58803040c41095000d02c440c242688641c5018414a40001c0005000707907006400207100b1103049050028450040f903054004100c010155900f200207030900688a13841100e690010b0351800c000184146443d0007074440490305030791a90309014400300250740b071a80f40100d0000f8010380c1d10103000180d0721442000c0c0f04134499800810040c1401030205200b400280c83d001d810001480148400241d0302161012103047c035040c100c411803110040ba00509016901c904254201810000b00c40d42c20401084440b61590031214480c0d9501e0086075a40113415089501c0a4100041750115000381c002c1c1ea0403054084020700086051141c045e08140340c4e020005415850b054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 99654037 1250 99652787 99652789
    0x30403050d020c060324040b03030d060303090e01030f0803070504030c1d10030803060409020f0607060e0d02030a020706080601050c0d0e0f04050105180709090614040515010e060c030903120405 85
    0x1020103c0e408041e903000703045080401d00c01d1400c0d013a5a5150207401d5143d81d000d00582d58030341058a021030050113603a41c408190080001078181400264042a402e01002440b4200c90380c44074101c0c0c0e001020640c90040c16a9011205e0384050126420000140004400b00b085030409a0040800c0c08808045444014031001012401040c4484000c003491042021503511411a0790041c802c9500103204500c0707100081402c1103000185400c0b0001003207820401c0702c15400041108202c0d42120341302d40b40d006080342d681c41080128070058001200c2046064090341c0d03100c1d000070301410710b0750403c1c1805030307001c0c5000140b61f010302c009040126100810b04180d11695041e1500761814082076050001150300c0f004205c2c100e1100350360000028500512456205018040038030701030064596814200c501c220b440d8079440c0c03282c1c4c50000440c0020440404580c58200107031107038001030401504000351600691180c0d251400208044540ca90741071000480301d141510321a40c5542c10a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 99655287 1250 99654037 99654043
    0x5070810050109091112150a0605090615071b0b0304060f050705040609031203060f060806040b010503060d15060f0f03110306100324060303110d0f0e040914030403050d02 75
    0x29208929042c6000384c07800c08200d12015003000d0440943d00080410710b0340d41e8051030821451004100010b02c0300c14000420050b4200104891381110740c4070042d16120200000c0c1c55100c031940c00c0000003003007200c000981c0606510360342e41e120f40c1609075160742c401c1c500c041c03030703104407000c0300d4066175102c3c0313018003c80c2c1d4419280c10501510b4004d0a0908203140545041084c0c000601458009081c030f0b01c07410b202e5040140a0301007424141401d550f100342c091301c480c00940d0403520503820f00741c0550255105a054034030440e0000c0041c5212000c035140e003410b00421503000c03a441c0b42c0719180420282845117030031006020030400f0194951850400750001044859681e2090b0400001d1080007079021100d04150b9402000c091303400550501160660a1a10781891803142000f00000905422001000544c0140d000383e448050800030200e4810004d0700120340418010043c29005040c01e07803080c9459449078100503441c4c04411125491078001d40d0080b109907002d4484011034a03418 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 99656537 1250 99655287 99655289
    0x105160f0501050f190e0a020d1b140a12050f010c0c0213020a080c0d091506050f0901050333010f0501090905090d11010b1503060f061608070f050708100501 69
    0xc18a426890030300860340703880c4251068110020b01d40f1040c400300714000034490307c0030b0507600500030940c06a0340d1810a004480100c00211100c8009070001681c2d4001080350940000060824040c0380c10030000403030490310800e040e517040c0306801c500090507109208071041c03c059911011650201c52042095800e50001c2200d5120700500402602940124006801400750010140c070382080603240380c0244074161024080405590f00703424070ba00c41c5c1d0300403010f81d001610403103241aa0141030100e0312000b031280315003503440403140b0a4210382c80c44128031204010400280000721002a0b600401c4c000c0c0c0045d0410b06410408005560b0001084030040055410510107803500c4242c1c0c1c0d4899621191543c01c0c00410b00340100407840c00c3d4040300e1808030040c2041032440c00007060f60b429030421074481e80210500f2170b00c0380551a0820a40e0105650400a5164180140d81d100080c0e0030001d0304980244500748458001002889210080c000c0f02001f0704002c41c844040304151141 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 99657787 1250 99656537 99656551
    0x405060a06051e010807050712050d0608010b091b0c0102120915100b07020607060c03060323120f0702060f07021c05100c02030c0106030f0c140105030a0b0105160f050105 75
    0x40e1010000e80d08035643ca82e4403030071200342451840c5950b00441601c643c81000002000c00c0350040c1100c04058120011300480c4160440400c510750b200c41c4030078202d69034070f200d96038482001c00015000007812510020020100308503181000448180070342a60414000f041c0c45c003080500b0002408020001680381c140d2075070b17085085050681d40c01c90f000c03520340a1081504800a00c520035510707400101d0344000d50006080185d0b00c207100d40140148424042150322191950800240c040c440f511851920b4405003d4100748140c0700002c807069106140c0e0704e1500c0c4040c403480001d41e550318090142ca038000b9440560360741d0710344100415120001034085014042d8940c080100d02d00042940c2c100c0c00c5298005100b1552078001d91a50045074040311640d0300f014008000c1192401041c1c400c51b210b440b00f2340703001ea00d41d00200320010380140d0090005209000040041510390400c0d2403480301030510900d00902000841200300720840152071540126000c081041300074420140e101075 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 99659037 1250 99657787 99657799
    0x1215060c0105161704060c02010b060408060405060105030106060203120a0f020a050d0b0603040c1701150f030506090c060a2006100e1605090f01090e0f011d010518040303140405060a0605 82
    0x107504c01c108040d0034028102400302541c03081034a103090300035401800c21303090003004580c403550f4850074550380302000c42d4120b0301405120000580b0b828140248410b40b1071a40240d03080c040324007805480e11100810a90308103460b803020242c02c1d400352009050b15409070b0340c0c295841c013982c0e640100351503103a103456000f00310400800002c112040d0032941960817101d030f0058001c1c040d03d181405880c0307110401ca064400c0450000d03480e856901004202d922620a0700d40540d902e1745201d4865601d54101038000d8030812144030103c1c4075241142c400d0310122801442c5114404289140400444600c88146510b0303070144080180da000290f8004c056031400b0301d5a100b0004010314034060304000f58041d42c01c005a0b40740700d81c0541c40c4440600400213002005241c403d1400c140030a081c820062b005500307040036000c5041c0448107505840f0041d01c00c42c2010704840d4014000c0200410580c201075541003680707034024a007140180a68040c20050645081071801c403c01c90f1103660000b03103d80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 99660287 1250 99659037 99659057
    0x30d0608030a020f0a0b0a020304060f110d0b06090906120f03040608220215090d02031207060c080106022d06090106090e010207030e1002030f120702010b0105040b1215060c010516 79
    0x22007101c1001c1d4010f0340030502603101d403032b10328250b4050310000c4c10358240207080480d80d14202481c1c001520921300080e000f80142e1000005005240c07050300c040c0d40e00800080b000500c5070400c0c0c00b00044014605046801c258039280419007581c100ea007001d00080c41030f034203100d03403070326102c00107001c0b070400380c0003442c4840507580000c14404141201e4510100040f402c000b0641e00e00c3e150310304c2280c014081e504d0f0160b800b03002034556400420201c62940c60f1842d1081c156101c0d6000d5410f99159400415042e6410014203481400a455007984108003520f02ca000d0342d011f1080d903000e0514600003058082c1040843c406840c0050740c21687d5a10501c00c00c008a0751240c03580c0e00075941030b52601280c43c403040003242140b0a66605046034480041d524031405c00f01195217100d02c90307503402045910954801110b0610030f42c800c04018110070322080c4250380d0140c210076000451903081e1030002c5003e0020034920341001c03000010356503450381042000750300300c1c0c042e040703c075128a0421252 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 99661537 1250 99660287 99660293
    0x10b0a021011040504090602121005132703211b0c110307030f150204060c0201030b19080d23160f06050a06170d050a11030d0608030a020f0a 62
    0x7034404121100d140c1034642c1600308600c540003040314042d10b000340092043c640e0038200000607502072016205080250400540c001003c07480a82c141da400800b0300a00301d109500b140050040c48031071500c0301001148513900615040604040305101e40c807102e0342d1400200310a500e130540c00c0400c044540c01c002d4080078130003101b4113601c6035036003e0030100c24642c424203061482c0d11a101850350540704048000c0f0620410030340a45189200350140b03200c101000400c00140c0c0a41e00c5000c1c0403403460520030300198000e0300010f0f4480800383c5510520300310f0302450403003a200c41d4040c1c80107070001c0317014001156201c4c01450040e0050092600407804c1031840c1c40d20f40c801d180d40d0640d852403405400782000810b0700b40c6407840750002c800340210700b0001e584400401c46842440b060340441414080c1101001c55002002000c80d00d41700c0c04c08941c2d030010359820038a01a60b08184c002000b5613001b040c00c5e88100300c05403e54030015502d51580f618041d1a040c03c5a4407409198450440c00c000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 99662787 1250 99661537 99661543
    0x5101d031b0d051002040801290604050f030c100809010e07030206040306110409051e06220e070e04060b030d081311010e060c0a030207170303060904141c08010b0a02 73
    0x15002080d246802d41d0307051810914105080c400c1d441c000315000042c00642014150403131039810700c3c1e511801c800311609005040c2c3e1410038120841e08a0810b000c10070051a0140c0840328241002d42a034410040e803100240226055800403408903039040288201d10800740728050154500c0c0d0b00a013180340c1960005141c9010b544002015a900c5110102c3c01440007005d8800500c1340c4007082c0a1401e107405002951040b2000d0307402d5411128000401034540005030024a40c102c114010764981c01c0d2070340f840075142c0840301c4c4d00ca07440740c036900103078940c10310365a10b210b68050500040d50404840070075080002c00800c0b9410428807205202450342c40907040e854482e8403403c0a06403058000040c0c404180408856030f200c2804903030142c000c100030075074030000b078842d0b0700740c9846a40720100001e10501910034a6400d40c0107000245040c01d02c41d80311604140100701070880d8202c1100c0304c0385480d14030601500032095200d06c129105070490001809440c80302640c41c10000c072800c1c025a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 99664037 1250 99662787 99662833
    0x528021c0c03090b040c05100f050304062a0e0a0f0501020d03090f0c0e0a0f020307020a0308130212030a020c0105030c0904090311010218030c03070b0a0c080405101d03 74
    0x18885545600003a81d081c0a0b0b0711459000b0340c031404920080c80c281c28221010810307441001c1c0105078502000d40c00794400d1900b041910086c1e110740d811901e41e51200c41c010240c1d812003032902c0c1d08050300340b8a110811840f43d180300348580d64441d103aa00300414401e50242903802054604442941440701da038000c540c00e0307076900003840c000500303103000e080c00d0601740c1c2070f2800a0480b0001d030f1004641c482413682d500d44200b80a11040c000c0640c001401d90403484110b0f0780345d00603001202072500092040c0d40b07883e00308000c0351600c070b801e00054000038052213110034072400340d900020b5154022501030041c0c00c500402400c6c91401d6203014902224513114a80003071b4400d66480701e0350020540901d010f00940c40301d081c02151103507035040b80021580942140180300f4402c0941c44520351071300140003c1074801e42c0046a051240360913003130396030203840b22049802c0c84003480082a01c0e04d96414400848800e80c0d228400506508020143c0d554030809140c00303504198418214420301000c044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 99665287 1250 99664037 99664087
    0x81b03010b0d0212012306010e03070513020c0309030601060512010806150f0111060c0c0c2205131e0201030c05120103080a0507060509010b010809030403030806040b0d06052802 78
    0x60488255000380030f0040041b044070300c00200346942140240c0d13030704002c040d100d40020703228502101241400c06d07507120f00501c030b5190b11141e203091965005000d034015180c10700c10007040700d0030034860780c0020342042c601b6080080000c0c0e0214540301c214426a421a0061180e500500f24608140760307100501c410001c941130103944080d8408200340d01c40c0c010020000150000d6034240d01b080a51500b5030707030160800c1001840f03460660325040ca04001020003040395145403a1100603001c1e01c50014241c0141461a19255407554201042d549511110010010080c00c0540c20765407002608481140008004000d001e001c1109034514520501d41034a401811032612103045544c11600340c4240035004001030f0820703062102c1300c2e00c1500079941c440e1090702d5606981d603c071507106590f0300552201900281d5828041003040c141944110b920400c054101c40c80000540c8480003610000d0f500c003a42c03400c040d580c49400c8040058074000150280406501c0c00804400f14a40806a07968003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 99666537 1250 99665287 99665299
    0x15030417030c190e06120412020309010e0d050109021c1a0402010509010e130f060f0608190504050c120d030c1b17041a0a0e040204061b0201090f081b03010b0d02 71
    0x11410a13001e010141040302e001440756594283d038a141070300c010003d5030100c514555030020305807001d0011059522460040c0d4890040d26541010070103006d0007207109030790039580c1c0c6013101c016803a40001d20101090314841744134144902d00d000185d03042c0391200710001c10035407000d02c00180c3e8008115420001e0902c4c05030821450b44001a42c2c0d0114520420343e0a803801c02c00e4001c1b521160032400480c0c120b40c4000c1c00c010340da480255103c500440384c0f80041201e203901080d0f0080c0c0c41e845141c016000d1030444011002c0003000c200a43c2c0c00c91012030180c1e00141240c00e1060741802174a03800080352501c0d006503000c1111103e020320015400900d090703180c01e041464204d460082c3c8008000048501c40340340500140707400294801c001500c0081c4503a2000c2007981041d00886044950301d5032250007910320041c08810055045204904010002e600001c1d0012000d59403c0941011800b611102c54240e0300700f40c0c0d44000807001e90003030741041c15240c0380c0d41d111409880031540507507032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 99667787 1250 99666537 99666577
    0x20601030807151e0b040e010204030206120a0908030403090509100b1c02090319020915060f0d090606090b010f0c051c0c0606060203120f04051f0b15030417030c 71
    0x681c00140c82940b60b210003c41d81d800d85103c864420b0b8010f28005c40003a541000360385001202c01d8240c1c4224013029400050402c43c481d41412495031040d07109004a1002500d00c0640c1d40c0ca248035481036400703400144081300b00344203500d40b1031a440d400c08a4180c61221591812148454601030035030f0300e101c1c80451103415071140e505501100e0900d04003e050fa9a24640c510b00e2160700a84050160301074008a00040d06000011074521f2030541e00a002504029941c1d0810041d0b40c042000c001d50a601c660741a40010303054050745c2c0c042e209084002c10550000000103003110039206666081140348000400851804100003a091001520788d6101c0070b0a00e5083c0d42c82c07607240000600c030743e20b400b9001641719804409064450040001d20300d8603150f00742c210030140801d5402500640260030680e00e1400c00d18100f01c1c4a0100c00c4010800082010001d266220a001781c0400700308004100010022030343c1e050900001141070650071030514008032a0b0074003600c1000d01c1c40f4440303040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 99669037 1250 99667787 99667823
    0x20901020f0a0501090b0105030d020307020d02040b09040609020301110a05041422020301060305070c031704140106030501060314010c080705030705040f1202040f020315010302090a05030616080601020601030807 93
    0x4286001c07420300741201c407050000c3c5480340c02070010100965071003543c440040b44a1070003040c42d55500c0001e500550030110540c00b0840c02881d006c4049910654440c4845140d07107a0101c40fa01c554001c200c00680a111401450700b0741d1204a107038036103014108030940c2200e0f0010300303030707420748210915400d54640400702103030702d00d0301000c50b0220094284200814401c8a500218140d8906584c180407580b00c030802907034207010603c5d008000c11034020010684061a4080d1030b40940275101c841d2458000201c02421140580c000fa9001d0351908030034400e00c040188900c0702e14441e4402085540105100100b8000002e44044200400003011400c16031154090744c0140003681d80c50301403d680c864184004041400c0200c0c001c038106010000f41c150280f0940e032240c0340c40e0740300500540f00a00110000c1d0300c041c11055102890342000703d01501c1c10072601c2d100d00f980c282900e0458403442400340100c400104443d0441d8020001840080c0e1001d06035090030364040a001d019040c490 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 99670287 1250 99669037 99669043
    0x50106031b05430f060608070308030f0703060911040f050603011202010f02012414010f0f050706060314070314010501270902040e0601061205010e01060f0c0503160b0a0e060a02090102 81
    0x40b4407100303c60000c9091001d2164401c1c00c082c0c154419030040020b1550b9103a0683c884049102c0a881c000e010302c0010350400201c2c580b65804401071030009140c07038540b020481250700540c1d01d4441044085001e00c41400b4440040015203070880f45542507602d8540a6541d00d454801e000b41041510b82040101900035004500c4040507818600300881c007540c0cad00319418010384100c18410512071818941540602031000000500365500012000b0741041039800c0c0e885005c0c00c81e0020750f10103000020604031440d607044040000d0140c031a0500d5401c080c80402c03003002c62058117901d008010010101749013107815a00400142600c01c0b031448240b850018040d00d034020703402c1030915088501e01c00001c07230854103813032094a403600b44c040c00e07039110000c4842c02d0185981028910703006001c12030080304100c010a00d84d14084ac2c140e2010340e100d40c00d581040c0c1d40500343d05440d070422403c120086541560101d0001c40422a0302d4101030f04541c0c1c1d18002d000c1465640e400244541c00ea4424 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 99671537 1250 99670287 99670387
    0x304120312090503030a05130203103803010e12090415081603021309050c0d06060b0d0b100305130f020f030d0509090f060d1b09050106031b05 63
    0x70500700110882c038240140c0340d50088500d00031203450400014481c0c0381901c41da00c0c10a40260051042807401048a0010301d010411401080031101c000404200c0d100c2a511507201d040c9410380000c50007009241c02d5070b50343da20b002e20603000b02610b802d90085107001e89171740c0042240c001c2440801d89140c605010507a8104841d28021000001c0640030201c1840c401c9030b00c25114000d40314010302500b0211158400c00801542045282100c145025901d070050b170f50043c8c0001661300e40d20b80060724a540003040b2031641c0d07901e400c180a200e01d026518198581007d05041c041817a01d0004c204114811920060a85e840b03400c5503000c0d07444160710b0260300030005d802c80b4400d01c0399a00c00b80503900018100d40c4102c0340180000c4011080c01c0103140034800140080c80501c00640c1e03000284a100030050604007a02100000c0e20025401014020400c1d03403000110041030004100c01041002c4c031800901c074041004d005202c40c0950180c62009800402d18600000b680460a0101c92 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 99672787 1250 99671537 99671567
    0xe0c0f0d11040303170f090d080a0e030c0d11060403080a0c020f0102040b041707051804081306081608160c08130b040e01140f04020724020406030b030106030503041203 74
    0x400b0401008143e04240b5035a1200440503100d449540c2d801740c0704410f00c0003154100000d411090400351141c2c01080055040102070710082641c42a0001301807554111a140d108140d100c10326403050250404442240401040c1c041c3c03180340342607100039103010409810a90b0041e075462010b40040c0c4240b000f0b40c03601c034206000355684d5035500f403000c0040c3c000b0300858580442590041c4100000066003004507070000d0710408400144407071040e1010402001510507030001c1180002c8400f015070b00e07802801d01600e4555041c240750f039034040704420782008841404000070074481d109030346c5e8100414000352403400c400c0e04151450030a445001c1d075090314140da1204e40c2d0100e111902c0e07202500c00d8078440c41030328005a03a103140400c81c0c0000c00c008681c010050f0680c0003180d05080d002040c2e00350042c00b200c03568021001450715071402103e090a4040d41c0840d0034080035601d07004010a45200b14020710009095403a5903441c1c2c0309034441c421255000c42c00520416014921020030980 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 99674037 1250 99672787 99672821
    0x602040e0c030603191103121b010e06060405071106090304090b040902031f0906023c0d020906090d0b060a0801090203061303030e060109140a05011d04080c19020301060e0c0f0d 78
    0x8c174801542c0c51036040401c08900c42c5159401980c0304540510a078120011040001c03c855162081440010400644004204003034010340403000c80d01080034a010360407107401141c0d00da1500c0c03643c2c0211b44070b840c1558411070518203840c000d0394001400444091201d00d0008800b06403816520013000e00210050081d8008100e404041e0464000d49203401907508509400d2481405141c042400a0045100b01c06050000302000c20996001d00721460024003918030b401e03481d00008502e0002c1610842d003000700c0340100159420080ac41800070004140240806031032640013945800c00140703200600c400c20300d549d90a15110760403036410360040c1170a071011561641c1a0402800c0f0b202c3e000b565401d0600003040000c460352040d54100d5840c580c1005c00304030070b2058900b040202500940b90601e0030701c03000c11406e0303040c08002640c0c80710382d9001c05c440f03042e0310505003076800c03a61005074204e0300a4200413282c83e2141c12208101c10702d20f4041d54075004211424028000d41ca1481c5400c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 99675287 1250 99674037 99674053
    0x7241b080108060105040e070614070b09030706151202010c1a04030c060e031303080901020a050106091a0f030a120c0b0a06140a0f050d03020709090602040e0c030603191103 76
    0x150809400ea040e2920441034515a03130702d650a11041d21041c2001020551102008014561098400500310404600c03494600185500d550441100a850b024015000001c0e41c0080143e984115280508901e0b0003100261400e00c440045080c60b01e070107414403071410901020810600141d6400440301d280119490a00f410010400b415122003113a00524140c440e50300300800000f03072030907164090300303550859055a60301e00460f00040d0a1a0540c0b00c0c0c8c0c00d400002030001c0c0100000340c0010b580c00100108d444c0340c2d40c00754148a1074000d000382110250100306071000f140c1058000d401601d10181d5882c01841140d08544941002d0f00b00d0300180280f09485100d600810b0445400b08095800c04000e001001020759285c89400920740c5c80820403c40c506002d100035803100e02030300648100aa0721800c0c00e00340d45602d50300311540c550000303044c4044000305d013038960401c030f440340840d0847c6040310110703039188080b65075515070444c02c00c070391802c01405891401c4000d80247c02d031100740d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 99676537 1250 99675287 99675341
    0x5010504050a120302040e070f03020705010e0c03011d06010627061d0415170c150c070b0310050409060b040e01091e03080114060f07050601060e060724 67
    0x1600b03480c84101c6210041d0303202030780d90a20a0080c1c4d4103036003203500030001944136280141c400d0b4130a840c00c2014142c080c01080c000c50303002e1284185040e8120013528091940720105800c4400b02d420b400614054840904144040061200d042d94050700b80390188440c0074940c50703500b0300c0100f100c1c0341c03041c1080b0f404150164041003030640c0310004202c3c0f0003005440301c100025600ca103020350451000b0700700104580d0680fa40742814a450f0303241540c003201050300110f840d0b420700d0007402c0c43c0e0307010005524000708010001d08000703003400c11180303003181040041e244841c0c840340310b40c0c2e101e00e0300d8007040e0041c0a80c45e4030100400388001c00400000017000881400fa00c440030b0f00340c64411202c8034040c0c400700a150100c45169140d43c0e0b282c15070b82441c0004082100c0e414456811100512241004007140c134010003401d4004d20091181e5854088000c01380800e880f01203003d0343c000c0c4078980008500c602a43d00074418050031052102c54131496900408050030007980b154800c2c0a40181 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 99677787 1250 99676537 99676543
    0x605030604030e0a0b030708060d03110109081306030203090712020a0b04062c1503100324050610050a030e0a020613030308010b070b01060c2109080d020a02010503011509030501050405 81
    0x200c005851303400b01540d5038003d48046000846840f40422801000150280342c407441e43e42ea1644242030809c00c1c21580d00803942114070800c4212994800020240740e0382c0c0c22401c8030001824549815071551800000e241d4440b00c0ca4031034880203440c60550b0608540e1030351642005481000503d5071503d9540d84001c0c81441402070741d070109410041c041109034402c00400041581c00340c400c5464104110aa10880e4002000107a0040c418200403002803000411b0300e44040410a03007803190355044807500c00300c0d8005080d140c440c11048420000c0f458003c000d035420805e85042c0010030503114002c075810010312240c025441580000e42d107500390484403400d415a40a51703105803480ea00e0703000050084c41403490280041c0312000040001d81d1003403041488440c45003241d83c608141203400c880400c0c05200718007000c9003501c0c81c2400000c0703003007280d2003001c1d185200a0501a0702600081e10500c010b0140ea6406480341c260400c1c00e500840700b00b8015035100c0000c00083c44c081c200661 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 99679037 1250 99677787 99677807
    0x110a0806010e040605010f0c150e031207030608062409090f010b060403150b0a030803040c0302100e011d0607050307050a1e0b13030c230d0302040b031603060503060403 74
    0x1020802d01c108400c1281030503c20300302514810384a00030581d881042c280e07104108544212400c5c181c2c01c1d905003001c3c00314010100b00602e0303200115200c2d140341001304c00310100103011104051808104000020000070b00f00d800107030f81d010072804403080c3c0c800035140a80e402d0f00340d9040b216400610480c0d80001521140032119030000b0403005c40401e041016034811440301801d00034040345848015403e1340c5c4600c942c0c1d403000300a000e26954a0380c42c0005608100c905860f44290b1034801c000b5400c00510f204550241407428482c1070b046600044c0c203412102840403041c41e030801020002d07441d04000c6504a5030042c3c120394662056240c429036441d01d401d001c461282c00e41d402c00c09524810b620808042d03034080d104a402e0b41c0c88240c10907003042e102a054003080300442140d408035a44803e5892001c0100072a10111300240c0d207010f260003ca00307960b604041c8100820050110558141d0b0307000030020001d544c0e1145504c10441c0540307400d41100b9032501a10040c00101900245260 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 99680287 1250 99679037 99679039
    0x50306130501051005130c17040303020d05010504140a051503070306090c080102032403030909010312030c0e10081905010e0f090a080f0a030608030f0703080c0310030f06110a0806 79
    0x4002075132121a0740b403c0300624410140c004178100c604594403d41a0000d80d011605407806180654241200c0c1d500a141038a0560200e40e0000c0d03020070803c51405154007418042d1001d0203850b038012014922200000c20402619a9610104d040321425045810150700000d040381c1e80c0c191a410304070000d00488501f210031035080c034000983c1c65418021790744141000d034440791114586c02007070111031560102c1d07039a1501003001003060594076000418041c600821118660991510300901146c2102d40c090707003803103422040c20820740d0340c181d66001990907501d0903a4090710f40480480c1450154000b61000c5420500003182e10000c50001d54810080000c0c0101d45445039442c10b1b444458001000d004410104003652590700351070001d00002c83d4501c2c8c0055899030f200000e9085401201c1c0b001604040080c0b40400d25500002e141d401441c200d003030601d5801c00c00080140c0120511004005140c0c05100509220f11507010114940300080d1041e03640020b20300003048201c00b00c5400b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 99681537 1250 99680287 99680291
    0xc03090301050609100302060d180c1508010e0c070201030f0218030712020102030304080f07140d0e3f03072915060f070804120212060906040f060204050306130501 72
    0x5801c1d8500907010360b00170085e03070001040144c156021320805600000c428005203480d0301000700307100088180c40503910300844070210003c0c02c140800000c6403183c00404108100c403001401120b490030081034004903a03d543c140ea840c990310040e000382c446101d00110b020710118002c00300d000c0034560300784482801c0341500c0c129a00c071200208880c0c0483c00103801030340203000260009402c02e0003045401e0346280640d0420074941d95014124902c80c0b400000707074200d601c4814010f500807211401d0b00000f02c0b01c1101d0502000d910402a55050742d042d04045410803241c8042103241c0314a904061403001036a0b50344800b4104415481d81111000d43d03d02407081c1c18059425000c0c000303600807401c040aa207000e8034242d08019850704056502c0f0b042a07420003880d00050020402003000744800352804041d40544e00402c083c80324503540c4041d96070850410002e01c2600400c00b00e50160344a60707450300b500d1890810800170b000740c0c0c22007905071080c50103100b11080da2030084000c45101c1c0000f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 99682787 1250 99681537 99681541
    0x210020706090c06091203050307110d09030c0b090105120a0603140f0606100f0305070207080d09170c0303040320060703020f12041d0603011b080403020709051303080406060b0c0309030105 83
    0x401c68a5110b1441b039038240340300380c2d040e400000380b2860055421010500d480c0d5070312040c8240c01802c002d411950040443c2c0e55207001c10030050004903d40003014400441810041c1200000c0c20740c0c41088520b00c2e00c0100140000c41c5440c040d84104040e41c1c00041720040708a0f0428002e039038101d403002c45034aa21601000406500e48010034005070300e038964a10010b9120710700260b021b0200503102d00154012007030f021422810070880e609508446540c1e0881051414505107602c0c4032460b030380d8809401ca902c1c20401a00c000007110202d81e8440388800c405034001002007025003090b40c02d903074862000603945003403603400500405d400002c003095030143d89e0050b04401ea43d10551180c4491050342e0710710428141118100c0036803040c000b0f000481c01d030310804184c503e0070f201d4035500c2c0d012030758002c1030100b410350402101010702182d403c10002400d108107842c0c0180c1400f40003d080100e05800201048900d03007041d80100480d00c00a61983c07100740584c1d8490b0850424903000350b19102c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 99684037 1250 99682787 99682799
    0x919051f060f0326030a02180d0305040614040510030b030613050d030c14070c0e0f0f0a0c0c020907030b13090b04030c0503210105040e0f120a0210020706090c 70
    0x2203008100c4800000407807955103140da130003540c0020b04620352007600b1400c01c60400403010200940c4510b40036400144c0c2c0c0d181504090b11521458108076001701e04503070078100040d13042070817902030354002c0c240400c134210049080d0a040c407a58000c039802505d00503a0050503901500302000514084069070f04503918001e03441880c0300d030990041d2166200a401641c0c50340280c3c040a4800300314640700120618103400443c0d9640040340c11902c800d001002008400150741907035403c00040c0e1010302d4103060040980190f40e8016255101c203036921081c001040b0b02602c4120a45a4080c0844080303181480000d0014401d81903464018a4100100c01d00d0f44518800d965a0f03a902102c110042d8460b03440488400001e5102144d04d0300c01000310540d1030b003503103101001da0007040d01c01801d59810a4240f106403440404620304e0f80d8420120420010b0300451750607d41d20000300c9031a266080441f040f864081e11042c0380c1c2159200003482c034140300c52900300041d61030080c000c0503481c43c1da4031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 99685287 1250 99684037 99684041
    0x90402041d031207120509070302011206030b0c0d050606310305010507020708100b030303150a0b0f0309150708130309091418030903210d02040e090c011d090919051f 73
    0x41d07c8401c0e64112160501c01580a01074a543c5008a1840015000c1e220b0f0398041d04000291100185081c002c0740005420341c1c0d9004041d4010300036142c1c6400c11502c0000c103000202405100c56808482645c51800e00310701c490810b009542280080c031942c20100d030060b480303066030b0060087c40e004401240700500154022001c080310b025000307500e16034440030302180007404a4060303940142ca50b400003404c0c95108000e4000c0c5211190308036501d0421495440c505440040340012030700040c2c08006810b500207001c65440150744010489803035143c5811030704d01581e504036030f8289140812001241092440081c0700d0420202c80b40c42894191210964a000384031180341c0c180c3c001c030030a8800c0c1600540703540d030350840120514140203110454100341e0700541c20010b410404482000396041c401c04c0340703900240c1d0a0a05001e844680241c207805103141d00e894030301030b0106001181c0c100500301f080c2c0e108056450390b081150b490780c1c60529120b2590300161241c41017100075500e0700390094 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 99686537 1250 99685287 99685291
    0x708031803031014040b04060602060a05070903020a1203020a060c02070e01051e06160507030605040303140702030a030902030705040c020606010f080105010e1302070605010303082202090402041d0312071205 91
    0x84a030880c00d6142004e040d030a00750a0714900d8025403914070356015034459000d02406000c454001c2d08851901620311011224006c0c010780c204103010310204007507101d14521400b41e03028910700f442070f80c1150400303078070302050365000600711807503d4001c0b8495035012480405641580e651044266a82c5d02000380d1000c0c003d50a8511048011740e880e10741c0303403c1d0000c3c00010400f11581a590b03c251b1035984c101040355000383d80154031201080105030741845064402d280f007483d0041982400ca6000b5982d01074041c0c0d40c800d0590b10000c00040d541c003004140020f240081090184180003c0000c1d00d035101a2000c1d0b010034070140345001c2c0e150091414030705a9806a50300071443e0800d03030410402d00594404004142c1d820003008020403824040c29010f140031391104912814a5080744407003254800400785400090001040140d41c0c0561032500150126070105500c14a400d2079030700304580100404080c480081c80c119000128030080c3e108141d241ca400000781e8030040800191201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 99687787 1250 99686537 99686551
    0x9060106020d1e0e031203010801021b150103031d0613030308060904110d032105150105070203032a0f150f070503070c030e0a090609060b07030c110d08070803180303 73
    0xc5460100b681c1d04c110600503490100801700c07861341c0088006040341d40c2c000e801c14140c903500001c0418501c0003019203404850320880040080030311080130300000c1841800000e080004242d009e4000e096608000000c03039170000d01060341e400b000c5202e00f0002400d40310442c0800d40d62000100c0a10b49107203014492500010000141d0004070200704640c4c951200c00c0f401d0081a00c4200c9010f1607480035512640303c00400012107060006e501d4040b82030b2010310318100003040081c400103803004016500c84c40540d0749e41402071085104041c41d480211009a1501c3c45240d41c0741c0b40d50a8001503d800c405402034000050381c842220100101e88120349040c04500c00701f0108115511491480c0a194000e2034950740b0748140b42c000854050803030784113503019520b0b40000e1161246a00c181d0780284482d002481c07a080d2130303a4000c1e10300220b81070060f0500d9054042e12410781c0301d00e02d07000c44466200404907504c10b403a1034100303200d0300306440001226201005c850314402d000002c490240718 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 99689037 1250 99687787 99687827
    0x6120b0c040f06140708030103110306010e0705041404140f0406060b0304080703050d0f0507020708100e06130c0509250c0b0a0f060302032e0605010906141209060106020d 75
    0x1c00e03d0029203654403807807010700c00c0880800044021804140245010f1031140c11034206415040d01010701d0184107800802c0380700702d030009014096800c0300444084400c01c0030030706030310070300700340020000e00b211103165a28040002c10081c0c00000c0425407842240716a8040200e075440b400f065400d80001c4034010302c0c20104003c600b011178016406021100c4030070f1800300e103280d45d00352a10180c403002d42d8501c001d40e2141d48103008000060000240e03a5845050411007000c60b0300c0803958030b00014244200c0b807006400000c0c24090032a80240c0940740c040c14090250030004420650a1045096010040740340c0441414061050828640307030380c1c10420405698941d0800a001049400f05032144142c1e07540300000180c07401e101d41040c2201302d0045d00d1015041428501003030740c6000b03803031014a1a01c00d003030106a80000c025010707281185000400d020141d003c039001c5104052040e100240340c1801c00c4000a00002c2d0241603404960990b446c2007090541540d085502c1c44408032840 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 99690287 1250 99689037 99689039
    0xa1b0c08040302090402040e1509011109031213091503030f020309011205060d1a0a051006090306050a0e01181403070b130507030f030207090b06030106020a0b0a0f06120b0c040f 78
    0x490800103c4e60031a000500000700381c0c0b220b0040f94600003111768820340e00c40d180e1007007201b0342c0020310842040350502c043e454981400c0800107911410a06190001801c01003007101002c000c0000e85d2000c0c1000810820800f1a0a4560004900507100450010700d50807481505584003200b51282081c043c2c4807050f8410251006d6401741000815031900410010b8100e000714100f07034006c0303c1240248116900130b040c20072100099480013441c40900f00c00c020810410383d40e00040d45402c4a0300140c0c005129101c2c110000080c1550f14000b446a40c200090040040f124451038000140309202e490360b040400000c154880c0202440a01449102c40c0060b01d441c0d41e5085680c8011b10423001e45112948030f0356040a4205503400c140e00517400b41c0420b019034030a41c07081c04403807001120040d00715032411034025502d1520390b80082071104403001242000c042c40c0c000030754001403280b00b030141d2516002800603180d407804064a04a00c00701c0414124160601250309899881e5010b8900d2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 99691537 1250 99690287 99690289
    0x507051f0f1e050d06050604030317070e0d080306040c030b030c0402070206190c060501050904020d14010b060d0e010510080c060a0512010320040c020d030c0203040803030a1b0c08040302 82
    0x2041c0c100c1d400000340100c0107500d9a440038000001c02c00706480c3c1c0c643c03648401c11407820034100e504603004240074110801040c030100760010304460243e8410540595203585010301100c60390491440c0980145c180f0050350f00f000742403c040e40c800d502c150340c100320700c01e91004102c0540311005031003a0541c1180c490f8108504145d0004d010150001e001640740000281c2504d001e4003101c0400c4000402250f4030100b00a01c07401203500401e002c4402542a0402e41c0004031003080045000748224614646030608000c20341122000e410000c0c04140c541075030010b10301c0a01400a0401029460940000c0400d5503000c5454141c80143d4000c000c1c101194013840010f5120707403000720500c0001c1c08082a40c102d80001c1c0e90103584a00c0c445080b19801c02141080402501d140c68415820030030010809940041c140200251628010802a400e80b1003039085119a8002c826640000010000507041507040204403864006000c0300e684c02c0e5402c12290403581c07a40007042200200810409 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 99692787 1250 99691537 99691547
    0x10606030603050118200a0e0f190c08010e0a090b010303020105061c0809010f050408030705030702270f070302090306161b0b010303200109060e060a060b120a15060306030507051f 79
    0xe08a00640251f00b0183c41d0710601e0300b603400440d10312086001c08402c00044ad50700250888040368807810500c140741c11a18080c2c14072205000708a154862280010001c07002c50b00000001504010710000345d58403030500a0203020220303082070090002e00f211881036120304005400d04d5400a122a0901c100c1400445071140f0320410748081210600c004113800000780010001c2c0b503c10002541c0d034200e10b105004004c0300c55408400303600954000c4001e0300e000300c44403c0c3d201045031512450360ba01c84000342d0083c0100c40b6280e4240c880c100400010304083c0180106010141c0c07a01820000494119011a08403010051035044950010000a4020383c8001d40313880a10107070700e02040c4410300b96400c444e040c000c15105540c4400c07002000d003400303101c040e401098500f424071015090000f20b00251047c1c0e40d400c0f004070074000c000303060680d00f5444002030200c003041141402e5599607006000d09180d00042d105402540d100091503c0c12070f0340c1d50000325030b40c43c160b04010035864069032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 99694037 1250 99692787 99692843
    0xa030609030201060e15100e0607020f1c060603051207020d08030a06170d11060601210b0a0e090c060a090e0403020a0c3c0e0c0c010606030603050118 66
    0x4155074844c003002c40d05022080e203592148155001c0d03101c0c1307080128200076105450004c200103006840e101c8071850f450b250200d490554050326200000a01c5402041d029000b40d0341e446001c5071441d00880030072025030000b0048038010002c9032032100100302d80e03150b1391280c15002580080100c0302400010503080203994001e0414800050382030fa40c800d0b190548120005c6c15580c0d400c40b144a084440d000181c01002c44500f000404040c6041d900181c03041030428521094400d1490a010060009401580c15000081c05011105035a407007801c60b46001a9072001c00d0b4080d640c000c1e00541040d0341511120046545c8601a861802c518046000e40c043d100744c0450003054070210125030030105040c02041c41640e241c6010850942c000300740340302c645c00f071414101203215044107400f40030f41d810190f400f540600e0b5016143c001d24540d69104600c444020341d400c1040010b02031780c0650050040302d0058000707202101016003003d00841c6491001800341e1040d031004481c0103c0c1c03d005213 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 99695287 1250 99694037 99694043
    0x22060c021c170a0210050405031b1e0705030d02120d0b04180818030a08041e0801141e06030d0f020102070206070506070f02030c0309040f1103040302011d0c0a030609 73
    0xc009401c06403a050081d11000b181c4005050340060301c48a070560401458060380c03041e150402c1903062655540ea128070550080441e581003040100403019010300c0180da05101158200046e82c0340c080d1070355142c45042c8203c901c03074020065034411040c00803420340c0e540c0340c21043c80e901e080c050b10318200c000d08003200c010f84c00994911004484001c4070140c1040030740148001501c8950300c1c55038048110b00c007600a07011740c000401c0a0b00040c0258181c40c01d507464003a50100f100308650107040007000a50101400750f08210360b24a100303203c00001c9005014401600380500d5a401c1d01d1050a681900c07002e402d03034082c00408401030700c5410110001c1c482403001602e40169500011196041a07a06581c95000801800741c0c640d0005000e444100e00c50002d90704192034110101c0d1207000755444240595240d4041c82e90f1598103510820300302c80c020700d9190b00e0382000d0800074000e10090680380440b180e4070748030041e0101c000070b821140078030080104105a0465641b8030281c0301400c0c0403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 99696537 1250 99695287 99695329
    0x30303090309090c210204120b090a0c09020d0c090803090907032c0f1507030b0109091410140f04020d0f050108030c060c04060e010c020316060522060c02 68
    0x40740f450007034081c000d01500c095440d40c03c901086465000302c00c20310f140040e4840d20401003041650b0400b005030030a81c0d0820303002040d0b43d6405007682d060080c41d050007019a10181070100e9040310941c081d28070001802001c10410b50384e41016503c6502d2401240c050b58000c2c070421140c1c0c0360010b940c0740d00c81c0750b40c58013080d80040602400350b40300700580b4140701003040c00800d03004c2a0081040701811031018004040306201c14450011100c4040c1000c401c164484046007142d03401540b103c001003031001c0d8100402101840d98801041c801c0d24060341709a00e8590000d1070640807900c00800302d030001e00c060181904c01e000c020003548400d4405001580710840c50460414610a2a00901602c000b5540c3c44040640351030078440c00034000c500c0c4c0c1c04180004d200450f4411981b004a003801c2c00c1404d20140207000091a00201d50602c8035015280540450301c2039002015200304d0010036800010020444210785080019008003030018403454407640140ca40f600440380d80d500d5400c99 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 99697787 1250 99696537 99696539
    0x121b01060504110408123408160302060609040b0109020c0703122a1101050c010f05040309060f02030c10110d09050105070e060315133e0a0801030303090309 69
    0x42001e6482800c0c800401d00004942008a0ba40c148905410082c106001a00c2e00055192101c440c16003205144c7c0000c40f55a00c0c03140741d41c440c1c900090207036042409a41c40782c3c0c1801030341c0f4144083c0b0204800601410000c81c1c0705040006808c0e010b20350101c000c070300750303820607a00100070341003801102e02c10700c0740c00c100002184441c01001ca82d05502d0351820707605540c00c4034000c1c00d40304d2120140480743c0c10084a5011944411240c0615002480d150782d45802010f80b55024284d495001485145442e0a020030960030801c860100c683e50345511140a40c429000d90301ca004440e075681d89608003262842980e9800c0e0300c03580207810000c06150034848040c08820868080b0760701128079130b5558051250164004003607000c1c0031411991940345280044400306800108a0040e00550100d20181c220b946150080d1070740d44504100580280e00300e040d400c48031008446502d00d49489240306940c004080400c503403c55029880d408110792856a04400400290704143c0421a519030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 99699037 1250 99697787 99697789
    0x912130e13110a0b0f0d1d0a05010f020a02030301170f0d09050301050a0c02030a030f0209041a0f040501050a1208040b030708180309030a02010e040912021b03121b010605 75
    0x5800d00030001d0346070350003000165240804121241c020800c0c842c0390040c10400080d120001292080000c0b01030b5252107403101c0c000c1d0800b400e26860300c80402c0c0c944120f001400c507400251520414002c0d4001e016a260800b031001c105d1048602c0340005800420041c04001c00c0d086070340d400c1d035105400300c406042404aa9030b041401c000907020000e40e8005041103c1d02d000d026454005041c41401c00c400e481045006c0c3d0f0b6031250180e040103041d242c624091540c0010307410f0380d034100d0f03000c0c20a0200c02c40b01c03000f07135904600000030396216800303401c032181031424140b288070b0599001130921402141030100100b510021102f04443e0100100f001042c25020403000d03602401d01915506814141040c08809a03030381808100c907154000d00440303149550014081c501540c080c01d10f440a100c3d07280104014180350308002c4d000c00000b41060100550008052602540380e10a8095042643c010903844990f2a40c42214021042c0141941400300d6840310310382c080d03c000000b83c4140e03124 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 99700287 1250 99699037 99699059
    0x201150f050409020a1a0d0c090b03150f030706020a0611180909160303030506090601030905071719030507020108090109080306011407050703051606090b1608040308070b1b03091213 80
    0x190340206e1000e404250780522641e40d00407810624914180348a01504080c100189400001c066060410101044a10039216007040703c40c50400981070703908050b1941c40183d17440d41e2180045507428541803044480d44080b6098413042104686d0300100401c02d0400c002e000503014180301e4441c041c0180c1582d0100801e04403800a62280d20042141d00e080c004200090000610060600d420155074100245000c2113820903500c814501c4650b41c4003085406103000c0c0c40565110f0380d240307400c2c100e1080c5900030000e0700781180300366a03411031565107400d00c9080c1c880840340245a18030030b0000c9080341d0302801285000020480320342c1d080060030b842d003500c1c00300240d0055600e5003017180d84184014600c80c050020700554140701c0d604a1820300802614800d001400c0f501c0312640404d2410084000f003200e00450704030052580710300b090300340860701d08400c2c1c51010302641240709442070618000d00340e91040c415074019040c0f030b004504042c08540d00410b0f400741c9850a404010958400340 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 99701537 1250 99700287 99700319
    0x100b01090b03040c030606080a230c120313050303040602060708060d0b071119020a0e0c0403120e0301060e04120c0c0f0b0d0501080f0601090c030216030201020a0201150f050409020a 80
    0x101a07103282c0724598184001121f01c180c00200041d04004818030110304010050009200444154040d042412052600f03084203038002d9079100501c00c504a071042d1000001e844981200d00c80d610107603595004260703891090340b06010242c0c014100184000e4019202e66511107400b8146080c0024503542d06070401c202102c460002c16900d20041744a00d20800020030a4040c00060440300d0320b194001405003421032140d14502c81581d40010044800d0009850045074080c00103030010385d086802030040140c8201881c000c3d8030f403640005a030b180c40708640d4000d5030028000360a1403800d2008030b800f480c54180c00d484501c200d09000440c542e4940c52a0000c0500920080d1144a00f0481d14141d0310103a00c1881503601400301004207c101188041c1140d00b0b4040c00942d5030080a001d50203030107580c950300240c400e0240300005154064000381840812a402042120011011102c0f075070094081c600542d03c41c02c00c00c1c00641401e52201d103141e4001402c601209550b040112051880c3e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 99702787 1250 99701537 99701543
    0x6040305031201061107030f050c0306010e091c1d01090e0a060501030f0501060504060f09080d080403021c02030d0b040f020f09120c06070f060b12032703100b01090b0304 75
    0x82d0044489480d0b211240940640d1070302e1009244180c0b1800d41da442a4003010b410313590000442410003008100b001100f02e409419140c8541c3c0d6002501001036040b1542016801800c0c0b0304407601280b511a903500d0f2800362070f040902450216035600b41c2e154110b04605001345184046031240b03200704500d101d0b41020324040388940c2468001001d607540303911a507004030305210040c00441c1e009001d60f01543c1c600c3c039109004042c90076048418145540c00403c42c0e00440850b100c0703055002660a106031b0080d000c80354029a0306151071918103540301c075180141c005010141c9000c4280d04100f8000000900119004502c2d03900c44089a10024408003503110016a0300383c10b00b05004003884090002024020076414200441c1c140c1c480d044009201048801212080100990001c203003c40040c103e0042c019440d51242d0380c95110002045000c25000d5140c8803c81d2581c54825049001502411705010102415405410000742c1f10b03050080c0c606010404440c0032016500c102c0c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 99704037 1250 99702787 99702793
    0x5010f060f14060a0909090b0402010f0f020a1e0c08010905011404121419080601080a090c0902130b0f071e021806060c1f06060903030f08130206040305 67
    0x10006002412104141d10400d0564865201000024502e2840c401c0800040d1a401d9840001e903070f04a5004000390010f08205207408152024032080740e002a210358801c0c0c0702c844400d80012010346401c1c40011149005902c41e2220301c00069031488040e03c444002441c1c46102c900b01e51315103000c040103030040c0140b6951540c03100c082c82024044d110911401c03134501c00300c50406481d0701013450b02c07410f2683d007400040f9048518002d000011640d5044000c03628417039001c401038000b4204441a02c4041c00900010040780002125120f42d01c5500d5100c614460003506d4280a00040e410184030607504140d6400002280e0600f600101449609040003e0b60750130a4502010200d1580c001108481128485000141c030b0719500b00c01d0592031018441c0b03450380d862001494912400d00c0107902d5014605240507000380d400d0000c0d11040c00c8150070310541d501c0c3e41040700e044000c1c0c4030240c0001c881110140000340113584050304000e00300760290282c210360700416096030290380304072000d074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 99705287 1250 99704037 99704051
    0x3030f2106010908070905040f02040c050a1103040506041205030408010e030c06010b0f0708070606151d04020c0c01270608010801050702010b01020d0f02010b0a032111060f0915040501 81
    0x903a140d80964000d00900388200240d0a1800e21aa16a00c40c011034000941d6080464140006190301c17081c26503006000303102d03103064002d008100b6008510005c02140b40d0010000b00c12102000f910199200503048a050078607045140b1418040400150307402d000420010440c80000e016010740203c98030011075440c1c24540100d4900b2005a2000c240f5030001c0c8651040c00e0302190071101e4090f04810702603121130781800e14200424595100310601841055403281072500140c640060307041e000904e4035000c030182d0074070042e40306001e010049030700000e0421540f0740c00b038961107254a10040c6e140307842108090198131620459003210001c1500040100810342007401102d41c0310b0301e1480280000350744000040d650301d284403035040901440f07500a0410510135400080584001400710001035920f003001d00403d840401c8650302501c032185000b6803a80125401d0305000c5040340100150340d120119115840741c043c22904181c007440410902c49491075007094042c1e805400001081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 99706537 1250 99705287 99705337
    0x903030a080610090f060809031207080109110c0a02270f040b0105010e01020606090a0f020f0915031005130b03010c020d03180503030c090109080304080a122c03030f 73
    0x22810f4005510100000d0345820720a2080c480b01e58001c459440c144410543c81d40302849007103001e28251000441f00e418100040c50348d2090740c241c100c030303050542004001840d0340f00c00000d1113042d00b94041688400c03501c1005080c070b050310b02c880b5138648082c445ca035000a104007000d102c0694000917404020000c0c00305111800040c00d00601090070109141104180080e4807090010b000d984503041c0c4800042c02c04040381c00003002002540b4003159640f4040c4425482500103511082c020400a8400c0c81c02103004012607010b0000344481c0301d401d070b2a120400070040076002d0f00c2100d25403a13882034140c4d41c03024000c100c10181d4a40140040c0c01020300001c044880b008049191180e01040a00107d0000300441e50071641e40120310340d40303125440050301e121103503500ca204913110001d400070707010310007003080d0341028420b02c400440d08499410880380d2844064412101d0f00d051075481040c0d03005d4a195100049010701540c1c20a09100b84030003550300400c1405101500c034081d001c4003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 99707787 1250 99706537 99706549
    0x100f0609030c05090f040209090c030f03130e01381602040c05180103051f03030f030506091b0306040b091819050d0807050f1b0c0406032004020903030a0806 69
    0x181c40c09844400c020324010715038860305d072000b0300701034007942d09000401c2144c00203012000c03100b44c01030104c2e151403618038a4156030303510507a003824400d000a040172611200d2010307014100d80b104031081d00c4542e40701c80d90040c031210024414102c007007203546000080b040d0070040c01001c0358001201a800d05030340148429075011160040401004002445400c6c203010342c1003151007000e20b0f0005035aa617504907030b40307450b140c3c0107000d23020b56940c03000004240d800821400d80e4a980d0b54180505c0d242c240070b201d11010191102e4903142d084800b4104484a907901a550000d8005c0002c94180c00c800c010a0740300302e040d01c20400681c01101d80d80d81118040025511302002480d4441c06240c254540a40300c48026121408105412000c1514179110f0800c0da03092043c80c0c0c46240e501c4162440c0b085003803021800404285c0140f00e501d140c145003510860301285e8000c4141c4881032236803002003000c1046000303041e61055017031102070b0041e1400c001a004054480e03c0c3e40d44103041072410444 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 99709037 1250 99707787 99707789
    0x20711010201090b07030e0a060501090203100f0e0601260a1a06070b04020409081c150803090a0e09070803070f111203090d03031b0314130804050603100f0609030c 72
    0x3040d607052560f1100002c030142202580305080d0314000680307401c8441d481e4180300c181ca030048d04450030036001241e008007960080d4002e00c3c03218200131b100c030395030303514201540b04a10038200e06140070000a19594040e0000c0340860840300700c0070a45682d44004011082c41c2561262402981c0360746040180d0100e0343e4812034800125092420020702c0d588203d01d4500080c8024000e80d00c500444d000c0240300c1058078460001032903120604c1010a007200000c081c884d03990380d05000041d00000740e207000802150304a020241c0a1803484d41080d010a50900010f815501c4912807400005081e04050001d413103224801c10b80a280302001b42000d01d810301146600c90320030703030041050780040c400000440740314400071f0390040c004c510b0700e0500717600801c602040800100440a034107900158554040c103207100d0100301400403501d03144c48a040241501c0300040140c10100300c00e2205151802c045c55002e003110180410540e1241c0180c6101c003420741c0440c020030724000051040040c0b11501344 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 99710287 1250 99709037 99709039
    0x2010807020c030a110f09071701120b060915030d02100e0d09120204140a050402010f0503100e04020607050d050d0c030902180417130806060d1112010207050709020711 74
    0x1000c0b126900c1c000a46404c00c42e4801424030066403d0044562600004505903480c010158503031751810100107004a180c000205003190410400414a0700384081050451604a400d44089070740707040c2844803000000c1c0000049540041c604007030703590208609501003020f40d002c0c2182c0403810b03200e0400d48184240041c000e40160a140d60342550101441c011201c0c019416068011280082401015036000c60034001d83d03170002308181140300340c0249025038401c0e607540710164101c0c0411a0a8001520482c0780d082035000100590104811401c0d0070500060251f403402009940e85440c2c59120845040030400100c0c1700e034080b05040c4110a06c455981c01d040c800e00b041c50340045d107100d48a001c900400a0100045014088406c1c1c2888030f0074410801d050380c81c034800500100c0c01d00b05126490b0f00d8460300c4005011402d00120000d51140d01840300100b4800c00010000d6030755914240005a65081c480c0350003003042084990020030603401c0040e5074201d64206040f00c5441c00b2911 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 99711537 1250 99710287 99710293
    0x50c07120201210b060d02040618050906060a020c10171e0103061d070602010608071d04030c05030706060e010302010f03020c070623040e0f1f06030b060c0a0f0201080702 75
    0x42000d41d030000518044030380c001c01c0005026003d4101a8018070050002c141c10a00c007141b07842c100b0710720754014412780380c49071100d50a610550b072401440e054140100c40d080107451000c1481420248040d10040c150b5005444000d404030012411660741e505100c00024080c4810121046000d0700da103401c034241c1c445000354210310840309032810038103220043c03a2075503d0440030403c202d00150500034045880075181c5165555000902030301745030107205058040c3c42d80c00a040301c818020f1059481080e000c28049507103e48081d038010f0b041220a54060104000a800180c01d500c030302e00c0580710456030b58150754114000144005100d00c408424944104030302018500d002800800700d030702c2c1740791645410034032007001518842e885440c555045404200414249000b10000348141c9203440d0200c019542c90085010380c500800d5603c0300c0303c4408400f80300e803a1080d0400c29850b44040d04040c5030082842e462443d1011084e030950380e044040168000310341e0301c50301c07550f0442041e02c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 99712787 1250 99711537 99711569
    0xb1f0504050d08090f10050f0703030e030304060c090902090109090b01050702060c0f0111031515040503030c070e0a0204050a0608040c03020d061d0105061005030417040807031202030a080a020306040f0606050c07 93
    0x47c201d48580151136100b00c0703012a8050030188250401c8500301000380581e80c40303051a1401c0400303010064a02c3d808114100800700721503c4078800c3d03500c4a80142e40d03800120785030040c3c8030000d00e0107420260421800b04094809621148002e04140300300c00024207402d0011040242180c4850200048000c801c100780011446034924000e1043c1c1c1c1214a05110001106041814455540308540500001c00d08008030303040462620102e51829404a403a5990b88061004034880d50040580c020799650090240b1807188508942c00351186000c034811a807680c00048010b221100d0485440d030b21034460103200d100d00d0717051480301c4030640d000340001d0414400203035003e60718207944400c01c40e02000003000e2000440025041450911106036038948803865107071100c1040c0002c1d2461100603a80e01c40c164400800c48030900c01c107a0b201001600c035040c02d94040e60014040d5540192111412580e0007014451070008080544880399150b1040407180c0c2085004d0340a8400c941c42418 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 99714037 1250 99712787 99712819
    0x1060506120612150a090515010b0403081c11190804150b130c0207050a120302120901030f240503010207020904060c050d06030b04020111010b1f0504050d08090f 71
    0x851242c200800b03d41808001d102c020050b8a411002d00241311541303248802c0c0322440320f41d40d1102e118240a0030a51301c00e104001d140040f445001e01c20403917210b000f00700410101c2e00c04000381408030607000e80c4880c40e204c1080300001742d91203401e00c0d14800740d0029241004103254000501d91200c80d0030031402c1840c01da01e078010490a40442c0d1114151102d420100c075545503000600c030210018004c0010040d02c0200940d2040c075405868060194000d0100f054401e8008041000354181c1c010120102103038111032280c2c01101c10281030540700d00703d6101102c0e19003e44410010242c030080e04510750781a4810307010307505501850007079104101c0f590240c0c48803280c1a6105130040008a156004107904a9a5104851504c005140740c0040413007004a4682618003880c003da0351044807142605140d07080b115101c442c0c070303032160340c00910300500c01d0a002059030481c130b1030908a0800d40c0d10070204020b000c0041080750b01c4100010a54a249401d0481b12085a410340b02b41d070411410079 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 99715287 1250 99714037 99714067
    0xb01030c020703290a090b060d1e1109150f012109170f03090c040614011101060b1b0d0203031e0c19030b030c010201150302040e100903020a030201060506 68
    0xb00002d8480100c4519840c14540500b10302862103268039081c4c40310b880d00c0d20701a8000d0413481c50031030f03042d056000030440c14a0014540c8101d40d07085070603110240c503801c048982084440608413000c1046070600d4641741d49a03070b8118881c4e030741d40600b051403510010411019040104040e810300c40c40d4400b408494500744100f0164181c0b84400050300c0c03105080ca409a04410035030940803850000305603800200c00e002440c02003004000f2524030480c41d00401007a40c106000e08007004010340701010040d0310884460454864107400020027070303119403c0c208a50700160668400014440c88460f04000800c480c00d483c4074240301031821070601d030810f9000d081130081c0030200ca4550101141e4400d425104690400b040c20b00640c0400400c410302401800c940034009100c1d0051200c10117065006004000b52144800b00050245007160308220080140001c0a24144140c0c048842808a24420b40307680701d000750001d0000140514000703095079941d410060040200f8001051840202 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 99716537 1250 99715287 99715289
    0x501080c0a080a06031707060f02030f06010507150509010603030e030106030b0c0a090806070f030506040c0806040c0e0904030905030607170601140c06040804051509030303040f031e0f030b01030c0207 88
    0x1407515900d40c0d22501d0b820380c054901a000074000a60340300d1b6506000c4008002021010720440052083d0750103040c00c4812800704072000c2a0003184c07100020b0b100c2d84680010920548035980203414501c45105800880f103084a2800c00342e950707030a0510074150000e05030705001d94101c0081c80454210303514484140406403080088000109540b00424001c55114000c2d0158408031609840c000340c00900c6800c0c20820100443d203440040340d103a0900c1d01071090030b15450b465403403290711220144801018003400d00780c2001600c40c002c850030754510a03550b01543c000d07600c0740401402c100030035050041c00b5140e034040c41340400a801d40000010f0301d02d9840b8409080c1041c00c00c0c140b04075502c25101d0b20540b0403140c095001000100a102006017048e21001ea50240c014907503140c66252070304c0341f40c03010b075455401480000c000810070321029107400d200b03141c0403032055006a20281d211000d00075540c042682034691140e920f0707040c0705401c01003a09107018404401044c0c8080d44a07d69 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 99717787 1250 99716537 99716557
    0x100e0d030b03070e070e0a120b060108071103030c0307020c010903030c02060a050c010f05160512060909010608030a0f030f230411030d0302070203060906010b0d0b0f12060901060501080c 82
    0x4900652280d40d82c103108140042840484101d000e02d040040100a03981c0c004010307200700208070700031402d502c0c003c9a103000b40f58400313021665501c1d1a00155611000100100c003006000000c504400000780040c600507510410b045480c0d00745484042d040c481d0030101141007080f22241000442d5110f1806550b5940545e007503079851402ea40b0032a418440e00004112542c24160a143c00c07d00340e5100034491301c0c1c018407400e0041e14800c0c00b140c0300d00c501419019012403c3c00411803614000c0229504444080d0001a2060780c481c00f990450704903640c1c0401091882c903403107542e07a07094000c40c8803072420441c00b0000c0d05001000c003940d404c8211001034228900100040c100115026000c0c1980b00003012941c1451440d90028040e43c040d08c0202d00074051000031901003a40011100c1c1030350000b0000740d040000c4c4030321140003045000c550f15480405058000450b031114100740410301c0d150300141180e0b142890034a0700b5505594004c40c10484004100150b401010060b1041340034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 99719037 1250 99717787 99717791
    0x601030b06070620041e0e07050f0f04030204060b0d0608010501060903080319051807080606010207030201050d291804080a050a0e060408010c080c040f030b041b08030408100e0d03 79
    0x2d160081300458544000035218000010f000c00d101206060412210529050650031180c031013550705000c1c5c0c410303102c050100b08280188007031110600040c014805040c0003140c241a0360f900020706843c1ea90380640764550002403202141d0f4590300a0402403c50039009001d51351500f900108a4801880013401c40080403020540791680203d42802d1403585038001d01450a200102c10f10309800f1f4071100143d4030880c08001801d59000c070710244104816006013880c41d140d6001540c481e8445030404903250b5403403098031a0f40300b030075050100059404410401584945090050014250341e104d030102400c0c2c0104000a4074410032500d05524030b00c3c1150f2181c44030b890a4404000c045e4515a0111001c9808181e00707074150b001d40648002707aa03030030610b41c450026103103084c802c900030082800001c800034400f0450a4084503009403181050380301c01d1030040b0050058100c5038000280d25000002c0400c05000100400c2c51903075070346442040b44c42d10025030243c1e600d03003064030700d01416 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 99720287 1250 99719037 99719051
    0x603060112060305010c02010f0e0c12150f0601030c0e0f041d06040803061813030302211906091401090905011410030201140403020d030311090a0305030408060601030b060706 77
    0x80d126400e11501c07440d04800c20700c00c640e180e140043c080d1034030402c164010348c038250901c520011306010700120f11080c0005000ca211100d428400000617071103480398a0300c100300010000b504041501849075035100c40c4e2040d94107140e000101a912502d00900400c90200004031442c0d4406103a446141405c403000100140001c0ca4161480c0800140400e80d000d02c50400c0107100c28035001310720840c0100c4c0e420303844030241d0300c0540e40000c064903910f49042c003080b800703000280258024034182d01c6020038039501080460708891140c900b12401e804100714012561042d1103180501c00c050714004406001d5841071045c620b00303850051050707644280d11102110103001c170a50156642d210190440200e45c07808480044143c0d0091100302d00140c200030011150002c0f80081d01d0a07a5801400d9040109064404801a120814000c5001d5008011800d0155260080d18005500c0b400155840c1c81c580095582044001000e540c1410b0030f200b100d4003645d40d1082102c100d2507108000060711 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 99721537 1250 99720287 99720289
    0x6010b0c0606220603081c0528060314030a02060121021302040306090b01030b01050315130c0509010f080c04200c0709020708030613090302060610110717060a0c05030105060306 78
    0x500481d1150900c0c0d113084400310030702a44100421090940041e0640c2c0c408203058480f0803520101d4800718401807842c3c0d0780c02415034042c1002c2d40081e901d031004c84e0721912600d0b0328030f18070000c0d40c6031605030f40b0000c2c0ea15042c1390144041e0740180400ea81d1001c17044490000541c20a40c4103000a102c2c10382095808224100756059602840c3c105000300065001c501c0c0440781240c0a0105031490070590f00005600c0c900005d00050354009060798064039224036110301d00c03085015100f200d9040c0010400316940d154a4074440c003c0000c1075820005629091486040a420b01102e5001d0ba0030b00a01030680b150700d42100640d01d01840d2000c0c0e40b20354005415041042c240c200201d10780c000944803040c8000349014600840b070485d0f001491801902c00e10044a10241e001409600b0030b41c0050514a040301c0e03507011050150a001c009110714a1442f4181045900f0420001d81801c24400307025108002599000c801082d04010b1b840811030b019100340014441e01784120390003c002442 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 99722787 1250 99721537 99721579
    0x807110708330702010c1e05040e0c070f050c0a05010201200f0f0406030912020a03090e0604020408120c070501020d08040809060d0903080712060e06060a030b12060105010206010b0c0606 82
    0x2400c00b01c9090ba030071400c200000030b019042070020000010403610007410b043e03541c806841400400c6803500b034074203440c0c040c05040340100100507280e15041840348001040340211980c000510070800382c61440801c404008100752180c1090341103a151540c800c140c08416820342c8600240399684a45814205941c2c0d01d2601c11000324080390313180890002402c070b030590010005684242ca81014080c4011001c81c0d54011203403014001842100c0d0401a8a1400200a0300400e015202628060300c400c049131815070b803440c451504990004200e040105d051041d10050701007440505100000300e04010000720010f44094800f1a000460151950b200c2c0100c03112600c20510a000c6103d1500700a091030400700c840e08089220584000040c10913881643c4c180e441e01044003545454440620920380c00140084c0141903035001e4080e0a51f9481891310b01585070240103002c0c1c0d6040c1000207081200c113078041501d07900300303000d1f0b110b0241e808515254000001d41d50040d1041082c0c6a400b9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 99724037 1250 99722787 99722863
    0xb0f06160c060509011412130602040902121501050403020303030712090c0b0a020c2b050307020604030f030e060f160f0b01080d0e060c06160302040905070807110708 73
    0x204251540300d0014505030444044c1900280989400c0d040e10b40a1011410314401e40c20f0f164003155814001506055104241c2e85c1d60340c1c0940401410940c07124040d038200e07484800d81c0c4400c40304840c100156802c50740b1581402070000e10b03207542014034550100c2d07680d00007d0518000e204074603440c81d01d40000d580c82502d01c56041803001081d42d50f5005d000040c1d07408000c155006014031880c103102401c100301d0600340f048062078150860000f01100001d01c00780d221045581c3c1c00100912005607451101038006107001e5410b22107072030364910300500016008403c1d14050781080c08065003a15100c0180e5514114010342240d021200d071411000005405800a02d58807420001041050340040c1150080301180c03500210100034204220407801440c80900c2558401c00c0007400c40c401403900346403400300760b080c09424141c17510214801d44004885200c0091a204200700b061640215184020725288019000366030170507020580301c0c940c440480c046080d41802c1d440c003503520103100f60 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 99725287 1250 99724037 99724043
    0x151704080705010903050901120e07230d111206060603040b040807060f050106031104050a06030e030d1121060a050402031305061806180c0d0f0206130e01090b0f0616 73
    0x100e80c4a59117070243c0f02d60028034480e40065901840d031004503540d81700d16100c144a560040844903e09810003800d40c82c0e02084071400406045c1710b07410360703c41503421403d041c41b41005100c190700c45000d00c5602540c003910070352654080000e01c0143d8841d0070480e0780181c2c20103840e2403242d0719403c00302e03441d104d01c8200a140074900b00b844481410749902c224141d501a075014401c4001c80320305182c0d41d0095006895202081103400c11400c0e000780d1100c2c0090f030004042d00e00b0810108241d03001c40c1c0c0c48045581d0407880004500811600c041d140d03922400709410121814104440410b2090010703000b0180034603030000208200260311011002640d5001e411910700d8909020348841050f022584500988211404119000c0004010124482c0c1f06801400013610130010030503010002017041d00c81010f40c281413001f5071181001000c10313010210110081626024001d01e003540141d001108030762400b4030004c11962040640484803504607450368030391141412100405800400003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 99726537 1250 99725287 99725291
    0xc08040519050906060915160f0c0815090d12060b131505030c030f06060d0204030308090c0402211504020a0801090b060307080601120f020318010615170408070501 72
    0x60700950144030030394042d80e40c10740321450940c8800083c4a2103000d4140700039800351040081415406400f80a00395400c0c0d0310f807000741c4160341078455070500c04902100341c0f95810b04c00c90901000030100403400380321080c14201e817502e15040c065980c4802c445001202040301032203502c00b1041d500e400890141c0845594150b503900c0c45201c1126034a0f2030b00c41c9058420700310350343d41d4401e40500c0a4074400c091070f062035851591261141e4140040041c1b04a81c4048107000382e2201c20814800f800c00341d4401c0d10340c0c14003400e04902c0c1034a05081700303910a100c0c50040001800844072182400480000c441d083e4079030352601d540959640401000d0703550450f2020a5501c803c0754003601c2581216030f502003c00009202509011041c4000c0310f40001240c010b0011503495441a01200c4e02038099010003e26403000b00c52400c140da101341c44032030000a4213a00100b14103420310445004140c913880c401b61511403890003038401039103880c1c014200c40c0f003000000d06101030f2a0468420a51000007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 99727787 1250 99726537 99726559
    0x15030605152709180109050a030518030a02060d200d09030906050705031b03090d03081b18010c030903080f03010609090b01080c090a0f08030c01050916060c080405 72
    0x401c0c1d000350020701d038456403400c070072120100c2a050780c00c80c42030410010f0002440c030f03a40ca403c0070110081c0422485141d66850600c0d8001c20001e0000c90b100c5407117a915a0b41e10304d40144030428860700410104d00c00d0300074600041c01655100200ca40d11100d106c1c02142e031500001210a4910b14010b0031800310b40d000a8207c42010583d00007451113100e03842d0300030250b44440c811105c5022b170550003000c9038000c1003c0000c10202c5110004084880d0b411640703003440007008a659003005150480100d18480c0922106401240729100540f02a42410b82001883c5c8181c1481240b04101c25061110040301081450f2040c04002d001c1c541003c001940c03114100c010001316403003403207002c001415840002c80c8500d400d009880d40010141d45d90140e0303450b25030f4544003552090759920340c00744007403030009648610043d03034500408940c0059034960650032246030035110000c00380011a007205810001401e54981d518081d60218548848035050314949001c4610480c0c0040380e0100040c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 99729037 1250 99727787 99727819
    0x190b031207080a030e0304060f031a060705070501020f010e0703060908130303020601210302030306010806040b0a03030903020306090c100503060409151508011b0507081201030b04050c0a05010915030605 89
    0x14540e03c0781030358040111340c0e41c0b081c1e00d076102d02940c00380c24001a004064081c0740c9210790803922803a880c6414080700281c106c00025425805200e04442e07076040240100055a0144800c56090030410020300c104000c078440c2c0340d240d6829000041c03035a0303500d07244c010500901e20b06031031404031540750a8554035140d04020307581d27030001d120315009007017444042031461403103c0c000702d41c0c181e00d50015800c1d074440c240195100c18000701030035042591a98008426540c00082000a5000b81c481440c020f0650060504007680109a099268016110805a0b1311101020200301134a440c046480e619420b002401403c1c51010140101400c2c4100c403421a0301d5501c04446440600c003c400403aa03242c16150a8411a0303d680c81d0a4122a40c6041c80a003d00c008000203441030055600c0c0c91182a400d11401b2801e0700141c0c0c03640d80b800100010407008103d0921100c0007221402c0106144c0340c0000d012401d18052440789030301c0148002c28103400b94110901a01004100303514003502c5d60 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 99730287 1250 99729037 99729053
    0x190302040c1101240e07110d03020705061003020a0302010518090403200d090603090606030b04050c09130804050d03020a0f1101090f051c03110312011d190b031207 72
    0x1405107019480c0c040e03403038410760044404460313444443e01340f81c045504c1c140e170650940388001d164030b050040604035180880810b01041c01421030319180182c90740a0b41c140203107007010080000444807c914418005a80c807039015100300c3c1c0e0f0900e00702c1d43c1c0b000c62040d0315085484c04025190008201020f0008041c2c101c441401803421486006040d0743d07204240341d03903400458114001054900200384080c52094100080c064020300c008241c00790380b0340e03850540d004125809d4400d90008485001145411a00d05820000307010307000c00316481f181c13510b041c10311680c42568030480201c0d044108150090100e1084140c000c40b08408148450070000047d11040700310600180d42d4050114080556443c140141c907805050307074030500f9028020b10740070340302c9520960a01a0422900800c8030013000100350700d503c030003c7d0f464254541859540110141d10b142d001007490041001203142221003a04440c0301d00751008250418a640464107140e070f814620302504d000010f0050505c0615 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 99731537 1250 99730287 99730307
    0xf0316030c0e0c0703090311031603060209010f1403070f090506030906071206120f0804030503270d0213050a020f0a020c0a060c050604080f0f04090b04200702190302040c 75
    0x6840302ca250b54034a070b0407200d540f15400c401004500d0110092002c150f00c00d10410100e000501100d83c1c00540a1429071640300542c41242ea41d600080c02d1050307560f0151121480001c54100755803480c040284d280014003000740030408001159461514440c46404400018000540495600e0409206042d2500300480c0c102d00400c442100300100035249114a2040302d10040e101d44410350242d80309500d40c03d401c582502c00242c05d00020010560600c02003030f08001c0e4803130081d030380014041c00140039000301001510400034288020b0150301c40800c1c0501c0d20503400300000e483d036903280402000380144004420070903804111102215000a922071107904211013607040e6a903074000882c0d0724200110000d0554000300045000192a60081d00c00321410b01c031142d0a000316190007005a0b0410791107445883d803a05030441d0380d824184507001d401d84000d50111903680c4411024034180c030804d00000c0c06111025007111003000d003116104083c0d07600410a102403401180020030b07400d20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 99732787 1250 99731537 99731549
    0xa050f0c0105100b18012015100b07080d0f0906060605070c12030903020105030403020c040908030402090711030306011b0b0103080909011203080604020a0201091b0f06080103110f0316030c 83
    0x603d103000f08420b0903500c242e400100b03103142c0395803028540b40c1c011034002c00800c0f0b04040041d01c2c100300300e8507150203002802c0502c250fa49901910720748004001c40700441c65018040b090000c0040002180e41002100c0712134240300e00c082580c80b0704196140c0200a0400701601062030b020740170400650140c018003070726006a002803406522076064005400d00a07274010082960000300308015401074024550141c000d006441c0c4c060040004107082c1e80c01c1e10002c40d03002d01c001007000110700c1c001d0309054200819181810310b54452600d00faa907840040c044906101c0000e100d00d401e111800c0400041d01c3d8484100c0d1300c0b659580c0303080b003480d4010707100041c0f154114800108003250401c0340c80a55540558500d8080d44549003407000a51101300c2c03a60841d500c400a61010030404590b10310341c2680450000c402030301e030000182c40c0c00d0281e00141c0420411030010404500c1c0461070340d002480442c1c0c1208400312020010740382100416140e1740c9105203450010030702200c20013403811110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 99734037 1250 99732787 99732811
    0x5030c010e010606180f14060d0c050a1421090a051006030c0e0c040e060d120c0605060f01050f03070216030c080c04090b150406080a0605100e06150a050f0c0105 71
    0x1117408181140c01e117000d00314118211080821100740103002003180024090304140c60540603503801c00a071810446107001050000540028496000036031510010b02d18900a0410901c1e20440d50034400d1a2030016a0064200100304a04400d204c0c244600d5800000c4404034009200c112011344910b100603a5202c000301c00010f68000c0c10300fa060300c01c9049080092400342003107100510003002a140380e4000e098120082c0004da40250b10510081203074440452191080c03030400180c840007030000b4090007008108a0352030747c000007501e80083c800c0c0c2e030039610383d03030b560800320f1402030461000204465a05030000034440036071900c0c402d5030121030940740320b0407680003804107860a101c0f0060545003130078009003480410042d0a40c04400041021500d00d90740c00c5003034035290f40440240c80c050303601e10a100780c1d031580c02242402441000c0707404003146044400180c01c001580542c13002540001903142d4002d21800841d80c4580350340100f10b071201007540c0c0640c0240022242085d8400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 99735287 1250 99734037 99734057
    0x30b0411011e0804030504030212010515061e0d0b090c04060909050c030613150b09090109060b2205090103140c1207090c0212030405060403080a0b0d030c05030c010e010606 76
    0x540b26502c0030b00c1d000b101412840802103040011607041400600a40411000b4400840140c2e13400c80070740a09801440041a24108814050700c01d1021080c0c0030310440e8104101003c00d50840805031407010031131025629014032000710400341c00d45101c2e1aa000040d0701c108101c0402010241050710400e50b03e03140c440d81c0f1015024100c2d4020750350030b0070580080c4006281c510b4218001410b800454001090042045c58800e800410980180095442c040348030505402c1c440c3d6018010003500e078003405250710745840740d2254894501c0c484009802c6810301c010ad450704101c008020040070340340800341d40e564104400d80c06440f50119065020b0100c0748680d034507101c1e0b001e00960001340c01600300300e480c0c0000c020080c0721140208041d805403600e4040031485510103184074502a4015026603c1c091030f0007811600700800101141d4a40800110942c81c2c40c001d0a00b0740d80d060805503140300c140d0412514500036244006419070230100242d41810040d00503008444082c0c40c2c20880c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 99736537 1250 99735287 99735289
    0x406140703090f02090402040f060905010602010e1609050919051b041a220e15060d0c09111c0603030f090503060a050c13060f09050a030209040204051906030b0411 72
    0x62a201c2501400f40c0c1107680b401d078050328101510750781003840104001000c681c1826414295080d942c8201c0c0300d55560380040056a0b02030044191a91081024081c1122131380d40c80100f610b100d00605201c40c0d514000184440e604001250700454080030381d4414011500d0201c3d9900300b10107075044132600d0351010100b1410940601c200316400007105240d40b652240c1404044d00410b0105a0700d0f2051150403181c0000e01c0c401c4200441201020b40880034400088070100390018040601810808a040c404540c80c40040826160f40c3c01000c5264900d41420700c03180d00850300001588007400c4c0c0d91480d004255801302d81200d12070749510107410303210501501c0742c02091241a030590032460000d460f622080d40442e91010090c1215810b002c00c1d5a4040c014811a8116002042d10542100010f91300a80500020102260700703500381e07411a03000c1307242c1160150000b4043d58440020648009200548100da03d125280400005641c0d0134088045d402c255002d9603150000b000d05801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 99737787 1250 99736537 99736541
    0x3070e04030e0f0f0904020f0d08041a0c030f1321060509010506030a38071209120503100b0f0a200613170d06090f0b09060103020f0405090406140703 66
    0x3c16240102000e201803940c1007449030790040100202e80c0030ba441188a1802c2d59020102e50302c01e8044c100050302d440c10502e140c0c0d441c681007044120100000e10808680c07650010031550040c3c450308540b5141c964a103140c82e46070406400c00d2111015400e0307058181c240100315141c0c02ca00400b07040c0326640324001a50f00301d0710251106901500994008400b041480300441580700755690003001038040d880c4915082103a40300c5440e0050312400038088660740c4160178000d400000001001041c40c29552151400c100c003c1c054148840400020520000040114020032400030300565038000307601480c00c1d5500c08d1018601142c00340503a00462150584620070744494000180710a413030303110030011001500c0604456543c420322034140d00490100243c06000105580811040e041c43d11400c240c1d030740390f0320040b035580ca0a03540780d204e544c80c079a06541114003820f0043e614900150200d07143d205d2500030070707008008081404200300107980010040700e00406110000d488000b02201 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 99739037 1250 99737787 99737809
    0xc0516030b0622180c150e090703200c120f07021c050a060209040513050a230a0b0601030506011103030606090103020918180703030801090207080903070e04030e 71
    0x281242000c000358241c1032028031403061070000c00168510f404020790300e03000d031884109442c03e82c0c1007a14100d02000301e65841e0340058004140c0308200580c042400034141050030721800d00c41d4079034002041341213010384d020340d41542d0007400d0440006c001c43d1801045500900c0f440e542c900c40c03d100c0c540015051000e0b0350500064460341840c1420a808011244103160403400c0e2004084409600140c01040f2506185100d40c0d000b5880d00086c100304401c40f20020034041203078042105e40c1001a80106507070485a41c05500059102c512841d1a41841001c40300030030940314a074500403d201d801010503205200903038080c0500d546010044401d030158810200e450b52040c40070548501d4110041c02d003000040c98010f082c11842000508403041b150354105070404070000b401402100f01065504031400440200710b0a0b203036a41c000c0c154541441142c912540c041072040410009134200d440301e140c010304480d50f081d02e0340146060900c095604038085001c07640204440d0802580c14a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 99740287 1250 99739037 99739043
    0x31401020a09050d020a08060a06090501090603030215090c1809010b010903150e01020f03040f0302100b06090f030307050d023d0b0d0605091b040203040c050d0602040e01060c051603 80
    0x180c40500d428140600526000d9089034807500d890340200d00c1f40410081c0f0340c49a140d041c40400c19500c2c1c141641c04903801a00030802c500d05050003440425000584850030780c95803548243c0d2030f43e6030b501180c1809a025000c2d070307104200c0300702e4140c00010f0f0300070789002c2c100310b40003040055030078401542c4a491b01c1c44000e00741c04640780788807140c60050f8042e40341c8480c5840003602c2c1420180c0102003035803040714225625461107101d0b00034964100207031407403261060f404100700c20310000007030640d0084000c072620401c050b85d02c1c44a19181403066a0782c2c5a4480c0454019800e8950080c2d2104600618480003c90003c038401c90990040c5070131a40d0605003859102140204400801401b00511401d800c80f1551102c240010158850309200380003c002070110b0070312040245032020703120b0200341d00c658010300910011481c482c110b102104d00894040c07150800c240f4040c03020340240d82c40b004884401800014180b504a01c0c6000d5080c402c41c11342c0c10002da00c038600c00000354140000307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 99741537 1250 99740287 99740297
    0x5160501081303050c03030106090305010507020d050d0b060405131d0304060c030e030a0c0f14090103150b270414060405120d0b0d110a1505030a09031b0c031401020a 73
    0x42521018440c2d1442c00d15802843c01e14034080a0110ba1883c5600a0740f001c400603001510404c03d001c0e00313126090300108984060320a886004000400764050303601108111a581c002d0030b002a514981240c0082c8005400907031011502481c1500a040038074520f80202c2c12458022010b20000c03088030196815904e0388103401c031203500e00703d6141090701190380d094441c012042c0045020812504014150065500c09075410000040d02c16410340c09118014200140140001b074035840d202c03071100403c0000041c280554400040349440c548011903025200384404005207048169083e20a50180001f192071900403283c0d01e90b00c3c0740440300a411a00300c01c0c90b02520264001c01401000e00004010540070f81e0103000442140c0300380021100c110080b4005843c60801c643c4174001402400c0010b10203810104005e800f506c0010b051010180d6111080700405014910802e100780d02c90165100d040400e2505d0760b940030550000340c8440031102054140100b05008841c4c10b80c44030703510 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 99742787 1250 99741537 99741541
    0xa03051203220302030d090f02090a05090d0903240603290f0603030712180603051f03020105030106050304030c0b01030506240f090415021216030501060e061b0102160516050108 78
    0xa00000340a0607d00b1148841803600c0f800150f500c200c03480d4003d0f00c80b0700c000144c0703052071b040c024607100c440001d80b0b06010801c3c10030004544580c80307000200020080c041c50402c9400b000754020a1035400090171030004110345903501d00781405aa54007185010031100646030342000c995005003c5078190390552040008a00192084440302c082c0555401c10445a00681180100d1050503400c80c0e8001703070b43c4000300100c8621881c0c0251081414103062000b007402c540009002c0e1105000c0e21050003400408142014440c900b000c0c110354020043d110b66503101d2800d55107840d003d80345622240c04484030880110001d0501d40040e0100074000180e09070a10305111a00c40d00500c140c030800380303003034440084240070f000030401200210303900c0c0c0003403a1a16aa100048910f14000200340c44c00300140b1030240c0004e080d1005290858100f62940d02c085031004444c09a0750620910b0b5001268608a50103054400c0c138039648101d003591011070407403e100c1e06a040c144510360000e200140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 99744037 1250 99742787 99742807
    0x120406060b030915540c0405160c03080c0c0d0e0907030e07090f0e0123090f070603050613090606090e060c0f070813060519030203090a020f0a0305120322030203 71
    0x10180030409000110829040b04030b4406030340401c0c1003a0840c0151b000304001e080c103440c09102d4183d202c0c42404405100c10303820fa10042c21400d094200406001451004c42c000c05503d1081c1c58580881d4001c0310000303001454010320144903401014002e00d40c06000c00d03200c2d8064080c000003420107000800e040e91402c0d1210018040745a0b514510a0b90f031402600c59540a0042d4044480341200c034810540303029013060290007008040c4805504062028016000301140c0241104c0c002e180c0850180ca030113000038004e824500020f21464581101a4100800781d008072044641d29072080100b049045042030302c9041c11581c062400000700403071030420721594040d00c0301c40d0107003501a040184050b20039820040541204010900204003004035030001c1f000d010075440c1501c0c00758154100075078510782d180c407074910080c401e17030400040c0a1140c030742e12141d50085800400321080d0951812000a040c0e1090b902c0b0180400d80380c0303018290b40c0c000442c07507402e1b1303606034011480c01400c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 99745287 1250 99744037 99744121
    0x1a090a020d0b060409061401051005070c15050f1b0d030c020a0f140f07031502040e18010e071e05060307020307030309020a0306090326060303120406060b030915 71
    0xc00d4075034020317034416120003c02c1880c0b003103000b040c002401d59155941000c04000118007621a1502001303010800c1d030b0b00007013a5003190000c48500300e140d03d11022441d9030907680d40c080c140b807440300f1030000300342000e084400d0b05618000c1076443d81070f1509000c1c40c66040b410b89911040200160f400012410001100c02680c9001180640c3c590301085100d1400542005d0105c1d200b40700320b500003041031081c00b503200781d103a0303003544280002c526107403806410300c00114004101e1704d42c0784803589940ba0400380c207401042c001400c0c9419074002c7d42d03c580701c0c0c5c00482c84801055191500904011405050120171a030081c121500110308118103640d089000d00302e944807c90f04110b101800100141860048000c0640310b03840d542c000795107518081400c6040401c800281001030424007105490110440f44c0143d03c62400781099525410319001a200c190b00854440400000f00b05900c6408a117030120980c0d0080d090709a41c031144001c0c042c045d42061400e1004021b01c40700b0701c1040c509 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 99746537 1250 99745287 99745291
    0x9070212160204110408060708190f09020415060e040c080f0c04090213030b06090708070c020315071e050a0806130e15090709060806060d021c1a090a020d0b 69
    0x944007000c0541503020405035901c6036210800d1800c0400c003440b45c0e610600000703034001c02c81e00e4401c1c842e10707281e204440300016107610104107650310701040038640825000b0159254014106001e224040700750500f0250040c0300c0c401c00681c0c4030880303c0c070342c0c58640600100502c843e6110341d01516040c91059800348003920401c403282d01040300140c0ca00240c006803134407901003012040c05601d0341c2031540900100502c2203104900450400c1200703600300340e285030855070741d1a081e400d14180d403020a10700172540d81444001030158040145a552000790101d18000103003000c00070a44a40301611b070381c090b0800c51001304012100142aa041003907056080b0482071401003503012188210504141c01d0040d03074002d170700c2103800b0408011010042c000c000c03d0200d00401c1480d150400542c2c58501c007a00c0f00b8414030140c55401d06558503642d481c5204290250034070400061403400354071000ca01c85026101048000010b2400b82001c42e19a510b03980191100300c2c2c0703404582d1446010400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 99747787 1250 99746537 99746557
    0x2090a0e06060c01050403050a090803120c0d02120a0c020d020d08060906010c1509020f030708100228031b17060d0302030c0304060504030c080706050d090f06020d020306090609070212 81
    0x14000443e00400074000c40340280d000b0f0705c5060380c400c2030710380013401400240c12440496008100351500c0e000d4000c07940750300507070750020b2503103400414810300042d210300c01200f95003515030418005003200303175444005400300a07000c9a521412502c0140d88030003000e60204042140031000840303c0c100703024041c1c0d0042c0149041c5010211aa644207525456010028400d90b5250064030031801c2104407500c00b42c0c0220002d15075039140c044080e80d101c20b41c1500000c1d007034001c0f50301440c00c0d1201c42d01009100660703403c41c0e40050b040d02c0c003c000b00140700843c0140142000f84102d00340c05803021001a10805110f07181a0b51214103006505050013012400c500c0100413600d030204060010b440680711a9407481c2d42c42c1e1441c204074201c05000c3e000364000341c02c0710004001c860b40100c100c4610000422010803049040d00b4a102c80f0807040341c0c0a040d950000503110018442d0707034002c5109000454114815032030340c0040c00100c4408646a0000d0791043d05002050030441c0e003d0609015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 99749037 1250 99747787 99747799
    0x6090e1302031216050d05030c0414060c010c12150f060c11040501180f0b06030412050f030c0d4a03040e0403120207080a0e040b12100605030102090a0e06 68
    0x420480e149206038441c400030f40c0c02c82c0100c1020784c1080b40902080b82c00c4000da10b810350460900100d004814407a0344a0500d04500750307240c0074082d80740d420a07191404503e1000704480d2440b8100608040400e04850001924140b161510b820f003500d1990700ba0340c14106082c035070030705001013503d09031520f543c00d4964013940641e00c6016529030140501a24045400c2c9104014141c408025102c00da03c05440c550700708481e04601fa00d03000c080e29402908191000307501e0341e00c40b1050b05d0901c6000718000200c7d03400010081c3d0000500010010910303c0c0404110610103400008524424510704428584203440302d580484651800303900c0040d0b0005014a45021181c1000e01c1c5134040e82c851003071308103064100010300d43c0059011100403100d110541c41c0c5a52aa11800d10313104440c00c0d08140403a000c01202581c80e642d00c42503030013101400980003000c0380c001a680d40c1c040d901007140802e050600104087c1810700070749120b030320301070015010316042140c2042628001000e45170012 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 99750287 1250 99749037 99749053
    0x3090a0f140f1c060b0f0409050d050f070606121707031202030603031308010c090f0e07200d020109050606010e0d0b070507050303070c05010513020d060f021c020301080706090e130203 81
    0x5aa2151003c11103103e840c001680c4420704041c040180c0c007910b42c4034415403900a45002042c0c010460745090300380d03840c180359144021400c40c00d0500403503102030001840c00d400840c2c260000401c003d8418041d001110300780003c000300503202e200c0d200000b03000484600d254030f580074060f0042d64200d000203090324100700c8500c81c40c403e601c5160b07100d0709282c5e45031805406906d411500000241855620303040d0003a04180401d080480c0207070802041250026504801c07814100309079802000380000da40c0d00481c0200c7c0280038000000d81036805006600110305a91301403510181c4426002e000e0071000383c40e6444015500c01d000b041e81050020030000440051010310081d4840c0f4015100d02d00c00341c0c81800c0490854800a20460508100c0882403026039580c00000c20361580c0500d0224080c0d040c001d84c200a80500f540102d0b50544445d240308a04d00340d030300954181e0301781c2e40454440c0d50740e501c0b046034a070740d0b688103041d11442c100e00880e50404000755403290490001d01110080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 99751537 1250 99750287 99750319
    0x108060402040b070501091a090316030e0904050a021207050109120c120b09060901020f090906040b0316140a0b071205130b03061c0b01051212030903090a0f140f 71
    0x99131008a085850781d6641081008020078507084003400200d005002040340340c40c4540c50340e2489100e0064030212161444601010300c95088105801c1000d01201194141498019924240303c0c0c8100d11640750708414a880103c009502c1040b610140d5504c0703031551070800c9201c0f09241642c001d460b0f1003241c00022802140324910001c0d41d0f032007803011101c0703442c0141ca070a0820402404150352640104000401e540c0c044040d580d8440e004c40b00c460803600c2e08400075004090400420b80c0600a0400c07103031049480b80b0400302200c540161941403100310001704407094280c0e009580381214113000b800c1c089039000003680140311150a2032407400d080d0b8800c1d04448000c030340c820000c01c80000108981d0381041c010303c10401c884040e4183d40781036190348108000405001d620701030710020b4030000c9600301c10420b681c583c0707140b0f03861141d480c1407045c4815200d51141c1480380c066020003030001442d0216070325940c04c61700145c10064089901b4801c001030100701a5419500240403005460b0b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 99752787 1250 99751537 99751559
    0x607060501081f020703021e0f0106060f02150603061f09060305160603020901091a0708070c21050607030c0905180a0b0103060302061b01150e040506010906060e010806040204 77
    0x19040c18002003110f041e4290008030010030b906042c80e5428010300840001a40000c1e941c0d48400c40841b0b0350107100b1010095074907050555040e02d4442d824500300061640e04100c2003401d072245c0d5420745190f40e103e21000c1e8681403042e156140c041c1c2c4000300140e040c03031108540700007901950251424079035841442d103048e00da0b980c00036110380c1c0100030840c240101c0405c9480c01070440781425030034101440f00290032030381903200701e02e82c0c0c8400380030080a0b20b41074800c4a000c65403003540240c449549080024401c04240940d0101b00f507080383c0c18070303041d0b040c400c0205116880310007020940e031444811406822a0820038040c4034880c1408070b19561151000c82e5040320790b00400e0030504e81041e8001c203441c2443d081d203040c90b02d401c3d010700241e1218000c4030115800b00314403e00c0311410740c40301801001da800160483d54000c0001051030003954004902507401401140d8050340c9a4030500100c422034483c540106010345142070055004841d0568401802400181021360301c0d610f0303080d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 99754037 1250 99752787 99752789
    0x30601051b06010e15091302150a0903110303031306090309150201020a08070809300f03010303020d2105250201240f05062b02190305060a060507020607060501 70
    0x34030703411142c014090301c11409010f641c0060350a4400300404c40e100c0100302882c50140074400c0e10000ca400040a43d190000c030306420540c0440119a038040240005103c64043e0101b01c5030403400566480035440c1c00425240505a0700045e014803401d60703a2060000d00301d00030b044050040c0444000b400718030740c1c02c05c03441c00c0307140390000359480c0898100100f040b1002070194080c000380c001848002d5000240240041006204200b2003006203400103908503a21103ca4140c01c00c00103500b4400c100c42000746040380d103c1c0d022203c0c1984a41010707942e4803040c120441c00d8808034112200c10b040180c000c20342004486021554800080a088405800000303a80026079158413407202c0c583c200118000341440803501002541341801c102c8070724040c2501c00d062003450b000c203000c0e98020207803400c0440090001d082e08003910415040f4030194104400e03102c00f40484555582d5a1400390090302d2084000400802d0994100441660704c3c0d0400102640c01000902283c0002a41481528 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 99755287 1250 99754037 99754087
    0x50a2007060f030b03010c020d030e0705030a1209080a02090f0402010c02030105091b0f030d110316030315050105120601110c040f05010302030607020f0c13110a12052a03060105 78
    0x1d109140b01802038195241c2c0e04d1494066850410380b014039a9001c20190600da5191a01003020407400b484139141c0049504255450700801282e80304201d02d90320340160f1017106032a013a900f603a440360a03a46884a6803c0030307412000d844001883c1030806c403c066440b030303c1410f10400380426034012074210390088503840801d42c4020301006810041c0300e480008040100c403081345001c2010003181e10360010200310303800e000c5405580b4912341800c0c002d98071841091149044140782e2410000c01401c0100c5184022803035010b0046100e5201c1c0d812a26036000521001440e9141c401c01100c00c113002c5512040240121440c242c2c166441c0c1c0103024010555800204055045004060a10754044c00c004150340c0001c0004103407040208108840c1b6800703c4a5004000c3c0040c0c80c003010b88000700710112441e1000601a1070369030448400720341c980152204000641e00d080d030b00c061810341114050b140142d03ea550a002c604403000960b4400e006140132804e1054a00b403002c2842813980e111 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 99756537 1250 99755287 99755297
    0x80703021308061f05060c0307020f0a05030a051005010b03040302030a0c020301150801020d06060302120114010c0b070f020106050303040b1c02070b01030f140102030403080705091206090a0303110703050a200706 93
    0x128203000b85140650002e005c040fa040c61600098001d082e60702c0c0300703480000f0b0081004564000c030303a036696100c490003000090144ca5240c003c03490f080c1d4544401c050618030b624035240c000f291080304402501d20441c0d06400443c5403094212007603500b50b101500403680341d902e4244403c0756098103030b40b0b08024a815400940c1716680c81c0340313000c1034600785d4014104252050000b45482010003049a045402e0741c0303000e20100248000495110311a40c40c0540329110360028402c3c800c1c0e0100b40d5210f4404240e0081107880d40354010140c0301d11603803148046640c01801560311142175240c2c400c1ea000200b800c01450481c4981d03030180f607008260300903901100142c02c00c0050040c0052680e002003030f804004c61030b51409903000b1b00703124005003681082100c0421103e5003900c03540c41c000d0785070442c081219120b00e00500c40d240c2d0b400d02602c04800190a15242800807240ca80950341d0403503041d1034590400c1103240302120840c030060030b21010400811203040c15040240100302c043c180c80e1340c603 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 99757787 1250 99756537 99756571
    0x204020d060b0a02330c072a0501080f040c09270c0501080a0203041e050c1f020f0102040e010e0c0d1e0e16060f0908070f03030206011508070302130806 67
    0x50f000c55000410f1000240c0b200b030105c200e40480040c030b6a82c1c1c0410010011034540c03030541001c00b04680c103040e0401403c0c40c1e08803041c0100f81e0b400d07003d80450340d090741c1e03040090742c1e00b401c40380400310160750060001032615801e00c807601c0f580e0048129088a0311000c00342d074601c818a026500d03456802514141d10b50281800325507805a4500da01038402802503207903040558640310600c078009001c801d4882648503040c10001d0a0100310b2070840e00800b4520701c883d203401100d0a2101c0800c0a0340588104038403d42c9251043c02034800721075058208180b41c0c1e2070b12411185034503000307014001d030000821112030810020712407100c2a0240105d48074901140c10130b82821a2480304040c00700f0b50010080310100c20162042c2d10036a1814074200d07402114006081c0e8104103e504414020300a5682c00b090880e450700c5442c0c11240603500b140e0850360b9490034084038250300411070f000076841e50005043ca034020340007000030000c03584850011554401c221800e20000382ca21210340000b42c80 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 99759037 1250 99757787 99757813
    0x201090510060311090c09040207020402071b08010605041109040504021807050418090b13030504080102040909050d0f02071a0f280f09031b0306050117280204020d060b0a02 76
    0xd0a29413503502903550b14410705010981514901171042c5442c03040c1c5e0009840411034950707405407258aa440340c004812100030071040050032005000303007112503207000e200141070300e442c3c0911105490030f2100d65103003030780700b000b8880540700062050b600700b003000501d91442480c80301c1a81c803650244da162510356090805081c0100040340d07688400c141068600c80100d000040d9154011000c160141c40e4030f10036290584103030280d1b03070100d911948003150018400400e0340104221074450010748080b0a50300038180d440048004000c00140e00c0103d0a100c8005c084c0c8000d401110412a118200b9034900c1406500b0751108201e890076040c210780b82a400140106003d410092908090380001c00b8070a00030441046480080d040d040e96001c02c0403059000801500510340000782489150b0311064002079040800c0c1d01c15015105600ca001081d0101c450003c2d501c04c03034019100202441178080001035002943d6020030b95a89400c0081c2c0d0400c418000c000303441707041e00640f0040c80500c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 99760287 1250 99759037 99759053
    0x3080702061b19030b060c0304050f060c03030105150c0a2a0b0f0702180411090c040b070209220c0612110d09080c0604110906040e0c0402030702010905100603 70
    0x390802c0700010076002c414a80780c0b041c1c0280d80c260415010840000a20b0310011805003504035016a0485000280d680d180c08021000300103442007a640020310002c03000620001d0310417040802d07000c3e0801e000605c181e01c0c1154080b01c6081c0c09480840c140000b0391480ca08003441441e081341c41042201420071101048030315910303002c10712641c0202e014500290841035104940d0302c1c061030000006c0301c07070441d41e0304402c80d40358000c1c04400c00c8403440c051401c007c0b2814040d03401d40c41030843c01c00003942c0402c0c800494090314080d18007a418401103500b846146440503281000003048081c1c0d80e240e8101c4000451012401620008411468a40060300f04291284200322003801c00703483c0200c8a14a108a41410f104480000365040c201d0800c82920300620b560646640a1402440240a00401c50703010703d0f00100c5000003c0d485e09070400045a9402e030303002800d9000401d0062091805a000d10750102050001184100207036403414107160f40780805030100c43e9203200c00e00911042c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 99761537 1250 99760287 99760291
    0x50c04060306090513110102120403050c030106050d030210050a0b0409050c12010207031e020102040b040905040c210311190308040b0a060503060406020d1d030903061b0702090a090803040308070206 87
    0x3c09000c0100341040d000500d5500c520484c050000e921020002002d41d100b00000801c2c4840380c0c0d002c2e51155100e00d82076440386842031056110703600741200852a40f400c90f902c14181507050b0020704102c549004900c003d058020856803080fa620b40345400c0c5a03d07507004800c03c05102d4409020401a800104401d24000c40e0400040d0fa20500c5030200083c0c02140a07208a44180c020903d00c2c2c102020403806881540c014110180000c01e00017016410354003c14010ce01c0f890700b41101c035865412203002c03d10850f4800002c124511082d10103e0b008403005a03200d540c1006135443da5444c1e080048840c1c0d05070b01c046000840400810081c07045041c41c45801588601d81404807500e08000241c2e03c0c070001e0400b40c0700303c0d400603039041c40008941c856081004041890640728101809490b00ea40050b00b003107029001e03010008404040c0b00e5040500e00809500190803c8815001e2180e1003200502d8640c03c41d642c2c20f0608003040c80700340a0f5124a110340c0c0c036420a4502900300034141500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 99762787 1250 99761537 99761549
    0x501060905010b0a030203040510060e010e0906040b011401030609060b040e0c0a02031b0c03060f0403080a060506031501050904022d040605180f0a06031514030709050613050c04060306 81
    0x500801070001c0e83c07042d421507015038810728003d0b841c2e1b1140d040090a100c00005031505141c6000720006d420001300c18018101c03541c800c49000269210441e094031400c0480d0001c02516040c2d00522007002a980050809001072500003007903501d036000c030000c89002d0341000034400c170042010000400602556680813401041d4a81000712240d0040e60768044c036041640c40b03d042903400d80c0f40f500200010722990100808070f44c1141007018140e0781c10542902e040e4005121280001c0f0700145901600c0115040a81064a15a103141845507450148001141000000c10001040b90760701e002030309521b4051040d0385c601161490306003110070580c0480b2030b40000c1c00e1000b04041500542683c070714103041018611404001000208080012050702d54820100140403039080d0341a4040c491300308007004400e2040d0b480e082c01d00400103014400aa241d4031041e820712030150203400954110fa8068441d01a1446580030a001e40f0012101144010000f0504100d00c940c980034040007020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 99764037 1250 99762787 99762791
    0x60a0c030219080c0d0c051809070f05130801060f050f100504050118030f1109010f21030e0d0501090201090b070b0a11040b0d02040302102f0c1c05010609 68
    0x82d00b08a01c01d6100510b80b00041c080200700040c0d00041c0e0408030b494840c84000100701810b0704103c00b5103190000308500c0c0f0000781803044c0c4c00b69410104030540c0640f2154907072510464184908031081c1c0e02160601e02400c0003400d000902c00004d005220180c204034081e000ca245c181406e0041ca4040c1040d9584240003513408107000ca60802c2c00c95059440038a0300740c02000481d4042207504070340d03610041c24180392502010070300c240c6101c8020001401c407191402a40d80303146150140c4100e000d1b02c0070301100c0c45c3c01e00482500b000810451107209040c000540101c80d400103524062502d0700303456036512183d0309002c540c0e00500110142c0382c3c43e14042e04101281d02d03040203070b900c02880c6519071540c0c0c60400314419a020141e800404014107060703610700c05441218082e42192104900600300b420306001200d00074000e0000d0030480c16000ea504c45400c1e00d13500480f00d02c40d405a9003500400c0340b034051540301e0f10a0031000010102184d1505490341c40c0141c21200540c0c400c4003224 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 99765287 1250 99764037 99764047
    0x2104050f06040b0a0908091e0f0303030114040b0a0f0608090f0607120903020a06050a020408010b09040209060112200403140a0312110d09050604120e030a032609060a0c0302 76
    0x3c0c00b50000c01d41091142c0800180035009107818003140c403c0891180d404440040403400c40e10301c0900111328000c2c191841728040641c0814103540380006e01030b0141c00c5034074520320845800c1642c4511382015004050041fa159a846202c00031041504a00001201d00e010800801801c11071b5008141440004044515006d003004201880029103250a00e40b6040b4500600d4420080404400d8000d0400c00c036074100074200340000d51092080c0501035081034990485441c01001031446550040d00e103014640c0d500c2c004507461480110060b1010340d0720311024a040003c050001041880b0120b8217a85d1807e40c01c4c54011074001110315a2540d01c44241f04001036881b111540508581140200c0c0072202c0813404113917405012001e8a03075038074200329482442400100d43c0d00860290014855402003644112200090340e0b02060301035004d040b0b00b81c0028440c1440140300c4e142c083c1104c440248034031040c095148141c81118180d444013041c00603d40b5544101503000c00142021844c1c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 99766537 1250 99765287 99765293
    0x8040b0601050c011b120f1b050306060f0408060a0f0504030c021509030115092301030b07090e0403030903020706020c1302090319050102120a06050607172104050f0604 74
    0x10400400ea60704005011580d045100001d40240b84800142c03680104d003200d9a0000500c0540d024004801490424601d00030241a62154281d14070241d078807548000b400c0081a1f8003507002418082d0030000030010190b1144c0f1a401800103040e50001030f02d03850502100410035130701001c084580c81d610302001d100020342c00100708160309505890000240c1441d00044c200c0e4043c6450384c40d0035501303000408108005c101810003e07210750200c200304444000c5406506090042202040170011400520200d44442d42c03d9a20507034901d0100e5415490b04441070035910265400c4000c80e48420140013015018064080640403601c010100b80240c0c83c0041c04a084000c01c05806950020b6007800f551024021070315124201002494180324518001d4002d5008a810030841c1c100e0313402140189586000d22003c94400a03c01c0d400d201841d20307002001320356018041055039040141c00280c0c00b4211090101c0c40003580d01c0300d00c0c2d241a060550503c900343d0001001a001070b4100400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 99767787 1250 99766537 99766553
    0x60605030712061e050310020408100e010f09061a030d020d0e1c0b011809080405060a02150a06080f0114011e03080324180604020703050403140105010302010f0804 72
    0x100414030301d000c14084041d0b400100090040d50850b454a06030004082c481030b03040700c0c803501100c00550807201c0e040c03400081c0c00b080340518010180c9541001c40c01c01c440d003030260010041d01011400000749070242801007001c0707400700001144c450752541c0d080d0381804142000200185003c2d40a0901421010b000944a5400104e01000d2011442d03011a640c1c803640c9820000108110b80e09500c24864241400481024402ca102110501009044080081c01a2030245510054607810242407030100710694003c99008000c6204408100010035414180f4030b019044800000030454108601d203400e2990054a214a83e81001951441d12a040ba8000d04641c0179248200400c80c0c2d40140703804031821640040d0030203101005125848066101a4464071110340e180b0b50700e0202c0c201442004101c200c542c0e428005000700050960030290010400d07644a0b02d400717071400c0c0c1c5075924445010030310043c0008682d52540180111758101aa0305407085d121f04012070145043d54851107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 99769037 1250 99767787 99767791
    0x602150105101116030b06030d140f0304031106010b04170606061608190302030609180a26040e060a0b0f0403030f03020702030118020906100905100c050a05061906060503 75
    0x401c104080907541803051080c0801d602c140383d80c0b9400404c141d030740d041c1002190029150360303210f4021050011765117070284201c1c08984d105000e480c1c3c1004c4403c854a1f00c503400090055051085007008591300c08818031803d0301070310000d0700003070700c40b403c01d10400c0c2e034840301500100301944410103005c11580c3e0001543c0640706c02400ea800000c03000c0c80c1c02c1c00603000f00c1104001110f10301c203540341180d416401940c4074140030745205855a842c24002c0d102e14031642c03030319407040e040000311401107008010542210b680079456104000020b01c0200e085034415070014030712810000510005d4900211000018581c0034810350030700348002c040d0003036032007640b200505121500880c8400d1078000d030140e60100d90010000c101c100c1d02e40c480c445030540301c20401c07803180c0079000000700c05182200d01c2c1c02c0110000d0780c51030102e5080c08240410890b40b44000002d0010847d14400041c03c10082c00c44461301c52400b034103c0b420700c50030301c000340210469035072020b030300703004e402d00021754003005070781d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 99770287 1250 99769037 99769069
    0x81002090105040f0906140103060e0612121b0105010f0302060f070204060b04180f0e1009020f040c0504081207030503060d0212160503251502010e01150602150105 72
    0x1640c035048600103036460720443d40120340d403115003400041d1000160340701e0004ca07803008540803891401c10300110103e60305402220044042940401d2060500c0e162030070f01d100e2090201c0f80d038100c41745881c00141d007102d1000c40d038544500b80702d10368003c000e014240c010500448a00100c0341980d0010f0b115000e22a00003400c40e9006c035180d0259611500100d0080600040141d950b9488049048800011800d8a1101405c2104040b80040c5a110369881050303d2405400000700c59040840500080401680c0c010f4000702d2007962550750344198286c4864a403203550b030311031810b5041801d1807400800120340ca10180300348000f080d0040116a80600112030881100c0f05a2001980858181c0d852406500c02c00e0401c0500704280c0d680c2d88140c0f10120101c88492150070442c4118203680504600c4140080104021b0300035150100d5841c080c0d00c0c000414420f41000700182119a0020310342808400c2c040c04101603074060181c6400c0d05003664082c5484d40c10f1001007113210400d100e8503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 99771537 1250 99770287 99770291
    0xf0306040309030b091609020a031a01091a190203041509050a030b0903130b03011d0105130902030321061008070e100306030204150e010b0309060c0a26041b0810 71
    0x140c201201400184260300d41c1e2522007800d05e4440d440c00c0009e4209441e071601083c42e04000721031442c1429000e0000c00ba05075101c080f15820300c0c00d4925800140e0785a644c1480301400010448850780f24a030b8080c800c00d03030095881e0b0345060004143c05a2481c00c21043c000514018030151b01c400480c241503d0704440c4010b050b4492a084500d5403041500c0b403503148190b8400890440d95060080d4100da402c01158030550800b0103041010007020b11449501255850440c030000540c2d800c00503445000030292814113643c6d00c034000d2005c1c820034581e04c4500035a81044900e00c7c00d40034140204c809450000814500118050710030b0a0a0b01c2e568030030003141e605001070078403030b401c00310155502070028060046105550400e5501601490101c45c10f000004038403050050140da10800141c07000b410640c81d4005680d0003580301d43c1d4448108a0114819482c015062001c940b0001810f40c01c81003514003400c110400d20481481100c1d00c000070747d001c00089000041c0015501709150300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 99772787 1250 99771537 99771541
    0x907091d040c0b0a120b04020c1e010213090506012303070c0c18020909010602010b03070e100906030b040203061602070b092b05010608010212010e0a06030203010204080c0f0306040309030b 83
    0x1000000001c0ea20080071044002031103c661a0f00070121740c0c01e140b1035902482882c0e428410402640140f00f0050140c2d403004000c0d620f0b0b07900c0e0f00316900c25102c05000040c50081012013902c007400c03007500039020040c0c0768402d01825507840584030700d0640c41d2040e41da5080c81480700310905440054210410051080b00c00c506001641044038010030781f241983d014840d40e5051200a5041550781034411031541000040150041c00b6610324444000d0250124900746040307010094006403041c0364540070b040003c2403600240c419040a90700440d03000c4020701e041e104051501e00010440c400e9241100742e0031030f01e103400080c1d5206984032140d420b80c54500354000300d10003a480405500d100c002c1c403200001031401c242c16511105028800038020140c81e668034038207074401c1640504004a442c3e004110403074030382e03c981307400012082002c02c0c071310b0380c0350002801d90f040b5070070401d51354200e0300e41d043ea5450f012490051030300e4150f000d400e0500d0a0348001d02214180e21010b001d814000b80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 99774037 1250 99772787 99772793
    0x903010f05070309050c06030603030301030b070306150c05010f0e030409020a12020a0809101109010807020f01091104060801050402031e1c0210050a0213030311010f0f0207020907091d04 82
    0xa40d00d12800c5500410a500d048100240074040c003030340503981401038424030301c424101142103d12500d80507000314a16440c664600290030401000b41e010180d50391000702d59500034100307170140e461843e541c03c802c4489074208203084031044030002000ea46071051071023030030b0701c04800e41d8102d41000c5c90040e1550210382090310340c07503090140e491001e44002810182d881c0c000b245103008464032811200d4111301c51410904540305403144400c899400c2c0000d0361250310a29100d6407103001c40c0305550303003100f440f000d040c01d5607159402260040c80e184000020f50405125400090034803c000784000d00f0a40c02103511610001c1c0310ba045000c201451418010013008040d070205065120700e6050f601d200d6009407506030307030440c51480c103080c000428034043c001d000752400e00103100d0400380c48a113565010794a4a0b00c0d50031400142d503d0706456040340703426208120107089507070310150343c65080d44104404070000810354001e1203c0340005004101210249502c001c1c4041001e65072611281 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 99775287 1250 99774037 99774041
    0x6120209150409050705070c09090804080a03021b190302091003080408060405010c0c02030d0e010306091415030d1704020a05040f0b0a170c010302250521041a090301 73
    0x640d856800c520545a40300070440d908008104842d401c06040026440d200800c441d140b10390072015003001c0c0070715002e03c501c074000c5d48090500b0784070350034140c0740682d02e040c401e00f0000b4001041c0c01507001000c1f0906441c102081003043d84400329802d02c00e007500c240e0b0b03950186600d408068010542000020450f040e4143e010002d147c02141c0c85072250360346c50300290b983c2d10403642114154207020a80d0501070040c030010072800e600402030202c101200d001103558443c404005410961503480000e507040d43e5108450810203215500d1045280514855420380441c5003064025408410400039560740091100074040c41c0c144031050940381c1d4000540700e5001c94100d65481454910f48110055199100c9031181c2c81c280c030111459a41c884c00c09101c4807410034083c0b1150044c15401c0020741c4280d005101d00481c092860f00c5203602d034460f1425198603620112510b5002102d10404086414003045500c1c1c01203080320314090400b8086003000c00c2950950444c41000b08000e94030b66800c2d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 99776537 1250 99775287 99775297
    0x5190303031d030c0304090b0d0c0302060a140d060303080903040e0c0c07030506010e040209090a0510020c1005040b090601080714210114011707050d032703230303040c061202 77
    0xd504503a120328054604c03c0d101d600074468210203601c6c0065580c41d40c2130030303d008085650031400d013075244da24640034481250b0045ea20a400c00800c54907115020200d04c01505582d003441d02c00180721825441c0144c880100a805000c0d507a105001c104602c5981ca01075980c0a44004071540e100c001c00c080c514905120380d08004c0080c0503c030004a9890310035408180709070b00851f003034031140e190b1800c81303a100d10000342c0180c031680100d5512264040b294000340350102c3c0800032a10202d0303241744000111078054400720b440e0b8601d40d05010a104080024a02420301e41c070141030002c8ca001c040183d400701c840b05840c00b4500d0382c10480c031812518100b0f62101d9034180024043c0041c1e001321341e1a03000c000d00841d1f0f40d8002640c0113052814000501800359200174000140c2a01c0544044d10913030306040c0302c101c8441300c00d56a81500d5501c90b888800552080d40e10040707008030020400303882012018100d00310f500500030000071030006200d61088030b411f03080c00b128007400d621000c0040c2c842c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 99777787 1250 99776537 99776591
    0xc09010c0f0b01060807031113030305031005090a020304020102010c0906020604110a0b0a02060712110319020c0a1203050708090606010305070504080a2306072709050a150519030303 80
    0xc0d503800059070580148002e1b2107503129590802c415042810656000d001c2c0884600c1006149201413000900900055030452000c0810164169803880003030896481140d20402941e0040144400c550f02400f8207000301c01503040c010740c524100b100003503840307100170300c040d211145410542c3c1d9140c880794014030250488007000c1d6628000c3e03000c0690f4580303064a10100040781a04c00c0180014144100d0381a030000da8581841c544602c14050446200090700d000c1c03c59080210040d404000c00205540d00e21483c3d0120b43d010402e200a070403141c00030720355001c0c00401002c000c18900b0104200740d10190908000400d92584a81110315010310341111825109003103503070b014441c42c3c42d88400c42c114100907800d40100c0b22011191505010b949010100b48541048030210011080c0005040c401d4440940401da94600d03044c02c0c0d400640b4003045080d80c030a06030085940c0e0002d10005071405448440310000f011140c80a44029444090101651080c0c2c04114085d90203025426102d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 99779037 1250 99777787 99777803
    0xb1902090d0302010902010e0a1401140d06081501120f0602070c210501050a020f0a2604030507020306060f13020a0c0804060906020f01060503100903030915020c070506030c09010c0f 80
    0x3041c2c035000e0300900d201042031b408107244892040c034a103000b12003076041e612080380e0f5045404407400103599080100700b01031460842440344034402e0109208410051052000030301b829008500740f50344100068102c59961036220501c140800c20f15121049425400400160781d80381b641060201044e01e43c002803520070400f112400c011103240e80407108140110020046a110740b0a400d08a104404081c80700c04024400d5810480c0070f015104460f8250891004541448044440410f8011203048010540100c0c41d9400e508041044a41c0320005a50604182242100207540400d2a4290345102900040e0b07519900d40b00b14007001c0380d154000c1e9095155612000c0140c83d644180c09008014820081d000c5011748050107403504407140a0080d000c5e45041d0082d00c000303810800c605034113040d01c480000d000102900402140548003800041c2c07561041d01c84a414440b5a41c080f41c8604014402e0000c49010b132012101c3c0d40300242090f6460162625151040190f0454040c3c1090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 99780287 1250 99779037 99779059
    0x9030708030a1803020a03020d03170a02042318130b0103110f030d0504120303110304110906010c03050d09060e1207060c0504180b060f07050c0a05010801030b190209 73
    0x1103000030140070071801685038030318001d60380c40044104800d140300107035115904240030800f42c1410009120303000d009103031010b019084000480c040300b1007030f144554420b600040410480c0c00041406043c041035881d0a004002410000f4280481c450343d56400070300e40501050700c0c1003078041d5140030b082c1d110409004940c0d683c104683c280c2c0042a0b00c0780514024520f084441ca004034a2008115031078658508190501d000c4140418040f076040b828075680380a50760307541a180300a14031440c8280c66075984204104180851404094142814040000032a0780000d40150030385072004a181d20000d6220130508110b000740151018050890090204200d1124040b00042c41c55500984040c012034641c0b81c000c13a400c0c0300e58480c0c105118a40c41100da4004416044920856401004142400346180510407a640811000c42c0c2d140c0c080010140c03103041980c0114020002401d11020942c5141c65590303070003000800c14480211401e0010075040d08560555500b0040580001401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 99781537 1250 99780287 99780299
    0xc050306220f05040b0a090506010308070303060f0e0702010e01050702070b0c0703061112060109050d0204150b0f0409060e1e07020a06020315030f010c050a0e01020f01020d14010602010e0d14090307 87
    0x1000f00b0f03201a2002844080002d9141c2964010080d503680e1100080c00c03568030b551610030312600480c0045080644450002a4032244012010301602041029060310308100c900a4211800d01203014103a9041c00300300103043d41c02103000011030f880c00461039a02c00c83e1031015814011103410041c4040d24107101c8200000001c005040c035401520451b100e185c54010041d00c1900591040551011810950000504142e0842d6102041d9101040c18090f02c40001c6105070700050801300c0700c01400710f0200018011402600d0060a40c0c03100ca41d044c1c10a10702403450700315140400c0802041180200e003015208208004a083e0880403c6450303060013003003401240113245803140309105072480e001244206100c2c2c078048041d2600c8403490030441400c10755140440545050650042c098070400b07050083c001017951105a80c40003e514210440a03015020180c0102c030840e85450b00c15800c4c400001002e403903103005400c14106440d40100c1920b01071280c401410f405014003100040c403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 99782787 1250 99781537 99781541
    0xd1d07060215040209060607020310050403050a0e180c0703110d1805030105240109030501051602010509030f0322060c0c06110708091002031909080d030c050306220f 73
    0x15180d25509881c645014540c0c081000e8809840182d40507010382d002c81e846207030142c001c00c01d003407000d0140d40d900c00b0029841003c42d0320480c4e0640100b41c0000d00181450342c0010100c41d00e000450310004038500145401186d19030040084048410001e18901454003c070183c980380101102201c401c09a2004020048010f0182d03a41d0454000d400200d528501070007440c0c800c290400c442e03510110052104000c00c4840c00c00780f41840991301c00400420002e0282910812020142400724210a10002d0031070b00010001000f68000384080084034030b85ea41186d170888062000101031001c602c1000c03008000c0c444000301074a140000c1c0b0210f00d50458200308195005e50410015003c06440d244070f80d104081c0700614040040000c1c541710b05d016441da01c4000c481d4812030313041000500300014100140c8070010003003a03120400b003003050401c002400c03400c0303c7c1c0d1405000789555810050200c4c04041d1040b44180d840c0d01e62680a107955024401e04020b1311401400b507042d491300c078040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 99784037 1250 99782787 99782789
    0x901030204030506040c0e10210305090312070b0f06060a031512030c0b06030606030c1c0206040308181f030e16140a05030307020603010614090901030c06030b0409170d1d07 76
    0x3c4549940048d140041159070202155400c001c4102120358400d03c0e001d101e40c02500c00c41c1401014086034105850030050070f01545040d00d523560743c41e11181003010665070010b2400600030124070030445161240d00c10794291415038140170403241c010000c0749100c2413140d08020800c4269140006c28541e11405015106005d0010314003680ca401040c903488440446140340c065000b40310640250405103070140708040c100c124400158603550000b201c0d60b01070360068942d01d04c00b04910070000011440c0a5030010119001200b400e0f80072041940080701180d54002c0c5640c4207190780071001d00f400310384522005000d5108880c3e1b160603c00103140003803008140118006440403800703080020498038155001880141181c0c6800401c44005840054041c00683d041c0840f02d4030784c49041d41ea60180d4407400d06416010b051000090840310344040b0036103e070303007031428040100308081c5240c1942d06103c1900c40d034442c00f60f01c806000c0c00c0040140c0600b10b00096456a0f178450110303a0700 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 99785287 1250 99784037 99784049
    0x503091218180c04051306050d0c080d0314010306020c0f0604031e083117030417090d060b120601080703020f120304050108130506100f0b0703080c0901030204030506040c 75
    0x40e5040760100200315074034004450000700306101300700a00440c5851280103040c0f0b1081c0c0300200c0d030715807100d0104214060980c021140c45204003000d000012090011594100c0145001c0140401c1c20316040501d10040c131004d48056800031301c5402525081c0468404d2003141000c454240c205072034010146c0e04c0300c0b42c0d41c480c5440070640741c3c109540308240d400c0c020f40c1d503800b10403101c03000e18001a03042c01d40c840303511155030f078003864000000c0d04000e80341c4040c40c0c4e406440b81d124505400c18500041c184450602c1c80c08040008044940d500c0c01d8031100c5d1a08640700150509951020400080c503000d40c3c4a00c522401c00001807010b400945401603a2095888000c400c2408045c082048007620444989400501090105c0e520030b001c1070354011034180e2070790703c0700702943ca034182494400d40e104008000c12070301c20b004d01118a04100e00801c801c5024504d4083c117628024040714020b0301400d0001c0000070403a0880c2e00ca60181c501454004040c0c540c281044d15100489200c548101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 99786537 1250 99785287 99785299
    0x507090e0612030909090f0706031505010e0d03122912030f0304030309170406050d051602030d15051906030b0406060f0c05100e010b010e040e0a030503091218 70
    0x14207039080103070103865500880307002141403080c058100710f46078000809000084c4100500706000b201c0800010004042903200010090702c0807010301040358481d0801c40c18881c1c011003810746c0e40c45074144000c00315058030b019401950080108006841540281100c00144110304040151910303000c84542c0d00480711201088560342d5451b40708d00a04c05690a040c4042c00001d01190281e0002e40645106458400c404942d942c0d1496881c1c0084e04003400040002c11850880b402c00c3c4a045d41003400700e40b00c1100c581400030001d660303101d40c40b019a4610303102c801c018070310380c0d0603803920000d03150003003a290f00218040b5040410202520038440024201549500a03040602c2000306450300d03695030a02401880006076681c0c00401c0d4103c074281320307055001c244098144264510b01010303c0000c01c0c0e1b0001c02000420000021014511940ca401103140085200040d000d0403540d050a0003912035480c11071140c00c1c0886491081d6481c203002806001e4004810310184d0501c4c0c0450704 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 99787787 1250 99786537 99786541
    0x6061701120b0c0c070b13060f020c090a15180212010905060d06090503070501090b010f0b0c062208070503130b1c0b060919050901150813080d0507090e 67
    0x540a00c4003400050001c02c1e0500200f2000780c200001018221040001c41e50701d5607030b42403c0c81050784080c40c6082e411160200910540307034441c0000c10842010310061209050f00400581039010140443c800940d880d21100d18880ca1403014000400100c015249451301040241000e540924900f400c0500440004200380c80507118035801140b015080c46c554000070780c1e40303000600e0900000d5406202c1801a2000a6800d01481d046544142d1052446514045442d03800040c4ca801c40f416602e02803204010b021f40000d10035602102844005910301414281d21b030b401408010b0103010383d80c000030283c0c1440030000c020300300f50b01c428504004590b42d071100d50559000b008000355140240010300c102e2014250002c00b15010001c081d5494003810b140015007050906802d1260b0103680c08040000d0303e4448100c60042c40c0d119207040d01078800744001010b151009100b0340c400c0400c1c2c440d0900388a62001900d50121190303808000605001502401500082c410401d1501c10080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 99789037 1250 99787787 99787799
    0x50d0318030e0103020904020708030a09020f0f011b0f02280b040308030406090201110d08090d020316150f050112140705010203180f0a0e04061506090603050405010f06061701 77
    0xd03840000e0340c1507941e000401d030940004502960004a40561068084c8680c7c40401c1d062030096008418031a00062500708034414012b070b101407031288034880c0c0702d445608019660080b600c151200190f09509041650134600322095610921000c1c1d0000301400c240e18030b28068541c03102c0841d403102d83d203034100c59540c0424002803049001c010315001091000ca00000c02c2504610040da205051440d00b0070403079400c161a0400c0e03c1001c60000b006070042c04844102845050461032151000d10b1510070785168481242e8950a80101180500343c1c0080c035288141e0300c07914003020b542200348041d580d54035040b1207461400505035041201c07014500f02e40ca5001610f1021610181c0145040420080c01c42590031210848650403900d03603641c005060796420004c1e0060b10fa0501420b40c1400c050408070201d5115912402e1400d00c4120309000d9640c014844e44200d880a20f00825591b442d4070b0514098180495144a140d0826801040c0c80360080301020281c102c0310f8080002c0d0ba41e9075 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 99790287 1250 99789037 99789071
    0x1203120b0d02010c06020c07150314060a050a05090403050c030703080f16021c0507020301050406151d192918100915030c0b09040c08040302060a18020d050d03 70
    0x2440080c08604e4024858000a5041d0040c112034100b06040c0c400d002d40c2c031101a08111404480100000d80d9060302090100802e0003807070304490282d50226126042c50049901e061503030140f07920499400000a00f0144214116400070142e14140c0e600d4080628014040321401c0e250852400c86400018219404040031140c0e402556801050042c0060b150200b65001e684801000c0010822060015071002d0040782d0146100c1c1c1d03400900300268807144e072151819900004004d5004508910a21030054000354200f0b030040107805c03400d016448010300030302d070b08010328840c031160721008801038268400c190b800540c15151072440b11002140d041645404880b420603000c8000418014400954004800e0001e50203054001d940c698403104800802c56010382c188641c00540150941014003d111144210381040c0c40740d820a9603029481d140010720440407070f66034242150301aa242c4041c104c000381c003d081d20000d0001c9003000c030b49034045511042c01182c10141c0b9103001c50180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 99791537 1250 99790287 99790309
    0x81b0615040203062103040806150f10020615010e0d0b1f03020a030f030201020408120a1704021e04020d18050115030b1609050a0605071502130e101203120b 69
    0x40010f096a505c410041020b1402080300c111a072005000124100ba0100550390003980c004104c0540340b0705100c200115003410203d000c1c014041c003004010401e030002045900304107080c01c0307030210403001001220210041000150720524a00c0d08605011000c030032a03016000050000d8422401c100004266260922009400180344842000400c20f0f810101c90128460300c005031405a0301c0c4902481c2c01460944840c00f45400101c0c4210036400000c0007501185d5000743d149180782c03540003c6c45d01d1710b1094541544411083c51144c6a554a5048480f0309042c450b08220a908860080120146101c81202e0035864841e48440c10300d507040e81141100d5010070300841998648d070808108003d881c404905000341e000010850f07a4486400382c001e00000e54034a40c03106918200504a0380c0661400351000713104004085614507000e070040c0546001300486455504c43c3c62a0220001d20343c0c0c000d0803040c9524100d2001c05502104200c6465418881401005181001c001c208520 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 99792787 1250 99791537 99791539
    0x60105130909051203240301090b16030f02040602010b1804170711031e100506150f0708040b1b03040503031206012d031a0d0f081b061504020306 64
    0x4894020400d03030074560003000b080c2d44694142c03074128002c1c80308079029070410390b402000f00300300006501c050000540e1801c0d0002d801c40003802070340e40c01e4640c3e105100000c0c1c840f50720034902001441c4518041e070071008007410320003411543d4030b903100c0000b8000e220703007450390348070740c0007510b24210401c0d1507112903004031b400c8840f0011582c002ca248118561103540201c0d07000d1004801d914140e51309124030510240c0341d0301440b60301e001224550382030108011007030810b00c0c60041440460b8644015440c0d00080080c1015070310b1001450111140c0134020f0010240c0c00001004981005240007500ea401c80e01002c9110003181c06400585074000c0d400b486403d80d1081c03060240140d8244086a00b000c01814403400910b41150540c820f016110551420507003f00788140a03107905106020114188011014403440802c0c00180181c01030f02020300403034144600c0034103005052003150340c600030103610444900e1355845c0d42915507104031100807107605518643c0c8500c0c02c6c20b008903842080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 99794037 1250 99792787 99792817
    0x110f0d0905010e0312190c0507150e031603030f0201060308030c0c0f06090c010e12030304140c010f0e0d05250302010909020313022b11030616080106050307020a1203050906060105 79
    0x3c8800c0312801c0c40341b017031000040003040d060000120f942802044041c122081540b02142d40e022009030841b1803404583d4000c0d41703c0d801d80804442140600b130305583e41454210008443d48008a014010980001c2c01418000007030103400c542080003000103150081c159011005580a09034075080216441c44450b0042049600250300c61705071241003034002800d109005a2883c12146181c008907021901800700070b10014643c20100413a640070802460b22011020382407000618214000c40c03c24082c040d100049010800305003e041c0c50042c459040d00b400550441d00e00f120180640701c00d0380810203c2174042892030590003100d110f008280d201d25100040d5609011072a80050003c07800404c800403401460101c0303a04600d091406061301064404c8180109824004040d00301000c0c0d104484484c420785400c6154141150182e040098682c0d6540009a04000700c120009140003e820b03c0300003d65059400703503002d0030400c0704861641c0e403001c0064603a482130080310f205443c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 99795287 1250 99794037 99794047
    0x1e0f0108071209061e150e0c1c090b0c0d0c022b020708070f0302040f0e060610090e0f0f0603060c19020102040308030a060302030d020616110f0d0905010e0312 70
    0x14080c1d00840441c40c03040100003184d040018200c0303150110301301ca80900c50b80310790f4010784221030030241707001808207150160001d090089000807640b04102c2e08540800c001ca0018683c4274032036010226403600038241455918003400181c4895009030182c0c03404c9403810481c2400c40d84001042c0a1200c40d10380500d00c101c207400010815220068040403c61103600000300c2d2900c01400720b20700034079280b0300c0c0c81c1940341184100415140394000c84d20f00d0f2440e01003102501a40001d01c290803000683c4d0b00c4c101001d2a203001c2314040d04680240080e900801c0500c4407495075a5010f900c19055642ca102054890004141c0c03201016158000d0018050285101c051041c0070041102e0340c0c2c0c1d00005107416074070340d98007140c2e800c1150301010b0346507115004c0081d428240038001008140d48081e0005160480b885606c03100c0000c1082c1c10882d940c8042031000c11708020104c418034111085500c01004c21a008042c41c41d00d005150008004548040d13003400d0004980d80d1042d0240c0d81d090400c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 99796537 1250 99795287 99795317
    0x30f010902011107060801060e1210020c0d0503040807020402090d0f0b070f110d03020a090f080a03110703080409020906070209090115050d020109090c02010603021f0f090e06010809010b1e0f010807 87
    0x348040001d455110090ad003421440101c10401c884064810070005a107420740180703041c0c10100041b4807d010301c80200704000000d9840000c0f030340c0399541220f0040e16170aa12000c41d080500c0000c0050803030100c094150140907080304094071400c4540d0300e03910940111042200d018035100900d100302c0d8015904038424030700a030081c2c041e01c48107280c004078075030781c4000070400e2000750780c05907442d508103003180b01c00e00d580b1400200101d400c3d0b000802e880d510703568810700d042c42075110f10b0701d40e203034040b4803942141c0d1904100c4d580250000d24150460810410140c001d0032291240032840408034030000d1b150501c0c20507503107041d40586074445114a007001c9000a0807810158034115542d4010101c01651050f5070119400138000c15101010461100500012600d1001358140001e0381410060718a10b40440e90340420281381084950f00c8260419001d808030307044a541c8030b140620000f40e00c03181d40081c5582034000f1240303866415960702c01500d1036402903d00c2000204405103203160 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 99797787 1250 99796537 99796547
    0xe060a0b03071425050106081203040f052416032903150705040303090e15060a09090e030a03050f040f200402040303030b040f060e0123030f01090201110706080106 72
    0x43c45a540c034040c9070810313903142c40c0d0b41c102d04c0091090320040e03a01032440900ca000d110340c0b00034022960080511160b900041c0404d804000c0005016041c1103400004004080c80b042c01140d260000540782010402882081c0c440c0c1141e100400102462043d40c19520034041c900b20f92110141142000d049080d5101800c0c5000c0c400542500c50301c0705420024007150400ca1050380c0d20b0b0355254589042d481c0c0102100032661000c00340210090910421010b080c003c8038030041c089a5850b82c1e0111540c0c150707096241a480845018a040c1110082440100040030030161704d640802c681d03a03070107040011078001590702524a03d0300104c0c060000c1e00344002640421504200b030005c1701f03181d00001d4160390207a0000c0f00082d07103c0c0790000d40f90400340503a0200c601240814402d01e824080c00c00c00740072051244400d030585600070031040b280559080c03c6507800217415034100c2d038490401345000e0308640078100c1c0019104072400d50071403804908a025a9500c7c1c1d11b004607030b4038025044503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 99799037 1250 99797787 99797807
    0x61c1704090c09050a290a0201140106030618091b0803090310060b0306090c0d150302010806030a1a0c04090614151602040b0103020d0e0714062803090503030a060e060a0b0307 77
    0xd90541d2802c200c1c0346d10344005c4040d248071b50281d0f0001c02c8440207030400010f111b1040c0d001c04141802c09906004c40140750764406100000b620001821490380c1c02c140001c1304030300c0441c2c07186c64030001011490700000b2000303114012050307003250aa20300c02c40c1071004603840b904c01e10380035810600c0030404030720700174030882d822480c20003c103420003001008100850300b0b103040c00350003012203141c10000c6580001c0b10700c4d401402100a8540100540c440c00080341410844c842e14000040c0010b004a410609a0b0301810064008000e4103480d030f01c01018070103c0da00c1319441000d80740100740450458000700c0d481500d80b0110342c2c0c202030031a4240300282c0965490941495000d02148044180911662402540200003004103900e00030324403981204002100d1700a0f5403c02c40f03008000000100e200f2003940343c0d004281c07014540c56088000b4098035100420034080041400f0403101d05800c04019203088400c559040d031580410015900c0f5180300700500300344184002001e260040b00184 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 99800287 1250 99799037 99799079
    0x1210f0201051306030e010606050304051005060a170601080609030a050406080a0902120c090a0b0a0311060d091a010609050d020d060605030106080106080c0406060206061c1704090c09050a 83
    0xb40c1802d5016682260030f0705103400080029039151441d0f65255024007420005000c0c0d41481859401c0a403601511898400c410400075601c400c04030b4400d441e03403102070008141c486070003250420411481f545408084c85010400e00c682004a1070240020040b241c00755210f80b01d030391401d4604803040d14051001820004e29035a115549000758460702c850500707410106001c1d00001d2101c0b4100301f45143e020b071400a0700c6240c100c0710f03082925440c650b074013920380003065440c00003181d40001e21580300342c00050f00304a00b046c2030300d170070004614a40074400ea01c0384000007182e84c03500710849900d4070307a01c100b640c01004111100c8c0036007091480c24000500030f0f4004510b460319075000ca4250740c10f96101c0885a07564400c1003100f03034410310549940c81d100701e03070911400345084002551080080c00c00c6200e014201001c0c1c040340c210b462100105907100e4004050303142e80c980c0400d42c0390418468826100d040c0900d00d4949803141032030314291003000300300b140d000c0d0030058a110040c14000d411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 99801537 1250 99800287 99800297
    0x30804110402130303030c090f050d0501020c010c02030405090106020312011404020705070303020f12070506010303210c080601080c0723030f030a05071803030806041112090c0901210f0201 83
    0x61a115160350004010f2000c0c03a80071501220b1035403400a04a560003a00d1004009030003005010b5030181039841c8048440440c0c0024540302142016030080c07240c135079056119840c0c20300c203090035034011001e001210406c0302d884030140c0c3d1300c2c24141c0c0c5038070682401012040121005005a224003260b00442c1e9002900c014103100d400d0307030390924052030340d01b003940581d11480180c1c1c0203480405c0740441c802903200b00729017041600d540c2ca690314003040c0030007811b000d1100c0395085481c000c16641d14000c480040140000c4580c005c02904001041c3c0702540000c0f0703c4000070f40b07140340b0501100c0c00541e000001d0591a02e10400ca041c4000044a981d44075000410084030303e095598041e5014450f981000030711401d110002030101d031412a105c26000c002c00c0010800700c5e420007900e030340c814410751380414603103000b109200380f900c40c158148080348449130034019020f10015484003500c0068030102c9071340e600c603020020002c2a06d4020300f0101508000f02c0002102c2400e4000c00e284107040c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 99802787 1250 99801537 99801563
    0xc06030a0603120915020a020f1c08040b0309120a0c0209040804180501080705030d02120a03020f120f0601020f0a030e040e0102120709060e0108060616050601090207031713030804 79
    0x20305441405002e03c5100254039220300f800380304002a180000845070303000074444454180d010803080503003204028030900504400305d0003480341e640790041090307105154503a40c80d116880b41c0c601c4e42042c0c42c3c9291034402d000490300710a01c01c8080301e80504450311441c40c403003015820071852030780c0144101c400715024000007422100c0c5c0000d462284180c000042015030600b6420342c94900c651340f102d0f220b5400803e810800c030360007241384a04d0420400c03c03e0382e1204080c800b0f134083d00c6140c4014240d4a00040c01c8040659a5420703140a402e610405d40305a4507a4801240c0d075107a80c040041140e080030000800080c02000b14119400c0007810200301d0030034040040d801ca8112446080b0040003080402031810742c811105406040d050802143d0715180c07100080620328014409409405c002030711300d540309800001f1202c855400000c135540c940e150b10701e20000c0c2d005514114082483c40c031003038180c5200c44c0e09061051807420041d205a4103161030071100100054030584d068018410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 99804037 1250 99802787 99802793
    0xe0a0504020f04020310090b03030a0906050d0e0a0f15090c090209011b030207080f010c05090f04020d1a011107141c06090f03120b030607141c050a051003050c06030a0603 75
    0x245205840400d00706c003c07280303400c010f6010751b12034003103051007904200000c44145400c1081107003510b41518103542c955442d01311000003044a190031a10074800c2c030780c400042004c2c0c1017035402954861801d0f4490000c600510105580048500034a1152401001d0041e034540c0ea0240190ba907052610315610034041c4804211a180c8090650068102d010207000c680810085045207402a90082141c24541301000741030380a0b070b18200344920350190301c200480da180c0d015a0141c05181d1401c108907100c81c1c114900041907030002c00d0200300510781ca28510b98000c05d641088491a503001c252072940c6030b08125212401c0848480f0040c0022480000300384144a040d0710a4414141210300740f440703082c050b20800c0710690501c0c9142c00e0bc24111941d842c04150b15401c0141c600b004811911500c4811780d160041c2d0103218811030b5a500d0842900040d604010b002d440141c40411094483d040045030354905800050310381e80c004107201403a403c080000315032110501000040030768480d6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 99805287 1250 99804037 99804041
    0xa0e01180f0b03070e0111030702090411041d01060801090c0b162102100209011d060c1f06080d02060103080918010303030509101b0c08040e010303050a08010b040e0a0504020f04 78
    0x1030440c001110b404010007202580002c03113444078242c00d00b060b5070780d1806d43c02031940d60311850000a00820700c010101c0d080041c01c3c07048440300e880051040c80090361140f402c01c3c014450341c11700b1640b5803d001d800503910a040c820459415009410313242103e0508610312201e6000c0f80102c46552044442c140202c0e2000c1da00050140300e012420720300c5138183c1002032608102e54010309c10710b88100b200d808180c0e0410301416001d4078204e07480b10b045040c9400280b00d4047d0040e00211380c01a55101b5400319400090144a000700b1082080440c3d11456050f540308041845440568056401030002c03444880240c05400f4009051001c0001c40c1c8000c080c0400081e4400c4006c42c3d160024414406014810250a4031350300c10200a00c018040400303036049500052181400350b010366540030300084104503000340a0003a251005c07540d40e0714000b0085d80c00303005500300003480c400011a83c03903100811101203e0103c02d402c00f080e00da0800300e0300100b0300500103c1e84101840c0c01020700b903d0764 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 99806537 1250 99805287 99805289
    0xf0215091011040315050c0a0807020a12020c1f051b010609020403030f1d0a09020d0e061008070806010e190209030607110d0201020918040201020712050a11060a0e01180f 75
    0x7007105282c883c0e10390314003400910038910700325081a0170401045110142e0302c040d14004607040c80c0c40c60715500d0700903080c1d040c520400e0380a800d143c500e644500d022070700018044801030060b507403a40400c41c12000c50030705143c5210700c0750010300100561203800c0e10100b0b8202003840404000140c050744c0308011070490b07000341e004901049444203490510340d00720f44900ca800c90003d540c02d183c01101d60004144400501440342966404140807001159070f50040c55000c0ca1902211424142a81c03140d0503200684510101442044d401003030340000403801d54120f03241c40501040540310184440081d0b04079241110140d1303401d010f900b43c244d80c00c010b103a02031815030b00c55500c600382c07041c5c0352410700307592040c0c0000b90780c010880e500f01342d2a80c10b6803100346c01040150003000d072502c0c80100d01703140091748002140c804119041c001e01101244c1000c2e81845030030300f40304008441080c4803540c090010800003040c040100350341254002c10889041501031048400340c0f90301c40441203041112 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 99807787 1250 99806537 99806561
    0x506030705010c0521040e04110f0105120408030c09060403060209090903040e13020d06021903060501030905071202030c151207081e090309060703020c0406050a0302091501090b0a0206090705010f02150910 90
    0x107842724034a1504086003035039000c10003840d0642c6404031501c0c0800300c20001030301c02020340340d0001c00108c80c510000c06035110304e07400178101030b9103907038a00b0301c00081e4011341052803061901c6008149000000070442e412030302c0000e00d0300d500d44c0c0c41d01040180c0c0000c0e60401e03a0404114070b4440c0c00184030303100610800c6500302c0c145008240d1000000d04035100c50704128180b5240224010105000043c11412580958206601d000700e0303101013800d2101200c40c1c0c9800082100c5c0309040c131a2420007800701c10310000c1815609585109049a42e24020b54403003444003000c0800202c00b0b101450f03d81c0e800ba02180c2181e241095000100780144e11404040d80107070080008501d01c1d15142c05110003e000854402c62200e0442e0001940404050310000d07012280a5039081c01d64045e94182c0700612460b4a10394841c0704c072000203034a07000111380c8013440e40205203000c900c0f5030140c0451030741c400c860740c0140040c4c82007001e044507020014040300034034440c083d50900342e041e86024005214403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 99809037 1250 99807787 99807803
    0xa0c0315151e0e04090204110307082d0708041416030302101103010513060f091a01031125050604060905060903030912180904060506030705010c0521040e04 69
    0x80185000344041504140744180c0200001d5810200383e100a900748421011900011070070400e100040003065600039507901c004000c03007008552500100c01c1440f0790f41c28442104024804550a007118038040b8119510310700100c04a08028424030140d540148251070081c60100187c0c01c503403a040c40c0c100c0100c0d1075003880e0800e0042560610240090031804c00050149641c10a189981c5010500840780540003c1c46a80f0024025410481c000c2c82c2ca030700c00c9402aa121078020020300208004944035090600200c030043d40320380700300325920025088040c00c0905002d606041e6038044400c0c40d48860b01c014822002c0b0b0000e003c00c6d4040d43c415040001c4a940ca0314003c0c4c1000340003051504035400601c10405090004260701a10502114400d6601d041e4060b04d0740390380b480d007204185c00010010811080210340c0d4400c0740229422422a2007a5940c3c100440e5040c008150003050b50f04098840004801a03001d2030420b1b034140000e81d4103082d1208841204100100d4007615550 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 99810287 1250 99809037 99809069
    0x30403120516051f0905070303180905250c0203060a15030b0901050a18030c030f09080118030905101704030e0d030224010305030a0f090b0a0206010f0608040b0a0c0315 74
    0x4000620ba0781429813000e04c0610800f4402d4464580ba4691880091b0511046110402c3e64020300400c0f03c019160b0024200442d00700414030b01c031584c0004c549106000c2c000078a441c9001d0246a440c1130701d070f5004004200f1a5540320400015020044051407030340287c88012001805a81610b03200340515400001c5030318119040805403668a00c1d15034003903c1c00b40840001c00d500c0f0010008850b0941001980e981c0600400c55041c0c1c80b543c0101c00c0f44d46004200b0f030350719094019003510355001c3c1d901da248041d1120104285000c1c140600310100355402c10041a00a01082041c5d00501a05011010001030340204081444110003240141c0101100c0043e03820400f1004860303134150300e040c80d8158196590240d480c802c2006038014042c0800788040c030326200796001c81c050700b824078449450720940200655181801e0041c41118044a00007003030340c5200f00030140c85503400411a010503140c2d000c1200c0240703602da1801c0f00701525190300d5110104495900d030001c0010416000c818 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 99811537 1250 99810287 99810313
    0x30236030d0e0f040501050307090e0c0904080903070e07020705040f1103010e0a0e010203010e04080313080a0c06050109090503091c061d060702010504030806010e030c04050c03160306060203040312051605 90
    0x758900e80f61071241d45010010302c0943c80029104007900c2da1490300048a00c10402e2103490b240301402d100c0c0e03204a4806c204001c02400001030040524240d00311086a503d548220000d10740032a0902c2c0140c1c08442c08102034505a0080f40c021089840002810042c005004880364401d0b00140e000460110621600c0c1c2560303c50842c512540e440210b00390f5040c400854207900020f400503101a80210119601000d84008144010392080c05281e803480d4a40f80500042424207080e0b4a031031400c0000034090045002e1040308581c0b1402951404004038100040c1300c2d0101254080000e016000000040c3c8520070511241302c1450345c003600c1110400601d2078584020045021641000f05000029030020b0707909800a409080c41e45801420102192901e200150a00d9101c0e040c0010701090080303401c021809400405604080300d020500c09a0580b0000d1080c0c00059100300420000f16042c0301c614545440d02d80743c010306e030880c0c0035400c6982440e0120156201c4d0400e651034004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 99812787 1250 99811537 99811549
    0x20709020406021e031201031b0e06030d050a120509030423130c0e03030d0902120a0b01060503100816090f140c07020f030a03020c010807030236030d0e 67
    0x5044280040d4582400e02c400207441c4c4010703000c540d90703003100c0700290701c40c2c41e0091098500c120805010301c181e6695904025082c1e43c0d44101100c0d6210400f803000c100e80314249a400d01c00c0c1009002042c00c0c03844a54110344607480090048104400407071520343c1c410043c0105c07805200110000d617151410000070140082403543c54000c962089100c01c081c1e51a5400c03080c2d40c54814101c005858040d151060300d02151859107613902d0700000910f210003101540c0020240d03402950362034100394241104540d101d07820b80002d420303000003500411295214400a55024140b0b83c48800c3d00c0d42d1b544005864100410350301c09801441d1101403003081c00c40d1051180340649400140502e0040c0100d0030310020f000b030486107801400083c5042551104802d540351080094101c0d9504a03550600945490b0580c20325800180701c24041460b01d41b2a009483c02c5101c0c154558420100c081c1c00000900411300d200895003800340c0031030b68680d9041c0081c03100503084da00d402250f03192000c10000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 99814037 1250 99812787 99812789
    0xa0c0306060e01030b061908040c050f0114090301090804030b0a0b06031b09030a080c150a050601050301060c020a03060e16081b060703090504020403030504060f0f080601120603061404030207 84
    0x10189000e00030032046a00c9150040c0c410001c1c00c0000300d19051001048a601c1030f0b03142c004269800a1001000c06d40c0724005c03a228034003414000c040b40792600d0800880c00011492640020442c2c02d142480d5100140101310401c0b00400004d980e0041b59941c0309650450f40c000e86064000500301300019501d80268003030048210f4625207107141ca038000d1007806925040714510601c000c50010b03015202000074515454002d248140c0311824001659602c0e03051101d00110202840701141c10010a402082d00030712050310350a046a007420811242209a00380a070703445002c0f10030000101d0b049210b800e06510010001d850045154010b02c3c4104c1c90710762012090798084203800c424023110440d03a0040c2101100d1599480c445414104ca40c148030390042680140700240020405410500038012151a03441d18812180809020348080054240100100d125400051076540c0f088204042442051600003203054413520340c54120b031004813a0308c501c0346040b810b100038183c04100c868 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 99815287 1250 99814037 99814061
    0x2031b0f01080708070c03031e09021003060f1703160b06010201060602060f010e0c0705011503060b09040209040b09010935130506030c0d0c0924050702120304030b040b0a 75
    0x81c80c2c1d400c180c800100b40d800b0080c405400c0020b00c0c0181403c151107604550504440a100b20040f41c0740304051400038100da510491103803c0c020a5104614007a01900041340c141c14484500c0038502441d145d150b0300030701054206408104162404900c41100440c42030b0300800041c009841d11130f00280c2110566081803040d03500c00c0c410829900202c1211030305643c01051203801d1034480d41c01c1005c0e6401601c0c001090b035404c01e001c1d0030160381a90403250481c0e004140a110f01c600300c20030700124207000d80b0083c6d0003481b0040000c0114000c5c0700b100303070084546d07000082d42e05481d4580d04841c0d542c000901e0480100d055046600c1c0c8007580f00220070748003e02c182d034a004107010364807400702590301c0b07094024040172000659007007041050302c002404407503051089800d1642e00400300b102c503004148011500c0c440c211002c82000c05401c58a80168403480e181140640030441031004069500e0001e10003004007100280d038400860b40150712507104c0b01082c1c1002602502aa00494801d03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 99816537 1250 99815287 99815297
    0x917030d022b050a0e1b130605030a080d11211005040e0c0907020d0504060c081c0507020d051c0506120f150604050f06010c05120f1803060105061b01020702031b0f01 73
    0x11000c02682c2e0080d480c03000b0000c45041d0002c4d00c0002011f00903084030743c030441d49400395a04040902c04814000e150980880c0000c1120b58540e9070300d00d825000b000ca2080100e11010105101c0c1220b0ba48030580025028000a000d581d54500060584100344c100780314a81180188038a80c1c200004402d4025545001510748600200f900408900861283c3c0040024201e46507052016010481c0c2850950100540c1031041480e420800341c0350940c0d040c001482015045081540300750143d0328041d000d00501a0b4200c0501e07500c1003d0b02d00602155804880030300c504a12030380800800004c0b014940280c020142c0d00035242886501c01441c0070b0155052030200b04024500203102c1d580a032090800c07007140101d5060075454001000d04a00d0140d8001400148007002103014200d14041e00314106000050b41040c9034861500f8030644d40c1104080c0119129011a4121042ca40c02e8440005003820102d400203440d000510110b0140100c40504106207802c1064913212442402c2c204 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 99817787 1250 99816537 99816553
    0x3020403030809150c0d020706020a0801061d150a030f14090d1722060e1c0309110f01021213260706050c010e0703080a0917030d022b050a0e 62
    0x100074504130014210344903114005415003015001d641580c0d012500840110744a2001c1c0402408012080c00780c80041100122089406400c0500c504c8902c070002c0d02c4480318180d54001100d6641100318800203054543e103514611104921515003450600c4100340220304289801c282400c00448041c003c00066414a082d55602c031500507400c40d070359850b03440d41368950429004080c00741d600c0007000e5034240201c1d005243c1c0000340000880540c0466850300f400034440c213404440c503ca500030000e0207003240c20042c6141101c0030314240d40d01801074032003450030319000100581c0070407420740504251030f80a000300031052034400c03070601c4042e030080c40b0620078900c61581c1b000d0b180304030b2042080021300c0d400d00c1c00c4290000000800c803a030403180300a0b2207288c80703459604280b80300d82c0091800440000d85910401c404d44c00041d03104051403420340742c2e80e00040658021058940c00080c14100c2d028801581107035a100041d5429001400d801c100b80d0f600d0503103005482d81d002c02d42c0f186c10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 99819037 1250 99817787 99817813
    0xc0b1f060f02070608041a090f06010902070203100e0c0306071d01030b0303180406091103060f0108130b0402030a0b0106080402190506041e082d06010b0405010309050c04060603020403030809 84
    0x3440340701350380207818001c1003651289401c5000703031109092103007a07000781d10500601000000f0344003c090310300b005507201c582c1ca4184060487c002c020019504d0307402800b40042d44d001c0c0350301c03d1030201d004c8400c5d194104410f401003850410166200b000040700c0650040c650403200703100f00c6a4410034a41800450380d0500065901e00400c074543c004606082100c2c01c00342d907503a00503001809403080a010030641c0380c1051030190400c0340d03602c1c0200e041e90200c00c0c256108080652103405030034240b0780d9110341900d4829244100404c1280c143c400d10264001260701e86800e0380c000c108966510f4020f1400e40b050001c0c82c084800490b681ea40f4020f801d0007295240c0003a90103860109183e0400c00c655001d5000c50f01c0d0b05684159118010300c100d5401060000c210306014020740d400801c0200e600c1d0340382c556200424802c0b81c40300c2c8030500043c450756209801a1040500840480c2e400c4191500064103c95007540001c1c0442d9001a08108050b08940c400d41c1c0101007001800d00c8400d145 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 99820143 1106 99819037 99819043
    0x3131203060f12081215030a0c050f030a08090d08070b0109050417030601080c0702040b03071710020f09041d0102070f021503090a060b010c0b1f060f02 67
    0x7400c0030401201c4070680c180d07143d600181e40752030000201e501c40a0085c02410026400110542ca545c50743d13410031802106900032441038a407180350030b00b00854295440c15041c0642c00c03280d580000f1681103020350350501c01c1603d080030100840d1a2400c83c0344680e06004240001c81000420030040d02d0780098884c038411040c007007079040d003070501010500003150403034006281400011600040c010282840920203000400c054100c10000382c00c008091300300311002503103400c40c240c104800300035100108100300021460031000e41200c01242c0302e000d403940d018076203401c05162036038840b41d480d1428086140c02103449a0652030803141600d06a441a40300358a0b0101825185e101e4030200c0b40215940c800078810303103450307030741d0b920192001d2803065040c0014000030380b020819880d03001c1e12611008c101503280212148801c00c5c517601d02e40101c8104044100035400041e000 = true := by decide +kernel

theorem cover : BRFrame.Cov 99640287 99820143 := by
  have h0 := BRFrame.cov_init 99640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 99640287 ≤ n) (h2 : n < 99820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
