-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0724
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:24:48.998211+00:00
-- url     : https://prove2.me/submissions/6196c0cf-35be-45aa-8ead-26945fb95718

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 130035971 ≤ n < 130215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 130037221 1250 130035971 130035989
    0x903060a02070f0f1103030a08060108070212250501060803090306090304061e1101060e09070b120112170309030d06060201051605030a1113030606150504090216140a030801 76
    0x100b410300080d24007003401e00f482c0d00700181141c030700d00e5805e14034000302c0a03000f0307154148000108001400c2d00f020b2030a108082c241c845c980b5aa450303c0c0142e86940309030300507080d911401c000303403055002d031040076881e841a000740c6d82c500c00030380396500b9084a02c82d4000749c02c194808203600110b49410010a03601200c03d0340a14140791a101025143d2100840307002d2900c01d8400700c64051600c00c1152102540c0440002c1c0b203500d070744280140800800343c031030307016900400d800032800911100882d036400c2c8500c0341c0000c242e882d081c0001980282d5580403192951070510000d2881110700185005082442c06181d4600303158120a080700d000ba032007071065904044c200990380034120005c0a0b504042d060080da40c4d41c40b140290010701800400c8640070318080350f0b403640100d21041d06c0d000c0d00c0c4681c01c100803258440112034101042001d5440010348100410300400c440e41d00038100c0d06030304450b4464141440e0b51588110f80310340c031020341e1684c40000e4142c10b0503403100541d401400031030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 130038471 1250 130037221 130037227
    0xa020f010507050a0201120908030411010e0406030305220503030a0f0e0d15090309050a030b181c0c0f0812040209070f05090105091c050f0f060c070b13080f0903060a02 74
    0xb0f0707030f426112a40e6801c0a0b042c03110842c50510f0304141e170b0700b20003040355011003c1e550b41d00e450720302040c42044c0c180703601307000501c801c1021710207007414800d11041c0d94254903400d00700f00c84600c001d60400100000b15562404400000413144c50030000707411100d5194a51101604580c41c005000c1c4440c01c0189102c3c09040141d03201084045802c05c10240c0341c018081219061405c00766441c2d801944015004401e80c0400030a004845002c44d00413001c002c0141a240e040c100c1785a0b0781c410a1403c5102e14030070780088106107010340203245d8610700ca42c0d403501040c43d85803940e03401c43d000014416030000801d01003204518006c007400385d0084141c20813202100d810003006206001d83d4004030305114001a0340908ca41c1c0749000404268903010103c5102e10440c0792103901c4040d44e1075031410a1240b0130705080c04003c0444d26a10808404040a081030020340328605100c04c00380c4070480b00e2460440200216020000030002464501c3c01940c0c0c960307200080c90b01c1d1003001800c80342d40d14814 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 130039721 1250 130038471 130038473
    0x201020913090c08030408031b0601060f0c150212010914041113090f030c02030708060603190614090c01020d020c06070204020a050d020307030f1b0c08031b04080a020f010507 77
    0xa2122031003441800d12001452294620f800210003040d40c110540724440824001904000000107160502d18442c5004a460a0303040caa035030b0f40c03400c0c01140c01240d40801003003000d5114051024240b070041c40101d000280030400401203a202c043d114411f03601c800e005002d010b109000d406007a41280218030f4152801d0340b174070700d90001c298a00511502c41050741c0000a0b1950b04909000e07900800e920030041e0300c9160181c00000520703422802406100800140f4110215190348200c60140243c0141e14000601422a11300728100700c50440d5501c0c080d21801c500c01401c01d00c1800080e008003043d80700c50002911302409a03c102c1c08550144296504c5078a07210142d0b209035905a40240e161208001c090702c0301e015a0a04c84140e500c08400c110000d980341e00480c0c3d00035200e5104000091801720f9100244031255403050100c2d00c58901e010014a11000644d440000308140d00c0707403401c00350f1074401260b01c280e000090f10b0348001880815850f060200c5001c80009090030741c5881d420b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 130040971 1250 130039721 130039729
    0x60c1812050706030507090e0109020909100308040b0702061603210e0c06090a080a0f0b0c030c031609050d0c1401030b150f1303080d0b01050906090f030a14060708060102010209 78
    0x240340520781c2099100e078041b5031303114001d0881001030310f007151540c001e960312400544000e40001d000d41e8441c2c5180000b180c112580001d603e800c0e2600082c0903841d0034180800f070081503000341001c0383c000700304110036407080e440580c100e411144070b43d0f107003080c01c03400f80100559181c034581000da0f100e140c0b10700c00141c41000180c150303041c001600c40e01d8039805100c00203210000070394007041e145c1c0603c0501c5010050000341b8125038510640d0002c0c603603211014510400d010450fa950380707100c003c0000c1181114103642e00106c036040303072505902091700c85001c40d40758001600c1c210345a0703142810900441c0554004420350800030b190411042442c1000110b00d8281070000b141c5d00c250008940081c5030400046800c001600141d0b280c21980d20300c1e114403154403851030324210b1071912001014940c86101180c010340001804070341412101070030000e0500c07030f483c0030561500c500040d00c00010382c91181101d841e0600030180250f4500301070041d18440005000300e0443e481008041c04550b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 130042221 1250 130040971 130040983
    0x41b080a02310803030f04051b090601080a090203010c0c05010e120306060705071a0a18030309090e030d0510060807090305150a0207020d051c03140105060a0c060c181205 75
    0x2000c058001900c80b0440904480380c2c010b403c02c2003240030000410906484104c900c9000c2c500c41c1d03003107980c941d88d00305181c2c012800001199500185440c0070856a600c51720b401d540041c924100000c0e80101540064219100000160040741035a9641c1040c03040030b104044041611202400e1030040d51104102240300c01841c8500c00e039408146842880b104100f45409001c05150f40c0d001c50315408803511a80e0051102e0303400040d10700c1141c0403034a00b50810402183e40c16202c2a030030500b17103a09036000c1c01400d000040544030034070055102c42464040d090055424000502e0300508000f4020181c2c00c00600c15010310a80f0041000090030000d0030407040d40b0008072200513903e842c070800d4083c0c0708281002e94003045000020003031000c0420f2980740d850000d082d0750100d84941c0015002d5513045042403181c4d1200f040100b0150500c1d030000d00118501d0b24103128044800d0342d40d28100d4107220140e82c00220004031400101040c201000080c2151003d1840d0790046030ba11560350351 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 130043471 1250 130042221 130042267
    0x250504110304021c1e0c14011e0e090c070506010f0e060907090806070809060106210203070318060c02010f0203240109080a140601060c170a050405041b080a02 70
    0x150010400b03043e01130118104951940316180c400c07242104503c4414006108509442d86103108000081d5003590180302000244113840380240072000b80304a03000c1d020503032144428060050345031803043d076840768018440c510410035652202d140f03042203031505205070041c441400b94a0000c0c40010100c1107540d505c0741c4203c59101e52a528042c04540106141c0d01012507407086000b4024081d4001400307d00c51642d6008461080c0e90380c1004603192001c81c1c5d005154000100c25081410640760011940480d0604000c640742960195a800328130340003c080d240c207642d540000d980a40e0a004039001101e00c03a80035402c60500380140700007003d804851950610801003000c3c4070740d000c0c8140400400032070b41641c554021500300440c01116483e0800340900641d00003191190041c60f10614550300020342d01c011440742e10112007240d0080c040340080c8041840f0004280c0d40d44d0044c02d612000e144045281042410b10141c002c000c082c0c12900c0050040c07004440c5c1c09000c5180d40d420f4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 130044721 1250 130043471 130043479
    0x50d0201050d020c071703070b0601020c01050406080c130815010b0301030b01120203010b060c01020408060112030f110a0203070b0705150121080712020d0f030207150f0b0325050411030402 83
    0x990900b41340f2840c0203260f60110441088403180350581460100140c5195030148442040c03503500c0c07000498a4040035110140030581c14401408004d201d40c8050b80d100d048070040710f2401c80c064032075200d0b008807640503080d41e80c0710304011405220441180c03401089001d00701421541990303200c90038548140100c010036030300c50400c50190b680075007210040e202d010b0062a41d98a00b020b001e4041d50050284116a1151030000200c40c02000410701c4210740541e2444607050340b8450445c5c403420107080e40d9005104090783c02c40580d60074018840200785100c2803a999005038500b19041c60510407151000f122030100400400001c08110307449620390780381c0607540744074524120005000f0000d001e00008590340301e05900680004000d180c016207900e440c403040d07034500780840c240d03c20f107100140005d54030b0001e9104440d2070b4000106030400f503000495913107103101c0407034030703101418121094204462040561803094404080041c00003a10140300710340c8c1800c1c10001501c0090030090103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 130045971 1250 130044721 130044727
    0x907050901020c040911040c0e030a02041d0d09030303060b0910050924030702010506190504110408010e01050a0b03010e060402100c0b04030801030b0a0504021011120c06010f050d0201050d02 84
    0xa142e10a01c0f90f0101450014010042000300741822400000444096800b17035203030648030b600d918003a042d11080650001c008220b01035156092102805403483d110072004410260024100424020911400d0342d035a00c00c2111803460a000341602c805a0146801d41000c021203682c580303c42c0c046801050301418003e0340c3d002c880c80801c003404c14403c4040815031403400b40d800351100c80342c011405002d59a000740510340380c180c20841001c0b240c0307a501004c0740742600104994241900600c403005101d9607203508155555070321900b50343e44403000d03030000d0750755004119056000e0300c19807a01100a5000300000007020900c1c959404014001900c1114501c1000d8401031084103110081d580c001045d600a051915000c0c0c85018207000441d10302c25120001b0301e8038851442428402c5400030400311181a00e18030a40f505415008050300c0d2b40509107008400381f814600501600114400410003980b425903c101195660b8004900c0340c0e68080f942c0004d40c1c0d202003540c4090609820040e6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 130047221 1250 130045971 130045987
    0x305070509060f07060b0414160903060f020a080f0105031e0123041716030e010c0209070c1b1413020d05160e1818010b090906041a06090705 62
    0x5818011010078aa02c5034000640210b01e0a040000d000c40e988900c00600071140001c0070001030311110300c1c4211084403007500142c081101c20600c103464840c94204103080a40302e484943c240d0310744020300110a900024032121041d4403007403180e03000d0a0150003c009504000019488054100703a040d401d00110400011600f400e600103600c0300c44034602410108100580200c40620446098916510702902c900d0401c0b107090840b0b0645501814140300381606580540d40080038590803410010601e80c8940140c6807a2556030083c1c0d201c3d00c0365102480646410114a640c001c0c0c00b01c07080c0114141001091015403a13420605012540c6040c0a040850200300900032180c07004100c0741400c003030000c0780a428450b40d4003000c1310f41ccc800c400d1a00e00070500c2000f40042103c2c01d10b007500030000038040544480c01e159542d401c1c0c0004900841080c000510744803081d41c416940d0b8010754140020801070030080300300c401075001401d41d24074001001504001004003440244000082e0044c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 130048471 1250 130047221 130047227
    0x50f01090506070309020f0604090c0f020106050105192c030705030f03030610120f0b0901050105120703020d02090a1401021504030206011404110d0c0207120803040f020d1406040c06030608030307030507 89
    0x7d210f1050191106448175540c41300100649075440c402400301d4070381e1904018251043c002d0000303036031041e100c5626003444e035003410703046120b40c1280ba4100040000000d02c60180c03600c40380f00400c2e140e000304070b103480c3c00000c05091403015803006109070f1258136458803900010041d40d62182c82200c1c1041e00c0804020241c507090b00c0d11018915151500b214404030002c29404540450800d903501401d9a0708d40005546510900380345850182d03045002a40d0544603030001c0c16101482030000d030504540101013110028179400c00200c0c20720040c0c2c0c1069559040051000c982c001400740001030400f074801a403130310418040d00d058107910700040b40c0702c1e40341c0e83c100d0f086107000741090b030b41d44901ca8540c500050660201d4030006005501001400c0400389010800b11508031424610b140c0701c0b90351701c0ca040a0a1401241c1200c0414081d001284025000030030981c0008050412841c05150803000c0c545980c20802c18549025028007410400205803075101e8a6420001402d460341d010603 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 130049721 1250 130048471 130048489
    0x50a0914060919031d03010e0d050306040f0501260c10081006050c0705010e03010f0603030f090b0f1b0c15220e0417120406050103050f0109050607030902 68
    0x10301240c00400410329003800001e0319901c12003542d800d03900381550102038104280191000500002e0958103090769046640e0b18091440c80000c1c000100d00084800441c14480b40e41c04400c049400801040a58203050090300c003c0700e40c1001c1040750b50b0411404038044000e05a10600102c2c3c6500322142c1c50318200000051400002c012458600d0184d0004110030002c0b14039072031022180c5000a41d4034010b40584017080c21081c0034010b4641400011120b106405104603071664981d11601da0010103031140c040514001d40e2650208a040103014003183d409502000d5031700d03000c10041001d06800c0d400c0d0380b5100c54000743e0a442e401d00003209440c0012941c1500c3d80110b8030b904000c0300c1c0c0a030000038441c440c240300788181000d10500403082019000c4c0302d400303005103080b0002030010f41c14201303080001300c1d950074050134442000c4030142034280c111000c031120381c0e46800510900c07408000c0c1c45280880d840091042041c1755032525203a03a0050000014107840382256001c540d44e041030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 130050971 1250 130049721 130049723
    0x10302030a0f030e040f02030a14072703020d03020303071b12082802041401020a050c100504090f0617030304020a0501030e0a0506040f0309050a08120a030216030c0c05180a050a09 79
    0x148411000760030b40b1b034003e50050344c01907021481c056010104003072407800a0f1191420f0703100c005502e800c68920510203159040700d94140d61703000901000580d0f07203000003032045020f80d000359100d00c0c29601c05490050706940c201c1d20001c803510700c1c000041107050281c1e4681d11500c0c2000958480107640391445a40003c510460000750901c41d0f1900c615038050030448000103c0441810010401039844640c030b1000600382e03820280000445043c44080844042e140d1301d4014038003552420b20320300b211910390b4070180340d40c4c6078081006815080e80919100f410010003039890342c1499030001f013200109208040c10f141d185c0c20750301d401e010140480fa01c3d80d1340100546480d4a4185030008143e407111200310040f5040c4072003c502070408101c2601940c5907078008182180d032100c0d0101c09904074000030010160204001703000a10800c14480740d40d40319860304450b111003460080c41081250700b010740610072814a01c000005146410398025524001c001503a03220007026602800e14000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 130052221 1250 130050971 130050979
    0x7030c1b050d0210020c062202100201050702060109020f09100306090204031b0806040302060705070f020d080c12030903070f17030106091d0c070201050a02010e0d1706030105010302030a0f030e 85
    0x2115009208000c12051090720066081d82c100c03020010752131040780500310101d10f01d0340c000d60014220242186100000104888174402e9074031142d40060141482c1141798070060b5141d00034003032002d40411010707024150b05070702903007001c4000c1c3c50b00c074690258110440c4038a12540504801c2c40c080c0e8060b030054000c8403015582e0301c3d103c1c203180d40d030103100009200705c2101605000070740340b902144140c00b40d98103902412091301c03414421121a0000300044e5000c18848010700d005031340b0035600120803442519560f4850b18280c0c045400d02e0728a1407d402201020410002000c0000c012200c2d025842061301400000d58208001445507200322500d50355400800460300320f4000004608865038114a180030703020106281c0d943c481d0a0310554224402405810019801040603004002080c400001c1c1d01001c120014940001c02940b20085841030386000c03041502011000d5000100394028403255242d60301133641ea1508407409464407166000c9401014071030391030741020641c010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 130053471 1250 130052221 130052267
    0x109030501061e0b090a0b0304080c100b0103050f0403080c21151201020f040603021809070806030f0c093103030b0f030a17090607020d0f0203010e0609030307030c 72
    0x5080d0603040f82080c000300d12082d102d00000e04862004120740d4680720181c14500100d1600c82e54040c0782d0000381c01211001c1041c820114800c0c42002840c1e802010084041940c0742da007000542190b9018241030452140d08041101007500300c4201504040c0b8210119520b54034205440054041c4520038980d00d20824140041040c1800ca9000d003101c1c00c66200d81600d401000c41d500300c5c42180e4100b44007a6003444204080c03030099000c1d00f140d90a00c40c580d06c071a00c0e220005a082441180c03640003044c55901405903508041002c5000c94031854024581b03605c41a0014182c1b0742e0007444004682000c1d90703003010054202001901e018401020101001c120b447d0280107490394129a901035858405800300610300091402541740d00001c50860340c0300b40c15541c65940d4060002c1c2c68202c80c040000d0001600d84241002c802d60141061462001e520b104041c207490003034583c00a103903c80c0040c001d0420300402203a400108508000400c8100314100f901c8034411311000d003001d40403076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 130054721 1250 130053471 130053479
    0xa02060c19050c15043f050a060e070f0e0a0905070314011a090406090203031329040602120901030603080c1006060906170402130207050f150408030a0b010903050106 73
    0x601540c100c0000c4856503000121303160740501500803403150790101007031001d0707861070342171180303155411055601340c985521004092503c204d91145da0048a555201303001d0041845814494864440d4002010f00180c07440c080b132842c01c244150052950700c28000c00801c546016940c840e01c100d552003402c2d1045540d03a402c029664040130304a00002e07508200d045c2468000d80712030b5000e111001008000b4a0b1141c0e11034800404070044220b0301884108840c28004800d080400f000701004a0180d600d090000724440308000c60601c00714044000f0320041c0800307070b008103202c0180381e2400c5c800c940710400c060048000d018030350700c06402031500207811907050b400407a101d005003452030710501007180d46060440741e80b0403030301c512800904c80200c0c02c0c085004000525030028001000d940c560344007200400b0890380b03c484100e0700c50f400b492403000000010300841039600448980142e042c0740c15103030003500d444018071040790242d88400145e11607000718032100107903401c1002000700c0c68072 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 130055971 1250 130054721 130054723
    0x60f030d0c03080c070c031112010e0f0c030105010501050301030b09030d0f0209040c1103030a1d0d0e0117011d071b0b010518010f0303080709091a041802030a02060c1905 75
    0x51000507400101c00e10002010440400100ca621607401840f21203030518644a115030710119a0030070382e02012705a580070181c14240200d184030001c000c040c00c56005403900062502030092031050103641800c004000581c0c12000b45c03811203800042c504e5003942d8140440303041d4070418420344806842d212244a07a03141660260519801c2900c041102e4008917809603090043e03401801c45030742c000c01c0001d0490506802100c0001c0c2079000014610642001e8141444018580d4200040020000c44c0a640c0e100460300340215845070280c0d060b5041c80200c1c15000d1114280d030341020111404111024416010a0034410340015080c0c042e041d03525100052110030300c561b520403551080c1c0c0759000d410280c2050b040703980c5207546078480c620719601070351800ca009103410b090180e6401e002800715581e020341d8071025154800542e490301c240b02084102d6406582d10325800e25201c04410042e2000034109451540442e00581c440558100712807a00311694841404d040e6081d881404201d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 130057221 1250 130055971 130055987
    0x4080c0a0c05011d0f1003140c0702240a03020702152106060a020619060b0403030513060e0310050a060906180c050a08070309080f0304050606120c0f010305060f030d 73
    0x84241d032940700c0708110b44e01030140d59401c000220f40c00a007400340c491039490111201c1100400c6400c01141001c84102c008000740700c1240d1481058000050707075001c41c9040c02040c10184170012840c0d107007240b290200c003200e00454403210300385940080c140040d5900c6c06400264004840b20300c998815860b8502c04840300d40402848000c6110400f08803a841c2c19015a40d04464581c010206565810781d0f40a04c400d104046a8025136507442c00310381c1c03804840040c0080c50007612840c1da1000c0788116a00d0380501507000f2000c0200800c0c9026003030354086003030b495000b034041c2d0102d07a03900d81000c404010800ca5000c441028500034000030000e00d9024000007443e00c0303850400100d4400d1400755168445e040048000417207000000300190300a0b031000003118021000107040c00d10710b0a1085003584181d07001c0c0c035198070140821481e8079040e01da000298000101902401c100c02010461218101590170f042c10303103030800951a91607001181142c080300a0440d483e000e1017160141c01c80c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 130058471 1250 130057221 130057229
    0xc02120703020a241505101211032403060402130c120f090512040b0909090a05030a08010312141902120d0501030218010302060405040c03150e0702070e0f0f04080c0a0c 74
    0x303814940a0201e44205e4403600046610240200c0c207020f003c2401203030316440315070910f110107540c0c0e4005140c00350701c0d10183d482038160003088044071810026090714007132a40030252003039016800f04001a100d02d40c40003150034a00c1004101d20540d03400036109400e4400c1074000d91880c0c0404030070020b266402000c40c003405082520500c05003072400c0546031103035000e0161092801c00c41c0081c41d00740b000b05240d02c404004103442d078a03205581c40d5070a40c1d000852203000125554018418010b01015240450a6034200720000c0c03a2001194245c9008002110b4800071840c1101900d070340c0207002c04650b898591030503503640c003c038000c8a8001e140071b00060307009808003503503100c05a04c0c10341d5a50680c2e800511080c200303441c110400c4040d10358a0160740c1003603250705001042804100101c0d01a2011550410306d42c501103000034640700181d8404081c0c007002c0c1c02408411080e00c1c20154000407880c0020b41d640e40c82d400c2591a40c0f0480f401c103502c1d4403501d4808004d111911068606036 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 130059721 1250 130058471 130058543
    0xc091509120102040e1305030403051f050a0207030816110f010f05090313091808120a11070b01050f01050c0d0e1915030506130e0a060b01030c02120703020a 69
    0xa031903080001c078201d0040d8081ca801101c0d410f00800c06200040308100f0005100e203003100d147ca034603036a42c5818041c2490801d1580384454016006021140c0140c0b0f42c026100720085080c8a4651030007040e10308041c26a4056000341e450070300a4921542d40d601c0b4040001003201c01b12484010b15500074451080c00400052401c40800d122101c0401264050340d0300c2e4601c0004d50341002b80d0300c00107028070340d0b4003105d041040c0f46407800a80010050414600c0444115400346055000b0341706462401c441c1075808142000280001400c10140034103441c02501c01c2e0001c12500d100683c0d41d4817640801e44000e00c10049085612903110002e040e40c08000e4417031076818080d5410b02d40d41680103026030460100c020684401d050301c02da01507075124078000c0c90448a10b0740c07001c00c28121101a5500324098001c841e8401c1440214080e40161000a1800304401000d004000f234076407903030126003ca0716400062032002e162081200e0303d11a60040314001808040102200441550102104032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 130060971 1250 130059721 130059739
    0x3040b030a1503050a031805100e0118051302070503090301090c0f0503030901140a030b0a0602010902030106141005030c0d0f06080d03091e03030e070e040c15170c091509 75
    0xa028218140340c403c9a9000c00280200102c5542c243c03803034043d422014461050071503001500d507441d20400b00e500c4c0360f07645600c2d02e402001c41c0010081002d03011440c8039011180c1c000c10854503080502d87ca0405528801601e901c1355140c114110310642c002c160307040d82001c502000f031207171b00005002201c2c0400b003a074021580c0e64003030640780c0c01410689804505000123115583c2941c50080132601d2681c40c000403032940342400201d058485821500060b0742d20a00c0c0811030800f48500c002400742007030107040d840e1000300020780884120810108000c000b002252400c41c241080d901c3c400040041031219a801d5520100106610700c0781c61103074400c0c0b00e9040d036001d000c1d00c42d00d0034680d00101c01d074541b0340e0100400061544d03000741c21020550f443c0d00c2ca8060304410310802c405001007204000b0340317040a00740004581e07004e40000f00310a03a05100c0a8005030825080e0380c1074201c4289045080d0360341d01c030a00c03c1d40a100c0c0e9481d040f820034041c105001040e0001005002e030121a0104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 130062221 1250 130060971 130060991
    0x10f0b0306070e0d0201080621060106030606080c090d050a0f1b09020a020703200303030a0f0605150a0804030309121e0c050613060e030c210304031b0804050303040b030a 75
    0x9402c010702a81982c21182e001c0c141300c0036512400c040c0e0384c0108040c01c2c7d009440910000342c824035000c001c045400380c0111b00140301c1d01d039050003580000d00503440d140c0c2c41c1d414071008440b070622620340600d224000070302001080060501a00c094250032051402400041d03003011300000c3c00c2c61400984000c2ca4207404504c4844070310070f0342c0f6200e9a941c000d200b19411981c500c1c482d004054041c0b500c4d40c948081400c0c45a4040000b0352040b84440fa01150305400c041805092760000d811082c8621012054040400546c3c005d44203039803640c1c900450f070758889003416001080f40c17103405400d001450110b0010b098002e800940c4015500400a8189140350012030b003070148150020b2070b075000b52000c1105001c0492010034602c0c001c80b000100000f120300c48500c0e6a00c2080c80e251590014480190803007080326140e007020402d2002d41d807451802d0b6900500000702c1003105842c1c04038010390310701070100e0b100a450142170f001d400c0340e0366280c655501c40150342044800090384c9040050004e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 130063471 1250 130062221 130062227
    0x1d010f060b1c090510090305121303050d02030a0b0d050c01020d03060b09040209030312091516170a1d0a021201020708042105070f032f060d020c010f0b030607 70
    0x40c0b0100501420301050081d03150206000e001e039407209554a21030a107001800314100c2c800d0703614003032081e10740c903907991070b00c40d19800580b20013410b030201c070b00601590030080307a0450b0032116204103840c0010f0b80c03a640d0603001c000400134611200d8000960108000c1040b10000305100e03004000d03000c036402c07094000800c42c01d4503a03d01031a0000102407118020b142003507009003015201c0141070300c0c01e0100c031054040c1c100d40d0441b047c0c0c500354411f801e080504a1501c1019070441d4801050700d071010140800a050301010150003041d1000001c0014400003c40e07003d409603140542c0388112000b61442d0403035403801400404c2c0d01c070303c1c1100c072081401e41e0148200d0b103129070700031219428a8a40200c0e040b9484d100324061910704003c06209001513010302001e000b80104c0e1042414a6045042101280b00411074110a100014010b1607024402524120310000100c038150b5a900d04e03685642c010780182910005590b08086131a48803048a0700300702c943d40003d8003103c08556a6010032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 130064721 1250 130063471 130063477
    0x8131b0e0a0c140906040b0c070f08011503030c030e0301090b0a0e010212060f060c03030408070b150a0b0309010621020114070c0b03040206070b04060506031e030f0d1d010f060b 78
    0x110000c6154034080021030043c2c80c3c0908200d0500801079030416580300301d41089903100c070300b00e40950b4100303000903c600b801c1541d4131710183c046030008101e2882082c40b000d0520580e4000541406161035100d01054415548408100005002400007660500c0c013012098402c0c0c60001b030050a006880b01c1300d803014426200c2c0e02d101c1a80c0e50300c9541700d02c014070404e48814007010390006810030104c075031620708000a50085125003070b1940d030703146c1c141000000c0390000790001c041c0640808511040d55120362980e4181c0b644a03514558076111200403a004140c5d030b6120902e084000a0040c107070034981d010750314406000f81c86044010048240c07482c0c851003000344c0140f1100e40c040d010700682581c4c1c0302071580a0b1001c2d02c1540382c0076450b00c40300c0401c070007183d0484060303031a50300304a014241070055500400c481301841c5c2414080da01142e489001e034a010624803031000c0f502c8101c1000941188050f405040c0d81c8a40c03440c11070400034040c3c4407145200000a007044c0700041e40c0c0a8031011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 130065971 1250 130064721 130064741
    0xd1e0c020102120306040b060c0a02040605010302030f0411030f012a0903080313020a12081c0b0a0902030a020405040c05031f050f01050703030f150503120901080708131b0e0a 77
    0x2401500303155940c1d501084e0800b41c1140d4020381c0d1a04440703607540380c1100501e20000203600404001c03200e8810030040d10380c550482810140144140041550b15450311904030b544001a00c9182c408400030030714121100300c81244941c20450458540d04000304a42000c603400324200c02c2c107401010301a284103031f2500c0001c0c0750f01810800103c080c01d08420070f01190340700501c40e500082d503547c0b4030114080481c6040e030304020005440c0381611203800050000c940110014014446d000c3c3c009200c403070251080340d0145800100041c0e09281682c101c07405490014802c1000700c200e11401042500125280c610036840344450010317001240024038200d81d0010070700f5114841d0400112282d4102c50380c220b0078035484188510104909028208541051202c489540c91810040620f8104e40301183d80268404110000059900000d0550700c181a41054042342d100d034082001d401c101c010002d00b16140e035258270040d480800d01c2c1c00e0115a00c2001d020115211102c20000b25200181 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 130067221 1250 130065971 130065973
    0x314210606031302240d02090103050907050306060607060209030102030901060509150f1513080d030b0a030804060c02030f0105150414070903021203040f0315051308040506030a020c0d1e0c020102 86
    0xd450014034007017422100c1c000703a00310320f41001e0a4104403100b554000c241803174041c82e0040b0f40e4503034550303043c8500d503481448a0010840d040c84e20003c0317519408060101801071100081800500886804132001401c002c3c001719560710703000001500a111038020031b80b0a0900b08080f40040000b14125496100000e062030b00d40c003540f1080006038101c0c50250820800c00b40b142c107a1303c81d10250294020034407000034003611050080010100e03010145514442c0d006d402003840800c462806440a0b603d190800312115583c030f0001919000006103010500c0d802c000801c80d0652031030b02c040e00d410300140c8060041c520240c6000d40380c203004850b07003000109620000c05c007614058101e165401c0b000c0302a41d20700b039103554105217014416042a1455641d0703841a0101241910810350304c80c5d00e00440740c0c007601081c0e4034141e4510881c8681407240e240400828140d51956044451000c164021070b03004110500000c1c0c840c2665164031401a1625404851150300a03c0c150541c150705034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 130068471 1250 130067221 130067251
    0xc061403060d1509110901080a110409030c02091003030306050607150b120a081905030609010b0f04050423061f11070807080f0105060d08040e04031421060603 70
    0x501c15681442e07001a56002443c100c0d00f105148648240701c0308034020b0240f100d01140c102c050141a0006074001c2c03400381d10140c040d40119641d8903003004981c0045502007181400c03802d048880000c03454010307510600c06000c0c07018049080781e03900101c07840380e18140201d41d40c410812289000d400e8002c3c02c4031503508011441c8050541c40a0f1107510b00400d94105128880c500618107030145108a07600728001a044084240104030710540316a01e00d0050305d103292031400b1610703444043c440c0c10785004d400720704107445004081c251409010060f10402c5041d1241110054450119040d81000104080400c00508203140104500c0c600d000c6101e0030b851100e90704855420070003014072802c2c050b02d04046020304040c0040c030b00800c980002044280c0d00c0d00c1100c0e0854001030511842a2201014070001403081c4090760304441c603569041c0c0b000c7d0b480b420180c80070481c500041c90004000240390807540f1644180d050740300c04540340886191f94000134402d051105441c6411040f40c5a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 130069721 1250 130068471 130068481
    0x10f06030b0609011e030f050a0207210c020d08190c02130605240c010207120207090b011704061803030f06090908070b06060c01020a0306032109060f050912030301030c061403 77
    0x3000780005c10500300d240c002155440250780800f01c42055400000c1244c0001c0c985041c03102001301c01c40000090015402091b003000d0000d0720201492800901600b1030304410070a009091043d5003080b0550440499a442c0982e40202407120008080344a40c0b200f19076060b52030303418032950054900c003a002c20075510600000c420701c2d124005100c0442d0100b003082d40392404080c000703442d442c0d101d045400d401d044500720117402c15106030801207a00f8a000302c51341542c0c1e40010100e200d090441d90078a219196410404050402600e000303010a4a4410940400d507056001304400c002a440c200034440c0c90341600343c10340e10075000c0900103044c180035080100d40204081900450020826442e002044c11114260380204582d540825501d00b0100248520001c0807003130010025224072596040c40e0380940f60191a010b10130401c640a1100c1e50080d008504548130080010003a801080054001a030b6a500901003254209104d090008115010707904101001800b02140390950340c0d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 130070971 1250 130069721 130069757
    0x70501051b18040b120715030b090403020a03050a0e09040302060405060c1216031b0e03010f02070f110a0506160615081203100e04050109230a03030e070905010f06030b060901 77
    0x40506000d91003000c0e148005d141900c2002018018501c03603203109a09403000030007400b00d8194840c0c0900a161540400c00001c1e03000c41c0180d80c3c01d60500381283c0f030315010002160502d407107415075138008115034148000d15800050f51440346104004a030303015501d22130804c2113030140f05840800300f000080850100108800044860b0949203000203000e4101821050700c130304c5c100c0d111804200d0441190318203003401c2c09050100241d02d00306510700000c565554400961150010300418880700300e101950f514160030500a00c402001c4a481c2c0e0512100342115a411070b808032134050dd445000c54140001e800c000084030424000742c0f07401d20010078a60ba9540c40201040034000551001142e24080e1808480c00b440c0614000104030940d480d000c0300b40d8030650b003c0c1c7d0510460210802c1d400c6070004505500d582e140c64040b48806034042610f01d030800940201210358140700000c03400380c0c21140004112283da503014001c0c1c10198040c01414405c00c94042d00040400710707400d5030101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 130072221 1250 130070971 130070981
    0xd0302040815130615090b040903080a0504140f0c010912080403140c03060703060315063002060703020f0610080616020c03070b0a090f0e18030708070501051b1804 72
    0x80c11003040b0403c2d41169071840100d44207540c40c5544080018000d0003c85241e1096100509003600e041005403280c0d2170142c61050002c003c5009292103a0000f01040085105051107010140480c0c000c1750b000d420094581c10b4075024540041c0010350009400b803113815045e0401500080c826243c203081d40c9901034040790301c00203440340b48100108500315031010040144030380141d680005200f400c40c07901003030a0303c2442c80d49240d181003101c14045061856035010390980b106489410f000780b40800ba40d0480c40104001c0c0d401000401d1078030503d500405c5460340142c01e1010b55000350780359a99100c40700e6260298440c1c0381d01c0708001682407409904607941c6a511070044a41240559000a240c203806400c6040100390200b0980b01d0720790420701311409040303401c81035028107051a20321941904010309420100d9141207601e04030361420710440d200b05800c0000e042c1e64000d80c7c20034a010342015625001c4150401d40c41c489401c81d00030603500120780802e100500700e0b524070104800f4003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 130073471 1250 130072221 130072231
    0xe030304030c0b04241409010306120b010e070801031104050604142a0405030a1205090a0b120c0a0c020111070504020a03050f06030a020a1211210d0302040815 70
    0x88420000440480c907151a4400103201003a140c0e590790f030401c0d12068a0304405901c6000e45030341c41d4003100d4580e401144086074420814080d60300d852543c00102c1c0605019441100c203c90301480440600100640315416103105a0380c910043e01e400c001151300307100911000e05148071039001030100745060f8009541141c1c00038004030703018a110520046103030082d0740200c840d5409a141980c042d10b5102040c00d080400004107041c1460b000c01f0a84a00c081e440080c00c4155050040c00e5160081c0141d8400c5a4003419610860f6200c040c1e1500f26884070718410312011000000401d070b090001d0450f03641d003034565680c04650340c050f8015210342c0c070262180c0d8004c0c0100c0d90041841d13201c030700c043c0615956075500458181030400305801200702c054062800303a040381c0102e0000d41c4075501110206d0f00b1090510040c00070707604200c0050540d90038510340c4280702040038498881e89003048404a005c1800b80c4001d02d4480c041036080703225511595289401540e2103034008810000302681c05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 130074721 1250 130073471 130073473
    0x60402040b0307080603011409030a0507260409050a02031b09010908010c120b0a240c05030f072f040c030b0d0b092406040228030606030b040603020901060e03 70
    0x2003601d4148010803034104440e504000341c0c500c010025a407800b4081e218442c4102403003801039044c1070296079180e128500c1c0076804d110001450301d00b0003a003155107440b80c01c1411900094000040c0c00c50b41160301510442e0401400c1c100803c7c41c040141c07007100d002d5078450340070f44d42030005500e100106801c03078440c1c503050245026000400302d100b03000b40920f0f0703400d03951001d44165204003020116500f00d8181c902409000c9410300c04120310740001004c5645649900000c120b6440088840111a0900038007a01011500108905954010380794580c031414600362281d084800c421806044001c010b030003100c1c6554401002d0801d60b101c07050341d681c54078000c11140020808940044183c0004881d850180c504100031a141844001d95914031107556a0481750441c1d4600005840902014030031a800150ba442d0040200c920040c81542018039003440c505001d03001d8010b000600c16400405c0c10019080c440c2e03e0280302705000c0e41e600510144159082c114100c88540340040f0700c07501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 130075971 1250 130074721 130074727
    0x9050a1203050c06070509120102091503220503040303080105030607210908030411011b03020c04180209070914030a0302061902120c030115091d04060213060c1a090d0305060402 78
    0x3e40349040c00418880c104644500d41d448024a0030b115110603401d0b083d081c2d591040c090151143c0c2e64858101042991440042c0c4a48900050390341e9040c003001004d915541601e8600c0400101001410859000340c641200d2680c0e034405064072410b084894000141d051940000840c65035007207440080d103049400156250b4642d60484550b1041e20b00baa0303152000341c000182c03507a02081c84100c42403169080c0f82000c240c2e6901039500e074000711010340709984841c40c4a00c07a5410000c0d1303803481c80d00141150024213103844007501070400e5024111200005000c2d000340c82c00c2c0056018987c80d1326a00038541079030b90440c1e0080c0c081040d0078048540360200030350001e078005000c00f00e014141b4603a400d5a0b81d4034084606600080310140d107014048543c03810014a800120014080d00413286410707065074a0703280c568000c0c464034500903000910640d001c2505079014590103005840b8032010001d51603102c04600580781c0072210007400ba0312100a140c801c500c00d0300160740000c405803001d41 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 130077221 1250 130075971 130075987
    0xb070f0921140d031b050702090f1e0a0905010c02070f03111c0c0e100509060d0302010b03072304151a040e07050a1b0203060114030f070b120709050a120305 69
    0x1c1003c00d0100740030002522410140540d5040c110074805202c15400d0041c070f08419030340451080440240050782c441260000140e80d101d245d05503403209200c07404204920329182451000800049505407040d6182035480d118803030000483c030003920002031415503070606d103030703034000001c2c100d222826000b0034103209003c0561598609a84590b06ca2203000301c07154106078101d08880c20040c100c0c150418420810021030310342100943d0000010b070746269000d01507040981c05808a0003d540d09446811400540d055546d004924181e026a89a840c843d13508001c110a607107d88240012a02d0090001c000044000301d0020b4220013140b0881d040560303444402044a900301c410102290300011000c0e90b580e400b0032a161080340c2d01541007610f07075103600440d6036504d0502410800000d2311050001e0341d5410081c20125000c1c0030219404a0b80380ca1403e103080d0030417403044054201480120301c102d401204040182c60b4050428140945060344a101c20105000141c00344401040303444 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 130078471 1250 130077221 130077223
    0x60a080901200313020a03140106030b0f07050a0503060105130806061c02060a321b19020f060d05040606080c030f120d11030702010501050a210b040c0f030b070f092114 74
    0x5290790380e8230800010b4040c40c6007040729641100414080710020004100301c9420782000c107440c0d40940d03d281458403551060016910fa100f81032600707940705032881c00020210000182c1d0340c442e00c0162135126194000c40131a406220034014000d6001c0014090328017128440c00318141c110a80341501c00803264400102c8403840d007140c100b02c0d944507000070440092844400d0312940010340c0c4000707200c0d060784041118082c031415640240301c0e48a00040444a5a40324143d030300c180c0070658200403905142c9410301c010080c5100c1c40d060381c0200554a007240c03401040740f00d000c040d000050458840c002300305280b180d00403200845801d941e81d80d203031005c4c542207000c1e40c811502038000207038650420040000e80342d01c03641700000a41b5540182d10081c250f000980c52040c3c1d0141c0d00325810386981c5484080300301103400c030152560081400000388040905414000c2405031120445012041003c5400140302e000e003c40002c520304003043c900c541c80b00c040140700e008481c000e50a0f900c01c0031407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 130079721 1250 130078471 130078493
    0xb07050102070b330f060a091409041505040f0b0f04020901080d021906021e0304031214131b0b070311010c022505060a080901200313020a03 62
    0x564040e94089800e0080020031107000b6000718001c511444c2d5a607014400368001d0402400062001307080d041c1000c081e446503001c1c5080100c0080459072110182007000304a44864890202c0c038541c4041c041465040c11100c1c0c50085400c00010340003960000302200103400003800031a14407180170a6580810745840685d0302986829400800c80c2c102801000001c11060f002002036410107a0108182500010048003140c2035000140c50540c85040081c02400b07259a0300e100c008075021352060802602000b14480c034030a48a1002c2c3c06460f07280001111511107150803c0700c2c0e14400310303140260594070b0402c020b200d041d201d170b44100c0178a2a81d00f024503a6000070203448000c07070300382c04044c3c02c08510720766441020007c206500c40319038000c1d0b4621800c0005090b4081c11101810f0039886505243c000d441c2c003030b00c003655618540e05c0084c400c203001c81c1d5103c255440c00f094084a491062115045030b003169050702d0442e20380c6009104c00700321012013243d00500e42000003001942c59102 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 130080971 1250 130079721 130079723
    0x916050313240b09191a030d0801051203090108042a030606231008070903080307050403121106060105090613030807050601060f0207090f060909140d02070317030403090b07 76
    0x40c850002c40c1282d40d0a0641d00d492898074840d405540422541c590390550300c04d5850000c8402003031a82200400e00c03000d0800041468140c0290154421740c1604030b050319040300c0083e00d200340640c10b80408280c490140d21942400502e8140100703000c80d100721401c030054807240b500013100e00d001e61244e00c0151085c0d40216281382e00da0400b040390b600c80040d400441000c600451002070308607400039030b4482d021071b9018140b114520110700518030802e072000146134000e0b103141e90307400c02101c058803640161008030717480d810540d003902c2400e01c03078002040e00340d54010080096445030b00c010f41d00740d000103c4007a0030900503c11101c0482e021170b282001940180782c244d0341c80c0141c0c140f403800d01358144c00040a01400d00000d48545d0350021707039801201c501980010346400408100c401810840d84080c07805814052840f0501802c03550034144a00000126441e2540d5003000f0f985440d03107844041e203581603000c0244112003040b40250350140c8280780880c0d00c00e8075141c0740c02041c4c00c001c130 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 130082221 1250 130080971 130081013
    0x1e1202041502060105040b0a050f0d0f020d03030e1c051204030203160b0a1103060a06031e090803070210050603071703040f0f090501050d2019060f0e0916050313 71
    0x400041c1887c2c441c8480070041a42c0d030400041c142000b0a890320100b0b0407550181840e5a40c0409018040c1480707518580d00078800110400a03041c000d0207072032840d07a07441650144e10726109080d001c5a04070000920350307803106814600f48409800c020381e00104160700b5408100984400e003c2ca141c2410700705c522800c0d60f141282032200f5894102c4003450700c0d03079811001c20001e00c10aa40e6101c68501210214500420200c451402c4410310400d00009140c0c1c8904010b580c01c10440c221020f1481400207900711400c1c00000e554040581c0c0f010b81e20140c043d0800c01d03081c46011000140b5403080301182c3d0499203441e03500c1940300c420342500d070308c8461440d0300c5540901480355240603050060004440510100d091915140c904800100400108034044000d05d50389490703d02c40c5070064042000860fa0700ea680d58000f400c0c4140001f10000007810951189200c0c0c6040006603000b1661220481c100640d821000e131603d50028000230609840d541038200000e844942a0003103580d00302d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 130083471 1250 130082221 130082233
    0x60902041a040b03040b0a090203060c0a0e0a051f110304061107060903020307050105030a140106051305010219020103020f1b100b0102030315060d0e01050f090c011e1202041502 78
    0x589200701c181c501d5801d20114010001004418420001d690f0016007010684000d80c50b200c42210007007842c481d000b901805003804000e10101e00030064180c07020b071511142000103010041006030a544d00a0316070199400400001c2030300c003503528103440081410300340410680c45112074070b9508254085400541c1e0b1810f01c0d85541c0052112a00501d2242400c103c86421540020f0329001d02e80242410004044001504140b040d0883d149003203225120054a503150140141107a10450002c0c04110362418001060b5200240e50500002108504040d120348d650046019512110281600d0303001805024407a824401101c3c00c00c01010340100740c9000745545120a41c1d03070340010705056402c10b004112102118011030822110f00b254496501d14004441c0030050480440a0300d45610b03090801078074034540740c1100d004861807801c0300d84445910004481e4494204c03141d031400b0602c2c0c1090b031045405095083c4074545481030141c00c003511240e103d003403c010b25006034010b0b031000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 130084721 1250 130083471 130083479
    0x5010501080c091b0d1b0201060321120c050417030901021612023c03070b070302030d0e070e0408121f12020607080310030510090c0303030e070906090204 68
    0xc100c03001000d0b0301030718100c0d820301c0c0c9440e6078100d55003501c5021158003030005a10a0381050380c3d1041c0760348000398403050b40300104508020300074489d0340002c984158103001c0544a50070107846094000a040d59540241420700950402601c035070b0303034410184041841f0210740805100038101140d03412000854840d071b504400240f81c401d0040c80030355401030640d0140000064202408401d03501a03608031111085c5910803000c40c41311130388840c0302161910940e00f190f07103900c03400e02400f2800c604552225450700201e0403030f1f02c204080140540c0c0704101418650010740c114007000103146007511460341e545e01144010941c101c8080300e92034000503c0200207001c0411a540104201c003012a4100f1a00d003d41032101e201d000321b5615000040d0705034110350300c1c1802c0710030b0fa035070010003035840c1d0600a400b220219000d0104407054002c24088030862012440340c0440642c00064510f886031450701c0540040607501c03c0307450640a0b851002c070720107200e4014030b0000c00c0460300050340c4900e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 130085971 1250 130084721 130084723
    0x70b06010e1807020a050f0a03020c0a0f060804050f2b081603020f0f0414030601060305061e03010e010c05130f030f03050a180311010e2403060f09040501050108 71
    0x101414103004020714214419207891040040b002a030341521012500d500c98242d240802c10100244684142103c400e518803000c50f1411300288690202d440b003008040402030300c4812170044190000c0d400108006292050f42401d03001400780040d00c8211040c100304500f4000c01d41050000816400074410706201441412000303040e5519081e01c280c201001d03940c5070540001c17840e10030035070041303020b0f0b004001040807150040311101d900d41d0359640d1401540a104143c1055034803034084e84000242d111301034002d01e841540e004044005405a0030012184034400341001d60709990380301d140290450092144c98090f034056103915440b043d01c0c00048100886035044003540055601c010000201125584403a03e036050520325103d000b04036040b00d02c041c01c81151105d040302042d0010a001d00d0b0050241c00040c281d840450f00042e4206000030020710301c030317010700080e035900303400304440d4500700038507003211b802862180340b228100c002484210041d2000c0d2682c0e555040104aa000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 130087221 1250 130085971 130085993
    0x803011d0112020f0108180a0c0602060717130c2c0a09020d1203090803010b0c07090c1e0e06070c080c04230606040302040203010e16110307080f040b04060507 70
    0x107042041d000d01d10307440740d02207946413001c04045030510500d41d010510700e2000985140d015590724007120922002da041184080d54284120801360003400003003003405104503803d98504100e800c2c100210745500d41e40c05108200345500381c5079504100c4021640d180509440d03a50380c1000440da0f84041c81e10b40c894440280c0c040c2450400c10f181c90800c1c0c00585504440c041820303000200310150300c0c00c005054024000f6488002c018803000000856050b080802401e02256031400721050301d5190450740003210443d03400c400101c0c0c0c0c59404510351034a01c5000c07448400c86031500280c03181c10000480d0031030308159411182c2174400780b024040c81d01d08121807100b502007202c081c0500c415507083e0003217601c40c0401d01c1c2c0c8240d281000248040d00c8100c2150f00841c0e011f002150f5079070b03654100004090041d0703000100480d600321240801c0e88564100c03010f418624024502e0300300265030340100c0b544032400030f9507050003d204c00510321045801800003001180c650720707622462860f01c050520 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 130088471 1250 130087221 130087229
    0x1b1a07020f12160809150c060f0f04030503010510140d060503010e03070305031f08100518060727210314070507030311030d0f0e100501030b070305070c0803011d01 72
    0x344041c000d03845220145450116a03036080140c042e40c070318580002c00d402005031b0100f002c900c03c0001b02100c0d0843c1c0050b8084c0b040400014410064486a6841d6940364041d00d000d00040d50900041c440c52428250f0f06454a01904008c88000b030b800040613903c0c2c00001080911560b104c40c200114102800340107600c000360400345d4070380092550301400d06c0c0400303044050200b0601c1d04806130364110300c100070080c00c100021075035801543c5d0009409008210340c08003445c1e14106090450980004691703000d49459114107040c07900b001064051003901c08034070382264540c5000010000e400031010300d0700e02402c03041c0100303203403c504001d807030030001c2c3c1d808052240c0f08000c4000803800c0406d02c0c0301a00c2d031600c1d00d40007200003045420b03e54002c080c60072074894506010550800c0700c82d48082800000202541c20440070b11068104558092201400b010380010010f00950b00c66030005038442044c1c1020a00a0321303580700c0a1182c0c000b60000345664110307460013800281c02c144201c1c010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 130089721 1250 130088471 130088503
    0x20307030c0612020c0304060e03070308120a1103061f17040c06020d0c050a06051302041d0601060e0a0311061606060e0a09120305151903060e0105071b1a07020f 71
    0x446245c3e103105941380714900c0b4004c10084038002c6441c6030341e4280500e0006681142049032110292480310191003820703200c00e0411450001060080c08044058174403d0100900b4811003a10300c512801022007404150300801807400c0a04101645000a00e40203070b00440c09070042c10309140c0b0191528296059810a2040c240010f90000d2400a117000e04143d0002020401d40c0f11210864581c520718000258080d003021190741401e03091501009908022404591040c0d80e9108190380800743c0c00c18541e08030710301650500201c1c60006094402e41c0c4040d03e244d107090040d141105201c251074104540c12501c0346000c10055403114407603500501d80150030807003140f01c1e9499074912000c4103031030010306490340005a9202c1d051440011840340241c220103041d01d2603101110000014003080302c095140c80508200190140704151048810f0b0301d5900c901419902e0301c42c40d8030314030700080303a190203201e142142d05030303400d02e000e80182ea02d03800500554040c2c0100b80d0030501d8803d900d45e90 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 130090971 1250 130089721 130089727
    0xb03070503060f0a090501060e07020a020315010b070f020609041112011a041509090204090902030106090905070b0f0d09060603020f0108070801060f090e01030b0103031b08070803060607020307030c061202 90
    0x3c200228420640262050700300042c510030b40d1510301e01610080e031088035078030b001008002803990003142032205a03100724243e4108540228500700100c1007030060311421202800f83c030300000c19030f0b500c0038011800140b0701802c002d07040d00041c0a031804030074581c1e100c48000c05c0c802d41c0c80352100041400351115135101c0c0b002000f4030011501c01e01a51099581403d80021031031801806032020f0006402c1e490015540e844e210004030f40a0280d514040380a58a0010005100903851142c0301015074000090503e15103003141e0031015800403441d03541290307020002412968003a10034a03032035500c02c4401040c90751440c0108196201501c0304241070200b03034010041082e50064a0b46e0540c1c0c2c2508000c0700304450204100e03072958050300040f01e002c1302040040140000b441010381203038820764030081d2590102021240c44052560000c0074204288055400100460f002c0c41d4040f002a0445041002640000749401d807a5031090714446d2503541e0038041e0a80c4001c0c100d0094030802010740c0703 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 130092221 1250 130090971 130090981
    0x207120303020306011803080c0d0903050c0402030910060905060108011d01030605150310020915070305091c0209100608162114090102090406090b060307110f0d030b0307050306 78
    0x18421414000301019030000000b0450381c01041c80702460031822000917452500c81c904980c1680c4200c00350364517449040710600d00b941c8980c8019050300d5000011b4200c61a081c818400690400303848203606018452401400070324500c50000244400c21011501d410074a0001d0308144042c0c00041640340c8181440021041d0f0002c91070441e03500000c00281d903519100e414034550304007801c1642c58000d58103000c040014a4019003914042103c81040c95482c020940704a40f11f050ba004011034024000e60304d480c600b40e07009015004c40d01c0f00c1e854003c40a03500003003981000f1282e0142c04800031200b4403e41d5071040c203c0d079000000c00c1080c000740010043c05450300850495019980e61044031074000c024994018a00d00c903003e18600c1d0040c04e240e49420b010303400c26841c2c14019440c1c4180011414128082c0700d000ba81c000c4e00c12451a01d840c00120b07814045a80441c865110b642480c010b103540810050303e0f40d01041d07038002a041101c03420141030110552003140303e940001e003402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 130093471 1250 130092221 130092239
    0xc2304030308240d0303021b100b010c0f110409080c06070e040605031005090a0204090309030506091c1d03060108160902040515071109070801091b05090402070204090204051f060207 80
    0x8881c1141103402d0780d4803480c00e180c102d0288c070600c0846a40200020915450300c400080d00c07400000c14008248610918107004590009141e0000b41810004c039580501151621482d0703602d0070030150010a07941269110341786c450748001a8610035078020f9040060060380030b00c1151002d90100d0741070110317515080000395128000c0c604020000e270358201180a04074100084070080d6805441807080e40a1814041c2000307166120646080c0240000203000c410017254510b519410500744841c584862003040749d5440c4076902c1c000601c903620b40e61074665a0b00300b205600916031072004103044050210400b640c212150b029040e0f281c01400b051200c0d6980712020803401600200e00b5440f00018140764805141048020742c0001000d802d0250480d40104041d060381d5445c0c0c0203008140e010fa0440c910001401e29100c00568103100c5080b0500c4e10b60010f151030f0303000510115072918141c00190407100150740c40102d1a001844404104035031100c2c0200604490015000701450301e1042 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 130094721 1250 130093471 130093531
    0xf020c0105090303040e0408070c08010c0207030b0705120103050303160e030703030813210f05071109070c050106121211060103081303080a111015090c2304030308 72
    0x1040c180100420b010000d500c042040e0780082040b1082200300c1d04107420641b00a9000120a42d001100c1940100e09000e05008900c50440c241e03004184807490f41d102d40c100c0400c007900034020800100700455043c010000080d019502440180d5524100484100c3c2010031415200051001400c0100119500456410b0849425003406070341a81d500c092580c6510070710200a24103004400e0b010803800e095104085d080b0400d455491201c40c000d40d0a076000e0042d5580184010b44108000d04d4030b003010000e036500321419003040e4106000a40d546404c0d116103400850744034460b01902d03414020220016a42c413a228200400449042d414841d20b40905000c06862100f000414030701c900145410b5a0065401c5809107403581003180000b80048251580c15055101307d0b60446041e650364490311500c0120545582c0e8a54a48030300750001e04440c108140c14090121358200125012101d500040b0844102c4159940e095281c050a0343e90b0141040c40b5a00440b4070540c02034460345ca007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 130095971 1250 130094721 130094743
    0xf0d02071505121008070605252003010f2901050301030b07050c030d0207062003070e0103050402040f23070201060b1b070312030207060f0203091e240103120f02 71
    0x200b40fa5444124a0701402d020760700000c0b41340f140020000798150310101904002c54100b01103903080402001400c0c41009001c0d001d072460001484119a00d2810002c0d0140804054004164a0305d2008445e0440e2004041d04000d102003092081c821148950b070320002c02c01c2428018115419a2280303074014400901000134000c0c00600f51044034410416554281c09401003956101c006280074070180c5001c900d45190540c032100524031003590751007628401c00341c0382d40303c2c07041c041c02c0d00045001c1e100142c8141c1c0c1043d030360817900c04000c070b160203466442e03650310504120000c2d000c80140d41404e4010915000c5914019007031080701c540c1405c803181c81c820782100145882190340748c2401d02d030141d8001041c00b444142038074801505a006030a0242c010042081003810031b03285032040e440121038240c51074001c2c140d503604c00d80109810402c3c00c04d200302150701003d41c6c078080c010b206000031140790550b00c000c0e004008008180e00102200105450318100018922201a503a0110101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 130097221 1250 130095971 130095997
    0xd0503011205100603033b10180311150405030a11060c0f011e11030103060905072c0603012d0b060f04030203211204060605030f0d02071505 62
    0x441405011081040001c0318403902c030b003009905d540389400707090003440843c400017120860007513000f91803a049801c041140e0b40440d440003d002c9000308105851881342c08801c0c010b66101505070030a100300d00c900658450707207812031314130b07448810010703a080d1414a0141031881040240880c3d180400c400c1c40181c3c3c0300710202c1050184100181c0a409a00c007001040e00c00c01c2054070741d8010540101d245414403180c0c00000d00103c0e800c400603220083d61152001104100400000d4442e034040100e03e80901d05684040383c580721500ca0034540f2603441800182c1d400c804e0143e0606800409400c068120300070401e102c006540072000491858400360b04400d85510444c41c0b007000e0308281c940d020028000384d40c030052252442803a07002400103034068822140301c070403481402401ca42c1150341c0e0440440c00c200f201001c840009600807c1226a1a00d94400061303a8400b0803030104072030788242c064140a444a98000d145c114141c0c400c2c40a13114400ca46c494103a0850111040286820 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 130098471 1250 130097221 130097249
    0x115050904020712080f01060207061706010302040308070b04150b0d02040504080d090c030501060f0605071e06060e06031203130b060a0509040f0b070302130509040303240302040b030d050301 84
    0x310014000303002c0c1600181031500080b032541400d07584100c12a205003403c840d11005641c80c1c0e14200d0b43c0c3e203002d004c2c101c01b003121000f14040c9a00c1144e4604e07071009051401500d0075480365190705180e0001001260021302110a010400401a00300074070300061040800c600041c80000031340c10425000064025a500c1c40403c060000060031141840110f000a2112009626140520884510043c0c400d17501e00704000c0b0340071032090b10340c0b0211031842d80d03007500b00307201c50300d40f107403c80441c640840d00c07203a21803c4030000650318000c6500a00041c401c240b851b00e0620149400c0480552000751495420001c220011000e020043e46d490f400a96055890307a6010100d507103a411901300300c0c0e21a10300b40c208401c2000c0714249a5005110341c0d120940340c2c0b1444026404c0e8080e1400303009400c40401418811418005422176110b4003030301d40401c10041602c24078000350b8842c412095415400705091040d424a07006101480d1001d8009080d20342c8040c200405600042c010308a1070158030f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 130099721 1250 130098471 130098487
    0x3030d2a1d032b0e030f0a0b090c030601061b1b061107060504120203010212040b10080606180405010b1f020705031603080703050c0d0203040518040b0412092103020114011505 77
    0x1044c0d0701a0f0b800c405003c6601c4d01c5040c14086070781d000c480c1800c44a600c40c0c4400610301c1c2002103a01e03d0b0711000500100031603400c01c141911500d001d86404d50400f07045100030008503c2c00d41c1421100006400c182a0280c24404020240c50744490107070241d92000d00c0070003000780d200c0c0890b4220740281e02c151200b45407071301c000707800fa1081002c01200c0604040c00c5c80240400d1094890184203000c80f110105555401d91a07190303403088458581c840e4882030084c1c9e18010512231294040c0c40f801c00091102040e000207080f51031440031003034456602c1c0110ba0362103070301000004044e200480040c0900000709038002e0941a150000070301801c0e01048500400d4041c171f0503560002c04100c20303101402c0c007260000b0340d660018802d1a2045640700b45020710807a40306c0100b4002e5811403000c82150307071075480748000180e2105c1c8010810500c54030005a150f408903d200c14041c83c004d00321003209407810000d003902e0f0095003428070750002800400144446120b441d2958201c2d040564444c1d04e0b0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 130100971 1250 130099721 130099727
    0xe12030724090f0b0a0b1f05070c09051504060b0c0606060a020106051c0b0a020306010e010e01111e0706020c13230906040b0702030903030d2a1d032b 66
    0x2076140018a112800306202c0c08001d10000154811750440c1c10400c401d50010040003803100900e0212000700e502d40d00e03000f4481d0b11680091107102e000e505290740042d600c0030b413102140c2040707680c00700c8102d224021121620f03060290a00800e00048060309090184d003016072181c0340030301010311446001a6076060f03c2d000b9002000240402402d111001074440180342203001014822540c081035031700000c01c601c03d28400c1c2ca00506043c0d46030031000981400545648180c4010581400040c004040d200c1324108940220081c5221a010725070140701d10003450070b0100c0c2c1209003550016a9040c002d5160222a4000d490011070040342c02c40c044810a030420700307200180c410f8603171004100701016800092186c00341d84140050812503569040c226128001c100032107074942c2080040e504050502d4201c100d0a2a0b040007a014140d01003c82c104102040e01c400000304000007403400100352030903102317001528150094000c0b40c0321507040c0100303010f14006102d4a04003941d0000c100603c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 130102221 1250 130100971 130100981
    0x50316050327070801110f040612090623100b0304030f030e0307030f0f08070e0f0f0603070306151b080d0f0e0705150403020a0e070c0606060e12030724 67
    0x16220350350b00c1d04003a00c54150b540b252000c2c01a00907075803d080c0140040140c01c4215010310b00e400080c141041d06200c012560b25100312280d0b1455602d482d445004140144500c44541510440800e418505201b0590700c0246c018611442200c412104101300b40003001140e900a5041c900318000483c1480203800174400e1000f40041440080b94034410980c220260940078a1142c441e03110050110004440c10003045480c03070001040d00d00074052600788030311130f503032108002003000003214200700118101ea00304441307140000307032511010069a41600007180c0d1545503880c022606031084a0310341e924000e8080b00405038000003d16800440c02540060903210010100307203c04980c225850317943e25803500411b40324582140203050f640c3d461000700c9044907400b0301004050362500c0e401030350805c001420b070424449188001c02c0021103601c02c03203015060f55210400d42900200a01c00c4030b0390a0000c0c000d890b4001c22158001c1032600c0785186210a072941c40c50040c0004a0562010300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 130103471 1250 130102221 130102261
    0x4090c0906080d03050c0310090c020a020d0b0117060403020604030815060d0507140403050a1104020f0412050601051206040f1118010e060d030813110d0503070b06010503160503 78
    0x1d00c1d110011916840c08241034204095582d01804103899911000c0020712003510540300c1c2c02610402005901000e8001410003049801034880c164035a40200354031907108502120b01d000444014003416081c0030860706109124002450b8500d4960340195540c0d401400240034451600d00003840d00320110040b03440300314040c001c1741d06c42c594454040c018202c15a40130300400c070480b600d034940204100580e0102e070303001070090070424030035281c1d0020398004203106d0b50016020090300c5400c9192030002c10081c151440c10810f00a400d0070b066040c02010b801a40c400c44070001da0b10f004480001e0f100e504150801c29252220301c891910744400e01e09207281542240300764981e14070011440c0206412240c20b8115400150744000c200040e00170710483c02030104854502041c6804034030001140081d200300400311040e42d0f41c10001c0c1e200e4054000443c0c442e4000a1480e04002d0340d0185560002800e08080e030441c200002e480c2c04600c10841080304229010000445402c28002905008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 130104721 1250 130103471 130103489
    0x30804060c020a0e0c070f1106030103050a0c0e0f0c03100905100f080604080f0a020f0102070609030315050306070e0103020d0c02060f250804020f120106051c0c030204090c 76
    0x1280d80d800040c0001044a1050388180e442d4040041e11a10309492180b00d01803501995103002040e40d105a405080c019040c3d42058580150b0011901ca52004602950254004000c104d04c40c1c5454044045190020324140f0344903030502c0304101e0013189140e00601c01855041d01ca642e019003010360f003a001d51000e4103880c18141802101c0174490300c80310603911961180d0346141d455030700080c0d03aa4026a00245550b1013007002642c3d0000b064054255a0320900c10748061164000c0d0791402e81e040740d03100351600c954950a880815406209898141900108040c5103d16003000203855800060042c8103104040801401d5a8800d034111552103440d214100007101c0c082000039524102150380d240101c80c1d0300b000c41c8400495006050050054002032941040019421541c01002400c01c83e007110340c180f1036070303550764500004a101051140c000501913103880d0800080d10700703102c004c0a11a81103403180011a5413114031034280da8054501041e12034291a029a244000f68080074070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 130105971 1250 130104721 130104727
    0x60f04021e0c010b0603011401030c0207030c180c031802192102011b0c03031404030605090c0307051002060604180213020903010c0806010f0e120304090f060b0901080c030405070308 80
    0x380700c09030014050042051008011013100354042c4110351200b0f005081c250041c1c45403a03086581b10b42c00c0514400028415075008981d2a034400e01042055044080c00034403070407000385252294456a10140702514040c02104c01810a65454140c0c00c48007900400c103003e40703a070700d48400205102c000d01290741c0c91840c61840c988403201121074010224001650f8813041c1c0d07640b40030030103642d0955800c2a200c1c01107900c0c40d5001d0f00c0486146845031224401484004041640d510030a8030070b101500c003424030358041303004060a00d0413903000130b071054018103d581c95241d030000c0e4031a804941900d000840e01c214805e40490a41030840080d4482d0009504503518501d540241c00740850560092081415105064500c94070840d5054001094101780c44003c80c070625103200b031070101811601d41c0484220200e815940300b504525180c40d00c1c0c1174030b800b00031042d2040000401207654042e003007680c802c0009005d80005054505900004008075051050a00450009541c08450039079 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 130107221 1250 130105971 130106017
    0x10c02011d1221071a0702011805010c110303090a1b03080a021506010c0b040807030c020402181212090108040321230402150a020109050703031106160503060f0402 72
    0x2580d03900c2d071041205211161002c108010b29414103450704281c0c800c03d84c4207403840304401c505076031740c00521280856403941c2c0201d000c034100b1030862100901a60000c1000a200b080c0274200400c10188101168410420072102c08808145101016030004074120341580c80c02102c03404421603000504900c0001030720003800c58000070002d051009080f00c001c4241e58079001914a800900c4001d070210504100180c00215620020030100c0e01c641080b428031001600030500303d0b08042c0402d00000407010050760b0515103500301804c5030310a14000e0100034000e40f0900b119028a556060610140034046803c150162001404c0a41e0340302c3c500c0180480714200300040d04a14100005143c0900c8c4041d03180d45800001d144515000b814601c041ca41e804480c051030350205414100f1550b03140a903c00181d07091000100a501031355a4002108020034402e0070700c1000343c24155400c0340c0081004020340c0000c1500d50141c0e04550f400c040c2283d01011034081d01c215107491042d0081403120366 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 130108471 1250 130107221 130107223
    0xa09050f030301081c050703091518141203030402031009030c06050916080a2103021201080303060306130b07050904060e0a050103030908010b01020703170c060a0912090302010c02011d12 82
    0x200c1c400d510b250250200340800041d181da1007484000323030010711152030600203e55070f2055a24440003915016001c603800b00351506d00040c140c0c201ca5400d0301c00008106d050702d890207092080c0100c140185240d4280380e40026550701100720719034941070300c0c2c80300003040c1401051546800c030307040351040c002450400320194490121490740034035050841c07400b00e490403000440380c41681c0c0c0021140c01104401407901515080c440c0c4110815800304901c0081150700001e180c02021240000c648a0408004140c10480b00420070b0141d9448150003401199003910580e400c1226410030a80d95039030b03500403e010b05440c0e08017000c0c180d02c49040c011070450300d5110768100c902270764a240f03490b07454240703460076503004221050040e070010000380007054400f00101e00020241c0340c00d83c40c180c101d1424501b00361048900300042c0740c3da1040101801000400308091003110f240101c500c1d4250b40c0040e01c02502c0002c007030304003c0050313014403608500040030384400000500540003500a03203285 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 130109721 1250 130108471 130108483
    0x1403030108011406090a1a040f140717181006080f0c0a08030909130f262106030f061f080d0818070302040203180105100506030a09050f03030108 64
    0x449507a6103030051820402e20303085000da00440005080c101c2e592a25210b42001e802c090048080c0034244a441c02c5080c3c0d61446903a166140ca02c10108102440c0001d88001000007403440c802d0204400d032710200c0340c49005100e540312221142c071500a03111041450300d4000307149182c10b821440c281c00491004000a0100d040380d0441c0100c6414042840500401a040c1d00c81c8800ea58410700a450310340c03400b081c20681c0205032405182000d00103840750240401510b40a40d00b01c42940a4a902c00381c00b10325800b100d1015680321450720708420401d003600c24000d071040d944400c000020071386c140d50a000c61000d480300d10302184d59a04200e6030441d00d0500411000b070140035030000002c0c203c1001b080c0c905e0110000d071164107031652558402c00701001c125520350074034082e018012005940e90310145001c0c6170380e0700c41090301841780c2c000c032402c50350081d045a0006551000820070b580d0b481c1d00702c036403152654101003149640f030f29200385011580603403214280408000824003210000d80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 130110971 1250 130109721 130109729
    0xa08030118050601030e0607030c05190504080706030608030304020105071e08042606010b030c04030b0906041109060d06020c07030f21080405030405041a030a030201060e070207180c030914030301 86
    0x2000306460f628015003c0300c0e00d601c81c00c0c0d42c0d030300000001803102d8001c1c0e00022040f04142001e6181140c0c2808501028060404000c0881c00201e41480344002c100001405010b150a0030010282841c1c2a10f81d24000100000e0402600243c2d03002002480f0417540c2c00d00500002c500d90002e224a84400c0d503803c01e00030350030006822a03460754103070120f01c04651510620f0003e00b01d20f9080c0013024105900040040710b180800b007000100140004075020310520441c0058920f074141843c0840c00c54811503101032103a001c44080c44203c1d581d01030b40540745a4004001a07681c01010480b03070074414198006004500c4030001d01060000700381342c20748080841905140850740501701590200030650340681140d00c10b210502c0181080c1d07108600b0541c40c00d11450881e486280003074034000c100141100182d45544080040c4005000c103590001d0640c0050501141404420030f040880d011407200410384801169141c54000c4e0b1004042c9a008122500d0001145003900d551b9030003845 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 130112221 1250 130110971 130111019
    0x40501050c0f07060c02010e06040b160f0e0d0c12030210050a05070503010317190c030f03050919060b030106121b051809010e0f070303110105071b03020a080301 71
    0xa449124503504030744800c009410307500c0c2800c0513601e40710020840c5000c264190b41d45c84d040c2e0081014200f000701e03c5144161002010b900c4d0500002d0a0381d070101601c0303800d100c0703c004803440f0540c1044584000100076203815003045000d0a00303108030b0704250b100020407100ca24180c814140d001c141507084000049003841030380c840110f108200c0d002201c50b0760000e0018001800050140f03e0948103d802e80001c0c0d42c1440c00d1040c0000400c00c1540c1040082400c403940c0300d0415800c4010540d40c18007508081015240151145031100c900109440b00420004030344010400a0340c0700e00340c0948013400801c0110740303c94251481c000c001500fa5126419401c080030204403416125003a0b480c041d10030081c9940c0c0c03a00e80080e41d400a0004c120395501c800000110b45c1d42008140e00700c400200041c0300321031450070060441d40800d948070070264101410450f040d0b0b040940d00190585050034003403401501c1c107040b814020396440051040030000000104803600c00202103070008848 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 130113471 1250 130112221 130112231
    0x6351002340507030f171206040b0307030c0b0703021e070614030403020a020928020306010e0a0f03030809120304060603030e061305041d01051f050306190c0c060c0305040501 77
    0x6621180c591a4801c000c04039030088000348005040c801003959042e20039000380061154401d80116035400c4003103841c201482c108100300c00ca14090003020219039003a0301810415007075484480010600e070140490725480000c16204240c8200051518918800d405442e082e000641840d01c805907031007030384005251200c00e8001c9000980803280102d506800600d07401841340e003031094941c8000d21000507504100c10302a04c40904000d003413800003003940d00681d40d00e402030002d0442d140250489010700402e110038000004006000d0080e03980605006141e603540540d00780c9080d44046000c103400d4000310600040100356000302d42602c1c070030340f01c83d6071000b01d10040c40318601a269481b08008040e18007000141010b602401c00c01140b00c0e66041c82c801c0038480e503401d541050f80c0301d007003100c03c48444881c144c00298541d000350108a0281000b401d00c00c155103103045001c030008030603d41c6c60304115040341c014081100c1072640f121050282e80d0300150050024403003203c007a0742c95401c0c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 130114721 1250 130113471 130113547
    0x12110102060903090f0d080307020706030e0d020307111c0c05090106031a040f02040f060e040f060e0f070903020d03120501080c01020d080a06050402190306351002 72
    0x21801c1031161038484015400c120480c020080b8054120042581000080c03201c84007080c4500025071003140550010700c0e015242441c0102120081c5411103a950040c0400c0400254044101c401454000e0201c142d0000c0c25000101c0500d071240262000c44010f075040c6d000c2007002c03900a401c07503100f11011041a0780c1c402c030550a0315040c001560354120944908451460141e21424100194460044c1400d446014108808000d03810040c04540c4802849103649894002e0140711645d218050124a113099403c099048010300400e240b41d030345200140010784243c0e200d1004680042004054003070a00b0003070b005400742d0355642d10303840c181000401c0341e000020704000d141106074020032012612072012280960054006007189d51100d00000d003c0d541d42c0054408100d844003017124901d540300e006000c64025034403405007a40c05001c0550b061a8404861026131104c001e081c040302411801c8500f005449034a0031451403000c241070203120b43d541e480d909050010f040030358041400e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 130115971 1250 130114721 130114723
    0x20106030308060108040f060501080f190b01030b0a0e0604061e090506072a03020d020f010b0a03110d0506040305030105040e0604171b0d0c0b0105041a1509090112110102 75
    0x129010140125000e1008540954401e20300c00c0c0d0311a02401205000c5501581c907481560001e901c5040164080305d005111040c060002c903480d00b0111000b05515041030f6180b5030b64007130502c000b920540c9000005030442c0d800da0081940100c0620503540d0518080c509640145400c0701802c0c0c0011060f484c43d1600a03d611840c0300c1d60781c100d070040100da5603c43c001c64441c406648414031800310300041031040440d915240d4100f5110350044c188542e01500024a0100c2c428903030552a8109208494a5140c10004a007580e404c50b0a2410480e4408003082d043d02c14804001c00600c0368104020a04d036220001d107050310022107040c004081c588412650300e14007070f20050000700d0807003c9150220315180c002e000120309404215030000c00200128105000c44400341c02041c00c1c2c0ca1045c2c1082207890003103014241c21501000302207080d0442544000309020882c0c011202d00f0b50082c0c00503030702d00544900d100024286c40d002d40c0c481d0140841c0c5281000c00325058540c8180e100c01942c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 130117221 1250 130115971 130115981
    0xa0f09090207212708060c13060302091507030c0b0c04030201080c03100f031b0902070f0201030b030705120f060702010b01050a0311090909010c120b0105090f04020c07030b04120201 80
    0x10300302030004064025500c40d80031a9451680c01c1041c442c01c60114600031300d92280300203c03044aa004a062549406801410000b0091095461030b07070800400e03d250300c541e202c040a84005140c016150441000803c039420070002c28100200d6012070b05030101a4013404000c0c0071343c82a14407807019140d00105c0090360146002c02400300c0e07501400580411400c0300036550000314240c001d09040d540303210f20450341c0c2c2d040d042504c2a14503840f0004240058403110130080c10320030421860810241c9030484010110701c0024101502d074004642c19540402c061005400000c01c041c01950035070030f01658030a10051014510300442c0700007040c41c0c1c01807088400d1440306856940c80d24844d84000c40041122110001e98210241700ba410716444070103195106103d040300004582555017000303000100c803c0d5914500700c0c280826051282d84c4034042d520380702c00135150310840315021000680a4001c64180d00c0491090650000c00e000255071054004c5000e84622035968021800c1242659 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 130118471 1250 130117221 130117223
    0x2190e06030c1210030c120606050f0a0303050a02010f0203070f020105090105072a0512030403021e0706030c02010917040f0b040f0e13140601060e1e010807020703080a0f09090207 79
    0xc9000c2c080001900103004a03e64802c41901140244e143c0700ea44000314070030160000c0801c180440c242c1c1c0108200c51040c40050b0800700c80c0ea1040600c150f0020f086a0b5803808010100720001c40c00000d814000d412480819100c0b0780b00399143c0c68009001008141d8460b141c000641c20140412010441032282c60301680c4640c3d100320515003d241400b141b0b09440c20707000d4007444c19102000105506001d00800304506a051643d00e0606e400d00074603250044101f041d180020310f40e0301061040000c0d0440840304c19007030118551070482001d900500c0080ca0280c903010300c1c90a00c441c4440c10f04000e10658212a80080b405600c840030141c65005500540449401d0030000740190502480c4e43ca521805070402d110803000c4035543c429044215100300c41c2c6c10350050700140b058a8000f44141c902090540711107035503c84066080300b143c40c440144906020401d004140c54a00c242320030400303140c02400187e074441074010000d100301414091080014928400030030840554021150b0311 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 130119721 1250 130118471 130118491
    0x10f050705190513051203040803041215050906040308090109020d080c0d110712060f090b1006020a0302070e040507051f030b01030e03030a1104180617070503062802190e0603 77
    0xd00346801c1c442d0b003000040381b80100e032105200c00100e0715410801040542a480424641680c4034034104107040e49580c0d24042040c00d0004202d19140001941540540c040c50300c88442d8980003180d0780105260607010750804c01e2091024144628000101003070304541017280d0502000c6501200c540707080f07804100194114400400c120745400f408480401e006060015520b0000c0d10410101c40b0001e00840700c06034460b0800042aa6040c20240288554000743c0b0019805507002511140c040c020280b0b40411840420140481046880042c11028241d540032003907084184030b23501b80545d4403000280c200603000d107039540310b40100c01c0da2500c028003c608513103a41d80b018001d0080c8038107400000300240700000c5e40190540d8003846002d640718000074242d040142501c070311107c5120031a07a80d0b1203407000308155140002c040743c1c041c0d0803150b60b101c861030800ca0080301c0075600540364203060020075181c200e280f09901c0c101c000582900c0c1e41a003818684103102c258001103460b040d403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 130120971 1250 130119721 130119757
    0x1206070219060227040e030306010c0b191e06140a14120d0903030905040218060a030915060e0a06080304090902030f0f0d1407150e010f0507051905 65
    0xc101d250080e16034280c86000094201401d003200c400d09050500300c42181c08000050100e01410b01e4031a1240742e00e101c0c4080c52941c504580064080e00c00042d00900000b00e400010b074244240d20385010303004440078018440d140308424544081d01c11610844609450600c001a003018600c00903801c695000d00750360342c040c3c500f4080404c081500c041c0c141e04000051708031a030000c010702c11400303980c1050700c40400850950074010300070745840e04107500440c81040030801107032210441c0004680200d0303000e0b65030000c00000b103000c9c2420304070003403526403203c5215408150700d400540c2503480d410b40e000110307a200380228064984c01d105207410398000300b0051201904a4014206e0301e800074007110180481003c105142030304e400c2c428070580e0849207202540b150700c00c80444824140705c80150030081c994481c103450356108404034910303a0381c40302c8800341c07000290800300ac2081104070810a6142011001d442980701442103209221fa00002c1c14500340504256a80200082c1040c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 130122221 1250 130120971 130120993
    0x121050d11011b02061501020714040908040e01080a0b0702160302011409030708070906060f12180609061b031404020904020a0b0a051e0a08151908060612060702 71
    0x41001c0340600d284042e540300c21011945184050201e0208240c65004007094940b28010072801c060312103e072030454200030400c001103420190b103900e03480e00c107d60014000d9070f6071800c413082d449240e05c084c4640191800005880c5004200c4c3d000950040302482000d0350b4199040762140144030040c2041580c0a005002652150011b0f00070801000c002c0351400e04038000192800b5010383c02080184d1059005102c480b0315402070000418003800c0c281d0118041c82d070040c014646a000083c0360079501c01c0201c2c100210b50142c129041d41140341005010000d08041014107d070400740300208403500c00d1a41e80c03d1107440703081e034074442ca095080c0d203d48035542040309035a00540160303030001c02c000012911905401c010306499840c1d803609503443c0b4194400c90f6072409040407010120b902030215951880e0440a900e60140850741c0c00410080384d040090750000c0c3c010007100c50541c0c820030205007000005442c0e80070b20401c96503903204000966503c2d94440003107880c0c00c0103820003c1e41403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 130123471 1250 130122221 130122227
    0x114040e0f0910020705010b270a0c030f0609050f0105010e0a05041a0a0602060114011418010207080f0304090f0b010c03080712140708070f1b020d05010f050121050d 73
    0x1d40044600043d5802d4005541000c0180d803c21041601c0e21f0355205040c1403580380c002d5403007140e13021015820354509004289400c0041c1e000703060a00a0351902c82c0130041d10700c81d41c4414002080803e0800006442d58030b507000401040720841c00310400c400000c1400c3d03000d0043c01d4104c00c4028102c030102414403040c0070107040c40c0c1003281c1c043c16417070809441c107566501000340503058950051280e0f40c9000201c03440003061040c0c5506001c034825001041c4020f440480e1560b41400300e0300c80001c086e80004030300c0e08225500501c804d001d107891241003103a02200400403110300721000c0c80340042d08030340007084450404640b8041840d20407100000303070049040b01e601007014140300c451141c00442100c10703600c520300441a041d03200000c01c21126081031450350005000d180c001442524003401500754004140084c1124090301a654110350318051001c100c0340c2c0c00b0b0b000f8040000d041900402814081c05803414140f250070314562400e0050408000c13841d0003900605011160070401c2d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 130124721 1250 130123471 130123501
    0x30603050f01050c04231810120f020d14070b0306010e0102030f1e0409090303202a030f0409020306042306210d020604060c020d050d02210a09020114040e 68
    0x86d5080f800380001c0c2865548510900d41d0b440c1041e50a25a14075046100c6151100036811914001e5801400780001c2010310300c80059155050790180c03038504103420700e0a0015280b5481e42c106115207040410180000e001540c0616000e890b14603a00107a1401aa1640a5600108141070041c01540300078074107032048013000300d03050b40f0045c80c190301ca5410a0660300b0000080c4c020075140d520340d809150b03200081c03058001119583d94108100703130b2800041c8454a001c180228082e140c4a80302024051013240d14421f07a0b5607010381c2c0c555545d0103400180d0000c9400e0f030310692170004040c100340030205000c03d5400c0b6202d450041a030f9450108010041d1200400700000030602050a035080200070100501d11645c0003050362346001c0c907018054585407884a01103410040440300d886800006890755442c504e280581c40304070010440220181c07140784c95151710002d400f805000113442e1301950a0b18000e90b40c24003929a203034040d000e01d00c60381c030a44ca0418809400101c14035164110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 130125971 1250 130124721 130124759
    0x1020a150506060705120a1d100c0302030c15010323060f0901060302090c0d11040506040902210c030a060b160f0302010906020d0b0a1d06010c031b03030603050f01050c04 75
    0x4070508000541c0c41e024540016110070114200c0d000a004018603007181d808e200f124a003083c4034044401c864080703a0404403215101c07040c44400300719041014002d0041e101080484021560a814045840e01c03521000303220039296001c0c045038840c070341d0b901040c1407610b003562840104825102c20346d4040d040440100349046a5595071800b00060741c0b21100d81b805813030b041484d070782c660024100c82c2040303441c135000c0c601c2403a0080104004a454210944040b94100da500580b508004000d03403000c07641a400c4540a82045d40820030140080343c0a07500513417014030100038a47e00e401e01c0d9251807281c051647c0b480c0c3c0940b0b40c1c1a00260300d1030800c04140340f0030b00c008034030341403555a500e0aa070425040c050480d44c8981d13041045042443c0c01000806070b0400140411b0410211107103000009080241040710315403036001850b000350609ca91810341c81d004021800014100100117102d0b50004881c6030140c0521200c00e10014040c56010709507c24025252501d1f08208c6201c2c0810420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 130127221 1250 130125971 130125979
    0x6030a230f01050403031b030e0c04090602070b0109050106180e040803090f07060f020c0306040b06190f0602010b21070b030703110409020904050c040303090e150d060f0b01020a150506 81
    0x4501c00d0440001e0042502852194402140c0c40c030b400d84080c09059029216402054a0800307800b07403010380001d000b00454419a0002244595410030901a100704040940301c4011040005101507035580a1812180c241e0f4805010107031064203104800b00741c0c4038405200082001140c0858130b03c500840e0046461012101c02d5034581c0d03030807400c0c507180343d0102021600802c401041d558046c0050002010700f140540b0380341ca041d40e1382c14480c50000d40f61a0081d5042100b0146d40c20201d50010080d00801e41840a05039442d00020301800860003442c0c010f40c1030030070080511002f5186044401d01200c040d00c40f00d4241602030907e46c1005105038101512172911440024450b401400600701c00c900150303071481040706000941d04054140c0c8607640c003c10081010940c81810081502d480722a0203c0d25124840500c81c0a085441001d80c8130808800f80c4040101a501c40500fa40d103074903040c4250101c00005a0b01d450044801030121914811080c9444201d64402640050010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 130128471 1250 130127221 130127233
    0xb12040204021804090c06090501050f0423090112020a12020d0f0201020115120203070b0c0706050a052b1a0f0d0609080712110303010303050405090a110d0903030506030a23 76
    0x100002d06071031180209440902286c2e10900c0000c0d882400803019081c01e0070001d2401140ad00e05000b01d1042d80705401140d14103d5201d060392580c01140442400c0052192f2440d50711081f803031038a860185412440754801d00030001c0c001c1c2c204030b00c443e03005030000c00070741c0044000d80300d204241001440480c115540da82484078030b00e100f501e2131742c09002c82c02c4400c141680c0078414186017101c160030000f510700052000e030360005c07400600c0074280d0b0258038101740c60b00025039003030311036004903e80748480c0c0c00d645880b040301d004510fa505040c4900e1542c18440e20031403901b211119668414140c3c1c01c82c040b0005007409042100d0202542ca00c9001c00040d403415988504445800500040395400c005e12418064254062141d140c03181d10300018501d903504d96031f409002481030b48100e42c004c05140c1d0000329101e010707030711141c44100050780b904d42c0c0d00540b895800050040c5482140401c4c90f00003c1a02810005000c01c443ca501c0f50880e0036000c1d42c4107180031440380080c805003030f600c03491f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 130129721 1250 130128471 130128517
    0xa030e2701090207030e040e060105100903120c02011b020603061504240807020c030a12050d32010e040f020607080f04060f050304030f1d041107020306010b1204020402 74
    0x340e880d841c000d0810310801030701c4610710f20b00140124040d0700784500c50350401520144203803010800f9411103008980140080225440c04c0d42e14010590002d00100d0070f08041045442d00403500030940b41c402d03641e15000d0130704a0f4242d42501c00009010b50040c00520010781305042c07c3c515080c640a00004650405950382805100601d420001c40c02011030321000c1c2688540220342540c1200c810300280480c51100b00100395501000a4050141240c030040070040703a00880031240018103a04040c03004205c0313600170303005d003448501c04450310454020600c0854429400124180c5200d44400030060302d658651594020859405a910000400184000800b482c0c002c090307050208560581f200e01d050f02c01f03040e504200c0c40344400e1200c100108000254010101482c12000341005018a9000e80f0814400391100320b24540062a000302101c2c800d031702e6000f1f080d120703108038201c1c0c000b603880381301e0703a103850091501210021100001160043c506074024043c0c6034803d116540c51020701c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 130130971 1250 130129721 130129789
    0x1507050a032009011107180515100801180606050d11040b07060e0106050114091003150603062103050711010302070c0e0421120e0a05030403050706110a030e 69
    0x40708503802c404000005808010f542c111031400781404202018201c564078080c0d050201703c0000194980306940c0d50001500100111044046040c2c050701b201215400104041e0a1030800e0041c1714581042c4085024245002c0c05904103440c0c45603a0345003014032011049020f81848200c2196003101400046460002140600100e5000f0000881d403d209900e04908448603600310904005d9120041a004d0042700101c0304145019603402408124015081340203081c604030f041100400a000021b10b079905420000035110106603213808000d040f250744496004040300140491070600460700401d100e4003004c00c3d10f00041c140545840099034a04541000c26004801c041c1102001e05c002d00c040455100c1803219806511200c8004144000d8140075556141c9451540c407034072640300800d401d100c0c058009900c602202e466540307a180440c1c6034005800f0340e1000404000d40c80420580005000e0444da405854641c5941d10a005010904030040300c00d10508000c0c20002c55a811 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 130132221 1250 130130971 130131011
    0x12020c1606110c0a03020f1203270f0a06050a090807091b0c0803060d0501020918041703190203091f060503160305100506130f0507111507050a03 64
    0x100d409108404141090006441100c001c8003515655001242c0405152210600705082c0c07901101e841b003084840d0320010384c0318100000104101e01000c40e120310301100c50320f504500c5c2a010307051011032485003000d016440c499000c0c0c42d07a20025030841084014001c00c01801c0781070380c600d45083c40f6606c0300c01003840e0103030580c00100d0490341c9840c0b03030313848180540c0c003540d0b44141031419081403c1c40343c4800501b07010207010f40e4829219501c2c070f5002c002007541121541640a444942c0c0e0030050700f00b5400b011021241a55284094282000540b00c2c8504582c402e8404200608080501c030300c1c62002900002c20950b0280715480401c0c0000922111110403011010000700303181e82800b00381418002014005507000d66014020f00010740701144c4059105400000000c0999519000404000562014031070f010304d0416101940300e00c6811980c070030314154540548034802c0020b130542d90540204a042c010329000003007031305184950011b250a130240d20307011407603c1b100231340c80e03482507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 130133471 1250 130132221 130132243
    0x8060411040507180b0a170f06030d02031e09010311270307032303070c03080c0706050705061609051306051201090305030406110f04060203120604020c0a0312020c 72
    0x244040020085440c1a0052583c00000c0d85014141a60401001500079415001c0c4a095181c04203da001e91482180c550708229002001309895040a401c851454001034072080c1c0603010701b25030218442d000000311403a600300140d040078407808040317600d940c94100340c502504060729151121240000100a0016040d0059880b54500b06582ca4908851503030b06c00766002e80c011000400108690075060441c10f0100b14005040046103000300303003984540400141103500b405400310134042d030f0001a04140343c0300421507014070344071030003500d10f030007989001883c81e4010381c00200c04a0f0201c0101800c00510b04106912584400000d0804121000301d4105603035038140800252601c003840450400000008012001c110b4030014442d02c001080a00460745411051081c1ea11800881d141050080b00503625103031507940c02074603603100ba18004004a0040042a0245086d2084844198034040213060320292507038292a101e40100d003a1101c0c40d03003407243d0ba011080c02d11501d1030300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 130134721 1250 130133471 130133483
    0x80907060819020327070605090105033c010602070b0301230306130b150a0303081504020d060e1005031011120112050d0c030909020c030910050306130e07050d020307080604 76
    0x40030742c1d2903a1752070004171401c48450661051310100714883e0040c0440d400044286001d030765a655040825100207229110031441b5990340340300d4038000004548400381202c0040140c00c13580da8481d0100c0e60b03a10705003d00c0768800c1040004010450170b0300c98591800400c801c582c290902400d0010b810500d00302c98200c1e10140c1d407540c40003002543c84500b644051801c4802100e108450b01040c080d003401d0100605219107a40032801e05c080d254007861100c030340144159568000c0301c1e40c44001e05002d01c0381c01508a601c00106a03000d464a440c04159a40034006141e42e10030803d02c0005030080c09813501c0c51143c01c00001c1062a040031041d4081c000c18070401410744082e14103140340500300000c0c98104400407140000007a4060480c0040ba840481c0142c1c0728040071640604520500c500140d10410f400d102c0d0500c1030700240590700c40c0794211000c0d4242e6000841040959210b490741882e650400401030007103203070200240300301600181c00ca4000b5901c0d00b41d0b5518000781503c007a00c403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 130135971 1250 130134721 130134751
    0x2012004090b011416020d0506071205060409020f01030c050409061707150203070314120901060806010909020117180601030b010306050a09020d150e07090603050d0809070608190203 80
    0x80ca0788940100e5414400a01e0b05aa40000c0b00b5150903039400340c1101032446848000000d4103550f9a000b01100316904503041e646182011b40300548007600407102e00e91400d09050028146140c5442410b0442e50060902406403810314011001804010340d018180034051101003200002403144901402903902c1a44c40f440055950300d1030140c2030384c890301440c400c0c01d81c10301d2241d07030220540700b030258581043d0781c4c888904580785042e40180000315443c03c0e0090100031003003005402c454211920310042d60003690300c51600707000351070f20000c0290200d05119400c240f00c490a9480b40c1d84070551009040d281ca141c02c4065041036020f0303000703840220314080103009008080c0314050700702251035000c018500c0181c0c04180c003d050700c04003401210104503601d4200c030f816044651000c0d803041c10b542072951203076101002002c6502040e25140b00710310f131640600d1300607001d00e402000800010000a403500d882201c5103d001004000c50007071000340c0c402c0291490000c1d5000340c0c0c007691084070b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 130137221 1250 130135971 130135979
    0x40615030807020307050f0109090902060702150d06060207050a170f01110c010c0503040b13140105091b15091306090510031505061c0204150e040b0915060f0102012004 74
    0x17140120a800c0302d44035589928080246a030848040d00884900c43d00104100c1141d0000031118052564080e40020340d502c0c0c5103030340008250051048802054080220944a0104a81c0c0e041a40a866006503101c0024011040b40481c0000d0071040c0c0801c4800003121310303003031a0039500000341a00100c00c001c1011303c0c041d2020300401002c1156417070440d080d0b182c40d4580101e4400c0140c0038811000c005100c14091100c011501207804411100912030341c24001015942d0b40701540040312249100d0040452520f00300042c02034240f1070004048c103084600040011b1104c502480c5085281e135010700140c1c0704e007140070b01d92151500100c40c001d59480c2d0306105000000c0d41c6458440369240100b089481d98491401103c1d01c66005403829441c0103a102190060031020401c00a90340b0803940040c0c1c401d03820b8000c512480c455403580c000c940b5411840f03540c03074800310091002078108100292450070003555542d0803000c14800401c003094a40d140d102c50001d5406510b82150300010144 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 130138471 1250 130137221 130137223
    0x1218041503050a0b0c0a091703070615090b0f0a170a05011a0111030a0903080a050d05090105040302010b0a03030807081905090a14150a0e01090506090c010e040b03030706050406150308070203 84
    0x6620020000c107552901c112646d0081030751150307011700707558080344552451882604009070340b0070540c4154200000341c0500341c40d901e98440c1d8032a010700c040c1801c500382c5560404980c4503601d0a0050705050b0301508204864000c0d40d200c000200e000d1240c3e030144000302c0d10900801d080846061003440550042000041802d246034074100c08685c41088240700c4c003940090b100003203a4010b0482d41c0c81d00d005501c00c44142c4104910300190301d0616080c8443c151041d03010500840c03091300200820403007402030210241c81840042e011504100005a034280201041c1e54014240300c410b5075140000d400354021110180d0300e00c1c2c0d280d1b0001e40c54104005100c0c081c3c040201144000385403a100303002c0111046c074001041d40d26050b44030f0b141816441d609400c030011040d80401529158a08041059660040c0d003a40d140042e16142070400c460906206d500d455a01c040e01a51401c5104d80b90300c4040d00014104551480e9107071204030508501d00040800b0f1885070041d13954401080c0101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 130139721 1250 130138471 130138493
    0xc0d060506040c080c032415220302030706031a060c0c09090609030d0905030d0e030a0e0a06080109051302030601120b0a02030f1303050702030d030204080d021218041503050a 77
    0x40c01d112040050012200305103040c6d0f03901c40c81d0200f200f079110581e03100c1e02c280060012402a0810110403800b0b20914800d009071134030b808084101071601541c031110b540a94818480650980c02003030b4180324a6120360803000810a40081c0b59100a8004000c9115036004d2201c41c00281c100902402152801802145e0041c1c0d60b0300040116090140070240ca03032080b80c983c40f44080d5640e0201c401c03c20248141d900c0c01207070746010070441c48052911074481d4046989907000421041e0300300c46601c1c04c01007000070f40f0380d2946d56200c0e43e0b003020b2241000f828050f045c041c1140d0003001000060343c0030080940a804030807911800c1000c00c1c540f00c0107520000d0500c080d202d00500c1003080d2342049140710f9910080d0301030b64071051075240c00c080d0740f1441000c0300603401d80121110141500c0e01a0014012034610008440c0d031007041e034204985550b01e0b0a11051401c80800480d01001084100c140e9040401000010810040600c1034a441c4456108036845d030001d1090005201584100c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 130140971 1250 130139721 130139741
    0x706020322022d03070605190507030c0605061f020c011803020f010c02180f04020f0f0d02060d0f06031b1502060a020a1202072307030b060d03020c0d06050604 70
    0xc0041002503a800100030141a81c101c540703501d00000c000f101e088500100b81c5942c8405401c0d250360a444410040c5681c1c000c601e003041d00007800e044076171628426401c0f034281981555884402c0265a5a464040e02018001c6035010814184c8030200d4000c000310322101e0602d44d00101182c1ca05c5d0030000d854484c103451001964141e880c410030141c1c94800302e403902000c0918007400c0c14421440050400401822070300c03140c007125001c110401d004450294002c1d4002c030f98003600084801c04110b0300c0c00e42076400c82e4000400644000060400710050250107070b4440e80454100102d45103681200c2e000da00c10744d6002d410907661100035054030f6055002d000c401004070150042d08a02955840d405040c01c0744176030303001a400402c14820701049808000c0400e040d940e0341d08500b02488210f0501c0d0152419000340f041e05514000c0005040c803c4a6014400d8841c0365512010881c0350703032620b4019400e5000e1301301a662199684100442c9151146100040a0074040c040c813007100c4143c88 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 130142221 1250 130140971 130141021
    0x2040f0e03070209220b010e06060a0e120c04020a12110301050a0b09010504030f081308010c0f110f0105040317070c0f080d060b040b0a08150d170f07060203 69
    0x101400045004002c464000b9010b5441d4a2161100351103000b0201c40740318181d5003207034003050690800000602c114101c5071030900741401070701c07003004000b004c4c481c550700b0502003810500300030702c3c9090072441c150340344039024180d45e070062681c00810160f0f4000301130f03140012070040b550070720810300d0310900e4011083c0c501501d0035507040502041c1c61070014028828030708800320305007216030310860440740915486002c80511503594a0700480e6500400c00e002c8450b00196800b03d00c2c1c803014491940e0044843da00d103030a5a900050947d00c210b96141060b4a5001d20f603080304540c5000d001c3da178013813442551500c420240e2004078464510001d40450700b0020481c0740c2e4000b06400b11101e5407060b070484140c60b0786601228071180144510390202c00151008200040c82c0300b4078401402e403100803621220b015a0321200042580010022050350100f0903010120124280c5803a540541e03000284482c50000b4022441380550400300301240c4482d000020881745490110400c400000180 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 130143471 1250 130142221 130142231
    0x318070f0803070b0a0209060d1a030a02220f02030f160e0901051c1713090509030301030b07051b01290112020a0c08070b07020609120403030e040609020d060302040f 73
    0x802901d034850850084c01c1c004a130000b05c2c522502d660304458000400400c42c594806490b08458040e002d0041d001c80340c001812404002410007003000c00b01180d000b01994141c4e400c00003840d03200b141420b10000407940d00c40c08100310011910085019000d0a00754140d03c2c5409500c49640c0c101a0003128100412018a8042610b9480640b070660701708036030700c00c0c2c95a19801c1c1e580742c4440c15500502603400e2884498040c0070f00c24000c0c118004000d00da020901d454801c0c01c801d40314207841c002030591082004001150b140600079800042d185042450130104a20f2811362060080c1d42d280705075500d5254400d044006905801c0a0104100c0203030b40045200010b4400d41c590f240d40d040e82c5400049418440d88240d40a8400c50340c04445292503220a0410300084c190490318400036124000c00329030b482000227031030f0110400c41e6200504d03003802e698003100d00501c1108950381064540f40d0100d0544e02c5070014020501c0d1b241400240d05145004020644124003a692403291904c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 130144721 1250 130143471 130143479
    0x6090b07180905060d060f05100f05060403150e070308040510030e100f0b0301092301020304050316020a03020a0801050702120f041e091d0706030209060306011b020301020318070f 79
    0x1c000100494002003030018059540001080c4075601d6514024004c03407600c2c441440e030751110341c0a00d001301d002d01c2416401c20f4882d200484a80c086000e202e07402407081c04100700180800d41260560101214042401e45112180c1c1e407510318150001c0b0303103079040032905108905000b03214040e0700c1c0c043d01d4280181c120610794103440d01481665001100d80341c8242404886443c0c10120b069034000d0001c10211629007000d0200362914460880041c81d103046c00282e50301c2c14029240100d0308070f0301440c9480a014801c0c0c42e00c002d005022a000a80e2480001c00740e52901c2c9803d009000c0f01e0008a0940b801140c0281040c40d13401d420307003070340c00c007800003104c08584031050344e0030303903072505403c00000c0103200340000592820750100500c00d0a010918019451500c000e01803121507808941003152183c4098013a40990f100c0c04e42c103d503060000a100d98459100c20105070040c0c00c0f080348000346500401d09983c01114091400081203c1120403030f1401c1000000628204841c00e16880c14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 130145971 1250 130144721 130144757
    0x408060f06011b11010309051e070506070210270b07050c010f0807050a0212030403030605090109090f060f091a07140f0304080903030c0f07090b06090f01080c12010306090b07 77
    0x5002c0050800c039110300c0d42130301d964026480810704c00c1d08401110f51268025440070400188600b403400c0c0c074018004002482d060040644140c1d541c01801030118013051202100e0947e0446070034040c404140551080d010051aa01d1002c0c1900001003544c8010341d0800e90314007038074040850304011107100c0c0005010b5100d44050703000440d5240c2103a9a1603c13200c200c0c50300301e030324400c581c241100000340400c140e010341c0400704440d01a0f601c1c0c2403983c5d03a500703003108841403030308003030060041c0d901d03203a00007805540804100c1c03070a07401c005405d0083d41c071440310b50a01c200707403c0904103250003401036040d040803815002c100140400b910b030004250080c00a404081c0004040355004101034903a44d405205880f0038401c0d00040383e032014200303207210303540b08464480e26060501d41101051541803c1d81150400007002d02010321714181c900045032521001404205c5104080c0042c80c6154000d81450740211b000307001c00705190080e411300c2c00031628050300d50018003018807549500181c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 130147221 1250 130145971 130146017
    0x103060506030f240316090e031815071506030c050406081b041103070c0b01060c0f020f0604050d06140105010c33061e150203070b0612030408060f0601 67
    0x518940c548528450f04c0b1101c6202c2c0d0070304055031303030500070200006002881c0c00c91840494504100070f0100d0001580c0e601e48074030660a0303004541c1170b402d0b012460b50510100500e0300d90904400c0034540503840e01c1e072509907810300b550741440644a2104200703100030124018060442144e0400c48107240c556039a0303544440007001c022005804464070030303654840d4010518441131a115558030315188100030702c400d104420444074400303030388004600144900c400000155201c250000201c0b855000c000c0d0400c1c1d0411200d910042c03c000114958030340f82c81c613030001c078402e20001c900703418101c0c042450080c05030481030400c01d03204949400f1854000b0000d40c2084004001618000c03112402080f0f6140110003403c2207003000c0e00052401d2280041d481000b030f2600150302c1483e210f00361003981071140e64091005a009000700303070108105103d101e400c140000c000b4040c6c8030034010501d045800c243c5c844005600314000f00300310300c01400f2119a018000346080c0c0e281050301e540020143c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 130148471 1250 130147221 130147231
    0xf0506010e030106230604091113060c08030f25210c05040b0f0f1c0b1009180905010e01050f1b03010329040b2707140604030605070507020103060506030f 68
    0x4405c42c1c141603922894102c6014240c081020b00403151020040840c0350f0000c44500c00c41c0c1c0ca1000b0001c0c0ca9031081d07422070380d03039070b0b100f90600c0c41c585540c9110769400f2800b07031610f04000186003086250000c0c0200b10101742c000c2d522603544e030b079450701c0c607903d0380e40405101504020706101c8405451076000007190260703a1445030f515114020004203011500400002100c0000002070b80328107081c0722140303141c004440034000d1040300348210070710034a440c4000c07410f004105d50140030b00c5032041c0b64001e4038400c40c0020f0002030f000c0483d10388600703485580a50345007507555801031110402000e54040d80c0210a1540d00d43c0300121100d61001ca07200500c4098404070201d44030742b21ba81c0c2022080c064200000c1604103090900c1d00f400c100842c001d481c200301c1040030619044911005103100000c0000781006850308a186c0781c84500c05051403803115a0041d400c01000c400180301e40b107100e0181115a44007502d40036940700240441d1160380040384169018000c01000d10141460f169102e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 130149721 1250 130148471 130148519
    0x910180b31081006030c060e030c010302092403070201110708040e07140304050c01020607020c010804022112030603010b040204181d0307080304120306080703080307120f0506010e030106 82
    0x11580102003415121080e00a01c000f4041e00340502e0f0030128980019098034000c4801d514101c1d940c200503604002c0c000e840303c0e056044090280c5080d80070381d000e0003e40340e000e00582142e106002c20340d40711104100c0780840342071001c414040510360910a0100d152500040c8514080ca540c0750202903020314440c425071034071201c0c0000c00881c03092200136102180200e4184c0c980c00c0c946080c584070a905070481d80184541800100007074400100013650910603140d106c1e65880395005d0013403d6004050b001c4007000002560355003d42c00308448100414911412600ca0400808150940d40d070130405511a5006101c28003811540c400c40c0c020710100c519001030801000d00440e10b0250342407000d00d015000201c1c501082c80a03034001148158400c00000041c121030490550484810340074001070f80d07000c0d00c1c042c800a02d03d40001d5400018504200000c1800c510065050b1307001d503618401c0d0981c0b10400d100440d45c000c6003d00070304404800911204d410700662561140a0a800c8451 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 130150971 1250 130149721 130149787
    0x90308041206021204030e01030c05040f0b1602060c060411030601030201080f0603070f08030d11040b0f0a02121b1c050a0311040302060307020106050118080304030b0403050910180b 80
    0x41068650484041401c0340700244e02e1483c00342400ba00301c800400009010034100618485000e00c584201c07025610316034000e1003040c1c200421400560002d4907840c00c8041c070b0350b03a00000760b550032005c2d06034841101c0041481d45860b1401441030a00c021901e8001e910a100610040c0c0c1c00c0705095502005a901c08034169480800103031504250354403031010480c6c101d801141c0f06070040002c1c00c0b800309260041c0020400303014148284d01c9103100d5508005014050300100d905c000c00146620100c92048409421086548520b281d0040c105050320075119501060541c109004411007989000d0704160100e08081010b0414415216913400301551142c01d148455442000c0d02e01551f005800c6507140d00d40707020040d00812050050ad40801e0307076020000450095054040c060300c45d941c000e981071520710382c5c0380340c808413000d80300710203100c0305200b20784560310347e138140140800c0c5944d21f06c10301c2a2008404014101150840343d8a020300304640b11318044071580080241380da804038914 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 130152221 1250 130150971 130150973
    0x3020312071704060c02010c050c1005040206070c0f050f03030703021c021e030a081303090302040917071113021305060c031c06060311040311090a0b040606050d0b010903080412 78
    0x1400b525000d81d07011201030310001e0000744000c0e94080003008145400070007074441500007d4803107008504039220980e1000107607500900c807e03004141c00c140f0150005040c2042551343d800f00005582043c2d1012040310410030031032400c0e810b280e482c08410b40143d4035013241610002d482d0034144880b100344011b5030209046240c400c20050300ca50a1190024081c50021110b0070b0b1641d022002d4480003602c0040403c1c3d0142da0150203151866040d212010b44520719400e10014103106030003a11104989820854110282401086058440c2d040601e041c00108200130381c02e001c0311214070540c0e00c10300c90021604071941c1c8a0781540e0003118500d484401c207a8440d0710b58807035409001c4051441e954130117611030742c68100405407003454406118214010100303140b00d000c3c0748801340c140f50785401c0707021282c00c0031100203400c1150341002107015500000410142d983ca544000001100000c684420234400e05c52240043c4091a102c1510340ca1a12181079a01660003140d450941c21007800e4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 130153471 1250 130152221 130152227
    0x90609211e03020c04110a050d0507030204030f0f0302060f0603070e130218010e0f041208040302010b06040f0f050a05010921051b1906090b1309020d05010515070302031207 76
    0x400d04181401d0704401c003026260003502c03070b21041089800740d800e2902c40e04080700c5007001d4480d0b40d0207998800c0c4c144040c40700b90101900300508800b0030701d6420000840030038034070800c40d112680582c2d000103070004180b034020303d4080c006140c80308103860402071250b42c0c1d41c042054411a00c0300301140709682caa88074004070b00985258020740c00b21300d941c10707941184c00d060b00c514104c641621640c499075075400a07180c0907040844000305130a00a80750030036458083d100031a00070740288000603140d940c0f0004071321142e0140d04902d0540760500b1040103118680d05005020f0281500c1085400349010001703040051640035007410724004101031701441643d01c00d242000c2e03810070100d420f14018410b000003c00e20051415005a02000170440003040d8400000102d80d850741c3c607030305260310744480040ba58001c0050601181e8000e0300004c1c052109001801a05414400018095162004001c0b80030f030380d00081642c1950901202010903008000d03542010441030f00454242d80f040421 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 130154721 1250 130153471 130153493
    0xc05010b04060905090d0c02010509100507020d050c03010609150e0426070204050702010911120102070605100504150f05150403021018081209130e03070f0309060921 73
    0x240e5002450300b000001c410056030000d602484144054a00174984400200c4480c206550301030701082d410410031145041400c014803e041041c5070041c20f020310340d80020340c42031500e2010364882e80200c442c019186030030310824000300b001440030008a140a0283c6007050101d2240c270820100b0310001606008040c0c82e80703400e0070201452600604c0c40f04007070030216040907105a0003a07240c0380024586500504c1101155070304031078052030b2000f8400c204002d5140c0056a40646c0d502032000c1c00010300140101030181c0c1109903e201042d060005000031180320748940703244501526001c01c009100495014151030050f64240c01e419101c0007030801c1441145d00094000c65012143c3c0413065000d010211181000c00b01d0710000b42da0b51011079980d604100d48418612000c00c8114000d10b000360b81c3c26011000102e010425005544045082d40c0001100f80e402509058010f010136030b10001003405400b00e420f180d00100e091460084e280300b60344030300300d403400108102c01040c0020811a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 130155971 1250 130154721 130154741
    0x31c0819020913020703020105060612180309181807030b01090506030c13090212010c02030904020c1005090d090801050f0402040b01021f230c0306240f0301060f031a010c0501 77
    0x10080700c1d004843c5101c000354003454041d0019407800011807924505101240c00c202100e520004181c1c40300e0300010b00307134000c00f0003d6216200420840110342c90380205084903205241e6010580d18102454012184100c13840b5485504102e00900000f0292008a8103480b000b0310b00081a564400c0441c0c40c0000d04504a07611140c070b02c82c0b00510310000d4020740b80c214829250780c0084200446228241c0c2c2d051041c00c4d026070400c4c4074075541030810354042d14034480004111083c40351039801c1c030300c2101c000b0b50754140c1541102200504083c0c00411050017440003c0080150745061404d03001035020207400240300d903440f107001c0d0813070303038070801408840c0640d0309a40720562141c000104003d02c8280e21482c05030324600007000f5001074640409110341b1048000919690f906070401607541e64001502820b800410486e07403003518040007900c0c141104071001c0b80e0303e504020002c1e1013903441c545180100b40c10181c03031100c1c419200340042554102030070054116132092038090b0143c007029034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 130157221 1250 130155971 130155979
    0x50405072a0f11011b021e0109090c0207050306070f14070614190609022a10020f09041b0e220203040809010906020a0b040f020409080703090302031c08190209 70
    0x105400600c40c25204078090752200b40c076005c840b030b42c1e0f8540c0f203080d81c40c0d9000701a42c002c2e503140c0514500842c402d600300c902da40515002c005175403105190012198084581360042c0d0003543c0c18080360800b002019003151490070003100c0030800070001400310070651082d0f1424030010072100d0802c01603402c80c03040081074003125190340c50041c1c078108850b6140142c04468030300340440044da100386407003101c05210410702200500599080024076020f0070804240e0107100704101026144250300c0907000c0314000000c09581d0340c45d02001c100c151501020902254100b103040318420a0700803100030040001520300c0c0b0600034420390f5407801c0b04002d0070b000700c055000004100c10042404004e0030b0b050026210016101c0d00c03060101d80c0c880c903d41c0014070740c142d10001b25001ca00100300045880e0b2005201281070309580d07940810903000410110041040500144114070707061000c4c541c1c08201ea0000e15264070319110080691001400400c201e00700094503071102c05061f0104e481d255030141c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 130158471 1250 130157221 130157243
    0x20906120f06030709060e1f05060d05060405060f010507230f060405010c18090e0703080703110f0f0a14070b04030b15030303100603020c010605150408010501050405072a 75
    0x95000c519401c22030320240b0900801c43c0104880026108440980702507d0310035042d0380c0ca40591044a0280401224801c066000001003507900c50303004040710a2011340110345424424240f10540b40c01400092140314600f02070369007664450103070703044142c0060810344802488079000101e401403000c0981e05004403110402451400100380d8043c901c124002c026060030210100e50151400d40e05072400c084e41c5104001421503900f05984160f107007c25074181903602e81d0b9030651036014220840c003180c606e500c10744580d41d05005524030000701c800a45016844107240d2a15041d00c103c00601a08803d40101458a010894400600100140e96650729101e00340209201421580c2c000d403100548920714042c10080305690003014035842e081402c0e0306000080d0040c0d00203440446503596150b4000800e07a84815021012658000d1842c0d903640c00c0c828084e0959a0580025004909100c1031003980395004141c03101d10440c0340c13026074444c0f1414400641030200c0c1c1c500902400d03012 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 130159721 1250 130158471 130158481
    0xf07061706011b170a020f010501030f080d02040f060801140a060206180c0913050d0c030207090e0c22150b030c0a020f03130e07110a0b0702030403020301020f0c070e041502090612 79
    0x41c401019045c845408440245110100d00b42c00c5e55002d000c002c149408620030350f0b000440101c0a011000c042c55805828691180b08214124149501c08400511500b004005544140384060b6595a090b40c20000762800d04034041e50f20140500350f10403909082e507901502c1c2c0c0003401001c050480003480c000050a00c180d0406d150603c00c136090340c050141c0020340704510300656150700c42c90b52507005020202d140c44840310081c207500d5014407050080140141e20f0340c2d10800032040d59441d180c118090700444403e01412981c007201d19005500c4941c82c02c1c4000f20038042030740d5000b5888080d965070795610000407400c01c15007001d134440328030000c240103407a05032540540c0107403561b10501c14401d60740c5040486031b070031224407002000e030400c18801001c2031a0700a8617a000400c2c5c0112880c160b50b0341e0103c0e003203078805a0750030581d4002052004080d5410701100005000f038034003014580c102a114600e90035081882008580ea0005a80f1040d403a000c042d01c8003a6480e2440101914007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 130160971 1250 130159721 130159763
    0x1b0c010e011a03030307020a020d080c0115080d020c0604090b0105071e1109010b0a0c020406080d0206040c050d2f1509030d020d0207060e060d0203090f07061706011b 73
    0x4041c0a0b1041d080c01052100742d0381000015640b146030b850b401081006071a80038040300d024042c00030b03500e5032410410000c0102c400d009403031310540003000c260512880c01d15981d04006510345805c3c1150071100d030741d1030959142401d48082d01e248000008a41e8090340040c0c0702e81c45000c0004044540c0c0000c081c0da144da00440582d1721714010359400c002da2070350a0401445803801d00913140000024041c0744030140c4a083d216074480d1000c0d00c002202c41d212030040345004194030820005a04c11410441000100c40154000b040c00781c41803916202039540b50b091500003801c01410482400c24424511900c0540c0704000e6200503290008030190300d600340007107502ca400c14038064403a00c0300464800c0d10001e050300b810181c0e503015261607424803100b12940c09036003003016400003003802004100080c40c4000c2d40240139200041c9a4420300d00605410321030740c1e50107802800302c1880e00310b640074002442c65920150034a0203a0208030000300303540418003400400717130080102e80707440051040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 130162221 1250 130160971 130160981
    0x10212090708070603060302010c0b190f0c030e060103080403080a02010b040513060b03070b0f0a0512091c0f0504091d0a05031809010503030a05030603151003020a080102121b0c010e01 81
    0x1c1c0d0b51060340d0416403200c0041d0181c0b9941d2000030300080000d02041e006c102800c1300c0da50000c804400324034628854068600540f02662555103215658000700c050081c0c0600c100e8615034500c0010340b01e150326544074070391603004612004e480e14030005850392030f084c405c0d4454200d03914018000c01150403d004014ac40c0c1c40a504120740707507440c0c000060294170380005c01c1011100c41d900301c2c07803400303948092140b03150f048002904240f01061001d40d074170703011000201d03103d0f40a03280208044681d410f0114030303603022400054240f010000341072208540c0070003241c0945003210b41c00303c0ea220f01040c40304a0076070400d124403028001d00000c8020000e010000300720b00070f40c0007000c5030005135200412806090070312515034103900410034020f20764010030107075074403900090640e1003086441c0038000e200502294032241c02c4002c07210a00840c9058105540a003c03680004c50800591800781044001c1c09042807141c043c3c02049604170240b490229180c01152070000d002d661185031180d400b80c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 130163471 1250 130162221 130162229
    0xe0303010303140306030601062106140406050603041e021f02251404090816050619050412030b15040906090501080c030607180b18030c03010c020c120102120907 71
    0x100c9110404240650a6082d40c0c06100c5c000d0103080281d181030070681b48010038200300c003c141e0760700c01d40c109400e0703051003a40b00809034800e014508000e130710200170440300590800c6100b00720504c00c1c04041860300740c0c4078484601c1d80404144d6070f0180d00000c1c00c04452107901d07406d480000c1d1605601075034003017500000401c0000d802d02c8a58910130420800d8022030080c0881900c0009034050036241c141c01c44a03c1e42d026043d403d1605440000100b00201064426501035211109000c200c007a0034103082c3d280000d070441008181420390f40c1041c08114012200101a110440d40f492607603401405140c4039040b00f4015178071950341c03000340d0103410b0b90f02c11a84410310b48400050b06000108440c3d44458005001c1c1415a44454040c1c070760b899180c241c0d04090305032180104894850310000e000b0005038a09021807078017a4000c041c5440c030004001d50080c4d0609580048242e00000c64030180941122a0500700088000460080c003c0421100781003650038248419410042070314003d0f2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 130164721 1250 130163471 130163477
    0x50a0920010f030c12020f04080102031812280905060a110c0d05032a0703030504090c110601150201180f050f031c0b134803020307050d0e0303010303 66
    0x41c060300b20b025002c4558940903240030035040c145140c090706041d40209842070419550740c1c101911400d5031030032038000311441043c0989030b00ca02c2c0102c035420001c00f4580c80100c80b0892800751000303980c00c62404011454650321494039900c0f02041d02403121304001c0d1038090032554480405250081c10401c1c1c90000c010340b401010303c00c46040c00e04550290403640c110000394030f0803044c5081e1a41c5440e0044001c0c0702861540c614062040042c010400210301030350340c0d01e80b510704124240048554418024040c003404240044043d0b0740415a241180e004880103c905904098203a01600c800307445407104841c807903180d9082202c00094036040d20f011710221042c00029041c7c469892050202c6001c84040c6084241903000854000d040d020710050100408000003941d0360b001e40e03102c10b0324a48a902204800c05000d01400d8500040310754940c2444404141c040050104000072080303001015000000a50301074080d00488201480100702007120340c026a40064898200f03000031800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 130165971 1250 130164721 130164737
    0x108120f0901020a0501091113140c070302150405010f050606070309030201031a04090b0a0c0503070801030b060d05010203070305090c0a030201170718030c050102150601170a0608030c060108010605010503010303080406050a092001 101
    0x40c0c1c852881403541604038402d2000b4182c80328404bd2001f9000060101d0452068240c0c0c0500c0b0900c00e045240030b40e01c104004220203044045e0071058400c01060703240100414401400400e61082c91842103e40a00f03002400c08148110400b1440589115a400504107078000040108a03044188920311100c41041001d202e180c048409100560b0880c000500450041c130201300010041900003a0003130598036a10300c15510142642c20031039800e00441c2c0e0310010080304c040140521075942000321081206142140d001800004400311011182030240e00050310946c0940c003188034001924880b100710568a02c3c00f0410203405008031401405516009104e5400800d40c0c1801400140c66240030481d6040304004a9000209405602512180c1c0001c5e0b241090004118503030081d40075104640c106424030707083d00c810703920182c100722040004002003907120046a070416030044010480313855500400c00601168a4090a8a480408840c074404280402c03138020000c2070b01d41c114 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 130167221 1250 130165971 130165999
    0x40509010609050a15050d050c090a05030309130515191a070f0212011e0c08060909030901050a2106050108100b09061c150e0108120f0901020a05010911 67
    0x80c161056114058201c03070300440170300c1952441032100c18480420324001e41003014491741d0100b0358805403089080044000340e031880c24284a80b001d8040c000c290010340c64000d42c407002c281440c02c00d8140c0d605460b5a140404d50124003c0408903010034020020501800e42000200c1c4488051007000190035026105074680240482a64800d0360030001407101e904140e0248106540e4511256045550f00d001c0c201024410000e419070340103070200c0000c0c1d04214070101a0900c0300182030315109001030001c1044d100301c00821a80e0910003071a220f511007091480c1a581c0700e02440304a01202d0203003605c800b0314031459000070110f64090ba41c1c5a20340d200e002c5801f041007001d009107800311404103c2c480e510305001c401840802000c485244a030000000f40c1d50849445541c6141054090482040000c40303a1106501600207080030b4021648000d60400070351141404500c00fa10011488a40c0ca038000d10990042940220003404412401e10303045c510a000c110009105c0d0bc5105880782c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 130168471 1250 130167221 130167227
    0xa08010807080706020a0f05010b0405040b060f09040b040f1502040801050f0a090b0714070501020c0a050d1106010e040c090c020a030306140a030b0a15140315060303031b0408120405090106 83
    0x15013203d13242e4019240480260701c890000c21808441a98599210715140160b6146c501c101c0780300d02d015058621203800e0840400c1040c183c20400b15100da441d990078407012600e950700c5242c01c19401080440c2d9410603241004040c2c18179084100b02e94404200000c410006402c01c0344181d4500c05c4408050ba03900010400700c0745c00440140c0600741120001e50883d0064001e41c64210384200002d00b080682c2d540e003400c1e82d0010846a18941150303155600b040000c0184510000d07141c18018144142c00c0350700c44d940c03501403159007130702c113810b0000c03a040c0003801c0d0110300035260402083c4005e1a51030710280d59108107401c110b0002e40342400009000b5811a001150311034010030007007905146464481081c14094902d003c001c4d0b0b580d80500298488003150740040c640303078994142da021600105400e2095078288840158042d600b0040729540100c1183e41c022070b403a00d5017500141c0aa0000d80c1c5004681100040380700d8040100508030b070314000341048800c210399450b0706a0301d50f0400c0b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 130169721 1250 130168471 130168483
    0x80613030c11011103040b0403020a0e0606030c07030e060a030b0a0f06120203040203100c0215100b16030903120e040608070e13060b0d0b24011b0c05060a0801080708 73
    0x680007400c0051854005100450000c88002d4145490080380050055060450b84203601c803001e042c40018041045042240041009111140f1007901a01c2d1600c040745461200802c0080e440d580002c0600425010f00d9440c42c1001003c0e10305520384c1d001c90340c0903005002164690b0f12610100b10009100100c102c1c1d51b4041d50540d5503200e9a501e40c091008020f034002500480c0d00d402058094804c5c01203030300c0303850340e03102e911b40c0180038016440480034500d6502130401c000302003111100740449103900c0700b144e0180c1011001180c001503d41011034000b0501c0e00000c15481045d034054407081d502c100109400001140e00700200d903641e508103980c688082c03050460404510001078054458080708440541c011200410300c0345500d000540c0c1148281030889500d42e0302c005005601c501348503058001c4031811582500c80c420000040c090484148c420540c07038148040000c03c11132002004001000090441600c80815400241640509025126091186141c0001e0029002802e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 130170971 1250 130169721 130169723
    0x3060b0910060c0525061404150509131506030e07080604111f03060609050913020f040603060207061b0c11091005090702070e0c04050112050907050907020304080613 73
    0x10500703030780c41c0280503642c604030703035505841d1401070004044400b0b5000d0002c440a0050b460080d0369907041140240c4201c0c00e001c0040c0484206101c02d100078100801c610011000c80d00b88282c560b00341500065203c103000649106060800080219110301f294552003524a180c809120b500d085c0c000c02d680d034003403600c9100d030680d01c0100442c011503a103000303035954080083d000c04401c00c000d401d40b501d000e60341c5110301d0009984440c20030202e984000d0349005400700b01c4c1c82507103500b40100c1d40c5000d81e03407881c1c020703103d0364010740d0303249050360b85503c842c008543c054425511291a0709201e4001c215a00d010f103030f0003070300344c0340000340038840d0041c10111a0320035a040103a20181c1c09125000320010521603501242200c0459199180880c1030722581c40da40c02055070301d00740b001050750740c00050a80480540244028840c1e030381c201c0d0405544803a621000a05d075501c002203d8505240c070b510141c0c01c01003440c18000403640c044014000c3d18083c40803545507403200c101412a41c11b000c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 130172221 1250 130170971 130170991
    0x111c0606030b0906090403050705070e07080f04080315040b130525120e0102040e0f090714010c02010e03120307050403050d080112080d060302031204030606050307052b0804030c03060b09 82
    0x30b010741c5803171803009801600910b01141440016a03995180003403a8000b5000c400c001c50411640592090540f41c0c844882400c8078154182642c4000031400041e0051403031042410b0004a00e88544c0e01802050300c000b4600016035134142d40305801404c0650301c48010790380500c000c00890540d13090008030101d40d80c2e5214804030340351054800402440d042e212555408100c0014141c18181c2d020303014081e1003458180a0507c0e10340c0b68a021401e51200c03410b0103c041070400305a0301301c01d502e038240e43c080c01c02c43e040b000210002401c25086105e000f80c0c0140100902001c2039000020b0004c1d01e103e80e0403241c154402d84401c0d43c0500007440358841c0c50880280c050001101807014114040141d00c011039042d850750300107420403010710400f03031034058089001c1050110b00d000e000e000300401d8024084980c20300e004200c4144092203042481460002c1c400c500c003110001c1c401000d6000b43c42e5a0f2969101e24045c0c40107002440b09072903560a0507403c80403844c1c43c1d030070340740038020501c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 130173471 1250 130172221 130172239
    0xe0d0203030408210412022415060d050106020304060f0318020f120d03020d182a0803030709090c1715030703020d15060e0906010315111c0606030b 65
    0x540c0d0f1094a5010364406108214964882c1241c0300c00d03454140e01840c4680e0541c0300c05090545d0003032402d44c8034039801a40c800c900340e1014125410b00c22171a0461159108004248103c00c04110300e8403603ca2400b822a10740000050b40310b50110180003a14169543d244407502d0341c6400b1019242d0512201110b01c4103d0040b500510740140740391070800c009061f18540e48600c04c0f50302d0030030107240c0b19031001c6500021b01c1a00c080b01c03446120765486c92102c158155031169104d82300c03a500428039605218543e103454114281c0f910b15403070001c00d0950101e07940c9103003803000240904d4040c419105010700300461032800c00e001d00b82e00c00040b20b910b4941c07601e85c1c0d51003500c0c824a001d10718826806018001c8040b000d40c40312480188290300418003039145001c0c29043e03004035002c030f0744031011083c00e1006001d00c40340b002c1801811250081506644001e000250740020008410507810300309001a204010324420408a509010113041c100811a40e6600903025501d03008104d43d4840440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 130174721 1250 130173471 130173473
    0x3060c030f0403031b020c040617100209030106120c0603060902030c090d0201030f060b040e0c0304151a09090a0b0c030c09060706020904110706180c140d060c090503010e0d02030304 80
    0x30815982c014060b1502244180700d9801c2c5c54100c20b00d50300c1200050304692114600d0b0f003454058400200121242d8410040602e00c0303541c1c40d144075000d20a20241c000407125819a000d4115401800e482e1000c00320044003880d21404141c01031007a0760109040170000111030310503100b528800da803010201c2e450714029104104c0803580902d000c03814595240481c0481980381d04c500d801801056400030740c0c5074140706140001510041c10141603244c100200000a800a03641c2100e02440550115a030f4022001d0a100303006840c03581e5030403103020000c0000e9140b0020710600214010360084030140c450b4030f042203145c407045414000b0500d04028030070340c0d418440002d00701780c0c1c083c06005003080c0c0f0490000c2c042d40d006402440384d40a01049000c1401070900c60071002140758941e42d00404000d42d6119842d0700b95114800c00121022480b00c4c044d15014072259000d648003504100400c4c100401034a0704030300b4001c542c00380d880c180003004a200d00040216207400c4c541c004600b1607840b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 130175971 1250 130174721 130174741
    0x81506090103090803150a05030706022a04050c030f06040501060e060703031e02040315050601080402040207051e031b030906031512030a02010903081e0106050a03092102060603060c03 81
    0x10030159241015035501900c03000c618400302842c02603a203800d00652503e000d00c204108070941b60491480794100f801d04000040e00000c600e8060314500040e884e0034120015500501c1813042c2c4c41c9074019003008108010090200c008520543e00300070004026200c120600080f20001d006070f070040340208582c45590b18100000d854154828074020409103808048981d04c2c00407030340c9020030582c0204e0148108441c200720602810075800b0200040e00e4030341d0009060000c00351001e8040c9500123015401d1007028807002c0ca1203412072403c45011404680055603d610828210465070382110f00008601c9000c81181c0c0c0300b0200500440c1552603100017451900e00c08001c0d183c2c02200c1c00ca000c01c018200f8005402c3d420308540001441501c3c9040103050b40c42c1c0109082c0b03610796600c03d400b084e40303481212107054440c20305e800798941d0301d044020ba004005000c400361481081e40c5110100d296640c814075041c00c4580d080e551182c4a8106140d43c034241900e1300c512500c3c060000804c6004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 130177221 1250 130175971 130175977
    0x9050f06040b0a1a030612060f340810050d03120203070c0b010308070b0a060b0d05060109050402130302210d11070f0611011b05040b03060a0801060b070302010507081506 75
    0x1c000c000c12a007a80c1d44018500c250149800351000e0040881005000d1030000b103c00440412400a4406881c106880b03420b8104000d044110132040001c0ae08400003000c040c080e4030740030554810031510181d5101400114088481280c0030083c0540440d260510090400000b54140c035201c410043c8883c0e0003002c6e42000f400c0ca420030004401b19004a02904a00340c003d50089252555641c01e13402c1040300d064005081101c102c0c1042c1c000c10030340414070101c07602001705540000c0c031a101d20b00122020340d020385c41160302c00d0010802044282404a441c412a4400c8886000c2c00100e03101558040c00c4000b00c80484c1d8000740941441140150140014500c091042d650a1600e0700e1100c009490301d5000b031000100703500040c0071330540910503580c01030320100c20101c0303c0041a400134032910031406591840100440482c5180e01d4003141c2c0c40284c860880240700d0789440b40e50241881c1c020304001d80040d070910001c40d0f109406580424011b10700710020010070b00d0304c0c1e0180304142d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 130178471 1250 130177221 130177241
    0x8270f0d0809040b0d031101060801110313050111040f0f05030d0507080a030e060f0103020f03070305100f1107030f09170601030f030e03010e06010f050301060e06010f09090c170109050f0604 84
    0x50b46915600361541d480f1085da1500034070a8075050070003549102c442e401c50385c05801ca040140e00d00b41c114a00030740490192a44081e8904101180060301c0c60594003520711220701014012000c5008540c075201d01303000d08155484d900030440300954401c1003645e42c00207501c004021680401c242800715031280700a100d44843c1c1c2c1400b0450618014040c1d1801d44221000300540042d00300602c02c5141905130900e50134070480041004504584449480b40d80e072844e004101aa10310f0b210031200c000b504105c6001122081c055140d460741e0401401c41040107100f600020102c2001150461002d0750301018210010000c01e03290b800e41c0c0d2020f404103510101034081c030004910140083d5024000d854000511070060310b070719403424100380c1898000c1e0704420701c2641402818080181180c0200d540a602480c11300902c1340701d03080644d250310a5400c49821076090100b4044c0e044d411841c84407811340d0180748000300d42c0e86e03841c818003120015075580a056180e40041035291030690002200c0b1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 130179721 1250 130178471 130178479
    0x901050f011106041514071707141b07050603070e1c0b04050d1409031005040807050f06011e080d18050303040617060f0307060f03060308270f0d0809 66
    0xe500b141d5042450000d00b110102c45050f404400340765003040358090b120401c405009040b105007040000940151a000560900005140c0000d100ca07407180c2034100c468010300d01070760f41d2500503003201e4000003c9000200d5981c0705a50000440742404012644901c9007a6185549065a101000400b1803070b0340504802d005d2501882c1c003c20300c540a5240118400c0008107545c0a4041010702101c00c14510441c56040501c5011aa034a000c038441c0700004d4144000103450b581c0d441c0c5001e46018102c4083c0103485030100100440e103002800700d05075400d804e0343c04410300d204002c0841410035402440d905420000720140e07140d000d182549440c00c9280f00c0e541c0c00544480100e032071030300681c0c06280060310b02c42c1ca0051a06d5000102d541100068508040703010056001c00c4d0b48100600c103543c20405841c26110072035200380e0120000d584d02c40c1006a444a80a0440402035000d840f43c00540482c21407880c45458855001c0805060141c04041c100303000e925001d0180d08407003901600 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 130180971 1250 130179721 130179737
    0x15090106050403141c11011b202401090e03090604090b0f1003150b07020904142a032a15040f09090b28020a050702040e0d020d02010b0901050f01 64
    0x1c00000000e0303980c030041c10b550ba11b840c448202c070646094861004030f0308030801941135401d22483d842420214a1070818920920145040e112146441c65404004c2d6032003070606220345075480d5a201340e504980d603034102400011043d45035240c0700e12845069507449642004200300f100041d0308900c0008800814000d42d03000003034040349041103c0741c2100006139031b8604080303103c5217041c1c010010340080e1a4060034000c0300c0e8041010094050030140c0700a00c510407001074030300100552840c600d0400c0e0390468214400e4a2242c400e08045045442402005110f40001854400d08818100c92001101d04403000c0c80501c1801d150a01080202000801010580410b45c98101c402400c40000c00140c801c17850411001c2450040d1010101038801c00b00071003039640c500c054510320303114400c0040e61120203101c1a11940700340345009420a0038201d001500c207030041801e00150046c1d4087c0d440c40342402d4012401c8500c4422203650003190b210060055080500d54024411018100040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 130182221 1250 130180971 130180993
    0x80a1406061c0204092f07021e090408031602030405130203060d0804080c21061b040b031f06050a090e06130c0c060c050c0703231002070302010b01110c010305061c05061509010605040314 82
    0x18ac45002c9405a5811100005020601165002947c5034104a02c084e600701414400000c140ca4402020820704a40120218003d13a1b01c4008503d4200e17408072181c1d942e9540c0344005501e23032010a000c1407141c00003030381401d00714080001701c800d4025818003400241c0e4603800c2c81002c0010750310950310313924406d11012845180c414000c0d4020000c024228100720007041d40c0504050745600003904000f014005a60080e4001c04000d0650703185000c1c4003010b50700c64021410920700300251040f03090500720352001d242d40000714184044d0180200f881b1040e00700c0c40548843c0300d17014030f03003105500500081000c1440d00c3c040d420804154000210080c094401d05440d00214800340e803c42e13580010f50301d0405809100311656580c0070300707040e83e01018140103243c54818140400d07041c180c8510004407a0b036034002c10483d000c490b0b02d5410347c4a10081c208681c0d640f8049549030386d100401c110141c584d10b0400e46250403591560f0b9070b94034242c1560789810002c11444000d02041c441c41203440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 130183471 1250 130182221 130182229
    0xb1801090302070510020f06040803090a0602071a06010302031306091a091c03050106080106200609030a08010e060d122a0201080a1406061c0204092f07021e 69
    0xe10a18080d41c02401480d04100802440582400303401c01903601c80454121540c2d0b0128000d64426044881d2070b0301ea54500b4030b030505018201100800c05403000651a0405c000184010001341203c120340050303940b5100150224072090320590303840d01100c6841800249a500107007041032160f80c4403040d4560319070250b2107602080e10415955000700c503418114004201c0d41134101d621600c1c0500055141106c0074100260602440c03040000e86204c2c822028110001d40d11084a40400c40c1e015140408000e43c4a82041200900240c001000041c9004807000300501a12009001504109155460f01020440003c00a0070710107159151081c160060302a140da883c03c1c3d0651070320115040c4001804a68003c0c52500c40900d002074070304a02000d0903505070b101d07906580d0256152401d131840c60100d2a9070482060041c00000d02081c1d0302c2c0540c1041c800e082084012044020f04240521380c10207007212070304465103040c03180d00058503240130f1518003501c000390360324250b10715403001c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 130184721 1250 130183471 130183481
    0x30848160308040e0a1803030b030c030d08090c0303070c120312050405030405040c0203121b040b04090e1c0210020d021204050a0b01140a051003020c1e070f0506070b1801 75
    0x584141e6800700341003055a0f10501140d50150265008000c0710070501200c042a1b144104050101562228070001c48e440801107494080c0004044070442c0c0f495100050600c082107902001501030661040c1c0c50341000010b4454469101100f161000d05004100c3c400900000080e020061407011500e00c0d0448de2194500941c08ae00c0956901c0d428402404103480c0085040021075208000448012541901c6560001e000040d8050980c402d0060880c1c18091500030b62480400003070002403280c0b4685c00403030541258415a03819005290500c0709400d603122400016070041c0040041d407081d164010407c103c4140030060800c1e0742400d540c1200030085a04075200e9002c441c1c1d1074280301600c3c04403401000c0169000c3e0320405044e001c0b8100409521641e8020540701c0420401d641c069010741c1c1200803240200c0c1c0900b0742ea0b00a81181c0e0214103001c001c00d02401d240852102000744955094800140032030b817610780705603030b04030712041d0080040d0b41e8080b503400d20010824084c050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 130185971 1250 130184721 130184723
    0x5071403120409091e050c01030b0102011b08100803130e090709020415031103060a0b03040f0b090d080a050708010501050a0207090c1d04060303020a0206030403020c0a0308481603 79
    0x3c2c1c1000516008001e81d4092070900f441c001c1050300c0c0000034400140310300c9142009c2c600410500315240c0140d014043c8000050250200803891081c1d1036403102c01c0c9031050f08160b984004161b81d03554455201d1064807081c1c00d40c102500303024020304600920180d0404143c00171548903580c0c400d06082281c000c0d8000b4200c000c0c5005a40e13074002d5060003800050612600901d11b10306046002aa60000c14841c03c441c0e01800700c00a4240000d40c426800d4094200310003590b145064031905d40c881c00c0107114000841d10281c0810000460742c819240302d520503403203490180e42813000550701c0b60881c00ca460114030503078401044036105400381e22070f40c1c15251146418901c0c500c0c03000065021b80c079001c0d17008030b15192041000c00d40c00a04922804d8050b281a5038944441c00c0403414040c005807400d0b000307941c0b00d02c00000c10800741d00800041032503090780030700c80a981054590010350b41040d400903465010071526007050765200c814401d817041b011500060241804102c3c60725040e44 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 130187221 1250 130185971 130185989
    0xd0c0506040f0e060f0102030301140f0405041110080402030703020105032d0907050d050604021c1a10150e1302090913020301050601080f1b090402030a05180307050714031204 77
    0x88108120b00c0c0340f0404503000603040301d0000c1040c85a400003507807400f0502c0b40108075103038501c9855254481070210101900050070512961a103814141c80d400701808500d4007030034405203059080c520a4a1960146600901622803203185400441d800e4001401d60b1807181141045d028852322030f035041d550b0601b0741d4010088a0b00d014010b050801d10b03e039200600512104030303181c00056020070394036405981200c87c80d142810300c40c00e1811031907021400524011901c11840c1d03810690203141441441d441400411281c1c1310368036411280f50300f624200c0401c1c0c2103038640b000da280c405032103944175040e504c006040485030300008511003c1a08e034800c09100b002402000d6060a00441d544040d007801d105020342030045c1d10000d8108014070002c50620b0b9098890548a00c07078089a0f52402c0c010401e640f44c1c1002c5420701c2c01014240d805800e00c1102a8078100707950008010345101d140c004011703100e2039140c41890180c56039040e40c1d49901d4010003240101201d10a030182c005014084 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 130188471 1250 130187221 130187249
    0x105090409050105040327050402070611030f150607030c0b070e1c020907140d0b030a0b0a020315030f0c0d051507020d03060501091a0d06180c0e0418020d0c050604 72
    0x108014061064010180507110002c03403c400300300c2031f41c400385406c4610030b980040c0d8035501ca041450082005e28a40011280300206000201129901550098100f02610101491800c040041da0310070711000901080990740100e001c156102d40b405d03030182043c00c040c107200100720009800607950781c054100c02218182410b0030f43c1043c0780420b51060b07441c00c10440c11740c030404010302507010706c1a0748078100740c85100812040d00d081c800180d405500294011003814110b200310041d4208031942c43d040030400490295901c2c0002d01d10500c3c2c82c464000e0816550010184180541b10402c2506c40380b094110039403001a070712456920444c0030380d000e0018220700030001410743d42960b00181c10031002810900a1940854007a0052201e808890342d0740c5416040000241145038000c41c0310030b0380c04000420342c045907005840f1110007aa08c1107201c40c80030041108503070700201c2441e4180b0340014100014248501d003106250702a08034042403941e80c80c00640320b0307800780d00000041e101c24 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 130189721 1250 130188471 130188473
    0x30b13050a1a0604050108061215010b03010303020d0306060f18030212030a0810050907030c1b030203040503160e0a020f04080f101b12050c0c1c02070e01080a03030b010509040905010504 82
    0x20301d20181c207039400c55403c1e24107071601d40000c242c03030b0f0050840c034421041031840d0300100008211011768030744c02c01e511250320769690a60040310b4200f40b0064025005503c0c489602078402e103c0c2c0020745100d07440d50300108201e900c084541e4845415441c0352002160344c04000344e80e800d41c858045a000400840e40c50104020040c03d445016049c09500400000e043c011030780c52042503039004100f8940001c00708813121317040341c54850440703a070254210200303402400d041d400303c0100f0a0390300c1901120300750803c11120054403e5030b8070070310b4a084440400304074600700b01d400130700300c424103c0811402c2a44400343c10303082c080fa45282c03a040313a0158030340180400c80b602503414049616170819240f0b0f15032a0300982000041c1900303c0c000f40e40c5400040301306081c2000e80d5910b484000c200c0b4a818008c00e5402100c1c17040e5001200507204096000441c224903100e054142e56012018041280301c0360384c15005020344600c0c180c180310003804004603036180e0307200b440c548500940005c03a4604113 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 130190971 1250 130189721 130189751
    0x50a0803010f050d0b040f06021219061a0f0d0e1006090c090806070c06060b0a08100801051b071518020f0609030c190504090507080d1d01030b13050a 66
    0x1955015a008135081101100850041551213511076080307420a0180082890841d000307225040c04132998400c010140002514005040c02c5030103a48101000110340790f40b612544903041c4540b05444a60400161001080c0f00c00940742500c40c0240119204100103a043c0c1044807116100390f02da50703618401c00c40078055001d003412501c0035080084146090a0b9429140c1000600c0103041c0a07041100c101045481c0d8440801050201d8111b0344401c0c034030b03000901070801554a048104180040401d41e21410320a0300d0203074605905507d00100e00c4011a40c8980180d40300f0b0f1030070041c044140d0000c845038019113040500300307035025808030040d00c10440084441a880380c000e910900c003507140d5460000782c41da4406400c49107800d81c011001c84804011041c0d402054115040c09124802c02500151030019106039805540352558040004c5801042221203060100b00f008075641d059400390b03002c540303641000341000d00d0b881900f076103000c15542e05842480e40160b0b41d9200c81c500d050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 130192221 1250 130190971 130190999
    0x6050d11070317041a07020a1b0608040213020c0105011401030509120409150302031902010206340c0614090c06030603070b031e010321210513050a080301 68
    0x2202916940c1400007a0314024000522800e0305a07a5680b010003003001c0c0220f01c41011040c409484d442d00d030500e00807000a444c0c1c4040c0c00300301c40842e0041d150395070706004155201701f620140e684041c1607a4440e000c0041a2120911504140394204100c0301071000070300802c0d01a103002c0c6030000d540fa01d507000040490703100803c20962504581030201c580107025040303c040b100310140c0416680030042c0522031071250b6a000a6052089960710145030612050351540305000740c081d14030710f54894580031a600080182c4142c0361003030621405900e8034050a400c000304d4245000304101480d0755070b10044400302403403a50001f155000304080f00b0400c00030140c01440c15504030b4110300708074000c0790391240c0c01d025280035a0b03404000100480d0242e501407880722100180040c081d6980e04110142c42480c0041047c00501054460280c03030080c0750102d0b00c08400c2c180c0b00003091b03000300703d84024400a00702da050b210f00c928090011070b80c10069603500d00d000b2114540c0d25451f103640250400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 130193471 1250 130192221 130192241
    0xa050304050a0803031302040f0f02120a1d030327060f150f03031206012304051305060306040201031505060403111201060b0712210902030c030102031003150f0606050d 74
    0x64010002c000e500c018542e1b00708209681070368042805030301d4900d03d00c00342564950b0800881c1c0b01145140e400300f0f0310080c0c603001d8024200100110031074407200040c60040400010003c1d4410408500e0307510010401c039200b2100052a0050a60081e8880342058402d40b2403102d4801c0500500980104200082000143c102e60b10080d60804002180d2030340a45039185241803203034400500c4590148003c01d8a80a007080468400108441c985210380c01c1801041d00071550050360710b825403aa44101402894020005e0100d50307200d50046024011446800c001128480300000d680e44550b400760001e10301c11982840c0a014942c01c1c04401030950901c0c225680c10701c14200071640b9600304450b4400d4210050000b107190002c026100042e240c4034406d8851502107004244a82640c0003020840c804c80075070311004c201c5001c060a03400155044030a0b801c400e481080001c8144141c1c01d40d0003a01c0b000411184905d40d07001c1c04403081da41c841c00101e80c0002d40d005101c0342c58458903c0325 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 130194721 1250 130193471 130193473
    0x80102070506091903050c100c090314010603020d0f020f09070e03060c0301030b011502030f070c052107060e030109020a0e0601080703060f05060d0b03013b031e0c0a050304050a08 79
    0x41c00c05000d480c11303c01c0d21010040c0c180724000544118154040c0b0081081d4810001c040c05400f2510390018045030643c48140d41c17809080701c2070070580c0011b000310001c40b50000d12900d00040a502d48101004100c0001c0ba440f07114020305070008e80b00c5100480c82901c4c90b031102e24020542c0802e0504118006100b446552400c000510018901c55121030542d800070880c103200210407042a0b05d1403040050507a01c0c820701207000c104020a2640d07620a8510540d4002040c02d203c581e44012000c280c3c0011640d030304104000d0140c42d1107048940f500200040020410041a402040c084030540d080a80c1d1000c898040140c00d5030450726554211030303103280820141d854005041700300003150007414030490001030402c1c0507440c5500000b100382c80040003080350102c0007134011804820501840c011443d4002d002680894080c284c400c04c076001c40c040c504d41884d1500004824040420290703070018188100b0020702002c00a080d0824441c0300207681e1903051508024200f4800da010b5905 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 130195971 1250 130194721 130194733
    0x209010309020907180b030c0f090d0807081312020f01030b0307090e030c0c090f040308131b08070504090209040204150b071a0f072010110702120607020307080c03090a08010207050609 81
    0x4948190400c84221300595100c03680c03903642c07000000c0c0016901c1140a0040c607400b003080070038003b031440101440d1440310b0b8035401003940c0d258072411149105101139072082d010048103030359500030340001c00d16000040a540710302d61500c41c3c80f0b084402207510304a95510108000e18144820448000d192030219281c034100c0ca007160310300c501200010301c003d04010030500410301c012881003103c440e150303000007a0b06000030080c107006044480d5100710082407007400c100151504003440b400c8441a000342200c0e2681c0e03140e8080c8005041b05582e401075501c00b6580008000800d1806000343d44c0c4180b50300f8021003c81c0610880d007410240c100205540d1040910904582101c05011180d40d4105000d4103020880340c0b0b0350520400007070310b505060802880d8955060984010208980b08540b546a04040111000e55502045400001503841001044003240d02d12000d040c90407000300c112464450048003043e8288140e0340003a046030740100382041080401e104071a4840d155a00800d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 130197221 1250 130195971 130195981
    0x1020c1b0a15030204120311010b0a0b0d0e03040324060b1215031609090b010f030302061b0d090606091d0705010c03020309030109050c0307080d020601090209010309020907180b03 79
    0xc010041d44200a42103840d1000d500350b9500a8051710b0041403945003503402d07003401742409400010020555403255283c01c08020552900c4c0b960306080c1c4420800140c208985e0840d600014019428000d886200500c80040028010485d14402455041c1c82c0c83e080d520070400c41381034070000d40003460043c3c0c0600400700e8034144a401a9448141d0540c1166519203c00200b410866400b20400046040001c0450f10840c540c00000180e441410000c4050f80ea61031742608800c014000140107070410304c007103085000f020140280d030340d101c051090700e800c8804c3e8000301141c81d1036800300c0b4000d8603030340c042000d064a071240d813241d07207094a000b148003400c140800342c4442440c02160305100102c0d01c20000c1c94800c1095588181c0003400801030881c41c0d01700036907100980302d03008c0c0c403901c00c40f14082610f8401080706069007407640c004113100d9007401c0480019401601c8941d0404d0381d104405c1e805a56a030007414020242070711942103141c81070410289078812600320704000c2c2400c10500c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 130198471 1250 130197221 130197229
    0x3030f08090d0c08212703070b09030f0723010b0112020a0c0f1a060a030506070c17280c02010203030415061a0306130606022a0607030201020c1b 64
    0x3648414a04202c2001c11481c4c142e16a02640108600007148111011104040ca921541c05952050545221401c41c3c20100054031000420600103400500c07070100014581c00080b6000102e50082e6403e200148103205403a030495030342601c0c0c10030054220071180e201c0c10791f44003203a036103c1c009208800714500081c140c011407c0781d5443c010340c00118201c099114001070002903610448520082e1701e41e0a007010303c04d42c0348074000449a4003401180440c9401027402d02243c0c0d100000d030105544550782030398000e07102501074620003d1844080b0300b5100c038000800044079803c01c100c00002020b2401c0ea1142d205c204140103104000c644600580e0b000020761354042d5101250402c00301481c0b100340301800d15980000490040305010341440000071019600c40e0f10152003024000c142c50078040107075001c80c4502d03400760b08802642e0380f96105c03180c600600c641074090b88847c1c0c10400800f0803070a6000300e000740e00503540412504820401400224440c04c500b40302c003001c103c640e400007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 130199721 1250 130198471 130198483
    0x60501090510140c0f060901050a140a05040204090b070c03120501061d04060e04150e03030105010c030c230a170a08060613030804060806090703090b220b0702030403030f0809 77
    0x1401c1c003450030407614250240303200311410300c52040c00f03441041140c1e408446e6580303400c1d0707450900c6500b000c4c000ba10702c407054402c0d5041c015104040201d1520303a0321040d40203220203403080c5e07000381c4c840420b05c011541c1e444009004005607030321002c42545905004090710100c80c40240400d09000040040c107511900b01980318824480000d208119207001500408a5070f0041d40b42c40e91007001c00041c400050100445450818002d11151851501c500e44a100c24080c86001c0f801c0c145050001c05d1041448002080c800c13002642c11600300104444d030b4510f55441584182c0c4071140c2001008005242010b4100210580d03a0034411001d00c00b4044010007000c26014580108094485000b658120350007190000072880e135840c0c842100401e074000461f0464007600440000c54480d521900c14081750710b400c204650710603103a88051454010b580d001c00c0c8016042d42001c4000315a407901c016005a180d03400640d40d40340f07540781c0a0400981c0890000c1440341442c100300c00940c000c40e075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 130200971 1250 130199721 130199749
    0xa032706180804140a0513020c070801060501020d03050c210702010b030a051203060a0b0f03010311060a0806060c0f060c0d0e060c040306050414010e0703031227050109020613090605010905 83
    0xc00340108182d40400c071117504650016910044248001925501540c010f080000c0310304180d0303031302984540b040340c00e0315203070310a07640180c0c0075008561b5845e1180d44910342080e000b000c0549004158891070070040c4c0f9901c640da501c070301800244031855409100c3c00d01051070a4002c0c002111690719071603260420326254903801880040010720594411420394041c0103204007242d254a580844030855030824041120344159a0008d40018540b040030340c0c008920955400c4101d640700c1c420321549030003500120103c1d115039164912819028419a8030400314000d1a0741c4030300c404030441c025205126490411600484140441d1848200c00c48050b02d821510109480d15079152400a81104012000e115480c005664101c100003081c2d880032079010342e0b40d06540d82d40f00c4e021042280e03017103007000e40c02c2c07540740d10040ca480e0707840d01032075484901900c0000b40c000050340228203d0703409007401c3d1060f408082c0b0103100e8441580300e1040034140a01c0d00c031100c9400c04010440c0b182c40241 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 130202221 1250 130200971 130200989
    0x7061a0a231807080103051504080d0e10090501050a0f18110303070606030b1602120a030905030d0501030309032d020906041b0f021209010e060a032706180804 70
    0x214025050300c40d142d0500b00000750001801003450140d40c000c0110a0078041212940100080c080051900010103030040350040e05003490031255041c0b090050010718044003050183d0281940c0b4042684200c031050740c06400007042514041c80f65000b203440b00020307058420300c2c0c0844960480d0b074404c0d07000c8040c6e510541000091240000203881c600907110014a81c90500341e0100030089002c5815000e107900e02d130b003030b03d408460180c1a40c48403581e01c10707040c40c558144501c4010030f21a0f0444403040d4003442c00e40340b0303100c28802a6002c2c0c070400d8005801103a91000c0410421032805006801c6400c803804070154003010056146110355a4000a482442c820011400c150b6583e40400e00034041c1d480d25400714016001c003e0b083c3c02401141e5005405128103811040d90070000311032030032a050b90f41125050005003008000d8011134103210030150f8455010900f5811038a215842d0340c0c2c02426400d81030300714075041041d0b404c2c03107100880c003c0500500b080041c4010058074150b45081e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 130203471 1250 130202221 130202279
    0x1030b03070b040b0703030b041d06090715050d060f260610050405060423221a100806070302090a060c0c091e020d09020906150d020a050403020607061a0a 68
    0x400c0440180234283e044650262a0104100324050305200300d00c00c400040c0141c4405640c1c6152051300c0349003c0c880c082c500031245100b031011a21031001401030701d10100c00000c05544802448c003445d0400e80109444c1c6140c02c4000c214054154845590b1212040050440746070640201015040c240f18140c00380da01c902c01b281c0786650b6508010548132040c02d030203043c1c0c41700c24220921800e055030302d45881c801099001129400440704540010b820841d0851261422907590590b2800181404440c0c4250800070411420921603030380a41e6040d54003503101d40403001001980700d040d40c4010184402c098807000060103c003250003c60305545000141d84503200c24000444a00c080346180ac10b00c00500e403c20794070f1542c440c0024600a42d0000541d42e5444140101d000303c00340d021148100a200144021400703800510581440d86011418659a40e0101e00d16400003d02290640e86800700c1000109500c0c00801003a0400c40704200350520f04070a000e8191240416068816401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 130204721 1250 130203471 130203473
    0x6032a060a090b0a120b040b0d08130f060f09090c081f05061c050a0b0102060c0304230607120209100e03070f0b0a020105070c020a0509041410020901030b03070b040b07 74
    0x20b800d0003801810841e114680c0c4040c0d01800409603503102c0114180b1501e44540e1183e00e0a052041c1090380101808140c620003ca48505050f50004002288102d002d004081810300c1d00c42c0d0070384000d2895880f036803440c01c0007038005000b0404603000f20001920308604007200329801501c041c0c00c8598440e0606080c5843d041401d01d88203070342c0040703070405030000f94030000b81802c00700e41022581040b41004240c503078480d0309003910141c005660051b03003d01e01090442144800958006208031801031948031491400890002440c0b68610301d0340080041148141d0090700c0c51003d10081d4104515202c104c4000906a00c658118034041200c105003420054400b00100c101030034600b480c0c40031090340d80721410080c1c2d01030708119005500b08004240058010328034a041941c3c01040b5898003401c0006001007490020004e4075510466030344081e9100051200800824548d5805680c9084d250005404c0d9404c0c0c141080c00390340100780400803502d03800141c400f56a128900c080c2e0784c83c21 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 130205971 1250 130204721 130204727
    0x5010e010309060c0f0e100203041710050106050a030e060610120b09040f0312060605070b061c030306081501080601170703060e0709060504050f010e06031009050606032a060a 77
    0x2c2500090645140004503010141c200d00d049407009100c0d0346502141804c04144000305003481207940241c0d0090209104019803d0300d000a45495602101e81001014141c5019200d0a134031810129800083c41c101039a8140240c0987d4a090700c0140094104500896400311820070000c04125050002c2c00d040710454216943d07003035004000c2520390a003401c1c1502d00000040044011a0b51103524128044580c0078038002c54040381c603500d0030f107007698440030b003601001070210754040340324a00c515100c00c44140c00702c0307013602030b030740000e2958140f508043c0381030240840c060a00045000403c02030200041c214191140440c1d2407810070b0801482c6850290550030040246040c9480350f1032892000408400b10744080c2c10600107a96108203100441d00b080c0d80c48141c120005005212403400c10306001d80042025044076494070050350060215603030414102c0c2c8680003c400d1102510f0f04008801084481e400341152405906080da170030400300180c41030180d440400d2450103140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 130207221 1250 130205971 130205981
    0x1201060504050414012007030c060b0904030e040b0604050d0f0609050d031b05070503070303050702070b13172404020a09060603020c0d110a02010c060207050304060c050c030d0905010e0103 83
    0x30140041c00a400c080c41c0c100002c8984030302c900c42c3d80d0310700400034288025004400b070051070758034607152601a05441c116150302112505a0b0146c1e103449043c02c0d1911a400c40034070840c0079980b44030400c18032004100a49241400c114401da400b4801484103031385400000f80801e80c40040c182c4003545902c1e100c0c010b00500b2802038480e000c0d00d440256040e8254200d01c132051410070b15000509880350341542c05000b03202c00606140d000303101c24400a8065401550001e90a00444550030390714a804001a48485598100c01541d50f0080006c00010210b140e40d014421016001705504805135080ca014441000007180001c8000b28045d5124804048080d112104050114980740e04000e40650f100d0042d50004d0301ca40d15407090301c02d00c0b41c2814001c032a00034000d0300001d48181c0046601d441121000c3d80c00640c00c208110000c1e10420080008003016100d000c0d021500c1d09106040c01072140e05907010341c00104000700800e40c4005141c0c241e40c23003402c104100c840b0300801280100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 130208471 1250 130207221 130207229
    0x21305060307020d02010f050121150e0a02090c030f04020d0614040b010314070501050d020a03060f1d0705040b2a07090b0a05030106030c120302030c01020f031b12010302120106 78
    0x1510001c14440015400300301c4188140541c1c00901c51304000321000070486900f403082c0ca51400000105480e000c061002001c2c145003d00318080101410780905000c44910090302084c46c0d01019507401142070500380164002c2121321154210715203a904102c14400c020002440713030b80101107200820801d64000410500c0c00c1c038121003146000c1c0f40103543d8040a0002b5146551203a41e00441003100081c14016103030107965141c1800c100c1d0032080301030740000c66464145500c504d07000c1010304403003045000414400785a000711407900e01c2c0000044101038180e200f002030800050148941c03810803210490340f1010f491003c1650700c0d034410071005c00b10500c1e081c0d0307002c2d010780060076140070303084100410f90440303910310b01c0c0d5696070416003242c40c240710003068113048500800c0f5a00382024984030003070081c0182c80c034027443d0725182822030f4029084240d00c15008001c0c002e00300c03e12000340b2603201c1590310541c03804548403042c440034001480021300c40d81400314490300140c0d00390003460040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 130209721 1250 130208471 130208479
    0xc0f060d0903031d061608090a0203100603030e010503011401080402010c06090605060108070e0d14070b030f0a060b040602030715020f04060503010e0708061c02152205010806060409021305 83
    0x8074652034002d001d0251508280c5007501c06100600ca482c0c0e0203e0501d0003640d80b5044030b880040f52103810b58004400038440b40c7c01380204603851000d038070180b044a6805c1407240d0700013440703410352a000d03180d2007e50400d14108001030006000d01604a4562004030360309003007011040d503962004130313410041848010710b0340e400c1c1681e003000c10807290006070280a098840040036a43c1810441c0c080b03030181c0a180c1d00c010300d40da010012440c170112039150b13aa010001d440b156500e428004078a03600035104800000e00c41410041404142d00c680f201800f600b14903c0d24151800400239642c0c0203407a80505954202500b074542d0b51a10341c112400903046100c00c0d500d5556881001e400c941003441002e030700c030a103a000900d079903100e18005031003a00d0007010000745d100141c0794210ba0441d90b050890708480389030220400b140a0714050120310b907403a203c2c02c0480c400d06a51120a890b543d2186040c0090300040c01307040da4800003581c1c150342040c0703c0140c449114003242110710610390f00c05500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 130210971 1250 130209721 130209731
    0x120c15060602010c0e010311040e101a04150918020a0903050f010212100518041704030f14010c02070605070201050f04060302070b1602120913051006110304080c0f060d 74
    0xc0e0b601908600340300315054440c1100c00100c80010b6081d40c1c1c05442c2e4040d0f54404100c24006000c0085003142c002011090301040d084c1c4031564144500d8411003040300012000c682000b041c100014030044480540c544414a945000440b00b0003d00049441c1495900420101e10041c411601c44008580080c1101c0305030a00306e803030318001c2d4820500c1e600080640300000d40c2102c4005c2400c001c543c0043d08040003841100486260208080d104030742078480c50010b914a03000320b42c00b0b88055809400d81e00911049450b0010b40351b07240143e40c110b02d904215103414420b402188010440c0c41c50b04105650380340a100403074041c8070300242541000070125002c03403015410785c0030741066032059400c00c0c00d5072200004410320340808410840184d114041d880d44c0250300030041c20b03c458010309481d00c0c6490b0703103803550300f81c1700100da001c0741c00454521308011107540001d00d4042001010040c510f040d0400a800340c5804a55000034054a0a1403c1c15040c2e21a8411100b42031034020342040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 130212221 1250 130210971 130210979
    0x2030a0c1a011e0902031006030c051b0102040e01080a02030a032f01020d230c070204020c100b011404060801120c0e090c01090b030601080402150912030d0e010504120c1506 76
    0x1140d850240c5a40420740c40f6044082070300079a038803ca80c003880385078510185842c6050011806031000c17800304000c2203400d104402c4595500000480c0300b42e0b42c8000942c8070380c24070841f45e07002101680301c0e4001d980894101c60160f14041042031030f498061030300504c2189482c2c85620b00c0c180c580c80e10803004140d8140b1160810040d4068582502491380510188003081140740604454420580d09880b81002040118060b10300402d8818809000135050070002a040340c02c2c40381340d00f00403d61640b07034100e2503130641e404140442d0a041386200d19041c40e052070740c010a514014000c0502c0f4002901c0d04400340b2400070030190050600c008440607a29144209d40d0311220703d041d00c9400b09607110401f2030400c1113131065a00c1444181e4440c241d603034480d0200070002000b05a038080390107040040800c6619212400b540a00c500d40c000c5507240040c050440855a413a99010708692404003804000b41c202ca5024a400684c0d00d400d0000340000e0600b03a000c5118804000c200c2071030108006 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 130213471 1250 130212221 130212239
    0xa020304030c05091b0a0210020c10050a0203010f0b0f0f04060c0c090c080f04020a03060609060501080c030103020102060403051c06030c09051b0a0302130e040f0c0f0602030a0c1a01 80
    0x5aa101e8000e02c036090742d480d41032204048042c0c902c4401c1c55035180c2c1c103604401d850409001c00201c00c3c811034040d2041018070f02c04a81c0000200c1c0325540040300102c42460890041c0b6030003200300c4000310f140d5894080100ba809003a030180752800d480010301c00210841040540b40c030740d42180ba449030f99540d90b0300054031175006020100c508201414000440024038030170211440050340743d0400c0e5540340d0742c00d240035040080c01217074000c0a215000c00401c43c05c0c4511005880c2c8c508002442034108000903151010040801c903100710100010300050b64041412500641d26090080d241c1842a40c1c00034801242d1101c943c403540303001c100000b4041500100d170b00b128001c00c01000283c5420800307c508503008905542803540c0bc105c50f4814501ca40e00902c07031150482c040100882c4ca80a041c10b12141c1a14103039000000f00001c40140055000d1103402000c40c41c12198010f40b070040302039281d010305c0442c0320910103414070080c184200d0140c1c0d440340114070071415000b903840f01c07280 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 130214721 1250 130213471 130213477
    0x11e2102030711011b0c02011e03060807050301061401030b0a0b070503040303080f090607050a0c0501060b07140d090612021b060702060615030c030c0f07080409181104050604020903030a0203 84
    0x44000440c040240b2400102c10f1240081d00817818203105c4200b00310100a850a81080c00120304104000e00c0c3d005850380041641c60000c102544c000c1125482c02d5403580c81c1c010b42d9000390f8466454114104121948038001c521307984400c1c00d01141e540102400500c3c04aa00da00040e8041d0000509104101000c070040064902c03d8840591644609400c0a10243d0407650f081044d400300002c2184240101c01500071110359140149448036240e0726517083d2510f5502445090380040b400504020022014065411041c4010080301007010002010805184101c600788a00c12489a241a070207030111020144110118165052211190f0342c1c2c45404a0320407006000c0d00b40424094a0810008807290794140c402d01e0942d15142000c0c48958005803509003c1c1e54200000c00d0391181400c060f00031360b400b4083e065285c030310301810034045e0381c00691300c0f085041c4110000000034145040d507208220382502c000503d6a50500414001c1c8141001c0c039034984408a904003c1c141d0000003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 130215827 1106 130214721 130214731
    0xd060f020c0106090b030607050f0a051c050c0306040e0c0114090409020405090f100b010c0f0c08030f041e03050c0d1e120e010806011e210203 63
    0x1000d0300312090340d4048130615844202c1c90000b0701d82840f246a00c4240c0d4185580380120703026080071544038940c02082480400703d0100d0118040c0341c10006000514441000103040004001c0003d40046491600c0746090507942012800c0c0461241119501a100c0051545034031405400a4020ba00441d400564810200c40503a81d81d0180c903008603610b0000d400901e03240c0700d01504208008a282c40d040e42480322442c110790b800750600d00540d0308903c035861032003030f50f242c099210f000300d6005a078680310104252202070440780c001c10444000c01e500a28014040019442c0d1110901c00130b4031640080e008445603080c9a144003000c0c2e40b00f032001140040b2035a071010066030740300e4001c1d5030300640c010800c0101608048200316066007400c0c111064901000028501c0001c410780b543c110b030655000d810400e0103081801445885901c1b030014001602c1009030003500101c0b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 130035971 130215827 := by
  have h0 := BRFrame.cov_init 130035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 130035971 ≤ n) (h2 : n < 130215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
