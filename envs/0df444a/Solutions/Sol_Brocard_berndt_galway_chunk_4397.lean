-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4397
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:29:09.950429+00:00
-- url     : https://prove2.me/submissions/9b922f6b-9a24-4e79-8869-32eef83eddc1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 790647482 ≤ n < 790827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 790648732 1250 790647482 790647511
    0x1030e010618111e071a01090501030506060d0b13050c0a0e0907080d2019060606110f030409050907120516090b090703050741030121061112 62
    0xc203581007003100d04c0032115024840c2c1103042c0d802801c00340d40c40300300c0441d01c4038040101121071a0717a11803124000c00303251074001303400d62450800b82c1c2000c40080180344140408103101001400036000035400400405a0b003107134241500c3c06500c1c100710a030f40d40390f020741441340000b04140d000c021a8403c0c050381064844181c1d0ba038507219503400d041d4940358007040542c2d950100040181868040070341000003141e038400d080ea4074005543c01450f1003a02c103151141414411503030440030203160a000c000091215844440b240303900d0340513a01a80c0030054881c8045607841d4410860310018000d41030084a054070300f4a80781e60f944505040c082a900c031598800526402c4d0351140b41600b0f8009072800f00380d650b4003841203004007401000c00c020b000d8200c8130030740424649042c1c050001c1030990f9402501100005034401d0b0302c01141c00254040082006010401644c544401440c0854848078480c0e503040c605030000c0c0002d0300020000000104051006052405100740034243c030004165 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 790649982 1250 790648732 790648751
    0x233040602090414091c1e0905090106050a0c0b0402030304180b010e101d030f01021204061103010803070303110f1602090f011a07050f0a0305040f0902030f010902070201030e010618 80
    0xc0b241c0e10f0417210301c40ea0741c10030302d81d0322050800d10303280d048080b0603840e00c950800c0b04801c0c0b0131085940b2010300c500082030b00c3c00500190074941d0100d030140c25542006400c042c81d04000a21411502500030845810140070070b045450400030780c1d02604100342040541404004548020502d1042580c0051021107030140e15007409409098003042d26519800030440818548040c00b00202009801d4884c00c408409820070070300c042d00300718840d11035000075410f103810003c0c1075400800b46584840b03400c0004008468000040710140707685414041990480708030f5502c402d014601d40d0400010b03000403442e00b4240b0119010074440e00c03c680d81c140c1034031003042803c08407200b409944d070381c1c1c0f0104130b900c038080c04c50034080c042540c800d008a031080381c102c5c6c0310982070a10008045011650101c2d051020213030754034116018000461045082d071801d40380d581035000e01842801c0085a0020752a800d40e4803d4200c68261020800280405565187c80080040c1401c00f4420810b140a0052 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 790651232 1250 790649982 790650011
    0x506150d1506210c0507110a0f06051308030a090e0408070c12021002063616081207051005060111062406040302090403050c0a140304060f02060702330406020904 71
    0x4030704d0040d05540d1503007800070790398030620362411881a241d4001815040045c00000e000f21100103005035a0300c0c9a01d40a003070556045140e06900140d160390020711251003101c1d8400312003411034140c081c0d80320854a8605180109100d8a10042c0c4070700700b031100100344101004000b0505610982c0c8900540030242c40413a11540c05543e02c12150a0003102c3c0c0544c504c409551040c002401c50380c3d015030030201559149808021540c0340c1c02051580f9041158036414008140f200e194295110b00c1e08803030b940e61584411040c101c0c00400d544e0340000c14503691107a1103c6120302018402ca0f211402c1071094407215149540030300c00e0f60003180048041c641000030a480c1100c0d0b02902c114080d855a0360191481d8003c0c45111900c0e100b680e45c1d9401103001034000b0180d402c0e0b5003001c1c6035154200400101020718002100056501003014000071650020704800e40040c00107013140507070002c10817a0f00040c3c1c150204201c41145905201c00d1003007503802090700350411501040003041e01e8452 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 790652482 1250 790651232 790651241
    0xc0f0d02010e0405060102100905010f050c1c020313120831081608070c0e010b040b1207051306080618010303020709020a1e210506150d150621 63
    0x90010b102c0b640342c80031900341a044613401035014010f4031102420325448408440c081e0500741d4242c0c0d100e1361110079501c80c501c141034010f500c2e1441a4034004001441c1802102c1c62030100721090350000004581121030300740e1004079a4000410307140c1c40e6521784020086d40083e103c031541d00300c0c40b00169440c6d4040b800004981d02c952150610006440e8550f440b032500180e82d145041c52903210040001001070000f005040e10503008441d039641030010514014805800244100c0010002800101089000d80d05e41c002c00c05400c0d000e03039407015012030315406940421222202c40103008039241c0c4c2c00c10f0300d0a100e01000d440700c02d603e00c94070146c0e03842c4032402c3c80081c0150b04407610500c009816500140300d854860300f000602c0c0e56090030485008139000c40325900280780201648052000422842040580030800b070046041050010f000d10740c60100c01049070100003800782c60031805802c440020403851680288250303031010041d012a42e0880d000c0104003a041411558000f607116 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 790653732 1250 790652482 790652509
    0xc0806060109030b04020307091e05010501080f010909050c03120d1a0907081f0e0a23062e0305100603150303050711030f0d0f0801081c12020403050c0f 67
    0x1205010b940c41c42c0c81c0c01c403407190302620036a018001c44001148031802c900650680103030400d81021040b103241c00d0441200d9041e040306040003034140c00e0111041c90060750034150b400840e400124015640b411f07501e0701e41d000c01650780500840c46000e111010b4880038101007181c120003840302d042c5640140c00140120000c10384e21a20b484003188410344281905c1d540706940740260840e000c0700558140b14021135074003c2c050310900c401003140040c240e00600c00d40c2d0003000d101c407141001e5410b41c4980d0302e4000300400d00400360a90008280508086102e00301c800c0c0311181c42500d82c1038a0001d01074801241c503402c0c520685072002a01074880d2191540b080584007441c00703818256501280c0742e074840c04054401801c02c04000c41590350501403414a291108024000040c1d442009454422008810000c2c480303008010001c1c914082048114040e503100c040800c102e6210054845001003582550950b10114001c01045800500342c402407904944003a020402032080268a144611 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 790654982 1250 790653732 790653737
    0x1b0c0b04080a0903051002132301050c0a0602030114100212160f140a0c0b1e030a02070516050102011401120213061206020702130501031707021f0503040c08060601 72
    0x40016021031541009824002000c3c508251207079a01e1320381a14001e000810441615400100c7c401a4904007220344010f103c200b0072460031a034803002a60318510206009810300c8000100d881440c8000e0240b042c405901903c21034580d41c4920000c59034104010b10307907010340c11a403042d403021400090a0000440c0c80701c0d41c0c0b4079040360240e1800040341c00280440b030b14406c0c10034160009a0400034610340503010700c020014109642000e48030880254000c0100d504200040440c05e140c1c1040300c0c140c5c04001c40c050b0f0750781d11003659510003441883c0c4081c0c480e014004d40c0c3c0420145801c208130845000364001d1006401c44195580c030107000f8810140c080c640511041e0050510a50300104010241000180c079680c90145c001128580030084810750350008005085141182c11400e4011420f0300c07c000725811955202000040105800c11418000c00c0650440d0394a055588503100b55506003000d0303603d4081c02510540064a00326000300342d003071021a5544000807114440d9805a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 790656232 1250 790654982 790655003
    0x50c0d05030d0e150a1e060b2706121003080406050a0206060102031201120f050601060306031a010510110102091c05010c0c020307051908030f09090a1a04020315131b0c 74
    0x480e0000050040f0040003011405043c08810046c02610a803030083c2280c604003950b480500c070200e603c20103c00356510320440407003c034558944848040d035503030142040c9180b0441d00c1d00032401d000c1405a5000411282000030040380b2540d000c130140807803061540894600344c4580d00166241e00a00c1030351582004000010000c2c0c038bda0000c0e01040d1800380701e038484540b4582e02e455044c028240c00c403001082d1505000c02c108000107188003080455811403000035410702c800140d620105002c041c3c1080310703088401d000d465084d4115166110300501004080c02a4012075980d00c090340d0040e9869440c180c0344140d41c0d0b0050404640303255005010300b2034203081908000041c403104102e803240506400010490328800c0000b052500644000c050300ca50b01c210400c8448013000b8441031b08942441e076400030106043c6030920a003041194003503229078400242d401161451901d240e4000c1e11840401d40300c0c486c59108080d03415107014810140140c0400c01d656413041c190006241d02d541 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 790657482 1250 790656232 790656241
    0x4050a09091e03031407080712020c1b060c0a03021b0f09061003060542030106030c030e030d0b030d050c10090512030c030106030b0a03021804050c0d05030d0e15 71
    0x102c0c08280e02c80c0c1c0c42410f000810340f4080d411929807803022141c0501140300d003c20320511682119900c000703040150030079850868001c10035925004070031200c0c410314011030618005076461100381c40c1144240b40840e007010b28203044c000c1d615000d0800040041d002c081980307209081c0340e500d61600c000050486001d589980f824404681000c800013010150b0350031021035160fa4038612451140c01540890180d5020f0101822140c0000a280001100c1149000b85490006016241145c02d281800100c8840807034044c0c019140106510181d40800210701c58402c2850f07000502d031103016011551031a10310b02042c1d620744580d54a18500360320202e41ca0300c0d800d071f4a41154285c0307072141081d00c410740b90a0800c00f504c0d400c00d4860301c0c803500012005000c001e6052007020f4402c0000c46081049500d550045240741030581c5940080201c1c040024041c86020407070303004d00c40c00c0a001c0c0307018103840d401d155403640c0109560010040c20000183c1007800000307101e8508050201c44100103444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 790658732 1250 790657482 790657523
    0x30305120a06080304030609110a1a0a1206170d0806030307200306070804031106070905091e090a1106130b0d060e040b010302090f010b2b0207050304050a0909 70
    0x3000705030503120354807200041100c0030140050070043d881104d0100d640d850601d042d809919810f81d6190044124000401080d8154028190020030805106070fa80c84140c9040769200400d0b042e0086150a11000107842d4052522850760b011112041d91909903203100200c8211030159110740e0305174428401e03a17012500d20010469102e102604c0c482d0b10181c0c81010071305002c0c08440f160b01080720303c1d0402051540104030099070b0107040001e84482d2510141c041d02e5a4003601466004440b41c4000503010512803c80c403400144203002400245050301c0380315554255283e04850108102c0702c0c02c0c00307a0401201361112a1a440141b80c0340a0814505070041c0d0042250011110b484450000341c031583c40f144e850142d8066102c4202039030640c01400b4a500c809040c400c9601d445c08010064001c00c80d05840d000c0d1042c466041c0742c0748620740500e81900d90f8058082100d07200091280411000200a008440d400e035132507400c55540f030038490101c40c0b401101420780404400341c00031008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 790659982 1250 790658732 790658767
    0x8060a092a0905040609020a0f0e01060e0f0a0f05011205010b0714120703120605090906070e01110616030b10020d050f04090e0c03010b041107260a0503011509030305 73
    0x7454403034001c601c40c1e40345034000641c0d1080c1c0c0c098614036aa4030781a41542410011000a0b010080d010703c841842d05e4803401c240030701442100c0c01c001c1ca4510b00006640c0e058038003d072402001300800303941510340380300c014007903154885c0c1c0340860b00325402449c0d0031083c0d014082c121100a12118207101c140d440c0c49030301c0aa40050500b0038022409040500050314000c2c1103400d0081e82c4400024500c481000201d07021500400d1150080e2020004100400110a54003411508d015200e18020320b0043e20440d090f5690300c00e56002e0041003084c072518030140c0b108000403070b6130140000100501400350040c0100910707401600042c55015595024200510004040e000d106240566400300d11045030000319508803d03403c100d018500c070f450300340521105030404a03000c10542040f07880c0d03502c8a2003000c0006010400b0343c03041040880c20540a001000018180c09540302c144003c0282194024060078905035280000b00f60802d115071a01e109aa6143d200d803481d042130005082c2080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 790661232 1250 790659982 790660043
    0x813020a0b040f09060e060f131d032d221a0c0d0305130b0a09020603090708070b040501051c0b0a1710020304020901120f02100908060a09 61
    0x55440004074112080002c10041001c026030310511420800300b9002e40721079501042c88031020794140030b01c5584100455916190440f0380d081607955442101c809030484401c945c1e100c005c5000c01e0b0400180200c020800d84540c9030900701c001803080520701d0000340d400d81c180550f10702884540c2d12101c0700c0740c00a509445801d01c8400090340c43e01d51003050041c1410014a15001140364100c0710b13000c12410107081040d08041c050307464442d0301c451105d08649009401e404044011603824016544049482a005002c81d0341d00d280031007da03541c404052281c00c04d2446080800aa03049002090303400b0740398165600303450100342e001045100204a0700f003018807030340d0300302203d0140d5441c42050001c02d01501e0341203503030085036095401c0407080712540c2051030042007004010b1784c81c80d41280c15904807840010f102007460030100f03445400c0e140004c0d000488900081a00c2c1e41114030102100d20410440d034107030f6075004001d0b085c4ca91051005140c050361034050640201c03d401c011044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 790662482 1250 790661232 790661239
    0x13021315020a05070312021b220f050a05090d050423011b051c050702030703020d03140403050c0909030711211c02190507061823030105090a03081302 66
    0x803070416241c9038213243c081e43c011030f03c030000032401d419516010300c560096034502c40200d88503102e41034046003031500142003266251601010074100900a50300c03400300181c18000400240c6001c10400000b45000d07241a4110720030034046800c0340748900202e800341c44c46001d034a00700804241060000c12565003040e418422580300300d03c2204210035000303807003502400080074400c40ca8190400f40c7ca4000c220700d41013000800a210140e18000fa42d241265410790303a420100c0340720304040300e140d1030090241c158014000380010078024001802888000c00316440880c0782c44801c0702c281e41e40b10f145002001e110542e0713081c2440303140c01c00c01380d030305410742c004034001c1c958000d8101030034607108441051720404298003015410f03504000c0107031810b405400120701d840f02c0d620798036551801d901c00d0000700442c5148170b103140c1780d506c04002e0052491205c680c2d01e125880c0105034441d62507100e1103002e5071800c6d0014101d041c001404000203a01512000401c1e240c4080040d9001c0603418203980 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 790663732 1250 790662482 790662493
    0x8040f0f0609021e01020715110f0102090901050108150904171c14250c080406080411011e1b0b0f180a3503151302131502 54
    0x300d030444644411503481101c00085056491040001040014142d80c1c06501810b06203481a40c0005840d07096074503400104030038180345201113410b50000704e0b00d00c0349401800106980540c054000d01000401122503000c140c2c0ca030700045808100884004140c0c808044003510b050404c1e65105821a001d41e58540040a09401d60060b84d030010b0382e01a00302045100b242141403003407080360740000e4140c9528440f0b00b003107110002c40c03200d054120100221102030f007008540c0950717100c9590b9941f01c1d00d40c0b034442d40c0c1d507500074015000032101902e544890721102c6581790700c0341881c071110000003010180020342d1903070102c1d128680e01d007042071450144c69288010a0605080700d115540e1007045050601d40207441e12803580c0300613940d0002d0307030002c00b24000103903000071030000002c144c1d2122023a2144540e80c4107414205a804403034200000000e00c03165289903000c0a440c80707801e5408507018040811030208034410380c45104410101204148620071008000300300c2c6100d240304884 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 790664982 1250 790663732 790663763
    0xb0909130c050a0b040512060903071e050a0b0a0507030606091a070204050109090c12030206010501030b1c06020c0d05070c1208040f0902070314090907050c03120a0b0f030f070302010804 82
    0x6883c0000c603004000800400300d0b0802291512620321000503803800090035039810010141030340ca016150b002031140d00829002003041c006011980401138011048446980140c20042c4650f4025074481c21400e04090008251038001d004940882d0129a00e04074114035001280c40c17103411441041100300420022400940d0756030003601d001c2c00b680e02c800114014540b80c05009c0c005103030720004003a0032103d18000071035004110241190001e08002c10040c102c003000420850b00006144401c00441c50b411051194a9003c2c0020103840011107404061001003a10315014002d0b006014800c4880b042c420701520030304401407039110300b04485c20281c0392850441940040c1d005014100c0d0f020640030240b55000c03030742c44004462801035601d0080003402203211b01c200205140300780072000400540d4030500300300300e8242c9004682e0780300740c0c0d0914060103405411100d620f24854105220042030529010490400035003842c401001051b10711380c01503a020100131300944266020480d0107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 790666232 1250 790664982 790664989
    0x5040602181020250501020c1014031b0c0c010e0f1516080705030903010c0e0607060b0f03100b1824010909180b161b081b0708070b0909130c05 63
    0x5040c00b000c0002d03a010300c5c18038000a141c410181940b80c40340044070704000189811140e560402c0c000d402c1043d95aa0301d10450b0a19048003902c0d45441e1140001d903290080401718841c0b040f400240d9686501400da01c04121040c440c001c02d069101503290160610445c0803002411072110315004035405031020388902115400400d41522a6000082c5c0c917803803132a00384030b50306001c03409061804a000c12030b00481c02c0d5000b180340041480d40c0e21180a80942c1c1c5004108000200c01011244091074203240c100140000040d018001d83d852040c0c1004201940c030308510403400c5c0c110281c0301c081e112007620350f1803800000490600c41c102001189204080c050002441d00914061080c0c1d0360714545004102d0b4000c000461200d52007900c8010203611012070300103402031110901020040b405e080d0312600c59032010008000d03040f1004034000f88042205405c0b20110030554400d10758942074074620380704201c1c025500502c2100050300e6103d000b2440b0030818020300810a5054480010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 790667482 1250 790666232 790666273
    0x30907050a06020706171306050712020d0c02010501170c0910050402030403030606110d08070f03151202030f070f030803190c0806030f0714061c05040602181020 71
    0x80b1005070410f010902005070424003444c3c1100c8210155800791030020400e0340d40c5003035440000c291503155408194180d00c07814442c035101c00004811035650001c040d4160040c002c0010b401c0c09035007040c0000807440c45040100c25a200141c015101400d102001c1001103400109600710300e405074040883c050725180b015520840c425200014a5414035402920105c4c00c8101d504d1903034000109220b003942c3c80244103800c0b40850501c8003451300303d07000a0700a4005c1d90f00314810b01c510480000b07a014041c00d0794544140c0242e0544110701d01296200e40c803030b540ca0250310203014045038104005881c2c4401151301c06c00000001c2180040c00c0444400e41d1011603410000903c08020300c041490140002691b100300c1c14010607005280004040c40405208a0749101d000c0c049542180c2c0601c841c09411440f5200d0020001c038035152404030001c3d0888403460f1250414009a00c140342050742c2140d51500150b12080f00f80300c904079284a0b141c40312903141c20240564804400642c0001741d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 790668732 1250 790667482 790667489
    0x7170319050f1e040c0902030702070801151a0711100e09150108010801020a08060607030c080307030618060303230904180512041203030c21090b011502030f030907050a 74
    0x10000103403c2104203003039807403503e069100c1407103255410f0000280c4416140d1086921900003d0789070354540005030708000b19a44068915400d203020000020401d41d500c0d000d40d1061419039011000001400d1800e010304400100140c041051140c0e070f900c0e00b9450451314030600e00d8144414143c1e80f01140d001030702070341e10f44100b0004c80c008010075078011080a02521000000b1401d04044050051641c0400340032540a0300d40000c0203020325105044008080c1e8000c000349540e070414983c000c00902d02880b031200c0440d06c56030145072500c2e5038010030044035059650307000c140e012501c098001805003c1500e0344e045003006403015603140c5004002c005000c01e00d18060032100c0341401400d082d11202d10461548041009001d9100f103681d441603683c2e05440c000902d403d050500f600d081c1942c070300841c000d4403040d80851041800703412140507148141c400840903660b4409141c1e035054880902000b40e00240b246908444004000d95800301d40c0108131142180d0398408a03407161010780 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 790669982 1250 790668732 790668751
    0x20f0706020f010c180e430f0c02120a0b0405030316020c1302091207060e090907080604031404031e120915030207020a09020703082203201527030717031905 69
    0x5964100747c0c1e41c544001e1209124103050794040304045004002d41550600244181c6041159011496042261480c11035202030020b03030070700789800c0450f92500100d81501c0840d00c2c5032015001c1e54070124007010180c102400301800a40c1a400302c1029410030110560030408445080809000400400740100050b850f0424075415001c284110140700900700404c603400840308012510000806a1340203405240054642062542000407842164400b4000288001c411600c1c1320002e0300c2460b10b28421140044440001c2c5819200c0300050710a8254041210340009551030007a002000e440c4d10080003403420343d866403e40c1040b40c102800940c00154080304006110540c203981a088580d59110492011426940203010394640c400000c0d03810014080703c1c00103131007080300507600146610341c000c0c907240a07a041d03200c40d2026034940b6880500f0510780b0b0b0700070001208550409800101c10340075015502c01e01e1240d80d2015107261400342110301c030720302c41c00340d584506409800103a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 790671232 1250 790669982 790670071
    0x30909160210110408151e0c12041a07020a0b010e0604020702030615091003050c040c050c0a11012a0809121f0b060405010509040c020f0706020f010c180e 68
    0x808030a21308000040d409014204810601400301c502e00c030050803e40041440d15002d42d647d560004150240d42c0281e0704521015003417004201d4000300000be405440903040c0c12580d46d10070120380e1000002009800180d4110040c000c200a0245044d07200e80702400151078050035a000c2072508404a4880c3c5080b0020b4045040e240b41080c6819082400c0c0000201241d0131174507019162600b02940343d00c101d03500e80c242c000840c094400c1d039149020799030503202d00e0142820725030ba100c04400c0c1c0040c00560b00c0c1012099005450f01140303003d201071402e0300c100d0040ba9542c0c0d60158007110480c0d6104003034038816044007004000c4444a281800c88c20a07041c0564560764007607402e40391410784691020f01c0280f00903640182512195002200c0128100e6140d10042c0d051446420202d8440e029081c0d021424a8001804521507a540c000812241c40944000c070741c0701c40e650203840c2848017140c00800c81c1d507100350070352600003500c0b40c0d2070621780640315900300b140e2254407005100030380003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 790672482 1250 790671232 790671239
    0x7031d061b010c090518040606030b010303050304050f0105101a041502070609080a030804060f0b12010b010e04050106020712170a0309060c020d0e101704030c140309091602101104 79
    0x30700540041043e41d06103c403040f8202000140c0e0941c400120000501031100000c003409490b401490045030041c0d1440c42558407070400406552044406640318410450ba14130b206605200351486109500e81c404042410040c1011401c01c00c0741005402d19800d00c80818002109140302d40d24541c507800820115107099070142410106070300295968004101030070200e5001510668000c2d84800c000134451154003000d002484e01080741c0d40c02099248d540050448150f000c604500382c01d07210205101c11050400064590034043c240041e0090841045041c407400c040700034043c82800c48041490305d040720096181c004200d402d0000c2c0c1c5481c41001030041030300c0307105043d090130300c06400814032508000d040308030034400d4680544003a003d600516031284404540d00782c800c41e414041420a414010417034141b12205440e88480f160b0300c140d81060001c101c40e90f0305800742005009075035001012609480c0002c02c001540500b0480c0254000644548501c0102c5a80c846440310304 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 790673732 1250 790672482 790672537
    0x50f010e061b030f0604050702100614190f0302120a0609080703080a0c020d050c190605090c030619090204140a06030b0703020703050906030a0605120d2307031d06 72
    0x40c2c141520340342a074204140310000e8000e054042c1e01603c1502c002c030702501da52504030b19203a1001d0f000b07084503240c40300c04240d4104c482c0c0e11002011007101c0f07000601c12044001d9251112900c101824160441000c100600f82401010000b10160007500c5646205071661819500602801c84d0115000100c0d0010540c02c10740c0039070001403c00d030412001c00c5a290295480e104041c0f0041401800704042885150400009607244610400803410f030100385442805000d003540c640000303005054000409041c0012101d1242941c440b4468651100d82408002414480001c6c1d800a48503a0038622080d84000f4880c01a40c800000050340c80c13039070824091090700940154101401005003c0110380c1c010709541444104542c0c0560720b0b280c004511004103580d0340015003001090701074a0030840c0c00b20384000c8880e02e5480383c0f1b1203140c00010042c20208030480d40d0503108c0043c042c00c1d02191051891540002822640b084504803080029100d07402c5010b809a0306901091135541841c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 790674982 1250 790673732 790673761
    0xe0904111305090c0918031611010503130303050c0708030f07120c0210050c0c06040f031b0f08071410090c0512070e071e0e1e1c050f010e06 62
    0x40d040d81d0200a1800e102c0b4400351180e80703840945200380c0402e0082188840d00929116000365140e00f2030f983c0d40001101c000c00032040c0307101602c0c2c45059025a50b4154010000c80e40704003640807000300b160441e41d40c280d00810001e0540495035002380301c010000703041c0c140214003e017403a01800c1414640a180100031040e551003071a6111304140c908501c0f01d0700007403100703c0c1c140c401d03201047c282c3e1610002d40060140d222000050b100e040140310501c842070851026550103a95804020700a0400d1080c3c040c2100c0c074005c01d034040703204d86038001c1078042001e8180203124a40d50702c0c140714002c0340340f45400c105800d14011690380309200741c10407464426440091800340c600d43c0c9034030703ca005100e456891034400c0910080c1c10200181d03200d40b0134181c0520074039078110010f01c0c8110901000380309185101c07059000350040700085100140082040e280c0c024000c06400da0309042c05000588094800c0044030f0522614017440a4010b00f0b00030441300140403c014501c42c5044540700c00d001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 790676232 1250 790674982 790675009
    0x7030501060e0a1a0a1401020a02030d080f09071202150d0f0204090c0e0f090924010f0e0411011b0209041b06050c07051005040503060f0a0b030c01020a060c0e090411 73
    0x2410b00113803441190f215403c5400072038081542d412000b004080050341000c8003000001e6040c01000c00340c100c240e8121825901541400e04000d245030386030b1604031703a82c2e01c0c01c1c0240f440651901c0b05110040c0340000032400d030a00840e100307d081203004003c00054409a440285200d6004542400a1455813184a124070002c0c500102c25020781d0011440c000e03142100140182c0b40c4d4000105d2a10b0100042000300003070300209441c0381200e200d4200628000e02452000c44a8014001040000c11491030702a82c0c01c000c64001c049050001912920080300800b4040481510308001503600c1710f003482c0c421802040c3c421500e2a4806800031262000c2d005001401070521032040d0081000415005460003aa5182c0d607a656452042d80c1c540510351026505100b031500b00064120100201405070050800501c00d100c1107504258852202080c03850042e0300406195004c1003550b0880844c8a510342081415030400c00d001c030784200d4040702c0a94070841d0700d00c01c00c06141480418000342 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 790677482 1250 790676232 790676261
    0x10503010b0301090c03170f12060301050a050405060a2f040e06040504031d18180606010e01210e01060e07081308040303030c270e010f030b01150207030501060e0a 72
    0x918582d20380c0e45100e558003000d071003a219000f142c90010f01f02c1045802084000c060305440d20511260b0000501041340c00c18002d50030b0401103440d0240d20300910740a554064040e0485980b00c0504c14014201c0d8414540500074220480043c0c1510070b400c240501c40c0c01e01807554039810698010b040000203003115000e01c0c540410000820350144046002e540184250100640103500041908481ca18103000540010082c0140c5000d444020b800410704003044d0784250b0354038401512103010b004000d130b01180540044029200c0000c01c0402e4a800f455000a0b01540c0b0070f0a65003140d00b2500309080003280300b02440681ca411280c010340c000700d444601e81903100caa6858a04500032840020103068840003003050040c0180041d95103101c6001c0468410a00392200e48020300403446008907a0758000001310b000c450508501080d03e401c1048450f9a900e080d4104442040525035502140102b18000c40092402e008040090640d54182c03405401c8c6170014404440411008491 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 790678732 1250 790677482 790677491
    0x901060c0c0807122319120e100e041b020313080f03160201051b010b0a092307090e0705040509010501030e0c0108100e04140c01051e0304021512010503010b0301 71
    0xf4868102c02801c00303180e202801c0c1141c80995412004000417590b0300d140c590151041060b0404506d150328070031503000e021242900c00203c00c013a21508444c40000e60401c0d1a1400c0217102401060081e4050304090000219800e9609044005108410100006810020381007005840609054000d40500350281616100c244943d6540b441401e090716401ea000850394000e43e80078000b5590200c0c030841c220040c12030000d40e000e0007001200e140521500d503404010407005114415921382c03018002240c80740e0031050100c080311450040000d0304001002d0004510445005120750080a0a84800d92103504110400c43e1240c0c050708001d0400d072030b20452200150340090ac2d0700120000703003004429602c1d500e0044541a11a401507c6210028020b00082000c000d850344c0d03440e5100300035541214540001110f142c400c840b44000c400103003246001d010701c4680002d50b00103100a2400405020720310a0260710303003202110304e04103200100104460300b000c1c003441c076110030708070000c10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 790679982 1250 790678732 790678739
    0x2030603160b070204091707060605011d010c0f140f0303042303220b0a02030d1d030a0807180e090c1219150203040521030412110109020901060c0c0807 67
    0x202c24050080c001e845103451303102035800e01203d44000d205110784000e0b41030b17540c0070905011000d0143e40c0300790781c00540c03110010b4440e05000214030981d080c1c1659487c05a440c1e548481c400c0c10f15a81e01500c00d0461f003812510182400c220990b00c1e45242e5004d50380700c0c542810154003880000c090790706144a000d81e40c4040d20400310845040300341d8000452942040c2158440c2ca000e0103400c1103141e00300001d034402e10719400002502107100c40440c280613140c018074550880c50300082e2100002c4e44140312680140f03020b814040c4c0c1c410020324100442900000094100381c44950080540020603c03d01c500b600303090120248192080d00c202582032052494950744502e021401e000d0f82c1407606400c0e08103d03000c80c200c0d0482c2190780d000c0d03499080605049071241d80745101c2401310a4040100d07d14401e190b42540c0c0309940102c3c111181e00340d132403415107250078030b1011211295614003035031005944001107107010748016581c41c0c003040401d14004074800c0003038000310841d610214080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 790681232 1250 790679982 790679999
    0x50306070c0609050c060c100501050607170f0f0f04080d030c0f0c03090815070807020a030e0f0607020a0e15030a020915060c190309060f0f08060d14010203060316 72
    0x300c22079521610009169009003001820800700038182503020a00082c202e11054001400d00c00701301c000c240810150340d850007041707864032070808000e00007d01d8150550517500c0444c0940b40a14009009520300714401c00c0840c8030341c2c04044290750204001c1802c0c030001e0000c001c050841c40907814104414120045d025005804807603c8808100410401d8010507101c0c0c10210020000c1d4001c84281c22165040a1306000d0103d0350300c00003820660014980c2031000850111007505911030f1810050f001040c010222107100c5001e0b0080d1007040b51100586a000420700104504c500303007545401c08416440404c000300080074805e500807090200541e40f600c01c050740000c6099190422618280003154041c015260070582034041d042644552101a54a0f070403080c0c0301e42d80d0300200a07210101562103c80d05c135650000151924424034441d4003813960a0b42041f0b005144412620603680d17045032090825000c0540e81c0d401205108403410308020465191020071800700710182008500d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 790682482 1250 790681232 790681247
    0x120201020a140c0102040b030f09010c05040605040306110f1918080316050109150608060f09062e0609050a0506030f04110f0a0b0909010e061c050313180605030607 72
    0x1c4012142c000511803504620940c1228010007107050784507100c0c500f61040c000c00020423a41c0800d030703500301201860010b00c1141110140d440700d071030751401d01c2c0c02d54403010300500000c03d4070f1645601c00c10080c4c0c04069040040c109100c103c20807040c42c403254810081c204044800900428030004d20240000b0314040141c6110303140c104101d0007103000d11308200340504044c18000d00700c01c1013030999120080341a000181a91080d104a402c180c44007040d001000c0720843c0d029403650442c1001c58410480c1a902d544032007115604500140c4003a880683c0d07501c1d8540c0a1380104100384010040b50600b004408000c00302150114194642410501007001008100410031a015212511a56a000341050a0384405094610ba080e22544e04070105e500041d4040d200d209503400004490f15204201445441c005e0403242c480c1c2e0311034401d1030118600782001c0f1030b9400700b0301115090f8031a00500c0f400403c200c0700c00c803040e00300b80d00c40741b41191384c9900101d01030f4110000300210350350007009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 790683732 1250 790682482 790682507
    0x70605090f060d14040614040b010302190b0a0f1206030203070e040318060e0418031b02060403061a15040e070507051006080f010c02010b100f140412120201020a 71
    0xc916007000d07100d80c005081c51080400900f02e0780d14001d2407214084c941d108151083e07200d0041005081c07104440c070b04003da01260002c202d410f28000520041c01c12030f520810440c103858480305180c1e110803441d5042d401c0400da220000e014100b540c61b102c0c1d40424030301905c0d101e82100b08001d03030650f00400c0e00da40d0980140450084508041010035104003c603203001e00c0b04c080520101c43e2142c100802c641b00b0164024451800c0c64210501c41d0244c0100d00152039142d20344032640c162039110702005c84040b0800740d82c003403002d00002000c100d1500501000301c40c040c0c04926400030600400140445c4000603800d401820300041c4034000f54101081d80005881c10400d0b00d8a11034a4101e1a001c0c43d6807081400c00d0a040c00003c0980000540c001c0c400d550343d000744100b01c20b58200b02e00700c5100d030b056130b54000c0c41102d070701042600403241004802d0007450407001985070100e020761564819400a044070643c04c03419030500c05002c005224220852000b585403581940b00140070300e01410707 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 790684982 1250 790683732 790683739
    0x705180d200102070f141005180112020c0105040c030c1a03070302070804081903080108010e061f0e04050d12020405062b060609080706020f1002030912160309060207060509 76
    0x3059100341c2c0e00800031640200340444409000300e0319500f01c1c070b0103291200c0419016007080760807003010b1809202903500c82c9807280320039564018821b00445103207114582e01d4817119800c10081804410078010f00744198050b04003214031503d180307041d56041e040c13580202d543c1d8810070350050411b039015003281c0c1c00c00310710b180140c0c8503101802c109266100e141c0c00f07425984640031030002d401c07254040c40104240644c50790a903580c2d80c1c184440c240e030081d200c10b11035500941c001520b01048944c045103c6004c01c3c0a80030010b8079603a5100e80c1c0ca0050317400380d5071a03109628040a03207134445001d00c0d6501221405504140c40c0001040c01c0340103d4044101e110300a0000001c0110508107940c0b07010340c2032100b488000e0f0340351000341c41c5180d00e01030305c00f00c0d0085030804a041800040c000d1081c0c80320400411442d9848c025600c000e4101400f05181802205440c03040941c62002401100702c4c80401d06140034500e103000781982d00b0f603078046402c0d5003184104214880e041000d54018000c181e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 790686232 1250 790684982 790685033
    0x6080d0f14121e061c0312050108012a09031b08030c060a05160e09040303140c04030507120f020910050307030303020a020c0405090d20030a0905090c03040c03110102150705180d 78
    0x500c0d09550f9013031f81406110074540b40100005080300150001c102402000c4682071480406030b01010030583d444448501050100904000040b0b403054910a6104802c819040c0e10382c4404144e82513a102c0c82e83c40d031180d40321034140b00081059210780c9801c08119482e0041600440901800c00703803401940512a100740130014050600a0f0460140341040010b0f09203030340f40045545082e2f400c5400140c561380b16a42021801a071801c0e40c05018640207003880404000c43e03420400800002054022001030301040012661003c010201c0914070a84001d40c0b14442c9200007803501106200031480f0301e0408043c0241282c0c0400c1c10000c5134814603042d00d00321a003001610810150b441c4c00e181310b100009801410b6640041c03050f007035031402c4400000a485100c8190054003090703c01a180d800103030000c00000e208421407a0f1301c404d060055602003898220682c42000c021107101001c11000281446640600c900d20f42441c581124100c114601e26100e5207501d03042200e5030414500b00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 790687482 1250 790686232 790686289
    0x507060311070b04030305090f0a080301120203070f0905150f010e0f010c0b0c040501140a0e100c0501020706090c090e0a0221100c1206080d0f14121e06 67
    0x20107046507a0150045480440c604140ca0001c0042c103003142c41840500800040d10800100403444818030b5812201560959081c252103841c01224844200c1c2e05101d01000000c0110800c4811001060018000141880d04101c4210020440304455105440b100c480103c181c1c0c010024184555050700e11303a13111048000140e88004001e9000b609104141d400c000d95403100d10010800e40b0004c0e6140544000c142903802c5e0719000340c009060210752300c100b4407900340c24107140388154030205240420030f408058980508a80c01240300392110b0b0784901c1c1c241c0070701c1400300381031000300813494080100c40d014000c00781d120307400d00030300a20840c0320713007858034a103c42800c640c8180c10000060f10481d1881409903802400e11807078410200314130340210b00300381900340301c7c41040340d81e00c2c40502908000888200c0d5002d81110503107040c4060160344000d2560340c0c001504081040044100300d074105801680c5ea10264140000e4103484147d00b00201501c030f00c08031941450131600721207215440c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 790688732 1250 790687482 790687511
    0x80408040902070b04061103040507120302162919050313051507030b100504030602030a0e0d0e0a09060b0702190312030902040b0f030d140d140106091205070603 71
    0x249500203140a400450780710203200d041800c0a024600c509000c007d80e1460049011240c00115000303801c9401c030710810849c4904150044070340c81d219205540c6031a041c482018011002c94004041f1040c00744055004051040d0154800c150280101824440c01205048002c15250050810803a011000c100181c1c1a4144402003940c008241e070000c888003032020511400c100d5107540064200000b044d0b49040801c0c2642178190701d66582c40c41c0900f5900c1d06e2019500140200c0ca105940320b10002c03000c03c05004082540815588640204000d0020080100184d40103401824908141005500c4000044911441d030566450002100a03103048a4805483d070010b001641c00310400c008855040d0b0200752414400c4608108510009d024425a40c490801494069002c268421030345801000f5422140f81c1000007a440c0804e4041404262042c082190120200762401400a0fa402148040c040d2440408161000c22035484162350f5210502c2200d05140e940c48014842c1c18 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 790689982 1250 790688732 790688737
    0x4090302010603140a0317090c0d02062106011d0a1a19080f01060c0b0a1d03070b0f07080c18011b051b191509050310050910021603080408 61
    0x581003c0d042c501260340000042e19000d42c02021800a00101c2451207d02d40d007a4605010b901c1c404010650022601e00780301c03065650500999100c0c2e014450008258491010040604240500b001e02801c10500146c5000d901c1084200401c2c010326101700e0313035220203901c10200d60303400c103000d01104000d8030204a10f100300d07100d4029651814130800f200070307004031006d03020b24211044140c56aa80d003c048600781d4200130010501d013105008125050801d80100a04484904003098000c0210012034603550101c10122180300d441c000b00800e0320701c0e0042d0254444510f042901191500e140151300900c601c0d1818080c05240103480f030220703403040182803415002074900340010822410125540c04c5581340410034840320b000510795505100c1e0020103040031185044c40298148101c1c4207000b9940140641000301c0030200042da0b6a08103c031324140c41003042c0c0021103041a80415050030f21380392259451900400089091811084020310801e4240c80c051111b42c64902d841d6003e403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 790691232 1250 790689982 790689989
    0x120f0c040b0a05041415120a23040210030e06040f05010f0c020c030601290c03070209040c06021506090f0a1104090f0612050a0b1902032508010e06040903020106 71
    0x507000c201c11142e00d070090014000d5801e02d10388140303400010750411203c10060404041b0030031040c8410400d00c0064030800743c000e810300754041604032035110302284000818011034040040c00c0184801e608141000000d5400d8501e0140800f081d4525000c0d42ca040c0a00001d00f08490940300d40c040c80020341c07149541100c4518203004074115540000c0da0307034100c240010b200c3d000c3c03c03000240d010424100712640c0b0341d450340e100380700011032503521600307800542d0480940e000401151005035181c8020522031f40c4a203a81322110350400c44000d04d0710380b04108a103074940d002c20600046942c0d801c0d140d0b40c840945000405190383d0b0b0b00509020300083c00d079a0860880c04213012403040c00340d820201180d0030408080181c0c1d5651045909035070100c00010700f464105060751400f2502082650398401612515541c00034201150300081341e00031600b00881803201544117000742c81030b4031a0000d041091410b00c980e5410184170004982003d480c040c8641da40e00380f1402050f00079003280004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 790692482 1250 790691232 790691249
    0x80c03040e0f160e01020607031d060406020c15040305340503040816050a060e210c12030a2a02190e0721020a0c0b04050c0f06120f0c04 60
    0xb800c01105000d0121010b88201c004140301400510075180705045841040105a0080c1425214844240c004200f035402c0058018503107090107400b8a010440140140e21503d40140d8a01c001c102c0e041c00e1096070203541d03020607844401c4c0404640e024042d07a9200180c8130800001d80c0da044000c29002800480c5402e481e00181401c100384100070010300121503082c0e05540d070381d0074040204072041504d030040da03a10802d054810302c010b81c4902d001c16a042c40217030810030301c0643c0b05c3c0e1642c0345845074241d540440d40811504c604038104600d1401c0341c012403000440c24044040400750020020002a2020140010780709112252110018147c960003400444a11241442e807541001d1140106070341031240c079012071300d168424540d40c0701c5420326981819120030030b000114082d41c060302c0303040108001d0b03206410103d0000b1000b2405944628010001407403980c06100283d000340700910710840041c8444030080c04548245640881d0300911514070755180507102c1824000c54001126 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 790693732 1250 790692482 790692509
    0x130506091006050109050105030109200f0c010612030804020d0203280c15080406110d020a0513140a1a0d020a020a1106031018060506030702010c0305090303070507080c0304 76
    0x400030000c00c1c0d41d5008008503000388215600c400055400d0505485014006a02000100b02c1c0c60402d61207034560a6031612018907440c2c040c40b4604007900210f41da40102200010601180d040900c10900289a00b880981101201d030b1405402040c0091000e409944006040310446d42c0c10320400080e8804d031810790300483e018500d5201740100e00d000c1122b000304d00c80700100b9104210301c0e002c00407020654982e8626641c40d42c0d000003600600030004406682401001d8103820240081c1000c0f209130ba807400c0c0c03203114031150030688032180d5102c05202c81101100410a40750a0000f4007650f0300302d4428079480d80b0804002510b0b10480c00c0079010f491002c00c0d01240c45a0105002501e070740220000480035942130308110b5207110503925200340c107170002408c102c080c0f111001c0300100d940c0440001086c0380d6031004544254022103040c0d0050355500c141120b01c6130180326203600000f4040003582140360000d03000c0c1c550303c58880c0103840a071002c50a104241000c00841d000b92494954414 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 790694982 1250 790693732 790693741
    0x3061207030221010e0604080a0c051603031d0d0309050f03030d060f0305060f0c0706050c0d0e030c12040308070b060604030c060806011101050601021f14160f0c1703130506 76
    0x40d103400c40c243c00603107a508042c01200840e0000504038003070380d008414285400101c9209586441e10500102c500f400b91300140c010341180c41c4060300085000f511000602410107814031080407150740254490102481c8200221740d1200e504070503210151040c0c868030082c8000a0b2940c040c0204000d1000e080020200e491450014500106e908c42c90440741c01d601da0f46080c040c0140100c82c0011442824001c05001c1100c80d04960780045184240340d14050036844a203044c0c3d2810030366100a075100191854000c0420840d4a100f82e07040301e8020300303103400d6a07590501d030310039100003074102440c0b00c0105000350342e80c60444e00215030004040900380e0303440c00d01034080e003000c49986012a0a500080720800307018054a845400164050241910070b9100503543c001244200c0c045035a949915807060521311895034081c4211a1401d070044c03031140801840010020300407003c101c01e142c3d52000051a084903001000203140300c46850740c3d1281c881d8420300c03d015002500c00d2103940c0c24003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 790696232 1250 790694982 790695019
    0x1407030e010f2945090601060f0509060f030a06050a03060b130e1e160e060907090e0112050a0b0408070204150f03150f110d050109060b030612070302 66
    0x100b04640b5440c10b1914100141d0100403a0501800d404541001d2038061300e01400707456003001c03507444080801282198004c6203100003808040355110902c1d444040103210094100c1d402c28030710001854520301e807662100218026000c0d11001142411303011002c280b001140b600408007604001d49880a80e6580b8100500a003a040d06a1030280745003950030000411140a00e03100d121115004100c05400c070107514204907c05200308100d17005001e48a9455100014072900401418061003014100081040200300018103480d050110701d8404010540744030394401d04451f002541132480f5000c03401e0150071300c001c404001301491200800c01c410450101c01801070306000b0707103041080342c14646151b00c540103607000e29501d0781031030101000021002c412070981da4030200300c0401c03c000c4e064100c07401d440d602f8040c5040f142c40820900e00c20980c520070540140701d210700c01d100c4540b500b24800190f10001c0c01a038003032042c0700c105410107103040110000466014195001c4d8985aa010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 790697482 1250 790696232 790696271
    0x7020d0204060321030507020d09141518030c100215070c02040203010612050a0b060d0b1201020304051c0201021303080a031b0504060f09300503031f08011407030e010f 74
    0x104c03008a40307420041014144001454100070002d912106507050501900c88814203034640030300e40c0034581c0254440c2440502c006009451342107001540c2039100082054184450a1100c0f40603131b8516110350070b49036000550b00c0e241e801d115078004040e00c540804640e004a04a40690094000000011210340c080380e4424080c98000e800c1000d601d0307012013074043e80e0290304003070f510403000d01ca07195026125070f000141c103a5008140744640c0300b08071421426178000726400c0e503813034000381c1c201900100415007070001d1560703601c0214a01400c0c0c0c0d040a818104600020340b03074420100e032841d2018001c0c3d001070f03410300300c1e840780d280102040d5000a042e544107000e640c0010389400049070b0000e0140c0d500e902509d000c01c0d10706102a03800003000300701c41c0d02d1924003d0303100d0100d8041004a24140002c43c050240460262001d030320700207400100c0301c0070741d2044950b80e24101c00d01080160061100c0d0300882145404a8000b0355110040e002d0460b2901c0441203515140d0b686082e000310380c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 790698732 1250 790697482 790697543
    0xc1014040b060d030f0806030a1b030b07090806190902060d09140307082514010b011d01050a030f06051005031009050c0f0d0f020f030a05090105010b07020d02040603 73
    0x10201c129a20582449150000200000d000c924102e425203040d41c06050340360383c45007020342112040510340d1030365001070741c00c0c83d0850945505100140240315500070083d81c4083d55080c01e036180307841c00c40d015646040041001c002d24443c94106103541600c3d4000f0a94140c00800003600d0301d560f050034000030142201e00315002ca01c424010008402e020040d42c460035040360b51541005100d0f41c9080480303103040d41844a5604560100002400d90400031408000c414000500d1082520000d014118420141030001c3c5820b010076005a0b40081296101f07901e500d004100c1c0d4840d031418501624003034210613440b031280c107034020f900343d84a00618880c51002d03000c16509681c50448501b03c504c10b407400540d44808200c49500314480c0c0c001000003102c00c48000842041c3c1c402c1c14400c0b80c101c500f0000310038078004140a00c2e51203074000e6541011410f00204565450941ca14451344204080203002d1841000040207554403030780803100440d00000340c0c8001d0b106c41c4034001211031200c80c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 790699982 1250 790698732 790698743
    0x1118030a0b1f091107030318020603010f0e15101b020604090b13020901020c010f1e0f2007050d02040b04020c0303041a061011011d0d090911030c0c101404 68
    0x30002094109030240c142d19030910135200d49048540c0d1021000b802c11612240700301040715545000585840d0000d40c020910384202c9851142040107103209004060000310f00007110702403100c2c0d2a41c0301c0606221100f075904082900c010341c50010703046181c1860000c0e50000d004100040c0b100d0494021600d2650200c030781e0901500100c05510032400f030108080c0c0140c1c0b0200b07003980301354020904c3c0740c694000740c00c1484c400090507048070f00001003681c002e0005804800d900146e5034010000070041403c003555820300c101701112040e615149031240c0d0380303d00d6450b010341e425502c0b2031f07100e03115980c4040d100355524100d06a000385c0d240d03c1602c00b12402c0303049101c081c1000800c1038400d0701510009211140d100c0c000b100484040204844403003180d51707148204c026a00f680511400510004005040c550107034001c0900700d007610350300c44a00603080c00000f01c0724407008000c84e130340640051082619031055458031407030001088500c18950b450403099054110b401100680b1071440744 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 790701232 1250 790699982 790700041
    0xd0501060e0603011d06040f0218130212030304050c041e060306051b0703020619020d0510030309090e030d0c020f0a060603110103020403030e01031d101e1118030a0b 73
    0x5d100c000d0031100c0040f40244144c1121001c20001100758005001d400d000802202c101c2ca0304c2042a2501802039a140c4500b003c0c04012104508040c070180404401140195003145043d8448584607440c05003142d10840c2d0b9800188162414150000070004211004010064403490610024501074409050b5010301c16070540090b010002241c1c101541640940107540750f0f000c88925200c2c2c1a02e40004250b000d010400c0d0780f0240b072084030711500390040004d0150b451400c004c4c010100c1904003040030b5042504560403e9000012a0700400080200050305903942c00104e040072000b071003c0740d51b4090001840f003480301c41c0d08100309a03405070380004071000d03407503005404030301c00d42c40014040303681a4a61207444d0b0103584007227000146110301c60056191050001d082c007104d60101e030006a61440d190201c1032146140e114003070341d00b080801c01c1034500b0b1208820340c00b40110006c1250214401c1c7d44507510280004655030750710031a80b070390a090124110042d030704003a1555080d829803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 790702482 1250 790701232 790701251
    0x8010b0402071a100b0c012408120c0f0f060108010c03050610030b040f0f0e010513020105030c030a060906030c051822050102091002030c06101a090d0501060e060301 73
    0x18802c5941c040c0d405003040307a0030068280e80501d02a0028035069140d544544002540d0b01604000e145400303a020000880c28075808a60300030500840d41e00f043d1003c100da0512001d400021203101d1030807a0f0407000c1d1030f01c0c07612144074a8403044400240f141e02030000703000d0101e1300c00604603058940f007070028046403c40d0b240480880f40102d40041e444001040c2c0c1d145c409019501900380d440713000d8000b003500000800c0799001c1d2891101d590188503035424406003015428491a600590892403640d49041c0c5a00000c02600003d850a6443d000000202e084284d0b01d0703008100070801002d00340011940ca0502e0303540c1060501c1858090031110448040c0c600d0090003891080217038071660700e020111003907010181c141c013250840d0259820042180c80b641c60100740c840c00001d81e4000c0d5aa08615134540d410140042d0481880c1c01c141d5800340711341560180f500149014520b9103948506103013002a00c4441c05220150403540b0307159011401855500010748111030940092002038030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 790703732 1250 790702482 790702489
    0x7080105070f0806010e0306070815060c07030303020c0a17070204140f0103080c030f0d050a0605090417030717040f110114070b070302041e05030c0d021e06210108010b 74
    0x42200c08500007502c0580d401100d0380103030720682d04401c040c90b0411301c10300c40700b01003440c080c030a880440c080b404c1d100420003c000c00354208010a0820303500e06040500f00701e0140e0b45c40c2c606000041c2403540110300910045401c00001b064503400904255a5226507141e4814680c40000182d01550500c0a594030354030184526a00900031516100d15607031135621131100c9070b001041291043e001c20001d00d00c40000d1500500b40d8001c8001000a55007404410320045440b10751001d4001d8950030200300116002580c6a4040940074503000ea481e510110211001c00b0030401c0b11482503c03e605020501c00040002c0c8044c5116117800c8140e8910361006403000d4030244940410303201c0800c000700005540c4013080390881ea42d424058101038070f410281d13005c2c01d1011645d07140325842d41400c000c680342c00c1003803420405050f50f00000d950110b80100f04004500300090780103098000c003200c15074503030008036019002040c1c1380381c074656031403650100481002c0c402c1650560070021083d501c0d16 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 790704982 1250 790703732 790703741
    0x90d0312050f06210f01020d02031603050f0c0702180403050703110105091f06080715140a090b070309090e0309030f0601060807080a0605040216120305161b0203010e0f070801 77
    0x500105161411351002c101d84603c19031418071240c607402000801c59540209001902e61229603d00140e01d80c5040140205c801400349d41420401d405c1c003060011500c00700711925003242e4001c811690703441c4075002160010024140b9024060120360400040c558001c001d44642803287e074801003052001c1d00414203035882a501e0b100240c02190060f0310031311020700310000c0d06a800c04003090080d039501d070b150300b07084091b130101c066901c1009142d1a82d903030256050201c5100d8040d41420442d40c040018600c280c103000380c01090500040744c1013414010b40b94a00100b11000303080c4124001c1511158883d004200e40034003c0c826220701841408000c0f03640b03411b86809654a80c4e660752070500849804e4409003a500340305a54603004034090700c0d00e00040442c4840200c0c0542846200d2801400182100c080042014981b81c1804801a0000148180a0401d142c6845035101902114450303111108000390b0661800c2c003104c804041c04521800404003045c1519403072582d4a29060a80c0e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 790706232 1250 790704982 790704991
    0x31b12051014010309020d0b010303020303040c080d0905060c010906150f0603020c1b120a03020307030e031b0613052107060c0309050405071e08010e01060c030503040b0c090d0312050f 81
    0x24030b641c00030300318154800d0b48180b0081e4002092160200392580319400c008500783c200741e0068000008000078800c081402c2c4001702821002003280701d10a00300104019560700959114800028400c4a00003094110744610340d00801c2c100114a00c081c6103000b4180c4034814481da41601e4440022500e000e88280c64220b5940300c042c10242c0c0429102ea014007101c48200c55202002c591402d503800700400041b51460310980040d50f44120504000e08103960342e9404910a0380800404030081c56a104c0a140c005c85c01c1e01c1f02c0b5141d05504028028100b0030750840d58101c0a03a400c40d240249106c0344060000d00800e06454005480740800c4030303214256107005d40840e1781c0040400c05070400d944103540c00401440c01107002c982c403010000c030310040b03204550001119400140041d107400280d4500505550500c201c280c0318664000e401800001c201501d10360f0140002264110a101100c001c6000141003600320441032034046c10100041414180035440e01d80010352100d400380080303026 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 790707482 1250 790706232 790706249
    0x507020102301909050a0311090a1b020a020a0807051804050c042903071d060a030804030f0605150a0905090a06020406030914030a1e031b120510 64
    0x103000103a5000403444840c0140034000c480388060065081281070301070f00106080c00c4000c5100441c0510061080c009034101303d02c542c41c0a030082002800d450031703040008505a03402c00966540a02c00030007003140c000543ca018a08415018130182d01040c40c440c0203100b20740340d84200307854842c00b03a40c0d203d203800388a0f005940e42c1d08400b0800d00421407681e1051252007182d111503d01e00c0807400381d84505100c0301d6045c202c40c20246282e02c47d184821800342041c0c0050280911300309006500448003050140e01c00e0851000c9155a1112401c48015540060340180c1d150b0f0b5038980a404686d046206031003003843c0001165902000100c074030840c0000401440406041803108001460013500202d9241700b6841c250002510320b00107400102040c0d240050b9200b200d081801d90b1400c8294075003c01e030820003543c103140d5040100d02c4c10956854030001e0b2400941c000541c004c200580190f0501c02d41b01903503011180d0b200031407000040d076942041c13084e602d822492213241d2100b405010740 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 790708732 1250 790707482 790707493
    0xa02031c05070215070210080406051503120a0e0603040507150306030c051c15050603010f0908040e041a09060126210904020f0a1107150c1401050a15060507020102 72
    0x140c5414201d40d8000520340b0703101c07460803101b070b40040c0c50741c8001002500403c4100080209000b118818142e101c401d0a580825032003040700066210392081c80300340404140440c48440b054800c2882c10140040500070565a04240c109141c1d01c607400d2151180d804020104150528420f01030502100e078007440740c1103000d003800304005503140c00003004442d90052600c2d020104102c0008440c4c1106c0309400042d15060100a25082d2200c003407038148024104018480082d4004048030300f102d110700c3d03a04030702d515103140c80424035036100e00101c0320360321b044180040e100c00070588d50704036a50302d0341c2060124060160359050125903007007680141c0000d10301e82c580c0c00c40c4c600400041090104200e2802480c9400a41240c1107801c482c041800081500c000700c80d000f1035404c0e10300c215180140b54040ca01050b42140c0c6d180b080c0382c4010401c02c0301d074074020851012040140c00c80c080009124a190518210b00107080b06020204920745509001034180d004004858115406902424 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 790709982 1250 790708732 790708747
    0x1e0a05150708280306030506011508010909060e0a0302070918021806041107060f0b010801030507030f02030a02271b0406050f07060509030d05090c01050301032a080a02031c05 77
    0x181caa8015107050600201012200143e000501c09207100000c0c42c1d0320005605415030034858034261050304074815404140c44c58003c1507800003c0e00e41180d031181c03000300e40c1c031140d890004050413000f030301c01245100700000c120801da00800c5c00800d0301c80000d020088036140340030401c1d000707450f103a01075080300c41c0b440c040c550b07501c0d0241059880f0402400224807100615090042d41e400402d00340c2d6481c0d0b40714014080707070615006403d000b04003468140032950450726000e4588c00c60b40700050070301340c045005504541341071010380412a0014101034054402c0c0320780d50301807003441e0000f11456489100040c1da016070350b003180015403403c210043c1041c0c1000c0f015625a8000c030149644400140320306c20010b4624014036108045c40c5000e503485141048181098031400352094801da04003c802041ca079034004252811a0b400954000305424604a0075200e0030545804902450000c1404146a0800205850716510a60072500000030984a000c02c4011040101c00068420032520 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 790711232 1250 790709982 790709993
    0x40206030f040f05060c040f14060f0c0a06020417010506010c1101140d0e25030f0b0601050c0616020f060105100c1a0115170709050103050a02091e0a051507 69
    0x441c1c2c820f21035244000342c03412030307111355241c40c50440d082000c081d800582400340009000b401d0009000070820030307e0303c0811500103081b03400754007020143c0b5a4040361200d2048030422107040d089405c00d10441d03030b464441800c0e6040303003802d420080c02c3c0c0d0f003024041070141d4400e980c1c210282c4d0b008030107091107590002c011520249924488660500140107142d58110684603408940703c2c204010610300712340101c131303110141c00c00700200100c1582030020400300d0b41c0740518010f07040d80205407020035922440181da10703010300c8400850900c542d104011040c007040c4111445007450340c084441c00150240030a0351381c0c80074000c0b41c0c0c201c400c50302c10018181c0295400c0704079601c160050650b450895088456450b03099200e009041c0e004109504103d420250002440048142c10181490449005019801c85103c0e540c10155200e000620703400c0e5a0307043e601186001070540102c166001809201100e103c1e001c5880349103440c40020b880d14021160032440084c06070b140e820a0506d4941 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 790712482 1250 790711232 790711261
    0x10813020a1710050903040609150f0f09080d120b060702060706090512070b060114031e0405010e030a020307020423011a070c030302031e1806160c03030c06050a020304020603 77
    0x1802d0041c03240d0420400080e08601a5070700c10380c0020001c40d212403800200402112641c1d1025203040c00c25443c401110364092581e000c2070080c0c0c10542005541c0000403144090075034441203050280c81482000d841d403240d82c1407400104040c0c180107101b600010003190703205004000f948100100030b0140040c6540e00082029400340c000d54100da41e840c00c00001daa84aa50304880311400c00040180c0d030b40e002030091000d4401010014250301c3c101c1e0f0b00100c10204241d1200c1d81041c24070006042140035001003401001d004c00b0789450748003103103019540381c01070042240b08500b807440e00c20306924454003401b900d81c10100381600d40c0c1d2030f08c8200301d08202010619441298204074a0000c9001000640001c0d072080d80203560341d951940054482d110704414140d2015020030509140b40c291541c20000044106d41040d40c40340e1200d50702d107400405440041c01184070300030001c2895044125601c55134002e04c002d010300c3d9034a110f4035041340f2041b030b4000d601c04401d1002c150701c0545c1000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 790713732 1250 790712482 790712519
    0x909040503040f0b030a1b2f070915051c08070318030305030603062505090118151101060303201501080102031911090402071b03060209010813020a 65
    0x80e280b030551a00c0c60602c00c081950081d143c4440c00005000c20b10400e07110b0200c20b86075040c0300c00016100c07540c0c010000c05448003004040c0f001e030341c103640564000303040d01d2003619072490444220a030f5440188020346514a20070032007040320b501c005458101140f40320200041c071142e2114022880c5d0f2902066000340805608000744200000f000c0700b1849800c40142d400390b19425107a1038000c0400d031900c0760007000b040000e87d5181c00e01c624842c00e16007075440102d21b42462a00c46100c030004840546800c0d28a05440b030100e04009410305c1b2207651201d01c0c01a5a84000b00e00301c2c800354045c281d94140c4002030001d18014408183ea0142900000100b90701c00c0584c1d40041300740d44001e112441c02c0c2c0014225941c0041407000c500100d044002002010110502c851000024002c4650169180c00e03802150000340c10020400c1000080c0c05642c0102024442704d601c9060800080d04442c2230140828160b07808900e9010070351103d0b0800c194000c0c10f0b030010383d052848654640c1200d45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 790714982 1250 790713732 790713743
    0x1006020106120b1b160c05100c050a110402070c030606170f071802070218240306010e090f0a0c0f140f010c030905030d031b0801051c1a130c0501050c03090904 70
    0x300403c4010361300d400d05e5201070700841550790b0713090034401080140b0032442c115401307021445e0408000900301041c00d282d19070b0460b816000410141c0003083c060300c00c80301d0013000031080e06d001008100131a0300071015a1803e06c58003100c11588540c0550701c80c04071911850903030000000300440002c200c0c40c03070710195000d02c0160030004c8642c0400d00c1c00c41d00d40384880640e007252007041216a41107134014013201c00e107203a50580c12400c40104e521944107001c2d002039500d40d80001034035a03104001d00410b0b42461022102c4042d03090900e040c07080002d0045c1d1072851107098000074018800100052160710080c20720020085200054918418540703007207050150211000039640d6080c0480301c00000030341c5010032031460b94400c1c3c81440d200038031040300f84031840d8018045a01c5079400003104220b030b42e4a0251802d06410110000340010000d020108051001c10422000500e8401e410b1740c031a8407810112500c42006681501031314800990581c001d211700700e21031030424401a017190080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 790716232 1250 790714982 790714987
    0x41e0507030902031b03031c1d1c050d060f030f11090106081503010e01110403022407031101090203030d0f18050606060703140d0c0906020303010302061602181006020106120b1b 78
    0x2098079400394044040c552140b1560f0314070840c0b01d400c10154120f001809c29000c0d18000000c0c240e65409160800505000c100000c20002d00040e0598400f401078144a044500c07007581e245800c0e40c100305070340411078456508001070001c504041c01c030941a10500c1c3c944107016681c0601540d11800d882110aa0640d00d4582142414000f803040e9800c018241080654660550050080c80c056001c8004891148160046440c1c3c00c4d540c03d1fa07612550600c0d15040e070540900c4494003402003404003950501002980c00468030b595130140b15200c801c120140300c0b400d1114800c3d144178008440181082d00090700180c4185408030090400700e200e402c01020f212500180e5000580200307144192665a6500e0b481450742c000815030000c1080d4802580355604640c0460603e0045007101c0343c039001c0300e1190000b19a241090143d40300320803940840c00d0b182681591007003501e144a408099480c043e008a05840445204c0100381d800c02d42d02750355926942610a050303050404d14007500e8405 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 790717482 1250 790716232 790716247
    0x30609030c1b06021e0d05070201170106120f02030403141309110a080f01080a0210300b060a0c150b100504080d210c0509041e0507030902031b0303 65
    0x81c40141260395071142d15041c440760400201901e031503202c0c0c800501035007202d28940300c0c0f60302c00584800045440e15255407603240a200503908200005140484001d020f800402c038154403840c103080d40309011905211140724017040804078402a03601030000350740604e8411404100a006040d240d5440d110742802030b42d40c00d640c800715a10348000c04452200081d05031034183d030100d1500e40141405807004c0165140c548495541c8008040003406280b55003041c4c55500d014400300e4102c8808415500c000610758104082c2c01148481c4890784a8a840c800039094100341e016541d80e078060b619020381c10300341511500840383d094018000210b1311010b00c202c19407145c2003001d001300c8041c3c03240e50300c60b0b052501c61400c1400d0340c0800d00411207448080f0b0b05001c44c1103886d200c8151701c490001a008030341681140c8620500c61401c0c0c00c5030515407901030149a07001c00700940e81c0d003100c04001a84451508074103560000c04042d42c1350f80610098a490312401110310b62912008007200d141c06007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 790718732 1250 790717482 790717493
    0x1b0b04030602090f09010501021e0102070b090a0218060d081b0a0506040c1203080a1e2405060306180a090501090606060f14030a020c120403050304080d030b0307030609030c 76
    0x125400072a0400c0e000704040030903051810240250040c200c030917007140d42c10140003d40e02c2410b41105034003000d083c4221207007801d0070b5044440071500703c2141110751510003182d60340c40303902003400c0b1b0250b803040000c1d848180600005600810300200390f0f0b8078142042d11006100d4124020360300c0030030740a1840d00d5207040d00700a2080c02c503110b400604081e2425040000d080c0c0a2030b8420761201105c1c0320340c100001c1e40040346c00d6010404c00b10006070991051145840c2101580c1c82d02c007120b00c0c081c80a100030302500743c91002500c5048403550101c7e15901804040e0009480c00358002c0721081488924950002519a0114610070005001c254580ba07840c20344415400645507d40e56500c284143c90741b08100d0142c0d0b40041c101a44024020200c0c402d0600c002025500d03050783c08034054800100900400703c60f5071402d04100d440300c1d02ca00b40103450385c0c0588114125881007030100c0d00c00a0013070156500030200107020385142481c40d2640c0000e448110380171800c03c07460050f038900254 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 790719982 1250 790718732 790718737
    0x60c0507120309030209090604020907111e0c0406090e060a0b12030301090504120f0806010516022701240e010507060203180601080f1e12070506100b0a0c1b0b 70
    0x24069690f0b40340d400d245005219010030050440c0c01960001390030031000d622644c80b4103030858039a1414400081d140403880e8109081c00d11005232020402603003050380c010020305410041012202001040c1c4c1d54551f45003201c50428136207402c2d802c104006008400d80350f0068111f17078006416240340101900c2c046095920980044d0101540c0b80240300c180580203180b4540c40b0f103070341010340c44002d071040040c00743c0600034544d40c10000c000a01c94003400302000100310807a03024041600075540c0c1c5041040710140c0c42807203055031445200000e0140ca9640e040050400007503551080a40d00140c102d41840080100e01c6c180320b410440400002d135240b00a40c425031480d0040d5481420030807034942003000691010555501410001c00c1c0c1030400b00b0a01500340c4803a21010b0b20010b109501d03401c101c854070043d070010300049000d000740200441c100f4440c004401106910780e071946904012401099070304800100102010000250400d80c410043e18842c02400302c2d503a61503070b24000a5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 790721232 1250 790719982 790720019
    0x20301140a24081b03030c2409160303050d02090a1509291b0d0206071e0c06050711031b0106141c06150603050702060a09030504060c0507 61
    0x641c0c2c2c1c1e40180b00032001d980b0040011074a100c5207800703030a00e80318038607a5484520f000c0c61890030365580c82c482c850360b0400407144103d290000b602c0c040880c0c60040c24210520807141c045403004c03100040e810100100300054400d4822030020826070130358504071203a400c00621132071450b9003007101862907915580d00400411b0070070b0b40804645c41c5110010043d0840b68044140805540c0c10078044040303d103041c5d2812012841584e4540001465138040c14020030312110343c17805246090f042c9142c0c003080070f5201d042c03641c80c1c031200aa00c154503503078100319070400d040000c0d07269080540000c4040c2c021a41141c82407034420030f005c15001d402c0d030842c0d009650b504c0c613504822401105201081c007401d802026110300c00400f5070326000c049170010007500c0040704800c07140540c9030308000701ca50141d8461b501401880c200c49407140c001400070314041d201c640c0984150000500b000a090144960055050b500e10b03080524111702270b140d1000c2403000f140c40780030304003000c01e0900c54005640c290 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 790722482 1250 790721232 790721251
    0xc0606031401140f0a0207030504050d03031d03040e06011b02031203010603060608060303070615090e0d080609101403070e0c12010b0a1b020604031401060509060a0e0c0702030114 79
    0x1041110600320300710340e03c085602c480c48185200b0071095010880c86242d1240e0720034400743e5248014641105c2c1e612890300995400380100c80d111080c15415802203a0000801032035038900501c0c180c929917039005500ca8410103406030400141c86500c201c5000c9990030b00030722400360b2045168002810704030410f15011001c0400310041044517418012180205002d090013041c90408801082e164411164090a115116000c800d40007180444200c02001c056400300121800c60f080d19840c6c00c4082019000210040301040700d619000c40344d140150b02c103403462000c45d4903020001036000b04043c50f841d418000c81400203400d0803007410143c805e658840c01560360305440e4104000116040e0401e000c42c0c40e0a22503010050b800004000c0220f05010321003d00418504c000340440c0b140340c10085c0404600c00c800e00d80840d0541151080d240111035a03003c1e5550b07002881082001031240040c00c00d004c401203a401d03c80d0200405459001900116002d40080000701c10000c0c20354683c0038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 790723732 1250 790722482 790722503
    0x1b030a0c0c050109030f02040c0e1c020915061b1221070203090a0603020d09061407120515060315041401240512060a050405070224010b190c060603 65
    0x108a40150300c0d41c06400242406210982541c450803181d0681c41e00080c0556a0f4080508180d800303901c501c464818007c2079400c0258401106da2030341a02d2200481c040d07003072035021038010010003030604507010028240c18280701c0c000802c00791038290301c21055442e002e100b031407800032043d50000303100044201e140b40c082c003e40f44681032200d03c0b00614a00071500280035481c07459481126010490761145000742c0c40c1c48204899100800d081c20b0014000340c5014480b03911190154403c41c071030905a1680d00201813241c2514094035801c5400890350150304540c4401071030031b04051038100600c51015980303542640c000c1001c44070900000e40002d002132004203d1400d001d00070b0503000c10724908115102d401d4440190050241c040940303d20160340c0700140854a4a500c00d4000304402081408241003998010303481c6d40d04020f40d14419152881000c0c44d582104d402070341240d0a000480b841d2090201c8803014902160b00301208021401a458010900c42e00964002d14041c1100c0e00c2d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 790724982 1250 790723732 790723757
    0x111010222080309060f13080703060603060f36020a090e0d0c08040e04050a051605120115060806061603030f05130c05010f170901050414031603051b030a 68
    0x42040c0707a941d109500a6008001c6541c05032101401d42d100142c107520010f4940c1c2c3c4454030f4884101039600510b080c0e00c642c84001082c0946038000004907401100c0401c1040515010a0180e44000c5460038000d030808000310700d10b030b19144440d01c0c9001d04500c00707041022a54000b0b07404503d1940f000410701d072100c40404038654180070002442001c2c2c02c2c49200c040c165a258070b0715000341d05c1664008170034140020f091001c203001c1160142c0e0f200c400d55100c0003502401e56031701003440c01401c0c000c01d1801c1201c94034842c14400c04050715091030034500042d140038400c0760040f03c000c0400c1d0304007006100b840c11080c4215529003826100e41c8010511000580340c01080b40c400a00717500c074005001c01081c0200302c1500546066034030a19241001060201c0c041e5508407010045180b184008010082061010340c407203800b60384901c1d41d1b03120456802101c140d81e401072108084803545400c1809000034099401814800d000e0031010190031001c81005085400480c0c0e40d0303020170401d58001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 790726232 1250 790724982 790725037
    0x11070f09060609061e0306050907020d031d030f0a030e0a0b04050c010518120f07030f0b0105030349020a090509010f230a150201050702032701110102 66
    0x39015100d2403500c503003e00d1034403c00500ea001c803505d10210b480e080c080740b501441c1c4a40c00050103820094100001c90409000085d50360b45001043d6000a1801038890b41900c1801600c40c8456140c80c025402c0110b40038100304550312801419040c140d6410240c201d00405120300d5000300d000c1c040d00c40d1a0701d4507080c00c44c18850807040c6107040000c00c1100042c0b002c8429807000f00b0b55070550f0401103142c2c18144141c0740c00c400041c22604c51003208070010400940040c00c8094510034030079041249d99810038142c5e030707005111807200c1104001281000a010350300d1110003e00d820442004030350005c1c00d05600d282901c0507400d08003500042c079400b040d90440c02d0000200402c0c1c60080d4217602d8500f00040c07881860084203180340428003140f40e0000014080d081e040c030300904000605036200c3c012000c0021261100c03025500b040c001401c0f00e400030003640c3c0550212081e004005004d8050a1094944110620305202c46050310040300842440908211000503030810140e40004d10f10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 790727482 1250 790726232 790726241
    0xb09060f0f040c120f1e17120f040302071d06190b0919150201051b0a09030b090313091508010e0706050313120206061c03090308030711070f09 63
    0x1400680c441c07000c00c0c40001085451003008507030030303004404085111391800d145c0d1000208800740c0840318482d40c49648066180c0d8142807030b0720407180004070100340e40341446e1034090a880c4255a07140100050500500c010310b1551103842881511101915000309404004482141c0038903c04040200241410400345400d40403240b6544100494075001d0300b548540304030710525029020b20380320094407400d45107603000508400200708806110003e070080c000d2400715142e83e443d081a02031040b14000c800100c1340402015510501f0351411034861000480014154010903c010410311042c5080c242d4400c1c041c007800100856003403080e1400c5010718850350040205d0380d1516450f9141c003240010300070202c4c0c0807401c1c050b890b5030715220080c000d0b05180340e01911240e405058200c1e90b070b40c046940d42c4a950b040310030103240b8641ca0300c2c280f10303005c6040c030050116100e980280045900e20010703551041071860320810304032464281d107041400039405841e865410100500503445039004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 790728732 1250 790727482 790727491
    0x312121e040209040618050a110a0e0408040e1503030c0f06070201020f030a051003020a0602060703110702010c0b04060f0c090f1401050a0e0604050603010b0d0624030e0a0b09060f 79
    0x4515440741429000110b2050b00903000400003652107070401001610119050384441e0408107480008550382000711908881150b042e02c10901c240c00441c41010014500d4040c03600600d00d5800c00741018080183c0c900c010741800c040c035000a003c00006d41c3c0c00c200a00e618140700001c1c14043c074480180302d00d0020301524410969006110341042e0354005801d49501071039000c03011403035840384922246103c0f02070f04041d401095001d80410300c55000504140901c0752503800704120300d2000b4190196000d2210003c0c00120200510008100d007106180d4205024040024035494507110400c01c543c000781a84001c10303042d04c01001245070074100075004228102642da9501e0441000070b1003845049100c0b41030101c000c030b20902940301c0005580180002404044c0d8958640c0700703100b4035400c80d080220b0120b0a020020404119405400d040414502c00042c0e403c0c545070b00950260030001e00000c0c061150f58490008035030794a6034140251110302c05003c550600c1e51440c29243c07030051 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 790729982 1250 790728732 790728781
    0x5062205040e0d031a151e2503030e030a0f02012f2d19030c09090f090606060e18060306180c0a0305010606030609050420031212 57
    0x407080d182400c011810709074600f81803600048a40340c040a0314010380700306000c0c039040310003140c261400b540b0130b80040456191054071000c81400c0c29603018190b10549200f421a200e0030312203460210003042c85100e06502c00e0801143c082001c0c003201d8074640281080c0000100c2144450024640a214100102403c4c0380200399411440d880120110b101c03071040d00090100003010840075104240e2001a4490921420500c101d416003120150b003084284a0b0600c1e5017401c4540d42d207020788180c500c001426180e0800c060318040c0404000c2aa0035296507449480d4802900000c1252140700c0280c040d584035000c0049100d000e10000e00720b1454018548001401880103030790300050090742c46941d80042c0b140b05103010300102e003402c01c400b0005400c4192980d003c400c0240c10740054040d50340641d420004103070340780c5942c1c0c1640c0b0180d17806840c02108649030042c120342c42200040d05000078045444000700451790100703139480b0041c40c1c011160300b01c061242c000000c0049100c400f0000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 790731232 1250 790729982 790729991
    0x2101060e090108060c16080d060e01051e240c1b090411100c02030607020708010e0c010c11150a0c120507020907030b2419180e060a0506220504 63
    0x80135134a01e03026150304814000030403000200740841c482c1a202030341c8003a642e6201c81c103404c10803020b04140d000e008c00032440500081001c0c00e08404246a0b10f036800707007244404041100303229140800d18404614101803d0010389000307000d40040c04081a2000100b800840d0982400d503859200c684041c8602c03218424040072908841048000d034804039040d80c0081c220303040a8401c51284640250180102010004020b03008940841120b03030010081c4152025900087d0f200e1009030482c1d0301050351445503001049010040711848003000e8503001031079803802c0d2240c1542c0c004600e176800107a4400d0000c410040408404601111075080c52070603e21294001a0180c00003400901095514024240d2659403601030405c21010f00c030f4080c05001c50317214a9029944920306044413420007045000728188038040f80408100b80280340000f8070300b01541a40d14420160041d03601464000c8003188a54400c0000c04815115903d501114020f03011124550145a4401413289161 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 790732482 1250 790731232 790731239
    0x121609080303041101120f053c0a020409050c0a0311070b060d05120a050a1701151107050a090b03010507172205190b15010f050c032101060e0901 64
    0x8292508540e0001c801340c60b01386200d0049070444e44680d00d1070359590030110080304124607640030b240610082003d0182d448200c00c2d40407101e45c2c80700241d00e03440184c48403021074005d032864410f400c00384101c000b5141c01d5648a40f5001c0c0d8034183d80202e403000c0c0000b06800380c01e17051b00c030300f038890100c20300c07846c0c00d04100b070f00e82036403c1720014040c2c0d014000140303060701002410301c4400945460300e0b00c80342d00c581c0c204d032000302160040c1d47c05c00c01027a070401d5031103a1711641010490485100c1400e490782c49007104011140055051002203091054403c0070446507075801d6000080c11541c0400180c0b0240c0d14101801e588002e8419814000b407210b03450302060380200d65a43c00080c100c3d050001e030140c5003245000e0201480c2c00b40550045141c01d100120b0003400c04131503140640d1155009844042c1d600444842424420340841c1c00052030710089030185020301502c40020f0300303480c14005410450440c2148402202201d02c0144005214003600b2451200d88442c094941c0d00c00e0750305 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 790733732 1250 790732482 790732499
    0x71107090b040212010e1b0309030405040b120d0f03050a0b0d030509011809050a0c0f1d0d21020118080f070c051504140d0305070f0c0b121609 63
    0x285401848442600d0300d01000303054880e03030125130601e01c815118a030700f580d407940080842882903404580903040d0703140c01605942c004080c0da010701003440282d8502454201088000c2c01c0411055801c01a28905071070710302c0c401d000f092105c00c695100c0c00d52803094248024102d403401440001150301e48041030a003502d40342610700171903038581066031b611103402d801690280e1000103071101e4241d00c4003000c200740d2025007225010f035615140074881d400c2c1081040c0c03030b40e00c7c3c400d840c000058813148a80c0c850b80020051b80c0c0c2c0004014042c103031804099210071210b1005580c0e6184000c60301d0a100201940c24807844a088001e0082680b4040321584d4240592203003180068000c03202080d84000c1c4180c081500004010062a0020b1040400300c00400c0d0341080c0702d043c1684c00c0719140100341d0f050104c1c0c001c00300c03a41692010b142c80f0041c2c0d03c400038194019025200350307001c03120200d8442c1a6a0003010883c0151500510b5840c04180a02640d20304484c00d60421a031900c08001100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 790734982 1250 790733732 790733743
    0x3070e1c03080405070b0c0a02030f0a0b070c06090b01080c19050f090c09031f0c090b04091503050f070306050c1306081f0312200d0509030a06021b060711 68
    0x1a8185409207041e03d813420224030b004010707008141800e40003d900003d81c0d10001c1d149021038425802d603081001071782c0309152140407031007010700000403440000d040a84035184c200c4141d0300c80c950000d141420b41d221244000d038241c20030b00c429807040611034040c0c50210f80b07941141a0521541ca18641404045401c0c604151042402000303040c1c04540c00d05641e0050343c888100103000c6860481045200c01001c1c0c0e050f80d034450040d03240020038403903180b1620b048010f032404501490314107490005440010808400d0050341600a42030220000750140f150018500b4860024121079080d4282a001c40e18007803d85416004200008101c44010040304011110581002059a59003070781910308041c1b002d40c0c4c8400c00d4140c030004010070000d400c040c3d00780c541c260f42d078500511407043c08071917041440721455602c1c1d002803444003e441c07156008042011020b402d940034401c0302e85e00c401c10398202c1c050901f40f4500d040301c1e81242d8142001b4455218440e4500058402c2e5807040e61921070307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 790736232 1250 790734982 790735039
    0x50a0c060315062c031207020907020d090303110a06141801021206120f0f070609051e040c0201140112030e060307050706050c0f1804230a0504030c05100203070e 71
    0x4e4030004518108448a10602d13000214080c06403140c21002e5080d0040e00d034808582244910001004201c14074400500c6440d40d040ca6100e07842510b0035518242d0300d603401c100c08405103224884511000801500402c2c0009003403a002001500b0102a03d82d140e444e0a000345006a2044c40b4044003040c0c444101600948180e941050940c135031101241801c0a664049165100d0b01012510314040041c00b001169001d5031480380c6d26440d0010460300008581c08907010030070341041c8029a00e40f50b032200d00c01840600000400c91a4011120082c9600b6403001003076040214900040c15000215113520301000c40d80c0700d240d8034040e41c000e80702c0d01030b0f181d0245c1091342e00c42c00a407818030700100701c03041602c40d90007150319460000c0007440e0390003400001c0c40c083c40c240b901c40c042c41050380349000c3ca86808442c02c010705945600d418002042c00400640400ca801203c5c0c4c004a42c050141e4800004004400b59a900d4007400c0940f0345404100702c2c1d805034030751206080c04403104048040f00c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 790737482 1250 790736232 790736267
    0x82106031c02071a0f0403030f0f0305010501024c0b040b180c07150c031406032509021b07050d020a03080d09140c15040e13080403050a0c06031506 65
    0x40c0300e007042134034600d01607800218002600040d01106140e0800365020202c10990f0f245c0c500c504410b01c00314190f038000c0c07050a0240e404081e01324074003280c2050b040d0700c194107000c07960994401d50a0502000d00000700e17484006250414011207845140604085070341d06650a2000b0310303400303001c107a25110f920004c20b1040030038030111b032100f2140302c101c0b44595007000c9050745500c0413038100b8008262002160012910384025a0000300100400303e10070700d00100540000341e0742906403852030441b00c5100500103190040030868030841c2c4050aa400032000768a402c1d0001041420f240c08000c4c2c018510410030b0303854910050382c0f500c0980d025240d014000ea42c440401c0082800030b010900401820f00e10701141007900c03404002402038004c081183c400050000d101c0402c0c81a110b1030050001c420703161000190090040255001103d03c190819480d10f43e4a444290500400e550125a01c80346000c1c20810594540500807844080030304529020f45025409040f2003121103030f61a8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 790738732 1250 790737482 790737509
    0x216171014190b130e100614060c01060b0706051f05030a120309022d0f0d03030e0703060c050306100f0c02041508120702211207082106031c0207 64
    0x501c0300140c2011080500142c0f44891112000740c4100240000c00d0b0304102c580718882041821b03050500a41040754030221780682d1910560051040542c00b00d18412500e40d2603880000b003540144004005480c01034000054a0502c40c400d0542105030158004806164110a03c00c3d0795010801401c4e150307111065441510800c142074018000e0326201079800b1540500607111000e10403800419154401c4140c0341240a500400013900d0100a100c0e0b00801c0d8082502c000078001d0740902c0c8402501000c45089030f58030764070b00050366665424003000801c0403041c88020308000c4160321543c0f106013404514000b400f60011b28845002c0301c06442540c4404520a000d580104c507040942000e40c04d9600c8a502001350000c0b0b6400528201d0068003040e48202d0600201c8510b00c0c140c1044401816910226030740400190f004100306980c140c2040107401d0080d2543d84911901080340070000a07189007a03020507080044100819109901400c0187c07c4c031903001c1a83e40559070704854115 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 790739982 1250 790738732 790738771
    0x20c01060f062c06030414070801060b030f06030705030f030a09050105070302060420280b04050d0f03020c090411010806090c040b0715020a05040f0504110304060902010216171014 79
    0x2a491810328001680004c0c000080c04240070402000a4400703400b00c08503040190307202c11540c01c803041da202e15280050705001059010011101c4550004801011036074034070784410000307080c2140920308413001d07070000a1a04803030390888036035401401d003400c0ca1810007140c0d8a0194845100900040801c1c1442040841001d02140c0c0c0b01e222120291807295a440d800780c0000102c60301c603c10030000740c0c01d040d0008101c42041d0803a01078070700141c440c81d0b03034141c1c6966010765a002c82c0c10403015406400d070010000e8440c09009482140100cad190804248a1000175011400241c540c0d40104006420071800d00c00c22011101107801c1003040c42e54605450400d002c14880503001110410b0002074140d56003a80100a070060780c0004d0550443c15642c2d000300001c850108034200d200303c0090002074003050385540110000790060058445450b5680071015070003001d504420b001c0c80346c0f0b880b0846003e404101000d590315180301c0400402038141c0c52a9684e80300102000c08080040c1f4484 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 790741232 1250 790739982 790740047
    0x6100c060603170a09121a091207062f2208010501030507080d0e0a050f010509040c020601081212010e07090902041202011b02012f0709020c01060f06 66
    0x8015074201c0041101204001d040f044160320094098000420100001c40c0c2e801800c08142083d9510035100c2c01b40400c0c00628942c0010002d0030204035009001b0844a0354845030014203040340304100010b0b40040d542d5055011941c844002100700031001c3c46042c034506c2c400104c4d4440c843c209500c0300c00c40010000c0c50030b40300c081e803c82c00705d07942840000000c0100000b00700c82030790003050584080701e00710360f408c0361140458920980e11801d41c0904000b10308000311003a160100600d0305a02e404401c0001c02c0546038401c0842c40141e2041c1c00410140000b400000c94541146000a103404246e40c8030403905c05040c015012611182400328102601a040c40401411420400e5413159a00e0342400d1583c1281942a4080307001c00b2591098070860f10001c078076555050b19042499803c0000d400c60b84640c00d80302e54480c80d8007891040754160204034000040c900d106015960b4441c002141e030940b0b4040d4000008501442c00c144038450304000300c03151181500004c6098042c045014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 790742482 1250 790741232 790741241
    0x13060f110714061b0f0d0f02130e18100f0212010e0702070e1e0a0e0f060a18020109090203070c120816020607021e0c150c0c040506100c06 61
    0x45604400010a24100081408074800003002182a0303900b80c0d61340403010584110103160001020020000030005a8041000d031007014000c490000d4070340b8101c1c200320200c0e40001d4144500001460f810846900e11044540c2c1c880d0381080c13542514404141c14680e034412121281c0c03541ca4991440b940b1001e4158107460b605154191011004c0d650340182c4510741c80301f5107400005015145001c13a5404030650400d01500c40903104176815524501544101d0368050714180d80203860302c0389000e1441e801c02150300f11380f04a901500c5203040c1403038210708490400140c4170616103130500e030300c1c0980e070014558001c0b10000c900c0075a50b40d40e002021a4110343d600d03001018103401502d500304155111030700c2c600c00e844000706e0f00303480445c3c600c1c1a41d440d40d00b1680000164040070015110740d103448081e2482f2202c10045840c401d20542c00201c08101d00107200c2440003001c12100c2040b5420040c0f01d03082c0c03030f0503a81081541040c0d000714512805501c2032a007485183c4800500308074550f0711 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 790743732 1250 790742482 790742501
    0x111090603060612040f14030f160510060b040609090e1906090f061a03012009040608010507020a1506080a0b06060d111902010e150702151504050703020313060f 71
    0x4140756140901c6c00004c00c0c848510181c6109000d400c1144110310700004455201c0726040c42242049401c03040a0400000180c04541b240240340003211800d01070b0103000d01030003e499070b281c3c4032400d00c1e50042c0004515840ba90005052050307103103030f800d40490b00c070b81c00b074809a030b0041c08004c49003403440240c0720309540107285294890481040c05421360181aa030785941114501c140c2000007010300740c070000e0304200c903011328241020090444040c01042c0d0a00045c02c04140c07550f8501801d401c54508607408405a041010f03003e0400200e1080b20205030981c02d000c000036418003144c1d46e82c1e1501d003100101b0014803a0082034540d9910425207001c0b061141c000d00c8500501001c1d0b10094100290354a0281e200081103146140107009200c1c60600382801065090716040d2403262020014000f0025030085c00070034281c07006418800ba1183c610103500354281c840d500184030884000418a9007014410310501c444910141d084007400350308544086800006c1d030310f86c0c2c0024000502c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 790744982 1250 790743732 790743757
    0x10207030f111509090601210207050616020f030d150306020304050d180b0711060405090906090d2f010204090618140f0c0c0705120109050601050301110906030606 72
    0x20820701000380144200c58030500948420710000100300941802e400303002006503001e84000300084203544a420607411105c00461103030340342d43c1480e492104076800041d054510390801810804148003054110040e21214070040c8485c0312044c0305603844c0d010b40c041e017010b00d0343c076a500c0b560500c0340c20401c60f002c5c6800080840d031780d0401e0b24045542d2018911001d000c18010b004170611204070007c00c500700c421580c0706600d00b003060303a07440c03826121004045074007420a01000c0b88a8554000484c82025150010300341c82c01c02903001032030300d210034006604000780b0110500307010a001e04450792030b80b8003500301d1a01c9060355481c1c50290080340c04c09008140742400005441000f00a0b540360018410340401c030600e20314240461241d0f04880390200d200062002c20318042c001002003170501c40680c2a44c882c1500c3c4c00000700400b440e02c0c0c44a92580d120510342003484820701c401030041400301d0003041140c000300c201c031040c2d01803582c0c4a0b200703c4c00440001c44544465044171028240c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 790746232 1250 790744982 790745003
    0x5070c080a02030c0106140d03050d0212071d030115030f02150313060b0d0c0314011530030806040e010b030f07061e0c020f060d0f050604151a030601020703 69
    0x51000a60f2a004145158010760030710100045d01e03070305009080100e50b4050450840050b1035203041e2070640c0320341e0f07410120a900b0400e15003a0001c880400303019004a81da0050644151000c0c00954030000c0d1800303119902d4903041c0120000240300d0302040702d80c4400707554520780e10b500028001010403494600104000803c00c2640c6400410f669080e41c03090000704101c016000a11204540c011002004c040c4a10002e20110755030207420024240e01500204811142e40a2424209580d9000010b1300c0744210a1090754502a212060800c0082440024921441d1001043e0320001340c0f005000b0343c1c4e15025184040c402303421031242550081c049070629911205450780c1c41110b8841c04001601010304400118040e0b0040850120240d5480003031010b00d03000c1050304e1405056956012204214041c058021402140505081000005900d2514405100c2070b14026829502e00005600c814006c5040342c02d95118024003144007103850b0790324240187c0ca000381a40001c4c2100298 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 790747482 1250 790746232 790746247
    0xb0106030b011209110d170a050405040e0109050c012f1510140f010314040b01030204051b07110102010b090f090c0901031211010209040207051e0604080a0305070c08 73
    0x3580120521080c280e8074010001400d55892044a1030b41c40001c20f50740d40e031515840740303103020241c3e1140319024a070700300c5011710020005001503004000c0ca801154010030304010914062080c440010480c0740244019281540d45540711007564900a041c40b4004124800700000c0000f2460341e03070b186209120281040311841ea0355000401c40f02c0a52003a55400600d0140202d20054112503d520304522203010310410410100720003101141015a00c031407900034081d25a8070140114013a61025800d541540140000d80303c005004122084801200e04010034002007150071140d0807041c9107041000c280f00407030140c00820200c88d80704603150103014800301a000610302a8244001b00d43c0116420f105200d201002444041c0010910390078a42c8a180102e030580307994560a40018908081d1100040498000c404196074980c48005080118401c03a150502910129401031000d46030903031743d0108510070150340c0001c06485501156200d80100340101034580e0000c00300303881c0e200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 790748732 1250 790747482 790747487
    0xd02030301140402070302060f0408130e0a110406020d0806030115030503180d0c0605130e240d1112030403061d06060a081b0d0c030c08070b031509070c0b0106 70
    0x10070b0041c1c02600384185400d030840d00c0c20344201d82c005036154018100540d42d0b120a0300300290001c10542d0040030801c0001c640805850f01074010f01344024014600303003003407000c0300d04513030242d018841e803003104000501015800080783c0c040d070200c61410048540c1c50741d0129015003128003a00010000150001c020020084040c0507080d05020341120002e462408221854540781c50207003d543c150784040c801d1a00c181c00400207140a8200403108580e12156880d2100707003142c4884409041100300d490301108128601c2840804603000c080c044010f48401e40800643c0340c00c140705180324074200700d03110814403d640042d42c008101b08541c0a0400b1100c02e41e5020307043e20721850260800241061a10400010680d103900c401004001282c0d42a698090302c890324859001c0000e420810000d000007070032001642c428480701d6007507031401c841507280c41695000201c014006000300f20384d0f9000902da10400800032241c261a83c0c40e0000700340c401c013840d40e038082c0030110360134008201c1d140c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 790749982 1250 790748732 790748737
    0x903030a051e13060e030f0a080c0d08100603090c030b070801030b0a05150f0a0f3f060b01030b04021305090705090d0b07020f0607020d09120b06041d0d0203 69
    0x40c6140d0001d0b910080b400d004414815400c0c100d040e508290750a12040e03200301701c200020315000d001c8039500a01d59100714900040307407004582c2c241c00007070701d8029101d0500500b1100075043c00c00c4959402c01200442d020340c00c80c02130404140c0c1d90116442070200c0e068030380c1c000b160030192a4229042250300188000b40c01d000a403004075440c8080b440310fa245200313040c419105440d001018050328010080745414804007070b81e00c0081fa0170040b5445074541100001401c800c070088441d5003085c1001200c00d9030300c00f0141e4424000030141820f401003c402c142ea1554400c5000404104a000581c0140000c21050b0713000b62011a107035031500303901000d80c011b8503402c903080c0e4001d42d5040001c8071144141c8460700d4200d500ca003031001c00079058404c01c40d00804a0300549190181b6585018070300702c800c580706070050340030b4000c00c004203030080c18807009030800100051441c481e5455100750750340f000c0c15180c0100d85c0ca191400600a0000380440ca05200e00152404036050340d2000f55030343c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 790751232 1250 790749982 790749997
    0x2206020607031104080d1d030d1101051803161e0303020c070510091e0504020c0a060c0f1d010c1b031109060a0b0706020c031b0c151804020903030a05 66
    0x24500f10504000c6015082610300700c80c0994010208500b08680440744608010072100c1840150b83d000c001a940a01844440c20903d9440c2990403000304405825a04094050346102203002d034100c000f544040f0855080d40c00000c085415030802e4038240980701c41c802c4102c2d4004002d02075038020144d054000306134000c1c5010407030701050744031740c00c021000f96140c018901068104038104401c0c03d00000000307403108501c04c0500d240d0ba80c1c0300800c099a02902802c80c607600000c0e2940308100181c428055030720568a0b000c400b4554040018002c6064404a0342c04510910100c00440e8450030a801d00b40c0d41c4010248000303911680f281403568060b0004442c200344001040381035007405142c440c401c40004040d031000070301d00311180980340d204c1c2000b5a20709400300607580c480c2208100a0003004d02101034695500040380780241441c401c2072985102e83c80c001d0044483c000c001c0140d407202808404040380503901100010003c0c450700c0001c035014040071400f21456900003001e8400c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 790752482 1250 790751232 790751237
    0x15060f0303120c0e010c0f0204060b09120a031b1e06020d0f020313080f040320090105011b03030509030d0603050c3d17040507051c020904082206020607 67
    0x10b140404024291007488640c6000940402d03050352066110312000c0c00814018209260040c51980208041d50310075041074842e00d01c0002c8044c01424502038001050740c1102c09050562015036008008840c400041001c5e10380d55050750040c804550441c94801c0c000d00c06580c04c101031850640042d40020719000040c1d841c06010640f000c140e802102d01c190705500e803c20f040f0711300c5d0340c03003440d40d030000407a1080c0704c08288030200c0068a050180c004080c00074410405800308034003086140c441c160095410880078030307505603039a00c05a403400b16459040c200400c055440c0440f06155003e5410948501414504008103006010441104040303065072a11040e43c6091001c040050750b8007400e00c000da031014810025810304030303d441c0e6184564030300590601c907800c0c0003620615058030107840ea80c100040c200325a241100140e042400f4190070034111100c250006904810001d00203400c001e03002408450240030180008140e04040001c11085500c400000b9070780d0748101c410501 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 790753732 1250 790752482 790752497
    0x50906061504090507090e04080d1808072003010f0609110405130e0a0c090c0207050108100603020f0903071203080108011116151802010905090402010c030c15060f0303 74
    0xc00d030501d06014004503418560350340c079251902e400070004201c000d0400c003c1001400e40810030309107403002d41d0b018a010f0b40035140c650925034414400c9550ba4a000c01c131101c80343d828a000200c2e214103944800d50007940e00011480300d9003400b00b0203800d00c00480d9043d403030f10081540110070382c1d10034015603098640c100100909042401c125100e58000d881d44000c1361840c04c040504560001a041800340f0242d8103290695921000c0d440c007030b41c0180e81c40540320460000719079410410000203200901c1d00c2e20403410010718615005100b8044d00b42010f40010f1006c01820810707003115114140034086410440d40c6410004246056590480005060200008440c80c1c140140300c8040b8441d100c1510b0b00b110b03c510281681100c0408032581100541a00100301083c0303d880901d6030859a400d2030b148082c0300040003050103030030181c400d2a0040510001d40d9105104000c41c59250170111285440c40c00d0032100d00d0110342009041e04c3c20314601040044016140c14101c0b44aa00d5464 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 790754982 1250 790753732 790753741
    0x23030301060c050105180604080a0c080f220609120204060e0a05090d08061318020301050a0501140d0b070f0c140a12080603120306010908010608330a020702130e01050906 75
    0x91000909661110640c0c01f200104002c9010907004101d4042d01e806c240c0380c1e5810564842d1400c6e0840c00c1602d100d414003217041101c540380c0c00e103000000e0b0340c040d2690f2607450030b00c5005000308545001d200c900901c51120401151500e900941c00f40280240308a0149041c19021020b03201c11035506003d40038000d824282d003401a54031501032071000b0148000c5001000f01c0034020490784c2011124030309144848070140e1400c0c8189400345500c04008a500c0d814108803c00000340c01d4215070291030272182a60200741d286004c00c1d01300700103203468030490a076603604030381d03107580002d0160007a80c500c49104004480003a00240c0c0c03502c5880b903102c0550a100003076801d81c400b2070b071180e0560001030030811040310f510000d43d4000414100900e0a5459032621400c50320030381c05c4040300794450076030442d6500b041000c0749220700314050212384480318103905000103136000d01114501b0350007248a0f421595403100c2c6100c01c0140c0c5400f0803030780780f450210601901064609116902078a000b09 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 790756232 1250 790754982 790755001
    0x3041e05030c0d2f04090506060103180f1214040602010902090601050313060506120d0914040204030804090509030715050f2229041208101223030301060c050105 71
    0x1c2c1d0030b50300208002075810403150710b913005450710380c680500c07501c2c1c4056211450760740d4860301c00c0700c1c0d0180c4001d001c1ca2500e24000f41c12590a55180c1002d0811041c050001402c040225400300d0381c080090112030400c20070036103614130401d03419a01218042000300708558154454a403e90003120f01c03540f1902c0da1001912640b0050b1f03040100f00840b00c14520116585401c402e8010f14054800703091062540c608030f0034225442ca0f607100007800302c1410410703201d000c1242e0040c3e01c01143d0452900d45150744001d50352003544214080140c443c800503103c80014800d407a14190091281c203408240c10607050010242103410800b0703000c50b5004200c4500c100b2910116940c503803130759a00034810a0310703007590400f01c580c11704001c40c44003189c030603101c81c0019681c0c3c00340b03214480075000c09041244c003a017220001030801006c1d01030a0401c11410742801000a80560000c200c5800c040c1e0099100f0b500c2c210031016004d551000100010740130340e00481c3e40c3c00682c0900000c00040d1240d0302c00d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 790757482 1250 790756232 790756249
    0x180f05070e1303080703050105150702370504140f090a0602030406050a0c1103030106051e0d09051506031c02010e0d180e06030a1e120305071209050a0303020c03041e05030c 76
    0x18660000781e0002c0c00000ac0c40904000c110242c001003c0c0c198425251049403100307040c080044401000045514108400380039801d0f02500f8115820f00200010184081500c071008101d92402d804030b00c00302d0040e18007400b100445513000b15040d584c2e86400e0410382c01030710040c0d81c1c0b81c0b04140307000c254440c02403107020104084101c00c2d0103545582d00c0c0a00440e0307241c0007001c840031954240c400003419802000c000f80000514200041151500c90030310a003001000b2010221300811340c4100401a900468421196013520403081400585840104c0c01801c01d40c260b40310901c80c440d4a8958103401031103001e1003c43e10501c030030700f1540ba103010a0700740e10242c0340b017900b5600403504032000501c51f00142022514040701014003400d0b68940b049210034111400001c00d544205002da030640c0100041001c401d8080b09101d0400c40f66502903446100328400703810035501207241080c2e624184220703002440c0100a1228244280e840c1d116605c0031841401e00c40d01c51055440c0035424075602 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 790758732 1250 790757482 790757489
    0x16050706171b0c0102090310230c090108070c02121e031201150c0b040f06060509040b06040c03020d11091206010602030316020a0215120604180f05070e13030807030501 74
    0xa81d54840c944841482480d030810305124001e1354091050781004d84080015510100340150045006401c521210f1045440b0701c3e05c405040070030004008008603044e0489090700401e01c0c02c80310030760b90070b13400b1100304c2d0582c2c00c000d51101d80150f1344403000c0e0000800a000010409452141038904641c0036520301c520303e404046002488010481c1c0740d103c1c90f82070380c16103850603c1408203405641e001c40b0003204031412507155261110300401d01140344201c4018140c1a120402a420142c031345910301c00c03008005610842d210780e288420588290150b86103082442c0041c0144929240c01e410384d5004003031064004c2d00f070041501c0300c40c00b00007001c3d070489440c0e070095840e40d01c0e02c10707078040800b03001b44103203040d803044280300c130016129a40455041080c1005046c3c840d0544c002c3d80301c8008024203441e1040d800d01c100d00d054125250545040c3c1584602e0700c8240305094544541001402d40c04200030303110742070412203e00c0c5c2015001418030b121342c0c1c81074459615610140e003220402e00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 790759982 1250 790758732 790758751
    0x130204060339030b061c0308160e0f0402090d02030105010b070506060405070c120201020c0d0816080f0601110a0209090307030f03110f0705010b0a0b3604111605070617 74
    0x500070030210b03c90715804d60b00200702130400f55404545044205400300100f40c202c002a110306c0401880d5042003102c8540d01e642ca01e451401c14548a0008121400c21700c07a040c1f1984e40000c0907030312a5034a80c1e081c41d03040e6000d40240321540e075491f01044c00d070b0022082607400d40641030006200385041e1284600c28807040e12030a00506894940701c040748450b0b212201959400c0143c0c4050510030040070b04484215a56900c19140006584440400302e0050344140042035040c804917001c14090907910500a103002000003480004070781c5401c560090294015441d4000c0c0b00301140044018040503000c2d450f44000c8080c044003c60441d0300040703404484120a000d04605070b00c07101c006220b80340c0644008100580440300007810b516280e8017100388490001081c0c01491001d03509840710f050301c1245500c40c4002a01301e903840400400d0b401c1d02c2183e4a8034206070419503507003610b50700713100c4140385403c400c00d42c9401c42e902e134518050000841c0d202824008600d4441505070b126035802d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 790761232 1250 790759982 790760093
    0x1f09050d050307050f04031101090504050708180a020a0b070c0506030c0a121d0601030312020c0601090b060f0412061b1e030b130617010903171302040603 68
    0x399000c403001c2d003001d0031030400c100c030030072060400d000b01d10b000e0809140204203440b4071307a4400c3e0014104c1032855019500640c18502040030054015055540c0480d0300780083d000c500382c0c0e941c010b0405001d120000d61003401e000d008603001000c2d401800b1080d224075400e80f0b6550304d1320304001e000d0004a40e00d640380c035002c004206446102d181e42100d16400040c010039414103201c00070300c03191081807034041d039644054010000d00d40c0c00050040c032415554001c5141407202c2021584035281401810019500c2c1ca0310f5903026201d69040703455000c4442c500d1a11340d0740316222000f1035541a9800e84001e42043c003a00509816043d007007444142948418024010140d81c403c03070b0051401350740d020306941d0000703c616030311112599504010388042c0002d4407400c2850918103201518240c0c005a81f50a030081c00080d040302815510540a240c1912155600616001e82c192500c900940084c01d0420010401954516402d50b00041300e10001f0490745144102c00120480c448030300803c00034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 790762482 1250 790761232 790761253
    0x1020c030a18030b070c1109010609060c1b080307050c060a0503061210110a02010609050f01030209090723041a0901050f010504090e0f07061107150e040c021f0905 72
    0x3425000e0384161014900b4503a65650761100146808101e0f02d02000c503040c81d03007880810440200e104030035a002c9072040c180b0350424800070503080d0103004480034064400c406100b03100104801105c1d5584034a50386c10b4064540000c00d84980240382c04541c03a2160340350001c1d5910b88501130741c04090715503486900755522102007094891801145115034000e51815407079920490250110820044040f40d07980e00040f540242143c41c01d601c850801031405043c441c6100100c0e071590f04480e01165061055104d1b45043d40c1031101540c8011100c0c41750705025002d1051800c1c000012600c111401c010344c2600e80342d511040038800350000e5101c000840184003600d861501b11a10800c180b40031410b2a48580c0101c0858400703070360300e00c5140e000b644100711490007045418060881032610040603e4011700b03480c0d85905c03a0103a201074000c80d135a56003101c6d01c0348580e4511500020b1082c80030a24440b4040d486070034a460070801a007400e01c602040b1482c9006d101c2003264420b00800c0382001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 790763732 1250 790762482 790762487
    0x30d0f2c010507110d0804050a09020304021e19030302150121230604062f0702060d0b030313030c0906081002090303121815090d081015021e01020c030a 67
    0x8100750840d0404d101c81c1c00e90095031216040110b055220300d095661355030404040100201159006400003401001040b005803182040002c0b902a450040b070740100600300020101c10311140f04080010f403850001082c1980018103000340104503002e20416601c401c4c90b8018040c1d1414103c2c100d402d8200e02200040903d0858460303203001c211014840b844512400f4240803081e01c0a0300c2054451141469030300c03007034068811081d09124410110b6402d0000440306019084c0302a100b100041100f0403075440680210001074001400c2e250789070000701100d404415030740810340e08507110905c00b01d619210b41c4500400d03128075100902079000c2c118100c1019500508850783c060105100385100d00c0c1d0702c47c0c0c0d024002c810a44069a4100044404a140c4441c0c1942120142869009d10404420101d00205000114074201e1f581c0e590301d034003600300088140d10071102b224200c84a00c1100b40d0210b81e003d80e0355211000d0510441001c42031038240d00500f452400ca5400800c0162082070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 790764982 1250 790763732 790763737
    0x6020a0f2a0302030d020a0e1921170f030403170c0708071a090703051216020d02031e031201050a081f09061d0105250f0509030d0f2c0105 61
    0xb4071900c122440c003810034008030180c0e04814418004a5107680c0721b80403915100c3c500b0000c5500711008100c80b0740ca400c03006e07004a51405105248001d5803c4048140240c0d0a031683d00c0c00450007803a60741d1440b50294a14a500454007500041c0c140207400647d41c20020210b40101500c4840a0500d08503449115981d402100300315559103407100c01c1d83c01e60b21420400e92250342c40b000500000381c0786041440c107010b0b108440c561407107420003981903512010908504090380684520a241c81c09101180c0742c215000b6582500281c48080c0d041401000801041e007043d500c1940b65990364fc031810301c14516080c1c040c0548030b4000c1140845504c01020001c8100d2945a40c0890040002d8031104e04407000c0c4001401c141c1c150340d112514a1109001d01604528504461308221700d50580c080d542d40a4441e000f820022503000d000c0c07206200b24142c1c0ea403800b009040d501054814140500b50a0880641001013001600c858450901c20a882c140300503030042004150002d03100112000d6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 790766232 1250 790764982 790765067
    0xe030114010e0108070b0405090c0d0e1e070e0f04030305130b07120b0f010c110103021b15130305041e090207060c0219020d020d030e0d06020a0f 64
    0x540d40e65090052500c0650140c81c028548046084000e50604c4061801c0c00116000200c0c4804104403c21a54450405035a40b0003a141c4e20503032540110701e074501c00b400d040314078000c3c10301c0f5a48104a02a0040ea01c1206003c040d00c100d0308800e0751240c0100c0340002c100e1310440792151070030000b8003103404bd801c290752110185e00c0500c481261940da50034400810345071100010340a10106c0b031020242d11aa480c0d0020490b0200324100803040002e040b40c4c0c43e0100180f4030200070300c0301310b0703264040d4050300c0c4a900e1034450625240c07040841907a48804046955080c03400801c040360020041d104501e500c5501650b50310324082c00e02c2002495112458464004c140c02000c0c0040e44c80140d01c0a0403556114103070118501c1000d68000349050f42e840005032024145c03213003450040c0d4a100d0024986981510b58000e0a207003400c0c151000060424459000345c0a030840c0c0b000c0160a0b8020441e5040039151000014240711040b1100c481c0e007500341c404180702690400c01c0d0031050844200d034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 790767482 1250 790766232 790766239
    0x41205160e0604050a1a1318030e1306051804020303040b2107091214030906040f09050112080406200d021b0909071502030706140601110c010801060e 66
    0x95958040320045026501c00450090980c0c00d0052600e0140500f6402a5428070f09100760b05154050030781c0d40d800e4061061044084019071400b1048030f8110b01d8416544d180d00041103900e50401502203001c0c05402c80c420040000d600c60500c52510901043d11805031003455540145c1515554140c0c01030300680c0d251100303020005160400b80000c081d00c02a2811510400140052002400740701500440501c0704005007405102c1180e180341c3c1056070412103a51460440f075a070a8210700ca10b5454a401100018011038030902c01c100241c112004580204020381e40e4017400210750807103220050000c40d04201c200506441098040400050180c109810303240007100207207082c40c20038140380560480c2c603803031030891900aa40c0b0f021400c00d4501c20708a01d00200c0d603907220561070080e02e00c031484030401c40703566034420400e80d546203038040410003210034215481d10703003035000700c5015000580c0c07042c0c000b240800101322b01c0340d03025040c0c482120b140d007001d6041d900a041012078070b41 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 790768732 1250 790767482 790767493
    0x80c130216080405030f0609030d0213030c060f090b0a050f0c0c040504050c040b041103070f020f0708060f061c03030c0509040f0515010215040f140303070906090f0b041205 76
    0x19210151400c030841d80b445014110303a110b18001c103041c141811000d12a03c0c58000d80d0030081030750008800c80329520b50035040140c1c2c2e0103204d07a1004891800384c002601c080d40c648804540720380c00c00d81059240103561a4002c040350b4610000c0a0762161200341000070b00b081c0000124141240044c140041040b0141e40c4021100004601228401c48054455a10071500d460690810744101d07080301c201030b141400301d8241e071007803d0f64510000c0d09001c02c004e96602c07454542407080c000a094002240c06880582d65190322903035440c1000e40c1d080384480e0140c070201e4514544141329031590b103240e0880d10711000142e201130303004003a0702603000b0a06c10200311141e9180d03a5440303101c45628858100050340c0c2170904840c2e1000922108042c107551050503c0f01d003201a041400d50300c141e00c030301c031003000400c54500196441c0d000910501c45110200a01c02120341001040e030075100907a981c51b200d21303568036054500c2e640620407440600c504200c1400022100c8a0741420617015608944 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 790769982 1250 790768732 790768747
    0x1401200109050703061a01090512150a02040e1e16030e0a030206010e060901050d0605130c091b050a0e01050306040b10050301090f0902060a0804050c030f0a06060f080c1302 76
    0x103003981c0c03a80358100c4494212101c14010025607100c1c096841e0510401c0313401c07016140002900785075907801000c1c07040301d050507242c0080404016603141850102d6000d442d6040100240d006504030303014440d136800103c0d000400c0036498140c00700c1c0740803e26541020585440c40304200805907800403e0030180c66410f4400c503120200502c0100b1486a402080d4030740c90100503100880d0054455440f9500d00401008079036100752003500389130b402c1500003039661039411015002c03040d20a4000c0a41496110010300f140840d804070f51000c06d03110501c0b408141c01da0b01180d20703214203403180000ca269402002e20551190000c0e590042c00500001115050400040c1400284080000000d4030000040c001134139580200890580d210704240f0403d5041d5000586d540038401008081182c0f000024052010812080c620007401070306560617240c03071240da1a02d40810030f41c2a12a41d041510018080c019100590200c2d0810009005040403400804c034501d6000402c20740100c4d024410030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 790771232 1250 790769982 790770047
    0x2030c0706020d0b150a03050108030c330a0506030d0206270a02181006021605010f030b040c030524030d111509070302040e01181407080102160309050a1401 69
    0x102c1045c20607204064668032100e40007010b40700140c000e80000c0d0010311400c01c5c0c0c418006042200c02004010f9600b00ca041c0415451900c0500300d0030b0708123080c40005110340c882040d40024010f120642c01e542e41c511700d06a050307940d10002d4a1424040f0061010710b81000b031400311920700703800701c241510a5403606400240800b00014a0310307000c40100310900092621811061009040c14005070003a51000b4190180cbc0c042d0600c00c582c107100180e061140e00c284240e11111030100010030400000c058010000c0c018031080b6900c0d049003509a481c0280411040f074115248540107000b8104424508800c46002a5080340031004d0303c5240108024412400c0584c0c2c0310700803503002011003524500420060f030320188202e412903450a0501c451003074103c5024000300e03030040b1551200c0d00c882020f040c50304155074400001544045804c8180042464405440030700941da0580d0158940007080150025482041900d0300011004980c0b940038051589103690501c0049080d00e5109481c1c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 790772482 1250 790771232 790771249
    0xa1101050c0a0f080615160b15030601380c030c071a0702210a020a1d1b0306041508010609060f0509010e190204051c1505060303160204090f031e0302030c0706020d0b 73
    0x708840041e24134100814201000268014100c046800c89030900c410811403400a400b6010f0f64000d00080300498103c3707623201255403800e40442281d0f80c40c80b043c2c41c040d071a00309600520380d00c403501004440c0814ae0b00000c0d40d00107900240103500160000030400030b034200c01c0d8000385240c06282c0960002d43e4801085400404125500d6005a16031400840d0303032800040c03281804c1102041d819200201c244140d0b54025029200090840e100141070020303200305034880002036081c841c001c1092000764001004460490b0782041e4407070f07116000c201420b0030034010b542080020034001881c43d00751028010307001d0300620300145002d403940c0101c0c40c8008072184521aa9402800e0401040300808040041c81c001d00e5003040a4106100084d03180d1182c0c64144d10307400304800c100360030b40d511944925040c59001c4200810300c09030789400b51100701c031036009030311500e90386c90b4402d146802070080320702c15011000d040b07160103403036a1240e0081d049a074003003104070b60f40d17452803c594480c8d168 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 790773732 1250 790772482 790772491
    0x31005062a070303030b010314270f030a02061803160c030818091608062e030603031709060f0c0705060130110103020a1101050c0a0f080615160b 64
    0x40c090403803c500300074041d03564030042c1d1030401d49070140c0e203100318269805207034000590107001d015200103064402454503010354105040c0c0500c44010003000400001014680c1036902a11004d0784d4045464003070318090424032a041d0003c00455803940c040040411406100c0c1c2038080d0502d889454144031500042c102e4180035400540c0d9001903c0c10a000c40da01c81c40180c0b50b8000c40032800780040c00ca903c0a404075000d007540c1d01d81c0c42c80c20102c0c03080e40d048122100c0c00d2010401d40301d8400a0213801c1c0c5100940100d0030703502160300c071a40418840e910644007500181050788541072062248280100140002c440a00c07102c40010381c144040c0307008020707030319843d0860100300390310001e0318442d07080982040c0000c42d1010000340c151900700002003000d00300181c42c0c2c141c11405135030301100d09144800c2540b0b440304004072240b07410064001c401e60782d5518011011207003003c4e51074000585c0c4407940141000c2030b20b05000c03070090041c07640c0da10542c60180100a103941d002c940d00c00c1601c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 790774982 1250 790773732 790773817
    0x30103240f090b0121080c03121e06030303100b070303090206160b06030a0317090a050a031e09061b02010315030c1406030115030c17010909060b0603100506 69
    0x104009111403a030a00c4d000d085442c0e040c003100e14140301040c07190640140000d080d81d5001c1011411460103105840f2810750303040304005036181980000c040840c20a0b1344400c80c554500c0407a110b800c0c00400c6c1d034442c80c40342c0b50f5400090700b04040b07010030b034019403c12410503496500c8680182c03a04409091482031040916483ca215440c0406614200510035400f81d405070352440080317644401d2241107070708030b002a80030039210b040405040c4605403202030910700c96406001c2c1050344c4400c100c8012008031400b81102c5000400403102c0300e4952062200190782000c044403a44116a1300700305d06841410001002c030001d8100c4196803101d58020303141042c010604102c0940c601075921a21401102c0c1c40d440e541c14640c0c4070800320114280d50007016960030400d0750742402118124820f0800301e5600f2041d617540d525840103084210001c071205404c00142100b581451010f983c0101c451a84e0000001c1c00e040c107100c41900100302d0100302e9034281649042080f800c9596840c80d80480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 790776232 1250 790774982 790774991
    0x30a02041e0515030c130e010903020307050c03060f010b0306130501080a020a090b0123092115010e13170d06051008070e06071a0705030117060c030103240f 69
    0x8100c14402c0311001848403120300c01580c2c0e0f8983c540c1c0c010401c04440c0d8021103040e80340c842c8502000d0000e18804440c00342d550700c0d03c10741000740758000016110340c0707108408499150400d0303800e06855500a5440e680c0001c00c0c0d000500510381014003079503003e00c01610728010040410303808801d951003a840009a504014440c8040d42441ca0880024041075071040c4400880311000810310702803084810054a103244a03000040c56141c12150758010007840704081c1103580682150203c1e220700c0c100304034440e00c242c0d912068913400b40300e812156210710f840c0da1036580c00d48164070001c113040304031910048080500703103100c556409014400c000180c0001c074642420b003070000039400c0a4211045c88030f480104004594842e1106c982d000c0c094525503110b20f0f0500c0c0542c016090142da2032013a8000c0710400480300e40c00400365040307035403ca20350300c04103009101c00c585800051341d00b5141110100014808030b00400d00c18941e1940720003401512240310a0800c044403442c44050140c26185d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 790777482 1250 790776232 790776281
    0x90528060509100c0e18100b1b0703111c0309050f01091e0303020d020f03030406020906040909030806030c06040803030a1508030a02030a020c09150d060b0d0605040c120c03030c02030a0204 83
    0x1c1d420748070148a5421606c0007030500d40403405000c010b070710421007a11800a42859900a00707240b07140c003c1603000495100d541c0b640f45c10000c0071100c051a0b406038900d0084524140d240c070054104090301921039000300c80c2004140040c0035580301c81641440041e04001031b09081040b00b8074921340300914002d01050851500070b06128003494648110741c40401192051100802141d4204c0d41c80900107035104a40c0c0c000c900c841c0115409181c0c802d1a04169409064200a10311f01c43c10b02181600d03c1c650303000d010040e203805940200c514a90051000544050807503010a0046039601104640241d81c0c0030342c60f00d15031006134424010307040800c1c40000706804105055018030103e81d0111540740034082d200042c002594810b100301c010350011070034030080741d100389010030000d0550001c444107814641c020700810703a0115030030074004400044892040706119802c0e43d0000d0200181c51031510101d803515065007060f6458014840c1c10300060340d86104d9054018010800807009441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 790778732 1250 790777482 790777489
    0x314060108071e031118030106090513081b03210709180c03060b040f0807290307090b0307030b030d0915050d0e10090528060509100c0e 60
    0x241106040c400c4000500804640000c0d00074054042c0240c0d00c4421044810101c000d0600803041d0403c0c8080084c800398207041b100380720455100b040c1c000380901d96440c1c0c002c00031601d08898007200b080d50911044006036a032001450748038040a00e80010707002c03410300b250a503844007003075100c001c401601c010a0760b22401000c83c0d0151440c103061034081d15100c10303080e800c003668100b007034081d5480030300301c0c1d205000c0e80c0030001801508614a8030f4a48445000c42c60b040c0a00680b1420301c1079070f00c00541c00c410041000348000310141c2641d8600381d03804034543c140d04043c1066060111500340415421514405188140c86c2c503034001c5a090700c100c043c1070400c10036402c214200054207800384003401e0743c0c2c080300c603e071200c40c644070303a80c0c01688078118020000c451812401c2e0040d001789e000210000e4000b00a01e44c0a101078500e072600003021900d003008081070052603200001200c01c08141c5aa000035800b0410a003924a00c80c04803110030210b8410907122000f24056a0b850700e0b0508 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 790779982 1250 790778732 790778771
    0x10501120b100b180334170d0c020a08030f07140109021f0c02060d0504030e010f020d080705091206010906060318060b18010e0609070f0e0f04020f0a03 67
    0x2c1110001c0761418108010700a0903c00e44c0007000c0210701c2c0a00c0b00041c2d450030849100360340314070303042400094030440410310482120107014001c0c010004c1c011904407980e40d0003003c548005001020305952140040c1c0e48510170010690b803184114000041e0203000f4802401d00360300801000350745082c640340c6100c031520013458040e00380c1e241210840050301d0f401030121035031084125a88100030300040c12942d50f01300381c20094210001060586d4083c003d50040d40c0200d11a403107107070001e046070004407559020084030b000181d001000341100716009056164010107103241040c070b8a80040c0100d60725001c50002c1e5816544000010070510400c0d01c99413001c0c000610701800001581d021500b5603440030b00001e0080b0f0b5981c07091050303c0e0364681c082c44c3d120781c049440440d0b030341e9a02003001640f082228014040c144260010360018814907a035001c1544e1500c0e45120041e004050140705458a400907400940c00c00c401141c007560781001d8904042c840d900850045070800d042c14804 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 790781232 1250 790779982 790779991
    0xa1b0309180b10090e0a090203010e0706030e0c040b0a0e091c0e0306060405010b22120507090b01050f0301290c01091b0506030103080a1b0f110118140111010501120b 73
    0x480011414014a01005d013203d4110101d82404281c4440500000b401010b88032240242440b4000d000203409800d80c02c107d81d1040e1003804e64580c40600000d000a90b10a003210640c8020b100700140048205525520340103000344086a902010002800b1800e08252001c0000f2400c1041032031100c0c80c0c10005254001d50582c1c2c00d101ca035260403900755441c003504801252200d107441d0451150310b44c4200003001802125100b0a02d250541022602c41600380541c03100c46092071001801540104210348070221803c000600e581e01c0d11040d0b03001c2c2941a080c41d0307407000f07190103051420381114000d030112511070000062404080c2ca000b4084044005403603400084911003001199110401d580c11a50030041c1c059503101c1d4030508491410040700c58a41e0781e00c5900b0000207002c5421014110903114043d01030200400d00015a0142d202c01c5070005400e01c0700006100d85004010001d00c0c605040c14007869110010b140c00c1c1c00d40b01e00f6003000030184119044e04c01072001980100303401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 790782482 1250 790781232 790781237
    0xb09040c0914010e040e0105100e070306030302370c080d09030203100c020a200a0e160f0e03060901050601020606150304170409021903050a020a1b0309180b10 70
    0x4540342c81c0e00d00d2200410303260880d061201000081e40c2540742c0da04100386075002c003070081119150024001000702524040c03414408120070016944502034801c00003a41d8068000306280c000c84084020080e9444008600740141103030b4141c40c1309000d900140d012840707000f40c503501070f04048150340b800d086850680108880d0b102c0420268402140d5441d01e002641c030081050107201b44103a150030401580100440382d6030750303030751804028124011443e50b411078000c058103a45586034000b954040d1611280034a1f0300c141e0101307082c0100006000f1a04c5c0e420111100240d15001906100c0c0407141c1059694564081203900e41c1c3c10b02200da0710060403140944a0b0b000304154064500005000408142c08490a000550001c03401d4170300800b000da609559a84440703079040010004d44502102082c01e280210b41045450300035140ca000042e07441c1c0c0078041a01c9071710300042100c143c041d024070201700c102255042c1e03c408114440c02caa4a008610541c010041c0260402d00700d41300402c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 790783732 1250 790782482 790782497
    0xd020c01020d080f1b07031e171b0909130b0a020a0e0909010b06121b1201180605060c010209041a061215060424020a171c0c0c021f0519180b09040c 65
    0x940da9440f01409d60005281d0094450743c50464400801e24404c0c080903c1c0d00401282c10010003040440050720000e200d4403001c0d400c0d441d0409032000364011203030500007140d1248044105810301c007000f254046104c1d0004244a40d40b100030a0180e4800c1600300c0503440c24074108040c40403100282140c1400a403d058908880d5500140100106014448080905c10b91801c4120581e400800c081c000c020a85551005003071403243c000e45c0100001030166003044200c5040441c41010044020005082c1501c2c080c0714040360b601c0c60200170824140c1825510071000103464003c064030250501c03035040c03240d03000307007080c0b06804060010002003107510514003400010040d55034050707a01d04c04e03455031b0780712076205202094001e0103150390402546802c1c0300d04100d075401204241c0d240d000369a46404a43c0f481c0380d50100001e500c1b0040e0120b00e0800c41601d9407902110312503102140b80c5429520408441040c2034072100d281d0046c1c80501e0302007980b058030b18141c480c1003d904402c0c10a0039 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 790784982 1250 790783732 790783757
    0x20903010b0d0812070e0a06090e13120f23030912070f0b150312040614040b04030f14120403140309030c090604090b01080d020c01020d080f1b07031e 66
    0x1090f81c0726040c20418a69100c0000c911401e02441c2c8410114100a08610b5040d40b980c900402c0c0066602c2042100d40c01c0102185c0099007481098002c030380c0145401e01d007401910b10903684504504034100803c002c0002c3d50b10615140203020050048459006603641450310803580741c00c0c138810700c2c5018542c00b00002c100040c1c48841502c1d8503a4400c0b0030320b14980d40c1c9031107200e44c1d4121010300f681500441c020b03984032410940c0204140c9555480c1c1350200d07104e900181c03000e805603000c3c620b40803000300401d00100c0c1c5500b180103807a0303218204441a20194040403030800080c0c5224030343c02c040105040c010421440d10341c2c0500c10f083d130011410001801c0002e5034410403001c03d80d010f5000540422029181c1ea0001840c1d03542000d404515540d48050319070350b803c040d64280300103014411400b000d962000c9000304034944e03070fa52482c401c2c0e11807203c41030350a03201900d205400b500f60742e0281103105000002c3c100f014002d80701c0084c00c64122202e5004510041c882d4030410000c4107491 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 790786232 1250 790784982 790784993
    0x70302010810061d0a0e040605041e0c0b0f310b03160c02120d02071a030421020304092d0c02190501021b060a0c03020319020903010f05010603020903010b0d 69
    0x2404442622a66810944082c0b0100b40f113800179411010281c501c0b40100001c0c000380f9000340d4000d5100386001d11050381400304110709003440e014010b08035452094104060080d83d400392210780030400c009840d12110964203083c070070004413081c00d03d0742e28011000400c0c0000c00071070b008000e030800e250f1179440c0c2041e1051134155a6000c80d0b05010141c110441507407a200024400b0200350300071180c001d0074009000e9540d00e914032034500b84604154001a540c13100d80300b664055a80613900079548025400968001c40b0b105041c4411803109200003d0301c0c1640c1d01916005400000407003859080d60456807985880c0040d00c0000142410000c00160350700190346c00c1d00710852003241c001809a454590301901c02d1603203290b0301500d420b1900510b1103021484a00550b19610104a6031011100540581c00100d81c0742c9442101482d8950794400103030000d1000d480b0040c0000380d09041030640c482115401c0e004000001d501107a02d10b103500302403203482180b54080722400d08280e41c80e41d82 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 790787482 1250 790786232 790786247
    0x1f0f090308040324020c0109200306061e031006050f0a031e080702061305011206030b072f01021909080703290a09110d03170c0c010501030507030201081006 69
    0x2480d00c2011040c040e001a9004c030107030709544071000b065540e00c8001803a80d010f00074414094542200c40066042100c7c901140c80700c2d019006006800d40d580c0760401c015592144401020342018040700340050f42d5000e00120702c1800f802e61000400d941003100744820100c503818014014502d000007840840e92510018903606c030300d10f1001d424205c2503d0b20030301c14050014001e403c1000400d6054000c000780702d103a02500c80c2170740c0c0c86c98815805032441f02921000d00c4041c04032001040030600440c401d801256112400104904030340044003906118035807a4088082281d41c0401c001500d00140c80d04036131b0151140c80e05400135420595141c0c0c4403061440003e2100000d419001c561440030a18500c00d80b142e072001c00018681701004001400820108540e0740500300c2e481038862900b000041c41140e00340e5200041141d841e440750a03c01c3c405090921002400e100345665003000740240780c0611300c40d9000c0c0c045a0314520000d00b4580c809070404100e52a60041401041c1e808200d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 790788732 1250 790787482 790787489
    0xf0806040201080c0f1e030a14041a0403170a050402030d1d0607020d0b09010b04060b0f120901060801110706110f030a1802100c150513080705010b1f0f09030804 71
    0x11216601c404000c82d4840030700c90314183c003240044413900c1c40d580b94591b001540c0b149028503010f000c410704003104100481d004440060140480155a50941211306800c9038002d20a0500b10030b864403c00700b00902e10006c644800c100c41d207540030401141828401309011241d1030802030410701e0504103400e80a06023005150150202040c030340c081d55070340040d4005c4241c1100c820295418494501e034060031245a80c10300440c146880021015400002c4403034009403041c03d5800c20700c0880c1c6d400e4046001a10b800303255926000003103001c2c0800c0c410800149905902c0e195140000d103480b03c265608580c845221150511084503440400812250b0140d1110303070010701200705d017010f008034840d9043e010b1b40101c000e00558183d1500085466101800f440d0072a03160541003141200740e40049851082540440300301c2d00004981c100a01643d42c441d40000c80c84040715804551f40340d11146006144408820100326441d420407034100c42c0c280c15180100d0b000e41540c58844191190740b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 790789982 1250 790788732 790788751
    0x130506030c16110d031e0f120b0a0810060501120504020f0d03050c03030c0a030e0a11041e0924050907030201140c07061101060504180f0c0806100f080604020108 71
    0x280404100b01040f00c004000b07050044c61110f1080d09418024606030303503020112111800004003036881409600040280042ca64501ca4940e104161840c0a41301c05000c0b82e41203084d015010448140074003810300c2200c001d000006d9014600300004003a0b01080002c0001079240c41c050002588801c0200b5081500940380307061503000c54a011601e620aa1140300c40303a000c04001c3c849010002c0004045000c00360b80c050000112940d40705072a10100381d8020031904043d0464402c508103504076001c11800403951100031007030034000c0030980c2c450b040c04903041c001c5041c4001a84c4240050516184040c03501041185849074420381d0b1584180000b034148020498800c0a10b02c0002c2100c40c100030f8081968801d542c0d81c14003900b51120140b802a00d5401d01c8001b0400341494070407150340300c4010741c0104481c40301c4e450300c00345c1207020035003a181820052008640c9003003c000480c050310000ca0b00c1c000c1c0341d1501c000c03210141c11507001090140c1100041c88003603031707000680359000340741103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 790791232 1250 790789982 790790017
    0xb120303070c170403061a22051b0d0c09080619090f0f0f02030738090a06080f010e0601050a08071e020f01051317090114030c130506030c 61
    0x9003003264a003411215604180f40307000801100b0014581c0007401003010540000d00302c2c0a4440c10402100b516050384d030013459045a0b4050066456006203401c0105141d44841c000301c0c201d50100e036640b100081402c6e0b151a880c80c0f2101c0d43d804641000101114000340005003442110780003218145135034044048c1e10f2700c02440030300c602c0380d5603d14150781c022001d05e0f9044503854540440e000c01401648280104180003400401a42030b0341c1803c0118550f4415620105c161003124000400c10f20070035050030302026810f500d070403902c100030b05840d0716850b0a501c0c0418510f41280d0058204054100b05103040c40300a07604142610141a01c0b8140304155a442003003c8038002100040d9511481581c04c003842c2c1283c001c02d1b140070b00c0d103002000f4001642e4030000c89924000a81d40288161403803112041d900a659010340a845414541181c55070030342580c0310f0303683d00183d0b0b400b05d80120009108291154141c0e41c90300800c2d095420a081d0310340741600c4406402100781312400303142d12 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 790792482 1250 790791232 790791257
    0x13050402091f0e09040b091b01020d110a1b17010c09050409050f010c03230f06060703032c0609070b0d090807021306061b0b01060e0105160809040b12030307 69
    0xf95000503449401070001c00c01840c1504020004400030713100044507000b40b0707600020040b00c400440103d0001038004281200302ca800072102032001012840301405050603800c002440c00301841d00048040e0450716000b03003000d003490700d07a040032074801c0d01e03070b03031400101c2d101e55504194800119441202d00241c2c100d06400c2081c20003101c001c400c1410352030407400803031103509075015184000103100340005106112100b81c0c0c1444007900c0c4500500c03000400100140f406c10010b210341d51281c50302041180e40081520101c682068408181d056605050030720035a0401c1803070303408000c00b0010090039141541d148c00e5849400303e008015612140410240920f0408803414564094007814001300c2c00314818000b89524002e03400002e0501d136807035544000140700c40d080300d904159400c00d503134a003070400c0e0b8100c0021100b0300c0c14001c050240401c00380303118164045407401a20000e07502c100103401c200445150702c058612464030420300b01c0a4400000640343e01c22128180309950455 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 790793732 1250 790792482 790792487
    0xf030a14090d02151c0e06130309030b090a0210030b011d0d0f060510122a15120b01030e030706053706091424130213050402091f 57
    0x1e032502c0280d04210212900c1881c2c41e40c0304000c2c6611140442c02d840310030708403207820054442085103240290b00000100f18103030780340306581d1201403003400c00c601415900d03503072411040b004031201c9002c1d80018444000b90f090542c45003000007454501082030152200001e07041480c0c0031000314030568812580e03070301c0362204a0040050b40e0070001c0030311900c980740381c220b02504d030445821000e6001c2301800151501610140d40748a0f40c02581c9825955000791040038211880c010003064840940740061308101303503c24184906859982e4802e2079007410302040135100301140242c1010b107007000c25a08501d02006036400e2f10391100d404140e54070349030303032000f01d4a0410003880c001300e01415075481c01320300550515240f00c0644c0020310029943c0d070401d50481d5600c070b009104002c0d030340c0700040d10b0424420032403064a20030250f81603140c54080101344101d04281030100706940c001858090b10345541c1650700100b5080b60151701e05000e202c040de94042903880781c0002505070700c0340d1214207030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 790794982 1250 790793732 790793749
    0xc060f040318080105090c0307030f0f020319030203030f16090e0a150f0e150109031e060e071406030c0a11010f151508090706050a0e0406080a02030f030a1409 70
    0x100d0031408080100d40721660f02c3e009007030603203003c0c078544940c00c45058a0704003c6081d0781141c0c0c008080038841f0480e6102c02210000c0c103c4100c0c1d140c001c4440d0181c08090a183c15400c070750080e4000c0d80c80c0d00e00451604984840a0001c1c0002015910310f11002d9034007424150540740d544620448607164811400041e010700d82d0b0901e03140c0d16001010850f00b503e00c601c10f084540703440454400d91a2900d40c402c02c150134694082c00105000001d0012551800907501c4021491100324202c00705a00c0d0941114041c0c0880b40c0aa00000310420083d201814402d4030940101d0b41c00c1d2450038800e01c4080244a80c40e4518180121000380e0b444060081d4400d41d96501c1051003800502540000424221800e019540c03807018201c085281681c42102801c0c8145400b90042c50780d9800c016042c0c440f600030f10441b00c204920b902d1041c643c1d4442c0d018000c024410308008000e02d0145204150130011080d0210030300ba401030001100c10b9602810600c00e0301c100200a03680c0f020800301083c6080c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 790796232 1250 790794982 790795007
    0x14160f1a15060c150103110112020a0f0c080c0604060f2003070f17040602041d060a0e10180f0617060402090c0c01051e0604021303080a0309051c0807050c060f0403 72
    0x4003513400c000400d0015442c440007032080240d8588003502000d000c40c0d0201d0080c10080030004260605403200c2500880102840c1c50041c45541d041c041005005031424800b29011111103407034101c030402d10741840c05040e401280180d96240380c541400112111804014060010406220080c030031160003100292040c4540264115141c642410948069030007449000c40205401c1d540103401c0266090130790003090b0041400980314500b0ba1502124030001c1c140303080c1c88100550000d0495450118503100e02c140c01030125112040d150725504031b64165001c3d240c560890307454280390303070400b1a40a03071280e0304403081803281d160b60345645201d00031820340011561034042805220400d51050014100740c0300702c00e0f2000d0780e440c42813206074044d925000070711403035944007480003d0320417018110361215407400040c0030b10240c4400b07203061a00c00100400c4070b06681d4840d4040c0d40504c0b05503100c0203a01385545802c0120b140181d0391400102004030405140c00030070109881350303181203540d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 790797482 1250 790796232 790796263
    0x70f0302011409150a08150109050609130e01020406030e01180209010b030903270f060a120b13090b1b070b0402040e0c1011060f040302060714160f1a15060c 69
    0x114007117128007402482c4150388416810240d80000407103507219641100c26540c018102c07908022441040c445030030406030740303c5040350312001a2001c000003403026000820342c5a070003250071040400c000e801c4490074000c81d88070614040c101009078464144090450307444100041c0c0c0c075070721204400c7c210300499100b43c0e6501605205104800c0c1130200d54494100100c40d01288a000141040310702c0c442d020380c3d1000f150b000d11a000c1803240a900c0a0310a032400b41040d243d440c01e50784503034200d640061086815507100c2090201201a81260480740003c6200907803030544680c0310540b42d890000d000a201d25140c400070403d0002c00d000c45070380d028020700013107142a075460011b400f00310b00803903007809886141e001950703d100d42c0c91003500460301a005071070182c80788141220b0900b6400702f910b010b410100b01c00c2010015054022003001c0c09070059081d00c41c0d041c500340d161100040c001c01290352500b0700740b04c414500342049109003501100d200d6501c4982507102030a103401c4c880385241 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 790798732 1250 790797482 790797487
    0x31b0b0910020c0a0b030402040e0703050c191502010e1006030201090e19050f0106110102090a15050f0304080a320a110105010305030304110901080a02060313080d0c02070f030201140915 82
    0x1141a15003000d18002c0d4230071201401400c40000c0754640d958002d100c0078260354050301e845212420511240302c0f01403050010050b00c10b450700660228032030a0907900300180c1d0349411044201d41e05110a01a5043d001c00600013540b039500000d2200543d4080c0c101e80321039500104621200885c583d06104c055528284002d14000510714484c10382442460b02090020307920100b8044c0c1031089443c3da0400405402920741801c94000d010b4140000100a1007420030070310006001e00d00156200318030071380c0840c1d80ea10121f0001050038540d040000e5a086c4400800076101000182d984040c00b402b810085c0c41d640c64440441c0c17007104035111540554a010004420321001100645c40b0328001c0f60210b2a2007151814420140024814004650040d501040051510704000c1d0f801c40b8820108145414041e26400003582c00080307010044c5036140054a10720340c040c00980300811001b184648801d00e141c0003e003c40700c0051182143c2d410000d8421b0640e925196410150100d80d41c0c03564 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 790799982 1250 790798732 790798739
    0x901031a13090203060a180b040206071502090118050306151c050c040b010516060c02010209060a0309030f05030115081e0403080f0112110d03030e0610031b0b0910020c0a 75
    0x1014041000d901a0040700002802000180580c0b160190440c40071f0511200303d0b2507403500b1a0303015000301d90200c01000a20041001702d00c0780e44205400c1c580060390380007100d0014018020301f100700c484181484004100d40d03070f0045561540400c0502d0b400300011401c03000607002c00c0310101c403081c1c10b89240040500784000001c15070010a0145e908002c8522001c4c010b41d0302c1c0c0620545ea944299080d26100c00041a40d001101904d0045c0000340c10025420000385840c1c0110480c0300c0080d9640584200b80360380049103040324403090822520359414510a00946900d1100250502c0b202402280d49001d070b10300340ba0105800356503e00e4040c181845d0050111f0026503020182025500021411403400b107020032040383d0003902c201c00c078a00c500c140510080c002c901507091561719084207030302c0b0b00c05022580c4521032148100b50014114a0701c40700041d500c00b0b1010b02c070030500900b840400e40784000c0300c00d007000071940300c0c0400050000803864030400c021380c281c20404294000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 790801232 1250 790799982 790800019
    0x702040b030a080c01020a03060b030124020c090c0d0c0e091303050418021b0d0207060c14010e060601020f0c0d1113150303140a0c03030b060d06260d050901031a 71
    0x103242e01f180a076814009156500c0412400d80401c1c05010714038000c13825040a0301c16045000b0740d043c0d0507801525040501c01c4001032050104807400c5491410014503420f02c00841d100b055104200e0f030510002c820031217004141c106500a154211280101209909141c000c0080e50b000746840380c1c20841040c00383c03a854010b500451015090341e055000c4014210001049c60802ca00c2947e006000b00f40c5800422034550061090964201e8401104041c3d003060a000316141020304e040201103e00b061030009180428280b5900040d42069003440410b5481d107000c4008c00d81c20000c58401c142c00800002c04841c400311401c2206c2d890903a150111486440c102e504890103030315105940340c00c66203140054442c1c4020032001548000c40c141c0001c1c002d40c4559200b20300a003e490429010782c48a0003158241c1e0899076003103c41c1d0200600120561900010034464140070b002408c880800180c041e004e80f460b0f840c141501c5840d02d40005150f2003031740d91f1307a400003450900c2e8900c7d41c0000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 790802482 1250 790801232 790801237
    0x1020d0f050c0304030f0e04091b05010f1403040228031a0726091603030207030c05041e02031e1302010215010b040303030e1207080c10060b0702040b030a080c0102 72
    0x3a280400d041c0800030361905035107400e80c4d124680540f13074409040d031042e03400c0b241e842500e04c04551207643c5040900c081800402c180480c60b01e04064040c0141c2054005042210b0f09440541004098440d040c88003001c00107481c1c10580c107030399a0f000f07104a00700d080f001c2d0000031905e5412102203000041400924a00900c0d002d10f402105041511a404c0448802e0a01103c0034501881886d11400c003041c903441240c1c1c003524000540d90000d00e643c1340c2ca94032409036841500103900c289414000c1c4494099441c0c010300045404110b20728040074030072052501c0c00800900c05a0110010760440074081e1240450449400c43e100e16103056540e01c0000403120000f6401489034186901d400c0013a40c440b5810b17168032909990a0070301e1960100d0140002011121290088040400eaa560240083c0c0f04283c49a0303109a210744800800d5481c00342034244101405080507401c202011056045034580b6405881c00300c0d440318103401107407901c12209030007002b6410000e14208075580643c00b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 790803732 1250 790802482 790802501
    0x302070c0e09031803060709031b1a0406080c160f0f0609120e040506150f04170d02100504020a090902060c10020c1006182301081c0c0c0308090f0301020d 68
    0x10711340305407101c1030503903074001103c091002c03490340d010500110303030105a62a120501480901380480d22041d40c0f0a442c0a0b006090074007100105060000d6604103040660001610f01d200e4102640305c1e0b00c198038040400030240026141195800900c0240b400d2100c016400c40d00901c00c8600501e0203c10490030000c1e0500000e2004140003017901d400d005080c0216030003050308004910481807000aa0f1200719041025141003000040c9202c60303000000c098003c020191080090458010f4103000c1048060940d451a210030840140c0d200e140f00c03425102e82540002c0c54500f80c1c8045451441004800d518601c10005020b955600d150001d10030b0400c1582603540100c500c110b200705440446c088c03600b0f88407010420301d0b00e10710a03911010b000136070408494510b01002101406c000d8080e00642c03000d820120040f010540c1c0b03000404446e804603d00711400800d00d4958103031202550000410700c1c05c000400b1811940c038101c5900203848010001c5580d006c40e8900b04008201201 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 790804982 1250 790803732 790803757
    0x50904060b0705060406230915091204060c021201050a050403091202010507112716080f2a1305101e080603070e010803120606040609060302070c0e0903 67
    0x4002103035140107078081c0e880e03265000b0000c10039910313a41e8030907028141551480320303410a45080e00f04007054a0903140c1c003450014001e80003140c041112419044801806c1c520706621000701c442c1a142e01008980466049281103079090110784000303481c2811844102c44a5801c0c60103101c0060300c154050b5000d03600c40e842d40b00155a441c250280d00c0c455441c0d0180c0818002d0102001084121890303684002005001d2000301100340d2a12128000d05c1d5000540c0698090400c0301d5102c1c2a41500c1d254041400d1041a61401000036560007500801161030401c10b03582150348034045041c0c10714500c18640b400da488100b0340310102e0070506903214081c0b10304500c0e4415184a8068803440c0c1c0384814003009050001e0310398401356840d84020b080703260984100c19001485a015401c0d17503028102c1c040140d82d85008001c029131550030040c100c80c0c8518030800c4200501a000032000c0304841c039504001da00c9951505160b01300b90b156520800d0540042c00400440c01360200003000300048c00c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 790806232 1250 790804982 790804991
    0x31207110c030c0102070e06040b0306010e070206060d0b0403230f090114180d11040f0c180b0405040f1401030c080d050f04210f050304080705030619050c040b0a050904 74
    0xe408156581c0f020700d1440340981c020071014030100750241c03400360b4808009407010698881d03a801180c500402640520b89040180b4103206d00310358140305607504042c0c2211181110f001e56120080781c2c03000900000c00740300740401a01c80c0340c800100c0703000da0101c0c4941c0441d1240c50700580d4030036a03403004605c58001203009210703039901d0481405030b510b414020354045e10003003110028010b41441c811001d41d40c405508980e81510341c4c0724003c12100c0000800301140c88007036484003610b1041c0500c031142c1203041801c014410300382e220058508a80d01220003103122114440c611004210484194035054039074400402400541195102110800c204450703078101010421503c0b4094020100c1020004000400c200c40b17441a40c0001c504411140c40203841440c0d03164182c501d1110004c80c0c2981021a0402c082c00043c86000300400003500601101d142911035800d036090080005444640ea480101d1443c811440c10b82d0003900140c240c031039460000d03080140040d0840e15080703118900f007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 790807482 1250 790806232 790806253
    0x1a06151b0f1c03090b0a0b010507080d06031a091c030e1e060106140403020d03030b03011a210a06020c010b06030906090c040c021509011104030f1e020303190203120711 74
    0x2d1103108040c07174220481d1032030b0340c0ba600341c11005000140800743c100082401504041101c000040081c10392458001401c20b2071071406013003480b161f2803000c3c0746404504c104400c002e0003052032502840203a003012480d80d0002010340040c1401180000280724091030054100c0d00404003000b02081d410441e8820380c5d840704d04444955440902c070756401c500340410001070416921807495144a8200401d0341c8482c81d010030308607011444541d0350358804500e0150182060401401c480030170201220340c04454610302655102c080078002d08039076001508801c054020350299010030030041031113a4a00b48190096514901079036070b5495406440c1c40c20325245011b115040c00010741d0b401402d501c8490081d00300308031100918503050742d502c034a803900c0c818080c0c00081c80a10300c251980c1080d02154200700a20045441e00c402400c14440040c03c0981d400200341c94070443e06e0524680300c1885100201d0440c000c91485c1040140b040341441501034000c008102c0d03100301c08003103911240c0b8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 790808732 1250 790807482 790807487
    0x70506060f012312070309060c0302090105120a090f03080a0510120221011d160f1806120605060f150a051608161a06151b0f1c 56
    0x40701c0d400140401c1c840715094030900d20740c0c0740c6802040d903024a01c9080484421591500c50710407100d080c0003903903405444040165034401c80701c00401038907086040003890000a09a80309000000f0035070708542000511901c8150403140e20359a1000030300300410054680606200821303203401068500703000010b451104071244c12001c80b00004c0c0030755101450b039001d000c86a00d003240c0d800034503d244901060940380034000c0d80c40030540d18642c85030004032550118144428580101030031740f450082044042d03800311104007610141c401912080c2da0700100f8031b004102e640c1c01241c04c080d12004a2043c040e00c1d9000e60320800e826500ca002084244080100c4030044002001d0f14500620481c1100da100b00d000e0200c00802c0064143e44503119103407041c0301d8118a2a00c018400d82c0b605101c03c0204041a08201d10851441100c45081c07190000c1c1607401010f4000f6040740001c903190200007280030b14240e050302844107452004070040f010300d40b511241d65556810a0518404401a03031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 790809982 1250 790808732 790808749
    0x9030b0c0a0c06020304050c09010803031023010528080604050a0203040f03120e030708040314070f0e0c2a06070e0108010519030210030605010207050109050d11060c01020c0307050606 81
    0x101039541d0540b055060740d807240300a400103002036460317100708841380109844070349082d406002d40700011a03d03450300e000300507003220190304403942c0d403400704281c8002291080c02c81140c071034090821b0f030b4907100a408820326954900c024405d030300c00e00c420038010301ca401c00c000c01c0c010182503030700f07101a96071003140300f00f684819940100440807085180d030100c6d2158030b0491540700090300c080340c040400700042e4615080450f09175480d0034000340400400802440440b10403048001804185181021044480b110342c0f145c45040b803c100001113202007483d003200c0b11144402c5150013501880e00f00400136210b03d021481c503610618020420040c06605100e08402d03059480900c144e017020107214a51041054102c0309901c061404001659202c00406459030250f174001405440c203c002803a25205601081c103020070720344240030030307260780c683c404131503404c400f40d111681c681c8000301d9002d01c41c102d07415100e0752000c6010310180d0b0b001702c01486030038081d4045a0346030329038104110150 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 790811232 1250 790809982 790809997
    0x9090b01140d0905160b13060c020603040305070c05040501120302010c030b0d0204090203070302090408030a1107080a08090708011505090a0e150c19030905060a0c02060705090402130609030b0c 85
    0x9410500031031201d000c0c2ca40103030100d14460b00a954001e050800800351903000d50700140d1501c14040b900e00b0b031030844a200c08000381702615154050b081140c0100c0d4181c0300c0900b000e000c00c48001900c80c20f11010f201840018600640200507669440300224500002c40c68101c1c019401c02401c228814841d000310718903218000c0ca05000a211642003000801198000b2601400350480001c09a03541d006858426805595929941d02d0111a400100c0b20561103030703030710400280111008140003000342c8200b07580070300304942c540c0c803881d45544c0b03401d0060b8003000040d803d295184c072181400c45c010f03e04844040e2410380701500c449104d5000e03686d004c68032a0290388201c0075036504000c013000f12034000e01d1080c1c0c07103443c0140c207810502c41c1d00c0f0f0031041c1c48007190300d6003160004c01904103c0a64804c0600c0300801c00022110f000079190032015200c1d07000c008020600b80c816943e03690442d42480c034186000684203640f5a000340803c44503200c283e81400f01e80c80001e0b0403900740c000310341c1e84 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 790812482 1250 790811232 790811267
    0x13060e01081510030b0a08010504031107080a03050a030203060103090b04050322051005131a09010807080f0f15210d0c03090b030406020714010b04180c0e0c070c0609090b01 76
    0x43c0050300d00813401084411543d9510502459000583d500c00f07200b8075001d9030003075544210304001c015840303150200c01e90181c08541d002e0b101c4040441e9100c82542d00d501c00510f0702603904e07151070004a01400641c10040d00540903c1e0030b2208002c0004001c1c50390400d019908013802103e24050f60700c40645201e5107401c400181e41040029118500a2204c00102400780010a85400b44a00188080407035038919150000e154985980c10400c001c0d40400c0d1880c003540c251030048007000303949001410070b40f9840071100101342c402030800160b40c5005805000c0b0162080b80b01d0050b414401c034442d19200500410303907609102d82c8a000e0100c001509520342c1c620007842e01100c02d480d035000030026a6425828030402000600c15203061000d181c008002140c0703205030000b0041110300c84002c564080352070b410040c0000302072542d4102140c0744001400311680d140003446015200d40307080104026190722f404500c0780e40194101090b914041c004000408640c001510280c0f1004820242c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 790813732 1250 790812482 790812499
    0x3010060e0f04020310180e0601270c120c080a0b030601030c03120c0f0302061e100b0c12070b0910020f1b0c090a060e0903030601080711010213060e010815 68
    0xd06042c40d80003940c11200914242d0b06459843c14841d802040414440c1c0001340c803500c0c3c030384403600100007990141c12820304048080c0c001e8581d503951000c141210080d01c0381c9501350050514003039480000301480005090003000c0217024000c00f1640220b40c0944114500b941e141d02030f0800143d258140d9500600f891407240c15130301c540b1300f050b850b141c040c410420341c2c3d080140001c3d2058201d42105100c0e400621050905d01142d8402c0d54800296410400d03a032820840d680742000d071641c00320340303501040e1551007440e09041414040d0705414400040030002e001401c0140c11400f840c071882c00031050f601c02c0400c90900710282d00c542c0700005c1c08840c007840140940d203c01100084005408011510a41025804a1200d510403240e0004040c0c1d40c44041040c10007500e55140d1000350380e4081c511b180380440000c0c01004001e0f05101c06c1101030300000c1c5042009604541d411705452103040826648c484005041500b07090000b400550700c0000302e580309641518000e0f041000030810311 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 790814982 1250 790813732 790813759
    0x15030203330f07081807060507050c0904031211070c0e040b07050703020624090a051602030c031e120901060303030e1b1c060204080102070515011a3010060e 69
    0x16400c0c24064440404103140840700386040c17204100e81c4008007140d495417602c2e08010b08101d03041100c40350f690b5006030034500402c0b0000b0b500100c0c11885824107a00002c03c0c8000b000e400302d0034001c0341d00081529080043c08202076401d0060244103a08c542400005551001001c481134050700720000c000d80c1c429804101c1c40e01700c40d43c50b14400c0b500203c03980784080b5800c0003d403c47c0b10039107508842540e15010701103010131a010b6251044d1072400154901907541c41e0199480c407440010a05130070082d0100b00996000800302d44425140c9096200c3c3c42c01e040e88a14000e08480c40304402091900608911803040800c0d20807440d02c010308080b460b803201c9814043c9800a04c45442540106d0005440c002211807000e400500f102c2c00005844908507d401ca20b0010f2400c2c01072030030303080c1100400128007809140211001103910040e120001c401001c81030903100c1540d0785101d030300c0500c5580e9404070381e44128428516070440c4d114903580e6450035108a0140003500c2e4010f0030781040718 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 790816232 1250 790814982 790814987
    0x1e080f031e0f161113050609100305031801180e0f010f0308090d0503162109030b0112110d05011517030421050a03020a0309090b010c0615030203330f07 67
    0x2c0400034010404041601000c02c0003604144000c0c824031740702c6507103100b40102da0508814090340030310004011b000680c01c0d07884040d5640142c1440ca84d42110503659601c80380d100d40010382e000501d01940b000100c0d1a10041001c0400c11101100d400c0a404000950807518200380d8003203d030002042c0d45000009800d000010703001001c140c5441c803040110705103800722250b005e69800d014003c9550101030f15030503d541d50310000ca00034104141054140040f07032054120604407144080038003032680e07032850001d0100014042d42a400019240800d06000c8103420401070b150f030408c031319506951101091001030350141043e6415034070500050002000341c2d4002841c0141ca4400700d42490503076a180d40c54810002011001078001c2c0c144c0908064000c801d160180c008002d00b80928040d02000801d0414100e6026241790389541c900001104443c0c5818041c680180983d01916240d040003601c1d02182c1d0038001a140740b100c213919003a040d101c03545000745407080070752003580c5968104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 790817482 1250 790816232 790816267
    0x603071e020703081c06080f07260304030308070e10140904110711091006170408210613020304080a030b270402100c0c1e080f031e0f 59
    0x80c00307512036482d000c000302e100607000c1c20300c00ca2030503024088402e204502da800d07280580d1220050764410300003e051440c003c034104060700c00c4868030b10401d0381c841d40d074003545c5e9860010080c03039400006408424140e01400a0b84940c881c7e44807200203036111030501882101994404d80001c004500c00f20448080c02d00400c00d00d0402800800e1520036019100101ea01c403940c100c40a5140e000b400c010303070a145100c2c941c402030407400d24005910f0090041d015030350354041c2ca050280b04a000504000e401d00645420075010f20300c04003041c1d58140342002400b02038a1051086400000c42c148444250003102d100e191711103202030500f24052010b4029003090001d40740d101180203500d02c031000811807411050000c0361b20046190800f030044c03000c0504007008039820003035100964804a220b03a0401c408035100c03038505030700c5004c1d1100d011341c50064580020b0507901a500c5070310850320001018140d0109041c8828561001041c10079141744229003495001901c20322030b41c000041c19400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 790818732 1250 790817482 790817537
    0xa0f30110418060b0c0d0f050c01050403200a080d02030601090314010b040b090105010804030c081308150c19030b010c0204050a0f0f060503100b0d02060a1706060307 73
    0x1008101491406445061078206070020780c0c180140d071000c0448418a40203441c02040c0200c43c080c0751400b4101c8254641c1107010302e00e402c2c070140c00034035a400380c41041107452811005000b001700d400c1c03d29000344101e1848420080380a55a4026080c5075000b08002000b035030301916040c98120201000006504010f00b8203042c000140b1001020500340348040724200004400000c2c813000a10400c800c0390307000704906016980080c010b01059030024200c03600680c050411000ea041c1a1500421600c10f14400a4090404c000b0004903c0c00002d4038407007a442403481e0308005e0703607441502d005c24010012104445040c11041110b2070b4025402801c1d4488180f5105080440d182c0200d025035509a030030f210383d1035580b01c242022080700c0c841e41e141e045a60b030042c4121882c01001a030382e14500008071100da640d8450049541d43d03a45c00400f4606c0e405030030103481d59071191000d49206040500003003401594800100c540c50400c044a10a148a4807030711034072158136560a48440c45980d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 790819982 1250 790818732 790818827
    0x3060603030a050d090f052416090902030a2424090302090a09061104080c15030711011509140127020c0c03070906090e12070212120a050a0f 62
    0x41b13240810b50a10802c06540080c040400c1000282c507081900200c006025481c00034a0844211503550322803140d10444962382c1000d6100e80b00d0118000081c40d000c10281c407030205400100c5000c0711281c550320211001921176482c0c035400d140d6011051221034003440c002401d000d60900042c5840d030311040d08168084400555145030b661002c00321134a1203581805124046820000d40c001001022614070f030a42d0501003242140000004c0350001501d84d80c2407048071007030b80203885825130000c0e070140915848405a10741c0c4104a42c01803803010040800c9403907202c00411001403e050143d0040541418140403a62100844c0300a420880b0003401c40c0c010744018407000c0e901044060040c04481400042c0d40d45000ca03940d08480229207081c0c5190001c42c002e59000d80741c0800d03214000c2e0192841d84202d1929540607040081100d800919000c001c208208040d0740030000d00b1084c030f1789444100803901702d188141d844400d4200301c0f4030099030408400a03540c0c0c800d18404025485403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 790821232 1250 790819982 790820003
    0x1b150b1c12110a031e020f100b180f0f0c03160e0d12080a06090606022109030d0306054e071206060e010f03060b0a03060603050c03060603030a050d09 66
    0x2000240c1003c01d6008140d00240d41590500120729803140d400d038011446000508074880c0b4080501d031200c103ea41c503540c40700d80d90001203001d511038008141c006d001d509243c030344625108850f406454015101403030030307940c0400065402000c41c01100e0040c2d642c91714108502c220f2040466901140c0030245070004a50700303e5000040e02900c040280c0c507800e880705210351400c040c0b124204c0b4803680c0050380782da040940c100710564000c10f0340c04400c2040046200901125610290584500718901ea090300c40c9826091781103505502c0101500d0044424192803508600d40f50ba51451801610341d01c85103008044040000c44040e0284100b0400102c1402e40444400181400242d5001c841c0c0b1308404070399441048141d118080c0a40180155040a5411b06602c0ea48036405070100074142c3d99280340350a4517075a110904001164090814803040e526442c00d251220461515603001c0d00c40e0101082482c0b0b03010003600d00d02c520035503c080c00c20122901107000340c100e250081d5079441a1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 790822482 1250 790821232 790821257
    0xa230a0f0f1b050a0c1509050d0f0f0302030c040512070e0702030a080906070f050c031201030c1401020c060d1a1906021209090a05071b150b1c12 64
    0x681c02010a0214881d0300001e07074030b080e01000140002981021010000c0030844500a140c001c408010500e0b004002070f600030001c2e00d800d03070081c0144580600300380305d0507500c1c0800640c03060003200941039954651b0000801c200307041e8164001941d142178500010b110511590900c010100c01d0309400300121014555111049200450241c40d070100681000a8076001c560f00300022640100000c8004c5c800fa1a02203402000c00310184044002c01a0000b030850920b031080003a2068461a80d009882c0c5503502d21384800c0d90b04c020311030f09482304010b0a038402c0c0c5600100b50f8250011029145038030b40703800351006030700030b01390f05454809840c485500f01c50b0a4540c00000c0000f1403013413808002c1c8505084010749808426600800811010401c0c90801c3d212070243c290889502d80740030580f51100b007410f48021150f03010f0945400343c0459140288081609003586020485904000700c01d0740341c0901410066a13a01f4428018030b0b45042d100284020f000e020907400346141c441c10b050b21 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 790823732 1250 790822482 790822511
    0x70509010318060903091a0705030915070c0605091008130212190606091104031104021e0c06070813020f06030a0908030109140a180f020a0b0714060a230a 68
    0x19007401600004e400b09018400d402c0801c44c00207402031440c2c0c0941c14451249e454035a01e210380d0410354050100c4d856076441c0c090b91441928091030340252000134541d00c89038002c0141e04004a070b1032040e45001092035440b030045040c1c9000b07070200d50b060b0407014026020301241400e0201040140c2c4a25910440c0010a0119141d0410711461001c18080e180c01c1d0300c1815104800030481610ba0200300030400079004081e81050081d06032401350b2900d82d024410344c50000741c0e200c585268076001540040058000c81d0395407060000b40ca030110300e5100d140c9403141401130744200940102444142150341d107000006181c5c848a0700001041e07548446d03880e101690002e922901a41d81c0342c43e0814026021200200c0d441500c805041043d0400c2c00001944010685c201605040c00700e14508290340310300d100303000503140c603004059983c48240341450070707140b03c02c003a214507000e4030011070101466809082c00c80300c48a482e00521240d460000c820540e03014041089952381c41d140d0703008108 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 790824982 1250 790823732 790823741
    0x9060412020f010c110d0504230d021c053018030f0a0c050d030507080901030e03031f1e0b030c04090f0507030506220b0315090105091507050901031806 67
    0x10150344094a9490a4007810310b0041e020546c141800800d00084c401c4649007807010402000c01d1031580085800c500226482400d0700e20003a4010280150165140801d551307042e404d940b08034100e030f5240c1c0c44140618014040c0220380e00201e40c00e9001d44582815010251140c0301c0462140b01803a61000e00103840c0c180711104100d8140c0240e012030044c0504880c8080003401c0c103913900300454050341e500a0180c0301c4d18000418000d030100701050315074401e070300078900d0031810750407281d50703041501d00c1380c0c90321956030035001c1542d041e98004509540c0b00314100c800b482c000c02040d50964208940409940c10041c0300d0b65004000303100c0042c031020b0781e0180240c400d211040000e070b1810400d4006099950040965004401c0c010345070038810300c501543c80500309a1003000920220310702c0060704000d201c04001c1c003200c4210042c8600e140c01980f000b4000d492400c2101d90301c01c1a204200a1484201c83c03240110704240440310355035019402c03109241d200b461003030918000903500e100c1102d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 790826232 1250 790824982 790825001
    0xe09040506010e07020c090105101101090803180c030613031b03180e1006181208090f100c0f0f05011e05060a0803030a0f090503040914060103020309060412020f01 72
    0x40c1e0044004100c02600750000940003e000d00c00341c40803c0849011a8403c40180b1410380075410040303864208038480c1c20102200c2031800002e0004004a041085181e00299450542514080c08200c4001f100107070744110b100b030150141c4441e694030307890780b82c00111004c000d03018041040ba20142c00d81201c1c000301c408a2003a01e403880e1551032011070100c6d00c4499009485014440804c0c442e410b04035145c1c00040310514505420302612000441d5060160781e03010100c1324011a0901c003c004100018020502056940210b98010380301007100100001e4031a5000c1220207000c80080f90b400d0111940080c003d0032240401c004598810b4212943c1034030100c500f003400700101e80e00f1242405240c0d0400402c40d941c00482d42030640c403680700e204c054100a842035036041e040e02c0415007500144242500441529195030366601143c010b4034442c4852041c17551041d00064896002c2c0c400c0d07a000e80c0001008081c6d5503559694042100e50352084242580f00d842c54816000c8003d0281d032006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 790827338 1106 790826232 790826243
    0x7110d21032d0f09230307020d0302030706150513020d09020a060f030c03092d0c0603060303021005090d0c0c031a010e1003080414010e0904 62
    0x105200749200c0003088040404500000001c01c01c894036205000c000d100c2c01014403c3d5804440718200020f0140c0203462014003154010300e1a40c060300d540782c0c101c0e0316160607074002400ea515509000c4005900029840c410050507014000c20100c0c0071054000325810329000131503640a8000501000d0740c042404510815103400c0100d025130003901c0e074500e0343c2d101d10000f040400a04c0c40c50010a00b04440007090030700ca0708c211029250480075040841c2d40440d2000408442e00c040300410b411515100804243c0941801000b80019140026080c1c0f440c6030190810034403030f643c80c0100349040d00300880030001143c003444c5032065181c040c000218610380354140d02101d4201500000000340455109800410224141c1c1d841e450509019074641c3c1c0ca0400800305400001d204140a010420030031030001c1801c050350303005041020b98681e1100210b441d01e00d04503030a0340d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 790647482 790827338 := by
  have h0 := BRFrame.cov_init 790647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 790647482 ≤ n) (h2 : n < 790827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
