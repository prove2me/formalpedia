-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0096
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:49:12.727652+00:00
-- url     : https://prove2.me/submissions/9c34b275-0b24-4c9d-8017-5309a3adf150

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 17086337 ≤ n < 17266193 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 17087587 1250 17086337 17086367
    0xa08071e050102040b0703030f0e030412031103070c15020a0c0501110f0703060c0809030702060a050306190305210f041a160309091b020a02040e12040b0301090506100c03 75
    0x40d031990000e0300c2440100014003d0350480d03a201e040505000d8200c03040c18116800d0341c0d0074003c9480300c259000c0220341c08d8405034040c0808015071400d040720b184035540c0005015101c005441c03814003c1441150040750401c80c13400800c0302c0151012a200e6072014801803858002c004240301382d41c02141c500342c2da03980203012581140800240700d45800c40690003030f218140d540c111424850b83c4109a00e03170000d44d0100031481d080150740800c04030712854045504001c0d02002040483daa817145248855610002e16031015482c3d06009495103c105d4240122100e200107072864810018103451190048401d01c40c10320b46440440c4004420100001801c0b50003002065410034460203610a428000da80d0002c896041454000484035418044407107140031310074101c00c03640e00049000480d07506480114040c03442e0f846042c0740c0405c05134907542050006c034000c141d800d1400e0141d81200d4010206028503190242840f40b2002c2079114080000c1d8038100180201e03005481703035107603500d07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 17088837 1250 17087587 17087633
    0xa0c030e070501030e12071104050117031603050d1406100207050f0609150c0304090b0a03151d0a03080603060609040203060f040302070e04050307020301060816180e0a0b090105090a0807 82
    0x8144400940e0b20607c0111146180801e600225040c24803446001d01020710700103480425048800360b490083d43c9041e0351180002044004041c864030964500c3d2001d00710a211480b10031151461134002124118060300158007140e0f26288001740080c210f40f0040c0140303010124000500507240c2c400c1c42450340002940f1000440c1003070400003082003c0c40301c000ba41d10341d41060400c0e41540c4c00117505902c11900c1d807109201240001d012040d140c420b5000c00582c0d01030044045600e03000c0168010304502440f1034900500d81c100003d1441540304030705440460b5540d00400200301c3c41990065012303480100010a01580c449003150010b00a004031070000380d40720b00918101c5000c450480c0da5401c04100302d411802d090181d900a496090301a1008410075400c0c038407000e99500c01c072a00780d17070000c80c0c0b103c1c3c1902960104601d64101015a08400194140640548002e80700380f9419860a00007540c0c801000c1f804210181d03000c0000344c905851038a44240b20b89080e055140009 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 17090087 1250 17088837 17088853
    0x6060d02030402041b020706020609070e06060904060315090308011a04030f030203090904080903011401050102030f0d0608100b1005030106050a0509040b090103050f0111030408041203050d05040503030a0c030e070501030e 97
    0x1410801760801580c206500500860b41004c00085c140304018007868001e03440000e0034030810717000c03101071a0700050a48615885c0c0d5802c00004010704400da1024003280c8040341400049000d40e004600389074040d40b00c41c0d140366a40d00000c00e100613150341402d103e000900c0240001903115400c041614000d00c1100d0030015460b0008240383d100b0764045039031003800954000941004e00030f079841f01208040154880d850000040d480e40316121813039012030300010f0000780e01e410136407040000d4030490084400b5003442c400464002c003600740c03110340324010035030385c25a141f1f22500450303040e00c041c8e0f500d490a010001c01c041d1030f5600000551580507854240295090b00c403400428002e501038801081803444031440b0324219410036030007070b110140400411021803411012a400c441161882e500300504900f0102c0300c9015019115011500300320600c000d02000001130740c026140b0103c01c000e4042095405c1c1c0441e0717400b142010703ca420482081146600075130020740c0400752982951114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 17091337 1250 17090087 17090111
    0xb01090e09010b0f010f020d0503100305010f090204060b0301060507020103020306120d08060109050109061403091608030403020a05040203070c0b0403030f0c02060a0b030610090216020d060b040b0906060d0203040204 95
    0x42581107451100a07903403441040301c01d00e0100d00011a40c5070030b00b0103450800700e60400948402e01030303001109020000020821541c01c1d04410402160087e0080000d00952a40722010300000d480c10b0317100c0ca0400c800451810b5040341164121041c0342c58451a042c05a0b00540280d003000b0300841d0b21000140801140703280512001d1040342c00b41d1b80c0c411281c41c104001410728640c6800903810400940310500004d6007044441f241141464141038a80e42c070303494035904d854030780800c40320800040840054020000005072007a0780c401c4801b10b94190300c8106020407408100c03026800207642d840c404000c114112035a0350000e0091a01003165540c1400c41c02c25560135400813030059014808000d0040002d20030710f03299030400c6020784002d040c48042c03d000d490040c01144800b40e030004428848074100703107a0040da590301078115480a0041c0c10560002d06901c0d84140c041d50070002a0100781c940200c880d84140030040c05030b418071880203e403d0003500003d1049800a40e00d111004070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 17092587 1250 17091337 17091359
    0x4020a0902030403050a1404050f040e010e07080d0206010603020a1e02010902060313140102030603060711070f060504080c030601180c030609140103030f020102030c07020d152a0207080304090b0109 87
    0x12441c003175154941e80c0d007106038000304041519a80c5281109060109100d555181e8250088401c1d04446c0460840f80681807540100821110003d5620681c1c0000658040100c1c0c18103c9109580030b86d4116aa5000305405034441c00c801c1d0000100d88a4a8181c44035044000070302000d401d1000140f00040307580403654a80c4191641c900100940520004001c4542e80c000c0c55001c7c10b100942c1103080c107901182c2c2d14480a040c580c01d05c15030720340864049900700420340003411105031000c1510307a140c030084c03d664000e020380600c7c0d01944580d0030340c50900088450480c0c000b00740c00704800d015200031200900318002c001007015161240040c04560601070f0002c40b609800c9161110352440c80c02410340c84504849606690050041040c2843e490003512001034058a101000b144185000d1403d01c440008000d03e0030300e81506d0303814599110f01da031502d1000c0d05500c0f143c0c45520000903a6181458031400413660700030801409403035a41d4111210741c54060406044130b43d00ca07890404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 17093837 1250 17092587 17092591
    0xa0c060507031a1504030b09031204110f030d02150919050705190311060d020405030303071707050702131104030c03060c120b03030304021002190f0c09060806010e04020a090203 78
    0x1d803100124000224081c040c898100f10072100d400d116146215040400e001d80e1001903d0f580030000003401d00c0206108907110320244c0602e00b5240e1a1600d40301001c2d01011681900560752000c03c110301c1d027400202c50140c24030940040080003804d01d6400f100c0000240944540e0003885800c19480e40d2102e000303403001d8420030103403030070606020070b000142100110120011007421400c101040c0b603441c405c420240c050f2007056a800030188500f029202c2da900141d0148400010440815440f11201c4404001c01c940d01107aa00c1d02c600490f624001c01c0070180d8051740c640780c0710401c1140369114400c010700c1c00c01c1140c14140e40703850b06034500b00f00398415920551a1500d0f034210350307403201094440c080c2280c810000045034502103a0b80c0d01000300007e01420105040400d500d008200c1d400d0441105a46c0b507120082924040b42c20070703940041110078426a40000c592a4078a003d100d09451021000b0101a80381c00a56149010301800c00c0e600301188000c04908801740d400214 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 17095087 1250 17093837 17093851
    0x7050a081e030418020a02160306090b0109050606090103020304020d020d030c03020c0409080703111204080a03090b030412080c090303040e0106020c030c060306060901050d0c0c0302060a0515060a0c0605 89
    0x2840d4140d09070466072001c150018048142c10821042c09994800000804451580400141c861010182c02d80c0b07025070150a04a040c440d02d8000400c000b425000f00c240c840c4200d00102241e41d03901b80080950b401910490740c40304042c880088070354400d90142d54000e000800b217402521268012888801c50020243c00054102c0407410a0540422103c00f107080159400c21880708a80c1b909040c4d07000c2c05800504005d01a4046c2c241307014104448017003158840455980c45603590b83e0940c1c0c0b5032500d00101c011850a890029000c480d960aa030701c20340e000044100b246420090454007142c00602c202503084084c0088802e03600c1c2040508040c0031a030848011039410000068901501c020506110342d1003098441c2d82c40d02c50000762078200100f40c48050f103c03403003030005840034051002e41c1d05a0070f1800175941402d0764428100058513020b40c003910066105c00c11040b064030411105171010100480f0340020500300700c00100054121441c0854040400b66210b0341610000c1e900c0c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 17096337 1250 17095087 17095093
    0x7050f150a030b0a0f050112020703050d1d0d020303040b0a09030504080607050a0306080f0a0813170c01030c0c0506070c02010e03010e060115020708060112030e030a0530120907050a08 81
    0x7040309414012130f400040e010102c2640300d920b180c840024007081401103411700719500030a401c01094021420f40c0c510300000e280034032142d072440101c0f6845000061802c4094800c03450181703090360011041741c3c00b40d80c100003078424540c2ea1001020140a603008104c0401100704800a5030200520a641c000c3c0856500c0c05d58808050078001d0913108260400140342e0069402c0411640001550903e180e501c81055034585c840c0141c50072040100754013140892007011501d0a00c100045252034010600b62070400036142441022a007241c2c0300c99004055601c0311010810301030080c0d41c44641c2510524250300442d54090105c0d00351409541c9100a0754801c80050010b10b0030b60b056004400711901c028140d4034640505141d80b40700603c03840d42260312910701c0f2428075108146140110b030b80941100e60402e214545507944444584c00b4412071014402503008201c103a50b040059000d5220629003801101d0714841e5010502030042c0c001c40c4180c5d00d0000799525482880401002e1007406 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 17097587 1250 17096337 17096351
    0xf080403050a0614010605190305060109180603050607030e1f0209040f05090717030703110a060507080106020d1706060306010e0306090109020906040e0717210306030d020105040507050f150a03 85
    0x5001c28484d0181c100805200c810b00500b04004030348030101084500a1a0104054032400c00581d04417105422620340f20b0407841d0001c20402841d0130542c2282d1052040f03401c541e0750b807034080f0100e0703036481c0401080e908800d500d2920222402c0c0d0101c41003040c5040145000c0c00840040d080303a1415401400c0d0302e03210410030070801400c3c030003900181010302038030981d2081009a01d840e849803040040900c401394440740d20f5070400300046501c49070f000c5800c01c454100f454019004050034072580c0d0042c4500c0508900340c0e032099200140c0c0d105502000c0ca03540e250101004140d8200502d00c904010041d030018034682e44c2000100c0c0a03181c1d40d8000140c6804500500c182d60800a01d02c5018a00b0701c035001d40c0b01040011502c0448050852003d815049814007a05080c0c000b01c50144281910161a002d0360100300114010507045080310790440742507100741e0a0b14000c5a002c2c02d16000185c0411483c01c00e41b9041000101c01010700008644c1c1c001c9040d4142c10070010343d1700103541e13003030b03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 17098837 1250 17097587 17097611
    0x60a090b0601020705090a090f1205070b0709050303030708061c0303050a0c0507050304030303020a020307050a03080720100506010e090a020d05061c060c0507140f060c040e01030f080403050a06 85
    0x155240c01c46000c3c40500549420100403070302d50346024140280d455560b41081c0188801401502c03a1541d001e00d10114143e800314000340a600030202c242e071201081800f00340c40038003c40c007190403544007030055030550341c8084096a805800610680d08182c84804400205800b03a4001c061144691000103007820a840801c080b200f0640070b040074000104524004580000b0640d0111b030b40c10b28005da135624410702e04074214041c0b084002c0a0f88104001201010781000e031b814418044da03914401024102d10001a04030740207a0926103a400030422a84008200c0c0c0143ea403207101030402000044458011810700304040b0740800d400b6070b01055030100c505003805107a0304000b0456507120051a2070300c0300d5200d01c000440c000c4c03100d44d8540041d16082d0080055a4003035400404900140c0301aa400342e840d1070b03020402608a000e12800100c2c1e04a548055038156159030100001580c2155612030703000440650944884c1c0051000000203482000a189000e00c0b03204089603c80b4070003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 17100087 1250 17098837 17098853
    0xd15050709060f0203070b091e030705010f020f220f0308090a120302030409090314030c0304031205011a03180303010807090c05040302010e01050d0e060108011505040b0607020d03030608060a09 85
    0x1c2c1042c0e0800001161800c0c196a00000740c42c074068018040c0c034060740b50500450f2a00034407900c4840c50100845000300016001f0001e80095130080000380504041549108101d220300e80c500ca409541c14000340c48628046881c000b164400110615446601c500e00044030041a90046800b844001480c0d8940e042850402000f40140c00e00002c507101c5c3c3c0d64019449000d0f50149000041e0f445031034a0505228102c0e98600c4140100500e5880c282040400340d06d42c42260305601146040601b44ae005c01c280c492030f4100c0b0030000c4281c8030341c403c960240105a2014040000751482c0d0009001d01044c107100442c000c103c120300408031a4a02100038082d42c81071030324a4188035007400700304051b0341c1108403503210340030034642166140102c1280030010441c0d20480d408603c03440340082110581540034004c0511089040d2100603524030410041c1d80882c1d140782d4104c1c8051162100504022054244a510034240800d07001e071940409031901c0350072901303450740a40720140c800501c4008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 17101337 1250 17100087 17100089
    0xd140c0414010b0304030f14120106020d141608090414010302010216060207121e0302031305040e0703060507050705060c07020916020601030206090a080a11090705070f020402090d15050709 83
    0x107601c0c441400d601d44401003d4070b01006201a0a000940881d60506481074000350720080c0d0100000e6100c1c11072407503036014001c09029480151066611507190907004801100181c0740c0922000d16040c480200030710110060401100c40c4041031200b01c0d003a82d101e0260040c1d803400940d10810075031460000902e049010705014071126010350040c0101513022680609407401c2d0703c00041650203d1414844803018002003801c2420b0b5110008105903000c0006c180034680116105015078541081004a400341407028255601801c01040001c2090701720b5503201c1000e0405a0a28129854450400b00200d40b004c40000300000d0407821850494001ca8108072142c003181a03146001c0806940c0d807506020191280794040b804640130740d541c555541c042d0421030260380c00881185840f0365544117005e500c1d032142000e80700140a1500c135005403208182c0044d200b6083e400c2507020f12000303500107102e040d005aa0303085c1715030204040e1070030000003040c0300c6000920f40c070707100800612050b19 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 17102587 1250 17101337 17101361
    0x6010503040507092a0e0111011503170405030d03141029040f0f2102060304030c080405060403120306060305091e010b090408040312020a0f110d140c04 67
    0x18030601c0302155000608a0039641110300000341e080c1950503140c04014051004100410b0b01480c84628079030002c80c500d920203007a00c03910f408059200449080c1c541e0204003200d44c0031100410408900381e425000c07400d00344040014038182d220408030b0b041410b02d520040100303441d400078482c244400050980d10100540060030054104803000118079465002c015000440942412080c000e0408440080844005806031107907100c543d041c080f80300f0310032143c100c1002c540d5000d42140c240c00b180040359009203868039543d5150b4098540e10454901031381d000c4030511003c00c9a841d03081c010070286000b14030040b495504404014281c0d20903420460426007040d05115080030002007000e410400b9406111001030341c0340d45a030040455040d145c0d0300410170410310041c03204180003081643d0151407449405480c5034800d907650402800001d008000d51990700d00801d0700c20400058171000103241c4400f07103c490302c0b03906603400700301400c105c19004161007400310f1625100301c45000d50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 17103837 1250 17102587 17102597
    0xd0503100e01181d160609090e2d010c0e120c01140906090415061805010206070c06090b040311070501020a020f010c02010c050303010f0f05061306030209060d05090102120601 77
    0x810314009208a560391048070a4003a262080b070001084e604c02d100c03048030409800c030b40800300319101e0700300101c08070b11030100814107060010460341042d0044a00d080d04400061544c80c03510740d155002181c620001030401c010400c2000d2049070f00303020b0009190100c0d9a4154805c0741001000480c0980945102880e8000c10281003da60404119221082c204403520b440d80b80d41000300e0828419194180d078030a241c42c0031102065a801c014405a80890781e0700301d10040c40828518100d800b9004803409030b484080001c0310b02d41300314660f04a40b4440d400201c1d003071510350b451800058066804401040e5084541402610200900c034002c260910040104104c07640204038144410102503040102c8003400100b564058003450a4850384042200d50329a0348140009602078a80201f034403001a520000805140c0a8140d03452041442e41c100745031450000b00354000d41c812070109030014000d2220030f1581c11148920741c4900d40d000000f590710318074424040300c03401d801031600341481 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 17105087 1250 17103837 17103839
    0x6030f030301080d1b050c1302120103080705010b09131211011b030f1109060708040806010303020a0b1003030203030612100609020903070506040e0c03070302040306020a05070b10060f1805030d0503100e01 90
    0x42c00010510501c42e800e80301010b01000108d600c6019106036440350f01e003035195000000c1048800001001424040c4008004070700041041048450007502c2d0b22600481e890740a401040c003d2080b0250403905080580140720700c0c060050940d800240704184180010980c088980e4050085000003481440100541c1e60040d026005030300499504e280181808a20403042203c9907003190081c0c8282021070342950b030340c0d203030081d40e8501c010003c1758000c8000c0081b0701e446008025003400e4030f9041d0003031420b590f64074003800503800020003003084502c0b840002c03030000011440707544040c1c4403002015a90700204000c5c940f0784113040d40214081c017000c00003042850000f110003900f0424032152076a0300c1d00c5501088010380241d030006008184002220051641c00c4070040c45070600c03a0117100c440381d03100203010482800d640f0075040030410381e44400380031501c9141c0c0c000402c0c64140c0e106c3c012507103035000b02c1e01c0c010f1b01c80001008a60300005002c051281300d04064001c0a038401d900003070b9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 17106337 1250 17105087 17105093
    0x210c08061918020c0f060109060b040506070b070e040e030405011709030702060d14010603020c010c08091c020f0303010602150109090c0303031806050f0a0b010e030c0906030f030301080d1b 83
    0x31145922804034900025100c1c65042c0c1850740484040c0b1403403804994038a00b407a0300391903c0b02c0e030a100c1e404009140c0f00c030000348080140180c03000c03030724020b1a0b80d00b0a10030380c80318140900c0080a010800840c00c0d030385130a031ba540c0e01c42c0e19003040108000350388413420500090020803841c0c40002c03600001f0b00030003c00800000482e80c9199042d03540c90f132104600242c003400381001580702050741e410a8004114164035602520b0000181c400070300100d070f08040240c0c1e0064007a18000c0d944d0708805a143e8100a4082400064605c1e42c411204d00c08c0c40499668151f07007081c0c01035801600084410110001c0e12807880f0301400c0744401c01c01110788581c1d909690502948002424580c840810401c142e0041491420a9030402428009440d056040c0f03298603c0486150000510b400c3c02d64402c0d5101c0d9000c8800e4184c080c0041111080c1482007007440d8800400c1d141d0315100d0360030704540600c0f06001850080090400400c40810f90340800385c1024030816040b00a0701f800e14214000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 17107587 1250 17106337 17106379
    0xe1c0804050601031101170f0618040210110c0406080105100f0e01270e15070201020403080405060d0e0d050702010f0e01020607080901020d0207050a050706210507210c0806 76
    0x45075840b600034864501080010f8070101200f5110320b0380012a40e0810030380ca4660702d91544031b03078001c075501d803080ca680e80ae008180f1b050648000e034000100300c0d0540d06a5015916002444851404442c1e89005843c0010141ca0013604941c241d42d440720705001c0c4035004002c001e0080c0c07590a1420894038106004440700c40c605100e0008000d40300c11f54203001c4900d491101c01a042c0884c030500104240c26145961080004241400c000c04800050718071803040c03081e00c0a9a5200003024500b030300d40420446a90080802500015507401c0101c811400400c24142e4421803a1a9142c40300d25038000540390480d040b07040d50520282000802250ba800700d00036520098604081e03685490300c9240c18020b000f40700c44d806915200068420a01c2000521010703072034480c0040307801c420b4031040101c980004500c0e042810030240542c508150020340c00407a030000040c40c0100c0d0440c180b4540c0070488500c3d035400300d00255103031a003003d1903510000d11640400c0c00d4920102128060060b514 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 17108837 1250 17107587 17107589
    0x70507150b120a020102070608060312090415170f010b06030609070e10021609020a09030b040807170705010b0409030503010611030d020a0509030f010e030a0302090103020d0e1c0804050601 83
    0x985000d0010164159a84100c00740e000180480b001403510054460f6100d01c20001607000d4400c0480000c0d955204162040c440c0e000500070b002d2868100c40421000e400100342c0310b17482900c0d4801424882441411100206080d592400040d1020415642400100c5a18104e14bd0405010080980710030086a400c842c1c196500009513540b104200d401401c0800c070694000d00340c0c0d01c858401c940c009890340d1000700c03040b081e4407002c0da039140c0380c4205e114020404020501e520400c00119011a51495000e4001c4409a1504640740e51350300f12030b0514092400349035004195042840401d124882c80520260303070410483c155074030007030414041441450b040108511135201ca08906000340c1d4501543c00d0400d54450281150280c82e68110798a1a80603106c1e003808510300d10707014010800b120046001440c07500c014903800b240a5409414000e05040d003c00c51428502c500b41300d8413980700204809000c020400a40701400500071603802030421051030144004076001049142c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 17110087 1250 17108837 17108843
    0x5030a03080603010b0a14010e0901050d060905030f030a0207031b0b01030b0a0204090203040c05030f0613060b01090302060703020703020f040e100f0912020109120f02030d05150402070f02040f05070507 89
    0xa10070b40c2c03288000ba02610b4882c0700c00350483c00c0114000344820044022012000f8262103821206001800303128030802c00340301c0d031940310400f04242e0000c95229400342011500031419285002c500c01d009140b280e20640d1305c4980c05a000030340105160748200b103080a02100707004000c00c0d1100391202d1900f401c0600014024001c5500800c2511401d40d040b9401480d203280c017592a86428246003000c21480e01c5028082d018000c210040305101084003032090461026207180c005a9440350001031000414a074180044404003201685e2020082d242c41c611a82c010110300b411407041c4801c6c0441d5840d030178040ca05051407400700ca6004510304404001c1d04500045443c00c4003d104080c010142000d0034a288002c800c005099042d00a1071000e0700448008030b40e01030380141100c02c0058401079500580081c0610a901c0e401c0703400094200025240c2031040140950016080b40c0c01904111003210400034081e0460070b05006019143c481000100704a2400c51005009841800c00c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 17111337 1250 17110087 17110097
    0x2010c111c350a09020105030a02070c0317030901060f060909180212061b070308180f0d0201021312020f10110102030403050301031406010303020d14070803070905010f0302030105030a03 82
    0x6042054071641401034150025840716005412102007454400080a410002540107000007007050700783c0d008002c004c0b54182c0d01c2030f00c0e5646904444001303400021040b903940700c0c40c14002010078424007243c141065061406680c80c1440341b602802c5501a40c054a40410540c00070040150082c00280460b01c84c0d070004180d0290740c000e110f0741b4032204000298014088042c00ea0402400514203114032001309015054616200e40d013a01070003000d01c0140017400407800201130420180011425680a404482c81030803421041400c0c21414107040b00180c0d4041400e0b0105c1c2d050b040e03804003e03d10f40e00c0b03070403041400360040b502d0020b0784248a4081d81513820643e0702240329805404092042c00000c644034101807400074995070080c032090b83e02c00c5001c42c450380c0070800841c407a03040329455001004100c205a40a071a102e01300403034004820014400c10001c1014480290f2141f00140e844500b907508002c005030903d8240d800704030030940305200600035a02c001407200480754141c204 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 17112587 1250 17111337 17111383
    0x6042003180708030316020706030b13020705031b030a18080d030209060c0a060207030e042a180f05090906040c05010302090604120605010923010e04020a0e010e060102010c11 77
    0x4a20301c2c0031401d60182150b448000100007115100034800c192810865003521541075407208e04400313a034000c40500360700c01c010220013121240031340d005046071449036084d03a007440c0c0c200c6d44a103d01081504035482a400001e022042c051b403080b401c1504484209180c82c03024101105c280e170722a078001c030003000d2550005000b500341d61030340b09840304a840202100c245078458641500031307410100c811000304a20328140341480c509400b4405c80800d4401d586d103c042203c50b80601041450511a0244203c1c5280300410340c1da00c603404005865229014100708d841d04003400542c400041205220f5080b0000b800700054640e014042203c03400d180158441490f40300040b818400d0b540b1584602e00c00300051b1081102a810040c101c0b500c0e40300c200303c1c642440c6860300090040201c1e00420448100041c010003a603059005c0d001800900a5080103880d12480002078000707801c164824a0004c04024203580d090043d002c54030050f00d4070b984c0c0100c0c0e030318a41d0b645400607010780c00f5141c1c1d5404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 17113837 1250 17112587 17112631
    0x614030702010914030d0c0f1d01091d060901060503070207140112051905060103020408030702010305100b07050714030c090402120a06020a110c03030f0a0c0501060503060f06042003 80
    0x1101e04626049464561213403940059581d81c0c0d1304c40704010303100c04e080855441425000398010080144240c44803401032450b64881c0c0c580c0300c4800c1c04c081c148401050041500c0c0400074802c1c00503500031801c031801741030200407c000860142c1c800300030403104204000c2216800304605003100c0002d0801c1c000c41052170b00507102481d0064054040d03a02d06004c0104d8843d03425210b01001480c4a000c000f50740700c0c03a0044090b803080740944c0030f6a500030400f500055100f0741c002503000ca9200d03111f032900c0d9100c40700da603500c0d4271040c019138040d400340c0c2007848100002a107104181408030001c041c4200304101207003520304000d00c0a031080c0602c403c4000045030500c070fa0048240d01c410115071b5030304205805410f400c40e001607071046100c0c10a40c8a000d0800000b1601800e104540e040c1c00c0070000300c0304075107075915444211195520b03504005a552010003105002d5598082d0310b044916080040c041107400060041500c81501206800d2616894003100d0308060b50240d420100f8401c04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 17115087 1250 17113837 17113841
    0xf120c090c0d050702070e1504060305011104050102060a0b030703020904020d0f051b04021201050d080c0105010902040914040c030b0709030f1a0108030309060a0c110124050a061403070201 83
    0x58a140c01140000801440103200c400a110741200314008106603201e5140407a9142000d005160881c200d0300e020860040c245495894441d1005101207441501c1303603507040c2035072085000c8940c0c44a01080034401c2d9a014044554010703001c49003040b03a07890880c0066601c119901c4003a00444207500400d00395150110f40c909015002001c04613070307403154980309649101d00d02042d440040d0001c100341030792415008803001c24076205e082650690801007000803242d0031b59003c0b6510702c000c00441031052028003035580244103408005031594601544032040e64400d240d2000c0c030003900781c10040042d00c40c0c01c8201c1600d800213424056540d408805851016043c0c0005d450a408081520204905090300301040b011918a900c2140d9031240f0f010741e2400240c0c0c0308101d80d0803600004900581c1d552040c404410180350402142c4440c170b0740b150846407c1d074100d0b0107040c081d441c140480c40d13501100c100207000070351716001070500d006c40c02000d00981900d58040b250000000c204030324030035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 17116337 1250 17115087 17115103
    0x1403070504050619020106080d200a02090403050301050f040b1008040212030d02040302030f07060c0f0203030f0309010b0103060e060604050d06020408070602030a080906010303050f0c070807080705030105060d020f12 95
    0x40e01d0143e888140d440c095454403109a8280015801c0c1400030a0f442c41c045200c0079290304580310b44a102c2b82013130b103911140d10b051190403d188500040d00d0003591f51400c50340d000d14020b44907582d80394186418440384070040c1c000280118100304c4140325070340703a8910105084c1c80a241502c1c16413581c0c80014001910849910035520011803c080c80681940c02401282c2c070032011208895080c1443c1a06c1e840c80e480344001060591074030501040400c408210304500c000d080e6032520170110403c20054106a07103103c0c0b03c0e9076030031200050f541c06114401c080c020f01401d1050700c0c640b642c00250244182e00481c2e020b000c151109004010781501500c02519084051f036400540300d450007036413a00b15207078503800100c02070007040c554400030441905898041d41d90300c0c500090f40d441c000c503079804039000700e0300e61284400000d80744030b0a000b840c0240107880043c140e041e01d0a0101030a40d82e0180407039204d0351003c2c0300b000040c1e550090781103d174402603c01180444602c003242c0d080c0800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 17117587 1250 17116337 17116339
    0x3080d0b060d020c010605040525030f050f0601120e0d030f0603020a090903081006080c0c0309030d091806080606010f0c050604030c17030906041407210308090607140307050405 78
    0x482c0c090a501d00310780107001c3c080e074040000c01107075941e0020002902c40580e020104207202241c2100c000c030800d2446401a003140c14040303851100d90f50008101c1d030701140c1400304900150188143c0790f03800942c1042d080b100c44014043c40301c03e8448544c0b42c507200c400e03100a043d60340184c0c03005029203400480055030000d240324101d5a07596200c0b4040d0800c00411400a4545400590140c0400a41005030b881d0303039480d29141d648144001801c2d0784040c440b40d62621041c03100400503503080003030410460080e550018102d14040c00c1000d0303803c07503180304090030341803100901c41e0410005095078080001d10b40001680b400c2c8a041c2e03080300c1d62803005841d40c06010300704014581c0022000c0c5010384a80c241c8002c101c00c002c4500300d107020a40b014a4035410010228003c40c2414065002045180058841c02031b500c40c4101003019101208107141c9003003203c104185500030440c0f9a001c0030b2171000c0c0c01d2900d4103140c02002120540c40c40d080b140c1001c404500ba062040c2c1c1901c0c0035281c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 17118837 1250 17117587 17117599
    0xc0302120106030c23030708071b0305031005060a0309030305090703021e18010801020306010906090e1305010b030304080109120804050d030507021c0e03160518092103071403010f03080d0b 83
    0x30145c01001c07503910480300240401c0310720000c1000c02e0b101c0c1c00c0c03c01500088154500e0a46542e54046905a001401c03a8000c6001c0010103c1c4640e2f4100c010048010b0310340340060305003c245030140940384001c0c800d48041d00f0446003000941c6840303c0080280e24034414600640c1c00d03e0b000a0800720aaa110f0070110101500100e0301160540c01580680c0091b2503805545580d0801220301030480d0140c4441c1c60580301c0415403000c260f1070702840342c81c0f2503030001c540d105070031000c070340385800c180c2c03210103542e46840b0441c3c107210b20042c031501600032618000c01c0394907042d00d949990301d1071a1844002c0580e5240003c05030f03032081c45814038400d043e000e80c1c001078a1145009201c003c1c2007011030720a00600f0300c4c00511012014220089500241505a090b801c090940544074002040c02009004900411041210b4074018100035110b6001154413400c14400091240c0d02800b10762400386820001881180c030600341d100d04482c5d000364555602c0a0701900400905400d11036a60090 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 17120087 1250 17118837 17118887
    0x313030309060909060f09090f080a030b011103030c040302060c07080105070f08070e010207051e0406090204080607020c09040f0f020307080601060e0303040b09010f020304030f1101030c0302120106030c 89
    0x554810a408112046a0f98a4040b603031980030040031034a8034070809010702d10310380d07041000102075004900d03024019500981c0c04005c0e80c0340d031003550f4002c2d4645400071b55249685940e640c0c11040c00d100c0c01007e14002c1d400c500c0d020300060894440c5010180c440e074000704418044480810200000c3c0007102d00a00c00340c01c08000162a908880d9400d00124016000050800b440740d24291001c0c03105900130651149000e0034025480c040101100b0750416501c08098180c48034003940d0020501c3c8a00143e456207010071013400c22401402650071500242040c0e1a95a102042260402c0d0400c2540c0514003040c9040e440c0103851a10003505409420760004000d480802caaa04230745040e1220000c5017001002c1503164400c42c00345074900f1006001e0040c555109002c0698112841d0044030b25054a0b40c039030303901c55410380100725080e14400d090036034156031500a00c11a08151305055090a000e11000308018205004030410540d448001824040c4500c084c0e20890f00c050700200c01034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 17121337 1250 17120087 17120093
    0x90a090204180b01020c01080105090c0c120408010606080115080a020c010507121a061c140408090a0b09011b2105180a05011d0d080a1101050c030907090e031303 71
    0x1210607000b0103640c0b1843d20f9403140441d400490341c0006101e0503951480d10b81c2c2000100310100201500000580206005e0500840c4040282c0311808400382000d544552070f00074594256006508a841004240001003252403075004808051b602a81084021643c640703041000900546080040329820311083c41b442c41e80000340810039160280701809190003504648041032051000b141e084681008514059035100a000c842503041030710205141000c088001036511003a00c0c141c070040d900040c0ca26841c9400b4401030024040701c00c9140c2040a101c0001e4072201590740390b02d0242400a44078801c003c400300f0b050314968098841c00007160a0a240200305420100300e00c4e90798200410340c4240c07842c000060b0000c0390b6059650031488800003a00803011605d0401035500002a40022000100d0103800380541541d1951341500110001849a094441c00b41c14400c0c05442081882840c081c007043c0081564261440400d641d104c0420305071462044001c2001050100315000c410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 17122587 1250 17121337 17121359
    0x30916060509090f010b090103090212010603082709040201110c060d060e010506070b04031211030109050403021603080a0507110409050f070603050903070b0603030702102c06040308090a090204 85
    0x1c01e580904451340c0c2c4501040034000e0a000d200b40c41507080c0b2542c6415842600089240e07031001d41400d01b0003000800141c00d40c1d220340c008580407880031802e114010b0040d80340c804e16840a030340c80010b0305080004101d4100300608082d042003684480c04003250740810461741030420240085988070075840420006082d6806446a0f60b58410300004552806905a030641d80d0000710004040e11955016a00310340c2e241d10705c040190306c629041c0300708482c00303000c3c44c004c081000c80481e240c5064a0000e08002d81c511042d0112030074040c0920124002e20f05036140c041036820041c0d07a44d41142800d0070401c4444001c168000d00700038040c400c0200103e091040440312000700c42a46455540542c140c0300b048940020550041c4036210200d0081101c1940118002d002d5910340409600480e1395504515020800b08019441800161100032017803c7d054418441c90301c3c4840c62100010014803652002405898010916000d035581c0c1c50034000c024000c4050455813681c0c0c41c50a019 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 17123837 1250 17122587 17122597
    0x60a0204060e06070213150f0312030e01052a0c0601030c0305010509120d09020616060b01090503031c020c07081f050106050301050d0201110f070905040b09010207080409020309160605 81
    0x10020701c980140c41c0d00b40c107014094a44003030380100500e11001010300e240c40146119400940440c81c0c0b1503001481071036003031201000c0c5000c0c140c0052201c054450240c00d44039544001c02d25603251a00f00700d04c0c0c040007000700c0c1154070240180d00c1d001c0c0c0380540030318241c0100d4581000c0760081500001c10001320500c2c180869104030700034800360303540900c0c0d00c0d21065500c6840d6003c01003044450054403c643c0318200c030314030042c07000e03050401016407aa490301010703208032000ca07176074400c0c01d40d50b6801c1107104d001000c0850055140c4107003003140c0a00c42145908001103280c01240c42800000244200c00150030003108a501e0f03242c00d4128500640341c400783e8020b82031300d06000403400a100300d003141c0c1602e6028000d21144080380c1d004450140005810300e2003405100c031407041104080c4805001005580030100d41401d00d800e1000d42c584001d4200146a88104080400038611600761401c955a4640043c0c803a6944800d040c140762682a80308105220704101240b46600440504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 17125087 1250 17123837 17123849
    0xc02060916080303070e0310020a0302030402180702030d05040f0203191101030204031a0403090306021303030e031b0913021314100303090b0901030b1309050d030501050d03110f060a0204 82
    0x52072050700d405821410455034026410715030010800111103d000f140c01090181002d8220381c0400422001c035401c030f03000a4184400a9000810301081d80341040751240110208819021141850b6002956038442c6540240d07580e46c42e40001428080f185800401950300507003a20301909c07580d240040d0300d001c1010201e80200c18003502440381d5229100791400e9991080c204480924210000d0b40c5403040100121708100d49001d001c00040ca8600107031508003442c841e000100c03401c41c90040c0040408a5200f4000c0d4013038a048000c45030710f0304402c82c0b0408252904c511940f10036074a001056018600a50814420808e0b48510030083c0c1c4040e03d0100c41c0d000c400030984800c100103810b001c0910010b800036503010303410700c003682c0030740300030400c0c04814100000c018140101103201d00360a60342d210043c40d40c90b5002c074148001484107171000d0700503260030030042d8104000242c2d011841d450241c00c0000072560402501c800f004288482d50401c011140c2c0d078a4041c0504010b584103000c2c036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 17126337 1250 17125087 17125093
    0x110718020901021501050924040e01050712150308030424060501030606020a0f080307200601140306061e0d0c03060e0610030503030106050a120e0703050f0f10020d06030209070903060b090f0a0b0102030d0c020609 93
    0x14505065143c800d81d038fc2c0321020300c01a070b0010300e1900c0303110130f54102810650b04086445e10199001c20001d4581400840540000c240a80303020700240071502035500220554001e51010703c0001d1b026102804659030042802c0e40b641c6401004503180c0c61122101648075640c00403400402500040340c504840000b901032010444d14414542c51f403c086e00d10940000d207524683c9203120103507002c4074060b60041d0050f10302d400c003500c0306811841264400c3c1c031090b43e100407401284a00b07205003030b444540054401100391a60f610f0956900c01403142c00100701c0b01003903840320180316581c0e9841e4043c01807001d1081c2030420010316161301c0e851004071581c1c85070170001079900070081144204a4203410140408000c440074440107176100d40003125071240c0d00c82001c80103980d040123490081d4410ba131020619411407038654101c03808545e075184240780d910100460085001e2200340d101e81d1080c80407031284000c10050f032450007800d80321941c1c03508210900700c104d40d001507514480c01c907010403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 17127587 1250 17126337 17126357
    0x60b04060507060c050a050901080a1e05010e1012060203100b0319050115050406030b03030405030d08070e0103020f0d02090103200a02061302010207030201110718020901021501050924040e010507 86
    0x4c2a80e0354803503100d6407408078806101510080d801080c004d41d200749148001308a0900355a0f507019a60103070580c00d0003a555440040c0440f24850101c0c641c4110040310201b401800c01c4080c000d281210b402c000d01c0e0b01c3d000800901209002c000f0400100146050b10307489042002060841c580620448601140b61100002d2045580144500204c0440c0c942d0b074a0303e03080c030304102c01a00b8040c0005406120400001031183c03001c019010454407603075180c5402e4100b601008005085a81c5003d04050040c8503141c252010402290444600c560f00141d485c0c5841006030042e28045000402c0044500d96840301ca49021008004c83e00ba9607003560016070781d410614000000b501000390059112803010720055001e0550b810002c2800d001701d07a180e1b82c0c1c80c1d0352044601e800700b0721a81c0380ca401152045072540c04215061602030b1f408807041c415030500011500c03140d4010103600c0b52841d1042a158034110250221451843c042c0003031100e80d03d0518902e001e070106a806000080b44134903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 17128837 1250 17127587 17127611
    0x909080705100605090105040b0111030a1e080603030f0a031514010905040509030d0b120304080106060e060712080703020702030102040f050a0e04030c1106120405070f14060304020d06060b0406050706 88
    0x4983d00c01c1e103400500b500103590801742444010001080c0c458107006407490030143d01a01000a4400403041d03030f9514040c01c1c0a600c20480d2044c040e2140c1007442090703401e00540f60380101c02d40d4810024000e0181d180d650444007180604002015107442c50050200825103d100d0f8003091500c00085c0c0780d030503a4680c0d440501c8110f5500b00c0c0e007004140c000b4040725443c45407581007982c1c41000105a040c5c4902c042845170f0455000c0e601a40306691740340c504000d00794008000c9070049a0494200b4288400c5480b901426102c009000c0104628031f40020003c50007541503810070754000d0001c40d11252219a64229102940649071003401995000201884401000b074071907541035445c1031004410381c0c0d1340241101c6944590360301020a0107038200d8001c03030070650761286000b8401000550701d00b035600d1008070f041e500840c0b20f6064400c05e1490381d4440d54100d94001d907060f41c0800404585040c04d4004000c3c1d41c11046900000040000744180e102c4003801200d4040c0c981001048001c01c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 17130087 1250 17128837 17128841
    0x504110a050a0302060702010203090a0b090f040504080304020d0203030f0703020c03010f0c1409130c0509040e0c010e1201090c121403070201080109150b04060f02071203080f10090908070510 84
    0x701c0368942c420724600341032006007025409051940e10600459003001440400218070070aaa0080340c80390328080340710126880c0c0b001c00240818400d460030045030409480d500124800180047d0160b51520780c41c80842d1002c004940030505404034194a900ea18603000751107948e100140c6109600340004051411444d04c074055419420761038105041004122030411500f00701424ad41c4604c00ba070f4a00d0b02c241c910b02178070115030761541d201640c503540350080004980c0301c80c10103102c80d403200f4524044c03660004a04c0004180031586115078080c0301d03035510b02401680c0c80003043c000b0b09080015202d8107032000014101d116011060342e0882030b07a01c040d5030f80150100680022042001004018202d921483c499041c0c3c050314080c103511201c4030141c2d07034041d61090002a0108090030046581800b1020103802c845204d0140d05001d034800070700d0200040c0248da9144e54000100d07840d07040e01c00d4080c0c01000101006c1c45941445c0c01d00c1d0149800000c0240c4850140603840a801d010034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 17131337 1250 17130087 17130089
    0x603050c0901051902010b04020d05071b050c040b1f0809070b031603020c0c03010c05090a08070807170a050607020d0306060215070f02010908040e0a0e1207030c0c05060a030504110a 80
    0x60b9103c0b0300344040440a134000d41803a2488409655032100e401f0a161182d00080200010342c40010801c1d00b0601c4006107a1900500805105282c44038484009200400c0c48a00031200715404038112241d00c0000e500c404210f606410072a105850304448641c1010b140d9114244640c02c1c0e51045586040181007840f04071020480b8850848140c40e04900039400340404100311005c840700c44160101003801c40e00a00103110100710302040d101c0452802d0001b600240403a40003828030741349401d0200d45d480c02e2501074407080b13918071481c51080ca5010410f0545850300701046402e14100108040e4031000d04401d1200000d0078060042126800007484400810348555007041e00c2da210242124003000c0b9401000840d52101d03030440100d034190014001034682c820100f002410b00751010411a401040d04020036007110701882c103030714001001d540103686c041c00d1490340580b191415503c803d4003500003a500000101e0b4564803c0d605a000c1ca21540c0705480380079a00c05444204080300c801 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 17132587 1250 17131337 17131339
    0x3020108011707050d080d020703081b0a050f0706021603080118140f0403140d02031008010501120b060607080c010905070f14120102090603040302030a02070501030b06030c1809100603050c09 84
    0x103c0c0b0108014200010140c80b01800b51000e1800d182880b07130b0354800d07a44001070580c0000c0d40340e0305008010b03414a2203e1550220308601c0c038a0f19a414501400500613125180780e501360210b95403060101d9501190740a030072140740c5c1000341c0240d10340900001c00038000c8440c03164103034060302120400703846200e007010001e04c8210003a594010710a060903400402c04c80800035075540605404010401400180c8855080507880c5e19203031080070491000d82c0d001002c46d0303040200400a208240c2d241c178018540011800c801e80e51000c011407410708c60904c1c01070610500050101e003482041d408000303024445e4082c0c54429030303100c4100b201c000c80ca01a64008840c01c421000c00c0e4a860402e40404134250b10015060890210010f0800d420841c4e09901580001403c0c42650f1f506000348030140009007400c00c03411106c1d8010030391900004141e142c0c29480003070040710207829400105103804008100c6003141c0b40c40c01603c2c02501d0107126080201c0e0902002c1004484c2c1c000554034a500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 17133837 1250 17132587 17132593
    0xe01080706090b0f09010e0a0f06020606030a030f0c03020109021c06140610050c010902190e0a020307050306040b030307050706030608010c020a0f08031e0103241503021314040b01030201080117 85
    0x184c00748080d4150300c900f090794140030380c03542442035039200c02c850314008004c440104505240340840290920b82c3c010401e41c40780d00444900000aa00701040c200085440e03c2c0003c205541403605900410284002039407060312180e148002c0031008000c0b4a9040c4507810074840f151110b40d40d0781c20b64205461041d48080301d0070083c460944101c0c080e00500402c180003041c0ca5441344c021400300340c8075010403811141100001e010303190b403000146410240c44507045140d4500361b01c00400c03c2c00050011841141c8800340710031283e40c20410303542c44070380103000d9402e40d80d9514000350052010b441a41c869500f000251b024050020410500307141e0080c2e03aa07000c4801a42d54089d8030b034030050500b080c00c1010b000c01140f00004054107070281d84103c1685c1d241004030700307001c1e1001040400d104040d60400354580300d10026141c0c00011a41d060710365030342c01885c0c014200040c0484480002c2031600541c10001401005500c8074101c80c001e8850542907620380c0c01200b40440300e0600310095034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 17135087 1250 17133837 17133847
    0x20c0303071209210302040e011d0609040308010302060d0608030a0f020c0a050303031504180302030d05060a080307061a0303070602040e0106171308041805040c06050c121b03040e01080706090b 85
    0x4c0e8011a00310060310603031070300502d49034682c07040b00e810302c0382030b040720b044a46464000c410050480324400e8225108852603002d070b160035680181911414040240127480106d802049170103640c004c0400341842c5000d403600c551146500030300394008070074080018403507000b00703011130b040c6003100d0300680b480500035500e16036950408140705401503d0b2590060390b07441c6170031801141d801c521030313a2901c01d5010319a0340e41d842c20500305981014122a1086000710420000d6090000458400c154080d5005c10101c10001c8600d4082c2c1a03080040d03013501001501707a0410400303500030000d440d03030358402a6469807190411108100c0c00461092903685890216450b4112a400302ca0058442d5000c1480d260b255000400d150031f0101405030031036180c0c0203000402009041c440c01a00051a01e1800d2484100e00c042c0d552000b4010521540400034202d50043e649807076202004080808882e51035076203101c0e041024a0034800c1125501407000c1c04074629225030580811140749200050400f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 17136337 1250 17135087 17135123
    0x30215070f091a070c230307060806040e01240306050a0b01091214240a0b0102030f090103060b03010b13090c020307060b1804050304061407050706030e070801020c0303071209 77
    0x1ca00c0d07201d0032400040b018040d8000043c0d000e40c454020300586e24070a4410440b5044400000c0c8a150980f031103908816070034042c583e48541c0c0a6400b01007160f021414440b40d0a11758014030f5a1f079845943c02c14200c41c0a410125411a03020840748a141c1c100660380d80d40c1004411500e00c250014001442d442d81005091001e00700e559409008440780158040141229403802c400d80b01e03903500740c40000c56444203c01c3c0521107035902070000b1105204500580c40000d45920034848220b415500c00b240361042c40c0d209138441c0e0081d180d051034840d40c9503180c042503203444c3c1008403200e0f00c1101c3c1c1580458250040d0007001400c003000e4008504080483c0c0e24900030380070441c100743d04002805641700c1d405900c03800641c003507070084000d550b4603420410020400b01b1014115440003404000290000394002007020031100076240c0011050b01e1660f02604210311503002401540c00410001800038000c00114002c0c540754075a40560340c1c0c004005410f64208007130103860070545002016107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 17137587 1250 17136337 17136359
    0x302060a050408010c03050a0e03130302011409130509010b0d05060a09060b0301020304030f031a0109050405040203070b0f040503010c0f0816230408010b04020909070c08120103030215070f09 84
    0x12440031800d0207400c080e140c0d09520308443c0041d90309030021b611340b0b0a00091003003c1c4500a02848028003661070146110040b0072003119510009040100d145850b012413a800710981d49600790081c24601601001e6000300c010304020707541c0700c10035440c02401c0c0c0380518120301c0148015a00c0000f0300503d41d81c031079041005044045c000d40d01240c035640b4290481c0e80a1006620440c03280e210017010b000302c0600101242c441d62600c031108407624440002c41da0308032100104035001220007088a59861010904001e0158811204444080341c12071411805070041e009480081d4020484140d0b100c4045a02c45290390700080403e55101c045058510307040012408044642080078108485d00084031075040440e0200d01109000302d000e010b0101c00780120101e540085500750304201c0c414001443c0417801030b20940034051000082c5d802c00c130a40c41a102c0c1c01000180c1c3e14020b6070b40c0d00300a911002ca1102000944005000003007185010350407000c4507807595611044140d04100302450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 17138837 1250 17137587 17137597
    0x3011a0706021303050d080c0301050312070c030b010f1805040f030309020301090212100b0405090d12060b030411010201182006040512010e0f010c02030a08040807020d23060907030206 81
    0x38000740c007049003251540d1500c4031180114410f000601481b001d0850040000c00d01a010b80e002e55410001007107503503400148110741d4010039200c2c0303584184a04d0202c0305080140e02c01048601490000503802a0820b2003004580121440c03850400500144100701c45045074000c00c8813441300601d6012070711aa0065000d07030f10160002440213500c1e00081c030100d07802440200141c0c400c00710341500070903030300071620702a8055506102900b05100c2c0c0035120030a03100c2041c10802d00d0007060b0b200206a0704410018604031a030b442d0f07a42054140101040598809070b0b0141d03081202e0004410240313040907003e5500000048520950840500c000d201c490700d1882d4003070014400443d5541d03441040800c1540040e000082c08031108607c1400c180031480d20312031a03490a40c6000101e5001700440f94862038070700c2c010040390340b07d01d081c0603d80144d103c06504285110058410442c1210010103012a08100c640f0181c21100d0825940c40e0210343c0420b640e04041010801400d003100600307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 17140087 1250 17138837 17138843
    0x120309030a0b0402060d05010e1006030b150319060603060f1d0a1a04020f0304020a2c0601030617010501050901090e03070f02010e03030d0902010e010504030b0609040827120303011a07 81
    0x10b00d8032910301c6c080342c10b442c0c0030380000900404420500c4400d01003546142c00401c61401c0074419111803070000307002c64200201c18051544000005a0419080a00102040000d030703800c105c0c0c80d440703900c0107004000380d0060301d0780c00d4013800c3c02003000040da10004100141c10b16016841c1e54440000320f018140a01d068601c102500d01d42440e1030ba1580003520b910760740d0542294072441c0500400040c510254060310b4108100c02d9400e1400115a007090b6030410545841405034a803480101d00030400d50303109081d4aa104203c152841606401490480d1801c032807108250340c0b6070240303800711842d10320720491942c420031030030000500d10b11a840c13903a030050401810582c000070109095910244201c4c1401d995001c56401315030704103c80343c96030503083c6001424070b8159520592400030103001d45200d01da5000c0001e04000c401e80884094240d0b8220401000c01c480645c519604803084909100311008846d06044440000c107a0f812201c0c15416408a1810001c04030b0b0140c0c00f081c1d01f6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 17141337 1250 17140087 17140099
    0x90a0203271c0c060c05030609070c03020a0206040603050901060803030126010f0207050d021212040308190f0b03250302100309120e030d080708060f13060b09120309030a0b0402 78
    0x203542c003098122559a088543e00e0740d10800455141c071030200c0b00c901221106003d002d0041c8485615440500ca6101110342081503000c849400d007a0f16245100800030361041c000035005c6029681904418012001240240080c5441e5290140c42e40424052032804150201d150890400d040c16400d0702600f504000207a50300c0200340c1181660f11084080d6465844a40206186903040016203108192010760509081a00001d401d030400c0140c0042d0400c43c0c10004911081080300c2d0007000100054401c002301810481c0c0ca402510155040d90722074003c0c100e81180d1400f060700740141115944002e80542420b41d0f0070004e80d440c2c1c0b000e000d401c25945a100f000000c0844051500c401c495840701e9100c2e01180381014036100a8212282c10040b203034085c8a00f168101d40015003040003102c2202030b40207500081003c0e045280070fa18235035810070900094050710344001388034080040d1400c0203a406235000241d40c034482d4091240c6c0540c003008824021603103003070003983c00c584000c2603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 17142587 1250 17141337 17141353
    0x1060608060d110a2402010507120903031407020606180609220f050601030209130b0105041805060109050108060106020d0509010c0303061503053108070809030604050a02090a020327 80
    0xc80e50440080e000200c09030f09500e420f1803138040e05c0c1d00d080d002141c184028002442d0240340202800841340701882d86036103a00c05402014042e800c803006104950946080760b1400e00e10080d5502c00540b115801120614450b2000c00003500381144245d601410329549a16140c450300d0718003090b1849016080c100c5950b2500240b0001e0300390400301e0254004020030f5055004000c66a14041c095203040d000107000400010100c000d5581160421030b40010a020304030071002c00300c04441c5004015000300d00c00401d411240b43c0c03040e8141c9040e4021180c1c141e0300c604087e46d171810b0303c11400300417070f1061010209541c032035221001030b24440d00d00407601e140c2d1000c48034401da6401018001180d00c800c200449130030313441c6540030965402481788040c04105401e640682ca40840d020b405c0711000504e00007402701c5042160704c83c800190889041e440c3c40c0c18202d031034002e00042240720310070038800f00e03103d04014020750b4050f403a618030003500c40059004d801c0e00701000401c1c1031004d02820038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 17143837 1250 17142587 17142589
    0x40c03020a030302010903140316110106090906020c06060607080d05060112060e09060702010618050a140c03090607030c080705091206070e0301060e01030b01050607140703200301060608060d11 85
    0x7480e80110b100380c0011510b4030707071850040c000c00c20398043c03524030b95400d204211300079000030440e0b07074507035811f08005d0300c00011280304602414a80e0064a0340358104207511040050f154020000c007a582010f642d080e4a4000c201301d040d10540002901d0044c091210807100344487d0711003a0040b6050510000c81c12007085080182c40c603580c05000510140b2040040b550b8043c00000d80c0070304c0ba44000c004090074881d11100113845510001032050f0342d403002035011001a48412200c0000b451003d610703181c07810001c1040d500440350b1021324000e200c046a081030180c05001d904440e16207072407050f1340e20500111403a03041440700903840041c8030f00b1806008410b01c182030183c6001d554031030440c00c00105041c01d562082e880f1b815804c4170000100003207003003400c50030305448044039030990310600c40c20003209507001111048001e014400d40081004842c01b007442c40300711042e01040d0244540d8041600300c0f4558400c43c0041a03800d4005400391420660032103000d4442d9000440900181d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 17145087 1250 17143837 17143849
    0x5130e01050c040608061504060f0e0307092009030703060504060b0405040b010602121c0504030909021801140903060a0c0201020c01110301060207081c0507060b0402070b0103021f02060c03040c0302 87
    0x1903442c0408001c0060b050060507405004150310032000d0710403198126000710710040900c124424a800c104201c6042d0181c14843d8080340d02510000707003212011503c448008000700710220900030861900d11040c40700700300c0142a01d08002008001c0d25046141d91a900c001d072600520865101380c2c0c4a2800f1903a0361280320b414000c902804100c0059810600c01a24001080b414594400014030829900071284d002d4425411310403600850f140d00d55150136200ea1506410801d851400460b80c90890168101c40c14013009090340c9080c040006165405041c0c4104225150035800000004114020f10b0b0000780381070007144001460701c04121440b40c01c41700b05401402944000100402c6244d9041052030050140c00000e403860903202c540c20740c1280f446076098030500101003496014010f96502c94051801c010b80199641c0c9042c0c90300ba1800c01090000b00c1c0700b4080c0b040c00c1141c030384800c10402002c500079001070400c0d80703c2c0b400d4100e4540005108844411200c0004801a00d80b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 17146337 1250 17145087 17145091
    0x906070c0b13080304050c04050a0207050715090e0f071b110d08040812031509010e070804030c060509101401081f0207020301020c030d0506040c05090405090709020a2c060405130e0105 81
    0x80c5d0013510400014a023004161440609841c0c1254014480c030f0001c00e07000314401007150310242001d1030500c5000000c0d140c5806030703804442101d030742600b0441078206402c01144114566038403013401c8500002c44100541c1d81c0360010f0300903a45070000c011542401da010740e201070700609880342003a6031040200d2030610801d80068882e100882807016111618800100b2002d0444680e03880c0e40c1020f250043d00d1302c00600395020440b001021400f81402800c4500b00070b0340020044c0030a00d84041100c0d03072041c0d140340c017118543c50000004488140b0140c4035068032500d402070913041e988043c02604103010722120700d1700641d00704005c0005079000d00c02041c81c4079115000d5511604104034103002c680008003031a0151b03090821000302e41d6408012522420f4040300c0021306601e800d82c025103000d204e5000103405910000703c03000001d0f08840c00401b460345044920304403914a429440171441000f80ca141c1001042c00103000307510b04501040c01800c002c20300000c000c20780740203031400e507401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 17147587 1250 17146337 17146343
    0x30408010605040f090b04020607110901060f1704080409020d020f0309010c091202031507020a060c050c0d0e0f060702011202040e01050907030c021506030a02060c0102040e0906070c0b13080304 85
    0x1480000b0000340c106805242c01c2000e520000f004100c519440e11503108400803c02881590000b440c60100b1a80401c800c4200700c003d420450307203613142c50001d420501c4802c1c000340465850f5001840220a00031000c4c4550f5000e10040e08003442c2543da000690814450b84410741c3e020300c02041c0682039580a5840707120070200110740403030000c038081c0c880100380c2c00240030000207040d07480140e103000800511040364950310368540d80d02c0b246c00720b06018451000800715420001d07245099503000c00600140c3c8101c805036400d14485110035a107909580d01607940144484510302c1030707807501c2d00241803424010f04200c0c1800c00c0c070340b01100890340160012140725115000600050400d0106c0540c0310145040c1088601e8441c80065a103504c201e44040001d44113400086998070144007188401c7d81c09051070340c4480004481d18044c0d0410300614000360186000104c00782c1c400588180500081e440f841500800d41d2600151003000800079404003440c06018000540d8a8004611a81c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 17148837 1250 17147587 17147591
    0x3050307050606010e15121902030a1e020a090b03070207030503120108010c08060102031803070b07060f0b0306060a031419030c030905010503011a0912010203040b040317040f080a0306050303040801 87
    0x83c200001404015041e01e19034040e410031a1100c62104d10b0f0706c2161380c0ca4510f480495802c2e80c500c501148803001080a19008500210500400e002542c111400ca2000d050320030780c41c0c8081945150490090914010000d107120008000740d500440c01103400961034410b464495407651180d510b10391101944442c03c001c04001045502401c0c07040300c18a4000b03140801182c00e0001c0001d5403802040c9200c1040388103100040290b5804001c058010024400615110b041c242007200c02040c0102ca24842d0f42d09100700c20550703180120301184241c0700108409281415074a8150036401928400441c0d07100701000fa44400b0b020110005d000f0f4841d40e2107204003500c42ca001046c1d0f140c250301050600805000501c0301034445800d16210504c00b45405031168900c1b40018403c0128244a500652000003440180a425080184154001e490700303519070740504002d4130001c008841c00b4002002d002c200100282c4503070014036542070249000710341c0544a10009042d0350150340050f44c169 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 17150087 1250 17148837 17148841
    0x21e0a020d0908010212070522080c040f0905030f0304080904150302011206060509010f140703051b19030305070314010905011e050607110a030b160806030d0e0907020304030503070506 81
    0x41c0d840142d080190001d807000750f0030410021080c180b007420103071000341803180100303407041241d5200d4103899001900b036488154559071003c0072602d9400781070060b8069810441800c004000c6800b502a104d64064000c40c40c0603940342c0004626000a002141c0708401000b00140c15519801881070103103020b803170145014918400034000ea10074900400c207140c2440c4080046d0780d005002d80340b01000138200103079411980c40d004c0340e035001e0ba000003811441000c00d000080c1036220025004900004c203c2e500f4901620407269940c029030344500b407602c032210102ca000240310b0f070081a006100c0781008038419002050806600f01700760420740341c0d9982e03400100101c0105a02e13848140c441020082c0b81582071501188061113444409800503801d5400c0c6040d41d00d41c2d02c0c01c08002c3d03410850803052803c1120312108181c8146d0102c9000418000205900349808214070162a01a4442035098401842444803003180105420154007082c04000042441440208401881100a42968 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 17151337 1250 17150087 17150113
    0xa022e020d170420060d0608030405030d050408071e050301050a09060f0903050f18060408011e0b18061201020a18060e03101109100302030417030603030409021e0a02 73
    0x101607494010705000030280d050001103132500d0401c00f0301c003140640e00d0303628511020100d44544100000081024a0f000300040c00f200c0110190007928400c03015142a030720340c3d0314220f0b0380e80568003404030140c10803030081001700d1440066907060408819404071465a407070000742110000c889040d01584c41d0041c9204100c000d1081035200c0c030350500d082190006c00c1d1001481400398003040c4000100c00500c04001c440c0b0324207441444000200519038850321075900b50b019040d041d05e803400404580a040078800035501a1020000c805400d800c0000240940c000e048017000e400d694211a40350000d00000c0c000f8001006030b07000540354107a0000302d00c80c00441c10300c81c6034483c038104299412445003035900400c0000814000a0006c101100342881115003441003850080c2d0004402c210b1100702605a005144103600030403229007101340d03a801c40b0b01d0511040352420380c1504200030500540000d075001d002c0d081c03080e200360018007903028031070740300d82d03022140e03030301c056402880c0075031103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 17152587 1250 17151337 17151347
    0x1505040c0e070c0b090102070501051e01080102091302070c0f0617060402041d0406060b0712030c03110d0e0a0b0103081209030a02030d0c020c030a060b0f010c050a022e020d 76
    0x920754140d45046902c2c05040c000d04030011004000c1c02c01d0300e220086242c0180035010b84030426005002045039040c07404d48072803500d100e460b14030b203454140350000404400620030f95890007000340c10002ea11f1041417140009600c01542102c640591503804152015980491400b034400c0740c07110303400100d6a07094a0a04800141654440e6004000c03e10860310040c08003d141807611500c00019140c40c036040c4060640c2d0b4001704004400410040180721422420524803980c0e901c04000582100d9021015030707541000043c0051800c101038a038080190780034102c1d00c952041078401d92040f666801300420ad003030b0710566400102240c80c554000d0340e804178a0b0041c40203070065140111024000c0c0d00c901443c1c481104056660380b02492b018024800b0301203006005041c1c81c01401c051406400520b0016042800303000314400840d032075406460080007075900140140b9500e5615401c200f100414441007407090502d00f508000d4801c125589000d260110741c0252600f8400c611000f41 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 17153837 1250 17152587 17152589
    0x204080705120a0305070503040b1c06080d08060121020c0a05070609030f0602030c0403020907020709110a09150203071a010602010b0108060607020f040b0307030501150504050708150406031505040c 87
    0x4480d000955840040b41c10014210503a40d5142c14075513201c0090b428154194026544210f0191000043d44803141c030048030005d441400883e402c01203a5143d5681c030f640c482d24601c240e400301d201030307020464541c040d4111441e01040710009100c902d40401078482660443c0c012864903278040790008080050030311406020309050718005084074516124a6050491a80098901540000410a25440303070080350065900030302140080e0a14040080d0303540003e00c100000107213080d403d04101c1401c5c00071196041d55585d62001010b0902e00f80c001c021590400007400d500c802c1000c43d0000d03004030183c03520400e000034680c41c1503250600107400d40340c0540c002810401c51070200300f00c583d1404155207400350195000d1842c02c03c00c002083c014216000e00c41d03814495804000f080210541000142031108000b2100d15a5a4024032050780c00c150740c00b001007000b20b000a040c0b88640c4a5800c81e14038020301c0070400a50f692107807054203940a800d901401d486908002c14040c040e01303060 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 17155087 1250 17153837 17153839
    0x221406011502061504090b07080f06031902040b030a050a0503040303080603030403030903080304020f04050109020405041b02150c090a03030503070f0c020105041a040e09011413020f01080402031608010204080705 93
    0x180c01d40c4003001e0000d4031204000e001c02640381c55185240581d449541c000040c407544403841c01042c0c20559001340c440003003100d04124103880c0c040042d009003004105140305250110141400301c640358204400390414908050305840782d404680d02140d0100480800b550186000c1c69499045080c002c01720000104418000e50080008200096201280740116504088225101d44491000034464140c001140340d00c5401e000c00400c4ea27442a500a00031110120b90420401d070982d002e130424001c10351520703405600034000201c40031018899560b408480c0c992614a441200800a46864100d4200742c000941c04400c01201c20340040300f820700010720b4103003031003100d00e180c4c0000e02c54411401202c29040c0450b40d1903007111101c00070768000d0030500e09030130706074038110098a000301456402c15030780c500420003081c0100b024202545038540c024203204440b020810042d168818090b00032a00b43c403540304140d45a603130542c0c1c880080e000c040009640c83c5c0c40c01e0002e9140641d182c21007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 17156337 1250 17155087 17155109
    0xc210105060d0c050d060602010e070602010501120210020703060c0804031106090709020a0918090611040b0d0908092107080f030301090903030e030f0406090e091522140601 76
    0x50019541d580c09558020192507004200d02003145411540340c06903c0790801d4035802d090010500507010340142480c1030810341181c00980da01c402c00c900f038560a120b44010300000e60044030160501e40c07071040001100e801145d500031303540d0f03035082e08540c1400006000602000140010164800121200b00020307600a000e01d00b4883d900750388031482445000c000c60381c0001c11020040c043c022140080c03440d5007205601041c02020f0300098010b41c0402c0b1001850045011660311645081c3c43c00c1e1250300d0070050801d00108004401070404000640b03040100380648141c9a0b10170b40c2d200365000300300c0120118180c4198071f0314540403203604080c4281d0803281c200c1c02d8603400001900d044130060403000c20041b1080c101a8014041c000b0011014080014101c61400303002e4010720455407540c0d0b600a60541d030b40c03206005003105681e02c0100f03070000e031400748000103c121803940082e030340f60b00c14003103e162902c0944074403d00e1404803800f06c10304481421142060000030300502d4800da10b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 17157587 1250 17156337 17156339
    0x3010f0f03051507020f030409050103050709090c06050a020c062a011802010e1305011e12020904080306010905040501090f0b03060603060112030c1211010b040b0108070302070206070b0c2101 84
    0x2020307116040d442d88404030a5030030f40021034040c0308208003041c1070030701000c0d0b80c0d8442e1a28011005060240002d844038864050009100384603803081609644d00328404607400d6042803001c8945510410f6640c08600c00c00c0101c0c401651280010000406440f01550003004480e4601d0b1428601003d030700b205034500315007483c0d4400301c640c22060103a07091a080c00041030140000c2c440c1e8190311246030605240070300200300440c11525034140140c0c81c5618401181d950041d0800c100410300d4000c0d0000b641c000407030001407060015503041007050510140103510313800403030200d82003680190041601e52404280e0100f80b0310950005007004e0b0058140361602a010950720030b03061056100c400c1c0c007007542809061041d900f541c0041c0d07215220001d1140040d000400c41d28117640070084a520b46034054803549003910400d01c0c0503906840d2401907544043c2c09a009421450301a60004030800082002400c80c80d5143d205124248070b00342ca0b420300c0342c5098540d1003011400a154880c0d640 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 17158837 1250 17157587 17157593
    0x307120b10030804090f060803180a0b03070f030b0609030f0c01031103060901060e03100606020d080a091101080c0702031c081e040f06061d040203061e0a020c03070b01030803010f0f03 81
    0x8121380c00d980302550040350510400f4440c2d80103141950081d040c501021a14503020394004a00b140d0354441203903025142034076201d00c282c9510040e280640850510500c00c000d4030302903004034900b14001002c80e802c0c5000d0a022a007000400080c0b9007441c2c11110a03c42c0f25a01803064403030f0364035011181800c501d44880030074400d003c11300071102070100c01440c41041c0e80e000c20130410075120100003441030382c0c2e40322400780d6134180607882d10020070503050000d10219114480c8201107504421520b2800c2c43e1f65005403142d08001c2d22010002c43c0c03c10090000da10200540c569556200d4440005e045000304010030449001d0043c000030b00c000351380907800d0600408000d8105400c010303051589582442d100c2c0080c0260340c4059000b0b078410f505007000241c240340c0544214002c0c0c00382e42690362050740800c02c40c0c009620400d40601c000000c2400007007540d01800352000f040b02224070b0002c00f0344500035400070980c403c5507134603c000014081c4c2104028100c00820010380351a0030b841c00e5035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 17160087 1250 17158837 17158853
    0x30221070602030c1b0411040b12010504110d09030e060c0304080601050303070f1502120403080f06010e030d0806060f040b0a0201060812030f0a060f08011401120201080c0304030e0307120b1003 85
    0x1020645c0c8009014144401d40d68175540400c2d8503004000c0030903501e5a90704c22500c3c064001c00c8414071b8090503440006428100307070080c4040744410420003443c03d110400c8440c000c0514241c1039040040c11218014240c030340c0c500900800c1d8074100203503140c52070103142c0e83c030300b02058115034001c0d0010300001c0002414006203225856201c1c1b4201008060822110000c5c0036052070341c11b082d2614000d22041c980c02444d030901031400403481000743c5c0d03a60380c01501c511001142e41505644044602181544aa9051900604001c02e054135015640510f5480368115810050038031500290f003410450b02441220001d08501c000b90440b03005908002d00140802499180866202c030700003448030050303078001000341160791507d2420540300e145050003400900403004440000c0d01c000b1401007444d59001c0b42680e81651a0a0756030303100c054144442d080548210280801d4003400015503805110300c4000d40754261005100c101d0340d04088284400c007400500c0c03000301041090010900803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 17161337 1250 17160087 17160103
    0x1514070c1106041a0f070f12080601090e0c07020114040305060906010e010b0301120203010207050703051f060503070510090306050411180609041209030b130c0512031c06030221070602030c 83
    0xca507041742c488401c2568120b4a216104009103143c02ea040440300b08100880781082c085415920040b040d600c440c0151001c10460007010b1000b074204001410103001c1c1030003004064410314060314114190341d40304485e5042600300300c405801c140d00300f0080700003c200403401010000e0306107146500d04070f050170040c40b06004550b40f4403007041030780b410354400350111030000b0742c400304454017140d0380e00f4220340b034480c908101e2070901c18402c014980e06c056030040c03000783c5034003c0141885034a030800f04083c40b0041d00c888401d115031510004007082c014030904c2d00c81c41c0a641c107442c00c18183d108108108080c00400c0c4c14824841d020f100b03903a141c400f10f540e4419807040c00c4480c04404950203441700400c0d03600060909000004110801e03406480310200b40380310b100007100080d01d8008010014140c4020b6108070f920900c14144c4221110350404540060140c00207501e0f500c0341c02085140c48541e40020355a24100d04000500008021500040000d88060350500d10440390060b120240 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 17162587 1250 17161337 17161379
    0xa0207351206010c0f022206050109050f0405041403030106020601051009030f030c031808030405030f0303010b0a050304080d020f0c06010f0605070204090804050405090f0610030f1514070c110604 86
    0x5601504001c1121083d101795480760003c00c059251b840d050303e2140e80840d003068000905003840d0340002d1550080301200d042da00002d0111201990100c14400104002041074585803070005414101003402d1000b1806032109a001e0007107503040a0074041e1461105c2508002c200d0014010404541d1407130f0a00c40da075034903140061000865003400c079000721040441002003100720700c3c0025007450000050048031303070680a4521100c500b49000707440780002d106401664408000d68465a8440c2005641c0a0720a4440c24140048401107104a801c4640700200030040054001203d10023082000d005041140e06d202ea180c0c02c1c4100205503005201c0000d003d151544c0403c0c041018500c19103010f4a4003a00c00c201d01e14107058a15a1807403842c0101805000f40404691005a42c030002000d407a0402c0c1c0040c1e8040703440d52100c3c02419186502001c540e564403401d05140091000c1d00d0080001d580e410341401c0e420b0911048200302e030034440c0d101c0d18003003004101c1c01320403030403039000d40700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 17163837 1250 17162587 17162597
    0x6060d05070c020303031e06120c1002030f040b04050103050609090c010509040f110406090905010602030405150702031b100903150525050703080105040b0a09050a020735120601 78
    0x81d2808241e5003000804002035260101004000340a50240c8911202d03c400300c91005c4561620303000d01195090b443c17000300d03064110404d441004c2c10301403613260f0780058503c122860420210540c81d0319420641050265000c009400c004642c5e05009240c2c02c400222240700c50b07800d02d1a940c5603a800d107c0c124a041c40004205000c0d190750b5540010040402da00301400b401c1060444110345611901a00c000b18a10039004140c412140c840c582c181d80c0c541d001103142a05100030008250045c0c003484850003000c0004000580301844034048120090104034540d0a42000300440315100302103050400100d4a0200045508400004941d0300705107070004540d12500040000d0b6491403007685002d140000b4104992944000281803250180c0e44a141e60b9803030740c0c104009d6030f0445c252194042c207001014090102c0d2a804903070042c0050500514202c0b00d0765600102440031000b49107441103030050344c1c049015a10b942d004d1013031042000da10384de4210070354031111a4090005070400c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 17165087 1250 17163837 17163841
    0x31406011b15090f0804090e0a110f04111216030c0e0904230a02030105070f020307030305090f0a0503040e090c0904110f040e0c030f07060903060506131409011406060d05 75
    0x141c143d60200000980000c075040070900c4505103942143c0c07080c402d2060746882d01421000f6040c02040310740000b9440700d02101e550800303008101c40c0044031085690300540d42c8021010030b001d0740f8000c16000340c0a41510010703141008041103215007200200041c1400c101960b031320f4651240446564030030441f14a2415105c40c00d2039221102035502c80150003900c00d545030180d9100045500420307208500034446070380c0340d40c4121410105070340f0140c0964410f0014a000900940216500c070030070b0011544102d18400d246450704d60003102c145d500e0741000609001c507200c0c049034154407052080080c200d28a0342d0020400360800108090b05e40741d002c00c01c0e9040d56584017110252600010300500a541e0700c4060161250881050710340b0a100b00d4507503141d996070210755403040324125203809c1700407417458441c10042e1900800041d803001450845140007400c605c150801c42d1030308642c404aa18001c0c11190071103800c40c0d100329003000c2000800c1900da54840403913804265041c40440c0c04e03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 17166337 1250 17165087 17165123
    0x50a0c0f0203030a021006050d0201170a150b04050301060803130501050a050906040914090604020102122a0a030207090510051003180605100905250c05060403031406011b 75
    0x40c649840000d41c54080041d0403061581e000a449400b44622041000300643d81da082291170680030070000c0c0404d081e68250304001c015064036540c001660720000c10b001070440c003101490100e81e00100003110b00802d013800b5500b030174801c02e4050030000c0c009524180803450006241c228078410f20f41044030020711498207611640c01e59401c404058100c17900d0710b44130501c0d10040d1401c02c40b00c4407060000b03030001d101504005041805284c06802420b1071503444400b108444d800007038180c0400c002444a804601c50300300000780c030b400d1440050b010402c002d203002410315400340d2004c04114106810301c854440b42d01c0c000412207000710380700107806440c04810380140503820070000312600460001c50070710185400c220710a5065030a02980707251aa407040040700c1090780d0302c415148000d041510080340d401780b050190769403410882c8407c0308590700c462500f00200e4040300003907203900e40140810740d16422070341c001009080a180311884a2001103800c03d440354003400e4025681210404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 17167587 1250 17166337 17166353
    0x6060607150c030204060e010c0c050402130308040b03041a0106080f041703091005070302040b090d02010509090901090b070f1e0e030109030503040209060a030506011206021309150f06050a0c 84
    0x1190009007001c0c08145032008010f0000e4129118a001050500c8060800c0390312685070150714a1f409002d07060000e0501e41480000c2d0050920030120f8420250040041040c40002d800105001e214180c0d891400f898050411400591481ca140c08031100500000743c1001c44964440d41290f03070014145c0e19401d02410341d190b0100904007011000043c01101c00001c1340003144a00028003d20003a221010308804030b01c91351052840781e1600780b190741944d181030a0001c00c00c0d4014540b941c101000200060740054003520101c40036903550b442c14040100c0311130b5450340140c140c10080d030b01884907440603102100a05c0c1c19000340c0c0b06420281b200703078003542c01c01400c000042d000704801a51460050215441501c003684111000c5c40024243d107080402041aa03078440060078441c0d10749480301401e100c008200302ca00c2c58007481065003400302c1d800c400c80141803104000c250100d0654074a03030342001c9a080740690220781407043c0400741c3c010b411078060700c4032850803d410400e9400d00c0c40e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 17168837 1250 17167587 17167613
    0x302090607020d03022a01050d0b150a090305010b01050f03040201080702011401081b090405030403020d061e02042102030d0c0309050306070302041a0703080106050901170403110c0a0806060607 85
    0x944041c40c09100414164009103c81a0b042d104010a10034015080156074101c1c008001b070b80020001c002d05600c070002a0007803800600b020f00000c10503583d0410103540c50704049082c1000445214042040c441f090140e034003208400c3c00c0c000c5c40d0500840aea10740c1c6120003080a410f00159201082080e40b00b5400307892056599160120740d0358403061a542c85085a5242e4056500c4d01002d40020303107001468103000329840402945481c0c40d603800c2c08a00d0a00c0a007d407401940c80d100381c3d0300e903e02582603400c480990000180c2c0d031410014480d00c1041c9284005411403805400710380107171400075190349034040c18140000e40054626049521000319000380303402d80501404d20200c241c05402910680351000e203200c0d41004100203d80c0c00d8010984040d00140c0c0450040010382c0c0100e004000415040c58040051a00d00d41c4040041600b900c08500103055198000c40d203840c240320070450300d081107422038012880c0921481e40c0e0310000c0d10440c450715001600100300210307146008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 17170087 1250 17168837 17168839
    0xd09050c090117010b0a0b04030f0311060109060306180b1504061802120702030a02070311010e04021c060b0405031b0d140606010212030c0d0c120e010f06170706030209060702 77
    0x14101e50785500c070302c240e00441895440781c20340c20011203410920348403c2900a0304c4412001c9410540b5586811b94660800007040e0b00f0305c9001c10010004076020721a8501074003401401150302407651401c44222050085c51480150700c0e80403d10000d40c90381c14564004d050301c0d52000e200b0110100140060030954004044034200781c2c0c18992010854025000305d030501d484090182c0ea500b2418ae03201d20550b0228001070b084a001440090b40d8811803020365103042c50100b03d41001c0c400443d04907807140c89442804446c201c0d448100c10b1450294202800c169800c6d03600b814a8017000c41e41d01c60000950758a180d4408524600940b036140f124034495400064007030b241d13008506566181c00c0300380ca9040c014000e0ba0030700000300140a0440740100350450301185030201c000d0300140207000910404c010400c0401e1420380a40c0a80580306000108070000140150103000a100721031980e4041002d480c810b1a07003080240010401000b10380c03850901503030366954134001903450311a0794002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 17171337 1250 17170087 17170099
    0xc0d0e0618010306090f1e0b01050706050709030b010e0405070503010b031005040515040807050d0c020d02010c03020708100209120f060105060f0d0615020c0405090601060c0203120d0c1202040b0d09050c 89
    0xc6c0400b0350031140e60304c0090b8005050710441661803006541c564a40b460103e14100440340000e80303281d002640c81201403074181001030722030395004c03403001d403c1c0e00124002844500f44810720000340002c40003808110002c00c058681100440d403100058594005503503951070008007440303410701039800354803a0fa034045500c3e8a403a26000030182c1001c1811f941070301c1085030010078103004211249500f034000b0f1a901400c0707011f03801152a20484142282103019101307000641440800000c550b04403101c0b030150301d4152002c24012a061080105c40b03181e031003c0c038406036068004c1040760650350182c9085542e2241503842506500c2580c070040c40080c5060400111000d1100410320319a0309682914039003489a02000b00b030b11000d9618104e1078003d80300411041d4000d940b502c15407840070f810344040000c16004030210390017a987c0c83c8101519180c5804010794055548a010380f0a0f213011400c05080ca543d40c40e01d80290a22a845a5a80e003440d0040c01420801400300380002090 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 17172587 1250 17171337 17171351
    0x1501030903031e1e02130311030307060c0504050f030718020309030417010605011b02150901030e0102070c031202070f0603051905070903060605120a08070201230c0d0e061801030609 80
    0x2440100041d28103134160001500c040d1407294800d00845070305404141e1510801070641e22103401000724480940c1e03040c8030030003000c0005525401140880c1d980754851a490701d1409084c880c650020405880c4a9088000c050103407054030346040c2d0b508100c0000050716035592041c014a148941d820816103103d04950320401880150041410b80b04203a032804003600c0c4101c950004510342c900c1c02075100c0803014a45801c103103076202070622a0814074000c030310014040600360032030340201300c02e440c0c550003803005006001940f425a00042628401001a60318280710b180e07421240b4020381c81003540300c00208541c2914100108101444038208000c103081201028200c0e001c03610046840030b00340400018645441c030032007612545824041e140c4141341d907641002681c0304940490511071560903a034240552548011840d5201e140e02c42d03615115000218600316100410f041045081150741f00305445110640b0717054560600321a690300d031500c005801400d0180c100ca1038007884c2c040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 17173837 1250 17172587 17172641
    0x60414150a020a030b01090b070f0201090b13090b0612040f020607150b0a0506090607020f0a0308070c03060b0a051c0501060b03270c030a0201050304060902030a030e01020114150103090303 83
    0x4001c103c4980640ca040090703455400c01544c0803080ca1150908002c0103100403004200c8219400420a10514042d000d042e21412442803581142c200200000c14a4100f481808507a10615403944000c946141c2482100b40000458242c002c20081c400c074140c1012000710346544054540c1240c1c8075125031403032151006044010410f0401061094401903000244c5040c500c040b1200f0b030f00c014154500e4111a0b8090100c03024940e022950030202c41080003011036000005481c0c890321030b4200c078102030301e58240340301980d4050b00702600c40c046140e401c001580d11403a00c10805004410808010002c5040c440d00500e4242d200c60f6200100004000d00742c202c0c5141451100507440742800440b0050a0f180c1d610507488460355010307400341e00740344050341c0224042c40e40315209100c003207940c0b2560b0340420305148003194110007241c500c54000b01990380a009034031750900400394030411480c1c0300e0403000c0a03541150360613050664801c0f58000b40351080d00302c41c0030445800f25a4420301e031100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 17175087 1250 17173837 17173841
    0x605090c0903010518031909030f030215010b040f0e06040209040f050613090b060603040c080d020a0b090c0906011b021509010807140f1305130504050606040905060414150a 76
    0x1c030a840c425441c0c20001040c52248408203007040e194400110b0411344100f002000c20101c02089200780310329000c00000041c0354025481201d8440d43c013800b084815544e1500c07802c801a045484000001e1000b884810180d400302c10031070b80d10780e5486405403070b2100824024440e80d5540780d0000d05008122810361031036004a8010002a00c00ca008051203d0b8007008030b8810b180020040e05540b404034400d480d0400c080d64010f8000d401e42c00c00329654883d0140b0301000740b4600d4001d6040b032200d941c2842066000709030f001810340c010700456002c0400013406000010700150501111092001030650043c0000d01801e50190800302550250b4010703211386c0d00702c60038145c0000d21020010b940c041c03052014030a004225100c542c1040c03031429003d841b5402015040030040c1220000068960311401440c2c421402002c0002d0f10b42032500b0f0260600c60020040b03405681051238910010f00000385043d441900625246200643d501525062243c1c4468402d41c0490171414404018025 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 17176337 1250 17175087 17175097
    0xa08070227150402120f0403110a03030c02120c0a020103090804080d092103020a080f070b0106030504030201061e060e03030f0a170106020105040803010501081005040507050d0f02030c030402130605090c 89
    0x15842c0307031100c2c0366000104000e0348a5205606005501e010101c1c4031045d07484181500588641010742c00289411745641c41c00d0207940060b00002d03191204951202d80520070700401d40c08000e0018608201c4490250380c841c01244024101940e0340300d194140141c0205403030282c00b044050720003008001400810b1007402c4d019038000016040014502018a21100400c0f2075141e0050f0515503904d4440c02165080541102c8485108101560000d84903010700350103030600380c030700003800d00f8a4200242103d08941111032014002080004e07051003080b05030044404030318100000207420300c0464158003c1911441c6072800103d9214503544e00100c5180744000c616400c10b00036a0f80f140c04900f65501960090141002000113008551003030300728a500c950300003030b00504a6540c034080f400b25034084501c00006540803407020140c0c2001c1c0100c00310122185419421410b1030074088506100140c0021f1184403900d0310911808032540101c801003030300130700454141ca09101c80c0c04942d0700c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 17177587 1250 17176337 17176351
    0xc03051813140a06150f022d0c010305240301020903070f03020108090d05070b040515010e070f080c0904091401050a0504060f05090a080903070b1308010b01050c0a08070227 76
    0x1c582d0004482240a00c07a00080700d003101c04500f40d58009560545040c01014001c07011405001e0740c180140e00303e040161070003c0c080c2000750305010094100d83c00c0c001198a0b95040608003402d0000002402c60035540c014101b00e103001090000b000028020312601004e42e401d4000c1d0000010411207030f00c0d000c0b003281d000fa20340010f03c0d910b042e00c0c1611100028540c0c00803030700500001d40411000c80c2c0003944544140211b41012008030751403000300d8002d038041c81c6508002020000d0740ca6001d41c40600e10312042c1007190480c10401b400445601511514030702583d03503082c681080c001c501e100d126251443c14000c001c14146041d40740d0150408403404d440140c102410b40c0380d481c2e0382d8812944160310070405404181401c0c0c0e00c5445552202c0c1031942d05225505002c103071521141e004060320620701d40d03102c116500d8244620f007507808a00310305042c0607081c0161000c400c0d02054405c0816408400c00c1c1d95000b007440003c1d003507161100150740158a400d101032030350f220340d0480e034000d0701 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 17178837 1250 17177587 17177621
    0x7140406120b01030b061203070605011701020c1509120309013c0b040b0406060c020a08010e10020a02120406020a030201050a0501052b05031201060e0f010c03051813 73
    0x1d11009445900c03008030700000d104440c60401080460440c1c81c03a140c001c00e0040405001903400b5191501d1030304240c8041e16015501d8004000200190080320720042890b8001c0d4285002c00441c2d644805410256402491903607000402215062141d40d40c5c101000401c10b071207040003102107000345014010901c005019192140e040f6511008800400e412070b04035000b0915840300060240040c01002c582103600e483c61040c080e030320750180c1c0e409818150b0b940e05994405004104205003180d10204699240103107003000700c84041500006411351326009070b0350b4003890b01c049141204074004900c070712002040100d0b24641c0402c00e200042d0007680240040c0d140d81c10b5490444000b03200311035101080e03100500c13460111001f901101001d90224031183c41850700c1725405c2d41d202480c3c4a01e0b0048040c0181f19042d000555110281800c0d1041084400ca150001e81000364012003e01848400300e940804051900682505240007030480100440b1404029024045404040c2c2c190302c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 17180087 1250 17178837 17178839
    0x15060e01080c060414130b0312070204060902070c0b030403020a05010c050705061008030301050d080d0504030305090f03090f040f150305030301080f03090307060e010207090204140f01020c010e0114090307140406 93
    0x100e040c10944d010380d6080e140a1210301003440c00c108075078204101e1084c0072030701da40a142403030f6401d22021085d80001c1c03031803d640b50818030400044403102d030441d0aa141c07041c440c0c0c0d0301190558000c4003d440e00c540c0059640c0d280c41c00c090f0314088403840d0083c401e42c2404280d03259140d00a01400f01c3c0d520503400c40d682d58840c102001f003003a24600500000d54000d02c0100320070305c0c04031500300889008500c1c403440d020389114042f040c0c0305c0444041d00400e4451040c030101c0e11042020100200c080c2c0050350030042039400107106e00086483e01d6100300e484810221140391950b205000c2d2501d04084003411170303501e00d0f1a68a941091241c07040783c0c014080003102d40e6002008a0390407110045c05800c04a0505006070741c903401004d00e15045114105020540186d00d100400280c00950880c0400c1c1056008105804104445075030441d00002502a656600103c50700341801013400d00741124030903000090614061010000c0c4c1c98820300d0000962601891070805000c5e00a0ba0144241 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 17181337 1250 17180087 17180089
    0x302041803020c0609010504170607020c030a030207140f030f1608070503030409020703031103040602090a0501140327101b05030906071101060b0406050903062a0715060e01080c 78
    0x4180041405000b5800c00b200101c09440c3c02001400c0b10f080505201d170030152150004039a0312710710341070780d032083d845001440740c2c06070100481c80700b00382c04030014240c044107694025207d100c1d51040a220005849031014540c3e02c60102910401028007141c040d44080c0c2c058540c6c68408002c0c490705000c4440000c14004030110310b00342910000380c02580382c00d140600700802540300d56030550030184c4d00c1d039040394002190700c01940528003c020140e11552600c00700320383d601080d0711180c1440b0420b02405022000309044e03960003900e0000346404c03415603003010200381200c03501d10889405003155117901d801e5981d2020007203d0540e64000c542200128050707030320744070a5603a40b01e0307580301c1d02c009244030740304030100c60b0340c5100e8a0010800c1a5100185405030b04180c20150100e000440c03403100c64241008100d50003a621072540390702c105001441c0c034000c01d180c0001c03000b00740c00150000038000300e60500b0340c4d19100204108503032030313848a0180038100c082c0a503580c280500030040482e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 17182587 1250 17181337 17181371
    0x30420030105100302121006270c0c030e0301090206041d090307080304080714030301030f050609071a07030507150b010210050f060405041e030f120e06070e061c06030204 75
    0x42010f0221841c0d00d85030030354080008814100c50043e1181c8038007076088101403501c2c0142401480302c8030100c2201a00c0d102001080c0b001400c0c8200e6031441c102e8400c1600c5c1d800140503e0864240c00d1081c0d401c44d540c00440c0c09000b440340c010b5001140043c0c005100418003e09001141e8408420a51900c645102030346034401e022024200500c140007003004554640002c0510521519440051903880d070020350664100f640103590b0b01d40501805400e0100038440150300030024000781040f9070800c103030411010302d01203d0321620140420302400309401841101d075641c0d001400444561102c6901e400900208001540140607071007030340c090f0b0031a9005160162070840124000d990320340e400e01004000092003a211082030859020300080010203001300e1900030344d0380410714510504083e0416041d52006800103241c0030100981c014007007155a00f004c100d140110395081e00900141c41400f4200d43c03d807000c0a00d1503031a203404080c0d44183e048034420345042c000c040c07814042d100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 17183837 1250 17182587 17182591
    0x10e010602010b121011040e010e04060e0d080406020a032403060b0618060304031209060c020106120c090506010c1505010312090b0901030902060d090b06090c0703170604020d02030420030105 84
    0x1013507500441c51400200700f9504500e00b00c0455280540c20556103a0340345140c03031f030281d1107016442501020b110034040140a0401080340100c01031107201e940640040800302e0080c4068286940481e115020070300c41e402c1001c0d1042c3c01c1c401296400b10900c80e80c013508a01d807200311009481c0410480c0340303003003d000782c800c0c4034115441c0c82c0401c0300300024070510740e2000740101c081000000240c0c0300c00c5214410700300c400380255030000c1c950b0700d0250701a0841f15036400c07041ca4410300c0c9c400c100028102100130002d0b02c2c10b185021400e0307103a0f400161103082e203103000240b1010840704480e0580040d940000c1c101c13409541d282c00000090b07042034602c1c040c10b0054650200301042059140c0d40641c024080092014214500c0c004c180340d07200044407001007040701e503c540b0400303001c05440e0800c01c05030004602d5103041e251080c2a6809480d55000000c1035001244c43c070001445135441354181d401100c002c06003556a442c0525002d00c41c4103224402410a000b495030394149810b0510580b4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 17185087 1250 17183837 17183869
    0x70203071101090302180a0c0908100905070b0406180f05010c030e0a0314010b030606060c030901080705130303050408010507020c150706090c090605030f0c0a051c0b010e010602010b 80
    0x528110907030315165002800111268180f000301c00e000001a00c44c9480c964141320074120b0b0301070034200006920700765205942c60000300500e40c44240889500446d03038807902c00c0b0243c00001c4500b0380e49049418189664003669a842c00070400154031900526007540c0c1510ba8a0700c08011910350711082103103076850007201d00066800100000203030182001e1031a804000703103140c0f00c9070354035035840034011100c0002c0801d0fa5100c1601d80c01380c0c101001403640114040360041c0c10881c140c80e4807640e0b400340405582c10031540d03101240140d130060302203500b8580010f014134191500c90401816981c4144103040d815883c00000421f01d80c404a0020510800180942e800c0106d2081e03000e01500080c00c16a9074994072241080054030300720000d4018402c00002080c1c8519140c1050b0920020884503003494200708600441540d40001040c16a0422500e02402c0303403054030f0011f005001010010841c1c42c400002003080c0a00d00c0c0e0650407101c003507000340300045120307003403082c8001d10301044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 17186337 1250 17185087 17185093
    0x2031e03030a0e0f0714010e0109050f090c04080a08070b0121030f0509120601060221090d17070f0c060302041a030402011e0c020a090203060112050702100c02100509060702 76
    0x40b42d00003000350400c1d016000075100311810b8010784032400d400d00116a0001c500050b01d483c05c1d00d09941c0000d044c440c40034090034840001440e2801080719403442c0c0e03213010300c14440030b80001d2449032280240d50250000c141103c1a43d0388501d420305242c1d01c001c100b03640040c466000000d40143c50ba880e00078a281407031205603030580700e42d0191080080c070780308007090080c140005501616122040c800c44200c0e440113125552414070060b0030310074105000c0303c80e500208107000503914808110340000100350b8a42d28015698100002c10b807050240c0c403541140002034240c10301009080140c02240580910140d4030303510300c010f908030700c80d40c425410558082016526005a010095a0b0050040c18070070800145410f01a101e01c2c900001340700411070140070b1106504000124101401c030000045145040400000e82245140d105050240751110001003100c0c0c402c1c0409213419694410601882c603038200c0c0651501003403940214414038000006611203000248075014507110303009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 17187587 1250 17186337 17186341
    0x901050a03090203071203080109050106020c150d0609020d0902030106140109030b0c091203250c05040b040603060f0b010e040507080c0f070b070e030c01020105010e06190b030406020702031e0303 86
    0x703030098540c1440680c0c0c1801101c00003c0e113000851a15066140b09903148a190741c1400044002c03107030182c1081003154007d040052054580d8800404c05541c640042030715000b110401e0340182002d90000c8410301c0c004aa49001c00003260455000d1034400c800074800c00f512084146c00510044c4510303170000d46c0d12102000032641c119006d580045004043c6494800c01e040400d503003400c001100c8a56138400039072103480c9034401101e00f01454143c083c00b684007095407905a02e1400364028184150781d03135690050a83c0d0b550b07104000940c1c1c404414007100c0740080740c071300041c5412032040380800c65500c00802c080c17030548150303031152242da1105902e42d1a45101c810581d00000d1140c1c00601d81080020040340c040141503103c3c28181e070300c5e000c025500300145420b089860314414190f82c10500184510792400403400e9000400f0b96801c2010388155004028100c15030b41700648030840042800203001d516002013905600075001c403000c0070580700044c080042c600401c12510703002480 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 17188837 1250 17187587 17187607
    0xf02070302240115050d0509030a02070b09090c0318100516090509070c02190806100501020f0c040b040f020c010b090f1605030a060e1603050a0e03071403130603090b060402090105 79
    0x2410100c14184d4074000341000c1c1c031409040d003150401c0d621555035a0003c0380c4003911a82c104030300c0010b850041c921a00740034090b0081207002801901d5641d00d51b1001c00000c40168405001c03c0e540c0d2000c04c11500f07141c0144014000404040c0c80701a400d40d008040120000d0007180404103c500103003640506582e15481191741e5040183c2c00caa00c1440da40102c021300d41c0711000840500541c4c0040c1c07000e400c0a26485c03a00345a1a40000e0640d000b90301104500c1001140c210701c428000d82e008a10148a04002001403c1003020010300e00d1001c41c210f012420158091a4411000e40d0855526110b18100a41d0220116507603405001903107202c1150074031032000303190004205200841c41c0b03919162403056880c8100c880f10400c00b000c00b44012481e516020749a04044818401c00040c4e031510940d03901e80c41a8400603145003070141161088038800c008880098100c0e80500880644a40300240a480509011340710400e041000ca202460b16200700c0d140120161541464144080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 17190087 1250 17188837 17188859
    0x503070e0a09080309070f060c02090a0b06040815150102190303020d0f06030b0603010b0a060c02091009060b0d0c030204050f0f040603050304060e090901060b09061803010f020703022401 82
    0xd001d2076081d03803520090701c006001100910301404156020344985810400780500c00455a4861001c0210500c00345015031101e5240d00e0300610a014041175400342000424418070903a4002e42c445c0c401c03003250a00c2600305100180c0078440c80400e0070031522880004907503580c0c900312109900c000075441c50000078040c2e8004e003c1100c00640c0402c100e4141031001e011991540e0080e181440642c0070402c9a28080c45852040ca02c11110303007600f01e082c10070042c0f1a0746400d00080c00780e42d010b800300f07007d00403401d0400000c1c03420460034404103894031000d05546c0c000d00c1708940e01c01e050141c00e0070414000c0c004e0f64180c81c00030300910400a07032501001180c0f20010726194200f9074403480880400d13024802000075101689840349000f1050302031003203e504c024050342042e49091018014085042c00302d82a03128102e92458a500408044080180c54520015415880c00b0101500c8410f160050103016001e1307029a65800e004d014011000d40190707504158a8904a0044c40385142c82 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 17191337 1250 17190087 17190091
    0x6060f0a081003020307060e0108070305040c1a0d1b0206090111090d060e0609010c170105090a0527070e01090b01080105061b16030c06020307030806101106040606060f03060503070e 80
    0x50b0740744107025920f8000c241842e109400050010b240c070f00c942c43c850758214900341d4201d080d514007004145440d803141080782c00c00d4002c0540b007101c6a08004007200a0105450408624280400095200390000b91404464030b1994000d800303042c0020344100700600c01c2000c89060245035610308103c0d1401c101c80358049001c1200c180707544d10141c01e80003a042240b64401c104000000989504000c8041d0801e1103090440c10f170790707080d0401800f11b501c0700e440c407540004a274a0081000d498280204140074200c94a121034114500b030302c01e07601003001641344101d4140840c0312a070350740c0f1501c4c08400c0d50314030800c07507001c9094080108004d040a800030700c0d503140460f485071400d040040b0740e0b034100715240c00644072090191100f4000d0081d20115680100b0050000b149070502071f5030090641c0344001d01562103040c030251103401c114050071200d410f00440c1c00030349866140c207140c40401000540214800904403c582d04880e9000e44514000d45800038020458146440c84801d5840c00c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 17192587 1250 17191337 17191351
    0x203030f01121a040b01091107050709090f05030307050d1104080c090a020c01020c01020d0e01090201020a060906020d020301061206060201060f090e0c030a0f03080901060e0604020703021e0309010806060f0a08 92
    0x700c5003d0150302d280601586014a20565050703400f03526020085040c2c52840d1410025000e04008070307400214009654400ca0303e04800c0468180480d0400f000c0001c507030fa00250071804004104884554000000d04e076040b2140c004224011455040d050a4000c0d4042e41d002075002e4190341c0c44c40d240c071181c1507a0101d448140035140060718440142660001c2c0c80649140e03402140014445409001d256900c0c100346000700201032850300004e5a480700224050000c55640800c60140b0006030110342c00585407402c00d6584e543c2d5000000d08000c103e103800900149000404aa020f2040c0100001c8452003444d41715001d05260aa0009240e05030603a03d4900c0b0b50288110703d51000d2003003035040ca0203081e031244003c015013400380c104540204404250307450301c2c10a2203007080c1d920805070885400d40f0300503140c41151070103a1614001401c0700e0a0302000c081d04400303650f40000100103821080e42c8540017501e8036010300072180940c40c000d19085d04140823500e800303482034a415a00a03030b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 17193837 1250 17192587 17192603
    0x9030a020319030e0d0305032d010b07022e0e0d0c0305060405070e01080d0e04020903010906061811030705030709030803070201061d040f02090a0902060c0c01030c0203030f0112 78
    0x52640068038001001c2d030329501c0c414048120310241504100d02c0b11002c541580c03030790304100c003e941c024150301c0010440a0111102c248127103010b9102c1e40600a0380000080709820707961503454120081d00034101c102c1c8291103114014542500034015007000c1c15460628901244d06040160340307450740c410361150458107200b44500421800d00d4801c00850042000e4120740c1400d0070014101465034001e5400803d10030010411000b0000d88030406200b94500030262200c0f100014001c1d10410111a5241d070034000494280b000d82e9201204440c042c126101000c0701c110400001d6808602c401c103c100f0080c800030300d01d40d0040c0c1c02160702c0082c2e07103020f50040d51a6590040c0c07030707001a2800c00042c1c1d503400d824000031642c044840d0b07042c1120341c40c080345481c180d40c400b0410088450000d000360400d2011800041c001d13000000306540c01400640c907032040c040c2e029030382c1d003411680c580024100307004031414a002004403401001c0c01902c0010300c0e0300f04005400d14003540482218901 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 17195087 1250 17193837 17193853
    0x20a030b070e03060415051806070c03050c0d120606030b011d0607020a060e01080106030b060a12110a03020904060e01030308010905060310020a17160507030305090c120d02060a050c030c0903 84
    0xf503028003a03e4812407003401c12020342c0e02420810300480320b0080103400700002d40300501d504884c00282c0c06038401c100b4a01007021200b2071070100ca9600410194004911940300d00c5002950170034034030500141702d04401c2100c1070740c4800440580314600c1595002c6101404c51004d40001400e10702c2001c540030f0b02c0645400e11aa02003201c10845502010000d00900456079156a121000c81d00409483c43c0034002c541350740000a206218882450040c009180d4051009103007981018804c40d0145100c1c946450f450307440a4081d51100540a21503407400d5004510201c00c0c42c0c21505a03900b555806a09a0070b0112200003404003030805607051040340c410b1000c42d102c600080c0105551a50780c030341c81030050401d084614001030848001000c0010901c60b1880d40401a0340700d039034040c0f80118140e181c250b510b90805280c214030760f4004d0001d5105c02401080002e881c140c144c1964221042650b40d03400c400111a800c0d1120159440100045031904036044003a10b0744080040039100f0340 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 17196337 1250 17195087 17195089
    0x7081b09060706090c180e030304020901091503020301061404060b0a0905130e06010b19030b10030216020a080303040b0906040201020a02060c030918090f06040b1609081b1c020a030b070e 82
    0x2c05d19031140b000d80f12031902d00d41c0c040c0d03a82e00446c407219076000010750641c1070643c0080d0024105010b020b46095403035804107610030411018100858003d0000c00c492612071103c2c02c1d61001c1c405205000d0750514000080202500c4100c0700300d803d440d91180a100d00f46420001d42c100d510402900b2036842e8440c0c0c060407070381405a64024200c0c4c2c440c80350341e03070f42087c00001c650b41e000e81d46c2c0c402c2c540307001d00511085d110304480414450051a0050365100410140072880301c2035480650851021303200854001c0000009501842c040c0304251001e540c0d0303ca403030359240c0040f103000740180c00040d0f540c401130410f80701800c0000f0065050724284619a0049628860384800070030360081c60b00203108108800b840807040d6010a1000b0f841c141c6007986941107402c0001e001c5030042980d0303000b441080b03481400300401803c8040c1c10344d68100702540c0d0104500c42c8680c280d520070740492849200c80c41000c3c0201c504d142d405003000400030300d1615842d1110a00518403824018035140784429 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 17197587 1250 17196337 17196353
    0x11a091f0312080415020c0705120a05010905151003030905040f021209010605010806010c080304080306010512040c0f0e0609040308090102040b070501020712090506030a020c010f021207081b0906070609 89
    0x2449156100e04241c90181412017403201c00b00d014600c042d1041007040540b0901107146402d5070015600301c500110710314403441ca041d401c1d100151240d440d018001080080200d43e01090758100000d00032941c0b0b07590f1440c0c00c0e00d50188002802b00d50f4640040000b03003082e4020700f4920034406001401c00950300b040f014031031405c98081c0a50395580b0002d20041d81c00400017504a1020329000800a0240d61508078500c00a04042d14101e40400004c001e82e00c10011542d030102010b07440d002e203080500d0141c2e5122042d0042d10803003060800c0204004080b50b8840e407054170018056209619503071420b070740e070705c1c4003070000866550204030114074481d03e00e00414003244903100069483c00c071170806002c0040c02c460920200442500200120342d03428003565080200000016510039400c007240380104266413030400f0710f5001103036810f01540003411041c0301c0d02440e06c402c05150707226604d80410704101003140e040d1038028450500c2c181000d00c050542d07a8862031000030901001d80716540 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 17198837 1250 17197587 17197613
    0x3120601030b042406021603030e04060b0f0c07080105061003020d09140d0207080a021f020a022218023304082112060103050408070b010603050108011a091f03 70
    0x51800520030382010b20130f0324030703610000a0461b132028115015092041500c42142c601c40941003000d03d210b0042682d60faa8080030042c500307034a1140d5a00018440740b00650007801e4418001e000307002001508040c103000d61480b844c8000c0201e900419103006c20307402908200850a00660355482d0348001070714202c10145951121030003010383d801c4c079500091521941d500404003a400200300f41c40103032141d155480000350b644116046400030440200e03e0070a51840181d0b10207419401501003a510f0b07101481c1c4203002140900c060121682011074a403c2c03448020741040e40d10f60385501e80c0320300b10803502701e04107c5003100000440b941c502402a4000f034100c100350b50064002c081040003507004046000401c0007d05003440031551b06100c40180040546d814180c9a50000e000c126000045072034840e0b01c02c01d03c0343d01d940c640c180140141802d000c0e4a2407980b038964031a8803030340704642d000742c012002070031a04035680308803500554803000c401d005020b03404c40d00040000b40080b43c0200c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 17200087 1250 17198837 17198861
    0x406021c0c0809011d0a2406031104060509040209010e180a050106050103060f06050426010903020f01050c1c020906070203030d150608010311010f0207090f090c05040e03120601030b04 81
    0x49030b9003401c603405405c440300e8443d819036011143d4010b50744520041030038509150818400c00d01a121141c0200c9035902c10030740d84262619100d804010407030440c541104031442513808008d400d4840040c420f100c441550040e50004c2001d00401104400c420080e900c10350200340064883e4000e4411494003d903800d081781e190351280014800c1d035a240c8207a0380105a45069140003070724218002d0404e1040e80a84203880f40c9800ca0300100d400c039040c2c0c100700314030403800800c651a15820001d40700d0751020700c45d5000f07500f0980031607c644000070a0360004414900f4496614942c03203000c000035840034000603000001882284090b80d400d04c041c00549481e610041524104021040395500d03103908880705100d10b290051000c54a00ca41d14150441d0030300b44043c80400f401403e070b2420340e06910041940c3d0070300190002c185070b82c6c0c2022081601c6011403001c0991603504000c2a0780a001d44554103500a020300c001054081158582017003041c18001030000c4218040f8003501d020309008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 17201337 1250 17200087 17200097
    0xa050309101107030324030605040302060702010c02070611070e010b1e1201030609020a090e0c0a05030304050303030402100c080a0302031f060e010c05070b03090a0510020f030406021c0c 82
    0x40000d03420701c201031508070300c0c040400c14000400319044042c015080040c00301039a03091880200b80750208401041d1518118620b000c0d80d891a2000143c0001c41c0c1c11401400b035100850300f0717203005000e80e142c12481c1d50050100c250a0450440e407a40c0c04a8140800348036120001901c3e9000c840d425003c0d244401909958803000300da4588401800c060081c4c04607402c001030301c01c1000c1c80c0c1d111819680c0c441e0300812405a1400000c1c08604e0a80120b16072030701e401000c141d1610001045440180c050702c0d401c202540c1c600070941c590065110b2140c040d0400c000003001031405140d20703d5440503134182000046010740f522005a00302c0340d0200c0220758000107200710091401c3e01180c00c1d50a900e100954103041200c010507600b121290141441400d8024004000d4107000c13a002400e03030b001c902604c030715080746415604e0010701c2094909d0f000d54441c189160050f0300880c1c41d0b21069586032455610b5130f55405000398024501d4024101e10850a5003032201940039a03c1048499999 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 17202587 1250 17201337 17201341
    0x60a050403050d0503040b0109090203030c0f0304050406060e1e0102100612060b06090a1a0f1207080c030408030f0c0705010c030b01080105030109030c020f0a0509010b070303060f060206041202030f0a0503 90
    0x34038038000800c0c030800c090081c02d108010028000c090030506649d0407480c0421142e4452001c02e14600640f48002811302811804449680000002d4811242c1c01c030f0f010300200e9643c0006840002e150000550000c400d06051508070700c2c403105c40e0302502010320464004c1442000e003c802c03203941ba00410000300241102200b400780074010513829200489007140780c08443c1000946041032445081e08000c400d02c1903c12070a41601603d02d20215030b042c0540c0c2e15280988945032043c21a801f40c0452401004500503041500c01d8a106507444a80c00345035807035189403107400c090020300f808002074040183c000018801c0c001c510082d800340e140414010511b00c005445164141c02c020f000740e00d80410300f80482c1d8442d042800c080d8056a4540b40c000082c000329001206503003101e50004a08000043e040341101c0050034458040d40d0100050317500c8404018940b0f0302d91060000590045012901150035558613480c11f407040d004580c0740004d4038041890a0300000c1e0b0304e002083c00402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 17203837 1250 17202587 17202593
    0x203090715030509010507050a020a0f03090b0409140901020a020a110a0f08010c02010509030a09030204050c0706020c0a052a010f03090c12020a0503010e060f10030209040b0a0c210207030509060a050403 89
    0x1b030681100391400e11a00b480601d510007980c5d000da402c409406a24a0680d20b002d00d07000d0071038140503000e1041440c3c1ea41c1e8803843c4000c084d0040724583c000b00781c0110f00140703840c40b042c800c1c2c6011000503400b40440c5541d688030001142c2c285940c00f9805841008005025005055130304002e1030300d1400894826420940a03003160001040142c0a802c1000182841d035440300d58142560b60481c2c00203869115203411615038050800014105840054254080400010496074251082c0100d0f100c030036004010611b075800580383c441601a1804c91041258082c610504401600d4540007031409440d4031000340c524415800b5180c0c0c812400358100c15130404014034405444250002e0145054410300c0c2555658010620342d0030030041c001144158102c0b2280390300070b640040041d0550300b01810002503560050703915401c81868000303040e2015004450200e21a83c0e9191020041107120342c1010207580880402c4007041030403c09040f807640ca02001d0642129a40d41d11038071541946 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 17205087 1250 17203837 17203841
    0x30806030f07030507290406020106031e0c0b160f060b10030203010e010e040c08060c090103140702100e10050f040219080303010302130905010212090c010c0b0a020309071503050901 80
    0x406008101d8004090900114000007009000c40d00016481c1103808519660300105c0301d61072804006c03111000500150082d07054028805881c012840e01400f0f14050010303503c2c04607a0b4074010a58580a402000361101000c0500340c08042c4540c1100b803800306a0300d1601021000000700d403402c1d40c3e981001e429080c0390445070109180c5060445c9554144100340e4203121b414483c0d150315451000c001002c20400c00001300047c00d403001150b000341403404240070710750407400806000925007444400804448800f46000e19450780203088031414001c0d204010b031209000007001071003452080131008030903105080c480c42e01c071041001a8103040c410807054410310060500503a481032018406914040100e030304507681110041002e00c60200d80780050840044003500e80c0d440405d031804c4071b14203000261310a41d00d1030251121841d03c00c0c015901e00f002c01c4030240c04800c00d54006035410440c0ea0045410524078811208040c2c1e88800b4409030562459200d0002a00e841c11310988110034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 17206337 1250 17205087 17205103
    0x2040e0a06090b10090312020f06010609060f0905010f300f050702210904090b01060c05010f0618020d0212090f0606040c0f0503040611030709081203010b040e0901020c010903080603 80
    0x12070380e000c444e000e00b49000f0f204052074000903000340d40c50032007010124020402107000002d540309480e01580c6d1111b0240c0072034101e21a050202d44103400003d011803140c03c82c00b0989505071102c6041c945111011a504c4080307941a006c1151150303260a441a01f0091001c06a602100c01240f02c8007000c520200b80c40000c0c0240b0190b50040190f0081e40c181a44500c1120162011881d142d03030840000a01074085010060241ca85400c00072490310b034004040309105000301c0090040799007082002049990034410a921140405502004640341e0380042a1380b09031041c016040001c002c001c40110807041d2502c095030303403020000c000745400038004198026002c4500700800444100c0140141000d904004200a0300000040801c11264440c0c0300181507440410745a01d041280902045c0c0c07140595403141c41840032041a40350f8081c100c90584081180050070329140038180034041030090403101d0503540a105104030843e091282c03a1550340a9a150903190801070b09060420302e41c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 17207587 1250 17206337 17206339
    0x7090e010605030c0406140112020f0301030605042f010302070804031406010608010e0403020c060307020f1c1d0a0b0f0403050a08030411090f06060a03060803040b0a020607050304050c010c0602040e0a06090b 91
    0x14044201f01403d0548440f040c10306003800d08e0701420502030782d010001d10910900b80880b180c080004010b10800b5440148228490300120101c140c071102d4695510080c0e88110007540a03403020040d0342d510a80281950911400c012030406459550703800110340d4441d6580a11b50000c0010010507602040b680d005080c4941c40e03a4a50030140c40081d150078019201501404000010440f2036100b0081c104459000b542910b84000100c1e00d1294040e82c600d12000000d6400d1520080d11080400044203004000344003015113840c2c00c0310034556411003d88515121824000040030410505c20003480c42d1255209507681e00d81860300c50400309014043e90f00131031003030003000001c0c3c800074125500f11804840f0300380c5440b511201100905003c1d08144000c1c000400c1c0046e100740c0040180490704459000e954256403042e1040720903000855024200342d01200803103820b54051079180200c0c6000e1000545881c0d210720701d1a1b940c8009a854a03140c3d40e40f94000c114100e01031081c02c0311448 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 17208837 1250 17207587 17207591
    0x80105010504060905041a030307060c0f05090a33050904060f05010c060b060d0c1110050403050403240603120e03010b0d02040b0a05041b0908030a17070207090e010605030c04 77
    0x304042e0300a140750245d0282c50b004a548814141e84420b0302040d00320807040040c200c80c0ea907502450850054048d030000100480d01100700001050b000301c003501e0f01c46d03c016082e502c10516095103081380c10f915004400300300c0001200c00c0c89527942c205107000000000c7d1903996072450004244011594141d00c50500440076000074041680d22013130016003241c0001d0040f403502010400a0194031a1b0040000b01a18000100229a401200031001d80304080c0030b584000d046210800f00340c500c212001000100204014400039444911942d01c40e40c205054625001c0c84200701c8003140d5082d0001c0e030780f061002c086926400c2e800155072409003002d400910000120101141c0612400704000f440340e5106c0400111075100c140b840d100400b0000c0090092400c49811a0001c2c0381030440300740021821040880c44440000442d500150103541d8000300c1c0c4200b03204c1070300018005c1c2c03d40c01140107038074001581000b140030308841c07035100700000143c043c5020209454240f000d030515008078 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 17210087 1250 17208837 17208839
    0x403120606140703090503071509050a0e0103230d090e0a0b060901030b030a060c03020702090702011a010807020a0c0602031803120708090105040e0f0a05070e0f0111030721080105010504 82
    0x2035803080710009898041c2c0040703516900246001d07260382d03505070405601842402c10000e418021851030b205800b8040e00c402d4010781e240c00501010b08480d000e1590581d40341001040000c440144051841800788c0400142d00c411140482c00d00d0407414ac540f0018001e00414441c0500903494660441480a000c2001c440c0701c0d00401c00714004c51031910305040c4c1e20340582e20241c070140705085071164010402c102d80f900548014009410105050340a82c41105c0081c103c80e0051249031500000c1c5106a030759850500c0046076110002800c035421802020885d00008a0800001e13001d400c0a402a5458101001c0e03900755800901d04418401c0d170058074070b004254080b00454488907004011260744004800060300c03a07105560180d000000401d003000045184074072020300030540b40f5800e1145850f5000200c1e466001045200d40c8825030240c00d4103250301a510401000c402101520308201107501d4001240d0322408610400c18111007001d08407581c044110f901520090030030500f05 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 17211337 1250 17210087 17210099
    0x907020f060c03060103060b030c0714070b0d020304020d020301020c1506042007051509010c03050a06050f0d03020118060504120809070b0d0f060305030c070609080c010c14070e04031206 82
    0x5410060b002c01040400040411000e901c00d0b0810006840d00c2007004d44d81303040244840c581d640c0400015680b11002c4000120518000f08041c000c481c5040540360405580701c00581c000d500c050300c104d0b84000c404a582005032008e0020300000c40252001d0034007080380700806509498004d0040c0d206a180030309210101c81010b031801e048460341410390351100a603162252a10340300f8618041c10510844c00c02c00040c3c0150400c3c03102001da42c1d003e06c251b407502c0c2e0034801510428050701c4e50080c40c80807402c00d1420080d4252090314000e1002190041d00408042c10064911074103440054540080100f88141c8020b540a50711a629064929141280540c0c3d00c07405240155003980000044c110b029950070b42007039000f403040000c00c001150b92803030b110f0360300c1e4810204040300e405080000940c0d01c2c0034803550f004540d00d51028022140c0110011550003080307050896200c40841600132180c882004a4001340030090211181414241006480b090344070494482c5e003400e010b024890 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 17212587 1250 17211337 17211343
    0x306010903060b0f0d0f1703100302040c12020f07050708030313082d1c060315022d0406080a0504030f0318020907020106060315050d29010f050907020f 67
    0xc590b00000d00249480c61140010b02c8403900c1d828440c0e02008030100f00f420701c0300d400e05120580d4425158401400301b03d0385c615640780070803218210082d900c0a8100f015041a4001441c2c41115181000c500340c1d1849400007282c00024028404131004590315003000340400442c405048080001c50840ca8842d040350760404070000700070901e000101d0445110306500c52518210011000c00188038011102c540c040c82e0400c50044c90014241c0003044000b0540e482601c0503640c1014254101b0b101020700d88019500400c00c0c000b038510b82d40b41900710f602c2c042c000c034a606100c80041035902c6180c0800182112006024019250b15140500000071b4009122030441c03c81410081444511205000d04040070682c011790025100001c00003440d6041d401202900c07a152020040507002c0c2500386075164041c00703015005089941700c407010450318090010b49811507040502c0c1c104d601d50641d001e100c4280d02c18060503004000502c01c51822460301a840521440103001c4010188030150b5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 17213837 1250 17212587 17212589
    0x2060a05160804060206060f040b0d120e040204080a0209010506030c03061009030203031b010e0705010504170309030a030908121602040f020c01090f0c0f0f0b0903070e01030506100b03060109 84
    0x500c400060305031051000e07203400185154004640c07a40f01c40c0c2d1081c02030b407107440480c0d8052058540f49620401880c0910400c1500e0384041c00b5400c1c80300560b070b00c10300445ca42c000c0f40414050701401090943c0c0e01c2d4001003004d02441c0018080c1c1c03046500c18018110781c183c000c01d101d000e0500400101380644001e07268070103421070b081001d01100b410103071050081600040d406002c001141036074241c902c6885140d46008a000308854000f4607043c40c0c075012a07010710350000301c2c1080200f00c0781c41c585070400c400c03c95100aa914201c1048c0010303140c64200842140070605c00f604c200701e428000d001c4154002c90181030b00780340c00005210b2601350305a45500034451503039603003400c041910650542e160303c000700c00200300014203403c0c10707070001c01000c80844107010311701d0b00455041485c41c44501110314088c0d4080006040c20700c81c100c5500302c01c03c0341d5018860504005200c40c801031600e030085001d04050300c064203040794a0f0b03909540580045481e440200b041c0310659070700200d000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 17215087 1250 17213837 17213857
    0x1201050606160c030614090f01060b0a11070f060c03021504020d0201031a09010f030c12020d170708031008190206031501030b090c1b0706020705150705060c04050117040206 76
    0x121002c42c00d881c0001c041c00440d040a409a4906031640c2000704d076608255010302c1d2200112008240c04038074141c00d03520395029007141400144841c038041801a040c03115051405000e4410080d2251401d26140b03015900440008100034541004d1580502c912000440030034080e00036071030180c012514040c0800c4000b41015030700d05003910122041c2c1031a14000704010100f0076a9650b03050782041450341c07030005894890348580e000a041c400005607664699001c0d052011004054131009030600040c218900758034070400000f03001034004402035205900c00601141200d0411700050700c0d0020541d444a040490800745c50050b039142400d80e03a10002c100040c40b5a85c86200040f4003a103041c1048540003202981404140c101d4140a026016400c03803d240c0c0f02c2200c031540766500d41091007800c3c05604100c80c00d00042c01c11131002ca8940594441a920b8111581d81d00c03441c01c0c0e800c4070021540c9001040a026640c0c3c854101040305000c01c01e04003a03414941c001600c0c1c1e2180f07060704 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 17216337 1250 17215087 17215117
    0x3030c03021c0f03060602011401030b130501020a030f050f19020309010e01090c08010b0a0e040303090206070b0403031a0a14040903090f06030203060405010504090809011404080a03020c1201050606 87
    0x1000c16208115041101c0715002401c401404640320290281081d1000c0c107000c02d040ca000440d501e4170511400086d41c1d00042a48002d0b441e54541894420010b49002040c040c00f001e140701180c02400149802860f954000404005a99487c0201c41c00940344408075010102440420141c5005110b030303642031a4001656925094a2203004205400c5050019402c1400f03210900030707071192041c2154443c0000380a91814a001c0124008540c0110909a8000c1000c42c011038030a902200086d40701034a145d00d00101c1d5140c8181a00e0111000c0f00001e45a8031200058000f0401c1c414401c0819108224400e0502e410700e402c400c14203500ba8052980c0e10184000e01d4802e200d024001c1c03961711118240c3d50344559000f0041d41c0202d60320b034022400c12000040c0c0c0d007064410905820b81003c41d8605024061004540c1003081c0f40c00100070600c20702c00800d501c2c20501c60010340720b1103500200246600788050048040d4020358180c40307a494402040140d46900c81200c400326849003030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 17217587 1250 17216337 17216357
    0x120203060f060a180501090c0503010f17030d090b040203100506010f0e030703060207120f02030a08130f08040605040806060604050f100201091502030403030e07051507050c0907020109030f030b09010303 89
    0x85043c1c0a034980c001d811201d240c00040071210070710350140d810b88424000500003012005000d582d18802031080b400030f5815020f080018200802d03103401c410030304205070707488c10701e00f11610000e17600501410384c0c0d401d0000e024002180703000c025140500c030030003000740701a02c3c0880018010344295081c043c144442002c03e100035680601c41d44020315400038085442e4034241c00c1c01e40441c500b50050f5408100c944100351150fa00001c190b900c0801e4070f9407402440d1355003400244480d96200c0040700d400b5294146440013400d000090700151074552b9406850b285031004103440c0450182c40a0b00880301080f090000f82c68254040c040d100050310f824080c5010494124010080b0003409095038964001d4407400508503001103000b180655400d00458602106050f26103920f842056800700071056440805099080503182a03401601030700c1481600c0004a02d0503402210540010b0f5501c9095204141e00004031041e100c0c4140303002c011900150000c581c00040c1030101a013844a1019 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 17218837 1250 17217587 17217589
    0x109020703021f0207021c020607030509030319020606030c0d08040303030506060f0307020a02090a0e06010504050601030e0106080109170c0c010309110d0c0612020909040210090e150406120203060f06 88
    0x30103d04184000014012410f61400740000790400f0800302e1003070360800c0c6a07544404040802d100e8403900108041d15050440d9000c1c4c801d0390240c0340094041c001071105031842d080445202400f038010b41c016001c5817070302108040c2030200d00b2811500c900300041412020600341410742d0266541820f0004443c1c40c0c0400040540c09001000c41c0e208078000204000f2030390100b4a83d60151095440b00c4507900e9201008090310520307051311440d46d11400040040d4a051b03081540c0119040c10009441807103101c466080d606075801042c002e0391600c2d43c800401141c0e84a00121190308100f283c1011740812140e9110180b0030300043c10140c5860108060111504804084a00c014600100c403212403030022261401849960b0204100030841d01425409000f240c0d00040001c000960f01c4d61207a08000c10311500c1e23600c0d1000c20500c0c2c2c1020500b0340440c11590300a4241c0f003502811444454108030686019401c2a1540711154a1080046c0c4000a01030b80001d0602d40e000702c5a0754201c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 17220087 1250 17218837 17218843
    0x18030106030f08040503010b0405090a17040506121005010203090109060f050909010312020c04181401140c030a0c2303150a0611060f0f01030201080408040f0320010f08010902070302 80
    0x40c1010b0150102d0900040c200079a40005208464080d8000c0c806100c0e803000300003c6410884080302c2d07540010408500240d868019082e4854004e1615420039403150003083e0582c00240310888241510000e100359110011040380080400344010340c501f0001d200000d0070903200d44103400900c5481e525803560b0500890a80c5c040c410701034089403072580c0d030f41049403100410302445c8000d0301a01e854241c141c03c2500422103030a00c0700b03c3c014041030903644c400c0340c0c909171502511390035507031214122108a1002820381c002e00c04101c4007030712401d00e40349c03084c00c41c0e05400f045010b00002c000c051400f0100c900c1d40802c600040e1140a440c4e545101d4000030112001c900c06d940021400000318941d0703008950074400208000484116940e200403a0810306029600d40d0841c0c0364000041005610850105a21030321500b81d050520750f48641081c10500345400c11504604a07511a000c0e5101031000220094024070b0009110702c4c0b4044058605c4106014441d801500001e416080c14020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 17221337 1250 17220087 17220089
    0x7080c070510030209180105240f040e010501120903080c07140106030c0f0815160903050601150f0f0c02010f090b0f07050105011208090d0201091d0702060105060f18030106 76
    0xd810a00d071950880b600030002d5102c005403901c51180100700d8071508000c4e0100d2410303100080c007a230710744410801d01c040c9551500e0034600c0711ba042c02c102d07441e002c03c00d03080904000c000d4485620344650405002614507005007904040440ca820700f10408240d00540c0c0607001000c4480007903458505d824050610300001b40703105038660a1000000400400041d0b09045400780200d40703001c1506c4440d41e80d00d440c0d001070b008459030382200c04505000540031561492244605103010754540ea65603260034080241c0c003210103500316426543c8103e030041000340c01410280f80191b1540c0e141e80020302806070180001e4100030000e812880c211340110207110141512014280d150742800300d002d00c541d84000c00c1200c0c0303942804000607040803010380c3c40d0105540b055165043c00003420600103c03007100d405c06d038100304859000060301c445111140900944040113800d441c40d0652010f8178055060313008500403802048000e60321211107094540d46076400e4001d130841c1c0c0c2c040d40064050425 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 17222587 1250 17221337 17221339
    0xa0305030703020d02070803070507050405150306040305070b060603060d0b0415020d020409060b0705070306022101080a0309051203040302011d09010602030d14040201050d02030a09080d020903060906070507080c0705 95
    0x100040c0007040c1600001c036aa900c284503800c4840c03c548510442da160700444200800301e51001c00280818a8903400c010750003500311071812100642c42c00082d14081080d90300b5804100000b03034200c00d00082e081c01c03e071b0204069880c0c074998141503000c952070301203d141c080d00f1000780e0004034080124100b1300030781c40d0900c80d80079911440f4006020700290701c1841002c044900e40440050419404010b80d100c030303074008001d041494659190f10020f580454454811354050207803410308105921225800303407504100502c600a442d244c050424902504500d205501c0700f41091040100001141d040d281e080c60303c00024807030f40102c01c0840346c2d00303038802d0b510122001c0086240b96000010784120483c005080c0181003021040710354004054402078001042001070f02d03140540d503002941c0100b0340000c0000c086500f40c4030f00301190040c94491300e0700d41d0001400c0c801458200001c81d00000b99401905036428120b001030030600c1240002414101c5c00300d0780b500c0b0160180a440004d00f4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 17223837 1250 17222587 17222593
    0x9080307030e0c090c0f160503130501030509010605030303070c030905100e0102120a05040902160f0b010906091802010c1a010b03010603050c070528020a030503070c08030f180a0305 80
    0x9040c10302a018140103550400c0c42d200b030300c40c00c4100d403904010081c090000e43d50500d10700115010920059406986c0f07200c25403107070b03003e16000103604000a203c41c100180d01c01440f6420130000405807034002c2d1a03005680e040080501055401000b10394014165080c001d03010001c514080d582054103070700080d488035041e00c001d81065044014090080b01c01d90948041c06140700046941d401540001c80004405002c10301003050107034000c000900ca041c0f410082c4640316941c8980d40507135100100d404103a43d40040044200710700601c40609604542481003402d0f444011840c034002c080f01074100480240100b0a100801180744258602c017602d902c001d41e180d019440c034640c401e10845000924000010301480c2c02001590100b82d4400b02408040c0482d410303854150007501480d6400c2e0242040745001a900c0340141030003140f1031006180c6070281410500b0030808541d10000482e0000c02c00070b40c1c2d4441100c12914045594240c01e86a02051000f29040380342c20340004002d48 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 17225087 1250 17223837 17223841
    0xe1513030507030b0a05070c0c0308030601030608010524060c0307060b0a0f0305010203040c052e120e0c130b0112050912030411040c0203040b04170102070204060f060305010914040b0a090803 84
    0x220721134046115039820881803060791107010044400f100c00000140219400140074070000714000d0055400200500d004254070b030312403140e0341c2120029501e2010303001805900400865500c011a091384400700c5900d81800050145a5201c1c0304080008103102d80e42c40410101d5903d0090050240400201c1044400d0b102d140650003540143e07019603103820050300000d081c2c50b01449000c01d80c503280c10741245001d050407900e003141203604e0543c1c0c1448856016420705401501c60f440031401200018000c4034503d00520410b443c00a002ca800c146c10450000081c2e40c200b1501c140880f114240010507559208640e410085000300714858004008140010b101c2e400041c40d078010000c07a020041c0743d0740e0034416603480c4500e1040c000407510038042041f0b046541480141c0da070100d800050f1410083d40c1c00101180d4042d0000c03100015490418003426a140c4207107800b402d0703e2041000300e50600b14403c1819240107100405804034407001070a1001d441c0c1048400c1035000081b41c0c0c1324 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 17226337 1250 17225087 17225093
    0x1a0705010513030305091609050637080105090c12031204080409050601090509060f0301062112021902060f0706060801020c15040c0302120304080f03090901060e151303050703 77
    0x503010100c4194002405d20021620740007001ca440c08050300b980343c59a410f1031070005101c0140000a0000740c3c0010840c08440d2003c00410601c21422843e81c00e14808201124041f100204150000c6035540e26150821042080010300004506811100d070100c80708000c0f202447d620411281e003888000d401c09000811081c14094810b035040f0050a10103036403404011610200948200703039002501002084190914440903544910050000310f0280d403101c0c0700800c800e0f07034003501c081400419a410802e01a0321411104180304600c0a406c0050300c06041c022951010500130307102e410300203003d0080c012004200e4681540c0000300340005a0341d6507400d0f00039044a40c0c4000c0500a0001c250041d0b0301e0a2920340c0305550019462000c00d065800b4001c03004001a01314425200400010034000c03020810105010428001103588001d808141b150300031040c5d200034140310406c0368261040c3e54000c5c580d41d00c1e46207103c2d11070301e8420301c100742c050180d12980054524004d241c0003000f4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 17227587 1250 17226337 17226361
    0xe01050103060b0405100303141b030a0906110604060510080f010b01030507050906030c090303040305060a0603200907110313060c020906061e0702040b06041403251a07050105 77
    0x1201d028500c100540f00440c024071080d2030085030340c0d0b05903510002007400024010302804881c00400702003907040200b181552901150200d000030804c1d840460024540c680c000c40b10401b8103c0ca103450011500e6000c0300c3d41d56804090301c0100078584070340c0081e011880d41140000203010382812644036102481e4564002c0104440b8580013a0414001a0350070303008808846003544081c080034596607801201c0c1280d904280f43c181d074140010407000000c40c40800c003a0780079108226000500c980343d49001b1f00c010702d2000c620b0380d0894050f560004143c3d12047c802c1c0e809143c070b041040241d1203030a00707541588115134601002880d00c40d0049a000e90001240802c00e200b076402504e1500d41c4000c01030300e13018180d03600302c241502e00020002c01000c4130240491604c082c0010801e200d44100046090700150800340c01601821110191450300308a401505498144407034908000800c03040303030b5100b203030051400c4800c16000d000d00341517205040303a00454100c0002c00c06e03030414083c080d41d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 17228837 1250 17227587 17227589
    0x3150b0309010507051303030507060b03030301030b09010c1b02010503040302210a030f020301050d02060f0f0403121b03050301090c0c05070b1306030204081005070c02040f02031f03120c05030d0e010501 89
    0x2040b503192400003552180101c003241d070301240c4003070045070040c0f0f143d400321031942c0401800c541454a500010805840400c041c0d4081c41c41030801482502d00700401508560240c40c0c0002040b4074105803080c40c01146508465142c0c0a18201e40e807a941c42c00c00b0713860403001840d461403103400c80c00500d058045100142c02490003680c1e040c000c0054004c800e005a00083c000c0d07507801013050301210014642413009000820400d0686030411440d034004c075040303170010303841501c000400903240b102d46507100801007404a0b00040b6614440441d8600030111b0105004291a4641e54502e1b4204c050240c4c02d404402544a4210307251203844020031844c07031300880c141540700c0744294004104640a4001d54058500d010014840d011096103240d01414020f0081428003100c80301c8100540c5403030041c0721041045180169503030034140360090314603840303c101c2c028544004400780005144040c4180c1000344914100e6001c1040d07042280c110301c41c1e04880c0003103601e010030310400700d60b040d04854 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 17230087 1250 17228837 17228851
    0xb0c130e0604240504091703040303021c0203040b0117030c0f01020c070602060103030203030703110405100201050105030d0903110906030114010f080c060c0c010f0201020f0a030603021306030803010608040303150b03 95
    0x4400c410010b080b100d44040a4480303001c000301030b0f61050000381041d038810742d440c1d80680e01e0384c0310441020804140315402680c00303900098000880302c1a100c00307890030304d50700340d20040214a507203070549501100e99818003030344140302603410003003810b00010400c3e10168032891058444207409844014000d41c041d544950b01409001c1d00060050300104561703040b6034158001d1841c0d907071a00421001000031049020200c1001d1202281503200d4503a03040c44144e2503000040c407035050800305032406161125a49c1001070321802403000680017040580c4810701513135009450344880c00000c0c0500a509080c0c4250a1444000611250b0301480c1c4011107100006a50000c00302100b070100c140320328102a200c5a00000c1d0442d21540710b028460041c004c540b000500302070703001844041c00d44c848141c2c040082d4544070148154600030381b10b101c0c405042001002210710710342c0c59041301c1c0414404c820a0002020000d01454040d41280300c0d00c914241500d580c8640703454a00d1041d420541d428 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 17231337 1250 17230087 17230091
    0x405040b010305040203030a0e010c080d02030f01080601060207050103230c0d050c090906190e0702010b03070b040f030f030302042c09010911060702060c03040f15020703020d0b0c130e0604 83
    0xe800d03500030711034940079036006000703545800009001540c40e01a03e0f03011078100f1140380c0070a4041101034000d00b4602d510018096030b64280142256400c0c0d206800c442520b41104004115054001075020700325002800c0100b001402c06110b0345d010790744003d00c0d1a80d461518100003000c1012070007008910590351040000c0d440f00c10b541c0c1d2007402400c2c441d42e0810040d40c040340440c41e046000320390300f00400e41d801d20f440303490b591040c1a980c01598030f480581e442e00344041143c03600b404140043c06079003c507941014507111a184402c00c40b88009040040c0010f0510305162180c0c0440340130780303110403890000e240e4080100202e5010307144500c1c0c041940c01c01041c02e0000600661000c1c58001030103c45a038030a208010342d9074485030040f40d010300e00300081c544828085c00508010480d8503640c01c070b5549001e03c2d141200c1c2c21604c41100319080304006100582d2804000d4481035082a95540c00d640c545840018134801c804030020903015601d000074400e52648080303032250109440c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 17232587 1250 17231337 17231351
    0x41205071d01060801050603090c030109050102030108070e040b010e0601020a050a1b0605270d20030d05030f0a0504030e040207060501031b1d0907031a040c15081902040504060b040504 81
    0x14460101e0000c2c090b4000140780800100311302d1900501841d08030f07a962040c0d40c100030a440000c0c0c01c4428414041300d180c0d4010004200b449170070300c56400185500d115140403403815548894000354140a00c1030007071408404a040c80e40708124001000d0b03030010456444c0030060a04602040302c13064140d020241075080811100d110b0026620030b401101074800e001c24118010f1141c4400420026401034880300c2d1803400705051034000d440002041c1c4540d0a4603c0340024542048100030240081c08000c00a000000103404074003070f4030480c0310000240700d488515007210001d244c0317001c1c244c1c41400840c1e42014022181c0c00076040300d108851a1211000d40303418560000e11902c50500103103d4440100f040c1c1030800340c1c0c1307a0301004c40c000344e403507054586e6075100049011805401c026035911081008110040034210050a6002403400241c03955910080c42c04a005020611091951140c104210000c1c2c0550380904001481800255103a082c1080706420506c1420700c40c50500e40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 17233837 1250 17232587 17232629
    0x90112050c06160f0501020904020409020301090e0f0607080702120705030a03050105030127020a05040606020303041506031709030a140c041407080103021905040203070512061207090c0504120507 86
    0xf1100703120080b041800c81c0107030680fa415903503007001e0030940d16035400708103c0380355658520040018220000006880b5414035064600301c0340a5400c201841d44815421044100001600c40d440300d80d030b1801d0300040d40c90710340c120708080404000c00018180841d10404010b408800751940c1220740d5000c12590b0b980b131082509880400e01840e40d82906413035a02c0c07610408000c08140c2900184c8a40c10a50359440498116080e9034001001a00040140410003110003a18800800060418440b8a0039030f11f610030300440c201c140d07941121002034000e00e55141070180f90401908001b02c001507014200c0115111800d10b02001e106d10b107048420414892003010b858003039000da5540c0c1a0030b0b800c41d400d00c44d02d5083c2814440b81129643d20001c1c4071b540b24001140703d210265500ca407211040210300c0c4056a0260040b441030705420032004203a0310000e00c41c07088403801e04012802c0b07100301600743c0d498883c5801c803d5810b8070717900500040c4000007603510704807031569101140d00d004141c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 17235087 1250 17233837 17233849
    0x206010302091f030f050606010906030b0a0603090201020a050d0807020c031507030902060f0a02010b0117130602030c07051903020f0303070c06090212060a0b0907140d0207060605090112050c 84
    0x10000a600c0054000460a400d0f01454450710100b4000c0424107401c0e1a9260f1442248a12604496035440b0800700812540c0c0070310850010050381c1414041c0c0207505000480490716401800308240d0b8501292040da88204417442e0000e8010003501c00d1030103001402030007440f0882d02c102c098400d51044054034240007032442c1c00c410840f00039941d240c550307100807009480b5425003039078040760a002c200a50304d1900c0050404403015000003985202e03640014040d140981e04203185290180200b111102854500e00d4443d0303070210005030303665115105100c81c0e004010003d4254170410f04003a40742c05041d1541c00800d03004c1d4085400221100c4052562440211105d40000704001d007540000303107094200e140c4c0c00d4802000d1404016030240610300d869400c4803010f07046a12030b40450301509181080f10f800046510740114142452680a400380c898820f569040c41da0006a91085c842203922290181400500481c5075513928590622298940f00042e14940204030110f11940340003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 17236337 1250 17235087 17235089
    0x501020c1203030f090a14030405010f030b010813020604081605090a020408070b09030106150503060103062408100509070c050c030a03080a09030306080102031017010203061503040618080307020d020601 89
    0x8107004514603a60f03046140301e84a400b5041030300c28400d106100001070300100038100d5640181c0000d640741c43c074180c00100240f20030740400e001e041c80c00001d5000e1340da1084a299001300e1014040300d8002c00c40c0f001c03c1c024420f5034844182d0b4080c100c605c00a5024107034000d0210307070b01202d80d10700903140c50007508200d00c694460711949501805040110208400c050480d00700c005000043c1c281d81c2c0ca514248000d1103484483c0000d4000080000640c3c15205440107401c5240c180400800c80a011840422410041c0405d2020a00c0040d8441c2000c090650143c0030280c034240035418030342c030081c022030032020701120b0b24042c8000090840c100003a0450406400d5034400c00b10303440e4206030341d00505212105504041d2600000b04044509000443c000d10000b201d560f005841c0400341c0b00302c100b040302000314a90040050045545c1d42003002000c1854102150b03550b51103a1401000a081d01e6070001017440d0050048020b000d2080003841c401c41c259020395000d42c08200c4226140c03003003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 17237587 1250 17236337 17236369
    0x80106091b0809010213090c170103170c01021303030512130c05040c021006030b0105040e030313141c0914010804051507180801020403050c010f020304050d020f12070501020c 77
    0x707440c81804465215901c01500451180c0c0014502401001101c0e078100703554210b0b03040c0b1500e1b07a42d85c915071980200902410103984148403081e50440c1e840001d01c81078101030000c12240421880c99012080d4129001c0c0035019846140c0a030384d03460050103541100c002150390389036880000e130341d510a0a9062942c240e102103400c41c0e0750b0608081200508858a2600461040c10410f14100c2c2052065601a50045c3d20551440d890101000140d0700d00e0301c4611140d400610501204840c2c503100343c141243c1c00000a00a4400c0307100081c070305004154400a004c4001005965451b0030003140c80903900d5034107840611544090055801c280241d4004241d40c5c04008046500281c0d000040e8000c0304600c0d010000c400a80d0f03504109036201d4100407061303503001804004000301082110800c0c4000c3c01d22011009070450b01035141d002d580706541c01200c0f100d590300b00315030b100850b075696454000c0c01004800c80803e81282d5814907401741c28054418240c0102407460310b95580149108 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 17238837 1250 17237587 17237621
    0xc0a03030801120c050301050f09060c04060c02090c070510020415030c120e03040504060b0c010501080a0b04060c1403040305070606060801120f060204030f0f03080f0f04030f0c02031608010609 85
    0x440d1180c0c1220b140188181669900c48200000c04c0969080c000c05000b0064040480c1d272030706001c072840c3d040c002e011700285d000b40e108100400090390802007441a07160110744105040d42d40d40e518000c01d101c0d20b8001007107406503184507268072080c0c0e40070f4010740d01c1d01d20143c02c500420000179004c80303201c1084036010491a00302c400d009000c98008480590404007601d040030342c0c5038049402e444041d004903000340c2020810302c08920003445030740e00525002d070090540003110307116400c10074400703003000c0c04050301c603042e1241c0c050085a0038000c206001000d140d80340743c00d040c001c00325000300f0401c965560a1500029209100b21100c070305076080310601203481a04c0d5640d00320101c9040c90100c50350f0380c0078000000070400343c400b01e20380b0034001c4680000d84140c0d880c00915403500181141141c0413510184503e05a5501031258030941c10700b421070740c1490b060700540d590807036000300075414454800160b400c24829078a140032035402c60700038407000b900c032000304065500401a00d56200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 17240087 1250 17238837 17238839
    0x20102040b090409060b0a09020d0f020414060d1404080307170709090207050a0209040605010e0c040305030307030e011b050a1706061204020a0909050604020a06080403080105040b12030301080f0c0a03030801 91
    0x450503500c00100030307219000004450b134409000c0703905884d03e0f5100d108e903a98007045504008006000e250813480b04003004500d402d0034441e00e00b950300c0d40d00380014018000420310842082e4507a202d24420380d02024144c010346420b103440103442d4403c0707070300c48002a0005807094850100413030141c000e68064480d21855402c00a40c40000d400c81c00c0203a4540c0319045a041c003517212589441d00417406a003004c201907041070138200c0f10f404003910a05000ca0704002c01c002007003011082e2a001032a91502141400800100302d014016120b0000d401c02051401800d00c540c0000040040040c55180d196414040c1401c02c03429442c11141c04d5000801008080c90426000c5a11a4400d200900525034941c841c000042240d494401c1101c03954403041c00d110551410840c504010003041ca415281481c00c0d40d401450800180301d082e00403038a400d907401042c2d817010600d640380401241281d480703681d60200c07a6918200364078108001d0080d01200342c40c0341400c21a1100343ea030152100402a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 17241337 1250 17240087 17240089
    0x5011101020c21040b120402121c050f070210080405011b05070b07090e090312010b0a0e040504020111010c050714060606030412021014040201020c010305090c09040515180d020102040b09 82
    0x100f2581683c045602c0030800c03000c5400c049500107410055820001c00821345001e1060100e5071001d860101030691001450542c407001c3d141c0520b102c40e2007460629250000354010500d03600808100a62160060720213044050707000079503610640c0540001d201501e000c80e039410014801850200c0014401c00240c0302050360003000c0352f004180c500d840c0307061030303520250040d40c031400343e4580e500754000003030500e42e45217446401744c050480c10142c0751a00c1200c14020f40074402d14a03402d4050f6403200001000e41e8002c000f9041c89096110003072111600070200109241d001e5601101c45e0030b880c1003088401c201c0015200d12800015200620310381f50781e114070102c070703001d034030202d0452180c0d45104010108034060008001013100c0f4602079404c0500c006410a0826800306040511702010020034403400280600c020800307446600703260b100d9041440c00e0203200902d220111504030180724418502c8591400d00141c07400a60710907210200d412400d070b02c9640700e40740c2d10038402d015041407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 17242587 1250 17241337 17241373
    0x50906090d02150c070602011a1201091205070605090703080304030c0f020604030b0403110c0109120804031a0f090c030304030209060303091008060f0a0b0304030503041a09010605011101020c 84
    0x122036802008511520115030020300c802031100011400c948021440c1e1010710320400c20880036000a00080c0000c03000c140b04d1814200e950a0440d20800014291004001003036012244494100520880c3d00c607aa0340007420980c030100048411504d00340c00141c0e4860302054038001d87e1f42c003058192a40d07d65403012a05200141c2c802d5170f8504040500c1310060740c4000044c0000c0d8070440349a40700e481d00d410040e00070307101811070240c00d4000c8814040f050380e0145c008415120803542031200b000882c10201d9941c01603400c0209034a00031407210000f01000d1403594803981103007040d41055500c810030683c0781c10f090444250554030920051006150891b0460341c03112020b4112824014880001204c00d40031508180c0840c06000c00e014140c1480e8180d080319140580e202c01070035150040d052618800103001030b0420402201180411107000d17509942c41c0e0481200301c805040c500030941c0245014131509021a010f19405a02000c06000791500c601c44407000e015541d48070b5001440b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 17243837 1250 17242587 17242597
    0x130605121f08070e06100c05100e03040b030405010906060f18021b010c03050124020a080a030603050714090f04020d060e030903011a030d020304030b011206060509090102030f011401050906 83
    0x41000c540342070108003002c00704450f40081c46550b03900d82140c1026014011441c0909030514208002800e80401280001607513503034082c0307984400a90185c21900290a50240380c000c46000d01001060100340001500038002c03190007201c08004440e51110308082d2103a1610403030180b07559003448040b0000413580600280d12b030000703030744140700c03040e05640c3d08580010b6000d001103942c8400600404501290070f014020400610103002c0700ca24601030741c1c4080e103580003801002d00103800d00080d440790700818011a4404104c4c0c203125250912510503403214018540207c1c54500000e40d00d10320b5813076080c0242e4000d04494a401c400380c0f0f40002801c803400c49181107110421507100c50ba14240300da8403440e08890f01000f141a10303001018100424090b0303000840d4403d01040c00400c11300d84039107045900148005091241c107140410213040164080e03940094118100200410103400442c42410040039010a07070384c0392900c0711442c0103e101c5282c0020801e01c0541c0041c00c1ca040182 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 17245087 1250 17243837 17243881
    0x90c020a06020d090b0906071704140304030b0106020d0f050403030e0a0e0c071a060f09100902030709050108160806040f09050105010609051306031109070507061113060512 76
    0x240001210752100300c2680d0000c0303a803441413542c07601080d06012010b01c072030b43c21010080240c43d86080c160710007400d4680b01e4a07110458840e610200d010083d000340a182d480c06080166502c0c6c564030700f480d0762042000d100303c40242c0503481100c020b00744100c2040303080218a03100c0501f00380c25510201d990031070380f6a1681c1c000104600c007040c8503102416082c410400100c542c0e56401040c44d04c02d4601c41360a00340d07000e20404200744000c554403070b1031a440e0a402500d4509603592003002510302001039500c8402140c1c03002007070104160748004804103482080c0c841c5001c0e6200c00d400345014060200744000020840804204240740c590403141d142c030618030021414030714640b41c290854000b81d102030081110280d0030891401e00900c49002201a84010045540f95031100e050404243c280f40e41700f007481c84001107200d405101900c00d05500140100002103030101107242503800040201685050b500d0001102880b401c200ca8141c01c000710b4a0140b0389644003e0083c1c8070b0b00410b25 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 17246337 1250 17245087 17245093
    0x3070803091f0e070501020615042a0201050403030b01020309012003040b160201080f0103050a0809060c060a05060f040e030d0e0c1f0e04020f18010908010e070306050a020c07090c02 80
    0x200e00c1d00140c500248402d000c40590024002001c20502c41c034280d0a035108a0540d0440001c00030300d02000700032014002410340b404904a0001d00d1a0b0f045035401300750100d900c14540c0d00f0401503660540c404c0c2d208500c01c1e20304000032002c0300016a624010081d180e030009502c480c031810310140502c0580c040c00c82d0341f422641001d07140e41c8800c60319040021104400e00301503a010b01590f03804016150030030080c205503889035040d81c44150b02c07260b5105000e0310004000442d40450786928003180c010b4039203401540d049040131011840500400e0f03441c2c521501091400701c4407484c1620030200d100340c1c640e00035890850845142c10242c0003030380502c0c031640140e1286090702ccd15459210845003960049400c80e002d100c0f10090002503444100034061403050145d40d070020005021605000d2000c031807600c0343f80040c80101c901e0101c5400c19005542012024200c0c000006030b00c8041e6445079030188001e84d00c45a0500480c010f40e4030090b816485040c04010380d00b02507201c004d00d180e081c81a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 17247587 1250 17246337 17246353
    0x3061f020f0d02010e070b0301080a0f030905090f0f060301051509040f020402040602070f1401050304060b0a090e0307140a111c0c060507120306060e12100906020318070501020307080309 82
    0x4031a0038440030b492a0b1000d40d46171141620812000d115610140c10100702460855041134981d50ba41c0000d10340c010540840041c0900515000d42e440d60700410000300705240901d4464101410028162241c084581003180460090714045c0161842a8800b800f603482841000042002038000030b00280c9a180303a041003030006d600c45000030000381c920707034008140c01407501450b24000101035001180b116290000c0c0c0d03405070b0f404400c40390040e4208402140f0080315600203400d600300e903400040035900c1c01568400401001c030150610300d024440740c0c0e50003c03178460096103445c588040101080b0480d0030500052601c1c1ca10800451050301c0f420b4141120340e0744400c050405900102d020039408030b4220b0400400ca10b1411f14201d0321301c2c0503c60949419005003030300f0018000c0503c500030b0403060000a540400603500900c0001500f0700c011409400e00728001e520660f0004a00d102e0003c00f210118400200ca10031200182c0c01540b0703004042d01e804880d5000074084030503e001d07101c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 17248837 1250 17247587 17247613
    0x90204020a0207030c080a08190201021903060801060b030609010e04140604030216171c03150f090e2109060415020f0d0f1202090312030a05060a090203061f02 70
    0x4050881e40001d60001c065003400c504040d800d036a00d603031040c0360980c00403d80b040000d99640c00d0796814402130405442e07203415910240e0190003102c00c1d81443e03000c40c0e0300c01ca01495050700070f04205d60020008000103922024240f8051108540c41900042001c00411a1018005484d90b100d070240300340c0e181c0e00f034540000c0e40c10b0480944090b401a800f201c8200d10149804070900d008181940440c002d43c0048400542c440030504a03d0b0485239003048050030300303030107900301d41c4030246481c041d140382a8813004680010700d280c2c0611075003d0310300030111140c0703d000034801484511071341c0d0500a000b0070194a46456015584660b04010240800960441b03129401d00101c080c0360080d0246c0d4450803036051421282150803170810402d40c42c5019001c0d04106520a0054078135409030b61444150007107482c0c1075490003460450a00003013000000c40c81c2d58403480c001c3d442102c0004815030b5549200081e400241e400170341c07103040341c8401002800c82500e00b9080c860b550058400110b4824 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 17250087 1250 17248837 17248841
    0x40e04050a0f0c05130b180403090512010e0601080c0310020304060213090b0f030c010f050f0f0a02070906060203040e0c0706060e0109020904050108060c040b0d020909072001091e0303090204 84
    0x21800300c0d0690500c0c0018821442e00410162071305c00c1c1548100961541c80c40021540c041d0340f40748500095a00c1d02103001d00d0320465640c1c0140101400f041e201c5010305074004c0c02032000380340d44141c90143c3c4001040c600c0001c540440380250080040078001d40b103d04d2080258005882100d00035420010012450040084900182480c80000524440d030f0400e01c01d0010840f00154402e401803161b000c0c89a0300480b1100c4040d25a02d052500c4040382004481c05200d00c04c1110314850700030881c5a002a40091094282c0f2002c02041c03000e50381d80e09041c0c4c0d0740d006900407070440a4039240040c01807240c500107003036903500419008c00c81ea90b5030443c0c10000682038001c0c0c0d40e0a500003c107030716181014080d0a00614292008046034a030003251210b281c0568021588540c900095190015110381c0540c0d615180c010129101420082000790401ea88100e55101c000f010b08443c090080041c4510f20100340c022035043c2c0025804180701080603c1180f0840034590784980040c0980c640b8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 17251337 1250 17250087 17250113
    0xc0c0f1009030e040504080a0c0609080705011506020105040507061b020d080406180b0406110a0606060c15180201031d010501090209090f010303050d021303020d0f1506050105040e04050a 82
    0x40c100042402203401e008103d80203201e885030040d030503d401d2000140110701201c500703a189180400d21111186000c0340a810000405890400d011036818203010066000c0c40c9041da0001c90988000e5032040b00780c3c00e80302c04440203011a0428101000218056980301c250005c080c40d0054010200b503000890071500b90070160780718900820180015078000d002011218032191849030b607240340c0145040244507a010341000c0103640400d00084403420403040072482e41c051803d2140c191a1500200886132400095691032075480c06070300203148500c103812011008800c035078500c02507900154091310407242600500303040d00240c010601070a114041c064441084096501da030142c040006018010b050b0300c4201d90020010400a82c000003220403100450030050b8071017801c2011100304407140d03840a0b400c01c0c00e0715901e100300440b41d100e45101301d22072400c945051310070002000c00c4440301d000300c03801b00703408010502100306c11181d520340c040e10a4007100e10000d11641e94450705041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 17252587 1250 17251337 17251363
    0x110d0504060c03090b0310080f0102090604140d08070b040501050a0e1525050d0f020a09030f290906010e070903030809010b0a180b0105090a0b0702031203090c01020c060903060c0c0f 80
    0x40501f0900031280d0a010a5640e40d800c58000d5080c11208400600107115034491040070036034044440c8040e440f010510800560402800c41c0c03a1038480c20300741d54140d402c4604440c5540ba0800090f0148814400e040b0401400d02c01030a140b1a00006518681c01c05001c800000d01008040018031320f000355252040101036482d56154075081070520140d4140400c0d141c80c1038014000b1484082d4031242500440390464181286007609003440c94500a6105d8904c44000020200d03010070003041c10003901803544002213600b10b0380d0b80d50030040711000640c0c800c000101080f50400c0400e204000698025485030b0000a00c6174060300003a00100117a88040915400c84000000646041c854141a0b00080c241203250100c2500083c036081e03c5070080c2401400081034440554a003004504080585010919544d042440301c03269580396007140e660062040381502481c07418600c050380c0c9035900180c01001d2a4442d002c20305c000d0303000380350384646501c80c0007100ca2502408000c0c042911507 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 17253837 1250 17252587 17252611
    0x9090a050c1e06030c040906060314090a030806060705010612030804030f02030c03070221060103210306080d08090a0c060c0b061e01080702031b010507110d0504060c03090b03 77
    0x42a032030304904058801984038416203421505464200070b9001014445004554159480d900d09901180500407604507080080c0b4040300414100d4050b48101c0c3e10880c4801400c005644468000e542c804050748010001108940420200c0c284803001d4200301d03104d600081919500e64010024841c1c0209054002541040600042c150030650311050118035101031841e003905a09000c4c0d4034450901d000b402003100e0032003c004910f150080e0b0032440c5400d0f055480c3c0756982c1c207146000103d07400780001c60906a02100c0340180c000d01c9601c0c21640360001800342240e81c448241e55065004084946a00840042e04001916036500300058400b60300c2d41c91418800e420200042c10b40105528004c01c9200c3d03101ca00345412072200b8140303c8003403904000c40e940700c0d2022400c6000314940700c82c2c2041d0703a01258825103410f400052180c0340e907903104c014680c200d982d4141d5550854481001084041006000a601c128100e00b0b00c40e00904020030b01650b11000d22a281d8070844003819141 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 17255087 1250 17253837 17253853
    0x6050d0609021008090616200703060605060403020901050607020613150306060c0f020409030908011a0306070203030705030a050604090807060f0e120406030b190b180d080304030318020909 83
    0x103d000320a010310b00c1068070381154185003924000d582d410b80a844082000f0007180300a4a00d4454503044042d80c01c000c1411180140b0100f506580b0340b010b0004503807050401201180608106090342e040300e400401c0c02c4c42c1c60346440c00384501c0381d10500050b40c00c074004204003000307260300c860004004c0c0003041400d4129580110002e088070025041041000000c01c003060124030910200b82001d90100c0d800141c1c0420b0f490305481c0c00c02d155100f80300950805003480c07801c000101d24050681010703400d0310030300e5407a800226280d1100b140c40c01e001c100c05001082c5c1c45581e41c0d00c6294842005000024003410a86840403550009502101e01644030b0501e1020f5070203a00407845221501c0008000300d41c80300000180c01d00450180804140c0d40c1c5a0b045426910840300e1900466083c2c0180000c503129103c08800b540000761001210303040d5100c0c444076003031071041e000c000d68100c000c0509649640d0741c12800380c1103940d040942d10f015140090096525145580d00807000d460041441c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 17256337 1250 17255087 17255089
    0xa0306180c0b0702090402010f030e0d050c0f06060603011503090203010212011502060402130c140301030804030308090c010c0b040f150b01020c04050402030a11130903090603060b190509010306050d060902 90
    0x19000030b4000d005540801d0184900589485120707541082e03090805109510707294004034010030540344901d0ba10721800040300300c0a500b0034010300110207010181d407240307418500083c0d03644d80240c4840d80c01c40e404000400903142e6146030b15046000709d01d404900e07401c50340c00103820381e000300140115140418004201818a400041050901c02d0016006c18a81500040c0c3c030081020840e0300304c15190b0000400f081e225075004480003030b030800a691a540c6a040a00da5030f082400308402140203200031609105000804510601050f503400611072440c5d40c0d82416414040e00071207c40c11010100c030f0001c0c980c01c00c03001c0c614140300d80000f001001c035000289426200421203000e03d180c00706110142e20302203052911a600907103440c21a400030400300e2039404145042c10440d518254048080540c0040c0c0041190602e680600020780c682c050042c0710b2140ca200020905071805010500c00e0080000d0b040402d014140021100da07610b0116403c000740d030314120740c09641c500c100021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 17257587 1250 17256337 17256353
    0xf0712030522050c0103051003020402041d01050d0b06011d03010504031110060f170c030a0b07030b010e03060a0c0509060d020304120c0503030a020c0a0807050c0a0e09030d0b0a030618 81
    0x22540346006440382c600300c41c0c6580e80c5490740f203140613041503164000174605900010051b00155030142085503076564076070515200002e0014041190608100005aa03141c071100d100062904260003030000d8850000664541a42031040c0003a92945e00d00c1d0f60140e0780038441c10384184d020791201c501e10200c1d02d41e80d905081030400314100c082d00c0c21005004016440c040d2109542651246040800003400114502040f031048264180314042c160410001d400700316502503c202d4506000448200d00151003480106140640640c80304002400504594112800c42500c078146186440b241901080e51a400f040d2840381484c0c000051004028009a11804841c400d2802010503400740d43d075540c8a10001d440d40700ca042d0003054042014034248010013103194008070290391051030780340c41030b1640819694a440340318408800940b07034101c086503600c540c03403103030140d8900119401800d000b805400c00c031641100b00090040300003100351240c00d02441c9c1c0780200300391210302407a2200c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 17258837 1250 17257587 17257621
    0x7020301050916060c05030c0105010b1801020303191808030907031a061513090204140108060301110a030c020f0703030302040509070309020105070215090a03030306090e010209090601050f07120305 87
    0x440c2c3c00140c0340c1009990500c0181d0549a891402c80c0d01e040880c100f080c654001d07052001c00d50f501e000000a0344a5171400204410240b0b64844807100c0c21010043e40c880c04212000504403d6290381c1c0381251940c2d0340000d1007400d90941c08044006140c5035451241c1080f1901c0c00e41e58402001030003400561440300b140c8201c0600e10300304500e4200301140b0303052501c083c0c24064500206018090700d0010700014040c00d28000c0464684d6900d20702e051781580c03a4103505000c10030391000326010b400c0c1801001903840b1880030691500781e41d9281200201651621402180246486d104100000b805840015401303a54096142c6023440100400040090840c005140c540205200140d800c03100740c3e40000d4044078202c40b84007d10025030840c0c481c189240d0f0f402020084084201501a841a005d81e050030900b000046c0e0b000c60313154200c0c4206400c40d81e0045800c00011a5984a0002042c003440910306041c1801e902c0c0c0c0d600105103800a842c00086503e8404201c030242c1c510f40007103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 17260087 1250 17258837 17258851
    0x180f0501030f0602030405030c0307050d120216080904020403150f0b01020303010f270207030305010602071e030210021203040507050f06030705120a0b06120f01090b0102030f0901090306050c0702030105 89
    0x205524540c0c1c0c000b140710210314028000b54000c800101400740c280160380d2040c4840d02a00ea03038501603d4003a4503004a003a4800c00f285a002c1d0b60030221201e40700fa5540030b508400034560745c182e55103810507590001c0a409601ca81c007084044009160007100015242c0045400b203148068a0020b4003619007080c01241103500510040046039000c096031b508441940d0440c4481d1060f0780c0d29100240c25540c0c40c0c84129000090b0781081680c5940071504a940950036200ca00d500d03000007440302c0800d01440c140e0700502b03400c28005840c142a00e203a50881c42d004940041000e0910443c407a00100c400751764580280f9010445400e0041444021010031a0f1252461030000006840ba016948a80c102049001d0025081d60640d5010341921f400003041d0b291100c1a090010f80e0056085035080d10b5201300c072000050900311401140e540b02c00c141c0245080002c508004409a048108100e04028410350000003180350362280a0048107120b1038285c1d01c0f000c038014142521000341c111 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 17261337 1250 17260087 17260091
    0x306050601110307110a0b0301030305071211030d020306060405120a11090c07060b12030c010c020120030708040f0b010e040302011b02070b130b0c0a17030606160516180f 75
    0x885405202200b02d5280592060b040707919485c8000200e40000034030303003100400106c000004005d041c0c00c40081d050551250700c86039207500040130100c420601d5500c04107143e6009110351449002d461b00950351044024208905141c0e440d000290b40740305001000c441c0c1e800c111400b1043c4201103ca00391405420f84001c0310604002510380380910505001419070395541c05000510b80d0b400d003e5848182e00c100403282c0302e081c0080200e000b09090b4402d076025600e0003800d8613401942642140d0040b101c10800380c1503a40c1d07142c058400180003442121f8400c1c26450300c600207000c1c2d81d281c0c1c0c06003061000e9100581f0b0a440e010b400c503071001d070300000350144800c4299600e40d4000341c600f0540c0c110800d407940310007060303c03050342e028103d4000c0001408007043c94905940000340440800e070158008da41502c1301b103501c203540f07407005454054100c80304100c0783c5e401491408191800324070620407160081e5200203c0706d190041500800b0701400c0c1d0707140890036204540956907111840f03000c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 17262587 1250 17261337 17261357
    0x6030e0c3105040b061309050610060f020606060406030510080102040b07030e01050315040e0109050709051f0f0501030504030912030207090f23040503040312050301030b0f0606160501180b010306050601 89
    0x113100382c3c0c80c4010150f034031440d620413403a484807045400c407411251348035007203070305a042c80c1c070030181402e566000e19030000f03440081101000c1e1002030380c2406414042c107800c0c50541407410840142600500d4108586100440024030000900c0204000e01a040c40991141010320300100704071000100541040740c18070034000741001000e440c0c0300140d03089500064119000d00340e00d02400c54135070054107900410700c001a4882003904914428004c40000c007540200034625511508000d0140702003005002c5814040d5501980c44650858043c0c200280c441e66640f098050440c42c8803070480c01030b00156004c20041c1d050703002c0c90604482c1d190b07041c40341ca2903600c0143d500c00310030b40c074009958003010003240030b00c9001e100b207070041c40d0840000d41c44041c400c036002d00240c0c03003840f044481025010004d200300880108003401080010a80d03440c22910003500901501c45034825034540d50f03501c43c1205a6040d1480f21174800b4403412107400c096145040a0f021a10000c000c14140400040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 17263837 1250 17262587 17262593
    0x513090501180e0c0a030c0302030114041a0c0f2208120702040b060c010203091507020d090302090403090902030709031509050304060c06020f0301090e010b0a08060106030e0c310504 80
    0x59110700500c16078002034003540e000483e40ca0820b4050b03070190801c030740440100500002c08290301c00e8030300946c028000701250b407040025000f005c0301e015000f81c0d4000c070810301d5042601c04060b00140d2024055003482d0840417007540980c031a4108010240c0301041c15017802901c60f10020090091f000a000d03c1009195407800e58410180d0092040c1e50b540b540c2c0d09130380d4032072083c0c42c07184108000031900c0e8906a0405580d07640c50725924500d20143c8000245440d100044c880d880e80b0036580c0303c1022501d140d0a0110f0148042c10480500042c0a000304090441c3e03c040c41c0b05108591382c28120620303500740385828148131101000c43c541045a80740100d5000000c8900300e0f620b80c0b03008103a00300030b810810006d024400f01d43c0c07e456000000002c4003034841e00803031890f4400d02c008100302c1418600300950210386102d601001d401c100010821107000c0d034840c1c0c03884407140c1c0582e007038448003600040008000084245048404c0300710090f1b0b40106400510034a02001403c00960500362 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 17265087 1250 17263837 17263859
    0x4120c030203041a07080c06010e180703031103162109030503030f0405030c1006090605040e06040201030e010b0301090b070f0504060c080d2702040515090f04110d030513090501 78
    0x1001e14500c8020f0360503501004040c100c1291041c58014101c961601c7d0400720040d2101000c0c400c086a081410b0082104d41942e41c0d9070380c10500c41d81c00185401c0780342d44c0e000d0f10740c20b1144104d15080d02081c02004034000450000795003803031141c07020529071540541c0701483c0170180d80d507140812010610a00c002000001125080341040c4030983d0300b59642e2070418074520442443c001a4050103501c4200c11100d60861402d58202c02c5050203010b80b2071003803108585c400840340b405a0300c2940401c2c09035000364040c00700000144004550703558024046401d40d03602640840d2298105010481d1441e07104481680e00011858100e00cad040c50800000c0924600501c040e280300c1c1e0004001d01c0d00040c41d0b02000384c018902c00c03102c82c2c0519460b80155640b003400300682c000c5040c180040c400a681031040441a10700403c00c5000e0b0711034003115048101e005004071014400705030a074041d81c6e81d802c8484040342c0700740c0d151903507030819902900e48803105074013441680342050014425003040e4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 17266193 1106 17265087 17265089
    0x70807050405060f03030307200d0e0415050102070b03090313080105150307050a030305031504020c0a14061b07030311131403030f03060d0c0e0703020304120c03020304 74
    0x100502440d09804e2201ea43d0640041001440c158060383c41c40e000800504401070031201007140d201d03d025040c80710b40c004601c01d014102e0151601d80207100607031151030400c4841c0d07031502c00041e42c3c0d26035500465162200110000d9013403881001a50421054000c50030079407565212018020541520200803a0a0120150b03007941800600d1a0448030040c0511448a00d1600c0456050f000a41818900c00b1002c06010f000d0b90341c0d001810000e00b05a02603c0b68003401d1500010013201c920116406401040c10081100104075812641072105100c13559548070f1817400314006c018409030307840304400210b00b022862442210030300641d038841d006904c45c03079904010569280595060312148030b40800002e201c508240c400d49009501c01d001b440c44141c0c0351080d2807040c04088440c0300c006a03000c01008248110ba4038101035807446c03418607121540c841d07203009407244a5 = true := by decide +kernel

theorem cover : BRFrame.Cov 17086337 17266193 := by
  have h0 := BRFrame.cov_init 17086337
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17086337 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 17086337 ≤ n) (h2 : n < 17266193) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
