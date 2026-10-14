-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0464
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:56:52.278642+00:00
-- url     : https://prove2.me/submissions/964e735d-8ab8-400b-a60e-e2b7682bfd8c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 83273382 ≤ n < 83453238 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 83274632 1250 83273382 83273417
    0x10207050a0b0403090f0602030910030204060e01080411061b010b01020a020a030b090717010c02100c0504090e0102040b0a02061506070f061d031b06130b010b07050a0b0f0403 77
    0x169491a0008014803084900d6500c0100006000340309600300940900d001c140201042100380c024001e40d8000c1da11828942d040041900040108074241841044100001c42c0c128141950342d01003403d108440350303134500307080199403100340354103600c540001055070011100150403035922901c90020080718588200583e641c00d0b54442c01b950002c2400b004200084007205115404002e0700103035040d00e55500390054420144807111842070351120b181000540e4104040c26043c6080c2070107011203407410801500e5442103010315024692201a4060250ba094044800070b03c0503841160f6505610365000b03464036419034450640c820001d440965030324101017a07030345080e0040020f50400140e80d540d00000c0203944019200c02518514403a040780c4c051014005e4081c40c50403600c0d11035031000d150307030901b07030002e0800f55081c1c404c10300d01c8045403a9052403419100f441020b00d584100c00c0c00d01d58035000e46c0030001000c00b2204420000c01900342d00c6124003c40c40303274a80300070108440300030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 83275882 1250 83274632 83274637
    0x4090b03030f1e07060504140d091a0f2205030f010b0f091503061906050303130608060312130302010306170a03081306050a0c020613081905390102 65
    0x12228240050206a1000840000f8102a0401c0b400000e24084c41507907484c050343c00484081d61020910780002c02c41140500807920340f401c0360319201203c2801e00301c1c0180c1c4603000e40c0814580c2038005c01c030590082c080c03104850140810b0108800700205c01c00449104510318011140680200a1403511201d0140507404040600400040b2102845030610183c184000c25048100519501041d1552410b100ca80d000f650160301d4200078640b00c0d83c41d007090303604a6000c036001c0c1d0710130010402107407254070310230058801c07500e012070b0786849000004e89003820301d03200c42d1190f8100141c145017042240100500702d0380300380c070103205035030351010041c04100b800109548a41c00050007800024443c60303603164000100e00a02a0219241d100d0300b04581084801807001036445205400382501000729581c4882030400b43c0189245551710400140a82c0f00c015152841d40c055000c1400c1c05801a04c142506140c07038107000040c880300446d0801c6000c500480340b900751f03030700c803800003c4103008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 83277132 1250 83275882 83275897
    0x30c07060207120807020a03023a0201050409020d021902010f0b04060303080612031905041d16122a0e090603030405010e040e07080d080109050103150b180c04090b0303 74
    0x1103640c1040c0303c42e00d40ca22564040d50040740c0c400032000c000310060340e580701030701950311803400e0402c036032032031680460b9400450480d00050030121030010710050781e020007200e05441b4240809a15140240040c0c0e010b8002d4070040c3c00b20000f40c450015030b16074154401004c031500043c0070300c44078441c801440115221740c0000340000e1140d00004a8a08207071100d105140785e510100da10f040703810a0540d19004440c5440400a9400182001500c601020162660b44144444280d03420035092818030f09503484881c2e42480b03500c01c4000001a8035601501149a404201c08a07113042014002c0c003400090692101040c541041d4090360b041c40b003846813041c40b010700203518103401c0100569561250b015415403098981000008500c4184001c80003010100d0040100403e4000080c1541105820401d1210320308401000419481600050f444c5c0e246000027442d4801100411480074050800600c00d101200c140140b1000070002401291003505041040754072200c00c25490340328405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 83278382 1250 83277132 83277149
    0xa110313030f020c06130512070e041407030b0703090b0a06030302101509090c150c03050307080601050c0601030c050a0603060b0406050310080a06020304060f021e0a03021308030c07060207 83
    0x12030000003902514400945600703600440e01144031020000f82c8076800f821407802c00c001908000c000070f0a0000850714140e15110150011300d0404130508a507510060000c1c203d0351400d8480c0b41c20f00010301204e0099a00100280307041d1038407020240190070503d904540711003a103030014911404920400302604d038154050900c2c03c4050321248003401010100400031120b6120000f03082406100700d00d0007603c141e0541c10214075091050402201810b442001d1080c0d030101d600009a21004607680040d075410501c140d5200c282c0101c03824002c10903007408074401d500010003480102d80e00102200c00803101000c9550302d9900c100c00b03544c1188070349195178400344001e01085004101841d44031840100740c0c2c00c000d03540e142c903030f1031b01d10744903030548820707900006000500105010380c20000c540401c00b54540303494410340a103401908080c5444650f404248151414426011180402c0080d48030000036a20b440189840e54007a40c40300c1030521500e00c0c0043c11a0010a43c01d04940104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 83279632 1250 83278382 83278411
    0x8030106050319180b0c0f0c0d0f1404090513020d0606080610050303030c0901030207050d090801060b0309060601120b1003050105190f090504150203070c06050f1012020d0c0e0a1103 80
    0xda0320317003a0700f06025002c0c0e142c5c0e10013030010701d04498807e4098010540c4075402825002038030392000d400701401e8000481001100c3c4002d1408420000072182141c3d0045c0780018540c1d0b0360032520f26400da00b804000d6000c0c802510728414452a034100400fa0703030001040d50714644580d162807401d6041071003000c0d090b400510000315810450005031600b0101810003500d4004180d0704c180c2840108040d110101e0044e100170312070060240b2840b0040c1c2440e10b40c0510b1400d000c1e0035240c3c0c8010081005040100c883c0c0f508200768601d8003c0b094940014003407240c80160b00304064042d0109005641c09002441040c419065804a11200b01c8401c030b01e240361041d0814203968040c00000304181d40301c5441d01042c1d010424644010b521503690355480304140c00759490030301d040d51005441e40e1161860b00c42804110b803590065003048401c039118a4011011500c04903d881d080754201510a030001c0030b000403141500203500d441694a4413041080088504108090f0700003500d00951504aa = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 83280882 1250 83279632 83279681
    0x80306150a0e12070b1b070603090206090d170c01090209060301090309030f0807050a08030114030c0f10120e0606012019030c140706030e030403121b08030106050319 73
    0x5031a640f003001400d002910f515644039503450f8226403103045d0400381500d01c01860b001100e403e002040207000246020b21500c0c04c2c0707400141850140722035580c0f02d8114411103504001420180403027020304012000e440340c0c8c81c82d8503079009128454081e4004c40c0b08000203100ca00d018843d45c3c40440c1e05840d800100c1c1c3c11520341960904642c6011a4190000c00290010070002c002d020032280c810f143d203c4da0b940c104090f600d884514043c13040d01030343c05031480d16055035030b0501191540710240c030100c044a1642c0401c0f100c02c044006a40340c4c00b07280010300500154081180b038480e080a07282d40e00c01c10a00140001c00341d00e0040c01000b1504107035002d52084281112003440700b40203141c86042c050860729140c2e54038040d100300300810361000d030707080000c07680500628031000f0343d036400b4500303040c070b56102e81c0d4414071819200c0007001443d00701101c582c4007000800c40d0b01e64010240070744a43c0c64580c080c01030b90098510341f045150050403802403088a0040f1410540c040141d060250700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 83282132 1250 83280882 83280889
    0x1030b01140607140303180a0f121803110102060f0c0702010c140d020d11011505090a09080409090c050d03020309010f120c020c1305060901031704090504080306150a0e 74
    0x40d41d03900c282c0e21030001c002400106210b01c00d116074010344030f0042c5a9070b04100300110400c60040c4001616a0841d43c14040400d00c14440d0144885d0024148002c0c036940c4041158540200c0040d8012989015404400d0004a400301821082c0a80841c0c109403504140c48103c20b80271100085180c00c2080380f1401940710b2445000b0762845411a03541c00c00d4400300c05070414045601c270400591001d1522208245d00100100e60414014000c0150141c00140342e80c5809250080301d000b006e044003c40c6900100380d000b0386002d43c12805440d1116198041d40d40a0300c1389507400c2e196520000004a050b180400c8080300711603040d0010340c80c0072607120055541078986030b201001e0041c00140a090f804c03050080044041641e40034100710382c40da000700a140d540050101c4081403800b820400c15031a10768000d41540e07040504116401c0300b100d01c0b00761600c00e03074005186441c213140600040108110103980616011600409803035815041d1802e10300401d07071040001030440e081c0c0c000c40d04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 83283382 1250 83282132 83282159
    0xe0606030319091703070506010b090d0b060f0918070506040b090d060905060a02042c01030b040609050d210e061801020d110a110a050a06020a020309090115020d02030301030b01 78
    0x22a40c100214815a2400c6460102d003140c040d0130300036000001c09004200041c480f9034058901c400420303051810070008035902d1001100010050811200414078550701c0c07101040400c50020402c040e64504940c480d4482e141140c2910540c3c0701e82c0c00c002c6964a411415201590b8085100600385070f000d40400c0340c00c000e030318400c1d2219640c0d010003001040c82840118030801c00b101d005a81c4902e003c9005a401c81c0359040c0f2001c0f0901203020200c4c40041c004128116a00302088004507110b07821720b10014684924014881c0c4181d241000c0d5a0b0b401040b426000c2d51880e0024000030220800c0d40305031024000d074900d8a070041d0b000103d1940e0303410704010281500a00050400c000030301010200d80300d2000050b00c085011910703038507155016a14a8045840d20f0140045903d80d903542507030b840207040010980d680124404a05600c00c005449903041d004101d84032a50359034482d2003d07030012100c001c0060103020f8440603520700000c12203048a512198100060b1728081500c1ca100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 83284632 1250 83283382 83283427
    0x709050904060b0d02360408030103030f1701140a080123150301020412020916020c0409020d1a06030f030a081f03020d0b011d0105180a060b04180e06060303 69
    0x4c2d402030150003584600440c1c00e020f846500c502010400c5803441c80c3c001d10081c5e180040046140400c010005608800385c0c0c2c1103e40c103050a01c0d0b0707080c0654065407918141c4404e421035034441000010080041a1500348510b0240c1f541010262140f60300d0342607805190312415255000b411201000c07071610241c44c2d00c4842d000e24400c0120308040001d007039030b000385d201040051040805130254030f00000c1c03258229043d200180700320009160013a44440b41086804e200382da80f0840e010642d12210244074803160b11003e4135a102403000e044544210040d1003640c0a0321a440c40c8080400c2d0000c200d0300f0841150707d8005441c6c0e40d41100364054802140e80c40700c1003041c0700d80040140c54020106880354841c4140c1800e030340c103000a000c0f613081201290361014210307a004010646501c3e4515200300d00b9402140c4242d0b4030b503602000903102e2944030b005a01c100203000240c404070108460840c10100800b80000c82c00803013904d0f5144820b0b02c40b5a403603002001070401c143c90b1510b401200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 83285882 1250 83284632 83284639
    0x203091221040807060c02030601060c030302070b1e0907061d04020d0608060412020102190c0c03051b03010e0a030e120c10030902010206090d1d0303070605040f05060709050904060b 80
    0x5000c10000700079100104840c00c000e85190104090211040c107000309000740250345050881c0c0c3c5525000a66500418441e01e801d1011a80118051520a40448460f10b81100d0420814200641d2484031041c0b10380811644015050216541d007501040c504111500c6a540703000c000650025403c4503541c100801e94420b6080211480309007107401800001e00c205c0f03001d00b5003460b160400342144150f5610840469204002110441c8509000580c004200e85000e60001005d441c2050b2131004503000034040703104800c00400078040340300007074031851010ba000380080604811030030b41d00d08481000070089240004c000e401401d0940300355003420101c00465912031b024401054151040010680000303444c1d412090540d40c0400c0b0320307a0003055440003410503a83d20100144440420440403542c0300c600d002d548103995080041c4c0b900385810100c00c2141d41824500404c0c0d4a240c00320840d5580104070000b282d2602402d0000700b00d900c0503042c5415641c0d10b50b290b00042c10882e50320b0b5031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 83287132 1250 83285882 83285893
    0xa02010b03010f0501031b06080a0903020f01050901150f05030705090709030f0c030309140d11030f0313050a0806071b0c0e27010209031203040302070e0a0204030201030f020304020102030912 84
    0x140390354240103207100d03090350960006055042d410408810003151000594145484004000440c0e002c40b00d10f48c42a0001400100c000e030a140403803d2140f074038091052582040c0c01e2126000c070641c451103850b906e5500103100c50741d072054080322452241c880e1075499041050204a141810340d4034030343c032a2591400341d104a0301c1e60f0740c00071183e006505c140c80c2202d0080d0280b0825030040406005000e004050442080984000038509100720a00406030421005602107544003001a84c10340d00601c025039403174919100d98001080698403d26116130b0b00200006041100824102d01030340c0c141c0d450094609411003500146c1309100d90848105811440c0050940c3c0c820f20307080e0041c1402c160360a00c541a40e4000b04441a20803a1460903902c10414042c544c0d0f00001e001c002a4801c180094481d641c5080030b0342080703499803040043d0304404007003107800c03a281da0082042d82e10076201008a5440e100890f400c901040350000d001d41d0003000246035900d08443ca5140062180b4100d48 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 83288382 1250 83287132 83287151
    0x309030219210506060109050d02010e010504080106080102030901180201020d0309050a020603010303081609080a0b090c1203130902040506071506090237051209010603020a0f0311010c12050a0201 86
    0xa066074441e034010341c00b0030701c100c2c500041200c01e003c0c0039001402440c200185c28241f0002a0750441080002818407101d42c2511480b640540291001085008d008201080d5103c80c040c0c040d620444490700c0c0740d4030340900044200c1480800c071039100d4061b070007084043c10a000940007440c0501c025615845082d4a00300140c1d03400000710702940c800d503114049810202202101e10803207034090010302c18447e40500c64804009000c420320341d000301c0c03006c0c010b80b07030700b5903040c2407910306c102140c0c100280011b080d1444030000020038407000b00249610381150b9400008049000340d00400f82d01040403c01840401e020302c020500d00142c99900054040d81c880800d0226405039401180590f5003003481c0d180640341914200c010140201600c00001040380002e00c94032903d0b030f21041c4d00b4008404035905440c25032110000d0750b8040c0c000e041290b1a40b440f001c848400e4441141e5402240f110450300b03511540e082403845a1110000f403440c08440000e07685a000074403000215961105080f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 83289632 1250 83288382 83288399
    0x304030e04090809091602030f090f041103010302150406020601050d050f06010e150a030b040602070314131401031b050c03090915030d0206070210050c1b16050307030309030219 78
    0x25441403040880c40d5483c14075400b404884000141120250185906c001264075004002c94a46641c00f803022507480000c0c40c0001d802d4075003042040c2d0402d1a280c02c80528060110003141a00d000b10b810104803040c000e9030b03c01c3c40c42280110001038226070010000c0741004011000e800780b00f0b0003604e4404a001180d20319000c1e0980c03002c400c0c425014140017610307100e03020164021100341da84044d02c43c10740c0c580c0980e600340a44000c0a803030b400034600b8103041c4070700e4040c408552000c00d01651480d400030b0f074001000043c052281e03a003442c0301d0a0019036001e0f104500c0031300b50f10b0400381e440114200d006d8801d80c1181c0c06a40c1e0500003048200d100399241500540f2607540d45002e5869250710f1420f0502d0008951042020365018600b03024405400007030811940d2468074021541e80d035408040081d41c003030401591805030006400b0209040c01041800b0001764900ca078141d0247c4e40e40070182d88100d6880b015000c160031020038405810310b902080c15a1611000b1074001a60354a400b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 83290882 1250 83289632 83289641
    0x5010507080a060506070b041b0803041203030b041a10090807091a040203060d0b060102030d020a05071b0f030b060307030f0302070f05042007050c061305011b080f0304030e04 77
    0x10100041d03614020000300701580e103d504003401059900c1030030156a03542d4070101c0c020280000d05101091100007005041200c8450091300d5404240ca40303030790380c602c111000341390204012030110741490142c07980e60a00744547c2400e00c4041980720340c010116403d2080007840000e03218100305100a001c80d040c08100030700d071b0041017103800000c4c5459090b480c82403801049240184113500410500c40346a4401c5e203007e101d660444038003010340c0c03030305070040c0d2551082c003086041c0d0b24000300c0c0070780301c032034005000d00b5145004190040b113200580da0035600c20015400f411688550b403000610100780b0395542e080c0d0001024049821842c0c0700d45581c000368524840441c010303400030300c040c03100d8081d80c1250f40050400340c400344001d00520301c00038801140b1400d2a070390396002007000404e0100c2000b16000c0070340050405a543d11800e41002003107409409243d0104031341d00c419002c1c03840c459550310b082036088503546061480302503940200e54000b810641c20418195811080c941c1c0302c0c4038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 83292132 1250 83290882 83290891
    0xb030a02091303020f210c0304030c0b120703050c03130314040305032101030c030201080a0222170309090112030c08271e04110c0601030b01030204290d0c03050105 72
    0x142c0100c1c541c1914000b4909049204464503c0c2c100f140d49405121803540180f844100540c585070300c079014100741e1855409242d002400d820a14080000c45074423410080081e56076040c091003c1c2e9950f454140e0a90f4415101040c0d481010000240c0482c401d80742c0c021050712078a07010790400c1b124050040399800a8005455a400000ea001040090100e0403030320080700c0c20000400350b14540b074599080d40c8608c0040c2c1405105000501e50b4441a411070b1070410145124250094001c0100b00b80c070540d50280d0840104041180e115454001040e1050a00010085446a070911141410b00485070350b08409000540034a000010303038000c05025012415580601034640b00e420750250108200c50581c010b100160310240820500f01c660040d082c0261000705501c05907440101f00c030301c14514413000c18060040040708101c410110103048a000319820302880d03010f80381240011280c032000c258051041354200407181000b612203401a4001c10802030f16aa41707848140c2510030441c1e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 83293382 1250 83292132 83292151
    0x309070b0d0e07051503010b0a090e1e01051909020a1103030c03060102060709060c0308060f0307030305181c03030b030c0612070f030507021203090f070b0417010b0a0303030b030a0209 81
    0x50102c201c907001c0000ea001840e044507120340d114510700b88400b0b04e01c0f040c046c418840500003840d45050b4003c690b400c0041030701100c01e0500d0700e8203c83d403032550010031508004140c0c101d000080c4610300b08811081270240707410000c1c800c61604840e14020b41c8020503c0081c000d41503000780ca4450144055031154911001040e50b030305e0b00d0000203040030300003030174032081c0910307100184520341d48034404d0610b0640c182020801c644440001410300c424540c0c0d1960306101d1100040105a030080150011644038074148401070100000c006440070300400811120350010b0141c00800c0c4241c0000004078405000e071060000c410f4041100da911492080030500f00040a00000c0f981c0000450071903011840c0c208100e0800c40002074640090920804020901002203015503400f4403085203041c0031842103903101540d0313600c6400943c02600c151b1000d2102c05045074242d08060083d060040c1005086c5450141140c0d0198010002541865010b00c6003500d541c2c010303281d060903540140c0a01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 83294632 1250 83293382 83293391
    0x126060117061e040e06130c09050c09040507020115230a0501020d0f2109031b210e0603100e150904020d150c020105090c01030e0606101101020406031b0e010804080309070b0d 77
    0x7420070f4121120280d000002707480c80e00b000c2007d120035000a94460b03410881300440c140c1c4418401b00e01400b03000c01a4412211306460001e0200b079aa0542d102200c03001221760000d0916008000c848404d510905015030000304496183e1849102c2401450456041c031005042c1d20701070105042084560a100466580c14641c083c50303048011a04101c1544003044003c10b4550744074080010031000e04071a041d100d4460441d040d004083d00340005401900d03250310b1340340c05c8082000000c61ba21410441003005008104a8041c44008128001000e07164081680b150340c207008001c045410b0940e400701e182d1a0f01c8030f80781042d014400b03041d10264000700d85410401c107040d0401000c9645103040c5032034100403220380403001c11400d42c0000110b40c0f030071500c5032499003074520781e10350300c008401548001004940d083e050341c0001004241d0500349420b03602c2000c015900d01704d61a00c2140402d60000002d000614260011035102c241502544d4616968040f50080c0b60400b01c20200e20035101c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 83295882 1250 83294632 83294671
    0x90503040f0306061d0403090e09030918010f0501020f070303080711030c0705100c0b01090504021503010906080705060301030503031b0d0207061d1204030308060126060117061e040e06 81
    0x580c040c0c500e0094820700080785e5040542d40904001182d00c0f07040000c078192800990b0044081c8140c0b440360130050700c442e030200d40040200c40300450900a0174510741001c94003240b079510008281c40c94007031101c001c100503400c60720240d0701030000815500c20024480300086413403a0074000b91040311408801000d0590400f020001e580c0c000c08070481c200501c20300c661000c5541c0398102070440f4010100054943c4440c00480c0c1074400c01c0c0c6010b43c82c00f20000000844044540c0100d04031140c4074261034041d034542042200f6440f00f0f100103403c50b03005001080201c00314030303602602c0d00340030500503140c01080807c65050303030444841925040d42d69018481194591592040c14070318940191040d608004d451806a0140d408041c080160f0300000804036402804e020000d40c60f5070701d99081d050b140111001044004076600f5000440500c3c10003a00c08049000c0c0340540b400500403590500c2030601c00c1403a0030012101540162a0700c100904802e0500002d8001d4030096a188980040d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 83297132 1250 83295882 83295899
    0x9060f070c0f0902270a0909020402040e0108060106080a090c03060e0a0c0b0a0801080102040303090608070e06070c06030c020c0f0d060207080f040314060408040303030506060d0e1b18060103090503040f030606 92
    0x41941d01800035924221145c03015515100b680e801e5844241c0c00040c004e12600226009008a401c00c400e1348000100202e48007100090940c1290b0003655004616641c03144107809541002d8402413410b8000030040c400a000da4000a82034000041107072000513040d110400c0300450340d4000072104000041c092a0b284d071216800340501a100000d5240601d180d80c0244060010311900c400c2008a002088525210700b0644000d913000038100c6844041e01e007000d0b0b144d00158883c40e4007007450046000c2d00d241c000710703043d400010300420720003945200005100b80304ca583c440c1207a1059007000200c001038840700182c0380c601508580161a42e0461400704200030845001c5c0e002d43d031091042100080012048034181ca5051902080fa5112040803440740e0050030f0610040500300000b001e00c0b03480004980030b81400340d20208030803c0b4200140035003200c00601038000314680c1700001da03c45d400b036000f15001c1072088080340d00d011341d6803140400c520800e070130032280d00780c032107908000141 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 83298382 1250 83297132 83297167
    0x1101110114060a0806062404080102040303050a0e040e070e0c1b0a0506010f0b16080c030706090209060d0201080105151b0307030206071403070f05090409060605030106060509060f070c0f0902 84
    0xa113980050201b800e00780c00161414420003140300300100400c826050120f18201698028142c0720001c7d074803142c0b01d1501801036003000160300001000c1010172039031894240564204a200c0c58080d01e00e0b9400c004102020a00050285160340350801100ca0342c03214170060210035100c420b002d0f1002c09628a0424100789040c0e000707898141100c0e81c01e00016181ca004c80d81442c50b10121420b00900d14507025020f80a41d40351804240000f0039064107000c42da80107030301514403c455402031350782c94034200003104900c2840030b8006001c420040c002400c003004455003913040e0f03850722030505160200f2484109206803a0201e55000070034400100f580401800790882210304180d0150300d01c66082d0300320b501004140c001040615030389455041c0c06001150442200a802844208030606200d00039000ca841703040c0c002e618010300007803170900c202d003500d0070306100504aa1509800350325514042c3c118103800d030342c0307160780d540d0001b00c00300d01d00703090401443c4980001d6191640741c0a503a0120 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 83299632 1250 83298382 83298389
    0x120f030306120c150c0c0e060a0509090c0102010e01180303180804170c0609010806060310030b0a0b0f04060e010e04240e0105060a03050c0d0507080d05040e16050301031101110114060a 81
    0x5ca50901048002950b440401040d02e215100800c0180d6910000076040402c1c0d0380a80c0e0420106800e000302d03110040350f03d00c041e600a8009200c0c258948403d1400c848004041811b400f812048600c0017a100f60003560f440100f10207880010f012580341c1d00c00303a51042e84140001c2c4410090300300050018170007c1d45030041140c4190600941800281050000801d11840740000100003102c0c0c500b40e120600c095500450640950310302507442c14010b02d24a809684107416540d4845820b1502d0300030b0000303444034940381580503440c11900e009140d001420403160055802107050300701d40700200090070852049004610311125034881800c40e04083c1445002d01070740c0d0802e00119100007000b6545032001e8440001400344c50410a0814149412120380b42c0280c5850303000d495800b9029100385c800c0030b6840c911549510482d03545401001d09054007064052004001007030007800089910310040c181903032400c1341d1144a030b0840b00c18007820181101008e0500642d8100381034440d024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 83300882 1250 83299632 83299637
    0xc0312010b09060304080f070f030e0a0f230117090a06110306010e0910050901030b060103061e030f03050d023103021813080c030a0e0a120f030306120c15 68
    0x30010b004000c50880c1c44010300150042c41c0001d1480d0955540c8070880361300c9034010300c20542c9502c179440c00a0002482004a61140040010100c0c0c0ca48003444603104481100c61805a9007040d420700b1400610021115814403805803050000f41043c410800d01c100341d01005814040301a01d06401180c0c0c41004820304d29406104000d203c5c0d0704106582d0030503000301e070a00d150340d40320822421000901e030070803504030501900002c100803606200c6030081209890070b021203525041d400e034416071240c680e0344940000c0401003010454459080780414028a0907034030b03080c404a6860280d030b00802001c406040482100f01c0c2541c00807031000640358007845003960070b914503000144043c4c0d9030780c030324010190700e80c003ca98039040002d881522a9030040e02d01d920307202800d01e8541c40742c20408804c400b18400c6600c00216161400d074000603580d00d019102c00319109511810309201080004505050b528400850076155188401e810907100f00d5209910030f081542d4819441d100d400107200303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 83302132 1250 83300882 83300887
    0x60f020d0f0f0e0a1214120306010206040f0201141602040b01140a120e011e0c0305070804081c150501090b090108180c130203040605060a03030504060f020109080c0312010b 76
    0x642c1c8881030101e01412031400c10f04003010040081c0300510076901c02004c0040440c14103040215162050380f4007060107055502c104590881d0110500c0122000781c0160454400240060503a0280045490061504220011040418103c2507002e6010000c201807094109011440c1c01d0140d030726030711804e28100c640d88040503a140307980d000b01030440c0188107010880c0c80d21742949a0080513034801c40c0000380816507941c820003124600c0c800300c0d450031509049010840300c1c0203001d02c6000e60000d6a1f00641962b072038880b105c4070f400000302e004442581c18020310380f40c9083e00074040c1750102c5401c41030741c031454400090403940c215405018021014804604141c0c4c1011010b5071241c12005c40e4000c881080340d01d10b0038481c84008190340991020051590104250f01a61142c5d00c00c000801c46500c42c1c030b003002015000da00c8010001241000107100c801d120700442c0c84088800e0001042c40310705640c0b0f51382c3c03d82000720f0340b0b4121703400030031603d0304110240d1149004001c04000c003072 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 83303382 1250 83302132 83302157
    0x60c051c080703020a031503081b03160209060f040510050310060503070b0705211c090b0a020d0e030412031b03020c0d020f040f0b100f0c170403020307060f020d 71
    0x7002050020507070030502d0b5000c5140c20000d8000d070441203c044200144070324660301d900d003140541d00301c41150502c10350b20a0b0a500c9050000007201d20441e501110f0803280200c0d6420000500c00c014402600040503080c110f0207525240201380c000c0304158a02c010382070401040c14908010144030350340403800c110081089840c0030800a05803482e0080499840c0d1403410311a00d00508880c100310608212884090030250000c00780600002180d0760a045040100811003555403840018102241c3c8201203205581c855004002500911001040410382810503506580044e8802c0d2121b102c0049c4000800d50700402028062019202c04401240355032002540c0302421513440d4001c1e003900c031505043d035652010740320074040300a005002498030322910001400001580501078100980000c801c00c2c0502c118000748103560b600c1d129040159200c2203002180600103114401c0200401304c05600c00303001c4003010302055110480203080f8001c1c024a4101482d113100100b06201200d03d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 83304632 1250 83303382 83303387
    0x3051014070216050909030f1309060b09092703041206141009240612271707080a0903030905010203070807030509040f0204090b030606120c010f020c040204060c051c 73
    0x140c00380c91045e100c2c00007035a19090710a01d144188441850306242c040707503620500560000c607000703a03140c03083c1c280812661500c082001d0b010300306989600c140801c0014046601c0030b500d41149016080c0010340180c0550305140c2103a01c00e130400c0c1d5030030341603107180380c140001406030016000cac5260b1111f10502c3d00b82055440ca0700075000e040071564a40240141c0000007101c0251900d14010082c602503a0700c480190580c161035400042c02c3d8108104009024a40c5c1066104100040170300314210b80340e03546000744c50102c8000007261a0703041c080b9a01140c08803014042c10a101d80303850303c1c140e056040c09060841c80c1c1d0b000d03a0443d8410001100000c494130182c42045900d81007003510b0307000d1400000c0103418850860b0303031120310128001941d881d4039004090303035020035420342c2c4140c0c40380313000e1000f14041d00301111000e80c094006c59440d54465000c81c1d84014481c41599421a00440064140d0b0b1040d8481c02c002880c1842020a000c014420701d10080a01e60f1601500320111502 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 83305882 1250 83304632 83304673
    0x1403090c04290d0302070e0117060a140c1e0f030402090f010311040923011a0402071a07020325120c0308040303050c0717030106140c25030510140702 66
    0x1150300500380018043c007094001c010ba00c0c06030003c0000003500c0d60b1245a800d071250211001000e8610458000c90400c502e00d1203200d0706010302404211050352611100001a4081c2110303240100d010092103402c0c040040180520390308014203140c1c0e90070700780101721342e040001d41542c0c4a100070000400000d52501c521440c40b240540700820080714600f4006c0314011210a0b2814850b24944003405c4843c0640c0701121f030840c4180c0c0441c4007019101807004901030000d00400c01072451200a1250f004100c2c5542c0c01f140c50700c101c0b440c10304003000b685848032a6030003652200300c5030700b02d001c2003104031139040700e40c42214a0b20912094003510000e002050281010f0207055482d00480c100014850841e01c41a030048441c0d095030740300c0c4617141002e0b4030900c0b0307a100207050503006155018030082203130030340e038002c034000c00704910f24600d03000240460b40c04818040d1014080000040d03018007824a07c030802a0b00012210150000b07500101d800900c440115040180181c4200300610305 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 83307132 1250 83305882 83305961
    0x1080102360d11090a09020a090605061204050f03280507031b03050c0a0302031801020604050619020d060303080a051008100f020c0303180705040504030914011403090c04 75
    0x111010724156509100a41802c1c00c0f00c0c554000104000b04180145c09801041c11144291215000a546c8902c400111003c500566601a000f0030810170b010103110402600325005006503400c0001e05460246190301c00a9800b00480304040d9201502d180508180b00081150801c42d280440c0303a03074010300485000c48107102c500c0700c82c000102850310441c1501c10121007082121070440745414081e50f247c020243e811640101c09950b4000c40d440418107502542c0e004000300b040d619400300c0004000e0a40c807200141650034094a010490503000e00c800850080d1500805030918aa003070f01174070802007540c0050780a0714410444010005403000710000100c0000428a4040b03403040d000e0300c9684080e54091101000748001d002083c01846a0702e0740c41c20440301040d43c2c03107052000791241100d01401084814400700300c2c2c44140c04150861000514110001c8149040e002c542e0f50001c1e15140c11fa41d0080312500b00c50305003803245880100e00c59000d1402e408501e1000c4905a00d9105c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 83308382 1250 83307132 83307139
    0xc0f0503010918021003020c070b070206093304030b07020105091015091506080a0c0203070b04031107060801080c0d050a1112010203130b0c0a021b0a0e0108010236 72
    0x5914031000102c0580020f65942c01000c0d042080303140840140030b5005401c480c19640507900000550050301400c031005558050980d83c03c01c1c142c04100702c45040c1e2440940402c0c001d0300184860004444101c21501040d08a8961502d056041c6041e030700800400900540e031400051029420000480c40340c64038410070b02090600361804182c40110490740248002420110728000b00c04045c0074031020388101da9206e039115940c1d0766407003080d911034441e14070141c0c200b0000900440c2ca01d11032194854003d0400314101d1500c100110701e49040343d444580045e0120006022204091103c110501000c83e0310048803501515040e46450700b0403001040c2e1100420030040b16110b000c0d41300d07404502741008644170315010506199400c0c55420484810004074005003d029a0340113580d04a402e0394000d05403030829294002c4a14040d08203035500040150000403d44030800e10b0601034402100090f881e001e0145d40183d10741561100ca07610024080b2b0003450042000303041c09000941107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 83309632 1250 83308382 83308391
    0x1092906130b0a030f021503070503060d0204060519090c05070c1403010e0a030c05060c040308030a0b0f10020f0d03110319020d020703020a0209160c02040905190c090c0f05030109 79
    0x40a01c000240070840c0e0071030700140080400418043d0840c049600d0600917200e189503106d141801450910081381d20101141d81031010484d00e042000300c00110501c0a84000f03049901e8400044010f03040f40312103d0740c03028813a0b00384034a094a00440844010307a0900320b051a4071540c80400f204500c2c010b030200711501d00840a00744c0d0b030940107500404140d000fa108600050308004289049a680594241c42401c0100d0020403400040340d089a40008005d030440d10341d80d10140151916440b00e13507110740c44440c101c4031540e445031210b0705814141c00170a2b0440900f180d841c105400d1030000070906181048000300c00e455041101c0d413044c5c0c075851141c100607104a06000134090f2901c489009072022031076074201500051030306107042c001c4400403800e80c2c07405a150714255541b6503080c006100c0f003c504005003450b4000c410000c2c4a5021384001040d802d001c00003c0c031070403500380e5103981485005c00940c1ea1911a81c600c0d60351a00d0070059490131048054124441885140300c46580c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 83310882 1250 83309632 83309659
    0x2010c050708090a0e07091a0319020306010c0605160e040b0105030f04030207080d0806030f010e0c01030207020f1806090a06050901030308091606090f051c0204021e070501092906 79
    0x50034000700152815075040402400e11b500e0041000041e4082c00e0b0800c21420080441460020301780c80c07140c0c20001a0165050311045441e001c0d40001e44018140404100c0b02000134109020345403194218000710002184926001040e840800800f180101e1420300c0e03c50301c0d40d0340803007144da0041c06030300714040a840b14901240303480070355070100c0070bd8014441002c0c40a030344144454010700701103084944e41c41c4003d51a500700c44c0200d10b18845644036401070007055009801074500d050004128444522005001c581c145460050400c0c803584000100b0500e072400041e0650410507081003000724031f013400c011a8112606000280920202d0000691111020842d804060703040d41060703000c941d41c3c0c6070007410307000150007121480e02c002c01c0d0204180c00d0125000c20021940280e0003103100d071680a2000a502ca06001034030009807810007802c4044030002880302a1041c0700010b141d507245d0910703901060b4442d8074454540030060100248000c5140516041041220300b02d010100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 83312132 1250 83310882 83310889
    0x60909041202120c010204090e0c030607031125050d09030f020d020d06020a030605280b0c0a020d050d12060513050a0204050a08060a1b050706020a0c0614090c0102010c05070809 78
    0x11444081e040c50303e0004220001c460190003600488841010a0010f80b400084903511140d00301c1c42c803038041c0c0c0408006013500d4800c0d00203c4032000c10601c070520307144503e4000b8022000e10305105051004540d00202000010002c0c0c00101080c0d1514044e014113541da40042c00a80c01e001a120f0140f1151040c255940c1c20317403101206034458011991444403075005805402503100d01c500c14a140e44d84a828002040111031043d11451450b200c01d608010002e04182c01900761810942719003801000161034912204083d940035200900c00c0d4005036100820080d0310b850601212400e1078010040340d20381800d079400e06002c40d8004945540d80c408060000c0c015640314550019485c0c40000b00100d01040540c00380c03141c254140004652864050400310007040b0b01000124100701c03110100c6c0842d0702403c0613082a14108107107003001e848440544d0850041803051421340b4062007105082080440f0800200b80001d0245541a12000c0c2280c040d914010304200300c00a90780b180c0d90b8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 83313382 1250 83312132 83312143
    0x10051b2407090f080604020a05030d02072106140f06010309030e01081b03010f0e1501090302090910060902180103060609050d1e06021b01050108061305032a0c060909041202 76
    0x1040c0c0980280383d0f03611540d00740c3e241400e66040e400b400d10a0710102e240d040100e03841d040364817644c004041543c540900d440d0030300c14810140762601d00c0b1265040c00101580140240d1990001d540e180a080c040982c041c8850098089814185003000c2c0f00c0000303030800408043e050090900003182d0352280c2030100003a10350310141c54090000400411042010b071b8005044d6004680041c80c036944095413503248244a41e6400c5c082604410104014544062141d07800103510056460b2020b47c2400c18065070700700d403c44402180c002c17a4051010b40c2d03030342d41300800010904e4148a82c40c86d00402800020140c01403c0c01000b84d54980d1040c02603202002440c2e80ca070000440707a005550a0180094009240f40360090310140d0441462801c140901410303941118094203250710341c50181071601c50305010440b1240820720046160078160003c8030010507103c0102e20203c020340503210305010801280702d1107020280f10b07100454542c120030643c816400310300b09039824081c00f020703403904 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 83314632 1250 83313382 83313389
    0x7080f1b070c030c150801030503191b0b060f030d080105040b19121e080a030c1e080612010c05040902090604050a0906080d05030c18040b10051b240709 67
    0x1002c60400200b000204d2040c802207502c80142a140000c2060017103070240c000384006003482d4070a02c942442011441c0c2a00301001003402c00085900c05101c01c982094041c59007030701d144c000102040b907203007406600308039600812000340256010a65019100000c10b000300390149a640c0628410340d02c0c1d100b1056100810041c4040607a55102d02c1026074642018084500e04440e02d084400d8680b99104841c2e1103501c007003054203103161600700310000c00000310010200a9145141d04001c1c58804060f40b444071103955002c05031170b1840c14404c080340784000d0500c01c1c0e8540010b6140b040c1d4440c06940c26114812000340c0d6032014407000500311700458100c0c0da8030030b50040e8001400b1989a0000e012a8840d2003540e0509441410581b040c0c041151418543e480400ca0000c0300700c81a6041c52500500038000030340c1c00844804500c0300c00c003d80005d00400c2c000140b049480e48080a501d82c0c40c042403004004140c0850190b6000034455100c09000c1480080440c00c0540a94200e4003d07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 83315882 1250 83314632 83314643
    0x31505060c03030910060608070509010e06040306091202061513020d181707030807110a05010516030b0a0302060f030711010c0c03030c030b0109150905120c030607080f1b07 76
    0x169507072009102d8595000340c90510b1288122021000d0b03d000d039009400482c3c1041e210044555207513a803d4405034040350403581041000c403422820395544001034005140903510019816502d4a0807041200392845000c0565001c5c2081042500c3d46141070b8061001c2555113808442d12a03581070064000c0d8114002c04900701004540c0c1c602100e280c0080840c000d103140c0c10b2900140016204c2ea1117403410203000511040c1c0003e140318019140940244d641008a6a443c0c000c0d4030340900b110b40984c2c02152111070394804082140e03150007484007025040b0b40c03030300001e4615400a1038500c103441002071880b134040300150015011b00840c0321608004402445000540c00e401031006521000480120b40303040d450a408510070306c50440c01000603101c3c3c001c1c26042034840c0707241c22018441d150802c803a4000104158940402d05224803401c1c0006201c840702d41020541020b200800c000c0c2003211500c1001084d1104104080c1c01241032120300500544040c1c10000501ca510005801e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 83317132 1250 83315882 83315887
    0x909010303020c011829120c0a200c0d020d050604050319030509070303030e030c0102040b120c0c0c010507030912050d0219020f091509010801020a0f0f0f03150506 72
    0x9140e0049003d841d0322038240d0f2040c3c2c6041008a580030f20600b58055400c4c0703024131540c08140c042008442e020325034100003d503421b02c82c02d0010f00300044012610031000303000c0841c40305a0f080d04800f812041c91850749401d0202c1600e19071581d41d8090342030342103204640c1c65280d04155120900245417090304501510719514040c140700c2d60b00e90140070f8182c000d0226440e2420107078030034402c50780a07100da280038010a40c51a1000c80c044c14280e0314050150204024a001851017480180024104c0c0e075160b584480381c0c0c0921040c070202c0204243e551410030882003649207000700d40038014400c00d00f48640c0b154180d017801c41e0f00445503008000c10614210156041c4000054400d15400d401e1f407c50345c0c502e080001000c41c86c06040f20082d04119040800b0b5042e01d06041c9042c0c0c01621100b00c515001c68010020714110420fa10104050758009600b441c0242c0c405007203100003003981040b03170362461251300041100700803c00314400c1581d99107002c009464002205001000700412894 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 83318382 1250 83317132 83317139
    0x15070e0a0305060f0f06181902120108010b030f07030b090313060c050705120c060c0111070f0303060e0606121b0a030c023a0203040f0e070305060a0302100c020303090901 75
    0x543d14901602ca1364801e0300d1440000304046910700241d03200d4107026140c0904030900e500d90001c2d1500280000300d00b50031711050001160703030500c058000c0d40c41e90902010103504d880310503400c454402000c0c9001c0e4200301103101c1c3c0488009110011240d204484043d2542e48004042c21030190613002e1104c00e00c20180021403982c001d90882103280107500303075810240c2d075204101c814005245011030b01e4110780c1c640103040c034081c00909220402c5030004106010790a0004021303500c14001215403503060340c0c24005050b0b140c407910300540510605210103082450026840d4017074400b4000341d0111030030018800c29140388024034501a5000000d4542c65a0713100940988a81420707800103106200c865001c0c20300b401540d141003031814200003100001c00c91014841c000314001c00c001c0d840100000103140c0407841041005103000c0e68a140c1c02d05001c84020160380010b001a440740381c10241c1817025070b0380e03000300c85900b051504044009000b10310109081d4099510000c1d40b00f9140340002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 83319632 1250 83318382 83318393
    0x21909140402010e100504090903110f0106080604020d03020c190911120a09050f06070504060e09070e01080a2a030c0c0b01050108060d0605041209050303090315070e0a03 75
    0x9840400009015450044003211400041228083c1c00506a43c540502e20f0420006100c16401107140403881c064884d00c0d2041078a9040c0c0044000540d815040ca204c02c0d014400d1801010b05a40284181407524000641e03482001d40040d114801d0b607400da0080500030489404000c030003910a51b008001030b0090194070f4a0352003141282800d080e13a00b864040d40c10116070381080101d0200009031100c601000081c040a0401c4405100301c1204a19030042088040d10640040e500c0d60340e00c81c201072000381910ba107800745c00c0c01011510280480e20f030308612202003c80080c03170b1150803135450100180190100030040c80c4411040790388850500044200255100340300d0f101401407040181d422244525440e0024007030303c0400d001408207621803c0040d8002c034000380120132000550f16102c0c00c5a905030b400b1140342000d152129080750704804040010001100035504248003c4046502c1e0341112681c1e4100808450005001d2805401d021f0101100a44843c000941340c0c07804 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 83320882 1250 83319632 83319679
    0x11401050c011a0f10051b011401090906060501091d09030f04030c050a0501090303050f03090c090a0212100803040b09120d0f0305010f050d030c02010e040c0e0108010b03010e0c031302 81
    0x49401110100d660748500c1c241407000c152007040b80d50b1b0b01c0303152172002d103481401035640d5404038149548450a0443c1c4991001c001d5020b40501a400070300304540d0326151046454990115040c03010111007044001030050043c030f411300150b00761110755910161418250312610340000e1411074086804018031001d140705200f6603000395000d06c5c030f2584036001510800d01c0d51000500041080003805500031f03404d00a1074100151804070703103000d881c10001826000040342c10070740c0c242c0d0102d9040460700141485540042d003580402d50518185001c1070707200d10a50041429901e4005550852510b50881042c820f80c8040140c40c03400c803801c0001002c40001102e040700080c01c0c0000031034810320840c00c0c81c0807070b4401803004a518071140d44c140d481c81d00081e000d0b41400303540115000551039501604030100c2d142c1d0f40d4590792040390f00c0050503c03030301a046844030180c140014071440301010031707458102c50300d1803c071502c0b95280380d5941014882010000c5d0001c00789040301d95441d80b00c184 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 83322132 1250 83320882 83320931
    0xb09010f0501030e030c060403050f070b01232407020a0f0b03010e09011e090201030212010b04050102010e030306030601030201110313030c09050a0209010e090c160f14060708011401050c01 83
    0x3c0900c1070180802c0340301c2d034074002c3d05c084024580202000c0390010b800345004000b00d41400384103504010990f12075240000c02607000b40200d450f081502c0000081781e8042d0800300b6001c40c0c0510180c1000f81c000003d02448010f064400680044e1400c00d558900c081400200200c00700c2082c6541c8a0701c41c01c0d0b01d41c00a10481d46150b14110100380341082c18099808600c00210200600401400e0345c45c020b00200c0c3c10583c103169080003001d280c4500d504142c3c2c040d00d500005a0b545030300c1d0100081c21583d428240070a2504240107000740b03aa000f1031100d0440b5024684160816003c1098500314400c0b40c0e59134441e07000003034000040211a04a54040702c02c82c2e01e04100582d5041c00742e4060b4031420011074006422820f191480d80f81c089030306508401b40f215880d04040001440b01598021000140c80340180007101900300f12040700380b1642c288100380a02047d00705414085c0034614180500c1c0ba401000e0149100c2592052080e18183c2035008028030611311401003400d80b0f00c60040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 83323382 1250 83322132 83322137
    0x170c070314010e011503030503061905060a0f020d02071a07050c03060708071403010605030a0f1107110a21080a031524082a0f070308010906080a0c0b0309010b09010f0501 75
    0x13030718038010017868851080781d41589503d46150385910070000760f10000c0c07001d41c10601d408040030806032640409000d1202881e101c86080544aa80103032411131050700140441d40080018402d0543ca402d540c02c100f1200b105003515103100e4074006080c44003903494950944182410001c201c0c1e030103103c240c043c2043d51200411841008828561840709004100c0403400400201c0d07580c0d09a584502421801d454000613103c03403207800301a2a0340141030641e1030900b20b40200110340703400c00b0188020600050101d1100e0340740b00a034043c040700300b140030300090004900176644a01a80107500034062a41e040107003a900c40c0d5200510560700c00c01700b103c03070640d040b0000840340204460b40c09080496036900700c00c408a1036001101c1c40c9030680400800c1c00340861103108041101800041d0b2094481280c90b42c1011404c80403217141d0343c480a02c1d0703400b0315007110104081c9402ca0040d01c05428595549580b920340341c9000d4108001456080342d0341e000002601c0f02c4000c0e450341520401d9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 83324632 1250 83323382 83323391
    0x307032006041208040f020909011a030706020d05180d080a020d0c0b011401141201050306101a0304020d0f05010b1003020310170a05011109100309170c070314010e01 73
    0x10050350395900c10032140185524010300740c0b82c0b9040e005102c007940c014418007080541e5042d0750301082d0f5540c002d8540c07c01985d12102c040e00da410080c22480b04810007030b03000300000742c0780060080d0741e103109803810b805008001810030716014440c44402c1400c100030b0091110f80300300b45070200d8681d1041c0c0843d0018002d80000307941552103001454010b54014490708d20781d03400d108110115803a000c0001d07042c4000c504415400280c0b44d8041c0000d07440c210507506d00c2d5031400b01410b0800c180180b110014001d800b0b000d0100c1400c1107900f108203400b0303941c80390f04c1e41d48903c00328055468004000e440030340310124800800c041500034402c0480203036901006800301c01c1041c0e05a0009035800600c00503107050600c030382441480d000881401c001e040741c1c0c1001142d2601d508694803c0d495150b441800070b061405401c3c0007885070f00b40c54152400704030404040d11000d816040d0040035814403031001420202d2040c04014501c043c540016a2100030140341c1c40d564000d10007084100080d50a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 83325882 1250 83324632 83324687
    0x3020d080603011802040c020106050409061d0f030d02030a06121103010c11100902030102071b0f0b190f050c0106061205060a03030807030e010f09080307021519090c08030703 77
    0x40c0a15105103158090111361800154204006424a18200b004541d030b1158002001d9542e801901c0e0501c1c0180300024115010411002425a00c0b01c910001980300b2107040062001c00400c48803005819040107841e40c8035042010040c00e203580c0109560071943c4840f10603c103249460080b0040114004c000d440c4d03888405844002c18070203100d00a8204018042c0c50f040d00d5045030810750320050005141c400d1940d22504803060f445001900c122415070107001403036158007000080c00610030014201908002c4010211480401c141c00304000941007001c0140a003083d5444542007030000c0c81000e4446100821040408095401c0c40703041c140494400d0821070801c43c02d8a815540b003151950f60740c0001d4014003100f000c030303418541da035942607800c001480c82062038032841014055942e0070120b500a1510740b6291410641c40342000c244100f08038a269407040b0410340d40360100354031b5120b00b0001c420100a5000d0b54250000060703041c20541d212640c0340c050103100c000501101e51 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 83327132 1250 83325882 83325889
    0x30901023402010e030a0804030503030a1415041503050d050a0207090c0206271212060901050915030708030408160b120109090206091503070e03060c030103030810080a03020d0806 79
    0x200402000c0056581c011500954450800465081006402c9031500e035002e94a14240754441d81c01030b140d642010041c41000e0302c0a019042018910000814072400e0500094014607000100d0724419959100540040704c1c4c68520f02c1e00554000062314218525218041c085a1100015100600968001040e011010300c58203214240380e80c02401c03140d0703444a01504a40703010800d00044000c02c50405420001000607100145081205903100c40400c0b11803914880003400440c407803144600140a941c40b5000307002e030f01c03922215000160461180120b41030031545d400c40b80442c00006804200320500141c602030311074500d00c150102503035075804070300ea40c001e2008040000d9201720040000080031340141c1c0744540020941d0b4680401c803000921050600e002d0103248140200c00c11810b5904107840311407082c8294090403d034030342585034980c6880140801014818007502286500890700d1100c1d02502985040781d4410361107003006551003001100402c0001d802600096190a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 83328382 1250 83327132 83327197
    0x3020a0905240a021e01060513140c160507080c010e01020d14070804050d03030c0e1008010b0a0201020c070605030103021306140f06091e150304020105030a0e010b0603090102 77
    0xb80307011624161400d0b03100b40e0788652012880504500c51506400e44152070385a070b0000610f403580000640354a08018403510030607071151102c0580c82c04588650340ca08480e20550f00c8512800e0003035403101100c42048100c1d03a0040090000e11819401050708e802c00509002380503001d813a14010307045144012651042c80f9030000700050480a18a800a1510703400ba00b006840b0701740b401e00302a08c40b03007c9031002c1c480d60070540020340c40b284411021504080414070030941942d5695600c80115800b805001041c450030100480011304c100007503200307506407101282140700741c034801c9596040013400c40c2c1081c001a4443e0105d1080c0d041c1000d058070404e01194403210010342206950002c00404422301c1c07040b6900500b0421035100284e58134080480c2c4d22002201082c8081c5894060109049103914040d40c1c0880410038400580c1e040b20a4070b03030154995170042282e030072451407140034110801c496600b0a202106020b108101900605280c4250124050103845824404440360 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 83329632 1250 83328382 83328409
    0xf02030d06081522030309030c0204020703031e02160f0602090411190201021e0307020a0525080102030705030c0c010e010903030b030c031204090f060f090605030f0610050904060b090703020a0905 86
    0x54441304080009009401c0803030014000d00b8103d841e5100c41d0045016a840b56100302c00090f941d08080c17403000c3c2c3d40032100c40c00300b035581004c504100b91000e030803510440c8500050090740142c0c1c0d1407800c0001640450382044006441804040712040d0410744a0b081407900341031000540c009500490703c144240c540c140c000d85040090b00c0c0800201c09c11641c0084c00b013504500841c2c00e21000700d4820854040300f02980030034244808202a0841c40e03100c0b03190046c07019a401081030061065004095030f40000c40356882507514510410340c01d00400c24151141203950130058010189a05980005241e4406400740c54044550508150300c52451400c040482c0d0700034041802611250b40c440741030354217641000241c0c2501c82000140d140010303070110a4890300c0703176014801d07400c0c180031900c5500d040d0f10081103142401300c880620200503028050085030500e002505016164100c62181c5074054004412400c12f540000c1c0071794802d801010104414290004050801079902d081d00d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 83330882 1250 83329632 83329681
    0x30c0608060a05010c0201120507020c03160305030a0e0111010c0e0103050105030d02063903010f06020d0f03090804030602130e01050d030804350d0f0603020d030f02030d060815 78
    0x4043c200801500d0050080340268100910100414094982c034811a809644941c00408407028500200362078001346403802d0024105120040000410000c20f07201c0304600741c207013407000b0103a0600480314400c000d100c40310590300f084410f44080360450b404c00b00c0c0500a03607041c081689c840d8207256a840001d038031240180d00c44000a00e4010894550340050b036030940086000312020b10340740c0d81e10100d6281d00150b80800000400c002610b8a1624000380a680081c004006c035002000d40304042d0341c83c540042c140c0300c1c49d00d903040020710703011034018542c40003046450345481c060f203036400c2c00340d40519030b0104c40d540004200c3c1e20b008241c3c1d40e50716070f16964010859585540345040350080d2810700410344407a0281031100c1b44030423698039142650015854407000e404d83e2513001c2e14100110350801501d40700c0300340701603186e0600c0002c0b01601801d040000e81d5400310100d08c1c41c0b15012068003024544040410581ca02180448401000b50100c62a40d150501000d00c1c07861640b501241 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 83332132 1250 83330882 83330899
    0x3010e1f0503060f0601030209060a020304080f0601051503090703150507020106051c08070807140303040506060a0f05062107090305010b03010212010e13061b0f08040503030a0e01020403120504030c060806 90
    0x24801c050301300c6550701c000306250241c1001e00940206010741c024603903140144c1c00203d0300344101c5d03e0410540c050711981c50000c002552420b004141720711540c030440e180c083c50010000e050040708001040c025684000d068500c1074070403141100818080d41c4180055090080016507443c00c0c1903941c640e02440c0764072140e000c41030398400ca025840000b040303038082424001040440d440103030880f80c04100f40007131641d81c6007507d407203410035200500b00381c0703d0101818103205010351003103a0015a0015112607075245003900700c400480509119a03000d1401040820941c15480054101143c0c031440c02880301c0103141080500781d0040b001034031416150a00100040001809041c0e009000400c083e40c00c0380580d141c3e2003c3d01e00070070846100e000f0041410304030b01e600002ea41c2c0030101c903191110007810a40e0b2407a841c1d1001502c064649900d03080d100444e000c00794121401598032064080c0313059881c00020b4459005880140c441c100603040c0000d4031401002c1c140c1c801c9800520202 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 83333382 1250 83332132 83332141
    0x30f11030f090102010906020c011d0106060206160c060c0216060512060f010909020a09050a06030e10050603070503030403060e15040804032919050919061a0603010e1f050306 77
    0x980c00d4000016860441d9258006e00300412030501c0108504007141c400810f85a054121850b4aa079204503050290703032400e0400c00401e5030110b4a150056128102d180c003038142e19200f00c54003411244003402c06864030003040517031a00010b0391820241c0c05100808059540c90702580c48d8007809000248079140d20001450700e02d030401541010f07410504040c40c5040c0c0324482c080490700280c5481c004141243c0d42400589411000749001b13162915092040e02110085e068843c14182840d8034020b8840b0301040440c0e800f401030101615000c3d013240d0b252580d07810410040d01e0f4003040305409020720011041170058084440303108a800840091400d49543d440604003501c034001f04d0303d008a80e082429802070324000d00d5018940c0394195072520707502010900100d40000c2c100440310b6008600300f500320b0b507102e42e42d10081030308500000396080e945155407480b40c14408016511042c0040040381c0343e01c4a64507940a0f2500800000039894030407402070240340e4038010305606a11440000b03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 83334632 1250 83333382 83333407
    0x306050a0314010608030307020f1507020c0904020301110703021608071505030912030c09030705060a12020f090904050a03020118020604090c0905060c1005061c03140c0613030f1103 80
    0x320071500b040340001032860360754000c203082d50000c1d074904005802516034109600400c003c3d4072141965906411102d05001d240a03640c0c0d1a44400a0b0042110800060a542d020352015035004079076200c1d81c3e500c0d521860029110191040244101c0c3c640d4400400d05040c0040d6035800d80e1040f034805813031244031020544064100406d0034141380b10f01d109510307a400300440a980200c41c40c41402e03480710100010142403d200d03400880c000d07001031242080840c4c0c0554404180290240300598407206c8030340c1a401403241c1003c850304160187c0600c0204880000d50786000747c001d074020400c4200d02c21145064401041000c5e621007010301c000d000040b82541300503491a41800c0c41c010003569040840c00a8100003111403540c1c02100c260b50303142000d401010b038848400c440184409010300c000d56441d00740341d4800741c00c001604085550440c640340c12500ea00500c207080303034401c1ca8642450802040100000c80c0003424000b481c1010320300a003444c0000e250200d01a42c2442240c0048 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 83335882 1250 83334632 83334653
    0x60f080a022806081e0906070c0201030b03060c070519030e0f120d0f02010b04092a1a0a110a0c0e060315090c011e080105060d0f0e1c0306050a03 64
    0x294941010381c00b01e6075001c1ca494603468000c01064807588079920700504c000031280c10204500500c1d0f1110001c000b04c114001c40c14907400555820a10f034025164001200140464000d8a81502c034201c02d0040d1180150098509039105030300325002c1e01e900301c14031458443c43c0440140070035101c01007014245003240c003001c1c9680001d459003000208294415160180180042000c40c0c0a100001d009a5080c010490401d0003074406201d81c1040b41e5030415030b0800e22800300c03c02540d038012103055080710450f00c1c00500b0800c2c000d0414051a801540f441c1c0d1010101202041d0506d04443c01c1c0c41011945d8201c243d00400d0308004a882c00c1c0c0c1d4040c11641c02000d041c0c0c14042d5040c0c0816440d03040100a00504a020007032600d00c69100c005000440d480b000c049180d5040e5030b4007509260f11180c4941920130907a86981c907144440e503240003400407400e15415907810304204c0349101c5c000246008000c08100c80d01c1084001c4c50b001030381240d525014643e00050704990910100d001c1190 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 83337132 1250 83335882 83335909
    0xb060d080705011b180513150812040807050904030c060b12010f02040e0619090e01200702011403010b0703050c03070203070303090303020607080c030609040203011407050904060f080a02 82
    0x18500704070766540b1421141562081220b404050036503081082e0b104540040003c2480c40d409102030802000807040340c00d10004450711f82c0c0380e000e9007418242c1408080000c00d10789003251903134018540166150b400a006d40040c80c403680c40001400e14100c94128021501500c40b41008420368071804042c040c0c00c41172580003c0500b610954550007441030005200845500603120782c1050342a00805d030001d80072600c1003010741502c82d009c03e10f4181500c2180c0300f850380001c0b482c07039611036103015141c2c1d011074881038a444612040c0c4040690000c3c0000351003648c0724419801c003102d9110342800b00307004124400605101110019004030010940460018200e900b40012030703000070301d0a000e80c0c00c01c90025411a80800c00c054040155540000340c90408003402d1800300051075107070200a010600c9500d5500c00728056440a5001c0001d810324805025040c0c60060005031643d481807a000d8043e0b49003000000c0e03035440e20034121040d100c126001e821924059020400c00300c55844 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 83338382 1250 83337132 83337143
    0xb0c160f09020a140a050c0f0d021509071805040506070804080f0703090b040915080307052a0d0b060a080a0803130c15020a030f0203030f07230f190203070b060d 71
    0x1120f5074900c00d00f800291401781e810b5940c455881c07a50303c02c2c01d410b242030340c00c0010080c1e104001403100c0c1900031440700c9404078140b4201308140d0300c50000b1840c3c61f101da8881000071407080107495030304206802023031045008500b04c41e900e03110500d08841b01c0500300d81c00360403100c003440200e2140e1071540040018074000d00d000071101e07072189411350b2554800e501040e03040c1d90320090102010000c40e40a0b00400195000d10308110083d01c03829100c0006c4403881f4107049002807030702090302d02200744542c070b0702010f400807500b40e4151401041404064406510541d00c4050000742c886000495421060b44140c2c91030864a1f013038003c103960301e903a000c1112070b8841c001c00402d50100307114051100340c1c115401000c03142c495060203400c10000240080c210740013041049100c01c4004021a084522803403d00140851454441a0250002da4200050304005083c0d800d0505e1034005c0c02c96003034807009004241e110b00a05913543c1c815948020306160710030002070000d01d41040c02c0f003580360145 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 83339632 1250 83338382 83338397
    0x70207050405100504051b04181d0109060e03040518060402071e03140415080403030f020a020606030706030e0d0f0c142a0105041703040f0b0c160f09020a 68
    0x60300041c0982e4002c40f00c1d18282e41e560b482c1006289828000c0c03d40164024001004403104000c0c801e855124078001c1c26400c1500740d2110998412a501c55800410480c8011041d00403828900f400391004c0801510501d041000800c0c0c400d00c040211402c40b40c000300f91402041000310884c010b800014103280e40160300f07002c148041501e0307003c02051560040c0c0c24803150035446c83d01502c2038003290b0150755501b2084c0001e00c01540081a000300004550421034819900d40c5400c1b00680707081c0307007e020302d580085100000190005001409944c040307040e1052640c466038114211243c14042c084180c1c080310550403006c1c0191400180d154451501914000a5440703e0380503907107003843d141099000404070400404496100300f203643c4204030700c12013041707854002402c5001c4c41c09000c0f04600303140201c0da0b6508081048034018044c4034800c24029560300b28406042d00508002111405000c4406d2980e9000c48003410135580303c404080985030030030034102d00940201b0303003202c10701c07440c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 83340882 1250 83339632 83339639
    0xa02030303010f0303080c0405010c030503100306150504050603190f2915040b0a090f0204080a0b010303020f0f07140111120901030f0e031b030403140d03050708070206010b03070207 80
    0x500c02103001c0c1218886142c1d8551071880c00811821004009003100c250902c01031145a03440514001025094034045489445406811322000712035070008101340c3c0341258102460b034075100c000049400885041045650b080107151711103420301d221913881c10503402d0f4039001404640800ba0004d0040b03c4415002003803131036400901140c03c0e24280110100c0d401c2000b82804483d1108402c0f0040d20140110720901000c140c00b24214055204904c2e103c24810324004590b0b41503030014407024040f1408211107007000381e01e0680c2800300350010301540b4001e000c03248000584445090b80107004080030352500182c080c624803044542810400641280042000100002e58290b02c0a070849541c880403440054102c41c0c241c4807120307006080c42d4606520701c40100c180ca0942c0504064070040c0d1740c0a132841c074150b10568000800f641c0311109203410841000031300b500603c400d5103003004151142c00e000d40c0e40321802c4640c0c1d401640f2081c01071114011075800303550400721600484004985 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 83342132 1250 83340882 83340889
    0x20105100e04170703030b101e030c050705011406090f01030b0406020a0338011d0d0c0b04060509011202070506060d020a05041a03060a020a08011505040906092018120a02 75
    0x131141d4103a00207521101528050f2605040040d000c0103542000c9a029a10400300c00070a40468101000d16550f06500c5610901032002c98040300d40c0321008008051908950906556042d1230700c900030100e10000034114000f101d1210b0590380c000e01c000c0450ba60383d50340d02010791300c01c49141007016241c00c1084420215008450203581c0389130301701054000000c0d01c2c8116000e5002c4680d041168101d94503c254a101264000703000007958017290030103035818440401c010590204030130754800500004c0180d4400060612140c00b44d03207141c15146a80310840a9021f96031000c0e0458104002140840c5000d0320b24000080c4003074802c41045a41d0303400501142c8011542098060584c0c0c8285098136081c82500d5203c0c032844004c6080a44100004210040502466580b22070490703a80082c240114291030003000e1145c0c05000043e200c8001c800a0710b000341040407041c280d00d41043d000340140d810307600d0440c605030340d0340d210103003a01c03c00032410300750030303004407107008052480c80980c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 83343382 1250 83342132 83342137
    0x51902011415010e030102090f0f0f03062502070b12040c05030706020714120604030c060f02180f090106081308160b0915040b01090e031b0106080c01020105100e0417 73
    0x50440d412107602d80c0310341e4000741000f180c42030024400c3c2d1041052481a035104240c01c0041041501e825030106083c0000c2140f1440c0061744551511070102080000d0513039076691400c8e41e80f850310014001008007005c3c1e03a268418000d15946410a00c0303a4900c01e5500c1240c0303940710340110308900100307560300c0104e414804903421000050304100f50a0180760403111b00d0030880306050b1400518240401161038950f80040c000404102c42c00c8054030601c0741603000b1b894142c8040c5011591450504071200c40742c460302076404d0141407090540c400c40d142580c41d0904890840c0c4880c6450b43d120030b0048451079032044102c0c0e0000e4240502d2622070600c13214a10002d11864440d051410170a00103850804032500204100d000318082100140e6003a91843c110780c0407020204154100809490940c011b0303000e184d8445d050a400441c9224054114100322004d4000b40d031014030a081c012426100120b07011030805450103c2040992104401103600030300400186040007401ea0990b0b40e00e5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 83344632 1250 83343382 83343391
    0x109051504060305030a020d090305030306040c1101060806070801290d0603080409200304050706120b030f0607030c0905210106030822120f030e1f1707050a0519020114 74
    0x19800428280c40d00c640420191003101c0c0c8030305161012038a16581c0c2e079070b00e0dc002000700f4000c9441d0001c0c001024001e200e1001c2c000010b0000340401502c400d41c107503a4001c1142c40800085504000003851420814158904d800440342d0302596423070003034407100c05c0c0d101081145046540d4580040481d42e80405000036280c0650045004600e17082c2040e01c803658803480180d075040800c10300000540004964003101c03100d052801601d580000508011703d4210900c2d60103000c0c03080d4807010107102080c20b500c644100d4400b0041c81d401a60102e551402e40d000d1250025608042e0301d21011200b41c084e208100644004507240b516030345d40f8180d075040307070154440b40726800b12480309a125004d244070143c050700a2910600b5025103401c0300340141c0503c0a01441440700c8102d000da15080014001c08541040f184405840100001d006401794078001440210030000300f16568407070341c02c5030401c84081d03a880341001d81c0c0c0386004030f0340c8080e010154150365803000e600004200007036aa5104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 83345882 1250 83344632 83344643
    0xa21090303050108060c4608042001020c130603060e1c0c0804051e0303040b121b090907050903070303050d05151c030c0602031312051201090515040603 67
    0x1549040c280300e00e081c0b80070701102c2c00c81c0c105000484900740f02c0c90185100800c0a088958808401080c5400301c03075007100381811f1000d000040403c030f99001100240034a10079800040c0000741c0128881030202c204011034016085514190740d20314007141801e0761800941400161555a580d4013030440300b1013200700c038458103c0000c1010302c09600410a040300c140d420102a0f4682c15919422148514000c180c41002d010707810415184545010032800c20f40501141d07603454641244a4080c0c103d401c5d1400d4500b032030f0700000c0c4590a942d030b4040d100d48129051a051505480402c96a010028100000c00100340b101108a035010000d010042d80a40c0f14196580485a0644c042c1c500040c51b1049003030300300c1c40d1030b43c0e030f9142d00010b0450083c4101810300c44280c28501121000d030302420142c8518008000d011103100b010b028841c01502c0790189108110400006580c1801640c81d00c0031b0317620b0310700700401042d038203600510f40c41044005100f03121403244000508980c3d95801c155070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 83347132 1250 83345882 83345891
    0xd050109060f06080903040603050705070219170309030312190c09060306060806030705010e0114040e060414010e0a02030604090f0c0602060a060311060d060308070b0708010e040302030a21090303 86
    0x8500c8a101c28005002e83c0c1c03070004458a01a10b0050340c2e80704030f208a40c1059664400034020034811400e45540036030040940140d0b40d024160280901043c2c001c2c8003002c0c8144c982c6214a1000200312000d046000c3c002c0c41c00e00c130042c6400d040310040200414035000c41412007450802c918440c141824405845010401307041c00381c01070441b0a580c1040062118003010701c40c2c1540c2c0090510105c0d80300b4a050000c85007104012900120301d41c4c11a0301d11400800c010424006020030a441918296010032000000700756105010701e080c03086600380e0781400c000c1500c101e5690019940940041c1010400f90b00580c0c4005180403201c00aa44418074841c0a110156051103226040240030700240032560641d22908601030f6503040b840d115180005122826041a421000013103400c4440740351a04514141a100014100e5000d00003401200002c111400c007048078a0046805034021410440450000d55090304d81e0103c801c25070000485107040011240039041d02c0034400d030350104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 83348382 1250 83347132 83347139
    0x8160c0f03020a06050f0618042a1805100e04060212070203030a140106020c060d060e190e07060c020613090c02030403140309010507030f0905030102180102190c05060c030d05010906 80
    0x1c040300c0c40071b00205c0718000c0381c405024499552255240007400b0700c0d058441281c81d90325007240e207100c107141c00009086504100c2960290745101d1001121740400c0c00c1150340d66010f86120031154110740170910300c1c03035040041c080d0180c003030b4005520500c90f030001131410b140c440312801ca00c4002c440000c01a800001082081c21817402040481c0e0248071002c13102c3e504114000c0c3d12008043c6086002d9000480e40c4c2c900c40b0240e4104000a0a2204c141d0805040241000001a07161640200d50605003d00d4090303646000490790704840156032101060075180d1b0030081030346d10682e12500e24040c400740200f510301d801c0c801c00103001d0694000711382c5c1381d00d140382400d5490101c08900e9102d41007404200256601b10085404c85641440c0c000142c0c01c92500540300507a254108640542c030106000803100e500c9600c0e4500c80c142602140d4140a4070b0788040c0d031040c0c0c1041e009090110411017002281442d6001c2d00501e01014140c1341400d43c00ea00403021140c0c00d030f024801aa480e0304081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 83349632 1250 83348382 83348393
    0x712020111150c090f04090c1a030c090d05030913020405030f0f0319110607020d09050301051e090111030f010e0f070225080604050c0103060603020a08160c0f03020a 73
    0x11042124240141082c6041c002c1098101c2c000185142072022001428900a903111400c0e9040c980300103000b0050060182000c5001c881c10b40a11803150a0783c40c4440102d022031415a48244103c0389910301e00100a418054030800001c411a041d10050180c41000c0e41d0350b0700780e0048140325400043e10396161908151501495a200032315541010200600040c401300c21182a2910000c03443d5200710304007000c845010070fa0340d8501c1ca41c09850203000d0201e50100e2400e40c020041d40e90b061400d5100d900701804c8450a4400140703c15200c1e240c1c85400072024001a07004480c1800080d181c1c0032a404c0d290554801c898840394298103030014040820005003142d0400701d030f4070710f9020515040d00f0196403030b01035142e550f0884619031200c2c809000c4114900e005428000181c405505140c42d00680e2084122440c0d404641001008541d2503c240700f50b41508000c1d039607040440d104d00005889030b09140071941d08110543c400c942c00b003092000c4051805101358010300c0e001d0003e0610 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 83350882 1250 83349632 83349647
    0x71505210415021204021c0b15040c080603210412111c030903080c01060b0711030601080616030f061d0a05010b040e010902031314010b0a051f11030c07120201 70
    0x3840d460b40e10601002808513030f0004050303402507041e1141e994204171406d4843c498000400000c02e544078101c00c21050700604255500b22000c152011301c00c0d003014007020394480300c0c111042909540480c0046100480702a601e04803000b4200125107042e48503007480f041d1401c0500180d0314129001c0d601a02801c10030b041c1309004503680f00c0c0054448082e54010210056448042c0071203001240c86040c000003980000010300d0141034050b550102ca2030300c14812204582c0e0148607000d0540005906c440100e0094418100101e100172034081d030803000d17802081d080b4003107102c1c155035110104020700c03a03849600340e030594803103c0030399854942044402c0d280141c010140340041070200f080b0302c4414040d0326040d524102005070b100e070790740b06c03800006c0b68040744068000b152903022100c031013206510401081c2c0c1c0984d0424545901c0d9020722900e009840b20400d160000c0380c100c1c0352400c1c842c40c6658600070120098900d040304444c10076241403c0d40d08003901800700c0900700d004642c1c001c146c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 83352132 1250 83350882 83350913
    0xf0f1002030606031314010501140f01020c010e060d090803040f120309030509090a090b01180b01020c0d06050c07060603051c0f1d0d0b0f04061d0715052104 69
    0x8154510300d0004045401404003402c00311400c000e29070700104010203014055918030584000b00080e41e0340300b0250101311030804503035001e0b181c4c035260500254070105420070b0340d04061b103c4661129107031f0b05001650380700000841d500c2c2d503544614070000340b03000015030148d4040d000840d80e5080da0f00b0040c1d00c00e40d924002c034052600d0301c400791300000e0b080819603049000403a2130050b42d540d5608000098000c10308024807000f0004c0011a42c0103803540b844080d1b0100c0d81040040c9186e00005907a10901e413501e0075400030060b02c6041c005402600881e5001c6410101d0030f051004590b660425030b0b801e0f40048941d5041840d03010412000c1c142c038801800c08520303000340d02d503200140107461100c24004915a4100780c104520403510340c079001e210450f41c42841c051080c540118503103140c28041e034084510a0801500400c0a140d40a04200b1820392401810f1003500d003018100740c04500c07402041c240401404040c5e600c0c02001503080b03140008150140140c40c280c5801210b00c0208030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 83353382 1250 83352132 83352163
    0xf040b0d06210f060204090f090506010b040f09020304020105190309020103050c070312200f091c080d05130c120201080601082703090301051f0902090f0d030e030f0f 73
    0x1060302e0344144900c0d5804900b5411610201e10048507041039030207032280e0b0f08100c03040d900f00500d0f003482c0d61039a4410502c580c002c4056458513600c4084041c42841244200c40311310707164a5003807255030f08036401103401a01c141401860035480600d100341ea100c0710500c46003c40e80d250005005d55816001e41c81e8024003002c4074a203032060aa40103001030418104940c100c60f917a0f140d6140054490380014041c402590703e0f66100d400c1d484060009034013201185005240340610b0303000d446244002120450b500003402410180780311a24402014001e10f04201051454030030300125403208000c00c003602d1010b00f1142002030034000505210005060303035040000140c104440c072858102000d00401c080b40d090340341c0d110215076181c170310f00905801d11751552a04062001802100001c180141e0b01200e41000c140c1d0741d81c0d10a000c90003401c00154002524280d072000624020750f80c1c003003031446410038005000548010a02d046400401c1045580c400c07600d480c004407041000762454203055 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 83354632 1250 83353382 83353409
    0x504150312141617030907030302010605040902030304180207020a0b04090b0306091c0c120e01090b12010303051b120d0e0a0f03050a120203130c380f040b0d06 70
    0x2040c004031140710b0225821007043d0003a082c9000c00c00002201c4a8056500c030869407281012045651140303842d01c0300310050741c64200002610f040c00c0c00790341140b58004014600b858904400c641500d1408038184444540c00c00542c0010b03500c07103240601821610b4078083d00d0754200b031450412103281000b100e22a602c104100440ca23900000c0e1180302b10b01040d414401151a14030a8448201c0c160000b89503006503c00e0380b850ba940005c000fa100802640d43c07400150707a03801c0c10320f44ea11514141c0141c011a050040c004640180d00500c1c51201010b480807980d0300c5580283d003090f0324a841c16991b00000101d8840c52400350082012460818010f4402ca00c010380d600c100090246100500340240400d030b094032240150405880c1c03c0041006554078078029040e407002c4440c070501100c00740d80c100d601040032030741160002c1c0c805002c0d00050b06e4407030300000710400060311789482003103440c01006821b180c1075440010304028016100307960749980b9001000c0c400d844035030700044802e4109 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 83355882 1250 83354632 83354657
    0x306030614040b1b0906030f0603060f070503040b06010c0807030309020405060a0f05090606071208070f03050403020c0409140d18080309060f09012c04060905060609040b04060504150312 82
    0x70315500b2400c0d001d88196003d444c0c50b01403426000d0b010100340c0c80400401049420001c141c1d00910420084003510303940d81d9180248210010140c41000014200707000042c0083e220104240d04000c05050000b45d10f03042d5550004540d210300403c600103605c4012000842c201409060380040044070452155421305205e90020130692003120710408003200410125100c6070f00300c50010381c00002c01807900700c2214018101c0907007580d440d000120060341400007a03200f0f206150003642c0c59030180907070100040402c000b0380b00c031440c151400c2e2110403043c280403604020750441c8400c561204100182d4243d080503400c009030381b111800381c100b003004100e00d0740c550088684284e2502182900d441042004850000054a104041404203109407241881c40b051000031034008613010320003903885071400001c1c0e86003039032070701c2d0040c9081c0900400d62600d80c00c03100101d01d0203000001e19594800001d015184441c00f041489003980340140140710328080d8030490030085040c12400500c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 83357132 1250 83355882 83355893
    0x7030206240405061306081509010b010e010c020307090204090b011101110304021e0301050709080c030f07060c0602070c0b070c090207020a030308130c0303030b0f010e030d0c0302100507030603061404 88
    0x7070302000c00e1046503200005003a80c2d80d10030300070070086603d64041008945803036106949003021004d042002003043c00150360380c1014054030a203810180e4030061000c0294006503407180f001c0303501b01da06019a0001154804140c4081c0c00107110302c40c00850088203031400942080e0a80c0301401349a41883e1030054011107041c1180c0c0c20a0781603841c0c071342d1180b05c00161921043c00303c44c5640d065081c501880011540301e5007540c1501da0300c0c41610840180002007594509040855010a401032201000b1070b80c01034078805101ca005280151515025030b82d404607032803090b000300956450220f4940c090080e100e400c0c10103403082d03550451600c0d1b4980c0024626440300e10004080100d14000034010351155010f40c00c0030303513000c000a0311480c1c0324034002d0b0241c8101c00d40b19000f188000090700e80d56200d028524181078010f0302511780a41941000c94060009110642c00d5108008400a03810814442c41e0312030542c940c2c0009640c1d05500d040000e40700381c801112101000201848007280c2c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 83358382 1250 83357132 83357191
    0x42303040503070b161502030709090911010e01030e030d060e0606040e0123030d020a1110080406090c050307080d08070f120b011101020d05100b03040519061503060207030206 77
    0x58011000c030345c0700d1500300030f00511000d49074002070641c01c507100451490000340c2c001d18096241d980312207808540b03a403114000c03100d40150241000b18144c030047d650394081e07540d60150740b0040c50302044211a05145601c0c40d8000c9808040d025510300c8200a11005403c4144d04120304444080c50246000d82000618406004000000080b24810b000d02d0580d28101030740303c0c001400355005611503203400794441043d8031080e1303101d60238040c00000500d04240350640701d92980c1c4403106070391a540c480c01e000f0400a0812180404841c1000c251542c0410043d4010800c00c802422814641c6500900040000d17001030180007485003042c0c00142c22021020171540001e40000da59480500101d548414000d46032800d9440000e01d5010300d0913940245104011503507045034a00d5a071005808130780b00454000d80281c01c0300e4404e01c10081160300076410f283c000c43c0d010840100504003680718444660085504550016244042503018068180c0c841d0010704003a8825405503001e45011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 83359632 1250 83358382 83358389
    0x40f080a080a0f050702090a020d111608030c0c0a0b01151701030f0c09020a032003010f051507050102040e15030606130e0708030a17130213180b04230304050307 71
    0x101c001a071030310500c4c4c807550540311229001071001ca0542088002c0200035441104494241814000030304200301400040b80d05c056202a1518070207032985d1552074441d040600b13290400b500070003401141c0c0d01c0c10044039041c41c1c00342e0340580d42940344c1300300e20000800001c54134042c400890b0070b8440c80104e016032281140c0c0c1000b19660300d48210321308581206803e800010b007980c070201d102c0041580c1035101c1c40f00503200c02241c20070741802c00b00c0300030240007d10644a0300008280c0901c202e040a4a0820000000c00c2410381084215a1080c1c2a41c0091308000940b1943d08200141d4056000300715803014004d07005040c580c10814040b80c002c0d07496410480d0415159040c0c1601c0200410100000b00b1014040d26240d000ca82001403110100d40c0c15290302c080240007040325118240e41800d03c842e8024441400d8815441c2800040c12003041c440384581d0b4404006008200400c0f60681701e45e2041c03500c1a0701401e011101c0c0060002508282d419600c00d1000303000d41e8070002102c0099 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 83360882 1250 83359632 83359637
    0x9140f010c03021c02160b0301030c0b09060705100c1b020901032406150807020303010803040614040e040605090d02150a052d0f070309080d0b01021002040b040f080a080a 75
    0x70103981000da107030204000c544103070b0703841040300b01030485c4c2d0100c3e250b5442e4402c00c881e4001a6600c100a050a00080c0405003503d01c0010b0200204481f2000500460b400501021700f48481c2e82c60f00c0c8c1c14007030300d42d41c4d2209082d1200101e024003580480d080c0c4051240c001d036403c0450b000e40100b4414241404010005004032413201d6006600240301102020305c81d0050010985504c40241c00880c108001c601090100c5c3c08540900c0c004030940e41a41c078038600541c1024540081150080c601007035a5049503802c000100300a09800e030b10a00c00c90140c080070401d420b08555980c03500111400700b8046410000320050310112842c92a50410b0f2840340101d03183d2103481c405607078030300d0380c680051074010343c030180740403031541011510310580e1486c00c41140c3e40d0b44e115064007916007103000240100d108012101062800741d0103200c8030b0b8010b104441401c000814080c040b40d2198000c1640e003800480d00300501c4000304480b0018040c11400b5080f0358100e40e41d500300340e000d12070500c3c05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 83362132 1250 83360882 83360897
    0x518010315211703070f0507021807020307110306010b07030c060b040504050f100b0a0504020d060512031309062103030e0a0f0b060d0c0605090409050a060203060109140f01 76
    0x881c805445601c8050034895070303812402021035040040124216004a40ca90039050585041d8071030740d416244210403640341c0e1001012025011201a8030541040341d106c0c184103455070040c062040140c2c0b140e0342d21b8004607078410160500c3c03614401800c0310a8440d50040c401400b85041e841c095440056040c140440c030701025160840103459100700e0280c00910303020400050000001e452800c502c030240982c1d181c0402025024260350341001d43d10f8100e081d00790104070303d0401d50f0040c6083c03030074142c2c00101071380c07944006039141300000042c51b0241e0021901d400301d0016051048001c0c44201c1c820481d0601d00075403c16502d200c00300c441c5190901030920421305019400401540b94500d06550b900001d42c43c1031a0036505805040e621a243c1e00006041c90901300d00c4480041e42060450211502d068000c458592212a14175081a201d01103a40090b00401c102040c82d44514405600c0e890070f10001042014598089602d001e0700d40c20340301d80c039100c031440d03001201802c3c6040c0c613 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 83363382 1250 83362132 83362151
    0xa0c0e101704030314130302070e060102010e010608030c0d090f1a070c09020d0615140306031504140d0801060c020609012a050106050d05030313051603050303011505180103 76
    0x9a110000700e00401c0198910000c1004241e8940e0203412440c141000140b89034071007241080d040041c10400a001d030313001c0441442440d99144c011030340107805100100d115403c0c1d00300103003035901680c0304010383e600224202d16281024000003914030018134003e240f580c5411520b506402c010b1090401103031000d200d030544020a10219541c09402010000d00580c3c0c1d6030308440254403603010401407038030302880070504540c800e110000050199584030302c01da6500c124850140d2014018070390620452034000c004002d2150391920440c0506900712818a000161303504260b5081041020001c8180040c002150855040d100c2d203034050316859111a00e80300143d41d000b54a6003058450a80c1d80b002c411640da008040c14055441417000744201c5950f8418084013001c49980107015420600000c2c258642e8000329207000d0380960103c400c1075441c0a810725240000d60029242908000014032114880c1e003146080e0b42003a15080e0b06d0000030400c246043c10b00e0090090406840c0c00d144c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 83364632 1250 83363382 83363387
    0xf0a020702091f0b04141504080c15091804020a05011704031101020906040b0a090b030615090607120c0623181c0f03140f01030822030b0402090a0c0e10 67
    0x45015001404c90030f69200d032210402c4041c00200aa09031084980d40d24002c220200e840a460895900c000289000c110002c10842440f4002a0307900301d010040c0407855203940d4901068040031101d28080c03c9506060052049440c240d0300851305002502401141d030b10807642460743c0c016018a082c50b642d0007080e8110340648100c0180592210011801090290045d0024072240b1607584420f1381e5603940e951108100e00007141d041354040120158014420403200062a203080003c2076240f0b025815610b544c0032441d000141800038810710b9090082040c103110b251007440440c1c0c07131003e540d003490550110703600c002420303107a0b41c440040503410540e008000c11002e400e4078091032030b00c08414040040a148400c0d50081c0001e051012030390381e004004030402d01a8103510f00e00c0c01c10380c3c00c50f242d2140d5940124003611069041140c0d01078003040c04c1100300007840c4500703280d1180381410700400140d040081d15124466181402980306141c00000b03941d190b0307000780da2140c4104403c1005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 83365882 1250 83364632 83364691
    0x14030303070f180b0903010e0d0203091002030408030f1207080402090c070609050607030c0306060306050a0501030c1214010302010e0f2803022101200301030b0a02160b0f0a02070209 80
    0x2200105099001c0418114100710141c203441d0170960003001070101c0100f0155540200d91500c0e409600b0400c0303509440e05201482d0465581c181c01240d1410355950709642c039562000403803000600d004903c01215240082c58150031480300c1c60906043c2c106030300060b0204030f0251035078040c03038400a4102c04121550300104500c54105081d151245081e00000e0701400703c0800a00001c0d00c1c00740046941802440350505070b84015010480117410000190002c00c11010500c0078010500d4604000c043d8a008051400040625544c50355245100242c0480300c07240659120b403c4858010900380c80710400c08420081440c00ea0b91b2108034910006101c244a80000e03401c4035856070035119003566210729112041d4000000c11082001d13648103040600411020b8081990070030040001c0383c18058a030750002101d0718018a8040f2180a0804400a800045139000004010410740c4024100c0c1c40307a0110101c14107610300082a40015007120004101644d43e5103a40032100882410848 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 83367132 1250 83365882 83365907
    0x60f0a060b030414010c021203010b0c03040e04030201020702010f03060608040b0402040f020c010501050a0b1204080d02040b1c0c080c040e04050c1017060d03090b0318060703020901030614030303070f 88
    0x201d0303560364100760401c200380503800240c0401c03560a04801440c643d1000840064004089001c01c0c11a4245813419603281e03ca600710030500d00c0705000114040c80d1000000d80918030a03000142c2e140c4d91440090158140105403000b810310f4140204400c903013001c1c0c03040c0c1c89503000078110404c0c1d40c1c501c00580205079080711020014408190355243f49415404141611001c54812414940c0c4101e904224030401e40e522035410400b04c007003070001d800000500080c074a00c00002d8181501e03141446107a4000001c480e075114041149400c00c0c0a07240b03d0340350108003500c1d02940d145040c0141d11010701c00e40c8141990038100301c00160621200703000d80030b00c2901c020180da07140c0c814004000d1148031548072782c099010031900401e61914054503d17040e800e602d03441d0544814980511803003950002402040d681c21001068651100306000262280300d65803030041c0c444403050300040407600daa401c407108901c1000c0240740255000401c0d03e5004589180c1100e186044d800b0454107040c40c5803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 83368382 1250 83367132 83367149
    0xa09030c0b0a20030402060910020a020306040f1407080d05180603090102030106022a040b0118030302161e050913060c08010e071d010e0604080f06010501021e060f0a06 74
    0x180714144669811008583d110b410382c2c0c1c108910340c1e0014200c98031068900035803020b010030907142c0358100a030354105036400600503160480c030550082810401d003110101d03482c109110b122010081c414143c0350120311000c006000d81c1c1d0404103a20703a41c0044844000c28030602140b50516441080fa00c58204a80500043d44030f050224505010790820b0040300c01501440300308004d11003080400d40030866410000e1065404c4240500c0014001204400e0402c05005001190780c00112100700c0294460b500a080313205184050f01e0581c010760300900010ba4520f00040446801d0b107545109641c803c450303510054660101c00581d008640c0c2000b4880c0f07051000c2519295085410035040319891a040405950f410004407030640039100c0c410700021500307482e034806501c01c50b140402e0410103021140341c03a1700c030342c00c0c80e1a049001401e008581e00c1540144007035641070000b03a041084001c503012065444c81c20396601c5890080c200d082c0300b450f0a00091454005420000080a070903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 83369632 1250 83368382 83368403
    0xf060109051e150d0c0203071a0c07020303070b100605090112110c12031501030b10030f1e0e10060e0a1a1f09080309030a020105030406060f060221040e0a09030c 71
    0xb11041c1c3c07940c2c02c40c1c0d1502503104d24101c80d42a400c0d002108542d04140e00008806082000c04441c21208401810389004041c040c00214010384040004008441c02184482e00e5840c205001249410803604103400b000028451114070340d0f0448400c0a6100d50072030041000454440f02d80503500484490249520818140c950069801001140140c5d00c644081c01d80546420055090750a01200550084030904210181c24030a5109811032101714402198010101c03001103030f40d07410041501000d5946408200140c80100102d4000d17401010003800014604103010032440c4000300700388603070790319050581100c0e0510800100d001000400c90418592690040502c010324002100cac081756007518045003800001095030384607800140100b45141813540119015040540221403107511440086078800402c0320410103051640d006100365190094681c0b01da042071039040c48032a034104401d10030b51006060580d840030500c83c0108444000c1e2078102d4159054010240114002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 83370882 1250 83369632 83369659
    0xc02011121030403110c01090b070213050c040501031b050306120f01020f03070e010e031207021201110c12070c0e19060608060406060e03060112050718020703080f060109051e 77
    0x2407201a5000314000d54440c0340340d080201c0c56030b50314558110b1503030104802e50307004c1006070b05100003420920320161960306240c00401000054030b0090b02d14048a600104081c0030300e590502c075540c00030700ea1a24003140e520704860060500d100280540307014080d5660315211450080051081d03c03040300000719035038041040c40d405960000d441d001d0000c0c0031039105102561183c041080140f00040c05000003281d41c401c070341d001c1d80c0022030480e00185552289115100203101d065040e00140c8425940c1e807001e1048907040c0240458401480041404146c003c29000044030303040e18000001907440b502e448281004508140d0040081c0608202c0c000c5403080e400300d083c900850041d1814403145460318000d40d1540d5082403125095402080100042c8032400e2007599400c4c0502c0a4900303580d12401200320305224916041c10f802d130000f59080405a0050b003441e44504a5110a01c1d14184a03000030300c1c84c0e035035101d105e100c0d18600c28041e204400c040c25445c1401c01c020b003014101101e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 83372132 1250 83370882 83370943
    0x507030b090a02040c0519050a020703080d050906011208031b09040c030b010e060708310b031005060a170c09040905060118020406050403061802060a0c0c0807060c020111 75
    0x82e000400c902a40c00c0c141c228403c14025010f4403c500812100c1100c88810204101d0f000d400522000046204152000021501c06802000c2080d8074950100e00340c130b044801e241ca040b8040e0b12400c5403410a0750102c000c200d92a05494002c180c483c541c801c00350340c040303211045024001505a1040c80d0100307402c001c0340c042d4014142c1c450282c807902c665291010030030800b801440d0703001d0004e9408020350051821400e24902c4040185207503d50010398071011b404042d00d20b600011550400081405507240c0302c18514070081c41d040342c82d0341c40c1c402c4041c6c00074000308500807400c074902048004034038040c0600007550350029000e00301700810b03001c0b81070099940720300780f103a0f88020080c00700c0d260780104507000321001d85400d17440d2185498a159903071f03401040484082ea41c0e002c5807695010041e0b903400010000c0300003a60317036000c5040c0c250404046103145607003d401282c5c000340d410010550402010508a6024240203007203c240ca40b0346030070190740d2182d41d226116071400e564841c82 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 83373382 1250 83372132 83372143
    0xa0b0403090512010524010504092003010e0108010b19051c060c0203071103030702100c0c030b0a0b0111010501030c05060c0a1515120206070209180604050c0114040b070f0507030b09 80
    0x40908111b4032080e003070440b905540d0880d01c10f070008108200030f000d0000c140c1c008042c603034084661014000011048180c0c160801c0e08210414103421004010f918403d0142c0340e041c0004861080d0010405850020240403e110b461301405a03444140311401480300078075030694008005201c42500c1312002512a40022401c4038541000903220107642070000036070b01c5459001d082180c1f01140c01e841070301d1b4400c040750111030515183c01d001c00092401c90516004008901c004540400c0030000500350150320b29194945a04d40303001040803030303180e02404086507002d40390a030795040a08001414120780b00400382581030803401d00d0448002a600200a0080300c0e0008040c85d40c840041da1004180c02801035880a000c0c442c1a01624103050180e4200032140e2000c0c1e2005044a003490401300111070680b030741d801101e0111855600042c03020180320009040516007810820701280b580508000a044002d00c100c5443c204041080030201468004400c1d20081c83c01009103580d41 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 83374632 1250 83373382 83373391
    0x8190b092103060102010f110307210c020c09090f07050603090102040b07050303060901050604080a0305030c071b0302130b06071101020c0603040f0501110a0503040303092303121302030a0b04030905120105 90
    0x150b103800e2507c8600f80403445818440340d100b501b02891610b400d01d04a40703414174400420300701300307108506031202c12040c402c43c041c01c201c58000d040001203030010407030181c0000700084076035081131440d2804d403200451604290703034080b80e07200c1e20707030b200e8084407402070140f5002040724400000c1d14400340007001000e1489002d085594000c982e88503014008a40100c0c45188104c0c0c4c0020600b070002800340020b10380c0490703044512403c0209986440012182c5d840340010342e40c40780a07090003941040c1c40c00751508001d40805000d00700c01040072075003500c104c842c0030748945c13002130310315000341e01c03e02c0710383c0c3e4a1a00a1803592641824101070340024608101107807250320b0042044030f01600501a94204402c0741c80e401e003190b031151010781c0030340320102040394075014038046894155282c00d40ca101c1c8004800007940c8501d07501c542125515000303098883c0100c001c02d040c800581c1c000071292a0b055200043d200c4076201d0386000d0b54526202d0f0802da600c080c040305a121401d50560069101d0f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 83375882 1250 83374632 83374637
    0x20319050d0e0703150c051c0c20120d02040b0c06010f08010506100e03010908161104051003030c050102162f090604020913020307020106080708190b0921030601 71
    0x145440d0075110b5a403007080c3d110080100694a480d40321001060b84400340084c12401d101e80703000c000f4070003050301d0400803c401c010f6a0350368400074080c1c1c0c2d02c040c29142d01034224005402c0c02a2107000960341700c2103400d0003040c031000014909080907594050310000e2440300c10560312103004400b156280c9000740035021000980480c0050401014000c060081e103001d0301c01845142106011a010384450305905c1d00b541d21141028002038840005048440c400c511080d180c40d410300c1d21100d0090314446491240f82803c0c00e1242c5075800748400d80460743e240c2443c80501e500ca01d03019001e030140759000c80d0028000140d803070034800d24100440c0504a1920006ca002c8090f507010b41d9903a0407180c059800ca8a4140010040e09003070f401400341c01402041020004581000001070f40e2040f100040181d444030b800300038a01080101c100a00b0b9460301038480e00800c260002c0f04928840b50140ca940090408200c0b039030410300203a040504000400c41d40c401044002202c0e0f50300c1510035600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 83377132 1250 83375882 83375891
    0x3e0114070f030908040e0703150e19060f05040203060a0e07180618271104030b07080702030703030c0e090906040c050102030a0c0213150e0703050f040503070f03020319050d 76
    0xc1d4824450320340502c1e400580541001d081050343c00300e0f11001007001301450303a9001116114021070103568010301980d82070f404240b5100002c1e04031703400403000440c101d0303003446001d209204100c050070003564401d450048e01d039a946c1c0000f810559103035001c07581882c00407051040c903560154890445107907400f00549030555828080342d040044000000e002e040d95030b01808000c1c0c040c035000c009120b035000314650700c0068004200465140058800d44881d0015080081160b142d030015031004c0c003414808102d26066070065140e04c10a04002d0030980d4401e08204090b005d0b480d0100c8104001d080c043c81850403420540e5a91401d85040da070114401e00005980d44c4004111380705610580d4030104812425805d11030ba944c3c000c0d0502030304540b00d50704040a03041c080f0740c0c5030041800c00d1404019003441c034030242c11200064141007484551000b00008640004211010a0340c407081e81c40030940c143c00d040f81580206040041d000c845403141031160740e4010064500d89500345404c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 83378382 1250 83377132 83377157
    0x506060301060813210e030c030703050706030b0628120c090905090c060f070b011401080103020f04063209071e05090d150c3e011407 59
    0x1926000922464000a0b558030000c2e0030b400104035034244041c4540b40c0b8200100c000074103940c0050760340c50788000042c2d42d416800194a41081500c4031201c041e005803000300d0650300c03855140c0d54180038040a05443d0b07458001c103034441900b00c1d8909940101c41440c0c0080f148682c41c202040c1c11403403000252100a903940d41100c0c3d1080b1903403070f501034462040702d920b00312256003d854001d001c08043c0c050850001e1080d160320300144021000c1880407a038800035440d16400c001d6042c2c111801040c40500c20300c00903600521618196501120450b000c10101400180602665040320030f51040000614619031101b4101d5030b0808081848000710007201018000807000c101da01100055a43c901858002d031007000781004000d0901d0000e00c2d2654060120f00c00c1d0480e103204503411110203050031003204ca10f2040401103583c0c2d1912800000d01c24012003800311000c500c01c0740300ca400e0816540a66000d06110745074500d1b2100034810507401e8030780c2c20a010305c01c0b584400032550000f101e8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 83379632 1250 83378382 83378389
    0x1011040905100608130c09090b010302130506130b03030c010915111608090d0f03020a140307020d03050a09050a030609030f0807090e2d01151d060703050f040e0a0506 73
    0x180300383ea00359a105a0382e9038610700078820300c8208103070a540000b150400840c0d0b0301114040d007418107011b4200b80360705500d07500c1032211144803100c00c020203c0ca000f080c0b01c51552260342040644070703404c174007190b1342b152540040c0c2184926001d9141c191700c0d142e9400e08100c000345001040380000c01c41000703840540c0e910300e061441504440d801e0760b91010145800241200080e1190400c06441d000b15046155525010b101d04902c050303000d41c1c860b8200340104240c1d0380c51025001d8030782000c0d50400e4016030204282840202e0000c1c2400800300e03018044c2482107412100034100106013800003550390500710000c2c01250300a41c00200c1c03200111315854020100700380284665960300741d0903032820500d0000d840c00541b8900704d1b60256850004038045202081003007a11b681c100410552510018841d9402d5440490003800000070404540700b602040d080403450060351a2984d8500340d03c3c0854841c850100311400d80c200114002c00e030014400e0380a441160b1703028040046807281801c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 83380882 1250 83379632 83379661
    0x706031418010608030408010e0601061b0f050c04020406030e0c0a120b0c072415080d030f0902030d0504030605010603090807060902030c0901080114010504050702030f0c1011040905 80
    0x2a4440240c00c003001c544202003003084445403071000c8000103002900c8040443c11a070259100c844140c0d15449002460b51080c4895801040e2909000b1030326440301d1103901c82c1d02d8010802504000b0703499411000d100b014014220010707030062045507902d4541801030300820150748100c4d071501c100b81102126061452683c001d0b034001214202c1c1c004280e540b4800c0c0a000180400a500c3d002c0c01f110700011007034181d81e06102c41d102e407511a84158090410129045042150049400010100300190020448040805192078046a0340000300820350190400f488000c0d0144641c8010b1070901e40d2101c05402540e202c3c1c0310070300c07050340d03210002c03015070300204400751414504100202c0080c0d4680e110000c2d05101a00b41e07044805010002008000d0992045034982d454040840c594068010780d0781c0581400c071010845420680c400a540f8001e20078000c849460004840c50304080420034181881c1781d248040c0078420030100004280d820502c6010107103800c00011400d80140d1042 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 83382132 1250 83380882 83380901
    0x60b0d1512080d110a080103060e01050105060d021303050708010213080303011a0c15090106080f03030c0403020409080f07050d0909090f0201080712060f030b070207060e0607150e0609070603 84
    0x41d509014400e490b100c00e59445585072400d440e40e02c4220040060b82040905a1141a0b440c2c4040320b40c0345041c0103069130340020441c00c0c0c5914207230051200742c1c2c6150a0301c16075440031200523110030402a4901c140d18407600050054400c01c00c00003003611054000f444025514411800300560310007601c0c3e41d0340002c1c00341c1c018114000b1541043c1070a07aa0203000c01240340400c982c49820308140b6407010101c1960074070540e945070907041c08054001c000c00c840212151008610350310341141c80350094003503400021b21803030b158102d80702130191250a660100d0000c0c60420390351041442c0159540d1510742074031001c80c00a0b1000500c81c1080d10a050000d90031240c552014211903004460703d900042141c0c05001400b180214031034001e118842c09042c03032401c01000a401c5007404004500c3c002e00c18011540241818001c0603800812075600b40c2096440c1a01c6000c076162440900d110882c1030141c1915104035110750750780c001001402140c10354203030350391180c13141400c0741a00c8030b542 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 83383382 1250 83382132 83382149
    0xc060a0c0212040302010f0302040b030a0603060b03070f050d02010504030b0a020316050306030607080a0f020d0b03070506030c18031507030504110402250f050d09061803110d0302070504060b0d15 86
    0x20130155004111070b002200036807138014902520348101c400680c0007940d6800b14640c2c0c9940910401029205040036110210000c0103072501d0040b000c092101e8602a69000b0020303aa0640110b9001c1c0301554080c5030f01c40184110751500c1103d840081d00200d40d101911200c051300c00d01101d014000305c038000c48018014040c980e0b40c5002c1650240d03005012508010740c0c8851403001207415101800347c203c100c52021800ca00e41f802010724040c0190440d40c0301c0e1501700203228502c44207104036154a001004910b0052001a00281c2448104107014014460314000c01950552540c4610312031ba1049403c0e01500781840180400c03801461100e5400a01034080c2004280f9090800c41d0310f64400e40b0310070f0588081da03644900304080c41c05a40042510f50100340165030308070030b0380c020a02110001c1c1a08a01e162203c41c0802c20803c0f01e1400348400d6000c1e00180341c030900946025100c050010b000182d130f6210041200c3d4000304a440e105450150400a0544d103c3e04c44400c071990321 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 83384632 1250 83383382 83383387
    0x160305040206091212040f09050c030c0405010c0f020d0605220503160507030507030605060901080309031203041505010b0910020a1a13140705010905090f0f060f060c060a0c0212 78
    0x2c007032090710151101d13091032a10500300c818801841000090015008445900d400e8a10301080c24040c4d03000a460702c002d85d80b044c000c00045052250a990444e07100b4a01070454035901d0400d500b81c031110715000394000c00a603a80b5400d01465800c01401000300ea140c80034600340350711030000a07000000006082e07400c1000304540401c2550180300d0b01902420644514695a6607564608540d41e88102c030300c19110420003442e813800a60141c0102416005107103000500c0e40001d495001301469118048004008907060011040c0c9090080d0702030982000596155101040140c00409003544548140542e050040d407010840d041d4403a4000c0003080d14907040510404030b000010094040305003031140e0b80e00480c1c095504500502480000b9100c0f0720709100006100b40e00741e4101a00604040c1c040c40003515140c00c00d01d510405626a48050707482d088009542c00301d42040617607010401007000e41c190300011500c41d0142c030800c0d07003c00114610303c1060340c590341200c040765104e0205 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 83385882 1250 83384632 83384647
    0xa0608060d0b0601020304120506010924180b0d060b03100213140f0303040e0108061602100504050304080a08041e0b0a08040c09050411151806091f08160305040206 72
    0x2c24510b9030005014010b8a003450340754601401320500401054070709504c400010000c19a40b48a98a00070007000b149498401740c1c40004041603e00f40b041308134a40014041046030710301c690201050b0840140f80201071222805d00001401c050820136109001d180c0b41e001002d0018400c4030700503034040d101c03030250700c0c030317005c00000140d620281d107075041070000c600c2001c1641d003030008001500e82c07441e5203070342e07541440307461490704c2401007014007503211503004402c0040c3c00150f22040a046503001060990b1185007460450003a0b074404242c1d880b9115000c002c000c005400b600a94a13100c00c41051520380c428415050341251055280d11407041041c0110a40f050b00a9070703005000304844408243d40782d181d0412200f0888042d00c0c005051031010810345000381000010141d220080da060071024114a60070a69400400d0b100354400030b0602031b0350310340329111300107070740441c5485a2038049c1d010054205c4d24100c802000c92041c0382245100070340a44103090081d500a04518103088a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 83387132 1250 83385882 83385893
    0x60f0302030405160b0a0e300705300304060f0c06090503030c04080613210201090507060c0c080105070c060506060c0f0c03010f09020d02010f1202180a0608060d 71
    0x1c00b90041d40c00340507528800819201c9041c030b28009140d26440c0d542e072032000030001465240103281300e6100e00440e1181c02c803004400c0b2501d50307004100c2e66606224110b002425071800c1a15846150003001c5aa0400c4201142c601c0c82c12030350070b030540a440c803440e01041d500e499115038040d2401003103074a00e800003118881c0300084000c2d8858800000d415105484040c51034104035841089064001014031454105102c01600071818005422007458280da030b00c1141e00c1c001850500101d440c408070a02c40b032003500914815600101900c08498a65400410b01081c84105680c107250040d8002402c020521600e48144601d60310340c0c80540c3d0701c2e9207410282602910084d445103051040071130095050210005003403c8000610340302c20040709041c2507601c02500c0910042c41c0030750740e10158550040360729415a091802c0503840100d01e20980e00810055440b4000340d2022a024406040d04028414600c400f2180c1000d41c50341c07014200c800a20407200d847d001402c50388540e00040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 83388382 1250 83387132 83387137
    0xc0c240403110a0f0503180103051006050c0a020607051501051203030a0507050405091f1a0708030403020a140a020405011a16110301090305070c0824070201060b040305060f090304060f0302 83
    0xb02d4103030940315258602d0700e48540c2048000400e4402d81c03c0065101e29400c040a00c010340601c1c02c0c20248001c2c94000c00c0709501c0b420b140300e4a000c1c04400a03c110145005218101400fa030080005442d04060300300384e955074a520340241c130b00305078010010a1601d401400c030194450420019441c42d43c0f820000c4000c0c0c0000b92503501480000d100200d640d90310b240000e0700c01c102143ca010f0444030f40e07512a0800880f103a01001a80414140c501d4041640030100c80c1c40b07903003007079040341d403502e451400301d280c060400d10191501c1800340d10702d410044041408450a40200c030140b00690326460114018021105244623160081104080c0145100344032040140500500c1e2050550035000c2401c0d03c00c403080490008070009003a07400c2286800e203640103803010070018689a03420f40e032500351032031080d020b50800c40340810000352344070310035081400540409030a064965a4034600699102030035162002103006920001300c40721400001e85044990944d18440743c0350240000754000c0d07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 83389632 1250 83388382 83388407
    0x4060b090a062d0f2a02150c01051e0702060f010311010201110d0b1201090308190605030703031e1707030c1b080901170c0f090d0204050c0c240403 65
    0x35a0340e003905080e104445100b200014a154440c0465074138001401805642c2c549014141d00d01c84842c0441c424000c448141c0015a0540313070100c4414008076921800e010741e0410342c00543c00c02c410815019074803446c401290b10042507000141d2500007003a070701c9440413124104002202001080031813803180841e400c8a00600000505482881070301c01740f6444510344c410581e44542031a013841c00c001c8900c0c250307030540c100204071510a0740d50040c1143c0d00a003043e60490b80012206540da04583c0c03140340208001001c80350700913600d01d0080c2010078620350a004600300e05101c1c082c01402211006803020000d10000d443c0e035241c0900750010042100040b00300300c44c040c0000250a400620a40402d010f4580d1640310108a400140850180c010400c3c1c40001c0c078041c009462296070503104108221004191180a02c0d004240c01c4cc0e07214201950160520080c05459000c5100601560195405880c3c48895002c103920b2141c40000c0c1c000d548110920008000c644035001d41c8011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 83390882 1250 83389632 83389667
    0x100f03090b0f060f030708060609100803030405011e09030c02120f060108030d050115050904090602070218060f12060a05130b0406020c0106090501050d0b060102250504060b090a06 79
    0x10380c603041c1c588070050042101c900301c0049803081480b54602d011050040c1c101e00c214000c200d05405c100c0740940311400500401e002d0600c900210b85a80001c98412014205a40890752246824101136010705a241b005000c6240031100700010240c95018020100781c05032a800c8400c0d0721582401281d85103002038000750b001e40c00380e580401c0d81c00e205282c02402c009000f1600c483c554510b80c001c582c01a40f1151010311070325100e003007441d0004c1c00c3d00c0e403800b0129000608001d050410001034815960000d61140c0b000d40c03807070126070340110b644e400f980082c0d6202c5450000f217000e10a050b07e6180b40a41980c4c46000080c800003d00d401c8107a0000c400e240c0e140408138196150034900c5426102201e00c21740100c0c0c0032a62401c01d00c111002001d42c81c00501840d450319011607040540f210703025010b0642240040d4603039000700421074081c9000100c5540b07116040341480001a60303809804d1245052020002d5103052502c2075a142c01c000074551540d0710318101007034401c0700100f221001e6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 83392132 1250 83390882 83390891
    0x30c011d10051e0c0d0807020703061b1e02120d060e0420090f01060c0c080f0106051503010f150309060914010c080c25060603050723100f03 62
    0x201501c41000c03850000040b074488940b43c04110351043c00d0794810207610300c4641c0c1c09101c94510180005265145a005801c02d40c000e5110910200d092008580018212905080600b01e22a1030b0321542004010305e40c1d1000c5121222000c41d40070301c40c1e40140000140c2c0610400c00d88410310400030320009401c02000100306641d0b580c00581c00000f11400c0c1c1d03a4958081d900340880342d050102e41c035003003030448084805141c841d4026699907018002c000070080b81984c0c0c401007044101c0c000e405800e61008494a004079100c489000c0e0800c0e01695000d00307040803400702c0102f86502624165401038030851116401d0503003141403260303603006000805445900c85404510703a07206010f07181d40290349495810034803100080c2503540a408500400ca8848200005030602d4800d5500345071181d2040c00c0c001501ea41c03100207280b00410080d10b0907141405c00020898001801c404860351400c43c00c09055045081e00d030704555034008140c001d50340e82065a0701c1032203540b9806031410113040025 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 83393382 1250 83392132 83392187
    0x7050901030b1305040b010905040b04060c02030919050114090616080d060b090901060c02010806090711101401050d08070303110d0e0a021c030504052112090906010905030c01 77
    0x221010f824116440c1030650f90010301c070a000b0501c06260140901c2c4800340b085080603900c000800100400282c41c0c10364518810040510134022600000d50050000f040c66004544003590310038144602c030f002c5100f4110f484d0340c40c0d545070251030810b400142040d0410305821000000302e480c01c101191420f03c204001c50004e2034a101e244064a52a06055121440744040c4802050b068002900340702ea4902c0c0580181c0e48030b184070782e200c08151103008054039419015140c2c6100030390994000e00802c8000414414660320020f00b64040044481d2a40d03138034020b000e00000b43c82006490307040200100000f080c065040039072241c001112162800004181780c000b25801030b51400701f43d4202c00e8843d000d61820950012141054038008080b4090701d69019010344100e1050600505840119414801a08200b00c44601480c81990322002d0361464801c1d0319170200c00f0a9200c1d0703c01034003140c12548140c00590a56030040d001b0b09244c82860019101c1d040e45000f2400009a10030713100c3c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 83394632 1250 83393382 83393389
    0x50f0a080d0507051b03100e1204030b04050606040504051213120501140105030304050a14030c03030a080109060602030304150e0c061603080a02030c07020d1103030304031d040c0807050901030b 85
    0xc6201d141107564030758a034401460710030b0400001d0000070030800281c00a440c001e940109407034541c1c40140c500041e9001d041d03021142800c507d02d40600d01020081400400e00c810000390310b10852080055509a9562508206c104c84e0144c0f40581103a0042c4102a480003900c4000c2003100103d2491400095403001191034480d45210308440a07511204005107200c0c403200d2146c050001280550300701401c10b004500c501c28548500ca00c14600141381d29942d407000d000c00203c094002c1d0641c4c2c0d40303036031000e00a0614803081c4170740510903181c8180000c0e41480841a2401598000144240c8071502d01829004c0c3c08015201100c07401441010502d80d0380702c400510044890580e0a4403030b205a0601400c134401c0244903142d040c0c0100104050040020304640d1240c0c2e048a0304184420700741006140360340c4400b5071a40601c0008184030a254020391610200b042c80807007c6000050301d414482074450000ca82004a080d48020800f014081e2014104008062600058071501503002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 83395882 1250 83394632 83394643
    0x80c0f010614041b02030d0f0204030206120f070203040b0a050918040302010e100510050402030c0f070c0302041b08041103190c1509030305160201031e0b030f010c09050f0a08 77
    0x401800301d00e840315082542001d008000000c6034844020403000303420704c80a901c3c3d00c100c400d0290a2070740c505042954691603415500915005852651941f036070f0084a42642c105407050507081c0402da0028032801e20000444003a40d10b0506010b050404081e0240d03210342103e1001c0344d012404000014048140340a00c9210724066800485c1e840341260501d42040c083c00003001c0c03014140010444000460030f044400c5031415100141c2e25590400302901c540036022659000c0000004d0b403506000c1d440f9103100660303000f103c08008070701d00c0403610860400c25001c410041441000003030041400081c2d8000307a03243c06070641c1e918009032550325031a00c401c03403012a0195920380c010300a01000c001c68501c18601800c098580505588001d41580954500f408120151031251011640300e5000200c02e44012101d2025940700000ca080142c0f8900d42c115003e031013520341079100c083c0c050144820311401a01c528141c01e0a00051200c01c001c11200550010300c98000000d280004009 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 83397132 1250 83395882 83395889
    0x41406090a030806030c03070b180d05010e011a0f04050a020408010908070c0803040b2b060b0a020606011805040e030f19081003080a030504050c19030312021204080c0f0106 76
    0x18107021555468050140000500218042d6001a500c1036003500c000594509448071030140b103445840481026030100c6070040c0464011100e00c010b0420030405402c1503152001110090101802055900141090300c0b540250f00007114100ca02d21400c140d40010b400030481e440140c075041e111400c0e6800c0d6084158121001c04000481e071051100c404031042c0a441520041c614092405103002881e00600143c02080740304006890f2810b258844810200750707014200b0b11034113544031502a000c0d006035075010058014030380095950340c400c0101c4548468075070720b00c41c41c0b01d041c81c0a100043c00c110940031141e2104101061603544480003801002caa030608aa8400000c02c03001000814003030103003c104428014103000040401055640580d00c91070700041c00d90396802c00515043c2c41c0c015550700845940066107a9900d08040b00342541d0090312138001d181e000210750812445420507110070b141404000c80e0001c0c490360010a4564400802c4821180075503001c9401c5584581c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 83398382 1250 83397132 83397151
    0x703050102041e0f081231060e0a18020d060f15020d020a03020307110105070f0c06110c130903110102030106050307030b0102190b07050c030c0705240a08041406 71
    0xf05a40303e001030302c18003405904a12280c105d1074064116902d120107100120319190100b071100a02c449500150050041d8000c01302c0403404015030b256841109015001c0084c00c4103c180c00d140c1481c1c4101c1c0115000100e080c415041c19041084c000d41142002844c00c5442d68030000700503041d210303401d001d0642030700703443c409060040001c0c0c5000304c490364001c20340d00060300c1d03040426008406e40342c1c440d07041800000c01f00c06a000490b5a071040c4400103084a08440c03803034040c00700407811081520f40703e4803103020039100c41e05030300d40d5203a5a001a035400358081e1050443e684454105d80e100c1d502c20306000120079411000c1a00313a8000340c110500090021082290080e818003e06051500c20300140c41098044441d0b030707280c1100508080d14070211500030038410351040c8102c034407007801c081c01d590300c4a240c910096100d1403d881010b12aa40003403c00701410f000c400021a4081c030803090520346440403601361054940100151804068148543c500344410b000061144400c0e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 83399632 1250 83398382 83398409
    0xd060308121f030206071a0a0902030105070507080714120711130603081801050f04080f07050a0e0f2a0702150903030d050402210303010e010e0c03010b0c070305010204 74
    0x21076120007103003030040c25142c6800010340b5a010003080800c155054a40640e2002ea03554058105450704210701051400c64045c0c04c0c1c1000307110343c0294010740446e48210028012074070f4103881250079003e940d201403d413650070041180000c1c003101d10b002c020b4110300180c03803090050462840490b0040c24040e10031000c05c1910b5000c5161204d2546144a4902401c00c40d203421601c40039158080c0070191041d981d292000014503a002d501980c0d24010043c407866646c90300c0b102c0c0280c640c80c40030194944c51041d0103010500b0701c2e01904190a0b25041e40c01e5650960390385000ca1002c00005e0100311001070052001900c4038908040e01038103401c400d852903a10307145071044c4810324082c507a120303402207000e1214035990b541c0070045502030100ca1301c000c203040e10345000045a500020310242c5260703200072010b0110020100280d81228851204038596a0341c8140c3c0b0310410340c2c12100403115240c10070062100084c000050b0901d5159401140c145540301c0d528036003240e019801009404540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 83400882 1250 83399632 83399647
    0x912050a080609040c0501050a02070e090c0a080607020a1b03080a0f02060a11030106030c05090301060321023c070b0306040c092603120f060103060503010902180901020d060308 78
    0x48640c1da034202d1400d450b2a07942d890076449500418030b1034015241004400600e903e0720328400c00000d070140644090a2590342000032805940c0c400e0005001c0c0107000e48000003903480c0010611901c1a6169006001c1b0301a00707540e61000750702c1745104000610001071012000c2280240a0001d00c28191a01503000842400c040c0c5828070003400003c2c0f05081250010340d448400381640d0440f1014107000c1050448903909403003500138040d41c1a010b40c40c02c40c000091041e000e82015140f4001c0c401c0d24040c2082400481c1c8070600d50302c2403841d8048100c03004103a2044040134641c074420310a880c064034542001e055007001e00aa200c00511800401071243ca03141c00d200381e600b14481c82c1040014980340c1449080020403e8808459034500d07401142000c3d07805004696031401400340d42c510600d403019410512002c140c0d02940003e24000012505080502c1205001a0020602c01e909c10f00000c000c2050030004107442001d540a110381c001811706801102d005d075210f000001e48403502d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 83402132 1250 83400882 83400887
    0x150a08060405010e280905010f050402010305010501090b0403080901200c011b150903050c06010b07061808120408040f0f030212030306010903080915032e14040f0912050a 75
    0x106800000800c14280c0901001c00c000c40c503580c801040a174403454189040158220040400eaa4064015401c01034a5000c0980e1640b00c180b045d4801d0700d00700b00c640d072540011a0306000030b0084184401c0d041206002081c1000301600306c1100501d840340c03903001101d0804070100c0c481e80c01e91056910178001083c01c0d42e0024100e40859030b41070a10504008282c0319423068502c0740d03055280d5242d4503141c6105041c402c00c222960120060126440c6581d207030340c0401294003000782500c0091a01404c500743c59a003d890031005a08126480c1c18007609840c40440d5107005030007150520302c00c1100280304100c002d1050000e240c0c8100c0d8003203461840c0140f00c50902c200e03242400c0c1e0b4000300208041030fa00400740320250f0703400490f80303510b03100103001181d2807580042d80c0352010103010040114540078091002c100010b0600780e417846010a08079100806040c0c000d0604507000550041190300341548424180e14800c0b601060301070580c1c450340c00e1aa201c2102400040000940601558 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 83403382 1250 83402132 83402141
    0xc0c040923030a0512090703020301020703080108010b030706080708070c0b01080d02010506120a0b0c041d0105100f02030a030b03100c020d02160303020705091f0605090a09060f0302040b150a080604 87
    0x40301c0501543c81c11807031040040070b0348285c51a80140050003404500d0200f010404407001d1507024000719980d110a05000d0140e100c24800c0207000e6007404c100d010681001705483e005c940782c5855210702511516800d440940d0000c1000c420000c03065142c002084c140d0740014000c05403030010f00b954000f0003030001d007514801031030b0794002c6c00d0030f17034640385980c0c0006240820756030003441910300c644071a10034105504c00d0b41e000044903210b0aa210745c46041c04c2e044141291422241c580550144800035078014141d80342440c0940c00030720003c0a0203006e40c00103031031410002d044d21145688081c00d2011070b41084c006200581c0454000c03140603804102840144600b02980350202d446c555000b9611541400764602503c403840210316000c16041034488001c80c145054420705480e0a401003a0390420200a0b00c0340101400c001142500d178402d19041c1c42c4540795a141842c20b40e002d00010b03001c070a50071904001095030b01c54441c0c240030090041040155201c1c440c0f410041d04010982c2e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 83404632 1250 83403382 83403443
    0x1030203040803060409231507030509100c020109060204090204050103200406120204050907171803090607081c020403150c020d0305040323030f09060103170c0c0409 73
    0x18810030501010565000036a13510540c11a808a0280d005140c40c01b9400240c07004c07044856001200100d4104020440185145079185801c001da0740d003480c21419114203450014203500711807030740e24000c40b050308401142c141500010032915140e95922080764441d0340309803207056010070207000701e60381070140a01001007840b00115455914010b548144140d1185109100415108020b07040c1d0340d80603100100300003888641c103443d0500c806044820325292488841603044000784101c00d000140ca550400c141000350300b844403c10503c9500c2e44042400d64032100103001c01341141031402c1ca141051600c0d031b0360140e00d491071440d280c8030075040da0b018030b8a02824500c500645990002d0011008416072038082450344441c20140c0b02e03050503440701c9000304c0e0f1483da0840d400003400010341c0100d4070800305910b03ea50352a255520758038280070042240c00c200281e5016503a0781400340007800365070000c1d5110200110002411070300032070012030310007000101c02c2440c41d036400480c0070350 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 83405882 1250 83404632 83404637
    0x50c010b010e010203030703090f0605090f060c03070e011206091e0609020306011d04060e0a0209010207080a03020304060c1106040f180915182012070e04060b060706062301 76
    0x1040c1c4040041d4817408001c08030710408d555099090107000c954440280701c240c02170410042400d00304036807910707030902c20707aa24040d11a01001c50a00e1aa00d000c5921a0f183c1e66036025060800500440e402d040c00100c624100e900d070080455000110701c00c954900c01b0488081d01c0740f000c5580340300190f0f006130b40444189c0c0c0c4103104004950342c06c00c900c0d9140c21040c541940c80401c448000030010b000720f803c003a42c0c440c1035408100d1181d005600074600b95400340c08690031076580f260301e0765882c814041d000300140c0050000300030303003800b411154501c14450600003852010f29808105681c02a600440007201c105070204010409241241c00c1505240414007200030207440d9401072100d90710040a803540d541c00c0351000e0a02412643c1c948561001960091070751a003524002c59808912683c4110b07500200c504e80c4160000c2c103a0f00b124001e8101e010250344a8031480010720351400850340104042010031300050036071144101429072540c840003211019009a00210880d2503420306 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 83407132 1250 83405882 83405897
    0xb15030f0106050c0a0f0516140604050105070203072d0603022703070e10091b020607050d110a0906020601050f01050403120302070f0606060806040b090406051503070303050c010b01 80
    0x6854031003068506403105400d000781d9483d4039402241c6030444500003d811211440c1c007104c00c00a02044c17058000da0446c2191007600d48445807000e19460481806a1044041004110b00d500030400740036104c0c00101921985a9552041c2054021056921400c503203420f0036211b06458520728200032742041d28046040859000708000c021a800e2454a003107841819440c845a808102107000352800742007402c01424150352048048000b40610031000f800d141300b590f022408a0040c545d1038205a0040042c0c1d140d40e40150b880e82e0203419241c40d0745840349140700543c0403981c002c084a003202d0f5a040c1c21180f618000905289040c1c0040b8411055103142141300c5c0c4c1d10106403001d50f40c00205001c0b00f00d0750741000313500030701c28001c00410f5100d01c008500140180c50348440100c6819440d07000541d80c031002000b0403140392070501607100f240c2d0350200300841c08640c00b02e41e1161401d450003c0300d400c0e040c0000d203084425841117001420008540e8a040340a000380b000c00c1d00c080c24130a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 83408382 1250 83407132 83407141
    0x10f050118051c02120312041a06090a05090312070e0a08010b0d031101020c010518010b010806150903010b1905010e0d0c031502160f021c02061b100f0b1503 69
    0x1801001c2c4520900701c20300c3c2c01c454080039943d40200340c00400c200d0748210390346c5844a002900b8401c10807501545e18480e407a02a01008000e82c1c9181c1c800c9400504080c2150741c1c10030103000508016050042e03d20040c424194032510103007500c0d014141c5503c0da102c201d04940c0422108041e00c0d00400c20a9050100184d441d440c0d1840d80520340b07a16052109d513180a419a4500900640c0102c210541c00d02050082c042d03280980785400c000544000e002043c4914015548110141d80c4540c201110070002000803100c140908103e440007000401d58404240014640c0740c0b066a209d0215100210100030540e0801e0507007500d91016500c03502d045095455011207440c49110140000c0380c370310034401d04030340a07904903030000201c100010681e10030317403d00e044d258107a287c08034040c04600780e00001003811083d1080e10141d00500302884d246595110f403081051080c0755070100e02c1030940c1628462164000e41100111035100060508000c4003004011041140400c821540400030700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 83409632 1250 83408382 83408389
    0x6080114040c0e040b010215040318091806020d02070501050117010606080c0906030603070f090207030806041e0c050d0f0506040c05030403050405091e0708060a05031212061503010f05011805 84
    0xf01d06030320b021100003e00c6048040140c1c105001307004c610403001c082604020130103401040405019110007520f2204039180c4d40c8110843c0e80c104040220006503010751000034100b41c004140151a80c400941880c030699106801e4407001c0e04000507041071a03482091202003485020024075403131030216114203000502c66000d200e0211403e000350350000019169032000c2207940003d1650030518005150740d034032061300075000354100718000307181580440d083e440d15018243c10384007200000a00c0ca001caaa1030380c001c0503110394500500209101e664030b01c0d50981b081c000b00d600c2d070350000f042c1c03858010108000c80d28007215403402e202e014010b01c40800e40c007900b90790540f002900d03101d8164035103500310010306000d81403c2c0801d2400b0001c000c001644150074901601042d81c2c0b43c42415120381c10503441c0c10118101c0d21150f02c1c10b1005e2412900e0f4040460b0304036902400c48229100928808485940241c118414404400004000c2540c1c04101e0b0802040e9a001d40650b0381e0a09001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 83410882 1250 83409632 83409647
    0x506090909160305010509010c1106070309111002070504050c030417070302030f07080703030629030c130312140301050d03050d0b040c2d0906080702030705010606080114040c 77
    0x549018034012000624203100070801441898050002007050959a241c2103001c2d1104840e00d51043d400c00010310401809000c01c0340c80002c1c4074024000759985e07444224020040402d06845055201c040f026164455001c0100b11a143d80e02504e0742900f0705051009079030000d08561024842041080040b90fa0010440302d030381c0c1c482000c143d444206007012851800b03615125507406100059820070440500010801988291010302c481ca6840c10a219a600c5c0368241c000032183c0c03100001c10485466000f540d2101e40c0c42d100d0b0341407080344850700424404c15001240c4140d0441c18000003c0d4203c09078814103441c007006c403844c40d0305080101c3d06501c00d58500030144880801c0e5034480311007076040302810500c05003003088210b2a03140010700030090348000d0030580702d41d400640c4030b00307c1e070344080035450180b5100d015440384dc01004540c2e059008005208501091182000052080c0601002009142e541107031950401010411082e6040c0282e4816458443c2140c4803580000e071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 83412132 1250 83410882 83410897
    0x1e05040e0c0a05250203060c041d0108060712060f080d0206090d0e0409030e0d0602090414040b010519230406090c0c06020a050c03070510050708130206090a03080307031b090506 78
    0x82c4071000115801074003802c413540010080d45809001c04020001c40000301400407583d40d0441c040b24000d00d0011040d00c1c280038051069550400303030010320f5407070113074504481c40d03e94140005112565902c00710341d02c0040d030700840340355005544c1c248502d41c1c1c100b08041d0448240d201410740b07007000e100050909007072142c0b21801182c407008850103241c010000b922034000c0181c60419600e550746014002503000d1000d0381c0c032a40c41c0002d03c460301d40d02116207038815980107400c0340050b401d190400906254540481c3c084039402140466403588043c08043c80250020b00001c40444031003c00050f40d4039a000484c0c0140380c01d0983c2d1045da032050f0385030007094121400680c0c485101e101102c0c14443c0d00d001d00e506102c00a408003c100300051440510032690300c2c100400d40300c0e004201d80411069401c1402c5040260b030920251528100a2440e02c900401a403819541e99403104603580048420401003552001c00384100320054114101544691924103410707070410f40000c0c0140581d03103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 83413382 1250 83412132 83412157
    0xc010c08011d0601181205070303080106020d17100503030705100614011d04060f030305130e0f04030516020418120315140604030f051e030711101e05040e0c0a05 71
    0x20080600d100c2d410a08004e1b060060402110301154104113030b54518030301c000c03000900c0d0705c0000110b0520104002c0646001039503086454140032611440140c03014000040c0700c074645100107140e030790400013005094412400740824142e0f0303854090441c1c0342a40602000302d100e424480481c0e0b4400385900c00d50154001e110444ac4c40c00c800304e0b004008c0c60300044000c5011000201c189178209001d001d140204044102c10180c4a04900e60380d0f11068401004020700c0e40003060009001318003038183c3c10501030342c101240c01030b60006800d803000f241c0c0c65000c1c038040812103414040c1103c00d8200403801810140960061105062115400c41c4124281c05004a20510b0350759a0541168019070300080701d40e00b042c0c10783c06e1141d10f41040c0c140c070500103505104116001c58010050b1455560000b40955295110304280070701d9042d221909010840200700f580200d518a200f00d000d03c0e5000d5492503290f03811f08030719003907698024041030106002802200303001540502216000101c03071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 83414632 1250 83413382 83413397
    0x190e0c060306010305250302180d05031605210301060f0215010510020f010603030f020714010804020108040609020a0b04052e051303050601080a0201031d07030303200c010c08011d0601 81
    0x1411400740241c051b43c81000705094071712018182c568035801400010040b45594143e11203c801088041c520301c2400808541051019024100031307003038451420b42c001c1c07082d81c4080c070203050106803046403a404092010800306c01400030991050f1074455190550000301301070701695880800d0100d05100d02071180400c0c81050040510034440d00300a800c0b8030009011280c1c4a10f00544880140164140180700c1d0010024801070005802000044180c56000d180d840b030380c00448008600410036110203843c0c0d012000180c5404844100400000c842146c95505200400c040c290000c1e2500328071803503518030050a80443c1e200b03404030002d541882540c800131000c4810702541e0766032010381180160350000402c00800305580421034402d03030b0204a0390030602c03110000c9104544003c03009901c20041440041d0299010a07103820483d800349103880004048200107622403907c0d401685d441e015500342c019049414a80580604406000d4030f03105e5218014070218001c001d9810010407 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 83415882 1250 83414632 83414641
    0x31a09061f0302040911030a050714030a0b040204120f020a0504060305060115030e070905100603060311010e010e04020d09021203070503030a050703090b07050a08090c010516050f06190e0c060306010305 89
    0x3d9048a00402245100b48202e0036040450f034580c0c6c208903110301c4864141000039564500c44c0e050618581c101c0d0840300d003103480e1121108001c1040400c52a00158204400b06010030140c003418211441401210003420181c4103010040806500c00c40c0601e00b40320040c0001400404c11505544413869070348180b01c0ac00c034040b005840400c1080e1807030b0080d2100810451407640100f03220300c20701d264580c4503580c0e55004600b100c01510028200c044150159a920b41c800c14800308082014074082c5900c403030180c00a0101d0307000b9202014040d42c0c40c02002e0443c28040124002100b020010b10300704540d58550301e0300c074400144007000580c1c1c3d500004000300c0c02540300d03442e030a400031010b005501d40800041c00c0781c2d006034040804580b04000142c0345c0e41d0001800c0f09280303010380d141070424451007141e105400161500302e8240c010500c007044002e504101140c41819183c0040d403075031581900520490740b031050a940ca0750400e150000503600c9000441c0d400070001c4ca8001015900c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 83417132 1250 83415882 83415887
    0x40306020d090b01170601080a0804210b0108030c0f0d170709031a04020319020a12050f0f071a040302010507201216050102070503102703031a09061f 66
    0x25110350003840101c543e00045440040c020000900b41c064800300c448507629902c0c0c5a50750a60503078018810942040b00b800b80115002c580342001d921080300c2c0030200ca89580e0021020026080150b03183d0000c00d0100040c0010800880d0311103114002c1c21f000b6101135801050461202c5040311280292000b20300f900b03200e0070091005541210420050344000c6d01d801040b0003003031710141e1080c0700d407040c000c01007104600040d084580c0280b10180356850209207800c0d035800701d81c0c11f50b41c900441204040340c1d40240310b0801840162000341c41294109801a00c5403036249048086515042c0000e00050360407c040703900c103c1c1c202e100382c80048069006130b1124901500010f4000d800103030110010100040c4407001100c541240c0c88105841d00012640c8800902c1826031661028901e60740751602607101c0ca505100c51501c109003842a85a0100c031240310325021000079940e00b81e410800c00004422904d004411078600120b800e01c40001174540141c40ca8004a81c401030032007208003030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 83418382 1250 83417132 83417141
    0x80105100305130804030b0f070e03100f180b010501090806090c040f060801140601110c0114090303070209010806011d060d121b140601060302030420010c0c03081b0102040605040306020d 82
    0x2640304c11901da480382c503403900842c0080c0a686041c59911450046190280125081b5401c0e050241c000c088036820718034008040c1c007034a40d0041c1c0c1d1301c0da074a5a1501c03101640c5000f040d181d02808482e191545072100040071410300c0d07032168400350051030170302c804031901242540700702c1c0c41154042003001d500003500c0300900300766002d038180c0d40ca050900224010180c285d0f43c4180400d0300c81e100c2070203020341107540301d480003e000d80c0043c17003443d1350b0b8101414480c0036050901002e01100d00b00512980810454002a001400158041801084440c08002c00c8403080c080d85425100315041440104160104602d401013035803106401c0303148024452a200e014568900c10b00111030855420300d54005122520708001500480001098850083c004c0742c4c01540d00c003441d145004200400800d03406d10301403041e410010084801c101064100d5002c4002d540644c0c0d005a40354003200d030303010301113820300781002d5264010301080040d2500101039504882e08001c002d80d0b940901e040000040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 83419632 1250 83418382 83418421
    0x6060417010b010906030c0512040c0b0307020319030b01140c1015051201050906010302060c0a06020406030e0c01020f0706030f020c25090501051c02010c0203060403110706080105100305 82
    0x25410048061015009a0418602130300d42c10350640c2c42e400201c2c02d4554890803200807d90402000c1c01c00c21035810300942c0103024414800c001c6840d0300110600f075105071143e000503400440c0d031102c03030004030601e40a000214141000040c11210001c4d0502a0005000201d01c07408035885c401044103112240c9000b880c1001000301840d2003c0d21a41920a4003400d40254895400c0700b9070f2120502c1118000c1c0c00c043e00a281d40d030310b9a800c000b019840105103070b03c1801071845401c0002d03081e001400141c113540d14040341c1c082151142614022100403071504640c401f00c0100402240821190150b0f40e2500d070114165840d203134180040c1c07003480e40410a41c400c204490911650780d40100001c98003480c007840c1c445580f039900d14169042800b0b42940301320720300c0080d074441020074482409288181804104000075400283c1031440844050b80810100c98514003086400d001001c0038010300d0404171030035414080826030203401898400b0078999a80082000c040c0f502088104c030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 83420882 1250 83419632 83419649
    0x4050702031201080d0e04060b0d02090307030b0403020105010311030a03080103021203120c0406110609071401110102180f01030c0203030604020a140c01020a1205060d260f130509040305070b060604 87
    0x1956554000f49543d011000f030a900024101d181081d101c7c600f034010b42040b504e400204604100441403220025801100c06030b50511402030f00000040244100d40d110754083e80001a26600d5810071b060303041c170848a2284260009000c0400090f0801c5280381503a0f0140c44101030a540400254550311038001080c2400d4010303020494082802002032040d10050f507a600082c031800c103e06a9940026607441600350062002800941c058445181d035024051508010b800d0007444814220391018400031503040392840c0308591805c0c0704183c5220500300b031030f0802c040c48180304000d49030b01010740500d218a4001a0300c00d01144194420b0040c290310240099840303c070405150b000390301c102058000b11354090726010844c0f1072441014899240600b51b2030240d080c2d80ea414445200441071100380000140e54066624140c00240c1070323400114100950f43c581042d00e101d0b0030116540520b01c0350b4084401c1000095008040d241102e61107018015991240c0000071494003d64019004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 83422132 1250 83420882 83420917
    0xb070f111207090e010e0304210302120316021c09030308060f0402030f19050714130b04060e0a2108030c090d0f0201080f0c0406050a0c02130902130e0c0405070203 72
    0x40700b030b5690703000011300c602500c000c01900418640e03d079102e0250b0b2194030008001108080c07c61803d40e40001c1c0403600c60301c10759181c00c0c0445604185500180c0380030031291b4a191070000120380411118086007101c00102d000c08203544401001c400c4d0328000241000801c80c040b6005840b414200040e05000034015900c91a01c40011000180c040301d0310004a50a4602c0b0500414030f4811180100042d54400c040d4186e021011036055000507082e02c040171281c0d0b00000c04800110103040642510b40e180c00c0da00700300400b008060100c5400940d41440023940c520b4040b881c080301c5603079490380407507007075142d03a179010f415110b90041c404c0090700048020b03d03400c1008400c1c00d5112440c0d2007600c0b61182600c900050700c9661104550346d160a900410007400010701400c040c01600419281010020140e40c1c04280c10506980b00c5244142d06d82d05c0520441c0340c001954034508001c104204101300ca40b20403103540300a00b80b101d0b402180e07074002080d805072003402154030026202c8804034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 83423382 1250 83422132 83422139
    0x706060902040b09150403050304050603060f031b03010c0815010c081e04030605010602150a05150307091a03161503140910180c0311011707050d060b070f111207 71
    0x449502c003100c62880380c9515945c100b0610b46040a56007900e03084402941014101001e0106c01da1002c1d041035440925191200385550b03080110030791440c0030401c8490120700705e41c245803d41e1010440a0709110040040000560403a83c41c43c3c5ca00d070302480c01c10790743c03d160304000002c5c0c07007001c555081410403411100302d11510b190041040700c2c40340b202082039070303070b10b90040341c540400281d82c5500700c46036030101c1d5603560560819074011104010100250280c100003d2406240b9845603201640740d07010141d0480321035081c4003201c0001c0d005802ea02644411000d02c0600c5402640c12038440c1440c0840c0303c45c400d900000e100110071880858078145149211350721100080601501818917002d1030408824800b270200c0960712007110f0022a0840c2c2ea404500100303071805504005080d4031490b40c02c020b4003403040c09490700b5105d282d40c4040505042c3c2c1580c1240e0042c0d10011800c001142c0003405105002500a4101e0010054240e00c07500140051440c002c581900740320300040071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 83424632 1250 83423382 83423399
    0x50c0d030606020d08010303121a040c020f010c0309031b150e010b0f150702041d060f0403020712080a0e010306030606180513050303040f03020c0603101805010f0b070606090204 78
    0x40d151240c003200c80100d00c8000851713840800340401000581e5580007003080d0105508840443c000e0030b201c0100a2040001080844100241c1000160301c035440c0c0180010080c42070322202540c51400340b180303a00c1510f0103040c010300f5023200c0722903102c01d40482051000c030150a000700101c50b0020311000c6103410202d4003814008030340c3c030702c0362209031410304182c0792191224949002004403d82050325a400308001000150b181c146411070940e00200300020620080344101007013100c40402d400d240c00c000746010030b02c1d00030260175800340c0300c0b0b03402080c40301054550714070507407070200101ca160b000101c1c043c2c0440c4e07000808035410004081000807030715003403040d0080901c500300b00713941c0d81ca0400c0307a5058800401a026400030400f180204a21600b038400440c007034011120303036011140101e005548101d075980041620340e01c080c080503140720005125804144824003080d410301c00c1e00c4100e0510303403056041a802c00a0304404005840c0c1004006040c030050442d102c69644103070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 83425882 1250 83424632 83424641
    0x70f03050405040c02060609150f060403060204030b010e130825030f0e04090210050a050717030a0f15091a0603010e0105030d0f090504050c0c0a032c01140703050c0d03 74
    0x1c01d84103078189013112215610026849104030304c020000c007101d403113003e80711018080c25200690044000c000c441e04581b100802013008501c20100160b55900d0360400060031203041c0c0200c8242c404500601142918404e05102c1607908000a19601c60a0700c0003808164400744e2965005c0c40c110a00005054000c0283e60a08810b0785070381c880c0c9071b40c000400c03003100c1801f44c0095000500b250a03000740392084010b01400c101608119107040180c2e16100e5412030f684146a078404000410044144914003a0800c082d54500042c040e82110090401c03006c0560700a40390301d1030b92104004622250b000000074a080c1c05003045999585440d0030814042c001d0040314040d204466a081d151480f401d0304807844440c1d9918241c5250801003040301a020140000000f0b840912011991040500c1020003240c465224800d0380440c0441c51505003859070105104448014403040031a41c0186400c1e00b59215200700d90f5451600f8501520b0750b00450342101854402c2d400c0610701c15070903500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 83427132 1250 83425882 83425889
    0x60903030b12150f0709052d0a03080306041505130209030c12060109321006030612110301021204120908010501230a03080a21020307020a0215070f030504 68
    0xc6012580b402d0b140c0e03003592860b1945406450a0700400022040d40405200c650803d51618240d1803260b43d6100103202041c111494071105210410100c0c10141c0e00741144440b910152034081d00079145446e5501180802045240a25203072001100f01c5240201a403026060040a00f030391081c0a41d010b900a40011100c18040c0c881d0f103402099a152a1140020440320340e00200301503800c24207d034020703090a48003400700f44189104040710740b201303c1c132811660388400100b00003032601c502c0d01e090441d615840001458a007001c10f1000c44035807211031404a401405c180b11107942007011a009120f950020030451a0340e0b000e200c1040411169001d400d8440d50b119010513071903061440c202c80080c400d100e48003103103140c2d40702001440391702240034a00080100440c96640c1e100c140c0a03500900306000010150405954010f084841032400384c1d608641c1141149000c42010303560703a49a100c0688503d49140c0b192545203030500c100c0c2d500366445003180d04c5c0325030b4618000c0c145821900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 83428382 1250 83427132 83427139
    0x30c050a1e06060914040f0303110d1a190611070e09010203090f0313050409080d05101502010b0325031202010b1003050412050a020102071a150603010b04031e060903030b 75
    0x180020712004502803c001c22140e240245d03d281c842c0e644104403016808401c070145030301e901e41440180051009801e8506800310081860501c0c0340d00031611200000302d0324401c2400c00c0c250548040071031100d80c240e80c054100002140c1c01500624035100e100d90101035038406803010441580c0c0190007450281e41701100315000f0909201c8913a45a000705c948000000e040281c00308803900d4980c01424465004a0320b03140b61084201d219416107030200c41003161070302130301d1013000505d0750aa078800c1b2070a2036100030020250031200003a11040640c1c5c2e0300521207003014200b842210b0a043c0701c0c00855000a07030b0480d48514020290180c140148500d02c80c0d150010030312421402802568862540904d8806043c40d014074244c8107500710b51040000c41d07600f8040900014600c03041c0602e00c0607900350900e0189001e0044191410b4038414550003090280010810008010180d40640e507000c1031250a424601c8601300e00010140c4010348040d003021813800516030103038005040d01c40c00b41e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 83429632 1250 83428382 83428391
    0x903070303291302041503060501020c0609131a060c0a03030c0509060a14130e04050d020f030301060305040807060f0f050c03010501120209031c0513080d0c030c050a1e06 75
    0xa49190304840012511002d07240605203121100e03141025880009100119005052036114107182d0640e1035200ea02e41e001c280c2c1d07841e06011540e0100070103a5865403c9902030315280d12140481c024440003003c031103003591241841c02d03806040301c0003031443d0b020290920b42c981500383e4145950320700201d03080c1d0200749480b00c40d0407103074855000c45400c0c49001d04843d1a00440040c212510140c0c11045100c0e08014001c424451243ca02900700030036034521525120f040508001d03081c4034400400382c1c00c1d035000f0155640e40d0302003c802d40e4111a264100083c00f42d031203080c116828410b0710b000a1226140c030301200c54045581e4080000e80503078035010441551400020360700c510081c090140800c6172140364000d0383c5069002070501e81c40240a5034082c858040c0c03150002c0c11030140d8440801d0004c0f844071400d50354070060000030207080000380880101c190300600303800b40c84c1e000a010405132000c0d04007842020840b43c031915501217403c10540010506291140201810483c0c071a42007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 83430882 1250 83429632 83429651
    0x120601031e0809090402010e0406082112040b070c0203030a17130201021009170a090303020d020304210f0507060504080c030615010305180102030109090b090f0d0320030903070303 79
    0x1040d181c1c02680c0d440364030203203031028050030841ea200703008004a0412426801d10800350300d5600a03c001041c4140c010500010f00140e42c42540405611300201c1e20030a20407042a1186030b441c441d0010b4102c000540b03643c440741c40c111065100f660010f501171100003481d2802d198800807600c040304920654283c0b6071124006602542d80c144000790060340080e0120603030350226485042d209115072241d440b0031269581c0d520b101c0c4c0100081e40081000a201002855010f0209109041361032020f5840e10303050102d8265145000c414104800e100e021002c410050f014106007145078110088411050f96007400415913481401000014010101005c1c020300300014024000d07140b070701c80307035030503241c0c1c480110300404004107503441a03003541d0080c4080440a00c02036010f0314a2603408159030005040039003035541c01400101e115400200840205c00d00401c0b6101503205030319000c43c84074056180705c009a0207804802d0313411030000090200100c2d00200400c01244a604d090028a02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 83432132 1250 83430882 83430923
    0x9070302010f1e0f0201090c080604030201060e0f01060804030c050f060402100c15020310050a0305060f1806060915100c060c030c140f1204140606030105011a030a060512060103 78
    0x30303d001a541010007080c1203542d80c42c001c00101000007550320000a0741e0a0b240c81c0e441681c0c0b0b941d07010380150f41194050006040e82801030801900718200119000e0411076002420a84140303d4642006420000b080406103d0600e41015603003200403125998450340b00395407541029941284280700800c080c20400d4060030801041700e8000c0ca180c44540f20304460100694030040c00752114400400d00442c455803000070f2007002d140a40024032080c50401101e12010502400180f240203181e04180e1620350002404d6a000605488124140c0c40712080c130302e41811202c034030544c810040640884501d07403144260240602030724041c0118560f006081c1c04031401c007000500040d10416284001c84003801c001c0002403040300d646072a00142607100e003952407090380c04a40000742043c41c40141c0e01c0c20030909401c882d003100200055454020740000309c7c01903004148103500040009042c003a80b075401400201006466507040c001140b44403500c841d80ad010480c0e5800e00d005100020a8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 83433382 1250 83432132 83432147
    0x40506161d0d0f0503040f08160f15030605040515090a020705120c07090c030902040b0306070909090512030112051b0f06031810060801200412170309070302010f 71
    0x10080c080c44100d9080071401d0250340c1e40000d40c141c4640b20350302c0800300040c0301000100010464a1000004c041c1451038140c10581c84811483c011003452000344000892030b41007004980c206142080d04401031b54081e00a00304a40c02164407a00c0c180c10082842002080d4020040b02120007801d2a81e50030b03d100100d0082540251441e44040c2c0d100513140c8242e80145200c00100b402ca58296035503100d14010b440029502c400040e03142c201d00d0046080c24000d00c84510021030180489107440c03080100741415501c120688c841d180d11101c010b019007444500c0401088002482d40c070342c2c51345500304402448410481d0a40304e001c1320000031240300e02003500e40c5003008000700b000c40c0340705042040070782010304041032050081407031000980040040c10200b06c0074801c081010740c80d204049084030f1000417100c03840400540240d40701d61014045800740c4a0078039a41030f20344070302e0400a0040c0d030441c5600c071205000100344114400c0010304441141d100341e80d200d41e01c440c0c03003404442e0035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 83434632 1250 83433382 83433407
    0x5010e090108030409050402030f0d0201060e0604091110050d1407080f0717041e030e1905030604080a050403020303030c07021306050108070309030e03070314010b030705060f0901021504050616 85
    0x360014001031000a000c0d0b01b01e26080f900007411140c5000c0818001810403000c55040710141c3c2d56084104494590500300c107501031405c8500b00102c005a0301c4d44001c010031740030300310701c5055076044a9501d45e0188041c1e0f43c00c4c1e0b500000810600784140d10034102074034240c8217000851480400540405081510540b186032960740e003c0b56a03520801c82059882c01502c01c072240b002d5102521410120031030380d4004075002e6030710f1841e00d041e00402d10420b901500900342c0c0c04405200b0500194400017607142d0026888007056958480800f022505806250402075142c0000800d100d0304540d070308094401140221b0b91040707000c0b951030062080b15802c3c410f090100d620500041ea5142c040c2d404007075814003d060130100001c4280000307085c0100d682044480201034025030165010911522407021001d0f00188041400c1000081c802d00039403003100320001c030000b620385072640b00b40038042c485030110b035604280d400d1620b030554440a085905135400c80b504078240040034030440c1d0f5040d04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 83435882 1250 83434632 83434649
    0x40f0c12060605281802040e090604060b01090501020d0809120a020a030e09010311090a0608030a050c01050f070c02091807090b030d08070905040e010209060c011d0d0207260106080705010e0901 85
    0xb8600440b480409400e07001741000107a0034400010b101c9800307407406104030a400c000d089549401d2400e4030807070380c05444d014100140c1c40d00c10302180e600018118445071050410b841c2c5580c1d0b6800451400100c0c1d0019031009c1c4002c190428038030340001d540c0c09124426100c11009103104010b00c8202c4009200143c82e4254042592409003000441e964024014040103d0a9070b200d869052856100040001c0080d00005100140c50b40a20030150825065402d0200c02e00788240000d0200a844101a2140b502940405c446456001c00550443c01c0e4a05840300196100e004c01e0003800b110040a0203401110000840d0302c1c400c90015100d088103848104d00141004144401402800308500300b0b0340d03003040f0710182d0b40d03540d0000d02240c007060b00010460041a045070281401084960000c03a03001c040039001d0f1980108504040d540c42c0800103500c50b601400c40000c0142218840c81c0551034201d010540e981d0100d420340640380c1c01e8807084402480801401041708003446a03070310 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 83437132 1250 83435882 83435959
    0x8180c01030203060105090414010603110903060c090a0314061e0f04060c02070b07060b0a0f0305060f0a060b07060c03050114010210090204020f0408060105100e09040f0c12060605 79
    0x20560003075000c0c0d60010810315000d4245400305010404444402400900368442500100a16903160244251405800034441d08221020f00401d0340d4050140141d8090b00010401020350b44611488100075038000036206540400d4291280d10342d9425039604c02010801006203030b4200644c42c1003809410701c41100c242d20780d42c6480d104010120820306000318007440c100040c140714444050b2059900800000441c40c00c410104003461030a17a2104c85c4814021604101241d404a070a96004484000940c2c44e42d0740c201034000100303420303002200c18900201e0003006011040c0c3c00980b24000c42c0d207080107240d80315001c0003d5812006803941c016844200c2926000451350001c650052002e400582000c01d01400b002e07154000b40c21501407980300c600100120310b00f070010f02410701030904101c09030340302c02c4001c99a00308000b00017a003109440d070341e10010031a9100d10f4200812002505032038100c0e0a00d4181c01400c6944035640c810000c1d458a0b040003002e80103003441c031401c03c6c0d04043c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 83438382 1250 83437132 83437153
    0x30703110c0c0f2d030d031e090c0b0403080c0607081023060304151a0109140312030a0f050c280302040801090c0303030c0c33060e070818 61
    0x7043e000d00110507034002d403100303540706640c0c10b08013480c00d1250110302c200414145400d00381440c00c60003010000405040c490034003802011a51100301044d0006408103400c001810044010341159110a50702c1c40001000824000c070400940f040c4056002a203030a40c0b5400710403529039009590760059248412810060a5051070f850000c0b280b40303002c2c0d034090f030224030006500c0d600101c03019641c841004141c030212100070f1141201800414048131075001a030340008103411603500a40e02d403010403a541b40000c1d0f400300000c2d001421a102c5941ea6441c064480e00040d0944c500c011100f641801c0100c5c010100c1181a500036840030400c454810000c2d0f0115502184860450b100b8103600f08008030300d055007801240c1500340540007168140c0c2c0355103802001c44218100302001c0010920054001400c803d2040b07140c000c1a2402c1c0c2060f42c030102d0b20041450740d4129010402d40f600e4800114109143c000030703c074002a49540005503100302080040080203c0714101031b400c18100c40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 83439632 1250 83438382 83438389
    0x30a05070c032a09020c070b0a1806120605030a0f0206091c03020105040b06300709020403140706050310051c0501090309080f0d0206060607020d17030703110c0c 71
    0x10a0928040e03041908201e50365100e00e900d9003000c4140f59090004400400007003030212403107a0040003040803c51a180c440c4070703a9625900c0311700030702c4450b00d00051191040d41c4115250802196002c00700c0180981e2503070064244000c4050055900e0700709080041d1074a030210f0404552a0401005032514101e5820048590301c51b4416a610410b030721040c0c41c125441e01c0c2e00c108440e110f5000090309081c68148104036240061030076104021141c000401c0480284841d94020504c00515030340c900b0300c1d210641042030641100704910f1000c41d0000902c030310182004005511401945d41c140e845032800c0310305110072150031040900082d820852400c146ca15404100480c15055442400503501c031400d40f1004103050b030000e0741d248010700600c14180203114143c002d24005002c013206100d030194a40c02e00a150034404c100c04039055042d5120071598004190344030a0104007075000d141070078800e410554200c00040d14040f05050a80e84010442c4e102c00e0000c4010409544032a082 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 83440882 1250 83439632 83439637
    0x31b0402030c070b040305090f0409080a0c0302030405040923060106050708090f1c0605151e1c0510050105040204053f0703031101020f03010e0a060b0307091403010905030a05 77
    0x110032a0b0008010318004540c000000d1801507109136101c079500d00c407890420410002c440c946c280b04038945410040007c481d582201c2e0303901d11600b0924290700c11810140d0450140b27901080d041030405110504100b141459120580c50280d96801d855240e00c400e0717035440c00c090080d400800c1c03040102c440400c200c1d1015296020000340817416241c103141c0824188000d0310215031090315800c121008100d400e01030258040b40341107030801001040000118072800060300c01d106000300c0b042d903811340d84034022600c02a444100303c19203507101c10724040d070392165401c0c00030140f103240c500007081518040c02120200c40c0000c1a01c06041540c1b01740808064000908450ba10104041168140d0320805018001c91901002d802c00078078504001e0004180c1411148990f48100b200350040410f20003503c3c1519408a01a201a80c1d04041c0e000149a55040f0b51050580801005916a07020744400103650803460340320032a40040040c1820b890000100602581040c04080b02c5244078001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 83442132 1250 83440882 83440891
    0x21509070b031f030204020418230601030c09080616020d08040503040b09061c021e0306030615031e010f11090a03150b060c011d0a0317040201050c0f0606040b031b040203 75
    0xd0032804196241c1c000790407644540e0010b01004480d05901148203460b216055040e41c102d4ac1c81c00304040c0e03180c0c1c041c28030000208124185544c0c0c90441c0e210b14400c1904d4000341c03103000c00725202030030210720142000b448500c0720320044c03203000c20705c506c5581704460690045078040003c0d800d25090146518103a080340312801c0d000380050000c2e020450040320b04203640c940703034140140c1e40c07100c0702c2c10200d4502c02040c254800d07032020014041161070010300c403a0300120b403401c1e44081000002c0068100041681c40305c4100340001c50070b40071040194004c01d00c0c021080420407155040e419054054000c1c030310010f62028911100304041801040c00c204034011417180000c507180c0b1030001905a4004d074071044101c2c0e43d2024371507a101d40c0c181e100c1740b118074403400130064400c640e50001c02d07480b01e005601202e00021004642103902036025034402c0b44160007915030f00e1892064282d5a003404547e01032140303080c14030342c8109080c0441c0d02103140b00c4500c02d05406403000c4081c0700c0a98030180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 83443382 1250 83442132 83442181
    0x501210f11031006030629042304030801051903050307031103090d060e0607050309060411010201020909040623160c141203070e06040b0306010309140d021509070b03 73
    0x1c0104426a03400e000d0306414481014002070304030b0039810305204481240301c8580c2294001441e08058501d4241404901e031812600454540d4a21040c41d11409980490700030246030b486c2444200340c1c01808032810703034070242c415042400900e580ca0170b405501d0b1002500301e0b04100584000b09220705a4440019503c0c81101d14029440b004203480140c0d158040c0c50a550b034440b00c402c8a030042c080740f50010141e1402c80e003542848000345d034840001a00c024405001940303620440d9000390181c13081e14500506410307491410742030090203084d0041d500a803540084034540f0600c2000b83d00a070183d90400c41c0d1582c1d40d00310b800160350011080c0d405481260283c842c5403107042c404c108050101e000d51600760b8403420300c00c801624201c080100e90f442007409120a000e480f1103401a02c1c3d01c044d0034a00460018003505000904d4000e408640e042d41c010050328050342500000e40b04045c00a002d00c00209607107002c421500c1d922140200c0b0307030b249402c101142203c8500001c40000c0078420 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 83444632 1250 83443382 83443403
    0x60609042403030908030a02030405010c05070b070c030201110d020d210501080102193002070506090d11010b09010e0c04090213051815120705090405010f0501210f 72
    0xc6010312054034401c4600502454005014001c066011034403600804000d8002d500340302d05030802030348a025238003526041048410002d0103001c400c01041004240d140000c0e0313070710559070038a141039121502051b400b048034842103900c035800000c1c0c80d001d545480e40c060000c451440108642e45038040b4840116020070b281070802541c09881107a008002880006903502c0340c0101044001089001180900c68040803c107400c2c03034001a100c00c4040c0c4a10b84010142c1043c41000c000d0066420180640c03050b6020001510f00010340184620b031075844100b52000b05448a500761a5103105050300075080000400c208015016540e410540c141c41c80350070143c0345d14031241207800103011200c4148001c01c0410840c02c2005c0f4421704c41c8403903070790200b0902c3c04401a04812041c03510150152161206000c04e00405100c61300280034002d00070690380c00d060815601800100c8a0301c01032504d0480002942e61611100e07040d0ba091b050750301420f6000a4a9000c10841415001d5401d140d66 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 83445882 1250 83444632 83444651
    0x170f040212031210030219030b010623070b010303030b060403080f0d1803021609050408090f040e0304060c020a1202010801030b070507060509030d0507050a09050d020a0909030c0b0702010b0906060904 88
    0x10400d803180b060f1138008011010600d140100450341c10000c03c07103480c00b02e41c81021710220b607403c9441c41c151000f5041281c14800b52514002010341c07154000784071404042041c0f0304101281448504a90181c0e03024400c00c0c5441c01000f15503c130758840241900001c000c004641c110020151000d0703e1407000000d050104242c0c6034141c801c00c00e5084005070002034103090130483c41441440586030324082081141b0303055840744403e100f9000b81900c1a29010b4600a003503489070401c440303403209541070325101ca60b216800307482e5040d5410224800c0030904804115400c85008106059805940e154032a0346507489020b5a0100070300000c2c00c110042003c600401d40c9400352074002c0c1c440c80000c6550f41354007021141119800742c820410401d0402500480540c007c2400090301e41c01c42c3c0d51061548140b002541000302a440000c4ca1030805281506041d081001d9181d014001c01c40415956104d410890807244c1e142d10244d8003041401c046001801c1440107040712410107840050400783c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 83447132 1250 83445882 83445907
    0xf06130b0a0204033003050606030a0513050f07080105011502060408160b0c0c1b0f01050d060e070207030203120715050901090f080309011a0a0306020f19030c170f04021203 76
    0x85e10030109407480408400040803c040130f200003c1c140b03840c0c1000241130003c0028003510005e018009003580f0307440440c2d600d00d00a03c6c1004a070350701c41c0488242d040441c026945034011031280483c0d0f5440c00f400060003410402c0001701c032544641c00b400960740c850b92015200c0e00b0942d056a440c15074411103500042400306454010100702d404507444180e81c005291a00302d81070320407225840d6a90381400507071100b00d0750a0003a1400d017040da44034a680c40300b840c02446140d10a490f075103070322428800d040b5004030741c40c2c051382c0c0298180c96040c0f01d8451042540e1246100080000c94403c0d02540000c10903801690480302c0480049914056600d40004501880800f90388000300041404000b18003413040401c0307a1504030100444044200c0001e40c04c81003480054542d6400090306400d82c0101c00c200c5900e9521300031401800d40a40340020001c294166203030f00865030f021b104ad040d038600c56840342e03c1105a910140314a980d5542030100d955156000e0002c030344018000043d5404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 83448382 1250 83447132 83447153
    0x2010c0f0509300703030302180d0f0b1905040c030212030403080a12060b07050c041a0904080903010204030515040312050c0304150b1003020309010501050907080f090703140f0f06130b0a020403 85
    0x60090360003584031910000c0d22400d0031a5010301600c5103082c0020940002c03544419900d80a8002c00d22104d14de07903580c0160410500307403015440c018500802c02081080c1814010300703036030003900e54241d500d1031035106959911540c00050705000d020b22070030038130520950000750005405400441c0e011340e129030306015500410710494454204c0c20500c002403d140c49170302040c00c9003070224a011405070000c81c015070406030014000d16070009641c0380e03544003501280d00441e40320701115900501c0e041002e00b030201c1070340c086000030b0450885001e41b40e01030203214011071442d00701c4d0740b41d903c0e159911543c0002d8001c021901075118020504640d0311880701414451903910056030700c0c9040400c8508641058020341d00c01c0d04001c0034400042d50080c16a64406801c016400c4107440d441441ca01e03201d0300c1c2e400104040c4c040a0040c01250740855040007544141d02142d04500352030040580300c0d0800c45100b241c8048501030750700440c03260401150802c4005000526040e1640c41700200c41 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 83449632 1250 83448382 83448389
    0x510050c030f040c0b19020606100507020d080903060408030f070305040b0f0a06030b0903130906030302070506030a020f0301030812090106050102030d1d0615030601060804030816050c010c02010c0f05093007 91
    0x25100c404212800a805003d42070380104200c1e122b030680b01c0320b2030001d4410700480201a00820040d61000c1c00c000608d0105c451500008040300c01a1500d450f007078000350b0003107904c1140f02d2045030200e074105020740990f0b4020365000391840ba150350b505203544100400240b8541e03c0a490b0a0000041000042c1103401000050041d5585200d8824a05600c84c0c5039400313280d10914020302000400d9020903000207076a01110322550301d88a80e00300b01e02034044c00725415403e9000000000800060070000c0c50380843c620506103ca9403580340603800c9a00900c03a080c00358100700100210000f11741d02001003804c8040700c3c0940c006409121030710346141203920b10700c400300c012050202e6107800c2000c0360040203a840c0c11a01460940e8004103021400b4092038110701102c0384135500a40110292030107892514001c100003c0380c0700e80203002c1c1c43c070a510b24011420307030081781c1c005c18851403c99006141c003401001c0c031941c4200a00101c2484015156072a44c07105050f806006030500016004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 83450882 1250 83449632 83449657
    0x1a04050406051e010f09020c031b03041d060112050901090b0907050114160213020f070308040c0807061e090816060305180c280e040510050c030f040c0b 67
    0x30f840c003070b2030b00004100d40e05201030f6102d03a0300004012407811200b5030700980c0c3c0e580300c0150f00d400980e0141844d40c0180940940d02114400084504003400009481150856401e54200b170944450144400c0300507501e00b40024068074004840a51070b0700a19000400c5a0000449130310989820200e11010b5890304825004442c0402580d1f80c024401c8607050303412410782d07152903000550761074a458603031002402003030a01e2070b6100c080c901358141c1d04000414010303a661100646001006464120703401c6030825010000820100c0300003402c001030303d810740c503200c1400100881200d0301c500c54800c0e07841003281c004804116200140080008020400c1c40c4a0945041c2840901513030401800d0800f0704c840314001482a010014400b00694803e8950b1103800484940f80c00c140c112603944507040d6080580c00007244007400340380303901c524042c0b019a80c90382c581d0181703913042d0b50080d9116030310000213201152414002c1041c40e90802d04c0f030b00c1e4000400e5034441000d9840d07002314030780c1542d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 83452132 1250 83450882 83450891
    0x30506120f010203062817070f12020a090e190602040308160302010c0212090103020703030b1f14030411060c0f120702040b0a0602030a050d090204020c210f030403031a04050406 78
    0x405081c4004503403508559807003a0140b030410b005214100c40c1b90381c810a965103101c80281100c44c8400c0c031070900035100f104c1840742c0490710756421340e0f44030b14540022402180030710fa00250a116501c5989000c0c0e60460281c1180541d00d104071011101c2500141c40b010341c20480000050600c00051190f0f480005104601016038100a8211a109500d40c0203642250b101c950b03400d5850800c48034008024200180c8800c1c541c00d00b1002010f02809003074008030741106d4004280c454440082c03c1402c169038500c4517021060401c2c440e030005940080c950030078000d00c41c1d41c0c0e1401c0da01402d03041020501b19100511003840503481c04000c80410403514100042070002c0d400c1c02d0240e80300440c0203a4600c0750092400c04000d65901c143c09030f60081150100d6449241201a000215060b030004c0c029034030390880c403081c9900c803a044000c190180700ca551801010303e407040141c91072407000b40c1805086a032591401d0b8041c15210010903200d2007061012012a03840d0303c902405075001d40800203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 83453238 1106 83452132 83452141
    0x30801171b060307230306040f02040b0a14130906170a020907080604140f0a05060d0c0603020d020706020c01050702071202031b03030c1209031606020c01030506120f010203 76
    0x7010400000e50743c0251700c41200514041c940423034040190306110352039a800c030b10852013400101e1405000c8203405902034010b21569510041c0340a02d8007866043d100002c40031074100314030f81c80d41c0d52000c2c0860740014085000b5080f9000091104016a400081c00000020b00d40000c100b0032000044203901d458100f80310700061441444032504100d040e4011421045822000c164070f0400020124506440d4403040a50025000c4035910f0410b02c04801030741c002c001c00740c403a0340c0804c070f000e0010305544011702100c82d00307100004e000e0030400002170070714090354000c102d1540600150805660040781104590060800c030b90106884100031a00358020910340300d009000c0d080d40c0c0421102140014880418105c09403800c000e54012000c030100554050000141d001d0f2915046a50207a4040d41c0c002d000240821300f00c1c1c44c01c03802075180c070100d07040320b801a94003c001d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 83273382 83453238 := by
  have h0 := BRFrame.cov_init 83273382
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83273382 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 83273382 ≤ n) (h2 : n < 83453238) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
