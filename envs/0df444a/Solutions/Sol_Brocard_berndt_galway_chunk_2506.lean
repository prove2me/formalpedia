-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2506
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:55:08.149995+00:00
-- url     : https://prove2.me/submissions/f2a5a352-8688-448c-951d-905e2d94669a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 450539568 ≤ n < 450719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 450540818 1250 450539568 450539581
    0x1d0708121c0f14070906090b1210030c1e0b0403080f0318030a0c0b0f0103030206180a0b01080a0c1a0a03023709081506011808012c0a02031203 63
    0x180031041c51840100b410f0040703c046400311140072600407281500c0d00007589507039030010380d40401c040c030a40310042824031a10803603071110030902c2ea110551000b1740181a44a554618050049411035002020324249074980e14507a02003000240c22841441030400386075696908040c4580101111001800f0020803149a0328405100c2d1a46002003540d0300c0d104100c100900c20114403005940018818001c035143c5041200024141e03034059000c0c2a4550b90014400400c143d02d604040c0e482c0304030803c6001103407900baa5070303001c5c01107080a81aa0002030820300300510051304a003181c603400e034a50614401c07426003121030914203801d0243e00d400d4401c224850380d200030581d000301004040c1c501c10000d2040d03a40500d0014694403400000da0310f801c3d155694601482c0c25070790a40844010030299800766106080c2d502e044d06855a00347d07240d080c600e003518192107610aa00540320305680d42450300f9000013511002c150000c207000c421a0300001d5660b0403004516000c0c90300080071450 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 450542068 1250 450540818 450540821
    0x51c0503070606030515071d09090f0703060c02010e0d0210051012030201050a0f0216110604080d03020307230d0b060c01021204050d030509060a0e030d1d0708121c 72
    0x1d141e421200c2040203950740e04049484401404211401c0183c0c000019402400b1707003003004103003802000c515104062a01800b45004020700072036050312800c0c00400c0030000030410800514464180840c1c000c0c86086d000e400e4910f813803250300094000520301030201d640010615042d0300c000c6004150390b2180129130890004070b8003c0701d84507503080d658600307240d01500454016600f0510400c8a250883c0845040b03014204800c00c0707821191074643c011500ea15108080040300404982c9026903a42400d850180247d203d000844d80100c2040b60164101058000c01502460182c101c00c10070000c05c030307240c80356480450506d0f0340c1e00031a052a850300015582c003034800000071991f980e030695001a10f420101c4045519124a49940c80414801c2c040c4038051880b05005003400d880380c00008015080c00d00070742860b444180015094580740340107035520a5004007010700c14680c01824181454040e4000f400980d1003408440c0f040c0240c0011119031900814520500e10b205280090 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 450543318 1250 450542068 450542077
    0x20f1b06070204020c010b18090d03020318030a090311180703020315060d090c1e0b030702030c0109030e181603020706140a1b09030b072a120e040204051c0503 70
    0xd41291011984240b14103056101008141f0101c0d2200d420304110007500100405c22240705005800c0b100c501200e040c000c1d009180c01c10030145900c0b044459010f84545540c003e00510000030b00720000800600940241060b00c0c218280c1b102d145008412007540361000c0c0103005401050350000008941c0d840c00b11001034100802001ca80c2d44200d0312024102400c00c1c050256100b034a00c0d40b00003100c00e00c91000c0c01e01b203c545160b21459614282100505800040912065003c10005405010300a220f180304551180e103c6950411503031040c0800ba1039501440c203065100c0030207000c024564041c06c03804862a9180242c0d0b610014500340003d048140541c0e41c905464100b0b001808c4215040728100070080200b4014510982c1c208541c403503800e1202070100c950078404201c00d180310301c00310b10012500004242e014001c500e04203414a0780b40c6019200714506180d030502180c0c2c07000c001c0040304811101035081a0410000500b00b581081c1c0080c0c060341102d880304100001070094a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 450544568 1250 450543318 450543323
    0x71707210c02070503120415200307050d0e0103020903150703090803010b09010e0306070905150702100c03030506031b040c02070f0902090a0e072721060b01020f1b0607 74
    0x244420784030100060368611180c0035142c40b80c007600007050329103c1060150b0b0120740350011040410a180d40055513032540c04084228480480070184120724401c0000305072242c0716030000e141d0361448900003054841d031281c000d8101401000003c400391760001e11600240c40303407003110803151900c0005900605844500400c05c1002000009844e030049015003d8034100381c8400d4071111661003010b445900c01c172011000f003440d4500c00c1c03089040c04143e801141e000300d10903d10341251900020b010f80400c80300d010016221241007010103915014070360f0001400e800600d5002400480c104150000180c6907000d1503441c2c016410b014420040c840041c0340020006401a441e1440c0001a46c4840d02050142207105400500041d402c40850303c1071213207030b4920200d031003441061388a02d05a983c040340d20760900f00021824800c0c0080c11036412140580e14680070b100e920301141520100c1c54071a0554000a0845944440c01300e02e020b0071705280107400180b2046a03000902034004d82c00003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 450545818 1250 450544568 450544571
    0x6011803060905070b0a090603020f040504062303061303030209190602062e1e09050a0603140a02030d0f14120403020c030a020f010c06021c1407170721 67
    0x800d0041d6a030149409a0080d800d0300c241e1512102c5402580c0f15202e001000210701369010001a8481d40c060840b030b0050201e0030b0318140e61000003c080c0c90498011740110201e00c8140481c81d58000060075500f1425000303000b20385440140c00c0c03071500d809800501410340000b4010059a210700b9103540e0305510702164001181c460034004d40d1203000b11940480b910031462081402a41603410308962141d080c50b054115003030240d80c400003011003038001d0700c4201241e004140c0ca0a41d000709882410b4000c400559189903049c400d0f50040b82600ca030803107800080011001d43c40201e041c040c2c4540d00d003020580c1140d000310482e030210352585200001000031404099110908008074081c5020340d00b12424a903060003050b031076143c80a4000c1d44143c81700780c0e28216500410a001c000c0d40921801030800c8019103042d060401c0c0c008040c00300d1503581d600070343c900c001040700c0380e001900c9250039240301ca00710030f0700c008032040a4541014088091204031002101810700510145031410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 450547068 1250 450545818 450545867
    0x50a091e050106020715020703120e01050d0c050d0c08040b0105040b12100209041d060103032f0106081903080a200a080103020a060f020703060209041107121407050d080601 76
    0x400075160305c0030b40141c4071080101d00d41d0000300b62000a2100513240c2010004112070b600800580e8400d01c1e40d145a4140107003400141001103c0d440350701c04440050700c0d4240d640c0c0b0044441780844480f040030b5400d012480d014000030810f00b48080303056030000c0d107000425120f5a000251013030210361f4403050500c10445803018114568016140145040e9004c1c02484503802c69603150301c8034a044500e00e5400b0340c0040011a109454519040425164031041c2c244041c3c501d5550b00480040207074517039122042004502c4040140707601c21003012006a8200300566401806203c01800452010344c0b11050341c0341e20707542600c91900c280e1400551554034400400d014208041c02d20042c1d201c1c002c1a04005400e40c01080f82100500e425405444400c0c00c41e5280802500840300345071700203599242840740c00c0c009900500490780604403c03101d440c01008000c2c40c2c0d500b00808080c2d1301c0400c4c81031a000400c0050000c0e034a80c502d05200070320b07548001c0122598840110a94100052000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 450548318 1250 450547068 450547079
    0x20904081305040c050901200706021f0203070f11070e01030f05010b0406210c0803031906080d0f0f020c090c0a0905090c12090f010603060222050a091e0501 69
    0x40180005011421414880740c0c1d140104070032140418150400306004001d9080f15621500b200c120072002041a4850803403454195443c0c40050340140d40075900c45103488014282d0105c1428195900400552440c40c000100a02c50604070040c181407024443c02641e00010900c0403038081c0c814003204041542e9a4101907949002c1084207850f0b0b54038000070000d25003494020348081d6481400c901490041134484440c2000ea010340640e040e0a0b051808104041d00340011809000a0306503126403c5140700001c007120780a07030040700c0942c4000720400040d078100408020b010341c0340c14100902280310320168240340030303400c82550000702d2008105d0501e0700c0e840501407402c07491f617400c000780782c640050100c1240143c820390304520090015250106640d88420b52002244e001c1d02e0080381303070320405401e68469400840b14580c010511118883c0f0095030a010201e4000751504802d2a00001c103001c800d541c000c5000d21521001c940110b00110410020103850f2004200481e42e95070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 450549568 1250 450548318 450548333
    0xc0105150103151413020904020d0207031b0b01090515151c051014061b01050703050601020309090a05130c0e0f1315270b06010905010207140d050307020904 69
    0x15411034040380c903010b01c1c450340c8683c85114106607100a5982e401002201013000107070009601003000c4640c00b08400c0c103440d2100c0c0040c12062844640151702c0e444103107005010200b802030080e140300f202d400300c100406d542c824010704444090b4400140703911180400c0c0d0340a022094015008046840c0c0c0b02c0401a040b40101300c50980c0b5090403808030425010705003500c00641c0d55828001c01c204050000c15141d4000e6075074244001d00b214030b0480150f400d1001003019140c26404c5035912010003854640600815a2190b003d10181d460943c4070400074595110240600d2809a07a50b8000b692080842411805071504101c4001d02c240d0340360005104001e00f100c1c079005201c03202002c9055600045a46500654018140c040000318070089000810441c100180004030245080c5400741d100c0a0902da824003034208442e0619100f8005008580c2a0b84500e04640c04508104004a19586a0440380ca801c03504002d42c041c03d030a026286014652002c1d600c0080d0311f05220410180303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 450550818 1250 450549568 450549601
    0x1b020a0504140115020c06071403070c06030213050909100b0102010b12101d0a17120903190f05040e060d0503130801060506090d120c060203010b0c0105250c05030c0105 74
    0x4c0900b003415040e0f040c50101c3c0c442e034980701e00c141c116405110780b40009818003280f1080d80005c900704c0b41400c0c1503480fa1024a1003e62204001c26030000d847c40700301004041c46405460700f41c51902d010b040880129644d500060000400560b6494101125030b20079006070403020300040500c00340e02c2040c1145500e4920b000301042484d4640b01e03034101d94500a00c00c001d100302a100141c8011031481e160b90001c640c4580b14070092803000c000e0802041d1450b50b0407070144009c8401191541b60303d440040300a642c2c14208030038080f5003030300ca1b40c1303003a031140c100d805980144403421016104e100c00709400c1e105201008080e40004a402d10b03201a840d1a00c0d011100c411000f806420382d1002480400d2062480d1503420507a003d4841c400b181d41610011094030746840d0120f81c250807038507034030126042078002c103100d2440000e1022199100b4060f40350081c000c41d103038400c01e9201190035442c1e80d001d007000d0000e200401030341c0c8050020a0040e50005110f034802400245000d5040560301500e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 450552068 1250 450550818 450550829
    0x90c0503010303030b220b0a23010c050c190329152d01201b030c100e1908070312170709050a0e071709070305031818071b020a05041401 60
    0x80c600002400391102007030204e8501200051566a5403102c01102c1c044120b010907201c500c556403400e00252220b05030ec9002c1810328114040040c00d41c45c1c00c648042c01408520b50008403d00745d42d008082069000390054402200703107100c1511000851400250112400060301440b54a180c041042c0b45020341aa070090761098400710b90459090348003c540b113001c880c554001e02c1d555428903003420f205911201d0084c1100c400c0180000042d80d012502031030900042e602e460004c0880c2081d91450115045811048a60764103101805640340010301c0090030703110100c006408240d0040c01954414294014950001e14200901905c182020310a43c0d000e035130b80ba00c001492046401c4500d016201c1c5070703524a40c40c010328034803071910700010300040068000d0080020002c0e50410080050034142e00381480310207500810460403610601416225200d18404c204044c0d40c001d0303406a22041114051580703441d140003003034000d14207810890f04039150101200624818001c018101c46 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 450553318 1250 450552068 450552079
    0x20306090106050a0e01031a1f02010501080703050a060b06090d05010e1009080901031505041a0f0a06170705160b0415200c0109061e06090c0503010303030b220b 71
    0x90742d80b0b100b2a0383d4403842c11200c1c0000c054420203e81903119401411000c04546d11811303c15020350001000001419100c0050340184a100720782690203004590040201e68040d000e541d26644a540d2119003510740280150b985181d000030a82e00c0320141d6140b1b40001c0c100040c10b08540c503045008201d03080f40b40000d882400340e0341009524a0080c4100e80740d00815107030070329164070019406010a0b102d6264640300c00f940203d5151100d1140c012001c0004003000700c80400c81c02030080c81e06898518a00031070281c03100740f0145400040902e000d81c14500d10007103ea4551108072118003036440c10383e0b0443d12903d0f4240500c19003007206400703103010f02202c0c40b42c61240724509040b200308503408400b11030040c108507107440801d4080e1141240503000454080e98a94070f40045648640c00c031518030302d0200d000542042c15104040c080c00000b2400c02001e550004080d0050005101c018105038a4400001d06901d40035000c41080f11180943d840c900c4480d00700c000a4041c0301b58940c05032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 450554568 1250 450553318 450553321
    0x103050f0114190203041104111e04030807170d140a050a0504020901090b01020118051f0e15060d05120405121c0f090807080c12150a020901020f01060902030609 71
    0x1c078034852401581c610030700c5146440c12100110103500b00400c182e9074440d0000421038103403502c2c0500c4031400050342482b5501c045080320710b50b210342038080ba0180c41a01b44014400a00044116500355402011030a0041038a418400540c45030811046031241844d403149006448025100e000391081d100510003a55503884400032a8021036000c2d42c06921840108080161644042c0c16a40184008188105034051a25030703030f543c00d007007180c481d4441d82c2c000348a0668401d10320034490b28210107001040310341ca0302c2952044c00500c031180440410001c0380031a6200f00515605c00d9109060701c1010b10200311201c1d140d001481800d01521004018030203000010407804041c05d0840c803a4914081c0a644c11541101f403582c41d90103001d507400022804000070070001c0014000340e00281002c01d0207406100d900c54208140150760343c0031440c4030020107100114140d020810040c0140c655010800403480c0031602c140c81d8071344c0e501c0d00c2404680c0d00400d030010341c4034003415100404072303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 450555818 1250 450554568 450554591
    0x40e0f07020c0a03080f070c0e040209131109101d150d0b01030f0201050408100623031e100617010c05070c0902030a09020a0b07060b03060702070611030408060103050f01 75
    0x190040c000140750b02c0341042c0b1042c000100c2c41c00290180300b030355400c41800c102c47c3d40d5a815203c0c40b690440c0d0a0802c0c40e404100440c90101c1201d80e10460504000e06604c18a9030703003140351085082e46521500307400c1c002802c540904c40e114801806c400c0704510100710320142c0d200000b2801d9600c03500345c20900307060108604200c00704190055110304000d503581e2860701d44605880400034100e041147c20440010340e03010400104861000c20500016920702d0070315070300b8540680c503084e11100d0745d40e0b01e880c644640d03020860071110300c0900c0c999802c0911202d2524280641c03404c000b070b1003d24007500828013809080718035070661302c1c000082150702c40200c0c003036405004117000249159007801080c049090740b500a59005011402d01041c24801540016103155075a000b100b056140030400500340100c600032034a1500e0b06501414041c100050005e4544c1c12900500c028400c0403070f40c44a101104000300c400400c0d80390b0030b560aa5859180040d1204c0c10158007480c81e60034503080e01d45 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 450557068 1250 450555818 450555823
    0x207320d0507030e0a030609150501090b10030507030e0106090905060907150c062007210504050f190b070b0106050307020c0d050a0c03061d01060302060d021e040e0f0702 75
    0x402800c191119070400e009543c1c2120b030036080240c00d64100c1c9010400000103a60b9006801e0010b204003450005003120b01d808100b00ca205078000d007012070402810070b04d81d4032072202c01c42840841d45004515647d42282c00d4025090310000c50142e58030b0034000084011466010541c1c0314030500a0791307501d03180d1920303e542d244818042c550000755083c80da0000c10740039500300030030244200000324a080800c1d107454800038000005503440b4000003405400c1148a40c5003440005041030304080c40c00361040000c08a00a80c01014060035a62442c003c0780c1d0355203400350260a1564000c107038030b99120084507600d50400740301296807036200d600110341540124140d13442103200e13030b0051000d1440b40741001102c81141c0d005a0b95801840d40c0e41c400300700c555a005014600600d8007140707486600c982c0e0401c00c122040c00e9a460b914005040c40140c0c0d0b0340c0210f50f02c500080c1c201517110a421600080c68068400100b2540940051f0024041580000552041d05800c082084076940d41c0030598 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 450558318 1250 450557068 450557083
    0x130b030d0509090f190c0e10020d02120a05040503160e070c120f031e05150a06090314120705010c170c160519061509021c0b04020732 59
    0x36480045040084c5180f01005050703035201007403000110300c0041242d43c010446011a4406002640280d02840c080c201171100c004c014940b8402001c0d500010f04000351510a089446641108009049102c45108809035000340c0310050981d0703da00e03282c519151a42d0894840c0c100340c0c0322040c002406803801189600015038204141079200034148000700d8002501c030501d8002c2c0340c0d96003815203072092803503250a043c049030780340000d0300d050906000041140c1100303071030b114400c400d5052083d994441c0300801287c0d841240c1c82c2d10380d4150b80070181480f0300b6600c0f800e485000030545000388001504a16020400c41e2108660043c01d807445820b1440c044a00740640c200c200022400310060b908040c40c00d0340200305498010440380b20b0840003003d00e04d0700343c40e15a2141c0380e41640d4214180e8400c020b15005008601d01981ca140380d42e0188806001c050409a44a850300207613219901180d480d03e901c003644120284020641415842052504d180201100c9221440c0d0f85e9000400c0f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 450559568 1250 450558318 450558337
    0x1140906061e1303050a05161401050c1002070309180506010c140c03160815222103020408010507020c09060d020a030f030c15020301060e0d02040b130b030d05 70
    0x1034644424407a04480e400700d021008500c480e8100501080f64021028090145115401400d0015180e041841c038040a201c508003405807800d20030089140313001e0820000200a081036a1141c02215000d8204900000d110507060f0001541c5001c060303100383e8103015540d02c40c0c2c250051030030104400040701e00c112a03c50126186881c5d04012503d9206203031400d4008404654a800c02c200109040411040c3c1e01c0b140004200400e101c440e0f0140b101c2d840113600788424188a00d040c8074041d100554010000c0ba0001050240c84144260001564458000700f2034040883d11600c900400940c0984200c000d503520300310209402910200d2600d4a444000340220038544640d0100041075038900012070b88142101030000003d07004069a0b200e841c003a458036000c0e5a0281400403a400d554030800700f1441c4100014004070340c00200d030620220b0261803090007081c041c40418000c001c0705850591000290320340030440740040e042604114025005d450b00035014a10560b0076000d61a40c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 450560818 1250 450559568 450559579
    0x50a061e0e10020706390302071211070308040b03220c0501080c0c07030812090706021f0e0f0120120a0507020a020d0807020307050a0b031501121401140906 69
    0x1c0007802d0840c3e401130105940103542c001002000300745500c1c0d95803003041450100041d24540c1c000c3c0b100c140c8449480006250400703501d4010140d850300c40008500b4080301c18041c036a0030903904018204035010185d03070700c88181c83e902c035181c107000006074008640700140c1c811034015941a071100c8440403400c0300e5010100c281014140740054464010062520003841e00a1280000f803003820400da500a40c040d415541e6640f03040101101083c00c01041c00c4040c4c2e001c180c0412030181e0004407460000c008500f22581100c1c0c0c0a95100a0104a1014061b80c460491b20681011065101340e80c0a8084403d58001801c0309003006071790b0049070303000c46801000c500014801d014981019501040c4e901c1500c60003500740d0700041c0170009000064074030394008201142181000c10001024000454103400740c24903150988003140b100407e00400002d46101c040600d034012141050004001130341404201c03c400802c4458000c248204a414003075038820600300c2c2070040015003c0d10000c1d02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 450562068 1250 450560818 450560833
    0x170724060803120601050d090303050109060506040e0708070219080a0206090c030d03111620030a080d0e01060b03010b0711061303033c0206090c0a06030b0a03050a061e0e 75
    0x79201c3d040c035401800035041c13180801074600d541c411351151400140c0300e80c03000540c55040079041d40840b041c07a005940580d50030001030181c0204e140545500030708a28010344140e5a1310012402e103405032008600f81c0d225a01803004221401c030160030300046503421035040e42e84042d65255100c1c2d03087c0b01c1c4d90b00f6800440c8140a800c2c030a8004103aa40091200503240c82c802c44107848001000100545100b6640240f40180058054040f440054120008d1100c60303030540b80c28945108030b580c1420030319501c0300151048070f002c5d00240014080d040c0d81a440390303520507542c005503205100c105c460718038000001c140c6103040029105008a440d840b404074906507981070350403102414503010103820789100443d6a00341c0c900e40710120009440c00904850b09068043d142c660048c3c9143c41681103044903801d95142d1030071200844019241c00328100150b9004102003c005402c05403560107254811000e010b502d42045c003a11070001546603050080c4015007044030a0446d080c01250071404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 450563318 1250 450562068 450562087
    0x180f060609010504030b0f0402030d180e1510210e0c100512010906030317041502030a0f020304050115050105040803031501030608010e0c01030f0e07050607170724060803 75
    0x81c241e014410705000f480c3c55201e464a0741d80301c800300c1d0310b80b22a220314800c120840c1028030400d1b40c80912410084040300e49141c400801d80414003d00a001103400002041c240341034124000e50040a8001c40b140c0807500c1004003600740e213803000b5901c504c24064100810240c0d2060450040c10b500103040c0d0345c2c3c021b40c104040120310941704030800c2003c0c00403400c0c000042d100c081c000c0101c4800051107a15524000e06250020042c401486031480700704004180288100801c020004500580c1e0350344480780c0100604035110520401d6101100700810410154000c5402440d031440c1c0341c202540c0c503401100c0c1c03132045004582c00307500140045100b41411448040905105041c01b048140c4c48142407421140951003050b031aa00240c00e988071541c1520600141c8004080c06120b800207200038503550314810310401b40200c0000030a802486a00c8800840b000f0b111542c0c00e0b6141041d0402d07280000ca4144060508803140311568400360f681e110329011076442d00c000e1818240c040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 450564568 1250 450563318 450563329
    0x6090606071110020f06090d080c0a051c0e0d090306050903070302030a0c0236010b04050a03200a08031206030316060507170c040e15150708160c05180f06 68
    0x4141e08040d4442d000b001d2032020024000140315030087e00080ca25408901001440048042c11107079500504000103440a5840000c030b4001043c2c130308007201420585000c541c020140034202e140c65000709540703013403c1d0313921501d21310449000d0342d0b0a001d552501305200f0303102c1c03240d40310090143c1c0c002c00040750014020391048400c00d00007803a1100d420b518000d07040080d40c59240081c4031044244c1d428011401101e0680d001d031144001160516062001140c0880a240000307005804d09500030444140800300d07014030090050034a120700781da01c803480c1e6038136005151041071004144c1d00041d030505002003505e0480c0041d9650415045244d15001d000344000740295040001913094a100581c2c0da005840c007500c1c0404071030365540e2030318410750125034000d0880306101001c00b080d120541c0d501d10325480f0701c0c0000b80c4010390354044c078034100e0114840d001d4150030207500d01906000384001d9036841000c03100241c03800d014451000b420600603040c222454902d801c4040e02049460a10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 450565818 1250 450564568 450564589
    0x8040f0c0503030703170702060606041a0417030a020f0607051603050912071a120705160f06020403150b0a060516060f06031202030a0807030504030e04050f060906060711 75
    0x21103200c5401074480001c43d00319070110a041c0c000c25159080055038603801c02c0456440310141c809000a403c10900103091803180f031040030f042140c5500312002c101c85450844008080c08043c0034030800445003420388a03001031f800c40c000f41c041e0081980c400c54000c2500d038070400382c80c6e40f40d620300400c091710300e03811502d1000c0607004c02405000040a60311040422102d940c282e80050040074034229519001024588c000142d0882c14000400c89440b801d2415030448200e040c0544c40fa4203149290a0024007800b02409085010250f0020300c1000e034002d109407401a0134401202c122020f512081c0d640c0040c80341d81040f829038040041038440e50142803030130840120729001c0501381c9c407400d0980312400a00030b031090b511442001040421702c4020b884e02d4150014604040302e18101400031740008240d03138207250b201c10001e010107110345655040208000d204201e103080000b005c184081048440b9070040c440356000c940e6914000041e00e5146078400101c0e401d0420100c14481666003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 450567068 1250 450565818 450565823
    0x150918020403120c15021c09110a0f080c01110c01030b0f0a140a17151003152f0f0904020d060602100b0d1a04150e03090103060f0608040f 61
    0x1800c1c00040000f60781d04040801c848281c0c2d484a440602a013081901282d0624103809042e00c100003802c844068100802c180da514248000703440320791400c010301080294910a13070301c072101560224000e0031a0021600b41d422400c11118007035030f8100107542d461519284101c00e9486081000e2a540c403e81080306028400f62a610346061104003054100006400ca403071030000b0581083d86500380f603a241001401d1018161003010f5814011545500c092031068508600b15130003d843c20200c0031a100045901c04030b49410380300f4050440e0b0003048514170380c00040e04803586111070001407003078500e80014120103403031400303080c1d03010001d440d441001110782254080c004175800e601c00d8820324000f0320742a00075202003100845032004849651034600d104074521480400491400c030140304490404107140035103619103061450200d0b007a0544040c4007814555a070000c0c41c0080003425000d9401e0300c0a200142d190342d41200401c90364090100092814800200811100342003c04402d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 450568318 1250 450567068 450567071
    0xe010521010f0605040e0307020d0f06110a1d030d02030f0c01110d0c0807030905030403080304050f06010611070503240c0f03070305070e06070c0302060c031b0a050106150918 77
    0x400480e14290350030b050310001e642d075031200100324605180c0a0000307002d82c030101444c0780000c0c070740c00102031043d45d0a01414040c04c0c07091310810000c4c15807218181e402400c0100c0c1d1140511080100300704a84c4002d0a00000c070304081c50403504001600c124a402aa0055410059091013807030240c0c00000c20346200303640321280c041c3e0068108004000a076085c10000c00c1810301110007611126010b4030200400d0f2510001001103034001c020350301602ea0001e0400d60340c6c1c4544c1412460018540300304400c5000d5240005030345500910700384422400b02091758695a60742c03080541b580f2103110b00c50340000842d140c0c105454a00d401e030543c82070340c0003110340c10002c00c142541c030075810840c0c0400119a9070300601110641001700c200c2c0c6500c044428610b000303002d40d65405242c0851100034002c41020030180c7c0c44000030302c1503c412950a0201e0711103080c4441d481d0390b075184500d00c183c41c1d55180c500086401074848040001010441e1242c0001c14a400704c2e0340701400c400c04210030105d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 450569568 1250 450568318 450568369
    0x60309020904110a0506030c2a07050112060e0901090605090d091a0f0703020c0102190203151503030f030604050915130c0f0b0304021009050d02060705010e01020a0807090e010e0105 80
    0x151b03924409180034108051400d51240000550180140c095404922403c10625450f207405400022440243c8800307190007107526841c01d08180260035150020b4040b44610010000302c05d80540c40080854020030040c0441d40300c1968071503c0c0c02500078400c0004000b50010f115020340f1100554841c00060b039010702e80303c61111640e40541200508500580040000c801700d5a810401e400003030340c000f0707080721203003995a0010790f8404c40f040b646602c46100b41c0001d4500c0028800c01c0461010150036a0390302c180642c95422240c0c411241988128034200c080f41100b1400151a608401007050402d9580c580e5807100c8511011000d0484031060254004a0b4148401b92110000d103440e40d02d02c1d80f641018410007207040b5031414508208042501c041103680d1310041359100d41034054640c1941c1d80e515041842c094401800030040540c00007a161164a51102c2054030032203682e590b51100c81c0d100c03100100b40d1503080c4a4030003090300c0c49006001030f2506007444604888461a00c0240 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 450570818 1250 450569568 450569579
    0x60b060c031c051e04031808120901260c1b1009050d170a090204090b010b04170307080f030c07051c02070806090d050703090803030a15060309020904110a 68
    0x3580c0c0039000c0c003241e0700d035402d0307101c1d00000380c0b4051160080d400000c2401c000d000300d01380d408200001070001d01044016030380c03442d085050884400c041e0490005030740d02d202c02581e20b02820342c810028140084c02252907001408030016111180010032130480c4207c4e1244c48600707040da045400c3c00e2964004100030003c0b0114100042020000000c001142900c100e0401e1800c0003044c1c0055010300240d80520340040000c2200c65a01440e16440010300d25001c1c00410014140c4250090003e08000008074000d1a08805402202da083c0000340c400b0551400680c3c0f6030107400001480110140402c40b482c00d4220080c540c8441c1e0030040c4e030305151098442c40d2501d0b03000081041854560068042d09a81c10321443c005070125030010499410301200702030b030b0b902280d050b0204010000c101d50007010b115903608002001d00008407a2203007040d4038244010301d00180700c0608c0d402e2a210014085010303000c1d02081a4004010741205d5665485641181c0140404140d00c6050346101041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 450572068 1250 450570818 450570823
    0x1f0f02030f27040506030a031404050303030906090c03030f041211033a0813230105070909050408030708090c040f1406030708030406110c090403030902040c0912060b060c 75
    0x440003411411a40903075011040d00300740b600840300c4500640c14141007100340d44001483d00112681403810003900b0702e04000d03801d17490050f40c22080d071500002042c0000240000741d06070081c1171072419141110001c034100b603680d1040642d03000c2c2d006000d1004001d521519192551014000e02c94036005045030000070381018044559031007544001d502840e666401d4141414000780c0b0040400000e081420b03000c2c1040000074240034510100084840400c44050516200042e040d804280301c0004900441d029001c1141c0e1315000403a401320010380030074a806014043c0e038104a540e0b140d5240c0c5042142d64001c020b04011080c800e40c00300341025112842001280e11145070002075940c041c0e03007003501544000e0f001e54460751041d1418488050301000300c90842c0d819040218041c4d01c4100b80e103047c4914401c42c1a8070094540412041c51741540043c0d8065100720303010000700f000e6900076a44c00360540a04031540c1d201041400008425601401c241440108814146181c403502e062 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 450573318 1250 450572068 450572077
    0x1020d020a0c060506010509060f07080702030d091502030f19030902060d0b010e030d021203040c050301050f0a0f1e15050402070812010b1c231609051f0f02030f 71
    0x3900c1e2000442c01d12003d4031401c0e420903002d1802174071300100ba000248140c02004c031814401200003034040c00f044130310030441c1c0c003150b8058107851861b0641034000d41803140c14400d27100724150b0384440d00c81e003034404400c840213080c44c60620b900300074525020300300e00e003001d901c5101030640d55450701005da5590341c00b0708005100007002088110349a000180804680c00c000c901903403080010b01805a00807030180000d00e1007a000c1c40e201e07901c90411828440d11640040e030554600760a00c12075812090000c2d2140d280e410b03080c40301d050850040c00845d5061921820040c00200100d80088229000b650b2001c0003400d4050381c164031640054100c0c1c0c08248200e490010006d031f11200303038000d01c900c0740c0103120502c003071805c00e02c07448694941c40810b1f9012004081e45c43d1354030030000400c81420141c248500000c1d1515107007207440c3c2140c1c03141e241d0608000c074021000004007494801c4241d0404002c0b600890030b00701c0c0e0348401f556886903603e07581c2c0540c0018001030595060040283c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 450574568 1250 450573318 450573337
    0x30b13060806010504110c281a0114090f0105060c01021b0601060e013207120305250c060e030f03040c030201080a09021f110f07031b12060e01020d02 66
    0x2001c0b02e51500342003000b2a4000b00c009541c40f507040c003204800d80b1000c07480b003120f02c1301d944a410040c1d00c246500310801c046800001e01020b017440c50314000c051008080b034140c54111031800c03980060541008041c0400300d41000c40e41c0d003580014040c03400c0c0039000d00a001d100707200160078004043d9900080c00c50030241101203600400c010007603030ba0310228410746443e080c20304034a698a8030000015100401d41a0b49201e6851074400480d083c4c014200d6080a40042d85040c0744020010f00030302804088d9400c021007100c4c0ca15401000840d800c1203c80c1e95400e071520002c202041d0f840b078015040005070f40c0c069001c1440066210640000154440c602c1034110030701240c2540b00142031010050030349040a03207004d1501c4016200c0c03031300500030246003100d25040c40c3c0c640c0604540400c0702c41c149290354040d41041402180700001c0f554142c17442a8035502c012401c1504240707104402d403003181c040e0500c100e544c0002c0341c49a81704104c42d0040d00c0000d490040510700150a991140074038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 450575818 1250 450574568 450574573
    0x1c02010e070e15010306030c060e010e06030901020a0e0307060e130b09040b090f072105070306110409050606030610050315030a0c08010b040b03030a0e01020a0204090f0308150a0303030b130608 85
    0x108441d4604082d8000003c20090a0422255045441d000e040c0f070040c2c01514203120040480c800325a002c0c1c5540310101400420300c0c1d6491a016450710b010303421a29014020501982e403200482c0740c003045c1031003502c42540d1500140308141c1c0421a560b0342c03103804881d01720369500e80308642d5101c40d050b641c4120f000c5c4d062124079041c40f1840303a1a0214036400c2e400c85410458080c80011280440c0704140c629a5031061440d19503410302074180b28142e40010b1505161010420b41c0d410b0507400b40088464501080081e542d64805026040c03004441c02a8005800f502022140340200095a0001400e88a54075400c0281011034640848104192200c10001000b084596000d00a03401c04401c00c0e5014811000d0240210b9920b00a100020050025120080d419a44200450588550010f1040c468040700d401c05400003182000240c0000300c01000003115050841411800520090310100c0321620795241240108108035020b60311549050064004807200d000c1c41c0007030000d0750003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 450577068 1250 450575818 450575821
    0x705030301030203062a07150f0b04111201092414130c080601050a2a0c05090f040b040206070b0709050f01020f030d0c0e0d1a060a05031c02010e070e 66
    0x4140c40c21100510038004060802070070307180ca609906c0d01102200c003069a158036004c640c50040b0406906014681d4120b103400d030168003004042e08006411001a40d0410050250300c10703403074842c403441c06c45000020f45a4010071204000e50f02c6001409e0f007c0306c0d18030003984559480041c3c08010791000c0702200c15581c40f0689441d0000c51250b06880940c0304021184040c44050407903007000304203d041c08004501808441e020783e10075600049120b02604110310040d07030500da124103425003a180400c0c80f00b408601820009840c0c0e018140680f11031140e6a5196584060140d000340b08903040002441034500260040d0b10450040e00385890f074611035401e0a0a100444081480d42d504640c40022800c0312020b0120445142e5900359601040403c00b09906a6010500c08441504409000c4a42c1c081c0100d219607440c2c14491044c0225040d00c275603041124181d418002c03291315030800205002c0103021941c481440c075556000104d5542c0008907107034100000d560012000201d03160 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 450578318 1250 450577068 450577073
    0x60a0309020406090614131808030f09030a08011503150914090106060e04020c160e01090c02010203041e1109100303030506090c0403031d10030b040f1b03150308070503030103 77
    0x242c0c1d030241c004100100b000300d181485146000240e02d01c031178007030076816100342034247e925000010401c542c032203403058012207460b1100496008854418014000c90040f40e0102008421034000300c2d0165504141c03079090807a0316944c110029040f0f02807603910420341000d01e104040d40c00060400e24000500000101400541ca07a4001c01c0c0114a034036180062124a40041c0d0920b141c6100340c43c0162122098190340d490080904c1040664a00450001408020342c082c40c42c16036205403030600c00100740d0401a802d13400140c0d0010201da121402030324041d00c1040d101c2400c0b0740030b240701d11308209043e40800c04c9a00107440e05159040e104805005058050040c00e400c8402603410b03c8861900fa11101128012400300400f007040424100c0716104c44d203034140201000c0282a51101d95174220003400802c04809001e0083c2e040440c4411500d46510070b440320f1003246500062113a203804070840041c54400e0001e41c1801010a0110201d404c1c500a0400c00d1f03c220025a034950460 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 450579568 1250 450578318 450578321
    0xe040201120608060a090206070b0903070c1205030313031e0909060501050324030f010f0f050f0f040303020c030c16081608210708033c1f0302060a03090204 69
    0x8104150700d908000782005800300004900303500040c3c2c84d130002100800c0b03100280702d6100e4980c003d814241a141486800c6c003000c40100b00d80ca02c902614440c03a030b941c44401ca5002c408a9000c0c285802c24000296103508180c102e50100e48245089003042c0e00b030301070412140c5c0c440701e0240c0020745440c4044c041d600103449580043e16003400c00a05620b0706440d0422042024100030300c0318a400c1e1890001902d00300b1002c820324081a000b07000003030140d900e00c0001c3c00702c0f816150906091a02080411140300c124500840d070b09441c3c3c03ca03654941d18103502942c0300001c00d205901c000c004064200c00e05000110344001d0702821030000610f442005032030710082401e01d541c212003640c42000f120340001841b000c660700c12042141c000e420041ca8280c140070319680070b00941000401c00610800a031110b0350b603500b50b001514400c4140340c004000020070440b603200e100d1400408108074004260748001c02841d001c401440c0039480750301091494000044a0000c030340c84400450462405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 450580818 1250 450579568 450579587
    0x60504050a06150b1801031b030b0f1c02010e0a0503030412120e211905010c11030c1e0c041103180a110603040c030c0b0405011b0b07081e010e040201 66
    0x81046400241c10194440080d01c00c450b00c1001001d150260488187d000f0340102256160b150324a643c166482c0070003801078001c54210f24856480e4980341c0041e0700d8a8900c10014106080b0310b107081083d6076005480381400c400c24190f21802d40c4074001120303501000100003406500034058180348841c0307042d503400c2400c4061701051001c000340c40c0700d80b41c90f070740302c401556458045250940007040c0d0515041c000982d5000508030f4210a1982c01c0c02070540040c40070902691780c805034013a1044001b500c0740604100004c654108101000c0140e103060b4110400344048402d44441024131400613040b15100303041c429100c02c0120401c050364802003840c0041608817030103003009025503a60300c02070b07080f100421440b904020000c501403240040e103120145034010103a45003a81c459198410a4116201d4280020000c0e142c01d14110013a9034444152a8800002c0585803202070060340c2001c0010071041d0000c803c0b5448a030302d11150f601040c02006a021100c9140c1040e00004154489 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 450582068 1250 450580818 450580841
    0xe060115030f090302120a11030403060212090c1c03030f050403080601090b120103061802130501050316050a0b0a050d020703030b100815010f120905031210080a0816060504050a06 79
    0x2070b04443c0d0740480e40100d680483e030340750444050f968900d00e400c00c0d00c200948170072184d110f00c80484c02008004007070b40108681c6000d410311000d00d40d03c00140c0d944c0c440000020581100a1300c041152110204a1090303500b8030904001c142c80c1d440e02d81c4541207400480f005c2d40080d004d407040c02595600024800c0190009201071442c0480304606031600010600c001407200340c0d95034074141d13640c079040c07010304d00d803a40217041c1e80c580111155000090002805124407902440100f03142c1a074110075031004a42c009808050000e00c0d0610306030a5070030a00060041c0301c41008041c40d800280d2000b003040ca840f07618005519484141849441800180c0d00300074441c202d02070101c00c005c40019240161001d183c0040381e81181c8000303d96a0f0748850300204035908000c031083c2041004400f5043c003e01e14a0880503d9443e207041402c201811b10a10155820042842e0081643c200050818810100f00170040d0015a51584100c0744100c900f96065040440e40d0b10801400340035800d40c107407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 450583318 1250 450582068 450582071
    0xc081c0c0f080c1e07030914220c0e09040f2904110a080708150c040f1404020f0705030a020f030309070e0603070e09070303020705010906050a050d0e060115030f 71
    0x741c0c1070390040c111000c003038001007005002084410f207203205901c00b0704040c0305204074241c85621900d000703054000280600b600c00000c2909064541c2805000c81d50007070b204896610003d110701c41280d0041403d40c4440e010044036003a030480035100c86020750b001e503124102e480d000100e10300b8150b0f1118103d1403045401540c85100f007800c80340d090481c903003240c1c105201d8103000310842d00092a80c1d4040c0e000720410f0003000c03000200c810012407541103c00b000a0400d00a540e60040b81f1400d00c181e018005500076001d1f4280f014141030010f03000c078a44050070041c43e0400b400091b0030f50740c00c10801158a6403000960301c0e005641802100c040c408080c000b075085040c2520f142d9210741c1140550701d822062400011401e0740c2c00c00048000300003459002c0f00c0c0b414610f1181d51281c1d454042036001d44200703e07000519510070700c0d0000448101e5070312281000001941161994045101c9a100d1500c0d00d250030480e85080c407803180201210030303800c0b104030403070302e400b074140c580103810050031a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 450584568 1250 450583318 450583337
    0x3050a060b100e190e130302070b090d0b0a09050a061e091e03020102090603070e09070c0b07031113140109090207050c220501080604020406170a080a0c081c0c 70
    0x70b80c100c40416010340003128840022010000740c1001c00304a680020310a0701700314240b1658484200000342128065401d07034000d140c941e41c0c1c1100c103124084041d60058000c182c9503000c078405066080d000b102008010603010802d8403181c0c80d2080740042541c0070366031800940c01215950116044591480d9410b01c03200d079068848100c02c01c02041619018581c204400e01018401e60440d454058010110368480c2004200100f0089031045010f0061216202080704180200c9881064540c0035244a4040d601d41e4406c80103001031a0300e00481182c24014440d030280700c28074890180103451003103800410b1000006250611a0b0b1065141034410410b41e008640702140802d110352041d00d00c21a4070303202c000108490300240560351011464007001103100358010603003601940c0226424000d558580356030303248034000c41003040e240d984100315440000321104058041941c01e4140203007602c5275529500103036440704c2d4003000c4011407048200032060702c9210710740c000100d915210a00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 450585818 1250 450584568 450584599
    0x603141501020a030f021204140109080303040c1a120f09011803050405310504020f09160c2303030910020405011d030a02040608060403020c10020705060c070f03050a060b 75
    0x6a030092080030741001540c517860001a0b0081040301c56186c034800c180c1da6590351301d20748242c1c0744689140d41b40c001040c400d000601c2040000c2501d000342d810000b52985280b4101260a000300000a4038403421418021200580100340780c1a00c1500385040c2601030b07181a80c0e8050859680d003c0c14882565200d65402c0420ba0140581b415a85e0a45032407086074804040d68515095010542104110080303d001c5040041d03004031340a68030070f4072102c070321005060030001d280d503045400030f070070598000071b0748030561280b80210410344c021511410000c144441c0c00032140488106034819a100000b8000c40d0303e0100311150340702c180c00404500f098149030000302525001c10103031015900038071703401109640070b2105640c0c41d580100100300e0203135240d1a01e45c0301e078030840d019000b60103116a04509400c1c01142080b00310025400340603071504140c10400b040c0c0054005150358440c20b030740403481c00504001d0b54003541c090001000710032502e141c0082a03840085007180180d002000c0b1414 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 450587068 1250 450585818 450585823
    0x303010f0902090a170d2d03021602030105070f1704030e0d03180e01060320091012180b0106050f0d0e01241502010908190216060314150102 62
    0x1035541100000d03a46807101000903e070b0351000d4000c1c1c5d160100c0c481030580180d200161003030540c090781e12000b0800c03650443c5507100002954800d50080d540030040701d0301503c60f60051601c00241c4010460151098012070708403031f82100c6400105140c0141b2800a80d0002000988100c003401c42c01d58901e460360707000300f150110091a074000c0040e08085030805008584400d03c1108014101c04015560104500007200038459000030900d8480307001c0d5504405c200391810030b500125845d1a002540043c07008440c030200c038100800c4140407900c0c00d40c04080c040c00d0400d036001509001e0000762410076000c0c80308103038003000030700008024000014524600341c5914a5024000003484551b4844050140540c02c1c400d026250b0700d1000e20354415020100b038820f80b4541c88034448240310b500016403c0f00d003401c501400055080c08420400b4000410b283c0e18a00c0c14410340311419000d807506040003400360000b40c007007030716100c5010700d509001554960010402c010849007018840010b074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 450588318 1250 450587068 450587099
    0x17040521071202180c0a030e0a032102091833090a061701050403020f0703050a0602030901110a170a05160c0602040f140306070801030b1914190b03030301 68
    0x7908030015072400400c3d0340c0d030301e8405210f008011020744480c0c6824400005642c1c80341c0030800109290468030030042c8800a80203520790350546480500b5080c08204800103c10366015100d125004c003d58100390300c2e60400348001c80d00b80c2c040c0d83d402d4180401d962808000031605591a43c480c0307001003418502040c07036545403400c199586420394451808140150a40790003810241c500c015103100340400c15448a0311650103507003941d5120181d1008581c03208000e03c0041d000780e10410800c00494040c2d401150010b003081c2c000a5104642c408440301038218051400104600903400300701001e510b0718659000800b4541088540b401c5000c080354042200b5540c810005208031180030410158100c034064503601d440c000303143d0360b035000c00700700c076002c90808074000d020b0080450702650103035281074185c1e80e015503506699038804032003000500d8182514400251540310491900100704a000e0055030300d0075036200d10715001460780e42900c1d00c8a89090003584104010800c4003907615194 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 450589568 1250 450588318 450588329
    0x105060309030a050f2809050a1a0903070e07121107080403110409020a120213050c09010f020721140a030e04020c0a0b010b070c0801060b04030308090a1704052107 72
    0x5d40320715100d20917030060301901c80000314001e1403484180c814000d80810702e15401243c1da46c10906c80d1100140501c0c00c2d0a846600b190300001200d00829180013070142114100180c21510ba080d40e52425081c0c1d03100a90700200419044000300009200b03a000310902c9031050824603260403056900c1b41260700c61880058040300f020403021006654540081c2d580ca5001054513141030b4940303440500d2201c0c003420891040098121402e40f01109005262141400c038000d1420b0103100700044d144009643d005200714000e054020810b8108000680144621000a412105170300d1505129401200344440c0095010844450010380c3c0090801e60b40c1a0681d400b584401c46407841c0e42c03600c0707010000200700f00c2c2018008500c240c1100068801c030381c020b02c21031490507900c0c0c0015017200c0180c000c06626240070042400821300032114681c005400c241102d00401d000d0b01c60500c1c00c0310140c614181c038000001c04108030b1030403410001c2401c007081010030882d02c030155010355071001403040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 450590818 1250 450589568 450589577
    0x1030b2203350705312601020a08010504140603120d0b1804030201050106140a0c14061e06010311090d030504030213050a050708011503050a0608011505090105060309030a 75
    0xc0380420200d042c6000d030010b40c11070344240c284403401609940004207990310100c040400700703061130120303107110310195402001c0410050402e10481c01c15203240e4000c540d6455518280c4410341c400348000c10081110342e403111070550600c2c080000341c1d403441c04010b121020030700038441d103641d0110351012039425083c1415030710160145800050620000501d50080d4011a0403241c1c108040342e42c0d103d64400d0b80200056030322004144c0341c0704540f000c0a29007034428881c200d001c41c01022031107400d6004007001c004041140428502c1c003042200d811049480d4107035007100b0f541540c81c203c1c1d08240f00b4202032001440c0340e401013a07203000c0c0d4a00079100c2d0040400080505d03000c0c1088801030754028002d00000046014460080c08043c7c5148020b18074207000140f11034401c4400d181030f180120441c00c1c1540303100b2001c8001e410040e00c610b44490340c60350002038050092055519200d541007070750660301d282a040040401c07059000c82e00030701c41081000100900070044800d69940c6080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 450592068 1250 450590818 450590867
    0x406020d021c1b0219090b0f09010e0106050c0705150d0c0e03120d061a0403050c030c010e040509160603060f240c0303090b1005130e1b061201030b2203 67
    0x581e8005c10070010822108100c0030114a00d02d240d080032102c50400d86d1007189642030b180c288031001409200341541d440c0d08000500082c0d21910040c40e48840d80c504031402141c6400001d082c400c141100e24003803400008100500344034a00450b21010881c2c00c0060040142502090316460b0342c071340c5203c56000004042c00d000b00b2a070700c11000703400f9212030000c030380b03407501e29541895009000c2590780c0d2045120001c4140b41c0014540c102e21010380d142d404000305081844050100038008001ca40150440c0c181880c465205900c002d11840d9004034043d8540043d604952405400c0007244c00c03090303c031070031403400c8403180502900718034605000800d8a40c10b0031001800b61000041c5004114428001284100c02504090752411240d000784a0060718004d8103c07411043c3d20400ea40103084d0141e04001c46503001c99260202601c81883c040780718840500591b400d030811107414070004203200181d07044070303058215488886144800c07c4902e890281954440c0c0429040c542e00090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 450593318 1250 450592068 450592073
    0xe07030c062d031e05060a050d0206120405100606030e06070c170d0c0806030307031d030f06040821131b080a051b190b0304020f060406020d021c1b 65
    0x842c081603140b5018855202d0019030050140140c08203c0610070f540e0f400514402c2c0c62803080314098680207000001c000d10303140612480c5c0c50f10b16016039114100340f042c500b82c00101c0fa0701c0c5110f28030400192840004c0a01c0384002c07500e40340c00404c01c1610b00f05038884d801034009001d43d00300c680c506095812803614a0100c0450716043d051803002080807807900c040700c4040c1c0003084000c0483e1034840040d501c5c002459500e001c0c9000107030005046d020490b08032740c01d55501c1c2e00c10705005029a184000d00100d4240741410a841c02c444040002a51101e1141d403c075020740d071048003c005812074181684100c800e105800342c0503200268040300140034070413401d000d074001c0000006451825030316081543d02c0d0b07500b040326200a98014004103a13245048607002104116080809040b141049010b46481e00020070881e00016203681e501025074441004d03000508081c2c0c020300054000130802420004061540140e80883c8241104616004003941b401c000d04041c00c4000c1c05c0c19070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 450594568 1250 450593318 450593357
    0x20c0304030c030b101a07030c02040e1902490b04030503070e01020313090f090212070f05032a0a0302090a29030601031214120106030e07030c06 64
    0x303510040652210310b80020403c850541c4072442102c10302c4200707910b10b50b03500e08140e80b403000100341180001c0810a40000a0240010100e120b0015000003400c1c1c59212005180014005003c020390592031850011490a01081c090442c4805c40b8119014525510b000c05402c440c04049a81c0e0030460503090001c0307205c40f1340b1030002d80102403c8490309090601030107560003540d1207800180100c150b00450b50001040b1428000d02100d622982c07460107042000406402c08841c14030b5480c0c0072400301680c2d541800b081c03c5e0b146d1030082d107400c1e86020850302302c2c4015980320313a01a400801e0080c2102c90f05178400c4c100420b1104000000049040000320400c100750070081d8096140d00c1808042455035014020b64052521300e00c00c642060600200c0f210b4080c4c5682c1d078103a21840052000807440e40804c0d6952107503050007803040241440b4070155400c01100c0c00001500e00c0300400409a1602901a0002c0440301810707546045899501c081d2070b0500440b414840080408000600070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 450595818 1250 450594568 450594577
    0x3021203090118080702090603061005040c030b3007060e0f030a120e030c03060c07030e210a020406050103020723030f0414030d02060903120a02190207030c12030210020c03 76
    0x2402201c0d06a110145020356143d00071742e40a80c054104840000c00ca070600142e00c901414550501da0451842c0c48204000b510450340b03000304140d212107040040d6200c044100d07113074021030301c107841e0b0a031800c008210304042c03050340c5061294040c0001704001c0e50000b880c0c1c403600d80700355006518030f400400800c0c035100703e60034002c0c810f10f070440788400c03a95480703003030000c2c6e5000880036a103048144800709580d5a400752190701460701c0401c540b5001070701940e001f202e422005070400d03180301c0c2030214102c0c0140b225405510b00343c0040500e1000c610b0148542d40161000f400c00b1800c05000da2907003288410081c0701e40b000450000305603070003050100103407001c9902813014aa44c0d03603119a880c0807080041c4c41100e000e403084482d034415844c0042203007842911031390000e508108482114036101175010f840e0100d0a07508100501c0122500500382e11268281d40041039031a1031850034040441c1d46a009071040c82c0709280c0803001030350204913166144410100941c66426000703416046119 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 450597068 1250 450595818 450595841
    0x2f070212030313050709060302060d050403020c0303030405100b010306032006040909110a0b03071d01050909070305090c03011e0f0e070320030c01090315110408010204051c030212030901 82
    0xc00720802c0100541250500c400901c140162443c980c6c1d203031001e070265141c030300000398015000d104c04440c0d0101c2d580001e510500a10448001440c2c0b440883d003160700c01c1d00d050f103158004900b041d06a001e10f0007640d900b19428a01003105505d991030b034468840c50030104610040c00c072010030800707a1b5400d064074090110250304024844081c5005c11082841002890040000400018085d10414260392141c00c0c19221401c10030070110038000b001717184140c00c0d4140328081c4441d401039181c070074206d032140c1407580300001c060400c1c80080303144c03070083d02c28030744a83c2c10040303400400a18080d000d0b1140a9568000c41e4441c6054016006011007402e03942d220f02c03a22070b001040c00319000160800c5825814070b4620030b0b03000c90505854540c8000c250740460f40c0c0300d00420014412815030340c0d02c4440540001003504403210b09101950241e03125002c180e4009c80c0034002c500e8918005548107844040031482c8007a80c2c4d0b4003a440b120014a540c810f0303000403000800090b03082d000300745140d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 450598318 1250 450597068 450597073
    0x909050c060c0f210f030703020403050d08090118171303150b100305060f060f1c061e0e0c0705031201120c08010c120c020f06090604062f070212 64
    0x10b050318a40d2207403c59940f0603036101e6040710899501000711100030a03050314030150328108003c1c01500035544041d0400702055800c1100002249080c40760084140300c6640300c09417801c2c030030703009403d58500319041c00f0913a02c003620074000500e0b0f6003101d42d11440031544c0c0036102c0307030520f80d021101d22599001404560190302000440b01d580d61090311181e0089038415208405100120200d41085a000d42c02107000f0650001d6481c000c0041c10b00c0c05460310303406150480c41d01d82c2c3d1000c141c250b81e1461a8681750042480b01440c0d018403503e00c002c490002c6030b4858684901c5207007118019103180011340000a42d0801d2103401d008071903003d40310310207058203560360b505400c4580c0ba1030301003520a800000d43c04594000c0c1802150010f00302595008184010b001070303000100103421800d82036200f0707810030110302c03181031050300d100ccd0100b0409052540f40034100360044d540215462100d208094850080b411820078821211200401c00c83d6140e01d864804210040b0b20005000050b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 450599568 1250 450598318 450598327
    0x917190827010e070e090c22021201081216140703020d08090310180221010f0b0f0108070206010b07020604091103040c0b0405010903060209040212270c06040909050c06 74
    0x6803815081000755030210f00440c1ca2555807442690340d602c0056510819940155420030754511300011060509001c1c3c25003110000000c0704401c0c03c07a403181c40c802c50b036104a100100325081040c0301601c10100004d219500e4039041250452801e5040034000b00b0b100322900e11030041c110300300301c140080d40d800340036500c4016607400c00b200701d41c201d852480d01c6031007404008881402d5501030080c0b5003003000c050182c0040b442e402c014030500d00d003160300d200607480e82d2103d4908900f40114030294007403800014074000740406000070729200282141c18802c0881c00d005526500240560456414581c80d1b6120303407503440001c4503842668030400420b03007000c14105000410500640c069031040044681481c0d588180c80d5560156224450100f07100407420004629250002c10388020002c000615011802c0108012520b040e2138404203030360410200d8180004441066441e1288040204034014480000487da031240740960702006848440003400c000c01004003015840004100c0d944230f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 450600818 1250 450599568 450599641
    0x90501020c0a061802061801210e010b06040302060307120b061201050f120709090501020f07030504180612150216050c01140c030d0c05040f060309171908 68
    0x2c0729211801540e10038507200c0718080e21034065040c0915140c2c098042420909041041c100440503202c8841c103000d61800c04245010546030f0007182e089849100040140840c10070740e085651100206000d00350401007400581d45030f0003965403000c002e2030481d000d1120f000012014116803056140c000b500400c0e000b100000c00000c2d00d060300d03815159101c1d14125a0304000d9050010050b05040d43c020120a100c0e03110340b6042444150f000e400094034007110f84c010710070a5440040b0a030300044010506008074001034460322514003c1840c00c2c41407604040e810001c0b04028400100341c4030386c0c00500c1e000c054031034040c0c52407510f606070741030705068142c01d0181d2030340d007036a507214001038206913100050008070040c0c6c1d51007040c1d00015810000e5540b01c40008002404580c4180710007840b00080f20500b619800005e4034060360045421601d91801c1c081061901446100828041c400713a42606030021006903a014503141203045070301c800500481e0344000000c003210ba0302c070100e58030310b4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 450602068 1250 450600818 450600823
    0xa050409050f0f07020a0b0a0e0c0303040e0a060b0a020c040203191a0108100807170a0519030201110406081504021303031805031501060c080d020301080a12050f070206030a090501020c 81
    0x709020015048040e5aa6011300b20b0301c601801d5002801c007541c06000c038003024076940c0448031448a690403604000d80c0d0b000041e08c1c0d50056801207066030009002c00a40e0503041c05040c0c020110144c826007001d510b640d000e5280c10f4114801d13402170754040001103016900c080b0070705407090222810403142c540c2031041c2c0c140070744407050207012405c00004035041c0040b5040c0c44007218015405020050304040e19050541602c1824000d1442240c9100011503c240311201200c00c03c0d00e00000c4c508041c0c0360290950701160000c00c04810140000c01665801c260801d40c80516001c081c14184489070000b802030140c003200c1003405203518400300030035800000d00c0c420054100445591a40d5034410956590340e200c5012415003d21f0004000c0f031030150b421842010f00c500c45107414007070900e00d0042282c000340d00252840d40303d00729680901000c00e00207004040c07a031030f00d5440c0c40c00344601c0d00340380c1c411040004e0040c0701c00400641d640140f03a001c0000035501500070355032100c103001d030180d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 450603318 1250 450602068 450602071
    0x7021b15040e0a0b0604080a02060c0c1c1218050105160b0a090b0a0c0509060c0a050109150e062505040f031410020306090403030f1b050c100603080f0a050409050f 72
    0x14215032421314801200c0c60110b00703840c101e40c041001419822610760a03c0040e400c6140300e40058454440d41844503660851521302004c00918405244801b034108442000324141072001401210840440c2d014078030034126050394001e0a05a035200c080344405954041c0b00303c8040c2c0107909241c04d0082840341904403041d0540100c865030b0203500c0c3e8050802c1110031200c4807201046040041c15402d080050180546209020680e44074030060b8807981d007514900b01c41182d0314003100d003814020f0b403501e11900700c0c54101d5100401d224508550300c250400c0300141e49800c0c41d4000700b000741d6500c4c49442100e0207401a0b4205021a56481c40c00c0b00459019100c10305460046003520a407940e4544240ca00c2614020300503000364442e510240d0092009010440c1d2040e110804644005242d0300380c0c2511100702d81c0d80c541e51b50084d8002c08d0030080404160804203040540070000700d40c032041a00e00c4152002c02107641c80114060030340b200c1c8a0b40d48a00202418002000340c07842c424001c45 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 450604568 1250 450603318 450603331
    0x61b0c070e060f0f0d02100c050f0d1101020c07031121030403031b0f0201230a1d0103150b03150d08090414010e13020307080f0109110907021b15040e 66
    0xc0e240040b0f541c108407400100c0301c0c0320b82d00254800c4040001d45000c1c080d81011f0405070816442c400416100c0a05240a91a0700403a41d40604018850b50b6881030707242c00c11201c0d620003141007000b00040750341c8622591202911042c0b5940c035903041c3d6030703c1404608010380d11010700480c2c0c40d4200c01e216140e800620065022034603e60f2038814114222040d8101903902c40450b0340e08440c01d9006544d07030a06c0341c440080d085180144803075a4074280707000305500c54550300c800d035940c020080003409500410540c0350401d0b04100114010200d00c5500c3c50540e18404840e980301c1d65030b40c9000c0c6140c003241c01c210b580544580c1012080c00f100a00918031000c042d5020322401207146403200c8401000e05c5046a0205010f001a909000e840c4030004664402010348650a40d20040c031407901e5055104450303280d5441200b00100241030100f546035140a40718520744c0d1401c404081c1d10b03604610260001c500d0380120000300c55450510308520410300060300390716552a1100903c10380c400f200c50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 450605818 1250 450604568 450604579
    0x2160b09090c1c050f07050a080c0a033201051207171507080901050a0203010e04020402180a1d0114010c120306120609030f030911040c120906020723061b0c070e06 72
    0x4101b000b44200101c0300200c105031549011a1100c00c0210850743c8414205810950364040180c1c000f007400402d0700e13103864084070b803030940c0208010400c41d0180681c80f00d4416140c441c00d0150f1144045444001c44450b0078440184903000c1030a81d060180c82001005d0079800b890400c4099500034911900810206000700b050369070b50501682244005e002d07461010b0f05a000050051609400401d04400d0848856002044040c0407400180c603582045480040401071400c504c140300503040d0041000e40145001c0050010018051100d040390151015041d0310941105600913005000100044591414500160308203400180400d000c102c0000b4542989448010b109005840f4402d07040051000c4206d044000c000040c01d40451080a10445102080142d1a140314144005002e00c0015950b440a440d091207422420655590010702200c06100e0005000841070791048844000d840400d000d00c040a94600400c4512222803180b114049064201602914041d0409544 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 450607068 1250 450605818 450605821
    0x23070c0941090a0b011401170103021005071e060c08130b240a0b04050a0503120304080a0318060b0405060109081002091c030f02160b09090c1c050f 65
    0x207049100000c030315049241c10949501c1111403004428050382041000d01120000030b0785a962104c4030100340c0c094441001000d90a4007296003088520001511070880403403158110b6001416000b80c924100d4200100032500d5000c010721030441d900d4001c1040e232124202d180c03c0ca408005842411281742c00101d07078101207010712000b0881e041030550700800b80c100301c0d95040010050003010803110f0107860032081066500b9101e40000f1006406011300079583c9605100030f1081e01c0015910090103640700441001d20084005d050ba600302d07910412030741c0c6d15601590210094107084000d0340302c0101120018041100303682c004c3e039440380c09032014000395031614015240c4900c1c1d4860700c10141c00c803203030307210600341150700518600100801d514001c528000707501c14a0b0a02c410114003050b1603002c06142c103601008541086602c4210354102e071824120964114020004001e0042c240c01021611809a00c020344584018000b0440302101408060b2005498191a070548a404240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 450608318 1250 450607068 450607121
    0x1503070e041b0c08270405070212191205190c03050702100e0f071d0603010504020616170d0603020f0f030319093203070623070c09 58
    0x610b06031291603400e0044440d0200006a03100d80103040d044520042c100120f49000d5030751215100743c1500b400d0a5001c105514043c44101c0d00c01038960015540222180c15a4003ea01c045440240c0a80c0c074210300088542800d4070b4030a01c09408895050401080003480c0c022807403841100314004005004030310080c071050741242c100351944001038000c48140c071662062500845032007541001124082c480c2070001c0350804a043d04155038000d40c0040c603248005550481c05e03080b01048008001900385940020440c1c0324540c01030700300a040044c182c0512230351030f2000d81105110b521895484804d400e1080060209010072485071000c107186070658100401d01e03140c10000900214075100c1082e0b44000c28420403e005000c020209030007040024400c8448010640100801300300d01084448502c9000c4410601c54003a40c80540d041002075440b04040710b60f200c0440b401404255820040c0c42a48941040a0511718203440000740382003080c0d0050001105214204030783c43e1000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 450609568 1250 450608318 450608321
    0x50306041404050303070507020604050a121b080606010f0203281d0a030b1003060f020301090518120c010f0e100518030906090f040e0c090a060b040e040609021503070e04 75
    0x81d00d003e07000303a005100181600d400b400c01490803d000500c4d80e41090750b03c0f00012404a0260010075541004080303070b1040114492202d00d00c0031149055601039420448226518800145142d04202c00b51404006403402030040b100314a9400c041040680549154076000190f5032201c5070003c2c410340e00c3c0c51055082003c442040308801407003c00c0300c1c0d14540300d54420070406840080d404000c0080040000c1c000d10a107a004620560050385035850807001e042250801000c0c86107615010807064811140070031602d04c2410104585a00e800100d42c0d400d00400444003c2c22856141952007000d8220000780c0c1589010074000a008030365448100b100710580581c600003003075205110b075201b02c0c689040a0051180d015101c82d4061510600090a0301c8041c10303d840f50b0342100c0340b4a100c509100c2d810551107882010244440c5181200c008550b201b50300c1001e040c104900c002c01c00f00300c10707500010303612038008100c0400c400b5500c2103200668070a07a8001e011682c1075116002d0703402d16 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 450610818 1250 450609568 450609571
    0x1902010807050903030d110c07180b060c0309040c0e0604060c050d0306060203040b0a032a02010506011b060b1c0b0709080d08040f02210d0e062505030c0601060503060414 75
    0x6000343d814041b90024802c003401041001001505080c001c880d51120104036803001000c50f02c0038000c130700314900440703001c4895510721107008680c100910300c80040000304a074070044095800290701c00c2092802c0b61084249202c0e00c0c3d01641c00100000c5540d0b201c041c500290340280c1c191844441f811030305608440c854407410025800501c070401401c0158805440165114107004c0f07480105000360f070100740900442146a0310208114001c0c480e424130805a00031420700f0310550300c1e000d901c10402c3c1d26070b9001c0d0040c002620703984a8066070311007072080c40001c815690452450b025038907010080c0c4104035900c03030006004060008110b000043e241c90b040c4500d440741c483c40c1d100d50b02c0e4141d0f1140e100c04140e8200420301445400c0310754840c0030040811008020303000a4645d02c000412541d000c40a00b03115030006d006401d1090581c00c5400d43c0c0d958100382c0404601401e00c3d00c90b0960040d120244140d006100001510b142c2090040d48110402c4074200725403285c1400d410a4a0b10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 450612068 1250 450610818 450610837
    0x30706060509040b01052407230106030201090b181002030702100905153015012d021c020a0b33010302121302040b0307120303050c0903190201080705 66
    0x8100c0040016003040420b8052080c2c2440010f0140c002d51f84003c030b00c1d03a10490045490f100c284070810803405407264007200d407504d660002e000c1c007880d58000a14920726806003a483c2d076000a002100e200d0f01940d03030020008080d000d0322030700402d0103010751030ba04046c4040e40101d0105c210380b00803a1244c035803001a60801840c94911200c14200c0214a41101c1d952529268540c0900c00401d031580002a40f400c0003030001000a182c02d084d03c6982d0b8035050314040c1445070082c0307ea0044199074141521500b080752071496031801c0020b040345800101c415401a15120541d0081b0f0a50302103015a083c03801010080d050351a01d0100b06020341c0754140c0e1365803102401c000c40b01c1c8648441c00004100c981490003500b8100807022401c150407041d6000c41500c51346080031001c6003400d000d00074003404c044016142c21841c0030700041000c0c0c5142d400a080594a0001480415440059604403540170b0215849107100d0480180001c494030401d90100c0c1e210030000f030b840c511030000c5448128 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 450613318 1250 450612068 450612083
    0xc0e060a080a060c2708010c020a020d020f210a020907210b010908100204080d0e0102060a02071a010e09060a0231150818060105060a18051203070606050904 69
    0x40080e12480000c2c003021213204100b200500c40151000f040020544200e502c60030301d10341c020314206d00c0038210345d03101d1607031801d54005100f060003583c1c03588007a1a18540645400c524640460300007040c5840042e00038150540c4010f800300c1454002403030300d00300c0d407023a100c0120a859072402555a80d9500c0d44070a18100c90626180e503250f1140c05c144424030045c14a40a016181c1c80a50b04104e404c070650241c03d03a0200b0104844c090400c1034689101d41410501c0866080e03100007501c411009101c1d10000e60002001070400c0f5290b40c60310300c01c190030a500405540c4400b00f200b54244180e50880b40c921403100420794450f183c0c42120100c1c4030b050b1b0306803210200e051894084081c42149e003c40c01c2014600000c0d1f115410304030402803107466807480c0443c94500c080040022000c650780550f13034003100051245456500c1142c54070380303003401c064400078182c000f0111000c8a0790400c0f50882420348603c00101c0e000000b50400520440c024001d06803030748140003e00000b2140a070504 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 450614568 1250 450613318 450613333
    0x304081806090d060c2c1503011a0c25180510120201020102130e010501020d02010c020c0d060b030106080d0e0d0b04020405130f03050d0501140108180a02030a0c0e060a08 75
    0x58100da10141092005041070b082500c14014295040d030340c079080030291101c00c02d981031843c1c50800140c14452034841f02d01030455040199002c01403941a00c5100f03801d0000a407400405020841d1f1003840024540c8000b0007002e070398071500351050358482d10360340d00c8404180c2c01001a05029180c8128903100500014a103071111240b031486401c00c0a07410755600b081402c00d03604a21038903e000d400040b80303141003945030000091520110041c0f540859150441c81801c5990114031780b143c21038115008900034001c3d090280050000c503150701c2d8150b181c10800070700c4810201e12443c08480c281ca44901090014050103280900e0700b40042602c1c0c0f10100090040c0741550216410050b0388408040001840c0d46690701c501d0020f5065000c42c5020070051a88805401141d01404603151086010007000b00042c2600310042c0000c03890740c0007070162641052040080850f11a0002c0c202e8030048124104210124064010181c000c85003100107005c1782000424601120381c808011700c1d90 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 450615818 1250 450614568 450614573
    0x90d0f0f0903020901080f06010501020a0b0412050c010c11011527061502060f06040905060f07051e0301090614060703031a060408010f0b0108060616060e030304081806090d 76
    0x2100c2290300e0410500031012000300158840b620054081c1117114018480d40303c180d107180f4940749059020504641c070842000c00024410300d249508558840f14180140140c41e00a9943c0d00503c010340703000c1c0d807030300c28546c0c00c20f588503400355206c5801034020092064014148040c0f18050301501c2074034244401d54200c03041140680c0b81101103114400250192102048800290781010344001688803100388042c400c2ca2072004c40d040b400850f4104800e40383c950341d0345d41714000140081c0c0507000c0d98002030680b138005c0c022136030400d4400030088156809503c410105030020700520310664504007001c500348a8444148888800050150f414021740d83c0c0c044000d000c21a08100d0307000c00b1698000001e0f25170303101030401f07001d543c400840c0c034003e04000300080703401c4035031318a0400401c0030078001c1d01d46030903040300c0c0d2445015041108c5070300c1c541402c40180c20344212480d11031200200704030074084000d014002002d0110001c3d102d800038038040015500600b082160301c52001c54441c0700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 450617068 1250 450615818 450615827
    0x30c03270b0c0403021503070207091503080c150108010c0e04150513140c030f06040b010e0f0303041a0301030312050f0a09110307091e0905030307080402120601060215090d0f 77
    0x40c0b0458582c2c0c8140340c00e03102d0340401d001743c00c0c020f0042003200f008820300003805c1d01440a20054003e440082124442c2856045101d00080c400a044900d000651002e030003401d2007240701740c0004c80c18001545d40d540100c6802001c1010b00040060484e50044030217142c5800386680054580102c40c42540c10103081110a40008425441e02503452000884961030302c0d0540303120f0131054800c3e5403685880301550034181e400a11a038070581c505490b81010303a8007c0130b000030007a01a20410b1066001c02c0201e81345101da80c100f4015600203035000b000b16082d10b401103068a10903500c0084840b0302c1e18451040c0c81055a040391066403110004405400b00d9003c4c2c54401d004110780d082c4c0c54040d20119007032503c00d810405c009501e510320810441d0a1440101204079030309001c1082c0c100c02e40b585500c03800042e0403481046207550110f41596034400c050820385102c407040d40c08a5a690038060b41d6504482040b4804501e007000080b4403490105105c40c8a40281d1545110068080310446 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 450618318 1250 450617068 450617071
    0x1061706150a080d03020415030902151308063d0b0304080415020c03010c1107030f06020c061f0509010305030a0804080c01091103010605100c080a031803030c03270b 73
    0xb60082c2603008001601074040040b1140b0441ca501e00590b55400d24400c0700c440c0d00400302030320515003000301c520010786078800182208842442c549032110759440340442004560f0380001598031465060088108580240310b0307084019810160481c0c00480c90071801c0310781045c0c010081111075030308000302c417030510040d50b00c18400e80306140b6090711001c429414032030044210340141e000030f4403503040d81801d1003043d0000020381403a60003601c207041504d541e292640002010311840c440504100030241c0c040e00c54240b0060141c1e0a01d1910110481204110100402051040400008403070034003250940c107a27031704440990324021f28000150b404040182040f20072200030840702c0116402031143c514103e00c15442c0f42603440e0444205425902550040e178404d980700d500300c45021f40c0250b40c2000c1c0c5a48845a82d80702d8a100c1d50a070300520640d4040f07010404000100350030164190b02c0b0000301041c80d00c04102c080c1e002420810424a190f12030100b1604035002640031840310b02041d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 450619568 1250 450618318 450618361
    0xf08010516081018020f0406030e0d020714060903010f020a0c060605150f091311040305100b0a06110f01140609070806010203090625050624010f03020a0c0614070201061706 76
    0x903240c1484001c42c0011b40c1d201398007480000c1d59031a48180c42907410312204034216124402010051705040c0b5011550200b41d010710700c203060010303009840c1c2d00e007900300010301010302408549074004900040e200e688155070490f0110b20b010750105a03841c1c102d050024118a204940b406c100c01c06000c8030440c1e1010540f6903014184d60748900865486006081c0c000840c004030585552440c0b801910300702000d002e0511145c1442d40302c8900f911240b4903041125094904031611024001c0d0f058100040084011095400e1400c0c0e6102049446003041c015601a108030b041035407500ca00f1075141c0c00c04e555060058004001e002020710303105000c0d0030b82140b110502910b101c03824186001250340f1003404c8440360001410080c1e42c40c2c205032070800341748005009281e410390480008080c041080b10720424140e0205528044901c00c4255001069000804100f414012001940902000c03254070300103608048000c9000c000d240b64861001701200000c0002d0b4075840c9414540c0388108860307 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 450620818 1250 450619568 450619571
    0x1b0904030e0406091d010b0f090619080a1505150f061b01050601110a0f08070c090e07150e0a180e2b0804080318070f08010516081018 59
    0x40052542c2e00c2c8103010082c1034895001490040b26080e000140640618500305a4502400502241c4441084100b801c104403052069a66400300144000c0d5031341d070705503003c0d030340d0400046560203000542c8d14581e40161580d00881c0c0c1e248001d0f0b42a204202c42c040c1280f01c01071521402c904051003105000b03000100b04c1800c000b0a917000c0e10740c1e5030043c29800300790f0b91540107000c455600996075104281d098000391911900d1529500a06031410500401501d0002180010300a0055400d809071040032018450340d00c100160b10340c0d40d102030141c10079000c0c18100911860303019881a2142c200003512501000389009284007035100e5591400403010b8581610090071903013807013000030840000515100c84442c0701e0441c07400d00c1004060b81c06001c42c1e9424003021a5640094960080403a082c00008404990321a42048050b83c48441c0101e4942c00204010f0b1046d0015813040c02d010058251103600d0b00300440d2620806c0d102c41d001c10340602030500070b000b10107844600140c4034010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 450622068 1250 450620818 450620837
    0xb041e050d14190e2412060301050105030613030207090c11100516050702040209030a03113c0a020307080706021213181107231204092304060506010206091b090403 72
    0x107150049000c20060010108001b9003c410307400000c00480e004070084d070080099605110100e170b529403024000b4541c511045040b5400c05200304011700140807883c00600000e6044840035102e01203c2d90aa400e9024506180d100c1c80b9042c4030300d91054071044800c1501d0880220f042d00c85621542099030055002c00c040c056546080002c109000e12076034403011707840c0d07805c1540750402c0d5018940188030030b000f054400070210044501c0d0042c4a200180400d48013041c00a54a00501084000e405008200000400f80400b05604045804940a81e0035002902203440c03040d00c11200e4155000407590000e12582540c50701288500340c000c5400140c030b20003840d814449800c1840d0448600b2640b04038041c1100403115400d441d0124800140740d6807241421402c82ea00440c0601c0380f80c00d9130355141c100a80c400102c141c000c4c0404244000c440c1c1000d0800711702030f04003141c1c118050f11941003c0f445e13400c0c0005000c1c01440041d4140f07104d4201d004108020080090826410040c003000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 450623318 1250 450622068 450622099
    0x60d02030618072310030203011505090303070f060506100201060803040314070e160e010f140d020d0e011a06031b030c0702060c060109270b041e050d14190e 69
    0x103000f0b1110000b1468464400a820100803105c02c013003013540100750040c0010000c1c440346814040304141d09080c00b42d250b04820020078998003c20b90040c150619117041d100038400c06900035405040d00780c1d00581c1c0610030306000d03802e0314031a204100941c1e108110800114081207503144c4403141482c02d4981859031024190307542c92007590100100164201c500d4011600b103240810401d20a080c0781c090a021404050600300701c400c04480f40d030800041c0f415210810f641100c0d100b08618004000c2c0428440e546030091a005601503501c50b80301380b206869150000550348100b1742041c400094007083d450348980360b00054000d0815000a00c120401655844003801d03a103c0081d0060201d90f161044d8030066546100b00c444c14800d0810070340c907909c3c0e405101011515002203440c61a52142d2416080026075012280890390050003000d040100200324103103040010341d074036040740c14524007856062185440d80b4a43c034605410801c2d00e42d0096011080340b80006190850810055 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 450624568 1250 450623318 450623339
    0x1a040507050307080607030515103002040302180c0f0c0a0213090303060e09030a111005011805060303090a0501030513021906200703172a06060d0203061807 69
    0x240c10a504d950000d6040200d000d6151282036442a02070009034141500072005c034840c3d4550319500000c201d01c080c00c1a0121030a03044418281001c483d070701c1807100003014420002d400600080b17201314820001d4000c10302001c2c0c2128050440c015030b4074a0145143c0901a50350310010040c051381c0241d01c9004003580c0c0f040204004103201020114200c0300501c3c004003100c0050704242695086a000e0007004d10340042a40d04003109414071080c1c9001800c0041d107801200c90070301842c2801c08001080c0b10441840c0c0002d1038050900c107110035290201095228000d2207a110782085c45520100714a43c82904a150400c1e000300c122030003240c0680101c0c50307001034445058025070890f4070401095a000b841850940d1041d141d51404000309600180c44400c0c52001800011003041d91243d6440044101c41c542c00075080c1c4100610b0518102d83e8000d03c005000c0f5125004140014500e0b080218040004175030043c05411a507a5044007c09042c20030701d6509064400d00c0000b05545214 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 450625818 1250 450624568 450624583
    0x150f040501061215050601020a050c100909050c04080f060c030a0c05070b0709060e1504031212060303120f050603060a0f09052d120412080c010f0603140a1a0405070503 74
    0x44d5040090480c0c103030451030b0949001030b0800e03045501009a440100704003107080c0d0002d4504aa840d41615260341c0e0481d02e140c05c0f9000721100600e0042442140800400100700320345989003525a0001031010540d11010120744012180d141080042c04090581d8415102c951450802c1030030a5815154503c0f00349080314084082144283c00b4403030a50030800c0380761440400c95030380c3c00341d05100101e1882c2d0b0042e84001090546000708010020340507103040354072403414500c01c1102c10341e20309000b401002000002901c00e8500700d00f04881c0c02c058040c01d8400c00c000b9009002c140c13200342d0010000c02094921300d103140e43d50005440001c07410701440710004c000f2201400000110088030103240c44014075880141d20482c1d82030500c45200302558100c44844900d1040605031b030419250b641b01380b028420203075207000c84180084001d42c3c0003000382c9010b40109942c030010410026681d0000c0c50002d80000140171380054241e040100503076000d4480e05c00e40c0c04295403000480c4c6002070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 450627068 1250 450625818 450625823
    0x1303230a060b030f0106030f1202070302190e0a020712080705040513060e01061e08090c0904080a030f1a04051b0307120b04020315130905030a020f0708150f0405010612 74
    0x807904007205440c907040010b00c0f1082030100080104a07d540d86030003085107642c0380200305e0403010100708161030003481401c00030f5401400e101c40b49240303840411204111406000040000e580200d03c030080b0303a01c00c1d195004e91241e01982c64801243d019111041d0050400c0c081081c00c020100e40b5840b60303801008903203d100004038819080c641c041001c590140c100c0c4007080309030000c50108039500010741240824500b84150a52541c505c824103002d51100e515802c1a9508107120801c111034004140e5010f06035410000003290700105c005942e0b202c0d20040e603e0b211030035a10300300d01c1c0a078885500703e5002c1c80c0300e18141e1808103040d4101d0308101c0703040e404202081c40f99140b0007018010920721843c200d600714035503e00085c1e1a21424008612180107a860783c800d6040c1000c42e9101c0300489406c101140c1e122402501d00a40d240e151601e0034041e4011820001390040001a980c0d14520b10406449050384e40e40b080501d0f800402401070300c2c40d40d03d410000488086900601e01940d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 450628318 1250 450627068 450627071
    0x60803040609170d05040e0a0e060412030e0a0308150102010e0f01020a08150a062703061d070e0a020f070c06170f070e0603060d02120307030f051303230a06 69
    0x24980003d071408036580c1420202681c004407072005101e80d200c0d084030150b90024a0b025081c1e124a5602d0780105282588082188515402e04c41480303100c0e003441042c0c10b40c9560600c03800002e100d0303aa466416181c8000c001c5545600400d446101c010354034885807a043c400012100c00e00040c070ba10301140e0745c0740003840fa540000c00e080c40700c2d0301c40b110725401151000403298920350030021820b8421284036260804c141d9076040640c03081c6410075405a10541000f074500c894690525400a00003403800703410b40d00f802e10454041001c01329015088070314400304620300341d9034000140040e43c4070305000c400a0100304003081c0000d521801da10050030195035022190842080007207100b030b1000e000c032450702c10318900300301c04075902641018a00c541510020345903214000419080401000001d5000b401d02c0141c00c071008001014040c500c0c0666601d5104503440242a0381a110343c0885028a440814090001c942906800160040100200ca24100b00380701984e003403140380501221483d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 450629568 1250 450628318 450628337
    0x20603161107060f080408090d0b191802120c090a02040f091103040224210703050108060f0705040315090302010c0e100c0c050d03020d080f04080d0e010608030406 72
    0x41d446421004035070300c807100520340300d410010090000b860299045040002200c005010049080192404104094102e030b00400b800d18040e400b52900300c5100d01c1c050807201400031080c1081c0122803030303a050718880140385403250b020703c940092020301106092281783d544104035280ca20030a480340c410aa801a2150b05000328204034043c4d590241c03040c10b08003901036004515101c100c0e80c02030350407a07047e800070130f0014801e070508202d4a0803148103400804c0c030151801c9000c0320100c40301c8410600450311707901c00c1c00580845100b80980f1003d90300c41e00000301c01c6820b01166a4100c68142040c50038903a80e542c42607030000300314802d20442515404d100b0105502405245004403003030800450959084001c6211b503112003410b0406c001b6140d5a610501c0140300548000e07101c0608101c00140290401943e40c3c010f01201ca00014110070000f00808001400705014682c00305540c2c0c90650042e00d0716014100c01214041555a10040010300d6207040000b080209440d4880e40d061 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 450630818 1250 450629568 450629611
    0x1b0f071b060e030c010906120e030d02130e0c09150c0a0f150606020303070c030c0602130509160e010806031e0d1107141009080a0b060a17060a18020603 67
    0x594410281d140c00f07644118100c075800e80e0014206401d588044c6004e101c00c076508058140904050007030603007203001c000f03502c001080154000300b0311400000100360031241e0314800120f00340c00403a90b40240c28400d004416191510360150f02000341616009414440110580742c20009910001c44421910b443d400c01000100348603050059444201040040c0c58568040d480b17101c020040820020001c11010403d40205030020fa91600801d085455004840d00000c0b049454044c240c891100c0d03400150400b00284240383e0505025521205840030b1000196101c000180c100c6515000f5428980e1600080c00002c1c80866814030052000c548400340103414013041310401c00d800d4006400074461714112908030382802c542900c1041c060644524201c50350300040c2c020f000640508803011091060302c0201c1c5016020407200422902c4e6140074444002250302034503101c2d45c001c03800041c1c540c070a542c4200c405496a80c00d60396003414039400100a94003c1b00d082000410035081c5200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 450632068 1250 450630818 450630827
    0x32809060b010215060108061302130f050d050709020d060e0406060317070c050f030a05030c0c0f09040f0f060b3d08040803100e07020109060c020102031b0f071b06 72
    0x8501c8002e0014210082940e605608a00d00052030703541401640701c080b40268031840158440c5080e20f4404640700c0d404141da030716001e441c510400340c20b40b00404000c81d4501d41720306015292032340040104032903441d2411002c040d400c911041007a4981c0e40800003119030884d43c05620440c860300c400a880f90451401245484021003110b1851200740540d000068a042640090b5103044138590b40010400780020f1074200540700040460002040503001c016001507d800c1800d4111081d0360b02c03180e8401440b01490f4110340190586001c070401e440802c15007030f0020f00003800f4000c0442c5c01c1280c10046581108059020b64001c0c0350084c402c0c6800108550502c1d041c429002d134203000d0700c0c1170032008044035000f8001620782080040842c0d0b5260381454540c005146100300d030381141c9002c083c041d000308140c0304152400e5003441101c2001c3c0f40b040c42140c0c4140c40d181c129a500101c1400c003d580f0703801c00300d59100c0f006400c001d6403002c500c0501e55451258a10b0185206590410701d00a1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 450633318 1250 450632068 450632081
    0x6011b060504300302310f061d040c0c1b05040e0303040c1806030209011d092b1115041209181a0a0b040f0803030c0a0503280906 57
    0x1203500c041441031804551003030070040c0602c60355240150321101072220940c000d41c0d0901c80c01d1002c02d0f451030130006c040d401c100d2900460310980d810750b000302e50f103181c1607801150008840f000301c00c030003e00d401180b52540c0004501c9500c0e2400000c4429581c3d51134841090060309400c29842c0200200b0070340c50540500300c84140640c0c00f850441c14103036515040c1c181c0034000c468a0842c0307008020000725440e8800c100454004040070348a596840c0a5034841c0090102a2040705501000480009000030500141014015881500c0402c0c898649030344001c0402c440810141c08014104110208800c40d00201568901001c40c1054907142180128115943c0248602e4501c208041d003441c101911641c40c1c2038001251240f0141c202c041c10f2a01841c20710303130102c9800404a441011035026006450707020641110840e141c01d0030540c0e90101b00e80750703000b00c0410440c401003244141c01960f0000030320065180c000d4400b04031451503100c0321400020701c6039510900e4007030218900548 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 450634568 1250 450633318 450633353
    0x9080c06040c09200304020114130b04060e0613030b06030a060e0705010e0a060f05090402071406041e02030c12031b100c03022701090b1b01060501080601050304060506011b060504 79
    0x5034910000c1e010101380502004102030306002e1084000c00750314001c001103518000310010002c0c0403c3d25603050340c4480c3c01500030400020b1002c1200e01c0c580c280f5004a4003103800980f00b00030118610381d0b0380d18800e64002d02568040c060700426200150b024001e002207500f540018011132402c0c81d000404000907200c2070fa119113007060b400c200d880c1d00101c007041013090600d05181d0303940b014800b1901912400700700910280ca10f00c09092400c4000c02c0c09070103540b02d4141003a0745503d0400100c00f012448a0180d0702d03410603000150720340b404489450307144200c0010750b81021110311080c690300328412449080e0f40c01038400300b240b03000c051084d0903a400c00c0c0d0034114200303060580c130f4022030001183c000320454042c100c0405030f40c2c0940350060051041d01101a03032070402014100304001600c13030800440d800e01d040401ca642c00344080794800c11043e56a2400c55481d925024044c5c00d001d8a010305009400d0342212026507401d001c0c4c081c0c030340100008185400c2c94500729684110a101a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 450635818 1250 450634568 450634601
    0x61409090601060f0302030a06030213090b0a420e010609091107110118060302040504050f150d03030908070605090f0607140a03020f040906030b0c070302030a0309080c06040c09 78
    0x140502da411802e13118008007649001600d03a607500c081e0b500113007034680006c4d40c010706c01c001c607040b50180c5402c0700d150b0390311554045100740c5484100c81d0035034030b410010309412201c0402600a18000c00c40b6003103280c1c00e01102c00301c8549480f81300c4012069070b400070440a500f404c010300940c1d400c206c48500030242004100201c107900e2007907281c3d502400130014810001040443c00582c4140821105001e111945810707882d941c0380003030020740c4039203d06d038080c1d0b0400300000d0185001d441c01c640b241004c0c00c00840702a50500401c809691010b508a062540d5820244c0205403c0e1014008003449114001180d0400d803035020724000f080c20f10b115441c0c0c012801c2142c031a41c820544882000d402648a03219028170030241c004c0d000310781140b000c000002c00e0001d422032050b00844100c0f800f840c40d032051910f4820001c44180b20300400079004d84d0081004101c824460340c018050140500721030390402c0802c101440c1004010368054400b102c050030705000d80369141c4107560480000b41d00703 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 450637068 1250 450635818 450635821
    0x504030228020d1a010b03060301140105152127010c140a120f0b0109062a0c03020303030a140106020a051b0406210c0e0103050309090a0f0614090906 66
    0x59807000e50300004009018251010410080003050040300080c4207858050041940e10342529034410b41080360030620039030038880102141c404d90701c1507605079000600b201004120010302010303030707a102c000c5c01102110354440d1014804a01440035000b60701c121094080c00035146a01883e056902d081c0c3d4145074503010350700d445560460700c0406405902d205050b2079032224a001ea40000703289000040c01c80c2442c00400c0e02c101c09500072845100262034480c54242c51305011141d1259690781da10340040101e040c2807100301190103104081c0e1280c00d080304025141e501003410340c2c0043d035009e48a1511811404401241001420b01401651005150501c515118a9512100003040003820703480114407450030384464100b80b014210303e0100081d290180c40f0801070a48540d6001da4048143d44004140c99144a2000c1c4c1265000b40003942440f10002c10080d44075805840300300c00300ea65402d08980340410340960030042283e09400160b007960344050220307440c07004103641030a030030120 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 450638318 1250 450637068 450637123
    0x60501030b150912070801090c05030d030203060108011818080705012d020903070812180a0f0b0a030b0a171209010503180a0204050109020a030f060b030c091903030305040302 77
    0x80c29500c0c03c403000c440d14034541c41043d40345420058150800d0000b0350900314942c0500c1100d064a4040f510198111035002c100c10750228100e00041d01d8450002c1c0301980100030090020f0b40c40d80c11103922400c0003031186200740c003840080c0d4008030304032039406010440c0801c1c44030a103e0750545480e00c49004840350444206120030b411100e00000302d85074041001039598400b007001202404091007211190101d4640c02029a0402090380c1c04483d10600c44805034208802e1140886d15005485e2440c2420710b45003c01d00d400860f8940109a951034809425030390311003600b0018244110005020040512602e04240e14107202c403104510811240b100e59034460210b99200605403001c01103005884c0a250505418050181d8003d04000012821710b60507030040000340f0641d1803c001e00403100c2c1c4ca51041c1c503814403640070307059014400511101e0551004200401d0020500c112a2001c5500d0070074520290700300780c00080d40e031400c1108040d01000841340b0004d4402c80021400c1026 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 450639568 1250 450638318 450638359
    0x108060c07080405270702190303051e040c0510020303040f08070302071a040f0816060e0102010b030a051b06031b070f0812041b0b0904020901140706060501030b 71
    0x15215850000300010707120705014004083d20040d00d401840b03c040711030303010082e40304110324031400e944a01c600d40105044900000c0c88c1065581031406c610000c0c10243c80540007400e0040c03140602d100016000c4910700d0145650b03501c9944501141c00c1160b06040600ca40c041001c0c1c864402e5600400c240800302e0151580220082d6001018030b0756184141740803030420506c0d51113155115951100b501e115128000a003081d6203850b00003204a0b66a401001d0707940e01d580b9007001110010300001d100b82481016020aa010107000124090b1084404a840d00c07100d0002541d181c1c2202100c030f80d1070700c2c0300c0100b2155a2800c498043c01c0d820829203100120b1440e19580d946007200003131410810482c0e2110024640d0044c015031789505480c02407610407241160101c1d1018440483d0300c4039103c465074000705840603084c1c080c0c103001034403080c8002540a000d85605101400c1c46074940f8041e980000d0004038803400e00030401d14505000507003070307407008101c01c2d2107a03c40320f4a500b10030140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 450640818 1250 450639568 450639571
    0xa02030906090315130b06040c12050a0b0a120c0806041505100302090405032107020d1b0c0312090501030209010f030b0f03030c1e0c030d080711150a0c08010806 71
    0xc480203582e80d141c40000910340f0407841600380000c04904c0401180360416240c03401010701888a0901c02e80c0d9400c1004100c076641400304011a00c0d00e48247e410801903030000d540182d070580005416009800010062122a4010911070032104451400c10884840a1005200000041084d03050070350b90300d401c034649001d0302040c0d0b40da50f600044c6401903030a8071200440e0040c020b8125810b0908040381c40394084d091611366020300130904c0d4031520154600358882c600550207070021482351581122408017100a81003c0b00c0c0b00750035100410007038149000118464910300003054588400601050403540c00740e03040c0351050040e00ca040c0d030000601140307491180f03000140b020072200014490f110081946070981300118428038541c2d00058280305804100f120143c80d046132030412562404c824041a4040e00485500710000d0b00900700070341c01002604050252034030b00c0010741c0ca0200409210259000c00c0c4050147d00e5190f4400c00c1000c42d19032915068640c18000590341d40e000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 450642068 1250 450640818 450640837
    0xc07060b0a030803131529150f0702060403061d060c07020d0305030c1903060f0504060b0403030f0c122d080105061b0f030d0b060c1005040204060302040c0f030c050a0203 75
    0x1c1740c00003040040402c00c081d0004281d00e001c1200541d0a1490503890040914008050386003502c40203061401c0706440d80c146040b2451035161080003108030490340c1190808982201e014480440041d40c076000e10140e541400d1200405520300304540d51400d9006801030303074030344030801c07040c00582c460140b00803020380c142c10081d680c0d440d8075003804024032070041c560607a0f00032003119491159054004004a650503460340300f44584404c03c10040f02d1092043c1d08040c4001c01040000034065118160554440d0a00c0c1c10008180d84076205607642d40340f580c500240d019042c408444d1620a54107510180340722100d00f00c201c05000103800d030340f010b0180a20070000403d1501981568038295282401d05c47d09450b4210010a440307952900080058400c00707061940c200c0d6a810450184c803081a00c04c4002c01206541d00d9001c0c005100107070050360490349401d00440583c0340e5000c1d00c80c0c0f0751141c0c1d96000306070b281420010104d0b8500501c042c20044104070600c11913034000700381c1b41440e6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 450643318 1250 450642068 450642091
    0xb01150e0415180c0305220f020d020a080c090109050606180f0303040303030b030c03011e0b040221090d020601050a0e090f01060f030515010608041410050c07060b0a030803 76
    0x490742045070440c4903e6005512810b00c55000452203921900141405401d6072014400ca0300e50303564054800782200b01c3e165561050050000100d0a8082d122003094006400aa0348071310030340101c0c001503180c2e003014a656118100e41c09203401e020070b0040c010722860808000c141810000180d81d40710b02102c440d860320028400d40b83c0c03592003c00d113801c410001030441380e0303440e03807850003030094940c400c41140310b03004139000e0800318201030080512400240803007140030003520802d84014400402c499410944c2407004017903400c41661014400c0000c038540c140710307240c02c2c48414501500c44c1d80500445d005240104120340303582903104281d940070340c2401d00c55038400f0300c024903041661017070b00c040b076007402c0c000282c058800320f502050f00d0040082e6040c00c3c4001e841c40000d00c07028465280050015800140801d16500b80c07040c04550342e80c00d88140d404000e104030190340094036003814130f20001582c0070400003d8462a0144c13076058807154440c518503141c4004501000340780c030b115003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 450644568 1250 450643318 450643331
    0xc07091e0504051e10051e0117010902040c08040203100b0a180b0a06030b0a0e16030c0e31051302060c0a05120d06091406010e0d020a120b01150e04 65
    0x2c041400b10100c50070780744c1300d1020000c0000110303c3d60b94040911107840b103858500800c0030b00c0e200c3d0005202c0351030380a6511440b07034078140c00d18142c01e20301d056508943d5070b60003050300140c1d520700400d08806d401c0e03035030990329040070f00401d81002c0400d00c00b61340182c03070404045d81ca92038040402d0200c80414030400800001e07075403148080c114203401c3c2a8010300e84130380402c0b20750705640080700034801920f60701c220f15200c3c107194075070540c141d400400c401008600540030511a40122010000307901d0706030402900700300420f85502c40906440401c44070a400409c0981030742040d001400c04458040c4054201340c04040108260040044c3c020f107000129030010481c10050b841c81d440d070110413109042c411030710a4405812202001000300e040603000138084555009044540c018060012810340340c040054406851078000c0c41e800101c0c4020b4003004d645c89200c1ca070000c141350180c0d0304040a4914210111a805810180e015041e012142500590156448500500545d40001d09 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 450645818 1250 450644568 450644573
    0x30c150d1104030503040e060d03080a0513020d140f0316060b010504180207170c061f1d01031e0c09150902040303030e1c0c0201051c110c07091e0504 66
    0x40e10002070700d2400a03a00007030020400000100034811111400c00c08801900d680d81084000090f500025001544180100390012081d13840a900f21005448400714010b095011401601d92683c01f070f6840f00030920111072240342440200070080d01c1501841c907299a1021950600035646000703058140c0d94000f501c00e51340540103c4001d00200300030450110002e00026001e076020000403215043d03825025040c80000f04207a801881100014011658070940a0401181080501700d5002c409400c00074542820650004284040043e280065030550074400242c0c400e80a00b1500c8009010861000c684418212015101c0c052004204039015980c0c86110707080e0794000c0740c07030076200040000800d81c05030b2018441c01c2200c81580c00380072054001d18030060309205920042442162403000561080c0c00a0810030b0013102144078140c00803031440200c601c40200e8007483c480010310850386400c00c10081c4010720003d0802e01c41281d550040c06004040854459202600c0e0000b2908 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 450647068 1250 450645818 450645821
    0x3050c070302120307051213050f030a020909010b12160b0a02070503032106090601021e1603050c130e0304090903021903030f1103040f0206071b030b0f06030c150d 72
    0x71500104080620702800c1d46050300c3e036105100803103c5214403918160740402220070341c0e040580540f8850310b82444c000c140800032044024459150003440002001a07445181ca9030140c0c2c05c00e0000940801c4079002d01001c116004401640c0d0b41c0004d000c5030000c5403120701802643c18400d0419210780c12500d00307902c1c14440c1c0d048140c0c1800007181c03c070410016a00320b41c1d10101c600a0181407900c407a024051490800e843c0c0500503000002e0080c01107101d0480d0290b16591b82e011240c2a201300165048480d130150401c651503007110324078040c64503208000011001907004101310f1030300410100c0f41c1da44214400c8080c801e403071b10030010074180240581501306899112410f40183e0030300d0010024181d0440000a4514210329025a81030000c00c0c1c0c1e00c030b00c0e4854800310a54005808202c0c0769003244004403545040d08140c04015009015104003c40c4294591111410b115841e41d172095001032416020390710912015807269075070011640c020b4081c1c00003aa9889944200c0030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 450648318 1250 450647068 450647083
    0x4020d080f0304060b10050c0c01210f020406020607050c061501031103070c02040e07050303091c14031801080631061403010507140715230708090d02070303050c 71
    0x6000c0744080100020b22600d60841024003504540300d00342ca0b19000010b48207801000540c8106511105420101c0d500407244082280d080e0b1030400720841840000b07c05888a80280001c41c1e50089020400b0342d80401c2200d030000c0650130701c1c41c00c1c0000031061680e00c40c0b005014620520245035115402c0c0d00aa00045d00c00e00f41d803281541d64a004003018050842d0440124026850310080390030090000c01c151094440040140d4945034021040000545e041691002d04000d2807510700002490001100d26480440d0040d64480d205014405041141c008249040c000020100019562228102c212408a07145000e201c1c1400c1003141c440c903401e01940710003c514140c03010030b11951001c22008082c00881c02030090359941d4000b2214440c080303034031103e000300c24000c083c0010440d011a00612411440c00070318030000f40002c1d8000446a02001882c2c00038006120005520083c0b83e640806000024111040c100d80000c0d55207842d40b0014040020100c1c1450b560700c001d00100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 450649568 1250 450648318 450648337
    0x915030703151d0f190b3709020f0403060921110f01020a050f0f12040c050315010602030d020d0902130608211e07060501030b0717060904020d08 64
    0x1c60b150780c03216000c6610f070a44041c02e250000c0e0000c0054002c000b550040c0d442034455450b004200115200c3c0c2501030009001029070100740e038000c131201c0800c40310f070343d00656500c69000492a64195400f95552100e500600201070040029403481c107590412142100c0d80b101d00040c4055132400c10b5481607500100309512071400302c0ba03480314a54442c0c81d600b1009400001d8413103408001103114201d105880d10b15003c60401d1101d09440206038020706203c1851200f40c40c0b0349011a040107100b0310303045a040316807051840040c4000d00f800c010428811a901101090039410450065502d0040034452208140c00040c035124000040d045003500c41d80c080c2a020f82030078140c0c0b22002030000b90003880d140348100202075200b18100d20070301c0e002c04817602586d880c0000b2210020340740c4295540c107054011003000070000241d15413007618020350081c1e079240400d0402d40c4009007045680d860300e69540a010040c0304060740d60800940d0010346c1126801c9280d005881c010708039010f0700041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 450650818 1250 450649568 450649601
    0xa050706050114041401051c050f0d020d0f0216090e0f01110903160b0301030305030a0b060d060305010b01090e0f040c15020c0f1221040803040b040810020915030703 73
    0x5800d00c030090380382c011603104450910491080341c81c0f41840440034414a5880f07222000d648d038160307602d00e004910a500038000d880841d0042039145151400b04004900164007011040c03c40c507501c1544402d62543c0c52002e080600410080340012030350030b000d2503800d01d91b41c01a1034001e10040101c0d0740c20040f0302c030081c0030091003400b4100701a0040b1041501a004459654220107040e080003c02d540a44154a0640e4250780302281d054100402c8148a180e0b169031642681da54880648001e405094004c14120f0840c50010b00755600310007002e051005940040c02980340000c561988402d042030401540c2d44c440c2840a1400025480b14802414403e1100354460340404c0e0020303110320a075020586030030440709120343c07281800c103031480075007000c5081c6031300050303440b40440e1000400758994189511070001e242180e1081e408144132070400101049518010b0090f003841080b5903c0440c10140c3c80b001046007111185001020034100000040c803542c004d60008204c680420f00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 450652068 1250 450650818 450650821
    0x1a011808010906060f0f08060112020303070f080702041a0625120809010c02070308070206030a09080a030e0118020d08031009140601032a0f050c0102030f10080c0d03050a05070605 79
    0x10303e200180300501038408040660500820b51041642e881000c955242004040581c41c140d65220309000c50348080768540070400002c000b090729a81090542c0380201c10160755580e4620421049505e41044400352103208404480302d56120300655800f01e20440b400ea84103149400e50700c4008204041c000c1501954549884441c1e511a079842e20031401c000003048035103043c080580c0d4035809840000c2c4504020002180181001e001540d0032140e020300121b5203241075074130300c0c8090f000002607400280ea18114000414002d00036004c0c281e0100c20301698046468000c5580118103040150801e030000010600c50181640003400401c010340b02000380c0701d00c41e114071411020a990103800607041181c500250b42e2103200070781144400015101c400d44090340306480c0010500742400910a0511100e10061004e0004603c01c0000c40c049035111324105c1107842922081e50080015503019140c89070060f11418200e0750400d0300f50801c142c41300840d250071a8213104092004201c6807c100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 450653318 1250 450652068 450652073
    0x1e150a05031e0c04060c060b0405090105061810030303051f1214060601080402040b0102071a0d0513082209090506040b0c090603010b030406140403020d09091a0118080109 75
    0xc0280d8001d8100ca500d50504281e89076502906a01c02d441e0703851004020001042800e0082403501c55961242501107440040c80001504440048541b44a165120010020030389060603401d4000ca1131440150610300742411154101c007001d00001301411b0741c3d00013040817070f806159080038110102d4544404940c031914564210768072284211104c0d5507904d0580d11400000c9031451041d0030695403110141e40b00e408100141c44ca030903102d0705600034510b01194500c0e0848030421051940720703030966501041030442c401c4800c018124070741c0c002c6041040d03002032000c00c102c80711f110f880051070b4042903411802a01ca540a0f41c03102441518010351501001000b08403544614011202c618440e51031005000507807050b44991a40a80108018010b51801001442e0440d008420000d10b12070242c555a00c1180300750b90a9015074401e41202d8401c6500480e40400f400d9400f0091001500b010704480004100303c00b81ca040c0f1900088502c40030001d04d05a00040100d5402400198000d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 450654568 1250 450653318 450653327
    0x307020c19030501231504020436141914071205060105030601050702121504050303090d030228142106040204050109150e06030106120509010504021e150a 68
    0x500c811200c0b54209400c0c0c0800400d2051403003c401d20107651304030155100d100512620800e406c049038050fa09200c08075a00002903803101154000e0103a045034207829140100c0c0030f81c1c5280040da07003107041483c1c11a50700d031088040b50304801d03000000d42c28000e08040d100041e0402d040f60300c000000b4801080b200c26801110381016a0548104006903140c441c011900c0740300c100e039002c1c0441e034104223050041c10540c1c0c03e8000c43c1d81c84000d03180c0600401c10174503002c800503601036855900c0841404480320052084c107001200c40d0404614094040c0964004018035040720540250b202d0074244086006261001c80083c00c00c0606a032241c0507030b0910000c200302891040703135501e188001640c0381083e108840a03100140c60301c92185103050400340306d220514003141c04100b01181c00724465164980078501074a625200c104031801d600b40c048088600051000b42540c0c146028000076803220f0109004080b0400040105440c2c040c02186da041c00f8109a01016800000d010303034510b610 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 450655818 1250 450654568 450654619
    0x91f09060b0d050c010f11030309030403030f0e0a150e09100f050a290715140c070b010b09030a0c0905100803040f0905062206031401110d020307020c 66
    0x220020400c00100100307100002c02c2c0e01c64001d00c01d500280311138003250f00600e18610440c10a01d1300d0321002c0a40c1e5981c906540040d18903050310362000c103044c02019000760f98800300c60150b191101819001c8000034841200034400e40c912100c4022805000d00c0c400c4202039100701015243e030109080501000107018841e00c1510f6000c11080e50115281c54011954000c64000340601c3e2649590030303441d0035014003046480c0c400300f0401c00c5620001484068800006c2c2d2401da00011041c070300b10108001810010440e103112042004044005410f032010b1038191b4800754100f944500c000030200e890b25507120301c00740400075000000912b049103074114a200e0700d0404e101050095136010416924022401251141402800c05102480b030b640d00c806d6104c6801004100c038042980b401810404e4030551380f1491549450341801800907001e0044100301c8070000130060310840718412140c2d0300032403540110698001022132841e52080120002c0c075030000f050300e500c064045007041152400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 450657068 1250 450655818 450655823
    0x3090b13030b07030209060937060315080a06050601020106050a03050303040507060c0201200a0c170705030309010e090a060302100f0206090313050108040f1220010207050a0209091f09 81
    0x40540054142c81c0304e4000d403444150041c24050908220300304104400c03580783c000001d117104003031403c0e03041e01c05139a8141584490169100136541806030042c1500e50f0308800724813207225000c04000003400002e540c0b00c030300d800c55000505a101c40300101e014011540c0036035030110042da808010700801000542c02940324008581d03019560f080162a281c1c222000640030640901c2c80850b00d1010010150712840890f0943c0c07641142e5a681c02e003040420780100c20300920b16014031520300000c00c46240070302000c0780118140850000002c062803030514450780a140a0350114480c60708070707007102c00519401420000c88010042005040c4260401948011b00c6100301080079400003100b01c0d02206060358501c0c540c24200030040d141c04d00d01030030484049045603980800305840007500800008c40341e441a50480902151140c01e0000499100169104105400005030002442ca0089905841c40c2510380e903008941414841c11140c50321481002e00103c0043c0c1c0050740c0f110300e0051 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 450658318 1250 450657068 450657083
    0x150901060f030e060705040b070c03060203040f0b0f0105100509010201090c0312081305030711030c03100507020c120705011b0b16030f0209090f10170c01091d1303090b1303 76
    0x1d4010310700b039a150700170f6401c00c4c0070610801052114000181c010030049009881428486941e035a4076400c903030003181c0548140343c00400d0301040111511019802100320f02c0e0340380c40c40d4144000500303450001003140051110028030282c4990003904803000c840e4001c90340e000540e5881c10060424004800c8480009d6407405c00203001c0003240c10f4446c01290404002e50518446030384140c64400000ad0956061140740801d40da540e40800950030904040000820702d41802c0c0c1019140c00c0c41c8038201d074800c0d0002044440380d0040003520708116072091805011900c100c0d22076040e14080b250016096009210801082081da01c90846081c40035503001c000c0e481300f103e95201280104685190b100d03141e10040b4428600380b0b0042078102c9050343e400c0c0a0705540f04100ea4111039911700b01516a00044011031b0039603040b00d0300c01c004050b80b00c400d4000340c00480b0003aa0107140100b0054240f481d01d92448207061040018801410f4000d90507a0b54000c111528a0b15140c03501c42106c854 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 450659568 1250 450658318 450658331
    0x708090a0f120f050c03091302042303100c02060f1b0d05070210060308191412190b0102120a020a080d0518160506070f0b011203090510090905150901060f03 69
    0x12440340040785ca010039608055800c104612013007100c50440e060303091001ca9008d10010400c840c1c22600c0c1d81c50342c00201354415140100350103050510711007a081444892402400d507011a40120702c03d0303800707080500401143e41d6490011014180c0c09509070101660101d140748059a142e40040e0140384503400702c030754a50800402c0400d58500d0300005246000500540c594000001507103031084509040585580018080e100d102d81c2002280d000e12050380f90a02c41c580f1082d0001013010740100005201c407404c0000040d66444040c0c10014480300005440505c540c824031501c031010b0b038000030b443d9a980300303840410007134102660120038100300501110340d18140002d114011900841c11480b180303290108000b03150700005000e071842c03154989800009203804d49941d003e17003d000206440f5039654107004040c6115600400d00030740030070141c070400340d401c02c803c1411500e2038000801d10b0303a900000460341c80e0354510541e42000c0e403040085855500400011b0107180703107030381c208400b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 450660818 1250 450659568 450659597
    0xb0a09080f030f190e060c070501081302030303011203020307021c021c12050c0309060d0c1106090a0b060d020405070e03160e01120201020a0c030803060f060705060708090a0f12 78
    0x124815501803102c2d441013008112080c40307925090302c11038006414201900940c84011441ca41c0c00307a400201560403e0380c09003c0d030b6070814002500510040a0305c401c111543d404280e0b240f0042c01648140e4840000b40300416108000f100c0c0b4075540a000d1040c00c1744101c420700016000d03050308a10560600903142a1a00480e410225081d00005020310030340300200c0549981d401103181840c1c0e070104101c000c8041e00c4480040c445911030240005e010203182c0001844844403000c06a0701c1d810100074084100390001e03444001c3c9070403040b00505500c4950000d0b02c280d40700c01d0001d402500b031204105102d40c0110107409010815000d841064582203903030303402070300a40505c00b08000a20300511051180222296660388180100c5502908031340702d60044440c0d0707900403280d0490000400400e8180340700c2c5002007620550300542403c2c4555030303803a15900700a0192040007002d40014052401c1081020b1625400c5016560a44a1410010341c00c00c0d81407809804070303500901c101c0d074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 450662068 1250 450660818 450660823
    0xb010305090615061201080705010e0d0b010b1b010903110c01030603020d1205041e030201140405130915020a020114090a021003150b1c0c0e060f0f040b0a09080f 71
    0x20030001c4401500e0203950304a0300718054241c50104036004003080c80b90b42103101d400035000c1d0203058084010181740e0316003c001009410741402807030081c0600441d1500080510100074151503e0b801c0d4240c0300c1940342100c190070810380301e4040349076081c160745c03105140c0c003d03030541180500c0d40b00369041c1580100064007a6039042c40001d4002d19003061000c049184d0b00341010b041e002502d401ea1400d0382c0c0d82c0d0400801900044d09941080c0040c1c0c0c02c00841d0307040174851810744100d10129051a00d0040018a2030110700181d403d0551244601400c03c07141804000c000116840d045480c0d05008500a00a00082c4031204440c03c101c00410404c8000091510200e94020720b041740000100c20110040d001507004480c894100842c0800c2c1030034280003a020b080e22602c44240807810240d12039050790901c500c0344050003100303261100252643c03130864140b0600301e41580d94803c890030401e6494441c0d603000000020b80800c0c02c52205500c4035014044400ca001100d0800310009501ea4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 450663318 1250 450662068 450662071
    0x2a03100e160806030307020a030c062c010804020f0a08071a0c250e040327140d0203070b040b041d07120e010e0a03030e0f0f070b0c1e030304060b010305 67
    0x41c00c400e40585260029125200300740e4030140250580c4e043c6100713680032440501c0250811201240110011301840c0c1e402281c0c8231030104094162040382d009956010700c1c00705e040345107a04006c10500082c0654030380d85545011003401401440d04299180704103521040503002e0322000507105c04d003030700b40303240c4d080d0581c0d80701c0c0d02242c041d001d2500302e0b00d40c410403086101d0300d4202d448503464000800b243c03030032841c9104034040d880b59000c19050344d1403110300c040c644840400c0000101000e01c15000c80004182a0b8402564210500c11803070000910740b400c0303640400880036001401188040e03000001d0011100f000c02003c0c1c89904600100d0301d5082d0440305100041c04040e42a1500e0500742c010700d240340300c1d590000520035135544051b424400c41c80c10a0300480d46032010040c030750104001200001d03001c0c0c0e0207050b40301100181c442c0c50b0000751058404030480480e2003211024103011920b40345c0080701c6080c0400c0b042c1c0d18515101e410032142039820340c0c5408000b4186d94000c0c02800d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 450664568 1250 450663318 450663331
    0xc090c090f0b03071701141512010b0c0106031b0303021911010e04060305011d0c01030e150901020c07060c110a03020d1401180308090f07030b0a052a03100e 69
    0x710707000d50810000c2c015580000700103404020f605010500e0f085904100d8502a01d0b0084851030111282401d0020004e1b603040300c20f4004004002003144003a070440c040c3d06558107442050b42d03600c0a000c10a01418860b00301a0107a59400d540c1018101484c80442c1203038403980039074001c00d01ea0809011030034200300d4080c00b800d05030311128149601c2080f84050303800c0001c00008031035480303071111400c54100c990391901200c0c03040044100320700204401150100d091030144560704030000601e445002c03d41c60024100c407070401181842d4020340658070507183c0042201c258035515240140600b02404041d10104106104421103041c215011030030b880d005842c160000f109a5a131b407400800300d6526607150355a4080d150046121040710b954501d01903514070000741096491241400b40c0700c03c083d407455005240070000901da250040ea400352070b0b03a038000782654a0540c2c2c0f40a5400c00c55507588101c646006046040081a020b1401480c0d0180c03101951902c408403040c040e401a9043d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 450665818 1250 450664568 450664589
    0x6090609160e06030a0c0b0918060a05040513061b09091b11070e0c0408010e03030103170a090b1903050601020a0c12060207021314070e010813050a0b040c090c09 71
    0x9000c41071100b42025009540901201c08900003511643ca400f0b4454109040e0b0100005020030745c0c4c50310311020041c0350404660104a0300b4000000b1b13031501c0d418441c00740603a0704e5100013203002c9498507401201d82d801000c00d10103200042c00820a41096170060004a03580d45000306452100344034804071003121aa41056854210302c099449941c0103103c2d28030340c442c3d848007081070b0a04c47d081d54003500301c90b090b068540d41400e1072142950745001503e42c0b030707070b1050004001140b80010141e18070a6400d0180c1d0340c2d0310400b00c0271a080241c0d03412501042c6400241c11028180300103802417850300c0c40d80d0400c1192505001242c90340510000682003440a1000703001c562204e459282d1624410440145016042d0b03000c10501c0881105c0001110b03540c5070102d0500f02c1c004060782d4016090300c0c21000819841c0000b84c01e955020701304243c61500c1c080c484080200801000b02025002084292503150a20b08088005158080c040e0313000e0030903862515050081c43c80000781d5012049 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 450667068 1250 450665818 450665863
    0x757060c020d020f2e021903020c0106060503100306180b010e160c050604020603090717010903030c14121008100b120d08152704050706110a023006090609 68
    0x1044261702c2007410005074010307801c005020b18910500800c4103c503804c1c1e200580c82d021501001c50031234506074444c005101c1c0070410420f03012003041d000015242d000b100061100e0122450303051702c0c494024010511580340c170020920260b88154944146c4821404110904040c4800c80b51400800c000804652080000c1801840d0500142d0352240810084030007081e541c1c000401d0140f441e101300c0e035499640715084018190300d030060003869007a5082c01103821540008001c02c0f44520680120b0003045a0042207452003282c8920000748040400c4989011070082e210004105460380c55100d4010200b50707030061000440c0303400d940452511070507401da80300b5088401c0030f4803500d034450b40300c2180d0011480c24102130500240a10900305032400c85d00d054a4072328646580c0ba0071a40502000510000426000085d95201d15a0660f48044020b820070280c0d20783c0c444407035440800c0740c1c01035200d181c040030001342140310b02141001c1711040c0d22008841511a03003101e04400a207000e4a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 450668318 1250 450667068 450667123
    0xd1b0536010c02240c121204030e03032b050106091d0402030111040807030b0603120a03240b0901030513050d0c03050d02030757060c020d020f 63
    0x100071240040e2030100010011400c24142402802c1c2c00c085111380842c600c03612500800c003540186064512461a04a241c0c0800f1507001d0000d000600304640041001c0e528bc40500c01c0d12000090881c0c1e11b040c0031a035410b9640c81c034080441000d6035610341030000030160310800410040b5035030185c205644a030500c4800201d54070090081c0e80564944c04400e10020401c402000200100c0b00541507603400c5141191180c00c02400c501d200c0d074801c620180c070690051045504412180c00d000811aa42080e814202511005000c610850600d80022030741903180c0204400fa40980c2d00308265582c0041c42c5807243c40f21b207406415503100741c1030101200d004d581a481742d2800b0f81032031400c14034000380800580c0d008581c5140002c20000700c05481c0201210740030605103921100307039071080503070482550852003840c03049400e06040c001c04a48a0000394690180c82c0c206105001d454030110002e90b5401100542c0b00061262807185a01d03010045448440315410980d00411180303181c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 450669568 1250 450668318 450668327
    0x9070c021c06020a090602060f070c05100528061a130902030a15141008070e1203090a060503010311040903050c0f060601080a060305030d020d1b053601 67
    0x85104a8110a01200c41490150840e2184640314400c40340980c2d115121180102002c0301a4800d109640c441003d001a507203042c1d0703e00758000014902441140c1c0982880c500c0c00421901c00000c461030401800002007100081c55903444920042041960340000b01408540c2940b1440c0225030705064260a0045004000c10354032060f2280343d1891500e03050769908a0344240c03044c0c1d520990703e001034144040e54003540c0005051500465a4101c0e08134041000e03240c44200020412041800003543c16000b0800d5521700400500b988020b40b502129195583e40310b5550300f4440c035030b4100002401d0b885602168140c9500ca8045207420201005020140c1082001142406424401000f00301410000c401c81010418014030803030600b4030002d0a20030024140001040c1405010300200d00c2c00000c641c0001080240140e8032061140740d0001410307905202c0e01c0021064204142069108002d001025000903035846034040040b0345205200c4040d104c3c051b840c2d014651002d00358083c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 450670818 1250 450669568 450669587
    0xb010504150503121b06010e0114040908030f0916030311070b07050307030507050c040509030702102a020f121005060a030b0a1d06010f0305060f04020307211a090c0a050907 76
    0x2c502c502c2042405c0d001444d061070f000340c002642e00044c1c000104000300782d0b65001401c0701e00980342041821015100c809051100030003401c84000c0d024046080c46008000f03072280c08041c096032550384c0d512440c004000d400e400780d02c00107038444c802002c118200d00c40c08807410942c0c0070005501d0140d065405444caa0044502070350760740a5405075651a440d01c0c0100380c800c554450186d40d03102c41900c104580844c030f1211210030801d00c03811309160a40020022a1100f2521801c07001408080c400541c8012400078107035008000884030351024900001c4004400200120038885940c0d4034003840003903a1948805404509142c010a449000c1c56014000200c400044001c484401102143c80d0000a034892907070b0381c904020402c14030405015442d084149900140441c4c100754000035034480c428042e482803801e6a000400902c5c070142e9410800340c1d03100d858122980101280003a0111084846618038011503803296160b18151403008207881000f0b0845042b515015811101d00c0d80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 450672068 1250 450670818 450670837
    0x5010801140a110403170c030f0703031404030e040908090607060b09090a2409140309240d0b030307120207030b07032a030603080403060504030306080703050309101b0b01050415050312 81
    0x4200010043d0711f9080c802070848402202616558240c1484d001742250410001d1081c645076103405e0000090780009140c034143e804036404a000d90140c14280c03018428a07a5a5601020000b002c8042120300d4100c80450841110002c9013640ca01c5400d548414031220001e1501c4d41010b05440080c0348603428050103c04880c000030100c010b42d650f40003040808003c800d59078008202030a9903d0402c2d41d140b024504440f440b40103454010200c1d8540c022610420f689070303194440d0350301c5602c04000383c5031455005480c0040c45911100c001c1c6d143c44803808190760101c592400113900714024003c850304119504c46418039020380c002c0909610a01c0d039014000c00d910f510f07000011034200005030014500521700050982050300e00078080715055803060417541c11039501000810408010f40d241b440050b503001e05200c207100700403690000802c19000540000c2040c45043c40b40c800f407410f040c0e46c0f06a4080240103c00102003003464000e10600c2e505131310142e2200c41c503481c844042e01c1c00c2d89 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 450673318 1250 450672068 450672113
    0x3030507062309070f0b0427140c03060102010c080403020a0b06011107080c040c0c0803010e060f0402121609050307170a120206041b03031710050405010801140a110403 74
    0xd000080c0e91581c2c0030103403541251944594820b0200315a0318521340003d000403503540c0d2030316203031051101c403d40c6812583e40030005030215850600340160800042c00140d00c0c20340101c0d203000302010020750401e03104c85005600c1c113003442880c00e00070b0307800500641d01a00142040c52460380e90016000000b45460b0400207502400e0516820401014000e450000043c00c0d0b0580c00074140411035100c081d18408020120115002003280c2c002100c1c1580d8014051581039618840465080c0211480998115200050402e890402000820300410b40b0802e12451180c0030300b0200ca03a591140105a45504021420440d0224110815403403010034001c1d0f800148542c2c490b141c0c0034201d080e0940158101d00100000c101004600c40d0a8810f0341c241d201031141181c400801000c2c0e41e1110301001c94084000c52584404400c2400c01040010828000c5684404103030b030281c82645020038031300e01d1000200d50038a00c01d00a04001c420302c0410070f800c00385562100070038092104111500310 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 450674568 1250 450673318 450673361
    0x307030e101416080c0f072f09100506090120060709090207120e03031204080904110301050d0209060a35010209010906030b0114160506100303050706 66
    0x240000d005000e407200700015040600e003440502030340018070400d4040210340e22000312070307080064280c1050401465a403500303020542d51707685100301c0d440582038581004642040d00d800b03245080010818002040c40840c0100911a80b0102030301c408103000c1844006114908011000d451000350500d8044124a2800401c0b03103140011004901150840820885600d421202210040c5407130b0b01d0461400019495400c500240418402c082003018032107214039540c04c0050301c155601c0c40318048036608091a0801080d48080078240c080c5080c0082004c100c468442601d04070380c000303022018007014907801c0042c1c2c403e004003020f500000385c02001c1404001701c0d11460000f056491000400040000c0c1c03070009074407a440f401d40b517030700420000d0380e1641d100704001c1c2151103604012495a50a034010303150501c02403038103011120003003140c2c03801103640c0b02c1801c92140508180d550369140c1048100500460b0300024000c50010032507213000480507032200f6512101d07040d41c259403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 450675818 1250 450674568 450674591
    0x80a170306100e0310050a0c1704050307020d080f0c15090304120204050403090b1303032d11100e24010b180406050901140a23040e010e390114030703 66
    0x480d94140c545003007c43d9100c2416216941180e5142c081c56220110102c140c641541c525541c2d00c02c505000380102903159000e41085a00c5080c0c51401c4841c07402d0707a03201c01048141c1545c1e01840c8041481700c43d040c4d4041680f000f4080100c5098964441180d440e212183e028480501009007040f4104050401d0011700e03403204101074076082c4044882c03807518501d036040003042601020035100200c1d101906620301c0c1a07840210651020542c101f8410804450710a00d00b020078802ca806400341c18900380003c1c40d240460428400e002c2648803400919011006003001002400344071020082000b00062320704a1440729200a20014800b0810b00c3e01d07400480d00000d42a805000c40701105484ea00725407902070074240160030001c0d4515480c620f105030b40c08074050741007581400303a95600a010340130002900120180d00d24402101c44007900010f03d00b03041040d880801d101c1d51910aa91401d0740b903907003101d20f40b008050303642000d250840c99140c6807960020304040c0505550316102d054 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 450677068 1250 450675818 450675821
    0x6030e1204120c09110702041e2f04030309061b050a0c17011406010e010e09070509090a1e020f070c060801081b03060708100f080a170306100e0310 65
    0x50011810070600080c03862402e682e82151075000441c00c942408030783c0d90070a400c54203485540d0f070100c0b00400c01069204012714401420520504541c0c1045880c2043c03401e99040e07074621400310001100c9607480e03034038008400d000e6404000d00003400081d0070070030036200701400c01c000d001c04552031601420701c0d620301c0d10381030048030103e8560400020401c03103041015070b07018015a44400901556195070341030180950001d0486041c40448100030290b64400c00180f01c2075840541410320504114001034100c0e005411340610402d0003400048501c01507009441199000d024007044c80300c1524030b540060341084030907085000c03092080901244021121030011302e01a1103503056035043c061924185881c01190140002d095450324450741c80010f070303181d40b0101301e07e0302d20082e48600701c004010b103156600c400c0d080c1c88110000f041c01c0701c3c040b41012001e80701d41901090004145d003020800d0104444084e4068040e4000d0340c841d0b4040c880700d108410b8020306072080303000903268010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 450678318 1250 450677068 450677077
    0x10e031f05071d3f01020d0c09030309030f02060c150109060f0e010e040501020408030706020c060a0501120201080907270e1204090216060e01090615080706030e12 72
    0x8691546480510a000d90040300c9011400c43d007199003d1040b00240204d0b1307131241e5803103907590000390426928078100c0440c080b003070541c4240724105080040e5107045501070b4205114411004c0d14240d400803009009401e6101100d52540300c43d0b4040d03195456000050a141c0c40680e080b0100b0021104101000d0090040c0684043d00d620380725410310401108443d020f800c4011000c614040c00d20210810351074a604464003008582e109d03039518540103002e409030750720100103072002080110800c140c6070068035041429100f191491350704c8901d00303020b990080c85544060103d00f1041c0000d54400c0d040e90794802c8c000011075000d655500155a04c0c0c03400e0289e51340044128a140c40113400507400354010350b05400e8002d15a92010031850001ea00c521b114440d1100d80c0003c01c07050741c0a00c002c4a280c0a6000581008820150010103010f0924214212405490050506000030201c000d01c01030f951650000c08105041402c1a002032070401059002c034801c0e405012100303c2c5200090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 450679568 1250 450678318 450678373
    0x1503020906160b0c0c0318030709060f181a010c05011b020f070911092407030c0b0703051618030b0106023a0c0602070212060108071e0302010e03 64
    0x300590000d400c2c240d22495003c2c0c0004c0c54058204840d900444001054404185c1600c1c00b0015240d01080040e2416030194052490726040110000f8042480300c0e10204992800e5902c1c40d0280d21100d0720030858001c0c0d10500b0b00503a552103242d002c0e501c42e6125500c100e110300000111003200d410210b00c10f210558024005034031050540d410302d0814412340c0c0040c0f20044062000c1c6142c40c0441d0f2050180c8406e00380510703608083d421801c1c0604d44242c88450024030544d6aa240d03604000b4010040d55006882d0800480702240200d482445074500c01c0140100014131421420011624600039840091000860001c00b0010440c1e030701c020740c020a100d03001001e00c101c02c50032070384004010301540301454156884080907529400c904808901c1e0074a06100c60700c02c1441e001000340204540030b900200c07845542c4580080004099060703072410012078110558440914100d561045018a520115191308100550007014a11400035005003070750501a00036482c00d000f07210a6084 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 450680818 1250 450679568 450679597
    0x8120f0715150311102d1403010803270102070e100e010806040c0e070c0201050a11060702071e0b070b04050f0a0302030703090b0a1e1809020301030c0e040209011503020906 76
    0x286040d503c0d1080b114005c145003414030491065031a40700203502202d0346031403590071081900a0104c2e511a850030b415014044200340c0d140d507141c000c0d03150349801c600c00042041c10400040c40c5020030550321400c0000050740100109401c0c4050462065400b0f04118021040c0241c0441d00050030034840d0302a10952004041c1d51500b130a0400301c03c0d80d2544018281034020090000306a40100c1078038100f0340a08169a9668a910741110a018989840303241030042c54140312116030b000c04d041d0200c440f20752203044540c854074031300c1c00031850301d1140e650380500811440000a000c80340c0c3e035920602420940e100c440c020465541044441ea0040340141c00020b114810950004a14006000c2c1e40402608020142c040608480c80b480b6100ca00d041d2210400c00c412071103482c0c00d5440b5034160112010b01980d40301e80ca000303034200307000486400e0b1281c000030609400700c0305818860741e001014480141d01e000c880300190b012000705101056020891502140c50315001003580c0c401c4581c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 450682068 1250 450680818 450680843
    0x20f042d181b0e0606030103030305130c0308030703050a18020d05031908090f061509060415060507051504171305040207080406020618030910052208120f07151503 72
    0x26800b1071400030307000364101c4040d10b4140411915642c050343d041d6980f40c10001607035220101c000c41c00c40740b20040142022251080481049941c0001d1801003030191001d00081d2075002032402610b541090568a00d98418020307405450002d540c00300c95070283c0305492400e0550342580c40c0e0340540001c4a03012440300d005014a2401c200095500400c030140a8034080c2089401814202040301e90b1a21855401c000301d0126900e9600c035902d10113001d007040151507074601c0e000d0030a411090003690f00e0300580b408000c00d01d00baa1030303035132280b0f9001a411500e40d62070000340100b600048170320300c07119044010110f15a00d079071000702140b80c02059980d0b151840c01900900c3c009004204403003265a009055504280c00010346202c4c0c5000c44000e0f590341c048003c00c80d06030140d80c4c03401e20040c80c3d1180741c140d02e42171160200c05030303034982c1c0c25118040c1d03072681d00031200e00c2216182643c541d010400c403000b03d071124105c480c48500701000410200340d0904030701d1208141e5042a20071615510 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 450683318 1250 450682068 450682103
    0x11206080a05071403030f0c03190e0f0102150f04050304091109120d1409041e09170a2c0301090b01090614090a050703020c07080a020f042d18 63
    0x700c032000b071100c82c134030503010100d0ba00425100d002e000c6580c400400045001c00e891041401a104802c03040d0113854854040d0752401080d849100002d14083c80811030032131525440403520102d500c240ec250781c0e10703c6c0c9502c124510b1039840108181c81c0b0380414400800c49000d540a159800340340b5080c2d640c0c03140111410450000008039108016900540d107450002e070f0000440c0304516549a0484d844180703180205000d000051410321100c7c4030b690154165010740d50151b10b03614080d9010203083c00e14403c94110a20840c46040b000c50098284041e030360452226000c200c0300401000c5d1464036001c80820700307451003603400b220301c1e8064800521006400d4031602004000030b42070031082040c42004142c0c03882c2c01a004502032500c481c00201c07086e000c1d404035050200a00f00711100c190781c4031030b2161141b2076101708901c122038102c25070510f07160500a20412188103082080015102d009038032a0a442001c00c0748200d44504251424401d41014484010f004104e0020b0112411 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 450684568 1250 450683318 450683323
    0x40804050a08030d050c0a08070c020a120813060e061902070308040801020a0e0301050c0a030b06070c03080d0c08060105090d02031c02071814131109010303110d031a0f011206080a05 80
    0xc6c451a1b861005116003600541d0040d0842d8111095081c4110090712600200715510184d400c05070000000600c1c180800c0040002014400803060601030766540300d070030840c0c00c000d04205080c0d00031014414008240007203000f250850210340100c03981a0381c3e80d9226001c0360090750000308181d5020988661850300f00390744049580e0214000c214030b01d4030941403503141c010401000c0400d59200046503454442c45e04480350142c203c0301643d01a5547d142401c50f680c00304034610401400d00ba010500b56008010090041005840740c2d410096070409100e405609590b00341c0e4140f00380300c1b1070040e200d01114080802451036025008050500000031002c5540b000c501c0029072505818440c50b020710341c0f4264000004180c0b441500501c1c1c00d00000b2b0b2030030201c190341e1154143c400081003540085070f00001404102c21340300807030f610078070603411607010000c1e440c040c0d248411b50321141c3ca44a004480950014103095011800880071203085a2194021034041c0e0b20a09689040c00b008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 450685818 1250 450684568 450684571
    0xa0b030a0f06181b1407111e01090b120f060310150602010e0303040807081b030f0d14040c0303050c01021b01091103061b0901030b0616020109090e15040804050a08030d05 75
    0x101003030411a40e40f404d0009050313a14007400d041c5e01e41004500d59081003801c40c00009620401014240c105010400c0144611214100b25001c90303480080040d07503071600003ea60301442402203048140d07a030580c00d026004030041c6025414065000c4c9071706e01c5011842002d003d000040704584803d03060650107400c41c0e0350000b404241d64000d00411001460341c01c00c844449610484064030303040c0307100c20116601c402c591030444502000c54602d40d140401005440c0d0310a031000c080c440d040c816042d001c801c0308143da020307101c103006e81d4040c00480e00410040c034803600300c0d0b400103281414004001f40113110f8070202c000c403070751203003410f60512521200c0002210740c120302524950a00110f00100c040c0b50070903c109441b0081092030281e13020f80d01401800d5000f0b020155581d0004000340040258501c0032804210f110b000811090b00314030481e881100300384010480703510a0340ca0a2001c40d0010811500202c0800004c1030545800c4028002004940c000b50307114003400f0044425140e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 450687068 1250 450685818 450685841
    0x15020a0c060e0118020f0409050a0803160305042a1d0a0c0212030f0c040f03051e0d02070303120b0303120702011b0c2303030c04060311090a0b030a0f0618 68
    0x41c44a00c0d4001034000c4801e00e002a030440c0c08001501b16080420b02510007103c0291040c0035060390396062102c03002c01107200b81021814400f500e03000082c01d41c00ca440a46e00500110050181203086010181824801d041c07071a9030406042d03a0381072070340500c1070080180100c0400c0d21081c41b18a400351f0241a114202c01d00143c204070002c20300722000341c04001c01d40c040c002d861a021584200fa4403003180d001c3d110b107210b8251a1500c80c286550386002d80d40700030034010702d61180e10302401c10104001c5d0300d402081d40501246851524119442920f0143c0d60f9106030380e03003000411699003003000301400210b8a082440500e000b01019007100c0366038810140055021000e8084140d00184900b10168010824200f524216030b92009208a258101800748800800d100401e14a080913000f10341459406100e181c110f120200b045000340510700360030089561090100b101080055a80582500d10010b00c0d2010020481c2c1030b20340c1540071120a040899220700c1c0803560b0f01070102c1064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 450688318 1250 450687068 450687071
    0x11041a0310020412020d0f0203010c050309210d0e03040b04120b070c05060a11071209050a060926150106051806120f070302220905011a1615020a0c060e01 68
    0x1d150060030740780004d6500c03000380301c2c0c4d040385001010400441c105215142c0c01400801001104181c0588154000e444104140c400c1d10050b64410f170145030700d0040d51900203034481c204002c6944003000381c10a80c401458034042800b01060081c4903c0181008101e440c802013403444550400022400700038100e031082040b1911440c000c52000550f0f0f0307401218241c400150081d0400d985840380c000c02c08001c010007800321030303c140310f58802c6000068850032503494610075907400d030948009440c0d200d440705140c100c1010381e0080c07200158000e80514600b042d51640f40e5001014100d000c0c098000300c020840200c0c440e543d40440b489070110ba5101a11640d1611040d25071082e11500003c2c44e0920085c0c2aa0004603a9480f80e019105124041005e52085013943c0c803008802d52524028510298035142c000145844401e5456a1030003e9034001864412480f0f9281c40e0181120b000740d0707410130140000c0420380031902c02400ca23006a0349e12904480028649032081d110701180103032850703 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 450689568 1250 450688318 450688327
    0x5131b0221160204091a01080c010c12091518090e060a0906020405030a0305070203011a100c0201091503021e0910030915060b03070206010504060e0f0411041a031002 73
    0x1280c0d01c10101103110070340128a500d0345034802c030044060a80000007034005040c64954810088024164821601c000101d03540b60b070780342e0f810141c3e1813480d104418001204544641d010603080300380481001c0d1549403102100e5111150300c5d03082c0240c081810700040c1c3d40c07541d241c00c0845c842c030700034013038400e120081c08010342a0b0170071070740c81e10060140301d41581d8031141003040041950403100100005401c2e51124401800c000c0c0264105034002e078060b500b08031401d60344c00c50a18540900e0980100350ba00300f2810240103c1c2d8801204204038107218044002180f101804200c0c2c0583d000300e541e026a440a01405170008036542d03843c03101240409014010050355a6441c164064a6a180004130701cac00798108070030010700c001c4e64501744030b18001010805440700001035104080e26000c50b012640d90f40140000c8038400d00c15000002800c5001c160801c8518411580281c001c91030b64442c00a81400a0200c0355114400c0c102003031070302040e60060805009030141128010021401d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 450690818 1250 450689568 450689593
    0xd0c0210050307020a050706020109110f060f070602070501021207180b030a1e0614120601140103021b12030601030606031401151101020a120f0e1b01020705131b02 72
    0x20540500900c1041c041c001c00000c800318820003500c5107498001c411955455610300c0064000c0c4044007041e15400001481012641041c02410140ca071003d03112a1814401000b002c040d0b0f0060b100445c1c00940070840100410300c00d002625030307000ca01250006c40d0416880103452400f061200e68000084110100700914100e4141da42c80910458003091680014a40c0240502041c2544001178a00b401c0800c5800f51030801c43c049120a81391340ca54002c6842c1d0495480d0002d100307103400102c04044652865201c1d40207482d012070f80540000d41e03607146003400c6d401c1c1480007401c14403200d0084104165983d041c000c0000034852400c0810540b080a078003420002c40c14003868651404101c3c0030340c0440e00c00d818110034400d000000b1925400c034540001c7c50070010107400c140150405040f40c0510120344118000341100400402c44589228410407600b010b0310035030781c10742c0901140000c0303913203c1180d052403078400c05000248841d500024848001c0c4880081c20465000e08030710141b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 450692068 1250 450690818 450690829
    0x1090b01110c0f09090a050708010b01200601050409021f170c0403020901350105010906090b0603040303110f0a050304020a0f03030c03030207110a12020f04020f04030b060f041d0d0c02 81
    0x143d9032010340d400c603056512549110318140d88550028a83d1084420004100c01c065110075614a8242d03140d000000f01402c0c003581d001000540566190000c42c0100018642907018468981c03010740007510b55038060003407002c100320b8490850301284490742015000041e19010590110310311001c02d003024150380114907080c030140a03040701c840301d4420b496451020009168982d4140c2e0f10443d044602054501c0e001e4107080c49007140840c140032020810003114001c500404901900d090b007180d0310b0303031400c070050b0410041050001c1c0e801c2001914440110000301000328a07601c815a4030704191042c041d1a400d40c1d8001d0129262000c0c0030700003e0350000c800c1c0701064140c0340250700d40c103103410301500b001d19000600d81d00001c400000a00c1d000c1da8032a44c901d6a001702c3ea01c10601e00c410044c04281d03c0b03541e100380c900c20390400c8180002161811126041070010300071074400990500810112032014451f0b0400c00304412071034059283c208512208000702e40b070100c940c040b0980c003155 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 450693318 1250 450692068 450692089
    0x3140a140d0f150f0e18030a20030711011d0a06020c12030c0741040c021501150c0209012607030809040f15061d0904020a1203120501090b01110c 64
    0x3c0c1e5004802c0881c2c042e030280d40e0101e001c10004002d1f20390b60301d10450041e14003003200c0c03250710b05078003500006244110301105a036401600b0260003104080103800441e500108802820006500c0d0074405007140c941c3c0070721202400040d00180701503400d032030402c842e508074480030003103a600810409080c10400700750780d4205c6131405180049908030108541c0207402c552007210f460304045030f01c2d5842c0035001203d03030b402800c150b40c104000701005000702d89600b14038030300c00580c1601380010003c50303b031420400c020b41d00340c0c0717807012060039294002800d641087c2d100d00184500170b81da003810304445860150251203400003c02e455851603440d15903d0003140380c001d01c916601e01d801d41c201c45903038001d004092603130345c0001c00c07080c2c8441300605074850300b8074401c502280c1c00c1c101a4040c244a120540107a40003081c603a956890304e2603850100ea02840200c0c10000810300041c0210440e004250103400380140c040b690a05032800109400300d024034a01865000d650702a141da15400d0600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 450694568 1250 450693318 450693329
    0xb19090902060f03100e13110f22020304060606050307020c06090418060c030b010306061205100b07080406020607050702060d0b030f030d02090a050303030403140a140d0f150f 77
    0x20518601a00004a160154601d00f0703051150000800240100301c4200384190790000501080c151102d01c2d08030440480e11070020595004040c080b1304500d4071030502c0c5a01c4030024034803035101c1082070759650117030504c0000038040e0703402009010410070503005a20240c692440c0c0a0f00f0340c036000d18021f544120320100d16020700000941c140031a11150020784003070540c0d012140d211440d0780340080060000014080000b403921822010941c8a4002d1404941940d6140d82a420039600418028280a070005110035103101d000101054400c000d4200d0380e01030201c2d552100c2c5407080c081e09140c4014804010080100500d80040c0d0701c030025246004419440044c1606400002c40d103080c00d80040c0c2c034101d10011602ca0508002500141070340c2905541092302d9507520407e16540b0700050341c004020540011f50301d40d040904002400d030404281c030f1b0000568014211031801603100c0100701403821344074030100058051900a840c59290f038200e001c0380c9d681c0f030001d2900104602c0e0041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 450695818 1250 450694568 450694571
    0x204080c18090730030815300c030a0b01090c0305130f050703022d030c030a020603040f080d0606080619051903060e0f060a1b140d0e060a0b1909 64
    0x207103d0006132642c10f080580d810003c220350001d0003400e0140058030100d03201b581c501034228144002d07007801c41d44000c0b02c0f584410b604000c8922071606034410001501200028490031003040600d1380c080186411550084580300b42c80d50400c0803d40507128203202034001d160a020502c280400001d01800704c19400c4440c6440c9410700d0f182140c00c00303070cd545c0040e500c0041c3d4684e0030281040a01070032041602044a140020f00c001b05150301c94584424556040d00100400e602600740030340115800b62050030903d5081d0181c1d60b450380241c00ca200400007003992a1020301409420a01c07141d04841c2c2168803040f000c01e403150700d201400c240d0007194005c4103014204544051079050f9040516403000d070500085a4918000c1d03070318032010741001c0142c0b00c2c0f103011448204181c422121360903100c00f0745079a403d015400c155141c01034000100e000070700420404a10021a1044600c1c1c19004806401c240c201145020255104611424070503554062118074a0518050800c110780702103e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 450697068 1250 450695818 450695849
    0x712080a02030d1508010b030f031204080717070317040b01150509040203180c0612011203091512060b16060b06041d070207060e0d060905030c010204080c180907 71
    0x40b4290300800d100c1054290038200640113460901000d0707816103650800821a0907854400c250f5101c2d02c00c4c04d8006160020002001240c82a48041da80b09000300b4229250130500e6441c1e103002003601d25400340080010480c0070400d0b07480402c00c01103503408400800c15040540718a02c094006115201403210317401c81a4640700c0c080c1c0b0a640180000900841d1246010160105e0301c04100000d103d103402981000c0c4038a16142d4207a903400d01e003480400089030b007041300e031900d8855000420f5050211031000080e01344103640c946225030300640c0c2d55181d00741244c01458240c409541080c0c040784d4040c13060895901094801c0e0031781c280c000758082980c51807280070600a100e40d41040e10038030752604050b05481c403518a0b140c01800c2543c219620503607038600444015546290081c0c0c4048000e2280b80428541e4001194050084068902d001607682145007241c1c001d9208080540000007407480707502d0b14070080b001d68002401c080c440f034503150820341e0300c0d01090700a09429405180c0b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 450698318 1250 450697068 450697087
    0x6010c03120606021c090e1906050d1103011a03030702061312120801091e020915040f0504110918040c0b03040305030901180b160c08040f0314071208 66
    0x481c1c1075040c1107110741c1000095143c0c14000d489004101c803001d0583c4600c400494414411852041200d1019000300345c152100d0a01c2142030302e14141c0324448540b2108c0101e11640c600c1250600644602e001d9201125428141420340d05c42813200350b544220002104084c0d207021085400c1107074102d50940d558030b681700128806070510f81000d0181c0441c42d034214104014002d14811100c1c55803101602a80e84042440030798003102c000f42c040f5401e0105a020061054010340b8607110010303c007500700601645034100c04c1d005540a41c0f4255100e107410042070805120344101a59000002031600c0121800700310820a4941840c0b810340d072100000e401d0240c0c44400f240601382d02241180c1d0b9041c5420002e02a8100307585039400c41d4a060300d010194a41c110703891040941c00781082a8503950300d0086015031202651440c20300040c400003100081c0410010f201424407102600c0c0c880741541418548103210303600b0240281c0c0040300500030b03074110214803001c0951041c8a203a5868005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 450699568 1250 450698318 450698327
    0x25140a1214090f150417030a02091002011d06010b1207020304030602070305030402011412040b061201090c290702090a0b04050703050108100c1d12030a0c030e1806010c03 75
    0x500e81d00e48180009050102c0007102150703644404262000701d0f41200703a80b00c01c0124003441564002d20300b401c208590148031610001941d44040d41110042c100181c1d50042412925010b10311801030355074a001614211000001140004c0910018640c43d0304041e5078008030303ca190300d24084016040e0004001e184204200ea0103198072000954540c0b800c2e140141c4541c0064400324045060f10b071244041200080aa5024820078007103100c807501c03035840d0403101c05005807100340c0224401c5016010380d0007d02525a0141c843d58040d14040d240107114075000d1074182d030140c03146000280d002e10524241c0305442480c2c0c0c048546140644036401800b00502c1482c049540140c10041004145905988080d04807040c0780e0950f61450307a0740008008850070342a480c004111301c01200400c008580c104403c0d4400040d00c41c40b005888556800c1c559081540e0080c00161214440c0041550100d9210030b0040300f0394440c88202d42845040b5200140101410b0400004400c402c0a0603c41d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 450700818 1250 450699568 450699581
    0x105071715150d02030406060611061503012007120c0521040e16020f01021903051b0c0d021b0907050d14010f0e0f06030616030e0625140a12 62
    0x2070201e10f039444900020003400307074100320380503903002d850080d000650754064400c2038a05aa000007411003507842c4250085501c085940081c2c05641c0c40c03d0080800c1456031000c8070407040050215250801454030307800c5006c034241040d04000c0b0501030640040c40014400c4020061445411003600d040c100a00403070059a006118441000050107200c400a0b004641070048030b0b82911422004080310fa13003030b48182c02040c02c0d01d020380844420250b205e0b030b04c0140c2040707041501c2411301d500034840c850541c00807802c030060b54000324111000310340c041000c1c4402c4400c00f1140c08181440c500000c2c1d001900401e802d09101000800601e4084664040ca1450a01001c220442c0d61106620403030440d150207603a008405200204600b0f454080da0b191040720000c0041580b03a40e40c802c124003106205442c0381c1071640b030307000e9400c07107140500906116024607051390400500601503c001030300700b4407281090000c0c4210840c440e121103000ca404013a541e061854480030402e191030004e040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 450702068 1250 450700818 450700849
    0x801060e18010f020a0c02010e100905100203040902030f0124050f09060706060305030405010f0c0c0b1b0d0309030e0405040b0c0f160b0604230a1d0d020f0105071715 73
    0x8005020204160094000c00390f1b14002e90b55950303060b5941043c4201d0300c425000404c003140008008006600c0c1c160080d00c400422481030b00d0509588030906000c0e60016101d030100e40100c1001440403090060701d2001d000d081309294124020000c001a003203104110174140036010004125815032210b8048510b03031075120074100084c1ea500d0030642d0300c84e0040c0c017541e4001495480381088003031280c030b051004580c0207071081420919240300b01d001540710342480080400c45454171040c0305000d02014032a07881540b0003103024102c03468002c044003100c10312a84514030b054180004903007000c40c560b03403006013905450b40d62440c4003140740c0b0b1070141c11103140740403021a400504000f202a0003902801c4291801c0c8480070002c494422548244603c48001c2804030000600c03401349908020160082e100c0704058050f20a05da490600d406102c441d409a84800101c16141109118440d40301c2d40c03504d8100c0c0c40c881510210480404007500b5944c000005051200c401d07551003089401008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 450703318 1250 450702068 450702071
    0xa03050607080a05070903020f130b0603010902070c050904050607110c04020f09090124030203060604090e0a02131b050c030c0d0804110a050a0504090f2a0801060e18010f 75
    0x1d01290000c000400c00c488a402143c24900424140c9000b05500310580c0d50041490817074801d10010700c1040b8950910a109103900c0d001c9220072611144011806410b00b124003590310441e604040140f8400c5500c1240035440700348c00c100100310045000c5820000c00c0c036100c0c0340446200f40e060f14259950311300c250710070b10024003401d21811303910060041043c2500c0c500d44681e0384080301070090440d94030510400b80144010780d81c65209a0003994843c9004011f10300782625500302034215140a01c4002660740302001c0041945440301d42055a284505002d00c8000c1407201d0308400400050740c0c2c5824054089400c4049030010300c1500c240f00a8034003142c0f010f005000c00100108400e403819a01586c1108002c174075400c0c034078200350a032070300034000110040c81d040c02e100003041c030382c1e00075907900c05110180c1e80017480c1941000c00700c0d410802c0c040200050b500311603d180c0e20079070000010340e25141e4100039181c12302c01d1403507001420100145811140d41d14860250011702d121a40d41c1707 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 450704568 1250 450703318 450703321
    0x11010e03040906241b1e1a041104020c1005090604120201060602030915090301050a0b01030e0106080d0e0d0b0c0409050a02030f0a11070b0411040b220b0a030506 71
    0x600000a0400c54107411000d0200300eaa42d280c4c81c3d07400c0c6001145440d4120a0442c02a40e0ba003c1c4075800e20003142e56004401d03d0348503480301805500b50100f00304a00c1100d429180900c4685924815010300082d000791080c2041c5d41c840203410f007480d1409016580201d9000c0804105110080701603441c4034051000b442c01c04510340d102e01080342d08684e00344911050301002441441100b0644070150015480c0113080c20130072901128881c14019604001c0000564507142800340b030303002c0c0c07122107804a110a60500058290342c00800e6541140e8940101001990400120382c10a021541085c0001107062008246240035111003c0c0000d00580c092213030f120000e90040040320001c82d002c200f551101d00c0020280c1c0300503071344c07401c60f4440100403e261619903030205e002000300039203081c60101c4e5030341c919100301801c5030706440c00b6039100800d03904c5050074007a00e08800011689518222a40600c402004038502e43c5c60482c0c59035091459400d88441d140c000145410004aa00a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 450705818 1250 450704568 450704591
    0x605090328021c090323010f140a0b01080103080f121302090c0702030607141902071d0402060f0702040f0204080321060a050d0602040e010810150e161101 68
    0x40740840c42440c0010301c14040d1580030350140008a110101c2e540d91491140f0746540c540c042d43e9032558401c844004499400f080100c0e07001d11850740e001c0058100814241d541b00c030304c1e0032940c10091410550904111030490b0583e03216003400d05403030703004107019101e5800050840882c0510341105454648980170b010000803640d00b07005285200325042681d6940d0104055501d008089000350107601500101c0c1042d406078450651300d4407130125031401c0858010841d021000d591655a0168100c3c2c42c050000601580081c1280802c003d1650500d04040e804559240306a418909a0201c042100710855541e90415400070000040c15504d82d44c540540d580c403a03000b0030340601050360220244442e5901950719503c08e44004094030800c2d031070070040c02409080311508541d1039030300300070219150b4503d40320207018040b50001444000c094192440459a20501819102c803154504112401c8a52042540014811080709034420548019952560316074450180c0f5400c00f66141d85 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 450707068 1250 450705818 450705877
    0xa060b1303050c040911010c0203010905071d06091b030a0b04021801032306060c0102130e1e0112150b030111131a030f0402030708060405030304030f051606050903 72
    0x2507070b0060742600c2908241e01e04120894032000c600515000d08004d562409602800522000900280001c00c081e481039450300d00788135540d00004640c40b1040b0510720006148508a640208244e40100040c10860a0801e00c2c0302c60844841c9251000000140001055000340c50f090702c1c0900103544070100b1900c05040080f03480c07400d500007442e08006010000e190001001c0302c0e0114640807140e5211082404020f50108981888a64003000340c1840d481040181c0030052102d501a0000c03800c0520703c15070341c5814100760385c0011310310b03500600c0411420708080f82c0490b800010600320307500031800140a071069140c9a42d165280c88100b4003100301100041c0484241c40c241c40803032540740d50b108060b10100300503055001105000003440030402c0384442d0b80140c0000c4c105c803601941c513070035140b418104443c115a0342d003020050004040c0c0000c00301c0740070036483c10242c0c1030080100808107810148a8007501c07003038886000c9400c400d414411241841000e500100920601501546 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 450708318 1250 450707068 450707107
    0x5060109081005331005070c030c0302010806030609060c070c0e0a06140109030809041d0d021005180604031d031219020307080313150509010c0806010807170a060b 72
    0x1155440c00418890700000d1181d005400b0a4004e25080314992240040c0704410b00620b40900c140300e020016200402c903410082d0004501c54058590264214400107208071809002c05001e944000c061180e409004101140e00200c600c05854540c0900e040550200d1102d501c58072a101d00360041c411106415000341080d151039034080d2008010300001190000041d10014041820920007401c031880c00e5000483d4000400f040829412030704040c0320304103a100d45244016038040c150403018400e06000d50340d40500801200c244401041049036200c9400503c01130400041d420501d543d10000910720440c070802804840b4202d16101070070416038403d0018a401c40703010444c1c1000340c0e1000040310300340b65112800030b056440b050402190f05560400403a8217015501070800501c1071352142038421070414002203018080303810050030606000d8122410469460108803420380c00034818100c10b2120510002141e0340c181c102e500404ad1038103c104c03510700c002818400700b0403c00311113 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 450709568 1250 450708318 450708331
    0x115120c030b012c090a0b0a320a061107170304050a0806011202150f0a090302180402100c060e07090c0207090605010c200d08031b1c05060109081005 66
    0x44c082c000d110110f00349106400380c1400124030900203c0ca0407402d01c0e030b000c0385c0c004401890214900c2c2e52840000e90f6441c05802c0345090f024000c070048400f601c2000041100e011580107d400c0006040100b91b440d50707070b402500184200112030420200042103800010710300c002c084d00034a0155081d072903c0707500500c1013500c900881e0501155075800450700504076000e10541140341102031b0f0a2003075444131fa01c11a0162642405149a00024000100340400c3c0720b40d20340c0c51041c114410010304800d49038020590002c034900300300058a80f030301d0810a41206041680540185160803c050001f82c514a0740600134503000240d96542e0307070442d8082c2801350f001c0e1b5003515160350340181150b06c2031043c01d000a1082081c003002c02c20440140228042c1c0010100c003003a9030001042d20749200f0704088401c540008204142c15410141500a280c14144910301d8008501145080010382c1e9902c20741c42603031800030a00c075038010400c0030f009014810607035000890015405c3c0060a0031100b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 450710818 1250 450709568 450709577
    0x60a06151806080714030f04210801050906060f0d020c0f0a0510020304060f0c1d0616060f180b01140d08031b04171b01090b030115120c030b01 63
    0x1501000e0103003500841824080302011451480c00c00c080321451006000131040c42400c140c52500300c0010401544242c05064041c210b5041628202603054200c0c003101010000380040d40e0305442d8030194850466074100d03420406502c0c1c2d6000900c59120f483c6d18059150b1000403040c1c180700064002d413004401d901c003603072002c280ac594140e03107407190523900070705a0b044120324072000803590b4095a0060f0182c100010034005c50340320b4804a400768440320740400c0704240d903610201a80c401c840081c074021341c0d0304c1e0f00f04510300701d1015100d800d400d001026961618241160200c09903c54018210844442c00e520801130a02e10070105c000e009080880010103400b4030700342001810001005d9002e0502491540d9007000001031052109003400d540d80d08100000d11694103505401e005420b5001911035040444807400d402d20701010781038140080c415007080310003440e40503213045410300e10702c0034803882c0c030020b041781c4081514000083c0185081030124503250b050788280903a8400307886 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 450712068 1250 450710818 450710849
    0x80909281508010603080715020405040908090a0614090d08120f040b01080309060304060e211c05012402120d020a0e0121150302090c030609010b0c0a08071103060a06 73
    0x80c0b1802d84807035000c003504003001040038100090042c000b01f02c1c3c50f640070100500709900c6900080554500704400e5400c0d00e80410700c01200d04e00044120018800c50821000c2c058001c40079035003600800c8646480340d40304402020900c540c88049038000e8031628001080d41c5446185900703800d0381601c00350740710125600089a1018000100c9008843c0144110304694466030340f02c1c00380224a100fa105401451110102c005a40c41041c0c6c41d0310040c004541c9501d90301207101c81c07a040351902c00340c42e9410400100101001424030085c0d039016502c8000598506200c03e07458012a0b2000041d041000642c0701403609a0f075003c3c0002d6040c540d9500600c1d0900b00046030105500090b501003445450281c0752054a19032000c4001400b0340d41401c2680c0d03803500001c0381d051040b1400c68400300000100055072030300054081c09000585222400d01c5500c0220641d54461398000070328581c1c0000d031003c203000316600461200306000f41140c1d00c03403400380000c0d00a80b01c0d6103d40802c3c22540c82 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 450713318 1250 450712068 450712079
    0x507050d0315170c090109050a0f151e17010912020309310207080405030d0c200105040b0c0703060605010c05100f090c1e06030501030809092815 64
    0x403140309030701e06900655502c1c01d240f90103440d04001250780580c0d1042c2c41e218201078940c42c080c54024503c010000503c0c2c0f07040101038054038801440c00e88501d00e002c213010382410702c106481090389d22400d1703001350240040c51365200711205500801001290190454490401500400141807003001212080440c0410580c0d4034003030b510009501c52052484808040540b0303031f50501740c04411a402100c0300e51804840100c2e03001d4403064888100006040c80b8900381002485411140c904d803102d450962074403450710301015000b04441d84a0301042d1801c1aa10403030549026221b005042e40d80e6601c140b0016581c1d600500c411a551810718400142640c06521448842034016020b0040d0b03401d03080c072201c014503541d60744042056507195401d01203480b2544030400361006000c000c08461040c19004017585007175101c0e40815080400610019140d46e0950b100c0c0d5800390b0b0559260b4031b601c50035410b20125201d00032602440a0084208911075800c1410b5408100c24a05400c40c3c0342c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 450714568 1250 450713318 450713321
    0xf0f03020d0e0607140c101707110604110109030b07031a0906010504050603040c090504152703230a2c010207030b040303020702181906420507050d03 66
    0xd450141c3d000c0300034440c0c880410303030512811828207000720658501c16040b00004811046170307440c010003e030641110164840e00468103076000a0340742031400c1c0380d5000c1d015250341d4180c001c5c8020030411340c12341005030310390003012b50b480030b580d0101d0415038030700e00108010010b240040030740c460340c80c1100341350300141400e415040c0140b506075a92480c00d03041c6000c1c80703074982c40540304580e0a441c80301d0005140c800f511495000b148603140109550030f1106804040e642d88040c52200280445080c00d00e01c98401e04032050550b250078480c4050704e10542038881000d80f140751003a562000503103502d0f079982c40301250301c919001a98170400c2414440d1110310008080801d203001d070703220102c10b0010410382851a503101d44079250152a01e58154082058084000454440e914140c000c0c4200b13000d40990352200000302c18420081540344c888203d0840142c58803d001c0034001c00034083c100c4034256004031240e000382e80000d00310180800006c00c154450300d002e85450048082000089100307 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 450715818 1250 450714568 450714587
    0x10b120f06060a1d040219090e06090f180a030207050103060e060303030c0c1c02060105100c050d08090313030b060117070801061206031a1909020607120302070f0f03020d 75
    0x20b03001e141007415088060302c0d8a030b421801d42800003a10360020f8415500d070b000400311445102c4004004103070240c4081d01c5200d05410810600100408100c466114001d00c0355001e50a09000c0304541c0711202408103268400169403100d01840e070b03280e428150001400320071076200382d80070403076aaa41d011602200c20192806a0305400130004107051580b140c01501c1860341d5170080d1040c0080262101119051040030800540c100c2001088645040c00d44082c5044190030281c160f890b081d0344003070700c0d812124030ba14244806031010460f4040d040090301c024020160b18041199103a0030525518a41102c070913000035466a2150b000c241c000ca5403038003804042d00c642a4507400c2c08c5041d035110450100c0f00d03440035951803001001c50401d94101112150300c0060102d03604001510b04004420394600c51461820800f0f024010b80715542101c918a4010213400c1c0409011001180648203000001c3e041300e40407500c03030040c08000700251914900c65001c031094408008002d582d035208 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 450717068 1250 450715818 450715831
    0x50610030201140904180c031e0302032209060909050f01090510110d06031b15020c06090a030b071e1704110a0801020c031804061514090306010b120f 66
    0x1003e00c60080c035070302600058104650014000700e00031a1444550f00031004105041da9041c1666104105000e05c0b007500440c1055200c2035100c08003000d0300d001e543e070720407401c20754403141400004040001c072070700c08d540250400020034001240e8540e0508054606180c0075126030048078604241d102d8140301d040300160344030b00580300c410700124054000380111107041c41c110f0420880c02c41c15845d02d100b404040c6108100426504841c1d241d649014040358122080846907883d00794295600010b40103006c5100700c07542580c0e040100045507000012f07900c01448026882e00b48030090f0b410000002d1062101c4980c0c501d00c81c0d0a000031501c02401c0308650352a0703400c0901050202d000034407402c04c0400302421916556545917181d90880c0d10001010001e42c00c0801e8000941c03c204601240342c840484050100a0401c0300750f039204190f80215800340151501d076490314604240c142e03440b0200003005d980300c6603543c80b1051020380c042d8100d1400d5004200005911841030029a4060036 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 450718318 1250 450717068 450717077
    0x5030c1c061d06030a21030603051006030302211902010e01020a02010c0f090f030b060103090b0f0105100809070b03040c0801061401080a020a0207180213031203150602100917030f0103050610030201 87
    0x810086c115006c0085c0c0390000c900b01920350b0004004034a0030415a445050b807407200180380c40c51410300034140f04000d031160070500740d900503a24205201380107031811807030803d82074225182c1000069004056418040303a042d400810361560241d010740c04481c4004154403000c203244000c11044034030040500030414905c08104040c0042003100550a0303008006040010f560521515041207501040341c0c8080342865a800500407401c090a01c55110046402c0011144c1459802d09d43c40708000c0c012001012004400a8140880041e003c4024503100c13008200c0d00c0d0300c98000c500c0c0c61000150090115507842d000c0744001c0094401c0318100e480c00ea0141120905060009400c0744d02025079101441d000c0c84007000142d045160b900c01540300d407a040d41c80b5003d519014054a03101d00316162800324101003040480c0d0003081000800884640000e8030382c54601d44020102c14101403216050320100402048140980d03059040e24042c40469800350340740c50600a00421a010090016 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 450719424 1106 450718318 450718343
    0xb04140f0a020319020a030b0c130614070f0204021b0303060414040c0e0703150608041112030a085205030c1c061d06030a 54
    0x564100581500c1007590000b903216054407100141e6401624000f80c1156500d01443d000355900a00440c0d41e8108013187c0c50150300700200400103000b10220102d8441d00900340c00012803140c008541c40c011180d580c410080c440104100e0b0456024442c0f9281440902d040507c0300650000840d180d14080c010001030342c050441a81a218a030003d000100b190a80d400060312403c07512600e0300d4440e900114014045140740f1685080ca449010540582c0f01a03d03900490140c40030b00e1410403040e00300300e0082d81c0c41400c810694410010646c5c00c900981d00350781c0c0301031105d0309240c0c82c03400d03003070224180151100315002c000340c0c48048aa8285440c1011000c010002c800c0200c0c442042502514621003c0e0a010b030023000840d40d5200c81c0f011544c0300388a581d8076801480030541e038015a4842d001021070303954170506008000b508a0500041c10740790300f0740101008581 = true := by decide +kernel

theorem cover : BRFrame.Cov 450539568 450719424 := by
  have h0 := BRFrame.cov_init 450539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 450539568 ≤ n) (h2 : n < 450719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
