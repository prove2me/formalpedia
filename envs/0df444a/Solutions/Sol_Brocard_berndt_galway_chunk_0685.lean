-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0685
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:08:27.153156+00:00
-- url     : https://prove2.me/submissions/dca5b28b-d470-4f80-9cca-9fbd09668b43

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 123021582 ≤ n < 123201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 123022832 1250 123021582 123021643
    0x5061303050c1f0e0102040f03060905070b0a050301060e0a0503031e0c0a06090b06041b050a0210060603090b0115020d030504061103070f09090207020105070b040317090d02011a060306061803 84
    0x5544d64002c1000031407405080000754001c14000740005000e01c0e488907035000401c80100a0080101500c1d104241c0b1881f80d6940200340f80c0c030a216034000501d10680310480e903d0840e82c1e403801c03207200030010342c5000040c00580c060050b0550f40c82c0c00480d0144120301a00d081442140d042034071803400010b610445140c18440d400c009030005000b24503150392880c041da04110342d0104405c49050003038946100c0d003412441c098517401c092140e9410090001005501a003100301518442c036a05200c42ea22030040b00b00c492007000803036006a1101c3e040040c0c0070300a0b404560032038064180403d01c5850000384114a51064482e03900040c0254101642d040d80010b410b000741c1980e100c203600d403d5554000030441d01940a000d040b241800001c201014001c114a403a0010003400d61450752505800e0180c85406c0f000391701000d0750030310320b51800d00c003803d000c0312034005001011581580c45071000d1110b10b800003140e056400d8503520124409650400c400c9c000b15490060405400c202c04440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 123024082 1250 123022832 123022841
    0xe060a0201090506091207140102071a070806010f0203090103090f0602130602070f030201210e06070f030c020c03060c0913020c0604021302160b0604020f0708030a0c080405061303050c1f 82
    0x14910395040291810300a0341d401b000c4944498001414101c000707045089640240300d090b00080c030700080c008200358056065401e40b4801e0810b91101c1d44266594801035400004042400005810401621340158041e91041702d010740621951521803480c1c1c0c0e201000c0764410780c0c0700c3e111241c99010030041075504000d441e001c0c0501c0000101c9040c81e61f40040c01c0c40c120600070700c044400050083c4414007842e4402411540f401c01140c1c2c603400d05441c054125204801541c00003030034010000740d803d00008003140d41d5800600144290340d150500c07181c4a8000000a035808041c0c2d5450300070704120346c00500303140042c203000342081303080c280304000c1540e8411000120040c014051510414290200600000d81002c000303000380d40c2d103200003002841058080410760102107640002d000201c0c02462040611100400c003880341c5060a440002e03040f100108240d1180d400500802d26410301c9018580c46030034003500300a4448001d5061000020140c1503850f012080844501c005004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 123025332 1250 123024082 123024091
    0x203040b1b0408060a050a020903010c09091a2d060a0207150801030803061002010e190c0905010503190c09050702060708070809100e030405060304030c06050a020301140d030e060a0201090506 84
    0x110780c42e1070300e00b0010701d0321244020b001501c0726030764000062902849030125042d0003c001c00801c002440018082c181c0480d5000f1060034615104400c0c200c50103d145070603100c2002020012054000305050300704141c0003811042034200e0301e000380b942e925a400540309003409078020748041410140e4203529044608940f13010000d41c0001040842c40f901e040329003240c01074074240340f1301c400d07242c0907805071002d800800541d00c103214078a40c0310840c01c040343c2086071150901c10000740c0c0c0c8040035010f9413400c0c02403d034540c100c0b4111303501803c8655150801944558005a50300307075202c3c1c91000b00c410465860b00560012010022907c0d4801e0a0560048880c2080301040c01c00300c0d902ca90710071510302e00d0707107045540c3c0d650b0002154042080e81c0060030300911441d07480c68a450000c107203e08840003151301ca0b04002c0841d0344010140241c9040c1c500940d00c002d40101120204100d561100c0c074207500781b0212501c403005c1911200001e200c915030070b400201c0c00140d603180c220700c0c0100040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 123026582 1250 123025332 123025381
    0xb09010b0a0e0727030f1109010906081b091f0e24011106011a0f03010801020c0f0109020607030311090301111801030b03210c060103031e030507092303010203040b 72
    0x60200c00440041e0001c5001e481c1c20806d428030301906850841e50100b182c1c2c500f2680240c05000000348819140c0015040d92078801c1504c203400c041841c41c1c3e4a21000c0b402443d440320100d0002800040b0f092105107000c420b107030303000010507940c0c50080300050082d03551442c440004549a02040300300074a1152108003881c040d00300780c00b00707400aa2a0601030140002d16060580c44081c146d001c0019143c1c0700000d26500c03907403540e541d00d0182c000d5000b40011496801812107103522040c0603c54910382c1074020b0220707881c00056540c110003c00410300020101c4000b844114003a4400b4440c184001c5040713030fa61035403480c0c0d1488404104200326101c03030405003407840140c402e0f103010030403038500141811541040102d50030071080d90b000344051013009100c0c00000006140d4048a4200d10207100d004580045801d00700460644608490140111303a0b08141046402d184080300c9011400c034120861002081d100001c2c2a6030080e5410303035810401400707100455424071002c007071954604 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 123027832 1250 123026582 123026627
    0x305060628170411040e151006170702030a03020708070f06050a0b0301150e250507020a060305072012070803040512070519210302030a05010801060f030b09010b0a0e07 74
    0x3d82c1d543d034441540102841c011071b12001180080e94041105641d2156880042c1009160541e15000c244030300740300300000903545810070b0a8040e60011124000d80d11b641c0618035013004504168069070040204503500c1804001c2940400d0403201100c100c2c038415040428241080442102075030701d030791500791203645050300c200601039001c0c007010200e541c1a082c402c501e07510702a038100c107058035007500c44030941c00b030a9003c2d05c50780c000c00810115108a611020a61321181c4c11000c458040f583c41740851040c1c540c8074940801c081a00c2c1070340c0d03255812140d04003240d1a011a03e80c120030011200c4000c040301380000c010040c8100c84c66001003141880c108070103500c0d6a944d03000700c10786000d5034000c1030380b1403800c0c000307585400d0780d070042411524091343e442120000c000794402c9405500042c580340000c02c0000c018080c1c4011900c00d10004c05105045840c0c00d00322000184c2100d035690351703c01e102d00c02c546900d0705040081100c910500b10740d103444900908818502c01c91a42c490000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 123029082 1250 123027832 123027841
    0xf06080706020d1b02030a050307031202041d130c08100605270a020f030c030f0f0601051c0209090405070e0a051b070f022806090b0a030506062817 65
    0x18160b0405102da01d0030880115a00d1101101ca80403040086d401d4044c06105c1c005110000004000c050310aa07200500d01e90021a2b85080340501c1c0034004000c4240040401066580b945042d080101c12203a0786903481541d80e45d201d0f14940781e012128541090008800300358140c4503181c005c20040d14081071a805504c40304090003045020b2983c422101c2c408035460701c1c0941e06071151540103562466480c00c14410130380c6284c00840305581c003425100000359142400e2103041c0d000d10010784404c1d04000e003034039201c1d040654000104603a245c1c01e0066040c80c0d40c0d04030034180103a02601c040c003006070a1400b007030032070b0a0083c0421200380c10001402040c00e18081020503040840d81180e803580342d1860139183c1620a003034003961042c02c00200d0007a408048203000b0070901032401117a040c1383d80705030a60b0a644644a83d580000c0d082c019402da280c000e070403240e40140018442c1d4540030f1941a094513146c02c414088550b5007035525019105034014414507541c91900c061040c081c81c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 123030332 1250 123029082 123029087
    0xc0901091a0303131502030d09050a060615021b010e03070f05030f1b150904090c0509010f05060d0c0c0b1f0501030501051c1506080a0b070e0310091a01090f06080706 73
    0x40500c03e445c1c1e030030304070640f81c03003000c1c4284240c9042d00aa018203000540042c2807032070340c410030100c05607521444d000c0001040c640c1220004d41d110b41d550043c1909441c1041c100c001c92481c1054103040c060040051500303550b0503c050360107403481081000e4254140b906162516240c001c0243d2542d1048540846503d01d8403134400f5002c0f01207501041c0000c1f5090000052f002c0d0010054001c5e0070321060100b0400148103030404d0341d80c19541401075a90703075024500d05200c00e10034940c001d0004c00034010042e900ba00140b82c2e4100c14184144a26501d5442200d4090111444940504001644000303588000342400c0280024078090040d075042c00005110858841038591450419401040804c4146180701c0048998600d081040c186d0321494a40c840000c4402241c01d10760100004200c24090310f010680c42c100900102101c110b5642030100038000c88070240e40241810310070395030034500402003d0103018161004101c128041c0b142c0c1c8203a41c02c41e0404480f981011105000259 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 123031582 1250 123030332 123030367
    0x301030309150c0605090a02040f02040f0311040e060702100c1404090f060b033d03120c02130b041401060212131211010212120115020c0901091a0303 66
    0x1080b010740c503501211400d40960b0710704546440100094240410800310038030101d000e003880341c02503906100c0c1c85c1d049038030b040480c42a8050103603000b01e260b00900100e07100c50101004100060000540301030b4030075080b80b4090040714440c00503072280c03000c03e120b032000780100c40c0394541d00d00b03040520307145044482c19140258069000318554500031803482e0305a40e042a8003c0a0301d1810590b0f034206440400980c500310304031074040f003c00409007548007035081d840030b9100901500c0a40c4043c01c0d40e5602902201940c9400100b2008408500259680b401da03440350641c0c140780001e0030340c0035406020a803010320032001e0b51400c1381401080065008100031464141c000900c55a0f0000d4002440d05180a03801190b00030040c034002c6070800484480b40f5400d071100340c007200d4801c044140b90123040e2140036030042c0349542c0311004110207599860408010512401940e03200c022101c0840c03000c0009a000807009926882c8008414020000340b50000c2001d501851511060003042c18001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 123032832 1250 123031582 123031589
    0x203030103080d0216030206013206070203100618052d060103200c151005010c0303091a010f060212121b0712030513030e150d0f02030a0e030301030309 67
    0x7680002940d8a0030091541207911903560000f017020f05400c1418000c0d82d812090241802d2488000e52400c0c4146118604031401a00c4000502080500c2000d200c0d140d0841740d07049805106410742d00d004105180188400380c80034100c5ca039032100400c5d1b205000d880011f05291081c01c0040d03401500302284503500c820901519118816030740702d00e001240180003a2098000344141c103125070050101c6500140900200345c0c00b03e41911030190080d40c40030f68140c0b040001c101520100704003650107050800071440c040d050009500501e900c07000c02c8900f841c40050403e0582100622107200c520340000094030151006141044da001c000114900c201101038210039520380000d90300e05130681904000002008816071079480300e10307100000e42591550440401d0400380004e13045ca008141420b0304c250103584e440d00c40d40050017444200744000310b4264214a01b044180fa0780d5015011745d401e04854400300507a40c1c50210001000c80b0ba900c03018000b0f40d0030400040000c0f0f035000051a098 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 123034082 1250 123032832 123032843
    0x4020103050414010207031808060f0106030e0102040b0d020c06010f0b0d02070f020301110d18020919200406020601090b090105060d02120124080c0a0c14122205010203030103 77
    0x40e100d07402d01400f10b92a0300f40103c0a0344c0005001d2003096801205030f00c041e03c101d030060440d181c844a0003034403000110350000c41e00001c0b00c010410548623410580d040440c3e200014035050f264020500c041d0710032483d900440e034002510b145203081c1044070300d0041606100300003465040a800c15002e21078203451a2501750041061000d2004038079500180701c3d401002001015200e19223954a90007004040d042a45041c80340045001ca142145445075401400c01c2a10354524078609201d00c20f40c8030040c0e0b0299501c041070100c4132001818100319207400b0f560f54642d071070403070028500b000581002903d00e0030b001203e10980c035072100c4941500c100700d0301c86d41c80c2c0c0387c1110750400a0240300b00c3c07005051005400011413031071183d403c280420011403446035503407482e18181c5030700c4016901d8030000182004004d02d018460040270070881d00c1044221040400c000340c040c9041e01600d100c914100c40060300407200f40740fa40c3c110440e8850201d01d541081d1900700084d44074001440003400d03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 123035332 1250 123034082 123034091
    0x1101120510050d032f100606080a0504030c0b070216050f0607081c0f060f090506301c020f0d020d03020702010e060d091e02031b12060f060109050108090604020103 72
    0x4250017401d03c080e4000c101e40325090300d11121500d81160015000ca40d140c68022601c80940d0300040e40925820749106495080d45616052403540003814014020f030b00f040300c40b5012000141480a8150103041c80d03a00514140082c95540f84490034603074491791142c0d04008a421132a11004141d0711000c2c1c06c40c1c4140e441d02066030700c0c1d02081d1422540000058a0519a020300c5006070344080103031403c0340000700c8030b99240d41c00d0a003200c0040c1c40e110b034428a049a00d0a00d041041a4250030285a003811003031414030001ca50b2404c00654881c3e0320301200306e40d200d1111076041083c00c200a062100804210b401608007940311032000d8000b50030150002a404156402100203007a00075001d00010b95450051205100400111700103d4080b401e40c400304409102080c032281c89160000d01400c4400f0701d07404209250070340c0c5801103401540c51101068030645c1031010a01c10704000b07074035980614200000404a2480703400441c14000f2600c01d0081c1e000c40040e01c44c1d881642801d0004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 123036582 1250 123035332 123035359
    0x6050d060e07051002010905010506011b0b0703180602090312040605181f02100b01030b13022212050c0117061c0c0f0608010e0f040b07110604110112051005 69
    0x5003042c80a4011036000300b9002c0c88040182e0341540301d2521540a180204040d894041c0110b60341026000d0011780c0c14403040383c2a01160301000c400c3e80190960400050b4191181c0d81c807003200c11a06020f40c0c40c280c2c041007804883c00d082c042507201241203040580350508000010b00203000d010b00030520304102a142e5401a1140090b01d880081e090060000d13107d050b69000f990740e908002254400f6080550303500303041d401303405642907084008240070506858002844002d401086e200340100708038990712030b010f22126003240003411503042c00c01c005030194141a031a2246e80c2e5405810850480e03040d401c40c141c240121070b046032084032204041510381c909880c01c8540c00d000540201220f01001404600c0c07681c5240441d069912541066a80d0b1100e54480103401c032401c0d8880c00380200010001589021030a82c80315170350810030b451441c0801c6040c90544100c07012070382c408124003113200643c1c01c0010001413510743c0030b0520061904145031112108035206007405003080700181c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 123037832 1250 123036582 123036611
    0x3070306050a0f030516320a090203041a070503040b060d2114070f0605190905010f0e030703021f020706020c0d11071512110d05040201020705010306050d06 69
    0x154018200101000304498442410121030f80f02444215110721503000d1000000c000060305000b101d007508081c1080c4800900224540750240e15001d1f10724100180990f40c0b503403a43c4109003e00024800183ca0703103071514001c0100c00455800c0482c60300c86000304880780c0c1d80300080320b92042e44001e2000454a03203501080c0e140340e884800601c0c2e54558083c03070b2007201e500824030030085030666075040c072110040301c3c0110f50300c6890400750114440ca0031210105100b5009160031402414140402e00010825181116a0103000311141e9440346501e00300243c0d41e000d441d0b8030f44001d0018518000c41941d01941c2c40200e0180b5800221010f49540c4503008150305403000c1c0c0380c0042055558447c54081d041d190b1546104040124082a035000e03100200001d0303020942e40c000d42440c0c1201d500002c152034840152191410490704e42c050b000a00e060b0710042c165500b094240800c55060030702c0060f08011283d0000c504040c50031004100e69562400840100c0c0d41100c0000b41030440c00c8004d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 123039082 1250 123037832 123037841
    0x3100302151810030f0911040c0507030c060c02030405060408060906010905010e06040509010f0c0c1b0f0b1c0e0a0b01050619030b040209030f0607110d12020d0902040609090c08030a0c08030703 85
    0x3008400f85c600100700c6d0602c042d138281d402e5002c40403101044920780040d400e81d8180034103100034002584007200351000540c25800305c000750740140101c9041c51f90b11800100c03568031603001251300313402c044203018150904000e89401344c00c484c8801d100e83c0d814000040c9541000900302881b954480700030940b0107000b948040074041e800501407000190654000d0020152804100d8110413900d0b001503059210700c40404c26100c024040b000c540b031170aa0404555041058045114044080103444c0d400c91841000780e4205008003800007074402e0b051224071180140c0c0042e00601081240004d0466003100707080b414403182c103000078a102c0381d10120700280a0b8020041d01446407030100c465026000503041d2041c8042e54071240070000d564500764882d100144004049004141c80044c06a1a0f802418200b0060500060f2040d080c0d00041c080c2c03029580501000c41c0c0d00c0210001703200c040d9490780e001d4004900111b1912420b11802081080d8100c0040c040d52400300206030300c0c0344281c02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 123040332 1250 123039082 123039101
    0x6020a110d030c1e08040b0c100e06012702040905150111250e070e03060709030f1202010f0c050c0c010207030506060415080106090209011716050a0909020310030215181003 76
    0x1c0258035141c0301c5034402c020348e11100101d01c6034842d015580300c00710b11500441e01c001100c80094542a443c060000360701c03580c1d0810308491500e00512000c1e42c2e0415101500043ca007603c4007249a00b003400c0c000c2080c8140c0d0416504011840382200e4015000041e4210007203407130400c10f00015034841c010340140e84541c012082108120060100c05688103400610301e0340c086040e02d0854846803020340700c1080d5440014480384ca000458004030f080510350400450320b0b03000200314211444114021651400308102c0070500c0400c80100c409401c111b004668102800180340720360441d29407695130180106498447c0d500c5201440d1041d00140f8510014130000000344020760300c5841643c080e402c41d000340c3c2c0c0001c05c0e106501203080c2d138038410a4041e007a400c81641f030508d0380726402c83d01503200c0c0c600d40092015140d400950320030030748010351103940d548504020707140c1140b0400c03030a070307240e403416841d440c1c4240301101405140c0000b4801c0c035007045507070f602d240400030010f6015124121 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 123041582 1250 123040332 123040343
    0xa17060f0c210a180c120201030e0a0501060819170c030705100f050a0612030c210c020a091130040b0603060603010e100b0a030b0106020a110d030c1e 66
    0x9040c649405212180c9a01880343c9100900030a1801c403102d0f0b1075062004c4025003015a00c00040100c080e00040e100c9800380180740c08281210004283c9251025195003144d03140c2d5603007400c118613481808043c01e2207444924452004420707449017500c00c20500c00201103650b0000d0062141c0000300115504190b11400303907070751119850740640080450040880300c907814980001c0300c2070f05601c03030310f0290f40c1400300807054500d054404031414a00610112070030005805006625130022544000d100ca0700d07910301c5000c001505c18030800341017540c8803020180c00c081c941300188510b40300351341010080c0c15181c460303042e120b20105016940720000524800000d0184018040c551026034482c103403c0d803c550706501c880050500300d51007141b00f1421500501d44041e0310300125003046600f000003c6c00070308020340741e4407500d402d00c030203a01c000c001d0f90142a1040400400409201074a00300316003054070170100e5100900640300720400185000407206251510107079a80c2003020784c2d034115 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 123042832 1250 123041582 123041617
    0x10203181207031722030b07030903090305011b0e06040501020601060c030c170a02010b220b03010605090a0203040209010602060613020f0c0604060605030111130e07110a0f020a17060f0c 82
    0x36130310f44180b41d124414801c02c0341154031035650551103a0ba10301040307a03072002c440704c4281e40b20710f0102c0080490010840403c80341c400c000010950034003c1f10344101c080c6172449490780300082c0160160151003051400703010107000030030291b130700400d80d94119411802c040940261901d000c40f5498031003070300106080582c084056090400101419801035250020000810740c501000460b404403003803e280000443ea80b50500c4000303070007000e0351000150000c103070301d03484400040526204a07898070740c1c9580401004194031707012013440d00416950003d02001d0500801050030149505000c00b501c940008280801079412000ca500101080b002c3e82c3c0c4506240c90900090600c03071003078a1013582041e1507000b8441650044400c2e48003886030140d000c82c6007106104a40000821841c00c0c4407000c0d03491200000c00b44601d98242c2c0c1b18419951200042d03104010201c049601304624001294004d240856070000e50303d41c1107880b101d43e412090346e99a00c440c1c41442440045034905914 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 123044082 1250 123042832 123042863
    0x40f08030109060f091b030c020a0b09010507081006020d0318021c0605160203160302030403080406180b030946120302070206040e060d081b010b01020318120703 71
    0x1e0f0300001c1914084011491007580c1d0340e1000c03042da0416421010041e43c2c109070410380384e02076809100d24003020300503207144d00c0c1c2070344810120000403109000181d469900304170b4080d50040d001640001401d0084040508200000350b448411034031107014035a40b225032059001e0120040325a042d0f00501d454080a101501f0802d03092000404039001d0b0305100101e80e06c0030303008a0b01115009258021820321800c0c00301c0b401045202e40040d0b00f0360004000c0400807450900c003c00140c0826241c05040e1202001a480300d14416800841440070600511040303035004a400c0054030546101512103c1d1400585002231340002c0c0d1a000c0c009800010340000222005e13480189402024421440c2e0b506d440290141d01c03600d60002d5100078100801c0c0700c0d55115041c2d284d0070803c00303445080d00c04019907480002d5400310400340c0d651010410b03000704402c024003800c0600f82e001e02c06507040965442c40a60141c8c00c00b801c0c0d070312501001c0c0b8411101c80d41081441c00840d000602003030b81800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 123045332 1250 123044082 123044099
    0x4150909021305090c0105030c0d020f04140301180f140f0c09010807061e030e0703030504090509120f0f09100507050601080d020604030509031e07300209040f080301 73
    0x80031503003280600b5060800350525002841560302c651059030103814204030b204011610382e40001e2181642c50414440c00001c0040381c4050718502c8010850b45594a080c0414100c0d103445028989100341e0409103440406c2814001b42c61146600410700075403645145000326085011000300c00c10351043c181d0400d50341e0000aa05105460280e403900f4035a621410750940b501c0c10f6010704404280c03001c0050344983e4001110403203048070351400095030030f0100889400c2c6030a5500035400180c0218041c09840c02130711400d44c10001e12001002000d0031b8400001c45405107808840302c410002c00c3e40d08a2003103d90131035814000080541917500c00c15200038180d41c01c01c040544043c811180049411800041c00784d840b840d55400078000ca5465580c1210039602c510b143e030707805002d0344076828550280c0840044908542c1e2001d8030805007465400e41c042c40420608a5506040050300000d1150001048100c9a0143e8100007541ea81b8101417013501d0500e040100400c00000000a051f0b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 123046582 1250 123045332 123045341
    0x9030c05011401210c060507030c0b090307020414090a02120c0d0605041403030705090402160b19050709050105120a0207080309071401050c0c040c090503070611060702030a050301090b041509 84
    0x601c10600612080039044d4100b01c1203024507002017800707030704c014140600c601038005000b0261013440c00500d05140c81e580e242c2813150640c6c1d81c441030392000c1941c20031032401c0c0c054504841e14400d01e10f07083d4540746038a25511103542c080a4001d5501c1540c0a100300c40500440a114070094003c0b20000c1e018a00900207080850b025a416440036416281c0d5803c00320440f40985159528141048603050030407009603c12810010480320502c1c0240001c2c0d91807030b90030b218124002c01c41c040042108140b40c152000200a50104858610184035580c0c104040d203c20422003481c3c80300554400102c40002d102c2c45002910040c408404c00c0038036200001c002c016500c0c03480028620002c40401950540180380c02c0740100d0704606225011410503901c00c030301d681c0c100d140c20703900c00365114040303410901141c006000080355415419a0010308104c56074102d0790034070003185040b1041400a1060006018440c942c5440d001100440c0e55143c0080000480f02c420460026544402100080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 123047832 1250 123046582 123046589
    0x2a03040807060e040e01060b0301090e0c1002030c0c0f010207030303050a02160c030c0f1802070203210d11090303030f0903040306110301061823130207060b03060c1c09030c05011401 80
    0x541c20311800407000401800381c2801c88000e100c0032342c04c44e42010003a0002d003035440324012091003000084007003540c1d15540300c80b014945801856913032042c00c1c180360520640302e120f0340c012903126184000340d990006c0c0800440f0b82500c0e000a80d5252480400040d12440c0c58640d980c244042d800c0c000d02c0700c42c03840c40040701c2c0304248042c5400c0e540d89141001080922a401080c107100c1510304c502d1080b900140081c501c01015a80304012014100b0840444102e0710800c6090114500c0504403030342c800c050304002552072943c2080301500c0000d5807844020b0080494101e5800490441002001600c001d1031780304000740304a5072076182e20310544e0801d110b4000040c4011141c44407414032102c11500351011200d83d00080c40d0700e8560290341024086800d074201b80d041064004403207007032020380585445110041115001681050300d000b8000e89464000f1004008000d143c40007214030b5180d440500d1008070782240c1a06017525144010500a45154202041601084440348807103058 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 123049082 1250 123047832 123047839
    0x507030605040507050a1403190204092f030a080304030f11060106050307080708040c05011103131404050117060a050402060d02070303050a1808041e150302030610052a03040807060e 80
    0x6a47e031480c049680c104100380c0c90f019044040003884941c8a00c1a1f412070f540042d0010070760b0203080d918408240401d00c1c03880c400c2c112000454080c216607036100c040c201b030110001c0188a4294648880345c1c8030160005080c80070480d400841c8038004c4a03102400c0f004101507a9240d83c0d40d02010308207900c1140c03104001520350000490040c000c908403806103804c0fa000d200c2c0c1608000044d2001100c00103070704c0c0740e403006101c1175400b1401800210081c04050500404030403541080c0000d07110181c201e40c9440341302041c909200c030700000d00d0070390040e101f01c0e003c1204c1c1c4403400410554890381000401c0365000050b140107240d0560800380c000d0100d12001c008403603031000070003400340908200078014501000100034484880f4041c18000d20780c2c80409452907550342003445044c40795802040860740200030810b1034603000180241a1aa03801c100c1e191100140c480e5000030f03000302d5050020445040114a00481041980c0c09480e0800031101c0142d25210068074528444600c00e10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 123050332 1250 123049082 123049099
    0x13120f0318080904110c010c200105040305190905100806010206090c030a2415060813021f03090b0108010e070801062711030a050712140a09050703060504050705 71
    0x151000d00764450740d50250410b000c681441c401e0020813010300320014803000205814410089400740c00c1c0b01e80000c500c81070301c071288591451806003019005010031080b280e4500403c201c0801d81040c01ca51680000c44910181da101246050742c103510150001e54000040800102c02250050750660140301d09030204c4100340d0307038801159035840c500c1c005e854141d04541c8250380041c603650194070342c84843c424031203110890550590219a201c21900c103030800c00c031404104980c0c004170010f811800c01420f0601c0210030307801190508582e10300754441e51031145601d040051180e03002d80d81040c0e2001309429556920041a806444141c0c4414000c1c05a800001010f2805101c0c0700c080321003080d240c2084100408401140c043c1c1c95880325016604c030340215904c02d1150004611601540800082c0d60800394401400300d90340aa101d03420516250000c5103d0381c1d850240d9074044111140418107a0761850a0b609145460380024007880c00c141c18482005404603030481960820f584015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 123051582 1250 123050332 123050351
    0x50f0f0103120f0c021c031701060c030e042a090902090f040c1101020a02030a120902030c060901030e01020c0114100f031209031b05040e071a0313120f03 68
    0x502100081c40000e280c0203540d4814440c40340103005640b82c90059007414980380786070741c0106100300541e00003181140804c84c004010140c2120500780110701940900c3c0c040d40c1000e4020b03004003200d680183c1440720601440026a6a5410119190910196040116161082051070b13025541240c070040740542d007020900070003520070344140c00401410074840c0811407050000a2040101050822030303c5120955183ca00b4001400420301c00c0d8021a915200c0c404010480954160380400c5c0c142400984d8015035000144005841d1044400c5641c584103400183d00a02010240c0007155001150f52110303820107500c4102007601c55801100c10b559800c1e054401d00049016541040c02203060034000700e0f400502403201c0700042e01345104040d80303d46928042c0402a00d003031606000401d01409a810a0b01890808030300070300081c446281020501c40001030301c4140c441d55a44040001403181144846003014941c0010041e000d94140c64401070100148081000200341801601c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 123052832 1250 123051582 123051601
    0x1519020a0309080a0b06060a020f060c0403030207061e03050606090316080d0c051c030b090a0504051608120f0d110706050105030a02011715091003020411090f010f020a05010609050f 80
    0x525111743c0c048100b00d000e41d242c004100c403903000030a48108610a11441c00c02c0c02d8400c11186006000400225469070702e5441c0007440c00f0b8990b0440380401c1181c4011080c031011240c0c0099641c4840d090100f06541d42c407012488500540721890b6040c070881050103008046083c0d920250b843c404113641c1d1000e40754500359040349010f4402880c1d9400b00c80c1e600401da1000f80d490308224207511f000704140150030001070000100b66004401d0355910b50520081003000c00a8001450300c59190304071043c81c02169940360300422012070790328040020078511604010b412100c540c0384003881004216a0006c1d64883e6400407401141e00302d18010011400c0d1a001810442d560782c1652004190080042c0d00059550041c0c401d10101c200c1d400651034540c0d130f107140c203172003100180a01220207245d4010441a5a0300e03008445034990300300085001ca031100a10007440e03003000e003400c68045202800480c68a18140c0d009802540780100c08280721065801c400d001d034000d400d41124540314240b00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 123054082 1250 123052832 123052843
    0x6041d0a05040305070209130f0602030702010e1218010e030102030c0307020f1c032403050c01030f0624020a150506011e0e0f040b040501080115080604050c1519020a030908 76
    0x24003c00e40a02c05c04c0c0c0107240c02c0081c00d0b4071442d134868060f60b25100b03a69031061141c2d25101145d00c80d8010041003240c550901c652013000100c5002400c49200c1c0390722000240c0328141c80c2d8a00b801c809901c9031800c1c2d000b2500740b00c50900c00760003199641390841d41710043d900199804001806a03040300e0014502c0003489004199038280e52070b40469501006a00504501c050b40c9602c080102c0ca4603002417901c1040e030000c0d805980a0310502000e40d00050407241040303007004542e86090000d00c82041c91281e080710b2840f5103002c00d882d11b400341c80180d1900102e40001894445500c0d2030042c044010340240d801070900f81c0700c45584024900300801001c281641e01d000142210100350040d10784a220b03240c1c20403028000140c00c00760301001c5070540d1003d8000087d00c2e91612002070354150108583c100402003640078204c50304040e940c003500c94506201051150f0842c0c29642c1508560b4422501c5e147c054074404032119a110704065183ca11800d0246c0100d880c02000080b5094081038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 123055332 1250 123054082 123054091
    0x1e04180f050c0315160e060a0801030203070501090f0b25050c09100e0a0f06051002011a0f0d0b1f15080709080307030c0c08060403080f0a092f06041d0a05 68
    0x4e13000c0d54421035840364a081140c0200108203008584404d2500c5000050408180340e940e4840ca541c11801803501d8101c840c0d0055040201440c01080300146020907070059451034202e6a585000b103c0315440c1c4812120304802c0082040132507030b010004005461031118000f41e519511642c1c032a024000440102c0c4a0080440a40b00003e801644940c1c041c05100c0085e200010380b2549a17008244404600880400940e540345a5002c200c10141032000d00348004030350003078407030810341c021400480c810320000301840140b2001c00c02070750a000701e04042003090009003541543e20440d581c406440386541c41c010444c0040454840d500c125004801d95012400079841c044141d0740480742501d04205c29100041d1074040403a8003201808041d0180c8e0003036440e02c000d810100a518420035025000780000c40c6455601000608011140c50328100039001174a03841c1d41d0b02c03040c0310010411003410796001034001404908203a05401000d00074805030503410455640300522002c4070b4040e00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 123056582 1250 123055332 123055363
    0x40f0e15011803020d0510050c0901090f05060a08070302070b0a2a0815210718020c0703030e0609030d0807021b030703060504080408030c01020a0314061e04180f050c03 74
    0x42c400d0000d810011216180a480b81c4202d4038007015090100742107800c00e0300c0e0101d50040000d500d002540e40042000050300c2d846580f03606851074000014081d11584200300c0078006600000380c2914040d5058604064000d41c2c0749086180c450310f52001401c19140740c0c03164000c40c495084040710301c400324003c8104191940b421603150b004030390002054008090b40d2002910b01030444800002d6003030600566808002c0c10001e04059442030410580c54038160300c03a1040c04142004003000420604072074140c10081d018030f440e0b2010568030300c03803030403079076090720131441941c0c261580326001d1880f0f461a0f600303071001403046905265034458690042039160b441203400b80f0104007558400340e08140f0400440745069590b1070a00e08540020102440e2a580429480e4403640c00d4003907400540050307100e40360103251540015a00009000748100105600d0b44d41e503005071103035404011011184c413403072100400385180074210b019058504890500034001c0085203401d00061349800d007844103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 123057832 1250 123056582 123056627
    0x8030f0106050c0c0418080d050708130c05010507030c0203190b01290d0b03060403050a090b040522020f130315060509180c060409090606080309011b0503040f0e1501 73
    0x81c400c2001526440e461a449200c51051040016041a005006007012303200d000c120b51400040103090030900800212031030511480450000307901c0103070242555000d003003013600c80c403003400c0454080c684503400941500c540300c0070040b950801400c0c0d138001c500c0f402c007020039a1b072609164002c9000c54070480494800e201440f045040303400f40502510045042e000031010350311000a850440305485c190b000c54000507070b0303d81c2c495200083d6000b4000140701c291501d80b03040e01140a50003441d4003440d0201d1207410840c4003c0c0c0640413a40c0c08580c118039a9242d04010b8403210400d2801d10040303c0b00c000707220255002c28168003600702200d000401042c42c40da514007000314020504417203600c0d140208002843c80313503101405803012f8411000300241d444494503001044801c00e0700903e82d50b9006206140050380c0c403070780c6040c140551540300011858107280003440c5000da034011841d0040364040c049548042d19100034405c0302c00c1d070b10310440010340740010b5501e900d481f003d0038068101d9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 123059082 1250 123057832 123057853
    0x30a030c1e152a0806040e07060503010311060702010804080c010e01020c1b0a0e040215040806070c0b0601031b0309050705040507050c060114010905060c150702032709070f1b08030f0106050c 84
    0x180d501245d005002420102c1e10500f03d01c10542411525040180841c038040014800d0010f64001500000000c1d20350504c2c0849035000604512001030000309807100004884061000c290001c100d0038003554001d6440300308081c4466120340d5070346215642203a81d01c2c080019840d01c0c6460328100c40003407208018544032502070104400c40c11001070000c0d5403c200c00100710408100305885000e003551030743e0741c4190a291540c1510030103012141050b0600760402d0031001c03c40c1500900d03614500b00001c8003442c0b480c002d4103000480c1d11155000b803802081018040d000402400320280100540b030f606d070388448002c00c0012201c080ca5000030444082403007642040340040400312003a00c1140c031000740460024080c2d400855600e4016040483d00c0e810541c00408000440c1c58140200c0d0180c9203107001144150314000c068008010140418018035401025032180c115161103072003400e8081400c00711010362007601d842011613047c0d4000a880c510420680e84001d401c10b0103440c1c2e0880 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 123060332 1250 123059082 123059087
    0x1050f061002071a040303170708061003140903030f011e0302010318021309050f0c0d121b0f0309050f0102100c020106052d010e030a030c1e152a 64
    0x440001d80c02507104000c00400e942080c200240d411850203c04076540e94203600d0000c0c0302c110f50000344074800d442e0906115000d034105074002e61040707060f100d0a03041560548102c000c0e00d22400c21481c155482000e0005d07001e40031000f103106000e600850406640d0b241075a00d01461002005505a6285001031006603c2608001550307040c110b4044422952a00001e503003010090044080a40c0c52207070004002040c00310101d005038400c00b5010740d0b07101e034010030342030b000d20b840042010203202c6560340c81c1e60040345003c2505013402c03030054241c0501e00d810001250100c00585c04142c4400c000078039441e084040c3c8203076a0041c0c0c05007071140701000c910405042a000540c0039075480342000305144d200c806048010601000b10603c90102000c00c05150101100d9101c5c100651500c0d00c43c1181c8000031014880c2c3e0380752801d00c1d1512001e00340100032a82080c0384030003030700d04c511a0900740413003071340443c00d0b0709022a4204070003526809204444042d090481041c0c6c01c4192001c0302e042d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 123061582 1250 123060332 123060349
    0x302010807050f07170306040f0219030e0f010509060f010806012106110d0b01080604020f160303020c1c170609070f0c050a030c0c090e030706021b010501090501061101050f06 77
    0x24140c1018145241d41c0c0d11000101204d102c105c0e0301c401e01200700540da29040c0960a065034445204625048000c8842c1d998180c1c1380c81076074180344d211060454690801c01206004060703100c0200000d08000e4982c40d12064155030095001d10721200100c0c01c0c41d0041045812038010140501d02c40c050a4600e001c81c1d12800b0060301d0903540d43c00c02d80c100d451080000c14035041e80394000110040007070000340c00701101a107c58084e6205005410041600d40100ea980791042208250150750320f07d811000f81c480c88011604500582d600b84440c0807034143c8020049031303241c480c00112070006086100c0f282c41200e2455003d00254040f40b4113900a9401c0c48840b41d59191040e0400303815107845103041711028088000860881c1450b05011014603100b0241841c02c80034001c0070112510581d89000c0d00b40080c1c40c0c10390005001c1c01c40c1e411020082c444401c2c0c64024803c56a603500008001e1109100e440003103503a058100414240c103124580c847c0b180e03024042000d444030400d010051 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 123062832 1250 123061582 123061597
    0x9080705011b062409060b040f030201050c030c10090b090a02091819261303020f0a051c03110c0303031b07170a031a1e0a0f0b030619030201080705 65
    0x2103642c2d51351000f950a504032032030903000441110f507914a15108502040321a20b9002e501c0100c824401880141450700070002100d40900c4e1084c0c596020301011070540c030a02d0075004051181552824482000e80c100c0900c00d07005202c4413a86503101064140c5a00080303400a43c0101c641c1d002403031120100342c098a041e0303071071011994000c9160940d1411090110303000e941440492052000100b00419511105c542d09050281004140403801d0008480707808003e11403005048090266160504400c0007000300400b801640800e40540d520241120201640000c1242440c031a801100140903402803001900661440d511818141c501c0380f20040010868201003001d03d0100340007400910a029041c0c5036181d0701c008459015040b0303001c0300220b1200101c0c40d07010071041d80d500031040c1e451440504081d180d4201010000d010b42420b6007041d16075500c0c0c2d51012407941c2d80e100155204440a84011b18034000c90b80008014240502c0024001681c40380060802c0e846030001e04410f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 123064082 1250 123062832 123062843
    0x103050a23070308030f01090c050703110102120a0c080a022b0608060c0406030522060c0306080d180b03060d031d060a0c0b0604090804060e2403060109080705011b 72
    0x100c0031114205400c18242c0c1c0e20640d144c00c0003009201d038008001c070f6103e00511520340d00700004241e002001d01103002c0c1410140170700180000c00a00f0190a4045235505101c0030900b00e014076141410500034a00c15a0300300000d900100010b60245041c4210382c200d403c1c0344240c2c4030786507902078000070364001440860030741038803400002141d400800503580107000c01096551160f05104c170040071034000400e030703081d83c4940400c0d810303180355000c00740384101d41c10510100d02c00b140303141d00760007a03c141d5121710b44c0c52042400e06040075901503c03051912020788020754000742c0d41e6072440800e000649000d90321403140098003002902402c0f4810050741c141807070703c901c60207010014089400c8031803900c0218905555000c1044400d034507aa60082007160100102034007a107031407406019600030481031001040301030b00305583d42440080c5040f414a0b03440c84414202041c60450b8000344d03012400301d94944804070704d030400455034005480d4103070340300f02104c108180310034000c400c0c1c0c1005542 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 123065332 1250 123064082 123064133
    0x14030613020d090303050103050f0a081b010905060903040f09110d090f080304060501151107260304230a03170702010905060a02070303020c04090209060909070e01140102010f050103050a 82
    0x24030b00b0141c041c5030440740c02a01d0014441d8034608202d4207000c06081010090b41059082030002881d03030041d41c0300380400c8251340d2401111010000e0042c00b240c80042d199106807802c0000b031040010043c002c0d505400010640b440d038401d41e500c1501d6080c04019200c94050254414040f8180c3c010a684ca0040d0035042e41349005413900724640c0c0c8140d40a07903582c0e4071079005010810f00502514030155941c40c0103800c00350004032594541140b400381252510b1115282640c040460845000c102039003411f40fa602e90360354003070002032005a009601e030006101c9000d451441c000460740c04603034210040c4544100d03800d440b100d8a6100450032410b01c0b8009501144507102d20007d061000100d03001001c10318103505001e450680c0030300c52248580d00b000041c100580714403403010380124060b81c0e40041d03078940716220707824542603820400004015400000c2c22000c100980c074407420081e0020131890700400c190800317446090002401560004089100082d404e02c0c94035210310604039480c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 123066582 1250 123065332 123065347
    0x905010b060313060522060504080f18030c03070e0103060b040f06030305070b150a03020103090204020c010e0601061211040b07030905040f0b090a0606020607050f1201180c1403061302 81
    0x2803040e0800d40350400f4554040c0d002c41c08010b010b00c81e458125aa56041d2003894400381c403482d0158024100003007400745c0320320218080020000030384000f5440f40701c03416105c845026041c1c07802003981c0d009034424410181e50b80e102d4100411035006540c010319050010360300f140c441c240640807606095401070750b640320545070010f2610a6130301452081da0750540e00e0300242442c40c0e4900e030103080340c0581031503150702511560f2002c09260440b43c3c2802e000c541c450403400010024010f11034100d08950070000005507101d80403c8060580f02a51948a40b18001201d00001c80b54402e5100c40221020001440311000b100c0c00703807428502c40c1c5481211241c482003c01c06039070040865906543e185c2c102d410280c60f01c95400b55229010b10000c2012903c0c2c030100a65591000d8100c00a01c000010380c1c80000c030030001299801c4011000240c05565900f00305101c1d44c000d910654421460720400e4001d06c0d00c2500301a820303c038a0680705040d81c541d51308202030026000c54001c8a15030810802 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 123067832 1250 123066582 123066589
    0x6050906032d03041502010b0a05010f110c06030a062102010c06110d0e070f0b130e04020a0b03040f02040c0809060f0a0204091104060201060501020706020a06050424051008010b010c060905010b 85
    0x92000d09042c0d0130901440170301038806400c1d01c00945241d441203100100901982c3d90008944141c0c91003132800700c074406034004050f41421f442d0f14607280c0000b0000100810b40115030403d0089409030f0f0720f5500c20b42210034102504121391003000340042c031400c81410100f0b0141d040ba01040c03556405140c039041c3d02c420044122402c2c0e030b08000494101c1c660410046007125001c00003071201350502403900344040c842c0d8800d1020790182e40702910460300030070150340362050f480d409000644213a60752820581044010036201c440124030030342c1403a100031650351241c850140209000002080980c4502c691100701c0140100880101c9078240300c001440800c40c0105000341c558807025568442c2482c1c0d00a00b0342d00a500301c60305544c40f070603080200340d50000e49071100542060340013a454440f031520401112440c8041d0f0060742c841c40003041d00052a0780901d00800d4006058620540d4690199081e0344c0701c0328016010074400403511004c56165040b042d561031040d030001401d0f600d1413002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 123069082 1250 123067832 123067837
    0x30503060d111e010206100e1611030403081c06120f0302030f04060c1104060e0a021c0e100e01051b0918041a07080f04020d0201090906060c0606050906032d03 70
    0x400c00340d030f0008144260f07950b0180407103604807038040780c0d414205080c40b4203070420000240080e003030b0444001003c00c14070300c0b9881c0445080c12207800e40e5621542c0b8240041c0e184c101551440899522402c4840004424032806045030383d00501070b4100c0203192a54403104c01110700c1a015408100a510040501900200050310711529194280c002a04000c14000d01c07161142d8012482d101e400d001e030702c13641e41085030310003030060000d42d4070340d4047e00d624400746140c0b0208040d141040710402d08078101080100d0945410b450030460480d00b21440c03401c0e5041a65014240514040075404a0385154014181c030403014082c10144650180c00147c0450301325803e40754001d81490350760303948026a40c0c040e08224680391400c0c0500f0302c552000800744000d04002e10840182d02c00c0d03400c6901401050000f420030000c10080300d80e581502511110342110f088604ea45031080c00b2407940340c03160145028505c058002c01c59819076840803141611170305111a0044448450245180b504100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 123070332 1250 123069082 123069109
    0x120305160b090d0201060b030403020c190806040606090e0c060418061e030302061f0b031f090507020111040e060108060a0801090302030904050f07121a0a030807050c0d030503060d11 80
    0x1042d98243d002c100a00711200c50700039030305015080040c040801e500107841051303c003048031005a04840a41c0c05900112142e1003409075000b80400c0000f0300c9070650003103003203031070b050070600c281c021880c22181c071000940d2100342d10440074001800840200b0240500e04a109100040c1403901c481d00a00c044030304800c001c0100c90903c00600403d5814844d56400c45c2100d100c006c1015452640221009224012940284808000030344690701c078a908042180c9030303d145003090340e12070f21190040c0008407144005503091503503003c2088420803c98088a05044040c0a60740320b1307900456121034090486a40004610750100da4a1401c0c0b140e03c1c2c040e40309030011a5100d82e1141804140c810041200740b1440e800400c00c041c2c81c0c1c100b540c45200c910074a8000441a40801f0a049034609000c3c84c2030f00b2104224000c0204254032009192b00f03402001120710b003100c0c2c601040745040d800c100c000c1c0011428008031311a801c0c40005040258403814201031280f01700c00110b030010b642c1d00b4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 123071582 1250 123070332 123070351
    0x1e040801061406070b01060c060f0504030206040c060914060304051227060901050913060816030501050a02270d0602120604050604050105030c0f0d1e030206010f120305160b 76
    0x8220108040d40b50380301c8200b0940b032240c00c14500780c8580742e008205110303071400d1101504001041058540c8448488244010100068201410002d54945003103408071821298220046000b0780200214001c803941c01e50f090070300c040b0030070500c0ba1940014000715a01d1054009100c00840000c02414079403010484100c407080400c01d6001c80f81e0201204039010f840104042c055a9a11070200c444100f01a1480030304003280d00d000c0001051240e100d651070340242400c0740c280e00c00c0c51241d107084a0140d80240141c1d11894000320072885200410351645088000f010001250300e0f0200060107001410140550126241c2506a13888550042100d0f0102c0c4100111031803d40320f980c4d004442035604000540c10500400d580307080d0114000c0c03050f60682c0b5103d4151b03503002d04c4211a00c0e48036403480d4070a11040491080c034510550114054000d05001149142040b03c044088403040d10503004086019207054800b075010007100042e0000c041648004154180003ca015280e501c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 123072832 1250 123071582 123071591
    0xe030403171b030a0e27100302101106060f0907180305120408100905190602040f080109260306090411031608010c050f0f030709030b070c0605070f141e040801 70
    0x180001007200442c0003d152107000b03c1000c0305005001c0c0195241c070303154400c41070059601c44104106400c83c148d44021740c44044e181c26084074540c0510080522012281118081e407071f5041007100300880d03044510380100c80c56001030382140c45101c0e00403400480c0c08100500301c1c0c90362542c0b0700781590109941059140000c042080031400c11884866241000c030800040790269522a11450b1408460232280b1003010b10b242485203540c1160003c0c020702c0312184881d0764842c140380c003804080005071000e58081150740e034440e10302102c1500308443c0341d40c064038507902c130b42c208104c500e000362041d1002000d5074218241601d003008558030015401c40f500b2080361409680c44d00355051103c04008004050044555444480055a0380061f010340d650b6100c1d41c0d0418101d40d40240b5500103030214040e0000e000c2d015400c02c900110311402040240284c4c0c0e54420255100c2c45844800c1002520300c00c800110b07604507002800107054440c40011616010f44c10b650120f800c03582050240b80d548 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 123074082 1250 123072832 123072847
    0x813060c0b010801021306030203060a0b0408010b1815011b061a030f070b18031c080405010c09060c02101b05071d010b04120501020d02041e090e030403171b03 70
    0x524401c41c01010190000d5103040104904030b850502107103d580181a004804141c055461401e014060301c80a2601501c4c1d44d40c1d248140d01030f0000000c1c0d24082c03011000b10100c4c00000c0301301d0510521400050480018810004591a503030000344003c0d11a4148040380c0003906d103025400d00083c0b4010b00000030402e000405040170354184440200b6449048100480d00e0b410086d01c0d180c035a003540d21030003944054040307418030310740a00e005030b540c85100300d6440c21504103820720300650051000300240b5004e0441507410b03048500030440400d040c0301c40d250040c50000b9050908486500c1d010890902c182c00030b2a0389036500e04112159000103d091110024921107002603208642c5564115450000c0c01c440e64841d0340903104d0940d030001c10310014002c00350101d40007910740e0502103540b02c1d500c0000c452444040000c12030401c9000c8000240d400032400341c000500035801c080c5142500d550b5412219508451054210000a001c0c00f403400881464070a29031311180040c5948086 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 123075332 1250 123074082 123074093
    0x302030901020f030a1b150c0504030309050105070309050402030a090501020c150604091703040804081f0c0804021e030a17130b0309030301150e041d10060503060604090813060c 78
    0x401200c0104030351300078800300c4809540170405000c42e940081448141400c5c0f070500c401e10314080044a4900360809180c5012039601074010000c607402591082010307034407500112160311400c0406000201901c0c0c1c180603510b425402590044000c0100052140169440509a8202071681c41c01c0da0000ca400103100c01081c4611a0f20041c1202e0410204051365120202c82d00d1000d1203008120b004070000341086021002c0390043c084c05011034009640081c903000e1285080020b021a1a0403c580c544d0210301038040640140e07030080c1001c404504220040303080ca0300c0ea103403981d4988519039040002c91000709688000e000f91140486c2c2d00d0700c04d02d198200704441075000b40c014500820400004010100131b4a05540044e840c0c02c14074100c01e130741240d0700958038120f694000c5c40c09400d10f0804098010b40b0420741b0b440c00a440041c0200241c09040f0351441c416160550411800200ea500d441e40c040c40806106441c2035040c010350700400c0c40c40100c15004070340440c14000c105402e100303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 123076582 1250 123075332 123075343
    0x6030f0b040204080a08030c07050708060610030b01020c060f040b0f09040b18041101140c06220c0302040e120d06030519020d0b070905060a0302030109060602030423010c0807030203090102 83
    0x50003950198038013460040e0250f0790311000440940144000b1010840c6103000b04122044c03aa040403ca44007075032644200d5071074032015118284a040d0840c00c00441501038054840034000c141c01170200b18400b10140041584920410650b02000300b04c00b189460350040076003411821044029110813080040c0022603512441a51148021842096030340c002d07246080d5000794001840c0400d140701e0001a02c2c14020100d03190300c060800b090f24121071a00040c0c403482145a8010b0032400c034a0000c0341d03200b0543e07500ac05440001580c4c42407001d81080d40200f02100d60402c112507070821446034154071a005072400c0801c40d52a8041007051000c10043c00c1018100803190312020340850380001d514040d10400100028140400902c10b24003555105004040140086640d01868080100203520074090303091814a005400328030184000240d40c1a2204014151621a1008068810a440c002c903180c1080302080619000440c04070280c40303800e119400850b00c415003d4006030901 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 123077832 1250 123076582 123076601
    0x30108070e090303130804030804080a02090109060f1e050d050d0e010e0105122802040302031e070621180201030c0e0306010501140c06070e190605031b1306030f 71
    0x8400300700034401828400700480b07030080c01e0840e04089000d10b07460020a2030080e0383c40a0510080440c002411910200b2034100c2a03108948425140ea02d8a41c8002111800d010b0650145000c0710705205200c20249000500401d64100741229a5030300c000a800306034403c400c030341076000303030111842150304004080c401440074200802003244090009000740070348400d22940d01603007404104008880d2500f00e81d0280b10304030503510f8500328410030b006944a440128020312a500c1840c4821741000703005490502c620024084852401c03d003200c9050521180036150703c3c150010030710480d014420078551000c07090b07182030512240d00015040707524803402e07541408007640011040f5a00440d0b018103503030003401d0078901c09280c3ca000d160140110920011070384115020300802640044804005e40421610042d280104282c0b00c10780c1e2003076201c7c180200e5401e10100b90000302c1051410145400d002c411810140e0321904540300001c682c2c084070209a80d2454100c509100c4d001d100c0e01c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 123079082 1250 123077832 123077849
    0x215070503060f0d02121510060302040e0c0a1407061b02010c0210020f0706151401051204121b0b150f01050301090c03020c0d09061d01020d0c03121103010807 70
    0x314a002ca01007088001040c0c400351241000b94540e01c1199221840320a0310801c08080b0f81d0440e1110000c00384050b0b0039945007070080508500052404d200f80201c03000d8400c0e00b014105d090302c9211840c0003a4000110a88c1801195a4460441c400d03017405401054040d4501080d484610720f034074240b118281c0015811641455041030403550001501c4032514600d0b100143d60f00300c0488020311034081c055004040390b00303010407a594030b0000000b8006852801c003c00744414820001901c19205000c085204800d802d070001c2d001c0342c200014411081c03204e04100044440b00c10b029000c510041c46c04030346085e020300900c041001800420241ca2205882e503076000e20181d00046d110b4041403042d200d0540c0c48180f45010180700350103940d50100550b0031110301442250703000e48040182e00a034000a1724114a4440c54906005007414401068010f0940108451400c850558001009409014201c00d803248040000c0c41183c0c075044417000c62a03140e50600003802d06148980e0306c00420b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 123080332 1250 123079082 123079087
    0x1018140a06060f0e16120207050106080105060405041a09030405040504080c0d02060702031209070b0c0d030b1e091b0307090303020606121504240504020f15090d030207051002150705 80
    0x341a6a0b0304045d80000034031104000f110042c210844444011160141e5240d002003408020840b0541044081d80c5100000344247c1da203c3c4240800c9030811100600b0003d60030072014510303190250007a420624540a403482d2903100d03004107050f643c099800b160340480004166400d00030500c005a203505092001e0109070038440e41c0299030780140c034001c8452503601c5012951900e01000750b000102a010801da80741c0c4c2d500e511554490880c4080b08000c00c2c2858000402d62610624111000b074412102c580d64110003401c3c00401034004010060f002c224000d090080444880030b0743c42011995900141c4500f1032900904203403014200750701540c1080f0660b0310702603020070048804814000809555903803400c0000072007924903c0b01d8480501e0f01030705244004030750804e92290340207403044032241066905001c0d4180070100344c018a10b8091060340039900e0107030140304200e4081c0c41101c0300180c40b000081e840201c807140079000b59010316009015007444a00603a0300c40d645003441030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 123081582 1250 123080332 123080339
    0xc010c0c02101b0f061506020309060708030402031510080f030c0601030b10030b040501060509070c0506060108060d08030f180604120507031e020714060c1018140a06060f 75
    0x1920600411001414000d290202c82400f00390301d2208015281c00040005441e0094204440109059042500009500c010120f4880e0002045071032104001c3c181d149000d4160710f8151b815040600220780c5809210b0b01d001c1004d1140344580d01400003140d104c40564074103d11a4549a05502d507011079410920000b003900c0804681d540c1104e81140307103485035a0720440c1e2414900842d8100911503c89207041c071003132280c154460000d0f51400c0c2d81000b40c1da11000310079110240782e5a0010000d500c0701001800f035511a58510760010409030000d4030303c6d0b03a2503403030300002e4000300c6032204071080c1481080351408402e2030348245080c814028000c41d0819840d141014040c1c2152171041c0103001504508040c4220103030038006141004042070141c81b008000c0d210b0006d849100c03803031010401c0d25030603440c12004541c6106c038040c0040080b180340002c440040d02d0303181c11000c0c40c0e610321703220301d0040351100d22904400780b000341c060440c0c080c642c42c0503000c0b241d072900000b0100c80000c0050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 123082832 1250 123081582 123081589
    0x30a18051c0809010e0d0602041a0c0d0f0e0d03030b04110c061308070206030a05060a0503010c0e0409050c0d05030a080a02090d060b0f030106080a0b0901020a020307020d05030903070b0c010c0c02 86
    0x32103078607400003000c642d29000c0000503240b00c00850481c5130022444052202031200caa0301410640354815a04100320001c810141030700c0c0104100c42c40c140d0000c009401d40c183c043e0010b03040070700c1c0508100c030000742e4400004603401c5032034205402103621086091203924081c414180820003080455051064004102d0f50b20040280354040d561014505102403092040036909013550081820359a1b10309a0380160141405a4900b400b80c492014042071900e0b042c05012411081c50307076864141644541084041d040c0242c060303805001d1000e03000210384403c6121b82c0054002c0004680d500d15008006145000007040718426a00c144020b111568910a146a00c81d80098010503210348402c000307440f01400e004826403540c46e005001500d40004958145030790b010380112203050703441001d02401d070b100b20780240c03005810030440c0c1401032038501060451280a1000c82b07003004e138040080fa00c3c0140c2a0020341111102040d00804403009004224000c0c246141940140304140d021 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 123084082 1250 123082832 123082879
    0x1c02010f111806030a020d051302120606010509190b0414100306030f0605041a01180c0c0515090a08041206060803090906061c020706050429040204020d0e030a1805 72
    0xc1e40f10b10000000b00b01d2082e1550107503405034210303940400640c10315204000d00341100741c000b03d0007003299210481c61907030003050443c45020103031201172074820000304100310440c17202019840c2031000c003404180c5140c103a0181c0054504064560144400f200c00c01c103d42c40240003c0e030800d414850244002901500310b203403101d40c4040c021031280c403607241410f888031070110b803100410002400016044000308100001c031180101c07c0240c120348240131035101c031940401600721380c041101080644001030b1a294028510400da03030003040c5c1035688440e9640194000103200714200d00340b405100951180707000401c5054029031810381c017074012411301c60b00104484c0c41744401048142c030b48400e124080781086404442159590144d10b810001080e00382c07400d41e01c5151040380c03640315654070340c8152200c501d8189103000c00c2c2d03280d90810019501494940030032544450443d0b84148007000036003801401600c8500f06000000c803074a07004041c0e9441148142602c1480c81c0c00c18030480031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 123085332 1250 123084082 123084127
    0x3080d020d0c0207140a0803041a090d03030e0606120c0f0418060204031a06010203030109020711090717070206100306090206122409010b0a050901021c02010f11 71
    0x411544659852450100900403120380301e1a0302d0030304904280650780402c103801650164101000a040d5001c24424134080c04d00504d400303644108404d006035030403406650880707450021064503003c00c0901003030309110051421004a5102c1c8580c80383d18109100340e6500481c2555029614040c102c00720f03558500708015140100700d04007200c0c240d074440d5001000b85449104400b05860aa4503101c0c009500c94031056820b000c4442d8010400010398160901483c0140d0003141980d00b00303000c0300000e500003202222511800e034445001c0b501c40010491140c001c0e03454584600c807464038502d400150081c441800c41d0418020040c40a03180d003a4102625048a00040c8a02c80d9101003001446044854021080d02100b00702540104020210070b0b24540148400da40202c001489802070084c01021161031040c84200c95903803003013011300703d0f000c0144102c482d4620540c000050b180710596044005035160034480c4280c3d8a9400303424a8a604480c0a6103061000390010080c1c0d0050103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 123086582 1250 123085332 123085343
    0x708010e06030f06010b0405130605030303040b0c07050d051b0106080d0c0314030108061803030402031f090f030e0a0e010308091012051f06020a03140a050d09050309010e0a0b0403 79
    0x11406a86041003c0f080304801c103002c0360304070350710340220344081c0d000743c80307817510a08005000c69201e40c4203010301c001310740307002e002141544c80c0c0c1e5480c9024000c3c0104042c01c1000144980c1010030b1040200c00c1d81d0301441d850360f81d900c00f040084805010f6480f680c8103600e1b07061003420050514001a4001d0180c9149017034070303441d8041d14084486c1e06000100918408010002041d0b082000c82d0300b50080c00d0758000020103003089890a074580c0070840f00179605801c41003122448240c5200d004152041d514400103140d4016603814038520900b400650000d01c0780c00022415040011951700a004042002041076245503205c85451090460710790080e0007104440601d00d01131042a01445000c6070140090314024401001c086109450800403000341400001c0140c004100d0700c06440d0183d0b2a030b4800c580c02030f80b4540d0b0358001e0604204100c0d0801800449145d10312950750440d2062010710b1fa19207403038000400b14901c50600c90b01c900307140d441c02c000500ca00300480c4c04403503214 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 123087832 1250 123086582 123086609
    0x8040c0b03060301180b0f090a050d08060607050f060109180c0b0702030c0d030e0406061d1905150301080d050f0a030906150605070308072c060d02040b040e06010305070801 76
    0x4000c84c3c094841444620303620042c80d6001d004002555007403602c50035040b000d1175100c0d83e9004c00700f941c402040348050607a80000d075903811464030540081b640002c002e401e4034a00140d030303958186400c1001103c200c694108000500500c0000d000c0c551300026001106074030301001c0c0c2c41d9207811482500c906921440006005c1c0c0464505004130300c190320004007000a2010346080281800010b8814540b10b107103041d42c04039040f0b00803a0072070020b00303039442d400b400103840300c051201c041e46080b1454030008804000107050750382c0d10305100000f044864519100c2d454551201d05c1c0110354501c2c00b0a0200a0003280300702102007064514001c1580f034046402d02032410000000d04c0c043d204001080e00f006004243c0d10380180c010a1894030a5540700c00c01c0d501c4030740031284c528410380041100c0190028901a620907100c0e881d14520008000501c2c00c441141d11070100c0c0d21540c0f2400d400c40780450200461483c403450164420004c0c00c1c1803000340b0380f00070000d0145005014001070320700003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 123089082 1250 123087832 123087841
    0x10212030a0b04061818123207031b0201050306090c0c0d0c11030a12030c030b0a090c02070801060b03040605130b0f01140303130e06030f1203040b0708040c0b03 71
    0x4075005100c0c0c00201800c1000707101d407560782c40c03c0f0760b4010000810b451170500060704a251103480d1204619038110600c400c00300c03010401100c03191564100d503485416440f2034908c0400e44403a06221042000310080d907520458a4090460742c03100404850020301c02c01d0150241c0d030400102daa0081c0215501022641c1e61201021036003e04400480d952080741000e608041d046130031281842c0c0204201540d104201042643d00c40c040000203080d0100d40380321040701d501903000300008400a09011844580c1e04022511114042d448050045d171103c0c0c150386c0355501480030300040c182d020024401a03050000c070030138922010b80010180341c1d80308001541c0d90129014a001c140d030089944406042c60840050701100a004070b01d50a040d4040340c3c2d40a15000088907404140c0740c07400c44c1864500703019000b40f41001400990503000c0c0c58481020f5120074454070034640c041c00e440946904040c1001800000014161000d0045034400d00000c10040b0700503008880c42030382510780c0d82c0d54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 123090332 1250 123089082 123089101
    0x1090519050702010b0f03060403020a03260f10060f05040605090117040c050a060c0b130c0b04230109030503090f01050421020f0907120c091203020d020c0f01021203 73
    0x11554a100542460700d030500c29800c0e41900a02d680e5001190b4980201d00c5e40420541c8800066500902591100140b64002070107a0301c00e0592511a44049482d01601e81e00e03603085007400c40f850a5021400c5081041c504c01c0400c0d010007a04403407070601c06680c1d120501500c1ca12541c0070303107000c0c80000700f070600b40d0f1380c0710b0a2600e0301107074a620090748070300340351401c41403513030322401103078402e2003071500114040303209480030110300d40c04c8120302410782c40742c00304520720207401e0506a0306d64482007400b00e0403801841c0100000c3c001d10305100752901c2c0302400303451881c0a4020f418100607115004002262000041d507003c880112a000868904200140c3d624851a4041d00c9400300740e2000d4500d5200c080c20040c1700718000e031040700d104804a010006004070840f048400728049603205908030480b80c0c0b09055404460500e046031a448512099001c046420102c005074010440006000d074140400c8042ca64150b660151003603403040040d407116501200000d06980200000740200c9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 123091582 1250 123090332 123090361
    0xf0f05030f0a0f030c050f0405240c100605010207050904060c120f020a0206130308011a04031a01031a0c0417100c0305090d08100e04080d150503070504020c06010905 73
    0x7409020301e5944000540016001c00e042c0311044000c28600500a000c442c0aa021135114440c0b50000754601030030b143c05c010b03001403001003521500e54065044421b00000c00020300c0c1d2142008002d060341108880158151155500310a0454024010401c1107444610882e9005580300001180101c03404400311414441c0c3c0d04e61030100f50600180b6480451150300501d4102c040d40c0c240c40d01aa10069111828510f50000600151b00d1000411203110902000740491184061070b910b8195a40c8498442911280151400200241c010020010314104080c162145044401514034101c0c0f0308840500581c49080030b0414202da400010782000c0c0b0404044006140f010404110910401801400b0448600015100380120f80540e00c2c0034000b054441c603000200c44248900f0034100c058800300107030040300c04490502030b84002541c540111002140a4011440410f03e0070080610302500c6030711003030003588100134018604501045240c1940c0306001d0104454558000851624 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 123092832 1250 123091582 123091597
    0x10809030c0a08090109090203010803090103020a020f070e0109060503060603060703240806090c03120a1803080c060703050a0908091009150e10091206111c0b100206040f0f0503 78
    0x7405202c072007008011681000d40030210702a07032141e0f00c41c1d8032540704004034031084c0506101c0e544280919145ca6109030010103802071944107580d5006101402c09142407681e40103a0801240341c4018003e44944d0f115407002410110300400481c20010080b0343c9400016040c0d1041540b1010218032207a00060448407a14100c4821300c050395a41b1820764070b404051700c003010503002d11072441c1540e04e4000340e21b0034110300c4100114682032201405a1b01c5c8445035683d807404490f50320f0008040380c910005003912601d01b5015011a141ca040d004040b600000c10100b0918a080104000700b00c103903055480204040d18140070ae50103204040d10680707001c2d80240400c59141c00682034041c1e10800200417082c0c2520003507001c44440c0019212003805000301c00c5031100104d4200c000c1001d42e00075941c85c0e5000480e85207020020580e03800282e0454003007642030f54885070301d090340d400c2c44800c041580007070384003800b2141020b03034804081c0400b1002c00f03440039100206a2040c40710510468400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 123094082 1250 123092832 123092857
    0xb0604120602030402100c020307060f121802010f0206010f12053306060a171305010e0102130e010e040305031f060c12020a0c18090b070302091c0206030601080903 72
    0x180140e1801ea0080d51080f9400c90058a0700010107190b280074480c0c1480c0b0b130340d00a001d000428140107041303a1a040030402842003154103600707081030500603c64003569580418502c19001c005000242070104681102003c6600a00c01000328000c070070a64000e071071000d408810b0303c039400c1c2803091030030404404801009182400d1880800130286e64000380c5101241507200503518441048168010b615600001c9442c45c00300319100d9030401811648580520030800805450380c80346800c44104076600d1085a5001801003020403000484034010050524000d030710798140f5010480e078000c060801000d014000c40442d240c0d000ba0001c84d00c00c4007801080500140e40d07090003d041c07542c0356406580e2007008924059a0605c00320340002050f0300300c010081c060307240c0704c1c4425190001c10000014542e5501500c17000880072100c60340035100c80c1d5005601c5a2441d0204600d0140014003c1e180c0311201200c5c13801a119101501d43c05003090910b40079580e40c0c400c0c0181075100d02d070301c950031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 123095332 1250 123094082 123094109
    0x15030b0a0e0907060f020a060504020103090f0b0709140f06030603100e030327060402100e030a0503040e06030a120e01050c0102130905070504081b0a0305070b0703020c0607030c02040b0604 83
    0x3980820390303600600c10703030b0010200c500c9155510000c1c0c1d0844444131480005800c03c5e910b1794041001a0400c0b40c0041c4103140c0028240755944601c2010400350b00e0403914205000f091052060344000150082c2c000e8008948075410000009040741c420b802a040c0141004400a000c0795800c0c80300750310300c0c1d617038038010b00c015000f00400588030307441102d8200f25540181c61030001c9000041d079190f003c0c5002402400c0c161216001c010144c10303041084410409199801c0d480d81d1410b0181182040c0301d0f4000f141c4660401c40002e003080c9000305107600a61018030800042509031000c8482101203040005100000760012942d51290703103c840040d42c000150101c004110070008403c8400d012810440707616440c100b19068461032003803a8061f8002d1342c13000005c21000c0f039414440c00340140054803807552aa01d050034004940c0c0480320403500450f81c1c10134181c051081004a20382122064505200d07694040e0804032907d40207401195a613100e40301e0f6403517010403038000d48046040802d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 123096582 1250 123095332 123095339
    0xc0612040303200a090e010e0f15030313080d020d12050c040306020c10050109050c07020f0409120903120302030103080d0e01110d0b040f021e07030903060504120f02120415030b0a 79
    0x605035400000203000082c003169000a00440c40c8070110305851230304998203216203d8200701c00307012401400e07003651444208508400d035581080101010031082e2514800c880c070f40f010260420012100e500159000740e568058015401a01080031043e008800a41c03625491030b1007001c0c3c022074000402852000440c0c034090400002e109900714403440c01409141e03200c42c149015200e0a441401d206d40c1d00740706140c014584480c2804039400050070000e41040c21307844034511070101503a00f10104540030380c01d00602520181401500080e405e0a40c03655145680e02d00086c403c4400c0480c080b55140940c0b061340c0420b410200500c14207442c555150b4290908000c018069006054865031806500200d000c005009441c49034002c0301111418108401c1100c0c950b41c40301c0c40c110304010040201000240d058840c080c09603025118403400d81d281d22038043c020031119006001550303c0001c404010002000485080d545100000c40710040c1c0c0da03405801800610010a43c8a2400d50010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 123097832 1250 123096582 123096641
    0x50a03180f060804051b10051608040311010909090b0a050c12010e070906020a02060702010e06040305030301080615190612060b030114040606050c0a3305060a06020c0612040303 78
    0xd40a03a0090046da4001c0001e5503103000c15102a80c4c100f90802c4840c00f4045589026002a002c1040704000364050168590358500140c0d000760800c90b004c160301c031481d400035640030f10307100d0141907030003170400117000c06032a464813001d402032001881c16100c030b000071214100d20007920b140400c10078a694440d40c40b4182c526801c84201e95180009905010001c3c030284001740c02c418803500034081070320300900c0760011100301c1e44000000b03400c420100000000a0400c0009600030071803800541050300788007495919003208450344501c01d001c242d0b000344901d919494080c3c01c450946c01c100009503410144274000c0d184543c082186d00320301000000703050081481006000340c0490707040040719143d01e010f4895000c0d40007000b0b16035000c00f0343c04000035076449600e07855071440a5184803154140e010165014a84014035542e1602c0c0d000740856800c0c40c031044000351109001401c0e130000b5405c0070076000d00810500c16490059200424240b50107a40400d01d9040f2036109480c1d0b513880381a01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 123099082 1250 123097832 123097847
    0xf03030c0d2003070e0f0a1d061903050f1e060a0504020f2106010509011809060b040c05120603030301051e130c08070908010501060903080d060b0d0e010f09050a03180f06 75
    0x10711b80030b403100440d003845d94a068203002d82a10041f071a03588030071b6556400502201d40013810f958101d0105010b01900301c4403c02d019008522460041c4100300075a401d240c01d01440c090469840190b01094050407400401caa6620140d82c5d980041c4680c1d80f400014001443d030061590000c250325075582010808020f1903505290400c00c80d041030742d0311400c3c000700725000d1040380d00e42800450b00300b0b840c041d1501f100e940d05000b01000315045818100140441e8600340e4904c01250001800d600050300442e030f0076a2000044001c1c60440d0714007004150341c2e001d2103500800c0d01182080031a42ca039078801e522140c407448504108607a2100000c0546003405c01d842c80400310b0000b204c00901103005000b000e044c0c5850307650706500e4a10715a1041c2c0705400c000742c109201601c2e414080340201c500c40c080c003454540850302240c01c20900400b02d084a01a503080c051340c42c00d02c800301020402c000741d6030400c2641842c00214004000c4280c03201c140407508541151880c00c0320000740250320214 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 123100332 1250 123099082 123099107
    0x702120c0a02030606030a0f0b041a010f0501110f061b040b0406020303180a0f021002031b100b01020604020f28180c08070206040b0709090504140f03030c0d200307 72
    0x3c4642ea6117405080541d182a0240c0081c451041015444d000452010925401034414003040c080e200c0065506141010240c01608040c0c6e1001c104010640c1d10156080b44003101d10003400304a001c214266445090040000082d21000180000c080c00b440f0200c400802500d844141c507280c80e580029103070750055607024410318807880c100041c0100400c01c5801540e1060690400f918070b64288982c805500d1107807002d5000030b0045955825016440c1c2e851084060050b01d03050b8540d4413000d04841396043c10604541c408020030005840e0000e10040c4d1714012101c102c24941c01c00c00090086a851002c8085075036042070000d120300220301551020540a28240700c9007521100c21601d9000c121141c00050b40030030049004903020a50b004c0e0028581c1c83d140088546481070f59040d55001e85080740c0e140341060340c40140003400d10809103107000c071001039461070070911502034240c0a2030714649011550b81c0020404030152200d041c2c02000110300d001e480f4600f200000d0702e070980440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 123101582 1250 123100332 123100339
    0x10801050601170604090f020409030305070809030703090e0603010b12070e15100e0613081e0f0303041203090b04060203270a03080405070f030c1e031a0702120c0a02 73
    0xc128658020550056852100c120310f42c1c160b42d6036003c12000c2c0400a60a40364060382c5654003015072a036001c4d0f0841280281c80205242c10100f40090140500410280c0c00380c109002c40c20009510003042400c65420008035a5140c0701c1c6400680101101000b65502c2900c00a001c030700c800740030440101b20b440107116504103170755408030540b030180380d082c0d01a0311a405603404010507015400601484001030545418048000005120b25000b600700c1c0c95603521200d650362010541184240800018001404e110307090300300c0103030f40c034040034000a10204401100f04100c03482030307005010858000c0040382940c101400c21700029841602d0510555903031180c00d0050381000d554103584010034800508403000786840c100c5112070040e0040b541ca0049c00000906281d1807031201010314001c0d100c042e0404d1a00c80014401d502c80c0740049069280300004101140381c00440b00d103d0310402d600000d040d40c0c0e00000b28144020388000d01402c00022505e40710181001440582403442a03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 123102832 1250 123101582 123101591
    0x20304173a0c240905010c0302120c190c03020a0506010f0501171b090a0b04060f02060906010303091205031204080409060e04020a0302061e03090a0b0c0909150102030c0f06010801 79
    0x1200300b12040880c0800142211042c03a07056880d00a0845050100a0344104000303403078400d9039102c6003590a881c0d40040007035004603000d02074440030b00c20103800101960140c0e1401e980741411a113a484401c40007401c1c80380049402041c54004c1c0805034180b540001541d03030940e100c02c4405102c80242c003410740000c140361203040303229003400400b600401c9032118016290080448189481d40b04007800340d0407280c43c000006c0c10184c607801400107031180341c0780c04421014022000381380540003000a00395a01c410010004250411504403e503482410041c0c5014420b040040c95441f8a10014802c10003001c104001d0040c500050010b8411006050050720355420707001030b084105850203940a1201103041006281c840010031100c10401200000d02c0708a081c1007520350421900011240c02104900c070800c002e480d41560b01000c03d0b080c403030605a5000100d044003500034501e40c160741c3c0c44811003000380e0080068800e600111000c8920702c3d50901c01c02903d0b58001e1180103550740c00c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 123104082 1250 123102832 123102943
    0xb030307120906201e0a0f05010f0e030315100302160c1502010b03060604020717040f030507050604030305030f090c0a12060e0c0616020103140f040b01090c02030417 73
    0x702000c21100c0c8000c00080a034103440070185403e8041008105d84284a50308000001801504204685034014000040d04840130703d80803094604405030806540c000300200581c01542130701c2c815034448240c0f001902c0c420020401e8000b031060101c1c090030200240141401c00800941840942c1c0303160202520301c94103c40180d00382c410000d40c5a40c1500030310009030890600d41c0c00342503114014071080c25900301c3c044841d11650311a0b0082003104000705418024000c1c204412002001c0c00c4c0e4415150600d1620003e00c01d0201501d16484440c1090115110720010095a848040b00800c0b000616a481c0721440c1c05012060742100c0d180e013080882d0f444820003103a0382e0784040016042e10f00d0041c156210451400d8030701401c0341491b50303400300c900d8604980940d0a2003022a003145003014102414010403d58059200002c85400c1c4003032030384080d90110950702103e8001d28a495802c1440000314204030b400c080001142000c00f142580c944090b030880c44a00700700041c1800420031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 123105332 1250 123104082 123104117
    0x1707050f01150b03040c0306020c160506030106050a110f0d0507020301050a05010302060304021210110901030b0d0c091d0609010c18030203070303080903271815040b030307120906 79
    0x12001d50b03080c04602404420802241c2c2c1c40000d66002d40328102221009880799200750890304415201c0714540e10598004400d520300e00c0b8418003904088462900f59803410000504600c114804a001c020300c85240c1d6412803400c20001c42d02108074025961149070152008090740c0000d28244d12a40c01e040110b00032410034442d540c183c1e40c000c6c0c001484d580da0340e000d1111695885030f130a0402e06c05c1d10300d00e6003166164801c0391004020300c00510b5807101c00600060a5955109010b072007041c021400c4e5000400e01240042101d02c00d040c0842c03194100140204101800c0d40d08000303030f009070020400c0094042d1f00ca034031b01e003005807500b0348041da801e400024001910301000b50141c0c000d0006001007070045510765071110111046916149110441a990b5070440c00e076404458013006d03010741940b500300052548050b0204040842c1d00e4080c400991085040040358041c40c1c2c1c03000a800c2d16103041c42103030100c41d008404a510304045002c024240380c1d941c401d500000d1030f039800c05142003d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 123106582 1250 123105332 123105341
    0x20a17010503150403090e0c0702012601090b03120f04051801080307080d0b03030d0e0c0d02031209060906120f0a02030c18010905041d0601050a05030601090b010302071707050f01 79
    0x8001800403e0030844825404024000280042c0c0c140001c070100051030f040d42c2e0003641d00c240c044920503501c4454902c00507000300d1504000140c082c28808002e200103640c100c200381100d80403030300840d02c2d1043c10086414842580c00e4200c1c4840c002840c05400c0e4184d0000f801218410307909100e103804441444044081d080c00b6034401c4d6001044100d02040c0b500c1d000c0c01095244800001d00360a60800091940d03000481d180c642a40304c2070a0070840c1401d01c05800580016500e4642a0403240d00003178032080707044103110101002046e04070b030645407030342500d400f030b0800703081c195507440d0b0351052148083c421078040341d072119031800207500b412540c002d89000710a004412070409503078800050241d030802031602d041280c0464009205e13901d50280e03001b4110703807036184c090101d41d4111107400c1c080160469030248404410411139628009500750458108040000740c050b0b02c800124003903c10882c005d4030419500b000d005075034003200000c105d9580314808490004400010040c281c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 123107832 1250 123106582 123106589
    0x903050706091a090f0a030311060f0601020c0d050118050307060c02031e0304320c09060a0e25050a08070306030203031c1805060402120111090609060702040f020a1701 74
    0x200d1048200c0c0a0340c9101c02e014111400c0c00034105e00c07a0305000804144800380342d030701c00d50001d543c0c10b40c0041c1070324080c01880e40040542c0c48403400c3e4079207400042e541da081a11080d0141c5203044003407042c84000c2d4083c0c00f48101c0078440442c4d400c2d0901700a503a94024a2007912030ba480d042e020301c4e80c20700010445a4002d07084000040c3c031450010311803215040100281d60011007011210410601c803221310b102c400c42500505004101d15200c0c0e442d0920007001140107203104070901416542c0d002207001203810316090250903581d0b505c0c13064004411806000c240e2500e00024a56035900480644080f40f0300740c0e1450704a80e68010101e0956996120194140d0800c2201c1500095045141c440c0f007000210080346460155601c401c8281000c40b045e41c103600410244411440c00302001c4104005940080c00004000d00042d05e091107815989481690001203a6100740c440300141c0784034036001441045203c1c2036050a0000e980426071150020740c40c0b548109600360303024243c030305a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 123109082 1250 123107832 123107849
    0x1e02070e010308180907030e070806060d0b04020102120a030204062d05130509010905010e0705030408090108100302130b01030b0d0f0b0a060b030903090f0109031a0604020d0c090305070609 83
    0x20781d1840c1c0301c104941d0f101421591400c90307585080000e0f034039110303240c80c0100c440743e034000303100a208440c0c1e500348015904000b1698001c80c0a202045e034803000082c01d125080417880229403160310040c3c1c40c040295064040c0c454000c9003044010382c16034040c0c01210115180d040794400903800c1d084080240d46840d0100b01f546400c5942e91a108d4030107032807002c07061000750100c1c40d119000160002c01c240d014a14003511200103000403000c62003da5040b85a5052080c190f0820355903403510380c0140c200840c1045030311000176038040d2901404400a40d0041c0003051019601c481e00c03805005041e1000340401d007000c8018865082c030380e982c2c403c2250890009900d1150a503244820010003030a44112551600c50204803000d1000055000320540401180d0700c1b80450144514001446031050501c5040d400400100c0c5400034580203840828002003001c0e51668000f4009000345c0b41e03010b00052030591050b0f0842c2c0c04c41180310580c1d0240d400c0b03401207580d48804488000c0c00e802130070803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 123110332 1250 123109082 123109109
    0x9060602030a0f050f0c01060f05030d1b061404350703080c070c1215021306030504050a08030a0902030f0102070819030204091803030f15051504080109031e0207 71
    0x12040c4203070f10b980403288080c034080d45000c801c40101e544603084400d402603140d54442080000d03074a2405814010403055000e0420a80b031130034041c1c0840400c0c110401100400505603040103030b10381c0b007031400c40c0106414031302504050420030502ca80303840c45040f40c000d424071001e2410506101140e444044041d0303080c80d20740650f4080714072030000313021291400c10030f0100700f002034407825101c0007400124554900041842c281070080d07102680700741050780e104010040b10741750812001410340c5c00608000c01c86440300d20b0520715020084001401541d804400e021508106800060310f450081701118454504002801c0c00c074425044000e1403180200035044085c02c0140c41804920f150303040040c10540c1c0d4201c100203592405d464003103041412440101010342611415a9000d0407400420243c1388001c00d40c00c039550a0700a8034840d0199a01210401c4100406c5800ad0002c1000a11414240e031074081c100e0541040c3c003c19251400145014081c030000b954004c03a0410400c00d00d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 123111582 1250 123110332 123110347
    0x3060a02070302010e10020705070b130302150909010902040501022104061b0b090d030f0b09041104020c0f03030604180b130305191d030c010c0813030203060118060906060203 77
    0x600a5004890840030b5549071007104502820a20407001400f07280400503a445040d460720a041044a4000040310703001440460b4a20140c40c141d401501d40c1503c41200c0781c0d00880c20303102240200d24115030b02c200b60b1030001c90110100d030080d02c00c403042a002c0341d540303c068902c141500c0e60104a41256108180b00410483c2e00c500e421007481450030702c0681400340c44ea118000254011a40d4200d5540000d1484c20f20070380c14410181c2880400c1010080d01c03584100143c102280500042c19030710202a2103a0140e4440c2e0440c1c844000300000c44100d96400c00c0402d449400c2181c000348214038040080c40189079003602107041c0c3e5881040c055407940c603071409108050408000341c0401c80f00780f041141007104490710280c4d00a1a032139041e4100c0034450300300e264480d1030102c80e000341c01c032040b120700780c0c3d80003480040002e030f0004003180c40b0814403030001d41090315a40302030f515214213000000d0126900e00c2e981125002840144007440d112140c0070240d400c18401d0038010b900c00c01226 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 123112832 1250 123111582 123111601
    0xb010203090d1101050903030a030911010c0f120513140316051003020c0102090a09050414010c12050603030d180b090610140316061808010c020a080d060306061202090708060306 78
    0xc4a03c0c03078050409900304154140481e14581102000f040171a65903d03100003405011455207200301300918200700b0300358281d9a02e42141c009080300404116011004020b0580100251005041d511032840c010301e0390fa1300804052102e01c2c20f000d0283c010307043c01080e0840002180070650b036000c0c1c20391203180704d0200214000e5100c11b0049402e55402c0c0307d01e41481e580c0b24220401010b82080c0410303035003030030304098460f082c00740585c409503031400e4080310489400088100c52600b1300100041c5c103945600100b13045100d4903281010592912403e400044c1072801c0c0703408094095500c0c100c15a030342c03c8200380c2c0c603041590702c0c10481c0c2c0014070800150800e03904155200308082e0568000f0035240029007001001600f003000442d00100c242c101c2c0084200ca90307401401a60020b100c0c44004d200040c0d114040b2150180c0400000928927400809980014004681c0300303e00300301c01591a12060091841c86404a1040303030781303901184200744160500340c01190b008020740400d46484811 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 123114082 1250 123112832 123112853
    0xc100f020915220306060608070309122d081015020601150e040905030406020f0c0a0e0c070506091f02090112050a090203031908130506040312021218010b010203090d 73
    0x11280c05080f0a00166461034000c0c1d0120040d4855100811610f0801a000c0e0540000809139000c1501d00f54183d4080342c031185090340081c42a00781f4070300132804200307403a000b05115104034110420001c080300d410b0760f03c21101d80c0300f141d003e0308841c001c580710314810810760000012540180d01000041c04241d00100c0b0001049400d410007682541f0070740c0104d401e0320000c1c1016113660700301050410509805200e01c41b01010144054481c1c100d41000140710101c0a006028007800504000f81c90000c640040741e002e6030304001200e01a11300205020303981c0640c2c02c0b02c00c210585241c1c1c1410710803030500980d000c0b590141c544c00189020498024020203005015542d200d4a07000700c4800358074140006d040c40011201000b5100103000005003980c4005424031105048090800c00855004a001608558189003c100070000f81384203402074050501041c88500b031076000e20002e07821131158144c051600070002d2003601d040d40010b9880b4007540e100301d40c010380561310810004a00948 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 123115332 1250 123114082 123114097
    0x80d0c03020715320c090111060f01080c0103090b1603020d020408070f080f03040b031323010c0201060807140d240f090305220b0c100f020915 63
    0xc00508000b542d485800e03501050b10800c1e0102d43c4c0e140c2c209201c64a0041a4210354900f65150008500010002000361040103026100a9134003285405050b8812142c9004411a0030201c0300b250802082a0301071460a10842407140b24000200340b59502034095400140c5c0c00c010410340680c0c40c15032525110080c0503d1204045d030030000300001d402d541c0702800207401c071500240000d40c280803c03007180c20a030707402030746a5900c1041c40482c4503900001700c1d0300366681545000c0e101e440d8400306014284005000400ca051000901d421907c0948543d856002c040c000034001d008a81405078200d40082c003c0c1b040c1c2c3e4001c6001400022545100d158900d240580403010148164807000103030005000044d2140e440100c1d14401c521989c06102c013000180344040015540640c0c0280c05441420b004001e1803034254456460b40d10142440d400070300c15178080300d59485003002020388844102502082c007514003c01007000ca0005d01c01c2e1040800c01401098000300b082d203111031180c21015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 123116582 1250 123115332 123115337
    0x40c090b0f06190c02190f051903020d03090e0708150d210216090902240901080a0209040906020d06170a0b0907090603060b0f010503130803090c0405090f060105030703080d0c 77
    0x740c100040e146e012485c082c40801c2c1803560a000c7c140404050041103a500c107a2107100a100078404003081c04600d0001c80740e045510039080b4000c1d00d002e0314000100d5200c1d070300e00f503c40801c006000740c020140c1403184014141d0381322840941810401c540031101000b1f4030405440e4404009035002052640450768140100e5140c0100540d407100d4151080d0848000d0f5501c1e04022400c40c140b526415244c500c11096518841209100c00031590040341c481604020a00340804e0800301075504480140c0c01c0603200303102c28501410000d0184d481a201c4104540c1380034800903a07901c8007241550040c420300c02070503160b00130340c80e5040502c402074100d0080340180a000200c030407440c426003005600c1007501140d250103040812161114407510070341030080800400642c1c0360881001c00c813051b4060030036522500d44a940c50715158a40c1d0b002a0070030f24010174856014000108050103001c0041119900d80e00c0340b0505440e06405e210081030f0074030503c1122146440e80d00012801c1d081c91 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 123117832 1250 123116582 123116597
    0x9121a0a0e0102160b010b0703050d020d0b030a0f020a050a030b150103061d0a0f0c08130302030c030d020714010905151f06030c0e100c03080a1103040c090b0f0619 72
    0x10069089134840c2c9400010061a40050000c2011220145004100803540e01d418007903940c6016145d4030650054801a0b6400116242c5418050380500314458000d01101c03400c50451515401c4805009001c1e0700c6000000800140341ca0b081816800307a82d03201c3c20f110b00503210100c05042055004124a040c151140c02c0072404694042911a40d518407101c100240e0400e041c14004481c0e21003140150070b410260344804150b000180a41c010004090841e4a2046424200e0641c080c2c031010340114000000c0c08601c04009401805902c0d0003110610b0348602204010350888034a240010125000800490340014110705420307400700380c0e4081c50402007040300d00746a00d00c09640040011950340c01610300303055489400081501c4007a1441c5914603a522009018141410750080400000c40300146d120101904015680715500c4e003000d07141c0c249407400d20303000e05081c000d035840c0501d4940d10307a46529100c2240704503a00061704003841d10344064808800c07803000c48202014081d90 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 123119082 1250 123117832 123117851
    0x30a2f180402190f0f0f110a0b09030406020c0316050d05030f0714100506010e060c07050409060b0102060903040308040e15090a020d1103100b1b0a0503090109121a0a 73
    0x550005003004145100800307a400c1014901500550406100d14208245045c3c90a901c6400ca0400c030b00500007410000103500308101500e1800441d002c001304804414000c0c420b0110000010b88140e5a0700d800750340c080e14110082c903585400ca040400c180940c203d80070802810314000c40120075000307a00ba01e103400d40303000d41c81700075512600c0220350041c0c00b441540094941802100c82c0b02507442c2c0c00384100d05040000800e43c00311003190b980304074000203004508a2042000f40014427000e40240091001070400000825079280910301500030340c1e001400030070010084509a035440940c0c24141400c183c900440c040b0020a21030143d41c0b01005040c2c0c3d035895039140d40c4500e9640e2405130b5a1134102c000c1d1000e9500d0b059940c2008881841404140616540f40c2425a910301107240e40360080003515641d6051908100840d9016110000c414041c010004048060302a00c86002840d0764244c0b5220300000140d014111b000010302007840d00046150041d00012441c0c0301042c40c110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 123120332 1250 123119082 123119089
    0xf040203070308031504140708040204050901060504140403020607090602190c080109140c0609010c02040b010314011d150d030305040221071415040608040203030409050c030a2f18 79
    0x2041c5c80c1540c200c08104014611840e00740201c000141e80240c907920b06080100780039040e4000948020700c51a20744001607040c880c01d521141c01408001d10500440c01d54400d4121a01d509035419001030242e00d00080046008841c24002c49916500400007441010021840103e68034001c6800009100740061326000074080c01410a0144810f20581c0c54480102450091400034440c0645030900180c1d183d070b80c02441c5d003081a0340540e00442e0a12603040100c000380007030514109041c009000201313461904055618551103000c2101801340c0301c00301c1509155844e080450342c016000e59441c4006403080e0050740e0018405800c8001203c20110040c58000c40444401139a5000000c2000044940719524401c141c050712003031400040c5e80d044c00c1c40d0344039a029140034018010f004c10110f407000c0027120028002c07003800300b000d4202000c91024940c000e440316000181001610000403d60400646c3c4170401034000f0f401d02c201804900200380c0004100100c041441c0c6480d400589 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 123121582 1250 123120332 123120337
    0x3120702040f1a030c04110a050f0702031903020c010201140402100e03030d020702090105090f0112050f0118051b03031911010c080f0703060510080c13030501151a030f040203070308 80
    0x410440b604600b5450f81003450710348000d25441c2803040341400301d600b9a01c40c0310401c80d0071460141c6882170351031401d032000c0d9010340f040040080d01840b882900c0011101706490000d049442076003690007103400d41d0012401d88920300031000492808401280051411504c20080000b413401d001500d080c8040002c1e045400260242091a0700000d1000461600190990142408550491850034005240e4411080502420700e03040040c80404007442001c1103003d480741144002030000741a5a400801c6940b01154201c45c0d81c400c00380d464002e942104402c185070a0060003c606000300200500b500a480aa241090220800301350113045028010f64103c0c00315501d8680845c1048001191400f00040c540c42c10145004001c1c13090750340384005003050380444d15004c2d4483e114140c0c510f40074400c94217a08098294241c00104011041d00000c14aa00c62114044425581c1c4e04040b17801d40f480000851203541040011a01006202c81c250843e00203001c649007552a0769a800051307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 123122832 1250 123121582 123121601
    0xe06010c1b0e0118060f09020c03270a06110d030b120303040c1706091b01050405041509050a02090a050d1704060e030106060c0f030c11060d0209040e0105010503120702040f 76
    0x80041d0401400028402403c4c4074620305211010454240341055044e42150940030700d0030541c4d00090310b402203505c200142d43e0300284a456419006d082032003112404120039070b200d0b0081c0c00301c6200051035400388184010b95400c8001504000300000e030110020300b03400030f040754000800c4038051840402000590311903031103014000c500904042050a081003c402900c0a6500070020803030a203c001c107103040581d0052000781d00b800040801600c03c1d00907500140e030828a8615094400310300f0078810030484890127010403498485074a50802e81c81035801d4503810121004041100d401e054001210150044907030a025900d8044004940e50180d404080000c0400715903107035a02c1c0a201d0400141558100481c0020baa560307540b8101140300c0c1c001d418001155070754010701540c001845c2a600008040d180c0e00d0031540e00750f80094000b081c0707160190349012601300d0400b1052060505a807001401401c1c006c2c00c040e450001030f441120100e8120ba141c152132155581c140c020200b01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 123124082 1250 123122832 123122849
    0x9080f0703120f0501080d0f030b060c0109020a0509070c02120705030d110105090303040f080306040b03030d200306030705060706020c031827070f0c0f0506041502040e06010c1b 78
    0x2d54040074090b02502d000e40c040e102c460340f0341001001030b10000289020490035a003040b0707180d1140743e45c00360024410304a045030400e000040c00e4465010660280c0340162085030525941911403003480040c8900300e030710802003803082e2100009440d004500d0640300303829504480b80c5544820200f030420650b070b901000440d0590052902194080c0074440c2e004a4010080d400d518003600d03996402038400c500a0702e01800040031800c60303280c940000302900c4005d0203d941d503100b0070b80e03d08000c01c814084101e14418401c400c0c0304846e680e4080740c1c00b980c0014010800c03213040404200d0304d9405204e0440d0151350030400003001c0340f030900203019400e107601083d0715440c8640090100b01c01d44011040244608120344c200c0066030000f03410341001423450b014104003c000c1003a14200134180c00500001140744104041040010780e291159201d102900560034464080303030103a002d58024031041e041039500180702d80d48035041d5164600e000d6203d038a00310b10090b5040d10240d81a0700221907 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 123125332 1250 123124082 123124097
    0x120090d26070512090603160e1f0e03030306031e03071b05090601020a030c03030e1908030105010e0109030b0a090c030b0910110403020d0209040302010219030b1c0807030309080f0703 81
    0x240310003480134020280f180141e03e440c1100e10800201c0340d05c8001c001c000b0700205018200c81c13951140a82e0922810080c1050400780275a1319050200c88584000200003220182c003591641804001d0340e01a060103401086118602d8452246c0040c0400c0c000419120900044011401c02c2001002c0c49800c0b09034100428140814462a04002003000d41558010103541001a61140400e8192034042c5030009100310341c80c100600304071a240c040c40c420580f01c0003d105101c401c5004504942c005d88900f00d50754560030054031100c100c0d00c0050654004c2c036001441c4071105030006550140b10340d4080d08541e89035070700e0002c02d001c1540c003c4540e070311040c00380c1c5000c2814803a00b00040e403c3d0240d18101891030340000d020321090311300207010700050340100e01094002d40584180d8003508403001045005020024010840381c1c203924406d1100114142c6250b90301005174240542041610303141c544182ca058001c2c0c050303800111234008040003010781a000c0740014207811403080d5603038407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 123126582 1250 123125332 123125347
    0x9211b07090e0d08010321020c1005281202090d06110702010207290f0c01020a0804030801050d0b13020a050301020406020a06061d16020312010f080120090d26 70
    0x61811440d20f82803c00d01c1310a000520100d80c0382e400c0c000540301004540c418414034807004908149415201603008007042c42000725440c0c0060141c40540005c111000108100c400c01ea114020b8410540010424200a030a8500506e800400d44400064180c821284642e42d464040312002d40300000e0a83d0041040021903a0601c05140100ba408101d00d00301c8041c0c0000040000343c116030110b121000042c8030044000b9127003174a40c080e078100021501c9944081c409480b040041750101c000807007a41c004240d034600b00710300103005d5810090120442e95074040c202c421552440041c3d80c4110b407014001210758003400100007900c015409042d8000491074a46c1c282e881d241c01012078100d00680308503251640d0340c11985d1115022010002d424051003050707095114584143e0000d0388844004515600314403841822159090002c12158854083e624444c0751019002052500d00f041140c00c54540400141402170040080c001c4050407422600c0160001d0641c01c0f010700d00118050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 123127832 1250 123126582 123126611
    0x1602070302090a140a050c0a050a140316270303080402120d09080d021504020607020a0305010903050417030328061706040c0f080c010c08070803040f0b09211b0709 72
    0x284c05c00b040d07060034006406c0c4085a003c403030080f2042d400801c9804985148254880d900204c64610b901001c00e90f6810501c1c03102c404445000c46078000b0484009651a02440d24141040d2040ca4282010001402e65408407500107001d03209aa2001000e640350f6030804041c001c910341c03040d0310b0b21075245d060b01d40414941401c40b10b40760f00c010341d0007100082ca41410622201a80564121101a9592958800248480c1803604046c15540ca0060307030b00c0403d90080e0043c01030b15480900102d100c00c440c9840c90380d13844211251905801c1099500b220f4080542800120809108010921a0300c40c02c0040440e00c411444500c15071241052000307001042031254060650705160340440741c03c0402113581d40c0c694107140703410010301d03c20100502a4501c265101c040d0312880380755881c1890700305a01c03001c2a0b00c10907a4031200325001300725030040009001501c01c0a08042000c00d0a40950000040c0c000c42142d0305041ca6200543d01400c0061001e48003503c00da10000580c1a09403401 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 123129082 1250 123127832 123127871
    0x7080403060b30120c0303040b060a03080409020a0216030f060504021f08100608040506010e040305070803070c0c091a130207021206040b0702010b1509010201090c17060f010e1602070302090a 84
    0x14078585078041007030341105c4102104070f9601642082070f60150351200008141010301e9030380040c0a81802040c04100d00340c16400420349035840b5070881c1e02010000d080c0b41d40d0000349100003404075011140034800100c2980000394071500080010410b81003940c101c107284101420b40800080300e680400045000304080000604000e10b4034040b035182c039641d0b1581e80e52040c040e030203010b013810000404240c419400c0310b283c56131003c400c60b01d905041001070100071441308110344182d082d1801041000f4544260740c019800401240125450001400001d4004002c1c22440c940c003002984003586809291225054000000340201e00e45420655640000a440341c002c590400060917050380c0c401d02007103014041280d4241d612142040113030b00401407080300421844109034005005c8540c00a94000b0610081c241d0703009070b595000c00c8c07a6030b100902842c0000401c1a0105440310700c180035207400e05c0142e0049401160700e030f030002225a00101e803e00c000945406d40c920f040000101c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 123130332 1250 123129082 123129103
    0x24030303060b2a0a0203030706060602060610050a0509120114010e0705030609150607120306051201060b0a1b05010e06070906030903121e050a020c010501050607080403060b30 77
    0x180c204a07500240445110094000e0119007400704083c032007002090194403405640102100d03500c9140c0e1800074042c14a5114840242c095800061a2420003182c99220044075554a5262144c440c6080e1416002120915007108601d000d50500420034420241c2000760b4100d111411b614100168861000041c405010000c003801440030300d860718610740750495803910f0404130528510000c81d9050080407005814002e012982d00070341500740e4004c00a9130300640b003d200d03600d50710306003d00307030343c241e208107100000100490902940304483d01404030030505086158406107072100c03801d59252180c0300c04107400140a21142c0c41e04031029000030f01e1141014841c0c242d00f030310090656490400100c54094445800c0907a0005941c000e118460890108120030304085010f00001d4022101d144007a41c03800c4004181d83c030300282a54440380c3c5c0584c0d09481c180c110365904000e0144d03148265080200d9500c2e1408442652030790490740b0800f0b0a05407039100f82c5050080c40c1805400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 123131582 1250 123130332 123130349
    0x30f0a05240406050408071b060e0105040b040512010603020603010609060e1002061305190c080105070503060319050102040b040308120a0606051204022403091204050d14012403030306 81
    0x244003400407600305865540719401400c00250f070f94460611540900c1034440003800d4001c0c0060345608510018000e4080e0b8105039900310304508070400640e018031035030042180c01c0310140820000c510f4907040e58841280c40700c0003c208a0760701e60110340c85030020380080300481c1464909006040c1e20568415081004507415600300f601054069280e1102422441c94203c40125250602600b0003e45c0c4d40007500105610300c08207141040c528034001d50040c0b0116508001c04030b030016118409072405182e000b0003030110900c420745003042a00c0c0c01c40d42200d07255003e01002640c07150003c058801140105035244c0d8449500c0440c80c05030341c0003005d920003d85866824401d09a0110071b03250001910038250b10349446900014925810064691801c1442031342d5040d180300802000d075004602c3c6400716040344000e44a0300305240030724001c0d1500840d020306d903200810f0b0703040803030103d41e05141c0000078603000c0c03007902c5c0348100031041c4c840d000055805410002c065041c422031004100c4134 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 123132832 1250 123131582 123131623
    0x5061b0c040c0c060c03090b09010b090a050106080112060e1f14011a07151b170405030a050a0e0406080304060e01031413080d0203040b0411061620030f0a05 69
    0x1044064660342e0700d200041c04c000e5541e250724003064040d92103210301c1600100c44519518201d6034040c06048002401c40c015031807080803d024044d5806014180c07070440c0c039407040136806c0c003880007840c075401c031020344400d5126502e0800c0c070101800304001c074040300041c24080e10340101c107000940d01d005d0303600d4603001d010308010080d020041c21292640700c04120301a44d21401c80c1003140c02488090f070541c900502d002540e241c0d02080c0043c0072480c0720b15440340c0002d2880480669554981201c0142c86c1da00101f1902f00b0721849134004000b0101c03a424800752205100340814101c031810b03000082c181d400041c0502007030b0b4010f601914a0300092070140720400e0b0b40e507a07050060001038208440c043c0c00130705140c10840680e040d90204000f5820840d16490641030101e01c07054252030503958601241c2c2201c0d06401e18100319103000100c4030704040100402e642d40c1c25890420344032841d480c41c080d922401103940c1400300d4504940140000c0404040c40c0c00c0403401c0050f032020003034041c0c0c0d29 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 123134082 1250 123132832 123132851
    0x703140301030b04230d0f02011d0309040b100804020415120b040203010509010e10020a050408100f0c0509030d08091603060905010e070302130203070207030b0a020c060106180e0603030405061b0c04 87
    0x1810740c1b07a4290300d28100f10029172105007603001d01504941002c0c01802c8100341030700c181001024240860741101c05004410014080c41440410305401d070f400038500c1070016005d400c0030b805c245914109048803082159031014a0707a0401c00c000c004441061000e82800190b24007401007941106170030000300054107000e200b0b03503074840360a02d003a207a4540100302c03442c00e14007940c25900240b200500b81c0e585c400b004200e07000208103490b00700582c40d18003c0c84180c102e106a09440074040081d008080030300300f0090a640d5208024049030706445441c0340c540585429080b41030007140b00c1c04000c42c1150b4646081c60035203030500316001c0c0640c000c200130005641e1301002c0c2508401403c0700145d4a07251560201d00706080e80d080902850b28040a004c0e070f400c1c1d503072b00511001c06200103480c8142d032100340807619100038414080300000540000d20050044d071400c2c0750001d1004045a241c1a03544c1c012441c2031300074505842c4001c07991075032501407100c10300150480c5142110b040050021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 123135332 1250 123134082 123134153
    0x60212090c0f0d02132415080103021309080a0f0201061205030406050304060e07030c08010e0c0105030118020418050603071706010611010f06030606050301060504110f0703140301030b04 82
    0x118045091050600f1a40c2d802952105072021500c2c1880944c203004902030080c0c0329000400c40b14141c2180302200700c00182002d0400e02940c044c1c0320690307510071640d18507003c00500410000d1403070b10090341d4003540000641508002c00581c01c664440c203846240164001c1d084604079401030300c0d42d1070300c1208440051004002c80f401d45a003814019201c3d00e4500b8200001c00304181445103920035034101005020703080b01000304440c1c0900082c03150700550181d480d01d5141101840d404500301707000501c440b10500322004408800004014180f503a203000380035260410000c3d8000213503540b02809800e04041c42000b01401d03048044654404c010410250703611014401e40d170401c8140039207020140e40c01e40080c16000c100103800c1c030180c4d440c1d041110080890788075443c401c0d0700e4510300140c181858004c895003001d13003039a001d05080c042014400b869220340310031010000c4410032060118084030107540a035000d400c1c201c1c8a0329080c40c148119404540c4030601c041c40700905040d8050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 123136582 1250 123135332 123135349
    0x3040305031e01030b0a1a1005090d080f091f021203251206060903050304051c080403060e01140c09150c0106060e091503030703030b0112020403060212090c 69
    0x59240c906203941c0d54450100b04810121221200b01407040c840001051105100c4198000d40e15071ba8204100054880c4c0b440207603020f0310320140c00c11107040c012041c0d035001c0d801510b071465001d4056000710081d80d890b450203920a0099003800310300810900d1440c1803c0480c8220310328224040203030140c1c070342c1020b5a0307001400501400114000002003000036201021071034880c80700c40407191403114a4014060800a06800c46c4113071070400000b525a100b100c41e0740403650040041e51a00d41810184907421441005046201c0c2100c1c08490008059400910003036002c2c04000401e03000e0655000d09603039040d5000c030a0324100e001032009003948241268200304040301c0b642ea40c003c0c1400744440c1405026070300d002c1d42d460072200103400c680241d103c2005105c2240c03642c80d150344600c3c01c1d8100040201030ba940560040c45040c000074029403004c0c0c00c0d80414186840262900d000980a81c2d0083c0c008607071164011950840d020034a80c2c0031a0070044000142c00d00c1c0714960046400d02 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 123137832 1250 123136582 123136591
    0x8091903090e06130903022505010e04110f0c0304060219030503010e27030c1c0c03141303060608190b071b060203040606050307060306030b181e01061d060603 70
    0x900080340144d0b0711034440007207a9050358000d11802c0c0080c01c002e51264114580c8509040c9240c0c1b9501540c01d400026600303456050312400031031a02441400001c0c1380c103e01014044c40c0070840c2d080849070b40d0000d0f100c180e0242c00110b41d55818440d0007414586a80840c0441403002021240000d030000162030640b05c0d4099016030035901c502141c0110284031012500c030b860b400c01d4802e00c2d1200480103003a08110308d011100b0b00d41140703034010900c170380032070810000800d003041d03240000303110711611044141040d19460402142c042000b01d0603011703500441d40c1a5482008200c2e158042c004e040b40c0103d40703003500d000b891454880b404120002890300040129000e05c0740106114003c90f0f0785030b00e400130342c219102d10f054a48a00181401d0080368031074802d0369400103845100b17015503002c0d240d008540c4170460300c030403160303500c013140d4029451254081d07a56400004200d400c80c1c0b440742581c070f80000c0cc511e4500303070f00c00007044500c0f8210302040c0d401808101ea240c440358200e9800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 123139082 1250 123137832 123137849
    0xe0403030b010c0b0f0105100912021c05120a0306050306070c0b0a060b0c07140306041101140403060504030f0f050a17041b030f0204053402070b04060809190309 71
    0xc9400000100c490000307290005012040c19000e0007940301c000c81702141610320680380d41140581000041c0c40107415449a0603003d0002c007241e030011308180d08001090a04107800d0b1405c982035682d13103806c0c4410f07107495002d64180824200700180d81400780300d00030318007034020b4022800c1c1741d40300900080b6808005421000840b010601c4004140d018000030180282c1e003e4441d100f802080f9280d007624440c0e2004000c080c4200b690074070340410110b0203694800f00d85007501840900640c0c581f400115001201042404004080799190040350710551003952040001c401644000e8503114120b04d00a082000a1082c3d0007042d8000c1c007901d64560701450200d0a6a50328580030030342110718441c00c40020070b881800130030414070300c43d0007a010f0b10844051280d595100c0c69044a10110b80c0180302d403003900501e054001c0c02e03031440700200c080c086c4165140252951b488100320b520bc0d500000c0041d9140701000700c071550501064610030700258008880c100070761070040c111005030007103098 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 123140332 1250 123139082 123139091
    0x90105010e091612061d010e25090b03041a0708010f0605030604020d091407061803110f040c021b15030c1309060b0a1707020717101104080706090e040303 68
    0x10f940c0140400c43c00a071071018140003150300c42d102100c090403015100b880500d040f130000314800e002d440040d0b02c907410190003045841c01188582075000a400004010710000444c00f2414a98080003942319a0081569510291040c100d4103e4010000c0c40c820400c00760400501240d2980d0041000b201d9140c0382c019280d4880800140080c07007481003000701145000e96400811040e0039111030107558030410f41c3d000316540c0900b503803108004c40540700c140307803105c10a100240205c41d075040590f10251001e0b0701400424081000c0f586409442000340e408100710350688451100645880c1006a0704021000e9117180f60980034000075040644040020421004110120344014002c1c0544081440119a50550081c25a00c100082c00000f43d0101810b604041c407001c100e0700414641c0d0007090807620381650306180602070503400d98a401182f200400109031801500300e4141e05000440e0384d9440d1151107840c2c041a640244144400c0072401c01007180755070131b61a400354041c02c0118 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 123141582 1250 123140332 123140371
    0x10f030209040b0d06140702010603080d02030c09150309010c020a02090703110d0c05042301140313050a080d0b01020706021c050c06090d120605030606060f0f031302090105010e09 79
    0x103014080320005640c00140d450130000070b02100e90460702a00c80324840c0c0c80c2c40b070f44803400102d080e03a049000182000804205c1203200901d92b600540e070107a0092541401c180b000e031f000a00d558100b020018224001105010300a002882603c1091085000070100010a540850710120005003041c0a042d542e0300100b41200212080307030103040342c1310000c2254011058024101c0d8016000c1d054105465400402e4188240402c0205a0f5816143c00c00c0040c808109401c3d00d50005117040e460360354030203441e000500c08002200e0300903c15000141c40c2c1800303032240c0e021203c500301601d045511283e0300f0002c441c1c021503008080358149a1008035140c003100b007030f00d003849010900b1105114071010803440410100314a41c99100c16503d4001c0488140d5801c1d0135a1400e00800d82e143d000300d00400d00710300d0f100c1c0060400c1200442c0050a00c090b0300c90f8654070303400031a48500c10100f14514401103162034420325015001c03d00305004030072200d001203001d0040003001e50810b0940c45151a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 123142832 1250 123141582 123141589
    0x12031e0504030b180d090302030307060c03060504060e010e06092202010302090a0608070f031e0902030a02030607080f010e10031101030b03010e0307060f0e062703030109090210030902010f030209 86
    0x1e901a41d0400100c00403804e020042012840d03211010414a01a8075481800d59105244031801c07a0f800400030360800080380c40c0e2030018030f80c400e581c0b03040c169078050005076030f1101c0c000d080c000c210203015170a15600d00144500c00301c5c00201002c1c03017403c443c010030011201c2289083c014200380810705001104920041e4000e02c210500c80f584140d598200281087c2e215180b24440c8d000d07581d411034100d482e50402e40558183c6050003080d001e00120992141d00e80e5840003003003500003800c465885100760042801e010040d541100020495804c000c40881c041030501c2c010089641958002d1500c0b1101124404280c00001d044540007108115103030303ca03421100200c2c5009000700184c5c500403001c2a0b40781e010403c1100d0f403606040005814a04a100e10070f501c85110015101680c1d415901f60f003044104624101c510140d04400c828101c02000a14044c01702c005c00020034402c2030040000e10002c10281030109400e0419000060341e000d1061114000303203050260b16910f030032000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 123144082 1250 123142832 123142837
    0x11010e0c0d150b04110c0c03011406011404090c0905030607090602030a031d0114090c060315060901180b0d1107020f09090111160201030e0f1c110303040c080712031e05 74
    0x40e5115040591144440d6070000041c00c03410b00306d508564404080c031702032500761840030a2820040580100040980d409440d01440312503001c1503091800f901ca00c040e20803070f00810844c50010380007000512060400308806508000345061100c1000d00d420030080d50392203a0b003004010142c868262881c43d0b1040c1494408018211000f800794a01c400d814105540c01200c2c1c5120320700c5404840003282c101350084a029800c0c0381241e10700043c081c0140300150703000c04c600904100000030005580500038150502030414480c40541e50b42103a10740f001a1020048400300c0020b0411021005030b490210035800b0300c5049d141801d50344e030741000040c010901e080080c840f28000044068001100305403e101d040e101340ca0030402039050301c0c0c8030b90b541c280300d0011030780c9940000304044d03062045a1118540050a1801c0a041c0c1080402c0908542040c0c0b81182c80891070740c414800703050180000310240900d1008c1000b6102151402030101c080e0140f6031500c050700a01c180c8896105508 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 123145332 1250 123144082 123144101
    0x301090c09080a060e0601210210051611010f08190902060408010603050106090e0c010206040b0a0b0d241506030e030405060f042120180711010e0c0d15 67
    0x10b07521031043c02c4c01c141c03010b0b1210105041150181900114094013001c0042c07903419018204440c1e20030940d800c1c00580e0003148400c41c1480308c240034000288007000316a01c2c40d10b210390045d0f031242e2512000903010304090345040d800d20001208109c07201c5e680541d0810041c0380400301007001c000320300108030f8600c0791b074205054550802002001340801500214103c0f181d6039020086501c42d22070068031184140340450060b00a28082000700e001c1b600b00301e4003c0003100c1b00061329213022000401044000d2400c4400341d11001e0140d104a802e140b520301703402d0301c40c0c0d410b214030741080c04101c0d241c5445010306014190317140e400c0b8041203400c00503100602001f400442c0d8071203500c0508001c0b034200384506100c0b005407000c1c84078100341c16142e0058244d402030a41d10740c408401d6007058034200881940390400c000f102554200e4140b120a90b004501503281d94031041c00c4401001d0a65009800e101142d5104070798510300e50320b6015440460707541252092140450403107413080a4809100d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 123146582 1250 123145332 123145349
    0xb09131d07150e03010b0a0e1b04060804030806010e0321120c03040c090c050304020f03030d050c0a0306060c050a06050403090b0a0e04050a0902090c0903070801020d090201180b0301090c09 83
    0xc1020500c221444418203500c03116031102242d000f041c60806007603c0070b601072103400003102c81007009041c2d41c2180250b042400e25440c00d000d050121440c8981d50402d0b848400000c0c1402d0038041031603081200d50b03402403401c3c6440c00ca44d45000340132079a0b94034101c03001a0000700070401c0365094000d00d030035103002c100000c0004280303090269109022340c1003074809550850b805600000c00c020b05201e039021030080c5898241c11682e81d03408000f00e01014070b5880f030b0940400c21048000314407038401d051080703202050080e1038668513038006040300d00640050007404026081580801c000083c42030038680e015401140720344d036a01e0129511406903115a03080140418107252264019003140070ba42c0702134900b0031a960b103400421090351031802019404c40d01000101d40004413900003050100302c09401c60b851300d42d542c007404d800c9030301103044401c4499491102c001150303480301d440807100316040f201d40c101a051410380881440184500b00d030150303032524001c2d0258062002c1301d0061400a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 123147832 1250 123146582 123146593
    0x10030816020406140f0303040f0b2104030f1d010504050910030b010b0408160b0d0b040b10050304051c020d0309030309021f08010b0f04050d05101d01060b09131d 71
    0x6989036084d4540c1414294461081200d200c401814000265801c503001c032104941010b151451090b81680003422a0207000788000500c00716420391400d060046100b90b5496600d50f004250040030b41101c07801506000a030340f46955020303030744402990240c1d4402c41d00c081c45500c0c4c00100410ba41703000d9100402000d84c8400010b01300c404540a0022502d0600036280c1a000d20070260903a040d480c0030300c082d2420240003260340d9418560201210160250000a43c02d803400000f45503043e1401c6040c0008800000b00400c00009004130300400c8072114295010705482100a91a4110290903008140e551044041854400e80000500300d40103041c0182c0010313804120ba18444010810b900422900400025110542c0040301c00024174683c455003420705183c100304024200c94015548c51080b0580b0f10000700e014070070112000d038560400040d0000c1d072040d5a0a54002d50b01c480b4041c8000d002d2071079161200800000b04100340000054040c0394a84064070840d810b5400c0500e601c140c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 123149082 1250 123147832 123147839
    0x60314030403050d02061608060a0b0c070f090c2003090a0603020d05060109030c0504020c0f0d030903020601061b120c050609160806160503100306020d0501150810030816020406 78
    0x200081050343d0180c0300f6a0b0540a201d04142c0c0c0c0c9000940e402c1c1e07007030244003c40c1440240f0643c4500d070442c030018461030341941c0d10030321807845030060911207005403c444c208000104030b0745446002400c50302420700150300c0800c40a401c24043e9001c510244500c1c9d2020000b9400c140300721021460010702d10004a529450014000c0d0070044051042a02d06004103c45601614440c0c0489a201d50400202828a01400003a40060004056034802c40500320204813051001001134040c0d503800091980c01410001d140c6603044e406a81806000000181c1d180074074011076418035041903440900e107800c104201e030110158840542103026050500c00c0ca51404135445032000c0040851243c0940c4400070252078280c25246040e049a410002c29407184c0100007031944081c0740c00540d5459980d83d150441607070300600d42042c03001c1c0d40b800103110710217112208001c1480310703161050440c5800184115100070500024011035004282c140800b5010703450002c100d0390240040c84602c1e503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 123150332 1250 123149082 123149123
    0x1e100609050a0506190324060b070201180f151403100e071103090f010c020613030b0109020a020c040b061b0106090e1f050c121504060f270603 63
    0x6040e0b81050215081c0004a5070030701e00b00200143e88071440c07860095040c0380d950382a90f451040e4000c59403809a0022809440d8682e2150308024041482d4559582c0e200d480018080e80342a8903942ca020800e8030305110064191001d80140d905408004175445603503041034981c480040e04903c10301e0400010011004003146174501114021618100c240d00e882009459101d1078212111461b8018440c407052071130f01c030402c190050018140300103150013507004a2500c0d07210102c4400758a15540ac100108120160844d00401e2a02d20450405d180202d0080d202c6041449040c403850310b40b01c04421540d103000403140f04e00c1b0303002c5c3e00e80002036103c001907010f0091442100c0d000c51034950703001c440100118407c103409030340221101e810311303038a40e5003801480050294542418140310440b4040051104603004c0e90411900d0b14994240d60200025039410f50460803541c5080c441c10461718039a500160b842c001420060b2100c00c1c00803200300b00034000c0d43d00117841c00c0c9641d000403030b0401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 123151582 1250 123150332 123150341
    0x90109031409221e020307120510030b01030b0f0601090509010b0c1006060f12020414190b070b04020306070e03060a0e0f0a0b0103020a09020304020306010308090609130c18081e100609 81
    0xa81403035a480b051315000c0d81d002d00b00d0004540c0c51021807400061141d40000c40d07804541e0000043c2d03030402180d074498941e1000300d10309804c00c56034400c2042c10b024603030700510407459008400346000300149080001107a9070000612400d200e070103002c240c5460380d02082c0803c458121b2400f004104559854100138108400001003d000c2260520000c10b00030450080f102990070050400f141d40dc440c10900c600e85112610070311b0a4000500b0114021500c900142155802903001100743d0400740101410980094900c2080c1316072011010a1603c01040d2140d110741d0903080010146200c5801908100c2c1405416900b4001c10307205904004114543d141a00d000355810108146c584441c0002c910069070b01a6140c3d2006004000080283c0f00030503034400060704a134109035529020070103080b043c200d0400030585800079240c03150381c05501c0d0170020038025222040e0615101d1310984034841c4072480322204c1e20011a064035078000b00306440f19004c1a00d41080180d42d00c0b06c1040090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 123152832 1250 123151582 123151601
    0xf0108030f0d0b13240b1303030e0d060c0e09010506090102150702070b040306090b0c0c07030605040305040b120603010f11070b1b04080609011b0e0d15020d05060909010903140922 79
    0x85c0c4d0705910200e4109414810384003403141039008210101e0658131709a80728843c0c00c48455010600807a03e10006015000301c1d0a09c00d07254840c1031019203c0700c10000c111005800403070003000140400c020b0b580e40012002200c040540c0c00444948038280c0c2203003800307500e800c40c19004800040020400c00700b03500154980d80250f000003281d4540500700c8900d44070b220860403450303101040074000b02d055580a030350414424182070345030554450300090700342c0043e851098100c03400d00c1004600d060a0242c507540d00d030b2000e402c000681c3d00c9a0602c420380103800010304146450400070304106201040703480e80500246480d502d8940d2100e41c00c1d904d1070101c40032102d0f5400e0030913810001d030032017482181c0345000d52910f10b0404103020510401600da40000d0f81c032000c003018808184a0244010322040041480c0450180381000920500c8000500650b8541c0c0c0751400000201c0c0e801018a01202e542c040c546075a501c0110002e2410114aa03000b50301c0300c2c200c44540280b110603803154220 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 123154082 1250 123152832 123152891
    0x80f0c0406090504080a1d040509010902030106050316030f020f03030304080c01061409010b16061e052409150310141303080705070201021002120f0108030f0d0b13 72
    0x205a02e0388032410075144159070040c011181484499040c03401120080c4101c40700903030020104100100041c00d948094407a008135966801021046d41028090140035090942c0207048081000c2c0681c0c901c42c10900c030180a58043c0741d91311003155550103e90307050f803200401f00c0e038a86c00e241c100080180e00840001125600c0e0800020b0010902d03801032000c040c0c02460ba6842d680f0b08a0314030603e51003003500b07010301c045a030380700c00020348036118080c030302c1c1c00c442210384040d100c904035401101e0016107030110140780c000c50100807580420f0f2085480d0403c5d1040d1115446000f41d806006000316800d40d45401007401ea00c10060050b40a000c104d0074140b800c000c96203074038003290820041a003000e40000c83c06000100d00724012030041c840148103104a49804048060f2340c01203030085006d802c44208010140034206c1d070780c0c510160140410707101940c5000000040301c05c10388222085604000c2d2a030112407490387d5009080c2e240c1290380007051004400c0c3c41c403500d071956180202d0095 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 123155332 1250 123154082 123154091
    0x60409021b0a021318020a030503180301060f0506090a170105040b130506010306240e07140a02151008010912120b091f08030a2303090604060b0a080f0c04 68
    0x10700d41e000140340c80803075009800c6090b00d201e080300603c054079400900c01101000f405a85006031200c10000b8002d50107840a50784070800324607018031407801043e88602c42c0e030501400340691006620301c9021544200d421503541c04002010440600040c1c0c030400580485140310034a05906400a900c154480c2c611803101d61344040122001c0f808010004c0d1441d8481c0340180009040c542c02054120f0b9007890005c00a081c66801445100c00d5400c020700403c00107084c48401604101c00000d21840030b0304290811281010096603105a0444401d000010030042000c40184c0b136884000f80401c50000c3c45030690324180545008400291000052103240c1c00d20b44070302c03240c880c100d10309100900300419034513600c1c0000100e120303480306401d90481441000990f910304100514544010b42c0720070031149100f01501c4107001c0d880500c5450710310100100611020041411030b0300c55408500014480701e2103002c50210641c0b500403a50307a129034030821103140d800107103001020720300f142d00f4807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 123156582 1250 123155332 123155377
    0x207031a0106051b01020f0a030b0a0803030c1804200c100516050903010b091317130b030403020a06051003060b060703020a2009160201150e0a0e030906040902 70
    0xd0510034400e040010300240113414580c00c00141c402c1c54440108009818040940d42415142d4850f4600d400865640d004c00b80c0c2e0360070030283da28018075071032004c1c0d425468051400300480c46000d500203a10401200103001c503956551041030107a51007200c6d81c1e100594241050308075030280240c4081481071540d100c602c42100d00400c0e11421582d100c194101542080954490700604d1905a055403079110660054507200e01040c03041090701e80c0c030108810241054140502034407095120400d04000c07032106000803440d030354102c5600c030300065505d40e21810201e0400500f101d00500050501081c400e1000040010b00281c030b006043c00c001603040101006100c0c400e4a40060158001c2804440880c0304400140414010300d1444408217010500064056104641014040ca445407880d00c4d400e80c24842c110580350f0f400034040e00b403030400c44441c1418600501e030b1610f00d52200d40c0362011b50310910688038821005822140c51303d0b1038280400c080c3d0082c00d0b0780841c200c034141034078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 123157832 1250 123156582 123156623
    0x3190318080d050f10060c1e301b151103090705011805060a0c06090501021804023901050c030702280206030a0b0603190e1506040e120a020703 63
    0x54018650b40e21740000280c50104103681c010355100f41503030b0b06d2001203a418030042c030200c0004403083c4200000020304a240172601c40310040c503041c0c41d0450550845540010380c0015901d6100a24485803c0109145143c0074410a0440d41c04604540c200240c903041c80b0640d00c051070190003801c00780c5a0050700c0b01c004403203070440c03000c0c8648400c541480070040c0317040c084020605107003a1300c0c2805e0344510781d44a00c003c1e1501410102c0b8581c3d400100040600d503110b558800365042228154544042c6008149160358021700c0c0d8015241000d08020b44540401d003415028641c8200900841c540004208c010740c00c21150b04000d070048030f504000c0200c4100310310556016000c1c04400f0701700590240005904010408001c1e180e0710540ca00c400e958040140d8400c10502c001002e070303840c3c0d8100e80c00950b0f5080b184c201e02580454034504605000300d401c1030744408156070003d1019107a0003c43d250850211401420b00c0000510b034080300c1e40130503090180c1340102c00803840d010344040003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 123159082 1250 123157832 123157861
    0xa060501080124090c020129150405060702091f0e18030c070b07030e0406030b06041a0d06051003060501120c060e0904080c070806010b07050f010e03190318080d05 72
    0xe1024400f502e5040c041103090782d11030903680c1101d100008681c1d100204682040ca900086100d001d034102c1c21803c02c0b840c0c20050101010000198282041c0c50500841e5581c05034040092040987c0c5001072050f80d8026410000310001618402100d903680e010b14030000d109a580c0e11200410021080c0789520000c11100c13232040060051028030700c1d01c20b001540380c200711401c50400c04da480300103205540390b02400c07020f90300800d407011080c101542003100f02c8600782340e44012080740804405d4160b40391401200140d402041c04111541c45492640d0806041d07003000b00003e14110001c1f400c03511400083c2c2c1040c1c80781d01e46105141c0c4550098400602044009e41e024002c40e00090010307001201130700c90394000300e04031341145480e42942c4e81400d400b60001e00000310003040000501000b003102000c135500e40740c000c0100d140500600341d101d02c104420a40004182d0804001851107584002c401c000304a10a4916160600c0c051000e40e102456038141d442c00c00c0045691100c40012 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 123160332 1250 123159082 123159131
    0xb27060f0d030c0305040506040902030f07020715030f06051504030b07090f030311031201170c0109050a1a0403120201050406390905030a06062103050412080c0a0605010801 76
    0x1016601441d640d01160140381802040302002018400003d43c0c1e01c402019002070300c22a180580c592800c9280440c440b20700424600855011070410040c06c232000d0f20452003240107207401300c0d01c0341d001140c1001400c441d40c411038002c1800b144451b0840c104101620540f03200302039114603a25006011a032940a600420030340420b583c608000003401050801059072070f0900703807410302d400d25031b4008000801341d00004a141e039000a0400c118414411500341100900300141d4150810021803c14486402101c2829507000a039890b91100c20701950003d44c1e106c924000c2001a050009010381130940d000c4590703909180000c226000f0300070106c00550b40880100c0407402002d41c0d550301c42500600ae82040c01000c82000c036480c3ca05210350200303a8007641d0301203201860562710b54442d020000045c28107003501e0030401d0003e64402c08990494500301040d020655950038042c40c0744c40f468560410601c20300201404000d4a500480c0c1210008802008a51012800d01e02100c00414 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 123161582 1250 123160332 123160339
    0x2070609080c0f0d0213150902070b01050906010306030b04111905010c0b06120106030b04051b030303150604090f0b030d020c01120e160605190e0f060307030b27060f 73
    0x50030300b4490a06054040c01000300401c441c00c01a5241c010400007001440c01c0000306844a01441a9900300e099810080c400042d0441c0752403da03807145660041c043c0140f9229441841c0490443e038880c0c0c20a04c00b4540040c03081025040510306900241a940161805920900040c50072500130070050030841d01c068440c01c42601403075460001080b00105081d6000d4a540407032009548240304560146200b00000602c07800c25042c014a400103d40842c1001c440d00b045408440d1404030941e0b80041d003640070900e80201c8840000d0302d41c0529005100da26207459440d10040186030490348541d00709405851440000d49812a1078841780c0c1c4507180481e9802c40d80c54070059682c1e01400842c02000305940043d0496517401e9903c0803e41c0c44600066004600d1902220158000c0f03080342e103060400c0a005c00030712b00842c016052440e0a11300c40c20001c07000500c0c4074000d40191541c0c0d440144003040e10511404502c0c640307c940784032006600100c200084850a2611810031140e1008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 123162832 1250 123161582 123161593
    0x50a050702040902040e0106060903050f0c1c0302100c0807030b09060906060c101d07090501060219080c0106030302030a0311120a090c090905030d1a011d060c070906060207060908 79
    0x903020700018000da00e00072178029940740d40c510390800003031040303201a101556030486103d295041c00ca15001d40884055810f8004207492041039441a280700d8266007800c00c03114104109003000e03400d000d41c08002e9416681041820f02e003059000c0c044901ca40b8503601c007080310302050014010244001c8800607003140e107600c00700b403c0c0e240c41c8e400303001614025411100306039031700c00404c000d952081c1c18401090010708529455500240902d1000e0005200100040d6140a44c000e41d2183d00c411113440c1011051401c07000c0c8402c81040724402c40244d4000d101c080e5403850020755076804101004c000901d0701c0f150704c0544ca10740041351b440055a5212400310f481e0a114940100342101003100d1401d001034001440002a0007200c0e403460042c0040c4d82c580312038072038001c150b848440e030084180c0890044e4040d5a81c00c40c0160454090408013110300609900c0810610f201e8220180101e202d5010009603003003c40d0803101c241c036016401d448195035030361400d9910000502941d0001e4000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 123164082 1250 123162832 123162847
    0x908010c020d0e03030d1a090c0c03180d05012c07050d060c0203070f0303091502040e1303020c030304030c15051303030302030901061805160815010e0a0506130e07050a05 75
    0x4070000500d4030700c001c064901d001e0700101d041c41151f42054090b88810f945c450783e035a1610f000e01c1e49540c0b03c29042d50303491403ca40240280c0c2c0301d2140e0922445006002e040d10040d98980c914039058040e4418002c0140790401c03d03e098205400c100c0c06c00f5924a80f84d030700f1500801c0880c605003103503c042c1600030b035441c06585410103080c21107041000c5110078040840414059403d4121080c0a0744000490f0002410b117008130180410000d030085004100421000d40c0c0614050b5001650300c403c00c0402c11a80303412400c01d01c06003c1c14ad0b05120119020060111881f8210119085e0125a800507102c9a0341030781c4034001e00b940c07603004c0010200d0403c00300c1c0c000d400640d4403020381c1000041490310f85d541c13512002d205801c8184801e950350100820100d0300300031025130700d80c21b0405421074074100f400594003003440b85106041200c400c0c60304005845008402c00908070092585840b11480240c4a04000d950300c100b401071668000410b4007980140d007101d407070707400d01d50f03070140781104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 123165332 1250 123164082 123164087
    0x909070617060409061b020c01080402010903080c0c090702011a0a030b011208090a0303090501021510051c0803070302030412170a0c2102040521030301060c0f0b0f0402010908010c020d 81
    0x3402042c07190810b4a40100308000351061141481c03030080404035192412149800034070f0450341103e450b051203400c4043c4001350f80c0048040c41200c0e40f01c010140e0361507044840b9810710100300b0189402817403003400d200b1015019000001c0945c0060030821070b07550083c04125507041d6a00c001b40c07a81003454018822006003011805c0b103680501400ea2a259004000c82c000280035441a000104408000d201560341417000f0010065541c80c003421b02c1c1800c3c03007000140c11030348c0b190310b214a00c6d091003c240c598411913581c144940103482240c580c5007025000e8081c2d0700c100ca04a41514500845040482c0960b030076410400112604c400c0d165500060040285003401000302409003449128511040ca111705419407203141202684452030403041c090301d002050441c010001c0340315410302424800000b43c0341114813a1905109107074003428110039007802a04090003110711581080070b40c040940016005602c02e0381c42040103a95441403d00700c5e8a40c840420040c1c01c041e030298003a91 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 123166582 1250 123165332 123165377
    0x4020d08031003050d0e01031113090f0b0312180111060a090f02030d0f12090f020f28060206060105030c0901030507050c07090e3003041104020705010b09090706 71
    0x14a00380c0160801e0f242d071200c07480d06950105520008012141d00000d035603040c0620340e0320815440f401c50600c0301000b03046c1016600c9004a40e041a0740302c0305210034052903005040c034100c003c6d060b1604201001e424054a5208546804100038180d48601d00d6501c140300e907401050b2004090070300c41e00c0d548141c001802c2d402c401a502000c000034510050b070b8050000e8091300782d030b90b124010b9840c0000000740c42261403290601e212441d182c0d200000c903840103201548680d0486268440182c8000000c000e103052080a07010b9903205042d215000200090820642d601502120a81d030755100c0111040d201c02c48029200e90030900803e0244e502a0300229000141800e1090400722a06100ca00e0081107030300c62100c103a103c004030f81c1109014032418185014581c442044c1c0c0921461007043c1d1303c0b0f18003100110210020014091044082640a2590004100755514441c40c100b076806440003944043c82540c0c800045980c40304002000811100ae9886d60a02c41c0242007180300d42a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 123167832 1250 123166582 123166591
    0x608060903030f090c0405011e05240f0f04080d18060507150905030c0307031b0807030f02030c01020d0501090c03060f05012307050d02150910050402010315060f120504020d0803 78
    0x24400d08081d91360b956107e020b111f02070903491075461850216003042014204e035079400f080c05012600d440c1003c20103803056180541341c10b02001c0f03030784840120345182548a080c50651014002013000b0482c0d01010510503805040c660b80c50304203c88880584c0b090100d0f034421500810b4003040400c000802644200c00a0102210300040b110051b450b03041c1544c0c08170020341d10b0f540001031520700b0543c0142448950419069064400d08140d079101c01d00f0380f040781c82c05024404410300c02403405208000301e0350022074440082d91a500e05045110181100780144003425062503107900340c3d144244561022140c205075044511450a4015101d0030071254034402400307060005680b9802401c802050a5403050005102007024058004c1c00c0028401c0780b0007000d200d2005220703220a0006060031045140e410004080d1110320060b0024103030007446c1c040c2c00003008000540190040f0645010090a4560036008080005280100c078402c0358025805110401002c0114008501640c3e00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 123169082 1250 123167832 123167851
    0x10c02060702090c03160201060308070b100f0b0403150e0c15130b030f011505091e030609010b040513020d0b1f080d0e010903030206040b0a020f040f03060608060903030f 75
    0x1003032425000b007440000b040f100403039404c2c0c0c004207110300401c0c050205061044588020052036003190360b55191441041c1d80500a041a440070521010040c940040200740398002c10070880d569191560103900944804c0d14841c521004400c0601214000c1b01c0c1742c841060050300520100508010700c102d607070311403032218440c14810380c0402e803108083c41d4060315015400d01d0301e0f032800d00110003004105130400f0103049950560010450741040c251540101f0407982490602102c07062445161070103160b142d4140325607418481c0301c01042d03004c15901c20047c1c4052210f80d4400052503841c003014200203401071000850381c0086820800d03515041031160307100a0885010301401e0b800c0440981001d035403900007942c489440c540200c0754030b4002900f82061413290b813840e02c1c040e4444000410203410780d10304900084010405034111a443d070484400309448239243e5020601d8851540003c8404a06e0107070003040504000504500c40d10801c00214555964021412000403000c1d00c40c510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 123170332 1250 123169082 123169087
    0x1480210050a110a200102090616020102030708030a0507030b3f010603080a0801061b08090d0804080d170c0901050f0403020409080d150f090e0f011b11010515010c0206 74
    0x14480d1020f4024510021a5603940c0032911203918515049200b0700c01d403299036031040110005680705c1e50103071141e002c07608040c05041d5032540010707400c43c45510801410040d00208000e103c404079482180181d44640c0c0401c1100d080a0512407450740b1905080510452256440204a9144c03500d51620202d54100340c00310105540d240c0c00d40d80c032a0821905018041030803084a54005001d5005203018074008081c0380340d6004c00481d44892080244c11303a240042e0760120358407000070034003a0f1030340a0041d42c2c1d07440d40d42000588400b40c1c04400000070301030064a00c040010318082d1401280b258040f50704d0090300c60010b45480d8441c0f21040c0308020b0600002000d0307911032003111400d82c02441801c0c0d41e0400d0815070011200503402034044030007200000d126400c800c0c8a0401520b40c0200001942c50020a40c0c6261410203030350201590708080c414841c8080000b2030344984c4086440f000c204524540303943d401c0c2c0c0c8046036808800720140c1c08880203584980d603c0c9042500140c40e861 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 123171582 1250 123170332 123170351
    0x3100c09120605010315021c0903020c150a020705090c0a0f090b0708090103060914160909020c070303020c0109081b010507060203100302010e030307020307030b0901480210050a 78
    0xa4280c420040142d409590b0fa0004100740010f44803070f00c40d00c02e00ca89045180812540ea0074000365120b50894040d10354916503401014000c10040c0c0c540000100784500e8064080610020756002007041c5c4018060160002050306000640b5402421000f032440d081441504040350404550002481000340704c51000400f4504440141401070084d19003a41e0380b40c0280014098910307036840b10800500c0e040d0501c0b50352040c1c2e658690402403600f445c4000a050800c00c50f52010386420140030300e440000c130301c03184c400001800412a0f209c1e07000e468521801c000155003284a40c4550320b103071303003102c003c3e0070400c9000c1c580303d8007240050400d40c1c1400a5525100205e810844101800c0f0b101c011003032040d507801286c50042000304600a44c0352803c1e6034007198840b2801d200042c804140e50020405442c07080d0000c60f004030004090540401741d00328009603001c082c110750315001214468002140a02c02014103001110b6002400d032174a6031444040280301c0103102440c540d1362110001c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 123172832 1250 123171582 123171599
    0x20f0306121c02010204050316180b0f06120f0106050c0703120315060e0a170c061b0105090601090f091101050901020a0c060e031204060c02100e04050a0905010506010201050603100c09 81
    0x2c0c420003007260b000607201c5080c281454503200307903024205082007000004010200340c2041545007804014400320768030b100d1001203842c3d90404404e0750350194000c61307032414006006a55500c46d9030001810b0555990b84c140544141c4074070011811203400c0a581800407410b01c0780341c00821540d5140000380a1030440c03000d10481d1454029400060008541410030300d000d2072090090502c14071041da0626224424560b43d0710007032002401520046075080703080030098419100054400300902a43c40d14246046d2514002d0194011040c60070100c1208042c0e03030310450450f29030114040300488030000055940f5000081c0103070451244030a04400a80250a11001000b90f5215208001400310415007007000c03054109000030814042000302aa0000344080010740655000c807021001b190202c030705144543e60a9049030400e400e00c840c04c1490b40c40381c076019008000801440d02ca03003004900f40c41c01524280d92562004070003027219000343e03028583c20f0815042c01d804060f91882c50 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 123174082 1250 123172832 123172873
    0x12050a0606090f0b0405070801060f02031621140304030516170406030e010203041a040305040e01080307170a0801050105030c0c0703060203060a0807030c0605030c160c060f03020f030612 82
    0x107160291107904a1203140c1140c004c40c418080704075018807251505103401000e44d40144102d60070070000e001d0350301c003480c000d008550403509a01841c203414080d45c2440d14025054002c400980041c04108000c681d1003403801b0b644543c241a2210f14540703840c3c504892541100e001c080076180001600c10016000d200d08050074400401203030344451810780d0103011512003404070300050340108104000241c2c810001c24030601242c040b0440d43d1100d04007100c0381c0c02682c00101d020f030503003400480c0460000015041c800d105020305e41c400c0002040341e04d00e6000300c01c0d06d9004200c07804e006200c150700a002031940880d4070b43c401810b1007020702825103014825407040c3d03a800e078000700740901400d0108032440540914001410038030715644d5041c5400a00d445802c081210101c0410720901010080303c3c0402c03000f800e004007018090902c0e0b12034841030b1180402140e003c10150494500a000f0380b0154a800401142190b0742c480030b110302d0020b9000c1c02701c941c2c0038007060b0f001249107030f044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 123175332 1250 123174082 123174089
    0xf110d020a120e130c11032b0204080d03270c03061d031219050c090a0602060903040302040b0301090203010c08190204050916020a05031909050607080412050a0606 72
    0x4044120403800c0041e48401c142c00d022042040c201d620030420b0f100c00d03044401c00c0d00580400545c0c034000d58000c03200c01c140100c0890a6001c0001e00c01940d1546005845040e01e102a03801c04080b0100511000ca104c2c3e4483d58141d03400c03401c1e0390b04010b406907000c0d80c20001d644203155441c01c50071410410b046003841b8222a4104051001d10501c0303a01c1c411f5542091042136000301c6190080038140c3e0700c0c0604c6141458072040b441c006a10714922182844a032075441d41b0901c0b060401c3c0640420a801400354640521101a030000d2420304c000390b0350380510041000345184c01d0035070f020700028144c902095078040d9211000880162400d10401c003264600d0b0352113050600345203d0305c40c08900e4901d01c90302100c3c010300090255940d40440c0035007260000d010f50342c01c6001c0c2c400581c03d00003000c078043c00d14040480d695022001032241513520311031580d00c00d9002512181042003a010b00c04001d40080c20170311003807000c10020515054000e000d88110385107040c4a44d03803c000d0366510341 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 123176582 1250 123175332 123175337
    0x3200a0306090b04021201050d030e0d0803070225120204020f030a051f0303171e010605180a03050307080307020f060106030f1a0f09060607050303091c0203070f030f110d 75
    0x1804006101261040c1529101c3c22a015032030304180000c03a4030f0607081030090034858082100300e0130805002c1c101460803040081d10348050105d541c10503071a1908111822030160080c05015208141c0e0134005002c0d41c9078001c03090b0704480c10032040911402016604a802590800080b034041130310b440070354460900d4480204407482d04108080542140c4a4040700e064100341d0300b840040d401111031304002e480c007076150072141e03140e03106140c140345c15900c0d64060303144010001c64031540c45002001c0100b10301c0781040911103420140030368240603100281041d0400c2c45102c00180d4020029030b040111403040f5000c1010001095061031401c1c0e000d680440d680e2000800b0107481c07806400c502400540180a0b1a90440082102c4030108071246110b410f11100080c031503076401041c1c41344581c00c8002c59449103055012503994040d0504101c122804884158607a24400021135007007580c40550003c5142490354180c80c107444080a500501005100390505a0700030042ca0f000102140e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 123177832 1250 123176582 123176591
    0xb0303120a06080717070608060f1c060e070e040816050601080c040606030e030901200a0305090a0e0103150507031404030309031812020f040906090804170a0b010603200a03 76
    0x6152a10f8444160311098041c50906040098810085001d0301150118107298120389d4801c000103c5a0f222415072503801100d50381060148407004580b105861b1160100308012060940d0140ea180664840c1d050240a2070001500003480c9002a00d042d00000743e212410032040e03a80c036401c1c002c1c00d8206010513440001541024030b810b00840000700b1030340c2010000c0c1c104010107251039118070503299040c81156001070790521003103202d054422681d1006e81d02e47d0706540c82c00420542c04448035500c903c10307050010607282c1000e55200d0481c1c0d13010860f20341728070442c0b40315009040002c18803003d266841031216411040c0603082ca109034883e0340e0014014210b0b14015140601840c03006850010181c02030180e41c404c5112050700c2c40d0100e550710f5050310400001406007001d0345004040508022010b410080204082d0095852041404482e202d44400713050340c4120841c03018003c2410311004214441c000e40c00440052907951107071501024100b2414400e40c0105240030010303598 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 123179082 1250 123177832 123177839
    0x2109050d02010f050f010506030403091815051507151514030f06040209280c02150702190206072603010603150b0316020a060c0302040303080c070f060b0303120a06 72
    0x2886490128051243c1c200b000d0304000e10a01442c0c0b805001c2c8901800000000c5418580140e0114000345980c500c45064059880c4242e4080e2846007510f9204a80700240410780303141c4510348d40200ea013450340440c00c284a81c0c880980c1d008049510074460750340c44101180400c1d80c9008039001d402150004804040604d040c1407a00c0002140085980c200400b4840165601010036811220030660551384030f108218030b0301d41100a80c26202941d02d0007a00c0401d0315000b02d00c00f400c44818155000d8140e5075144140d8070b41b0400b541c1808008a000964001403074040c02600481c0d00030080c030140d8101324041e0f0b01c01003d6072032a41d91520f50200c0100095685401101000c0149041002c911454401c1d034608a000140820580e889150020a4803034801c1001c5c0d4680341e04210140f180340c0030b00c1c0e4007030025801030000798005004003002070752240062045031059503001075542d50410180d1140002041c000c421194180820001c101c440b03080d0040d03280c0605100071000070481e1a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 123180332 1250 123179082 123179087
    0xe120c0d0f170913051003030e01020c040608070801051e06010302130513090213020403081b0c0d0305130603020702100807032c06160c030c110402030a1401060e060a2109050d 77
    0x4602404901c0904103020006d5030030403450f201d07044aa25040c608800e0828500507800c00d21100719032500245041c400250100001a00004655560300200450380300c0a4281c801801c1d407889152688444c400414481d501c40e5009044120910101404250303c8800082003402036000a980b06074680000a042d845d1000d40400340044250701180f42601e16901e0304901d0041010090030717801445110f4141010921603550071000081c1000c11142c9585000340061308200005e004806042e200442d5160081c1700702e030b140c0743d0024a10041680070707510496208074020100d604040c0c0380c24003220b00e1101800c603907a00104140000c0408074a140f0190f24214004111104400408240040c85031304051881d030002c0e05441d09003c0d02040d0300b41610f040c40c02d144000d40040c400002c1181c500041d0b4072206030180c81040c2058140d0b42c2d01002c545a84005944561104041050b1a03a0340d000b15562584082101101e024111142000c00f04540038002c0a88040c0c2003800c09100ba641e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 123181582 1250 123180332 123180349
    0xf030106021f02090307030f020301060b070503071b0513020307030e060703020702040b060f040b030a090f0c170606011d1c3c02010e040b090103060c0e120c0d0f1709 73
    0xa1082c0031410070302440000b03603490704140300140081140c4030151042d5142904084003500e07a21041c2650303655240780465680e0b005030380030754205011030340d64000e1003416031402c002c90b18024040b40e0083c501400480c000e50018003030b82c043c1a907864520304003820a2084a00c5504d281e28010f848429600501003621015070300d01d445060100a0854010005415602500d005024254803581c0319601c0700001d100d0900040e0000701a41c0d40034042040e9105064161001200b42c14140010040015901d050035240180490b8142e941d080005400d00c8440505107001490840181e0f081000c40c41c0d404540101910641d45114044480140c0c0906901d8101c80480ea0038181d0140056030042034481140002d041144100c240301c1c7c641c1c0c0f141c0100c43c0b0f0b42d0740141804a956900d140074002070010038040d0005c15802a040a540d20701030b820030904c0b00c0c50340c01074075500c00d0b14010045440e034501c40803100706110040020226000e007a0305583d03002e00940030341c1c0e102e009804001009 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 123182832 1250 123181582 123181633
    0x1b08030603120309030d0e16030c09060e15060310030c030506070e0109061b02040b090a060302031b06031617010e090715051c02040b070b010e0a05060a12080f03010602 74
    0x165080060100d20b0800204403200c4001d4084c00007060000800c0d400e082507801d41104842500308ea101005010030035803814200c4200102c01c1000e0380c0c0ea450440c2c0d070380308215007808004980158150302402d01900070350b40306115500e885c42031910396030380b4030f000c0d00103800507250340e8050030800129642240b03116042039401d0070020352240c60402d00804550f00444086da018001c01c4004085480e02e1f00210140d8900030403034081803910181c030400074091440b0591082c811323900c003806a41010655030400c244094013461556881039031180d1000d40000700c80c0c04101482040b10b04c00c0d03002c00401c50203860401004005800c2564401d80780500c1d503000741420074401c98481110a030020b0488403012104001541081c1d0018201c1000f8003a50713101d10900d02c000903688003045611584207060b510050501d58094031210103800031201b0071a510764001584000910915181001060005205070166071526021444003ca103800030303841603015a10104140354075000c3c4000d004680d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 123184082 1250 123182832 123182863
    0x414010c030b0a0602060f0c0f09040f0f0f1802061305040e030d110406050a0e0f041a0114040b04050d291501020f060c09010207030501020c0c0a080d0203191b08030603 74
    0x1034201f180d44d58460402c041c3c02d02c00382030000948040c508650344141d44994500400c1005504a4100c03090064901800f08a00540c40c010181c034280445105600881c1144000102d1181c000d0342132000d190310040c2000c0b5620440f040c0040c09503590301a003c0310022400145440c0c10b4540324220130b40f803c008088405d6082032006120300c65116040c0c40d0340700034902d0309100c00300c00d2002203164152100099504103042c1000081403d541130b2240c00070407001c0c1d84507480303142c0b4421502c072103004500803c42603010402080201d0301c0d082c144620740a0280000e001c000040200c0390042003481d4042c5500c0300340540c2000b1036003405a481010522003800500200903070f18844030f444d41c0d0300504105003402c001c5100d00d020791081011a02031070b4403074000c40d0798140c0e162500344d5540411810600c680f6107454042000c0d08003080d0706400c1941a0001c6080c10004035400c601407882c00514800c21080700c099a2018500c80700d002c0005006100d610794905011090504004e15107150148 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 123185332 1250 123184082 123184093
    0xe10030219060206060621070305070e0312070303150b0c010b01120509060406230c0c060117030d0b0409020603042003010903140c0307081b21070201080414010c030b0a0602 76
    0x4060f0080784250703105000302d0b1003950f41c0d0710300284e039400d5803140c0c003280e20003039002c10410071425050350005025003016103951003220743d007000b00355a0303081e2000180340d03a06040c00f0610009009400c1a070406191340020500d603034075210740240d6600000300d0410507a4542460b1841560031540074003840904900600c00c600d0050502a510700c005000101000d40d1030180581010b240c12071105d824400111600c050b08005a8034001d51300008032107a42c900070a0000073300e2018032030070310400501c0540034508080a0302c0842c8024482c01075100d030010380311443c2500582c0c0d01c20003144558030031040340d2003560f1216481e06c104440111160300aa152041d180c002ca0341100c001c601c0046c405801310f40c0d9604003c685070a6000d02c81000340246000702d101810806007040c9400c120811208565540314211071940e945135119911920352030003001080003551040c0c00c080e90003402050b10340c00713820440f400f203421107100c560401c0020340c0d903120765031702d515091300040c0040a8901c001d12 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 123186582 1250 123185332 123185339
    0x9050108060120010e030c06090606060306010804060e010b0a150212090d0b090c06210603150a090314040f06030e0307020604060c060b180103050d031406010f05040e10030219 77
    0x92980f4182c0346902d42c4004200d2071088241002d40010018650303120a81c0c1d113070078040e5485d40d80c942040e203081d800750003500f002814a040240c256481244141e40303c8206880d1341e200d601c01000d0410100c80c07155258107845d51283c03290000d034001080d99400e860392000c0c020800a00b440044a00e056500d00100034400c101c1d07035a00d450005680c6c100f240d100c2c80b44c40b101140c0c0d2401c240d64280c0c513084a004245403800014003108040004007000c110300b484e66a100070103455130a02c0810740c440150802c0031900510b40f66201035011417081c10b10140036424400510840d03007044d4404449150740c08414031005038580076080038219030700011401d040c2164002407031030065000f01410000d0204004040c46860b810245da84100606840c074105903114090f00d030000240030580d142e1042144003042a4442d00c03071681aa0079505509041d0f48561004542d640101001030003084824080414032461444400b4017032001c402c0b550350454a184140596125404071044481c0c42020080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 123187832 1250 123186582 123186587
    0x803010e0a0b01090f0b2b0902180403020a230f010506030f0a0c0506130b07060906050c070f080c0703140618030a020309010819020a020a060506100c080c0106080a12090501080601 79
    0x16030030380c0c196401d107c1d00c1b050030b103070040341c9444c01c4900c1c204c0068000384852000302050b40321100b00390007941d55001a0004820b00d810b424000d48000b0016407200e0781076008101c1c2e46140c0d4240c6400302101c95155103055540b245841d10406907909142d40d140144a081d10b400c01a60584180c0756002d09150344c0c0507200c2c406030b03410501c60319010780e500041407042207050341000f801a0006402503501c1c2c00c03150401d08014048030404603255850701d004145400600310030784000944c84403039a00010ba040d42e94940302d402c540d25110480c49080c401000041c3c030b42192440c400c1e18000106180d1400c420b14001008a000c0b02150941040000503079560707011040300d4450300c003800c1c200308070380301c0c0b521004020143c6551401014408910840c01540c0495440b400d2801110140080e444002c03c000140f01003180e03910124501c4c00100c1c00240800d006072000c40000f0000040d40c81e0b83d00141400c2c80b8a4034000c0b80e40c00b250100c03e01c00a500310012402424003803030300c1c0c080362a081001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 123189082 1250 123187832 123187859
    0x10501170c030c040506040b0702090a050412031a0303040603090510050403051608090409030201020909060402130608040c0305121207020102040b030408090a03020303040609211e050a0803010e0a0b0109 89
    0x1011070504001001454a90106040314000c010141203d640d0f00e55540d00d070440303a04075030002c9201d00d04400220728000014001d840c001d80c0c00814810080304404000e030003c1c00001030315820001e8028102003d0ba030b0600280005200544000c6840f80c410f1800b0703801c000c000111005114a41418070000c42e0f4480c003521360510308081e2502c6080118101411640600c3ca0714943c41820714800300c0400d40e064018050720001038500343c0384c40d211041000168010260350140b0b048021780200001480707811107580141c0102c2c481452191aa2245814520300080d03200c441800010a0030542c503141c1604d46d40301110388000c5040a05040140d2402d100142000c9d10103d00820940e01a0359003d030840010742d8010700300c90b82c980d83c484014003c02a0ba20178204c0401801410301005c00102c00c1c140b42c610742c08041294508426105004803440704441540c10b0b00c80d03842098000f954900046012f80f200b203880698a14002c604030051b195480405410004164400c000315648000c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 123190332 1250 123189082 123189091
    0x3060903130510050d02040603020a02100606051602060405040c03021c0e060c09040e01050106030e01061208040b1c020304060b09090f07030b0c0c01020d090611040e061903020306180601050117 85
    0x2403403d0318003a50340044a0b503004500d00442078500c0020000f03a4242c16030700800640d602a020303155644030b501122412280c141c400c210110b54100403a50509800041c030110341d074802040b03541032035100c1000c01c0417aa1405072610204e03500160a24032031013620030680340b82900c1c44040c468010340c0980c0c5500c0d11400b60642d114500c0120764606983e0b5103410154103040598000c100030b40e56a20004d001e41040205200c07154079109000c00c04441e21040900115000380016152501d0400400300e282d20260790b048035400da00000e1414403005000850103140245000304070442e1400400c1070340c04c8081d0044d040c507403080051114441c8003145140450350052041c015030750318840e2030302062084001280183d4030014024401a5590b030001003800d0040c0000c0100d244d01c02900070080c0300b6405160904203801c40003030030b140f400c21004180400780e4140321446907902e50110340b03040340c141c80707080500b09480b0721002b01e14000c0044900501d0700b41b034501039084108074003246ea82009003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 123191582 1250 123190332 123190339
    0x10060305060d0203060a0507110a081b120408060106080c070302060f04060b190305070902030f0406200708030609100b0702010e210609120406050d0b030106051509030609031305 78
    0xc0000d186984801c0d9528807182c0140594202e49002c020b07010082100300e5003400420240e246161b6640000a0004003240d84a10300b04d01d40104541034482c0c600304c510390160f4a200b84403c0200c1000154050401032011390000d0402d541480c0d0040c0140400600f08148001c00344440404a41d00042ca5900b150680861400c0e603291418100c010708480001e094002403840c1c070300b0002030000341540003100e0096080e5000107071109044030076880180c80d0f142c3e403a602440480c01007001580300d5248010400348071141d000d48100d50707000c140c1019605480e0035030007108111050800b40d20055101000c83c01030720040381407005d0f038521805840390103410440e0640f510407040d25806004c081000d02c0100d2003070600e00c0780d00c005545500403500c02c260b600644d4001c06081e11000142c5042d940661505410b2600c1317283d1130b6000341803502c03074941d1564031a84001840d440e6a07103e81208036450b100c6a41c0c60703540c001414170703144000d0082134841d40f041040c4801034246280c0c3c401641c01c00c9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 123192832 1250 123191582 123191591
    0x715021b041503170403031202032a0c011104050112090201050301061b0b0a021c05040209010501030c03020d0516020114040b0a0c02101a01110303100e061c0506041a100603 76
    0x2c0c0326500740701c03502d8000038807900d44070f5504801c50f400703100904200d922940e40c0c0f26000f030705080340c58142d0009550152982890400400b00140e040350056004e05100c1d40385424841e07004a880e0079103844d1215a100e0520018080c000c80d40e01020140c8490480340c41440321400c3c075400206207200502c47c6104010007048103440e029042c904c068921070b0404100380180c04d000c20103000275800700d000c80e1640f40000724440c85403440d50168034400c5070000e00e81c0c541a841c000c01500509568100d4100701507080110142c2c110403841803d004d422262543c2030f45d420b030190041d0844420072000381c01d024400041000050080c919585d02aa419001082c0e080c6c1030740c402d901d0048142000c1c2c40040c01c003c0300084088000010088045090b60303034840009000304281c0c0c030380c4000d440c68441040403e01c1071000103c12140550000c4026010380c0e0710150810500c500030071030301411600b6420860030b00090100b007000d54141104407009007191814138200b0305d00c0c0814035106600606844 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 123194082 1250 123192832 123192851
    0xd030902270a0e150a0609051b0301031101051902060402130e030d0207020a080a140d0306180504030212070b0f0c0c0312060a0302040906052e1a040906080715021b04 73
    0x140002800b000321500c44004c0c9051030750320040503100e2400340400191800c00040c1411028030905100c0310380344c0c00305601d10390a68444141003080200c841d418441c08020420440b42c1c1241040c03032084882c0e0151410307042510400144620760341031004441d0078010384544510005c4102c2360f0410441c40012f03582c00c000c4c800300e4801c0d0340c641d21a0055024001d626802c0c4078207076141e034007041c01040c00d8401411401400342e003151964000d5040b0700f07058003a0f00550840d03552040d074100c0d010303004940e55004240d14001190b40103010840c2c0000280d800d10080a01010710307140c000340325005642c1444922040e00f40d0b6809070030300b01c03c51100b5400100d0013a88400d02850041e41e005030091040c1d2130641012406044103079002c002c0c0844068244081108400c1c4041907220482c4042031182c1c03800c0c0c80f044d03003003486800051189508002c005682c2203944038442c000d040110103041c00380d00d446260114044171440c032170290341000850340b56500120030a1243c80208850001d0321450 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 123195332 1250 123194082 123194111
    0x8070605030a11270603160c0f06050a0f06080c300337081611030a0c14031201180f06030c090606050c10020304030507050d030902270a 60
    0x11464103141c602c1c5000a204d009070030400c1c041c402194104504204450f104c0061080078881168415000a140b4040d11040340c07080207e910703441d01403282c9c40105852600c3d160700300e404c1070307a043d010340340d6400c18050000c600d40101c2004203000c0c805800f800c4015004a0001010034210600403140d001d190503004004803444c0161013480c008581d19048022464401080b40c401311807010b41501aa200000c65030305665584003525680c7e400d20b94407515803003a04040f41046504c14444071a03e1084c41c6401007001d050f400205590b6083d01c0c8400c2d081a5503400c031130040007850b07508200801c01e4070942e5113900328119084401c02e0380380d8141c1801c10a00814406401046060078500000103010005480c4025900e80075810041559628001e5550f4860701c05034403004c1c1c004503d00c1e000a10b00e0b902540d440f6029080091501d41d40d580d4590a00d126046020003080e614040e180543c1401514801d195010301804091481d60301703c8007001c03030b6000703051181c80c94854207003001c1c0750b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 123196582 1250 123195332 123195341
    0x1d0405010803090418170301180c09061b0206180f010804080a18050909010c030b040b030a15060518012408041103120c0304050f04061505030703021b0d020c0301050108070605030a 79
    0x3500142d032815190034070f03051746d01c075a482842801c140d41015810b018880140d4031401002c40190f031144e105040c40c01c04288e5081d1038001c04949000009000740c40941c8a070002005c0d44e5500d4120300c08440c1c0d00c107040201c0300d2070305c4850790b041060f00000c000014003841c2c101c40300d080c1542010b4850840c810321040c8244400e40089070401c001030f060004140d415046170701c0d403401c96201840300048580074402140c440200f108c0e4142e02149080012802c090726810402d2410380b00825003d80b0b0f031021405a084055100001c40e281d44010403464402031291103010341036a48540e02407001150061091502a1001d407000c20f50814806182d6000c00080c10100f401c40c00710ba48680140c0ca8098481e0058403400c1c1c0280c000401011103481c0c148903840c1030b0b40341e001c5503142070f000c1d100044030503400c020440c4051650030000101600c1d802d00e180d003003107180c40b4010321000040346002420320032803860b00e5000b030303043c4801401403550106421042e41c01c5458130584a6884020400150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 123197832 1250 123196582 123196631
    0x709031b1502010b03060a0506010f05131a0d05011e171005340f05130906032f060a050702031006060f090e090d0e0d02030d1d04050108030904 63
    0x49021007021490301904000c8802c03000700c09603a5030341e48448540b8259501200c900c0e00041840b1825020280240090501082040c550041054654013041049803a10070100c40c1100003003030015030a4641c2c05043d01402c02c04008040301280111800b2a1581d2400b9a0b001e5500c0000e0b14154030301c040001400c1d5002c0f4182c1032140303040480c08050078180d034444030b14072801242c015048501011501c420031b0410365840d08110201c2c00c1c01100d441e00304451146130303805046d90018001c00c1070300455010314042d00250082c0038004004964110102e40051014844880101500da80b020f082e64160349080c200150349403100d1000a0400e42c81da2014204503207490404222581d2194003030022805d0340d25001d03002c0b503c908080c150040201c44c805200e5108840b12451303a40705551040640d4000743c10820844103a500182c01d00201504030304c00542101c0c40b20600400c540c07040c0340c101406803001c00c50fa504140c225901ca00c10284264055034440da2414014034074584c000900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 123199082 1250 123197832 123197849
    0x207050309100504180b0d031803050f1b0405040201170618040b0703061a04140a080a0312051305060606090d02030d030504060b0a36060605130803030709031b 70
    0x80c496685010f0a5604240240c130545046403201c070113810a58400d1041643c0c0080031201400443c0c0da080b074a5403908545070700c0b40c1003a4000000010401c2044900e455012005007000c038151708100102401a051640c4c0318500300024070000d40d810844000c15903e004520100940c0ca410110300d80d20020310072149403040d08800c11003409800d42c02280940c1e001d5805001d0f43c3d80d641150341c00c80413820564806903c6c100b104100c0300c014580688103918010301700030200d9940da40400e0070600d004a05030086800e039a2100f50b003c0c0c581c4580c0c0d9010b00e0240748884808080d4984994a40d40284210301507440000d0b061110b50f500c80605981ca64014116032002022810060250909440423207416050403254070103071401050000c141e07180c00d922a07906c01d00004040c044800c0e00d90340240402d400750340284c00307142c140c000c40700600300c3c03a2105030751845190b4495400003084e074031052030394201307005201a051340900e891045940010001c050100040482c0000a459078401030301e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 123200332 1250 123199082 123199099
    0x1203091c17180f0a030e04060608060a0b0918240909030a050c0703080c0a0302010b041b05030615041d010806010b0a0521010f090e01050403050405011107080a0302060115021f0207050309 82
    0x209540106001b002ca28281e400340280c42e9141c000341d509510070785103140d00c481e2991060201020b204013900b07092a00404104480d50590086a034450302030f101d601c8440f901c50540c40d44015054a211010801600c20030301d10700d00010546e84901030504100104075001580305210402040042b02560f0440c0c1215501c030045101316648111001302100594286040c18403e40780c0b610548030340d8040d4256a03024841f0310001214944c0c001401194020f440502038015907418030060300140082401c004011450300c0950300444030141e109103c1540b045d001444200c0f40c003000c0d81c001c203106040c40b0ba02c89081d4258040340a80819014580114203070001440d240030865010442c0c1c00380008114074026641c1d250b00381d950031507019020400410003008a075100e50048055000700b0300c251402c05480701141400d040003450103400503404000103110f11030742881c04500c01c006500003025524008982121603048040803598115401b05080f400d006061007110304e0420010305694 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 123201438 1106 123200332 123200353
    0x4030528020103020a210e01110702100c21020c040b030c090f0a06080a050102040501020c010207150503040f0b070309060605040b0105030f091203091c17180f 70
    0x20406c042407901740b0070303070f40b80c500c09a000240032940400c885084444071403d40341030542100c5400d40c100080e8005903110703218280207a2042c1484030a00c2410308100001c6464441c110600782000703408a89443d0307010401d40141201120704000201d0300710309066035495002d1105400c04030002c08512250003415525512031854000415a1515103814600345185030b14100c0702a0740208050019680600c07200c0641c440a1004207456032904c102a96440c650000d04428040c0002c04181400b0b08041c840c0d00e03154020707a0042c120b0501480c000c0040c140d0250644a2518107a80404d041c50725016411003004140d4480e4116120143c8081c02d08202a0443c00684124004c003005180a00040d6100f240800e01500d440140d5460100300c690907520284e0400044400240c00d42c0c042071030040d0045541c04280c00a5144001003d180c507585088041091091482c1c88 = true := by decide +kernel

theorem cover : BRFrame.Cov 123021582 123201438 := by
  have h0 := BRFrame.cov_init 123021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 123021582 ≤ n) (h2 : n < 123201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
