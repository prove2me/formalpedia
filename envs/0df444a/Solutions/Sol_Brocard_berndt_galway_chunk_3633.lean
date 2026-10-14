-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3633
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:13:51.86546+00:00
-- url     : https://prove2.me/submissions/2d8f1cae-1c32-4d88-a315-9d79da8b7521

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 653237410 ≤ n < 653417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 653238660 1250 653237410 653237419
    0x4090c0803070f1223030406091211070f050d1412040303050c1509060112030e0607060c14040f05041d0109120e0a030215031305010f021206040203092a 67
    0x51803401e03c11009441c5540364040e806002a00d061003030181d42840d030134440e103007410400300040d13010805100060759105020300004034546612756200a00d28281c0b10340c00000c02c80103241240c0480e8104001005044540b1090a120b8100380006080c841402c02c020490990302c0c040110a0006110780d1003411408039040780c075981ca0b450058490f82140a0400e42e520640031803003c0790740c11744801ea004001d100003800040c5d08100c00102d03524004032040c0c0078402141101400c54868070020000c5900484000400c2d1000c614020041000010058050301040c041400215031001c03400045500488000400403084030308903021030b080d03000f82016540303044030610a01c0b54184586441c103c540e5564603000200608002e00841c0500003c0e42162160041b505510307552030086820280c41c030074060030300c103071903866509442044035000d1305d8a4001c59400e2001c0d070011522500044222019400c62604c060b09074bc0d00d500c490340c10491110400c1560701102d050255813051210040c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 653239910 1250 653238660 653238667
    0x36080304080102040515070b0f06040207020306010b09040623042a11101406060304020102070810090b0a020304120806060f070501050103020f0402070b0f0709151d0a05030c04090c0803 81
    0x101094000c4d04148a0140107100c0c42c0c1000c8030940c01e110440310700d942c0c008207082c0d003500d400304054600200181601d8203c0da081201d000560f070108281ea0090101c41891350791a412032051006903141540301c030019a82140080310940b6102142c100141020b0b50002110002500c80842a080d0440c07420322020420003088151a0302500218002112608465648000d5011101101c1213202103080034140100030904916025004540090051040f580e206031982103950500004900c0c071008541c1e604030030070401c04840942644040d21100850440c60701c1d8540048142c00d80d541001040b00300386c0002d4642c2d4510040e2000c20a010030440d40722456458503a008001c01c0c00b051348211280310003040545414001c4070403580c0d00a40c002d90319214401500d0384054042c0c061002d1040786a0045110740d181c500c070498a000ea030791154070aa2a0951808071100040300340da004134040c08040c0003a860008000340c0019080d600094182101d0801c542c0d01ca00d560428041d501000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 653241160 1250 653239910 653239919
    0x4090e0a021002190f1403040b03040302060604060302010905010f230a0206010b04030f0b040c0b0f040e060a0f061d060a020109051b1c020f18070e0136080304 70
    0x8000980d907109466026031190314030802d80c0c0d5010781400c0d000d00104075501c0c0c00001644141220b802600c00d01a00b00105003590481d81075400c2170300240001e410200400c81030690400080c1d4000c81c00b96070400849040d5000200304800b50300a45043c01011300080c10075521888000b04501130540d4080e0503040c42c4071125aa03a880f0703100040052003805e00200e40c20014100b198200c0ba484024030168021703a6864040c9000010002c5e42d80444074000055419207030741c002c1c04440308002c54580d071039082022400c210385001d40076038043c0c001200248400e06809030320740d05982d0942890702d0038004400341440d5807140d606d0082e81182012648681003501504050405403083c0c0c150360700c4600b03c400c00002040d0041c0755036403000d80008010b80d40381444121190282c000350502a0401c0c40e180400c60090444030005c0003280304604200c0201d40c0b1040c0d41485201c246841240f1052a15030036000f80c0101f0100c1003001004203500d00024180940f410082513928146c82d11141e49 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 653242410 1250 653241160 653241163
    0xb0f0f0306032a0a06031104090b030f192f040f150806090708030a0212090114070f060501060c03090311010504082e0e030a0311130311040b0405060d030f0504090e 72
    0xd11042130151981e0000070640034000c0c0105040780c910b03103000ca41010319001d5101d02404e040000d4580501075040f4a8480c400e003401901c8034080c403010503c5100d5410710340700541c0160324000e001c0381c0444010218507444002402c45600e6021200480c0c0200c003296401c0c002c0c10030619102d2101042c42d80000d4036840032400300d1042400c007007035803407081c2d4440000340c5a1180282c028010307040b04100390107000c002400380c054603a042c07521908082440002040951141400380c2e040103021481c101008040d000c1d26005d0035052408030000c80c55660050715143d800d0000400c0401c0a041031100382e449001a5401892948202c403288007a00c0400340301c00078202c8880f505020400000c0004040c1e500408821400d1a0011490611104012030003402100d1214003030320382c108180700d4500190201e80014500541c4640c020074254401c01c01150080160315019504260400041c0c2d41d900001d0240140c05050038481120304420498540c482d03500040101440e03c1c54000600c5070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 653243660 1250 653242410 653242483
    0x10020d05040b0601090602030a05070c050d0303020c0705190509180111040306060503070b121b0d0c080a0608070e04030e0a090606110708030a11010605280b0f0f030603 74
    0x401c031a1442c2d44510004503038442c428041d281c0941d000701309944203244128002d01159004010b1004d026031950009408104055400e40000c5c2d0045000641503400f40681c8000385070031100010300e5101662100c00410861003451b1294050200040b841c400c6e510018004821b084000c0040c0e102d408c2141d4601d80080c08103640d10303484e00d800800c06e4100000d01000792a619030215050903121100c40214400080c1485c006000001d598001841802c0246c04154185000030a13828110680144902e9006211072072150515204021242000c40c4080984a0801000340b141c0d07074070304041d9410921b54003015040056410b0002c0d4004c0380c1da0110301542c0c0c00d5500d0b009080f50718040035941d20318038010514560000c0007880b41c1d8074080d002d10881c245080d00007040d800ea5800010f540354034034101c1050102d503285429807002444d40100b02c050984624824240005088126040c4c012000a0a1440400270110300702da5401c0010884080380e4140c1c2e0520349410409a070100d01c2e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 653244910 1250 653243660 653243663
    0x309050a05032214030c0405060d1a0a0e0a0f020d1a0f07083610091524090c0507060c03090209151804030c0c060e0a05061c0e10020d0504 61
    0x6018900410b040b071541960750000304d03005000300035140d40001004000c04c00a443c45078002103402017040007a000c0704080d02518210160025180b5044e00184151440c010401c607098102d1414040041c0203032403500c010340c0d01a10f0220b01400c09207402a038285a08050711250346900041015000c8a0200c485c071684107582c40c48001e40700ca00800610b4002d002010502151803900807072009240054814090340e940111210207203a070341294110303004800c069841780b10079840091004841e0041d11340315000440c550110111617004201c406d03000d070140b61b0b542c0c1d44500790a00450711420644084c1508048208043c100044001d0f008001440049000342d400b400090110100710505454a06020b49070505411902c9107208800000030002c5040c0b08000351404082034842c510341000d804261242c4c40d25100d40c00811400d811654082d80c841e081c100000c009604101c0d40c904540d01502602107050f6030100b0099003019801a0a01d964a102089800c9045010740251340242e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 653246160 1250 653244910 653244967
    0x70b0c0703020f0a05130c140c010617061605030c0d0612050724110f060403110f1b01050d06051c031403070504030b040303061208030117060105100309050a0503 71
    0x2803540c8103202c00c07080c031480350325400000306c0c00300d842c0600c13150091441a07543e803804005100d184111464950011030000105030b55400042c06040d0810000400140030000105910b1401800c50012400c1f8900303540108040800400d41c8101341c81d0990340f0039110000b05016044c0c80300104402d01d07c0022007514288504040058030625030b04411480c041380e41d07410010106086020780d21501503c1640700c07a4840c8044020740710310103100c502c0c0202d00c6a03035090301c001c2504007028a40403046407083e58a4105071031441003030031030b000300c0000507000b82850307911158450b032020000e190b1588500d4108100030924008900783d5009121184d110b0b490b011b0b11941c0001e0034107200d000403035003000480c40c200000d00114245089d01a03100d4424034001c224542c0702d241020415070603002c1101c0c8841c1c0480180509032441c02c8164002080170b0007451503601d400001010290910100e0040c5130703441c3c861006224086c04007007031141d0040e04599403103001c02e01c40404400c1189111250 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 653247410 1250 653246160 653246179
    0x4031a090303041407121217070f050f040b04030b011701050c040e15120d110c0901050418060e010c030e030a2f01060f0503011b0512100909030f0305070e031905070b0c070302 77
    0x46230328401c06014087c1c50b42c490b10500010710040e00c0742e62200440003600302040c400066040c1043c401000518400c0d0039900455150150702044d80c3c81a00c004901a41410200b007114029101545c040f07030342d000001d1038a502d80102e50002814681c00300f079004003013064090386040001a032a24040000d60390007140c3d10303000b0071854981c1d011140e442d5228294100400040ca02034026018425802004800c0d00f01d4076581c40c02280e0a00c0300d59032150b5100c100840d040c54042c4034410402412502851038034807042801402c865100d4861070459000701d04180d07801b0a4007140c0c405000000008100c00d544a0040061000352403003198400e40c01d10030510741c0c00c002e003c008541c0030400e441302418840c480741b04040310031009140c10074801d016140010b4040543c01800785040c042c0c3c4031016011500b400090603100003d00e10340921500701c423100c070700761400600c030404038980006101a040e10391400c0340c2000c00a50254070b40d85008141c1a15076040881c1d48403c40c1d01c2104c580300c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 653248660 1250 653247410 653247437
    0x1305060a050d08041e0f0806060102060c07150e010b0621010909210e09011e0e07090e0919050601060216150e0409080d0204031a0903030414071212 65
    0x40e100d00740e55000f000418207000030006484d6107024803a05030f056078041d040041d201c00d8400c4035012103038864005c981c07040040c49410350701801200d0300006090301c468608416a15001079001d210609401d4030307613880c060b00c00080400e520065848200506030b503a140341c618071040c0315082040c5000040045400001020b40c5284035100e032656204131190a200d13550104101d81e520204045418400012020354031a500d01d030341103001c2c05544c5014545c0200304408503500c09071540220144500f0300302400f83d65070300404c0140484168403403c50190741c5030580309007013401c0800410140b4500c047d958003006030118a590680750305600300c0700c010002e50003088003402c0e58424075184103040e0f2a000c8003e0302c030380c82c69850307030b18083c0003c100c0004c41d980302c103819840742582141c40c0b41e001c601030040041d010003011b0704904280100e209070500300704080c0c803440302810051601e06040c90091003135609001900003030108000e458420310040c28800211082c0d0619100081d201055161 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 653249910 1250 653248660 653248669
    0x718020903011b0f18050405010b04090507090b190507120f080915060d02010215010f090605011e0c021507030f0314040c0312090801090501090209010501020a200f1305060a05 77
    0x40c2440700c5544c40202c100d02e814010b03542c4054000302d0038841071166038086080d848900a942c028403c1030085981d40380781c0000c8600301c0760090071000801c070150000f044850510803e49007000c1000c00c00030814004001e0580d81807040f6800104071001000a0f44135294004400d86103552040d10b9032101541c0c1d062881c5c0d101c89905020072004e6134040007180250600307100c2c054042d0701c1030044030720740a0302c155200d402d80b809078440a4044481c46050048241601414000300401c1c00c0c003c2c000100341600841d102400700402d0300b0800c0d05490309095582e40100e010340c03100140405030365241c85050007840141101d140700c000ca4242003d0900352000c151503588100e0304818913a40c01c500b195108800540c4608002041000d103071004141108288180701d08035204000014400d143d0788184448040164855810754208030b2122002c03581001e0001b0900d0541800d50488000b640009803421103641c801c180c001080e400302e000d0102c42580101c0c0070b1381d000c0303034a02e803000e55440410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 653251160 1250 653249910 653249951
    0x3060406030c090b032e0f020903030309010c11010213120309031b21020d030305060307081e0f06090d050705120708030a05060603060d080706180b07030b1e090603071802090301 78
    0x545100c2602d440700d4600745456800700c7c0c01c80342c0b9070300090300d401d01000029280d03400940f214001c42e5954205402e0351501300c01e1002007100340c1802903023054207020241180c508148103c0340050041e608403010103101c0c0e03078074002035540030f41010000d180d900910a50310140703006a1020110715006015141e1418400007407040d4001c0209250320001c2d035007100541406400f16815101c1c40501040700c2400f03100207000b01c400712100640410031054600e1a180d01036210442a030020001c2c06080311005c109414110f605041c0941c0e20741d0b442c40c1051514091490351001c42c40041864810040520015801800c1c00702090195032540e20400a40740310a40301240c2c480442e08003000010300c03000242c034106004400000d44480b2084820070075400451b400c5800b400000301f0000d5003030700341c0b00d900f002e0401540c1c0841181c00c3c07460081401945c0152051003601000c001880030fa404014181c05403035148400c41d40100310844002c040e401015900d880395081c04d00c14000d00100309801c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 653252410 1250 653251160 653251213
    0x8030c0c012a0c03060612050c18060d1406101706010806190e06090c1002060603030304151d011a03121b0a1b05040e0316030503060406030c090b03 65
    0x250794828085600d006404040b064040f01d01400150001022a00510980000304200340880f41614100d00d821402d041c1c0c0d001d03800380301d00440090041c1c007055552031540e00000a840c01107400c0141d04014261183e4004a03035454031502040001e07100344110701c17100715001c1142030481410f5a0305140d844d2142405512140e620040015076076894902481c0040c0d5684480010b1010f2480d13260303403c0080840d841a940da10080352442c050030003c401e000034507040c2c406044241800300000e40c0328400a040508101401c2c03000d00400311043d4400490030f000c20441442030405190494007030001010b501b0300c2010710b085c1d01240c60802140d40300710740c29030400840c503000b150100c0d0100700701140001100d074401c0c01052800181d02c22040783c0c454802c004101c0c4c032a4030b890104000e0700d5a4655050054005000c1940310034020b440c0b81540952506000f601ca50314800400e0041c000c0d0b51024065041000d800140d44100f507104641401054050f1180e85050303100c4018180d459546d03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 653253660 1250 653252410 653252447
    0xf0801050412030b010e0a0b0918070c0201050f0d0507120f0e03041511060a270b0a091b0b0705010c05090a060f02031e0a0207060206060a140f030708030c0c01 70
    0x3040b04942d4420f0340040240403050403e0200b007009a0f020070741503852038105541c6208001070102d51842c02c4c1e107807228039020000000809103400403004110700d01c4908028184035001c50300c2c14114902005031900c001c0781d0300c0d0800442c900f4800042c020014514852201c0d881e01031401c60680c4580100e01030310140d10300a51a140c90030715240300d400401c00100003040f190340d8184010a0040c000140159119400810a0508690740c0c0c01004a11040031000720b108440e62800980101d0b00c0c1540058131f4440068900032605015070096500c1c0060304071130302103800200d107000045d00034004280c0680d0007017104201c2d9040c00e40d110300c103807400300387d10081136102004401e21a41003050700006907c180c900701501da0845280103000c0706594150300c003021900c00002541081190000d056a01c02441c040c00c00c280820039034900d5000d802002802445003211644824440301038544018080301c1c040ea640308d000d07540382e07000b00700092040c0c0500c1c003210304030750b04c145501d51003400702c280d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 653254910 1250 653253660 653253683
    0xf0c0c010806031c140f0406020703030e0f01080403030e150702010920030303130507090213150815060a09080f16060503060307090b030a050703030f090f0f090c0203220f08010504 79
    0xf50140c032010580d0740d01740c4090000308255920403810001038030043c4090340050844c50309610b805407420100311641c2d409103c0c404820100b50703034444051a04240c160070b001900c000500340c0070341000040c0355900080518681440340c0581d05500285030507000d100b800710300310302070301c1001c51f000e2545001b01d40c580c0c001c3c800714050360a400e000d6507103944100120b0303545a544080500680e0002d5401d040780b18502c070410400456041e1031180c405030301c0d14003581140362425118614210b0070243d02d024001c007098041c1c15901450f03498004e000e4820455580454a21203aaa10500c43c5090702c800701d503a010000d901c03406041501c1c05040010f000c5d0507420b003494040c80c01405600043e0742e040c400c8005002c0032a50078003585001d18044e64030210103013240385010386283c0b40c2da80301c2031407e13049010030061040702942400945001d040085001942c0c084128514080e40c0305020700103000000c0391085d818104a20411900c017458406019603031882e8050886c0d01c100c45c0a0720007480076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 653256160 1250 653254910 653254963
    0x80309010e030a060606080a0509030a02061603020f03040c170303150405151c0620071b031b03060b060f1e0d0c120513080a0e0103020f0c0c01080603 66
    0x440304001c0d01100501203030308407096504c03044184c0f105603011001103064001840f40c050b0880c0206c7e0703801007108005600e4030391481e10003503a681000b88801061a44c2800140e40944290111040d00210052203503c9051a040845e03d0f180b0070b1168204c607054064440310f807043c000c130540c2d00c10303440d030b01401e01603e2185040c0300150000410000f4141e190f9520020140d403134044030403d40c6441e82240100752280c2c034121088500c4250151103038003042481d06a050719800c01c94515039800f81c06038860250101154050314565040180744001c003440d00e100c1107c41443c050200c0c0d0282409022850400091010600c10301445103004402000680ea40e40b42d40020101c2c886407100070a45000c510001710b4007101c0104038a03200207825070605c1c00c05614a4096590400d800d030300803101e03c0c0c0c4269900b2034103124140030401441030308407024019a020340c0c180c80c1004810088955120482d08219071110f2040b40c903603021984040206105080010b0b82c00100582c55075030311100c4d03848 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 653257410 1250 653256160 653256167
    0x5191407030f0f14060405010e09071a0d0e030a020105070507020a0506160209090708011b090e0a09150506091b0f0c0a081803070b03041703090f0115061808030901 72
    0x2e48045401140c2c645801c0101c1c20803900c24150b110b0080300c500612401c0034400c100c150380041c0c2c0195034801e030440c141704080c08007082c2c100807600d02901c3e0000002e20b51070030f403103e809580c80403d231a520705041c09a0382000440100004e0603681e00070001d079071b1034601c01d40e944e00484002940003407568606000d5800c000004285090280b0000d80c1c00740038641c0000e00d8080b0441d0344015a400000c410807808909001c1c2c4010b07201000c05410110071500402482c2d41040e1162142d040304141c0401d090007201c0d8000c40c126074000e401402420b006c0382410b000340200351040d502032604c840025112408d0301c03c4e20b08002c076a0544d85894801c60b0103905c82290005094a0200d01035800180d000900240040c0501c1c0c44801e80c12500d80004800c1504054080c0c0c010180c00800b0010400098686009282c041502c0c0302100e4980c3c03561601c652070035982d03c003400b400e0362a01c0000210118404290000c071b91a46c0d175904250714082044074104036051041e4103056100b402414002c0d0300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 653258660 1250 653257410 653257421
    0x71a030903091c0f060e0c03030301120201050a090e07050403030818100509031210030c05010212040312050c1501050f01090621140106030b010315120f051e010519140703 75
    0x415000984101500f40c079071307449010914004490460341e4428440780303107409000b0018100801c42c00307141190b16101140070f80440c1c52800a040280000d11002800c1c0180143d1014018548960b00070749400d88002d0a2544103000903804201500001030307103501680d92004618074560040c01e01c1581034801c2102515020b000c0a080340424003410f11000030141400e40306140218402d0000e42c9142015148600c1e9500304030304642088130a80054202d80040301e040300d610100c40610f06400e03103c00c8415000350003400040e40074642410100d060341d129410305a840464848000d582010015651840244990008145500301c8121342000700e40719a28401068100425568185c190015004030260031180c0404d40c3d07581c6d49111964503104072021185040c00d00341070941028001443c20044003070080001e90901c0c008410464103101d10289014011001441440d0801560f40a4601220740300056900782c800d642d6050030034000c400b900500e0a5100613107407203070301c0700b00d01034503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 653259910 1250 653258660 653258689
    0x51003151503061811390309031507140904020403020a030f0c0b071109040609140f0f071a0f040803070c170d022a1002071a03090309 59
    0x640c0250002500194094001c800a103a0b07a030001da014201007410030604880600e01120500d00100c0c8200031401900300c070b1540c0b1040101d070743d019150000003501c25228110808000e50100500c101211000002e880c10b08400ca09981c16808421480c07000018108c885100260490100c5d04c6d00e0100100186130040c0c010b80050718003034403a0003194550142d94022600000705012031002c1c85001205013029041c03010141d4685040e58130b03168948200c2006041c850a86440401d040190540c0044561548580012032075000c80d484aa22100d1440700807501d8094690011210700006c641c800c20303620903d0328042c59035141c0081e00f070341c1c1c0c201c1404085004803c00c40070078044020006005124420030048d0007950030080c1c1c0d225423884088442101d503200b091420324036500030801326046030b4600742521304205081188151040f0002c0c0c0b0980150347c000c0082080c03580412035000b075034101444e1600c03406c40b0708001c450511040318820400e400c1485030700000c0c54034449400c00b04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 653261160 1250 653259910 653259941
    0x60e031b0f0f010c0804080d02100b01090306050603031b03030712020705030d05040c0314011a0f0907080604090b010803280e15040b0c070513060f050904020409080c030919051003 79
    0x22013a40c0e4a284482e401a0404001c40e4001941e042d401035040002c1b6401c0c40100700c06100360710200c000030301440500d01004200030303191400105640c60400a486622134018508620014003490311500c0b41d100340c031050005043c04c0c0203010300032424000c60f24034607030000c0103500e40310f0b4603204803000b030602800444100303510070340020124030500590103401d8060400050203504150f030700b41e403054400e20643e010365864031080e0025075a48001a910030a941004a80c035540c80e0001402485903203001002103682c0400410307a801c0c004054001c440640c1840d0358a4407201c8aa40c90711701c522a440300004081071020f22842c24210b18506074202100d0301242019100c9410303803256000701204600307076402a41c01b001315142c12504607000d4080600100321440c1014105d81074031105002d02030041d01060007150442d100d81e4890f2155035008030942c4d480704220080c042c3c40e81d024400ea20702c10007100d107803802402409001c40c0201c400c000d20720488038008400c103502410300c048104081 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 653262410 1250 653261160 653261177
    0x12040b16120302030a06060e090a0b01050409020703110d0e03070b09061b160e091005060303090303040e04140105070504170a1b0504050c0903030703051c06060e031b0f0f01 76
    0x7400c49958012400c0c4035100540c403440d04a40d041c0c11159103600c12010460070040e452241c2c1c8407a0751285d00004041750120b400910703140140d400b4442c90f480505e12070b00c001942018103600003001900b140904040d50240c4200c1c44040f0f502c1c6003544036469058005000400c51464a08020b106180010308001e0500c40c0c1e028070105548510344603c015600b0010103001c68101d580d08801c0900300c020b10342491400c0604000d0768410f0200800e000e4541d80b07401003101c1c6c0d50100107480c0c03040302c01001c07203540700d4441c07058001c0010240c508449203031007440c0c0071904c101c2c107000b0344d1320450031541c95500302494103280c4a030052461001003400d00510302608040b480940b502070440200701c20618001c0e140c401070004a640c0149044180d080c2800800c5c1541d9011013102c00707144c1c00d494110f46451030043c48040d02c20310f42c1881e1591038038003100091403581140c0d8280c2c45410072426185081c1030568403c0b02096151341c55680000d00e0480c2c1051480d02c0c04604014140601d4100003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 653263660 1250 653262410 653262413
    0xf0d03230105061b0109061107052a04090809060a0201140a090308071d0d08032202030c09100e070e1e030606060c010b06121005120c093102010f0212040b16 69
    0x3c80754810701c84680082e00054400038848100100c09a9950b1941d1403c0f0130000e8600c031150354810b48500c0c40c0f1331600c8a1610040c00b0b00c0d803003905e14000c80205419030310200e02c2400390081a044003500390a40c00d000001d81e8a551030301c5404480c6401d925550300c99601c1d814100da00f12100354060809510724050800d403620342141099056100305030055480c10f280301030918031010151500650804030f201800180c80c0404c8101c450881956078001c607485030301101888450913080513994182d0030b410481c01c10307400303505049982c1e4107580041c0e01140c080d000b03404903074810f401c00e81c05038001804207400e400c0850013401d004e142d000c00001d09410290000d41c49034850950580300d00c8207641441044190136811074028070045a1810a40803410744040e2101c411100061084100344e00184180c2400000c00301c10440d86000124804c1c8980b0310b254103040040c00030381c0005c21406006880900005200790051030014140e03040074035000c01c0ca101039018009600684069036030850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 653264910 1250 653263660 653263673
    0xc060c0309150504080f07030605060a140f0609030a03020606090f15010c031202070302032802071403070905012715051c060213090e070b0a050c0f0d03230105061b0109 74
    0x4c1d21b40b003100014101079455400c00e0f6081e6107001d09014440c1c003d00c4402c0000c000400107000e0b0110083e03030000c1681c0701d21000140b160003008003294041c021542e0f40b60800d540842c1d418443c40d022200d010507502c843c04545001c03803044540d65420700140c9600b01066000d00341c0220104c1c402e103807801070901ca5100300c106a8210380c000700c2c0540e0000c175820b500d894250044203600301201041e04154801100003e540f0f80c1144541c48242d41305111084a0761002c2c803961000e0030003c0010710055a40c0d1030948450700301c1a601c14452081e404d403e03021002507000e19a41c200a10700181c034058203020400c031500f20750801d01903049200c40070b90000617000b0b00113040e0f1244003034a034480c0a07140200101c02d460014046000540081d0300500c03100308441c050350107810407441d0040e201d0543c00540d9180981c211003801003403041c0346010202603810381001003100381845a04091074800c6d40c1c8000003e200707000c2c80b580030300b06002040c0d409803d0214510b242c0c00250000c61640d100ea120403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 653266160 1250 653264910 653264923
    0x1302041517070e0606070b06060d060504021308060703051005010f02032109070911070b090a020411090102100e030301120c2112170a020d020c0111070c060c030915050408 75
    0x8042d03008401d003040b41500025820f03500220a6500a107410025a104280c0780f1000b801c0a21449000c25115142036082e80700c2d034007030000508115034031030708102c00e2803500141c0d00c40c0c0d440f10320841000070341e803620038028103000c4c0020010000c5010b00380801504e0a0340300050900c2144400c0c4107888400c8107280b034400199000700318090340da0a000c25420b0414a05802006e801414941207421009416089030705807a0007011000741d40d02c6007000d21b0300300106000044d40c414101400c1c0c0d84a020840700902c0e000030700f6021900318031710b07001d4400165004071210030800d400920042101c02c100c140d008501c2881032560002c01500c50000780b400c02c41025a10034a5079204400b40200050940b50003034120a90610502180c9084074038000410001e04001000b42c0100e1004d134a1005601074428144c4c24000034840d0300c60605005501c3e4001c5031045e5621000c0c14000900680140c010a03a05034140d500c1400290030840388510551142c09072034100f101c10400058110810b00c00c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 653267410 1250 653266160 653266199
    0x41b031e050f010321170403030f090c05040b0a0f0e06060403050a032708030a110c1005070b0705091509150408030c01060816060c0512070f030f0813020415 69
    0xa0342680c3d41507080c0001c40103400c43c0540b142c0d4507011440d03290301c0d801c0a5654503106030001200515642c0349030440241801d1485c20524a050114a00401862844100556100baa0300708070817100700b02002038030315840c416101c0c0144001e07400e0141814840b0b0031a4002c0000d010b0394034042c1d507503550130b1078001c44031400c2e030000d00810818003824042c1e04803110030095900350404164105169651a4807030b01c21400300b4041e113610002d111801c01c1c003890369484001002d02000c1858400060b080d0b902080c02100d0304542e0304001a00c00d0f016100ba104d2820001c1c0a003a000960b00403044007503440703046043c0d845851481c125968100c0c0600400140009038050364860302100c910509580841d00100ca858101103000003c944069a0107011038840f403a04280040b460700f00a81450103000c0c243c1c004500000d00002481070401c0040041c80c402d0741d40815040754070200320740d482001e803101e003034a0780c0210b11078001d032034541c00030329000a1100070007644a55882ca500802c40b01d0500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 653268660 1250 653267410 653267431
    0xe01050615090f190b120c09150a1107140a08070e0417090406060f030e07030b16181e063b0d03030506100903020d0b2e0504050105041b031e05 63
    0x2000c8000d218059201034110722a0000c172400c02369420f00103103040042514008a00a010481c1030101c2d00c0b03600010b00d0521980706881c0c00b1a196001c141840720109542800342c2d5400f800000c0c3c208000484030100c403040380d0181400d40790b1717a85003501a0b45401d0f00d4803044105200030031081d91070b4400c0760b0017004030b40c0720200e02b100344800c003030291503c410900403590422101007011a40d240c1400e0341c4540300ca0182420310210b182d00b81d0f0f1507a122107110903d007690040219082c45008013045060303091005c0101040e80da04411903520f182d03003003400c9100f658075502a6042582c01707441c21143c0e841d00c21032011440750801086508107400000ea0020791140c040c0285410302c42c51204401c00985014080c02c0d0440d008501c0da10000300d4002c184019010005000510400000300107808116801e0090200f104410120445a02401d0712443c80c00700000741901e014810310403150b20f1f180c100340319116400422340007060604020341d07090520000381c20789004584602c5110707031034440303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 653269910 1250 653268660 653268667
    0x140a0b03060603090a0501063201080415090501140414030406020a0f020d02102f1b0f030f160b07120c110d0f060e0c060d090f0c03060e01050615090f190b 68
    0x1c2c4007400c200000100449e118000c03240d0580c55036403040e1300c03d902c00d81042c01038001720803081c2810b009216080707002e4015460040e40c0391100503000e0003540074500a482d10100e403104000e405443c2d1040e44258000350b030002c14034800144015440c0d0b0240d0740002c0c00ca600f0b08040c2d80116580013600a00707440041c4050307800c42401d141c214003100f1024640541c4070401800d906009a07600341089020380302c40141003c90304503036180011184045030150655042e40300c0910240c1e0354958015030011882c41c0f2080203c5c1c40d01c03074201034881041e08221048003a003c5a90240d40b42c1d01014019102072550028500042d101c4550700b8440502c91542c66280702060b05010044928102aa444e07540240344249415680c0c101a140c00d400240070014220362580740904004d02e002ca0000d2400204010010600825a00c1055140050802841141d0703500e410007098002e4004041c0c8000010320065030341e414010791080c0101005070080c8900030b407444400c1b41c0343c0100da0200040c1c0c440003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 653271160 1250 653269910 653269949
    0x1030c09060e190e160906020703020f2e021c0905090a0b040617120301030201050f0a0915091e060f0e0a08010e0a0c0603020414090406090c0f140a0b03060603090a050106 75
    0x503d03212170101d00c0d41c54020049401d1950007502c402c44c5110281c45551000348642d6655204801c2041507451800340c200700d202c6144401c0340808404d0100d00150103081001060b904e003d4000213143e956661740c0d00d10442c14842040b048820141c682c051303180d51503102d0703512910b4038841c050192038510400c480a090302440e4505d0640000c02d80d8200d10710900c0100010b0341c000056038003034825402041c2d2a220702c6007045481003d1580f02e100c0300034041e010161541d4000010710150360ba0b2015241454040d90f00d102540d8540784501030001e1003000109501501c9039003e50200342000341102012581c1d00c1c00306007513480b407000741c451030b030800b40c0d40034100b000c101d450b0700003002d26080646c00c1c9450404100444c0345542403103401208404c0c00a000c02c01c440d404400da00d40d1005132100303520713200d0800c0048400c0501036400307000380d080d886078000d20344b0042007000c49180400991441d0b0340c60080c03014a03040544420300c644507030085800015828043d07a000762071044400340201301003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 653272410 1250 653271160 653271181
    0x7200c030d09080d0e1c0212121207030b10030b15030109060e07020607020709111204060c02010e03070b060f0123030901050604060b03130c051503041101030c09060e190e 75
    0xc5860030f0112031800e1186903107548200c0c0801c03039810501d0245800075030004c0303588070248c0d100f01e10150040c1d84183d03d44008910251015085207140320712260b40e58001034048076000b1001c00e50000e191441001524801c0d08040d02441d0040c00d003d0f184e4141c10150703170454100703070008420952203440610003000d0900e011030b407100c4588001d200c1c60a0032400a5202d011500800110684401c055200464103008454242d190021a2109403920b410306400404881c2c41c001c00550a10006400d415800800d4130443c60b0400f403810b5480c0c4504040000f04c0c5000b0283e43e06019000c031710704203c0445c05103841090460502090750308e10b00403044c02d00b1200024490741c0f0803440c04034140644c42260080d40d50210740e240c4410350000440c200014400320300e6000070f611070b01240b0301d61641500c62000d580154403400b11003a0f445003120054007030712009034142c5c000407410b001c00c002c01407085024880e1400c0180c80c1602c40715580c110241e00081c03641091b80406000014440b07000075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 653273660 1250 653272410 653272423
    0x3080a0c020c0a0e101502030a030f2702130212070e03120f090d0213020703090f0305190809040203131b21050309040e01200307200c030d0908 63
    0x2035a201901e00400008009500c10160740115103071001100001000c5540b44c083c20300c040c0804000540360000e00c0c0100950782e600020b00383c00003904110740b400028409015100d885240080c0c2d90071500c1100026503400c251405080c1c0e40101d80c02180c2d0784490441c8000c010b082c0309685542d40078540410701502c0704181d6080213000b80c1c00f0804481c0c040c00070000395441d0810b11460383daa1190760740c000441c4c445480310302941c000070121116020301403950060028521a03151001e07055070390608100502080e02c00a04103070003d014900b10140612481c0c0ca0503441040610705020402c808a81241c2046848400050074111040284101609082c204130002c0101060241c20708803110744107418104065444401080341c4003c0180901c00e64420900180041181e44c69008023030740a045021011780208001d03a01443c26a55081c00701c3c0c1c4680010b80314000940c0ca10300d807107130121210301c0d0241c0c3c0c079004074005078049a40078408641078075526502d00354118109a0341c64101074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 653274910 1250 653273660 653273681
    0x30c05041d04170a0806130b150d0c020a05070b0319050c040501171e06010207091e0b06120606160f0c1707050306010e0709030804090e0111030402031b040e01020703080a 75
    0xf50a12003020600e034081c042d66880803094510030100440c01c00900058484411150f0340400d00007c5c0e002e034040560045d010f5000180c030203000b8000c001c0820b989840d001c180207422a00005030a11248a605005640002d0500400c80700d030504141d01008880c01502c156401e103074001010000340da40041d400e4005c0e902c0600c1012a828100c0444844015034818800680c102000042d4568001c1c4103540080c9500030041c450480b9200301084c00a040d0303440d58185a2a080c0c983c1c88605015050318600d08886c0d00c1c6100c15120001000450741000710032a4598003070070205070000303842c0440243c024bc80b50f40c0040210341401c4d61198201c40c008a02481a40030f140b040000e81e0b0001540da044941c0440369280588860000300e4900c15142c00180201c040041c00098807035841d4400a4000d072018004c20070080c07070342441181d5201c00d48010b540369002561541032103080e48485c426162000f400022001c084201035400d9801083c2c0a50120f030300c100410a00101900402c500003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 653276160 1250 653274910 653274953
    0x9150e0c060c03122d04030e030d09031a0f0c0d0b0a062f03092101020c0a03081003200d02042301080a0f1506080a080706140c040501030c05041d04 65
    0x681002c1c1d200700b4845d5151001c00d10700703480c0134045800e00d40a40e9180e90041009803d44628085159010701904403900c400c90300c21a42d005a203048104102c0321a02885040004040c285c80701022400c040d0012004c511240d55600c00081056444154500040c00b181c0c4441940500c11008a54001c00c0c0c2c441d90f0901d00003640780b55050702c07030101c12200802c0c41124800b21082c030105010701101d10b0a1207c1600e9032000a200034808000a1040341c000d1007075030380905640d91465a03040501e460b08c0001d2145017641d10141c5680404e041314001440701601c070404139030f0b00341c000406031840d204c4000240d405071401610380b001c000e05414003600f0040b00400d080c0c1407554601810040c0b200c0b010300900c02d0104003220f82c1030310fa0040030051010b8070880b504503206042c03c420990200c030702182c03c4da20300012002078001081030540705095410a00c1d0515140c1001580a4a580f0a41c2e0041020800011840044140c0240c8e00c50803100608002460300385012003000c0f400d0b1402c075548 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 653277410 1250 653276160 653276191
    0xf2b0216060f08150109151b05010209030d020a03090504050c0d050f0a060b12041b1707090c02150c0c0a0c0801020a110303011202010c1104050a0b090a09150e0c060c0312 75
    0x5d0f600201140e00b1213108101c081150301151000700d5490510740141e502600c2102c0102050050540240044840441c16103800c51003017241607940e41d04c000750003804668541010002458940d00ca13541c04a06859228600010404400101c41040302c150f54481401804d000c0301401d203204c0c0700d020703080d484812407500581418100ca8014010001083c00314280340303442c00f148030048018001c000319408620480300c07402c1c1c0140c036004503006485480f071074011201c02c8184001070145460140c101c2c031881c15100c4600700c6440c2e6200c100e04603051b21400540c8000606172540303180c000c04501c80016265079a25400420140c0d04860141d090751051005200c1100c44401c0100b42540c2428020030703500352071a21100d401640b0155980c401c1ca0417080207c00403842d00680c00c0c46a08840201c02566200f445104840d007180e0050003285940f24610381040140d03101028a18640084843c002160030018205511101c14000160070100f00c1c0c0614003a0318070040c0c0c0008100364510350 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 653278660 1250 653277410 653277451
    0x4091a0f1803041707150f020d17040209060324090c0a0b04090e010603060606021b120304050603060a08010c18090204050f0409030e0a090209030f2b0216060f08 71
    0x2c2c0c2c0d000720f00482508542c40714000ca180c0070300304040d000a1441c02101c540c1d100504030094035003035400802e4009409061041d5001622845440c0000403028036a010191621303003d1280070000144a1a01031080700400450203810f0719011919410070320f55912540303802840181000303145050980210f050b542c0c00d110300c013080d83c1a9415903004e131034006a001102c401160241039140d1010f030043d86402c001094950f40810465206104640c040d00c45040100501040b99598031802009401c140301c10700c80751900000640d0080c8000300000945512010741500310b9078484220404500f0803000b0300c0e0007111001070350008000c41c101c2142000c2c82c020218030344003040074900d80300341d641d0152041018001d03800c0ca81c400d540901200c0f112500e8605a070003d41c00303070310f6840c030910440d00b400c03106c000001520b40102c40100386043c45204080c09040c00c0c4101084d2210940c01078000d0800d18448980d402c000a22055603640310540d414070010301850320180a00f00d40107207003540c00d21b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 653279910 1250 653278660 653278663
    0x4020306010314070b031e150604061209020907080105090a0e0a021210141906140d022409090f070906050f131403060f0f1504091a0f18 60
    0x50440c3e403c0000d0540015581038414144035440d004003209903808000c2c418400003005481d00d0044410100f5160341d2036151407040e84001366032416601400402003070110030f10801c01c040c00d00078080703000300b180001603001400c1e2000844038070001544181c01080302d8a0104601c0380c00240c0858104480c085511140d80c403202c4e07003d00607015a10701c18440407041c9080090040c16103484808000040001110603200da006a9070364400d201e1503002d10804280504c101001c8851001c070900228400000b07101e003031211800140d034404142c01060401c3c070101e450500c1d00742500741d01540c0d524211030800c10755100280991030240c0d032020070894142e0b088030852040d9801828030644034202120101000c0c070031019952194602c80c100061010140d814009000d00114140c440ea9690104003000c02d01045404400113000c030030108240e160030a00d20340000c180500041103001d495280d41d001c4070030031a5094000b0481c01d042024002e0044100c5401c551000c1200801d84034101896 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 653281160 1250 653279910 653279923
    0x50c1905161e12150c080601020706090b031b0f0c010506270f0414010e0f0d03140414121216030218040b0a030b011707060203040b0a1b320303040203 66
    0x380d820444500700f0b000e01100040c401148200340c2c0041c0115006200c1c0240900000d6615501621440318007162903801200140265034035414101e0542d503500848418401c15022581009082004201c3c139010040c0014507856007140000310b6103090403c248404040226601400340c00c41d10382d40040310108014058001d54000c00c0311010b81c4440c1044e60418080402d00035056180425003641c241e4003080680c18121410243d401005c0d14610680c20385607100702841400220800040009030940301e09042080d150045500040000c036081c4a580d005910360701c3c0300c50310704c820000c24510101c011407440c54289819401c1c40c02e600742c070141440503051000e2046441320780d1260103881d200005001960001801c05482d40d4444400e401d4010306505195517016030480030076858000011030b03040b200b42034840fa00d010b404d440119000300d0359a444410b4600e80d20b85050100f285400d800000b200e40313810340c0524900005010364011001c0020802d40d0700240200405603a0201d030b0f0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 653282410 1250 653281160 653281169
    0x20030a0c08070c080d09051c0b0105120307052a0415140310090614010f120332041d010515030613050405010515180403050c1905161e 59
    0x81e840b0400c43c5840300701d03520305401403c19481030711440c1034002c0e03000c9906d0044560540c1c41e00e13142d50b0241e42d0607120049524000d81600e0420f0010009820541c03059580f0103142010780381020002e40c0c45609011403000c1c20070100080c151001e030f03820300b1040084182c0408a0702003100349100340c22496184507602c02c101c886248294011400c2d1801e21140042c80c1c0020300402c0081041c1c98048010925403401c42480d41f0b0f400d002140e100c00d100035007400e030750b00358418440c20640c543d0704403a071040c2c21200d0510824014188040d484080c00034134a50782e40034a0441e2580d05200ba0100d06120f98050151224000c2d00100f000b42c513180f0002010750101c12042e59a07a4803400030540261040e442100d04d503292604010038003c0640c0407a0290841a000c20b00e031502c0303403081025407003440c410410000052400f007400240030740002d000d0500e492081e113005105803c401d2062039440901076403260001c54a1048280e182c1c1d4102001c0c0400801c4003510040a0380210b40e040c105009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 653283660 1250 653282410 653282423
    0x30a08040c0e09150c0c01020c0601060908060c0d05100909050c120313150912030801050f040506060d27060509010b0301020309070b0c010b0a120b06062d160320030a0c 74
    0x21445d4140e82c4c40c2240ea03410f11040c001c0d5038071400c0810b03140d55920709228031000615800b002280e5541c0c0030031000c1c01080088107560a0503002034249000380380c041d20300b03400030b002002c00280c9030615000d20b61446014101601d480d1600313105100400c0491000894503070400c000b000712601d60740110f40196420326196500c0b40701c00d05400c5d51510b2154004001c081e03002c000c01c1003090b030301ca64118180e03401942c6840390890f0309802c0c813040d030350700742c0e500b5520440c107001e003140c4140c1c01d40c031901c40c00740880700700c0d41d0346071403101c80300810500d012060300c403203172160104814880c00740a50303255403409078002c52035440d0002c0c4541c4c0381d220074062480c0c0c1c800f0005462a007400b0941041da401040201000081551500c0003860112000030440d60a80031030000f03005490316000f9074002154524654141401440c103014004160f060103450940c410301c0078503803c0c0c0e40b11401d50340075031190b140d0b941ca0310000c02a1130b01c44a0083c4408025601c100002510305038044a2824003036817211 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 653284910 1250 653283660 653283703
    0x50c0910081b0906070506011e060507020609011809051302090603150c0a030e1606172814070203040305070e010305030a03110c12030a0606090e040221030a08040c0e09 74
    0x1000804034170071504094458420440042804c03036011840c1103299030355202040c502550b0300015035030b5000d4144040d50210003401102000c1d4000d18046424080c0001d99011180c2c8030705081d03040320700030794107070b5a82d2150350410411818520300340c03a000300040b4020010030038850820300044000415003c802500410b04032042030094100b104d00220040130703120720301c450100b218118241c62140c80006001c2e10f481e40c0c800b09000e0003040c010b409407950403900d004107540440c0200000740c4450b8a442c0d940059500b1501000b44070fa0040b00c60794055683c0301c1c51810080c0c5800c01582014030b0f1070070658010000240004210f921804207802c0124501419246502c1540030300c15884c8001c0c01034007152108040800d00030340c4600c5000208105803a240c040440d503443d2607010352882004400d002c580503145c03010091059403a8490140c8491407040801403c6422006c081d4010802c10020b000c00c0080062100004e0050380d9080070082c83d03e400e0300c580e2503a9194850b44002080e6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 653286160 1250 653284910 653284927
    0x120703030f02160e040b0f070c080901120207060e01060b0a17061c0b0109110418051506070803040c050d02060316051303050c0901090b01080109150306050c0910081b 73
    0xe012400d40b006601001641080d03844c44130ba24149400c5a04590740114100055060340080b1107150241c507490b44d50304150b0304507603982d24040d40008420b0b418000c0c0003505080710b8503a8002000103610030440401c060399891400da00b51401500060001541444009405a40700ca04000302031401c91580c2c1c0c04e500c945021590305054001d1014070301210465010620010b520b40b94100c0d030403080c00700700d00c00b0040028043c90003103000e5640d40544008003e59804540c0e04055040200d0b005030103050300e4200b00058056200003000c40701030b6808010082444074601003d0f004110a0325004107101c0c1c07650005619110082c9010021807110803240c491030300c550142e5111100420b6011030381c0b43c803820140d9440101e18401c5100305a075100100c0d03101c840340540d4551520603100c04005900300418140034040c0c2034042301d0300b4201c5003000001302e5903502400c1c2c050001000c1075655000a039041c864051100c1a40000344101c079018086480c1c02c110702984060040e6001315202d5140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 653287410 1250 653286160 653286163
    0x708030f0d020f27032815021314030606060909151914030c090f1b0d0603111206060d030201331e0b090301140703021305120703030f02 60
    0x229405014008008545080705800c5002e2094440813139060b68400d40403070508050341c8401525900444105180c2c064a4284140000410322842500c192060134200c20400e4120f8005d01b0140c10042d20020b01000280d80c02c2c1c9043c4014002500074112070700c0c1000100d4564402c0d600c240340581848000901d415541e81d490081d03002c0020f00088070100550701e4405007210030701601d0f403e002c4400031000c4078640010780020075080601499456035808844000e6030300020105204d1300042020505140c1102c8000c001c2050f00c0140000c0382411402c2424111944803c643d00840b110b445450900310009611540b203042120b40032000d02c3c0b9403404030b0161080d01301e4103486c041d81c111068000501c1d2086010350403090280701c0002640c44041c61243c0c031070042c040307000f01d01442c5e091000584007030003007118880240002c60300c0d0800008000c03a0f80700c12a04e42002036404074515004042180b1900010407044410203600354840725441d8580c0d005100c002d09001900310882050b500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 653288660 1250 653287410 653287417
    0x62c012301050906070b04060b101d010509010c080c030301060f2303091002030c071a0c070b06010e10081506090f0607060e030a020a0b060d0b04260c0319020708030f0d02 75
    0x24000e8941b40f2070f0500e850100050804000c90030301c2865600c2c140041d2610800010421103101d1700581c001200032401503401e80c0c0003507502410808407404800208030f070103008049c4080c403a001035035203614010005280040d503480100400040c0c84004002001481e024036181068901d2203560780c5628601919003e0320100d587c003440d00100420a892007500c000d030810900078407035105144084503141c4050b080494074034218241c00d00201010881d80c04400e0b501c00418104007040004000020700400000900700000800c0c08080040c10a0f00300d00840d001501031b1441d81c2090b94190000d28001041103909001e0342d00803c203a01807080580100c12981441d0303007680d81c0e86081d024000d4031500c031408103a400004000120301141864025a1b10a80d0420706064031358959030b03140e041082c1070b0120000e2040c03652241c03e80600f40d000c0180600c011440085544078030038082c8000a84010886c1025500007940c100011000031040329607a6460807030300d9580e101c508044800900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 653289910 1250 653288660 653288663
    0x7031109183a0306140607020901030b0405100f02180a05150309030d0617060f0411040c110f0c0312030f0118021c020301030318080c04020c01062c01230105090607 72
    0x40d90082e184095981651058003500e0a0242081d00711850000f409481e11030030100a400ca40ca150040001c5600301c9480ba4100d032050090301e80004844c1c0c0032005558004207611800ba60010300c454040690000b8001c80d464240e844210542c40c02c1c0000d44000c3c0b034660540c2c8900000000070b00205001d0049540140300c0c02410002d05403910049a07103d038036814250098410349010a4003003203031148562240754052a8284600e442405000c0603149075140c1006118006031004a074190500104408201120042c060f4030140f2013014602140d03920409031750b400c1003051050721140641e1040c10344116401040c1c0340b254030303a1140000e204645030105810100200d000300311805400443c1203a0107980d8031008600c081c101c0900c98100c91041581c0c50340003000b407102c00d06080e005044202607580002a58a5560700c40092019034852041032407081c030a80c18410800009160340034105000206400c40011445992000402d0f500d00307040c42004a00070f005640e550307044680e0380307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 653291160 1250 653289910 653290003
    0x50907081b0a0317121003080d0c201f090206030402010c0807050a030503010e15030703030f0e09100302040c11151803121b0f030402040e030c0703110918 68
    0x1070118a080485402010420000100840201301148401b4072110141c0350441941450b00d140744c090b02c8020440902004148482c2c41c04c50103a0071940d1550440d90345030f20000d0100034001d01104050410300500545445207004a0740b0056140d10095a81c0982d080c2061041940c25042a912900a614004040b841503c254108140e40304010f03604892420840310400e458a56501c0c0130fa15200807a00d806a03c028410000f19100702d041d000c402d9110706241100c601a9004070f080c035682150803600821500c5400c01c01c501b82449141c8098000c0e141200507070b881da0342030944a000d0800e2520300c401c1441c0c0070800c500c42e621401e07007070304190300c0441c1c1c1d0721012602180300780007044548000c0380c5220144006001c08140448050f503004400c050315664650342000300034a010f400c504010322050100711b45658041102e04080c41c00765030038400ca11002c2080200c281402008000d203104090385289103003900041e041c50100401e8101180c101054082011501084450100c5d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 653292410 1250 653291160 653291183
    0x9030f1209050121110d020703090315110d0b04151d0c03100e1308040303051c020708190e0301060b0a030e010c0f26040305030a050907081b0a03 64
    0x1080400015030080d4002034903030340005651940103407000d00741c005041c444402e1040c11580c20309503d921498480c0b002d04403440c04c00303600e0a5014202d0f000008101d010490103c006e000b17000b24041c450301c3c194074034401401046124162011340340904080355034a5910b400c00b180d103a60390b40d00314134100008005c400047d00d5951030a078140e10440303900c8559502c0207a010074080c058880403079100c0c049003001a0340b080c0c5800c402c444090303001400f4480510f044020301000600380c1c00200020f6000381d40b01601c4071110002c19107110158010158186d1040104400003000001661019000203405c041c1440400d84240c68680040320940d6040d480d1003030100b440c402d140e0141607485a40d90b03040201c402001c02842c01c030f407142d20245010500300343d0000d400078410300e42d01c0c2400ca200c9440316962000300e100c020400c1005d8508502090f00801080790222480c442c0c035a0041008000340381c2203240c10a0107490b04468082d100141c0020840350700e40c3d84510300c600004590101c1140b00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 653293660 1250 653292410 653292413
    0x30406020901080a09030207060c020114030703060f0807080c010507081c051803120f070519030b040e19081312050c100c050303060103051e090d0e0301060b09040c09030f 75
    0xc1d80050340c030303602203515600803a000080720302c94001d80c95450340041004030704141c2c0580c0e85014580c0100d0410400052842c407130310688002e54012101c0743c40c040381c20740c1031424004c07044c41e694200001c141e0051800308000400002c0d03180307103c0b00070308003a035a41c1518104045144a40140c0020400b01c001d1460001c9445a000605c224110541031640d40903a4198070b840784130303905c3c1f46041c1c520803d010604c07101420700907070380040107410818600781c022111001840c94110118000c08ea0f81e46605860b8100341c014800c50041e52400381082e0440040c161001000301e0001411458001c03071900842542d5500380006071000d04022076403412186400d6503104890300e4414000c901d1030b00414000d40c00b030380e860301d031107a4060090360455441000440007410014015010014408000e039140001c1c8001c05000d2016000504804080d0340d0028062252040086009a1606004100000440068030110041107030080742d0320111040031100019190009440b00446409100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 653294910 1250 653293660 653293673
    0xc0306030227060a080309062209060e06060301030503031504060906270209030d030c02011b0e0102151302120709061205010605012604020406080f01060e01090216140c060304 77
    0x841440c072038002c0404565809042c02020002e511443c034441c2d000703200303401c0240303448400750003019401131800d0510344180e48011641815503000d006810764075a42800310312402c1640039404501035425a18651456031100c3c1d8920006051034803d0303241d01e900400a60703a076000350b0001d02c0450307014488141c03100c2022050703449043d02e8801d003036041140c0c03c1c6071030a01d0080d00c541200080261150300c1d808202034000e40803142059046550702d00d01c0c11030880d40300c00e002042d03034416a145a110801100003900e401c1c540c16807808aa4000c0301081800000c152908401950659802ca02c083c81d0514051806450360040d107132080c240140800c1c41800c21142c00340d000d000b00000d00256a4820056510b2462228251509403481c0300c610040c130081e02640f900f0071300c0900001030b0300340e0301c0500c02e041c03581152030110607944030715082002800c2d02c019107025141401c021850401c001d807540e80c1c02d03c101400100210740082c80303184031703410034401803040c1e001c0039282035520301e01071a044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 653296160 1250 653294910 653294959
    0x60f031518061a060d060509090a0b06090705160b01140109030c061b0b130c09140109180506090607021e060402190b0c030d050705070323041802030603010c080412030c03060302 78
    0x23805801c40c000064000d05c80062650043d80c0c100b5020704840d01c66506000403550020000c40510004011003243c62000030403440c1400d018001040f415410025503151030780031401070a0402900d01c90500c0801d69119061040b149542000e88151074400d45c00c808500020f03034040e06511400c0300b0040b112032044498904c0c0fa210701820f4600ca9100c844170340803a814900003200441030380c001409180707050742c80fa0208140003548105090500d80d91285005070441c0c0c12610758100c103092004140c0c040042a41c09040c0e0074070101044040c1e20035582c0c0700d01c002c0010f4800e10a9101004a0381032040042014001c02541c1c155156400d064155032503002521900c6130074513200001e507145204500f9242a070760b042c0e03500c048481c00c0f08958100746030102c064400a0308200310010311009c041c2c2c2001c84012051502503220b16045040501b111030580c0003506105d0600708000000b43e0380401e03404405524100025081c8803240c0480c010403260708003c2d04424403d0003642c141c0341b0300911 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 653297410 1250 653296160 653296169
    0x3150a15080c070503090d1e0f0201030f0b061e0c0a050604021f0e0f011b0b010e0a0902090a090f02150d050714040603110d060f031518061a060d06 65
    0x80c18107988424100c1d00040c440c03020f02600a070402d00061100740b40602640040c14003071041c103a4441c404440c0010040f80356502160b450190172a543e0031960180130703012402240020400c002c9400d480824400e22034000241d060800c51181c2c11041d0711500252501400401d003251444005803508580c4d0300d03015582640b140c1c40403582d0312030303c420703112180307040c00116070742c0b107481101c503030144035180c4083d00e16581030181c03e05005000401841c007150000b03015203140c1d9519450469020f48161020303001e8503c01d414444444056214001920b0700303c41c1d205030000e00d0743c0150410405100d560754000754401c0020300c0301c8104445a801521b07a00342c1d6132104101c10f4132006020b88800d0300101d0b008082d01c90030b010402c0841d01950000d1a40c480251201d23160000901c01d0328112181c940143d8042105004180103008500b2000e08102c900050304000031b5403000c0040450001109000f06030781c0d01ca0302c0250124120500489000c01e024218a4441c0c80c40d0f0000c40c0072f884540903 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 653298660 1250 653297410 653297417
    0x605030a180c062001020a051810080708190f05040204050f07120c0201020d060b07050706080708060d0201020a0203010c050a0f0513090c054e010b03150a15 69
    0x107000341c66544084420200035440741d10400c2c070034a024415110f440f0383c500c1d03152030020405030190713101d0420700040440c0710a80d540c2c25074545400810603020b140c0840003e0182e006030100c42c4a4039048120241c1203103460503d680d96a0750309200344c00e4808407040014102d810241d0200c0c0d400525040700e8000c40c8200e4003441150341e802000301c490001107807440000391342824034200710300803035012500725402480007514042001c0588000d03a2101d80c40001d81c11800108141401014820040584100d250400450400440c010484100600128454055021341c130007107a0080080c0500640d000d8000d001905407400c02a001d41c200c01c10517000314060500500c8018403400803030704407090a64004044505040921000300050030074002444001c1094980104c2500d1401c54240ca4121103480c040d0110308540907207052400f0000c0b41240003002c440641280d4039142c80c15a1540e003403007a225510310580103000c0301a00c052503005443c25101103003040b6848030781c0d90404040c0e01d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 653299910 1250 653298660 653298671
    0x909140d021b0904030c0305030c041a1201080f030403030e0621060a140915030a020a0801051b03070e121e071739060d0b12030f040902031806010605030a 68
    0x2c140010b41c4422100100081d488021340c0e00041e0040c0302964000d00c03009859400c2030b4440c0e0401d03003010002c1d521006040004682196241c11222480d4091b101c0540a4000083c400c2003440e0740b0701031030000806100b10380d5054041525131506461011a0401202801420000d49400311900070b9820a0261071441400f084600340d0820060301075102404000f89603071802c13114035826401211999050050120550259596a80000c040c0141c800002400c0c1420b80400c90300140d05421184003074030601c100014142c104480125501041d29044440c2e00303c104501d0810360542d034003034903003c0104000503941c6070015043d000e94150a1301011400d6400225031754481c805a601c49036200c030900103c6c1000c0c0d40c0800d0108903500941c1c00e0350400c210000241d05608171100c18004280c0e264411001494150614221005480080c51901c581d40410110a124501401003a5900003010800280c020369548603940240410344105586511005100d03610948481000341c0c00d02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 653301160 1250 653299910 653299963
    0x18060f0e1017043306060206040c0b0a02010b0306010902070501050a062402010605040c1d180106050a1404090603020109090b0f010c050307020a1509060c0c0909140d02 74
    0x80c0740041061919110b000d9148181c404440001c00010401c5982445150300d40c09901d20800214104240500c1d90580c1841d003c01c2c4141180d4445d8000b00031944020b090001090500b00369000b99802002d2560391049c2d24841a0b0140a00c466121380602c1480c2c00003c9480d8160701503c50725104900034402070b1031707005100013900d002d402800c144041d006014842503480202c6907441c000f0701d00021440658410009044400d000441008502048a9507402d541140140014200101d803030902500610510340c281803014010703d800d02400058803c07400b40207011030400032078a0300c6100d503160b8503440c080d405864140301c201d010071403003d804504001103000e1202c03408800341450700070708a46401100c0c40501010140c43d00d000421580c805a100c4805400262440110a443c941e0302d01c1801803146140361300c0041004941e14800000401510190013100c411540218402e40c250819400580c0740c2060010184203400095003265000700e890700300900c41050341d03031030001003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 653302410 1250 653301160 653301169
    0xd02010c030314012918102715081b0a030e030f0c1204030312050411130c0e0f01082403100c0f090503030a20191502040806150118060f0e 61
    0x170507000342c01044130000c0080703031303401c2005035854000c174103103001c0740c88034145028016541b4083c003003980d40c186c3c0d00d4408d2080812907071020120907092b1a141c8110300d4a0171180109070a560480000784400040c85d84100d0300c203030841d4608a44030002c0e6683c07038040c42600c017030985c0300e42149021070107000c1c1d401503d00300d05004d841c01c4a40540f40c404901c0140d80603400103050042c000c03944150050342c43c000a0301e07402010b01c01c0c601c11030800a010300e0703003020190049100800c242e110b210000301e03400c03040e640302205507088101824500c480101d09180c90264090142c030483e054810744044180c060ba954000e07e851115a488690490007440340c212000501c0b0b005031500742d4810002001c1080c410306404140004c3c08011550504403440064100302e243c0b007081e05181000b460b010140328a072002c48580c0007011000b107140515110700161142401001e543d00a0942d6a02071881d0740500c0f61862205400e440610310307551201805004804201915800145116841d81d4039041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 653303660 1250 653302410 653302417
    0x50603061b03091501060c060b090c1b0c061909151d010c0c0f05091f15050706050a090506060a03031e02070b34020d02010c0303140129 60
    0x3140100703036212a00c0221201000c0d072010780406407510803007105402d2140411300ca280030b040702e0307515405003d0003400c0480c2030b1038200500610501ca20010f11000c5000c0000311000a000c00d144100c1320000d6075400d5017002c8200d0f03500303030f0000380004040e0042d136200c196685031108d0382c1d102c0030b0000703490f11020301c000d003070240710318000c0340b138000300101c2101c00010512600a030514101301d01803461350f65a14003020b10341c003016218083c00401e10091811012140c3e200349200c01c000f0900042e4518880720340050311072440c0c0d01d048401d152521610844c01c0710202508441c090006042c440400401091490810740e5a4000d503000318032a482d04000c0c51045030b41542d1100303a0b00e4244482140032603914803009056228041002030724000d40c0d0064016680041c3c440710402d048a084401d80070780d909245c02d01000c100501c5030040e5030300e80e04a14816020302c0d269843e81c55915007a80140710900060f20302941d60310000450304203401403008c01e50049000020850481c0014560600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 653304910 1250 653303660 653303671
    0x50c04180902090613090507030501020c010e0309060a0e010207030b040f0b060607030c0b100801060f060206070f171806040c0503010e030c1b0105071a0109111c05040503090a12020405060306 84
    0x10030f10b101149151030a2005941c80744c00240000030003903869030b90945080700a0f8800c4650340d4010076089032800c1d0038800e602c8100c0c00000034511700f5461100060700c030b2203011841c8082c03040d8cc0702c5011680c0d1082003014059588038034081003500b401e05100702480120f0f00c04039214950580043d2030b604084059a52299268540300c07036a008560710a01201e80080498400b076400318000100074070709001e00402081c07107403e51201c40741002c0c0000e04040703004201d081845216040991800e0f8446071540c1982c0c058500140a51140d000303040341005089400d10007840340105020601c4005841c1070210798003107000f0440c82c103400b0b507032948030300904200240b5900888001e0349080c0e000f81c00c910080d0014985945003e040c5c2e070b2103032403d052a5400c2c2c180d180541c070051003180550302c85e0b50360b01c03903002001030b04000d18130401c141b024180c000009249030310755000ca030401208000707030740046400034100a04c894440d8401c0401d0303882028184c3c4214146804583c450401284003800b66 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 653306160 1250 653304910 653304919
    0x52a040606030b0f0d060e1207060b03030a0207180207080c0610050a08070506030a0e061614070b0a18021c1109090c0d1119080d14090103090807020301050c04180902 73
    0xc1d044d01c08005451003407500c1590381035103c0700b041200003800d01a54051023071070f8843d9501c8548a040c6039003160009404140290720820503061480d400207a22421580d6000e4001004807514031508040d008201d4010822040820944504400800d1075480744602d641183c00705903542c420450041c08500c07805500342c00400003400542402230007160311a0228102051307140c07010b10140d140030030445100d04105210140c1c0c0182552100382c2c4072074502c0c0802003034104070164031000c1d05a4406000c5107216a9210009480c0e07584c900701800106800410419843d003c1d004e074a8240740000c3c1040b81d0500201e98258002d107003e0400034040c01101c401056580d40303290600c85020103040301611400c0c8000c15140655950080e8604040010b82100491510341083c96280200040c804001d01018200c504e41e440c5500083c0c900e8102e0901c0e0101385194031b17080003031141c4200c5e88040d4240d406c040402068040340001041111415056184103250114507003080301c03440c4000a501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 653307410 1250 653306160 653306179
    0x10608041505400f0b090105040302060115020a063b030d150b030907031e030f0f17010e0702070510090306050604020d02030702010f150b0313052a040606030b 70
    0x88250990035803122020700c141d800481c07642ca01903010031108803c02103030413a103200a0401000030107407200c3d800861a1009011a04290b90701a498000500a000e114042140325000c094400c07c0040441d907080319040240380f10340b0300c0a8608502e40460501d0703001c410b400102c0341c5004603030b0030b4101000080145081036580c1a134803015041d41c4070141181d4080d248003041404481c4025809042e01000525119180d850000415180300118500e000400748000c1c0200380c004c07044000c190303011305d40000d803150f00c25800e0780d04c00c031403040d61110600e20800216801a5900c8600d0003034405808440302c13550742d90100901c21005c882c0341800148a12403c100248143d0010f5400c14001440136042200e0041c0340000c0b83c100b1141c203030040c0e445000c40c10b003445d024800c1e034062051503000700350101d040c1400b070380d6503100c0542501601d400e0f8080110602c0070074440c1c84440861141155100400ba48800449180c144d0340345128615201d4000380040c003a00c0740d9607c80ca0040c190106 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 653308660 1250 653307410 653307451
    0x50c0f0a090e01021e03040302010c0309021807021903020c030609010c050a03020c03041814090d0504052b23010204120f03030b031002040915120206030a14010608041505 75
    0xb900310001401090740d005c0c858081030441814a0445151040c003a0b140c42e4a06030070b009007174500b100d500b1410f143c680350b080000340c0c69a050002d01c00007e054014003039120164220725001c1c4205071b60b40078101c42d03007481041650103d21400c0c002e104900700c0c1c1ea035880b481d269508035601030040340f0115208011015504e4041e8000c0c01e80200f02500352810301e0b540c0d1074005492002c0800340c41b400c540d01c104009041c0d102817403581d0030606100c0146005403403120080c049200b5800395511803103200120300e0100b9a000303240c03040201000b102e4000894545040d0201c440704c039007404600c8156003584030104005209071003c45031a0841c1140c0011640c13603c00195030502010f0703081540b122003000c01d50714100084074040d00c2c48100140d60760714050600d01200c54031091511030b483c0640c4108001c110500036400c0351038040361040c1c5d503230300c44079000302c014240310b0307600b80000580070b000051982d049004184224010000300782c0744101d00e50050100d900484460a488002e1450b805 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 653309910 1250 653308660 653308679
    0x20408070e061002031e0d1506080a0911130603020a06050304031b0b0f0402130507260c0f0f04082a01020d022a04090501020a14070b0615070206120103050c0f0a 71
    0x18060300301c00450301d01d040455003c000075a14099503c0c1c400d0800604100182c80e40130340850f0b0b000d84908001c1120300300759036507501a242d44000d07841c03040c15023b51051095101342e1081c00110b034004c2080c0301003560f444000d800c6030011035042e004a0911840d10000b0b80c3c3da81b24040406a12510b240362581d1844410910890040e006903004901c0800d146070820072841010700811058507541c050280c0e545810940914044e0000030040b2180f09000c40500c86400340e864500810290340c2c2c94400500e81c0e6160b80c0503a03408403505209000729481c810f40607034045a071071001c03046c294003e2032050005903075a60701902d980f0010307808182042000d903d410080e4404600d6070301d400242106240020f025124401d900740c41c41d0354000b50402c502c0c1e4000c412200d0f070450000c9640d003880f8480d103c64a8a40004000d00c0c0a44003400c2c00700d03600400001162607507a401401f50f52586c0c2d0304d010b6207640100900040301e082c4075040300d10b42c0c0740c03402c41860b0301a07100003442141c0c56030070303c00d664 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 653311160 1250 653309910 653309947
    0x18050d060f0c0c0b1914130507050301020a0921290a06120b07091e0815060603070e0f040903120c030209030a02210f34140310020408070e06100203 65
    0x21760195070b510301500310340e1040043c50007008080d0850140c14102d042050801400742e0009200b43c0c41042a4a819070b000b0090f10121500e181c04007901d4020601540301004610350010a5060907070809643e40c1c100c0314030b140c0110003800fa112a565100345030307001100d895010700d108400150128030006100e444280360b00110914081071920750b645214443e82c1c400072903956020384514010f00c0354840400c1402c0d02e440790003048004504203003004c5405444040c1c11072040044051031380300c1a0706e0341e84802000e001d01030002c0010740c0443c2401828102800c5400c1e0046003044403940d41e251090080c1d071002d001c028060030b40d0a0807a42000000188440640215075580d00003060240061001000e5020130401801044820116040e032880799142e20120082e00308441b10030061000c010315064503040c00b845641c500c0140002803901d102c44541d01d6403540000750204000c4c101203400c4049800341950004903446070010069000c0300c0354074110050b841800074492400802149 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 653312410 1250 653311160 653311201
    0xd0305090f0a05120307110f100c1a160e030703020303030a230705130608100e07201605010c0b3705010608151018050d060f0c0c0b 58
    0x1006100b90380e900c0420001e40149480c1c0300c0c0341d0400f107414402d1140d20028580403800403500e0410504480000507140031400e424442048607805c0708200b08504882014030340d603d4402c0480e1240b6101c03c0315001e48240070044000201d2960403400a41030020340c41d019203030700401075421070780d07106915401030144c010701200030f045080110440f03c1d044c20141d800380003c0d80d00c1d140d5501220583c80d2010b07032035030700c20380400c542d250400c4000d03000c1035030201c140ca10410340c4000a4580c10021185280d242c0c0e540c03001c810407103542c078240f142d0004244102c411000010f1942b80e0780e40005664010409001404c420381d0407002400c2e160b121035282031404050030820521205200103040841e801c00c01c0140c0e0f00355107a00600646400040c69580a02d894100c041030400113804101042441f00c912024051000e030502c01c03941840920a010317040c0500252a026400d0a141014041d44a0841c0c68146005040d0080c58494082491520307040380200e00d00743c80300c410b181814051541e4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 653313660 1250 653312410 653312419
    0x40312020c070e0c03060a0b0c070b030402010e1905010210021602060702180c12150d151b0503040606080607200307060216020a090b010f03050c07051f05060d0305090f 74
    0xb002c10401c44581c081070103500415080c0d91a4a490801d010401d101900903c1100310203100b1001960b00004a0600b540c0406980300d44039102ca100603620440d0041c0519400707440c0070340c10000901c86c100740070100c072000d90895140801c0300c9190b001324403640c0c5a041030400c043e00c000c409030804000512540348007902044880d603140c003089596200035100c07201e0300c80000850501e1101c1c81856280c01c49070103c01c42034041000710000b984285d071300e4801040800f0548141e107108005030710011200002100c86040130500c200010b00310fa0040382c0c00c940c0300c2d14081000c104032000054491060405031101c081c03210a05441d890340521070300b64007555100070003407800001e0301030020304a04861003000e030200051500c10084c1d15030290700401a02c900e40030b50115a40ea0000c030300d100e40022801c1c0001c040d1640300e40360109100f051400707801c610801c0c40d4020500d10920348001080040b00c3d04100d6620ba400c01c02001c0288410041d000074024000c0c44c008d0329082021b8120b0348401003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 653314910 1250 653313660 653313673
    0x2011808030a1229040f1104121a0103080405090a0f06090903111b0f0d0b0c0717040503060f06130c050903070911030406050705070c08010b0a0e040312020c 69
    0x810140c590b90014400c0000200000003141c1082d6090060749001511400301e6610344202c0b286402d001c401200019119030340712555103941a1407540102c008071103610350710380c1d56034440000e4068400144d908a0307034100c0c44d14040c50300d00c0640c3c900c40d050300da00856083c81e1a14050411902100c00b4045042c040d0b0740e0760a200c04a650740c82418010000c40c2e0b00032560945500300070300242550310400c84250401000010015040c0001c1045004c0856014940646107004100000c040c144014406140d1000707004442d500720b009411520301c0f410210120034131000d04046240914070945805a01800101e15800c14100e100380d44000d000e060340c00142031054030b000c147ca51400c41d40300413400006000c0d015007800d04c91100070f88100381081c060f4011041200701b0500c00100302603c801d07564004140100e12a10881b102d25030088402109580c840c22150300800009031500d12904200c50001581d06a006015126036056190300c6c03a05800440884060352007480710203854001c58 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 653316160 1250 653314910 653314919
    0x203160807050405160c0204110906040e0a0605030a1e030e03030a0c0b090c0a090b031203010b0901080604270503040506120a06050d24090206030c0c061f03020118 72
    0x10000540200506001001d80901c0c11042c03008858014080100c009600c003a140d0a00740c00007000079940794103076400140030380b12503442d01d03503401415015903202c000040c0025040601c0009a4024950103904202c1d142d0345004050344c0d6140da0000814102803184a02d10314461103060360440c81c0a070901034070144400000034210b40c4607a00b00b2010404007403600301407000c008002d40d4400703528001081d0b4103135180002154000035101c2c01d00385644408200405803018003c640c420b5003845001500e03961902e0802c00680c0184442500040d65000000c1e124070b840d014440c03062030904145803071001c0b5550740950241d100e0340e06403194030003040000380e95160540200001c04078061302a03c5414110520815500c1990000344100b007500104808100c640c2c1418129448000001403050540c0a440c0c000e41800d120280d40100080104440c0c406464018421410b03010155410703951b0398002241c1e0400360401441c40e200e900032080c0010750245c1d00901800c00e50304032000006968 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 653317410 1250 653316160 653316193
    0x12030912040303020d0e0f03072715030b0a020306060f0313020907020d02010608070503070e09120f09010e010c081e07021c05120a080a18050a051f060b07020405040203 74
    0x2580700f1030041c0d004000d41e90145501c43c1c201c07049003c0490301c0f0004807403204000303a520111030150219042402001040c1078006056606250458010034090900495440d2985a0292006031812002c090000751010400c2c42204c2c41141e00030011402e081c07200d0001c005c960002004140c519030300c2c045100143c0e560381d01082c4107180340c1c2d0040034a04242040213003501c50a17407001103554401c50040c42a50341c00305105041d10104200e1600c5076039841000c0d890854086040342c0000000180c08004480c00300042076114000c1c0c0302e9a4044880d00011101104040c00143c120b010178021084403054042045441400401c500340c200101c580000302914199800108003a2150200c1810020103102c4100996003e19410f03090524981000c3c00340d2500802d40010b959032412140310794800c62280ba84203c1e0044202c80365101c540c41d000307542d03242444580701c609a81203041c000500442c05040180d510805036207003080b1441e170a00000c1c01c0003500c101e9060189046924034083c6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 653318660 1250 653317410 653317417
    0x150201090c0f090b030601031104020705070e040303020423181b0310060806060f040e0402060403050102130501080606040317030408041d0a0b010f1b0c0b0a120605060c12030912 78
    0x1406144141c0246000f0803d011110744840081c060b4000c0001040859640c010314160032205440141e0b0714001d9183c16030400d8281c0e0031403102c140c038640c144030070b041d4507a01400030b239a40c500c401c440c0c1110310160301100540c0c05c2240c5070301501906171300408001c031080141d01300d0f109100522401c00500701c1d150540d0400c88603c4040306500c1c0042040d180c0c451305807a0040030a5905501d0168501181141c2e1b10031806022049403100340807070700715150a0110b0300210381010086403030b0134859485404040c01442218005882c0c50041a1070b46007a03c11101141d5102c000e420720101d84005e0701c5141d4100900c26140308005000005036002200311241001925600100c650b14041c3e00b41c80403a44052002d030304220514145001540d000b800d0b000008208220032426050b9a02e007070081404039400081444030302140900d0fa954010045403600281c0009c180501912401030160310f02401c034201b2900e40c0415801d034000346201c401560855014010b480c0300707007080c0700c601c82e943c0d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 653319910 1250 653318660 653318669
    0x16030f110c160f0513090503120a05060109050a0b071407030203010606080916120303090203011113030b01051203090d06060506031005040510081c03020702100c020108070f09150201090c 82
    0x7045441100b560a06000e100c4014007a080003c0504a04003008100f171103040c0000781c1d1401e030ba02c0c0703601d0040c0300041060b5902d00d08200c0d20100240307000001000603040554125021807150300c004200b510706055548103070781c28001c180e07090510940710b116952804c000301d010f40d40103071440400962000c2c001e0501420351b5072100071a03810000d182078545410000a03460002d40082c0038403801e10404e025900d0b41c1d03010700c0c0204a0030210300009004000401d450141d8010000c1c05007802074a41040c8400c0324010301a4244a1307a94a0500034107a16042c46a030442d0020090b403e054904620342d071001e2400780720b0004030ba540300c40100341c0e036900c00d5a00120f0a034949a04000616003402602d500030242420400c0007031a02540703030b90b114203544400418151510200d6484e03446030703060740d0043d0b4009140c1082801c09482c050700090b542c54080c2d000880b04000141400e00490380940301c01025550114101e00d065502c0e41076201c89045030f002c6540300c0101102042c0f443c1d2003c400740 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 653321160 1250 653319910 653319913
    0x1020c330301030b0a1b030c120525030504021027030c0f1205061605120c0a0810210f080a1e09050604050d020f0307090e1516030f110c 60
    0x950641c2480c50406600810250045d800c111001440516221105841c481d95090209600d0400107054900080c0640b8a481e12440c22080162002d070104004a0720301245002807204d4000c00d00880654004480294000708010851903000744500148090001f05440f0740400b08030009061640100640c800d48051701155001e10081d0700802581e0000d0100b04107900c80040c0c3c03030b030311b950b11a90014805108550074095003090180144111303841c0c41c0c080662114a882c00c0340e0f055041d600048400b000091043e000940d080f0018101b000966135440c10018034101a0705002c24054154101140d15506035514180050508400342182c148940c64201650701035680d1645401503071404a000c001590703004100320b45605040701d059030015207400c0c888000500202d03111040c07810505070144124030000900429a074030103080491010262170450b6851107440c5034024096440310404043c91500075a400d0099214070040700c4e6003000407441d01d0702c040390500d05401070400e000c000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 653322410 1250 653321160 653321167
    0x1020721030c050c0a060c1202071a130f080c160e16081b0706021303080d11070309090b030a02100909050108010615111006060302090906030c01020c33 67
    0x1120342502071010180d400b4500142002c4e0800f40003607551000b1700000d000180e90726141e171140c0303128515602c43c40c0c2130703a0020355a403090b41c60a000000d6040203a05000b00700000421042200c41804030086600201418556111520b40d03d969900061708800e5501c141580d44da0140c10345030264006041c0c0c0b880c811402c0c6041d43c1d41070f80d0400c4400d031280030006540d081180520390011490414041c035429940c0b00c801911f0138100a20408034003400031103404d40b000003044108802005962020101445480c1e00080060210b01480d01c006001c00d070600b2050107201c04075441101082401821074040c0030298000c90803820318036920600003076035020700307005200142c0070360341c01481e21000800507245050807400d1051880038110307041040f089501d01461000b0040e6a0215101e0b8604101c0d0655600b0041c009600c0342c01058052142035000030300c20326011510703504180068026001390b103656420820502184071076540704079502d0582c500e042d0601844129100c1070000b10320369 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 653323660 1250 653322410 653322473
    0xa0c0c09060302131b14071406061c0f1e0b0103050c1008090a020105220618140a1e0810050717040f0609031e0c0b06030c0604031103010207 62
    0xb0000342e40e01c04207410040401c1c0102d00103441c90300762006915081c8001b1513000603014251050081c060b0480b400304940c0d80743e40b400030503264000d440c1110710802c0220700c884e181c0c031000400382c005081c0440f580340c0180426414810170f5485000c80301c1e90320600c0c105079641281d0103400c2e002a5140d510052040340b01d801c10014001100c285400e0401084c90b1683d0f007030ba138400103200700904110020807071a8098411960a809450142ca880d044240d26100014064552400c000300e0319440580002031004450300f54500c208030160420540c0750804604814141782140b45041d42404201c0000f141031050103000074128803400081031900b04840c0c0200040d03000c050a5040c1007070385051000007070444e91803135050f6034800c1d004a101b806605055a170559004501d02c000b1601c4400c03504810380c003c000714040c905c070b8507000c50f03c0c3d15018245a07071000c12840013130b00030000304018800318082c0c082c0305e481040000c0004d13180ca40300d60359204000900d4405042c0e2034450001250 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 653324910 1250 653323660 653323669
    0x40302010c030b0a09020708160501090c060507050312090f10090209011d0403271e0927060e2415010807080403200d030b240a0c0c09060302 62
    0x7245034580c2c901480514044000503054000620600018650001d103007030030400c01405507003075985607003001e02204000c0d003040390203001140c40440342121000e00125019000754151401030703800c540110704102c14230495110030780c4041d00002c0c45204104070500c1c4001d04206440d107010900c58041000d0002c1c1c4180305010720181c0200d02501c02d80190316007940e403143e140640c0250585403201401440b0342d00d4801855003c0da8804285040d400d0100396045940304201004600b07503501a4141d0b503441e1080c080321051400c001c00b1140991000850800e060034610716a030044800043c041e400d00b144618000720f0f240c85001041c195040005190100055036910000902e10783c0001e41003140001d2112000520302c80c01e0000d08408a81814418200100c2c140700404200c00214901101c640e51408944036910010342441101703e8103044c0f40d14104595801c42508403240c030740103180b241a0381c00485420f0100814402c120340440d295000c0d041c0240a10700000034128114014407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 653326160 1250 653324910 653324921
    0xc0f0210061a0307090b0414010f030507021905011b0e01020f01020307170c21061e03070e04170403080a14070f02040b011211030114031903030b010903140604030201 73
    0x195006240c07400030815148980c41d060400201003850035900d99482406484400c01500581601c1070040b8021400030701180750000d4020007600c4100e0a000d450100714199a412a034071401600b00030002c004044202ea4640c00a074860000401c9000d035545075414407100b00040c0c0310001e1002d400984603540c050184c4006c81908000941c61352814403806400d0005040f09004090b83d00800214885440429100f4075000c84003080c0501c0003404030150034840940c0c403980b04425640c0c8100013001c010500c1d460b8034401802401c5854a000c0f10320381039a400a100752000c84d10400c0342019900000004c202851107a44d03038540721456190b0060450307640704c200f910441010040c800204800c4088441501d60494010503a200c80e800100da80010b00d5807424030482c1804a1600c10071411005541600d500900154405100004140e41c2d00c02c44099051502415008580440d101c1d0300150038040d018100820b01a40da56121507410301144082c8850760442011701c0f0405d0350a0085 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 653327410 1250 653326160 653326183
    0x2030d050904091e030e03210f120411040e03071e0c1208040306050c030c070212010e0a0b0a0507080705030403030c02011b050712080c0a03090c030f080a1202191b0203010c0f02 78
    0x9000c03008524451300100ca0102d04090256030020880d800b154200802b00c0300c0c021204503104c4401d0806103041445000455102403180e400d00718081c0340503000005035211a038202c800303c10f003151420a071002080401c07000355440e40341280080f42406040820a0110340705000aa540c3d0789141440011030310007500301041c0040030030501c020922010b06640d51648c04640c548500040c8207841030040c00340d0501782c003ca004041a05091001601c1610722442c01f40038144010381c0d42d5001101e2005086810802090050010401203486a403160104480341e0000042c01e4551501d80c00020510383c0c80d44002031400a5920b00308030705451441c800d0715150401205506002440d00071902615030141c04050355182c4050500000601500056030440000c1174010741609014940d41c6c00700300e48002040161003400d55080261081ba0404084040d00c070aa56280041c125400b400d4030b40700054540e4400c00c2c0c1d4025a0b400c0c850610844070340c0e242e4154401c041800a8289081c0307101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 653328660 1250 653327410 653327413
    0x6020f03120f06030708072d060503010308031e010905181b060c01020f03040809190303170603030c0d0306090b010905090f1305030406080609010b0702030d050904091e030e03 77
    0x14810001c19092215000141e41d04403403500ea07141d030042031500c84aa804209075100e080c0d4001041141c45552924405040b012800c40c0d0040008101c00e05078140f0031000040d8040004001007900400507503004151402f40c0c0e071010740d00f41c80710a0021401c0e0800d4202d01e68071070a2104c03c000c1040c81048120900c006070201d14211100384e40415010003600340940b8002640011440d029811540b82e0b10030380d82c040f03469007014100104940c200303c0695024078020720500910740701084040013101d40c503075149600c051803580d402603180c1c0058901a014403081c00000604102440700340341e9280c1e182e0f40040c903245048892402c4e1481905820705021110750280820303110a0718541d8800e0340350071024520f40700c0301d081d0354000e400040040d0150001140125031140d02c0800140254011206034060340d072680d004040512681c900250f15a000d4541a038000307004501402c40000020000503011405071901c42c803802017481c0040000098070140c00800d600044a001c0600c820340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 653329910 1250 653328660 653328667
    0x1030e1501180209041d06011e0612021c0b030c010e090a1a0a030f0b010b090d1506121b1215090f020d0303050603011b050d021804090c06020f03 64
    0x400308a08010b0244604101c0c0c1c0d00d0310075400040640440e55450381c0900208141001142040c01554144071243d00304d0190b580002804412510141005940c50501c030b401946054800d489001e01d8002c3d6210303044d024441c0743d00da00041d0402c08100b52003440d010440c640701400301400c002030020340311305124543d01c1d00169511050754840d4880c42134800000d0540800300d02c109005082d440d410350210300700e007022040000101c03620303803134a11405a0404590300c480c10f9920b5401664442c1d81c125174250f240c0400716984a0280f101c1e0303005c00100007800c41d01c0d0440c840481c50341c8a01a145004040807500c41c4040500f8800b0090660150074041c540a650f50400d540000302891849203403184240c10074030140c0d0032215800d680c024924a2091030b41d18003d4040e00b4100c03140c51080d440c1030400c1141e008030300c90040309140c6550b200b03881d0102103184500207401207800c03221410081403101e42261558403400a00d10300a101e1800c0840c50716400030300d03251300354241500c55041030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 653331160 1250 653329910 653329933
    0x12140603160f0b0d32060a1d0a0f15030201110102040b040b0705010e011515020c030d030c1412310305071401290a1503110d0c0e01030e 60
    0x1050036400e0f0781d0400e100a9544103800e1861014141000c0d01e890908083d803007000c9450200d0038160b01d0700e45c0810001800395034460810044440c2c40c400c001072080706c12440c00c00c2e45126490281d101e034150390b00003892034107141d91030216a03c06001c42c01e4005800c0f8144195030300318001403a20011003000f03618083c200704526649025620440103914030104114080000a400c411003500341e280c000c102175180015034880700c84136417003400f0300ba103141d0b800000d03514804907016410381e00190003414000c240041c114010706400b10070400b0030503c20003901a01411200030881c500c03482c0e0103481142041913001c1092111401c88035901212000304070810680c4100801d081fa425007055501c40746c4074140340c0c0d6503041c640c40e5041d140d460210341940b40030b8401040f91a003141c01c1c8004011001401c203101c4040c4050040104c04100601000030707003442600100180312031070240d5400d20300c3d203040c2c4009070380200c4409000b0a60580c1500c1d19541d05108880d0780e42e080400400484684 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 653332410 1250 653331160 653331179
    0x62809110112052214010f02071205030f070e0a0e0a020c010e0307050c0d15090507030b0a09020f0928020a020c1f231305040b10080f06011214060316 66
    0x1a00f50380c40780015619131902400b08010825440c001000000c0c042d544030080064029800b4600480b00100300c2c1c0c048040891007034040c1c07849420180c44029442e1103018064542c108d4605415034040800503020542d9411001e1a50141010400250316141064001c1c0e081d5072491030140e4580e8030030311419001c039000041e0000c5140060300e80240c45811400c1c403030415061903d45480241c108162241004000609031089a000d0a8180d80341d84660101c1e0055554031040a540038072104888011494941080d0703801c11942c01c7c002d05640c0040c1c86202d4040007a40392141802c2c0d010602c281349075014800403803480011640300181540b140034000007240010301c0d590070400c1d6504060804000b00ac0f401d03414050901e5640d8a8100c030f0503121030011094001e59004604120040400d8140001840da40e248140c03039a401da03564001100072000001440035041088a50007c00c80207803d119020041e8100e4a00500501c1c00343e041c54501403048a511007200b400c21030400502c102c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 653333660 1250 653332410 653332441
    0x90e0606011e030c020102160f03080a1811132c0c09010902090a0506040f081203090d0c080f0412030f0f090501140f1207081806280911011205 63
    0x2e480c1000114888000b104900a0181080014408004010010a0065055000812a2007a5180390341070b5109200f160a90742102d4007600303580b41c4040c070140090b00d5109400c0350301c400a40441044010140641c05640326144c0380f0050440c002c030110003c1c00d0007540d83c0800e014400007814500344290100326800414424a09101e138049004450365458000b150020180201200e807a6601c46507116080d216500c030f9203c140c40f03088003040100014005903407081c100007001e040320f124081c1051b03600700308402c030071240070104010200d0303003600000c06031002e00448450380a45001d58503014201c070503901580c01c01c0c05002a07621f414981c2c44030201054034400e01e00915485c500703121010f810f0140f0040c4001610001c45d055400d11110754140d8498034881d038460809807500c00150324000780e8222810095088500000c0d00480c481406202e0f01401c885082c0c1c06641c010000384c12503480c0541101e003110720080d08400b80d82d03c45c2101142c0c82c12103001304000c0c144414415400c0d0f0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 653334910 1250 653333660 653333717
    0x70f030807021501030b240604050d0215120f0f0f010515070204050408030601180f05060a0e09090a052a0909011103010806010f060503040209060409020301060807090e060601 77
    0x9009030001d07101038824465481c02540186000034156100c4ca05004008022100c01506404c140c100c3e9071420041000205000c1000e04054505420074040c401007054416045e07821034003100d049109011500010b050080200c071000410f03040044000d52001009000070085d05d800f6800d002a9404404002c0d045a8080b28000c801d440000c106218038012070b2406544203250008000900c04980b000303512900f02681e960484500c001d011f51401d84150003810f20781801305000b4401402c040e402003500d002ca60a28a15901c0c6100003d00100c0007100c070041c440e00300c0320003001000410442111402111040b110150301c06d82044c502005201080c2c900c030700f004a0100e483d101c402c0d4071040002109041d0280e5942c0c41c1d69001d5a908001e1041311101314801000081942c420344c16207006641c01004202552540c40800000e0090102d05a0385556030b14400545803800300038a2009000705070021600412405103641460720042005051181648924040c403e14445410640 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 653336160 1250 653334910 653334917
    0x60603041109041e0c0305070b040e0106080603010914010902090c0c0a0209131208070807050304110402071a010609030b0915060909071d090f12030105010c0602070507090b0312070f03 81
    0x2583c0c1d0b030900941d80d050042a0001c04d12044860300c040c0000b00c608031041d64000c01c211104160365118840c1a8400da1280c8030500440d140140b000600c82e02c051038000f20002c002180442c466110001c2c1c0c0c0c981c00100c801c49a40d640598000c50600d0003080381c0c450807480c85581040e1140c40069110032405c44003d100d4403008002604120347c507030307059130210f4112050f25180e034458000984480429540000891000d800181400c0e00c141d0450744550f621042035400c003144402400081c0d0443d0f0400c8845189200c20910440c2020180c4c3d0700820301691040030403031070340c180400c207001c0203004010150088840840c441c0c42004602e034020389c0650707070220156240c0c402c050a014058100034207805640d41e0f0401032001451629004030600c9064503c0c800080c151507503500c50042c0f40340142c02017030004100f03940c0030710144650036008aa01518247c0150748803800c08400d034103c1344a056590b840d60105003070411103080d0214007091600e150140075200e40b40a01ca1114004040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 653337410 1250 653336160 653336179
    0x30618020a210813030c080d021b131a100302071110050706050903071202030a02061f0825050d05030d0b131a01020c0312070b07090b040b0c060606030411 68
    0x88501401030b280c9000c2e081203000d500d814202ca808024103051348070685900d01d55100c08500b11202054000d40810380740c0041caa4a01a070108920450f008420658840e0000180180355041c1d800b805501441110009843c0d50070350741000310744800710340c038003041500c1440040d00007101c80210083c00302040324400101603000034221940d1142c03e4008207810300717204c1402100f50340003024106241c42038465082e0303003240200032a643c2c00740303074010300040e40890301080b03c0c82c15200441503034990345041100706540b0b840c1c0d22898600c8254220310840385603800d40500c0c82e01c07001c081c2d015042c21920305a8040340c0742c440030340e01c1c0505c080201030207a80c0c5d031221040750746100110640107101201403045802c4c0c103a4110050501050050150081402c841041e2a02060556800c803c00000c1801e01110303848010706000020403586c184000c002c004200403440c0740c05403005110505106603a05140c1901d00d0420501406071400344005000380310008009043c4899100c0069816250 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 653338660 1250 653337410 653337449
    0x21070809040902030a03030501030506011413050601030b04140612070b04140d02090901020d38061204080d0e030405010e04093e0d050a1b0b0f04030618020a 69
    0x9242410009625202d1714540808158058014074101c030300520580761180c3c0e8503004881c2010840000c1175106540760340a42c1022101e502c011380080c8185000691501e00300301044c1180c0381d01d4981240038082400b00101450700744d210455034a9204045c008141c0760840000160089024031600d1499182035820f00351203e03081420b00c1c60300100b460041c0e040a081c40c41c001c1d0300c401d09070f0f08458105540c8141241517550000d131450841c6800390181e22081c0c4501720000200c10000390303c5001003280d164050074285005002f5801104003542d03948807100c241e012142d03000d0035540f840d002404104501e1307801c109512017482c000e607004200c0d000c151524444055411401c0b0400b400200c11030b560030f611001c8020707480d0300b00c406490809000c145c03c100c1a0300000d0001002c55005e47c640b6000035050209140d04901c421020149040c0c4484010700550007064020043c080c01140070001d005039400b4210f040580d9440340b41c860304140d00480c60001300c6019017407420000c1902003d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 653339910 1250 653338660 653338669
    0x13021e0702030a170f0703121503030206060402160804080606030f0a1e0302030d0e01060501110a0f081309060e2203080117070e010902180a061706040e10060821070809 74
    0x200100104030380b0583d50740705c521f0040c085004600c076411001c6d151454490244100401410640b501600189619a03800c1c04010180d0f2110607034180f000503200c0008001580b41003d00083e14504026101c2860041c040c54a0551640c240615643c0001ea030580815546295110b110049c0b000030000f081103420240e26610450b042440d44038500625801e1070034040d41b02c442650710903039030b12a0743c4805100041e607484540b0000341c8085018400b501c0050f0014004112140d03c40040541080e84d5443d21811600107504c803550755503a8100f00440c161440402e0000400e10640c00403c5038103a48000740f19541c14050308023484459040d018003500f042141000401d081e100740d4015603142c80c00743c0d0103501310a4480d041c500407008030590a03d41142c001082e80c0315980c0310a0100c40d41d202041c41000e000c0c0105400558455151b2011642440000c8406200c0c07900415000c0c900346000b4503050007150600704c000051110140c146900c1d10803105281c4d004101d46482c1c1d54450b0015 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 653341160 1250 653339910 653339917
    0x100b0a0e06120f041202011a0d030e0307151209081b010227030607031103070f05040e040f051002030115360806131713030213021e0702030a17 63
    0x944020020410041400300042100703100b40d1103a17030551041445841d05a090701d44200e1507018a42403c1003001160403c1481c1c80300542c082d1500c0d54250102c80d0220f820160303150405401c50041c051282e001b16040b03034a50070500341c1090100084400f070f86134580c1c54054181091039241100003081e00c0715009406560582c1214150301640304040c2c000d18950000c8510218040d006650006030064000e03c16000303628400c59801c2e1944d0780d590406c03250524800d0312402403180c24080130a803008006a490310461203070b2910001d40c906428074a18019455440100c5140104014030013034107040c03c0e0340c62120403414000c01314501c240e05d112420110611009024001c01e412080459281c000081101e074000103031000d689400c1ea20100c24950408040d210181400004515540c4540105090103604200e000c1140d100c4e400a8807901e40702c8918840e03d03070045804101d60b40c000c140004403458050f02c007441d200d910303400700e17454551071107016040144401142e084030301c20380c044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 653342410 1250 653341160 653341177
    0x30203071103030a061d07210f11030618010f06030e0102121e0708010f050d05010b0a0602030910020a0c210501021306030606020610090203091207050d0206100b0a0e06 74
    0x10b6980fa4500710b460076004088038070600032940001c810000e024003a0103c0706008001d02c1c0c1e500c1d0106405801000b00600d13000000c40310311562204c200011040500c0350a401c540104081643ca090107003c001d15031002d03080f48400c8103030a00c0108502f95200c0180c0d0201c51050401050042e2a84040c0c0c1c028010891010040c151100401a407250040030041c03440d60300074507007030454490b0242101c9074182400744550480000780c0500c1903241c940f4084548a100f03c00100d54030343c4050128040b8403140d84075001503031011070240c460b0326007644c05050031000c500c002c103078112041e06d0700e00031000b092292120048003400035a1403032081c16800d506c040d4001009542d00d456000100348102c04900c03071400081d184c1040494100e02c081001c0780078143c814000c90456041c11034481c000e41c40604848170610444940f0f02c5080c910001030500306000b000500301030303040e240b006410118001c3c0f000344440903040060040f8a00b64054424080d00d0786498285c60380410081281c51042885 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 653343660 1250 653342410 653342413
    0xc030e06010323160b031005041a0406151202070206070c0b090405100b03040201080a1512050c03070b1206032a2b02010c02180403050307020f07050109060302030711 73
    0x100c2030209035482030107002211901c102c01403000712030f000e860b820f054a00d88458400f6140c2040380d40450000380d0f070018400c1c40d0702c0302c005076030304000b4007280d40d00301110000d5403408107001042d1506101e010018060b640c114200b080494034011f0441f2040744281c4030407a0b020501405540b213a0098408450340b184800d00c0c030a403240340003501a00100c0641d44200d0518001414060003952240200d030720550049055031255401980c800700c0c002c082d10341c041da0399012003e094240305a2074004001106814139180d0b21401d046003403503140c0d81c240e030181e88010401c01801e80d5440403521040300500b503003080da448980c0000c0c204070300340c190814560080005581c0e00d074103d00e14220046411070b610300d230400310900003040050300d05039044000400e0301407d40140d4010046400138520041c01c81840e02082514210a01000d85003a40040e00200401250036010000d000d400c1c12044000c054981c43e20000a000e0b0205000700d10030543c000c00840c2e201d07801009841441d0f0420720 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 653344910 1250 653343660 653343673
    0xd060e010806040507091e0e010b1513120b16030e0d2012031506091519020f030301090b1903031d0a08060411060f0c0a0c0608190c030e 60
    0x1c0c0c40c15601c400941e02a01c103405960000501e10a1501c6120170750030901c01c00550240d030311020100101403845541355103540312000310403650fa030980a00000c109100d070300317a02c1307130704114800024801035000480440390446980300404c0c803118440764802032140d80900c0b405032500045025006a41070359082d485250700c2141200c1d000f0750500d0b031505401501d03000544d0600f00c6103503521000c800d52514484100045204405000882c8124900142002d4981107900b0041a46802e103516009103d20020070700030a1030641100034518919980f0003801c0503441c0a8031b1540700e2106114412038180e50b1285080191989400c0565051032441d00c1e080e11592420040c00c8240144503885c41003d0381d071102101c91070040024016100344d000100071702c1d91107580d0107110724181141c00d544442c081c401c2d05401d0038140001c207008404400588120007071480c0203405a01203810010501120004002401c0a1000482e512058000703021600d421140011f500a00b203040301540d0900404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 653346160 1250 653344910 653344919
    0x8070221030702011d092a0313110d031b17071506050d05070302060901140316020d031404030f1b110a21110a0902030a0c02100b0a06050d060e01 64
    0x31015150320b5000380c03586030040441070030b10341515900e0010140e0058900e4046240c400c003040415000001003d850001e4004601c12240c041d00200c0381407144241000200741013212520300c1004040301680d030380000c41490359001c0c0c25020002907004560981113170380d405100ba5082c4400030302000d80e030040d40d01c10b000d05000c1f505885400c08420402c1c14004001110f0915030843c8840503000006030800e28115800c004880c4c4c4180001c0f41000300e000440d014409800c002180202c0c00b1840c1c480040c0780058010f820481494890800d05242c01008c0004031760711180c0aa11136458074101280c04440d200a80b0061300c420036200058660172052401c100c82682d10400c1d00e1403c44990b16259034560322081c1000b984100070010403002c00e03a4074005080c8280180c070750280204072a045545490030b071000c0760012504241c100e034031540902800b40d01401321040c0207050031400d1019100e0080403902d0f07003041d4410b40040010000d05001a10091ba0100003e49043e1078007000e0380d69039 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 653347410 1250 653346160 653346163
    0x20904090b010e040c14010c03081902040b0d060609060e0f01230705070b07051519090309140f091305010b0409030804120207030c0603020c10050403020102030a0b040b030a08070221 80
    0x48130115000301c42160f02141000710111341d85c49040c01690703a030040308081d81d412140018084e0416109130400100c09003110080d0020300043c02c1c00c540c050b40c690f80202d80e1001038686940c017020521403800380c20712101c0c0d8841505042c00d1400d8401c8060b0142c0c0e540100c07012082200200350004506d0405d41c0c03025415402000e00e140980100c2d400d2036107902c049045849144401041c60f0f0142c0190880101c0b2000d10952001c550f401000e685180c11103a41c0170341e0040c080071000107102c0d880600000e140480221001c100a82e45080700003406000301d07542d980e016003942d641203403041400d01000425001004e0102000d001886840824034000d800304070292001c80d84000c40c540b00c01c118a02c00249002200d8020b000035040c43e18103c0154025030000e0b044000c03600442c040e60898a42c40d001e0640079901c02d50005a40b4505442610211219510703194416824076414044950303000034286100354200030090365404040c40025807001c50407c01c422122550041ca103101c060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 653348660 1250 653347410 653347439
    0x80402330301090f020f0a030c112506022103270c011103032a280912030207180b15040311010302030f18030c10020712030501080709020904090b01 65
    0xd0f40c0828010344603100758120a90082d2401410100b005001c10618140319410000d00341d60b440c03c202c54942c440c04500d41c00c010060000d00304092140c291492507100307840000c8001c002a102500701c00b42d0704015203414421150204807100d1010001c02d00c541c040d004200c900e002034442419211101c2c203400c6446102d40e54901d400704e1031012084005400210440344156031a0a4030141442405590b039908407400807017640160b028003e4845201114040e4200340b84030b1120100c140c2c1401d0070041003880d02c2d4110300a038086400501c000030307800041e107205a50404001e42c0100d0001031a12000b0500d070725090303070700560284c00c41c41c68007081002403064a0140d0300000800b40110015026844182e4083c00492003810000d002a003000664001c3c040a03c0e0507249810400e41e00c0e28a0440aa1008036690b64009500020004c51144d0b0075400d4070113040601540d0f14003601161140c285100781d50b00310ba000030385542907550725486180481c1e07203d14400e0305540c440300034100307461 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 653349910 1250 653348660 653348669
    0xc1506090c1605251401050304080f1c020d05180304060f05030a09050307031d0a03124a04050114100509060403120809011a13060f080c0312040501080402330301 71
    0xd50443c14a405c0d944581c007268410307038102c1140c621300010701010145951081500112403a8a2501d02013440061700040a40c500d5900020880d410000da0140300c92090440f40701407a801000100115600442c0c90000181981072503038903542c0305002030001d02110b000003449800002422020550050a4052040300065240c075100c0311842c24422003507010301004d04006042000c01c1443c5110301074109140604a680030041005580707c540d41070382940c4140c048203031180040400010012400c81c401b0303021542400780d5490700c6a0040d5151200d1b854a0003400841c0c5040ca000d40038204580c80c516000e0501695103030749051144c41284501046400103a5001c04500151014000c4401003500b22205083c43e042e40000c11900d000402c5031030f101a41c4a000016560780c0c40740760a80140002400703041e80d003000d81c3c1003500305943c18020411107501800144087d99100c051140e000c0d50503a000811282c4404064600d101e54502c842c2c011000e01d03103e00c9030440d8032409141220b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 653351160 1250 653349910 653349929
    0x2180702011b03020307090b09010c0b04050f0d020a20031603030807030e01020c3007050622030c02060307030f0f0608010f02040e0a091103030c1506090c160525 71
    0x1540b50110168802900d190703002034020301e821b0107002c1284000702007a040c141401100c100709542d0343c00c072611007101c00351440d4001c8403120b4002c039402c1c44840310308209440070300f103c105540d40340003052410700701d80c8502145c840b4443c60180c404118040030f40d5500b866800c21160ba0340307001890700100302c41000c00203041a81c11807170794005000751107441e0410406031188032030080d0020b9012152506040040038807400c0c03184100d005100605c0158014009800d29107031150031240c0100081030441000c122415000c40800e901280ca1344902e5811100d8942e0307510303803035000c038007820410411200f104c0c81c206424828140503400b880448075040700a00000160190300d104034000ca00c00c1e03410f00e1000d04002140300d070301580012060342c45200714002a842c0350b070100345180c2100620302460f600007007402c10b9072941c120100d94803a00440d20f11026181207410203002d80540030040c0c4d4141c03101081074007000424441c03941c005043c03606243d00c000c0c0d12254124503800e68810035204 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 653352410 1250 653351160 653351201
    0x503030603070e0c03041b0f0905061c02030d0507050c040606021606022404080c010908040303121b05070c0e10030606090b0a051302070215030435070218070201 71
    0x981c80b40b003c483e1300c14601650390034250b0f901c90b01c40d0130b0b9040c0c548501d0400e09140e0200864503425040d82c5001824101c0400101c40c5001c1c4d003402034000041003121b010048075000500143d500041d44c0c10b1070400740c070700306441d000349140c0980307008070401d04940d0150800c032010480b40d60000d100c6451007034044800b031507141c2c0c4101c1a43c480040c0e081d550016030090782c104411026001582360094800d800d207515100346040303d142140d001c0902100c45000001d13041090503400a0700780380030300c4044402c00c81c1440010908121614802e225418000049408010310600d01880c000400182050810300d01c3c00c540016140703142800110790951400402103010340d69882062288030b009404c980e04503003071a0400a248030a41028000c142e020400d5800603100d400b1100d04032010b6103403894072401c1c9840d041400c1600860a82c070a105003411500002079810700500b154031505040c160740310a2400031640100200401100303829401c028004119415800350400c2d00c19050314444 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 653353660 1250 653352410 653352419
    0x1e0403210f1d040b0a030f0b091e0a03031802090a05180c0904030e12070603090c0501020a03021b0a03050102040b03061906170a0e2d01061a09030a050a050303060307 73
    0x141280342e180c1c00400d020701805500c03003d04159020104a89005103c003840b9542c9503900e0003d03140c4a80112410040070080c00b404aa007001360003021030141c1e41c24403407000060111550f810480401908140d2180b00e415004216150041006034024000501928001414001802c0141c0b007601c4070340d40500300542c09282c080f5600407a002c00030b245481c66165a20111200d800010900f980441c50140d8401a1101004810003d1807192000b14000d44641440c0c40b100400b68070040c195006520b55000107640818460501225050381a010f980908040303098543e075600002c1c5150710004002c984040b03400d001d10f104200071105440130800d4148524821109881402c020a0580403030b40d000c12401c480c810761141c00b1034400503265940030b9035145800b01070380302c05500075903c1c91141d203481c14500440a1b200304410090043e030303242490f40385000010150b10100c0040205640b0b02c0f656060003244007032078010081356108106410113039180c1e48161940d80c428400d1000024 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 653354910 1250 653353660 653353667
    0x90510050f070e031b06131202011709030a0810080a06060e13030f0815041b09090b0a05010302131d010e1614030a091b0f0801111e0403210f 62
    0x3c6603200041e018000b003000c0c1c48018062007901c0010607a1058007408a14042c0b00e10390381c004003e101021541410f81c0a0340000342c41c040b9091035101701c96803c80100b10190740000102ca60781d1405140c18103613135075000401e07101082070b44c201e01060b00035022074205104441e00600103886450390b801495444030700c0d60185041c06003100401180a003000d81a005000e41c0c0c1c504e500c214031300100984040024002000c031000d07042240c662101040001000d180d1059a04c4003900040b50108001440c14000401140040c802c1604040d000200c1c02c24005100030100c00429516220088400c212682120345000074021001540310103c001002c4003101c0c451044c54400790384985241c40030301d5604010982c0010030507010b45413030301e4500000466400403000c0c0c0144814500014a0500d41d44038140c0c80182e1003030300305a0408400b4400d0116100450700500300e003600c800031403582c5e803a00c00103d00031540054074104002c42c1e8100c20520f4069801c0c4000d202d651590b40b0714034952800d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 653356160 1250 653354910 653354927
    0xf031305210d0c0c03050a200a0e01290d021b0307080a14070203121305040e0616021f0624080406180b0907030c0b0304050a0b0a090510050f07 63
    0x200516031102c140c1111a60168043c109094040c1a1401d4050784a07200c1600d04901c00030101c1d420040782e074a00c074500205540802c01c481c0e0841d038031072141d071504810004882040c01209507140406220940c091401a02a000894103510761134603041300d04403800003034001198030020f042c0381401904003070901000b121605a884041141403a040b22800c031600d8040024000c0e00d07460811400016980400c020075501d84030301c41c5280c1c0c81e0340c50038489100040d282d000c0b0340241d06001c0c0301908004041001076000e0600049403040c42c0a81038102c0c41d060742d4807807604070141c10b540200340305100e40d009181500c1580c2120a00c91005569881d030070b44020a9000001e034001001c640051a95088194605540d41404000494507101c044923800d09440c0c0d01603552222004104000305070f0a400300810300c4d400380909500c1d1985405460305901d41d80209550b4843c0700140801c0d10342d0340002c00341038014084030000b104407451040140000e032280100c0d8480000003800d142d00c100c0c0031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 653357410 1250 653356160 653356219
    0x9060f010e190305160f1a220906050d0507171e060a1b230d0606080916030807060c0903080304082710180504140f010e0601090e06030f031305 63
    0x14245920b1600030740030303800419005e0031f402001082220300d0741800c0049840c1c025a00d1119902d080341d1805111380111400e55000a0040d0703000314082000c81d101264203400c982c1c910891010b4501446482803e0821203012a014104c26409145030400c00003940d900c2040d0fa2001085a1101c00406101c3c4601060f40c203c0000c4000030424500d0306d8002081d9844446103821505101444140340145d40c00703500f14400184146c41000000b4401304541001d42c50a00191200f00d404c50325294140d1003281c00c0540000d8840500b903c445114070741590013190011141c1d900d9040c54940742002e50320000a41c644442a076024040d040c05c00c0700802540700004103014100b11640401380ca42100a1600001c020401e100008180c1c4441c0180c480d01254040ea0f44903519241400420560040e00304401580f0003500304049641c100c5111004d451807400f652141c0d6a6120010346001010030703180e4500d000c00310f82500420000c82c207140507070303900312901741120307410021181c10f08542281 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 653358660 1250 653357410 653357429
    0x506010c020a1206060e131115030420100c060c0f02100f0e0a030c02090c030601050d2703110c090415020912150f1509060f010e19030516 61
    0x811148581c031000e10120f40c40341101041007a6a0034100e064080100d80e02c00040032400192000c2144403410401c040000f22200510890792403a009085d0000900041021101c2d80c00c4c1d20501603072a100d00004100100481c0c0c40844105008042806041040750440e040404a14a00e80a011032900c50f16032070b03005000403640e80c20300c5800b61206950000d0700b10368445088520003424000d00c84218081c2d155802205222720601c000b102000b04084261300042c41440502e0ba840303000c0312240d501c200000f0803008100c2072004c80da24030368a1142075481038054043d00300768001c0b0055003420100c2c0f042d940c8483d4900305111183c0230440d8020a054140d60410004400d00d81c040c1c541c81d070000d407200168221039400b1901d00859554141b2000000c1c408200e02c0001c04a1060341c020030007641c842e05100740d240400c9401c9405481d00348901d415041c0350f039180e403044c14101c219080051003601c00001c10f00c0c540d0384081940c0416603503070045d8034848085014080000b0304072100b600f17 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 653359910 1250 653358660 653358679
    0x90506090f0c0720010f0203030f04123509010902030a0f11030708011b112a18010510020a1a0606270a05040b011d13051006030506010c02 61
    0x200c550301090740100100540c4074203108010100c4c00d003e045140c0b0741048900000800304200000d00b605200c1030003041107610400030080025400610590482d9000030b10b101c2da200d07944d9068652000540c0000c03200c03001962400032000706110310303454440c049844110b40e85ca84070441400e9441050010b5015070001d40c000c400514100b2702150900d005020194024545600084c01c00358150f10290a9a4440700450301042d62035200304036040c001d06040d01c0800c04040c844e902c80d40c0d40040e0380c0e441100044000705c1950300c0d401100341000010025030800c140407810b29880d030340a016040c055a20046504403907070000a0210405030420180c100c1002d901010308040c910040505070008010b0151038054502c131418003150381d800c40305000c1100c2c025003d105200383d04d60300091090781040303014106640c001034002c2d0700c02d1042c44c100282007941c10102c1d558112103e4070050151900c410468001e038804019400e94075540c5d024003e94883c0d0004591440042d00c01a42c0f120400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 653361160 1250 653359910 653359921
    0x4201060c151d030c060108010c1e030e01060b120a141303090e040602030609100608071128030f0c0206090112140108011a03150c030408040b07031809050609 69
    0x94044001d850800000c51003941c81450010040d981c0700c1c540704036030b0011a803a952248180481409070011038002c00004070302d420020001012500e00301d18001d000c2e4050803400c2c1c42a084000d1040c9440c000340041da03520354642d00a6440309000b0007162980b07034085801c4036081c1c0955180d05040324180e081c03a840c0d030380100038101e52550086050140515000942000c41070445108900400d030040e2286001800c0c03010000c0b00602038411140e20010520140e0342003501079400c0b580515006c5120740c100074105180801040c550021040c0654500350300e058402040d078002d40c0300e50f4400500303903510b040541c0c0c5501070200081d4005002d2000c03a10a5106089100400303d42400114445912134a0032401190a801040d442d035124520b012000d8003414242e600f016081c0c006103001244945144041100609018181d2030000081418450594241e60180c80503502d9a96500005e280c05407140d000f120520200221145d4005011445c0d482820300c0744902800400c100d44d140d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 653362410 1250 653361160 653361173
    0x70f0b19140c010609060f0b0901120506240703090f1802030613091103070b1c05070507050f100b0618090408130909020306060301020a02070e0402034201060c 70
    0x24190000d81d8003005001c1041058802d025640c014007032403200050715820505a050301900a420015403410101304119180c1d90000111400311040c6600143c1502c070800054032401c0d230308030078428010f1807810406000302068001d0086c584a0384880502c9541c0d540003120f01c803040c0c8252882010b105d90310600700300c3e00e50001c41d40b200000f00040080101440e150042b1244000281c5010040c003803101a9820700304a41d10113031001e041010308280e0010006004000c2c0383c082428110703200e40129880500a205a0b01c18a47c0801912808040443d20a96540540d10807552141c140600350350326040100c21200c03003a54070004418000100c4c014013001202c050f0044518190400918014402e154050b1020b8007248202240002e698010180ba1403400ba00326486139204104289a9540020302002120440000110190350300d00000741010140d40704642e209466150f0105108281058a02d01c95200b801022120000389800c0500d03680c00d0040c240401e0710160300170041410f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 653363660 1250 653362410 653362427
    0x1b05010f0c0f05070e090c09060406052d060f0d061a0f090a090e0c212d060124020105010b090103110c0114040209130201050910030b09010305070f0b19 67
    0x960121003203180d5441d0100e0b00310317a0031a2040f13a140c00407003520700f803032a05c0400260405401c0740e051180038100b00010700040545d001031506451100c0c102400031140d10101c40d85600001c04142e101d0020251001a40c1e02500071400740e10b25000003c10b005800741448550408064055401d2072001d0090303541e5a804400019405041c415000032426014020086a00103e00c094200c0c100d504044c00f82d95070070b040c41689200300b03a82c0360010007000001c03000010b5003082580040d071036240c1c0105d1000000300e003280e01300c0e003e44400030640c030100c580c4c80030410540f04e071784020303040602a00302d080303617801c1c0221040300c0010820070641d0761007904031084a903c21105545480c02d03003d407290031158100e1400c5500c120039001c0106514045940a911040360080c42522640301d038002840c0388191402c9501c10450f00c581160850300c039501c031000030107025282c802c17030b1350316420415a240740b42c1c440c141024023203e00100340704851000b581d40000d0010350074110114916000d4a050780e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 653364910 1250 653363660 653363663
    0x70e070c060c030e0a12021203190c0c0c030b0402010801050f130c021e0114060604060c020418200906060c0619020f03070507020310090b04111c1b05010f0c0f 70
    0x5444c1c0c1c5a180e14040107100c0141c1003440b5100c408608401103202030700b044040040e60045d480103100300420340c030345620400c8000480990004030240075403410754000013101c002a01e0342360b8240c404010006410407041c080c9000b620341c589281e82c1c2d5010010002c11f80180e5503002107124420300c2168581b41c0080d00c0313403500f034015116010000c041d40800905059200815a9140c0013600003041d54014640c2d044002521801e10701414110040c0590000c104000d0095a40d00810850700e043c490032004c00d940e021800003c1c094000380482c1c2c1225180c107881d032141d1242008604246030003000c65990703850040103801d156803024101e103522502c0c080e50000b420340030064120208000c000562044645898545c0c0304c944c18010725207050760300c400000c000c0c0c1c640807064010520000249030b0190380a1f880740c5820074407801081030140501b07040904200c81d640400b0800140c2d106010440f1200c5000c144e02e80d03960801114484182c08864002c588000c120b0408101c80f18180141117 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 653366160 1250 653364910 653364917
    0xb310b072411040302150c0a030f03150b030a0605090121021f1107061701170109080a031a0301050c0a0f2c0301050a0c08010b071406040305030405070e070c060c 71
    0x18000c120344a0666288030000202c018000900b03000b146400c2000d9a5890342d4964a2800e1002c10407070160b41b070700111405414090218000c8810a00c250020178001040c151500780140d0341e01820450b0350019200100c01e6418441c2c0460142000d04804c0d04031001c04880c42c17540310601300d4807108500b20b0441682c02c0200a41044c115040c8a04034480c44030050741c03201c90003903102e8649410509150841820403018862091850b43c200d603010b0b0548480b401466284607844d0f09142c0181003101c00104409000300700c0118a982540c040c0724031817511800c041d00c030024401050f0803100e0445505180200a10401c038038a445070b071100d80c1c0099182895504400f00021000b24a01c1c0e1351440c0d01c408a408a07510b105040a0042c00d4216188910901c4818840f80300a49609414060032020300c4012951005001925200302100c0324071001b42e94550500d8240184541d10032074058550380719540700014540d9400071800e1281c4415950006c00b007400381d507440068181400c0761001c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 653367410 1250 653366160 653366213
    0x409050d23031e0108010c0804060b010203070b04030809010b0103090507120f0605010308031902131707030b01081c08071b06020403120f0e01020a0215130b310b07 72
    0x611079400154021608480305550540031100c1d035040220058201e4a000c0e41000c0d03401082c0741e0020601c0c0e803c6640404042007290741080101d01d14000c1182c05005d483d45603082c40245030304800f6803400b41d000c160080c4a009260030064080e200c01c00070040c910f40c44158104910800710742c01a071102d10440481c0c0b400015511000305982003a002929260310000512030000151041764018464000c003d50a0881c06044400708030140c2c881c0d41c0e142d240c00302c41105010001e020308009103038010fa4943c1d903961036032036581e526440303042c0c0c0d010384840c86c11840000c80e00a4840d03601c160390655400d80c0b025800400c1c18490a1030710800c80d41103800b800044001980e180a5500b8490b003691164000b94800ca4003d18101074080b23881c2c10b541100f0030100240c0c585004c01d241001d2511105d5a8031000020001d69001440d4002e042281000c1882c24003404071039042030420307088006005010046801d2598844001c2c41484075424040080100080c03105100142c0030002801d82c028 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 653368660 1250 653367410 653367467
    0xa081c020705070f0e0a06080c0405061c0506040209010b0301031707020103020715140604060b09090405070f030f03090b030c0403030309020d050d030b1309082d0406050406020105060409050d 84
    0xe0880f16400113107690150a40c00e000d80d43c02e00c030340f00d644150584402d105281c078090071503840764010440640145e880d070300091030030b44a4015242c07000b038042050480344d5046023002071701e0b4030f01038400300d21480c0c802000007840e05400c41aa81030303a80000c0e0040c4840d04800c903c0980d548290412414187c00303120540120b07160b24516044680010004902d4800c891403200351000b0003015a445140ba00c3d00a00c45c0c0c011032002d5954460064468040c03980f074901b4101e00e41107141d441140384620740e40010040101c0101501d140398800d4851110080c0c98034141d2615001c02c0740c0d80d041c013903018401040428442d0700262007090003d00303009801d10044c1c882c41c0c180b0107000034500100351508101d5649040991500b010701e5040007080084210380e59450065204404000214080c400198407802039020b64190210301d0ba070b02200c0c0e03601d5a07020003a201c0c0e0068030495016510301400a00e09081c01d000380840268040068009010103100c180c0310005000010020505d2141c072120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 653369910 1250 653368660 653368663
    0xc05010c0807030b04061a070f06060b1c0207120e0121020a0f020c090117070b0a081e0405060a15050406030c0932221a090a081c020705 60
    0x100189200e58507050703145018807015050f0764038410114080c500d0040b082254603004103588400800b1b541546e580d40c1802e0034082c2c00c02e440d10601800b61807810710005011420b10000b40300036000150020203000f0740000110407405a01c0740940303044902540070791050f1085504200800050400306110340a0744291000c000030740b00102c01d443c0d4000381e188402904006900006103083c4010921007a4401c08542075400620034100e11300081141c000c0300c60000c3c03207200007030300320000607c1c2c035030b400b80c000104440c105440301506500e40c0d40002d420841c146203072600c500d4220b030040c00c0d562075280301e0000900c281d102c0380032048a1a0400b20311680c0e5800340790015070084042440c60703403c04421f2401c99141481c508070b40f04d1907440c4840c4403110080e881c16111600354a101c9282d0300c079451441c1c400d0105ca40440c00a4028480c0703400c201e814180c1901400c0034900780e02e070030b030b403505030b95955200c13003c1d000752540f00305003c0300d040320b201d2290301b0510002031003026041420365a0f0300d6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 653371160 1250 653369910 653369921
    0x2030c0f0a020c0f12030f03071b200d0305071211070602060103060f0b030a030e040b091e0115020a0b09010b090412030c050f0409090f020913051207030503160c0501 73
    0x10050300020003c6060b45004240140809402c49031210301d140000c1d010340d660311a0b143c024080b008080009904140201145240303119034800c840000341080c40c03c1d2511240c4094006298840500030541da4145038441c402d0466140e2610780c980b5480b0384a40380c0d000706003160842040302041c3e6100e0110810302c4180c000348440c0c3c00400555045203401c0066840000725400b015182c01d6030305040d070f540040c81c02035103509424807408891164010a000c1e048514032181c000c100d41c001c0c0000d0001154084c120400614212921640c86a0700368507414001c074101c50040c0d200090100100b6508140707980c10070b101d80c00024403d40710b60701051682d41c00301c8056900c92101071044514a4050050f440140707118078101d07162845040d0340d10b000c3d024501440760a80e9603130910300204810301401845145d001843ca108610307084002802c40d032039140d0101ea0a010b5204050740d010700c541c09550301280e140d1526801c55aa18030b07214210b50003072040104021084c0d2038107000c103400f0b01c0758 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 653372410 1250 653371160 653371177
    0x20306041506021506062505030d0501060801051009150311040f0603240302010c030f0e030f010f0b0a05060702060703210c110f150603070306060e1e090307020402030c0f 75
    0x38002141d0598510111070300010302c600d0040204001010100300600c1120420b819507c0ea0210035a40c1424850328600400a01c20600c4d858080007003100794104041c6412110105d681075482c214045007156444104c0c400c03891342d60a10b034803c84805010f034212894200c0e14503402400e20369035004c40805042c840c4d004a000c01e82e03420481da0012001004146510210650b1f0386c1420301c4d50340024001c4620107809010010307004150020780344038840603c103191000b421501000a50161f2500030001580c3d0100c81ea0300c0c19031240054101411b115044034401015207007005225000d02030305071700c4003804504204c0f549034182485c1c600c18a44440981c3c04400004a8010100000d0810004c105d1028800d0f44440984410994001075504402c00c07080d40170103180d01e076107000c40d192403a103400040100e4200742e0007080604022094912558000c0c0c4900329094144003a03c40f2048107941c07120301034008200c0a005410541c0040d50002813500300580b406980003100c419a0300401039 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 653373660 1250 653372410 653372413
    0x90129060f19031d0706050d02072910120602090609090c04030b0612060a0b041d0109062d11040b19030c02160302010c020d06051807080115060302030604150602 71
    0x40c80080c0a40c9440b81101144c40300003c030141c141c1c9103032aaa924902880343c00d00304200025108a039000540580309a250b0018000c0480020701b614581c01840551600351000e0013040000c403004043d0964400311441c480c100d5840300903c3d11100d019500580485410010421a10601c3c0c0c40d81c00590344529820950141c440d415071074548080038000c0d10451044005c944603645c00c01d400b0070f0450704590100c4c1d002031145034030404200500f5a01151444860000c4240946580190010764420384142810000a038016032120303070590080c200c0c5643c01e05080144c408062681d800150001e07000d1613510b041c980d440e010f803107803507201445e201b038081c0c3d1005603980440d8041c040e40c208c0d0385080c0090207a6842407040c0c81c00a01c07061002a041104980100065440b049442d00100e50030510a01c0301d450003801040f20240201c001c944140b00b19080041c1000c010f219010b06442201600c000103454140110040e420103800c40c0d9001e0703a02c0d901071051003900c1030380e031001703100d10380 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 653374910 1250 653373660 653373697
    0xc041707150503040c0509060a030618060e01060b090105030a020d0203070c11010905010e0d030504050301090b0402030d21051503160501020d1416031107031109090129060f 76
    0x740100308480854040409200043c020f1100081c200c10101c2e06644c0203a5152245030f07213003030009a2100e2a94409404507207889242e10a40c4c120386c1e680e84119000f18000e01405450000d0a4200c40180c0f09001c5c4080d410301c91070110350b101e0b000647d00301c20910005401d015401304880201e0340150342060218881c1480740b02001600325504034400800d013850710b01d451500f00080e15034458000f4803842805809079030710070103001e5030a840c013809029008124840c034900d030a40200009540682c40b030b00c2202c5007049210301c51100c042d11507084d0f030604da182c4030901c00c0d04009030101420803582d9071b840c0845202c03951410080d59411522a60020614602d441c2c00039041900e0070948d2000c100014408031200c0668400f110482800d00f00d00a509000d1400c0440c3d00c001c0700b040c0307079000313000c1d200c000010b0003041003481c8040744045824200c15160f40348a1800c236440d4400381068171183c002c0c025003400c40242e144c4200280500280c0c6441104811000d5a50000384121540f2052a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 653376160 1250 653374910 653374919
    0x5040e0709030c06030c0f180315090507080a0f020d0311030a1d0604060c08070326070f0c0b0f1b0c01140a061a070609080d020703080901061202090c041707 69
    0x8070203c000401c1282402c1007054200000140303079644d035880c000140f041529010310b0440f00305035140011134020742c01201241516070454003601d503464040d82c0510443c000400c182d14045002200168017650060031b881d031035420f2203400e6040502c10781c140000985c980300b02003424001400b2000e059a038000300626040400d00c5410b0340008205c0c0500e2080c0020700c5040c1c0c00080c8400d400360001d031b01d60740b01c0019150441c1c50442c280618a04a0104000d40d000d0810342d41c0356078040e480b2602c4000715440300507822515103a68a001800c500189130214454201c5100d009800c210452000c0341c0404d1801b04043c06540910030840560f0b5654500d09804404940826081402e101080c04100d2805480c0c003c23444c44139241000c11a80041d44a00b0000c15a1042c2480c42c0d0084001e9140d0048001f640d0003904a00070640120b0541400200c01c00ca041c0700303100585000c203800301004d0001d038090100f100002080d1b9445503404201c049201080841c03440c16070300c1f042000340102401c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 653377410 1250 653376160 653376173
    0x30f0b04030f09082d030a12060b0f0d09050f0d0f0305090a030c08030703060504110405132f0f120403201f0b1e04060b03010e01120305040e070903 65
    0x412403031500700328504100348104a404220b482d0f01c0000d41c5081076075a94103d6561241c4041c020045010380f0002540207c441e400c40781943d2a00e040810401c051130307503500c0144c049e2141c1d1000050b00d0400f00b001030300c041036560000c050300740101d04981c180603068140341e00d08500030068502048041040c0c0c002c1c1e80d49401881d074082c0420002e040049040c5d40c001d08284003500c0c0003000d85802100107460070344250b005000415008205001c82e2101c124807104940c05801101c1c01a44a481202c103030f000310307000e08d11041007640c2d0703100c5140f0407420f0b81d0003203a00c00e050469040f050400454074002c4401000d0040ba21060052403e030303050a15024105031021301131840c01d28205090468410b90102e084003182e8210880c002c0822140210f000060122000780c6502088014020404801605000a243c0d10980c0d081211a84070982d50307485000034400c0c01c0c40e0444600044c001c103035800700b54155561103800e00740d0074642c903a0845903000d030f0f08840d44000071303909440400074801e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 653378660 1250 653377410 653377427
    0x324090b03010608030304080c2b030c0f091a0d0603060204140111030702011b0b0a0e0c010309021e0a030803010602030343050f040806100e10030b060a030f0b0403 72
    0xc11002000b0552030981c4d030540b81c1c00024000b0380860f5012542c10341e401028044a030410000e4080c050403072214240e40c8000f91039400403080028608005249880d000307441107120710400341c40d034482091400109059002181000809100c01840700d084840356a003d5207000e984204000750b1120300341001c4407801115400b2440c100440182c0300c52420b1008001c903500a0740a181065060343c0f82c80e11060138071407114004003128ac0740c40802c00c2032201a0300a201042038070040d1800c2502400044090380d079104006503118440328003400041480c000315001a00000d00004042d565940301c03900da5410913440074000d6040002005003501c1d81001c42e4034403620300c0351146045909105801c01014884084030044084542103011450050042e05d00046680c078031195555110183d56854107000d407507a1172040800240410706030109007407640b055100b0341d009100d00d0f00e03585606054103400340c19185c102c460b2072030110204d80480e4a0107100760041034170110502f0a454020114070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 653379910 1250 653378660 653378681
    0x9050a020f0304060b060f0f09010e151b010e03070516050405040b040201050a030b09010609050910060f0c080909010f061707091a1201140a08010b060a0f032409 71
    0x340304004101c00005944140d030340240e04034400055406010000c60000d100e9418145281040403d200122100f240c00506102d4000ea03602820b80013840f05004a02c082c9c1ea4100301c03483e2007480356189903034008250048a0220200118807814000140b42c1103a2154405032150f8000080b00101410340018820050605481c1000780e0f203400d8584a89034240a40028100302c8005404100c2620035040011942802450030009580d24203000d44a900e0070b01c80c090103591200c0024041e500c01c01035003801c65555403981200d120006c50200e070f030700100d40c0c1c0445a000085c0310381000b40e114404400e010789060701c4649032090a088000c1e008031015040b101c44440d25004024000f9480f070310f24412a105c0c41c0b40d080702106400003d020354064110308030034954080300001100c5000c00001500040290303100085591600145420385842c80c0302d00f500040c040180f410901d200c1d118a00001259150026441074560b54240200b0314030301500c4210001100c0c28000c0d4074003449909400c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 653381160 1250 653379910 653379931
    0x3080403260a1d130e0c010e0303180409030c050a050c01030e031e0a1704110906010f0206060118030501141b090a0b0717031305070509010302031527070905 69
    0x80802100402c0e084240b40500f503520061812034042d515000360701e00025480c0c80e414082c02a840214966880700313021458000f89850343c8018482c01e011040740c024218188482c620320803201d051001800481c40101d040262080a003000f1a1007441f0341e204040c400c2000d0210110104001016201e0170b4a01a9032500100414410b03403111520307400c0b03843e60b00f102c0300e9180c05000c201510042070343c2c0d00580f95402440208000c002c4d4000860b0795011085803e5031030388d01d45500444440c685a9081c00250b0700940110b54190b0041d00440b10440c0c01c0543d410364a5141c0e40d2301d134250b550158442c1c141d0300204007030119202c6011400341d0550041030a080c2454009000111070f8501da21804000384000500765060010bc01c0c0045901c82c44102c009650742440b141c90400d0845904080e00c140c003030b194021406180440f4010b04070380e00107005007514824507840e500301c1c0340c0c050001c5000b081d5200c0c100c03015043c00202180001c2c94400500b40540ca40348880c01650300040030003118 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 653382410 1250 653381160 653381167
    0x16060603031827060909050303010503070603110d09022b1515050108060a0902040b04030b06041e0203070c17280903170d050109021c060e150a0308040326 68
    0x9a02d015002070001220b621490310f4010042c140010080900b038003c0340209061054800078040c0000085040360015801c440b11159241c038100d003124080703450101c80d050300300900344000d8440c0d008660740c0f600007003400b44448401035090098407a240c0c050b03108800060b2007102030003c03900390b411329000c00042c14001400c0045004034048254024213050004507408184180c130360400304806840314400c110343d15500c0d00c648e030401d6005440211420441280040c07064241170140031855649420403440429845500d0700103508000c09050400c00304a6018000c42c0b189501d070151400ca10420b140c2d211000014a40300c00320300b041d003512032054400103540080c1c0c000c49850440342c001c2c442c2100c074a604092410b481c842e44603031406490034400080341203401580101040030441e0316850001046507103080a49410380718640b50b1040c8038000680641c00425082c0901c07030020301c8007030065181ea40c1c0c0400d9030416041a6920001e11000d110070000070f003030400a022031050003909 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 653383660 1250 653382410 653382419
    0x6090402090105010f0908030a0302041a040b03060d060e0d0906030b0420030606120a1e09050a140c0310020309060601020708070b180d030e0f0105070201120908160606030318 77
    0x41c50206108035410000c050004d0b5040620503040107003e03090700380980365607180034900140a9002401290409564a803207103500784052800c5800320303802012080d0031a9070b51410000c08540400080ea4055202d201c2940324520138000b4007032000c8203443d41c510705401c114000742102c40906102e4050f500e8410010f405241a03117a480d1861400400c040d036075a203030340219006004540c03104000ba4011028045d0a00703050304001e1a10080c0c4501d890910880000078041e100044009019600440c1805c000305080399190110083e4010403180d5960001000c00d25010240441301e19103030b404001d10561600500c221500104248024100310b41000c2c1030948556140c490f070b1403034010004100300c20148220586a00c40c0c1c004250402d2844541000b420414040c206030340300d01e1071815138002d158060000d4448440c3c040c9e40d21010000d80400d400300501d4103e1050300d4141e17050140c1921050728a1508020b588130700e00c081807071480c41c640500f480c5050841c0b0849481c01060911 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 653384910 1250 653383660 653383669
    0xe060d08090d02150a020105093702120f0a140c01081501121b090f0b0f070c0305060c070b01050f010819062c010f032f04061d06090402 60
    0x8809400071180d540340310b0164800a1440c1c0c1c2c0603810028603580101e10101080c2c0c0642c0100d10a11059060f0784080c24131420400d1291081c2d85c100600c050314003030340c03030b080421829000d450354030191800c0003403040840a03d24101092100700000c0e0303c0002500304200003050106180480e0070020407000740700300c001a081000081c0b820b03112480324005908241c0c03051001002c04c02a041c020000c80700b0b181c9407080710240d45034039800460180080012140802c42907041107034400c002d52814124002580e6200f136214003800c0d507075901c9408022000c50360030b0103424041da4075000c0b440d941d06980d03d019040340b003050707001a100343e2000b40900d20380d98100a0300c561029881c0c100d21025050000804000c095682000030410200348907403070485e0b0b6402480031002961403000440380c0ea10620408580d4840c08000c05c0940c0d0340403000c001c01c442220f403903829255030210110b02c3c560100441c3c00c4070910741c8240c1100f8084203003c501420401740381a002041962041480e00c2c103500401c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 653386160 1250 653384910 653384917
    0x405040e0304081528061d0417090402041a03010512030403110d0f050715030e010501120b041e034a01090801020315090105090108100f0b06130e060d08 67
    0x1010700ca50900060006012100030b401c1008095801c81480308a171580c1400800950050b03213050640c00700c03200605940c1502540c440c56011000c10380c402800c540025036904010b10b4560415001d0001050040070200e0b084103911402004a41701c0d803600c400c110b802140c0f1101010185c00804c07040c00882c451112075514010181c60109401c90b843c544042c64290082c000380c418000e0000100e4041d0035424040c110b24156541030011820740407016080f03030428814051a04000e40c911000240c00c904039582c001d001c1c0d240404e415174802c0c004801640358280440c00501001040144141400d000c0e0301400c2c0031700c2c4c900380100540003061500b101c613040012611040c12003d404568407e0600c08041d000d100000c2d500d0382026400c07200d046915844d220310407800d5000104807070510030041c1d81281c420b5001011401c0c06461000010100180d0300e1080c00e450f090101099181c41e0003d081c0f0015618110200501d428015421031001408451040b04446003140124030008240d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 653387410 1250 653386160 653386183
    0xc0703050c0a0f1a0f0f0a2d0c02100203041e050102211b010b040207080403021201020903030d05070905061207030c03021c0e0a021507200117041103010e030405040e030408 76
    0x759075203034000382c81c0002e9401502d26402c1b815a0000d81c90440760307803101c1421254448144045c005440d10580400c040c1c20301101385c000034a0b81a0a8009458001a411046a080d00680c0d03e090b8aa291a940c90742c404004e1070a45042458200070301c1d41d041181c804213024803524035013103240c040c0d0181028800c400f20740b0469012000501c0e8204400c0d0700c9108080b400810440d0348110740c2c07400d491150814032040e8419200c441c0544000001130003221500300c802805185801300810f0030700020140900914100458280b0200b103640b500401001041d07041e10342466a45801040182943c080b910203400b0140103015500c0c2d200342400d2405101c0d90201c4010800c095030511003840e190308280003960040721024154214240e41008014050007444644240e6005c488221000e40384800254002a4123004684001200303104064100d031181442d07505610113100000c5c00d5a00d5407400010540002404000516091281080c04900307a409503040608e40020127803030320982946c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 653388660 1250 653387410 653387459
    0x20606010c03050d15080a0203010b0d0b13050a020d111e06040b0a110109081308030a0801180b030a12022416021905060403080c12040210050c0703050c0a0f 69
    0x30039a228104c650088010f618150148100c21076841001541d82ea0200105a009500c2c15503031240c2418070b003c40048003500060300310600e450b440c050140c0ba542c1d80f5801d4429006030405080140d54640411725918041c11011801300c0030360040018008160042c425080080c0040d40003546035a030645040b1202000ba26841d44162001615800442d0003076600c107520b40422101000780e03440c003500d00303140305802881071151204490742d50f0303200d18041c00020408410041003001e03601e0b2018650001030020103e0100035010102e440c1451000c01110000e070a50030f5054010b5040000c103c05064040d445030f4040c030594950b801105014141c0313102e41042694440d0b04070b00800c0a28403045948125026280030b608189803104029501100000e5900010414421040d0103565900303003250171541841e00c8940c200404c0c24045840b00c0f0034424144194000900300380300d074400640c010405401227903402002c01c072003001179400104612040176018850b0800d80541c00f5042c1e403d000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 653389910 1250 653388660 653388667
    0x30a0b04020a090e191103042102060a0b130207060b15071a0a060b0d06030302070509090d0c03180801060305010e0a0302070611120d0b01110d0e090a0216030915020606010c0305 78
    0x341540c202d400c20389080c3c85410901b4070382802800d18011803186000310500d43e1451401c0c505c00b50801080d110300001644910301250244001d54004140b11100504400c006408002d02e4401c1e40c2000c0400e4840e5a5503000c0c020107400c21503000c45c0043d042e001e0305440c02c982d507580c40510b80b070300341d407141c2c0003c040f000010003090160b0f001c02c02400d02000d10755107584500280402030001030004034018000c07003400151074201041c242e4082c071038080140001c2101103004943d207004040098042007150f05840c0d0891281040e8400034191201c004200d00d41541007039400e44074102c02016060340101009004294007182090a9400c2d0346000402e0003c03000b011813402c5080c0520070503042c00081c1501849030550b00c0780c02600c5c002c0c1c9034617100d111106000b0782c84a507082d1030500812103080010446142c001d4089038441380350040103090002c044c60549040825890440210b41c00b0031080c001200c10081a80300480640700074140d0b07281a400003480d06459050060900c400403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 653391160 1250 653389910 653389921
    0xa080a02071a1e0f04150609050c1308030f09190b031603050906011a0a0210020a0507030917030f030406090b04110a0e1006200d05030a0b04020a090e 66
    0xd8049031a500d03000400b450081060100c203207000802602c0d1a50071550992544811800c0c0d501080d20490800420312003d0741c894079090400350510003880e0115585090118014041e40716a601419402c0c0030310351182d4021040300c034461030300c1c0c0003450340d0303802440343c7d00c82c409040c01151014a01910220325000605900702801e44840d000240400008001c00440e04940621044850413942d028041074480398900b0707880303280030b020b040d803000302c42e002805028040c0d4008040c01131661040300c803a47c11054020049801184014001402c0000d03c01c080c03650010500020740f91002c400d21001c02c07a07840c0755503244154100c80d20018000f200142c280400d95000308003858102c4280c54180c0340920700010060000c1e10690b2003000c81400c0860b042e655155558400c0d81028000f401f2503061143c1901d5003080b029035110203500044a180030110140600011400350342c46407034403820a100f03164141d90790511041e00551042c030a080c0b20543c800a5081181c051030700302e0304180c456 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 653392410 1250 653391160 653391181
    0x3060b0f0d1d010c2a020d020108060a030b01090504110a0f050114040b030a0f18020d110d08040810110903100c05190c02040b030a1713030b01060f091a0a08 69
    0x140c0b001411203500e091101c04c62617402040c09084204203175982c1403201512a0110844800710602940101c1910100d0380194016401c1ca07410690080400c1243c6907665120610182c01342c12001b030749600c81040c0030801c080810704529082e02211a040000e09146505149051601c5500e0403c03c5003029042442e510302d0444001c1c0c801002e42c4c0f552460a036240101802c0c0c420510050ba5241c002cac0a001070304074940b4070401c0ca078010400c49084103640c07200f40c0d810309950b14440c2d0294031801800006078885000f00014410180a8003043c0056040c01080740d82090f806014800100111241c558010441b420041e80581d40000c0341039060100711200d01802118400664400c0700e5211860b0300b01c1e89a1880e50304c03c48042c0403490a6400b07054403201401e8008040b04001c071762051341c3c40a0391010300540c1d1f403801020402e10781e82c0c2d2154414954280d00540100e2140503891364030a03482401c510240036a60108003800a407110403400340e02c01c4054282c2004842c402103000c60302c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 653393660 1250 653392410 653392451
    0x1080a11090a06030b010905010305360a0b09070503070f03031d100207031b050a0303110102160b040209130507090c05040f030b06090f040b1909060e03030703060b0f0d 74
    0xc0280801100e140c0b01c0318050000c1c5170064840340444c0d49000c0002e11036202e0300501c0d200304182a0014014900540801e01c8020780303141a504903001e205401056a400b00b1144284074007402030070695040032443c1c94100105904200c1c00780d00f2040d41030052440040410701100da0501d00001890f01c000455103024010342e13101540304150000c0d0454841d4006140300550b4001d000c02d807012411f0001e5000d004010340b2031240c01c0f214031042000424010210180c1c2c035540c1a0006d480c10040c00e01c0300405441c101d00481d03c4030501c84c148019130516401b12035000c051a01520b86e0b400254440d559202540d200b980c08054440c0c0321039007030301d2080b820386004012a001c401030503502c071724000b03903488070172161980522100c50004182245071403250b80925084824034005446441880d401d00100801c0601810744032030001002404d140b0500319130346081c1d00a10344905055100505440d00c90f44a400e4404041c048080b0003001d0300c040f960280c0d56500c2c0001d00e008956081c0c1f401e0b26 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 653394910 1250 653393660 653393677
    0x9030322050d0810060206090a031b080c01051e24011115010e1b0315010c02030a030c0611041a030703090803100315021c0b0a0b1c0e010b01080a11 65
    0x141090120400d90407002c0c3c02c0c020341c40511100c03030550b25004100d0360f0720700840300d42c1c101d544110300103408640190724182840040c0005907500000c03d0300c4810701175203d800c4440260b95900c1c2040245403003c80035404558041c03c102d02d050400c070000749403094444c1001d80744d02c2c1429210840c0c0c2d0780602c01c82100550140180c4115411500c42d8020a02091241080441e055030018040c41e44100c0d0347c21156809100503030075501c4503040c60b0240c50800d0183c9040c028007d102c0e9015030303801c004044000384a5139564071600700518000f0207407140b0b201070151100c020b10042c8005426500c0056469080c2600ca503180d58812000318090880c260000d40040b00c00001c0c0880c9898802c1c54006583c0103100100c0303604200074851003240703c0c80070480150714400400028410498100005460009044842680d00c421142d4a5580403101d8200401502c646201240c4c6060040d402404800e00c020003841552a0010b05000c01c020007501040f5680c104505104411105440c1c0780b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 653396160 1250 653394910 653394913
    0x20711090a02092106010f060807080a0609020d0c17100608131209030b010501050307050d0c031d03040501030e01020405090403051612080618091009030309061802180903032205 78
    0x100131442c0400c0b0f07124090200200c070f004410010820003400207101e0200c860795554120300e680c49290846400700c01800c80d0f007030191105800200c0081c940068070b808681c0745d10005a40d0414500075000c50504d51880440c040c0c00010041009100404401111400d0400e64280e98449140e07203151300c0102401007200041b10002494941d226090a040c0e034811070142200366240c10040d50640000c884020000d41e0400c40403070303885800c0e0840c0092000c1ca0402081205024018128113407548100c118140d0002c41c0401c815a403600504002c43c207010000c42c034207800d0502054840200810143c20b101b000190688101c1d50060840d81850304000d0541030f16905a000400110040c0d6000d4400c00c1c443d5000010545841c807464040e912324001481c00074001e03102403003c1c2c01ca0300f07400e405050703a5040e8280821038900880c00030000712040794030302c00101c1c41080401d50700741c0c407000903d140300010000c0706003000003140c0d045070314904001450030300070052000018415000515030b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 653397410 1250 653396160 653396179
    0x151823040225050f120a0c0302030c01060b0c100207020a0b09060d050a0c0e01050901081618090501050a08030310050d080409020c0606030d0c05061f12050a060f020711090a0209 78
    0x400c09082c200900244100203950003813030b050000550300c800400e2041c1104e1810800c6480160050340c50040091107401923906044c08451041d084485690000c050303224005991150303030303074140070321200201d0000c0118240302c050780101c0c0009990340500003035505c0c0044e00b41c141d540c440c81520100b140d1711101340041e10f0500400360140181c0814540880c02035501c070304c02507001740d003902c8a50806030b40e24051581c0b100c43c2c910300d090040311404240400c0e0b5944140102e10758032651701602c814100410154540020301810340c0c4564020f0040790418002e110988001103541702c1220001c5a0001d000d0080d810452824415075100112036480018103150b5040c01241c060b101c0d2108800751203007200088030581d043d844242c030085c0641c210f01c000844c000c90300c0380034105108940d5505d0241b030307444010070240b000032800d0594103035001c0301d070b11002c0007007a00a2070040d05040206505051140c0d9818800601c4844440d10031595000004e102c0841541500d098020052980701c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 653398660 1250 653397410 653397457
    0x6051309030e0d080306011d03010903020a0c0602070605030a050403030209090a150e16120605040e031c060506031303020a08160b06040515060d0603020a1518230402 73
    0x10840d805049000c62400100c0b1546482e080254a440c41e8001152914540d0350340d00465001318000e44155517032014103490a2591030910072102c1d4244240c004080340b150f0344c01c0c405103400309613010404550014205220855101d07055a40106140402089546491800341e0281c000e0010341600110410104001c82010b500b100d92070100310810500615140d0010080e061012144568190080b20761481c405100d650b4a0304003040989000440700e85803000681601c000ca18541e00640c004202034002c9030f01106c034001094241e0504010080c54400800c07041e00008040701002c03525a4072020034507000b07101105002d0b0b4000e1103641c0d40c0789081024200720300070840a84000144100184540c14184a014022400d14044650101204080041c0c55110204030540162a0400040140c8070080408062b00f0140150440307200a140000c0c40c1c41e5035039032803030729a00c0e030b1203801c205d0501e1034420505641c00d402c0301103200c0c0c2060707000f080107407003008013515081c81c4070840c84c2d9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 653399910 1250 653398660 653398699
    0x12140d091a070306062313090915020408120c0f06070201020c160b04050405040f17030412030903080604020d1410060201140114090627060f12031c0605 67
    0x301c4104003080090115140d0810850840d4014018a4007083d410aa480413654003212007030000d103030b201d81217880c0401d8102040c0c19444a03500180b40162a40820780412070112940700c44500e08110860600b460100e4103940d80d0200a0214185080088c202c0c06642c3c0c1401480c880c1c8103003100b11a154207000b84003c1c000d60044440711031a000d2949508400c0300100c03540003c9408100544c0e0030300341010100401802c0160080b140311622240e07842c0002c2c214144d504941035240140c503244e180c079091030605030030160f400300101450210000c0000f90494101a00460181c400507150b0007040031f07001c0100b03000340052540b04081403c000401c020303900c43c001074079015030003440301c0440e0b0268085005020300a0643c42c00b403614030a98281801c1c624070f82c0c0701070001c0640b261440e0f00d039001102e50729804105104c05401904001d000e0404103141d820701c038070035107203002c40f035a00d1000310340c5070b010380102210080c02c04030750205c420040e40c1080307028102c003c00c6420560109030189 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 653401160 1250 653399910 653399933
    0x706030b01050c1e060109140a0e011d0607080a09022206080a110a080309010f0513181a220b030f120d0e0a02010c02060a2003040608011212140d09 65
    0x609110384400440c034180e550007025080e141ca2448c03154107442d1800c602d8090b003c003020381c0c0c04030341d030b10351000103240c4104412140c106c0044010b070044d4184048024504103000302014121401d200304107005886165000c800e02c1302c84c280102c1c4810300f0030f4900000d4541503000d0002841041c0000042c494104008412048220b901184503581c0350101174032030084c43d11860204a61500c60040303240036000404036840c0d6a640b24410315210f201e40c0c8207540604d480781000990b2a41d461752907000402c1840d02c2001e00f181d00c0801e0801d41c2c40d0380401b02014100604041d41c64449105042d00e04104950100c1c50250a0b07a46c4100304034002c40a541204962590b001d003003107511101c0f0356011030f00c0420345406039102d070440481a020700c403041c2d000104c00000c1088647e01c40a80117240c0258912081d03051029550740ca107064001000150180c100070b0181c94034040c484001000f86030f84880b00b16080c05e01c40130705480c909040949001d009068201a81803100c001c0400c503d101c141c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 653402410 1250 653401160 653401213
    0x30102030115082a1c02040603020901031a1507050703020409080307120b030a06020703020f0106030c0906080102040b04030f080f0a080a0c080601021e24070e0603090706030b01050c 80
    0x2070701016554840d00120703404444850311030305402d81c18284060f003134a40040c07400705a080390010001c0e041c6400c000480c2c0c02944100d00280d03012030041c0d4a582e06014010340d030007102c03401c3c0341010f03c18800214191546400c0107840c2c4000a450701c10040140309000045400030000c0245420b5400c4c0782815510403500c1c500000c8072591030200b6a480e0348182c01c8038032005801082840604d0b541c1c100290301445065043d40b00c0c51001416012090103000003452240b0009689a4580281d400a56a840c0c01c41c8100740d006000038401d4a40100640b404c490300080c1c1c1d1500c1d005242484c0009114203510604000d00014010341c015800030749450207581c044038100f00012910b4011100c49406a503c0c0d030060b0403024000100f40c0c07090703d981750040030110980f160354142100404003401ea109010412034002001c11140d83c2c5c0180d01100351020954a0510b146484035000352100c54500420302850f030380e4100812107034840d40545038960500d808903080d066240d9142412500300185 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 653403660 1250 653402410 653402417
    0x30f060e072006060103092a17010204182307031b030b03030d0b011b030801180513080a02070504020c0c101b02010e03030f0a1106070315050d0f02030102030115 71
    0x2001c81076441e40d0341d06900c0040c0b48401800d4a9207030f0900440250400441c1607405255004c030340c000140c0c89006049000380d40442e14004a031409548420060090207503140e56481413104120304000c0c103407460030041810f42d0006201c14454070002070a12081c180304014010b000070440d0b0160103a01481700300005a02d20707916505204c3c4114140c4400b071a0454241c0c10500c032039890100942c00000b81d90360705040c82030308114004401c0709040e0384210290001110034004008a00c4070000304291f0511060042c00607140030141e0104c0694020401840300c900011440200e41c0700b84280302c040e010041080d513882199402c8140d8880c45401c0a6100d1030030b40242c4080316008040c2084080020010b0103852841c0c0c1e0015202e0780080c1130340c1a0075000070886181c1c090100002081b40505031303121107881050200c070320341c5800c500404500506161034007546c1c00e194888200811036000b2101844403419a240c1000a2001d20000039010340c0044004903006040e1f0441e440000d820740e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 653404910 1250 653403660 653403677
    0x204171018020a030303050a0b0619030f06080a03080403020c03030403230d080c0702010e091312021917090301110915070b1803160f142407030f060e07 67
    0x1c0d40c00d00d001000035031110110074104000fa0094004540c440840d038000643c8280030800304450f039002040082882c03403051010031181f500f40c495000c0006000304200102400e090030190749455094019003403184120000301050f2003007100028103007001d419651602d81e00d2410040d1040038076440307821548032801220f0811400200d8410012035136a4084254035481840c1480764000c0030b003603042042aa081c4241d0303440d45600075024103181c0007140200205410107002d40404180b041c411900440440d200204245110b20066904070b0103155929004a0340c1d00c04900c0745130382060301035082440c081c1030811140d0140c101d09000f5079001e20000380e00c10411060740300d8580010a070102c1000031500264500580740d9070603580b90112880c00c04030102076441102940c00841c1d00c18800100e2004020107205034140401c05034009200c1184c000e0600060041200f07030414544459100090750507120350072800c00d0303650030360003042215155101ca00d490481141d1040c013180c49030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 653406160 1250 653404910 653404931
    0x271c03020306090105060c010f140a0b0d0302030306090601090e04050d02070602010207021f14120106020d0327030207120605150a03120c110909010e1005070e0d020402041710 77
    0xd00032640704841c001d20000582e0308000c10090650414091481d0565850021070228401c2d403240d0703181800d150740e5a020034030b04410b213001941e401449035805440304901490010383c0000c1541d0f0015000c50707252101e81d442c0c000489000049501100030310105800b40f20a000c00414002071700c02807582560162510741d2400e0382030b841000c100a421180c2441031121101d1035620400500c007145c40c10200f0042010301c2004950808034448010700f03002001000016010404a80e03941002d040c14040c24030f01d07010250fa52000110002002080b201d04002094400d0040c403001e441c0d0400d078005030810500300440100021034540811400050000e4034920348040000d0840341c2c4001c0c00311074440400300407107007c1c041000c11035201b5091090100e5a940d0424418410320f0754000004607a107803425202d150650401d80741084900d0201030048665000c0190140300c41c3c1038504944900d02e83c0b022400901c908d03485924400c03900b09030042c0a0101264000040c0400740e820701118581 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 653407410 1250 653406160 653406167
    0x1005010b0405131b1e020a1a150909100e030f030c1629070903080d020a05070b04211103031803070c3b010e271c 50
    0xa008200402105000400982c40c01e528042030a007802d000c0130500790111028080790150300301c400c0c4007040f60502c48a036134a0040411041e040310358401080e50075080c0c0c403502452030b0558590095012980c00040e84050384c403103041c0802501070500c85080c40c0c5810a26111000305040355451418500c0c6035180741d81c00001d44a08040c1803440619540701e01c42c07840075981c0060101341c502c89614040b4004640c2001030310900c841c18810000100f09000c01d29a03a0440040c4094180080c100061021842500035a41c00341550a40160358500349102038a00d8016080024481e804407001c100070404d80700012034020709800409010001c20032429104820380d4039410312103510a00010340800c400e40441e83c00c20b20003400f0340b45000039644071503505035241c1c0c215003042c0103c610390400d4038a122186008a01490345040a0b1910300c805080d2801d1041c802c0004a22404010071100c025022001120001c1c8815523483c011480c02210b44495039680c0840724904840c04c281c2c0d08500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 653408660 1250 653407410 653407421
    0x15020604020303090d0c030506040606090606051c020306040609060315380a0314070f0501030207050309040518031606050a0b030a12140f07020f06040501170901180f0510 75
    0x207005024500706103903402800f08042c0041010303182e4001d980c0002002ca24140130181c010390261301e01003111420200002d040d144154441d004104c020040482c40c64804402022198582100541c0c2d1383c03140c0000801814090300281015850705000208016444079200c0040420300000e001c04606c60b041c00c498400b801c0750b0850b03c0380400007044404281c00034940c207800c10040800b000070340c0b01d032280b0b0700060038400016a030303600078501400b69158045101c0000c0409280662a040266a809899004c1e042c409400b940c3c40e480400c0060f82c0001c0d50456400140080340e4540c0b03103110007182c03090a0142c09a030658508000704d85281c0301405000800d240107001001c61011f02d43d150614040d99494243c2007020020740041031044460041c54400e201d1070116845503440c0c01004020b6a50701c0e4100d2140008010822850741c00040a107036513003004245031010381e150a0791034054404a003031101e02c0703c010964542084200b20b40c00315001d00030021580d0f00c5c060101111704484 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 653409910 1250 653408660 653408663
    0x20115090203040b0406090231060806131e02040e03120f060d0b1f0906060e030105100e0c0c0a081c0905031902070806010e072601030f0f0b0a0615020604 68
    0x844d81d90014010460383e80259003000c1c07000d00542c00e03400401d017100c2948606080b41c4407000483c00820604100d541c010340018180c50380250a2030300b8111480300c0f0160b0760350710040101060b0100001210701210032100310782d4006e8028424248043c16440c0c495105001303400994042c080400d12968071a0802440303828050035800100d0016100c505101c1e4004151514803891200660300c0e92126010140c02081602004a000f609040001d1b228040080545002c1c4c0c0c940410090803403d078140c00c0341110b89030503030408240c0b540308950000b44138042640c44039200e104242c20410200c54010500804103204a140c021101d24015080d1481c5400180c216802440700c2c2d00000b04544c0c0f82c80401d691381c011240036550b940c001a007041000d900000030001400c04104480d40c019050300c011285844c1d110341c6820940500448124041c08090108090750780c0c2d610400c02d01c640240059031301302c05c03040181d00e001d46401020700307060b0090702e00002100203000704017400003502c14040c6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 653411160 1250 653409910 653409923
    0xa12020c0102100e011d0f2514010207030c06120b0d211701080105011a12041106040306053d0b0d0603080c01150e0903030708190c02011509020304 65
    0x41c104040310f406000c6200302440503558490309160190081d1454201410030400505158940d12210f68240b034405140c54920079900616958209504c1c00c04006031200406240380300410000102e161800716040200f01c854400e00100391160081c00d92080d0080042060024080c001c05203c1c110000423001840c14a01a101c0c1d2400f8110a1843ca903d00c0303070b072900d0000743e0307012030701071146210a038002d4000765940d600500008401403070841100300f00001261810350014000005550001c101810300340f0a013000071440c0c0e440350101c0d401035400030030502550800c16002d02d80c21107245816104c0c0040000e00b9144c5900f812400360011149018031500645080701d1000541d00c040030350781a01c1e5039668040002846032010b040000c000c0c0c40009480c10b00100080008030540d0884103044403100c0400507218800021668001071926081055480d401003400406100c8224200203c0c20071994043c040da056004544819141c40700101da10307030710030002080b44815500038001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 653412410 1250 653411160 653411173
    0x30f03061e10030e010b100c150b09010e07261e090706030b150304120908060f070341010905070e311d070b0d09140601080a12020c0102 60
    0x18034029071102d072419403420000b00f190021b050014000000503c03029000c2000f50201d5000e020481340c1d0f01134200c0c0000703002c0280e4110b00002943c0c031a0b0522620011250410000e44251706c100e1a24080c081c14415105000b20800e1880b140c0003011500d018078014400800ca0081c98003061482c0940212005000c0c002c0c10003d00724090a4011344040c0c0017414512007900044003003001318410f6010b104074054111841c607000304540e4441d40510560350004050225051074000401e810060350300380020224040418009a4085000c1e480003220407800011581c050700361740e1880c0c844101200c802d181e0b0b218820f02017201c10543e000c0001524443c000c80c0342d0705101100e6000300c0600e1144650b4480c144403400050142c00d0411440c01d61905c500301100c5012022840780788001001401600d420310304416064098410603108040d00c3d06072410510400c0000144032a404105881c00c540e1030314445981c0c2c4622400403035030711441c1c83d4100c042500c086140000d00d03405078080d00a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 653413660 1250 653412410 653412439
    0x90b10051f0c08071a072d0207050a0603060503060a0204030c060503060f03070627030b070e010c121805040b01020a080f0c060f0405070503160608042f040501060c0b04021201020c030f03061e 84
    0x21112207400924055103e13270400411140c0ea01e4484074024006603601041117806c0800349070908401030b0803080711500500061000981c990741c840d040d2240f07840c00725180da44040000c2c140007481089180c150040050100d803e0343e1051403002c0d02548841985441c050200703103106207806510020700314847c99000300c2c1c07010b407160812024207101490035468855003034840d01c5c40c000006500002198210400780c00ca004420f030710344010300c0704441c1003020b002c003140081d4940b154100c000b0000000014102c0c0705101c44420b0b100c081e02c41c242240e1851400026400c81d80768252020344c1e8600c11000009011b1400145000272030100426603482d00303140c81c0c01507807003480c058011503101000002c040041b4030340f441000e10b940701c6600403004440c1c001c41404101d0350180c02c82c9003000300403000031011a01450030741c0d42169054414a46003101c4c0300840d402070244a03801e81640c00000ac58404e503d6006000c0c6000d0321086444072141c00b00c00317131468040004491000d4002256500b01d0740c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 653414910 1250 653413660 653413727
    0x1203020619020d02180a060c08160614070201090507061e08190e1b1909090503090d0b04060c0203160807020d0b13110402040e0f28090b10051f0c08071a07 68
    0x12b40c80b4801d010100f0341120588030140d080b0001c640e15001030303649540140a001040283d4001803181d400d00301c20755907200d559409510280d290f150140700d41e41300071a440c0c07400507003000000f015068041103000c01102c040e42d12007408403034002e501100c01c4851051445e080c5510202c1a500c2e101900f03006142282c1000036042100040e0303210302081c4003514654a5007213041490134400d0782803940c0d03450545021802c40301d0700980841198401e000300c1c480550054a424407070764125150640380c0b406480011180945040c004040012070380600050307003c00b881c4003403401d00c2807161034051804a01032000302d018512894290542da24040f922003880c1d4210241c104140c4101d0781d0b6049103421000d004030101030140d0400994038074004050000d5508240c0c0c01550b01500800014a4440041c0c182900212104c080e02c510100d0018050300808c2c09607100c0c2e42c003408031912410316050500d49120909283c51804007008002850640b0940000c00e000120030048018207031030b5107044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 653416160 1250 653414910 653414947
    0xc060f160807020402070f02120c0a3303020a0f021612110d03020c0a0e040c0312110d0509040b0603061302030c0f1605071203020619020d02180a060c08 67
    0x203454050041002c18056140c9000030700110b030082840c0c08203000c039841840600d900c0501d501e0b40b141c1050184100e155250070b50b200864180c01408403013000312558080c0c40042104003042c810b036000088070a80c41e00368002c0c1011140d10340350200b40601c416010790711400d803800e08251442d01c0f44001d00100b1003151500d1000c030700440c5071002042180002c6000403142080c144c003d64040f001c401e180d45800005140580741103016071006041c15a03813510500380c107000c02441d042e0b0840d450550f007441456481c030089a80404c40e080380100b01c3d4040d125078015041103018030f00300001140a82840300031240658070142c1101c0d01091103010f0007000b900081c14071424210301b0003841c4101d4003041d0140002002012800142c0c1c0d410f441c10707a11302003940d8806610045070700101d0010035004698075034000c44050000305000602802c0800030b10411450a00003417012031428400008501501c41e0f1a00985a11000c107031960001c0d9141040100300801080c400c024140b025a0a4a0b00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 653417266 1106 653416160 653416163
    0x2091003170c1c09080106090507020a02010e010509040903030f050906090604030810050a0602030c1b060f160b010b13052e090e0114030c060f16 64
    0x192665445044032102000c000440e02e4440c080d402d010420100466014501d29a015010040d1841d06240245469580380580206d4111001d00c42c1c280642c0b5039400130314901015500444042001700503a9041110a000c4035110352a2400b0301c2282500c01e840100c3c5600c4000c86000880d223000b44000d000d40e00c01c0090140003407000c035000390001c0d01440e150007503545001944800b0000c0381c1c070940e081003844a000644582c040007800481c424038040c0d6a124148000ca00200d9282c00c02031a4052010004030012038810b00c0100101c02040c40c80080c001c0c0280c40e40c60542c2001d0b4028944820001440070091003c050090044d12045414030050b4000c01c081d03941400140b10300303401025001c00d500d1030a500400c05100280702e5510040119130710b911100031070103070307421000b8028030130083d0701d02d05450060b00f511078034896005c00d17504060384a03140b5401156032040 = true := by decide +kernel

theorem cover : BRFrame.Cov 653237410 653417266 := by
  have h0 := BRFrame.cov_init 653237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 653237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 653237410 ≤ n) (h2 : n < 653417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
