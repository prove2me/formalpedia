-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0607
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:42:11.204976+00:00
-- url     : https://prove2.me/submissions/e996cb7b-53dc-470f-a5c3-f54e7d63040b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 108992805 ≤ n < 109172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 108994055 1250 108992805 108992809
    0x50702190812032502010e072c04020d060b0a0e041101030e06060f0427030c0b0609040b0f040f02060d0e073507080709020306012304140609 62
    0x194403080110031440c1458400e000c0c2010412940001507400c2c80890720b10309003801c051000c0440d41e41500c1d41c9440b40404100464800e400595103081e19004407005951684800304070103c094029003141081e08412100324104503c2d06402a500a00410861a00342c0c41c0c0c10058610301410b19045084110000303648013042d008a440349010f20030000c8040d005070001420307108000d0564516038007040c01c1c0318445c1d448054000c00d00604480008859151809500c100c0340d08150569110500e8170300c00090640082c0131642c0036100307507490ba400fa030f034510400a08180c1900d002c0e0210344050005444190003540c0304e900907004450381d00740c841e502c3d07000503003550100750302808554460500307442d080800c11459014106001c82111813202c41c46510b02e00c00441c0414900807224152121800201401084050000f007820703104c6007520f0384d22000c060740c002e0b22020700161201844010070801450303460f55a080704d001a030b14080c988504d0031500b0000b90728031640800308110a601903 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 108995305 1250 108994055 108994069
    0x303170709030503041d0a05042001030b0307060804030f020715030c170c0c0d050c0309010c0c0806010801020403110906030d03020c01110d0e0105070810030204090c0306090b060301050709030b0f0403050702 91
    0x402246c2c49038405404500d00c00003d098010340007400c25410281840b00041801c00030310820384d0302183c45021503002100403070240443c4074019401d03008191010401c15801005207101e580a03841e61907825500140c2282da60010341b02d112418400700f0b14003001c0500c2a005010810f41070f10b0001e80050642c10140d400c01e00c203445403014800c000031585103c1320140b2128100b00c00d681005403c2182c0d49180d1038591251441d6a070400c51860000d000300301c4a0310540010f4210300d82200d14035070312a41d07030500030760180c0415240701c8900d000e41c5003140b8051460a1040c0d502030080e1613408031584043c2d02075085082440c6203552078540c01d2900f46503c1e000b030020b80b0030311580402c00c090021080350071254041c003c4020042c50314100310b846002444c2100c01c076941540c1c00a07000c500303070400881603409030304024050740c2868003450601103010384490095100b200200710f507480322107080e1155141c61100500b4586c000c00001c0e003101200410540c028064100680341004503030000d149 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 108996555 1250 108995305 108995309
    0xc02090703091e12020d0206010b03100e090c010201051003020d02220f02070204060501050703090e0717090a0b150d030806130608060a140402090408030720010c080a06030317070903050304 83
    0xb039960100e0f031203010300406034018590381003940054041e85194640c02500d070320301409200c1600c94000003054001029112000c020000c005070160749040642c442a01c0c1c0070610003040c0190300302804103c407100311480384000c40e81e006000c81c4100d030040d42400744001c0c000074200c944101c8070040030803d43c03880c041c2040715151344000503600c0d401d61040000325021904114108101807140d0f000080d00041103c042c0e5940300c00b074043da940e501008a414201800480c1e60503c42c0e0824080340c8840018040c80d540e100722450310495560103103034410074001440342a0300580d0784c10002d02103801414802d03044000500408404010340381c100059640ea0b40c401c4c10b460b4806010411036010354030400030500110410200242802d030001410400041c20143c84d802000000c9141c041c052b5012031101d0341802c044010f0000c0c541c1c00340b8000c0007501c2d078a00120b80e603e00002e404804034460601540d5164480c1c0c64002030300031482016690003048201441400600840410300400c05440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 108997805 1250 108996555 108996593
    0x9050c03120409050a06050d30030b040b150307030209030111160b0a090c050913020a090506100201050c070f0201090b0f09010e060a080a050705070f0807051603030c0209070309 78
    0x60340d0792500e0f40d035204903000145400d11183c600307201442a503444905000c0300a030002c3d191102110030b40c101c40c408a1004600848400c12031450310100303030300350b0088859801c040303804211065210040c405080600c6089501407401040050740c4035000b039003c8c0415040142c0001001641c0c000d03140c48a0384069085a8040f8059200b84d0800c086920040c4c1c1c0103d071030200b409000500d035a823404581030f5024052182481100040c0000c00c6103001c80003040e001400030f02c400f9903904031900100026101e0a009001c0c030b000340402d540c01402848d014900e51140741d032030810b81da19440004400f018080341000f09107100000ca000c1000041c00030f4940030300b1402c0d540c0d08800009044507000c8403085020b4002030000f158a641c02140c050751164140002280303e42e96209c0448a51080040c000c1509a8440c2d80170288a50740c0c01512105104008642c031030003140e4060310319040244002000503150307070f10140050030100001d5400c800e8504010880040c0e0b56285500d00b0002d00c2c041c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 108999055 1250 108997805 108997807
    0x70c03051015080a0206070312050a0e070b040501050d0504020103060503030f0901030c3b030111120f0f0408070807060516080601050f04170a0203030408030a080907050a030609050c0312 82
    0x1185032007003881255008036510048144207071403e41081e894506091010303101d8a400304844040c54000c0303802140b40c054003201000a4030b080090600240280c4200300000e10a012020520342c41d148102c5040d03401c16182c080c10034000084110141c080100228100b6880360745c00601c0303880800180016032200f1940ba030300c80103c03100050459000a060508004064002e07238400c0b00c107045c802c0802c54411a901c2c400304800340070400365a01c01584160150701c1e1502c02000d45841d400a40a02e80038004001007a4440c00c2201d0261402034a04040d40b4038060040b070001848040200002ca100e20074640c2040d503592282000c9031400c8510080050502c1110b6800b00c3c3c0c0114160341c4040e0074209a4140702220a21900c540101d01482c188004c000c0500780d01d65404000111003164010201c075030720703500c82c3c0181c2d49a03049040040c010075111004644038240204502050702d6000c4c044803603061a5485000180c0034124040d2002c0c00b4440c022030b565203040c00b01c00b00c2d2000d00e130102 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 109000305 1250 108999055 108999073
    0x20a03030908010f02090603150f061c060506040602190321050105090a0509060a0e031b0d09120506040204020904022101080d080f04030c02030304170714010c0f031103070c0305 78
    0x80d6013076800024908100718410440d0b544560340326030030790703411650018040b01400b1002d408100d4409485401c0c50740b004010036221240d40c1c60340707200d00312003120320b20a102903540d0b502800a240503074000c41c8050b030449590701e59142d02c0f01100c0c0210902034500000658600f0500d1141c403900c612207200340b15156401407100c1d007444402c80390480380b428030800c130758030f400b8540079116200504544200c80d20b402c001e10484004005035007120349581889000420060ba4080d0740341d00c2480c0010216040d51f40c001085284446042c02c1d1580144c0a001a03944039400c1100951054480c1584a0307801d104960100710200308042c2c862045060500a41d41000e15081c0751107901c802c00c50800c943c8400700035455801c03120041d003065050812035252521440002d0441c01184c00ca4658a420304107a64003211002814804031503a1030400c9006080700401100c0008044178003500381d1030360054a100003481484d01038402c02109040d41c5c10854903645658603500c2a03070069a01d540480c01e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 109001555 1250 109000305 109000319
    0xa05040e06090f24060c01020904110708070b1003061e200d02030612032106040c020d0e0a08010c03140c090a0303121401080d18061b0609020a030309 66
    0x3299400940407180390540745004034410381e203201d00800381c0103120000211407000820f2a800749a4096008055946403203003100410b000f50405200c0510079410049880541301d0118104c2c0d941d507800507035840c90b0604545807005140c0c3e001d403584034a00d00d07800300000460940c0c0706003c00d2105031b0102c20009520024203a0070307268400752090b5284903050301c0d40c16869003c0101e40010b0b003a0711002d41c0b04c2d901d103400140c0720407001d44841d8803404005600c6080d0110414940c907004280c10004800352a03803000d000840d865008004050b03808180c0701e030300c800e002c0c0c0c402401c8000000c4c41c01001c135483e54403ca094907400e82ca004c0110f41c8950854414900180070190f00022016130b40c3d040890507000104003061034440981071200200804548000d44e402035841d0302c0302006688182d5035540c4129503140100503106000441016120301203034801e0b8608412100907694018041e5001e030a02c442440d10140100da44c0d50b40c2d246034900603200c5ea40e46900560181d150700304000d180c0f40e6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 109002805 1250 109001555 109001579
    0x506040c0b0a09120206041205030310091b1b0204020f09040506040e0c090703020712050301051003050403020c120a12020309010f02010902090708060607050a1110021609020715020a0504 82
    0x401c640039401401191001a031290b4281c0c00c60390a50509180000580082a100d01c00c0e81c0100355208044100b4400340040000110700030a44910124070090f51208a03004a0b1218601c20309041400c4154560003441024580214540d01c1800b0148010b590300180403644141c5582c00f590101081e071041628152040c035500c03134001e440a1003010410103d540d100e41e0b1201e41c0c0703807040200c4c41c0410181c92081c0e0540d1012580808068240d52003003a002d8a66002442401c0c41620042c1d500e1030301ca84203018490186616400030010940c40f4001c0041c048690009582d40d84038001c484000b14014286041000d00250080c41e650070340c3c0c0000611140183d000c21080d13a042641c82001030710340d80c0d045584021149001112500c07602e00244c11486401005030042c403400b010034007441300a090494002070708a81c080800d200030341041c7d854130050b074101541211110f408020101c201d0f0020909207100745045900d5501200c040313001c0b40c0005828034000344c070102d028480d01513014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 109004055 1250 109002805 109002809
    0x50a0e1507030e070f06031805070902090901050d0c0308090103020708040e011502070303020c040b060d090c0905090109230c09040309092912070f0909110d050a0308040c050901030506040c 83
    0x4084c2000700d0600c0c46a00195145200d08020150b6460405960300c00d20f840040b040c136404006d40d200d40d60384811450180d042880c20034458040320000050f0303031612074108503a050380310783d140c0303451031541d00c81407000d4002c808902e0606408002d40d20004990f44000c10160511240ba00440d504241103080c540b20385c80000d10655210b200c0c1400440c0d000107203840803810032500811051145000715086008404c42c0c80c0156042c80c20100130003e03403001240c152100c3d030400b001150b403100c540b00c3c20f0340c0094001070449a1b8010f64003680710540d40c910007030b090005041750711591500d40410341c419800c450640c0018444c0c0c030300f4000c01c8528020001042c5c502c00c0403e42036200ba0083c02c2d12488103100181c4070303988102d070804413100107101030401045401e2410398103075074034040e81026140000c070499002c601c3c1e4901c3d21403854018401151a9000343c0101100c04241d03500786d600d00c00180095540d0400c001700094a55030307034003040b4080d600c140050400d508007464625029403e42d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 109005305 1250 109004055 109004081
    0x2060d0f061a0f1e0708040902030a111309050c04030503030c071e020f060a021005180c040501060c0b041403031501020607021b0d2a03050d03150306050a0e150703 72
    0x70002400e841842c681a40c8641e0341d0a5211103a010441c0b0240c20715116181700241094030214000500000c070ba40a184120702e094014031100b0900740300d5203150301c0790545400b01807191900900c80b00c100c50307000b140c0c00110690200d01d4140c9944a0900d15001119030100da440c0000b40034041148116030700f4058011440f140d1540502d41c8e0026050f800d828192034001c2101181801e070350740c820010b926000c0c180b184100710a0030040e900b4502140c0d22074a54040d40714940141050341011711a250484020380d1310310001155555031105080300250061300d580500c07095440c2d01e110140000c50142440d00040440c07000c080002a041840c020085001e5411400442040e04903241001c1401c2134107e5880c440003ca6151240542000c4107204980301c0500c104000d407071100c1580300003501c3c001e0b41100c1c000c60f11000100c05407000c55180c41d80203411180d00f00000341c0c09821942d00820020000310340c410b103030345c2c0c0f8615108400340e045050084110a0000c41901441407032403424179 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 109006555 1250 109005305 109005307
    0x302150105030a080304060b13061508010308030606071403031512010207020108041b1d07032f1602030d031d030702091f0510212702060d0f061a 64
    0x50300c070020381c07070b60b0007000b0103040604000002001c10486501072980010001d1181c00c1071001010315000424290107602c4032004405500b03c440350046052038100c0780e00c281c166286d66a64801c0c007003990011101201c3e000c022619070b6501890510256100d003070f030301e104802418034600c100b000c01c00c81c00070183c1340c69104022240250342e012203a44c1d03005401130203e840c0c000410150401c003081700e6006200144072485480c029050b040342e620300a0015903424171080000c04940f40d41d8035411201c28525403c0c000135001c000c3c21031806021080c1030440d40f00007000355038020070f0508000d0036079400001d558a0100480c0082c2c41d011002c1d00c443c500085041c8601a8003080341400003510441011903400c91407003e030070603048905c01629001d00b051007618070401c0003805402d0400d080c03515080701c3d030701c00403a0580d5502c10420014011400c81000e88414007414403001c5920105a0b000303c0100550f031542c0c0f442d40101002080c40c0b9130005809440d114140603c0ca8010800d0313052400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 109007805 1250 109006555 109006559
    0x4050d12140f091905120a02030c01080f070806041506030b15040f030206031005030f03030a050619030b090723030f0105040305041701020405090c03090105090c150a12020f0703021501 81
    0xa0310100360340c981202030311340c20180e000480e540041021194007165220885403000d07000d05001103a800900b038420f80c00c4520404440006540001341100c05001c44d5410000060f419031260030900c1e0400320242001859070724880c0303401d101100c1500f060000c6078032600481e50a050000d403130200200100758581c1018188040164401694840030744126000b0000c00c5000c000f42c8007250082000804450034040c0c420303885030301e80d0403ca803441e8070945000c00103205030a0131142090044440703682d0041c0b0500316a680e0a0000010709841054400c0141c04681072014103407003141209c2011401d0305400c4a2002c0600d0212014918107050341040c0c01d00001a4201041e0380558004020301e902404181d083c0300e00a008940c03046500102c460140580b03941c0040046015294640080c4102d545180301c1c6a580c0072190b902507084140300e12405014040c3c400174008980d45442c1c035103041a403203030509059030488170303820000d1807000407100c1c1011707010810319110740e01164015071158 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 109009055 1250 109007805 109007827
    0x7020109051e010f3803062d0f0a060609050a1401020f0d0e090703181401090b1608010f0f0306090f080c010507081b04120804050d1214 60
    0x3400c1400c0070b5019041a0180c90074440300b03402240b120010704100f00041d5110b1242004044841c0f0000d0040f00e840c5000c0148100c5202202540c4d00d40203070080c800361b220a02540e00c166020310016007080d108501040e015010324242c940951000e8802c0d000d0b0303080c640048803c550065000c8802d1000031101004141c4506d00200101d4856111948800305044011b034185a0031342d02c100300600450340e40356503292b000b8040101644082e40c5000c815038540600340c044500052450702200e0300c60843c2c00c0000c480a0b103207164a440c0c01d001003043d90b003a80e61406403500984d50f001c140d40043e80d8295160380d03c0302102e401080780d00005c0186c01e10740b101c8201c00c80e19900015104903192510b40050014041c00320035020390241d41c1c20343e210401080329000b0201030701c1102c005852040400d10a003440101c550309a618007a1161400740760016940c04008110b40031070b6141410300002034560390340b04141c0140c50003850b180c4030310000300341c0c000e0124294079002c981c2285c2c1400740010721 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 109010305 1250 109009055 109009063
    0x628020d0815211501060503090c0d050309150c031803010c0f09120305090a0618090b0a1712070f06050c0f031603061a0a0306091a100e0a060c0b0702010905 69
    0xb28100383c45040703040c0c58580140c1062184100c0034008141e90f400014003542c01001188101c581c2800d90f0765100880080080c020701201b170203000d80c6d009100c0055189000846031460483e5145000e190410403101941160042800881580c201074140380c3c044c00d0a000e04420f00c01c0525000c100258072510150012145004584004518100c1c810416000e50112540038200030024101a640c44000500c606d00b000820f1405d80c1c15a18006602e9059000f41102c0f1a0001d040e00179403420003170a0030781c2e1114140b46155500c2121340c605050ba6040c0021b020413405051841c04203441400c04606880000c0e09810b0106020051010f0024011003980d4018082d11000401c9140081c4c044002d001250080e0b86c11101428029801e2941d04006085000054405100495640c5440300840c1c007500c0716441610300d0071512818603e01041c084104000c3c50030100b900c20742c9000402c00801082c0c00000101d0b16680107003081c014001c8140380c0c00b03c0300d4030090003000050354901d13807a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 109011555 1250 109010305 109010329
    0x90b1605160f06050f07032901051c090b01051816030c02010b090106021f060b0a0309050307241b0f030c02070503120d0b060406020c0628020d0815 65
    0x84401c5140064040280500742590401d4000c4428407090a1502110100507000d0ba00c10700401c2c40d00070720210b464007030106c0b04c030410076180d20b009a100e040e800550b000e40c880c201142e012314540031b0018141125224072034489015541c070724100e604240034003158103a000310f121052a041d00402076090110b441e00c038001c100360b20f4085a410340c0c2040c01d9001d00300c51441c603540000c1c2040045103042d030010b400802c440000400d400c0c10041d038428070301141d005006209480d80d0400c0060142c40c06034200c0303408940300e80122440c020312034584c00003220261506150041c0c0a00c40c04200400f1802180c070807080c04003c80000c030200700c1d03015284000443c500760501d9211308254500078024070000300103007400382c20749034110a880d8a81d05654049c907503685145103040482015400e10806403003d503022a0010310401880e0410042c003a00035002c80e50082540341d0514402009c1140e5801180f1200d0b00200701d048005100030780404001001124070001d0902c2c021070030342d01e88a607520 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 109012805 1250 109011555 109011577
    0x11070204150b270409050a11010c03080406020304110a0b190f1d0f0301020c070f080303060603010e06061b0309010906110c120c09040c0f050301051b130e010603090b1605 75
    0x10180194807010b01d43d141150500a51091130070b0600c005126011400e1220f5622901d0b000886480f80b40054031644400039010b40010302900c0000c0019500c1d42c019908540182400310b41035001ca8001040d001860304521036800000c2a000c5800c40300403459011104c4c6424810b00615407044020038824100745d202d400a4114001001130f92031381d4800070017800c0d01070002c0d542c035440d50803000d0b40c070b83e020320609200d6200d0050002e0791107408400d0300e01602000302400c1c5103074601104030941132400b50040e9031250003048031600250880e0310b11900c0380c41c120f01850303d512072500050b01a0105911020038400f10110030072501c100407e0583d1091811204407003206450380328103113480802c140058018100b00c080c003041c001c1154281044460070203005034110b880d1000d0600b62034080d9070580714280341c0f9510220016090010303020101c0b001c1801000d40399515080c01782840280d203c2070120303944200300b00500216003d800d51005640d00c1250310702d05030142c01010352051a101ea8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 109014055 1250 109012805 109012837
    0x40612020a0c02040f060f09020c060108010911090702070e010e04050c0f03120f0403020a030501090b0c070206042709030923030601150c06020a030b2d0f060d11070204150b 76
    0x40c4004170b44d540a840a042c80c1900c1e0040300340c50328046002588000754480b00e600c507010001485407070500410420795449010040c1c1c40c0901000e00855160241c0000c2c1980109280403950b803500c05080c138000c1c00d1428030f0080504150030141d0500204c64629401082e05180100e1300f5200000d0040b003111000f0900340d40e800e108011003486015a8000039400b101d0703241c0020074800c05401000c030301c900507501c880543c0c0316030101141d00d20032140700940000041c4020040141c50003419403d4100c1411015502c00880c0108030403550014002c80c04242c42d03034070500c814086140403032800c8180c0c0c00c06c80800300452001171380d91041423003403c5200903441110f10100348120342444280c2d6200c01c065485055520024025104910340703103005444038940c0e0f07103403010b40300201c0c0c98000082401c0e201c030384400c5d001d01c5103a914042c607268110400b0810810f800701d252107200c1036045201d20b62921092540704010a07280e0342c00100075803e07036604090101c9030314901101c412000b284451 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 109015305 1250 109014055 109014071
    0xc080d020c060901060504050906040c0302130209100c1101050403030507060203070201020c0a0c0303030c0503040b06040b030c0a090e0f070e0a0207030309060c0509040b10050a03051008010e03040612020a0c0204 93
    0x4001a10441901c10181e016000c14420400030542004040d110100e50500c959038500d90020760fa4081110090004040b0040030030244c01c000e112203801a00041015141040c50310100c1c5000002140c020001160344034840d051105c1d1040303600d0454401d2a01c20b01c3c0c6881e41c3c030b005125010701c01000d0a031a0f400000302d113009000b50304541c100740b014826074801c20720600340740c0b0517003005101c1030300880d050615542e80f040c030540480b0300c966030101448219440742000d220041c047d41d0700346601440b41e0f1204503c10307036420f00c040c0000c20740c444002c0b90400d500e0000ca801d04409100c030100c0c070b511581d0300380300032103900114942c00284124010307100e0301c06040840c0a41040603001c0d1a6518010306a1b600b070f5030060040a41c1da034240c2e000e0004002035014840048074110305480000c405000984200303120350061034000403204082440d823910348880e607085031214003480b08640d00c009800c008194004030410101c40003c9011420490041130103080c080e44050300900c02d551700c1c095 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 109016555 1250 109015305 109015327
    0x5060109062a0f030906020d0201110a030203040c0504151701020a0e0d0302120d14062202070804080d020616030b0906090c07060f050105010e1e010503130f0303020a0906030c0c08 79
    0x100b2503002e800c11406611800d0604002c0e1030b640c030900810340140034020b1a058a540140245035010008500b12031078003070141ca00314020741019004685182d400e10000035299614054000340b810080010350a00e0701d02001091200141d50907142c0d944d0052010348400381e0440c034440c4a04109980c074502c40e2100349412800c05611100740d2186150100b0f404001c0c08055001c02c030540b405030038004c100d84800341000b00000890b09110044004052007035000c2146402924169104d101120b0900381c4a070310080c1080002614000140d000004220301a00010014a085501414100048107920000c80c1d0302100c024503650080d4a84808a1250515031080350241a0002c04c2000445007903500318000e0302080c031640c0d0015240c201818103d1814040c0a080350b00180059004004204019940340e04000c000745d4882c4072071580e900101d143c2c0030950054610230b907401a074034140c004002c0c001c152590004c208040c681244c0d020101d410039040c032002c640048140f0f854201d001d071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 109017805 1250 109016555 109016627
    0x230610091d010302010f020613110d0f080a021e030a0f12090c0305061803090d0201090e1504051b0702090414070308090907051e0702030a0b0106080405010506010906 73
    0x201400c26245903015103502000240700300d5040e80d200345d07111003440742036902c02c0365112810348503200805408402d58001400c545845e1812030405400302441c80784c1c0d500d40f0b045034030106105442c0241c001078171000b41c1ea8140320914921070040e40d11080d4041d0381040550703034002c8010110031b0096021030383d442180282c113451140800d200081c001d0401ca850070503007034640341c442110244582000325a4031250103140b82110070f101c0e00191706000c2c40e0410013550000d0f551059041c000510804100000009101c92080071a414503520b03041682c410b010449500034555055805441c40c490940c080c080101c0701c2d43c2e038049590720400d40307030390401610844032451400000e00c1070450000410000d40040d00488404072400040f40e0b8a90000b905d403803207502c445840031405807824180110001d800b03421403900240481b101c1c10040c0d40c032101810301c20f030000404118020200010480c090050307c1d405330003840e000b0b01d55450301c2405000c48403c44040b00c0d41a032440c0174400c00c004054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 109019055 1250 109017805 109017809
    0x307020109200108060f01050a030b180702070e090318041508060a06090e0607020d181a030901150510030f0207061406130b01080103060905100c020c0423061009 71
    0x404031005049080c02e40c1402c02140d0760036010403240d50000750546000c4542e03c1740300c030040c1c403140e240031552141200141980030a060340030300d54420818032100d1514500d889068240c009140d003606041214035100c3c00140045181e5004104404038142c0b581c50150107508141c41c04500c1580170381d0100c00130015a084900c042c0314020400403c1d5400c0d41042045501008040100c40b0304580c0039902e8a0040f14142d01692080718121181031140c4848000344806000500300b540d11150b448010500c20244002c0200011041c4503500c0f030203104070801001d00010b050242807602c40442c181048601c0700074241b5555041441442840d501100c08155114000700604291044070412280c019107080b1b01480c1c00c023101030f00001c1c40f03102d840705415050711580794581c40e41e0783d40710241c01481002c0700c090040180624000415000351140c04d0025005000b814003110240302c100c81250f8500d207840c1266184410500b00e20390f00c0745420407400e403505442c1c1740f0784400540301d1210f19 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 109020305 1250 109019055 109019063
    0x1a090705011d120a08130609030b041115070606050111010c0806120304080609070f0503060103080d020f0408011503060e07060507080c070f0e01210809010f1b060e010c140d020307020109 82
    0x513945900c1000b600b5001046410010441c82001d0794a41600b100c0030702d180e000080c400400140401d02040c0103110080e15098001c09200d5011031205500c001a00320100881d02503880d010244100d41e0070031011080c0b04800c0c03000304083c5c540c0717100040c480c04010703100c180076811440711003104110500445000d48444400c44043e810040100f035550b041c13611458002203231000000c2010b1401080c0d5034122030300844c1c1107007402c240c02c41000095010a014a040840800c4001030920081c05080a65008111040009071540c14000c0680716002c00880450700050344c00d120b82c642020a6511958009107056268010400024a00582500440c00e444a03100c80082d0850b042440307241078400c0400c018202c021660482402020200c000130091103043c441c03c035031544103403940c100e90786513403070204003039007650f00c01c820000b4410005079649602c40b030000c11058824003070250312108524110f0207001150012008901a000344144029000404600707a1403007500244e4406e900 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 109021555 1250 109020305 109020313
    0x1303050409020c06060f150a05180a090b03010b030309030703030e040603060212010816150315090f2a0807051b060a0b03010506010804080d020706090f1a090705011d12 74
    0x105020f05945500480310303144624800084007800d81000000c0744d000310140c030030a505100950a0903200c40c0c0103003941c40b0041e2800c140066080d9681a8204003c8c07408190005406418205150031340e00c4000c24140294403c00c65554241c800040c2c00045035010b18003415121190400100a04290f0b40301034070050000c200c182c4410341e90141c9c14100c1c3c0300d400445100250720346130001c280f29288075400c90f004a526050011600071340141407241c5185800341452901c80f05030f80e003201c86807003030365003078954548031400e440010000070b15403c5242004450060f0303581c0d070010b01c0980010024000c11030301041488851030250071205400c2030f244159021031174010b84940045c0404040a8800d60a1502041c10707540105165030283c3d412245913031602c0b0350041d211001c0e600180c8200d030426030784e50b0f8003400300b8005080c112019100301880e104043c1007100c544c2d001817019000d4051500410b00800c0355a800840d10a0010109000703001d1040d001d00005412440c0450403600c1402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 109022805 1250 109021555 109021567
    0xd050f030a0801081603080414040e06090c0414090304150c0b0f040201080705090307050111150f06030c012105071b06061703070201021b0f0a090504170304020603130305040902 78
    0x18200b45050706903240641114000c0400060030003a40303010b484041c00f0498104814008032032026440c040e80080a07102041c80030125205500d0310b4030403903a4420f2038200d00c4021581d031819008158410300706600c02469401c01603940c030b40728480c40c401ca41c4140ca030412000e8203d0b00038050a8492608410451014a050442d0040c0c40e00c00300c030100d00181c40080001d00c1079004a0640e5030850019004080840c00c01c0700540b580384510115103010701c21001200d41410810f10380602ca01940c1400000030b00b4018241272030002c03181541814080080114074070712000041022001c6c19006000c1115110b80c1010f840d40300c40d0802d000d44640c6420003000038000c0a801074000c894a89034002000101154800e807a4000c51200034012b0300000c0600e40f020401100001c00541e00074041913521100c036000414000c402c0d0710084800d44c40b14208810f000401c4201d90000c108880705070310310b00d055400501c0d24400108095a0801c01009480a06100303101760340150103002e030300b1580c0341 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 109024055 1250 109022805 109022807
    0x301090911120d0f0804030c1b080d1115042a09020a0c030f0306150302030919050d0f0c03080c03041104052403031315030f1b1205040206090d050f030a 67
    0x40c1c1411014046044c2e440d840b080c1d544281c200c0e0784101d4043d42d84442d1300d441035680800114074004c041c81c114215500205171044240190b00a036030007a2510400310105c64201814520301d5250b0311140344a50041101240c0c0f080e0000c9048008002240f4255a030419403c180d101103400c800082c500c003180d2511080e400265124034907000b03403200d80c03406103010001c40903108a40106c2c0e081c40e000b00070202d1500d009030050f40c1c01400302070569412101307000d142d00044040d039900390343d1136010810b0344002c0d9402000d0444082c4207854111050308954030041c040a0020300b246403a4030002000805001c0c1c00c1c003030301c2155403000384103008a00f0402041d02c41c042c2c3c03180c1000b002a42460340002546400021260240c01024952182034a84005034900290f001d1481040c5600c0360950340e8110020b10400c0d444100166814580c2006940c5c000c2c031078441d41c40c000f034016281c5000c0c440541c0d924401d030b4003159001c07285440c200032103181c0f040c00c2c414074560540c42d0740b0020035907009071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 109025305 1250 109024055 109024063
    0x150507081e07061404080405010c0c032108090f0703030f020a050105010f1404020c0d050306190b07110609180604060e0405010c0e031603061a0603090c03071703030109091112 77
    0x1800f459040c81071009a01c0052240c10050304c000b44000020007040140754041c8206505050090756030303030302d01603690315400d00c0303400e070f022507100000070001c0702010312504180740300e0b00441018000d0840001c0303000f26680d030f82c40034080501801001010b510b09603100b00309142c121a030200c003d1040f035030b5501810000c41c0444c001c0c2c0b0103500e10340c40400d1850603e84255000300325000000c10540c4130070b80c010b0b03c1641c009418590401440c0100100041c2c10a50b03c8004108451086558228504210411880b019003c40c411a42080040c4440c0d80e0b401903054482d0800039694001e4a070100040c2c000c000c0e42d07000d0308404807401c2c104000d010040d480700700321000d1a182d07410410050030826403580c1c1c1c1da1b580c0c50f0303099444110900224059078840030403503111058108071100b0320400541c01c1d41007280d841c5240e6110400001c0c0302c1c00e00340b08410080641340c003a0840b248407594015160300050245244595031107030040140540328020110740a005441d140c2c1c0042c500742c1d81521 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 109026555 1250 109025305 109025317
    0x2304020c010c090f080d0801050f030106030203030309030a020606010309020d140304081b0306010803030c0f03070e120d030c05090d080c070504180507050d0f2907180e01150507081e 80
    0x4c0c500b00009280c0c0c50104803822003003115940e1140343c0c1e00300006c2090060703c051581d6019035840070040010b1324100011030050042c04015510b4046c0000020310380b50300103016031704160400030001c00507141e00080b0900d455000c10083c6110242885051448c000d44e4000b0405101e1000500806078540d0310031b80501006a041e650b1980e01c81c4500d55480c403064810401c0b02004000c0720f40d8014140780510381080301d41c90030124076100302000600410f402d4254001380d42000d009120b1640c6c02d88200303c47c40203070342001401c004003503000030113440c400c05010701642000211102c020800b40040c0b005030400030020021940368280c0c600541782c2590048440c0d109005000c51545840c0050201e0b01e41e00c0328480c0d00c00c01050342d03490400070095580f0755111001d0310070540e0310051001303043d02c964100e580d031003200342c0d8200c191460381c015070380f05000f94a00c4100500000c607203440107020324002d41c0ad0040d50303110140317021000c0c1d104103410300080e0788590b00c50701920790081c4010b000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 109027805 1250 109026555 109026569
    0x40911190f0b040e010501050a030209060a03020d140c031911030408030708090a05070b0f07020a08030c011107150c020a0b190b030118060506040f090c0e07092304020c010c09 77
    0x1c26a00d440c8804201d11a038010360b4154100140104030b59072150b4020305440729946030160400d0003003404130384a5003026000e074010076004640e00b11044028070950700d80d039000c80106c0c40a4140710040d00400d01c8068170080f21540c080d200074040d4521034020864080c40303508407660360700d003605204025810030790324000040d68034030220703d69090000e210351240303070041d01521945191030b0407410181e0207888004080a018007103140944c2d00c44681500030708482c4091030b52500e0000000303084038118005450014010310414003c1880d030301100c1c0c170030021204006681d59030018241e00c0e10404520003440003200310b0400c1200b4004610450704003040000c02d20070030a0010806007610166604500000d01000d180c40c007003541500101e0f00070030058400110703400406a024191200150103840b40381850008120140a0100c4140c1c800311614141350610300301030003c13401c0c4180b99038030301d1244085030841030b40b0750300c540c115040c01600b2002080707041541308002d06000001e02c00c00d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 109029055 1250 109027805 109027829
    0x4020c10140906010e010501051b0a110a052d0301021b0d02120415030b010509040606050301080c010c230115120308181e01090804030b01030c050f01080604091119 72
    0x103081203800041503416900001145c800903030800380116001e41080081004c80c0080c5204c40d1a949020b11404800600a4802c0c5803111a090b081c400101c1040c0c1c0554050083e65020b4200c050560a515807602c1180402c50350403803000000902a0044107060548156100801d660903900086d0340a594036180d02a40c160744404803403e0790758041d07131140c02800780302d01d140040102d210f0303403241400da6014100f00341001000e00208045411542042020800000c01070121303a10030400c0d06890301091078059010281a03603409002d440c040402da0a08404c810080083c1c4002e4000b01d403204051031852001980e500500d112500e580c25080e8042800722000c0317410b007020707949002d01c0d01c0d0201004140c010000ba20803142410603809414565503201080717070018402100070b00c0210b008106400c215411030404641c04100f40c3e003d18420000c800e1030340d405076007106440350701c03840484000803c0c2e070290406c101004805224661300c65541842442c2d01c034400c6050380241d4960501503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 109030305 1250 109029055 109029061
    0x10605030402010516020307081e16060e090a0b130b0907110615010905040504030905090702031312030512090d0219050a110a0b040b090f0f150904020c1014 69
    0x659151009450190003d1801c00003100c81c90100040c0d00c800c0761000d030444910740e540301d010030b0800a44000e2214070383c580741c3d19480c041c03404110505d654510800021061450060060030303941c0c0444207a070050f51400002038891210f9484042805000703001f24944426409110f002484410301d114400c0c90000d02080040707215006180b03170f0f03c45c07002c028001c50b12f50300078507808015640d141c1410000015008641d60700d560080d18041c0f4842c1d100d4141d00da05020400c80d0019008000c07208543c800d108094001e140c448182044a41c425024040c042003420210b4403881340e8410000030401c90414004900e000154144640059038240c0700712510003080005401c0241030094a031703500031502c68010039000d240d80e02c095100142901d411680c6d403050141643c0007940710030310620011a03002c1c2c8904200c0781285102c0390403034800c5481003003000000c0101010b400e05201c0c0c2d01c004600c1d100e203071f25030340e0403a11440402d40480e8405805070410b48060800b03040f04402641c050300c08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 109031555 1250 109030305 109030307
    0x20c010f171807051c050106121703100302040e0c03010c110307020609030a0b0405240118050a02090a0e01170a05070902030717010303020c1e0616060905150a050106 73
    0x300041e80145032000c0e54440e11400d4902600829441da02002802103501c000f580b0744d02d40140d442c1540e00e2454075901203480742445401c64140c0d910a0104c0002c0612080005801144c8011141c0200d44996200c0e103d006088070110300030781009404c24034201c140940b00400140115409404030028044151541c604580c5003d040e0f880c2c035400e41c000d0003a03c0061a04c400039000e0104090221209a1903035200c0043e040411740b070980c0e0036040741c0c51010300505d00c9005d1034800d1101080c052103d52404403003030303e24101c80403001c01c1c01d030b900c10114041030082e80495556620050504007855280c1e41c04081d034a0080c070036248148a410b20041c40d4010200e1030f034103e50b411401a011180c0741498070030280d40003e081c50100116103070500c0c007e01c3c42c61170484c0078600a500505d4540000028010440030004040208800e0202c0b002d900d03075503000c22074a2410117800d0b051440240d6107002c5014200310a0020a98010310310745d25851040381e113001d8426410180203006c1039076901c01c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 109032805 1250 109031555 109031567
    0x13050c011409040506180c031006020604020109170a150b1e060301030305070602070609150c0305010807050f0315090109122a0f12030e011a0a03032607020c010f 71
    0x4009125000e0030b1018114600d40740d44000c3c2d104602a0580440c2d03d03084030000d45041c0b080f0361450840707130040f09124440c11824030203c0506081d000810f00342c02c4c90f40018003200da162040c10041d5a18150135600b081050000008080c1d000d00c7c070100c00d102141c1828060801f1110890041d009520642d200c82440d0003070b044828405044c107032545c4d0854401310f0304d99200200603160345808001804c001100c034440d64603414051030b50b03500300a400794602c6056507030403002c91042508200040c40b9100002c01c5010481d03000b00c0301c2102c1624014082810036560702003101c61001d65808101540e10107400c030300911071013215258602c410449042d2840040ca96160b2080004600c2008089061240c505401d070b0141c0c01d00690200d00b41e170764204040c0780090f80300009440350428450403100b4007038000c20514030050390240c07202610200d172500100340f1001c2d040040c0100380c2d444401c80c00e00c403401c0300070a1241c071001c10300d40000084c0d038803c1c07900f05045c0000e19500c08560f005220318 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 109034055 1250 109032805 109032827
    0x180105070f0b10031703070909021806160503030112050c03060f0a09030504080a05010f0e01020702150a1803051507030b0102030315060408070e040618030807030509011413050c01 79
    0x51501281c61840e161080c610a0082c04411a4401c1c010b002c40816000c182030215074880209150356490b08010060000c0d000c0d0344055049070040c0140c409403030f5070040421480806549190b10b5003c403401000610200e1034000c0e240340000400450314000d001500d140250042e000c0741c0221506806166a030740381100e04000300020040483c881060710307000124424003c1c50403505107a05e0b04441c2e8104004403808503540da54400c802600c1510b24040c00058030440d01c000c50811049401090301d1032602070324030352030540000b02c2d0307064103004000600f0150181880052400c4d240d2170815035484109000c00c82c240808000a42c0f0640b0a016110968406901541c10742e1105042c1510740c1024184a41d84548140b03c0410201d80400008006210f0f20115001c1803d007404e01c03800711030300c0107070902510440910200c00329030407551917600015203140008555a0700f00813940180604000001100c03030300c1c0103008050f5041583c03425083d0290041d1081805858019510030b8810 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 109035305 1250 109034055 109034063
    0x1002060403180b0c1f0606020a0803060d05011e0f06031a0604090b070906180f0e19020a05030a0b370e040501060815061c032318010507 60
    0x8a800640040d00c5200c1c9000700180000d84921500c1e150818061250084032a2840c00e600600c0132040070740083c020103120f415910070401c403080c10322000a403a6250a1005081c85c0320010201d555502c1d02c40d0000c980c80d800c800200714513401c4684a03000d01b07120782c000d0f0001d01e040607035403903140400b480b038a070480743e000c018100014601c6c0307560b81c045500141802d46c013031b5640c8840800b003095401c4030340c45680c45541d00701d019420031001a0002c0c60105102284400860b024056000303001c0c003080a4680c80c48010415030382da0724a0f60380d2001c520f91941303031060003c21811907654112001c0c42c00307092000014003001c104441801100b88511548000c160490110345424000c3c0c01c8001410300f46259500c031050b5118200c10920990075942222240c1d5038500410000c00144021034200300080c02181c41d5040010004a01203442c1c040c030302481208103e204101405032101400e00f80c90b04991030781481480c01d00c0c61a5801c0010503221040e90325100c541f40798403400880d114640c0c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 109036555 1250 109035305 109035313
    0x112050c04090e0f1506011404140105030402120a060204060908030306030c010809010b03011b090b1204021504050d03030501150c0f0605042301020c010c0305010501050a0c0c090608030304111002 86
    0x14068126015010448180010340201c0f000b416400c00140101c400765003401c58004071701e0601d040010030740b1005c10783d5003016a900344800d02a40310359140064101c102443c4c01c03502e27074480d03000260480704030b110f54a16070303c04d0340320f1041006820f030058021100f80c0e4448107402541d90024980324401101c4042c2c0c59005200c03481301c43e41c0a500500d40100082c030001a00782c00310000309003120b8001c6c054017503203440010703010034966001e010b8070090000a540e0b0360074100c504504440008024000910a002d15804074907400792240c10340c0c0041400602c0a401e0b1929401d010303004000030300508601058101c92440c83e1801021810420f0b07621401c03852810102c2d864480c000c2c400604129100d003860107a8502d00d40300c250f0461004040000010303500c0c080f41303880c103084030040c1071704c00285402d101c0100850b0380c001080e00d80c214000d04103204070000610b000110285c40c0c2d0010481d607460b0900100700c8101c004055403245100b09100b46100d00520100f00207072494507074210050740 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 109037805 1250 109036555 109036559
    0x1060f080619060504060f0312020705030d050901020a08030126030a0210091118090c090402090105040903030b15070605100e010308160203100207020316082505030a0308060112050c04 81
    0x310b07a030b684540484440e800050072501d407800181580c4995002001000540c0c00c03d00a000001c83d14000000c054002800903a00e403002294503101c5a030341c2d5100348140843c3d200540d0b4000c2c0410100564041c1d40c96039250b8451340c04450804440a0b02e04000e83d0302c3c190502c8500b000422643c80c0d440940041c00041c5040d500c18000d8640e003031085905103078019510b1060740341c01821001588910320341001074078118010b1031808265001461280080c4428003015031a6401c0e140e0540d03406580101e000c0125040950292039201c1000340c00412072511030348040681400b03015a00e1003440c0620041c0c40300c0044c40c1491600d4020142c155042e8001040043c0c0440004e003c58500c3c1d5510708800324a9400003420158520007143c00e140d00090590300f10b260034080c003010a0b0305191011080c6013403000d40d030b40d6100851900f250715410a592208241030711000724004080c000c0c00c41b0f2010f1510301c0c006026402c10341c0c0650110341041484012600e05000740c03803040001400c030506083c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 109039055 1250 109037805 109037821
    0x70f140c030d0c0c15021603050c01150e070207080f06150a0b03010906030213020307080408090a030510060608010b0f0f091c0f05071226040b040e070201060f0806 72
    0x2500c082030480c4188000c1200452602d800d000741d4040000e16141c0341220066814210307403011080c0441c0703000602c1040480c2d551000318000440080d0145001d42d110040d03511580e00421002d10518481c001c1a000003410746500c80399248202e1184e400d486005030740da000b0542c2c0d07491800d201c0003580c00000009447c0c022400d20700d001c40e80e00400c0044210b40d1b40e6081c1049030b0007a04250340c0142c5445042c000d500300b801d200229400483c0d821840c510702554000c140007005440101403880c0011101d8080e40c403a08240044c60f0000142c800003481056010b000b00010721030103000c103c12500020301003199605458802c01107110080c9003240f2285801c1c20780c0c0c4140c0c0314a500103050842c2008110f6140305140500c0e2041c07450703141f0b84900b41092898120164064440c202c154003800c00042d1102088405039035000309020101840752002d03503028002c40d08040d00c00314010500003800c2007001c2101d8051101600200100b9440344203000704c01849020b010000d9000b840810100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 109040305 1250 109039055 109039057
    0xa111e18090102070b090a11120c0f0f032401060f0f05030a0216050a05010b1e040b030a0203010c050d05011d0708130c06020703060f0501120305031504090b040506070f14 75
    0x1c24400010f140007030941d558003440e13030143e598001650255580c041040090201c1d00e9200008851b10060b07551241949a03840d803194040c10f00401c620700c000803041d01d80141e501c1011b1801802e89000120f03800200007040d103082e1000801080040001507020b000307004c070f88000324590360f85070000080b0a03419540c40d440540302c5210207908000b00313030b0710040020071000c0e5284214045c101e24005402c02d1170940c0d040030181c501c0b0346c4400c1c0f40c0d260703d9460b9441c141044403050710b000c21512102400603050448400d00070b501542060304646146900400600501c5070042041000380d072144020a50010310000041c9003a113040d020031102405031a01540c0440d501d20350a0541c2120f80da1741c02482540e5111101690069101b031003004590301880c100d005407100704004641c5010030422500414400103000d00c000000441c091124400a40800c0c1d0703405401845050b0580c50404041a0111004e4031103004010100d02013034450140002412401c0c2d85011040c203040400001e1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 109041555 1250 109040305 109040311
    0xc0b0304170a050c01091203150806010515090306270d050906070f0c030605010603060801020c0a12171006030507030219180305010e21041503020307050c0a111e18 72
    0x9000080c011144141402d0040d9060030340314107026040035410a00181c00e0752284034030144071081c0110b0a0280312b2001a5042c1160000c42c1c02c1c114240500e0a000d203503109101560b50580624400c20100090035908418209440d0400050501c0843e01c01031301c54042e103031685c002800401002c1c0c03047c0380150251900c1401080d07000151a0b0aa40e2003820820684c0111601c2d03407590010482c203030301440340c0310082204100a6192101030b03c5e082c0d0b01c501422000405905650648540c03140c4904c441d00d024a501d640c058100741801c000c1d500b0b484031a0301c986070010b402c190004107400e1090080c0c0d0940d07a04030117560b5a004070000195003244455113059200e00c0441400004100c090085184c280b0750903014251101c0040c3c134242c0c64843d45d481c880b588800c2003008008405040d82031550390580751800503102d840c1e0140483c3c2612400c02c0d40902c83c807480300c409003840800e0600500020040751024446802040300d00ca0306c4805090403544000b100c0c1d841070362000c0202080364 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 109042805 1250 109041555 109041557
    0x3020f0909060730050406240306050405010209121b01030b011d041821140409050613090515060109050303040e1906060816170105010c0303060317070c0b0304170a 72
    0x500e241610045030038680d40304c0c8450340c0d29190300c00d0009001a0f44103d8500022445515258080b070100c199041c081c68880107210b540e490300010300b40f083c00c1d0305039948642c005100c1c1c0d80920206034555540c605c0f540303005000ea029484c4580319507000b840b5030b6103402c506841d400d02c2a151400b0130003030315400d00e81070340e04543c0728601480948a059006110b45100d0325004e15007000114a10b44c0c1c0743d29002809060107841c0044d03400c00d00500782510100c80c0c01e682c0125940d074034030f4085100b80540c0c5080280c2039042005403400c002012801039a800d1b200610000d240d5100c07401124505150f1107401c0e00b41d0000c01052295181d050400c43c0e110b40341000d403c0c001d100e000006011a070317403680b2080c0042e042006201c4070580701c400b10283c0303017001d161240d00001f070b802020301c0500061040505208120030304204040c00303131b00300000644e04032441480c0340c005003c000d2017030343c801101140c040300d00b070380d012520b840c2070070560340160f420480817522962203001c0540d0603442986084 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 109044055 1250 109042805 109042847
    0x9090103020d050c0a0f09140603060f09070b0d0501060806010e21010902090a050402030d08040503090f0112050a020a02010606050c0607051b010609092d0201050904090c080703020f09090607 84
    0x131511554440001464440c1d40404854030344802141255800e6504020300b14651051140c0740d540000c403142c1040c201403000790281c450514807481d00a4030740c07004e4114440400c600c00c811411740e02c010f0407501c030ba80350000d080e40c07407000440380006003207503030381d03115540300301180f03500f403040d8401c03200041d400000040c10b0304140c000850551003150b2101200d9240e00c00c0008609007800f60b10328000c0b090a0450300f90625030381e042c2d100e0040150aa003d00260580050903031f100b00b0000040d049180820010360900d0212400603501c81500200590f085c0b031400128144074030112144d213410403000d000c003600c504000b12000da1202140c1c1d5200701074946c0356140d400084c800c16000b02462200000c448101e882c01d249061124000000200c0d01c0007030552404c6960302c51480c07100d60920b0640c0c3c6c0d03040c1c0100050020301c07119401601e001c022000201c0d0040f40010580240d038000c03100b603c0344481c02400c005200034211008101500803002280401d4023540c10008810840d101035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 109045305 1250 109044055 109044073
    0xf11070504110c010b150304020f010e09090607090f03150e0304051c0302061302100804081309051e040309090903020c120a0c0b03090a11031c0c0b01080309090103020d05 75
    0x1c0c1c107030303208040a054000800542c01550220034440d1040f1840c0903200c2d290b024803c000d0074411804000d00c013a0003502020420455a032140f0f021480c000802040008281850795485a0b140340c219040b0703000c102103810220b40c060700d03020414212903205074101120010b403074180024181c1415031805922081c030000c21182d603182c602c80c14214101004051142003400c0c02444c08401a00c031000c0c000ea48100c500150711210121521070b0000d00f480711180d122450080c00ba84a0002c21003441c2c20780540c0812503099a1b04400d00401d030b41040c0c1c140c40c84030511400c0c80d0160a480c02000300b001408100451030154008151181c06401504d40791041c05c008600d0015115010006076001140aa42084044003184000c0d140041509003945003048000755035030030803a00a441c205510500e440c19650070401040c4803400c01c412000e0352146980042c200c0c1f0341d40300e0100c5104590000103e140d85000084c2c44100800034502080c0364030303540901003000b030010400c0e50140030704002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 109046555 1250 109045305 109045309
    0xb0a0905090f061528120501060603050112030804020f130204050f0609030c09250e01020607020c0f060d060306020f0a0815030618160e011a03090d0302160f080306041404030f110705 80
    0x30b81c00c01045080d20b4254008114070342542124100d2b0055400c0c1494000103115582120b03600303044060b894105500f50352114000110303e00516581c096000952481e0240f11511607005041101c0040d9019481e0541e02c800300016030042c0b10f0ba030354241d031014140100a00d40000031942002001d03014507031601c90455214070701c49009440d1400f0440e45000e4000c2c44d603040041540c01203071031001d4a11528030000180700a100f1245d000d204034008507000f802c130b00701070f80440d00070750340048215600c0d1b00c40b1880000076000580182d020400b00c40c001a07000e05074401c83c5000442c010003030942d90395503403888c0ca0011907281c11020039104460345000e52100c00361050001d4241c10308200065850310a2805592402c0d64100d5800c4c0000e00500c014003000107144516420385040c01341c0c032816070103280032000031408005080c80c403128550f00305001c0740e00e000714041e00058400b0f0208200fa84a00d6110550a0714010005505094681092480307400307070101c0b122524040d035222642e5000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 109047805 1250 109046555 109046629
    0x6071e0f06021207020307020a0b0c03040b0d0b010e180a020307031107060506030f010c0503060603181f0f0501030203030706050c0d09050c09150a03060f0b0a0905090f0615 76
    0x40c125070785580082c20401c0da080c2d14200c10341c0300d840703403009501c0c0c010182c1c0403c503640f40d640700c4e8024075a07000c11911f030110014007c1e9400340070703030031401c9032600d161418a0000d082c2d103828082c0801c056007220724160422098078a0200551103103000b04d6200c41d4403c000030341c4014900020142e44200401e0226102e00050440e03901a61020465080c07800400d401e007003480492001c140c0c941181c0304100c0d40c0110540c1e5112004407681e0783c0b6507443e55500c89481140746200c0c10b00d4003c02240c03d075100d203492221403d14440e00c1e010804850b90100460403a4820301019502d5441449624002402a00300c1544508905c18144c105211415100c0c103a808045086400f46c1000c0c3c0001c0c02401c000524a502c21007042541c0c2c2d0600c124404540324800354040582000d4403807514462180d99500101d008013400380080c3c403066900e030751800051105890b40720b414054800140001400020110f005d901c00006000d1018820701c10011064454000e480c20404004440b417031164a0403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 109049055 1250 109047805 109047833
    0x30a0204030c031401050a020c0d0818060f090709020f040902034614070807111209030f0c030303070c0606030501020304060903110a030905010c0302100507020115050109030206071e 80
    0xc4d110701504030f2810941d90a581006004160307031403044c0401c6800a40010301c0340003070740d05030404842d1526040880c002442e1030f42465540351042e42c2c24491006131010849103c0d0b5243c00030345541030340f100e00d00c03001c1e072240e030100120030b035401d00c028000c41e0181d5004541241c00e81d0840024462010f03600c00d044843c8982c48032241c148010254185441c80c00c0540c800c0703100c440100b03c0821800303a085554200942070f48104500c2200003117802c1e0142000c07842c0d66200780d08a8881c1120000c800306131fa840303801e44a029010710034020314183c80c001003030031521f40002c4c0903605594607401c0031514001c5084003502c0d850749421000006c50130a00c002e6001b180101c001144100c100e007009425030f41040c40304102c030791083d0300700b2010903171107030442c0241c0b40c091801300303a448000d013801c0b4946480b407424064001e01e00010720400a40541c801c850410260030500c0791540c0c0c81e001590105524840a500500c040201d0000100098a03e00955050002010034081d0503144c0c21200354442c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 109050305 1250 109049055 109049063
    0x1c0c02030405010e04050105061204020d050f07030c0602011514010207030f0803010504050603030310120204020909190e0106080a06150806070e03060a0902030d0f031d031201060c0203030f030a0204030c03 90
    0x1e03080c041540d0209185450030019281400594540800f00760188203c01d0b036080903400c060301090031561102d0b03621030004d03001310448444034012034140381c440050b07210843c0c90b021050000100140180903031403080044034406280306144c081d851880d040da0240349030441c0600800440080c000040d0355207a02c0c014034180d5101d604010a10040301c0025090b18425070080c41044100b008481b4240d02f1344000000c441e51401942c800300c1c0c0030f4007074902020f5002c00b101c0d04004401094524030320014a947c0c40500c21200c1300348105080302c041c2d0140c5029501702d000c0440100703000b038000721110100381440c042225903d41c400c505201c82642c030200000d40d44407424280c0d24007007141c150802d81000c0100f002c510a90300007640e0b2034220228905018000100c220b5160190388841100c00b081c1e5001e0b8102e541c031000d040d440790300c040f626040410030380707002084c014450840c200200b039000d80114a00000032400020f02c1e08001c04064685408010100008501c10144001075110f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 109051555 1250 109050305 109050307
    0x2060d0c050d0b0a030f03030b01090e040303020315040501141c0803090a12030c0c0311010e0d020a062009011107050d0c0608070f05090d02010908010203090303040c0f050108010b1c0c0203 83
    0x40c929106486244803104c0c401e0b4940c060a00100d42c4600c010b41485030b15007000105c0798926401658182a203601240d00d8564160402c070078143c04d40c004512401c0c4480309948080100c400300003c8030801e000345d0381c2502180744024200d007080c082141480f0307071220520900c40c0f45d07642d624503d03038022200d05c002904894411820040030b00300161b0300b000c16003000e000701c084036800105a86d52090000e01040240c40c02262000020340c0050000400601034440305d901c0000040e54419100341c1c01c44281c0e103040ca00a6001107038070414003803030100400e10303031504203200c1c0111030f010300b00100100c0c0d6008048000400d83c2d034440c032060070349110f003038254000b500d042d20260041c08014458000d000c50b4030441c40b1125805001c659151100325180d242c4000c0c3c80c00103c0ea000841c3e040380c1c40301d62000090006007e80040074520540c81034040741c0b007507501c68500c44050209071040e140440c00c07000c0144401403c850103460300d00c0d581118118592a031180c404243ca901400c0d803000760300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 109052805 1250 109051555 109051567
    0xf030203060a060311010804080d06030b1806150f0109081c08010e100b0d06050607080702100f0806093c010801020a020c1002070b0c010c031a03100902060d0c05 71
    0x10103011065100420220410540d03183d45c45040944507000c0c4450b04010170400000c0402100406551212810540400c401034682c80c10801200c01501d80f4000c4d1a002a00c101c1ca4210000311248500304031a120021681410280000c40c00078183c0b5a0502110754008945080d0070000743c524a1264080b0303200d90800810050981881a0001c0110b40400d008015104403503050801c2103d90a014007a40ca41c5d0340c690107030040c05903401c1507610400c0003174658280500000a050760b07a000715070340115007040340800c0d00e8103c901d81c5900c02041404c030025a0f10310b4290313100ca90200540001c4501c00e51140309071001d40c03080011300c50381e664140d122112160441440c0034098038400e0000c510308445008007941da80e82400d18184500c0c0752010140d50700e0b109000b11340003005030308503950b00c4440e004c1c032143c003a200c8002e08000280c42c00c0204143d81088803110000c42001801401500a40c0c007015009040b54420907608000c040290585000142c030a40c480181c0710350310203403605 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 109054055 1250 109052805 109052809
    0xb0615030c18011106040b0403021e0609010f0203190f0b060d020307021006061b050304050a0b18041103043f08010b0705060c0a440f0703090f0b010f0302 68
    0xc1e02d401500c40c1080301505980314140800900c0a4203d41c03c81c0303041005540754507040345042c204602d044514007074050111250b950024820380580c085400078081c1d11850102e20049000480d5201110100f0610747c0180d0644e5500c90a510f903040d140c08201a51480c0100e007069002c040484d00d029800800c021030241c2c144a0080302086410090011902d0b2540041c2800745d502c40c4e11441d0a001c40012003000400c008850062a016200c91942562482c1e00c7c100c5420400428950f40a070108125107854513214889469400200740d5040d9100c0340c035a2001c50318005a40c000034102d148000881445e01d468100c1d0640c142c0e6121003d142d40000020641e403010790044140040a01c00000060360209580b54802845000c0680351100320704100c80d410107214400008841003c0001c1c0945150200035009000704100761600140088000d201c9640840340c05040201f0240490704442c8603030000c0394041c0c040c1d101143d022a05458082440c030b4203a2001c030501040c50401c000b18 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 109055305 1250 109054055 109054087
    0x20915040302010e0a14010e010306080f061806060d150f1a031005060d03030c02120304051006270509010212090105101706150a0306140106020616020a0b0615030c 72
    0x91420345d01501211b01d85028152001c105011080c1445428070202c041a440381d030000f001407000c9030882c0c1e860307514003034600c0e1154800d842448000405001c0d0f02c1c001000003a00500454014103042906022500ca200709080c4da18281820316880340100c103640c415038010325003101c0d244070000b082c01e141da20030180383c0900030740c9458402c1e080804000840e0786110000c0d204a415050108500c050803808908044107110300b240e202c10044244814804001159040c1c50346c20001006055111000032a0840400b1031240c0c10241980903005031350341640107a80c100000c0c2001605100343c05169001800341225400f5441e9034440070021103c1c0d03092441001403045800800030000c0754003100340c42d21790044c07a14800303928001c403504503601c88660480080d40c21020800442d5849080f0034240c4d0428403c4000603c13400c004101c41e120a0030341d4045140541d0010314400d00a6038a0159000008000d190321000e541002080000401d006511030034441c41e2050703540c4108c0c03400c4184 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 109056555 1250 109055305 109055327
    0x50901270206040504020c071d040510050103080702040f0e010606110d09122004020f0304021807051c0b150403050106060503100e090a05011b0215161202091504030201 74
    0xd04206000d5000142c0c4400003101c040c1d50095501581e80e41090b000186401080e510a907000b00e80501c5049502050f64401c90140f44504151095a2080b044040c00d643c0e0030302010344040c0341000844010716141e0b11188105c3c480050200b142150f04c80c40c1c1e803c4500c0b90b400140400d03202e400300b03184080e091226121072403042c2003411149041c00390000d810724100200034901e241050304030400c09052143c080201c58000c0055596545005150b207080e001620200e009580711605400c081701c40c26921441400c1700c4d5561820b01681622018401e07180b40c9001c0030f41c99030307104010025218213580c560090302000c580c07555140b07985892421035086a106404000040c010b004000e50301641200403503414038030240343c68444a00c4141010022403008180b07610301034914224510403c95802ca1203441c0d022748980e041035184441203c4c204482d080301e03070800d4945418140d4081c00005020400c2c01c80c1c01414175409402045054001c1c580c0000300f6040400d0030011580d100c610144 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 109057805 1250 109056555 109056611
    0x70f05130204151d06030c0405090601080402011209020f0a0f082b0e030c04060e010501030f020f03070f1107030b06120a12030b15070609020f06040303090605030712050901 76
    0x45090300d8031201104007004001c5610130401107209a108540510070020010740c0d00414441d80c0e42421140d803009940b191180e00d0144c0e10f440006a52076018011003481a50107031030301901d03403404220345001041c5003034080341c1c030803901d03958120151a010f2920b000303002c0700155883c1311814280c019207460f142d4081400604012104401110000b070001c04805605060403060445d040300082d0420320700c04203040d00946082c02c0000c1c1c4030300e582d078050f049800a880401071082500c3c0f180341a480768050450345c030002000800c0416104101d89807080e40c036071078a400e0002000c054242401e106a1003a601c00c0940c00c05e018140c500828200d20600c50f0341c004054015099907810f40c1610342e203034181c0074180e56000214258481602c00007201902d0b502e041d035188000d00c1c1044c014184131030203078002c1104ca2201c90b45070415000f10360640b0f416440e00141c0f140340c04412901c5620080100c001c01031600c40004148202c1d00849000f07403140c40000c80e0341003546004044001200d65154 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 109059055 1250 109057805 109057807
    0x90c0306090c040f0b1f14070f0807020103060b0a03050708070804150f020405120304180605030304030605091c110c060415030f0908130306050f04150903090305070f051302 76
    0x1c01c0401000074100d4402c54169000704a40490b1006140101003410316142c000503002c1c840c3d0340f01c80c004403102c070103404243c95401030302c200c0880d03040e19409480340c020400031202e500d00010417182000f034880b00e0f20516012a11544404101441d60024080d504c0820740314800e101c3c810303410240655010180d441c2610462505460710080e40501a041c20906650b400a144460400f901101c0c041c19016210b0b66080c1413902c40c950350f940c003510800a8140d007008503900e00c038105000c2c0354112000100250704050654440c40014039007d0220f094610503c07010b00c2d9030701802d00402c030047d60540c85190a4405200206043c10402d041851203860f08001c00c2c07003100d410401d00f06070300d016403400180c00b41d80307151010020810218003605510012034800d1aa14071003182100340e0703104080521081c0c95040801c144403100b51230081c00c05006040c428040510b6500031414a8000e1518a0031103550b610703501d06101c001c1d0051500b1401c48041440310b4103140c5004618224248411 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 109060305 1250 109059055 109059061
    0x20607020d300509010815030715260108030712020102070b040809040506010e1f020f0a140d030204080304140f150307020f0f0c0f01121811030d02060f090703060207050303090c0306 80
    0x82207818007c0500914000c1003650300d03d40c1c0c404210700300c042c00e074145485058040d20701000e0452000c0324040402c840300100c404520149440c6914120b8001800440c00d00c2515681c07a4070783c0940320030f950110b650a0281e0400b15400c0340340301d8010381c0624107140d80c0e03c00c00010300090f0b0f8402042c0505110152510852940303034170324684c220a00e4031820b02d00c080c500d03d0040b4140907158403003000a20915590609011000c240307086070182000480740d001440c420103400340e0040c1e22420300c140e00144001c100f00a541101c0003920400102241c03034009007100000c80300d9001d140c0d01d203060300001c0304221685d5010080c0503c02c80e8500c0040172544070280c4101d03566800d40740d045000354030221a40c02140d000e040e03000090340008805004080171881404000a80644c00362640ca070b005800108505001c00c08030740c0482554040d041030b544080c070f03624a0302c00180c080002841401000008505144060000300b84a0b502a55a0f814040001c40c6810200981184030340c00038028 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 109061555 1250 109060305 109060307
    0x30708010306020f0706110408070e07121505040e21070510090f050a0308060307091b111207060b0a0f081005040507030210051e03070c020607020d30050901 69
    0x1800c0c1100d0340701001503503400c68000800c3d014094940c00800711810150900010b040e5500a401554081c1d01100e626075075601c7c80e00080340c401d81e0f03120041105a58160f04040d1150030580300082120b50303c8100d1035039840072404548260003030310314540120f6038102c031640510300a107200340340d118034030360070004c03140c88e5141c49801040c00c840815a4424482c0204244444400c0c2400c3d00241510072010243c1405000080c1c100e402a10038050030002040408c050f00c2aa07002881d5146280a001ca400c44295000708072504403103001d02c6000803c86061841c24000c0c01410301c994404100083e4040c00d01000e00020340014100324030000087c0110100090900c8507020540c0c00494143c40d1400c0103418603c6503000a900010704a50490302d10b0b400030020151a58603003841c6c5c51040f18020205410301003a20320b0b00001c2d10401322903015203402405010654001040450b00c0078282c0da400e0b687c40d1076000e9050001c0001e0250b04124a034202481d09240c9980c1040c034503101907100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 109062805 1250 109061555 109061567
    0x1050d0b042c2a0d230f0613031d1302040f0614090d080d060918050d0903030905010c050708030a09050a06020a020312250303020d060f180207140610090f020307 71
    0x101e5500540c01e030712404d01845400c2c4c88102180810b0090348454140c0c86405c41d13100e480b000440030b0b05224407008501d40c7c00c544020b048929401d0341c2d5071001451a8904a4441d0110300c42007580201c640c4503140d001c0b42584004c0000301040d2400f403001521b0500060000b80d41407040d8014004280009a102d4542020050107541d104082c2c640d2085288240d10040c06135402150242d840d084400a21043c0d50002c0091140030340203e403088050850101c5082d5820b0000400180b1041c108000c15409045100c600710310950036104900d489140740703450f682000745800001190340e8400c12441c01c181c5a9540981098800303024040981d40209554001c250940250b24000140307202c881010600c60522000074490010358507942418020040d42103820b042e50032500c1c0c581c00103818601d5001c001c04940e443c0204c5011420002148402900603501c02c1c2d8030403180c45403a102c416002d00c4014420040814900805400c007404041210002c400700c40b8054410821700140e907821403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 109064055 1250 109062805 109062883
    0x60405030a031e060306060303031107020f090a0e0318090f0f06090406060305010e1015051509010306050a08030a0801090e0615010e10051b0303010501050d0b042c 72
    0x10034007083c144000034601c42e2031243c107062503c0c180c1c40e00b03602100300700584c1c21a201310703402030798240049030284c4041c400d144102480203521230460b02c407013541c034289000d0041d40b0204000001600d000b0380c0680170b003990b00446400d11042c8504850300018505a08056001481c07508250710718648070000c4d59460b03801504039881402d2241c0040c0410013103422000203140c0c0f19000340040580c40c03071070b01da82d15600b4206036451030402038000d088000507122841120070040503a4040381ca110010710299004640c001d04040e2036800119003074a41c5a0300100825660000b580c4d0b408110304002d00c10001a00314118990915036060904a400540d950300310701d04503088980304d07200c100113903652843c3c002e120790006240b40f030000e01c55400c400a03140e02001c1101d41c044030413940010f5512440240509408200240b00c100c0c9591415032200000749800f0b000022031086100b101c3c03c241e4480c1c02819004416400035480e141020f02420303490701580d240036044000380800480e06105c0c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 109065305 1250 109064055 109064057
    0x605150904260d050a0516090e041104090c081501050d03050307181502070f050109060804060e070b1c0c05030109090804091104031a0408030a02030402030c0910050111060405030a 79
    0x100102100d10180a4002e020b00405030b14260b607480764545241c01901c82294800b413094604400244003503d0b600100c41c09403005d41d280b040050030107070600001c1201403c151240b01c0702141c22601ca4840b446513228042c02680f159a10b54940b1084500d407281c0441d640b20b01c0115200100116124a1036005085500d804c0585d241c1c3d9450703c0880f1030340e500030b0082d41c03c2602c1c540f000401d20f100071034403004e0407140d50039100c030103495081081c0402d000c0c1c49000e00041041c40108070f040c0c4a1180d40340c0151040b0008280c0600300881c1d68503181060300407061040b40007030f015082e4a120080c00c8030340380c00b1080c24060940510405401808144174030311085449609030340070001408210b40103041018020028140700f90038103c10307130b081404200c508050900102c008100c1c643c41c4548035917441108185196038195210000e50005402245c040c400c5403458034440c1c0d10b0000440c0700c1c004156010034518548800100000c0c81320000c1403043d0004000e003c08600c1c044102c50b64004c7c9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 109066555 1250 109065305 109065323
    0x9120e0307140d05010f05010f0e0108030405100210140106090e04050c060c0f070e0604050702071a07020d0204020a080906010b180913081303060b040b03030a0c0c050604120605150904 81
    0x60b011803030401400d10010595403a21100310040f10195105905070740640000c0a500d039111551411040001e020307040d00e69100b40700411040c6402d104924403080b561061f285050342007907054050f6011150040c00b140f140c43d0062004642c803a803807900500c0170501025640c00e240c0c032017585a01c0300f51b09903405608001001844410308112071440985010120340c04140c0d01e00d090010314030281c508134419418070000c030318102d00c00984a810b5401c603202e0241490b032098489881c035800200c0898003d100c1d5001d05000d60340d41e20141922450720f0f11a400540307400710350682006c1050b00506001e0005000700007481440d108050300e01d0f2020f60ba00070040d1149003821038000c0002500907d1502c00041407403040103101c1401d01120b1086a0900000104030304000079203a0303600c2c0d002d41650081c40000c004c00c1c411904110a6401440507403135194a170008218103511a0304446a10280758a80c5000c21003144141a401103000071660110a4000002030030901c0190000e012704d80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 109067805 1250 109066555 109066589
    0xd120f05041503050103060f06030218041703010603090201031b020a02060d06030f030f090806010b1c0e01060902040f0b07020d120306050618120606030327060a020109120e0307 78
    0x101500c200da000d40801c0071203485280c60035500a01810007400201c4805041070080103c518060003000e003900d80c010414042d01c00b8155011086001c02441603a460041c0c900c154155000d0303800440c080c0040743e40116040041e40000350980c2c0b40c4641400d000103d4000c03040c0c03417503400306144041e1541240c68540d6200c080024402070000c0fa00058141d040030407110301050b82104040c0251400703074032000c2c03815a0720701410741c03181024070400030401010000417100c290b41111041c007207854403030006200d040c4120381a00712801c43d08007407101c6500040a2200d40002e20b0124000e01e641c2030060b03e0319031982e005c0b840c140c811407001842d501c43c0e003030242c45550003904180c02a02c0b014020a40351412689440000248071000900034440500941d00428011034441d204010150003589402d68140c1d84085401c0c140d4040031b40c00107072110002c0d03140d940c0d8000b00144a0940d00102c3c207401d081c100104001410a040c0051044500d0f100c089910301080040031141c09030f4920446207 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 109069055 1250 109067805 109067807
    0x405030409110c060108070303090b0a05041a07051c0201110c0d05090a090504060b0406080a02151806040f0608060604060f031e09050a050606030307020d0605060d05030a1205060d120f 81
    0x40034a003800a00f602a0500100d01c810303001814000303c030b00a658170542582d40d03c900070071501c00c3c090301c0750000e00e003000b0901c0f043e0000324407110720060000c13410b403400381c4a4072400d007481c0c5d4466088400c201200341034400b080c0d09001c1d940d0701c0304402c4c1410b4a081016043c0d2503481038401511004e20001249610311940c0301c8200740028006000140190b01d0240788c440001c108811101c0e209914103030001c60b21120006110074000d0f1b000c0e01c201c0180000900c0340c1080c0e00b20b2080c15800064403110612a41c440c40302400017840503554040312030703040040260029900510460085005210403c09154081441122400c850071f0000e40d1101281c0207880003030003020031015543c1411140d07000c009001650060341d900400984005440d1003040586a209100e006540604142e40c4000880c00b941c0c002038001400038800040392055a4426085802c007250400220390043c0c0c2450031841103004044d0701c904201d4190f8403085140c1c0e80c1c00811102901c02304100301650014803806 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 109070305 1250 109069055 109069057
    0x40e13030311030901200901050d0b210f011b09090203040606050d2004052403070801090b01060e0307050a0b1803120c01060b0304020f130b0603040b06090708040503040911 76
    0x3092410b8240c69036072808420181c0a8040121130900c9804032074071160754884000b0540324549416564a442c0c0310104440d54060000d400780b41e0b501c51b0005c0014000d52040c4503e030800500024081d000a0030411003042c2128005d0403848900c0d0003032402d080390581e12495034030640c0c1c14443c0c01601c0b611517040113401008142c10494000c0da100d00218280300d1940e0444441500410442d03044071900c600340400e4541c05e94964000d001306220700c881700d007032440d40c3da17080c850044c1c115104507599007641825110360134405d4030702d644504014004503502c101c80980c41e01c8181c004000051400700890f0045003580300e07040460707001280110307041801d190041031b5003400804858621071402079550035648608881c4003158078140e0006159002c08090301c1c0301755001001d0b00e181da4160810300c00c03458105420b030440a940ca100b80c8010765200e101030f50059010b244cd128407450710805101142a000e4100414024014200000200c0020031101600d070091b401140d100c0c0ca4007102002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 109071555 1250 109070305 109070321
    0x40509040503091e04050702010e060c1c1802190e0c07051f1a0f10050a02070308040311100804110f0307050307080114060109030b071b02120601060f05040e130303 72
    0x806000342c100303082444c40249404800b40400c0300c1c10440c984868800340c1c00c8a40c040c0c40b604440d003003003000030503440c1668090500070480303915514a0782a0451080c048500c4250580031651200044c0300c191709000100006010403009400c10f02410142404500c543c000d20f0072a00000010704001000400d00a0000322101191920080e40050314070f0009080856101c003400203048884400c4c620f841c1032100020200640010304401c042481155a0751144544074158422900c001001910174401800110700440541c086010004100b00d5003050511030034027040030210900c004540d41c2034a44120500455203a00030191440109050041ca544400d60501402400280001040d00807030400e00310040e010115690700001907400103050300000c2c082d00c1140000500903401030280941402c0e400d05a81c21030300e196800030b0050309951103c0082c542020b00104042500250180d148040c1410078600b00b40c10801c4500389088024003400b41412056170f8141803600940c01090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 109072805 1250 109071555 109071559
    0x4050c0c0609060403020c010e090a020a030b030d020d0806040b011d04110c0703020307050111060403030f1b0f03050106030b0303270405070f090f030c0905090c0303030a200301050604050904050309 87
    0xc01d5260001601d40c481e1012582a0054019400008040d41c4601c02e04900110000d1602150781c44152a03180290801c56040051503500c0b00b1510340c55a080140d020714034404d500421001205000040404001918460295041500c3c00003a0303a04600602188100c102c2c440fa400c3e520280020050308443d09110042c0100185d00390140b200864050141d80c000c1d0120358165544e0001191400782003101c02204e41c2002c80030500007446a0041e4482c03036031035000400d8031a0019092209007681007080301c0824080c0f45602e840c180c160181c0c07801051f103418200310440b08080865242e114100d560000e001c147c00407109903030380c0314040100b01070010740b04008903d00280043e00c440460b406032004100c604030006000050340320000c0035a64080030304c4113828940407020000d484082d00391022800f615201e000e240d02c0030400380d88a2558001d003c00c2c049450100104074035807028540d07040c000c2c2000180096111201128100d80065410018596890030035500b5805100c0b07103a9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 109074055 1250 109072805 109072813
    0xa0c0b01062708060f070c0c180507020105010f05040906090c030f0201090b070507170f06151e0d030f090b0f03040614131212140108070803040608010504050c0c 71
    0x2041e02030b071051031208600d4102402d440c01407001003450300070010600c00d40754070b80d12110003c0c01c010b140340e0f100c035040441030501262401e0740341e4404400803500e410040d07480d141c244001040c50f07814091a90032084c80d0008200d254105000c8103179104882c010a4001d60715100d0300c03070410101c0d44c400251241c00101c0e50030010b80b04e00d07054840014940c4180d000402102d80415172000e08001c1b03880e0190b0000c02004001e18041c10401c0c500000c80b070700c48581c000e0078452120341d0424018984100c000c800700140348250070041100e120300c00c035848500300580302d81c5042140c07680162129440e405043c10302d6015a8504110303001c03031581d0010700e004000440d009008401c0240076501841c806e0505106034902296100000c101c1103e605140440c42c0c0c80d400041420b4440d401c0c11807030a850f003102c00d001120b0044050303443c0c81842e0010540c90000400c030081e1705001c000007400c031913400b4610340342c80d00c0303c010000c1006004a41c4a40e45d603c1c040741260101408640b039a081d1401a5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 109075305 1250 109074055 109074059
    0x11100c0203180915060a050d1d0f070b070f06020c0d0c020a0602030715020f22030b0a090203030702010c02041b0c110303040f0e0c04030606060c02120d0c11030a02090f01030c060f090b0a0c0b01 85
    0x10902004040150b281c1031280c0300074000242ea010071b02c10f00752330b8248000c9050000a8076404400d41d81c80038203455030f940c2002030f111030510a01c00901501080d44030207004040e00d10501448500030380c03010045400a000000004d0340310103000743e0054200c2009612982000f40540007481003800c5022081110815081d200440301d034410100d0b80a160500c94590f074140c505815511849002580354000300840001076000c0c3e0214806140054000240120303085104040d0703101000050000c50340c4256414100007111450700070700c02c5c041d0051401d00713251200d240140c1e401030241c44c103c1400680080c0a101c0c640041d1002550010814408a983d80201501c2c0720046541a4069482d65000e0115500c0000b2403c041100c01d559102095601751914a4040300094101e81c1c1405103003c8131005d60f0728844105e014040750382e0400c1e65075145140c040301d58004c43c0e0103003003880381d84404079a540b9000004031007192405001c4076983d1260440c1200d00c80d0b66074a00401c0c4042c40400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 109076555 1250 109075305 109075331
    0xe07020d02060a0603110118030b0a02090306090307020607240603080405010f02010c08150609060a0905090a0e0a12031e0c032a11100c0203180915060a050d 69
    0x300c5604840c2602a07980d0703500c40040b0030094400034000682030f007000c1e6100c41115403003086601c00c0c2c81c07040603a440045440340d03145222110150340030680240c0101c3e00d40b405150512501d50001c0050009502c0e0154903070100d000f41c000d2000c0903006c00310710701c100b0740d803c2280c4491800c1205845802c1100545a1508030210f80041c050380d40000c1e00702042c8560140144a403c684890f1074880d403407113580b6052840323200d420b222075540c1c0001c42800505203a40b40c0707001401860000303445216840b404c0809110103901e00a0070b0700c86482c14000d04510190002c00c0c01e00c0b500d60040000c5e0398621014000b6005410310891110400d038145590741c02001d010390283c0813200700d0f0b94041c06050074440e5041400b80c6010400c034040e81c080307026030207405d00407418105600c44240c01e8424a21030803841004032040f0035103510240c2c10018030200a41849074518a541e081101c03071301060b08240700144074151400e40818041c4000241030748009002d881a103410550340c000c18046450a4a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 109077805 1250 109076555 109076563
    0x90e04110d12170105060304150203090a0203010f0c020d0512040807031412040308100605040b0714070305030901170412080c160302070305010e010e06040303090201051c1506020c0310150e0702 85
    0x124061800f081400032a403860041c08a0b0300468016100c070340380c0340c1d4440c140c4000358000b52403410588031701403140005071001e0007540c40078003810138000f800704102d81f0064140150406210b0400904118100842d110580c4098202c0d0300808621303100d003080d14042d18000e45c041c0005507004404180c441c0b00d41215021248264803a655000042c2c81e0784440714800201070007080045242400140031841c041d1000e401480d00076005940346e59501c000d110700342421a0000d840c05c1d00b002496000750f503000408500006003403030301121686400e444074006a000c500c0442d081228010204c0d215148500c16510103020400c54003080ca052441c02a544520600c001c031015424400d517424103d80600c124480710f02000040c241c9591681c0d0224020060701404905100c000d0051600411740350328092821550450000703510001e42d40806c100340002d500030b000f1544011011300690328003042c1c00c0d160b60a08100070400300f090340305541c502610f540000f403044e0110400c21104d141d0000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 109079055 1250 109077805 109077827
    0x160804120516050108090a02011b0813060216050609010806010905040608010903110a030905010804051005010603020406030e010b030d1107090c03050619050a05010807110601080309010906090e04110d12 89
    0x41d400418080d0381c1c400540d043c85c0111219803041c0c001c00e044a000d0350203001480b80c024040100c90101d00c0c1d0719669200942c014402140506040c00014070090b901041028a210f0f030007004110b074240342000142d21441600d907035a0403c522140410050b0f40580d1601018000003030092000313640b241082d600900300d000b01500000c1d1244404901d40901042c04801103070075030b8503c554142018015100744001501c2210684142c103043d0000c0070482c0300b028013030000ca580160752103191600c02030a0f15061031180c08aa4034282040e004e075640060381c0b000c070b0782c45030601300d00090002000c182001a140d000146107070a1141c4140950b52551145202d00c1044071401003020043d55103a4452080f40a425000805810140415800341c1c905a60203c003d20300241507030a81da131200c4c1080703002ea0240c681d9078004100d08a040da0003014400c0600041c0c5440150b05142c001da82403080d601500103840810007100d0540c464440040f075030309540d0000000d120010151600400501c03090b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 109080305 1250 109079055 109079083
    0xc16062d05220503040302060913051311040e07052202030901051e0c0d11070f0302070303111609020c0a022d090906060103051f030606031a0405031608041205 70
    0x1400710700203604402c503011a22950898004c0d420941150300348007407540901642c6a10406000030111080c40f14018184500c40040003105200c44915002008008c01010301c0e1245040482c10705074070000051880445000b04c4906c81d064680c03040c201810030300f0f8001900c42a000200704070b0700313120540103503010303501d585000740303010100300703803c180c02481610303001e045103810000d211148905401c4000301891007810645408010b0340c942800d100d0306034084004d44c200aa00700203040d0061141e03401c9240c0a400f40000c041e02c2c801e08000d048541c020b05001035404246a00446400c000070382c9500e6010704804040450710400400804880528040b2151604150311260601d99402400703200d0000040040d503c0d10001900544401055070010b40f00e50070001d1403000603100b060008600494000544500f5828050201500000138440343d40c211000d10001910020413558a0b01c00104801a004802d1410301b26502c1a6800710b400300041d01f260f20144100440c2000c06003850b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 109081555 1250 109080305 109080331
    0x40812180102120a0e15040603090b0a020306220e060702031e0703050f160203011803030615051e0d05181603150e0309030a0f0201080c16062d05 64
    0x3414012651040034641c40748014400f800b9100402e0f00a030b071000111403008000c005c0001c1d145240b0f6010740c0081c1e1144c000681c03524491f50601c10a14a40364101002c00e10039403841c60a100401c8002c1e92804550461720204220080d0701070869001c0c0c444c0f840b40c4030036500b050500383d000179620340141140301c2c50b04903180c0c00e031080110032500711040c9a607d0380f00c40f4105101181180740b0780d0030865000f811100c2c80303403042006a900f072041404e40c8400e000c0c0c0c803050110600300102280c0b9190440d400070340c01d030805d880e103054205003910030004c480d40350783d0064180300000c0e48003400788040d1240e200f400d200601241502800d61107000140047c22642c0310350343c00e801d900da10700302480301400d680300760444400001c006030400b04950100500700e0b4904008140800e142c00350580007075803600c7c40180414215a03001820680281c0c0d0142c14904150224480a24045011f0341c01031113196140e000d0600c0b003501007800b46100c603030f10041c42c4e0303d102590f0201002c0c0004451840b0080b103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 109082805 1250 109081555 109081597
    0x70e0909010509070501030b040b030a0302100605061812030c060c040302040e03090a03020f0114071415041218080f07090f06060c0b0c160602041406070302150c040812 74
    0x148074182c49030311010300071303d07a851038400150014110200d0060700b042e241c1ca0900110b0701d0802c40e00310003a20a5006182c25603a0b1104e2400b100d059420041c465401000704010105070720811040b403040c115940408142122078191551182c9600c40746079004840400501c90b0380f0380090b0045034000c3e542400f114072000d1203aa100d200c2c0d4218907510500540703049c40541005030204040d60740c1810841c45440001c2c2048034150000e08007280c003642c421800368504801400b60002042000e1011402414580d0b10040303100340001c41c0d1400c02c00d64007080091b030000e08603614018087d42013038480402028110320388985090190702103a030306140300500350812910813081250040c0e504d000e0004c550ba40d40e0140d20802800341c1d503400000f40024cd550701d0b485118a103503580304002c01a0b541d4a44940c0204c0d80540d00303030241c400e10040c84080080390300810304c0c54480000800d9036a0070354880700303038032003038010364201015611420860205005040d80207002241400b00d1562180f5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 109084055 1250 109082805 109082821
    0xc12030a0e1209041d0616120216020a1a0307030207051f0207050105060306090712140319030605092205012a020606100c08030c070203100504060506040b030319020c09070e09 77
    0x40c071103090940c45944003400160301e5034a0350042c80301c07803401d5140c1943d00c448c1e00c04045090380c100d42586104400701046060441c40c10700c0307100e00145001a0308511100b60311090748241d00004102a040c95000969502088000c2c400114110381000f80b0840c0d1030510750003034000350800070b0b0886040d840c0a011460a10700096a5841058200c00629803241081d00305284200d000c1d40171207000e01c03441451650040240040c151100c080d104483c80c1900343c12009040d1a03260388000d00650384c44c0184a8151140c005001042e031801035105111491454500e0041c0460403103442100c89543d001a40803d69444422000c1c0e410780c203c82c0152070700d404200350004d81000f02c50100381e0044540b07001410b030300c01840d84031210441c0345051440580120381868003260781d41400ea60769100300010070409214650b0800429101045403000b180042540e07845131200d642c1c0d00d400041051003800d8401c01680e20500009421442e650504038005440c082d90554800e1041a6020000e1a16 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 109085305 1250 109084055 109084091
    0x103030e0406030507060e01030608011407020d030c0806010c031b060e150f0a0504020d05061603050112020109060e0406240801080a080403020d030507060c18050103020c12030a0e120904 82
    0x3c0ca030404042e2002520f003610540d041041280c036141031603225140000c003108203100d11200521001040311603460420002801c0c1a903542c41e101c02e2514062260003034590001c07002d0b9000703100382410f0340c4125080c1400e9606481001d9580d6500040415801c01c005d402c4d00901c05103c10b0704110b0342460210f11181400c14811911402400208000508058800e8000c550814000340810794583d1058881d141811422145440521101345409243c150705100321801844800d010025101c41940001d040e01d40381e21880f002c1254043d030b035152642c0c4035072150700104a804e40750440441d101001c0e0101400000c00b110101c0e20360b400001d101e44003c00e601c4800c507401300243c0d16050a503402c1200c0600410001e404100c0140310480000e1080d00c00c5070000700031501e480c1104215607415800d41001070300161b040500500101c0d602d040001020000c41c03c04564041e284d55810000340010311a40c040200305100d125164090054000300070305030364009460034480000700ca02607000b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 109086555 1250 109085305 109085309
    0x60c0f0203030604051003050709050402010e01110316030e030a200901210501020f18041505060f0c0a0807120f03150302040902030a1514090f0d051303080f030103030e0406 76
    0x15030020800a0f40c07614140d407000394489019420140225201e0302c8142c60808603070864845941e545d0140415503800110f0b03400701030024600049024400302d14035841e40921058641a2401a004542010b0103500000c00c00100078040b0b13982d20b1114180143e0b425100fa48016840804006002960600d1008541a2208107142102d0341d158580035401d00e4141410543c1c4a5500b40090010601d0303080080c2071220f02500c00b840d00b1507100d42040100e80d42501030b082e0780f010107841000540c40792400d4800380c1440302c0c500c6884600000101c0c2c10041d4801001704985000a008001c03c46c0c0b041c0314242506055071400c106e400c2014081d0202c0c4d0903018040403031848402c04000501d40364000b9140640b0107426208240c00b169120150403605034400c040c2c0c070303841c0c0c50014464080c0e45040c035070003007850300103001c0d2150b01e203651907e030040106824104407001601c1002d04180c07215050096520082036a900c02c14442d45913083d030000c3c0012030002d908110401c040b40381c03900544007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 109087805 1250 109086555 109086557
    0xe0106051011010207050d090509250c030306031a010e0708070e0d08070c080d0e0306040807030c081e12090c0a0501120608060907031202160e10150903060c0f 70
    0xd8481200c000c00d0710042c041c203469001e6036400f0414140012000e00c24030060308102c0c1c4907402030328100b40400c60780388002008840010b1038809c11100b42c040c100020803564280381400e0803510401c0c24114040c0202c1d030070141c40071100413980d0104040701e040090490340045189a0f045e2600c3c0c80459443d1000c1d01c1c80b20002d1001c004892192400350b500100b00c5200356009442c044a40d611307810200c9140d1300c200280d0301328186005c0c040e0f81040c0c2200038034000724050328207031034070307a5800c241d602400c0000b0302040040c018503020002e00c4001c480d03202d280d04001c13039101000102c114440b03602115150813401280030104000030030000d40322029040c0185070601003420400111032529065404041440c1c81c0d110000e811340041c40700c00e0003046610080d0031100d00f5814400300d181c01222055013158000c007401004151800b0040781910b0541c95101c2702501c821030020350701400750f081444091030508005c00301542102d0314a007181e101d00c42c20b00511003107100075281141c0b00c2403c04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 109089055 1250 109087805 109087819
    0x3702210904020d1d0a02090c04050a03081b03030c0901020d11030a0e03031e12010509100b09040b0901150807022802040e010203010303020a150b01051602040e120d0e010605 76
    0x20007480c054018060070030700e6440004982d111103083d80003200201e11242c1154000007840702c19420074000869000725500040d030320f8913207081c0215800c502c891101a280400104442c030000c8100c010f140f0140595004507070f2282400c0e04218a190b125124103400b43c8603000b4040880390080b0210307000d100040c4003450a03e04111810f440c01d41c00d04a5142d414082000f0350303140b4680000c2401110341c3c2a10480e038840102006c007075503481040e00500e205050210401c98014142c1e0307040030507696203504050702d60750000d006c1006408003031f144640c098020f0001160107501e400d200007100c610381d1340e086195140c02605a0f242d40c84040070a00001103081e584e040401d00d11740d501d030150b00c003400003e41421242c1101d801c98100307800490041e00f00c180341c0c0042c0300c40c0554019400070080c4080081c81151400a000352013102031103a5030001c001c18140540d40c856106109182600081e40c0148103080030094840d80003001d496515480c0020940d1940c40520484c2c0984401400c1c0e4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 109090305 1250 109089055 109089067
    0xf130503070b12041113090309050d0c051203040b041502150702031602030c13060501020607021f05070507051f140f1f031502070218040309030602370221 68
    0xb6007010001041540c58650882c220003c980300c0e4000d407021079000c6880050204030230324006000c80681d610940c450954841c0100105000c1c414003030072210200c91200c48003032407040c110305600031907014080078100030a00141c48822010910042d03412030b42650b88010091540240c4100182c550000581c4203100e656001c3c640d4411141c001400141154828030941c80061281481d120043d611103032a0130082040c2d503010000da0341c0010a074009042c0180350b241010f45143c80c40d01d0004401501d03240407400c1c03940034108031181c00d13400500f50341c0c004041240f030042840b08126545000b5241c080388221554807414014054101c0300b10240c5140c465082c50000380d01002c80e2980070302c81c80340c0c0000c0011030604d0380300000a4211009030300c401c91401045180440d01e088001c590304c4030010800040c1e40311000b9010b903940041c0c0180c4a00340140820a6400f4003405050396102408818040c402080c014102d030020b240d088445001c9414248014991901d0f0b15121a40d414040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 109091555 1250 109090305 109090327
    0x601031a04020901050f030a060306140118021606240b041d22060504110d111203361005040e070203090405070809010509030306060d020d020d020f130503070b 70
    0x180041d40f4140f419608001d40c1040f843c005a2003a40ca55012541d44d034020020071280d4081c1c03082b0803441b82000d0070f042d85000b403a001a02a444034071511030723a0000f80710100280d110243d910b001e42026041145d003501150380e4410781b50241d0705200c0d004c0c00c40c00c0016140d06010440781039854114055000c6516600388a0101b40041c14640586200e000050f901030006100790740300c60b0040e20085814109030410050515207003002d0f030b00801e00c50052001260b02141c11002c1000192006c0300b44002d8880d09500310700502e60000c8901202d0f607802420005800c01c41c00780003648500c91020005540f04101040c424410303688003080d42807208011030050410420741c07182c810300540745071552030000101125001c40c1d46901003100e07242070007020f0030700344034150344903a0f404001c41c9103081000c005070040c00f550000042c0d0307540019001800710413680641e01c1e0417031100c0c4190344411104060b108107030030204140040d220403c4d4002001c0c0703000121001180d42d035500c65840e004480d14 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 109092805 1250 109091555 109091557
    0xc150a05010b1e04030f0804030b090c06031f15030f060f0501080402100c0b0c03010e06010309030207050d210c021302160b0604090b09010b0a09060305060f041b09090b0601031a0402 80
    0x9690b80d540e40c082c0800404503a86000d6460080c7c495000035a6a40c2945040121105c018041030000d902010320760009464640c1140c1e04110316200d52604100e890100c2c072403035030003504401c400a80c106004040c841e01174021003a0362840c1c01e42404010345450b2000b00c1d000003403040c94002035041c0301150150501450a840000d43c51820b40d840e103090741c84815907248203441d00079003040000010012040154400c5400000c2440d091000100544000303603155114060701e4414140101c0e07000c01c12000c0001c17072001910045400b403184900d100c002d00b02c000a60420303801800ea4900144030401c1c107108844c0a003a203010010d04400164441144c0c9100041c02181c01c59540c500c40c01c04a6071180889120302c0342e507000407440310f0015062000380743c1d05a000340480ea0404a00b0f1000400100e12564044003440c41050326a0313881c01c00c10400800708034642e80040d058000440c59003020b4004220aa00a1010002507114040118110b1b04004011441c2880d44a400c02c0a8a00b40e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 109094055 1250 109092805 109092847
    0x3040b0109021606020c03120601030e150a0b0a0305160501050a0f051b0102161704030507140a0f060e0910060816032003010e01090b010c030309170c150a05010b 71
    0x5034078082203c03a1a5203103030880c0e0018042c0c40c001c3e880840d00c1040c8074a0401c500341c3c050000c0c80c0c180100750515402a503101984000c99601014200008029030304e03a0313010179444240102110119941c9080882d00c40b40250b2203801950000440403c00b54051411120000b01d80e948201001880c0101210702c0d03000350304840030b001c10000140414801c00d0020b40035030070b1040f5684558070b003540b2707010846400010b2103e4050340240001c00202e2000324419088032400c8031402d5034000f88200051100140d42c000300406d298400f0003203209076100107405040541a40c40b0681500c401c40160305840c0c561043c600000c81c5031000885012200440100002040c2400b00300c0e400700c0420b40318180c410640810920901000401c80703240204005401021405403c1192401f0700000030103d210741a4003030203051f1a204514200041d25460303409040000c0c0d1102d80703030100003052070748407068418400f41052a181c0410900c00301031003014101d5032400c014904d030101d50300e0080d204141d10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 109095305 1250 109094055 109094077
    0xd0f05071412070210141008070807030206070606030503070309140d1101050c101e14040503092b0f1a16030f0f05250201050709030b1305010e0708010b0603040b010902 74
    0x1011400ea00c01054002c1407540408a043d00c0340d5464060f07c950640b441981c4200e0266010b92010025010081440c1c015030b901541c13a25038900350b6040c10000750950ba44001c2907403000081d0001416401440341041d143e003058403d40c030a071050104289031000c1c10015004181c002e030015000d40c081c00046c00650301000030380d01034140d1100300604850203406981041a1807182e0001044489c1c8100030850140290146460400f92641543c9004140308075004203240141a826200040520301120b0040304010244184a20780100003a1103200c00300c0d600109c0207200d0800402c7c04092038801c00600c2141e21800c00e00c590120701a018400a850110b0366544550350216001e00a451041072070080031710001612502e10307201c0c143c2e842c44103400c6901d00018011141c0d440440d40c01101c0e08518110b090340ca03a4050300c40101400d0030004d02e190710300980d4100b014404a114800c49480c24000c10980d1610010f1054611003118000c1c01c034010440144030400b03640e03019288105e55 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 109096555 1250 109095305 109095313
    0x2130e0a0f0303240b0d050c040f060518040b030a03031116050c190e0a0b060f07031709010c1407050106030807150c050c0c01030c02120d0f050714120702 68
    0x6261200a05990340c4241035000a48840820040301240001c4204e6000f104581e88812403801d038000c0c859001b02400c0101c000d8461000c41c0c80541c010b81903030b01411408800c0040507a03502000b60055001c25094050490102181e0890b4075051143c40d00207100034010701203281966401b1401052242a40c042c203040a100200f241124420f0421246d03105200500e17541c1c0001081002180e100c40c446207003118080c02c14800540d10302c044581003014000b01244107000a80020301601904030801c5100c4404100c880074180c3c01241e02c0020b8501c0303100d12296888241e416420b0318000c54409010691403800078280760465001440d44502440002510540325a145030056000c2d2509607540d001c41c00091044040341e00c9010702213072039030800302d1410315004010707903c07001085c404606040e501e0101e4030009000b40030744000d00c054164490798420101300114020510151504002440c0c240091072081c000c0c151506014800020309050103035811103c01c050388000d011800b1402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 109097805 1250 109096555 109096573
    0x10050613090305040e18120703050409050a0209040e070605040b091503011d01120c09021c11040303030e0105071b03030b031b03150601090605090f0a0306050603071202130e 76
    0xc0340d40300d5840307098425514150794601d0004200c950400141c10703e0810803070000c2d400c0c1450000181e0140d001c41da60030158a1b0865410103682c140a250300c0f009105003080f04210701c4890a134001e00e42e00500b00c408119070032102040341d903140094050200030400400c000e00c80d1030104030190540c1f0380000c02c041e60240303840c4002441600203034002140c1d05039604489016200d142ca40c980500328003201803084084689800380c0442c0140309104400c0e50000e8040340840c112481c3d0282c0d10110a81481a079003407412491059010748011350010b440c0c0015000908410b0040a008105550b24920180c0c40345540070130318221800708a0503d5a21030503c07403603840501c005440402000480107440401009140c00c116003105407000315080c0804000060307070003501460a43d103072858149d86440c0b01c040400d46400744440c41a60140c0d10590000c1048aa40c00032449690250140c5044941d00d04c103240078030b03c0c0e10000942c070812a0140b0200d9510660000e4076007289442214200e42d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 109099055 1250 109097805 109097839
    0x702040f020706051009050402010c0311010e010608061f05090a0c0c0c031b0503030309062e030b04050106060203040b0a05070222060603060b07081905070b01081b060903100506 78
    0x103880844201d412944034030400c00203c17242d10303491008000e01c1800340320034941640020040401240b000f4140030503818503100810007544503500c05c0300400e000300708003078581c44001d54440c412141000703402c00d902580d0340e265000c40c2659081350005081c1e80080d44035008648080c0c03150014600c10404203060a10219404001d034074021070050f402d60307040d0a05a14002c6c0140025000342e4000da10400c180a520000040e40507440032410709060210140441203d011020440d01c14030040d01800011042c8041111100e002d6441a0000c0003032644d00e010681c0c40740a148600318a100c42805418030347c5001e200100380340d5100802184113952042c44100d030045158040600540e80c4400031700c411500340c0300c0c400c0a010780b08852801e10f41e0541c3c03070454901c0740d400600301e10140007a40c021094001c1c1e0035039031a0781c1d20400b90f002d03035a1038009103540d40c0c41101d00312040300d646514400c0b039401c1c000100c4070403c7c1c018000e04510201d6072200000341102a050913001084016200404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 109100305 1250 109099055 109099057
    0x91305030f03130c2103120209040e01150504050103030c060e0316050a030f0e0f04020d0b10020d030506010903080d050907090608152202010f05090406031110031a060702040f02 78
    0x98081038041100ca000c0038200501602c0c1a904042030641002031844011a901c0c001c0011460f4941f030481c40480d2542c0c64080a401070707005130f41c0c200741081418451102c1c1034004603100b0840008840b40c41d0350703030001c01044d15001e10014010480c013000e0080130a4103604911000000c160440745032040640390954003484400c0141d495030400b000d01403c141d03220030808102656440c01d04840c0c162000042c400704800e017502c41c411640051008103a042d10b80100e480e1341001822000302c0f054881f0040e48804000400740e000031700e040001000d96000311852070950380c0002d1880d045c0141440c130300000b007901a090210510900c400011110035a01881c40503141020240c500c15a08600007401500701601c2c071007188a0302c494a2042d02401c40d0600e441540900e001c1c81d4143c00b400d8151400d119044ac0190850f05007480403083c0006800c042e2503213401595484403203140304c2411002c44045010916404145c032802d0328513441e010003d046018002080040c030f00700290100022 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 109101555 1250 109100305 109100311
    0xf051e030d1e0305070f0c0203070504050c0405030f0a050a060209031504060c14190309020a1805040b090a0203060105190b040e01050a0b0726090907080603060c0702091305030f03 79
    0x30766420101c0d8041c205080008040e040c2c0b90406103d2810000000740028541200390810000020090003c0d9034041022100400b4050310800031800c10070001c01c41540070b402500d0080c41120740c106040341000418185603a08400607112038012070340d03040c1c06544001c403c0c542c0b5200d00d85120094440382031100740290311079840055014441d85001e0030720501001541011740c0305108a01412008890140d503900e80352400185018442c80045c1ca0311602d07030010b004c0707502c2540c1400128200c942c070032800741c3d01076103030090705950301c4d203001380d60700900038009406420240c010403241c180640c004242050440e1000d18003601c5000603a0309410990140d14443d002100420590501d2451000030300b150b94045850000d198544001c4000b001040d810180e183d0101c901e25200340005844103440020b061424600b40075100a10340e035003e0b00c070240702c0d0190001107200703000318000f100c03042940501074008541d07030078215140b0303160301ea0019290390004104061640d4140d00081d48 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 109102805 1250 109101555 109101557
    0x20706050a0509190f081e0d050a0c0e1f0207080304090630021002010605060c1b030f070e070e04110a0e0604080c01050f0705010203040f03120203041e17130e06030105010f051e030d 80
    0x82c27240340040034102541d170f0302d1400b103081c05101302043c820790300c445c44903050000412541011514900d17404078134100003980310881900000c20081841e1056411180440d03120100607401c1028844038101c001d00d103110700014404141d104400103041001800d03900f002640000288580d50310003243ca550301c01500340229420403482410f007000b600c0d502e0b0f09034110503002081d5441030503074820f5460105004100b22500100f00140310305114540c0d2401201000e0300030b010340603151041032000c0e044210240042055040000d0540c2410025141202d00e5400240056844a0f006540c16032000b12550441e01c2c0811a05c80825424001035000d280705240175240003c072410014803c100703100342c4001990041080c03201240803140c901a40e0600c1084200304002913240805102c00d06403254402d00302c000ca800141c41c103d12a0032403c8a0511020740645d6840d40b080500300c48090040c2069000301c16824409403c106080710380490414480f20301200d84800064500310407a0385444c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 109104055 1250 109102805 109102811
    0x10e010c0c060e0c030a020d0f020a0e0403080a050705041503020403021c0c0e040803011511060106050d0c021f02130b070b150d030c03050904020706050a0509190f081e0d 75
    0x4200007080c45000b8140d0503d0001e80606501480000c0c0c1b00c1d580b45601a01c5980f18490b52400d110000209000d0700d0f034010300c2c6c420b401d545c82c081068000011202600402c10080020700c1d592002d0046c948502801c0c0e80700307071403d420300181c28034290724a02c030081015424880400103807034006040b07004001107001141620145d2400140405042d00b011240400c1c40003840b00141c0c003d0291790541c0c512120340c1003e01c0841c3e1080303920490507d500c41c01c520503e0000241590014028003051841d82c00a00c80402805002d2f41c6c0c0d05809240100300e2540811400c042d03400780d9001c0c04003144503640a9000c25600e18214003c0d800420043d5641c045080a02c418401042c41010b0b0903c0152002c0c02c040e50316890141a08030a9400941840000503083c041d0faa00c550441d1100b5600c85410411400c1c5070160344000c080c2250440d445105c1c0012072116480c81d01c0301262040e41c003000c0c541045007103648030780031a0031540c2c2582405803849101034544030703000040c10300e40004403400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 109105305 1250 109104055 109104077
    0x50709080a15051308030a020f09220606050903060f1005030a15060609050f0d02121605032b111618060e0c0703081e0c030906071409040e010e010c 65
    0x24100d400140c88070401c4251301c809000044c00c15415a640170300c041e0001038446100c90801d640d18815950b4950f40840910030318803500300c255141c40c0b0101220001003003496290340c000d035841d104d0128034603411b500000020300644600c5002a5000d209600001c0103a44e954011a00d0b200b080407040301c03a400b8440901c440c6003818441c0c1401806280f83c252016864000881c160400d4800c0345070081501042c200c040d5112001c0142c1c11141d5041124040120003220152a003141d0040b50b1007401011803000c60603055884000342607517060350074140750f508180d0580c0c10f102482000c00c01070054510501c003a994060340b41005200c070351105d01007810f0001c242c40c100c2d21203400061041c490681401580201a0300361012268035040417581e980712400028820901400a075002503404810020501b4600c400765015202d80b0b41206c1c00364503000010f0702e440c1320042c180c52405405010522441c40c25410078080304880c20b000040f256064140c3e1420340f540e000e0100b0100c1c55204030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 109106555 1250 109105305 109105343
    0x50301031b03030f03020901020a0b181c0e09100302090403050316090e06061c0507020d110d08060907050d06060e120a1115040e27011e050709080a 65
    0x340c8045418005041d88040c20b55801030003407041907002c5030405502113680316469000f00301034140c041c0c0290701021549000034032944802200c4c9000c91050007540d140d02d203006641081c0303000203811606e03849540c5d4046c01c01d0056050340103003421001e82c0700f0200000940c80d035260060041d0301035902d50703960745000b0303c90f185c0c2802c1c10560182000b00c4420100140031440b20596000309088500355a07540a00c06c0c6011141440c112990b0018a004140010260001415a09580143c80e524074900d515446261910f200b00d03d80e102140c024000200e1500d000303512250b0114450402030b05000c129201b4a084031290740040300490009000544640b81828a40002a001c00d000346503055483c1d66001d012500d8100490282007841020035602111000340d40c043c060380080c80c000c81c0b5012030300008040700074801e1540328042159445c004c03c41800f502d8105140302181c404103241641081008103801003248042024560000c15800014491400360b2030088280d500c1110700602 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 109107805 1250 109106555 109106573
    0x5040209060d150212270729040f051008090c01050307031e0507090f06200102041203030207151116020a15050301080d0305090d032d0f050a0b01020309040b0d1205030103 75
    0x1b69050700c0341e05000441074944c0780080c44405490030b401c0c0002405000300c03032800c401540c0ca0081c8441c00808200402c0038010201d43c90215401160042c03a092528002035501480c15100401d00350494075240500c4c0d40240d0003590402c01034070300040c02d8080002110320702480c60804680d00303078556042c40708007507000c1410009801c003d141d80c05201e18040001d402250080701d61841c0000c05101964201c00a5068034002c0c00300d81c0088095a40038940180258062002260010301103c0741e03540002c01441000101e8a10000781403504003156040941411001c13004c0741d103e000404041b480e0f8291003400c00380c11404e515400e440c0d5040120041c1054000dc00350000c042c80c0c4404c0044103000080c06800c0300c03195042c00a0121700740081c8195407042565058145403403406031202555980d40310b20031105100341d04000d140c030744030500000d640c006600c1a00503070050000400c42c1c03510707610074203117032000400380307036400f45030303a40314440307030340400300e4070002c120040010028003244031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 109109055 1250 109107805 109107841
    0x20106090b010c0f08120915070207030c05011206081006080105090a0c061107080111030403020d0207050609120106050310021b010c0c06020f090d0c090f05040209060d150212 77
    0x40c500388003011207030000901d0405060400b802c1881d030150f4031802c0c01614001c5802c4200c0c1d000c503941486c0341080c00700b42d13074080f022220b40c0e03c2925880000d25503031020420703000340c030b6124501000b0745141100445004d02c0d40d0060701c0411382c3e200b000043e40b540400c5010307207240140b0008203240340ba0403030311070866100829021150304084042d400040c80c000c142d400741d8095081c5980c44018050340c0903d48480da8125030055843c0a80c00c1c10800e95030b8020314440c601c00d82c00c03140b0280000c40c080ba00c50106204168020323070144105119450606e511130164403e402c00006c0145c0d0340c0740083d1400f0140103030083c0303440e8001a000c000140000d540c620584c12580280b120380030020000b0000c4800d02409000c982d4003081d8542d29249040c100c510810707009010b200200361506002e00005030b1840b8001403113141555400303120103075004070381c49a50020a65071040d5166030600c414828507880864206408010900c900c0300c007031000d4290b01d00c100c811804185840009814403007016 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 109110305 1250 109109055 109109069
    0x1e0a06030e0307060203130b091f09051b01020a290c070b0a0207020d050f0706120b010219030c0b0109020309010c03060b03150109080a0f0c09020a0207090c050904050f0601020106 79
    0x1040140000103000003c607140d499001e40010303602c0e83c0301d040c03603007a042ca118002030a401c165024080c0500000851034000c1c5038150000c031802400c030007080d0494900c1c0c130000b00030381c00c032581c0c90058015100d803c00358008180151450144c465480c80726680940b00348200380c8100110030314100c8144070030309902c070703002d2410140380811988402210010082021003256000104a011500d0741140840c42990000071070f0780340031b061540103846219a004450008215641d102c3c441c0d0a030303000304802000e040c2c015003010440f9070403840381807003501c03400c0e4184282d04070440002400200d0050091541440c016203900f010f070f141609407040705c10940c08160910a05004016140c02200c1c1c01c5a02c03002d12822159420006035410102e9500c20b400c1030061082582c107020451107090a03c6200c0c09442130015200c11006040b40100e0906100681c842081400030140076440390280ca1844d00302241090b0301c2d03c3c0060240c6078201c0b10341035900149000d01a80f5602400380c0005480e0b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 109111555 1250 109110305 109110311
    0x16081605040b091b04051e1201061a07081209060a060501050310060e130618061e0b0a18030309050f0a030809040b0a09090506010e070f0503040605090c1e0a0603 71
    0x210000048001c8005001380d07100b11042400003c040c0c03852812207005100182600ca036900980811034102546c91903400d000f0910411203050303400c41071041400b521450080820304100352844401507810800c02100c844500b006218241c10082140d140308814000c01000349203484103407141914907030f50060341805424070511513122001c101d40400c2e9811443d180c505148410f0000d50401b07100e80038900c5051030401d0114040e007907603080c01c0c1c01c5110704000744400d079541c4800f1041981e80241c141c2d039628807080103110000c4008010b14801c603003450411490b40300015a280c0c0c0120720350044002c10701c51402008603040c182904a03940d90202c90030346000d45152a48a9180308000300b043c0b160b0341d03a06d448002c0750f40c0d240048000d841c461600300301c81002c074901540c0e1400c0030f01030076114103403003000105014458811000d1040a07070741c03030a055480e907556540c09800040c0c400c0200b4019051500c6aa482d080703c10260203882540c0340100c03008035801d00105098540000b030415003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 109112805 1250 109111555 109111571
    0x201120207030e1513030507050a2405090303070506011203033b1617120403080d0b0f0306071d03010e1905010b060d020706140601020a03111608160504 67
    0x3d08101e00c101c1802c420f41d01d0021259046402c0d5145114065203031614941480c00402441000140e21081c1d4000b650b29603201c3c0d803203291000707416010300910715040c480082c484103904d11035005820500405402c0340d080002681d1507c0c104142600403020341d4025120000a2590602440034861001d1041066454074840c003004030780700200e0b60080f10600c121060744203450030040c0508a41940300c9145d59941c8400440c090721100c05a48407040c461400d04003500a118000c40e000c883e840600c00740341504200342c1c0006480511241076018002100c50b0340d0715141802514420384059036403480300c2110562411003c281402e03110301036850b010061400540020796140c80445024106052010b00d20b4468098005048481d803c001d010568014514558000c0d015082c45204280071103680c402400003018400c80e1000d0050340034860391001300e4018404420030f04030036400e8440780c030801e0040c841c988075994000c9400e0380c0004046000b04800c141c200020304011103080c40000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 109114055 1250 109112805 109112807
    0x30b010e10080f06130c02030c0d0201020408071403011e021c06080a0308150604060903120804080301030b090f03030c091f051b011503060c0e0405040c1809060501080109020112020703 81
    0x1c0c00040500b030303c084481002c1038a6560b4440c1d01c00c4a01001d032018824220111002900c0381c1060b140e49001748210112002010300600030b0390140c0d14020024030150b484c0c10311203180c61002c0f43e45141c140d580d030149010084007011035100000980200035a603407034100313001010305414110071500b09207408002d02c00c6100210307400c06040d07010302d040034132a100d0a5140c0560b10651411035885040001e00040b41c58100b00040d040340d00a0703818112028040e20305480300c080440b0000e00c001c80c20401407000640d0340c1d10503034000c4010700031102d05640340300005141d5070054400044000b004900c2100c6854058017002c02c50a03522100c020303d40c1541000342a500038000c001188164184568a542c10254001c44819103c010401241907403420400020110347e242b200001e40b40c1b070000c540c28102402114040c0f54000312641c4403610305216040c220f40c8281ca0310390169290105007012071a14004c0741d0207085a03400014000b2194030001d00701060140000741e9080c01031104901003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 109115305 1250 109114055 109114067
    0x901120e030313022d010807050a08010303050d0b04050703020c070501020109051c140d0614010807090501051c02190806150306010e0a0302030f0607030b1e04180b07030b010e10 78
    0x3c01e10b00d82d030301a0080c910002c0c00e10034003001140d81d903611268148002c103030340c4001c49291000c213072500780c1c054407091400c40700d510629a4480c0460340304001000000c0c4039070000d282c600b02d0700d5000929540002c0004081d900251624000680c001c00c0a5500e0718061260313a0041000740001c000d5100d280ea00d139a20745060500c400d1700a00c03403101407800b541c040c103614162142c0d600b0110f5914032070200084010301043c054280c002003102111180c5c0d5010303119907400f37080c094a03043c62061900004440c40c0d413141c0b00d1200301c0070b0402040a05554140044c0c80c0c1d48080844400c0e0809110700001c11492004041510424a4040302016400c1160450303410020a10306150300c5003c0d980898116051940000c0d010700c01c1c41040c990302040480c40c41d02850131740c1e41c148242c0035808200440c1d165280200300d18419044030480076480c080d4000c1b0f0301764043c02c01c0309040c089561241c0032040c1c401c8600a0100f500c030309611030103692001c501c49e081c202c116000440501d808100920b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 109116555 1250 109115305 109115311
    0x3070b0a080a050c04030c0e0709050109180e030c0703080705100b130504020303070f0f02011403162001180c0b030c04120302010902130b09010f0b160c0513020901120e0303 76
    0xc2d96202e02141c040c91503001140d01564006038010034142d41c884140f0f1428404503460000502000f1002c20300d98881e20281c030032100c050300d04000006004801500030304010088420305c2c8420408a01010b0051083c50000c50150385030644407101802c040d4140420f18002e0b6014514100342d441c110303603520130040701000c0c0340c000014482d5542d03c0424610312a01c40041c3c10308403828220410000c00b0561141c80c5813007aa18070001e21191001440c0902058400c40074034584000b04402003031086030036220300034660361482030300c4000c0da03400c40c00c4607282208491180000505038050219407105440102500407160b4910f1a1178026520a4080c2c0d0141c0c0c03076401c0d10f062100003814402d41000004680060403c920914030086d0304006020403035289002d95031413400062441500340400342101e0b03008500c0341c6401d00491400401c101c06000032200c051440320081b400c1c2c0c6420a0480c4105030720b01006030340c0c1c01b44400240c0451030000b506081941000310301c0810340b00100503250 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 109117805 1250 109116555 109116571
    0x102072102030106330c020406091d06040b18070506131505040b0a03020306131103060a080f0c1002071203080105040501050607120302030a0902040e01050a0507050a0903020112090b090a0203070b0a08 88
    0x10f10401780e2104842041e10307100041c0d8003e003445030101c0c24008a61220701000264201588000004010300741c490b081110702804d01c64105001510028500001044200b82035090743d07542ca0311100019859007128482d500b00c04207202061000e005060701904140c842414000e0406181116402142c442d80c140c1108251700400400c071142c42c0c0d2101c90410b0358070104180505107000480404507041120702d680f0800c1c02220025400c1d1010036a550031112142c0a404030404460600c1101c500300c4d8001c8045100d00e03100020000f507041c00824019101e55503c0d0386c2c5500d4101084160342c8103801942c807841041000d4070000340a19120140780105007130150b22556803005000050070320003c00313904181445400e105881040d80304074840c2d10041c1042049840f8a4021502c50140e80681d1021409500e428000f66009014850200b05500c0b00464400e05c01e50314103140180a582c4401213a000258070811131905103c2c081c040c0441d5075000b8240001860014032245000d0040300d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 109119055 1250 109117805 109117889
    0x604080301060c0602090405090f0105151e03030c0d030605040525080a0204080d09090501170712050c060c0f0c060c07060509121504030813021305060102072102030106 74
    0x3d404c000c140d80548282e031070300a20420a501d0329140715a21030082500c00c011179440d03c1d0001e1017002c02e00001d107252100c05006480700702c0a04410b04452100340c62440d6140c4001c1c040c200002c101001103400c1d8050f44c1d600070030503500d00000d20050300d101811190343d203250114a00043d000c03440070040e510285203420700b082d0b20764107030b414000e12030741c1c2000340c1c503004070083c5000380390300848260211080424100701d241c2e6100d04940c0000761030248901c1c55044210200300704881403a9400703007c3e001e1416035010b140c60700001241907010144a101c0c58000c500e01c1c1c41d42c0f03607051051030185e2400742c40700d5107040e441c20303045900e56005000d18002e00801141b00340807600c078940c425103ca100501103c0c100f0340c20786c2001d09110340466007140020800f0001480954200000c0150b03107070301a0210401042c841008000341100070301c5641148582030000684028980c105580414841a0070720300340080e005150945416800455510750a01c6c0c0e542c847e19400810b01e110980c90645034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 109120305 1250 109119055 109119077
    0x8030402090711060c07050c0603060d02130f09140c0111030a0c05030f031005090a020424030b1306140f0d17071205030a0608010b0d1707020603040f0209010503060408030106 77
    0x544030005480c00407036030fa1140f00100701c407206101d0000d10a1038000c1c02181e2122400744208901c0b40710865107540c0002e03c4240720030050600140590030804015008980780f461807080404440754a1015600140700080400c50b105080c13003d002c02d4002841c3c5080c3d0110b4011103d030f130360304c22008071404000781070310790809100d0f0034000e5500d0840f400c00825540d00b490f0341c08454410b102d000f02842001a4004a429041c0510803181221202d00c02423000c1001850b0707000c1507003600044007082c15140d41107402c880d80c400a5400401c45a02c00c0020514203100d40c1c07889401486803507601620043d40a0b00046e6200c0309031842182c0c0c420043c404076501143e03110814010300b0b00040403511144078450109810002444c403070400400c080000c9a620032941e800d885d14103250542080c001d40c00c0c0e001140c150075900c031000001c50a114904070050b40420810307801141c00f5603401001d2190102185041c000c40390042800702c000b0501e40c100b17a101c0c030000d403006102d00030a00840c4050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 109121555 1250 109120305 109120307
    0xa1220010507060207150b0108041a101707090b15030c07110d030201061503020708120a0e0f070e25031e0603150c0f021908120711060f04080304020907 67
    0x1180c2c0303019071081041d512a0024900325030f507504c000d014200b0303880c10947d8680b40f80d481121010711944c0c024006c0c1034805401a102210b40c0006444802c40c2c01c000e032404103214100c06000d400c031486410080c8082450881c180044070706c0c220129101d030304002c10021b0a1800d100580760411030394202c0395030f04c05007071074000c0c585107400d01416000700310b400e000824140c06600120868120385134510f00303c00210400c90803032103852001090711405200c6509081c02c40740400b60720800d00070001401190a203001d40c900303003a0300a0156640d0202405200010542d0000c542000005107400e001601c080480b44071001c1d50015042059681c1940c050039029030b4000542c9481c030140100311303807612410210000c0c21041c00e058000f5060400e141581c0384217500030039841c140c6a000e000480080d10300341d03504240ca802e05648500060014041549040148a010740d41640391260190078030741400d41010300061401240f0750042c0108400710341e83c202240e80c416411201261950b42da800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 109122805 1250 109121555 109121557
    0x5090303062d0909060108061e040f020109050a170f030a17040602070c12110f01200a12050c12030601050901080a1401080c010207140d08070302120d0204050a12200105 74
    0xb504941c00220700c0107105043c00c2c003082c41816213901500f91091070365007040c09022600c90f1142c401d401440a000600881d5501550b030265520515002060076a43da0015003100c065400581019107104001e02e81c48500300800404201c80b00060350500c84081000313058050024908080a0390420004082105030b03412100015403001c1a03801c020307100d060660354116105800c07502c085001074042d48510748a00da89101c00d9050b5030307440d01c150030180710800c1c0d25607105e00010503101c0c3c040340d8800962103c110401004150361400d45500c0c014142034a41141c14501d00d690306420418410307a80d90000407110350080a092a04480d168462514020303e00c00d000c0810311003503440007048514001c9841000d03040709030300719810203460b008281d0b007140c20624990381c41010090844000b543c00005042128020f0040d110f1a41030903600d504a9403260b402010303002e0f40080c1c01c0c0681e20f00400c083c0090165810402c20307a44e02070340c4a506c0051a403d20b0241c0c0c20b0f030218002c00e2680303e40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 109124055 1250 109122805 109122889
    0x2031009020d0618090b04030f03090f061505090c031b070213150b0c030412060b0a0b0703021c050715200405090108031603050904090209190509030306 67
    0x542150b8034408030703100e800280301c9030045404144403200109211541c90041d01e801030340009070b070800c940b06d0f558166250400c1d0007100c0b052688541403030b00401d01105844d035080e40203207000b02d03604010384400d000c03000301a04002d01c5004420140301d101d404c944140d0b50f000c0c1d50000d0b0001d0004581001038030b00c1c050b00100a49c0020b01880b0610308503c03a801c85201a500030804900e607540b12740059a1038062818a038900d548180020016121b5035200f17495054020480090589000f001146601c20310f0781002200c100f00007441010154100300c441e0780c903034510b084604514050380c4010018440d4000c0a0303c0c1c03504102c10940c1c0610158000c1038030840da260000389130f40c080c142003403c81d0014402d5070300c189401d400014029070040200e84081203004c9a02c100851141d805135019008652a6500b1030b80d00c8a024006858491520303004810255402c0240c11615401005994006003400d031260018414001c1580780c481d10000d581446084030140e90703c046030308620f051112 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 109125305 1250 109124055 109124069
    0x3030c080d0c030c0e030304050105180f19061403040309032310060501140c06010308030405011103041a1303020601050111011b050a0801060c1a060402160c08070e0603060a020310 79
    0x42045120103e0f0903502901101080d516440e4001d40c601c07080548a02a51151a012400c10030040540c0c49441a110800c0040107040c5016a0028804186114680720380e0003850700303400b18203120581e0841c18204160321744a44513491032030325580090408116100c020807150300016035200d400b400b40007040c4004905070481c0c81c0f100d14814980040e04043c0303d1a0f010466641b040c0d0080000340301200d8a14070359900a0040c1c2c0d1a617030703c440e00c0d64401030044c0c81556890031a0503001c4202002140528000c10b0750b040c000042e4420010141006003600d84050714031325249001a4000c01d0301d038110364090a00d0480c0304900c2c01924003600a400500c40600481c0c02e01c0041150420003a0006440699601507542e884070004d480c14101000040d201c425203080c064030140040800a0f40404003074405030401c01050a0a400180715030030031a403010b2144400e01403400c0400c00385000f408142212222030505202180d00c2d800080c0001100540020004680c0340409074081e00a10350 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 109126555 1250 109125305 109125311
    0x7020d12081b030903030105010c0203030c06100f0801021c050717090a050601170709020904020c0a03080109050c0f0706090f05120d14010518040c0b070606030606050306040c03030c080d 82
    0x1801041e4a00855015100c03890029014402c445510162445a18044020340c5541d0811005490240040800300d9042c4000c1006a408407014006140141c058003034181001c3e003408030f40e0655610b2a04403103441d80c418840d21240e80c43d80b040d021039140384c2103c001380d103884055045a01da41c642c42d00c001101c1090040c055207003000500c2101d00f03801103080e1050703a40c07104004224020100c000c05225032203007000340300094240c0d00401c4010002000146441d00d402d0a1600340310045005801095040c2c00403c020044c0e40a4580d21034403d8034120301d02404a00e246c03686006842010300031941e5640030504100b10350700f0117404e49402004495201c0380e1810070a490390f0003110314411407418440b0344030300b010440042c64140c81004080c4c045803610000d00d80c00ca284010020784507000c013490000b4080c420203001b488880e006072008503201d0f003941050003e0300e031a50301c0b8500a9001e14200b0011480d910051020f0300e0385440c0030115400b00b410420003d0241c001440d05545c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 109127805 1250 109126555 109126583
    0xc03030b030328172215050603100b0a031401060302060408100605010801030305070209040309090c0e011413150302040503060705030f16050f0a03020c030408060f0c04150507020d 79
    0x211900d00c0124080f071101840c0580551034110f0700c003402118840342071021140800c00886080000c5c40c420507880c080c0401c040040c1d1036061800c2884004e0b40e10913580e030014031050b810300380440050317008204000e0000e50b4003003008c170728074041c03d02c00902040c1c04503485224401013900004011600249a40d484944685d0100c1d201d0007402c0f100100704d8030f8036100261950082c51040d048070740540382c1c00c0c01c3c001140c0a20890b5080207108404000f079187c40031030b031207400b84500c01480031583e5440030800e03000301c005450384200212030680c2107800d00c0120791204806915000b658900303681c1d0b10380b01c0b0702d9650990203400345420084e0f1600901e41042003199001c1c01451042c04495051031083c0c6801034903000d140300201c100400120100300313200f100f448080042c11344100f249001460208210443ea06582098018280503003050060004c09200e03540340640110324030f8155880c15140803060030a84050484410034044007091038400c1d944d0b0388210030480780d00100d1100f1451 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 109129055 1250 109127805 109127827
    0x901110d0b03012307090e1e15090c1b1506010c0203030d0f0504020405180c0105160c0b071a0112020405060a030609060605010f02030a080114060705030c07080c041107030c03030b0303 81
    0x5801700d0702c0c4400078502d1003000a4200d00502500e00528031481d00080f004a19041602442c00040900f8000d0010480116281c0c0707840d030240303104103100004151604130f4a41821649144d840c081c001c20b50081c903090103612940f440290b045070090a048140c1030003440030a0550050041d58048513182140007181d89509801c090700c128404c41c0e04105a9403050314269243c80280c440c2c43d070b50f510100c003540040d40512700400008440e204c0e00300a030703815661203650209194000c00c01812000c9195420009800210302400da880b040c0c2000f00e40c100080400c0d901075580e40039214507200c801007200c0d44c45440703007200030f180c11071030501450003681030400240c0f45600c0303414009440c3c01c110040e01403021069501059160b0b56100050346805980018030030302009265010f8420080480024401c000405075501c129024014641c6000395080c246020140d24a00490407c0030300c01e1541c4a4100710340480758942000c00c40d400550030210020120340700141d42522000a82280d04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 109130305 1250 109129055 109129121
    0x80624060a410a0804060f200c01050a050103120c170304050c1003021309020904020427060f120803070201110a0c0203010b04020708070305030705090604060f080901110d0b0301 78
    0x28410744244060300c030021a41d2100c1c0f00395041500099103800202c1c0020b440c03500000034001502c68081140380c042d0405c288561a0000751b1907034003c00050f205141003080c040c25a10a00450b420070040d1b1640c6c03500801d25400071204020002582c1c0c0c600204211b050684544492043c0a9516882c0500c0c1180d5551101c251851048000c00000d81000f48a03000b00e410310010340d4215440503151600d460003940040d040d007030344150248004560301d044030303010340d4004440d0322942c24a007004441580841ea900d13080070424200100c4180031507100e950300708001980c84080e5a0785c9603120341040b401010000070b4401900c0c0005071503003a03079074001114400c06008074005c01090b030078002000202e00c9008002403000e034041c0030a00110740200301455005a070783c204030b4684003142001401950003900030030046005d12010400d10740d03011618550043c8014003c11258030303401c4003800203010310314900820765101c00819180b82c82c2034210030044038800700c1c42046c01907010890b20720 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 109131555 1250 109130305 109130387
    0x109030804120201150b0318061909050304030503120103020a1401020c0f030a170301060f03051b0715020408060a0b010f0c060b0d02040516020d18060f030207050313080624060a 78
    0x40144c48c440d0700030701001044050081d042c040c1c40480c403296554802010f407682c40001d944a00081c40008081502407005040f284800b40c8840d2096055204212240d015900a5640b00d102c1005400240c0d80028850119001c00c450a003c1644242e000924000020800506404c0036034075504e4008254006141a50720030745840403003006184088040b45d9040f603210321007100302d00a0024500c000e00007003042c540505601e12004582d002d0040590b07115a0007224590710070010003100e54001d2140d06005482468110382c2600a030200030568a069940600341c00c2d41d51244070315641d61084c01103035056020f0820300480c0f51903a001406040c5542e02c5030090b00860207000040b030702c80c40b801c80d400c450800c100c4c0d00007030800c1e404880307112200d031011080c10b90810018000c950300704060540004480c490061642c180102182080400b91a00e07590720884207401c206100d070304d446601c01050035a41c6549440301000d040303456080070003811864100004411455071031035854441 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 109132805 1250 109131555 109131571
    0x515100b07030f120c0905060304060b090408070c050105040e06040b13090b061203070309030803060303070c0909030e0105040b0405040e100e0a050c060a12090203160b0406110109030804120201150b03 88
    0x9040c44d56160000907103800303800b20300c001000644140305c60300d090005140c0003806a240081c20043d05d4020613109801039800f40d8400744003183c0c10303003041710b403080d1100508020302e0a24146854102c500c0c03411480a00f01500c50f41d26500c42e840142c0340e04800786c1c000040600c0500c03d140007403c0c83c03150040c054500311f0003080300e008100111304c400022680b1007680340c2d49180485180d5212103580f030300042d011b55030500003007081d034001c0b035050031101000e400d00003400180d1540300d103005480c18007402e0305d0b18140042070100b0051860f841040d02c0884405442c04600f0072125040c040c200b80340114100103143c40c091301c0000708400041c0305060940b18408a652039000c210400040f40500c05560b40099407154072018101c40ca40c011070741d80362026049034084400c9484428009005130040c414040b400720b8200802c550101d102d9845000c800c00801450340c0317503100204081c900403c003410000340300403101e030744500c00d5005801401d1807500403407032213882d81204000d43d4815a0024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 109134055 1250 109132805 109132817
    0xf140c0c01050c03070206040305070606030804031518020303090f060403020622060201020c0601150e03010c0e011b0506070c02060418060306050f0603061603061706010305070b070515100b07030f 86
    0x941414a42021203005d007107150014803c650790390341c088402d50b00000d4200d5a0036141e9000100061042d030140c0041c40c460000c51394007818064202080300d8025000d10040c04842a80758007680300402100c0e035a4406072140f8046d5040e003408502d80340315a90009410407400250b4900c10040c02c01c43c10346050754800210615651084101d00380e0148454840d4260840ea004100d040c8119408000005450070200c806400d00c0300000c0c03c40390703140640400700340705141c000e1407580d100103075003981c0800d460320130490b0003603840301b554510000304000b0521401ca1008029590b440301540c0003800034005840c840d428070080c0c6805880c03184021600e207030419001c64803692201c1c180d98483c05003d4000c0c042c55235034088840682d110150310506242c0c1c0c034140401c031100000b0300003000c03c107148014440c80d45149032240c50402c41d035015011740401070040200045001c2039451002034003600c80103883e203401c1d03041b2016460317943c011802c2d4100001c4207020941c200f0b512a80080c1d40c0d403180 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 109135305 1250 109134055 109134061
    0x2b0603020103200904050a09080d05010509180304031101140a0203090307050901031203051906080f100c020d0c0302011b021501050303030705072d030908070f060801090f140c0c0105 80
    0x481264140b002c500300000c10140034520340e5081a900055016140501c08036050070f48c0e0700c1d400c401d90701031b1620b040a42d407144010300c8030741081000290842003969a00703020310761095407282c6030302460100425031188010a1b40681c0c0c0305802c1880d1503021504496500c10347c0b0b19000e540c0c0e80c0101d5669000c0d0007800340c0040c2d00c4c981605001c2c100d80c1c200650310100303400c0046c01c40080800074407090040c0340a120328100710080344941030142030104e0040c508042c2e009000d62400c03910803001490303a8142590801201d40c041440e0400d480300c0e0514030482d00f59458143e015110f1080101a0701c0d2004c80d602c10b4141d80050042d10280454013102010790302e410905803244011241a030110307008110b110001000c00708500710746564031300a201451805894494015013403e81a800140464014030003040c042c850b100013401142451a034403890010701a0410405214842c429a66070191081c03040d050382083d100010030602420700d134600140300d04096044000d090415600c1c0c1400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 109136555 1250 109135305 109135331
    0x1120b0106020c100f0c060f02070c14060a11070e07050414010f020607140c07060201021c05060a03021c060e071e0b0412050708100b01030b09060d06022b0603020103 73
    0x8a140c403440081c142480c4481000710903520300d011720304c01c20200100f0018250204402c1e11030310341c00107460300d4056540c5034142800c45034100d09420071030030800021240100d03a078a0400302c031803030005800c1290b12512002c0580b03003041c2480d4007040c400c90b40d034001c0103003032079022004100f552041c01c0d040101c40600b03401100c581c025084128090f0340001d0201c4d02d4540901a520000d202c03202e007540c6000f1503c40800d0508440b41d212a000d03030f40200d444d200f809010b00820341c00050280041181d4074014000440b00200c61202a0282e4041e00c4502651100c20314810700c1c098000105200e43c4105040c036941e910418070070400c200c00c408506c83e00606802e5401c00032501c5502041e410a0b0409400024030390518a08413146e20404800284040e02481305e5418050900000900040414009025141c1900c44148190001ca0800c10942d032005080e40007160482030040c0c850103c1800c5088003240c800042c0e40e0442e01d00720801048140c1d07005501943c1c403e036010b20150301e010407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 109137805 1250 109136555 109136563
    0x21602092e061709060c0c0102090303040e01060311120402010e0409050105130b09011e0c0207080607030203040303050f0405100b010504091401180212070302090a0b3001080a0b1302030601120b010602 88
    0x60108500c5d000714011030361a07442c3c0c00203000240d103044c000528007003080c0002480c552090340810142000280104222078261240902d00384116001c1490044000e80b64102c10800030030007414084040c15a40040e00c984d0300040c01d80d036004000700810704060000b003ca90201400858207000c141b00003440d040018040c8094205e5080490041c00050a40721030150024050030380c2184a03514000902e48801c114180c000c06054600580d00d04041c10700506030b500080c104c005c111145c4040c0800200002450300324001408000140d500d02400121071a1050354040c003205410441c403001e41e10802000303d4100c440ba40d0845a6030035041c07210307006074010a5081200d03411841c0c0003440c454001e80051601030001031101c40c51a07100c00007042960000c8201d001c0a20807844510b0304a000e04034100105c0740b02030000e1241c6d41c500b0311007640d6400c0102c0e005150028100108000740c4209034841043d65005041c1c95282da12a000171030500003002c0706651500701741c400004c4840c0082 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 109139055 1250 109137805 109137811
    0x51c02030a090303140906400905130501051014040506010822050706120b0922060f0c02010b130507080c07030e100302180103021602092e0617 63
    0x1485155502d440e64400740c4545524042c0c140d50f100382000210026a0750000600720130803074000d26102c000d00d2080c030308281c0a03201045081d520250750f00c2030108003595640002c460080801094503034418510034020791b6403071030060482d0300344003c1c8059014822038001c207170ba0401c280300f46904084010081514070540703441d40401c4241000c2004540c0b5034950039a90003445081855a0800b90740307040ca009a80d038819000540d014145c1641d41034240201c00001004070358200e00e40c2004181251000c1e0360103600002401c1042d000c2c420804582c00420801720300c100304110b00825450060301810f620401a0311038002c502004c00101100c3c8503d6001c0c8403560b031050051350b0f07440000340084e40941c00030b9040c000e0207100d40c21950f82c2c001e41a881885546d5000d43c440c2986200042c1ca99001d0f81a80e0500d40107108080d1100c00400514656640480303003182103441e803980d00040d02c8940f00040304541c5482d078022a680f1242208001290081c4c1c6d00d4080900f070070360208035901026 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 109140305 1250 109139055 109139057
    0x10e011704030305041a01030614090a0c0e06030a080d0b010806060a0507060c11010519060803090f040c050f041e05060304080a0c05071502061801050c0a14070f051c02030a 76
    0x1080c04640480e21a07400117600c54460292145441c0c0c1c00414021040c20907441150120b407200428081040006400ca422004150040c4038141c0d644ea01c1c10244011400b8a070310042c42d400024040d0755080084481254102c1022645d40d012265036030080c0032803400c618081781000f004101d81d0b0030030004490784189a0342c0c1e0641808102c1d580e190107052000e0000302080300550f000e10b07081100f8442d090003001d4058201d44003501c441300e14001e4581d80e511034072403600207108142403500d0714115040c40f10384c11500010900f101c40025207543c004c0c02141440c00d140407030301042254040701100da40d1001c515914500e035907901d003008010301c41201c0041454106100c41c3c00072740c1c058146840100d1145003a0784480d03840b40131629003100840360801c010b80c080340501c46a800c41441c1e020302008003070024041d85c80c04a0b8055410300c25000e07075104000207903420540000c041c1c0281c80301e01d43e02c203d2803070080940f8181360b541c69004034030b420350003190f000c605006140000110b0302c8940302 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 109141555 1250 109140305 109140347
    0x120302030315240a0e04110720181f0b0703020c1f0302070507081015090e071505090306010603061701091113090605040503040609060504080303010b030601020a0f050c010e01 77
    0x40e4904241450704620b400d00144245031754071050980c0c80b40103400b0f5811b040d10f0b83d00c0d21000365003407106014421810010704c9140d0507155024035143ca20b0303503802210f903005c515025078444203034680d500d0b1b0710402d20a80c00d41c0200008034030214407600901840d40a68200d51500f01c00d034040094002080d0410040d1030702080d9001d40b507034080d0b000342041c2801703441a1040580c4e91550a41000301814550410541d5102075040c10301001c003042019202c500b4040028002d4403441d0f81c0e69640a0264101c001e0f5600c00fa02100c51041c4225184448058103480c1d842d6910600a809410306000f2021489450840000f96003014458280c1d815009070b04030f94954803030000e12254074052203440325015161000000414024051203004511640045550b50300d8448020612480c0e07402180402c4402c0004019140d00041034034151400405415070325100d030300043c0c0c43c1c9144100001c042e05010401842440300114920f0700d00a003c0e08c4240c0010306400046030b20030560030113034582c120 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 109142805 1250 109141555 109141609
    0x6010b0a0e0103050c070b09061f0f0603270f030906020309010f030c0903060510030c0f1413240f09020a0c06020309010212010305160605031509060a120302030315 72
    0x84a0b801c269004a613117510146400c40d80e440d030f891503600441c0e00700341c0340e80700c201808440312140b000d8008e0310300303101d2180424500704403240300304140e14440c1c601010f8443e8400035400c00710b404001642214010415407412552a01600c800c2000700c0a4020400503c00000c000d4000b104503244154141e4560108266084c0150028100001220104044000080001070039441200d02070001e40901c0807140c2d185182c42e05140e0703043e410020b0b4418240d0001c1104120b442030921540000f180c054250701e020300780800041c00c0d141c0010100300c515150300902c0044006481d804e40d00c0c22a45820160749881c42c80c02a072140b03900c5e6100054a0780310200102d182d0781d01468005000c0800503141884003200d80e80c9801c004c2e0030545054005220035a040a401d540b43c100405480c10300c68114504210309030b1014640c030f0422030003209008001610f82e5603601c000301c050500084d84074540ca8050500a59030b07002103400c02c04030b4105010b003984604e00200c9241a010390404885a802d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 109144055 1250 109142805 109142807
    0xa11010c050c211902030106090c020703061a2d010e0105120901020c03070311060603070f090507090803030709030606051807110a020a03030e0f0d110f030c100c0506010b0a0e01 78
    0x242150444506031452481c0307105141e041131005811240d00003d904020346030500400d400c450700b0354454042a031501d41c000240680105614040303d4109071b00088030241400d840780381c01e42541409030320400b080c000408890000003241050348401c60562800840c0c0001564103281d08041640800c0007480036a1442d14034035103a59015902e00009400c1ca1034100b1224038603000721004401186130050b94250700b4108114a036401b60044000302202c2d458014103121140a40c0225015151601c0005410078002c0c3c451400602500c0e0450f0341c1d9107040c010003402041d5602040344c54604010002500f440c0403c0701006c807264803880303002d40703440b010302c155032100c004140000315015041c01180542c0d141040c40000714002d440303803041030800038100513030301e445804c4042c401e440f514042c0e40494003c0c00424011181a101c4034641341102c3c1c00a4509400c0e0340700c0c1c0b6031094150b024014515030081c0800f010302d10a104643c000e988410400030b49024444030a000180c0050741e580d219 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 109145305 1250 109144055 109144069
    0x100c0b040b0a2f13050405150112050f04020402070201030b090106230f0a0315080307030503071b030c030f0203090d11010e010c210909050906071805090402090601030b0d03020a11010c050c 83
    0x20b0311841c0c940d06260707548034041b906032002214003400c1c8002c01041c00700341d56040003851100184c0c02c0800c0102d0700c0d21000c445d03148540644064011a4041100400c59029620014207031070010a010150b60391040c00a2644902e10f90850100121043e10000918107000740d45806a42040c10b606000b0791000031001001e9640300041c10000c030000010380c0704400d2004000142c0240e0311140d4a2030200710107420b5202d100c007000c500c10040b010020100e54022400001c0540c1490700300300c40c40031100100d2131030054101e16503111a01c0d0503208100450001c4400b42c0c510207880b402e0440d99002c0054600c80702c40e00c0007502c05890b0610b020518940660403a4041d81ca5081030300d01d8549a114400444504440c20411030748082c0c1840240c0b03420181008050030310740485400d050a01001c21095000270300001e000d821080007180c0103a0003a0003402c0e02e44805800300d0b07030303440142c24000d6903540703400c8041d18090315140c64010f05502c070380248140c06410500600c00d4015150512020b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 109146555 1250 109145305 109145317
    0x409080403020a06020f1606020c100909110405030c04020a1202030402180c030906011401021e1c050301031109060a03080a030f020a09080610030b06100c0b040b0a2f 73
    0x42110100000300069484029030400740120b90300034550074100e403001d640303085860046c1045403109000d00b006025030009454160040603070f48480d200301a00340686050303c0b1a008100440e04114030280800c84030000307481103940c100c3c00c56480a44600a0104278440d603030f454000070300115070b181c01c0340b07806400543e040b9201821411640702c0360b0580b0304468409840c0f07000d017600c00005014030103a082041c2c5000d80640202e03a4041080600080d64030400000a13102100c00284400d103004000d000b04070039a140a080942d0401120600030100e603c01d020031200e03141c0590410220382001100319129000161441202e40d0454543d95020b400c60310100042586820703610840c803095002810074400e0689032450b445040910050418000074031203c401c2d010380504202291500310260f822120545078000780c8000584201e900700b04c590303c0500346c081d16105010411031068490380c802e9640100c104000d40651014458810711420001003102d0300e5106480a04290001821 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 109147805 1250 109146555 109146563
    0x302150c071401020316260d0c080c090d0c05060c030406020607090f030b09010b120c0f01020f06070e0303131805010504020a0c03050901031413020f06070f12140d0605010e040b09060409 82
    0x2810107001401c605c00001c0c100d880140c1f030f550109003d403103907215000b20200c0203041d00340b003080382c0f40c0800031006600413442e4180c481c242c414100800d1021558110024100107820940e545030b044411664039070051251303000503c00c031000150050302c500740000079120303040703804284149141c030340001c02500035054004655031641c059155503500303a40c7da169a807000b0003408112044004004200c0141070701d49056400c10080d007045550701148141d400324590034444090300403400842c1ca0340c05510402202480c2142000c20352020310b000c5c10350b00800c1483c0a010503030300c41e400d000c01d90003103980c03a10124540300d0031840080d018401400c848501850005002600c0c3c01703401541c210150741890b07460f4400030000c400d604201e207001c10200341c1540c4c031034a80710f00399540b560041c00018001e0452040c10a0007024144260240a0045d031010b038100d0329103406006c0400100010b01c0b905000c15403054441c48c113410540140101520010300030901d5542c1d000c00c0c40094011103404503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 109149055 1250 109147805 109147823
    0x31b0503010504050709050a0908040308070f0503030406151505030406110903120c0c01140d02030712091208010501021b01080c0c0102160c05040501050d06090203070302150c071401020316 83
    0x1246549092088500c00c0f40280c000300005403904d0140004c0305c9002e041c1508160400d0210008a20341400302ca088036440b02210340e80d0300d03940c1808030740c01c4d4400710700400c14007000060000b48210340d0005800c840700520003c2d41180d40341d4014503103c0810070444003040301400040c0118919500c00c000d0b28590340300035803402840c0c02c0003c2c100040900c80013414207010651a40c540d000304607000040800b03003032100c0996541d10306003c06004402c00391007000c0d00040080c3c806031158070102c01d8503c0e03120041c403601a1520340032070014883c003280b10004440e1400054958400150160300f042070b00100585400c042c401182d0307110006003c0386614000308010645ca40091000307201e11406010b841c0c4400c10107243c402507500041d8402c40c400d0b0309080c0148441d40e1385042e5116016030018000903010304030320110341002c206502c040c0d80708803614201d0744811040c01c01050502c0855080d54642a00c03a2108641c06400179461401a4000c5c4100d1074550303c400300c810003040c00b0300404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 109150305 1250 109149055 109149059
    0x601030203062b110906011710030807060504050c09101a0c07031101080c07110904061506030b0102101a061606060915060c02100e06040506030c0309190309031b 71
    0xa02c20185141071a0300c03903e00740d2600e80244030400100c100d032810301300d44801450504000003040413070f201a02c200c200350300c0c00c04a80280c4888100e4801154840c1000d600e071211800c2400003000704a4041c0d07018006c5900240f814605a480c0d28800c17141c0c0c0d089400d80c142010003400540d82c130a040e0003031403042001a030f5511041040304100131446049540f00201128000412100b009008110000030034811040001ea4800300f0381c110040a4840200300c0e90340c0e04150700a844409501d054005d00d01c0c174003195080c2d043e006000100400c2e000c9941310b00c03045c4440c1003240c14070b008041c01c01e10b440d2407258592031b24000525022864a1090b00c00d0b6160762119401c84026134440d500f030f00d550344981900c0c1030042040350b005024600b0140c000d03203929008036104400001200d42000341c1105820256079032030041c0e07401751070042c02c85510b174503101082240310342c42a107144d4010712543c1c084c1c550007241544161280795040e50703141780e030700d245582e00b00d00b0000c0301008004e2800e14001c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 109151555 1250 109150305 109150339
    0x70801031b2d0501020304030c03060f0f140103030e120c0402030901110307030e1c021509070f09090204060803090117060a1508040201030c0203030603070b1e070803041205040e060103020306 84
    0x16000e2030400a805070441c920058002d908000183c0c3e0080d8195001400704101040d40d0112000c100d0740c000c400410000e81c440307900300040410780f0a10110070f02c0e007590480780103503800b001c0741624400d803640c1d080b2160034020000340b5514203048103c180d01418000e01c850801d6005103800694000c0003085010304012006000e41003260100d0029541d00714a5030710300f800f0441d0115903504054194544d81100e40000d445540c00a41d05001c03070208001300d800302c4010000c3c05c00800f6500b8850b032707100b42c807250020050081072106034070075420041d000c51080e101004803103500340143c5905c0708c0d8900614240700702100c000c01c4550b120400a000151034444290a04041051640c488c0342d5840c0c1480050100c0380903620620456006208022680c0c40001d0350b601640c41014140e6100e51802a00a4444aa07410402c500306c00c003113200070801407640c02450180342b00380001201a07001d66000c03151070046110300540549441c01050455020b0b6000319084000035140740219040015 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 109152805 1250 109151555 109151579
    0xc0f0d0f0c18060902030c030a05040f1403040509011a03130609020301060b1c060515090d06110301051c0203060606030c0c0d1e02190b07020f012a02010203070801031b 74
    0x44000036070754400c1c051000503101c2e031203100301920b0403071021415030801c208004840c0c00000c1c54503000c141d854020500340b040c02805501129489220740c00310710b401e1444980c4940040c400e85001b400074000204e104450041d80c101c0307110303c000381c00703080d0390781c0c42c45842520342c019006030b480ca95034003440d8000d070728207006180c05852050001c1d80d4580e80009010240020682d000380b00d07519101061001e50342e503450010484100c1c10b80030381c494540c0d01c000380d01e070300e0b80c00d200030103107442d0414201403070540ca00614101d6100302c6601c4074150710000143c010f038185520096141d0860741c0000d08514040d0059600701c034030441d80c80d0510380c541c50130b145081000741c500008148060354840c00035080400b9007134182d12920241c81f40400d11981039025245103840280009803180004889034820880700500001030350082c8603c1030304d010741640c508000b40614051043d103400d85a80107005000316030095005990380d010503841c40e1107549124000c0c0070040142c11030700754001000003c0035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 109154055 1250 109152805 109152809
    0x60b0a0b18100503060906011101020c06010305070e0f040b010504050a090204090b061302120f070c050a080406031401060c0f0804180e06060d17090102120307021506030c0f0d0f0c 79
    0x101184840044040030450450400104042000000c004201c17581e00c0c1c00590703a4102800f82000311441044064160180c014084024113130320400c1e00000606c9400901c480444040201c043e0b01e50700c5016101d02000c0701100c4c09810398020900400090600e54410340e48008107031000107101d8016400a02510807a00c8190f0b64120003034144059490710381454002c80304402c03800c51070b00c2c02c94101500c3c032450080c00040e00310a41c0e40060001402002415030080e80181510f2960401c0d1030a501d0a8119000c0d110001e03191020528030500001203e5045c1d54a07178030b4000300c605060b650003251000e41402151951810b010001e00040075038011540b041d098640071500c013400e80055440c00c3c2008203418401c1e041d40140b1408128491a050b46c440049950681d60781c403114010307487c0043c1c00451a420180c00020000010341c04540c4202d00c9012450f0700e40c158895408240c1d403285c2a0442a60044603a18888090b02d4074580801a07540b243d00310080c810140e44032075000320a15 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 109155305 1250 109154055 109154077
    0x1090b032e0501120908040e0c07031e08130201020106180f0f06050a0b340308090105091e0106050a0305010606091203080103020d0303090204050403090609060219060b0a0b 76
    0x2003601d40040e1008602030303200c1c540c282081510360500c0c1c00c0000f88122200f01d0140d024594401000c011701c84204125005091801c000309510b0406541c1c072075059000d0b41c419800558002058444030315801d00c80c030020307540d640d100107090715005d034024460802004200c1c1999030318180000c0d54464800740454000c450400010212a0607406a06499501020003c1d0603c8c0060500c155a0b80150792010f031080c181e0341d240c84e81031821010b4a201011130983c0d01010341d11080d02c1c03015007074043e8200b80c40d2107a0307118a46034075007604a41c2602c0c010758414409800c220303203500004080201c0b004280001100204c0c040e9903c0000c60401da001c1d80091740d050b51a190144149034211140c00300510126010844034081501d0003400c408040c04000d1081c4000f1600c3d10516110750007840480703030024030400050500d0301e006802c0c00e17a03e114800c045a804900014501d0000c201454580d00341002443c1c0c3c0315150340e41030003c1074004a11540710b4541c0d4004a07035035030b01c100546802c06107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 109156555 1250 109155305 109155331
    0x3060807050918070830120601090807141f090501030f090b040503030106080f07050301060e15031306110702010e0d060e100f0630061d03040e0615031501090b03 71
    0x196030802000d020302598041b02c0b010000c0610713409480100204c6407402c80522a400c21a19910012602cad0a142e42c0183c1180c0b00d00074020443c40304900d41001d285000700e8604224010308000304d5844070410100e0004242c2d00d84080040c1c1d400b94000d00c9100b40540c1c00000c0c01a025038036801d45e01030a56041d181548040300600806070003031040e6070480b021000300b0a40345401d10009010303100c1401000e04014404007900c15079181c0c40700c2494113842808505032640340c8840c11114883c42143c0540700780d4285000c10500700703844000c58486e0b5406954100162108006200202c8110b04040b100f10380e48190010b521041840302401c3e18094a9010611284450079103098820079000540d01406102c190b07601951800d01451641d1110f40e02000b8440e010300b030450041c170b8403080c01111031781d01510250720f40b80080014000c2e2145107950750031645412042c80540144c2034040456044100081210842541008105000140f40415900341c4403000c2d000302e82c100b55805500070003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 109157805 1250 109156555 109156573
    0x90c0803070b01170304261006080c03010b0913060905160b07051506010903030c030e1002030c0f190212071d060111120d1503020607080403050706030608070509180708 74
    0x1060034107001850700044c0110706050401c12405401c05448143d800110050f00907003c1105092019508052400c034081280ca507aa1010b0703610740c1c840f00e40c8c05100b9442d044420100d407a000150502524000c0600c0c52004080d40da0400200380002c0261000e204916146048040c0000814050455891560344516051910307500d44414890b9101032110762408001d0070744da108a28074110398052070035440820503803e0580d00110b98044440c0c01c00c031a00c0c04140c126400100a041d5900e018088400c02240d080c1c201342c6401c0b801e1020f03008045400b06003005840c0c4101108081d003d50420348040c0340c1c1c0c0e55152041004d21012500602081208105e101e60700074240501c03000c0d01001920003003185404000f0070707124046500b000305075200c10741d0100c02401042000a0340c0e001e1301c1a90303651068100013082d038001e440122130b148034104002c0340491007405480100c03230001d8020520b145c104010001030720801403220802503000010310f1003c3c9003c1002c02c1c01404510050142c8071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 109159055 1250 109157805 109157819
    0x3090b0c0a1e0f0c020402090a030503090a090605150c0f01051311061206090703060305060a050a050c040b12151f0e12070e060f130b040b0d03050a03090c0803070b01 73
    0x640451000005240000704061810b5080f081c9a090301c0894a0140c18115041c0300080080c0070b081c00081d00404910008810480000000e05002034122403580d0320b60743d00c15960040c7e915500405422094007c03160310483e03003000203000e0b41000ca000399803c001c0051115400c6402c205c0300382e00103000b9990304506101c0c2c451981070031344406458461500881400740c514005002c1d10081c082c030741c0007000440451180e80128007655104e41541c105003411070240740940007d84507080d209142c540458034a5403600d0403a0100c410010845051064030112510030300d000074aa407100c0311070b01e60584c1c003561b0340d15080245010440200100c00c03049140c0148264a44c0c100c19000b0b40d440511340c01052000503036002142c50301d948102060b96841d0100e02072019070b00b8010341001360714100841000840c0c03c0000c001d04144c2d81000074004060030450b254901d24400b401081003000040b44562007074104000c0c00d80925035034180c1e01e80c0c40c0c82c4c16243d030388010410b031108080740f80144440c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 109160305 1250 109159055 109159067
    0x1513021306120201110f030d050610091d04050c04020721080705160f12021c020d050f03090106080304080a060b09040203072d0e0115090303050f0a03090b0c0a 70
    0xc000e994080207414200340c81850240301103880a8184400d10703054459001041041c0103010485c1405d40307031915081c02c02c2202401c1c05443e11440b582004000070309941c030503103410301122015041000721034600c076030004070320b280580152064040c4c0031a020558440d0f000900d1843d00c28001600ca80c5440c01030312a80e07013203044102080221002c10f10020551040a41c1c00b01080b600f041c208080c03140c5807036446138882880c01418a000284000000d640104851a008161a106a401030144242240c581560405240204105000d01400b03e4510740103194400000c400024220f52100c0d078040c50f50700300398056403480d80400c0014023080803038040c3e038010350020b440380c0c5a54202540060b403a00e040b402826581004403034902d0402c04910b00442c41900c0c506268200d06e500c880d00203940403024020001d0b0440d144040c0d1148034030410003601200e07090b6890a007412542c946084256100e4085101015280c9070f000001c6030800314401d00a40c4a01c2059990364000d41006d009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 109161555 1250 109160305 109160329
    0x4808010611010b0102120904060f03030917030c15070216030c0807050d020a0614130b07030905030d08010509060f031b0a0803120705090112140402120a0c050f03151302 74
    0x1d540d051950f070f850300c2d90700001e00d4a520074050007030350740780d60038407001c81c005008070b502010300c46207520000400e058000000c101035a44440c15898501c800030821741ea240b09482c0785100a501001c070152000402c5582560480454415034283c4011040544014500b9803c01e071604141030004101c0814100003800040c038003540c890120701025000a424103110f4818541803014882800e000000d00030101c82c101075030300c3c02150702d4a85400c135010701030300100401c90101e0507400000ca100d00c1d0000e401c03030302d80401e5510a55180e00307000a01400ea50080d200070303080360313040341d50700d101e40d40c180038034005024150316000300da5041804100fa440001e60058070355403c100030b0032034280300b050341599024a65062a5030b841c40990300403074521000340316518255142070120150034410008450195000312242008030030200005034841d40702c0030005000f8006c0100c00c00060800320300c0020b6018008069070250817030900b2031a1000030856004903030165150703071801140303450400048 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 109162805 1250 109161555 109161587
    0x20d0b0406060c020a05040203070306120c03020f010305220c080f0102070b130c031209090204080d030b1c03080405010b030a0b040c120b010608060a0305010213050a0948080106 78
    0x4407100d0f840d004240a50b10717500070f01d40659000000034050381e0081d00311034001c0080c450012407200c844d00f050400c0019500080b842584060b001c0f5100b9882b07030040d00e0051002c01c80c00c2c0d123a400f40d9072000e0301040c2e640307a086039028079680000454070f00c00c0c000d500100e89400009a52101540b50000501c10020680d0501e04080d0b005403000c500784007922410350340c4c4500403d003542405201a2026039070307503001650301400014081880c1c603000c110200c21880984050100c2d2034403400b045500669000c410102000903e03017000443e104601c000e412074011000041c11600300401b183c100b4004420694114000c03100780310400c000c5000b104020014074000c800b12483c107a0b40c02001a2040c0700e030784c0c00c01002c000810902e60395100b2480003035600100031955000c032005600e40c25142803088034070074180c000300020152051301800c0518030454010900c244111744d045910030207620954003802210040000700300040f001d99035030041480e00ea00c011580f600c6c00c000c080710000b110300307e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 109164055 1250 109162805 109162817
    0x15030c0904050c0913080d06090506030a200607080d060e010905040b040308180d02010e010b010302041505031306020a0509100c05060612150a0e01150807030206180301020d0b040606 80
    0x10000c5980410f0b8803000c034604032409002c07a01c0301c00001609641642001d0308640001850707650780740346a4041d0f4210740403031a040c44075a48850825481e0800310202800000300c100140481c0d549040004040c2c00c802000641000c4807a12a110103400076110418070968881c3c0c14807613030002c0e180c42801412030305c900303200500c1d0950f05d04800f90740c0a40005c00748030345e1034041001480c0081c68580d810fa203020858010300d003401c000a002c2c05411010202d954a006040c0c1099482130003214240d030b4055200b81200c00d22201d007100d00f82c0c8001c1c1200510201011540000740c083d00080c2000401640c406031228400420401e40341c031042d601c10240081c8603803103030018101245d0f085e0b100703008560a484400030840c0c1a42404996204070000e84400010000b40500b01e80c4115015880301c0300030030554583c848032561140860081c0b016a505c45036042006103824030042603070710f00418501c485001c180c0046401c4e03030082d108a2008907102e03c0015614100740c8a094020940c901d049 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 109165305 1250 109164055 109164061
    0x50610090317120702010c0305011203050304080a051c0c1409030a060f0b0a12291603020702090a140603120d090c050d050d0807050301060f11100515030c09 69
    0x150550800384001070030012040303030b8042e041c40110140c841d0f225400410006501d49900024024020400b4074808070340b410b400031456055400356a402154507441e51481d6032038640350084650007610301d03403041100070040038078078880c600c1400c86a00319240340803030880100030f005084082e0140c294a01e00c0300602403440913540004181c4503107a00b1040c0041c0012000300400098024200395642000317000000003004150520040f0b003079030203119076808195500c51044000c651401c2e8070030f8540072507402b0811140701003201d4210003030281801490a41036a012421030b100840c6c1c1c260303400343d03954001d01c1450303034100c8000e034440000c40290181c41c000d088082414000d20b030103140c05550f41c04c4448200400c0f02d0590014000003813603400c8072821072415540e140080c00c0c01a0028080101003045603004000380c03030603210030341c5807082e5800c0201c504407201e42100d4401c501a1042c1074084404034004e11070580540683e0020448400050040c54607088502c0040b0340524001010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 109166555 1250 109165305 109165307
    0x2330070c030b04020d08041509050f100f0e04051005040c1416060605030307080406140703020705100513061806050c0309091b2205030a050709050a021606020c01050610 74
    0x4600960b0380c4a5622065915140040b5882c480c0d03240340204032210002d000f1620207200d90200500c0a0f140e0b079901301c141c0c1ca0340b017408803919240d5603042e04a1350341094078034414000d4000c0e80600b40c0602c2c0c0300080c5194500041c096820544142000c01d0004601384045e040a00581c01c01c0501400e00c601811103c000610051061300100c10240694031254000c0140b250071130001042d004048030785900c4107040100840c0d1191041c3c5020942d801d51202454852009480200d50160082c02c503891801003802240000c590200701000000c01411038090f01015409000d8074060f940d60980a03055114901c3c0046550011814440c4c144006007100900100b12071801da03068880b10034a803581c0c16000d640441c864090900b040011802d12a4001482c0c040030a2b04a0b0018002140e5030382c00926032180204c1034041c0c0280c1045e2018000080d81d500040d0700011104401440c105000c1201c1c0700346803543c482110311b241c0000c1c91400705a0300b400b80d6500904102c40c0c0207070309249800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 109167805 1250 109166555 109166573
    0xf130506120f090c040f0203061c080304030c1e0c030209092b031104080c27040f0201050405040903110607030204150e0402190e03060a0e0a233007 65
    0x2c00c24101641a10014070341e0030341031040b18003001d0060000e115510f401108080a5001245d41078098000781311355500c446030f020b00c1c0100e81904000001d14540710b07928102e810306400c2c0300a881d01352084185c004a14131a000541301d103030103942c8100d4481d0562042100728000038098160642c01155030a48014580ca00402500d2812044144450a29030281c001c2c0020302c0c1000c2c1c0c0d401d40800c0000b52000c1c04520350340c40c29011036052109407680c1c1c0500d88250030020319492000ca010f00001c00241d4034203d26250a40141000350402d0b0380c5000240580700568001c8000a14440301b2000c08a803c1211039081140c030700303095085c0b0341030680b40022106161011008c00a100c0304001240d00c1302d034100c4030700b00400d41002c03003648112200a8502601c0c0349000e4001c2c450200003841071410762140c040030b940820098140e004032602d42c1e0030b40401030361403900302903e0030300d81180007030040041c0040549401c2c0d0030030125409161000c4040141d00d003900940720100700c48000100c0d500c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 109169055 1250 109167805 109167811
    0xb060303040515030702010e010e19051009240c0507080304061409010b03010e06090a080a03020705060a0b010f0207050a0b090f09070206070215040c06050f1603022503170c120f13050612 82
    0x841d24414180030780cd02c189414400d44c110403045203403600c01014030510040e44085003103580008840340708072a801c0001c803070102045070005a002d0100c0400506050011500039000d00c1d80450100100302c020000c840054810405d241c0d5140701000072410b0070b000e680442d10400c2c0c00790045140c0000f94988540103940000c100e00c00014110045078000c1e0705030741c034543d000402c44149103402c401460003050201b0306c0c0ca0100755540a40c0311824400140d510a807880503114455451404500c070b000740d0045111140c0c052000480e240c0d9a0b11150030580c0300e401583d0040109081164010341000c0c444003042c0c0b0902044030400c000706220f607020300704641107403402d00e5680700c0c0c0490401b8107000b141410341c1144941591071003030650002d5000700101c02c2048007030491040c0c65022450311024403005101d0303403250080482125030640606840010304050780d2005180342005a141d42c00740b11404406240828203000c2c0702c1d024481e0501415007900c049141166000b076080c4d5055000f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 109170305 1250 109169055 109169083
    0x3020d0213094503020a080307020a030e0603070e041d0a060b0f060a09050105031003060c0e0108010807210f020d1b05010c0b0a0b0f0a0b030f0c040b04030b060303040515030702010e010e 82
    0x3c2c0c1d180c8410140308010301c1521036001940340740c03a4208044000d445140c9400140c0006006007200c0360315282200460703025803001c1d1607107422101d01d4010311014100e070140550b01062070503103001002c00700f48491100e1382d20a18000441c070841e28100302c0308208014070360703020309010b0008420240e0841c562200ba200c007420b18503140d0b51aa03a0020b1041415003004040030705200040e21119000811500e04407002d072140245681c941c0c080540d555094850011907041440321302040209611039510003a0144c03a85048640494000c00e91241c07502c00221121742e2201140040c0c010800e40b01e10180109182c20009002c4548641c0320f014000f400002c40f040e43d480e004381c1750359500552403a045030040c0401c0740141d07503105a94001d400849a400d81440010300007140441ca4004541c1a102c20a644504081c110b48a1036142113004014030f0700f600c01040003040541e00c0710245050f4018003444203940c2d192040c0000e09441c0501c400032041c5c2e0400d0500c0f901050080f603901402c1c100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 109171555 1250 109170305 109170431
    0x3040b0a0513030c03062309070b0c070801050c0403031e1403060d0210030e07120503070b070324150305100b0d11120f150d0303020d021309 62
    0x320400d0751003004950f840140300d1040e0750000000c01c041e541041841c1101c0c0c0045111040c4d011440d564208001c40d00c8403160b801030003080c001d0b029a040a080d80c422500300300d83c805a2640003803400c540d0180ca8510600da40440d0400c201544529011b60085210041550304a1625005484c80c2c00c1940c40340c0c10303a1404000503020703442c1d440400b80402c0d0001c21400144402c0c80c070240040640ba07045450031b000d000c50100b2850359100d40b1071031250b4070400661400701c1d03a484810361000050114030425884460038101c80070812182742ca026021800030016a103040e0700c000805242c0c11142e800e00d800d10042110300015503088104444000060950790b42c05c01c1c140e100148003d0740d801c00000004500211050600740440c0d10440a801d0714580e65103034400c450104a101c440c20b01d83c410302912601c00007034843d1300a0070400440d5003001d070502c12a11142c4540c3c4038141c0252184507580c1040d60128510800040c890902403040c10761200d54070800170801d00e07240d80a0000380c0c51 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 109172661 1106 109171555 109171567
    0xe03030606030f06120105040c050a090c09060e1804060e010507051e07021206180c010504050105070b1b0714011a01020d0c030e03010204030501050a0e03040b0a05 72
    0xc0c020251419981e403e00c00b0320b210300c002042c541d0452140310601140b54000d0144500a611608502c54600d061100303005036907109602c215078041c144000703102c213550410349101c1600c03181d152110141d520f10300072a2002c00d20424201a800301e500401c01072141c2d0768884088a900c1c107009000d0f503254480d0495850081120001003403948070810310702582c1000080044902c0075207107130035002c4182c00c4c1c241080d008840d81e0003001e03205142200000c5046c410a8200e040c02d003003841c107207410040001c0440c00344550062011034224041518404409441c014851180460944d9100d4610305000311261001e5405d0807503003810030100407074084000841484906078000c2c400745107182c030100c8605c075280c4001d900340300d13a0305148002c0741c4081c0000c20156000d100082283c1c206034240c0c00444032200b207408104e0f0014401031040f0303000c0c2c0d01111080400c516205032038034 = true := by decide +kernel

theorem cover : BRFrame.Cov 108992805 109172661 := by
  have h0 := BRFrame.cov_init 108992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 108992805 ≤ n) (h2 : n < 109172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
