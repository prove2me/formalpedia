-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2907
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:06:21.64082+00:00
-- url     : https://prove2.me/submissions/8b5022ab-76ff-4441-a38e-747819fad992

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 522661870 ≤ n < 522841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 522663120 1250 522661870 522661877
    0x418060512011a0d02030a15022505030706020d090605040b011505040305070b09060d111306030e0706080a060305071403150108030a1202091f1d090105130b060d0c 72
    0xa00c0720701c0140c201c400000d092401032040a01180d500e242c080c0a92851030700050a486044055a407001e108010780c6022640707070f64001c5218841541e01e449407400b0b500b018030320080c5c41e070341c555100b035202e01c252400204800c1d030100702000c810b1940da00110109030b211408100300c1c103040c2000d01844400b44a01181c03041c074296020003107481070080d102100e5010008024182c10300c460b9a05035004214602e0300081c090040c407004d42454040d0a611440b0241d0055a49203182b4140512040c0740c0c000a06050030110f10b0444088001041000c403042454014810b4940720004005000e507544042c0c5184903910002c9500e02000c00c400c04510001c40441c0c3e141c0740c695401902210003445503003140e8209020017820b45020701c0e80500400f040101c0107150040520005041c1c0e00304101540c450018006a01d103010740180c86030a40120340d501502000d8401e9001551555050103594018440c6c01c1e0302e8441c11100b900700e10102500140f0340703501c922242d100302004140c2e031409800003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 522664370 1250 522663120 522663139
    0x201c02090106050f03010b07080903060103110a1a1e131806080c01050d02031f062007050607060e072106060501080f07030b0d050609010f050f270304180605 69
    0x8180070f44122060040380c150344a003180e1804c0026076a640103564150752201d42005448401ea400b80308150203135100707010001100d5800403d00c4849030590f08a0071000060480f000803881d1008192a031142d001751200000d040801c109603854003e1440341e403041c040011001c00d40030300c1070541d4103102400a50130441c841e9a519107507aa04d44c84854140898010880715414011640085601003848188880d80c0401e205074018405a03680c441000030f24241c01d201041070b1500d0781c261384941003e0080c00c080c2d06100000d038640c0300d01c10005011569480200147d5903040c0511401440c03003122200790703c2084030101d070000c2618001150b07810314061008c00d482d8001e041c070500a044001600d0000d64903030f18158010b10b6000001e0742c0c020b030004900800144204042c2d442034441e40300204e000d025141e50402510b41c0030344800c0c0400249010460800000880440e031440a1402c50003080a1104024114411500450505160030500070002d000c0d9800c80302c01c840056400844 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 522665620 1250 522664370 522664379
    0x204060201180317040f170901080f0609011809150509100924020705120903011812030203041407090b1e09162114070f020a201c020901 60
    0x69a150040216654090800d4560f600c004d04940c00380c030865040560880d40d4072840300d4862800b0860000c0440052603007201d5a110303802a1300103201408043c514201480007501809050041d20030301d040d12442240e41041365004400425000301c45840c100744041d40500250030119481c03803480c0704031304a10300c03828141d1181485c0c454001981c0c40c0312021210983c006900c00e0702c148845c02e034080c0311480103d0310030700c2454183e00480c2c070030b9983c5140910506080d20304110000c4520950580c03070001103407114504640940d07070343c031740141d07aa41c403480c2c401c28003e080d41c0400c20320702ca05100400d011b9039a510403a601841140c480b0450121741241a1504440c0c4030482e400000d032002282d01d051800da602e801d141c80d42e05221954218031151500000c00000e2504011030b264241031b24068200c506803078122903946410702000454007406540d55212907802499115400d282e40020080303e90344641d4890000c101080d660b090043d100780441c6840c0307090f072103541c51400019 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 522666870 1250 522665620 522665651
    0xa140603060403080a09060605120606010305090a0c0509090f070305060a1406011d0a15031a01030902092208030f0f1006020d0809031b03130e270a14010204060201 72
    0xd224903810307510b000c1c041d56a6017601001d080062400c8800981320b6901007040ea0350007160707441400d90341004068070714000d00010107840015110180c0c0750403c1c0d845001140720b00301c0031429900f06481c160311075260500c1c45ca107065141a9031301554018000c020041143c041107003809641e056009002c407070000e596604200d8015154117011814540718001c0c5401d80b5916034160b14002800840a25554500c208000d07141a0350030700002c0d80d550021400510010303100030303500380030301c1d0820100003079601080d00c202d80a030100100c41041d05150b00003104101611004d150b00040150b244e00700200e0541c2c86800a64403a201000c0000000c0c03a04007040c580d68003112441c0c0e0085c4505405820240d90306c18000d803161465010801c02c0034582c0c51402403c500322b0f2124401550340f45071008500b025198141c011822840754030003401145410381d280c1481620b07003044d4540400c101ca0700014038082500324010310003040001940b039020707819809402120034a8000f4000c05100103000c0e03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 522668120 1250 522666870 522666883
    0x507030204060f0c060e1207051005012108090d030e272a0c070e0109230604020702040906061e030c0603020f0c12091018050402210a140603 62
    0x4030001c1c070f0302014281c2052207003554000d101e0103040300003203114404180b00e05000c001c2084a0200a00044c00410090100304d0300500204080c01007140c1e50400c102030440e075030300c62a04401d0a08801c540c401707002c040c00c07c942039400000c280b00e04581080c500039050f5812411041e2081c024004a2024041d9080c8907296803803070110300d14030a55648200b0a442120b03050203200c14200a01c5002904503c0d000070001548801c0c018611186824110b8102c80d50503001a4041c90500240d070250951f42d801c40084408030790040c41c00c035964680420000e00441502035401814041440107001503540f10038107464400c5464070306032038400300c2c3c00c902c2103140c44002c280d603110146c01c00c80e041c1b00c0d6010700752541d40d5013549442c1800c59000d5502d0210140701181d0444c030009a81c030759500e88060000401809410804209220030540c02107a0120340315141c09103400058005d0701c001c00c10b2081040010341444400d02d03082c5802d00000621000d02c8141c010108200411045d25001942 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 522669370 1250 522668120 522668129
    0x1211030405070b0a03021b07050a0f08060112061814160305030d02090a0e18071203051c0f0603080304020301051e07030c141801031a0d0201030b06040306050117010507030204 77
    0x7042c60900d45018610030f40e000704d068008159003440802d11192801c48640d10300514800200784e0300341050100030951038281d0100721060136000081000c034001017001380c110307808804804074641d807505004000d0288800d8003002100183c0b020010040d40050b42804110223608a03030b01ca0780fa6086030380380c240c0e0602010b48594000e203d0441504a150021700d405031010703140d030b90800d80d10b40c00c0d60f001003070554401800030000014012041070400240300240119140c21110003549c3e1005031440c400d090048821401111303031245000043e400c031851140041c4002c20185d50f4904008400b50000c1d1800c85c408c2d400c100104030500b2144200861055103d603050100d03480707443c011740042515500180510108400d0140b0390203180c4040c00801a100c1c803000001d10125000408560049003081d45c820b01d4040b40f40301d1521800c6030318001d0340d42800d000840003501d00010348540296413000303080d40c0c241170000c501c610040c08040c100000460007800303541c4039280164140d0050340103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 522670620 1250 522669370 522669373
    0x90501020d0e1c050706110c030a021809011d0123040b06190e0f0702010b0a2303030904020a0203070c0f0803250f0b10060c0506060103020318010c1211030405 70
    0x12182c0d8507203490607040480f0480c282444a140d609943d0f90b41c00c08080b07034040004074812000d014004042070141c07640c404002c502602e418600d90340002c8c900341c10400c04100c009135007400650118802d52002c40c20304850b00040c6074031080c050080380030341000d1541c05400e04c0c445810b150802e568980700d174091948400c501101c0d6031140280244c1400a116114010440e00700c0000c40086042e00c860152960803100340c2d035450141c0c0b020f400c2d2040f860001d0f000e010354100c1040a4020764460411980201002c030288020b00ca0009266014202d8040d41c0288001240310b42c054000000b03104240c4a5038042030400c6d40c0d43c0c0701c0d441c00c901d00d21465202c0d400411860000d40d101c0003d1200c0c00d0450002c00c20765500036140d6009121440c04100c9500d20b8034000d2142d0f05500c8038072034006040910f8420700e20b0b031050f5103003a22110054040e40c1416000b03c00b107107002248070f8039014401500f800800400c0c0c2c003150014030301400c2008101d401c6240080842d01d40780751004492041d81c2200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 522671870 1250 522670620 522670637
    0x50f160608191e020406080411090402090a050a06030b100f080307050a02040b010c060f06050111370f12031109030303070815040c03051e040237080a03090501020d 72
    0x400103000f40e1a44150b102082c0d115082649442d440600054034195a4202c0285000d182001e400700c6080b07103030f41c45440303d2000c01c4010703940c0c24800c5502204e4030101145075290703071410740d0240c68107410080c1074007901d00c10481140b2240142c8000c84204944050706260f41d103c4141e100e111300c080280c420b030084000710015051607000501000411f161144420381243c03524012900701800444001d034650404208543e88a10f240c00c00603003076000750080e190b100916000c02c10903c800400070035403251401c02915040c7c00b98400181d0803113407501c0381010501d440002515401c2803400840e20f404449100301d880310f001c0e107000000240065283d87c07150a41964409002007484c8c0350010300103030030240e0307403039501820098026585012813a41081d080150320b05642d03440007220112003008000159076019103140b50400b030600c81201d5840e01b903542088160031542d54903605034000c2000199440b002411920950280e03071051011a2110012610344250724920f40004074000d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 522673120 1250 522671870 522671911
    0x60405010e040813050a0605070b0a150e0402060915030a051005010f200718140903031329090f01060810020a02070e091501241b050f160608 62
    0x40c0051484039584c0c201d001030242e4500000e0aa90004d4004a0000c0d001045142c00c001c204030030550820b07540c4900f0710041c540801440926001d0f4400c81e007009100d0000706066444110454038501406448280d070074481c41c84001980d402a1440d1498519000010300c0100c140709183c403d58005945660000ca00b040e0121072103110510342904c1c2411480944180003003c010302c070001c0403034584007a011079200907490112401079140044000c03241c4100101800c000c41225444a8601c0c04100560030a00745240c2d031141b0a040c2203090741800c0310310035001c03100d06e040714030600c51030046505c1031172441d8a103400e0780c03003600c510340c83c03540410664140c0e044640c001c1c00026245d441115110313517484d1012a80440c0070750b410340c2c9a070030414088030f0344104460840d001d083c1e52184400c249460004004040740b00e0343d81d21003006000104403454104c824208c20780290848115403503070202ca000740384c58420b94140c080c5603960b001000590036008020b00c5104a0202c014060001e859 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 522674370 1250 522673120 522673133
    0xb0f030609090c1005220e070f0c020d0b070210020d0501030b0603030703200a0206070c05010306050616020613170d031a0108040f1b0b180d020d0212030c070914060405010e04 77
    0x14900c003011000c1e007015207420300c0700d46c695034500034003540e0795400150501d05405410f00300184440000c00031031003096800f5841d070003056400030340c0c4111480d000d0341e2441030490401c510714442080b407500015000052800c00e03004281a08d0062070142c07c2034644404040c1d4900c03e4180050100e10030b000e103070843c030f000002c011006048800654000302501d40c005450341e403062604a0f100d039500d1600744920350f40752041001034803041d11a07900c3c0a490700161004090310007002480350900080b84110080450312400080460a0440850240c1071000c1500d440c88082024002480d208201302c81310707508800c440c0e4410040c0c4900f05c5607111360711544502e1030b11500903181030740c005031284500b041403800b684c014a522031303025407204040b1034281103c5060f440c00038460f60901c0015400759a039084030380c02155040703900340141d903541c2c140c29040d402626941c40c014041c090002078242c07500d070001180c0400c41411401150b54680810040303c10a02806420841107400680010036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 522675620 1250 522674370 522674377
    0x7030806130e01090c1403030703021b0303090604091e06050f011103070209090703051002070b180c0901060c0b160c0f05013b1b0d0c0b0f030609090c1005 68
    0x14074500202d144510600e103642500c0c42c10b042110080080031040013900e52a500580240c0001ca001c1c514100080e02c00075500c400d40c041040f100d5051407004803980e0303010003c4404d1400050003194881340c0d81c40e0648000d102c2030311a6002305041d0300d40c5001c6030031680b0035102525002020046c45280860046811072608205012548010032030000560f48440009105e20280c0c80100f01550843c0391650a003c100e00e03005101c40e0052248074002451000310680c841ca05078152001e40c00320200c0149844021140e0b250450300c07038000856802e138024800440b440c09119800425202c40d103d03456104841580b0a0014410411010018028041810200340a08000f00e18001c1c0001d003010507805240c044d000d21201079a1f0f25007194040e81c1d06007640d030300300320213030102d016203014103420780110841d006d11500b218500da108120f04110fa0a019000c02c114031074440c05081c5003803000d940248c4042c2c0c400c181640008101010004401254000103080c031700016120100a449540 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 522676870 1250 522675620 522675649
    0x102010603020334030c03020117070f0c050c04050f090c190308030402150a030518031e21010803180604140d2102010c030b011d0d050705090405030c07090207030806 73
    0x40d42c0c00605224400044040551300490141b03601600e188005000414682c21654104620000300100960002d0300150200101e0400b41c0d00214586401400d0001080009620914000c03e02ca001502c1041f1030340b04402010032107241c0d100c00410000400c110024114821881902c00e000052004000e2f58001d8409014100c4041e1034244144158100a8440002030b68450400c2600f01450180e00d14a607006405149050700141240d40104078002c00c589007064001841d413200c0600c00091105485042d4071154a56100c080b80750b104c1d804040b004101d400b80d1003030381c0303102d203460021030302210021800e40c088813100d182480440d0248000a444900c0908184041c02e1400c0e400802554001c0e4000565000019806001c46600d41030050401072400e010240d01080145031421440003154100c20304000761070720626062590300001d030010040024481040400800f420701483c0460603114801e48800d614401c901641501030001000b0b0404500f9030305115039846c1586 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 522678120 1250 522676870 522676933
    0x408090d0f06091709060915220815070f08130204020a080604060b03070504030204110415050307020706020d050d0c2c041401060e2704030809060601020106030203 72
    0x10115890310095180d00007010744032141c80307080c0b00301084428210a003100c400701c0b4100b4108a0802d003c1035881c000c1404450103483e22884400c1402c5154054461424410b1942d1840d41380303405c9001a00c9045120304c030114415001d800c001e04414440700d92244003103a44091060542d44000c42c0c071010080c0401e4541d03640c501d10030015072124002090203035055241c580c46803c105042c0400c48400e40c3c020007942400b070084c03204060340324040314200d035011180070480644184180b500c038403c075030044022081d28010301c203a91343c120780a5449219103070240c54540340c0e546410703615108055507800002d001000820307002c2d4400d034007403003401d003082c640030301180054040a045800b441500c4468821038940200311880c0602a0420a00346601c504042e549800000740003404200e0365644500d03007002201468040514040215409602d01e0302400c1c200703401c02031300c400000d60b86603015000341000174949500501683e4100d07a409402804040c40c01a00b024007804101c074800240c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 522679370 1250 522678120 522678139
    0xc0d170702150c0d2307020708060a0c0504050a080a03200706050c1608010e0d0903120e0607060507080601030605011d1002010b03070b28120506060405030a05060403020105130209040809 82
    0x192030b262060340800d40480381d0001074201720700904018441c0082030107085611103403042c04810400303ea62500540b0140c03020074018511182070702c0b140565084180c111450102c0020040e40000b1072940c03003402512a500d00030314107200000741c0c2010703004c2c0070130300e41c0f20660400546109200601043e407004003503400b00c032448889602d06a0301d503803000303800da0745610280d49110000d014080316100c542c142002034030700d15654105006400250101030003100203110010341c94607800c42d004e0650024040040b40b42001010b04659401d442c9035000034a003080124a5500840000c0c101d1103807118a147d02072211000c005514040c10807070400c41d500c40b400d00310541c400304042070190600c1c03013070306e43c48018260440d8000000c024400da07000583c2040362480b9600205e5001c4000110400840e040d982c07007000c41d2252186920041e050b11030716801c1400d00c0030203c2c04901440c401c3d4001d020a032540c402d082084540c00300041c0d4403462460100d400036424400510101001400c942c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 522680620 1250 522679370 522679387
    0x201080c03040f0321020705060402010e040c020c04051803040b13150507060f0b1207030203061005150901090e01270204061d0d0b01060807080106030507051804110c0d170702150c 79
    0x387d812030701048400b540316074140030443d0f8000b6071510030002d040c2c4080150b5204803c00031740c1d41000076451400390307039a400483d0742400c143d034101414002740c400703c3e035940c0d903104221182d50b030044004010308088020041648a10b058510500540c01da03540c0d41811000e40303400c0000c00007003020788509a52a0190640e546551401507510840d0780080c1c0030007131a50060606089000b42038058155a070710b4103111681d070700006048064071700410140c50300c0c1ea91006032610051a04a007104500f280b00004d454100010a904001800d0219580c510b030124410000c2c0d02650060101280d41540d0040d5607010a907109407003480014918030042c4580e80718021091001e812220026007100100680203030456000d9004140794174040200b0314061000810a00882d5400f42250000403058403813940c558001c0a1140380e800d820590341e001c006c503501c1d40d4003281c041d0360700401d010080141007180c0140403944941c40c070340c025201002511040110240c00180000a603501c11b121198 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 522681870 1250 522680620 522680687
    0x30c170f13050d020c0f1206130609060212011e0303050d090c171c0c050a02040c031b030609111303120c080d09020a0b070c1a040504180201080c03040f03 68
    0x1070743c4950f0303070041c02081400700144454407180245e468010080d2802046401000040443d44802d09000344c540080062078240040c16104001070007480c0003081d41a80081c011000d14121074076142a000d12800740300d10039040d45054800a00460001c0c81000440c81190300181d40a0b807040e0b0280d0310050702d5403120b40c5041c1200307200030215444544d4580b0366141100009071b03440c180d4102020503020f10340e1030594410b1181d01c020b015030307200e201d00c80815020f900004480b00385001c04000d402e03684980100184900d00c28030300d04508142e46000301e00d41d5081122032001c090f0700545046421b6444440d001e280804201080100809050012400c0c100141001503203250307001c1424583e41c01004401605508503a8000381c00b01f144c0710005074038500c4641220304880b901d81c0340044941d40c1880780c3c00385034003043d0802d08115082c00520740701700500500ea03201340c82da50b490342c6a0a03980c000c14041160028075500c40c00040801003406030840382441c0d407055400701c8140b900c1400e41c0c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 522683120 1250 522681870 522681883
    0x40803030c0a0e120601050d03090312080f01090e2503021801050a0b030708040f020109050303040f080706050307120f0f0e100e0c0607060905120403030f030c170f1305 74
    0x903000e62004580e40600070390124090b0703d01c5034104c84207074120300103400494071140107105032445155444200c034100f50050100301c00a60300018400c0f0b24010300c400150042c07404903110b072111101140003142c108402c0c460100802c84210081c0f0032a00105050390911040401a01014900c11000401680d804200b00d07000c0400d900d00000d07551425040c421404440d0f042401100d40900400070190340c010705c150303171150304029032802071881400160745083d400e40046800d404002404140f09103411032583c01c40b004801112074040c0c1d90f4004032034034001940d42030000307800c0a026410b041c456802555484d0001c160000b04103801004140844825403582c80e117030703084080313810010a22071041c200c4980084020306240320340c25000450700c0c4038146006204680c0e0f00400821300100300304409400030510b1015039910b8503418080c12002506034190002414828014230142c0320315115003824903c041100da40303840b21040d2a05400c8002c003203140141c0d51400f0140411820080b5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 522684370 1250 522683120 522683131
    0xc0907020c012f24040209070813330b0102030301170708010507170708010b1608040e07030501080d0905010914063109060f06200303010905061309031e0504080303 72
    0x504d00b1030a15021880c0c1d015000300006100f940900030403001d03031501c3c42115400340b03a501c2d01102d03c1c0d03680264410140ea5411000e050329030303030315504101100115820240b040d0308030700d8840e40c40022000c103070954491846c0782e80103801c1480100305001e0303011030f01c03003240010784d00755034019031030b50307801c40c00c40700704071a40130021f140350300303100c564400041c51560023580d00d141c040d21540c1445038014062051011408184400c2d41d06c080070302c4080000d0790081c1900040303810050901a100501800342805504980d0060480001256002d42400011a84c1c180c56490301246084620014100c0491746c0701e1b0084030070000d4000d41d4140101d5141c0e4520069542d419a40c400c00c0d42c4801a1a80d400010f011450f04c00288040c05d5020401400c0b5061440c0c00304500c035590107000c041d03020200021520340300c003000116030403000e43c001a12030602540c5450b003290a1000600c02c0c1c4003407110240c0801c42442c5201c00e064000701110013444002e003000e528040c2e41e14001440c41d482186d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 522685620 1250 522684370 522684373
    0x6031817040501033903060b04140f01081302040911030a1a010b1e09030313030c03061802130902190305031305030109020901091e090f02030c0907020c012f 69
    0x30284401d6070075201c0d003d40c501e000b107000e40740c4174a110580c0918070015a00350043e0340c40ca1703804003011482504104050084030b80b405890b2a80c5003402c012625000368054441c4161009460882d4424281c1c2403003480c1010710481c48440ba9002e21000b002411000e541464a42e062121540c904002c0d43c88035510501d10000c88140415040082c41380607081411108400c0011000c0710044039001c0c2030101e8030400f01c584d580d0703a00000910707620800c00f59403031001d0150350000078005a6600c4004903801b9020030300100700d800501340e50503010000000d42c426800d00381e41030406401c0c1d0080c41e01c10f101900b0800340c040c6a003041c0c112010554011203c540c03002034030401e001c00840341030000300000d80080c041c103045503000406000b1b0500501006a5030b90010b07070720213444640610021071041c80e003041010320509140c00584d03410f00040e07000c1e1107443e07000310160a00d0780280b4462249940a0034000807075000469140e4200c2d480002038140c80350386990b04606007900902454072000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 522686870 1250 522685620 522685627
    0xa0e0603070e0c0706020d060e010f210309170a0512091c17340b061f03021b100e06090304030305120a0e0a05030306040f050c0406031817 61
    0x1010549001802e82080000d007400d001401001d44010007512280781d8004400b589500380007042000400c0309a00c6aa00419100c00000340d034403901d840c58068800804601c1069070218000407207950f0100d2005000840d0041c040024400d88161400300c035140c2c0c4117907038541c90307141c0f210b40c9010204160f0788400c2c000085d00d4006454402c2110041d60414001500600c1060711395000020001c400c440c0043e2000a42c0720246074621500311095148100400b5141c1541d003c0e030044400c14042143e08207103640218007980f038071400b04408400c04049000044080d800c044020350804100c809040d050b00000c805003071024818800c032a2494000025480140d200750b52070610302400c03040b0203400801c01880400c0d40704044600003643c030000c0104e0707525415500b100402403002c0c03018442c0100c0041508000d0007000541c00b60b00100d400b4840244016000d80803130760261414030050004010400106029401171080f0b6480c207803009000a00d03a40b989000001c180c8400320041e08000f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 522688120 1250 522686870 522686881
    0x7060906020d06060c0809040b01021608100506031b040f020d02030a32040b0c0f03040c0e01090605030307020405060609031902040f06120b0421110f0a05071809020a0e 74
    0x510aa5000b13048902d41109103030413946520b07200e4401c1c4507005001d41d80b261901c0c541ea034000c00c403c80b04c000b840c000341071101d43e0710601d050719520345010408841d42030501085071890700180000d004800d560000700c0d0900d12404001c02040d8046a0b8501c294003405014101101c501c080d512681003094085244004c5120390080300c0030501e480c0081c000e0300c0402c40c88001d950881e56500541c0700340c0d0943d072911000d014010390f000b00604c40d034688000008010030446c1c1d46035904200c41001c800500740380d88484144c815181c603070140503010f034003c2c0321b000058075103600031a03084040501501c1c0b8000c0070101087c184400100380d588192241c042c0ca0045003001c2c400e02da03d980d04000c0c00c0000c2800c0c400c0c9580001c201d070401902c82900c503400300d0300780f1201e44401110740c2e80380c1403100da80500150014100c85075402c22070a02e402160000c161031a00817031544013a681c000094810503090800703a14401520366403100304070707a8034824100103071244540840030340417101000c0000c0c50b00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 522689370 1250 522688120 522688147
    0x180503040302031002130b1c0c020c0a060503061003021b030a0f020c090c0703110f030d0603020114031005060c01020d05071d030d0210020904020d18020307290f0706090602 76
    0xc4803041e5484510400c41c8186c411105800755055030b103404109980c0e04e241d480e01c40c200362141c0309025080791a0220354143d49400040b80c0340c5e080810b0b02c0701c82e10079549900c151814001200d5807074001c001c410400c041107200303900030311276403071658090540780c1e002e01e0640385182c101c84400da000c01c03003008100107003d4040050554402080340c035a03035540744c484121401030054500040501040360780b44c0f8044a018404428280c14050489032503940720040c902c068801440140c4c007041c0340301c9051b11502e028400b224032551000511030f503024a0034040c05020ba0041c001c001b0595030074040130070304400c030740203c50081c8039595031810601101504240705440781262144680c6c0000310101429030003241c0301c22440b2130302e04010388503481d01010501070b2143c00b248401c43d034a4803034400030007204e14010504c0c041c000d8048446444d104c0860141c80c140e01d841100c4800305403040b40c0450300c088802802550216118681400441d075641ea040c0c4840b600100c940503000301c1c1c0a00f40501e07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 522690620 1250 522689370 522689383
    0x18010221220303020a03081e0f1603020c070e06012007061b12180504050108030304060c1119020604080316030e010504060c06092405090c0f010e010309050118050304030203 76
    0x90403820071200a25580c1d0196459103002e0004040c01701c01400030b02071125807140e080880d801540d40f04590f141c82031110550041c1107815042e50016026a100094482c0c400d0710b624456100040c544a410442443c201c114000c11081c1005181da0407a10101d440b4030540c250703070350204010440a07062042c05061201e9465510800708020001030000c1460807049032401c030081d00f081081c01801c80e03022140e685103a000300d9005401e0074000600280000000c501c29405988104030210300c030030044a4800c454110008164420310b6424030607400d0350a484000e51005001d0b80c07800d65030300b8999040d9080300b69010514a0409000c1041c15008980750441ca42c091800701d24060801c00080c21020000308003902c17560f543d03840340040004a441505c0c10304110b0319a1a1240f2143c0090300c05403004850482c2035000f05082c100960a0002c014070002105858140440302e11000450082240c2141070f0742135905c1d40240b1007032a40407010740705880e000e074014560321800c50052502c2c020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 522691870 1250 522690620 522690667
    0x90815010e042405071d0904060510090c11060601090b0706020f1303030201140901060602030a0c0203010207020d050703200901050603091501170f1501120302100c080103060b0d020618010221 84
    0x411511006c442da989080800e80d0140c2e008600240036220441030544a41903904582032841ca001c5151148ca80c00030001000042484100c8005548001c011181812103108250030808140003210000721990080c02014902250080c107040d143ea1072004650000c0d4000d90150f551a03810029004603401c1c0103512040810080c0000ca2810600940d01d12800c0381417402c011030a80e0340030456030290112200150000d0106200030442d05019403030300c285120884a021506503c2800704404a40040060b10002e0070010940c3c80c200c2404131aa10082c046000e602a0074441c1f160f090003040c01601070030203014035248206029520600d05042c9080c031940c141c0c8844000409440b481501c2030548140c400c4205a0902d6071030168079002158008002c0720b800c02c2d045044c1160300140b2681207c0c001c1000b400094210420303c415190402c80194129004002c2620801c19030340f01041c10707940610450b540340501000d214003514581c0d180240001e00051416256440b001d041d18003407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 522693120 1250 522691870 522691907
    0xc0806010915090b03071e0903050a030516060608070812090907230a0c1101180308030618040b06030f0d0509010815041a01090815010e04240507 64
    0x14144000080c04032040d0703200b40020180c0b03100003124594810320109008250010007191242010034001c0c209094030003942078200c1c84061a255801e00c0b81e00c90008890304800034245003401c9440846035980904124601c004080421400080c0584514401410403101811102c0d00b0000d5884c2084c1d201c95944158803824850b08681d69548244c05400902e06c0c1403c40d1540403aa2105c01d4401c984400180c5600740810916036458200c58a070028902c00c0444000f6000c0314401900ca80d5110160310410918900c0c050001a0410300115044003000b0903001d2403d1108004e0110103030201c508a40d48240340c8180710840c1403c216080b080d40c40e0b8005040c8008041c1001452303030040c0b0301c1c1039042251844c04076003514140303d00038401403c0504180b01342a00b40c3c00d107840c1148007030b43e180e00256005100152641c0046008611154501c1041406918061420208403000341007590801c91095800b002880303002d105200443e1a9180030866191882020300140c03003603503003034484 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 522694370 1250 522693120 522693137
    0x9060103110904020c0f0a1410050c093a11030309010c150906050129040f120501060503010207031205010b0f09120a05030f040320010203091c081306030c 68
    0xc101a10030381d0715401d03080d900142c1794150910841e1030050f2951841e00c09006004100c1c09000410505603030742c3c8041e9085410300c50702da03610070007214801c81d9640719071a0300340300c0c810b0140380603c09403400c2c1c01040000c03e00b00d600340c90348000d08003c82207440304946031034180e281040f118040c040180c001c02c4016500300400100080d280e20608100180000d0110140303242202c41c41d40300400c4190043c41c20071040d80c445003500740300101002d10300282040d5460a008103d1600100e4056954502d45600d12525003010300c0c0008015501c129074554032410042110f450920103044030300d000c1d9840041441c164a4044122581a008011841e00800507580c004140740100d4100110a8401010451074031801c1800c0800300b0000801600000405800090507070300600250303406a8900302d0301481c20255401d400b580c00f001c050142e04280a004040e141064000150303048a945084090a1940d80d5001a9100141c0045503081440040c00403950502c80c00b100802d0b9410314541 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 522695620 1250 522694370 522694391
    0x2607080318012003070c170604030f0e150d02030103120507172508090423040605091e0a060c2d020a0b1008060708010609030308060105091c0209060103 67
    0x816018500e81d160602c400802c1e00c01c40a100f1102d190751041404040d40c0d101e04a614203803490324900c2c840c00080502400aa105402011070001d004a9040e22407100d490396400d000d41d0081c0c142401d00b6030009094450040c2c00c842c0d6170041c03a0020800030010303620340c1940341018200d41003500f401c041100c1409040300159001c02034141d03101c01d1a03405a202c1080300c0c50720442c4c140300905d40d18552441c50b8001c00b003010840240030709200032542070000b018285130391010720041d04103003121007803150046000701d4400d9001d213410900c8030050b06d00100101c16450711f60200095a80441e03801000c448043c01014480c844040350a03150400c002000c2d210405020900040f003038041c0c82c410b552881000c2c2c02000740b4104254407814890507803502103245546942d951245404502503040060340c0c591040c41c065040e034040c0d85400e14014110f403411078684000409460600008000c1e001440ea903615520395051110a21601d54807040c2c41030242402d0b01400e1f86050605000c400c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 522696870 1250 522695620 522695647
    0x5130c08030304030212070c0801020c0106060e03010b010e04110c0a0302070602070608131205040906260d0503040b1003020a090905010b030c0105090906040b0a1502012403060c020726070803 84
    0x86c0e180d02c0c010303280e8540c451420003054414665020400d10741c030024201041d004107400c0341c01102c2c2c01d5211070700c1c0c2001c9041414213071180406440d0000b12800300d001400d15040c0d0090020080e5583d82302e00b0710407c0d8000f10316088903120203501680c0000700c20404103604100403000703000545403000b814140515121010124140010400c041886a0103400c0380f040c4281c42c01040c900d00c0038003030a0f9030f840b000316089604858100d00b070920b201c080d00944600052040b0008015a43d513840c5a455849590b24510040d1521044440210b000000346e61620088000344c54a070b240040d0711307074041c686203084034405074040f400ba8110b8500c0694030303a00107054400e9004155002e6445603031b9a00054001c0524804440e4440380c400800f00364a500743d600a0034040e210f40080098900030302015641884400c21114805103036081800050301c203801400072004c10740111080d890704c881e00c840d2402588166550840c03070604881c070285400700030000007029900b02552900840d07400a1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 522698120 1250 522696870 522696883
    0x6060e0609010c08030c18100806130213031203141023060304060e070608060607080d0e0f0606010e0d0510180f120914030607080a020d05130c080303040302 69
    0x480c403821001c55104026400790340020002e41d48449025074138a400552880b481d00810300f42600200000203c02c40c40c101800000024000b81d102c100d01590303020108040c07150300c9607011040316000d119603071061800071425005184165100c1841c03040d55480103040b1030078901c000c090780e5400d8050140e0032128201c00c100351a000c41603804010340705450f05200c084910102030f00080000100420300c0050f501140603506108251680700d41c0d02c0008491460f010382c0c0d0644d10139000c102c0640000c1102000302036201000501241c10024070318401e040c40000c542c0074550b50029010000150b81c400000da040010450b403111030340c400c6842c0e141d540c004020341c01512540d82e0305140320328041c840c055292241d001d12100c010350200d00e0302e0300c0e080a0900d03070342c07003c9610040017069408291124011004015008199560760ba00c8110707200c4001400c800303200c50b030800034904404035500826115030134484070f00102801624003094200290fa00102543e0014401d001c0040e0380407841 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 522699370 1250 522698120 522698147
    0x9080d0b0618041a0a030c030c0f0e0601051e0a03050901151809060902030f070905010515070318180b090705070f140c090108010e060108070807030209190203010f1403010606 77
    0x5001000c082c803106100303103045006174480000303003001003000780c0d860a00f020740784918405c085840c3d50750341c3d100780404680244c18415034540000341b580c1d480303203000d44a00841c1d00d548481f0304423810254030b0182c0c406802d01e00025110030030400404000d00a102c0c50198822503400c0340e42c0341441c03604503241040c02c241c0c0201d4480703161500f44011900040f12564000b001c0c6c0310002c071099608ae0380d496251040070305071401c1200002d6149811382d52010501036101c1140e02e4001140c0d412201c40740b551610310411091100040b61820b02d8404104958403000780c0000d040700f500042003201c41d401030400040000422048000464803588240c201d41c0c0300c0819104100078406441c02c000303008141503001f00014000003002101508801c541600d41c0c016100c0340e0340c8401c422a10340c0b41c41e002c0e514555005d00c0c1c2c01c2005090607208941e00c042445681a50401007003140010b070303272080c0d1081248182010040c030440108620000c0301c02c901f1070080200f5443e05070080c0811026440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 522700620 1250 522699370 522699379
    0x30604060b040602031c2304060524010c03140a02070e090106030804030b100806040c050f030c060f16140321060901030b06010e1f0207092c030d09080d0b0618 70
    0x41d0643c1150402045018015100010000250f02007541f54104032810341c0c01c05e0411b8040360b81011581318204404003002031452280044400545004445190813020041c000052101900519010341803040c4680c0c041d01d1001e1400070050390018026269910a904d4800b00f04001410318003203a0440f9070181040c030640d92103600b0941c841186901c0341d611400351400304070800100b15030104c140c501c101d902c1300080307040600341030340e035004110480c0d00507400300103640b074a01c0b070500070b8803044502c41ea5052086141d0b6035043c03000302001d0859030540d80302049804030030581000c203c520813041c1d0009910340c41c010b40098030b8a2010310001c1e096041510200300681d118020004680d10042c1092041e211a881c101d001f600c05504a400140100d01d00800c0f01d41d0781d40620b6100b00040c10a00982600000703c0074820050b040c2d075200c491004220180158040e0701540d10814004c142064640d50480c540d04160349000c0d048500c10301c0100501c1030f101d1072044944401c0002901d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 522701870 1250 522700620 522700657
    0x40b0a0f1205040602030103020a140f060c2e0c0810060507080d02030907150f0203040521070801020d0f0905060f071107240206060a0605030c040911030604060b04060203 75
    0xe0054900007404203064070024145401c1006002c40c540065049a00c00d481c41d040555803175059004140701c000300142d2021041e0244034142c500407010702107401c5040d066540c0301400182c2c282c0b90100c0014035480d984128000141d8210030f5200d48200309103203042c0b41482e0f241c01a2011440d101c10b00400f414024081210b600780241c02040e5150b500070542c04541c0d0b81400c2d403ca50b5124120300c50001c228000c14804103000d03208000d240400c2c0f01540080d802c041c2400100100d0350000003202400c2d02907400590648030040003e0740080c9541c10006980d00350303c00782a401d5403407070a41040642d040084610010340001049580000400c40c00c0e4619118028100d55800309808145000c0c0b0031b036400881e00b1011505d42103001d101602489030440350300031081e80c640c14100d9170a6071007003101c0f00030030215014600455005442a40c15850315458040442c2151350204949000fa0b00c0401004400d040920030440540300c9088800d08040c50308900030741e40c0c4900240380d891032003010f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 522703120 1250 522701870 522701897
    0xb100c030203040e040f0606081b130f1b030e0d2109061109010201140c0304080d02090a0609080c12030d0b03070302090702010915090305030f04110a0810060b040b0a 73
    0x80c8283c40107800f8109588020f03051905181a141c1c110290903201c2d070b45070400014034040001403e0780540f112899107480109140d0400c1034680d003009140080c19114240d03204501443d00c980d940c1c5012502091070b0b140c40c031500c02011128943c00b0a03074141c2c00f141d4001c80301a00400d0714000c0010340e06514004805222008001e850701c000000c1c03115040c249490001407110000c0c000d424000ea008221510308907168034041c0c0c00aa03883c3c4e814000400c04500032a920030003c00c580c4010403c050310f040c0490010803247e41c02548003000007490002c0500c042c180500000040c060704179801a41c100e400c0c800d072520f0b807060b121003e5500c2d54a420310100b07501e0a0000600958000741b10352101d161020b00a800f034007040c0b104860710140c901480d00110058401d40314030540696600f425555004521040450040c1c0180c0d071400d9180860344150303440400c9803000d065040084c12600b2588a003001c240c83d4540c10506501b50188001d01240c1c0003032040c0d4940c40c60030314101c28100d44a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 522704370 1250 522703120 522703123
    0x23031506071406070503160e151e0706050103200a090b031608030a140715090602041511060a0905190c1e14060c15040215070f060606030b100c0302 65
    0x840b41015034010541000000b0f0740003000f45100d8240e000c4601404c410841080703c0c43c20041c80300541c01910b0b018005481c0008402a24400286481300b00c44904c80c0710440285070003000b0201c41c102c0c1c658006100704040150b00b142414a605030309065808075000054003548540260f0030741070303600c4414152550b002c01c00e6604501604051190064598400c1d030785982c0000c44000204038a0300d562808100400c040b5a10700e50000e400d000c418001c03ca00c00d010f404408401d071490380d028000880c5290031540001c00400850b149e021041c003c0d0701780c01d400d0031030040c1922000340c60843d02d03d000c03502c0410307000044c4002e0103d612440110746444854000e2a80002204014500000c8107501180341d500341070381d00c10b144401840c4081c3d420083d1911901c08651007541044098104c0680c50b04000790304244020404180f0900504914903250040e94080c0c0381407126500d1b41040c4501d520407500a03003078600d01800722178103c40100307150b4410302004504100d84e0144401c2031520 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 522705620 1250 522704370 522704393
    0xc03090f340501080a0b03010b040e031e0405010804060c05070c140a05091302060c0322140604140103020d093504050907081003020d12020f0d090b0d0e0106062303150607 75
    0x10007071080286900a06025a81f50050380b0313764041203c80c202c1e903c0040210065a0468074141e4803d54241d603940d440001601c1c40d403140c482840b80602ca00800602001a41b02c007074034096101e01e003801c0140d020010480c41960000d4081c1c1040c40911010801d18031002500c5a01a00d0705542e8241c1410b45c246144214025030042810800c032415007003130b08a03600c01c125814205020f1b21030358040204041031080c2d2040f41d02144203080400d504e94080e8000e485190000080080d0358083c549484421f0528185041030040d440c85203143d0071810403c6489400c0d10a1208905013800c290206501d8030001c1e05484c180000c0d880002d0445070710092007409150f004d40b40c100c1d100e00030b25080c10703007883d070165a80c090b000c1c62403240d0601d036001400071545410b607692160b106180c040d549655501401300000011b0310b0700140c0b600b205090166030028039007983c0c4c089009202c44ea10014564403250610700c11207040044c040c0e14482401c0d0000003c108035151a55178071545000183c250 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 522706870 1250 522705620 522705641
    0x409090c0b12060310140a05041a0a0605030d0306031a1b0a0c02040506010804051c05120906090f03040609090b0604031e03030509070605030c03090f340501080a0b0301 74
    0x2800190000035034102e48411801490260100d0300c8600420b0035001c20398460740c488001003941c28000951140241d044190094054000303070007040c01c0e00f83c074402012404c466203041c81d03031034103800c002c1c0d820704210301b0388000420301e020040c1e182160784060560b2440d070090301c2980402808141542c2070342c0e000918a6812141d095540c1000240240c448001c00360241d01ca84c0ca0a030005000d94018078199108541c004041d0601d14014840c0141c40340201a1150030400144040c400c40351510210311301070081c000c020940c40c580790304018030b0b107413003100700d0103c540040c00200b1140e60800040c00c2503c0250b40301042c8004c00d80007141c5135015550001c1c00288202909412102c580940724210034000d07a01840f046d13503441011984c0702014800c0600040040002034040310400c1c0213581c01469520580d00000540c54946140c40c80300301d00c0f0040e481c03102c640044180400d240c840c240392005000600120f2034200082c0804000400c00c00c0c0d2992206107003600d9a40c01c0d4000c01101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 522708120 1250 522706870 522706889
    0xd0f0518011b0c05100302120711010e0a03110601050109150507030c080d090309210212011b090602251415270406120f050703080304080c0d090503030409090c 70
    0x11003943c01c0c03600407071206220b030a006907201006084254880e000300c40c1044c03003030b912207640c9444521045421110f0804100d500795030766690303550143c0d414441503011074003d40d0b5110503071625074070381420020183e0015040c0301c000e00042141101d01e103514007503100c00b41041c0d61100520f0500b541c042c5011080209551000201030f60214070a40c884181280031390f58031001c0b60b446400c4204c020203407105150480c070031600c080300149820117001c5100c0c088580003080c845034405042080181202000c0b0114184030b1050080c294104480340000d520300741c0d80ca007030074040b52800d07001602038003a00040c00004200e454131600d9500003200c8244111495983c1e0340c0c41624060030545451140034100301c241105883c00c1c1c07030240030b20815208070b204038070610211031391000c03d164200310003220140070341d40b000404617603024043c6201d103000b94410b40e540c50410000720b04001519404906002e00c03100107004903100082a201542c0d02817100148484550824201d5080b1951014645 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 522709370 1250 522708120 522708167
    0x705060708070e0109031707060f0c05040510020c010816020f10050105011101051009051308040311090610020c01210e01020d0e0a0807020f040b041d0d0f051801 71
    0xa180d200303610500c65400c42c0d85403d506541e5400449565200784000340580c0f0114600c8403404000034000c0c0711041c8107000001703125507081006815210341031120b01c046903011504003c0c0d410f100f04807440203041341c40940841d942250010b040548003a090707100d506212106002664020070401410303442c2d071070450741003092007a551406040e007405118005914541c0011491005000e002c1c0200460b08200781c1003418082d900c1c0080c100101000860250500f90601080300790005201a600481504801d01281003d0044501c0c0103010507000d050250103640c10300360b0114140300c14440c2440c040721a104182c182480502960700514022854081000da031007405500508038002c0880d07042c8205446103211070349600301c0680207001101c04002e4480103141070203110317440c810001c10010310003100a002c0b400b142d100c504400840400040c40700c42058040100403030f0100a0324011028014161000741103004810b04001d18a80514201c80507a02a0070698007032055404510310 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 522710620 1250 522709370 522709381
    0x1118160c06090f1412180a0f0306050604050c03060d060c05210f0f06010207031506150804050f030405010f03090f02060a050a0e0301060515032802120109050709030215070506 77
    0x51006a43c0342102c142c80c600303280500c001d1010a55491070b030314000c80030341407545044845101109860495601c00305e0f4102c04524004250403620107907000340000505803038030505004c00c5500281c401e05660406000300300300e6607102c84803000c4555002e40007040340600c13a102a184ca000e11700e10800345803142c0c90350a0681c1803c19003030f84911400130541c0e1107511741d54840719940c03e05491a0b070068000c1001031002c0340101880c8243e418245900003070f220750324100801c1c241d0740542d160000514400500c01807001c104044400250b890000e50326091400c8000b07081d890006114006054507030138500c05000801940102c003e40107030540d81d89240c24107000f809680410521004504485541800d070b05051050100f51200604002010303e018a458050360f00001e00e501c40340043c40400d96541c01c4481c541d0358650030042c20251b00c0c1d19410404480054058100b465100d25050820040940c0016160103c0ea0140c4840440030207040c6900014801e000001d026480703900103001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 522711870 1250 522710620 522710633
    0x21207120615020c0306130c032411030601020c040b100c0602090d030e010215010608131b080705011101021606110403080a170601050c210702030f01091118160c0609 73
    0x105044d00314269030441d5580d45000300c4604081e00c4c00b6200c441c00078000d00004001d11018154a4642e60004080d9440401b646081c2c407003455104001c1c4501109020041d60104401e00706250216024001c0410480200d02100a40c240c0c64081003510f03240c1c5c1e01481115411036503189400fa114504403c4203040190044400c2c251590040c801d41002c007007005440404c00f0b05a82a950b076525180d00d85810220800c0c8a101059880c0115019514801c09041c83c841c0020004440985001880e0400141c01c07240d1303070444068035900400200000c1c4a90b0201e03042c10551043d03000800d00c0c0710b0078200c0344901450700018807003400041c50b808070640100410350b54010b4210001440e946100c011501f030b015611404500f40d00c0707154010348a0178603c0e6010f60341001464082d081400303540000e451315550060f0544203940d903c81b10810f101400240591880d000e80d18281c0c0c1c00415801d00490b1440144184480700140810925440c400d034219028590041010b00c111505801d100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 522713120 1250 522711870 522711883
    0x3050304140d03021002030403050c01180b0c120a021806030c0904050c09010e130e0d05040f0524030402010315030b060405010603050c0a2106171002120712061502 72
    0x1d2441c1d00700d111a411151800c0b040c0340c1581603156010386009117505007808080e410241c401c6040c07240500170300034002070910a581e4843d044e0703201a00100014148182e04000141100240b8501081880c81c0004e4841d907a94204101c4040180c1d030b0401c550801c2d29402c112101d10b5403040000060140111080c0c01034503010408440400c2161a03403030b8401c007617102c0c203611140072550841d541403e0745042e01418400074a882d401050345400750320f01702d04008101c00518041140441c040c8075445800c0704d1900034210658000c3c112203440200402250101c079138281440034000000740071039100303400c6074010020085615000b00e071039107000448404100c5031980554648030000404502ca802054043c0e9403004000e8608036014100316080600c400741e0801e03035081802c1c100323804074191041c0c40003828603150122040b095801034a0030301680507490b4041600600c04081ea04041e1040981c104d01c03030b81020300910040105c41c1d0003525184d0311600328800d051940900c00e41c0c001c45c41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 522714370 1250 522713120 522713129
    0x81e030f1b070509060d140106180f050f0705040e0406060e13050f0c0913080c100203160f090e061201150f0b0316030902060d02040303020d080a050f0609070c0c03050304 75
    0xe507442030791180700748107284104a40a5131b004107a0b030502c10202c3e10855010091000940000c9520b5807102200300025094668071440c0a40d1850812039125591045540020082c1d04000d6130741000d040c01080d44c019800344a858001100100303040050a9004000505201d00d030001e251400d84403c0807051000070055600c0d0007140740c1c0324a00324003c202601041c800400903400c980350000710606016a10200719011407082010105050082010720b0482024500250fa03a2904501510240f44551148000d1192031004065026001032461307054400315508a0380e2075865a000030200c410342c1c4071000003540782c9000342011b103a00750b4118003662110072000d91980d43c3d03158210010321040703d5031030b0708004401c4a80409407180d0401d000392800180001e04003280490f03404201d03800b5600450141e03100c41d01d4101407540009400d5401884514208142e00c0e2660003d06a0360300284080d210b00500000191002e004164401d80350350407010f030600040e240c2c54401d5403903005006 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 522715620 1250 522714370 522714373
    0x19030834210806010906180305010603082503080a230a05150312040b070c0506031602151909051213210203030a180509160e030601081e030f1b 63
    0x950021441c05010b20b1801464184d4546038200e152000450300350305002c0720030810001c41000013010503000d01480c00690300803001320765500c0e408080740c0d189150b15204072205a05a0103604007003a0440c0403540e1044401c0ea001c200b00d14096180941d04c1c0c500315864401d510910309110104850303601c0513208001518900312050b11181c1050b6684a03c11420004c00000b00014890804103034040e095003882a40c44500c0c40e40c0f40c9002910941044402040628900f01e504010300d60420159002543d8107403005003a0401c40705103190301c080c545c4c0b400c0000fa203c0c0c500c5002c00604001c9018510102039201d52213200e0354045800a240c6441420070f4002c5a140701144180041c403000030f0503034018002c40c50b100743c024064405c05482113841107214504031001401780c80e017140c0340784541002c0c882d12a00d00106807002d4090b0f02ea9040b1203000358030800040c4141100002c02480020804030715010b801007611100c0e02c0c1d445840c000180c0c0800c081303449d08040c0c8900907040d405c281c8110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 522716870 1250 522715620 522715673
    0x2070605010f150c150c051809010b04030204021804150305060903121b0708070f020112110a300902130e10090813060e19030834 57
    0x1207219464582d14001c0c800c1068039410380c1c894040c016140d29808601c2100c1000d030f14041c41c0c8401341110071110071000810300000d41c4203500d0840c014504205c40d03040325003500c42d50502c0d20300302c0c1e907003d14040280103075800154845044249030f0740c07030110840217106101d962035442c1080e0110079203100c2120750b41314800106d80388071008420380b0302101d130403014004950303a003180f128900f01c20120300c905182c0701004804041280c0c0402000400d000d04410b00e62032405100042c141121080345d00f00c410726051b0000300d01c0318903104403406129a4075026900880c10141c0e10080752240440c5011040858602c9040c0c1800b0340207100154003c49080030408030001200f0160b68580809040d0368000d0001c1914026450b4010200d46005612032030401421005c0101c064103907070440004200c010004459907d0a82003806024121320b203402d203881d01d1a983d0f0b001500039510b80581c404201c510700740000524a85a05a00c4c004000007107060350681490303800c00c0311001c00540c4207500340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 522718120 1250 522716870 522716879
    0x702060a1739070b060d080a080f010e130201111513060c02191b1503060503071217030a020f0406050c01050a05130b0c0c010c0908010b1c0308190504060207060501 72
    0x10003010003420401d102181c030b8503081e95104605800020815070340080840b001e20040f03044e0301c0103440b0114043d1270b5600c1b1403c09442440306018142d0104244900c04410450050001d02c29100500c4d4207007050401030a40100389810132150105070003c0c440880b040003030aa00d014540c0a40c0380c004c1c50108200a2001c0301245c0741d40019400b0030300000a40b000000041040c200140020400001d0004098a5014035406940794600400000381c41d03880a01041ca000d1007904024182592000300380811596500c04518840c0b80c40c52804030040700255140403075404840e00c050541c00c0095403181c07140c1000c0c02c01e4100d120101050341c0303442d00091310703412917118190051045107009241340c0f00301c0d036a1500c2400d00a281390314140781031100b015100402d000c4c00c07286003c1030f1a80b5a80c01d040c048210308650610040f40e1059145200510a9000c240010a04c0310303054038200526a60b140032000c8140c3e42900d2100d002840e1108000070f0000300e5000d89052031040400340030503642e5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 522719370 1250 522718120 522718201
    0x90f09021204111507030203120121080c010e1906200d050a0902060a0f0e03210315100509090a0e06130201020c030703050c130608030702060a17 64
    0x9070451004041200e101003808224003140d00d07000d0142c0200b0320030302c181d0014280562608240d0040b80903078004100301126282855003036001d81a640b1404059804040a241000310540f2024151382c40c0010f0141d0748000039005080013003280b5013203402071381d8800003920340f036081f0b41001d4818a240c131000000c2540c20008071441d10556402c904c3c02e2910bc501310b60003d00003e8004029503aa801da408010f80322540648580e641c6d503110b9070b21080202c24003a1003d050101c07024403c0c0c0084180b5918040000d04818441580e1030040e9120f5591000110035002c0100031a030744080b090040b0740c913490307000d0014031612000383c030214069111101c03558281c6450041c07a24403070300110f0018074002082c000e105240d500505c11141e88080c6000800d0a1251580041c0e03070a402480000e512400d241040c4811342100010800502d880c2c90034450b00c0e8003415100a2140d18005440341100340b00c0d0001300112964000900f5172424021450700034003201038003c102c141310401494455198 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 522720620 1250 522719370 522719377
    0x102300a0e0d18050909161502100c2001060503010612020d060507050c0f010c0f0f091512050f010806070f0801050d0606211407050f090603070b03070c03180305101a10090f0902 78
    0x9400074540d40c0031448a40d00581400342c402f03400c00480c2040401150f038100c81e91001810303483e00000d66542014145400c1d00c12941140c0354610300c858400f030060721440e201e202e1458002000003425110030302c0403220703482104005126449201c218086016041d0f10039504060280c5940f04845200c4406650800d40c041d9040d02003a40c60608002c010507690b204928030105103000c214032200840d0b8141290020f48140d01007285800060042d04d1040101075002401c07400c000c03c0c19000070038010500c0105018440c0161040700150003040f0143d00f00101803d070380348240e80d801d559614040c100000d0740c2410760741101c480d003034070380002808070b41da1043d283d0150420401c5100700c02402110000508450f4040c07050003c00628805501c0146001302d016507101e071034078101800c005103803e045507032200d4034240902040001910000720710041c2040d007013001c200180c03e060038282c01a40071322030345d800080d01601d040c009a0b0103c180e1043d18000a60706000640742c0e00b01100b00d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 522721870 1250 522720620 522720659
    0x91b090402060304141c0503100504110a0c11060a0f0206010603060f1a0c0111040303090b0913090302010e0d0f0329120102300a0e0d1805090916 64
    0x2040002c1808141e00194560002125030200c0b01c2c030014101c1c0d508410341411b0340880010b0340c04024400b14050340c103401340080c01c2c12034060116024500d0881c82034800c003000301e001e010340402c204042002d201c90076106c203540140503d4490813503081c0034098070080c016050046c01140f00208070039010b442a08259091025403102107030504401c0c00302c040035114070302180c660601008589036000d0207502c4d00e0b00351086410307860f5481d5203405049180150002c034842503080c048481e25440307042c10003000072a1018042402d48a50900340d00400030944802003500502c807079542010303005070354440c90a0035a0350400500c1d203020111024203848002c0c441c0c07a41e054100180d42c2d4540640d0350000718211760001450314007004000c81c4c2421000c81c0080150034020605000444008078490b4000d0819509100c501250184161074a401e56841814841d1000703240714041074603441e0302d000d000c000d00000120f050210000e9500c0481d003600c52080700c111312012500c1d0380708421944044c4c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 522723120 1250 522721870 522721879
    0x10e060f0102150105040e0a080d2c0307030c030e0a060504170c0d0b060a0e01091d0109030c02190e041401060522020f090d030c051204060c0f02030114091b090402 72
    0x20303424172003000058900341d0f08480c6684140502180480d10039401030214001d0090001280c1440d10030f00300300c0307a1504560448556104010320380b2441d02204035110300d581440e00109024444c030301a039030590400c0000d0741062401d84d010428a402000410039203040c0054014210217001d0015034036000d6603401a0040f56000e000320002e40040011500003030010001c40580703031968141c072072440c0241c2c0210300d030584440400b56803c0c9507000c100b00920411001344405880c0d500c0180c081040d480009018404800d5014102000030034001d02402c01c41d01e07020128180742c00d11000c0c1c0990f080d0040036070f51802c84009002c2c5019600274403480e4046140d2000001c030340405000a420030300c1c490100e81e10402151440d50f80d03400200c0031651203604c13844061000346c102540b40c070126000300c04168100300400e2081c05d80004807840c01e2544a441c1c80004855480407a0141410b51509900b40c2d20140074041c02e140702080000d1820020700703151018080703000803c41c1c4500141c40c0650030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 522724370 1250 522723120 522723163
    0x200d18050d020312070317040506010f1715041401060b1206030a030f030b010509040c1220070609080409062301170c030411130c03060b0f0a0807031103010e060f0102 73
    0x40c034130b201002c1c1c601070b400f1341407810007410303400c1a1a01d0706504460442e0982c0100c0014802103101d004004064500d0680c560745095208d0b1540d9030320300404030600b5103180c3e104001010040701c00700e01c000e0402c14074003e206c03942d6100d1014581d41c00c810b204075401840b42c00007400f0f07420f000a405165540590f11048241e02c600401d9009181d909802410031a0401c80800f094a5501a03060400803613501e81c201110256414400c5038424111916a441c02a080c9590110508150740c0c0d03458001c9000680c0c0c4031140f900c1d070880e1040f079000541803820440f002030781901a2000c2d40d90300c8410f400c0da0040f8200440110398080c0c1005805024260030008110f0005616010b1540b16100c1e120380c043c0c1e90021000070b61003c05001e401c004190b140c0e050752550b540c0c10300401009104141340c403801c15120b483c00030150702500e0310311010490031134001070301e0910070340250440202401070581d595071a6145041c012008885150180b00c811640d108154030000364007040780100d0300400203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 522725620 1250 522724370 522724393
    0x2011a0d0219081203010513060302010806010e120d0c030207060513090b030a021503090f01090c06050705030f040f15080f0a05181c11120406200d18050d0203 70
    0x4804501c02c1c203440b20308840360350120300040100100c09543c104050072a880390b2400003005000034100300e0451201d0b040100400060f6045000e03285c0090007400c0c09034030412540046032008850400c0001940b0070f5040004401d41c2014903a1000e9010b81d00380c40e4001d440301001e8605114444a070203480100100400c4400903a5203c43c0402070000c0603968441e086400080d2444a030f00c01000348290000180007915004000d480107803a031400090142c9486038450031525012841030105208000442130100b100a00845400d003441c48805a100d40c1c07112108004440f150003540c1064480c42405160315001da5a50303807248864118505290341c07028482e001034000580301c10050a0741c46404040f00005010301d42d5100e110003c031905400e21400000c1c00b81d880f03005500308070b402c488010100b49441800f02c9041e01c50380e090504070710102c01c9c034042d00d03142c016194000d81c5c01941880c0f00200d61225441e80490a60b02210103855240c0f000c0028170b0840c0d010082d0305d03521100c0141c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 522726870 1250 522725620 522725629
    0x3010e060a030624090c08061314090601051305010b0306010f11011e0614061209391912061103101d19051506130602011a0d02 56
    0x254003060151030a0001903690303580c0c1e025900409a040c40401059050240c80760704440f00d88000c00001c0d405000c02c186011020301121000303001c841c0100c0212581c40c407166402e40140d6040040700e4900801d91406040881d120f290071b01410f8402d5040301c0c0d10740c0e401f404030300074103060b92030140f04145103840342801503444489284002c0184800d410601907081000c0c800e00f055a079215005600e143c1c6031201d81000c45545401403012012924442e40032621040c050b500c03003600002e00c1450701d48138100041d29003c022824000d0503800045800600003000415034095500010040940746500081200401180c0c41c01500002c00300401c001850000e002a1a4107010b5140007984201500b00c03203009074001c40340204092140541041407101c6030300005207c050100b00b100b06030030400c3c1000c0030701c418000812ba507547ca42010407850780d01072102c44483c9500030300c07261f510044034001c03843d24002e506c07480001d035107045c2c40788444000103004203100c00d90050502044210076400c20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 522728120 1250 522726870 522726899
    0xb030702010e060a1d0a03020c0607140a0305180d020108061315060c0b0109090312020d020d0c0e18040b180a0507032409020a06051e0403140712080301 67
    0x404540d01c5200160481e80207000c4540075118402000c0365210a50017001d040e4003807034004ca10180d0100300e0403008640d011810994003601240c00950381c1c41b075424840d0340008104124402c078091031030f11804054010700208002040c21014400b5180c0c0c500030003070380c100c9822010340425602d50000d2078501e080d1030208139210030b42100041c5d02d0a8002141c0e82002c45800203400705903128074500c107200400c1d402070b0050500c4a4140030900c510303a802492602003805039101c030780d00402c4d0400c1c042182d805540072903c036202c0420001c1c8614100801100ba03544e0702901070054143da48400031550390b1030900c0340d50003003140b650941715440c40c0340701d112007460140e9050140c0610a40014030502001c401140070b102030751201c1c511084074901c4460405103081c80c45180540e8900141c42d078032001400c944003418096203d1110104000711100c4014110403196000034000c0300700f043c0300c12038180d0f16014008490034203440b03100d030840c0405400c0010301859014001040308003040c1244 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 522729370 1250 522728120 522728131
    0x140d15021303050601120204050c0a1e0504031a0a0e07080606060901020f030d0905011a18040201051c02030f280b061b1509010c0c11040908030f0108060a02030403090b03 75
    0x1214000d82d030300d44403076050038401c0e004420006600c0700200150710300750044036004003980910601d003200001c0d0107021540018503100810a040003031026a0b40240d00382c800640d04044103000340d0303024590043c0302d40821105050300c0c0e031815030801c490703080014452043c2d4040c10001c000c103840d5070007006119003003040198110703c1800303a002a6038906201904110700b4501e40855540c0c45890300e02e00b1b44500120340c0c440d01002c801d60118a9803051500718121640707480c086000d850303900049400303100d18581203000b01030064043e01c0d444e03843c7c5c0c0210311030070401d074200740303d1b071100e0640386c0e101c0743e030400745407412120410076001c0003146d070303000303c40e826001400280b82c22034010891455030424800c01c030031900011000100106c2100e400b550140d9180d00070090b4502008000d405100003810103000211042c108047c42d803203a510034100c103900a59095100d151000b00108284403d01032003203180900008903903500d119000341c901499140d02c078542058105040d84c1c8940d04001c01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 522730620 1250 522729370 522729397
    0x12010b030a020d02031c11104a0a0b0906042a0503061509070806090114010507060905060709120f0f060b0d030e03070b0408030f070c0306020d0204140d1502 69
    0x240e044020f07940161011000b800740d12600072a42c06030400e14202696103000401c00c8d800d100003190000000d0396a800244d01680309015100903070421464950b00b504c02c61100030b4820b10180f5885d140001d5400c8140d1312890043d411039a400e00c1194840c0300640f4004d0400da4440da2142b030052000c83d56010400b41c5446d000c08455031080041e142c040c0c191035a1814410f286e5980c0030500b840010150303c60fa450401d0461401c001c0042a4104014490344460b402d003081c030480302e60b2040f41103424640e00020140a2900035003000703034039420183c2e290300c0403615050000629180100300d065055030480301c0441c110345c550f11041c04081c29030f5000c8544a9a07400c120036507660300180f00d41031501036074414070030080c0d034014140350410b1341e000302400d00000e110401140c1d40000403144100450f80c01151545445d282000700c1d503a513904000d00c0280080b0f94101e214909501610440704000404100e44100c40d0a101100c400d81d240541020310001070340c3c0400041d40c0080c00c83ca1400322 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 522731870 1250 522730620 522730633
    0x4060f1803060b10021b0103020a020708070b18090106020a06020d0f051e01080c1f0c0b04050c04060f06080628140405070503090a11010512070e12010b030a020d0203 73
    0x4040c0c03888100d03820403914160345290b1a5414200701000204039200c80c001400c0d030300c1071010035034111980400f0382410950009010007a003407080c0f00c01e0b4000c2100070300f101c503071a48400c0c04070b20980001e220280d20385580c0b200038000e8a054031605040b01d00907009008401c2c813640b5500082c4d405140c001c00c20035100d21390210700d00c0040c415141700e46041c1002c0c6c0c610042d040a8660220b406030300031102580000b5002015540d00c81c50f130240d00f04056140c10314644491010b4442e002c0200b00a0411107a03c010042403000104008440080483c1c040101e20303181c06880c10b00b1074050065400252000740085d40328200302c5c503048e48041c003d105080402566024080d1881801c2d0041c000d1001050825182410180140d40c0c100d44030707040460840c0b4000200a9480206080186c0b64085154900300980d00a504480300f618001e2910a56490214000f60003284605825400369031169485541d01a061180c21200c9000801401d4280500c1d02080001c0760001020f9901d40200d9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 522733120 1250 522731870 522731897
    0x50924070917100c03050601172d090606060a050d0c09080f030703081803070807060f0609090302060601020105040c1406040816061701030f02120102090901080717010605030304060f 80
    0x8000b0690070503003900611040e02e161480e0415501802052014142003d09000355aa002400701c1d03070002c108c1c00c1c01584c0d81ea0700b00710b10340e03401841c2d420710030214056a41091504a00c2c90b0440c480e9542e4011179000e40c940205110700313071140d01e005c1c0000440900c10410401c07529040618403d40510b04040c01a49480846050102c400002d500c01e074000180d020405811400d541e80c8141a00303299910f1031591800700b6201d11403000d0060541c500001d440040041c1644464060701241100b00440b507244c84035080241580501503015101301c600190240d8414020741c1e00c20b6a000040400b03143c030b803801800382261049c0721300790300500600c80400c152204010810000960161503081c4901c2e01c08090110101502c0540504d004880144045583d203c2c0e42d49440740c1c1a56034400032507188c46410f0090042054095106004100006ea140c00c0021500140c809401c14588002d0b010022142201d41e0361040d0764154006210802103540141d451240765407a5040000d00405c54 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 522734370 1250 522733120 522733139
    0x10c05060901050a0b09091203091005040c060e040e0a140304120804060f0c03050414040212040c0302040c030204061713080f0a091401020322090e0309040509240709 73
    0x8850700003280c3e41d1101049100c81890058100741c40094400c006c5e5030402c0071565440c2c00d2500c1d001419010000045040d1240c10002c03144d200600c410200054142032400d01d0719000288100c000195014071501801c3c80c1600c101c601400c0c3c1600144503014140e6204041012408512a9540400e00000410030f18a800b480411881015515901c60a00b038000c0c2c03800005e9904542006031048294000980080840e42603910709460080281d000e039000501904c61110f400b90701d4010305041c0b20421603441102d8040c2c0e407007101c0a2110303520008080781203000f2440b40c00009500b29500e2000c010b880148907801c200d0082c03891000c400c640d2a8907065a018608030090a1000070302801015800043c0c0c101800080815000c0c050b80100001e40d01e024046450400e001d40c038611135062140c5005c0e180080c40ca202c02407203ca200642901e8880d007114140d94025814000001c1d401d0301c021402d404071a000c50001c1e80340c403130811030000001000401c0c46050002503100070800409 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 522735620 1250 522734370 522734383
    0xf0114070602041e0b03010b0c1216021e0303070f020303161218060906050d0605130b0108060303090a0b0c0309151b0c011b020102070b07030e0907020607021b010c05 73
    0xc1c00c005a603c42c0381662030003945003078807214880c80c4c120b590140800103a00301182d0448100340c402c02e4450b489020311038203107410300002d170b4184000019018607540b81201841c003414021141408080700701c07105020319806030704645070b05070020401305000030451002c0380e401c1400a81144e0030188184000038170031044031410754400401e11400741e070561740610381003502184094400042403801801800340381180c000c0c1c0060000104942003403880d1503000320f008010041c000c488d034a0032091090b000349420040b40b030026003080300003041070400000b12b4005a102500070321b8a640740a98042d459003000141c600240001c112200e803651714402c044d071081080306a41680c6042c42c40c9000c011070f0240c0079420207600b00c00c56510042e81c200040c40103185075003040ac24101c107540b0040741001200c0e0407030b0a04000100b6000181a40024504000982580c1013891602c4021040e681d41c40d044440710010f80c0074201e00c1140a00031001c04401d51810b040480c803c60095960608009 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 522736870 1250 522735620 522735623
    0x7050d1a1807080102122701090305031503120301090903090f030515130b040b06040f052514040b07060b091810060e0a0c200f10050112020f011407 65
    0x10420021042011018420301d0b00820464000b140361005d41099810b5154009250102c20340054405081000e202c0340c2d1243c4001240c402040300103000d15018109410944000c40304140c40d9641c00c0590800003919141d00c0b4060507910304582c40e01c4a49005008170201c02c138204800350100040001039440450013941c4620050f04507081803a450307007081d00c0c0040400040f283c2c2c0c003d050021900076a14a42c01913000110080ca070354039a80810054000c4501c0002d1003403400042200c0c0c84581cae420082d07681c89d00312441c0800c00311030b0300c122000140390b421401c6d0344d0420003041120311ba810000340344c81c42c82000041803649007100003070341e0100c04603540038a0100d040025800340c1c44c18020810b0200100d0020803105040c041c00b04c4200e58002c0240000e641d85103401c604860082c4440c41942002c2041043c8040e481451142c880c0010350707102c0c1d000c1c800c04844480042c40e601440d1b040c0c501210004c078004200780c00304000703248190152414810080c00010041c81400000c00c2c085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 522738120 1250 522736870 522736891
    0x302030709060920030f060316090e06100305060f040512040306051801060b0f0c01200403050d0e1c0204060801051003020f1813060b210d02010e07050d1a 68
    0x14909100e40007600c8a0f50001c0441c0e2224054135841c1140070810350750028084207140600b59a4407011078604504420054000ca0740100c2c00680c011103030b0081e00303092800e942610134a450f40c000101d401099404002d0160304004006a10706503207a50303032030b403003401003085403501d41c1501803a204544c170036082652050b407510704008100000031303170221050214100800c041c4c1c0c84d0000031880703805043c2c4100b10902c00015510075242c000d40000c071f01d0004100114445008812941c1d500d684103100498840c0101b0301c5000840d0b000d002c00b900c0054003c3e212146078003407816802d108400c0c203076017264415a10000803070380040074802e452180402558a00d5104c0c150300402500300b401c001468400e015600586040d280200400c64020f0700311028046180782c0d40c941240a04a0364030368130780000e0f01f115617680500f031005900d541042e103481521089460070070b0407800ea664400346541c0c950320880c000c00a0303090035608030034001d000d04040c1c14001c20610b41d10348084420341e103000d00f0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 522739370 1250 522738120 522738131
    0xc030d0e15190921020f13090605070504030b31030c23010e0604080a1b120c03080115170910061805061c110d0206072324090102040302030709 63
    0x1000034040c404400305452130003059640549900003140901710030038060145144901440e500122034000318009a407255040c405032074161802000d40e005840181d8051610801262120710107680d04070740c564007007a1600544560542c1e450903690502812000c00c040688410040340405420104440c040c4006086031410700f44603900791220081e1481480d00334200340800100c58000316155421241030401150399031140741c500134402d901010700764030090b00c040311030301d03a024105920310f03480385d1624010341e601c980d00c1c41c2800c011440c00c0c4001c100c29510034502140100b51095205128408485414030211210401d5a4803035015448049914207070000f944e50038000c441e0301c200182c03401e415005000c0c0c8144e006030340541c00505036054114001036283c41e400700b16940142c01400c03481e601c40180c070b0f040f00c0080100c0800310b58007488282500c5400f4000c130315503034100350341c00c1604400004081c90541000d4007038505001c0d0743d401c0000000580341400508010003208071300054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 522740620 1250 522739370 522739379
    0x506011707111218130b0a09090201140901170408040f0305060603070e0603060703091b1e06050a140d090b0906100f031e0201031e020c0c030d0e151909 67
    0xd00565140700400050082c00f0000340d103c404000d0800041c0e0480b17022595029903180140108285041580c03c07480d4500007050540a0781c0007844114400c2c0e035825981940c0000420540c0900d03010345000407030902d0307280c04496025228a40041c09010000e207000c1d0780f80f005040f0060319520407a00c9400417020405549002c0c40705100900b41c44040b1056460300c01c00198a50100904000905990360620010302181c0e858001611200400d05004141c690b200c0100702c1d07000066400a8181440c40440d655200c2c40c251000344000d03486184070828100f6404081c0c0e00044082104035643e00b1200340800c0389a00168060020400504a181040701a50304120002d0304117400c021032400c0c2c200300040e542c91030034182820706120f500d04001c2501c0124081e005480c0159036000c2e11b21410400d0345100d60040c425403810400316058406040181034464180e02841c801042072800c3c50085424021403011008413140301c0181742611052142c0245040e0b5068000081c680007010320 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 522741870 1250 522740620 522740623
    0x60b0a08010f0b06070f0219150804020f010201110d1802030105181509070e0c13080f190b0f06030a150605010801120203060c0a120f0b040c08010e0406050601170711 73
    0x3d460b0f0b905035595444d04042c0c1d1603950050002910003402150090300e0140340344899030580015140c0360441c0d40303086c5c003000d4006061f00010f880680c4501d808480e96801c0d0741c014417900104101a4400383d0600250031032030001030040c481c0302c030620f02c0350303084801c01a035083c855070344946844a0140e07100e010316240306141c070f8000b0010806c0031b21414107006000c400055000c00701d50340240040b496541d12a021200c80c01020440380c25844946008505c20402161250991403124210b0f0580101d1500c1e00688000040b40540444001030125020b040350300301095100c0c4000d0110b64404041d6a11000c4030318101014038a5aa9120401d00072581e03c00ca185004011905100f551642d541d000242c88100191903410412000030360004c039607000c0e065900d8001c4101c5400c200324004840100083c000ca000c180d4802c2d4985000b03c1c0006009941850607103030706419813071007682c803070756944004c140152405051005c2c040301c400d51f54130700003031492148825507540d40c2552042142c05 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 522743120 1250 522741870 522741881
    0x381305010f1203090317121302030f010209060d0e070f060e0f0405060102150601141605060c070302070e041e061407020c0d060b060c03070b0106020d090302150304060b0a08010f 78
    0x80c1c400d10b4a00001c0c0c40440da0194550040e0307074000e0208881a0100008509a486058802d80c145c40d490b07800c0081105050002c69075150090741030300c00649405204901700e20900001030742c00f070000d0000345804c4c20550b1204008a2049040704c0486440301900c0341080780d03a0784040000707080740c1c02c4022039086c0024031101040c130a9500340701c04c0c1003140010752100901500714021406090006195030321400301c0031a002c0c040011a59100140700090350141046c81d0f06890305c1c46040081070030440d4002c202d45501350194050320039070b42450383c030141105006e003065854901c43d009100046080c01c40c1d01c0c0040b4441c40e0005400301505a051000413402003041065400c010031418140e1504039145c0c0031254040380000b00710003030500003a5140600ca180c6032107171201080c0f5004020200402d41d05031106a002c450002000b108101c46101781c41c08001e400181d440c041b18404050b100195410a106503008240c02c80b00380d001ca121555079a11043c5580c0d101d41040d044404248603e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 522744370 1250 522743120 522743129
    0xc030417150708010603180b090f0105010f0302100c0c0b210601230d02070f05010b030712080423030124050904050309010507021203030a1b0201381305010f 69
    0x1415140c01000508401c00501c0b03500306058507103940387c000e8050281e071400c6540c0c0c04071f100949400e124610940d1034007070703641c0c2c5071036503281030004602c804001e10030704116940100110540482000c00311188080321004a0301c060030207101160040841e400703001c4034003007580705542403800e407a1045c2182c0b10140410341404260049100c1d122250520a681001103410031a500c85903562520000d101c1c0045c040c008850784140e00e002c101064000020ba075108130115000c42d40c84007503255105c2c00f1480000c2c40c2e9a010002008000c1c0c02e0454500c0c1280c41500e07550b507101c0d20384042402d442d904605c04d508504100e55031246c0d048108803d4029003400c7d50406031070725160351600d0343c1c0d2241500c128140403010483c9021941c9580e1408901e011200990344c5a00b480805240a400715020554040010b01c10584000d40705205413045d02124889003841c00c12200b240d8071071078507020440d29682800ca0080800f68407800310200c0c688010b9040042c582d071600d11214404078413a0030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 522745620 1250 522744370 522744403
    0xe22150f061e2c0312070803040b010e1e07140c10050703060b12090307020a0305010f050a020702030c24040f09050112080f0f0417010507080906060a030f0501020c030417 75
    0x1080b0943d44034407250041c0c034a58505014201c50f804200081c80c01450180a41e402e010009202c0e08100300c42004d140264490b14401c2c0f11b0f41d80300c05d004ad0340000c5c201c48020700d4040c42c0c0e0109412070f10300518207030403180f00d040c411049008440900d030309900c00c2d4440203840d0301041942d160b00032540300d410f0340701c882072801708000740c1495490780051086c00141840c0007035010105010840074001c44400e0ba034005d0110f8404e41c0c0d240b8009001e0030700d100d1440106441e02000548003401d43c022140d80b9940100541a0010744804001102680403030341c000750301c08901c440301c084480100410203001c5411403000f0842c50001c2440c155031050300249200723410001048001603a0500b07440b244c2480c5180140ca8001c82481d0360035500580d0300000e00c9140324909041300c40703410f40c1714502440c105d588503030071a620b8540c600d0350348170706075005900108a02400c00100d03a2212225808511800c0050300c1c000740341440c0d83c5990020b4001c134030203480000081e140444204802400d24a8480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 522746870 1250 522745620 522745637
    0x602071b080304052e0f030b090f04020d150213031e050a14120403030c06141b090607080703090509130c09110c010c050a0e22150f061e 60
    0x720564590066111361400f510b040e2149088034400c0780040b02d10440b040d2400807a550806200600a40008a440c000f09140180c0b00d0424102901c000b84a007c200440301d0040e02e0315824480a801001000d41d10302c18040d107441c8440005000a1003140820024640c09a0030f40c1440101160030350901607402490701180b000041c804180d22840a401021144031861a0a043da06200c6031200031199050b001901100301074202101884190081000300000044c680d0400400d4000b511003c5c4840c600c183d00904003802480107001c0728070003401d100c1c140f4000383e9840318030740c002d11400c07408955003031024082c03800e200c070209a128220341c41c2c01644c6403164813156403003103517070003022400c68607034200c540d05440348030494141180510007000308000d65940100990442c50500000401e042c0141c0140d01e0580e811050804008140808a6032000d04100041030100c0070002184282500000e440d07600020303400050646444e441035040c2d4201e000100c83c11750500fa841031286c2c80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 522748120 1250 522746870 522746879
    0x5010806070503130b10030b060d0201021b0307030b010b0318060f22120e030715050306041523032419021306050d0e0307030c0318030f0602071b 64
    0x500d1a08800c1c9410026501d80310040d0700401c04040c2480a8a641303220300c03e000c4d11426450050048074012640c2140c5621844100302905006460103801640102c81d03c4144100a0f1004600560024120303604a940d943c2c8400643e5801da02119030500080100000c10342c2c403034080601a441d10003c1d00051074041202d24040c0000382c250640051400c224481e003103d800c072035014003500300d4058468580020b500070f1010b0010318406019018050000903c040c0c2001c0c1c07050960001d858003030440d51508240320040c008101e030045459883d000015501d600c441d2007030310a511203400320f20340c0910b91040c14901416030090400035424081f8403402c104600000036040051140c205522065000702ca4002c1e014580300980341e11000346001462541010040070740c801c402c0800d001e50050141a03079280d0150040207804540540b02c1c806c002403040656440e185c510038a0285015101d4032085000c1c605454201c900c5540000d0280c00e0013864103039581d066101c108072100c6203050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 522749370 1250 522748120 522748123
    0x18020f060a0c060c12020f030610020606031e030936062d030706030603030809030a090b0a11060103080d05130c06030902040b09040b010f09020f07030f051c0b13050108 74
    0x101e8000d07207040d0743c44413660250f034842c09140e10541e08241042d9200c041841342d0540750b40c41075440d00c0c0b007021030743c03e6005003d0002c5100361080e500280980b011301d040c050300280300602844c1c41c40281c001000054119a24815415100c0f280d0411202c40d803521008003c5910309540e100482d42d507071501c02c02c5a6541ca5820745a00a950240403417010910171500b40e10805007100100d60500030040c0c0460115810391007401224080d0b9107890441d105c040089480340b058440800c0024032040051082116000040540000b03600d4000950f414422107070b82401400c0c0c200f241c511a00041541002d40349010701500107041510328a081c110320303640c50307000f84118032400052644501c49603040d035407258814620300360080d081c84120725007854602c0d040d02090050000105a803a000300352180c00e4820344002440c100255840d00721640c82c140c40200828a400303042003810401500140a03102840c840500700b4000807503035074640c40801241c840c14000c840406c80c43c1c0b01c01000304100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 522750620 1250 522749370 522749387
    0x1c080c0d020618100b06070c140a0504021602010e0604090203090618011a0108070e0d140d23071401020a2f070902030603010603020904110f220510050418020f060a 72
    0x101140005d050450480401c0050007101d4019003400e0310790000007600700600641c1c03403042c2011101a180c1e19103c02c10402240901c00d03410026090002a12005500440149486440050001c1d0415580c0c0303d0b4901a0b0303000312003c021942010042c040c04240c141c01c281c0401003000b00070300c0030308000b0942c102e80019041c8042d042003691001319000e01d001d601c00c0c0c0425400584403c100050604110620610098500f01c142c450ba481d01c0944903c960411141425040c40e9078519401500305d82d1001c1d0070002c02550500d01480748800300b0700713007440100b5a803125915903070b200c0c0030003801000f80342842d80c1c1040e400d01c0103061946600840401d40000395060100010389944810022034010b02c1140c100030b40000c081c20074032040c04074512102c0d54001046509110001110050090005241d5038000352541910000710704050503070001d981c40400310001c41501596100001c0c03d0b20034000c00358229074003102600c0e042d030030b014003031a500c54070641c0c0d40c0b0310381030306800020301031030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 522751870 1250 522750620 522750643
    0x9070e060a0e01030204120501023a0e01020f030a0902130614150d1e1107030504030b07020109050715031506050306060a030207050d0504150e06091c080c0d020618 72
    0x241a94858002c3c3e1301030313816a400b501c0c01c0208482c14174405d01c3c0940c001d5102c407480701e1b0100c3c51080d000d107200403100400300201d06400c0030a92714a000c42c40c070320040c2c89090000c01065409201045c20244044061841560795a0380415a040da40c01804400c000e0700034218100da06161042c0a484002c1c602480d054501b560501c0442d81c940c520352020740110750a910a990238119404000d41145640d0034191441003400c0081c484c845501d9481c82c0f203954402004a103091100304086060b001c6250b0340003105000209450300301d981d0b540d041180c660400580a1060180050202e500d44904412004000034005000d41130840282040c04003e00b414810500000e0301202c1c91b10075011f0b108107a501030105c880c4905d0460002d002078003d070140903110700100b00c0c1d0700e00d001c1c03183c5a1000c0d903603001390045280401c3c00b400e10811506520010f10982044844030002a0843c00103005110300d01d8040d11081c000c00c41c0003402c0c110040d04041007036000030038a8091302c0c00401c50307105c80c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 522753120 1250 522751870 522751877
    0x908030f04031715190308040303030b09070c020d020607150504060f0b18180a0615050f102f03160c05010206070e0108070e100201090210020d0504142206030209070e060a 75
    0xd10352442500c840c2598000030465440823030000101340d019041403540074405c903444140c3d6a20b0800486802c40c0c8200061361012948041c5805818984010150079000351a404d0603d005900881e00344c9400359001c40d100c41c0d6800903400c054105218009401034101c8401e070844044014040c02d1941c050803c00804244030401c800d40b017020085e0700d06465101c1401c0c441040d03400651a40b05116110b0b1b20b00440c3d002c1c40c080c1f50f43c6802e00e58003d408801d61615411b0310311011901c040803400c0071807c0b98004480c451500740701d50420240c00303038400304009031040a40901d040140c02000c2d82c4800e040d5448030040c400c0d0181c118419800d600001c5c41c4c00c80c290b545d01082151054240c0c90300d50b07000801c02c55140d41c0c00740d0642100a840b0300a0303078282c00b1000b0003c001ca07a940030390030040e80050428030050040103444121294584002415044620030b82da107081e62454088402d01c0c54240d90f1081081142012540340e07600100e5400c1000c00503080c4004a4002d103d0459002d081 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 522754370 1250 522753120 522753139
    0x11120115031d06060f0105040602100c02010f0603061a040203040c120303020403061d070e010503070302190806190b040221090f121e090a0e0a0908030f04031715 71
    0x5110b50322160811024844541d080c5012410312038580c1e02c107940b842d0040c0780000c0000c5065008100701c0d012107449030300030714800c2c00440a081c010200814000115500ca0311303144c030986428000c020195020b100001000300040700320840d40214544150700460050003000b010030448262181145c06540ba4a41004a940345c120024412500020019840d052104031040d4680503ca8013003250a42190181034558242403501c0000344140c40d07040c1e009401c04e00040c1041407802c9840e4440069203500c8507124a40203040090440304c0f811505180c0c3c1d000c684088041c042c02c40c51000c2a5411890700c05141d0740d00c5240410006800d40c1d03103855902143c05200c0c10445000075145a0080e40e9003c4040c074072101c416403126180c0b9a00c040180801c0c1c81100d550f504076040540020b25001c00c036803900b01d0b1050400310013070500507100d07035500d07400000c100c545008600c120426110500d42e407601c2e02e406062186013140c08040130b00d5600400a0980e2451132810142c0341c120703060180c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 522755620 1250 522754370 522754409
    0xb07050c2103191113080f070e010b16050f03070309150f20060a02180a0b0304020405070915090513020304020d02130906020c0f061608192904111201 66
    0x5448411480c08040c00300250b0342c42c1d91809813001c1c42c280c0d0150401e886403e00b00c1d18a142c2c2d1282305000706150740d000d810041054104010041405407030028040c4044031242c0c9507241881d1002070380c00c140342c00000701d0400301540300764080701402c1d09214454000540c0d80c0000d1103030350315420031f50a000003892140081c921601451340e8481d0305408680e403a14188090030065000386c03036400000340d07084441ca070944c500142110183c1e00010005070450f51f881c2c007000050240609000180464010042050507040c07150044402c055140c28910710720301401d0002c0ca42700c14140040480c818002c0c000141d035200e05022020360100c520640044205004600400d81c0e294000e001c28400500200e0480011425940c1c3d02d14403025a0f03025610402c02e0340b0890341c03040f0032800280c09240015101c0070140784210340e41d030008000040c101048a000e0343c4150400c041d0b0390547d5140700002c0003519180c0601581014401e8800303084c080c00010308600c1010600545007441d444038038400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 522756870 1250 522755620 522755671
    0x27060b2e0503130b1005011e02060f0711071716060f0c02010905190806070c020d0305030a0b0603181218010305040204150b0304030201050106050a0801060c0c030b07050c2103 77
    0x2d0b8158204d01c01c488142018041c0c00814002481403c0c08981a540000140c00034010302500c1440f10380c01902e11696548941c80c03030280300514510078400a01c000050000040055001034444c10354041800aa5098100c2c5031802e00c403500c0c4c0e1003200020040c80001d50241b2a01c24030219418044500b55071480141c80d24201c41d0406504040c1300441c510010102038075174030407600d80354195410741e11505030840788245442000b0790848000701d40710002038450304c02180d120307075005400229040c1840c00201550b1007640d41749603084482c80066940ca0050040510b090700c0e1850540c03400300041e180c0d80b100e03410300c0085418540d4580000d030941d100c40d080f82c001102ca405881920684404000c0c800360820741e02500190700c1c1c1000070402e1405802101c103414040d4640d0500e0340c1c6444421150a034094404585500b261403001000540c880005401104240c46c0c90340c17201d60809a00d403810784d0740d40d0580204007100041080c070240001c00c40740c00a0b02c110510300d20800820300507 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 522758120 1250 522756870 522756901
    0x140403090b090a170c041803020706050c0f0118060e060f07051b030705030415030203010e0103080903010f1416141b0a080c060109060909020a0927060b2e0503 70
    0x22682c1d04181360341c442c1c0c460042102d500c42c0200301c608000c0e5043c0307010078600d54244401e0040160340107840900005003d2006050016000c008540c00701c40e00b10034840c20f6590190b8103408a60000600e0300400c2182d010380000780886038002d0015140030b44030504104009462542480b1001902d40c2024113028006000740304000211b964801346840e1403607072640301d44142043d865507030110140380c1d13103e4000c69040300e03032031030500c040d903400c5464410301075002e900140d9140d0340c2c803140d0880c0d02d00c45014040240315108030340e14003442c03c0075400008035200848a03041200d010b0742e14400d04111016180440404603c0c1c3c5640c40101c0e609625145a801c8003400a40c030100700b140ca41040040c0a074169000d504041c0301d40c1d0b55070b08000b0b05840b1788900096011400c03800070b010842c2680d00402c005050f8a86d00403a609150040c115407074000e09082d12480d881c0e20303c0c1021800e08003056003090621101e00e290180041010746064005140c011080110010100e1403100811003036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 522759370 1250 522758120 522758129
    0xa020301110702090c0c0c150d15031104020c06040605070c0f0c15031107020907020c060d0905060f040305271002010b010809070b0a050904061a0d140403090b090a 72
    0x801c03030380c030452103032110702c0e00880401c0f403142801d000000e4644881030262a00c034480740e001410a20048002c0001e6440c046d070031454402800c1c0403d0700d2800d030340d0181c5011040411800000c00d400c50901c0e9903000000105940102e0040041d0440c01600241580c1c4c020782050001500740c4506800711041e401e0f1810161140030b04010900a200ca80c040070300c00c48560300080d018411000348140c0075181209034417016100305001540140c14a07480840d481001032042c0d03480d0281c032400261041d0400718003800001d0780c0d40e40070010480e00b004450f400801e808150300712450143d03001042c902c1180741c0c2c01c0204513207104d03000410741c140010f202040c8004100042280184200a00030000d01080320b00064282000c100360070004103240c0141c480e404081e600c0c10342901c0b0107a855a021210058015949500005030f00c00118129152440300031005503031400c190b4051826100c41100a0803415231003410b01c00013a80044420b0101c03011002e1213a2240480d000003100104140d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 522760620 1250 522759370 522759373
    0x16060b030f0a050d090503010c0c14070e1504110f04031b050d03030f14240303040b07050a0b100e19021201080609070801020403110405040f0f080714031204060b030a0203 75
    0xc01c0c41c00c00c0f40120b807940b40c081c040c2c0d03601040507917107030101400d03500902141404100c4030744251003c100c40c00112000c25140380b003191070166640784008005541111f54008220340d002d428415480d090080e4041e480d4030200e414282518002240f90600c2140b1000344401d20360354201f261814440580d2008101c010803414240c8454140070b4003410306a0744400130245084401d09502039a4885d15000d080d1081d02d40da82d02e6a124031004165603a5581e403075162009000010f080d42c860801416041e102e10054114600c249c0b500c001c00c000b0180146003070507041d54003031040c0c9042c134090f42d510844468011652008000010000b40f203030310940909942e0540012500c141e0024160340200c5e8414125000d40d503903069510f01b00e0003540401004180c000800000c1ca1038207030071040d00b040c002d0440905c900b04990310414030801d107801c115480500403074144c00f8084081c02c88202c2c90401406580b42020602c0c0703e007070a0400400041c07509a0301c01d00c01849880800640480944c00740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 522761870 1250 522760620 522760633
    0x312070c1d0a050c03040f060b0a0b04030609051509120703090308121b1206040e0316240b0603241201020315100f1b0b0f040c0b16060b030f 62
    0x1007040d5030402c448588105091001256110b2280c02c02c480c4240d070400d000c01202d40c11503403440050103031205800e6020800308004284a00d02c48001c0009500c0b588001a0000c028036055003030030900c40c03040c503a444182d0200982d00101194400c58854007000259503412145801d0f42e0800294001174000203011508114002c80a00307264051050340a240a52a2038000800e49501c506a07081c0c841030030340310100e00700f41401c0c6c2210080207600b0007500d04218500700044040c90f40c49409507201006854000c40d07180e1290040d9450490071170701444812100c00100391903103c080c1c0080441040b5004046981e40207980001035118001c10b0186000d104d41400c60103904269040000c1c00f0f402c4c40d070006503192013884d100f0200281c0d10b903200c03041140607080e43c00041007152000c81d0800e1780381c1c80e4000f071103c0c001284142c10319910b40280d41007a007080103881d04a50030801419000b0811810320701c416070a5420401d911490100d04882c03070401080c00d1020030800701081c1d11501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 522763120 1250 522761870 522761909
    0x1020d0e030d0f051e040c1a070308060306100e100b0d02180a14131814100606020309100203040806090102070b0c07080703112d011a0312070c 63
    0x1100404140781040380900041d003e603581041240e500340c2d545114004082d0041d50950354180403164410b0184581c941a166205090b0490104000c1c000300b6030100043c0c11030803d030b004100709401440c15001001c031072401c0d1180c80c4042c5da007802031001e00021071000403540b0300b01b100040d010301180d460341520340d5460340039039001c0e402c01805500d007400c004085d6405070030a202e0305401c56004d420140300442e41442441101512030031808106500e6180c0c18082e0010384014160140c030610310021400840c625440c1080021004100441d042c80c0c0100b2140340d0000542e0000041158510050110284141e2640c840c507403141d1010b0141f002006600c0b68190701500020b4000d00201c0c03099134030040044d005206880c0c0040c035000e028881030020030710800084581850901c106c882e0f0140000d610711400140910110028508201d824078041082c003032644114a841d1415840c00440d1000949076000d90104014420004c201c15051010061510700200301c4030703000315290a0407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 522764370 1250 522763120 522763123
    0x30a0b01060914030705190b0f0703030c020105070f0f11071502060c0c030a120b0d0b0402030d05040f0308030406060f0b040501140a08060409061104080a0b010909030c031101020d0e 80
    0x900c03407500440e40c4000c2c001292198140b4222240070000c018100e15810f1804000c421000c894140c0101c40b00341c0c40101d00709110900030142d0080e290803a5807592050724000b4107860851414000310790409e001d20603442e4000c04801c81046d04d42c201003980780c0d155141143c80c0c003007911492509208d013040014645e00e540c040c00700010555801d5969030340e10303218411920f204000d03104881ea0700800242c00c90a12540c6d4400a0384580e01300800c0d60010383c0d0004079100d00e4174000703030349404a80081c801145002c000c0002001c3c2e01d4208142011702d404070349031040c1c4030381c8009064504000001810003440e90b02050143c0f95840c00e80c5200c81d10b44403403d6082e0464000c4501085825941d04a1026a88113171045039405941d0120709954038024040a4200301604491003a12102c5105a005501000d080902841c000400e9403070303003500308282841c0e8103038480914a4075002030303000401d500510482c145901400d00c0a5015084800f041c024800c031124042c02da8600590142654030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 522765620 1250 522764370 522764393
    0x524101209031821030f1e0509010e0108011226130f0602030403171e04080d090b0a081605250204050a0509030d09020f0301050a090c080111091e030a 66
    0x20b150034200702d8441c0080d608041c0841001d5018055411540340040c0c0300e13541b0550005920303d000b02c29115001d955400b410381720030309072021800c0400c86207110f503405114100109800d00c0c00e440d40794503041c410001d88012100c041d03c40740e07500f940900d83e88a03502011007140c03182c8005d01c0c0c0d140c149126a22140646000d28170314828110400112203200000b600c007900d4100d103403580803856002c0841340310f505c1070300807507104044544146001c42e111350250009003503060240454610100c401014090355070045003040c10b044c000d0b60b00e4594000100c0b544a5102a009499440c0702101603d10b8003440c0d200c80c40709032618031811000d0029030180e0081c2c900c00e55043c0902c0d103c020511090f10700441c1c0c0784c40309a0047c080020040130316009400101d00113014515060a401c000c0f80c01d40b103088510f40400d03a2a40c000300c0420569440c0d060081c0f01e6040200440b80d1801d030120b003180b0400e1302481c0300d044007417801304540020141200400e000201100c2e0101c045190a040004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 522766870 1250 522765620 522765647
    0x3021612020f1203180f010e0106050f040e0d08061804050106050f0405090d0e060f03090a230c220f0e0615061608040b0703050c01052410120903 64
    0x25490009404102c00a40b400020304002a102d0440d0f0300c1d0301030700c203504402c01d01d5140240305844d00710301800028864072152400d80390000c500c807401c010a0140c3d00f4407620b1054001ca1074411702a091f20404540e640c2c10f049146400720154840c4000514981500c0b005903041040c56401c0c403013003200542c01481103683c181c0710b032150701c0c90f0754040004403801150928042d80241f038807420718034412902d40440d1000141300c542440250f1140081c5900100d0340303a2200d1b0701c680586001d00ca030300c4000d8020041c40b028140c0c000104240855103803661003000c0d900880c245083c0e004500c0c0c4110044810a50030801000600b01000100010300314109600700d0310700a0300d010601d403e0b00c0c43e9181c294198040c0c1903134541001001400310311b4501a00c1921040018800070410380c41c05030080180900070368944d82c9941800c5015400c551014040c8803021860103030b900f0046124610301d101c0b90804840e03c540c43e030b840d618203440c008544080d01c103a0fa072901000034101500302c1c5c401c0803c007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 522768120 1250 522766870 522766873
    0x10806010e04050309010305181b0316031203050c0d050c07060b1005120a0608070e0405060a141315020d0614030303061f030b0a030b01060f0c02010e01030c0302161202 74
    0x1039994014580c0441419140505203410402500d00390394041e82200341c01c11640c1c890a0418100200204e0504070300020b04480102050b03004801031404201e0201c0381c000080b4010f002d1840e60384d4602d620017044568600b40354441c00081c040b051104c05903030b5175651450051000780781c031411101003540005030885036689400751800f02410b111305200d07014555621010700d41440700d84e61000c40540105080951a21110003184003a01801741800a00c102e000c901401d007450724005007070102c000c0565121510700144260400b01840240760040c1003c2c0024050b80307110b0801240060341c03011b0b03100359a800051060004580799010704200d440340b51602d000e41d203111040503281d1006440d4030f580b01c4448400c800c101d54002005224500040c100040c40c0350034000851007054190380107440b0300d2104d100400910350030001586d117406051500c88c034207000c0c1d070b800030304416000b000c1c56040540c4e5000d400006406541110000005903085411040091034210010101c0082ca100103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 522769370 1250 522768120 522768133
    0x310021911031c020412030809060f0609060d02010c0c0b0a0f03090507090b1903080306010e0d0b07180503061504060e0c030c070213090b1501050f030123030709050108 74
    0x3031403054000000c07115000c0055480d205103040703c10118200b40240f9030f8460741c2003100080e8141c0082c80741c072074913200b0f80716500c1c581707040300c07006080000081c142d8010036440300801c883c6940700b0000550018040303171101d0080500b4001201c00c203612400082040c1d499090103d8403914442c01b403c0095140e9650314201c2502c00300440560f030b00c81c68014900d6114850a20141c200d9800c0451101800740400c00c44198251303404200d80000e600948141030000148012942c3c04500072102400940d003071003240749281d8900c0c201481c0141444104204403d85406020300c26908034000c000003004c07200740d400c2158003401c0b02c40045c00f000380300300d16120001640003c007000c1d0a01c10845004030301e082d503a60140d02c3d500c81e84400022030f0701c00c980181624070225140700340f0070f40c24040e450419a501e01a0780c00c0416440d0f11000e1414044180a0034a1012810044a0542d442111100f0f2492102c1407240400c455812445a05000741d1501090fa0740081d44428100c44807001201d15 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 522770620 1250 522769370 522769417
    0x1120b100324060e0603070e0a03150f06060c0201080a06080109080c070603050c0a030b0a030f030c05010f051612060b04032f1e0310020412020307140604150905031002 74
    0x14501c460710510000c510130118088007458810040c5038000c0d5541810a54203076800c00103103007000c054000b100c03486109925088502050701c541214800c113101d0401020f400c2c004064613131100c01034001c3c108803507540086c408010341d0b00310b1002041d080b4000c1c0520481481c0034200b9411000d4000c1c6188115003000030280d12901800d0f00a06000b045245440300c4a44101c01400104480300d800c07403041040000040c3e11461407500301da0080c3d8661040c07074480c1c60440c0c29290004108070b0700f2800e040501c000e642e03941040c0040c4850346d09211003c2094004a4405400c465000c06005c0201040000600510040c0c250803031b20103403070b51b11080025002d450501d00e02444402d8100140b03010148403842461802c0c91812001000c582010711280340c0c00e02070f64803541081f00c850804102500450404200000c0544a4800d500c003898507154007045250040380f1030b400c801102074aa40c82114061200080500b5024082d9120480701680c003001039442403140344803940810142d0f20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 522771870 1250 522770620 522770681
    0x307110402070b01050d0303090c0b07140a0c05010c020f0402070302033103060e100c030219031e0504021f080f0105030f06010308030702030c0a0f0b060a031101120b1003 75
    0x2041c0c2d5610480103038840e42004144000c0c01031110044040c103942d00c4402012801c00c0c00150010072155030719550b66040c3d440e0801c035079922803203a54101d5002c14280340004d001056080c0c1540e40a00c0c20f40b035050b84074000650840c210390402500280700007000340038198080014000000591040d03c10a000030382c001d5642c21000110105c0c58590580a000003503650300300c80c200e10401c3e4115100d900c80740d580c4504440086084401007613000a61299600c1c29078603107106501241020002100f070300035580302c00400d440345c10180503981c1000908548c1c607084041c0112100910040039894580f60250102c0b000369080e40100301210700010701e134640001c81c2e0083d07071006d1000d440b03a41d29642e20003540344c0004d0034040131350005100000f89640e0422032500813600031482e4440300715580c00c6c00c000c1100090901c5000d00b440e64014400304812001d520703040742d400e18040c0f140c05804100c0d000100b504543c1c20f64031a0501c030303500004940c9900162000f0603201c6076011078055048510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 522773120 1250 522771870 522771877
    0x80f01030503090402070c1e0509150306041202011104140301150503031602030f03071506090209013e06040507091b1b08030108060a150b030604051801020c0307110402 74
    0x814961003001000031606103500900b0141d4810914280d90548a000c000058502307125041d000c4040c0c103400300020b24000401c20380018401c8081ca48021000000c41e0700d4090040010b0700e08400288030720000b9100350f01400c01000014406074540d521800c0410245241c96080c038841c0d030030030342c4a910080d241c07a103213022503000600031403074001503240391550510901030076030f4180284c15031100b5031070303041c001403240074442e001c0065402e0b484c99440c4c0c126400c6070041035105105111000060360494800d11350f00200f450f004070001030b01c01040321020001c89942c184840c009049940c17607000041c4007409503108006403880c8035200d050364022502e1014150800001062610b10018003400c82c0a40ca0006280051031f0f12115031509203d6038820782c410109540a401007103030a058030301c66035200c00341880d152098946080e01c101c1c01d50101412407442603607940046985800145025203152111000035501c2d1404143c001da2240c1080c401600d10f03200d0301c61860114980307482103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 522774370 1250 522773120 522773123
    0x7030c020613150605040c050903061006210b040f090201020606030d080a0b360f0405030d0c110129011701061119050a030e1207050108060102160e010501080f0103 72
    0x3881c5807100b00e81c036901d4003500c01054681410760344520126039502c1da4082c04441e42d085403076190761651458203061900800404c080c01000c0c1c03041c800d01030f040e0300c40d0079009070741001c0e00c040f51480c403903040032402005640c101c0340d44076181580c0811040306179002340003a18000d80a840703042d903a61080c15143c1c0005001c880c0020500c0300001c032060701580c401000801c01501800422000050805991075003048036800c0190005213070380078090740c0c0b400a80c4188070031301010180c101513070b40581e02c2c0610034040842ca0344404075425000d104140b041d1690007800002d120000d1200104481c0307000340103100721680d428030524495075006000c0b600c1d1090403107400300386503803901000b06d4011065400c03842841c09003000801d01d5020031601205101c3c0984064945d03d84d00f4680501034501d00401e00740038102c01e1502041d110001f00d1903104441d0300b800c21469641e41e5000403030070318131619460b0000040681011071003c0c4042503107030581c0c80a80b261402619000d4501e08540c2003440b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 522775620 1250 522774370 522774391
    0x6090106080f040204020f0405040f09120518010e2b0b01050303040b0d0504060209060f04050f0904050a06090516031407050315070c030509120a03080a0b0312030603070b040e07030c0206 82
    0x803c005050580c0280b400c804150005030a003503c07080014107494041840c0022030323440d11008000d1181100100c5404192401e001d4a80255030a49010399030b14494000c0c144480d03541d5004d0541c980b416080c04000c02a4060f0759540511003502d99610018402a1400d440303100021416080c0002120140c95240325050309044081d07003000040c1200500403243c2c26002c2c09075050035141c20005d010504c200390241a26141020140444030000407a2244511501414400031070008911080c20f40d8100b100070410300ba0038184140740030780e02a4072014541720300c4000004d0201004030304008109040c140c2c0c1400e07a86a0406a0b600100a446060948a0000302d01201d01402c840f0313244a1080c20414205545140010f81a080070403103504280c010601c08000c26500140003544416490707010003404486c000403e50303401e030034000840a80d0001010500703035901000008000c001440c0615999501ca00304011501c8040d206076012900780001c44240900100d2001d1150581c003c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 522776870 1250 522775620 522775651
    0x2c0f0d0e040225140609060408190e030303070905040b06030108061f0902040e0a05070309050309060901121a030d02030703080a09140105010f0f050a080d050304150606080609010608 80
    0x30401000750b01080c44019414003c0c5031004250070024038250200340144c119640540c450190141080001400d01c00b031030f00800c0c00c000000e442c04c1d0544030302c07900c0c0d040050f480d5640000261054074400e91010340c9840048200704460b50710041480564070242d8041c0504001f51040c00b900780000e02582d0030030b421000020385008584094181c400c2a202140c000080d41d03001058102d90140d00042100c0d00c0c21000c000c2c01e01040d002d201c0e00500545020458900540c072020b44a000d004d040c0b91007804001819202684144050003088181c00070402026075034030a0803810301c420703010f40790083c01062408c21a4a0005c001c4da296960181c4418005658100f48100103125620f02240c2d24841d00c000d900034440c09108641c003800071070034000c0501c4d040502e5109100007552000744210508071040c8000345000c0760b8a00d01e002c80303007131090f201d4644e4500303110200d05801e12500094079008000904079840381d07006015160641d840c1130b035030744c0310a8112149103040307c2c0c4542801208 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 522778120 1250 522776870 522776897
    0x50c0a410106141005030912070b070e010c2301021209030703030606020f06010e07050d09050c15040b0d0203100503100b042702090405070f180b09010e01030f062c0f0d 74
    0x141e000b59401f0000e08240e46080c01012048001904a4101507030f03c00c15000403c403c96802280803c2095400d00b8241d03540d25042d520704080003c00407401d0b10060302c1042c500300744602501030300c0b6070390f000c4000c1c60300c1c6203000c130350a5507a0340042c2003e178002410a007001030494004204d4560561a00c1c015008030780c03c2403049502140301403c0b12b41000020803559850a0a0b44541043d451080c00074004c03046a04080200784804031549000c82074080104000011410040711912603a580015850303a941d80c0248100e580c5a0380040c2d0103001c2e0392801080f030350256000210ba540220340c00c10030080000544500c0c2d000b200c143d8900381600c0005800035250600180c1e07405072080d002c07030301915100e000ba840e004059038000c901103030180148204603241d034000d40324090701c02d44500f100c5600d0a001d000200c00107100c050100c40e0070314030038004e00886400c0300840c1c2008440c0c8070880c4850b452007007a00050300c2c4404a150040681c140444c81012031903000c1d0381680d0752898111090f1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 522779370 1250 522778120 522778127
    0x3010b041208090405180d08010b070b06040b04020415080a05130f1704060914031b130e1207020423061509041b0807050c0a4101061410 60
    0x2145820b4039998001e00410400d03a07524001c04d441030000707084184d84c0d0324007582c201e071404003081c10350400d1101034001480400245e41c161442541c100d4040000b0340c40e000080b80040240711001a00b0030300025001c64111000340c1b05405411031f9507540c1070b071592010185c10450303005680e05c0507054801505840442d0414102c0003015014041380c07a811980c0c8680005240c0c090303808100400c414110400c0680e0001c0c1e41c01d0001c520907005092621501403544070204030075186140328440c1d1035079941e0705d020503a0045007940c0320b5008607520f0188101103614075800c020808c0388128140080d82c1120046c412a485403600e8090b0144032135110002045040c0306420400601e402c0140b100581607581c9001d09280d0803104491604c000d07003611b02c02081000000d14400503c00100035095130700343c2c006403444d2995080750090900d20920f5905400c1111090071090030046800110b0121039007448071a07800cd103100e4002c000c10b0350b0f280b14144500541c1c405407940300002900503404a0700 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 522780620 1250 522779370 522779399
    0x190203060d080304240c1209081b16030c180e0d03180f08070501230606161b240203041202030f0d081515160816030c150203010b04 58
    0xc0750344d05020301c0028020344108042e016140918546d16090701e0303002c1d60740100c00011164030207802401a101207071a000c003035105038044885070170301c0394801404141003802008841c805620045110300e41e40d0030070042000090080005e2000008402080200507100b0b00d182c0c000d503400039180340c0403800401d17030040c041e844000001c1c101480c10400082c1c20400790b0b042192040c016961551001d06201c0e00b10307a200c0d0100c80311420040031f0071400900002440c1e03440541154826950301c8120081c1c94295a0f40030002e1101c6104982e16803142c604450b203c095400251500e5141c0d1054401204400c140d240b1020241e00100410720124046110b000e602a001800322500d442c07424440524200710b03a0804800660b5010a0045041c03042840200c030200403170350450496000028007800744500b41342020203135514190302c820808071405a81c0c95034068054401303018110309002d00038000000c011280003440c41c0448585c0f114604c240c90596001c09010350a2905200048a0410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 522781870 1250 522780620 522780623
    0x20c10120b030c120a1106030f01031202012a172e0b1603030b0901180c110d020708070f06081909020307061e0305010e1f0f0b03190203060d080304 65
    0x142200c894007540310113583c807581c10a840c00a110f07914040c20030411851200d40c00e140b08207020014000180308026800b81529000000008c9010503c0c60682c010800039045030842c00c1402024030350308144814680c04c1d0115030310703802c100b0f0031a0507a600340c20804444030019600450f011403c4284400f84142c1c0800d44c80200295158654070f08052036004182440703503802a240c104020594580274a01003084c00b5544500c10354108080601c50442e070b5508840c02c2030780c0fa1601280070f80300b804422445106801601e20409040170000d4460096004e8500716200b5041d001410f412400c0c903101c111845540d551845448104080c2100e45114118070b00ca251078081c0f22000d6501402200c00a04581c0c803a004010003e2800d81500003443e103028050510308401085084850301015610000c10503c2071103a802070740d01c030213444210745c018119660341c0740d10219550160350003e60140b43c0340719a03014504802442501039200845800c0c5e008540c0486034400900000050368015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 522783120 1250 522781870 522781873
    0xf0712020d0b01030602280e09150910060e0109081c020703140102130503060610050c070b040b0c070f0f06181203171302060717040e16020c10120b03 66
    0x89075640c0700c0c00400c01c002e80058542a43c000703403e500b00c00194500040d40c8480081d441c102e41000d0300b02078142c0105010841c0111805070004000c41c12035800d60b04030a83c001c10b02034481c10080c0a00ba040e12080c01454003154021404020b6036001e003d1000c100c8141c20000c0400103030743c484e60940070354190b11580541c440c10001000181202c0c08480c0d8601d083c0d0f00050311943c40c83c110328080b50450b486940650403501c140111902c0300d900911000c0309a0510b65600c04921003a6071400f2203907403008690020115020409808800041a401d110301d0b0446048584848007080420054420030020101c020410042a40100d103081980030b460f41506002590b0f031901e00050b000d042c6c408400182e10004031504141032203e01a401080e14104d00f03280000b1640483c51a104449014114801c1038941d81c0003001150110b8001e8450032018428900301030b00f4540c118041c60000c80d016000d8410b04c8034150a000448228244142c1d6520015100303040700b480040c0000300c04150907 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 522784370 1250 522783120 522783139
    0xf0307050d0e10051803030c0a0e0a080f0d050304082b0c020102030105130e030a110106090e1f0c020309040b06041a0c010b09042f03071d010b03070918061809030e01020f071202 78
    0x1a0b407032f03a86034170062047e50054407000b45104410350074442d03e031001b030701404014028032000c2a42030058030640e904481c240304e600c0580c801201c000300c550403014240705080c48003540c2c03050740c1900954101c40302500d50f030078003c3c8060120401d8500c40d2070080c5076a4420310010300751520030742d090302c521903d95000180c0203407a58031030350035141500c850220581c0090041d030344d030150109050001c001c1c010300030010001a600c00945070b11942002d03c1c46242c541080071003d503115000c4a0040004c419200d08588000da4200d0300303038100140000080d46003090b50070301401e05c0c842c0c442c4102c1c1c0c020394109840007007000c40001c05c1280c56000016201d070035601d0b502c0307840400c0304034041c0444802d81001031404100074500301805230047c222400c024001c0c0320049800c000039106a9040341c03d604035011820000307030010900340c2c3c801e0404070008031891481141d2540076800361806982c81a000821000040e0ba41c2c0305198410662039008440820020400446101e079840c40103005100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 522785620 1250 522784370 522784397
    0x100c150501030c08100506011b03031b030e1c080103080d1b05090f03013b010614010e010c0b0f09010b090c130e0106050f0307050d0e10051803030c0a 66
    0x440d0401d03002110101480f00062200940400501c04000243c0c002400146000b01c0020441401c0c403d07200000211a016030342058040d0704040740c1c91511a0079491040720808004011381a0000c040405004805042c142c000c1010b16011701c2030b4240c0c4800a6591841da24400c0c40c0d8820f0070802c10469446400034205100c0c950303010342c0105140d403415120103003402080340c8056414040d0b8482d82c9001c1c01d6443d29065030741d084440e140500300c1c05028041412041580ca01d001441403025440c018021409000507903045040f0102031b61081c218030503150040d0350a1001ca07001a0242d100d010004040e03448100ca683d501400c0304002003440391101d00401e90610054521050b2180d0100e4002c030700f2440b00d00c5100c002c0159495101a552410030091300e0703031107000c00765000c80b2000000101ca490003401100c85110140038100802d0aa5450083d1540403038460455802d05180c00301c0d25020195202c025000311803400f80d03285894040302c0c500030394084241c01c3b040c041080d01005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 522786870 1250 522785620 522785663
    0x1a0a03060b0c010506130b03060f040303060509090624011e090506070308040b1006170619031a01080706020718110319110f1b12030711010e0705100c 66
    0x100c00c002c2070380045882d042890400c100f8680340d030f03e084009842c10180942680d00015042d4021020f4440c1158640303c03800c04801900e02504080c2d08454010140701100c00000355552044081003540c4401f03680389148100d400c0700841090b0700150420314402da0003944240b03001d6482c003c2d41881a032495698020894507080342ea0107501164054041005010000501c05d520003400040503010328102100607200d518213108101400380c1400000359103840b808a103810206060605c01312150303072440d10544510b008620b62100c45107807000010002d000046000c03e450194010b0286030341049001c614660b110262810311a0700c810314550745c5242c1400031802103889100d8005260000742000069903403114060001103001c004201d40840c2400c00d480c0344600c400c0c0300a1076820301d0740d0400d182c0001043c1d501a1000e00100b03004074260020801542c040d034440080c4041c032841c540c55a1580494130a484d0020160708890011078400d0002500c801d01c00c424940f844e400d40e04102 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 522788120 1250 522786870 522786877
    0x1c05011503140105010e0c070503160803061c1101180e010305031306090f09020307020a21020d0206040f030324080a110f03070512030702031005011e1a0a03060b 71
    0x100140c050018003030007400303039071040c828140708540c009101951404400c4800c686005200300d6003200c0110b1540b0400c9030600c201c03400d50f00200c168081d000800c4c201220594002d41d5014400c410b40084020140b02c802ca9040850740c011030603016208480c0019143c01100c5103c50761000e45105011440c000c4000100b40a580920010340d1680380485205103110540d030891b5090052004040120740410007002e0181c4150388405600c0b519010b500b45e25101e0180f00003080e202050042c002c0e01c0140c1038000d8504040f550071074141d80c0d4051000e030789820f030035100600b451038030807401d0740441c2c01703500408241401c5034114208400768100182500742e0941050450342c000e42801400e00403c80c0480c2290380044842240300c1d11540b0000750780c0c1c00c0c18483c1d103010349a0115000c0001d1414001e40340f100f0380240607104101c50203440d0700001e18007401245800881030b0a144002103603c10b02c8002d07500130700d0038a01e0b8108111815a001d03080111800e00305a122400070801d5841c66029 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 522789370 1250 522788120 522788141
    0x6050604062105161802130308180907030209130b010c081b0d1e030506010207230a060503060d0303050c09100815060c2109030303010e0403110610051c0501 69
    0x2c0c034415032051500c1e0b81022400c035010404030300004014071802204120b040540200540016500c400c038920030400c0744017650010b03204200200360a4410004205101c0e06001c049840380c04540d1a45001e800324003034100d42c6508010104480243d02d400e540c81540e503d001410900103500c843c2d0b40302161940031000c40c034800042c0070007c00d07420380c2c00c1050420350100383c24480c04842522401c441100c2203108101c04254880c0007290103039000340141c201601d01c42080c00e01040240703600000e0094a60b200038020b07102035000180051182098074080d5100030301c0c3c601c3d141400e440c110003503c0048c005151002e004c000211943e50382c20280c0040c4c0350030b03844a400c0380c640041404c00d01206a16030b540590700401070143c2c00030001c109d408401078100b46c8644101003c1c22040c2d040e000d10406141c05100000000c07451007907240d410ba02c12031080c0d40700d0b00c003640f40b02c01c3c080d200d840c140c1e00307503003400181c2c0c80900151038101800d076030410800c142860f00d0f6a46407281400e40304d51301007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 522790620 1250 522789370 522789419
    0x2030a0203031c060602010939080f06060a03170d021c09060b030d0f1b0503041d0a0603020303030a0c031e051005031b060c03220611010e07030605060406 68
    0x291001c0350060b004d0340c00101104d000810141c3e00340e488061040300f00d8140c1c414008103070039000912800f0110081940181c58003600c810310b4407117442a0b40c1e400f10303407844000d5119140c006501c600c3c0071003131541665800707500b074400c0d04940030110003550002c1d00e50000490b004c0c0301050103001c4480d441a1032800d041c0000c64a0000c600b0600c040342e0a2034a01030003074220b80b620f1030b129a0069495004000f19140c80000b01980d00c222072107581c0d90600080441c0000200080c008d21300d80001d100e00e20802d00308840c5915041020811910244002505600305000042216a1a9001c0340502e2024100419039131030011102420460b45450400c105503100c0c03c0c0300ca0140c00085100282c10143c009140078243c645100c0261380464400a00c200c90001d1559054281030080e988007003c0c0b400c032017880b00c0780304150b00040c0c8030358004c13000020041098052407640500600000c0c0c40540302410300035055407100350141100900703080d0000d0700c40740c0020380030403040005c110711005d014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 522791870 1250 522790620 522790657
    0x100203040c12021509190803250c090504080d09050f1915180f1103010b040204061e050f040b040513050402090c030702071a0c21070f02030a020303 65
    0x19245000c505035030000750b84034224829540042e11250f07842a45564a0000f41e0b440703a0031000003400f0510540c42d10a064142610009140c080c004083c0c0390340c0e440d03c100003d40f40d107084000d50700b07105001400b0f0302840f1b401400f0044600c00e54081a0082d006071011494403005035801c0303041c0d0301c0b040401c69440c3c0c8990314020000f42c0512401100c03c00074030001e075031703600c80d40c90700c2d80c00052440c0c50134051541e4001300316a82030480f4206200b9a1311144110031b5500c50309200c0d0007840711103000d500a50070b00030926007600d024400c41d401e4900741d440f1900c21000f60302141003040c0c0811a15010f0041c2041075542c03140c0100b01510007009004c0e115a0b440d810300080c40140110f102401d0400750402090000507566051040c0d4822081140ca0343c0f2503840302030407442c03c2e020b40e0000d00c4e10321140e410303044030361030100c0202081c50b18842240c010b508100480b41441080310303407170041210140216400180810001c03224035000504642ca80032035034000904543c0484501000d00340a038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 522793120 1250 522791870 522791873
    0x270e0a030206010e0720010e01110a091d07030203060307050a09020403021801081216023d0203041e08010606080601090b13050f120a390308091210020304 68
    0x4002860140c003104c1122502802c0404020300aa0baa0b0303d10000c0031006400c0307100c102842540300a09240141000b800821052003046905a008110781c8000948170000824884691200090162440401c0404a0755085011030087d000a001584d26024038000052140e07119000e440c00340050210043c5d130b80389584100010840d4400200304145643c80041140c0080410b41031481e03542c08003031320f80d5021401c00030540300c0d4142e14001c0d4070a54407880d008180e00030084540104d60145405880d01508000d400071141c80c1c0860000127034010003091003003074290b00711402280324180002461130303250810903080d00e2041d0004000199001d04224040da400b1136414010120404140e04d0002800004508034106004040c003418100407020440d841f40806e9101303200300503040c0d5501e0041d0f4507114240c0d284070800202d4a440306031814007c406060f1010740240c1c80048240d004a25540d00d8203600e8104100d101e82c0001e2015000d41e0325002404081a0507148801c01607491405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 522794370 1250 522793120 522793123
    0x15010c0b0709300f030203040306060816060c0f02100903060911030d090803091011010903020f011d060105090c0f030c03100f06050d09060612080304020a050d02030601270e0a0302 79
    0x10500c1000b07030301e0701d8044a1681c1c0f8184240c1c680f1a103030424510141c000090400740e00e0b6105542c401040103141c4800064030b07220100d0401285010103110054071a510b0b40e080301c03c551603580c083c046080c07140e00503005152150003600c580b1040c2c00c000841130ba594035144100c80b1500780a0300d030140580c141d030401c1c0c64148007a21032882e0b907080c44000f940c10224000c0daa4061201c85900903281c60044282c07c2d4000d90345001c07200c2c0c98000038045c101803494001c0d01c501d031b0010200002e6090000ba1070b94001101c400320a0300d03100400501c6183c2c40c00e41001034603803000c0e189503103803503003000114101403640b13006601c19005817080c0c2c1d0756803c28000610302e68400368440946000301d99402e100f2654444100c43d40c45000e000042195100703820031000030402980b1203102c07802c082800404100c0c841d070245100e580210340c103110f007a59480c02d201d520500203500940c5500420010f00401035140a0422042c034070305041c000c00c0300340d848058115602c401d00c1c0c1070254440810322040550 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 522795620 1250 522794370 522794399
    0xc030a0f0c0503150c09010315060201020c06060f060703140d0615170408180f0310090201080a060303050a05130e190c020708030a0e0d0602030117060a05010302030615010c0b0709 79
    0x1001c3d0000c1c0794160241040300c0c2c0050001d018044403001c009060314441c0e1107600320210058500a0300800203980e05006030007540030702413094241c0a26000504640343ca100c5444415030090840c80c40d10b05165402c440d9180d66684805141c0b00074040159102490321a4102801418100e06041050490080c1c0100c0c80803254404107803500040100180d4600241c942142c00d00610f13816682c202000100c115a0043d1902c0d0144148041e4483d2610305810149441d8000c0c0c950ba51542c940001d5441550110702000c0c011905c00c12146410b0f80c802c1009100c0c0f80c40303c40314034101503281c3c40080e508110540780d100700601c1030880d41088440c14440c2201d035a866000400d040d0307141018454523402840d0b000707001c0c07040101d42d0f03150b1364880140041c04240d124074210355035030f11440807a0885540d400410301501c603690000d012040300d0301c1200d0603a0f400500606041d552003280c04680346519170a43d0401c4052107000700020309003003026000c0c1c201a26103100321401d1a541c1300c040740 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 522796870 1250 522795620 522795629
    0x6120b1b0c07170321190605030a030f1205150f0f09011802040905010803131706150f030303090c030d0c03090312030605031b010f05091806030c030a0f0c 68
    0x30018141c4a1400040540807180310500c40c020b0014104066401e6008100002c00c40c200e40701c0c070f544001000441180d01c5424138407410b0b080145c009803004107c2c1e00c18080d02c3d4155205615a1001c2409014900740a000c1c516010290802c41100d04003990f40a07549100b004a00b0150070032189084498000b20b400c3c10343c4d40c0042d00305014000382d01540103128400207003011707581290740c580050701100c015148108003401203594590b0229940c2d071000c0241d4034110306681000c0b90904150f20800032000b54900142481e031111180c40314552496110664485105d0b02c0c3e508d01c680741030001d10321174046d000c050702a0b1110742d0b052609150f80c850507181003044c0125008006034004501c10292a045800c8407c0c83c3e141c410150020b2015804c185d50500c50081c1a100049240c12080324902e020399031200ea070b50314050107807418054008040e40c8080300090030200044a80741041c0d20803002011159140c204c0004a0b051100f100c80540b1301014096a030340034480c500c04a00000c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 522798120 1250 522796870 522796921
    0xc031104090f0201031109060a02151303120f0f050103060212090309011d030f060103140d080606030a0b04110307050403061406150703180e0109050609240406120b 72
    0x1051180e40c0d407152128442ea0080c1856a60380c100c01d003100007041606c41f91000a000c1c26610303000588040e50301d10008842a014800780700c001074185002c210701741c4100f0f61545070505071b0721490201401401c640326241203150341d10507624240b10070381c3c040c90307000f0350090000507920075011425502049000381110080c1d8000c00054072580d83c00340780c3d204020010441d0b51000b80316540042d007403070121f40032000a44035800012040c0006140c2e02c00084003c94100c0d892076402503c2540d030001d0480e60141c6c4800103000291a4504640111850310002080020f0005c41210040348541051301d103c000128085402c0c01004014800c0c00402010a01c2002061402600054206088001004071310348003241c14002c040c06025800c400040304408100d01030348a265840115900344600d5108606042c08074445040c64404d41d40518040524041044200059240c501100c454081c1e04191307240000a2512502090f44440910441c9010880e0034060507158442800c10b15180e03030b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 522799370 1250 522798120 522798131
    0x1703070e04090804062f030a17070819020d1518020909130c0b0406030203060f0121020310180218011403190f0c0903030206011e031b0b070c031104 65
    0x30404210031390701110540e160401241c81a6002c0790740c58034964500f0301200080c038040f0748203250080060002403000b9a0344203011103213510300603a003103800c0d10100c002c22044030215a102c10343c5500c41d50301c0004011302619128401d2059022a20040314034440c17030042080620614816074035405184401680a60908079480300084100034080c25144003143c1e180042820004840c0207a00105020003000b5215540c3d204041c01039030044500c030380314251400080c1120341c050403254400014130140b0150074040e5140280081d48042c05903040100481000101c58135001c043d2191075081d45809601c442c92201744440c01c42001a03038a044c440e0090842c1c070151048000c0e20740c48400094084200000241035600410354030103900007060a10000841d590b82000c80e090440e0f04c0381d1300301c5240781e90310304080c010500411507034840c44a1a48080001c18032603400842c181c010703803101c507404640d14a41c810340d40d40200412070700784040032070804c1800f001c20f1840d4603942c41644e09021 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 522800620 1250 522799370 522799373
    0x1104330e07030903140a02120403080913021204060f061e03060c0509091303170f1906081009051603230706170901060509190b0d08030615071703070e0409 68
    0x18012494100b25200321012800d0746c0014801c020b005e45901c0e001d4400c503622500c0707007000b01c000d87c0100202d80c01480105a110310055641c030031500c140420500444840c0c03115070761a0054900050110311881d160080491028140350558148100340d11010b0401451031408c0f00907217090300844810b21005000c002040d841c0c030301d10a41d00003002c5054141441140ca4242d6600440700a065640c0c5100f004000c000e19541c030503580152080f0042c052030098845051060300c280d40925100340d0803c07540014421066049107460078400c00544852414408a400e1810300310742c82502c5001003600c04c006042c440f190040d0b4100c00c00d8000c1c0c550107081c880c02600704c884071802e00030307407003454000a03995201c00e40c030280c05010000d180000038284250030360044409010b83d41500d518110050740315142150402e010540d01440c52030443c0d07a4001004400910701400c4419140c0400c04c0324006410441c1c49100040b811013807a45904120030003c0c40c031284a82c0180c0130b80d1400e0400c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 522801870 1250 522800620 522800627
    0xc030c030a020918010609051f1802070c0909060912030e0601030803040302010f0507051c0213170a0b1e07020604030804060510050a15030c05071104330e07030903 72
    0x1001c55015100424980c84103544501142840300c00d144107540b81010100e8041c6880e044640500208072403d11002040401c40e42d1580481c4070341d20074180f80c2d02c10000903002c40d40142880301d01808040c84555134a0116806a4140000c1107450f16135070203003a0b0802280742500041c10a4914040000c511006001655000180070260121001000040415200f500030407112145a503043c005401d00c004050050b0f00704800078015089200c003401004181c9100342e42030658004101d503603281c500340c0f106446000100c0329500314042d07403e21102082440318910b008140e07100801041c5000b5198002200c1000b420f8007046400c10001d100c00701e03a020306001e8105030807010004558036170b5511480d281c40d10b980800e03000f82454400140102c801103d165003c00142c5080c42200703400c0c4403c94a92181e441c000348860300d0f0345400c02c443d0500390300c0f00d244400c19205407950240070600341002d020305564178090b0001041c03c20700481c03a1587e1610b030014400d0905000d1503070700d541c024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 522803120 1250 522801870 522801883
    0xe0c0703021504021f080a060b090609060d022502031e0a030806030c1306500d0503030402100302180906030c0405010b0d111e130e010807080c030c03 66
    0x204200e0b40316000714081d0743e500041200c0c0b90700c0c3e40400300d030492003802014045030720454038420400c0c83c02c2d20009001c214501190340075103004180d107142c0300c0040c0401440340c20904051802603400c2c007500e00104104100e03084c0810004030040181d103024410035103800078141d6940c181149840c2c0e43c85400000281c030040c0c04c0c2d45802c00d1091541c0e0341020074640310320040115442a1410b0109d0740950490313000d04155040c1201500060342e0260070b103000380d8920358101141c00802600c01012540c07000c101da00b0401461640070301407003880c0c00680f1075031101400380c031039803c00001d10045103044050f607508641039003020350404002c204415500122914104e014440d40740000e10141c5e81403203000010700000b00208140d58580c414500142c01001307481c0015440e003842030030582c43c290140d55490041030000340000001c9090542c15402021548581d2040442d011503a11410040c03140605441e80c000e0800500d05194146400c0f861003c1da4001d4205281400c0c072620b020aa0f03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 522804370 1250 522803120 522803143
    0x5090105011211041403150412050706020903070f150201060509060f030a050118030f18090b010c0611030604060e06060307030b0105072906100f0305090106080f070e0c070302 77
    0x200c584400b0a100d4640a8050041d144405003400140482c0b0191104186040720800b94129040c4507650740c0f0608070001c0944000d806d403000e4104107864a440354005040303103445000d016040184c010046490540e25802a50014a8200c002e02003520480c1601e110342ca102d00c000c0c41454030300f4010503914000038000902239451082c030800c55031001c000c1c1c0d40145034810000c10450716126040b0b441c0440d41d0004038001050410860070291080c04a1281254613000100740d040c0b504580b0030050100e80314490512050324904408503406115058205107441c201c540d2300d24084c4104400c40e201c40d040717407031a00e940c101404056121002960360111340e504002800140710030060f00d0b01d0003544001003020a6025148800c5032000311200d290000c0380ea1182c066456840400c106040034218000000f0007000c2c855600c14480c9c0c0000d40c20400344000001e40c1034981d51014100fa8002d051280f0720761007440108405444000c01a51004100003034604002e0030340d500940f101e281500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 522805620 1250 522804370 522804377
    0x300c081b16020a031545050609250315020a0320040e07030207031b03120f150b0c070308030703230603010c0206010f03081605010606020708160509010501 68
    0x4a0344118200040034888040e001001d0121040ea07a140803901100b4840b00341c034031700782800c0c8203041e80d18445940c07403c00482406066202c8044c2e0030510203421ba41c100712845110300100b84000700d0310501c00540a0280e1001510710b0000c4c40109100720415041c0703e00002e0029181000032035103a14050045503071020001d0f983e060541c504601a042d440007038580d8130220a03000a0040c4914000d00031181042500021641d4a0300160f0480c0140c01001d00412040600360308500d0988a0144400388281080d4000403060b440c1e61040301d04a400c460a9a580d030b4201c5a40200c000304118001c10151017018078254001c00c0b4503848100d2440b005190700c00100100c2d000602942051901c0c0b07000006401c082800540210719202003501d00c18001e510303008074102000d102080310380c1030302d100211030203000c0e01e59900d4100c40d40c452070398a910300b007840040e0000504d00303020350b80003480541c1c020040982007070700540c00e0210046080500c0318034100204429241e489409044940908 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 522806870 1250 522805620 522805627
    0x3060509070215090c030d09080601060201141303140a0c0201021e0307030518060708041d010311100c0605070806090f04030e0f030a061401060e0402130510300c081b 73
    0xc1d42c5005c002c01d00d05c60b85402022103a40c3c502d03030b0010852044404800840c0e00030b0342d880105130b003212010700072569203900d19000101c08820051300381e00d030f543c400d2030208407032084c8a91441107500010b0000d00040c1c0000d0f2040255070b41003050224190740141c5900ca812880385400d0343c1c074400c081e0028180400800c0f40c00800301a58460340007008040c110540d01c0c40c252821400c564402c0c0900200c2564148903554800c03000c2030800e0580c0c1d40290440d5501e501c2800304103164001170500781c10006101054030020700b19015a0f07002d003070b4a4580485a08102040010f00351006008440d510341150801c80441c1d44005225040d04c403d81d56000b8a4110401003400c00b0840d1001130304890416601d10a51002c400c0e10504850700c80d51007904181d40001000280c1c4943e03440e6103c0080b10100900032443e04010340380603045141444c03444256840e0040803441c44070080448180c0c800c402c1c0400303d0a050084541c566100e01d4203803070a1400034078240c3e500400202d1465020b4010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 522808120 1250 522806870 522806881
    0x1a12070c050712030f0305091e03070c030b061014090d03092c01061803080f0903100501080d030903200f01021b010b0103111806090607110103060509070215 69
    0x1600c0320303400c198221080d10301c020740ba034a50304000300c0350090842c0051019203a01c0e070158070030b100d401d000321070507405040403104041004854005508460004d80000c004250000e038030f000c0307298001c51054040c402645403010401c918114a66005824419a11005912011f440b0115140c42c00d080780c5040800714641400c540004003a0414200c1454241201940581005101c0031a2104649028103603803a0401100ca83c000200410b40030403401c00180009100f20002e801d80e1854014440d0030302c3c4005001910b070070ba481c598168107503910310041c82803940070f00c00381001d030000f8103050141a5159500400e40421034070714056801c04090b0780c4440400501020044004180c02552030740a5100001400403000e10400d44546c42c01203042465400f0740104812141000083c1341007007513002c0d03607808a40312a03245a6008104000d502c41c0b40c1d0300c030700140541c98010b58a07008051a45000541100e4180c0c10480c0306600d00002c011000b03a0000d9007140361624040c030a42d04e40ca0300c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 522809370 1250 522808120 522808127
    0x6110c030106181a12010203090d0e01020304090203091c0f0f0c0b220c0f05010e041a15090406090203040b060a0b0f0a05040302030d05032e060f0e0411131a1207 71
    0x1440d104d55002e1841410740c0c0c0c190105401650280d03010740c0c140c0700c091090310000d0390100c0c042c144050250b042072000300038030728090303001d540d03c040042e00f600e2041d1090b0001e696041781041d210404203900c2c490070140c4540c02092082050020b003800c0d43e0b88000b944030384061030401001c00140001000b5000c1c8500100060050f10980c001031a91410781c65007080f424803100c0e4010103000950307201461401d450f06000d801e00394038020482c2c502100c0607006200c800e80b280c0d6614144070400300b101d00865100c0344100002005140001601d0b410f242c542504035000240031948101914481441701d05e00f40000c0340c00000c40b0b411101c0c0e172028410303011f40303803030240d540065454000d15035a201000d401100940c0b15081d102e683d50750362290311801c075803400405010907290750171074032062002a00070f4503151442281030510301a1000c3c100009016140b202c02e00d1258030b000400c16031820195803120801a0041130002c022250360001e1440c0e040c0500043d0b109414980d00204003041d00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 522810620 1250 522809370 522809411
    0x406090f030c033207090b010206061003110f0c01050f07170c13030501150311060301120213021c06031704031a060415061119080d050c040b0406110c03010618 70
    0x2009509100c0c0702d200030b46101e0b1903007014442c600186d1708092a031040c6601c0414154481d0000130104240c002d0b00d000200c004100c41c202107901d45008201808010000c80c007c0c140802240d80080b4003441c2c110b0400905180207403c0c40f003800b401d54507901110b4031704030b02150300001d0406090f4545403018071226481ca003552003d00b8a518140a50503003040c0080c0c40c00c01d40e03003d8500076505046c104103009042c03009103e400159840e40c1d2000006180132101241d2445c450030b0050f04002d030913120015002e034480440c490303c41c0e03220020420003135000d202d288404040101c42e41030a165442c0c1c60003071060142c03108144041c003400241c0507501d81c1d02c1500c503c8110a01c2d005071544854010f441c540c2074a546580c3c510400b080007912808003000100d040390302c08007590811a08a078560050040948525040b0380c0510021404040c01800b40006005942c0c03106e40720a00c01821904248441042501070b0f4102801800110121690081641f101d2180000c0303444d44500d600b02c010382c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 522811870 1250 522810620 522810683
    0x611031803010609090501050402090c0f0316051c0b0a060f05040911070807030c030801090207020d030c0606090513140105011203122004090515010807180305030a03020406090f030c03 81
    0x900d800c40d41e01c140501544594272451090f5031007046601d40100310f00140c010410a00e0581a04200050360003400c0900d994516540f0b0a0076030410408540302100234060b440307000141030380c0b0409108030f480c0082d12000108142e04000c0c1c0704d4030303840500405a22030b901070b690025440b28030180880301240b0440d4185034010b080a5102c00c61854010303c80c9034964000d0700020700000011400c2040c0b88201c85d000703070707000305107150103000e6a400b03446030b03140c1190540e03c240d554040041e20071039a02030702d8030416071804940f0021600d85801c10841c0103103049115260b2400d40148010079220f03c0c41d0882c01d0301424403101002d1510300c10701c098920001d4014018031182d2001d1030002c0550064015128150802d0086560700c01c0b50314261901d00000d0360002c1d070030802181800e400b07244818040d0300041d82c500c1502c0e40740c1d21050700d550711000c034180000741c2c000b40070820a54805600c0c1e010b09920011180e4452644c0c403108481001c80c003001c2d2403001008500c91001c00120005070904 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 522813120 1250 522811870 522811889
    0x30b0a0314030310232206030302060601110a021c0203070b1801031b1d0d05010504050a020910080c01050d0204091d2e05040204020909091606110318030106 69
    0xc209081800782c5030780040e00d070b42698042600000c1041d0144e601d03020900503c02d040a28200c80c0c24041211041d1446129041c1008200319012100e101d030003100080c41c0031341c0041c01c6a0030090001041c3c00001103e424050f04192219001a55004005106103021a285800d07409150000034240b80c0c00360f00c04441944001a003501c40c0e2200004101808800d80701042202da0301218040c80d9030308102403500083d0b2a420b03091040c00642000340a1460242103040c0380149980d03910308641042e40d0903a425848412050110f142c01805258000c1c1152248413000e450001407907030f100344441c5100e05002012032030801040f52507041c1c0c2c00601c007840b018030030042c2d602107442c10380342b03910000d818502544074820058144911003404860b50766100c0c0c002840008204001014054400c0382d1254007041200401d640e403404403405159804040c1c140350a080c114072018a10b01d40c400401d102d98450489010840802a00c60429018101d0041c416030880041d0042000fa000003c24 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 522814370 1250 522813120 522813143
    0xf05091306110307031a06040b1603030e0d02010207060e03040501020d05090303070f0f050f1b040207080409060b03100f05100c030e0307080a030e09092e1e2a030b0a03 74
    0x1185d0603002000000fa46040e22500d508a0500f4010144140c1c015040580020048100e0071440004180711043c020700d0b0000d40e01420480380380c10020074180042c0180c1d00800c1500c1408000c0c0b14400b0ba0144143c0210700c0c0c54a803500103510b178000030450505005002c507001c0b0203602c0600c115401f503948858070368003000403403410900801003000d0699141c41061b00440e5116000102c0143e406074443c2c8404102030701000308400703544009022108000c050000280c1210240100006024091029500c034584038000340342444003544030b20003141c03840000704419190f075114860b0000721480c0080780c0800c1e6040603a8020321149101c0e406200c1c01a00250b0424041031130302c246840b0b523a610a40c40c442c4030400082417000e0380c09068a03041460660b5480c04507840c050382220310b10005442154564400034219800c040040185407415070000030522103e106030814440c0c61055020303001c80070720050401d00c803030744051010f060f901c034001c031190f03910304d400c0200071755000009008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 522815620 1250 522814370 522814381
    0x80a03030c02010e071a07060912030b0310020906030c160b040311100b0a0e07120203070c030e1c0b0a060e0c07030314040503220305150702070f050913061103 70
    0x301080455007005520f0304504501105011606400726022403c0143d1064640341c07048595520101c0d04461444d610021000040c88100c0241e284880c2a14000398080d40700c03050608201e501000ca143c024410801d042540e1748035016690441d14049025403074071070340c030302d090384007202d41da0042c2c6001c2c003003003c0008150340007031101080f0090b403050f00c1101106001890645110101683d13000030024002e000e400e08180405034400024500820040c81c1c495200003280c0c0f00382e55070303c00264180807000c10f2541041d80d0001300e40c02903c0702e00700111008043c0f440203140840013400686c0000c00b05c3d15443c041d8000101078414000d03a0300703041c2490311100d100c0b544088400c50200703040080f81c4184802090b02c041c401c1f50880013551411180203400c905200030401e1030210182c0d81007010000c20400c1124103400c0a41a04200107400d2404000c0c0c40c005031039101c07510f201420390007404940c46082c0046d410401070b1382c03101208003861405001a00c001e00c0f90000c908400301c100309 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 522816870 1250 522815620 522815627
    0x20d091506050a120b060d0204060f12020a0605040e07030902120d0c02041107152406030203090f0f030904022a031b06060f0910050306010914151f0504080a03 70
    0x700b1035808494076a03c05070340d407400c050f05038002c0320040c200d031324448000307580b500701031010444040c401040000c2c01c07511191001041040b50700001d00c0c000e001e0000f201142451540030026040c81c3c101141058500700901300205001000c003410181c1314000001192290568800f030741d05604180c03140d9542851009210040c6401e09910441c103010320650115142c004441b0070704d401c080442602c01424080c0c40282203481e003040200c6000780000d210680c120740174240980303801e07540035980381003101180c0d1a00102800540054100c03071400940700744000226410301500340d40c050303290300b0b082e20141a1030041140c240300c1404d8000040c000c5c040048012702c0e1440e0f001c5071960001070100a80c0781d43d5201240c090360414540c0b005140249402030055030b00c06030b105000110300742c444001c40d0402d04280e00c10900940c48404540b902c01c180b142c07043d403002c031080c00c030314007145d1000c005803059488101c900d507012243d50716141002d20810803a000b80100c1c0c000c4030f03d40000d614009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 522818120 1250 522816870 522816881
    0xd03120507051804020c030421060f0f290d050f0601091d03040b030a09080c0a0b010f21110d05121201210b071107030f052509020d0915 60
    0x1500c003c03000c18050301443c09200b81c5040c010643d0096003000d08240000c003d0b48981105001207860701c2c0034041c00602c050041400b802901c0802082c0b00400380184000e65050f000445841140e6201c80c000486220f1482050804e0844d10300300c249900e800c0c518100900c5940f40c8985005900c000300780c0d07500a80100000c1a050306c2170f0410304505500b0320392280658010301c910b42d2000c20110b0101243c0d60009070515004184103460700950b200101e242c0044c080084030303880590b82c010023900c040e0141c01002405c19040d581140c01c0140d0350f0b840100c2080d00000d04c0003541d40d031600b09175100d044c1d441d410720340c0c0841102c0700c4104081103038445402410100f2440c15510f000820011504005690060445003c0c0d0350b4610550740c0d82e088031a4018031400410102c0042d8030b021240c20844a8010b501400c00c00d8036040c042c1c280581004038200d00d500c6041c1e4485518042000c041c0e00a004940110b440140c40306030595212700030340140b5801806503250700308481307600100782c0d000c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 522819370 1250 522818120 522818137
    0x3020d29030715050403060b040e030706062103021f1112040c12084003020a0801020c19150606080601020d0f1b0f02061603080f150d0312050705 64
    0x21600d0003070380c070b044030341481c8040480800004c20500003080000c07400d1304980c6604500400c041480c02000c0300c003620b16003040d00c080e01c20544900b403c000ca000c0004040c1204401c00d0780480c40c00c0c8035038802035500c0b52113070311180446000507010609040d0907444540c8256140002a984804d801c40680c1d443c00203075810f44c2c6900c0505000900c0c0c00940440b1030007198407078103440c00c040c40b21404403006844110300c640200b420080c0c00c0e501d8402000340300c100094074840c00045a042d4010312281c0b40c001d8100114580c410821080c40d2000004c1c00c41c030b51071035610384400b80003661078240f4000344c41020480320a8102000070800c160000100342c804e000030307401c56141790340e0100103c9a40ca05401000e000c46d0b014200e032001c000b0016a401c1075180280801d040400d22035001ca00305074050403203100c1030100780181c41d0030035900082913034224012031544003650406405607000c0b030694281c0703144a40410842074003050f0082445100c0403022080403c0545810764001d0900e0b800f5911 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 522820620 1250 522819370 522819373
    0x4150501050f120f070e0a051507050f030406020d020105090109020a032d060b010201141014220507020d030b1c1b170c030106150807020f060406021213021003020d2903 74
    0x80746c03074942040c816a0080310401010801170403200801e40e00554080b0406070b921b4000d000c546e404020f000c000510007031102354014100010907040082c210b840181041400340d04100380300d4056030b20ba41400003502d401804038494103802290318040351101c0c00617051080103000c41e11013805116800104c0030366007138000f0300080400300540c202c00e002c1101e00481940034041f007400340b1b148100140e6480724019000c00c00c068079013100e00e0340d0701030b0004080ac3e01a032940304100810b9418051243d268106003001d00c0880030140c0010321484510001c07200810020340c506040c015601c2c09451400172400452440a488058060101f41d4042d140200e51240344500d41c094101481104201c9580b041ca050040c26404811601440003030503034021072051200380340203a5030600026001e90f100c0c220060ba90b420390700314445614001800400340586640044002d62510032100c01900b000745801a6526203075604400140001a031544d200d01100b51150910500784003200020b0340201c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 522821870 1250 522820620 522820637
    0xa0504030f1112191520030106030605030303090319050405040f050108011a03300a03150501170a0b04061d150402070218070201091709010e04150501050f120f07 71
    0x208031a075900307003001800c104d075006100050204520795040c40800f904c1e08404510384107a071302d01c801c2003500d003198164411000001000f08641501c0f40400620b000d0300a1800c0d8680a0911500d030f00414210103100541c621410b144544100200c0d030142400034010002071201c1164240189000d005070310031580382c16403401810000207002c1c0c980c2c00d001401450480000e030358103a04401c86003000c80e014010b00d070f441001a24070b5070240c8803412013903800080300e44a1040103d1b111207240d0180341403001940c810044c000511220f65407200c0c803444c000c1441d840510109000f040b440d84191580720742240341c820880007120206000d960500f4100b80380403215010002244150340000750300414100280c980d030171b001d001031030740b16a4234000018468580d0700c5505103a141101b400c11202c00000b056100c641e00a1000d121200782503804100344604006001e840280ba03005031350610801041210516141c0000c880420340800c840b0803560801206000180500f07441c004003060486 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 522823120 1250 522821870 522821899
    0x120b0604060b0702210d080f010b0306090c0a0207050618011d060a1b0506180609070305060606070c03020414010303120507020607050a030e070b0c010e0106050f01050a0504030f11 79
    0x14010303a415128600b04152502c00c01d0703800c20946402d90090901c450400d0f5000201c1da410500600c0000552620303002400e00e440150b034a0f1980058003d01000030b420700620070b10761114020a9400103082d00241e60302c01750004164581140e50b480f95070320540020314442c560101890182d1380100030303258034509100140301d03211280c040c031340e005800140500c14000144d204816100c01c01c480224811101c000a44480381820f40485083d0005602d00107622002c00c410021168440c9010003e440e4550440d0303142c0341c03504070141149205000c00308450080c0001c02c140e41c4001c540c001c004000d40e84038114012075002e001d01c010381c04128280c5958400e448240103161040f80f03640e002e841d00b550f4008003500c164020000302c0d0100f594034408042056002c0000700041d000d002d8865840d500c00020540c25208240707418051a41410001c0100ea00d40340c001342003030340302401c02c9501c40c0380b40c60741154117025030381c07024201091032881c030814000b902d155100340c4030b025940c0e1180210203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 522824370 1250 522823120 522823129
    0x6050c1509030a0507020a120503180607030c170d02040e0105120d170a020c030c10050916050d02030307170703140405010f11010204091416021f0e0102040b04120b06 73
    0x807650380380d968000b002400302c2a4800c10060580c00c0c80106103480c031580385d41050400c1910303100115519030002404490324540030b903003000040303c111040d1703142c11100d5400070142c40c9601c5009141c03254429810411410b01004d88800d019544811501e4907944c0c1e080100c00d036030070300c03541c1d00505129414656441000c1002d1004a6043d210461000d40c130184441100a000b4071074035040d9828040100c850005100070401004000003c10580004284041c100c800c040c04400b1203a001e0a00c404d500c0d56200c80d40d0040390000c540c40c034528070b03c50012900318810220010000546d00e504100c03041456005040c54601176698041e04414138a10581c3c1407245000d800d0100e0a0b12141d440918845d40f5949148140c40c0009402c066440040c001500c610b06104d0040c107017003000704005004480c854a441d6692407000305001090032004c41c551a020120ba001007175290010445025002d4040b940180515003565582c4c6d5a1000f41c016003805c0d51400b250044010000300302ca40c0361 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 522825620 1250 522824370 522824413
    0x140a03030f0f02010b0616120905030c010c060b1c0b100f0905060409120203090103110301030803014a150102121b0d090509280902010e0a06050c 64
    0x1815110402001c038052401c1c0c45201081103920219905c0e81e03c2c0401d9a12960f019200400000d00300821711074180c0f0300206508006001c0c4020002641341c1003040e6030f400108440d240b002824a140188184c1c1001409482081c071540e030001a442259980030f1801000e1600039402080c14481584424008409200341d0b2700c5208071040c0b03451404e01000c3c080d03600180d040940103000040280079541c688800b6107800c810400503130404500c5020658041c051621401d0300c0c445014030f9581195194100d0303000c1801101132245201c0c0c00d00d2045452902c0c01ca88003210403018103508100031860f0144010718402180c030580180000c1001ea0800d5407481c590480141c003d030850220230766014005800c116801c1d01c201480c1c131090b080503071f01408003100c82c4405956a1442c641031806001c1841005007400009800c29000341d0ba400d0f221405500310318144050210726a0701500049501c038120301c0d4401e034810050300000880503084001030103446143d07402d03070740c85200d20b2100054160 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 522826870 1250 522825620 522825623
    0x50c011103070b0103030f180806060f0a08070306051306020d090210030e0a030516080c07060f021203011214030315040b040605030a060213150201060302010e101b050705100207140a03 81
    0x25000f07001800040d010310180c1c030242c82945880b2144510455003003031860b1142d40301484940005080c0806410100d844c040d401c00156020540545413000c81c560b915071078400600860390320004240e0000340b0b400941c0302c7e41e4200c102507446080c0c551048004001d0080b0481c841d420240c944008103020780101c104042065000e440c216106d0780303007510300340d03c8012100421601014040f000030306c0c51016060100340c030310040035640d0070f0890180010b02d01e03c4c00c0da030039940240740324003c2d20381c3c00044a054501100f52081d4071130451805814072401c0000f0301c1d05a0001008001d15007681c0200c00800c0d0a0440b000c0c0252042a014070044901c2c03400b4654041d0000619500400c2e40340d0028001d920144203c5200141e907002c901c0501c2100548560041c2d4441c00d080081d50b03031110070031002c40400c54401c2c00c10724a280020308109181e8240142d007400c44103900341030040031300105001f8071000e0b00700400900160002034496516000d80c841c07080001ca1703c1040c904155074240300f907a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 522828120 1250 522826870 522826883
    0x10e0705090f15011107060c23100209040609060e061e0a060c11030a030503100e06012012220806041205130f06030614010c23030702060403050c01110307 68
    0xa8586050b80d03c020b11101000c0c0741400016050f803000c100081240c40024111951285c44240071450062480070490350740c1c20741c1a6149410990007400400d4038070079200000307801a503540d40a0085800350a155000a41030fa29003200024141400c1c662039101c0c440440d080c5002008800c1101c108200c4450003581020b5a00c1c0c0034040750340034140b83d000ba24014840101c0300450080024a80040030800704c0020380f0200510120515a42c0b40002070215038202036024548600002e0000050611001d00504000ea80914070b08051007010034281c0a061120350b2420b50700c0003a6403011001142c14504080c140d00001c403030b400442c540e40910343c0580400b071210341c1018211915041000e0484041c098403100044074440300340c29034018040e0b51070228031b1915150540f031100030343d2013400303050024689420000602e40c40d074080b40fa44100c0d03070a0a10064110800c2d2841c010715000a400a00005010040c81310000e0601b0420780240e9032015298011113030a6100c1c000c030070006104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 522829370 1250 522828120 522828151
    0x2060604020a03060b07110112180201140d0e0304061803050c0607141c0807020a020123040b2106030a0c0e040809040216060b030c03032706070302010e070509 70
    0x1403505030000e08041003a4500458220b44600c4001d80562040100300c8582c8840c03046010b00e5604400000c25002c0c030301000700606a00080883d64644003204000d04206042c0384080e0859401c10940c1e24601c030440d010006000c514038038075500d0b406805000b0201c2d0310101c140009865120400054030703442005042900070300001d000c0203412010048450080d45007000f41110340411000440c4041e1405100c030110800c0c20140003a03001405010864101d1110440540d0304040c00b8492922072540c5010340780d0712055008074501498000e580b0110700040c40d89c410000569480b03244040321101c0b0002500d03580c0c109030f42d0724940f5000030014060030100700015504c1c01d24043e4401c1c0140c0b400e41c6465046d00c0010201d0740b21201408450348408030082c00c0c00414032a00103a882d05800030207c0c1e402d10700010740d0700d025030102880c424981342e007000400d0505016406050501603c11a111101468068081d0842d020446038512910130006164034100030054000c0740350340c0c45a00c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 522830620 1250 522829370 522829381
    0x60604080c19170304090b0a0506090f19030524102309191a0f060306040e0601030b0906090601060512040201021e01140105060a0801051c05030d0b040c02010c0206 72
    0x400d80b402c2590b08a041c0c9107000001059092007011505481c01d072000303140e49a051114081c01c407450010001d0150481034428420703a1501c0c030840b070001500312141da0520121400103080d082d44110724480d00440442c00108200b40095466505600b030321500c0b099031003142c181d191801048618054070341c0d45e00020801030708281e1802c24070341c0c0030a882c41003050100020038005036094071044122044806c150008418074400d504132081c0032001050f8420322032000612403100600011700c20440000412003556942d40001c4940d40800c05441d56503071b480c1000b244200d01118020154040c0c2e0b000101c04d903c000c10064181c0d034140c0c4400b401c040300e05a104401c0340004008905500c0349080040f4144132188244101c0d078003c0c0c0002c540700181440c0201140010313070100d4050142031000c9441c0d6600501c40c94155403040d42c8407907004030340e680e020a641c80700e940058081d00001818042d151105d130880d5612080980302844080d60000c0100c0c00c98200050200042e0000c902281 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 522831870 1250 522830620 522830629
    0xa020a050f240a02040f120203010b030f120c01090b13120320220305011b0207030209010e1e0408070b090c1806030a050304090209091b0a050a170403080f060604080c 73
    0x80e0080c03c841401410251500311842c00c0b42405d820891401e00091141011071400740600c5400f41010f4014000300c1d240e1400360340e0b46100346040d01000e40b001107102e0100000961000401a1700030505d01e5490a081d0004140251a030009440036101460100a081d00a000e985140395400682e80705e4449980e0b540c00307040c0c0000a20b56410801c0325082c80c6040c14604560700554000c0000090300c1441c11299000305885501040654016a00400c0940d545c810712504460351501f5481c042d541c0c500d82c00c004924240e0806070200010800d000070f02400c04050070701e051161820b11801d40f01d0388007a03940c0d00c2c00750a000d076000010f2081000c0c082c03401d00700c050b0417080217011a8014003881e40d41c242142c005401100a04d03130b011454a2162604101d03850304440410042d001c40f042c0f094241c2d80500c520116103041c010001380082c0b20b24440e000d142c101c0120510010081d0400e4130f0f00404200301943d400841310b6400740468010314010782114110b4151030024203101382d1000520 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 522833120 1250 522831870 522831943
    0x1311090717101e090f06290f210c0c0c040911130906050c0702030307060902030a29011a0904090507050411030a06060c0c090b040f020a020a050f 64
    0x5420714045a00000c3c012a003200880401440c1d440403070301d0340c0c1010845001c46400d5080641d03034038100881004080c0c003090000f0900c2c2c0220550050310100e41300703010500d20a420341c4554200c000140940541c21f03054032804035042a0000c5520b85e180c400300c034201e42c05404e5811580fa003240169040078a4035510040700980b04500c6103510341242000a5030f03d000d402d5807412116214044402000030900c1510380c4103031100b90303040c20100f664021030740c2e078018500002c5c03190b80c3c0d07030325424199070b070802004503c0c0703900400e602680e404014107540c1c081600e806500d0303000302540001c00c181001c051070300902155403084904104050702000040d185220042d5a40c1c0a45d401c0170605484600034661503040b6001c4007662070601d400c2d82d5049072229070100c801c014180350900c000441e40c2000f1412162001404035900088a002900803d0245000410702d4400034440d4007554001c10b4407050540a40103850304840500d640c16100c0110216042aa00039900d07014030784000714540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 522834370 1250 522833120 522833131
    0x3032d03020c0a210e03070608040825060204090e0a08180409060905060f130309180e1608070e0f01090203091903031506050a08060906010c0204051311090717 70
    0xc803000b51015440b2641104c6216009042c5041d5101d843c841c8590040089901d1303c000b580100401e6141850060017040d010703000510003000001c000000508034481c841000c495400310024212041c17030100004c0d402031096003000f9007040d4090155200c081800581285c000341c210740b410703c1006032080340c000c0c000403055020740c4d615001008a0036910032112801e11540060a03282040d0f0072047d100c000040499a0200c1c0f81240d800000758810b6145084644141105c045130b05103560100280c0031180004c00c6138800c9001e904207072103c41c0250411500c01c9002e80300c8481c4c0b1150906285542141d0070040603405200401070040c0641c011584000361030155043d003001c1c8000c440615070813060540001c0d40b980d03007a40740c0d115003806d98001003005007032040c036100f01502c01414098004145a02c625500c0d000150681d00458031082906d0780100104010710703001806080032142c015054800015004440280b800c00340c04880c0200c5584e202d1401d00d554000400c614448000c04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 522835620 1250 522834370 522834373
    0xf0c09091801020c100b03120f0706020304060b06030405010c0e03030c0c090c041e0306060e041505041e060222180203040807020907020109050f01020310050913170403032d03020c 79
    0x64a1244c40c020305c40d0340d583e402c442d000840c0d02500002014904070207180d404400d0002003014021f1440050304669482d54044009070301e07942d42d030409034001c0c00c0000300340f500510000108010440194040001c58400382c031058024a0720030181640ca01884004000d80d034410215008a4a0102031469008140c28203c2c2d2500d0f442e09184a1414115610b40c0700200441c442441000414080d41010300301d903e002054910701a220000c00c82c500400e0600440c0d92813020805200001c075402c0c2004030708403121b403c2000c09240c802d001354030080003000c5012152051201c80e5400d070703582c6403c8400b50550080e01c0e61100480400031b610103042112024810002d040c0180c440c0c2d080030b4400c03c100e07000092903449500f465801c0c803078894140340c1603910402c10400789490780017408003550b406032075804003039a41c134aa8565989440c1030260a003803464a185188081e8a001042503c0c4241d690113140440300c0b150010300070300c081210744044040c6507640200703442940030b003101d8000d040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 522836870 1250 522835620 522835627
    0x7030b060912160b180402130302063a18170a090302180405060f1b181f1e02060a0f020706060f06030e0a0f0215071a0f0c0909180102 59
    0x104070f041e00f4585510503686400c0206400d1007084100c1c01007030b0488800c3d2400c1d450124144d40d05c01c0c0c031414501000344910f1000c030700440100f036402e58808010180310324100242d211002883c101042c0c50707140d03004650820b8040300310a107005180b0304410b680005054920703061549441c9a1703400090a820812000b00000030159a030001800103405510640c419241403604115007403c800070a42c81459560100f0700c24008031032000070350710103600740b4000d840c1c403000c2010b4004042c2140403594043c0303e000d00c409806c1d0282a00e030404404c6901c1e0030010303240281c40365490344c0c0c000c0c1c1c941015070410320001b080c1340c002d900516240c0c2c0110364010f16000305640c403c1c0490321b560b003100388810f44c8050240403068142c85404150340d01c4600601119000c3d80d50300039410b018060003070107409008518282c0100100c1aa1b082c181d000c01c0f910802ca8401001507040141102c5200c070705d64100c000300b003c4040075002c5a1410402902d546055075506001c0c0c00b0090340082079543e15942003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 522838120 1250 522836870 522836893
    0x90a062907140a053307020c0f030304031b05040b270c1b012702030303010902090402070b0702061906060836010614040203010807090b0d08040e0603010507030b060912 74
    0x3d00450700e171919461980040070102d903240310b40f424800c2c01500c1c0120002418030078800d40008861200210071205d03010104422004a41140920341c001001d041d160341201040c42c141050750403e40d030b800d40703080184030159400c0003440600c00c0d02481194404a8400d135128280036a10ba41c0540d840003030510309041c003020300f14161003080140343ca82c2d6681d809500b10010001010400184000000942c040030790002034a0b448188681145203038005030b80b83e00e03038403590162640541c01c07514119807071410006c084e48413841120b510f40740c004903540030b1030544624452407003590700c41d540d103080b2a07403041e150384039200c00e64014070f81da140c40e00903075075104c0c01415a0304a11401c0f0700010800525200030045140417500c1614030403070041c001407140000005102c0210b800a103400324201c8231060110784119000a8080d050090000700414418030210682d401038109400801603565090317011001c0300d94440500390700c81020444540b0a1034980700d544000800241503c2000040c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 522839370 1250 522838120 522838123
    0xb0405011805010e0c0306092512150b0a0e0403110a080c0a030908010207080909040303060f031a0a200a030f0507020604020a14210309090a062907140a05 68
    0x4901200c00303030b44035013200c0c1c81d48205100d074003500c4100398010050f6013081002141c49281c29405d100300401c1200309a808003001510b00c078004d040e0038002c00c24010036410300b009848001002c288085090a0045076541003814102080b5a00d502040701c854565a0b000c442c40c0300e42d09041d40e5148200130302040411101401030100f00540c4000300003110071031601030640e03c1240e03c0b4140d140d106102c0080030901540488461100c2250b40c8003480c0d4039454107a0040c20716070000c40172241b0858004c01000154203c50000c4814000d94503e00e5442540c85400c0d0b0312100900d80510306807005000d203034041c2d070340a01080900d0741408120485154880d100300d4030119144001644810240401c1d070400060741c5000d03028004040e9001c00519021a9071412030700498100c0311405003100240010a10655101d41d0b0010702d00c98007410100e00300e101500c1107000d8011414440d2910305e0303451a454045502201c2e080c0b20382420541c142d21581c0fa00048012001c0c818007415a900e40000c80 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 522840620 1250 522839370 522839411
    0xc05060a1701090c1d0307030f030c0501050108100e0c0d020f0406080111030109110703021c050c01140103020a0b071502030411030703080d0b0a03031b060b03010f0f0f090f0b040501 80
    0x1444000101c00003c0d44c2c0091010615080b400310710311074400964400c1c1c401144100680390840031100c0004d09030300d0200c480006103070001d450782d4a0200041454840171401c1c2900540c100d1050080043c8101100e440d0540741c20a10387c043c00c417003d034400505200c015182420390091001460a5070b420b682401d450a400d800031343c1040c00030040c41201c85522541011a166411007410302c0300c55503000e591088043d24805030750551170ba50300c001c944284120380c100c0c40d081000303119800d00c2c04e20341e05070a1030a00089200301289079000c42c04802d05e03005d482c0050f40022030383c0c0c2c041c0c01c03c1f1100c0d0001e500c090700684602a0102e890302072070300c04100420084d841060200d94911a403100b800807110b50509803803040a07640d90400200f58009144003469084080451411066140c0503008000c04d03c4207941650a00300116000e000d544d010ba48036071261241884054040308082c4110741d1032500080200d11080049004a0021000142c0c0302c0e205400000301e040349200240760844 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 522841726 1106 522840620 522840629
    0x40206120402030a0f050a0c060203030919021c0b18010b010f05280e012607180317220b030a020702010c080f031b070c05060a1701 58
    0x10350500804000a500c13060301c45c0da40c01203150072529448111004d8400d00c01740c1d100014040c3c008000c982c030410303040c40035160005e11940d40403481004000244c0e040740c607081c004408580c0d000c650503102c5005d423206c620585000f506500d150a00908002c2442e41459128002a43c0118500d00c4080c0d16060040d1100701d80101103500c1c6141d072142a02c0c0e00c008003005071a4a03004181914484002e0707907143c02c1020b10414902c038110091529204404003030000540440c4524407080c1b1106010b40b14030201d55507170711410312a50200c0e21226403140c0015aa090000e21a0303142c2a448001c410310202003840c2040b241c10034040108900d01c1d00b0707000196002168440c0c0303102450385e40e204440540f200b418140030076083c0c0007115178040485000081004000900040e504a264420040c04240b8141403c0c0040c907000b580a000c284030008070440450013804410b1800391 = true := by decide +kernel

theorem cover : BRFrame.Cov 522661870 522841726 := by
  have h0 := BRFrame.cov_init 522661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 522661870 ≤ n) (h2 : n < 522841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
