-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2125
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:42:32.087812+00:00
-- url     : https://prove2.me/submissions/fd551ec2-1d3a-45ab-bfda-1efd3d4af1a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 382014388 ≤ n < 382194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 382015638 1250 382014388 382014401
    0x1f1511100f140103120503100b191b0530030103030f020d03050708040f02030106080f0105060a06080907030803100302040609050f2a090f0405070f02060105150d0207170c01 76
    0x388070a0604045403103460550149504a0f80c21405000c1d0342c00808000f15240d0303002610040103892120400704a49545030020b2805984d801400044011407480c003400c1e142c8021100000c84050311020b501144010402d8514500c40c1a0924003240480442c801c0c090011113480131000c90100c00441007541003000c0001d0429150211024090164011001d545040725604001100710012400085820406140442c0300070000705100d6242c8039028605080040292421382d1070b4410700000d030502207401405001300d071070042c4880c580f0402d00d52f99440c00340700c0104200300000000d043c51520b110345001a60f40100188034040e50740603414040c00c01a10b030741c0c211060000100c0e02102d035907020303034105054101071090103500b034900199503074015000d10b541142629101c00700540d19841254462121a262044c1360344c030340d40b402032401d801608543d0007500c80950041c07407419004117a034406003000030096521003480c5031201c1c400c0700c14413141d1850b80d00400c0c0c10884d05811b41204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 382016888 1250 382015638 382015661
    0x60a030c030c09050a0507050a03150e1f05030c0f1c0b0f090124050105091306030c0303020717070e040206091509040e01020f03060d0212120d051f151110 68
    0x9200d80c2d100c9840c01000c881b0b05641c0c1e10b010070340400407860340e94000d8000545540f4200c40420b2030590b00d0741c0328911540110b0300741a103c11070b14000300c12034070940041342c00b918094000303010007030450f40410154130000d5405032141c091131201c00c49401280000035561a84809c10309264203000c0300c4114041016a4440615400e003102c0106920041004d4520881c032198280181d518007001035880c0c1d84100910f58000078840c2c40c03d45c1036003840c0540790040d48241d981100c0c0320300e181802030600c42103411803103135101051000d241030a400103005064030007070300c88080c036a2a244000348003031003184041a00003100500788156040c045003c0c00005a090303805011903030780289040d080f440340352880c5c01c8600e4140007189041c24803000680d03003948003402d004800c200b1280001d1914021400250450300d0002d20740d0702102c1e550003900e410442e03a074803a0b01c89641b01c01c440280905940280340c20300b80440f000014081c803582d4510744580c01001902c15501000c072008018080d1001d00703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 382018138 1250 382016888 382016891
    0x509130c0f031802030705100302040902070c060e0907080c13090c090648081801030c03020403020d03030902150406090806011203020607030b0402120c0306010e0303160209060a030c030c09 83
    0x840c15483d01040300640443d40c002c018020450400007003218403035070321117100d00b056824000400c55003514401030100d03500442000650300c3c5082070003402413050443e014014000c01044c0300086420003003240c0c102c0b03c0b00c141d807030321012040c0d42042004115440001da031805c0458002016400c0100369003550010340e03580c8800490b003c41e6884d490820046944841c0300300c01c2c20043c079004200416100c004a902140040c0b0481d00c0d5445260800c2c1c5a841d40050030321008001c40d03826105a541c0c0900c0b07410f082d8105031550b00040e1f00710f48910307009410f0641b681c004004555400714490400781c52054529103540d241d0500400c9007a080c081c900507441508008030781da40c0d142200c082800c1c0e0503401411155150726048000c0c0c01d90904043e00300d5000d00003070500f5204040c1051103011602d10b12912480c01cac200042600002d000c0042c0207400400c0a0f83740c840080a010a8498068940002d0740c1ca900c404190900115400130382000307184100801004200481002104c035010030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 382019388 1250 382018138 382018151
    0x1b0c0b1902010c0c060504021906081519030f06110d09140c060714100501091a0a05010f180905010b04080d090e130f0c0803040510031b0509130c0f03 66
    0x40903403c03100345881403008100c2c605500c00c0000c0b0681c201c268407170310291031400309149040302150209140d401c000d012803070341402c010415007588040d0140c00340440d00c1c130381140c080e000b60068034002da005c060405008c11900c0303801d000440e00700c2c5805520401c5400d1307650a2682c503000040146450850b108440200d46030036556000814a010310001082d051030701540d07954860300001d000e4881c1d001801000380402d414001485030500900e04100c0100b20402201d850744900c04c901c129841c0320b18000030003800107076403082d800300e9031000d2420100c0720340c072901c21640700407062680b00d0116103003008000f05d031507950b03000038000300c81c9618215480c04080350410358a030821030180842d650ba40c80b0001d008103022000460004d8014207c1074424080780c0c0302c000403003441c0e0300301d14100c0c2d000103010011414041e1a40000680703a00e0f041058481c41010855401400002034081101c0071400c031500d83d485d03880550700720b4a0319100b0440c4c0b40d1040000703091100f00704c41c4080070919006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 382020638 1250 382019388 382019437
    0x1e0706090605070b0a020304051029031504080f0c0a1b0b030906130f0b0a060312020307050705090a0b0d0c030c0b03130f21020f010608070b0301061b0c0b 68
    0x20242e440f01070707100b01d0b4122650f580d500f20200a400042c4159807910a800609004661912540c02c07500042426940303807407034052021310900d4040090701d0099000c00c840788911a03030303c40c1058000c0d502841c040e030b803403201c4000d0385414064001144098001c2094060421806002e00c02006403410148400107980e18032005e07950004454101c5a90450740002e0303191211100108401d620402460a8400d1036450701044901c0c00c40c1c02403030060369104280148880f02d030803070360500b00300e1004520b0b080140d562240c403080ca51042600403403c540105030060040e81001c40480f0014010050035407103410403582580045c40f007918004100c64001c14020000d07421603118031942e02c2e00c06402005039440c0c00c0d1840d103044055968003800d412409007405c5916071644003511541c010801c0940c400016403c41e821035120310813503032221000f004400c00351415641110450304000e0000400a02d0b041c90701c0001100042c51052201c00104083d0380c120040c0c100309004103245d00d00c001858 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 382021888 1250 382020638 382020647
    0x906080c012001060b0c16150e040b1203030c03011404060b0a200318030c0307080c10050d0609021b01050601050d090c092313020105040909051e07060906 68
    0x8039500c034001031040c0560b40380200300d1038401848a004800004c2c3d41c40d0b89801200860b00500301503811303504030549005c510300c6400e8000002d44004e00000036003880c07043c0084c21506c00c01c41a60b0296440d05407501941c0e80e000e100c49003c0283c0d0301034907500e00e40752904200540c024028014805003140001d1480e0a142c0728401c159125412490301d850125841a164691003010032402c1d08500145030395501400d00c003801369007800d89010461016500304140c1041801c2003554020340c09000c04220400002806080000099400c001600300107001110b0b9449103402c0c1d60103440c1004d40001c1c0c0140198001c0c480c1c24020b0503140e008600081c6007500366001a80e071640051014000cc000c007a030203a0000c0d1507584941c080c80e41e0a030b038070754954054070580028803a00c00c401c00c0090500507200f01c035180d44038400315244a02c0030302a0740003918901560003090b2401e0b5442c15101d0420400f04000803030f002051010310710ac0312000e8442541d0345014000c0d44006081004005803c6005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 382023138 1250 382021888 382021903
    0x8090304030803191e05010f0e1509060607050601080a0210051c0e03041a0a080c0403152c070f060207080307080711100503040b010f031e030225090608 67
    0x20030042890340d100c50510103503050003a40c16841c10355640d880301661085c0001c052130086041040801e00c0d42c90400480d0304402c1a52001070900d00d80307000c005041c140c02c100f01c07940e254105c50321540b54a610010407614002c04200500d0741c0300d1003001040c800d00014010051a1003200c80e80e070201003464045906008107010340c80400c010500e20350010400f9045030148200ca0000c8904007981e9254404241c41d128014140b410000600a20060780c04a84c0030751040c01f1007941e070303d0507255680d0012904803401c080d108903561030704c0c1404003c0c004030741d802c06080c06412071041d8400003400b160f140d0a071485801c4444019240c0082d201c0d00110301401119040c4029506101064807010f800760f202c4a81110a80c0102c0c0c07009609540d00700350104c0b01841d80c0d07074940d181c2c90145416009000c060300080011958900100f000690400b00301c844c0072241c005c40043c3c1401440d0507490008840284032800d181c070604058907480c039280d108201c1388010350078404607075070380701c07203a1620713070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 382024388 1250 382023138 382023143
    0x2120402010c05030c10050609070c12050310050d0809044d03070914062a0c06160507091802100909020301060309060c0e09280507030207030809030403 67
    0x510000401540c0107000e0910140c1c011003c3d0391501c41c02d00507890070001140f03400369030b85507078000344199801c2072580309501130f080f8102000880400d444a1000c80b0304090a1020800000005204004e0309642c50000300000740ca00c000c400f0b09468040c20726041003001c60702135442c1400e4040f10720f180c1810b80281e0607c01480c1f132810b26510b50051055171175243c4180b00c3e24005003201004008c158010340c45070006580d603004c82800e03d8181e038800d58a12242d42d20914007130111002a050340003200201c00f501c010400c248009044107181440c00c10718800794451000f15501083c02152509a95054401d07401d59103803030340351209107080381d0f1f0395100440701200c803982550040c00e0600b0081d074040110f04010301e00c6507a54103458281d80c000d03004400043c1c4c4038507040c410440c203400340c00071202180c10190710840105002c1481208010b01003c1c031212495080d00788900040b6510078a022460007d0040d0302d0f0800018011b03610480048000485880028009640c0403054409032030303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 382025638 1250 382024388 382024417
    0x507031401060c030302070c170d0201090804210b07031a04052e09060b040609090203070806041a030102071a0f070c03031a060310030b090c061b03041d041502 70
    0x3400d01c0c20844a0150f0114200e045c90303800c22501000c0340e0518421002044213030440c00d2401c000c003043c1e50800321916201c45c29a0f041c980110009902c4800352803e4400713124445415502c500c4030391801901452002d480c2b51107100500070401d40c150444003074165514950780151201d0400d22044035000c0b80d02c1c80c892420225900a122100703003804128a0714250500b07003c1e5107070070b03000c000c0341d0b031941c05040c01d113400040070030841e500101880020183e2580c110308501c0d10b0280607240c058000e101900c1a03641e0b100c0c00052208440da24000c020018000b1921240039141000e80f811180c0d48001d90b482c01b00c03001032182d00129024921450959a40001d1850556400d0b0003501d2154043c00c101c80e80d44521000e66210480030b14842d544000015840d6451420181000c810180c500301d555001444400c1c0b4a03140e00c0100c4031a1a0a14410054414a1401903086018a130413138000c1a4440600d840310540021035580964081c40c0c84807168240e1401c090100d11890100c0e61505 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 382026888 1250 382025638 382025641
    0x5210715020d0207080d050109050c03070e010804080f0a020f07050a06020a06020c030403060c0309230a020105130b0c1b010903170c120a021b15120703020706090b0a05070314 77
    0x940c558010780003a5500384405401c0c00e8850341d411005400810440c0d1031326503100300411902c10f0601400b50040082048e40380b540c244001e000b03100c1c991134030019040c880f50750080f48c2003107a43c804072054410a40c0020307480750002c0d03800079221040f10760300b110944141980461640307030140e0a80200c94040d00181a45c408598504c80a03401200d402c6000380000d010000101d241c0d0300074102341084aa800143d0140c0383d182a18401c0d1440542191403501d41c102c1100071000040c00507011a0242851926420110025030120541c1d80104944220100b508a0440c800051800580c1102c11030040e40b01d00c48801110240950703c009080150b0b07a400382402084507900800c10038030720000366411f20f81440c1c0c101810340e00c10707144040140d104c040c207020200d420602c01c0081c0501200e80c1d031000b00e00d0381003a06080c0501079401e60107000340310210303650901a030704581c0003e502c0700043c800d01200e07003132000355840d0403107240d46010308003800a6460b601c00d2180c0c0d00e900c00e00341c1c45038115 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 382028138 1250 382026888 382026923
    0x1415070c0606030203070b071406010b0a0e0f04090302030403020a1a03040201050c340503070e0a2310090b040e120a1b080703030c1e0e06090d052107 66
    0x421440e500a507091580c620020026071002d1101c24064054000d08591790b0b9150320700300e001d828629841801c6600700c0303801132000e50108402c40320f81d0310951500d0b01020380315500040c19001034500c6154400d14082006080640110190040740d00885821548994400390307039036600704021201c0b0a0030010400280150700400281034000c030342c80210340100c034420204a41c10316180403400104403210140e280d04007100842140586010340150010510382102da85202c84054181010651124003445401440c1d928107205490080d80003000741c213026040c8820b0609034051451858180084141d690400f8040c3c41074110000c03006143c0b2000c010500030980c0c1186600341c04000326440c007254400c10314a01c1c0011075000e0500d4564800ba10315000d0116040340e4040030a01a404d0b00c43c0040003c11000d9428180040c00c2641c0151111400900c03244503407103000d07500102509a080034044000345d004e40204d048400500c000480051100300d41c040d440c0d0090440c16001f204188 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 382029388 1250 382028138 382028147
    0x306091a0108151e10091802150702120601090c1b0503030403120e010e01020c0d08010f090209130e030307020f2d0c030a0807110103361e141507 64
    0x40c061002001e0a294444d20700b20180d040c5815111010840450348041c40701000b548501000a4210740c01070214951950124541051240f441c0004800c081480d0381035446a0503160490f80b4004150340e460340e10380b03010b18000c0200c07060210000307440d20302825000d11b070603d00e140c0d03840e0888021402d40c1d480b95000c98500e000490200c040c181c0f0303400d20b059084424000c640b0124062030000d42c880491070605450260f140800900300b188040c01008220f846918010654103c01c0c5c1c051390300c050410100301c41d8030411184203001494100d00d1602d80360084043c5004660316070a480014880d070903042d65444113854610700d10001000402c00581010101180c0d001d071101c01c2c1e8503241034441c0024101416100156041000042c43d4000c002c070580007910981e80c02d0a0030483e009200504107a19896800444254a030003c1600b508008007000c200c90580d0001201411200e04000344200c205140004c0313400802c100440c001d180303004103103407120700c60340141d00b00d407a92b03200300444 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 382030638 1250 382029388 382029391
    0x815190509070e0a0b0a03140112030c060207051207111e010e0a12050d02190f02040221090d0f0309150506061905030708060f0d0201030f150306091a010815 69
    0x30306100d02401c00700d030240c41c1c4c0312089006140c02008103440d05040d43e4042c042d0303505400320740144602c0000500441d20822440d1181640600d08030500d40c80300d20703000000340310f1540083c01d02d00c80e40c405000441c0f42000141203192054007024287e11040303003032000300781d80d0108100207800d600101c1000c1354840c260103d60300f00300800e0100308954410100b0360508214800b59010b8000b07034580c2c5403868040211003007040d4090400c0030110070a88440ea1881d21006000344140e400141014407540d0b0010342d549041800b0014845a003445140c20341c0c2d81d001e0208200100740c0d12850346001138028072584810315000081d10550301d6085140100a01005052035030004050000c0e06425540c030821040030303240307515410b43d43e08008002502c0c5c2c1c1c3c0c0040c41c8911070800c8a1055050743c850340d4a142100707a083c240030403d124945075060252403941400c01601c001c9000010034441c01c0d410440da200d0046407459201c4a003d4102c619151003402a9803007a4444140807240210310755005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 382031888 1250 382030638 382030651
    0x60801052a0d02030901050703232d10030b13020a050d0c08030f2a1c0504090c0c06060e010e13050102090d061d0129120a030815190509 60
    0x82c600340390b140702441281c0003a102014503a640d8403c01c113415030580b2603407403541c40351880b00c0808002c180e82801c0c0194000c000c18001004044118000400500e50519103078001c14030b1340540c90300d22501c1c4034018891005030f4100780fa400208039a4a9845045502175030040c290544a03030401061014640c04110104c1e088440b0280004540d44248082c0c104403440761b114030355035000348a041484111300c0185594800e2000300031421854000b030b010b141c0751a090180514142810000d0301c1a000701d5000e08485814041c1103510240c2c0190100d03551481454200216504e5400c160648030003401941d80504440002c91500794440c12080d441c80d02c100000340c9080444008140c1c903442c00001115034a07160020b0706410700c1c601402015011400008116607038885c0c540701100200150441c1843c40da100b42d4131165110406d0101c000c07102c0d50100d482600740741c41c0061601c14111039403003d0032140c1c4c404c0710300c900d40603100364041e0110f400f085403d90700340010001498000b5108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 382033138 1250 382031888 382031971
    0x40501020a110a0b0307170114010804030305040c2d0b09060f030a1e0f2003070f020709050403080f010603020f040b030c0706140114030a230f12070606080105 70
    0x900003900e0130007944115400d6076219461003001c0b046c018007101c1038001003500640d10400055a0364014101d80d80103800d440c02194507111414801002c1803950000c1c4202003881d007008070f6000d0780c0340a2044c444804500c580b44a5a00e220306c080c1e41c050380e074015078040c00c100000c07a0311062001c0a1900024504070010f07482404115528100c004c440c1a0341c0d074103803503001c458003045c035901c1907803482c82d1401380410320f0b142c0229445200d840010806005c1c007101509246280384204000005004222000c102a0806040280000d14111381010581824400104044d4420300a896400e425052179500301810703c4000450750b00000c02d00014088240142c030003140c803034061000048074154020840e541014644c90801104a440d240203500c052404c1000860801e00c503000303003086184400180c07100d600624184840b10f1340078100c901c9850b1020051001550041040b06d1140700c08000059031030241c5403d0750300488070a0010700000c07104d404540700c892921301a1000f01c442 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 382034388 1250 382033138 382033159
    0x30402012a030c020117100510120207060209030c010f02061513091a0a110910020f0f06070206060409030e01080405031306090e060303041a07050c041103060102070902040501020a11 80
    0x10501d12040ca141098002542d60a840c60565821002180c1c001c809010751541d0707840c141607420966042845854024085103071014070507440381340f090384079010082c0305654074503103402c1c0a80613410240348248a8001d08880403403540c003440c40c49520364046e8002d4a1396640d6280a554240702c58120550402c045020010f0076591522408504c0c81c4280010705d2142e100015900f000c4070001d0084035640c0c5042440003194012505880000c0d404603040010300c5541041242410120700d02c0680c1842000c1504030b049030701251041c49522035500300d80c00c0c3d5071900d0410054884e1290301501040110004041da548543c0440d0303485401030040b02e1038160500070944403e006903010400103002200240084074500a800b60030060032070041d4201030070700c05100207030944403c403030507140340014031031003088003e01c00808c0800c0028820060007000101b4104168170071034000d40107000c2c0081c041801c2e007043c8241c8061f560180c3c010044200701f42c1d105440041c0b26552103074003038a49034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 382035638 1250 382034388 382034447
    0x7120c0216081501050109120602090301150e0a051506030a0c09050603190509030403082b09060603020f09250908032a030406021b1906081806060603040201 69
    0x5040c032005080b03080050042d20908520741c2c0340054180c01044c100b209540d020414090312666102082d901f001c070041e51a144000001c0c010003c0101c00303c1940607400d0001151200c451059120300750700c1909015598919111a0b0b010150541441e481902400840c554030700176400701500b0200c60074000705682e103410005d07445400c101d0b214604031076034850001814000f800b0b01c60b005031300700d40113504203030942e9500e4480780501500c10080a5841c01d605003003440311240148a000e11030400c01042040c0c0c02d20740f02034640c6000507030040faa065604085070a00000356841100301035401500c0203840e21811345174844002c1c0980400c14903181c04102040103100070400703071100c2500c622148484a65044110190007400c1e156900306000800005402140c0410301440210300c0000400d40300c0700140c20210034680300144424810804142d09400180c640c3c000c40892201001e040f0240022a80d544011100103400001c140b000c10700550040c224410140340d141610303d145aa0340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 382036888 1250 382035638 382035673
    0x50c04142103090126010303180314070f050d150509160e06030c010914090408040902030403080f01090b0609270411011d2d151e0307120c02 62
    0x8400314140350400030343c3c0249503802195034100c50710007400344000b4200d281c482e0482c0441c1448064140300281504000c007814904058010f56403102030a49410b0300b0000d95952003a417030050300030311a80700341c0c08266880c2c49403000c003120780d00034030a01106540208110103042d01402d2042e1603c146a903c1038140503145088020301480c0e040c107c160301d40101054075040d10100124140a6164802c0c403000c5206541082441e1054480401030340311482c0040451146611000d402c51000c42070004141c1c0c49002e050240e00240f6402c4032503626400c801e0121003800360601c1d4860b500f00690344507814030603422010700700c20350080c801d84407019110306001c003411241101c2c440c002e030f808400950f130030843c00465091110708004034a0061008a82d81140052120550b80044084070351600022032955405100181201d1004d4411011490081d004070300180030703d60b200c800c045000030291054a00c6600550380750032840f42000300020041c100c0a03445421402111113082103048dd4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 382038138 1250 382036888 382036939
    0x9022b060513050402032401030b0405030d020307080f0105060a0509040911030102040f090e03070f08370215060d0b1024120c0e0402131206090b0901050c0414 70
    0x71140301181c0f624140c81010b0400200300900700192035280341420b22214074100301740c1500d030700c403040d03500c5070310f4500b40a032640c0140c2c118412005e00000400c80040e60244402d401203903400581c84613070f44c840701001000d000f001d046800090301800740d00076030300c2d06411041e00d5a014110420b000004040820709a0344180c000b9955008004020030000d441c900c10740d6010030403580070703600342500c640d240261800d40d42000f501c960301c082200d400c050403003004c1034408107a60800380d0f08000e40b100002c10611800006502500640d2916084c1c0b8801000c540d2245200401c1e81c0c0b940b811590711080408030246c880c21888450709800700e80f071206490f007084085e41e080352030100b0054402e802007000ca000000c0803d082e05080c44499641c0e0011506001c2c0403040302c1c0542c80e4a081d0580440c013184a0388140380f04007020a440003807201d55071001180c20b020b010240700d1961030310281426948180c0750161001405c1008011200d00c0301e1400e0302c0220000d01091130913200d002c28600a684 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 382039388 1250 382038138 382038169
    0xf092404060f03150b03030a270807080709091707050307140709060b1314010c1b091515200a03030501080106121703040302120304030309030909022b0605 68
    0x364400c080c02440402c0c4007055010b100c02e8020300c402e80178003020070781307a002d440713401e00034000340c6180032024074004404000c0101070941a0303003203a40d507651400e507102c806100d03d80c0d46000c1c0403404100905107000394000181c200880030390340802c46560100315882480262018002405410001103000244c41d6070400038000030034506040c8000741007180d000f07038041100c01c902005070031044010f002e0042d0888490510680d040a1500c0c01079030440402c4100a04112a107007800e6014000c0034400c0065480942042040751403c0080760f158031594040c001c010451648038210440c0300340c5040010f10136484004442d4047d01003142d01c5d0641d002c0045010079110001803280d42801d01c074002c0240b000c00d6040b50007540d6901c0c0c1c1c50440040ca44420480e260010000381854000c00221a0014107518030580d01d140c42d050040c024030b9880300403400200c5403500001c60340514001d130784c0d0316158100c0000c4075843c1542158504607441548400064552400044a5440384840203140780b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 382040638 1250 382039388 382039409
    0x1e0e0c091f0210020406080f0421030509010e070303200a1727150309030f03011e06030603030e0d14060c040509010902040605090d030e10031a0f09240406 68
    0x3040d850000e82002d01000320f8000d524418002002600e80c02104e00350080c87d02d90030503640b925030303040ca281001c00705200d22942c0881c5d0742d4100030040c3c0c154041c52046000b10000c00640445500e40381e154541c0380300190000c0c01c8110081150b420300380b111810040c0700002c880d142e40d00c4c0e6542198440740406800c05809021640c0000c80300881c03d00352600720035105081000d03021400040304884a05281e4515100100000340c1c000810002c82d001444d201c11650340703070741e504d200311800400c28105001c0043c100c1000020100e000e400742ca019a40d160722041c24103900d4605204036044024000c0c0c845248903504482040814850280a2203907a66900e98903030810341486806101a07000082c1345104110401c1540d52010076980d501d001207800030944102c03410210790205120b2481a07000a44100010180313030154401c003003447d18401c09100e054171a0013001912810780601030b81200c102c0001442e2014511400074400b14a48408a1211001404070701280d559400248909 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 382041888 1250 382040638 382040689
    0x51b0105180c04110d020703090810060f0b090a0b090303070b04030503090f0c1e01050f030f0604110304021e15030907030512030c0403021e040f060501091e0e0c09 72
    0x8207061140048804040d03c060200300403030340b0004418818920b101101c80e81c08982201003520541198001b050020304840b860b81ca0580442c0090003a4840d80200d0303040010002050381c1d0f0101952300c0c201004111400c4186402500300490740035020f640c0d4507002c100011000aa10321100034040e9000307586454076071600701c03440b40c030b01f420010303075205558003803d81c004040e991206010b0ba0383e1300000d440c440c0b181039440160b5a9010345018600c00e0384002c001c103d003040060569a11400301114288103003106491820400d1000f40c8010350084004200c80c00e088501041603060f010000d001480000690240b142a85c0c00a403042c28407908001800c1003404410007500d110700e01656211451418110a0041c161140c0d00c0024002c40d403070050800d8458508082c49801d40002d04103002004034540a0b40c0141a01d004160105078000008155040d800c1514056a850000c2c1d120301d040c203185960840c0d00c401021440000340401054035180c03520341c0e442c55140b00e403000385810b4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 382043138 1250 382041888 382041931
    0x206071d041d1006141302040e012301110d1d120a110109050907121104090f0e06060f04021b0d0545130e0a06150305060106051b0105 59
    0x80c10350502140703c4007801c1c5041440f000e00d03104d444c507a0010007121521080d201e00d195040181c01182c0c0000c00707080148000168001c00c18842d060000440081010380c84004001550b0a541020041105a00c038401074a04640139495100c111501440c4074007161041034001100100c50614030000da070845c0e010081085049030103841851024200030080078180700110308042801403400040124280e103c3e203104074141e005034020b018a508031030340c994a5002c8400a400c0727084440602c0f47c03a1805444610b03c01040050244900078150b00100d40d01d04100000784d082281d00b000318001d007400443c6501000c0000303000d2581e140d120b040d06c41c0c45c81d1400d0f440c104154441c4140503a940b14044c0404014411680d9015044400b114400c0f0100404200078030762000c0114900b40c45c2441040e110400041d021030400e204c1d11080c01700004400005510040361320008002e90f0001d4010300100c0e00420251900f105044040741d1080054981103094660a0b10220801c2c44d17a0f00e8a09203 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 382044388 1250 382043138 382043143
    0x806100b07031e0c02120a0c08010501030f02060313120f08070206070f030207060b0d03030902121902040c230324030c040c02031e070b06120a060e030403080d060806090d0206071d041d 81
    0x5101c04000bc008a42c03540d1180420444500002031060710008006100d6103401c03908001d21581014105041c65540d12000d090b0700302001c80000840c00707160004041d01d1001a09910404c429682c010440002d94001e074041d402c0090200c45440e1580402740503521001c159410b124020f0b074004c40d407031085005000003091014203000d42c130f8011603500030940b407070740329081041030341510000ba030034a00e80cec0d04842031203138040040e014048440c182c0300700031058000780d030160703c03c600c409042c180003100c1a203461b4413400001c1c1c4c240e0007103113402165160551084030b01da46580166458040b02c018180c441c507010f0b240131b15420b0300229410042c84295541076900103010b8030200d402804603410b640d55160f800c3c2e0001c0c00140c031901000000d450070f00507100103560119100340c54410700350100c0c01405107405825001d108183c002458090001044102d882058000c0c2120b6110800111080040340c4208050041c8810340003101ea1205d1062220422002680101c8546203420039070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 382045638 1250 382044388 382044413
    0x91b0c07090b090405070b03061309030309020301060f18021803030703021b0411030411060f0d0e1209060403030302030a0b10020d0f08090c010e030c0a0806100b07031e0c02120a 78
    0x6004451003c100000a4400203051043d5104540c22039200d50b2010005884e1006d00e401d14483c0c40d00f008440002c0503019045080304034400c600910445492307400a103050300c058402e0741c00312003004100c91040004e0350300034060002c000c0b000707030480c10f802c3c0042481d40e030002400b2001030f40040c2c2c518803403405121255022400480d000c2c4000401c0e4490a00300b80400b0740040c140c0b0000008003c65561500e08a91054000d854020f884455941c1186e008100600441c0c4280c00b908240b444411812400c50306031280040101d400d00d415620114000c0d00700819240006036299210203081d601e0442100300c03803a00d82d009107100c41d85004c0041110030a84c415600344401300f4140410441c0214142000b01d1082c030b0310030381c13440c00c98002038034010403640460380000d54507402250318100404c0b4a403143c140200524400c60303443c41c078500148201702014000541a841c1601c0100c07031044a1410b0b0002890000342811480d00054003074082012620300341d500c1034918804005403040303800f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 382046888 1250 382045638 382045661
    0x20a03052d1b060d0b220b0609060f0d0e07030f060b10120f090209010e10060e0609090423100c051801050f04030b01080a0b0c07050705091b0c0709 65
    0x10103102c25542e20140d40c8a0005124520828001c2503081444007103500802c490750008000010080c800d0388081502c44a9940000d14682000018841400c0201c04c07615081c801801c031510340301c6210303540703a15904456440e900290f1160088407100c01c04018075030240d0700908003203e0302e00c1e0501d0070600f200c01040813503016503040c40c1880603058210003007982d0300c1c41d403140200b4100204c1c40000c00800c0900b00096005541030b001180d4020f01c2c2c4d900505c56001c003102822020340301e803402c2d1131000e0629101ca92003c82001183e88a050680b41e85402c00d101c2c207503440000b880d101c804a2007076655220a0100d6105004c106080803490051000000340c0d4204245070002e08480400010045401c40f81071080000b28000b449030550304071001140c108200f2485540c487e14030399101c541644003680c00c024000081104200458110760185504c6401040481c0c41c0809000321600c2c005d081c1c5505500c040f05840d200340103c0020305c99007041b00c028150301424003c81800300d81051009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 382048138 1250 382046888 382046893
    0x1d03040303170a0b0a0509100b070c140d0807170d0906051b090d17090d08030106030c050405030c1302190c050708060c0d0506030a061a0a05040c0903020607020a03052d 74
    0x380d41203a00d0b0305c15420151030080c2c40c60ba0035643c0ea440c0c551050040c40c2c1c40310380d41405c000307005014811690711031000da4100402051801d010b803010090302c290b2086001c0d02518003000400006501e600b00c0c0f100041c03401e10210309083c114642d0804644030008140c072206c4c0c6a00400000140c604017004460607055042c50810b03440b10046801060740540c020300254038800000042c2071620b0a41c7c08200004104009910341480c00b64203603003007840740e0f002103814560700100982c09002940d0503142c000c1c0081540b44c90300000c20410000024500b5100e650030040c140d4000c0c009886a02d4030340ca11b407165502e50f440b0b8502241b40c02e150794405845500503c06102c00f24002c1d00844100e40300c0f6041c041140d458020000e401c180341d5140007044075242030003008c0c070179948500180c0c4800007116400c80e155950010b02098031510004400008c601d0039040c40145008005840c0356400608060740913510795a520303103404480e1a40c00350300440d641e0304900c001d1150700c155a000303e404c000f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 382049388 1250 382048138 382048151
    0x100e15011710270f020607030507050114040f12120f021305100816050903150712090b071d03060f0906070507050c010806040e010501060509010e19091d03040303170a 73
    0x10f0302052a4240b07801c00f1809050044082c86001032840b0354058000709419650115840c0c054010761111000b00c8465081482d031410303400341006010f03c550b8101c1044604c42001d940e59200702501034500005010075290729800c244040e1240400304e4218070300060780e644c5403281c00680c0c00c3c019440244900891400e0300070b02980251050f40250001380c1d6280555910b03001a60f081c000c0d0348519030107100d0b1000c800b0703980307569500c018081d081035107542500241d1441980300381e5007406406000100a0f030046080785114004003d000400341301c402c3c41c4984d0308400281843d0b07040e50008040041c40c414400b0500082c05156004681070400600e40616590781c0780c1c0b01d06503030081506101c4a4000222183c8650b0040310319a00c19200070485580c654401902d2500544030300c03400540c100f40d240da0705007480c042070204240400e1800c0c1c0450315102d5024041d01c100958401490358030380c4240c450840420140001c0c1d4402c0d210004408000c294003a04114000c01d5404c4007820101c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 382050638 1250 382049388 382049411
    0xe07112a09040f0b0402030a1502030a0e0a02030d05160812100b0c0a0602030403030902030105040605090d03060f0506030c0403120c2009060906121b1002030c100e15011710 76
    0xf40603510a034000b07001e07081a5914000a401d01d0000d440152040070b6034510f01c1c9184c03035264001c510035940c4440030440700032442041540c500600a000f50594803c48004901c03038010405006100c011452081c000390342a41d61107841d400c00b501c07000103c0d00902c180003100800d00c4c4064080c105290100341880402c1c00790f0350f995000303a100581050f9000010900b45031098001415060b00a4001e2126082c00d00c1c145006100c00c5402545a01a28038040c4402d4440d00444040351340c1451490085420001008010b91000d803044c0d171000d400f008000b0010700101480c01d5608480e45900359201110705100d10403120045404043e0f4a070f0031410755060344c0d0701807040d811181c1030b00d2048140e0344260200f9008101140004014814001c21107129030149501c041564800d5407c14460582000d080e6502d0040300c1c0c2e04511600104901c04c48400c0641c424007090300000d08540307002070901c2e080c0825410070381140d0f24440e01c50140d055060410009000111044201041501d9000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 382051888 1250 382050638 382050653
    0x702030a03030902040b0405041a0a050613110415080a0e120d181b0512070305250b0406050301051c08090f03240610030c090e07112a0904 61
    0x240001401c1c0b55a400c085800d540300c07540b2003c502e80c8007410410040c00d06052034030443d0400c003d8084030510010000305a400b890048902440015185454040303422032500041c0c8100c1803204200c603c24800041e254103089a03105a401d1580c60f00000e9040c01ca8240040d114200a61515a400305d540b541c640702c01c440440340702110710140004c5000d5072640803407001d4030702d100181035081810060701140b40840411070498000302d80b0ba03461412164000c94036000d56200c06851608046810071117401202c01c1c2c0e0f05208070b4181004402502d6104410303a90b0000d030410800140080014849030278000d652214207441032540f1a42d001041d41c0e0f414480c4903805031a4011403003078002da0095141000840d000b40c42600d0b000030078402541d40d4209140742261310f40e100b1000001907200c03c900a01c140040380c038550340d031556501d0608040050700007002e4040010084d102000c20074520081c000035102c01458500111080c5a800c41846101c1c3d09d85d4620b88500c00c03804c02d200014060 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 382053138 1250 382051888 382051903
    0x1020712170610030218030f07060f030509060a091e061407030527210d06150f050702120a0f02100e010e10020102070b01030c0f0e01060203180a0b041806050303070203 74
    0xf18075000d039880c1981c0200900040019035090f8061058090402c0040d0b000f085200566039030740d0300d100340c0e0070313001104800b940c00540300031907550040e00c0410080612074100380c550234044c001d506110f0030f01503400c0002d014910810740380e2940d504000c08071108058031441e00002030745070078000c50800102c0008032030032416207c4065480501d43c8558031206201250003a00d40c110303100e10302e0510f1482079500794490f24041034621318110002c51128011555031710210500d17a5080e540c91142c400c10b407006d83c020401641d0155414002c96800b2108124440b9034500c1120002042440b5105002c03a40c0e40c1c643c0c845050004442400e18540d0b030001a0141510048070b10810f031441d614000e80c02031003205406000b191410001009000301c4080000490f0b003081240014030340d44000700e0304504003e004040c010780082004010300118030302d1003c44100010402c121240d40c844074041d040c7e20503800350601d04080015150b00140601c5403a00500c001d4000d10314010380344d4002a00d901c0e2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 382054388 1250 382053138 382053169
    0xc0312100608061f0f020c04090503030603010606030c02060a0209040b04050411180106020a0206030a090b13150b090103060218040222080c030d1d03010203010609030209090a080d0b030f010207121706 88
    0x15009002100f00d0b2081010847e5603202400c10002e450003030816a449600c02c42e480b9010f90f003407050029840d48241700301710000d000d03580075100035140c81035048c01940c010084079600030b0b191401607204c1d07034907403241c0f501940c030680c0d0301000d04582e4000d001c19030340c1801741c04848125680040003015000300d124826954100d924555039038840900e800100311108003c0d24400325401081800c0300e40c10000100580100c052401501e40d8500b004141c40d902b50358a900306800c6001000014007035005404101c0050141d0305c0e0184441011034200d8025081c8038040074000070346410340240c0c511075603016181d1940a0521a880d0401096440c40e401d5016000c01c049000490050002c404c1d03980e40d840c0c4001d000355600e50350741e44000c200d90b0860109034030a4030402e002c030f001c44c03030001811000c0a50080000f402c1500000c0c1030401801586070840d0036015020a1180140d020310080c840355129402c07107011100741d070038000c3c981e51303800e241d90180d40e100c5002d024183c2c0c2d864a08041c3c414 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 382055638 1250 382054388 382054397
    0x50105060d200406261e04060902040e030a11011b0f050d09050d270320220b060c1f1107060e0f03070213020c0312100608061f 56
    0x10500d140b210004101da06440828201050108085901501d2171044108440d1407841c0e044a185101034000c03020b851042110207440015a0381a03100300c2200e07030190040c3c4001600c40f2031500030034103a440c1c0304c22160b60780c1c00000c0d1901c40d076a0020301e0700c1c0240042030004c000c5d0b0001d079a144041035500c0721521080c4030500e031a6003031303040c8598111100c50041c200d0520000001c0e1501e01d40c3d40c052a0201c81c08114540e100411100d0900c0d0880000384281c50007611003451a00c41e42c4040c01402490282c50150792100703c01900c41004400c010003c02040c0110440c0074607840701154564500d40b480b400080150006101e400141d8810444000c01910782c00751ba848110001060b402d8550701441e04041484014041594003000b485084241a04c8801031002c50560b12032294400080d0700c401d103401407d000c1011a400750402c01d95580840c0e01c1d00c0400508103410322401c075042140584030081c01d10100380e00482660700000c0917240441d034000343c102c011020002a440000820 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 382056888 1250 382055638 382055651
    0x20a0615050a080c13140714040902040b070507120210110a0210030b04270308090705120d0e01180e040c0b030a0f05090607020303181606050301140103050105060d 72
    0x180c44400140001000c00c1d02d42c41e568450b054403040d207905043e200b880110003050052400d40981c05418013a5400b812142d0b90b4804191880d035800d074124207465100b4040030510309101d20003000904040285a502c13040c0618046107000d880d0340140c000f80140038014070050b1900036026000c0c40d01c42c200a4024042c1c03e042e03500d098600c1340c0196200d600c001d00d8404072601548100341603541514140008004407005102106585400540008454880c00d021074400c0143c10780001d00c2400342c4442c01c0c0d440002503d898030100110282d5005600e42d015010341125070340d11a8102800c2c4a0004424800b40400c2d240980c4210520f644200c170000d4104072070b111460002e070454130566900c90070702c1c2d1500c0c401030040b81c802c2c16084c0d2030302c4080380d4030500000d406803055242e40e00440c515902e1461080386503805420241c030910a00f0700320707564901c01c80c1c6080701906a5a807840d0b20381d80340044a686800347c641c0514107140ca018014889900c600d000c6480282d4409004500c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 382058138 1250 382056888 382056911
    0x9060e060907020f060a02040513060f09020c03120114030d030507080a020901020a020307182304110a080303040b0403090e090a08030c0f0301090f0e1606033902120901020a06 77
    0x3081300c12442003082e800f4030410030079401c0483c1e01600554005941c00b05c254031702c070007401040703e0f164003a0010500b0801c908100008443d0000d0440032803907000e4a06010b40c0758501410050203030402d40880f5007040d01000f43d4141000340245404262406000c18100b042e4041d048410260444402c160000707801820350340200425520144e003e002c407080640d40d84d4944045200c90403100038000d0070000440700c152039882100c0b43e10030902c03e41120039291580c41071641410441c1c1c4540029200390001400342c000d2018512031402054140824034061600038000902c0c1d8202410130a0207006000b96240d000801080c0c607507104480f5566900c840c1c034000075034052003803c04070314040040013041406058111010040035410240140e40d00282d80a44400d0844010030303185148190410240340709800c059014a4a94a070204013a2905402c80c0900074660103100c07c4242c800d01140003a9041140c49c3c000c18500c40310500303000307400e00000d489000c84c000151209e51240c420051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 382059388 1250 382058138 382058143
    0x9150609040c15080105130917070c0b0d020702010206160807080901020c12070203011a1f0507120c0512040b0d151508010e0f04020f0d061b1809060e06090702 70
    0x1a100c1803032000b04203d2000f9006284010074014a030250700100d000303081d5080607000b4010210350001c45403542c400040340342c42c0b01c0e0b000f07010165122040c2c400300003101e01440000f0f000c20502e01f000035940310500d000281c90110081e000c101c910300c4032008424080e038803504036a004025403406c80a2921441011806406005072549590181000d08005002840300909441d4030980082c800c485c104074401001e0100e070345010760008000305c40c0c5051078190741e007150790000d05400d00504103003840d100e802424001240e00340110b600000c152040c03100c10411143c50124041c040762405003020b528040c580a40303000b144004d5110180c244107024840d40000103429100c40c14034101200c61170003049202e0a12a10f83d10710030343c2e40031622049011210a00c1150068280c030002c80d616001e01100f03400002090790965035405000020203048140d40c0100032440e6140141c00840651402c25411207600c5002d0310703840c00074100f200d45070ad8078001e80d1103102218051016614810160b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 382060638 1250 382059388 382059413
    0x3090920030a0c0233151f02010621060b030a02010f0c0201090b030903040303090905011d04050a0b0c0c0c030f2e021c0f0b0102100203072a0203060915060904 70
    0x4101080b4140496980c5a40a00030040001706030307024158665001c410b0341c00e249800c1003078100d4910329084004c61441c4414002000051000182c1c190b50b03054400c856442801d140c46513110340000c61410301045001d18241050b00300e02400c980c50765540040e0050400d4491002070044032100d071000d6a004403460402070440f010358980c3e80c90241f8a05859510a0000b00d0120b01e0072580031407011068071480e0b058400d03421159118440c10021440c41c0840103008803641c0c85034582d900000380c41000b400d0f0107402c004500b0703900c8402d9090250f041101c80a0141d010358481008482c05020000b11540c2c0d40640648000d018040707080450162151110198072842c000520100140d050764603210000b024103004205103002ca00300402502c100c1d1100c2c9005901c119a80d81000e055603004603040b10050030480c00150140381604030150030088d4096022080047e41400d50a0038003032941d0100c600c0700500881c0f01c0034035030340f54004006001030303020340c0c0c2690004042046c0300340e900c1d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 382061888 1250 382060638 382060663
    0x41a010f2604080306030712050703080f0d0e1f0b0108010b1e0313020906010f050a30060e0f0c0301230d120f020105070e0402180d03090920030a0c02 66
    0x1036030310b4501401c290440b40c0c4181ca1850081c4121400043c5010602d0000c0c0602c550000c043d1401d0713813640d1101e445580152408008c1d4500400c4614500c030380e00d21820710139200c0320000d44026841d40d8000300071181f080502240032400c0540545081e0b9000d0380c900c0c15a410709801c162640f001100c45941d410090711664840c04001090082500742199420341c545e2003126005000c0d91880300450b40c807441120f102003c0740e4248415203030a401980c4020100030171a15141d41317030406174074040540719420f13010200c0e107595801c00c0c01010500c2c03102d680d12030a180780c84500390502c001c1c4040e6a110500c1240320004a1119400d5101e41c0400c002c51407203402001c1c0d5031070080e40d040c005040b21050181c440480c081d5400003102c2030041c01414170401c0e558485038448241482070001075448241007900312007641c3c01d001c2c99692550188a50140295100c0c9500307814070314200211900c1c4a043d803100f0000032903e0045011074002c5036801031040102160090004105030700c0e02c00c02d090030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 382063138 1250 382061888 382061957
    0x3030e010204052206080a0308070804020117010f030b090a02010c14010204050901150806010c0c05010c03050c01090c08121c02091906080702010c110703030c051c080402041a010f 79
    0x110b880c1c0707058003130540c20103424074902041071654850410b030341c3d02e000250090104115000040d1414000c0c0307062a070141c0103052034401d545500b10310781d1700d07120241c01030440c280c0c180c0000c0c400d0245101445601403154002080036076804d80001e009200c0320341000b4400040e100e000040c280303003901542c1c0180f034041c0c410a45941c45101c08561044030500100008410f000003411940c451614864032a4100544050f580c0c00c0400443c2c40003c00c2d8410713414401300f00000351100c0800d108180c026400784c41a4498181002007031814510038034859000e0307003024000070821603803480c4040b054000034000140c5e9154a07101080400884110800e000c0095410004d41d458025001d24403420095008001907030800c42c0a690200c3c16132005240c9a10541c801c2c00020301540380c0585e81d80c040e034210f136005003158500c10982c1c0052000240000c3c1c5510510007107007400c1c0a070b010b102402050412043c000240000d04140748402c0c0784017080ba1070105032151041e0300b07274207562100740002d6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 382064388 1250 382063138 382063159
    0x13050f0a0b071b23010201022a010b03190203061b030a02091318060501060c0b010302210d031a1002030d090c051512060d020a0b0306030312011e0f06020a03030e01020405 75
    0x5819100c00c04d4040c90224022542d5682241036106100300d8002901c1c1d104a602c80da242c005c8550f110300c0920440348000d6689090344a1796a404000c2544510548c4000c041086440c0c030500d820174034040c000110381c400902c0581c08000c4080d003660b5000b00c0c0c4200043c0c96600040008081c2003448028804140c03404800009551420940e00e0702d0600031403090203103984e101800ca821944880b800f51240144070010b100510340202030307a210491056a0041020660a0041c10300c21100b0310f00c03001c80d686000c0c0100c1c540189107070312086101240c03880d0f010001c07640041c0d1684a100540b0749904e0343c0d5880321082044500641d005800c0103001005c00c885101080c8910768032090842103c1c40007000041c8803850203404400005502402071000545010709040c41034102405141d85800180b080c1d078201d840b4000c9641c002c100042d405600341010f0051014401119040064034128291040c04140c0e00011209601c2d0750620b800a4502c01082c4940d0081c09070340c0110f036101c40002e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 382065638 1250 382064388 382064399
    0x2060c0c1615140315040908090619090503010b0603041e0804080d021b03030405010c0305040806040b060f01030510140114040b041a16021c0605040813050f0a0b071b 73
    0xc58100d0075280c4805803020701c2c1d0f404108043c00201d680122946103031a0040007828141c02900b41e070f40c422508035060202d21000520941c0206440682c02c00070007078006440e6511495810090005800820508580350046032462000910141c1003800056440341f140310b2180102d401ca5030404940f985480d2502d140f03580b10000b0040490040c8580c3e20b40d0300555407007d004204656005000314941454100103403040200400143c05009090000181c441030030720460b88520300c41c0d031507000380e45401001c02074440300d9000a18101841d04c01001059206600071030142ca04070300100401010090040341d109034024004d054541c00481c0025034000340102030000e0703488003580c4980b0b44044d140790300220300032801c048010b141b030350f1190000740c1414600c032030881d403000d039090078041038513124001540c40c140c50442d041c5400144030948000c0303001403c806045d00f00c41e4a40a10003c0000825440003400b91400c80c0200160320700410030321100c072003581890300b4408070341207036940f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 382066888 1250 382065638 382065659
    0x412111c050f0c0604050307090e03130e06100309050a0204201909050907090614040801090b01030c1401080c0306041805070e0f07050a1809021611010f02060c0c16 72
    0x6204000c1c0c4100b02e004503c2d45400e82c00d95040d40c4d03016004207d85440e242d10180034203100e603000b411a020070040034607088042100803015140c1314810b40820f081c00d2041c81401c0e044111440101071130b00c2c402200148001c1070701500182c040301c01040741052824440c080f001040003250010900080a6004a2004000c0a90404981c8038040500d84c1c4809015030b84008862180001d80d1418041c070220340102560007464407910001c9041c03584900c24203086500b0340906035244240c0c08010020450340c03041840c041c110950400740d00020010000c1c0c940e4001a100411807140440041c1642d115035006584c0722104800c42401c0310103c0c1070840d00c0e09205c0c05400c1c0f603104000000b5100301c40340004940591071640e1282d28002070180c04440908400300c8100310600106000100200300f8009040d025440200450703a0350081e01d0441d20100030f0385507145c18031001807048001d5a03000b040032a488464109440c0e176442c3c01c03640003420100b2200b501030215600546c04510b51889 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 382068138 1250 382066888 382066903
    0x170114100c0201031d1f0c020303012304022206050901021906090503070b0106030c02030405091807030c2d0b0405010c0804030203100203090c0414060111070e0406090b07050412111c05 81
    0xc4954003001200006c0080152051001044e015a10030001000b6503854002032010701c01c4101079480d0f640c030f0800001001e0382d01081c5c4c2000c11660242424024000c060342020003080241070007442e01c036003100041d440e2030301e5441e44094041503503070322024019603030441150f060380502501d46c0c0c0e201603d010070340381500f070064200080c98080700c042203d00000468003981c200802d0240c265489500c14400303000e00000f002e146001e900b0000000071480228680030f4440d0004c0b401e1a08001b44011004d0081100f200300c07240c1c22001e007000320301da2003002c550640740c00b03190109038485030382080c0c009442a940300942600c1100e8040b02d440302590301440c01945407006441410f03a02008100941e03201c00e5022094050842c081403180d0301940340b1044202119050380d041c1c6680b20042c0074110720899068400350f0f1141100410840c0715075504d1361090240c00e16504041c14203182200ca103c0e01d000042022464104030b00040e60744609043d0469003070b012000c1c40940c00e10b069230321480c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 382069388 1250 382068138 382068163
    0x12080c06070305010e04060b0609090403090503160b03150a0b0301030321090525030b012c0907061409040f090b01050105070305180d050a03170114100c0201031d 71
    0xc503008240341034842d0080038100c500c486110b01d05034942d611042d000340503030001c0e5a03000c6000c100c080d003540c642150441c412070098880c9002e9030700d40010302d8205a41c400701144810f0008006000100c04142070f80e40188200e840329015902c0800440e40a02003a005040b003000d021000204141c1e01614404ea0502c0007010340356041c420040c00000e540c1071140040c0590005801051080d00d00e2120b11401812042170402e100d58035161081001020313080380c0d481552040340305c00030790720362000031b00e010421088a00382403504142c01901d50001d80100d5082103455003940c400c101e51481651402c0070001d208202640250350750701d0040c10a00400c4811804100000030198040c030242d40700140c00d80c842601c1c0c44500d0b40311180b0300300d2901119510500e104900c00c0802c8040000320781c228440c5d103d0185409401300c0c5000c82e20016030081e50080c1e203000700c8422540356040840606403460924400740056072006130054180d0240401100e8800601d0144485e80091001c03c0851b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 382070638 1250 382069388 382069393
    0xc020603090607031802030a060c09051302072a0b03090a0803090109020103060503120d0504020411160b16120903120e0d03050c030708061e0409110f090105011409010912080c 77
    0x41c0175040b0b00194080c2508081d515400042a110100f1603641110f481d07050240740c0105040d403284001004002404580340c0e03010f501258000030015174100644550850007484111125007190092851000340036070070300d852001c004140502010000f200719240c3c82020652286014034032a8003c00d0517403001d03400241400c1c0700045a06000c07508001000241d0f00741c5140100e100c1000c0c0c041c1c00302410490b00b19542d110003e90000801c8098460000c6070500040c800080d8248598900400361400d442103010107545541c4603001010240520002000070038a12000c0c1425152603e04006001c1e10900701100d404000c4004030741d129003104d45440c06c00243d2564054000b5500040303c403880440c0301e150101d48140341100d00303041840510b594802e000302c0c2d000045800d44284000440b1038055030203104c980c52429040420b0012002d80311202c0a41c902000280b049900143d401905c0c400000c02c2c0c48142d1040c0240f00140c140c0c82e00340f4850806916101e80c590b40100c1b8111040d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 382071888 1250 382070638 382070651
    0x61b0605073b120a060203070c0c08010209030703020d060905070303021e01060e1b0403061103250c0b09070b0c06070806010c08091005071406010305190503040e06010c02060309060703 81
    0x80040624004040c03040d040c0d04100040d03005019141e1004440203180d4130031a226400024254001544030b2051580e4484920383c0602c0e00000c2072507035801c4189142d005204c44c0d0000d40300001e280382240d40407110b00030b040145c2c1c200603005200a840c05080d40c0640c0502105040d000901747c00100980342043d00e4a0314100403460803074600c2c0c010a0b400303040c0080480d035021000c014044c041c0700c2c508209417802e566642e440007204c0100e0100d4504030408010070841c041510000c102c80500006003030041c020301d180081c642484c00c1c0004000401e0140440e80c018070811a00c8040c02d813480e9001d0b655014040c242d0b649640446218000ad051180000c00c01d5104901c00398480b507100d0485420041c0340c40c20040052442000076003049018004140403454142440c07a007191204041c041c3c80d41141045400d0040105001403814404141da600260000040710b040322208952140c030760b1202401250502c01000f0041d5001e800031060103000e51001c80c145026815949080002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 382073138 1250 382071888 382071947
    0x6010e03190213061805010f060807020d140d0e0a060e010b060d020c031e0a023d020417060906060a05010c03120b03010f0618060807061b060507 64
    0x100c103040d0075a881e6040207041e4850040c140710351500c070000007905001c80c06030b8541a000c0c140000400d803081195859100403c01c2c020100142d001803d001e24242060349014038000c1d43c0d40529103061030801c148107900164038030440d0306a4103804150322007800050700e00c0c0905592080403000c2521301c1403415040580c06001481703400b11802c07018010a0508100000e200b0080d00b0000e142c0c060b034003040151241407001552880614048240d40546420403007900a02e813850304040f5514042d8803000701881c0d020426284081c0041024060010b400e09a1076600a07000e10b0b4040d51210601e40480c041c00c9402044c042e1041d201c0c2002c9504940c0d4580400005000c944641030219500d400e045001c00d105118a01030414110b60104d030005030400840d00b1100c25407001101035694080512081c41c40300004c0c0e254003003240c82032208a08004c20261900d0700c1e8894a41880b50f05081d50100c0c40d0b00c0e220b440c2c629508840b0800c020301d00000080c00358000d120310490040b8031240c16281 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 382074388 1250 382073138 382073143
    0x30e01020a031a10020a030c0311161d01050616020a05030303040602070203060709210203010e060103051f0b180402150f0912241e15040510030f03080606070b040b06010e03 76
    0x14800360317a00134010074032180c42c103440d40034180006800304032060707a8450b00d1403404c01404640c1c410450607010350501e001e04d10300f07120081f00303d2a6420441e410040003540d0310202602c5070001d136031000c010007040520004040a1a80d405140c15001c0442000248041b6a002e402d405000b50144c64440e5942d417001c0746c580003140548000507684a030070fa0000c100d40e04c0c120172401e202400004094040100c4a4a00602684121050f6100e4039200e00000800b60340d520f42d900901c1e03000d219202800c0005821918505d100e01000c40c1c2c1d40d00007605650315506615960004600115599003014038030070600d91110743c00e203014400750040e200c00703400c1c005107136003150004c000000c5da044220050524501c2018089620103250000c825999000c5800614003403e0380f00c40c00900072002100b1701c02620401001d80e401d40751001800c0000c511000c5540c0300a907450711b403a080e01d980340c07000140c1030700820380f01802d10004182080300300210034030118010300090300e036080c005071544205035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 382075638 1250 382074388 382074409
    0xd1e06060b0405041d06010e0a090807140d09050a0b03040c180f0b01170613060b160c06020304030804060f0909060b1e0306030c0108150d0b0f0c0301030b060d03030e01020a031a 78
    0x240b031b80c4220010000b245000301c010b41c102d07080040c08a5130440c1d0ba201e02146c1c0c0c01a40d03080c0ea111180010b10051018104842071003500c4604049900e80d280500083d0780e1003281c0700320b00800c070001000a040155039150342e40541a8015804082c18610350800c008222001c582c5c90510300d0b02e41c6d441a19030080000d090400c00f1014010281d540d148188600f05425955107089243c031150082540b01411025058603911700c0c440c8890300ca001d0030a145052102c3d400b0000b507400400080c004505031b20203c500350345e000d00b403001c456050030504a521048030f40c40541d41cac600c1c0080125040b4400001001403900d0784800205e0464000c0c0b03410100d01c0140e805580c035070b00031403c03a482035020700207456101c16501c0e5544541100040412074005036100210b422049007410002d071581140c0200340c1002c0103443e4a407c641c1140d840400000d0003401e40740c4140001c1c1529000c040c480c1d0402c04001b642040255103c507032102026000d0303c8000e4118032580c8250500e6400c9080c014240d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 382076888 1250 382075638 382075691
    0x12090b090f060d0b03062e060f050c0f120315100e040b030304170105090d0309030e0411072015091e06070b0412110604020d1e06060b040504 62
    0x181c0845140200441c1d580000c00c240865920341e00c401e8070540e13007888028030a1044d100503da00105c20b075001e030001907403000c16603102c8405400510000d80d21040d4442c0304041428195030318182c0b0700b40b6514010070070848071075038842e0342105641c032200080a103001d40c1607240c1808548100e0401c004c41211744044610004060200700c01161410760407041a00e4800307420b07a481c3c540c4490019212100030580300080e03070b440e0401e000c9401c2d8200698204400c00d440c04102e449000e035001040c1c1d032030005895110f07507100d40d074801405092600300d8107190b5110704801d040142500c980c0645c5401c01d0100340c842e085042c1c9031680c8442800444900420042c43c220502607102541a41c9503030090340550003140a02a000020729818402c500560240c8808038102000c0c02006280001143c0f03c00e20303176003000741800010b0b22600c80c1080c0d0141e0110103150302500f08459840c2d0444a050040c0545061002c00241902e040f002003007560002c1c0e03024029200041c00c40c0d8111000c0741940e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 382078138 1250 382076888 382076899
    0x110711011e201e0607090e1b2b0509070b12130203030d0218010e1003051b130f06050309031209120a03050f010f08100e030903010912090b09 62
    0xc911070588100300541035042e900080101c4441c5409819190005030716100d0700c043c150314040079009508001080e405003441ca80341c2074203810080015a1000090700c030644000d0000058584a0743c0315041e03c41155099505100015116078021101c04001014040c0303546007502050100c00c1c007254400503104414040c914198600c4144081d4107802014080052200c00100005a40a1009101c0c8000954016032030b072000381004060300c030f1910315550500c2049400084070752619000655480354509001805c0d668075040d18846224545180c0d603452800a402e40660150720741410607a45088442059180c84803410394641c4029110355040398818040c0c8400200700030340c0c1c140e00c9140e21040d01e451060082800c041500194448400b280c0c5403401c10828070448881580144091100d03030900c0c80c64440c400380c88000302003820201507207644035001041c1c010401c4454110000d40200081000c03800d00d100b0f0b00942c95405c500240580c480003c1441c42a82610300c903e200601c4d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 382079388 1250 382078138 382078187
    0x90b1f0509010b071514072d0c06050a0f020f04081002070503040519032024041401030204050d03021f02122206060602070f1212030207020a030611071101 68
    0x303075085e40c00c184134000c048540d1a49416080c200841c00494014010390f100c3e43c03812110fa4030794600028945c0c102e04000302c1c05038641d02e0103036880740c0401da4081d00060b0020301612894180030180c940783c040d25404a00001c0d00c50040140c2c03400070130898010360300383c40c980d10400c1102c0c4103034400c1c848050190b5000707010500043c50028a81380d001aa2005440310b5640d0301c2d07488036144c008a0390b90b2204040d0003044010142041655030340b0b480c03208480d80b08410510342111006000b03074040c18007101c2d04070b1000d00d22139000358119005003000915203440c003062454025503580c0904602d05170401c0200360300053b10000e0007694101e0440300002c2c10075a4801050648480c41c0c41c00c66100d2003521a150030100b10540303d104c003e0403c90b0301800c005420507004444901c61580549200c0000c07804803000720b807241080c1925500b892a0159540b8160b000003420b188090300003034000c0c0d19165001f0342003441c0700b00a100d000c2c4941050044492240010740d805038117020006c203060216031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 382080638 1250 382079388 382079393
    0xe01020405062a010509030306011b0c0b030601020a02031506040605150d0203070e0d0c030b07090b030f13050f0304050411040803030721060605030609221401090b1f0509010b07 78
    0x4103003c004180100c0e01e585a0036070114441c252401566125407d4200005010465030b20004030700f520081e015480c6045011980e8840201d039140c4100ca15944002c804503089a2080c46040c6840ea0020b04682022182a0401d814002d05994261080c4e2800c040004c05040464141c0c120b007401e4600c0350b0520b440c00030100040e40c0b00070841d07001c0201d00505c600d825500c0b00e11440c0203d00130344412420b142140b41552115501602500034407010000c100451400301080300c1e03000b807650410b144692034a42c0004080641880001c00c0c0c0d015001d5070203000c20001024001b03e5604a030b06005076040000d42d80c440e8132503406010700d290420400201264090310901c00c1d900d2030f885102001103004034a80c421280103404c1030700019400001d03c403540c070309482c6c9190040c224041102e0644039000e4000c25011015600820307114505800c40000402980144107840d00038011000d1071a004100203c3c02a010030348108072300c22800042020304062401c1410f07a001603603500c0c60b0004a8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 382081888 1250 382080638 382080667
    0xf23010e072a2618040b2110021c050c04050d06180501050c0403140102090a0e090304030b0a09050f0d02030a0c1b0905070215060306042a140102010e0102040506 71
    0x10041580e40b0140e054080340d800701e080c1640c0302c0e94003c1c1e500032501e40000d1100c03040b4804807040d13100e20950410700c8501e100c1e55412080300c0780440800c0d44803991071078141400e0070301040309002c0183c544081512224400c1d800f48400c90240340c24030820981d034421a5180d0680034038010b094002409080003000540c071903100e9084402d0307010303240843c0c8800340e50389800d45d4400c607903c001c1c5030004a01001040300541c0c5103800303043d201e4000c3d03040c003030f01e200403c290303541a00c0f07502d002640701c001007010420b0a0084401035508046803401c02d28007807040d28081c09654204a90030b120303505040742510300201d81d4207001d21441e03002d03524201c14900308840c0f41641c641c0544401d1050090340b5101b0050240031001440c6030750011941380340203440641071200302c0c0c400d00303801d640080c100103140d60041500f40d030056100c1000b6071440800090b035811031002094600129000c00d40200c1c500120110000640313030268028441da40c26110390a090380518820550041c1c0140700000da91042c6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 382083138 1250 382081888 382081967
    0x30708090102160803190314060d210305100b03090706111006030507090e0a0803060607111810141c02010c080414041508100f23010e07 60
    0x140b04403055400000e1068480c0c121070713032103092598000218000403c1d065024121400118203041080350401700c031071244420002d0055201d44d036011001c0040000b0030142c040c010b0005001154010392891015000708806d4581d8892044141c3c800510214800c0850344500b060101074200a80b500e24103451801e2100c82094039070060040014800d54140b08440080d0f01980060900e5440d0030300140840300c0852011900b0b80044c3c0901021070b4001080b40d410503030640b00d40d42d58049600b4200160149080308c1c9a2184490064220400300c079090300f80a0701388810b11018507a03035800103000100c90025000c0e0001c00720920407003080b150700c540108850060400d1010383ca42540c40114a900940080c40c100803500203408032800d1a02c10b51031280c10700701c2c0302c2034981d0800c1d0740c20b56101071102c155144607441d02400505c11301c298110f10620942005c8824203821000d000491005090080b0484800b07000d002403501440741485814400c1c03040440d504107251900b03003100c1c03100c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 382084388 1250 382083138 382083157
    0x11220509160f20010921020a0c0608060103060506030103050c01110c100804050a0c060c03020106050d03080a0b030a050f031b070f03080a02190807060e150a1e0e010510060908030708 80
    0x9032000d14100b80b1000e000340351200c1d10035406d04062001000c55210f240034890031200441d84404071107030001d82c400210390181c500b41d04111360f41e5503038400124050700c40780d04200c1e04070801000010401000140c1da020300503090720750070303018001442c99070707540c031401440c1548c04605140d2841c100c0d405417016a4100e4020000d07102402013075214a074008550b03902140c0090000c40146090540c213200e05400303040c0482d00c02c010490715071402458400050140300d00741d5078450101c005650200640b000590f0b02c00191890140003c1e00386889800c03410504070101c5601006204900700401e44009560b0450300c07400300c042c03c0d6112442e07560042c01c03c40301540f040c51303a0322008040c6556452002d03031140495999941d100c0c079040066910035600b9005607801020321140601d60540392950000c055140029441c050040d01592100784c140c001190502e04100b40001c1c09045d040103106482d1501141c43c201d94808d8100c1e0031020609c00c25100350003d02c02c280011304000d005050491 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 382085638 1250 382084388 382084427
    0x15111005101205101b121415030a0c030b0a0b09010308040b0c030d060b1b011401170c09181509060c090d02091e010609051311220509160f 61
    0x300c6910100c42c01100788500c0c1c1c42c1007071740301c00d1010f5201000c0c4208454400c0300384100000c006071400f8051024150388082c000764070202101e600c04000c4020318a42100780c00c00566aa414640b011480070f0344d02419107410f01c01100b00034206100b0140c12a90301c811500d02c0e180c0381c600c41410f56009411002101c2c0020062043c09100a00030b54001d0242c54904558640343c0346180c1030f02605503d040d85403641860680e141d14003c00d9041ca0455401c94004610102c0c0188010f003481660301d180c5a0110344202403118040000c001c3c02c074085c4036002240c9d02c1101102e950300905e4012209602a50b000d10001000c8034041c0019000c401000740904511800d0faa0018031810f10442e502d10050200300050052942602c2c4160b00501c1103040c030805141c145001704c2c01072101400300036460f0f512520602d07031020400302180c05c188440e00003c40610008013945000106c0c80c07141d00e104058000c0411200100303040040e007000350a407541045101d0102040d030310341c0b040341c135440420b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 382086888 1250 382085638 382085653
    0x3040b0f0405130608010b0f010c120203040815040516080a03050d06120311010524010c080d06030305130803040e13050a05010216030305182515111005101205 70
    0x40c0c4030f10740403806503180542c0104030a400d040506003190b0002c02d07185d2240102081e01c48031a60010051a4000c0d006550300c409000780b03130000c0e480e51040307502501551081c0784070105188507500556019a1181081e2001081000a814000d03e00c50180341490b400c40218000001e024000500050f111040c0200c2c0a55a42c643c041c1c0c003114102044e40818184400350710034020030312419034000c40b18402400c4062140303800c0342c040c0192040280c140401d04d600d0b4028403c6510940d4100e810306001441025164030b4018450703000701d8121110740e140804042070400c0c011043c2c4054560b80900d0840ca41e65131700300da0000041d1513005450900074121448017203003080c0010541c0b0700400d02c42e50071540c030780d00d8003d00300c500080015501c13220006000c018040007003501001011114603080181300144000c034002c510b40c2d4090003954000c1404a800c00748c000c07000c182e1248101045d0703a10000308451403070503114210390012a5000e0400709202040d080841080800c0c050f0046600c0c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 382088138 1250 382086888 382086899
    0xb0309010b0a030606050111060403050a05090f0a0f0303080901060503100c0e09010e240d03030e0f15040c0e13030f0903021815011b030c020609130b030115030503040b0f04 76
    0x4074100b541068070101e80700c04c8140304650f04000225100c4440400802040c6010b4400601b11701031002c1d010204480000d900f08143d03141804c90015000c000c002c00400f0f55a103440f80d44001540c8403c5022803d1000000c122032410310581c4220764014001e0459078031030007000c0e00100102c003900303000d0003000000b8a0880c0c499115a60181c0380132416030f0303024240b5903c100a20907600c0400c03904444912140b4525442d07030b40350a03511a906080100b400f00b8036040290401c1d41210243c0005d10070203006c0d6206004015100c1c0c007443c0907081c0314540c9621001d049000c0d400845050310804a00da404500191040c542443c1c0591145880c0110743e4480d80060310309600300a0f1441042d20000a010521381200d650403500c1d0000d090030742240c0e0a1103541482010400000b400b0f0004060f0624299110042114441c141c020030840e080111f01c2c00305801003075040203c0b4025840d20700d40d2a0301c0d2001030608420380c0e401c4070040d03041502c1c11688031456480320310761000440061000285 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 382089388 1250 382088138 382088149
    0x8030c0d020310060e040b0616170f07060f092f0303130e01080d080a090303020712020618160e10030212030a0212071a07020a0c060f08060603010f0b0309010b 70
    0x24400f901c000140c0d540c9840e8004081503101c4501600c1540713084080d400c50343d00c2c10112070051007404401100d840c0242803c008403844080442e400b00720010f0740c0685003548100410034107101d40402c11007500c0d048080b40c12140b00f6400140400000090440e1141d07480d6200d0401c1c3c003840c601014240c003c1004a13066030880c0b119520400c000305405c0c00084264007a41d03000d040310b03400400c00a50819002098000060501c0f037542d83e403100c18800740b51007901182c46c80c40d00101d00c4220000d00000007982c070072088038a82186141c014001007080c1000c1101c120511110300125003541c1000114890444090485520000710034170000c010f07240d51004a03d20441d940c059511480050340203810020302c0e10061406803010481500003481d1b41100c8078030381c0c2c0c0341a18011141d4510900760300d0300a04803809803005042800018400e41d01006803000307101d03241ea90f541540c80c0d11003170220b0307404280a840c04461081d8002e02c101031030074014690046020380003190845071a40441c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 382090638 1250 382089388 382089391
    0x60307050a060e01080a150b0708070b040b0a0e120d020903010e07030b1905061c02030c130515180604090507031a10140108040b07090801020414040507020706090308030c0d0203 78
    0x1012640c040320103207542d0717000540181c0c4907489a20a00140c01100c035060b400c460a0b0081c460342c42d10200701103040c0110781c1d094070007070b035404440d0741003500345801d009901503012251506558201140c041e49100f020454800034650f407004942002440310500e0043e40284440315010341d6100085180c2220070052500110302940107000c4500b002000705103d00c3d400b01074000d642d4100402d021040d2a6035182400c2c04080010341c1455100520009003032011030650140e1203070b4601e10349000b103d85980030724040c3c072001f00180020201e000074056440110341104010281c0c4d0800217589080981107001c456118200b501c40180d00c1c2e503640103104c2c0c82044400840d00d4000c003004248101505408090102c1001200c0307000e64030300c0001c240c0200104010510240c4402049c80740d400f9075400000f5000b00e000030b649840d03d4903545070f01511104a1036201c1c071b0800c00400c40c0c45002240810960f061650b40100743c6081d612110055030000c0d0130b080851030108101024608184003a6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 382091888 1250 382090638 382090649
    0x922020702010f141603050906031501030501052215120f02011b0213110c01020c0a0506070809060c250f02030705030d05041412030f041706010f050405060307050a 72
    0x1612280c89000040c08504140015030030311081441500d0300c0c0307940d00e0945544410440d10a8191281441c080760301d4041d4009450f0000b9000c030a203c0b40450040c480380a03800207a034104010303030f641d404005048080307404c0900b1001410703400106202881e0888103a9001080c0c0c1410030641d41d40c03000d000d541c0d80340740544811000314014030031582d0040c50507514000c03081600384841c2c501d800080c040140302c02446503941da58107015010702d02d101e060341d004c1d8070040001c544030b00780143d842d62a164021011685402804009070005d400303094206d00a039015002400c0940e5103a0090342d0962101036561582c1c001108664001c02c48524104c2c203291103441c00c400c0403010740c07040c54901034498100c5407203600a0700620152540c0002500c8c2106e1880c50140c1548400b0404564003401c04909410350b0301000601240d0100a10010011100084880c0c3c4480343d00484864542c0002c0c020704201c81c5c1c800c4010490f615260f000a80c011100500351510950f45800040c01020950301a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 382093138 1250 382091888 382091891
    0x71b05060f18060f03160905030d02070303030f050702071a0f041202091605030619080604050102030105010807030e1009021305160e010504030c17030c0102030c1308031e0922 77
    0x1049054145000202c41880064900030b04211901c500390810f4040100310000c40030064910f0540248110742d41001040044c054a64000036048001e4a908043c0020780100741400050082800b492041d244107100aa014207103c3e424001400007060640b10040c0d11035009010030700d40c00e40c090008000521400d4244d4846070101d1042c000000001068030340801140320a196617150041c045991011045483c0c211500c02d010315185c803411310b90402c114a200701401c0000704034056000b507050350004d80b074410050355611800c90603255200d4408210382c012201c1c2d1500e0302840d42002038548d02c018030075524950484001801c56900715082400d05403a04410009160850809280304400f03103020b80c03526045840e03090310310500cfc0c0b080300107a151088840308072080a1043d41d500b1064400255517900b4100200c11250f040300045a038503050304103000078500c1c000011115000d0441ca9510b04a002c0e6406808c4560402035100d030300407011810301b0005400101194401d000344040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 382094388 1250 382093138 382093147
    0xc03020406090b070c0911070618061b05070b060d12020d0801050604030c0b030924070f08040b0a05060604120c181416030221071202030705071b05060f 67
    0x80007440c004580e0701100f9107540403c203000114000301c603043e0540c0c5c050a004250b4009000c4401081e10a000028004524180008415503040d60034058030b00c0c01040180410721800741025600100c00313020b00c0100364200403801c0040c0139400b0803a4841c0f401085180030710525101c14002400341d0402d0f00044c0c00141c07034100b01d0380d0460340c0903005d42000e0300c4590400d8115030f0b810800b100c0c140110104124040006201514200100c01c0006010850140a0202d864540d0504a0240c40602c08165a504d07031480303541c0300d81046407282d40c221100c9640c03074448002d07850007003034040c1405811081c00c20020940620f403401141c14544291400504145000681009055040c141c2d01e0158201008419103a0022461603000201105003683c0320b034002005074002d2080c1100d81220b150002d2118007505140140103105039815214440c048414170004d10803480120343c814003058061004401082060032014414041c2c4803296204a44400010301c41d500181c0000940740300018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 382095638 1250 382094388 382094399
    0x3030403080705040f060327080703020c0102150403030c0207081c1209170a171003030f0f020718021308061803030907030206030901020d0515040b09010f17100c030204 74
    0x41e0345a80c4507140345002c608050404500200500b080e106000405403100c80f4800b41c50302c0d2401c0d8040d28450808201c04030703262032600700f000c0d400401d001d0307016014030003103442c003540082042c2121003c2804134140036920b95800350000c10304042c0c02c070118891600f010178005000c108600c00c1c00458036480c48005011040240440014041030a06a0030b0588880000d2091681901e00c580c0c140f20441e125000b1309000c445044442c1100504860a0002d1141100d44141060280d9019540e4010204c0c0141400d50729038241000340d100513800020704010002c2c5142003010700c40e03020341c80036281c040300c0083c00120040941056065400c00c80900140071400800c3c0301449110700050742c25480d080100310749503910341c40060300030f85c3c0000000d0103450342981142d04440072440d0410080c1050303541b00c400840001c2c2d65074000c907e0203c6c272000314501400700604032014100306107115414401d1008001c0c400400d1141b40c0c0c0700750310500f1100d40a80c0503d8030b0303031045039030016100e600c3c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 382096888 1250 382095638 382095647
    0x170a06050a080a0506010308090d060207030c03080f060f040209120303091e0d0e01050a090e07080406062907020102030c0a12120c05030417090301062706052211070503030403 77
    0xa6000e00b4456101202c0740000800c0451100d0449800c1800161564048000b040e030985c0081c42c001d10280c40054141c1c201a0042c5d08600010f00a564103c45681d48440312840340b142950b0251340300c0301d4402000d007503142ca0340050400350409055440300310030303510f180fa2843d081500d451556030002da4030207045072011a42d80e101c071092140181151054028041c22001c003030f21f10f95040050011301301152a018112000081c00080c0850075186094580180205819034085890300c0c14000c0c00600d0405e070f0a410140c1002d20801442e988d1609841404181d11905080381940014041d49194403014004a000c04e8044c55243c150b1150a01009041210240d002e510552411815401d602d50000136a603006a001c02d0901b41100701c4003081415004401c841c55043d0f00301080412144400c4a0089034640f4028100c038485c412600d101043d00c1c03490160b40d420011007283c6030450303081c68070440000240c00d0320004460040002080f040d5001c1c030000da407142c1c000800c1c4800c15602 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 382098138 1250 382096888 382096909
    0x9050901140705040e130f11031c020c0105210c04080105090a0c0302130603150b04060504142703030f0f0703090308010603090c050301050a0902090c1602040c170a0605 74
    0x88880030310341c624040c4005040c0340214020340b40006040d500103515254491800701105400055500c402c814919081030380c01d0400b2281b50107400f03010341484800b1f198101345014105290042d003c0c055803076004543d1900074a1130504441010246501c0c2401103a00c0d80740600011200d40381d846040c0000242503900203061400540d2052f400c3c100420501c05e03441098a034101c400030b43c04045940800040c003520340014040081c401503847c601c0c1190307801200311110035076090040b60b0b0381c0c0d002c120403a40050a80c800d9409107100244446418184400c100c250108201001001186503c2e155400c2240c8072888140365100b44281d640034000c2080e8400402e2406112500013aa00142120410b2280400b45600c503008242008280c4560300050310b00500208080e242180c00c2c00003800441c00280c2c06030b28101d01040d450700d03500c0120340341801048040411940a0744c2400014500c60340c120b0108028140070708450140282d507540545052100458070034200310410400418 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 382099388 1250 382098138 382098161
    0x512150c07050703030828051501020708060a021303061e0f0507020d0f0905030f0c090903130302130b0904062a020a0602031503030f040806060a03031b081309050901 73
    0x414820100014800250101901c0c0d162805080689601500300d07c2581e4805020720598a811340d0604a91025401644030701071405104001400240c010380e01c0d24000e020f030301c001c2c1e013040002911600d20781c0c000b03010142000101d03910b01d81e0703a074030341c0d001b202d265600c81c0d41d012800c2c0c3d014040024850203860007004482e54104194248818069075500501482105005d41d60844107081c03401190b00b000105030160694102c103c40071040d03910b81842180c40c502c646891004181000000019281c2086191200d00c02050442d001c000110034500d4248580503100c1008000310b0711900100d5006911a000104148801c054000306510701117148101c0c0740b8032460700d88070a690004407480203a0304580c005903641c54001c8032103c045ca080c0d000702d4161000103081c01c01081303040010030440340300c082515140d4a4842c00c024a4840d030748005000140100145400c2c081220380c4c1142041c803a81e06da44c074054844a05020303140e941c0d8419585160348808000c403041c402c3c006d8040401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 382100638 1250 382099388 382099411
    0x10e010f0606050307080601140408011b030b03070e0603010f0e010b0f011803020f0609100f0905100f030f0e010c0906090f052101020f03040c051009052107051215 72
    0x7820510000d220b0b00005000e80100403400c40404c00c02c0c0d01500345140c0310342750404026030380d64449003002d01918003c1165222101c0004050404902c6131046040a0700000d0240c811a40f41034aa440c20303c501505a984c15545c4900000140300c2c507100f0204030400c120004640c000b580c00402170400103503900a414422103c1d040c2002181544007003095a604a91050744042c900000c69143c1c0150f88400da0031030804481d000321650007043c161840d22481d580c86000317039261010702280480440c0030300c0105040303c1d40403a20a001f50010400802c80c0a0700007180c91140c0c1d034041c2990030b100c03040300101c0e11603201840003690151034031014007048004050316520b000c012a04030f8111403110780600510031101000e0080c01c0d0125540b201c0d10003060cd0300c03401c240c100561040310351b10400748111981e0003901403c6008400c4641141e000a1043cbc0d40810200c880d500c0502810000c07101500840d000405c280d0398a02a91451003001c100601c9401c04c10040020484406003400c00c250307 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 382101888 1250 382100638 382100651
    0x406090302060f010311060c010e0307260a051803030d140604110c0c010c0c030606090212150907230301150305010f08070513060929010f1b020a0f08010e010f 70
    0x2145200e40d54240c500c159516075888ca00e0442c240c1c014188100071850b10700000886030180410400c0700354034200c42c0801d040c2c0310a0120780503075040c4100c50400010030304c1800b2868080d007160201c05000d01d0050140c9140c00610340c0180b00710382c00320700100308900c103840502056040500c1542c0d003400c00b0901c080c1c54110003840d0705940f043c5880600381000a0716400100300242d0b040800015076002206000c0c9a45410610020390480c0c5042401400c00c140003c40703230608901d46584c00100a8180d88440d19121000c030307040c0b5109400d42c9550081d112900c0540343c0c1d400000c50007401c400030454258101c120001f0b05445042c7d016481050030014180a65000828a01d0403500110740304100c00701800003481c00f80066a00c900d50680c0740120203a511000f04030b1402e0710082c00b15a007110040840015900b40b8045844800003650350141c4040c42903032701d50b401c007541e40000c014804031070352030700000181003094020340350594441c0e6420140c0d22090150303034243d104c002000d020f00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 382103138 1250 382101888 382101893
    0x306060904020c1c020d0804020d0204090c0f151d0904061d06040203010612020a1509050607140c150f03060406080d1e05091302031008030d02070510020910080901140406090302060f0103 82
    0x510001900c0a480380ac4850320000455a40b9804460320030f50010316011360903070700c98070f4001401080c85650900c0300040b295120940c41480202d02207107200906003004807410090104400e030060040f1025603541c3d046d010022004140d814100300107000604203441e2070301c10701d400d40702680c1c0054141c00070b800102005a50352224141981c0d0781164028101c44400812075121100d540441d0700900c00040290500c400a8106014541200c040340c0500e0221170a22603412542c00c2c0c3c04001d0401408101d000b207100d8401541c10000050000c00c400703481c1d51040c0e0400f40030201d01c8011035505c9510492081820300c0040c48400181801400c4c1101540401c01c440c080402500d0382950000018103c0002001400301501c54030701203d4031500100c62403c000c0d4000001500c4911401821000380c141d14003c607401128060100000c1d0b002240007681d042030082d000706015500d56802e00c911030001070000340b065000300004160341c5490309010b0708146000c0c003112984499140140f02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 382104388 1250 382103138 382103147
    0xa0213080a02031c030612030809010c090509070302090402070c09021b0a02010e0d020d050a030f02010605040b180705070f120e010305091513051c020d020a170306060904020c1c020d 80
    0x440c400e0f0700c00e00c03c01031a4613080440041496800424241d4811076842081c90b50103026030b4131030240c074802084800f041e92410383d11740107203205040d8007000820020348100c1c4650064804044041c01c05401c1400c250b448584160064200407001d40d804641443c4491484d94080e40040c1400090101603019800003880750346140c0d1030600130340c0c00400f03900442d16035142146103960880f09a1300700701058680146025003201c6020015820301304045598038091040f8004408010604864400261000880c000700140507905005d0280b00d0328000c14180c5c07180313138a4180b0402401e10707100322214002c0c0105194242190401d40303030a0411141c80700c0081d80d002c0540226440c1005651406d01820b2091201c0700028014011180c095100c3c40b60304401c2c2001c0480c640035110380714482007049030341e5104140043d0202c0c407401c00c03000c501c441c0880203540101020b04007910740100b040100b4103a0b401848405d445038010703454040c1031a0b55001d141c84030122480503190115030030780005c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 382105638 1250 382104388 382104403
    0x21020a0e0c040b03181f0c021b10170411012303040b10080a061a0616170409111e090f010806040f051f06050a05030f100e0a0213080a0203 61
    0x8400004500e1040c17032000307141103c1e0310002c1103401c04441207031590702c204060b422161009081600c8842007078000305050311998001284c1d01e8130301c040780d0100810004000d900b401808143d080c113255204d007007044c50784560301582542c502d40030b041000600b102d00304044810082460381c101400c140229040300d0b0010b80000101083d601c0c1d4143c2040401071503801000c0620070000310904200b03442c3c211082c51075402d40b24900100d5331105100051051321010000100c0985000000403401d844005168a54080d66404c0c140c40c0e084601c201d03035048842058000d8041109416819211030740321301c4204882000342440b9440000c240c1d00710000210340d044c029943c00150b91503e071a031260030340900743c02e030500441c00e108510075480c828100e407064003003e9290300814500e001e4401c540e2021035175951280381d0354600304601100640645140e010802ca540d00007900c55940700c58a000c1c021403d0010f941e07000701d01186905074960307805000290851038402025940200d00c12 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 382106888 1250 382105638 382105649
    0x1503010e090d080c07060f020d090209010909030e01111f0920031c170f01060f021903030506010509040501170c0312070602070c030b04030e090a0e060606090a21020a0e0c04 76
    0x29501c070300141c0303045000f80c41f013400f40c140e803948045501440801150402015a8000d0f2400d140d680d0f00c0c0c0c818801070350044d01c0c000d0080f070040c00c41c0e401194800e4a8040c1d2214001d01a607805d41070000c110240e15510300159a25552103642050a2100e40b514038441c0c0c402004550003111581004252140100d40000c0340040100040c1c07403555000f4400310b001d0150004050680c1c0c0381040507206465805c0c040e00c00060020442c1018842c000580c414059100e009264082c12095608402500c8006c0c102c0d81042424800c5896940f5140601070180842c011400303000300420880c24070303050203a00240e100368480500b02c1080302d852800c9a100c0c0c1c5c0c0102000d81c0c1c075041e604042d2748031001c5500043c001d1602000300001e042d030201800d5840a0100d44000c0c0c1910344090303110a40d0038550904880340c106c0c102150a5251540c000d0221000142c07225030582d543c1c1503440c6e04d0b400542201c0400b0404400480c04500c2c10400c8000030b004001c002280d0740c00d082d1000040e0380030b6030245 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 382108138 1250 382106888 382106911
    0x181a10080402012118030e010216050d111201240b041415070305040501031401050f310e06100b120a1415010e2b0807021503010e090d08 60
    0x110004548550904c540003007030001d05215220014440310161404c000c2c0580c0000c2d0102d50070509584040751080d40c200f1091041e058990501c01040030401c0c8045080f600e0401005110a503500d540ea0f5a5180c0f00009000080e9184648802c58441c00301a40d00c060039445964180700081003801520b0559200305825152101d2030310229500d143d0103080110304c440d01145640c109548030000704107560086e038040c4540b0000044801d041102030140c1640940c4024013985581031070440b00070801500e43e01c071320307203415403d008410414125a100c2e0031a6200c0d6000c140c2d56500f00710203038109803e41c6046a030755140803a0703080140079040070011010001c20204401007403507002144140c2e03a46620090034281403110f4242e01c0184603140340440c0040e0760005013880c1011219000001d540500321000c0c4c0204030162294010b1001101e80003014050b10700036885900b000c91500c3c2d04c0d01803a6a595043c108007101c452401442c5001c2c50b80120b20554070290701000b820340040d2508030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 382109388 1250 382108138 382108157
    0xf0503040f0503041e0602010203040c030f03120f0b090f0f0711101e1803080106030207032001020a080a090309050f1815040e01090506150307181a1008040201 70
    0x107000800c004004006007680c4804030303001c2501031001c411075805c4e0429103040440141d40709800c1c0e090340002c4401611012a990302040440c05282c0c1c2140294800d2402d00f1000500c2c841c1c100071903020750442d481035607031015207115504046801c0390f000390040044002c2840c00c0056002c110720020800c0c0200590402d020500c41010400850503854070141440720145c5c00c0f42c076603150101d0b03190004419003804560201140303426002c0381069050b54410b85960309085d41078000e503020b01d008804006600a107860821484507501c52035180140c00541da030340300d040004000410140003881c20a141c024940d00003900501c402c822210181c6280c502c0d50100000146404002c0f050071222480600400640c0302c44d101d500303400548202c0c3c08102c00803410001341c3c201d42d80b00000601e030b03034030000125803034420700b540a0403101c0b002000c603440c49484441d008600d402c4410442901e544030340d02400f98020310b05a514007420f0035260001820030300034004061203030240c00681402100d1a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 382110638 1250 382109388 382109393
    0x20a020304030803040f061409120a0c0507150e09150d03050f0a08011e0b040e090a080a0903060b041b0809010e07030302030910020106050109090e010204052d030309010f050304 78
    0x2041d20010740d000080e950301c0c0c1c60305007001d8050005003202100e0161609149444080482c3c05141c001c0001000418480c48150303000d50040d03001506800a00c2414585000001c00800c0030b107028200c00c0300c0c0c0d100300a65400000c0d200c2e421078100c191140000000304281500c1180481701c1140707003111515501c04050034192014130807120608091400016a244d0894002c00024122048049003e9500c8a0140041c00e40e900e0f038082c5048002040004110f4490070744641604182e008040e00d68222a560f0f4200a41e4805c1609001007003503c0010803c1c00706030320600702500b405450134026065181300c802404d01d00005100140840075000ca04483d4095020234920b00820b81142d2981d5180e040c0a541c07500980354841c41100b0b400c914201c0c4a00c10b01804c1d0440300c041e100e125002e802d020403200039107a40c0e003505041d503600303001c0001c040c0c4e150840d80f00d5000740740000a10806030b8010942c4841840c1d80494042c2c0d00401c407a2300b55990001e003008030072180c3e02c1c0c1a51aa219072 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 382111888 1250 382110638 382110643
    0x203121012031d04091103121603030e030f0406021b0a0b3007020705042403081c02180301180209070c05010b0402070317011d010521060702072313020a02 68
    0x600c4466001845c0880002c10400350302001085c00c2000c5046441c4245540c101c04014803444500c10306000b1705082e2900040e00a411040c0d0081d84541a00d0400c2d1240c405840d40b40c1041d800140140d005014500c072400440c0035010310b00000360ba41c410400d082542c1c02446120309080544052840c0d603000d58541201494003001e10000c0c050a011360030407200c000e5a81c1918000e043c0f10b20701d01440b01c46202d001e0704007600d039403000c6900c0e010030502c0d40d1915036054010090001d11030100c00084062040f6030320040440704ca0701c600092080503401e0a0500712a40102c0e0b800101c0b418600d21005603440c00c20490744083e840c40d1011701304409150081c050310801000302d800038008602e450406800480044056a5000840740c2c1607986a018580b000a124852003100086800501180c2070102003059076025001c2c0401d94250011400b92810100721504070040e00400310600c940b07003146055070704800d8141c1e8901c107010715140c00103040d00104002e04d81210b03400642c003142036000303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 382113138 1250 382111888 382111937
    0x70c030516050d0305060a0504050f161110090c0602010504051c05090301020c15090715030c030b030f0607110312011806150c0b0109090f110f10020312101203 70
    0x3406071030aa03030b070191001d0045c004c00d0320010700c11605180049242d0509100e034034070950b40d1002e502e046807503540c40c0d111503ea1003500d0380108412940038052542c01080720b4007004591304e600148543d02801c011256203100c1c2c01100440e4108014000421000a900c8516020b04001d40a0180b074001e82030f1994410040043d80550001c200b0003c000c6d4013003203980305180740160743c002583d039480781c40d52103669502406850f0341915403c1c8119900c02e0380910705240007824001909881e103400a8030780603884922510b00c1d4055404c07c009a0f6005009500d031a0410000350300344502c601c036150ba02d0b10140183c01c51903600c004021030992641d0441001060b8501d000c2c1c8a000301d40100400b030750020841a58481e2000000190746400e6120300e98803150014040200710f000c55039001c0340621100c50046e0f01811044000600340d0b04d1030900344200980e50003c595500440781c018003240001000c513500b0380350300f2108010300356102c20707200140d603490b25200c40c0a1039030b800c240c0d824600 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 382114388 1250 382113138 382113143
    0x603191d070306051012021c15020f0a0216270917191e0c150e0d02010b0307051f02011b2106030c170a1502040e090303070c030516 58
    0x201d410000600c609644010700034184400040b54160302c468851101201d0454000e41081455030a580e282c3c1c201920180c4080c82103c00c855600e000ca009501660000200103d0042000444020a9404124400c1c080b0152041417034807a18041d00030392060010703280d016540020031401c080199084c0d00c1181001d502080c007919510318412940c0340d0390060644005902143e0400c1c540ba28062103449119019a0000144c3c0c14822502140c180c103102c1f004845080030340c4511054040c060003203080c074041c1e0703400400301c9802d055002400c0d90300b0308003040c1c043e03044408140159110140030b0840010318240d07890404101c10f00c01c03401802c00c241c2c0301008000708003200382d0860b03024001c1d5020401c8035100b0b2442100c0c6480030011a0080d1200500342c0c003c095040080d039182003442d02c4115440416100109000c0e201c0e40000040707109500e041d03590000742802490008050681c0200f00f5200a60a520300340001070074910391140040e0900c800807504030a54094082804034299 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 382115638 1250 382114388 382114393
    0x807020a030308011d0c0f21010306150b0c0c041d011103010e0702010507120f020717030103050607050a020a0807020d150f0f090f0206090102120301080c0f0603191d 73
    0x75503074240105600428003454001c20070160303011491009865085000b00031941106103000802c50070115a54492818600c2c501c03a01d0390500a05020361203a2030003580103c00c085240040b012858103100015040a42000801d21488810417400101406510426140003076208040b184100d100100214070482c95824100e2000c07000c1c0d001c0c00518120307100780345c02000586030604140d01340d9800701e070f5447c0056600c01c000825010540c12501503807a08060040c90001c5544548040076a1106001c1d2001d000200420070800d007085100d43c044d03e01e242c01c42c200106940b0082d1900e40c070102c040c0800101140c13100665880e2030341c00d120785d544613070b03226022000c00303078164007500c3e070b036101d41014502d40312300012004c0d0640903242005070b0280768480c6410f01a4201300068100d10700c514110711070000030b00030f00c108401c01140a02500340c0200000705640e4204580c5943c3e00001c5401008240280404201a1905d400450040590116122107409002070700c85d20112013030b10395031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 382116888 1250 382115638 382115659
    0x602040e070e041a1806010908100e0706050a141e0706051501020f0709021b0d050c06072a021f1716050f030a02090607030e090a140105010c080702 65
    0x1640c010071031555400c41a90144401184420036103030704084004c13401d0308460030b0549401c20400340c0011541c880c0050400103038258560030018070380f005000c0301c103101c2c135a1011000303844c02081000f07800a10051400034600115864008c19140b500c81c407202e0214404194a00840c14084001820f00213080b07801e622082c150034810007070602680e040043d07a0360031840322060751000c01c50082711040c80006080442ca007540001c029402041400100280c40701c440c0310900c0305000000c40d0140742d50710030380c0304c400ca90b680728240310000d480c4500f4000c00741740600c0001c8025a00501400150240403401170b0203001003540c0c3c0c1141c0f9030380802c200c0c2240e903954900d1380046021b10b8209031540e00132040e0741c0b060819000340b0200804940801c0d018444240c4920b071700002103a11180c40ca4025080c0391548000c43c000b900310010440208100701400909810012165544082da10751b0511114641000e000e04000060054604101d4034090301d106100d420011600c100e540076200c0403c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 382118138 1250 382116888 382116901
    0x1308010c030b01030e0d0225080d0513092706020c1608010c09050303030609060a18020a0f03022d0403020a0905010303030c080f13020d0f0605060310020f160602040e 73
    0x90862126403408070345441030500c0440030001e040300e800c06d25500141100344220034950800c0b1655040503100c05400100454900d00900004150901d1034848030384a51541d40729511105194011590b45450004030501c01e00d4640d1018031100d04000400c43c07001454100140a40326044485009102d02d040400300015020340c00c10446e80c480000300221308483c0411503040b486482410350540c01400820341d94980040c800d0f400000040c00c680b240f80e5900c0e822440701441c6171104030030a5001c5504a00e0b150080c4442400c6541031504505d8401003c0c4d18441d500b01e041002d0000b130a62174a80c51220030390385c0803540a19001400d603485584d8505d62880644001d00044000900b4109890142401902c01e0760051442404a5407543d803000440344403001100c0069a0000100501a000c6040c01a186030914015040410707103142c0401410310b011243c6415949285c4104070ba190254405420b40e1894032004d01188001c0351513080c440081d000d5900f00c1101c610000092205 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 382119388 1250 382118138 382118141
    0x2061612020a031107261f021c0509150a0b0a140f0402070f080903010f0c032a0f0e0307091401090f0b06030106050703110105160206011502121308010c03 68
    0x652840381c1d541d210b130110010405611840c0500c24490035100280c0e4050500d808071150505001e803070400c031170101ca28071050b2a41c10941d200380182c51a80040c110b86c04010000fa0800c00c040906401e200600f80121003030b42d00d460091601c01c900d0b8000e0045440380445810000041d1001071500c031600c0c1e115050603d0384900340442d00d04c900c03c04089441c840c10303c1c0c020340d1280d40c0c0004180d071066859450300700b0305600049200e649956148a88a60104c4511540f0500074041d0b90020720800d030b0322207000750310b0200400314501c0d1a40d084900d4045901140745084185280381c0041c1d0300c100712010901c2d2060701d4025241460402400c0003000d1011000541211404c40c03084c4401050a0741c1c060446441e0b1480540019003000148000c40c0924003c294680c4a8a405d4801e80c6403881c002d400c456080c0c0d0385c00d0070348152000542201d54104042d50141c0700d900318294990b01d907520040d64a0164a83c0100d98030400300701e25107800d006244506c0108a82802402081d00c603110040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 382120638 1250 382119388 382119403
    0xb06033711041e05060a0c0c0f0b04141503270d02011e02090d08090112050a20090604090b0a090906141e06090c0904020f0403060e0d08040206161202 66
    0x2000103940712400e400e00714010440f10b08581010b04401d103810200c00c4100c4000c0e254510940d114140c812000640002c0144000018542510015100e60901211f42040066403040f144611244080d103886516a48100ca400c00008000400c503c61300c1d510000710560806680046400b81107000b0441c250190450210b041c01070800904650360703864010101e000f98074116030407444803001103001607081130081141420505040b0b04000e40c240210059030b0084030b074084415140e80c648408118902c090440201615400c13074107003950040440c37501e025921820040c84d4035950f4034184c685a080d85480904500d09040c003060415040080103071040c007446e201c0c11092030380000c0440740925041004140943d1042c0441c0d150803040100a001c054240203403000c041002d29203540c0c40d8030042c501100350b40c01803900d031441c60034140100c1d10801e41c0303107941d42c02c110045007040f6031004040f80c2c001d9040b13a00c203440304c2e042e1100e082d13006816040244100c010402d031a1031941c0001d6050b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 382121888 1250 382120638 382120649
    0xa080708130e0108030a0c0c080109050d0801092f04030807080a1403040b1609050612060901090905150c070b0108150a020f04060e03100516030b0603371104 69
    0x21641d8031900040c2c407070244201d40f1160030500060035050310981c40d03548624007592401c035003142c8901006013100c03030407801102d5642c0901600640b10f5001000c150050420010400009002121406101249040024442c80c10056071848071040d08252405190043e401703540f101150300d400d60841c0d114040e40d101240018121060307520b050b404480c8100c2e44840902026201d0203d190101102c501070030b418460401c3c4040780c5600e88102528080d40c1264951100d82450300610180c054182c001e0001c041c14241d40c00c010403000909112940f8002d18801256035800002610500070364900600d50000d00c40001480e0701e001940c3e02d001d0141c000f1090391360700c030040041c04078801c1c6803850242003130030f010400256004a4100100c8070010b019500c0a1201c0032400d0f0488004440c12610440e81c4007a00e6045607041c469a8690002518003503c3d42c104a800041740e45000020a034081c103103111f1441240100700340000b01c034580b00c4018002e20314030b02151b8070b15803c41d0058 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 382123138 1250 382121888 382121917
    0x70b09071211030a2f04061d090c060a02030d0501081207030813020d080301081005060a0512070e0a050f18060103170706090507060f0c0f0f03110d09051f08070503090a080708 77
    0x5d41140b403420348104000c44031562800f00107030070392a10000b42100010841030203406203000314180394440781c000f480c51420544c00b5696900004c02803404541041e00082c83d6a8400301d094004940800221060305805007003d885a0b075034015820f0f010b42d010030000703401403100d040c007030108040c1348050b40c140c45030b100a48460210281480c012100201c8a65030f0000140ba001c101c0d0f410012250150b102c542019902445d440300b40721204a80b050b6820013100d60f0b6402000140074941e501c5642044072849403140e44202112055a600300c103000150420540e401d000920310b0019003120000d80d4403101c02d1000c14400d09101c1c0d01c41d207003440768101080d03040802507507007440f40e003074181c0b00daa2010013162980002e44a14102c408001e07411018064040c054000c0e1407000c0140209100d050358446011900f04401d0244c411450340a80d4000c81d00000f800d1511504144d48680c4151315280458480d40ea0900b11440c2181204018041c8a4009031440601118000410116811404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 382124388 1250 382123138 382123223
    0xa170c0f0d03050105190e060301021e03090f03070b0a0b1c060902101b080702030102070b1303090b0304120c170406080a05150333070203070b09071211030a 69
    0x5014104168006c00001d0500103082407048500c1165115009030001d000181008500b8820400410908901c0c402007207000c01084050f86081088184400d0b122000d5800d0555a690740108000c1c00ba141c2c480031358580021740c1454503680c4404000c64000d01e2000190151424083c00910b030348031090707005422024142d080c1d00c3c001c1044100b90102c6c02c5000c25003d019072101c41c0700e40c0000e40c2c200e0b8555006c0080304081050006c02d24010a4010104545803126190186c000c1500e580701c9503011405100704004540e00d8524000101c3c3d150414603600340b02450252080030000b100710a00380c0002c18080341141d07012031024420a0741c402c0400160715143e142d0415000314070303019030385580700d845503c0d0b44542d110440f030f01d090342d0b654078070800300d0a4010500a00404644a400580c00031079107106201d1038600050b001400e1401130b03c0f80c2401c0c042c0c25602e200e2240c1c3c0281815040807280e00c8251070410603c9801500454018460703c8121100c0400024004c5481d004800211 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 382125638 1250 382124388 382124399
    0x90d030203010f3b24010c0f050703120e03070915150c02030303071215060212071a070504030515070e04050c0c06010810060f080a170c0f0d030501 65
    0x421241a034100d503c0b82450980b0b0076062940c200c509140c080b01010041ca401c2c104a1a241e5a0014846086000714204d15110710030030fa4629031800c1e03400d40b00c2c4040b003850f940c0b41d030070400712402260800130840d102c82d05820101e1400150381e000409a00c484e44c0d007002c4d03180d072000c1d0410080c007044080d2040550f603030318594260341d01c96402200c1c1d014103030300800a044000c0d4090010010904000c005002981c00280c1190011504200490072903464034a020b19984103841000c00c078907465499503810031500a5503022094104110360000191010500143c02030300246502c42c41c610002902e480038008055800500c012070301f43c424201c107000c91100c207881c030368410301065485922004441d01004050000642115280070b0108500e98200805020060107001c40f60014190481f0202d00c0004594840c0d10038003042400700d2041c041d045c00411101080e94200b04503240f0b070010281a1001841441c5100b25148031741a4808006d03000032800351052486a201084260f0340e80c13 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 382126888 1250 382125638 382125641
    0xe0c03032106030a05010614090109021603081306060f06020d0203030f0f060d0b0f041709090103140c1c02040f0c0c0210140a08091009020102060705220e090d03 71
    0x4400e0815103400c01d81800d038080e0180d41c5441da00100090465118040940b661030031200039800c8085406204900c00c1c0b07103801c1c0700d101d160060441c407600b1407070245080042c140e0b1051030b22000b4104a03028000c11074100d10308201c40c01594100d41c0400040c0c0d13880c1c50003111a9002d2080301c0c05801017440350b000b06400030041d070b4400c100c84104600e59540710386051200000040042e5481703211100c0d070101003625100402c0c07051200030084505130400e42411140811410b10700c41180b2400c1000080c1e9440711088281180e5110803c50484444419110308110b1042141c81c2c100c1004a88840400120142c2c40c11241c001e940800c220400404281d0a031000c0d0180d0401240c5181007071801400d240385c40700c800c1812464441c0341e510700c0a80ca0592a0701c8004000000380c090301c03c1c002c00513420f1010f005810b041050421060303c1642c0041d40780c103002400641070200125506c4600040108a194249d8050f268808040e8407815030004140b41a03811000a01c21082e500c01c003980030307 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 382128138 1250 382126888 382126897
    0xc0f030c0d290106031e0605010e0904060b03160303080703090b070e03010e0607020705010e031c110109020303040e0f090105060a090c020c03010c0903031701180c0219060e0c0303 79
    0x3800c0060340400c65100e02001121202610940b0007904030100412415612242d01030a80d030ba80c0030985241800d0306010545d13100920182c01442c00301d00b0001c1d0b070713000040c072000380809440c1d03480070741d981d410418005c00d8131000d61500341c0074081191518030503801640040d60300c25124003c0300c1d107130300390201c1c1214181c0c03500615005003800481c2d80180106c912001c091401000401c2c844e1450b5040c0303003000001d445040141c1d11141c4244503960304100d21042c60003041d0001c0c240c1100c000d03040b00ea950f40300100f8009003d4222402910100b003034005160341c64020301103950b1207a82d9408a500300004489024024011501182da814010301a650180b03000514500440d4188100c040081c5807071502c04056114460aa00c0c0e81d490a0040000656040e01e650846920354103001d0302c0c0b042c00c81d0303e8102d20010440140180d200202c1c00483c1910380c5000010201c007102e0069160500d03c51020006118042159003040066045000840300c4032050701d01b1001300800b415502d008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 382129388 1250 382128138 382128163
    0x32802071706040308090309131b031509050405030d060602031c0504050604030e030c0a0321051c110403150603150c02060a090303090c03260c03190e120c0f03 70
    0x100d42c0128000c6032141e45a503400c1004101543d181c0003000e8000340385034802c3c90211104680383c400c212140038080100c030203800c4450400340400b291409940158203054010f80082c5a40c4001150a1020410070703112203400240e802c004440d194040030b50349030494500c1d0300c05561f5044101000c2e030b1090143c5030140d60300030000c25046d00c03070307580071b441108000d030586415128441c0c0c0e18416950300c20b0084001d42c000c10007030f00000c030144d0085c080c9441c030b03080a50621008008070b460981600020592600c4480e100040788ca28490201d4054441c651016140e85885000100c424200751710040499106400c0c0c0304080200c03c40c9031060710501d62035800960017100008001005a40004050320704c645400590402d1940c0c8040744850b864100b503a43d0011401c1b0070413601400b0f80e41542502e03443c0e420a042268140a0b02e5807440340044034058054004125034802d80140444405038034010001b000018a003a071055032106007400c0035102e40f20140c0641c80d24113001c41e00340c52504 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 382130638 1250 382129388 382129393
    0x1201031b06050c0c10050f040f0302040b060307022107121d03060709090906180f050c0a0b0405060a0e1c0215030103020603180a120f02010b0109260328020717 70
    0x1310b202e4108181d45042d24404010b00004210704881003040100810107800d204211010090a60060100300c032104910240107080c10020b000e412038002518406910301000304104030011158140c1840c05030704e00003003413055000c0b4200035064100844600300c005c0c115600c412000002d040540d41d4070705643c0752011820404040c089001190042550203014507004543c44103071044a41c003802140d9010707598003900310034202c10420144034101c001c98088078a4940e0a007425090100d1b4170075031103080d124000025075840f0080c0251400340c40c1d460b00601441da000440a80c2e40c00b09003c03914200d100c2d641100074404144403640c1a05d050b00c0d0041c00c0340e070560f9100301c0c840041d6030080c0401c40d22481454240e000080d0752040000004244e5501c41c005514130280c060300303450301c0e00001d50621080c51400e10041003484810004100103218441c4c4607400c040c03800f8118411581e0941c4900400704a0b040a1312000b84801801c20865088508055075911000e130401d0b850651202581c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 382131888 1250 382130638 382130653
    0x806011b08030a0e010603020604080a1406060901050d0231060b0f03040303200f070209060105070506040602090f09010801060e0f0106140d0b060309070e0c070506130302031201031b06050c 83
    0x1144141c3c1329602c0404803400019450780ca030b8001031103a07000b991190106074062030f5007408003c064150071140401c143c00400c414101a0006080980140142802101002c81c400300b9035903940b00030740386030024200c1c40c4076040340c40d0502021505010040b040103820b045d0002001c10604044440394426410342500750b8172603907070880190201c1c8170f01700c14505643c0c00c00e0507000514801400d40406011f00340d0398510251040c4413040704000c10042c1448414071001c1c010890100c2c040f64010381c083c00050391f44680200041800080100c415040056000045881603055010f401580d442d0103001131a40d070741954401450000f4000d860018081c05200540601d801018002c81d040f5a8400b09100a1810128101307400850309030f20729038046042044804004107115410903a07880d18907181c456141c0714945e50304805000650b03460b80c0703115000103040c400c0c01643c0724011103e01c0061156900d0600c1d42028030182c9190b00c1c048140c01000807064064811a0700c08101e000c01741984 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 382133138 1250 382131888 382131901
    0x18040b0d020d08090a0806010602064501020d231302010f14040909033209090603070305011d1b131806060b071a0c0319020c0d0806011b0803 62
    0x5038001c031404c0d54008030103030804500c6a800344000750103003940c1d0340282400d1030070020b6000d0700b5556601401034181d40f858042c2541005401c4100b040c00c0c40000c001e6000f0080e06c40600900c80c420500c1c042c41d10304200c1c04d410654426038000c404030340711811000794407840e8060315628907040e0000c0c0801d82c00466101401e01900003c6580c1e4011242241170903a508250002d888440700110000350b040c94002034400000172100900305203204880b04007110320807081060317101c1c00240c0c501c6000d05000086036075a042010b81c000e564840000d000303080c40000a161f081220b0a140c01d060b0145c80d20680c0c100038412211861204002e0034280c4140c50308248034024035040b0500c82000a100180402003030050040200411303600500703682c0d4242900f403c64503c403100c40d03a081c1d542040c6050004100040040e43d0b000000250a10076410b0983e80f200000e101c1e013a603040142c000c032060500d01c0c035000701a0510805080c2c0f10031078031030b16104c3e0003205c44841260003016102c0a0010a00c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 382134388 1250 382133138 382133153
    0x1020310150207030b01030b07110c1c02040e0d0306030c06020c090601050306030a0b0c0c0c09100b160c140a150801171906020301090e19030507020a0b18040b0d020d 73
    0x110781010b0060b10001070b140d440d4010040c0d0240c01c256000030001c014031100c035600c00030102c240d44030382c4080d0100b4038543c3c0008408003900c00c4486030131015000c0703140966039036034000314400c0203000c101c030003100c0003e8000c0c001d03058905c0107851070000c0050019105001180c4000710040c0100710108640d039800c0190f41580000c2d14268044c46405141000548040b001c28042e0080b0801c950f250241034a03a039280148001141d80590440c105120051100307818042c2900c030b010a41c2a26861420550f403c0d40ca51140090030141107805c0000340000c14807a4851550b034290344031b400f0f441d160044146460359480c02040000d41810041010111001890059803091400c4d611004842d040343e113034200d204102518199400001001074500720f100d001e06001d000c002420b020042440b211200c0804080c0250500000042020455440b101d60304050722603041070342c0c1c580ca00c280890601514030012603025500e05211100a03182003010700191550060450180442a0340e5030312 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 382135638 1250 382134388 382134419
    0x20a060525111012050106030605030a0f050f03070f0209060a0b0306040b0622090c020c010215070e04090b06030705060f0906160503071a0703020406090b0306010908030d0b0108060301020310 84
    0x4506049094070306589944602c0d03c0700c85000b103682d84284414a891401c000c960040e801a003d044c600f000070400d50f00d01080c40d24107540c2150320a1600480e0342030540c20420954200c0361903000020b81da004101004842d40c2c995802a1501e80c241c0c0c2d615010b0201c40c117554091800304000a10028510307182a030041d00c0e100d0b10182c1601d041040030304040300d821951107901d20640d511b40e4400d0040040500c200100020113200034541c840328000040d403560751b14981d0044402c21030001854960250000528a42020300204043c208034148480038040694415209000302e950004551034401c2c20768000c03107100750b1076501c0c1c5000c01040000741d50048450149c041041c2c1c8030390002c198244080c249003401a0b29850144914806000c01c0160042c50f4070185403040c032052001c55401900d00041e10010743c0c130650b807a140c141c0140c07840c0d59154000005803000107010040c821040e007000100c41000c1e02c4803251500c1e404201401e03408222014a04010f07082c8081100391444a82039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 382136888 1250 382135638 382135643
    0x100b0903010b190905060301020f250503040603020715050108030d020a0e0d1109160807030e03120412110a0218070c060606020d080603062406130f03020a060525 71
    0x1511004641c040f800c0c200043c0d590315400300c1000800c101010083c01102c0d07000c42c045008626244074080d07115040c1c003500d10b1201800c0303038545040300b901c030900d0790004002da0054126500e803aa01d07030009019520074181240d03140713209007200804940e2402400d050700d007030303401440c1070280d0003403980029003150f261030040201c0c004814506840b580c0006181500811680844d1540038044c4121940054483c01a01d0802c6603500143c591107261641c1019451401094100304c40c00d2161031400f4100341e84294586001c240010400d600f41007000d6900725840e00322030000010b0080d42c55800e0b80324069005002c240048000307058a03101141c1c4015141001c02c01111152901c4d02120041c0d0070103405a800405107042c05c94000d0817299222104500401d081d290201e10388250407000541d81813103a8800810250076500c4009452075089c1e0342d441c64081a83c0c52510292940d0580702c247d0249400c02e2000c11001e214104903801d2044031281594010701030030001c2c100d40c1884d0400d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 382138138 1250 382136888 382136891
    0x605030a06051e0103110f0403020d02150d060501091221030608030a0c2d0609060b03030c011401050603040c0e060409060606080f060306070906030e0a0b0403020a050114100b090301 80
    0x8501d50340c605400f414448484a9030041c0082c00d0700024044500202e0840c900440c24448003034001000380856040d82e82c1a034440c40014214030101c0c0c030300b603248240c40301d0006021503080ca80300180e921840403114242d0b0b8980006685400004511a040c00041c0a140310f0403251035072201026100c2d0083c0d805072500040700e0f41d44080c4507045400c12800d80d4001402d1240b02c20031b100306070380104200742d140c00040003036a1149600d0000208591401400e0a4450303580f0821301c8910707807000c0c104007400303419130350781c0c0c113000400034002d00c901d01c490081086040004a15401e005043d280f1a030750003d955a449400c1a00c600c100c85401071540b50b0080e100c00e051000603606000303e03c014202e0b900c80d041071f030500c00303a503c1036000000e1495002307600ca07078104010140d00106c0d00d02200e0090030b00013161480e414135a8103043c2e40050142c85500c40c80103102c00c03d43d0009000d012140074100030044244d20600400c0d4004055600403042003100318140041c50300d40303004242c0d587c0700400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 382139388 1250 382138138 382138151
    0x60215041403030103080d0b010e0a09090c170708060a0b010206060114070c090b10111902010302040306020307082e030b0c21070e0612040b060616050d11060f010605030a 75
    0x20461450b8002d8104603580c40f40030030791f07880d680741901500040f2134003401c05401001d9981e0114550304110311030807000a4440d01c4013410b001481d002c01004e86030650380b564401c001c0c054866038071800c074821301c00a84030b400c0c0010130401d95841a000e640d641640a4410b98450034011140c1003d20110051442d030100016400600e001e14110700500502c4004038108400ca41001883d62740909140103011222481c000701000104640320305100c03201c2c0360100c02009000480003401160002005240700005001741d02ea0409102c610031890342c80500021040f030300d4403200200d4104400d0401c0d81d0840414000541c1900140344e10405070050710741003031060b010039007085680764806d448003091402400f40250340001d484240390000d8a46a260841130466140300400080018121840d06004034080e9030710310040719205040021481c40d0344401d8188507854024181801c008200a00b50ad84e4880d8404165a4846c0044d10110030b0b0581c03800300b056560745c0c401484e40c40c0310355a81c070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 382140638 1250 382139388 382139423
    0x50f0a0801050f01150e0a0612090204020d020d050106110705010e010c0506160f17010909050a0210021525030e07050409110414220201020a2411030106021504 70
    0x724940c41003004002c00350040d4900807520006117910384002c3c00700400c03904c1c80c018984450105a0032600310703140401c13581c0e0b50781d001e600c0200442c01001358041d00002d8400d803c1062a0050a0b00440c101c0d01009566a6150283c03000603841e5051003ca03001035208012541c081e01ca04400c2200605190020344095034400d401d110044460318055090751b428a01216840130354446640e0041c01d011030b40030058010600c40c1841486030410b44c5403641e031a002004410f0020101455014001080c4101804d070065161442d01300da2818011045c800110000d40f140840d004184a101000030102400c1400f01c020f4400d90b41e0261300c500c508400000c0c00e840342e2150803012400341a041c821242003004100995003070840c450b0980750741d2000c1c8200015004000140315113892000e84100e0340510050b4104803a503007025010204040c2e80143d00890f0042d414412641d46a0401020300c04c400d521a50307001c00e0140c00b005070b0007004040c02203601e1006054101d40074400d0301c8003803003030070703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 382141888 1250 382140638 382140641
    0xa1505012d1701140109020906040e0c0408030c07082107020f040905070605120a09021f02210702040b010f082e090b03150103030e0d080c0703050705240301050f0a0801 74
    0x2e0015031007603649245000c04503081d102198050400c0c80415440c0241c6480018030300c0c0914000c4000c001e10a00100340d00e071408404540081040701d082c0d0b07458000480e0141d4031505140b15001180c010504900c0405041266164240c14010946420f0140e6602804030f14490203002540040d959004400414170400502d00100016511603a0b502165808040b079404050310000c4524109009140140d45c0c4061060001143c00c2c1060340c5501c03e210102d1030444140c0f0380380c819820100b441001501c4110007084400d0080e6420300103c03e06000442d900c582c0d0020020000318220081903c0403040d0031100c07501c903024404181e9a205066400d903282102e82d0040c43c0c81903a8a11101f9607082c01e00c0f8140d10500107120b9484598955200030b08602031040002e88683e100c3d2545508000f409000d658086454500300d0700f0f219202d24006990382200d0007178030b1081481c0b804504891000724000742403e03c0d062045030442c1d2800c010300c8040d403a188455684141c01410110300b04009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 382143138 1250 382141888 382141919
    0xe09070b03130c1e1409060609060d060e01050f031c1d03030c060411060703051207050c0105092b050403170933030103051b040e0f0a1505012d 63
    0x8042500b2169100444d8844080c07000364008154058941e00000d49613031140c0b005580440141e400c00d59803160340c00007803801c0c0b2452201079061490901e02080142800c00407034143c40003034488120501c40d400400d41c0d195482c0a1443c000c441116410803040e100d64048248865060003205c600100e02d400a81160002049035003203600c000d00300310500804a2003002d01c004240c8401d0329145075905c00408601c100301c0710588005044001c03d1000307108804a6800540700e80c000c100c00d04101807081d44454070410150804c2012040368400690b02000205080200e40c41c2c884c5820701d155120181c5040038585090504424040085103442d00320802807000340100b24446080481d0b103042141d55000710802d600792105000620001d440080c100040c50183d5408411640e4100c0c00500517107113481341c80d00707640101e0b2681804c0480028010107210310486000c00d50b201c40c400c940044603000d20030000d410314407404004e0340c002c1c1c48101403074904402060404c2c2903102d48440c460700c0030707 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 382144388 1250 382143138 382143149
    0x203090d0602190306180504020f04090f03020607090f050d080409060e04120c110f1306080a0308010e04120809010f092103090c15020c030d020d090e09070b03130c 72
    0xc000500100f0f500c0c0c58002e185a95081d82000c0041c03509003070104070b244051307401441a5680d03400100e03040d0b41c0e80c5c4003a42103902e4000e106000039242480c013600d842c4d4001c00c08901610650000c00c410031b008452038803c5e500f07011490307400c0c18641010003800000144085d81e07020001c11002c60b1400403401a007002e4034020001604d18101460220a1000d1144150080100c0340d114000056040700d502c12008108840004100c6c802800251060001c014441c844528000d0001044000407513110181802511080c055a0343c1301088545018100c034010300301181d0441e101c0c1c805015154040d00b0140081c00002c0c08000041140111400e00380290b80e44607260352001c442680751102c1486c0c1e045249014000c400c020f50320820840d65500960b1500700c448111402d0240c42004001c0d00e01200070100c422004c40058082d481b00d031900036510018019035008503400b00d0380b04140740a07100c1c48009021045c90000200c030030380c201500b054402c880000640b800b240f542e10601c009400c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 382145638 1250 382144388 382144391
    0xd020f2101140117011a1002030c07150311250f0b07090e150a090c020c0a0b0301030506010e0403050910090506030a05012d090902011b060c021005060d02010c02010203090d06 77
    0x1410030741c42c056525105544800c40c2d82c10140351242001d0006404080c8006c286c400a0107403813002404d034110300605220300c59505c41c0902c00280041543c40f00d0007409940d032003c02014142d4183c1680d548140c1c02c020204898003c0d030680004000c414610b20130380110300c2d5841d40f918540c0e804900c0a8160b0700e050000390b80540a00c11030190b841c400341c1046d48400442050b402000214030328424031f1281118081e0f8460f0f0f20b112803802805003071700c0a81e0080c224240305841d2900fa4845d0b800a02050f03034184907134400400e070000e6454516025607019110b46041901c10000c01c04942c06400f561000c02c05c01c910001215121040514081e03203181d00041429170410400e0302040041480c1c1d13015102c2013401341350010032082d000b001600d0f100000450724005600059503209010500c0c4881607400c1c0c0040d50a0040701d03845014603070855804c0d61030104605070170400b0f8590568105602144d0182d0120041d8010040d004040c0e2041c01aa414580c10070000703207a90030b50315170035a0102d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 382146888 1250 382145638 382145641
    0x30c1209010c141204030e0307081f0b01090b0f030a091e031101150504110f041805010812030604020903010e10020a031407090b131e080c0d020f210114 67
    0x10343e000341450801c0c509000701c0e07605000c0740d0024200030b014060000f40601256500c3d00319542c0f0144455006848120100c540e20040340e04481e10816818403d1b81d940d81c6070a400881d25842040200d04854181074500c7c10a00820110700c11070703001500380c0d00b0590b038880320100003404003e034002c4440c101d21070011040119040291041d8189504405141d160504410700754541c1003206050312001d4900084a4050000640341e5100d81340803450503240c08107000038440e08900d0505910400b0003400c0c0070740e981c0d804559540b41c01109064100050500000b6082c1c109940a07010b52080100082060412500c1d15401c0900c8140060980c0f50000b400c014090780500a40000840c10390f1044403d2500c0341b40244490703514001c52120110000d2940002211404188050003c00400c914600120203200902c458544607500b900c1c0100302d2074013240c1c030f80700e50341c48030700354002d042400038040800412400d281c070586150302c40c0000b6071420508480034816002a00400c00305184107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 382148138 1250 382146888 382146911
    0x307090506011b080414040b0409080910020f0c0103230c0c150c090f180109020a0f02030a0f030e0a0804031112190210141239030c120901 61
    0x30403118000c00115070707851850b0f0b000245084200c8040b500502d81c6000d0300b07603000c0c00107800f60012140050341700b41002114410b020b0f03410300038038455404961410007510706c0d820a0380c540342da103e14030501ea007200c6600011540241c1002c043d50700e0006240c0d03241084640c680300c3d420026900355500400100d40c1000c1c55008010038240508031002100485c5050481d119447c40341003240350040c080c440c0c0c090004d803903140c0e401028005034281c030781d140d60715415040000d42245e0089800142e02140ca0040c041c004022144c0210080d59240003182034101c058010700407280403080544206000c0002080500020b00051807240140182464503038003008081407041e40c1414844c0c0055040244414a210080c9401d035410759080c941d410050307000b40d41d41400b6450200e048040010b880500d200003025851040f4221910340c2091602043c01045118018151683e04c00707407810460a50f48000c005543d0124204151030320380140304480120b501300984040c5540d80d154200000e1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 382149388 1250 382148138 382148147
    0xe04081612110f03040e0105040906020c030a030207032d200a0c0302031b010c1203110703020105060108090c0a03170c1501150507150e100513110a03030207150c02030709050601 78
    0x14203d110703200650034981040038150a150061040340e10440e135400c90300040101d00d4040e00c10340400c000640e91a001411800b9001c1c0d44900c0003100001d407580308103110780d180c070708280e00850310400c0b8612120352a16415103043d6404160004000000c0c3c2c03081c0051103042210240c4d561060401c040180e00d10f00c1450314100c3e1207407103e039400c1441c182c40d40150340d100e5400d1006070b402c0784689400b45000c0c00e00394000d1010320f07082e00042000080764000c0c0368054000c18090301d03080c1d844003c0b130b076134199940c1e80f961800c648032940700c0d042c18000c00c089081c2d0202031450000e503018141c5880b4500401c146002c48561685601813000c0004100c600e4000d0181c0403442c10604011b0301d440c105075100340c1d1020301460704045070390b0303500101d1480312810424041c0320316448404008900340400a01254060b1503402c4580c20301000c03414400d414480c40c41d8044079855002022000d040000e10700701324034407400d85000c01c6200b00e80c000150b54104550700c001c20451030001883c2c10003000061 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 382150638 1250 382149388 382149403
    0xc05040503060a11090114041e320f031204080f0f070f0b070807150b030c01020c0306010e04030c0506040309050f060c1c03090b0f010914010e0408161211 68
    0xd000f0351a000458001c122060200e0b10b1000092902c4041e0443d0009040c84a0150348c00200744c401e0140403000c080101010f291065404080c080d60511709003803d40703544500440d810b040388401500b00c1d05100e04008001a20980008041d583c181168481842c65a04164070582c01079101c01c62810000c241803081e5202d044a40011b4600c0b10f0820100108200ca50301c181021540006100820301082c401691840c83e405040d0f001e030a2480000703000600060119507220380511104400c0b650b000140c64100e4280160141846030318204480100f09801802170f028481032001a0001603020301c20140b0861082d25200502410030083c13043c0801640425801810100882c1140c50400100d502818a25880f0000f4800b1554002c41c00350030b8404c4010700382c00501c03080c0007412115041c114140c50706030504001003000c0000a4008003000e02c0340c00103680714100828045040c0d10001c056070310141c100121039522903650121030302000e90b002e0380042e000601a041c138113014002035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 382151888 1250 382150638 382150651
    0x150613180c110d0c080723010903021006060e0d0203030f0a0807090506030103053a0804050c0d020d110f0a06020610080f0309040e010609020a2a0b01031101120c0504050306 76
    0x4040030340d46088050b160315284c02c8050100301c0301188600400a40c00140c01038603044007280c1000342e0200311b80300e0207012841c0048003d8041d94604200c01006403251204036442e0355200d0401c60340c804184001c1101200050381c00d40000c1102c0741107000900010070101a035595551110301d030840c00204010b42c83d4101c2881100c0410040000c5600012400310300255130641c05150207901e202507008040740d480306991103084040383d80e00c040d00401e805200c0e9010b601a682e07846035010400965100005000f94405030744003074140450039200c1e0b103808402d0040c000e0040800d074040021104182e640c0301c000181e200d601003107440400c0c20040030061038507074014070f62841030800141c2ca030b00924004502480e40c42103030b110440002d400442c01080e00c1581156980d52410b0b0007403000d901c18681d901001c10401d9215801c28600c240c2404141c0c10009149460742035698564285984c02c500c40e040120b00d88040310021040d00c40d00020902a84820350b0303071840c0c001458141040103225 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 382153138 1250 382151888 382151893
    0x5131e090507050909041b171e07050607030f050d05040b06011d030325080a0306050907090807030b04031115190209100c02060c06012c150613180c11 66
    0x242019140c410045e604198400800d11600000e4203030a0681da199074041401c4580800302c551350440080b40c09607440801081070200e01540c16401c039a10580c910500350085d4082186402191040b5507445d5441190300c3e08130b1401c070010034160b00307503402940c003641c0390900102448150340c4c1118140000540c2c2c11080c60402080c074000a44a010b140345010076800951141c510344a0390088002c0d007154001c0d05c581c0c94a49616004006240354010716000b0036030030700404e81443c052031030b10301100c40c1d1900528403d42181d40345540120094811428415064030702030410009000107206115030840b854804e1405449940c0c0040f105020003150a1040140380415114078081000b10152402c20211000e528404103443d8810028618503d0042400105a10700c01c00660a04088411440c908000721415921071502003540c1c04440c1000c403848139240b90501c040541600c20b2201d0b04080c0045c3d40c0c80900c070352100c0704c4e040d103040b66035a0003042000a80004440d03c000744000300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 382154388 1250 382153138 382153147
    0x321050403201b0613090f060305010c08040c140418052505031203040f080705010e0c12150606160510060902091c05011503050f28020105131e09050705 67
    0x2041e59840fa40070121600940c0f0004540822083c1419600001c00b20b10b0420000701c0322504d01080140450f0008480307550a00707481003030031841044c0c16030140d80c2140c1c24038256480d0803e40e030101d4881d045020740264480c10310b4040e982c011964009011b0064000d0096011100c0102c5000c204400003200702c4403000c2414840e540b00001c6014140340003004081d80c035102c0e4203005109a00c40c10300140404400070300682000010b40003039903201104411210100366003410031807c114221250f42c0d46502c6882c0840010b68003c06080e04204050a03203850043c00c4081c94100c00c142002c25100ca0340809200c40c0310102034414178005003408281181003400d1200041c034038604021a01c112a07100780741324428841c007075022040921909924051455481ca40181c5a8a003010a00c1041c0900c0d4526001d02c000c1040351141203907000c82c2e44186401c568015100c0f5003050300103818054442101284900050511002d0f00c1e0000541e680e050b8648040e84080d42c000604c00b0303080110622 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 382155638 1250 382154388 382154413
    0x706050601111b1801081c020c10030c0c12020c010908070b030112110414041101030515010f050712091806060906140d0903050316110a032105040320 66
    0x2a103141280000c0000c40d41506100b4000380307208251650102c0c0300403004000180300c50000031f004003200403000080c510f142c1c0d000d009a848010a440e02c0350003144140b01c108a452003903010080005ea0f40c1010a008410380e11607038449090f0810150260740324060f0401c10b907800030307032413001400a00000d0000b6402c0c4220b0500f00d020610444101c1e20f4004400c40811003480030502a9404c0600100220702100980380d003c044203441c01e507400303080454100b145520901815104400150140846e0035038400115900000205d40100f04041405258001000ca0340303061941d82d095660071005078100640281c0d5101c032659011a01c5250010401113103400c004040d0407202c807410101d502d0181c4500c030082c14840c0481072040b1900e032042c1e0b20201a0800c021750b000d850211081c04541404960076030b41024804129401a84480ba012000038031440240040020103047e001d02c0b041c0300040f220076030390113540440104000e8030803004d081d442d442d5000030802112006242082c03078030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 382156888 1250 382155638 382155643
    0x300a1503050d14041706011503020909041101030e0f0d090608040c06030f24170a05190602040305191b050607150608070608010305060105060a21060e0c070605060111 73
    0x6402d10000c1c000c40f00002c0501c814124161001880a2000c1000c00c0071000081c9458003c02d018241c40050302c00303210b0032124800e10980d0805240500003029684480d00e0392034881c1c2c19079480d07504241e2100a20800900e09000c401c0102c3d100d01d00a0076400c0d44000060913410141e04840c040000860401002c1049c0c001c100341141c0c1c0c58100002e800b41015894005400c600040814515105034190449081ca0b9801c9040316400510106815580031341251560f46101014190307900482c10b90012142e00542040710920840c4014a41a40c2e540d40e1402c090f0104a48011120124515024001d66100030001c036000d610240511904000000d80a4010514042c10303509036600100f02066040e0f1090005d000340b201216906541e910000381008001d0004072958041e400c000211030403c0c0c415100000c825072201111402c1d01d511070300040b241c500c2d00021160300d40400195501c0343c106054000d4591400c12550364106091500c00d46002801560410440e04854035210201 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 382158138 1250 382156888 382156903
    0x140319030b18330310020d0902090708160504030b01060f022104050a09020301050306060d050703210e010207180c0e04020f071b0317300a150305 64
    0x4508001440140301004118000b4120901d80e00301d514407024800c040700d48041461490300b03504010840d0110b403c442a8030389141070481601980301070071145c00c2000940203002d01c10110b042c0080c450459400007050307503905444002c00b00c0e140000b0b00401c3d90410032050085041421314910309851035450410071481403041c2401c2060720710311918200d02c2440121340c00c12020f1805c80c00c07000110080c0742d007607000c0d21030144079540210300000c10440c01d00135603048410040140440d55101800d0041c840f07101d54088036203001e01100030000688201c0c041c142c411019545407540c84203034602034610754a454003641990b0020f03104001905103201006582c02110130003060f4005c601070151614416001900c3d030042c00825070000b541012000307070045a0048289401c010801403002c844d90915010181006150107102114032124500800480c502e0080d4084480f0360346141740c0300f4a40006070030b8000e8119805016400d80103004482260342c140c0c540706800340ca1f50303840c0c580c2c038440d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 382159388 1250 382158138 382158187
    0xf04020402071a040b070f1416020307180b010306051c120c02091303082226070b040b072606030a0c060801180e0a0f02150708071403 59
    0x40000344901040086820103c2c2145940742030f030300d00d0506181800e1151000c45502c2c0000e0700a04c0d1403103810380f2940746038100b224014080e6180001245014030b002d04062400e03609481450350000f40d0700501c01503401503040080700000c0d100f20410005040c1c40003540a14418400848000b034046001c3c2408414140d018444500381d22042c030f000d440382903003140c2c080d610a031404200840d01c80e01020050f5524402ea40d803d0580d910328205a090200002d440c2800c01e288503003d50002c0c2d82003d0a10300c5180c0040d20404091200604902236840b1210494810ba4000c09000800154510558018101d8140101b0b5916191452048a4412100c032031008040d0b101003036040e1000e1083c0c13031605030008030b0101c0c01d90704c1d0940942240400c1c42541e212407610014258800340b28403907000e4840320714001c6c0034551090744030003132805481c0311305990011031001b1074908070580800600e034542c840e4840075150116401e00190307040c5603401001450300308018440701c000b60512498640755 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 382160638 1250 382159388 382159391
    0x9050103020711011d0d0b1905040302060408070201021f09110102071413062105070503150105040f060509100303020f01090803010b07060603081602210618030c07030b010501090e0f040204 83
    0x15014070400000d00c00b2885d081e42000c920301c0d40300d003403100310000345208102c004000500309111003006030488604036001f0b00140c110b00c1c04540058003400040003028014411500b08032400480c0e400c248020321054960305503580c1075141040104055544c0504d001d001805031705141c80042115484980c2c40c452280d500400c02c1513411034983d00000203451810110582d0211300b000643c03400e1111481070701d0358490800700280354a00015074000a280d000042d011592802084c4000380007902d00600c03500b034035000003180f1502c5911041c4d104814000c03030a41200e186080c00380c242178081004094903410030b41c02c00003207245107080340d044485103241d80d60742c1c040c6424410024081c1ea003008012a0000584041e6101c0c60403421001a000b00c1e044030450038030b0021601d400c042c12042041c1900502c0016103c0300d14103035221030394001c2c80c0c144c0349008c0d10081941c0c1005070342d0b0400c803080d8800c41c1c0103018950340101654003814041c038003d402801d101012400b5000d001300001e2146 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 382161888 1250 382160638 382160657
    0x61418010b0c101406190b04420f08060a050f030a050d170115120b01030b151e040602250314010e01050a110d1505130c0905010302071101 61
    0x1040300300f064a00141a0410801c80c404d00e0041030501c1c0e06066454511400e003002d00e00c084108044043c008840301050550f00e0a0714145050b801c0f40021003a4152049800440e0140403000d0000d0300955000c1c54016400c1c80c0c0e512402610304500b00008034108a20b1608002c01500e8243c050020740340201d59000c010120080064a40750380c0c404002e14a000d568003132041c00750041ca040c50500d915440300e0f415a03890748526595601c07003c10003400503c034172034807c0c1820015442040001018940031980090402c08a034500c4241c8070b010711004030014181d0014065000c20900c04031285100324038140c82d080000317580305500461480700e2a02410512140855010b03800011548191441c3c2180d00124041e030003043c031400700c000c895080c540001c203941c00e01d104200d080d60080012a0410100e017091308020850031282c004482c100c1200802d803583c03005904120044400400308115141010060800c015544003606141c018000b5400265501d407114040000a20b000c1e4402c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 382163138 1250 382161888 382161907
    0x1b0d0b090106170d1706090a0f0b040204140f030d140328020d0606050406090e0c0c010207050a0525060318080a020304080618030a0503090c03010f061418010b 70
    0x60a15901c909881d80e40d843e80f40101010200c0c0300b003516050381d2260582520b101e4002503044408550741a84024400002003005540c1e6101e0b0001844880002495503128004a030480e0310030342145400b9078401e4180001880c2120170754020741e40c01e501408000003c03072409009001c0a9011000c490f0000c40091402000540d43d001241050b591541181d29070b408410001c4d8004060b014010341419800f1a00a006a080750704592290780c07000750542c07070300520411a20001c0c041c3c40302035104020004600c40f0900203400c03c0d07070207030700984088650b520385146050304882820b14260400c00c07004550051044100c81210050b06012a003c5030900c0030568495600100a0007010b02084902c10660f0000207402628004402c45503142c6808005001c2501c81d0ba01d00301d03656104008082d1030500c40d0014541000d125002c4501050200e00081d0035102146256404155500d00402409182c98190b07544094107568144e4103861703041000701900014004d940074003034005142000d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 382164388 1250 382163138 382163141
    0x8011e111615060e041b0e0703020705160b09100305040b180120130b16020d080d111201060302070b01031410292707050c06040f051b0d0b0901 63
    0x18801c20b07882d820403030282c58807114040100203880580c1d01103a085d284681c1080380040410640300313208800b40003560340e040210060340c0081411500c601a142c3c02461001600c0e18507805043c810740700c2500c070000d140a0105506c10140b10740b003054100b1050002003000d0064054001000130358904901c102c960080f400351940001b05c1c0d1041d407440c1e40d60a94042c00101500b48882114041c01d105540c940400c19240500900300c40782e04100eaa201005160a04030100c485104017070490520321514100411140c3d0f110603200d84a034000341800c1c2000c0b004000074054021400c0450501103141c07640c0c10b03480b0050100909000051003a4180d410040140241c03100303645505000c440740c00c0c0343d03a00c40c0310482e003180301d10104040d12100c26460080300001054030b141160405041091151640310803002e04101c040c81410007100b10400070602c2014440c500996951840c504603181c128034200040e0540510900d6504000905d580c80070343d8100103980143c00401070791900e440c45030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 382165638 1250 382164388 382164413
    0x4030204050c070b0702060601030510050306010e1b040311130c0e041104151d09010803030708060a0b1204110603090307031d0603090d08011e060c0606030b0108011e1116 75
    0x10400203c1108006030381ba0b0010301b01d03200703820031b0380c00b48625100e540c00e640b2403c0c881c0c0215903068106a0041c4000b900c214800d80c2c4c003002d50359424041142c0c40380c9010720740d44a90410360b6200c1142e485580a1b0a20f0325003c10990b0650a0800020600100081c1450b41d00000144142e840f409122900d51000c400d80703000c0d010220300040418400704000d80354507400b04800c801a407240900d40d016107003a402d101d0481c1c0b501800f4600e540d850340411a02c00c003004203070175801407002101242900e0008081c1c544202c4010b00c14580f420b203070510711500006180c3e41846000c0400030401280d0f8084290b0f0b610381d0781401d142130b0051358000c211914004500c02ca03600541c0c04000c0045a5030001001c0e01c24201076181e400e41ca9880342d0440c4090001c0d0029151104100d2108202d424400c104100321140512800140607031250350b121951701003030740440220780d140c00983d03035598440701c1400038a1344210700400c420f140107150015140034064190f440040418402028841b240c403244 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 382166888 1250 382165638 382165643
    0x10603080a05040906050307080303130302281509050304060e0103060902130e07022a030c0a030305030901060501110c01050307170c03010317160b1b271504030204050c07 75
    0xa0300c0e101d030180014400d030020700c80c580308542444000034039070502080c1841910440406186150b031280d03441c00f100c0b4a114000c80c114845c414203038254075020410640c612407141141400344115017441800e9120f580340c290f20241c034101d40500022000001c65045071038504100507840080c0005a005000e0b55210556403070000529441d0184048225001c1d83e44400c0111a0780d11210812039507800c0200a130707803440f044060100c42c00805c0780200d0001ca04000c08903000010000d000c00d0703850000350f0044010801c08014800c0d040c8083c001e10029102c00c1c0f0f8604c26010303003105900c0e030701c902c9410b119050000000c0801c1056124251500150080c18890200303803c1600d0050f4540d4002d00c13050b204407410303030318402c1e00f0356010081781c0e1000811144000301031442d4603a01c030b0382c5801800300c1d4458484421020480c402c148003800b0300d4020003214034680c0003805503c074042204c140643e0b104150305444413001c0480d050603a03007582c1d0191400946640c60603e000e0181c0b007145000b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 382168138 1250 382166888 382166903
    0x70f021c020717011409060f0411041b031a0d03090b0f040f15030b04180605060103020903070920031603090501090b090115050306090a1106040e070203031e011a070302010603 77
    0x3c9800f00c801508920000b03070340b15811000079a0f50300d00c60340d26107006545488031200031031f000c94081001d829080003900b1000f4070000f01d90540c0080d640741e00140c071030481c0109440d601c011680c10540e0604411500c420f40d0310300fa1400c000d0303500a005d041c0c0c130b0060210002000c1500c00000d050242030750090320303121440501c4180c0300d055440615140403506400a401d02041801c00e003401e01400e42081000003140c007194006035a00009090000c2000c0c4c1016400d010652941e6000c012050062030b100780005800e120000c03a00820071301c051507440883c101001440704010301c2c00300954001d1180c4c0f4000170009440d103072040c003605014402812140006091101d039282c10f505c100b120000720300c10040601d0343c5206244d15001d0460b000324841d08440642c0c4046052284510303240c80e4001c007111300c2d20352070701110100300c0c400303540d0800183c0c804800c00c44c2c003082d0380754003003040105941c0b2041030358903007235903010400c183e1003032000312050101e1504209030003500400003a42d44850b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 382169388 1250 382168138 382168169
    0x228030308100504020711040c3506120a0f0f0206030408040e10060807121805010606020f01050603120a1101050c09030106090902030601030b06031204030b0f070f021c0207 76
    0x20010700c0c07074105403441100d0184403a800070b0649450b100300c40006901840c250b5000c4400c1007040001c04d840c6280c1000d004444401031341c5c4050010b903084091201d401d1140018a2202e0190301c5d01000401030303405040075541114950f44009000075541d58044d181c16401100ca14080c03100103940d450003500030802000780010480c801028100756a842c0e04407560035039900701001800d04c00d03440342c0c0c4007084090010404940c815016014041c659810101d50000445110f0040040c46038090f01d2595654a040c021542e041c8240240c00146c24001d0125051070710020745c40d600d6402e06d001c3c80800004640c4086801005940902c420310b0b03000300f04601d8120803824660340020f8200b8031079440e044000c107182c1100c0c81149040d0b6009001000d5a80c2160b842c0351580764090000c07541441841c41100c011a07141004001031481460745c0141820500c03c0c10420010280110060009418482e00440e60005800d46088604d1a03807042c1c4511911090f0f050603419007184481118461 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 382170638 1250 382169388 382169393
    0x2b03020c040c050313030516051b1011030d09060b03031b070501051305040b03010e030a0306030201140a0c0209041e0b06030d0806010801060e011403070c050c03060c07022803 77
    0x9030044049105071400d0102c0110501d00f10b0342c42c401104c0f214190038000c008280403038407031006000741c4086e0701e05490b0f2000700c548079103180807620040f1402c0d02241241d00352140c140006540094419414002c50745220044000d07140d01071207407140390b1182c1d2100b81c02c05100440e0403940e2004000313002e8036680e01c41140c400d003030120f00c040e0680840c450190700142c036510680c00c0b14403103100b0022241c4080d0420081101900c4c0104a00d81d0541d2104908000c0b1441400100307160012500c00143d21131440c4005004811340050002c1110700900c0080301c002c1d0854000c90345a9412107440d00789a44624114115030203103084810221026130048081040c196050340c0910411011100400801d5400f00c81c10f0704c2c00c0b80c43e035000070503000040020328082d0702001d12100c8141894a40305960002c0f0007145c1d04106c0b41c40b40052103d418200c280401405898040b00381540a0040c500d000940e0940328468031038000d0082d8281007a8202000107600d0044400282800041c1250307501d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 382171888 1250 382170638 382170643
    0x7140f09040e0d02120f18030c04110a02010b0f0a0323100207060e0c010e06030907030819120501051e0303040308160b0907060e010c050c0a0803041502060103112b0302 74
    0xd074200030140c03180a5402908103002e0046e500855200d15035245007000701d480c5003800701d02450340700340c141c0700314507841449903180e005001c40c0c480802d400c507484045143e0300034207440d0304000c01c03805914442c000128580714460400203076034102ca4610858107500d00b4078260301c020f01d000000ba0f030041103e623000c1c00c1d046400907c00140103400074059094071607441e645a54018000c1c501155240205540c0c5051410181d64090041e00a0b92455981e03a25991482e5212039034807003a00100201e03001e00c00c0e030011805814401c031144100070540c18140840c980a0020300c56503064004a0349840c2035a4041080b40c004e56404404640c40d595403a05d20f074295a80038030304803088030490001501c1070000107140400c555080d40c0d014040d286000c01901d5138880401d0903142c5000b202c140780c9440e01d54900ca000140070580045030b42c1c1c0d1400c0b070708070b5001000032603480854004000401c01700d00d0f034000c400ca076540e04607905644650b00350098000768048690354450308030034400200030306401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 382173138 1250 382171888 382171903
    0x1b0c0312031a06030106030902011808070e012909030309032a0312121003020405041101030c050405060304080906120a05040c0f05130c0207270c0807140f09040e 71
    0x11030720207000812080044000300082d03650b865410603003e2004004581c8240c000849040c0181851449100c120407030358403403440c6401010040d40818000c1040e4070110f1038480c010000030b162050b88209041400c444a40489501c51142c040450490505d54041c401c03134091840040c12280584420f046081c03c00b0f207400c82d0041c4400d4181d94130b080ca4100801c0b8928024bc1d000d03121464442411002c00140d0000b40220308000340401c004401a04c40d807240700c1c02a8000c01c0c0600e0751061130800141644d50308049242000002d02c403c010315203920050300c1d082071f480081030b03407aa244c2c0c2c1c0c00301c0d1160050b414210120000081130200125155011a00560003441c500302965101e00070405203620b1441290340096100180c1a280741c0958007800340e15206206942c040c0ba5202c56008880068200108201020b180654001d0800303202d01c521400490424480503d040c60010704200c0c1110151142c40c0c0000545e0450075000c08200d6031010030051042284280296560790b88251 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 382174388 1250 382173138 382173173
    0xc0424081c020c0109032d14060601091a09060c010c1808010501060906081b030a2f0304020120120909092b02011803020105070f0e0904031b0c03 64
    0x607400804201c0c40400d06005082d01a120204014036564a419509100c1002c104201001d600904103407100c41a070922200c0c0075284808605081c110b00c00e05042c2c001c0c0842d418401c440100704520200b429440c03051842101c07859858840103004100248121a080310155207010090348105c1c0c4c000007892000c0480d1070101c001e0544030040707142210000e00614001c01c000c0072040000c1849000c425a002c0d050999507441000e074000750380c469820590300030600980700e046007400e040061106503c440c2d240800501140c00c4075940c2c40c0e06100203040a03040201400300c1d44000c0c3c00d018a45810404001b040b0f600c1d071a641c10351501c01e0f4012400903407051400b20041040d0400c0003408040c4410405420141c452554041c0400550881401d04c195500d51040b4880c00242d041030f01c003118041d400120342460f00c1c120051804103000740702c03410311104070001406516102c0082341e000d54582080101001a04030103078849a0024005000d0413540c5400702c00c000c08213480110610 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 382175638 1250 382174388 382174423
    0xc0a051006030503090f040e010501030308011e050f10020f0f0c01030c050c07090c0c06050a020309071208030601081b2206050a0509151204060207021503090c042408 73
    0x10068211501a6019440b0152040c1d000388070034a603c0c42c100c0d01c040700904005000040c2c0c1d8540d0120942910401d070700035004114a1401007103502105400001c011508100101c40300303082000083d40d01455600040c02510b21142c120701890080141c1511040b5003001ca84400404c0c41081e695031248041d50381c0043d0400c071115000070302401c15a481c9418010107000c040e420442d54200400030300c0c0940c010000c0111501c0d002c501688a41d50180c4048500984d403490070100700c51070207a030365102d5031400c191421030002280c2c59000b0349130050b00910340b201e00e03030311040c4800303070700e00031074100030620400005080780b000101c83d00380380480011060280441da41c84109652501400c2221070209004200400992414803c0f08109042d135a2807181040c80c0c1e100840d540c00c00c00c0750304030ba80650014800d829880d20382441e540d0803140700038a40c6903103801080e507a2141407030603030a0b0081d0b4550780b400b07a403050300d0296203000c2603540d040060030507070307501c0d60369031faa080d4100140841 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 382176888 1250 382175638 382175653
    0xb090f0d060c170105010206040f0620040302040b030307080a050f040b0d02030402040606090b040b130905040804090e0c0f060d090209090c090108150106050c03040306021818061e030f01020c0a05 86
    0x2a105183c810b0304072103058001d001255902c0d02e034501e1540c0030071400c4565541c1c9140009904440119141c100030203480c0103501d450940c03041c07204940c0e800ac0854460b500c01c0c4410400141c1060440721301c4030280c640540c850600600e8034810340115085034840f402d011442c14482013040d406544a50b000b20303014801c00344d540c00d040e00d01250340d02480c50440c3c0c04100c1403000000200007071448142c13010309250015554501c4000700c80050f941203604800008041064040c28020030b80b1511082000d8402845900d0004185880c0ca80e022070050034042200030104c409070740300301c04080d0090003003149450a85480c58588100030b044910501d0450004920800001404508618044490701680e402c00c6015180340c1c004a2003800c10703101c01c204c003000055240c000b500650b401a4041d807002c0e4920070801802510007502c5d403810320446410040c2c50358401004428421218484151042d0603402181c01c4c4000500c1d0358600358000a6444c10410f00094501000740c00303142070b0342d02c3d0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 382178138 1250 382176888 382176917
    0x7031e0c0807090f0b0a03150c09050913031404080c12010905060406021e03090c010c0c120f0312150314120403050c0a0b0310030b10030b0a0c02060601050408070b090f0d060c 77
    0x46c04018040a450007016070610070b02c0b41100ea01030041d8807280c1c200200c12a0380c030b10000d284040c08849100c01425001c251400309074009030f071030808001c482015801c203428611544c0e40c1c0c00701920581d1113078460a52200e6804021361095000c40e4021003a5600c41c90310b4140342020b9409411081e11400350301c0e400d8000002000203483c010308042001d003806500f04401101c4038140da880c10b031041d410000d000903040f4100060504403a00c41c203c44144c42c1c0060402403c1d0081ca00c0c3d00c1400c1c182403216908109465403801e030141c2c6ea2180105510788010355031540317844801c0849141c2010f000902100340600080c608840f1b101c11903011a4440d1141001d94440c0010b850090074840010024030015540210311584100c00d0600c2002d444e607a622035841c64042500c4002004d40c0c3c0315004903815a05001065101d442801d1061504e85841403080d039408491003152521100827a2041055540502142800c20000e121401007191810140000e003c04000480841c802ca081d9120 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 382179388 1250 382178138 382178149
    0xf0604031b050303010306150b070b040c0e0f16020c131b0323090a0204020703081602070b070b0621100c081b0307030b060301060903031107031e0c0807090f0b 70
    0x181d035036100014500316465981c1d074002621041907241c00008103800702240e010410300241c540380b0b025640c0350300c003820309007050061160183c01140d8a071200c00d0070045c00201544406402581c02c4c2d801b1034407003a10310070407420705001042080d13101c4804042da000c1580316801c01000e00519200400111400303090a50890b940c000308140080c01400b25005408032442401c0d912031140e200752007031100c181d0b0004040f0b80c8200001c07404a02680e007409850700114600c201190050f0004084243c2040468415030013210700040c040c00c4d5420000d101911107800c051503290042084070481d030422038107aa01c6104c1d10f00d030384c240c1500c2e00182001c00c0707203c1c0d0441c0c0d016601c904600102454000d40c20107490740010051000d06407030b014002d9103900c56a000358020b10b81c6136540b40b00e03541145401003024100c2803881d021b550282c6030a0000c121280d0015070024280f45c9100c0e01ea8095140213400d0308281cbe803001200340600d01d00000c445003550490811a0040c500400110000008000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 382180638 1250 382179388 382179437
    0x3010f0e0a08130909150c09050f041a030304080a03110d050a03020901020c0d05010509070803031e0612010c021f0c080406050c070b1003020906030715080c0c0f060403 74
    0x1040c952044032040701207100da1000702810529818980000c0d501d81144005540034284102c42038000190851201307031103403068001c00602403030481d9609284c01c00203481030704003004462003030740d40e4400340b040042010b03221000043c024040da91035954511000b910b5071b00c140020303408a007203052820340c1c0d103001190342c0303081e0380035611010b0030080e408108030000c3d040046600d06511500301a5842c59031800c03501d001c468440d000100d4036140c100c04990501000c1ea0101c3c07440e85c403e01c1171081254154651141d52862800c05c9402c940d100c40c001151f07046070100300030300c65190210031b00000d640402c41d039501000c0c41246c40e0020701e610300000304841002100c100080e40520102c0d0000d541e980184d41c00030001d102181c1821007036112000124801d0b00d0f482050034400b8420011424590001680400110301400c40540b405029003501d010040281c000c0040090010f4021569001600c14001442c401c6417981e4800d400500c0da00d003816138042d80170a001c000c540110143d20300146 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 382181888 1250 382180638 382180661
    0x1406030705090115030f060b07060c1b030c11060f0c160b0304031205060102030903100501150e0d1401020d0603030f0809010c0f0305060303040509130c0902160f030e0301060f0503010f 81
    0x1aa40c003400032000c60080812074140c000c1141c445100042d4230154902a200840c05603a001070160b21131030001c0c0444100e200803032940300c2e06242a0000ca034102e004030342c80c690007441690200100c0390005101e480b82c80d81013090300c00c02184105001400156481120300d402000c00070680d122004806140000ca900400080106035a012000c40760b420942d00024180112410890740b903000a04001500d403034034071041c0c1c2d140010055000e106031b1820791400b06042c8102c1d0f0140a01c0400c1c00c6069122024100507405a000c0c1c0e00131800350f0460700c40240c0318004201c980d0700d900d0000c148608000800c00060710500c041400f0f00b0b418491310081c1c466070340351450704282a100540141ca0700030001541030206010004050322540b42d0907104403a4041500350790b608078508487c4000c255001101114414801801300c4000c06503e103000d1500800307400086594cc0c941141c0048090103000e03055420706c040040c0c440d141ca00c812069680841c02130000190b104201400c95601c508007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 382183138 1250 382181888 382181909
    0x3090c01140a03180803090109150b0f011404120b01091b1b0c050603100f0812091e030f0607020c010201050f0c0a0c0813030c0e0405070b030a0f14060307050901 71
    0x34000b06a000303500410440c010315001040344400c2d511501d41d203800444003984a6510b8010610801039001d06c50898410800d0040084182c4100806d2035070021094a5040c001c001490000440039070302a0b4005109180c5900f0314815a07103003003030300e0100a1003030030503240c10005268115508400c0c4110301003419601c0d00c0740b4020500c450003020b10003110a640c40c2008000c00b003001d40721031009510803200c1c0c000c55244145800310504100702e5541c0140600d80042c400c00868481d414100c4485400c111545259550801c2c0494000c880326550680e151081c0100181e00c100c0100340c40b4819400340e000d403148801c441006a0a0703503412608102258501c0e00050b041d2901200540340c240354500c0d205aa40d0010f40d6140c40941c00209042c000c0384d050b007002c004101d071342c1150001419103102c0325141810b142d80d03100c2d82d0b401c1c0e601661503401400700006014440c1513000070401c2869500c103005c3c18046c5030b840c42001c241078514501034018802c011500d4102488d00a040b200203110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 382184388 1250 382183138 382183147
    0x6181a04020f0d02030c0903120c070b09041b030c0306050607020f040504031b050f0712031b02131a09090d0206011a0d0e0c18060303090103020d0b060304030503090c0114 75
    0x8010082d0b0000b0004411064180400c01c0e024030b940c0301843c03092141c41043c607520150101014602800c004043d40d4850081022070440d802c040f500204403154400711640320b890440014004c0c0000300c268048003190725012200c0355030f06402c041200c41c074640701000505d0716481840068440d0080107500b020304600301d9078907410254001c40c0e2140c000d01d007802800001c00c640c3c4030380c00c02903041614245e1004400410309407003842200700034403482600c0c2c81680f10541e005460211900302c0d11041480c440022819511005c508011200040a007081640859103407440300030b141c0c1d80400e006001f1000040e0009400040d480c4079400c1355001041140e01e00050004541441044030000b00414040d001c01d6452500421180d400c60202400300305805606011010130104103080142c4640e406006050b100417046544d0880c007882c000d81d65081040c0c0f0240981089400141c1020000041005040c2e0080103140512101e40556000c108041d004680e440d201000e015103411b0200b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 382185638 1250 382184388 382184441
    0x30703091214040b0313060608030705010506011b060b01090305030c03130b040305070b0f0415030212150109170a0b0a020a0216030804090e19030f0905090c03010308070305120108010618 82
    0x2d141c1c801b0341e5051181c16030380c2596500d416502903a200b44001e900100d40302c020040c0a000341c0b0340c03008080c0f0780f9080c401024810240380f40a8568080c0c039403030f40d9020124860740300352040c0e000f8503048400c580d600c14139040d0669596000014109820708411000b04850007100b003120100e940000042100030b0811308890802d60103014080b049070010440000d2032100e211281e82c00c04c80c280c60050300c403c0e20303180002c0d090200605501d07100f101991f070f01d41107030703000706d0340c02c05445c0030b004000710817003007080c04a18040c06418050480503204081014100c0150010700300d1481641c252a0001160f124140d00504207000080401ea130030311051103820b58a520400c07071008503000701c1301b004480044401c40d40070304800903400a0241111908030b56000b45904008050540750ba000d1480d010045600030700046c00010030035640051894240361185007600c469410015025185595503a0782600805d854454460319020b2165201c404942900c10340d40103000c080c174040c2040c18901c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 382186888 1250 382185638 382185659
    0x3140c030c22081501170604080a020a05030403200a0617130206210c09031002090f091e010f241112030417040b071203090803070309121404 62
    0x1582c5078103a10b801180250b0180140c140302c000e0054402810003440881d070003542c01407050308442d82c00d02c110303e2407000780100041e1072640540c10480c01e549030303003107a0780c120f0605200201c003034054400031502000f07004061104480001100031810424240d51044c04405036061003a2004516a80305000a00c4034030041c81740e0180f541c12680200102c83d82c00074420360090558059030190024051512100b00c00141c5c1e08042c4001c04a801c10000500003541e5541c81d601079803102d5004a20b484460320f400410a10703c0c2c000400003c840d00d00111192000e40d03102c1c501e1000300c410800000b803004101c11300041500ca400c8080146044210b5024281c11510603108040040c0c105840107544424000700c0d084092034201c0a68904080c1081e40440c640a68174018030041008104a141041c000321240941d00003c0071041842e226130540051140030b0000e8003481c000810021101c3c0d05910024483e07104084031b1440c080e4021044030900e4940c030501c0b503030002c10441800408480f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 382188138 1250 382186888 382186897
    0x406080f1504082703060136091a1f051806031f061406040e06010804060f0c03090b09010605090a15051002071502061e09031210050103140c030c 64
    0x3c2c10801d031804a440004001210310a0b0521a5988110310a090750f440d090020034010101c110612071041c0c04919151500d5140072501031030640c2e01a01c842554003940c002c01350841c4c119480c150808400074080521602c101c0341710a000c3c0c2109080c82a0b140c04411101c151036010b000d5440b00a10724504803400d11001d04180e40c0343c80380074054880c407911200c070b8503c881601c202c0811a1442c0c01011324203804151555031007001e041c807050003980354410102c1d901100c00d02e0a02c3c81d54030f440c10058004d03c130b038000da40201402c2621000c80c058140c0c014990a62060071030010555034111440e00f22020f600400354410604400725600c080700d0b030051101a030810a0025141c1c5e61000003402c0f00d5071165564001d604003000821440820b601d00c001e5601c6540040c1009141c05009100c0b0315200d40c1c1039130070405c1d08401003822188200280d551a2520301580c60300c0e824100001d201b0040188119400281010084080015003a42e076501071030002d60440d045d911203040d901d240781c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 382189388 1250 382188138 382188143
    0xc090613060303020f0c01031e090f080301120b0a1e11131206061e0306020d0e030313051209130c0e1f0201050708090a1b09060803090406080f1504 65
    0x209a40c01000040e091040320020352094000b4984490840f00c035078101800c4d01d2140b0b051618003c1c0301c1d0901a644c08145252403045070000a100649243c1042424441c01e40a01590004000811182240c405e22081c00b400381d0411001d81d5914200c10068402400c0c503800848001c030000c88940c0101d0b0094440d50011006147c14075150001e00b42c420141ca40c000000081c0000c000320a1004034484c400c0a403028072201c040860794102d10b803c580386240320051003075038001514518842c075907000d81001c2c00c8107401c0c1e030741d00e040c01c114551040088200035108d03406404020690114a07401311210f5a501500c070380101c485807002c00c802040401500300a0100c090703042442d580d81c0040d00444c03d01041400103003981180c00083c02c66400414280034041034209004400b2400188010785607880341000043d140031403900d20104405030b00a0f22841c0c2414400310f007400020014080c0c41c04151402c00100d660349611315918503002001c81c00a402501010040d1098910255449030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 382190638 1250 382189388 382189399
    0x406050a080429060f030304083309010b010e0604140105031009050928030e0d0c05031e0111040501052a060a060509100e0c1e0403121701080c0906 65
    0x74042c43c041c4001034000c0188890081c07820801c8070070301c1d04905400c2018020341c01107043c0b5081070f42c2c080d500c22502c0c1c214440d044110820303a200261000803003000c7d0740e0307080b010781ea5802c14040b114083c00c2c9242400f03000c208400030030b9040f820a1429074007140c011301c110095842c00c0c10b0055035076030300c090000d101e03601d448070001c6660744485c01413074001c440d08d00c001d000000e02c0c10303a01080094142410070040070003d68800c08203500c01c0034404150b6084454002001241c50720201640c81c0341d1005400d805941c2482244149410f56140b0040c40c000007400510b1113100245900e101c0c501803035002c9682803080e10000c81c0481c80b602c0460041c0f00e03014290202c1d515507030745800e02c01c0311541e0a17a526035606002a040084180d608014080b0010f180a03007011f5202c580f11400801d110500840403070b54107450002a02030720030700d401708001940e0761a00d034100051000a0b8040c10008a02060310f1090128031100c1100e040311454000f5100c170102c1c0404001d0195006404c15601c00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 382191888 1250 382190638 382190663
    0x603090f0b0705120c0307050304290106020d021e030307030c0c0f061a1f08070e0604030b091501030c03030f050f030a050106020c030a080306040e032206030506060406050a0804 78
    0x880740c800c00e070301909060311601d886641d6142d000d0b00700d160090080074002400d105000502c0e80286c152500240e1001d0312009014090700301ca90306906040040d40c0342840800005090307038011503076040002459080d64101103803960358010200c5a050311010642c8200005107072144258400b8090b2202450a00c6800303101e6103424100c04c204403020ba640a9a03841020004000c401048412000c1039581001003a00018080048016507542c0001c4c40129800115840e124a00215001000802c030039140d603242d04081608540880307544d82c2c6845003160b508003084491041354104c03540328112044181c01d42e501240c401d04400c0100b414080d09004948000005401441c80f48030301c030174002181d603d0500000d25082030969901d01a0b00404c038078034081503422045a61181090320b0200c0c81d07080d050f11162840c071038100ca241500d2042a0754848100045400004070f0b80c40e694244820307120380c2c042180c40d10503481540042142001036800140c028144264803a01803041d4803000f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 382193138 1250 382191888 382191893
    0x3020a080d0b0a171b06040f060804020a0503070807120c0b1c0614060d181407090c1b1104331208090904080d0c0c021017010603090f 59
    0x80d50020048286030a03140c0c07501026500b01030059100400708070710b00307612820300d0000517038640c200c5001a0038242c1c141301100d0441c1c0ca4200c1298010714100064101d0a5910032001f4206c00080c1d504034429018102d00003505e207400503190040c0c900b0710020b00f2507a0b2503c0034540c014aa500d6080b107034810842d50000d080d0301c000c000f9203c0f0010b001c0203031002488500350b50080350440c3d0414540c184045002c042da40d140d06c015600c0f00444650000f950350a01144222005d03158a0020003d40d5411a02c01d1121808500402201c5618505100b00e140d010f20648060800b0b01d5042103443c142c0700ca440204600400c2003c0d2640f01500016107403c84600340001020644580a81301e80e20807041c07000d4000306c4588000400c4008400750001525541c0c00d4464407030240c900340700c3d142c0f003008030703061000d158100d5500841c1c144040104008440000d8011020640d0a0b841350846054111140740a1140d9144960f0b0481091600c1e130709103c01500100401c2d03030181d031780b0300d500440c0340700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 382194244 1106 382193138 382193153
    0x91404050d0f0915020f12072003061321021c030b0d080a140d06030b0f060108040b0705040b04030b06090601050a05040918080d05010509090102131203020a 69
    0x45104204a0403403811b164140800098042d1880c002e0130070105000402c50340344243d0305d11100c074900d0701c440268032189264041d0907811a10006210200d132940d41c5241c03501ca000c90140c4d1180400709a0560140900c110004d607004140952400345444408502803050385001e104007481100481d001220001e0010000100490490521400740607400c901e12645502161201c0b4151300300741c09050184816281d01c0b006001080c480b000f20011103124001c1a1502d071820340b25035071030100f4884024079031001c00c1801d01000c103400c4600c20045c00214050798031110103007402002c0000f1301e5006000d00d0705102042041c64080d64012099508660540c600000d0b406450395103103000030302c1d04100415140c1d00040d0002c929046070311940c1030710703001e03544080c15582d4242d60a00b02e00c900c01c84900380e054010420440815024141c40301c0c144a841560300a80c1075544904 = true := by decide +kernel

theorem cover : BRFrame.Cov 382014388 382194244 := by
  have h0 := BRFrame.cov_init 382014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 382014388 ≤ n) (h2 : n < 382194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
