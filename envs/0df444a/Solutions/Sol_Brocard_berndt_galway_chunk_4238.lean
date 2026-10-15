-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4238
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:58:16.000727+00:00
-- url     : https://prove2.me/submissions/71423ebf-413a-436e-b9d0-e1482be7d886

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 762050359 ≤ n < 762230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 762051609 1250 762050359 762050389
    0xf17040b0c0c090613180209010e040b01061b0615050604080d2c010e0109090615020c041803181a0901030c170606070203030405030703060b0925030e0c 67
    0x4166102100d0003030915260300502c02c54080c00f8010b04122059540720200f065088071a280440e08106001c49804032101e40f030b03c000d500c915100000304d00c6159100095208074030400486500b42d0300c80d0800e881a1116841c0c042d0b0f1004e4010580e0000343e4250030031b401c0c104514007a43d66043d2a50700060b856001178011503c0c070743c801c480d100c4400360f10600803120710305e4800303c1c40841030503908844000000001c585061003c0c7c5520300e10700d64460240000240214641000321548402d00c88041c50305d002440f90051140000090561401d03104400f441d210032a8038100d000c1403a9003e8480d0500401040715490480c4000683c81450410580400c54423504c1c0030350b50a840b00002d4102c440340000b80c0c040181800b5000079415150740030303035000f80c4100c3d00b40d0749400c52171001915611030394200c2905402144000010040300740c00244200500316410306281d51a1080407108800846250017400508200151854000e500043c421502c500540746940203140104141035400311078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 762052859 1250 762051609 762051629
    0xf040e04060509061f03110f0a060203031009021215060c0d0c021f080604020f0405060d020711060a05090409031205280b01080402060a090503060c071707030c0f1704 73
    0x8001d0740f490103110b280d40c0082c5507201c290300d40d0003000343c0f100281c0f8640001810110741010720305050755a6050070807444c10061801480507200c0130025100d400507644280030420003400032404550f0b030f009403007980048080c09101c80e550590050710234007020965a420410403c06140e4160301804801c0d400403041e1241100d8040c03500c10311461030203805640300640801107008583c9a4010090707138120404a0380562990308655a8401a00c143c0c3d1103180d02c0301c3c000031100d0500b2902d80160807401e009031548404803154500b40146440340c102c40d0400600702700a503000310f240ca94840c141e100d000c0d20b40a500f0249900124040b031300c09031200c0c00380c14010310001c0881e0b40f040d0150050040300400074400107a05030006411400301500080c0f1a69020802e050758a104d52151001040005c00700c17240c608190000c0e48803648103c0d020340c2c12041409480c60311401580c215065207515030388081000c22241c840c2000840344200440d0125401341484040c07642ca60050801381045030300c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 762054109 1250 762052859 762052861
    0x3081612050c03070b180304030302100f0213090507140f0c16120221010203070906030c0f0801052107090209040e0715050c0c04020a050a030e0a080f0f040e040605 72
    0x624101842403500200300704070701000003410110012003502e54080c1c1c05009030980f40c030b4642140124890402c9113540303921011a002052580c0040c00c41a440d1002008104c0e207400d04090200ba441076091110398513881e203000700b00200c000d074071071a4844502c3c540040300381700d40721108103643d21080c511141c880c0c010803600048a01406640c250103640700722441c2c0649420f42900703082103d0080a40b19614800001881b080030100d010680c05440000b1035503498020409850344c10140540d10010f4540244109107070b00411506810761803948034490319038a400d0400680002407110890172207002400b80d2a10381e410018400034080e1070f030015844400100c03e0004941004180446903400b450041204288186103000c0e0b42520b0302e891695080c40180903441c1100714500305801030300c00210b054590b41d00078050f02240c0403d44e0103000c1803401401146d03894405c040701608449040000120203081c80c402010594107182c0c40314101542c41000451044041720251184c5803620 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 762055359 1250 762054109 762054113
    0x70f0323040209070c051c0c0804030b01061818020a0302070212030301060e03010902060f030403090e090c121506060c010902130e0c0d030f0813080304030207090f060315090309030816 81
    0x4140382e1392111842ca440e003007841854480c180c0c2e9424007454040e00c19030400b40418000d1003015681007484e0804d52aa581d2680d030b10300b102c560b201c00d10070314002440142c1001442000e0070f01c40d8044440085c40f00c441020344403481c400039030021102a042c90f40c00c1107060010313112010001c0260750014080c3d51298034040307001d080384540240b26442030349000d0036000140d549909960f4641d0482200ca030312030351540340c2900c2c00a2190481d1496189910400901070340024081d5030181d000e0b11580b00d0452001c02242c2c3e20848040079801440540002900d1420b1480140c8529003a43c40049035050064000c07500c0c030300500000c85003541c2c440400c26500101081801c50240082e10b59142244840d10b00074481c407881d400c420108848200400e400b041440c0a001c2c100341c000415694034109490060f6440e4468031605103218103011542041014511482007180c1e04080c03844078000312501c186000b8090104200c003407120460011001c03d40c440003400da030700100084040c80520301c3c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 762056609 1250 762055359 762055369
    0xf140606071707020604030515040611120708040c0b0c0c030f0d120b0409140105062d0103020c1e070f140d0b060f04020307031508030909070f03230402 67
    0x20001402500100050000108a14010b02240015210040d150100c42c07000814510540d40041c006206410300440c108090081c401d000380e1241c03c0420240344140c01d04035070303402005040480201814000784c4420b015910f06c4d0f5000740b08140ba4181c0c951544150000c0b6086082502803a171305c690000c0142e402c1c20070008014880c804020249a0381c900802440403040036400380c0000d40710034003d10780c1c2c1c482d50003070119558440d075002595408200340368001c1c401203030090300c1449400003207020f00004160400124008a941c101c105035244010b50183d40807199410b0244540c070601c1c4c4000d00545840d0344507d810300701504200e443d0104040c80d03a21607030009582e18104080e22440703581c88225013030710158080441034203940c81b04001081800b0120b807aa030014000000c0002e0310f503055110600e55800103501101c21511012034035500c1c012584003d03008807071100483c0c8040d009109059080400b0300e4081107001004007584800c0411341003511070059000e0a010442c649 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 762057859 1250 762056609 762056611
    0x1205130201122007060e192901140319030c03201e0f07090e0115031a0925061b0c03060c0203070212030307091a0307030c120f14 57
    0x3054000380300c0e42d030300041005100e80e1007420303c903102c400001d40e40041000c070f80c0203840c50034400400d45007003400c0303403a00ba041d141d00c41104480c0c0000c00a8510308044c0103a003c0080d1b00d640c4007100d00e10360309183c0c0c02c08a02842184e0b403075041c07141490020889000440c00400648265195001c071122072501800f103030a01c40b000244c038035520840704100340d00000c189641c005400c000a0303c214030301c600c1c20305004622601d06124040e10740301144001d102e411082d182c001c680001c1250329101c0408112030707001170100400500c8506001c091140d0180040c6d50004a95400e942903441501180e0080b40005014420400031840c002c01c04607401c61400d400380d2000241035914905546d131124002100303408014411903035000700b141c2c60384c403c0040e200c0d41a40075106000c840c0d615100d06135290012591032000805417040452207100d203c1008052502c070465507800c6440340c070713016405400b21001403010003c003201e400e40711501500640f810203002c2000041e26100c020b01d05500010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 762059109 1250 762057859 762057887
    0x80d110307120810150305090d02070303020a020f0411161110020c0108040804051e04050c091f02120706140601020606030a03031a030d05030708010e01030c03030f1205130201 77
    0x30711914011801800340c036810181c540ca0b002c01030b983c2d8500131000d52103813508040292800100c602d0425500741e84001e015a400c0b000300c8103856041365040340d82d107103e4000280160009024000141412010003089820041c00820178402c40c4103100b680da0000042c6220f40d1203100104000c0c4000f0191480390514159000b1300c41c1500c0d0348010390345080010200f07041090210018061100c600169809804000d0140409954140301310500f0710307502500302d05c0b403072606010500302c03a0310404440b10324002a0138110075101c0c1c8902003035244000c00c00c07441940a410081614210745100414969201d0080003a00b40350381205260441c200070605415548501c05211040d03800140030341ca216850318020560000f008547c410740303146285150303018440d203001c10450035080000703144a000503a460305030985e62a450401d07952028031029102c0064060148003184c41441e540c0302020107802c1140303031540002014401c4031021540304c100803001c8448801150707400411480110703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 762060359 1250 762059109 762059113
    0x408070b011406030f0a060f08030714033a1415010e0f0d021804080c0d0507080706020f2701120506130c21151707091a0a080d11 57
    0x108404082042131101070401c080c0e01000700001450201540c20600151412108660700c680e51218603d40c1e036001914200d8000100d00c80319144120000283c8004510440038031110200399051406104140c003038440c40c1c0101100c100805800a004145002e040c0c0c1103004194503084201307541c00c140c540300039410416203120f00b01455a0382c0703a010715903030300440713400284404034800034400240314941d110b0b414840404020503c030540002d00701d58402e501c161740c9100550403048401d4403604e08004c28106c401d01208000c82c0785030380030703140d01040f001c0c0080c41e201245001000c0eaa40807643ca01c484103041035410301550f404001c00c5207030344110000303000905111001409801c0007104290740313107698001b03555400e0304c1490740300f84076074440d0886001b0b842d1061100c0c1c043c0482c0f00c0350148804d84100002003001072001461071351042e14002d00011780c20000d05501404210100c1c7c0c200f040d003241601c1807a80c850002c1c000804203400205170305080c81d4406002180800140400c03a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 762061609 1250 762060359 762060389
    0x10e0318010f0e150408060c090901060804080403080f040b0d0b040f06260715121a1e0604081605031018060905011d1b03061e0c0906030408070b01 65
    0x440e0442083c00814400326003814200704c9030100c0600d40c1c0266408010315100d50003d0203c144540b40081644440980f940c010683c0c0b10074066070548804d840040205d00200820804078807284017401c2002d5400e003242c2d140039981d520100d400e4204e8098000425500e0014000501d0b080c4600d035000211720105202643c81c21204400c0038003840700c1c0030100d529801c1c04404813074040c040035000e00a400f003010000500c07003100070406072030401110200c03850440c04040400210102c0c1c0c4159030000c2c03509040346000901d00c00705079000d80d45c00340c002ca004c1c0004204011b090040b40c09200c81c44272844030252801080518100f031944405104030700d000d150301096003500c803580500a400660204a280035481c0181c01005400741610080e10040019040ba001c0483c50403e400e40048103056002c0c460010103880d0328065400e101c00070030b86420654400e103180b03140c65004070140d4105051600000c081490b9074400c032000c81d000d40c00080c46808006c0c80600990140440c40c0d000400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 762062859 1250 762061609 762061637
    0x7180803190e010e060c0313030b010801060f0b070f0507080d0507050c0a241404140424090c0216260f030a0806040b36090712030c05010e031801 64
    0x910300c004039a940250070000703200306c00b54010400c903141d52032891031200d21244d40381000b0000c0c2d4000e0040e402c4a508180e400207c040311420380320142e80c800720036289000c00d5a603075240120f00c0580b04480a009610340050b8080c1b060006401c60055911490390700c0e05603140c1706090100d20034903e03100e00b4046106002c0040c0603170b40c02c48030007000e810105402c510038a05a0720408a01071146000b6800100840e2a0820b80c040c1420b94405039001c1c01010030300003103882c51544203d1652003000580c40f040190f2200c0c0c0e0000d41075186540142e0305a110360f00e111102d01d41039504404c601c001c0c040390040800c42d1402450f00580c40007000340c03244601d24100191203110760b0b2030307440811015001090003a900c1c0da2000c411030500400c810034200b074080b500300048021034030186003e0181051002190080d0721000e100d08580e00c01ba00724241880c40003000d2900ca69400e80401100b003a64100041003441440c1c650365148004503241c00d506081c400c1c0003075010b00ca4030f04000205001d400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 762064109 1250 762062859 762062867
    0x905030a0c0e0c120916050d0f021012020d06080c090c0307030b2806030507050705060a0f1e0b270f07110d1d0405040b0f07180803190e01 61
    0x2e5840304640310405031550a02c81609018905855107403005040c2408841200090800d100007807505c90b00d207038039590b0810880000c450f21809032807034480078010001454501d146628070f100605010814410030a51181281c0050800031010b44da01d070814403090808118080e01d00d141212215164601061b005007280000781001c0103040e00c9819039141076440350b41c01c046291580e150700c0d450f107000b944805040c0c1511b2041c000802e1803c2c0104003450b03c107004403250a80c004c80241055111a903002c4010460000804501d41c1e0318040519128501c0360802d032190f804000110302140080100082c1c1e042a22100d40b85112811000c107031300f0fa005200b603a22413020418140f583d6078a04040d0380b14031440426207182c8c01034050341c0841c903810102910707040d01e800c0c0d4001488400d0310140b100711007064401508000140000820111010040d1544202c45181c2641c88010403034100700c0092490b00415907071380020034142401c9000017100300428a591070040924400c142c00a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 762065359 1250 762064109 762064133
    0x1080a150f14012414130b121603152102181602060f0a1d0319110706080408071b0e07020d080f010605090105070b1819020102030406050c010e0a05030a0905030a 71
    0x4824a0720101703014209481100b1b60034000c200c210a0035980d808160320695a10341c01711011984039101101c5281d83c1c500c03921500007141d03000804030b0616070904003e20086140c421041c0110107000c030015005840f001540b13230140741d2102d0581405e04100c02c00c2c0107814001e04141c0110760040d0704000f440700041e200e40342c1003800e0303000014580c1c04502035071101441070101311207140b10000c4c20f000f041c0012405006265401e5413100e00944901c926961282c0c82d41c800c0d030f03000034100c1d030114022483e004001c0c98502c0c4100200c107516140340c250454034a01c01e51021312400500c00802c070b4490740600c51146400702900d003d1400f8a410b0200b51503001040c042c2c40100900440d680c002a4000c000325040da03074020f00500d40c1842c01c40f0440d80e402001884030a01750213440710300d107500b140b0030b200e603213450394141c01071420300c1c0c20310404986907084402c480071a90749070b92245071120701c24460902090b004e0340103140d4031100c03000c1c05030010b0380d203502840c000c1e40418040070210301c0307894100c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 762066609 1250 762065359 762065387
    0x11070906060e030f0118020607020409020d110312070804090e03070f0b010504050a020705070e090a08030406090c0503070e0105060d020409020a0309031103090303040506070f0515070f03020301080a150f140124 92
    0x23a54540100d130000c58010504020002e42041c0d902154000380039406130340c00b07240c541c101c3c210351102c43d803e21408803074011082c0050038074005110921140400f5001803d5517003c1400b10303402c1070055140c00e16201940e14003072300c02c0c400c08801403040f13041501800398485400c20080d8501805583c50b0f5a54040b11320036103400200000204045c6401800000207807600301c1d20b200c3d128202420f082c0010000f8181c2246d40000c0940700086908011441d50121441c64214254682c030305403d0044c0c40c2c0c0f00148004209070308100201d000f80701071015010800b00b9a0f00003031491254036010784100c102c80c80020480e0300138000b07400c49030740c000222001d561007920f01c6504d03402640b409141000c8800c03401030a40c0101440303491040e41301070030988104000d036100701110200a070b0036404c030301c42801403043c1908004107281c045440072684007400007140000103000340c80300ba0580f007140c0c03001d018084507501182c0100b08450007826040c0c460a0709810501c4038002807040a0720310141c0441e5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 762067859 1250 762066609 762066619
    0xc122d0106090c050d0c03020d0f060815040b0106031116120e061303020d150204030503180402030103170c0a0b0108030a030e010212070c05010906021206130b010503060111070906060e030f011802 86
    0x3031b008035032098041d43e0241600c81030a21098507501102000317407a01c2d005041c401d01c1500c2d6010304180c0c522070113034040c94000340c1ca20010307401c0242c102c010b0701051842e00803059040266600149075640081007103030080076481001144500000c0c00109140001c41c8a02801d210184117029402e0707041080700d43c1103c1401c40110140b030009119040e55060b24542031011a00100b403000200080c1f40b0b00001d00c050110b004044401c000807401b00707000c090032030001040340741528a240401070500d065050110b5408030101d9480c602d0420098100d03040716000811400d600c1074141c0100c840e840102d4000303604040520044140741d0b8130041400c1d00b00440303c3e0011050200a5111003002c90304244195588c1c040f980c6e0f01c015002040d60b80781d00030f48809950907804507480c422015400d005a40340340ca5078072003000444480703020203645156030103429000140e14650348100c0000b400e07240c817038844d204c150008041c1000c0d04d201c0340c003080340d04003843d8800b44124844030312074059040302c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 762069109 1250 762067859 762067871
    0x1a0307020d2c030705060f13090501030506041205090a0623040e070e150c03031b16030f0306050901170d0801081c0e090a05060301050702030c0c122d0106090c050d 72
    0x700192401625030f1026401500020760030b02d02587c4500280301d00340c00145448402544c80c440740d4101c0c0c0c424840036099810120101c1d00140d0000c00c80034004a0310b142003810a402440090002e01c1d15520070070100b82c0c41001a03500090604400101600d03075a100781c2050700e452000e007032102c0c00818400401400ea640400c4035500c2070500c0302440d1410f0310041e140e1500040d41d9989500564244c0311fa0b0150b07100c1e03418025041000c844240c0042c0b02c18020300300301d564040d298802081d10b01802d0580390301022480341c0301c4944560081410203110070800404044403403e0100794a4204100800c002c01032189110009601c4000310442180000c9248162000c81d00300b41d003202c0b40382d445540c000a10850301070640100b402104200d00820440e20354860030390380c0344201c01040c0031580140059072254980030150540c400100c10035202c5400d0464a00700054207401000c2e0744440a0054403000301000b4450030010b0054a081040a00c0300003078090302e02c0c0030703840300c00075039031344a603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 762070359 1250 762069109 762069197
    0x303090415080a0b01060e0a06020d0804020a320f0901030b0a060314030d060602010203091506040914030309010c030903170709080106080c011706011707091a0307020d 74
    0xa01d0800003001040c0541c1d03071a15451801c0101d2000038842e0b2800103c640101c4415842c115112030200c40040c5c0040501c0d1070040ca050b10f00c140e0080007680d1208c09101c0019050300e02180110a80075403185620301540c0b55000d1b82d10a021181e0744038024421071100310074580b01c00210382d0541e03402015500707a654404480e0350240c81c1d00d4100405a0450440c40003100c00000090a400910030300148055503e4000803800c038001200c1c5e1090642c824400302c480c50204001580c2c20031000f81c000314076424183c46140701440d0244604465500000801606d00c0082c8580e12180d203041c982841001d009490080c14200c169001c161094041070225082502844024004281072002802500e50381c59200d80c4584d081854940410034600b200c00d00b08900039145485800143c4429642c2040e80904d03816080c1c0c010001020f0107054440810404888618020002140c1228640c2da203456400241000811540b22003400000f000e54852150a10356071178108048035102000c0d00310711 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 762071609 1250 762070359 762070391
    0x30b090109060c0906020c011d1003020d0501032904020f0933010323041124090f120d08130b0a050a110309030f2b090b01090b03030904 60
    0x70400a10051034441c00c01c01480c3c000c4042c60032505030f5001da41c0c7c4400501c0056038140000540c4038540c14090301008614540001d06200d07003240c0703203001420483d00301220402ca54003030700180c90704802c5100d20303405158041803c40c65071114001c6030aa03400d02d903011850009602e020b80344150b00900028600031301004001c01e0110075142d1074041d090013111602181140d1071141c42c000703400c04c000d1111580642161a0400900c03410444550759291501d0180d91410080c8903803200350001117540b41c90b00060f400d101c01070040c0115070307242c00040c10400c0c01140001400c1c02181d84000e0301404120202c0c3c0400700118504180041c0ea803250803207070061600040050030602603406104618006a11940c42051104000c010f0503840183c520100d00086405082d503034410403000c10a032003594040c0c4001d440034004c8800f81040c8021158141501000b044401c2c1d0380e60714480240034410032050b00400e0030030b0041008140340d44c082501c0c1d20610310b100c4c0c0515250158501d2075180d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 762072859 1250 762071609 762071621
    0xf030712030522030c05102a051308010606030b0d0f022808061603111903020d020304050d09050402040506180f040c2006060d11010903050d09081015030b0901 70
    0x1d040c200301c400f01c04915015080c800502c070255654828522041d4200b08148100a10414070400901504411040078000154510350180c1006000d109109002c15980641c178090101d400022401d1030030050020120340030701602c94801c6244c0c83c01c001c04503c01c4036440c500242c0640d084003000c0e01610f00a407884070708003850310100203a00b000050000000c60070038002c00100c08c56a80881e00c5540840c1a41ca240c460508001d004004000704803a50507120700f1340c0001810058208680d080454041b80c0080350145c03610f40102041c11540c0d68071038003840180c001205c00318145814580815035501910503050180300c07079a500310040c0da0b84d2242c211403400c001007081c402207151820007040c00404611360fc41d041407910700d1000800001c00d583c1e10405001e4404064000340e80c64541440285601e054140b02c041203010010500c103101c40140300b0b0381520f4070803419140000540c40c0c00c0403003030014800c0f072030008041640107580039040104c03600071207001c0b46500c07204001401040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 762074109 1250 762072859 762072901
    0x1090209010902042409051314010f03020310050c0405060c0109060504032d02031603030912230f12040215070b0a0b0108070915090806040b0105030f0307120305 71
    0x14000024030726482d82c00410940d9400c603404415825100e82d1651001000340e80c00000c141404002c1c89130f802d115480101141c0da4501c0071034509107203401d50308402070a03044000c01070f00c1c40380c0030700035420200103e00785035180c40400c000c03e290003d0494518007403401824856000018010402c1c00c003500300180040d0001410000b0707060602d0003801c03500c80c0c046005505200341c500c03000400395a04440c2c000204540155140c82c040c1500a510a10100400c50038165100419004102500300503000100942c0710ac10f06069152000074848002e0310341c0e9401c1c00010041403400e0788201e01901d50718651541d820649444500c001100305007009039582c0c080c000410070b04140034001e00900e0052101c501d04009007007030b40004550700e140c21a13056000c11110041005440024420f5845001d0645802c0003410349a202807420500151070035111080300c10014000c4c0d00e01401001e9540d84203034002d40c5000216640d01c16010344650f12402850390f034400003021501201e40700603190b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 762075359 1250 762074109 762074119
    0x402030c0403060f230f15030a38130204020f0403081605010e07080a02040207030201110a090509060f010806090a0f090506060901050910061110091406221106162405010303081305010902 82
    0x460ad1070a0182c40c00302d00b24420321942c850200d141742008080c0018020458550150034000c0a80c0a0002a5008070071901100780c04020000c0403070b9142c0090460b405002d9504402e215490500c0e50944000207012007082d0480c8900b0004128005100108035038151030243c1c84240e5820140c2c010241c501a00b84109000100401c2c00382d03006080100b9580d0480d001942e90725424244102d01181061483c013180b075050110302d852400e02d0170198426150040800c1200300c10503880251941c07000d00301c586030700c10001d1110500e070a103640c501521b400c0d6008040c030715100c134054010a0f10340c030a8034240403507016150f41400701400340c0016100400414420014181350041039485100c4128015010b510b000c81e5400d25603180c1b150281807250b40b0024031115544445a58906e0041c034983d02070b03004c012078103140414600b04101207019070351510a0072711184054003170804019030045000c0c5000d00500000f074004600d150000080c0b2460084042c5626040b4014110b40402035444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 762076609 1250 762075359 762075383
    0xc150904151a0a120f090204180c08010522050a0203060c040306050a0b030717011d0d080106021204060e030a05060405060115110c0402030c0403060f230f15030a 71
    0x240c401c0219000032a2180400c241c0e81d0b060454a48026010302c201c20000030309689103102c07406507280c105882c0e60b0701e18000082d04030615030024003140c41c41c1d01c00b4030903e40e0b8255100217000c450074010004060003002442146480f407c0140c40d0040105130b900b4060400c0e49100038000200700310f5692941c0a0125100e506252a00c00380a070018842120b0301d600b480d000a0b5401201e0203400c0000c507024004206c001d0818500b441603429102d03c034191780d96941d0b0501c0e540d05c0c1c00314480600708400c2000d403004085511b0000c02c0d89405030040800c2d50300c04803180c45031900385000c4804445040c43c00400f003c0320036000904000c1113450142151140c070041c4418400701103407040c100c0300220b42e02078007181e182c10107442110b0580d0303040825070402c0b903c50301603080070780081d580f101074007041c180f0303180e101e9581c10b04440e5140c03240d0102c5907481644d00e04030602446c800c0c0344c40c04039181316a154940036000d410042e20051031100c200200e00da116080341c80403c1180c200d035a201d090b080c04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 762077859 1250 762076609 762076631
    0x90c1403220f08180f090402060d2d05010f0f050f12030309060906060f130c050f040303020115060305040b07030917121b040e13050a020d0b040309050609030c150904 73
    0x100e40c01c4100004181c4048a240d4205417504d08140c405052018040d0800d0766265002c100303554000c030200500310b5803546290442440b01d1400750070b410f100680411b041d01c03068100402107510581140c1610768488000b40700c1d07a1154209601202d60441d410f02070b12130010003140d039010302414031072001d1002100344541c992010030301ca032180d4402c100312182c9a0f549800c000740c0715020040325400800180345c00721160840d4000000218007410b100b403811100014030b02c0c80c1d43c0182c1c8180e0060350b6a1425826901c2c0401d1080024840c81c41d0600035410300362540500d68a002d0114001e056a80009000b0441d0728550075450300c890305c0310341d61100c0e41700816611801044415020b81001c22000c060024034020a40c0c0644144210800d003590300c0003501c0701d20b0301c000c800c00d948500c03c00d000040142e9512501400140c400c0d1000801c9003090b01c1c000d4440541c031340000d40f00b00780c14006600c9035140020311240100040340c21600310111180c213880c19101b115450354000d400c101341c00e01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 762079109 1250 762077859 762077873
    0x30403050d0b03011118120724020a0812040c0302150409050604050c0702010f020313060e09070c02010210180507121416031104020c01060609090c1403220f 69
    0x407894242200900003424060101822181e580c050322620070024011081c2902e44054006501c4902038210050f000f601d40c02c1c02d10740110f81d4003d28106e050105002c9004480715484012980e42d400107000b005020303680c0c4450350045410ba68040b4550307500040601c20700040d880001d54001d080074500850049505034158028000c0001c0c45003403030041400760402d4030803e84212042c5c28600c1c2400c6542d030044440521800445045101c24007011003600302103103c20f002452141c40700140c9201c06d8003400f0307001500910200a1002d012101c00140c0d03004200c844041c0c064070300014a0040d84a082200c1c40101107004c0c156104411000c40d207480d0140200b445035005480c0c039080c0d45c1095900340c1d61401865a80d80c402ea03a40d50007000000d0460b18142a500801407002d81002884090282125000d9108100041c02e100081010758507910a00c4460187e5250007074550780382000304102884007034400c0a22503070107000130724031000500804500d0b070782c094002440e14105007031480c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 762080359 1250 762079109 762079117
    0x9190f09030210061a0301031b0306020d0f0c0c21051303080903070e0c0a0c03050c010e0a1101020106230415080d03050604020301080d0c020f030d0504180b060d0c1403040305 77
    0x1460385080f40c0810080c2d229945200b00d0103030800520311b16803c40d0f07a07040b1101c0030b8040c41031140303440c04030110008800e8000390182501848000585a607501c0601c0151218114164140308024540a01084c2200c0301c841198135003c0f0403101008482d03104442c18801c015120003c44102c6401000304045d65000341100c0c06e0450441c0c480c56120000700c03d10030390655441c9a4003500308054201c00d07025128050409001341803a5081c109035202e95400d6510810300d03c0d00c1c0b070f00104101010070403004d10719a0396030000e20003009013508046400c1c0c2c1041c1ea04803012074800c1c0e22040c10f84c881d55a80c0291a49c10030415041100940c1c0e0a905a51990401078000c0440d00b842c000802909081c07003500e0484501c0720003403203403002c0b003170007a11400788624060b0380220381041a000e076078604000c0d006020b106542c0310703540c60f81b03018209004a400e203910503608030b09040555140703a070307250250341441c628082c0000300b03235403004000d9480101070800000c180c2008000c110078140c1008c050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 762081609 1250 762080359 762080383
    0x110406050904140c03190507150c1716050309030d05161e081306080c090108150a0b031513050f040b07090801110705150103080d0b040b06070b2409190f090302 70
    0x19030304a5140c403504400d424840c054000000ca480c2c001340041442e80160000841c040f480342f91400065591524030f03110403c00a98043d400006c02224a0508200d00c042c03642c0a4a030035418004050303402d0100900120b8058440c40b52401c41503030301d0f480441e48121055000c80010342d01c80010b00040041c040521854020480d0240002d9022102c1d6040340c0d01c80005039600d4a2980d1000004040c140707810450907001b880001c0b000c99004280402076000306c800c01518924030020303e0420908040c00301034410030906203020b100c40c802003a6801a0000d52003502c80c91a507949103012110510b0fa507100c0c880075806d100800d0003000c2c0000051543c640200c080d01c0c0c0d2040c45641c2c804d01d6100a201c0142451420401011484540d600801c0000d4004001103000e51514000894940041c04190340703d010220500007069a20101c203000c051500740c038034502058100c006070808000402605401d8080c1c41c17010b400c0e28007548001d1a10841910404c203614590400079a946042e0600c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 762082859 1250 762081609 762081613
    0x3181c0806090106090b0307050d0914010b0301110f030c16051911190504153b010305121305030a0c0303022406100201020f040e04110406050904140c031905 69
    0x41035951181c5c5444050719000d41c03c9602e103031911a0112090b52100904100c029540c5d0400d0f4002041d1840188580004034000306a181d6940b0400d400c5401607065820310540401c00d0849180ca03003002c0d00c2d4051902c3c2d10140c0c03039407002508104146141d10008200d4007401304c1c408052001840800082c03806030151402c1c541418042c4040184883c554000c484801a410000c520702501300030004007a02d011002059a12100c040240c0d070121040300c000352100c841c0b0711349107010404144a110811036628015455078894640382e505140e6640c1c20b9a6000514640c0d00042c00002ca000f88805021102c11380712904101c4068005404203c0040c09401031085001c2000c0751f6101421109803080c4009031941810040c80d211403884a005554081c08a0305018222a0203000280984100c080032494035240045500d6a810160741c41f0310310701403040c0599140d190000d60b1165006102d4480c1101282c4818602201c08800c02d0741031080c80071200404040701042001644a002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 762084109 1250 762082859 762082861
    0x506030a050a05161b0c0801091505100614030406060e07050a0e06180105031e0709031407120308090a080d230c03040f030908070b07140a0803181c080609 68
    0x30f541c90340424905840002d0f09400210a0305815504041c0b11903101c0c100000e82e0b1b0303540f00038140c01c1d942c100509030b80c000c011a0b031000100480c0d001d0b03507520003203c0c1c480030b000c541031101c09801034410b0f16410358041804000a030410076239901500291610302c1741c2c0769031460b0040c40288650b10400a1100092080c10b0361065428481c0030b58000380e12018402c284604c4200046946800041140c2c03811107100da00150340c4c5403410601400381c0b40d6580c82401090441c18083ca80c410340c0c104d209507550103440c040150281207127030f000000754076150140d816100c0c100283d00e0050000009058a40000758000e5100c00e44d511843d500034042140d0380120b034440c03c0d0307015903000445104007545000c1000600081c81086030b80101d920a0801c0350a0075190503a051030819150003420030703901c0000d01e800c10300007440340b141c640c0c1e900c500041104400560b0f41e440e150101801c0f4a019880312034240b4106403060003054080001c17087c40c1140da4100c40310081c0245000e441d5a40a4030a0788 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 762085359 1250 762084109 762084121
    0x4021f0219080904150f050607050c0607060c09121e05030d050106090501030e07080303010b09030a0c180f0e1c030e01050408040e01060f020309060d06050612043c08040506030a050a05 81
    0x151101c04803805d25806d01c0d030a916080038442180d01c0010210344a0140c10201c203120354a6070050116075000c0c14001502e1031000201404801c2160004500d0044031f0340c00c80300003202002010f03052894a0100c502c054800c4c40c0c95451401903481403008141030100204209904c070000ba0212102680c2c14015180380345003943d1205040e004103c41034104100510a09006000030480900050101c0782401c0c456115218564002e80180018103010b000e86011501d03c4e004e1010700809040e400c00c489154486801e41e12914010f0a200d207183c200c165981d818080d52103000100c000c10000e01c200d140601d0102210741c07181c0036524540313005500120350144920702c1c4d000702c403078680c00952400d040c1e4001c02100d504070f8000c0090260700da002c0414070340ca03144041d046a1170340d03400c50350842c01d1610b0141c0304010400f02580241c0d5040c0000c203024205041600407000f10080c590021b51007074101040144502c1d0049074001d0000010f104159170700d503115a2190007241c0702040251951 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 762086609 1250 762085359 762085391
    0x7030e010c1b020907050702060c06270a030f050c0316060e030a080a050a1b020f150601051e09030a031214060a03080307120507090e060904021f0219080904 69
    0x40401204020710b540010340141006440240c1081031403c1c1141420141d80c005a480c0d40803550484a0360415400e0003030b0780d9117810703000e100740403903480f0020714a0740606816a140d914900280c100303c8005207c0304481c1c091b00449584001250984c0e945091000880c22041450003085909074074003100141100000b2042c1c40c81145035650b20b42c0240c0b15125a04040c110180804640030760322003441c80f14a61000701d0240842d46500500341d0140010b0b442410290076001014442424000308940d03030703038000100e501541618100d01043c83e0f204081c68028024007070644c0e05841005201c600340364200c003122103010484801800382280e40c035050052b40d001914a01d40000c1d03100010310005007040c01844e4400b9076454020654602d250b100f6007903070001d880c49404100d410005000880705100990383c492800ea1340c2444030b08065000c108554103240d500d03841600340c4030f0080443c91007402040d06420800c0074942030300c1d1450030311b989a58003a008940c495450241400081808 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 762087859 1250 762086609 762086627
    0xb07031a150306091801060303030506131104050118080109210f1d0609040f0b0a06020616110f0607120501090515060a0909060b0306040b18061c080307030e010c 71
    0x181090b801c0d9100e420901062440c003411592280c0c82030503140089005c24072a490055000380d40102c1c5a05200301031100c1520103211980755141442d0001c034030b01400710704460441e00d0138a0011130740401480290300c40625a04141829401e142c80c040601075030303040342907558482c550400c007150303040300060750700e0840402c804002c10800c0c0552a04818200348029481c6000b420a80c07078540c650001404940c049915178100541d100020040fa003020448903001d0281030005140900748840c0c44244010f010745284100401c03405000c11405090156803c0c24809c2c04c00c403481410104070241040d10803200a890103460100009800402e07070080718056641240601d0140d85a002403201c5a4040d00310803003805400d080005400c00c1074806d402c020030038085010307181d0915104200588407144180c0b03100303604901c1c242c441c41281501864201d142241c4180140c040c3c041d040780300908040c0c0140c908000801000103c3c0e4058010343c4540d80454000c01480403000800e4130340c000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 762089109 1250 762087859 762087889
    0x7090b040e0a0512160b0f010609090b01140309191101030b0d0f1202030c0a060b15030417091503150109061407061509060b04082b08130b07031a 64
    0x2001202c014061440c04004002e9109124881605c1c9205920f44021011040d1003071030107107202e00d004001c065841756450003d004ca4000a1100b288031500080c281580e1032107490141c1c400001080c2c40307030701c00c008094030045203451142d0a00741d641001c0c0d010803040302426001c2800e103007503241149008a422110700758001c076520b010301503d84984040c452882c070a001548010000c20300c1601d000c0004098a038442c00e00422a82200c8082c03003100c12080071800f4402406005002c00240c00242102d825406651030075110022440010914000040b141d00092000403e105124041500a0040300d05c282c807204d030003e5445004030342082447c0c5000c0131603a01442154002100d9800c000440300c0201080c0c41c40e25200c6401804603015507004503820700b0000b0382044040c0091211010480c0c19030041c010f034500070321900f01d007481400c12401c04c03c007444d0001030650600ba4000c084813900650b040401b8584598094024480011900744001c148040c80c2c1c400c0c50446400c44800c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 762090359 1250 762089109 762089113
    0x20901050406030b01110708210a020d210504060504050f12030a1d030409020a1e0504060e04090b040506061c124505191e0807090b040e0a05 62
    0x282c9426011002000940c001d1410880d6012170101140030401c0380c43c010b014078002030080d070040001071921070b40b65040302c0100756030144180242c4075000b007203404070000c49090040390703517590228140c030f1500c1c0710314641d41440c5000d081c03200384000c9500861003103205908840c1c03000d0003082d40d2a5182800440200d80420400c0000c4a803ca03a4000d010702c030300c0701c05040404a404038501c1d811070b00a034000341002c03580415240728160344004022000c0d41601e2480d194080120030040640c4542c2c0948828440201c0b14425242c4540d40100400780e000328031400b003410240344c46a19188250380b0148101500e400288041b0103003008011a150300c02c41003500101d40103010b841581c0d04043c448816030380300b2048044201d60709a6600d020841d11081c4250805076045d0051191464100d5400703940e5400c90075203180b04141c2c45c0342c22b4402405d90402400340c40101190880400d81161207280035581002410142e40e82010020b61002c680c248000c80c81503055a035a2075420901400d0f607 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 762091609 1250 762090359 762090367
    0x70908060610030b120703050c1f02070603051503030d0f0e03090603010509090712141902031f02040504060b0706061202132003040b0402090609090c01080a090b041a0a02090105 78
    0x7240660302544c00c0d404054008139100710300340016424121130ba40296010b4010b40c1118440d450200d807004403007807000340812640640a240259502c500d4002d050905640300003283c00080396040c000c10204d4007d00f01c91303840568a6010014110000c000032009081505410000f00c0110641c0c00d22030700a040581140c5ca040104100c3d4070000d044191035006501c00416101d0ac07d001100b800c0b4003c40036100c101c6603268110b89040c0340c1c081903490b178180c0300c074200300140d0340030841c01c0d4143c0340c1710140302c40f481c2d03008074000091089520596115240000c0007900e00c51413405001028010102007114a507264402c803903504598070f00940c40440641c821a9410403644606c145040403031403804020020280740003298820303141950b007602c11a04000c1103180c605001a808281603801001c90300704006842e07038854140c0304284c18040380d50001406440650b01618078641c01090104050406040184072001180c04e2610910013400028201d81c03458000c8401c03940043e99a103140c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 762092859 1250 762091609 762091639
    0x10c03050913050408031509061518030304061101050109050c090d0305041d091c1209021216081c0905090a180303020c010c0c110907120609050709080606 68
    0x10550100c00740d1a80684441c00c08030141281d0310516100b20710070407201b0b03501d0030485000c05259580d0943c4c648541345200c1084107544804000f4034546008030080364441d04074107181e8a00c082d0b200c081a401d84808140003920991000d01c481041e903810008102d07907620387c400314058a40c200c4001d4803682082098500340c0c24000c8081010318080d20f00719003400d8070b44113003140e40d415000c90400100008018494088802d104c2a02d40b81c02034200314a00c040c7c02c050141505450103414051141d90701245070641d281c103000c0078110440b040079075201440c00856100c140b4158050041c15100c0c200380314040340144114900c0070301d003503180c40f0121482e02080100000000703124409007034a420030703040345912441c000c0210602c079847c0542c03a01e02525032030b42142c0035400214200680310418001040d81303600001c0c0c03040415640100c03142d0300c1040a0f1202e6000348048006d50b80b0b0110002000d500b01d0b0701c0340d4041c41d01d690740e428001c2e560360350320741c0e5505058405039070003a40250400c3c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 762094109 1250 762092859 762092867
    0xa03050d1107080f030a080106053f0a020a1709060a180203010c020a0b10030206041202120717120a2f16050406120c06050702012a060501060e010c03 66
    0xd008100781152451a00c0c0d4241e2410000030000c090303040e6001045102c00240c0060485015000718a441c1d401d0400d2035104a0500c1803142101c66410b041c80076a08640c030413000c6071500b814840c0c108104c1e0342400b104041c02540b010074000009401a1910f10210012000c010700a080c5d44000300318540315642c5c083d008042c042002c401e000b159610840c01a1801c0c001c0440c00102034014003201e10041c1460500c41d0001800d0051103158900b060006a0b103040c01e4409941c503041e4401e000c08405d10209100b440c0d50200007005205803940058030f2601d8040744a410b84a0788162860600409950350540c002d005000007c20440420349030043c04400304d100d400c20400e51001080c2805030110703410100a150760012074030034192b0601990402d4000d140042030501084500c500303180e128100d94404a000d880100400059100c042d684039002003440c1c801040844056207901071000b4840030000e00088413620304010002641a004081c010f1106006844a082d04c0515541c215 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 762095359 1250 762094109 762094127
    0x5010506030706120507170106030c0e04060f1a04050d080c070e06060a1b14010606030501080d1407060b04060b0702010e0307080616091502030c07090207052802220b0a03050d 77
    0x4013007204e010112006070348450091f5000308010b490000310301c58040c100402c4aa4418a69800741d410301c0d004104054502c540d50080b61080205081e24003900400306143d0710a0b0f9000c0386d40500f1307040d150018010000b004001c407030003500440721016600d21030f21201443c1140c400f03a0140d010301925003e64011014040c01140800809583d03900d1542c03071030100440317000c0c0c178602d5170741d1010240070190305031064a01611a40b4000d1040c601c000d600280f124103e016081d44849020518408000254101c808804001070041c88000d454400d02e021540203010141d000900c912150711071401d01040a4050364201d030003505107580c0d4030182440c07a0144000302c0c0104894090001600c031148000092000520f6020303550301c425400341940b40a0b241c0c0c010b203c105e4410030245000500010305694104400d00000421000400b818480c0751210708019400005454171402c8492100072054142d103259002000040c800f40180126103049010082003640029111010240204900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 762096609 1250 762095359 762095371
    0x140906210105041407060c0c0308130902042405130603020f0d090b0702162709050d0c03030e12030604110405150901120b0d060e2503050105060307061205 68
    0x280015540da05845030845400325000d58080c0d1038181d43c885012018400b0744000c10381403514880803152031b01c07003184143c120f20005100f0080028610008804400c0c3c40700280202d08086465955605044841400c54040084c0c590301e07084400c0b90042c02181903070348070558040c1c040c017607604041041d0020b501c04401403481213410b0003030841050041c05886140ca2180101d05441c0c02c00f900702a00d0304a20010700d07000c0d00b800070020f0003541c00ea00502c20300440d1508000d0b5034030602507002d90041200100140c040e000300f14a48c10910740180c0c0c544c0b021486560700300700400303d114007103866822078500c481c4c1c10a81080419140e18141e04204a141d080d0f8403050b282a681e1800110500c0317510003400c0d110f62000c240e091080d0380112180c09042000130051241c440602c0c00180d00740c045120090450340d440c5074a8500301001c012042904500c8404659882001560098200d000c0e01c0116902d600304000a8801d0a01251001c00c40d00d90f519440300007103c03800c400c00542002051 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 762097859 1250 762096609 762096649
    0x50907020d18170c13020a0206160e1216090b060703140d05132109030b0403020a080a0201150b0408150405191208061f0f0e09070f09140906 62
    0x1007030f90b202020182c2e0f41c404007a0010500c210041080c81103444480858403d0381388144448404640c000c608580e2100c0c148407004245004840d041d1980d2007010311450700034120f41d0310342c10446000540b071039170810007007583d5104556801041c8281c0d920b601b990758100d030040c018100003d003d40d9409003e60900700c41207040c82c4007d81c9802c11a01c0450b10128a802e6100840b0203210240804145014100c0030405040081c0180586180d040d80b0004087d0252080050140341c0b00f40100c00301700741d04c0a2090f0741c0302c0101c00b009001c3d0001c144101a07600e00404001100e099101c02c4504580c1450043d00711940e0441c0c25078100c003401041950709018061b0703140610403030f00300e550180030b109020b02c0301c140fa0801da0051040700c00a140500600b4049031130301140040190f4459508200c4c60b04000b14142c1740d41c2140e000d88441030300360700300c042c01c0244407181c2e8000403800780314965503441c103820541e242d1307000d1013030741c01644070a400c41030240100d58281010030b15085450040c0350 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 762099109 1250 762097859 762097907
    0x90a0203071e17031c06080606101e021b0108090d0509060f030f10092a1101140901140106140a0c02102c03060a020703030902030a1b050907020d 64
    0x769030501100100c1c3d001c56000058024529008100708422114586908101c201c0c00e0a000740d56610028140ca48600d007162200c07020580300328001c0d20f9040c080d01c2e400821030003448001c0d40e585618007168084035070340600d080701035100350702e5903100e421003c00503c0030701c0201c84c3c01d44503a84010040ea030491010004242c0c094514001140180400581c2582c4c9203411034481455010035003254410074101014145000e800244860801c031240000c69000c64210805517411020b60104203099400d00145400111046960b180302e40c0c80c1c3c03802804042c090441001a0f00004d000f40d20204400c55400112601880080e02400e61a400d00e980c03a8242d80c2c000030580c1e617901043c08006800c001e02e0f5001e250302e0000b4107030750b201407580d01103105014400081d1141c400908480d406980800d00c2c9041c1442a005265025009010390304110100d0030600402c0003101040000c040c04081d0000306401d0503103d50380b0403940c503400b4201032a003031030741118070850a0a801044a440407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 762100359 1250 762099109 762099119
    0x61803190504050a0303170a0e03090f040e0a0605160c031b0203071a0702042406140d0207050a0b010e04030e041a061306080f01140909100f050103020405090a0203071e 74
    0x244c0c0203400b43d40241c999420884030f10120103901c500041029544604081511003403010020980b0002882251106590031003000458000c000d14084940c503485101c1105042c003840b580928028201c120400c2c899601a520558000c0080c0070005c0024102400510100400c00c200d20444c510007015505900d96529041501862000c046060f0400c001040d10441c0b400d03110f03c5200d8a0303120782409d580201454299040c03500c601c1654103010000081c1c211815034081201c99010046000710f403103442e00e0400701c1e541c5039100000c40c0ca02c841e5200106440c681e1062031480740b941652403481c041c018205000107068a184005a03183d00311a481c4515559800134007152007846c09417200c04c07898203800904030b042c0901232220340c8803510014030200490f204031407481c0f54282c1b290b04058482282c1c1d5480d04d0b950140b40b4009030724001c0e501800421340d400690480c0e0080f1000d020a0320340c10b080030f8681ca50400c0080d81507104480402104181c20b91022028071580007000c1010707554 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 762101609 1250 762100359 762100369
    0xe19082d01050a061d010612020d020c0f07050a0e06130e03070c031b0e10050607030c060203011d0603030316030b121504140f12070204290306180319050405 69
    0x380c4200c010f89803900024004190740100e9004003803210118001c880d45130480c0a0324000e55a1000c61180c4d03000074544007a2807468048410800d03c040031a442051031402007038685045000e0f9038820043c4010010f00741708440070300f5000b444010445161031511550300342c000c0c12082c100200d10300060041c603000c20b004261280080d400b4811208540254268051180e245500890340c10151901803050203010045004140c801c140c075200e5581d1080d04043c2c81d10308402500a05080c000000881d0280d00c612031942d268030000d200b001c0da40c40b81d004264580c04100d038224600d42401065140390741c86600108044d807000317000d080e40178440c101c00508104614920907081d5000a0900042207215a80810350030340c0c250103401d03800007038500d0030b4551000c40c500c0c00c0c06180100300d000643d500d03036000644201c1407102c804124100503101550044e681a5400d00c00c0c02060002602c0f806c5005e240081d5844030b41c0903503d005956000c50380c84811301140002041810720001c1600c1e154 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 762102859 1250 762101609 762101611
    0x608040f120804110a14091f140a150c111504120213110706021305040f0f0f02040506121306050c120702070f030308250e19082d0105 59
    0x30302d6031501024601400d0014018180900d540c0c0240c40c0800300b00030107035001c000786d100b02c001180c02d20703a43e03210300d61348007110340060f10030100c0c0d42034421001940c030300c3e0540a043d80500a44403003282c1565050b12041c0545a0007800020402020308800020303420001e0f01d140c00c00045c5800a0307180d01840c0c900c41608150002683c0b03000094070207040d441c083c0d031048100c000d0f507201440b03503404502c405102070052001c010910754000c00e103d444c088404002e907014100281041203115010109500900a40340381009007902d04002c680003940700d0f000700e0781550405492985880f560b086003107261003000313000441180a03000103d000484034003030240581c840540750368840d020868a0540c540300a060f030410b542c08040b0030032410242500800403650581003440c8140c0c0c40608418100b2801c140c1c0020b0303211502c034000401604080350a80a4009446160b14840e003440c2ca0400040301c1c0c0506841540f002c02d2045150084041c44100c404070200c0350346512001c440050b0075600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 762104109 1250 762102859 762102893
    0x10603170c102c03040614070804080a111206060105220b040605040518090a080922020c010e1605040e0a0803011412010203041a0702030f0c03040602010b010207030b010608040f 78
    0x40b1150001c203c160004007a40f0005110700040c524180c40c1034001361540f00003900342248004c0204114043c0141030003540d0080c40c9503415640c041500d403a0800d00801c2d00c400a0748120320551040d030074004009520340c401c04040c3c40f00d5240100440711100c0e40c03030980040c01e4001a24503c003142c1e60b22040003520040c005611013544550401c0104108030540200b100300c0f1180400400c0032202000034080c0b07031650070403620380c1d6440324400800d00b00c0c0d0134951400110800007840c041e00300141d5009011586400c0c008000c5114a403150380d445070510280e040c11111940c4050051303180682c495400404200112042012282e45d20285600240c0c00b444600f0480100c02d2800e01307002060743c0c11401034800031880c41c601561020003a19610100c1c51020b940140042d0250b4000c004907a00c0100140341251141d0b18511101d90b6a031181c05488019428026403540d0365000140c4c2d2001d40c0e80c0018400b070543e0034000700321604c0c80014410341d045140a410800426043c50100e00216 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 762105359 1250 762104109 762104141
    0xe06010e0901110c060403030b1509040506040e01020a18080c09010e0703060f060c020307060509180405070b0f0711060f07030e0a05040f0f0c05031e13120917010603170c10 76
    0x6c51705041c003500711640450030030b015030080b4420300b55001a09003250740303194003110f0002f001e880d03102c08100144800298941c3d150b2001450000c2180c00400348070854450a2802c51401c2e2240e0b01d0780c0c2c40c0c800414107150010075139001408000621130055030310030203034a00018a940e07a4290341c80310a58a510034070118559021041c150700741070082101918a5040662501c09c558011074500042482038244550710140032504124040c040d410017400043ca1a0b41c46882d103c1c4011840e6120311822030308441d085018011304d00f091020b46001c007040c80e8640382040c0064809540352801000210380c0001202d03004240707680c844c8200b1907018003d240000740c1204c1102e22108030345c1c0c0d003425001804824010440c520507483e03024085200c00e8501907045441e8040880fa295100e0040106038945144a04101c1d60388101c905085408425080c02c02d404249000784c2290b9117030001030400842c1d0204000000c0c039180041a10072101005c5400c0d081c0081c45501c12940d00b106841100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 762106609 1250 762105359 762105361
    0x801030b0703020307090b2223040b060f0d06030f030c030809010b1509030a061113060c050d031805070807080d090e0103030305220503040501120e06010e0901110c06 73
    0x3002000300d15690140080c1011455820b000300040c041c0d540a00c04c90b802d12000141d4100c550500b160082c001d140e0300b800607507510761103607819560241c1c1165078801c0307070074000c00c1ea041c1071034107008030700e244400544502d01c4e0400700220f0540c594000c4126461503038440c00000006115001500c040f1070203641c85d89140051444e008000d118003900e510307000c4e03040c402440442d5490119200340c0060b0000c00c0d43e07440c1141c0021904040c60a800984003e107007901901114220300001c0c01500c010900d81c80580c0c1c0c5881c0c040d12003c01682000d810342c1d00c10200c03201100d0017580040c082183c48078160101d004d060343d81d245003c603560800c65813a0050103081081c00c3c401c00840e8440340007810441d1340c940c00c5c40c05084c000c80c0d05100240c01c054440700810903c1c8103450074044200705a2416031110541d034200585c0e03c0e881445407500182e40740b0b03011901c840d460b10989403511107500240030310b0307460710b142251801405031a614280d56201140c03294108140018070a08150303d01030013107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 762107859 1250 762106609 762106613
    0x1f12050309040506011e05130504093008011802090d03020106150f17061c0c0501120e0c01031d0307140601061e0f021c030b09250c11040c080103 64
    0x143d0760040c0805040c00580b04981141d5404201c0f1001030850a2a00540b65224503080c0740c543c44003548070035009460300b40d800c003d01003643d80c04410344d44400da0f04001c04854030307102e42071400d00160314000604030074014007500c1c3c4800300340b25448610180c0542041a250300103541000680001c4000d03030755582d410805008140d5001e4403800160400360301e8107148034806400183c80c2800744540108136030014402e0365502e29180507409403c1d802c00300d4031900d45409000103100c0d02800d800b0800c054207094442815005202202e030340c24000e4500c030001d240c015009040d2511648800041c0e241c0c00245602c0d0070006051014042c0490282d45959003007070034100241030f00301008220000b143c098100425a4041310008050320f82143c00c9000404100e05003502190106414500507415560301a490341140d090100d089901d5001601c644da002035001410340f01000d01d07081c40c0c44418003964047e00e02408030b540a0f4501c04d40c07483d20308000500301c0c1c48a48a20b000f1078490300050003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 762109109 1250 762107859 762107861
    0xa0f0e100609051008090a050a03080901061202060d2c100b030a0c1502070e0c030901050604090308060402070201050c101b09030b060d150e250e1f1205030904 70
    0xc02403a46042903003071182404041025103c441d40c1c000c0178000114041a203c140401100704503940202c00d44400c0c022901e4014031510081d00d0400c0c40b582091000300751a8540b2090501c11580180314628265006d035180010f4a454a0010310824030b040e551104c041d1103e40d03d030112945100035001c02c64001500d08112501e551016009902508580d000101c031042c65405440705540c4560b003148404c0c20032443c1940341d800018a900768501848200e00c1c00101541c000c070740c800f0003071110390781d240c2c240300840300c600c503024001071030210205645040c51313402031120303a00614200d4945021119018509000720303c04803c0d09588102c1102c603503205140140e04400a407a01c8405140303580c48102c0100c9010301039604c10204c8000c21020406d9800701c4015141500d1001d009080d031038681203444107014032410390a400d01c0940b03100f003210b00c3c10841003561101d40305082551204005844041c0300044000d107869900c500c0422000741e60a40384100e40c0c8188000c550751842401880 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 762110359 1250 762109109 762109141
    0xc0c0f01050105060414031c0905040e061e0726040b1b040e06061204030305090c15220e0405030a09050901030206090f01090f061106070504080303150a0f0e 69
    0x1a260380d00d060014821a070b109001c0720100c0d000551004605d40b40c4000080c03c2c62512114204104034034440741c2203c58111140d20102c0340700711410400101d039100c1070f0b0f8841500701e80b242c102020f00340c202e02c1c9420240d6043c1e504902245407001c0700f403840c84100e142120442c03400b00d0070114298200400c1100900100c3d0340030b20820704948004031200e8850007240528050085240700d04d03130000d00303540c0b25003068503c10001041c0d40d00803800c0038203002d0002c01e019a00c1036101d01a131409080142481414805440134085c2054589000580c04c2f80c1c1210311041c02240750588800d0002c0e80070390140071240940d0148000c4c42e42c1c0c00410001034142c1840354085400307804003000400143c0e070381c00266600b03914143e511407800c940490040301e201285800c03198201134080c002040c2a64061947d1041021000c1104d4960b214120140c2d403034000c070b12a24145500c01c0000401c150401502d61701080c801a20f241a0181c489024100c1058680c02190000424200b08908110700341144 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 762111609 1250 762110359 762110383
    0x409060e10030323120c12011a070b0c090303040305161e0e04030314070f1103160201050d060b0a031a01030504080a030908090604090c1e0c02150d050c0c 68
    0xc03a00951950390301030125254a9480c113503044070151341c03880e00400c42c821181d0103040c1c40caa003401ca291020000d02c0d19000b4207081d061178083c100021a4074040b40b4044102420034403100c6081544c10f0351803203880e0100403e20104810305001844042d00d080020300081c1d442800506400800d00201032717036600c03283e0b01800c501d07142c500c10707220f50501c5100e900081c2c407900da1001c201560350742000d81c040d240c0b45080808c0780c0c2080082105983d03100c0101d8184129550b03c0c00011806103000340d42d280500038075403920781e1043c104000158003800c0107000b0010f5040020074600d940e4201d040b03158002c83c22040c00b1076100d558480901c4c0310b2041d8450340181c00d003006c000500b801e48921740c5a000b03440c030303260a05a6500d9030034144203c10094407040800244103650751511003072514042c0c1a032046441c00314843c545860035108698960313250501c05913032001d907185550b400b00031100b10400e50740b051864040080c0520011180101c901c85c4d2039944c2e005580c1e00701059824a40301140c160 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 762112859 1250 762111609 762111631
    0x5070b0c040f060e03252309010506091f02011a040e0601180906020f2a03030708190509160621090c0e0a0b0a0b0304030f0f020c060409060e 62
    0x109000041200b4122400d69034585401d82152105502107454814070139101210102852202018207541805180c1560b40703c60303100c100c01900c0d1030320394002c07501d10300c0e140c1d1710082983c010310403424842d01034010000010242c0c07000700e04402052050448000150005035156108108080301c0708a440e440e20750240c0b010401c111802e5061515003206001c0d5000c2c044941010411500494000c001c50036040b0b941159108881c05d100d000b103500a18580c50350301c00c18000d01300b282035002d098081c2c41843c0009940356075500942202c248500514840c49030310015036050b502040391144511421031480185005004140d07240c00220040d80300400b0004c2081c880c0210105240509003542d051110204141c9403030b1900015600181d000603201498503001c0000302b945603000138440d00401e0b5626081103440e00500480392004680180200c0c0311441d1100b542441104040880d03030052065035400f0458a0008020754025804043c02580b641801c0c441c0407070008040c0e400100c0844 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 762114109 1250 762112859 762112867
    0x60e0114040b07020c0603091c0210020429040302060a080601091211010327030c1a070503010612050411060304230a110409050c120f0a1a0a1a0d0201020102041505070b0c 75
    0x400740da9204274010586000c800c2d0010a0b600d410b0082019040c0d403442d182003591078a403505000040d154180c5140002c0704ea401c42d080c02544007603021241541d801030b103a28648403040700c040d15826805040241040341801c0001504440e040040340103e1051b180c43c21045001ca0005081d240b0040d200c501c0c0c1180e407160403484001c4440c50000c00d80d8103040030f260030f40c03d50410b100710132560550b000034441c8080400009680c010011410b0b240c49840712548050001c1002046510490700200301d040190780119062600c0d00145a01c54498420f501c900c0c41c07140e184119141c06030b00f0041036030340028091020480110261290b01100b69402c0103441309030b03181c0c241c2c0c0c3c01104044a0080b5103600710030f89824001d1280c026602403010403510150010b1910f4503c200c8050b1060842964010200300049210701841380c0c18100c840400703594400d04420442c0c16000f0010032815994204000603180c640c0c1603600765904c4503501c410380c80d0780070750501e0024480014642d036041e1038108 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 762115359 1250 762114109 762114121
    0x2c0604030f110429041103131a010b0a03050a1d0c0a080604020f0d151b09210311150a0e07050d03021902010905091801110c0307060e0114040b07020c0603 68
    0x10500035604c50b51201c502d5508142102003001000c04022207207125030b00108010340642c40300c00d00401c00c0d00c204560500440b040c010441c80000038042c00040c0b103c1041011509403080e0082c541005030007600041409428250841c42014400c154840d904030340600245803a00025000080807440f000d0b0599181c154001000240c4000815106111700c1807460709004030100310050032500d0030404c0203a24160841050040080c0ca034141c001801c0e2880898003c143e07500c2c119909030303021040d00780104107a078162100c40120540070762601c640000c2e1206166450842401a4540140007418000703c115503410a4540c1d0405401507200420038000603500007101c0c0106941102000d0364902c03030703200403560b10810b544031950015050051018022101c44141e000f003003407000820003444903c42074901c40c0a0300360f0100d5039400c20300c84000411819002411307101280000012840d03801001d00c00014030503542030380c460040f601040705490701006003108424003141c20b40c1c01c602d428 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 762116609 1250 762115359 762115391
    0xc0d0327050613060b120a0b06060c0c0d08191115070504140a0e181006081f0204050a1701150b0405060c010f051f0b04062c0604030f1104 61
    0x280603d00121000e0300c20a0a0002c190310003d40e481c00180030941241c00e024600d40c1e185104101540c0075112030300070035460718004040750380c101080406089802104c60030880140030401b000da4aa400400c015458212103100c40b02c40600343e502c40300c0e0718004410840346041c1d07106800c801116820003e00607050342010545003104e0101c000002d005c02d078440424541d00440e800600f48801c020184903025040b500d4025102e1a01c2044400306800000007500383c4001e07116010060304910b000d045c15800c0f0412058010300c4960001d40381c95550780c0402d01c0c8131031640c0103191610300a00010303510242801824000c034019100c00821508250000100380315610865200e40d00000f00c00150030320a400c500d1a5a0021400700003034038060983c50300301281c01c20240c041390486407000c108064000240d500396031041c1d56918540d240203200b0658041648080d1840c9800ad4461104a5445c60010005940b040461401c01055894998000d0dc84010f01d0391183c0d0902203900760003d20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 762117859 1250 762116609 762116611
    0x14030708090607080f0706050a150f060f020f0d111203070e120f0a0c1403030309030f09031609060e0c211b040f031103030703050a0807050c0d03270506 67
    0x2115903e03070b202c400340b810b101d0782d00c50030459034051000421000207000140e44002d01c01c0341c101e4402d00000b41d100c00d01e0b03072581c0a18003800502411094040c070035680f0920115034000b45c18012514140c0340c0103402c518100c0c51020784070004034091051380503c4000c0c40500a50313a40c04136898210f081c0441c01400b8802d00c0c3d0302c1507000728a0302c8072000d031010301003010489542d81241990751003143d5042080c004001030050190441202000760700c82e040000484c7e01c11741c43c02014508240b107050320207030b4039401061010752503c5602c050000c09204050001c004208401d400a074280c40c5c03c00301490a03800034030000c10341005111003141c0c03103103119030a80015060041784c10b0f80e0756040030100d000003071503031003503440100070601044840100720032405803405040194454042c15041544e40e00ca0b9500003000640d083c405c08503500d0085250703940043c82420101c3c1000b5125a41c546005000254440000c0d241d03890103a40d07544829006070781440f0592000c0700624640c440b280e076414 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 762119109 1250 762117859 762117877
    0xb10050f06074101050403030b01051c020708190c150b130c030204090c020f0106050306040c033201141005180a1b08150607121d0402130314030708 65
    0x94808000700c00fa400001100044802405201a41c3d00c0c2011402010704032003c0707000c28600051a405903004900380e0715984408440b40c00740c50719101e03902e80650401d2108541c1035070144455070810740006204403180034181d555003000b0425082004c0391800744200c14409524240010f1540e071280c2c1040d929002d642903003c1032540400804400034030440e070118680915004001c00a2076020400c1c1e2003030151480284101510360080540303405090341e00605008400c0b41c100300003216001d510150003a0706070b111210561020361200c1380408000a0403803a50b54013030b100440035444022a0300000f0154114010300d09010100f00c110b0030584038825024052000100860025005000ca450801c0c0c01c5a4000c4040103002e007580000b5034080322084010501040207092100c141c07071450303821000368003454814940c140c954215100340342074030b640c000d130004105841e030b400280169040d550700d00169600e1410003103030002040c1e1440900e03400c02c108400c0800c0d01d0400b030302c0241d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 762120359 1250 762119109 762119153
    0x1514120103060513050601081501151b050102040b030f01180605030309012f0607020715090b030402030a020a0b0307410c01060305010c0f030e1c05070b10050f0607 72
    0x2e200c440c01807215a820101c010301030706c0f60f80008500e2a502180a00c1c0d0412000e03202c0c02c00b6604c3c0c86541203030501d1445000e0001d100d1000c40e20901c03d420019108041c0140c00052034140c80e003085c4031241e4404c54201e0600018400100010100f440411501501d1800104085418940043c0d00c0380700d0405210b04100b140c0307840000300014881d0100440307001c50700c41c000110314000c03100d484841c101c49407409030203180030001e82ea84035007502240d00b12060b43e47c488443e040802c42960f030303000131f40140d805d4840c202000700181c5914080e00040d284a400b01521707413400c1d110080403d042c000c03404030802a124078480b501507003145041e21000c2950301c0312516003140c945030701c0300d8010b95030005010b600f0b1040000902c0b2066000d0660800d6503a524003080840c181c041d010b940f40c4030101c841b698400e50600b40c2000d0348000c1c69010801314501070746081035544a50107052416510a410712030326407000c000e103161520387c01041640503102a4113000b040e4440940300136010002c0a070b68 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 762121609 1250 762120359 762120361
    0x11040b090c030901060e04060e0607090b0405012a2d0c0302100507080a08060f0d03080406050a0609020703121d0607080c13031214180f03070b0415141201030605 71
    0x6000031741028019200900082c00d440ca054107006011b0042c05000c000d25002d1b110114500740d2250000700156540c2140c201d14040c81e03c40110b5030b004413078410f01c00cec0b400e56204401c41d00002c84c444124550258050411440400c202007e0343c07900707403004d100d0b0400c08825000004100c030710b281080b40c1d01150b8031644108280e009039440e1007111001440da250025000c03070940d411003480f030301440043d103130014484090014807403800074145018010440302000a03001070340c0ca40155900c0100c0320f80106040d90348031001d5050382c000706403c82c049004a101344412150f544500007481422091041c4450741814140c1c2e2038001c041c18140400030414001410004c0b50b83c11030740803114400010303001d140d50b1308008041c0042100c18000080180b14030942254442c0f0a84181480c170b03000d6100b2844600d410808414072913104903800d4003c01c0e100203802c00c0668081e00082920102c000008143c4242c010501c20300b0700082c180e41001070205228003a88844100d042d694886000074039 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 762122859 1250 762121609 762121621
    0x10507080d060b030405010b0d1104091109190e0a0c05120a1502070b0603120904270b0601120204240c0c0801020c0d0206011a0f0408030a0c11040b090c03 68
    0xa441452a07200001d802c105000502089100081d407150307020303100800100b41e0304801c12035019400d800142480350b40600200c0c8500d40361b40009034441c400d145403501c55000030b0100e50044000c8906910752034101500305080b90490080b030340c80359140800381c60b4904c1156150008180a40500c0340214001102c6001c2150108011719081ea00002d01c40018011001100042d512440c01103904400d010081440340c2000501091400380803066203003040606401d01c0018a10313105001100046840c0181d032040c41c0d040701c0303800d0500852841450345000c5d030002d45000e0320383d007030320696030701c100010005402d855448001c2041c00380e21030307040c400480104a40030781e0900006030084442c0840025600c40550080043c0c40b1458152038070000d240505903201c1e5801d11075a9489599280750307506001e081002010707429620000c0c2e80c28107841d120558a1600710b1250380010598010b4584240140d10030021054002150f0038030401d000c550110304890b00c06803083c64507e00110221726 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 762124109 1250 762122859 762122873
    0x14010f0603050c280905010e090c030c16060b18010308030a0c26060f010e090f04051e0f070b04080309130b0d051e03040e0f0a2c01060602010614010507 67
    0x14540920040c00c0c4004445150f81803a0080701ca61390001103002517a001401c1d5005a244049055006000c4d1a0030340ea400007034035290b07100402040300da100403c40340100242c0d400c0900c1c01c49014050000d441d048890a04c4800404500d1054214040000401c0000d401108480e40072541d03c1011848829004040d51020310355200d1101c0c5541389000f401c40c1080d15405140705400c200c4138101940c10b404010358086d40b100d01d465030040c001c2800079264460410002c2c0c0c0103480340d01210307211082c070242000c06200407940d00915400c1041010414001001150090172542c0e045ea4900751900030744035600e1140c01e01c000e000c0c0c44a45002441d9909543c045510f181001c6c155100b24180c51400c152290b02440341d0001c114508d003050b41506500009440981d4002aa49155600d507440b880e00b004c44018002c101442c0c075842d03807480da081000311090720202540f40c110b00c0d0700d04014815094030100c1d0490411a03142c603004019030603000340400d40301802804d1031070b40c415203030034081 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 762125359 1250 762124109 762124117
    0x501060e1b0702010c0b0403080f0f0907051c0602040f090f020901090e0603070e340212071b0e240108010b0c1216030f14031b091e0414010f0603050c 66
    0x5010045006c04000c14180c011488501c82c40500b00e601c0c3c415900ca0309903626220b410380f2065034070b6005030414480c070704110700711007881e0840d103421218045c941d0f6180c02c00d0ba40071350004110000e510748100300640180c040e480c180f0004410550810815000003841081548540c189000418011800e251018030002c0064000485444000d15000c1540c3c0340e80201d45440051150280c01e44079000911440d103e060038400c1c0c1d000e041c050540e4202e031400c035046041c0940e4078000301c104212160540b404040020109121000f44903c0d03c0040f0105070384034070380d02000e951001d1403600c44913a8040f05640c10b403040380c01d03401e440720146500b42c0d10b031072090a402c5480c6600051660642c0505201c0e1300380e45031103581d407074445d04a000801c903255050281403040e10a000e0003c110001c200c50071700501d50300401c130b910382804200c0c40010350482d289500743c030030450f900707410b0740f07041c10130f800b0700c1d103810221f201014500e51618080b0f1401c10003e109110030540d58001103245448803504613 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 762126609 1250 762125359 762125363
    0x14040b0d0b07030b03191a090f011514011b0312140109050f0c280509040513060b030a0203100c1106072f0c1e06070f0501060e1b0702010c 61
    0x462151401d402c1c050700902e00500e500d4464400d421600c50189004503a0724486a0701250702d083e88070319a1180c6164410103005585140900c05000d080980240324408002c1004454404040e00c2c014808842c4000540309071f040000c001c003003414000181045113081c40d40b5103000b9482480185600f0010a00b110040540b001d1907000007401c004503802c041c1c0285c02c0180c4000882d290003030502540d1107000b901841780748100010f00740d51010f00400340c8039007d0a04100d441c01e4941c00000341190004c0328a5007001d18400c10b4401845014400c0d000c050381d064000b0056181d00d07400182d81d842210f110ba04429449544010081d4490310651490600c034030110303651806c1620340900004418421240e0455004017001d82d54500e8642c2c6100b201c10582c00380c56502c0c52030052049200c5c021035a08861a0307440e48550090b1502001404580c3c080e12031034030801c6191500c103003545e0b041d62090b84950005002d1040d00c0c450540c030150a00d1030640c000303503528194401a69040c513a100c1c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 762127859 1250 762126609 762126623
    0x50a291002102a1b0308090c100815010e0105070b0618070f11011a0d061d07090f090203070b28082e1e0905090102120108010614040b0d 60
    0x80100b0440c011404511455403d0b14004000c841d448421a007008031108410640c02c40c0d0390110010074001c40505c2e4002051000341c5c0d0348090b06a006c00e001c2003c4640180015103400100207420400e031754002c15455091074035042d40c800303c41c0020702a01078110060302c00001500403441654422418101489510311551352a02c0c05800c042c00065038500e002010582d15280702c84210010300c2800c070004281c01c240e9004041c0710040c0084c008880804651150340e5202c04800550840010751581a00200404180307040c01e0808003510400c1c2c0c061a101410002480700598000c9a100300352000c40b041c0640f91000d0030440007841800519000c0c02c405100c07105450903070310075491841000102c42c1040400042d180310140c0124603481d4494800381035030140003a4808402a07940801c011400211884e120380c4200300715842500c4007222a1f50016451124202e000c071003a00401904008004c050b241c1400100800a907100d202c0c4940d54540401c40c059030b442e041c2c0241c00d500820 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 762129109 1250 762127859 762127871
    0x3030a150512010e0607031803050a0c0b0117150408030109020306030a1506030317070e0103020901030b03151b0c0604030507080c060a050a050c0a050d0b04061701050a29100210 78
    0x2c0c424020301c2c2084c54100035009075030025103114028000c03406070540320f160b461709540c03280e1411900c0340c025250120400500c1d003198008205201840307406400c021310311845801a000b1a64a03061400d6206e41c400c02e151070801c40400d0805081e0790465904820169880d500d101c0003904280300306034000d141800740361060302c00f040d07070343c0c802000e89104e9190704807400304003c480c3c214604100e030100000380c840e120340300745944240c0103000010b00605020400b40308080c000307408d00320f401d81e45000611011040100c103048640c5004403d00d141d80629290811b42c003002c0d034440c2d000903c007900b805800202c01d0104450038048400c000c410806547d9981882204030700507041c103035000000d00742040301190703c0ea1001c404403220003000e611601d103418100004000136003030004401d503119648000014440400215001003e030303c0340300000301440c106907130004036044003028140400010181c0c4000f08000310703004085100440740c400c54460b40c107104a151140d0401c910b030790749060031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 762130359 1250 762129109 762129139
    0x5120a02010203062b17130e1b131e1706100602060606090f03070e090d030e01050f0a0e07090c0309200105091306080102031503011d03030a1505 64
    0xd400f0790302580044400548104d00c1c40b24016014491114400c8410050141c0400145654017040030400000300d0b180d0600d0154034a0034070607140e40c3c2c0003020202049080200108040c8900c0c00c40c040301c265030500704103500038201d41c860454025600c0001011408542c9813000400c40c00040230040180040e01450310905515603e090b41d6020024090341001f240e000e0000c506188902000790425080103490307400c0200c61070001e000d03103801d8012210040f410403d100301c40c900c40d640d0680200440000701c5001011520000c1301800c00e40d2520003130108840700826165005460554046500300c01040c841d403c108495110311703100b0740742a041d1101550542c020528450203034601008004e03010000c0d00026103860300c1d2074002041006100074900c0c100c0e4050801f50542d40d000149039444031002c0e030882c1d006807001003502c4503601c2c1d6201203180c2401035941440791402c0b401210704000100340c3e0b46e40000f504050015031540c0c246070994188900c03420041c0001041102660688 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 762131609 1250 762130359 762130361
    0x5060f070c0f0e0604140a090f0506040507031401020304051e0316050d091d1f120804030c090e060604021608040902031012030203090f04090807150c030e060f0405120a0201 76
    0x50300c11510400900b03c00075080d86058032480040e44c03952560b000465994000c00ca00030107231038800302d0300007500c6a084004100d00b00a543e104030303c2000180b52660441c100750500c105031400c0b901c143ea0040003000001303640402c040c50441071030201045042c0101580b0f40c158010020280c1070b550610340c82e5003e015000820500b00d204940380d030603a458032010480d101046031f9440040da01041000701e414104044045039216100c500c02e400090385998000c00508107a010903526280049000e00a01465a6061000344a5103000f080810110711044d03890b080700601d5188126404541032908215241d80860174a50007200140c0c0c454036281d601c0000e400580300c541c14010480e03404a90510050140404283c16400440c00c01100c081048084810f4103816608680c890a43d5000039030082c01911070a4801e16512069103079031911402100c400d44008801c0504000b111030060f00040b41da83e07040562100b284da80341d83c0d1820680d160a030008082da01c100340001d2403403800b0f030381 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 762132859 1250 762131609 762131639
    0x4090504060615031503080c0a05120702130204121130070608070203030109051005040207030f02011b0507061109190603051e0106030527100f050c0405060f070c 71
    0x40f44094119918140d012012151401c0c9038641312540c03400c0c1031000c9225400501420300424040320000740641d900d0301d040900c2241100c1305e250021404030704500d0301404260074000305490450819243c20710991050001c6030010b405600065014000341d201c112819401014241c101c00b00c614503140500542c2d034980b900080140524000480e289104810352802402594015411079090000d408020710028120a44044015800003155220707400034242e0640240c403080f069244640019007540c10003070b0f18075280090340d000d035121160008150380d0b0460b04560001013401c0c0c01402003c1620034054829482200d4130380c04030000c031038818140241c81099600780314a48546604460340d0540000940b241d0038100c2c0140255032181e48481d603c01c1000f2050402c03983c0c1851200c2c4c0d00c100d031010620182d00140c1213088420f8840c026480840050101080949807260400c14603018900829200c2c4600040441d14900b2002c00d0b28185a004180040d040350754100b01099603c0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 762134109 1250 762132859 762132869
    0x801020a0917060f0c0a020a02040c08071701060203031603060b03101a040b0a1b0b04030225050f061303080301140103140f01031121030d0b0a210206040905040606 72
    0x84040003140500d400441d04034054400c1e4064904e0030b454048186000781c000940a4045208000804015030f8890141c1101e40441c0e17160502c103403d01d20001490044042014100c03544410010802d0590000446e680052711034020000828512800c0300540304942c400c000f0488040240160202d896000b001207030030600300c03090214800d00c00d64105004500ca11015044184400ce8166002d43d460155502c3d6525241c110031002d5078031189407240545054006034030020900d004004000000035080300d150101140c42442e013000200364944042919026550100d00d400b00381c190b5540c150061279000601c1526036840d00803941d038086030b001c15140040d04010000a0b14070380000c0c954042e445089810f0001c0c0e0031500e44044040d402d020060300310340702c40340058101001400c10a54560007034091a0b907020510681e406031401d141859200d000341090401555404416800002102c40310340c0740c100700227000042060199078000c0c6001c5040c0300811040008c0ba50000c800e6031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 762135359 1250 762134109 762134129
    0x6050a0b0109050d0308060904141f051b0405060a090810020703020c040603110f030c0613050406060e01170c0d1802030d140906221d1312080901060801020a09 70
    0xb643c8200308406070390600c0703003d00400c0030030011640034101005940d40c402e01031440d5058180b0100541441c2c0100341090803214401070b0f2100e440d8000078020b880d040000c4c1194100c0c500c0c80070f03070f404613144100e00c0780c0d5104100004d413400069000e0021500203100c40400d6886408100403108041e500050040b00103015002c00000e05152a201e91401d0300c3e000341120030000e508006010fa0081301203409030f858030642c404e4605d180e503444000c04e8048015a22508034030310f03200610050b06c00581286040c41100c2c9403502640c3da001c0b0402c040707003c1c4203e02000360740301c001c2e05025600c610f508820507142004004050021007403059800d403403099040758118070004400319401d1074403450151f0704400030015401c003860180c010306441d1000c07003008202c0420403140703c4bc0f9000d465101040088850440b00038550300c0240d5582c1c022072411100d980d004c00c907910300c0c2c2003c607144401814000040f01003000c54009501c00f40c050604070008560b1498000c1001d4850f0766203204c0e1114403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 762136609 1250 762135359 762135377
    0x61d0f070b0901030c03060503030d0e0705060c030306010807180906080607030605100f02030f031e070e06030f04051009060e010f15052803031707050306100806040906050a0b01 78
    0x84800011100c084820140005061051490044002d0200c07400240201529098040740581d810302c001c00000b20300000024000d01c1c1e03a02d200303050501951109120300c1060040145104c004000c60368480f90034608210165140c0000b519080c4452544412414044070041118079150f4410420b03170b1910000c40d41941c0d0f070070743e0490640b8504e0050f50f801140c100e004081850188680b0a0884118015641410501700900c441604116a803803540a000f21a4400c0021201602c58018141c0e05d03019001e5400b40c40071030607500c0302030991221000c0b203000080902c030702400b00f030b0181254a4005c0c4003e00460400034050320b0001d0501011f54602809421013002c01e00c42c0020702c401110b900a0030619150402000080746842b96035103055030201d403125040d03140e1450000e07601c00d848181000c15005038003c0c0540b0000c1042003800806c10900889030740d0800048541000d80c82c1c0004680e0b5040041400340803500c40c0104071600301b40920040052a8100c01c070301500a99464140d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 762137859 1250 762136609 762136633
    0xf0f03030f15010e12010b0301021903060f2d0e0415110c0604060c050403050703050619020301050f100e030a03020f0d0309030f05030402040213260601061416061d 72
    0x4542c40801003408900203244500032420b0900c5c5500c40340c4c0b0080300010b032144900b80841d0981c0e004480741c4550060680c0b00040f0344c1d40610031200600204902d1400c07190411900000440c2a81004480f40440009010395100c0140c03043c0b001d000c000590005a05007403402c400e0b01c00d040c0c01c01925090618403612402400b410070b13601d86444000003092592034640b920002441d040d4846030806c942000040f0105908004030802544180010800c0e440c12400c12680080030413847e140c0140104010402c690302c1e02c224040788203086941507003500160000740c5101ea1014019909802841d0341842455004035040c0564604402920017010061004500b110801100100400c0c43d11080300f00c03162141e009517502a1015000520703118032003840452840056100e40b03001100e8400c56404e4051074204140c0c0d01040c0c50081ca2154107041015254021321a1280910740c000709a500c01d8002224080d50b55030b81150081020035510001c1c24a810790182402c503582c07180d8004014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 762139109 1250 762137859 762137881
    0x3160803043c1e05030307020c09010302060a050c0a1b0503010509012705150414010b01140313080f0a0e030f0705102006150f03070f05010e030f0f03030f 68
    0x10380c80450184211903503200341010200c1c071180010580d107000c0e0030501c0d00710402c9114a4a084030f4004e0f0011603e0f4030b01440000d1411420f2110503020b40c4118004100503103d00c01901c40800b124100b19480b4428101920b26210340b107240589103580114041e00d031200240c400d07205941094000380025510203a216090300d00e44801004002e200c0e06242e811081e1540140e06201c0c4502c1c1030798640056a81c21214410b0b0a403000e5030300d6588100c41d0808450244980d00543c04203007460403449030300c401d801d429408010700380001c02c01001240d100700304003101116040150702a80c0c54440210a20061605e04403151150107485003250b80180d0f26030004010b07084503002040a01060400481190403181a030700c01c5c40500301e40042a1080481072010b0307449075100941c03450041511001700400080c0269100d03000343c2000d2014022500070b403a02d2426034600f800c15542c11034800e00030034540001c002800c0c4541c0681d40814100314030102c011406103031000c500445a4071030f40c200398 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 762140359 1250 762139109 762139163
    0x51c060911091c080c030a030606091401020607080c0706090c06090501050c0d030902010c02030f01090209011d1b040b0a031a12030a0309050f01180204050c0f16050316080304 77
    0x20741c1c8000e045500005200c040c103545580320b48280304d8a400c04481044140c41d5401152200c00440c0e181c180074445603a0240c500300042c414140441c041c00025070000c2e440321809401c01c0d08004011000504407501034040350b03546079220200b00312a115a00b80751030400454062580090411f41c800541c40d8442c2c010340760200100030203080ca1140748002900103144d0980102d041c0070808900e9405031b0f4061110343c001104910021503c51054410000700c1e01051f04000d0a4000c62003801301e501e074101d803205038030104c400d0007004074080a501e07521441c081c0c1d03400a02c00314030005407505000e81c541c11041f20700c0e002c100c241c004094050700f0000210f0400f688054103034001c3c8401c140300d5120750401d1285a000c1c50650f004840d085080c2400d5945442058404030410302402003182010b110307544d400780c90702c01110700300074000c44062400d10039079004840c1d03511101030800078800103100322404907039a0044140c90410034a0495415003044400f5180c4500c41c404084403032078210314003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 762141609 1250 762140359 762140377
    0x80310050a1805060307050402030a02030603010605010503191107050105010602031b01061d1f060f0e0d020a03021005120711010b010905090a09050f010501060e0a120b0a0c051c060911 81
    0x14403000c00500c0710030801000c1c004d11060f0b05100d844d00029450704d0380d20066019600c000c00242e0741c0d2801c0d42c249803c3d128164021410882c00700308200103013040080820300e11041a00100300d00031004130a80c0c40303001342ca80107850795207018000160030b07400000408018400c040c1c10100c09205165003422283e40384a041041604884010300c2c03000691312840c0d0100b04043c5541900a84d11855400c065440e044000481ca19054160340c2640006a064504800f2181151111901d134049481c5040d00e00c80207004045103651180058094425500380900c031800310f10301840c0c0900010b11080140d0502d9a05501e00814042107503c16001c1c00305641018104850f9520f41c070322000001c0140c00000d68460203000e03003c1000000030701415000b010203554045024604108004089031550310050412031032400400000341d842d001580d00c12007a5600098582e400502a80e0a100c1c44d400d21b19611840100e40c00400d6880c1d103e00251000500f04002c0408901680f4a00d4801c40b512 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 762142859 1250 762141609 762141629
    0x5070813050a03050d1e02130e0105030a020f0d06050717010b13061103070f08040e0c070c0e0618040b18030405030309060f040b1b191208061903080310050a 69
    0x8440b0209000300c0042c1200446000c0001d99040b10307201082c3e1007410041002d04a035000070795111112180da404030043c0101d21300c00609545000d001075603032000740c60028001c40b04042d1020955a5410380185261b40000c0144074900c0c0a00b0018400040c1d0001019040051400480c1c1d0200341420745148171801e210401c989814030b102030340d84600c8031005240c02c8c0300030003441d00021016a90170180720b01c504005504c9170300305100c401e0301d43c0c401484050307800010f00a40e4041192007160a08590301825940501d4480b00086401c013a040d480341c100b40c2c0790304811701007041416001c0d0b078421011744500300351000c40020300c941c0744e224a1040644c0743d8402e000354000752409600500500004180caa0700d0b20341c1e1050300003c01d4003c0c00900b1242040000c01007100f0805004050a2840c41400c040c00c02e101035030349a200900f00d10454082107480400981c0c0c3e500d4500103441c480851078040e042c03086c0d4901d030910407540112006200160781800000c0d007814000c00e418107541c0c220170 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 762144109 1250 762142859 762142873
    0x20118020102030a1409030f010605120a02030327372d0806090f0c060f0403030e04060305101a040506240909151f1b03050c060a0507081305 62
    0x41c0443d0b40032084103001322804401c2206c002c1c5503900300308150b000d400304e00010554601c2d060400401e5518100490810f8204503a4240141d60100440d000c3d5440d00c44031030803000307091100b400b441407460504d61300510b0001e01031900111800d4032400f142c99131001d000045054400c58110358220b441209c90020f00d0b109080e0128032404180401c1d02400d070301c42501507a5a098407803910174107440c1003496401c40c0e0044e02c100c07a4240809203525009503400303487d040700180001c0c0c0d544034621010f010410740c0807030808503a40d030b5042107000315081070441e46068014140400204601001c0c0520b590420b60644681c0c2458000c5910030f500c0180300c2c1b103004800c000309000c1d0f18522841b00154607400c1080d880b29a640ea28840e00580140400424a0500c1c000303100c079500c80c107103450103e0030060b00750105043d0b11005810038012401804444000030b4030f8141c1c1e09001d0700c882007003180162820071415659645c000d910420302562110003c7e142c0e1001d803001e880204c080036000345c04c114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 762145359 1250 762144109 762144127
    0xd0b060114070b13050706020109050309040c03090f0501060f0e010e16020f070b0d0e033c0f071a010605031515070b0a0c030b030309040c2c0102011802010203 70
    0x1c02140300094101082501d8030325590740ba407160300350403513000201c041c8180d010802c0c40010428040a442940020448145035840759030344c0c2d0040c2e149580c8110b403280356008059209400110b181580710080300c036048c00c14905103021342402d0103110b20071401c05400160000c407a1074498100c0d600491031191075120f008102d05103a0310583c0e103900b5171150348807a20425108005d030800030b003c030f101440d480340f041040841c150b52007490004001d03841403240e40e51781c80d912401d001480300444c1000d220701c185040a004000c004401000d80c2e640301040c1d040220820744020842280714581e5052440010b503599080712900307004460004030140005002504c1c0281e0b0030101060040580743d59030026560303e02d0310b0b440b00208450720740202e002c3c86207038004c5000c4c0014000701030800b88481d04001c4007103590380c00b48080962041d03494107085c51000d030042c40300c100312140900003040c00c04a010a00580c080e00414518010740ca001000001507400c0c00801c42c0311a4140c0c040d524180b045 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 762146609 1250 762145359 762145367
    0xe071e030f0f200306010c1205090f0a081b04060b04060201060914040f110303090d060f0b0901060c0609060209101d0a0e0f04020f120129030703080c0c130f05060d0b0601 75
    0x42145d81401080303c07a10011842c64602d00348031211b641daa03075603600036010a01000780d440c0522a0300500c1c074014203122400010425620039107680c00481c000100c61800038014000d96840f08256000001b40410b0580d07041d0000030a0b1103400c0d0382403055016886044d240b03280211806882c40c2d45510031200024610399503414002070040881e0305081004001030f115042f802c0302120013542d50075400c22030007070034002c0110109089640040c00c2d0701d07028018107030f0325a61038010462540d40c006013003040440c5d81a80d10803180505524810215180c0c05804100030800f130b083c4000d501400c120a82c5003544030b00c0700f91040794804030f815840e0300012801d100303800392041341e01100d40907a120643d00d400b510344109040c4c0724008503600300003100c001e04944000401b02041c5080f0805804a91030000700c0c4021207500842d030681d20041d2568443c200306454840c5980001071120300482641e964220149018451004000c03d484903000c020441c00c2580000340044c00c5080080c10941c00303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 762147859 1250 762146609 762146611
    0x50f1506090411100f030f0b1c020d0f0c030c0b25020f0919140c03040f05120a02100609021c0f110706021e130e071e030f0f2003 57
    0x443c1c000b5000d14103621000441500580e40c10800140c5200582a91141e1500454200001c1000300300a9401d24201041d44180c0180c00d00910000382d8200c6411900c03022142030480d508041100d014881c02d18001c486030320903220a0744c910400020214105011600729102061b050038280c0b00401c140c60b50320b072140c00b441400ea0340100150400c005540b2030005442c841c0030841a464440040b4424450072581d410900300704003400207003041a030384000022241c02540089122144000c0c03458058030b001136045201e216070a02007200c4c840240c00068010b40e0450302c00d02031144948441c0c8940480c0034180484d41858244450203a0300f28035540202a04290301001040c03429424028548940c0040c02c111001540006e80d41200c0301c45480292031800d68a000328941400d0ba0100460381c280360141c0c1804988441c0131408050184041c00001d420809094039185007202014000b4580d5411404042c0e0404280030040500e40c886ca120008045000c80340344104005c1488203504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 762149109 1250 762147859 762147863
    0x20127020f130c0f02070602030a0905060f0c070905070801050906130908041a12010902070c090c02032a072408190603140d05030c0316030f02030112050f15060904 72
    0x302c0b000041441c0380c0700d0240d9400708803561501100300d41d0050000745083e13040e0b0700000440d0400d0004100c2d540d84450309104a43d0100c61980e100c0c80d07000c01c6070140d445005c0c11174406100b041000900d0b20001d80002d8815401600c0f80440781c2c0c1d940041c002d154400f195000c3d0310240c1040d800a20145a91041c0301c01e034003640d445400d1549a02200c80110440700c0024441440401c4000000141580c1d003400b400340403c05504203001d40e603441215070a2030107407442c29520f50803002d06491080065070780c0f94a0351031103103581740c02078006070040c4510004540040d0040c80c40210b5019040351840d00a808850041260041c2c601400c803201440074080d03d100c56001c0c03041107159041c5000c0c46d00907600440c240c100c0c1c0d4540c40d00306494a111005a0f8040c04002d00400c010744406005480d84480c801d400c0124005016408800401000940384043c0d4070100c008904400640b204c00d42c82446501119100000c0580d000c0e9200140400c1d035110314030030780004005d401c01003480b98000e4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 762150359 1250 762149109 762149119
    0x6030e0105100b031f083007080c0307050601030c0513060b090607060b03030a090e0f04050709020315130b0102070b090a03030c03090b1c050c0a0c031b050f0706020127020f 76
    0x8001c186030117400c000c95480fa00f2194401c440314040141c00b40d1041c2181d50019009035440c13544516018014014500c0c00740c025040803410840d402e0044c021210000d43c0541958415038503840c0c01785c2c0703c4070b8900a0034014280b0b602942000348640c810a400e442c0040700c1e5508041900c8104552503000c40307022120103440300e4110600340c4042000c0d00926030b65440c0c41007841e045c2405a4882d05001301035481428143d010b001c04501c003c10341b9401d4034100f000160b640ea4403041e1440052a40340600c5030001e0b04103c001410555546c4490b505200903402d56050035568810b000160056090407580288100400c000084c010f03c0c4a4241512038182141d15a5607003409150341c1e000304800a81d505509c2c44070b0f0400300900d209840d80207240425041c180301d151900245856500e08009060000c80412000907503824003429101513071202c1181c1058a0042c6116210a11841240055070a2242220664400c07070603000300102041f00640005005030200700181e00c2031140f02c0c0d000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 762151609 1250 762150359 762150391
    0xb0f060f0715050403020c010927060b0a110c040209010806130b1e0103050112030804121809020c0c040b030a0b0c070b130219180506031005010f06030e0105100b03 72
    0xb0300c0340344000903120414000040c00d03140070304029040c44143d480d141d0401214080c10300c0758a54491041811881d6000c0c00707500307a850046080700811a0b904040103514010444003580c40c0c0c0021001032403030010043d1444c4050207410b01081c0d00407440c40c03502180c0140001295824a0b034880b441035126950007150301104100401c62003000c0c1c04669410b5401d000060400d940c05028a50042c1341c071014400410740180c07002010941c000d400104020890311038528218480d1032141e9400141c10000c441181c0d8918130701000790f01c034080102c02e900130468841c0c028645445004040300c00500a401c44220541c2c9030046140000c10021010809100381004512804c80007407054440c030880301c0c400403083c01080107080f05103c0c1704002c45c0410500344000d940c041d10401c01440c502d14003280c2601c2e0000001c0c145040751800703541c068985030000031b9001400b03003407808542840d03d0400c80c0307030103d9440900782c4500716000a060704d4041410070000c441d20004590010b0720040b03510038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 762152859 1250 762151609 762151613
    0x37050715050f0906160f0c0c150203040806130c0b0a030609050c09010806030d020c151905041e0807030b1305011a0102100905070e040201120f021305040b0f060f07 72
    0x8844042d907900e481c01e5500400c000002c1820031066030400d0b204060502903014001e8010510804a00c0100802c12001040f100704410131112001420b001801028902c0d00f11000955a81040c41000294400c0e00c0106401d41d20317054a400249410072900d4a0090803c080101d0642c0482002d104140c2e441c24002542c034240e00c201d5000704810b551055481400d80001098100050a26403294005070f240300b000a80020380f0800c104000d941c020055003119411000030302401070250115908509000707107082e0b0260090083c4e0740345502c1c0c159205629910305901074a2409460b6560780203c0080c8086550084a641c0c00f0508941e84002c4250b10b80c1c60501b56040130800080c100c3d0b0784094403c107507030140440c115291580004019092203130701da2581e00e4500b0301c02d940d010703950b20002c2401d6912800303281c0082003030494280704070282400488020b50041d000700d41445561180403640b851309020314060707040c1c010030710003004003080100030046d407007041c48201c210010008200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 762154109 1250 762152859 762152861
    0x50319020309072d091109120f0d08090a06020d0b0619020c1527030607020606100801060e210d0206042109271137050715 54
    0x220418014000d04101c40c5045000107544c2403014120000301001c03051500d00042d40503070b4100302c500074480801c0d210b4601c011155a07203e40145640c00c0340c01d82d8840c41480d2400514403407031a000204440c50100110001c50300b101c8291440751580d00318000ca0f00204160307070050500c1291301900000e80003031190024425a016201380f182c8401c0c210000d8005a4050080780c400c40010755443e04c41c00d03104501d0100911860111214802c6c040f1032035039885040e100340007412030b40a4110b41081c00c11450182d60b800d01250990300c070340001140d18240911031003410781268900e44444010915020801188600043c0b1221000c3d40c440c00692044900b0000c901d0b900d2050b4028040504203800e00c003072a2819000510740c4600300042c11341500d0761005e40c5c0d00880f202c2a4091000d141180300c5200c61500600c9050111424411203800090760800242440b0103034050b200b10401c0542c18507800e071031003100903d50202c1d00ea641c1c6c1c036803240202c0c028500e5a101716140c04680c4c1115000c04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 762155359 1250 762154109 762154111
    0xa05090106021c140904050a0b04050405100b150301170c210c030a05031e070204060b031609030308070e0301020f0a110d03140112060209090a1b1107060503190203 72
    0x1c01a0b220f10a9038000d100c0110612030741d01500d26144014403640540c4c16000c1c031408152600440e503880020340b446602da07000c0882840d0040050149051600b0404e0751082c0441002c807107546081c0c400c08843c5007160700030503000003020781181182e180c058030012513100e000b607a01140c02012160315580ea10644000d607c0000f2040c03098103902000065031400c1c1c042e1500c68001d5108015040c081000001a1040503141c20b0114a00b50600e010394603550040420003500241441c2e0040783c48424000603500c04d00d00a280401c068403c1c4400b101d4420342c3c1c0c40041e000c10074807008954001d210341c070a100c4c6000081c0c009450300484503200b44e102e42c8006951000207244003020f045424083c4844110909586401d1240c281401d00c9a1200603040c480c0303205e62440402c05204225194060700c01c0d50100401c01c01407032800c100500007a00d1100d924012241d1025000e25031035018420040c40046800002d00740c850514006642aa10181c0f05842c0e03a4802c07c5c5120410b0b60350b000075 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 762156609 1250 762155359 762155369
    0x2502120d0305070219150209032503150506090429040b010509010b04060807081e0907031b0e0115050c0703260306090402010309020103020409020726070f110a050901 73
    0x155890b03c0100207007000184001c00d40c01d0902d04099001141c40001c0c81901d03030310b032001c00503510710310880046d18207400910070080c4a840d8520f2040b00c01031048904007124050b1f03400c080c016004888800c00c0300c0d011039178264000700c1400802c4c045079280034440c10780b004804e402c2c02103074644018401684422501128404058001800a0b05110340740c03900500520401c0c9081c54284030000c2e080000041243c0200400c0c030001034140091006030103049494443d801d042c50030b00030100c648495040c0400d90b8031050390f034405440c0d4850031203102d00b1502078011202c40c5908200348810f40344210a4041c0c104030040c802400741030002d0115800841c410301d180e54040ea4a20b41400600e007040c01800b81c5420203004019450701d03001c1005610503424600042c001603a880160028002c6801400e00700d40701241d003a042044424103440c4500071f696450011001e00c423051141c5101c0c01d10018281244640744600040d190038410481d883d00402040301c181d100c40120342e110600341c0c44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 762157859 1250 762156609 762156611
    0x61c0507180f061a2502040504110a0b0a020304061b141b0105090a060c030314010605090f091003170d020a120507020604050c12010e030f04030b09032502120d03 71
    0x846a0096124800007840304a5100403503c40074000d00015006402e009100c40044061a80500d1310341c1d1170540350654000c0003001541090309100d0b042d22030b04071049014051030400070504284010039550036402c1035000314985801c0c05001c44001c030644080000008444200900194881500740c8801003004000e1481042c80b002c0d540305083e580e511076042c49000c0002014507180c82103005d0a94400d4209452102d03038034542100140140194509aa49010008100c0c99400341c0100545c03402190750300c954000080c10410700010070f4030001c070b800c099403000b04001a1011143c4600040d503c00039401c00182da4585420399000304070103400150b41c2044000111000e200e280d402174854401895240b40a42c5c440350366422000b5901d00c12144241c40084081d0250004091a601002903a0316104511680c055a03001400121940d61000340003440308000081591100046505007d081040409000340c0c500410201030743c1003800c2c00074400d03000307100300150341e0102d4080c0c0d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 762159109 1250 762157859 762157871
    0x192301050c0d0f1b020d020904030e03060702061006080108191a010902040501090e270712110a0e09030a050a0509030102070c050406140d080904090203151e061c050718 74
    0x28005020103c1ca5503030135001820301c410326001d80c440e2614042c0c070f143e040d143c01c0d0b00c503200c50074180c2d20b000c03038075500c16450710400c0c040051155010441900440c07298005901103501c8100c26200b0400034098885a9881100b02d204844c0002c15543c0d4030600904d00d2002c0c0d9949001001620302c400d0b0855a00d65030005800c02640d640414160001c003080c002c03c50f45405c1c03c840007800801050500400341d00d00604008502509110040003000021103112023b07403145031020a6612a46025205102c0310400040380d00c0320740ea0461203820b60034090340c41e0160a882c1030307400307421003c1000200241444508595182480241106401040110480d80c40d1001304401e8800d980c04c000d491011070001d02d5507e40703078a41c0000d01d841d881006151607a5260004c900149400b00000e9814803034400c00d441b414a41000c0903000704012520009060503101824114400c00d407a815000964669410a280c01c1c04807480e001a100300283c0d41115507038119001c103d01c2e00010000282d503650 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 762160359 1250 762159109 762159137
    0x604030506221104051005120f0f1c0c0c0320040c02010b010e011d150a02011b051c110408031c0c210618060302192301050c0d 56
    0x2d200d81c09084508140d88155825691402c4410100e01c48403401180c5480c0420072006202445002030480134000221900c80444215500c28404000d00154001c2140359a18400b0105501e5894009812180280c3c01035000440740727051054426903c81c0700e08180440022141c1444056039000f40512310194241310040008880c2c1074110f04095a14000d09100d45903000042141c8801e024200810509074014000440044440c40035610804a403070a60000d0452000351029150319402003100b2003002e01005441c480d0201403102154090054440d0308110005806900388041b4001ca094500700001e04040d0304560401d01003a00041081110101d00086442c18101a0b200901400015030000b07070500400000c50a850000d0040c82040303481c0e075400880c0108214511080700d000340e00a410002c08090008174801e0201c80c982400b20185040704009440000518031519120000842d610442ea03030041d80c1072040a0003414689882030003403071b40c108404d40716032a00b01248 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 762161609 1250 762160359 762160381
    0xc13060528031a1e040c020c0603100e010b0f0f0304030302190918110414032e05070503040302060c0d060b030f090c090c0409090c0b070c0302090112030804200604030506 75
    0x500e0359401941e00a0002a200720081000380720300d0130540d0f0003e20000d607010300b02d00f4061400b100b0b5400c510000107209402c00c42c1c900c1e980840d02c01c80d48811040e6200c2801c0101441400c41c56040b00a052203041d1020007824002c0d40c1191103824018500202000300640c000206100d010200c1c1c0079030307420444580c0b01d1003020324096030000100400360100d0300403900d602541c0140010240744411010442d1020882000580d840100c803046245940c0c0c103c80849103069400300200e0300301000310f0650340c0610182e0b802039906030050300f855590b190855055800c406c80503c1d440b502c40c200000c50100c4a801035001c1e1f0080003880c0f1071440c1140031207160506804141c0e00441030501003140b240c21a0050710f080d9500b498001c0381c024441e08000340203110981141c1c506000008043d820005041c01050880c0d10a88500040742e9131894186107800702004003a000c0b0701d803400001e000500c9040c0c1d029410f0000e414000c04985c1d204007059098106070400c0300c0d50390060f01072180c07001079 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 762162859 1250 762161609 762161651
    0x6040501051515090402070c090209040f06060509130605040216020f0909120a03020f0c01020721200708032a0d050d0b0a2106050c1306052803 63
    0x89864409142c2c0c001c2000301d294450001000d001c41c41d0049050941a80e541e01211f030307099042000e0541003034662550314002c0d40300381e0450303100742d01d040920540d001c010b00481c021181c4070385034a402c10f014001841009001080d5000c0f040d030740e842010600307030760700e2015120004002c803850754000803602c14424000300d5209038510034110b0404000304103100041c1d500094409421490329100300981c1a0702038011000280301c00c40c4003141c4c4520032001540a40121401010454818030000368680141d00e540009a000102116520043c0d000038003500c0509240c101c0c00c540a007603442d0100746c00c54202400994401e08215150041d1419140c00c0c040404e00000240910352400705000e04540320324988584c016440d45031004440e0340701d0400e01c0003032050044042c203d03031031b00031180d1454203c29001c42c0c440c0d00d0400810340100d1003000340c8220340c69442c196100241008000c0e0703202d4000101e065000240d40d041802c40c080c85000d101d5156071581c4000c12051180c0b030b6a00700080e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 762164109 1250 762162859 762162871
    0x9060f051804020d1410091101032d0218150304050d05030106120507022b020f0f0c0f0310090c150e0306180a2009010f120b0a18050604050105 63
    0x558078040c44096541d80b9440d951a903440045e81d807003241c101c441c1030709000d43c10454030070051a01c120082803200c4040081d910726407d0b84c00308448410740c1682000110340454030aa8080040d0b00e101854072643d00500c20401d04020600c070500d0024005042c0340a1344074240c11148002c400d01c41001070400400366500d01c2c5050060866050000080403002000382e034001c0c20f40c03514049556580203010080c03290903011000344d00c040e6100c1c11040035600c640820f100600c030f60850b6031100200421000d603815440f01c00303460034045074010020b0914240c0b5035203a050140c0301d000c0f074141080e80b0640002500c00d50882681c079141003401d000b4001891100814410030000c1e03000c0301e5078041503040c1d2203035110341c904610781242d92a0724a4003c1c014801881500c0c1d104c4803103400d0048031400a0620021141c0441680e240c5d10150344828a91003801000c00100d50028002000d0103006540200410b034006000d41d03400404070100d6a0b250001e5581e80c0140050006002c03080c090306038802 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 762165359 1250 762164109 762164149
    0x110603070c06180b1602160302011e030e1b030d081e040c08030a0302040f17030a110a021f17060a06031d030a2a081204060609060f05 59
    0x11034455406418049400e400404282c0d90b000140d038051603072000c410003035070410340240003403411050040740c11074102c40c001c000d482250040c6c0200b00144a0900a480e410f130344d19440c0707590b000b0408036040d1511422205064451205110740142001a9920380300039500d4044c1030703103400b014076007002200d80300d01003040003003010098000d8002aa01d07900381503104400070030b039650f810000000d41c803941013850030340130000750903090703651540280007580d40b050014402280d9846050746000c450010202c03d50308244104448107014042030345141e0901000e540315940750303500240107ca8410103a0186200848030301030003d500c004030f140448144a4502100e050410000d02011942d20844040548420b810f030040c0f2510040c00f00b40395100030480340c8820f101d10380600000004503210f08044c88404d162068254100c900d2118150805e0603d403602c5005281c0341d81507070b0020301c247c07801a00c807000094800658410340004002007100e40741381508050411608952192007a5868 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 762166609 1250 762165359 762165361
    0x301061205060d200406090915061d1e01031a100f051003060308041d0a090201050d1a03060106021b03070f050103090c0803130504110a0c030509040e01020d09110603 73
    0x507071036544a4643ca941c0060100c000a542001942d08108182013400d03003240c201100050020708540000a86500c01c403c1d10301d00300d19050396941125082d1140c049048108104180300030216008645c1001d000601004142c200040b41c0075041c800382e1040b01d010b008989850f407090408005982c11a49003407403204250f2800c900700604e12094000e41d4841c1e1f50b0f11018250450280d8009402964054204e9450700c1d07840700e561010510800444103a0030040e00080c0a040301c0e4499071107040da05840309030612801009240c004c001044c541e0320340082903002c00000f07035420020f442c004c04040c2d000707284000303441402580c40404c13040954002c1c0d100410502c0303041545030032a0f0a450080c07a00084588181c10055010905640242c10a0100081006509504101c0c00050356004e440501c0f140c09024841c0701a4801d003000300000515004050740041e12400040c40b5143d40100041185000d0064107401c84e8441014204520380d03a480c0c8a08001e410443d11242d62000c4401c81c2c11 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 762167859 1250 762166609 762166621
    0x18011e120213020f09120f060601080403080103060f0b0d0b150d020105040308220b0409050106111515040c020604110105030c03070809070e01080105070801090b030c0f13110301061205 81
    0x102d031014404a1415401040c40e824001218003654001c0700010015580030300100002c0d80c4408242c08800e07e07900941001808a500807825180610750547d078108050386180c0701c40d4010040e02aa9981280c2c0f5000c2c001c0c0d2a58500d040d40c460360b402000342d0303851400c1440403100d107400441c010328041e00e4220440d501603038114050764100e0b500031212680d154170803941c807011510725590b40d590030501c0b41c03808604280800068406e892045400700b0a0382d80325a01507400c90403900c00c00c103060b4080111551b00010582d591a00010609a4000317429078050001d01901c0c180c2c0013010050344a0020803090008111010303005041c00e0805d01c0c0365082060208441d07100c0180907030203110420b00444e00ca09020440d810040105141c01401c6585584055000c0e02080c1c840c000021141400400e0318204e13842052031400004004040e4440c6113421b102c4120101ca07041ca80c0114030301405c09100d220b40c00784900041c10040201d9596040c14000b5000030040c60542080368500010842 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 762169109 1250 762167859 762167869
    0xc10050c070b04050a0f1506061b0204020a140f0a1b050a1202070305060c0d050a0608191109090703030f050a0f0c0f0507090e010f1401060c0218011e1202 68
    0x1a0441d00300308402d070b5a5680d030a00c1417402c422840010b124900c08214a4140a1000024060b480320700806004030790b030f40c40046603220219180c0e0000c0605031081b00c0b0043c902039004184180352400d042c10110341c1d02c0b5002c003641c2c04c10003111055030389c0094000413842c1d10200c4030107403860248490980006603103d0540c0c0e50a2550003e00c0c180200782850301e080c0c02000040015a030003011910640740c10483c0b140c40ba041400c00504943c2400040781c030854081c00f17401c0968401400402800e070303010707100c490340200341c800680b600746400503829650f0300c84140c903520920003c001011514994a0010114008003a8040401c8001d00202c15000e50201c0b041e0360744855031030070501d1b000650801001240c03c0d150024128440e90703c00180c5802203411004000c007100c0001c0184801540d2190280e4060000c0865400e0030400180542409001c05400c03441c0041c2045900819180c4007140c00c2d1803c0e0020b01010440520f2044d004416102c4030700580b6500d01c0240e800761555003c55 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 762170359 1250 762169109 762169117
    0x509040e0327030f030a090f06020c011d0604050402070c0815150d06020d05041220061305070806070804020a05040c02100c0318030e03010f02030f0a090512040b0c10050c 75
    0x40d0090030103502007020f40d0104000301d5010495420780c3e80e1140c0a41028013404400d208003035008240c880c000039000e00124018140c0f0506840d10030b014540ca10f0346c01000200e003040c20fa80070300280404119a2540d202610445200300350303000990782010201483c042c4064810103a00d85000100180d82040c0041054011409c1e074050540000628112010307004141940045c28604810401800300c50580007801e08010744544085007a442981c000c416018403002c100c990080b0701003420300d0042c001d4600310343d01880135102e025403240400c904000e400c1d580c207000540d03003505010940c0f074600b404000030001214100f08812169230040d45032124a01d245041d83c0d91032404407500d038040d41008149090703000d42d01040ca000c51401405a28a28428a01941c40c0150380701d0461400d1080380d026010745580b82803e603a40c81000000380c00c0c680070444480c050301100c0c0b044402d210000c2d0024054080005468803031803406146001c1007200842d141c01c0c200024000c2c14040d0404603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 762171609 1250 762170359 762170407
    0x60b0405070c1209050405160801090507020a0f051509030408011803090302130b1c03080a090c0308030709080d03060314070b0f1803070e0906150f0108090118030509040e03 76
    0x1e00b04120f140105803192039240e8070040d0007a04080420110000e8007905540c3c0c9a1a5101d80085903210040d00701111400c65507200560f101c400203001050a000d03002c4109841141190035852600c0300003154580c050341d0074184c5510210b0180154902806560605820a01881c5402c0104d8034000d0810213240300290150724020816050b03050706402c1051008809000820701b190310700c5241c048100066001c0d0f000130710140101e800c48000d4061014040d40100003d04181c0c10760725810742ca540040c10718000d000c0b4148002609440a02c0806800000c40d18000b805518500705841210741103400328416801c494002c2c13021500b000c00784c0c0c07130600c04200425120034480c0034003040c89519200715503044c0308420000552400740c0001d02c2c4100d65040c180c03101a10351034804c100d50144008010340c000b060048540ca654401c00781d035a4401042c1c2c0000c03c00e17000b142c0c0c001d007504503803203c1030700000c000044494160070940505040c1501010055260000c416180d04190202c0242 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 762172859 1250 762171609 762171623
    0x20c1215010e180a03050405030c092421070608010b030f0a02090103060f1509080f0316020a03060c08040201030507140306040b0a0e0a0603060516051206120f0a060b0405070c 77
    0x80f0302e0310500d803207281e4140d5102204030380080780d0500b4090300c160001c1c070629219200c0c0540351000f605000300c4c0300f80502808a402c0d12140b0072103590306ea42224000000b60880e0782c10540e580c01068056052141c8560f40d8040d050807424101d00502d42c80f4140c1040c43c03640010018002e1071300b1070000c050360001046c1001600c0300e4020004a001d08096440100400407906000c26405406100038110714102c0d00c0d041501595000780356111203c1c0b03500c0041d00e070014807200009205011061603600c1c030080884000302d881c0d56401c02204c2c41e144001c40011480810001103503098801c09811003524106600480700e2400c49032040d102c0205040d000316142c1b4121682a00d680e21b070304002d010304030404c242c05c2c5070410403c002030095120507115141810041400c0030a2096022810881556081e00d810740304054888800b0b2f0103095142c025541c4100110301400c1400f00380c40074515a80640300902480c240041590110002c492280e8034042c1072003140d0f50042c90405042d075020030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 762174109 1250 762172859 762172861
    0x130207021323280b090901090302120a1e030e0f070503070b0904020403060c05130e06060a111507030f060e010b03040b1b03130201030f0515130219020c1215010e 71
    0x3054503001a91801c00403c0810326080e9140f0070700c154110902800f0305403034440c0c40b5640c0d003d4160980b2030100b809005030700521240f84468031504003c040080d540d0810580210072440781e807551040c0c001c2c2e0100040d55a059035000801c05101d101003014a010091503070a0403c400030740c861005200383c130403601c4000307040342c4180c413590150381c02160010000c0040841124028002e50b0003540c0800018504240100c3c840d840641c0160203120003402071030a195807034005a5400301c002800c503032240316641c0c544612030035000b1058031840c0c03a5a004a07190094022660a490094100d0076001c203481c0014410905544240c940c0725402062004198441c0703051480d110042540454481e075000041010b00349403110414000c900c00e0342c08100349011061410112803041d5803100e0140c0b8090500c1100f8a0b015007401503988840d00014074080ca0260040e58440d290200ea40258100c80390702803441c5000601d815014072070f5009003e024010f4034002c0c2d00540140124102c20f00307108 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 762175359 1250 762174109 762174121
    0x4080c0a050625020d0f020a0801022502031005010303050405041a18100e04050c090c031014040209090a060f05310b1008150102071a07020f130207021323 68
    0x681a080f03660f0040c244400644141c1440a001c140500d8181c0c0104140c1d10f00040e40d01d4140f0031100400c50b00d20540f5140e03400208516400c2d546000160381c5840b51143c998261511445054001c42c800d84a96a446181405010950382d0030001c090256500402011258450402d080640a0169401610399840030f10b52000c540c034507004010f01c80540f008100410000085caa81e680c2403c0f540502c0c90303916140d1000342c501c0101d50044420180e80800c00c0401400b0950076100e2030020000760400b07046130042080708608984564105403500d13020000ca1802c48000d8015000507150b440182100c21a0380310516990701740006800d20014102030a62080d910000b03c0c3c80d8002d0140f00d04e03044102c0002c00c0d01c00305695154002c4000d1064000e07940c0000380c1e060881d0b080d10480c050005214082650f80d03041060180d030001d40401c040449a503550456190a2a8072540107840e13000340d0050080c1c900380d030501010598a4004000b0034084440c440c000451903281110460350307140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 762176609 1250 762175359 762175417
    0x201062306041e030302010f0504022404091406040c020c060708030c0405061602130e07120510020f0d0b04060b030f0601111225170a02011104030804080c0a0506 71
    0x20f50104500c10082c0500d003464000e9252450200c0b4006d41c0240003103425051408202c40e429180254004048054000c000d08618041266020340d61129401d10f07035681055829100702c08000110140380b6000c2241c00d00d031a04c20b052044609d80700070000101064003003509440780540250207a6004400203100c8500740c002c50b009000003030700d05034940c150f000640e24003030103104049200344010750385a010925640300f5001e111154100800e2402c0c07519982030320407802600b00303803018090a170902044a910703000400c10080700c8400c05907034480c0310300d078881120f09843d18144280c0c2040c100b04519021002039980140c400b9201c0c5000e42c88250040c0c41c10001c1014500441c000c0b51814019075020b9006000002000020b03410800701c0c5d03405d044110b50050700010710102021408484244150000c0c012018035400005000f8041c0390075178203a90440d5204440d541c0000400b407040213070610040c0140e80c8183e442200d41c074104000161903005107807100c1041800e82410070024400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 762177859 1250 762176609 762176617
    0x210f0d06090218120706140d0c0504030203070603020901080103020103021b0d030605030706090308033d090b1c110402090d0501060807080d0c0f03111c020d0201062306 74
    0x10651042090503610650302010790449102020443c2040f201c1407500d08049400800301c0b5090760251580740e007040000c1d24181d2050382e15807420482071101308204001c904c6141c0c00e1744104c0e117600761107510710f00c1014039184490304460708050040c0243c02c207698010840506503542404e0158483c490711102400c01c264203004500c00b8030800d901e000a40303405611440c00c1e0388040d4103603503800e03880e0035060707882c80c0040c4002000d61600f00001960800142d00d0011320300b030000c06510040c030007254150740c0307480c100c80e00040300046800b0402c445089071041d03050035601030340c5400c0001c141c0c00040c0c8500b801b8903c0a0179425010203003d40654076581150355004000700b80d07000700b81c0c079401c250b40248213501510b0107900c036201d000b00b0b421a00003048001c0c0101d90380e60004c80200380da98080c4d582c088080403800d000e03040c0c82d4007110301c2d014085080c0800e40c0940301c10041a402c03c00a2608a001c96510156490084140490703110210800700191a00780703a10326401032100428001d2107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 762179109 1250 762177859 762177877
    0xb0403120f0911031204091526060703090b06010c0501020c0328020106030f12020309060a26011d060609040606020601140604260a05070f17210f 64
    0x86420064140d501103640503400b0240242c3c00d003000340050500707141d41c490b50340c417102d81c0d101c405010810001040360400c1400070b007050540740c1c4a50b91150705006a00804c40304500c0010440f9080070503070820011b965001c08149414442d401140c5c4482e20010805000941000346480840052060075011218101c13042c4c01102d6540ca0000c001d0000900003002e514103901c0300d4070003075406610500400c2c007030b0b0750003509502c45080d08d035503800243d6454200d0340003580001c3c4109005c81e0b954102812095516849103115414840c2c0b0a80d02d04880406070f0310f80340003590040c030517010310100ca00380c4050310b210400000d45400340021664041c5000107039120b414804080380280d4041070343d074104d800700d903809003401102c0b4040020034011406070506042d4000c4552800d80f0031416002413400000085ea6405422502c5090030b00c1c1541c0c0140403030702d40b499800c0040e61411084c1952942400018003510900815040b0380e001e030008000ca10b50b0000704070740d4407001c041421200006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 762180359 1250 762179109 762179111
    0xd03110f060c0703080c090328020d11030d021b10170c13090b030c010c020402090d081801030b0d11180a14070518090c0702090405010b030c0612040b040312 69
    0x8601220881c0b00355200c1e060440c0050b900501103500340c0c40900980310300100084c060000c041901c0746d00c50b0b440000030a4040c502958515113405a1a40c0c076459180c18025005940c4d150852024107142c2001d01c030007201103500c00b00c40580c5114405541445504003196071922070090b0740310803140c241e080c40302d041c841790105003030010b858807043c000c0009542d44c50a00040710b507100140c104441c83c40311102c0d0160040c0001080c258411b5541d100321b90b00c0100300509007441c07100400d440d500c0c418011207401c500007441c16042d0100458840d00414240f03028492221054049114804141c0e40180004000b5100c0b00c5142da900d801402180e4000d003203000d5524141700e0803805410b103581e00c1e140c500c22600104121600c24011503440301d86030411440012070513014010075140c000c0c1034070740c0342002344150001643c50f402c540e809240102d00200302d40e141842094281842c020030184207000030800d16205910203101d040c0d10640100a8071a2a51642800c3d502c840b03a01c540300c2c0c001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 762181609 1250 762180359 762180361
    0xe010e01050403030b010f1707091206090204050a020406051b1221010b21060102031e030906060a0807090525031b08010b0409020912060108060f0a0501050d03110f06 73
    0x905600c0984507034041e030340c1400300011103030043d10301e4504408407000160f040b08a41c0c4403260030a203c5900240c59250400200d50790b00e1401410107040d400455015840e0308401065103018040c03e50070909113a42149081d28042c40076040d88502d2313028124210000c1203041003090244060060002c0040c1a541e42d00c2908240c44890303041d400c4044a1144c181001080000850007681c0403007100300d0404064400301902ca0100601c000d0001e41148000c002100c8148200d001c00205a400500026120705040c0461820408010318003400b40c01c1444c4204280c40740024284220b07140d04000083c01e4580781c108002d40c8100d01d0101c900c024000d01c001d070074079078158059005000c544803e9040c0300c140210450340944284221450210184001e00c8031850b540d00819090400610300d04141401c0c800503400c0a900341e00c007001c25005041003003e01032210741c2c413a0748401820810045581404001031603402c1102000e02082110911030b441244100403603205504074404650407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 762182859 1250 762181609 762181631
    0x70f0606050603071e0203040b0904090c080f2a01170406150e07030b04050403080105010e0604030c0b09100905062a060f0711030c060103020906010c150203180a0201090501050306040e01 82
    0x5103201403003048100c0c1c5144021100302d1780c4080f00b0b5809868850b4100c5141180740350800002c0c0c0742040c4150340001d00c00d100060004402c0100c18203120f4888050031000001211079000d010320103600e16a071700c071400899101d507a03000144151940101880316a9a250b509010000703050889224444110700000440c0c0041c00c000364620548c0340b41c0e400c0c4000ca844406001c11b480303041d81d00802240804005000360343c040c0b00c3e0501d28510190241c1e050680e2502d0716000f0700015448000c602200282400460a00d40c1c0b44207070101150928607007040c030b0107011444c00e01c1003042c818140a46811480300804807400c0103409003c0203021155581413448a0852040c400e403015804111118a240e180d84408801d950100413440017504a907031864090000013000100014100501950103400003070401c058041d583e20b80480060320b078030300740710000d0128450099840082d0301c00214100142c1c0e1000c0444180d86081c83d01580720380b100004a8042e11031b038405040c19501f01600098 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 762184109 1250 762182859 762182867
    0x60706150801060326160803130b0a02120108030c03030c0a090302100206060a1a030613180c03150203010305030d0905010b132c0307030e0d021c031101050705070f060605060307 78
    0x2020070491700740010031207092411040b0b445010b030040c402c5044041c540c404031b5600b4011755484110440c03202d0701e55110b40c1e94041c00030702c1210540945540450f8040d03004c81c2842c861070140c000c80000f540303045a109440c1d580c0f4040203090841071480001c2c12101c852240c1e0900c00155800760072040390320f41d0709138041e448180031a8100d003d40c0100c58000f42511003210f8400c68029407400c020702d19260b4000b0300180724419003c0d014610344809440307010481d264030302c0f2403072409440340414290840c504202084441051324002500500043c00400c00220848820500342c04001645140501d86140901860700100d0391011601c1c0541c034410b80341d80c00403e201c00282907900d404000800d0210301c0f040031001c005120307074404c0c011b00001a010b44040c06804900504500114025900080c884a850601d07681607090440c0c201003003680165070362203003c0030107000f4041071030b020000074000e01900030042c04103a845221070703040c0805a48628054040075124a82d00d01d010a0b01070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 762185359 1250 762184109 762184133
    0xa180f0b0d03030e01052503020906161b050607111e12150a1a0607150203011203031b020d05091801090903110a0b0109090501182405060607061508010603 68
    0x41c031503500302000107030240310100c142181203414403e01101c00301d1f456000c030001d400c0320b25210342001d020060303900c210305000051040d484c40350707541d8442c004010083e0740c11030b0440c0d8040c90040c4400d04c02d840c0016003010506403245404d403003144250009031006107250031240388a50b0480e8106203801404140401d2840c0c0745180d10f070107201d29454019000045a1180800c844109500c580c404540d107042c3c03004181d4035024400000d004110440048104c1c2d200780cac4a44a100e406280748410141c160041c2e01d00b00104e000c504000d0507540301d020f51202583c1d00c2c201c040200000e0803250307607540c40d47c1c0803500c4006c2c0202c01c501766849580040080003520016404504901080c042c0c1c80d00000d4050b8102c5c2d0720a00a201503440c118004025243d140c3d0111859500c3c0c4190300d07002011024a00c1d0038502034007180491002012000001c0780d01c11400f02061800c00d001c0103a20b481d00800c89030010f510060000c1e0344401b608090407080c48a4120010b65401e201c0000240504600c0c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 762186609 1250 762185359 762185381
    0x70306090605031212090a1509020f010309120e041104090e070b030c0d1815050411031605100e03060103030c06110405031c031512110a180f0b0d0303 66
    0x1c1103516120b60070540d0383e2003906484c082c4480c00f0420061068006045580c100290804696250341c042c0d460003030710302e800e03400381d101155182154415403070090f02c000d254050a080411050419803039120348034040203250380511040703040601c191780b0360742e0091081418010205842369281c505010180415842007107051007042070108409049204a9005125080e100c501c2e003401040000060940014102065510341c4864008241c0520f6008040c0302203960000d02c9281600c1c10115040d500040d0500907031000201c01e0070001a1514181030b20001c58040c5000e010003002200c0d141208074a580c1c15010300d80000081507000754204400c1449002d0610910b1050709020226002d10300c900c1c0d9065000301c10f42030b03170b5420001b00568003183d5031802040640009400400350701c2c207540303c0c941d804200c4407945c0c18071003518641c0c0c0c1412403c440c155411450801070340e01e01c5140d410013403006a81c40904e07501d0b40003154407104070340d20080c0041c1180141407c001e402410040f40c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 762187859 1250 762186609 762186611
    0x40314040b03160e060307030c09030210030c0305090c0d0305070c031a0919171b060903091302210a0e07030f02120604020102030f0705070b030c13120206070602091807030609 77
    0x8801543c5000b5000c40744102409401c030360071691940e0040303014060800d420420300c04480004030150712214550a90113025413004609a001d0503001011203100034000301c034075041009042042e41c0c1d0358800701c4504e601841d0594513070100303040ca0462400755520042000840c96900035200000e118424032410010080da07034410540041c00d6602c800036032009001c41424607900404082e507801030082303d082c01c00341c2450080c407009003e02d0194195030510250344003040c0d08007a494410f0301c5040c1c46000000c00e600f0300c002e1804401c040b42c01403550036080c90084001030722442d15640040030901d41e030f10440c3d5071030341e80c3e04109050400c040e406034089d0392284405100e00b5400200b450080d641030b4020341c079068800c0e0a09415420409041b22140a4007000144107056000a98090342585504a95a0060030011044a0500da1184040103211550500507a881ca000d54400ca41c10000160742c520610000850590040040d07125503a254414000041e900d9442801079039440f00c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 762189109 1250 762187859 762187891
    0x20d021204050a0b070305220503100207170307050d0908090a0909050706050307090e0103320307150b0607060605033d1d01240305030a08040314040b03 67
    0x40c406454840c0b40105900064030030420003542d013410300200040303402407070210708040500007516100015000c102034194007100d002c1c89145403d101c5004810700f4404111714205ca29616030000015020a40ba5685404000600700310301034000c0320001042071004204481d030910300f041064200c40459130060150060205044206104074258203401c2030040269a02e82a812605d50740000d01540801c400390f00f00080031502c13003a40b2406140f28510745180700f02500c104800420456080004c26030255903201030314240441181d500726046184c02c400da4180081e8034001d4401e03c007985400690018021050010a0b4402420b8039000c8068418408525181894000e905040b040811a0702214140541d1038481900102c0008140128010000240840807000089608034140c1d4540001406002d203a114418601440d50348090f903c50071070326600c0c0e890148030324010a0005035404141494010500041440410b100c11941d480e201c944802030f40d002512070074645000c0078 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 762190359 1250 762189109 762189133
    0x5070516240e03090d03030e0f07150503040221071d1501081e0a1104180c0906080c0d0b03030a0e01111209100903060c0905011d031b01090b0a020d02 66
    0x800303100c0c0c0380b1074104011420040d81c50200040840d0210045040c19664424000e4114003400984600c044103005840c89078070f0810035801c5040b00300c16203003c0000400030000143e0f500e81e240c801121155070f1310099085050740e014680035540c0c0009648000101d050340300c0e0002c542e00f4600c0746100c0045502d45400c280010b40d03c441040c2c8540c0c0300d018070004003002c20600c1e010742d90740c0145511408100081c07117540c00100e90340150043d4501c0342403c044100300c1c5845018001860b001880c128048500d0044001c1c2809070140508030300d411300281c404c0f903850080e00324004040c0d00805490b901c41102d00302825030f41d6480c4005021403096805000460800702d0120300c6108400003241c5044001c40030440c4411071008948148101c5580c0840410510b1094480c0700f0a56142c0a0f299801d0900261400d11040060501c5913800481080c4d81c2c1c5000c644c01c0c41c24612a41c01c9014450000c00584140c50b5075007141040a00101d00c80302c1c0c00c0e60004201c0052000e030380a40301014a29 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 762191609 1250 762190359 762190361
    0xa0f0b090f070f06030b03100608070e13030507060218100905010f0824030a0804090212090d0e040f060512070f170705060304080d36020f040507051624 67
    0xb80c460012640340200d010440c090180d0030468580900030252800001c0d140d042d038045071500e07008130034031341c1c4121070520014a02d4034100b0f4002c80301c418014401c01442d54024154854550010046034002c0f42c490918070303d600035940903200c001c110076050802e00030020500e44a5100d410700180700714a02420060040001e01d01503032841c200b04103240503455010104c000b00c0050b035901841110320410124403690b0141026050705203000d60f44949050405101010241091086400c40002f956999803c0651a01400c50a4801190b50b04030800c56500170401d940c05203030012500400c441d80704401082490070350707405500c454001030f250001ca042e2032407840201d14441d40301d42c1c0103205a1415002541e03101d8850f4050038a0104000c0d044000d542c03480280741d82c0c2c40f419411034142012607510440d0b07054912011000c201c81a60002050b4140d003911b114021907440b8041200c6604c01c800b00c40001c40c0c5d59403804201c180520300f242d9010750408004074080a034900022560b001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 762192859 1250 762191609 762191623
    0xf120f1803080309150a0510060512040b060609040906020309011401050105031b091e01020c0301050714091309080703020d0c020a090209041515080c0f0301060f020a0f0b090f 77
    0x31403500030030340c282555520302c1e07590300c05000d0906521642c3d84c044141c0220305400d601c90b26510348041070f6820304041a00708080365030011401c1c48000d03c082003001c00030f410b4442d40250011480200780e110700300414030f103204440d5542d40050800d00c2070014403a154000f14008e4076460000c00260004c200c0c0c420440b1401c1c0621130001d0802c001280c0001e0b0841c501284041c14110401d2400b050940090303200c1c01d82c05580e4500410b50000808190303014400030041c51020b800a200519183d100109041550700480c2e954100108008809480e800d51156007070f0380560040210103034600740440140c2140380114014400c4485941c4030a100d88174400a0550190200003413a00385031220000c0d401821003a40c0150307440800c400f94688241203040100f28401d540c007905008154000c05205004241140f10341c010480003e02c2c0001c08212411a000e51411010544a1440407410183c80c00d002802c00c00c1c0140c010002e114400105500401c6010222400651100841c1d5205c1070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 762194109 1250 762192859 762192887
    0x309021207140607082b050f07030c11060a020703020705040f060e011203020c0103050403020a1211070501111e07091a010e0f0d2307030b07020d052d04030f120f 71
    0x3400d06c64602d041100c07800e10207214980c0800d034118a81c00f10522811900d0441c0c494071100d22000a108815415216110950070a85020301a006001c807005590341c401419610b007555000401c001850320a100755000342900400c180104c440d114952009061075000708180305050340c00001d4959604000d003a603256050f00a8500f8072050801507005181c014829829070085140e14030010310f40310b010051500e5251070f003c015104c0d111800d8030700582500702c103041c0100001e443e0203c050000d00c00c01a0105403080340340c3c0c4110102c503541401025071014070384c50f0410f102c14101a030741510080f003000007a80c1d80c0740780701c4150f42040b00811481001a400c40444040000841d45446040388801c0711200c04a0300c230705188103440d140c14190f80c010f6510884181c1070100305a4140110310b0404580d1811906198420903414404080402e0911007100c001c4985d010301c0e001c800c256070085410010084010081381400342080282018480001e000e600f0407182c5503001d8410484051 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 762195359 1250 762194109 762194123
    0x423060a050a090b180727050403031e0209090606040e04060f1b02030903070e0915070311040e04030201063f1b08150f160309021207140607 62
    0x144812800500a003000341c61403a4482c0c64180f00000324051800160090080308906140c1801d820f03c003600300180c6810035200c01c500c7c4202080304880b10903040c8041c80300c07034100156a07101c91071b06400626420440e100d01c44100c150300e40c500c82c03081d8003900000c401520b91844690715201005070314400ca014070402c01d0800c2c800300f004148280d00c00718a281e00018009400c1201074820a0400800d90b0b1034801a40006400d01c400d04083c0214001420000c5c400c0070b16003400a00c1684810f070060b0605ca4501240d8001000644242c10154581800000d155503654581400d03070207440c0700b11401c0d0701560819600149010012010680d0104070841907416000d204c2c520751401203401d090642d15101c221031050100d640052046079002072030040740a11440d041ca8642003a0500381c4040c0801c03a21401c110406143d40580c5610a000414a41e02c10030381c14001c0d00140750b410400394100ca00000103814507800025490251800310b0a074034403000c4a07000700301151240481c000c000d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 762196609 1250 762195359 762195361
    0x1b0304080d0e182d0f040f020f0a09200304051c0201110409020304030318020112020d0b09090708100c0509040c021f1508120a030902010512070e01030e03030714031f0806042306 78
    0x400d203011000c507c4913100078030034a54640c070311000401c42103681d0402d00e400c66035440441d41590700c0c014821070407001e400ca00c604614081e100c554442000000c42d600441409601820b664404c4d80700c421071514500009880da500d41013103030003d410880f400c4010900c1c0080c0303046034503410310500849075070507500c0c0d1818140f20300e0f0b0341c0041d420071141c16000da1f0710f81d80f820f0401d0b0b803209400c0744256070290041c04c0075441c3c03040562500e4030a013000d040740c1d440c042c2c054420170b034043c2c21180860410b84c0e002c621020841c0b4224941940e1007040011f5003841030b002c09805c80150404009407030717514001c0f03100c540c944200c0750b2207003540c01e15000008002c0000c0340c1024000d07009103510f540141006230038600203200300c03030460b00704030307040000a01444c0080d00d06607018811201c88551103402103040d0300e01160064040c5113440c544400304940800000c80c1002501c0e400c1982174031044a00101c0b40e40c4503805540da4400740d0b4115004600c1407001c18120041071001c0c085013039400c0c001c09103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 762197859 1250 762196609 762196613
    0x220e0a0f05101a04050604030f2108040206030612060f06010e0f030615031e0312010b2b0e0d020c0a050d15020c01110705031b0304080d0e182d0f04 65
    0x1000074010700d040c00b09800b4080017410741e5465000d0801140524603408070400c8900d0301622001065241c510085d032a564425811a03102040d598015415a0b0040d0340340c9500e4002880c840142d01000481d111f100100701c00c0d8030303516130b490b402141c00380c0790f00140040140800c41e004001c18071060301580a41c00003041504011003d2103241e0300074003903a80000c0c540ca4081060700768503029040c41d43c400079a40b5122154018103900411481e041c0b2400e042c4960b0308a00c41615001c0881e220b40e082c040f45041c0c3c034035a544859032101c0203034221103034207084a030048d40310200300b02d034140700c3c1c0311641d000225814409a1007580b03a80c007004c84000340120302e028134001d40015954008565030382114240400420004201c60340c0104004c2d602ea50301182048031122001c260301300c1d40d80090004000ca09000a0a035040103501d041451102c856480428408403e44000240c80300071681401540d9065210894001c2921204800010354000003268409403c0e9941503445c4004400100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 762199109 1250 762197859 762197879
    0x1052206150b0403140c0a0506130b0412030e0306060f011b0204020a0e03060a060506030a0902010c080703080f070503091b03010e0607020105090d02061b220e0a0f0510 74
    0x8116100d59800034a4a0301d5a100c20062007641d0803503803203034400003030600521010b800d550b02021400b10003002c181100c0f0003c141024814420540900d802260b842c00ba0320f015040c46010785103a0803810788583d922000000c110004c00c10a80105501041c07207400c3d4100803c5c0c161040340050011a1030341105001151404650690700032500c14542560f0010b03a250300050052038001e685001c1d408006c1001c150821300040c010208840c03804004018075241c8000b642d6224030700890000b491030756800161100000e04900030182d5400003011010150401c0c80c15000e1888088050322696a42c44180e40a01c0240d62560003a4044c94515040542c50b00c0301040c0001c018001050943d4004a003604d044826620803000d03035151400c00429210812042c040301c21f1780e1000b010396040072407040071248810a07070003800c102e001501c4c0c0741200790307000d40c41109c810401c1e24445090b5500761350a420441611040001c40c20f107000320804000a01441e40210600070f0391904240c54051420 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 762200359 1250 762199109 762199171
    0xf030606090412020312071701080f0d082a0a02060c07150f020d050f040201020d051c0209030a050a081c050f1f08010c0c1407060c030c0c0e01170d020105 68
    0x43c0461004020601c4085070402c0054001d60b40d40e1154034032200000070182c06040140c00840f00b50703200f1381c4140c034049400502c0c401d803481c07141001c0f069038030b034880001c6100500c0c000304030194400380300079440703201440c00070090102c86030f0079a485500d4074100101c0030f200e0f8000250a0400500301c180142210741e000320441074a4900043c58054050b034084150f51044444201210150080000f5940c0510124660203110314180c0d160400303003500c035520b102a60019200444d8040780200d4a82c03420060003500681080032286010810300c1e00b0402c552164524024500e41112158007148041c00341d10b005003240e90207202e6603901c3d09443c0740e000809080340414001c0e80e41000805100c01c0c824058100803a68501d25404018103082100301184445034080ba4003071001080650b501044151806074146080d200c40c2c0e80317034140b01000c600290032510000c50280300000c1d80041400c1d0941d00e2201101c15a56841c400e45001d90032220119104040c19101441d9001c07000450400c2c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 762201609 1250 762200359 762200393
    0x1006050d03090e13150e0f06060310090c030212072c07050d152904060816090816090c020c0f1306030605131e0f0b04081e090f0306060904 61
    0xb000800c500e58a4005d0158030000d00f01104981e039000100c001c96090060545110000300108040c0c1031400229655100d034500c403d0301c613641d80d1100c108000009200000640c1c0081c00101c00e070030034408140d121075140c03142d0343c0d0100c1003108010400481c9a9a0121900c0310000781c200344d96240016521039202310041d40c04c03d0b0350750128290365001445944082c0401c5245041c4401018040e40c0c45040200104443c0c054280030801c240342d440099583c2c0301e103280c464150786134000c03107003900c20720700030f0304040c030107002c0e160002d80091070401c040002c0b100020401c0c41003e80102040e6120a0102034043c0c000d0a56012540d95060081e048ca202d0050306200044150703494566104492040d95209c002160004284007840842c2c24035454044074840006140085590b40800505802c94002c000704500c034005410b0152800c265000400000000c2460050410031022280c0c403004101e0310583c5c07807002c14003041c00c0005000e48114006441a4032a07180c6451300070510102d00e201c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 762202859 1250 762201609 762201631
    0x209030a3935060105030d09030506040303020f0712020c0907030e15130611040311030d020a0201080c0d05040b060307090c051e04080d120c05090609011116081006050d03090e 77
    0x9031001c00702d98010602028003840003030290307941490100360400382c4507215a0200302c0c5180c014004140d01040858106a16003001a5191068102010b035030040d100058080080f41d6441c50216401103110308407424200c981d245076943d11002601110b41100782992242d214030714481c46a200306200341e400600107a84c0c8015500190350f084240d9504286d440150741010070108201b000c840c400d03003071018085000d003403101c0c0e901800030758606804e44080d0400141030040390040384260708031034400200da1414000c0d80f6103801e00c950002001d991860082c031800500040c0c0301498800e180224981e50384140c81e01c820b46100420203c84620b0441c1c03090303010000000c0d0902c042040900b0780b285a169404400b00074401c140850f11700000b9402070000170000020f40350348210458040102c00d00740420800c00401d405440c0c0781401d10640030441c1c2c0c1d2000403d1002d40003403a0410b0601c046000d110340c0340c88a050050700e010743d140040100b00d001000344030700b03019148190b42c81210404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 762204109 1250 762202859 762202919
    0x191a100503010914011d030f030408070b0112050606010201020c2113060f02010b0a05010c260f12090703051f0209041d101406040f0209030a39 63
    0x80c2c01c4601c1080100c4405820310030300c030540682805980001050701c0700f100034079080e1a456541300d103e40b04008100c1d00300040000c0810540e44241d601e03a40e041900d0700385668541c540d50804942c1d030f0b08245c6052041034005241503105000301c502d080c580c0c2c4040c00900ca0900e010030900900c1c402004040038040c03044002d604001054100244001da030352803800000030748064212480c1c405074038084c00e18030b001440740b81d0b049180000695400300d00b051901c031214002c0041d0541c0c07003074134091710780f000600080b6840a040190200c500802440822078807410141550355940b0b10000f450768001b20a50381450003000060310214810000143c83c0c010758900043c00c98020f10781c24101604001c48106464004112229a4001b01e103810000c03115a0b014808503850001c0001d4410740d00c03001000c08583c00f41d015a5161000901210f0849543e85007406001090030615002c22400d03401c1640c2d00100c110070030746481d2070413880c90200760801c0941555a020899941c100c0c10340c2c90 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 762205359 1250 762204109 762204119
    0xb04091515051c0924060b25060504050d120b15031f0608101401020a0809040b0402030a02070b071e030b12030c010518010c0509040b180406060305191a10 68
    0x40581140b081c490006140c8460400190074603000c00441003001c5c4500d01801801034041d100200c1d031001000403101214110225152002240c550b5001400301d41000e06000c06c1210000e2041c41401007502c3d40300034225006440b0045a2440d0110741e40b200101c0341d852a1501075000030741d00503221001d050b00c03d964580b0079544220b610b6000c8000545520100305011354038400f1100609070400340b11082164180000b0755071408084094140c5100081000d083c0d035550380940003004014000b5501c038030b01144001c000b500b01c0c12040d00c0701e070f08490008036018400c500109640400d00030806080502031b80490041c54035902e120381000c44c82100c0d00700c4030403c002410a000802002003a2458042d03045c0704000d080780040e15140c1e05000e904915107802c241074500311441035a0028a8815070000110440ca04410454140c9404410310003405080e0f00b00e6400d8070b0007181180c15944609107585c100c40b41c40140078140002c0384590070860f0130100c881c80e800446503001060919101c4e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 762206609 1250 762205359 762205361
    0xa0507080f0c01051e0f0c190201020711030303160509190905060a0f29040b0412050d020d080a0b0109090507030204030c12020d140a08040b04091515051c 68
    0x22014441e091800b04144140b04001d0250680c060201580c03584000010081c81e9070480d000b8281c4000410703c24002031118421000307490403101401c0c04550441040000a4000d511094040d00d2480383c6000c1c0d00d206060010849008401c1040c07180c0000c0b9201c0021111504100390703540d0b00180e0b42204e5503110000c1c080300d20141804010014550614070308112108055038440e50610358022410440d902c91142d0184071842c280703041070b162860a481181d0a80706681026588440c00b140225404846400f41c00c1001c0c403030310880341c95110744007060344c0c0c42c0803860744500003c0004001030a0303c0700ca608038498408041c14441c10f020b40310b4005c0801c1e181c040b9500800680d01003801c00500c515072856070010f102d00e00c2c00c01e91408003900403a1400480b40350180c0b16908441003240c007030a041001100150300043c14984440c2c13224a090015400351190750212420702e06485140e1070241d0184040390b04c104a06000c1203815241504d10fa00f0403242c8032102c0c607940c600c05006510b2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 762207859 1250 762206609 762206617
    0xc121106071109091b01050c0319020a030f03020f0d0207060e06040b060a0b07081210030b040602120c0c0703120210140a060617011208070f060515030c060f0a050708 73
    0x11410030205400410002c0c80b404a1008100c1c0081d948803016207007104580e07041c2c88a0244080ca0a25600c2001c1c850107441c0d403054880c0c80e10792090b0ac50002c031507903a010036801082446642c4103403079100d104800714103074050343c0b00940c5412020002c0b117140081c03903030007008898414103000c00c5004001000e18203068003160182e034562429420807002e4901302d440c0901520140d201c45050461503100d4024038095201e00c040d0680840c0c021030078801d506440350004650060010300b4900d81444c05001a4008920040c40c0303541100200b07289031004825208802010401811014034546400307416030105c0140358203500070811303402c81c4884c050185506091200c03510600782c1c200fa0a8a00444556134040c004011086140200c00011520003031304644106900102050280c1040b80141c441d610000b01b5417680d05d4149000c03c4500c3d04140c1c0300f001e1030301011101e0700648017030540b142c0d540c0b81a1a842181000a0842c844600b0042c181420340780c50f001781480c4060341c0e03882e02588 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 762209109 1250 762207859 762207863
    0x3060a0320040f06030c1221020d08220b0a020c0322090b06030a020304170a020a060b12031c060503030403051b1f0c0312240b04030c12110607 63
    0xa0890310001c14142401a2042902002030401506245480b181c0c8100081d008481a421159028801703002440045640030104c034001c0241c0d1604003440a552885100d0303c01d004a8503070800203050030414008020701204000752400d184400faa280307c000388000b80740c120103903824081c691aa5034104040c1030856a6032030316240020840321801074024095000201e4241080c20604281d1185000e503604840054030140e22a281c92400d0030303d41e4210500d19143c00304c0401c224610a030f00081c04c503103850040074101708604890041c44450042981e900340158802c0018020521900d04403009600d801f00c4001002c41e100c00000e411070740300e03900642d0a98490020916200d0705000c8502c0003200484001000080744c80c0e402900b010b040c030100b0184206540710301c0c18140a5580041134102c008002c00c80103140300071050f0030301780025424242d044610340100710b400e0028122001d59400c1242e0285080c5015040000002001c50031203c0c2d4014030b1507609145c8850015040f00c0d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 762210359 1250 762209109 762209153
    0x40227090705040e1b01050a02011803091401110d0e190f080d020102090f01030519050103080408010e0a050c12030d05090706110d0f03050a09020603040c050f0d030f0503060a03 78
    0x6031500e01000b054607820454500c4d290882d81c8901607000c1440302100c0704010a003000768030f80e100381d001680104100080c00b40c0446404160740d041581c0441d1307032002d903030315003090917420400217004541d0038100108002650303101c02d12000900c0d0080d60803084181d00107100e201e0041504622034641c00f20359101c0049542205014001c4076014444602100300901c003c5050101e41d07400034464482c0c03030001905152365040455084000d604464840303900c04013082c062542c4d03c2c40c240b180e6611a20411600e5403074074981e018080800b0030924000c4c1d03000320040c0b08408400041050903080715468050702c1c031080000782200130141c01900d1140748281c016141d0307903140c01c1000d001164011291512504000c051440064003c00c4002907a89540b0b400503044d03684079546c80081820b07000282d132124000c41044100451448043c05440c003d540d00c048042d5440c003881441032220a000300451840c410708400e00344510f02a40d4004001041002030668940b07841e03d00c80004407084c600c0d8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 762211609 1250 762210359 762210373
    0x91a0714030318120406030c0314070c0203190f06020d06030f030509090f07051207031d1011030f01031401141518010f05060f0c010203090703060b031504022709 71
    0x400d1035800424201c43d0000301030107104144000070700a03885140030303d0f028103551741180c1c01c0103442a48241d140881403c03d14800f400e108a02410708807104108a110f88645211a041c3d100c2c5581c58650309a4032422a0038188919aa0580a034021041102015941303440c0000800c19401c0d0282d00c25020b0b84a540d40c2d6900d4a00344a01d4410081c40e070b603691101c00702806006a03003e030840d104100c102138280f44030307228070030100c0c007030000b4901100940410403d0411545008950416100301c01c01c402c201c448007881c01c00990740400c9a0007000c41e865400100085000200441105d1186c180001001145680c140c12982c5065405001c81c650031070b108003003810880c2710b4100403d50002c414030250724141c0440d48101c81806114020000030603a0441c0c43d41c01c1d000d480040c0305280003551a49007001445550b50303040c0c40300f903c20700e042c00002c1c00203007004520710944207180900100513645903000d12100744908811a10320449400442c00440e142c40c110314010750525001c1c1601d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 762212859 1250 762211609 762211621
    0x906060f0f09021e070203011401060f0207080105060d0b1024020c03060907090908040503100c1d1516060501030305030618150d050f12070201091203091a07140303 72
    0x1500d95401102d000351042050300f990080c00001c400c45142580400c540d40c22051000c6400b51820061100c4420140700c00422140d4011400c02030713aa51030741c2161403195407101060300303a0f00d040d5005038200d0301c0f203654800070540f02e00d090350340000c504202c0c8100c0756a6054511050420440840700f0442c0e1a500c3e4480640c1449002d103140e604500a00c1541440d0301460303100c04607441081ca500d43e440190008020300c40e02554001c0000078180d0340700715000a01e40015001d03c07034102001500b1820011200d40c00c480f01d805517500060449039048140300691042540300220344440c203800051010000341071809140d0203984a071b60740640b03030700300642030083c0b5814450301400320301c020308108201d0070f000440301005114121000000117a513402c2283c24202e900d944082a0302032120800390003110380c0e000b8610a4402c0c3c0c0e95511a95807100c0d0b2800055840318020001445100100a41c001a4030301c54524128492150320b80302d0343ea0740c2c540c4c41601080d2000d02e203400100801030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 762214109 1250 762212859 762212879
    0x80106090b0d1a0702120c070306050c070803070e0409050f0706020105010501050c060f15090106030c0e09071d040605100e210a030f03020d0504030503090d030606140d0906060f 78
    0x1c0400401c0d109101c09100980c0c6640c031024404404102e1420850001003a07144200511013000358590f50b1160303110402c007140342e00e4501d070b4001903400da410070b000f04450081c014110340d003c0e50420078032130840d00c401004a0746c4550308030071154003a07101c0c50b4400204005012900f5000403042c014585541382c0040a42582c0c0c050f13208a060240c28012161243c0022407010ba001000c00750a81d00d9569051650204100c1400da41741c21124520001c035016415610a0f20b0b0302e00607031036070418082085c00f006007103401200c4550002e43d001001c4c5c246024100c620842214000340013141c4640c0710380c0400c04040600c130088001940950038813000342001700f0724000311020303041e91070000c800c5500bc0700e69441070301d43c0080800050703445090425200e0760681d8084100340c501030005041a090042c0365030800c0d03d07a801d543c010b40540d0000180a8482c0c0000c4a1103500c0d11030400c4241d106142582d080354603000c01042c0c84801d290005865072281754058941d90008503c403030b0400b13030490 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 762215359 1250 762214109 762214121
    0x130f0b091f06030501050d021c06020c070303080f0403090e0405100e10050c041202190302060f0903160f0b0d060b12090f0c180604090c03030305150108010312052208010609 76
    0x600f818036140040c4038030703220a480004c9454040d503403600c0c4528401801d4405914100014194910200e00400290804503819045134000e5440300003075110400f004907502420760300100803400c81002000941c90110750240d0141c0180c0940314050a000008820381c0c80400c0420407640165168800c401528071a00b83c00400040d82d040c1400c0c11300c0346c010350b0b03640d048601a1051042100c221881d51003045001c000d140c0c0907100300d46401d40e1030b00302601500540da004d0b109005014000e1003120341c020342030b01160390354522816554600400201c00d5801202074103543c0d900e500010541c00303400c0c001003541c01e5080349101c0d0f1500e85440b080f41844c400080351911504040d212480b60f66072505120302d100c03103d801c514410380713410300081d00500c3d01040040103580b0945e000130901d42c00d0341c0582c0c814404500c9c000c000d01000001160b40364001d000c01486010040e601c0e4803050710500c050540e00110701003084102c3d140c68070040d0f800840368800d0040ba0346458091010042d54081c1c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 762216609 1250 762215359 762215369
    0x90a0512012c07122604090c0206060405012403021e04030b010e180d08070306170105040605010801020901090905181525080a1a0a03030e030607020606130f0b091f 72
    0x104003132000035628010004c2d40c080b10030782040030020260b6810b45021080394000c1c10301c0f5500b000247c000100103900c0c0c10080350405c7c800c62800c400003500c0c1c0081222080c0d8903141d8411070580380000d801c00c3e0001d400c00c00f00000302800c0b9941d2a403c0508040040028501031109404507624020001090200040c100019550303d580e0402907200000784150380e00d905420800b070a5514030004400420143d0700840c44207a005000d544400410740c85107010710700410040c031403680c0b00d800e80d50a0307108108819002440c904410003100c0b80c0c550081d9004109003072071582c0e44510b900403a1400e12050318403840124940c051000454107003414081e960564095200da82c1c0000a01515a12004103040d8034641c490504040300c01c15003401d03d03000c100040c9010f19160b200e0500414000074104120300034415140401c030310600009141c0e10840000f4a020708039075a00c03003464041d11448154691068940181c3c803a282c3e0b840040034491041042c800391040b2001c400100b0101c0c05a020b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 762217859 1250 762216609 762216629
    0x5280608010b0f212d01061e0b0702040b0607080c0f07120f06061806180603121808120d0f0903050f0c0c040c0e0312090a0512012c07 59
    0x42c501d89511940b640e0340702c81c05401c50091010744d40c503405504102c050106501001c5102c4c03410000c108844e010307202c04510782e00003000910303125100b200d104110085501301c20307501c0b1a41002030000d200020a681da1001e0000300d0308200b0600400d01d25000140c08980305d820208103c0303480c0303c00b001b201c0c28504103600200003041c6018915582c050101c400a02891140c001a000744049504140d00500d01c00f101c45015144400c0c00200802543c000c1c030b01250144844407a004c42e4078000c100650707800c05982c4d00304440d040700640b0080158010583c800580f903c00040c0d4040500143c2c030f0519038014210307915088014100201e601c80205000818908203910001c02d9100c8184c84800708590310150791840e410007803901e85140042c50356032040c02c016018400a41c0705182c0510524154116100ca610903001c03d180c074041c089810303800280d022801c01031071038100d48030000c1c1110310f8000203441c480b08007000300c0e000140c80065540340c00640d41c1c1403a020200900303070091110f900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 762219109 1250 762217859 762217879
    0x10f0306050d110f0a081b01020f0715090312020d0e0301021204151d072c04020f0a180b030708030406050315031603061509020313020405280608010b 66
    0x40001e8420406090181440c9014803c0d501c543d1905010041c6020740101400f490540c1c2d007124640e11880c600d40c3c00301420503030303068081550000503015550070381d00004c0c04003a801d0107501034460020032520003c00c100c9034000004035986502a15096840e68081d160468082d0400f03015025141440c50082c5e01c10440424104004684d094001d980220100e0905110304a4040580580013040600c0340304051101008070001401c0400c80b110311600c442ca0034040008842422002200d00703140140e524009030042c039020003442d00d21440204a546503684400f0913240d40203007410762503c0ea42e036602d00c150003071070100050002005068000c0d4509807c02000400f2400094a2000c8000d0840306401c1255014000218561808801d0403111603032410840007500446003800d0502c10003100c08101d0082c54004c071f0380716105803030b000c500324540c580c2807000400000f4100c0c2400144000002d15400601c1c000e030488a210040100380076060800d0142180c2000180e5032003401011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 762220359 1250 762219109 762219119
    0x140a021801260d0e040609020c010207050f0c03070b1e0307050d1103070903060906090b0f250e0d15050c090424031e05060f0115020a020a270e0a02010f0306 69
    0xa0403da212599143c00c03e503c101d501c0115001c1c020300c0c0c102d120b1141c0003064805180e041580a082c02600500032a16800181445151583c15003000c0c40c3e0141c120b002c0510000c00400010700354003240b4500d800051404c243e0300314181d002501d4160021b400016842040c00311400380c03035140b00010240f1b074618106108090040c2c40c0511004001c55181d0b0080c6081c090313242c0c0700340455504000000007a161581001e4100078044586500c2001c030010300d081c8000016005040c00032480d142c04121910000800001400c1580e0132154500c40309001014400140105401822041081e40c1ca03001c1000400c4165069007070150588200202c221403514101841e002c101c9400c06803a102102404510040b2100203001c0904640308030b00511241002170701780d0604031000210707414801381e400d0f07a04a85441802e10003940c0700a12001c04e000110700034000c80c0c900007004074198030300e071480e103040c0042e1060a1000b80c4250084d100d0305040d544c0041321011420350615007040440d0402c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 762221609 1250 762220359 762220363
    0x703030c08090f07121110030b0111060c040e04051e0f15060306010302280e180c090c0c0f070e07090b040303170402011b140d020c010804140a02180126 67
    0x207120300030120a60280c00e0042c000c002a1b280203025006c0d0680c100060b003640064060000030310f1180c0007400131039400481810114803180031b600e06c003801e03500d42864800350070411000078106a03000c0c00380305444d42c0b492401c248004001650580039141c40980d904030746051a40310f5034106075000c04d5004020459a01140190640380d0413102c04240010140e06400c00010102d506d5070510416000807540e1225250380307030f204055202030005416044028181c8502042e44450341040c04140441c081100c0d034000740c219414084103c50503a95035080c06071901c012544004006800101071001d01030f030003090708003e02488840d0364985865075078003d040a0b044810f4001c2260b4100c0824110781c414240c9801801c4840740c400702e40902400c00d0b8030403410743d20150351640700340c1401000040c00483c0085008405840344003182e615501c5001c0400340d566003a204601540c900e13040103984100350305860a0fa040252000d40d810002004c1c1c46003070395000c1041641119012074520200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 762222859 1250 762221609 762221623
    0x2030c06011203030e030406050403110117060d29241c03141908010603061409060402070204020a0909200f161202010c080a0b03060f070c05030703030c08090f 70
    0x482c4042010b245080d0070110010220749000c2003890000080010b0300d0b44c0c1c00b4014005a034040d14004410426039001034580d010302c0580710140c2100795000940910f011904c003010240255503c41c1550501501001c00680c4241c2417400b00440c10b00b800b8980310383d0034500c0c1c40c042000b41184866140403000400d80c0c02c03e03036006420f21024241c040201480361901c50f561440c00300da240e468200032040303603422103084004000011090400020014840d0280030101c402b844848a4071003045024401c8100004100c030703812036001c008810068645100400118280c1d82c0d501900c03a043c083d034030041e62105541101c1e4440c206104c15000703407010b0202d0f000c40742c040031903507520314090344105050344a1190240402d4600b04401c0c14542c1c042d000004024903a50701c81c1c5107990740d08042c00803100c02e40309a0f5016404070b0002144824030101060700b100c4e00b4107001115216581d15070b4039660001c40103c0010f0b44410f14040c20980100d0202e410a1403000500480300c0c0c901429951403070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 762224109 1250 762222859 762222869
    0x1814160503010b0f1228111b0304080601030c23090f041a04050f160b0403020405070207032108070804020306040b18121b0a0c0306111b06011502030c0601 68
    0x1030f0000b84002c07100c0307012040310b4401c209000e0b1500949400ca801d2111a0400f02018500f044a0b518600040d00548140010580700080c481c1c20154115540d000c400841d650100c06417204003c0400d044904010082c021441a0440c107191820721203410740e0702c0328880c42c80c0e907001014902040d83d5580c500c103250b8804070540a183c159595402c3c4070407804020841d01800c1c0d0a41010f102c1808000b0600e4907005812a04032420718217280d481003c0e44a42d88982c07558120705220610041c60a5000640c00c050a841212052a07c03603c8902e035200c41ca102020030411012481c40300c5a4004900306c0d4007204600f00204e4501d0581c000c81e03190503005000410001c60070001480381d480202065805210340c03021030b40c4400c0f5000608040b9849001c01404244299040c1c111078003000507003103921941310101c061a64a5a50344c2406011104e10002d40e20700140803440f41141342c24090362000d840d902c01020b4951425030048d03415510f0461328011500b0412403070403110030005950381122 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 762225359 1250 762224109 762224129
    0x290301061803021c062012091501060908010b01050906180a1203020f06151503131205120a02031b07020f03030c0f0c0a140d0c181416050301 62
    0x1181d4241190303081c541ca800081d44241e048820580301007800403003040207482820104138040400780e81400b1136600140e9002a240c04004144040c070703407041240c0d0064081802c6854480206000c548000300076000300c400a0f440040400181900b4000c5c482c1240081c00c1241c500102076000c030740203100340100c0d081215450a00c04296480d042c01c0f0b00001c118213455424844c40c2c6240080d1562000054000240710710800304240207110110701080b417500604040c9800d03c12034a5642c180c100a00c07040002400b80117a202151102d00c003c280004075075501591131030380c94180b45140c2c4000d0442400d0f98810b1080009040000d003001251000c0d668600d5118001880000c186038035220040d50940004112003000d6100040c21429034030150080d00c0121300398106000c0d0103505841402c4a854200c0c1c10000d15051400340b052a0f18082c22242748200c0e00c4503da440e074100c01a070512600c0703503148040000d000c008100d07181c11802551120359004501324005100d8001806040058 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 762226609 1250 762225359 762225377
    0xc030403031a0a23030304090f06080f0c09040303090b0c03011707141513080313060507030e211c030b04020403020a06180e0412110a020d140a0b01090629030106 71
    0x940400c41c15007552007000b401c481d40c0380d4231100703031a01600c0c0712980c2262142c2070180205c2e000c44040350000c0c280300010000d0808880000420019150150064040c1a51048a4004102119442c0344030780c09107a056582c03545003041c4400c1000d07030700c89840e0444c1c00c010400c1c400340b0410011325000503070466030300d01d54006142c0000040d1240440940040c1d410300e82c0010780480120203485404d24012407a40a80da0702c1c8026940e81c800c000c401800a58520702800c00c40c82c0c06140300316180b802c80d001070403041c0c014039030303500c2c1c442c0c811007030f040800f02c181d6401d0401d50300d405480304050741034170154201460350780801c8580a40e40681014040800c09100c01c001e40210100002c1003016083c1d411410f06050980d920100d40a19100044552040c5c50700347c1d00c00220302c1c2c8140d501410088201001e0340301c02c0101c000e100c0c1a54044d0142d40702c02004a925013600502800c0800000a0b40c1890800c2004075003003c00c0414086140c1d50f81c00003002d00150040e241160700d982041100c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 762227859 1250 762226609 762226649
    0x20a120825020304170c0f01090e010909082106241206040908040b0703020d031b0c1104021b0c0a0303020706030908070c0e060901290c010b090c030403031a0a 70
    0x540c041ea0b0043d83c000c4c0c0c1750000d0883c1201c000229102440d9098400100050300c030001159031008a0044001003482c1d6001001050410f40c040341c4118081c0d41d02c58140f003599401c840301c0c004e20500c11882c1c0c2e0409410b0000714505802184480140d403001d003001c80c140761038044524001e07810008161001100020881c0d252030700508041a400303008241d0f11900c0300d981010761b401489003680184152080e000302940207104032a442c50714038040b0000207161070400c4502e10341c0e00104641036419007504070700a45550000d4109408480c030000c501100d1144071714903024581c903801703104561003101000486d4000c0b0b00841558007900e0041004070301410301d200c4e42d10411000600740d440800c000504460050b0349607010300d07011500c00000e80d0f41c1e007c2c1c8080040c0700c16078221402c00d07c100340d6030000c611074005212290ba418008104001e5000c001003540e04200c5070211000c500004200030158036102e58540310803e207101001240c50200854180403c41c01001c440108ca00c0704020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 762229109 1250 762227859 762227863
    0x103021c0b18280209181f081b0405151e03030304030906110705013005040f02091e070f02100e0d0207050301090809041104080d020a12082502 63
    0x8185801e01e41043e040418540c204101072000000600700300e80c04111900303009000b100e003040001488a2241400072407a50b400010251421000304031850245c0e10408000c402c200060415001407d0302e800062802c85604a01c004030503c02e80c900b070200a41c81c1080f10018620000546003560304030b80c82c800c7c01404456001006034140b00100401c01015440108001641d44503500e0f0b0b071101e5401015036544480c14001e150100b000c4180d2410340b03003407491201d000345030580c603041981c03410b0040d40411558291001e0340d601d190f0f0f03075441040d0308000c08010340085a9060441c04288070700441c200c0321310301400b6141041000840d89203154401c12202c0320107800d24500b0400d10304003400f0582e131040030b95603890140c05488800261481e061107200b0720160080c0025241221a10400c80200059907801a20b55424040403840080800c4070f8065580700f43c00811400540707041c038110b107401904036081080010010080401014211200b21000100300c583e004c1ca040501a8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 762230215 1106 762229109 762229129
    0x506040c0f17070e0a0f050a051504151403360c0405131703010608100510030b030f15250207140103092405060103021c0b 54
    0xc03100d03421005107243e1000d0340746060384c1068042c00010710300004a801180c10303285281c3e030900403400d01c1580b14002c0c0070f04aa007441c0214405503505501e01c524010a88260509545034120714011041c800081d5400e408450300d078905020a00740100640b807662842080c446900303012107030320030006292402c18002906090389a141844007a11002d40202408100d1420007400f0448804071480c80b922114401a0741c2c5d49031080c01040c02d0b20261840071003290b6403904201996490709800b41c008c9041c14041180c1121800090808020301f810740d409010307294000c011a0000320125104992516920030f40e190000d00c000c07180e0101da10204007503031049000340b2040702d40f420f038884003600514000c210200c2d80d0390760010600820401c0c0d00c40060070808070036072107040c0c010b8690111003840c003113003095070b4400d561080110012009901c180d0b940350b407a2031611140058 = true := by decide +kernel

theorem cover : BRFrame.Cov 762050359 762230215 := by
  have h0 := BRFrame.cov_init 762050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 762050359 ≤ n) (h2 : n < 762230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
