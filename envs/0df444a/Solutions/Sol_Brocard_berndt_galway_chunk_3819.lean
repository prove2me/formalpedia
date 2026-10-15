-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3819
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:46:16.661419+00:00
-- url     : https://prove2.me/submissions/83b49d2f-201f-4f0b-8105-88e2acf4770d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 686690647 ≤ n < 686870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 686691897 1250 686690647 686690671
    0xe13021207080d0e04090b041707021003020307020609070e0c0711040606020708121c020322140d020f0a060216050d0507030f1805010302090303280f110d0503 70
    0x120002100344500402012014000c2083ca003a000010300004101c144c80361040307141041c0781d004039441c04031542d4002c0e448500e03092150060948204a40116a00039401c08800301c203000350030350541d00035405581c5076000c644656030703001d521640d41e0354540214124849044046801c9030b90b2800034003a40c46c411407003040c2d01404000441c003111a144c1c800001a44040d00c10004420140030b51071001c05880703401e900c0d020000c08000c52403040e80900f900740560000000f00c641c0c102e280d550000039036140c4030340b42d00012030821800ea8410341e4420ba00500510750303031070f00250001424040b0b001d0008040c115a104a0f19120000d4006405507050340c21501d5212000a00034404401d00700000d446144c0c07203200318100204580362115503035007440910001550100d41c000c02e100100c403000d280141c3d5908044010030b0540c010541581c1755103a0300000c645146800f25010303160f0710b500359202c550065500b1011a200d240e00398840d101600440c0c45800c49611441c001d50b030000144007a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 686693147 1250 686691897 686691919
    0x31e0c1002030103021f0e060901170408040312090806010b0f161a010609050904080315120d0219050c040519020c01090210051306081509090c0f0a150507062a080c040e1302 76
    0x207503245000b04633001c44503140c0000c0c0501c1044500b90011001c02c80c14507258481300d08140c4c803540d4409043c090600f8045c0c000c100c00d0700420310b07601141c8981d103802640c2c91582c0e215282c0070b00c05204415056081c3c800190010403042d00c25181c3d9000c56030300501004641d101c0d070322118500e50000d0450316400109507c1c248280d22000440c04c10850f25200a00424002c00402418100d10b00399400707006511000c0d110114070006420004280d080702c00060540794030f032040f03425021220100c900f181c0041001e01c4481e0701036216951150084d00d0000d078410416400311494482c54140c045a895602800e12480c1e1040c0c1c60250701c0341080030300203400403a0f42d000031100f070022600c0324907640c4080c07400c160505009a06d0b142d904025101d01032030394208480b00130300d85106180901006400714842e01840004c1d0000e03000d80140c1002d80c1403e0780c000044c0fe5104520481e8103010541d030001041007070741c0d41001c540c211403490700d01c4d81083e1074079a10420360701d00a070300690f80b0100c8510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 686694397 1250 686693147 686693177
    0x20604090c050705070806070e09071e020c281707181a0d1203111e04030201021603020f0d0827030d11031e0c1002030103021f0e060901 60
    0xc20307185040c540b03454050300c895075890403e26114103904280400d410030340500446640000e40e80c3d9002808403100f0049071f40300b5000b1141c0c0c481000000070b414143c0403065a8a9802041c0456800c40503501d00c00100b03041d402d0640d007452100b180e0350007a0f8091804000080c3c0003000803101c00e111009032400c00307a13214143c02007000c001e0300510055944048070700c11202042c951403064503080c0c9016000c158a5100c42030100303144d4018006040d2a03c1e00c010350101d01318200c0700d00d12840400e0707207000452000100740a801c40d000403405032040d001e0366480b03010001a0001180c0c2c0c0208280c070310288113014003424501c2d2100884505c0b405012841122111182108010f110098001c155041c00010540f420700310803050f02c184126200d901c0c6101d400842192401141c507041120044c5010202d1a094865a201000c4030300034140c4166a54034030385c000318100c90080f1007000d1100090040c4201d625042815403000c01c1c0fa0550b0403a007401d200f0090091040141002060200460 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 686695647 1250 686694397 686694401
    0x6030a060b03071e0e071b120e0a170c0307030809010e0a05040509100f0e07030605070215070306090506180a110c030c0106090c0e010f121b0f03060504020a021902060409 75
    0x6408000030844d407410701000d0084100d480e400308007454a140c8800a81c0300c071802c0c6510340b103005001a850003031881820381c0101c5011003510406031181c094180e80c0c0d283c03060000c820491200c2207000340d0145103000c1c40e00003440405c2e02e411100040ca0184d4880c01513031110f1500c1d0890380c0200c0403000c0018166102d200e03143c810403010010303006140c0175031551000c03210b0600041c81c0e681d24101004001290025040303055a81c04100011143c8860b00103074542215010140301720081c81080203441c07a81501b140045408407401805140c0740c0301d041161204850081c6d199900543e030018820a000b60400c5806c1142c4446503441d02c00051205421a4040c60200c0000e80d110b8800b000501c9941c0305d10b80411186140210720030240707200090456408030304041c10030465801d00d5045040c103034485003001208584207a003003241d0b9800604a6100174400c000480e143c60030002c1d203070030f050007110b18080d0181e0240c040348085004440203030303450a0342070744c000405200114601400b4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 686696897 1250 686695647 686695679
    0x4082a07050a0f0902130f060c050708010507050f07020a0506031f0b04300503041e0e040b040209090c090f041e05060c2208060105190b03010b0c0c030106140a0e06030a060b0307 78
    0x2649e40d420240140d041440c034240309a48110a20fa140004008540b0b41c4603054a005146000340c090741c4043c2800047c0c480381361a000f585d4030481c00024403042d5002e050707508a42d480742c10750030002255241421500b5029a124451408501141c0d40c034100200d0017810701100b1032129081c0400c0328640303c0d540740d90003540106c1e041220300c40800620035a94200c1d1801041040c2c503505441c038146d83d4168070040060b0000b4022031914ec08109102d000b4841c44801c1100500404040d143c8496011145c00040d6000e4549064240c008a401100c184406003940c0d0004020022501e80443c2d11900d80c0c070a20480c01c5104000444110200c03005110b0341c01441d00310010042541071408004006c0d201064000085003000c804116900e021070a0301d044429900f80303241c03150f801e98100e074182003e0040c003913415440c020010441c0c095450800c4c00c181c20948407003403540d403904248088140d0a40351182c1c5a8070150500d030004107a60407504c2e4020303000d41070303c42c40d0b59960040d031980010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 686698147 1250 686696897 686696909
    0x4050a1a010602012403020402030618041115270d0c03080301060201051e04032a03080f0916120c180b1009060e0904082a07050a0f0902130f 62
    0x1004004006180d4240541704203a07003d030300380441c801002083c41c910300819120003400b990f0048001016a0307940161083c520264506809461816291110101c414144214402c0402c5081148090700031010b48801001140424000d254255421500103048840e51030340040000d05c00400590100d80104c0114403403500b581e01e0354100f01029085d544004d0260082911001201059400c04001c0c0e6030001d8040c100325044136081e0540030026440c07584100300100402c50720004156100005920584540030000e40d03c0c0c4401000f191141c0c88600030700800c01030103209000703d01005126001440c0f080d004810b000d565610500314440100240046440e504c5001040310306140c3c3c502c101e0809a072030031449403070510001400414141c0c00c028082c0c0500130000e403c01198604807001400420514039600d510700c09828110004203441c88014001c0000020b03442c217180105800b5680b890142c0f201d16810310b000040250021140990f02d024503900001e2415410f410764005084 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 686699397 1250 686698147 686698193
    0x5070801020a0206061e101103130e04020108180d030218031917030106080a0b030c19090617070302010c030207031704081e10020a020106030c0f05100f020c040504050a 74
    0x7404038100300403c10b25003131040308040c54802c01082031f5206107a111519081d030030500c00c060f00d5000c9075841c0d40208101d040f0040c00020300070070b0070762132410464440d5100742e851404a0703580000540404013000c0c0035220952007490000285130284c0c01501803d84590940102c541032800082d00c1d00c402c000b45e07614803a01040c154800e0118008920301d11101d000c90b9980b80d94548480105040c100400c00e005640d5a100450700f01e46e8280f0079608040300081481e04a4140d600800382c50075405c3c03081c001043c0c940b450000d160038000c0c0d131070310b40070b80444094001c05207180c00541c2d01200c484811821801003902c040000740043e000100d9001a1050071519075080c42030151400709020300e00b0b88042c20000d4002140c110000d000b103610b103094070015881c1c101a04099003d00070079007000704800c081030800f2400c01e141d14090011150100e07000810009500340a03254240c00384481c00c01070700f0090010075541001c2c2c201e250020310038000c490f580e0360326843c0c80310a44218065200a00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 686700647 1250 686699397 686699401
    0x50904090f2301110d111204030302090a1403060f0720150c07020a05011b23010c090308070803060d0209130b060411091e06040305010204080d030c1b05070801020a0206 74
    0x460000b01c0c120b150009000700080c220504d0400d415000f4400c0c0c9460054540030030741c8800d02d40c1410b07542e2507080075065984506181c54054083e402c06001c0707074040c0c01445000200000800080c80340c0910180240840380c403224040d01e42501d0050211007809003584101012544640f405c88038030392607201800f588400d10840b69650390010b0840781d0900818400c44001d641c2d841d101008480302401d0160030507007200e01d41c004500780300001030031070b9030392011280400c1404401072407040d15440c020013110824400075507500c0b80b01d000c040c002d058140000000206154000c50f04240000c2c06414114001da0020340400022038107000c0c11090300800c80308010360028141c0d0014400c0f00e080c40400284828802e02d0300812408902c03c3d104070510010a541c032003e01c4002850103044142e503141caa0070558041e500c44d100f080910300c02c01000b000b500c0e01c07910134400a629295a45042c1c6081802c184142c81d4408605a40c68001c655001400380400d200400f8441e00a8010b04124 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 686701897 1250 686700647 686700683
    0x50301060501030b1c02030f1b090610050d0c1b0f0b16020d030f0f1112100b2a070906031401020c03030c070c0f12111f050904090f 58
    0x566803507400941454205480039400c0d0341e55801410265000c1169a0710b940340b06e0000924152591011022501480b1003170b1060204000d92402005415194980b031071311480d051005000c44654a800011000c0c061602e4000d5a0380015820160519040141c1844c006113030f45c400c1d00c445821980c503c10400d190040180c41c100050380200402a6100e160104440194459508000d18020143e0700c854000800c6c046a101e48844401003c0400040072440b150a466500c070b44682000040c203840000c050b10580042c2c1b000380d840c80003a82d0b003486d185141c80c907907840c0503c41c0700e1422560020740303074400c02e41004400024070052001085180ca135003406081e44a1052015081d0703401089800c4917280004112a080100903080c29580e0000e4100a0302d146402e42041c94958030001e40003484074000c202030060700d406441140d0b5004809020043c240d0b4158040d12195802a000c0d10034940c01800684040b54000c0c0c0301250a1000d9601d01d0102505001c08990101c407030248d410740 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 686703147 1250 686701897 686701901
    0xc1e0b0708180a020a0b0f040e040c030b0f0108120c03071703150f030a0321051f0504180201030c050d051905010815010b0f0706330509010e070207050d0c050301 71
    0x42c0b038008a018020300b03119034020800d410180c1c02158002e038000a0210000540030b03007200d0003040170250380c40d042d0a0500c0c159141b07460314801940d1415426000c204d0855039400641c1c125441e110080583c0400311ba20310030035400c02000704c13826000c24003066000c1081c20500d80b44030803490f00b00d180d4a150850b54203600360f80e210360450150f5400310707072000c00703490000d01c800c6083d8043c1012520001e818000d8907446811f413224800c00c90074903092018800d004803444580310301c0c3c02d2500c50b007684c0360010705c4200d4071408001c0035141705920046000d540664441c648012292922a1070040060351882c10754506548a854030b413451078451100101c14452070307000d002070030094031621925501030f80145206000d035071000340c5c00049c40d03940c40720190308544416038801e8050014603507181041c52000025040080604003e804025201009558038800c0d240c005045820990030700d5900b401c42240100030400354400d213180851036550701c0b0070700d2100500c10b80801014908100625007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 686704397 1250 686703147 686703181
    0x18040c1802040e0f091606030515041404021005160f0b010f08071a070c12020f010320030a0612050d03140c07080703020c060c010f110306010c1e0b0708 67
    0x4549106000a1003040c0c0a080f15903080707000e40ca5500a16280c1680c1341d400c09070100c0d11040c80c9000b680c0300154068140d040039100310854160f45000e41c1804041c08261440f0110402d80361481c1000980149003074441c0c4d50508a880c60716508240c9001c2c2014407518040c01c1c19180e814016540c0310410541a0700c0a025000307256400128910b000c0e20f517a500d040c2402885803104441500021000c61501a5001d0542059041c550981d48105250741075018003026401405002c0c0f01d41003650090181811082d044403030000040080c0c50741c00742c1c0e9040605582d110a80f11800000c01554410150010601a001401e180f56004801a08890200e0050034480503407104100c41c0080c20801c0e5035272280c00160344c5554103498a0100d040c60135000c030080d4001404240300340009015480a111005031200c208010803c3c0d081e8042da5000072034001d03000520340d0403800c1c0001c8150040c8041304003003a101c0281c00c1040c5c1d0381d8942c0040200d03069400640b205080201024580304142c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 686705647 1250 686704397 686704439
    0x60302120106080a0f1716030e180c090a030501020d0e0610060e060f0d060906080c01090321021e010506041b0c0b070c0c0b0315010504080705040b18040c 68
    0x1040500d001c285a813652401d0101420b143e0800403c071060107079001100a11064229a0a980b841c08801810901c3d070214026030005075581c900c0388860400c0d400300c0e004207401e54180d0400d85c5d60054142d030f40b903000300412600322124010000003c0d5090001e04400103441c075003c594000364103016032a01030014080040320004000820400b034011000c048600002d90755a50740d0342001070840d82c184a04280b07c82845c0c40c1100004076401d4030350143c0c065510034070a6803a03808005004544241c458040071f8103c0e28103074402c0c00c1c82401400d004a01150724010348880c08d8040d4001134004010700303000b84150751a2000c001c40d51401e0300c1000c0e08a411180e150b6245016414010001296100010000290f40001c036503050f01480c03d0703820b6150700c0000312803000c0c3c03207183d00e4481c3d800c10755200462405146402d000766004805640640d00b40c1d60052003518a8101000302911040e08100d4000465084dc2405c89081d140341d03d00c03581c000d80d2101040c901d02130100e4a0000d035520380b8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 686706897 1250 686705647 686705651
    0xc03071a0106050d180209040b0a1b02031911030a080603010f061202242d04060c150209150309060c3a230105010203040b070308040f060f0603021201 66
    0x5001c4aa00042070780c01d00303135144800107117208545003a003106001200e40a5442901c4c14104410400d07501d01d103922881000b501807280202d10001e005101d240000704030003580080c0100b42801070000482c4c5015009440c1c048150390707941003400d0565211808100000d0b54103020040d041c10240600500300d1038040701080306500c0c254038510010700f900c03c001d1007040300c0d920101d8150005d01340d00000c00d00c1c0800f200d66410403014400350460150000190240c140b020041c01e000c06203040e2802c85442d600d034401c0c400c95035501d0b51140e0006041c07103268207900340301c182d000d5103805041a07410141140c0d0140d81c2e05104900703518040e8002e0800f0002d4030200407000136803000d41080c1e40c80200304860058140d41401150050350400007090a80c03500c2c02c4403014502d807403419000462b44241200000f01d903252001241c1f02d02c1180a1000126010014000040d102c0c40400758400d00030074000300d00c2c1e0642c3e640c100a40f900e0803040d02005444000c00e10a40c94021542c2c003850200e2402 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 686708147 1250 686706897 686706899
    0xa02012901390c0b040f091a0901140102060603011808070512040609050306160e060d0603080705010207031107080a03080a090f03050c010b04231e04051e0a030e190b0c03071a01 78
    0x540801c01c00207003d240709554032103c051240c02c030022303200f0040100082100900d03603101e100811140d0f18128111340140700e1300b008a80c030b5040c103104489412000300d481710f66008190712030110b142d00c41c0348121002c0c03080d140035902c100d1100d0050f1014040c1c1d0760b500b0100710b144c182054509074001d4200d01400508441c544102500300074040040c8006503940c607201c100100c180401410345501c080c1c10050000b6013141000740641c0107184070b500c07030740301c031b48409208200340f6030740b1b0880b801403441c56442012040d0100c2d01658120360702a52036180800e000c003c90b0741c0c1c5030424119043c203c0100d9004182180005400e0094501d801001d69041280c1300c050341e1101c038207042401c0d20001207480c0c140441c0120810090070fa61502d00c10005038000c0c2854036000d0f50310b0880154008501c64a403040d08090440440c40401c003680664458021003619000c0001154882440641c1007001580004443e02040090a01480c0304806540c4600407400e040310203600c1401c04500c2c0e01c0d11100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 686709397 1250 686708147 686708159
    0xf05060a06030c0302070605041103070807120602090a08302a0106050d140105060904021315050a0b0405030d020727150306020a02012901390c0b04 65
    0x6a80c10448150385800720b10216003003000c0d002031217003001c00361655040804110038010341244582d03814030b082d41180e1503ea41c500c080c98a448450099202c84d070320b01c034254400700f00c0c250060603070914010140c1c0c06031071351940f1086c07a00c04d4219040603200c92640103041c610b0880d9900c1049a94401c0b909441c0c0b4103070000e01c1d4940700c0386002d0940050490407a05040340e80035030100c8044d000c00f4214082c01401c0b428604c440381c1240400040d950b0911001400c6420034079401d6018640c003070180414090034080c0c48001d0500520083c2420041401c00161591030700441801442420060b595950401d401d0609101d4414082c0080d580205070812019001e0030410602c1c0c0c0b0b61900000c9120600e070504809000c2140040d49522607455020060000d0f0764000e00d2034805540081000f0345908500035950542c010039149030410b916003419055000307182e82d020200c42507580f66100c1c29508000520758928a16000c0540181c081250400c04078020985c042c0405200c141e0070285824 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 686710647 1250 686709397 686709409
    0xf020d02070b1605070b0a3516030e0d0c020a0803040509190207020a03030519030608211201120311030c12090d141f0209060307110708010911040f0506 67
    0x305a01c034010304049440f01c00d102061207507038003500f4405d8585507242d014800081c00e0300303000130556441110150030768580e450035594210070b2415508480040d03580d41d0a9040c060f100b181e4040c4240341e22a0b81402e51140103102c4e6030003641160311070040101890060001c007001035000103105134401c00040c00184e40300059143c0c0641707041d500c10b2400c000030342c5080290245034002034100a600001101305600680584170404500c07007000048164042c0440540d10180f1541e40990000f95180003148843e0b00c4980020150882c400d10780108690701c002119401d81c0104c04440f05840c40f4010150310101035443c08075820010750a245481001d591a4405041c50885a0000084500c01616440700100d085c540201144141c50501c20320686c0729441d03c00414101e121181c42a0401690b9100351420b0103c068034142c1107039551041596003031010030300c3c1c80c5148141c0400050a606c2402007080751889440d11088071a090402e020a8078070100802a00c1350030b08080011546030f03c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 686711897 1250 686710647 686710657
    0x3060406180219181802120a051006060305161223040b010303111203012c0a0b12072318040c0302030d1d10140406110c011107140415060f020d02070b 66
    0x44487c01c10503003188040300c0c03820303004010040036801130841400039416543d2118048400d1070324103116550b9a0100402200d0032208003001103070600703111080403030080e4000a182c00c080f1101e1140e40b200380009c580340f500d0464045580c0303030b58000184209076014882c1c804091000009007040200f003040c0b1440740c00705000f40c400014200308201c268403c0107134240c1d00c1000e6108446880c5c00d106200300c010f008403010340c034000c0c0d6102400340058840041e4003000c8a400942c0c3c4000030680c90041d50010565038280756001c481c0c031400364283d1410040080c0030340c1c40340ca51080c0fa01d1079881454100b082901a20b03042c441310189002498a00c801400c580352000c0b15405420110002c05845c1c10307540c0e5040c201a00c0300031601240782d42c0c003c2401840725034860111210440000700444983c01c05105540c003a4002403002c1107101240d01d12003a1214004002051826000d00b80c00d0b00440254010310001c1c04070010b01405035010b2101a024607000d00c0540303195030070101c4070a81c511031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 686713147 1250 686711897 686711899
    0x61303260318121909050a08100e0a020a06020d02010606051e160506011509092f0405040c05040608061203190e0d05060f1503060406180219181802 65
    0x1c00d000c2214203103028000f840a08a450b400c041d140d000440c640c01120721058000d4020811a13400070440389001d0100c101160b49071002415803100e40c12581c00902413078050b503242407140d00c40030350045c0e031400c600300c015003000d500034203064000000003825113400ea070096040c04001c0180002d00c021040000704074410a520480e234400700c45030380290212030714001400c0b50083c07400200d03402c2c070796501c849014a103907170728000c40715201d00c00c9a00304c07885c59543e48041d1084001d00b58180100004200e01501c1c2100d106040c90765030300201741501c1007004001c00103400058107201c3d0315042a10710740c200e001a03d1240658640c60080ca603203100d8580922071510300944d410f444603104e200c414400c038801400244902c0744920b00550703200411781d6001812100d90300002c00c90101240b4020240c1801401402540c840c1c4d15110024004181e030110a51104550000961a14040c1c00803e000c0f0007003c0d042c10703190203080c0e030410030405909801c10b400c01f0001c0b40b01400f55114407144c250 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 686714397 1250 686713147 686713171
    0x60309030706050f07021b0a14010210020d020307090b070b010e0c0d02040b04031118010e1b131a0901050921121908040521090613032603 61
    0x191150114910301803614014401c5090404102d6070307a40c0381280740d002d2600c54081360f242012001420082c07003035a500064100010740d10400540720607400c0500d07003a406005403001011082000d005030380c01000d00745149600003040c00a0180d11100074130043c504100c0c4982014841d54441b806800180700342000d2010050111b100040b18100711552a04802030442d43e4559440e91403095400900c010f503841c1000c1c5020348540c3c2004824006440e0003040c00c19000e1b801d01940e03101d880000740c070200030100d0310300051140c40f41040c003c044091600051902c030078508011010045d2100700d464040c40024001044c580e42c10500b5a090b02c841100c911001a22904007021152802d041c0d2009034070032145000d404103038403170040c00c01910380703801288c414421040c03d9508050903030b4014600d900c2483d8800818840c0d0003010044511000100e140010100c00a03c0e540c104581401c003441c1162400c00400c075100000c40041c2c40070103150550900000d40b0f02e41d985c04000c2030580c8040c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 686715647 1250 686714397 686714401
    0x20a150f1d041a040605060412080d112a01150509150d0c1d0411010e0a0504110408010608070e0105060c03040e0a0e0f070b0d0c02010605210610140603 67
    0x5010848122800c21015004000140b0641c0004640a40f648011030240e40760400c0403905041000451341a02c4180410742c1e404021070395000d100b07a120f01c2201c1d020070343da10307a170700c1905050000a110080c2c0040d102e04a52411409a1300c4a505811000e42c01d03070305d4a00d8480f0740303000b0003802100315082199a40c0c2c02d50b81d030340320104198400811136a8411844d10a14041000c20344026050792403545054800004203814002c10110548024002c180315081c440001d6108001032031003030710041d20342e8003480d039140d002c101918040400f80321810404281401004000d00c03c1e04014a00e1100415000745409000d011200c4180101c5000344d80024100c4250701c01081200c00400d2010110b813220f1134003a0805000706a0503002107401d0160185111000300001229010b4800c0c0e008207900c1c00b91110700b0840100f284602820955484103000110b0381d460303a2038440d803207c1c15540082c0340a11a1039060030448000d1980301083c2d06110f0a012006900d4406080140c086c0d0340d2503500d07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 686716897 1250 686715647 686715677
    0x6030b0109030227010617010504110c10020c1005100e100305120403030306050402211b0c011b020a11040c2a060e0a11060706110c010504020a150f 65
    0xca070360741d08060741282140400484c1c00062511007001507290228405059803240d00484050140c5400700c03200801601c01800146441d40c4045510314611004911380b444c644212814011a010003265803540803c100703041e6201403040103083c0004500400081c5000d8070f101034009080c5c00390803074410700c1400140100490216440c09075800400301d4180d0100001c2c50039860f07005000031400203041000020316408c00d4003d0b90a107248407a410700807030f03a00754260b030380c103440c001e005414400b00e46804980d0300459000402d4483c2809001050f0120158418550b0000c40d46140c411075100099100c0403601034007072900305030070403100450f000140c0f010458025111001d0b014038603c070001c00607466022401242400351184000740b2030703c102052460f0701d9031942017002d0b040c40080940c1140324507080c00201002c501c90b0200086403200c0b00c1941000350071000c1400a02d80d50303007050100b54501004030800400d2051541d10100020001c0148080890701540040c40305404401ca01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 686718147 1250 686716897 686716907
    0x2060301180e070e1509070e090601050918180601081902010e0405090c15090616060f0501260d2f030c03040306050108010e0307081602042a11060106030b01 69
    0x46218000d0849441d04d4846407a5018000e041d10000000070240c200a0018109120341030300c2002c054951a14445080b01032040465005250a040107410004a2100d03540c030404028844c0d0004400d40d11460416560090460510340c004069400040100691400018218034000313480003820b00401c01403006a488029031460140d0260900307003000900c0000140c2c554480d80201c41d010300e520400c52014010340300e88414075420250030040348140b01040f0004109161240500060201180072040e040315000e030040c60911030f20004111000d0580d01c0204241e152400162400c50072070f00002c0c10054501140d0002e4501e59039400207654111070782241d0008030f50341a030f980c84a80e500f03019142e41c4580001c58540703140500202d0650814411190050504c070001c6207000315640b143c565541200c84d400f405051034021b07240060f10f40d0b000d0940762641d11a0584150f2003d03c801c4008185200841010031501c480d052020850025009046030040e0800003142e40e9114012a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 686719397 1250 686718147 686718161
    0x22505010c1103030406030b193606080703021207050108010909050316050618060c0d1e0f1d030a090302040513080f0901031506020a11010302070501140f0604090206030118 76
    0x10380f5000104001030481c5d00360300004d61242046a101c0240400762050200c0d0100d5800b500003010780703090440000c0f200c0b2514616040c083e0796a03020f0707500030a210b040203070351068114120700d4002000800c01c605014094110001800d070103085c3c0a414800004c0c4901030520a20401c01d07144c11010050107014001c03651030b4140051043e0464544e82401035960300180c0c0c60403000500c1106031102c20902090ac20f0294140010444c50150802104c4001e006100a140800303103058015407042405841005110203880030089440c0240d0310403d1040c8410821040191700f04005544126a1107220300c81a2541101c0c0011992030fa850315006a03402c99200512661001498052400f100405800300500903a81840078500010200034401f2081c032409004d0303232040580c03500003074032000c00c001910018900103003400d0750768071880c3c2940d01c040c013080c420443e9001800108402c0200140d80445d05403428400c0c606c0a07408902d6a110511902d5103c42e44101d1289040810380c000007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 686720647 1250 686719397 686719399
    0x112020702030105040b070806100909090203160f031a0c0702010c050309060a09031b03050307060203092113060305220f080301180e0606011205091c050901022505010c11 75
    0x1017881c2a140c542030210007030702c0d2100071503000e00000b00380c0d242c6400c491141c00e010340e840f5005a8601a1004e01a04141004907890b00a10019060008407044003100030701000003580f00301459401c00028040d031150104188005031390412030750203843c07001c45194507428a000f000139002030902a0840c0180724081d64444000a1000021607015164000b9a8000e1000c85401416174010300d0415810344002000e60308188028400305150354060740d0b010107071000751005103402002451480c051410311801b50341012030f00400c125880c0000d8405010103007410041c41c00c3c0707081c405402003000e00000f800e1621941d107190400c07001114031300302c03590702580c0395482e03585941007087c90000e0034400c16001498140691441000090032038062401a102c40401d01103840c0500041d01d0014948407461041ea9045c01f40e00150040303c0c512521079944068480c4100c800080c103107582400303035464403060300344d024640003030100e0280300320b40302400c10580c08422880c0c40800e00d54030100b19 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 686721897 1250 686720647 686720651
    0xe04090510090c050306011505130b07140c0d0b0a0903090b0a0201021b150606090f031b12060603060c031b0d0603120507050c0909010207050109110307050a0303080601120207020301 80
    0x50680300100d50007100b0102c0c810060041d00c40d071242c00b4159070f10030920419400d0f9101000130800ea900840041500400241c4403000b0182c0366607045000e0391180e0340440b4204041008068981c0b070500441a4a90303044401c104403425075101c4100d0340030050300b4120000c1d0b66400d003804241c000e80c0c0b07080050a91456a68a0758480c1e28042c0c001d400118401040300a160b00d01080c051000c030342040050350070740001d0341c01e407500801d11490b41c11540065400010b81154010a698200000c0a41000f40300c101d00546e0800010300c41248102d4001c80340720f5101900348151a5004030380300d9880b10b403407c0417644a580350302c01c0d400c0c951340203020300ba4066030000702c5200c180019003164042c0ca0003240d541079040d01d034100c121001c1c0b062074000352050308181c0c00d0b04810701d0f094100c150080715034030002d17040c8401c076100d1600715008280101e4009041034140071513030409020307140083c0700440c0e180c0340151a54034040e00c02c0c200100b6860401203400d041484942d80381d41a14a810703009402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 686723147 1250 686721897 686721913
    0x30304120b07021e030406051b1603060c0c03140901170708041a01060c02102a050d08100e07021614040b0a1a03060a09140f071704030e040905 63
    0x101180c0d041c2d8080005000b5140000c00310900d85070340c00b60b030b038040304011480c2610340f41d4119902d8103d9034200c04000c3c8034807129035030100100301c1c481d0000300305030344103500b280f0358502101290b00c00300414080c0240d034801e04021a0f0810165640748100400450b507520b09440100d03803140c5d0b00c0c00680d28410710351060001450348130092034030440c0300300081c111481080c062080e20101c2481000e001621294080c0010706108482c00c0601d012420f2003441c0358450100c10220b1340e0f060842c1d0500442d80c1c00004113001c810007520f0307098109401d0441d81030401000383c40308000a401034030411072101000c40c0d2068420001a040224000100e0100d80d8079052541c000020320546540310314206944d4009900d00340104004a030302002030050540445c11460741140c00050940364004034008000440e00440d008102e12010550f000055074a4000c1c0d23180c9a1b400702800b10380400280c5d20f4000f04203605107081030303002a00350600707030540d911400014016240c8008000c107113000d0701d41 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 686724397 1250 686723147 686723153
    0x909070b07030c03080a050411040c0210020c0a0b100e041e0b0c070506070e10030f110a0f181d0901023702030f0a050708040f18050a0504050c0f03030412 68
    0x3c4000c9000b44699901d032520b444040d10002629800c1d18040c0880b40c5c405c01c0500d00d441c059100e80300324180d82c010b440381c0305d6880a0143c126086200c210b080c0c1c3c0c01503590081000400c50745140e002c0d2030001d90010260401011004e81c01c0000c100030101c844020700740d0b80555189881d010465403000c0c410015150a940701c41a40d0805201107605100e140301003403546005101e02a8040e10242c60912402e01c0e44500300e01238001590425412580d903035201403d03048080c018440000140c443e143c280b882c54800070010340071045c1003a1040b00b1800e040c40140b020f0940391306040b030060b020800750303160300070003600a1281d112400000b0100c81d01c0380c006910322522030b00c0205401141035140d010141c03401c0e601c9104002c03643d10704410402c161074038203000740040e0003a40d018075001420b041c0c071110701030b40c81c05030358000c05c0b000360010030b4044440380c8500810b503200031200d0040c0f1280c00c160755801d039110b0042080b42d108120f450f61490050b1020011f07a402006085800c0305220b010341 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 686725647 1250 686724397 686724407
    0xe150705070c470f0a110f0a02091902030f01030203012004090c09080a05030301081c1b110a030b0f06010302130e04030314090c0f010e0a050909070b0703 68
    0x101040720502da03403810004600c440e8030454607000b00400d00b90100e1040c2d240181d120010307001a02000076102a2181c06145a07120140941008005441e03036105900100580b00500820303013100c4940c8410800f00000a01249030104558160b4038080300c0e8950018580383c15030f480c1002d45d910f91000c010403001c40c2e140c0b10001c2c12640254020400f50141c2c41c070000e442c01a02c0e0000d41c6201c01040104281480f0354880005000140303050b42d44141c88100c3c0c6410404040801e507410b40c0040014001401c00f402003410741c2d8101e00d1010b840c200146405040740548010b0341201c41e80304800401401005104807000040080a003581d0039120720f041051503209840d58403c1014000009542d54020320861b0609000040c1c04869036161003000110000010300c100c0405403101d15602601d90740318a20f42c0244640780183c0b081f08442401c4c03090122003500001d041009000c2d004010b51200301c0303100c080c0c4800380c3c0c1c04101e9a0341d48038032601c0e0042590003128164000101101416885 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 686726897 1250 686725647 686725657
    0x3100b0d09030f0518090603030c0a03050c010c020c0a060f0201110c011a09061f050c1501060206060901180905030c0a03020309090a0c021902011205011403100203090307060e150705 80
    0x944540f8203040c5140c0d01241d40340242e80030041c40a00d038092004003458000c0110380d2140005088074586001200e0140c01e150a07060304402203840800d501610010a025400320701841d48000c00c17100b000d0320006455078086124010034060210851500903100303400500c00208010340f0076941e90801004035000700341001d00c0d00c0d4400c1d400c10280c40d0624001040c0c80c0602c0d002458502c0311621443d00c40b40c6816002c46d00e50070301c9420402003440220030701800400e40070b41740610101c0e40c500100a801c1c200300404980c8560006c2005100300542120007040200e47c0c3d0b1300004481c0c0701840c01501c0c6104090308010b140c0b05001e2030400b0103074008020542c100f81034555000d1a116202c0900540303040741e80950140c1c002d03a070340b001c0b41e101111051014500515016040d582880041802c036076081c0c1250364800c00c0410155914242003040d995041000c10045281d0325024501d6078480c011008010416502e4840b54500100700701300441403a900002c1612a90400c4440a00141d101c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 686728147 1250 686726897 686726903
    0xf1b09060e04060503070608100e15040f0209090a110d1104140d0803040305070303020405040c0207080118050a1401021902010b1503131713140f0306060a0b03100b0d09 74
    0x40070440001c60515005490031140d029000303050f4a42408811351f40c0e804000c0200600c0c05001c1000110383d0f03062401503000c0c4035411444100505810140026524584046440a0f0041045000c070352100140140c0c0400304281c00140c000001c1c80210365031160841295900703040c48641c0750761006070030040080780d4800d02416010094a0240f0240d0341280034090006441800001e012a019000606aa0744245001032400f501c580c00241100c6000a030b580060340104c8041c040b4140912443d614001c06003015940c08500340d840d81c1d51030341c0e004001040c04030194074080000c142501561030316000d416403014401c0403070380024028081440d07168841c901c0c1503907103940d004010044a00401d00c5101510311b458441d150b00501c0076000b440d0039450001005043c00400c01d08900c9005407010080d051035148107002004801412019414801d80140080c0080d5560f405100c1e0220344055128548030b6070f400310001e0404030994070042e46400300142200e9849070940c000500707544 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 686729397 1250 686728147 686728157
    0x7081b030d080606040e100f030302030c1006050a29040e0f1e01140d12020a170a0e0108090a06110307080f09030f07050109020d030507020901080615040f1b0906 71
    0x450028201c40d5090b06441250300284104803d0162440348109540d1000c100780000c03500c00c5d924040401042c01d035a20541c0103801c040f84101d00c2c50414451003902c0d4002c50740c18007107142048006118900c0c4c0344078070300700041240c01100ca46070607200110f9030292580d0005881e195a400ca040c10458115060b030500c0c1d0030107001410034000920b41c40e00c2c281110f010444039a08150000c080e080700070f1000c0b03a2216480e5085000070744201d00d0291031408641c080d101d10b031010f24107807521151030305540c02480300074428141c40c5588401c0d01007000e4030034605219241c42c0c050354581400340d2050f010f01001e04050b0890025030001009500848071a6900d0005075145180c8845e803c1042d9900121501300b00308920407090160003502d03005000c2c2000182c414090740c00507141a00c0341c24100c011480100c2c01005600d05140c44a00601007000500301d00c4c0340200c000801100c1c0f2340709492265a446a00384654042c50740044900c60342c000304140d4400d62407030040c10781c00144c80b403000021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 686730647 1250 686729397 686729413
    0x60302360a091b08040f051f0c03090b0a0b061e030103030806091b030907180606020706081e1801050720070302010c140f030403080904271407081b03 66
    0x2492403282c42008641c0850120b03580c02d01500495140c08045c0040c0e403001c039401c0104022600612644040c4c0454504071440390b400d2020b20b60070f807008020030400780f41c545954440443d4404140e10343c0081c40c914001641d003841c07070010350383d40038458070448030940c42815820b0340e40d1000c0c01113040c0c0e4000d40b1914134540d215810002c9041045411002c0340e0114285042c910120750051174000252800340c2d02440e8441d81c0034440106500c40a10383c854a81c2c10130040c1603014083c5601510151401001038078200303c804025002031141e40f2400221711000070207800301c005000003207060f040028080c505010800610070503010143c1c01c41220101046620304000040102c2266410b0b16600080101511034500d0014014081034140c0114242038119a00510081000c0d6203c1c075485a1208809414070040780d01c4e144000700e100070b1058503541d0086c180d16020311076a62100c0c03440b101c1d0b40c8841c0e10303908040c400da1065003980306103038015000055601550030b1050080e02120228 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 686731897 1250 686730647 686730659
    0x70e090c0309070f080a110405040f0b0a0f141504060b0f0a0201092001030e03030912070f020d0507090c020706141605240a020304120c031115040506060a050a060302360a 75
    0x2188282e400801e2110740c42d2f00d040c0016211030b64241e02c15003080c40000c0da20945000c04007555440742d608080003200c0d00400c08201d000400c402d18542040c0d0b0100611401d0601444442c030807966419212540400c50910042c402d420074015564052002841042d52000040e52410b5008420b03001c64107041d110500041c0000c185c1e80f05003044001071000e03105c0c1d4000789200b917008034000d40b95260703d4030791240543c441408901907144910300a24625141080200440c0c1e140c3c003100d4119080003400b0804194441d03507020040101803440b99580300d070140300414090b03020380c00800c18000c2c2c25000355031081d0785060041610796a10580c003a603640650310f804030301c021200140a0001c1d403107150301040c800c568015007148642010350089d94802e40192030b001d00e10b60002541070b800403c00080010900030b0a40241d0251251a402800c2c5400112920028068041019400f1481c203c5807419240300d1281441403406035a0041c580344940000c0d0319515103a540101a1040c0c00142 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 686733147 1250 686731897 686731901
    0x60a05030a1d0309100c050a0804080610050102070501050904020d0c1101060f05060a08180714010e01020f100e15010314070f03030e09060121060608070e090c0309070f080a1104 78
    0x602c14254018502d04111102040780c050002c4600c42c0800c4070010b00440080c00802c550202c4501a00909440c3c501d003490542c03030501f008207040b2111047c0f06081006980005180c1c0683e142400c2c51910b9401c1c01e80450024007031200d90f03401341800c0403490014941c0001b0181964802040280f040c2901c0d40e55203c41d082840c81480e0b0020710410000074454819000c003074001d90019a65242100101280f038a803040da03411103540300c1d91104040d170641da0081c0c160307840c12500780089d1045c104504510b503103504482c80c000011a1311901c03c1e00407040c082c440c060345540f194041c4905940c4a06009214010318401856588100d15011a5400702450030380c0c101d0fa415078036403140b402d43c1000d11020000c040c004134140f007102005c2d00c030301d100e4000121803105c04851001503220318050b00127083c800094103400c24040d100d010a40c080c1c0750321015a50150300c04240a941e900e4001e6100e190007041c0e0300c00448a814464045942e00d40403c41d042a00d008800740404400244c0400003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 686734397 1250 686733147 686733191
    0x100510031a12031e130f05031b011b0c0e09061003032105010b0309010b06090102251a03100503070f0303110c1c0c080d050405090c09060a05030a 64
    0x5801c40191000c07840614100c001120340300048015242000c2c05580c25520950002084007024100840d40201030780340001482c00400e440640485400c0c82d144c01309841c0d4140c0d032040d0b5400240300d00001e4590340117000611f2808041c0c0130700d10b581c3c00c15042c1100034542c03c1c0180d80d6014038000108191040014506004066074501000850b00d1940d06443c0e080034030f1140c0c8202c000108051460002611071280248900703140c0950b02c1c6000d840e600d00319803045803160f104110501c940a030070f980c0081d010740003c502440046043c011407502d42c114803016445040c400704102d08030080e006c1544007071405085000d03900681991100c0030181c480d00390340191000c2144540302040401e11a050055101c182030050710584042d0f000490002505154480301e2900442c0854003007080a0840800410b1480068084042c000030020540d102d40c0c0309043c456070740b50003c03810450b807600869400200080650b0b03694200b001000c0c190ba0000c80c0c83d100b440703207003035075070815059581c0c1550 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 686735647 1250 686734397 686734421
    0x1814032a0d03121803110a0b130204060b0409020c0f01060305030d1e060f050316180509031b01090c0503150406020d060306020c07260d0e0f03010510051003 69
    0x4000ca81a03006124a1a504003000c0c2d080028000401038010443e100d1002c1403c1c000c0380d0102c01c51103900b4090401d00c0c42200c1d08645501c507942950104003480c0c80103801c4005010010441082800041c016086580200c08010300024000525050550050140c200686c05440c00b450542800a00300c45aa11020304140c1040040810407509944599040b01c8984212003e0740c03005403103003088030300d140c0011007101c0d0601c030140403070700e410401c0c42c859843d03004018500d0340c00d0006a00481c000303040750780003580c3c840303010403100c81d41801540d00e09000818020025800d0041c200d02031b248841082d0740c44200b6003030201d101d0401080440100104050003070081d21140c0d101d200a52119101c00201541d030304c000b000040003070001300800051140140043e9050001c5041d02010105101e02042501e407154164403801242600f1184128148a00811072040104540c0c500d000740040e0306502e84010040d2030380003500000c0a8030002d41d250321080c46c0d444410f03000c88003a1400c072 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 686736897 1250 686735647 686735713
    0x220f050f0a060e0607020d050d081911180102070e0703060e070c03080f090106050a0b180604051e010318080307091509030f0f02030303012304020f030115181403 71
    0x341480f414080000d0007100c0c4041c01d0341d1400c006036118181001881102240022b0603542480440c644c0d104072803888207442c82e400c000714181400e00c80c031140304448060400610715011282168028080c5800030501824041c9940c548000c0060080409018002c400303d04040070074802d9114070b00c000c03200395043d151000c4640342c14040580d2614000c0c801070596481301d00103d80754580004582c0100402070420f62580362800c0c540700700190140308603000341c0e020302081026036141c4814080d0f4a24840e03100742079500c1000100e003c1e00010044000700109801d08504101011000354450756003580c401300e0b1661205030300448050382c4446034001458685003400460703004684006007510807142c0514950705540400c4c1907030402d9104440e0380d00202c0c52840001220070411a000310211170440c94100310041c002c1d403500040c0101e03034007c52440110106a801407040b07036003204250f041d2060080d81e030a6400d00000312040b16038024081c1000c105030550b841c2005400441d00c6602c0c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 686738147 1250 686736897 686736917
    0x14010b090f19020c0c0112270503040e040305091201111905040e10030b0f040201050a0302180d0b0907090b03070504110d0507030b01080c0c06010902220f050f0a06 72
    0x500ca40081000e4114000020b80192400310401103200400d452195000900400c0c4800030014043c8001103020050517420040c1809000016240906104120032401c6034241201d00f003461031030185402020847c0e0001040c0030034076802c0400750100000c103e0301d004081c011101001e084ea660000c0f640101801130108142c0020750151004017000e1601c0e1580c1095584d40c41303403000320000d03601ca600d52924000140180540030386503e0384030964044080c2c141c00e0650000b4120b116000c144420594003041035045d40603d40641a40400700418020010106003000c8603003420070740380c2c00301074801c009002510380524020001d500100501501c03155240c02c080c80003406031140c0c2114104010000c0d1801ca001c14440d29000d8001c40d5000510486084005400110040e1404021071400d002440b103600001034180d040d20b043c45809621081412100c0c508002e01c014061180f19100c0760124049000040801c1162811190b1031400007400303003800301100080c005c0800040d20120 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 686739397 1250 686738147 686738161
    0xf180609181e0605010321050403050c09070c02060309010c081008300d021305061207031505030d020f0d03021e090d2103110a20010e060106090314010b09 68
    0x22401181508040e4480c51074a071640c3d042d0807181c00745c1044904843c1c08034480c2000000d0b003400c40c0380d010941411407070b2604646400fa510034204069034812250440020400c0b485040700500d0b0303583c0980f40035200c1c18900348443c0030b8001c41408400181c5040300042d4014840c0e04040106c84105000d0400310001544907041171841050300030180520a4607200c45080c100003c00b008a4850303030044e200c031450792071606848240d5220740e201e004140072101da002400180c42c0d130050828140080c07420403513203150300c1c01c07501c983c40030b617060040742584c0b200140c000c04d00b6a410041e500035103000580043e0142c0480c000c000708002414400c0c03100d80b41c40c208802c0201082c100092840040c003800c2d9607802c6103000102580c40042442e1b03411008029050b0040018112124640c0d608003003511038020100d1006610550355000f0103021656407aa0a50000c0340c50b05030001a40c50399a103441d00900180081e110031210204a00402024020706200d05507001000414200301500c48003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 686740647 1250 686739397 686739413
    0x601020714040e01110a1d0d0c0e0402040605040e010609110301060804031b020d1109130203102301090b0108010b0c070501050a1e020d0e040e0a0b070203040f18060918 74
    0x144944599941c41d81d09103010ba0440c0d000d451701b00303000c1d950000b0f403800da030360503203c1c06d25040c000b13a01030201046808002000080030506a40030307040721401694070307400080c011309102d901c05a006440c3c901a11910f45041d044141680c500c04420b101c9140828401c45480c8002d20620b80041c03485d0003c100040d00c5242c00c03802c40241d02c9440030b042280c540010307017214010b610403140c207a101d010217489030802140d4140d01454074482984000306603004244c6501d0440c1c48254195595150036002c0c4501132042501d90260f41001021503031922441c0d0f0007010400790301408141050000600d9403d00421500400b40701d1020b080b0700382ca00740040d00d041d0801070114052245540c0c0d80b490340781503c201045407500d070354020b2949840100d0060301104405480c00e006500300805510344500016101a941d0b51201201b0503e959148040b421806680c0040540c600d01b6440000c448404117001d1401c00d042c1401005022b0380c0b4540c020848014503940444100409200c50209900c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 686741897 1250 686740647 686740661
    0x40f030c0f08030c0a1b120e01140c060a0e060c161103030c010b01030b040b010c0803060d0b01030506011a03220615090e010606020726030d0507080f060102071404 72
    0x1c0c0c1480c41c0415035680d81603030541045a50340002c0402194a4203502c1e4400380b1141102600050a80c21128075103403a000422031748003410900c0341c0074942480c00c1e481600c010506c0c80e1880602074884103080f00b650b46415042d54098074450030420b4800101c94040741c054056000000302c18540210040c064400e034044010550f220380040b80c1000e030301e8900340020117140300e0540000403d04000d400140494489201d0103005614210b0113402d83c3e60490b0030a134203541c2260b9019100da03103190029001103201c06004014850b0040000100a070001e072031410380e44a415407040d0181d10082e000d43e14041101c002401113400225070b1280e5600102150403640102d00c046000511081041c401c1e01d81503200031155a911818401c5c141401e21481024005c0c0e480a40107035840c0c0705c50003000b40c800c42048400e9800780900005011000c100b21a0070040e4440f042c4090b21f40769070003500460307007101c0d503007507030b101c81e5000503050b41c408640007007518814411044200050f1061000408071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 686743147 1250 686741897 686741903
    0x2c010302040306020703030f0c0926070f0305030c060705031302010807030f18150614060a0e091006232b111c0c1e0e04060308031e040f030c 62
    0x30801c4048040303803042c00100f03007140c02524085801030845822000310b400d865170351401c0185401062110342d40c4000303c0010340007081454015080e640b10300504001d91580700b2810490480000801c03c04080050065a114032040d40c44d55501c000d01500d03a48030071140168201c1160a9482c01580900030a0390080d1f880d240006041030304240903c01c4410101a2440c0c000e1510180340401020311161501510000300c02d0084903d0b00d040c0c48840c55081d00c0061113024080340c1c1102c6144200c600210040b0010920719050a2034000c8c804e0300d81c500d01603140012814504c0505c19244541c0198000030401d03600d0349803040d45a644586801c95102102c00c4280e0502402c4032180c0354003550110190041c0c130f06035681c1c0c40b0914055101c50814a0340aa00d040100b51400d080d0000c4c85401e0110200310001c004401e894412900900484403d550142c80c0120110521a41502075403080c05641050360f0144601401d03100d460904850050280b0380000c40c200000f44a41082d5188601c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 686744397 1250 686743147 686743151
    0x31e09030204020c150108030414030c0306010302091f090f0b100e010f0e031c170103170a110f0607030c030b030c1207050907020102070b07030903230d0f060f062c0103 74
    0x43c105003501e5400e1f4800c170f0850384040ba0a0007034440a240446120f10200d000344154003000010039224401448061311500c141000102c02000b18009117a0b0387c03030001e5010080c280c0ba40354080081940007400f240c0b1030303e80241c110700ca0500456040700003115403100203071403902600446180100f0002c1e00d08200d1601c40a050f81c0c0c4040042198001c01d2400481c0c69084140300100a1254860342c58801c003603907401040420840043c11001c034445029442e41c648654400f601c91007107100e18983c05100700c4014001004020504600401c1c05a505101c4c0900000c003c40a860070303601c104e6032607000001080c1c40340ca00900982c0148071480251400c0943d144002808400c1c00c80380400541d400103a40300810a0504c1c445900c0111410104105290b546000340b00c2159540d51b94008101d000701000c560480303a068501080c00004140014100c2140c0c8034094800c6204510440d40094800314549000b980c070442140260b690a40c410300101a80301034021600c412541415 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 686745647 1250 686744397 686744413
    0x70503030d1e051012020105090907030509152809050f15010803070807020d060e070b07150c1b0606030b01030b06030d0c08090105070c08030412031e09030204020c 72
    0x614148060158142070300e00c0058450340c0c02c0c1c40c00e18109002a01a40c51038504001c202c1c0c0d2403200c40121040e1042d41c944400042c40d035200591300c0d17125043c00680e00100c11070410a8807541500200d1080e04140c040e00c41c40e09000111848103c0d09450040d158400495031116000c0c01c101079542c0540fa9040c08101c1601c81d440c1c81d07040800b04490710f04a50080c514100d481c4100d001c4440c010311440004501c0d00b4035030b80b074264150049203002403180000841900500101d500320684901480c82a11400d80d61000d00c26499400000122030503c00e81e003980d10180e05910444180d80c0c0280c1303c0002c01c0c00701010880746105520001c0b20682c2e030700c1a0102c0031806904016029600c41c805103046407c101c01014a4510321805540411804000c03090010b01000180c8055003001e00701240c4520b46031401001d0005241c0011030103100c04180084c2003c0c0755140e444001d80a40c895036100c4070b0512400d007460582c08906004541d00f02c404100605080e4000e0255180c8082921411 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 686746897 1250 686745647 686745649
    0x20c15070c241106060105030604090204050709050f0f0a050f0a0801050901060501120c0c08090409060509030306040608061e07030608010e010e16030b010b07140303070c0516061706030705 83
    0x480c480e070000d8080401020107241c1c0342808548000b03006905003407071500392070740f1945180c0d107200040405040000200210300c150310746400000c030042d40104140094980500020320350712251283c0341c07041c04607010000d5a800c00c51441d091201000c2c02c511040c50418081c0048058203c0c8000d0700100c6044000031510020301c02c042c0541130344e1001050480c0f406000501c5843c610059403042032410900119081d0000c4107404459808800580c85480c07a400040080190300c401030045420b20b010006608070110045224030411074003045002c1d02d5004903a0707101030032504c1c0007003280355412000d646125042c036a5406895490040741c00d5840d101803a0030340e0754800300c40c2c119a4640060608001003446010740c01d16040c17030b0f0100c3e81465a210105440301c10320a52501150006404051080303860805120080001c1107a5507810f0004009001103c0303220191200c1c040c0030040c000a0928081c200f080301c805aa610302003401e1843e004a0300000609001e9141c400c8840001d05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 686748147 1250 686746897 686746913
    0x3090904050f190b06010815012007141203070f1106090a06050901021b010e0415031e0507050607170a090806070306030506060604060903080c150a0b0f10020c1507 72
    0x2030f508114601441e10010740c90484030801d0081c00319411b0190b40c03010030103118250321240d4000329007403806072058000b6400c030504c03c5c400e0b0366420086002c0c00d94082046000041120b0385042c06507281d4880010220b00c098032402041d50051100c0c00201404003c81d401c2501c0c945810300c0204050728021144001819100195200c1000702d0030101c1c800010b507170144a1801d18100d21300c1d8645a1288002c0000d0101c540046254425035517180d00c0c2100b0903180ea0000f01a6a001031b10320046072603da0b8590710b0841d0100f0823121442203c002085074280300b429294a19440b022000d00d400c0041e901e8402c0e500a80e0200c0c04000e11b00100040900b020421103000d80e0981d180064082c2c118208241004001403950f40030700f40801007005030079400415001140d80014429444905032004c803414034405d0702c0500c1c50320725184188594603132103074414000180e003180e05e0102c0741c0807601442a010b0300a2100350158201d0085202d403400d001e40710a6846800d40c000e20729100c21655103c036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 686749397 1250 686748147 686748163
    0xa15031410030201030c02010b0f1011030c0102031609030308070309080705490c03090e09011e09151e0f0905070e0f0c0f282003090904050f 62
    0x184450819600b0001e558140c82441700a0003507100901c000011390000c81c01c003131802540c50b0f0049250b00721000c00c1c2441040c1d281d8500884005a03a526010b1105040c040d400c2a520f40000b495003c14901055008410394801c5a07855100c0304203940d21500143d00a1400101c240e400000400c44400040c20038000d500c007180080000c4011b1484960014071180035448201e9072000c0f0309190740c020a0180e01a801101b86540b07011160204140b82c11101d0703c250381d22142408404109201803000103401c24130300642041c2c007641c00d000003c0000000d46004810262010414490400d205035080e08010901c2000012005100d4802001c60003142c410780320a90b812139881000701d00704803081c0041801007545d55004283d9051212032840001c0b00078246100b126400a40c110404850400b82c4251400c0451110008030600c1c050148201b07044910000040d600750306034101094183c2000010000200154100b50303181d01031282c140300192050b01d040c45805643d11001c00700b00201c00d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 686750647 1250 686749397 686749411
    0xb0109110d0906090611040503120918070504030b160c02040b01020f03070305030105090a090213020c121207080a0c090e041106071214030606121005030715021207020a150314 77
    0xd05040e417401d041e422280c04a0120400600800c03040043d96000100c0d11000050b80c07290960703d00904001070500409220440b100503880400c00850b160440058400c030b03802441682c91a81da26155030103510200c1940c0c80c04580d40200080c050b0400b81d014284808040c01185c80050540800030325613000018101c000a400100500003800c181c40c081d50084903640d424401e800403640040c00c03800e510103585c03410701d030f010500310800881000b00048065201403050782d03c0c17401c0c268481020130100c42800221b14541c3c00700e00c142040780f080e443c0c1d00801e65640a100740c10403154106c01c0d040988151020f0624888107442035480400601004d403003458800b40e003800c160405082e820740004500700008060041103103075121903045840224a80041d848a80c1d1000200c12600d407198000e00c2d014401c4a60108600700b0140490300c01030059000c6640c6003880b0018040701f0322601030002d41101c180b9008020300001400bc00003047d806040c04110b01d40030503000280342d1411100c0d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 686751897 1250 686750647 686750651
    0x40627031b080a1202040506030f0403020114010803270a0602160e0f040b090f0604050708010b09040c0618030818101d0f03030d06030b180a0b0109110d0906 69
    0x81019002056401030344074480d408080640d154076100030b24018600038205201948081098101d05039045801810000b8115501d81c14030900940044804840c08c13001b42d031801903000210f0354802c071170a0480c0c03990300003989400d240102100c01c07030440410000070343d22036044148040da40c500b100000b07010035500404030001c0041c2c4109050030780e03510030f46407414000f040c8070616100a6109600c29000074007084107071600440c0516208820240310800d004100501080040c089154007c5424041c001d024071313a644010022500c0080c1c400404022011004024084c001ca1448030040ca006007000006666a124808150b21000109040b02094a040400351400200142c107040c814600300c4071a00e271000e00e0484028143c3da082d40324801507095101140e9040080302c0c00c541000500744030099807403401c5002c00000fa60300d07104003220049036400614000814011268104058002e140d10f401c0c0c4000c024170b0105181c40d4152810842460070004500807100010710035440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 686753147 1250 686751897 686751971
    0x16020301090b04060c091a070305220302030f03090f120109020307120b0c040522060906170c0411160809060723030405221508150702010204060c0305030406 69
    0x4c40707001c031035001c40c404c424420005000d001484c2c44407803007084d568130006003a0b9140b44e80c2c02c041da2640149450640c160401900000143c2924605642101e02c290f04440b8550504286146c4901801000f03540003840d811012140c1d03c4c11000d20320301c80c2022000040c5003016500401c0c1448202c0e00070000c2030314440c000c0002c02c030461440036409601c01d0840ba0405041100094008031260303501308200889015800c1820980c0e4042401029209000c102c100d5403a44001d01d528007461900f84680100c0b1804451070815014590302d051801d8902850152220392480741050305440580300b001c41841440066211000100741c143d0007814480c0402113141d215042d5901106041480c0340c205010030007468070348202c8400030510441c2800160044030900c0740080c038011a1110507080212400140107034003054081034803aa1070460300700d6644080c07040e400e0340b00e103218030f5000810a80380e001c00310344104040c40c0c20604c180004500306041d41d00120300030300001c1d141807038110fa0303c01d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 686754397 1250 686753147 686753153
    0x2706040302190c0527070e0108060319020909122107230a0201020f13030c060306120b040305091003050907080a080f0705150c0703030501050f0a030816020301090b04 73
    0x1c00c848416021156442c0c0303011691000341d550090720426000707100f4801a510a10308200078181e41c0c40000300310400910381b0160040480004014003404510342c880400e06d50b060108006520524510314900030328150703400e11a00c004002c00401540c0205c0b07410044017082c8030010114091800b100d4140e5500b050a0118000c00250a4805100e0221403012111210b60b14160545011310743d06501c8034840308090f80a4410030407a0528107000041c2001d442d030f030840080c03094a010302c2d031030880c0079140c840940031140280565081510b1003440d4000051403010b16980c894402c0c5841c0c2c0c1403012407808554031300c0c00e42c4004404261510308202c0030110400800000b00401002440d00c0100354680346824031030000751190300702e000030b012010300c00b080200141081e0b003980c072010107282a0070348404982240c3d400b1000241040300004030740c07800090000903100014149446580745d983e921510307521024161643d1405c009410300542c4d0207101d518105406503203011090b103400c0c6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 686755647 1250 686754397 686754403
    0x70b010608070f030b04140f100503060903071b03020409140633030c030607111c0e010806041e0218090103030807080702010603080f0c010608030f0f032706040302 72
    0x1800c01030802a0303003020000200d62082c1107041400103402e002134240751104c042000b402c02e50320216402031203071040c081c0354507904d01c4803803046008060108216440b0010580c81e080143d42c2d070f4490b80e105015400100f4225005056484208039084141903034943c04a401d070b91500c0e10070340786c80800d20780d6003487d04001e1014560240708a40800502c0072000700320601043c010581d204105a418000401a1400c21145001500c001c2c1252114681100000d11402c843c00d4404401d00aa8680d46030302800b000058024144a841e030040c200303070707220044a481200416055020741c507000d65840807480440c0b00c6289001d000300c09a510303160200340c07607080c00c001d00c2c4203405844800010000700c1d5000b029560804a2450f003044940c80c1c404080340903210b2a00b02800443c000a00044114286d4006140702c12240d4001d001c15680c400c0c65649a001f604d0034101e0380070042107140405074080c00255844001c21100ca500e8944401900c0107075400c40d040200e042e0b0242060000341a010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 686756897 1250 686755647 686755649
    0x80109060b04020405011209081e0c010605010512011e0b220b040503060606071a0a06140406150e06070501050c030106230405010c140a050601170c0f06130306020a0302070b01 77
    0x6842c25840c19142400003884070014600b5a0301107596a0000c80400c84c4100840c0c0d84031120b4140f02c0042e82020003401055484403800d001c0035032034200c0003e0b06501880684101e1032a81d40880a81c0e80b0703250440c901080703140c1c075140440c02c25680201d0200d038450301400d80004d0304489001205101100b001800c0010b80060b20a070b8818001000076685c00190340740c0c4404246d03482d5443d1202071030704040c034205031200d102c0c10b060040704010343c04181c1d60050086031aa204000300c244842c0c01031004503409802422101c040c100709001c4514007401e006002400e000c0c000520380101501c820742142c00584401c00d6151000004010050b88420407102c0803103442c0003a020000005005685807140b4484c0340c3c148a080d210100600c1200620030002061050075039181c1e42c01c1f49040da4070341c90240501b8018854114041c08805400641b207241104060031181800034220100300554102010005950080c0200400011410b002070700c0c2c4440300751400760b01c400e614900507600c0401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 686758147 1250 686756897 686756899
    0x2010609090507170304031730010302091302040906050a050915011a0d090339080d021306030213050d0203060435090a060e03030301060f0e0a080109060b 68
    0x5241c81d03403020030004940e030801c0360420b041e480c590040d4001c40c24198011580b0107032000201e00c00000415002800034007003406100b031500304d408ea100031600440c9902e80b4041c14034040c510010b000509200030300030307045071001240c1450617038190700040549078840001c4407140d44920070310100d040c0c14024207400038000703000f5200c5141c0c40c0c10603034500348052203004d00074000703090a88510104202100c0c6450100c940a001465480c280600000403aa241c18130285002d240740d82d80010810860408145507841c00140300036a4031241e140390080e07941614582d900708644082c51a851a0000c02407040342c60240c1c544a15000c43e411505043d030000380100c4843e4400001a13601050081d4003d41c011540000481003040340c1c0000d1840f1520a41c1c2080038144400000468030080c1c9580700341242d49000b0703103465070011640400b07459104d80c0c06501c144014403282d40280c0809461200a241c8079819000f100c00081040740326502074010b41e5900c0c071440c400e01642d0f004040c0420701c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 686759397 1250 686758147 686758151
    0x20307080f0303040b060a050621060405011802091810030b0603030f03010506030403030e0303010605270609090c131502151b0d090503030f061c0b0a0b010c050a050d02010609 77
    0x61102081e0320ba20000700000e100002c0c100010b25940d41d18040038001e001301400d019261a0f020800c0c5120900c5428281c514000c0301c400280310b03103014001c040c103030380428130701402414a01144101035000420001e90041d950040d41041c1c5070100d900922605e80c0c50304014000e803440c02d1400c40400d002d4510f03070007a0000c015114400003c1c000b141d0444006940031a03a0340d80b182012401019040000300d058040000001092030344000076003030a511862032842c1c10007001c1131a582d916002018a90400740500c20303481a46001c910181d803100c20310b0780043c40c1242c405041903030b0f4203542c0c000700b880101c00155074078090b90420110400c2c440b10b89804070181440141840d038a00c40d05000c1c04135001c00074a40c80045c1d41600504d6850360310000f140e4803403c0c80948592004d07021030710503001d110b10b148640322001120100194158014412220a07100c183c2c1000161001196031410f1003000035541000030001c110505549000310040c0c040c007114440001d0031f43e80340c2c1e405840214 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 686760647 1250 686759397 686759413
    0x801090c0c0308091c020615040207050c24031014030c31050108241506030a020f18040510080712060e030406030204080115031a2205030702030708 65
    0x66000302001d00c01507003508100344182d546000951a14a404490304540c203000340944c1d004940000b41b107800313140f540c031299580114a2003800103d01440c0c40290203540f00051900e020b081000f00392502881490100c005095a030714800110341c400d50ba40310100d0300c5140100040c15803587c0740140303400114007611842c40803800140081d0382c004030341c0780f8801102c0903040d07501400c0e2500c0383d0300c5411000c00340200e6079580b46094030340d1410806400669a410341c00e685080c8451020361151121400407120000d03a4003e2007001d420040140689a80c20003079010310040442c040c00c080c0510b9065024034031034900074801980e00c081c4c22022100b8010744140500f5401251060035941808075a080940aa041420240c01580b1001415000008010070f2043d8540c0040c0b05982c03100b4000d120703da21881403051501e01c03912003e00320b40710303480740e5076106109554503642181c400388151441300d00e49035500121141c1e0040881c0c0542c40000c0359402c41c14203110280080c00c1c02d1020341000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 686761897 1250 686760647 686760671
    0xa080f10050d06050a0b0d0c0f1208040b090d0609060209010314090a020d020415030c1719030e18070e03100e03070807060e03030a0624050a0315030605090102030601080109 76
    0x31107410000038040f03030300d5400041058449a00c524117095000380354a5171a249400c014405062500400d0300a0f507480301e02051158a0000103100540c0c03102c0ca00d440c1c1481c0c82003d030352035049800455846041c0c0d13562000800c043c5c0c0102c000b90740c00b400c0016902c0420100140454503104500800d000000d0100400e5540215103d880740d40c0503201450000014030004006005904c000c5542d2031607000c02000707200502c0703084010740e40c0c0e001c2c03841c0740003840141703a5544100c204042400e00c2c2e2a50a80000a485140754184106016019000c10101504103428000f400c4030003000150b5400d102c010140b0b41041032001d01141c0c0ea0301001020b11488040e6124400e201024280140000b98501040f0301c503031042281c212442d06807034a03810030729040c0000d03002e01d104000d02c041d044400d4046a0f0781e440c418105110f03c507218a40740004541c0d098001c0e00c007180380138030140d1010038000041400c0740070b0148610400c800042c2d492500300005040400183c00011585140910801003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 686763147 1250 686761897 686761909
    0x1e15030706030f14072001020306090105011b060507031b05040b0f071a0103030c0309060e1011010623010f050f09150408030703021513020d0b090309060a080f1005 72
    0x1070300d019190210f440c1ca04048104094180000c002e41d500c846081049420341d401071003510440304151883d1440400a41d0301c0b400d0b0700096032501d41c81003840004115a6000310301e2416000c0108003103603901c0c10b030303612140d0440c0c030110382c1000405e4448000f600c006c440241002e0b90f501d0030b810102d08082c10400c0c001c0d51383c010400d4248610710001042c00502014281840c0d01000c2c0d5003036040300c0d43e103a00d80105070065501080340414904e20740801c10764050085440d810703e0141c00c103800405142000c035045030090740032400c60756031640f0103d00442c6034089a442c0080c524151070b41c1d40c940c0d1000404600c42c42c107180d0100181803090101d00720120703040b10641c00e8210341512003804045a1415588160b03880440305100001d0760303104043c0c0115815091b904a14a2180540e4440340b1211744174000302c4c1e00941c48a1a6611000090b40700d21219400c032000704c0c120707420030b840f00d00130419035440140c900012821290400041c101c0d0203101c0b513401100024202805460000400c003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 686764397 1250 686763147 686763149
    0x20726040308030c03060f0a03110a090203090a230d020307140102040f1505040b07140708370b0c030901050924040f15020d0e0a0308060d0302070302091e150307 71
    0x3018a070000101e00c0659522040c00c0001f000107003030703c0340c2581d0ba00d0000c00003106012428090041c03010002000e0707840e07100760381c801e0311694060640006696151094044415035915015181c0b140035044d41d4000c214a00240d240c90b00150390351301c12410f14101800541c00b05007040ea004100174040d44455042ca00c089406402d0004a4a4403058043c1e0b603a0041341c03c040501c001c042039400611480342e044640f41003070740c016035504540303030891143c8070200407140d03c1100f4140480c442e502222001e0510034111400b00210364401e160f920013540d82c505803a85c8582160101c24401845001e2107003139048146100100758003007030700b6030ba00306100c01020808078149102d00068180500b40c1c1074074006581c84965241d40c00041d050110003500071000369400345103007400c400804040001d5203410b80307070152100340c0c443d070710f900130071036904a95a0200c085000b21100007005071039099005020310b11390111036010140c401b07040c450038107008202110550700040380d060151400700701e20b4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 686765647 1250 686764397 686764411
    0x603060403021c140a03021b06060901050609040f0e0a0b010e13060504080c010501080d0212090a030f02030a0602030a06030308061918020714060f010e011406030a090602072604030803 81
    0x280c007070324180f102507070301e6007080b41d10902c0244000707581c048aa0b410341c01010039003d0703880c0307102d01036000d07594403a604c0200b00c402c1500000240e005120918209010300540d03c3c0091020400e954180710704816181d01c845016150b81c000311400c0c040042e02084a400760121a00201705803500440480c50a0400038014001c1a96200898240518a421100c82800307240003402156540e03420a07075600703080c041e0341c0c0060055141d010301e0307800c60500721960070701d0041c02d501e00541161a00400d000425204980c50302c5110030b40000661940041c0d446a070600c81d000030120301c0c6050180804c0300c014184c034400e0302c042000c014032006c102081d034241c848800240c02c14412880041d002072282e104080c092440358038081e1224100001c005216803205640411aa42d80703045081460b007003806200c50500b10301909800c10704140000c0c46d80314000d070001044010aa80ba200100e900001c01075900a048034407942c42c0080c1609401407481c202c56265160030720390345409030240006403141d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 686766897 1250 686765647 686765683
    0xa02030a1b0b09100e031206040c0207120308061003020f07030c0507170109110603010605040315020708030411101b063c0522060b04060f1706060306040302 69
    0x811801c40e445518808260740c0800ca110b1281000d0010903079460700c1d4040080c601d82000d80003000349601105644210b0240310071801c10340c60f40010000a05401030320241148154040000d0b00020b2030744048486003e506c2c0c0c1107080c10f150702403000346803602e020314084c0350042245520022002c0d040700c000b81d805140c044d206500380c0c45c200e0304082566028002e180c1d50141c2c602103504040d403002c8403103403040c404151442e1120050002d0b6010034810741010800078401000400d450035803c00514002020040c90b004042e5144c00040e08156004d80d213014512400c41e440d0300f030840c0e42c0003a202da20b040c0700e0400c0141c00709403064611005001010a0b848540e421f4103088101c200c80c1c8040140c01507003404505418460134040d0700c540d20308452505100200d12000c14100d00005801034040b0200c1004200341c0b20305001d0007035070b04d516420a98640c00002d0b510b55020075000074180240f000b2045110310003aa41c0340510250143e8400e030008014040022b0700013500c50100c41e505929 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 686768147 1250 686766897 686766917
    0x70f08210a0e0d0b01141314070507061103040c1d0402090c280503161b060209010e10020706030b0a1410050d06120b010e090d0305060d02030a15110a02030a 69
    0x1103503880181d82001400701e050240041581c00c454030800ca80b514090794841582c0c9400700207801948d4403010001107003242c410120388210311031401000c840e03004940c0031840b5031071410000e001d036104179020340da21072418000340b140c0361008c0b07901012460080001549810150001171807104042c00005001b00006450051181117600910114840000070b08102d0b00b03000016009378022999114454031030054809564040d1010b0448440b020501c01e010085a5403108001e621801e25181480701c00490142d699a800d030485c45040f40c1c0e5030140c01101d1130071030040c0568040400c05842180b00420a0110310822098032084480c225070f0032011000b0300380c050300c0d00c2c480c0b4400c007114035041ca0b07800b050b460080d01c0ea04800d90f2052880f000ea07aa66a404506661010f0b60b01401e95000b020300410300b28400e0708020303000328004180c00d40c012101c2d80043c1c03030641b90100846071015184950000500316100c4c200c0c4040d22005114509007000300000d441c3c0c452184901705010003888 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 686769397 1250 686768147 686768149
    0x70f03020c150c0c120c0a03120b030319020105160507020405070504120b060a0b0c101e0903021b01090b071e020406090905100b030a14030705070f08210a0e 69
    0x41001d10181e840b2402000c80d041142e00340310039901c002c240c03203110700c130340d5590403190344a020032101000000000b4000d12161075030111810015010f9001c0b0321a240c0c5248410340c3e03401d00007007002d000d09044203a805c0c040c2810207400e60784001e0610103400102400c008005800c076045500c0700782d048400040d9543ea55005841d00d008540000016100f50000c01c002c1100303071603006008480031500d08044c0d80c0e031503a000c50248107072040310b41c4642010150103040305e0329030002e00e140399041740e0300d0041d62902440d01c1d0446401e42d5003a0016809403003843d40c03000400e50700c0c2d02140e0b400c1ca05504418203120690459100700e40004014810000d580c11400c09001050498258020414403145542ea80c1d00000741080358002e8483d40a000c0a0703070f908049502c21250101d0380980502058502c0b0b0302c0b0000350b4284c50881e1210b41c04100007500000300103128040190410081d504480c2e410b100380c0600d001984080441c1e202c41c40141c00c5514003088050316111012403034282c11a003d010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 686770647 1250 686769397 686769403
    0x10060821131a18060306150a020c040c020d0e060306010906080a09240f050402030c1e0d301709010b0a0303030506010e0321220b130e070f03020c 64
    0x2d84544000364200c1a41402d080e800401054062503910341098800107502c108103241c48265a025800080502108099140c1e000685400303080f074015510501d01c007201107029038925219401c01a08845071102070103411003284010854180c4d00e540c21031814400281100d189400303840b040c8981c520014070810400c0c4c1040400591140500b46030b0102c079035516000d43d0740600d401044504040214030081910b01c5401d00c25a00113009006805000090201664910300300e50208592210303240c00750749500307200150040c441d41100c400000140707904004403400740115280c145182070075102c5a0340c030040300c00700340055109415041c0c0b60554a54010b0005820683e006800303c1b200000345a01075202c1032044900380c03200b0070b003111480e04054448803029000c810b60302c4000003680c030700c202010213042400202d820400100c6100810000300c04031651040b0680500003135201e08e40c080d9070b064800240300050a451440c01c0802000d8600c10200880030101a80403481a151440c10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 686771897 1250 686770647 686770649
    0xa0608030705100222081c031811010207030b012408040503120c070f060e060a200d0e0f0a051204030317250914030a08030a05040f020901081006082113 67
    0x1e15141904513075a89800f540701e98210b0740c112607009417030607c040b1180c01f80c06141095440440c44904c09041e40c2e48207205005035200035030441c0709441002c00000d103005101c82c0a45500071501c213556407030840440b503022400e110a01040b1401c0144800100000140c4810490b0a20301c14803956550001441a0081d810060107001c0194124802c1c880c00b6404420b81491000980f01c00f03075900d883d00304c152080e101018102941290000c440000d440780542000b1403408404a20000c46614462801d082d03015600403582200f040314041200801c09280e1401e800c840c4c0c5402c291031614003410103076104d5040e850006147c80005c02d106405486800b510100c004078184000070719000400251150060315441e03544804000c850f480c1c0000d0500301c0e582e10090091460b9695000c030f1001d00005071048ad14408270381100d100503950804010b0180c4183e074001d204141c3e58035414400da90456020703040c1c5400c5403c0e0700c00d41c0e450700030040c188200818402a50f4040b210f44c1c5116a03101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 686773147 1250 686771897 686771947
    0xc03151211061207020d0203041211060903010e030d0c0e1509040f05011d0604050c09100c05010f02072109060e0d05120405090903090604050d02190306050a06080307051002 76
    0x400206880f501008140942c125508032510184900001c0e6a680704138000d07014009511543e98000800c03140350190b01000c0645001d007090806400f1909594032035000c00240d07000420b20600b4403282e8423800454080500d4071003800c12904003c0344c03041d804980d600b000d1030b2000130412a151519081800203400210b020011581d603403103605010340514252101d401340c0314010920303500d0180942c2e03003d4403039100e65902e004404401c1007410034041390481d05000101c02280b000c12801e00c1001c103960043c1c40050f82d45c00c00c0d89000c60085070440c0042100d040c1c0c400341d0516059100100500380d40c0d0070700348080e5000d4010f000030540095000c0c000d216108000c010321f401c0421030050422640c0568040380c0c0c0b901d5607100c06880780251003015401c42010300c400c110764949010580347e61800a88508941490b660a28800c24150740040d01d030592900184400d0301340910400e001001c1010181d410180c143c0d642d1900c604114000b960f01640101e041c00102046108420011007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 686774397 1250 686773147 686773159
    0x3011707050a0e1e090304050a0509150d030c08030408131d01030816050106090621030f0e0103060b0316021e070308130b071b0509160c0804210203010c03151211 71
    0x2174000051035880c0e001d03014280c0035009000001565080002c042070007250200843d01e1440109020700144400200c1c4c01e0b0200b211a860501c08140780e04011070045010343c07940c598841c0e50030b680d004d6442030b545c4626541c81902a18115808050003d141501c0d44a00900d0b91512a64010300074498a42e0b00507000d035203090000608126164880d00468444403c08181c0780e400c10040310350601c3d18100503022075504400c00400074820b046200074458141000a1810380310004d10b1400d0704222621900d01d24008060010f1a804002600c2400c00120424148405042d10b8039141e83e424400204002c0d008103490880c1c0861032500700141400010b0540c0b40c0c1102c3c2031940c02009200504081e0001240010886051890a0b14400c0302035000c0c0960070006a2400c407140ea0101200f034880032800d11000c102d06101c810280090342d1701219521103012a40101805c403070180c078003503042c180780101c2d03111441d10040400c0212241a440b1060982c90b9081012041c828024060381c022 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 686775647 1250 686774397 686774401
    0x5030a032d050103410a0b070e12010c09140a09020f120105091b0306030f06070905033c010e0a0b090105062b0c03080403050303011707050a0e1e 64
    0x1c45540814100c0c0d000e41c8025022060001042d9005010700004d2a40110019942c1c000040c2c5400d44244441400d02202c4000300d95403100021007006858107000100c540566040516080f49450300c105c421a008028040c002030300542040460b02c107503c1000038002c10300b261903540d842040024032807041d09541da040382c100307500059802104400310326403e010000c05c66003888a41544100405e500c44d03214800d40d003003584960f41006044992500c01c10070300717030880ca405001090140026840d000c0001c0d040ca0308040c10001e054100d0700300401213069189410203021000c00302d190301040b2840c0580030040069003d49a880c605008505c10200d2141c01c03c41c090355060311420401c40200100e848030f008000326180d498419900303003414bd0b00410840c2030500303016204542310f0345a01d400d03076683e0b80c1c1c0c0240310b41140d071007903409800c0803004229174090760448201d001094005050254145000100c01001500400481d11810340c00100e40c002c1c01e01e030501d4446580e1011681034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 686776897 1250 686775647 686775731
    0xe07180606140a0f0c110a151101150b0a140a020c0114160809060c0613060605100c0308071b0615090213210f03050307020c0a0305030a03 61
    0xa8a014462400018240d0608910015540068030000d4149031389103400342c00b012800302e900034225081075904104004403040310750b4a0450b004010a0107054078081075680c2d0300082d1400c0f000761000c0c5c0c5140d0415441d04481c400029008040c7e480180c7d469884800841341104e6540d24032480340e0701c8032800180c0f17000c8980c001484509588090b80d881185070b03901100c465960140b60400c40400f440300c14030600040e08607000c0c015480300a00101c4c01c004001084901d0044103032100004103d242010000f440410300504c40604010303144100a070140740002018590105000781c01c01c2135960101e11503e10824144170501d603000742c00950811f060508000502d40c1c00300c0c0064103144010006080f501307a0003996688c1b9841c0c10380700641e074549002c500d00c203020340c0d00f210020712000d100c403000141421a440c0000303000ea50781546078540008064909032500b603d071889045801810000200004200c0314054818a80800c1c07401d480c2c0c003030451241c0344200e0740b0000ca500c3c00505200c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 686778147 1250 686776897 686776901
    0x2b0b0405120f0d05090313060e0a05062107030605090c13060e1315080114040b09011a010e120d030c02071208040b0f090604090f0518100e0718 63
    0x5a806501915a010350301041101103200e1181a0000b00d0824072100c0b502a403281d1040d91302919000a0340d10b005035002c22075003117141c3d981000c0f01190344040c10328400d003031150042c1d015040c295401031401c02c4420490844100000550b0074190000e80007500d014800d0700820020100580015461705012034070b1215500800e0079503440924258000445070712500c650301d580a0050082001090217011610160000c51500d650031006000001801ea07024410313280c0c0c05140315203035441d0742490f01c0c02a52a110141103007403168100700c0500081102d0529120542d0800d0070407174005004200440c48400b8401d0a0744c110b0702480040a8007103415410042c8140c19903401d0761040da0311011440003203840020040d0001506100900441c036203140100300703a8000c1e07101c2c9820300808500049803580070750050340400f510f43c29110444c0d00c042c0a165081411031421032000700c1700c011159031301d200d5000c42140960701c0d0801c00207121014041c4001034404558248048012070040e000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 686779397 1250 686778147 686778151
    0xf1201060504030b0f010608070c0c030c0602060115091401080a0f09050f19080d0504051906060f060e18070908160f0b12190e2b110a022b0b 62
    0x894013000c800040215012200c4103058680c0398075030844a40340d00c02c0403076400040d50411074a00040c200302002181d1400040c00003050710760300038180b540c100b6850200755000c20083d0400c0c80340740318040c042110b0324080c0380da1a08080c80c1420340c0d0303902c041004018000044120b2403079403905210f501401004101440000100400c640c00c0711484c000d017409820003076601500c0300c00c0500a01103400982e41149400900030300c110f400802d5001910011100104001c45007255a41410000901e0b29a020340040c0307243e00b0510900803c2d800400c1200039903504050b07540711250009881c0500440b4250050460310007162030b175030040c0a844072001700a002d000501c1303007080030010b50707104003100710382d0000c4080c01c16006030340700c140003114580700c04003a80c1400c43d00c40c102002c824504002c500340035800c50000c5200007400701c5400c41042d540045841c10054148401d4909240000f030031060300d81e06850038240728110307a1801f1020078218602c51010010720700c0c00f4061024049440d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 686780647 1250 686779397 686779403
    0x100b01030f05090c042d020a020c0319210206060111010213060509150307050a110111160b01080c0f01050711120307030215040b040201230406020f0f0118080f120106050403 76
    0x40051b0700b40c0360040c080d40440350b406a0395103855404041259003500585000d802c1030044031750f0b08241100080c103249600350801054503940c040f0909026030700d4994240700109100029071607400500013525800c0050a003814001c0c0c601c400f502c5901c0035030445401040d10040042c00c2612080010650b521001d0201c1c40340d40c0c1580368950050414040300c1c0985069102c0b145080040041a114111703080c0b02050302d55030395052111403419400080004501d006074030400f4603094a003101b0b40344010380040300030364002c1c01c250206444001c0040d60741321302400c02648070391492034a482e007034900c20000c5400c1003401504e03514401d00003010f0400e041c0720390241c40c0c400519540e0041244005c9602602c002045e0b404030740954058008810512032040c9602c98a04140403c000c0c17a900c903030b100c0340040c1e01503c3c0520302803405100d0150300d601180024054209071100081d040d040c01400036004040c0040d12186400b12070084070840c1d804000d168001d5030759010082c002c1d400c10305c420703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 686781897 1250 686780647 686780651
    0x11041a2d0c010f230c210601030f05100b0f0f041d15061b10140a060e0c03070302090a0315020a0f2f03070501090c26100b01030f05090c04 61
    0x3d507020541401a01200b4000100500707a682c0800c0700709101820203402c0520001c4c0c104103206104464500c642001e0813000810306050a1050004086070601c0c14080001c614000078040e4592800c10f1341000c407544003010548928140c0044549032051100600459400080000b000013041a103914103a0748800341a8071580c2c1d0f841010300c2000c030ba4018550100781000790380104403000d10781303400d00c040b50000c40300e1001c1c281d07909070119003a1840200d15000c2100402006050700c1c06a10080e20341c11540300c0c664240615048458000070b08500c2c140754011950129580b159000000215046010b2041c1c0350104005080298021003a03400000d072040340a1703002074040c803080c071030320a207040070150010541003041102e443c101000c8030785030000b088980041002400703412803103809401120725403840d01080d0800c0300c0c50307101200900d02400042070682d81c404a000031105007848000b28009005c0c0004800400c01101c6c120701d502d04d42401d11104040000f01398a0a080966003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 686783147 1250 686781897 686781911
    0x3131d07080702121b160512030903060a02032a130b0406020d0f180806010503070e07020312060d020d14070b0429040b03011811041a2d0c01 62
    0x3100e45080444045016900009020f02d02403074050080101c142c104240f1452251002129820070701d000000203606e4044110601040c5800c0d50031030f1508904a0003186065020b1011944964000305807130001e0742d020000400141410200c0044c40d840c0341c010703d941c1c104102c1c00000c1034001c40250444410803840103d1104100ca04680c152440e81d0020400c141104500701d031810214401d11041103504009208030000c840c1041002d0314107107001c0c0400d98145424149444030302c1d40301c200818800d00600422540200444410402c403100c9080250368260114100c4a602e010081d001407464048a051000c0f6424480c0c46c120310034181c80080b655005816168003032070084681140007015214044c010340c40b021050461818503140c1095a61190012950000d0b404980d0000098142c0d04899030b080c0300300ba48101c5a4500340b0300702418080b001040340110514a4103801c0d000030113442c1c440c0e880f25109a0112496601080124421045c000603041443c88204560038007034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 686784397 1250 686783147 686783161
    0x121006030b090c0d0b090a0c120c1b030c080d05060909060403120f0e0a0309050102060f011203111e1e1c0305040215040b040e1e0c030903131d 63
    0x140741110300c0300600c0a40c0e15218820380c1d07001a4880040d514426a03540c001c0390413600d403894010310501003c403000030340003074035200606840031400a0400041c030b40005001e00c81d411500b928848041c614030700844110516058078180e06102d4050140c4001280f030449441da1b542015100c0e04d8151807131802a15541e805903640c5001340c0e0000d0103e9068040c08088560f95400003078640101080426444103045415051000c140810380008074940400c1c002540c042040580040007102c0890182d0b141c040c00b91400c0003030050090802c1300546001d210840d08024007031003401000140001180304c41070f45691103c254403c0082d00e15404904044610301292010840c050011083d00a2554800440007804010422a40305102801500345500c1711000780010709407030191240e490742003001102c0d400d24000c250042c5814400592200c02e0b15540b00c0c5500090116081612a00c400901c40d04500810103001300c1071003550790003d0001c038140d4908910012014804040d03841da02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 686785647 1250 686784397 686784401
    0x150702030a110a030b09030a0201270210030b040216031407030e0420030705090427030c062009040c110715121113050301020405010e121212100603 65
    0x105019605400000251011038919104005841002014980710070344980d103030b400b1618140c420189543c40031403070028454091007211030b840492030910010700980194841e66841010000340590403441c00c240410303000c0e410107003000200600c15500e038005030700c01c40410003086e0015400241f04040319081030b20b00504440c550340c0c240e81c801089101400c10300014200d04055022020840c401800c0321180400c040c500408030f41d981c656840070100b00308420b85140d10030200401d100721101e00e55250f020440400010341c1410500c006200350b05024006001440065416444861815003800014001046520000c44041100d0850310388221a40440b110351101305a20800040c08440c400380c80424100c501d80c68043c2895040303032242002e8648000c100b040c00d150216801c401058080b043c1d0000d010298004c500713261410300002c040001d1241d0302c50154038114608500c2150501c0041c090306010303552207580e05c1c80c0145074103600c030003159a101059242d12010800c90711134 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 686786897 1250 686785647 686785657
    0x810020c1534170c04031e120203040b12070c02041a2b0f17070c05090718060e040f060e0f09010c05090906040209150c1014011a0c01021815 62
    0xda41c0d59070440300364106000500b480505500704d104000c0c0000070010b25801541410348070320030000c0351425000e29110f243d0348201841032065400a1006000d00401a4207644510131802e044905075212480c0c04d440075080305c10041d4029083c4001c50302d08500e42c002c80001400143c0e01c91510b101040e0f1006680e5000c0c0c2081c189018024003200041803608103e07107002800340021203c60350180012082640c01503808858100008808005030710f8401c808a52000171400c04440d020129006040c404005002d1303481407105d20082e92030141c449a1181040b100505400c00c02070b030325003640500e070410481e14000c000000c4000036000c1241801180c1c7c8101c0c04c0d447e41c1d41020000300c104203c5070401002542c005509100302c1c06165521200245040403c418955640420350015820101c000024100b040e0401d20220009140c01080300e0450b40c3c41b00080c401c4910091005c80b440c896101d804103150700200f44005081580101c004e480e44040f50b81e031a8402848061628038010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 686788147 1250 686786897 686787001
    0x211b060c0c0d03051c0b10030510170307080c030c0d02160605031e07030506030c0d11090601170f162a0c080102121806010810020c15 59
    0x75000001060909201840c003561003070030641c3c1407184001010750704464603600a400d058035883d045043d07041000360300100c03508916090246203040c0c0000c510f00001c40c4507144c208c140e0340f0b00e04185104148281c80070395a100e805180d444292220440da65008400f00382218003610a007420b42c680000390040101c0d6170695000d0381603103418010b40301078100500d2920716107114151898844a0502c17843c0c45107400303450004541c02c1100515240241171848180503515004110b80440c0c1142c00c0580a800c003100d000c0050303528000120b4142100314036a0410070104024400c0c080c100c4c40d0241d01c200380e50110b041c0300c3d03c800341c030031100c900d00d0303d1a1801009240c0d00a0b1301c24038400313211721481806400c0d000440c42e9210281801ca03440f00208600541100045c003034189011601c0c062203550010003041c031941400002070f2111000703031420000550000b1924081c0205103c0d00c0d21100c8400010030161030442000e080c0404212089050390170455000e1507840ca081c54a004002c01c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 686789397 1250 686788147 686788153
    0x9030f0123070917010f090503120a231305070e042a0e07090308040801020a181508150a03080306010315060e040b060d05040606051c02010507030e211b060c 69
    0x40f40c4504d003003854400d2040c002c800e5480d2010905020103038003032100c42e45d2060b0000d581e01d5081650500c0c5c560009040d0f080d509003441e404103e071400740224902c42102040311030350192941c3d9000a280c24850b40014014040c2c01c80c001341007038010340d116200e10b0203a000c0f5404c030040f000c05580d003101c50851960800c0d140d10414805808481d000641c05600ca003050052a9243d4442803500d4101e42e0080500b41e4000034502641a0300800400f040c904520103800349505100510f40494000b8140c1e034100551000001d50700f1404811030225400050091400c668580c105001960700442d41c50380440d0a205041d26881d041e100c900381228050340c0c582003000d0105d402c11006c0c009600c1d440e82d2203a030600200300040b0886c0318160082c0d1140b140001c086151905110381600048111801c0c10500039082c405130760020102d40185034140b07000040e9242d02400280708602c0c082141c4400118024800000907002400c9241c010308128501400e492003800c1207014030800c400521150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 686790647 1250 686789397 686789399
    0x8160b070f0f02030f01050f0709080102040f050105030402011e0309030f17162604030f08190902041b020c09060d050a02060c250f05010327020609030f01230709 71
    0x9001d4498940c03843d10003402e460780e49001e00307555030035076200707460300c424503100b52050140303050300303c0c5402004002400083d42420b01d098404c6443c80e600c1d214079810301c103001001400316845203070003003880d44080f00700c507040c0c0150400c01001401c0121080300440d00d10325060460170301410b034041ca5002070840c04c807003e0b40d40c3c100380310030309007000d80c3c010500600049660101040e851020a00d087e02c3ca510071040c5000d080c014146c8600000030001c1c015281309010010040400881c0c45034941840440c0304d45607072010400801056842c00250b038890803440c40110380c0418101d40c42041240d0b11a4140c42d200d00300b01051009110007400c95100103284401400e0003400f614600c040c1000384c1e028000c00c40b00041d8110340d580c0d5a030305405003501e000d000d5401702c01c40c050045c2c9020710382081400c051f070307a440110300d4001d840d2042c2800c0d003015003811540e03410101c1e0020140038081d02c89440c05204c1c1d2601800c805061410010b0b18455060455180082401d1084010f69140e0201c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 686791897 1250 686790647 686790653
    0xe030306040e0f0f1b01030e0601090c0c061109090f010b07030309020d0c0303020d0305010b030c04060e03070308040609050a120305070209071707200105060f040e031308160b070f 79
    0x500410442c2e0010703000c0c0d00b080100120080c421655500c2010b40a011483d060062840215004811490505180505006d03c54000050f0207054400260000601d59010241601c3c119543d540092001d42400c0c80074040074120800b030684413009403040848c42d196110100e1b01c541c0c00340140c12500d41c0a000724404070b40700b0f07000483c80c1ca0015120b800304035840d49450341c81c50815042600982d01c40303220083c085505200701c0b030052283c9407820307056003481d800140c41e0341320380c1c0310b80d00400425204040c0e16907002d0103850b000f150301520040d6900c7c0d851202800c1700b207452003420b214a02d02900002c0440f0718140700c41c0c0d0b055066031140c0c5880c42a508100d84180007074020b20030000d4000c0d03050920580f0001580c0946002d440303d08017010f2800b20320300f00541d0a0300c800c0203641010180180c0d07458412894090f04011a0301080300c0349030382096440c0d03024190900103c0c100c00400000c82c0900072801211310200c600c4c42510098803410303144102d1248020040503450144101004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 686793147 1250 686791897 686791901
    0x20c040c0806310203010302030d0f020a02010c05101407230a050318070303030212070c11041a09010f05100507030e06030a02091e04230a0506210c040605040e03030604 74
    0x41c4603500c03840d00140300420f00c40e460b440221009000b83c0c20b07800801801585000c10010b0440c01c0207140034680210360210080d240c1d600f0101c02418007a0f9041d8487c100f000500860809102420040086094182100300341c0b81c419a643e00101e03919009045542007005030440d03044645200705440d0088410742121aa803000300040700c100c40c02112a03903c00780a01c800d0000f94000e990258652191002103840190090600700a10129020010020300607072070a5071b014208840001d112954400101030904a41d0a45a03000d140903001060702ca0562802d403090700d505460801111b081c610050b1528440d07158003401041110040b0360307080c6481c3d401560701c80844d620260401c0c803990007003445208140106080c041c00311000320b803981051b1244102102d00ca241030103004510754424050f03020060443e1300e5032a21100002c0543d162580113a1030031304011466048000074103503107500c948406054a01c02c038104440040c4916140c0142c400c9581e40307401462464a41c4420000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 686794397 1250 686793147 686793169
    0x5060a1709070819061802010c020f01051e070605010807210501020702040903080a1415010318051e0d03060f060302090f120307060b0418120207090903050a020c040c0806 75
    0xa441108400304848509001c0e91400d02000d109542e5002c2881c50030b00c0680d6103000082030130300e03880806d0b0800750303a0040307424601c1c0b038050780c660180e10344110040b60f061140000315404045004100d11035420910014103129018050030421a620381c440355445600750711500c24102400302c0d03c07010704100b190b40324000c544503400046c13803c455517011905990b03010109902041980e0304000b000e641034043d0582c00c16860380340354814a4583c9078001d003101c0b603c0003039042550340c6101111825a002c0c0b1600403940117001c607804000318904542078141104500c000394003882e2030410156000f40218800d035240c215590300b80f5828018114003d400c0500051381c4010b016130142d0064a4080e4480d01150a610107103640e00102e003400c070141c882c03124070980102c0c50602c00da100c01050004541005500407020440041d0410049142405079002064039a2520040c08209500540100140e43c429000d07a0164000c8008010850f0340003245c90010580c018001100c524140040e56 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 686795647 1250 686794397 686794411
    0x1415150738010b210c032214030a020f07030803070804060f0f020c0d0203030105060f0a09090c0c030305180706030b01050c07030b0708062e030902130603020a05060a17 74
    0x540c1840400c00302901c1d0100070380c400d000d0001c00003988061034914400034541412624950300c0d560074203400440d050b00c00241000ca480d007a0b0441781902c0b500b00c4054840342d039000f202840c4180d80040b010703a10780d4413588005000d0b110f51960030802a0000c9821011260030200c01c600b1b43d943d0706015103201000500031141e9940c0d44503482604c411520800b02114001007006886850021040c3d1410385020380110a550007440100200d070b4440c0d048460310085450115100c001800c001c0d00c03041e02c0c80e04207500280c24030201046090344802018107060290f903003406540c45524100b0002c8010980206a64020810074403c0a019030480380ea6580180360542c600748003004070320704010880e00b0498030952400c061103215039200640301c1e0480c401312503813690342c250011080b00c2d80c16030121060940c5410210040b441d8029448141074580103000120a0803040c2d01020007400c242c0402c920505c290100410b1504240d01640e50382d43d0640c44420301c0008a00310f400030100f00400603 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 686796897 1250 686795647 686795723
    0x8090a0515061201050f1008010b28080a060b030105070c03080708040302160602160b03070f1107170d021b0105040e1b0c071403030909010e040614151507 68
    0x44084003c2481800e10800c90b094041c40709080a0032002c540d880039510054080c2c4c14421100000c0d03541c441f6078682c40c1c1c02c824071602c3d00d540a04040b14550310590019006000e20304007030381841801e03044618a10f10072070003007000ea80c800780f090700c11602190020b40001c404200007441c450003003402da80c0080c001c2c0110b450041190f2007540035504540c0005005800070110761245100c02c1e800040a0806045450700f03501c0c182d4002090783c2d510990b840c0802c284c01c50300d0211400d0503c03160000d440382608840c403d00442404d9a92900140343c880c0040c825603400c2c0c01c2c16801d100c0101810b03003050b51034919240c5802c3c003103035110901034940b0f202c800721a001c0700750301141500103140300003030320380603201c0b0510300510781c48000c42a0721840e001e42c00c104040340d0141d8800d0811815200c40c41d41003400d9440d00d050160091a48030000c0411040c04814055a40c0b1440d02e18075007980202c1d244150101c240308801d03802c0c0540100240041c03c80c11006404d1400b05800171001c01d604240 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 686798147 1250 686796897 686796919
    0xe100909022118061b090d08040503070f080609060103030e10050d05130201300c0507050a0507090f0e031e1603080402130507080f0a18060203010608090a051506 71
    0x20200300040903510720601d1010300745451840b06050005a50143d40e4407020003582000100001030b1b03200e0310058a200c0c601c507145101c20480f400090b20042d1101034129400f480c0c450600301d4404039280039600e4640328481c00a403032a2000a0b00905030399040c0d840740d02031850f01702444454803d00700345200340700b8203011601071604948500752044480d140c03503610403d914000900100d246410b00d00130010242e04001001170649041d03080f8501ca07400001d00c5520034102210240600314000708140503d85600d01409000100b55040d190603820400c07154100b8140c510448203e181c800c0d4190304244515180b13000500c440415100841c0d082c0c51500c21600002e840000f0385250403004522010103000540c148070280102c145504141040326003012030f0050418030005100c000b00800400001c1c00110301c5403c818a02c01da0040f44400c006e04a2405001940090042c1400030b40b0200015600c0c040006c0c845600a41203000751a140f80700000000924000414243d0060f5000407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 686799397 1250 686798147 686798197
    0xe16050a090317091002030f1801090e19050702070f0b0903010213270b0f0d0302070506070c0915051302090406120501091401020901270e09060103030e10090902 71
    0x1181e0200c2c142c3c10200c0795907403003c00401400c45c3c045c05000c0115401449400c81030f82024040b18694500c0410259121110300700481c4c041100c0c1c0c1224a820443d5814070403500e20012000c901d0070351124003440b0582d10b83d0030032030f5105900e204840803036000d0b007810801d40440100a162a40000d03001501d0034219400000c3c1221071340e880710030500785c50400424402150003112002182d03100084c02161420400a03030703041c00c1a24200e115070901207900003014002c000c000010300c1e01a0072940c50765040c2c00d00a01c840c05d1031041114441c14040c22a4100300941d9440040da240100301000d824000070035034009411201c17400d500a175031510013042154081003003001301c0e80b0407070020804081e0b500d00501004044542d82800e07a006101c500d10980c1c01c1058103050b907010b0500e031003050342441a10851000d0700d520850b5010710003000d009200501081c0c0038103a034080d84070303901e1a0112200340f024180029490500013540888240001d88203a001002c2c000418a00c81d6a888080702c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 686800647 1250 686799397 686799413
    0xd0e030d050d051510110f07240c0b0907080c0306060d0b28020d0c2f03090603040302060132060c0a171c020403020f0d0c0e13020a0e16050a0903 64
    0x6441c1c5c07008280020705a06504d0810003030641c684035000054070724103185c00801021425040041e6108601c001540d4070711502c5202900d540b650003002c6205607050500403140c03201218052144d03907010b10310800445060002d0414042e207030141030301c1d00541094440350519200a400d62103501005892840746960002c28040324501d40074006958050341c07100c2c5000c540b56941041c080c8200b141b03c0409007404840b904000c2d103500c26190a0000c448480a0304610803c1203440c3e01550100601040c15030014401d4140c90810300c085000c190082940c001450049103410208514000c03200f505041031405810024054422501c03005c0b11561000804400343d001c061307081801048c0d41342d10348a6845d01c04413180a4010440c60207080d50080f880c0da5882001440c00340310740e0501c480400c00c2c9c043e010401051202c0340d81c0f64030305060841580e884203440c2c00340e129940244002c14035120001140e806203e0207030b2400c18005c5003100503205a0807889041c0e0621158280000c0815100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 686801897 1250 686800647 686800669
    0x30c2d0a03240501051905040e0a061410050105030c0409111204050c0312040303080a020f09030609060403141207081009060603050406150303080103320d0e030d050d0515 75
    0x8095100b02c209204206482211016882a0300c914400c00c1003660803540d00f07040005445054a0101f0b9410414680c14a48aa10600213052910f40060518401031000ca000d0003100d004d60003c4081c2c0e0799034011134031408152030070992440c0c100004c01c21404164000140d00542803041d03418400001c0e44e400c9132000445054900383c0050607050410b00d0244584181c201c0c00c40409814281591001489100000c0240062560014103461102c03581010340b82c40c0400103044a8040ca00a000e141c1c60b014103170340c100c000c1803046130100d00d25101031042d10501200440c801e0b10325500d0f124201e464440281101c2c0e161031021501103060031072400780340e014288580340802c1c44d00349482c007002210803500030b080311071140c00c00600002e84c0c0012203c1c112a0001c500312100142000c412100758082d8010b5100710302d840980c5103412002080c14000504542c95442a95004070107040c2c40f0b400c1c0c0485c0780300080c000c00c64502074509940c090b641000700c94a85250010451010458041d10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 686803147 1250 686801897 686801933
    0x9020d050f16261903110c04110a03051803041203080117071a09100c060e0d0207151e080f0c0c0a0204020903160303050405030c2d0a03 60
    0x102030900200103508204032086502c2694010b0403041ca088070001002c1c01030140203820b00100c246594807030384100043d10300e0700130441078000512040e01d80503291010045510310540240403400c004c901d841d00c594000320a15484031890004103040460042c08000c060003d03002801e00c03105040034081000e00054080c100030a180c940705401c01400310507050b800000c0d400814070300b03101c500300301180030307412030f580d415407010081900d5038914804e0044101c05034014840420540c145a4050141103681380900c4040019188008105841d0106c1d4041d210140c1d2103640104034600c520f02c0141c00010040c41c2c010360001c25059003e2044036440c82c8080064042c1e810300a00500002d02e40c1c1e006401451160714260001030103a413a0413001102a104903030204248216460500184150113000b40c051002103449140c0a04550840c1c010b20f4041d1081800410300c900b0141c3c59502d00e540519103030059100c8100c010254a5020719a240d00510304a00000c001208004c0c49d80103050 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 686804397 1250 686803147 686803153
    0x9050601080c030102031e0415020a030209010306050609031b01050f040801020406080f01030b01180621050d0c0c031103070302030601080d030c092d0b0a0c0b010b03041a0a09020d05 80
    0x114001c0c200b4075108050080d07511a034410401d0181d04041c52150f20f0750500c010000d04501d0765907080040d01520181c0600101e0f0b400002e910001d40c0d8185d00808045c107090720304110ba55116810f100580c09808252600b66001c0c802454084c0064885140d101c0c0c41458250320386404210290348680042e401460540c0d0041400e0000940001c00c45034040d0300c030034803281039614540300d403e20003a041c800c40300075098201050715403800d1a000707000a011401100d2003d01c841e0451003503a00989041039642d40241c0d0710b03e02500e80b18008410342c45401680c0b0b00c0c40c00d07085468080011041c1400306500d8070401714004016101400030b0350081010501900b01441d0b03100007c1e040d50491501441040341007101803105644081001700c1c0c100203800c04001c90082d84400d201e4420490300070f2501d501d0041503c3c60b100703511000054001d84603146121842c0d9a850810595000603180140076000d1500c80740d8000d0504203046074071510b10344010625042540100d400d620f0b030300c2d5013503884d60 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 686805647 1250 686804397 686804399
    0x619020904090c0312030e03040e1509070c02090109020c1f0f140103140d0912260403061d0c1203090a0b0714070b030a020927100f0609120f0609050601 67
    0x442807a42a80580175a410107016080b044044142c80b403086001e0b4540316000708001c1035070b10b66128003001e51888060030080450520501c09490315a00c00400c0b48650204d00021403520100d0003a20440040000101040760000c9e40e9407510615480e55440d00f01d50303a01d14240300116038014a20300700101d100c504099410740c14600a201808070f4131040e42c1d4031950f550b9600a51018000d400c6681e00300800702190007601c0d041481003105040080d0301c01c01c140062001c860b02030000e0049a100c1c0a0400c03680031404640e4040804400c82d8040c2d0780c00c00c0e0f0151103030f400d00d036800088803003819003030360324041c3c040c0d0000750103002580059848500114007401005800090030f031824514034002c0140300d107400000ca03080c1c840104062082c5070081075400458450321009091004210001507001100c103014005c80d440494040880c1c2e5964000060414281009107091303404c0d550350220b0903810035105d803029005003081201d101281c3c181180100f40e0501c25005c1051003040900425 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 686806897 1250 686805647 686805653
    0x40b0f0a112d0a08071223061305040303020c0f06010515030c07060c02071404020c0a03050d0b0d050604020906090c04090c0908010c0c030801050301020f030112050a02030312071404080619020904090c03 89
    0x5200704901e640e145141900c0e4074140411254041008610740d0300310011643d42d08e002c520300034800b00c600780400782031030144420503070143c0244c2140755450048070441c0d9228449a55119001c0c03082c1030f0000c401c0240005001c0036800216801881030000c586040700c1c959404007200d44450119005030058007040c02003820320810481c440b4400c0301d00307600b0710030020300c05500c2d40d9201400809110001801d403201040c941c100f0b0b0401e04004144e2240c40380e9500b001a1116000ca50403849011342d170000410514042024034000d088009002d800e2600346213451005014145005061000e64200000c100500b40681d00b6010056583d4510058081c030b4060080300381030b00080d1081e4014000240d1800510050380d0456448074060121141503050444c00c007190703068040e401d400002410350341c400380c94052a000e8245561000b070300b08600d10305a08980124046c00c0180d07086840443c0034040001e00400302c04040410041c5452000d0001030102c2d02a8201120440d00c445010424 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 686808147 1250 686806897 686806907
    0x70c050906041e1a0d030f030b01020f0a0602030402040b0d0503030109091a01180f1b030b061e070c09090b0403110c09101e03030c08130e040b0f0a112d0a0807 70
    0x30785c2e0403003d0151580e13000d8880028402010201980c0b042d41c480aa0300c01c03c111882c0121310303406e9802030001c6040a0000c0d510890307080e401242007400b00600c50078002c40c540c80c0550060090b40c216401d00e0705c80005441c03506401c0d286c1c05500d4078040080342c8881d11040c000d060560071103500d65034039940308d03060710340e661a0034912600e01004900038a1110300c8840c12005580b400103040486d00c0b0016049016090000c90b80c25010038064034400c0701c407002001540d000e1410f020390181e48002500682c1c4070b51070002d000342500b001140000b409004c840d054825500c00350740d0114046008264042011140e41601d6600814100700a4252229440c0520511010f1520b22070454802400c0910031201c001d142e500c0c00540800a5941138550323034060180e00004480d2410641004c04030a081990466101000440481e41c01c1074540b007440c1d0305204582c1141d08004421556424090f43c4000803152041c11104001a0200480c01084040e91705e0700c40070120300f01540c0c0105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 686809397 1250 686808147 686808191
    0x5060901151101110f0403151b08041a2701090c05091906032f011e050408010e0f070b07031d1f170606070c050906041e 53
    0x201420060005000018590004100c40911402c00d44114181041d030a40102002c01d01c1665a8102060151000043d6401041100d000304c039a41c1201c03810343d031008110f070061a650041c1049414603140800c0c05407804a0344540201501d001040011b48c46030348030001152441c1244881c1146541984006d00c0c0c100410321040c0c00800100710a81d8400c8455402802258031410804000070107a444281c94090b01c4030141100348021a907a1400c0407030400000310095016001c42c92404403d40c40d03c48408010405035900021021000c605410741b0042214030401c001c81040003140480c424080e20040c41c00c401c004020300e042c2005414103000003034000c1c0015510402c0f1182c0400e50000070404040d801100700070441c081706d00080c40200d003403422056640ca645000c004515006480824608020710000c0300c280e55031020002d1910135143c00070001400c480c0184881d00302194030f140c0c09207001c0c0c0000350310300e0300c05102b4591032501c00b084200a074441080c0c0790000401c81c100e034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 686810647 1250 686809397 686809399
    0xb011412100b16110d0f111003141918030809070e0c0d15030b070816020303011d060d0f12031406011b020a0b04062307020a060f2706030506 62
    0xb03401c0c224140085000508004009054007803440106111640c4540c00000e003503034001056417540c216480d11151165030100d006100d050f44000c0794100f00d0090040070801e0140034241034041c2d540b01668002060340030a400680d0b1b5071601c0f03a035995030600b10b4407521030b4080c1e00c846100349031822143d481c04a180e005604018268800d000001a0700e1090303c5003800820400b081c0680c080841721007181107540044e116440040c2403000b00c0d07401983e550300882c1440011a0004161700b42640c1d81d20080c4101c407036003510701c1e042910701e02d003184241340c00a02c010030181e5920621b4542641c0c2e03108090b421750740c03052802139040e0419054800c55000c004e1060b41c0c47c4aa15104001808021030440c40480803640704100030210366602913850090700400300000d4555032140d0000340b140c0d80c03a5442402ea615210721804221940c001940c4165030300502603072049041220448000c1b2042c804201070100e101c0c46041d41b080200a0440c0d452000c1c454521880d2800c031004065400c0a0300d06 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 686811897 1250 686810647 686810669
    0x9020405010507030c1e03050307020606180a0c09050301150e0a0504020607060e0319030203070917030421050a0305030609060d0c030b0601121d0c010f02100b01141210 74
    0x80000e66001030960301095018100441d0040a6040600180c101010040c005144080500007050b8200001e180105025421951556207000a100c1d031305410500d00100d80c82144001030345503503103401203202e150f01071508240c2d403035540021a0940b80c07040742c030703201129010805001c108003078207159a00050900c810310103401e00c1d801049551182c03a001903c02a242d0039800c0c50000c007002190320707039181404280111070030712900400a4000781c5089001444400000991007003d40c840c201202d88400554502403400221603000800d00004510981d502d80d01c4101050f404d12151100c2406901ca4a5403460700d04204210b000340204110301c50410b43d1890004078800403642c0741a294450220083c54035a040140c0e1101c101c603c1c0e00225604140542c0200b0403c2d0f008a070f00c4111a00403034080315045401174490800c1181210010382c450384021403004600c0d0049186050103041c155580c90304a08440755580c0180b80728100400704409100f844d8000d80302410007013002c0441 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 686813147 1250 686811897 686811899
    0xd110607050d090309032a0f1802070303060e1303090b210702010b0a090b100c02090411061c02090108060105250c0b070309090b01050712230c03090406090204 70
    0xc054014000c1181d858a86a5651900400c050281c9900400f850300403801100f00e814122500155202c980d00180740d68004d0100012030000206401040d64541800c02800c140d141200f0700003900441e0040d0101030310751400003a1441041d4101c0e019804410050108001605003e414800c09a01c100040a000c00020340d2138aa103480c400d61001c0e0464805031180c440c824101e014007005403287e0350040810200160900341948a203901500503110444480e100b140d040d0f4102c066410081d4100c0b0f044000107000508402d620f003542000102290b04251048001d00100400340802107081da03400101c02c4121f680090546030700040c00d1814034908281540c0c10600c1108440e04004a19400c6d110f040410110004100207003548007031103031b124111800e00a000d070000b48680503a561400c9800c00da554030802c1102e40040d00311828001c1c502d14204121b038200304e90141c0702d170001c1002003c181c06c440d4010003001c14080d00300083d070302c89003441e00300411140e46500c80100940304007c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 686814397 1250 686813147 686813161
    0x907060e010903030f020c060315041a0603040f0302101a0306060d05210903011a0a060c02210307020a030309060e091b030c0403050105040803010603060905060102101a0406080d1106 80
    0x807801040e250304d460082d090110f200c0b81130b854980042c00b580c0d070280001c000c1061081c0e00c240010b401d2074048a081c412105600d031b200c0400251203520301d40202e01080054003044442a48944240c0300f84112a2081d8030a10040100ca14201d004241055880352161503450b00304152608207000300c44d80000c143d0b00c0d50301c103030317940d0117002c40d107803410101d00c4803004008192019600c03000d8024000380b03d881060441c02d41c804400d0342c0c41503c030303040f0f040c2e001c20311501c900d50f5041165405404000c91030281200384480340ca0386054114603200c1040440016103400e14190001c610907100d8519450034003802402222007800e0a03805052000c04000300f5207a0b00712180403074280581d00b10f03965122030062900707611481c0c1020300b240d230800c8107000400c04814002c504a40c1c0b942e6081114640b54850030741607500030307111903005a002e03110404004500f540718840341d81d03075090a14001c10070100402d041c0d440c035600c003021941084080414054000b403000074400d80400240019250140e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 686815647 1250 686814397 686814407
    0x11508090a1202010b030609070617070e040b0a0902071a0603010908071209050a0f080615060904050c1b0f011a1005030901060b04090e0c090709030204050a180b0907060e01 76
    0xc1c8015200349441c400b4103074194000e41c0660f10f4414054207680152804a00c141d5944190303100e0800058040255245041c10070780d10240610915501c1c40300300c005074000c00c00035200461000340c2c4031100f44000076102801f8402090303094070506842c0550b80160039031000c1480c0051006006e641004150000604a80d04035402c1c542e020706000000c0006803002c0706d001c030154002c0ca810900003000414806101c28200c01100c2280045403000d5550400c00c8840c402a9107480e07801c0f89062000740918039150704840e5216040041d420706140e1242000241d602d224142d262070303074104103d00d00d5a95800c2c02174407038201d60f400251a189501c01e0120b0307501030845c00b800c000c024011001c00da420b0070a4004900601d18080d08580f01e5403148072038001088021039400c1c5a02c10300802c1142c034100804041d20603051900c8a01c0010b20310f40a200c0900301c0103205200090b0784111102c0e012030402156560b46009440103407040c60001089440d05402c0c0e00b240c014043c41b200040d080740c1e800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 686816897 1250 686815647 686815663
    0x903301b050417030408061f080703021e040f0f0c031a06030105060f070203030703170915070c0203010615090315022506150b030a1a150f0f03040b01150809 69
    0x740441c5a04030f0445035850300314025900700300d0140c06180c0074084682c070319180170341c100081244024400c5584051070303036880201d03100003508554484800d005100c00c0e0344544010000103480428039130039103041e44e4225001078802c0a0391036507500050a0302a814800d021031300e001100e28400d840842000245580014071400381303d84000116104044884429199420360103400c6030744985103231a002e08103450030b00384242045903a6000811805000883d101d441040783c4820072162140c850896030005c80c9031f010780e0150740b505000503140b18803007a1650f92940907a90700c02030341c1c1145000182e0100001003000c1441c01400750507040542c0ba0881c80c1c0c040900782c9000d401c0400c6242400181c100c400c11118286c00901e40000c8480d4188000c5204015800c400c00c0341e41900c103a02e08221110046903504882000604071407120303040010024496094602c600709882c0031242202680204e80c2240c00768042c05c010002031103032040c600003d103140e0402440f245000e24541e50350300340c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 686818147 1250 686816897 686816909
    0x405010f0b131a0d0f0b01080402090606070512040602060c0c1c0c0b0a1d0a0308150109080f03040915080606041a031203090c01210903301b0504 64
    0x1c0081c4020242280d0760611005200f02041080d4900030f2074060f41c05038108a40d03084020341420b0150041d94154403901c040000c05840c0d140051306d513a02440444c0703400a0007c0d030801c1d0f04009180c0400c1d410031490603151a05000380da46c85007080002424010081e1407007414020912920302413080202d000e1042200e11446074091080191045a55090100c0b01800c9100e051060095425503900309080c10608604a4060400740d00350b410b40c0c603810311501a0010788104040b40114186145290003041c0500d4420030507916242c0190074492040203001c842d0340006400c0280d01c3c8070f40500316000c81109000700e0341e03130700e0905076a8071182c00801891185a507072038540601c070b00072881d1505005d4080c0884220100345800d4658952060710100b08500c0f850100b00400e6102d0900703003030507032050b82820240001e01c920842c0a41002c1070110f0900414000aa4120144809220180101c401c901d0701034100050410f046644401001001d0941d0300b4000c0e040980280880c3c00301c0350 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 686819397 1250 686818147 686818169
    0x12021509011e050703090509090706120b0a0e010806281d0d02071a030c0a050310150c2a060c0203030f0301121203020405030604081b060f090c0405010f 67
    0x1a0640040b645000784044015a491074801541d000c5a4040302500301c0b80d2194690203040c5444004000c0c3d0800203ca4140540c0d2103140c05201091140e402041400a00c860102d420070102d07001580400c00368011490740242080108003101e410005a5044041410051000c180000160121420021200c00070540f41d9090203001c6010149402c0411034860554000b01d228000094a41982d0302c581da03500d06c04c07010f0701509002110200ca016107112102c1c1841c000c03402d001034882c0d8000901d1184156000500040d120b41d195216480c1401107a44003294183c441c0f50002c02c09060041e26641000c203401289542c25105107000107a6099003052641807a2030300c0003901d10701c6940126000f03690040000076042034643d0740c141a0790b200340c1c40c1c401d4464803c0742c00c6049000e1489600c0d410b51280010401154a20004002c0d402c810041c50308612207100d1071a1900000361511034000c1c44003800c00410350b805000f40d24030003008680c113020551611100300e20150a60154044180b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 686820647 1250 686819397 686819407
    0x90604050705070203011103070f0207050607110a03060e0106061e0c0b0c1c0207060b12030405011b0506240f0630090c090703230403020102090325120215 68
    0x502900c10f40e0440f80d070080090101110708032100403580c01c01d8891002040c2e04804140f0050f001180000503194040c1a140c2025416101c2d030500700360b040c81c255000540c852010010465600929501640b040700220b0380700c1c9001070040c4a00c1994010203122a11908914281a40010600581508801203400c503482721140712810380300350750960940c40300541d0a00c00720b46454001d8241a4010002081141d02950a1004c900d21030f011654154208220500c055030082050310045c096420900d1038880303403581e40c6440c01105592040c40d060b100b403017503c5c180c1c1e0716091060540c40300340c840c117601407540004103007140204030007a071441ea4542003000007402d0034031042511403c10f170445407160070002c008686a24004c04918002e00403400026880c0e402070084e0340031140a480c048408660713000071100f07488006001181107540030010340000d5a01042a8484034032100d144071a80c0c0a078803c42c181c854010b92002e01c010a40c1190207000d42c1d41c0c643d001442085460b03100f9614 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 686821897 1250 686820647 686820661
    0x2040b03030d0f050f01090615050a090f03150605060901020d11030904060f06121802010c05010605031b0a050d021c060b13050117060412050c011808030603070603090209060405 78
    0x15000d000024150b8030f00d80f41e10701c0e00900c2c0603003001e4010903840350103000c580d803a40d8913101528130b18001ca8043c2107920024400706842140100184942441e0a000d9036403030700d00b8a120046030f0b0b8010342d00402208058203050581d0301c203130001468202e58080c5841c0d04880040c0d111044d00d0500024001500303082102c00c0307414022641e050320011f108000d0725860b034119000c81d074994000d0ad00000c442843c03203d01c0701081d2150301d04241101d005103204030400e900440b0013101e4400202d50079500c410000400e80c4040004844400702d0000c0c0510f403405050501105207140e5101c1403040c0b1708c806100000d40c4514040700500440e03098550340c819540e0801c0406807100300f0300c20f50840880050031030700d2800d6a00c90341c140c428148005040302c140c0403240b50382e0142950041c211a0450703c001c0701340ae000c1c00080401510701c90020032510b004280c200c504000341c81059426000010400910380b6040c000c3d04042c1500381410043c801141d0040390500384d0040c00d09008941e5200840d4003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 686823147 1250 686821897 686821903
    0xf0a030b04053304140720010903021b060c0f0607030b010203090f040e0a0c06171608010b03090705040603081308060c041e090513021c05060408030a0204120809090c1602040b03 78
    0x511098854443c018200030701c1c001e0001001c10301c8200c120030008250201f02c3d9041c082da11030290142d0003080c1415980400c1e91002c2052130303007140e004000f049020b82800e410f008940240700c0700806007a036803a10b03810144c103440d11007100c281150010031107118035a5849507500203112060300c00180042202420798607002c440c00000d840030301c0300d88002601541c060580c808450410044c120f407919002da030180744904511202e00824441c100521000145001540d44550f141e003c5030003080e90381c00400c00301d9240e038006949200d000196084a0081070b4074880052038004010710084c038014108040c903014078020701010307039850400400744010804808001e401aa00308101608014854100d54075003500224040d4803100f008100c502d03c69200400d0158110740640b140340c1d102d0780c0301d6119500082180006540c203001c0030459200081d15003403902d21501c5900d54171201d82d030070070100403030041440000c10f50800c0f0348c01c00c030444c0f00280007040d0750545000c03440c0840000041c1c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 686824397 1250 686823147 686823161
    0x1005070803010b0a1b0f020f1203090108061309050c09070f0903030e13062603030c070f050a0b040f03030609060f030b0a110c16080f1c02030f0a030b04053304 70
    0x42620f604907111040c46100740c2d10890303c610890b23001181c050398805010440c2440d031701c8481c440d0018403030b0340c5181d400740f00166809040180300e40441940c01030000102e0701040c00c03d844030390100e001044035007402070381a40c000885040c200e0700259612802840d807e001d000c01400c00500144030040c079190b541c15002070740c0103d00c0500c04140c40d030600302c006042428051600700301e44010000f03540d4010040324081c02e82c003039009203490426100c00c0349000841a0403541c0d0b206444500b00810741c8280e240d4041c038402d0811100c110201d08004041d80c020b50880200c00340b50a03810841c2070706400b080d20071a17520281402c843d6940021040080085039004540c4072000140340303914010101c1d9859500d003003104042500358460a2507a03030382d1900d404200c1c60340c1c020000e000074840a507500c1c8c214070031284100c03490404921544085500400700c0030300401e8980c05140360a1509006950340a42842000050f001465980e0155a2000480d0000d5082e08003000403083c1c5032900044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 686825647 1250 686824397 686824427
    0x602281e0609150b030d170c1c020703030e150603070303110309120c040f02160f29071b0b0106080709080109050d020705010908150601200a021005070803010b0a 71
    0x12800304498205000030302400043e0354070900850340140d800602a20107800c47c0e81141020541695600c40b03000300c207501180c0851818420b07901140089100c5000500145103c0d81d80441c0c0c0454910b40546131482000c6194240d10000040003842e440001e01101103e8051400c8010030700d8a14030141144220b0b90b005400103084402040c010400249102540a056034104100c04001c81d01808a01590b10082000f034a010000c401090502c4d10081030103005901c04906095100341d0f00714100d03550780700c0c0309000940c20100000c0c10341080d410110360b030001d0404034107100c95584922410a05000300c1c4288062a03002c5903c0e030784203000c2c40340a01040c00007000254258140544d0b101c007008001c00052060150105030703075128030101c0c41160a0b001c010000e81c00c050180c0c0c807c2120007003103541080f0701d20840a2030082c80361250340c00c50b44400050700072076407180103101544180f60603200c140007007000090000341c101d404507811103410914241d03d90b80780410440320080020307409 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 686826897 1250 686825647 686825663
    0xb0714240c04051e030d03020a0c061109030703031106060a0602100c03150902070606080c030a08070f020904080c010506040c05041710060b03151503160c020a0602281e0609 76
    0x1c4c0c51030181064000c0b00504114225016170500e5801202030b0311800200e80c0c0003c140300d2103000000c00581090b202c1220003032402d41000b5080c0046468032318180e01c10f8000404441e2039414410041c4119600200281e0341d44802a0810300081d6451344c0710501921400d685005000040380300e40d201b0744140464201030210690f642404001a400c800e40640f040e03440c01800240d5907000080303103444000d0240140800416545a1503415000b082c41517882044031141e0400503a1403e045a1003148942e414a442d01010080242110001440700c0d002d91710701031032031001c2c540101c0bda5048400c916101d11004640b10101800d10241480550025062040100700e008240002c1d600c200b001c8240381d04016454010401a0742c1020800420344008001240c007016000034042c45801c0d050400c0c01441d6510350203d400b480c1564000c10041e0022002e1000a20340000f10b2008080c9400703290242c1c10080d15100760351b034131030792a011400c600514203404010072600a2032030141c0090318 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 686828147 1250 686826897 686826919
    0xf0c0f0b190204080a021c1112030c010216030f080c031807031a040311060f0a0b06070c1e050103050c0a0e1503150114280e0a0b0714240c0405 63
    0x20b1300380e6514180c41c089110701890102d01e10705182c004400c45841d6041450160464044424401201c03043e40800c01c503030004100c0405040c1d0240020103c641182210107140c40b803030300f0300606440003907880400304a1003405001c0d140d012748003a01e411001c400c030f1800c41002510085450403c0701d40c00241507000041d9007040c2580307a000018031540c02500c0d030b031960b210400d00c11a1a00d008842c1982405a0000400c20f010308507402034101c40005027046140001d2a114914800c0d056807200c984404001038074098000c0206141c00207290070b090610043c200300720211142d0240300402c208001110403000c8642d520342e20b544802888a60105a81c0d040100350078800d208005149030100380242e00c2d01c070380484114119441140d0214840e60310004450406401a1844550754100110320b1103001480d0b954181d407200809003410303901c2d9600d500d07203001d0780d440717102c00e1401c01c0c150000e20210000200418400e41c04018841d4454041d503945402c21003240110b03004203801400400c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 686829397 1250 686828147 686828159
    0x2415080412050d0623030307150207020f12060115030e1527030405091b070201180b04090204150c12050d1407050c0f0105070c11030a080a020a030f0c0f0b190204 71
    0x504002c0403002821700e0034092a60141680d80c030607608014240960210580c6603248541d0180c070149200030400500c0d10001000100030b14000b11111180341c10950041202108290b4100175488040c142440280b00039070440744c940003800520f03050503491400088243c041c00c04404a41802090703401c0c080169250004e5482c0c110740619405820500c011582002840301c2200088100c850241c0c9040381e00da00440da80d00c88004035000750b000c05d010101c0e101244034040c0010f4101c0701070040e103480c076041c002d078210345140c44000d00340040c1192250204802400c2c00382e4440403420111707031791000c6110b183d001300303030041541819074580400d2206c0a540f100041c00154150303400c03500540819040c0508a440c299640c2d40469031012503000022030b00030141240c0c1c8401020340c0d1a0b181075486809642c4c3c010406040142c014205102c1003540162200c41d11000f81d1a040a07000100d9940300d00118a454010344284103842c0028280b00051400e00c034840038108080d0740b81c0d82c0d41c4d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 686830647 1250 686829397 686829419
    0x50709050601090b04230619021b010207030b070c0f0b0702010b040e030d0f0f0203160f08070e06160f081e0909282415080412050d06 59
    0x4090154954180404180a9032140b9108826a0544180c4038581890f00811405441000340c0798002004024050f140582e21040517001600076425103161240c21034500900384000c3e900351000d0044040d800131440c5e60f0014955055136484145544c0d40e807110b0100b502e400c80713170000040c401c680c1481d001042161070b146941c0240e919030020b003c1040c0b904200300688001310790307030241c684c0113221100c5901e995811603115030800601c0050815240d1004200b07990040341d10b2080700320304012210b10194448010700c080030541c54000070078100100d004012074174407204c1d54031403103000c5000344008100e01d0303018a180741d10500b0703003984440500d0560f40d150414040c0b09c0c6c00c100b807499000a200581c00450300d110f08000c014510540d25490080060709108401c2e014007001c645105103034040c58803510b8202a0704c123008088041100122882c01c4a40341c0145041c2c182c2d19480c034138190b40080200c6d80203903004441c05074801c0380f84000c90706400b4500c00b40e04001d04001d0b001030455215 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 686831897 1250 686830647 686830649
    0x1060e1507050c100c08210601030e0a02270a0603020f09090309041d0102030708090601090c080412090b0301091a120d0c0203210c010605010201050903040e0c04030602030703051812090105250507 86
    0x41c5c01c2c940f038a503100323001075040750ba40f00b83d51903150300b185064200501d403921030004000e54900c1002102812000552424102290101440d96444209109500c0c0c0700103c0741035103c0441d05030344a854040c0c425500c0b4042da0a00900454441ca03030720b03c01c4000020108800c802c8000215200c2c68140c0e00100743c0402501e2025103801940008a0b5214040c010140b5400311501c80700070076166556031f03120800c23103013110208200e5449804102132200d20011402041c100c100411039000b019a55100e000c4986105882038a00461656002078042000b8009610a08041131180d00c1800824100031800d0241c0351014160364004030f4440101019000700300280008021043e190b45c0168200c400c2542c00e03182c0784d402404204105149944450b5110001515940c105580d0380e4542c001c0e60030640b01000400d817074504001c2520b03d0310840400d05410a030003010b04a2480111003039134841c5251950400c00c1c0098072210030b041301c11205080c105c0b8940c0c81c6c101040981803082d00c502c29 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 686833147 1250 686831897 686831947
    0x705190b0f011e030305131a07060f0501120209090c1c0b06040608150717010306021b060601090501031505090106090f090501140f0d060501060e1507050c100c08 71
    0x200c20000c03e24030032003500644299030030650791410038115107064510b9084900b5106451201c48004285804101c00e001c06c115182d000d4951141d60700d01d04003054031080d2081d034801910b0100100810415149006030854061b1141103e0b0789541c030402c0c0c2000d0003c0034a076009006080480c2c0d00b4801d0f449400821400340c0744011540d1034600811003075800e18492814558000d85c411030a482c505881550803d20320309165030004d9601c000c2e04100300e002d074020388403d1ba01081c1034070740c7c0c01c0e540c9010040014400143c204e40c640b81d0000303040c40c3e029004030380c100f507a14102444200d0031001000040c0000600707a0300799603540e0000410100c00c0d405620521043e00d0300020b03100f046401000c2c141c5010500410300c20640c3e5092000380002c810f80c20750f0200e0401034940100d02d0500c00c0e1070181c10b81d40e40d000b00500c40e000170300c1a0000c0f036500c1c90359040340800106010071030101d044000c940d0b04a801820a924900040700c0042c82d0300e030003400c090783c00036064010500c4400d00c02580c2d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 686834397 1250 686833147 686833171
    0x6140106020d0201141f080a12091401020703060203060a0e4206030c0d0f0e010c0504030201020a020f0402130b0a0f0c0b04030c031b03050403022803080705190b 71
    0x40d00182c00c80c00d8810910a021061520101103803040303d081542c14000380030070021a944a0351980000c4c5481890802500c540021059103442c85030701540c103001800c0500b251400c140080c000007036480801d40b1025240c240d021000c940300c0d03502d024a400040451810111075420010f452140c03254804c0c28401d0694a400303034421220322042816480908134900d008800100707003091012640c4014100710071450b0410048100700594030070171202c90300c03143c000150a03401c0300c0c04c0c0d801c669440001c0411f001d0b0602003000181c2e80000c0400d00c407a81901e240d00320082904c0070130068019086903c03480884070038041440c0c50914098200e040c00d540c0e440c6c2c030300480c0e5642aa07943d00d44102c0a4240001d090000300468000c2c850101c44500c245810096040c803007200080807424a00101d0000d03070000b030200150f00d0000c2c0601d456120340310480f20b0319004920100c41000b207503c4014545103010030300c0010311000b03018120109a00c51203902c44c03c82685445200014207c4020001d04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 686835647 1250 686834397 686834413
    0x5010918050a121107030b27060726180d1d2403042004050c04050909070e0c0409050c0a0c15090206070c03060e0106060e12070302060c0307050d0509060a0f05070614010602 76
    0x281002448c4007200100c0024100300c0e111180100e907198107800010200d100b000302c6910b2464803589055109d43c203000425403194804100d902c0c2040b1440c0102d00070070106002000980241d11031003140c00c0012139904148812055840006442d600903007420088044200401d1212400303030300c0d180301440b100d145490541d440410040342e40655654004c42c40500060003030342000c064003508200160200c4191b16540d0381119005502213902c400b002c50081001c0110f40d40314040e054200c840700000c07900713218400c8030042824169603400340c030804680c40c1400804405602c040071044d000f4092a507109524180348801c40342c180300440e8a01e141103d8100047c0d418412001518501e9a800e000c0b07100342401c1203910510300503480d410380900d0708004016a034003001003040103012000b65441703c01c2804e1450520f00b030000f0020a02004100b15090399035444200d0304070b100c150502c5240000c0019041f21107004008004254501d001040d0b9000d8078002fa4183c101e07422035003154404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 686836897 1250 686835647 686835691
    0x11030a09170111070b070c060e011d07210807060c02010b010e060901080c2104060902030706020a0305032a0d141e0a05060303071505010918050a121107030b 69
    0xc6550300510f03801c0e80380501c10b43d80003820125019400039007a190807108007910391a4001100e00d68000c4003a141c0d554001040d4204c0d204010f010196101c0000d07120741e5280c071441c0f0340c00802c00800c01241c10b400140913010030100000351400150040000c002d92204410040c0c020000541c10f1400b0450942c40c1d14014038102003181c0182e90181c0d00c6070050349908c010450701d41c0103940c2504c86806042c82080103808104a000e12a6000700e0002c41e00d000b480c014182400950381150b000c64206440325408a60000c04898012003041802c4081012501e500c000c9500041400c1502e10000118049585256040340803030700740784400b01200b0745580b03110f0694560040b2a60713401034541000914402601d901055210001400741d0340740c0380c1c440e6102483c14490310410724485070743d0070040c0000980c0f4400d0710905044a00b60410349111911100c0d650f00905100800c9003061084100c0d1032440745400088181070320b402c82c0c001d83c0d103034039000d010041c007210844217002d0000005010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 686838147 1250 686836897 686836901
    0xa1a040603051905120a050904140903160201180b0903060c0412170909010f0e0a05250905030319271715040c05100c02010e1011030a091701 62
    0x2140c0e88034000f00180094034140f203100150640c82075a00d405403081200d017180d081c030014403840055903120f55958010008004c21584030303030545115136140710308100002500000321240030500c41d8141d0000d0f6418401240c07001030f0031241407021030b8040d000140d408801405052a05011002d86003140c0e1190702c0180302e4001c41c481c00d6840000d440080700810080c40040c030000b106010b030145084a00e40100315445002e038010701e4031400b01142080110071407903100b078011945034424005800c1c0740001c6000b0070f126912002e101194543d00c50401401842d09000400000e801c0c3d035298281e0041c400c40208600c40c141c0c000c00d20368107a0780c0205888170541072855407040c050100780c0e1306255000e103c4410042d0300c0511031044c010007013410109090401d07c5035100d45a1004041e08220034000e102d1098151791044c0440705210303000513170300460507207480c10059480c244103500f001d404a4003810b900d1100c001c80c0c000040d100052541c00200340003900c4504c0c1e0645030812240840307600f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 686839397 1250 686838147 686838149
    0x2130605030d0c030e010c0305041a0415030203091519050106020105060f090402060403082203050d0e032b02190c0303090b0412080a030f0f05041101110604060c020f060a1a0406 78
    0x130001ea101d0a403082198000c903a030100440c000d2a1082c10551211130188400c55030030445800e51901240c200300203e02d00310a0b140789034040c80c0a5045080207000b032680c960151654682100420000550424100b0510003031242c1820081c0b11550352030f0006402030005403101c50141c40701c9403000c001400c000c0100382c022a8058035aa1400d40345498542054012120350b1042c1c240e80c0121071154600c00391002d01031030284015292081115902905001c1c26611150280e0040014200c03010207940110f201c43c83c5c40d0507104001d004500c401c07810419030110034031085400281da00140680c0d900c014003528800d484104c100c40d1500000030032030050741705060b980c3c0340600e844c000050201d0040d0095034000c0c1070204102c503a48810805603029075481c2e01c5100e80d100104002e000402d02114489003003800c1144100000d00c50395502e808005101500c481d4692601541c154400c00400c0c4101d44a9000d0b05c02a060241841d80035102c50300e85c0710020404401d0000143c81c0070f1050320 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 686840647 1250 686839397 686839403
    0x80f07061508161a12010b0a08010f060804110a080304061e0c080d091a010602010c02060703051014060909010b030f0a020906030a0c020a1209051306030203030a120902130605030d0c 80
    0x100703d14a4031545602446244a04400d482030501190003d03690221036a80641241d450658a0b0542144020400781050f403045424200b80101000301036000140160400d4005480c9a054880e000200e001150180c0c4a800284000500014140d074000d190416101c0c0340414109140a42c140032503981e5004a0041c0510304204140641d481d000e501076001148900354203030345e140903941505800c082c00d0f0710400141c0d4540c0d4250494560620242e503011149040422075130500d68158150844030b0b0252140c40c403220b9440081607540c139801c4e1103091400403c49003456031184400b070385a40007030700c10040c2d92441c40c0118400b1021070003583c1c0402c402601c0e071802c40d51145d40180190054030701b2402540540171040000c9210090700c000c113400c1540324039691601d080300340030b040030011500c032201303910f044424001070340c0101c02c580846c3c40c0c0e840c200d0001070340542820000d26240c0c1c0b00940c008100d0024403002c0d84540c10910454000324191608641b070321206031501c0c69518001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 686841897 1250 686840647 686840683
    0x221811030103030203160c08030d0e0616020705100519031d070513020702060c0d03060602070f12060b01180305010b09061905040f09020306040b09060c0c0d03020304080f07061508 79
    0x80740d25a5480c21b2200189030150f26120f00050351786078040d007168403402d09140c0442e03c901c000c9400400070040c3e0390300070b50721503940c0c003450310302680081d16000b00c0e00031f0604c00d0141e402225001ca1103042078510650b21503200400c49410944042c0c002c3c114481c0341b81c40e40050245c0c80410100c080740450499038007034501c0c1c070102047c1c48440000e52010800720307840201403002c124a00d03003c11041000034819200010b07075604210002e07240c0310349548410301d801c04103201400454548192406260740c0908086041020ba50050302c2d04400c2221907012248001400414080150010020302e02c080c0d0300144281c4036202881480342014940d00188902102c04000b10300b4658480818081c00320350000312038141b640003d003486002d48041d00d07102c038007030f080c4541184c00340255034014000e001401c0c0b405144556564a8424250101c418543e001c4000350601600c20100e030380b0805c03030358601603498001d407418000030114441602c81418902d6408503200c80700041003e1601103588030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 686843147 1250 686841897 686841907
    0xd030e040c120e0c012703030e2b0501060902090105090f0411030a140a271704030b04060b090f15060d020301091a0f0312250b1905040b0606221811030103030203 71
    0x680e402481400300341d412003414400402500c280a2502a0300030088ac00300302c044c02c180c02d005083d52a55004400003e204000140080c2e81040c00c84055050a8450301106c810481c0014010052000b0680ca0080d000080000c1d5440c0c640c4115054041901d10a89079215503e0507001c40d03403e00d441d6000c0e104003410a06105250300781148489114001a400c5200c0c00080c008607600554411940050700200b40020415203000f000151081034a0b043c6840c03034081070052103030502030010b080004a9001380016521208210f81c11408030341d20039980d0f540c3d20740e1140014038201c42c056006040740f2854600c00d15081c00549140310004009104410001d80b9140282c0c3c4000031550f981d600d80c8041500a4840d004540c640038042d031301101091034010f0820454451302ca0582c50304500d0101040000b507149684142c00420544007180c40c0c8078800380300340901040c40c002016080c441640000c0c0402c2c076202214141c0c4107004180310200700c022001d202c90000303000c0100560070900c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 686844397 1250 686843147 686843153
    0x2a0810030209100503070803041703070308190e0d050403030e0316090f1d010506090714040e04081605061515030106030b0d08040806070e0d030e040c120e0c012703 72
    0x201164100103c0d901000c1420760b14400680307400719952004205800109c1c0402c03408284401178a8a0702c85076014521b4602d8940e001440c01d5802003038003424801d150917169402d05070390b000c1c003205528881207400d032120f180d0b8060059002071000702c0009071030704560b508501303010030f600f22095a00d11032481c0150400c41d10300c0140805128081065586420b032819000d03444551003014141d0000004841c01d2100c14040c20a00041c90601444020f02460140031410b100310740889660342c4080d100d98a4918159499100f2102d003c1085410b26040340240103000c02da0317a004482001c06022000100014840c04881109542d80020410f000400206000703410000075003c00601d0452140d14a0760381007180d0b003003500b000703080e5804041000021078224060743ca180714100d8050100c224103580051060340401e007024000c46d20341c02c280003000d000343c00c074401d8094524410300030503410b400c210740c1e14101c07186100d00040340b4184080d070310b469110300744021140b04140c00720381c0b6007151 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 686845647 1250 686844397 686844409
    0xb090402100201090f0f0308010b040f0b0f09090f270601050d02030712030f0201112b06090c0509190501092916121d090402040b03012a08100302 64
    0x8990810b554031409070034002586120b26801d41c1e40b00fa95042803a801605008100d004143c001540348e48041000740201202c82d030004049410380c01da280e56071955690780c103e090041c1220b4a400010310780601c500107105910780d500c9801d142c034400130811544200001c0202c13041a0f041c1c841c0d0003101c018015400c1c00c0d84082c00b02400a41100c1c026036403010b005d6248421004140d001410316030614200c1e603420300a460a40350032038812800c046610f00d00004e00c02102003014803102000d40300a40c00500c68000100074002108208900f1502e80c201030f01607480b00c0c4007a4030a1600005507a4002d8600d000d0b0300949406035a02a200c5d4200500580e44016045d000d400e00742201030044404400203005004d50290700300407001c00b031101d01c3e054401540c0003080409001c4002c100a41e001d50400000b400040100c1d40c2074440c0c3c4450000c14001c0c22000c080d140c00d9401d1444c0d00c40b0741e4010031110340d00e40c00903441c080320290400300b00b11100c1c030341920164529000444100054078002e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 686846897 1250 686845647 686845669
    0x6051e10050414090a180308180d0f031a03030a050c0105100806040308070c06021803510a23010b12070318121107180c0c050a0c050f040b090402 64
    0x70a02c000b07a01186490264449681d05408400040d503100801c540880c83c50301c0b0340104000280200049898802c01a21508200040be804c0642c0c0703042c810321645545cad1100900c0700c005005e881e80c8a500c0340004190b03038413000d1590829800d140118108900e03c200c54021210f10002601c0d842e03c544d5030454000501505950401c00d4260207280071485500c01040e0300307135070580c020015072802002e05080c03c00c10340308650030140d0f07044244985c00100d00100640710913030280905030680f0741c14410000b0010380c2c1d50f100c140114810850801610f41c40004614442d0f00f00414100400c0700002c4110004d004100354400c0c2071000505403001401c060360803140b41d0502040c91080c82580300d8281400d4003061f10040501c040000300f02d40c115007814002e160b0000501100d42c14914034101c03045401c4d0625000603038a40e070031203203503200310000520710798444290b40c0c240100d401c001d0031848882c00303168890b480c5503400c0301c0c80740346c5031144201d030740f02c040c089680c603995030b0702005229165 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 686848147 1250 686846897 686846911
    0x50304050a2a0f05040b010f45060810060e01050708090904060c1b020f0d030c08040602010608010c1704030309050316150b0a030b0f0a06051e1005041409 68
    0x2c07052180c12803540d100540025002c2408a056180e1800d070820041d201248412414046424000d031441588103da0300e4490820003906000200b9046150900c0c00f50000010044201140e844c414030300c00c00072240413030304e0301da0380c10403291600c10502c00030301c5041c070503400030801c0fa060008255005d04054140715006820003402c1207054008100181c908850840703016541d42180c0444030b4000b8101c1c00c605010203a007103075880c1e940e4042945548010841031040307121440d0601054481c00c00c6407065a0b2180f070382c0340c6850b40d0320300180c0644054000d1f00b04650800550003030061007007030701110081c041043e1980d20344030b0361030a400030b00705010140c41500040090740d40704c181d080460340146119103840e0b102c503110000000d080354030096403d4403e5034a07481c1000464140003000da00005052208816511035110b204018242c0c0ea101d15000140c15030688069108003034054504141980c07002da20340b403c05011201440760740110f00b40405030308000f070f20360709262105542c4031507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 686849397 1250 686848147 686848193
    0x6030a0e0a060c0203030402011d0303090d080c0729030c0a05090103112a061302150c1504050d030e0316050f12190201021e07050109021206090d050304050a 69
    0x150340340d0388283d450b0b095003440076900c004144000c5503400b0808170b5240090740308000086240c90002a100e10441007035030311512507500b020091110f00304c221038010480c202202c881d5699600317900501011481d07000c290b12030b03000b00f100300d6820382412280328681300303000305140420502c01a11a9002054441e04050340c50004201c200c0d0718600411f084140c88610080ca012400c801c005429850350843c034a45d0031103014451000c5419040441042d8100e0751606005510a5100041d004007072000c016485440440600c1c191103050807402640601b0503104015001c480907002d8030b00b0310f072030004140e004102600e005c3d011003d212120510440503290322807501c8151614060031200b02d80c640603800982c80021f031005c600b640c1d06000041c0001c2d801c02d200c446102c01500b1010070910078040c400185141044802e41c0001421343d8010200c4a034a0240c01030761390b407280c1c2155030380182c0c0300700c28001c031600e8051400d03a032050b60303c20010812012250303101416102c00d0444108200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 686850647 1250 686849397 686849413
    0x20a0f24050103060f0e0a0b16050d02030106050a1e0e09190e0102090f090106080f04020d0f1a0a09240b030d0f02011401030f0b150312040518010506030a0e 69
    0x200300e03805180c2c000c6000c1e6901044030700c100d840c09012540d001d450b1403083c3d40720440c01f000042404c000b403640048080c0b03e001c4410030f040400e8416128032001a0402d910010000c20ba1540101c09091f00311040da40c6d00c040980c0355851400310310860100b076000700d410803011100034030307140c0d9420303520104424404040d8203001c0790798026160305200e80701159401051030401420100c07240000c001084481c0422940f40c443c0c0a860200082c1c4502003000c0d101000500f5034444950008100750b20804585002050f03040501001040c0c00c00441d540c0094404503030000c00c5801b840480c07032b070004164064070303034000f00d103c01001c4040c0d03000b6079054540c1e8151040e40d50074000452034000d252104a0b112518030130007400c44003074203485e48c074207400c200052000c92020785e82c8003407007680036681504517102c10412405907050800d215a05208003400440713401841e80c00b4004807201a00c10205940e44100604102d41003400b03150340044042c000102844a0b83c0c201c440450f6101081d20303140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 686851897 1250 686850647 686850713
    0x311030910051512012f19020c0d12080901020306060d090c051503011d070806010f030f020a121415061602060d061805010f0627030b0610020a0f 64
    0x1d4100314000c056551445028840507594040e0a0084010611107400501b542c1200c261383c090100300c0c0081e0500034a103d810180200b2258242400041c1165000790491820307221201000c00808006840f81d80802c461b008140280c80c05004010203541c00d0500350007900c0300400c19140c00341c414006035003001495440b01d0b0080c00540d0070f0902055501c0d8184110881380410152188010305d03422401c00c08290707440034900390445403d2911252414203c0012409006001045501c03503100154441d945070b00b040c03000340505003000c1c0c1070043c400c14a4881442c003030100d03010302da1003a594821900c540341880c0103124001000340103014078101c139004038405412105000540315034603c1d0070b1002e400046090640d200954000740714560400080d816880094072a5105002a21500450100d1140582929010940f040d001c0030351b43c2e03060000c21010152038050148094071030038076906202040e40541d55400034513510000c3d0965a8400c1c01d180d0190781c0c0c0f086e00e0b00140c1c0709401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 686853147 1250 686851897 686851909
    0x90908040e0c09030f03090114030a020c1f1103132303040305030a0912170a0e040e210313120504030b0a2c060103081803030a0f03110309100515 64
    0xa4803003403080c58641c0383c2007050600e49040d00500b41e1141c1d1081c0118580c0c2da9100711820f00300d00303040b100d1a450307464002a60b4046d009070b8409044070300034000d0b0300c00039004000300c415036040008800e00181c4400e50403442248401c1d1080e01c0c80c411108940c03004a0020319800044400700c8003505004e4802108847c11a04250000ca4080d040001c40720081907000c0351210181092030003c00201c02196200035800d0030f508400c481c018404a41461820b004880c0c0c41388002c6d0262003031010540c8007800c540c0701d007500690b00140000c1008400ba501008000ba80d215020982281c81d010409840704155180041c0c6100200b01c4200404400140104201405129426404907402d002c181422a690741540c0c0b10340c500b000251541c22100e81c0004444d41181d812015255860710341c0540c031a65000d2401625803d44030000d8a082200d61041050340d950010707607420400040b84540c0d0341140d10081d81c0c1c9101c940c0c01002d05c0e10308a501c80e40080d41091404a08040c448411004213003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 686854397 1250 686853147 686853151
    0x70509030607030207021e0303030402010c02131109040f200c01062c0f09030f0d06150519051603030209010c021f0206160512130507260106030b01090908040e 70
    0x240c000c18004214140084447c0202040c0e40039800880d841e8030100c0d42c3e038040204081c0c100514203854005540350b82c44400c84103058050180310628040c4440c03003d5500c04003100d4052840d160748900118820700c2424011300344190035128034a903503880d54603207400400003190555078a540003d8800240c1e00c1e50069600e060703040d02c1241c100d50b144000e403a5001404004510022010802d0101d004411185200400d1004c6501c404e40490756000038040398000100d0440c403000b4100d101604a00a0300505c6400c05440510b2041d40b2011101401080411812a0b04400405001034066005072501b40018900340307202000da0b4000456848908a00b81481d0710b094020a91003507061150701d0303001485c92103c00308444a86001441c0d071090306511941e146030030380458007944220081402c000e81142c200d400d42602e40e0bc140124001c3d003d4000004241c01c8014084154103004d01c0c41103e17046100450168a028450310107000b1039581147d030f00404000224080d03900e103107914 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 686855647 1250 686854397 686854411
    0x61a0a020106081f0b010201060e07051602030f010902031b010203120c09041a12011109150f0c10050708040f0311011509060509060d0b010501230d0923060f0705090306 74
    0x1980203107441103482264940c0d05c1c5ca034110790424100380503182c0d403106415040f445070715050b07503150305005401000341c12201c8003c0d03050044031107040d40302c441500500c403001d0080b81900c0c03800c1102400603101801c045d02090144c1c0060200102c0e21804120136640000381100c1d6030310341105240042c084444604e40794a600c164080e01107098245030282508980a11000704103403506034449032410b00401c030000744509158040000300c002c4800907510074602d000ca160380c840340c0c44800103032034181d0500700e00845c0e4582800154051720482c2a83d00481c2c0016482c09591410340f401c64408642d50f60810440d074842c0c0401c84010a56100d003001444003410028201d418001040740700c0d00c029206902c030340b50200d40031020030380d042e8800e411070b502420904040001300540000440304103000d00014403000c10304401441c5140c00c160081072107914030300007601624440440c2940c002280c9442070388810300081c0c61070300e290b6096401110a00b492404c2040d00000645004821141c40c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 686856897 1250 686855647 686855683
    0xd0201030e0f1c1704080f04030b01030c03260d050403030b22141608040204140103051c0206090c040b0f03010c0f02010606051207031e05070306030213061a0a02010608 74
    0xd240a10840d502143c2404d00e4120207400d040300c1040010381015001070030090001491b218907210100032a4015a4000b4410b00d0310b41c0d490610b0b8041d501ca40c8000d0300c90945503c80c040e10110300c19417a28010340c1a11182c0e017050b041000303070070007810010821420302d66580d02c115455070300d41030342c3c0706c6488003005802e56258079002608165000d04070041113803070103c02032119100d5a24202c1181080a15240d1100d0351140002400380803c40e10b0500003005c810008420700ca80030464406d5120302020f00004030344401022079403500704948140c07080e00284800003c500c0c05401452103070704000c04955000b409500028215601d850f619808518128403100440c0d8081c05900014407903410102d04000e150740c4030510b200c070002d00f60b004040e59001c500140b281e0906900400c2800d55000300132500e460840507008240901003640b180a440d10080010003150050400396054099a2400300000e050390800710380000340703801e043d55240c0d0004245400104654664000c1c40004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 686858147 1250 686856897 686856913
    0x203030c010b0a1203050a0f021005070e031501030209061201061518120b01060525141009020a03030507020319060603210f0f0207081f1b09050d0201030e0f 69
    0x1040101820360707200c034030a00d501038008000311b03400c90f054590107040ba09104a0078007010300c0481c20165221100500d040c6000c007400403a42e030060000454000035821903098100f800d14a600740082480700079032066894002803214103001405030044070181e8004503c0c80c1d00e5241c03481c04130702802c1d00c6c01c00099404403005000086d54000030014201c80001c0c2d1411190364561010401717050040c0000d00c10000341300300c074207200d079a0320b0043c6d404c908910211503000703441c18110714080d0b00012242449a4403c007591302d1114070526243c50390041803012841d2450350700341c8031034021540aa074180120b03028010003229201004c0f241030f201700d000058107400c5107060200711001101c40610703c040341040c00010780d0020b81d00d004290a50816921044c0b5070300080b481c1c180380703401c28045802045402d518000300e55200c0c00320329002c1807082c0300380c1021181d825000d45644600d04002402c2d11350030041402c05018204502d40180b602060903001d03071840d01c1c905415071244e6020340e8400e602e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 686859397 1250 686858147 686858149
    0xc0203100203040b070c0f02010e150705010c020c04061d0702010204050d0c0807060f020d0e03030405060409060e090d0906080402210312060a0f06080a020d1401061202040605071407030203030c010b 87
    0x10344c16a104c00c00b824168180c44450300c600d0200791100a00a062000004410180b0340d07850f2403407020160600513469451b5040c0c9070a901901d0780490400140c07042c000c0b00321082c038141c044c481c2601e00002c0104c036a025035019020040c17030050441010740d5030070080460b00b03840c0c08002c0300806020307881400020307140c00812860100380f0b0f40041d00b084260f4000c4035070f45038081003515130151180717010500c0040050001e400e40c45030754007865001c134000400165011917038004074103c50310003002ca250399460811a54942c45118641e07400111512014000e19010303514980d00240060682c000d141000c07035054a42d800701241c80880e946c004144540c000d010000ca60b54021015a8000c01c840e2500886c4521300c1d4080c0140d0090100a4001803c0d4001942c152100fa0102907000d02070f01460036502d0884090a000303510008c0c0b005442d05035200503900072601200c0d0b0030303500c0e00d207003070a66142c0c2007403448041c0c20f1390828058100000301581c7c00304090402c1c1c40d20040001340c00034a0034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 686860647 1250 686859397 686859413
    0x1b03081e040e0606070606051309050708070b030408160204060303111b0901051c0f112115060f030601030b15030109170703091508010f17060a0b010c020310020304 72
    0x2200340000c0004101c14401c0300b1802c00c03200e4028200760760641e250700052600700082d108a8200c1904031181022800c500905074103e840485c0c0a1401d4480d03458540c040152101400e01601e001040704201203000140040000c1c44902003085c0c5c2d91410301010350000f419a00554002c1e40000d50090390481010301c01d01034104041c01c9012500b0034951a1004900c10000520500d8890406068a501d2207648561a2640e107030340310310a2110f81c02140350007007001000d0364865004100800d50010000001841e004903494440b0003440e050300001d186420540c4d000b800580c20050210700714110380c07410029070b406144144c01c00c45140c070304003003580042c0d40345000c5240319a040540780c00210b440c42c1c1d03002c5440c03050761440301ea90b030020341000c1d2010792250b072120016a80c0d00400c04112540417801c3c41c10b940003541100115550340342c8014407c010f440b850010b542141c00440c0b81141d0341d40c8040310180040c181881d0505658000038104031100d140c803496141c0000400040203c46 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 686861897 1250 686860647 686860687
    0x5070f05060702150c01020904020c06011505070c030611210a0c0e1c111207081b0108181c020606120a0b01090513120302070203060a0606050a0305041b0308 69
    0x2918100e0500c2c01a80002d032514000051841c0601c40c002428500e1100a40485611200181041d980e5080c0c01007804d540e88024440c801240400a8447d2400c620403000c9a01460f040b0481c1c210380d0b810354440400811003c0803080f074240c000c208c00202c1844668407a510b2091030a1b84268618050001d601510b0a40d51a8010003007111002c0c0c4141d0b40d65241c0040da00710186030342c000c00c40a49421020294841c118070341c42810f900f20482c5800c40005c0e00d20541d40054296a1609000f0342c59501c1e24038160603e5000c0744803035001030300003404ca2301060f410015890444010a44404003140c42981c821041c1e801a004039041000b41d060445429030700c00c2000d030090802180c0f54440c9461034006002e850465038654000c030b02c20345140d40d02d41c0038054115444014164511602800075440300707404078042d0140100040000c441403042c81c04407462030b11001d00c0d044981e10100e0085c00000d02c1140c8400710740d9900046110301020400140d8841e501030b45c0e4681c0c6481e0920310388800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 686863147 1250 686861897 686861899
    0x203040324061e030b13050a05030c0c0f180604291f0f0f03021903050a050f04020109060f0513060c050f0d091202041806020d06061e230705070f05 65
    0x80e41051480f85803400c0041c40c2141d0300030b034411080e0b0300d404c2111303000403440000c06441480380004103070902801000821410809608403520000858180480b0501c8409410341c0003511914040c0607120741c4079240c0d800040100006014050007002002c0c0103054120b00302c40240c0710404040c81d0038010707a410076a004465440c1031009500000804540300112680b0420260070300f08154203000340c050b2420443d640c001c68440001a1800400503d8211500d092841c01c140216a9000c03031054218026501a541c1601c51400d008064401503141c4507200b0030440304109a032201c00502008002800c1c10f9a5008001100781c10300314906000078005c00303226005034803401c2006810948400844855000011a1040d6400060001e0500d80400d552001e60111400304001c0a940103007001c100080007048404e8032007104440600400401c1c0810202e010b210345e030918010200ba1071035070761802c1110000c0d5020800524260001201124240d00c02d400a00240359110800000341ca0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 686864397 1250 686863147 686863169
    0x9040908191407020f12060115120912180512010b011701350312100b0a05040e0406060f1d010e090c040e010e070807050f03010624020304032406 64
    0x50540c502052031143c80d4000344243e10402150b2035030f88802a0210040c1d91040560355950f95403402100c0d520300594002c400500b4903c00a600140340e0300c680c048103a001306602c0302200c01020191044288142440d46080450038006610381c3c900009801e014141030000c622a03100c00001b41c00f00d100440204503141d2060010b0200000300030015007442d070b140380c030200654280d52840b41421018011031600d03010000b8480d8400302c0205541e07010f01d00c0c1d401c600099666458404503a070152100400c00180200010000007001d140c415801034001c0d140003420b1070f9102100c2510303030816408002c020050001e180b140000051074a4014618000407010030b00c0c2001d162501c3c1d80c00002c5480c0b085541c0c50384403074507480951181d5206521242203c56803500e50307801030f555035040e1042070b01c542d0480d0300340306050506000d014121074620705449110300c80300c07080880d000000d40300da81c00c500c0140000800b02d1200000350711817510072001c1d80440c5010302c0141c1e040e0b0310715400c0414510703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 686865647 1250 686864397 686864417
    0x20d1508340e040c0906061211090301060303021b0303040b04170f0627030c0d050d090605070816030b030d050c19240603020102120a050904090819 65
    0x100d02041520000d401e1441003003045000d00400412190058200c640c403880000e0007045401003004054082c43c05045502803269403120148250b035400d000c2c407000a07148160089040d00f1540003400700d507000c1c41042d41020b000e900800e08480595100360700603440b000610300550700c00c00069030480400c2e00590b14003030400100c20b110b0320031807169406000c844064403240240034812000d2221901042d034103c0c3c10b2542110fa881d12184e881d844c41802000440b540d013100000c101d0b440194460068440a021b83c04191030a420440c00d140c090b0fa1038402600010700b443c425184928103039144d580c1c007824100285003c0c000340c095094140b40c40c0c910611026680000c000020f003000b450003070790f030b5107004000900b8004104061002c00c10289042070030401d100300f03404075103217015000940e15481c101c91501503400710b00c0064096001300c940000591600300c02030040070b0260410500c0d100001c0086001c0f82c003c8202610760144c0410381c40d0384440b543c00c84440c200401d181503e02c407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 686866897 1250 686865647 686865659
    0x40803010f06030e1218030106061d030307020f19150f0f0810050906030f0303040f03030e0601180203040311030d0c0212090109140d080a0504031a190c020c0301020d020d15 76
    0x590303508070120212040c00b154a208451b0040c079880b004807005002440119590013018108a6443c1c24604040501450107070482c2400029640d605800500c01068206510144190046850181c9607800c0300018041440800300380300f54046695030340c03486270141084100400550350720340c81104010a69092201c1c941c690700d440b00c1514003c459104841d260100003a1070800040003211450102000704002e019034840042141c0f07010303840500c003603c0c18128003901c54000f4010009a4a899407c940d4031002c00d43c09140d000c0d219080191155560b244030b00d29603001020742e0f04801d912002048034460381403240e4a50983c10f461064141b190850004e80006da0318021481c0e802039a81c1840312598480c1c0950001070303040380382e09071396030500040140301d079105002c02c4e00e00406880c0280a480a804451489280701c40071000282440d0880c190141220143c0301d01148200b25a94409903420702c010848200c602e04010b9840070740c84a030109403003001e9101502c5c220258002c1040b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 686868147 1250 686866897 686866903
    0x605030601030f0e0706030b09010905090a030c150501030b06010908060c0a0507050a020907050304140c090c030a0608030a090311040606020c090705071704320d0515040803010f06030e 81
    0x22000d090104022410343c2c2d42e28000c1c403004c2141c540c0c41c816440300080958050744296442003042e5424034080c0c2c0c85e40101b070280d5105131145c06040c0c0c004101580440d11469040910a01ca4019446141044a800e405481d4280c200399102c0040005100c1590303005070703082000780889809810780b480d0940d001c00042c018485c2c11001d0050004548080280238484181ca035540200004a80c4c01c207588010031541003260120f82c0c0c56000c60840210180c0041d00a20303480000b0311070141e035070369408a00c45940024100060711b64480101080204007030000e414080361715a030352440c1a11b541081c61102004805c1540030314500102070124030303400b08416840200c01d03100c00045403102481264144030b940d6001d444589071075042c00e03100d240c1400401c1107801524070702940d000343c041d100c070320307042d90b04002c83e03600101030000e1a0f9420b00805240c5014002e40076a0600034586524080041d0125421126a1070020041c8100c0502d014402d002c1c00030340c07a08103d2201040825070b6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 686869397 1250 686868147 686868151
    0x408030a050a0510060c051c0201150b030402131a040507050306010201060e15010818010c03091a13020915040e03071e05030418020d0c0c0201141c02090105160302061906060503 78
    0x2c1003100031b815440500034108800c0802007448824081d940a8200b8024000c002d40500300301e1403107100d03e0000720564480d003030303030f000307680040407410385045000132000202901d4400c00401c00b43c0400b651899a950311905110301400c2c3c458030740d20b10b80a0002400c543d116000081c4801d1a5800c2c80013258501320300307504082003801d101c1030503200c0310404000304545684404031582005e00c9400500d5058003c44402442003100d50490103a4441045203090210b030078800240c403509008000d80740c2900d0b100c0c1c1141d1802a400100700c10f40300440c054501c80340304c581481e4000074041d4200302c1d01c401c00384590480e070314649011849566926440307116a2040844100b00364540c0006100395504464000320190400c10269059000140c0b92100e48641a40416501d000d0b24850b00400402c8508441000404041c21840c51040340b0003074009404260402009000d6074580149600820302d0660194004200750b1074183c00303150360511190110710003242440c03000c005041c2c1150680c0d07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 686870503 1106 686869397 686869409
    0x3032b050c0301270e0d03060311040b030a030f0e060c0a1a0603250314071406090105040e13083403080106140f030408030a050a0510 59
    0x701e0750009109a401d103040018008003002c01e10741400800002031900019094000203c261502d55580071181c0803c0d6644414810721100d4241528400f104131401c3c041d41806e2001310380c0750ba841d000000c0c03d1040d44c031021102607010b11074442c0f41e540d01910140d1512010404d1542e5010f2004c02902c40f114581e01c41d40c1c004a00a540038810080500102a04249403d00c0f181c0258a041c00c02d0640c0c0a000c0007000191a81500c191800100c400400405040c0a8064291519004d902e4807840040000d4000b590300202690300b140c22405d48450306a0368001c040300f41c9040c02c50000d000c050001550200381501417217032941c0381c02000b074400301c040c0c04001c0d40d601c1d1801a0f201902040710203004100040c890313030f08180d042a08041d040e0030004004503081140d00191001c9864100100030024290214400c003584402c0b0301c5030621560501c2e000130a07503084540625 = true := by decide +kernel

theorem cover : BRFrame.Cov 686690647 686870503 := by
  have h0 := BRFrame.cov_init 686690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 686690647 ≤ n) (h2 : n < 686870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
