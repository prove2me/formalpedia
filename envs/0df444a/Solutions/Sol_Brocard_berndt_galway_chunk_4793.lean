-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4793
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:44:57.5494+00:00
-- url     : https://prove2.me/submissions/44ef21c0-b8c6-4859-9eaf-59b65f5a8ecc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 861870503 ≤ n < 862050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 861871753 1250 861870503 861870509
    0x70512090402190c0302010e010b0d06090302010603050d090510080c0306040b040e1f110309030d090606051e0a080318090c070b0f100f06052a16061b03020a2a 70
    0x22a01090f5254117041e0223008580d00741406600030401441c0d46400584c455418840c0600040d035904281c0f03003014000d52164014603041812210348403581d4a000304088601d0041601a2038616100e80c1803a0241403203502580b8914a002e0171503a0300750038400201411170041e6803058031000c462903c0c030401e01c00a00c6003110031030350350244043e1110350004d55400d0f143c0500441e204004109030000c0c0071054500010140b078001c5034813406420300300050070b100c2d04a43c2c5c0c002c0145030703500e0300c00c3c811500806d01d03c0e00c20b0350003c165540e18109180c481c003d0b000d034044001d4800301d161965150038840e00760720140e0024a80d041c8038003502c41100005045640f01c104039a00d405024021500f02a0f0078002c05055030b4200400381003000040150080020302c9062b0044000c000180300c24082d40020030a986200b202e00d880c180481d44082440c880c8154408a50816610b11140d850b45190007109a0540c0041400035107654500c11130a04118a110040703001002c801c00c907201c030b04412002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 861873003 1250 861871753 861871757
    0x20a060c0209010f05060a30020406020105090c011d04060e150114210a0207121d01030608032b0603120e09040b1602030d0510031707051209040219 65
    0x510405803061120010042c1c0080c424480c895400f048269114802c484038510365240c803052030704050500c60000e04101c8c003407400b205408031210100150a50190003200e4040c2d000340401d403148181c072038564071010440c1c0d00040304d1020400f620348200e40300000c4c40402030070001e0103a075100c8014640e20415203004c481f50b01041c1c8003a8141da4001c958000181c3c1008015180c5a080c40c0b58005545141c14087c0e05000c201000400e14080e660540f0103040d04040000010101914020003002c0410030200e00c100003115090b6542d40300b44101e10545404c040110703c0c042010280b4081040b910848094806100034903820000d10b50082d80c2c000d51243c000b0f800740311981c07480909a41c0c40b0080c1c0ca03004200c42410007022418100b0041c0d00084160743d40c103090140c2c59070480c00d500c5944040c0d00705505000c03d2200b80780c0c8900002d0105c900420354507811070151101c95105104840000d4802d42c8030180c1c8601c0c17490084003d00403404010401442d040f80b1828003030041d9104020b00380 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 861874253 1250 861873003 861873017
    0xa0213060e180a1b0f0c23150405010f0c090b03040204021308010218010503041101081f030b0117120301090203151002030a08060f010207060e03031e0307111f0504050a020a06 77
    0x602c810469188000204c0304c0d04140015a032000c4005003074a5030010301803d403070a950b0980b201001062000c180822a81003907403a1200e44028078200e908041e901103d0540c45c00b481040d960541c0c0c410302c41202c6841e40c9441d40766141a90003035280c1c001410607644a5400c0112001c00300d441d200100c0200802d00000d603c8204504601c0508091903407024140001042000000341194202403020602403c1c102e0316610741c0d40189401046188800101095494020060000b51010380c0d04030707a0a5500d607000550704089180c2c036141d5130b8808000a10080c8018071500400e9005954002086590202c500d02c1100000e034000903485035010160f0000240a00d00c103500140d280d40c0501d00f65003640040602100007552841c60f44070304401c014a03059241c605503400d104135240710556150045403035001c150700042c0343d4000e841010129491060020100c0c0c00490000210301c02005040c04441070360030380c40040c007002401100c903401008811001a504c1d4150500506110782d85c40b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 861875503 1250 861874253 861874271
    0xe220516030506190504020c011419060b04034409010e0d150b1c06150f08190807022d04090b01031202150f06090a0213060e180a 57
    0x5000c542d07000d05518020140010140b080c46043c0f09600d00b1030f00c0556005035159100c2c2803150062440004014281d00006d0a002142200065289030103002c1007041040540d138166840d090320031480002e280c4200c0340f0701c44125034030070980900d00c441c1003003c64161f00740500e55041c10400035250011090400700f0207484659008607940c21000d4261100111412035803520380d60034041c402d410380000c3d194100740342d2a8403540c019143c0d00f0031013440d1085540042c580351001d01102816410444507016002030752082c8845082c045a81140c09050045108038180307030710a641501c01d5419640400c510001030b220540c01e15074408407a02c1e03054038800480380d00078401d440d0690302ca12031418000d00001080023405400d044070790111000482c028020000c0e400c282088002011100c0c4100410042122482d0400d2050008803020780f0b56686003603900d004c900814000d4484107801c40014005e00f4000e10b800300348031800800050801c83e5401c1100030140d0700321410601152220000323 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 861876753 1250 861875503 861875507
    0x4060f0813020f15040f0801020910050a080402010804020a03050a0302010b041b140a09032f04140613060b0f040305010605010f081308070b0117070501020c010e220516 74
    0x40790001481000104803442540025000c0c0380140c0c0020b1155142c145035108060a680172a40100a5204240b07085541c49440600030741241d404a40038400b405071100c4901d2040d01110b050890b29103c1102544950b001103583c484001c1007240c0080c004d56000c00441c00800828590f14440e0703001240c0e8410074020301050f40e130740362409181c0f40141d151a60f1000d80103250108030012018020b600e85403081e200300c076800841d40c80a844203070306070040d18a01c41107840580d004d08940c4602c504d034601e01d2062104640d1301c664900c40302d8680601040e003514010b0303007100d0b40040c20100440d035180c44540318400ca6220700945a034000002400300200042030203810001d01003400c004480342a00315002e400c84030018049018030144611000c200140031096491450f00010070003101c1da1614550318050030011241d8245200e0904002600d6200142e020300c0707000181d65039900418101c040c4600c03440c0c0c07182056040607207004a2032402d4041e11801c0d106000711840c941001c0384184c80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 861878003 1250 861876753 861876767
    0x8090a12110a0b130b1c0615020601061d0906120d03060302010e042c1f0f0e0a0c21020405070504170d091211090c04090c020a0f0b13050304060f 64
    0x11510b00c5403010320401aa0740c104102100c1201c003085d081c603a4441e6600c0030900500740188040c81d0103860440041180750445000c100e01120315021140c040c1d0300d4500c140c44040c03d86034080c10100c400c0c1c01d041c00c03a0503c605603d401c900043c1c60012050740d046215400c0c0280c002000d000683d03140004c000b5580d10444820b4202001c2c2c408001e8000540351110803208984200809483d2a681c20040260308000d514240510400d24201110014101c0d4002c0c0c17500107010040541043e45900c44c81c030001c00c041c042c0c650302003141072a00e8500700c020381e04404125020341051504001e80c02c05a1294054603200300382554a2542d5941071103001d205840500541c0e68031a4800c41c1e94404c050741281002080c5e170541ca14a80c42d503900c5241c580c0710481118403194204202c1818131041040c000c0145c410343e6503002003400b64000b070712002c90f91000780842c0034103040c40030913024000c40d10740c170701d040e811a0310400d10841c1d0360701c00d4442da45160702039844100042d102c0741107182a2640925 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 861879253 1250 861878003 861878009
    0x8031504090b040605460c02060a1d100501060f1803261c0608032a070803030112020406141305071107080a02090a0c05030408090a12110a 61
    0x4007005010507645a90107548801000146195680c1006c146800c5007480701d180c02c0c40c003940e5003c00d00d00740305031100c103044500b480c2c19410900000c0e68124041c2d00b0702451003501150360040450395601040071000d40491124038000b0601928a4440540248504803c804030341c1800b1a107545046002401ca05402040d1801c200d101c4541d404410361103043d650869420034450200e6010140710502280046030114007003810001e020300c030b01c001a01e07100c0791801051700304201d202e5450012540b00e00c00e904400700f001013a00305070f0200c1081c4181c42c2004c001d200040352000b98813007030380c1d5107964070a802490f581d441c100040d20452400d4001d0001030312003044420f1002da000c00103d0300b5035950300c03008282140c59030002100c46200b90701d07a100c81c01800b0100c1d11403035620034000d510b0ba41c122209078040e403c10000101c0c003c80501404c03d10340d0032946e446185503143d40720001d1903041444180e5001c01003010004480701c0207060411080d02030203100c610740d00d82c10200702e4031a0542d8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 861880503 1250 861879253 861879259
    0x110309100e030a0f02030d0203091c030e0c01180e010608040b06040b060a0e01110d1214070206040f050c1509030c041a1c0b0f0426190c0b04080315 65
    0x24018885054003100b03880f24052107040203001074030041c000f81e003035005000e100324a241c80401006245880002c800794407242001c003200047c000e00c041141034070040031a04001368445c410000c0305511860051003441014800d1200c05601d841c1181400c0c40d082c0d1040d80041c0411091000307002c41d505823107402c5281141c040052140381004038080d4010b548002c420300c40280d0a0102c940d008034009040110183d0680b10103407045800070701005010444404654507160084241c0b201c0c490070f8034000c0e00703990010b0980756215940c1030005264124102c64030b000b04610700a9a84458030151003200902c07000603101c04040d4103140c074190720041003074840c80c1480c503080ca40a82904110f1040b00c000d5854401c542800c0640301c0c608001d446000300424200010881e0500384849018069803040d1070188200c000c140c00e40c0140303081c1101405004100b0020a645001e01b10054000800e140c1040c44030107900d911a0384000e1002c4406540d6844000200a032640711076070004160380e822 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 861881753 1250 861880503 861880511
    0x1203033c090601082b03140f01061b020a030206030408120702030a0e0306070c020103050c12130209060a030b0604091410091223030403020a051009060b01080105060d1e11030910 78
    0x402d8580d4407003001701d540c100300412501543c000078426004150441c0c407034a2121080e04000c0070701a0068801d229020000d451480c03030400034024400f83ea028540c00500c0046110b08640820000d50b0010f003084078501c2d020041500b40704500e500040c03103904580c01442d1070b1a80000050207581807813051074825040001000300703141d080030310034170016020b10340080c3c103640d19401000341d44920011815510000001c129400701a085c0c0c1c002e07014130a4031403540e19210f000610000c007400c2e00005003030503a1000040e040d4100395002200b41d42c0504040544d0460748503005003480f40181055110300d40b1031f20310b0f8042c4220106070001d1400e00346860484543d6036100000300c00d00803c0724120203000007010038281442003004040450f001420b69070040d4a01c205503006101201c421601e860030301c202040c00d0340c001c20190341281e4014120525010410255000400c0d00c3d10f100c07400b0a40c0324040d0b8820440c64800d40810981072403086999050601d0803504e4560003505401c81c6c2810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 861883003 1250 861881753 861881773
    0x7020d05040806070804080c01090804050f0a030213050c0d0519060f120206090f030d121103040f0303150e07050d36050109021309030e1203033c09060108 68
    0x780c03d0340c0c004807502d8100226180d0345003c1107148945040410700390f0a000003e8103108804004000702c40c0308030741e0f038800c0c0c00009052005252091101035801200e58901000100da03d400144d4002d1400164524010140c0420000c5038000c0c4c40c4c84a0603100308006000b110060306c00d5a002d020914100900d640c87c3c0700d4001030444d80c9010080c015400804c0d44203558031040034405815a004055400903000100c001b0b0101150800389a64242800b0090304003c880c02d0440340210342000f01801c030f0240395141034000c0d149500d8140501010502c0c00030b4441d099011450085405689046c0d071014062119030076901c6007445215044001000b0415105510001b00e0f003000c1210b80c201c0c1002c032241851401041060406500008c06401e04002210940e0000b140315120751280b00103508801d085c0000310740d0803210480c2c10b900400101d01c040e4214030b084205124030f40c1e1800c0f0050543e81c1110006414030380d081a840c07100809004007920244a01030140a51000900403451703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 861884253 1250 861883003 861883019
    0x504081819212001120b030d03020c030c0d0513060810090e0f07030503130e071413031a22051b010c0807031805010302070f02060f0c0f0607020d0504 66
    0x30707151007a081c0040740d050801850400701442c40000941200c62035541900b820031402c80e8041c0100d000740054140304180324a03244074413480c0021540a0010009880c1c0e102050b002988901c400418611007401500e042c83e03410001c080010020b03039201c035182e42c206170240d0303040c070481c0e0002130510002c50108140001e0005c60307941103803450070000c038030784113802045400c06021002202d110b016008001c020701c2000170060565800d0058100c04240c1e55401074a0302040a554040c0010000c40883d0170422a07000035101e102680b40500542d150f583d55840715021420340700b200014110030410090640320b103200200302c2104031115a410080c1d50b60180c6032901405080300300204a803114001d80d104142c9865010ba01180c03071036039080e5030700b0f003d800c1c1c0c568000c510400d01008034011429510a00985200c01d9000c02c1c00c007034031409542045183d400ca40d004c94a00f10060000c904408410400802246d64000c0940701c03500b40954004d05080329080c480090001c02c00003080704e80 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 861885503 1250 861884253 861884299
    0x16030906080a290402091e09010605030609040f2f040f050402061c060b162a03060b0f04020f0304030e0405040b040209060a030c0b180307210f050105040818 69
    0x103a440110b01c41043c9115001400030700440802580080009501d410884803424001c88022001c032440852680c0c0c803841151144000c8414070303048183d940118000620343c01c1801c821b07900c2508540090b800580c03500c54034154030303044035952034402c251800702c90819104d50300e0f182800c180c080c002d51410f078010a14510a40e03d60090301480c0044007015010294085c2c80600b00400d50781d555158160501c0302c0c00d80314030009542034845c0740030794442407030080001c0114040810882c030080f4510b446102c024914800031640082656401c040b15582c1e034401016030300c80030100d02e07480c0d051500f0010402c500b00c070106070066150105000c049200400a03540c480d40c101d441f240180c0e00d01001c10900703280b03a03000604c500366107070003c00c50045800c0580b027400038251403100003201c050209540c903602c91041d00c52141540000c409400d0243c0401842c0c1d5004900d08405000c60340e0381c603821110b003101d060f2418200401c2c0400c50b4403d10a11094041080301c9000d00a541c84499008034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 861886753 1250 861885503 861885551
    0x8010e0a080f070f060203070e100e0409050f1204030311061e0604090204050a02032a0d02090a080708060708010b1326100c02070608040c050d0816030906080a 70
    0x100d10301194203140304454000721240c080c0d0000e0130002403840c070324180029400945510f800309800984100c5542010040d0a682415603960f400d507002000d401c0c00000d040c580f0040c0c1c6d6500951202c3d203101d0f101003140300340751103500fa00d01350b9542c03031401d00400c034825101c01c44545030007507010301600051075030480003060280d204114880c0c44410009000b4a802c0c1d500035001800c00080045400140d4043d500c02d4010b045466400011302ca00d000c61500d00000b460b00e0040140147c0f08450982d90240500200203452460100d407500340d420b1500c680b5038410348040d88550100082c040d402030141d4010640180203a09060f0045605400002c5c0ca00504003800440e5011040d1003030b072400360000300f011040603524a0300300d110041020340024001d510243c8240c40f400581c25109000f01c074852038100100003502402c0c001007000503034030001c00361107540c001c1c007001000d0300350000640c3e1150301c0781e112a1400c521b0a5005400303580b0090800d03000350300d8074151480321603000da2040c8003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 861888003 1250 861886753 861886763
    0x30224030106260f09010e0c1e1903080304060f02160303050901061d0919020907030b030a290114011d060d0c020f060a0603020d0305030402010c05060c0a0908010e0a 73
    0x107a8064000707018007440460a504503140d4103050104040444800b13901855081e4020301070100204000c0e0b0f643c500c00381649401840001222710b01c0c606140802c1c90328400182500444c0d40d841c2c0648082c2180b941040e109800b001052004021140c425980c154002a5003541030900708140d009000d101000c0144c141600c03000001c1c0340130001c1d40008080c10100030840a41244d4424608209001f00c7d40c110071440360f45403a22408043c3d105444d03405500412610140c0e581100403406004810655038040c840d00d0403600c0062034103140e0101c0442c50f1301480c000c005041100c80d107445810303807168006040031180c0401302d07607000000d40c8008152410482c1a10314000c0803404502c46c00701450b150741d10700704614803281e03400b0400f05055900d0710111003041d221008840115030141c0f0000750301c00c1c4c02d03001107000280100040c550141c0141481704d00754206841e040c3c105030017200d1040b48828002109001036810112100190516800802c2004101d40e042039803040043d001030a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 861889253 1250 861888003 861888017
    0x302300702012303010b120a151503110a0c110d150b0d0203070e01050901170d03050403031e0b030f1c2015011403011802090c0d1401030224030106 65
    0x3c0440750700009a80d0030481d03442155980d80e580103d03c1c5d5540180c80840c101369000301c0426164095801518130314071a000908502c680b410047d044100c1d50104150281130b01c68024200c912200b1015200400090b00d6510428110b480d00000320700b18040910301c9000031a00c4400402d03c450036031411801c0303182000820008040c000751000340452002507041c07140c11004681c800f640c000d828100c4c1c6e0169004030303060740c80745040800c542c090100d40c41c0742c2e4400c41004401a11a42241d0340082c040d040015038030742910070201d0340c03c0c40050520001a204e143d10011400c04020545180c008840078101103040281c1203070a4881c4170b161182084042c00305009440c45444008507901c0c21002210b01440d80d80c024103450000901c60340c00a5204210310300494103040c0103003c2074051401c00141034840396405c100b00c0c603401402803044600140060b02d40c000d000e10440c00310405590a152456140d0700c100300c2c9640030400d8a18015a0000300f0310b038a40c0070300701902d040d1202420100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 861890503 1250 861889253 861889277
    0x6090c0e12010e0609011406060a170a02070605100f1403100504050c0a0f0513060501051608040807080109060509030403030903030c030c060c39060509010b030109030230070201 78
    0x540546a2050f1144082c0104828040c6032041580501e41031280e24114054560b01c0004210043c000c1800800124080d040c15444900f00d044110380c1c08101c240c001030038204140c903950100d40003207030602d5007118a00d209000da1000e60728590004c2c02205104d0240100a00110f40c0b81c140107805c4409240c1c5a82c0030808220782400031000b80e02c40070f80344140a50380ca0302180710751a10352181d41e009003010f80200f4040c00840c000d50081e5141a11454640507500710403042c1c60f01c0c1510160303140d00061101065011050200b20010700c1c00302c1c001300300c643c428180707001164009068003c040c1d0081108100190304481e41d1800c89070541840150f076005400c0a03030740603120b010010002450101a6500d894110204800040d41d000c1c6a41c04264019540070400c11200e01122444a24102110001c2d003503400c0300303902202100001c52010a1040428251116032f0000c03000b58010304003440c140b402e03402070440394840720440b0b01c4044201c054203000314400c507500681000382d00c065003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 861891753 1250 861890503 861890539
    0x3241703040503011107171905090102101b0311090a05012303180c100503061002011b0203120f04020a05100c0c0605040914091b0d050d080a06090c0e 66
    0x601c0003490050002d00000b500c00307071440240e6104110031030f05040b04090380310443e10440182c0318009121585811358440048050358180c10500600c1c1c11485000e01d4003039665075900445c0c13142400307205000080240e007200541aa10325140006e420602484024000ea03a0801d410088542c2030920081d500120365230101d07190100c1102580001000051050501c0b89409211200303407000d003990f91100300d40c0b0400c00782c1c94030a0030400000700705101048951800444c0210000050b00000440c1c0b88807900b242e44003038030042041d000da080810300180c0f0103017503c05e640d0f00000c6001506880d1030160b000400000181c090640550080001482054020b0380c000c15115001884030040aa0f83c2200415650083c040c01000c4e90405089080c0d01c0802003030345000b0860381025080074600561100d450301c0c48002d6880e84000396014480124034240461840d030b40c1c4943e101199480c11000c00800d40d00c4541c0b01110a5103040801110f140c2e001c0e084621403001214042441d110240c0c0f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 861893003 1250 861891753 861891757
    0x1030e03122d01180e10050903040f090c1808280209040f0311010e0c06090a030b0c07120e030a140c030d02010f05101521020406050a03241703 63
    0xc61945211401c1c006140c1e00404155a040300c458000340140d1090890103a010340d5205ca96840590344560b04180320b949140d001142d0000402088038240340c0d071844000d101c09090381c4455070a9998800d030110946c1e11010ba0f881d034900c148010711500c3d15000e48a5078441128204206104d070482e9400c01e681c448214850400350000c0040c28a0b081501b0448403948814030101d02190366519071404d83d0b13006015000d001d02e100d101a0030700002580902c9000e5000403282c039401016240084005920030300c0017801800740051842d1155840d280c0101c4000041c4415070600804844030728080d600018010503099100e08205d1500803801000f0741792114200c011581402016505030605605501001d000300e40040141702c603407140d0810108540e010700a40c64984202982c0d80d040f075000c0c80c0344060884218401000f480300d04107010b000c0344c08c250030010008000240f0f541b0295414050b0a10506100c01720110440c40300c404142a034070284036107007840d9280c40740c2107420030302801 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 861894253 1250 861893003 861893041
    0x7060507140c030a03140105210c1807090801060b03160e04050106050a1202090f010f0504080a0b0f07030b01200a0b040602071b260a05100f060501030e0312 69
    0x11080c2c5a4190054494070380d08404c0740340000a1a010070709560000ba01407290480310042d007445d401400740271540c1d20300c41c118810b010452048038136810351030b00d81c0c0840328503500512940402d00d00301710310010f181d100c05602000305a0f041010901c2002050b03000c07240c200d8030044c4032420307142c00d00300113550b80004050010b500510b000000a00301d600007009028009240d0b070740c0054280c01110420032800360683d01d54011071035140e02d4415500402d80b01590792000d0a100b8209a903c00081d03180040c9107008403010211075007482100c24170074030526000350701820180325009034040002d0401c0c101940080c119100d90108150918080c050101c0c030310b400000701e000350320345070410b0000303980248012251401990b619a0b070100014201c1d0f41a00c803d21040ca0355020203101da118014015001001300d400313041c2280380094410890404081f110b9900030907440e100103010011240c10703502c40740c189400c00d8088000001c01100311002c400004c050440356884071030a050001c60800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 861895503 1250 861894253 861894287
    0x61a180d14120405031911060906190c02011101021216050c01062402030c0d0c1a160f030e03031b040b070c050a0f06051c0b0415080d0c050307060507 66
    0x1c002d000103280750340024800e4800650413074140c038640c1d0181c061845101d0320080c3c8040d40e03c1c610003410b468030500411141d0401011241800c240904950807800e8900d12000030a041d64124021940c10640401c81456400001c5060040081002080c0701c00100f80d4a220f00f0b541051300741ca0350242060b21100c400307000080012903201c0c03043c651100c582c483e002c104ea101d44040103560074800401c40c0e040c4001c540160869200441c2c0564640c61500c400315500c48010110348580c0d0000c3d00c41a00c03405030300d1a00141d4180c2c080e0043d003010801e1380c01c44101070400c03c0c005023002000003207c4d0414500381280c107007400d419180c1d149034026070f00a908400c1000490344d091005018540064810441d043c2855a5695803111046034035841000089001401125100c400200707800c80d00700010305003c0750394812400020215811991113800c00384c02d0304411700c4902410855151030030514100019600a5500c03001d90780c1c014110f0041c804c035240e900103251184500b401d010306a26034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 861896753 1250 861895503 861895513
    0x405030d032a260c0d110909041a010b03130b130b010f0e010e060d11030c13360b1302150a020c030d120905190501061a180d14 56
    0x801000103285001c1c1180c02215182c02c0b0030f01224503940a030040c01d0540d0704500e088440e1102001401d5a44003d40480c04144000035680c0c4a00190030310540c441c071000400b41403040f40d80c040424060b00242c20741c0c031087c0700b08444245a1044042031a070409400543eaa8510f083d010f4000c0840000400c4001c0c5600002030142d010b00b00d21040c0c0f840395501200760ba0701c4102c0c6960110089450641c8001e162440402240481200108082000d0107071001c00d4541c2002c0395800040482d443c90f203545d01c40c901108410030f0000d900301c40010210540a0041404403407509510b002c00140540800c0000700310007024500b05030030381a5020306054928140003211610581200c500a40940202044071045e86400b00748440c4c540015243c10302d0380d0340f48605060050080c04c004884130701c6030440008a281024a5004d54a4426000403500904060707030500b10b00e034101ea60521600d414091301510561081d5442286c05c2d00751800d601c00003042c06c0c02d01c82180d901c00408518012 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 861898003 1250 861896753 861896831
    0x10b0d0905101418120f070b010e06010201061a030606220602031810020a0b0a0204050306010f031a070905130b0907020604030306060e0607081812030301060f050405030d03 76
    0x35800219904401c40c0c1c80601e82d03910760a00000d000b030214101c03011034100e15000948201721001030803c0c10b2007814594240b409590b07805031041c4082e00017480340c0d00f101c02080025079090003014040c2142e40800c04102d000c00c0c0b02c006203400081c080520400003c5840f001c2120a0080b818844a1580c40c2c1e80a05a0b9007201030748a6118000700d10400c00b400041c0400b5042014002c80c0b0507000750300a114480300c43d161800b080e40d01400091480b50208000600c550342001214040d203140c1e07450b40320310f610758035040da03003c1d00303205003030249250000401000300c0c1c01c22118821905c058614042d600540024a001004d0f2900d445500001080a214039a40d001400c11b224a200740c03802c00500782c40b4041902d24440e25404143e1100d000c0008100042c50200a07244281c444001d0403d20303114000020310505810b09040042c2c2c1c804001000482c3e0f00410400112002d07080c07292400d41040040f9440c0c1c1d4445042d9410305898600221800c851a10214403401c404000a8060b00c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 861899253 1250 861898003 861898033
    0xf182310050a1d151918050f2502010f0207030c02031203090a06091110020619060308180f09010b070506160905190b030a060e0a06030b010b0d0905 65
    0x1505018a601540310b86101090b1011480c8581c00000403884030100b1598550b040302c58003080500380c0c00d8002410040060720790b1070780b03082c22000d003c84402c141100112190114200c90000708506501c1011405002604d0646000456500a2403c05005075907005c54180d001d01620610500100e200051040600d5446210620a54401c900356507003140604101d00480c00192085c0360313641c0080300b040c1c0014000754004480584181d0424131940c80c0710300091a002020601400540c02103410080070030100b82d418801c248102004228007403c40c0c64400282c0104107106080d500580a0f4210035a204003040c16881c800a00c051744a40c0c4466141c0d2480c1c11103001152144500008555820507460355020303d01c1995a0710b052a6181070304011241d030050403202c0c1da05600c1c0c18007040040840000350300c01c0c1605100450403519108a905048500034004602c6c40d01d0944140000ba50281800e4115902d41824989a03d04a141d0310004d04003081d004016100f001c0c0180e400d42 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 861900503 1250 861899253 861899281
    0x9040f0f080f0409140405060106050c010e06091e012f09101e020604082d0705160e06092a070c090b060f0405010503040303090f0b060306010f1823 65
    0x10b00400c8003171203000c804660704a801c2c0c20170341d0002c0c4980c11800040c42031724030400141806500d014004603080c0240d00c40c10303086c51030a544c14091074002561051414210b07510040f000080e030b00081080010303007440505440410f02822801c0f01c80c1400c1b4080c021680c200b07683c01c2d403030024100070103444200406030120010080041c51129000108240780b400410040c0c8a00c1d04200554613048044910440808040030040c1c19940c000c144404d020f601c0801400140340324000800c40000d203840280c105601310f40c0302031010702c01d040810000381c03103e0308002d0700300070300e114400007a0740b010301454a410402080f0110081010a0242c240605c200641d821030300b007140f040000e4070101050001305c0c841c040e42e000e2a400c04000070001035100344011039121f40170745000560341d82c6a40d2428050b40a4610a54130a01d00b0014004686018800c103801818510116890185400c1010075011181040511450ba82d1381d1034400c10b092003030003c00c1400704100d08800d24034000860741004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 861901753 1250 861900503 861900509
    0x90203180105070c050708150417040806070302071b08192103060e070c02060a0c030e0a2c101a12010611010b0303070206030a09110303040b0702040e01050609040f0f080f04 76
    0x284c8501140020302c80e00119111a20b44c0940023480c20030b40c0c668664501c0c2805500eaa0b90103001c003040300140d070742803d02415003d00425070b40560382e006203042c111076002400040c13103040180c05100300991070f80010304513101240039644640d00304031410075982400c15150030400001180c000c0c8030507168503a00c5a02a14810044540261241c05048a5010780185c0c000d402a0040180740c1c007880c020706554459603c00d1030020f41001150000c152001000c0d130103000b03c94a0554a1100e540044084a1540051596045191409000028440701c803840303007a1b80030b0200000e002c8000042002c40e10700303003881d4048501030b50352508000e0130340d00d00c0061a4030303d51034102c0c100401e1070007001310741c00c0c2900284072608513107545110700020b00b0b00c42000c4030484180b5100003010740f024070180008141400800d600d9580500502041d20010300201e680c0c1e0749010204280c55648500c0260020b0b0005107500380c8021624151a10902030400a0303e007481c045100180784503030000034419 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 861903003 1250 861901753 861901763
    0x2a2a060509130911010c080c0a060902120c0108240301020c07030b0f01060507060b03031c0221040506040b041b0305010c0f02010c020717070302060408030a03060b0c07090203180105070c 82
    0x20070010500410b08598503480002c0200c0e400400007100d662040b0040e0401c14000da1100d8900001c00304150b2901e180c042080781e145403035440c0e031020352900c1c6441400c9641000701505186050000080c90114014003c100102e8041850207026180011514840101500865903104a80100d954807905480708a84100e042000110a000c1070b400d13a50480e28030f0349541d4281045603503004040c044c0b581e00315426100620444202c15090319144642c1c9203884030041c1d442d1400c1d0802101d40828200c14042c41500d0001d1000017580050142e034401d820008038031043d00d80381741c200c1c00703068180019009244070100100600006600c9001c0c284200d8480303010001c044003099003a242503440070b41c0560007400040208210742841520565604419140704903101e82c00502244c0107030b044240503500204d40c2004107501841080301030101400114200320880c07e00c03540e640c0700c41c0203c0ea4100d4004c07000c00c48070f003001e030700c41e01741e50b00d410000303002d14030300003c0007060b03080f0000c01174603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 861904253 1250 861903003 861903019
    0x503120f01050307061205131b09051f05040b0a0f0803030a050f04050309010f1e030e0c031c030b04111b011406013c0c032a2a060509 59
    0x1c2c0c245000074a840480d00c50741c4802206162814190004100c003c100e665044c202041203400221481400d0950240c00e02c2c171000c52604200006044900003403501c008602850441e210b003a2841480d02c040310011034002c540ca485000205440348407e078030003e40c0310100c403001b1503c400c2c0800503501c20400c400c010007140d903444040c0342d1803600540c0d000d0082e0308100810f03042c030352169800ca04020424103000c100820030140c0180902c01c4c1171000000240d5540c6642504c2d01c0070b10072615400c000300d00420500c01c5059880d040035403c040110207050341c440c60401030b515981c0040d1002100e29011644bd80c0e550b4101c0b840000010792070708034035460400480100490700e50100d01843c01a0b50312035407041329034008503200c4c800740304035409440c046010900118040701ea08812082c5e82d9510000b0200d1407030702411024984000b0403c0c0021316039402c0340740d030300d05404825068110076440015044040070340503001c1004003404404500c9440451000c2d0010001c0c04841003d031501e46d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 861905503 1250 861904253 861904259
    0x70918050d0f1d0d080f09010206011a271005070b0a090b0112080c1606020601090509190204090209010608070e03010902130203060a24090920160503120f01 69
    0x140c60b0b04415801e10b000c80d001100d4440308148503490300d540c90300c01900c1149190950b8031030241c103420042c16012001c00c0014542080e581c180101d40c010304002004c07400303100c00304d011202c0600500811105c0e1548521b188141c5580701040010000d002414800c1d0303141e01d882006140b03511211083e00d68840c6140440c1d8600c415124441c192034004e07842d58110313400d115507108944070041060324240310070b0100081021007403106d00701c0340c980c0300715015260f4609080607041c58416030001c003240c0e00d00344c20800000400f0441c2200000d15090462100404d840002e00800031404041e40255000c0004140e4540003c10036004451645401c0403408800e02017600f650f407400301c001e4226240c0791510f0341e041e4654026580100c03004048440030364071030145071000300c40d440181c0b00d0701e4031446e03021380c030590461b540e0805031010f4001070010f1030703801201c0b05041400318440c00103160000f4980d41e0105c210010903200c240d00c0000c2d039940301c2c03200c00c0d503074034180c003e80c0d2510304418804000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 861906753 1250 861905503 861905507
    0x31014030a020a0b09010c23060108120712090e0403022118042003040308060117010e130201030609020c07090e0109170708130602060403020c101b05070918050d 71
    0x408550003400c43d082182400c100328035176040b04562034184082d001e5003000040740c0982c0c42c1244191000d2000c4000c40035456540b80c180103074090f8803660022240c1c07042c208050812104181c1c0c000c1030f40105d8082c0c0c010121060120b5611042d031b07491418007030004042e804500720300da01d07201d801c03446948070790607a940c90944100b48521170550740c490002d14032801c1c10380040e01944104240700b14640303500c18607100d580d801154120001202d44c0d041182380c0d80c0101d1104c2036108800d00800b280d6040030910440035501a0916001c5400903041c40116031003038012030041d243d0081c1c10b54030303108020016552060300340a03041000c0d0034440000038400c014400e1048494102824500d61180c000e903400303481d40000c0c01582c0c00501048014280c0c0b07218803140c1c009010729070040040e4034050400a0400c100000b110744103200101c1c600a01960044411050011b0a003400d04150100e103803031843d0403039580c41110301b24204004400c6080118450204650041059415079400d00d030781 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 861908003 1250 861906753 861906763
    0x3020d030b030c2805040e0d02060f040f0602032e0f0803030f010b0a020f010c09030317010605041520030c060106020c0d17070c091d0309090708040f0803101403 71
    0xc25810807400200289134900c0c44800508001c0c2c01c2d441e40c0070f080d4079200400c0650303247d003001e11540d510002e9604202e60b0304201b21a842414109030404c107060590f29400f82081102011f446035401102103103c2d0041054007860450744010840e040781c95989a4000203502c030b100b030700c0d0a51103a0b8000180140040203d034454415070001c085a6800c0c0300344131100782c01428443e0704502c0b844030308200081d800d2091982c0408070b9110800101d2443c98000c149880f403541c1d40c1c01c40803048004000300c0360040283d45c1903c141414041c0d806003c0c110441e072a03400424080e0101441607101c0110303040102c0103111540710201510707004da8a41c9420380e135903410501202e42203544400c581c004030303030302d09403030450340c2c0c40025901e2808540e51030f259404210341e0050710b0840d07034491651000101500c0c1101c0d2220143c8099030801044000140c40200300804600601821034005030800418401002441d0f40c400041c1c1e4407428201000344080070303940524058010100c10740d1405140c000b035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 861909253 1250 861908003 861908023
    0x409051c0509090406111603020c0f0303120c0307031401030b01080c03070f0e07050417072108030c0304050309130e240402010c031814090c071a1302060703020d030b03 74
    0x741c50042d03220350385c8400040c100d49010302034400040c4840a240040524440c0c1c1184c0240e0041c400701090a0400034010304100c1e11511030360007046880100b034034840c1d580360710000311030055860743e603807510a13805482190450345074904840000300400c003007081c141341a2180c0301e088a440c20360038014159120568012a4143c5407040d4003004042106001d11368004014a07060b400c081e66103210301c410302c90305030101045070000042400590125628500c0780c114648507120488040e468070610761002510204040c040080020180708003002100c50009000d03080f403208c0e154964510b40288500524518180528552140c04010a202400c0040310b0620a8001601c4650040d940b200010398101e00b0702c082540d511395985030201c0c02c1401403a2004440d448040d04000708049020300500c1214401001d12002d000b1402c00295a000c150f0100301064103600c50100c085820b8850940003540b2010000708031080541c0031030720421384507141c1c0701440703444101c004042d15001d50301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 861910503 1250 861909253 861909259
    0xc03110901080304090b150304030e010e03010c0f0c020d02060a08010609091a010521130309171f0e0109110316051c02011b1209060804050c120c0409051c0509 70
    0x101080c404007840780e00001e03200400811f01207041039245400c00480d0811a41540443d000035114800755070800c809141c0e40030101c008028003108030304007403c200035a20b109410840142103a00454898003e08440c1940050500d0f072103006802c001800841c0074010140000d0100400003100c500ca4041c101c410010509052195100130004507901d0b0812103041064105074900c03081840d00300300245005007a1448181c20001d07c43c00c020b010f0103140d9000920b0b1100044a0410300500441c0410404035600e1648801c8a5400110005130130101d00c0c1c0600c0e0751910900300b08104010884565420b001c0e015030381075070381e00c40d09851058103030301c02e45400403883c040c0182c601281d8603184001e0352050504501d6441c141c690a45030700c91460b000c403107200181000c0003030150010f0280000781080c3c50411003510b02540e5442e200d624038500359000343c07043c090b0840510800c0c8040402d183c2c025008106051381418040d50300c18503002001c3c00320085030095032001e48a2030031251401406 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 861911753 1250 861910503 861910507
    0x3320c1f0c052512150b190806060324220b0721020a0e1212191e050415030e030c0106061d0109051504030803040305070b06010809100c12090c031109010803 69
    0x2005e09100900028510284e010305408005180a0032000c51200901440d00040c145454100c0c2410318001040c941c440500c140d40d442c0d011821405032503141d02c929031702c501b0103080001d201c01c0407601c00c025000914445884041102442e030011620303259406640e1008034684403907206004070300c110a442c6001401446001b151418250114202101c4580c221403024130a528143d070b40d40c206c0d14034100714441c14151a02d0741c0da841020945d40301012814500c00300c400c3d5001030030074800c91040c2001d03c41c50021409140340660705c0444008a20810f030380c3c2ea00710010580c0e000700142d02400c40410900a42c940d00000000c01d09001d82c8010b031a07040b13045090004218540e0040320141e4202d00041201200081640b13000e140104d110b6241d80d619825249000e00507450010074860400400c0380170409102c00000c0c01034550481c00c440050301c840c070045d049880e02e1018103446808c9042c680680b0802850184403405c80380101c405d607889001001c00c014a40c502071240894a13841 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 861913003 1250 861911753 861911783
    0xb010e010801290c1b150301051c050c090f0a050709081b1c03110705030a08160c05092410022503320c1f0c052512 51
    0x4012000d00315070f105400142d0410360701c5001d041c40d080b0407910000d600e5521145c0360702242451211001c0009a040e0700f0390030340d8181008600b160387da220f10444038194400e84e890a100c024403c480b400100a0b1041c00780d440c2c80c03140c1d410b80340c80981d0a001201d03e8500000e100c28801c2200341c090702d40c03d401801e40395680c003040301605101c140c80d071544070065059100446134901d503800c003142c0c403030b0301d90a041c05201460907090900c20b80c01140030703400c101980000200c880084864003801440c00360541c004070306002d45014816045103400c00f0941c02400017a0341c4061480d5590301091105108554603001030001d002060581e0320b01582c48003260103900703d40c1c02065400700d4019081307c0c1d281a522b13100d010240c505145910b86001e000d07859980f1591000601041c1c04021100805110923120f000c61a44446583c210746080400c44808114901c101561108580c21100700c88042c001d202c403022030710708030140c2c0d202d03a80a1031400162810140103c1d104503900502c08860360300b2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 861914253 1250 861913003 861913049
    0x705100e0601050105070c240906080c0301090504060b0a08010b0a12051221040303020712020303040f02060a03020d05100f0e090a0b18010c0e03010609090b04061802030706030b010e010801 83
    0x10b0303201211180300114020441d418580a2650507840034658103523219403442028010403002d0700908104a462420018107510071000c03241150000740c0002081d60303c504040009200307101d045540010310402c00208001c05401c480d2102c41d040361a400280d5649003104a60256142d004103107400140080001c0d05610b0041c0102286001e801c05140704040745e507002d1500121401c0303000c40c1c1e022400c80240042021150b20511040c00294558103040d11070321425400c058009100b140d0004600000ea44260181c038031011905806000a04100c60b0000c2280454054004c4780143e11100040503132142041d6130186001c007001c0e0817030103c251030344082000014410740c103401b031408132090789400034800c0c00c40c05183e030307910512122010000c240c29540d00f0fa11040001c2c2c1080090008110590113880c0c11660004c00020600c0c10b420303240402d000c00100103503040c0030342100064000d030541c2000003540000da0315048402641401910411801c5c0a0003031044a01040c40300e0400b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 861915503 1250 861914253 861914257
    0x190f050d0302011b12061502060a0c180314010b0102030f0d090f120f080601030b031e01060e010e0708011d2a0d0f11070203061303050f0f0705100e0601050105 70
    0x20701074400030501c0840580341640c5000c20007008400220312100d8000071108038440c56020300209035072002c4a00004e00c009594250140440036000d035106a0180c40c80c0c0281303000451024103411901980b0707560b00307051401518a52810343c9550800300e500150390b101100300d5200c14040c1450070300341400c0b000b10304000c00740c510b000c840e07442c104814403011901c1d406410341c2858042c3d80d0300d008602905001040d825000c0c004a052600b0068800326540c0c1c04660b40d01e00020842000c503050075039204080c050400c5501109840c01c2d42e03030010491048100100b4450003190b1200c0c840750343d0b100c499200321a584418200380d0000d04d40400c1214041e150305540c51091120319401c050640c010110403684101204100ca40d980c0220250b80740850040010f0421307940d01c01410210547c011903107070b050081c000010780c4a103c42513820140140243c410304000c4040e0f5684039030507500049a10360250b03406840030311032001c080d072009000d0f0090043ca103c1c80e41c05400359910304030055800ea = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 861916753 1250 861915503 861915529
    0x6080903070804151b051e15040501141f1403150c0309011503020a09051b18090a09050d0509030a050a0b160c030f0513031a06190f05 59
    0x1502040240e08003007400e40015002134204459204406a44094082c00c40184110150031202001c0e29110101e400410b009180d40010009003052214100030170341080078022542c04416514401c2c00103001d01540140c04041144150851507112821a4019090b404802489001c0c280300c0c02d011090b42c90446451841c13010741162900140c6008408016100710303200d0500751004410419070790001d004103d440c0f094451504003890940c0c0204181c54018010581078940300c8020031549068028100740d0468207104180d10b4054602a110300040301c2d2201a00c5401301c0d90200e07103400f90328420615001d50241c01024032817a8100d060396036421800300198140185007498020031011301c20105412301c145000d5840386460b0140d440c00340050ba03458410006001c000100103500300d517a403110300059040041d102c802c42001c541c40c100c2c582d040108000002e44101428003c88400c150044a04072030003608600000743c1c010310540301d0f1007056491000d81c882080782c1c0c00c0c00207030a00301c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 861918003 1250 861916753 861916771
    0x5220509071502070f052b060f0c0306031e020f0a0b0a020c0a06051b03040f0f080d0e1e030a020604150e0301151424071b12080345060606040608 64
    0x80144540c0070b001c0c0c0120300c41400d40b525909e0b0018001c10048034810174803090300c182410007005065403074090f0f80e012040d1300e1040388800000a04155500c0804800c14160300500101d219134a41501c400540c01c1064004058072500c030b0310a950349003100016040e10216a0341600b04031003400580b4030401c5110880c111400100400328000e20700f80c001074094003410b00261117184c82c021a840c03a01814074041001c200f04080e03408040e5440c0c00c40c0f1041c0f11440250110589000c0c40064141916100c2c02940b00303100150018a0440040c13403640b454180351a00c80701296a0428103082e140342178451f501a180d00841400100501e9800c040300a5000c1c1449075140c2100d10000c01d00300a14001d002c000b00007240d08400c0054507072004160603013a043c00c6002c02c2c507003884951181410000105844c0020000401c542080000e0703115048000080040daa900394400000d458001294003420301031310180d0b00480003000610b240140005415580740502d0000111007443c0041c00c5400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 861919253 1250 861918003 861918049
    0x1d0a120b0414010c18140f06070c09020d0e010e070f090c0c060903080108100b1309141606021002180d0201050c0105191b020705220509071502070f05 66
    0x314810903c41c4450790403da0320341d0068049014044105c2e0189a8007101c00c0782c1c42c810201d07005840b02015081e03c050144c0e15036455452503d0041000c819542003109428030120300f8021203440c58001d40d8101008030020049a400e6086041d162040c0d4000ca00522000748000c10040909502c0307603180403601e01c1c042c07001c0d40c2590342d40c2003543c40c0d221046c1c0001d0032071401404400e07024072002000c882078140c100845009180442c040d900c00c031002003411903503048a54240800c0c03c02d8284010396030002e8449588402000c00c202e55904e02402e0f0040c842c010514090500d507100710b03109a881c400030040750a040b0010005410013000c07049040020501c06102801c800b402214015003039000300894100070700041408582008174103144442c0300f2490880b0007600031030b040d802d94006031421502c54110162001c0703600e04481d00c10045610b444100001004041540c1c4155844101184000c03501c8210403a40c400b0399000d901030030030903104104550314101900c1740ca140e081e601050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 861920503 1250 861919253 861919283
    0x6010318050102040e09030301030f0803060a0308070f11012c01170f06010201111912060f0b030109150303090e1308030702010507020c15040302010e030c040c1d0a120b04 75
    0x28400303084010044034941c2d00800c0c24003010400c4012158860100c03002503045624540342d0540245400c031000d021aa400400700e00302c0e03110315107148042c540100c00c0702d83d07440d880c0c42d001010120b045c600383c0303c039080c40f4140f6400d5840b0b00c203103014014402c401c14120004022540c80c40e01484003d4605120b803420548500f40c0710601042d1242440304c110341b035a841c20300c0c0060709403401070302d0b010b0441c0703c10049104004d10442e070301c010351400e0346801c040340600404841c006002a401c40d180c2c2140e110000140c0383c00440095060780c3c4118010300202156400c4100c4030005400000c000c40d41101c81802030f484965007290f0301036204140006c51444a07110482554002d5404070b0050b5114020008030a030104140a40c2c0001901d02d244d40030300b1840840414020780c00000e041103c1500421a5550100000080c1c660000c008005d901d074201000740080007600c0821480c2d405440c010191480d0682c0c0031022941c200084061a0300c80d40c0d078451403103d00500c01c60745401150402 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 861921753 1250 861920503 861920531
    0x6190b0d09062a0903080301140102010e1e15010f031403070b0115081806150102030c060a0b0112020903070611190b18120a0c151e0c0c1a060103 64
    0x410f52030200079034210074410006115118a4400106400b4001c10b03036020000034400b101140c0c1119011a4500c0c2038801c0e1200407405010064030010a51142c0003205100100c0b030f14811601a005204440404608071100d64070f84c00240705003040064141c1040010482002c1c151b880c030240102680c2c80c060a59a038080171000a07080340f40f01403c5046040c2200b6040a1200e410405002d9400c0400501350b42d0250303940002003d282007507000314401d40311a4020401e580401204034281d80141ca000c0140354020007045024030f00140704080c03807a0511089100b103c444070805800781408600300101a0741803004020243d05910903144400103602c10902d0400f46103128a580c070f00c090030045406e61002004280d4a6080c2d0400c941110032483c40f101141c0044465040c0001000303101d0410100d0104c5a0307400c500024104a8101d000d01c501d036a5809068078051410844030758000720848010481c40c1c0000c2500d1030002d40c90036902242215290320a40501d03010138091818011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 861923003 1250 861921753 861921761
    0x50a03141e030405040b04090f1403090d060f0606111c0e09070c0219290c070f1802030c0901030917072d150c020114010305100506190b0d0906 63
    0x815401e504085400d20071494140107021303805c030080741c01b405424002d80301c00541c06031607040203143da6500581171000308403d00550b603081000a0481611072405e00b4800003421806140302c0b451407820002140050040282c40b0f0794800c104002c05440a8410444890106801056043c840d80c005201110b070b07289071009104801a5035a001029214070512070700b4501c0340001000580d0740e40040c402c02c01b08001105e01440031480d41004c0420b00c1c04240c10500c80c0171404405070242d8000403a05591440a000072985400c00e841c8180c0313254407000d0103e00041da081c001c0010304101042d420f62081c2c2111003418061401400380da075001c4080c1c200380d13101c0c6000311f41d80c003c61502c50b1040d1524407500822040c8555884081030120340e0f030b445509461004450f030310781c1d61b0402020010300c01d50101c1648a0040055406940c4a087c181e50b1b400720382080c210080d003003200040c0d06040c1000b6003c12590b101d16090070441c100f454030007464004911038852a5690b11000020509a010b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 861924253 1250 861923003 861923053
    0x5040c030e0c120d200f1b06070803130201140c0a030810030308010e0415090c150f021216060504210c0f1e0b040c0f080106050a0314 59
    0xd00158468410060034102140c0107002840b5810780348400c00c10010100d14491140480d01d49000811994207070202d05140d8242e5a4580b40f140380d60030030100c000007849402c0041840c2c2d181956006100401c213040c4610540200558018008141200d022400f1050010310505180d07003000101c1c00c031840d15070800d9295200b9a4060301c0d1aa00b819004003009401800d00c12219a003541545c030003504a00041c4100801410100b00282c1407010764400e01410b101c410b9014050159103041c8130b0503142c0b241c081d540144601c0715040048501075054608041c2141d0042c1c100c02301a84401801c0781c2060718064450b80c1d6808500b00024500c4c411980310714802e05484488000340800c030051900c10441e90418070024410300c03008652510a0071002950290004031400044010b60540413100380c0020211070b140001c1c0300822002400b50800c0d00e8003000d0051080e60746141050a80d1414891a504401c454105002060401041c01a1103207040216094510101035007003c01001103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 861925503 1250 861924253 861924257
    0xe0f0f090c09011215031b1802041a1602010f140c06180a0506361b0f0a15051c0c020d03050c16020f040c0e03010606080103120f030605040c 62
    0x103403003450f50f8000c2c10b040707480c00c9001c00801c440b0a0300600001545964040a0249081c0e4050001540022010790000d441e65240d03114010103940e26040103034010f4080ca21000400040001c04c3c4c080c044e05403480d54144100c45c14807aa400d40055840c00c0c002d031103001c10020340042006061049600800c900d0306000000c00c0302d454100c0c0300842250413501d10015a400902d00000426000555990052100d00a450946170000307190080488283e448043e200707131500d60500c1c0d0160101d00900d03140400c04800704020048400c0200010040f41000e600007030910050085801c45900940d00b5044c41c2840d034909100d042c0c034820301d4000c050714a80b08944540498102c1c55060015110349071141c2810b10032414440201c2019007e0410540c4c4040002c1410005664880080c050f8004c0f006d0003c101507080c010000707000d2100f00c1003c0e07000b0342c240003001504900c035680a5040329084403a00c40f01c0050343c1403c03103282001c00341040c01c0546550021820f9659031007801c0c480c281907 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 861926753 1250 861925503 861925507
    0x91202130f230f07020706081b3105040216031809060305060702120306090411010c02130b180702060c130330020d050a05070804031a0f01080c010e0f0f090c 69
    0x80c806843c100038622411500840000c00c41c0c03d070001c1c0d1040d00a11607901d00e00d5a038035640c5082203280039003075125030103000348075034054501e200c07074010140c40f05021140e18080707032100203000903480f80854034480405044220000f00c1c2c46614110440c00704122400c904940d42c0c50074100703548171030b0400e88550f007004043c0051181c0412059144d4580d60441c54114070b45640094000b6078001c202070710440740340c621403801c2d81c410000003507070b12360051501100c0c901c0c40d958000201914210b13039002d90014040314901c400c2038098035100310b0159005081558945445402ca81c0190b50b0590200011003800b00004a641d10548a0702d8002103028441c81c0c400b081c04a4100205d18040d0155000320403040540c951000842d80a03e5403800c0095540580f8035010f10a40b040d913002400c0c0e25188201c607400003c903448254002e61809141258907622000035036258803a200c001804aa0304100c42c1881d420505907100301d4500062100020098800200340c0454044600c44400940 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 861928003 1250 861926753 861926761
    0x4060c0f08070e0d0203101b140909010b2104050313140907050a0e0d08130518040b0709090c1e05040602060103060e0a170a091202130f23 61
    0x2001900d095505020324029405007808000a0100c228284a9a0240c2006030b824030554900304824502002240f0042048070052104803080007805500040041d0006048c00740b20f010030300c155007040c0030003003c5031406d92801030b00704521b03407001e640b51100c211000104101c804282c0038035845503028cc0007070b41d65130301800700e0089556200d821403d81c054601414900c0d6444003c0510303400300c0e00382091a602c00c85803000b682c0707401c0301510703581d805400c0416241c10021540050905170748504c500e0300701c547e12041006044c41c00112a4030811401c0e50015000ca185460700301d801004a00f801c107012078444800b42c050744d03400840a804101266130306c0034400b2448118081c3c00c51680341175400c140c10b10300025110201840040d0120742ca030b450640c5001814010390202d80e50040d626094201e107200303e030280b500006290404940e01c1c00c00044d100746070001c0e40d4202c076401010401c0c44104095090000c06407600742d034886698418442006c9826500d4081003aa43c204d8440c21502d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 861929253 1250 861928003 861928007
    0xd0819111603181d04021216031a06010f0309060209060301170606030106080d030504060e0d02061801050c0f0310090501090605030708011b2601171011180402040503030304060c 78
    0x440420f0040d1910003c0c008220740e0f25150300440380e41c0c0b0122400e801540304e0f80005030758419031020914807030045034905c5003165041c52001d0200c9204e5107200140e02411080382402e55400c96100307011034107a0780480300c4103100358032102080303100707240040c20004641d003c14a5a00260884c0c0084d90446051040c07131582005042da00480403070091260f5810282420703140c8000020350740c141516500498104a0103412240890f0301032011180718015101c00255600b905a4030055000e01811480720300150601901d440f507030105415500d01000003c0300b0165500c02080445840070000020038460300c1c1d40140f90003000ba2000200d0028100f604160400c00c0d0340e03001d910268544004503443c0e5600144401c1c50111908046a842d85009200400c4008140900a40c0144203001013040103e441030840381c0003640301111003e02940304414100c4171003803403a03c85002e05211403400b00400701c0d01d0f00b00c1e0120203800582440d40e06d0005c07915641050345c0448507661a8240c46010325 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 861930503 1250 861929253 861929267
    0xe280c180902211f1e0b090f06060306060d020d1a0312120105060318010207050d03050c120f06010c020307080a05150408070b07050c0607031a01020d0819111603 71
    0x9070f185403081a0098980031140e583c0d14140280001c900543c4141d40ea03000140e2002d104855200c1044002111151000303000384141d00050780304043c00f40208284000c0800618800c6102030121451600c40310100429908400b08150350070b41c0070410304a4a11140c003941303070740070490369603c220700c41c5040030141444420704105180110030300a0303000441500c0800c44c11210242c0351380f0b58a88821034845072046c99640031803c2c0f5800000c070001005000148140d180703003180e504010a0301d1340242c09200340308528819442d102d40c540030652003118003803825000501410140c070000d0945c1c0c00300341408081d5028001c0d50b00181e2050040c80014070204070550700100300d80b003080ca4255940309981c001c9410290440c40e9100c00601481d0044040303440d07148084084414900e0001c000a000d400c0341d14002003005801d034000481d55000003203034104101c054841601c103a48551030801e001261001000c0e9658480c003003a0600c542ca1001001c8115000d64094805403560034050810 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 861931753 1250 861930503 861930529
    0x1c020708250512090604030f030e06040b090301110405061902011d0304031205070309060e150301032004051911090a0803180a120f0c0323010e280c180902 68
    0x26034200000b02e401c0e03550001b26000d580d400400c0d1810621503040480300140b621030600e070004000200071644030440005000c00301e004a00900c81c0480c00c91441540d03019900c641c80c0c00c42000d222240e118030b0600d0061a118280b8800011100d6038000e0300781911901820010142e000010240184280030540080140e6903040c01460104a42c4d070090461850348981d5080003e482d0203d0f10f01e0340e54400d1130404851a402994403944c6904007000e049030103e5400120494139404c0d11341c6030078180076062040700f81191a00f5410303c2020848007500c0d240100f191000710410001e841c0c4c0d42e5504a134805070004100454807801d0354007278074001c0070308031840900c50010300804110215070341c0009814968003554003c0901c0b2945003204c0d8810032904000c0c2821158110f4000c1040152200700e01c0c0711100009020800354001116116110043c80c3d01e00d42850b000110082e85400064000c0e1601c0b490500c0482c559940718400e0441c034801b0b40141080d11440000251b01e0105114468 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 861933003 1250 861931753 861931783
    0x207140a0305041502010204050619021902130c020f120324090411060d0608030d060e0c16031e0306050f01021c030b0109050a14151c0207082505 64
    0x9524607200500781c3e00951251815507844868018010740c800e4040d01c00410014001c1503c0d82d1850750b8207118a03414410000042c4201d011800c0c070a150600d400300ca04e0380261480c91843c480c802803c0142500fa54403100758130416111070300c540c40401400d03030040301201807242c51b400c100e00c4401003a200210440c080902c410345d05a22a03813134072656074000f82e0000ca601c82d17564440000c00e000307003e00d11281036030a140c02000503000501000800f214890b25608020141d210650007500920a5818285d0300c0c6007882511075848180b10b6218013207000781000843e189100c91080d401c404a60081c000098440d0304c10000c2d07051081d1458080c040034000707041003030140000303000660341c8240341d802050307241c04105509900401066010301805070428030700c291076030045522146180e40d210b001d0243c012081c05140503820a50315400c010030080d05030700c006010107402a41014400755013141c0c3c2000744481d0035809540180140c48844000c8401c1200384c20700f21700301214810402e02c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 861934253 1250 861933003 861933013
    0x20909120306040b040b06070c090e0703031706010c0b0424110a0815030d110c06070201050a050306040f0c03050f0702010c201606110118020609130b0a0603020714 72
    0x62000d1208041da40d00c0042581e00141c44044100000d02620031091100c0e00000c0c0000e43d2020701c20124044c0b001c0e6200d180007401420141130707203a43c1d2000e1a120180000306016442d4181860883d10716410120514192051304115118108880000e8408072126443c01c1841d88184182512038010b8182003181041107401c5c1e40011000703072241419280c100412200024601021f8419440c0c1200001d41210892266428003170408545c02e020803240d0300c6040701c034034001e1802c442219440703a8107940303003402d01500b204141c03143d2304050850365025450324041e00e0391400d40e20840341551002c1ea4007041078100251a408022702c003030540002c69041c19280d1011613040003d400d0f0100ca8100c0403041424004a01e038140703820086000602a01414001003030f0758810140d000000c0c0c1d8000810041810701019070100500c1c0f040203400c6582408580c03498941010a241e1454402d44003040d2500400d0000710035604503080280425030100c0e40905001e0f50200034a01180a400284 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 861935503 1250 861934253 861934273
    0xb0102010b0a09090321150b030c1b01020d1506031808040b0a1404080d0807080403020606010c06020c0a06021e0304080706020c1c0c0201032906090303091c020909 72
    0x211080b0150003806001034880c1c4031001007510030400e848204e051034092042c0c0d161041003071700c007510700c81d03040006060034014041141040328040300c0c05048201620303850f08003041301c07d0700c00c1c000305000b0b89030b5550f0900441014003000d0080d010049402541141852700704113000e81142c040e040d5605111f50240c1d460390005070400115410740d10108042034580000200c1111102d03002116160640ca001c1000524040001003900c5058420384490115607152081280ca04200f214003030010382c002c2c0003048541d4014981080a180555800b62810016507525860034810880485119a00040c1c0180d4070040c2c0042070101c00b0701d4000c0c1440d6013060749806201e801401405040994002844241140104024140c10010072401000d00d0a490400781000c4ad09050990103c0c0c1080352103c410411244410a0049080308070011000014144040d6070081e152480e0148800c10400840356500303031702e82c02004039024043d40c4601541c414081f2140001d003140c903c50380141200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 861936753 1250 861935503 861935509
    0x170c010906144c08011b020309090411060309060609010909110907091703030105090708040320120d0e120a02071404090b040f2d0204020c210d0b0102010b 68
    0xc104510a2000d5040011000000350303400c21014408080403510f01500b28441c0341d44201480200e9128900070000c501c0c0103031021744034141002c0540011f03001008903581c140343c422402500940284000c401032034444010400310391084e5603548560344a0010003080749080040309026009105060040c80c0c61681d8858018491100d541d114000b6040010003803403240e2400c100a00449103c0b00c410003040301e140751a03500a0203058000d40e5036100042045001c0c295641c010b56043d0348010b6030074100100304071030840c120124101c074010a0401d441c0c1d80f4410b0301524444145420000302004017810492404843c29480d806040d0148118104550007048031411070704400340410003480b0a800241c01028030040c014140e2080d401403205100b00d030602440c01741d00c5110400c8400406001c0031480704004030701042422034003040140141401d40141003128004001c444880c2d030790745024042d0b03498001d00060010404140b0f212003840030301410304010400e0000b0004c3c0b060b805c0c08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 861938003 1250 861936753 861936781
    0x106050f04031e2108060105180105030603100f0b03071208030105010503100e04290105030c0d060204050306011419061d060705010507050409060b0f030f04170c01090614 75
    0x101038007014450520201c56290f400c00c0706200c9a00c000c4440000f07a10303100301c0000c0d041c03034518980059680000201c055008074101c40701c07203240101004410118000450b500d500060440350540500c01100050014901582d807a5006052020480d141c1032401d040c41c01e1840e50040404070385000312580030400d00c204490543c7d600b840c006540ea0307038001d440d10b001c4a55502603001403025204000c01c0c00106a803d07256002c0500c03200803203207503686540641c2e4400380541d03649130308074040360700b860300d800302032090068030600c409801c1550b6000001d0514a007640040740440440c401070380f0700c0c5031450710301d10300b00050082c200005051220042925509004e9080c4400c00c142c0480100d81d0f03200c00360b0300001d52042c000e0002d03242c02d010090043e00030703208000107142404000310b000c020743c0c019030b104102100640c6041d66a5a5a101c03880280074005403001e8505e19480101c80409074002c0c11003030080000400c003c0198a40b20b0b0848841c00e80548111b0348500601c560900540d0b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 861939253 1250 861938003 861938009
    0xf0302071a0403200d0f230306150c0c1804031e171f0503010b0d081b070b0a1b030816020c0d030207030506090a0206030a051510050d050106050f04 65
    0x11005115602c80c0750940b11400040c1125550324000d8080142e10f540c0051050241d103125510088514090101030f1841c0149001c3c0a004644075414080c80001c0100036680c8810018100000c0c10600c0700810301690106401c42c285400850300d410300350424603d41d000c04042481e400c5400c2c0f0380394a0042140010060f9000409030001113042424451181d4910a04d40c891428015080152142d1400000c0c0011030030102001d0f040018280380600c100302e80c0303a00240229401c051540e551131139a5202e0309000380f00f201e0215400c180918100a02005802c0c0b445040e980c90900c07400c0030744044056110280369440b507000c000000b0360300024450f0004914441c02a40d2443d8202c02d038107001030040c186800c869801880302c245640021090201d0f4082c1c41906c2d02500c1d6003948503202d0741810700103034000e1001c00125501201e660b00456100380031209081c410b10750100003c2d5003055500c403250001c1e0000c14109000c91300303840780c0d60051100e8141246450085101c0d01c9407402288 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 861940503 1250 861939253 861939293
    0xf0105090c09030a08040e151219080d09200904020a05450a110702010f03020906040e0f060a0810022b150b03010b0d05040f0b0c0405010f030207 64
    0xc10b0620380da0310b080000c401565030040000351115114415900b11800c220b408543e01c9000102c0741d19941442c3d0040c00e80c02c0c07101c002400c1c2d22803040c40342c0c42041ca01c02c9011203003080e0411450803030340700c544203400e01c0c0741c03140000c000b54401c085900341000301c002400138810600350301403000681c2c84240382030448009540501242061406074040000007031090720815035032140c5803002040c10f4a000801d80c40c1c03a0304a0416482d40003c000440b44402918605102d04000d4200990300a2044c10303102c7c0c40ca4500036113400103603808511a50800e5100101c210a6032040c0080703851040c44142c1d00c40800d03144016214034005003140d885864524180c03200d940091801400122010046664007912086c0a010411101c0e502c00505000e480c410a009403890b02082400401d003c0324122820001c400342482c4050410000a0101034003c4640c41c5100000c04d00040c015a440d9101c0c0207425174003910303a032400c40050561460000388204142c41001144005a6422641c2000c81418 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 861941753 1250 861940503 861940507
    0x1403061e060d02060903010603060506010f0201050f0606030c0c010c0905010f030c020c150d09080d05090729120703060f15080f0c040302031b04061202030a030e0316060503010e0f0105090c 83
    0x16001003104c134880c42c4503c0d0f81550a101002c01031140e1504114051030083e640c8411000341214100e080307410541d0303000d90f00001040800c0c400d01d0820003541c1c0001d030b0394144c01d1520089002d41421140200c2c1b1640100d2600d04080040750381004c80551800c1d2141000c0c4100c4d683c0f500000c0d10b0b0355103d920a4031032001d0403110810780d90441c040d10326504281d00304021081007030a00d40310b0b60f0800c196540360030781070900040701d000010031094111909c00883c44c02703036540c22002c1044003e412000b0b042d103010a01c0350702c080010b00020580580c000382c070b00041480c1021500c039003401982c1c11043c124100044101500c0707502560ba5640801a803410395070545a440c0400d03054865540043d40c1841100d0804c0007075513220b500d80288400c200c808000040d81c8400c1c0e003104c454018000396240e080032100034086405000020980c0d88024280c81d403481c06440503c984070060741209000440c040014008081c11076040c40e0088607540c40740100d0b41c50310300065590100100320030904080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 861943003 1250 861941753 861941779
    0xc03030f0408090312090a05030f06040f031b030f02010609020a051602030a0804060908210307050d200a140306030705060a12090f032607030b010c0b011403061e06 72
    0x101030309840c0322220080541742c1c2580d400e284035000d5080070301c405204004400c80001e80c2d14001440350714003107050000d0540b5036101e84482e08031400b00d20b0300b07409100307040204803043c0c60004004030b03040c1e100381c4420340c0b8000c2c59078009086030219004060030030b104100c0b141c040b42c1c0200c250703421581112780f071414652aa10100782440200c0000400039000030401199158101c560603050b1002201105c401d4401e003102c43c0400500040780d10702050040020030412440f40303000f070100080c51100450303044080d1b0200310008055200304c1d00607180c0440c80b042d400350700c4060511170301210354800d429400d040300002d840324894800c5e540304000c005484400c5034081d02c000705022088031010041d0213018240b190703050905c11070440024100441c1c080503400d000d0b6001214083c051449071913940c812000798000c080901c65641800109825000050391340242d5901800354030b174840150320046401d040ca040030141c00d11180d0035075885e24a200301502080554040300841c0c0300d480c1082 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 861944253 1250 861943003 861943013
    0x806060f061207020f161508090c0a060206070e01110c0d1403030a0c09061701090c020304170a12020321072105010f12050304091112100e0109020c03030f04 69
    0x400e40d55202d400e181e90408000c0c0f45a008100414030f00821401c2c3d07101555026002e00c6102624005c4107101c122006030407904a00c6121003581c06004002110300803601100024111034182d481900141c0c4224108982103511400c600200c401c203007488181000020001a00d5040500040f4000c0c9403121202082c000941042216501c81900303980d500d0a01c001c02c00d0140030710300300020210b484914000f070001e12506c1203030b140503408064000030383d00f0020000050600301c4107000851006120218000c9003005103024020f00e20402031050810360300e40b601000f0003043c100c006540080c0302481501c08400039420401c0018008100c09030740c0c0031400d88400c1031840e4843c40c4620310b03010aa040100640c060b9043c0d4401542344407800759210300c0405d00071440c900051254005110403c0700102c10b030070164100c0074a01c40d00d0704103100550801c0100e030007155441c025903070b8184c0801048012300c3d030075400f4000c0440150315203000c008245603644006400ea01483c1c01c1200018103000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 861945503 1250 861944253 861944257
    0x1c060e0a020a0b070201140412060b24070c050109060f03050403170118141005040e07050d05160803120619030c0602010212060f010c0210030b13020d05060a0806060f06 74
    0x503070700426030800d45031100c001d0f54954000b000128003240081d4281150031215106840440e40d0f00c20b81e400446100d9034410003e4203c8484064008600c2501681010590f00030000141800220240c480185080000c0018410f41c8014148105803009000071076101c01491100c0e225130801185a4549140485840075040480107407489030000107e40395558102c02c411014070644140300e51015500d40da501628282c0b040b620b4204052401c01407802c16400c842603d440b1b020598440d80d41d2440420499400381030100e81580102d05465080c414041da40340140140000940c14460514032400c00000f010340414403400300c1c11113003480c858803900c5500180d544940c1c6080760030fa0710b920190103500003070003584660b10b5600010b082400c21400000e1301c542c05944040060303090ba028000386040a450f90000c0544450b0642000d841e14110342070403107039641c0c00503610241651804212030f4050203403889914402410000140e0000d6413a8000c0022504d0210300c010040000b8018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 861946753 1250 861945503 861945523
    0x2010c080d050703090b06030606010206180f01180b0c030c0d0b040f1a0f01050306030a03030b0a03140c0414060a09050a020715051024051308011404030e1c060e 71
    0x803420b02040249599240c0c21180342244940f0880625840300e504145e00e468080318050700503445080062100c043c00c0309480076007001c1c24162102203840038880c501351004110258041009480c1010800c042006865800703d243c0c0c1c0f0f50703401c5061290058446110b28a5402096910343ca454042e03999541c1c0090010000301c003042018109084041d1001d005100b032451084440c4d00005d120303540240c04036841150300030042d100c10103c907641130300100248100755030048422113004c0001465041c1008040c150780005024003078800c41040103032408c034070560200b07080b003c2c01d0043d2501e4901c14601501e0014101258507a103044030200280134007400500980d0003120030003400743c0180d014034040c90300072070815040e940361113a50003550b0f90042030f40e50a8156502c0c1e08035161062024180c11119042c407408003030b40c0c911003a0300b5074a070920110f11014903c418007041640201511581c0c1c071090fa0300c1c2400e0b00d40c44214180862040b00060b08881d10fa104c80c0141c250b0600012803d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 861948003 1250 861946753 861946777
    0x120901031a19050906010c0305091c0507030c0806010605040506121b0f2802280b0702010209101805090c04170a152903010603082205060301050d02010c08 68
    0x181d070015800001194816107018010920124415510a509004c07255030235417261490840e40381e06000710180580c14080050403c500d041c00003c90501450300110f01809800c0b4009007807810003400c19206074040c209010081104024940316002603c1c4c1d83e0b07110f04040541c0780c0d40c1900a4aa281c2a07008642075140c0c00078000240c01146805825104c2184012003001c1019803001c12881400b0b20050f0301581c446032001d040d0540501c010150741c0041d40c2c030380c440c803040b617550414178100a03205000941d40119030010f0303e06014000b000043c104e8038000c03021b40115042000000b516002e583e0107400c0000008021407440b0781118018080c54070526410744200f0300741d64651091160490b000e4900f1015a1016805401442c40060304c02a048003118100590050750007804014070381c040d52150300000100d0366400c081d0406460b0412001120f4a1b0000d460031401000e03001148159030500c0140941c0d2544101c00305001e0703080c2056840c610590500080c2d40c061000307140c0d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 861949253 1250 861948003 861948019
    0x10c1b0504020c011d07060903021c0b0f01050f090f07050c010b030d030c020d0305240d150518010504080313080d02070c060e0301140f0604020d090f0b0702120901031a 74
    0x8190401540800500303580264000003050001545c40e880340160300c17409000400c04035040c005886c02d0404403c440789107144075084440540ea400546003403c642c800d0f1980e1460004008606000c4880c56000404a40110031458554610300d0011000b170500c101b00316000c601004542000d501c10311035041c00804407800000110401005802c81c070f12030b0344c014059003207003c610314088d0080a026080701d042010780400f0801c207102c191040f0b200c0c42a40302c070700c4801e25400b00702c202c840c543e45011b03005008981c500d042c0d0102d403052040100c013207515030306d01020000410f07401c03010750360005071880c00005250341070b041003050b600662903800c0c0030620004625040080802c1e04030200c4a0a0711000c0d100030f6200100b46c00c031811038003104e01c5c41058400052111210f11b079103943c40f1000400060401144088140c1284c0002d0b00c1202c604800c56800028850100c14055001c0740c1403008100c006400c003a01501c0b0700940c008541855244e003200710010340000c0441842042c0640300300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 861950503 1250 861949253 861949267
    0x302031203070e0d0507061d04020d0624020304090507140a11100902221e02070b06040b010f05070c0e0f040210050f07080d0603020d0f0b0108010b010c1b050402 71
    0x2803640e8420395444021905003885102282010800c20840350b0304030003d0710446203000400da0310740101c200c1d6a480103101d81c1302e000790384e0380c0c620203014401241080000c1050800c1c02810181780007a10000c456800d45205225141e0300208503800e498400c0d6010626032102c1c1000da681190081542c0b42e8100301003030412b84540c0c40781c1c680d08080b01c01c0084850341518131015a04444142c000a900085c8a800004a40301034441004214803080f0b400074483c00c05940550501d259800754103e41500007420354184016032000719003180049404201c0d101d00b40300081e1500340d00c041700c9070030300001217510030600a07091154001003110506c080410710300342203d40303817003402103070100d100710140c8000c009054420f4054640c009400f45080d403900b885a101c01440d030704402441592240c5900c004801601c034403d04051540c46018049490a140c1c50007107000d4405802803035990380341c0030b040d04490780d0208c0c80a04854003c0142d50024241044100481d10070f50440d54200d40001411 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 861951753 1250 861950503 861950533
    0x1a0f0a0b030c03040308010e1308090a09021c0b04051303110c0d0303060e0a0603120e12030c030306090906090712030528090b09151c0606120c02060f04030503060307030203 76
    0x4604c620300c030b5560a075440e80c82d503400190400d0240c800080c4034520308000ca001031300f48801440d505000800d000c12450740d818501090303905c86c0f01e2400040480640140703218500d8001e440320794804503014091071500c04079445050b24041c00140801200b040041e00e81c0f40e042c0030201c03480c14050064200307107035903090140c06449a8403500111b0103400d40001d207018603511035581500d0b03006040e180f40400e41001107034034841010039568040ea640403000c1e00ca0750104010803050b0310220285d80c4a1501108102981070300a11994841d00b1a9003040b48001c0045034000907500061501c081d80405814126442d0040440310b02c400100d800c0813017000301d1000c90010310048581c1c0c0325003480d900c81040003124051084641d800085541b100c100c07400c615070107400d241c811030050300c0c0c0316446095010b0030307286241c0c030000118852807a41031078200c99000b1000581101d000078809405d1160044000f00301c01031015040103000300205500f65401d020600046400808499812a0314594 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 861953003 1250 861951753 861951757
    0xf0c030b060d0c0303080c090315101d0c0a03022b1a0d122a0c0b031521070803030a0f06030503070305130929041a0f0a0b030c 56
    0x603202124014001110342c909802440c110a038042d0390425030902e1a030f42900c0241000d0450402c0c0711041c0940850344c0c4040120040c910011848110541000e1050018a500d141c0190700740310380fa4068101e1610305c420f02a900030007800c800503902d0240e98811002070140c50a0a0102c03000d955407099468080950000702d0400201e0411500010010081e014140d502c40c0c42d821003801c8800d1300101c2c1c4042500d070306409940c10320b0504810518020301c0840d080181103180800d003100081301380580c5000940182c100124441d03d9420020141c0d50068140c1d045940303d150600e04190000040b17820154100e41000c04461525880e00110f0b5100d410840c1d825166500d420103110700410130b4051242142c0d00000990315020503500d08803041c0d80300300c00140e10102d04180c00901155a4401d269080e58004c00401c0c3e2401d2502007809184100a42a0f01c11401c100008016045030032941139101401c440c40d240c1d403041040482e183d0362955002c05d8910702d005c01000340c00491000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 861954253 1250 861953003 861953009
    0x1b030a230d0e100501241202160506011502060f06120a0b010b04030311070b16050f0604080a1724010309050604061b050c2a030601090606030b0904080703030c05070f0c 74
    0x1101340150307030300c0c0c0300045c1d059880000ca44045040e400d1082d1407071801194402c513a040c80050261602100104c40084d5900c018400c0300c080c0c2c02440104040c0c5010fa9145040380007a102034886070400c1d4103405441c08000d01110310a400d17020705906440010815107a009500c280b03030f65134960707550301c408055800078881a00428401d0b007400c50303070003400305074101a80c07070f40460542401040341d1502e600ea54400c400321480c0c468103d04244404007004070714800c80c41880d11503600c4580c02001424030807010710703d01296000c40e040c0140ca1500d8003950b41e620704030354017074040507142500481c0a0418102c01178017a0050740244424096143c020134103512038425011039620000e04105c4592140110014075a0411071074007203200c1c160301048203621182d003608926807801500084c1480c2c001e0780200e40e0162303506c03401c00c08070340c15024040170b00740203d4000450340b4040d11180303180d12548100504140d81c408181100368010001c0c0c5021642082403046104d566242506000440d40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 861955503 1250 861954253 861954283
    0x25060509030a230a03150e040602210907180906050c0304020a0f06020c040906020409020d0b0406060201183c02010305150612100b0f1b030a230d0e 65
    0x310700900700f1021000c0d120a6111a00b005803400d142c20804070b00403e505a01303803c0503814107400141c00040000024055409000700507078441c0070002216800289020010100407110100501a00c3c041002421980724408030b5400c82d1407100e49500910b4010340042003145442c05104200d515000a944075502c00c1e1202910251600e00d40400c00a5a10400b4016800f6261802c5641000c0d000003800d0351085c2009410180c5842c410810b0741c0211480f80640740c4e840b905125140752600a180c000c2c4401d00082000740c10248140303d40300120f50b80600300f0246401d84d084c1004400704c4005034003195105006401881d40103003e007003a013404d4268000b03410b0a010803010044001c0d215a241d5008000740e00e441c520310100790400500902d0200f80051460b4001580e800310002001c1c481c418444a566030981864184159900c1b424a8801540240001078540341c000340c4800b00c032402d01072000c000458110040340c840c811844031150407814180001c900c0d003800904055040035071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 861956753 1250 861955503 861955517
    0x1e071404020c030d021c050a0c03140637060c06050702070f05010f02010f0c050903060f0105010e0123070f05010e06040c090e07030f21020d0525060509030a 69
    0x84000c020580c01840d11030002d58004000e00c40d00704070154000c010003900d9880c0708601a4020031544115401160100001503c510040e28040d80c584102d4110017410000440c040c1800001f0802e50320018070b010b040c01c05030b81c0c403040c1d6000038481c1084101c40b41c2903030745004a4a89600400c032084004084918504020226062034004240d03803081c0d809488040b038641e45030400450f030500b46240d5a50555581e1f5486100921040c0210800c0940d10f484160750384001d00281440d00d10014000b503408000440140b04507a0300203004015407409280400b48038524880c10400150341004003230008500189a000304800c4524007140c4a01840080012262904000b525460216002400d0080880c000d21001007654805250701d2007650071a4003e5880785d48012004002c80c000395480144541c4403400f0402d84c0006582e4000c40e44003414620b012110040c24600401c02c0300c030001d00c0206000e007034a440002c090580035400031350a20450410050b8140c89502039040703080003402c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 861958003 1250 861956753 861956789
    0x212004030c06110f060f0703020717031506071203090c080f1b19260609070317041202090c092106071b0b15121506010912030f021e07 59
    0x104000e680c00c584c0c40d001d4500366032069820110b1250050600d0241603003030001a002c00c01000e02800d604259101140da60300306590030b4a030f4030240c503c0243c4a8a01017040e200021320600050040c0c10441c1004a2451403074130703240c4521070b00364000f1701242c07141c07048480304140c0014185044982e500d40a4006260322800d206590030707581c64840d11084030034004c100900304503808814659030400640b44180c44040c80d5410a042541c0c000302039071001c1d40500078082d01c14010000400c1050000380b80c28504600b0482034114140040d12660b500000242030005042c2120745101008001650f203400d8219020101901401d941d012441814001801c050190180c06202200400303031000c8407036181d8480e0704107035009200200001800a800b0182d840342c4100030080140c41c0007800418042d48405404a00014001410400751410070095105902207800700d842c4c1600e031201c0f0040d0320389810391900c08201d0400c00102c2400303211051000c00030405034161058402d600c031000c11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 861959253 1250 861958003 861958037
    0xa08060a120f1b06080f0106050408060c090d061d30070c05091014222f091206070e0d170a0503060f01212004030c06 52
    0x1054018810308410703041e24400410440918464910711540c94444028014400102141c0041d8080800300d4844800d21540c2c1c000205003070f003d090146880d82c18149401092039036903600ae00b501c40c0f1014000b40d409402e4440c0400c0200d01030300000284001c00c2040c1080c805036036140c041e004d442c001c400c00030f007400e510300d0300803c80c403c01e0390080ca0b1500c070056240e40c0c82c1d40c01198100c44412004e1000951600d44034652403141c3c1c136600031a000c0743d107807003039844031781202101091042c0150141145c0c4040c40c4540400004004c540c00100d951098514101142d6515046c840c6001d18130b000d0b085100b80c2400a0146100640d61085055941d0b03640c5555421709490050200d4455034842c000c9080101060740341c180109980140c2c11964003800c4650b610100d032404c0026000030420000c3d080440c0c20f010300d44000e1810481280c4007160600c540205500418074060301ca55030940e5071005e580443d5080011650600c0c2c4d995500d00d44400c1700c19840c030400780441c0d80304413a01d600c0383e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 861960503 1250 861959253 861959269
    0x70b0307050414040e0d18050909150a0c200c030a06020d200414180415050c070c0306020c030f0f0a0801050901180c030e0a03020606031e071e080a03050a0806 70
    0x100b68400281000406d01d0300654001d8006001c00e00da045660600040725515000181c0c001c45030390b000f0f843e144a001c1000085444011300c9030b059030307080180005989502001e0000f0500c0380304411120700c3c079283c0d01300341816a0241c0e02a454407500625200b0b22919500800ca1200040002c003c0701380b03100c1d00800e050074840a9000e0380d0b582484104602c01180760f0304030100030001c0c000e00780604206101b0600e28400d84060300d45000c07034140c00c0c41c84003980c0700c2c0580140891061070f0810303a19545040404240c0d010050016801181110300840c040080c3e40400404421a42e1142d5040c01640324076004a2a40000540080000185420b00c000c10034140c2d0b90a541c096100b0b81441d030314201404090313650000b0160750350300144800744244010429280b103680032746018246042050301e489510609000c0103103020a4050801200140c810201c81c0c84181074040c44007203401940221b0400c0d070001407180102c1940710205a0301400400b00d8018586640c00103031183e5003840072032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 861961753 1250 861960503 861960521
    0x60d051c200606040c05190c110d1e0303230f070905030d0c020f040f09020f011b021203070804080709050a0b06251401020c060901150b0c070b030705041404 69
    0x2680210000c203502c4d00303154101c02610031881c1845e030702c3c00c5d100030000d6460b130045642ea0000511410402000c029000c0000b09680104031a114044d070b90302d4540034117800691108000c26021074050904050203a0400030129806080400032007a6580100a04d901c0c22105070002c0c908000002e0b565900512070442550b001800801c00d55000b0354064844030781585050360f1290180300000616510b60090b00100d541101e40450071904030300c1400300386004912854144864543c0402e1140340340e10420400d603804503802000d06907802c02c0e1904510a0302d401901302000080c003c98030f4a0001031160850700007080800c01c9544400c55002180e01130b80b45564480400c00030108550001401c1d80b038160300084903080200702d9a42c0320314000020075a02d440381e940104580d010050240b0000794000500d00091100c0003100c00f01000030708640c06655004440802c5410100004200b0301000d0901a8603442c2d890030603441c0980790707170850b1141403010b4009042a613580d05060044900c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 861963003 1250 861961753 861961817
    0x5060f040512071b1401020105090106050121110a0305010302030d0207050306070e060d09111315050d23011b030c090b0901030e0303150405010807031703060d051c 72
    0x100b00d0b0741076a5065264402081510402d1164168801e5041800b10740303001081c2c02e01444405520b04000a4295030000300341b03951503454120100000c1c0d8002c0c4411074000001c4e400341c2c048007110f4400c44000c060b000081c007082007000c240340c8046034050b40130f039041c1c900803002c841a10780f0303005007265151018052540c05410140110740c0300c030300440110006000042280e0f080c030a400c0c81c4031040b01c1c1401381c1075800116004030400c9a0030f0098940760b4403071905109114140f1000e240a0b0303060080c3c4501c2d03019040c01e41d100740c103100c003090010300d407000051010854140100e45160280812050b142000d501c1e030003403c4440303030292151008545040d105c40590078540060604640c00607810581403584412a0561a617014801584910025850502c548260301c1c10f000842d00c0503086051107901c903600600118421b0b81081e49059480c5240d03941da0307500d500200d0a110408000204144242c0050001c00409041d607002084216640c1618143c800d030305500840c0d00341801020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 861964253 1250 861963003 861963013
    0xa0f0b102907021206040309170f031c0605060705010608061e04060e0f070306150510170c0405040e0303061824040914030706110a0f0503090106170a05060f0405 71
    0x1010981a01c0900303181400206010070b8400120006801c2030400c0350b0450005060a10a010703d414804c2020800b0340e0050003006550729040182c0d65901c0780701451040e02d8803151660080c11000d40012001d0702020b0b0046031201d07910714100c4c0c080c198601a0f403449000e1840040d03900744c5021036821a0800d0480402da041c2c4950712200014103215958120502074050400351100f0100080c100461007004006401d4420303141003403108100b9003116218500391402528100d50007081030907401da000e101d1020076195100da0042ca17102e02c0e0f02280d0414285039103000303c0c101c01700103148207040a40714a0380071004640c04084070300041311082400800b41080b03540348542c07400070602243c00900000307482c915545982081040381c1001c0921a403000400408008903401140d80301003150b0300450500035164800707020b20301110b4106040000110001741d510f602500181c00501c0d06000018000707e04e584065201d03240080e054401d48100b10115135004040243c1510590b00000601 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 861965503 1250 861964253 861964319
    0x1b05190e062502120d180e0417040f060906030f0506101101090c0e01050a080d080a02030702031c02040515130504020c0a0b010602060f0a0b1e030a0f0b10 68
    0x500e44400100b54040c0007845001c525006807510880340301c4182d202e500900d000c2c40383d0b0100804000200c2ca9038a02030b14544002c0010020500c1c0c029005036101c50742c0350048495507400343d1a401180c0c80040004911500025419049501c85080e26880d03039081c0f20b10b021708020071064030300c1502c401e5049240d8410071645980300c0d64000094000c040e001041d8160f07c3d4941e8450320f1708a80001d109100301d180100050701e8030404100003414114042c1500b55140c10010300110740060004428075000000680c0075407007441200c042c0240c045031201c0074082346214400a401c580281e601502418144013140310a800c10f8400c01040c41c02041d500c54244402d00c8003035001002284918810021840001000c0c90389243c086c02d271660041c1124984210518151480501583c1c50b4510f050000c2b4181d1310b81c0c883c104505c126880711007038400041d0004c00d1a182003080040d02d105c002d6a01c0101f042611007666000305d501380e14001820b615054800e0640000301c04039030200701864070390 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 861966753 1250 861965503 861965527
    0x15030501050f0d060c120207060c020705010c0c060c03050405090a051f0e0105060f040509040308071409030c221409150709031106040e01140307090e03090d05011b05190e06 76
    0x6804200d400d4600b5441001400c4002807e98000031012a100703500e0f51803106419504000d00c8004000901c2d144500b0501d54890880424441c0948810842c3c80400c0b030040c1070241c4120f600a1001900b280c0081c0b40c070795910300080c001519900c203a100301c0c078108000e00d216202c0200544080c40041d880d540d2904c410800c04e0342c015150800c0c018024040000c0340e94070790022500c25402515001c0e81440d00b0322000700107260114088009070070078807012000ba01c3c00928200711103000c2d5a903441a15070713221000f0f003008a81c502c8660f0309040404c400c680441a1a580340a2660002261001d02081c07a140700740729030895480d00082c185010410201c3c0c20074403101124070700944000d00e401c0d2518149a8400b8098011041d005403481d5680100d003004c04c52a4002e066401c01044950355400806449200740004036100c0c0d0f400ca0b107800709001007075010802ca008201c01802c011700400710080c100b80c02c858500c1d030320139410078480c40315036010301081c540e174010080070380707140205003141 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 861968003 1250 861966753 861966761
    0xb10050a0e061c0c0315051e06130204060903260319111801110610060309050736020c07050409030201151815080c0d03021615030501050f0d06 63
    0x1169500ca0a000f00b100009107036400c00c80c02242c0161500f01c221421801c26082c5141000014060203241508000b070700c1d10003004d00c0c0c5280b0445075480c0c100d92070b044005102c0b00d504154040805100080014000d07800400c406c0071a4481e440d50880e022040c0302484111301d481856442d50392040000842c024206041c030303203041036101c01c009401034061680c14501e410641c11040c6104000418454a41c2c000300c12010124018009041c0e42c505410320f80b00300c258070710a240525403030f0032030f0a0810500b4001030028050201a0010380c044000014002c03000d00204007414040400400584200d1802100d8a00c000240182413003450001800010800ca00040c1e0865603102c0c006d040001d405e5108200800d2101c044400c1e0345000c0c1c6102c81180c02104402c0780c88502c035181007000d0600882c41d0840079030704452098100509040030f0b401c1543d80d2a40b42c070350f4400110080744001800a94209802061781e041280c1c0c0e8885062100846c4035201d072560118505031490005015900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 861969253 1250 861968003 861968011
    0x1c0b03030318070902030a02090418020d0b150411070201110609060f0a0e030a02010606200c06031b0c1027140c040f06090f05040b16140307020a0b10050a0e 69
    0x10864000f0365450603841e00301d0308142c680207040c540015400002d441d042c051207040c0441d00b01c1221040300158005044603804110081003903000c1d4002401d50900b081860b01d03c042d000c0c109010006a5aa2080080d488400200d004c100028a00c07071509400140c4603100b400c0748401070400e030301d81c1c4000c155025402083c1400c0152540b28000d914503091002d4405800c1039000840c0e090b080000c00380c1040c0101e4036110f0062540190490740304070000c0c440c00f0b14502513a440e552038480c4214a4445000b04c01da180305600c000a40501401000410003400907140c44100300c481404a83c424050082c0b00c0800343c00c0c00000f416002045421400008000240044070032407110400410151881088136104503651004200a081c21900031407d400c0a40c04e810080c80c50146c0d101c0c184204054103042122503040005100c650140b1a00c94070006c03205900ca40303a28147c60003e41d034101072401251440702e0240420600342c204050002a11801407a07030900d142400c01800d59105c0c020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 861970503 1250 861969253 861969301
    0x2030603392b0510050c18040216032a031d0a080d12110901020618121206040b0f0105091003060e1f0618060302030618010801021c0b030303 62
    0x350140340510424412001c0490585248220902c00e03003407050a01301032180e1080308a080004122000000703104880000c401c10031210304510090021600030b01428031320410503070403481d9140034035801503124000402c200348007100070b8004101d007140905d0440c034003c0100c1d04107804420f180040c6030f0600781600c03000d03102042103070390356010b14038013242c10090b140030861f103810036241c220301d60056240e000543c207030041c54a240343c00000e64858009001009400c4060030750615004203000101ca80600a51101e8458034621000300c130a61041d02c040c0c1c403d81c5010141c4200381481000307500489016110241050324120502405015a0402d58201661034138041001c0c6010074546d805242810b45140c940c0d400404005e01e1515680c02c44170901a04012140c40441e411030041d0640c0da0f00c0c0350141c0c90361100404a2032403603403218a40350502000c1c002062221056002c0c190040312035040703600d0043d0141da94001c03100401c2185d6056041000051000305229440c440e5140101c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 861971753 1250 861970503 861970519
    0x909040f1103070b0406110a1a0c210709060201050f0406020c07050303070503121f1a0c0316020a05060f09100516060608070b09030a11010318060203060339 69
    0x1d400180c2401400d4024602c5207034081820320520398004011000c9010810003840ea40030340b038407154542424029052a41d400203800070302d06204c91003e1b0b8a41c400f10984080a155152001e40c00ca00c004840490008612100c0050468814041c55000d424201e206c54032984541d105c1c0b00195002e44480d902520a1000003e0b10b501d080008007101c1d8041c5c8040c68680505a0350326202c01c4d4041e142401200144030814403131881c44028108517500702d4019070072001556540311070307402101001301d003500010030100740507103507400350b803082e20310071514440c0540c0c903a810807100c2c0c014089684201c4505000c40d03180c50404040c2d459540c4124107019040c1145583d82e030302c840b0303140101150f210780c90351000c000c101d4040102101504a4640150400c03001d4004a6500e0000f0440176004120781040c020540c0d000c0c2c0d1050b0700c0410b03e041d819088ac03042d414003301940c4203441141c040d1182c611400100200700003510031003151005509000d0b91511440c619013100e40c41003541c05502 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 861973003 1250 861971753 861971783
    0x200301150308030a06092d1b0806121b010e040e0124060201090305030c030406091e21020c0105071106040f170105040302100e0f0303010e010e0c0909040f 68
    0x262652034000d52042e020141d481c80c00001007010b8a1290b031041c040d1070700705004d032200300c40440321040d0155102980d581e444c071000954000544010203245403680c00a00e2204481588111028030544c4260340340010007854292480d510315450791619070340f190a501d04da4003076100c4c1e081c440b08210010b202044011510103a1805c5441c20507004a24550003801c031009d14170510380c3c4c21f00601c2d060008012030325183c1c4001d070580c80010000d51074110700000040c208a443d90201d0310281e00010110458039043d0104030320429a54002d8804103031007002c45041600c803003020842d0720701030ba024000140c0e0200041da02ca4100180c02c03980540c07042d0a0720840e0310f6510242c0018004440550740c9103182c05000584141e004090050f40d074181010000482d80002d40e5004076040d0100010300d05a007554940e08100d1414501c02c0107000000000400194205641d8103880c2d9001c0910742603140e0007c070194038030890302c3c6280c221040c6000203001c0fa4003506030032a0203004150000326860 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 861974253 1250 861973003 861973031
    0x120f0c01020c01020901021b01170a02120109020c0106140a090504031407080d0b0607031403070207051206090d05040e0f0a0b120d141c1d161d04200301 67
    0x4590b5000441da03502050b05803184d80d0410a107006070502a00d030120b040d109800080011280f9010045001582e0002c54032400540e4100c450764105002034800b196180d40950019500002448000e5800c180000c5103c0c45101c0b910300c440380300104070140d92031811400070088e010080c8180d0900540c07501c000c03141c10580340103021061203034140b00e07502c441400fa0842241c801e100ca00d802080180003a1000a8102040301554103c0c15030490312540d1b600b50481c90007072a504901c0d00030314415200607800d540003845a00820196090b80d03841615001704030380c203010b144941400402c00102259452001494894002d5110080840c03041010404500d030010b11422181d015400f4200242403180e10808594000202c100c2151619400c036015030140e0319000803030041680e4900038001b481d03690042440101d02c9210503140484100d0323000c9920a001032007050141ca0040c2658900c0b01001c41a25201e580d1000c0d182814000c001d03003541080c002c62001c80d42542da04d000341e42e6450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 861975503 1250 861974253 861974257
    0xc06142505030a0902190e041b060210090606091503110103020c190f1a040309090b0a0306050603010626010e062e08030d0609110a0503041b0519030b100602120f0c0102 74
    0x1820759001f00d114246031804c80c804c4907d0500c2e2000d03581c6640000d0060307a9001c40e02c004540c502c0318000c15054200c0c1480c0008198035400100d00528100b60901942d1130142c4050441e8003520010001e032205400540a03031281894030070301c0e50088100d0b000021148942d0303d856601584592001c4401542c6040150381c041c0c0c0d522000000c180704100030140c0c04002c0b071020f820304c10428405940d540002c9060f024090000610345a110000120749407025480071000b0b00c088502c039401e1640f65038066058054181008496500f0001019003500c03000581600034030080c001294030707035100140c0e0400841280c3e03148000c034040c480c00080500b41000a8042c000048a0004880d0b16054415084400800032024180d509001652107980c012007a6540320b0740120300310255006009d800845010190400c9a000314018520581601040d40b4001580d201e071304650b00316103d2203034003800380505220f00401640200c00144480d50031002130800f28450310100d81c14500780480003130036070f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 861976753 1250 861975503 861975509
    0x3170f0d05040209130b0601120227091b070210050904050408030a0608190816080a0201090b06010e0f1c05060108060601020d0f1b030c06142505030a090219 69
    0xc151180240002e41c13400c1904035801000c5000b040c012100941e0399441c1a007802000031381440f13000c503030300c0c00c0c0e01c03040380c0498094855504500701c18190540b02a003006c0e80640030076000d25440310008610009031450305e102d0200c000394030703810800d840c0d0812400b9205a8001c00420030705100e12541c0e5280d0340184c600035845108160380720301d4640380e428121030300307507210110700d078414490038840541c0c000340500d02a8009010030356800100c4401504416020341c01440070000203103278171045d41d042d4042c5405070b03c150700ba80140d4898100444158a82c0104650300901202101520b071500b028290348040102000400140e1240c4809082800c2648002816041141000660b40e4107100c0c21041c5541401c0c8201d22045900c070052541810303080c1c40801e11740a40c0002d041c94025400e4001c030941c0410244100001490340740950b102c15104500c1d60f50200340c0a0b0702ea2010501070090454050b5103403400d40e69040c5d4564098142c89000742e800681c030300303e20301007500c0b10882d020107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 861978003 1250 861976753 861976777
    0xe2e090812040224070b0402040b06031306050c09011b030e0a090203040204140c0406030b0a0b0c012c100b0a080717060a06142707022b080103170f 65
    0x282c0c6002e0051092046480b504003081d400641c600c0d085006640040d21902500224980c1c1a5522031000c900180b110100b0240d0181d00881006502a02044021011441024203218581300c0d02030b0400103000310300116005c1110803900e11034040109850f003040c1e80c0240382c90700000750b2403008142002c0c096080024660340000070030003503040c039000b995443c842d030b4001461645028800c515460146024200030152142c89030105070b0380f0024040060444100980d5994584114242c001c04845414001106441840d10a414034a444203c0c0c0000d5207005044008076001d8500000c00d80a002c85901c98880d00021613928000c004075400b6000c1c4010780060201440740e0f107480c105000f03245a0400d82041c80c14000380944080301e2100c18815038403520040001a4a4888015000f00108000b010001040102da0740006d8100c0300c40c1c4800072007002c040700a600d0000500b600030940c00807a02e108010400200b03c51442e4a810341805201030174112031541581c0789900076103080e01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 861979253 1250 861978003 861978037
    0x60313050c0a030f020d030c06110a030c0216090f110c0f06010b03060a0e0402030c100810060216060c020102120703020a02090f070807030c02160e04060e2e0908 71
    0x1040003410040346104500c2111120074551543c1c1c0d50120212a01000a00440c0e86402d245c00b054050340c0a0803869a0102c130601200741d051140880c2900840f100c40c0c0000e060042c0201030500100780e9885a14213120354603005424150b103079025010b4603200301d004a5446400451081800c4081e08030807401074054441d55103412200f61a115042c3c0080c41928001c1090040320f9a40091400c220b601d42da040413074a580342d00000e4181111140708940280b604000001c5443c0d100460074802c1040748003c1801d40d0b01c8010499603401507030491354150f2950340b410311419000b41c8461203800c1c4140b0403109494140e59903e4000d401010707040f400340e408146000110300d8003002290303015159204100580c07400301b00082070300d0400303060101072694801c84100c510740300348140035014410008510b07420f036850148500c185801c4809540701071400d004120344030300200b6401030b116140621000c0300500c840b030154480c0c00c000d11074884103541d20100000074404c5d201400c080c4078260343c510 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 861980503 1250 861979253 861979291
    0x209150408150603070b0a08070c0f06060e0a0c020c090c070507140f01030911010f030f0603030206061e1e1305011502010606020f030d020304020402040305010912030b0108010b04180b0603 83
    0xc1c00e0340d50060450b078442d0b00308003c10300c1b0f59102001507403000007040ca8000140e4550381c000b92518020b030000500f0b02c6110101003814454550401421161812018a560b584118520f400c82e05603040c5180181c00c07803070b6501010b1900d20031740c43d086041342502c0da26084d81a0740e400c0c9071810a9000c038920f42c54403e40e80500b80b07410111040b00700c1f82820b00384284000360b40c4249051102c42c0e1620f05100c12030b100c0c185a00d01c02c2c0d00a1040101c0c0c0003040011648034140655205804c40710070740b2442006011369418104000c00079800b80c0c01914000070404446091000f0050000907281c10911058450b0fa400419028a50080180c0007884103e4036050070000d084d903050742c11003015580411304090b96500c00004a403028204464010f03126115803000070040d1181c2e91002c1c14a600304990007080c41310840c540081d071315140d1020084400b00e00015170b282d2800740718005242c013090104216001c01c2c5000e43d0100410003200190130381780b51000a401d500706842c002c10300d60130700e4498 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 861981753 1250 861980503 861980533
    0x18050c0f07050d0221121305240a0603080910030b0a06030506030d020a1e02030a02040906020406120b01050d05040201022e06330c05071d0604051302040209150408 72
    0x128004e4618800d602c01100f0030341c00400714600c901042c9007494102c04000075030309245012284501523010003902e10211040e800e0301c3d00c04002c017024036448100b480220321507008900c16036080b80d40c884031260138076000408002c42e04041c0c4450000b410340315426020181d5030030550300050001c54a000940d410309034207161402074030074a080b096512512849020802c5c52554407403c0105190548014000e407010a04084450310000e401909190f40c0e141003012036006007082d50700071750711079100c1c9100c1c0307080e1820341e01c000300e103903010841c104048a1103003140d0300071075446401801124003c501c2e601510000d029031b00184480400240c0c00043c00c4111409101c00810000a41882c296401008801a4503004044000c0b403042d0445941c0c00c40d000340021900d10360880c083d28082a83c0e10382e941603041d030060141c440668040000340307080c905031003164000d854403140c8034241e200c1542480000c0d80000003150740050107000765454011502d000f04081d10700c0401030715240700010303a4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 861983003 1250 861981753 861981763
    0xc1e09020301270c020601173906040e04060209010e031b010e01030e190309030b010807240522080a05010b0a0501030b03030d020a200d02070b0418050c0f07050d02 72
    0x4958010f400d0400f081300c103650000f091070550ba41c0c0c4006542340e0b03000340c0d4514035041f002c070710b42103060300381204a005101c03030078540f1441c2d840250348221407036010b141000701c20b01c1940140304038100c080000c038010074a90307405400746600604103a840030000c000024940802040c40f800c00c40c00036062080a543e000341e00b007001d03a03030a080600800514100c4640c41760a1522168104141036200b04140344c42501c01d6030045410103032014455842e0580c080e00c84da001e000d4252036040328490030b00001281300d03161013079501030b9542c42d0520070b02c43d00c0c041d800004040703c0308150034095000b0480b4541031080f900c0c82c0748200d000003240613445040c407100c90740e80da03c05818186042152034181c0c602004032103500219003001030ba03a0f000c450050b076500d62644401c001f050341044d00289864000a040c0c80400c00fa034088400640d602c0064620b288610b001e5140208424084500c1d5503009401c815001400320844508055240304280000c0d0021031040d617255010144c040c2400e501404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 861984253 1250 861983003 861983069
    0x30d030501080a08070f0b01031b080d0504090f0f060f03140105010506040b070309030b3303070605090607050d090f170a03050d0e100c021006030c1e09020301 70
    0x2814411503140c80308958641c05900406000c030000069540300304580300f28401c0d0201d606c0303810f1201e296144c0c00e2508000040000100c0e000001c0f41c80812001000980395807212901c0eaa403512380741c20113920340041c007290720a6494541e100c008020380304000c0e00500f0301800a20850070045480d41c18500c0c281a0820b40d50613099142c0801072003a034450030122010790720100a41982c41c8881d140c215980e000942c005442051020180054601c84070322240b038502440c3d030103032407070203020505501221081900540c9940601d4003001410701500c09802d990400070011410310907c7d4640c1410081c1a440d5900001c3c07040000b0302640005c085071001420038210300d62200d942c4107070102d6944240c560040c3c188840424460000d1190703400c800b2200480d84d00b959000114500c58001500c0320164480150248001640e44000302d0300c2100c0403281c2090a0740c900c0ca00d04100c060324030500e050702103c0d84815000c00300d290100d03400214000c054041c002c00c00034110700f040d861700d81e41001d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 861985503 1250 861984253 861984257
    0xe1305090d02070515190513121101020118020111070b130303030c0c0c09050406020c1b1f0e150f0c0c0103051b180a081605102105070203091509030d 66
    0x170a8000c0c160480509490f041108860929620b00303829000740e409001d0a03014021071100c1c000c004c280341405804036002c86100307822a82c1c441918000580c00d03126014444c8840580101700e801c003640c400e040312103400c603084084d40d030403603103501e83c1128a51050201c2451801c039450108105645441030200200715860104021354043d503805529080c5d5100384140701c4c1e01c07540860107118142d4105c41d61444600101e410318907984c4400a00c0c10240003815210303404020044501020605004841010594032a40e480c1302d10000c10502d60850311910244417801d01040860060380030003007003026a480b00501941a0050004082d00c80007004402d40b0310100c0d41d03040301440b007001602c4030b00c0801d02d0302d15641417250010031a5242035901c051898803d00b608202001c41c040203080c151101945c66100d032220b0006d042d1107043c01e55002e01c2c0c18805055503c0b480ba0b90310340c0102e410503120320603607107800001c000003070490140e0141810f00384000a03035a04035181c100300021201e103041c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 861986753 1250 861985503 861985519
    0x7060506030d051e1818061201050106170405030712020a05010509030423190902040306050a020702030d181e080f0105040c140105041d01050108091c0e1305090d020705 74
    0x11400c0640740200304032800080c004c010848030b0003458180c41d04100032901404800c2244a404000d0b50a1394041d90b88074000c200b0085c429110300300c18014207040c0e03107080d05d81c002035107134515401e0386c1070900900903986404188201000141d543d515983c11880550040031040706c0e07418024210b407405000380c02c480e8020003041009482001302e40c581464000841c0c200010301c40040f501c800c00a981451701c40344043c0c0d011481d20071580c050010f480c05039800304003540c0c504200104070f20450030042e50590010003d099014030070b003040308150115101e02600940e48035101c480b007154003d900340c00f01c48050020b10080c001040160502c0c00c0c107100074000c2d800e090711001c100d040c1c14000e640a055406800384841d0340217004489c001c00d81204504040d00010a00e00c031402428002c040c0018500c40c04115864800640c603048081c48810550f480b028442d42a41d030345951006041d049a401c010012039145036108851148807190301070005075000045c003e00304503283d08044c1c1700e04e0b48 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 861988003 1250 861986753 861986767
    0xc0f030c0a1118280506060f030916080a290105280f0501021c091202010c0609060e0d0c0302120a0c08040602030903060c0c030306220207060506030d05 67
    0x1001811904030780c0c101500b5211034800c00041549081450302c607001e03552840d014090344004001d4900046144520180041070b40c444404c001d460b02130f1403042d4413150074820b030307602c6000c044002c682115880c802c0b00d03065108003140c906c800e0510350081e07105820020301d66061100000070044004000c550048040d03250355000117400c4810b0103540d009003040c00101803882d14800703081c01d80f55949010300c40e606a0301c40c001d8400760210300840b80180100101d5804940c07450702500c0c1c2d20799281d12844600c40c100500c44001003008102a0304009156170000c4c0801e440c0c2c828a07615078003a0201282c600682c10b4003070300e4404650f032040208014084d01001003503020076607422902d40b111046507100403401d821070703203035503240c0f4083c00d5144005000110250000300030040c568007078080d6171156441ca07480c0421401107001c501d8643c2c100b00000b610300d02c0c0c107003404a64407084850034040303090b104a4641c200e03040100215102d50b504d20a1140502d0100070002081002c1d14105191080c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 861989253 1250 861988003 861988027
    0x51c0813051902060c070f240206040f061512021f0e040e0f07060908150606070b04020103060e16030515031c0e0405191b050901140904090501020c0f03 67
    0x515000d410ba0b0198616082150303611011994a406201c4c100d0309500d0700c07010000f52010f014410001c52035200401c1035560402041c080040358040c3e00544140d40d210344461a0001440e0012981e4035550026030741c0c0f101d150059280a402c205941c0980e103410740c414014000c1c8a14079040306542c481c9217590751168050048480c0c4a420303500800c0201050f04600c5c9000340300112a4441e004084010a055a002600000311010241103c01c540581914140c1202c0140c0c0d102e500042c04101c142d020400c03108600f504148103241c000b81c2c465440c060700340e4541056603509140e024103113002400c0d0f44d05001c1d141e0003c00c0610285102a115000a0b82c0d480c0d520f420502c5804407c0e44c5071038101d0140f00c11450b0804041c00c24801d516080c641d10355505142d450310441e040c60b04044050300c0700150388a00a0807100d441d280d14280c96480152000c80000441d0202045d0030070100d000f94803180100c95000703110b070b0000358860040c1f0b0029400c10720b0040c1080b405520901905101031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 861990503 1250 861989253 861989263
    0x140108060112020f10030504030801150e061b0f0d0e032808041d07030c020a02010c03050903160f090c0c05030301060507380705040b04140a03051c081305 68
    0xd11110910002d2000c02c0c800310740303408884451541e00c1607003814002c4c0c9490f050380000340302e50b11a669841c3d2780e03a00c82c80130f0240f0075a102c1c003850005202215080907820400001c02c5086184e84500459011900b01540341101040b0704440e1500000c12503420241c1080011102e40c404402600c0380003200ba43d00c4900a0740008035150f071180800f6680140070913a0308480242000000c0b00c401601c0080768000310352016540c0200092074509148101803000c0395546546505070341311055504580c80072683d0390405184d00f640f5000c0d00a82c01071106181070003000030100c941160000500d04032800085441c1c1d002240140000c808040000640200840e03040d2485403d1658840e04942440c401c5080039020034100c0014541d160b9402a4440c14240e03110503401e005482c103941c4080d400c4440d80124842c140260f9030601c02404402c1030341701a584c00750b0018005a120580e41d4650500e46200085c1000070714900b190702c070fa01694000c01e06603020426001c0c80300c400c621a5209075030b030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 861991753 1250 861990503 861990509
    0xd0311210d1d030d020c0706050403031e020705030d030e0c030115031b034b0215160b18010c0e0906040b040606030b030c10090512010f0203191401080601 68
    0x750742c1c0e42008402c2d001a040818a540e40740800710382d1641344559450000b50b110384c00401d000d201d030080004d210340c482c4d0101c505a96040d07807118800c0e040d8034802240914408484800d50244c55004102070324100942980c4202950b004101c0411048925041c0f0103500300c0d041c0240d040c80f0200a40da00d0360045e000450380c3c080d0928080f03046c980f10302420b10800e40c000810107943da110b103d80c0300b03c100c0704c540002c0c501044020034400c0110040c1d4210f000543c103912414404400031000b500e44609001090040010143d26040c1140354414407406c501c0400c07075105403140c090000500220003d641c0c04d900c900f00800058503221000703801c04a4208101d8460f10f640000240f981c0c4941e00440c1080f00003800600c107a03030f1103c0028002d8000341210038064864807200d212245444c81c1103000d40040d43c0c40b4084a54148024042d03040c10540d25040c45649521140e440c11659100031741c401c010a02000b0401000c021801c030a03506082200e40154903c00010b103c4684085407580c11 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 861993003 1250 861991753 861991777
    0x102060f0414010207030915170a020a0504170a0b010f08031e090a0f0801140f040210051204060911060a0e01080a06050a080c09090f0a0b0a0b0d031121 67
    0x12541e01ca2600b100d4004954201d40025400032520303000301070b0403024810030340307001c0310a0744020002500111120fa002501d080056142d440104144001c0340e1b00825038040035140803071801c1d448140c106045100d04d0240d425580c0240360440c140001d0409480c05000302001b0007041c50319040302c5542e6401002d88404044003030100303030f07540f0550040c220344801a000c0c2c024030015a1f01c280d03841e403001d0b05104401080d403c02d400180e03040031001c0554410403814000c141243c03266000d00501e182403060741070921004000c20340550307400c0c0e20b4092107507104240104082145162a00101558960039809090b0900041d0002034101c0c2c8107940005c001e01e00401240d90780b0310510301030006036004642000a04401140c42580824010a0324100380e660310a50341318a00c0d05079440140b081011400d8001c40c01e075000240c4640740303ca4002c44021008221079801000240c1031615a120880c08a00b4105d10107201d240c050040c03d2480c1108071402c02ca1409030701401d076040c0b050081e8170351 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 861994253 1250 861993003 861993031
    0x12010b030912091c060c1101021315140304050c0a091802040c2609011508060a050c0d0c080703290603131a1005040b0d060f0902090a0f0b030c010206 66
    0x12590715004445113411a400c2c080191250b92410450014203c9031003100001380b0b10300400305412014000c4400c481002d000c5003040514221814404d0300c1c1038208441005400c442541228407042d015502a0b8002c401602400c03030900200510030f5400d6020441960908541c0d40c4a0000d03080c0b08501e40b41c0548021032407841c0c1c0801100c900c4915924008601541c90202ca822128146c00500c80c81944000704003001004908001038070003441402c010741e02800000d2000c05580e0003c0d50810700c00744d001400d00082c2000f030019248808104070000e00078804120a10703a00d40107044113625001440794845040741c04080501c0b050b210700901501300080030800311012401c42803107842d00050181d0114401480c02c0054003030544003981c601c50341007408a1030785400e208103d60160000c00d842d09500e81039980f100505502c5085c0c641080d5a0018100541c8036140094400c0d075013aa000541c0300c4503403d038802128064564140680c2c0f0001c400001a6000650782d034000700907004401e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 861995503 1250 861994253 861994267
    0xe0708221401110903150c031602010f0f02030405010507080408030c07140105070807080a050702070905060402270a1e0501030209030a121715130e15010b12010b030912 74
    0x8540034601c00880c014640c0f800c41105900c0c2c103444007600e484102203080c0d410960486480c80301d00e444c245c40c11700703d1100c1003001c1207490b90400c0300022910100d0001281804000d8900c6049032001e03800070081310b030000b08210420000784a00740d4444c1050814550f0341c14a5100c160103404000c15900c0006030004444c01400701d0703041000d40721201c22000340190315100b440104070306016a035100c0410788a40100e910701c0c03080e000d80c42c840c00c5564014052a490315034100064a00503150359042035081251420702c0c1400b1440ca40c04625010b07403c906000c016050041c15a16030313114141d00d55042d50344058103000350280404a030b80903e000341c1c546040f880042e05058808000914042201c00c402da40160010f803007603030385100d900701c0341d05a95901e280c5030121380307154103180e501068601c01070901c0c0c0340562001c2c40d200300d08001c03204039242e011003000b40082c0a0700000c1031a880401d0010f03400032115000b5016103094200241981840012260b81c3d250052000350000303c041100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 861996753 1250 861995503 861995513
    0x60201021305060a02211207020f103207110c060910090e160e0907020619021b070801111306050c010f0c030c020105060a060e060c12130e070822 64
    0x194001c86201c0000041212070903046c1c1d20f907501c80c8100c1e0000c01030401c0010092070010075013880c0408094090440c100441c0d40f404010000c3c1003120349202c40401c01200c08100440309924941303840815a1814140f440e00546907212500c05035849a10074088990651145026641105c8044d50b0202c5804a202400e40d1440100c2c1c0015008140b07400c10049013090621a25516204507203540f1a41e0040c08140003a901c81141c000300540d010001040c14004000b00644402140c42c60041c02c2030099140d01c044181120f00e540c0c1594000030043c09000428801c800340b1000c103030714051800450ac066520380910a00c144424008003064240c03241d0002e4108489440c10343c00304003c00300748898050300604500c036103480190b01c0c080010341541422a05441980e4107911800c5100c8459000c00c46198084091504640201c4e040203061aa1140103030089080039080c0b44142804c01220a4260b48020b12a004202052040c05044a202d00e092100841035102d0007040707000714104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 861998003 1250 861996753 861996763
    0x907090e060d0206071b0b03100b03060d051006061b210306120f060e060103080906070c031e14070f0603020c010905120d0e0334140313060201021305060a02 69
    0x294002400144203006c002c294170440c550720700028040e8400c981c441520b85014003044039628080701d10880b00380200e0690070041c40e072150700149540c030f130003000f9568541821031600c92600c0361511070401f489501d400014602c0f040d15583d078182000e1069440e039007091560310002c0b060340302104004070b81f1584207403c07544c050005402d610b221603442d45055540b4a11035082560464078140c4c10400d980030109825040760741240c00541001b608004000c810360104500b155a01c5070351038008002520101d0501c41442c203103504000503175007030a02d401114040381011629420611060115030025403031301042e11002c2c0f500507100ca5203060010300401e14108041c24038450801440800700141008001003280401d090103841010406190b076802001e455070f41000d051321303140134440002003200f0511040b0020b45003c681c0c030754940d14881c00c2e0811004d070842d000041c055203240800852007008282c40e100841c5042201d441070281d0601501456100d41c000040d203044151007084 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 861999253 1250 861998003 861998029
    0x30414150304030504060306061e0806040e010608030d05061c080a03020c1605030c030f0c040e0a02090c09040c0c081209100c0e0f03010b0d060221090a050c0907090e06 74
    0x114540c1ca04260502400c541c01074490603000901303015001c00c004d4424180840c070fa41b0306200400080d2141034040e00c00250051269400580e200c145100040c0240500002020307400069580c40d0b42c1803a110041d545c00500060161060480c904014231044003203844054105440548540540c0f03022006880340e0b603181e001d0792003000061401141c2d8005182c048500440498020f05c440d40c049c5929490240307034900264104203000301c007505054104a01403000c00e0240c820cc00c0c603a500045103020141c4130b1007117081010400348514202071007284c66005d021700701041007920b1035136041c041d48100d0b15800c61070000440803c035500720030440e110041c042070780107021007441024018564601c0c000051711071035040b205034030181030603c901c440b40000984001c0c581e00683d00e810010b5413000e5005900b0011005220355031031852400741c1d0113086648060a180f080c1c606095241c001b40598030b0f0303c81e40904050054864210301040115403140724203a10384d984100c00611008007001e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 862000503 1250 861999253 861999289
    0x6030b191d0c0109050901140103150f0b0a030b0312040501111c05130b09100f0225051002070506270a03030329010c08070602090406091a01020c03030414 68
    0x3641101d1110307804181c0c1c1504000a80c3d070b0f071580603910303000c10014240a00c10040b181035040d0011410354401d400100b960304412641203030181d5158040c05840c40d05a011480c19000890044151681406602800f040860041c140141d15140380b82040c4514440c950500c6131004070044008400d04c00c8400c1441c0c0740c1d1410622018501b00505280d12280400480c89424036000c80d410400c03000b9102e9446001d0104403803940d22031419101d22000d050302c05c1c01e40c41a0954080051001d00d4a03420384d203500b2596140c80f0b031034042030000e03800307601e011101903400004040c006610340070309031488901154681c9140b510080140c808804004207441c0e040301049101000780340e00340e0000e00001ca400031810103030704407248040c42c00d0480348003950700164200340f08a0200750b0344009031071190700400d80140342c4000d0700300181c2183c2d91a4800900b150705c542a0300440e074602e4501400c840020f001420380805907000203916840340d800b0314401301510b481080115110480040307103504d405 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 862001753 1250 862000503 862000541
    0x100c0c141e010e070e041a01061806030207200d0206030c120f0405031614010c0e04060501020106060e040507031103040302100612150e011503031e0306030b19 70
    0x46100c65446030054480c00145156440c020001e10405102e524030700c00c9043e0150030580d00301002000d40240140060350a203804061410703280d0b18540905d4000c05071034940c0410070740d91040c1070140300e11036071006040c541306006000120340c0c110801081451821815120407080302c0c002400d81149040c06500024080304120700e4030703500c8004004495800342881541d035a10100e1401e02042220010b02c0d40e00144003003441842c101d0041070009100741d0440684110104219084503072881801002031440c4090720764500380752103154080c00e800e100034402a8204000580319000c0c0c00100c0e4041c030382d5031000480c1903109612000d81e511032038003901da41e800c00c0e04000b03584004404003501014503000300040d124038a0000844260340c0f000160311000b0580c0d004000900c0e41c03030350702c1c0c00300d548905810b003501c45c40d020b20901440c42612240c94a10001640d443c2e000360045080c800d142c54207034140040b030a51a4225844101c0c50001c0f880e00501c86400f07405003180308030040440a00d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 862003003 1250 862001753 862001783
    0x2120a0822020102120a120c0e1f0c0809030c030105010605071a010e040b13051002040303090504050106200309150415020c0a050f060909040b0105030d09030302100c0c 74
    0x2105042078014803014004980ca000104581c100c11401060000c0c05684515a400030340e4481e0000740403030041a051a002181146c02c418095a05100a01d4001488604850302600d880d02c0d540303040c030014804103c5501140800640018080003000d8480325000c2400d100981c0d04108090b03e0030301c054020711107540d56440240068200344011540c2002d40107044d12040062254a8105c45441d5000d01003a12103881d540851480500701221500c13454603a071001ca207080120407143c3c5803040005954a19604000740501c03029001207119508000040040700c2d4426146030000c00078500301e048003001d0864883c5107214070702c000c0e5001400d01c02c0680d0244e048901070320446062030608201a01c84400498480c03860340d419940c001e0103450280164200201030a40400f009032546103000c5282e00029050802101c0c01c80b00b21185100602040c00c080c442d8000b4010142860040241035942c082e45a0540540000d00655107a040c102050710441c148500c4036080b0541030f142080c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 862004253 1250 862003003 862003007
    0x3120203032703250c03150605090105030a0204020a02030c0d0c1502091e0301060504050f0103050c030a12050d020403020d050706090501091a030a0b0306090a1104140a090302120a 79
    0xc2107915690000b031240c1609154214081a408044100409507103130410f02550038000313501a21103074015284002d03e11000407110040e407070296000b5140c3c42c1143c0c1e0303a96051016a00c5039001240120340320030040245440008000752180d5049801580b100f0011804908c0e500402e440307a025842160b003010785075508030060400341402120103503501201c460b000c405a02c602402e8580001d03400e000c40c605818540c078542564000200081402030380c55001130b00b030b24800d03030301a655080000010402c1181c1000800321211065018180e0b00d0a1616a0004a400c2100c1c190038040001044400164582c0c120b80103580d00400380034082c00d890500e16541d0070707140540d2002c180009408111580240c94007411500204c174820849184582c0c80100c40d00060545843e8648039980702242da42c2c24041c0c14481c0384000000c2c01d510103903040c03c08901303c1095210340582d03d000c00902c2d0ba50880c00d401640000b00c2d17140454101028031b000c9240c83c0100503081480d01001c00c0e9204a55 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 862005503 1250 862004253 862004257
    0x80412051c080403031a0d1202010e03040b03010e0106021f0522060e0601090203090a021c0b090607030f0504030509120a170c061b1603050d050f04060e0d0f050f0403120203 76
    0x2030082d5420802035400d101b01105036007028054a601844000b840000142041c000c02e540f0fa0091001081e19111024201d1440d04035802c000480e207801300c0107104005003104841c0c0101103901c01801079060003a4004146040c01c1c031101c0c0c030503072110001106641e80360b824401d0031a104414540081443c20b000c8000d1207502c01e00310842c0510000015400381c01d00070b82c0e000307240400142001c0d0406034208412900f0f407104441d00003d00342c85800106071162041c610600606001d010549010340c401412541d42841c440744c0c4618100038031010980c414141d407403400040e603a07405042e407000201842e103101c1d040020031502d005416404070040c81c1018140c40c0041c14100c42141d112680c0190000794640301c0b40070424414460042d0480003164103880080c000d06082d8034086002d00704070150380080380e0319140e90301c60b901400100710591280040c00943c0c1c10242c500104030150081c01840818403107400c000c0003203103213104208290111802903034804400000142070b801d001c0e4a903 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 862006753 1250 862005503 862005511
    0x3132102010b01030516272603430606080f0a0f03270e0103030909021c0507030b04020c07061103040f05150c0f060f06040603080412051c08 62
    0x650910108800b01c1d4020300071180038201d00c030214100090035402c12a818940100f840b0031201490840070711112070825070300084c00b20b8030054a0614040c2d14680d03d41881503c02240c258000c212003045000c6c090f1440c10b40141c40d8048036041c82000c0d0b50394041d80600106560141070380380c100010044580d202000300d0784140c0980c0c0c1c0260890400540701e1350942030260044414100480c0000e20035405130400e6652a02c1c3c941c000300074061030f10a54640c07504100140c402c4200140180f542042140006048ca8070040d441c1280c15070160491580809503124155124408101c140b4002e070804045200040d10464841340001009551440300c4c0c0300388400f041c0e006425a41000e4003204480540d0500c01426600603d04003c1c4414004103020101c0b84130014000910500000d000180c0d40d03a00310001445c941c1403a0303102d4514801e0140002d8421031400c4000c10004121030141d80c100e4032401c202c4a4201c000d401c0c620305156005604c05500c1c1007003800b8009258000403c5030013 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 862008003 1250 862006753 862006757
    0x1f14060906251b050f120118030c030e0609310e01020403060b060310060e01050906032701021822050f01090c08010e010b071505070c290c031321 64
    0x2a9034050803074030f000300d0403600481d50451302002c0461140d0809120750380801908130000909030341c14144001761b038402c01804a000030480382103c4141035200102e009440b0048864074580b894420000c0c040100e20741560740c1c9603e2a8420000040c40d0b812002d042d15214402070020382d019545450003944140812200ca901e0020750180600b006400d9038890403002d520440f415042800070307200c2c03011a040e07490412504000d80c0c1446d480d44c0029500500c0441035040044546408120000b26982d040340b586a00c1404281c003081c1c5480c111b1035080c441940d060382480d401480d489840f0340c3c8840800d0f4403900b0402401172043c2c3c0808400d04846140b1002c1000c3c501907207088868440a01c03a2000c010203a00c014001800040028440306100c1c0c4145819000e016044c00c1c1980c00c12682c2c080400c1c2c0b01d454042c00c1c09002c45110741c000d0440440c0c0d00c411940d00394005140d01c000703480c44100c2c010110010310b0070b40a52072602a9281c001e83c40c16402c05000510700c103025151008500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 862009253 1250 862008003 862008023
    0xd090501021002030c03040206030a0b0d0f26190c140a030f11030301030611070b07030b0f06120a0c0c050106080c0a21030e01180e1f1406090625 64
    0x202c5444a100340ca001d018500c9805155403142c0e020060990406800c1c26401076654000340e8040da07900c800a1400b9110340390541c0310141c0c509200308560600d807047c40704500c1402d507403d8607800c000d0403a4094412441008140004c03076a0031900c446400c44001c241c59000014900010000103004540741c0c8696542060404140c0088445012140700302290354001d01c0184001451600404004480440344504114003522520303400c07803003510f002e800300750349440703072041800c01480100c1c81000a80c3c07141d181c0803400651401d00000141b004810ee030303951100510540c8140404040a0f41100007440741a803141802c2e038442d80449170341441502180e40c000380e070b5010300880c2070784d0384918249096050603076142a40c1ca440324001c11410803071400d0140001c83c0d050850741000d024051014140c62801840003030681c590307003641046500c02e007041000720701e0880003800c4144209641c02e0740c44d29a0840450024000d0003101500070328420780c2109074111445c00400400d000d03a114070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 862010503 1250 862009253 862009273
    0x80a020f0a083406050c090603150306160801030f05030f0708030109050105040b060d0504110d03050301080d0507170a1403090a02130b15070c031202060403030b031207030c11030d09050102 83
    0x4a1415500c82429100f418200741e1600802c3e501d601c0703035074031041d40046a481d00850000090265000f142c0b0b25071402c81c1c13404128110700302007101c184d100581c1842e07228041021580507021580c144002081c0b04440a003510801c80d0034425101c0301c1ea500211075031a40600d18144045800c00d0140900540c03138030700001843c3c64035004005901c42c01400403880c1113a03200e95440500b00040050720b003081c0f50a0805d0158652000c07034403803d070180d0b458603141c1d41080001c90602c000038140804001c0d00307101080100d44042c84141c2d0080d40a040656120810002030301c8610091300300075414140801001129040801d4103030000f4070840d80c5070b000c218040d0304a01203600403802d445d0482c0750a10400c54138400d0744002e02ea810b00640d550300116950b69120180c4140655031040180c00610603c400c2540600440e448404100d0107401920301c2c01f640c1003250f006850011f0100314503441e00304c0500413407207010b5820440141c1079035000100c041010b00040228031483d40140314100d041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 862011753 1250 862010503 862010557
    0x10c02060f0103061a030f071d010b040512010b03031206191503020d0f020310030b1308031b0d14071107050d020f152b0b0904080a020f0a08 62
    0x90311600d840704440304240d0039910741342c0041c0500441400c0b6411200410207407590304004403810f80d41c4103401401d14070300303102450b00c41a55111700310f51860403050052200100c03500944040c1e4600740c031001d82118403440514003400c0700390700b950340501000429042402c242c4800f184900c2f01910200514504500e502c03680541502c5440b10200803549540f45d071a103e5002020722641d00b040110f854408010070200b03d92054820341340c0d07041001010401c1010390450f00303501083d0150304c49120750443d1540a035a01c170007400905101038903004603102d44110f10507240c6c40500050200111920f030684451205020b0b01c803e00840c10301c19400200c94400106041520000b40082c41c03400065030078031440b448800d1800382e10050700040c00c2003041c484070241003800c0341b04104005c445541017206802d900c2001d2000403181c10b00681181a031903500c031403a0403d51068a0583d204e03481032080b40fc00c00038401e03550003070185a070700406001d245805407241132800c410f0700b065811504d03c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 862013003 1250 862011753 862011763
    0x1502190f110703140a06110307030509070e04032a0303140a060302030c060a050c0f010203040c090606020a0308151302032d130516181103060a1e0503030a0c05010c02 73
    0x11000303095000b00c10901c00600d544d200480c0e1040707204116041140160303900760a5a5400203039840c0100c01000304101a54140101600300c074054001d010014100504450004001480038060101d05400c01443c1c10111030910a040b2156140445041040c81c00030007030b0444050729800321b9402c0c4082442842c00e8032811003141d500500628580c10624284841c40e0081d0280c081070040030b100107039003110b0a06c82184043e02c940001a501c4c5400d203010540110603400c0642450f2410909010b06a0001042420140c00d42004103140c0c0e1081d61411a406125040c581c108104568121040c0c2d03180e0080c60140110240c20003600f16081180d00740310604080c2d2450a8102e880400c03152808200008041c4c1c3c0101c0a441c07a1650000300c01c1c0c0880705503400368070340e508040b41c0d50035104900d03c900680f801c040e043d0721340386080800006503840c0b00c50245955500803048203580304441c0c604010000c10300541500e895a03001d4001401c2801c0400d402c0e40d04d03509045079440e0062012075 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 862014253 1250 862013003 862013027
    0x31a070e0406050a03020d080f070317011505041e030516210b060909010e0118031d0f120c030a0f0b0919201302041802030103120c1502190f 62
    0x400c000c4c90f10395002c102c0c1541c581402940c40c46010840c1c1400040d100e8020000b99020303031242420a0741c0600483c01140050780300c403008488031035009120961000890b070032100c40a120b503c070b2580350f2030304648200c0f090348028a244614041d00c020401c0599426080702c8440f40c0250001d103480701c10302a5044581c10041010401d6000180c030303490041b002a4002560500018103080340c1c0010300e084804481c0001c88808681c070800e8201503201c3d607410804403000d0904080301c41a803020804403064034048901c01e5000446048005008110740150000000c0496459021505242d41100e90b0705006862016000c000199549000074040780030306a50081038817052444d0f190b0103940762404500c5071030503c2c034140c5c2e4000380c1c3d5400e50003481003440410050741d81c2d16000c22944444007000e04040e0060050004101040c240e40d12080c0f00c02950410341040c60407850b040c0380040072540c07050752452000c03441c21034a000003101c1358106159501c4040058003030b06016525540549 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 862015503 1250 862014253 862014259
    0x90c09040501030308101202100503100b030103212c04111902010605060c0303010509130819020c0d0218100b071b0e0103111306150804050106050907050403110a031a070e040605 78
    0x1000c0d105c01c1c80d10030002141ccc40401c1001d0000020388030141111554007c5e8000d44404103146603912000d0001d091500b401280f5040c001410014030740c110002040e001c01c1610f000c00020f060704065151608007855680421241c241e80302e1410028102c1c070640c9600704401507207850400314442c2818012582014078100046003186e103042c1c204902200700901c10110250150003003800a1000e50103020340c40301c0c0407400480d0541c419030091074400b42d081150700c42c0c04941012009170300c0d020045080b030400400010004d50f51122440824440c41d407258400140c002644014007041c00000904505144d10240703c0ca84d841d402d200b40c80000380000703080780e0000d40e040c0702d242c41c2000c82108040740701000884c10701e56408092104541041c0c115021404c000c0802040080a01c140b1002e010102c46172002802c1c0030b02c0c000d0a030300542c000148082c180700030a885c42d81e1044200c400540e1720420b03210400920045001c0d03841410764a610110321059040001468507007c0c80302621005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 862016753 1250 862015503 862015519
    0x60c17031b070f17070201030b04200f04030b07090810061a0d06030615080601080d08062e110f1b01180902040e220809090c09040501030308101202 65
    0x403100000c2d0340494801c5401c0d241c89580d00000030101e05018480000182410b501c4245c540009002e035801a84618030452038108043c000c3c500070809601c4803950035140325100d00f02c40d13100c903401c0c3c86607400281480c40001e00700204590702034201404d8038290f0007503503881031000e800300041e0364640c01841c904401c00c00003044800d12000281840c8030240e41c01051040c2c2c0c94465100300c40845040c004001d42408050100c51030030040c81c0d0062407444014405003060b000028240c505c080c200510442c103d500c0b61503048450021a00b42c08030030070002045211000011300f02d400000782128044c024001c000961940c00300d81c0a030f005d0034201c00318524441c0040115582c2320004041c0c924187c403a080400c160a071403001d4005007040620898140c00c102c0c0b6010b0028000241524120909000542c0010369800a5402c408426200790919171149078480e1014042c11241d19007144c034050000050551083c05580294084040300c800c140c0c54003050100c07808900360194200d00c1d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 862018003 1250 862016753 862016791
    0x1020a091208370c020604030b041401020409020702010e03010c0f030c030608071706090d050414010909051e071817070b0a03060906050607050c09150a060c1703 71
    0x2110000d810864814240a450106107041e011107500e03d14a004160342107401c4040c0110612420b0a000c110301d03410300c0a0b04860503070000b05030b84030b1808010710103880c3c840802c00b0080c0110b4036071001600e00c4000d54407543c5414280009400c500416400144072202082441c18107200301d020305081c50f0703a10a03c030815002c0942c090070f100c1402d41d04060717540000140090702841200060b000501d03800301d110000c01829454004094100801703074112103103d5001c1600141164121a40554456440d65440c00140d5094015a10080200c0c2c01c01d0100030100052008490b2406003a004009468aa0350f10884008180c0303150f0001c0604079070710910040000e0300072140701030325a6040300d62080d00c2c1d4001c21119040050040040390311480c0a00480f80140a84c201034070007600e4090030500c050715002e40e213182c598074440c0a00380300400b10700010201b0740307814000c000203003440ba0312659490005100355054034058444614048038840409130101c122402200418450807200d05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 862019253 1250 862018003 862018019
    0x609040201030e0c0d051501060305220312050c130801061d0a060305032205060702150c1002031305060f090d1b050a11010e030703020108010b0906090901080703120201020a09 77
    0xe8000c040b0460740c4900548074559a403105050440b161040d00034122148880308460fa0b50801078026104ac94108410040c00c040d502103104026100040500d03a00c2e0068201079600d00024118000d049082c10100902218820300074012101c2c2074800340310050344c4150190886c6e00c035000380031400c040c0003508031804c0d4058480036002031160f107000900696a6550301d180d58070007241c07c50601c12a030764648200030740b48105801000305032000707458004641d0000e260300300d8420300c5410f410710103e91190700303490420404807085410035085599041215207a2280058000202c80c103114190028800c2001c12030014010b80c08d000003000308030f50030b00341a1010380d0011a091543e9540d01030071008510100030402e134090080c18482d403455111000100002d0700d11031140e0103a0b00c078040c00c00050b40c2c09000b036411500c010040580b14074452002a596110300c800036a84001c1766000801c0d20240030134214101c038880c0c400c845e094030070020160309071b000d13030940700300410110700b010401e000e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 862020503 1250 862019253 862019261
    0xc02180609010504380112110d020f0904060303020c0f031614010203070f0b0f0606090a0608100f0e0601022a131b0f020c0316090c110712020f09060904020103 70
    0x1c0320040d00b6404000c0400e0341c240c014841c44a00340204102c417590304135507581164100b480035013159018040d0140300d030307201900b1717201302e21b9520602540007039580400000e880a40350501e400410070b0200c20307030f00c0c10002d5a48030408151445a1000e6134600001c2c034000a02c0ca8031540e1a500900c00d291800107901500326010340800d06501041041400003042820b090380380034810a05018181460304000044040003402280290010401071000c2d6072000d408a04035101441c01c1821651016291012205903a0003503181303202d61100800d0300200201524401d8600782d00b252001150b9060030108082128001251b100c3c0c8103010840030b040210404d40d083e043c51002140120810309440082190300821348005840d0780c1d810700100c7ea0511507503040c070b98210010061801010414104160144580c802095480302d0030440d06002c1c2c204224a0280c990540c3c082d10395448902480200c0303044100d00c64185900017183d0b610340001458010300019084080f1a500ca13030042d0010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 862021753 1250 862020503 862020521
    0xf0603021611062a1902130f18030c05010b06040f0603020906040b0714071e0e0417130608010915150c0215070311010b030a0b0c12070c02180609010504 67
    0x410010080e240a495441c0d00c404c103124401100301c0004516512150700300001e400480e000d4444040803000540e8a54080c01e01c40e54035a180014480450108200200209000840c3e003211201e01e50013455001b003401d015541c0a600240080200d5008020082c45280182d61150602e201c050010071320030380c090b00c1c615034003401e00d9241c86c2e2500d002c01516003140d03200700c45040c400d00c0342540303601d03050080c480180300c08904940180096280d0301074104540c0500b01d0120304400000741808490808a5034542480c142c680e038403801207810f0903100c05c1c107008490105050a00008680001384600e0312400d901c2618101f0060910214020f080d01607043c032410810b03a002c0760300c007580d104403d0b903e4503400c82103610f55840041c540a0141d010607250382c1003030391410f280301340e0603200400d10400c2940d0180c4044965980c440801e0f06500030105031803030720f007210010003414580092200880318000c0300c0f004040a01d00e041405440000c440f100e42219441c40108031a0400d50024401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 862023003 1250 862021753 862021759
    0x10b0a0302160f120305061c020121050709080d021b220c03060f05180402011e020705010e06030403020c1e060304081815091306030605100f0603021611 67
    0x341405110b01c05a0001a6003015100036140b201c0030782c204810500f0740c2c48001c03e6030601740158a4508000354005080725101c0f81d00f6410014480116803080307910a00b281d42c001014400c03068040e4040d002000d04a4580c000b0070303d40d04012a41400000b00d8170010b640a90090000d290390702c1d0800c0e45c107980c0b1081150071540da480c814044030616401d00e4032040811000065003030360440c00500743c412551001000d641c46a20501c010303124030030510308a00404038a916503444500c01201d042080f13003030142e25529045940b0050070380c085421000c88a099036042e4181c4444020401d0741d21040e00d0040250b40006d03000800c9040c04000b50342040c2c60622208840c011190200d03041f03070b00c1150101d81022001402d1000c03200021400491808240e54910201c121000150828464809c0d098801d801d80c0403030700090401500102e000d107a120a0600c8a81008440c1440302d4855014160f8400219034000c58118803d2098654002d205581403c101130183c64a044a1403004000d07a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 862024253 1250 862023003 862023007
    0x71b12061505060c0f01060623031b1c0b040b010518010504090c020606030d090305060705071e140f0d140c12041214030f03040b091c050c07120b010b0a0302 69
    0xe050380e4443c0548034022a28000c1c00b03008412035501803c44180da0010014031005825841e10b00c400100725403500700c0b4615607180d89449110558102c13003502030380400c03010400a0307801000c0d041207400000e05115540240030501e010010001a07452502819000a1040c405202c100c014074000004002040c10981d10385a10751244006880e01f440e66000542d112005010182c1400c00c690540440145088d000d50341c1540e07a5152114005046001007000101e43da80c10b00c603065017a0b030340103010840c0d40700c4d000c455850145004c505030103000000380a288002ca40301c90000c2032078271001141c1d540e034008800400d0340c007550980046094810920450f07003003034200c001000050014004426500d241200d080c6080c56140130b03e04005001508140300001d024030030781041d40d81143d4004904030003580c1d030858a0340341070700000311071684207400d41400600743e8215005003042e140d41000d44020b00d403510f4244003403c04d00e00008200f02c09150040001d440f10b00701510307e8111a00e0094 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 862025503 1250 862024253 862024259
    0x130209040e101a0a031212020c01060e010305160302030d030f0209060c07080d030e06010501030e01090204050a0f0e060910020310030b010e060406091505040f060812071b120615 78
    0x520b4403103103036002000c16540d0b0002d83d0344044030109922490b403044441882103400c59640c50f82d400440d2219205120070780360707500f012103181d40656488a820900801081e980c504403410f480c1c1080c4426600d42c000c4080320100c5c60300c54240c0005482d0040c0007807021112090084004051000f0000ea24690074410001da0f55285002410307440e082200800c5050304060865050031000b1214500b494a801c44540c041500481e246046450909000803507140741c2801c5805403880308402580315107000104603020000b030f4407491500045480810402044038a1241c0d11501a5402152580054002003105e210782c2c0003154045400b0b1110f034812981c0380e540741b04a440a82100c01d0030042a0100300351800c041c81003030700034101a20107021104801c11252000d05440c024180101c3d100c9281c441101d0003a0010320083c45040b08541a091000740361140c603810480d0708464096001d09480e0811890000180940c0c850501f05942c40312156901c0c001080b102d4420703886011442000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 862026753 1250 862025503 862025531
    0x509071b050105070905090702060a270b0109150f090903050906120702100c0e190b0408100c020c06040b0d09200315090709020c070e0c0a120b13020904 67
    0x441280c0384100300104150400b40d001a00c0a11960441070064140e0410800303003580c0010400d8200014000c0060740b540100554018441a00c04150480004a4801040102070100c86048888210040001202186091824131181d200e02c22103454401d60a028140c4554417414404d446410950318011218020818503000210181e010454210421941d2074041c80601c11800358031004210602d03d02a0142c25220811581e500800002480c1000c203c0c0c805c3c00c450142c8405c40125469541e00c081e5182c1d180801040b41c0c080f80d00f0150007120040c000039603084040781c0108928141030414141c00344c140c21410b40701c3d05d05030300c0d40482c030301041c1050041014001d050141641524180c020715151100140c4500c0d0034600f40e0f000c02603005000310b0494203448a255000d03aa4124004002d850a080c40d00134220350041c6a0521441590500c02060002c1300e03511140325450300181003d04850080c00c0e8a5008002186100c8124001e0380c001d040c640c0e001440000e603044050f0718 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 862028003 1250 862026753 862026797
    0x6020f0d110f25090504080a0e0103110310031403031006050a180609060806031513021906020f07170c01030e0a0b07030b030c0a0b070204020c280303060b0c07050907 73
    0x3a4030400d1100100700000440d03031811400580704c02d07202405141000e41c0e690070035105540c80fa0701000811004070565030b100f50040c40c00c0d43c40224100c0d8036400e0a140440d9100b03440d1004407a400da0050700c0401b600c40101c1528896884583c0a03079003945010000c2d071722544007480340ca040181211804000d00503000349103000d414242e54401c4860304100d03000e404e60030094451031007980f201071840c0c0211080b04a41e603100d2607203a60454040070910102e04c043d18100c10903e24209601c2000c030b40d481e40040c9100c0d42903014001c613000603613280f848040c00e035002240002940c100c03545011072540207402c01c0ca101c1805400f1516095982c1e02c070040d00f04402d80300100041e441e281d600c1d280d4035041040340701c5d041c41100c54074a054a003d240901611840800034090303500070901404000303003801a80c06910350505036030302c00c1c00d0112100d40c800c0340c101812808245025800304804007500282c4411144c07070001803ca46007030600308580780e8401040e0070b0802100324100800c06504883d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 862029253 1250 862028003 862028023
    0x5031f051e0f1501020f061909020d050c0f1e150d0c1e1b150b031212010f08060f180304060509030d0305070c0b0901090b04120906020f0d110f 63
    0x241d040d05030501d03800d80c3c200e00c0500e2071000d0465200e0505200803ea002c581540c100426030760640c051205000020094452884003950204050210303c00380a800300b0101482c0074100c0b0b00f0280906110200401000c0c134075130005030444982c8541c240c6e030a001c5910f9210425802d24182411016041d0302d095a0b8402038803030000b1811b042ea910180482c400c2c0500840300f60a00c20043c02d1a801e410100c1a01e52102038032040c00e030b4200340d020064651185030a654013600b52801040403c01c5c0049541c080c40c6c00705004480b11000180c0c50084511540039505084090407441c0c6030205804081e46000e0017000d1010f02d9000c1d01c6218070410001080209655154161a6424402018100190022180140350601c0108560207502501203085940c0c0903402010741c0d103c12a12138010400007000030101c54442c02031005210f400751000c034195849550b04d01c400ca4680348102d8841039030700d010900c0da0388000c1c581c1d01d0240c00341d08110200080003088030750f000259a281490610050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 862030503 1250 862029253 862029271
    0x30303090b06042906070f05060709152106050301151805070507030c03050408030a0504051908060c07060b06030c1e0a0207050603040204140405010209030705031f051e 74
    0x4500e04200300d481c03118140e0014085408004040c04e00144810702c2d0414252a02c509070030a1241146655100035100c0194110001c0c0101c0c81051820554540d0150380180c0421011203002910810075412041600749a5603034000202140364410505ca5044045449443c1c84840201d40e6440034401c20040714131017005006014078200d503c01c520328860048030059410001003282050308202159811589440c010308000e205080880b02c5015641102c00c150000254003da6140d0040151040d03a40803120104801c8061003401c400740c515101e0034500d50003040010f0200c800c26000380a2aa00a020105464400310001481c50380216140404074401142c04548481c022000c080c00d01c5081c0c86d49464280010340195a030201c9204451161100100103801c40d111504420100d10111002c0610b905061410714040d40010030002c2c064840c0b52000200c529000540e030384201300107000b403490300304090031b0940074010003814089900d81c103210000002c800900124070581c804 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 862031753 1250 862030503 862030511
    0x50d18140c0f010e09151210020415021609052a0a09050109061e1b0606080613030903021002010603050a08090a0b0705060a0b120d030f05060a0e070e040b0a030303 72
    0x203400704214000c2c1486031904210850080115940740c0006130740d08500e181141201c1c6a076000c0000d10310303100e0300a0703c0c400381c0545a1800300100c00c9401400655804c42410b0f01c0209010000300e980361800c201106c01050300e480b00b0018140540d20054000c0018891100901070b0040ca20b59a08018070449030000c00004044204e5076000c0f41c810050103092800c0c410040c50103400402ca0390304566803c4140302024284200e150080180302c2d8500f8030102030340030304290b03800d102008005510503d0050b005600004154100060441d03482c55419103500441d240de42c0c081c00f02034401440030209642d610400800464801c204401030035105d16a610341c2d501d4800b0900000040e2035000b0070340c404003402054002131000c1002070384140722800000e1510020701c00110301540040c0780011600510101410075a815000400c4241d00150140199220901030281000c010f1050801240075071010448052041811503026040240081004085040002c0c0140307095440ac801003035071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 862033003 1250 862031753 862031773
    0x9101509062903091c02011d0a15050720010b06030c030a1a061c11270306040f030c08041a03040b09300723070801020901050d1814 58
    0x650341c0500e4800c20b04285241076040240c9159564841040d1081481e0b94814050300c40610035844041c2100c00342c484d6600044031042c2560711891040402d4803010a2104844040543e41c05024000d8005035074461905100644010581050145180b951b541b5858031500e282d58180145011703141c05520281c0e47d04041c003228040340c41060030201c800c0701002c00c007071107580c5070815a00300749030030004032800c1c00d1070940d003600805c0040710407400610007007005121051002810011061407041d0a4100c00c0c0da2820582c0d00d820454004008140040e081c8000038824103048d0710703591143c0a0681000d031907040b003540c400e0f142c0b40c080c800308802004020a012a0321902a044209240501080c610390a0026419106008461514035130350080350403002c21901203d2005070802265000c44015030010b4068080200030320201d48504540851049410b108031b910044050310b54030b2908940f110118042d15441c4422051030030760380030010125558284403c0b210404002404030281 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 862034253 1250 862033003 862033049
    0x81e0f012d05070507060f0216030206180c090403300209010801091806050705070203010908070b0601050a0f0e0f210d050403081209010b1f090b030910150906 70
    0x80000101501c5604090500c80201d070000c0448404a403c40d0005c181c000e24078074014080d204c2d160340c41031582c0d0412203803000d0560200f0054026102c0e442414400500f10644507502e10003290016402101103000c0340000340100d9104140345140000324140c080f4600701c0c0100449508040480d9580000c0c0380c1c105036034041c14450242c102d40740104213460807404568228840454010312040c2d03654049810741d030244059850035035009009002606c401c1c42c0c20b5500c0e40210000b21003c80205c800302e450b03980540180d514a0b455561800c0d52620020411070f281c980d203030250b079080500102c0d000c078561a0450a0840400072000070b04280880307004141c40e033104080c1034420854144002d10005003d642160341d42011760b0b0700907045440744282180105045190b00e54000360031400811001d050041324200d015190711440403040e0b84100c2142180b000b2921003400e50020180041c04290a5220891008000664402c59911142c02c107085440c2500300d5401c43c00c1550351365210503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 862035503 1250 862034253 862034321
    0xd090309051c120801150e03031309091103030307050a0c060b100f080c04061d06160c03030e0303090a12031107090608011107020901030f060e1c0e0109081e0f01 71
    0x1013840d000c4500d43c5800c0d05010070206208100d000c0080200c5048400c0e0703010010f0725003020141d1540c1c11000d6031421200001c00b5000c0003256078200b2110001d42c5880c3c04001e03240f24080301d440340c0f441d0030301d1413008540b00c3d040f120701200d65a039581405569a143d41c80c202c02c00d028240c698220005580d1320140588400400c104a442d070108001e0000951001c10f482000808808030101d81e64400005449030103611450340380b038200c1c039540406000b020343c90402101c0c001c2e1684030741c00c2d02c1c00b01496100d2085011164200001700d0040004080d5406d003041e0640c083d203000300601d000c0c500d0042c10001154854000c036a2621414040071100303202d440c68020300e260026142c07441aa0216030103000502c00503060025440d84402441002c5d04009180d80b010030589d803960411180c0441840e076101e2803900050035211400e00554050b1488009445042004214607503c019150007655200c41c0b185d15140074061124a0450007400b17101081c22544a1108200600100220540c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 862036753 1250 862035503 862035533
    0x1202120703030e1905100302070c060e06161a16020f060915091e01020304060501052d0d06060f0e070f05090108100b0315150705030d090309051c 64
    0x2600103500400009410520b064040c07070040c0c628045450710240b9580c0c1c29a103aa03c281d0300000115407441c20545c0c59402041c10510031102924600d84501045458001c4a06944e42000d01004400400c0b10307420007038003819100300e41001d50f00140304030781c444403802616106100039410445000e040d030103000c8070010040b508003c050515020900517907800243c201d542c90880a0008541e84410a01ca00c00303142005010200441201d651442c0c000d610446040d00c0c1c2030b1070840040354034900041c10003403900001e06c010040714028815181030380e100d00d0003039034000c45003070600c1c00003031950160781c0080000c01c60b0203500070302c0c01341c44241c450002030031841000f601d10310610321a60010187c4038505000c0c681b020b0a56211650131284250a0b001660710f0070300841045440681e142d503551640c902602d50a6020714500c129900c64080c524004003036410a00468081103900e0b4000d5000d64000d24001420656501c04650264080d4400c4030100c000080354a0a02480c480500c2030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 862038003 1250 862036753 862036789
    0x801090c11060609071115040308070c031d0a170304050f031c03150e0103050607022107030302030408040b03091515010c031818200f0921071202 64
    0x1040c0000728058440000400c00e912031071001c030100d80b9913482100c10b079180c0c80b0210102d602164842156803120241150304500050411340000c6446220b560000d01071907254981c1115600b00821861400c0b64100e012500415680300004001d0341906031914652195000346a40d03d08040c02c0c414940e58100045d80650702550403810400160081e50084400b030f4940000c091180404100e030101c200d51107040381c41c03600d00001c41030120215000307005030415000c566a170b1002d00c2c5500900c1d100c41c084660b4409040c8400f0b40802c2c0a50000d542c0300d48603044031072420748c036420200020740007070350612820b5200340704284410103400903a9400040009000c0541850346c000240403440c0c0240003000c100b50464040d81e002c1c804001301028081e02001c1c456035aa015811000800444808005100d0040101c500d400c2450307007200e4504841c0c116581c9007084120500606444040150115000c8502001ea114000307000c007501401000054480241700c9004101d000031800e803a680f5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 862039253 1250 862038003 862038017
    0x903020c0a1a0304050c040f0e0c010e0901090f0905071401020601090203061c02010e030a062c190c09020301030c03060e0c090a05090c0a03260f22150801090c 70
    0x10500a9012600101c250801c1c04030f540c0396900d2600c0c82c245a10840c801c0c0d00a4286500d034800b404143c2c005410b450421021140f001d082040110f0314101c03072841e01030b04081020014400750105030840e00d9958200080401c103c01d2a580721860b10141d9842603040d40f001c2401c43c4560360307042c0a1107006060b880819811410001c0000e42007078070134407421102c2070442a00e0343c11a40155252060610000c06581c9541594140540070340b5101080501e15101ca03070f4103d42840d00203034105010711443c0000d2800d60566841c8003142000032105484900c1001000582c02883d4001513018501c07401103400401c0c43d514050381074038401100c40c0c1d45900012a0688540c076074800107a0300039500300c0e012405480d400e0700c1c01d00b09151205040d82224100e1008410300180020301c00c0304204a0025070380100350040a00e046004d0000c0b002508603040101004006040d0340003c4000e940c030700c0000841d43c1d00e880f00105074604c0105400800c07028001040f04e13108521501c240c0000606181d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 862040503 1250 862039253 862039259
    0x729010b0a08040201030b09190f090807110d0803010311010315031a1b0406050306030f19080a02010204091404060e011109060c0106080303010e090106120c03030c030e130903020c0a 80
    0x8032140241c200d00c4041001160000d410341e0702c2600100543c0c40003900900303150074188910840f005000c07054804560415400783e18410b2907109140d5002c0d0054a854141226552080158580c440307001d07500103886400480810301c0003004500840c460000d800e229990030b40054290341050246036000104a5010400310304d81180c1448040714414464055683d2400c0841400451000c404c00c0c0403c08100820070f5a0048001d5004440071412600403241d003026285d0303a01090904005101c4010b0000400129031001500e003418540c00050304040d11030881000b122410300d41c42c51002e020300203104c180441e610400010051940003881003122075481102984500300003d809840c00040f0b41400000c00c1d809071000d01280815603a403541e4400746007078581c0e0f003950f842e00700b540f038004005012a40c1b42000300e07c541c2e0103103030f003e041490758805440c0c0c2002c03600203070305100d080c1c21250103c0d502c8044140a40381d90520000c0c3c112480d0800038030b890f107850182c41c01001008414 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 862041753 1250 862040503 862040519
    0x906040c060e120304170c0d0503041a071e020f0102060f1521030405120a030e010305090f0109032105060d23100203190902090708070c08072901 64
    0xc50250380441c00e0901d0860900e00200300400790385614450302e40400f0401168505219554003003000203803040381c0e201c00d203400c10001c07c40282c060043c101e9008001c2000415010000c603110548018511030500d401c0e0784030b05031703104210701007040c0113000c01035000118070340910100090781c0284001c0195203030403944420340c2c903800345c40c0400e039134001e00240c9056a1604041481c0c404051014415a210302011640d01d400a01a581c0302e100d490605600c86030002490850060301640c60540d024a2080190000c000141c00e80380c0c1e901808050721068003090140c8503c50307100b691080422204211785002008191078120882424001402001e03a1070044800170b4541000076490004a010504160413141000e03445007406241203090560415501851181105080321030705031442981c1d020441e0207405000b54083c958070302040d07641740304120580c2d00c908281016155503010f500d5400160300503a900329154140f1030740c1d80148548142000f5251280c0280f1042694140150 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 862043003 1250 862041753 862041773
    0xb2818021c051003140601090606140711010504051207080f0d170c040e150a06031b0e0a1a091309150c1b150b0613030f021203030c070308090604 64
    0x1072550440d48450100301464000204030000390fa100b03103c180074005808609496881c24800c2c8100d4903e040d000081440c0a100c4c2c0440ea0b9141c003c0702460b10030223680c1c08600919050140c3d04000c420302c00030415854400501104400000090030341ca880e00c001c1c545840c0f40143c520383c5a07049501e200c0c4050b904140114601e03018081081803035500c0780010940d500580e4004984080349505010345503c248803004240341003a9100c00079540c5580307003a410384442004030003100000c0c11103901c060f44107003510b001d8990300604046a00381e45024226050224424103c10191300203120741080c0792105c8840c0c26902480414040100142c41d4034074201c0054840000b525214821403a000d0b2180d5800d8154640118100c070844400341040b400c0028403c003500005490881c6000d25442d142d010f03034040c4400920f0b17a4142e503007160380725039001c45103050483c2c004d00c1544580c0b20300303281031001d180300b81c16141180352529900c3c100241071403000b031300c605182d802440a02c4085013580384 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 862044253 1250 862043003 862043047
    0x14030309010c110a0e19020f1603020106090608151f03080a09030c1418090709150b030103031115130602160b0406050a0b120706030b281802 62
    0xa01c1c0741c4000031428000810b21500a22581c007002500780401c1c1c0030081172640307001d02500e00c21205140440b2040c04100c1c0300d4960700600414051200d60302070780301c0410304031850307200c0e10011031101e036500c01100c00e440242d00601801e41000d28061140041b01c4141a4403410a1310003076240c0da0604c24006038280c00c1e00010700f0003240000c041d40320f2030207802c0c06402550b011111800c081d07034480081d03030003d0003081c0c294400d500403614254410812842d6900403070102015040310345c40c00940500034250742038280b8124401e01d200060355610702018500842c060b459158540043c0326003a030600c1180101e0130a00c428039814046902002945208015030213400160390300c001c0600143c0100c80c510000701101d8288041108100091308464010000c408082c800d00b0603d208000c420000000b5241403988071450401503a84203400890080300c01605209091a903000c80000c400c61603005002c21180c1320208000448880007205802002d4038801c41c1005c4080b84143c5605400305 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 862045503 1250 862044253 862044257
    0x30c010b0a0f150c05060a020901030e01090c0e06030a2a1e0302040b0d051902011101140f15060d09111e0907050c0a1a010e04020303040608090102090612101403030901 74
    0xb16000b058540a050100c04c034941010885505140c0014010040d50010a5860010307081c0001c00e0703035012050260f6050154442e02a644c040d0038506280c6040382d000700607035072611403010414082014480242d4007030b00030013001c600101940040ca9040403840e0b008540020700410010f10040c182c0ea90304056a6044401107028440000000d0850070400301c0a0450b00628980c518400354a42c441042d1074801e0702c0348030310004508001800c0342e05250300f08100000403c0010300e0f4100e11200380d540901c20941c4003000b42101e00100d00c041e0019071100007444e9580e0100d10500c9446081d1b40410076049071840e0210b640d68806010045103503002d01d000391070440106407000d008405948892a41d02d00303d4264190301d0500500741e1a409070700d10400c0b0390600000c2141c0c105114110310036900074008500d13180c038180c0d04403001c01b00106003244a56091208507402d07a526802400c4041848581c03551070b041c030000c0c40b01d40c0c4c0701560081c0d170050003510303982255403008000c4d6643d4627024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 862046753 1250 862045503 862045529
    0x61203160302010209040f1505040203070207030b0603010603060c09031704050d061802030607120b150f1305060307120b09060a0501181206060305120708160305130305030c010b0a0f 80
    0x1529081c0e0183c000e03221035503881b03030a14000c4400100c917503001e840184555450801c00030741d110240000c9220070f87d040c0c401a001079070140003140706819010380011016000141031652030b1280340803074052550b00c2c0b000070780c401810400c2c401200554030b401e01c0080074041c030305131805001612400f40480010405601c1d04040d04680c44000280521641c002e4156180b502d0714420050102c3c0e010322a00d0541c515007540000b41e4204a900480104044401203107040409040b110003900f000e8210b07c2102400300000c034030740e20307010055402111075448085d894429140c0e5a41030360b0001c0c607040c0c00b403c1b02104000346659402090002c6071420300300040081580d6441c1525207410390803451174040c0381c034502010066030340d10440813640501d0654201090f010319554440c81514000b408002d0103120181c4403d42ca591203d8105100e418414507002003444110441c03034140d070040c0c079582c00129450f8071402080c01804a01b1030304403000303e80103051445280c1c21264a0050340440400303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 862048003 1250 862046753 862046797
    0x90e0705130510050d21121d031e0f0a030f05070c0b010302060a201b090f01030b1806040303060812040b0301090f180b01050f09010b070209041e0515061203 69
    0x481001c00b05c03d4030307040c40038031b02c0044c0030750302905061403801d000750341905d407250f070020b5910419000e408035031a10014616050000d24012161000c4141101c142c040401c100a4000b814400074065191aa140071075016005000f54003102c2004008400344010b4600f1500007403080c09125041d664105c84264513400042421280e0300c0203003040d40080c02554440c0d010382e150004100041c00c600038a6084070081200074001020003d85156101014040043c40010500000e86522801c14285001e2090070f000d28645003e005480590100c0da0300d480910500c10709000c03203103581d00c040c400185032500c2c00c0c0540c01e0310310051103030704603459990203020124070b1140c10001900000c3d0b0a00b082084441c100003032202c1083c82070314490900070306a505a818040c0220b8129408440c450382000b00c0b030f40070300c440000014001c403a640d031008941090600c2c280c2040035080d000c1c0e001002500c1b203d880e00f040e40c42000d0001413040491090200400c14004201c07000702e00d4441e00f1001c5100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 862049253 1250 862048003 862048013
    0x50c0703030f060503241006022e2d0605101d03030c0304060f021605120a0215090306360c0901091a040c020606041104090e0705130510050d 62
    0x545504041c1e45402a0b40710550145440600800a6010001106c2e0282c03114a140603035806188940c6000d6000800d81750705241e1104022000342900c0840945014094128101103c03208080420070701e01c80c00180c007218074008003100120802d0041040014104400180ca03240f00d542c1c0001004554220f0340b9a10705150085220f8860217011291542c070061112501c0340c105010f110002012400c0c92080588005000d11401c240c0d4900c01c003105003031000b0320502030001c0c41007034110b118110104006846004110300b2030310b0441c00860b01c44e0880810142801d40140000b0f001d4100320b086e03800501810010400310750a48a0324a02c03c4d000600164102400d043d18503500a054400006002c03003260450541d4140300c420041520341c034a4200030403640b5482410005033701c560b000078598140359111078140700d0190051414107036101d0018054402c5417581c03c03501d80102504100a080c1144054480480075a003403266140c01c500d000d84443c1c0703510450f40305203010011581401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 862050359 1106 862049253 862049261
    0x60b030126070e131a07110106050a0f09200a0801030b010509040b070e010c060213050436020d050f0c030706050f1803010212011512050c0703030f 65
    0x10301c40c206021414984203804071796410360714290300718902902c1441403181c1c0071a0340b5030704000c2450344018292103290f480302c3d004240c584000c0c051254071244a07015200040e10005003040f58980c0a0045108130b51004540071000400d10f2082d40d000c01e545040c0c0740102038204103660fa41d014814040e4080394080c0900d03810001180f00148140d0b000030034001c05150801110328284c5402c402c0364408020801c01409040040180307041030701800440341c0000f0300303078540800821148003006140c03000301042d001c20700741404119540d40d2440e0482c142c0110440740410302454400c0c0d40d841c220480c05103e4840d280380044d2640c4600115050500d40e19119030511900003c007101201010800c4c5034955000d101c10030210628400c4a40244039840403da18030184810203001a4281d03003418010070305140410006910401c1100c807a550f0510f0001600c101b8801020010 = true := by decide +kernel

theorem cover : BRFrame.Cov 861870503 862050359 := by
  have h0 := BRFrame.cov_init 861870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 861870503 ≤ n) (h2 : n < 862050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
