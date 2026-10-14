-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2412
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:38:50.707481+00:00
-- url     : https://prove2.me/submissions/7db5d4ab-1749-4a08-a4a1-2b5abd8a3be3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 433633093 ≤ n < 433812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 433634343 1250 433633093 433633117
    0xf0115062a080c0d0c050d0801050612090c09190501050a180b0409060c05070c0501020a08041e090204081006090203091507030f02070b060108090607050a0e0f0d06050414060402060f 80
    0x58083c06800d00c02205030035001c1d1207012100da554148181011852100d0360308204060b030044c030442e503d94055840010074040d8003449551224a55803a0440030340c4915030140c02c16041000490820004c0940d88140260500150b613035002031040c512214001c0c00c034004811226403d145240c0c0e0302c51074031030400400100d902180e41c1ca0b44070480b40440c0c007203000604000303624030a100e240c0341008000c08083c401400b8882c2c0a0b1a102401e01aa0203209400d01541c4c04110031000c101818201030906480e04650b41c9903110141340d13480d03c003601c03000201c07420f040c1c00007040e04051003a64170070f040140c00380c5001c0c13403400c1c500e00d0442c00041140080c559940200c000c0102d103031005e040c07003512410b0390304001c1c00d080001400c85070000f031100f0410307488201044441a4024265080e0011605040c00c880c12000002611302c620500310580140c00c0d0600802404100d13041180564084c40d40c1c001c1031002030601030703118402224060b400580820502d407403860b0080c01040700c04600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 433635593 1250 433634343 433634347
    0x1030605040501030c0509010e0f040605130b0109290604122f01120506130b24090906012c0d0501090f030201240510110f0115062a08 59
    0xe400000e0450300c00380c000ba9511440030400b4015810020741d07650142100c520360440918040252a4401100400080c5a0340d1160046101008103240314440c05030b03c80b00100d505c1d030310ba182e40002045546554220010394001c80300b0700b800b01411080958030040d004a18080c1016050f882d1400c0301344044410010040c103604070f0131420000e200101c0f03041c00745045100d0510000505100120380c82041c02450310f001c2c042150f07030310000d444107242651000714101c500c08000032181c0c9410340d0001001619080d00d00300c5417030500001e00006404a0b640309281d01c500004450b0350800c900c0440b06144000840c41c15044410088403032101b000b4255103459501e6070f03506080d1201200101c039440f0045018408250f028003880785c2c1034803260109130fa94044005182d1014009125840c01081c000d003022010f5403280c0c0341044180b2490003103c00c10040003042900030007c00000000f11100f414020901d11300c5031079502d540c0d40c5901100b180144910b00c6030b11444008041c100c48003101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 433636843 1250 433635593 433635599
    0x8060a2a0206100f051804052113060305190f0f0207050601080f16210c0303020c01021509280209041b150503011e0e0108010f0b09061f03020d110406170c09010c02010306 75
    0x5103200c1c0c03070030603600680c20607101c01052b50100300105c5e0a4004106140c1071030b00f00b0080c5548920207102c1282c015001160a07044080c40d030004000c0012070040c028000100c2c0402d01c1000142103040780d1415045881d000070018070b0ba520b56001034100d541c951414201003201c1c0c1645501d88501081d100124101c030480341e5140141d8040640c01100580c100e000711200940e014440c5c08030043c0702c190000e50a18041d4401512034601d00d89521104407445070300c00400c081400c164a61503800791641000d400d090800c043c0b0900101d21a01c0f0600c42e1800106008456403074140381d03148103440300c0c1c1c01c5900300342100c0080e0504078440c000c0c15102c8100028802e4a941100f802400641e0000039220b588500c542d05491105460720f001f503040e002404043c1e283c0070781c180321094090303915001c0c4031000e070000c80107031107101c0c0c0d0b402016040644a01c0c40c41c00140c001d00407514191100c440c2c02000925498942c4012240c0e000aa401480401c02d50350040759109647c501c14540000c040761 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 433638093 1250 433636843 433636873
    0x603010f08060603033c13060e091b0f130e012d050108060607060c090503010b010302280504030b0a0c120b03060615120118060b0408060a2a0206100f05180405 70
    0x10011040241f038003107000801101c1e80001c11480008401e8411800764581142407030f0031581400302486404500080381c07409290510306840300e21f40104010f84041da618481620030394000c0c045d4008080350503c0343c00e0003d00b0000b0508801c4240000e05020b90b01d80401501c5200c0020a0b054000c0c00400600c40080e146204404650300241c960401e6a41050f045c1401c54100c00c45242c11316104201c410150503900501001d222010030310200c051201c038408460300c0c080c0c0e90000308900c140005106944c01b294011150b81041c3e41c0d40d5501480d14120060700303440d0684140c68150b040407020031503a061601258010740c8000c100346180140c1200e501158080c01d03800300d8031106101c100748002c2841400742d007008103c0390350940e003018101160252602006481568515619401d00e00b104581a8603060902010404e06014010007200071b51a0902141da6900c0c140500c08085503140a0f8040780013564400b411000007114180c8103d035400001034415540c0c1c0c800d0002100c8000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 433639343 1250 433638093 433638097
    0xa05030303131112060109020307020309031b0102060609060612070e060c01060302132007051609090605010b0f0406030b060904051603061d0a0f0b0603010f08060603033c 75
    0xd01c04180b5510402d000d41401c86800c0c0382da24405101d4114440a0540d0050014440717040d07901c5100d0050390307522075210903480d520499a545815008104804a8483c198003112443c0e5000381c00303a500c9a0380b0309042102c8004110352003a44054107120500c0c02d00080280d041d0b0045c643d0034080c401c140d0a50014605400c041c1d80d004070303a9100d0205008505003850341620003801e90380203000d4000100c584051074880f2040c44840040040341a0301401010007400089030b40070403140118584418041010307207600903060f290f40f800d0000004040c00c80d030044440c5107040c40500d50629080c010102c01505a10303100990044051104440720ba8452144a000e65103181d0044102840301d031000d0240d640560000c00390f41001c1030500f201d919a01c1f045540215000310004500d8541400c090003000c0400c2c480f6004840440003003103618845180700141c0322010100c40055840d1410141c0e01d21071a603040b02420000c0400c0e00940ca107520b5844041c0d9205488401c190b8003002844901e5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 433640593 1250 433639343 433639351
    0x621030f03061a0408010f1104150905040c0806030105070905012f061314060405070b0c031e0405010207090912140f03090307030305010504050f0415021b1015030f0f020a05030303 79
    0x40f400004e01008080c20034411800c1300b1b9468a403d2114040c2c40409080c140158828250420900710803805124811100c0002030310300104200042040f80c1402071030b6603000c486040c082d61820303001c100300c580625a114200d0700141e60394030245100c610480d404440c59140d924240c0030b44143c50541e1700052003141c0c400e191002c2600a08050303410a42440040b680e20300300c454001e0700074070001c82c8020030754070f00703544100d02c6071a658480413030366a2a40c03080442c000650075015544005404415005004440003682210107254071041194102d420b400ca00402c0c0000f841001020340e4060700145101d9140c0e040d006d030519030481400b03c0341354400c580c000401e810003d0306c0402c054151240d10b01500d0181c50070051840c0242d1400e0380c0d080c02400c05000d001c5000c4880700c6145041d01100d0400c4580c0300700d01c202e8a040000e190396459100e04a009582c00d03c80468440c0a060b00010112030b000300c00040b034807049031a20200300e1549403091f82c0044107908c02040310b4034108021405 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 433641843 1250 433640593 433640639
    0x409020d0501120b040314070203031201080d02030406090504051f0f180e030d0b0f3003091e0a0b04062c0f010e0307080604150621030f0306 62
    0x2039011034440003821104141c00c0700c40742d041d0420070741c0041807600504a41c07042c2d01d070a000c01b1010704019001424080d1000082d4540301c00141c58003604030907071300e05040761140821140f0302140346100760380700d001700c0c01400300048544404000c18941a00403d41108011200851b42c40000540c0d07003068015800c64162220401c1040040c0b030301c0e402c00002d5161000908012600d0201d901580b02d20848045500040d00d91341c002136243d40c0c0003005120301d0740003481e00c5100120055449006100ea0956070b810020903420103020302c00c044101e4141791001003000c0000b101c1c071a4541c814072903c0014503001100c01001240e6550130030700400103030a445e1194a440400d812000c0c00f004070104a21500141d841c412a8954030f070551078206061003420b1240300185900c0c00701e45000c000d40d02009061144006001c10300c810140c5081e00418102414061f045c1c03030f030f40c1501c030003d070f030802c4102d88089031040302c400f00348030b41a5040e55107094500880c0141d50340903803c40c0d01e0140200e00c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 433643093 1250 433641843 433641847
    0x90f06120106051b0c060d05060f04020a02071a070b061203070506070c11041e0b030102090307030b0601080a0c02100e2e0e0624120f010b0414040210050c0111040902 73
    0x402c01351448000da074004060001411001c01510220b0f005014144200050ba80c0b95070201c2c5140d80c96482c04205174a006e002152038003190840250b07210514401d0a607030701814402064070340344000407541141e80001449072380740c9446040c000d9501d500404070301c0e0350009214180000e1814428a401181c055603035075040c004504081a5890f040415280304a1801005c0b8034502ea60384400b44051000a5000038010278400c0400d0191141d04a2140d01d07016220300807080005c080d00080c09a10280d0f565506591461101030445818140032030150b4032040c03540e03040c0402e86d0000d00042400009454400c0e101780c41d0019851210050603c40b20001c10402d003840d110f501c10813040701ca01c0c5005190900701050103400d0a100d0043c4a04008540c0e902060141c4528101d0305030f04c10060202d5003200f0300e2045050081004c800710900c078a040001c3c03a0440201001440d0040350010504120314080c940160703407075845120003003a203540361030f1030700400030040c006000284950340003d6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 433644343 1250 433643093 433643107
    0x30114010203130303030618021306080709030c09320c090d0501051e0c04120f0314070606090f020a121d0316140a080d0903020127020a06050f090f0612010605 70
    0xd03c203004031a23098456103106000315911946100310302e00c203d5440307081c01a1300703443c0c1c030200b02c07000c440c2604080c1086064103400104690940d205103030090314004024684507000c120351340b0304054561990101e002c0e00021a00551106009002c402c0b03004060a018803103d03a40c40382500d0046800101c00301c1044001004500300710803080c1c2c000c41d0411601d00d05414280b45080c41512410040c0404002459044c100350080d00020407070074544441c69129500c624010026201b24001c40c42400c0c2864040e0780d00038082d0080c0c41c085105038854030381410110942c04002c105100c0031001d200c0d080d641d9074000c000300744004c10b030450300000c80304400d0145043c607400c801078005035503680380d102c0e61801000c5900042580d110000d1003202158090450800301e002d0005855800b07040000700141650300d01c0c541c1e64040c405442a90010811136589005889600400c0c6075451900380806c0b0315182440e03c1d00ba010740e420b0008144074201419681054101c2c90249c000c00e0103d00c4c0041c2c21 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 433645593 1250 433644343 433644359
    0xc110a1a1b0723030a0803090718060f12110604090f1506053007030605030f0111030109020c10090309051504030804060813052a010309080301140102031303030306 72
    0x4661500c03070140003440003d00e000f6075814110608086a42c0d10a0f460822100c1030303a09004400301a504a50815243c1c24000e401c40c3e00ca501d50b1080c283d00700c20081c4604090902400b5040481e040c01003000d0500d403a040a5000d448540c00040359440c0e202d000d42ca24a564420281c07001e00000900042c50341100039950f42100c130354807010550000004030030030205034007408a0703142c14602c00350a40c03401a0040154105100a00c003804150076003000c000e28264581d01c64001c845080701294a450700e80810282201d88600244040440c20401800303202410b0700284100b48141040b01c114110008600c81240d4182c40e00710009a80c14004000502c0c0803148d0403050003404d00043e16113841c5a980e240c2c144614824141805407d500141d01c00103a000c0001e02d490b080b90956402030110600e250710b41c000020f441d205054480038030445944207224440c012948100224a5030b42081240150258000e000034110310003080341c01206403107140408001d42c86a100414030b103040540c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 433646843 1250 433645593 433645627
    0x10902030714030405030f07080712020a170307020a1403070215030109111c33030b100b0f03060d1505010f051008041205130b090306090d0c110a1a 65
    0x58502c02800b4001c0c0000718201004543c2e616800b0508269107031081e1074000254001c802c00a400b080387d840d100340b44a070700810044001c2c3e226515158510809400032403c81c00203440004c0161b00006495001590f80002c440950400c04201ca041813200e500003503510030288000c401032032011004100158140c011001c4940303880030b5442c00c002600803d034002c40c2e0f069902d5540070f0340301c0c0c00811a565010180184001c14201c5015421a10348004c19036065144800c0340d11a44400c0091030308407040e90749400f500d030151086407030203010050000480d0006840d46134031900300d24040700094441c082807071941607449000301e000d40c0744c00e0081c00440980c1c1c0c010717401840480c00710400b60764000e400d5a4050707481203000003103c02c50351044071140a1074801c441000c64000c0c000c119240e9100c05010000c070110105e640c07607661000300b07548521545e042c1e040414500280e0078001038080b4411511014041e080201966480105102e4020300c1b90a00c0a01c240004440d81282d481ca50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 433648093 1250 433646843 433646867
    0x5070507050102060402090a020708070212010e06011e0512010204090516020f0a020f0d030903060509250e0127090b01150c050606040207060207120e270c030a0e060109020307 77
    0x90113592030260041038002900404070f0300f50703076400035140007003200130800c0d100903a8020f40b4004d103651003030070114020204861000b480303200d04000010340300346440b0010704003c8036030701c1d074002585048103000b5000b061008804865400f4080030680c10769a11995120307114402d941001307422240307406801c100e102d50840755107820507941540075803100c2507001c2d1280c000fa146000d110105043c1128242429000100a01e0400c01448030381c550000c1e00c2c14052f0b0348034040903000100b4000e050101d460b90b00c110300e028052000104075181e4106c1c0078040301050502d81d40e401c41400d24200c02100d9907104200d40c1c83c00c84900511070320001700316100355103203d410103006c000442c1e290190341c0c8500800c01841183c00183c0d9004000181d01561652a800b40c0001d0b0a18000c240280c08100b1250700180650707800e562a80b102030410410014541c907110f400002c0745c0741c2c0c45010038568401050b03a00c090b5107034510b801c80ca000420400f40205405400140c69081c594002010020194 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 433649343 1250 433648093 433648097
    0x2c0d0f11240c03090c0f1305010f17030304050606060717190311090a2102060c01020a02010506093c07080114010c02010203121b0705010507031820040615050705070501 74
    0x100c20480301c0c0400041441c07044004a44051140c5000341c001180c60107640b4a003001f05007031000000714907003e8003010b01510381459000000ba03141c512526907900046401600a60002001c1130150030041c00801000d8041e860701c1c10040040c05d11814070303a1007000c42201102403403451407441541032140c410561998115585000b90340380c00039950f580c02d07010740e403624142410308591000340c0c0c1780d1003840b0b2079020300070a07103d840c1e9040c424000c0d0004103030140554207143c0080ca25251441d4010f21030761614842e00d186641899400c0300c06a4100004030115221080c1d0b003444016800a01e44500203540d1703005c07060741c18201146403009106410a0522a1448040700140e80100a42e42d401d4a0091043c009035139448030300384182e001c504280400315001070710005012064100e2845008161024000c62100d1080001c45210341c0401815401484004000003180a0020b40c080107008102050064072020710b421042603020098001c0b482c00180f002c1040410320164005200034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 433650593 1250 433649343 433649347
    0xf0305030d18080910030e010908090f0a030305031b2109010b09060315060a0b1606050739060f09140303100e13050706032c0d0f11240c 60
    0x1d41c1c0d000044d00504660038483c001c403d5074440700710310980c0047c8000c82c01000a00012191741000002d540c84411000e024030300c0c1015844403401c08481c02c108403903041e90b4581c6103a40d14104070310040d42e40b006075144140c040041c50b00840482c4004071810102609811903818000505400c480080c071a0364002c2e42a603040261035940450001031260800c10441010b40c1d40314001200d2441030307084012090b80104412000002000d1f00c003542d00d105a60400103600c2c0d25105030350780300c0701035481100070a038103074040380300040140c800c24407091000410303d401c1aa0794900c81a10b650340c12414107640e85419490501071504240c0c0412000385000e0762541c00c0c0920809103402441c041c0400c00c59111300811580c60848504040d40f6400c03030300741d43c8150386522000b009041800045080351607403101da0711052001c64900d417a40d20b842402044410000701094030500c000d240c82c101032124440e1300411050702403000c9410b4040c000e1031007481001d181248690404003410b0901402d000b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 433651843 1250 433650593 433650641
    0xb120106030b07050d0e03130807060c0f030c0303020702090414100b0a06030b1302120109050a0c0207210209010909120503130f08070501020c0f0d050703090b03100f0305030d 77
    0x40c0b402c190000c09900e0302e19a680c04100001d0064911482010042c0c880050504200b0302100b0031002030b40d02c0d22054640207a900d00003210000060341d4087c2c0b080707040ba0722000020340606180700c3c01030701c203090150910141d81c0000c0c4a24004035001d1707685121901105242d044207111400c103c2d500d1130b404101d80b80c0240089007400782c050081900741039513181c55003d039a6603411190900040c01000750b548054821003400c80030000e211b8064024240404541ca600681c080c00120200c44d40c020100b4904d00364894000d041160f080e801c950211004420140c1c8030520058081c00c6001404a9200101e00d8071640d2660707541005420000240240000c0c1e6034103c1c9100392141d00002c40000c2e9150b5130074109024452400028145e40c40041e051040c1c007400702d20070305080c2801050341e5803887c1d8110301703488a00c40c5680003400070301541b00600104402d02c0166400200080818109903101d01e03c5004180d11900252420380c00030402d017007600024010701000c8400721100c0e82d00c1c051 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 433653093 1250 433651843 433651853
    0x20706090816030f031403040807030e0913030815040207060504111801030f05011104170c04021c021b0a201e01260c0705060f011a130302040f0b12010603 68
    0x143c3c0001064059802c07062018544039240c48100f4003008103045a40b402d1514054000780d000f41070890202d600020005014944103041501c54140d640c0c0c09401c90101b59421034103548000c099503588030180061498907282ca10180c50f5552166000080508060400300b26600ca40446944540c032005802c8040b590310781c119a0450743d00c44103006030a40e0501c3c15601403c1d5801440e000d00f00c0200f2300255140088520404034500e0388291024081d03203500340401c1e44a05800e030841c5a4100c00e155000c802e695004002e010310708101c0c000910004140380341013400c1454265298038040340b8032021005e0225074204042d8048691000910480807031203540314040c00e00038144000442500702000454424179a0800384103205180c80c0b50050345480c06411006050b10b803807207988001402413065241240c1603c44180404011503081503240d1855440011303034030402ca00c0c0c41000030051326140101c0300350710500400842e03800026008c0c1b20920340f602d80d04020580c1400400c1020903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 433654343 1250 433653093 433653133
    0x70b0d1104062a0209100312030e0c150d0e070e0a0e06060d0809040c030501060e01080f0112140f01051801051006030e01021b100e0d020706050a030b060a0207060908 73
    0x791440404403c400c1c2e4560034818184444003029400075401c90030807500d903810700307452003e0300d200f10201c000311181c1d000304900302e0f015910b0080f80d03944140c4041400d4a071031091030304c0100e5403d0a2524009040036600261490380c41110121380c4078800a004a001082d034069100309020307020001b0281d540480ca50b2000042c00d0b207402040030009800501040104440404001510034030502d80c01d050028001c0a091040d800010012800d1030b549610488a07503000f208500448038450b42001a8210749a0820348100c448810582d030030149603100780440083c0031f103c0300002501d0f20b026501b807080c60000240040721649804104100f030948401508255070b00382c03400060103c040150a402441102c03400740d924000c803110846489800100440c440003400800e02110800f02c84046d85c40c520740b6903e0000d070b000391000303002040c070400241000045034a00421410308040100300766a0281020800680106009120741904850088010302041c0d0003010301d2410031210341b4060f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 433655593 1250 433654343 433654367
    0xb010e030a0503120a090f030e01031a0a03110418050a0302240a0c050d06030b0a11030415150f14011106070f05090a0806010605071101080601080402090402040905070b0d110406 78
    0x2210702001248040240750712840401f50b00c0700a180188100703080191101504404031400a414049020041800084810100c941c0135142400746801c4d80e03104400414003410a52f08070356160070404030a51414860880c00740240094200000d113400c0090420b80c1b20301c02d0600d628182558603010741c6568280ea54440d04560001801c12007000d01281d580c451044211540c40c1814004006d02100d9502507014580c10401040803000001601ca0640400c403805010008014407400d4a91155003003e0011854a610314140c6034444d030342c80b80006144d130822041005005041070440d44c10880c2c1000002e0542c00030040c1307207060800245054580e101701000c202001c2903252142e140c0c0c1507200042c060315001ea031801c0d0386030b00c001001d54000302c40541d000d030b508154003046540201c5801c3d000b40f00c181d445c0e044995550f0244405041c0143c812600207130b036131008001084061050101818001e041c01c0c0d51351910000c41c40a88215012030440c5000c10041080401d420511780320344 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 433656843 1250 433655593 433655617
    0x21909050609104a122107081204030305070206090c0d020109151e05130b030612100e0705090c03042a0303030c03050a020a090b0c0309040e010b010e030a0503 70
    0x2642908113400031900020420214422102e00c4c60144c0c410300055080c07285071048040d0b51000ca004c001e40c00080400a0f0801d4020300b070b103c0304134a500742d05c5000c403038002c15400f4601505070341e903044035510441d407103008481c2040c00d0004059141c01000e40102880c4000d1a4500341096201d858462400e51944140c0d215148042164081c0c4000030081c42014008401907000e100e002d45006d0350311020013950100103000c56020381c0901c0039640185004960340c00058141f00046800d0782c80130b00344960021500c452040c0000c400c001c01c8030f44807051100803424401c2d03c0700302e0340751001d540c115032720440c2240d017080403450122080d6640310b50444c1c41c0008481400360200c0b105104035011112000500c0c00201c01d260b01500b1640050303096076401c20142e036030600414224003c0c1484040018041c800400c9203820b054040c2225a07990000c2d20b2402040400082c203c801d030900226850b5100c03990f60450b90380106000712142019009040e5808042e42c41303685034132540900c419 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 433658093 1250 433656843 433656857
    0x1f09022b08031008070e010605030703022a070609050303040e0415021b06100905060105180307080d091a04050d030c060603120518120c041e02190905060910 69
    0x5198100540d0003025a60804821a924104400c0201a45140f4001c003001842070a20000c0c041ca440001c150480e000e641c2c800e4115190800210040e500c064901400241c400c800001308081c007081040002080b0001030800071b1034900042c051440030743c00280710382c000b840b04207d254881d01580e03510690041202c04000c0000090b40000c5c060080b140410015005125840031000070b03000e8002e0307003d540b108451998803241c0e01c050740c40c1101c025000400500c0900f83d201b000c00c1180200e460000c050312a160703110421945401c262810769400581d05031010481c1070b07440c10352940080300c18242c440c909420400815910040c0f58401010008280d09100a00881d5440780c4041d581c010881c51000b6950640204641c004420624082000081154040c50121090360030700b252007002d030001004003402c1200906c40030101d100d82c9004101e089650f10b05620040130451441c040c0d03c10444008107005204040e03d030000e90080400704580441907480303944242c1c503c2c40c9458061 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 433659343 1250 433658093 433658149
    0x5160615031b090f0b0f0d02040f0f090c080a0b0606030901020d09061a18070c05150a0e070b07110d030203162105121f080f1f0902 58
    0x4581800c1507800640100d11220003000c40714001d440d80e1080b242a5070303091042c512000d2078201100d014881456102c9400580440c6a00f002e17048904030900040c000561440c0c400200c0043d55030020b101d02569583c0c0ba002410459640c030414060701c801c4008052120341513a41420000c4081c004c1882205c001c000a2013142d0250101d4201c100110b5060001d0700c000d19000011b4840c2800600403a0440c050b0008a07040403503090010009100b500c21682d1900c40c02a1849110b0384c20a07201340c01030b400140c40403040795840c6c1c4d0145031011800901e05d4191001325041c500c082d00100c0d19150100300a50101e9495140800c00031400c4400c104080e07511b2030f00340c0ca98401d8003850408180510107070300a0015015011a041c208a00240c4656030401800c9609210b281c030312030104070702003012445c2d1180304c00000c803405540114440405450b449558505800b51018001d0703640030644a05400c01030f5810706800454401052044402c1c81c0c0c009070f40f4881038100f074598120004000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 433660593 1250 433659343 433659371
    0x1220070f06110d050630070f1706090328050909040b0103020a0501020102040303051204261e181203090406080a0212030f04030303200d0f0507051606 66
    0x854001d0703000c0002c0180c4424200118071940144102c9030616207842c00068007403d080c10b0074100031182a1306441c0015011003058981c40301e07458904024800c44002007200780003645404050075818140300b02202a9180c0c440c07505400900c0d80d1340136040ad02c1041c150301c82c9514a8440d00548164807a050302046030119240d00032100c000303906c0b0540c1000e120034841100031442c162402a40d44507001ca4075400103a090f84204d100c0180091070400c89030034190701440c035454000f0321450103124076000c3c80c514a10015040d909849250200250600580009900c5200316081c540d80031400d004c1905443c55410074800c2c541400703107411040d00c8000c100309004035080150018004c0041c5600e481d80c3c595a0301582008a000311401c0a81c03040c03104000040d034800c1240004120b14060850342d085001d004200c109462100d04030480c0402c3c4095074019200c40c4011040014851a20094079400d90f10050b01004c04c1c00b000b00840c100050740000240849500100041038180201c070403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 433661843 1250 433660593 433660613
    0x309030f0c060f0c03091202070f0b0906090904030216090501050120010f150503010506030a020619020304080307060903081509011e09021308070b0903060105040c030902040e0d122007 81
    0x2220709241c50109249040345d0150301c898500c5005603005407000c0001e0701300340d03580c100b030f4016462240d1102004005810003080100740c614409032840b41420364030380120303003680d8003035500300c1c05a00600c2100c1051800c030014480280402e400601c09945841300180c8407902e01e10910b5000e0b02101c002008003e002d411001030400324080c10001c1c02200c001a26403a400c5000f107500c25400c08000c180603103800100d8402d02c4e0b80007400149400d00b414172000300860103c1c1d9a0b010f6000a000021f1400c10a00160100c140226008921403110389002010448000c0c180b038070310719110a0620300d9844030720748181510401030322503040e44070007908204800010713803207464070500000d00108000c08036200b21003182d000b2000c0b1070a807620303010080101d000340c3c0b45080e0180d11540040101c1d1400c0d410503125900c403401c0015007070303616070085010740c3c0c450980544540e00041818508035803002c1450b10030000d0b4070080088428013021240e1103020304816100094002c900a0144a8103405c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 433663093 1250 433661843 433661861
    0x90b010e0408070221070617060415030515040b13030e060c0a080f07120519081b030a2903030729040303050a060603060b16031404240309030f0c06 65
    0x71440c176100c0c005650000900100c4080c071620f020720800001c400713000308421041000c440c040400b00d90303200c500f84001864281205440b108540c50b00002081c414007060320749504aa4640e4107505d461704011040c0200a054000021440c0074a1070109031f11120000e020641140c456644864400100d1320f0300e500004090202c820004610101c113a00e9001802120f2085406011078902400c2c15a418041e14000c6034141696071805440f0600c244421580300f00c10421414100030983c00b420701c59003085410840c5a0307900e072188072103260b05030443c448090024503402e81000503a8086902c0740180b0b8002092180c4203485c0d020507508417500c0c1c4900300c0e10902045560302d00390800501400055070a03a40c101d1130480e000c602076100703024010a662281000c185003040782c0110600302c000804040c3c040050031080e030380140e00c500000300010002e080b0848101000c40b200828542c1228403038905052402c040c17480000d401c20050340101d250707070805d81c0540e0b205041036005001503003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 433664343 1250 433663093 433663099
    0x5120a021e1002160503061902030c0f04090b040b150412022107170c0607030e121606030b0d171b10140f010e010b0705030d0908030402090a090b010e04080702 70
    0x5084802e0860f40056054001d03c1c076800d8101080d81c0d204c0606444120903114081030b8007503801003a140e4040c2d60001e58001c15200c411030302d801440c00f000c5000d40c005070040784c0300310780b614a040701381d103050f005118152070101d80481e8061911410300d80d0903c101c0c4140e2144454410000c415592074107988130214200c1c00f90f440b00d82e1090211306496072130500440c07a40003d00c801103440c4102c001074043c0780d410082c2c12585080c00d1a01e00755010510740f045550b00c200e43c2ca441000d610000c2c8210015980400750407102c441c00e000700074056414030038081e4014104680400045240100d151069444220043d69500403000b007440706403240310804503d034454500c0160715080035501080f1084030308120340c4981d8a545003c043c0b20202803007465440d100c100014065001d20600809000b40f2401c00c0302d1500e62100001001c3c0c82800d0810790f0411004005c0206504101c0001c2c1d03840854000200041c0c0810394a40c00340000600600e0303d600c002c034002030300704500c840440e104d0507001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 433665593 1250 433664343 433664359
    0x31005010b090a0608070e0105220e09010b010203160609020a03170a0306050303030f07080c09121b0604060c0b1008150105010e10080103080f0f031003060605120a021e 74
    0x705141c840035400030700d51a0152164910000c0c20500c20121a0b001d0021555224143c0f60003d00468094100403001a04c10116100300134007101840c4e064002040c0c0081d0b1060780f0318018000500f107076040a0b00c0e6041d90410411030512107048100e5002507984043c000441010b00e0001c0340c0c606920350001000c44030312a96003c4200014806804100c00581d41400f202c1c0e2590245504d0b8041602c0d1410441e502401140c680c0780154252603000070240c3c00c1900b0428100001450800d81419031110340d0008030441e000704c103e170300840e0000d00050b20010715062404000401e0031406070005003130011410041203109400f040420010880c82c41224410001e0650710101e264080c400c050100700c1130400d118807424a401c2e41f86a0f440c1d43d844070402a841d5455002d00c0c4c0c0d0002d504401c445104020603100509044041d41c01040314102d0301130a9802e5181000480c1c5407a0051841104198521514800000307141c01690341e040d10b110f00d020f4107100e03900b4054079441c01c1d080c0d440505 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 433666843 1250 433665593 433665599
    0x27060e120a0e0906060a05030a050a0b04091a070207060203031501051308030a030b04050118020304050307020a080d02061f0618080322050d02060702010f1b0c1503060f1403100501 79
    0x2c054400748450b5400c0326601c02a8440c4c2003040041c0c07060681c01c001140081c00080c0207039050364441030f88641c1101d004201c618000000404a0300f0101c01202c100c2d8040c0e9009440a80d0340e011154030071000d000902266040c5200a9500d000082200d1050011a48107542a034400c20076110300003c071910b01c202c02c94456200a490307400c03071054100087e140814080307007440d0500a1b24125014020f002400c64996100c900280d1b00003002601c85102c02c019042c010317114002e4000c000c0201501605c0420f420900003030810001a05108100711700c801b001e48084061140e6070704680e0320342402c84124103543d160000442d40383d440304640b0700000c20030310000400e0140044120b402c001a0509a58481040110111340c600f00607402807414440d090055000b1140030070b841946007004103e401d020125040007a0b4a0041191411250a420024442c0032550f105c800e040c00d0400380145410159402c0131160544510185a0b902a03070341c50403a1814412080b0703540700d07285c050082d9a1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 433668093 1250 433666843 433666847
    0x9050604050105011e090b210f040c09091703040b0103020102060a0b0603160216090c0f020f0a0305030615040620010903081909170304031e0e0d02060909090f0127060e120a 76
    0x4488c0703001d07180d10f8100c02d000401800341a05034500c00c03580841c048201508040a49004009110040324400040f442190402e0307a4503014503c20351180004038110760651000900384030b00500b603200c0c1582091031200d01a660001643da00080420b583e2540d0b030000b1a08070303c0c00b50401d4440701d0740300200b900843d205509802032018000c0e46d0702c5a030200b44034090121782d1040b2400f6a040306030003220a100009210748015a0800070040c50710020300c0c0ad0340d0798541e06900a9101d04c011925495a603c014048100c0d0003c40003002e000800c000c01440d24042c1400c0801080e020b01c50300e0f007540a0030800c00700c0c0d00541c0c00340c0d027000400110030240c0e01312951560094600b540480d820f0800416905c00e10121402d0750780080d81c1d20503120b003103001808a440d016500c121383c080401d121813501d6445001003940300720100c0d40180801d03a40300d4003003400c58203802203031a58210001d000009512000300105196a802030000401114080e803075800c000f100c41d02e461080c40e0000341e07042040c2d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 433669343 1250 433668093 433668127
    0x11180906090c0a051503090c1908070609030f0b0603010e1b130c09140112020c0c040b09070203041707080a14070e01060e190305120409050604050105011e090b 70
    0x29070300d041110700c003950110802c03050b0621845080d501c41c0d0809240c4081e8828a030165421071030400480b24090381d4100080da42106141d912241034602c504200300d481e4013040450014882da041600c8540d0468607640e411400361080034104000450116280f51025800441d042d0007103030a9600f0300031556000070201a1030032011f48905101aa00c072074a114078420b5480030135142d100c0d00c01341454580ca45160884e41600d4605208007603400c2007402c801c03400206041c4551401801c4888017100400007140c1214042c503000344002c0c02042104e60700002202d05032038240c1b054100601300d01c0e40c410314000d02500b100e02c031401a841031100704200420185207803911041920304042d1580055841c541e424460140082d41c0e07405041d902d820048196000c1c8060308070302d1822a41c0302c2e1103242c0307400c038002a452803c1c0340000d001c0041c000d95202d120703088001107600303001c42d500d032500082c00751070240848840d048011008a0185025103515001000f40887c0c842d1030f503820b424015151 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 433670593 1250 433669343 433669351
    0xb04020f040216032c01081302040c092126040b07050a031103070c0b0a121401050102010b0a0302060306010e1f18050102010c0c081b010207050a1103160311180906 72
    0x46481c4c6440005e8402240440304545610300f035000345140e40000c011030704140054010081480817009501c0036850318003403000040c410751580c040840c03528503c008c44410504110340b501c801c40176000001a031610003007019a402246110855a102103000300a100355072080346683c600041c03203000c10038040b440b400e906000e61210084207114550540d02d0307115101006001110b910024044001000080c0c40904840c5c034250103022413030107581e022208861000003070b500d49000100450769090241c40e50810007910000303046861035001c03603600e00014020a041c07000290000100361500e029410301842d20010454050500100140140f10002c01301072108000a002180c154014002d1102c01e8280c0d6542c88d20071350a54a448081d038201e100e103d9800d110f4680e40382e00d410b01c240042c210903401a0003a00380e0903800d10309880c004640d0821140a80c1107002c004500070b48407034214045030f4000800d506603000783c20004001341d40b001e07001e5010215890030303c50070542c0011f00a01c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 433671843 1250 433670593 433670597
    0x2070f02090c0c060703091a07020106080708030a080105090c21190605060702040e1e0c0301150501020d030e07051305060405060306220c050a1716030c030b04020f04021603 76
    0x1a42c940c2c06608500d8401e4000e0680c150303000c100820322030342c400da010341d68840c0074520781111030803000651059000e064038180c0060303444103824080414140011801001c4000055141003250f2402800710318051251074860182500010301001c85503048a904840e1002000007410503d10540794128050b140f02c0106884c1d280c21564290700340c841e4030242c07007000b020241040c0b0b45600308030190030303640802e01c224061081002000610003441c80f0142200c64082c02c1505030381c009150031191031001d800d00b4002c0003002001566000300c1c018100b03040c0c524010908440c40d0318200c0c545552903001d15007240f000700c250031305520107034040342c00380008a8051010f0380301c0c0c008056803130300242d410840805101e181400c01d21031032141c00010a2050341d03114081940c410004034046215401341c000c202491b20000680c1006011100f1808969400903d007507080d49c0310b4204507642c03400018403801c5860041800d55590600e50240c1c003d0051055542d00850750f200807541e41d03140e1040740 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 433673093 1250 433671843 433671859
    0x6020313120c050409140d020a051501050109030318081002030712050106051b011103130506010f14062a0304080106060801030b1f030819111c050a021002070f02 71
    0x603640d22020001c1d80c00c181c010501c186001d0400d801c10000b0548400225a061082900d0b074000d454103009400d640d1701182c0140071401d1031400e0407420b14401085040d441c840030341c01400241e802282e0003041ea509850840c41e0701c03803c03000290040c0070a4121100611907500e168a03082612340081d8032820f041e9690750030500c2c1c070031030040039100207028101c007188017842282e904200c02c06084140c90350b9080003050510070700d0b03604c84144c1c2c41034464174004113044494009020041050500402d89981c0180c040c83c030740410704031041c445041e11b500c91071000130032303041d0603146814800b081000041d01509000362140101d030380c0e5006100e036041c41c0d424410005840c40c002c014850403039400c08001940c3d0350319410f1140d8480c0c41c01d06440e050119590001c03000c01c00e180058016801c0c0319a00c010300c82c401a10181c000d00c0c83c041c4540841e88a4810b100301e1680c0c140a0400d02c07038041c245107450f4803403210300740d090901103050b00605a201254003428031840500d0184520700a03500300c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 433674343 1250 433673093 433673099
    0x5071505010302181e07030b0a152a02060703032904151208070c1a03010e1b12061c030503011d01030512180406151e0903060b13050106020313 63
    0x5001035030841e0030b100040c101781861300184050000c00e9078024003e10300002d88400450000e00c16804c90341040c1c180102c140003a600c0c1e16006460344291001070700c9003641d10711000700c048100582c0200001e010f01c2d8042a40f1041500075008031581d4446c0d0142c11040211101c2c0500c0203403580c558261080e030410010400000080c090241501d410111420004181d501e03a03482990180808449400030024000b8981c1500c1c90800014001410a0340c2d69500d0031004203000000a001818400400000701000d41c2004003203035840e036400200901240c2d610000580c142c05003030751115007400c00b0f03603c080415a000d80154181c41c0d4203901c0509030b18042d6a04411001c1c05d00009055911106001c050600c0210207029000701c04054880061a24004601517406581c401145132400c00e036030452a90700040b5400502212068040c0241d0b005000200250f90074803025101039078800c0d01400c50b49400754461502c14900c0028056543d4905000b5036039070150001c81d5001030141408 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 433675593 1250 433674343 433674379
    0x2007030c0b070e010e0906060706062c0f0103060e010f020f1b0f060f0a020d09030e0f151806071b05030d0203040b0a051602031f06060302070804030f0305071505010302 74
    0x3503c1d1000603990450740500035010700c406c014029007187d0f4400c0003400030b84c000a81da4040c82c0042c10740b140c281c68584007405c841120001d800212032400f00a480d00308091a4000030b89281140c1d080080030a80c040740401050040000780300c105125030002a40f0350490035030303c0c01001c49400385080c00c1c611001030b000240c3c0310364000010520941181022400003a091000c807034004000d0600149020f0050b00d241007180c10015088002c1541c4c291119001e00d031402c0300408010041c1c4450340c402044a4240e1110700c10030140c2002c0c802d01b181200703100c4c0c40320026901d5559202070119082d5001e0607801c1c19a404502c181c91203072060840e4401c0c594404800d4034100c031110384100d420040b02200c142c407283c01000e01300d220b00402d07100d0000980d6040000a2044911014801002d00720000c0d0105998403900300703d041c140108161030005074220700300c40440c3e400a100104007096441c0c115901e2047c0c601c060404000e0b010102c4000f1a10760041e4101d0f4402c403256102e1010044032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 433676843 1250 433675593 433675607
    0x115051203040302010807023415020604080c07081207060617060a0b0114071a0109060515030406060e01030b091b0303030a0b011e020106080f070510032007030c0b07 73
    0x1240300c15081444100010b5002d0010145c0280701401a82c268448007c0b402d115030100911000391103504420400d4010507400140c1c01900c01c1c00001c0c1103036415420081c2d500c25001e04001e0101c18002503440d4002c8040c45441c0140c01c070401070b500c280d81c117001c4803d0180c10164081c0c410b00d10700000010070400f1000000c00c074035490701c0600741c540d46181e2402d0003440c1100103181406420f926150b401e0804000030318082e80728061044031800f170b54400010822058004246941c5000014801d07580c07945201d64035401007140c410394075507851409101902d0350340d015046001c40342c1c001004202c3e030911058032844001c4112020203081c6e41d40f07190b403142c54108050701600304001040364005c0c2504404441d030310604040d0017095115080c012200d24400d01e41c00140d40d100028010301400340b0070002007400140040c00d00505081c0011038032101e43d034030700c1c0a0503510010000c5890b010b8070303c5c28001207040c100d40c0d19200c4030300340640381f2807a03030000f20f46040807040010041ca00400c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 433678093 1250 433676843 433676869
    0x1d0301050f0109180204020d0504030f0801060c0212010615020d02190309050f01020a021509031b01090e0a0b060a09150c080d1e0921051e07061508011505 68
    0x40380d280d103a40780c50b01803402001c012031820303182c146204c402005030315540010320441420410000d454035007821b006050490302d41002e804c0000e00001004800d90010f40800d103603030100e506603500c00b0500c403041e005202c1c5c0e6001380e0052083c002901000f0780c0104102d2903d1a964089d81c1e4105501005038405a1401d40c0080c082020046c3c10b0059040c011000c2516440c18012105178200da0740000301900c0c80140c1141818100086841c0c003400c062280004224038100c00800002c1a140060080089401a941590780340c500140030300e0b0490b00035072401c01001d8801c03a80d540701c2500c01410882c20f070144a49007000c3c04030241841d48a42107903031569030082165824141000708600103800404503241640b508030f0080482e202481c070401d0f09041c482c034107101e600000804e4650784210030b1400700c02070103018050600d0007030090150003140420302079820750b40c034003610303000e001440114010fa0b03001c0b00401000c118401d05512001425070701c1c02804c40d5a640c0c80d030401c01700b018440e07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 433679343 1250 433678093 433678111
    0x17070504150c061410060201061a03100f03050d03061509060e0105041d070915020a0201030506060c0105040507090605031f0f14070302070b060f09040f06060b04061d030105 76
    0x11042100d80419100741c0750710041ea29001c070720240c060715a00700359440185001d06000303102003805426800042850f005004030b000921001e460048a4100c4031040b0743c00304488000040054080008900200003503c480081224659241d007007050707641c004541c07a00301003840c000010035444604400b60300b42642c240c1e983e8425a041c10000c85102400da01c0e1141800410b00000c11440801d2082e204001920703001e0014a2608032002004110307035500482e003003103c000c0d000d00c5185c0e010a0b00d100c0a41c0a00b0081141d071140004240e280c032030380300c41c802e06510305020300081181c0801c0c00012555242010b0003495128010188c0351400c40602a120140f0399505d80600034242e00401d0483d25800030018011412005441a0402c00c542400009a00041d644200580c441d00260071010a850004031a141c09000ca000f50b68050405402d40c2d40d00740302a420080590000d1001d403651000b0b803921f86640d01e0014000320f15206551062920032480da00f940e00701482441c0c8a10744034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 433680593 1250 433679343 433679347
    0x211a030d050d0e1c0c1101080402090a0f02042c0105060a08040b09101109100e010f1101020405060a11010f0902060703081308180a0806040302030f13050d1104140601021f02040f15170705 82
    0x4101420010038080c4dd20140c030703a801380400255410b82c4014140e01c0c1e01c0300344c0c04c04946100c102845003c090140c1060b0f03c203242c14003403925240d50000029074400d0b8490b51014035520742103017142c5001c271081c4000b04c402d401c220075100307549034090150040c0da109462850501c0d0b00d00400fa143c00e081c4030500c5000801050004c3c1d407891042402e00d1740311008030001440c2a8035130021401d00e501100300c08010500b10307003030340c0380580091007a0f0080300d01c02d00d410003a01c5d4850b400580a0f1080d1a00582008400c6000c00e0305071b509030500011749036200d00c80607916021a0b100300c0e141d01140c50418801d0f20990000690661301290300c51056505a01461801d08001040c03110b0350040c005846000c084050086516214440d0249440340550082840c0810200801050b5a8080540070400c00490f05101042e42c0000c0d40c5540044440f42480000b204502d80d040240901d5205400d0410444000035110400032501030301d008040e6214140110201089184a00c0a81d4103500182003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 433681843 1250 433680593 433680601
    0xd0e06070503130f0b0108010903080708090d050304030527040b030a02030a02210a1518121d03100203070305160c020907211a030d050d0e1c0c110108040209 69
    0x8060300001c1184203182507135506861751100c4500324402d8100848a039500c803618428583c00000640c3d002c80b5600d01054240360a245a0362242039110200050010100c0440c2c201030007003040d01c1000b406030105022030034201e01c08485050240841034042ca18005000c0380038100803072030303020180d00a00203084002c81942448452011a40140c0c00c941c046508980d41100a021048600380580503642c4c400042540d06000c903000910707803a855164050310200001c020302c0c8559100d110701c2c1014080c0d0040413995010b542d8841d84060341c1406003240b0070009010700d90255000f00c07015a0b0820140d03580e4120250034002e40c581e0700000c600b400220030010314100b03060741d90020f118502120308442540d004404e900c400100d8000d040c2e122401c05940100803080039500b84c4044008000860b048803018141c2e10411100400311a10780700203050243d010080380c0e070740026220b00c1300541c04001400034203d00c0c86a000310358100c0381c051812095072060060501490b002410002c20b42ca07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 433683093 1250 433681843 433681861
    0x20a030503060d030e030f010209031b01120c03020c0d05071101110a060b04020d06080a030e1e1c290603030403021f020f060702030a1202030108030306100207080d050d0e06070503 79
    0x14000d0f000c404000300c0c028043d020751820302400424038406000943c650760a201014108903010b01d0300b081a511500d04010241c1c1e01078a4040c404074a0381d0006000c402d20f150481c0030b03100f548900f0040d80f081c070008030101c0d68080010714806000b402a03a042c00c0c01c02004450818540a022041d540b000e07001c0300106080c1e1340011448070380184010b103802507440c00760056900a5021702c10582090a0803400c1c5030b080ba000124400c0c0031201e01360400040386522451011101e0521b00030300e807283e03020070701e020b81e0381200042c15040401c042a03140a0800e484480d00b500c0015912102060f010410604002080c0c60660754003e0144110320f04004011018071501c0780c1d00800c42c442c0c0c210161070740741c0a0007032501491030795004e0355a03081e07020700c060040d803288541e01400610400c010401e40c03d005c4290780e08030b001110001c20038240083d08030318002c1e80383c2000442d070103072400160030160400c0c018450841c02d008188055460040d43d140c44070801c842d204042001080000c401030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 433684343 1250 433683093 433683109
    0x12050c1207021014070f0305041e0f06050a0b01110a0323120f06120f0601121407060203030a1b021213080601030602130e040c030b1012050a060507020a03050306 71
    0x3400c500c1210782c0c0b81005990441518442c5114800343e50481c41070056040d8050a00b04010740746003001d100c50704090f0740d81020b0b400e00d14028041d41c41c0d03207012b40e010031920580c0d914140350001d409000504180c80882d0052003251111800702d01e944002075001403001c102c0c030800640644072038038007461341ca10140021690704003036060302904200c4002c4258000c0200c80c007940c090344d003050700c9181643c14044000c0c01111402c109500910103d404031038002401e5040d02e00900000f48290928a01510031030483c100804207070260320404504103a000014520400301448148290720059039032115064044003003c00580001d01ca40302e0003001c8000601c0500e508401c801403942c2d903a4a441c6c20440b0a8100720744541e00000e5248134104014041d03006014440880e003450700b0190740c1c0700c558000300c1c44014004005400015040641e138110040107011b03000c18414100c1c2c0318a840b94441c1000841161035502d000d0100306020710001d0b2003d00640e050700c6482c030355103540007000255 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 433685593 1250 433684343 433684351
    0x30105040b0306040803151516050601051504090b01020307080705010e06070f020d08041b0e0a06171f0b0a1205120307020c060c0f01020a1101060504090b04110a030c0b040612050c12 80
    0xc50079600c04a01504403000388909c0c4590306186400800074a015400d014040c1c0c0301c103115a6082070f404214440c5102110116094004005441102c0400503825400f13680030281640102040010600406403c80c4040141403000d459056403200410b81b100c200c410921001a0301c1b81c20000c1c001d03805044000d800a0080c0c03c5146003403150950315400200c00d412059258041000307004400005d070082c900640021044240d200040d03c03415a40c610007401220380e501d4240321400f0400d8802d80c000e825841e005058101d0041d1a0307041c4040c20602003804580e9803050203071020000303402400342c5e40030b2207180c0d001e031810540d0101003010701d4012504403a2540180100221200401d1004046202940e2182d4032071610032010a401c44140b07a012501507400e00c02c00000089003c00016071240c2d02c440300207c101081008150541c1e0a500024a140e008030f2003c11910b100c40040c00c1150340c1640d500700d080d2142c0000c6420703128103841a054444040c4102c0c00344984c0c0c9130b103031548 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 433686843 1250 433685593 433685599
    0x3090312140a05090306062704060e0604080406020c011e0c06020d151e080307020411090a030615060201110f0a1701180b040b01081506040b0c03030105040b030604080315 75
    0x3000040301480c0c00c0c55000c0340c0c0030702c0070400000e129101d0342000e1011540c0004102c1d60f4206000d6007400f900074154001143d1403030401c8403000034041001c1c650224098044a03000c80d006803501c1c0c54400d015520a0107100094407030000c40c08001e40c4601c00001c456130000c00b050303041d2400100c003902c55908861301210080d800b84422912020346d485848083c80d800396400800516284001c1c014082d51801c0f007881c0e101c040b00c24070000200000300c40307220782d040d240040c01c0156802280e00501543e46202d60044411100100380038090300060001c5203501c40c4032900990f00e404c1603003207500180180000302c1d8103200250b0302d030105101424203518070b801d204942010b030106120081000340c0060305510304544100844182d1881960103a8034183d81c05c01c00700808000207030220700c00804c2034803a0001c0389520031554030358000761001000c4410041e52286511045562690024040d0700c0c0201d2030032404084d20328000400a0240e504a6001803468072a1700b47e001c0d40742400540c203a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 433688093 1250 433686843 433686857
    0x110405180102130f080d090e04021c0506011a04030b0415020909182a040c03060902040e061206010320010c0b09010e100225020418080a02120703090312 67
    0x40d00c08000c1c00280707203121140340320b5a0715900300340400c01c5890300e030f03080300103a54042d0b000c030841550085a160290707440e00c580022180d036103200089105075040701c40141c010742c4d100781800b04100020f00034103880d00f0001c518650780700d440419000d4080c900c03001c1c2c0214010008180480c440da2090049409201c0d03002d85845140004107070042d40580707034060384e03840ca080081038881007840259641802100400c040031701d110000340c800c0603a0280180b2840ea110580703203009019500800c010140b03210255222642c0b403c01ca48200c4045442e2402090b980c1c8181c0c54007800851280d040c0e07680910f6440100042442d4500c1500541070101e051001007036800b400f03d48011640703449a600e1400100310b04648080d01805c004200780440c91182c010703c4030107220090b8490140b030840d84010201d441c01aa1700008018084001080c0ea40340c44c41501401480341e42001004c0301400c1d90204c5c2c41030035001e05c00e45c980384140d10024001580c01a4140700040c0c011000d200d0b03c04061070299 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 433689343 1250 433688093 433688131
    0x109090519021b0c0901030b0705090d170d0b03060f070804050a080301091e110a0f1e050702030d090b1207030e010507020f07171005070c080708180d110405 69
    0x140c00c03070780300110f00e04007440c0320407107400c004908000c807a81940c015901841da552440c1e6400a01c40b0028190b00103028021401000a4581040309118250402c10744070403a100c10481c1d4034a6801071036500350442c14021075107a07900f0300085a0340206400c081e10182e9948150044a5803100684111440c0c050a0306541c040341541002d51b01a114036840050b02040545050302c0c01c01c50b44d41c060340810f05100502c00001d80c00802d50f45e98841908000e10031000548048481020b0403500e090401d910b014240d0304154044007800b100d0340b003541150080c131380d403282c250380f07086540c840e07214038903810801d51100c0d1550501c1247c11601900340130442d215400001c40c25610f040700c2070030040e072180040c000e02801c00c1121100424001040100043c20250010b864035882c03a0802a540e4555003c110514810520712a010b500040490f4484030989000c0384181d1100540c0c0c1d00c03091208070154450310f40668100182681300c03050301004d241d02ca0502002e80f00c02004031040b501c4034a038030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 433690593 1250 433689343 433689391
    0x2b020307030807030315080c0a030b07020f01091a07090f0306020f04080a0f0c12020906060318060709090b0411091228020a090903020a141f0e07080c01090905 70
    0x150440f18420b84000c90000c00320b190412014506038480c00b01540080800a26912400c081c82c050341d411049003291039865050981c41c20940e0300ca51701c09503181c0300005041c8240c10a800d40d55481e5407070318813401d0321070352400c07211110325001d12040d2840c80c5800b0000a001540100722000080f09201d01f850355400d50507050003000102559280400d401090401000e401244083c20000c0c3e03540c13100c150507402142628030000c000350300600c4000701198008100f5152034103605403d00c203e551034074080b5030083c06c00d500752181240d02030600f0103845007403401c3d01401e030f00340071070104203070804006400300540f518150380310905c1c038040c03414911940b260150364120900000c00c2c0c526400b010600c14401c0e2000c0590040b0fa090386003070500070010f64042907011007030390040e00078024584141042400c00366401a03c8034141c0d0b0b407144a01c41c03140301d034100030300d5215181c0c01d540da060317070702d192083c1ca40c101102c0040c006240d5100a10808a82e58806a080410780300e0030700c812a102100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 433691843 1250 433690593 433690597
    0x105010822140a06060816050103090c05030f16060c1e0c080d020c030f070e0c030a0209061305190b030a0f09170715060308040905070c06090b10052b0203070308 71
    0x4070035140d800c00e844520038000c41740038080050201100030281c0c0098080c080c0b0a04619000302d604158582c9661700902002e1907950001e80402000c0c0c8211442e10840995100c1000000800748030069400080c21801060545015508924240f6500c1980354a01c0c41190700d0382811030b01800380c0d61020410f04010000d1155100707064001703100c401048420149016914480020171341d01c0700200340400031524040b00c1d0011542440342d43c407a1594003002010740070351940c5a03040240412031700f001e41c0c0c0c2001c0c0142203480c00d039003400c4a084102c9002c083c6c2640c0b4002c1070750903042003003c0342d50940541e010f418100c28a500005000e519503551741c3c40d03400f903611481d03144180490761501f1300c252052504c2c800003805400304a51840c41e50391504034000c9102d5046000c0d514800250018041c00400100560000003085940000c1c609801000420784001e10111250030003c1400e041280c030301800f0481035203507402c40a00110318402559030f41001260140250f120000001d818040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 433693093 1250 433691843 433691873
    0x5070c0605040911180103110d050a1d061509090a050a05010204030515091009030504120f03020c03030c1504020102120a030b01030f0b130f020c0a0b06040b06030105010822 76
    0x1881541d075501e8030412600b611380d107a41050314210100000280080d0020709254107650a007404284000c02071f84c8803085000c1c0c04801b01041e41002e041020344e140315400121098039039125001c3c0c040407072210350350340c040440c2c0a40c10300e032a040e441c10305446c05c040f41c2d40e4032042c50402c461030f003609640c4141c1408a082d1003121280e4002c00c041c03080200030b0108140300d081a1807204080c0c030701501d84030359594989d410f000315195120081c00078140b0500494000c3c00d84100c81403a0383c138017494a505c98211040c015001801451070100a514000c01210f40052954005102551103117100c0120b1010143c0200c1c15446142100c0340d0800c542e501411007803400d5140050881c07010700014050398a080c01e01d00b01e15103800482942c1c1e580702d1442c0c0b02460311003c0c0c00141d2100b0000f0400080c4035a030b501c42e21910031501d052003000610060700703100300815103003400301d01c2400f028000300d40420b0003102d0108143c0310002d00622105005110042884075008420100c5601c40c180f040c1c2d400a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 433694343 1250 433693093 433693097
    0x20d02070818010311030406020c070506030403050d110405061b011d0f06060f011d010e1507061401150c0503070812040b090f1b0411030a09031e08070e0105070c06 72
    0x4a8801a1042c41020070600d0402c01e003414004140c40b03030041c03000d600c40240014001603011815181e1244100612800340002908a95890400b03080203083c542020a08800160070201901010f103580300035501201e0f4064030482c10b0480700d800c0c1e5a006d0a00c2254444159a5641200030321002c40d2481110103005602401c0b040d14650320709824050010401c40c0a010400c00307400603642d00441c88000c050617103801e160b140c011030004903000a10210703031543c0180800038003026030a440b07008000840c4928010004582e8001d0544030744442403141284500c844820a44034a00032030f030742c100945c8107006503441c0c4510f56840905c2c540042111451500980041004100300030f4042c82d000740900004045182c00070008035610b003030030540800718080c0340000d2000740c3c4440c3c01540d000401c44a0340c903124034146009038010903003004c05030700162401d80c904020384155081c1c10555030241c1d803402d4040c2e580d400c1c107589880c0d0748088641003000810494002c1411141080c0c041c00d07039a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 433695593 1250 433694343 433694347
    0x1103040f05031207031205041b080102030915010b070b060d080409020d0b0303070b0610050c0714010305070c0803010e151002150604150e0a0e030c0c011d01020a030c06020d020708 79
    0x4030080c90710b4500d4040001c90290f00810000022035005805512003c501e1803010910380d90358507042088500c2c4040d4036104000c006008038004a064001d0f510407002e080449580d1101c3c07086e11803001a00703101c4e440c8510f004211101c00700b0a41c5010b01c3d4401e80c003801c4020419807964510740c0e20742c0aa4000c17400194042000c0203800d5050207159000c0104400560406106840328411050082c2c101c80c0700b044a8085440c20318000e43c141c070694144102039400095981554009484a1030442030019103010001801d0500070500c15102a030003100b02800d581c20311041100b0f1041c09000208840c100c8002c0100b1656446c0c084d440402c01680604440c00d0f003241001041c40004d41230300d1069040590364141a9100c00a6104440d1100051041a1aa00c0c1d11500400c511540040c19000c0020740c00030350b03a03002442004901302a6200414101041813501c0080b01c030a91690050300661b5107071010a110301d0409c80c10710f00030f040040c03034000d060100d00100c0e030010404071800100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 433696843 1250 433695593 433695599
    0x703050c04151419050301020d020d05060105070f140a06020708090306060913080304060b030a1214030f07050304020f03070f17011107140313120605090705010207050d031103040f 79
    0x10900a00c01001c2403034480c04666800c0c2030b00040b030f19a800449500441c1d80c5907442241d214074010480c010030000d8001c668400140c58010040e51094000c03070356403400c00021801551203030302112955030300510600a0b02010395030b83d601116003030307402020901c01c070080c61000c01c01c01d20040c541144603042c495500d0340030308245810024010f1419202e070110008011203c5140021a0744259200c410b0696030344d501c1c90400c00800107400c1403901403003052010801c0110302e8800c403500044070340311001220190f41800849210499060090301d09220124901e58080c0c0d018581261000300f110350070302e1030344001c607150103403550003040c030a04480010000e659190408098039506800240311100340f5070181d002c24840c620000303202c800202942c8003c8242813040c0c0e6200181196203115050ba2100207411b80d4117070900554203986098080741c034070079000559030222001a0040c00f480c41c03a1804020a0b0404040103406201c0760b0a111032003248240028006400c05501c1134002c242 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 433698093 1250 433696843 433696849
    0x60e01150e01020c0f060906040b0d060305070e060f0907120f0209330a12090f210c0b0a140108070915080606240c060421080609070306080703050c 65
    0x22081e40860540d0004580920b494640355605808500e00342d49060351380f100c13003001c62010301c42e80d44089501d42000c12041c00d001d001d82c02400840380248225080d041d10380b072400c00c0c02c50b41a1040f650003460f20f02c1f0040c1c5401d02501c130b00e501120b0341c1416029010703c0c21061041d120140380483c200740d8001208001c40c50704040c0150321511040c0c5103040d803400700702401c48640c0e4400801c0d02128006c600155030720b116000150f24180a40b405009600103403915051102054104480404000b02c1c40d501525414581201c4051246e0760768002d444035481c5c2c8800c1e80c001406d03c0c898180c6810402c1070341030100207114002d00440005259070fa1400e002042107900e420b00507a000180c0c0407080050500c0001d40c02c0d003143c001c952500d8080c1c807110b45a00451f802c44070701c45480f01c0104030340103a450041003051040d4091002d10704a020506031f0311035096018014180480d91400109a950401149035540040307642000038825031280c02d002d1400000e03520840d0994841c90207007080342 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 433699343 1250 433698093 433698107
    0x60305060708060120120306270709140f011d030a0b041b0e2215022a0a030305090c03070803220b0412021801060e0a1502060408030901060e0115 64
    0xb20254807000d41142c07041c061511401e6240c00146c100e003011021546964484500000864007002e01ca040541c1214000e581e02e00d04942c0710b00820350140e4001055844214500c031800c000900c4154400140001502c9009203404954620039a00c4000e2159441c10800080494001d180f211010704d0030385007503a5044042449514071143e9030b4020000b1944400c2c900e5040b520000219141403124081041001080d1101a20401401004035103017122a0300504a962041103e50303450100079050818041c2d42c2403044490758000594400801d110790f000300c1e04464020b060703908098406000034a012695000150f0981000601302890301d0105111804a608040c00f0700f1140c3c030305100702500d030103140721b882c1d545400724145004558a031a01c40a01c40403100d8010305e20b58444034010040e08048071050701a0800c0000030504550030b0101d00c040c0c013003550083c015a9900d0340c6058480e00064070f042807640d25094003140380000300c180306010744503c01c000840e100400c0c0005245d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 433700593 1250 433699343 433699367
    0x30b090c1302070305031314070f1814060402090103020906120925050f01111e0f0106030b040807080409020f12180d050c0304050607050f0c15090904060603050607080601 75
    0x341d881045148006904401541e42c805814002201a0700290400c00b2145410341c00c000114010080d0108007118502c183c28182e0b409481e8400088080c2c03045030b0200d0f41129107161188099400141c1d0502c0c4c16001050740100624000d400d10100c9004248240c1000c0030360030368014828204204000201b1041a0300341105604140c032210300000300d05007904502540c0c1c0070742002e81c10401e03940d018007030384c0c120410b4440441e02c200740d41c0c8000032072003140140e00202c40d004085480300f1600c01401180c00340da410441c2100180c0311a540c1d580301d035000e0710b002c6815400038040051102011300c090b09245044400f0700d543c4491000b1405085480242105400346c50940f0800d0029000900301d02d050740c2d20b00741544c1c1d4140050202d4918012603005540c01600012030800308200880c0c6600a00310032001c440701300700d4040810441c0101e040c030040740340030b0500c907903030300392400030303c410b82040c029500003807216181e880c1c517400c0c08011190000400c42200600009503840510200c0e4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 433701843 1250 433700593 433700629
    0x204050402040b09040c1b02091b03040c08071502120903010b0a030803010504051003031d0102010615021c030501050306220b1e0105090c090d06061d04150c091e030b090c 75
    0x12201d40360000d060287d82d001c001900031500103000448070f8216640112103141d40c404600e45900d05480c0c1342c2c04a00d0f01d401051164054100c0c00150a210890703014030404550700580200e042c414142d1415401070268142d040d0340b1400d45200d1a181c00411101440c010b110f030036a04d42c184410701064a0740604806400c554428041010031b9001c601441d21a0910001d21b03640030400380102e000d40322942021030040c4030600c2010401c1d8000981440200449840140340711050701c0550446009101311900364212000044556000c080c81e000c8507a8030030031102500c071440d01d888840d80421070302c04402a0005074448002841680101e0040008940c0c00c11a0704e0182c0c0300e00b071f82c0d00404840c02e000d40510840a005c106003038100b030010701600c4030811b0940c245020070b1400408165000d071400740d503034045294451f0050161071030a8a0703944501d020a0b18080b0000700b40c000c04060705e1a901d00320b4002000260000b040e49005855580060020312241010030400708d88141903c80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 433703093 1250 433701843 433701857
    0x809120f06060d021e19060c02040e010204030f08030405070b0301060c031d010f110c0301050406022d0301271109040608030301180507111501090b060304050717010204050402040b09040c 82
    0x61740c4401c040100b014001140903041c0406001141507154002c0c1c0c80020b030300b00c402011500c160306c0032941e50403d0007144c05200400c450320119080748585d0101030846403040b140030000c41c0c0e1007002560458843c0c012640010b6842e6124545a0401e810400003d0003624a01040c540e00c01001103605658403040001c00740d41d04006002a0b80082c440c00a100c04019884040d40f001c5c0448484180058020300840c58580b070140000d6100e43c8021003000520300182d8046c0003070007100c01c0341101c448945844c0d6401d02810020b4494103540360b09030a0024903020319884034500409408000b518000e41c1c88803192000c0006a51a64000e00480c0d8001d1004014405041500d8100300407410740c0003406848014040f80e0600b07a40283c00d1407413040d035044500d101c1d1780d1490141250900d44003049180005020001ca900c8169809000c95018031014043c000e50443c041180c168003600051500b43c2d0341000c01d041c1c0c0c015500061505002042c529140d00b03060242204c0004e207460015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 433704343 1250 433703093 433703119
    0x618060f061e0a080303072a060b040204050414100602150c0918010f0305010f1109040b01030e0f0106080f0102031315110309031306051303030c0809120f0606 70
    0x4245001404948115a6040906041811030460400090020306101d0f9056160440b46540c0c1d0700035103ca6000984c038105140c00001e10540800f11300f0701070800444005031544540f4050804150010b078090303802c10001403165994822024203807056180315081f458030440385610346141e588001c3c155000388034041d4620700d0704841641d120080710002e58a900040300400d00000e1079400101c91544410000700c0c402403582500011644914020721030109010440707801d90f45160000c051000c03051226807028685508002c1c0b0208040c50000380c0c0c03050202c051854540c6640d40c00b40c0300d9648404c03d020320f84050054008805a07040250b28504140a08500d85500c1c80317006403944d0105100b2820300070300d54120100c480c04010095499003800d031403c507101c1d40900021003042081810000b5102d0140c0b0981f81d40c4030180c0001c0c0b00261550b01d090358003402d051011146c40702d0411405040d40e40d07404118141005410040040b205684c45040c5494005041c07a0720442c170042c140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 433705593 1250 433704343 433704361
    0xf0702070303050d0906020a0507200d02011b060614120a0f17120103060e0118080d0c020316060501050a08060615091c030201020a1b0807020d0f050a05061806 70
    0x4022282d061610590780c0714040c00c1400180300f01200100040d00006105009682c80300c0074007200c90003404680c0c00b10b1160041c0d8480382c01c1a50070260806400324100001d580a0309820504800d070380d46050081c000c9907554000c40d140f44d085480795107a034641c1020241410361a00c17100380d8208000b401c8114a58942e4044032208000c001e107004400c09581040303002890949581034182e011100d01540c5034038203440907156040c2c40102e198a4000310103211842544403203919900300e4807071841c00800000c000040c0c00c0910000c0103510082004040c0060030b918190b0410707001c2c0000140c2541008108074450702c0395400340f14594800e4042c01095a588070084064940760004140d64580394404111a109800f442c22404100360351100285901074004206031310450303440050540c00702d58101d000c460100c001034032110f020b024410047c10410040c040ca2400f45024011702c40c101e58401d450501e000e141282d46411036000d01c044003520100e40c080900c206030180856107850040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 433706843 1250 433705593 433705603
    0x110114040b071107031113020307090603020c0102070b0c09150a020c0d03030e0307030906110d090b031302060313031202070206270604090b1918020304110d0b0f0f0702 74
    0x20203081c00040c003010500c20307402190303016503902500d419907400d16aa4240070f00c10183e04102280200c4142c021200824824401c40784500e1880d210421040d040400c100c1c000d40003071500c5141076608106a42c0419900c8903401d100c3c401404813940c2d08c0ba140c00502c424424000000e94211500340b1881c5c812503004904030300d80500984010010000305c0c00c0442c0a40040c0c40c101c0403074000054075005041d800512034090b01c2ca170ba1207a0001c1071036910384660b01e80c0709400c2c000024000d41d03821311050713110f40000c42d080150030400815010050b0002245c0380e2003034501160b04011203030314804064001d01342501080a100e030440c1072030015000303e9180e02c41c0006c5e482006a04082030b000411204d80c2c54880503030060300898455403603003078130300040041c3c40115114950310301c1700c0269100c0b19004d40f800d0301c0700000600d007a514440409800303504058001c48075100700c034140103071030740f2600c05040d541c5006007042c11842c142905c50703104004005e0320300d40308108410f041040098002070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 433708093 1250 433706843 433706851
    0x1e03090a0809040f02180a08060c0f1803070602070e0105030304060813020112050907030c080d0903080d0f0f1b0305010308090d08070f060c090621051f080d110114 72
    0x9040e036841d200100014010540c003040b030013180303201284407100c14414041820700ea804c01e0301c1144d40240c0b5004103a03030740c640494042c0e44000c1c040020140300302d040b0019001013190700d0701020300688103400203800c2241d0b5401400050740416402c22040e8950b94a09004010a402075460142000c03801003e501000305024401c08401d0061003c5901c1203e0f11221020341c880200701d903007003100300691914280d200c00d0310150321040e401325140b40d002c50b503001c104210743c48008003240b45640d03511294020500500701d4aa46812014449080d0f01980100c500000c00004442c070000b840184440484d40b030b400c04161030880180006940081114410041181d50301c68031412807130018998843c100e40203001900300150901048415080004104d107980c45124006403160000c50346041101481680415454001006811581e100715003280800000905424481a40c080c004140307030b005501c00d500a030002d030744040c0d118055007a42c0c8003250007030103c400a0503140c08000c401034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 433709343 1250 433708093 433708103
    0x20309040c02030c06040309140609130b15030403050301030b010819081606020c0c24030604150509090f06060a0608010306050c0c0708210a020a14120c031e03090a 72
    0x322412034003802001961324100c142c1085681c00e01c0c00d407600501d000001c0c0302d040502c4c92000c2c501c8030b5510740f850603100c2d010009840c50040e81101407000d4041c0c20b141280e181c200c1c8046c03807601d600d64908001136100768080c0c0c403091345c3d82d49503242800c2c1500050b442104141c01c000c8100d0144c0180c120300c80b402c1c03604440d8032900c0382012181ca2228000020000307000c58800280082c6664010034416200302d01285c141d00c2200c0702400c0101c0c108104406400c2c125800c0001415615040c3e200b4603494110485035003c40b03460b44042a95484140d0348110304c0e13400141a10b4a4920412001d41c0c804000da4000c0242494642c0c040c107085410f0000410450b1242d000641c4800c12005548009030100700300d500f0b6170b42e074821117906c0d1105003100c02c60128030180440d076246840000c80f0b010000366030040083d4512912004c808a400c0c0e050040306005052480145803502c80142c2940000c81e0055a1303034414651000b60010300d1543d80c040c505a050041120790355020842142090b040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 433710593 1250 433709343 433709351
    0x80702090a0609090309050a0e011d04061404030314090f1230011406071509110303130e06090403021908091309020103150e13020a03060c021507030c02030904 70
    0xa416000182c071050708020741680c60716407980280740c0e005100030120351066441038610350b219085440c50300424042c4c03805401c0c400452840e89100d400740d007030740075000d1680000c2c00c980700d00720141507110558040d0006034a64905140400351034824030b40040c81d01e0018040380306030000aa03100d01800c0d000b1700006d10085007000320564a08012040300580d2079071050a100d102040d0a10030328207006010260140c4142c980403400c02c81c0c02c480d01c1c0c9070002a060040c4001e00c8104010300070500c411644803020200007005070320301700050100381c0100e0b104240502e003061508014650000c0c00141f0031007014081c00003190700461010300c2c03c3c0c02000c10003c401200e0424080740d201b00903810381c00c2040101c070344d2040c00c3c50340e1244007464404da07810b00c8510558551440b8100c0903020340c0c240c3c8410000810b0620344002a80c4510074400b8100307406a07562911340e5400c44100402d4103000d600401c41304400d41d856140340603404841ca0804020080816000a54a0003a0a180b5004a50b1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 433711843 1250 433710593 433710601
    0xb03190302070305070b03071806020a060902010e0901030809030d03091e0309080708100501060f080a0c0e04090b06010e0d0b130309030b131401110d0b060c0a03030b18010308070209 80
    0x70a0040b140590b4000080741c0c2c0b0a9070301c00c5840810fa0044512000113440ca084070b021207008002d100e000c42d0840c0d401044060250380740c050003003203500d0040781400403860300c4030025143c0d044910300950040351226110650300c400c1c141083d24220000080515100c60000010140c007050452010a9994240d4100a074901940c6591040d003105106210b102400981000001050040442034140a0005076a141c6082d64015510300301d60010885240009007840300a03880303110071130380c50710302a12042075013008642203424030b90040d1000f1882d401005070a50b04140550803800055408500121590f182c0300501007028101c0f12000081241240a0510824003000071715041442c218960421114200140011910407114020b01040500040c40c061140b0f00c0400d8082e01403a180c4004c50b608000100319080b1500e0b40030350184404e05030083c08000c0440850311a413000505111440c0c204000c1c2500160308402011600340107000007183c5009880d0440c1c2d0548030780a250316 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 433713093 1250 433711843 433711847
    0x150703030b030a0b1b04032f0a03110315100e09012c0709061a0f040305010203040f11100e0d020a150e18060d03050f07080d0b040507030b031903 64
    0x40c41091030ba070500c01c441001d024050010401d41c000c1401c403c48201d0304100b810810a00d00440c030001d002c01c90300100c900441c400001c000c41c0442c002c0000c400c1d120f40207000150707603c0c075039030000d80301c10301100303c083d1850070104914880d540600c0244540c034039055802c10b54101890065803071405180700441c448020035041403600c0160000d00c1c0c1c0c240a04806035140c40b84051480810b09e00c00d4071000a0803d9440c861042956500d41914800aa80c00c5661046920484450b0102c00b010030000001c220700b8401355001d01d03c10012040e880f0594280301d44820b001c4c1c2c01c890b100d02e461090242d051070b00491400030100e01981c5890038000e0a000082c50480143e10100c9142c64091120f16482d600c98418140c0980840c2e87c1c0a0303c204d40e241c210203002c81224001d820142e0000c003035021078000d10150015a01c0024018504402c6035120b083c15001240c0444e06203031282d1720581289400c1c020300d9401011486d00308004c03001c26001940e224455044500001c1d00c10502e43d0030301d8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 433714343 1250 433713093 433713101
    0x615060405100e06070b0613050603030301090c09121b0f05060a08070c0210030b01021e0c01050f04092406020d090b1c1406040506010903050a0201030c3b0303070215070303 76
    0x8070b00a181e661605c943e8140180c51078022100745102e6100c103030301c0c12043c52641c0318090082034040d0065081d0b03802c150407600100440b10301c0b41c00340104203000040610809001240e4948603856a14550700420281d18003a0300d0f580204410070808082401681c45907415070702d10160900c0c0c100071a40f102c4200784c40074006c444000c3e40204140c414802c1103509030b000601b440704283d0031202c10205034080c00805945903d00007030503070851541c4203c198885c030007820020b403407200c51078505603490520300d040b039030465075458a050100c0848110b1001d595906c1004203418009041e03c03003071070708008080200c0c81c041c83e4a65840403d0b10100d000f000b4003031000d20a98031780100054882500700f40455a01219410310907424a00010102d51290b10301c1c0089a03171040c020400e001c3ea0364019400341410002c00c604001030640c0c2d1100c1942880f0000041d6039480c0740c3e10101749400c011200c9060b2480c620640030b5032080080300300507100d034401080740d20010710320507440d03009238a0214054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 433715593 1250 433714343 433714367
    0x30b041803020c010917030f341a0421090f0803070c0f0b0d0c050d0515030105090715120e01060f171c2f010905061506040510 56
    0x22044540000c200354000808250756038007602c0d50585a5074800102c10a20410b001d15480c0d50014040c800920a26102410003000d444200c842c9500464250000048c000b8a440720282c201800400c00d00c210b1070800040034100d10b51b03c5a03103203002c4d11882003164014001ca521210740001c4080c0d603034440c0c0c5803035011344851190701e0380040da91108640c1d00c0e001074030300780d401070400440041d40d40358844940080302c4840d02c0c803a0601040c04c414030014012102204140300c420070040410751154840d09104080c404004858020b2003401e241c02c4950060235092580e00400c0f082c070800b03e0f10551101c0800b0145400b2003200030041c0c80b0005400702c241d01001035030030008040741440100048a040c0d84610b080f003141e01d120940310940d18901c480468444002c400b0100d01800e20610007030f01c502076040203260500e000c1540c0b90480700200c0e040203d05954070340c00301040101c140001d617000110714048005818000c0d00040b000d208520600b80302d00c0c1e0b607584045415020350019201c2d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 433716843 1250 433715593 433715621
    0xc02040501060906020f0127030306150819060e1605130803040302011b03080406090807021807090603150e0921091f08041101210e010b061603030b04 66
    0x3a50750340ba0b0181c4840307a50b02030000580208042c0f070000c1d5074140f0860100e48242101c101202004101340075401d000c94405174101600d88038049502500520031172000c04042d59035003428541118447c00701400580c003400107604141e004c00200c06641c40b61a0403040780c0b103180080404003070b82918680f045070302e2024070100d084800100c01c1c80101c050000c0340d000380c94044502c6024400783d41328000d030307420003008111101d01043c017207a040c6d48541d60080c89204a00d180c10119000201130002039040006c460465204010103540d028100070000d00c0395060a02654908050030100c44944c0d0040c0089500c581c000655458000c11841024211105800b00c4000400324900c482d0390120b940b142c02510015a02c0034030034180300390385502e10b140b650340d0740c1e16031181d540c0c3c0383c005202d0741d50850400c180c0d2001740380780004607259402c2400300c00100181c0407031700907101405d40c3c002a0700c00b44503513014049050031601c800400b407001e96040c5800036518529400040c0246000d0000c03000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 433718093 1250 433716843 433716851
    0x170a02090f040302060c030f0a051009050f06011b02030a0b070507021011010606050f0304030c030302090a14040506010e2112071211060702070905090111030f010e0105010e100f0c0204 81
    0x2110580c8807101c14001c0c0d0103682550100e80d20440810850311003690a0500003815100040301c2c00c0407903204541001c07a0380010300350240d40d510304074140c40054580908480d902c0d404c0c00841d47e0059108542424107d0703005840c03900b13039000603403200d405e1000500148050000280828840c0c0201e52540d075000702010001c180c1401d0040941501c150240c9856180420110360f89010780d094408008103a0240d601d1a075a0b65001c80d80301d08990001c50505130240150b8043c1e44e10b02d0504406090030b500846584100170040005a03000501020705015915015924a8907040d005600f1080480841026541b001c3c0314580b51140308450a0780c2d180c00030500e0b00400c607009440504100855540031103080e00c5e13003032454035030b1000c6c2e81d14800340e03001201c00c00120005070003559215490000009086030800d0745010103a10032240344400d0041e010060026191600c0301c42e01400080c68003100c10024100451550003420800130b0510100c0d49580300268801c004140900354050010300c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 433719343 1250 433718093 433718101
    0x11101232509090f0515010c142e0908030606070f02031e06090601050603011509081b01120204051305251e0e18060d0614010608010b1201170a0209 65
    0x2040c00d42d050149044007424a551041a001c940c06054012022507030100b5001141d00019666152800c40031540c10707074801820740d4001001d0024180c1e269201054502038003002c03402c078a240b00620505020076280018490200e4500300c26650700440036280b16039600c04506024451010404009501d0705c51698209030b069400d40c070f440c8080340c07082d044424548400180c00d0700c03020b0074050540c000e0742c1440100702c0c8d1620221610000440b6080030000c6585070409141052803165018078620004a40030045580c4000f42c074070701c0d60412000310f04040c02c150015040d49181c16144d00840d44402c007103080e802d0300364954814901031548030b111041c000325015050920044150040c050040c01d19000c49014840501840400400020300689400717500e00d00002d01400440c1c00c000901d840c000001d00c2d61040308082421100d0418080d80b50607401071180b103050300017030f84000d4107004014107a03040d200d1003415120500303070b0110f02d0f509004c0460719180b1000701c0650f018070310000348 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 433720593 1250 433719343 433719347
    0x7080109050d200a06020a121d161212141b060702010c020a06020a09030203060f0109052206050411060d02090307050d032709060605090111012325 65
    0x441d80c0a04562105945100541d1000c40f110002c60024002500004038000004046900034207042d115801c0540b0b110011502e40740403903030294440e50b51802c0c40e581080344131408101032040d034207055014981c850b0500d90311892080d441d020051942c02085180410140110f80f2032009100202450303072155920303442d00030b0188030360140391180d002d41c0010900c00341c8103024290081440390018811804182e582c2402940304003d0001001000100030006036803e00005005d503241c2c0daa5014207504148000080750405013110308030300c20000d02154100040040c080c030898010800151030740e22410440400040285400c0e4001000690404404000e5000e00481d45042d02281d20980d01c4005001303003031610300c85c0940420780c0c0e55482d41020800d04002e480230244014810012a41c8502d268142da4060704164007043c00400d10207800e5030b0111608148a202500038811060744a1090181c40a44241c4600b85044480041c03490804140602c0c1c4054002c28003001c104c00c90350f00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 433721843 1250 433720593 433720603
    0x3070f0f0305211009290402131203030c030501150f020705030d020106030b0604060b04031401090f031215050112020a050702030a0501060620060a09060b030706030506010906140f0c0708010905 85
    0x44c10001080c200804203034420b2034491150414100c0c5a00c14051154859102024254454480c2e110b6020410030500401d00ca00100003070511008100d501341d014035002d020b803070b0210107a80c10549803400400c99124198011a0781c0f4819003020b070075400c0ca40310201d0400000b43c0041e074052083e11078120490364154040d400f100d01402654038682c0300c1a0030072050b2100f5101d864003444052105101017502010b0f85020b51103c48000030b5401c615a9450300c44089060065010401580c00c40c2c2030407280d4000d54002049012890051700d04040000c1c144070840080c5500362035001c51030082c803601400449011940083c1100d10500301c0740f41c4a03002c0c0515004020004041614081c004099461018200040b01005c1c260903641c40b1010340003003c96220907194140c03078000c801d12b10b44042c480f00f0040c040030750b0080313a80e19000c000074058408650002c010440369480c95910313080d0700c0058940a1504c000c0d10f81e91185040441454190741d030b0010241c1d5440c100860040182c0090 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 433723093 1250 433721843 433721851
    0x5090313060201060e0a0c050c0a0609020f0402031b0d180615060c050a080304061805010b0907020a08040504050c07080307090609050607030f0822050703021203070f0f030521 77
    0x5209400c1900e070081282600c1caa4800c0d0003811400801240802015821841c828013442c5440780c100010f0241c15480e004022205440c910758404905081d0304041481c00c0109101341c40c15440c40c01c2108030101c0588020316510218132010a0441d461002504910000d51034130040c030286000b02d0800c04010311a000620aa40054840000303509014007094000240c100018002c4036555843e00c80c940d910040c42225159910301c51a0240074050209083c5540103038000254128002c040c00314054001e0800c90940d8029807406d0300190340c6004880649034291400b00b800c1d119004543d005006180c0014071110b0040108400c2c994081500c00c101e804c20390b0340b0104240e44001f403081c18419884c2c00380000313041024035442140100c0c0025002100c802c840d02d411210324030110a034000d25442207441d41c01440003041036140035001c5510044650001e149041d03c5039641303d03620b5180031402481c1c44503865240c81403600038010754034030700842a011140c05404055200c1e40c030404031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 433724343 1250 433723093 433723117
    0x70e0f13020a091409161a0711040912020705030705131a040915051e040b09070f0b0a02060123010f051201060c030215070207050607170412030927020a020a06050903 73
    0x241c002c0c1e80c01c10342498030100d0f950030306510001140c0c442c4560465200080550b150303282e58000003010340382c0d40302f03e9810b90b001d807551815000640308003e007044480d5200500c02e6006130410b20255582d0f054800c400555103400081000044110348d50440b00089010341c000d14103003050061240c0100303040f1134002c49074020801696022442d458001ca1060740012100300b0400040005a85020740303a08032000c0c0301118403803a0b64102d05d02c1000e1080e0040802d1141c00705001c144140c0422000c1d0140c000001030704c0c801722030f501c40600340040d0b241500f81008131200014461034003072403c030380c83e8040d4600861101d46c0c5805014211042d40340c5d08600512498180d05032a040c4c03620050700418665018013860b9140208000b82508014003d48155241103c1282d030490514000e00007850141c400f111485010304008e0006402e83d8440d80742c10110b91040041d40280c1000300110340012440141c9810000340120324040c000240142600e14210521030700c141d000000c2c00d2113501c48 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 433725593 1250 433724343 433724353
    0x20f19020303152b0602040f05010206060607121709010c08150d260316020606030a051005070e060d1a0126040f0b1305070e0f13020a091409 62
    0x1004200da803407008869103183c55020902031085440d00340303070b110200190800341c0030007016078501e800c2880f003a540e400c40300141d00280400c40c20380307403114900041109001038680c0c1c3c502040445c0b45842120001001560203501000c5e0460091203031889000c0e2038940c016852802d01403003030003050ba1144203000320b11110b00081d0030b003480003810710410300068001c0c1204010b55841c84070b03092000b2000192014084c1c0c6440d100d20010340a50b20540c1d403180301c0f900404002c0d038043d041080c00380602e8001e812425008002c16400140d060448411a10005090f07a2700d820845100c0c101c04102640000c00180401c14003055412180401e0314960394a1280b140780700041d100040d2517003001031410608641c0e80d94600c05400000c4e406402100304580c402420341d64664000d4048800c106031440d200c0200781445010071501000c0c0441240391507850403d8030b00d442102200500c0c00a0701c0500d11002c600319120420b0100080515810501c0441900054120000310860742011280b1034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 433726843 1250 433725593 433725637
    0x6030b030c0406050105120702190c0e0f01050109180617030c0d0503061e03030708070302070e07020303040b130302010608060702010f180b04150b03070b030415063204020f 76
    0x2842404104d510585500d1b10b0200064444c20034410010910030545c0911104c07111483e0700742c040d86180340e109410028110f814001408180382024000c4c0a5040304080140b00c180d8120072500195000103101c03c100c003d00501038409031140350050740342209244000e00c0d044000202800089942c2e10584000da070380c0500884480c0021500b0310341c0004403460406c1c0103031403480c00381742c0504040c0a60b80b5003460782e110b140590f40242004c4005030300c0b024040140700c11905485400c0b20302c0344042c6281d402d05403628444180c000c0c120004001c40f004c051803c06000354070080c001d0086800303884580c58694806402400c28043c1c0310203081c1400f00c82403400d044041008081d0758891010303038480e101e60702d81303010146801ca45401070550740c3d92041042e942c10030000c4010500314048590700c0c82c262804407441c0c10003210312840ba44c1031400910400d20030012010b590b0041c00e840c2460200d00300700140b41000480e401c290003a200044149900e5031407c002c211407820700300e000754440c2e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 433728093 1250 433726843 433726849
    0x61d09101506030b06090a150807052a15010b130f050a1401200106090f1503020616060608030405010f0c0f0b060a270506010201060302060405090405031306030b030c 73
    0xd1840301501c0080326a08107204060099028882140002d030a107424090003002160309000540c1002c0c2c00c2d142d0301b04a220754035501119484d484800ca04c0d0103428182181c0b8aa0041512039100700501081e1828080c09400208500c0d071040e0a003541d01e1015507550740d0044945d6001440d440315072100d024010a0420780c4424040413110044c0860a00c107103044400018013202020603410403181020421072500980d6410804550351000001e00602c2c00a40c401191200d0300d4418200e401e107003040034041810102d940450b90162002c640c0c0d100700640ca00e03001c0001030750003088030380307070010100d00c0240000107001030307800a80301c40352440c0700c100003681c880e50100c000030500f90042e40c251000600c1c542c2507940119015100300649600d800130382d201b800150005150308044110084c203000d045002e46a00310700e003030000300946402d5401085032841503010309801030503000b010408015041003200c50018000c0074200105071641e4004015101e0309801d02e00c01e00c111010030389140307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 433729343 1250 433728093 433728101
    0x60a0803130b030a0912020f010b0405010b0a1133060904081602180c1c0e0a2012390409020409080a05040f09050603060c0d061d0910 59
    0x10041c049039215071501240d65070540c8020a408400e40e2030303040d4100011002485404808019009006e07098070302051b0608484103800d800384500d08060040000c1c07041d03502242d40c010042c3c90003584400f0b0b003c45a03850320b038080040382c81081440040010795000300142d01d2213031400c144e42940c15298001003201d084030036100604641000c0000c10b5084411500c0c4000051000d0000c51400c2e681e4800d4041c000c0c0119815a442100010200c10310000d007401034080300d1414034100a4580d00440303035030744d07042c010000a0070008031400f000440b110070400401d510900600c0a0910040d0078043c503140e1001d80c840c02c00e142960304c1c541d0200301d85100c11841d48450754181e65040a00001004043d08050809a030040d684400310f00110300200020f091003001c41d00e42c19613403840e00741104010512580802011840c00e0140425654041031094001c03284642c0e0946459590500300d004000c036920401d12480305131345551000b8000840b0314820031a0005a440160300e0b803044105031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 433730593 1250 433729343 433729357
    0x611010e030307180b03100602010e0706050316230a20121615060f0504090213050405070f06020606010807030902100518040207260403080f0318060f060a0803 70
    0x15810900003c0c10051181d5481d518100044510b02c0103281e8802c402d0354254815502150900c1c002101400340300c1d024040c503000d00500c180140000c3e4505103009046000192054403412812902052803a116070480c01c030f000d00e15420409440702450303203041241c0c061609440031130119102e800c0340401c0d900465801001c1d01024262217902c0d00c09c001e0480c4d02040c03561108501084e00c1201261030f000d20412850f42d90200010514145410f41c145540103901840c0311704c4c00c4c114068016122404807044903624070130040358549a0f0b01d45641815150340020004078004600003406e10350028842d0302800c000e0702c8010564603402d0741181512418000030390070610315050068114880c0000f40700e040351a180881c0c0e451000e000080603644120426507210900c11082e400c030309201c10320b010030030064510017864a4030f556560201d40c000d40c0f00f030180f07412000c40001c801c803078047e04542048100e1400d641440c0760080c590849004203a8483d0300607400e6003408507880700004201da0314 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 433731843 1250 433730593 433730621
    0x9090b0c04080d050f19031413050c0409060e060a020d05150d030807031d03030a0507020d020613061103040b040c0506250507240806040507140702030c090a06061101 73
    0x107403e03245001030300e096001c150440c00c010420400503a48103000c507041c40440ea081c2e03402080304d460515412562000103030107102d0540c5650480800600f000901e401d0928081c0e4000c11251050b05040d801404607180b09031160040000300300400c9103544c0140080074648504100d944c8480c01021441e941c00c580541c1c012955029407030109000f034060580c803503100c1ca0082019000c1104100c54a140d0203d11a4117a00100c180942c06285010722540201207100518000131460030096540703c000e03240b1954090007030542000d00119803c000e480d0f60075990380c642d0303d00b01854001c2501d10200c8041c0c50010200c64041000c2c600b250072203a00d425481c16080003410107030300e107040c0d003410800200c03907500c45c4d4140040c6500d0541d0301d0180100d020b00c0302c1510030607816409802408000e1005201700c3c54201001915074000c4041c00040480f60800341c1c81c2d140714070100307182c20040c0c5000760380710a0b81400c2101c0d01c0e4894001c07a0a40d8803d544400c1c10441000c03046098a0b90301d080c042c0c7c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 433733093 1250 433731843 433731853
    0xc12150f0f13030c0204050a0905120c0f03130e0702030f041511010c02101a040f0504120e01050301091e060f0906120b01290a03020307080c28140409090b0c0408 71
    0x51b2625401882d0807140710030002645240a03907449190401e0a150500d00502c042030b5011300c48000e0040c242c0078103042025610789040f15130a9402c2220700d01076030201c581c0308008240a00d20030000d85501148804078a45e0b116100c0b2000c10f180b20210350305070001118443c200302c4174070040c01400801d00c0e00d9001060502c810307400910151400d80c001c9429201802102e04141c1d4407070007841e60b5940350340d400003800c0c2410704007840da40341514404402d01102903411003050341d000741241e044135044000022814800d100c0912900c5400904402590601c47c01054000490940310304403111442c0c1044940d980d03219940364005655001ba211081d003c004229400304000419a5001074120044983e558403e1560385034125005c03001c00031b41d01004005000d6008804950402078141ca03050074080800810030000c1006c441401141e68020101e800340ca001e140c040445241840d101615180c4402c17503000241030030311f0186d510030402000305900b0710461003110151801c92010744 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 433734343 1250 433733093 433733117
    0x3020c07060f0e0405010308030a050606030408040902280917010612110301090c1d0f04050303041407050d03080f130807080c0703020a03081902030c0c12150f0f1303 73
    0x503502002c450924020300101244150f000d550f0b6104141c06184507420721510b03810b00001d0642220710003404103000341020000d000100c2c81940a80b8111402d615001d40c0d40d2004030402001c03000d0217800112031603030100804208c142c022082c0d45c1541c044461850910100e803040500b655118402c50406200c0d01d141300d03000c166024644004030780050001700e04405990750341d0604140590107689600040b80a0200c101210f103074090304202c90103000a81070800b41ca40c40d860307100c00703040108a2014202100c0759000c050080100525004222100001c01818013600040d41180d600c0c0c00c04405000041c91035040704014050142c014030402e06141d032513039a0b0f0036140e100c010110951712075104004016a5620302c540045d5200310711150300d49201010140c8002100742013181990810310002c0c582d00000618416030645c11140156089107101a05041c0303400c201d51204c180c0f81c0c00d4100003010707201000c0c10340100114043c156660f0b030341c3c16041c03002c440709510007000159244844 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 433735593 1250 433734343 433734347
    0x604090e01090215044b0303030b06030615030a0e030318011415060f0f0706020901030506010201110d0c090911070519020a06031a1221030105060909130804060c0c050103020c0706 79
    0xc02030301e454140c0c6c01d8001e1003030701141c03503101d05e40c0040302801480ca81070034001c046d03140c040c2c48031b29003054540e40e0079401c00c1d81c005107141450341e02c51b01003004d011000070040d0b000e6407c00c010b1840c003e0180c030341d07a0030724843c10280b0030a6800c02d00342a40c03c040170102c0380c4002c409080d100d03103010801711401e0200d190030446158410891084950424884a800414140001c0c040184107402c016603c20078000050160764000782103034103592514070302401c120b1821045070801d000f07070840015030800604080d44e050105400c0490514a0b0001750b54046403401d000f41480750269084039030461740030101c65030940815034020340141381d420741004840c1c0aa040302c0100d030b100b0500c04a20b0101000440c11084050810307212035802075183e1044e5000b1070310658142208030b55507601d503604110205038140b24021110b03008a02010000384d850182c0c540031000d00c0e03408818a0b56850b52040000c10080401c1800c1d24102d000280014a40d07000f0310131a03500752040c0010b0001d003464010700b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 433736843 1250 433735593 433735649
    0xc04060507020a2301030e0606011d04091e110603090d260702070603060501050c1e071a03012303102d0203090106050d0803010e060604090e0109021504 67
    0x400ca03040b008000300451244080403041c490200000103880c8440c0c00240010191002107112a032181c08c10b03024010181d90140d803040300040c0901810042d9800c103c0403c009000b07028018002401c103520103001c0312290380c822112940510b408c2600c4c1c1411908001d07143c48195650503850b440740041c13015990103000e0344184e81e10015000e08501c850030300c88105d480011076403040160032142d410b12040d5054403603900504828a403480c284090b9517480d980e541c6420300c140310f5140d600d444601100004003c5c44014180c00c032005c00c0f00c108820b1010300e1700e82003030103100b08101d644c12141500070b0a01c3c40a031440c107001002410641041682d0b00d00400031640241d003513140510b00840610600704107500c0c07140d041c0e20b0044c1d0b00d00e44884100d0840310365800c083d1084103944d10303100c04180c0079001c1e00c2c103641000486080c5510f554000501c41e2086900c0340034403e0500c0320703034040040306601048449001340d07608541161401d031030502500c914000e0310f8000d004030002c00407010071061 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 433738093 1250 433736843 433736857
    0x500301051008090a0c060e03060906011419050a0f14010806060706050a090204050702030a18060c120908072304050c2d04030501050105191d070318030807030e060c040605 75
    0x1007618084c41030380c1c4940d00e0182d01600701c3c41c040b07000f2050641c00c60608000441c2d0140a040c0500100c1d4101500c8100c3e410f89605101e104081c840802e000707681681503904001d0400409040c005e40d514120448005414030601c24181c10300074401003994082c4000c14841c1100800c00e52030034607240c0d01c1000900c1c01811000900b81c0d6a03c80741c00603203170b51048a0050240f0f4000315200d5282c44002440c12030490003007005202d21100c1008203030341003c0c5611000354000a00e203c0c4903080700c003c0f2601249640000201c1c032615500140382950769904285180e4592500c21000c0060020301060f1170b01a11010140c203400c010880080b0000d0718550701c8040c3c5509082d240200405403c2802e4225800560f0680d54070b500411252030403c2401c540810147c06907d40d5174540b02c034810016001d46139048505109100140314613200350b000244403001019400309440d014200106040021908040441c5c0742c00070410784694001150791180415140482c80e29003802c000710351980001c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 433739343 1250 433738093 433738111
    0x6090f0604060c170a0b030f0f0c0d050f070906061e0f08071716090816060c020a050303030f090709020c030f1305031c0305060603040b0403500301051008 68
    0x143d040303078012004d0440c14080c0841c1003001c115001e0380c00130035007007080d9a06541d1059008032808c40740c0506c08030701c00d0300c441402c07079500300044064186130f0306225802c0d503140254000c0041c041030302009940311f40281d80c91035807034801c02c608560380d90162124200324880400c0d41c6583d194842403156500662000c4c0c507181007031402c0c10b404881c0c92100400e40d56104000c0b1a240c6607440c260f80241d0590081503040c000306400154550412508d600c02d020b168104880e13858080150740791201c401009010107030403070703070f43c1d28001c0701790985031034142da00307284a01034070710300141b54015030081c0d81e00c8101c0280503625000020100c40c005a200c4000740500f0f07840c0d0b54000070f25030f80510911400003511864903100e0780034080010204c80d001804a4070507881402408041002c2d0075125070b01035132508011280100c0444404001c2c0e40880030182c5084a1200740403040c0c4104600101482c0e42062855990410000e08941d0780002d01441b07803c4104624440b00c1c1c01c7c402c10040707801030048 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 433740593 1250 433739343 433739357
    0x6080c0324060a051914251a040b0c090a090f0b0406030b010f060c0b012102060a0e0f0a0b0a14040503030403061d0c030601050103150e130506090f0604060c 69
    0x110700499001d4000601001c04901d01040d030800c3c00c18140084000340c0c8103854409103004108614240034012500e081490b440c07140202c00d00600002e000724104c035000b241e42c40110b122036011107000c500855085401d00f2009021900170035190058554030070004014400c0a820242040000c000401010040640314610700ca4161500d00c6182c2c041c40c06040706182c1ca41c14030806141d0400c0ca40e00840400100d19221004111140c04160568841104984107503150310f4490407445031410019501201c00904101030640105000c841154140c80c400020100202080b0040d40d95200312114210100800340f051403141066000041215a2040c10540c43d00702003880e40e0042d400c100c070aaa990014016008441160781c2c160b01e16500081142081900206c1c1d1104e90605c40d4074103260300e5075181e040e15040c1d08040d00140c6002d014209041c0382422081c40c3d61200d00d04295818011280840d880c0031010803a141d8040000004001c90340b00c40e5107541c001c04501284d14100125 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 433741843 1250 433740593 433740661
    0x602031512060a2c01023601080603030715021c11040302090601050c0109030914041506050f04210b070207080c0126130302190314030603011503061506080c03 70
    0x84954107131384001200050b04e815404403454410000944040c2d000c8901305c20b00c0500110f9215048882ea00030300c0c00c1006501e542d00482e10b140a0600c00400c802160500c0c01d1003036071a68080c0c69a001009443d0301810030f500c400030222031981c3c0d188a0948001c104c24005800c002144a410000c180b5180f4500444480c0399400c45030b44440031400101203000c10001c900c01d503070020036a400c00b25001c111071404d5040d0500410002d1140e142440004500d803024042d0740016607000b003510b60582d1155140314044003c1ca00e182c40d0003202c24a901c0e00108816500c0060341030143d074a010020551549003070010342c0c1c407051002c071400b0800340307258000d000c03846903190460044007101c0718403202c4401e900d40a4104031f0034101c80d507140b104c1704030580003080e40400946070155170141090349e03e480e10400300c1d0142030040d800b10310902c50310800008000d116440514082c50178000c001c0090303100c00d812a0808000c2c3d644500480050020912040199400410303808041048840c2024 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 433743093 1250 433741843 433741901
    0x80a0c02060d02030f010b0c2e09110321030406020d0207140114090f03041403120a0903031103070b01180e010c0509040f0e1c050f04030602031512060a 67
    0x2102e0948600b003990044140000d8100901c8868050130410b01c00d2401c2484540d4101d03583c001160408180030600031000028071a540390150013400b5250003400030031304a040c009441000c01d08071174041c1c41a105800b40c2e0100380414280102d4062030064916180c4c0d0b107a00029400ca9007510711200c1d403c01640c0001118013460303d02d480c1d20103001003031094101401820681c0c0040c15034071141c0091b02d00102913003011080b039040d21100001c221407480e441c40480e184c040041524001400001110040140c103c803120003113a01c03958841210224402a15440c0c1c0503140d001410100c0100c010f202c07a150040324030036031a4440b2030001e101040c49520a00b03455800c0078540c04110001340f85526810140076000c5403031501401444014041007650307070754420b05194401c122181034466880d051068080714130440f06200f803903840725100d08144009600540e003080041c403d144030880b840c02c1c02c1203110800000300010304844d40d01c50f185c0202a03c02185100360980310a221071800203 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 433744343 1250 433743093 433743097
    0x40515010e0406050708060922120201051603152102130b1306050d0f24060609080607020d11070e011e061e0f0504051201090308010b070b0103080a0c0206 68
    0x5080740c00c4882420982010011508090420400c10140d04100f2003a40c98801c0d130707a0f030421108858203810300d4a03044912100b55407214020500252545400300d143e905411460180d1103204102c800495618825002ca51088118440b0030402c03c0341049a50b000740c1110000c0b1b03007a00b554800c4c0d01040d500144820b484a103080158039030743c0080320b146082c60035110a6141e0301d040200001c50802c00000c40e1005c1c8001c3c002c000c00320040d40001040b11400c070b05100c000a000003e035400f034140c84002e01502c518090840083c24800c800a401240003551a0141c1d80640140001c010342090494869000641410080c1300319040003907034042c80010701c0d00a1072842d43c5248580018500e0400c0720300d0507030104080040c10120b4103070412007102c1070403103900d050800c407988081d01a010b03580f42c02190321080d40940c100c10f015950740da041d040102c210f07202c3d645100050781c840345141c881b03015854000d0026903001005100155135036000f800011103038242a41801c00319030008140e5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 433745593 1250 433744343 433744349
    0xa170d021c0c0801051c020f0f09010303020606130603120806010e0d0b1803031b03040507090612170301080a021e0a180e01060515162a0504060b040e04051501 70
    0x41542e42058034485540b0402c0c2602400742241c9040c04121954610300e111440c866010388507031a000407898580e900c405403880001400790090400e90f9417410040e450b1a02150480d004402c0c000e20014091518071903e402c0d41d90080580000c0080c11204484480303004040301d0501211042900660f501c0840c0034841d644100b103e100c02e0324181c102e10100020074a0100c40c242d00034400c1c04600740c1141d0714107002440c000c80554481c3d6450400b58a41202688079201f2075103040c40c00704895009114015a40740200126070a00710600508542444244100a41600480c1800c1c0061402c0803030303518403590b0328441c11646100748001440039443c2d07600081d4821109118050100b4040c0a2260318400c144020041c407490a0045801c8110200c90409000c0c80020150031402c54000710380b0320302d07410070580321300e48020001c80305010a024600048000141034005070320f2605000c0c1c04c082c0e864440303286040c50724251102156100c0903008440c2d500a00c0d8101f08810300800c009802 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 433746843 1250 433745593 433745647
    0x30915151701020a0e0303040302010507030c0c0302130e0606010e1012091401200c030a110a050106031101090503010b1003111b070603050606071109061203130e01080a170d02 77
    0x25030901d1310405010f43d01441c0301d4600030703001401302304007503a001010381d800b003a0581041d1002c00c210340350101080801d0b802c000c2d07110120303c00d09410f0040740d501212034518414116103440d180c05005503913141900c1e240ba5445540381904004040c418804444282115040440c4020099588a910545448081321169500c1622a20340c2d0062000100804e034440314040c548803241d042c4c81d0701ca206a124803001d2014041c00390228400030400480d0264210008120494030391900c0343c0c1d0384990415481c002496494040f07514a41840b8080c003600d401004562039600340c42c0e0a40c0031341086c3c3c61190007034a0900920303c01901016402c450071045034054a1614144032001e030071104054046401684207010b2030000070a040b66856007400212816260340d0340b02d2001900304806002c1c04a1ba6000104080146404030007001040e40d485044440090b030704d8002e03459880140c1c000103060f0059055580021034990030007400030060600300075103005580c101c040d26001d0b9080501d44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 433748093 1250 433746843 433746847
    0x241003021c0e0c010903051002070c1e090633180f05010207171932010c0203090117061906020a170408070902030a0906090c0f0603091515170102 64
    0xb29424144a0a0621202403c00807905070840d110aaaa20490100d0440c510b5002900c0420b00c031100c40807c0042151004450402107200c00c1c880150340e181c07190340107450810320007007058498182e4038018040f4034180310b09030050004868444d08550342040080c00f4211607003c00000000b1001006455031030b404201080c40c00000910745440d07a4054014601c888c210000301d100e002c140c0141440c004060300113003a481703003042e641181902544007003411105079283c0440c6203203040351800950700320007040a0b1710314000a07608c922420790454002190348090410010380c250b140c98005002514200413210300e0300d240c4400b804503810400250380030b42c1c0000200441240005c400c001c0d40d2100c1410b051034105010380d50f00c02402003400042d004030028110481962149a9258001c1070a1052629604141715400c0507801004155282d0b01c80200f1054064041c06030340d00e501c4400c0180034074021007580010b044864004241c071403e071000041d2030201d0030f0400c1c8001d18040c0016 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 433749343 1250 433748093 433748111
    0xf0f0717070804080f010207031e1707020c0414060109030f051002030a0f0e07060912050f010c031e020f0702100e0d050706020114010b03010317070606030f0605241003021c 76
    0x40c03a017041c190707260300c0b143e004121003000240d010541c500c0407241034626450f1404540c3c0d068540660030301a01080301155070030803003040e900060f1410f8411090301d04120612006040c03c0080c0c00848929000c11a046c1041000585001e0b008030b06601450039151400358440810007a0307030003a911501019121200784085000d00e05c100c02c44d150b03054005188951404001601c042060710425010f28503c02045080c440180f10019120700c18078000c010410b20850007800800040c2288110081c0e2100c09032801c16a6100710380e26954940b40303550810b1030350350820003d4842411010200101021520702686420662680b0300d8461000b4100746402d0010003030844200e4000c841031000130382c00402c2500c80da442102d05681d007068240080781e80c4222042c0035132240c0c40c0001c0181c0e141c07440010031f00c01c041580c4009940724050074080b40d1a884481c4051000044116500c491480b103065694601070402c0c00d90980c1034200981056031956509041d00084921102d4180d204c00c0f0700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 433750593 1250 433749343 433749359
    0x30305040e0a0507080406021b06091509061003020d020105070203062e060c06050901090b070203070303140606090405190f020c01050117030315061c0e10020f0f0717070804 76
    0x1c20342c0000d01a9040169180c1004001c03c1910040c0010303250643c005106940e012880448030398100c400b4040311a00d080ca0106160b54040f202c01c03c101111100c404141031850105540b0b020702280d411640c64582150204504004100c1c0200d050240c01c00442c001610240040e500c5203024100044429952000c040d000d0704240b801d113030075060358060a018941d01705a000c01403a400c9000050700382d0b44e1000c2180100000100903080c4401c00040040e500c0e400402000c0c081c1c82a5414082911140200d12801009568990740814203000d100c209003029442558030142c031030901e58280c0ea4000030003003210f03640000c02c03c2c0d4540000301401221000d00078103004004c2c9002004680e04000384d650b07120300015103190b42c0a982d160400b000350741d42c00144c5107901c1054100401911310800c0e104010841c4900c004058028458a8205140144240e0300844000c4081c1c6107070815101404d146540511421100d40d070407503000c0003c000081010b4a4201e10410031165103500b8072440c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 433751843 1250 433750593 433750619
    0x160606062c060d0b0604030f050325020d0f0c0e100e010e0403080105130b130204060f0c0b0c0c0a060906090b0a0b060f07110405160e0d0c06110a05030403030504 71
    0x4001004001140701400c0d070380b02d2038100c1d4401201c501001074075135119000129244556800600341c01c20200f048810711102000401001c2c80300b2040003140c541c0503c16981010844402a500c0248a054800800e10170100380c0301c03881c4560080c0c580701d51140c0649100c610140ca8003032100d04111000d00c808400310b000d06003d00b124203540b9100e0b00d0103030380060003a1414000c8601a0980030b08444050b100ea4102103802e8034010000d4100a49061492009410a20030403000540c54140c800aa0303000b080e02100c1a45c0003a030340034503030b50307120804070281d40220b40780301d144d10411844c800440c00b035205114403113100c5d05010419442a04014041010282451580314908107030211660381c0c0c58200c40d540ba020000094483c2c0e410b060201c00420081900d94001d070901c4e0810400302890400038064112a4031a0350529049509100300009007900003000502d09044c148040b40c000d4942440844842046490714903903030380d44c41c0c2590482c0e4011400b0880102c0c00b4003883c411700c01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 433753093 1250 433751843 433751897
    0x5121017150103081b030406081506090d020405100503060405061b0c070510120513060f020a12090c080304060203030702192001050412080423031216060606 69
    0x80100001d40070710076441d10303900e4180710042004000054424402d001c04a840c03244020711020340340c8036030341c0f0321b4040d00401d004c84990301044490040c0c03080710300d403085c16114000340c05440041d0020300b91b424400244400b4081102e445120f8000087d1541c0030802544194031802c050300150409006034007440c0f88402d2506080001030081d00304c84034002903030f44125a41241c440c00c00140400c4152a62141032104842280c1004100910228944135074128544107c00400820030750740c4900080b405201258000141071030b04030580300d44540c00404060307000740d203210707016036a03a40c03101d1441d4007a620000250300080100b24500e901884881d9050b40c4091035a002d4094650300c8031135840b00c10400341d4582c500b04034440d446034030450980c0c020b400c2c0c491442c17001b09818149100a0b402034856880c0159460f020329844050018541100c480041c2c010b02d1246135802455415400a03130410425040c180e40d03501c04160305010f18001803c5584407550303040e1103803000d25001c0620032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 433754343 1250 433753093 433753139
    0xe0328090302010206190b0d03020309120c0607021306210308010501051315020f16080c04180209090a1505010602150f0c0d02090306010602010212090708030d020307051210 76
    0x64080000d0f03600891101c0d80141c94400751414100e01700c480c4030041518580c046c0d0400744440c11101059000001060391203001c0341c028032080c01c1d00c414503950301d01071045141c00401c2401030b0001424200c000d20701240c0c14500c0400c0040d20344560041440c40d914180180c02e440b4a4460706040d004046203015000a10f082807a0202454007007802199070710a114001c00520290b040c01c52080c0801c4c00302410800940305018094500050040118080e4048a020300c01541e00289010722402121603552044202000029000c00c42103800003014403c0c203001c0d4181c617000090003560b122050203200c040c009001d5040ca01d00a00c0d18807445400c1900f100000c0902c000350712409602ca610044e41200d040c3e6032000120508044d00502c555590103100d401c00110746640c042d000780041d908860130843e155512071406070f555810501c40d50006410800028001c0d81950700250b45c86400c600b801c51414088240e0310b80500e03400c550041c002011400b040c450301010701c140c6000380c4002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 433755593 1250 433754343 433754357
    0x5091513020a0e06090f0a080d0e120a08031905040c2102010e19090e07080c180c1303051c0809010b0109140102210c070909051009060e0328 62
    0xb00d0301801d003183e40070280e4480e080c080b411039030b2581c4419040c03000402c041e01e08044aa61803107450b50f20040d007910031012520000100c241c0e4104540c5c18140108204000c101200541e2a00300c0300780c4c40139045d0100701c402400c2d80d040540d03982c02810b00461003040d07410319092401e00300726090b83d201581c03c1c2c0d501082e0a041d00c0540c0e8009001d041c02074045a140905000ca0505c428201c511a4071100400d07003030000d08025070102060318422100260142c07840d5900749020095684001940b00e0b07804034019011800a02545e0050074088429491540d03130343d80c584e100c0904d0420004450080c840340d66008444090b0301505a94200f074827039000344051990200003804821113409500d8a8400050804945a1080002003941d01150360384e40c00c05e04400407228030130fa121025041075403041c044002000301031807280000264000020b49080c2c0d501e842100081c09006406881c40c1c0c1d1203161283c1c4210b401d200030b1204440d843d441180d43c00d5944405400c0f02c280c180050207018403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 433756843 1250 433755593 433755607
    0x50607090b030f10050d0f02030d0203090105030a020901031e150e0c0f090622080f03041409060409020a0f0609050603040210080a0f0c0c02120f0706030c090509151302 74
    0xc100070350350000030901200c9484d40e1a02880402da007015404903600030364605103003007440b1141c44081d140500035420307600c0611008034141e943c1d100c2d40c1c0c0c500340059400c00c002840f00c43e56502400481c001458080381b0360740c04040c0210380145545207000f24954515184049403220294140104440c1051420354a00082c030f0348034902400411000f424400601c0e03550559036601190a4481c00788401d4001201d041071130b00300001030b40980c04035072107101c241d100398490000c180c40c00c48414204c00251003c80c00140b010503100608041d820a0325580340c24010f81d520004003014001500c0c510407040e2602100400042e020361085014180400c144009030316178040b49140030803941440c480f1500c0c0c01d8915401001ca020030340e1102031034074061402e280e52007200752101600803150035281ca03200b000707e02d8a45054681e40070a0782d10900e020416503019812003080003403e402c241441940c0e40c80410300c1a0021030300440b05042c0402904100e00e08030b1040c01b800a0804821400c2c100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 433758093 1250 433756843 433756859
    0x3120e09010f12030302071713120503041505090a0803090f01030612290123030d0206040210021002040905010f0e04030507150603140c011d06030414070e0c040305060709 75
    0x9250f02070710014000500c40c241c2814003d804544000d0351001c0d100340b0004e03901305450280c0c1c1040d500c08180f103408800004108000d14203505034a0782080280d841c103441d150740e41c0c90184114040d503041c024103208101ca55a0b9041c070300b40080400070055130b41d5000402c03c03c05480800350f03815050602d81709042c0003501d5080c24424045070310004003171589d031110150346820001c8040407040842c145001052100399000c0310b00c007822042c4030100d0301d0700d00201096202c1100100420041e44000001005031903c0f01c11100d4100403401030301d490b275400810000a0703030b119802030700045446e4001000005034500c811402485903161900c564101990010070900c00e100d0082c0c200714403840084100c6280e9800300c130085500404452043c11010002e036113030b8401108090216106d088501102c550f40785010450134801020149140c1e01c90707031510550720f0a590103249a20034000e000c5400c0724480000d1340600065414191514514a010b03450300100030034040070880c08000402100c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 433759343 1250 433758093 433758119
    0x10615020f0a06050c04030c03111804020303072d0609110a0b18180403030c0e03010510050402030a09020301050f040506010b1603030e0c030105100e0a050601020607080414060103120e0901 83
    0x5580040007294517100c003100c05025000d00d41001e4045880300600208000080509070702a000540340c000c920380303c0e410041c8200400326000303134058100b0444000080d030202d1f14a51154111817550249a800708a00d8500450001c01168100e542d80c5080081c071050383c00c03800e4601022901600708900340070080300d8074010281d14a03010b43c2828103141e055070310704620a121400500c0a801a458103090050145c0003011400b8045041079020400608042c044d4500c542401440701e01007074076210502c0001d600090200311004d5071180d41c00d00580e001e0282c103000752280641d407070040c02d00d410a40d041c540107a20050704602c08100e4801211000000c0481880c0c15040002e11f447c00d401e803040c00c1180e03c10f083c1d585546050100105130206e8586d040030b0b1110402903884a075100c0c641541140c0f030558402d409a03200c0700000d0040d9200e008056413052240c80442052501040e40e03502e4200d00b0703001210b440242c800b808102a510080c3e000003417404942da2145540f4005d0191004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 433760593 1250 433759343 433759363
    0x306061011070527151c06020708070b040201020d0e0a0b090102030706060f08010f021804020c0f1f0507020604171e041401030e06010e010b0703091502010615020f 72
    0x100818100004074101c040c040c050082c00090044070444104400e0825024a0b0700c1c03041882c4a44100810300301080c10b040008080005411610b000c00500c89926801c48000800c43e216a001c0103101c00103000117003c0e168641c420b28402d0703c94202440064101410410301e0360030490881101081959881500c40480320100c10590b034400d0b048004070304500c01c2c5c0754060801030034407800291452881800341c3c206d5081c0c5008000b0040da9060180607031003501e00280c1981c032980100000e0385800d50083c2030015101048440c3c2a05911055040c00880c2c231031200660741054458464200b1400b40c903600c00303a00d2015100030318107a40c40c2000382080702d4442c892041c000c665103980150800c1d40c480e9400401203010b468036a100100488a0301a4810a002070b0401241803555000020000d0607244101441c00a5030f0804603148101c4d000550203500b0840449400589007030410108441c200f1951b002040840c105402c4100c0c18450219407001c650007000083c014001c04a0078000c0c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 433761843 1250 433760593 433760597
    0x507050105071a09060402030601052e09170d0339111609110f0f0a020a0f0b15100c020f041d100b060403020109152d090503060610 58
    0x242c114500f01140a15000c414030003010b800d010610180f9a00045e01510070340c42102117810f26031700c0d002404881b0843d42c060124001e4808944680710110181201d1196010300c1c0c04d40d0056502c030810900724828860751144c47d0031a03040b504d50260f00d806906582c140c400c061180c501c0342c265402000741034501210020719005c00189182521a02c204110b02800c101112140104007a407040660340710310520b0318941ca0301e280210000806003e0b1100c0700e00701109641007010042c0070703022a03408001084114048d21074030000064400282d845254080c55100800740b4060b0074070707001d40e4102c0c00700f07501c6181801901056140e000c411815100d5050394101600340c402070115010b070540101081c40c031aa045942c030441000012400120040d105041c400038802c0c0061146501c600c3c08013131300003240f000b000e100c3c04020342c80e0152400700c186084078030301580484040d0840007983c005400d1900050354501c00c0c44d40721060744083e01c401c801500c003904040000503c041892103c10302 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 433763093 1250 433761843 433761847
    0x103020703120e01020a08091c0c0f05010f0902120a1e0507050d0302010e1603233d05010b180d050f060109050705030402012c03100b090705070507050105 68
    0x400c2621511001804200040b0148030402c440b20046020f50440700d0034000007001400010028140024603028a4006000c115410204020b0440d00f41050f1481964045203081610002803030901c103a81c84000c0300c940004400c100b910422a89110076030f510082d544c4030317402140220f105d088200e0802203004560a10803090381c45c000d818a6640d610455001c000282200e0a150b019085002c5091011056443d001261000c080e090034081c00003800c40b80d11001000b03103003c41424194003840a00c0d045504044030110000401c24a10300105102510300040c0c64030952848004000521140402e0060303605280001800740190352881704285605691403400342c0390034228014907900001615049040c0741a440e9031001c00f071045c0601e491070000003030402071050003580d000b0f40e41603481d40c10b060800e01c501c11070721012100c1042c820f007046c151501e070350380c04008190396140380c40741c081150282201001000071004107070780c0901000300201c800080000c103184040e61002d00b8007603 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 433764343 1250 433763093 433763107
    0x207090510030f080306010305010e090c0603060604030203011e0e010209090a0c0504030b07091401110604120905330304030504060c1104020705061005030c0d0b180304030c0f091109010302 83
    0x280307014040364070241410045101007800d2005120040d80310300c20a0700c092211b640e8959900100031011601564a900190101005450040015504481d00501507401c05841e90006421a01c0244a4640303031300c2c0032040000c4c100b41600954000401c020000c43c10254800041040e000b00100140085075965a0300200b807401041545c02441e00000010103e10300001d002c1d084c1c01440c0130f0020001c201083d00d00483d0b118100e04103010002901405803034072a42d440e0714004480500c2e40040c000760345c070003281c15180c50001c00005482c44210000c10081d4000c2d4038000c1c04075441540300214104100401710f138105046074200d172841c1c075001162182a04048020a405014482c0d025000084c6102030107400030741240251101c1719200b0308503540d002099551013034500340540201c1c0c2c041c4240040b40b204441d00d0340c41031003640c0c1c00c0c80321044428018211b6100b0340003140d207074000c010140075680600300cac4240a8045d1400c100b01c4944152100041d82c00ba0f11000760415400260381 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 433765593 1250 433764343 433764361
    0x102270d080f12010e1e070905061e1c050f010f18020f28230d020409051003030212030603120c0102070507180b0414041e05060a05160c0302070905 65
    0x3c50807040c0c0c1c00704070450740d40c46911321402c500d0183c0300032442d80701411001c00d014031080292806009540c842c1203d0900d06002d024158101000030030b4201e0260302d44060600300d44000b055000107001c060b00c0c19441d029166012114043c0190220f18940c42c0140489005403d801c0241c45041d480503010b0b000b5520810040e01c80c20040000c0d0746400300b00501107080d002c4401041c040243c24124402c9000c070300c11242c04265a15261742500b01005145180058a0040003440300d07403c0054500307600c481c01d8005035081616180b4805c41000d07010010301d58117005070100342144000e62499428034800003030750f50b0ba03681c414400ac000c000484020908003541111506940001550201640e500d0f030f0344520000200910015414441091042e00d400e10403d07802e02c540d580003d9007500c0d140c840c0210560311540e02407003110196a00c4010850410205124240c0450040350782d1404510a014144007210b540061103a41450701c00081d40115212080d54400703140050030b82d50b9074002c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 433766843 1250 433765593 433765597
    0x1111b011413030f020a0b0909041b0504060b03040218040b04020405150d060c0e1005040e1509100906060c021014210108060702070305150402061b0102270d080f 71
    0x3a54480301600c2d2000001c111615544c0c80c64a17000b00e0f449609a5135480f09a4454817415180d940d020302c171000060002031028888403041c0b000030b0340c0b02c001d4640f9a070116040380c00c107400680140c034020003004118504042d1190984101c56a1420b05003041d80d54212030344c0010744024821a11080051159040c0505541c0d016030020310200c600406424514020110b20307500d00002064490710b640603080c0349000a9200309207981c4d0529180c500780c1c0a95a07010080c1c44c20400d000d40541480303140ea1104405e03801002d180d4042d0340c0852500d50103008035841030340403078184114a040d010150b0b8070640341e200031200c0350410b10110340303d4480d0366240c0d20035115204446500c1c2000400241c00c10900c2c203050301c110b1030894a60391a4808240ea440d50f480c480180710381c1c01294545501d0b2410200d03260094409000541000748000760101314001460240c140c030380d400b050785929030501050400345a441c2c000c040c5071f40078114010030010f210140000c5c090000c005a01040c110401c07003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 433768093 1250 433766843 433766857
    0x216080d0b0621090105010609050d05070909030906030c020a020d0605040f0506090a0b1b0a050a02120711030d111036020118060509010e0f0a1401111b0114 69
    0x22195a55140e040e40f1188a0800000c8400c0342070304000980115814803440e81621b0303060f224180414545001c01600852107c800c40e030a025070071000a20441e28041c00d6200c3d84030380c541503812400d1920060440b801d9003118001c5500220301c807000b41e121780680c04000343e0040000305881e82e55081c8042d1000041c10018218030520003000706059005c1040f10401c0d21a08603401d040c0c94210303d84585075280c0100c2d1030100010011545c51500600003410007902500543c0c40400c03401501d08aa40c00c9840c0c10f852200b4010040312507441d0030321822440880500380104620404046180d4a0302143d40c2907403541e40d02c800c2441e24080b90780d074100036120100c4030800c0704942e0380c0e4110300e1403481c48000c0f40801c40c0300d1001180740e0f41514030315080c1c44165032403600700f1a00c1d60044034400080f21285811441e015000d81040e04ca01150f0b10103440c50301810b4a07032782e008800050094001c500030746c1143c1c0007010a020b50701007107104082c000400f40380200c41c004c003848030f2a50500c80d4030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 433769343 1250 433768093 433768099
    0x1006050a021f1e020c030a03020c121207080a0203090d0f2102070b0c0a0225030602030f010611070b09060703110d090929090405010f021305130216080d0b 68
    0xa00a1202905590405103240c0000283c0300701c3d0844608080e4240c0c0900d502485842d00180302d000d00052003540544520b112500444c0c4051828130300115940c0d0000003840400800102000101a0000d8229800908014003185146040b2480680b0352149621000c1040010140303d601c05101e004d500010900742c2c000960f041c1c0d5006885030007075201ca4800c0b1540060355000516034100d00050b02c005504d150050001c07840c0c6020341c13048002030400b02d40383d2040c19000c04030120701144003461040e140c1701a48101c950425a010342500c0218071114003036485a0001d00c017580600e02500c03070701c02082d5500c0741c03038000e1803405442e65450881300302c407288564580c182950382e01140c02ea045540c0c00404011400942d501003411002c4400300d445a401112140b29040c18800716003035229014134000201ea61004c0a140140e9002203e10301118401c1c05c400c1c0600d00c0c06410f0f4a00c08604244118680041241e400c0100056020080c1c021000462000c03040b4a15801c034202c142001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 433770593 1250 433769343 433769383
    0x903030a020a020a06020a153b06060a05010c060506061624140f15120c010806030601140105070c031725020f22060b030103050d02061006050a02 64
    0xc0e4000075a9580810340c183c0c816008410000340390780c000309094a20340e40000009a00d0640300c043c00020f0301074044160b165800c41da182c00c60010441d0003c0c402c2d041d10213560065401c892410b6403405501400030303485940507200401c0140c0c0c00020705458142e000302c0108141d178035240061151301811200754940030081180b0303030030410250700381d002c05980b01c01e031221155013144241c3d00304c0c1d480c6189a4448500c0b2404217100003c111200d0381c0c8208211244820b981c808400309001200c03500c5800400d03884039000070719541e04032100b16800b8809400034400c41d0b1518811609144c01c03a80c20340c1c14004000740341400e0120180108000d1038110038013020645040f51020741c1c030b500c50842000e0b105403e06e50390102c9002c04094035001d03a0000c01a1840107080c5c0e080284150b2400c281803401e0b0446520080701e00946c2c0200001800c3d902c40b0276491b9890b5081c030b5410200040155803c5400c58820024610103100d4400d081d035180340b405607250300c8005400c0c4d181907400c4520300c04400807 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 433771843 1250 433770593 433770607
    0x10b04331a07030809030c0a0303090510110c0c0618040b0a0e04080306010801060c11010302030604090506130311070e22051b030c0105090906040203060301090b0103140c1c02010c0602090303 84
    0x164000601d505803281e904c513811030340ca200b0320329242d004581c411190307500040c96200c08648a0340010103054042c0040d9484070f210001d803401102d00e84100310b40780720700c0818262500b000030702041500c43d6060300e101d864043c00700815041c0c4010343ca0054811661901c101000c0d45031a114240600f180088112050400b8181000c0c135400440325540010110000401d030b19125008264240da4440c0c1042081030024005501a4000408803500310703130340300001c0002c50b000304034542c09030410f1280180242c5640c20010910945049103148650000d4420040040a549025481655107142c00e10f0350094860000f1081e00e00c80001d0301c00d1040800441c0101c0c54000200341c5248110304560000c1036040041d1054083e040d01c9503840302078480001c0c05070805d50000c583c8408000d00001d030401c00380e5145c0582080c00c0c1c00556030404c01c468641e5648108000010180604440c0f00840c425085051210440c044000a04101006602800304000d58043e5040300400509403515414 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 433773093 1250 433771843 433771889
    0x708070b06031606050714011512110a05060304060f15030b090709050c0f300f0604060308040312030905011d0111030c16080426010b0433 61
    0x1000703440c40c078030038003d45614854090702c0c15012003c49540780c40b034904040e4203031184401003a05440005d495525641d109402251036500340e005840005003680300b42c2c8007400d0040540610030b500030f02a0118800a00c0030381d4901c0c0a40e039000d50700c07040100e100c40d041d00c00c8601402218401d61141542120007104203c856001c661141c01d5040444070056a65586c0e003056410645030451544000c014807017280304070300000c00403184140d2600440040c40c02d400340d1244e050304003e1003100510000e00c40c082800940301c0f90041e504540521900d4119110318240340f10358400280300c0d0b15800b0521170194000c0d0019840c0c2900007000300190084044140d112060b11141c0c2c04455113000d101003680800307541a24010f45540078128181035502c006200c032900344030001e490314441480001081110704102083c9001098070611616081c0c549050031340e03401d004030610071070800381044440c9281d60031100200d0469038000c1c02d82a0744071001900c80402c0d82100441d000c4030380450404203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 433774343 1250 433773093 433773113
    0x120f091e01030c0f050423030303070f141305010528030204080f16031704030804180b030a050607081e1501020c010903050c0904060f0915110906070602030c070807 72
    0x10600ba01e0a20404444400032a0108410400300c801300d0b506020500400c40600c9101d8640c14507140103902d01024500003e01d90f40080399101d0001d405c01e40b91204040e440004010041084c098103403d12800510084407002c40c4c0c0a040d04000020800e1101d07030390061b400d000c01c400c0034903605501001038403004010b94020700803003007248614441c9a403441e10001d0689004249910b0884155007195960401c01141000b80010b204007400040081810a0020001059220000045502c8659411003600c0010362101c2c800d0b003222440c400030403008660160320116600d4502200d0303945900001c0785102032000018502c01c01c5042040f0400fa98041610003007098003220940c030b03441001180d141d419408000d0003a00400c203503003543d0400780c4405030410310401000c500c000304001d5203c00c40f032143d4002d40350450030501d20f0404010501c611801c00d1081485031f4603004141d8003186051040110040050307500000203902d071003103001038661982e40312006503030b41c01c90350402143c40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 433775593 1250 433774343 433774399
    0x30f0309030209010b0f030c070317011202090f09030313020a08161805010303120b0418050307151505010c0f02040501061205011d040809120304080a0b0f09120f09 72
    0x782000c1c0f030002c00c81d20703101c00a480c6046220011a413450740d929158441640082000b20240500740201d28104030691040d580030701400038240712072600c035004002043e08003030884100c0f280700005200e02d4610100440e40c3c0011141c5150324040b10520100d26411055440942940500800d4503034248103a42000b00320341c0300b84904030b030080d604c90304041216002c2c4002004182d2500040003091615003110804035001440050420481540d9240d5604015800c8031141c20001d0300c0010000c101e17080c44c1d418848500e00b00003007103a4101c1036104220301d020b40d60600043e507155204124102401c149102d40c06042400710356590440a00007620580b08100701754101800451413038503c1c00c10f0070340e460180c04490213603181e0b0703200d00e861944110291368002055074481a80a041080144014081000100b4641c007640c20000e4000c200a81980f10646113102448212240000c1c40c3c05101c48400c4016584c00b10801c2002003031052800040d001088110421051803c1c81401d582d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 433776843 1250 433775593 433775599
    0x6090f061706040320060c0403021002010501060f0e030a1407150804020f010809010e0a12020f0c1f021e031305030118060209060903010203040b040c050303030106120c09030f03090302 81
    0x1aa80360301076180840412409400e190380800000341c04a0311504005100708600c00c3c884c3c4043e80c415161504052040790030480315070380090300b0011818006003405520310240700030809075041c11001040d01101455a0041026400801300d283d54240030780c8155541c821181482c1c400c60301da819482c1c0f480e07031080701150000101d22f0003005010389501803080754000c01a101c03459154006590340300703010b01036010740d44d6141824040701d20200041c0311502d000300ca51a0a40c030741c4402c0285081c0490243c180c1c690004a03e0f08207980b20b581204150508030608ad0301c0588055000301c1c034000c03c02c100c1c00344d1441400b403200e600030404001001c2d01320b01108200c03090384d260400e1600b6622500d90800b03d921070305840c039000c03414607800340c480d4110040905117031884c20700020342641c0056409848402010052204110140103604000c02054000d0360a540c90080301400348611130485048007038844400b5a00c03507216040660296a01c544814914400c2e070078000c10343c003454002280 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 433778093 1250 433776843 433776851
    0x140f1917070302060604020a05160b190204050307050d02030102190f0f110c04090203010230010509040f031206170312280213050405040b040618110409020d0606090f 73
    0x24812000201e80e100758040d0010a510b4440c902031000a52120b000c034000c2080c01e00130320065107100250110181e001d070f50060402c3c00c1040101d0306110010085413491403040000300010f03207010501c00d04035141240c004032a00d00a00100e40a03120b0244003850003071054615952158010501a451194940c2e0f019801b031740e80141a0b0b40d40c1101d40c1080e281c0d0384010810002d0f40b40a42201241910280002d801c11442000d128420208000c00c1c400010001c505582500e50703040cac56500500d0f0848c1c1c00740701424507450b8103900d444424800380c10440528008001904a600454001c000d54546142c0301100142c2440e02d0740c0102030540c411130550b0002c20300407040f66820480f66003a40c460140700000040c2e8410081d8011100c07030000400c2150001402da8681c0720b0540314900681518a491410f03103003aa0440f40f070410910740c450328848244012900c40b4000c0d0001600035500020640140e00000782c88450005000f00359a05014001c245910640c10040c42c03480100010300c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 433779343 1250 433778093 433778123
    0x30504090c0e0a0b16080316030e070b030601110309060d0f0c0c0b1f080f010e0d050301030b0f040807020405242706060c030a050909010504021204140f19 68
    0x11100c41000500641c0000e0548013402002050b5009245d44100814841904880c9644902d2290030880303140e041d142192034804031a81c2c050040502d544081400780149034140600207075036002c06400a810040100004004400100121481c03400e00401050b2034607501ca940d40d010341816034806000310b08000408440d40d0041c0080c0c1c05055100410320701d07a03520f41001e4609004210440d6801440c85000000c0b07002040c070103c0302d81c0b00360900118181c2540303000c50b843c1450081280007040810001040803c580201c4190482005459000c81c3e46803030415000754061890701a60081c0b500c0280010401741c0828101c2029003080000038060300c4504020001e0540003414001c0310380c2e01140300c20011841c4a0a40c42000100042e0030001d038103440034517503084121503a0104178001207503943c901e408150315006001c01c45065260500665a00c404407102400003050f03035a82c0c00304075642890501140c00d246800300110b07100111549076a18044854010940d1441e842c0a40740c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 433780593 1250 433779343 433779347
    0x5010b210907050609041d070f1a030105010e0d06051018090201050904090c0f0e0f010e16080a1e0605040515030303150d02130b01020f0115090b060904020304030504090c 75
    0x5944075040c0c21000d07129662505003409200d500c800d00181c0e01c1070f5642c0140790000c2200148042c400c00f081c0c0140600c034100001d0720703c4000ca13030300200002e0f901d459100400f0328500c800c40e4152002881c01c2c2e8100300300500410300c00400741c40c0c0100842c0c181001c0200c45070558200404a4104441c40c1512200c41c51400d4100c0301309900280c00500100f0104030399040940240c4491481100c5424109a48896040b40d6441c030380c0054001c801c20704103000245030510380d0070b0b024080c0010f95030201d04041e40d0b41008080c92002080a00008d90002100040142c2c00003840d0103641d02c0c006001d42d02c4d108100c005008a0003031074417803403030500843c60615407490105082d900182c0214510f440f4552805a200c40d50351815900c45948100a4016101c4e80801d00d030041039014007196100600c1e00281c2807941e0600c10701c40d940e15000344400081100d001c0340086880d80310380001c0611458001c45c00070701c41c42c90701507081400041488201030748040200100c0f81040c03000c0002401040c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 433781843 1250 433780593 433780657
    0x306050402030c1602030c0306070807091a030a1a150c25050d08090411030402100c02011d060c0a0506010e150d030806041b18120c090203130605010b 66
    0x3c21a46040705101041202d20084411681c0c640010100d660124404000901e1700c40d003201d000c40024485001c2c4003d480e0008403084c0505255418419852a05840c3c220345000040140d02d5075511105541d072420303105a5408a440005045400d000a0854800080d071340261003d10f03007441545064a4100c000c20421040002a580710034907503498041003160419032000e00366001d14040045901a503654811003200002c1700b085141c0341d2a08ac010000070914610703054040c8903041c298030340142c0e0b00081141ca2150700340b00606400a8000110b2030b60302910a01750282d00c11036068505004000520604071144000d080042d55604041040e00d200085980713030300030080201583c0003c1c01040b80b04c1d0b1000b400703071002034898091140041c406251810080203d00d035071129000c1e02507007204001c080c01a82d00b01a0f068400795a0b5844c03000484d01c41c1d14195503002c004180b894444000e01c004154005d407091011356114118280703d5404952100100c1c80d100c20070300340781161400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 433783093 1250 433781843 433781851
    0x5030619050616020a0825080a031e032705010608031606020904091a01030c4103030d06080c040605012c04140610050415230f070201030605040203 65
    0x9120f080c800303002843c403c24546008102c0e17000d5411500420210320402208021001107000020000c4c648500d00c0d410700b05c1600702c00d159401802000011941201d9951844030540003500038400302c14800710700410009280c80c1008141000c0c440200c10200d0b0189003060290000300300c40c580d2082455a00d108110028054070094610078011940c198003802109001500110301000180d890030301d407208046600740503404c0340300144140800300a02502800709201a4401c0c80c03003016010703180c9802e042008048002103040707000710ac684504403032810000901200d4076440c0c0c220303020001d17141c640241442485100c2080aa9207440c2c040c040c126041a118140380071580c4426595080103e4100c0d852428095002c1c155501d5601c00c0d140031400e403544032001401c1c42c13001c20101210101c40d600401100348030600034203400c0c20502800c0415804e00e2640e459802011505244548490240303084000c1400710f100392500b0002d0008610036079041101946600c1080202d000603a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 433784343 1250 433783093 433783099
    0x1b08040b1315360303110301050d020d0203190803070e03070f060302090a080d030603030806121207050c0406090519051b0903010e03030c131d041e060501060503061905 74
    0x3495500440e85684140c0c141003101040704100480048090003d00080c090010b555902d2001442415494415801d00c81c400783c1ca9140745500d424009031002c105030300081d1043c0ea440b030013201103650030000d0300409807243d400c1c2500c2e9002030800c1007450300704031409004241d0200390008145400304141c401c4e50302c5040700030341040c1040340440c000c1d00401551600b03c040210003042ca03600400100820404940d004120941507143c002e20100d4080d080c40d00552a00e820240d524001050b11940d5440b1100034a0700c8010f00d0600520b000030501381207411500e400c1012891103101d0b0465445840960281c40541c011907801204a500441d0481c0001c6004549114041c003880010711441100a0000c100309000240090841c2d0040e903900c581c1040c00101d0500c92070508441b84014030b4044100300003000b418400c40d8902000400081c804801705a00d104941a84444801017030b400c00c3d070401c0070b0340e100d0030060059402038071080d00c58405243e80000d003618400302d04050754005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 433785593 1250 433784343 433784363
    0xf0e010515032a0a020c01080c160c120501050a050f072307060609050105100c150f020c030d05010905090c0f0d020102010e0d080703060b0a0c020909011b08040b13 72
    0x429001c040700d820240010300b1003a1210001c10f00e201c108034102c90000c0241004a645140f00100646412428889507040c0800b090070404220208800d5926205900501c00c61610f070341e142c0b054501a080e0403a00d0306005840c20503003400070541c0014030442040c4010032442c0c8444010500c0c01908803509000103041c0d5210103d840840100a1156482184c1141c10040130741e64020030b8800542110440591300d0004211626146403100155030b1142403081d00c02e1030b00d48075102c1d201644070b910800c1c20384a030061400314102e54110f80700c00e4090310030381c2e4840514610300e0020301420b2040f10400c5007000086030301f450002c120081801d8000380741c90428950345080c09070a0b4031084003641507560710303d200c0000c004140481d114542d141ea403494502e2502c82805011140c0c1504401c0d6655024003914944682002d20110503d40454242d0f04070350303a40d02000d014101980c0b03d15100c48804100c2d18503544c01c0100c46004910880e140003207a600c40c05d0b4507942d5000084060020742c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 433786843 1250 433785593 433785619
    0x403020f100e040905030c1203010f1e0302040204150e0402031501031d0607020a1b06050a120b120a03080a18170c1203071716030c09050907090f0e0105 67
    0x700d501c0000502085062039000c41c25a0390028003240e0800070281ca40ea00002403160907420140b04403a807606040301345609650501c0c0f02c60608080c640a42c07000c0d103444859002c000c5481980032030085600610035582e4a0b01c0c0c0240920340c22841c0030140204400300704e143c1c15440d0600940707100c0c0d022810421003a242510044000d85102c412080603508500148101d2160621620307220b50b03d103070001c5c0b243d4281480d01d140c2030710304800c55038290a000901400340c0ca5100c412034031806911301c3d1420708108200b42c1d01004111030610355234000f15a21001c01070100c0460143c0602d80680c8400366035076285038220042c1c601c032590411404200e0541000051010b030b180b5200c083e0300c03002d82401c0c400c0c408841c5240103025000e559075004003008116596903c81e1508004218070201c11001d42040000480401c00d05851202816103d5003400d010511813040b0300000d100090190031982083d441c0035002d0780f404e00844800001c4204003150361800601d0b200e0485602030014452865 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 433788093 1250 433786843 433786849
    0x110402090f04111201080d2f100506031b0a0e1315020417030901080105060c011509020406020d020a0f0b0a0615080f1008030301030b2a0c010c050403020f 68
    0x10041000e035500854012024205850340e100e0f80d00582c40e43c00045541c1c02e541000c40d084a00705a001c4010340d88849400703418135601c42524040ca808418000c80702d40002c9110404d290b242c0a02e003040e80c480c0a9038030640801d00e82161340540000d6040d034044101120400725046c4a400c40700340c00c07411050041002104c0d2a01c0c0541c03011038a030411105084650751800b40c104040e4024a070310340c0114007401424400b9030201c030724100e034400440c64800703030b180041e0048905108561240502040d03882280e9400c2d04017a18102c03e0034402e803c401d0310b400418009402c18054000144203503000c00c4126400068504001600883c96441c140007640d9002c0c0059002403027810820b44440b00003a81814408185009001c43d442d13500031450700300d040f0008660014070115600881803c00c1000120203c11070341960f070801e07005002ca685508201010070312058003d0344659001c1e100401b02a5014041c100c0c10894400070300c0303454504102103500d8007460002039030105120300d0108180c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 433789343 1250 433788093 433788097
    0x206310b07140a05031602040b0a1412010e01020a09031202121c020403080301030302060406050c180108040f0b04031e05032509050306130c0b07171b1c08090703110402 74
    0x3001d1001c0303c12100c201c0c0d03a514219001140e000c881611034240300030451905028080f603600c02556452203061800b141c494410702184141c0f805070b201c00701205400071007900401c040c008500c00a541e140c0e160344005000301c14a00c070030340c2d00b026180d004268051000c2401480700c80c10b42c0300a4100070036146010b1030814142c060701700c2c40d40c2c01c20001000403c3c0c0300c00340d0f000358002c0e0082d1115103450304000e410707200004c080800500d001c0164054000d82c450406c0d2810f1030a01c4e1446041c1d55034901381c0400e040750800500200d013400200010146c2c001d070308010344003402c00c804221048030071040e01c05d40015512049503c0c5003000c0082c914a00040c24a079040b85450300310035440d0350340c3c0030030706082c0161001e10300002c011040d1002c0c031410022010041c13211540127850080c203038440f8825800040c0c40c41e0440f14000881241c221075184501900800072015100002046d50999a240615403d1280860240400070308056004a50700c41140d40001119850320030010400c0000c1d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 433790593 1250 433789343 433789373
    0x2070807230105010e07020d1103030126010617150f1b13060e0a060905030c04090f050f0a1a0610050a03021b030406030b090103150b06070206310b07 66
    0x144010524101c1c024000740542c900070888020107644c28280f8440003414584c034810f80c00113011106810f49140354000003220b045514404084480f40c000025021031044244e020740c0980d802d1a0000c542c0041454130b29111610300750468006000c00d1016141e00c0b181200c10f00d0101901800040803005415108411950a041e03900e1604003205850700c8881c03440d0300103000148020016002604002d502c2501525682c2440d0031406d1410300000e0361040c9c1c14010901a41d21a03480d1010415580110344c2d00a500070117480252298071070b07480ea0f800c4e402105070b60711a404080c010340e840e0301100f0540545000b6100d00880200750b401a1043c0d0f02500710344003010790030040800950048114550501c0004011355aa42d141c60001016140080c2e6000e1103080f542004000103a41c0324000d58070400e079010007054a916207000601c46e4003c442000c0d4104c01c0000c0c4a9494000c240c5a40c0b688250342c0c2d000a100300e07640c24627403004100d40e00803591040d108105a801140d8501506184 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 433791843 1250 433790593 433790633
    0x60203041103031b071d011a0c100504020a0b0a020a0609030e0a0311130c0807140405180f0702010204050f0418050304080601210206090405040204140c070501060902070807 76
    0xa101001c0080703891980f001d41e0351000316054080c0714142a005010200c000c21140f01c4660300b101003030031a441c0030441807281140710340c2c50001040d03040401030203440c0c80c5014401a504d2036180c000c600c0025043c00c031801c0388951105000820800c009500303588095110b54000d000c80c030504c4d607806004100041c020340c00d00c80f010100c42e4481e030381c0351410000f4600c65400420340c4690082402003040b00d00d1008081c40d428145021020b55002d040340fa03000c050703494801c48580e440901083e06214640037640c00c01442c00051a090481200140c0a80300800f12881d0a90300c2181c101e08034011401000c0e40309001c201c003120546841d81150b17100c10390103040902000100d594141c80c540c09584454080e821140042001e0105000041290111580b465002d00404e60000b40b0501c02c07504080d101d6691070010801b59212a44019a03000321101c03c8011420120702020143e0041141184d8a41c201074000c210292540240c907450703a4002c490034104019a555004107543c800c1d048a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 433793093 1250 433791843 433791863
    0xf03090212010606020c0904032a0b0a021908042a08010f0b0109080c010203070b330406050409080d18050a0308010e0603030c10110d1103070e180406020304 69
    0x565944440088514404400060101e20b03019000c0e0500060046c418400c8030984100300c00300c0d030484071000901b01c0c0d6030361043c0d03001040c40c01c7c102000410030300070f04a00d040d4010456154007503401080c031110006003035414081c040038111034020f000c540080c0b003120a032403001c13000c80c0140b20180707402c410940d11541c2e6a4491048038215140f0501c510325490311400441002c0d40c000c01010301804001e809407002515041c0040c1d40c0f40b00c4c40e00002c012604000c002030128008041d112169020319820074848012036644035041115041c0c1c103845646489000a8685403034843d0800650b40800d2035824040c05150400041902440141401e6000d40c0e208000545c00e201d00f01c4c42ca8800e0300c0f0352040d07505050101c400190020002d41c040ea0040280c80d50041d40050380c4038a40840c40000304520320150100c00040c0a00300910081c9800c04501508001a01c8040d40c0310f045240e44000c00e40708248108004a003070b90340701c1c0d21001200030118010404a03001580d00c01c0c01460364107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 433794343 1250 433793093 433793111
    0x130204060f11340b0d06050a05120307021c05060709060f0512040f0512041e060503250e0307090219020106150309030516050309091b090904020d05120301090c030207030f0f03 77
    0x581e0725880031740080c0e60300f40c0e600c00a001503d042e44a9001429041c5c8520075442c0e64446600e44d6881241c4000e0300c180340c041c024036100006060301e00c0006a111042d68038074101081d000c0c01ca00054020300d00800d1510b0f070190b5607248588162210345143e5100110a91580e0700d84025194003120b090342c490295204030f0741640301134001000100048044032034011200c1c442e45030f4145660f0030131001c214080041c0301403242c02214401048500d13084d0341001c1c54445209503007002c15884d545805000310000014101943c4d80a041070703011215404241d14640031049003244c10034041c040101000a0b003c00034544664400c0c04a18401d041c45440c00341d51b6a0101d41715800c0da0700483d51a880020100441d080c8800420b0304001200c288421070a001da01d000700c0390160100c118040c11605000505540d02c410502c5c0c10190004280c48420207510180300140e442402034070b45a6091808241505102c6d108584e44d268155686400340944801c04984540d1310814820415441740c401d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 433795593 1250 433794343 433794359
    0x2a0305030612250b03070905040209030f120703080f040c29040b0403051009081b100e1c11122a060a0b06180906130204060f1134 57
    0xd1400e03412001c2001045491000b218060f2000ea5003000785410070502c184802c070307508800803109036413041b170300580c0320005240402e203071041841903c2c42030f21400070303082d83c0500640010f0104501982c2c074036800b90f41c0e501d100c07448070300c043d2030050100d03401070310800034540303801408a103450182c03901d444030407400000e0088503007254105c2e1883c3c0400040800802000700541c00c25074a40c2e1005101c40c0003a900c5152003070140d02e0f440641040d0040741006403040034805030103c1500c4510821100c170046d41002d039034041034400c0004880440d40c1c070407401d5000d0000b5151900492000300011103a0100c0c4400a800094514a40c0d03040301120385585403007030901c1001a0690030062525243c405000c02c1601c080b00c011074060071041114005410381c41032180c0f20020103907505944c94030307100301091240d13014a5907800210b102103404070382c0f19440083c58a402c101592002e00160414540c540c031204202808a10400045100c3c2c41010701c2156401300c051064100303a48159990b860 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 433796843 1250 433795593 433795603
    0x30c05010615091706010512070905010e04050f03040b0306040c0e1c05010c030b0a0e060a0b07050a06061a071403130f0806130f032a0605072a0305030612 68
    0x80b80290b0b40030780e00b000a69981c000d045200915441100781000312410468a44418060140c240a41a4041c2031b040d080801c100000042c6540700703003000b02d03684d522041010f03074005a800303c8580c02001840140b12400000361415909401509459902c800d4100802803006a524100b4095400d0001c2d10782e13500d44400e403010318110b03402440800160310f001c2c0c1c219205d6048000615241210810990321404000401c3e1072412001c50f0030317030f00d48034009007000103d070f44100c450741400240c5134104034010403a900401e20402c130503c100390b228034042c2d503d8120903645580703c5c0801d0041c10040790303100000380022058041980e10745401d5840914107124241c001505140c3c03c0c80b03041100e584200507540d409180c48bc64040d11140380d0395404c05010034002d01074100451102c84030303442e0700c040514032807200c80e0a40c012461401031a01c80060101210f195010400b00c01081989520f040f01c410403003d8000d100b8240e142e903071351303040d0b4180c3c001416450b0004841d0322403c40b46501000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 433798093 1250 433796843 433796849
    0xa02060a0f1811011e0504030b0901180309080106050405061315081c18060c2d0f021003090c0b0f070b0708040510020f2502030106180b06031e04030c050106 69
    0x2d8003e50841911001424100190190010310558010030380c3e141c40c0e0000555007961f030b1200c8045c0698076900580c0340904814a640402d100240f86c4042c10150003110b41c03012509008028498540d07035104000890307104903581a000340540000c00316070203840c3c0c000c0c1c08800940350068001911078840614215001c021001011114109450260342003051204080c110980e500c400d28100ba00c0140803e16060380105482d02448080c22049540d00e00b40c4d40d14140e814540032140c0303807030900c00002954030703100740d0040304903440302d516182c46030003041c40494001e031081482c149840c1c030500d407075400b1401032070b882c110501107000028035001401d030041c51250b840f00214102810090304100c0e1780120f81070158410002c8070950148042582c011002003180200c000902c2e081c5480e4040c1004402503041d440c0c08404640442e20f2105c01410202e054010403004078518180f100742e110540d942c585000c140d6405100040c280a10668080e101785480b04e0755842c25130350a402d64134650 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 433799343 1250 433798093 433798103
    0x30c07030813050402091806120a210e0a0515090402030406090b0105060a090905060d14010c03060b0a0c0602031807060903020f010806090f060307170f10020a02060a0f18 75
    0x10390b07802000580540b00054503040341e046140075007100000d21600c4650341400d01c9029404000b84030341d80d641144ca28202010010351b14040d03600d2030304442c02d00f0180382040d02401624002c81d01244121051900b015019010851460410341000130203e100b0344061411282003003090020f4445001450080d80704040202d640700c1146400700d400c440507041940118414405051441d0744894003034126aa0b0810004280d00d49901042030082c0741100500641c190f941c820724844015448144400c08542d002c00070203842d96404403041c403490b9000e05c00074003500c0307407500400c00780e9004580100d241d42e40440c9a410001c0200e050522540c03003640800c1d001e0004006601380311b0724070481407100b4038182c0c1c130629080300010901403000d00750340304a40c10400002c01c2d989082010002510160404513505070f030b035501e1181d4544894640320340d13a020300040d40001c40d41034001d132200710704550040c0040f50f9410101c440101b8840f41c001c0c01803900c2c0c00804841e65900160142614002c1c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 433800593 1250 433799343 433799347
    0x50913080f040f080106091e02030a090602030c0d060e06010c0311010e01060602030a1d180702010905030c07140303130b03040f0b01032f0109060e0f03150f0f06010c02040e030c070308 81
    0xa8132403821114181c1c0300c0c90040703082a2140400d00034040044d07003003040f005da0041e00d0b40c0310310700190010100500003c100600c0041401060303241a00a068940d141700400d01c0780701e49940d8102d24600041e110a03020a44140c01e040c0042d00030202d031100900720031300010f041c000f041402400d40b040c03076200001581000483e92813240c0d10003115201e4606111000e101d00d5161070200e507004511201c1a110b134040324021a800d18406c2d00824400340c0c03c5001c580d22024503c84054407800c05102d0544002c07000312110119003000320070ba81c01e0000402814800030328065814103d07500080040f5034583c00108060006140030b0803040c045d60142c0504c51100143c2006c00c1e560415003540e5420301042e60300c000c466603074418001c9042e903000749002005107501d107011488107000880120313414000c4004440d0041d54868a140c070492a0026020103501c69070340e00c20726a001913804500086200c40014054201500424064041c1c20110307490720f6182843d850070322b140c4d60001c0382c0760710740 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 433801843 1250 433800593 433800599
    0x70f0206071209080c061b011d0606010e0904050307020904050709020406051e0711060a050c1e0d0507121824020136141c090609050913080f040f 64
    0x200550307032001380000d00018407a8001e07110004000303008030545d008060005500071124180c00307410201b581800e1011091b41c1080d4001869243e50007101c4103030008004c801600000d01d8802d8103280030b2134010018629052885d001d02007400030083c01513421344030f640400280209144000d0005050960b503a40c0c803801c80180555817107540000701204004184003000c04a006c0701032140051608035112a65114051029074007130148502010440c090306052040e07954528100840101050054a080c07207074412041c2c034a8060340c5005400b0b4441d0310709400b0418014848405124508880c00002951710349282500303194001a070036003056a002e1061802c0c1d0240940146034410700d80e0080d4410a4030708444500306410800d09200c82c1c103594203c1132000900d481d0421050500c1900c0d041d07150b68040310344182c0000c21400c002041081c0000d14244610b003d0b40c10350f000103040c0c04040d03ca004282d4804d028141c42620079040400130300000203400c80084c801000344c00c00110003e89 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 433803093 1250 433801843 433801847
    0xe060a0c140307210e0304180c05040312030e03090a1205060702031801050f070614041a040206040909051006120c0b0c2e0906060306050a0c1202070f02060712 70
    0x4600c01e45580e51800b8400e00c00d589404c40c138202c0c1c4000004422110f20400101c004015203142c51141859020001d004070788079100741100c42441d49081d07024892055611400c40312132080e4400a401c00c0081c40740d80484c2442508003107040c0d400c1500f16070900780e05d580019140b1085034000d203460305000c0382400030010107111596115034035001960506510644000b04040c0c800c0459040190000b0403003e90141103040e00c0d6140e400c41010480c009081340d40030788108064a054400d01c1c0c5284031609190b40300c41c481841076a018005604052034079100c1c0c03000d0008100103c50b140165074050768a0050f602c105001448030052800144400e4141414682099040121000010810b4aa607030344000f03404000079168141d0804d400c0c510802d004c0c0049044801075024071308100100c0280035068000d076003a80c1c010401044141c07509490034045500780d102c42004a10014082c00303035030000da0301900c204c42c001c509070b00c2106166030000b8901c1d4098001100d0300702c14100c09000240d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 433804343 1250 433803093 433803107
    0x17031608060102060a1805010e030a180305030708180d0b011502011401060513150c1203021306030b030304051f080f1506180409051c0203120c0703030e060a0c 70
    0xa1614105000319041000000b501c1d10070007800c0d0500b01d51071700701840701c2801c3c514043e011150090020030200b04031a91131516a402090040c000031240860404d0400040c9021021264820001c1d85000a650b6421880c1e4226599a000240141d00d41d0602c989a0000b021101c912482c43c001d450b60500400d40012002d4452100c00c5a14040641c00c14401048040e810f6035010f08185840304100d55507509909040c0d0811a514142041c0c40017409811441d81c103403080c0f18050340c0c0410255034404074101e00852001c02c0c04003840d648100100b5010394030504820501030141c7e0f1402e519a00030607024203001c107400315034140b5806c0c03002c2082d6010031616000000040300001e81d003805403010100d840075000003403080300b002441d141c02d400d1540580c8500e08010704140002461420403603102c1c90070101112400410401c2e402300d052020048450080daa28114100c1c0d03180c0703040b1103105411100003203083c0b5540300c1c80d10a030120100460340c41154050000300d40450700000090600c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 433805593 1250 433804343 433804381
    0x350403080a0603020913020609060a020a112706031606020c1c12050d15030b1e0702030a03020f0408060f180607050a0f0216080f010b0f0604120309031703 68
    0x76500d40041840141d541c0d074a92500201540e1086201d040d1900014125120382034100764401c80024101000300e8010588510581c01181c220810003000014813424441090310540394400b4995240b0941c00c3c50820141c000c14060220741903a030382000390f50039134240d903000381c0d025070702c1490f4246c0d42c0d24181c82c0f0447d4881d20501c681d208480703d1354560318188440000c10007405008030300da01b04058994410843c55a40e50312035040036541c3e08285102c1c00d0251800c01407541d10f0307012001c6030b1078000840c41c0540c4042d801580f0700802110110000e400400380000d21760340820001800040402c02c56000d078045c040c1c41859424155184054500c45004060b5a6088001081480e0f0381101c1a03071019946400c111010841341d1004a081400f00c00a41500350610440404c078a00001402100c46162100800c074041041007000010b055080c2a958028001c0005004030520200103405c1c0620a080421640e601c0741d5880d2286445501d144c8000a000f0042210400e903d0954041c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 433806843 1250 433805593 433805611
    0x105090708070512070605180a060c050d030b0a06050a030e03040e01050a240302030402131e230109110f03010b0909130c0504021602030f03040303110f0601030335040308 75
    0x107091180c41805403105c0c0d00c0c0c8201001c0c03020214a00e0425240e15801c00c1031000c0041c24405682e40700c0c94041d06c10b121041c2e0580300c510500380e00301540c82c000e115400018100801c5102e0b814544081225507038001d45561080544520344952401c40c1003003e0030103480b0b202040c81a9606001c180100c555407507200c5081070800881c0f07900809102c1101132646049858090f03620369980c00070a6400445803d02405145400c444141e208000c5c2900251011421820b2054101090791403040304580f685101c16440310300e004010409080d0f0214001c1a05070b92158201540e68000c03031003d030003d900c0181003840001e00700c41035103001c1144076030191003d01c0e0840841050780742e05081c3d0300030b4042c1d2030040b90300080c110f20504100b0040140217a00070120340c17403105850580da03100e802612003100400e4041c680c0d2a00b90030017103200e1210130b070310f9001400c7c640c1c6940c0f402c80b0503000c14810341d05543c414400100c100081030503045481c191400c01d066803800c2c02e2400811800c4000e1903281 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 433808093 1250 433806843 433806859
    0xd120c0b161403011419050d03020d0905101e0309020d08070c09020a0f0c02280330030b150a0201021e03090a030c02211e24090c0301050907080705 65
    0x541c9031700440307819060b1350a4071070300038511402240404c0982d25401c410b501ca1480000942015400070303000d03001441e995140c54043e942e880074804a038072012920300119210160f41030400128aa440b12040694500440d060520380c0216400051642094440b5440041c40308c05000030704a107000100308190301103103068041d600c0142041e1a92070031408201001403404155564540d61203c0940d01100004245c03040944049084900d4071085506255201d9061485548007030740409444500a080002d071903100e8048000b070a03203404480d405421880041406100f01000d006c0d02d030010f800042c1e03241e4080101c03407141c9042c1d503800c90580c0810020401d09010120316080d44503814200300c01064081d00c0080c42404018050540848550446150b202d00001e0800e65044c80c034001541c0030b150010101d83c45565a0000902c40740c4025600c08602c0801c1c40ea1907808500c08007900c807502c21540000f800c1da01c00342d80e00543e95000410074003000350184900001040c084810f14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 433809343 1250 433808093 433808099
    0xf071a0a11120f10150302090312131a0d06030b0a0b0409151d06070207060f09120807050c030607050301050a06051204060e070314030307080a0b0d120c0b16140301 72
    0x5107840400811041d21031941e9808620302d5513010240c40003030407a29840000c101d0080600900940103003071102d2003072085050100d0208c62440485040c0302240d0640310f000703414014218449a440c8100050683e01002492100340b03a612a40c40a5445000011600e09001c0d03048000d6420799003030207104078580b82c4c078280002c1d14180804040c1184060104904219803004180300b08420884800d500130b810400051943c041101c0040e20600c0d143c00103e4140d655003218505614001d841c519045c2a80d000c0101d4920400b402450b40b1490484012115034008242001030a03500d0101040c0c0200042c0460701d01016054050b01c01c62610b00e062000d05071040186400103000600402d5490440c044041e03020310900010795000940b0300030322000e042d8196566842190100000380c0500003080c4030380c010b0302a141e403525005040035010541d41c1c58408944c40703c4511082817003c824003030000680310480079441821295000241d90100b07440150a080140c0c2d1030b00301c04e5000300014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 433810593 1250 433809343 433809367
    0x309031101140403030b0102010603050106031a0106140f070f150f051b03130f021521010305030a08070225050a120b01091112240f010f050f071a0a11 66
    0x103e43c41601441c0219103105000d0040c0d0042c01740d42c201a0186d42440c4001c003d00030805405c2c20040d115003807242860781d131008200d5403843e00500610410104021041510032a0b10141c600c0c14000c4800c09070010a503500d501c6d2141940e0741e03100c082074403113880043c60101c51040581c0704035103c2d020640070a0f201e400011a21004050701e03a0b032291100c2c03080078008060660f6100c25400350000c040400003680c503403046e41000f41d94650341ca1410659600354008009028101d80d030040007181049040c80c0141e820f000000c0001d0214842c221004c010302582c0e1041110360240c000449085e02d09110070302401c8200b98010203a81d82c1c141d640c02c400a5802030f503160445114910005040d110f105110b0024031441180600292120050284032002a03400319000500030840542407891041408034502c011100c09000c604000c0810340c10a0090004000c1011000606807600c00e29540384440c00003180383c0c410501000c4000c00c84503164903c903a06001c1e510035421401c00f00a0008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 433811843 1250 433810593 433810631
    0x30408070b0705070503030403200301090201080a020a230a1101020f0415030e060c0c010e060630030c0106030c0f030809040e03070c15090b0c0d0c02030307120309031101 75
    0x501440d10301d000030304605104051000d44042c0ca002002e0b42c0d95250b503401c10101c0d2010440030300000380a582050107051605114641c0450360603140c5540c00d80c0c481800708001d401121480c014803620307040440254101d2480b50403680303000c000141d00da51142c0d40080c030b604010046034070240e10401103145102071130801c0e1400c07690721251050a13080d120303408602804a03076044404c584140e0050108040c4200080d0901c00d805200800034920132800b450354414051b20000c0d0041d070030ba0041d00e40300030003144c5150180c000b0401e00c501c607094600e51502c0e40e8861200c2600e5a52350310b000f40b04103d5400c0181c0c008001c1c0102d4504000e0071611024200e10031012010b00c04c1c0d513944030038240b414051040d240340c140c003c501010400d0303407500e41510303110700c0c24640c1c8001103d505001c1240d11500c030544046004040c0100000e500c4084140c0f81c0005205050780d144c841400b80600242c8991300c88100303004035a4011a0b10840e070702d0090404440146030b039000b6410184031717449240301031300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 433812949 1106 433811843 433811849
    0x507030f02040f0c0c0308070c0b0c12090604030207090506150c06040203070501031e1d060709140a05030c151b0303040209070302030121020406090e010b04060803040807 75
    0x22030003284e102040e103c0c0400c0c110359548010034460020b103588040982070010b950b000580304d4101010b01100e00e01c802003000141c403e210400c804010350003800c003000400c0c00d41007542d00030b51200b106001d017050741d99a40d40040e6495485001d8010410742d40c2e47c0c120f41d0b4085000545494840440b010390103849005030004065100f84105101028040780c9650b0103609070030103201500d800c818100c107525442100c07130300c490409d00116010300095196000c01c07502d4401014080034920381058400c0c814990100104d840200380c8a9440c0d00c101c85491481c0042280c909490180d01030341c0400000501d20070f81ca040002008500990080300c10103aa6601c0c510114140d120034000c403132816403071452000301200360302d603001540c038401480850f800361101d844200319442c05c84415460fa455640041190609100300301c00303026140091840d16051208196880282e0302c = true := by decide +kernel

theorem cover : BRFrame.Cov 433633093 433812949 := by
  have h0 := BRFrame.cov_init 433633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 433633093 ≤ n) (h2 : n < 433812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
