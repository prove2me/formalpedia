-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3038
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:28:32.16632+00:00
-- url     : https://prove2.me/submissions/e4420014-ab79-4afc-920c-e217f99591b9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 546223021 ≤ n < 546402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 546224271 1250 546223021 546223031
    0xf10060b0c06040206030c0c0607021c020102040e010e13020a0b090108131e1b030b060a08010509071509090507120e1209091e040c0905072a1704120303 67
    0x140365109038011000104059070014002400600304071005540001c002a48242400242d02e2107a140c0602261010010f800c82a004080149840c0d4144000520750000f5070816080c60580340b50544c0500c13825544865007004941e41c01e200e094080041a0050300310801c0c40c4e1200d580c2c1601d42d10515049000840c0304001a80d036040300304070000801c0e44040906d4003004d0710b0000e10101d16222405591903c1c000111240043c9160500c04c01548542881a51841d008080015080080d400f40c1c00a90400d410031155a42c0800c001c41560341021442412042c0e10034125801010f039005143c3d01443d0106005010f50404542d03050b5003020714040c40030b4000da5018680f50304018041d403600314400e209450403843d004140d05d90142c9010144116130f003450f421001500002e65003620801045041408100b540e8060103602c0403c2d410300c0b8025818144440c842c4c10b000c84168010302209040031400c02c54091040600c2171241c0c003599460f10f44403000440301d401c0c8280c6c1140400c2c604 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 546225521 1250 546224271 546224279
    0xb01060815010f050715020c010f1529071a0405011d10020c0a231908040302060d0b1e0109120b01260f031305030a02090103110102010e0f1006 63
    0x1d0744607503003088040e56914504810640f0581e502d0f0458182103c1d4000c40003040c03800c01300184040c0801a4414001150031280540c41e50101c0f140511b110051f0784441c0130034059030b824202c0e01e204030754082c0031b40c1da4400300780d01405580e8041d9000007002c02c020303086500403d030801030f83c86014901580003002809030f50030380701c008810806200f01054020000c0c20180781d009038040c001d0f0f80744234020740d140303904159540c00300c25a5010f072144058103034031032070795400c04100510300705440b0207a800c80c6807845648440c4858050342c0b2000317210300d000007100c2c07061200301d41080c0313030344000603007480001781007103490305001500055041c1c00508184000032340c0d006c05058490325135804c20f040b8070f420390030154600f440d022010303c0360101c6000019201c104101c01c00c4502503405100d0080d6403034040740341050641100030340c8000c0c80f80d441404102c1c05a542c04900c0c2c0d044a80c00840c40b10f0140c590740050b0f02520041012600342c1c062098000c0c0703020380104186507403000c2c1d0300007044150340b5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 546226771 1250 546225521 546225541
    0x606030311010e070510020a080309010c091a0d38091023030a05100e06060a080d08040204181a16020703030309081612030f020a051e04050d0b010608 66
    0x12038807150807550004101704501d0804082c208090510fa1054880ea9203580e219440258010381e07030b2803420380d0740380350f107150b05644401800081c01c2c00400d4151501d030103043d0720301c2d24014880400103699442000480354003600302c403e000548869140c0c0c60b07042c54046e0300580c1b880f07000511030180c83c00b03c0000c5c03000d04a500d0042c064921929900841a005112068031010031404c12a0144100f04006c00400c40c1000301d10740130400044d001c2401c00c0d8100c0ca150400d10003400c1d42d4023460100f141030200d5071010400308a00f5900e4a4190300c0350f13a4500010700682100541c1070160a400e800100134031a45a82c01c0280d00030b51f140000041e1149600002c2041d0211480401038000c030b402803000a1298000e12000d502030752809007000305444c06c480b500a500c210854100208420035a00a90940140e403024694014110309241e1a544050064400c3d408095142c49205410184401481064034042e00300030b004483c1880c01d5142c003000d44042030040b100490007420000e5500c00f1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 546228021 1250 546226771 546226781
    0x303080c19110609190b0c04080304080f01150e0406051e0a020c0105100b1c0608030a0c261c0905030d230c040603020a02211305120604020922060603031101 69
    0x170000c80004900030440e1100c0806c510017910009030030104100019055004201034405482000c0160003144081d080c800e017190b883c40c00c41a004000200c040080d510030300520341d40715800600100d4141d07a03074014904400150040807002c04c40c61000d204001120360b000e0862001100001c21040e19042c4a861a8415074840c00d01891020403204000c040444c80c40504400c550b103000c40e6007911426001d003184c0003c0048000504440c5048044c04110b088644541466081e1140e441c900181028418817030306810040c509440c2c444181030321240ea11a20481d41c0100c02d0300d4a8842103e005000b400030080c00094940520324003030941d02019001d140103150f00d000c032900d020300d003400940203504032032010400d40c00380901804044417910701503c0040300a41c45180d640c80e042e1100c42c105c5600e500050b024180005000034036000019841d83c210790100c854610b581c2e070340c07010008452001d0f40e0b410b5218401000807410031086410107019680702e51100b09246c0500c40c1058200d507 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 546229271 1250 546228021 546228043
    0xf0f0605180a02060d020a180312030c11060a1805190507050307150c031e0201050103120311040b07020303072003010b09150906060904020414100507030203040303080c19110609 78
    0x3d820400742c06030325170a600a140c040307580c2c1404568051068003a00c1d04d10f80551040da06001101d808440c03084d07042c450010b00c0d00d203500788502040314102d4401d40e1101c00811529505c0c0d5a02c001d400301c0308815010352419680501140c000042900f0740c030316001c41c24101141c6038440c50f44003280c00d00c1c01040c0e600c207807075446142541c44038507050111a5840c0c099400c0e41401140c0400e03605089002980864400c03c580001c20107501d140745c11607107030100240400405141c030512403040c28200089508698020391095214013040c000281184500a401030420b4040302440c2c501040c03954403041c51b480220000c004142c0007070103021008900700d41519504e0320445280005152455042c2c1c2c010364040c04450a000840000ca41241c0c41030f00306030030151807400200c001e40781a8000400a11851420300d003024119a0007a5403800b640c00010180004000000d00094031441941d20032404481c009590404464003c4c02700d03140c00c1a010403601500d8006008172000281402c114 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 546230521 1250 546229271 546229279
    0x10e03040518070c080904061a18010e0604031412040602070609060903030804060504050a17040302030c1804080319090f05010f110d0207030e060307030c08240402070f0f0605180a02 80
    0x20390324a0317444039a82e0384150509a80603540c1d20021903007600144211800044141d01e070b03039072904601c19001c0d8107801c6400240c1000a900445d80c440d40340d070003d40e0110b82d400303480c5e204294007402d60300d4182240c0e40e445c030a00680210780001d070158009040000c9600036128850200d4444908485807141400050003042240b008640051129032015074828012001d4901d18813a035600c0284810501000040c1e1620109040c020352030184408000c0b6402164240e41075200600c00d1819410001c101400304180070000a1900081644059a10008020410601906150142099424010540f140e6180203801003850000e03205002c0ea10100045190a0030103031852800a54011403046042081e940c0f246456921280b000e07601a102e1510003181405900341d00030300c207160081c452500c0e0030038003441a81c544600c40d029500400e0540700942d803040103007006a415011240000e010b40032584440d008d004283d84000c0c011580d0b032008622520184050964a8080310f074080d46c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 546231771 1250 546230521 546230537
    0xb01020604020f0d1208060f040608120c0f100f050f060d02060a020309040f062108161e03110609030a02030f0307140a080702010b12060f0711010e0304051807 70
    0x94941042032110f4443c000700911240d60340c6959015220041700c4006020034001400d002e03007441c00d50b0212880b02d000356420065a481d250100f5a502a900031040c090800000c1000b10100140003205c5859a00030844200d00012075180008221f01150004642c4c40d00300807402c07800355a0581801044014400110700c0001d8003081000d9021240c0301c02544410080340c00f068550b4000c484041c0180000014803e03c1c01c90074000c65410303c101290410003420700400003500030019503040307065a40c926046440c01d898141d0301004003504882004407002408410998082032048814400e00113482640c0c40b0301108035030b00e000300710006000d42c005000300c102400428000d50b03800685890082d403105541340c41044c460b444a1032200010b5a88000c01c103006409015054101c84c0c1501e40c9030300203600b00f14a9440346400351042c83e4203000707d4017080849200313010104002410b44000c11215005005260382c0754040e105950040c2000752400d100c1c41040c44505200b0700d8140c0360701d25 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 546233021 1250 546231771 546231773
    0xd0b10120201080a0e011b030e010b0406050a09021305041802030c01020303010f090e01020906130905060d0804050418020a140a0801021201060c052506080f160e040f050702030702010906030b01020604 88
    0x1c090b0034045c030040d1080d9610411a90745201d45010f880d02001d06880004204451455242c25100d030306038894052420031f00d04029640f9090007007000c685c41d400b00103032100210400104118030a520455200d4141a0514401400108074201151003202109c1c0e002000600590726800248112001152190380070072a41455030407801c51062031000052801403514001002900300100800c41c2d000001418008003034980305040d007041c030440b50748000403416a2a40d1301881030b8040e02c1c1c066074072280c0e250355943c12134144600081d4001c01c8507180036141c01e1040c01060035024514400c0070032800000b64440184200c03442e01e42904402180c3d6070a2100559140342004003c5507248507010360300d8540345005e8141c078641036000c00d500d1405881d001d0014044000034203c1c101855190052000c15800130040304901c4106061004000100300c000400900140c040d0000640c20f180c02c00c4215a4080000d18aaa100740c80b40c02c401c0782c0356801101180c4955100300d0141e44044013042c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 546234271 1250 546233021 546233041
    0x1309020303390303090d020102090d021e0d38154b030a11040b0607080406080c180910030501150302041d06040b150d0b1012020108 58
    0x44400e001d89907903254003034072000d044050070b88080002c40e840c0e000407081c0a103c2405000004207454203100950a120100000aa8000120b10000d00c24201801d254104410100c80304500f0b5000404412406945040c60003d940c1d0200f85000290390054445080640c0110b4610032070f1820000758030702d44ea80240c440381d690300c20044603501243c5d00c0b54009a01c003645030008004032141d952000c0e18000942c1040c503190381035514030242c40c600a402c0752942c07070016039080c200d0f410528000e4100e000700c000c200100381d41c4e601caa42110000410300d041c0301040c401030044401c55074a01400e9510200d800c40070b030140480b00c642c11844001c07580c10310300d454510b240c1c1080040c8400415242c5d070380c7d120b608540349810800105000d001c010001d51a0a00c104610040307201812021141c07200a0691241d0004000929205403400071682c41e02ca130710136a1151030000351549010074010700302050103040031101d201e80701e1040600450006130f4240145441581a191101941c42d01c2d4261 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 546235521 1250 546234271 546234307
    0xe130506072309030c0d0c030b01050a0506190908070807031109100308070615061107172817300c07050c04110a080f06011407031103030c04051309020303 68
    0x425810710a03400da00d800c5070b4030046d0351131020340f180003074410441c51460a07003e00354059200070b02c03848030460f00b0081d0b61140012034890251041212040d582c07000810355041d0b030307550052080ca200c3c440c0d010581010009462040c0ea0040701e240341400303c881c04202046e4030864890b01a9205140100001107c1c03e003c8c0100c58858000400c201e140c6044440701d07030b031503640454000340710300c80d9554048109100543c06000c0c0e148598a10540340101150f55032520300c0840c4d40050f00500c1c42c0755100c10031541c0b003103403540a0402e400c0260414102025500803104148000d54114029208031003202a401c02440680e80c9034083d698402c0d1540307a1980100f0420b0780c4a019107038950040d90398074804c404455283c03101850700d41e49100402056204024905440c400f0100140b0020703030380219599036400d2600402c0c42d039500803480c04452181c011501150180300c08824040f03910308810140080e118143c039078003120201101034a0035202d03135890281d0150000c0000c002001c4403540a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 546236771 1250 546235521 546235537
    0xc0703140418090308060102060402010203041a0d02190f0c020d11060c01052716030b070507150903032d0b030a080f0c06060907050307180e1305060723 67
    0x309400c0c1035450711004546090040d8101403540e54008003410540c0083c042078000c20300f80f00400d00c0d4035003070380041c2d0360344a50700454406c0c00504640c00310499002e03086031070a49a0503000d5440d10305882c80e161031503050141400c0410044503030200624898103803104080c2d0000e182000d400c407540c136010102e82a00b00328a401040400c003007200c49100340541030040da40d281925030101840b00f803e01000c10000a85900d5410410000c40b800054201c035405490300300e14981c01d06d48400d00145c1d0503104000c801041001011610024007600342d10034810740e4080c3d00c09201c0c00130110a1040419030030003040b504400c0092589030400025070003600000c0000d0229080117645894083c145c1c0c002c4040c003e00c13840c0018134407000d184140700b016000201914801301c0c1c0d0412410140c8940030041004040008172941000c002c450781038503400600b130701c0040e00501d051980740441c6c141200340003682c02d403003500c0200b14054440c03407400603502d0407448040ba440f02503880c0303400d142e408410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 546238021 1250 546236771 546236807
    0x30f0a150306090c030303060b0408030f160b040b090610080627010609060513020702010504060f090512060403021204060e0112230901050606040b0a05090307030b0c070c0e0c0703 79
    0x500800010030707a01c90340720300c03c0c011000784da206499803078000c0a032649500815813500b010b0004101600300001075072085052140030545035481003a0003a0b45038071642e00a070041c006038090100340010071032110301a030590400c0c0c500541e19282c2098101c5410f1140303800c241d1003007000400070b0281007036201040c5581518140e03c00c1c2848006400d54040360062080540c0d1884100700c01e1400100207510040070880550074000c00303130000fa00f240070340d01c140d030180000388001c0880c19100b10003101c041d1100800464540c9010710950740c0d121030458046002d445100112284001a08107440459006036100b5040894220044600404410505540507100ca00a002d10201e1000704080c4070038203011107400c0c0c90220400c5080d03801c00b5017054091902000244480380d414011200d050300306060259030350a0b6400420714101090f800504094620424031a000000000a00e0301d14019514044100e49071301094140107025a11888403640400640000a00512003103040c122910 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 546239271 1250 546238021 546238061
    0x7030e0111010c030606120905030405011206030f08030f060f150d11030f040c0608060a030f020d0b0a0219030e0a02101710091b080609060f04020d0c14030f0a 70
    0x907401800c1da6000121000880d86510052010326070006070850f1803154000180a1081d0b1174807004e40304d1046d8000d80d8100520008102d405074540e800c600011769000b20303030030380c1d54845003400b411a420689003010f64617690310105480e85881c48902d0b100c020000c0400324400c0c0152041c8a0b1940640c1800c4819a1102c4090500008940c0030707620914281000842e24680b034a04010429101d4000005100d0705605118203038a4041005040d81d0f030103980d88145000b58000510554032200303000302125501c0c02000303141481c0350050712907a2200314a5003000c00c5c090000f0341c1940c2c40311351140c9055200c8281100903140090301c6e102c3d69a0706041201c640303110001e55000c40103003100d1424540c3c0c89410200611520382c0320f40c05c1000003104481043c424404e1f401003804030040d009503c910309507400324039203075513144082060100c018000c554480040b05504c1c060000c1c4500031000c1041e40c0404560310071703d0000c4038401c030811001e90700d036695580304600080c40070300a0071031020405 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 546240521 1250 546239271 546239297
    0x114010315060819050405070503120c03030109091e0606060e0d020609041128080a0e0307060b0a05030312060a06080613181401091115040b180d0c2907030e01 70
    0x103105e6035018a0080c409005800d003003405140c5080742181c00680d4044081110307490400c804010f0700c1c1500d02045010403010b500741801441c059200ca0f00f151400c420040040c10003040740d1001c2c0442d4000d8562110402c802010414020500c0c00c010350001020000c614a603d0a903000d82c58003240d40882605007410100300c00465041200c0c0c0c858400117910b002d4100981140e03002d03a2001c01c1460030700c0902e0450041603220300801d0001080561030702c00101c266514a075a24002d050080c0440c0d880c0c043c216915110301700161a03c1c0c2c0504215400402c15500c2103002c1031003503d0151280c0141d80400040074000c08a6103480301445d4855900040024810509074402000440001c15040540c0c1000144180c0b1420394910880800c00940e420180420594003103801c00d109558a4a0004104400101d504928543d00400c2041208100000080850305039100d5404a0900412a075110320050350800c030703481040da5007401144c0c0000c0c0300b48103001c01402c040c034042c2814010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 546241771 1250 546240521 546240571
    0x7030e1504060210050f01140607021809030a0e0f09010b281709010903020c010518062107020a0201081501021c02100c051204030f020f031201140103150608 69
    0x455004540180c2094403004d40b1092140140350b001500c0801c0131300f40e5403501e16040f0342080d40426080c000d900104005041d90380b000b50140d41d0383c00e800141038181c54070081294803540080122000700c0c0074440c0075061810310300c1c421035003150041c001e0034099081c94001443c07600442c13207100007100c142e04580328a01c42111741c8455858191241080d5030f402800c4440b2600008203486407580c901082c450101b5800902070f41d400342c0a00b03003180d40d030100c0c84013081c908034081c000e550805400a42c5140c890810424400d2039100850958169164001e040745c50300c0d05120b02078001103076040030a240c1006200070810420050049402d480d885041d5825940f841a0400c005608104042c107403d00450090361030603043c40c902545412510034641040000240c805410800c0c50003884504034001c00041c842c50300c02e41e04980c2c503007d4000d102019103001740180d5010400345203000915502900400c000313103580000d980c0c440741c1001012228114020061101804a540380704c2551203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 546243021 1250 546241771 546241777
    0x603100b0f070c120b04020405090708120703230403030513050d14060c040536010b0301081c0219050c0d080c0d050a080a0e120a0e01020607090b07030e15 68
    0x65110202d807034050a0510700e202000c15030103a0405481c40510342c001442030244564456811200041e81e034841130032071864240702e0340040f507481c030540741260201901c14010f001c81c14800d555141c2c52103400c01c3c1c0180c01004540210301090020b02c01480003c1c0a14041e11082c0d01c0406442501641c030740c00a84030140410090310396071490054003440b080d0500c001075121400c204041d107860f2425007c5071004a8041c0300e258035108691003140343c5a601c502441080540000e1034074a56111140310030b159200f031044040e50301c26501a1645040c000c01003c03441c2c51590083c04148030302080490000103081c1d011120341c06402c1020711aa5922403030f210ba600d0141c9131464841958410483c94000d00c03201450600906010b80c0003901e40c410401380d8080241c0001280c000c82c00450030f0b1425a50006901d90740002052000301c0540c4061405002c0c1000d03803c0303c203143c4440c1c07416518000305000d040c03603a0310208401ea021034000ca40c6141900d1000d00544524296800c802215030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 546244271 1250 546243021 546243037
    0x30c150210020f0a030b0105030c071e0c0621140c070611040602240606030c0c1005070e090f160f09120b011d1006080c0706050a0c0216140603100b 65
    0x83c0d0045404168690b041c4112036006200782046440c60618121001d00c1c2e0007050f07001440340d2515007510140420787c18003e03403440d81c0318000e035410380d0311000007510901070360340e00520001d10780c903600d4240321040c050740c10451000440002161038090401c2c0040d408002c080e0380e40c9440d21284166400008003e00013401d081e80600009440000a00003141c40c3c040d01d0811214680b090091650b9540100c0e5044001c18072131a81c0e4010320329080d820512031420b524a2a85420100401c0d585c01c801207080743c001c2216054155615800fa599105006440340703000e80d11002040540d990007054050103042d12070a0201019a6850a42a00c11203c803412224025031a004114018508001c412074400100100035036150030009200c40354414800d8604020310140400d02e07400501c0c04413143d184c2c0010003030200b86018580f8101500316a01d005005124032950300304082c9100ac0c2e003030283c0d8203110079400c06410f190b040111a40000c1d0685541504540000aa12010400070300c405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 546245521 1250 546244271 546244297
    0x7060b03160f140306012610020304020405010b0a0806040222030507140618040207151a0906010c031709030405032a010c050607031d01020a05190207030c15021002 72
    0x49040c0004200340d82e28980c880740c241201043e05403801c2e640414042e0545001c13002624150078807182c0d40c2c4a600c141c0402c21024080c62100b00e0840c00f4980007107205900a072007d0081d40d0b0380f0900303c03046200c0c1c1d000c4100003680c41c0d00480c16600d415001880590707515907800c0300440000740d4007105841d05510884155000d0082040300305010040140c0010040314014105000864144018401c1c00c001e2481181c1c005112820000c442001800d50003400e8020000750302440d00845c0300920031618070348200720450004001e5031141080f500f40c1039140d07076070700400d80945142150104c000380680074980005e20021030740c0d40b010000806000c0d003903402031540803008280b420b08440001585030405c50b0780a14140820b01c0000c1c0c031908016546000034034481004241e800c41c0140ca151100b00354000900c7c3c1422950010240480b101d004503455000307034030210203981d10700309448020225800e100d0200040310b5003a85088260102d40142ca209401c11030541040303901c002c9840c144 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 546246771 1250 546245521 546245563
    0x4060e03190e03011b1b061107050c01230f0310030605090a1712010b0309010603080a0327050c090c0c060a0c110601080622020d0605041502070c05010507060b03 71
    0x5858240103607040c18045181060510810b00002841109514034502d00c6c1801c88541d0000c0000c542d210b000d1180d5a110000e03151355582c0703080d0b030321400807007a4180054901604000b200300c018524035503150030184031510b0720500410015990b0002000340c0111018100000003051140c05490300c04c0d64108050f104200300c40c50f03d200e1103410640803840030001072210000006918443d141510804410303291030780d44803100d00c0d0140c82a40c20052228101265003602c0e190150040c40d1040180200c0c3c4400b81c4004c010a41d5a51030002c000e08564001070042c0740904004c070209410540004034180340c1401e48c00f00ca4a841c0060b5140000280c0e10300c480a01c10754042c0c0407190001115019101d59450062426910b24018040300744605050041104040745204076207021ba90192100c01000c034103080c5040180001c440c240c8680031701483c0f0114145072482110110f6a102010000700b0742080011202504070803000ca500540c1c0d900070340c80540c1d08100e014445d80ba00b1182080e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 546248021 1250 546246771 546246797
    0x70f0b0319060506030601110a1202011a01030e0d08060a0906140934050903070305060612030c0d08060622080d0309020102250b0c03280804060e0319 66
    0x300790840d032050103a80d0b441d0180a100c10740d02c010480e40c0140e000d107810007244501e01407013810550084002002d0000c40360300b840a440d01900102007100311141900240780b0040c0040d01507034003a6400742155040a4072a210f1240120600c64020704041c02085d403150f16010502c044038000d4002084440d881da03900305241c40c1809580381c1c0852130841c1c0b500155140e21204c1540c0001508800d40a0f420b180d1441150303104509840500b000101100c0141d90303a400c150b81c49410545180b40251400e190581c1c40c02000000c0b00e203007a1980004008180d403114044034a81c90140009500c10003c2040c5681440b01c1025030001d07106414011060307920301000d542c1b400740e103a039081c810b1508000784000980c1e00400c0c40c000801602040c4001a02080d03041e141035005a00101556030700402c101000103c00006840b2a0440300010100244c0d4042c1d844008806c03e05100000303100c0000150000d1560f0b00400035422028045074100340780308151150324900c901c803040000f03000c410142 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 546249271 1250 546248021 546248041
    0x170108160605160f0203030906131a0c0d050a0309060f0b0a0608011202060711030f0a0c0801090804061107083313030f020f060c030118111b070f0b03 66
    0x31004002900788107191800d00103004490011650019110981810904055417014003c071035003550002d080070703504c096402d041c52091a8601440483e40b034209454804108640116055840a80c0090040c050751010803903040d0300c00e11141003010f89542d0280002070203409042c05004000f0781c00700b1070900c1d003000e02603006c1140e803181e0300f000b02c010010420340250041940100c0d4040c1e5826030394040904042151001c01524240c252003120f203210480306010880307100341c80c8280031207565155a5098282a10301242c00980704100030403041003c0e5000d00948480c90150f01c007500c490603940c0360074508009189201c04e08641000d824440f454a0090b041854401411440206418401500440c4440c0864007d042c48a103051001e0303c14000c201c80300540313014004580c039a1410ba040c0c4401a0400c6c465a0861a014001020959514040c0c81c0e920010f040c5280c0c14040300c3d51b108810f99001c078030320441c80d02908401081c4808415040b10284c400c0c00c030540c0c0d990603c03050304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 546250521 1250 546249271 546249313
    0x306082b08042001140c0d080c0708160f020a15090914040f02010903120c0201110a02011d06040e0a050601090531020f03040302010b0f040b0d080703170108 69
    0x1403000c0110079010803000818040c8610078292840d2414190202c1220040e585440c0214000e0311651000c0303904c42441c2c600007074080c8456815981d018058640321803010050040307002c000c10123201444a401b103544130300a1450701c1c40c045d400c0010000d040c0d4000ca2201010360300002c8560f0f0b907045220b401160403414290042090103010031940d80c001c8001803408402400090903581510f40600a581c401c003e40009103811586500614091603000350510448550403404151800c5c50040c80000103c2d5640d00c00e03406840314010303061a0668900d180590035a1030f030340001c1c280030100d1200c0b500101a0b12449803131000140500b0300e10009031110b90030343d1044e442801c0700030f100d0b500e1031654220075119400762201d0519070403040d42942c01a000780352503061308040c040200030500d9415040004d5001301940c0f009141040d4a0a200a480d40d902c401c6030440401004000003412400007046d17200d010745080000d0340c807134017040e4204202c2a44007861580c08118140b17400700e901c9040d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 546251771 1250 546250521 546250603
    0x4050f060f0a1208090103090c0801050708010909050606010f05190e030f160603020d1815050a0b0a170703020a06080907210201030c09051504030c0f06051207030608 73
    0x80c080425241000c60003e5000855004251050100f02d90102e030b40079403c0301c80d071a5030180301a01100c1e1960781b5140200421140b0724005040b41000094081c058822440a40d812034043c0800d40d503004015940607103104440e0041001c2000a610035602c020382d20024034000745c0c0c881d03c43c2d0801c0400c152034441c10b00c03d190110b8000010405404840404070b9089690a05000d030300c0d050b203d0307100c2001b0021002c8480c1c140d18408180410014034502c003101003070924004202c01d48801483d401202c1d22060065000301e1005410700a510300701185070031901c8100100c540c6182c50ba404615500c40b154003034404034500b07909100b42d01d2400c1c850600034041900d0880a41040c0c02c62003c00c9409d45500a418590b070351092000382441181d05a0240402503c201d011103490340051902d54130901c0709841007064131402007903100c0c0c0c414011086505c02c0c0d941c00e0810140512540c90f4400103401c400c1416138039000024220820300080c01c0b0700550080070031450b144030050341581d01e01802 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 546253021 1250 546251771 546251779
    0xa0822050f010503072105040b16210f0908070b073e15090d0306050306062b121d01030e150a0e0708160501020601140d0c030204050f060f 61
    0x20080896907845401c0c0c0c0d0740544035142c079a411201004482c000040c0303000c6c0210100d41400c041005200e81421207074054a5200e80210300c120f1009011944540150b6001880c2c8044504154003e9029080078140d46216500000c1001d170710780d1074203a41c1c1d215641c100c80d62941c0b04108040c0c00d0700842e0784103a86440403041c49581c030000a0030344070890b0888001c6680c80100903890390402081081000c20014226070102a050402d0b040313179039510b518542c1f000281060401308040c100881c1880c0280f030040e154003401e45280a0303181605040399014003040c10740140310008941c000400c1d11000e10303030b0f031940720300400c0403000c0100d400405000c590515041c00d00c111008a8006083e559000e80c1d0303c000c61068544a410002800204410000c103100307501020440c0c2070702051518640ad01c100040b50f00c0381d910001a62908400d2040408035402e2240e502014108018800402489082c180c0d80d529100d9000808454059034a03100191744907040005c01d040c2800e840a20420890b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 546254271 1250 546253021 546253039
    0x106030b1501081308030408220f0501180b09040b06030103030302180402070f24060b0d0608150a09021807051b0118020f04110703020d020106090b060415020a082205 73
    0x3005004d01225820005091100010009043c05001010b4541543c03040b0100c0c42e0742c996a8281c16107025a80c091803e4905c83c1c42e20000b00c560044040098010030003c9401c000361070140d071030019407c171900c0903800c5503c0d804080c1c01c940d1540d0055020f140300392801a16146010312010000c10081d202c6802541b0400014001c04c20ba50054401c045d40099681742d0980721540c1120004c404c40744102020341403400218000022401600190304200d0040124955604040782c1d100f10303840c6002d00d0001004085000c5080b95040b401c000d40c0003509000c0d0300141002200000041280c103440020008a10490145012090134008018580c000c5c00301041428901c1c0100c076000c00020b104001105074000a40c82c0e94000300913121000545544403051803c019455030b40812001c0015481c00c003011511070818854a074031030f00c1c00341c500b905050608925501540c0c0c90341c100e20a601c00d100e41103001603405030040c81c030b0243c080036480307a510083c070b0081e00445280d003010f48074550324 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 546255521 1250 546254271 546254281
    0x2040e07080c2b0303060302090a0b0f03030301030221010603150914070302060301050d0c090203040807031b08030105040203090c0d03030b040b03190602031b13060f051303080f0c0106030b150108 86
    0x41c583c0d030202101810102c800741800c503d0258001d180ca544002e4000c89500100050703000c0a60045810317240648100c0030501c4680c007010349a2000f4040250311036003d50400c1d0f80940420403100501180c540005011038503604c1310070103a0350286145040e01d13152041d0340b0802504d41010154055614000d001040c1036a00044a5000c14001d0303d005114001a040a000d0701c030185000a11230b0041c110361328100380c02d1003107041d8030180c410744c08541d0100c1901118007100761001034240d04001c0860940e402e2104000107944050304c0c20380544074401800c030169a5260010150900c2500c00003803108041050100b9035000207038051194210f61000b400392504001c240448585c007030001030b541d6442071948410101c420002400c1c0c2040800c1c00c80041c01c8815881064074415100c08d48403c006840841c2c4501c51405181e9140e05100e4041002528170b401074036140d0140c902c858101182c280140b405c40b5290340c810749102120300c040c440700d0b01240c070108040d41020311f0070321050710300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 546256771 1250 546255521 546255559
    0x417070308060114040308030108030315030a050d030f1d07030209010b090d0204090201051306120f11091003110c0105041b030503160809090901050709241b02040e07080c 75
    0x8002c01c02070510a0900d52113854440000031100a941d1000d4025141e5131250400b980d039400440d4459082c00c2e4201c0300c1d2030700f86800140d10741c902d80d001008018144c043c510440107811080340304204940c5440450792500125030f4140d20b03441d120b800410b015072941c01000032030071041c0c1c4800402e000420541381d09407a8014500d050540640300803031510042d2004031130502c00e07a074003600d04518a60001c246a5071011802c40540f211080507c03101c80440060780031644d00007058145000108039802450400076100104051541800145500d00900070b1185501220000e45c1d16595981008200310300e507410904c84000d0302181070b0035241980e07a4665039205042c80707114101c40791080d48003001008400c58190010280042d0f41c00d06007c62a54060300059440b10081550694042440d80042c95102480540e03050404240082a0015901031003441040112030014140b62030240e151030007400000f070228002411f120b8a08400c00e030034030f0300c039054082c880c070b040447d03500ea6182 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 546258021 1250 546256771 546256787
    0xc03052d0a02210d0807020f07150c020f0a080a2a181104060f030509060606030c130518060a0f0305060f09190606060318020a0e091e0604170703 64
    0x103415a04103c0981584450020010704102148220b225103004054455400000c4034080e10342c6808548400f112034502c80e031580c44500600f5035042800c440d808a562143c08030f8182140080c0400442c000081d0200e007600303010b50018070702c66000d5070070001045041e890407103801c020185600d40e40c04500090031840b004520503c21640c0c40c0c0c0308038101041140d441100180040403186e6a00d80d52030001401104211044001080c50b20002400002d0701003091849440c000b0513003072843d0b07075128045145402041000c1c15082c0b2180002c42c00e921107802c2e0400a031b080078104441c92030480100102c014064010303a0100800c840204002a000035901c3e070803c2100400030043d69550b850903160040085541f06407007006011902440840c0d40160140c0b01d0959051110a024030201d02040e188031070001e42040e0007070802c004010003045159001003007603055034401101d65015041d01c5075951040080b0f40c00c510140f00030481070228403008100c0c1048a0307820410300d9140500041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 546259271 1250 546258021 546258023
    0x2130b0301141002100501080a02130e2107050601030b04120f080601050703031b0809011505030a120e0d060213050d02130c050409090c090b1203030c0904090c03052d0a 74
    0x1c00001c0000300324000c1c0491785c0600f100c0d4104104540c2e50302849540c841d0641c80580c0540b80002d0700000780c4030700b800b0f080c503644840b2000f0950284544125041203076407401944408409021a0001070818070800e40258001c0080564a0609003032105110710b5504000090240007100c21158a8209081e10350002d82404c0a17a151440da080680c0035000c00ac071854040501007000f0380f4859000a255030146001c41d000308000d2016100c000c041c030a1070f000d9264158007903034520000448803052000d40c002c943c80d10140c081800d00c04034481140901023210003e03004962105030748107040d10340009000c2100c01c0758000d0099004116086c1780040c240d5039043d129036214205a0040c81240c009002c884403c105544c640e003004520b543d080d0290240c42c07403d00e9540e000170300e4a203d4450908050401451454035604482e4030740d9805080e41c130350407548460a20002c00c0f02020180002c0d40901d01400012140a10a080d110003c03606c0d00501b05441500c3c40ca8524001200aa21 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 546260521 1250 546259271 546259279
    0x40528030f0206090406090c030605031605090915010b040326070f060e0d020729120711010609050f070c050c0f01021207031e03020f030f13020d0602130b030114 71
    0x5078060b0700202c0c10911036803180b1a040745c1802000100c0c10103507446000342040650701040700c4c0d82c4170800c054880100079007550000c292401c003840b140c41c1107055250010803001c11500e40c5040082c080c50b503901c09902241c0541d00210b000c10912207904811201001d260f164585596882c030300c030750118041e186010b80084081c510f020100890f682c044008a00d0f417204450901c4c1001a00130b54503019801000321827800740964008020714144d41c21841800320f000c42d41001d000b02c1e03070040840c40003000c5004201d010340803503103207031170071300c51100a03100c4000042600d240c01d10070441c1005020700411f04020a880ca00c2e80807079000700c1c0c20140b0400448514010f1482d020040b40741072300300038007031102e41d1002400c8000c142d002604843c00e010203041400a45021160550407802000701d0740418140400004030020302524040390704c0400007031030324034400312600031a401c4110480112201e550008400c00081c0ba01c8000d03000400c3e4401c00d081c50356040050760604c5140079801c603409 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 546261771 1250 546260521 546260543
    0x203030a1a03060411131404030309030207120b040606060c1709010306050a0e1e0f01030b040f0b0a0b0319030e060306010e0d03050910030212060f061308010204052803 74
    0xc100044001c11004000504071100e0b42000e040495814850a4007607101c0c0700c0403e02d80c0313003408480c050320301061044007460f4050390b02c40e1016400342082e40c80072011405a003c0124450102c103800310b000c0d6004902000039450b0614004048039a0740d048001800354040c071820000380b07401d0250508400d5400d035683c881c1112030059020340b04a4202c031313074002c50000300882d0030710407001160300c00c0300f801205400c12440b4000c002c60f41c0c1015100f02030480c4070036005001141c2d590b02e400360081e11a4016010144d055100c1d02d03505a0180c8500e810b180d260403aa03941d900d42089125505104445100c0c5065969038029040c1c10b41030310414003921011000903d668020f159010813080c002e442100d03541c041d80f50051407030344030413000c6c1d00c520203898540c4e0742c6620a209483c7e4100a204d03c0860b1a2140002c00c403c500c202c10070382d40d1207407042192000c6101880c0417440101a41000540c0740c030f041004100030304000312006110103000202d0805003001d4802144100c07038200404000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 546263021 1250 546261771 546261791
    0x20c03370615080313060c0317040f020402030f0610020d120f1826040b0d020702041506020a05060f0f0f0a0b04090c0504050f010e180703061b120506010203030a 71
    0x41c01c040800b102c1e041c02c2142c0006600c0030040014685000e00c01c2400000c07948400e029600040c1140d00070300003030396090b03290300b500354031278401d6810078040c0b01000e02e038081990000c1e06070380c022105009849004001d20146003000d00c41c03119138107810f0001d0300203445021401414450b58802c03410030036444040e600e0540d499680194110b800c2c5020941611615050042944c0300245404500040c0f00c484000b402c038200303050310290360800845500c0c1c80700c180c55100c0a9009204240d038810350f66a201c0c106082c0c03581e1258020080ca401038070705a0841c0c10481c0c00c100b001820046215000700070031824903a6080d11310303400750009022800ca901c03100d80c800d00400c04c00a090303811a240c00184800c0c44007094884c03040b244100c805000f030f0b5890520a090100c001c0c46117501c1081924040342c0c00e2000d5000c2201c030500948200d0302c45035983e0b01d82405940b40d050700140b4080340c2480d441d042ca9030040700107061340c500890501441c109207000035075034440142010201e40c5d031640305903 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 546264271 1250 546263021 546263033
    0xf06080c010f1b0f1b05010e011214010f08070b090603010e100e0a0b092401030209131503110108070206040b070c050d02060a06080106080c06090a080d020c0337 71
    0x1481503000c0c2e00e071443c0e0309889140c2032454440110f02a241062401e401c4094201040241c2c400e41b031041e55141103600b00c00c0015100418041c58800041ba1150308503117007450300ca200c0c50b00070988400350b50012071a01507407d040143e40d8118800c0000c04002940c1c05850341c0017100d04582c0840d0840c1d45c01e07070751810600203007180c5400c014010004802401600090340d0800481c03482c044500c040030f83c440010a0394904801a8170301c16242c110f4808038143d6010740c1c081d1084880c0a8201c141c0c010340000354034205c132518a00d00180f036032031940078000d0209004106442003000e0800c00d656080260b8040d694803c0180005c11803c1d103100001d40e02440350b402c0c004070035400340454a290b4214070b406900c1d10b01c101c440d803210074600400091519014007400045a84201c090115280341030180030040e8461088a9001b108005c80015003003010080985a1001940070744080b0683d44101070405648540e05001e20340307165004658041810080c0200c3c241c00c40e100c030f5a61250740340c40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 546265521 1250 546264271 546264287
    0x6030a021536030c101e1107060c0501050a0b150706110d050f070f090501050d14130c0b071109060d0203120703090f0e07110a02030d030204090f06080c010f 69
    0x81c03082108158005080d480b006845a141c2400c218140c3d40707080803840902003031114102c2180005038402010307085400c100c0101304480c00356481c00380c2907801510032642c58100c0700e0340b00600266039801e011041c0f0000307105007904181c04801c1884108031032000508c02d40703a901660050800005400d10822010b0790107044d422000884035521800c40454810040900310b503004001e400820014001c5072103000b040b0710101d031a8450b102c005062900440b0560002010000d94070307582d1003140c1201c1400a6003e1150110300401c50304101c0c0340c42d00c0e07046209030340e1011190944c03c2c021140001c14900102c520301d030342034611900c40e50b02c000c000346060b0f0300f420029426024201c0e81e07800b100c0744e0f0002460501d0190325840c00095480d4502ca0b5544200d201d2009204105008626464030407101405d40460800448005500c203400113410720010551850100350f00060400c80031419005034601c184145504011240c038000009881d00388211415040040e00c4030119485d500038804 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 546266771 1250 546265521 546265567
    0x50d060905040b0612060925030f2a0e01050d0602120106020606040b0604051e12011a10050a090506130810021210030507090504080903060403120506030a0215 70
    0x8140031505060400c3e0f910310806441d050f01400c0490070a00d4100000520b2a0190102e04010a0810b100310307040a143d580d5110901d08407a91020b00001203107000095148442c00342c1e07140e0007400d91130084042c45003600a16603d45150041c03080124415007d0038504560f429a2110038421451030000001e1084001003641c0c0c0317078080c0000c91003560020b005882460256030400001c0c103114200006805980b0403e035102c0d400e014080000762440800000b06500074001041602c042400c007800d4444110850801c01c01141c01000289441c4da01003140d8602424103d16064202c2e000600c1da401c24043d0b40e024442c0001c007803164010201c2500028840b9409403141500403811000203948000312001c030301401c04001c070b0fa84035402400c1c43c045980c44001407003032a25017402440607100003001552030031000d1103204030a40f002d014a40c8220312079a611100e001020040300101e4101034103c2e0701a5010041901c01a01c0d518400d503121402400c00d17a03206d904000c02c103094400001e003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 546268021 1250 546266771 546266789
    0x1015050c0f07080111040f120812070324060e010e0a090e0a110a0b07030e0315070215070305010b040303120603050a0f050d170705070212031b060c0a050a050d06 71
    0xa80110701d01c1c07000c00e04905a6420b4402030050980ba034166081c1c2c3d000d6030181f105103070003100b0208001d4640071b8140c0144c51003417409038101041d040401018280458003100442d48070b42000440030300e82956803862551400b01d90704558200100204086030f140185810321101000c2001d050343d800700440014002c941c0300f48403031222100f020303440304a0b034901220180b503d08a100080d2400a4941d4240c48114412604018041e1802c070396800003480002d416010742800015015030380003a0720b1240140703400801550250500b400090300c0700420031401c05107000c1c010300a00b02410226800c03070360103281c890100c110444005c402401c0740c4c1c4c0b00a0641c802d070740060040090f90b01d40500c2250295041c0c59644459070001e8440590800b285048155003800007130100f4050f0026104240c0003070a030942c006c0c50420b5041c03450b4004030031610f00201e1200f00504200080102e168480010300710f4600340383c1400c032702401a02814200381c0602501041c580e541d040560b21032402040c12070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 546269271 1250 546268021 546268033
    0x120504031e0509010912050a020d0615260d081b0c1504020315070f080a18060b0f0d020f060304052b0806030a020a0302040518010f0c11061015050c 65
    0x10300c026141d03902a60003e804610744031400a9001501005d03005c82a410a000d05440200c1d642002400350800c901158000c0e544c42044003007190081001002d480c43d00c11482c44042d02081e0140444000c1410807400d41c40003c48482482d80080715a810902030003c2521300400721a210001c0d020b01055000b0b244a115691200c080f124900c4a0085001340e0a07520003021406942c03004d00004c1703039a88085a00002c54501142c41079805a42c0300390b06003c0062032080da0240d0380b0f40440d020400b40d80340340d11402008a5458580407540c55082d04840f07114031048a0760220b00c4c01d0107002441c5100b01d40210005044c003509211484480d080c90380701110072004412004820000c45d0b1441001401101c00521a4280000c0e4000d10f207070001c005103140d5103154204409020014600d030038050641d81c040202030802d00445c07202e002c46980c0820100e4041c0350050860300d4000c01c5402d29440300040c0003a203000e05003c14152100c1d07900303907450141e55100a580510038030b40c1101281c4521 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 546270521 1250 546269271 546269327
    0x1109090c01030c12022808040812070908031204020901050303040e010e040318030302060907060305010e160e0621250f20010203040b0a2705100e0d09060206040312050403 75
    0x900c1e02e500900e251111401b640141900494958104440041100e002080340312001c0030580c1e4000d81c00026450416241a243c00c130340c5007950050b0340741c1d690486140d0180021480c10000241c003602040d0000d5003031514100402d0407400041c800c2c4038010360800d02043c10f05100300d61000242c0084c1000c411569501e286c02556001c045418020901808501140e10f900c68040c00b4120b41c45041c0402e0b10703448498109803010102da0140c428000311882c18081e03610342c40043c04071004401055603410b06075031108074031071750003d000d42d28070030441c00c1c0c3c8211300704800b104e040043c945281424404000c25000c0e0386000c4211030440e00d003440c0ca95a200340110540007188268410074240406444080c54441540c0200a211202340014481100d1510110300c044a065000300c040b0341030079142001c0007007114002c40000b41150424411206815000314440000b004640f0041643d4601520001c0540b00000004038226889001003418140708800ca0402e0030f841061001d085414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 546271771 1250 546270521 546270547
    0x1140d02010503270703141504032f0c03010b0a150c24020322030909020f040e010602010c020f03040e0a0f090b0c030121050307080a09030f06091109090c01030c1202 73
    0x1d00e210445e02942d12280c060301c0b042d400b050010000e20491724000113900d880d0303425284c00d802440c0b50141e14107065005550714034009040a0b40780c0c1450b0240c41400d0380334040c5425610b0601e1842d0003540c00050801041054102c0003156108074901548034424920741032034100c0400031840850381040f1802d2410200f1580298081c5000c004181d030703403820381500c042d85007901a40190200341c0c0c0080800080b4416001880031a0401421034038060300c0da519118200c40a801500050707548050701c1e100e49070100034080b901203505000710b0a10b0310748000340d074940c603004109002071f503255925202810b034250400003c00340d004413502c8640c9080f203d00034141c5c209210314680c4510520190600403003041c250b075400c42d0800060362504a00c0d803192006036000390290420012074510000c00704410f01c6180074a1446244003051400c0e842c1001110281004081441205c50109016506030002444500c418003820b010410700303090041030700c0c200d0251010f250f0070781c0002009051607103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 546273021 1250 546271771 546271783
    0x100812161406010e07080a1a0909071208070203060c040f05151603031401210b13081606050a020c1902360f1e0c0f0403030e040501140d0201050327 65
    0xf0643d66071b052030f07905c400c0394009446042c0400c1c04ca21081d660484550704011940c1d951000758001100c1c0103607a03e0001c141107107540f034401c1d070f00c003800803130001e04616003070103ca6003203000301c15098142414400c0e003034030791021485800d114244943c03180303a500b9130450a5400c81d4030300414200c840ba80c00d04014029000b4240c43c89103020f0f0744070002c540f0814003000d0704410100080035500d0880070f684c0710344100101802d0b030150b0303100c081481c0001a00e018014401d5078003440b108001319a641ca0304d0403e0303804c05001d010401e070040c0004800b000c1300084200c1c01c2032080e840700700125890300200c5d001c0842c841c3e91355405961034061112407130403248c01c8074402114400e02070343d55032461102480ca032000c0e200001c640305480c03002c0300b508175010402600400030407251407074800c6c0f01190703a8480d4015801140811100402e40d161403400d0f104590040c9503001500106100c580300154486204030f50090502c680480440c02e02c5003514014103800c20b440c80e40c404014074141c2010381d650 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 546274271 1250 546273021 546273031
    0x507051309020a1b0f020d1202190f12112a0301020a080103240207060606020c030c030d1103040f0e04120302072613030b100812161406010e 62
    0x120390040011004442d1084441c01030183c0d035040840241000c0c950707001d40b40a5000e55981c940b502d00300c4096500c846041c48018490844000702c045000c80203810048212400204001e2105040d00890002720b09130282c103501c0030020558031000039042d50a0608040f0003603803842000300c44040c48151030085405481504000301e800c0c11407404141c20303481603481d0a0002070299004000040344a0403ca050b003c001c00100c6440615940c0c2c0c80890308140030903556a80c40c1c3c0130030402d2580500c0350250a4030103401501d600d14140700403076a60803510400c01c0030800b00c01aa2400508188151000380c000c10b4484200196034410740001240c2c1900d041d100d4081c440c0f241c200c5140244210f41c61158801ea4034031442907610300792800c4d5001105425030308441009000b11041489e0010300145106606400ca135040c010407441c146a01030300505181c1c5e00148204240f61010001d40e0b528410744518504030000c0351400303200c5843c5401da980d17a40c1c42200008200010b00340d180d20701c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 546275521 1250 546274271 546274297
    0xb030321010f21030e0d060f0207020a140f0105030a0b0303070f0b16090b130e16020d021f091a0a0b0f0a0b030a0c031d0c19050102060f1009050705 65
    0x159443d003800d4084030129071402484002d0a0310003c0000340a004100546003001b00804818403843c0c5503682941c1e0500e02514010364002075810441c40c0500b00c0d40050080c03030718000032007104a070109510055001945052003c080001244441d0a4000a00020000d0141c0382c481c509458442e0b10001d8220048845000c010f000801c1d42e800070049480d40d541564540740407502d80b0411500070382c420322001d1043c0400380c10104c0d041a845070124000c80c4442c1d01440782002805c4002c0c02d0940c0440e120003190040b8140c080415a070441c01b0f10003900010700015500007610300110300020b2740301c01e000d00704828810400a080c0b1030744640100d141c160b41668481c400302c010403120605900402c002c100b0b0a002090440c5050ba020741505690b0703040024001903c24825194040c000801505541c030940c40c0820f1030510f110204500072a806140041d42d050400207515820001c00c8034040d0405500002c091449151082008000c0340c070040065040100303000300540d20040014901d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 546276771 1250 546275521 546275549
    0x612011e0606080c041a040e16020c010305060d140a0605130605010e010b2505032b050c0f030703091b0303020607082517070c0308090109050d030b03032101 69
    0x4250300804945110b081300012243c9014105104400c00501c0e041201c110b10343e05000119a5101d44110540520380310748022200b00e01251000345480c90555041c1d04050a12013403204940741d0300510040d281d440505448094550300803145008041a0040d101500309001d000340c0300d11b148850640c42c0d015250501c466a00d49401810000084c45498420b007000c0001886400c82d03a0302c1d510150003104020f1f440e4050a4996a155401a042c024541f1030103e12601d0135251481c0e07071121600c442e6030140031600c0c104c001010300e07000b4078100050b4880c00000040c1910b01c00e80c0a00201c0e540375845106c0d03058041e090902d0000030303020440142c8101c20129550901880ea42071045603401c23640d00303001c81c0700c00300d40708181400803004d800e010011003c0c00c5260400c00c202d500c540b14a44d02d544071003005040c01000306801810740140e6914102c1c038032001c07502c0403802c281446414140803c65030305010104e4594440da100d80d0a2a0b465103881ca00b1400034120180c0c103c0c1e00d03443c1600d803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 546278021 1250 546276771 546276779
    0x3060e10030210050c0109021306090b0a030510020f040b0301091d010203090c120c030a120305070c050a020609060903030705061602010b012111040b0703020d03020414090612011e06 80
    0x405003618000650320118043c088032429100e1401002d100c006070001244110903036001c81c0d809035038a4003075034026403a80c03000c2c0b10b00045441000804402240d21150351407850315025161102007408450b003a800141e05000b0100e0724084600030700c141e00000303540e50780d074081d83c4000384025114071024091401d418400d00f030381402070b280540030200c054564030303904604005410b0368074003441009005070507884201d0366080c402c2445290158100800500d0741142c0142254402010754003401601c400250109000141c1361000b1541070f920265996002d03000a642405003241d815454070001a001d0108403000c00e4072402130441d009004085070300200c05030302342c822035580280000c20b902d1307541280c0b801d44075000702c1100150350005104071580c003e9031400c0d030058011a008102c009410701c1016810403100040404900d411070926091800745e00c100c8610250a0344504581008141036035144014900201c81c060000c006180f041000c0034032042182849810b40d610f002ca0000d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 546279271 1250 546278021 546278041
    0x1504050a0f030305091e060d0e12040608010306050a0902060a03150b09062a03071214040e0a09021206090109030e061204020603090304030c0303320904020c1c03060e 73
    0xa0705603581503d8a07420904240c060103ca10001c5584444116280840070180e0726040e006040c40142d4140c0030405124240c8010314280c1c545090307125030002008100700c0d1652044095054076402400031501d62101c140710301c0507040f080c0c0040d50050002030380031790542e05540b001004a4021a180320034903540c0180c00d010740502c1a241703410090400484161801458069100321601c88082050310030308201c061558001100c219145a141e04810100540002c408030f0940359001f480f070b25280c1800313003040c21783c18080d00164055444089100c00c541d200c80328071000c4003103002280d4291503c07c0303c0f503018041070b0b8800c3e0041880201034102174288402190a040d0178216178032020344640d0309025803030b407006118031500d00080c07002100040c8865180c10083d030103543c030420300c3ca0204d90003007483d0025101c50601644840e00402d04404144141d610640c4211001030300c400c4440c43e0326003440c1c1c03001c1e10236241c240b00030100d1200541541c0848161030500c0c48200a0ba80c2e649101d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 546280521 1250 546279271 546279299
    0x6180c090103110d02060409050405010902130e0307060b060702041e0b0d050705010c0c0806040b19140708060301060803033c220803090d0305062b0602091504050a 72
    0x3419031400407919031400d06019220f400316510192211f8641036966010000700d8400780c40464090f5110741c1c121096140014949190030400d0700301300400790300d00e829540d5910070340c0e100a0a040e00d4049071030796690741005035507202e034003c0c0c818090b400380840007440020b070800303914010506c1c1041001c59410910203a40c0c3c15503001700141401803c14006444081e0307005002c440722480307440c01145c0801d040c00400d02451242c4084181c80c00d0140c4034800c00c0da002c01c00141081d2405100c1200e00b0210784046070001c43c24141701000e80c40704d001113800741900350042141440000306200302079454005a040c41c4151b01000c0c54050100366a048206d0070000384c134210540380700003040c0e030040700b8184101c030707607140c107211904c04413161340d420f401740e0001c0700c82043d00d401000b510403400307400d0701030140e002ca41210209030602c0e180000e05400740b00d1003190200034200342c980c00c081220302d504071000c41d0707001099100c20200341200170416a21600516008401095002659010a070344e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 546281771 1250 546280521 546280523
    0x2030706022a030708030d06060e12060411040b04090c1401170c090a030204050103030302030f09060702120d0f05190e0c0603060607021801090e0115060f0c06060806180c090103 78
    0x121041000005000d40c2da500501e5070311039410302885a0010300e801080004016410200201140461608074042e215410f1484600d0007142d4014507000c0007500821081e81c0198001c00d000780030400b03031000c20000c0c1207503418160068a00f101c0c00c0140301060028030201c80740c0242103000c401044004498070b002510354420400c8848011070320807011400a040e41d80c10103805031030341076540c0d0000703003c0d50300a03403060b00465400814840c0900224011a500103040c00040915052a65000350307658000d001c05e1941c440b011481c03010814050b000f400c4005007008052146040128425810b60030466004d8002031400c3d910214135803022489860580d0000e016a0071540c0301c0040c09030035030040504aa1000c1104240d07408862803403506400f910a4001c00035a50b000484031608450807504168083e83c81501c08228441d400b42003051071550501d0070030740e1503085152000c0070307000d00d0b00074486502a03141004803801900c0d40d01c900f02056141100c1269030702505100040000b804 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 546283021 1250 546281771 546281803
    0x92102091605070f0f05030301030b07030b011d04020901091a2107200a060c0302030a11030103020d17070c08060712050403120507092301031413020906130c0305040203070602 77
    0x1040d00301140307400c8041c40c1511701400e5140a6071145541e12411170b4406d0308215104014881031001a5a1601c103120100a083c2406d60403080160003c0b00c02c05c00c00041188150b40000e82114107034401e03001c690060004001d07013001590140074240c0d640e0401070854410071102e840d011442016455401c1c00341045031186203004c01da00c00031408040f40344c007105000d0310600e42d80d000080c900e8410a07107424090b03640183c40341000180c42c001e4030316a199160080106000505c0903944100c44074501c15400b10551042608080c8101a24000c000c0050014645900700252422020032018400c010301d03900d81001c0101c0f101c0c000103e840645014000074400420b10588500d01d038001038010006080002005950384058890bc0400b0041c0f00c030442104035840b0344c1d5582500030040134094010f1142c0300c2c0d140c10100c0c42c146200c24140640300d400b8038001301e00b00340c44a0103800705030103041d9410300c60441015405000340800391001c074040c2c81840c9001034128400700d0000c0880342002c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 546284271 1250 546283021 546283027
    0x415032901031d06090d0e010c0b1303110708070302131b0e040e010e1006171903050d0c0815120d120b09041b050102030910030c092102091605 63
    0xc004500030807101d4500d40310b000c075103a4032149101042016910512500004207000070310004002c00031840303034410300e040c0000060007000086c6100c5c503050b4440240e138075100c0050a24101194288500b000c1a00300380120000401c1281010946400b500d000b03480d824078910400009108680c5d0010710700c100c20440380352100aa03481103015841c281002000443c3c014500441d071400c45110b4003961480b41d220942c07080c9060b2a0740105030052141c070030645000e0301d00b0b40d0215290121f0617a0241c925449480035400c160007101078400c1c10700c0e41c80017040018020b0310060320071075040d188004641034034004401d881c81c0414000e42420310344c0c0d0103000541c000d070700180d0340420300d400d06001850f241c402d0b02c01e198940c1510070b44168001c40c0030452076842000807001c1004107820007811900100702005680e1100c51201d100700c02e040c500000d0b401c2c1c0d00c00013242c4103d0190030540f00c0341d4504208205401c003107069601e180d4001c1316600e000d034403202c001d11616210b40c0c480030042a418 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 546285521 1250 546284271 546284351
    0x6020f071203030f11131a1318060803030c0304150917072d0b07110309061c0603060c141303020904030c0807052a130203150303041503 60
    0xa60000c41c3c001e551590003261404a02c820903110ba0001e282c10158221403420401020b402c5500007040082176400e00d03490191840b08446808083c1c0c0601d100c001140502d828280092b03510400083c640c070000e61707440f03041084c200140c5038003d0f02c00b40c1c0c1c1c0826108407204401c50900c980c81e9110f82c0301c1181382d03080390001c41c44207094000711000d481d05c1034100e44003188103581c00e11500800f0061034200c03c141e044c0d40361100340e00c0700140c004000c000d180401050b06080010860791944400c86045071a00444c0c40c0c0c2d458950320510038402810b003003800c0007080000c59080042901401d44a0032441c01c0b15481900c0759001e000c90080b00340d075410400700090b0405032000d82c2c105003e480e044a8003481c030380b520740c8a94050328088403a50b20807811806606410101094644640d1040d0f8040902c0e120004942256948030942e41550001c085440394003494107003d400203026040d60b8845030348201d9411040e4603010381c000803070300b041d948000300103140c0c941140400000707140da84941c0078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 546286771 1250 546285521 546285527
    0x30e030313061209021c1a07020705041802041d101517030c07290304150b041d0609010e070f0315062105010b030d09060e1f020706020f071203 63
    0x240c3c1140450b09035441e0018000f44c0c44a91940100c541e01c441151105041880d2900400c5203901d0481201c914140c24000ca040d40420030b48c2c2190400c03034001c188441102404884a4004203000b03621510f003a44082c01810040c0c01427501d0109201565142040611018152001e0fa10980c42e28015040e040c046049800e4400d103400702ea00f4103d9040014410b80700307250107450741240c0311804110781c41680040e02c4240111118690001c000d00710b007080e503151425103032541400800b5035150001034041d42c8441d80591440408030190b402c0198a44000a441e40c50a40c1d209219509004810000010001d401c0c0201c40e40301072000708182ca9522f4442c0309130840e0700d4155120b5200c4000041c1c2101558101c3c1d041c45e4007001200d41102185060f0782150460034800c0d00a8004801032800243c001c0444011034151342825000800a18005140c1900c9003003480c0744100d00000303240a165000035942c0075034200f81c0031500038541c0040c41c02d030740c1c6a00b4420010248104258107000901c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 546288021 1250 546286771 546286787
    0xf06030406021201060c110d080d021810050a09080601030b041227060e010c17090a0e0c0304050d0207030f060e0a0510050a110304020906010c080c030d0603030e03031306 75
    0x8081c40c80103050262440d800120000c084e88510b0000c0c01c00141c1006002101c000740c4800001103894a4445219a43d2000c540c060441c0044039203034007041c43c45480d01f8030315180503c00700061091440c22000c0e90302038a150401d54642c800242400c00104c2d1690300044c44c2c1e4180c80c2c00c4107540710a50b4441d85c880c00100c25140340d03182004101c500295685020342c2c1d100202414101d100307209a070802000404000d401440a81001000c090503c0800d0031528122180d03078140300c00725903440c50328000c1a0a10b1607680202006100e1a082180300b14807003000d14062071141c4269040e4040c040c00407640c5480c0c07030001034100146890418002041e6a1010b051030101d1003d0310352030f64813500c03000e003442c007028407030b1207601d4541e410880e40b60f4051082414131104424403504604041d00403c0c0628002451a03043c001103100c14800d000803075047d1001071603130300205c0741d984140783e40d80710190110348400c5000c100000b0740c20b0078900e004000d96400300590358000380d86501d4440708a603450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 546289271 1250 546288021 546288023
    0x1b09040309090c09050411120109020903011413060b010507080f0912060a090b01051e150417010b0307050603040224090310060807060513030b1b0d0c110c0f060304 72
    0x40000c40300022101c1883c018001850040c0c0ca46000d41380c5040c09003c29100c04800500c071f0102d00f0808800b00c0ba40346e11049041d105020b400584804a590129004000d00048250300b80d000350100031020401590004034907104400601c5213100c01c1005441d10300401d5001002030400380000032705080c004002c2c100c0481d00500485a0b1000e615850341060340644040407210344400740c00c018041c0001c0c410740109001e40b007141003155803018070081c2d403806100b0103200c1c0000789542c050003001076080e60068170b000040c1c16203041c0034450050092841d4259180a03014501000905182540a4912540c1c018103c1c80c0300440441034420184115000211700d00d506010a1505031410400282201041034000440070300344074690f0b207407841c0d560000080010420001800243e4101000102d1740d0104004d2480d0322041e017898913074804207031100c070024800300300c5030445803058008018a040310388610341c500c10300b0b400480e03c1d8072981009980200079108a10a2400c010b4002c60340f003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 546290521 1250 546289271 546289277
    0xd153b0c030a0b060d0b0c070b06010e01020a06020d060b031015020d0e060318030a05040e010f03050d1101020c0d030c0f081b0a170403020105010509250c02040216060c111b090403 79
    0x3040700d03580c506d9558a03095540e1509000c01051042c10020103c0d0103a80044c1c0c00d0030326101d085808030000b5610039558000070302030b42d00883c01141410079074201d04058900d0b0a2095142d1400e9450450629200e22804448040140780341207054000b09241d415164543d4410114108003c180300b0b40f07a10203801c111014083c4480248448070909c040c084001c0c80356a103035031715031414110071506041078220b500b007501d86070700c100002000051000824913035800c2081c9444d81c403009407030090007880c0040c040f41c01a4540101c0090345580300b039203c05d449071900c0c403100848a9040750940030448842c980401c0e61520351002c400316030041e2001100070b161800783d0400c803031040700d5800800d59040380540c3d107800050100d850074062407540001c0c81c94a54001d81c0c282e07408094000d0504a00606000c01d030724810040d0340712031f0100c1da002446041d03401610103240c642100148410b4541500145140360051003102000c01d08040d000042040081c146800104020b14403102400803814 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 546291771 1250 546290521 546290539
    0x906080601140d0b0a0510080106050d0b0417070c060f0305270c041a1c05030703140405040203040510050907060203190512010906030605070e0d153b0c030a0b06 71
    0x113603041501511036100e04202251609184c81e12544040240e080b10900d07904001040c4929199110300d1001e294000c0301d480c0881d180c0d41402c2402108540d007855192130f000a010342030000ea6035481e002c44080744d42e1200d068041520443c1181d130243d80460804108400192358130000c020410640c08500080c3c986807500000007508981c1030135501c1d031151100d4400c000407460321a81001d4445446061405404034543d40e075916807040c202c0007401d014445d00105101e03002c0006580c06001c01078030865480c10f20b030a0265450304d0305080e80a0751824000041d09201002c20928101c0c0c8442e0000c5007050300d8082c1440e40441c14644400808c00140b14510350852060202c500074403844500040c020b081d07003850400d58100800c20014000304081503401c6464901e02c2643c42138002040840d500441082480030780303902c8509007072014a885508815080180e4803941d90415807000015464191007800d450360545c0c0314940d41a0040380a020101b0420710b141980500010940c0e80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 546293021 1250 546291771 546291773
    0x2010e010f0912051c02030712050403030504061a01051e070606030803090c0d02060d05090a1b170a0305120415020315130e210403020a03050d08010906080601140d 72
    0x400c6424074015901d9564a400b10390043c0701d101d1086140d82c00240c50614500451008200c0102e44d803081c40740091a0300000140031503100c0d0110356580d82801405000900340750500074050070080d1010b40b41a440d004949840304040f001d1070b204104180c69090800100002010280703504a80d01215940200001c50005100c0c0c41100044c500c640070040d01d82c02d2540100c2d18140d007000c540d60003441180f4403034026a07104029509020002400418a542d401407420b0400d542110300600c06041c8030b210f16110384801c041c44007510180b0310051095840d03183c020307640b01d03805640a4041881001082036061a0846032948907004480032440c030911000e104c412070f40f0866100d440311100000084051031300005400c0c00d030a07090130038032410410b404581d494401c41a2000318226440c001e03098001c0121017910015a0020081d40381b5580e03a0502a40300c19250b0002030006088400204202e0030901c2100160b444400042440360b08044400e002c1075288000603900c80ca240d52044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 546294271 1250 546293021 546293023
    0x6090f130c080609030a080a06050a0311030316060e0d0203120f09071e1502030703090b03100308041202030c101b0201090b16061107031202210108010c080109051302010305040302010e 81
    0xf601400c6500300440d030310a42c40c0401016844041c00c0c0f0382c5001d081890410107980e4002e0300c40162a00f2207100b001c000080c600082c550b100714500d04411101c0d04100c10b041c000180d02030f04030047c103007096444000b03203030700100d8407442410031400440c541640403526031011301c01c156501044038000c5694041d100d00003000c0700400746401800ca0100300c01c0600c121030a840c041d0649101900040d414280705640c081c007058224007807441000340100029010040b80740c41280210341206030700e1380e503c0d218400b0051442500704103030301070702c40c240408a1a00344028000c22040c441c0e95aa601807a4030b130b846142845244d08180d04102c90350380003003006100b0384004c0a404400c142d1990f408280c503e17040c0d040e1029901804407540c41400401e0200b41c200481200440c0f804d50016502c4408402d90840880055800040a8000c3d800440c1380c0d141540b0440c103948aa49501703207a40e136120a2841134170000c484504c0e001484410020055019400142c3c02c1442400040b80400f1520249 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 546295521 1250 546294271 546294283
    0xc0507110f130606020706081314160303020c031e10240e1611101104030503070b010f1a07080901020a02150d0e01020f041211090a02030103050606090f130c08 70
    0x6450b1554070303c0200540b84c0c0411000000308034a062400c15443c1400d11124502844800074003206070483c0310900030041400700c20403007400d1901407240c403503d906000f5952450250759030300a100c0c0d1a04d1481401c20a015840907035104002000043c1044c0902c8014102c00d8143c10100c600401e1006d1003101010001e50240030442010012850240e070741d80c17a5640d84552420038441d031202c840110010107e040010718036800000b04610752410003600c0d00c0d01c202da101400c0350002190050400c082414002c0c12030352001d02d4881007503154220800b55500000444400810410018001400780e1000d8461408140140d0301414100d4011800c907000c0c08203070120502c00040c0519090b0103a204010120400310001c41c2042d0301c0389200d454522841c0a100c8405182010220402900c240c660101e40c50281c10400c040c1002c40c030102c0030b03410070301045419009220018865050480c03001d8810000b0782c401c0d00440e11000b2000c030003800c4110041d502a1168000402c1e040420854 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 546296771 1250 546295521 546295549
    0x50c1c0c0312021b010503060f03190b0712020c10230c040816030b040201080408071b090b0d03080403120204120b07020606010c08030613140a1e0c0507110f 69
    0x2000300b10040c02a0080c20300503003103604e090348264081c40488591303010003a40c1c0c1c410f00c140d43c0001c80c0900d0300c1c0020b1401a00d132503800722151851010008004504c482e9500500d0b0340d841d4200104c10410341c4500303034040c1000c004a0781d4001c60601d414094903801c0b02c0c0c1450380c8010304c0c8074400910083d5100c107217021584a010307490300283c10030000c241004481c5191820800e1140400e00f5640c2d80004900e01500c046d04001601e408907040c00300c0b000442c0c0c030241e4444c0140c03c60090066002c840311580d8032585a4461400a8a0120342017001000403050341c182e8400c103e641d59941e00781d5402404e600c000500681c2880081810307a100601008482c0c020803854000b0b00d0807010003440d001e40141141c6c10440911503403800100204140c1c0c0e0010710484943d0b001b042c0f4988000000d008903d810070440e00540c0612070820342d20b500c50342003c00c10080038000b40c00311b40400740c2564100800180014401c00010000c903a15105007407580b8001002c040d039061040c00000c19507212980 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 546298021 1250 546296771 546296783
    0x1050f0a0305100f031109250305040b06012f0313140a1502060103062301170d051602010e040612030503191b0309030e062a0a050c1c0c03 61
    0x10301000c0600358000d00c00030300101004c0da80150444d91a5508200aa01e2140c02580190046102681c00080481540c6407040c01800c030701c5820a4014044d2006a505031440d00005000c00c0031944251408021881055107010711070036a4410907000d50340c0300341c0d04141e90005200145c844460381103c0f80081062041c40c1202c200c1790302c1008426400c591000c1210340c0c4c43c0081e401002d80128440b41140d400280001e43c003d0844010054202156140c03e008141e0100100301070107040c6007010700c403031003a0031244113141c1d2110580c0c3e14811032114040d2038481d030700690f005600c100041c08801201600206602d40c0c1c0300600d81a1060700b42044000c03a001004014101c40c0031203800c41041c0d44164240304034102c1c42d60507180300094290010401d501c2d4401d61043c54054a140400c01c107014150f181d88100f00c0729010700c0c862900d440c01e510f11202030340307000c9280000a60442e00341d03001340290009103a1281000082d4020610b0603c0c1138500e025400301003400c80c2e64040045001d40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 546299271 1250 546298021 546298031
    0xa0b0709091a0114030c0f03250c051b010c05120a140a091202060c0f1b04050105030d030213090e0c040c0c03140a12020705210304030203030406020901050f0a03 71
    0x1119040a903006842841d00c01e1802082d10905aa400b51107848001818180c0c0c0b43c0e40e8440d000140360b14130411400301964100042803080b401c0d603001d003560201105507000001c800d0804c10444240c06210800742c9181c0c0b1900301200502c2d052030401d41c400e401410801c0c0b00700c01321360760542460207240000c000c0190105004a1640d0400244c0c01d0a445d07024116140c01e605506c0a080c103409400303200c10b0f00342550320040c110f440d03402c100c03800341c54408222000c0b0300a100e030b41942c40401c4101c030b40300c044a004400300346040c1409218140d94004000c0c059514555008400035000400b013a10180b1410200150500c524403400040054503c00b030034141140509110070f83d04454945c3d020007050002d0070000c01d41c4005001d84014101c040710359244425201100d45210356a00d0882461000a004041000015446019540111941030110012a1800941d000c102d8010380580c0003000020300103030180e130062a941505052441c10082592412a466085801d01001180d41d035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 546300521 1250 546299271 546299279
    0x2040f1514032b080f040308070507081605160807060e04050a1b0203030a150b0910020c1302040503010f0b0d1b26010501080d0512060621041217070c02030a0b0709 72
    0x2213024030b40c0c840109449480760382401c3e60020314150000341000d0802030042900c1c0b040081e500c040742d4071301c2c059202e0181408401e0400b180c0b908480e4050000d40c000d00000001c0703000001c54100200c900e40e4680d10360320041070040c400a00b000801a0034015580c83c0c55281c240c0c040348154811200c03581c011610b92505080080c03c4421580440310343d03c41c181c0b82040702010045c100c0703c02080a803200720b0617050859003a8600b0b458035154552100208645901c480170030750240044803001c03002401000b02100f5158104c60009132000d421a10108116001c12403803112400381e68492801c1c95803503565800d103070402480c95000719030700c00e90640d200149881d0901409000d04400d40c040c0002120b601800340482c0309456160200d451aa00001e445580300030644450b40391440c0001c40a410703414070402a030300f003110221130041c01c102c0d05002003031003842901004410700c824890795440d15402590701381d000401c2240d0510840901070b00003030b2909081400b80395151a070b00c14241c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 546301771 1250 546300521 546300527
    0x90c0f03090804050d08032d040f21020f1207050c010c050f03070311101e0f0e010203100f0b040b0304060e010b0d0506010501020c061e13080111030402040f1514032b 73
    0x22407510b10190b001c01c1d4000700a020020408250404c0d03000507100c030031350403a1034515503124000d25a1560600be55202d42c140c190080741c04504110100705550107562298140c1180e409006d03400ba006500015940e00c1c554000c00074030000b20b0080040743d240115600e402c510f11b5109000440010b840c1c20f02418880c10b003003000d40d00c407039031008007070045502d01145124a080c42c1c43c2400c105a4a980c1c2d0041c599200d40d11083d000040ca00080d5900e24000300411902c081901c181041c1d803e501c10001100100c040c166415103410140342d40c50f40c0c5039a1034403405070403580032492240d5070700c404003045983c4107451111600c1c410300c090300b044e602d86000a03007042000100c947c010103080008456804000c0c408440910b41180745940782c09d44503500860350111500700d21001d61801501e11071410b0007134042c52269100311818060000c820007001c040d0386a4042d0b128040500b004140028504a90710916021024040b0364a0000002e9605a05841806000b80c12880114200da5050f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 546303021 1250 546301771 546301801
    0x211104200a030c1b0f1b0f0b040e070906020a0609020103061e1e1202120a0b04080d1d0a060c05130f031101020c0a17100c02030d0501090c0f03090804050d0803 70
    0x500080c81d0301307040c0700719240d4440818404200030600250101914020940a0580c1028014148908030a13030348403c902d0810368014015100303681484030000d20758500c1107601390159481c0d64044c0c034883c40079607a81c402901c0c00501c120305144e00c806010842004410040440700e100c140309414051502044410b4032400074a2072421000200c814001301d039a1070004180c0c5541a2400490024900c402d0b6080140012009180502503020701040c0200d4002520325046003600810158040b00074514030007035410041031440d0004040000803540315400341c00c03841c0d5107040c41c0d4070b0088000700015400e825a00190300d600d40b19130301403050100c02c080226800780b0030300040c10f40000c1e0030002035000c40e8511428a5030000d0001c200d4102209000301c101034200310f030042c8404060341401039101d40000da50f07000c56910300000020440440d0184480d02e07141d5480d042ca0015159008401500d40103d00f9544400b003048005081c2d00c5840c030b581708003400382ea1025101d04040c0c4800100e40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 546304271 1250 546303021 546303047
    0x2010e01020d050a080a0b0901030b10210b0a11030a060f0902030c09060f07080a09080105060a0e1b16060207030219050601060e030c0d030207211104200a030c 70
    0x5481840c0700e100c00354004084582400090424188a645090b00300d0b0262100040048c0c000c64040c00000070000180f0301d072030003110800d0154114a40350900c08483d40c1596440c010795a1103001020080b48600d01c5280d00301210030004204c004200132940019401910100855076803014100b20070344209040c0b502400802c0420351a50502643c804664010b00720b6652192600242d8651007030501d004440285c2e80c0080800d4803070424000141c414a02481001c1241d400c02000510758586440c1c808161030042d00c00f10070a80740c1162042d1034650151783c64007480001c010001100440000280000340700e04402743e81c58015207002400c22101e00e810041c45602c00b00c000002900c04650641514024035101c6115054040041d1a18201d035510350b40007420340161000f81540030800740c2c251106005084c40002918449020600ca2074202404100840c2401c5619260135040000c50204041098000817403840c43c90751564406000ca40201396107580d21540103030014010f40b900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 546305521 1250 546304271 546304273
    0xc300e01020415360e0703020a020a08160b0a06080706050c0318220b011b150506061c02090a05041413031103040305070e090d0903241802010e0102 65
    0x14a0b0400e0300703400f083d603283c45000307110000b850703601040c54070120f03154141101d0b03040210151003c0384011040348180034000403129800c0005030114041c1c0211901411190700810500540780c0f0340200b541c20540401014114540c0c000d000300d07400f000710f14000c005000000944914003c0e80301d160107400e5001c201801414031135a0b242d6900070040d02c20104a200002d106200100001141e0621031b00342e45290000c014410a9401c80950210b00002d0003071301d590500000d9081c140c01d5550310a031004048400f459440807844210f900302c190062006440030303081000324210000d07070b01c191420a010240d07000c201380c1254a411a8090020300701610300700b02400d910306410365401c030001c1c403000c200814001090704040c442c054036561b40e844e85081e01d480b15200d140254588189201d03186010002a0118600ca030022901c0311080046889080d6160700d9503440440000c0086070055100203003c403408010038850142d0400c0d13140a20b000c0e06034014900c00901b03486429aa00b83c11 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 546306771 1250 546305521 546305527
    0x40c0b070302010509011503051e15010b070515061e0409021809011103060a060e03120a050405010314090307021e0a03060b0111011401090213080106060c0c1403060a0c300e0102 78
    0x811804144c0c0d03202c100b0210a071030400b4240d0f03600030340b90805044bd0900410083c4000280d143c5240016001441c17046d800d9030645400d41e260070845e00c41c1500c10700c0c1d000e10800030092448188202e03220700300c41c020b8404203141c0709540018001c56003140c1c0f0b42c004020840204009800d0a214040360041b0075041035045003000000b00d82c0d0003015028a0b020710014030074000031030b9002c000203012005144206660b40050040c010156080341c86210b010a0a010000001c03030100c0201d54400c54000340214142040794003003107914003103841d44600340c01c04c0240301c0740c8030b4441d100e02001941c0141004100c10f00f105000400b00240c4902e84686070745411010480354464030121411940041e01c05a100c0798101c1c201c01042d03843d135211500369032030310400103803040d040140c2409941c05018151011543da506400e2009403c3d500161b242d00041c0008100c03c055a0016169891318541002e1220101c6450f01e203003245261402460180e001020890001501070490b030070985500a41c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 546308021 1250 546306771 546306773
    0xf1505070e1c0507180f0e0309100513081e0607022a040e0705030c0a0f0509100302061219090c1403031c0606031d03090405040c0b070302010509011503 67
    0x1051031240a80d1601c10300905100b810000740000000040703503004400d0796026030707640e1500b00100440d42501e0084500b05404001840a940b14400b03030b906081e0080c0d841e080d00c0341c080042d4401d14081030010700c082030100700c110002c0826044098031003040200103000d500342120400503110038422003035602410800901c140c1c0440c1040f485a10420701100d00001c880d00b280000805041c0039810500e064040440004005060f038201c0d44140d06480c3e08070140002c1c460681590b00441c051555640f4041005040c03400103142d0060380c1c030317180c2954a5100d500141041d8052450b1140c85021030080c000459a02c60180d0f1002000d01c400300000001680c401d00700400030720582419600ea40755400903a00c2c28011035503940c0c2c86201c1c2c81c0c40321040c00942c2000700303902d000d5040001e150225501d1f062403d01c1c3c2440c640c0000784001d40c00c00400800f00005406c0c024030480b504680c48000058151220001d42115442600041203d14121030141d08644940320200000860b04030104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 546309271 1250 546308021 546308027
    0x30905011704110409080c160e0108030906030c0306010c1401050f0106030615051c0501060f080c0a1d04060e091506030c0604060c0c050a120303050f0906070c140a0f150507 76
    0x3d0501c00613100898203404c03d00b00b0071418000c0320580d900e54090002950303060028001400705603030200c0b42250059803260511075480c0030700740d410341d08145c00300007061045c1c080308050741c1c2c4020145800c0b4040c0c8008e599100e03002407601c02d0a0320580d194010711031520f14210b280ca0141c905803604000d242d140c03880d00d02011070721203460000d2102c0015200000107400e4942000e1304c05608041c002c9581d2000010b18180e9251020b84c0001c00c80e10106403004042800c0b44c0e00805140d45a16648480040e150907055201d02c000c0d501c0350f620140012000c1c40500c200e4030902d5404080d00504484041007403d485005050610903008501780c510640d40c2c08003518295041894440c007000e0f124503181c0c80205040e0011584011410b10010300d10401da420508a00c2c4295400e020306d4039507100180d043c4c40300b03841d29001a00882e0002e807210344251404040540102d8a1040071001c0d084411b04204000d80c2c203440e400142402c400600100b070500a40d9901d40b09010030143c50201c00003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 546310521 1250 546309271 546309293
    0xc0306090c040e0109020613060219020102061b07051e070501020c0d171303060506040b0409022b1b0602011508030f03151c0b09010e0303011a16030905011704 70
    0x762195075203030590750b0f21000941c400b81c00316a0140c0700507070390b400c1216880d1100c091803140703600621500e11111030380d55200c400a9035050381a0020002c0d52100c0701c402841ca81c01c0b01038010402010301c0f401c000f050041018464404203600b0f000034010a0b025660704014103a00030905540c0b01c1400d0880756110205038034030b0b180d0480480c626808000f03440308158130a14034480d131500707442c80b0044188580c0d03902c200d006607400c0f1400c1040c11a800280000da60868070702a5000c88071100b0000c0c1d00c0c9030b01d140141c014402100c6490340084950b41c01c0200d014510480c1440805180140001d80d0244102010001d40c0001104d00c586004142990b030700c00c01603e40b0394031101101090b045228444d80160002d401400744080d00c64814005044c1d0304d03c0d0030180c40008040b008184114418440c0c00310314000c20000d1031460b8241018181c010b055002e0085061200f00014510825400220441e0078842e07682c54408038030b064001000c0760a929164150002c281c0d084c000000d68103525 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 546311771 1250 546310521 546310543
    0x8030408120a050705030d0e0d1706010e040b1008040510060b0414150c010209040b0901060c0305030c0c070609060215060a270c11060c040815040c0810020c0c030609 73
    0x542590750201142c00c07a01c038090000001c1642c03101081201c0268441e4102d08842c201d14405c45210b203c402c0c1e001c440c089155918604801c03c2c61004c111154821204109008005000170561440031000300c0d030b298409107105400900b00105220800c8020b20200d2000550701c001805041d0404001000328800c1d8460040c0e0700501c1e0b040300c015030f26038002c0906414a618052511032501806480c042e41c81903060b540320364078150380d541a62420f0b90a20381a5801c41d075403081405402c0e07406540c03540c805406107005101c1400744a1518038100a860007034602c1e50340e0408074510b0308001a1034a0514040311ba83c2e05840e0b0200300e05501c1d00e00395007080701d03480760f804042d00d1890080302c0c0d183c04803203c48050347c2c0e042c035980100e110740042816141001c03210894210342d8840071194207902843c064070701d498100309076608142101c900c4041c1c1141c014480184019a40ca40c42842c2c03411910010241d103802041c242c20b00381c0280402500060164054501c600c3c0c1902c1b6541c4541c00301c14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 546313021 1250 546311771 546311803
    0x30a1202030f130c0b040b04091508071203030b0a120515060f090613051609060503011401050702031c120b010e01020706031a032409151611030315090108030408 71
    0x6201041c8140d04a04e8001400320048070f5a8480d11101103041d0307a80103018403400070703040820300000c44c0417810180e000c89101002429203941881c10780d130002585080190101900c8680401480c2e94103d411001071040f00a4070f254414035251003814188282d1103142180180c41c2084516103460300b01710581502140c130049a0390f80c000008806511540060700307864a84810000c0e64058109841501c95058641c104415521081103c0c0c6120034003d00b9104500000041d20a5000c0c0000d00071840c0b008044e98040e042c00074440314000c0300702200400140c0705008214854065220f03491082200b86428402030303608070300203035451140c0d100e00001c00d0703964424881072480540031103a0303550004056401c402c040280d070078a070030545140020091025404112004000611800c060380c2480c1c03000c00b2a6078843c2a408400c50743c204140921038002005030b10700c0414801140302d800b031044500f00d024910b5081c00f0941d603058009482640c03040001b40403288002407014045543c0003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 546314271 1250 546313021 546313051
    0x60412030c140f06010602060603010903320712120b1f031b18060e030604060c021507121a031207050118080a080a0504080901080a06030c08030a1202030f 68
    0x450542c1041400c80c180360400e00810018040d1014089002412624164210788130b44d100d80c42010708950000200402144103840c2102880307402c4144080c0020041d180042a201e803100150403543c0111401c5030254007071288413803220780114000b101c03004040e80c10484092280f011840c6040f0800c0080800c0b850410420001031180c0c0205400c0c41034501669103001c0c01c0c4074064254010104003142c844684400070507464805c0720f410707541c2c41e801002071442d51615101d000040404e441c40b403003140145085e001090b11412f1155000740d4807a9215074a40170220f480b801126040310144412400e03100205409540005da084102035400130b007595161928900203004002c8901034100040040118034103100094001c0c08841455446400c00303a500d07052070f00b040f0cd404480050417607074240810701c1c01c0d500c1070070401d5200219000000c1e410b501e946644141172200d606c00b0340c3e41d500004a00413401c4e8480380c8140f403204220790035401d50400114075510004000d0030081508090 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 546315521 1250 546314271 546314273
    0x60703060f150503041104230604051608070c0b0f010503100c051b030c10090b0f011809050f0703051b0108130f080d050c03060f240309070b0d0902010e060412030c 72
    0x4050500444002001041b041e003a1056042000c082e500c0d208c0071000c120400210141450301406110b06600c0340802c9450b59051019652444081c211504105902d800d040024201c0c40c141d90048664040d900380303661600040600e09850b81c0003c41403103041c10041c08046d9041425200c250f00841e04404090242c00d40c50b51540c0161034179a40c0a00ca0019071800b101440c2d8400da0206005040300c1074103941c1c807421036036030081c02c0c0f144410680050b004000000c4a651200c42030720b01c504282d400407402e01160710300d00190340e001559682c10064020300720014588001100c1ea0302800e0400c0180362150020b1102c01000e132010303080e6038188002508010700c050840d1b150758103c0908210a0070500e41500054104951036400f5015802203002a4078121101743c036651004c6920400b40d035003c0b00d010303645800c0540f00d12070910030450301240403074844000e406202d0910341c000898400b68000100903040110300c0b0344c09210100420302c0081d000300381c194000b40d05030230055012002c1e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 546316771 1250 546315521 546315533
    0x90a1e053019052104060203061f0e040f060806070e0a06090e01051512040c0906050604050f0112110d050f01050a080d030905030909010e0a0b03161a1b060703060f15050304 76
    0x8450700d45038442c4900000c0204014880d40598001c00080e100100d031600418001c09102b204580c00c1c1c5c02080895104007181c0c0780c80e400620f1103514290f0701140d00303030762100030a192010a607980c1e00400c2c41d0704120301d83e604007642050014004e61401150242c901401000420740600400e405440030800c840040201c0308121039100081c04090702603460710307080074000d010745800f900f1092403c4c8031000078145007203002e85081d01c40040c203101c0300c0c0b0b400d4001034400c001e0500c18040080d03160181d00220301c12280c050140b0540212000c030345c515040d5514819020160082403245002c0c8005014080001510702e40d04010740c1000a6080c0c42c90614614500485182d04e5110359130714008030b595151020840d020b00655282440100300017030400d5240d4440c1e234091003052521000400100303660b407000e1400c200700300c03034150714142024108100001d00758002c4030b841c3c2d01020074441481e0b4140b250b100140070322507200d200c650900d010340d012495281e48000801c42c011010a0502c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 546318021 1250 546316771 546316807
    0x30306012016080607030606020d09091503051f1d07060819050a2901050f0a03110705030c1c050706021804140a0f05090a1e05301905 59
    0x4034010b80c404007603a0741e060103581c0b03e0080703034200300003420020700040141c00010344201485868a0b0450a1030504800c4001801c1903120a603141e6003540c1c4c0000031540c2408400c161245088007400d00d000035407800004c0d220104c9501007c00d2104042d4003030718001042641c10354807035250030000b50700d84918091800c02c005040802d89480c0805000010b003150f40410030f16140c41145100700501000b050140d0410b036041240440c4c41040b40140c240030000c002e2007144101c3c1000241070024480100b410340000c4c0c07080782d007a8000a00512421001c00960344e101d407820181c4080c88642420080c418000c15400074126600812420041e01c40c141801c603e100c0702410400100041014040c0c50303540540351085035514105400c0035221460149910902e280c0d001010301c690300d41d40da030340c00420800c600607a112128055000181d0144070b5030141c085082d0160302040d1880040f5034600702024014607500b0001c00c0a10070402d2070251614410200342421900c13420310807030707100c101e071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 546319271 1250 546318021 546318043
    0x1050409050c070c0602010b030d1b0519110604060f0309020a08030c28020a1203170c07210c02041a03030a080901050c07020a03170d020a050a030e0303060120 70
    0x41e04250401428a001e10090510507001c0da5014a4aa69849082c0d0888841c5000503801d42c025400501c40d59004a4180400360340000c21700207600c2e002e4135194200307486030702d421204010b12507060061000390128050b1401c022181986014903202024040300c0307480130305509043c2c480f1040030a41d0b68800c0180000c04008043e29600d18440c6142c81e20b0360b56a091902c0400d06904c00001d01565250b005d194080c0d02400059141f803e10442d1111107902c51402c40401c5450890f5614442c2e40b44449400b4a9201c2c10741500e0311070a180600351307404586900d14044e541c07290380e1620030798041694800350fa010303100025203090740e14a4804100b0075424050700340c440000d5110003e588000c1c940d11450160300204420f848440711640d16105104020f507010420110038008a024401c03845003c0d071032810540e2400d002c1010305410703030700514501c402007000422611141a098069484c58281d410007843ca1461b0100001c0c261096203548041817200040c0180002402040103845803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 546320521 1250 546319271 546319289
    0x24030b09031c0c1101110423040903050c0c030102070804090b01030e01021c230130030e0103050f160c020d0501240e092a040f0203071b0b15010504 65
    0x40c0700b01d01c0d401800341200745118000500300d16050300e40c0703040612030101c0550401301501d250a1401b152070b03c1c046020241684406e0b200320504480383d4480c8200b04070039200341c80399521740081080403800e04011a801c2c5000340d004211910010b41090112400c3d181c42d1140001c0e5007a0382d200403001484203d00808540d8400039200070b4410300300444001b20481c45900f40161600d03580140c40f072071b12030f509403100c1c41020710043c0102d4981001402000c070700360200e070301c4003150341a0b4a40389060000c015800315000c0440f248813564140582c651018a0300310311035190405180c4601241202c6003482d080141142c804011584e904956040b07164006000388202e80b0031440c14103c80344040c070b440002052319000011040e240450507071203000984c2c0507100001d4040071107038410300f00b282c46009003204041e803004a69528440c20f182d03200c42c1c1d035005840303281441000e0101c0c02d01982c080c085411903907580307001803016205958809100381c0e10f02a280301c0d03100140ca50b40a560418858 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 546321771 1250 546320521 546320557
    0xf04181211010e01090f1e051c17100911130b090306131e1a040309050406060e060319060807030803060112060501021905100c02010902030124030b0903 67
    0xc5074081405100da0810788001c02808854202c401c4c225050b5040c0104400e100d240b8990104005803129003034281ca1403042c40c41700c0b013655542800c01b940305041245078001c1c00c107071240c1c0903880311b440c11521121000b20031b0307203051003280c0c812803410505c03800070400c0e1545052b4685030119825125407400764601c1c20521078940e00c00c04580c0c0c102200e4580240304d21000103401b250980000204150409601c040328528140c4d00c501c51a040001030b101054100c20614402d110140a1445940207645048056041100300400d94a442d031116082180395881a881071360b40c102220b801c4a0707460286001440429410005040c059202e4109406024000024800c2c40f0000754072880099a400c03c00228200c0f4100849146025040c01680161081d0501009520454035003034064000c035111031a0b004a0441a106040984030041c0d446940c40d07070071030409025400b220a00c0c200800c05840b07010084c51205289840007038052a1154082695000140106c8042c0c038440c2c0364450b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 546323021 1250 546321771 546321803
    0xc0905030d09030b090d05070609051c02011d0631020607030906020d030219031d0d11070b03160810030606060914040506030c10050c0d020d080c090f0418 68
    0x10481c0b245110a0765101c00001c00180556004a01841c540c801920366500740840c1c0d4540d6030041c004500c04076454400d08072051f290540b43c00c3d0f0300151349460f41c00402d1014403c0707090080b4441c9685883d003150701c1202400f0410f05031049800900551010010312000000d0171941404842d10020f500884000740380d0382030503030161902d03050b2903843d001c40708034a4034100110120301c16582101c0000c0710f40c0b070f411000d00b03100e500710b65400c13900500302c0c145820481e00c150b41405011480100481c01c6441d6107040700c40b0900c5090300806004601509504d06280140d500b1101071005c0c1041000c01d40003d5040e1041d441d501c00555001042040324035203901c000391058a03c0e0040350040c1d021014448400c0c5414050613209007005000b4180074035000c07040c04030314503041e480b050501609112f591450141000000c0d040e800030780c000d1506a40c2240c0c06000400050410340454032304015001c100d0311100d19100e1210025903000810010310000d41003525000240200307143c0b42107150031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 546324271 1250 546323021 546323027
    0x20a09060f060e0a05010f020c28060206040203030301050904050a08040303050d1d0a0b070302070212011b0f081603111b010c02191b03020d05011b031a040c0905030d 73
    0x1410360308100d419008450300d400703080c3c6114021698290f844280e105091001d035109942c00d0360b850005004039140303160880d0001c1c10050381041c0e000380702c0c103141c44003012507040d004400001341140d002410713035400c150700803c1c0c99100501419000b80700c4100030804010082026000d500e401401160701c864903480c00804951024080741030807400c000f0b914288489001224951486480c0140b640b03540a039500700e4070b1b4100410100a042c0c0c00e20a403005078036080c0d00864814080400042c3d81360303004002041d0450002240000c008203024080c90503a040b5281701d4011240c2a000825102011021000f80044032440d012013440456a21f2403413091150404150a072500240b00300c000300350f13040366540019000c40c100403a05034080b1012600b41000a040c0444070f80c03100c105507442e900818130341e07c0040d0b01110ba45c0c1d900d0300c0b882400d0308800b070a06503042040c50140f00c901401e6400c042c640c6119180c1c584070395559400342583e1801444080010a40601900c2001020060103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 546325521 1250 546324271 546324281
    0x206070305010506040509041212060b040e0a09020904030e0f0a0608190c021e0a1e0b091b010e2103090301060b09010903120221220806061c020a09 65
    0x18802190614002154601d400340588060321005009040310b1756464803042d203082c0102440c5400d003c100f20360b80190420502602e4040e00d0080c20781c0c1e46e07681c030b454030180270301d10000c050032071003860030081400590ba00303ca6560415054074100301c43c45000f600003116802d52008841c2e21808142d0000b59a94104440510034000003c43c1560541c0e0043c0c21020345060800e03000042c1c00c044510b149801c420300c03059042d041c5600071200d100d00260790f64400b114200104250380305000003114100000465400d60020b8814043d211100c201c0300d030b05005015105d50241448480e11140c0082e07100d064400035180d0000c111910100451a0740940300d91120848601950a00354003090b0311504204503004540d040c2d503407034045803a58607174150400501e24000118002d42c001c0c20030403a030620407030210f0400c2c590380c030b961240700c0c20b08454013860310f2b00c04030f4012a001e141007120200200d009035000c9016034000503401a904400c0c0c1500580100c002d50141190703201090101c019407007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 546326771 1250 546325521 546325531
    0x90906090b070f02032703030c1e010e0a021e0310020409180512090a0b0315010e0f033c0c0f01080907051306081c080129070305040503030a0206 64
    0x16803001500e5042080712810f401c000080e01607070041244203503d40c2160040345501c660040d054132071009180001703080d07520040b1100ca455011a075809100904078450341d0042480c40002c01c001d1440c044065107864600354042d00c10b180c480e01e101888000920a100d650070002c050300e5140d00740410041c020341043c000e11b1501840c0000c41102c5c0f5400c600800719050b00b0200900900b502a031551049600800380300307030041915200000d15050b510051070085040240c90740d28030280340001407126100304c8072284548007a009903a41603c004c103014502c440340720741003109904034070400480090150020100d144074080c1c0e2203164040070540d0039060004032034956030004140011100035406070b4000070550488082000149000542117400a804000c00b14126035204005414080d221948410400222107407038042c640c131115007405401040d4a40118800302d50342100400117004080b8001000011000d050500900031f86000b040020b00f101e80d240d00c03c1000030b495040c1036030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 546328021 1250 546326771 546326783
    0xa02070e1005060d0e030705060901050405061b03130302010213082503021507050a0605040f0213060f140a0e010b0c010f0507120f06030227060303040302030309060d0609090609 78
    0x49045046034200c0c10080b140002d242600704484030240b00000e00380a011646907110400a200008e2014017000784200400000020640760606125040540041c0944110180c5a0403a07118011400980303402a01d654101c3c68169079514090303009109040030880c0c08891440000b400600000e034560740300452181848280c20005100e05441005000c0258880b000100c540110322600b800340443d03c1c010805c5442a100a454401c100c80084d01c0c00d60716628490b42403003c2d410483c0028201d160700c1d8404211103450485265403c400500031200b4105001c1d000000590314412036001401041d1540c0026503910241c2c460a54002916a03950303500304410041d10600c2441014455252a120080040071030507a1800808545084241c2c440e524540440980c60340d040304042d2080130744086241e03101c213a9a850202d50010262031003a402080700b400140c0340481503910b00c0380d060714150f8640c034480950b20050506504020446480c0089110600555801c4840c859008007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 546329271 1250 546328021 546328049
    0x3031524030612020f010503071e1119020a120204020d02044707020409050f010509010b0306190e0f01050702210a090e0603010603060f020703090b07150c12020a0207 73
    0xc8104219400b842074042d52085e044803440d11954056001140c1c030480c03d103000c00842c044601c0010403402501d510400095043c071072040c03071503000c01400700c41810b1603045004039030382c0e90300041c1443e0240c040c041d071203a410030601003151100e8041d41c200403142d0206646454032540003080d524000030340017402043c01240d180452115000000d00302000380510940d2106d65a0484016400f6050407078200c5d80e00c4030349402103101440700345100a00300d07002141c81d091141d10301742920f40c413640207403003500000c1c01e000030420381050b04e07500c6140038800410300c14000d442c0b0341d0421a84031000079040d400c00c41004203c0d517000c00d0b00e80301c00040080060034012103003205a0039000340903080000c260142c5017400118115441254040700c018008a0000c2c1c60b1781e0741c2c0c400d664050011458079500030034840b0400d600704006101400c019030400303040900c43d4540c05902400003030b00306072040d52103480116080c0700360405624001c6c1540c081d075859941603070003503584c0d00c10710a0308030880c0b140d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 546330521 1250 546329271 546329279
    0x40b060102072c04020f1c020108180712020102010917030a0510050102060a0f180c080d1b03030b0a030c060c060c0320030606070c1211040216030315240306 69
    0x2034100055100b80c10f400045040d1001400d034121000503200340c1c4c0c40001892a2040741c4d075030300d86e81c82c2d0160076500f9054001040384005030420383c02400b03410303101c034550f486000c042c240013032444201c401c0050141c201c04541d00042c0c1c01060100c8016121511100c640a0030800c40c000079800f407510064108000d654880401c090107442d4017500340140c009201041c207070000ea8200307a070026024003000445545008110300a0041c80c1411140c1008110003003280d181c06014540c0141114146404400d0711100b4120b0300c140400d100801340355982ca042c01040d280e50090710050340d40000941c512a03150100070388611080102201c010782013070111000c2c64840c0c0160100d03558494032140d03000c20303e440c101c4030980005010a030003c02c14001400441e200f14040402001a034540a1400c840c9041c0072820803500100a40030350f00401954800b20800804501100e415103800119581d15400030012402c240d80000058040c0e003141101c0c000300c11010341d034110308c107860401c403c95031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 546331771 1250 546330521 546330539
    0x30f070c020d081309020307020a03090f0602030a1d06030703020702132a03181407090203040218190c0305070f140d020f04030c08030409060b0c0d1412040b06010207 73
    0xc0c1800079080201c03240c000c4001640e0304041d1004030400183c0500e007070b840b01d10300403c980080f1750b0303d00161320190803a018180c000c0c49500141200700407251149007000e402a540e40703d50340b00c040400c44a48030240b00c01d20100c1c08800f41c034000800302d640ea400d00302c900801941181d401648688000d03129940c82825910482a8070001004000301c680341414410007000b4907512014103058642c2c0192604959280d260800d0a10501200581c03210007907a0360324100306a085030517224810418040983d84220500c0c040100c682e10160090761249031580000030949900c14241e802d000601440d1505604081c1c4184804d5942d4596091948801c440d00100d401d912280a0000c120744a0803000680041c40b80c00f0700c81352541c1c982560b80d9100000802d5950080803150004038052005005c3c4c0c1c00340310003e01e0441c8065003400003424400c0d031190500d00b0568140301800320503e86510021003640e00444800000d0b041ca444c1034200300c00c40c03560485241d40180242c007408182005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 546333021 1250 546331771 546331787
    0x703090e130c0b030a060509040c0602210915090904060b1504060813240203010303090b07031b05070f03060f0507031401060e01120603300c0219030804030503030f07 73
    0x90010101107001d450420f040640e80c0c0041c0c40d2141560b150103000c1030907141d08201078019441500307540d21051401c01d00034101103421691b5040c030944155890142502c0d10150355200400300e0f094010341610090201c0240f042441c115040500035080005001c0301d0352003110b0441c003d40e240c0708010081d4000040521450040c0408291507401040100701901c0480d0101031042c0450701004015050000f6405401e200c071600d490380000c01801003681c00b40c81d1030014040038544030700382a9240e4010300740c20101000b841c034803403003980007505010080045600428121000b481c825440c2c0c2411005401d2450002a0440c100004266402c0c0701b4400c50707252110300e48410030142d013000b800300c030b5140102c0d19590400100c100b2611101159216000c0218420b905040f2094081c003822100350a030710074001078048a01210800254010a01c02c001c81d030b0494190700c04a60061942d070110403950000783c0380341c1d000b041c04010002c0010085008081c08011510b05a941080c12250a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 546334271 1250 546333021 546333023
    0x30b090115030905030f0c06070f140706020d060f1e080c010806060f0c10020a02010509070e070e0102100f020720030a02121c020d0e0102030c120703090b0703090e13 73
    0x41c00880341209024800d40c0b04014192042c410b4902e00700919403480300c5034224040c3e850003500035100340481a42c01890100e001c1c0403034148240f150042c0c01d50104180500c0740080d113499000101640c0d240c01c1d81d44068042d200030604030070030a07268483c250f000c0880001011207070007c2c8401040d1008000341491341482c05a54034031480d0354141c184076080e0070072100700400560a0100c100170382003e2000d040c6854407100010b0301c03101c000d40001d013542e80140145050381c2080c24207110b20522615070301d510040e1340c03c00c1c0c11414800c10040340f0300000300b81c0701440c0f240b07410f80900e641ca0403034000304407550199a1211541c6105145e9100306000c680d140b56155100700500001824403040a6240c040214107072050249200149240e00d44049803600058002c0c0310205a0603421410442e0320450030310045046c0f88980180e02e55588040388510540389020031003008140c460b00342c80001c0e00303e807188185c45481170301d00078108080d6401400e8001600c0707000580c10b20480a0608502c0f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 546335521 1250 546334271 546334289
    0x7090f20090d060c050304021c2001110f0f06090d02070e0c07060f1b030e070504091103030a020706091208161b06020609010c030513320a03030b0901 66
    0x15804410a0580c1e486020707840c0c1c0100c140203000c0e0200f00a40b2a0103d100d40680302c0c0c5a481c07503d07104100310b5000701100e0740c1c000c03190f10342014040f4103000000c070700a9403c00180f5041c1d1401800695070310040c030000130300d603110351034006ca4050343c0803076000e030318110300001c45103140c580c0490700b070300d0389010310fa0000140e000000410035500c085444540180c80d04108a00c0d010355621084262240030715001440d903158448952003444284000c07044011918080104004000d03015460789000d2050b284655180c0142809020f65a80ca03601d4004000f002c4a6641c0203a03807000e901c400151080801080b84000b0000304207820320281c040c41c99000070742c20b06e0903203108061005116000010ba8100d1880c9050014003031403410f088001d01303002d400902981c5044010700b4296400000040c2c1014240340034040d414111020b01d506c55603110000c0c50644401100307403441100341448403076408142c001c41000c10040441c10381450360182d43c003400144010780500c11000820301c114907503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 546336771 1250 546335521 546335561
    0x406171b06030a09030302040e0a0c08060f0a0b0309030c0a0f03020616121a0a0803040305010518070317070602030103110f100f030c09030503180109080f12161407090f 74
    0x140314940e40104a811700c6410010b00b1710352035160401d04480222a10195203650705500404e86d40c11890080e4028000c4030800180c402e91004a5101034042c464038000b01d00110104001136414400ea4440b1504402200c06409203810101148146031f8002d40141c041c0368080f070340c402c800706c140c3c1d1310400c500d4640394840030402c4542d60041c0300e00d0a024101440d02d80b901d1019503155419040109400320055440704d055003059400c4440290000e00403030b1050503a003004940125074001202d400808030203a40351109001d201a21810710300a0501d880000048108420440300c0b4491000549880707182c4481c0b1028800450100b0096201140030b41003440142032103500110b0700b29030304d445c0c60031b92259a0303501c0303616580102d041402200340e07654064110303507884801840108075003c0201006500c52500c10340720008030b07404040103d0006401702d109906075040354140c652201d0401e441e108181c48598440c112030180400e40f60406008203440203040c00f5070509140f071500c039001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 546338021 1250 546336771 546336781
    0x1504170720120a080a030b0603190507022503030305010605030618070c0c0e010603150b0f0703030b100c030e040905060105090402010306030b1302190b070f02030c0406171b0603 78
    0x207181c01070308545076124421401c0121040d80903c4074285251040c4011358030b580b44080e02a058500d1400b5081c0140d07020700812001284c81c3c5600195404032a02c0042d4646440008a084c481b074114007440c0c0070905821244c0703140300444541d0031a8081c1e50200b0903070362110780440e002c1c03205484195118040107450504661081d180b80d030401d01d107091240d54005d559071801c44200c0280c0c000a64210f11500421100341c040c0031b42c0400d561506000203006080208040c56802034030301008854501040352410580241d000705004100109a40012802140b0041c80e030031205900300e0019007020101d00706030405025010400381d1140280510703a0802c400d100b0980710090040e410592942d6000001c82c0c00c5c008218040c43c582400303003c1d203030001d00500c105000700c00c03014a034081c50500d04000110358a810780e04d100340c3c082d07400c4d00b588600e800003d241192444d0545d030301070301d05507000071800c000e00354804401140c3d02c01e4400c4c651482c04892401c040d00c6003640d07007141c1c041002074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 546339271 1250 546338021 546338063
    0x1111602042003060906030316080403020301110304020315130f110310180b0a0207141605091501050c10050c0424050307110708061914160c031115041707 68
    0x86e40454040c0c1143d08100801203180003000915600791480100043c040c000d40c1428050f43c682d6400b03020380245907061030342c04a0b55461180c1c0a0b00000c0b10b40b54007040300c004061942d1404180c02980d451505005030030425181404116664802d209443c402c180c841c085004d10720419416610380c4925003184d840b40307205a039000748a2a0740940c00c201480004140602003114088080000c1c68158545240a9428050341e080b0a10445a0740100b082d48110080800b401b248280b81607070308c2d40140c44c075451511006401c00341100c0c1c140307007c009801c01010f020f40704492031040b0301c06c1c441020990010410000724140380000c1c108200050205000b65152003910011204990080da550800716061600a940507121000e82004982b601c80040c01a07405501c45039103c00d049080c4120200c81307030004240004240f002459419041c1400380c0360803501072440300180c1d6038440c03080790401c45034901182e084070724007207420f21302c082204550305407505c80b68004030540150f41250912 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 546340521 1250 546339271 546339289
    0x1e11160305090603010801020403021002010b03030301030327170c120303040b0606071208061e03150a060807090603020406060203030112300314011a0306120111160204200306 77
    0x36818840100320092494890200450081012800058413603096104100301c4003000c0c040d0b00304586c10030000440030350703000c0100c84c11a03a0505100001030400c042c0700391180f40c460705150300000c22250000342c20401c201d40e0b20300348640780c040da0075050710003041206800c0784841c003c080360310500000300001d001c2030000303802090041109050035119505d17444280081003402c2d00081e68401403042c281003002c2c0c5900450b00c112030a0303440760f0516000ca5501e1a4410007807114200318400718480ca100366200e90041c0c210300d0180d0300807507112001440603220a20049024a241000001c1c0c07a61000c003d50341610b40c00400720b0011151911100c2c500140f542e940c030360102d5901038a0703080c1000419400901d00b642d440100d0703005e205680b2007084d400b050303001c0300601d2007100540d950484c0303000480754440b104a6501043c0c0c0040d06a503030040c150101c04140c0d0540020f417403030740d07851142440c0e445240f0032103050110700d41c44120700e42125410610310030740c2503003032002c00d0480c41d1900030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 546341771 1250 546340521 546340523
    0x30608101b050c062707030f020316030b0a050403111005040c0e0906010603020d06090615030e01110a0c0606090e10060f05010e101103270a0602060612011e1e1116 72
    0xd55001d20551079021b420032a82d075204540c8189401082411401e0511070401d0548005240d10543c6295499504018800602944080c0c1d0399000280416001e10844080081e0001c211060344000a284500602007540c050b1111381d190705000840c04020259240306001e2000a4079103a441d10700194042d4100b0304258249948411003c102183c10b8850003005062900e4012005c1070500800b60440700d00c03c0d40c16a041e4100043d00c1b400c1018003045a882240ca8070b40010440f00301c6c10a90024032241e04603054103420000001002c04001808201c0001d51341c0c000c0003401e42d00c07030421050a0180c8291070203e801d04080401d2464181e080b66440502414000c00c01c401404a4900b5a48040700076400040800c501f110320030074191864036482e0b41683c402c01c1d0a810500c01a664940c0107024900c1100901c182006c000000e4110b501980d050103103003201c0482d624401d47c003405615514203c5415081c00c0005190740b41e0089601001e10072482501e0074242c0c1103003100e100c4503110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 546343021 1250 546341771 546341821
    0x102031e1306090c0501110a2a08060901020c060708090703080304060207150501140402040f140d0609060b1c0c0e070201151701051e0c070201030608101b050c06 71
    0x5141000300b07040740103269050748a4031407031146a007024001360807101c6101a000031030f400600d01c98006004400301446002041002c2000009050700764440003010383c000e41c009000f510144a801c44d41500500040502d010540f0145c0d51142c0040380c41c1c1c00215060082035000c0e860800104040400a5401a0045601620740003854442c42008907081b2002703002d081e60b40004010100714440c0451340001d08840540c078041c500403c1c0c1d40b610002c0d000352401d0504807551702403a581c41e145901242a8840d80500402006040200c02801c00c5261240110200e0300442008981103903092591603011603007454840c141810fa2039407120040c107040070f542d42e0f28400300703581e401880f00100912480c1c0107c101007100610103801d541d0003512600e11201c42c041c0c20340c1c64086a11919a04c0b032403016245403140040d0004034003a000c0c070380c40101c841c0580141c1c481c1070010380d00284d07000b00605455604000340104103e6243c4101c0205071200d402a4001ca90320700d0380380c90310052421040c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 546344271 1250 546343021 546343051
    0x310060c2f0f0102161412060c071a010b120405190c090f05060d080a05090418110a120209151005120916050f01021e0f060105030102031e 61
    0xc0046004031100c00c01c001c0625490404418151920020107414040700784064940080200100343c0d184c2c0142c0103120400d094400c40c62000c1c0c03a88031001c006103115104030740c883d0411a02c1045070794088201a2074400035407080d01100b060860a07103040b0b0b68058900d51520300581c0d40d10780007000c058000c8605010f90841c0d504e40755005004002940e0282c2181410700b80307040e07001811140c42c4138449100906003020402e00342d0313900150b00480c8bd049041183d850141c20303800c03992481a6000c807944a0b1800c09040711070b10056040c0300d0b00c1d9118070a60300c00f0b55111020000110107610a543d0001100e082c42401414618605d0b90490000884052003000c2e80c0002109a071110f2a060006200460000d0451003001d100c10f401620010260045800041511443d81018040c50b4050048148102041e9100300065407411004a42040041c0b0200c0800798a81d013168a01c8501c034440c41c0000300d090b24061003200d001d16201a043d0601126400d02c840b95110003c00e510602c190103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 546345521 1250 546344271 546344303
    0x19020a0504151404140111010510120c0e0a091a040c090b06070209091f06030305040605031806090c0a05150d1805012a0c12031508030c0307050d050310060c 69
    0x30013510107001446000c03014004984001480900300c0b411840181c0e0424003400404001000200c0948452540910000100c0d040800c8800c400b030380020b8040c010f034410414021642d07032041c0c080502c203010b050443e5109032000401d694082e5401380c20581c001100300107080703d946c02241c9281019141c50b0a00d046030b0002120034600700d49030201034000c0c11074101c960180090307140701411180f13420403110f03081d510010040e00980c00b8410511200001088c240e00b2040000700072800c0c00412200d0614020396a140c551200c5020603015070b500e0030001c036241c9002d6060f4841d0400c00502d0604110039962000301400d540e02c0596840c0383c104d070401010030428000c000d400d40c075000e5031203034000d2072200c40c61119214001c2c9604005014032810001103000d424400040c03217515011071041c4813489282000d0019510020746c920000a0022024401201408800c1d001d102500c0e1a081d880805680d20300c0100d51140714030300d01400500500e40030710113001106005170450100d64841d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 546346771 1250 546345521 546345557
    0xe0901230709081504030804110d0507080d02151f05031e060a0c020a3210060902040614220801050f06010f0903061a060f0319020a050415 61
    0x2a03885644145000081041c03050b0004801001007000d80700400d641c0801210381180020b01400044c1000302d0900460280044290007040040c0020100e04142d130b090300d4415507030f280510810029000349592906424000700d51002c40301c410b4480d4080c603680e5a020b04501442c07126081101c000c03031100100d21500d040103291049a0318030404074042800c1103826203000d400401c4049100c1c20305068101442e4003141c1d80d80c0c215031003000d0441c01c040c90310500007152944d82c034207014003401a000902050780040c003c000618580c400300581074540500c401a84610700411000c1440c00c1248812940500c1c020084050005066810512408a0540c90308c6030740d844040941e440f4411302c030a0f90903101903660050000d003030050100d10100300250200742c4070301c0083c0010b0343d83c12080b450a0034441200e0114100280381660b201e42901034229140c005a90300011070300e0700302142d00284860301c2140c52504058407002e051610308149c0409291a46600d0700070000864003400a800f4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 546348021 1250 546346771 546346811
    0xf0e0f040f24050f0a05130e0d020c120c03070b0a03060801060f08010b03070e0a0209060f0a08040308090a200402090d2006160305031e040609030f08100e0901 70
    0xc2d01409000c4040c8407840c0d0150300b00e640d5044244950503c183c0071889a8034004504111038082e1006050f0584400000008100850180e2024003030623030124191079012558000441003180d861004106644c025a030f240070802069815901908040c0030040c1118060845849035141c040346490b1108951420b560040d4403954505c1d44450040c4001d4000b8050541c8c1c03c8000c3c0c0040c803090346007491b02c1c240304c400a04022a4680c2c0000d1801c02503e0b144111340101c050a001c0d87d6031a000c640004100d801d04480580000306504041080ea42d0080354603581180c10034026503e00848000f04020198520394696105908214048858807068521104240a1a807644851401c446044507000c1c443e81411701c5032108108240d41c2c2c0000701c0d114030034150103161642c0c0ba41d8601c054182081201c490102035011350204103c1000a03c8e0080341803036201e0341d584200c642c541242a0f80149c0140c03000d03184505000b1052110f440c640e420194491001400411036409043c10400408 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 546349271 1250 546348021 546348041
    0xc080f060115030212040213140c0415020304080309100908190c0b070201090e040204150b03070311120f1902040311030c0d050a0602031918020906010f0e0f040f 71
    0x60040d0340104910b62060088040341c0000b414158139000300300788031048451004000034810f03000c1310366003c0d580201d648900c40c9594141480300306401c0034000420b9940041c8505203145100c104440500c07440401a101194101d80056044c44510f070100440384c62210865010440380d0f90001030380400401c55000042881d11500506074440e0501100303c043c0303600b0494410104114880040c0d910503284801c580c0990351030803645c1c84130300c0010098a001d2021904107071b80400c011800141340002980680104e480c10000b40301c110000c42c1150041c1004020528001c80c000348107404003040850b07004410300760340002940f5070254102241c002d03400c10307105103420030003010703282c00e003080202d80142040f107607681180c0f001d80e0380f2513a0f80c091281c01080e0540105c04030310b03050300b400c003200e110a078490301c140961303640840d80d0140089590400c0e44914556000f05007503500070042409920325664032201049001c2044c021400382c2c0b4191207801a40c0c48558414508141c42000f09003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 546350521 1250 546349271 546349273
    0x703020a0f0e0a0909170a1205100612020306040603120f1404030c151101060902030a0b010306050a050f1503010f05270a0c0c050f160e04021c0c080f 66
    0x51800c0c1034000d2264180700100010700c060b0000c050b965a07036440c0c07590b044410040e00883d003111a031034451309440042c01500c001c500c0c0131a0550715180c001d0b00c20902600458402c00050780da40d120b6400940562107082d0200700c06030440100c0c0c2c4e007150003c40d4421704c05080032510700e950b50303101c190ba00c090072201000602d1042c0281070b4039520040390719100340754a8120f4201821911891035465140c403c1c1c3c403050006014034021640075030044090384002c00000c0056542c1c0e40401c2c4003940c0225400b020546ca0200c070704c0341d558081d101c0c0300180c82c005007281018605000c01d0008080b010982264440345507104940000c0c40c039001103018002e01c141d103602c00c030320300020711810403c052801018111806c509001d02120341d402a1340c007081c03910b400300e4a11801e107026148054802c0000d8443d00403061841507445000614003000f100403a0400040399a13000001d40d40306050714000d500c41709104000501c40302010fa41c030300d0b150084404031103ca694016203850085007420712181 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 546351771 1250 546350521 546350527
    0xc150605150c192405010617090c090a0603081605010c050304120c021807090e011a04151b031706040c1b060e010f05040c080a050d05180603070302 65
    0x95401e0003050709000340140d22080d400c00e6062040c1c82d460303400c001404248229409085018040c20382d072030041a04450096040c12550744000202030f140c240510401f1030700c0000200141d140c000c4006101d1548200584140c054030070420003150800341c40442016104d007004400701c1e81080090440c0c07403a801e0852090019854160300392a04580c1e0042400300038020480840d1542451280701516440c01503915181440004c1c9120003500226054289240c10004895041494042aa14074416565042e070703a40801c8806c0003002440c40c0c0901800780010880001c8aa03502100c400305c60900f403110052490b1080160f8080d50019000242c450a0300d0021144440c00e41c2d41006044d5014407001d00c2d0001c001e0120b0000141c506a1301608607076640c240718084d0b12413864012140003d00058034052641c0d8007800c02a80e041c0c68480345030b10300160402c4006410320801d0390200c041d024182000405031000d810000300b14540f0180c403455a4201eaa502c002144a249076480050b2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 546353021 1250 546351771 546351779
    0x117150723070210020a0c030602090406091a030c0f060a2a030f180b04030f05010b060309011a041505090a1e093c0510050c030f1b0702060a0c1506 65
    0x455001c1c004c070344001d40d0030102c1d80d1804610100ea40da0152034002c0e07030240e620900b650101d001003076aa80428207062a08003000e8082684142c00207044104600701c41d000309580d000c1000c4240c14840c07036030348103204201d655102030080c46107003a0b142c032001c070290a00030842203143c40014540c60460025288444207032055402c20f44051038000440c410300b0990b41001440b520501c92400040d0030026084e04d01c0c07040041c01d400500060030044c05030754072820120340c0203010f00088050021040394001559909081c00d1081c240c90a0007414900d030310f41e00d0042440001c120140490440d207880b59020400c10311503034032508114141c4c100005401c030640c00c01119080001e01c0c81440e280d9081070503011507801c010311039400e511032441d881c2425800c0c44c0c002c1c64444400d0b400400142000100410030144402441c401c4000c1000001039030b4881c0000034098204003812028048240014009030600a010b8007100c0720701c4c1091403032401c040d103c1d4070b1054a1400c96034501c3d81c036103030140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 546354271 1250 546353021 546353029
    0xf140c070b0714070b06130e030d0b0906130903020a05030f09090109090c210c0b0c120301060c0b18060f01090f0e030301030602090301021216020601171507230702 72
    0x81c0c2d2009882c40e040d1124003158005034064442e40901400303500388035011844954461090301e001044008040081d82c0516501030b4032a00000c981802892410010500d5410244034040c41104018460a9011094074495005101c0c2280c2942107119661050303001a41c00c10040c5000620903003055141c002410802c014510160020800541060750074800250303104a40c1c2d042d00c440d48190382c905108404a480800c20025025100d4030340010006130050800d00104541300300541501c00403807519010102ca84828421000002c031502c01d00008500c04402894100c1c12002464400203000c120b40c614089094401c41c19502a6200402c1807007498030481004504180f0180310307403e284c03044141c5074041440058849030300010b5001c882d170340039411540202c0ea03104100e0740c141404415982c1d941c1c4000e50060151047c2000403501c29030b107a803c2060195a03100a03c100c2810001100003a00c0c05005270341801041903c484220903604c4445130302c1840f84c8095a12550940108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 546355521 1250 546354271 546354293
    0x91f0b030910050610080a05070201020f04030606030b0a1103011809020406090e0708010509030d050c121e130f0807030309210311041a130302030312041a07020606040f140c07 77
    0x704d00c1030102c2c2171a03481481d002008250700c05076070100007c0036951001d00b64060310072840a18100c802c0002e002c82041400d6101c0001e40c1d02070fa0302801590355845808003111304c4105102da9114040c00100b1400c1c0d01185034000c00c00341c2800c045031907503a07a070115003511840e0300141e5801340c940224240e4010304000100040045400a01241c01d202103c0c0340c503403045130309918070152120002078421040a044a91000100c2c100a4841c640001d006280702c110745000c816a40502c40415500d0791034001400c003503070300503079076686d00100350b0356801080c0d01503241141855180c030302400c0400c001201456582a1101c0810312044007560010121031112000c24400c0c00180002e10032400e2980c0803045142d01000c001d95980c1c5172150748104264243e00c001e40c117120028a440c0c2e0215030a240c40d000340d129003030000503004d0f648080c00542c44201c82d10401030348900c00081d614074203504030011700c20103103d000903190160b22401a007800101c0c0e06000103000050b407001000041048 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 546356771 1250 546355521 546355531
    0x204090b040b06030117031303140f0a080307052d031f030b060f12070b1c0c080403080a090c0305011d07030302060105060a09051e040b0d02091f0b03091005 69
    0x4002c1070040d6000141d0328041070051100c0c14156801100e01c14000704211010820031900c5000c0c42e0390743e0300c0c2080c109142801c000403075005e2540c00d043ca2020000e501c11440381d00c808020f05560b1544811039081d009141101ca10b0303102102500c290030955850581f0300d0621042072075072883c0038514049140710001c5070180c9038085c5602040071403245240350317800050840f003440003c0c41c0c03003001826206402e407101c003084c0980700f00095080c41110080142e0708460f0f0301d09488000840150081720700c030094000c0414081d000107400244504010f552044110600040b076080c69120401108090b4000300e03066950744500d802c4c5022a0b040404105812500400e1082e0441c0d4000392a07807018451a0700601c8007040c2c90000c0c07402810381c000904000350504071071004112a0103030400c50b441c0054007503071500088a880c1e0805040e244805130700038205034119110054092510720381110b0480c80c0c40c060400100720705141c4002540140b403404010027060308503c0b02c1c1c8044540c0502 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 546358021 1250 546356771 546356779
    0x21020f01110312040212070609050a050103050103051c050f1204020906060a0906140d0507080f09061611010b0607031d0907080402011803050d02011e0e031c020d050a0204090b 77
    0x2441400304100004544040281900c00c450946492001c46d52191760702e511441c03079001d0180c0124a15a001c03040e1402c60780c04540a1306803680d5200107500301e070400e0001502c1c80c2c03c1000c1800c02c40b0b0101800f1400402d41d440c080c0c2c64032082200d44811030300503094105000c2c4620741800305515107104090303041241190300d10f14020110402812081c0644141c009001c02081003008144200c0142c0e00100d608400a10446c80d00b404002c004500491f04020308800710000700311090b02c002401d6110740307015140c04034403100842095400751316400705e1940c159241c100e455240d8464001820070a0710946031041c1044003d440b021381c1119480320103024480c008104250558040e280310b400540a0270120030241381c10039034100710081600003411034451022048401541580580d20b41c110492446650303680c0d51301100c0648202e40d54800c0c42d030784203101d031401d41311445180342d000803020038005241801554425090315400c40d080c4180e1640800d007003010075118014254194400c803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 546359271 1250 546358021 546358037
    0x518060a050306010c060e011a0310060323100e0a140f070311040f050702250e071119080a030614090412030902040504050309150c0604060203060a21020f01 69
    0xc4000d00c10b00008007541d040141c0d04c41e000c170901c40b055102028a000000007408121010f410303030b85c40517100c484030900a00c1030f270f116a01c02005070f02c10482078170351002a42ea008000c0800d025005a42c042d4009100d0054032a41c41003850300d446030086001850380a0552044035041100c00c0d411041542803650300a0a03481e0002c00c00480c10030141c075840710340d02800b101c4500202d0021310812441d10100b916000c18004002d8000855003078100000038a00c007201c00610752a41990b2843c4240c1d0b501510140110b8485400384180958a6800d00c007190038880346207151300e859680000080e941e80c0720014005030a241e02d03002d0000940403402c034402c804c880740c3c404125060790003000600880308503a1403002c414481d400101c8e000f81c00030428407041c00c05040480c0c0b242d0090074034620413802c070362040040480203410b892001d81e02d540940301595840e00d41801070741c40200115030007480440042011b007c40001c030108089901c440000e80211441071046a060851019050081078 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 546360521 1250 546359271 546359287
    0x90106090b0f0405060705150916171c09030c09111902010e240105010e060d02031e040b09100e0a0312060f0e0405150606070f0f02040c051806 63
    0x420200d8040700c0d0030900300d690b41c4510300c115150758062600503503070110002450b40d05002000070070400c50014000310282d140c80300300c0c031680d854400c0d80c202941681004130802818222007401d00c49030313120360180c4401d40500e80e07200800350441d4001c02c001c206010700600c00e07c107059071224041c00e84044104611407075000c08210600580e00b000b107003040c07050b03055a0b01c18400c0d00880310300030042003200c0c80900080c2010000a0002029984181000c40000703015172290b4241c803207218000e0900b0317190021929503607010b0740c401002200c5030200c1e41c0441c103000b051115440d120714082c070800c00ca2428514210303400c200c50242c2c04841d10741800003c05984201203101c800c1d00ba45401c02c2200401604000c50140c55154842d076899503145038001030703008002840300d00c80c92041d82510820b4104001c0c0201c032070410341d042c0360009428007007480001c40000f141080c081c020f1181e01c041c800030703500007400d49000500b08030006501080e280034220702c1d00010342699404071800790400502c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 546361771 1250 546360521 546360527
    0x7050f0f07062a0803010f03051213032a030609020906150d090510050a0921080f190903030209181905270102030403081e0a0c11010524090106 63
    0x6500000118440c5220070781d40f89540c80e00a100507940d01c401010f4580d070303403103401a011080754031050f552401000040003d42602008035070f12400c080d003803102c1040c15601ca42c01688104e0702902a0004610001582c103042a8680002180f05004c04100c0c940784c0d01c140000c0c8080504001d00030210080e00d080450705203800d4030500c0c040c0f02170000d1680480e0030001d140946803404640110321300700500c61000c0c0136801c158103180c000c2d03403036444a02c0b5101c030410140c184540381d54009400c00003c2040b072903005400307907007110302e100002d4031384a800491035040361000302007200481c0c1c0c005030350036a07401c00703030302c224902000c00b02d0380020b501d04070440d22180c150722414036009039500c0c0001005901207503031143c225610304403108440c0d00c000300c11078000e502c1904e09070045241100040d8a4031716004141c0001700c04015074030802d840328482d6002800c1500303000800c0c01820271000c040c0d80380034071078984900810f8004078000000703015607100c09540319041a005c4c2c24085d00600480760 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 546363021 1250 546361771 546361787
    0x60f0b0a0e0c04050a0806090f28060605090708010e0c070b06041508070305010c0e0f0112150b0c150f2505040e07020d020705011107030602030c04090207050f0f0706 73
    0x2040329240d081c0d9555428044003103101d00d800003907100649a1011840d0000010150f11400d03016045a1048000280842d03586940d250b10742110010788034580707181400c07207001603680da00c5058040343d415200e00c0081d0300c0c6a81241d22100140106004026014200e140c803500100c0c030b1858549080b20035168024000402060305024584030361131030a1549003090420020540d100035100c2040d142c3c58a540a00240060440080c9c2030740010700051030600f40f8040d000105840d03400060035207034015806001c030840c10010031142006c0014100400800909200b500040600340d00b4850004a8020240141490300120b074200f081119a140d21050015200c49406102c20603901d146003c60b1b141c031440c1c1103081030491840a11035440d13000901c09880d021590255800541c59000440b0b20400b807100f45007645c2e003d03110030000302d10686c0c0195049400908154941034071000c002c816648002821101540401c110302c04100c003d206c542c101ca61074501506016260a000800c2e9003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 546364271 1250 546363021 546363029
    0xa03021e13090510030605010b0d0c020d05093703031409010c0206030a020f0708040501020c150f09010c08040602070315110f090117151003140c030709120f060f0b0a 73
    0x103540e00f0106030210003000c4401d006640c411700522042d80c4443d810902a00400c880c1e000c40c50905052040031400401d5504291070079684603030401d01c0107401c208000d000200c441005c402c980d00300402424aa400080108081c8800065081d1a500e00200a801ca010103a2400035007480070b070850740c1e801078220203c2c680407038000b41c41c0e4880e2209040280308010380090076650014000041107080000b078400c4807401d0b000c3d1060076030305006101d50b40803220320401d80248100310904c00342c3d54003c0035003841e00c010b245c0300445210980c0c46000907442500100056070001c03c00300208000381d02a262285140c40b000c0c0308050501a511415009001280b9101d00000c680920141d1003944001e0003804040000c50040c00d000180e41046905200381a000361204802d94282c14001d01900c4041c1303482c10702e000c0181d542c130300c035001c4250000f0b0014000c00840c0440001d001d180c1481740c038802030040328074805854080c54003070111500c0d20100070900303040100c82c6a41c1d545540001c0100d07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 546365521 1250 546364271 546364289
    0x1c140c0a0615080d0e0a05180703020c190f1e050714010302091e09091212041e080a0207050d050d030f20070b06030601150c170a03021e13 61
    0x610744090400382e042d41c1d03a0003074210b138415810103089035a4061200f110300d0400780c8064120f2034485050013032040c09100202d24180c0e90b600440e50140c0710740d000700000e008541c281e5421250680e0001d0950000080c00e4481201c4e0000c3c140034014010400c00c18802d010440c0364071005e0315902c4603111013030b070300c40c200c5028144407208402c1d9009404680000000402822070b800020b040c1e83d070120112052180513010910004000703400c0010b0450048800440c0d02d8144129802285050800103000301d44580c0007200300c04140c250343e80c1d010341da0361060054985482030b16074005d141080d943d0007640f190309500313002e10214001007450300c0c021001c2c6c40c0105040c40c0c0060048080c0c003100c000b4810000d43d80c0406800c04160345c007e07040c0d2601c0784e610081d041e01d0744401c06039203090a010b0010303100606c403802c0c046140100246d8176800c1c07080790010254032041e035101802d900464080d00102c0c1d000102d0480150404e1108081c1c09010400d5500b4005055140c1c5190380d410b00400c001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 546366771 1250 546365521 546365531
    0xc060a0e090a050f04080c0c040504050109030e0a05011b06061d090f030a0504060809071e03020301061706070819090c03030807140f070c030611040e0114031902121c140c0a06 77
    0x307242401c1c04951842231001d442440581805d01c2d2850090034541019800101c0040c9444500e24020440c042160030513583c0070002904800910048041c151f411a01560303a0100011080d0b05a10804400e0340d0000d21401326103001c0c0f5140d4140a11102d0340302043c1c00820403280507a03080b0083c0c40c1030302c551703103003a6280e42da03100070107031a01d40e5540040c1d4042110ba26126100d010704000d080544e40301398024030440c0e90f1138412000d60700e8140118500e13900490001101a03102d4040c0c1d90b40250080000c0d407400c030741140a4400c407482c000d015540d81401400a005154210f004242c102446180440813a10070041b06d0150b0b02401c02a00358000d00043d1240c18441005220400b640d00041d0801c9403000c0c4000d0b101e1190700900c5000d0140b410000000b48850b0075920658034404c002d0040c1142410514044041d000c0a0360700320380c4220040d4440d0030701b00c8100400000e619800c41703400409602c0e684050b00090100b1058000c1501c100320f40880c07210045030140b081c60380148080b070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 546368021 1250 546366771 546366787
    0x70201090203100204090b09090c0607050304210308061206041106070c0e1006090b09040f09081204030219050712050304081b0a0501030516110c060a0e090a050f0408 73
    0x2000d8022060069410300c07a99680074040007032680100304442075400304100940700c0c013050107420351b821944204030781c01c800c600c0101401c1c40002440d00902c00c00a484c601911400182c0d00c2c02c07104404c81502ca010210380c0d00400d600485416080403046845420803040114415502c0d46c0c010401049200d1560740d041c0aa12414140c65240d90700070b06c42c888050726020348100c000310403120310f092904048400124503004107554001d40300c4d82804545001400010b10015222034050304450550322208a40031804c600c01500101c1c00c0343e804100c40b400c041c00c0091410803103c007410051460b20b6a207400148001505204503079a5101c0e00b03020056504065056008540c807078035007401001d4600302802c201030021000e144040700d002c081c3c8da40fa40011070403100c003110564a08102151050080ca00480c8641c01c0c9640041c101c6028903e1030703010441582005003150089013500414201c40e25140f212160701075441074040280b803818010780b60510f0000b80014001300e0300050326074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 546369271 1250 546368021 546368023
    0xc031602030f0a05090405010e09030d050c0904020705030c0114010f0e04060b0303130e0108030a0813050a05121308010c0f080414120324030c15090a1d100b030f0702 73
    0xd09100c280520803a00e40003080c0f0702400941c4065440b9119518010001c142c0144c1c2041170360041d41400002c0d81000b81c060f0920b0000c1101519409600300144200c42c1c01d661039000a0217035620480144d41c072001983c82c154255041c5040403d85005100e006001c5000c041c50207004641c40c0754202c07040d5031038604103000180041002c161b0180000a0b04d80d403c1203445030b08000300c400c000b1013004161b91340c43c1103649a008a095203c002040c801c041010f0341c1090021205a50040007a581e524103651350780f0b40f820054030007444460501003020400c100100c6207150041060400901c09911000c0340200807811502c1c00c1801d00022001207018413481d40c2404c0c01c1500b440d400c5030980344a0740c10282e05500104d48803e40041e60b0800b651400000444420407020094000d09100303040380c0401c1440031007020004d9007107034180454801992010203000040201d840541c15000d55121100c6078481c4c010204a52030154107401c00c404030a5404403584085960320408207a00c50040807 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 546370521 1250 546369271 546369277
    0x10302040e1f0828050c0904050606030d14031b040305060423010b03070e0c0c01060e0105210a110f0612070e01020106060c0f050c1003020414090c03160203 69
    0xd164040c00081041014a0040d04511060303401c41000b0024503520488244c0da003400a001035050011900713032450294080c119280914412426514500d56030030216800610484e000d541540c0290b05114490400780090310418981d45803002140416411599083c031010b0940c1010752605a15200c0111389841540c024651050a4030528180390400315042c10424400c1100100a0601515400030500c03e80780001c1010b0050048149440d80b07510341400010b0042c030306c018080202e10a210428407031000039182c2c1203c81442c9505103c24000c08000900b200181c1c00c20040002181d1800040d41c0c030f1580b540084140394041c0600041070110011428641e0400d030007081102c20700c482420090b204403156541c0b071b0810320743c0100480c02c0e20101d00c80c140119004000e0040031600304038200d4031a600940032602541d202c480452888541e80003084002640401e00780a18030000c1a40086564122101030300750416501c0f407403440c800030706003018603400707504d107544118000c2c416 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 546371771 1250 546370521 546370529
    0x140f0702031e060606090d1202030f0a030e06060102120d02030601021e0d0e060313021203071410050109021305060a02120a030617060c031603200403062a0e01030204 73
    0x261542c44108005081c054880c1e080c607a0b4240c002c4100190040c20404207907001d03030341d000f4409801c1c2805a194460f400501030200000c600080008045071601040102004103169400040b01c0380428a45410644050100e5045400c07001442240100c0001500c285441c10759005907203486040040c2c2ca0242a20030304a4903205a0107241c0c0040000f0411181c621919110621074609032000c2001d03d200403610490b00a59120302c00001d8100800c92411074142c0364201d03494042180c44445207242d10300c400b95500d83c04001d2095030000d5a010306401400c3c507950075410244c0c410400ca44a45c46402180e028480c00b055000505208002c100d940510b20641c060751160f28900080c0904142c0c02406a0070107101c108042c21040040c41a101c2e02c00d030401d01c0e045845128500041d030451500b880e0405454807540f031440c041c4d4201030044c0c0e075441c034038050b91686103180110540745019180c0729008040034000c1d54032513101d00880200e21030752410f02c0d814980b00005034024020f07500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 546373021 1250 546371771 546371773
    0x40b3007090509010c17150a05061201061103070c0510021e011b051207050921160e1501050f0f160b091f090204140406060501030b01090303140f070203 67
    0x840015440d8065202900412683c0001e12024100e01d000340c4030891180070650b5170141c480c0000305221079000900340b9030f400050101c01655580c200150507900091700011140000c60700402c299500034002492100811b0055410113072591501d03841419548105030240c10404d800b012464405d001c42c0c8001040c0340800c0c250910b00c00344050017450105d0149d2800e46440541c91807240c0035a094680c80b6034241074000c0e4035515050300311070b103400c06c1c10790580040c6060302e040310154002a1a0b85000741c0e9000400d070304441e4911482d40041e41d98400075801c03c0c030b0014000c0000381030302d032440041001e00700304c0d9440007504100c000d41c0c41040c0c1d0402d00c1d800042151492010000c40700c3c540a806400e4043c41c03522110307c15074403050281c90412025409140b1045101c10725000189001e000070000500c5800c0740070140e2004400b15000c4601c03d584140501981da0544075401e240802883e1151819041d941d0141514100c40d03041075100c44042601104010000d0859240941c050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 546374271 1250 546373021 546373033
    0xe06010c0204090c1a0c10020a09030507062102030606030f070e102304180906060e0124050a12090c0f030515280e070905090705040b040b30 62
    0x41400011400103000c1c2c580c8070316450110f0f8170f2032411001a0f408002e0602d000d020440d01c01c5219800a40c400200c0c0745c04d20450704000408124203000c80c03002403024bd07da600d00c0c0c0340640241c04210000707865018a181c4144240440e5032940f0741601e6203c04110605401c0c2d171101541034502e0102c0b86070b09580121940c484070f036041d500040114103031850369610030b40c40d140b115a5420b90b010b070340104034a02c01040080c1c405600300740c205040c070341d00039400000c00c01c1e11010801c00e00c4100760044080c81088440d01d40c1070708185c50208903442c002e85005818001000f40003013450150800a404642c0c03164298002c0c040c0c2203240300000e002460143c040caa69a1030520746540c1031003003040d102c41004001414281c00c01c4240f000c4200e0740400502c81e090403034156001840440000c081c0c40c810074901080000217480307510300440c0b400d001010f206107400e00308801e41d0221842c403030050741055100d0b200d82e1203101940000d0b95000200d10740a03130802a501e1b08030390504c80700446503c608 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 546375521 1250 546374271 546374273
    0x30213030224031003031d030a0305030c120a06031109010320030f010204030b1f080c060a050d05010f15030b0a09110d0207030507030e01180303080601050d240f0f0e06010c020409 79
    0x300203d002c4a2081e1503106d1f210200c8001044540703030f081107081e010341040035410000f84c4504d004552011815403a00e040111100910321055011502c203c0d01c150340f00414001c3c02000c80106081040841d80d90f14690f0441d40c4048a0410f000c4000740e4079001400410500d135000c0c803880b1b01404881008544a035600d0a0086141c08182c40380c040f03a04c403105400d4001100346512200380c4089030700904c01c0340b440300309100310740c0d0200080104206050080307100f01a06405054000d01e2040d09440c2c9040c144001c0c0f11b90f07001442c40440038540740500d444016114100d0b1a800c4490303102c00020f03622500c04840c0000c1c41407040d13010820344001144c4080641050290074100d000381c0c2da03401c0070301c200c1d070065030b00007032800c00c060079a54550750800000f0700c10a070700d6520080600d00b40b800d001c80000300d038040d20851081003800c1d0300e00c84007503114040582801c40080c0300005214080300c2c034140030f0398440070316809410005842c1000140d800c0c3d000302c035482c07041a400780081003401c0b45 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 546376771 1250 546375521 546375541
    0x20c032203060b030304060f050a052503020d0f09120302010e03030f011a0705031206031c12051005010c1e0f06090b060316051e03060f0a0c03021303022403 69
    0x25800102e60440c58503841da221070500005441c02e640c02620390000072003000c40c0540b040d4006e00890700c204541003004a0490014441141e414049003d07032444144041c51301034206282440c0010811200d00d0a400d0401c2c1d000340e00740221400703041405074541c00c07824100e01500b0802d03280c4d2440c0c0300010a2020110f040c0c40c040d07048405011485002d030703004444411a603c1010000340c415031060090388403040d581c00004d600650001c0459541c990001110510883d200d03029a010400b1442d040e40c0034031907405204d520110070002e0034003542c10000082e00908020101818035041601c0311148190301d07a200c00ca800c0c0d0009800f84c8200c02d80e19120020f403400602c103c1c0d80d040d00c040411070078200001c1051420f288040d00d416481c2c1090140646400c07000c900c1010041a51150f2000b910288100350040402040c4008986091000001943c10032107481c1d0800d0710420401010345041100c80c01583e1b41242d000c081017614681209024a01e8415120013810020601400281e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 546378021 1250 546376771 546376837
    0x30e040f0c020d0f030c0c0204051008011109030114040f0311030f0706020d0f090c270509010509070f05010207091d010c0806030d0c021f051201030c2610020c03 71
    0x15003981d88158490100138100d064030661805000032500d00302e598401441c0c01c0d0000d076800301101504500301591102254203451002104040f0702000061540c06403d080c060a20142c0d1988144403d50800d966035002400d8500000b404014001c1151401180c00344220f60441c50000f61041e282c9006040120080d0310000d00500c030b840c03400c6c622600b042900d0040d404110f81010401200610702075003a80b50b031200d424440d40e1403000002c18081200305104041c05403180c80300001d03d902e40603049a2802d46c1ca500010501100c20004100d02d81e400101103099544051000c80d031070a5a0424a02c40a2140300e00806542031281003a03000d40d0102c0345a128800c200c04652890f001300c101a10600030f0301d81c000c2d40101d400c4075072200312660300000c0c1d00350b82030b2454910310f00070324503410649842d020381048404150085003007040b003680b1075151241525001c0c945e4014100040d125a980d60f0051882c00001e8001c01d4010f0284024010740da00640c0c200203a10075859104d1444110003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 546379271 1250 546378021 546378043
    0x702030d06030b0a0f0c0c17040f0902070c080f12280206040b062d011412040b0c0f12040206090307080c1003060806011211060706020d05070509030a030e040f0c02 72
    0x10b0b185c11820300c6010348071b005520f2400b402c0c4d100d284484105403940b900e140e04c02210071144840c100000545010750345d1000c070080c0200d1000503103d1031039140c1030301c102c4211350281d0a035074028a48160503160100d06000003ea0443c0a0791303840d11403848052030180d16415180c400ca0041491002e001e40100359244541c1c0f00c1c0c26604050b41e90780c000c0080907580c0d02c0099080b130001e00c92000220000030001460240141400700360b000b6042203640103540540000722003800514280020415540c100c41c0d009028103404a050800d000340c0a807540c0141180b4510b0102c00308040340954940f6800c840301300e203014041d5624191950030346079071003e244108900a090310140d42002d01d202e44241c1c0c06440c0040c0c094103481e4030740070303010b807900c54202da054421301000c841c40040c40d908d540c010281c10380300b00d0000d80c0b60706029046100702c80004003143c090000802c0040040c2d0340c0401e0041d203050745401d214010700c000f44c001c44c004001a6085100c00342c5014882c800b142e0300041d00003081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 546380521 1250 546379271 546379291
    0xf0c0b0d0b011e200613031b0822030b09010606020606090c030412140a0305040b1005030304050d0f0507060e0a0605041d040f02090115090e1902030702030d06030b 72
    0x40c40c190700044500d000303a5040441a030300400c1818034000d2280501c51812018441181d181c000340314030450501c1004e480214000031240403035010160804880d40c00020342a210340c40e00210754503040058812180ca000f6002c001c50408002c01c1d1400c00b901016580205e096611450407070b80c040e000706094091071780584501000100c035483c0140d28984070b1014100002d0964030703550390340303e440d04181d8202c10902c000480d5004214440c00003901030840b1300d58000c0380f01e00b414100088004400340c45002c0e68500d10005100c070b51800003c039070440d20141c0d138424401a43d410545548003c45100805600400c1400205164007281151a8440450f54074400f04e60701d0700c041d91184568454032a40400000d0032032007040400349001c0e441401080f07030a0001c2595400941181d900760001200700c0c0b0380d655a010310550250072130000e01400612000c0500f0004201c48100350342015007031402d0740000010300e03d1072090058841c0b030364583d8418030040e5100c1c506a075100c9000c880750010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 546381771 1250 546380521 546380531
    0x903031b1206060c16060504092909060102151003150c320c01052203021b130905010c020601061404050f0406050904030804050105160c151d010501080118020315040f0c0b0d 76
    0x10080c603174036007201101103602426a001112b4007405030500e8020b080b14150b009802c0080d68940b169a0322901c40d00041410061890a5103440c1e02d129000071050501d051034a000b120703060390010081111604500b03040001241481d9904a500c5044c0f007078800b071140c020071038650007031054005502a910b01d0403c001e40b0600300c00f0200e03948003160b40107401a44000a04d02c61004820007500d4002000b80054031111203c840c41c2094400c0c400080b203403030795204140e02d040c41d4140314480c00351031280b03400124000c8014a01030303180a13078015a03100b007100c0304000701c20399904d500003002003030060121419880d2034140548007450407202a569942404d0020300c001040e9611181c6000307541e10f80c014948260f45400d607440340c41d2407920500540c0e8103404000740c000007030124010481c0e00d001042560600c1c520a0139a0b031030103a843c90705404d2130541c80059502182007942c034983c00740f200c002551035041260200111480188c10005412000f003034000444002300100c021519041c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 546383021 1250 546381771 546381791
    0x1081e16031a150d1707060c120c091a030a1515080705070b0a0506030c03070f03110301140705161a070e0a03110402070503070b0903031b1206060c1606050409 70
    0xf845000c1c0d40004d0b444124207510b00c0020b243c00060700074501805010a09000140d0b0b1074100721112105000082005010400180052405100441401031a00180862502410007891040d0103d409400f05010001030f900411035880032804000140c08058069a517402000e000341c2c07207030304003070000d0f112070300041d240c85c000c00c122460103030700c4094200c0355030341c08446000500c00603040030b80c180514090328800740c3d030410210002c0e0420181a41d912846c40c83c000361000c04003c0481c2c040d03410041200c0002c10280b05117075014a0ba400c1441e90784481c600e404c0300c002d810356001400084040d4408041e030314180319192241240352070b01c1804000002c104400c5ca03030a40b000404030003c2401c550468101a009405903030b100307008403414261240e0301c1d10b4000c802100e0000c900d505c003000704003401101e05074082024146c500d070107182c00a100d68005240704005c0c0014040c55000400c8185034908204461804000790082500c2c2512114010540d0b8003a1180035003843c10940c0380030b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 546384271 1250 546383021 546383041
    0x101806050a050a03050910110918130609020d0501140105040b030f070303030c050903070e0702010b1c020d0311060901060503010b1e0411070803041a0f01081e16031a 73
    0x25001c000305440311400c220304030700100c0c040c0000810304102d174042d188401201c0c40c82405100c00644130280469140c5e034482c014810300000b400c14220b03001d4207050500000d00c03e00e505003007a503a0452004168004540041000400110001801586400c000400c0b0301c6000309880e060300d000321410312050440208065030f80030b40510b0581e0302d400040c81000060300076030142e00e004100b8208141000c408000080c2040c03d01ea0214810074084010000c1069080c0700d8414a280708030b90a85090196506101004d00414002402500e4111035401410b0091490405040a403011201c0714600880064040d202c640302d468025803c1c0581c00c4114a40388100f0200403200e4521003014100c207804000140c402c0c0d5005a8000d10b04201c01404030360340c58002c40c81030740503000eaa0744110f402000d90a4109008003040d40a0580c00014060b080d408901c1c440d050b00c91500308960301d22a030035003e042292101030348200303841c01c01001080140301c0c104030304c603000c91381109000c0d5a0386c90958 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 546385521 1250 546384271 546384277
    0x1050102060f060f041503060501050d0c090b01050d02070f050705010f14090a0506221d13230c03060a0213061b0b0a0906050610082410180605 63
    0x10601603040078001800c1448641c55060303110000070010b42e03140f03103130002080459560313210b16210001808814800d2188902400c1c3c010202611075642046580c0c4840c0c40555860207181c004da600c03401c00c03558030380c41781060f00d0ba484408042107503140c0b00c030b160404081490000854040c080d5840c009a5507001d180340303c0c842101c0d40c41c0e806440302c03040400b00d95940a0031800350b103c602e10002040e1525260b000e01480200442002c4001d07002207001620810103500594601c0000702d070074a142e02d191402c40e500500f80991001907a6403500c0c109564001b04580c0d00e60148254001812a00c000501014a40801d41c2900e02d1510741d80744240c00d0380308102030300f8080d820741c610400c11b180c45112509801d000d0300c0045010800e8031340d20b80c61031a074261407140f0540e4440704000c0512506104240c2c11a100b00c07110f032400009210003074481c45009065001d0b00080c00d407680d0000004c2d400c58550500b00812100362001d6044010305a207225041904002150314030214450f8025011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 546386771 1250 546385521 546385529
    0x40b16020117160e011106040528020105040e040807050a030f030b030c0a0b03060a1503020306010905010503060d14030d02040315060f060503040b0c0d09060b030c0402070b04060e0a0b0414060f01 86
    0x80c2000300600c0004d03541107660400303203810010041d81c503090f412014000c150046100d03401030990301c1c142c1c181c4100107000c0c1c0c51201d8010822240c100d03005130f030000101c44c202c17040c0030061070a076600d0b402e210070f0a0080d43c0300074219016403200c0404040c2d00c05d100f0340d6007400e41c4c0c608021002d850404e0550f114000c0360004d401c4030003c5800c1c81061540005180d000308000c12440e0003035107030b000100203401c1035030350000400d07000300901140350b0700001c000021704000c0c44e0003411860031a00203802007608080142c10000c0310105080500002d104448003c03240038001c0d9519541e030b107490740b54020304216a0311010b1500d800880c48195a207004012100c00740c0c1c9203030850311f450700c0d00c1d000308ae40500030b2000c000d81000150701b060f43c94011083c8543c010fa00006440c12444240360034049622156841a03204101c400001040d80302070941003070b0000000a90010340d421914074111820318080c00c90f0b0f004004000802030381c242d1100f500c4085d071060b00c5040d220000301800564007030003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 546388021 1250 546386771 546386791
    0x17010f0501061409041d07030b1504020304030215071806081509040b0708070306030c1508010602191103030405090c040305070b070b06122d010b0904080702060a05040b16020117 78
    0xc001d01251030b286c1c109083c42e20100031104184559000401c0c90120281c1c4111101e5407a83c1c20051150300191619040c0b01059405526503d05560025107600c00e103010500440c80102c0801c0065100340c000a100d504030703021004c940c54480b14040c080441c115210050100002802101070800c10f124a00403540a41d141c0660b0b1280c0c20141e40414001f0052010035990300c1e00000415808001034004000214064512a0380b1100003400140140c001c2d105551007a41107152814002c1c03246180250085000da00d141250000039055200700d031700c0306034050550f6041c071214065940040c0300700c0348184115241265039001c1c2e6502030140420180a80f03a00600088079410b2543c1860058865901501c101c821441e50741c221680300401c00c044941520208180300420034816901990030441340794050b880c060340d03102624410104028096a408201c100704103004005640140801041e01034130352500705045110508148000c1e800a1070700821607a0301c14040c100c15010b40c080c10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 546389271 1250 546388021 546388027
    0x1f0f06060203040303270e0603010b1f12150602030a0f0c05070611100e160504060807091e060306021c02030403080411010203040305060408090909060f040b1017010f05010614 77
    0x1071816100e00c4441c20300d0000b40b1b0302d500052411180380941c0c0e50b000d02207035170021140d0309080c02411f084460b00a841e43c02140c00141082000a0381c00c031300900484503240c1010703400c110700d01c140c0207810300346074050345010031482c0821100d80110180901052036941d10342d03620001072085078800716140c805440b6812400d01400380c02e1082c0c198403000c1c4001c40485002d8047c0c102c0b81d10481d018074000c0d00c9281c0084000c0c00104a01d0710702180208402c0b82c00b8401a800c1104040d1290317024420782c80d11560785c1241908076008150f042c6e40722415540304001c201e503a405c108003c0e501080341103221150341e41111340d25a840d0b1094078082c58060751003c505507980d9a82141e40704407401518150b120030701c000000a02d04000c81807203148910790b032540320000303001070000c1243d0240081c0526040f4500300310004011080c3e1b15446500640307810300c0d0b81c071001e19aa440c1401034011030048072171802c03030120100054001c45c1e90800c1e00002001760360f9840c80102e40e0540700c24075000b0b00007010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 546390521 1250 546389271 546389273
    0x4020c07060f140f0702011413090e030a2106080f0a020a060503091009150204030813051215040303150303171005150309101b02120702090f15031f0f060602030403 72
    0x240c3d014005d0b040c41810801c01d69403102d083c07110250414603480031000f00725601400540e045002d20400c10901c000254181082c0000c060644440c142119959642a0071030701e600f00c2864018100400f01c0768192407040780f0800031942c03180749240d41640140e0b9042000904070380f08100316881030820101601424801140d02000f0704148082917481300c40144001c202506030b480100700031882008083d0745c07403c04a1142c0000400e59019038030603012a0102d40405601140001c0c0f610b03400c0c81c0c2c0c1c03100c9640d01e01e01178000b17010ad418040081400c9040100800d0b410240d80700042a00200308281566480707202070105145010742500007640c241c1c802603035503810000e1900111044161000d1002d900f40b40c0088684c501c1c04040d0611401c1148280281c042c0036100c0e01d02807c5503894036190041d0040341c10610007802030454441041c000580c102025014880e070035100400741d17042c0d1044540c849412000079402800100d24201148095084921400048400c9500590305142c55 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 546391771 1250 546390521 546390547
    0x40509011205010e0f030a022104120c08010507050306040b04060b0a0c060f091b0e07051207270504060602060603070303270927051c0c0204020c07060f14 68
    0x2a01c0121a41e41d2102d44201c59031005001120480f449400219101c90840c0b00013490b1a031041701d0704641029200300d19000152020440301650014100040c600783c0e00d01d0302906c12202d5500032a419441c01c0c0a002030710741e1080040d40140e0041301e090084541c070100708400c4400798400c0e113604410821400340c11501800078800401c0c01030a0003d00000f40b10812001e0320420324003190315401600100c1040f0b0320072940c40020780302342d080028840c0b60407500902248070701c8641c0c416110601c00011166071023501c5e160300c00824a8510041c00e02e20080500d850b402c00c1c018244154200384c07020074030361b00c00100385224001c010014081146551800d59040315000582d4080444028030002015081405d51005140070300c400629a9552403580a200080c0076000803204410b000c05c0f4041200056030744608070a80340d038601203003032885040e2007100c5140c0b0700070340190001c1140b00d1030000c00701711303a011654651503400c2250b055003011202244002020448900180010f41542c40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 546393021 1250 546391771 546391799
    0x105030c24040906030b040309060801060909020f160f151e09021c0f050106091a040b19140f0904020310050606040f0b130504020906070303181209060f020304050901 73
    0x401c1c405035280c15115282c0c1002d9800a40054481250481c00c0c003082542c04200b01d4020b100d149080040c650425500500c14a0140700340702180e5004034100e4a509040c504a90706802800102c402900551500d072180800741d085c1680d400300724000301038410074140902003594004644410910380c080f003100f0014140001e00341d802c02d240120841c200389400303800164003070048541c5001e518172032030071702e080d141a40c10034140d0f1030034506c1b0f0503544003800c9d40300395942d14122000701c0c0c2001914045105114039a00112a006800031300060b05c04100e58518801d100540b401d900300041396050001c41541680c00a406501001d210600c800056100c0750f00900c005101901d059a2030784a5000b2081c59081510410030019011086019643d0b80400520341503e06508150b804c400040150188407805010726858000700158000c0c4c810300843d28035807001035001c0c840d03030130b0000a01510b52806020007080c82d00d10b1000b845070002080d00c0868800914140240c0c5c00e100003c55034203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 546394271 1250 546393021 546393079
    0x21005040f08030f04050c04140726070c140712150915050a1406130b040b0307092702130221090105100f180c02100207050706080105030c 61
    0x303410200401c001070b0b2800b000b140501011030f25180f0500b0b01d81010317401c08000d158032500c01ca2810042d41801445225803c0d4481c0c0c403410682508649201d40107500d460341c5800407541c00c0200d0030070904903002080044518000e1140300ca40101400c080c581d40d20355406200400c0151180980001d43c20b48020040074018120104540b401da0307039a02c00d07070001c03c1124400b10351180100100c0412a01c40e00d40703074181041c0180c0031420503c000c500a02c0c2c1d0004d0a20000c0e44900d1451955281e94020103003040014088901c1c00e607480b03041000824400d0080203018040c0b035400e60640ca9440c0040035800c5d001008849070316a0041c9480003075021b01104004595681c103034007802d00380e00c401c151041c1c0503c8004522858010540340504051790855850742080c03010a01c0581400c40e21300d510300500200016014500031420ba2030903030782002d1840180e000040d007108010000c0341d410101c0f4a40c0d180c140c882e0740c840302010f0300c81540359002074201e0b0300140d00c0702c109100c02c0d040032241707 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 546395521 1250 546394271 546394283
    0xa1103221401060f1502010b1e0d0c180b010212090913020414040c0801090503040e15060a0e01080a020901390501022205090103030c02030715110c030102040602100504 74
    0x15030524411982926a04d5012007020f84800104028442440d034400c41503440d988020080d03040c001001581e11010564924141203260f0b4000303410b03484503000290200c0d042100206000d6492101071103080103102604641030074107091325059400061176401c601c0112200070700382590b00303041c0061360100400100c1000500301041d00940c03180c1c85903400905a00003c061289401e0900c10030b80714007640001c01981c50a103020300816400703c20303035060b182c1c1400c000c446900c4900e0040200c481404c051544000e00082e590000d942091001040d010300703030cc1d00a07590307a503d55900102c2c02420b40941c041000812040e800e20000402580c2c594000d03030400e0b00c0d0705d59203001c0344040d128103039080329240c4d800607000c030b007103443c0d03290300d02c0c4014041e0400c0300094103041c04030300f4001c4103100007010b200030344905c1d00071136801780700310000f41443ca032160030380c2c07115030340e0050580c1400340400b1014040c0818074855420107008440a4500c140c0050207002000c0088500074100240240c0300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 546396771 1250 546395521 546395543
    0x120604150305060a0504080f04120b06031209040506031e0f1603030c0303020912071203080a051317070b10051f051801050f0304030509120f1002070302030903060f0a110322 76
    0x8c8003d040090320140007120348a448400c418503000540a0303010b400c562180d44200d500000240100b02100c04105043c0d0f400701d11500c550011a05d0520000e00300343d04901d00300f4039198600d10025540b070801c0002c4040307a4040c0c1040c160b40780035500758000039000a05480c070180101c2c1c02a001042010b02c0940f0855050704a42c1e4442e0400c1d01075001342000c0a01d00c901407003450380c000c42080e001100c0a40402c00c1c0c1c140000c0800410340c0c0d1b42c000074041013004000011407a515001d8964075a007024a200207842c1000d945040384045004442c4500c051001c0a8400911200718001030344030b0703450b1245030100040440b9516200500510304010301007104202a500a0740a54000c5110fa19525185c4458800304100c12915000d1440300364000c00d920f400343d900c0002d0400780c3d003003026001030703484200703003002c030305610070442641d401d886901e040c07105c1402840c071740c01d209081007a020071620102c80204449072006881440e2185c1c00c082c41030f0810079660300000c41c030303d11880030081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 546398021 1250 546396771 546396787
    0xb0304030203161b17070b030c0d0e0a06020f03010f09090209040228090608060c0a02030a081305190311030901200115060302030402030715050d110f120604150305060a050408 77
    0x2130004100d030040345c00c440200390303444101c00d0108580005800b0f03512040d8154904689020a1405207441481605444d03003d14050182c0c00d000038114140c200d4410355441060741c5240405620a1055084900e07a000000641c0c007120703c2110811980201021101e031250740801c000300f96080007501c038906030307007820300c01d0b0744001680f85005240140001c6011850b14030070383d08280b0020300003001e003402001618205075010044400c2d4075500d0034910300355260305041d40b08002c0d203010010f20340d01c40d44000701c210000c2a07180300e00107813080c0d40c0c80d0846056016425140d005604000e4003180c10b500000384940b038900c40304d00d40c1c10184e80000403904100d01401d210344c0c0c03a9620190100e82d00000384400c1d4102031001402500181d0303005900f030301e50414010194172510441600140ea601681c50340042c00000300c80c4050300540c04141c81c0d04241500c3c010030700c0c050b544076100b80c0c5030040c01180c442e000301d41c680490350494041d02903980d1300103841002d000c00038400c90b000385e070400c0319207 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 546399271 1250 546398021 546398063
    0x903120b06090d1103120a140a05040504020708120c090a033c0b0a0213050f010c060c0f1106060f090712110406020f060c0f0702030a0602030a0212010b030403020316 73
    0x43c0010b0085142c0214608501c0c01c0c103050401c0e0400c4002c110008000180405420544540c0b0301c1c9107945402d0790319078004404a803540103c2c1c1019a001d40005210401d002c095406040381c420b0700d1541c0c000e140c403074407111801c5214031100d140e041614a5801c102160748a180d40607015a68114101000014621403d02200d0011a0141c0000e0801180140559842c83c41d0b07201c02c020001714608070842d41c50710349a2040d842001e01c0380b0039004c038258072640f1401d04141c03032950101c010301c1800c402e01005040d82071000210000507520101c800600600010840d0050b00060040c0500c5a07118003803181406005141d2024442c40320320740340158529104071200c0c50f01245240d521503041c001e00074100002c10b0b0440441f51301c49020700030340f5910306040b40c85000c030030980a40d41c2e05403880401d080000b00e01025211920210030440c440c60150020018007100d0420f410385d503078031030128440600041da40900103030700c28000d400c2801c0e04002d108110ba0301503081d01c1c0110400203200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 546400521 1250 546399271 546399289
    0x71205071206020304120e0a09050619060302180a050607020d0f080c0a17340b190e0601060804060f06151d011b081b070602070302130903120b0609 65
    0x840b8010360010030001880801c03071003240d0b600c2da14509420700c401c1d0940010321241441c0a400d1340301da952030209480b81c0c1e500007880c03000749007405400003069807014041c0080d004401380340340070040a5220386140c6040050070041c0c800c020301d0036080035401d40904c1407224400c0340450f683c51400300000c02007107000000c1d208500039100141481515441e14240c002d804043e00c0410300010301000d070103a0704418202c2501910105841c1e805504030390200e6084000e00009440d00c5462428020150485100c0d040a040300003014480511400b403c540da40c1024420b20380001d0141340803500056182d0800741111244d46030116141e0b4844074030b482d1303481d080300c00340300032604e80201c40368945104002480104000d080103052900910300102e501640c03588003d1070400d000070b80d1102e180c5241ca9511b05079458100b2503070b182d505d840c00a9500d0300b9602042e442580c1409650a41170f080e805021241303503150b6150051040e9001c640c04c0a4212403003110341c02502440704500a4492100c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 546401771 1250 546400521 546400523
    0x31207060b040b01080f060111240f060603070f0f0509060d09060e0c0f190f080a0b22060c09080d032c03090603090f070b0a0f030902030712050712 65
    0x24951030741804000454080200240c117000c5200d00b0042c81c002a180d65561005c3d0a09018005507216440d0900301a4004140f00d51065040c28110b0b148480306011071003001c500d081c60b0000c0d1181c00c100074881c00201c802400103500450f41c0f80c141e0740714000040c41c3c0703002820041e040007984000112903400800108080550304d4005d581844154082c400305c001c60300000e80355003107840d00418821100303080e505000351000c126002c82410b03031700140f030002c1c01e0b0344090300c0c3d0b503e0f103480c81243c0724604008280e903285200000701d09841c0c00c9101c183c0c598107401030115008812580c030700d0050300310844140c00f07101d101100054228004c2c0000c4111849075500040c0b480340c00301e410000755148003803900300d0811405464090300300000448031403003011100d007922076031121003091406215900744000b90056450014480340c0403c05801c5081c01074440d40b0307d2102c506411011904d5a14010b549a8850b8004210b030380c103c13185058201c2e0240094030804e6031181c00901c036600c05500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 546402877 1106 546401771 546401783
    0x1031e020f070b09010615110703032706050a0f111e1911010e030c0904020603150913110d0c150302040312020708061b030f06031207 59
    0x65034074030395000308403810302e04d0407102150203404544150081c480701803c02c040140d0281580089881090300101211891614101c0b840d0030031000f51030f1a0400c613010107a81900180700b4034007403e12521240e035204041c007401011800c01207c0d41d03040100b040400c00300440080303110070080c0d020810130b040350013850a1a1f4100044a0394181c0c04a00d502c180008000f41da0900c840107400c00d88410b86d0151014007416141c40e048840706511038444400100145006000346402060502d01d44055896200125050704010364003200040f4840218004004d15220706840f461401d551086038030070725582d503501c41410390240170300071104841303003261440c030036416100110382090010021101d00c000103525500036000b500030900800001481c1712142140405200f0042d00703040e461640c50204610714840042d001581c54042c0b0b10680c1d096400402c0070340f000c2e40c00b80c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 546223021 546402877 := by
  have h0 := BRFrame.cov_init 546223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 546223021 ≤ n) (h2 : n < 546402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
