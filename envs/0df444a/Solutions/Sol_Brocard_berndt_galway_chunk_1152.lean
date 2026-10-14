-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1152
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:28:49.53298+00:00
-- url     : https://prove2.me/submissions/81aa46b5-bd15-47b9-915f-cacd7800d90b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 207014388 ≤ n < 207194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 207015638 1250 207014388 207014399
    0xc151c0b0303160303090804030f0203150105150a11071e060c031704030309020409060c02010f09080904050601140409021201080a110f0d060203151801030b01030b0c190201150609 79
    0x4141e030752600100d0032030b54000040b483c4c20b80081c801140010f0100c000440d001003404100ba018051403402030301924075207000c0200d098590340c02406615030001f0301d1100e03a44000d0324440982140f120900b0301071138980040420070710342251a445001c0100103a01c280903030380d41405003c40140b00500300500784141c00e07a03000c2d0242002200b8914655283c0d0002030903d031003a003001190039006032040041501d1420880040c0601c040c0420166007404000403848000e0300c9565120764206414504181700f0711300300000b520b0b018011a042020300c0790400007100e01600108010030300103c00594900c000b4100e0700507000140e0002496400c58000400401c81c600c051054030b007000c40e100304042c0f0a103000182c904100c0d035070181c002440403040002d004a20380b058290500b0840d5247d031041400e01458117640024000100090ad072900100300040324604400d42004500c486542044540d40c1421085183e180000c0d0040c2c2d1540d49200381040c460307080300098026072910380042410322 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 207016888 1250 207015638 207015643
    0xd1709012a020907090b0a020a031d09060f04060812030103060b09060112050c0409020408060a2d050604110d09020f0405010b160f0c0b120a020901080a0c020c151c0b03 74
    0x20788040d00a2401c07000103808a03120b64010300241c488103400b1501c81089500080d9101d0440300220f000c1060b055540d40c0c8103207150f800405031000205220060b68609052202c13900103107c0031500182c64600124207000184071800070320300b082c031840d41c4940c9981407203800e0701c41d811503880c05040000c09100b81d99902001e81d5100c02003c44000c0350302d440b005501c000f00e2043d0303488040003510100b004100e01c02c3c0410700c80e000f004841000e0204e01c0808a119940c2c02480c00003080404000400040b12552500b126510080c014070005030300307101d065001c10a0340009030304aa020b80c0c1c0e04142c4118a815031108143c0d4500341c800300f11942c10711510700182d1155080d00d07001180c1218212041100d440941600c155118060b800000d641d004031030aa03800c41480700381c440c490034001406143d070900c02e0310380070741d4144e55446a03615155600002844080031400c00c40c06060103100064880b603500e25140000e29030299038400e01c8440c0200c0c1c4005034048a40340c80d0825040c01c0155500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 207018138 1250 207016888 207016967
    0x5070905160f021615121b0809150f010602150f011a04030c08150711070e0c0c0703050606030f0703020a0501110708010c030203160e1e0d170901 64
    0x66040505600800d090203070702c0d241031100c84c0011030b04104800701c2c8100301401c80005550003602c3d20001c0b000c0d1a501c00e01a80d10013511071801d03051141c0c02807080e500c2258016001400c82c8142c0d5140004140d059800000843d452006240c1c41401040710700d0341003241d445100080101d1a095003071034807900102d80018440d2800d01d411032501c1c28244000b40c0c1c1110011a030042c03003070803915902c0421a486500341e1040c00c101c40c102800244c40107020707203074102510a0b810007420289003001c090309903502014040d0181d80005101c64441c0e07090401c0b0f200e0186000b40014402d9240c404101498114a01070080142c1c120440c01c000588405203c0380a90706c007400d12103860b41441d0011031030120b0541c0000c4140d0b00b0b100b010030301e15405600450003684415251059003420b282c01707845607186161220b401010032039011140e240c3c3e410f0601c2c85140010590f603c034003000d49605403420006501400c1184001880c8001c96070000d01041001560086900e101c00304207070859405141c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 207019388 1250 207018138 207018181
    0x132d1401021305090702100e010b0f01182310031a0a051302090607050d0804020a06030905251a1b0d0c030804110a0b030a05010b03060f060d0b030d05030405070905 72
    0x3c841005c5440c850090001e080e540400020401c80b0900d41c440b014043c1c41d03401c032001d000c0c00c19280341d0541c0b03500c0351070861580b050740b032644d0b22110314101d8601c00e622024101c50300c2144ca1002c2125813540c03003801c40044024170355804503540344040d003a54420790782120b8a0f8812a0028010003ea031140001002e107003600a200503111303490040803402e20300c94108010618090300d0384075a050358101c0c0d20280500d00907103121b40c9240e12003038241c04030740004001910681c0708140403480c0030208151600328076848022084216603400440842200000d10410f00240c040f8103051210303048254002000b59902c028aa100d40004001c0d041d050b00d041c1c080d0400194000041c20701c83d901007900d90414001d40468105030359034008001a070000e0b682c001409090900000d000c070705641c250380c040c004c01400850400300d03201c2040410361005d030708034409580714a11240c15943c18072040d9040070b01612010780d01e02e41450f280f414018160000c068041ca06018014003221a40d13107000140d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 207020638 1250 207019388 207019399
    0xa0603110d15170a08040312090302060f0a0206090a0b010b0a260105010e03010902010917120c030c0f150703020d0e0709020d1a0603132d1401021305 66
    0x162980d509a1078454000c042400034107004911038550380401c0d4140468800b00502e80c40c40703005003c4581c45400031840600350400501042c004904502c0d110188402d160801e191038941c0c0380e0109104c0d800000c070a10407250017040f441c442d00e805114581e44204000e02401a07640c0c50380e98484404018010840d42d1100070a484500f28011514040220702000605840014011071351031240d809008080c001800070100c0314860905008006050794140c66900e043c9040500113075001100300d05030080f40c812103c04440c02036003500100700849a880185a88640348048280342c14282c658400860340500480ea19166a1208040c0c200520b89805640d8103041e4454501030105259840b032030b401903c2000440080c0c0e03500500720021340710424812029194000c0c00624011200a60040c07410000a010000c29108484007144902c09000408220300884084101d00d40040d401800c4040124414802102c3c0074000e101701080080d0300c0d1440b041d0500007000740d00c1c81124000e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 207021888 1250 207020638 207020651
    0x10c0b0705030c130b04060905042c1014060f0a08070509060d0b0702060109050606040503060a270b0702070f0b1b030d0c0e0a050111061f0308160b0105010801050a0603 74
    0xc108040480c1c441c2c82c86480b0403104241c4074500340e030395030380903105060101e2041c08c0000703440d0816000d24115011501d106510b0404a2086030b800c8040c44000b00c1b544c3c0c001d1000032601b1315068800c0003040549414a11114039144090210056440310494032404042004001091000410409640058542002d40d0f100d9002190170039000b06002020701042d041000b09680d40064858100c0b02800c5042c000d0742c481201303001c031600c42d5000d1940c25400080c00544015219000550b4003403004100f0081c110b940342c400040c0c12403102046030b000a03048207000400780d04000d03540c05001408509507840c0d1400003e030700e1034451044d660030700d02e000c088410f03d86101030042c0e40341c0001110f0180916003115a009006950303d0281d80d108070507400000c98194824a00161a48440c0c00203201907101c014040503c0350007079218100e0500706020100004154001424213202800e41004281346146080754030420143c0166041040d641c00402c42540d40000f01403c546186c01d001819 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 207023138 1250 207021888 207021901
    0x1701090c02101b030501090213050904080c061003110f0d0b060d0606080304031401150303110a0c06120c1e1d06040f030b010902090a0b28030506040b010c0b070503 72
    0x345001190002201d500d02102210201481c0281d2000320003c0e40d020000ca81c1c0300c3d41424200d000c0c84090021294400c54140950305040b54001c1d0084e000d0041c0c20300300020100b0081c82d0070b2003160103200c4a5060f290070800c00004100b8115007800c2150544c550007020b03000f148802811043c09400403080c040410115111810805165500004107000107a101c0c00d606d42d0780c0c0c0c424441102e000c00355014500e06400d0620901201c01d1100c08004425442d40d00d04032000c9190340030340c1d62203001b00d428500c00200e10b0090040280f43c25143c1c8884c9003107102d058804c580b400d25104003800307581e1205e10143d140140e0010100781fa541800c16203d03282d010350500503001e02090680003c000100071074181d91010005048034410304408500b603885840c0141a4015030181700c1d00403401d03100502c217403180b03a07020b004181e641454840012800d030b94098100440740381d0071000300303580b41e080c80f0090605020f051000e210a003444010150996102c0c00a2070000b00313201300308400800400c04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 207024388 1250 207023138 207023143
    0xb0d0b0705070203010903020f070e101203021203010608010905090a0b0c160f150e070807230405040c051203070305121503030403050d080a09020303071101050405120309040c1701090c02 82
    0x12483e0007074000c108140e80f620300a951460042d103c20898820b11030300003822171404200c0341c81021060109a015450044010300041e01200d044095004503c400c051a5078800017a5000700034a41e02c91010354035180e02c49007141c0000d860705400d5080ba038807000104800840554100c043c00e8211030ba174010b034546040081c81030120013004500340959610500ca900b1f4500180382240d0403040202c40e070700f501802e81c0d0b8005441209030507001207808105800d02214446131003030040204154600500c03000400b10b40c41254211008a40d000c41440a810f20340c10003095240044015460055030341c40181090240721071046682c040c40e800030700c030100d540c0103801d50b558015040f40e846a8491411588842070f203080100090b80b00d0f0300041e4000c0c650f0103807101076072300900a10b142010b941c550701102902280b225040c0034003004005601d4864805442c3da642c00d08010f145c88000d400100421344140019010412100103107400c5440d0408072418115508035400061741e507800402070f170 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 207025638 1250 207024388 207024397
    0x20307021009120503121f170a0816050114010b3103031205070f09050d0c05030d020709140c030c18060a030507020613030f051303080c0d080a0b0d0b0705 68
    0x5070703920340310324100f007000f200102410f06880c2c071340c0140709683e6841488a8242d004d40c8030420315401802c204010703c000784003a5400080c0d0700300503515452403d440fa15031070b43c8580141e404032201c1021b803500b800000c1c8a03022500b6170300078034010903500d004a170076224002d8035100c0e904480103d04029941540c030740604000f40a00c0380c070b192440d03074a041c040c050540703082d0140003003820640010038840c850445c100b112000d035168000a076040c4414002c0d003980e260b004071421900082d010809540810040654045940c010102c40d81050f80040640b0021604820110009400d001402610b0340940303a0003041014066102c1d07583c0080680c0e150310000240c2c0e0040000946c148405034140c0199201d0714007030b003c842883c5c59040500c10070a0000001a0020384ca1b1501d8080700c500c03c4d4010403207000d80000600f111904c0c0c1d08d8940040d070200c2d05a001c59800146036800150b08075500d10b0b40b090354040100942c0e1034a40c00310b5004554664020000052940014085405081582c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 207026888 1250 207025638 207025649
    0xf0d06030506010308040302090a02070b130221030a09080c100c0f0f06050105150c0d080702010b0303031008060f09120a03020423040b0d080d05060123180a06020307021009 76
    0x10303100d659517414491450341c401c1c002a03000d018807200140700445580202e500480d0301c11a42001c580e900f25404141d10603c40c0201e90006051448480101514610503c42d01ca00c0000c0c0d541c4604000c00035090144540c4848460b401501801031a9035402d94400744080450130300c2e002d400c0141c5084041d00402401c0140002c03216481102031003181e0303100d14161102900c11148001d444240484180501d01d00d90700346610900000b0381c014071801103113800c0269400046018030300700d400241950021580c00c2c031a141c65003000c02c03a000b000c01050790840039403001501c1906090b00e11030340320800e11350126840750700010000e44940c485d038100ca00400f2250b04640300b204800074101401040c3d000d2b10780c41035040100a246d1490a492490507055204041078581142d06031303420042c260003031950b0b040c44034600000080c040c4103410003c180045507100c60f610f121000013200c1015138081200d020f81e0202100f0700c4101d0f0000100c91050341c0484030220300b1140b15004440d0010a074126 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 207028138 1250 207026888 207026893
    0x6080a1e052505010806061e040803210f06060304140c0402030109020a111b192402060106080c040b0904060503070929030d050c1612021f050f0d060305 67
    0x400d054414006080c00c000808181c0c2034480d40c0c0d0f20b00440b11781c2002c3d40d17456404001089950310b52005075511070401c0254241c000c0c1001e655500d06801d54022410401c01641042c6a404142042c1c0e02d01d03e81c4844007181515071820610003091050100800007090340a101da041e08450004004400510034020000d569a41c0c5580f001c001a422444480012818596442c043c010300411514503080c2ca440c50100341c40c00c1c090801c21030140d40c451018001c0c130720b054017050406c0803100241007000000f01c41c0100402039003000b845c0071416445101005505814040403001c07010454085812800c078140c1c6072941600007800070280d030b50246a140c8111000021348c5030060704680c40d002e4400455074803080c405a000e0030b10011109140e175064004401300c06256000d0710280911403a10003c41e43d1150880841c0703001003506e034001c907a40d0402340c1d12141c21427801050740e409201c01d40409460511402074040c082d4016038031200e110281c08078a50744ca21400c0d074018801560031208 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 207029388 1250 207028138 207028153
    0x11205210c16060201050a0605010e040b011101060e010312080702100902040e070315060803160605090a17040e070f090608060d0c0b1206030d02070506031005100201050703050a06080a1e05 83
    0x210000da10000d4420f8502650070a40041c1300840d841c441e10701214810303100d8000850640c400c0000a00c2c84051890500114441d60542680240308100c0500444200e100c801c2d415801c05045580103813038603004000020003088261680401c550164802894000c158001140f001038042c000c0400140440c0c86084000070a0119200703002c0e21900555001304419501c511000b5224400e40c241c0c0c04204401501c3c803800a80580d05c0703e03500c444000b00746ca42c60b880366600c41c0e29004e83d0700840450b0040101b01442001100020a9044401c5007452100311490010180c03c640062084006005018001070101e460b07042c40600a1640080100c1c185521400d81c00c1580c1c00c00c0010050008848002440e1814001040480e050b61600100002883c2908210041d440100004403410113440300183c1c907101c140c22000260f84a400102d070500d84190018203d40b401045041c0e003a08094040000e004017041442c43c20b5008201d101c000206005810b548444601c002000b9105624 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 207030638 1250 207029388 207029413
    0x160b070e04051003030e100302250c050103061419150207030618020a33080603010b0f060d05150d0320010606080c03090a02101205011205210c 63
    0x414200044904100a84a400015031090103e0000402040c2e00c201d00c6c042524280844400c0201c1d545805840e0141c0c03034a900800d140c024400c4120000885040c3e0100f20304504020041e200c286800c03c0101e10b050410804002c180306858001c000d040d00842d0403041d0368040070040c2440c50001c0e0000401513100a42c4c5440e28441690f4591138040941880b40440142c04202034004029880c2c103810038080c4402c0d500000003241e000c41980350248400803c0d000d101c41500c1e2280ca5189031460b141c001e0609464845d050944981241803144c034480d5900d500341c540c5140d090b20300042d6956004a01c400d000a0310030721030381c0030106400713880405a00201e1500072a80c40d842001c00481c0d42c5032054240d46960242001140c103035000038000c250102d01440c0c0c0300103080200c0744503081d1500450000d80c3c540e9403034800288440134045e01c01c0d0580c010b01d1300401880c128480d01321129110300c0d0f140c088c0c8420b042421401c2000e0007a015600c1d1080c0c03070300600a881641c40407041031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 207031888 1250 207030638 207030647
    0x150a0918060506030a0203030702060c1c1e020f030f07020a05090f06130b01020721020a150311040503060606090d0b0108010219030203070815010918050711071802160b07 75
    0x50001c981e294200000034105040c0490059440f9a01400550403c12107600b00207242d040001c0600041c031030484252030991031006d03910382030040c546540007540b154900031a10386030441e0100f0b095611200d080c000342500042122180d081540b41e058496450b440000d102200c01d510036648222018107100c0141101503804d402448100c0d003815034181030280100c2500e0070500d07160f0141c3c03c09030040040c8040c0c0c071602d2504151000640c1c2c0320b92440c0e030000300c601390a41c020b810460b0302c9038003507584c0079014441c40c0803100418544074200303403400000950740c17103005220078080d01c00413407822200d03107030007050200b1540e0040419040350b8451451074000d4003d03120034008585880745580540b402803089078003403107240d40d80040302e9484401c10350709900c44102d000d04200106800240d80b0306106c83c125045000c605e800315041c1803954009000380302d07403403100142d07422045c000c01000c03400f80c45100d03419070f1184015844030207000820403001304001d00078015241002c10451003070703800b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 207033138 1250 207031888 207031931
    0x405010f050108060f040609080d140405211c0e100e060622110c01060305070e010803040b0301180b0406060f080906011206020304050a0210080726150a09 68
    0x4032003080040340e80c0c4101c102c0d551201030340c0c1c129940940f5004100407070700039045010101d0041400d14074050540f41c28800316103100031203c03081c8030940309100c00c11406101040c18296400300607015410b48407131240d00e500c42e4440c10150b19079104030300f200c0500c864010400550040302950700f02070f0045521806080a0241e920160181c0300000301c070f52a103120f20401d0003400203407503030b0001c2d44040389400a001c40091f11103403080c103011000400b0740074011440610310890140005603d0034541050075503060300000c89640041c0b005012840d02c850550381110900c2040c0070010006000c05002021003d8205410605000004c654203800030300004155007903a89041156444241d942d031118403c0c0181c1e1922075004410070086403160700034640142c0a10140c5081c070304968000341144140200c00c42c0031512410400002d690499058030349041d201e1a40c4c0c5108214165540a4202c0140300e100310101c0c04e2075240c890380718000050060102e51408010f410020501d645c1c40401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 207034388 1250 207033138 207033161
    0x3040b0403031119032003011d010e0f0609040804030204050109022511040f0f0f230103051c02150903030108100b0a03030e12060403030f0f1404030f05040b03040501 73
    0x1010485183c2c601e41c803040300c0540100b981c81211001e030410b0210040c0210712421080d10000d11030036030f4910b00160080d802840800268410403031540307403149014205070701026910003000108949a44107880c42c0d640300000302c030300d083c02c5c3c0c0c0ca9181446041c00f40d904040e401c240b9081c000704803610302d9401001c1e4012400802c001e2100034451301700d000d00c07098a0062210784400c4d0901901e08254000c240040c0c0c00c0030011400703145807600319080b02c2c1030380e0021048603101c22950b20002220300780f00c02c10680c41c80060082e50f040d91650382c4d545040440c5c080c83d1030040391554102500c05c2c001001401d22518040c00c031400c0c00881580d0300d40007801110241d00031040712a1007840079100b0075149500207010504443e01d107407402e903503441400c10815042074a580400703a00140c1400306c0c901c1203101e13480001c1c440103454800c0007141c0b15000c00c80059440c01c000907640e88500d040041d031250703051828485110880d84201c80c1806168451299940040306220411030190082c048001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 207035638 1250 207034388 207034391
    0xa090909060c030509161809170a0f090305060f190f09030e030109030806060309030c10090c0504021c050405030910050405031002090d030e0409080417060a1a091b03040b040303 78
    0xc603045c468503111400c0c1040000100080380040003031048044e03001e480e807491184001001c2c41e017a204d903014840408003150440b14002101d00c2d40d5030f08220a40000303021491304605190640e03413400d603074050180141460100e0440090701030644044c503000e00d15022207052046204011044003e014003500440c0424100e1007401441e0405100705981640c055440403040e49460050048580c0094000c5d60140001c00271410079003400c010102c06504140790024015000303051000140c042a00304600c541e00400c00303480007101c51030005100e68840310300007505850b03038a4124078512504880d507411120b805021141d03240c02002810031524140d05075010014108140000c81c4030368503903150b010312400c108034003007403088034009030000002d040007810b0901921444181c0d001341d071041601c002c8540c100a01503400340a00c5400c181300060030300050720050f010b007448842800305a40a0010a400202446895607204584030405000d0035a82c0c20300b0300700746171038003000c0300c0075000709 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 207036888 1250 207035638 207035641
    0x80f0a030e01050c0a0c0f05152202010509010806041b26010f0b1c060f17060f1308070614040b100f0e191d07080316080a090909060c0305 61
    0x2107506020300303445020722034821403901401240030740c0c043e0001c400a46045840400e1000024009c0000481251400580400a1820820b405408004500480402e1051500b9600180d801100b510812042401c20380340c2591440007040c000d1001b120181d0700128004144950b9075000350f0000404824030310030308010440070400c9140703d0000e100b0011800c9400074104a04405140584604100c20000a40d03506103016030310b054481c01d41040c400800542010000d842d400c504910003030302040050821031034060442c0140c81401401c7e100c100803154542d504226109040320805517105030100042c0740074050b402c0303140c401280c040301d130700c200d00d00410084e100c2846208102c17084096014166810005c945904aa02402080b8103010f2400000b0500301c150103000349200c04a40000202d94800030300c0c9180040300e5200c251142c1081040a107148400108141c416070441800e82d900d4910007000c64904696901a049480c94028490100501500b003048000a0741e0b800b40200d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 207038138 1250 207036888 207036911
    0xc180603070906122a06020c100816080c0d0504150e0604080906090d050f0a150209030a0809150a03091104050108030304110406180509010e07030203071809080f0a03 73
    0x316400f6006480500079542030003000110360011240f440c983c04401d2803282c148050040018801c190444405038201c103485a5090900c80c50400c03401c2e20f280f5151720b41d41440c814803c0e071002000100e0702000005400900701e04244000c603018020f0a45040080385018200a085491400500c00a150800750444da40c1d030b03000241c0c58003440d0001c0e1000c2c0380414481c00c102c078541c0003012254005810520180206400340005c40860070709001500b10384002d89042c8011511401000141c0d038814024800c1c15280001c070080703443d40c00241195a10070a6000030000c801c030910720003480c103001440c0029030764103030404000302c0d109024426516030722a0400c020b440090140001d0b0358002d1000501046c4403200b142850032020700700143c250303140e6212690040c0d0003482e003001140c88000703103c5401003d00c2a038a6580c10340b4090080d103411980013949030101c030301c43e00e080703601e19002829650103d0780c408950148d10184060380c4003c00d42e070200da1130300038443d18400700380f074110321090 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 207039388 1250 207038138 207038141
    0x8011a040e0a05130c0e04020108061e060c100606020d0e0607030507020f0a030602040b0c0c090114060d0b090a0b09070c030504091d1005010e01080a050604080307020c1806030709 79
    0x54a8495007604200d0380c0d41d000d14801408010001510303840542a4000400d0128950b00d01034440300c86030388040e00d800d0001400c0b50402510325401048408581800010701ca801c1e00d9843c0400c55a090b600d01c2003510071807034801c040140412491400b0030005c1d41d030780c0004d200408900291104040031903214108045030149081c09401300790100701510052034280346c00d6105030340042c8000c80146d202e845840490700603410020000c4000a290140300c041081101245641160042082c1d814142651420303a03607001101e009010114980ba142c4581d40c0101803089400b403c00c050381d150042c0c00c1c0c4003405100c0c4c0101d00810000001c514003911070140b0300c80c226090740f5040c1c0f80c01e1420400398014044504144004201a000405c0042041c40940d10030745c072a0703401181c40d5040103012469410182e212030b81c2e61b40b0000380140012004540c02e40d0160f04100300a45035595100d040c0e00341089940125030105891440f0240d020302600114050901541120040d5468200860 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 207040638 1250 207039388 207039397
    0x100309020a0611030301140d0b0403020309010e0405100b07050a12020c0a080105060a06110a0606090e0118051b010e03030703030c27141504030b0f060409020d0314091008011a 77
    0x40071030708108010311205087c005018000b41c0064118a295000d5480b007411043c070a4408400603000010000104c4d0fa01103c11041c4940c1140c0402160402c0340120350851050b00c5540c0f6400c0d400b00b5401c040c0482130011010054005015240e41c1001c444001e4031a00c556400600c10001c41d04040b41c0b507201440b446104840181c442e103501c42c1001820b850b441e8a041c150302a6220741d01540000980c18024030009200503107000c1303402c030400701c84c90f400c4d910140c803455200310b6403c00180100d040000e2000583c1c05122140b2522170b41c3d040100d5038036090000d040c2d014407000495804050345039201303179001d411695079004901c5600d5007695012084240800b80b52070000300511051254009204c0c029500600e8011841045c0c00442e0258001c0c0d401900c0400d41c007810414804010b18805500c070030200d03801c00554803240e000074107245012402500b000106403c80d4944c69483c0229152030000800040a844200e6001400190300b4003e22002c5032106944000100381c030402d94 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 207041888 1250 207040638 207040667
    0x10501020d1b030c15110309010c02150c07021809100b010801060e01051305091303030b0109050d06050603010f0e070915060221040b13030302210d0e0c100309020a06 73
    0x44140b50468a08503440c142d0344105407075a0043d680000d0885400d8410162010b11051941d038803898445800780c2104c07021111031095402404d2100c07100c4880d82c2c5003990181c0444000c030740310718180c0007256441d01040c0305020007000c4142440f00100e03001a2504c4841594034043c099900400700444100340d00b13220300c0c0d0214619a40c1d5803105d42c050f0002d06001480007184150700380c3e54200044000c10180c401d070a840950000e48000d0503454020030003070403020300300424024902004a20202e003036150141c0010741d101e01080a60b6402e410450b90b040b0200c10910004c11030600482d182e140a00c00d000c1d2140c6004d0541070f9103400d01003500d048070029009800444100b6085039207290b00106480080003080002141501c0540d000d85140801201441200e60451801a10701000010a100701000194007000c0041e44d01c0c1c112413140b080020b01044a98815258a01d0001c012494903480507000041c45c0d061760f4035502100305207000301d619041e15551100c0a84850300d196440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 207043138 1250 207041888 207041927
    0x6030a0c05010f050705011805060901061203140c0d0305061e03030d051e070201020d0f090c051005070c0801090b06011d0108040c030807030809010c1b020d060e03040806010501020d 80
    0x40103558000d01e0002200d480f1030811525080f40e6035940c6003150a5040d400d062903010181d05c04c280f040800c1800e5100388000300800216081c08034601c250130000300b00404210105140c0825014007105030ba50004000b41101d01c0c0d142003038806000b500e01210b009024200003125000059401d8203142c400c028007034003a610b44482504918040e20300103003d541402501c418525891300850305161107414960b000588920b207003642e020603980c240c003044801e0380c20000c4d44804202110010f0044680486140c2c169036042d5800761024040c071000500030017030707010b40020600e0064000c03c820134403480340c050b4142c1d103020064401002c2c8a0246080d801c059103440e0465004854060308030f0701440c504071849075240d542c0d006075401100100d00142000091282040003401905444103140c18628180050000b0420b00514030010213841454040c80c040d05101299004036480882c030820f80b55116250074045958038020711840c0d00520030307415610300062140204040b800845c804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 207044388 1250 207043138 207043163
    0xf020111091e060405030a03110705040b180403110307080c01110a091421010b0f10050a050f130b070506010e19020901030e0d0c0506181c020322030b06030a 69
    0x30108082c1c03800c0015640000c4200400726141d80e04116103415140300b680c0b110030786100807048034105041030f8802c0c0d00450915141050b5941e903a034042e81100c031f00d850071034881d42c3c85041c1101c0042c1150325113a06400300280c00030622400e1001014444100c42c000e100018601011480c0f0780304401c0f8200018a0301e810600910154041120510360028a07814940041040c0403c000c08d0304002210280e5441040b52002d00342519007040011080b901015800702a100c00f600a1144a8552003004800581820741c030340440250380b110440100c821039805d0701d90064401c4c030b501c0f06605581c9445480300000300444d4449a0604c207051402c15a031075144904250720103500b10040d01814103854542c40320860341c081016200003040f0f275407800d010400310f060580c00d049000e0f01d1421030306015000c01645010004000c109410501c100c1c0fa0310b203010003400c9096002c0c1070748a450006061015206007240e91082600b982c0c060403071500580c44020030943c0c1d8151100000345001035010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 207045638 1250 207044388 207044419
    0x160605030106050a17070909051005030d050c07030b0f1803030402150d0b04050408040f0b0f190c0501020a1d012c040f09050a0303150602060103080904020c06070f02011109 76
    0xf00502241c90860501c6110a00843d481e6a07044004480540004000c03440c1080001c4007400f4613908041424100e1400c01d0500011a4031600d0700800c88003400400510b40100c0310302003108600843d008521480b2a0802c00c5c511704000e1004d4a6900c108003070041a450100c40c0442140d02403a8000c0444807180c0702303070f030b164100d07504401d4042c185c20740e50389035085043c0c5a5004551003644680300c00b540c0c40341020845010b0004541050100040a1003006c0940c560302c4201d03441c480c504004140040c851030b608544e51024440000c2480d4004105801143d0b003150000110105181d000110343c0c030705034011902081350070300108080c0300c1c2c5c3d00f02071080483d064540c40840005440030904640b070740001d9041c5e990044080354181c0c00002c8940a043c0d15128102c0503030821644102c0c81440d0400007990707643c1c180409080b8080000302d80e0311a40d6150304580f61203000e101540e41c09d141c030b440058640b040010107031025500304560a450502040120f60800c80020310445640400301e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 207046888 1250 207045638 207045647
    0x10e0a1404090314031e1006080f0a0b1002011506141806220920030a11070f1101080a0e031b030d020f070c0e070804082217160605030106 61
    0x40820b905010310000e4a890700c144413002144900092006c94a00c800001c0104903034002c024800704044106c0a402e209003a030050700a90482160703d04980e00780c5401d400000201141150b9684c413104c20301d25450302c1034064010038a5040e030450510f000f51350300c120548441012803100300c0c0c07101041000351075200f0f07591500e401030384001d0002418071685000c5041440c0303120800035904000340320300f0080b28256029040c10400688004200842d80480b2030400c1d00018180c8440d4644851215040c03801220984024035040308108036036103102e0511140b440341c441505800a042d40c00041e00080260103803800c9807505c54002c520302000c6000c0840f1402221101950703030f020420403428400c1c5c0700d00140800c0500c500446944050b60300d0300c0784c0c4e101f8845d030103002d02d18600c400700310340c0765042410181d2054000700841c0d0b6850403041702c0d02078010450070b2180c1405a68501048814020160702418180c0c0c100b2106580000707800500c40b04624420040002d90803c0144402c0340b14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 207048138 1250 207046888 207046901
    0x51011070b0a090e181c0c1e151116030203190302040f1a0d1a030d0908010e060f0103020d020102030d140403091e090e03120c030402010e0a1404 64
    0x650903655a99100c101180455002005081c006049100c05100c42044202103a401c440c03103180941c80c0c250b048841c6612901d442a191403071417005207103109024003403401026034640c0a41c00302680d07141e00b401d030342c2c190ba00854140c0c0e035010300010084500d0220b10a210703e80a4011449040400b4080040351076112500f003141140801d01a8018807440030b9401540d84040e900c0140e29142404400c020281c0e03144d0240079411404203030411902c0103603007100c1905091510104a40f007200d0200c1503500b0801c50300d590981315540c819180356900200c0f031019228040e00034050040116a144d035621000e5810b0308408a009004000504c0c0928042c82e00e684180142ea003411030b8078001500312550307140ca00340500c1c50304040004041e448080e0320701500c401502c0c0d603411101043c0c1c01010100b0340c059400710030780c1d404a0780103407501003068841500d458484606a0300d40620480e00740e070001d650481c08164006520300161800c00d00e8141503e003c0048a80551040e40410014100d03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 207049388 1250 207048138 207048167
    0x3050601121a040f05010e0c070312151203170114060301121e061b08010b0d1d030f04030204110903150703090f03180b09031f240e0108070510 63
    0x2032076049502e454690380120810400c104200085961510014880e01c0f040140b070040d9042e020000d01c00000c0d00444152201d800499001030300c00103240d502c00c04142240c101c0761122080e000d09200b0558418005400c03034440700031403c1144d9803102c01a180446a0303103010392115041c40180051203040c105c1c2c0e00028011051860100080400aa1003042c428800e640142d01d400606140324042d80c80c0c18501104c6262810b031640c50040c1d05406806440c15805040361113180465806a1071203010403034a00003801d036990340b58000c0458003664400c2c88204d0090f03080c0304507125860b07100c1054601240000e40a803a0500e44180284a002c1004080d08185541d945800000c100c1a01000400501c00d444440300642c4c4001000b546004a5008510051040100e1145920041358441003001d1403c400c0d51007050300c0c0c803e800070f00f0031000c1036000305030008040e410b82010400c18000f01c1f02510510151640c0b1500001e44400783e5009141e042491110794100301d034440c82d001020950b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 207050638 1250 207049388 207049421
    0x402130506070f05010b06090f0f030c130c03050603010b0a06051612080105041d0705060a051902060412030603110915120d020106051e0603090f0a03031505010305060112 75
    0x98440000a441c1d40000a0940300444243c80b5882040b10910404d0300c440811511141000e0382078000405070340003c0030071401203d290171691ba003070f01c0810005440c180b00070101040b0307108103042d120082003070108500000341004049003040c141071254800a4002800007070140b070906d2410f84043c2d0280c21107a81c0152040004000f01d00d1282084d000342c0c01d50f46d50001954905410007041d104007962103402c50700c44200b61200150f001440c5022102e040c2c4146483d4001c840742900c5c140504031200c0b00c0740f401803143c02511036011482170b01c228841c000c200d441d0200e031541203003210480d0000406a40d8007070801c007800d00d0010350403135002030b18050390f841c07440a020100e018841d4001144240c0d41c002078000008d541c0a0107084040c18080d503092a01c0849800d2071100703407102c001194003580380000230502528080c0205000d010f0280c048a50306d03c80b44c41c00900500e04082aa16010a086000308142d0f10902402d80620b0701603407419000110032040000130030400d020000207a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 207051888 1250 207050638 207050677
    0x3020a02070b0f03010f140a03030f0e0901080604030206070206040507090b0a0803160c14030a0803060f0d14100227031c0315050405060d110d0f06021c0501060903020402 75
    0x31403440100380300703441c010f125a129454425202101c1500c0d400403444035201c0000b005e42c0381c582c4101c12085036018a05468804105c80b0265400d800401d89590031940c110000700e4840700004885004a10950849480d59580c01040340c44c0c0710241c400401603080074004000e04101c40d041110341100040000324095075816140c1d1031580702e602c00108114200c40b0710424480c4408540e0024800b0384c0c0380742d20100003200040d440382840701c4000d01040010000c10580d8540a07010903110380042c4c040200c041090400015552007801212001d11850310202da0b11516030082c4c4242420301c0b00c07201c5941c05411104050b4403101030300560984100c0024840743c0c4001200c070f030304002681d2000101da06016000041482c1d560700042d0080c2c2c101000c0c0440740d03e605031036858040d08140c0e011890201100019401152400058140140354900e00b062100b6680100740707034003031a00540014022444101c050f54000d20500b000316164031300030809414140c00a05402000b800c82c0b4100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 207053138 1250 207051888 207051899
    0x603070906062c030304060507080409050103050f1b010c0221060c1312030f18090207080901020d02070305120d021315090e0613020c0c030d080a060b04031203020a0207 74
    0x1c5415a0303000c10300162818403070203400520004100440c4102151030b41c1c0380040c11010075500d02c564481c10302003100000d15041403050640507140940781c03e680078480307941c1d00d0070003554600c554001c414440c080c1001c502e98450800e00e0034002a034068541c1c00098101ba001c00035054003d0881e92041d0000b40f0800303c984a0501605100b404441052901c0d07181c40903030702420a041d500304062000040c80c0900100307822404001498040d4a86400c0c441d004094030180b240369640108100f03400800c503801000040c001400c40c1d811b0aa0031100e42c908001002c0366070b610144800b600d140c010860700704466240074002c00109001150242c03400282d088038001781034107a0301052600040b80d07003001541d5840f0742c1c841e009041a03030120403541820400078600e40340c100e2000360b070780e540054942003c0c00c0c1404007460301c000c010300f07441d01c500701001c0c041c06890003100c0c801150381c50140007066014400c03040c4d80960750003140001608a1055058000350b00c240342203401e5100b0fa2000050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 207054388 1250 207053138 207053141
    0x30902040504120e0406080c040c050c071508090303041109131e0302070f0b0d0c0306051c0b0105010c0302120903070e0a0e120f12062704050c010216090506030709 72
    0x9500c20b014035003a01c2503800f001010080b00f003400134030440c24400c0c100840780c0c0009444004650407100020f02c40f00c248819103203403044100e00301440c01680f02c009405070809410b40110041d42d118070049035529109146c0781e100481d4000e000b00c0d540903088a99040c03c40074198000710040b403500c000607254644070403040e17004c0030340210b8041416042c01015818490000100b6940350040c001c0750402081c61000d016040600030f1240d038504088414034440e400080003004041c0202c04d01ca04414041000801064400c2d03c03841481c200021f0f10303510a16107070b01c40b19010350180c810854402c180090650040c144150306126603140400c02e40d0440301414010840c070400001e4501d0b82c40d04803400c00c9110700341c0d50122442400464141c18041341103a0610703900154241096403850b00140c28241604003100e094008445a00641c0c2002940c10340218000c1040741c0000b0306000c01241e41e200100000380c041c00495030208480c03041500500e0700004000c0542711084d40768401c100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 207055638 1250 207054388 207054391
    0x303021e040302120c090403050d060f09240f03020f060c1c020115060906080a0e010f0b0a0806010f030f110904200f0102030a05090303040803070f0210030e060403080402010309020405 81
    0x25161030005080045141801c0100d41c140421806812a0030405000034012000180085d080c002e00050316031050352030354440b8000c0e00000403120889a03d910207280100411100101c0c0c500300c0b134001d01740c42410020304000310b40d59918841c0c28a07055500740f280c47c0c0000141030b40c0210042c080e8a401d04401e220b84800084481c00c040b1800364104e500a0943d4500040a01c00104040051091a40c003080c80340c1a21010305000d2801c0c2c0702c4000100061100e42044080755180c100241c80640141c0c10004261008640740c58146071a01d42d40b54440b0b0702845505000501c80b101000010412008440420700030a240700e8a0008180800c5080900710b03401c80d066210740c82103598070014222100080c0100740c0d000b601000711100043d40d80e20440f5010020301001144603500c0740c3e410421540a0314048080d01e0301c450b10352501600c00c800c502c078124032810034098540101d9100340b24405566138403000400c0c460b121910191032031100503005030304058450b4415405a1554014107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 207056888 1250 207055638 207055687
    0xa0b04090203042901090c17040308270606041e020715050a02030f0604180203030f120115090608041104050f0609060301020a0c06050717010f050118051c030302 71
    0x5a07032443c00707161000d48002c01300c0c0c1c041e0749610740107109901c243d110901075054031455500060a260b034034000340e502c8420303400f0400180824070100410568000b19407030040350484c1c800c0d00e650003080174a03200c8a400400b10002c0781e00450000700e480c9020303041441900104011400e001b5000c0341c090060368004042500c1038040c000f40c01c040c1d03448501c40c8a0740601e8036407086040d030428141509454174082c0002d8412034451000200d01e10103da620081c1581c0101100e980d02e42100011020750000b0300c01191400d030b00e0340001a1100c400d4500000b007405a6950b4400c1400c119064400da02c0180058074100322181200b43c1d0f60b100d5128080c05144e0480c21a90b030b6103442010480c01200003003205020f03034010b010401c2007541010700c0e000e0b6640d1002010801d644c40b805e0446d400c1c0300640303041d01400503403030002444103d04030556040c0c1d13000303a8540f00724249000e0134010744445482004d40003000b13030b0b002c4040007035851205400903207e8078003d0300c5d019815980600200307c4480a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 207058138 1250 207056888 207056891
    0x9191b08010f1d060f060f120a050f0405030715020910030e06070207060c14030915030906010e040f0318050618030c04060e0103032109390506090a0b0409 68
    0x180b00108000510714018989800181c2c4880c2000c05501e64100c80981668007070040d07040740514990b685802d071001c09410000660302c030844140d0003258410181c4a414480d4540008580401404008c0c4c61255030400c005525280c4265030711a0040b0000420022580d07084c4803100d801c1e50f4003a1400b081124507074010803c0c0030030145140c06d100e8064140d5086d0b5101c603000300041500320056501164101c01d600c42c0700209841014210301c101c20005505ca00e902840811200d070b1040994002c0034080c048030380c80d83c0c8510002030f100f807065401410503110f050441c0002885101818002c8104410019801e03503558040781c51908603541205440c80c50009225076410100f008069850301103030140031407450180c0d15915420107000144c00c01062085c60903100c500070030322404601d6601e40030461b051003800d20300310400c0c003210020714203c1c000701400515170080c1160450101d54101c0d641d1480e141004004c1d44c1d0381721045542d000300b02c0804c00503035481d0b5100500001d0071241d40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 207059388 1250 207058138 207058141
    0x140706111005010e070c030903020603040c08160b0f090d0c0306290d0f17040b1201050301050f06040b0d05030d0e160305031c140a060e090c09191b08 66
    0x800c5428103484005a141c40e81c508001000000301c1615025002075883c00c0c11a8295100d060071911040684c01c084c1d0082000402e1100b0007601c804403408441c98030041c0d9003030762480703440750503c0707a1903106120081d4400c1c4928031001010000910805500410300d00c07120031266a2000d0501095005942c141d075100d544034840800c1400c02ea8000c3c0440425201c8109242c000820030b039010031001d000014004480c008021948001c100c48000404040d51550390b9041015a2944000707114070703180c21010000181410705014160051448501000e0700369255028000209900c0213002d5008100d9070360500411824001400c58042240002c00c40c0b80307000058514010030120303080f54500609100f000851804070a5800c094602081d0f1001900501054800b0301903503100d240400344010184450950f20b607001c201240da018a0b2423034640d031070303549940c0c4420090301025017040c5400c000428407030b040004044c91084410f00051a2000c03d440c18600309098404440450b81c50b40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 207060638 1250 207059388 207059417
    0x30e0a1d0a0f06060206010e04081329210a1107030e180f0103030305070e0a0b030406050a020c0307110316270501140d051f0902010905060a0c0f140706 67
    0x303580c400d1400c2407030600c2444d24140c40203595180510070340c0c11080e0548046001c00121004890a9900d1408910003042d100d440c05032103a000f8148419558041180c0690380e10900700c20746613003c00140b14040c0104407500590410300d001003446100c9640e84500500d485162000340051501079502c645281c034202d01440192071003110b0715041000500c080010841c0d603c030003641540c0d80361402003290f0f100d82000340c501e181c4610301d5941c000e091130008900c03502c0e0381c0040c42c4a00e008003001d02142d10703111107600403442540c01c2c01c40d03950410012400030510000c0b441c1c1c84800060200c410079580d8142c1c0150052054105401e00084051800050304401a8044000310402c80800c4154545020014486030286401d4003a03032540001505100051020307442d03010300311300c040b100220220071000080080c05c9080740440e1110001050714102101600e0b003610481e2540001e0039125214902d410f0110b49003121504206e0700d55901024050180307400400303160300d4800201284a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 207061888 1250 207060638 207060641
    0x3010f0306050a050112080d0b0627010f1d0d0204060e09150601050702210105090c12070302090f0417040303090e250503060406090e06060a080f0307030e0a1d0a 71
    0x20300f000b004141400d00610038100142e584005d1554001c2c0c480740d9801078000300c00003621400b41f15552181000c11a103c83d05040c04a035100e00095802c036100d031610300c00044d0388200030b00e08404001407286044016120b5040103401010500070040c4074031103c540d0020301540e40c1900212080001030050015007401000b031040000314039101d64859103070500000708030740518030019100d03000c11846204005003184c1e400106800c200000d000918000d40da680d501d058880b4490300980740072046051000300840d084090703030780c02040c100840c0c45540c001441c100707010300f09481c808410019291a80a410001c0c00198401e0310703980341300d910301010580362410041030a6070403601c0d05804805840d07441042032000006080540e01c0340c0b90400440c008002542080f0481860081b441f1418800016480d20802080700c00741c0d8601d8840c5050349c1c80702040800d4a210794418000725000a004421070a150350007e040b101c3c640c0d41d904000101441c80c2280c0c214170011000a0080c250002d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 207063138 1250 207061888 207061891
    0x1905060c04300506090a0519081210080a0f020f0f1008041506090603020a080d020714040f020406050d0e030405060d0e01060e07120e12040b070c080303010f030605 72
    0x400c908091904000e400700440080c920140328142080a00079103a201506407102a0400212074851600e080c55039500c1450340f8040c1c3d141e100340c0014041060320920000c04055200d07812034140070b8030400b48680d030903000c0d110101c1c010050ba000300b0749200030030400382c1507409010742c0001343c0350b940140704400d010011424062251500c521515403514242c0c000314240e682b401c2901542c42e42232180d0001042461248410300b4410700168801d1b03141c00c4901038900889640c45800e40d2031b10306580d2420384401500250708040401c000151500222071031161001d0710100d448081c09540c0310817a4003e03086603002c0340c40440c0343c201504e27481c4107903a445949140103528007400d2030002081c0740241100105c04503140c0b00000503584080d00402c00070240720720104114241903c0140009030b80f803509000786840c16103840498200082c221503c10b20b180e003518a4542080c00b01480c640c008503064840c0c560300c0100040c00c64003007000754000d1000d041c43c02801c44c03c1d4540907066600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 207064388 1250 207063138 207063151
    0x1f120605010c111207090e1e03030f07140405040504080423010203030c090a08010204060201060806090a0c15050c070b040815090309010302071704090209041d0a0311010e190506 78
    0x26209048001884100860124400407110340c04900340144c01e0900d04111500041c1c5180d040000d0800500c500080b083c465040c0b03545940b80c5144a043c0f560b503280400c840030343c0b00c403001d1400701e80440d0190001014091062001514154940e0702140a032001540c040310592000201040601d00300e4810355840c110349a42c01101c00001e0380000d40d28000503081d06a00a400600381d04656030b04c0c100c80000b000e51000942d100c0c0d5035160080e008068074842c00701c89000d4040011841c01002c500041e2032079006260071409802c2c00d200d11762a00c1e40381c0c1c020080c02030802c641c40300b0329410000800249030713401c0100c9c0d4981c2010200c2d400d0016280101d50790350022000e03c0001c07400881500c940850a2800688403961414480c1c20034440450806100200080100d008041500208000d690035101072042c2c416050309041030318601c0c40010b005820031020b100009100c0c03405560302d1034001c40045820310f507004415003086051094503688540c0720140c00c08005d03080c009540d0142 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 207065638 1250 207064388 207064397
    0x421080105180912090102011e0204050a170307030503130803180c01110c240708030103030e120a03030e160608060a060e01090b09031203040303140a02040b181f12060501 75
    0x5040f6a880c0c0c0c1caa0602e07169032140b94000c0769a40b90307640300f54410780040251100000307482c00a500300714000d5100d401064081d0903070050110789807001c0d01c50160038601c828010f5240040503201290030780c0014050881d002c0440307000e03c01141600740a1402903a55031042c0341e44641c500d890301e141c8044000546e06020a032072010780d0b1080302003449200440190342445a6809004904403c000d075440c030341e20840d4004c10104140040640594142c0e44652640401d0180e0003080003119490003d001d50941c0c000280d10000902c01e802c101119080e03841103031540c000c0c8480c4550110600c0d0020740004d4103810400007140340c42010b0070300804640c100800c10030462070009000f0540307400b85138a00c0c1c100041030a01d030788040092040c2d590019081c5516802d20b0315005010f04044a0300c15020650940030a1011100d482206c0c1107031450140c0364a001d545241c1c9400d80c880e80c04005a0246281120800b0b54000d00500321081c16540c0c1c40e046c1e50403507212a80c0c1100e085400560412 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 207066888 1250 207065638 207065641
    0x1060e0606090d0c080601060809070b09060301031e020405010602030d0b06030114010c0503070b0c030a1b020d1103070203030c010c0f020c03030a110f07091d0105041a042108010518 80
    0xa4032828100d07091200c060f60142c0a014041c03c00d0329402626071312242031445043c00005810794020314180c060340840043e50b00d4240e6071704240900d40900484164402010001000001c2900c40c0d850904011990400600202500000e0032600240d100c0d002580000503d140c0c00030446c4500c0390f040104650040c1154145500d801d811081508420b05001c070b2074668100b1301c60300708240c6803d2944412120450315140044040305c4c3c100b92001108681082c031100545081d40c0b151040a080c0b56000f04121850b08004884005906803229a9400100495005a02c0c01e10091084910301400440d0540d240c2c0c0d80189040d4131184074201715042810803003550f07940407080b62074190340751804d90980c0d02da1210072814044404410312403449004800510030946410004001d81c2d21001080c04c81000945d950030307642c040340c00170184001b004020030b8074158181c8113500f090003030500c100b20306002d6002071482d030114a83c14021459100042005180c06281c07415017810030074104040c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 207068138 1250 207066888 207066901
    0x2091302040f0b030603100213061716210e030702210a030507020a170a0203060703020a02071802120a020304152c16240302090604170a0209040b070201060e 69
    0x1e220601458043c40800000b107065682d04100340c10440301118001c66941d280d250408042c04454440d040100341200c0210009032180c0c0301765880707440b5000c200d680b03c0c1c00241088401c0403c4070010001c12100780d242003038504551241f116070581240056075a03031103900420108400c12103507285403064099014502001c0458688581681030904a456407401d200180c0e40090640010680b400210540c44203002c000410b80400ca00a42c140d84883c0c45480c401c5050348034030714099001d0b0303010f0070003081002c940004888a104440074014145020080407510383c0c101a00e060088175004804d00007404810002c052011254200400140d050f542c02035200406414506206414400c001c0b00c8005050108905145000e19180d000310748507410b000710641c4004000340c00910a480c50f460284c081d108071070f42e10b0802800d03582418901411070000c400501c00681172400f0b00d03600c120041e166020000d00030361103040e480103285001d0800900711041944403c4081141800f44900d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 207069388 1250 207068138 207068159
    0x30106060507170f030403020c01080c090a0e04020d080c030a020f060f01170f0f0f0f0d0509130b04020d09020906010305101e0b0c061803070b150f0a0602010209130204 74
    0x240d0b55200d040c094548120000303052403800b404c288500401000803c100c02c041d80400d240d418500262608880c640760704101400900598900b04d400240641e01445161010150682d0081c4020030b5406141d03d03990f00d440c0c0d603412505d15010b844e400803544069441d014040b202503220007030300503c810b01d40044032000c0c2850610a4001604002c0a109401001445000c508210000444a40c0014030556650b01c0d254002c03000d00900500800036a20040402c400e2030000c00759440c030741414148410000c8d0035110300f07a440c81e4542d070b40029400a1702c0728000780c43c4030303203d01100140000080c01441700303034034004107591b04042c81c050402110f004000c0c10749059900c03c90020100e902d042c40991840355032904185528800440c41c02c03004a000140b043c42200c0c520704259510541260302c1c2e40d6400758a20080a0b104518001150842f0401d807860803a1001042e1051403c1c01d0404640c070001c0310303008000183d40004d80c0d034643e800c0200c060303034031050484000c40c5071601c0c203216050f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 207070638 1250 207069388 207069397
    0x417060f0c03060402090310050412031d07060e01020f0601240f12020f040e1306060b07080d051302060c16062d09180203010504060603090305031f08030406120b0301060605 76
    0x904c0307550701182d601d1064030100156418205202400c00071400c041c1800c0380d000302800d4071480080d0401a07040013080410401801c01e449820040200d0341c10040d040e103404032a05e00c603604501c52100c541c0c503092810071a0324006c1c41d40c00e9062640812103030415100280c00ac0000307060081c0310314031402c1554007410200361108a410b00603103038441c0c00c3d420403c07881140c0c480303400e9400f050188241203402190041e002c602c0342d030040001d1580c07804495554001c8140182c000e840601031090400000e4000f1a40001c900d00f004000d02d48a500003a01600320300140311069000350445c0300210554081c1001500032410948055414a100140c00000c1481040c2d020540c180103502454050b81040000e807500983e0031181d4544081284001e4000b44a1584150308000000130f10324028890400d60b20b816654251441e0703150410004402c6220014458540d9150000162031000b800580044c00050b0380311390000705219901020f407990450800d02c00e0345400010090710350480c01b1107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 207071888 1250 207070638 207070651
    0x40c081203060916142703060106080103080705100e030a17090c061c110703120b0f040e0a06050a0c0305060307081e010204080d05120a06050f0d1104020417060f0c03 73
    0x144c07102d10750b820003240c0d0b882003030b03000e4070702054085982807000100c0318010070300b21600fa01c5200c0c1c1210720010540d80b074100b845420049003d850060010412010003800d2032400740c800c442c05082030103074040031203241c1d401a840039000411480362059004480100b00c550302c50110b2103505241c0025500c0c1c60250308100d120318070000d2074224903000e14451103541d1960403010000070113548101c0700f042d4040081200051040300304281c4000103849003802c688009094200038038003100600000300f1000440040c1485180d40c1c0380001440c0f030055038840c2c00c0400b00422200308410010303043d180b0180c0079074441c0d01710280500c0080c00010b84070b06415124441e0901c4448030020a5009204941080f401405450480514141c10400030b0070005806242003803a03507281c4d40700c44c0454000703005540d4003a142441e21082460608080c44032070380134800b100040c400b040c002070200d034802d42c0100040c40102402c141000c4043c00460b50115942d40700b00c1e61807420849004d058032005183c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 207073138 1250 207071888 207071911
    0xb1c080405041802040e030301030311070b070609030201090605041407060801080d05131a130b03190c02031b0c01090602120412030e040c080a0b0a14061809040c0812030609 76
    0x81c030060f503041410603c011500030303000f0040070003010000703512507000740002e6011442c0c195850b60b1a0800003854801c9502c101042c50034504543c0d00da4015080c0854260112340d03c404140c404203c1511032240a140f18001402e81541c0c40d8016500b8079803540d2005090200a500401101d400820b107030076100e1003403809590b0349512034a550005e0909800805600740e4003401c507104001040002c00c0c1c0c01981c940c05589003540d0b215030045a100450f81c16030304800b40001080c540648e904a0900c140e0300d40180d034102225008a141084d860350321400184c2d000704200b8000b560042c003801c02501080c03000e0103c0b00021500341925110310301c00c241c244403c0d080a081814811030019240d46001041440310442c1c0d844000d02034401a100041d1840c600940300060b803030b00800410840e50070509280750400c4113010001190440290700c507912003241b030030325100e43d6190342c03440c07040d807080d54050300f01400c0c440042e160447d400f44e003120f00e06042090180710380c0c4d0300d40c4065014111006 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 207074388 1250 207073138 207073151
    0x13080c1c0b0c07050a1109010e01031505040303061502031210031e030c0b0a090309060905011211130803040311090103110607031431290405130b1c08040504 69
    0x4000c8a02d200e200b03000742c1300303005070f8928004110020032515001d8400310703910745199888a8189200f00c20030b2000422100e00501d11301c105112035004103a200303001c0d00b00014070540c0c0350698034001c400c81c1091001a00001804605030941d10380494001c2071424000c00c0d1300b81582d9906000d15085441030000809008a031001c051241032205095940030022921504219a001028004500080300882c031280004510b080c030960003942141d030305a40f00220404020003420041c004515402840380c41080b500c14a03801841c0014010225200299555440c50030b05064064540515a00c0741400300010008100500014108010101d40265417072115140c01d89121001c07a06e9815002400f00300340ba07255138080300008400c0710000544a0604645440b814850400e00690116507003081c180b82400d0310083c480d0307240003203040f0000d01e082d4898002500c0000c802d0912180992a011415480c0c102403000f030a4003546da00c00c00d24004480d40c0d40703616501075805031901980d91000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 207075638 1250 207074388 207074401
    0x80c0d06110f030402100f2109081b070806010b1207180810060602011401060c0203070909050c120d0e061c090501020406080c160209130813080c1c0b 66
    0x107000400c194010a46240e6810b00c0784548802600f08507001e91181c42d0360546034074000e01a200d814105103681d907580b0710310030425100b0044036040301c3c04038804940c0c6025000000e1001e200070940040c00d150800629030220529900e050b5842c2c2001100360000d8004100b0784040c00241c80b12a040d003082c040d020340d10381c081103505660b80d00003882d4507800d40c140041c5108004c10361902980b840c50080c807400e5224807069007079030b01d0420320341c1d6005900d40040058500c00e08440e044144018261003455641d401001d065400210042d038180e088a00c60804c50b00e0084070401403074186102503c40c40e03071424401b0b00070208080700a80900300005131803020000759407400a0003000c2660801c881c01e01820503c2c001d4001c3e0086d040811142008100610002e2041d200300315981002024645460350a00c00400c0c80034020300032500741c80d070301c030700004500c0d0000e00804029005242c000301e280026561030040c3c803c0b4407d01400c8000b402d25485491555040c66503078000b1a003c0707942e1601c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 207076888 1250 207075638 207075641
    0x304020607080c16030201030b0103060e06060a020f030a02030c06011a0714011b08010e0105010908190312021b060117070e040804050a0e1918030f090306050717090106080c0d06 78
    0x20b1445041c0d13014a00320780344600c02e4802c4100c1564001e80e410030080c500d1340015800c4a55a0141968002050001640d645400d0004000101c000c0c419100840360322840e01d4a103800442c0c032100540c102040340c0042d0881003144d01d00425041032080d10300b500d09810081503110344040076010802c0e07000355040c60442500f0480c1010f0004401049094001790010728003d000c7c010081841c1061000068644c400d15804040e510072102a0510030070a00108030310500d00c070340403024801c0c080442042c103c141d00c060420000c000c0000d0040c000800105418032030140c0100704184140709114400840008488099414401c2c000102d0f0300e031411700d90f003a2b0155034400d90703000525032404a84040644c40c1a8090406144084c070002d8485801c43d0a0701c401112041041044140c1c500100344100703c49046c00455040c8188415226103800090380d608480b0340c8003240c0008100c544000942c14019400010000208441801c2002c199143c1c01ea40300034601c248907000d801401d00285 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 207078138 1250 207076888 207076897
    0xa0c080d11030c0408100b0f010f090308040f0e18061501090b030702010b010f020d050306060d0b0405070201020910110a0b070519020d1e20010207080c030315011103030402060708 79
    0x8004031989030702d040100300c0f01d50b034480d00601a5600511501240003c084c0c060141c0c900303001403145014209000044621101480c491410488084000008209000020700c050406000341454190a050b0032042901e00541820500c0c01100e841e5492100b002c2409600075011220f4590510001d4004860505480e040030242d44030000511000e21b40540c40070800000030388a456038180000c205036141c0440610080100c1c9041001460514000c0018403004144072070004041c03902102041c215007080b80c0c40c03070150791300240c00a0586489074180110f10a05c0c5000800960341e944c2c0d00d42c540c000c075040208200000c102044546001e08281e814124808844100309018030300021764545070a8000300118207200f0a010300386461380b103008001450390700c90341c4044034016054655107200ca040c142c0c1955007482010001051880141041c1003804011902e9050030b1801c500a405444c04460522250410030343ca444c00100540f50300903012104c0a4030b4400505000009104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 207079388 1250 207078138 207078161
    0x80a02031b122e030303050a110c0c01021207051c05091c03080606030705120601050412050303181507030513023001020301050319060f06060c060c03020a0c080d 71
    0x2000c02d642401034140701040d840755044910800341c0c5008440d102154811840100f251150015014408203000343c000c960440000c1c68001005035196014007410b03013081c4000c0d40306801c4614205101c0da41007022040c000d001005461402415580e5155030318104044c00c0f07000307142c1090fa4450b01303004030252091003101920200c07144030510300180b42034001c040201d0216000300041801811701200382c0307104445a4503164a08007048010424440c40180f9903410000100000302d131040d00034113030314400d51041c030065459042c0848540b084d000701c80d400e03c1203a4410300c442c08000468401468000c0700f00d0a00040c00d8640a5417148056503180c0d0194216908403487c44405015400c280036100c4654100f800240350600310038240d2100303201d10380d4540e00a0b0180039201503c203041486280c49602c00150303001c01450768505172130480e480040400e2010381014280556805801820318240c0740c1145007801c1d01d06c01420040f100a00944224004540c0c0b15090042d03a000400000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 207080638 1250 207079388 207079441
    0xf090e01090b0906010603110a080403111e070e060d030206010b0f0405060406080108010e0703050606010e180c0a0219080708070212072d080a03050a170118050606070201080a0203 79
    0x50f1612107a035803104284130303071000603251010032035058100e0b6013a01d4a4074210303980c402e1580c44988048070036107100c4002107240e0107882d031042100040c242c41281d21078000005060f14514101c00b4611100c00148041c0c022484001d49800281c0e000c01d82a066a283c414440c2d03d5407030292a1021500640c2c02141e08100d0004001c142180c01c91071090403510400000e10130301000c001060349501c000d20000340254030050211b419507004941020360345201070004140316403041a080701004003076034860452440065441d203281d5040c480240382d411684070254950039a80d4585455200c0c50300041c2188401040c110110754541031022039042c6403c017190103803911003a01811800c04c0d450380d016104461990103010011008104003114200c01c00741c031000780d058038140c40030742c03200d01043c00b00440d414075280e41c42165a0614041c1042010002d1400c449540c14030455402603c40c1f44600e5040c464040183c1e400305080340d005175559005600c4ea00c030480e00302c0b20071898510741c5c001030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 207081888 1250 207080638 207080641
    0x308130606061e1b0602030901020f03100609171f0e0d0e1c0c0e0c040f08060906070503010b03061306050303070312060f032f060409050405070f0f090e01090b 70
    0x2036510000e00f0400302e050030307511035210700404800e40c3c0503003200d94419103003260030542c000803612641c06598800702420000d407804003c240b848290760f00455034500c0305001d00d801404100e500c240d41e44003815015103042500c0c0101d00b22941e0780c3d0b40070007803121480b04030110b200da080b11542003c1c02030820102294007000c10b40c2c801030300094102002310302500003908440707124509080d80310b0105412444500141d401c0095401100b40020308005440104000001d400040c99071a00c00421840300030304011f0a0107450340341080d002420300703420490180014403000d0000f404417908120225021410081b000721400e02a0041d544201d90502010425506150b0003d250f113000120303a5104204160300d81ba00400c1801c4140005020b4003000c10b150710100c0005034090520191552009041c1345100c0005080c0e07904c03a03005581c05079110b00500040060800c0700702c0c040c001da40091000d207030502030010000ea4182c42a940c1c05030f00c5643c01d03e9140402e50140710a40d410620041e0107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 207083138 1250 207081888 207081899
    0x5060301140906060a09050405061c08071205070201090b0307170907050a080d0c02060d0209030118020405100312121b1e03050403050f071a16020f07080303040308130606 75
    0x68040d40c0352000e008001c00e90005509180a40417940181c000c1c0d25150b101c0c3d42810248401407074000c10540d00040d10303c6054107608141044200c64038801c048040d51021545000e105841500e61080188081400a04010b0703811000700300a8500b603c040c961299601c3d0000c64520a0003010350040d20076500920001170b9002c2103071000d94000b601c3c020b640707950300c0344039036904c0c0d101034200d200282c0c90200403401451701800401300e513040d050000d8245005480020b084030340b003076404254010200c211104500f00340c060180e00400700d04c2c14028041c616120071041c40081b00010040020034600c0e9446138100340d2041a049600400705e1880110485c80944503c1100407a00c0380c1c02d4100340c4621020784640500b52169038103584140c2014001c8520000c240c0024604480300000c0d180d4240d0200d601c2603d840c4282881c00d00850b0f0b40070b241030080c0c00c0003810070755185990000d42d02400b40180c00012250800d80c107141001d01d03542c6002483c1020b03c641c03000103100303030305003400080c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 207084388 1250 207083138 207083159
    0x21e04022107021603050c1020061012050d0e010c0f12090b0406020a230303070309060506060c03091212030405030706050f040231020408010f0c0f200705060301 71
    0x8126503d0f000c460007049a58600f6400041c03d1000a0641d4001c0720b2100050410032070691132108141484c40c0d540420340300c080380c90612501d0000d0030f50f10007000c00090707142c5c1200d468010524202010040b0a15484803a00c40c4280c105400501960004481859100e540217545c016000807803007420038801c0c60242c0f4000c41c411b5904000460244002c100109030724212000c64101c0e4004083d484866960140441c4c40c84000401500c00280031030486001030004503c40d00d4035580001c2c081d110740c902041101e0010304810f0255406111103d101c41000086404842003201d80180e810b0761260603e14005103111901502d000210030b01003082000806032244031f110f84401d0203ea41c079184141c01c1c0b980c046901035845206002c540b410119003400102d92507454000e040c191a880044003000e0fa8095804418103a6443c000590101e1807403088090720419482c2603000c4000042d0010311080e08501140140080c10b1440c40c00b0560802c621002044c0191200340c036503940391408007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 207085638 1250 207084388 207084391
    0x504030e0a0803180a061704050a060e061906060c0602090d081b0f0a0c0501030c031b090807290a02010207061406040e0f0715021f0203061804021e040221 68
    0x40400400000c2c03001c15140a017000029201c0c980e5952500c0659002e88282d08070015006507090f015003000709012a602d80100c0c0745c00c9150000a200701c1c140856800e00780c0d0303040c03030500000920f441300500a00b81d0080036a08484c0e0480b9025848000c0040060101c00342c4580080500100140403d2000c008108406d0441c0000d000c0d03a40303074070350028102c0e00c0d403074080c03c0100008000c2005101942c0030b039021906400080c60001813480301444a845051110902003000c90404001040070601c1088038201400000110f0307c0c2186030500c84162101e1406010110410013003491104507100f54169956240c100400b40710038031569806044015040d100540243e083c19420780d11035000281c9410301d400580014003040d8604503880690030800c0003010114001d1500c04603e04a410151001c5d103040e10303000695a050890810000e0740c21a043c11445080b20020000540d0700d8036100c509030700f13075070300780484e4600f81d0340008000348109025040c0402c3c500f0301100390f400d04000301704d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 207086888 1250 207085638 207085657
    0x303020c15040b030103060504061b0801051e1309050f030a03090c0801020315010e180a020a0314100b1809100302030c03120d09050f10020d0c1407060504030e0a0803 73
    0x1d07101100900c0c1081d22038403030340c0150601c01c0c3c800c100420008145502895016020b1a80016042011304100c0d10380c01d007919041c4c0010345408010302c2986404c0120300d6101000103401c0d1007241060000c80c0c984540340409000460362005008203212081c4000c1c51144003513000c2e659588a00d80020b0000d010724072044d80c10350f04480b8040340c010070500c02c0343e019024a40081d0071006248004585c03168280f40055041102100040c203c00361034060303d4005c50b1020009601c900403103038001c0850320348030020302d031000c1c800d006e00c02c41c04000b600030403e45181d22200c6540e00d41071044c0701419042c0781145504681000100010b58040340c8060301600e108500341c505610002080682da1408000301d500d440c0d10421a1049102d00ca5211010740381c4120207aa81c81d0288101c7e281c00e02854013064200703250009020b00300181c45128928001c20b442c10440c081c0305011440c0c03078240c000e40c04000c04045c0e03104007250605000b07034174102c07501c180203000e03115041e100e80006d81c0b42d401c40c1102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 207088138 1250 207086888 207086899
    0x706180b0301030b0a11090607060506030d02010b01050f0309071a0a0206090102042106060806100f0e0709031e0206130305060a024e0f06030a050c06070503040f0303020c 75
    0x8119000c4410450b41200d40108400c0300a86926405c03034014001c0c540c50980d0064104066107680d02d4140203808524002d4400145900d066400d05040c0701c1c01098880031a4905400d2580c80d0b80c000c402d884d015031111110707a442e5926482541c0c03078184560065250303805071101d80354901d20004000c1c401c15056609882c250745a00c980701e0300b80d021f01c1c0500d01c2440648030300c615280c4051160030b00183e00585010888640d29048035050403c01e4170440b545e074282d44801d101524928902e030300100306610f0410b03171a11340540010a68181400300070924244840c0292400001081038041a80c00800301a512104d00e203c1c20b103c00721300d00c02161140104400114424154800d03a501c1c221219042400d202050b52052051103500609406d1141e6113150459002041802c02d610400d03111551120360402a83e14a1940e030002c0c0070522951000030702c100000c0c00801c00c00001c10042c2d4683c0c1d00d6000343c1c500107007140030303a40120300300c44d145000000c10316038005110b500c0040c3c280d0f82e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 207089388 1250 207088138 207088187
    0x6060f2408010605090f030304120f170a020c010e1908030408070506070203030a0819090609150e0a030e0f0310020d0c0903170906120708070315120809120706 70
    0x805481c0031500340300e000046801071101d0180360800040702c5000c5c040060a4902c3c3c0b64651302c0e410840e1000b80400d44125410078030b21810040c00c03140800c607070f10000000c0c50501d82c0d41c2c10003e5407602c1c00300c0098100202d5105164840e1100d10f640c00b41c102c42103242c1d1400075180c1102e540c0e031760040d00c40c06441d0300c40c0c042e00150505040e012191025000f50141d0302d4441e5001c410f0f5103030320f03010300389031000a56003043d005449094030400041500c12100400d08596900b00512014007542c400001c0501e040704104082d0000030364401c00640c5400c01c8010761a400e400107202c0c25403001100c1c1c241c000d205d030050a14500780d0040a801d028800204101c03180300e0340c110350640e4540001002489101b105032040004e02003d400b51820080c051441c050b48109002d04040d81981c010001c65428024040a1605405646183c100888880070664074055031000792401d04000a1300c803034000150071a041c1c480008820980554004a030302580c0e43d140c00800c0e101d402100851404024070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 207090638 1250 207089388 207089459
    0x50a05070206360c0310150501050f1204080f0a020a060e1f02030c0403020d080d0c030b030a110316060f0f080f0c09030c0405070909140c07080706060f 67
    0x8040c40060402096100c0f0441d041820b99441d0990298000075a0701c14215500090b070390803c01217008014502c40450b00c9146003480b02600d0340c5540015051207000d110708134503502e1004c25100120351048000040741c40703c1c00c01d2012481a00c080300c034080320029076041030741c0d0002084644544582d00070131490651640160b10ba8141c422424031203410602051031403942600a1500319000c0d404452400d07549500013024030900c64000c507903465002c1041ca0320400184146804204207040900181200c06d0011b81c94a15160340101b00196031403102c0b002d92420002c1001d003614030701d94402610b0319668090400c0048000450004041000c200d2540f4426103401e4020300c410002800e140c1c81300081d2460300d8002c1c8008981620816075143d80300da60382d00909000b23000c0f07611032801c0241802445c009171000c1001c194990a840400e10010124040450b102a84c0000c0c285446803100c2c60110094800307580510380141d03a032000420342680c002120030950204d00500b2081d0003460 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 207091888 1250 207090638 207090661
    0x1617090312030c0703050315030604031d09010501050409090c0509090303101410031d061008010e0309030a0b071b0b07030506030a0507050f03010f0f05150a030803010513060801050a05070206 84
    0x8580e04080200c0074071940d40007038050806981c0007140751003040c0148c413165002c2454410300310b40540c0003900d410713540c85000d0310f41c1d42071100121080d42c060140d5814034002810794400c5110303070360100b581e94020034180100702c1c4e4010050800100303580748030300707000c0009a640e80040d1280a007048040d5000604944103480590705800090b0113a0f081128000c0c0a43c000d1842c100b0000c0640902e00c0c21003480ca8050002c184516111342481c0500d608140307005084600510320489641c1c4108003070440e0307039800552011a42c0d4400c2034004995940c120440745101ea05a0281442800301d400d002007045601120384074800d15034003006140d498400309503844500d00c070050401e0b00041018000343c20700400c820054100036001003004080081040201c1309103811180320242d8076000e00903080020900c02400940442c0c0d0424642c0c01c50f103800045100c18401d0314070412806d0b10202c11180642c0006008005c40d0008000d1894007030b1004000d804115031031300050141400246903002e42 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 207093138 1250 207091888 207091891
    0x5040b0a030c120602040b070b010305011d060115090f060906030c1403060f0f0d0507030203070b07050d030507120e06040b100b120c0c0115090501140114161709031203 74
    0x1142d00c141070310f88001610345001d00c95050394469000c00c804180d40040c3d9000301429031003201080c080b50302d107090440c01c641c1c03015103000c0064075501204445101c0042c100f8156400601c000421545400c015a80c4001c0765000c0321002c92901c2d8005110798100300d907401110040e80f4188003070150448201c901080d2607032440503071501030020824908003100c00e422400400742c103c040703100b40c1000040d03c0c421010402c44840c0e00031403013030003141414040c89004082d542065410901e003940e40715211a2940f0003e0f081654071070004003824072030002603010700c1c100d1404011560f040d8001d640c0300c0c60200e0b0192000242540841c04202ca4004050101e940c100401390034141d11952524200e030025001440b080c0040c003c00301980d40a1064100030103600e106442902d1070003500340140c0e40c05070300145030b56040034003c00391a60080b440c061000000e00c00c0700d035502e104c3c007180740c01c080c0601c60140c440350f40303100955108000c040081c035803210300700c084400d1290b04008802c1603200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 207094388 1250 207093138 207093143
    0x40501061707030f0e100b0d0503030f0903040b0d0b010206060f03062403071d150108160513090e0c19030b0603030c0a0501090204060611120d0e010e010605040b0a03 73
    0x7001c888210061909400d40398010071a880c0104085142050102c1540c1000c1c1001c002a040414545c82c1502c240c82036400703030f907400c0d904480d015016842d070a0316804001e20960315001000d000940c8500d0900448014000410445480d041810b181100a080c195407aa0240c0300c0d03940840d5640c0340032203120324403090082c0106059a2790b25850354690303012041020f501c2060b521100315641c0c0a0020a018200c4150b8410524024119804080a014021040e0181e5543d81461180d90180b0400d5002114a0804030801900d85049540303210744401d00d00e0350801e00c0c030085000242a0000200c6500398012030f102c0b0000760080040009903011040000c41c0043c40820010f0a040002035104a00405803420a01c840604504240360160308079240d035911600541145070a20a2401810f5149086611b51300d43d030300c40a5458070451442d900545010174110407a0306a600450b100754003081c0207015410481580d240a400d00d030085038400c50901e039002c84030307080003070b240400c0740d8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 207095638 1250 207094388 207094397
    0x9061f050a0306090e030306030120040311150c01050f01080d121107080403060f1506050306090a0e0703140607020114040602070c0302041107020f0301020903280b010f03030e04050106 81
    0x18442102900c640d80040803070810b16072114000034250a180c400e41e00703030310015030103103a0301e00c1c14004250031180bc20000c1c0da003040590707982180c142c402c07800350707810b8035403090008040b28182c000060201c404127030450514000040c40b0202c151042d00824081c66070300300000d003547d03251020243c07107001c0f08608000244031480003440b1800c00c1d80011040500f03080a81d4034204a0303880b05980c80d071068100782ca82c2034031100347c51403491152040101c4507070458000344802c0d04200c0020268800905072912500400010271000ca030303a1381c8906590b510301303000c03908580d40c0c03440c00c580448140d21014038a406031900042e031883c0103004242416000500e00b6440c0c0e030792640c0741c0000b50000d55064a12a64902000c0016111845208406071802e8460f6072115401e1040052981915110a0080e4014811031000e03490004440c034101643d500c80010748078600b46085100f0780060342c00743c508a40d04000042803000c0c101c0c44400e0768041e50b248425101820248800d4800a125140004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 207096888 1250 207095638 207095689
    0x90303060f1e0402070c06121a041508011a04050a06060c0209040503040e13060b0d0b010b0c1903030b0306090109020306011701021c0213062a0201020f030a020c0906 73
    0xa1610704054005014010000000150782e80041000c0380c101d850212040704c2240000e0200c2a040702541e0260201c407407061180e0308900e50302d100300b2200b0303d043c5806162201c05081c81d8000a002c2d400251800300001c04c0380383c01500c0403146503019144000d00a230303c4c01e4042900340c6028052b00066800a03140c1d48110001c2c0d41c00d00800c01c0c0000c0040c3c589010903c4045004031211501d14002e10400151200c10090783c1400e1044405604859100392000d410010000300540c0281d41100c403a0000d841c2c544040c481d0303080c1402400100244c0e24021406154205601503105102d00c2c9000e8040b2001a500c820340c460032075102100195150744000d00400512044081464003117654030009030a2120f001500d80c40f20581c0c8405c01b4100e074002c200c0d110900031040000f0000d100c01e2500c01148c902092024031a0021184482810702055107a0f4056900130003422a00c080940100d0750f60700343c141402900c0d036100c0a0014880c02900c2e0100742949820001c4556007400325024407400d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 207098138 1250 207096888 207096919
    0x70507212705060705160603061d040521071e0b0912030a020a0309020d030e01080c1303120e091018020a020c0103050604150f081203270705040e01020a030509030306 73
    0x10741d00201421200351282501e188400f030103203038031b01009181c03d071070105046040130000300c00b800d01c03502018400d030a24000c000100e20002210840d6403400c3c41d9011112080f851410b280c0d100307045000e0203150440f01c0d48605800403000440241e4029070320a06140c0b00d00f81c480351551420040041400d5050012810560595000707100c0d450640c240010014025804130340d00c0203280c141900420b10a14101d0215600140010b80c4461740d406594504540c1d481702041c032002da0b020180520800412004000c3d0041c59100c2400780000c01d40c13041450400b050b003816041901405145a501d4240c506a1034118000e440c210f1030f0a801401c8081996401100201002001c055209890b0817401d4440c81c0f042e80c9a0700588000020f04002505000703e5525210018243c2004480100100010211003080200940441031203040404503401c0d2441d01d0700b0a03540045074800c4c40c014003540800815401403214864a8405000030380d90192469224001103814503000020b041d8040361 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 207099388 1250 207098138 207098149
    0xf2808040e0c09150c120a0f08090304090e030c01060909080405090411040e0d0206010515040e07091505071101081b0d141006020601080c011205070507212705 70
    0x9200c40074503401824282d040b800501c214070301d44c80301c043c0d030301c00001c5202c562401804204852080d21060700d1400c1100c4000030b20101c0b000c210442080f0180d030110344110070502c102c40c02880c58110038415080d9601044e40c03a0303481003181c466203602c0c20100240b200c0b42030003003c81d1542c10107602c40c202480d00d070034010103140003482180c02c1d40900f0f01e5586540e80e6842140400c071000c1000300030f42c000360750740a4580f002c1070300481e105540c07001215036074100c0301d02160150b0310651400384181c4c8602c6400d07a000c400a400c40d000400b99503002002d455803100142219502840000b0517040000300103586400d001e4034007048030090b000d5028070712000c3c04020520f20040c0030002403d603080783e07000018118240e031203101d4032071070040030841983c1c1004854050048003010f0092544d240001801c0c004c0501000c401c019103400002e40f415000c2d40588180170780240c0c03410780c0c2811809194005000121718000450346c2c100c40401981001840c01445a80c0c3da680b0050050600c010000b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 207100638 1250 207099388 207099391
    0x10207032607140d0b09040804300303021606061503051e04080903070b071112060114040b28150903020d0f080906070803060a050609010518120f2808040e 68
    0x1d00058441c0c0c00603940c6d844000109210354000c500894582c0e080404d4171130403504c0c1d800d420030040130600410111200c181040c40229034581001079075090710212007800c0c022002c0d0003a0040d490888001070303003580c1da000000440c0e10741d40c0800040d50340c900175000f1f4403110102d1540b0601c65000040019211074020003441100908540c0d0031507994005584036403002c40c00b02da44400185060600d41086441d81c1101d907000c3c00509443d40c1424040e4001c22100300c1640e1290341ca40d11000140d072184180681c2c0514144408031180c0e40c010b007200d08030b00c558401c1c0d140001c001e40765401c220b4450701c00352050f07a5005040c9036031790351192607100c508210040b00f503803c0202046594a183d540070010040035200380c144a482e490100100801c1107420b03480140603000801002559a03444007c884200e10441600d001c114004d4020a65403403010611480034071806881d00f1050100091144001105415070003d8910544d0244200d25443c0303c014100305051000380708040c100c11a05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 207101888 1250 207100638 207100657
    0x6140108040c180617070305100b150d150905130212010b191509030f02130e031303020f030f120a18030c031101080f0a0e030c01020703260714 63
    0x2400c810751140e4003858146120041c005840c3e507501c10070440500410071211a902d0000040c000b617030307c0c42c2c449030744400c0d44142a190090fa1214101190381e600b8032603908129100e20419262001a05032500414031680d803117aa0390502180000e0645807802020702c18a45490500014110395084c4619000120301011042d500d031103d43c3d000c1d403140c05c86150013160071942a008070b441d180d044031014103000c10b840104545484140b0109940c05296044541d05941d00f00e4400326804c1c0240045c103244404803021b0000050b042a510f4280c2051016240201d50401184503180308169441e4006080301e44a80c10803500050035203800c00280202440c50300707044443da15038101e460600e0910b500304030b0745e41442440510600c540c0b103c40e005898000e00300702d04282000e5009850b049030082c0485a03030fa03114203107450588000e1080d90600e001801c029034440c2c10515010b07000c1041107141402c0381460654043c003209501e10b007580514801d4945110003c08078100d82a16031211030407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 207103138 1250 207101888 207101903
    0x120414061e090a2301050a0318060f060b0405130c0c080a0f12021305060c0c0604030609031b0b06241305041803050301090203040c03080a02030901020606040614010804 74
    0x54040e00031150181001c10400035501da40d07106544010012241c0b0315030000000300c070031599441c10390803036007210130000c61090030080d8540d50800000c6021380503510315648004030301d50142042001036001b0f1942c4584020041c0242525001d414190303010320b03c02d4942c0701006062907101020740d98000c6403914007500c5c3c0407202030b0b020748540300164082d45007400003929070024004aa85c1c007031745001980b501e250042d441c102003a80b440e100e002c030a000f240d2007604001204082004204001c0042440240c100d0f91542e40c0c82c1880401800c2c41482603000c940c1e4094100c601c14180701602d1540c1360b03c610b42e195240c54034000c0c800c01c121407117588003007000311030250089011107002904c952a061101c14080c141800e040c80250ad0b4200c500010081044601c030f00080d40042c29281512203925005071a80d50b1401c200c00340c88001d601c040d100702e40c0060354290043e4080020031154000f0b030200e4895840c0e100c2400103c0307401c3c0c45003d5241400c604441020b6220305c0701e0940050040c940f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 207104388 1250 207103138 207103147
    0x2030706091a011706060a05060915090a030c05041107240207020409060506030c030c102a0c0f120816110907020d170403050307120f020307030603021212041406 71
    0x102c0c1a0000e40a0b007082c200c2e0140300c0301e40780d060501008000c3d0b004000b40e03851600b5500d00000f01c1c640c1d01814520a06c99260300d0b80c2c4802007000300b0280c801080c402091415401c1c0d5a081014580201d03009941c09581858980713003081c070180044441c010341c0700d50916907410007107004d094202d1922001e40e448a03001c20030310026030b41e1800360084460058030001114100401051710701036179480e07151300030b0304507884000c4540d4404c40348a400b10302904080b242d0300040c3c0e0750410aa083e41c00a5502c00000320b40e00028401c5807440c03c800e40300741c900c4008146456001440c0c5415043d03800503d501c0040200e101c00301c04030481801c000d44a40301920300003a11000040204c0800c0381c0390b8005074000d65a50b4030889d0300450044070380c403040c100d403861410251801001c900c00281400300740100707a070014914448a500c01241040805c90844d1282040e000007400b506440c4801d84c4280c040e01c10501d1100400324451001c1d100302d00b01c0e14035007458103c540414030340390400654010380500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 207105638 1250 207104388 207104423
    0x13030306050d1109130b16031509140c0309071503090606150e040504020603011202030f010c080703060803130e100801060906051216031506150309020102010606030207030203070609 80
    0x4804075412845100f15100419000c0e0522819000c003e00d0a000e1290f010a440045528242029000f0f000150301e0407003141c0200d03054001c0c000d1802d46610703990341000000380910103940507040880030b441c02c3d03100e16114150000c856000945030a08a40c2114204004d100c0106864210142e141e01b008210420346132568000c0740c440b6807000b1001a4000801d21450754402c030424000c0504803170070411402c01360003250305d50105018100c1d00203198024601590380400104c0c150302034807002807021201540008004940030358041d0701280c200b8070702203440343c1d001c000d841501c030904400021061074082c4825050201405068000d80310071400700351074200f801444080e082c0310801040f600c0c1b074502070020b40c421403111105203421454100103043c4002c051013088980180055040400da039440400400060b80640b505501a21100802640541101525a000760001c02c0030360340e80c14054003648560707c030050050300108000400118a98000a000c030f0040b980c0402c00103000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 207106888 1250 207105638 207105649
    0xe0103150f170d0c0b01051e09040f0302010b03011e020a0504080303040809100915080c0d0603050a0b0703020403051b01031104081501060906050a120b0312030f0603010204031a070e04060605130e010605031303030605 95
    0xa4030162900003038001c060bc18541c09000302c4480080507802041400300841c403814002862294183c0500c0d00028a425403503c19820350b00500741100030f8a50740e0510b032902070141d50040300c5880c09000c0710b09018a13090b000340007803021105656095802d079002198119001d40d801070507118031502c20301200041f0b01c054411200035500c100001e0510310241d080110b0020b0008150000b014010003050000480105a5000803641200250440c110080c0164060000c1d41e00300e0844202c0800e001400c4c5800285190000307800c940070180036600c551044542c60554020a008102c4c10881007003450b1107005040c1789503070114000180040d0380c0d40001d01f801d00300701c00e48030a6000481402035411164808542010084000b10301d89491a86ca0000350407c0c81501c2c244040040c0c00030760498024031195a400030003d004001454030703400007802e1600089080304d84c03881c6210012070740303403160490070303041e60b05d5030300d0317290640d0784140f03004000500c41c04040381003549641c0700041c1a1101c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 207108138 1250 207106888 207106891
    0x501060c061d0d0201060801060b0c0c0105031b120402040c02010b010519051606060f140a0501030f020c0d120e0303040b0c1b01020c010603170a0e0103150f170d0c0b01051e09 77
    0x704d07800414072034a00040b5a007580d81980004010402c1003254403070200e40091340d030000320006c0c00d2031500c036034802ca600b55008404c404064000407000170042c4112030b00a40d564403480c0b0031101084011002c0f4422400c9581600e03040d800f145007041020040c190120783d601c3e000c1c030b07149040382c40c21906100d000f10088221508851503a11a80103000032650121500c028000035601c4007280740a074000241722902078032405041c1075890519400c40c02c110380446024601030030449400292106c0d000b0094003041c0021081a0718201c2d00c54480070b008000c03240104e030800c1031103c080c0c4810307000700d0003544004c45483c2900c0011a2242c0460300a00241c20a000d0050000445078518101a4544908445d101c200c91804001c030401180d00014404c49824081c80d00140f000f2020825000382c01861704003009030b06000c00002807900d0712502c004081d4a0841c11744194861080c025030b610f41c0310030310060100e0201c0005101c54180780c007121504030a80c2101e00e00c1da1000300085400c0c40c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 207109388 1250 207108138 207108163
    0x30206070501051006020f071503020d090c06031a1f030e0601080123010b0a0f05040b042304060815071205040b060a140a05010c052d0708010501060c061d 68
    0x44a00070041c5020003442130340c00802d024006080e05590004049441d40d40d280034803071449000d5100305960798403940c10707600700b4031170090100301d090980c0c00d10800a609a11400740000c0c100f005810701001c003150030ba40884005460356204031441ca4500402803010758400c0d007096a140d152040310b6a00300710560080c81e100000051f00302514101d0002c0d20200448203800001c044010404050040100c41a0f0720513490300b90f00b806031100d0201c07100e05c100e92042c0c00402c00403030003261084135520410309030184034200c045d0019084091105990300381c490b0711602d0b0052005000002000302005900400705d00c0e1a040c0c100c20110030b4000c03030f481030350240c2d00403040204000260400100c40c4028201e40510a084000340c10700084407601c007070154504121500b07020904100003003000c410700b40110007104214000d104095070b001c84103560342203614424800005281c01041c851035058540700c1d5a00a03044103141c1b182e4001d0407101d1340d49140c4959036559020101000d0282070035101c3c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 207110638 1250 207109388 207109391
    0xe0d05030706060e070e030c0f01080402030a0c091e0605010509130e070f0e0601090830030702010504020312070503070809031e011e11030402010810180f0c05070f0b0c04030206070501 81
    0x5c0040d001401c041c0d0340101b0314007079800181d000a003541c0348200112200303000d1a14014568662010074100185008001c00048825030701144902ea10741001c140034051881070000c14030107100720001c0d5010340c42001d0100340c04200c1d441b180c1c1404422a40c82111030701c000714000403a1b51845143c0040c5074009041c0d001540c8080c00b0355000d0703400c544d4003d042440c01e00b48482c1000381c210b4070744204080d940c02500c0210301c48840c000d80b212211840104041600b503c0b031600741030203406407070300f264100d102e40103084010038548800c1b019540040e8200009508082203940c8540f0141c1c4101407980d41440383c0744c140240c45c0c61a150001c024003a0f20000302e21000300340c400700c4000e403500c00041b01c014104215051a451802706696000390246001403050319041e00d02031201e02c2603042006210f0000f600050091855000b01040201110040081c030000c208201c5441c01007050007404290f00c042224003003042c691465400502240d9400d1500da540c0d8002441a4003011040f582c59 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 207111888 1250 207110638 207110641
    0x18130c0b0a080708270a05060108010606090b030702060118020c030304060c080a020f09060304080405120708070f06020a02010e030c06070609140c060d0903020c12030304060609020a0e0d05030706060e 88
    0x660b005411030780200300c5040051150074540f1045540045000c02d80c80900c0070450011040001000041c851640040c2980c005584981006010380114041c0c40c003c0b60030752100142002424003207911603002c4d50702900e0540d003000350003111405811a40c42c440754007440b490900c01070510003580110300c00d150010300d924810ba006040888003c24030800d9510501504802035400421034200307a0003140ca50b0b40ea5540c610785140140540d8012035044040c1d506000001e010000d80201613031821b00c21111096912200c0d100c5101c0e5900442c0c0060300038415280065000b070380500c82400d0300034280e4894064400102c4c00d150848141581e00360340720003185040c04880e0301403005510030720000e0a0340281203000301e062841140e0807100041e645a404109051007030100c4964550001d0040901d10001d584a65030381d00180c80989030302d4a0158000340f004028400c98100c181c064a176214001080c40400c04000c02a10303050300e050104200300170000390b051040c00003500090100c2643d5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 207113138 1250 207111888 207111907
    0xc030105060f0d0213150602070303020c030a1205070f051902010e0604050108180703050102030a02030a0f0608071503060b03011e060e010c060911030111030106020d0c0218130c0b 79
    0x29100c020300660b000c0c00d46450240308640b01d412003210110340583d0060300040020140300010000714100d00700034609030f8004035041d43d0104201003103074029422650416081020152107058411000304600340c038803889285280a203000e000300c2401880300840511003a21450304007900341c446070301c040c004200d00804641c2c02a12204411505455040c101420180083d01211020380080480d44012202c021461000c200714800340d40d01800940d201e040414218000c2c0d00103588052a003403c1c1514080707032505901c0f0b0901103c41e15002002040e140041a900401c40105554105030310f80c0400f02c0c40540c4800114002c1000d07001e0041c5a11b90250420300500c2e06800c04800c010210400c804160b07448105075220395003000000031200b28528042002014010413190076500b8078074000b55000a50016504852842e004d07209a03621048040307898000000000790b100c074401248121140c843d600b86c1c0d5110640e880350049500107a00d40042c150780300c0e84180300348840007030749829 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 207114388 1250 207113138 207113141
    0x13050d030b10211e0e0703020909010b0d030809010621060c110703060b01031b0e0f0307061e09030803092b02031c020904060308040f0e0601050415200c0301 69
    0x5505a261400703c1050b21403031803000509007a114207402d541e40320203484911021924035024012083c0d0010002400343c0104142c60350500c0c0b209a11400340440018035a10301030040e44000c0c40e00800004002c03005a800707030b03000007014140c410030350760340c1c5004a00c2e004d0803960710100007020a41c001e181a028076144056132030341021541040101c0120055800300001c005084e240d00400c0800d00104440048004224404114000140b00c12841406c03c0d08401d48001850055031015440c02501d01410b82c2c40049100e4a0300064010301845801e48a28920388282c2043d031528014550f50f03900c844030203400982c1c0c44030241d00a608074601511026140100100d00384810b40c8584402c880040d4603402000c010082012200c9020020090036a0449810600c0140100403968403800d0075000c45c0c1040c003c1c40d04240c0b11000102eaa0142503003114481d2005a40e01e40c80c05040071804d020001d2030305285c0c801d100b0380f18251302d4111142d502d109004450b0b01d0041c0201011581090b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 207115638 1250 207114388 207114409
    0x60a031a03190834020102010e0c0109030f023f06060d1203290102010e010204032406081005090610300203010c05040806010b090603040b13050d030b 66
    0x24420307442007038050710407031040c4034501d0b10702d800c510583d031903101512140703068440c410201d6403220010f42104d01005800e416140820b8002c0e8000c00550724815541ca907a0318100342d1307450104030b52410420000d5414401e00e01464409071040340950740041e4001c0e0101503c5201035081138078400c03800c00c501070343c09124100d48100001880d0f40e00340700c004641d8480941c08041c0540a030079030080c80050090300b004504060104003640707141c1407a144a014248030000355070040d402c1080441440c10140207450a4a42149582007403482408011a060000e001c00c1c400303c0743c132440006107440b000c1c000e0152060540380086a2443c0c60910b50b03040900c010000c40d8030f8164841d09202403005200011600500b07900b40149240048481e46c20b6100a810000d61640c02c041c40003000d80c1d0301c0005002196031a0b000c803209030b40c903052220007600460200e203800c00380c01d10006c4c000c10030801c0c2c0d207500a009000320780340140341512280c1c28440150030040100303485003007000302d504000003c0b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 207116888 1250 207115638 207115691
    0x31803030103080306010e0f10080a060f1809150c090f050105070b060907020114011205072702070f0614061c0b0103140c091008060a091505040c05060a03 68
    0x21465503040d80e407603004600000e0900390401020b184140d90340d03110120103008960f001404184104003d900050500340c00715035a18040d41803a00c0001d140f00704000c0300f010790381c1445060350f80190304004080206002001540c000b0b4410354510341202d01440381e907101d21030b942d80b061411410b00c1882d00000010380c0c483d0f4100841002500c000c0780e0440a102c0c1c10010032100020f903611203450407405401003078800d450710810040001580f00700d83c0f0302c0b100f150380b1070301c00e45071642d44c0c644600d00c481d110508248001280c1c038180085225591703004082492143d1006038a6880729118181111000c00300401501c001c14284540c501e04001050314603403400b90500d0039008250740b07e2000d41d030180b1005141055110140c102c1390350903c140307a404940502403107214503140340c8001289a441c4a00d000500030040407a800c02c010b03000303604005400422000a0048a2481c4002010002c03c151218000c6910104e0541d84010003050303001d940d540d0102c0c01824214101c10a556400d000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 207118138 1250 207116888 207116893
    0x20a090509040b0403121b02060f070305010e0a0203090304090e100e010b0d11030102040b07050a030e0303160305030a09081305131a061b0601030c260304050402070305040b040b0318 80
    0x104000200e0003c02164070039454074103104440007005490003e48440c1c03a00380c1c03100c0002003911519a9000451900c55002d107000081c2c0c58594020039800c80f003080c0100d400006514001131a048180d4000710313088415102142d2030560769003000401c880c00708090240c030313800840030f94540107210301890f4400c81c044002009202e0a80c000a03215521095000f002c01011108410003590294159001400b0303034103011381c0d40c00d00c5242680c1c442c456024120003040380402d00b00b5543c103001040d81c06c403c2d08140a07250041c80e81e20b0945031030700028600501d654541104c6000292280d0180003004816082301d20740504020401c26048112817904501034a00442048109851f0501c41d6541c40c01ba2080d503910044a0352080a00500c201701c2199803151303000007c2044507651406048588a18440c1d1510800b00412540c440501051800c55481031000b800146004d0b40140f803841d1081c10b2052425940e52071500d00c40e0495845020351800100811520440c003045880110000202 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 207119388 1250 207118138 207118141
    0x25050312132a050d02040f05040b0f010603050402030606012f010c140c1903051612030b0607020915030309030604060212011203020a0308190513060b010f0c020f010c0b0a020a090509 80
    0x41e61882d001036403181d60710450000c840c02d070664481d41e101c441c409202c41014822031034141480403601005980703450b4240c0b140300000600c00c0c480d10070140640c0d4010003901c4a91141c40c011540c2880701392020f020201c108601e8202c2000786107166019041d9100080390600803a8000703020340100030080061018100b000d89584000400c0414400c1c8400340001e10405840c1030440b107900500c071150703804405811904050101141c0100e84910322964144080020f1100340b10300d80c001d03940020340203000400480c2c55050184d000c501c144601904503820000f0314000030746028130541d4207903000769000544e0003444444a26071400f51000c4007500c84240010f6600079601e0144100103400c01a4110100381c0d1108280f00d524030101c103078402030207903003015900d040d5681c640d170b0070440b00b09103060700881d15540623032144403000840e42c8501d4080b10703440d02880344400309684000c0c10000240450780001d862014042e0149040c00d00058540b0038640020306080c0c0b0036005284a00012380 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 207120638 1250 207119388 207119453
    0x30f0b180402040e07152a022101111b0c01090803120c091201020a0e0f0f12010e03031003030e01032c0c090a0f0b062505031213 57
    0x9512a0807560641e030014204101c402000e0410010790080f41c5900c1038250042c602ca0340c409624041c04020101d440d0040801405ca0b0001c5da488446c02904000804d07003000d1280d500841540b2540c211500100d00910300444c0603589a01c802ca0010580381d40b00c0813400070f4041001440d40059080c00c0032180182072005c8a540c0c2e011300701c00009030440141c00515a410601d069515107100904090441001d0981d96070107500036135141c80c009081c01d402c80c4e0441c80c10409410104801800070a0384680ca40b05200000707000e6922000150b40390b03035145441030341c00c0005610034000702940001590941c5802401407155000603410503041088081005040c1c035a85000400c1c801e0442d03000484155440c2d0904185101c01c680c41030158080113980304075504410700c4841c1840041010f02004010450f03907008102201c910020450703920031001d42010040401c99008008983c1000e881d0300005001c55802c407059111802e0780206070b01040311070341d0b440d68601c4a82072510b05240c00c25 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 207121888 1250 207120638 207120679
    0x30e1230220f05101a090402100e010323010806010e040503030106081504090503031f03050307061112040f1e0b0f0604020708040b0a020f1504020f0a0504020a030f0b 73
    0x40000c048990304074560030401050941000036580e0000684d070041404080400003000340340c0d00042003001704106000b151a20101443c41180d00034642c1d95104010340c41103035405030340c488050505a8a079104079072008050540c46841c0c45002d11895158140a207031400c0c901c1c182e10000c0000600340070b103c0050390100039281992030306c4c50a1803050355031000c4041d440c4d0f0785458443d0040d203046507071018040c2c04002180b1131302145032501080c59408980001c105500e220250640d0820700c00140018410780002000d103241410490911140c06142d1908480039102104e000d1301c074156200030003081880c3c81a104440c044041030f8440d8503203c4d0000050300900306072403244450002000d9a0341d6505450b49181c100400c992919241c000711882035008490600251041c40d6010f05941000104084016124040c01c40b0545859083c00901c20074042d00702d500c20a08200840e02d500e0703500c003500320344106e0b50f0b010558546804210088031100c941d03140c0203c0c034124801c01c109119 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 207123138 1250 207121888 207121921
    0xe011208090109050405091506010f1d041b0e040507030203010e040201030e030d02040909051219050c0705091906090506010903111804150e030a0f030e1230 69
    0x11008079952180c0c0001265042c00e160440d550051030300051000c8901e0000b040d40c01b03180803246c4074007a512000b005445501c511410303131000030303400c290300b05031080e40011503d0140005880821941d107104505940140003222130030000718803c0c0b8550b198038050040540240090804510395414070050400c00c1a004001905158039494006a94941001103501c428411300d411510390391202d40c54800b400c0f001070140e400b0f20542940700c016400500c1100c2040001c090501e203083c00440c000e5039103401176840400c45001c0c9240020380c0b5114858054480d407001e00f0428031210240405d0400c444042d080748a1241c034000402a540e40c0080007002501d8025003250034407035024000601284010182c2c0c0f034449100b205100800c004044811604006450300340080300d50036154603030300d0040f41c0141000411007914142d41034026400340c3d00c0403003a401683c0490940c4405100c941e8010380722240026082c0d0782036038841c0907000c2c946181310441000c2c1c2440d0f040c401443c0902014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 207124388 1250 207123138 207123143
    0xd06121a06010e0f0f031203090a151401051203040503010204090501051009060e06091207030f1a0906010b210f0603010b030a020a0911040f06050307090510080a1a0402030118060e0112 81
    0x70101a6171070b83d01001a8102211500071681e500c0c902040f06c01c5c3c548450100c115200c80c00501e09110340c0109001d195203a0000c0003000c8000e81c0381c8010002030a0a42907440c089000c02c00c0085111346080c0000e1028162402010400c0d51411041c0002c1c01d402c14a003000300b086103503092080c10742c042030707010b104842210300301c2d01c8420000000e59685640c114102e842c0c802e40000100300503d81d0300038503a6600803402c0c000c3c0701801f56416068070204503002107151300400010300c100103582020b043ca40c184803800c0d01c401c0e01d1076401d10780900300c2074607011400130110b0301b008058542406614500c481c1680079201440d06ca80c04586105028080c00d404152038070100d02c07446140c0d4050303e0041010703c0411802c2c07a503a4201500c80d910a80d4600c0018004010104107414a003194503440304186d607803900b89a17a85a000c00c010407801031102149032650380340d41300c941e41c0c5001541c040c005103d0401c0030503421200402c111000f951002c8145040403004010700100d0000c3c1352000e58 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 207125638 1250 207124388 207124399
    0x60412030203090102090a030c080d0801080c0d0609080d09020306130c0b0c010207050706080f0c07030c0f0507050d2f0108180309090703020c0c22020d06121a06010e0f 74
    0x80f5512003050180c0210000705410611210b4000140416003c4030802c691104040c0d595141d62031400b210b0b42c039030901410305c559208031407215590070701036005120a40134050024040c1499a1280480d610481b825040e154448280000f0341c9000c4c481d0a400144c6003070b04003003240317255903940c005004030320500c5078226002c61218000340d42901192045c940c4401501c12807901c42c0009000d045080d520304000d184442c000038200e005090032100003642549420030320381519501e07424541100d4904803854000c8110020380b40d25008007046002d8410b400c50031244000100b101f00703403030f8240508071000d1214804001d0307a982140c1025084000184401400d040f00303c001742c654418485403681000c0c00c4010003520940c90350190a009040f907091700c14076401c0b070003080140704c82010244062a01005090380c0e0a070581e005140e55546120082151941c85c4201e80400441e8407050b60742d00c414640607544a00700150107944100c090074030410b85a1f209001c140700310140010b050044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 207126888 1250 207125638 207125641
    0x61d0a0507081b0108060319050d0f030c1209030e030607030c112d0109051209040e010605060406031d06010308120a05071e02150403030b130b0609061315031508060412030203 77
    0x5807424080719440618a58600a0b11401031030481da072102d140000e0ad0002c0e810300c2c220100c862007400307040000c030700f140d443e80304141c1400c2843c4e004044101c400c0781488100d240b078040d19282030192600c40d01858600050b00664031030080d001100b1032618031101e801c1030211207044024007111720840030340501c00389804000da125860040041003000303400c0b0311a990304c1403c494000c0008040c4298140c0301440402c5a480c00d840c20b030381e217600415500c0182407000b4004988640d00003484070500100c000c01605059100a003445001e80068980200c00115601c0000e51110900d4000107841000c0007940741c50f407001459024003050f00e80c0d018a0300c440c41c0c40700c0c520030400307030410140104012034241002c0c6800b60040c81b01c100010301a60300394849071040c0c3c00d903104115581d2801f60030b80785401442ea040004644c00000000000c5a10200204480308241f0109100d01d9954500060382e0301404c1c600302d0900070560040c0d1203640290100000035501315944610550360303007009a1a03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 207128138 1250 207126888 207126901
    0x906270209012d0f0c0507170c04020f0d060f060219030c1b09050a060e011811030403030b090c0f070b040c180203041a04031b061d0a0507081b0108 65
    0x81d886031000f4001801c074100495600300c0400000126030b0034160b19003d03036181884000380d981141159000d8800e40042800304020001398803070040200d10441995004c010707290001c0c007240c10400c02034000c01e0011509003e6140c0c0380c8206030142000070240e070340c4207252000096540102c032917104024628007141d03004040c0a050840e8200b980460325110b0804698154454045144103140340076050030003080d290f00241c4244403e98024642c0d5aa0a80c200700f44030075900007150403d200b050340c8140440d40101ca040140d4016486658049030030034483d0200144080041c1200703110301c0f400c100b0209000d0391002195130b0315a000c810940709070b856084c1407564a8890b4007108284140302c0e26002d411105034010b510a51045030302c085503400c001c000c25003003e41158000c004c9130f10121504c91005501503044001c0d803084201040001864041a80c0184010b40b0006181c3c09620f0080402c84180400005010321800600441d41120241018102896501410f003d83c003c00b2800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 207129388 1250 207128138 207128147
    0x60507060f061d06010503070c0b060a1706011e0e010302010c21050d0e060609010e09010209030a060204090c0305101202030c04110c060705040b0706180c03030504090627020901 78
    0x10207004501042100c19600c0024000c16105240d003036066554600000d0f40c25030140307040e40d000d43c1c1d05940d001d0350241c0540d1041151030000c0d001c22f43c840040c0c0d00009a1110300c90b02c1403030703c0c00320318050200b5500d0f04044a140c80248401c00010801c600c0c018400e64070256001c41c1102e40900e09542160840e00300030418200c0102141c00e0b4603114140004a582c11100403d0800804c042c10019140001f455a1326918280c40055111038050010020448000b880315007061f2100001842d001d10440000c1c506804d0703c1044850b00d4002c6010040510580b05140707010032141402e128a242138203108070881a51700075070f003403c80a860140300355101003140303505205e07000d0002c01c580038402c0103007400342c1c0000e60450307135610903c0c0002d400c4520072815507080301c0c502100542882d5040e520b48001d0400c08216280c101d070344011040110790310070491801940240c41d0181d031141070030701c40350541303541d601301200d081005140d8001031482e20412061007441503000684809400d401280c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 207130638 1250 207129388 207129401
    0xa0c0c26060c1c020c06010803030105010e0604080d030b060d0e0703061a090106232208030f192d080702070f050904061103011409010e0f04170f0a080a0c0c050706050706 75
    0x15a40714900021030802300010095069070401d884151481507441c04100e60707803049026a43d01500504103050401d0b000e41c1050750b001d10000d11890900c9140c1e9165400c6602e1520010f00e035500ca0a803c00602c078103480703803c01d40e8101240c151034116091000c6408041c1c18454002003089503041800c440c1c1882030880703850301000d281d1719601c0103504c075079072110140c220090036041208140091101ca00004540c00061070750291820320b0f09150700c2e024102c1c2480501c200b40030003075500198090741d014551214074048039200d4070492640d0401881c40324001c141a06541c401d0405029440b0320700640c0d0100c1341c04031a81c1d013541d80d95241c03a0010b00360202d00c20342c01590100000c1008244c0c29100400f011090b51010800d0b030365440110b459081c1039a810b88809440404200440c43c02d407410000800d10b1190f07585840c102690034406036100c46c0d14180006c05000c144a44444980646080d5848500d0003001c035804a0f2201d5480c4e04c1e042c46120b0502ca80019003504100365508a403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 207131888 1250 207130638 207130657
    0x200109081b150f070215341203020a0206010801051902281101050c12060f0109170d020105010b1207050a030905070e061003200a0c0c26060c1c02 64
    0x5501d94492a0f2030480320b4005000403803040c007000301703030041444680040c0c81c1100c2c124640018408041080080d001000a4961000660549510004c22544040c5c1c0c0c40500e02680d0042e80c941403010024108a4182c1040e14164105014001c81c0d215148000c000440303c1140165101e0b200d05000c2d542c40c4c0c440300502d400d441c10340010030016400c28182d1040c4400c0c103009002e603139901594200103201c1d1b207020700000083c22020410340e0804280f140c11504044c1000c1100b1500c51a010344415008510590b40340d10000300d0003902a820b0140301d004040214540d402d080da0364110b1105040000c3c4200d042210201d507503003003144250008407a00d50800e055440741500c89440c130300003000403034210340680c0308683c04406161191168050502c441402040380c0f9150b4081940c41b03500c070302480d1041180c406e0015000ca014010154011310305803041d80a0717090720408116444c09040d205030910380098040021244090040350419000b00200742c1d5111a050032140c000e00880904 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 207133138 1250 207131888 207131929
    0x481b0f1101200a030c030c0215040807050306010302030a08210a0603060605030f150a1d03070201030b150403030e0a03061506030506040e0c0607030516200109081b 72
    0x4a10a00100888010000d002a82c1d0401c2481d07a101e000e40c50b1141101601c2a00da00109803000030031310940000c55960311a00e000d200844050300010382a00d000c103c00c2c0c3c5001400101003000d1201004680c00a0806902400c2c4561460300040d45a140e0040050055100040c01e00582414104104042c10389081c81c136000b4144064550014a010302007121a60b1522401080c0f51034001081d800152110340205481e160040c03015007401d401801109541d9212a400c0850520f501c84e00c0c0c205004d684001c0d61078260500004003a81d60324100c8602988030300c0e400d002c050051000702c6041e03d070142007100b88100740030040b03200225030386e1026056520308100801c3c80c4905001180c11130304295024480d94448508020480b1090a1804a2a44035000008042c2000c90203048080d00906005043c080161b586c200c007040611811501c0340e50703070304030000e68018401803d00021400e285c001c4596080c41c0c05a90340380749160381c03100c0c50008001014000d41c0d0b00344000c100301045c10749 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 207134388 1250 207133138 207133163
    0x3080a02030a03182103020c01060308180609010503040b130f0b0601090f230a03060c02250308030708091e011401090e071a0706481b 59
    0x3501c0c2d4018050110000e820100c9504000d04014025080b140d000031443e58181030300d584080c900382441d40071505060b0240049100c424082c485d4000860046000a65500400d200c0301d0442c00c100c29610f204c3c48040c8407840c0140d0740b01c025288d1050780865204050344440c0322064803da401000188141c2d0f500c0240c00802c240c0e0102c040c0249000e0701c400d0900385d01e17000140140c0202e4010585441f00b1820903114501e4a035600c460700c0e010241c070310b010441e140c0d212030043d039618a0804025078400034110503903601c1901c0e00840f0007900d0500d4100c403800d550702e400b0300d884080e0441c0d0802060901141d00120b06220406107840c1140d0000a0580ea0501a0707001c4c040000d000190542044000100140036000d144a00c00c414006000c6413401c041400c07500c81580000d29400e80d4080c0144000559584102c01c0401c00c03445040048070283e800f040342c0030300c0f481c440c10300314044140407848004520110411154042c00e200419812500740301d2007100158001a0501e9110b11 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 207135638 1250 207134388 207134407
    0xa0609030518040501050306071d09090303011703190305221b09050f01090e030c030301080318100207090209061309021e031005100c050d0f1101060308040905100308 73
    0x80c0146a560301c007460a0050310b0340c1e101044201d84003403080351b0700340c0c00030400204498412881c20750074122208403101a2444040800d026240c00c6801c0f2490780e20020042c09001d0301e010f091000905040029840c040030000c030400080202c080800905440b2400700d10801441c440009044003404201d0380410b100317061201d07180401031101402a1074401c0040b84109442c01010311465103018a6074030360746000d541c5401840042d11000e0035000074445d80c02126402d200840c0200840c00044d5191002c0c102107011146c10000103900c150131081601d580190003240410407102840401600d451150020481521800040c103829402c0f241c00031801c3d0304154080c002001030070b42c40680102462424020900c810343d035070741c041b00c8249010071680c6026503042e8600c18032850083c01c62100c1d90b480a11781125445c140f40440e0071020b002c18056440042380c5100c40d1008002c1c02030503c0c43d00c0c2e0850500c5640150101140c84070000744090078150140300045500203000303a40d850200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 207136888 1250 207135638 207135647
    0x2030c240f091c030306061b140f0303040605040c0506120403180504020703031a0604180509011409060f0c1c0e010b03030705060118090c060e030c0418150e0d050c0a060903 76
    0x103c044020910340000422031611820340c0303103065001c5000c0c4d0718a842c283c0d101d624426012800104540c85030000e0000a51000d1002e14000d83c030403800800c0604062a0100c50520b90b44c02150040800380102c081c0100302000941d0019054108207018000040582c80320b07035075540216422a000090800825a241d4030010111035014401d0700e18904420401581d440b841c4910702e030351500c02d2a20911101c3c240c7c0f2080d0041e40301000061400c0043c9000a41da04d4202ca090a89420940420002151014420741d01140b80c2d40214580840980300728840146508404070f515500d400103000c41909501c0070700c00180040031030f500c0c2d41d203a250150340c0c1c0c18240a01e21603036881c400d40a1041c4154084e04079502d03400b161600031142440c00450f41110450102549486000500383c000e40b070380d102d00f030950000050131000c4032200b401c00303d6003059000403803043c161030325049001803003021a402c8200c0c0d1503441c000f03541e40c2c0361218051400b04240000b5000c1c9152042510416070030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 207138138 1250 207136888 207136939
    0xd050f06181f1d0a050103050a0b070903020d080304110102010902060d18050328020a02061c0b0901081011030f130f0503120a06050405060a05090c042102030c240f09 73
    0x46003041819548040c4d80307009903102840010041d902c051124400206c120042c2540300416140440800d40c0e079070005090800d40007419109040000706100c00d01180f414160902002030009100c000c01590204410303208a582105075030b0303559040551941c0e03c414104000710307041012640c035451460013480707066a00c2c04e66015071003120707c2002800303070010403211070160300241064200704000815281e40e280b08014a400c0301e50301e801c0c500300381c4d1340c103d42e85010340100e00040000701d461241080c110b6452601c015448a014010070400e400070b21402a409804e2500030300040c60035160a990500345514000d206000120300e030543d110340c00f0481c512410b101c11050040b0340c1da03001400221403080c0c1754950000c1e49400c003803006042c07880310340d500400c100002d1498503681d443c040700d00d42c024884000c5040c1480c254441980390410004ca998082250344582c211601000059800c0c2610011021000301103400c00c035950801056030040100070b40264456003220b40290003c019 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 207139388 1250 207138138 207138179
    0xf040c120908090a06140301060503150315040b0a0b03070504180c080d090605070809040e1603030e0a050406051c03020313030b101a040909060605030706050d050f06181f 75
    0x130b0340c400018500c0c443c001d0f4000040b1400322007031441e401c20100300c8090380f00500c0c80380000c0c0078505958945d1030402015840c946044d400440e10705040ca090004110090302c524501410324448803140d030b4021914404542e411200010408001c1540f950721409814024008007004000058100808140341c80c0c00803090780e074402481d1f1500426690703030040240141c02c00704c4c18800c2030120304150b84007c082600c0d500440e06807440c1c820300036048000c280c000f00c00140700400f10804c1d90030a90b42c1030001d01000c0340c05025060a01012441140800d400c100c545002c4820312001d15000b4012114142c2c041c3c24800c0c0d40c01d80328280041c13800d0381607841d15000c0303040c0300c3c0000f101902891840c07045c442e01904149410310b0000703000090424a50150380c03861307440c1000541654100400401410142c1b81c0584490b01d05622a0841300b002701414400b601e800100402640c84c440c10405000b0b1100d0407070b260b51541c101c5c40e025440601904019a8a0107001007840c07684d60072501e000c541e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 207140638 1250 207139388 207139399
    0xc1f09061103090c0102150103120c0204150816080a0b10080d09051002060402030606191d1e0601020d0311090a03060b3f10020a0323060f040c12090809 67
    0x1301c6030049a880c0a02216a0b110515000c0140000f4402c10b1400c0040100d82c6000120a0580c0d00002c0481e08492403903100da00c1141c0e01003054003c240480415035000e182802141443c0c030407402d40b40d00d4991001400b07940888000b403141c019481c89000a030202a0403605d50040018001d40100f0090007100e00c11f51140f46d40554183c4005038591050340d000d0301804258880505001d058405414100004111641d000c5084005000d1109030304184080b0500d1600341220603a5195100100701d58410700f075403007004050b07600051520034020440c500040c00c000400c00c1943c450090740401a03015900440000900c40e00c0d1700024032004045072940302000a21030b41c2054002007540a40c86080b885698041c40a07465560340c0020017000c080c0c40a06a80c0445081282d01c010035250101c2d0761800004502403038000420800028545119950704001000980030302c89000c0d11403080c1c2d190000320480c54807400b0028000c000f400014428081145048070746070704031460080c09103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 207141888 1250 207140638 207140653
    0xf0902030f010b09030a020907201c0f05031306060504090303050109110c150406023a050c18040b190311030307080a0309060b1507060506060c1f0906110309 69
    0xf8a028011a01108001002032001c1c1c4182e90a0120a40d0018000020300076042552481d1700680a4100b802a41d200c000d40b203c4680c41324180d90703524a98460402b001881d11104800a401100300c0313800c5280790501c1c0603030700c4c81880e00c840038081a4000c650054140aa07040c00c154041c3c00540c10b84074540400d2010b41142102c03460103008180700000c00d5403150b00c2001d03005800061154005008050142c941003030180b20500c0002c2407104080c40f01c0e04800c490500b40100051140c040381441000e0105040c049140301c440e0103040000d0a90088080040030507035580e41c411040f110001e41147c1201082145109109506210603906211f1031700004406d8036010040300e04a95000072a18240000d1080480087c88900070031114140d4a0901c041140da03900495614424213203071082c0e46004600d13050341603c2018041034060700061145508800003c0341ca02044070440c80c0051500103400c0084000d00016403000c2d010510b021550754401c0b00344002184145080e100701c0710003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 207143138 1250 207141888 207141899
    0x3080702100c09090207060204030c080706020607030204030b180a0b010902090102010b060a0f051c021603020d03060608010612060e01080102040302011115010e19050f0105210307080a090f0902030f01 88
    0x2e440d505002c00001034038450060007100060340c00751264500410006080c1030312580d407211151100c0c0c11680169000c00301c1000107a07410410300390b000c0d6051509600b42891070346c840d2141500a8040440c81d0b6401030600b007184010040d011519811807400d0310709580d600300101c001d5010035010741c015420100d40c00b80b00c1c101141140c800c51078a9079040095103444100f1121134020700b240150550001ca0480342c040744c64000307000200c20504c4000b4003c021440c011f498226801c000509140c01c040c010080e15410045440c1141c640d41445000403506800780e0005003640e0b0808496480c0c3c1c0c070004601c0d10815030181c07054a1003030b2900d1355101034143d101c0d942c1d4280c4413080c3c08050002030061001c135803040851500140305203002c0b90008402c0c01e602d0107880c3c007118080c6841107070000411142c034140c151241035105c14171031801700e11128020707107440e445682c00107802100b0004507880d40030b1040a07400c1c0106140481828050748800c04000a544203640849000c03e048001044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 207144388 1250 207143138 207143141
    0x91a1305070e190e07050706020309031213200105040f03050312072a0804150c02040612030203160203070f0e090c09090c010c0203010b13020909010b090108150d06090308070210 78
    0x3040e4807aa003d040e01c0d10f0308100480414005242c2010480d0a000780c40014029002031805031198402070340d205c403500071049810f41030003000c50360342c28020350f04240810001d44108a4403503c402d041082040d140e001a103452103650321904417492490030010500c440400a0108080f8188040f4160340b00d440c0c1c2168898015803010b0307004070340d801c8807507614040203001003c0b40d07224850050400381e42d5460b03a07102940c1d9918020120366000b032181c1c2185001d110b42c502810b42d4507001c80c6803580035103000707569002c5c6042540302c4889212090701556020010007005041c691151a5180d882d8090780c0c000c100166000307003040c414080b41c000917140606006104a04190061841000202c01180d4516081c14142c2c1c065688008801003603c4401500381c0e40c07060303500d0142c0c0e40c149140c02d1014440d0160300a03d104407081c481c00c0001d0781e00020403500041a0700058000442c00340004104d04e50303074100189054604034881040541100d01a03200b103a01303400f80d504198001e4940720 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 207145638 1250 207144388 207144409
    0x402090a2013090f050a240506030406060509190506010e060d0507090f080127110607080c0d0903031e050f1303050a0605041704050307091a1305070e 66
    0x8001d400c4101d035042610841c01c090003156200320840341c142960fa484480481c1c0300d1007031091115890304104607111300e41d0b00a444581516000c901132031032004001c2e1030a29554010b207441104004007003000e0017519002003014000c01049880e49080c0312a40c408040350903000009401d0826002a650358012031212041c40c501030001858803250100250041c0002401001444456030010a00200790f486000103410f500000046c802040015218236490b803842412048021501420024003a07140c003460350401510000d40391002450101c011340070310078450107036108000c207403205298098041000c50b4040e46502075160291490440707144015101c59011a0081000741c004c0796059006040c80501c000e003d91006803280e690500f400d640d21401d80c3e031035480b0418403003449240e41d403103c192030050790701c0b91809207444042511150a4400d01031100d98641d406806600703030f0b6244000d0400010f0442300750800d414407042c0280030a540d0700c0e00140d00801c00490703c3c01c0408064 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 207146888 1250 207145638 207145661
    0x10810080c06031e070e010908011a040c050c1501050a0e1611070302031204080d08040f1106070f060c09080c030705100c0b010906210f02090709050a0605030402090a 73
    0x100151000c1206121aa40c001382034801341d1800582c0030001c0d40400040c1c0e03802085599298403621044030001049613400d074108141d03a034907200000b165640d070b403500302070001000d541c0844d002c00c0003402520a80269840d44a060180d00b03044800c00c203071402403034103032082200d410a03034545030034810700c0c1c0c1442101e41e200c0704108018400001350107003c0320b8010307004210840e02e440303403641d0100c2d00345105e89400404420000c03800b48143d840078007045110303040c545020580d920740b0361145440034070034040203841103008150400700c03500c903002101c600301e0b08424000a564141d281410007444c0700c910010000b0341024010400d55001b2074400c80d03040c001001810480e0a0004010901052400060034402d0812458002890203586d260007001144400641d0614168a50814040e070341050240014500950000114070f00c035803072070258040d24260042c0c1d0310300c0c00944810040b500125482526074000052a40d481402188110701c00d851000240d1581d8010300242c0e5170080c0e24 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 207148138 1250 207146888 207146893
    0x1140906180301020c030f03150405040b040b09031608120c0418270f030207080309061b010e1605040f0926210105030f0f030d0e0f010204120201081008 67
    0x1d14040c0324404a224514200400051034000740c2144c070391440d4006010000c90000c08000c2150822800c2591414510180c40c02e11091429540c1c40782524401400241800794010203c2c00400080003900e0103c1134120403107948045030300301441a034100309a140d68902ca4030340014240314096081e941214136801890006550403802c03c00585450001002d100c0030328004410544410790b8140c6c90f803800741400e901c8026041c00c0090070070240e50403003001540104100d001c640c49030811030780a00400e904064900301c030842c83c40e01604195a03044c116114002c0f1092041d000c02d00840700700e038030840e0100310050f0039507030800c00e0360240701016100300220142100d012812030301c0c0c0500404541c003100d103000d91600d40d1100c4003031000101c3e826070500340e0060000f41010012403000d83c03c2540146480541407800a40e04d20a4020302d0012548a50001d02144010000d04800b030001c0402076407180d440d81e555aa50300340725281a80000d45c00d0000c214840040403070041030b162940c02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 207149388 1250 207148138 207148147
    0x8040302121b0d03020a0203010501030c080d0c05030f0a17070206090d0806152a01020307030c0206040f2004060e150a0f21020306040c05130b0d0209040314041401140906 75
    0x10040600c4090900f9000c5d8000d684008005035002c0c0300b030b43d0185200c2d8501200790350a0144403031070110301504880c24400c4858903c8041100041560900301401c0780f42655a04851001c42d00c2c840c0d4820502001250300b014030441d81c0e0003180f0540700d0300c003020484440c203d1003001114514003e48001d5013200d00110035181950401c00101081d40b00f00303c8261072036640b0401589060900480094565070110034044900d41c036014180040031a440248114145074550b05c5a146007102c00a10305904c502d11071030300044e0300c4c481c00c0185100500411046640710100d004078002125404845a802e4039024004e280555200040c0d6403100c680114550500103001c0e0356a44450794085910840f00344100140e8040106502c01c40c483d25404981500c0c042c103000104828402c40c3c074200b401c0070200c0e5007070b13140d00c0d09801045070102c070200704680792428190380694519a03002d220080000f00400c10420654a00314030031000c0e629029004c6101001400c140505c000007a4003640421 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 207150638 1250 207149388 207149443
    0x706051302122407030216120f2a210c05060105090c1206060708040b13050a080c0603180604120807090f050118050603090703210c03050a0207030b040804030212 71
    0xc0b0780a5000c07581e410300500c1e00b5840044843c20b02e6030301c10110381230300074110003078451a8840d2051003122a90b08140c0c005031602e24046802003114940c1a8504000d002d20405001405411001040100340200350603070207444003c003100000c100545407445100000951404d114021601c694091004681096040980340f800d0003000ba001c2a40640103100c0c03032010034500d60051004001c0400050380d208100520811082d28170f034805171060300340706410440b2540c00f24000b210310104403112a42ca5862804c0c3c800005075074086c504891151300d0130401000101306803024401440e0302c450089130b803171910840b10721000c6c0c01030900c28429400704001e07079405281d41000c03c2d0220b01d00d8a036070603122070108065070030403501034030782d680090320410038441e004070314500c441c07a96503100142c5041034101070105a40c684004040250000303907481f0300c9100f0f03c00c0d0310285512034002100da013810b0401c0c0742150420300080e442860351003420752101c5000202a5000c0c600e130903c03c1107421500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 207151888 1250 207150638 207150703
    0x2a1706130314041d0603010b0a0611030d060801051806100504090203100f0f0e1605010e0d17090907050316050306120303010e15060a020709090602070605130212 71
    0x14401c0342440850104030040c503071148050006400e102441c80e58540e5150445640320b00003130400c85c083d900d8040c1000907a100e5030b001009484160030b1010740441d40d048103034654800c10301c648030118a0800b01081841042d009103004000640c446000072540f4080399880e0f031001d843c11000511001001c1010741010381081c142903000506442e5004002d0030300a017541e8800400f0b404042e0760710300350400d041c000d02c10701034041034840080980340d1100012840300e16060040380c0c140065541034084580d1006000c1c01e00603801450180080007521400d0b546801100b400e0380302d0040f45000510851240050703c0c42410801101d9a030807412103415611680080d040b107401080031510781e840040100001c1d0300034117508010500304d15040e5840900854501e4800344242002c01002d800681d00217000802c2d034144500c00214012a85840300080c458000003d2071a030808040090804490020b0311010703009980c0c3e1045000001041e90310f030500c04009907844070443c0021001074440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 207153138 1250 207151888 207151921
    0xb010302071e050f0705010206010b0d0216030201020408121204030305040206090d0c1802030903041509090e01020306040b240708120f07031422030306032a1706 71
    0x6040062410440ba200c82c2c0941804403080a80c2c1d080486000080150402c4000350016540001c3c0c4510f50034500005d40340d00f010b1243c44400c000c042014203081500b40e04031020002000c0c8800710710026854042e011303420922800750180200d62a0040410b4128200e418070280740b070030450076940310b507010740007007902400585e0014001e008c0a000750b01c404030803100e03007800380500c205014900b1010107494084c2c41c1c03001c2d103143c0c01407050110500c0b001041d102982c91840c6410341529100400721842242d0785c1c004d01720141042131074002c03800c2c190b000b5401040d0036241440051003140c1071107480c1e00300546001c0c0c82c0581c101c810201c0202e0300080c1c83c1c1c0e14030420391a460480424030310303541c1c46801c1d990310760082c00d5030003842801501485000300344007405441148518101c1c0060f1604d0010742808003000d010f0761004010940300764003040c040e5500908044555101d06c130503104034284214a004000803d100101d2501440412201901459401000a0f940c3c900301510b44100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 207154388 1250 207153138 207153161
    0xb01050403080c1515030f010b030705100e03120a0807090509070f0c02030d020309011205100302010c03030f0c030203090106050d051b03031201030f0b0f1005150d1e051b0d 76
    0x84420501305402c03404105405583c803c864048200c800d00304140c106545a46140007582c0b400d0010300c80ca4501103484000ca407021241e40740c80b00e064013410345510700c1a52a4a074903000300041c0d0490414000e001c2c11920b68039a907400020b5490070300079203040c41c0c24050180e10281e8000000d0425105900c0000020b07001d01c0d15110030f880726408a4940291b043d06400981c00200324000030f035a100d04454074200e0310035021300860030018003401c1c010902c0d000c007074108000e87d1000000e05000e50414000f0319841581004541080300c3c00400a400a4400150b0b6500382800010381e80f0302407000100f450340140203001d4641109540392035842e070308040290140030a100c90030b18000820740090086018a504108800240c9020b07030700f40c40c001b45404030302c98104043c03040c00040d01c5113110903104180d031036894001003a00f04034690700485400820140c20080c1c51f00c03001646580654034424090824002505c440c60005499401905a42c007131800c1030203007001d00b00050308146980030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 207155638 1250 207154388 207154393
    0xd18230c030a080904050f04120e1225060f0905130e070801140f010e06010806010306051c05011a061c02040f090b090a11070605090c03160602060a0b01050403080c 72
    0xc0e4400840d00301008400282ca0180700803890f0481403c280c02040c2c0e028138041400011443e15942e01d100000345a00110100300c008403003000b03140c40e8603c04a0010390f02c001111080c400ba65400044150041d1980200040c0c4200c0060703100d020340c10303840314001b43c2d4503031001c0a4182418003014200010481c44030a0312802e10000e620824030140d0b001d0320392000042480e981500c074560000390042d160340056544080104104c4044800541e00b010b400d103090b03255921141b00480150445401c09517120071520900d41078510715805425040348240d00900c24484038400384003d00b2604502c0a41210081290006040b41a0503490641c041114014203082e1034080c4901c8404030342d04095031755950f80000541910f00101100c1c1d00010040c0180280c0c0529115034115003c2c0f480d00801143c0c5030004101000024441c000c203140014089640c03444440036481103010540c4151405802900045594000c003409030500d100c0068440758545461581e07051110b42c000381c0c84503410f0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 207156888 1250 207155638 207155653
    0x204050c040f1e05010e150901090e011202030f0106150c031215140906100e04110a0f0813080304020607211e030209090f070909020d020d1823 63
    0x149070702d5090006480d6142c0301c50403801101d44260000200c6030030141c1407000440090754541d6400c040d4012043d041e04c4402d80780c0201c1d00c0107882507080c80e04501340c0740c082c0900100d02c10720008041c0903000c1c003c408813201030301e10408103402c131191401011480c46815a4040610b40240c151940040c4245003103254040c03500720320310480e6444194900c000c1402c02c0c1c100030000444102901c00241100d006584d820018000b803441190710480d0014411141c2c80c0301569a501d6000020f041030900b049941e6000c9550014002180080c03030b00b01068604022036002c80d02130803401c0009510246080c50358480c0e808000040e0401603040301e1b0410300c0300f509600c40420041c0d8081210403911040ca807507103c0d82252511742922071800041510621800c1002d640d8070b2509138002004202c2260140c1311792004841c000040e40250050398000125001a44c04a0740181041e1b13011031400c0003c0098140356104c0d45054200c090811504070340d40c821500d4142428104001d40c03201210006e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 207158138 1250 207156888 207156899
    0xe01051f11071d090f06070f0c0c0b0703080f09030706020304141605011d090a09030c08040b030415060605090925050706062403021c0501090e010b030c06070204050c04 74
    0x400780c0b030fa00020401c0c00f60921118208890203c0b190700f004000b0003504412101e2503040c1d079140e800411700d20410850240e144111070280d43c10b03200c1103030070008010501d84c564000340c5065002d120200c002a01000010b4404884101e04c2030003001c254010b140b0f02a51070300c41001940000d00244c800c81e501d9402405000420859840c040e0544080d101000c0d18260024000380424500b07544250903070030215440b90340d0859100e074080d20300b8400082c06e00700b509003115444240700000b80281000100440e03e00d4890015601ca14410914560040001007096068032044e100c1c04001c104103004000e02d901e000101e160f4031203014560712401c2c1c0b19012250001000307054100000c210001409420b001ca80c2c004c181c00380200610000c8035160702d0030100351251a01c90301c0010183e012451110f45100003c0406d0840c0745804140480d50310741d0310141c020440c8010f440c003290318200d04241d407810702081c0c44900d003000411040c2840030680034480908001800005521401c03c404a035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 207159388 1250 207158138 207158143
    0x1b060d180203011103070905010503190e0304080d05070b0402060318100b040b0a050a050607082b0b032e0216030f09080304030507030303020903031c0b0102070e01051f11 75
    0x54036555110368a1184180c0189400c4991010402101007010020404800e802c00d92070411a0000c0c44e0907641c2c1d941c0d8040d400c1c100d000c3e0407a01c03e0081d0400d080003010240000203031040c0d40c6000250f409225040c00c0c01e6810344280c03070006103982c50080015015240c104007541c1d01540600407103804840310b104260411030303040356025503180d6641d03104a040c01c0a00c03c21795101000c2d52085401c0d4213020004040744810b104841c846c010002c0d00c0b10401c00050281c07813000502c01c1e150044410307000800ca120340d1002c0c90b0440c460789072140c90f0382c4628001480e04185c4003030b01c0c000b03041b10403d8041d4951071070010014141084d000c014140c11500e000400c00c038158003a0303441611904001d000140541001e500c2010141d10611083c80454030100e1884c2c100d9038142001aa10315802010a040d4003841070100011980c07889081d280d074601d9005600014401d80c2503e046035154004000c00c208280101500000c0c00d65a1992a00b000c0c0c06400f607030000c81c1444042044500d1584e071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 207160638 1250 207159388 207159401
    0x1204030801140402090a05121e03070b070e010c02010509030f0303010e0402030705010903080909130807060f0501090903140a0309020a0335120429090f010e1b060d 72
    0x2400102604010005011180001e2240b500100d50640c43d0003121400a548000103006080c0300e22240c02c00400008800c0001d10b5101c5042c01444081c284180d003907039129044420306507026840d04000948444c401d00c03801201e02016150740d40e40c0e02c05a00111505c0e00300c42c490b00d8041c070440d462000d40c2081003019600030164102c0c00326040c078103407050606161080e807110b4144aa82c80080c0300060218090342c110b10350135034444003107654501180384103132051070029081d400c0c0040e04009001142d0031044000b400c01000380403c0c5d0303884c6440c80480f03e00b050041c0000c3c0642050b2011414814018040c507078039842c1c0031403017007116000030b03111210985c412120880072100621183c240c50b5405c02502c29248007213025440420091a41440390b9542c02d01c16421071400502040207076181060601c01d105c0700da80c6041c0040054020030b10080d030701503807684100000303110403401c14040d0600c46080c0c82c0244c64085144a1550039112400d80d2065200314148181c1c5229603481c419003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 207161888 1250 207160638 207160643
    0x10504080d0c2613050105030c0703030209030a080a080f18250504020f0a030c030213050904031707090e09060402011719020d05041a0402150a0311070c08190c0e04081204 75
    0x43e6070b8101e211058040c6140e85e0301403418004180100003070920403400f540c03407040d05402d026039140801e00009090820f1142c0040c03c40401043c604846170f4402515481815030b984524001d40310713905201c1021a0034104012a0b601010240c0c1049022032080b05403c03458600ca120780548603400241a60896400743e41d100c2404605d882e0300300d03810300800b1142503141c20218074005440b20605460707101c50094600038114031000c0f4040600c111504801040044c901d4078403170030708140092480c1103034440c1c5886901d804001c0f8021480c081000d9004981c140c4420600303904880685404039401442106103890f8150140c00c4807a550000700044011100b00154910f0704d41340444940d000741c07022003401c009050070040107840380c82c40a0000101503070116180d9126070422000340c01c00300c0d8160700c0d042e00402e00f2070401094100c1042561014001d560b51070a49900403020600102030150981d511017500b0040c0b100701c000a160003c4c0100c920724030b85020054260881e0f401601d04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 207163138 1250 207161888 207161963
    0x9090807120e030c04230a05100f05030303070305130c0e04150504030c020f030a020418020108070f09051e030f1501060c030903020f2b030e010504080d0c 68
    0x811078103007030700280101203042c422842140207010039620307800c1600305800386039180f1490055a00200160181c40c454041c080314625105840c034014160940d080302504001c0701000c04c4403041210b01c14151500a070045095903118031044000d4003014000050240074060440d01113880003140c00b0141c02d1003031212003c0c0c2082c2c549000455a44201611b07002c0c644028080025809900d207194141c0440340340042240030700009042c0740240c14000d41c82842c01c000d1007600c41100c01c460100300e000762100742695451400941d48496003080b560700041c42031a00f4420b9281040904c1d0241e02c461480100e40c0c00c03d400404c1ca0b12085403d00c541607880144c0405401e00144240e44c090410b518061004c2d072030603540900034680e14003000b44240300e001003420b61030716001031803140960480c4410030040c105504068802e95001020390025489106001d03155008a0444088500c0c2d5801401e0340c10a085080b0b0300c5d180798901c01c4403401800c15404c800744980c01032100021400030003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 207164388 1250 207163138 207163147
    0x122b06051503040219260f19021504030201051e0f0c0c09070908070314030d14010305060708100b16151a0a0b27040c03051e0c03130c090908 62
    0x40114103261181e11103071709407a8040502c0884421413030b90011100e00044a000325665040c406c2c100007955a50011600c95a405c00540004051070201183c3c000d4070481104400000da440d010310a50001a0114004100400309001d03040c1c05201702c0301c2d440302018288101000d01c28802d0b441140d03117103481c0c0d104104050080c0341081105401c0b002c641040300005140c03890312601e8506911018081c40414038202c401d141c3c1c1801207600c88104140f00700145048804031b824441c1d0300b07000aa629119600010703000e10300491460340511400c0a56156003480c0200595250b8446040c1c1d031860340f0040c1c0c020000815001c64184c0506a040c00852000d228154150382d0444c40c620040c4150580f880400552011a0880d445c240c417070f80565840c0c1001c903a20202c0b880c10701000c0303034109140010030140355500d40d03ca2805a44c4044140c4078500384903c0705c0100c80c0058605000d449410400b0420303e0314054608a0014800e41d4900109030352803040000f1559420026143c80c0b40004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 207165638 1250 207164388 207164393
    0xf020705030607120b09011a07031413061205070207120602090a0314010b0105071a220b070305090c0112020322060c03051e0c0904111b122b0605150304 67
    0x110862004141c61b1010b0301d40c5032802d10402110102d04100d003101000940500b0b0500c288903961100741030322030043e91032005200d00c540c1c5001500c101c4c0c000a44a101940000c42d50b4050b040c014072441e8001c01c882030921001c03035070f41c945042003114601d03420001801183c854581d098002c3d80501e01b0b1000c0c4007a0702203030780d003901d001446031030411408018850004449900403488280780041c2c0030429540d00645440c03a19000800b4807602c0c564070341090400800c7c096540c401e03c003560b03040c04541ca80c015415a580c00c5a11503501081800702c44204801c0940d018503408009920f00c400181c01e4081100c8008411401c203486581d211801503ca05801d409800d0300440c021014007095110400054001e080207491940040b800140c01041e03030303841e500001180c0030f0f20f05c6560381d1005046d110010b04a00244240054015009150542d0852100341c030061010002c21860100c5041c080e8800400f5080b05280c03602d41d03030400400c4603120b140341c440b00840c2052145990382000d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 207166888 1250 207165638 207165641
    0x120f0b0a0b040501090e0a290102150f190b04020c010501030512040e010b07210f0f050f1206061b06071101020301030f03030213080f030706050f06030601060f02070503060712 77
    0x6401c480d404034001c100800c503a99016018108548600d40d80420b0303a221554040041d100500000c520381c0c1c07440d81c0390100711070808800c101200e026000c41303032108078407803031907004c20030072540644403001c01030010f03d00c1e00d01c07070081b4000b550a0940c0012511960000641240c0101c4410761103603540d0304c0103008100003003105060200500d1401d5003020314200203010a50740c140100c1e1003003030303000c01d1038401c1101e0008079800715004103642c8482c808492000600e00400009031000113504203100c3c101c40b82c060802c4500c852202140d5a03c0d1070021035041e0282c1c40302038640f58101c0e000b00910012011001c055542d6424104060320160400c090004c02c44030924a1000c00d0342d20400040000032809024064401c1e81401c0250302c030115000c000c403040c809580030441d42e004140c42420010404030090410f0361090004101d10b444000c04842c00d00c034110f40240d09030307000d60018081c00f03009902e030b41400c028610488800c00d0700c807000f090070074009a03442d10100d03050001d0081c800d00709 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 207168138 1250 207166888 207166909
    0xf0307030225050d081c05160f02280606140102060c0a0219110d0c1a0405030a024f05060108040809040204030b0f040219030809010f120f0b 62
    0x211101100700c4006031448182e107401c5200340c500c1002008030060421a02906507207003080700c03c1c0d00b100304c001e2107403260019003811a1440c04940c00d00300c41142c00380c05101c0d00041400302e54000d00c5419682011103844d90103103e45100c0040380101e2150004090340900006403505844102c0c84560300c0c0000ba20f417100140149500800034401520841d031300280044000d0303582c07c07000c202d51400d81081c0c1e0070701800c1030314180c02c09043c119117000d102c2c81c2442d04c0100c0700c54810350b000c0321a212150640310301540c003075036a25400222544001d032a002c01d01d5240c00ea2070858124000c0170100301c02400100980b5140180e104001020035556034038440254800b4910f9000e02c810316100340006c00d08400104002c02d03081c0041001c16550702c072a41524040d42d030225401205040c09a0300b84042c010891f800c0f4401d550305107804641d4000300c200c01080701e82c89101d00d400c0902160041d10007540c0300d92880e003003000c00d8140c44044d0b000750090156010003404000740502504d03046c810407262 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 207169388 1250 207168138 207168163
    0x310080d080c070b0601050c010c030504020a0902040b0f030601052205030606010302031905040c0803040305060f090c010903031103070b150a091802010e031203041b060f08060d050f0f03070302 85
    0x124041000384804a0804a4600d0390b13012184000c40d982c0e403001030b9090300846140c0f9080c0c0d860900c99000c21605540a04d00980c0200ea012480c0f6580d00302003403d80c41580500269030704203001070305880d80400d0203150407000504085e0704107140f420500f0700c183d45c07003088400400c3c41404100281c0c10280601c3d5041142841c06501d107140403501810b43c203e031a9400850720b5500c038009010301003070740c010101828140d4180c940e0f0360784c1e0f42881980c07040151200103a103070035500031807404400014850340100041e110721030314501c0c648055518406001e1035801d41d010400c43d150014070254913980c80b4110f081c88900282da01c01c000c2c811700c2c880300d402588a603880c1c0040c2224580520f005203002950904e00807118500d140007090600090700308074568017030044180700802c50340b10350003084960100e01c40d0b10080c5d603c06086030190050201c20000c40c4c0000d02040c0141804a4508442c0f802a4201c3d66102c800c0031500d0703c1e2090030500381889800120f04082015418040c2900382034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 207170638 1250 207169388 207169397
    0xb16020904052112061903061a01090f050d1e0602041203170907210b0c0415030501030c0b0c03120103030210140910020c100203091c032a03110310080d 67
    0x62901440f00291000b4003840d205104d00c00321520a0700e102c0981c1d030051503124000f80551407027914080b00c01810400e809022812024002c10100f25107150041210303c0144909d05114003900c03030408254207404d060042000c4002c624000c142103000a20050400301c0c400008080e540c10020842062450610081048071042c443d170721a00040a906954011400d10008810081d9003803900250348001455007200000300b24118500c100600111462a210035280c61141c450031404c89000740402044844001d006005003040c59000d8032200c140d110071285000c3d050300380303040a05000d074401c400503403281c450b440100c200e90040c54590301001812543c82c0c01c1039032090342c407580d8030a5859006580030600c0181804100041d0114080583e011941e9081050141d0b031241101401541c043c45010001c0d142d00d0f100f48103d03800c1c01e00748400303066601060017481c010042455400c204041c1c0380c80400c058a00c0080045008600c1c001181042502d004052800c00e8410b581c0743c810700 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 207171888 1250 207170638 207170647
    0x308120105190603020d0e06040b060a0506040f0e0c0424030e030a0801050409030e0a08030a0212030c031306020d140f1003080304030f0306120b090708070f0b160209040521 76
    0x4070b0300c2c8001c0b815100181405a26805040d10400040081e1000c0741c44030b118401c140000d1084a40340701e40202401d49400d1905c42d03d0b0030601909102c2d0340304100c041e0403101d0040105460350700c19180c100f920150580d140a9458488000040d0b92800c0c1c0008418070782c503c0352a00340c151045060309045a800f80d420401c1c610030140c2010414807034580207a48580c08130341018498165000e00210013864070b0807c0f41c8807059261307030760440c9030140050710401c81c00441d92445070050340e10444031420381510f55a2061100079914000d0582280d082c0d400b400b0114024141d401582c0c0c0743c0c8201d03610b1000c2072520002c2130403541c0c0d001c1c05c0500619a241c10500c045601381080707961054150428240140750320300c080b170003044c4940c05014421301d0300010108110015810780d003ea90035800721000951642d2200b40c964482c1d10909c0c0690103030500400c1014220009080010700c5010303e521120415004140c180340115021140c0b90000e40b42000000305585c4080000203460740c0c40b5090 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 207173138 1250 207171888 207171919
    0x201110d0b04020f0c10180f1401060801050a020703170c0301050d17041502010c0905060301180b0d050a0512070317192a02030c0307061e060308120105 67
    0x2512589802100d0303a6211880010030752143d80403542500d15200740155110444581d644d01c0d0500001d610741c149080404101d540302e100c1034030380040303030300702c011011100000d175140403039142a1404025039548684002450050a00c41d10703201e1030201c074025903910700c07910b80104409410b4030302005500c85542848490280b40040c1d906682c01034a602c141c000c0e10341000001c0f40703450a421582464000b8010802a03144401c400448907e50000c0c01800c01c2e2101c141c07030300c2c1c1c014080d494010000340700400402e044100c4185000555000c0050011141800b01d071800c882000b06840e45e83c00180007004011041109c840c2215120070318604041a56800626118046180c81c6801c1240300101d5500d4032540308040504a04880401448080420100c81003015036140503d10754075221000c100c600202c110340180c506032002e035140258640e9010b0042c04555980b00c0c1400c0440d50802135000c56200c0d10010f9030140030200c0d103403000401d842070540c1d0141c0040e0b0086003501e20ba000c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 207174388 1250 207173138 207173171
    0x20c1c080a03020915040303020109021e090a0506060904060b12010608070503010b1e1b06010b1c0207060e030c060115090302100804060216080408060c070f030e1503250201 76
    0x329255500d0007580e21035105000030044445c10b507110b1084080040d0003c101070301503115105c014800d0380e844080c42c170030115800c402c0c03149811031030704003a02c8800608108110751107564440e100901c42814501450081400c1762040d4000e20000d03000000d000850741c03e0800c140d4010305052605190510345610020242d01061143d80f80071003010401d080b078201d601005080785107132400036640b15481c1c5007002c035408132203a501d01a203004450011884943c00c04c00c40b50042c1200d45404801c00d40400000f00030352100105032025561904016003c6030140000c204807030400008143c1ea50400500842c40302c01e8290345024407100780c80800068840c45000280e80009081c0115070740d483e402d045002e84144020f28140a844c0f100c100300f00654a006041607a2040013168a250340f10031070300c1140d101e0a800902045000401741000034800c030030b51542d400c805410720704000b15514900c049504150351000540107140702c0c010701c92880031060195404148028460b4640c1c0411188 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 207175638 1250 207174388 207174397
    0x4050f0a05071a0409020a0c020a05090907050105070528030306050306040c0b0d06090e01020a08090102040608370204090c09030c140a120501050402010206010f03020906210a03020c1c08 82
    0x800310300c0f0362215203980ca0003e4082d200100141002035558500108000b064414160812481414101c00100c1c05040c860002e601c03070b482150003448100c1c2000015034107034001d108115070500c00c0ca0f551000031b401101e80c4141000407075102c0c202039405890094150b030b10030781200780a6444402080003240c109410481140d0880b60100c1d0750319545802900507202c2c0b5000076034158100f03034030000c1c02c040550041004011940d01c01d00a5100c0001950903072080348998000030b103144020450644185035503102c0410a80d010411410f2894500460480220300ca03103005940490200b202d18a207010380c10141d820303881c01d0300255065940305c550b59a61070042218032405100046815114208444042e28480400d810341d140c0b0f9150690203080120b03400c030300602956000003051030714104810700740e0303600800c950f15035134503501441842582c7e20b0b040000242040e8850704d903c030090084040b0103002e940a815031241c244240480c1c0c54645480c0d17808100d00c0c0c10180041040301042d038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 207176888 1250 207175638 207175649
    0x901050408070f02030c0a0806070f05090a06050f0403060c030f0b0301020a1e020c030312090d090b090907030207060e0d11190b0702160609050102010c0f020d081807090504050f0a0507 81
    0xc0043c1c41040c0042860001e10001c059045040f00030045008100041c071944034049135a214004d400900b681100c45000b02c520494000c0d044200c140207460161000c1c1140d0701d0842c3c9140d00740765403911400f060340d01c10400c1d100031a944444c2842e2401a600070303401d405400f030b4000e40c138100d842d210090848511880c038141d501c0e05541d030820810320a01005020500050441e070311150180d100e01159003090310f8141b62441801d000761059406213540004544d4103000050501e010703441489294140241901c0801d5800c0102600180309481031072400d5510400800344608586c0380071304122000340b91002e1a0340001c1080c0607442c010049202d0003540504207403025110303103009a1400d4180703181783c25210200200810710320703400180c0d00100d40b400d900074856019200710607141c4500c0d800c440801a00300c89070aa02182c0a40300d0940c022100700c0c03e01101c5c203003400c06079080420540000444589034424003040c13140c10031000310a810f0260140c20b64403a5170341c5190f512140c6100d10f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 207178138 1250 207176888 207176903
    0x20a02090a1803030b0a050f0a0e0408270f09010b04121403030f341b120e211504080c06010303110f0105090d230408060f090105040807 60
    0x1071079000403a0441c0600d000c2c1e82c140101012003a26019000d0650310509a01484a842d40000e5501c4c1071610121841f6015026a41040c28442031815188005005454a00042050f46000050f005060b88100c00185a45503006420f038200018591748100b07051294449500502c9030340318a00481b011034910801150b4000c91a02e00440c00a000201003000f5010100401802e00c0c41d4400a6200d8400342038000443c694101480200710b241c100341c80c2030342c2c001440d4052624010b0011582d00410307001c0444040003d49d8604074101d4100540000156001008114505050707200e2071840311843c50060300d40317040700001ca03070b07c4580001d140291003251000c01c0510481104941440311010280c0300c0960311707810040c0c01ca00e1001940320ba94450414020102c41c2c040c880d1174000e00c10070010385032007444010111150924036041600030440d0b0310600c0c4684698000070402000402c2c003400503454a1100d00481d004004d103010383d00c2c3d0400b030810000800c0002201c1c5038651100d403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 207179388 1250 207178138 207178141
    0x50c0f0a2f0310020a140a03090209091f020a1808160605070f06050705070606080307022d010e0f0d11010f090e040807030e0415031203060305150901020f0a050a091203020a0209 78
    0x8680344407640d0055090b4181c006003112846234580c011142880c0251a51909915040981c03035461303015400350688860303800d65542e10075403142c005019459807440e2003081d1502d02c440e03485400c010b6a004c03005591059030304803207842d5801c0c4500c000b015a030a06608250a82c0c0390300b260202d0804004090135560000101554081d82c255000c0503040303902080826114251309540c0d911005003640f150440c62510303407074070302c405010703041905110031000403074541c101c019505403503a110b8080c0d04c010510ba0441158079141004038803a4021041301c0d07000c40c0c3c0d500000d0074441c54600d20750100101e0300c60921040701504904c5030459804841241d40e824182401c540260346440c04030b9020f07091840342d1014119040d00c0f60103890040c005292041042c00050781264650303c0010401c0d00842621500704040c3c1c0d103000c1d031080ca03180016140c030031417001001c0103600264180d4046880400c81400040d4420340c15006090080304c5010f260f94a510080d641d240c1019001b4880c058610 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 207180638 1250 207179388 207179407
    0xc020a050c150c060705070c0e010b090904021302130e0f0702060c1c1407020c04020c2802040c02070e062202031f1217040b0a050c0f0a2f031002 64
    0xc003242c1060800f2802e0307a8032810b001c00014802d900403d81a101081412008903035640440340d401c0c1200d9017a04194079001c00c810a0000842c0d009200b66031051207280b001510300003a0000701814503524003807241183c24039603075000650001d0821004000948204405140c00103803071074100b481030210382d840e00c0620140b08001070b021480c3c0740b682400e00a800d0501c407514282d0320f0140107290240c40d164182602880124095484140f1031588844201c0403000b883d0b1030f200580200007004041a490b880d0082015207490b00900001617000034001c00c217550701c5c44400c80d00060304442c1805a601c4848418603842d03d12002c40d1120b69001020030060319070046420310131010700021402a0781d070382c1003105540481220a0354090b04803203248107a01c1c400702c1114143c035400d000903802c01a00d00011511500a01104211445a0086441c1180c0204802c06030148070300307281100000d64420b9034849803544802050b19840d0150f06141076a0040742d061002da0146c2d000580f190301c00d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 207181888 1250 207180638 207180679
    0x302150c06131127071806030b0a1e060801080c01080a0515040f05090d03020c030f090d051203061806101b0b0f040201020f0303010f0308090402040512010903030c020a050c 76
    0x8240355200d0641e0080f000210b04090810004c1c42106590101541c2c030284295a821013071514584000c00002003070017110700030b074420111b0300d002808041c1308544404000c0048543c08083ca503401010140030003000b60300824440c00740140d0409031401d414464000390000e14003400c1d550310315842d000011009440040548280c080060081c04040307200034804008003030603a0012441c0c01000495010207000f8000c0f640341501a400842c91321b0b406062081c040d40140049940c4105601820008588100054152030001b50101c82e41c07030400004204100c500c40c4d4158444100d00801c0149680d518210122000750030300785050000e070000d500c041030ba100c11500070a030010f60b206100202c17030700384030b12481036200380c0032642c9040314000741c3e5a80e404244522205031900c0740c0244001804071016020898018002604264807000003801300010250204103987d5200500780901d0b5050141001c01001c50015001210281d1245038442c60440b881902841c4040700000880001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 207183138 1250 207181888 207181913
    0x507111f090306060b0906030f07051c0204060e01090b120a0e1b0f03070e0a0b010512010e0f0f010f0308070203070314030c01110f070201110c04050109060302150c0613 74
    0x40c864014519902103014090070307840c0c007040e140c1c0c62a0800108524181c682200c3d03070350310001c01e0303182035075140e10300d01100d65801007010041020030b01a44070a170a4417091002440e00c030701c1000da200c070306001004207144800002d40341000042082002914484002c07078070a1210044541059660f80c5201c6010b44100060f8045902c82e030704d01d10845511340e0f4481b09010000312980b20641e01d0160803d65181418010180140e0b00700000c01c5c000c0030315910100342240d06040c03c509001014200700c0908400764403c0251690007020808091281000c1540c031000195031070240394104114008062242e01008044940c0011040305564080001e20029580b080070100402e0301c0070210f0751a42c0006a07512100c1d1f0800c002161501e00803000d07a548615400d06050514425400440c0d02a8040550101a01664451074016200e501816010b41150f43c6c0220301c00389140705009503400420711300c1848000a010b003a040320000302c4c0303681d0800d00340b0181a220217118100080940e05c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 207184388 1250 207183138 207183169
    0x40b03060a1809171305120f16150c2001090801090623160f03150b040f050a03020a06210903120501170c0103150906090e0d0f050711 59
    0x66101404a5600340d540090000d1131007848154240300c09030020941074054010001c6140c01105414401e03030030248100f100b1403003c02c007201e05010b108000309081000d280c0c0c4124460015050521002c2d4800311107420408880c80c09101c0d2240030b0b19100b1140402c0341040401c20508152141030783c1c4039211301e00141440100800140d9800e150442c001c0c94030b6440c003180011590040303a805100401c1d020704ca44030b904001071107164100d0086614004030b040e03240500d44c4e6141e08004544800c0041c101812811135031503503c1e42080c41d1403034008a141c3c80076204480c00c101c2800140c0302d96000004840c03650509994188110f250403845c04c0c40406c0c1038091a00e480034804c00d1503405000030445402a41c0d081100380d80750310805820010301003400304503a1181e4400c400f554481d900c010600b40755a07201c40340f03ca40318403010302a1806e6a0080e0206070f110310680000007018010076070000d60a0400d0064001205009482c034014040081c04520b8581c15001c00394544131200b544101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 207185638 1250 207184388 207184409
    0x3080c0714070305010b150f0d09080a020a0209100305120a020703080c010b0a1401050a0f02031308060115050a0819090209010902030a0515010c020f0a0b030f0414070b040b03060a 79
    0x208030016540d201d251100380e13280c1d030070405000311905000d54014041224501c5c0310385044014803443c4d07440d9200c5907a20140300e90301c4417601c9c00b284045000e044da04185501601105220b0b00412098900103052418146d03482d000c2040001d00009107100401d41800b410f5440304100caa00780e040214581c80036106002c00110101510010360100c6030072001200c1742c0d48919240c1c000100d000d103c1000440c0410020801071620b14000c0340044100c200342c0c4101e920700411001c02c1120829203a02c020207940c414001800221003010b41c0703809808076450001d04001c41010001d01300d4070040c1540168030541c00880404c81c00344e030003501407150040e111042c0d035695900315074020742c000c5070300c1d4103050314110119007007001c000c199904960050f560410442ca85408000c0300c1500341c4641d5500c0414068001400d815a0003c3c40c400c4031a400c2881040ca46820004c540c024039005d0403901c2e41000006100c841c4d0f02d10166400e50b01d00041c03071516590751401048031410759070803625003207 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 207186888 1250 207185638 207185663
    0xc09041d0a0819030c05030a05100f180e0613020904050109051e0c0a060e0f0f0306070203070b01061704060f18060b010908010605090103060e032101060806011b03080c07 75
    0x30156000a16143d6030401440302c0c0221915012030495048548410029204001003400b42d5019000150410485846440b01d00e942d101e15644040e11a800004485030310303408000151150311903886407200710310141c111440d00100d140c8191700f018a00170700c07911290010509100c000d502c8440307183d9101e41207070004122030700813044520301c0030b01d2020244214070112115042a00c0503008440701131302c41403101c1248400300700824001030b9030903400c408191042c111982d01080a1030140d20f90345c014642c0c4601074100b010030900143c01007403d00c040c0ba103071051001b14010f009540180c01c030400095640b28421000003601d00d13051820030000c070f04910740007401115400051b144500f622004040783d80c0300001403d035141d0348036040d4450240d00042002c00d900e900800901200d81050384c0c41c0005012044500d040d09130032110420102030014007215800602041e0085801d00301804c1c000c042842e40d51410600e00c2c07006041000790380105101c090a90145c402c1d1a920880c1000380 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 207188138 1250 207186888 207186893
    0x1302060c1509060f0a150b1804062d08060a02071e0c06080a06120807020f030a0c0306051e04021201150611010f0522230606100302030c09041d0a 64
    0x2540404c1d11004409080c100206920b2095481890201140c20309500c010518003c6541c42d41c0d0882010141403100100b100d040c9039640748215405002240c584680600190000d4904001c101c3d01002c815545c0110078040c0401c00a10903034009081e60f03015035a0f49192908004913940b004450074110303044c1f003a0f9410807a07107181100c107484032603903103d4040e5104005002520301c0f0344512041c0c0480751310307490042035003800103025060016042100442844010924007012014261000c1c0968801031040007854041e041d04260b80020701e103000111400c0c26078a080b00075000a1283c0d07000c50603106040310a4102c0e200d200c4030140101d0465940740c00c0a09101401503444495501c0c2c444680061070861007203130700900e0100c158100400b80c0c00c40403982c0c240d00c00c4041d04c01060780082e004903004005050203000035410054030f802d041003818070042c10300051300d0409140c01402007102d860803240607141d0f0541c0440e8041954031151905440e2410081c5031034005009881d5600c05 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 207189388 1250 207188138 207188143
    0xa180f0b06010201150609060c08120f0405011427010912020d02010e07120b0c0d0f0c1b030503130c050405041b0f08060f07021911010f081302060c1509 67
    0x318401c2a0000c3c003e22144441c007131000d10f814010500070a003080300c1444030b18860360103000300138410554985403001da81d61040740c2c5241100c80304111140030080104200d420700a100c0002c0c1c8011a406c030a051615056104040c00ca00c0a04c0419030040301c0f101c5841c003500205001034002c038242c0c814542e10301000b51104448020a0301641c00c250f01c044c030161000900340100c4482c9141078009801e5507a81010a020140400c0441d50f000d0146e020a000140314404103801401c0e80002d110302ca404c0090010002c0500c00c1c254a0000750203000880d4118046980c480aa8108001004001c0c80c02001c5405c15400064010703203000e08120411101001c0300144103c402e1803207407110f561f80c1001440034445d0040f00744a41014002ca282810520211500150f560040d6060342044000b0340410420f41d000580da2038045500c1c2c101256000208a01111540d1a08a48074a48070180d040c203c0c00f8440300a00035100040c1c6100310039020311510103450452802880c0d2420082110369 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 207190638 1250 207189388 207189391
    0x200f04090303050703060b030f010302040213081207120809070612180c1d090c0d1a0406050f0604020c0c090406020f0d0b0406140904060506030f030a1205100b030a180f0b 75
    0x700800d20303107403021840543c0ca5003500d10270b04039a08103c0d4560f0841c0d0038800a0342040e0404140381c0070005002c104a901840001c030f00c40b140c05d403443d46410f00e80c1054084110107031002024040c80740c05104602d580403425009942c1d00c0d0a0241e406440b084003840100400310580380e8501c0c3c507081e00c00401c01584202c0003110007407410400f0303200c00d041000c010620b00707a54140d01544010008a92820820809410b850182e00003880d0a24400c0c01c3c6090312000701c4040b103010395600c0403c034034030b00c035044a02c1e0021003c0c2c07001c6082025000d06207640d22540039507188110100c0c80020200829034049550070066094070546500a451010002e0702e6040c620340d100d14103214001c40e0480340c50403400d00e030b420000c1c4400059100da4595500909029140e00d405028000f11145050010001070000c0c818540d24142c104e1030141040c41242c00c060a50610700701c0303590081105a104070181c1750465660480000d41c80c81c80552420540288240100b100000c45458010301803142d1105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 207191888 1250 207190638 207190651
    0xa020309100302030702150a0f0c0807020f0d0203040306150f0b0a0201060510050d0e15090a03090b0306010206040b070c051605010f0c0b010603020f0702060c0a031407200f0409030305 81
    0x1c0004080c46405030240c2c00300b15030300801a8840c203400754512620341d103029004601c2c41c20025810a9000003007040d1100e04101401040254043c0400300d035040000060151205003d4001e0f80002200207480344101d2001a082540303030140075000c1c82060680c9001070184040c034142d81c0c3d5585548003010342046d0131107800b42d480c1007000160ba0408906000c980101d6540300313490854251072142c010300c0c0440c204269807203902d8201804040304440c05004124040c024460006a440d004048054079009511040030910034400c26903000168180c121340d04c208200e4580c1d947c040125440411000007030703c9885500714441804003a0f0b04100283e48003aa201d0709401000e00c42955002c0d01030304000c040000700001089441d00c65400381c50b05c0c604003041145000e41580000d41c007500702e01c01040e00ca411003015641056000080700c01041c000500c814104165a1030780b4644040b0a2900d400414036004082095620b42c40c4141c080e102c0100100444200e50078000c1c0180b408841c00c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 207193138 1250 207191888 207191899
    0x928110405040c180b2b0203150105040e0a0510050403020f060c0a030b01110a031404090204150201060812030114150a08162d03020408030c15060105040302030a0b0408040801020a020309 82
    0x150444007002d03005240781048091b11003080f104000d015a2420035141a050754004d07500702a0100681e824070214040350b00d07070101c510083d410032080104551280c80820080d500080003640059008074002d620441290310004950fa540e0034283e0501e64070307100c400784a0040034204103100c244a80540146152550100b0003e05e29200560300030070620312100d5130f5030104004c240001c0c4250f00d909101c9507009041420170780d03200c2d4418141d03002074100c00120603804c40194540d980c240703c1c8100401c2210003c20980c5030140d1401d4062006008000300452a65947e080030740390b54180c1405881d81038907403551b4000410001b458194182d404050b504400000c00d203941380728036900410130071a0361022452000c4690050400b114681e40042419000e0200142201c814809043c05050041c0500440b4846036560b16204000424050500205000910260310002100e45d64158011001c41301078413242481000d6010b241c0c000c450a600000707000344a940d020015001c2404203941 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 207194244 1106 207193138 207193169
    0x61109040e0304050f090c03040b0402220c030507050a090e0a15241404060509220902010206010f0614070c09050a140928110405040c 59
    0x6040741c40c0c0c0010604000d2810001581a0b03030240c01c4442040c0782c50310011070090307404090809005054104005021926070714400c1804203502038240007079817144045100604003e10303081c40001d081801042c10980100d060343c281c94080d454407000d480c1800c048425800700140240000c644807039140000c1c0c42181c0c080d44c06000c10300e48404110b440f46500a120340034480c1c07400204807000c0c000d203034046080002c0c0c070180c41140c0381840e501c01c512800200e4100300b1500000c4d500110350b501c0394484040e9840f6000d954402c0c3c007610490380c0c1e103d40799591010184030302004120014210909050450700800304280701300c0304401e4180e192043c0604803032007141d0007003000356074141340910450b49a10151748020100c0040003030002c10080d42c80c850440e610140d032036014549102c800c01000381c03124030b82c401001d0803c100c01e14003810022001c103e60321800c0181e030740408 = true := by decide +kernel

theorem cover : BRFrame.Cov 207014388 207194244 := by
  have h0 := BRFrame.cov_init 207014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 207014388 ≤ n) (h2 : n < 207194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
