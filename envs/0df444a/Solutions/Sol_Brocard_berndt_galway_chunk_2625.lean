-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2625
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:16:05.295983+00:00
-- url     : https://prove2.me/submissions/da3c2312-971b-44f9-8428-6ec6fe52c5a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 471942446 ≤ n < 472122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 471943696 1250 471942446 471942479
    0x4020f010507050309060a180801060f0e07020d140903190c0b1e07060b0a030305130902031005010e0f0604060512010902340c0902180303030603150408070c0f 70
    0xd08001c0e04041c0d090f255a5620300601c881a8040c1400040302e101e6079008039081844015540c5407003910781d0321070081c14040c02d61071042c0d0b01c94503100000455442c4040c00c010780305000c560300404020b22042421030702c0f41d06040c4040a240010402c003c415103007071002d140c050340c921405030340404440c0b03842d80c40c40b40701c1e9105008420091103c0b0042c05054401d88100e2011102d00c1611280c0c2814890010710003880c04550200320000000101f42c1c110300074001c5a00300c0040891a030799201c40d840d0607444220b07200c40d0840d04100c018030056002c0e8011649211018201590000504005c03545ea80c1c0b06030885000300300c1c0070501034111201001094050501560290f040034041450f0907000000446400d00f4044062418244150040001c48002d504581c4034110340b07594900f828029400344032000840b4080c895695401d08001080701e00610002d0010600c00c1441c0f04c0c040030300300001d8021641e6000c1044000c000c28011040e00002d40030a1840c501e0a03403401c0d81c1d0040c1210003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 471944946 1250 471943696 471943699
    0x20a0807050a0504021207051b011a03010b01031a010c15060806100815390309010612020d03030207050304090c090e0702010c0915020a05100b09060a0f06030b0f060c010504020f 78
    0x40107072106c0c1941c406035041e0001000d05040d43c884805d441c814106281040342000c156280c0106900056114225a1165581640200a440a44e40044040d918505058002c901c18079105140552181c0d240c3c2223414050784507030f40070642900c152826540c00354041d070b0061740801c05019081c9403406240e1300404500d0014240803900445500c01010b00820030300e1011090b002585440c0392a40070000c0c82142c1c0c48810100c1c1119010340c0656400507540c3c403840f91b10f4824003040442070081010411a0001c1c001c0322001d00e10741d0304074041d60142c075080300d07180400c0c000094100c507140140411900d154031003071007241c10000c0f85466024000e00000031a0f0400a400600c42e030000460420343c2e000201080c80743c1002c0409038a031911481005000d8410324071b00b00e03505000e691081c0d001c603908417007406080d1210340c2001007200e8140100c4200e00c0745072404000d814003a502c041120007002c2c10401c0038002480010f5031581250340c4200312a5125010801149000602039000810 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 471946196 1250 471944946 471944951
    0x30d0603170715110405041503140d05190903020a0821030c031305010605100302120c04051e0414090f0c0a210c0e090d030b030c0d0b06010c020a0807050a0504 70
    0x16161503603c0c14400c51907259164550f40c03200c04501c000c158040742c019207806030042c009840a0110b940300704030984000da0380c1c840100035000545801107984515202c1c1035551904003804000d8803400c0d000c45140103024881d60740c1001005807202d8030040d0080c090b640c09040754284080c44c05564a0300c00c400d4444001c020002c1190003940e00b001da94001e010240703a00e490f0085403502031b004003015042294448042100ea0924552580040c40d800c03d845444903560b0710348402c4014036009600640b940300d0044a1010383e4030f0701408a804082100800c04251204074084100900800b952030441070b402c0107030013030840030041142100c045001d8030284c403154075217100e042c0810440d4501c654107004207040340d0f0070b20240c40c5080010f8418079401c0311481c1403c08143e651510089101000b190805001d1080351038003092040c1e5124001d003101c1a4940c0303d940d0f071a60000010540c0d4184807111070060302588440c040600a01903010007440500d00340000c0150002180d40014421030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 471947446 1250 471946196 471946207
    0x3030f0a0506150c250302010318020609090a0f090b0402090f01050a051002010b0a06030605150a093014070e09030a0f0c050f0303040c060c0c031e05030d060317 71
    0x1c0b6030b0708005140040c0041199103642d0aa41030030308200707807207580032002c9411904d6aa1019451708407082224401d8a003000007a10040e50507107881c1075414041e5000600740030030ba032142800d411103a8054400390000031051500c410000072204a4141500d46500c200200021402c0c006003464005003180b400095070340c50030740010001140c6008060041c0ca141c0341c02c02084e1b00035004200d40503001042d0104254036807070010000d28443c0305840c0304540030100d103a04030161800b2105c01d00c44554400bc42142059441358026100c0c555031207400350164140c20810750301c05c1c1c01c0e40c80c552081d049001c1c1281c1412a203441c9c10031907001440d03110a42070611224480003c00c48444000c0d40c100040b42902c5920140c841c86441600a84940542c000d4410a140040000c1d41300d40d1003450040c9819403900300480312503004000060849034220001e001060144080b007400081d4140000462801551001c0c02d54100132030803842691900340900400a2000038910346904001e000d50401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 471948696 1250 471947446 471947449
    0x180803090c0109090e0703320c27040f0804031a090d030204182003040308100b07031b020f120f0c0f0a06030c0e061207120c0e0f0d02040e03030f0a0506 67
    0x1881d00317100081c80c40d54001001c1c100b01005a140c4a2901e1117100350762040c15081d82312a403640f000600c178500c2905403000000352b010b8001c500d0840041003050081d00359031299205901c80244140984240700c062000100148490060350f0707184d40c50180321741c0f1904040164034030784841112010181070041c401030100ba00412081d01c61000e40820100c0d11110744034a020864441901410f0414000810002416040034030f907405680f2543c080030000c0d5076604601c10f1405404001800105000400d8281081032811090501d00040185111140420004120361004402c020007904a855030900d00c3c8002d100d101c4110700103860003242e8441c00070014014030424000d00c818503965149a4110310711814110703050000103440250f84e00900c100420303040303070203d5007000041c1c1e0f101e001c5111000c641c0101c500d070310b1442c1c54941a26010200300308094a00080c0550803101071250400136907518025905000c0c030103006035990b420035032050300712048000e000d20400350405007489000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 471949946 1250 471948696 471948703
    0x501050105090d0f080c0d120c27090c0c0605090d2304030b0a0501090b0d05210c1c090b1305040f0e0f070609080619180803090c0109090e 61
    0x208030100c0f00c035910141c29144c080030f030303603102503001e0020741d00400c0f0b00303448540001d4051020a0551104003500800f41603881c2581c80d904985400038030138980450f001e0b03855a04100c51901c203501301c08c600c41d446940c1c0c0000c17103a1600072200017a0b02418040c00f0b1014910800c8d4005006001401805d5415036002e0300e09100b080c603804c1c8041403440076003030031041d0700c050f40c0c040c0d5840007816100e81001440c484c09410f0a0142a10305440e00d07800550380d04e001d440410140d98048013070600044001c1501d0784000482d0740e00c0350b06140421850027103e2060000043c0408000049450300b6040d41008248074203a400650030108100032070480381d1800450a0111070040300d000c1009603403103070040301406901c1c21000031842611030722300084102183c10004e80b50305030b0322640784c1c50365950442d90720102580d10381c0c400901e8200a000b0944240c008480340c29800071040d84030f410342c0c2d82d09042075000311028041c42e08283c04038501c56a0010501b0002e2130006414082d82001e0111240c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 471951196 1250 471949946 471949957
    0xc090b041215110d0e340e040c17030a0507022b060b011d0a03020d08070f06051b070206032e0e090f1908070609150f0f0501050105 58
    0x20101441000201084001140030302ca844940d6400d0024140500d5449070b26000756942a00300380c141090340100c9a4009804455900c60904590004070113211031034035514003020101260501c4080410703001c0140072094019881a600380d410300389804e1010007440440014014140c04c200003403441654000103546286804032a0111b08030003a204040d5050801610030b02401d640040c08000c0c041a0740c00a21542c9080e280d2603102c1c06100e07150451001108010390380441c590300c0134800b5007080f980d500f030075a04c1031072014501403d0740c494034860054040c04540d0142c0b01c0f4100022907031010081207540a40070110b03420300d4000d80c009150303808001c21807c9211550140315040340003c488504080180b10042c4660369211051441204800c59a1110f1032241c03150342014040c0004001c51030039041041c001246c0099560038070640d2055400742c603501c1d207c11501c0003003803800080024480352801c0000da0402c440c145001a0752b030000e0f00c03000d200c1ca008010030840e40c000c8200c62 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 471952446 1250 471951196 471951209
    0x5010e01063c150f080112080d0e0a120f0f09140109051003090201020105010b040b0a050c030f0d05060108070f080c0702010c0b090303100b13090c0e030a0b0a0c090b04 74
    0x2d0404501141c0c1400007040c0d00c440c140d12495200041403505824007284050311562040841e40103140c042e25012020300c1210300018148455201043d00070004d0074003d083e003d40031402e8000003a8452a003000395a0a461546040c00c03407603900d540041d0941d400100700d0512a480420301030028008030803074810318001c1454407101c005243c3c4201050000751600801035a0003039901c2d44000c0081107218001c0f03000d58038080c004500200c40c5c2c1c00f03840444205038400f918100c61814101d40d160055900c1307440511083c80503503a1044a1406410b2031a4960000500c0b89880e400045c44103c01402940510030a00b40000684d54040d02240c0d0214400d402a87c2d074021510041301c0001c0803000c007418a860303080030b0040001c404030055000300400c1d20320031180e0303403910070f1060b552041c2a078099501c1e141407000c00c9140150303040503804502d94200800440744d010b0110b0308001000b001100c00003c11410400b404900c0e21400048038110301d800b48000d0f083c00c0c0000715a10450081c41d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 471953696 1250 471952446 471952499
    0x1b19111003090b0c25060f0e1207110613150e010309030801050405070203070204020415111513020409020d0c060315050a05060d061d01090b0103020c0d11010e030a080405010e0106 79
    0x840002c00f071002901c920185d40c20b140c0c003031041c02d1100c010f01070f0b00c0403070031340c01d042c070084c0c84001c4e500240c06071180030802481464256107982d00c00340d4003a100c1d10741750011014040003040e41c0086810300c0c0244031107682d030954000149001082525841034890500d82350000301e001091f8807c4000c6d054a9050301c00040c00d40790081c041c1d107940690a00258403034000603010640184004650701218025198403030b600c10051030f41c5480c1e22000180c8015100c88800155030789519452040c4514006000010343d200d2503004242e070514814401c0c0c03180b03500300d00c04101d40c031351501c0b031401800200740400c0a201e0800c000a481c41549200711441007101203404040b100070782e8400002040e502524000025041d81c1001e00d0200c01d1141d80300303992800c10402d0329940240219203000c0f1810014004c0103405007400d640038200030318101041d40d83c4201020f807d8500700000c0c0560315440c1c40e07581c521700d41840c165003982e43e105107124059040035803c010b0440e03102844011000301c0c6016 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 471954946 1250 471953696 471953707
    0x3060609071b03140a0c050c0105070521131211060c1902040f020304030207060905010c0b06131b050909091b10020109020406060c0b1b1b19111003090b0c 68
    0x1111035204001d07041030340c1a4002070f1541c40d0380c0c1245d4a030300100c0c0701f40182c0b0100c0803040015901d030b02401201030125002016145480e40100d2019040302205140c00c908007100e04640301c140303090507002000e4000d1880c5418050010740114040c000200f16080c903c0c11803d03900c3d55896140c1755070b0000405003c00c03100350442d51141c21140c0007421000c2d04544915050900940d10700344d61050300c004c03501e0701101056a500c03440c41d8040d455009064183d0b1038540c5002e11494001020319591a903a461104505000201640041c41c8409a450649920703605013080500c4c240a0040c00c1203610420107142502c09111006d0301c0450211a0f56003200f06904042c0c1c050260344000a611510f0f0610205075580c1060000710598000c2c000c81c0140d0769512208880018046520990f4081c240840b0b0305a1302584410b48804da0b07080c00740e9a00540c0103408004400c1405002c0b2018200042041207a040c0f001c0d070010703022107514041c0400c0d442c5403a00c0e400d01c200039210550f03001c800240d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 471956196 1250 471954946 471954953
    0x302031b0310020f070312020316110c0904050705010315050d0305070201050c07030f0b070804030804121110061a0304120305180303130303050610080c030a200903060609071b 77
    0x2003089142064401556514801c000b80c1c1300340d9100c003404501041d50f0070b076140b49841442c800e80307219904c80c9a0300c0403030355034481c0700340d5400c02400d241c60406e101e001e01c17201c019110885c105000b144a1002401c80604010014040e11140d1386508907087d1414020080c1d96250b18010341440d0301410181d0303841003d800125240c2c407950a6990300c03403041c004000304104404421442c1240200c09440181c0c0f60b0001c12503000c24255030160000e114000030601040c04490250800705c4c0e41d040900b401c4052007002403d060003034001610140d5905010071100303c41840012010a8180d82e00f07195241035940d8501e0307940107140c01c404260381c6400180000005100302c481e820034200c1169101c2c80e0000782d001c140803c04c2d00440010b070138180401c119051002d011664106207442c0c00465039a04404404c45400c01484040003607118247d0f40040420108035480c030304885081c0d240d840c42c0c1c1c0780c141894604064026800745c0c3e41d400400040c0340d4405140410703802c0001115074540000e06 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 471957446 1250 471956196 471956203
    0x1103120705090d031e0816111e0610082e091a041b060504090504060f0e0d020d0f12020a0201151d09010504020102120a260906060a0302031b03 63
    0x24092500000c0143c20801419000043c001105c030495103484a80381c203004044500b4a01590048040c164a940c40344030140107543e4800f203200381c603080304c0c90f80030400f5009441e9140e054507030704660000002e1202c0e03001d81507584000f0b04070007402024a8030751a04940b15500000b01400400c900c41c40415841038a150085900d03a9040507440c110081d80310005420184180c078202c40c144014032088002403207080c00c0b60701300c95543c1c55050400e0710b030400c40b4018040091040390610307a50f1280309040d03c400c0c807640c650181104010080c0041403c0d001c1d01d00004c104d04007043c0450b802c424031809920401c0c10301601182c1c01d0250702e8a1075084164050260f035102c00d20740c07400d8202c0110f4040c2c009840300c00d210760304140c100806e80b10302c0000c034200d607000d440290042c2c21414500007080b80c007000078018400185405c0c00c0c110f245c012185554841e0500102c851441d41c0248654203a040000c941c0040b422941014507c0c80c0d0740c0020b507240801c000155045d07140c43c0b1001030303555061 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 471958696 1250 471957446 471957457
    0x3050717062a0d020405011d240c070807031205042405071401053408041b0803030a051e041202010f06090209100237050a0c0302101103120705 63
    0x115282a1101c5250f400c0c01d0181d0000d000c1c0c0c900080d9202c2207401900c5160f81c0c2005880c0000e48070640c900040c060848043c0c840c00480210400304000414804c8410407200004007c1074010b00095429032803c1c11031882c90b0306a0b1001c01a041c08240304026103040e80030700d40000c1c1c51400d40c0c00c12420f201999580100000908106080b80b4032031800304040d0002441105902a2964880e5074001c000482c0c6404640820044081c0c412b03540c1024003880038140c019025000b060940c4141c800042e0882440d50440d0ba826000881400f9103610140156904803490303c0c1c0c0101c00b0004a111100108402880170b020440792141e200c0f8003a000390701c09000140b564000b07000d0680c42d0400d03036010354001d40c83c4c64001e83d070f03082d1518091440881c0e92440c6d43d0303801611844218000c4607124902c0c101e18000e8600d4990328203400d0010b80100072003034040f4812400075000c3c41c1303507004021410740044080820701c01105407502d52588080126208940381c16500e241944401c4012205030090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 471959946 1250 471958696 471958771
    0x315080607210f050108060a060311040903051209030a080f040809010815030f07030b0106110a030c0215160204050108031903020d0b1c0516030305040501082e0305071706 75
    0x5043c1550a4407096800c502d040c0c2c2e4100d0101c4105454140098048403054030010740342d104480e101c801c061a158001c5003c6074040e152060406100043e0343c55125026119640643d01c001130810b03415801a030002e80c0600c01c849c6814542c0b406445040361482588525410840201c0020b45054412181d14612042c080c0403115400c440c3d001140d0b40303100302e000a4894441c02c4000103a024801c100c6043d03041d0383d03203001d4042442d0942d401e840c505194001281d128041d141e560340600321000c068030b4083c1c1d84200b442030aa040d801400708032030040e0080304591700208000284d40c1c08001c02800700500900c0e00680d0350b4401480c8038001c5c0000c200715a48212a85540729004030720b150b8201c0d016001e40c003500c184409603001001445018400200032480c1404100140d46c09500801d41c440c003060f078444900d00404c2c01c0143d1000c007800003803400c60301c0c01d0810710600104000d06009844c1110001d0b04286ca1220840e03a205001094110400c03001700b09448490807000200c40c08418 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 471961196 1250 471959946 471959951
    0x6060a03021008040609080318010b06090109060c0f15020301170105100b0d1d0303041a01080606090a021303150605010302070b0109050705070609110f06070213051005061207031508060721 83
    0x800484404070401c1d6013409c3d0301030b90b0a00c44426494648101151204d59058480c03222075854108103542d40c4180503410f07549042c0c0c2d0300d0040d0101d044140720b80c00725a40d064005075a50f0422121001030750303028000e01083da1601c010800c00e11401e1452100781c0300302102894450080000c000003401c5c0c105400d036414040e43c4196106030100201440c090b034031598601032100008550028a060248500002a4414004505641050300380c45800403101440586401c0c40c04a81e071140407029402101c5103031180d90014818401c84c0701d4000076120904e820351514200e0707220040740c60b02c10700a00c51080d0b5202d000c20492130040040f14a0154419000c0c0320302d15950801c41440500c0d00a2140101404848007d403894041c04484515034010420000c0d40000440700c801043c0c002c149030f0141494080c0458a40e441030090240c1c01510141c00c805c41ca0414801000e0354251240e030701425407483c00c180719101c00400c84079404080c619199030002c40c1d212803c002c44511704c090300300ca07a2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 471962446 1250 471961196 471961201
    0x50d140c100f0501120f0b0c0705060405060109060803091e04061505190809152701020316022103040206070f1a01080c01020a030e15041706060a030210080406090803 73
    0x19481e04142c1034000100c008000030380c1e0b14480c041d0300390304007a0000d01d4404440c40c1c3e0000a03009214030b541140d0800d523007500700b40c20313030b983e0a1400360103485c10f6980c0da0100c0010400c21a1034060540506510300245041c50900c4000c02d1400e05c01c0390307a4580d00c0c00d82128007005074072250700c00f078000e161031002c04480c01c040a03030151540e805580c490b44103442d00a9418146c600410481d800780c1c1e403d10050a4070a101e0b602c03960841e0002d0000c0d000c242414011515595000030360398104030b01c0400059403424031446181c5040d00c00c2c1a007a05540004421499260380f110140d000b100e8503000183d96680c1e10300c0060013911891000610304208105a101800200c1c00c10031303d03010f04a5000310443e625080f410359038126a0b00503034010f038002145040020302c58012080c007218080c190b18408000c4103c1d2000f0b5070426000303502139030f00a080300c0c40e00d60003c1111a812210580350100c5d07450854021507010341d0020021800e1019403408201041111f0384040361241d000041c454070390 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 471963696 1250 471962446 471962473
    0x120d1d031002030f04060f05060f0d14031c050109060308071b1a040602210301150924021b010f030b1c050c010207091e420b07050d140c 60
    0x10109845c180c426910701408480b2010440c82454080d0100414055202039a201000785100c0111412141705441c0d9003900c8030b1031000c0018090548807110b610303071328820720740740c80d0100c410583c0000d2805050650400106000b8800c40f0200740d00702106400c0e01d5203030740e440341d4440c109070700c0101c420030f8038600304a00340707610f00c003a1003501c1d00f41e07003510350340c00e0030985404145407168031030cc3e0088001c00c010088000b025203449810307000c034103060318a503581740352084c0e004200b203d000303800e01280c004070a0755a40c103001d1059840d10203281c000c0280340c5940000c01d480400c2110405160f5100d500b00c6c4140d03144103050b00304490064907640c403000300d0f2418640702d0150f440218054426100042850320442c0510340f561090f00031038021025400d0307550390180000c880041070001c1c4400c0d8040040000c081c0013801880e00b10300c014000c400201404505007515480080c0804040c04018000750010800030800720721858a00d0505050031016165841600d050022621400070903d828 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 471964946 1250 471963696 471963721
    0x40f03050c100305090d11010f0f0b10230307031b110d020f0a0f02040605130203090601060c110f1903031110090803010614070b090606120d1d03100203 67
    0xc444040c1c42c0000505149801501a2041a540200160003182407111120321500510780d50b03c1001c2c0001c6982240e60b040c100c21224403501900803251107015140301410300028210a4604a14110780130084094158943d10702048840e4002c85000020449580c0b290f040265020004207407002c0d0024422405410380b20790305c22829980c0560b00c0c59a100500108400b0039104c805009020942010340d03e102d00c4445501c000c07030380282d0343d60000c5000c0d1075031500c1c83d0300440100c1c801a56401c6c80c50390079181c41c005034021420080c03820f600e200081d10030241c001218000399030380c2200121410000d01400d910202009410845400010a05078024940041900c800050300c20b4081d00d0040b40050703c1d541140504074032002c0004022981c81001d1401c014000d004a40b4240f400b40d54811580c0c0d94180c5903038031164016400d2204900c0c0030350500030306c44182d9008000400c2d040c0005403202c505103880d508642c0c44100d0740c5500e51000c1c0117179180c01c290460115070301c1c541014200340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 471966196 1250 471964946 471964963
    0x60315090c05010e030c01030e01150f080f06010302011b1515030303110424030209030d080402030c0901081c0c0210031b0201020c06060d02030c04050708220809060906040f0305 78
    0x4444071461800a0303254050800d490040b0300240c05820092507100054020b40451813150001c2d40d41c4042000d04400803540902c080e0110f42c8a0422131440d00001d0351602410b0304120005410a4004000517078110b00300c3c400c000d0600d6096a00c41c1424142501c40160144c1c0350a00c0500f072002484004080c1003200d02920701c070b51810880c107019001e00c244a80900d0150590b43e025890040810341c25801c03100860038068076000d49064460400f0900340041801c1910205902c40144000c524040c0303c403c2241070255a031104a40c0f501140c107550702c88101d96400c120500c80d811601880c8950b51032103007150050f0040340160f0700c0300d10060090484080d02400d42c0310812a0b60350652041c000c4403451041440100820707180e03201040502e64803204200d90611504032100916100e0303004061140d102601c0c2c0c1c4920745004883c0f01c00580040038613003041150486140000381141081e105140026103d40d038032102c449000c2811886a9004014003842d05c01c07000082190000303401c070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 471967446 1250 471966196 471966203
    0x20060f01090e010207020f0609030a080403060c0305150a0504020c0c09090604140d0f030b010903060905150a02090306040b1005030703060606020d0801080a0b063c0d0314030a06031509 81
    0x4a00c0300b41242207802c07800380060003540144000000e40c105e00d00340c0302038003203802c004080e10051030280d0340d55041a445a40708803084c81d00c0d90391034030440380c03d48152a4481d040300c2c0340c1e90f50b0006203800035901284034000c1c60701c6654085510791295404000c41c481c0c14001415a09090a254150071f0f0b03a42d404a070221103c1d40080100070b034070900400c0305000898141c030fa4031500743c0880c0080c1c0c0030b440a141b8281c1080745400740000450214064480d0160040d0301900d9001100540d801582000400c2c00c40d9007401006400c0b010b4130700203032f0582d0140e005006003400d40c8400010000940361b950110b07602d485898004030501806178082e2048580d40e4080b10703000445d0030001d0320145002d01c1142c2403034001182e00c0021a0b00c480d0455030001c1c00600c00c0807013146c0ba042c46a89003511200b070010868413141c5441c520b11212400300383d8008211384d0b2131200441690000d010361094001d06440c154080040b5030002c256801400142d40c2c492105101000d036118444000d0078a0035098 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 471968696 1250 471967446 471967451
    0x10e010f060b0d0509030d111305010f05040e09070305032701091a0307030905060a0b09090f03041e0902030424050c0405100905030f1c020610050120060f0109 70
    0x6160605003441001c0488155112040c1058410b0b0440d000628005181500d20701041101c80700e04099031042e8114200108005e03900d500342e006c544808049950062030611102c0f00f443d2181715040400e441c11128102140b003107903601e255042d410900c403544000d0a510005c91035041e2020103090020041c1544140c2c840e00da0381c8500115601c41031485440f40c481a98403512003500c00c80b4000315401b0786c1508004c0340e403084642d04c0f03070300c2d042040303918281543e42c1d88448807013850440c80c210780207a1084000d21880500c5401c080d1640b1662043d12008000705100106400103424040028000f8071801c41d12840c0a0502d8800c0401004680c011980342e512690003911180c030400703004240700c5030960309150a280500000810181c120014007000400000f10799504100e0840b00c84084000b070702011990385ca828162451840590096400c80390810181200410003481121000d29013242c0c074003c003007170f4001022007690b83c41841d40580c0c4200b1114441c0c2e413600ca412211881c808 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 471969946 1250 471968696 471968711
    0xf0f060f15060d09080702090c03060f12070509060316031b050618010e15030a060302033f0c01151401050f040902070825060b041413050c12010e01 65
    0x6142600c400c1081c00b50300c11030a00c0440c000c0b5840e42d001c0242c9512845c0128502116900010750405044554030034030000002040340504000c0042c24120313409940400d84801c2c000841d54650146004150048251000041d40c1359810041d55040c02d1500500e040b002e600c0342000855414400c5803100c10031641000040c060502008507403954448829010345810208011100c1030502c5081503400300c10703114540c0020702064000c50080e00d0b40ca40009920389544181030428101000e112500103254041c000203032400008050920350200c0c0502203010200d1451080e0f0058450102d0b1642ca460403081c10449a000200190b0380c0c001d00101c00c54907250b00448140c4244103004907160414802000294410b07000340a59a200e0700b1050309151000c1e5641c1c9080c40300c1c00050986071b06041e50001071117028803400030000c805a034103001900050074415080e41001d030003103501007a00d00365a800d012080c4800f003408407000b02104000041c1d4840756010348040000200d4a5103410b05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 471971196 1250 471969946 471969961
    0xa0912050f07050a0602030a031104080717010507050708070605070224060a0504051b1c02030c0a110105150904032a031101060806060d080c100212102103020f0f060f 73
    0x55504c00c132546540210314180100100710041d000e40700070140107410500001c5010702041c8144000b5240010324401c910540c40360300c5080d81d101034800010302c43c04018520200c1d828100715210690000b00c0800c85450b001c000728540350032041c00c84400c024510b0b0041181c44620b02441c090b07101120812402c585403c10081102c0d825a075404026400800700801404c44101500480e0f04150440700d03000d04800351003040e81d00450b031581d81d2443c00a4600714160300420100540d0380c50b0030080205e1310301070b50b29440303503000c4003800352090303103054001400c1510403480c1701103039011003000517414011206442802c4c150a0001c03008207000b1048052b0030841441864101c90210008002c0da403130340c0003480b49000d0ba503101903540680c20000d03001c600d0300400c1222001e0254040061707480d12002d115016840700030b08141c800c070080d98410400d540e00d4040c1008c2c2d0074074440114824046c540f40503460314854900aa5840c052000c01102e460404903006208030000b042c0501a50b13140c44 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 471972446 1250 471971196 471971209
    0x21030c020d1b020a0302042c0327060c0106091b080f22050312040c14030a021203040909060203091c0507150f0f09150b01140a0912050f0705 62
    0x144018000ba88150980e01c100341000c618900840c000f518501d507450b1242c0203c6c0640d901c10f09018150040140c0080c001c0000024144a050f0000040c41c1802c0d020f00c1003000410400c0c24103410458940082d6105603907220440c4c41e90704c1e4000081050569031740e14030014003007810480302180a070282d83c11161b0f000d8040c0c5445003548825400b40340c2d0700e6001641301b50f640044102240e0000340813580c000342c0e00700b00030815854440055401807600c1e241c42e00c8100e00b05e0b04041001c00301152100d1407030310001282140c00c0d078110f40203207024540c00754407032440c000c1d507010740324103800e0828a01c14849a0b900440c09404a00141c583c200c141c0040c0703054046603d03030306c3c10002d5005c0250a0105003034060f0002c8400504101055000b50f14103d401036174020000c80303560035503420141003046212642c045c4401c03080042407100c0101305001a001d0403c092200c40300d400005407010310305104603907580c05480d95031104844501e41d0300301a0f076a00b20401d028500c0b03102d105408100d81c603148 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 471973696 1250 471972446 471972463
    0x112020408030f0327070311060708180f0d030c02041107030c1502161202150105010914040e0a03120b090f06121e1b0409030f1b21030c02 61
    0x5038000c1d45410050f62542d11907a10040800038401c504402d800c6000b0407401444100694060040003414118240010817002140d1520301c40c4004000e0b6400041804c4d05980818030341c1002220321214082c045803189807a00aa140c0c0703d644080b101c020140c005407550005802602c00300b00000b041131514516200d40d00000d03010440c240b801400040c141c0d00e402810b8000c901d809802c2c01202642c1c0c0340a800d501a00303c03a40141608134480f5035504120302118401103079041409540b604002800071030a03402810102d01421031442603d440c1ca40101751040f0744801110800405400d00519001440507241c140130706224841c0d140c1c1ca000110700340114610341046610381c035440200308811014031402d5141e0b000e1081c040d801e418103904200204e8600201078203490901083c003210300344c4001e0754076118510307002c258000f01c1d078840301b10907040005041102c0100b00c003001c10b00d105015044010b1940c2c1c01032000840f6141482110b92208a032524140881030b06150705030b032a0f5655 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 471974946 1250 471973696 471973709
    0x150503010908041a090405150f01030606090506070c030503131502030a052a070e16080108060619080610060f020307150b0f0301051e010602210d0b060a0306030201120204 75
    0x920090003000146412107070300d10402040f0170310342140740d400300d4103582003103c02c064003100f0076200303603114205101000000b0000b481c080203098100000608000d140b800f4990041002048031401c100c48600e04401550300241100d45031081c80d04030118051b0140656000c9400b03058603010824000000d4442d914070700c2d01ca1a003040201a402d81d039101e03084420084e00b03c50348040c052210340070f1046c4405482d10801c03210051502261002100f061003602d074003009a03100040009480228030036070040400c681900815103058465031000f80941c02c02e403007501401040c0700d02d204000c80418201e9003685c440039100c03488800e041c0d03102e00a103040a030100c40545034021242942d94070810070041c009004070b150b00207840c00301c0c0c01c452044440010005448400103800c0b1004d51000c0d00502c15840141004494041808002104e046203606a40004550400110402e0300040101d507005480340c0e840d0050a4401130240484e880141d0208602600641c01000780303000b102d05442c00e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 471976196 1250 471974946 471974963
    0xe060a050328020a120606061d0102191112030307030f0209030307060f0e010c08060f030a1e0c1d04120305060a06050310090509030a030606020c100f0903020907031505030109 77
    0xa50103241078030040000001c0b070340400c804c40082100e40c58004011000c0303000321030006401c1d040c013002601a00d0344110300410304a0748c800c04ca025a900191400103610f070446c0491502440d0700d03092042a000c404201d030b02001d5214810803680300000950b00c07030142c541d130a02c103c0280b014032004034800d119100780c041d0800c001c1c040100c0c1d40781d04103440000d12408005031000c65800140c1c03c58540a1911000407031800034070a240c070700110141c0c0300100460261003070761a00e9a031050302e240c15071421010707040b912000f80107000c418041c81c0c00616625940d500d030813002d141810701600d8111011035a1488081e681e01203a81303c1e2150764410030f40a00f410700020f0800c6020b40d40b6400007004180c044e844039030045090303601806100e01900b1440300954440040e0342001d001d82c2c409802000031075001e2142414140d03502305103400035052900708810001032041040703030082d40941001c0d41112014062281c0e20717074154855140c1a03c3c1e6038a00201b075480b001014281e444060001e050040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 471977446 1250 471976196 471976243
    0xb040504350406020a03020f0309011710030506040311190b011707080d0c20060f0703020f01090302030c240103110d1223030f0c0a030b0402040e060a0503 68
    0xa0008000c02620215074120990860311001c071989500c50f8110a0050300154180c00c205901040705503100702c1c0d45009982407415540008000006d542c0c0c030b9a04d41e010703804c00305800c40a418038550145400c981943c042c0c3c40c0509026004405c0501c0d40345180c404c0e0701c4410007450300da03140e10400e990310000740c02183c3d18203051080200c880000c14119400385035000284c030001001601441c09140d16406c1c0320a041c3c0c1003210b1200c82c10900d00c440030100559001046d40e54030111801e5080b9080722545503001410100d251502000b2483d80640c0f90078030150038542c00001074540c8401c00011504070100c480d41445510b01900d8102d85095400380050000a060000a185a81e0301600c1c2000c03c00458444030703d40c0c908280c0c41030100d04041d15080440e052140d101000c50403c000191550070007450108800800915144ac1d10340d0100315603120501c0703070300300c0078107030034010400d645880d00c402140300c04d41401c0d08c10522034190444006198103020a01400004001010901d441d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 471978696 1250 471977446 471977483
    0x50712090c0512010f05091c02070b1903090203010903180801060308030a090f0c170c01050711010c02030304170601090c0804080d09020a0b040b0c060703021303030c020d1a04060b040504 82
    0x411030320f520304901d5480f100340c082501036170f03c1524401d04c1310380000d10070300d440c03250900b12482000d030b900411500445014004091a0808c5846a84100d45e000b088082c2d080313400c4000300b49059001394194240004d9400b8141d000e40070701109511644078802240d603d9644a0880300640f00c0180600700a01c0094501340469211000340c5004d40c00344848801996102c2c001e41120741c100c444203400703200a2555000c01001a40e452500a081440c40d00019407a0110750040702c100c814104070300003041d84c046407424010765008000020000004803405c0300007585400c400d0041c0341c85030745440000444a13118481d007500580c2c01085007440d0580142c0c61601074400d20800341d0b02b01c08180310014036051940c0050009100d8204e841d40c0359002c1c404d43c1820b24001502c080205401070004042681052200300100d030b0307050516500d51480c0b48003159100600b0035024241400c10780030818205a1411060711481c0b117100100b0407020f5001c04c21080b24800d03103001c1c140c000115498881c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 471979946 1250 471978696 471978709
    0x60f030605060d051903030506221d0f010e10231506030403030209010305150105040b0a03090602180316030528020d110a0b070b07030506060d0c03050712090c05 71
    0x40c01054802900e40ca48601c2c205084100700c0c0c00e01c031181512002d00d50307d4440e49420582c203d640c6c114008415541110b03800380311250015090365050107000e12080002407444035031000050300c0009000f00300072402400c45100c0e40265000d0b1002580c85030382648210381d00f001a007844000c0d507402c03484c43c054940100404098a105804041001990f40e003400307148118032994015030395200b204001000c0e550080c002d41c1007000f151884c00156a0094141c0b8190f90024403070689a501d5108200c000d82a540c4020f8a0103100081c102c10501302001d010342c10704010341c110303101941c10078111200f80b025440041d0040d04003c488100c4400b01a106c064054882e03e510041041c00e50009000c94120020480c0c0030081c0c00c0380e055203428400340d104001c000e0340204900b4544141c8504140e4000105100109952000015440c0d641d030025640b225050202c20025403890ac00f001d4010711060794400b01241080d6002c500b0321081d80a08800f5640c480c0310220407902e4501031042 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 471981196 1250 471979946 471979951
    0x14040503030409090203030c010923031903050703090807050a1211102003100302010f1b0b0705070b010605030f0c0f07020906060405031204150c020a0308030702010f020406080a0609060f030605 85
    0x4c6c18042013185e01e0506000740164503500f4040c030700b81c2c00322004482c203614581c49581a50f500c503410070b011801408907600e40404600c000c074180400d0756618454110700420309500010120107011a00b207040c0140000c3c00040701e8403600c0c2c41220011904401c0d541d001d13006007025169070102060f450340703101c148c02c05854456445440101c0e01038000c01c03d001ca030000c0380c0603602c0140d0181c040088d5a40109010400715440c24441d821034009095020318414048002e03010020503070205030014030403000c82c0e15140d007003482c0100c156161700c8014925801541d00100401020020800030380031041241d82c010980c000951410380c4a50901c5164030b001440f9580c0b158080c0000585074400380800c810313640b565402c003542d130760600c000061901c0703004444504005803400d000c030042c0c0718801c4400603642c0040c0c1c069141d0355003e20483c050b002100c00c4e6940c40b400810009803035a0000001c6000d035509080c140701240d01d6001c08001c840e0144140c0b9446412003404002080c00ca40c823007078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 471982446 1250 471981196 471981199
    0x30512070e131e020f2814130b0a02150c040b12060a080d121409030a050309010b0a030f021c120509030304030b01030503120a02130315021315140405030304090902 72
    0x51042406203c482243c104842ca0340c2c00c440d000840c520f00c2d104500407000707001500c0101a400404140c030080054a800c9400100f000c0001040d41000103070030783e000700410b5002c2c0c4542d5200a9200020344070746d040c0b00c005504d0904c1001184003210304100f59410781c1e460041c9681445080043d000c22048003410643e000311b40c0d090003140009050210b817410800b01d0311388801c2c03150b80401d0340f000c803422140302c0c04c4111140400d100400d4004000c94408102c249003141c1c5940310f8201c2c01c0d00400b032316101690b012407840000020403442c6801001071a0003268450f10384151007401c0800c02c0004035000f88089542c80c00b0707100590094002c1c007000c40e40a003c5a04160712641c900c1e4000800380c10a40c0c40e1b40c400702d002d5000c81c1540c14295401440e221095040582d6003036020301350013041c04010315901d0b000300e02e5100d418150b0b05aa8014201e4124010166a200416156030200460307200003d50002c40215888509604036011220060000c600d8245041d4054004107418901203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 471983696 1250 471982446 471982481
    0xf0f0e04031b02192303010908040303030b0a0b0712090e0f0604051e0406020c0d02070e0a0b0609100c15200901020307080a030c0905040c050d0b0418030512070e13 72
    0x3c21512010240f5401510119440341c0491001d51704030a901003400240714801d070b040c581150000350200e419241126414140411940d09240010b401c2d4a5a07801c4000c0400d408110300040c002009003010700b008180d00c0303030069940c8410100d80c01d203104882c001101c00305080490901e0a050740956408044107141304e6034030350411a052a0514152015540150081410340b1043c80a2061100c0c2806a00040c0207003880c240c4c03040e4604a006012054280d0341d40140c0c211034032414100c81a011006160122040c1c0d07118000c4c040703020114003603a00f076440c00541d221403d428450918640c4210070b40d49009110f60040e29103951000040504501080c0300b042e0004020001400000600e03072000308207004070300310040c070300d0041d6448a4400e90402c100d2074501c54200f411140f441c041e003400800e10145403000305016101d504003880c01ca01c4521903020906903c4001b401070081c035401181141c2d01c895070b08a440045046140ea800f801d60740344054640034517408100c5114100c0b424 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 471984946 1250 471983696 471983719
    0x40b03180f010f050901110c07031506090903110106230405090f01090c080c06030f0a05060d05072306120708070908120405041b0212090112060f0f0e04031b02 70
    0x40300d0940703c091004440890f251414400142420f0040e40b80f850a40741449040098602c24166504103d11000d00400d0035108900503a095542000016200c159824809400d0300d00d00100303402580030801d038895283c00d501190070740d01040d03031101d070600751400e00009a030300b42c0402c0000c01c4040d00c12520380c483c0c5580200c002d1000c0c081d2820483c058100000c00d030b490b1460050400d0342c0f46088074810703031003042002201e07414400d646800c5611044001020b940e000701041621121260141040c49180c00c00940c043c500301c400d00b1326801d150380c5540300304005d1046c40814080c0c0c030460406400c0841c0042c039407501c15080958009482d18141c90a0b90740e40b551070b414585040f080d4014020009400d000c58102801049840050300c0028a01070041d40c1000791a0008000d07034068001d00000d00441d507a104000038407000ca0041410840980e03282094851207070f00744a0f8400252310b4a000003201d003044c1080341d1059425440b2485080c04401402c40a0101101c0c12688585200340 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 471986196 1250 471984946 471984973
    0x3060702100c0c0f080304020915030627060f16020c0612040f0b0f0411180126060901050108150411060d06030609050604030305060f1302031e090304030303050606040b0318 76
    0x30780c100c0b1a0003905c06650b2428a4014451184002440c4c010b282d00c041e076505105840c00224582d0003080c0d1400c514186c0741d8140810400c2540917101c00040c401c1d0300c1071110010340928101e001704036040c0080416000d0b03e20580e110000f02c200d0300e9014109010440c00a2034400380954464405c40b011a4820155603c072101c07000251400c001d8070250208100802c10b004d888482010740c100d41001e02c00040051111544030140036108035100c4511819280c0d060320b1602044911413101a290180740c03903410340e40207240c2403003101c80d5407040c01c203442200481000010b00550704000717500c25400700803051040c00c0d404803101c1a852641d440001003c9840e620a9241c00c51046016086904040c00d006003540d10103007600744254840d80d0003a02540e01e5200407804101d600c5d5000d0b84a0751410100560f14a5002c0f003464403040346410001150004001041541c2c800d4500704403548945007400742c10302903400781c110865010008141c444504401e9000c000740900e00b203034541031003a60f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 471987446 1250 471986196 471986213
    0x61b06020a0329010206010e010503100c020313080c090115053103060c1403010b04031103030903061015020d080103060f0f060609031110051b120a0f0e03060702100c0c 74
    0x540b035043c3c02581203801e081503a05000c014010310446450480c03d5041c10000f9854003912085d03d94410f585104010034103000b441a684514000c0c690550115070b03400300307aa1a030b03201c0e035001c511981405002040410801030102c03611210703030f079905042c00c402e9031001c810008841c54035583c0f160309a06001807080c50030740c4440a10b12494003c00c505442d4070000c1d14210140c403502c80d43d0f80c5c051005004c1d01402130240e504aa8202c001c10402c0c6002d007000c2030070342c410291090b8060007118100000f05c00255002021192500044085904500700490b1034000e00000240015841001000400e010350000520030030010000601901d00f0005281102e07074a50080713000c66041442041400340ca201420705000081d101910100302004004295103c0e404984000801059841000c540304100c007103640e854005006981d62016100030b0043d103492020350000682d80f50005145090210712503002c0d06d1207030000c00c040c0074104040c030094280c05090f0020003200602031f44c080b401c1070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 471988696 1250 471987446 471987491
    0x160b04050c1f0305070f0e010507020a0b0301060503041a04050718020c010e25080d030e03160609140c03060c0c12070c050a1a07020d0602040e04030e0901061b06020a03 74
    0x52030b0982c410000006016520020010024800790224040030035822241c4189010001d190240c0e43e40981e1001034940c400c0b1790460303010481c000c0008503689030040011806180206500203205a079441c001c603080e041158020000d40141c94208900c132140f040106030780c0b69540c005403d01c0d10075088242191000114003106500501031280151201c500c14030081080700c001403003050600501030b550f4070850052a081580da590300da018144180305485c41d550800b095841043c00c1414400c000c1c000c41c04082e2800c450203544184060340014040700400400380c0545801d6a41c404c021449801c843c81c1c0b0400b83c014250b11408614042c001071210510400c1a185501d01300800d00c500725440d40c04c0388915202600c0d203101a007900030183d500681e81100c0d003003c07094240c0f4021010780201d44c050390154490000348001c0540024024440e1181942d415a51381e0341c85c03008689001c4400c64064234000343e07040242c0800e1254004023000e9403c0d003000300e90000d0000206c1008000c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 471989946 1250 471988696 471988729
    0x1081e07030c0f2d140c030904060509090a23011d1e030403080a1715180c0f090a0b0a0c06140c0904020c10051317160b04050c 56
    0x100c8000900550300412001d007540c9040c5807000d0010603104c4100d101d1502d10f0454440e4024201441c07a00c1845042e1729041c170348900700440d464804d0018960f5580c0c00040300c152040b42045000301d80c9040056001d4445e04140f00144a1023919459402003902d484c0d98000c03113100076030b000031f18028090190269071007442400e401200302110b14a42400503800c060f04008024100303002050a002040e582580c1d00314107038550f11411460180c400b004100000700c41d4070444001c0000448401c0d0600400200075105a40d09100b0122600c0c030784030f01210f83c1c981154041c00300341d0344000c00308040c1420300809002002140d46640040103141c00894101c0000342000c40503004000d0540510050103031303150302400c80743c20400c141110394003c2804280c06158041807113640f0305c00c100020719143c01e0107003040090f8242090910484a18203c064510391000210040650414400c0703070211805880700440c0b05c24160b80d0078010110150003521944102c8030500b22540c0c5217800c00001e0303241c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 471991196 1250 471989946 471989951
    0x1003060218040b0d051213081005041b0e0703110d0f05190501030201050d0207051c050901030b0d0b150d0b070c020117060a09020f04031406010524070201081e0703 72
    0x41c15001c002c1030ba0812a8558000d98004c4014030005d04005243c00807400b82000341d03900c03500e15620001c4a040154007660840c46103206081903008143d0089004600074880340714071f9140a0100c0c0c19000342441000c1c44408903000040c0454803941c4076039000707400781c0d0340c40b4508640c45144005892082e0701072031076555640c060042030381c1c4a0500c5005004401c5050007598034540001c5d0031805851524072031190006416802c0140c00d10504200a40d1848950140c1810790340081190300000300c3c09001c03a107010150b4020f803038424039800355a50b000f0a4840301c3c0c1c1c2c425500300e03c0e0741e582007006a005501340c40400d0004e84510310061280509030b940815064983c00018145c080248008941c4080e401c28010300f03444406000041e548800300240e035070540200032510500c903e07400681401040780005180180105050381221030841711010418103440150b4101c003100240c070340084008100385c10042d402030038115030001180d0380c0c015100a52491004030f2120840d2800002075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 471992446 1250 471991196 471991237
    0x8061005011b11040f02071a010609140a05040c020102040f090f0b040209030d0c050c1c06050604020f16020604050405090309040c030203070f0e0604031a01060305010603180b10030602 81
    0x50384400c001010b11034407204031509003202d88400000710a400b241d940515103400404d41500303407540403200c00c50b0380050304c81c0e80c040a10350701ea02c42410a004510006205000001d09600b03070607150160041c2c01068490064030b0401000003d20300b03422300030155502803100240e09003c00d000030780100708030100422200000d298002c12107203001410b51040c1d206015118cd9034030b000648421341c414609000c43c22224604021345440c5940741c44a43c0000010290000340a12031812000a885080140516220401000103034046c4070b01800f01c3e04820702588414000009203201818005022180341a841d1002305060312411200c081b9075074000a0603c01c80d05061050b501c55004900c1c00b10305605103c9001005008005040701c100980100141032a64840c0202c5009503800301e0054a11a00c032501030448030f0b42481000082032900e0000180c0b6800b030b020f00d10100c501014002500300407a51100c0f011a401390014003c9170341c4100110009055200a2020344010061b152404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 471993696 1250 471992446 471992449
    0x150a1401180c180302090901090b1e090a03050f0307140d0b19060801090b010905030604230d0822052a0a05030303010902160f0605041a151908061005 66
    0x110180032485003000702c1a021112246803003c28501500d904851544280e1140204140075007442440940004a01001e00210301c50101d91030031f88284e01c5060080c0c0c0c1d5240c00d012600c82c80d0303e2a018020a800700708403203042d0120001980d11115900304a51049001c1c00d140c02c0d61b400005032004c2180d501c101c003031424505410180c5d000715080c44074065841c24003200030000760044c801c100003540c03070303c6540310980c1c01400260043d180103403c581035443c0505000c1c1c50041441e0a4607002d00d02004044291400426101055041511050202c0d10390b41200e0014803004410050003d26061240740014018000e002c0225400c000701d402d46003400d0350015041e031740c0100c4c42e40709800541c02001103843c04025241140c824103030041c1c032180000350884815640d000024001d01c0301491610030488140d2142d030203540907605010380c0170b021406680040d0810344001c000c602440c40300703c04514004c1040c500304040603048a04a40e542c00d0407a240a40075100340c0030840c00d601c0103101f0ba = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 471994946 1250 471993696 471993701
    0xc210e090f0709051002010902190e010f080a200303030a090302010605060703020a0f020315010807290702150c0d02031e040b031f0f060206060907020708150a140118 73
    0x31080035405040c0507070b020784105024461a406180054595a40e281c001e46c01410940e4015202e014006048106ca1300c00500ca4054000412101130021403201030003142103040d106210000c10726651142c0710340030305941013030841c4104402e42600042d943c40c24006140a00640c000103d4036084d5841d0282c29a244d80e000355001b0001440005c0200340d0005038920819005220f005204480d4000b09040641100d5400f582c24046000080c0316200000c0007002c40303a40e82403401c03171040c081c1001e02d8540d88024088000e44000d02807030001d4900a0600410301c1e4480e00182e25010030030210606200c4e04000751005a0804941004404034060500c801c205070000120721b0581001c140702c6042c000505401c03a11007450030b80116101e60140003401810910094150309075035094001d41c0c0740c1e012079813280181404000705200c540000395040c2680d0b0110081d101e0741c1d07184c2c5038034030508000516081d51785444101c244070074020009210302900442c1445a0aa018843c12005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 471996196 1250 471994946 471994951
    0x210050319151a0a20070506030c0d02030c180307050d082b060611070308040b0c07050301020d050a2a1407020d030206040203300307052b0e0102040b0a0c210e09 71
    0x105e0360700c9041c010000380104594054940841c0d4071600c2c1e803a00e00174400940540c1040b40181840001408a12032842020302040f071811801801c5840e0000241521000c440c030400d900000780a0740700002482c400003070b10407501601680030070180f07070b00c0740d100d0345c00c0e6189226408141d03111028084176900c290380020780b282c0c0c24000d052151842e903c00403280b1540c441e000070840045080c5141c107006104003001840010020b5444101144a150041c40d0643e169400d092512060105c04c8541805070010b1103803109461004e00046903080d95448440d0155104112003040080c006940f4807241202e4580258010007551801d17105040c03034240f1a41841d100c1042d00d03206a80c0c0e468202032110004645803c003c1d440c0d85601c076003501c0c6401803500c441d80d03036a003030384245139880c482001103083d07400045024031800380010075980c00c070300c11400742c1c203401c0c04200301e401c1400d4015030a240d07a01d4881e480390503041021028400421a10440c10000100840c202920a24103002c0d1b281c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 471997446 1250 471996196 471996227
    0x15010303050c1608100e160e0f061c0204110d0f02040608060316090c09050301020703030f0b040212060918030c1c092301030e0f0a0210050319151a0a 66
    0x2014039080c0f4131003559800210001c0205551580c0000100d040140100501a04082c4044ca1026210b011480000380c0850340d0724011850507001138038628004031400c52103170400220043d025883c2c2c09020140000507440c0c00d000b4000c01c120301d00414144503074040301455110040e102c40c104007004101359006441c05101e648690751030400031074001001d41c106c0310a842c0c0010680d528844c02e40e01102c01e40c1c070181e403551022410b00185501a0000366203080020010090410441c0401c4220b000d48200401c1a40c00540001d03842c1c00c00310300c595004110721039480d1410303e44202070b915691040c03c0100f8150800340a410030781102030034445405103203041c1601e05030709108075011b4022100c408003280d001244420b501301d074000c4d403014a03a0b19030042510102c80c0c040040c0f41c0d4645049104134014044010f0008281d4414020ba81c0541c1c401c2d00301c1ca401d15640030b03040303020341074020b84400d0300341040c00001000001a041c0b4848060060406031b1214101d15001d8445140c080f002c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 471998696 1250 471997446 471997483
    0x4030c030c060806091503011b0e01020105091603030305090f120a03202a190c050a030b0112080903010236060313030905100908070803270315010303050c 68
    0x104c00390f56000d4006500415191a0480313107400e1900103800f40684d4810f002c148807032400358858269110200060004080e0001e00a545076118100c0d40d41d40c220081d0006c0329100ca000303000007272103a0006a00406200112820b90031440c180d542820151540031901080001d00d40e14195014001c00c609406a0440c1d2654018441c50b1400300e849541d81002c100e001c0581c50100e10819207003212008280e04040b074103540f003600c914200c20302410b20305941e0440700c804005200e1900c080b00d541a41e605c030035010300340c1c0d1900014880880b25024100c0b030380302060200c8084c1d92024400750641400e0407101803002c00e481745400001c1150880712480107407246103134501c2c9448100c126074202c3e1400040708840321860030211258035054015551040780b10580c078401c00d81c844804c1065a40303403010340c0d0a04c0e9491600b55034a115110300c0d0a0743d601c074000c800c0c2da5010a00d6070b8091009000e426111103035204d110100600348240c004802041011600c2c1030000e0042205402c07034490600007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 471999946 1250 471998696 471998701
    0x90816031b0c0b091306030b011d040507090917070302100506060901140307120e010b19030506040201140f1204150c080f0c09090c090306070801030f020409030203040b04030c030c0608 81
    0x4100022195010b041ea24010005042c2c0441c0c03502000010b05d080ca0b44010000c15072640f0704480c45100a229283d03035640c05107284103604001d10f805038002c45d404002400c0d407510b414a014090400e06109803808985a07980c68012440c62004189451080d03025280d01c1201c0c503d040d04131030f005040741c0e003d500c1c1404803041a9030803140225085a0284030140ca980d540041203610300c0043d1042c02c2600d003080700074140348005400840da115011141c0100c580c00b041649070015a143c800606980c3c01000420099402414006000148280c0052420103124142603240c1e002618028407441400f0401091003a41c1515090703a400e00340007440b18001c04200201405001342918040080003404a05620800c80c01c86018075009800010185880c00c00c0c9030441d0000c8007450300074025440010215885511080c0c1604d03400034070500c1d0583d15400b40070080c0241c0000f2000d40c0b0080001044001034074000d0f000075480755000c00c0d000ca080d842c1980d62110160302400600a510f000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 472001196 1250 471999946 471999953
    0x2010f11190305190e01060e06060313030e061204030e12010c05120a091434060e01180b1e09031905010209040908251707020301090816031b 62
    0x1841c12001e1981c500071401e6100e00c2c00b011842d600403900c0d0381010345420062144180f0640201d42207910280140e200c1c0e40c0d804c820b004032480115202c088902c0e1015601000030b005515090605074081c00e200d080c184005007080d00344001385d4080d40403a00001c01e0141528194441c6400c1181200c000d112140600c07501038524082e200b02070310710102a0001840010241c3d0100c051640c10900204555100c0e0b0a0305448049920038080e201828643c47d21403034004070003040180e00300e0446070a0141c603080e001c031080328000c10030504004685051b415880301c0441c0e043c015000440b00c884e40c5182410040a8114807243d80010550083c08188013070f5502145003c050300c000440b64101c06050b21300300c0c2c024071030b049035190301600d06140c2500703026006010b00020882c613000301d0548410062300c1c1010700c212102c014801d1000ca040d000041460001502085101400101d074504050b5101042600700140801d90082111154000e0561154010f20343c5c074040c40c101a20f5068544 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 472002446 1250 472001196 472001227
    0x90a27120c02010215042307061202030a1503051c110c0f0307180b040b0924040f11030403181202010804080d0c0e030c042306120d02010f11 62
    0x2041082800070420101d025a4003c2c4462a80ca964070303260fa0350349140602e03244810b200090010f1000d822003c081c0c0585040004855040e5849500c3c0c03010029150720302040039610007001c4808841e203c080d80c10380d448500e50300b40013452044014180c0d00c04d8052a80001c0401201c003241000640100d8009402d001314001005880607520400d1240000c0b000c0307031404080348d200100413152941c03074002c40480c80e40004100c140880e030500c4404502410014000d00644030059015160b9105081c64050700b14041f6110001600c00f05035140141e81000407102403060060f030200c40042048101079001c0b82c0701102030b88141345000b1550412542d611890320075030000303061105590201d024009050141d4150702c0c0c006101b8040483c00420080c848001c420f200b6001e031280b020320009924250085800600080c0c14941c264010300c8068046160041c1030b45400408400c6400242c00c0148001117054490340c00204142629030701080c1207a40540009940310000c1c13110340100500c46 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 472003696 1250 472002446 472002473
    0xc2116020d03110d1e050c1c1b051f09030f0c08121602010e0c15130305190c06020303130303020711090a140615070b09010b090a27 58
    0x140c40c910710541c6a0728060320f4220641c0c900c0030040c40307800d51007041a40e0007400c0d0720101d03000d40000f01d443c001801013510540200e10354044a43c0002110a0081300741c41e92010907071489140c141c00c001003455601d40741c0c2241c07550903036075072300180301c0e00304018200415070540c42e01d040c6d410450b0034a151002018075020191500c1003081d9020b0768030500240310103440038490288004089400c060a0074001e8201040140303000d9424a03000340202e031004203019414000107000740c4000400c0e0b40010007280c0c45203401d4013007040f0b4030001001040c400c1104481102d140d81000c2003440309410311810040d001d61000c6d0865104004100c003815603c0074007200c1c1c5515040268898400f0719000031005a0210304035001440d2104020032400746410903001c3c2003c503007140200d0b840e15000c0c808560030b002d0103003501c0c4004101e07510004280256540d0312040320b000009840f4005800105001d1007951002ca50a46800d550408080204014031000c506920189080801ea035226250358465 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 472004946 1250 472003696 472003699
    0xd08030a0e070f290d110414040c021b210109020102190206040612020d090302032203020a1502190c0e090d090302041503150509071502030d02090a0b0c211602 70
    0x444c0d0000c4800009001600e00d51080c4d0441440800000ba440c031060350410320506400b00e41030680d021107400d01340300340c0d03402c01724582c0a0500b60050300d5900d0100c807864403400743c2000001c04104070480d032010921402c0041d003400460320714000d0000a2030412030128082e0070104041d00c0c03000596a000440d0f003120441d040116100f1070180b45072009016640d005c206043c2003120010070140c2c040000c140b9030017454000001ca8204211140307540c4041d0000942140f845041400103040000350203101400c1441100e5151015504020310b000b840d1780b04648028082c80144140e0204515503a4043c03442001407c0d240c03090030006205100f6448060300803039894800ca8000000441f95001031074020f0840c40c1d1a01403890f08000901044622141b24002c030103000c070703003a41006c3d40c41c0201d10301c0c1e034000c6080582980600c0300035409810390075844125803c0002350300d407088000d071038580100320103405650181d00c00f041504003174202040e140c9a04121003020300c4000c0b600c15005c00d40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 472006196 1250 472004946 472004999
    0x909092401081504030e03031c050c0702031506030307021f03050711100c140412121e0f030b090a050a06080309030703030809010b0a171b010912020d08030a0e070f 72
    0x44e94102962000f000180094040c0400506900600b8072007170076010f8158100b00030040b942c0c4022180d81c05028400c402076050300f0411581400d58600ea490302c1d04800001c0949142980e95400240d41c40c4110540b110f039500d050044503d0a5054419191b02c96080e0411200c07068134080e0700c2e501d408982110300c060f1a640c18035000c540e4450700c000703100c04074524212030740c454039100b14400703c55031154122070702039102d00c0745c00f8810b2290441840c8071421544501003000e810b1802c2d5001c14441c5007102c10150b0f10703418800380b40e82e07070703016603001e80e10b03400c00020141800c12080b41510300780d41060b4042d80c002c000d1044107480008070542184d401d0319003a461034a64020003405410507030411390348003410140101d51000003a074040502c00c0f9941c200c034611100c06025503542c291401c0e06a02095080104008540740d9081c145000d1307100400d02c5648200b1580d0321449604259503806542c3d070380c0e100401898904004040141a842c9194402103103800841d5a025042894403251b100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 472007446 1250 472006196 472006201
    0x3020703090b220f050310090210110109060908070203100b03060a090c05091501091a03062205070503060f120a0816082106010c020f041109090924010815 68
    0x242060030460b900d00c0b66070691907074103565016400e00d03084c480c050783e0321074000d101d9481e001e03140034400c480c100c0d030380601201002043d507182030320480340b0f400c1074401c25501d924015000031030034800e140c40548182c0d101900c4090b1401071610b4003004548800c419460a48166407a40d40065450f90100a84d039022810306d400b032400d800300c050280d000c2900108a0014895801901c00c58440c0300e400c00e0ba07803002c1e0b03140e4650244400502d16107c8001d41c68040011441c1400d01840150740301f1982c140300b0103d505080048401c840c001c40e0034100281d00030060001924092404070a030440c100c540200145640c40000d80b10041040001c11990000074140304140c0400c1c0039414164120702c0490b00e0f4071501410385c07032645480c50020031100c07029001640c0d40d030280341080131440e000f07070920403100c0c802001d100003410030010940c20784134203006150381580d51580309442200400d02078110541c01c0a141d503104648221180380380c01c001d000500040100040c4205d401c044200d0070031494 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 472008696 1250 472007446 472007467
    0x30a09090c0320032e0612060308130f080a0302100903110d0504080d05030910111e0712031b18180c08060319030309060204080304120b0703020703090b 67
    0x1400c20812400b400d5892252444036940c031070000c0c6118801c45c82505200f4901100000100202e012081e80d0305521041d0030f210103031151080c481040740780a00011003d440f0307112a95a5000070b040c00100500c891010f000d0a0103040c0880300030050300c001031013400800d0754041d48940c690f5000030b40c401d560703039521801d240c840c1702c0c0d910350310300c200050398401c10f681c800040440e80107000700f175024850480d0441400340f05008a908c03440c4da11b0301030000c034868a80308030060280c1070039020380d0000a0103400c84c24036000c50030072501c0306170181c400c4c2e640000703240415074440e00c0c6c10302109140c0790072640300c10782c0360b8070420014400303040c603261400a94001c020080780940d0707042100048218415611044c01503070180c400c007905a16030207810b58440c410190341d58031941201032a455001302d00e0300080d004e41c0125002c207100d800098105038491884034510381140e803205411243d0f0554820a00400c0e090740d540144c803078070341980707040007a440c00382042c11148510b030142c030b00003e40744074103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 472009946 1250 472008696 472008701
    0x1b030603211207180e04020105030604090c050402030702030904050609040b13030507060c050d1407020d0525050114180304060e0d0c030615050303030103050c0907140307090f08030a09090c03 84
    0x801e0a0031818618208442c00418030500142c06414036061102c02045c1d40c021540d0041c89180d0581d1807902e166170301000d000c040c1406440c202c4c0d042d0f4507000086071a540c2c50000d03521914041d80115140d4004508110a50344041c0085004e0a03668082c07101141c581c403031090b4440301c080f00d0400c80c0d9055240494141c45040d001900303a918100190417800c1d4400014080d085070300e0814081421090480c4511000c25500c5d0000b59020102d0780000314002e2002e42030103102014152030209200c80340010500c40490b046440382d46d24904481240e580c100d84a40100190030024004002410232540e64892400f0340014000c4080401c2d903195504da44480306c540e441040d2181c1560b0702e00d00500504003842c0c0800c00740d011701c000070480e4100001030300c0c100c3c1d40081c0188170301c261940c01d11862844c05801c90342045403035104840410800c0c4000c1d400390055a594180851602c05c2d40080700b01c0e44e0f000400c080d00100040f00209a20180c903800b81d0b50707689030001d407110894405800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 472011196 1250 472009946 472009957
    0xe330f1038070507030c0306061d0a050627070f02060c070b100308070b060f030a02030312040212060114010e220c23030f090106080a080f0418051b03060321 69
    0x10f140301d400c4011081020081c2c9541c01c0300c5c443d800a0104a4486c52109010542d020103400e0700003403c400210300d090307070390041a00007102420b400d48986c1040304010701070b041020183d24000aa41c14040b04a50048165018196078400352030750703084c80718515955100e2080080c04d000300710000316404114102c4580b004640c800881e642e07446035490402c0d0403e00c204d03040d600c41da40c1040c0303140e1141000f20348404480d034002c0c041d5203000400c0c071401a840001900a130b0704103c40c3e15544450502c104240ca02800c024100c841c0744c9105800010710740650f1240d46401a06207500d4050400c0702c0ea54140707420380007214046001c0e0340e0202d0841da1406c040d250181c8a0346009450340341409058000c1d40107240c2014101440c2d52599541400d0b50f0842c41440b0035548580215004107444102a2103044482c0c1c520501d040c0d40c079181e00540303600c824403540149a03034805000070700594050f0109154600c0c0101070561401000098440500781000707e9403007450000c070616030400c00b04854 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 472012446 1250 472011196 472011203
    0x8070912050a03020c0306010518040602090414010915050109060e0102010906020406120b060309060c03070c1505220804060309080f04091409010e330f103807 70
    0x4503000403070811503079030342c08610700b07030054001d8100c10903260501141c0c07603060b214060480407130302c40c04038454002000300420a031101c0340e00b40808211551349000da0091100c3d0320300c0c42e0906504001c0e00e14220380c09100407001d090b40841042003a030b6005480d0b0800c90f811421310340d000c0004040141d01500c030080008040e60710000c2c0100c3c4154000002200550318800e0070030244500c0414400c007444181e507010015480600060742c43c004002c01190b1180c8036180140756940656500c4400100c2071030300018464848081002c0008010303440c40d58480380f08405240185552625080d610a0340a0a41019241c01c00c2509104190048034694402c51602c00d070780380e99401001008000a60750038070070311040c030041516a44140524070355016802c01402c1d03066844921380e40308452625001846903034101c020300525010000c124441c0728046121075a52512480020701420030303821138101202e680352a13014000142d080044d9803d208070345208448410328504915015008008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 472013696 1250 472012446 472012469
    0x52b120915021306050f0403020f270a05061e01030c020f1e010b0a18090f020409060e060601020316080904020705250e0f040b040204060909030525080703080709 71
    0x74101e11549500420a41c519240528102d945441c0c0c100c41c0c034422130030701d0b1203240b00a0005001625207240d030312040c0040204000c3c41120481035000b10031000b0304c44041d204052104201809003035000d0700d68441003c80c0d0358400f002c1d80e15140e40680540b004c000d41016607032150a00c540e03000b004158144455441100c00d80711200f03106814016510760003410315400c2c407825103480d0070000e49100c103031070143d91a50b1649000d0318102d80100601d180a4031041d032845401d5000d6241c070b2103014241406031602046980e08400e040e840c00e41c010700a141103502c100400d42c0d84406244110103440c6e80031005540c0c4000c9000024003030300a0110190843c041c0d80050030107031000800c0411824080052a480241d85a6407402e0302d580403181d007041c00412600250009040390400c5520500c02800094403580341c0501104071040d440040700403a900250384541d0403074182d01007084004200964006c80c00903940e14401d4020500300405001400700411030007400360008170701174210701151 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 472014946 1250 472013696 472013723
    0x902121f080a050a1e0201050301030b07030b18060a1a1e0c01022223010e1f050a03050f01030c05062d0406110f07051009080d0903052b1209 62
    0x21902c40308281c074101c4210001c545d11184000c80e100e0f9142c1e580d501610b0740c0e421a0310f1603c2d83c0c260004014407000401d55034603813051281c2c0d02c0071040210403041c40b01e4004549012018000b41442d80c4d000710121088110f0b40c241004c0d19141200d03240a40c100c50701d141018a40c464518601400c2544041540007054510000044002d001426105110010000b55460032500011a40f4010425802c0c5840c150351000e9401030442d80e003061009020441d186010050b13548480c07140316103600001d42c00040000b0380d240d050185640104225400041951656842424000b01d500c900c502480c004100031828400d001c003c07030b0701c030b285504000364202e141c004c076210154800d0081002041300601c0e00300807144000740305400c1050203401482c65500300010843d458605417020707010404200004035500360144042c07170000d007068664130410782c01d601d410ba0400201c0e00502c4922150711700d0a0540706145a51402088140d04200c842c0400928025000c1c100c1c444003d0300e01c0111002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 472016196 1250 472014946 472014953
    0x30206040b03072705010305060315010609050103231605070501050a02040911160201121d0303010801060b120a090c0905180d031a130b0a09020c01060902121f080a 72
    0x2c0d40f0500280d600c0404000c078a82550611128210503070804400002c020301c280d501940c8000e0300094000c0440e41440403030a503a41c4000401d800c11000150418010405d95030180500c800660981d0360200383c000060300c0c51715901e60020002c2841c856050104222980174030100d44c0801c3e0480000d10142c50b0251032000079502610816006502c0c1a00b2408402c11100a4442c400d0300070b60344031083e00f0140c0044509080071024004641c2c2e0b20b07622050a03e1a040742c00c0f40b07624180001d561298541401c180c00c44465038040c0d0750306e6208000344440d0281a54101c0e42c848454100007404024038101103800303412a03002087c1c0c2c1442e01c0180200d02d400d01c000c2c941d80c1c0d80c0d19811200501201181181510102c14242c43c0509880018114610f4148040c04002a50b44400141c0406a400203080b201032a80070550840d8001000e480301d480c203001d600081c2202105c298130b003000004035107040620003420070084545007400036089401008801005003604001c6507500c2e503140c01c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 472017446 1250 472016196 472016219
    0x1404030b160c0228090603050a0209090f01060e01031109070203030a11070c06030203040b0105100504060c02030a020904030519020136060c030b1f02030304031107080d0f080f19020c030403020604 86
    0x515840c5619004c480000c100145020f84401d070781d0710034080d00d4802040d03030070710049950103005e0348040c1c0518041030303107100804d12601005018460130101c213035145050940c4034a440c031201a0140c81545c040041881d0000112500a10100350000d61007449a90408142c06500c4005220b01500304000540d9980764010b1070080b030040c9013085090766542c08000803000b81c4081400031480502c82044054080d080c6415014005801e40740301c10b50310360000b001e900007103d0840100d01d01140402c0c1e440080c00400700d60304c45030f0000b005079404400311b140034034482c0c44111031850310700014500d001a007010b0341920750ba404a4140701c40a003400029000d4505011494010030303242078040d000c0028603d4841120400750055031658030b0f42d0310201c9000011741c10702c0c1214030aa030800100424100a5180c0c443e0b0b4035a2039080c424a1031074005c100000c040c04254005281000744514280000224030b0803070500f510050f031340c8403940a60360540c012980069070142c008180050300350340c0603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 472018696 1250 472017446 472017499
    0x9061803080f09091003050d05130305010c09170a0b1605210a1512020105071e03020102120106020a05070b03090f010203090a030f020a2001120c020d1404030b160c02 73
    0x44808010a030781d80c2c11401e09052171444041c00c2175000a07110440540510010014040c4009a00d4021516510344c1801d5941c000c0c4200c4c0010700c01201008a40031601c0c6081900807504043d25503403415444024003d040035001307000c6e084410052040150003102100c07054000509412101c1020002d001c5020000b110150b0b021401c2c900703d10f81c0481c00303c0341c540c140da2013502e2001c21601c05070011151504002c0d02142d040d08044c040c1c440d000d03030312072542c101e071482980096691540c14025178800001a8010000d56200202c44400174002048000076901c410000b1074880e910080785500e40701c4a5510b007441548000103000e4400c0c8040b5100e680c05000b6240c0c403812a42200080f40d98017500d42e805017032205101d1400d030b0951a01000070b2408141417402141d1100107000c0c200c00c80c1d000144500250f0700c1402d0407103a0a0b045882030b01c0c12002d02140c141030520b03686443c2c494810052480da40034030207004010171640511124a049600503040c2c45901c01c000741c002000c942c1c003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 472019946 1250 472018696 472018699
    0xb04290f01020a08041203050c0303010e0103060b100e0f010519180e07020604030324090902090c091e040e0a0803070306080102070c0b09010c0204050901090b0c0a09061803080f09 79
    0x40c0c2404144075400003400c070700007070743c0500e80928007890701131183c0e040c41002c1c5003101009420008000c00701010800b642c06040c041c41107044c554514900031013140c3e810340b01c0c01e01582c8002d0b00e581c0c50642120b4201d040c0b50381903d80f84090384180307004070791500c5000d1420021810f482070702600c56a004a14140c0004003041d511441522100682c2c02e1030001c407914001a0b1018000500103480703034002c150201101221201c00646e21000c042c2d2587c6203400c0207401541e40d081d48820b500e0201030094000042c2140280740042c00030118084443c4038000c00030b0900260400d68054071107520402c01e1801850550b0030585403840c118009500c01d80304040001c0c10b0480214034140d0610031100707001d51000c0c420702445c2c54545060b505801c2030034050706100042c030014001d6212401850710441c9400000107001c065480d00000300c460203031114141907010f2050041f500c0c2c0200c00d402c240d030943d0824800740c0020800190814007136410040c0030000215184610502c480003816000c00c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 472021196 1250 472019946 472019959
    0x309010906141b07051204060c03021606020c0d140604060b1009060504032009090d020d03020702210715020a0303050705090306010b091c05030c061e0103060b0429 72
    0x465000ca12141000351000003e00c008031182800751441c02d402480d601c1c3c412401d036000c03071140e18100542500540c1c001008142283c85580030198103204092006a00c02c014a03d0681030000003076441244502c0c1e140112000020101481007011000301e250800c8402c5841c0381c607082c0380a002404a0110039070060801c0040003a0140c0182e41120650301c250b6101400e140c0b03035840d04820000f8156991800584802c69444243c035038140492040070b009004041d0749aa610303000345844600385c0340301c1c20180306200c0000180d68051034034200145400760040c21500c150091403c0c013401c6e034090024480100302907226942c0102e80c118110340291010031159440200c19281481000316603940754204400520000003800007404110401801d000b2184103a060309440d0100c03480b03402e5038146e00108441611200c02c012541e80711030104070a2941d40030034400b014100070180002010316032143c210070602d841c0c99018401da481d4444c0c0382e200d271404130070000310031000c04a041c81c020403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 472022446 1250 472021196 472021211
    0x308040303030b0d030f1b1b060801090e06010b0a180e04020901050409020d14011d06010f05040c170601140316031413110f0301090818040b01052208030309010906 72
    0x24144200c0704409801d030b1a8185d8804403a142181d100304035003d1a001c2c40d90307d407140f4011510000503603c9141520f210a801c480c1002c00140090304142d211644e1181006113070701001a000c151203044500810045451301680e0200fa2901004688002085484408001041205041198021402692044810390f214001e20056a890005c065088481c0001c20400189040d07080f000100b065400000c4116a0081b21810b880c0d8000076000b00e68402c030010722182c0d1144200400070b000440d4200180e4081100103800c0e000e03000c1049511a800300d00081459001d007200e03080444501c00e609549180c080c404800007009802d00717400092400d4441e00700101c800c0151402240b82113191039844043d036032040c55254203044900d4203c5855541125152001d00584080d5485801134980703070346d00301050394201c1001920880c1304a08003410088241d8100048440d041c1541072038010b0407101681340103003072900c2da01030b118921001042248115041d40f00d440070ba441a0303000d01030403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 472023696 1250 472022446 472022449
    0x9060c0102161419030e0f0306070c03081302030601050925120c030501030c0b09040e0f03030402091609060503090a020a03110f060304172a0105160804051506060c06010308040303030b 81
    0x241c806880f90913900d04000000001300c2e02034040403102c4207000f0b0040d28416101400b0905122083d605c00d03011800310f1117100109900300f500d0541c80b007101c911850180e4566000240d0728201807281c14051302d50480840c1c20004410080048003403040065401c502001ca0014454001040d04046151074500c0e890344a52282c052710341217a803c5000040854180004074000303510043c0c403e54040e5a81c01c1300c24544c80c0920a41c0c11004c8010084d41d101c0c03130540140a41070f40010a21923000c40d002848003d0f1710380001202c41590305902e00282c40e43c0e15884980d1816a1400c0044e520403d05d000020801c40780d0345042c1d040b400181c5180c040245220300f80440b0780420384005000245260101225039100d4024103054000f8048044051000706095100d182101c0358a00c542d03510b440401031342c91752889001482030a075142c200d402c0e1409495150310b1340c070701d1281c80c1425417a420105055603582d1040c3d46070f03044a5010790700c2659480c0303042d5001d54080d100c2100820706105d00b01902c0e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 472024946 1250 472023696 472023703
    0xb07080f01080607021c0306030b0a05090111030f07050a030b0306040b1f120209040611120a110c0c190906080601090f06082e1e0b0a051509060c01021614 68
    0x15192074006041d103406d105440d204445094022408255440a00001040321003103c68044c80c0c004200040c5810141206070941d4241880c000c100d540070002d102407110300c4a41e044d441666850b0083e01d030700700f072602180506079144071140c0c1880340d281030000344030500c42d4860040d803850034503810b82010380440c42c6045041d48501002d90400c8050040541411a001a40240319000004104440140802072900701c0507005c6a00e0200300208a0f03005001e04c00c02190082106909043c54100b09603180d0f92981c0300c0419009941c100e000d101420807901c2c8a0001c0d00c010042407000a40b40c04056a031000c0074030401d80307440d0811408800d101c0040c03003200c007590300c14405450015200340d4062490034803400409154900e80700070406c1003c19215411140d610000c1900c4014a1100e0039001c1e41c2120102a103e44800e01d800c101c9a580c41d105800801c6031400359a403186d140c100019110f00808036540310315400001c540280740910510507102e80d100c3d400e000340b401d10710b00c0d0701d955 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 472026196 1250 472024946 472024951
    0x70816050901032301060906030e070e010b1e0c0c0a170a3c0201080a050f01140103110301060201090b18030d0e010209330304020d020d0f0b07080f010806 68
    0x1003201002a41e440703500c00d07003002ca81d07600708a00707102403070118a0266030001001d13480b81d000180820070038440c031a0315024611950031440028807849050000c020881d04040c881c003a035202001849040248801003825191810200f441d5101e500100e030140c2c40d01140004c01d44103114038000802d4681110003610103484804000700701d150625a2034000048449280f05403250020304002e003a6a000300707002004195020310707401070181d01e20014010755030103040c84e00894100000c2000e552847d110090440380c0c0000300b04864200040141c00404000e0b800070390303002c2d0010010913100d0301500000103882c8210703420b488a540310540c0c0c28414921141c007003d660001c01901c60644038076009046003004a034001072405802c41c0001d00c8040714134860071505540300200844001c8401c5070700c2c229200340c658043c51132801d079001810b41d80150800030300c1044406101001d0000400b00812401c1d0f100041c10340a09048001030004c180403a0018550305600d400459610001f140260 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 472027446 1250 472026196 472026241
    0x306241804020108061206010902271005090d0219060905010c08030f150d060e12040501120903050c0a0f02091005030c2404121b0303080403030b06090a080102030708 73
    0x55880781d41c0110b404560207454981e2150101c106081d0314903007070240310b000b00341f406001603940c8512000707c0c02a4a0208194200c050304e034013803041a8481000c1c4606940c02440c116a648081c14001000441040030194001e00c40c0c0c01c554168070089049402907a00a803101e911059607030004490040454500400d080c3c0c044c40426013500403284010f07080054000010034004400340407429503081104c0c2a82c0140d00c452810f602864144021450300d0489070b101c0b440c0600f4900003070b1000000c0010000401d9840116000341445013007603540c0b0358185401c0d550703010418103040b00030528074041641315210f0840407c4890010402c030703208584005c1c01508400c40c41a0801a00c05944c92004620341d03035050710f1002c0f1122170001070003d04607540350407106000c0360610103800060110581c40c428050502880401e42012000e640503505d807401140300f544000100725580900d8588540044a81070042104030040d0003462140d243d40e91900300550b203010600c0d00703404d00d915101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 472028696 1250 472027446 472027489
    0xe0f0d05040e060a05130b0f06031317040b0c0703030f0c020a150c062306040e0c21160608091c05090a080d0804260301050d05010b030624 61
    0x1008641e842200c0c0c5544580f00400070060b440d95440460b00700350103100301d20740e6180e1716a00b040052070304044040466030151201c0c0d0442c900940d501c1c88668188002400d0807080d2100302803d20b0032002242e003d00f00c06000540c071641c200618039030300ca02c1c9002c100d010840d24141008005d10500110a2450b0010311031882c0300c3ca0400b01003409440443d40c402048003c0d41c809012a00d54010030303030001841503015580950f0050b801d9403400014101c2342c42181400c41001d00d02c0000226160360410440b03441000d003042c1040742101344000140c0184030b010304d03030b852901458007490050460351142c039541100c2d0b45e402c1400c5d84981300c405a03540c208580400c080c443c03620480241c40042005069803a4094950011900d0051010a03a0000900d290104030820606032010381812a42d07009042004051b108007400c1400140901c0c2e01603044e0601100a0003000d4104500581018003a54824108002c80310303840910001070305a002d0b08002c2c217a8403400c00021a40f20300b000c20406 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 472029946 1250 472028696 472028699
    0x31101020f040b090415080d020c0319030305060307090e0105180a052505130516051e1c020c0703020102250b07020402070209131101090303051606020c010c030e0f0d0504 75
    0x20340081d40112804c50f811a590301820221541103c05c04005032143e80014030801c81c1c000402407030500c180486078003d401007049843c100b800c0030f621044071903140c14049650b544003004a0301d8440c05900c12090303a418810010306405040d072003580107290345007041c074420740c8071070500740d03510180c00d4001e05d00e520a03403050b40010a003180c0340d950b24440c004001851780d6280005001c500b104011141141e50752414030000c903018421b0030050341402e081490401c010307180d00b0001c0340d81c80d0100a00707182c40001c10342e00c0d8106d8031b000300052145940c01191140c001c01c400e150303241c800303005c2240540710703103c40d20000115020240c00e00c0d51031126601d69003030400604520a030405102240c0045c0c007400034100590b1031045a9105594031880d6500302c1c505401d0030702c0c0700020880d0301c9040c490460b4090001c00d6000b800c850308514601205032a0f05524613003100244107001c1513140719440c01030003081841d0300d0b40011950300700800480300050008c1485540703442c1c00d504004003140d001c200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 472031196 1250 472029946 472029959
    0xb0702090a0c090b070503120a06030c12030309020d0501140604110a0c050109052a1917280506010e060607150b0a090b040c110c120c030706030504031101020f04 71
    0x1020102e00a151048810741c1d501c50704c0c255500407000441c1c2d180c2001c1101d805017a420420207a01c1108002c00703019091035601c80309425141d038010107810314840c0407400b003414040d030010f65020350f018003070100d0040e0318240b5a00900ca0504066003880c80000414210f240030701810050300c0003900700130701d0301010b02c40030b4502040d0010212800c1d5210a2000302140044c003803c0f11584e41019054489035400c805c2c0c3d003407582d5444da20340c800d120901102c9104100d51501070281d95003038440480d840c00340b4003011b18059003803d01c040303015400880d06603400c0d640c0f42c140888034415400c03107500f640c031500072f8406048101d60407078000d0320070300c09a0085440c0c181160f403010b69055000501c26244c102140c0000007c1e0003040e400790300c6400741e80c200d0801c0e125911012800349814501103034001240ca440311a200038280c49030750101d0101c200d5106c10b003c210789040300102100c50351540c03000c0240c0907100445040c0d011808041d0828004e030010b000311580524402c0419140900f8010f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 472032446 1250 472031196 472031201
    0x301180201091e030f0302030405090a0905030304082b0f0e0c0306060d1401051f0b1920190b130302060c0d14041b1a0304060207060212100f0b0702090a 67
    0x7401608000c0031483c0001c04591901902c048040c003ea001c2c5a03100d003400240034038030310003402400b2800d0ce0a041c0c0004a10088242c03904030b94800000d030f076240fa0303604000c8040200105c1c800c1e54060b640940103a50740c40c41d400364615074000e9006004024800e2005611000303a00b5031030360075800850010f251031501d00c1490104078811a00920041c0d070000b0b01d80d0131144111100b01c018204c8002407100315102c000ca0000621901c6805840c107001655000341c80c5180090322070074004042041c04030407003c0c19060169000d58022103400e2941000503800805441340f054821903800404201d22940000072070240355010740040000b6150a280fa94450740501041d10705150f84070303282e5452040e03020301e442c040d5008003200c2c402c513081011a000031102a0f440102e8005001c868102070050580075241c0c4141c1003030340140c03180184e040c1180079111310740b10b0b140b100c81020208402c404c0e00301040da0a444c800310007a0034250b16000d02d41405c0c4182000658080e06040c0003503200106038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 472033696 1250 472032446 472032479
    0x1503050c0f0d080706090c15140f09010807050913060905010b0c0d0e010207031e05010e03030127110f0304120504050105030a050a06170d1e0c03081b030a0506030118020109 76
    0x449000906000035201c88001c00302c04e8224000c194514036800074056401611482c4881040505520340b4002b02c0c86614184604c2c0e000c94148840c41e000214994003a10588480b103202500751a01d55840e47d8a400c0200068040c0000c400d250a0011130021301c40b60960b6181025040100300e426544503054841000e1402c0890441c450010080002855a5503a00e082c0c501070b0306108880c401072a21500b0350308211a0094a680309100400c0581d0b0585110403076000512924920740e050003801da4050300d03d4016242e9000000500f9410b16030840001b11302c218001c403030055080e164100c046038284101d105040c0020820b20128080c4406680115000030109000003501940d071801c59888616616030b000c1103801c0400010b1540ba008450928070924800300482d1010074050007404081c08290090304001c3c404000031113000030024200c0c1030008001130540c480c68410b030800c02a140c00c82b2064065422f180c04551380d5690310400300420b40c0d050b150388144508003040c6094181c2c1c01d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 472034946 1250 472033696 472033703
    0x9050d0804092c060601081302011422090501030f2306160201060602010b0a060c1416090b0d1515030215040608130507140a08011503050c0f0d0807 65
    0x70840050188200d108039640b940700740d40b103d05640c105014003100480407250101c440e4006001700981030780d11400c203690028810708105512612400100c4240500c40401c00740090000b503c1c002031030300800310040c01e40b815510300c140580c40700941010342c1e4003031200810100b07007041034000040c1c20101030800541d04201b0003103095040d10503d490158182c400902e140070140251a0140e030a000c0d0202604580c0000d0028060201c04503079044c0c0c0d41e00c41c100400199000da1010006402c050106501340202200c0491045202520707041c0d540d44103900d40d252601c07000c105181030011401c0f6149401c1189034542000c128a43c001405520b11000300e0800d590401100680d280140001401d02030410300c1d4030b1320700302070b00980100c0000c1c0c4102d401108000312507001400029048003502d11142020625207099004074580301c000350030401d039a500f001c030b0618041f5844152602182d002d0350443e140040c03010f05000100a840e9452500304140000310b6001c100b1203401003070201e01c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 472036196 1250 472034946 472034963
    0xb01120609151509141503070509010b0c100b060a0c1b06120609110f0a0e0603041511090310022203140706050f072004050c1209070609050d 62
    0x103a503070b6051002000c0165168540e0700c400e22044684030341000b4014000705a004c01c80f604c505020030030780c208010710003081e5007103081c50540e458405216180c000c0101400504e40303940c4440855042d90001800c4811030b114024004a0700e040307500400d24034400243c0110b2134010701d00001c07944480b0640080d40c40b8443e00c1d01520b00803000d09050801488180d40b0320303616503500900b020076a15240c1c070101000781032028524609003031404803106c0c16400d001c0c040d510a007400040c0e80c1c80c03100b503000583c02403000c4100001c3c0490103c9202141c0e500c01c00420400c10914210384841c0103210016405610035141900201041c1e8001d00403075030900714690310f4032020851000e040010360412100c200c280a501d4005030410403651010300b02500704241130400c14101c1e0b074001d018000340a01810400d000b649103064501c8444201d0300c42c090030071b10981c5032030f2a940481ea80a0b01608840d0024a00001d4403008007144c100705070340c1141d4503081d22504d4441000000c41e00440d065500c00c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 472037446 1250 472036196 472036211
    0x318030c05270c070204060f0501140313050307031d0307030312020703120c0504060f09030f080f1c0b0f06090a03062703080402010e0f150c01150e06030c030a0b011206 74
    0x7012041000e20400c00201c0f00d641d1a031480c0b041c0070503255140e21484000004131000c0c40181e030410b036040000ca440050391520b83d075030b0b001c0a00341d0180104014143e0f00000451000303065008410300c200c201035150755180c0e241c1d001d040c155200202d100244c0000c81004202413001d25640003410300314024a80014110f040301d001074200c81c901038291000c16000141013020702e4202051281407101c5040c08400f00386940c0f6010403403492170400902c0c111000490032550540c1c0000d60341f0505402044540780e9144400150082c00c2045c4594403c81c8001480041450030307104a56550348041c142440307a500d03543d6a540038101c050a20642c1012280c940c000f00b0a0390001040d100f03000366103540701420203000240c4075081800006029166850441a02d40c48001810b0f4100303022440c203580e03031882d185140340100140544900d0501400314000ba941041d01030f203074040c46086090300e032100500001c141d80e5040220006001001c4040104421104041c880f103103a806102c0c04240303076 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 472038696 1250 472037446 472037509
    0xf0e0a3b0325140f0309040f0f18050106090204140f0d050d020a0308070504080a0f0507050a090209030106270905031b010516030e1231030318030c05 66
    0x6a04440c0641d202c44031000c0030140070b100030301c0d4503c10840700003820601105a00c1c031034480c4141c5649a0185031a0320816580440700d501000a42c00800c008203d0018582000c40400d00158403e480b250b0a1071008035000c0d070030344222070888443c045141401002401402070101402101c15440052120510042441480b9940ca28503a55001c0c048c8a611031074050000c420142034081001414001448804800540d000390103030821055281c80e586881e2a038504506030704010741050b103440c0009691140c42c3c01508001100324003e103c059150310710a4001d00007013001d0b141c22600d61070b41350000794040c0d0140d20054001d8041c2c929101f080d51000515100d03201d5522120307950b4030304002e111a0100581e1500149a1501380664241c90000c07960310301100049605600c00050301220014000102102080a4015030500040001520303030340781855105c25004600720450f004161884100741406407940300c49462620760900062000c460300c001e08001d4001ca101120076203d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 472039946 1250 472038696 472038727
    0x8391b1f080403020d08010e0f25030608070b07020d02210105100503011a0105190e04060e06010f03020313060504030c02030a060b030f011406060a02070f0e0a3b03 72
    0xa50165254842103081a143c02440c0c0144043c00e078007041035200043c000d82c0040005c0f5904031007070f4110f06140707440310860b00ea0b000c10561034100f039a9010202c10040740307405800c064120390341001504c1e007040e40c45100004a2084040080d03011880e5460803005142210380944040005035410340c0e0b458440d10302a037112010340d140281c030004a0020042c80c5001d01814070090f120803d01c01c4550100c1d13002030020302400584403004a44002c11000d01485a030a00c00b42100080086c0204c40d900d80c50b2180b40d8400343d03007641c001907100c2d644146a50103802142d01842940c481d002510400f0349418004000c0544200c00b00002821410b0240e5002c00180103001d010b80c2d80040c412003030104061601c3c0340c801114540764108115034440101d0030343c046070700100542e00c403680c071110240200c0c2001040c1d00001e461002c0c110340800e640c0c0c50b400c0c80500c03411180a040012840c03030348440c00540700050319100003600c0c0c4d01c00502802040300a07a900089540100c1e400c0c01491500c9950b07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 472041196 1250 472039946 472039999
    0x304030606141c060b010e0607060c03060e010311090c09060c0d0e1009050f1512061011061b04150804020913020a031b0308391b 57
    0x2042030700c8080c1807100c050040740d100b21546046864440c0000144003903110f443d84420b01401d456919001007110340d00884402080810080a190381c400c024030f401c3c6c0050942c21601c01c00646001c0c0c0100b10b0070640c11046050f02d8101d40040240c0901d601003100000d00103140030404241804085c03520344411000c1c0c902c10000c20301515484061120003040b42c100544c580344500746050b0581e40564220b2140d9060720019104066a5070074180072a084125240e00c0c041e490320b000885290100b0085501c41c0240f400301d9240d001820081000c4440000b15081040309070030203008100c0070f00902151a801040f501c0741e05080c95500c6801d0700e04c28030440b00d000082034115040104508c1c01200c40cc0c0d0103001c07900c042e5110081900855100000340c0001490003100c0e600380c085042c010098078008550002e4140e503500c90040f440c0f8400c50324820541500d00b000f2510281184441000251051400303004020f610704005591a80000309a1003035004401600e0b03504001c0004568240c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 472042446 1250 472041196 472041203
    0x164107050d020c09060d0f080c2d06010b1b0a02060a0c0c090608030306120325020f0301060e0a0207030e040504111302131203021603030801170c030c060c0a05030403 73
    0x60201d00c664064108410410740d5845007038501c0c00c120651390368083c1401642d410041d191000c0c0c810340360000103481850308102081c4500b06d910034042070074906e80c141454018410115460f0b003006080d603a00320038000d6141d400c1080c8498056410880885040c000c0005e00711121800c00742c0106440398031201061000074040d4040809114100784428024a4040303400c00202e803401e2112500c5e800301074141c0b4403d2a144070902540d9100300269540d000d0f840710650111400c3e0201c0c1201c4203040003080340100d0f00a52007800c1c80c903040c0305510071500303d00640b44003070762401c004400030340c0860011801e204140c4041c00b56516580b143da0720451141109902a40f400710400082125400041c42e0325801082002550500003800b44204c031450442015210018941642001a040c6c3c101e0313820b8111a80010a26910100d26030480e070310104020b5520f542414465142c09210707041b140c25134410900c031511410944020286580d5220550303020500070703a60303241140c0c00f175481507 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 472043696 1250 472042446 472042453
    0x12030403170309150c0a1103040b0a030b0621101205070e0c070b010f0905100b0d020703030b09041101080c2811060c0a02010c030203070804020d0606081516410705 72
    0x6d050850300444840c2d04038183c40d0085040ca4030b0003d1112840c45481000301c03c00d0340303c0c500c040b22a1145010781c1d0707840141c11011091208801e03a81000e03040300300c40019004c10003020008034582140130741100190014050a041c0d030030040b0018504001038480386564a0412080700401c8807032020718003800c0d8103140e882502e0314202c40d0300c0c2035600182000d8442c2d007000b40104805003160049030386400c0128000368071080c80d801c040d0700802080080640180d00b410401040010740402c440c05504241c03101e10540d1508410440c0a00800c0503280c003400e8045070101920413901007066141000745008120742086488290409a0a032040c00b03440d0400f00e43ca43e4010380a0042d510450340301d250450943c50480c0c002040c202024001074001c180c07410180c01807110310f80050002e8602801128003031071103804000e40c402c00446400c08003445110951034100e22820f0401542c415000355540103121111080c0c1c52555641c04a900c0c0f4056040100456803ca01c00303042e00758000e1014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 472044946 1250 472043696 472043707
    0x40c1e03050706021903030c02030f0f0304031706030a0809031014010602071d0106030e15100609050d08030c031003121205101505071b0e010512030403170309150c 72
    0xe51030b01401d90030920654000e01100c030054006010b940501d6905850042071441c01ca64060742984680103200e2400000002c511208008540c0118021440307659002c8800c2d60810800507681d6041c1d80c0b06900d0b42001d4134280c0420142c8006d400901d8000381a504a0454201d12400700c402d2280000341c41ca2010b0010403c80e601800644000c00d01950700300188400c1521113501c0303a605020f6141859078481401141c201c6c100301c00d00b07800d000391003180c906080c82000d408072610310b44650000103182000100e45410200403c504d401d600c00032090850b00d5014100718076800090122090040514000000c2001c60b1b00080045005481c0c402150f03101401c602c0035250000d044001d108a4404100581c1c80200321924080c5414946181c0b030388118a000503912645c941d18080000100401107a1034511045081c120f580c01c0790a0000410740031407581d100d004a12010307091a1419100801d01410034005640c818000070565a1400801341b9903114104280e07500300332084040388 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 472046196 1250 472044946 472044953
    0x20f120415150528030308150f090703050c0d05100e060f01020c120307080309030a0e01020a0f1104060312110d021603021302090a03030c150606080f040c1e03 70
    0x190340303410940900c81405412035021491450301c0a503c103003400340d00d81c1c400d081982003510f801c1c0d5160712000030100b00c800b962810002c0143c00191041030014402001340d13083d41c075100d1061401400e001c2c024402030f0703403034100684c01440c0050501160032800c00c890b44041d06a4450184120001100d2400c40380c204051500504801840e2901900ca883d00c840e80d5aa0005941e8030b0088085410408640314103203424214001c041d0000c4c00b01d1404000e0120320500800503100500c81662903615002280d001260b9460104ac030107401c1c0d28a0003410300200d182d41c41004d000180280001c64040c0c0d0781e94401c00704100c803820150001c0c3c20f4140c6406218802e2010340d00745103070b81c0300800184864106c0b840316146070b80300091044007600700a80005c141501501d80004008040110a5607070342405828402d01c83c104503920520014400c0e60000d091007190169070142c2d8640d2070300d41c2c0380701c101072039054040c20989a41d003503c040001c1c031807a040e0940c3c9042c1c05540008400710319500e13 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 472047446 1250 472046196 472046213
    0x92a0918020f0d091e050708061b0a03020306030106120605041110021902030a12020a15050c07030c06060b0d060e090a020312070609050d030c120b031f020f1204 71
    0x24440c1000d2401003000842d45402d070707410380d07020b04000000020400ca5901c0c00d1981400c1441c00f00742c010399503210501c00d00c000407880108580b03aa600340ca15a0f6070b5441c2c1d180c241c07400c1841030304401e0700c1400700005881c0300340d02a41d070003100034000240140c1c44d80325054001c00b544000722011510740701008204090604079803800401a07641070324200000001940f01c1a00c251064540301050b8000805d6640401c00840c1d00c540180901149501c0030b00c009480f1100000b0540f1140a4550300c40c00b00c100f6813240d280300b040c5455041d8184002c81d0340445882072485030036107910303889203000b086d02c80e010f40007082c0340320100c0740002e106c40c40d00c582003050748001048000315801c00d04800001d600d002c02c0c44603600107408159680c540305171400d00c008102c03084c0c000d00644580e031504581c1d1a0154070220340a9030302e03142c0060382106405000165211240f800390541c02c0284c00c0c4103041e00b86a20503004940464016042c1440341d098002260014500283c0840004091206108059 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 472048696 1250 472047446 472047479
    0x601030606090c09270b19080d1e050307020f010c11010f05010803090607020a1706072007030305030a0b19030c0803070b0c07020109120b040606120c092a09 69
    0x1d0804c181d41c80d2400700e032803106003c12032141151500441d01110403820300d40c0015108240200124103030340640c01e803406003058901443c4203510820040c542c4080c050183c0030710f219001202201105a4984d049450303800c050212070030b520034002e9000c1289020b010311050003006546030315030b03010f4111700d96003500c400511880c441483c000040c0702e829130200444c0d84944064034641d039035102c10700c04038920801c00d6000200807200d00c50500707950318012607028050020f80c0d4803000e6814449541929500d040078030f014481d4000c881c10030000c1c3c040d0004d0b40e4000c484c034900051180404012503114071002d200381d0701d2640850018000c000403800d440c0007500c00c410040d42031a11940d40c1c50a1701d034000e4845c8800b0742d00460800c08581c40703505070a01500d500c00f110b0f01c96140c54500080061000e44007224450300b00301c008100c4500c1214500080780c1c01018001c1130741e01d00350f140002070020180b900d007100003a5102e04c85104c40c04000380c03800c4000303980b0f11115510f000c80380d50080009 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 472049946 1250 472048696 472048721
    0x3080a0218040207111e041a0906220c1110020301061b02060708160c051012021b060f0f070801030c0e0702010902130906060503150126060103060609 66
    0x140000d203850729200d10480c40820303003510016501c220b070b402c044c056003603052030a50f40036035903a00200b059042c0100c100c100420a5900f4454211490300c20045030b03d881d2411030700b2411240018002d0b19009403092002d2050355400c02031210004001d200381c1703070901007407004900034241000d51840100800e4074400d50500e4214115410068010001c104031243c3c040c291190103001410366550b0401ca41c645607100c1e81031503440c0004c250302c3d00d5005007460241c0b0f071140341d0180060b240c03d2810320a00750350142c0ea9502a8103040c6400f20000390001c000584080c1480c440e0002c64040400103140202a41003160700d083c5030801900d010807000a101c0350030046031100400000300f5440245007a144840d244d4501c550b00c0050480c010540880080e50201408020009141c0c00354420901c040c02070005100c40f98039070041c56070700c2113580ea80b0800e842c01800104200e000c0c5000088291a41350209202d241c0c483c1141d038070381103080e04140c1d02070f40d64002c00c0080c641a8440c044412070b8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 472051196 1250 472049946 472049951
    0x106080717030711010c0c080106090c0f020d020304091a0a030b06030f19030807110d03060f090605090a050402030a05010c09050a060e09040b06030a050703111008010e060d0f12020a03080a 83
    0x80d29a44c800340c00c00c1c01e004540c180300130104c02078200208441e80402804215000700f014583e1014454090120200741d000451840c0701c401104520120b84c2d880f0240c91500110725041c03414044070000c1070301c9022175100c0340880c481c800c550350702c0c218800000c5000300d6150303065080240800d17041c41c143e40911008c9510043c15200705249480e03411031131981504143c2807950780d4003426903010981000c00035081c0560040c0d0420950150300107010754511031247c0421075110081c06048070080d0064540c84000600010741601468100a0f4481d201505440d441072480da241402c1d110f62104140c003040701d2030000d10440c1041075011000f0103561800d46e09003c0c1c0c0c000410250107010f0301c0600b010314400001801a1410818640391030b80c40021240d4496503810544481c002105186208007082d503164207650748510b140905894030001500503540352a4100f0040400c4510200c03540c98507640d03c0c0703000c901140d8040401c45115009402da60b10186001000014000c12042c3ea1a2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 472052446 1250 472051196 472051207
    0xe03032d01090b06040806130b07020c0a03080d09080406170c0a080402010e011b030503091501031709011407050a0b090607020a0611120103030207091107030512060a030203010608071703 82
    0x32040038824119418040c2c00181c1c4104100070414a1003036401032076442c8207803420712085000e40740444080b01c3c0200c5101c0526144d5140407a10b070711000c8031080d848442e05100f400070807481e0700189200802d203c1e0000320030b40c0c2d170b40c0e078160700c1c2e0041d81c40302c0082048092580342d11042c000c0045d0f40320800344820340c0760158481c8040d185000241c80030341080400c180c0c40601c0e90092442d69454000201903041c0140c03245001460342d0b02c111020b401d18020f030b503082081c8201e8026540e051303950001c04460701131030060303500e0029004421b0880c1000001f401c200744950390b510060880034041d0010307102d400410705052001103005420b90070725034840307070070807202c0c8cd404522a140303280d12140100340c050703c24040441c40d000c0c641c40e0b808d1041c001c400010070550001910000c071400c5407020b20a800c21382c40b4641281c00380071405400b141042001d140964040d00740a50300580c01080184c4494598000c242103c60070b0f0001c034482d6000704800e00800e90584107507280c20043c1001140b405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 472053696 1250 472052446 472052521
    0x100c08040b0619150e120304030b0a022502030d0801270e011523210f070e0a14010302100c08071e15020c0d0e040608010e0303 56
    0x60800610140495924030003048107941c40d110604200300e0030940002a140e00c6010260b02140d01d40200c5002c1441e16880300c2035030406c54034031165015030a01440c10686180c590000040d80102981d207100e41c20800b0105400441c950300360000c556082e01151000184140f6141c03683c060444808d000d10040100030721044041407401401c00f000074144988080c1030309201a20148042000c0783d42401e0003000c040c1a00b80045040f01d0348841086200004000340007250550000602c1c1c0240321811a140301d01c0c0f0428140341c9000b140001c81c1d0501049200280c14040c4680000712225080f00c240712002e94280129540d444005215010030351640d400504801e507140744500a00002c0100741c802c0c8000c0070f0076521125002498030300162580880c020034030f01e2840742111131854200f090060316003244250341c03200103090000d0802c003080610540d145c181e10018a680291180c1003c95440402c1c000c082c60300505030000c58807424603030304c0000118602410720039070954054076503150 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 472054946 1250 472053696 472053707
    0xd05092a150a0908071e060f050307081312031e02090607020904061404050106030c150c140f0f03090a080a050706030903140703020a02042a140c0717100c 68
    0x5001801031007075440842c05000c0c0d8449049510802d403a026034840013905003401c4c00c0c0104401e4800b9030005516403104420703556101c40070010000034000b030001a2200740036440643d00100c5613000804011010380e215058280340658460003ea01c6072480c070310307100c1c0c08520352920b10b168030019804c0c860144081800c0740114030f406407240d8207280118040c8615544004042140410b00c03504a26040c10821b001e882c151008440c0c501040c5000151540242581c18010300503035503004203402642c0784c3d0500d041d02c0400100d01400780022140c1e10440401611908036581e0b8040c503228000d400c10820b80307a9441c1c0c00610315030010b1405d00c00060010482509503851410700282d480602d04044440e202040d50000e07aa40c00028000e040c10f800180b8104c210344201c800780100c1c801074188190070071031020b05481101c040e5143c114018040d501d290f0030141f102c9a130509003014112810b20b801c041e5442078900e428207403298401010180700c580b65022002406101d03807810074200511 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 472056196 1250 472054946 472054969
    0x705030601141504090e031c02070c030b041103030a030b010206060306060612090313060305042306071422030c08160905060f030109060c090f03020a060302030601050d05092a 77
    0xf10f9240349a10000c00e01400c81a2000f51040d00400c1000a20a224481da69404000c00b001015560700c45491a5607580c0200c4114940c840d0a9a207110318540d910f40c00318070301420468140450700708400c49070300d00300090030000072280e80108031035154000281c14030401a050078040d4000d00104421616180115200d070600c5070070300852a50380c159440d045010700484890080c000890010f0b115505801183c0103138010b62602120a1004096881000c0c880f020400e55070020000100424004c0f400c21840801e0710001915124083d44030481405007414200f407d281a4003081c014003401d100840d02521558004191024800c0d52403040d84255108481609441e10700090b06a11004100b41d00c505000d0004e0041024914041c000b1382000d4a42c10000b69a071100001c0c2400e1102c508402c80342c0140c510b0700c0941c141482200a980000e103600e0500008000c0e4444507412885850b11403040c100180c400c00c44011014103216030040c030151001100354290300b01c266102001c078203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 472057446 1250 472056196 472056199
    0x1e12060e130b130f0b10060c020f013c0206090316020409080c0604030f0221120a0b0a0605030901140106080f061201020c070f05011106070c0c090507050705070503060114 75
    0xa07083d80c2c0d01c1c1144890100720715004010314a0350102408008100c10054000d2000c124403808440d2241d000316035918070000c01942c400c549400f24031440d400b4090021901903900d604035003548113180303948181c5400e040c990301c1100084800240c456414407910f078100c40c0d03c80c040e500e0240b901402001078080124080d100f15515100c0d0820401c81e00126100301c941302086d070b141880c02d4200542481d1044614901500070300b107900d040b4032001c804d0300c0890038402444c14182244500740a50502005002e080801d60720034016082d5507030b0025402c003e08540d61115078900e402a00301d401d449615084180042c00c030320062081e642c00001d203603440003c000c031000305559440000b840040400c5000300b025480010703069440070022800030140c456918509030150740e1100111030150101c03409200580010011442080c41481504050f500a00a0002545d11101c03054200d0344180c3d107810110b00005030b0102080b43c144505401003104501504056140000d012192658400241d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 472058696 1250 472057446 472057463
    0x605070c1a0903090d030804050c100504180b040e101112040b15190e0f01060e0108130c0f031103070807090b010207091b02210f0a1e12060e13 63
    0x1401100100142d51104000501920042c1783d2418083c03d09541039500b51114010340034049013604100704480c0400a680c3d44039031602c3d140251500b0181110020144116295042d5440e982d9035030050704c042d021894007420f55180350010810440718039400741014000309000d10500402a0307401543d00c9070300080789262a60720008403203581d007814100141c0c0140d40400410003c88400e170320800303a0b041d8240100241c0c603481e02c0d01d0b109550900c603500004071015044c0b426944608072861700403a10300b01080302c900c11941c135508509003c0d000b2002002c11138030100148400e0300c8800b50841000e8000c2c0850f0b0341071841c81600c1e20b00728094a0040350312100b520030b40d0791080280000406125004002100d07403d0342d0032004450407461030005214140d020038207440081c01d86251108441701c840c0c6040c40c3c048041000d178000680f031100344181c04c280340c010780610481403c000c01140d90b450011343e850646290842d003a54120265644996082020916111003c00c07c5140c0060a5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 472059946 1250 472058696 472058701
    0x20d02100e040f0c02100524130f20130302040b0612010b040303020c060a0c03080403031e06090e0c03030403020405040c0503120a0806040b0105161e0f0605070c1a 72
    0x40c1ca00614080015400c00d02e0040310302c110060a60144207150100c1e42910170891704c00c44e462090725016101001501111200900c036002c204030921440741001c1c002481c24010a6103000444840c0c41e02880d6040e10380c855902940072500e100071121524280e101d081032900c401000e034041d03072400028040c0b55550307a2080705948441c245c0d400e40101074034040d0a5a11030043c007a46070050310044000d0300c1040c1c601d0195180c84c2e402c8d10100440c40e40c902016400e203440071111380102420a905050383c83c40e00c210302154141c4d800d405510140300105103c4c1c54101003804035405108804a950480c1a4148903607070048100d80450b0b80490b804102f540fa58102510854216802564140310b03510342242804505009800d40c44002d0300d410300f4030b170303503100500080d5050f03103030740300e000950400c9115a40e460300300821030345900076403e00505411084080d80d42101c0c014040e40d21002d60b11020b420403866029199004429140c00d9140c80c1d00f83e960500c1582d8200c4460340d079412000b00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 472061196 1250 472059946 472059979
    0x270a020412060e10180803060f04020304030314010e1b0702030c1c0606050a0f05040c0309020918010f060803040b0a11010c080a05090a050c040e0f070b190309020d02 73
    0x64030040c00d00006002161034440c9800380c01072840d8800920f803401941e04101e4400580d01c10540922400096441c0c0d0380310b150781720b0404e80e200900055004080320014505a01d90b480594412442601c00150402c01e040d5020b0b64030b54164401803821580703c0030020603c00d02c03000400c004514001151700c614540c8006810803180e20328054004020380f840c25841ca480b4401c3c18002802808100101c0c0e441c2c07410b21101104034040c6440c4600c0421013000982080c0d441880071040502e40050030950540c0011080034040c0c416070707880d101810400c0483ea41c28440c450745260403520410002d46004201a205d00441c4501101940041481c02d00240200203c0c044143d00d80003c00122005d02000303000c40409891904810b450721000415030400040d8805d5090742090041c62a0300c640390800c000341c50745401c00000d40c041e90316110760030300003040110040c00c8880340300e64076600e54000f0120082c2c040840e1a0806040219920240c0c441004104010f5010f844502c601301c414403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 472062446 1250 472061196 472061201
    0x91609090c080f011d1504020907110115090f0504020904030f11030408031806120a02090a0503070b03150d080708070c050d0516050d170d09080d0605030705270a 71
    0x5010400c2802a0042c00002e4141944400411030f044c107141c103500300001544030b54503841c40ba4161000310301c1b100410003505c0c0020410340d00601920b01580b40804175400703542500e91480c004041b20701210410720000d40140a480d2030050704040420441c68280c000170b0003120040c00280900c400c0582c0500c0841c414605400d09001490449550f560740310441d41c2c1e00e80c0a00b218842581c43c0750325041ba075103016021100c1510a0a81c080300c1629004240002540545281c82c1e001d06001c400290340d4809114400003400d1007600f054a07440c00781640112058100050751040d17210400c1c20b000603440405407482c0701c0e0801021600c0c0d0b0003d1801003082d2410342c00c51a44200003201c0c22003004030026400450300c05500000035002d940b5424060303280405d640040201c0602221034103d080321001410101d4441100452555036503150511940d000702004140c49803a102c0601040c02d0400c02040100010344005181100d410f4000704920550002030300c000c004800032031306494594 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 472063696 1250 472062446 472062449
    0x1a2206091403070506040c170607030c02030c07121103010902012a06050f06030106170309010509040f1d0f150a020a031506110106080a030e090709030b0c070209091609090c 76
    0x1400b02c0365901c1181c180384e555034000300d5044548004509000c94001c0400024521090001d802855180c40340b5070160041e11050304410114401070065850010040113803c00402c012502a040c0c0d030024144408103200e0391203560f00aa040c000403c1c01030f41e018a100d41014040446241c91082e0a076100100107113040000d08001e0814091114202e18155100c1c000c1ca0120001c004455a903400d421202c040d01c485c000c2030381c00a0019010550055004042d103030001000042d0031044d4540c80b0701242c58046d003000b07005507108850740b83d21070f003005000c1e0000004401841100040d8400d000020f10003003020b00c48580200d44660400e02030f0b040382060056034818502d215407a031b0300007490702d44034055031501340d0308285000518000c04642d0006c3c980c0c0590f281c1100a0501040c094225000380c8100c0c10080052400008a50144100f43c001d11542111640c3d0b0f10a500400c0b0354000c001c0c081c203015800080b0409098021204110101e40d0700480c0494982002c0c109030300c844009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 472064946 1250 472063696 472063733
    0x20703031b0b0408030708070f1407020103093305060a17010e060f07090e0906010b130801022709150f01090b0c010509070f0305250302030a1a220609 66
    0x3400c00c3c0810058200003441c030031680c42da036040c5980c2d01c800301142c900480000100109002841800004021b0b038014840207006040105040381580e44440220240064080400302d0061300c008101611341d0303068079986031803138050003581050000113442526901c81e8425a40b4022000100a0380030341207214960400816100940b41109036519010411220f030300015403810004500c84048000040c05180740074000e15540e820b003842d0841d2607010b12109815203000003800916102c1c24002400c0011400700e07401c0226060040b001000301101c404144a50280d40410000c01080c1c4a4001000700484102a2030703900980140c4003882185c000700200d44001800d01510b100541015000e00c84070411104085d5550b0116451181d0032301004110b40c2141d003e481c07000c0030302550a0b50105100c070080c0d590036502d41c00a40340080d581c208464090014541780b03070440d154844581e1100c2807004104000d03100c0c02c0c840c5002c09242000802d0607031f54034840d500340300c0f01709203000c004001c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 472066196 1250 472064946 472064963
    0x1031e02070f03030509280c1203090911030f0a0b15040e4c050604120b07020706022a0405040503030411010309020607060e1f200406020703031b 64
    0x1500e0601801d07600c0c0b00c00c800c0c0e001c2410b20010604038040000c080c60341d84441e020140480b04010100615696050710994520b01103800108040c051001c80880144c4a40c881c0010702d03103440003000a81da800d92822500c00014010004a43c4100d00a02c2e0706c0070400da03002441040540010b014440c030001c4c9000004000b20b40422401c5a003542240100e00703032601c1e42c1400308444040540841c0720030b200d01c079a205d00700c1c90000079071f01c05c1d41500c41502d21840c2510b030130346c417070700070580c01c3d0000e51111001e100032030221000c3c005c1541130385800841d0342c8054020313103082180296681c03415000b00706001d00d180040b00340a4411340c28034617070710000400900290400d41022039494006541c25981c40c40f00c01000780e070f1907009100b407400c8140d01604040c01d02146840b8400101000505401c141c055501d02008464038802001b03001c0802c950001042d01c60301e042c4440300a0070102202035400e04000a0203d1500050340f04210b9a00d03150500d41124400c07010403c400c3c030024014204d80 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 472067446 1250 472066196 472066207
    0x50703031b091706090a150906020315100e011b170c150a02090117040302100c081e0f010e0907091803080a0b0a060e03150103060c08070f05040501031e02 68
    0x25030060725a8119070380400109550307030f440d0280315203590054580009a502c10120400080d00280342c05000e4001c10000043d0740d80c25031150002e0368021940b6240f0280510300c00311051400e210111040d00c1e140c0b40c4000e000e400c0b840040d025028899110240c0307102600d00004000d15400644044c0340541d24032031302c60002c024071a075102c0e0a0001003034a00b400742c0004590314002d1094510a41050b0f42d0b0a0b0354035130108000c4001c04001d8402e60440c042c0c01d0050a4840041c000d9000c2500c5503601c1000c585010022400100303040b518000c48000140140001d43d5803030070ba914192845622920a00d80301d061030a07241a1003a03200150302c0d42452b4800481004412900182704e0281d02d03811207a41d90819054210349161480c10b82c4108000c8003130111503c55240c29000714030190403504042108011804032503026441190f07001d032518200c0018030b0340440380e07603003012050800c4401e010051034090200d002c0c90041904259450064200200034600c3c40944842c00e40401c542d02c0c17 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 472068696 1250 472067446 472067501
    0x9030c19030606080f0601090c110a0f020a05010c030e0906010c05120408060105151b120c07080709020702010206041e0b0c12010605130306021602060c07030303150e010605070303 79
    0x40003a2006554003894440d0000304400049401c515a41589010301b80b81c1c0e081041b40802004211008000c1050b1441c200c071900c002000b8100c0940c0c02090340c5c1c8002c80051041040825850b00520b041011080380440040e401600c1400c418008070f820208903640c6100403208080982d10140c00d80c80358591000c400103919000384190b03141075094902c0c0780c0e20b9009204201c42c400d0626041c2010070092a080910070350b643c0c4041d28454020f079003000d0400c440460994122000200c0c258120030700c20000e4120030001d0710000c04c160401941407154640000c2d4641c50000e00150440a46900030340c140ca003011402090664000000c1c5c682d03040c00c04818074140c0000e103d5422040302c0301c001103810b501407410b688a002c0c42c810841d00703031411955010069000801f0414207000b9544c800c100598407a0054103c80000e02c000300501c0b0f246003001000e031040401d44000c00e1741c504c18244041080401f909054803841c0c00d1442e0f07508101d1074110f0082000504120b003580c0101d42145a6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 472069946 1250 472068696 472068739
    0x61a060a111b0906060d1e020901090e1e0703020405040903050c060618180102210603070b09060405120f0a23070f05091008100c080f0f010b09030c 65
    0x70320641800c6448101d011501e01c9520491038028950004907480000c020b4a4000e00814051400003c042050b90b5000c104003240c8207901c4200d41500e8010400f00419640301072500c004000c02c4400111504050044222150f840245d0000110a040015a80501a0701102e000b000d010700204490181030030018842e0b004031150520602610010919514214a61000013004e00440011030384402c000c11005402183d12020655020302c10020071102030405c1d00c00300070240c0300e510341c10b01e001010941031850310340081050820138000c101068684105030b505076030050301e139503d0b4214441c24031440c02510414020725886464540804c000300c02d1004640c1200030500c044c510202d203107803551242d050780940f01c40e54000560800061400e60030003a08011640c1e0501416501c0325051410490201c0c0804a05074607040070ba007581d030f480a00070341e001440680301c1e070700e504184804122218041c4945107030504c02080c0908140c0c1c06108103190f1800c001d001201c0c0010a244038840f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 472071196 1250 472069946 472069967
    0x6022104030c02040e0a1101050c120309100e0d02030d05040804090e100e0a02091b040f08030c0c01110a02040504060209030316021528022113050418061a060a 70
    0x11414012048046900041c5202c10590720614012207204d007d0011222504004c03c0510039210b00014000384c0320040300218062410b44000d020301140402c1030409a490703017100d8603115441a51410f5a0503030100a0340d0a500c502500803805440e6402d01062500443c0c019090031032800704440403079540010701c03242240d00600e0510078043d201c0c0c00c007038171a00c50900180d004103555000030071300a00c5514507004107540d41c0045060030386503040003c0001e2584c203c480c0a03840000c007007015402c01c000b0301282c3c5509280038103040340b00c4603503541c0320051484d0081c025502ca070045000c10600741c05980e1040c001600316611100450107034032030450200c1081c1e00454212880307401c244084011590952080e45003034840b5001080421407800380800e4040850185a42c0031510006c0c10711900c0d1040d140854040e145c0303610003100721131070460340e100310f2190745800d1621201c82d4541c003840e01201e0300b04400080754142003441c902c8141c20b203208a40e05c942d0000703400f240300307070402044071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 472072446 1250 472071196 472071199
    0x3022b0b01180b1602040f020c030d11130b0a23042111100309060216050606090106140a0c020402040303170c03100302060d0e0d05030a0c1b06022104030c02 69
    0x80d041d00310840c00b076003a20b03801990800041008444590410408440c506510180001880028504004040342c000001208180e0000140391040d07002d18010b071002194000c0115203010012400308207146c0b0310303201e154100d52020038860101e80c080c0c5900110000200356260014440b0310b01c4400c075501030300468070500e4850000c0700103000c150316a05410b035440302507c241c1107618404c0000842e900b85070081015103901ca080c002030503d001904c1c0b951410010341c60302d85001d10b0460305000f4018642802a500b900c0100700f503c0d80450504607110740d501495a0f034140306401200c9400760004041c1d00035000007800420540e01442e411076901c0600070003003060b1101c0f01300c20020701c403c1d00e85410a000d1242d083c00580b4040b8004c0c21032403540000007031050440e544050400e804038030302001180f800700c10064802202d0103401c007820070030b251542001001030780c5401c1e441c2c600072001d0603003540400c0d1500349030090441d610401c424449484514501440c0061200c80d0450007203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 472073696 1250 472072446 472072457
    0x402010f0c0203100c17130f081c0605010f03230601050405090c0d18030e09190e100513050604170f030c031f0b030f09070909060b04061505030703022b0b01 69
    0x1004480c0307140407018000c1d0b413032980e01004407c590703c450200007846141601c40fa8004c001000b15200400040350304400c0d80c6c18041241c500e40710014218500c03440040050500300787d401004007000b01044c0301c00d60207041c00c49490303072907035401210140540d0b00406d40285840c1b0a015041082c40042c01c0e8041d412002401410000355800d050032500300001004107040c41c0904e591340c0340c0007460681c009140321400003483d0036664030809540c181804114160001e42400c41d100c10180100c41e4800c1c0c030020205203032030450b0ba825965071001071024200d058414040e10122000000b210f03028030700c2030074040e140d0611544d009155403007521301c00c0700341003441d82190a442031200e0100850341c148071040c0c00d540d100038101e5652540100300f03c40600590034003148010742c51069203111400f0300e8001410802840034441100c07aa1741284800440c00c0307800340c07150395001046075840b000c14038002d030f103690000000e5442101502040140015a9586401246801ea01002c0c2c40f9000f680c82 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 472074946 1250 472073696 472073717
    0x2705130504050c0a05010801090b010e0a0308030a2904020c0c04060e09070801060e060111070306020301090c0e0603010b030612010b03190b1509070f0203040e0703050f100803030402010f0c0203100c 87
    0x8100a11380d45100b41d501181c1d6800040107500025440740404550605090011804031704c006900c00d4001c0d082101d20b03003004014410040003600c2481803848000e80d007a090002c1d0201c5068506006400c800c0c030403900080c0700c0500410074025810900c0d80504280542e548811345400c00313502c1107234001d2451060910014804a050082c074003124040520303015036464280c011a120034100c01c400d0214841d07240008001025032000714001c115208000541c2c90f01c49100500d4104030801d00d5205540c180014400f5000800c11250010310860b00400c082e460001c1141c054042075002a6160040500020040e500d2040c0d1b040c609206603d01441591120180701405020518403a0042c4014000a40d154040c41c102c40c201c000301d00449007410f6490f140002c40180c116407081c0040d440360140700c2c0014030100e2840e00462701d542d102d800c550416442030303500d0000400180c10024010201680c0d00c1c090042c48032a10707009016108140103070300c212005402c141d8100030020340e66885 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 472076196 1250 472074946 472074949
    0x160503040803011518080609010e011406010c02150708090f060a0206011406070c0803090321090d0c08060901050f150108010e0709080607170c07032705130504050c 72
    0x88912440c1c0c810010741c15a424000c440c0b086035028100ba6041c000c40000844071081501c035035000802d1910002c0c0001d242c2008141e01717403814602a1080c0d6810901d81c2c6284180010740c003070388003c0c02e2910186c0ca400305d00000380340c070360381c1d46c105855854001209010302a01e50000d100b51201a540c3e0850ba116038814400648a24858480141c10000c01803048601440e900060800c00a200f44c0c01c14156889a494000c010350200b0f203154400207142c01541014024444003003130714042d14890300342c1c9030310302d00c3c0500c9080485480342141514080400280381c0d0030710081c0040108843e1945028100d85008050903a00c1c840e01d00d00c00d10000e01100341d00b000d004064003041e036410180d6442e00c100c1d0300c890840540b85005001039100049003482080000c1403240160f5034440c61034030300c4504e8034401e91030050580002c441040110310b005c6500308906144c03540781490000c0c280c1d02c0e2148007088402c1181c1000358010f111b03d01d20462200d464102d240550302031000d40d01440100340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 472077446 1250 472076196 472076207
    0x70e04050309090a0e03130510030507140310150e1806010504122907030c0e0105070f060e0d030609060e0f06060d090f080304051915090213110316 65
    0x840080c400d034000c02c007200241c1041e0a003d50050003501011840041448540e800c2d50054456920380000c03420b01048a45415101c00c145280541030822071420b120340c00500a0601c0c010b40c403400b40001002c140d040f04684401c41c01414003c803907198005103d0802407c540c400b803001c40c420384030b03c081c0781d44a080900507d801060140c403102d2810b46001c482d0344054180050070350300300f1544a048144402000540304107510311501000076480c0c1325034003802b190f00c2407028404200c103403848140982d0300102100c43c030603000041e0341010155440d000020b80760020042e81c090080340c500b00c0d040340e00341c0c0100d0151100c204040c051140c441d01080c40d0310a040711925400d0301d03180082200ca0400304000c5c05415800342c400715000101d0340f15a00044102e480460b020311001040205211041c04400d860708140e581e550074603a9152116201850040301c00d4406554070344a100071951804210982803166440031300c00c0d107043c4107004140707800440d0704643c5030b1044100e20b80d40d5403094 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 472078696 1250 472077446 472077451
    0x1404030f080d051006082403010c17100e06091801060b0a030b0d050c210a080702010e01030e060c0a0201020c06010902091503250c0203012903070303120f0204051f02070e 75
    0x240d40e11b01d000e90f2460101640f10851510036a142c2d6041c10819081e07807401e02441c071500d10180c0300c903800c80c9042c107800c1c80000710042c19408060380407002407150380080e8174a10b400c9603044400e0700305911004030b001c01c444481d1218101c00d610303214001800c01882c1c0068202c40c64152030802030003e84030700380400c00203100001040c3c0c0c2c1001c9402021840c4c01d003480a00c408120626038003072003820701c02c40c6c0703810381403201034604079400301c0d0003003c560b44180c40c59146130f4280b07001d00005803030083c076980c1c810026000400307614000c11540880c62003507050740c90000c100d40444481e96540d05184009501a8140342c0c0904d042e14440c03540c0800d40c904072030280d40954114040b2088145039401c444e619802074108001d400380040740566002d0146607200305407c0036040116012030450700103600b540e55018080c2e004102c2c2000446d42168588244000c500c101046601c0c9138a0700c0760084c895a04041e601c0b00082140c2e012054110303414001c0c000281d000c95040365100c80460704d850a08 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 472079946 1250 472078696 472078709
    0xb060111071d100b1309050c04031e050327031203070504030f02040219080a060501110d050d060308031e0109051003030c03090f0821191404030f080d0510 68
    0x1691010300d488100e407200b81c0e912202e0821030205803030329010461125480944548841c0c1351507142031082406a209007500804513500345450b1030b00d10381c1d464140b0340c54104c490f030090100c1962181030140900869050641c44800441c540d10400c040000a0402da035085000c0d00c64003c0c105040600038080b40e024542c5030b15110f061070300e581d49103c10204482800c0ba0480c0d0203111180b4080740b40b806408041b061307502c8000c580c0c0741095005045410f6584401d041103c0d20b20b10f02c44505c404200e1404030001850160758800481c0c0600e00074012030707800101941c0e000402c001c120138490107820034105d807031030018540b643c0e01c40c845410b0702d10a40e58101c1c0220001300c200000303800381c1c842c400f01c6441b9041c42116541e503200940700c003000719400b440513600500707108440030b00a80781c415200510545d5042c01d0890300039545443e10340d50895036080c0503c10307680004c9040f6000580e4010355010540302800d05032407900c855107401506800120600344008240d1001004030f44030140d920 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 472081196 1250 472079946 472079969
    0x280c021c120f0b03101109010c02030111040305010c081806010e09160f050a080312010302040c0c0b0703061a071505180a0f0b1f030204090312090b06011107 69
    0x10510000090080344080d00c205004001141c20a112a14000c1080300b406850300094aa68203005143c20a00120310b12410203240c01c00400b25a802d400686408107420f1804550518032803011038018041081078203600f001c0800e0020230090150840001d8040c0c1d43c1d0b9640032074607102d400114090340c04e10b0070340c0c0982000c0018448822980c02d100d601142c0c4104458862102e000b55142041058001c0d480c050b828840501c002d0510940074002000e41000452800b90040035090880c00c4c18000248034035101c860416865115200407680f0a8000d8200c0c050350900f103c025005115912510b071075070034103c3c90712017840303508815106410307009001c40d240102c2c03000c01c4070300504008000d4040d0a10403394891030300d00c100022a60184614014800c0e80b80c01d08000c0c1e01e40340002e244040540920b10702c484407030030000c00301045079411b03a07002c220b100180c90203660380c0b5108001c003110310b86086600803d00c083c900c0010b014400a1702c40d00700a600780d00c880c60300c0e12a5401049400e12 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 472082446 1250 472081196 472081213
    0xf07020f0402040924080706020a02120f120304020906042a140d050a0e01060503030406030903020a1a040201082d060a0b43110117280c02 61
    0x422103115008210300500052900d40c0b42e410322000c40d402c031100c0754036040c9051030700c0d8a02150420954003030081b00e40105445450444025078039004250000c0c01030340301d080d1008008100304084100e0941c00000c1d1031078101520500d0081d50400c8500f40c2c8511802400715005090a104404081e0701d6824502d079061702e06114500da2000c25003841041001021641c0310a56402000d862440f01851004c10301c2d050804641d0141e03820b14185d2002e03a490718004000341c1d50004222000c60724141008280e1010368101a03003004a0040058465410782c0c0505050702600782600307118a00c00d072507004041c0c45030510f84604442140b2400700c00b46a00c3e845001d07110070401d105a1000c402800c01c50b11a86480c3c1c6120640c01003104000e03492a00b0072008a80404a40700b5a81e643d942008262030310700900d8072900c040384075113001d0162400920245501d0b44200c000640315140c4e00d11340065800c00c1e200d000301112980c40401d144a0b000704900b001c0440034000d5a8036914030360300901e20007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 472083696 1250 472082446 472082449
    0x90302010f0c050c090c090102010f110403150b0d060b09090d08060613030f050f0f0604050721170903010f020c0705040b01051605160e04212703170f0702 68
    0x611600000d5540d4812a03c0590f8030b5680c20001754410b00d6000d1500d03444214000000e400c1d01c2c08542e511003000d041101c91481c1d1492076003668201c0e6007080c40e188941c856240440c3c01002030058035a0400c8610b08050140521a040b900030f1840540d42e5814503038581134a075440d41c950f00441400224400c022962a252000c0900ba100c0340440603416026500d689080980094200440e010380040c10083c0e000101070042c54001002c90300038181914140d952151115410301440242c1050f07401c8050510b030b4010380014486920080c0503038000e01414500c9826041180420310030f60030301c010302c41c8000c00ca000740d40e9003000c11402001c480e030038041080058143d10407018100030003404540c080d82d4080d254100558090b001403d0190701c0349400d26082c0c90030307400074803194043c5801e100018400d4540fa00002da4900400d62000c00d40b203408540446924114031030400c00d21005070300e0040039500310000c5902c11412034490300000380c0900c49500400740c2e4032035101400d10011016 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 472084946 1250 472083696 472083707
    0xd12020102040509010e090106150e011209020603131b050d02041a1f02060c1606090c0b04060e0f040c09030f03090909030e010e01020304051e0303040b0a0503090c01090302010f 78
    0x1100140009030906440d84040f98030280c0c00da101b401548a030405004c8124000e118104c050b01e11158400401c3e803c480c0050403044400c039000381088016200704200d04982c0c1c0c0a0340500ba0f0041045179642010003560040d802c006c2c40980d1242200136481ca40d02140c941080221640942000800400c3d6001c200003045c00c541024905c42d03000341322094658a28400f800c0c004503100c03100001c4a1500c0c002850903000070240e6080050812040701303403843c2c0d50740c043d42041d8800004140766009203030013108542c007035011200c240c00104004c10025003050b000b00c00e00609031006a00310320640200b109450001c0840c0c4003040c1c94100500100c0c10924804100380c0c001d042c49100d95076100b259a00b11010984d090b400600c0210003071031150380c41900d0b1185180d0034401941040d0800000402600800c120003142d000e00e0491031011391000e00503100100800f600440e08ca041c9200054000e43c000c486509042c0034482c065009903002c0c50300401502e406035150000c441028000703449 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 472086196 1250 472084946 472084973
    0x415050d110406030c0e060906060f1810050a03050c03041a090708070b09030c040915090320070314071d13060603051b0406050f100c0b0907170105060d 67
    0x2007880703851a0007001516a0f001e068010752180425400350f500c0d100b05030364110b00c01f9180078410880c040a20282e5a200c500750340c2080050042256660240c107484a18040101c607403035002420341c0001005150010003811000b00583c0f4103100c1ca66881d000903485101c221401069003c50741c080302d00001075641c00d564000082011604255140c50605103005816402040340d05030001d200c0d1034a0409000820845009440500840d0311907039034044140001d11b1509244c650300d064900626100344102940400000c031a540c400f00761010058a611950200380e4045003038a0030640c2e09100019030700700b1200c0c2080080f449034006061454100e902822001c140000f400a42000c0f504900c1503000851080004080220b40544036a6010800b00d00b010b00c00e601d07004c070800164441e80b10364a06070f44100c4e14003044400b0510241c400943d11440500b2800c0030808200600b600040d101e0150350170390520b210034001c004089404d990b012a821074000100f1000e980010701000c1e0411f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 472087446 1250 472086196 472086203
    0xa0906030f0311280c061814060d0e0304030b010b0a080f04020109031401050906060312030a0b180103060906050a0203070e010e0301270c06030c050406050306060d05090a110415050d 80
    0x2103501105800f2441281850f00810065a41d04810740c000c110794840040000d00c80e82c02c01f244088018242c03001e071602180300e41400882d807000d404441d603403104100c40b070b0402100010422604288025075598002d4041160120345002c004100422003e041d03404160543d9145200c980c0c0da0707008812811005042241844402c42021000a00e025203540c2c1c0241d25000018413440d004014500d0a03070017034242402904030400400803a60348200701c030f512840801011607030b00c0b0b142006c140c5602c0d1010249079000b503000c0c00130040280c1904880c5040d80142d038240416141c2003803400480c8400d0354001d01050105d4402c0c0e407154000c1c250034203221001000001d88900585050001e481c0c11114445040d0b00194624100400c0030341c0308001e0030711440c0420203100601c0004c0c0452103580204400d00001200051160752034504035103207008a11001c0c401401c040580e9a6940320b03080c8225101080c0b8409150b140c10b0510540b262004503100301c0303450610705028007a011a000c203055 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 472088696 1250 472087446 472087453
    0x3150e0309120c0a05100909020c120a0c03030b0402040b0d05131b0602061b030c0d0f0c03060603241e0519030b0a050606030103030f0203120408090a0906030f0311 72
    0x201e00035610420120803003078441c0d000c0c2944041040c2000031000550b0000383c82400f51101d101c014581c00451442075814050300169070b40d15214030980b5000c1400303841c0254682c000740404e1921b0303001076031030a994820303181032114020074400c001c1070340200e006070700048009121480300c0b041c26410081d0404280750400390007c04648a0030f0511080d143c004010344840c200800906504000650740400c210240b1a1b030390061807125030b15840080c0010303401c1c602c04140c491046815910003820f04a40480802503003400c500050044c0503540f18500209141400103040e031103111040c100341300d0036107440304805800c0030801d00007808a1481c40485400c03a55011079546c440204800000e00c4092104000b80e140d880c141f0140100100300810042c100780920642c0c1d02c4610a49042d240e05003007121075980045012451401030b50860342c2c1e002c43c01014441800381480003801c2511003070390b600c0b00c000d450302a50700540e062440001e00c800840d000c1980820300c01c040074080b200d10355098 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 472089946 1250 472088696 472088707
    0x1e21040501020d1b0c08030a110105060f090903040b12060a14010c0201050d111206090c07030e01080a0e0102030703291513030b01091b11060a1d010c050c0d05030103150e03 76
    0x40c1741c030f503140c942c10110041e40300140400c00c0c2c40d0003091500420015500a0016140001c0894201080c1e0011580200049404100c20305014020381c0d01401f00d580800c1d0701ca80300300000540b080d0080c0d514a004180c0f01801281011056410144040c01a16540c0096a80da40111603560007140385000b03032a078501040100d16240d90041100071701a0880b00b0350380c03c1a01c00c12284110141040700d80702d0081005000080c0c0043c84000300c41400d0030030100c1503035620f034000c02501400103e8442075100200f0801010f8040c1d01080358805042e8040c2900c076440014041ca42da0500005c0364040101e110f0408514501ca00a00d0001c01c40c03074403462202d541e581d4240c800c00c0300307800c100b035200d0b00e480124905450f102c49162000c00340b45405052000f007505142c0e160b0340003400a010140e140c14070205030240c814100e072001504a8001c010340a286e00d00100542c20040650745540035402904d0150361042d400d803030507241c00c00e880c111900d0030301d8001d100520300042100c5071400309019 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 472091196 1250 472089946 472089953
    0xe04052e020f0301050a0902070f06020307120207050105390c0109170d0b03010b0f06070f021018150905060c0a060614040e0109050309121e21040501020d1b 69
    0x2d050302542c1010826107a50501081001c0c69290740c0204151501c1441000c0105a42d45408800245c2241b030042c1c1e00d445800080310034400301c01c80d00b6001030001402c2c01c204041503001c10301c41d900c040d600d030b610f5414200104001d0500c2c5880c1140265600c42402c1c0411540002030107101024400015400500d5a405000001c1c00189410030600070480500740030035400307110032048044000b000f2086070f603400030700c2c000c1225542d2400703074002240803400c11087d07502d4803201640042c58000d107a81d087d0030040c5282c0c0314280444850344030317030030002d020b900301480b2a904d00c92a44403411500d04040074070082d50018500d5000501c01c1c0c1540c040400c00c03a1003813001809035441d0030158041d0400c2404256a001000c1e00c0036a071500508401082e00402a6010381c4400c58a03040440c1d5a406070f0751070305001e081c140d01c030720040d0080321051043c0020b281400007155600000403c12865501107030f400b540c40303098056085007680300f10300ca00c101c5e00c8018103110b0300d0004a00512644 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 472092446 1250 472091196 472091201
    0x5011202040c0e0328120216060302070201020303071b1b05010e041a060a05040f09020315090f07201005090607020f030403030c1e0c030501060b0412110303090306040b010306060e04052e 82
    0x201b50f5005030b0851283d101c00c40c21490080c801400881c00c2c1035260501c00e84c0000d580303103c0108200100403500c801e21580e40c0310220803148050f00484e258225001c1d0340c560510880131441014003055065410301c001d0f0a060041800780c2c2080144070074481c450200b4050554030800d071042c00c10800700408500140b049000358054880040016220b01d88440783c02e030501100c2410ba44600241800c000b0840c840b40c88445e0301c4101403604c90340e10701c0b041c03405003035110800c1107007070582c000d05882c111422015408203110b40ca2503001c640b40c6440d100c0c0140d844074550304210100390000c02080c00840e00410400004502c0741d54940e154500e507450001e440c00320504115400c0204007400c20500c1024000c200c00303003000c00081803500380707000d51080c1580400d100044c808400d1146444c07190341d0130300503290f014801400f5a080740c68185403031100c80209000c201d45d42840c0c0f0340041159840e1800c414820f55200c0020b00f03901442a43d40c01c010a603d415440f607090b02402180c008806c2130 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 472093696 1250 472092446 472092473
    0x8160b03060f0f180403230a0e03120406020a0b0105090c0301120309120f12181e0e190509030306010e0607051f0e19050c150d05011202040c0e0328 65
    0x90130712000c60030103242c0104819621000048411441007840c101520b2100848140310014102641c804080802090900c00c0c440d44901e004000400c1c0001c45540101d003101c40180308000b0000540e0303c550400c0b4040700207451139103040e0028401480303840540f86450940e170b03000c1d023404803034560307079024200c074a92032100219410b0019081503010045400c0c501c0c1d00f02841420320554071483c1d000e4000d00002d45208503d4508000b07100325000726000c000d0000503206103007051180340f403d80341d0740c200000d17180000004c1d645003400060460301c0c00b0041e240500016510240c03e160321108024041d004120f09403128010ba100c040a92501407840e0ba07041240444046041ca0b48050020304048981e0344030b258901d000ca11280006101082208080c00c04641d400c440e01080301c0440510701600e52114140b91400002003040c10031050302c820f03664401c95040c040c502c04080d0858006090354925a015800715142400b43c5c0361401c428130303c10103104440021b1844036100d240c1d0702080c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 472094946 1250 472093696 472093729
    0x140d090503071101020c0d031d0a08010c0e0102070e011203050304060e010509061006020c1305180706030204050a1520030d0f020702010905060301082a0d0b0108160b03060f0f 77
    0x165810b01a44d6010b10003400c3c03660b82140d6000c8115442d80300030b07001d002c01074200c48002000140e10403c40d40d411185001511a00008001c4010018002f40855400340d0746907001d4810508002482c01c0c0d1644014180c620211040d04070078070030b5074191550b801c050710803111152540050385214030309100382071140016100910250405914058641e1020340114013150070103440140b00c0e484081842c1c1031450384280000d030540e15640345600c4040d0400c24034086000fa804c000039101e505401a2068800031035246041c0da0341c40781102000c4040c0051080843c541000300640e85000c111110aa010b101d0280c80c5012210061003044030403480c0380208403940403518506650b48416018003518040d036620740b85506082c138580d0780d0310a2524886c240c11160150102c510b501004240303d0810140650112031094a4014812442405201014411140c5849500040c60140800c684e20144180d14507158074040c8408425003060702d98101e1040000c1c2c0c80c0344d032a81440000d45241 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 472096196 1250 472094946 472094963
    0xc09020f250213020a1b050c10050301060f05090f040f0b06070b0103060605030723010207150807030b0303030c04141c0c0305010b0f090a0b0112050907090516140d09050307 76
    0x66510403c1100103004111180582c41031113140c6455401c030501154181d840039842d142441145040d40c60188041c0940c1d13040508800782e601c00c90f402a010754103071030840e120300305150050b50707003203600b40654486a507116081103c005036a0a1551001c0218144c9100208051940001048aaa201203c203c1e44101150010024003400788508406040300b20003410400303141c1400141000790300c8055075101c1c0d00c0901c520502d6802048004020485a60000c42d40030148102034a0404215450300202e41000300f05a05440c01000700c91052008030041402c1c0740c1804018403038107048008858001c600700c15110301d5840e10b20005407a2602c54210154414210f00c2c2484c00e45000600307050182400c1e060f00c0d02da40d0f4071109942e9020082c00c0740054090410700040350700074201003540580078544400d110304880040b8150041e03880300441405503848020400710088451320340c000c0050300c0b1614510308070700359200500040c5140180490020786c21784070541943d0109204494516 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 472097446 1250 472096196 472096267
    0x100302041d0a02120c10030f241e091506181211042c0c06070b0117030c0d02010c030c0302280c061d15040c09020f 51
    0x509070094440022078070704402120169008000da4403901c8100c000c1c03040d1020350008040c03200402510001c04001066881d10204200001d00200352220f1340b002c0e45820b010180c20184292191607044110001c0014001881c19a803005030542402a40c107001c41000d90006000d5203038050042402c46140b040e0030480d01e810000f0380804030440e8003a0f0f2a404046041000841140104240b0354101d0107054084821900040c0240300d42c3c0f5080c08289000314083c00e240400c411003040241c2c01a04070390461380d0244c1000290702844000403c000710110060010080300c99100040f0145081140e08222045620a00f0000c88250a10050395208100c08115a250151509812090030704510341844c0d8940c221020039003c1c14a036114011640b03525200784100e2868070015000741040024004403051a1071030442841c40d030401d4401c8010403c00141a4211240180c0d0303c404140206407418610f07a000c0e4224942700703a22524280b00c1c44604240e40f001d4140328040807281a010034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 472098696 1250 472097446 472097449
    0x703060e1608120708070311030a030e06060103020f03190e0a2001030b030a0303052220030303162f010b03061005100311071403031603090308040326100302 69
    0x8a082d034495407a80c0d00192040d18440302900c212a4010340103000c085e940c00f558102640c2080d001503c04e42c0350302c00002e4000a00e5815807040c00400c503400161007640d2110801141a8001e00c000c0c2e1822220070070215424202661201104c11007074540890f1001c54030640e14100b0ba40342600307849050f01c40d01c5a043d2004100740c8071101c00d4090804114603074510340442da03035004006006040c1652031012070074060003400903855014a40b118000c0d101c2507464480d40704118101200009801d210000742545000700c00d4900c510704240b00c10000c030a180c0002c4403041d141507200b4021001110089d90030038070381060a0125902c1078004200017160105151030104010020450401030074010b02c5a59690411400814418070340411503034811401d02c034462045010041c4012109155217040060104c0a18451890148641200c01c103020042d070540d1002c960040000b0803880001d00001d024029200c0c01e000342d2030b4030300300d01a04000d11060084007034685680c00300c412442042103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 472099946 1250 472098696 472098733
    0x280f030b0907050406060e130f061203171b0f0c060708011e03050318060c0a060c08010611122a0105101a090f0114030a0603060e0a05060610020703060e 67
    0x2c00f4181c808011191038410b00406040310701c600544a1030741000c003190700300019004890406070007070701080003699500c50f00010780020304003240498018070903805c400303040312842840b442d4003426506501940103000318159000d11480420243c080c0420101b60303101700152482019203450b402c0c5036505201c0d8040c52052120180300607402d09140c1400019400301c1518803240040b07550341d82c2406c1e80c00001c0c5960003101400c05c21407154450b1642404260b400c001c40511040d20f8051540e601c0f284215000a60302801004c03a42c40140d46903140300648000305400011000071560340c3d0718428400c10701003000090440d1a80d110707000d0000f840300c2800000700030102244020301314424000201c0d00d80c000c2c41151489071803203440b080c20a03405803401c8064074a01413030b1a5600e16004581c0d1004000300c2c00705885ca82d2902d034011010007000117460169941007c0100310955a0342c0030061201007580801c0704500031040004009440340c010420b10400f01c101030842940c0010707030102c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 472101196 1250 472099946 472099949
    0x15120313031a042001020a050a0b0a0b06160813030204020c07060206011502060604050702070b120916050f090604061e1e12030c0503040e0c09041109280f030b0907 72
    0x7181c00b140d400344030004290500301ea888080d5a080541d04005007001070341081c41002e000f070708074000c0303282e080c2c00c000021003020701c40c120b40c000800245084a06000403406854407178500c9801804d004004102c101014014500c1000403424615031a980424160b8206403040c0d03846e603009103002e201d8981c0500c4840c2c0034108140d0441907000b0100002503540c2005084503001e41d581d08042100070b4402c1c400000035142900501c2d99031070740194480042001280c0401703160051040040c04007a801c2c14040464000500481c0c00000003402c00404c0403010b041a03600c17035541d00c00000c0702c04501000c0d03c80c010810f0207240080c1d141683d00889407200c1a00345540079039010050004140700c0c4884101907405140181e01000d061038107a1551007913421540e03040200004115202310000d00074040c91405450500050101e4a0f0035401c0340030781e240003540000440380c0e04100d0075003c0d6140540106008800c8991551200c40704c0c862440e54100f50b880c001305400700160000100b04040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 472102446 1250 472101196 472101233
    0x17040504020a17011a0d150b0c0a0c0b030c0a080604090c0f030308151f02010207051c020f2803021606030207031e0f08061314101a031512031303 64
    0x14144a00030162054401c14090000080d03407001d80001d400340c0b55014030060601180308580d01c000300c80149d81e60f650468030450306c07448420004035500e00540242c03802074034a040e805040c158207100c16143d480004011580040e80c503081c00f80403400c684441002082e401181c0c503011811424003e00c480c000130014070b42c000b01e02c54110020340f201c0c40b0400445010706507280e0010008181240a0b01c035400c00580648120128040c943c64102d08500140c0348a40850364014841c07039a2544401c107400c1665400740213455104141008120030840d41032092054a840495448003424424a180c0218000980c0880e07400101a00001c4c0040c0d040070154030511054a05a0014481101c80350602d080100d0300011582d2910381042c001801c1c10b0380300003030040720920001c0000302502150b452401ca0740007400040c850f0240e80d0081c50b8200f041511600c0c65554200712040540d105002980094a980c80f44504480c140041c25650780a961404240340c9107040030303090140d0203046c09 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 472103696 1250 472102446 472102469
    0x904030801091104210312091a06030115031209050604090203060f22020f070203030c0d03110901020a0210090b04150306060f1d190815010603060f0317040504020a1701 74
    0x34017100c0403001d03401034a42c0d00803070441014030051404440100428142c2c8400500380710303282c01042442c9403c80400b000c44254510a075840f901094269400d0107000c41c4080406041070010403c41100303180358000b14200150640c0d901d9001c0741040c0e1099100341d020540c003005100700c5281c146240b203840c0d04215001100030805807040c94004000030314040514dd800550550301944000039591185d80040c1034035254146913113402c0c0c48aa2120056002070b180003201095980f81c0800da07035554406038018003a440c42c0d6400d00003c0080d1031625014415000f0000401260300b41c000c00103014407d1244652410032071020303059442c0e540221081c81600c040d224051948040c02d4840e820100c280d40382100200f502056446d00101094422034124002c08100301d140012100707403d190320007030007445030303a0344008030102c0380c1d94007841c1301c801c42160040021030284d00c06144925424001d4a141c640d41d500060200d81c0078112100c08281c1c08184800200d402503000c0d8010680540c1c034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 472104946 1250 472103696 472103699
    0x10e01050610050d0b042019080108030d1a030109210801060815130c0207030201080a0c020d050f0d090f05060f10180f0903111e12180904030801091104 67
    0x141c8070380a05065060805c0d42e450014040740c0d10760b0000c1c4040107405c10a00141d11640f1028600c075030000010199441c03c48003040d03020352254050504980b0202c0240d400c010350aa035050203811501c004115041c0003c0909032265000e11600218a104030310740e504a01001c0c00154900f21010044406d000560300104015500f003c01e5503032095543d80003072083c1408100241c05182250b00d1240340038900300005103503a80025880060760f000f44c80d4498141c0d40d078440c1205451400e124140142c00c0401c00d681c4207030158024205c203400284c9954100750040344004100c8665680030398003001109414006c1c004d003481a0b6410680da0003581146140c046210f54280c4003911817075010003000c024048110005a1161803000080c036014000c00225003401407640740b189944d903896000c0c14206800d15940c05074544c6600b40e2250240c98415210382d82c200d8250000240e030340400c69542400002565000d00c2548280e100303071148030403541024181c1d400c80d85c00c5030f089942038604010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 472106196 1250 472104946 472104979
    0x4020604030210050c0d05030601091202100507031407060204030201030f02121f0b04090c0215042f040f0c020c0a030503221205010906141302040e031b010e010506 72
    0x4880c1a07070380580d6003c0e03250383d01d403100315640e118600c220882801b4543c41c10810607801402540159001d0782e40c105816202e6401c100546281500254841c1000515242150285c3c1c0a05000342c02802d140103170421034685011a17600c603540c1202d403075034006021310071980c05200e25421174841031300c00c60410102426000901300301420110b11b21483c4c1c1e040040e0340b8600c1c031050016010341d000582d03c0b6950384800708068112184400098000c0d0140604421100c00c1b50500c1103400c0b044d00050b2202c011454880019103554802049032035040c40c44154846003d11103581c600c05c40300192081a028009003480194942c0d10b2054550900c2040807038030000946441d00d15980d94100d003c1065900d800c1080c030380b54007075a840110250301400f80403040d07000285141c0140c2c018000340100741c2d42d20040e9101203034101a400300340b0510002605140c0d04c404610900102164034205031a8041228019181c40c0080310b07a459030340b41c8052010070b00499802940c181c0742c0c14841315030300c003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 472107446 1250 472106196 472106209
    0xa0f1413020f030106060809060901050c0f0a09031e0c0b0c100f0b0316090c0f050d0e0f01062702040e06130b0a0902030f09390603010f080d02060402 66
    0x2040c024503030341100d245006640e20b0040030603009100a000701700e0f041d51904040e2500d0003c8800e0800390141c0000130f20742a5060142e58400c54038070076103d00c0d10008948460258125400d05400c002d07203001c02100240041c034806150300000345a0000c0c409ca640f400749104d00c8160407014100900b440619001f00b000201141228110180070078a401200545001000e040300c130940d00d8411040160b105000c42c800130019035042003828070901c80040800e4408240c0c5000e0880000c1082203641c4100305240e006000d401d1200c2d003a00c41c013509604449003074a056800045c403140ea851081081852140d25101c2e0a0300e00000941c02c183c030b02a41110503000081c050390141800282615131400d0f02e50200350301120080980000e10303114149a402500115031001c0202c0228020601d840c100040400703145221400b103950030307104c5000c0943d14100ca10075181000c40d0a4046000c296a0600079601030718104c000382c10703064a0306959902e4041140d98010954010000b84070150710713101c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 472108696 1250 472107446 472107451
    0x307030f0506030f1c0e04180510051b0d0e1605010f0921021903050a03080622021c0e030a020606011d06090d0b070806090121110d05030c0102030a0f14 67
    0x5c80c103111050701010700b40d522514a0341c49951003850019158504806c0020f2052100d02441c1140e10300440d000300501203d006817002100c804510b4014441d2000c448003c00c0354078050000440c061290500d12450311036072040c0210000c01d111402e00095030301ca0000316442c0300034a4002481c0c0c3ca000d2040002d9003001d2030069150400c44910819522507080c6606242c041468422506e9030b2828425142c580c0c00b0001c600180c030f071202207003c41c42d00c030051a070b011018001d82c0003840300449070100258080c075642c4250085070102410589c0b050300c52034090402e841c01460b61600c0e40000207080c800c000b482c2905001c455000040611580d519900520800307481e07103940d0390400400a5051901003100038625034100341001280d507403181496006510a440000ca141d132104030b425103210200f50404102c02601e24050041104025200c0084c5006070011400903000d40380c541c11640a455410003580d000801d20070007003124807910350050ba010004010500581c0702110102c00c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 472109946 1250 472108696 472108723
    0x20d1a0103060b0417120d050712020903100b0102071521060b0708180409080705280f060e06040311071202010909230a0b090603010218120709020307030f0506030f 72
    0xa0300c85103110100400410901c6d121402c4090b0310762540c040d280d0080d0404a40c004006540c407120506811054000c0c0e6031003000080c0541400c184010502008007005541300381184180600058903000540180c1d030700b0242d5646440e11840c00c6100640000b0102d28070000c1c051608030100515492038040e02c03d00c680c0700305101d644105002e40c1152003070030f42400b654050f00c0e2004400402520800901c181031290050384c0c0c1c901104506180c8005e070030600d0440404d2584c034080005040c2c1c445542c109840740c1000510f020300c5100541c90071000301e80460203e641e114034201c1c0700c042002100b009040e0810601e2a1314040e40c002044403400784202090b05071180b601e00f02c941c0240c6281c03040351545000d800140d1400c81c2c50900500340d8070329918040e442d104041801410706000300c2e0310b019484151014421202d034140300d8442d4140c007440d00140124100822440d2090005600030741d038640d400726103061070f00c035007004440003c3d2255210b40c0c09003000c80c1881101040d0320312010038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 472111196 1250 472109946 472109969
    0x1006080c0c060106050304051603050d030f02041d07020f0a02010233090d030b0103090f0206030c040911030402010f08040510150b04230603190f0b04020d1a0103060b04 74
    0x3a440c4020090740140c655100682c05624008113140758000d02031480381d806142203600b44410301184082116840c000031700385410050203e40c03040e000390010000082070100052030700d543e60403a08002031464554410420000c81401680c5034104095198100b54030060a2102c219600107540e40c503100e000c540e00c43c0e411400c1400c04011004e0300160307407145c6201c02001032500c0031040380c031205079080301400300c1e180c00e9008040e13501ca0b2041d82c550582c440b076000d020425940811443d030b00000c04c60909680c0410020070440754a00071034500c0d20781008055100e041901c00501641c203041002400c1204800c20000410b50004180c6001000c1990000e061008004010b2504102c1d4200c062101d41c00100082e41c10b100c000c90406110a6030151440a4005800c0142510080d0780c501072034210030711034410142040e40a21417485803840002810322954010505a80109040b6406150b50703030400c8132200221154018188070900c0c0c1048071a0030309642d44020301a80c0030b000c05002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 472112446 1250 472111196 472111201
    0x108030a0f0e041a010f0504060206061201200702090109020307081503070515190c03140309030904050103060b03060a0b0607060b0f0a08030a0e0a05010e0127060323100608 76
    0xd00901c1d0982c107600c40074205101c1031000e0f4100c0c0360385040050311140000c001d0241c600c4c3e4248954190303070907504194040d004580311031041250059030640e42c00080d55845849110640c840d142d0500962030003401d494403007026004000a00005a00c10a030460040040103403d0b603114280603446082041445450510030300070900d000e903150800d45d0080080320300a00c0724030f60703e00a0440402c1d41d141606c0c0b00c841d24441110380c0c850b40c860080102c0c0303079411401c40781c60001e409550b001080c441160b0408111100003025100203a0003038500d156503403d10a0381f42014025180d2089200000340a04020900890901d00c030768000900466034424040d031866645d00d030040820701004002e140d520352951456506c0ea4803261402011500f104506205c904100d2000c100b2204142c41e2000840c40803401960a201000b50141d03000d080c030341c0d54504071680151020090400c45c0e9000524a10303000007281800700c24041c5440704c2c00901c080008070049660040300742c0344146800507030358 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 472113696 1250 472112446 472112477
    0x2a03030e0103090b0f0a1512020423070f1e030c020f2d0703140f06091f050604091b05010f0e060315030a0507060f08010608070f0f020304051504090b090108030a 71
    0x607c07403000c138002c00c451008400039101c1c400c0002e0049076402203d0030009640400708281e100c2625018803c050803000001402d402d00812000c246074045080066250001615213103211140d95800c60200b95114001e203012130341040350580500042005042d510480e140c10512440803050035124030081001070308030620284151002540e020180e02440c0e0180f040294550030464558001d03446030704005442010300284100c0708415040c01e1080790084104400003802d401004035411544841c00303540001e2054588c058241c11100d03c201070181098001804845205218010800c1c000304241c900d03590396080f260801c5882e001c65440050701d8020034101101704001601a00440100040c1950491145842c00d0b40c5951082150382c0c840701d041d0341480d019145035000a240e002140400c501944c60038040310118011030b41025506c40008000303042e40d4881910400012030200986603040c0643e152200c4100e03801040da606246400d50750340201000c0c4d800b000390b104041500d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 472114946 1250 472113696 472113701
    0x61806021902061605030301030b010312022103100e0703150506070201090b070f150509070b030f180c10020318030d12090f0b04050d0f1d0603042a03030e0103090b0f0a 74
    0x6136500c5000d49489680d41e040074614030000f44000d0b5007488140c417500d01d1143c0701258988080d01c50107007a80c00d44180c0786844c80aa04018000303034480061a402144400f0000702c0d04e4800c242d0f81c0c1e40072072502080da08a0035150029480389003c1d5105000d542c00603038020107081c0940780c0503164580c03514071605003610259405000900f08100c460780b0694081002d8000a2081210741c007190001c540d5000001103034801102c8800c10006000041a40300d45103440d00080003000200b00c5d119400500002910f202e100b0030280c002d60b1000901040e01a0303080c6102080c82421000740c60064a1014083c4c0302c45c0c4c03000042e001c43c9503991320482c10004010b405211258209441d00c0c6685000e2500369510703021440c0c4000810782d8074080e4a00c651046c284c50688460384020080707600b0303c02c0b040c0403042d000035000715074070103500c9903004441e6603802000d0319025820b0300d02d510300c41c40c609000d4110070380b100c0034a040504060f59a40032901c400744080d040b4440e0044070b00b442d03442150382d000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 472116196 1250 472114946 472114987
    0x120210230c16120e060304031709010605060c0d0207050a030f08032d041e02150c240f0109090b010510020c09070302270a050105030c040f06180602190206 68
    0x1050070b1001001003444229008086903103600c0d1181c001401110041228a0008541c0200050b600d41284100c1000032131909400454100c004945142ca40c40091000e8104c5a080711242d0b2220100256140c8e041001c10f005000945400d214241980c5400f80400307401d01c005030a1440c0040403603c00800840011203420b240c4002480400c1440c804100d950004c0e58181c0d89034480100c034500c3c00038240d40e0405402d43c0180203010003001c4d19008012504034029100d030300d000741c585001001c01c4040344140302c00200d201800241c03034900200e04228034103820003081e02d8a0721545900040721030340094151602150815505031808030224070309180303500465002005401070180107900f54014040303071242076510001c520000380c06602c031000c138150b840b80c0c44180c000e42000a54000d1004540110508a1a03468a5242d510601084000f0350103800013170258000c011070007168108400107410305101400000b0701240f28240d03510003420000c1d10694002890100d0503078000020344 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 472117446 1250 472116196 472116217
    0x20a0b01080307060c05210a1401030b01050901060c051b0d05030a09080d020102070c030f0303020910091a030f0402090a1b020109050708060c070b13020607120210230c 74
    0x25968580d05020340740e4000003c1281c210b0f06000c0a41007013030250003603070090030884d4140c12120038500d0b400681c1e840e000e00041240380d43c0e02040c107040c1c8050006c1501950241c41842070310351521083c0102000c0580c089003c00046050001c00180082440c02810211203140d036441d4000800040440468171001040c038070000400c403500b25084032812040b125490140c403031800d40320805078240d00c20072070018a0321200301c0c3d003400020070702c02c901e02c6041e0091038014149803e000100d000700000e0b50b01030000c2201200e0070401510510084201451001d0801d421400c01c0d031450341c0700a101610080c414034851000500c80c2540394440c003055404d04c0043c040300344292201030300805850100f0b0b91180100300020038500c500007046070003504004400ca2910b02c061306c441d071003840c0103091610a40d03194100759000d40d4654011b4403482e4011030310b450320010070500c00b0b031402c1e41905480c030065040034011101c0b0031034154480b12000540305c000200340d4500d10044402c0c4212003200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 472118696 1250 472117446 472117463
    0xa050c0a23061b010e0d09062325050c04060b0a03051803031806011e180b04060923070207170723030d0201050603070b07080d11091e1f020a 62
    0x300115441504030010048020064882016501b00211640302450044001083d44454100084c4e445008101b09010510701d0403820a1248208466038482644001ca4840e04689080041c003406115450b0409c0d4125400c0140070301c0d000b071140c100e0158100c803c042c16500c20000c1c0c011603c4502e580004402c1c1000d0303d0b5240f50440707501164022904019006110384000440e4094901740724004141c0e460000b0268186420800810310866405011180d91140c08401003a140d601034100508101d4502040c0d0140c9a80c980b00c02c11030302405466421030b1003050203205900440c1440580e000000c82005034100c115507175152054541c888507074080145480b1b0031601c80320b00788060708038040b01900d100c441188012800d8810980d4050340c1500040c1d0100000983c407402040a144980d441078100252640d642080710b50f02c40e26405290000100132015141441e042d030318100c2d020b2511a131114001c0003080d045040400a1a24481d4030340503a4401c50080006010040c0c0c048200e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 472119946 1250 472118696 472118737
    0x2010213030c061409180c070b07030b040b1009060302130b040b030103051515010e1809060109230114041803020312070807050d09110a080a050c0a2306 67
    0x62014071240700d1200081d0545042c4403c0b5a0f044c02100c043c2c1500801403081800070010302c4081c0b4401078a01b540700d6100300540400100e05511451040030952000110030001ca400d0000b901c200a403100c2c4500f05007141c86c020349412088042c29288a07140058540e86418025891095140c000001080e030124000449031034060046050340d10900640321109110000240c0e201c13401c2e2074964000301c4411046c0e0255101c5d101c801d0501200030401120b40d25043c0f200c41d4010016500140140c0180703006204d410000c1c01401c104046102c0050005401510903000001045c0101e926102081d41e00b051599940c0c0c02600229580d1881d06800c500a03160295403a4464842c4644801c0340c14006880140103003415449072000e03885862130080b01c8079600b0018102140b0460703140036a45041c1440b9152030201c40702501108009010190b102c1c00c0551922106200403880ba0b44a01014010998101c845008a200300070751102560001c1000030703018003454034000c0d01c00c10384004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 472121196 1250 472119946 472119953
    0x1f020d060b0c01061e0b03090109081207020d080903090d080d0212071103120c090a0305010c02031e2505070b03150414060f0118031704150e01140306010201021303 72
    0x6003051101240208691030f541c01030540c044100305c1c83c42c0003d400f840170401c004c080d80c03002154058401000019a140c0769903d45503940c002148900d1721201032410883c64940400900c440c40c9a40d0402400511300f02c1c0d5030950343d10030198140e0281d889a2007501c100440c580554484040c942415925004485042e60904000f22400f9000031b00700c80c7c0c902148800802154856036006186090130703556250002419840380030183e030004020000000811003c0c407510000c40c1031903014550794140c840405881480400350f11504a178200500840c0403c40c07807c68020201d072000000070002c00341051414038441e58041c401c000c0c0004200701810020241c55801c0400c201d030104a00d41c0e81820704107401030b0403685260092603210300403070035602644800e04a5294407001c03008054503550303490580c5c403403041c8402e08040041000c0c0011000b401c802d0350300103464a40320700303030064220008019140000300380d5420600013005c521141d01c00c2d0111021105a842e691b6401030341c0780f8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 472122302 1106 472121196 472121219
    0x12070803010605070f0c03050d0323180f0d02010b1309020108010603050a090807110306060d1707030302040506031e0a0902060f0a031407032406021f020d06 69
    0x28920000740080714a1b006184030b5400340601d0a91408080c0c192092200c0c841a480c00c1100300082168198800e940e00801c00ea0110001d031000d00d0b0524140b6101000d04600c500071042280e4400b07070150040c0204400c103882a6840005803010501181c9060742d009000501c60304c01013018a1280d08901c0d0010328003480042c804405030f564142950110a044a01c0c22600030006594941801595401041a40d402c01c3c110420380d9074418130600c1c00d10b034034408500400d5490915110340d040d036000c0c005c00b402d46c0f40e03607080440448255420350701c82c44080401000004015290a003d1456807e0b4007601c0c0300d003403c800350300d000c9503504003501d008100b554441c402907180002d00c4a140c000d94071a14000ba014002c903043c0401e859460003510b000003a4110104101c0d07a00107122264000040319a00c1031082001050000e031282d200c0b003490403410002d021810500301b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 471942446 472122302 := by
  have h0 := BRFrame.cov_init 471942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 471942446 ≤ n) (h2 : n < 472122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
