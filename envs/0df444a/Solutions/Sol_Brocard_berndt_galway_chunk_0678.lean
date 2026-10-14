-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0678
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:05:37.623717+00:00
-- url     : https://prove2.me/submissions/eecfc1a2-b8d4-4bb5-ad85-e838975a2c0b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 121762589 ≤ n < 121942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 121763839 1250 121762589 121762601
    0x907090506071205090901080105040201081e0601030f06120605041b080a0314090a0803070b0906092d0d091403010203040f020f0301091b09050f161404030f0f050c0301 74
    0x40d0402002d011100004294000c00c040e10701d00350510b18109503903000002c004103c00d030444081d594580e010300c011542c00a103200c1d000b0500e2900380171066001a820610800003c2040d410540c0320168001d0381419584200301600c903e0b601c40004d00c58038206003014150035107007200c2312030159144070398440e1040c0e2084250b8240e40041e04481d0a02d440881d480d0210b8406101030a004100103030703459480d50203450080000801850b02c2e1400740c10b0100d409031000340300301440d40260080240040010681074441c9420092800840c071244e0f0b070b1405034802801c142038680c480c5014003204c45801c06220000c446041c02c0c03034100c40d5400f00c149800e03400151002008942d011002500514042280d40c18045010300002956541c0d1780314011060021040c0104002c0049014048403030980075295014424409440650504c16080300341c240c00d0174107071000c00109c1d052200d840010300302190300554000004a070080c10f1800e1440080503040402c0704d0744d200358044941c0d0382c24103005107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 121765089 1250 121763839 121763849
    0x80c01091d04080706060f1203020d09080c0112060905070503100b0a051606090203010f1a0f030a0807081b07060e030114010306050a0e030c0106090b0d0b1f0302060c0a02090709 78
    0xe049151543d0ba03034940340d80c02140d02294841c0d200c80c40071541d111220085c000900081e00c1809061480d8280a81041001400f50082080a00d410301c814000000c145107101070038601100c54190002c1018000d1103140c106401d074034244402e00101039400400365029005150092202903500c00000003d07106204001c00881c2003401a40b800b01c003d0040c590b5014007600001c030f484d101645c0040d0844140c1c2c8001d2820b1a0b64601070120401c16045a806c08002500c207a2003618074400000d560311620b210041200100180340406c0210f0307e420344010404185120041c1c8400b440010340b16500e0b80900c800168a490ba03032a100d24050081c0c0300500c80f10200400941d08603120728010b04401410000542d480f4000ca8003217160801c010301e090004840000b40c05420030864209a5642c4001e03581701d50f40c082200404036841e0403100b9000030410115102e001c1e18050143c0c50710b066548065400b090102c2d6a07590f029001c50340c820380394400c6910900c50390742c01030256178030b00140c003034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 121766339 1250 121765089 121765139
    0xb100812030606160b010e0903041d0402030c0a14100f080601030f0e0312060306070905090c0a02070b031305010609020a0507110303090405090f0601140d120c020901080c0109 77
    0xc1803041035610401160440c0014207040e241c0315103081d001c410300d40c94070f40072108610180010800000c443c3c074441d820084500213940741520f0100300c803581c10b803080e15005d034107402e9402083c1159010004c1c40720341a80540b207000f206d55500408142c1780c50440c40c0034010201c40c1008180b0612400d000d641102c015120000d5944074070004400602050b4140000160382d0f49418011420401c040c048047c41003078588460314250040c9428810050541c4040c40108401072002d40e89c0d44800e5680030440c5060316449060400e4200d00e070110b030394000d01484600000703000642404042c0e0070092070040b8001c0c001185c0d81d20b9070307600320321a200b01600003a505110910000b008403480c42800d001c010100c0303007031000d8900003038100c6405440c520020343c01000881c40e4504180030362130040103500008071030302030034a0100f032010407040802044100b121004242050080000f40b0000d0340140108100d503031100c618541e103c210607074003800700725901380000b02c0f222244440c5021007007010b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 121767589 1250 121766339 121766353
    0xd14150904020d15060b0c030904060506031003030c0f0804031a060102120a030c02010204081902030d03061404020c100903030507030b0307030c030b090f0a060b011215050909100207050a0b1008 85
    0x680540c140090b84041420305c1e2116400a1030f80d03e410007130f00340901c0e40000f4550310800e400030081101c00747d5000e0f502030b4409008100102c80c000340b002084070740504000034100c00c030f0320300b06055400b0804020005180454040f081c400c030280c41031003840461515002a4075810016a50f640380309000d4500d0036001c00106484511980043d8950300c42c90001505294484c0c071000d0800700a80c00e5220042100760780c40003036103000c0200403a081151f0608200803410205010362000f01000c0ca60301a903000039802c2e00c007040411110b00800c46034002000071070030b240390041c01b401c404d980700c1c0002070808010312540e140200c0c40b5400c0f02d0340180c80d0900340c1d01d103540d8405040d01c0201220104d0003260604030000000b4000a4081c0d0312800c1c000624010a0002600071400d0304441c10030241742c2841545440083d040d94015103034100c40340342180d52041d00c51403400304c4c160741100901c1d00101d0b2440401000080c6481054810381d8501400d90380d5149125041d101c0344505041079000d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 121768839 1250 121767589 121767593
    0xb0709080f07150c020405010b0307180609090b060705031803160608061c080705100501060e1c0501021b06040209060102031c0e12190e01050906070312020d14150904020d 75
    0x201103883c8040071400c1030b4001d8070311500010120b602c03d0303212008a0400004210b0303a203030f200301042d0b68000c920100c41c22250070001e0040581d5a01c0c01002d40d0f0580e075280c503504a5880a041c4c48071154440b01b10796440600140c3c002041150b21074072070091003280c5d152a10702035010030401c26244207958482c41c5079035090422903403400000c50900c8040d2100388160110b03914400514602e40103030300401c0d0085480500a00710750701680000c0030803070f03a48810810350769801584078080820b00d500120030b18150510398028841c4981c0c1c0010208403030401d07101d00901040c00381c411070003121440d180c1e5881200583c0c880c41001c561710411896200d00f80703080c8070141e0202d44900f2000084549004807892448020b92110390403240b07032285400518249540110381c51140c003000c0c0f0300107080003080000308180b40078520b4000d052041c10f82034081d071b401155060315001016880280400d80035242c46020700c620545003584802d1f819000c42c240c1e820301100d6a0301465002d40003e0142c5400c2d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 121770089 1250 121768839 121768859
    0x81b0603071b020d02180f07032a02100c030c02011104060507170708031e13080301090b0103020f0412050d110607030b0d0501050a0501050a060c0b13030c0f0b0709080f07 75
    0x910012a4800c4000d81c2c03a07401741e1a441003a61031a40e0f16510b6451078102103440b1143c44030028540d00406081924490082d200c01c5450803140c005c03211b54001030100740205a08081711842683e6100307260082c2c80c04c00b0b503895000368005004640080010348488075101110f48550300402d004101c04110000c000307240d03803007040c03022024a8440c03418459646d4541c0c3d00d03a0300940310190041b0204c84203000441d035001e4170982000c40c0119920784064140e0300d000c4a03000c144200f2560603030710032507094182d0294040307074080700070307403080035a200c2e150750640c07036111800a019074252007045015a90b003800f030f80d652840b18401034000e02c1c0c00e41e0394400407000ba0903003001d200d40004a44400c0320000d01c09018450040060401c007040f55070501d418840c1e190000e030700c001c0c10070104210400c0840c5c05046a140c20044080c840c12402d945410165111141c1c0d02004144072225449603052024110409000b010b503582c408502d2903440c001c0d03a91f60a07641c0442c224981080c4420000b600300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 121771339 1250 121770089 121770137
    0x203121303050d020a050702090108010203090a060b0102070f0801060e060303030106021903030621111c1e0506040321111804060510020102040503010c08040c06080910020301081b060307 82
    0x4a85040c51602021030740f240e060f60032040035040880c90100d0220110306e040810580501000c1008506500d4035001d51584c1e05481500070b40142d80d101841082a44240004000742020200c2d030f0300c801742c0c4c4121710342c000c04c1c01e0712403100924283d030081049458040b080740e041301d1141e4000c0c10074050314100d003041e4050743e0300224145655504006100c4120301c0f0000d44105074a805a26586180c0c10103000001858260030703c03c0c02c40c1c2c983d01c0d40002c403009036a030005800910300c0e007401102442c184903200700c5050191007031148008000400d5406194440e07000d1003460541640308002212000b03803980c000030840b01541c140601001032007605401510007c0c0180003041d142e0f0340d600810100302262048074010303500013a080c41a0300702405842c0007100e040c81d0450482c03034543c40c0c00f00c000c102400741004101001001c961034560410960350554aa4402150740f0351303582e4140c1d5511991862024640042c030a100034070761400c082624801e2082d41c6444070700948902d1100a107070708c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 121772589 1250 121771339 121771343
    0x507030503100f0311030d02190809030c0d080a0e0904030503010311010e060a2f19140d200a0b0a0e0313120c0f0b0906070201020a060c080a0c02031213 67
    0x2c04440c0014000009140740c900031405040050380900c444c1061506010300800a80705540c03050810740300c980f103020740d1041c0c883e0300001469100c04801002034201303c810603603150b001d55030b00000e10501628000030100382c003180d00c540d000d1200c2c03141804940202241d002c0c020590500040000c114076140450f449581450400800e06601000864540203041484d0004260790300c2600821480c90310081168007050455200e01801a0840d07a03448108400720200a40030603a1000c2191580c0c19808103e55813003079030f03400080c0c0100100a490744119103004820725454800802d0300100d503880c4e450b60043c0030000d00359104162603001d04132044070380030b4a11003001924501c070b1030400480050500d8805540d448510783c1032005086000e0b8011000c90041c040042010618100881c1c419402c19581e0380d40750303502ca0005034200889000098912424410030a00540d0300c6100e003445031210322401c2020000002e401c03a40d9028104031003106500200c0441e15090880e02d4000c2128 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 121773839 1250 121772589 121772611
    0x616030c021609020a03060f0f0b070813030503030f060603040b010626090d0e120c0103050a020d02030a050a1b021e120d060f170c010305180714190302010507030503 73
    0x30400c0c07607000c841d05603254808200300c2d0b40801d4036922141d00d8047d03c80102a102d0b030b1201000d082c03011070301940c0340e01d20424007a21000a010020444c10805980d40011281000c0311b80e1941d07030034540d89030f51046500c402da1035951000180d43e0714040701585d000d2034000c0b09030411a800d0044c181c0e0300880d0304144c5400068690306401441c0707808559036100314112000b52802103684031003d406030b4140c04220f03124081c0c5800c4c582e03c001d030018290345614003d107004140e50302c4c1c002d655070092003004403036003a03103000004101d000d807182d401003402a401321104002c1d0f219050082e81409189194030030050300f181c90120002c454180020518241e181c0584d07a070744030740704941c4600d82c0c041d0701e0442c1800d440c0c83c2c1c10030030b0f074854040050003010101e5902c4100c000641c0c8140d1030754900d40701070741819640c501160003003140303d40841802c002e2004580d9401d45035020b03070344003811a940c0c00340b043ca0580c4540100420645002045980c181c66007400e1019550b030641c3c46400061040140b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 121775089 1250 121773839 121773853
    0x120830131a19110f0a09031709030303070810030f03020a030212040f05040b030c04051006110d050f0307032d0b060705030406080c07050d05040501020d18050d0204060b0a09080601080616030c02 85
    0x11380c61005040f000b08035240c1c40000c518501e00b03036004054992011120444c1401790f01110b0b01d002c0304881d400100e0707103004480c0da660041110040790750364101606240301080d401042640005800300c8550083d002c9076500003c6071824441c2d84501e0003500500c40394002c040109041641020700c0f0300c00c005046d5111041d48202280c00c81d10100e40320740000114174820000560031071107101e00081500e02a05003100c0001c005085403140d4800c015509800000040c0034501c80d07804200c2c1c001f030703500c0707a10040b0303404d41b40303d5115100d0070380d50154035450b081e05030026103040717412102c1c22680300707000e5801c191038414281c407820402003169076035100410086002032401c2c0424504418580c8509803143e00704000240f60051003018842400342050304040180110240101129000c442103022001d052012174040c043c15800100c0050000c580058503540111403601a40c8078001107031800d0307a0750b03000142d440c2420f8881d031850140c20103124000521a80002890600d1401100d01c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 121776339 1250 121775089 121775107
    0x15060705100510030c0b03090a02010e030a0605040804060f05090d0206031807030f0b06040911090a0617010504020f0123030a110a0f0801120830131a1911 68
    0xa5401c201c824004403e05400c05208100207402d1450142408401c858114500000384d2a5070f85205031001c0d040c04141c400021441c3d07410000e140c0f5241c1c0c000c0051105050614011305d50350130034002d14011456600b02426110712030307029036401642c001c103c0d11080312341e0f4080c414260300c060149941c165070303680100100ba41c108106002588034218103100c01075541060b0401c044090806d911071400c2c0104c0314003246181c641040d004e007080300c0c84071060b241d5103040c1000b44441c2c3d1003240c150550440c20044c0f62410343c000d5110342d00903600755039403070911001190400719240c4a10300079240b80d024680020480c03006960b0140b42d10b040056200c1e280c0c581c807000e0384c00500d400000159413503035451b1016401071842c0d00414060441d4000341c14140d03160240c6004a11501100c0d410b44034101e050000140c80c1031001386912103142d001410404070000306203480c820160380d20184408510051a2908061031103001d091010b01120036075401400d020300194000c01400361024440008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 121777589 1250 121776339 121776341
    0x10608120d0209011115010614040302131a10091a0307050d0203040f020406090213090e0a020103180209090f01111c0b0307091d160b0f0d2304030e091506070510 71
    0xc51080c090007406c45c258034000b001801c84401440e105a0580103010410060711030f083d101d03400c0308420078040303a1007694a6810b804030300140f01480d03105440b4a4003a502c1900041000700740c540010b1402c030501c2e0581d08a0815110070317249a0000f480c10010700e500400b03554040d6420510400ca030079040c10081e0001001d603600c41d0040040e859001a01d0111142e20741124001000440401d01003000c082e020581c4170140410003a050548480e0780c005140c02e514103403003900e40d004004422a062508141d540c070000382c80b00e003c99600c2c050701c450381d82030303520141c45603021104c003410580e010483ca8a4050909410015018800c00d0000305200301035016904503072020314076000f10700d130304040c0342840e0508050103611a01c4441d041808196010411108004082504141d5480b510a100002401d2104120041c180750350b40052031510546001402a0301960f1241004440c803810011448002d07105000e104102074801c1c0c02c9420301801038146540918103407801c440005540340c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 121778839 1250 121777589 121777603
    0xc090c0405030601152c010c06060503060109090512250201210203090706030618021b030c0d031a010801031419060b10021f11070204020d0509010608120d02090111 72
    0x79410034003a8440c0300a0030703444142541240c070103021007046c1c2064900e9103074641c01e02c10442810051007020b90402c0c0a002d401030001004040c041f10f03070b21b6940e5420100201f103505011600790003141c0301480c00c40d180d64150740c02c2d0038214000010605500380f81e4205d14142020403810700115600b024800c0880101d40e01801c40d201034013517a289440750302107040c858150072000905d880e0540501038042c0c030700c1702060b0608a1032001a038543e10803151071220b0741d00300808010f900c000113405004100c04505660400c1c081d031002d0080c51400415800346039080300c0741c94005a056030040003c59420000790913440aa00140e03101125580d1000c01c0a04030303200141c07030141c0c80b01142000e60401c200f8116040380726101900790300c00610942101040505003561406840f055600e14000303c61080703698040e40100300b15583c010a4040e00090704040351010500e5182084c00900f1010104031144440000802c151400200142c114029002005201e0400c070b46040b06c080c44003001c00c212 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 121780089 1250 121778839 121778849
    0x70f171003020906220c0201180f02150c0c100302091206010f0905160c061e050a050609090c24070f120e01170a151511060601020c090c0405030601 65
    0x269810600758018415040d0300506064060b42c07800580b02821060395a1044111500c3c06001c12101c14112049002d40700e40340140350300080d10f0700220f042140744550301d6486842614034a40c1401e00e04c00c54103850040c2e17080214141c101d14070014007450000d0200c1402e8050707042c0181840510000710f181035980035420070a69000c240140030300030032041302000070524858140f00d14034104d040034a15040441111081c0404c0030002002c00c040368205844401d040d40090110b1a4441a41c00280ca001c0e904119140d2400b070101c0d03540c0c14205845440754214100400c00300d440036051001c20b0208200752a1401128901e0354016200c2c01c0007000c00d0750007012103085000c650b0074013000da05458400d42c002d0044400c0a6012a42c00060100610766600b90b04c02c107990b0b55100c420701500902e010040642018003012034581561048802251a2035446000c1100714401d100d40c0d400050b80c0c1d160150348089010961854110726003a40035425180841c03c01d903440011270701d0400281c002c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 121781339 1250 121780089 121780111
    0x1201020f04060206090307030e090403030e16051e1e03100203040609151e09030e03010f1a010c08030612030712031406010813080c01060b040306020d0b0a030803070f17 74
    0x8108443c3c0c10000950004402000303186410240d6401603e00c41035160381c41d0281041c0d13070010b070074107009034408203644030404140c0700d0889280864001c000c00d1405841c1c483c0707a4492042c14101c00c0050006501c000281140091081d141d450b038002c1400c0c00c408550500c0340c42d4942959410038009140182d10030308001c510000c840c908215001c03110f642412800c2d180c8109211800003114006075070960303c150000700000b0f2410100c1d0059584510380d07816608141a00e0b000032440c0d4800c03110090681c07840101290042d0045850b4040288041e00c0000184007040c2ca900d000d10030340c0043c24013102140e14007813050b958081d810401214150200eaa100b0f000301c1082025031406078040310074a80290315250000302d44010b00c02d2840f028041c030401203582c14417010258840809848803c511b0b030b4450b40e4910b84940a5400b00f00e07078076421410710314024081d05182c8071000540e03034442116400c6603507500701107a03000c240c42403c50421081128282c2072010b80a40c00303001d543c282c13203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 121782589 1250 121781339 121781347
    0x7080405040b06210a06031a0105100504060903120c1b0905070e06070609060b062206030e0a030e0f0406030f05060702030f07170f0c0d020c0303070f111201020f 71
    0x810040395034242c1d449004440c01c20a00900402c039880c0584d14100706250008152070f2007580074000c080f9a00020107122601c5544c1c90501c80c08804641240c2d0304561981c02d5000b2030000b02c5160081e4805c2c070004c40c460070720600001d0746020409074105101c3c90705983c0303c10702d07803594245445184d0035103070164441c034001d000302c0b8041c0c050981c0c4440c0034104841140000d6010035200d100e1440044c0c0319507500c0203c00f0401c07142d03808c50445a00000c000715125180e41e00d50484551101001e004880400c5400107507003406800b80400700e240b6200a00158540341e1000c4e00c1c03c0000381c400d15445480a40030345142c0d0785d2407141f80040c5005002c14030308103005290151402c08042e040d10155441488008420a10102200c84d490740c003488410740b040704940450124002c1d48103000345da0313802190300521100300040c0c107580c50000c0d5003120640c100440505840344503024010b00035210001075400460383d151880b40b04580c1c06000700d88030180b0502024220f822242c910303002e40c40006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 121783839 1250 121782589 121782599
    0x140f030c0c160b0405040e0a0524060d030804080a02030d05250903080412020102030d1109180408070305090f1201230906150d05030c0d110d0206180a0503070804 71
    0x20082d810200100aa50340b900f041c0240d4424003441c801c0600c80c68446004400c4090244140140d0303660040849a101a86002004c0d8501c0302407200c0d0b9045c00d0220025046180c80c802c203880d500e03010303140c1e07c203075480d40d440344001503002d80790003801c1d44001c00c040b0740c1201107441514440c091024665405000042c1c454500c416840003103401c101c0c2d0240c0c1840496000d0007150304642120307048100340101840140c0c20f6008110b004131351286001072446a032081074000f002108021104460410b0b0080070980c61002c0a89020f00300680502814000900031001408075145c004c020b050314101000c0026a103846510311403040b6511410f00f1407001c0c0070101c020b1415208180c940900d441c00403000c035a224001041001d800568101d010f490b52542c00700c0796034454110081c2c1c0d5a501122000a540b982804a10000200c2aa8407115500004a104034008100e60b001c0d0055844031020821525110000709a00380142d0403030b540020810030003404c04911401400e52218580 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 121785089 1250 121783839 121783843
    0x30b07020c01080f0f070315181406031216022b0606061b0204020304020f060309030703090905070e0405040c090e010b0909190609030e1003050a1b020706140f030c0c 73
    0x1c2c3c484c3c00204814010b100b00300c030030f1160031a44100580f40000320a8062001c1146500080e40700c00f02420b030100c5050461541500444400b1030314950300051601c80034141a980c2031048005441d102050204200c0e060032103c000484600040c01c010030769031241e8030000038130884218114039181494070130f010003c0c9800b40788010403070340c105003007100c13800c0341040d1011b0b01c5680000d00c12607001001600310368a0f40390708891064054850b50301c924001825076540d50000d407003580400c044040c0068010603a0041c2c2e441500d4a0350307110113030500601880040c02c0050000c4810300d200e150046100e81070792092040c40d0300d102c400803440401490500c2500f58020700245040d801000b500b4611038035420980f000154040f0002601d4011400c04550014007120455405880b01d007420181030b030f26410581c0940b0115208104030400304018400d03018601e610003015030840c400402c0414010301c00f1000110200d51401c0c50000238003000c0d031031684100c459198015012415100c50301c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 121786339 1250 121785089 121785091
    0x60a0c030f0f09050402030a020d050106050a02010501080303060f120f0115060305010816180b0301020406050a1704151107050a0b0403021203011406090415060f0e0402090d030e0a030b07020c0108 86
    0x125062080c075a081c0c00200800f440000e020f00f5001e21780001c00304452480990442e2040901e10350b00f0400c958458000900d1a031001040100540c20f00c0004218014044116801503030010060390030700e0494030510150a4003924031116600400c111070070350060078083c1400e911041c0d840c501c01141807a80141c1141c0d0107030040241e60748002410000c80703403141c1e0494251348080ca40307020000407078080a00648000420241c1550010800045140d00240a8103907100070383ca43c2c81d58a0140b469000c01d050781298068058051161003e502518135880301d140d0021300c0781d1482c039045454551030724000e0f001c10101d80f07020101d0100000d166050201900010703c080b0302d2032555140040b02403618211541c0e10b0702c10f12001480c103140c4d5840358042e00700040300e1041100703529a1214040c00306410100c1040108803803106240c680c1c94a40300311401040010410311480302d403901c080b82d9001c540642d09400012040b800700104403201c1c6110b1298006500a28000500500040c01800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 121787589 1250 121786339 121786367
    0xf02030a140408030a270c0905010b0703141e0c060915090a02090c0714010b0f041503080d02040b0d0f23070c05070f09090606080601060c081602060a0c03 68
    0x400c401c1404009110070048a07000700c0358040c0403c2243c91500c450202c02c020070001241255400109030401c0140d280d1102107540e82d0700c08000a03a03944043c60a2171045180003000180810354102c0d0890940300640701e8210213480b491442408410240441d610440d00740800380d000c002040540442082600d400b0140f042080711070381418100140d8405154400a01c034054100020383d480200d4002d032102517411131408440600d400e160716000301400000180210100c3ca0404c1c158146401801060502c540d540c00743d07103207507494131050342e00412520440980c003080f0000302d10742000b0203850b2201c03400c2c0f0700042040f40c11030044100ca01c1e642c1c088090354640d91501007000c01d11440c940c0e0080e40d07030400300b440307808528002e4205034080c2c020203426110000b0105030b85402c1c2d03101c0100c641c440c0344204003490f110250380365601c03024800c3c4800141c031069a40002030385200604140d407190385e110b96038031000e0b50010700280c001000c0f030400266000018001d140d4020440c034507080e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 121788839 1250 121787589 121787621
    0xb0913020a08150301090b0718050913061a030114160903080a08090c04060602010b0f19060f020f0303010902030604050f0f0105010f0e0307170d02072402030d0f02030a 74
    0x215584030141c2070b240c008000344070180100e4412942a1001c0d013010900da0707445a5040c00303500d0700040280607007400c040001851003410700c000c1094208415003501540aa21800050308041e584030409010360b000c43c04800d401032042808152001d00544035000d00c03505040009107030001c981c20111000c1090b4908020009500b0004500c50408035003081710140307020906550ba00145900d00501c07a64242d8010349082e000081c801d5040d80071182100007120032000c03e102041c00c00111008200161010300007482040280704e000303086481184400740151360001091034520317030940c0c209a2002203107a4001040041620b85803150a40c082845640804242806e44d814403420f917050042d2414444540044c8003010f02591408412000003005c40b10748644681c000180307101d646071618414412007903031440703040c0041411400e4078a420140310801041c00341c45e00c2c14015808031101580010001003a801219010b20f00c600c481c5800b025075242000c1d021502181ea40800c126654 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 121790089 1250 121788839 121788847
    0x120c020105040513021605010b030d03020304150903121a010e01051e03060f0603130308160e010c020612070804030f0e0102250e1602060a0504051c05090a0b091302 72
    0x141c1c0c020341900c0540380281c4600e0700003a40104420004e10a0090a09005000a101c0e02c01c0003015003265440200a0f02641c415044021050701030780401d0b84c0050080040455803e04e01c0c1c044e501ca4034410f4000e142c414486040c41c80c0000403252100512001d600085c1c58614083d40c0007650780798100301c02c0c07030400e1900c03141c2e400c3d60071007024111440c119290300102041c0380f9038a03010701e6210980003c003000e549003003604d2031098881040380218003160741d020010701c03114a02d407810807011000c0e8565890102d14600119448580048101c2e44018213020680034072032509005407085070700c0c1d12035040c80d080504001c1d2420440d8400001001072106901920f642d0108001c0107802c186c9141d003000d0141c01e04840701c0404c41d5008808008540c00400680000043d1078106002d165001c0d84c01980303805d554482a1502100c028200d58021681051524402204c0804804a503d026402d2881600024117401410342c017543c1d03001d0703012840304803510304902d60051135003141e5000c520b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 121791339 1250 121790089 121790093
    0x1060302010e1c11030708010e060f0601080c0a0831020102210909090106080a231203010302130b10121505010c021309021816090602030f070204110304080304120c 72
    0x4203c0107a004180320070740000100c150f2010481c0801610102c0700901400d80110500c40d43c80c00c084500c4040440100f000c5200c650007088054054034030041050718101120700181e031394000207001c3c450700541c0a807901e14440000c5980c1c20390f4007001c81d104c172801140c5000081c80c10f9480e0700c0c4c15001c1c41811402d04143d0030503c00b02c9403d05001e48401c0e020380c0d11040030500401d256406145c16004d011150000c020038500c04a401a08402045490019054050360756101000008152102c1003006001500e0114900c46d840d644a03a00899810f0484000c03c0e45100302c014910082042d20b400c0b21002c1d200e900a000e070400308950200b031450324000000b0304a01d5006e0f03000c0d0080650511214801c0e4007034011604464001c0c04241f00c9100e03005c810355111804583c8001100c040e272444801040c0304812134404c45989900031820b000004010f410f16601c1340134100d034465512460410115000806144030340e01030b283c490b49170b140c103040444034400c0d075010b41800c014603100c0a85c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 121792589 1250 121791339 121791379
    0xe04200102060613150b04091509060b030106031a030703030926071a0c010501060f090e04050d120209150304060c0c12030207060f0f1508011416030204051201060302010e 75
    0x900030071211340482c40c118003000d02500d110b46034100c5096a0000600421240c030310b41c020070890300c0000074443c030f010740c4c804180040310400c0c040d82d51029010001000303c83d20903046100704081c407001d1112207100200001e403502ca85a48102c0106066240c01c018050884da40d4442081901c241803101717800702d95510391964464060244000c2043c00240b160204800aa80007010110f00030012545c41d110701400b00b041c00110b442c00110702c2c50340411165011000103001381e62010060162114140003074501c4c05403015503503290307036003800425001c0d03454134060880b584051003e103541c1c0c1094144141541e14190325101485000c4502078001900700143e040202d0151600503296106482c1c0900034103032149032005480d08200004800c1111540600612850607000152580c1e45100e00c034261010052202c1e000e0401200040e101d04141c03130030408005080c500149000e032908009002d0190303144841b00d950399280c4081c021548c00641140385003104590300290f001010341114 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 121793839 1250 121792589 121792609
    0x150a020c0c0d06180f0210030608150613090308011403030c120c0304090504080c0601140d060209040e07030b041b140f01030605090a090b01140117040302070e042001020606 76
    0x1e80500107080300d0109200303040c0c0c442c0038010242c58000729004064100f900aa5868003001d80c480e44205000c000d4981c00b03807050504440c1d5a0f4050300c007a202c055465445070394003e00b1160000704805208905900d10300c241001d10f44251030b100d00d00d505180440782400c0015140a00a60017004048620400010408002c07040c0b0642e4564a6000c0d141341c0d4254012a0311640049090200b80420810b803030019002d03030000c1700b0450740f031680ea80c1c91664142015000d8180c002042c240580040782094005210320304014102041039102c01080d1880e10039241e2060718078080c10b000748801c0000660042441081c141c0700058038904124040304000111580d1900c116000908000d40c2d90094100d20b000b01001011032540e45012008030003c1c2041140498800c00d1380000807509a0801014100852040e95200000410040d412940420180007075096208bc00c400003512410160520311651042c0305901100302d180030f8002e6410280c1180034190b4020800300507a5869002d0a2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 121795089 1250 121793839 121793863
    0x200102040f0b25140c0306101202060c0d020d0f0503070e06031e04060e010e0f06010506131703040617040b06090c040306020f090a0e07090e06040b060a02150a020c 72
    0x3043d500c00c120001000010070485a01010259061002d03050002404e4400e00d03000710001681c460a201404054441c58107d64480745150001c20074011000380f22810f8401030710281080c1d00e841d1464400a240240701c206800c01a03000614518030f055220700b010740852017034108030341507051809020b0822151503940d130307000c1c42000c0005100703007225200d541d20840c451740e41091035040c1410f280340580a42c000b415215801d061020803c104002507818510030314401a0180d6403e040c1044459071000304a801800b01c0041c011801e008801045d130404a0903c00860b66949407800281c040d1001d444003001c560000404c00c0b020a2036034900592080c01103034105919078401c000801e8074000c0340c1014200d18800b24000006c6010a8010a00c0a030100c0d25910607a555048048100c4000c80c1c4000024004401c104462002081c1294001000410200f2140fa0140116002d078114070f821000503440080481300d10013080004541180002d03005500d4003201c5d0342d080f80e5031b900c00e0b041c07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 121796339 1250 121795089 121795109
    0x30403051b0a051201060504050c070f0204090f050d090e0109050903160302070b1b010e060c0a11010b15070b0609060d0b0405030d050112171206101806200102040f 72
    0xd806010b9958512a0025000c021314440507160321920643c020205400b956008038500400b0440340c01c00b030016100a5a40030a0303102800e0415428040078140482d01200c03041507c500c000005075042c000361720210386c50394410581a01d000e11716002500180c0c0000035807032a040c184441001e010045a81d20b00c04801c6000c0051881e00c1c0132842c00e044c0e1750002180030700c04244440c001060750161604088580f00a0014406056006860b00c00540e40590b040c1000c001d0454103e025048041860044200004501c403205d404900ca010b2460601115003500141050801c0808000b941d000101940c40c035001c4d1804078041000811803002c041c0c81c00c00e070940003900b0000200200c40c45c45006401c10310003565100d40c8080c1c00507480b1011100030b00c0000b01302c003200c00000c0a45d03107943c51541d294a800c3e11a0024080041051400711082203c179094500500c82072088880060489a0b54030940c3c502c03503031104024804041002001da401000204003500070140407800340e0707045c40c031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 121797589 1250 121796339 121796383
    0x1030606141605030a020d021006050f010c0c0e0711251a19210212010b030a0209090405031306020708100c111902090109090b1501020109020301021201061103040305 73
    0x2d00000c295000042c01482440002406800c450f804900555541c50503003c80300d030ba24070700701c039030090700da00e170042580041c00541803d031b082d0b11401040c80e03050b004440c1c41f0410360b29800450005501100d640000c01c104034902c0900400c108141203039141c40142119038200e0142c1c0e000030b00100c6104030036104440c400c01c1203064188000325480403000c504035020710b02c641d61019015003400043c448107501513051190f8000c0d441e008660031403855407064081c03a0300b4098150f10942000c0e24148506a080c0324880b125140c102409000b240108011a2907070790044414401d1241504164110f40180d142085181c000290000c07030450201400b14151409100c102c9100700016140440c1e44111068081056220010501408d000341c64400d02d607a2200c1c00881910100c848c003d0581d0390715070004440d2842c02800030528041440045002c0c0986d400080c203a070003e801020600b07050400401203c0e820160b14600071101c280a542001d1450f00c0e99070b120704400e0055841095041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 121798839 1250 121797589 121797607
    0x1305090c0d0b0103030306081204050d060b03190204110f030a0e15040b0f13020d060b0a0902120105090105010c0510110403060c0512220228120605060103060614 71
    0x8460050003000141c044040d01d241814401141c2030280320035800b191400c81e002c540c40d1804107005000e00190504c01e03290610781418040a0704038102c0980b0581d40c1c40c0e111740041d640c14400b00c1d04419070b41000070a01500d9004103c121800e04070ba010340031004010b20298804090709403680115003030000038501011468041c01c041c421901204140c0151041000f0854440c4a613405001011320741c4a5030303900c0b18581c03c00030f013000e074011358480441842140000d215410040000c0c00c09020069265541c15403241a81c0007584001d402d002020300601c00d0303003421005680105001d01c4c0a0030558203d0b01c440d501e0b002c440800032000c1c0d4880c4071000c55080c0b07070400c840041d40d008074100461611410001c140b0303000b03929120b0b01001c21201244d00c6070450241c8076503969803500c6a030032182c0e5a07420002c0e008100218091180505081c41c6103d01c2c0103840030005106c4417450712900764041c540b440c111640104814141481d00800388000c07540840d4801d503000c111031803160b17101e20036 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 121800089 1250 121798839 121798843
    0x30f270f12020607090f030c030204051008100b1203041a0a0203040b0a031406010908120d0920032802060702190303030605030c0102070312050306011205072a02130509 74
    0x4400291038207849100d1807014650020b900c40c4600350316990001620b40760b821860501005200c0500141c130f0101d024009031609034080c98000340740341094060300703030b03100001420450030407030000e65117544008402c030900b032030b0f24038640d03e11004018510b891b0503c0d042c0d4181d1500c640440440003008121110824000c1007194060700010140d60307101d80e1004001000360891000c99019501c01c5c102054155019038440010740300800040c200200c2c544c92454515088034030040e1086864511440200d0000c41c1c190301c150715040302e03c60300140a1030a162074015084000040d401c5c403d1074182803c90f01d403041c90b5800c1e504130360890307481c84c0f1400000d001420742440307003200014000d000401c0603011341c000011210150b0503202d5001e0800010781c5c9031031081c0300c050034401280582c410350328420300055511520504000803400030911112017111000c48001006c00c440d4008071440107c0102060b9826071401c08080821711568085070f031014100d14009c10240d151030120b041d00c001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 121801339 1250 121800089 121800113
    0x91404290103060501051c12030218060706050915011a030a0b060309010b1003090201021005041a0108010b0a0510051903231506040503190501110408030a030f27 71
    0x4031481110256124203085004001c00e20840c0d1003580d0407400c12540c030802e040403610450b0000c14107020560200ba00360040d500404240d0808488641040000e5a0302c8010b090035900910300003d040c81e101a00390328000d0b141c035001140d803a4882c010485031900300b40e00c010641c0c09090080d241d40b00c0250440c042c20448001a0b40850301204202200c5c10541c030030040c5000440e1201c426508001d000d40c00c80d010208040d005801081045180104d1a081150440e106144040d584003011400d003070030311400e07044021180d448403100000b6140004014001d04011290b03541610a03030600544039101c0d1100022160880c40d030b004003aa4041c2d40805248450140b480d0711281030780404201700346084404d030039a0404e00101d503071a820407030150303400d41c1c2000d401411800180750388008006119403007121150341314038414000c1d03008007002c2d00c02000d0440c02541c507406180006810b55074004049101c0520340008140850196107520511244010301c02140c8c03a400d0412202004c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 121802589 1250 121801339 121801403
    0x60207110d2001050a091211090705040f1a0414030a06020a02100f0e060f1302041b260105060702060f0708040e01080a0803012105010908030907091404 67
    0xc215101c202806403007075562900301c1c5100c4072500742d100c0301c200541c2e40b801100002400618000d20910940340c070030701c0301184140100c07a00007044806800080140700d049a006000503030200301000080001186030b1301070440401c00e81d000742d5500b20640d090340281c5c817800008a400031140c0f240e40d1030502c803030190309800980035035803440c1c21080a50745035806c0208103e11481e20f000c0f11403a12003403159090070084000501882d86a0b402d2450203004003410348410180d00c5041031006039100e2051070b41c003001040c1690025102c62101820002c545c01e84210070409003c107282400e125828028103450040712000d4640f0b045001084840c040c003554031280d14070009503c01404040c4000d04204c4a40d610420416038807461059207802c03440c0d20040c43c2c500d0520041c406c10101400c485810200c040546a03510020b4a4076800d69004900c16182d0400007c1442090f080070311908000d06a0500b09121107036680f48041c030482002480944041e80da41d19005030b02904001e0826685 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 121803839 1250 121802589 121802599
    0x8040518150108130b0c03070f0908251d150d0201080609090c06030901240e060f0d0210110606101409060403051027050a140111070602030a05010807030f06020711 72
    0x2250080342210a9442640d008c0046203401101841b0507109000b0742082c0e0314114090040c0040501c80100c9100b039400000c44980c20000c40400c4544070b50f0032403540c141d03042013240410300705074400d4042d20740200c0c21a0b003c0d883d809547d10260740c00c1210650800816100c0408541d644a0090b0030300d0a4003c185a010307200005100c00828150000121076604446080d01103010300321003200c80300948512044148101e000843c81d1a10b000f0900e1892405410303c0a81d000550000c0d2800d21001c10040200380a801014540b0001704812680300c0e1080d21804a000c51305480504800100840c8803901940002c06000d1500e0340740640c3c0045600904541c540d907400d0984002414807111a5101c00c0d0300c03ca011410310189074424080c654101c80030313040d8450983c8070308102e50200080701c5225902d400b4040158040f20b00140344880c0a502d00580724185513031524156481030f030111620394000d00050020801503201c1c8080355910a80060707940c14145420845040000030041d884 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 121805089 1250 121803839 121803841
    0x70e220e190b070206011d0a0209060c250f0b090316080d1202030408030c0706060503060c090909010c05030112140d1e1812051908040518150108130b 66
    0x12039a1440d0401c82144100403081241e5240315040380d450380240308842d501036540761100c01d1104150000c81d0440d0400b140585000010000300300c2c2c95100060242e401d50090540610801510b04a90380d514503410001e51954900044084207040d00d0081700300b040320004540105035070400404e003181c41515500c1d034089039a25003e80d1034002c48c1200002140201e41004c1210001d44222071181d80c2c050f0405085403504030702603240d50000d403001c417000e0741d503144007041e20381d4100081803140100c5440c0e41ea44031003a10a0150380b11307018004407420303030414040c19002e58100302a02d06441c45001c82d1f140030240c40c24800c00769201c1001c011001d0040c28254103d10b0344c0010500c0c00d440814120791900d0302c00358800c6400b0055003000d6680d01500c50000e0150110051004aa0b175004104961004a04010b184180280800f044980e540e000504100a00b054030a28804001c605400c144900d06404070000306403d441000b4100b004090004010700042c40c2e0044070142c000c00b12501d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 121806339 1250 121805089 121805113
    0x9050a06050114071a07020f0f0f0c010903050705040207021f0203040603320903071703010501090501080f0c1b0a1208062202070c120804030b070e220e 67
    0x102014001d450001e02e001c2d0100d8246100e900454000940c80b000c0c2030b1841144421022024201600030400c43c01424440300c0446d4013084082c1c241e9a00c2c402070617030b0119940e0000d00e04030244403541c1c140f1140020410208030702241d8a003c443c1d007564090f0b9034960f0343c40000c100e400c000040d032507641180d560002c0d007a03500001074001e480484c0c800700300c450510001114195054102140702c8a05000300301c45000000c000f068001d840882124180801035a03001588102c21142a184500100042056682c09500c02000701800e08101a0604000301541c2c04614000c0088a00d40800100c4c060000142c0001001c0681e00c030082d543c40d03051500c0e151000500c0d540d64440000d4100303021076a540740c00c4030080320028405a80d1103000501109e0310f40a900f1080040e00c80b03192003140095050f0a4001032104644030303410799560b40c0d046181c440e04035800a00040100109258001c035261208201c1c2c1d20f04100860f4281440d10700141208054004030702c9a0b4038038020340079800740c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 121807589 1250 121806339 121806341
    0xc0d020c0102010b1f0332040c0902040e16050f120a0f020405130b040b120706120203060a0b0702030c0301020d090b1509070507030c081201060e01110d051309050a 72
    0x40a40c0d00364028001c80a802e030410140c80001c14403015200e070124200c0b201640654800c0701c000c0d2080701c0e00c0c280040080052003842041640e218090343d1810100800c0151032103080000e40f110360f008504040c105803550702000402003091065000c5080d0070115940140c05441c24460301c906095901c00221500d011041010740300703104420704203080300998425500907542030760006069101e8401d944082d4401400e02c0141d81904180e0300c0c00c1e801115261560341610100119000301724072032401000404207058080950b41d480d20500a03c24555200c040c43d5040b5041c08441549035600c030b00010341003d080c03110701c541c158030000f6401c407080e9a641102d1480350183e040e08986680b400c07840a40d4050401c00365601c140d5000004480c41d00500140000754000e01d0681e0044203d41c0d200003455128494400038242c00b8001000410b900c6403480354580c4003882c0c04059030490408444c0d5a07152810500148a0b000c961000c0c600e580f6031094004080302c040501140c10030182d650 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 121808839 1250 121807589 121807603
    0x609092109030f01090206180103020c0d020a02122d0f01060e0912030105060409090812010305010b0901080d020601060807030b0303190e06030f160507020904030906090503070f0b0f0c0d02 83
    0x781c041d0040c28a100c0e80104103210340000c461700606100d1800d440c1d036090703500c0c0e00181c04950741895424000102d810b0703010000c3c45420880c940060900c684580100002c85070003007011809a400fa20351850060807900042c0d03014103110300d0441116801c840c01364104003090012050a40c6806000100302d030050003001d000b00c40890940c0c0072084000702030301c118482409126001201044100061500e543c07001c04a540105002800c01000102c5543d40b44000e03172040d94030f80e454402c003180d1403411130b940c5801410701400400d0640c803c43d40184d140c0d90140316244c28031682d1400188454007036002a090a00010256aa60701e50351290800c00003008011500080c0c040b120008507081040440b4000c0c500c00180c1c0f4007940d26000903102800d40744812000b0807005000502c01621100c035660301032072003915032600795410311a0040040c502c5030f00c810320903401908100304035440ca0f00100c042c0c3d840380d1411651460000c42d0165548a0584001030601c140c14204074510340c0840c0070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 121810089 1250 121808839 121808857
    0x50d02060708060411040b09030c0a0f140d020f01030510050307030f050f0f1009020d0f08030a0f020301050105091306080d0c0308060d1101081003020a120302060f090606090921 78
    0x140c09501c3d100c003800202e403074100d07900d002c0d01c00820081c01200d401c40b015105528005044854030800740b00811071030303062035000a040042c0c64405010042e0a10800d8102540c00d0380c040d4007800054001800400344568903078107041d91800401e12607448200c600000c0c0c07002804480d442a40c0b458907500207201c000041d5841c1c01000d40c0c007011400301041d84002c0346503000091030007025001d0502c00601682c08101da020882d01c00390303c00111040c000210541c09441b03140d44a01c2e109030800c081e12204a40508210b1041006204903030300241920f000e0300d401d6501c0a0b0000a211078007000b031481e078000c030031a4445c1040d04e040c0158044c184460191095035242580d44a03801801380094600b0307001000601c09403481992944030740b00b05588425808039141402d603032034003c900d41e5103080e006a8544010025010240f50f010852380d5040148480d2840c035a18240c40420b803603106c0902418820500c100c041500004104107000301120001d0f1011403504580821001e2a4018490 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 121811339 1250 121810089 121810097
    0x30309021e040e03040f05060a020709060b28050a030b030102090d050a1401110702011d041506090f05061206010c05010509010203061509030d030e0703050f0a300c02010309050d020607 81
    0x4091070342c1c001300c265400c643e000b0031280145400d1408001440d0080c00c4640304600c6440c4001a0003146800785000a0007213078000780d41c41000450b4841109050041c0e4000710881d00580d8142590040854001030301138070300041c0c050703054030019001e48640324800317a03c480004409400d000001c5510f440461142d1810311000300449032050a07a52440301546c1c181c0300600184001d5405000f51a01103a688011060016030300c400140c202c030741e0042d05c0101e426031800d00380b00d01d5401001050152802c0b00b200c0808901d8140044da851141c41c80c0100c40814040210302240d0003511380e081025400030080c421444d0001c0141d00030740040300c5030f51080166803410740b4840320900071180c4c2d80f0006405072441000d0038030281d01600600030718120910039144c0000c00300e1824850191080440c00c00361005600b241025500b08281c02403428112080503040c903080c0c03141000040104240f8200744007040d00130f0005034010802100064180d0040d802001c48650340410039510480c06a19 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 121812589 1250 121811339 121811351
    0x4050603070e0403120212040302070501110118020609030a0c06030e160803030f04170a050d0c05250305070213020d050f0c12090a050106080d02061e0c0304030309021e04 75
    0x20805503103810707030310494001d20201004030f00440e108291120034190700c8007000d0f00e801d4042c024452800000c0b6000c1d40180c2080f181880740c2c1d0384c0042451851101000248524540c442c40ba045145500301c00a205010000305a0700b140c038140061016207410000c69604981c0e04c0c400680604649810040b850040c05180721503013548084810a0310599001941917035210310086401e039a02420aa13044800c41c1030080320f40c09407200504140352240c0d41c40e901c0c0d030a42d041d0034098400011a060034068244640e051001400c1582c1d4444a5254540440c4a10702d003000d80d42072041c004040d410120700803040c12155a40d0300181906403c1001c1040243d44619034060006415160417444c0c0c0c40400180717400036015100300c1d422825900c252001050640c0e209821205154000d40043e08510382c80320701d80b0307010b00c506540481003500240c45483c01f080303040c82c0300e20010140906000080041010f051199201110141e4007402421a14581d440b10008145110700c030544a00d080c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 121813839 1250 121812589 121812601
    0x30c0d030203130b040507080723090c0a0f05040801020a0306030201080609071407050316060506090708060d060203070c05120309160e040204050c0c03160309050315010501111603050c0405 83
    0x8401c6a03c50002c2005180d600b018079580c10066500180090341c203442a02000f042e80c00c420f10540e4010320141365a0190925443c5c090b50750032125910031132140400300c0401550044540c1100c0300c0340041d00e4080304202801105070b6060250360440d2045605c0800e0041c09036415510040581c1d00036244c403d2180d81d00d508002940108a0b0b422001810407408400b0b510b01d080c01804089200d001640d00301084025100c1c0041502401624403585039000c2c8101810604802c0b41c10080515090400c3c0c50900049501d00700b02100040c20240d00100040c2214860821082604d074000107440b481070414190081581042d40c2481075809650b25100071240310210410460f00e0341d0310f208296554540801008010003420346400c0d0320200300750280c2036014401891014020703c07402c00d0320b1842d1305000b0705d92032447c1c10050280c0d1100e204d010712840ca418069045490901c1c0c889030001851408a0401071840e001d61544561120301104000d00890041c1c1e5111042d030302000700381e07180c1e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 121815089 1250 121813839 121813841
    0x31403070204060b0922230103060c14030609073b2e090b0309060403030b10081303141b0606190603050c0f0a0c0b0601030204050a0b0c0a080c030c0d03 67
    0x1030365486032014180d50415058200d02d21403104102000280c43c0769007c20500118403101e480164642c4200e0050040080d02d100304089103490b8680283e502c0c0b0301a00c0e21295220182280c0c0c45548030f407002908107489504080312410b410300d1902616072501c503505420800501020305520b200303c001d5406800c0948850b58400703c00d2907000c060460203c8009030f0110110b90010812081000103e003001418006501801c0054000e0890340380c2030900400f159a442c0020f84251440c000c10101c0c9a2b1000710150004201c44200d840c175007941c81d040c1c4034405524003c0d5890b50021444c0440030100c00c080c01e03203151010043e40d0080c0d840c0c40c200101d0781c10340410b0b00d90841036040203006840c400d602031940704000d254402d00e4030180440c0c4840e00c5d0401150ba1000600c20980d680c1046401c0f50100d0300140c080c00c0c15820300c1e09000008900c4c2045024050104002280111418908018216020b6040700101d9514045031118544962210360038403c50700c1210110a00e003446 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 121816339 1250 121815089 121815097
    0x51501020d090603090c080a05070311090123030c19090b1917010e030d020405210c1302120112020a0e012102010e040606030203060a0b03010b0a050304020109031403070204060b 78
    0xe5031071001e002c3c00c2c014154010030100c5401c2d502801a0a004207180104000050500d8040c0c0d0041c8526480c610380240c00c84030034600c190240f880240100900d80601400049400c1c98811a02245154101082c40c02100c2d010083d4016490000c90420b00604449182030310640b04092000954400512000a0450100d20891041c8401c20856007441d0440c20b100c0c20030490021840c40e1118200600d0342c3c120300d001d80900750b4005420052440c28000082101c0f40303d40c801b00c1d560b1400d07441940c41e240c1d100d85150184450503410809408035904031031058002d040082c82558640c20b45004801044201f24000d809400011a22881c0c52a002d41242e4191030f082041c840401103440002e00e4121049050007060400200d031079860f801088040d003003a640058491910001b0000741c070310681e2002d0000a0308000500500c4c0140c0d0845410380d80c0e9007019552900d071840100d0f90b041d43c5a1001d0010300b183e211400300d01401100400540340221400d20405454000c00fa4083c45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 121817589 1250 121816339 121816363
    0x2030412030e010c0b190f050613021305090a090204050702120901030b0a0302030d0806040f0e10110906070f05010b060a020607080c0c011815051909020f060d05150102 74
    0x26105150400082c45003050041512041c5014114002d80741c1c1c1d0002201d2040e914000c840c51801184030442c4c445220b194240c0081c50030602107800d2071800300301e19a200c030303140540c00c0d40c000503100d030003d40303240e2203000500c8040c242d00400c0c508100448028032140070102c0c030031030502d4040b800307503807000510b1098410308594851505441100540080c0341899185400c54840c2400202595013070000c440c21024a80300c01c9100d107041404c20003110000b480d0b02d020685002c100041c8071b80d00040000703a07003a501034005046c0c0805900ca55060242403802a4031201c001482000c111500803495015440b500c000c0c00044080ca082141d540940c1803d40d005031310400020300d81c0c0744244100e0340c100c3d07200012645464500e0000c0d5003502d80101603039600782c6041400ca0208240000f0041d03070307140035400400c0790b4101585e80034404810520300303010a6854050607411f55550100320b40040500601c440d98070905070103100041c3c40c0803140c402500500d0740f0400c540754000329000b41720f45 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 121818839 1250 121817589 121817609
    0x100309080f030901060b07060504140f03120c0403060219090b030105060d02071403160201021207080a110304080601030b01030311010c0e1002071d090607020c0a1a12150a0501020304 80
    0x10030381200705040d03504000c1c20705900759220700002841d1610324000308680d03401418085298542800c204180104086c10407256620506a60000182c0441902e4200102a49400140c0c40d1030130172809501690300083c00340c904c001504103400c4c9131001d40f9103005140703844013850b00e9540c1340601400c3c00240300f1690402d8040001c50b80e040c200e0303801018014460072072503181c00440711130240f4640054001140a1520f050140b055607010070500c1500042408410b05e41081950782d00da85025041500c01441542e8840355403100c01842520b01400e64a42110303440c0d07030350381005e00740003000784001d81c041403190080da00c4105040c0075014200c4c0954480e0400c08015600780034402c5040382003130301103024007200840d9140c51406884000c0102829145490038000d50003800c0020251410044d58032482994840d0345612151000f1140c282a00c90070071520325500780224420042c0c0104e4100041080100d0584d40c1600686407680990b00c11a2042c1c45c3da005aa491052303002d03a01a0f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 121820089 1250 121818839 121818847
    0xc09050408070303090813080d030e01150501030513050a12030c0513030305090402040e01090b0103051e0c0d02071a1501020d02030906070f0b0c03091504030e0922060b10030908 78
    0x401d00a412504820344203031b82003460b0208070a0121007544043e04480d1045d04507808284a095050083d100c508410744000c000718034000e5280105d014081c07041605245d00c4000081510103060500540380d5040410307210034245910307100110032105070420011038600043c0c90389052084040d03828060460020301c0d445030954405642c90b800488129520035001c010204035003a030040c400b802080915400704120103604000760640e1001003031150f09002c0760040502c8030a030442090b401040740c80029607200c040b902c004001c0d108606c0c01400030012001e46070003411003803022038882d0001c0b0b00c40138540c00b010401243c4500c100b00c40d8a006038028071044e10348e8580303c001403000f140b10b180202003910035540c0340704000034125100f5103403840c08420042c1700d000c180300303600e1446000c081070f011302d01d0244c3d80506045801e0211038042c1945400198207045d030110700400c2d03c10100d00719800b101207480c7c0100603045591b4041d000f5000304d40c4e2204514042e000d451701440e8091b16030382c20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 121821339 1250 121820089 121820093
    0xf01030b0712020d11030a0507030203040203030304150b0d051507080106020304061d190e06040c12090521071703010b0702012a03030501080f0d08060d060b090907030c0905040807 79
    0x2c18aa03400791a03000c56401c201c00e120418092140d2080303800b524402503100e01c2c013203940301c04941d4002e040700306141c010420040107940c040f0490340d100380d0101040303024030025505030004040701c0510942040991007070000344440010001c402400340c0030501241c0c0c4c3e40d02000c94001400380303d054050b034000e2105001d1140103400c3c10202c00182e070000510352010307400050350130011122040e002d100e1a80e00344038002100500c0b5502c17000644007031140c03400c001c200908013118ae814801d00740c1c1d502d071041c008118040c080301a04051500030b908800e11484c41c0280c041d03002810440d03006115159140c070918108065904a82607456540d0400c52070b6001915203508139211001c11030035010700c008007503c8440a20fa01300703001c1d55000980350b06000c070162411201c842401a16401902c0a8032816070050b42e05a00c441c00340d8003803070200490b2400e2405071100c01c101c4c0342d1050803002000006400020b038042101e0290b002c00c1e8107c0d0340c880c480d404443c0300b5038015004940400170400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 121822589 1250 121821339 121821347
    0x12140a030e0a0f03090510170103080304060b030604050609190b010b07022e12050907260a1109070c0b04080f0c0a06061518090b01020307140102040303080f01030b07 73
    0x100c14204041079450700c0b00541e031421207034460325204a0214248134401d101071b080ca602107000074170781802c26000340d07007102e11070342580c0005100003048024004005010484a40c0114180d60303c06000c0f02c2d0141058541181c450200b192086a04e1107644000403001d000300c859141e9154000303000c400c61740d00b440040165544030f16020307030b0401c2140b1118613240203401500e40940081040f801d80d0101e0701000100141c060303605084c051410300c4103205407100c02007410f404841131f401030072821003014046401c01074080c196030030560003110a0b51061140b4001d0050341503104640d49507081d0385001e01030302c2c0d8011061000e803142980f000001d00142c043c000810311500c0501c0d005003000d425002061800450703941c22070b40c0e19200e400030440365461135030100f00c0c0303511820898141111044a00c00000e13043c4280f0320700d29211420106641d00034811074840c1500442c0c522040418848814040d600c180706c00c50004031100300088240c080101194180ea5021031141066152210212 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 121823839 1250 121822589 121822601
    0x5090d080307050c0a030807020709110a031a0a060c02040e01061508090a060603080c010510080a020105070206090a0b03041106090d08031b0a1106060301050103050712060603060f02030412140a03 86
    0x2c420700108124007507055504020781d4082911980e24003403586000c20009040c4a82036010f14070f140c1c01d00e009003801000d0802524a41420b40c540000d2003405040012a800103400c131143c0c100000a8000ca40317a507104101c511a640250340901c10103007900c0c981c40c201e03038281c845c580c00100341c10814074029120b0b0306869080b245260844031201d09a4070b5003c1200c0075039208592000e0300040310300b4060420b0007096440180440d08910007480c4c040d084d526103401b404000d04001c400a0101c08541d40c82040d181d07030540241c110901c01e911507423218510f42c0190b8058030b07411031300b08002d5100c0c81c04004441c0181c034007404081c1c0104007a0b1750540640c101600d52554501d444124401e02c8001c080034002c8624a0b40e140368028011103400740c1840e101524240c040c2c1d06001c01403010600000b024001c450a23075143c440f080301d030303400d01c00c00526094000420945c1820b0402a03003c0881d0061030040340194426204a0360044085e14141882202114205d200780b040c0070781c80d030180d4030030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 121825089 1250 121823839 121823851
    0x1e060803180d210f1206030209012108123408090c03010527010516050304031106150907030b0a0e0a0b060d14010b03040c0e0612030d0603030f05090d0803 68
    0x59180f10a000210041e0307121880b08640c006007402d010b030004603034002c280d40040b015109081040c58295000f01e481b01c0014010048003405c0045d80c051060707081800551025040b00c5240d0301d422540d01d030000c91b02c0341590822171204540092402d41070030340c1501841d04214000690314101c0e6114151040a03005040c50140d005041d022100b9031007e0042e181f007a4050103034112140006907100c3c0340800740d04850941a0325183c100150859650b0766458107180d44c2c20601c0d281d64840c601140c0c0000aa5100ea026000784018099481c04500800c8001c51040791084100c1e66402d804800302d842c400c51040d40000c444000700310000400349556001035035003001081c200403849c040b40303141c1e00038051040301c0e40d0b580c442c0b19408803c0b03000607409404500f113482e00c2d6080540320005020311502a508030500d10802184581d61140d1845410728448000e172a25070241d84820703402441c5602c0180c0100b4251210300940360321503000c65940c40c1d070041c040441241151240b0b201508020300d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 121826339 1250 121825089 121825103
    0x90c01030f0e0d09090f02040f0e061c030905010816020c0d060605041e06090204080a2010030917040f090203040c0e040c14101b05101e060803180d 65
    0x2108440d030b000744000036a00d051500ca400383c2526042203102203031411648642d004d84148420302c400411901024112800c103501805280c0302c82c0d001030314401c1240da0004815280c18044000c154014901d60120341090302ca018413592466450211079110311040c20058100b0070a8000c9446c016400e42240f03809a000000c03040d807079001003411150710300305110704c1c184c068001104000c0070b4000d20740600000e0a0070741c10311f450529556560b001ca18401480310880d40d178904070440003000c5181700740000812940041d03014110180c01005851070644000c0030010803038007541b60110458044412084420305468a0b0600e054000e40016204542c41a03a905c4001008441a00554040c80c090000481c036240380950403582103803d822200c0c01604040c040c000d64640080f400f5035280d400c200da405402d181c80ca0700d541401000001107482a19240e40b01c0c00a010801518000c800c1450040092946880c802c0d55207000d860850b04040d8540c607440b140c2c5080051101d54458800c0710 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 121827589 1250 121826339 121826351
    0x30c15090b0f04241b111806121c050d0b04020d141605071e02030f0606031207051b0a03080403050a1101050702030705220203011418090c01030f 64
    0x200c40441c0d6004404600d03030601d0110f428071004520086180e02003000c00329802d0090310207040a441600d00303243d15600d02c90741c00d07401e0080c4160030103070344008400203040c2d410480c4607200c0c50f000508150303520b81c018550758940ba4618840040c100e1041a200319801000648540c0308581981c018885028410f4903444900c0a580f1640060310441c809058041038000b00e0304000e10f120300008242030104c400170310310604c544e40c21034210b403021034201142e401030301d200101101300c2400007140250503209200c0300b429041000309490f40186411429200407070041c0700720307000c140106400605180c020000703c078030900810744016187c0601a0050006640c0c90300c480410f80c0141c5d000b80c031170b9004075800c201005061290b0000954003420012b007401c140e5004283e442e5924010345000d0140001242120034000c145c01419004a200a540c3da6850f4502ca82032020f01062080c059074010030f000703400d01c562a900345d04c0740508100801c01050303050300441c09040b203409458203c42d6680c0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 121828839 1250 121827589 121827599
    0x90b0306180601111504032c0f0f090a0509063105250303020c060c10090813030c080706050309060a0b01050f031e0109020a051608041d090d02010204030c1509 70
    0xc850700b01707401c00c0e00c0d183d0710381842c1c141400b500f4181017400040c2d02d15058a039842ca034150608101030300a505490707408611920a000c035020000e0714003055070254404d020000e2091107504428400c1e22004182c0c2e1040d195146404641103580328140c02d00d500d1020480c60810b800b0084c0e01075607000d5000c4442d10344100b582c001d040401000b82585894401c101801030640400181e0403042d02610058640042500c0035500c3c5c00603038403c03080a0b501c82e0301103400d000c040019035030400780f19400121f1680c1c1c2c91a14131580c180d5031103004030300e00030940002002800f480a43e4170850025000d0481c07980e40000140081032401a094180310060100d040b003401c9039070185105800c00c1c1d10490054072090300451070700905178002408940108815159140e014060b19002a0400f501d140e884c1c0d402c1c505022a401103400000480f03403603004107003100c0301c44142c0600800e407400948910300e1200604034282d2195000207442042c01040c100708004d2450781d9101441d200b032400700003044d252 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 121830089 1250 121828839 121828843
    0xa06050403050c0c0102120d0f0f0f0204050906040203060109170106080a0305041d061005090102070b0a05070c0e060607020f1c0506060f010503042a0803130303090b030618060111 79
    0x340d605900003039010890b1407454008104603030310414240001c110007615020b1000851241c401190805034442c403070400d00189640001c080c40382180800d0014406140d0340800942185c444c2d41e00c500d69100c042401030030039208480c0100c82c183c4d10124154100003182c00984418400340b04e07650359451000401c40000c0c4209070050f8402d689842e50b03030b40341401800d16200081310042d0491195001c0c41042d6030f0780f14468034900c04a040490310358242400503400c0480c207500401569800041102429a026006200c51403103200074101c100d4a4032002418a0070031251f00350009000c10004001d46421040c800b101d51004010004207082041044203a4200c030700211980c0d030203181408500d142c02d4461419a14081ca0010b0071454140c5988500c00000303220b440b48443c8501c010440b080070b2510800103000d80c0c8085aa6070103590090310a0041d0f45e00c407e07000901000c8004c25042e8051040b030f4080c1030001e02c01107440081c00a064031805014010a052240f29a0300c040700d0303041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 121831339 1250 121830089 121830091
    0x1006110a020f240403020f0108070e102007080d0f0207031e0819080a090c05041104030503120126150c1306050702030d0201021306110a1703070207061b03110a0605 72
    0x1103c1d603281d469078514810300c1200d41c8002d0301d4a0501c1004800c01a000340d014203444003552040394590703100b83d00d0140035541c9039809803844540c0504403c055040020002e11142210f40050490710020400c2d08120740c0320140c402e2920041c2c0081e0020000b0988814012003030b8500649002300c4100c196a900503164840344032500d030070402c0130940709403130741100080382d229410010511000805541d01c5c0010616409542d201e65a1030020118560080342500c020310303440780c01c0b642d075038441c44040200407500744a29940c48003820800320050b6880d02c40c10050004620040200c4280100105183e64006041480c04030040c0b24601d01803079103501d043c3c010302e51a00c81c03546d115080d0060509000300031035841c06685c0104400c102c0d40b0410703051801110b04030700e40015007002d9117100343d085c417a2540b006807085003548070baa46501030001c003d5006002a03003ca44506540300d405032020800505603030401001a603598000c80d0181310380c11204610b540560b0207801c25591590700301c5030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 121832589 1250 121831339 121831399
    0xe06030712022b0b0102071a0d090615030c0506120403031a100f09050a030b0105010f020118060c270b160c030501090201080a060b030109020705011506081006110a020f 74
    0x403c80105001a080c0c0d00c03500140000a2003c0c101c141d08110210f0442d48403225206100d4500140414024810740d10024056a10903020b000b011491002c10000c0109030000385c072880c0b60b004c0d0001d501d1810204840c1601d0a16138004841d5403261400e030000e08000000f40c00c505400c00351040290794010b80701d0041d0883ea00d0b40e404850081900a10000341508041c0c05092a034000b440031449024085d411180241391030b4500e1031111808901420309005803004d0090701d00750100030464590011440c4075100e40d241d040945d543e07580020780c142c0c0990151403030308000302e09010702e900d1040100100010001c4402588070242c2d950941d1030b03035950041e00e990b59a50301200031507901030240c80d000070500300188491810498078107041c2c4010710400c580d00b03600103040010854207400c000d203014480801d00e05800e40e24100070b424042c04403518010b40700c04800214502d8010561007101d241c07441c00401c40c800041d4280000c58907055011540443c007070201c450780c02d48010800d65405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 121833839 1250 121832589 121832647
    0x90c0806010603060602070311240409140603010c09090506030703050a0506010905180303191d01050a110705060412140412050106060903020d0605061201020409020702100e0603071202 81
    0x50302d00b94004048581e1030704120308540080c0310410124111081d000d05800003200e40524403c0d4103050060690405c0c1da1800d40e00303501190004040505601c6400f1403000720380d51480710f0742d40c03104050886007070000c5907005c13811b841424080007080380d0003136031311000250440d85416100e44501e46030015082040751660301440061060540034064650004003140f0b590070040051480c507512400018000400942664052014102583c100301c5003a54110358459000300d4104080e0b004e0001295044102404d20240502070841c0c201203d0741590402d01070405502e0750341c3c0b41040b0b440c0c0a03060604108800e900e0003101000c400091000309071520000341541c58620b040340c02e58103140d105a06100414500700056220b000032080103640c003c00005180c0d64003c00200440d0310341e4500881588003281c04616060700c0d9005041d0309000700e0300c280001c1c00000c4d003241d4400315407640f40d40004090001c20b8020b40940016a0711b510450030140c00c013000c2515100140d510700700c00182034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 121835089 1250 121833839 121833841
    0x31605060901060e04030207180204030204060e06090c0f040b1c29031b060c1e1b040b0f060a03061505030103060c0305100614070c0f1d01030f0f0501090c0806 70
    0x500c8244a40d900821001c01103920515081d1401f07502d9445604c2203180d400f0600d492200460082c0d0b0450b0301440d8020406c12903161542c1c8000504c200c101d80b940d020703001e0800458184200c91342541c495070311080c6203d150600f0011340d201e07950001c0406640d014002c0380300d038032514814000c01c4601107081245004000340040350082040200c2c2d00c95002c6d8001d101030400d2040300b0107030b400d240042618465605d4000c155298074006c50403c0b0f1800c01c2c103454510408010001c5006e034980f84418804190380103401040104a404504505a00c103200712482c0085080510281042c2802c81c02c000882030b0b516181c400d251020f40d0340080010354000014010041c0d1071040c022800381502c1e04101034540f414122132640110702401050121802c0c031140000500d50403a1030701c1d030340507060740c844960303e4618820301c1d0900e0040c000e07418010028203600d540c094203024100c0f40c024401048410041d1101e841a10200d00d0503207280d501c8a144002051b00c2d4001940101080da00504003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 121836339 1250 121835089 121835101
    0x702010309020d211701090e0f01060f090609060b0d05040326010e150d021201061e0611030f040504090602071202060604062705072003041a030106051b03160506 71
    0x84e1031120301e294018030500e021000499601003810740d05551034802c0c00104508510419860640920b400f03656960814501003610000070000c48111260b000092040c9500e5202d62402e548160042d07907164802070000302e404c404582c01580d00316001c1d08000302102058000008045542000c8030300d00c1c1c00384c00042040b6401010300ca80c2c009111640b03c0c900e0b0003104000303446400f5041029102c1d500182d4012403022007075010f10002e18005c40340921042c0c140501017000c40007842940c0208240b00d1641c092040040100d8800d2000210014a401d042104120003003040540a640840c1c1c280100c1c800501c61701d000740c000c168190000d00d1b1500e8880100f100355896038015601c9040082000c0005451106020041e005000804510303503481440840d0308021170710700ba049035404440c402610b101c0c04030007082541e2117240c1c1c501090031044003820301d612007881040d002039410051000c04820b162620007411800d001564035000c0307204242c1c55005d195200c01c3d42e05421800500130 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 121837589 1250 121836339 121836383
    0x20307080609060319151a0a0b070503030c0c03041d040c050f0102070b032a0d110f03011e030b0a02090307080c09060904030903170703030c0c02150702010309020d 72
    0x64441c0045900d840e0034940031001c00d8940c40b81c040c0260443c10000b2a8000300300f05040e203521030040241c800c002c885250030035884031520700c03400740b0b024021b1003402007030340030540d0102c41c80548c00000941c81e44d1202000000d0b01d60100300180f0b1980003d110100e0101c29504404617090002001d0180c2c03410076040103250103042ea40014410460003090100e00e0340c002ca810004c4940d0780d0f0b5090f4482c2c1c2d500303c0e5900032006c0d104a1403229403011101004d603041c5180500071940c5004010480c0b240b140070504218441c0310340542c014a030034401005100d90614070000d40c030800100899506680e44d4442200340c0b400c5e216040b034650040b82600c5d0a05041011000a04202008140001015001ca804910b010344818080e45180c40040c0915004503c0e140086034040d81c944c0b150444092024440c0d0418102100003074140a4500002c40c0700b141c181c80e00580080c01c5040c0300c402214944415403008034103c1c149504c0340312440140c2c3e1802140c020781802040400003001840c41101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 121838839 1250 121837589 121837591
    0x1b0509070e0108010b07020d020310052d010e06181503010c0203040b040509040215030a0207020f010f1205090f12070303200d020702010e030a060b0114040303080a020307050c0d0302030708 83
    0x44108508101e010410b603038030412042c1120000c0c510540e036080d207800440c04c44520b540020b9050302c40c46e40034484124035540064030441401c102d2105036205520314000581c0883c1c1d04541d000102c070300502180385140b1180c1d80103c8014801000400752210344404424215141842e460107204418900d04003805560301500440c4007075440c00d030500090501030f0089001d5030b0300513250003002804640f2280031003d080b14013401125200d00d0004160400b03076025a4040703000d0f044100d15010303e54003a55248400b040c0c1c2d40c80300385c000c03800c034038041c80100402486008203210390303c4101402d0505021090035051990f00d03884d0f40340400d0a014080d1044410038602e403401203002c075290317000004243c41c003880010b0000340e560f0240e400102d030000b4000d040503505000710400b4604020341940b160414900030703201c07082050680c00304051180118440074010a2404001034840702e0f2590040d503100107036062003030511120b007000514140c10a0301210200754000103220826030440d102c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 121840089 1250 121838839 121838851
    0x607020f0f0d021b0d020303070b06010306090501050f0d0303021308030304020907021207030c0201030609020412060c0306151215080d02060f01150c0c05060f1206030a0c150c1b0509 80
    0x82c2803040da2a04029076503c480c0d64020700340e0b552000000c450350780f400440d070b83c03041d0018102c035152a00ca0030220500a001d468181c0401d242c05800550640303035000c0d16040310f40040c100450540000300340407191a00c80801c800b015800c00014034642c000c4100c15010340041c000440c1c41c0e02e002d2040c41117140d0050054010340d03001030329a8002e0129101122040b6615290a0f010030f070380da1006034080c26458011240b05030020074041071122a2030310780c40f00c40f030042e00e050010f0382001c0e6003902122a18040d0484042d000e16504202601071091000340ea84544030004409010200388242c4c407010340c110401c1ca400c840e11284266034100445904041c3c00e0182200552415184645d0321861008071428003807a40c10200c240140f0500380c000802002d0700095580c040d0400246241d88120b1200c4110000c10020440a0500046d000c400950094020340150f0401161861a04030012040d08004884800c8800513000100c0390740c48204107007107100b0050030081040144032000340740c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 121841339 1250 121840089 121840093
    0x140901021603050f1306030c03140402090a150b0a02031207030b060307030c200309030709060e01052b0503070b0106050909160504050315091501030c0303080a09050607020f0f 77
    0x2064800c600314030070341c0d15402c0d8141803c6039250103c00c007030070590054441071120700c5d0b2402800a0300c150987c00c401480c0e0380940d010011b20410440c5c80d0100601564065000501c1500140c45802d040d8030031201c8d4010460721050706503446001c84581e07880f401c460801a080441c0180f2440e00c940710494104005050038403107280703600003046950100078550741c105038903003c070100640d008004c0000540708030751625029100326488203507030703501c50180903009104401700002d4501062003000280ca0741c00c00c140c0a16481c15041004500c400c403c810303541d21050a104011098402d08510211711a40107941c031281e05040c188030484050303100c00c0c144081008034a40903990040c00740d6000c0c01d40800910400f444000890341405a034101030f4240c4100c41384101281c5603900008d10400c00744003111500001640704c05461202840003d050440c80d1105000182c0a812402c0d80105501c10014070a141600c40d6842c0c00781c00e8075038030090f07003100710034819102c0305106004280c00c401c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 121842589 1250 121841339 121841347
    0x105030a080a03020307090e04050f21031602070518010f050603040302060415112b02090619050904021206120303090703030e19030b07030609090201050301030308151314090102 78
    0x181c0c0101c03031045003100010140d000000506890090084001a02e9140c04440d4a40340518003103903618a41c20384c21407680301d00146940749002130350352294880c3c640e003c00d0703080d500c484480d14a140f03680360100c2d0550040307040c0894280c42c2c105400301c2e82c0c407080603060303280d501d00700312035040443c00e8003c940640820400c2001083c0c00041c050b03002988000c0e880d0001a421850300002c1c088a2166060001c00052035003003440d61900032903880356124022900902444c10080803032207940c041e00e82025007406003408100ca144420241d00c81603040c4140b03800c40f401c00040880c1c0c02004450038140b20441445000d081808000c01103103054030003507156003816020940d503206584802400c0052009140b41c16031900084044850080882004510f84070301e401c642015041b20314900091601c0300c00127030940705001d414040c40d0103866452175a400c40d20704139603601d0300502c0c0e900d004601000e00d01c0d05454000c0410840c516007600000d10500c42041e881d903084000d041070340c03c2d82c0184 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 121843839 1250 121842589 121842593
    0x2040303050313060603050f0c0a0e010f030b0403030b090c040602101a040e1507020a030206071419022a0a050d020f01030e12030a090b0601050a0806120f01090501090b0105030a 78
    0x74040340c0d0000312458800f6032651441c41c0c0307038010b0011030300001d001e40990400b0000304100000d022624103022182d2104403a01c5454229443e82c0c24411402c001001220030004284403040f015000303406071902184e03c0e04040003064070500c0c143e82404a030b2800003000c0148a5040c40141041030280c0014041110712585d80d400200740c14814505c50380d6594004141c41000704000000e155421900341c42c2ea01d01188081d45038032000d50158058043e07640050032951043d0694181005032619890901d14240c01c0e11092080241940003503118020851a411265000d040704603009003a01d00d0307075510440c0511100860541c0b01c82c3c01204030807141001603441080f0641c0441c0c0038600001d2448205100603e80000f50b10b81c5c8214000c004140201c0c8a2141c00c640c10302d5008241c0c50b08143c5803000112600c5c0302d028450b000040412000c11003a01e40b502c0f155800d40b0707203c802c842c2d40303d40c1b00e40e245003142d003070031800c1741c05a558020364000c00c842e844203107004000480190a5805550f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 121845089 1250 121843839 121843847
    0x105130f050103060b091e0406050301110717040602100209010c0f050a1103010618020d060321020105070c211146030c020406030f03020309041a030c1507061407090902040303 77
    0x107610400d03c00d45c00546080c8260f148c82d0300510080c84020024841c0c002c00100076100d43e4095101038035800c20f030307403001120304842070300320b41c22940113500820f40c3c2c50180c0c01d540700a4000e012810304100302c4400180219442d441c1c0503101d103001d48040d090b000d11600d000c0c403500d5012031102d402641800010000e87c5c0340f001741103905200b03090300560343e0b030228845000248000e8000414000001c582c1040c1c244022011901c0c900c40d0341c008024545410300c050307403901c079920300042c9420310b0208a00500707280b003030075017401c41003030b042103100714000218003800e240c0303e80740902400c40c0c21400010240046038103090408401c52032204000e40d00000c8000100403d1710240034480d8200c1e40d0011074a0f00e07404070004540002c0070a50040d50341c60021748075408039a90902c118100503035520003441c284100d042d52500100101300744100c04040c000d5003036901c611600c15450620001021a04601a40203981d514038003600040c41d200340040d01e158001c0d004131460360b1050005000003500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 121846339 1250 121845089 121845109
    0x20c030a02042705030d060504020301030206030604150e070e030105011703030f09032115090609061c0209041211030c07230a0f05010e03030313110105130f050103060b09 75
    0x16900400d21090083d603105a144100a00ea02d10a40000e6080d091000100c00741441c21040601448250754600412044e40800e00019500610400c049405840d0075400003201080249401e41d8007552020140b005070700803540440815000011802c003031400380701d0bd0780034141c565452500002914116681c070b000c010404101d031a0b520021940641e003c100b9550b429401d025612440941142200030000c01503549401060a03881607100030301d400c0304501c0c411391016210405543c0c5150810400d04210350070b0b00052001d90003004050384480100703520444c00f91442c810341c60052031005010400d4002d8031100d42d0824008154011030200750035045451403069410700544009080c81407036072010000b907000c1d40809000806000741d4103814115035090300c440c5160003c00c0145506d1388000c41d00800340501c060b10840025a510203090070070401131611600b49100d010340f103034510010750040d1305100d55070003042081c1d60341801083d002c3c050318101a1300300603495001c1212804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 121847589 1250 121846339 121846343
    0x218041a2403010f1502010b030a03050d090605180c030d0801141c0309140102010903051c020405060a020a120509010e0d020310180c05090106120f020d060b031006020c030a 76
    0x84403807030100180c40c2074091210028441000c0d66541e4800001d04a04840c1c41002c408190303c0d040076030b0342070040c451038035400400380141940a03910b5070112100e070300890955088079920741c0140082100744c80350701c0c8506508500c014440030400c1000b0329102c80703043c505100c0c0c1e101d0140d601065a00c18102c90460307240403c0c5080c4c103005107000640708040c03d5070000034030429007828802d060f408541d04081382c044462902110303a48800490a0f60202c09014010900070810f4403003d030130104100b4401c04103100018102615440001c2e07481e40103180c1600140c0c001d98000301400781010364911281e43c04c0c145189003070311110000c0d16204820310718512500c803840031801076441c1400805005c0718062820090320030f0b0031100800c500c0304600c0071b450300c682002010610341400c0c000141a50310300d4a6116540419001c100d0241400b0000001c0c000d800744240706480d00c450141a000d030114040240d120300c1c0070406070720381d100300c1e80c01b00d4215030144011aa06481c08070781201456 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 121848839 1250 121847589 121847599
    0x7051507170603010f020f03100b0f0a1206050d030f0215040b040b040302100f060303080f040503030c07060609050109060501030f0c09050f0105070515010617060f04020c0a050a060218041a 83
    0xa503a200002c1e006050171969616443e0001450034008003505008610034840c10403103444503500c0d5140f404540c02800c02d00459803008010070240d6070300415008291500c8100f000c119607441d8408a1010740a621080b004591641310803100f81e03805101047c15076440060a4296240c1601d810121104c00381003d0300c900c403083c0101d0f0034580300344200301c1207244540c0207000d080322400c5001c0041c59940f00c198005040040440c1e4bc1952500300d003802550407000440c03d6031910315104101da405080212121583d07118009001045801054000c009180001440614001c00902a0348080010403900d0f803a1104144c0016003000e07443c0d0645006a1784540360310044801610300303114501014000b032082034100301d2881e6558013410b068450558840d51103c0d845240404065019038880e81d101e28594106c1c603090900350302808401c1c10b0a005c48500c0e450913201c540c2005d8003210107480c1030313400051220721252074403111801203105490401c00409e491000510501076485021320032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 121850089 1250 121848839 121848841
    0x91401020d0c060f060b031b0310170a0f030905120c030d080604240501030b060a1403040f140a03030b06131703120a09020420090d2102030705150717 66
    0x101515510130320b13481007004070810506072240680032082d0804c8404000740407904904000c40304030401603034000c00c400150450414105144035180c55801092140184141812400483c01d00841205104d02948803846d000e0f04200502c069003400c2c0e00429410360100701c1030462600d001070021004000707071429000e40c1e19040009006880358400000000740c0c40d1403804c0b0402a035030b02d03040448400342c908100c0e101680b810700a0902400302720b007002c240a4209000e08c52810b100440c0c0c010700c2264640301c0c242d03007655030f40c00480000311072a0141e8404a0303814101505442650320710740040b03813140e0a0580100310407184000a000340004032040104010301a9420000d81e0040b40351800b2a19142c81c000400350020000780c98143d201c1d03424115004501c00e0708100340318041140300304486c500494035060219001c509181158082c480120416120344126902c400c4503c1e42d90155550709074600b40503203400d1100110b00460b1b4201801d0024076504854004942040740300700a0903 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 121851339 1250 121850089 121850093
    0x1f030c0302040f0803040807050904050607080901110c011506021614030106030803130b1308030a02090d060612050f0c03070611030c01110921060601030b030c13020406091401020d0c 80
    0x190041e035129000041030440f000c9210540440603105a404150032240026944c1d000c001e0051020b8a0183c20b41d0410700108040e6032150700c0c907590200713505c8000310381c1e80280b00c401d0007650301107903c8202d00d0750359410801c560440c42d00058010280d52000784006580740314056080c64082c8101c60b804150880c1c00701068070300303400108c000e58202250340d88918015411040704010a981210140311100001d195008010303504442e142d08145190f08640c3c810fa0050003c0d448400c640f98010031400c4801c000031070078020000500b0241100b0101482c1d140b0f8154600042c108402c5401d0300100040d4500d81c0b00045e2440456000d0310f00741c140d80a61801060a6214010141c000f03542007541420809030100d0050110a000395030300314a00c0c002d03a0307501807241040c2e607041032140c20402c00700b1080d40c4a41c100400402c40102950a902d40c04400596035490b04000700b5903064012408201054107d07140c01c1c001d000c004140000710126200003902c8160116001060107109208102 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 121852589 1250 121851339 121851341
    0x4092004091508010f1409070303120c030207050d02031e03060915150d06050f060c0c120c0306160f1704020105181201060509010801090b01090203061203030a0e0c1f030c03 76
    0x30b11a0030000c01c444400170760305030058400c0c1452600b4510910010a10a00000a80b40212501543c03460120310007004c00070045c0900c4011101003540911941020542c00e020030301079003010750000d40c0c0e60004480c030300c8662000c80b00401d00d031907010300c104075240e15503e40c41a84044030307030082e04100f890180000c10303449000004110310b06010030085200c100552050040e20317801c0714000140b504e4441003003143d02c6480b0b25646039170000156003500c1c3c10b0000805540d00762080c00d0300c204420710b40109103840000c880c1090102c02118001c0852504150201120308a61910400c0350810b00e521140309500508000d0420200150400f46090030080070400902c004001c140d00071052001d03d0f01801c100d008180c8290000000003038815014440d000c0000d80c040c61320400303a0301c1c01c42004001d400003000680c00405207040e44421600500003076110b05084a000504002c4c1c01c1c80f841d00d0025502449405201c400181000c41c1c84d19841c504d900596924000c902c116655408034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 121853839 1250 121852589 121852631
    0x3030904020a1b05010614041b0e0a080d05071505070503040f2f12060105030c010323040f11100c1217010f0602060f060d0b040507030b0c0409200409 66
    0x1090860544000c3e90401c88190081c60449007680b829400000200d004c01080302c544180556401030040c020740b46080c007540080c0710000d40102a0100555a600510700380009203041c00000740b400502d80d001c03c00b5112103000025002c0d88104850f140c0010007a128ac4000b5001070800520079030f0f282d0800440320190494000c0078844d116908240c0040b204c240b000340c2c2541c501c500d011510000703d0400000704075040740c20060040000381c02c240b006400400317807030401d070b0344500380c9441921244c1c51200c2d510707005a2050800d00c400d07403503e00f0f0500e54112004d0141744541c180003110411079a1002440070f605070041c0f030085203600c0380102901d01c1a8500d03881c00d1400001d00000445000d14940041101d0550302650b001e640c0321404058031403130803255554040c1004030694089012110460781c4a44500111038540e40c07241c5031181c042a0071a422804242d00180c02d0007107100a024025441d0401e0030702504018161000d62150b001c3e0b40500703580141d030f03409a000300469040600c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 121855089 1250 121853839 121853867
    0x40e0901091106250c03050c0d021e1504060206090d0c05030409050a090c170106060912030503090f1f0c020606010905040b0a030f050d030b1909020a051911010c03020903030904020a 80
    0x801601300300c0c0d18102c52a000d4911059540340180000c10040e41001c901005209038001d08203002002481444421604810f610035040b81200240030035103031190008002900542c0c00a1030741e46055000741e46011192400c181c10800380910b041e000800020030348094808081e004140341da596032648004242200e40940804900c04000861004402c004a00d048095000340001520358a040e41d00c0c039141d104080860080c0b510b84030210b442580515000880c00040d07400100e4010b04142c54401c40b17925082c030400c20340c80c0c42d58030441d09100b0f9810032400d900182c03500b46041d0001900c0310085100c0e003805692101100d6220755600e80c07020014552010024000143c2820040d81d5500c0c14150840828940a01c0b2809441c0ca5014000420300201c1c00114aa007000094402b9402c4030b00800103126081c480b640906c0c0004112903041d00103517480320800c50100c03030703030301e085da02440401c0c0c042c0340c41004002050b40f40802200c0c3c859006075409a981d00501d2811282e80300c145041c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 121856339 1250 121855089 121855147
    0x31305010507030501060908010603020607020906040e0708070503011b0c060c0e0307180e060f160903080d0203040615080304050904020a03020901080a0b0615160f021005040e0901091106 82
    0x20002e001d038041d8092070581e851507440303000300350300c1d5842c06007221600d0001943c03250040c0b00b424014905500c905a110002400100d00d03048041c01207403800d180c0780c01c40314045d0403840d8103201c40d003024401e281070b41650124054580040c0940504420208134024110b50744807030a20019034003426001d10075120280c01c41d8030a41e03864802d1075550000c0f005414100b400d141031500d4444000406902031a40348051581075203813a42500c42d035045100c42d440c10b02c00a0b42000000c10300c2c0c007010b4408140c0c5418096030301d190529040c01151104610301400702c4903003000b803043d035400005850645109540c9840141c64500002d014010a40e200a502890500001c282c2030004100940e14038440d0313400c2c14413a03c2d14420860710645440312918000418013000c07494000074100604401d000f03502503038201071280c004c03400d410000903c5d000898000a01000058a01c1c50f4065000c49000000c01108903540d41c2c4001d00b2820070011842340300c0c00b01c2d400050201140701c44e000a000515 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 121857589 1250 121856339 121856341
    0x1050a1e0b03010f09180203030307051b011b03050f011406130906080304080d020c06090d060b090f1006050c03030708181006030b1e010b03070509030703063c020313050105 76
    0xc161450100c09000301d0403140c5c244020b00100404884652901b103500074055400c0d42d0765044111a01d03000710300075981d01c0d03000000e0880201d40038482d481e03240c440303202540010390440b000501618009070230030100300302c03403401040000d01c0c5001100600b00304481c038603510701c0302040e5031001c1144c5410000e907141c913080f00040c4503280040144110f9100e60252505080c0e403000590b110a0403089150b0000c0c02000300101500e40742080c00190f901c1140005100400d100c00700c0c0004400702d4603044100031007814040c1e110711200040e0014066883c14529106498150540740d000140540f018484860041241801c0c4443c50a86290503403003100c004066a95005024003041e202c20b8581c0e60303401c00454050070f03042080d450a00e40c2a9a0700002c1d900e4882c00240f0707544000c018108111041c04032902c03030381c2c003031192000850080d0300c042481429078003030399040c0948070800d0a03d05140c04400c08aa4184134035201d54040000c4010f88940d0340801201c20825100d4009002e54a448 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 121858839 1250 121857589 121857599
    0xc0204020c010b0a0f06082a090a0b030a1514010507060e070506030408030a060e06030d08150612011d0f16090306060602031801020d050d02030c0408160602120301050a1e0b0301 78
    0x1505c20081303c0c419515141c03247c4507070b209003400c00904420076141403400215413580000700d00c01842d0611b03010709440700700e40d41e03004000000d402c242c0b0b01514003522400d24241c41c1c5199030801c80a411090361a484a050103000640b0903c104500100b00684454649080d004103120010043c400500110741d00e00d00391400f00000d6004a40e6090003610b45040440c40131000c6098602c1010b0240003000c907580c030260309a4013900d0040021207400900a06c0004076120300b40a03012441c081c0c24a1803165060450003a040190304440f5003140000c0c0082280c1c1d0400c00313507101d81103d00000c3c0c1410740310900744101c41002d4543c10140415041400c0025500d600000034000b02d00d0311070350702442524070401280c49202550002c2c002071400c2c0040c4c013203000c2aa0003541c104014a440c0c03807520f80c0c1c4441c89401c010800700f8582120750400400c02c00c694042c0260300846d0200742c941d0b03141d903051000142c045000e600030241007203ea00d115201d07010041c02582c01410715851900d0302d9617566 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 121860089 1250 121858839 121858859
    0x608341701050a0504030f1116060512130f140111030408030708060f2202190503010503190b0f06040b130b0109091a10050d050108101103070c0204020c010b0a 70
    0x44a000c920540c0791200050301064144a0940030702d074142c2d103100c2c600003c0344040b20841a00d100e58a0680a500f17900744520503002d107504010010350302c64a840b110901d98600c0b41d0310009190300f407140d16a245510005003e10020031425030700040c000b26115804100c503005040c0220303100e05a01c400018001400710742806103205403000e6640c00c14a41c0c0b0141840501c0c03003000d034a40c0c0c1010422044907040710000e450b5440510fa210001414461141010042c030041369006c180400c00c0000180300c582428881d41c030305802d1455031440300451f03030394543d00450402010302000d80043c0010401c90380c3d0310b07080380210300401460382074a01c0d48803400f000101341c011110703404240c3c0360400188190250080d0754030004000c070051101070050080c010790080200c80d00080200401c9860004019442406d01800c7c09000900381081103020400403a0000801c01d11444820f00400044e980d000e100709074080d50584002d070301d6401614441d40540380186103c0d9106010030000714103c001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 121861339 1250 121860089 121860119
    0x908031e1903020702040e030705100f0b09010b0703090b07080a0804080708030a0c030f0c021c0c0203031309060909050c01030b010509030d2105010f03080f0426070603060834 77
    0x2200e00f0460002000d040c180d580c421520000e0540c1c000c01d00303051021585500141810030f23340301c042140b80280e0000f420040e400d812030805803402003001d2051580c0500b041d0003520780840250704c1d260705074a602401c0d001e1a103400d000c219a141c000b908111032482640e404da98804005612410400220000703851002c1c1d002c1d00203032928100d443c158095005c1c00201e902150040d000884400d010b14842c07504a02030031081c01800ca030703030f100143c40400007080c4020f00104030f01d50701c500b030544c1c070780a0b180d80c0e50100d9280d509254602e00895400b140310b40e0303120b0f4242000100c2d61410300041e00d46007d880803059041c00703908660f80001760460641e40440c02c1c60030840118a01d02440034046400078054140e503100d1038030080c030020390300a00919450b001c2843c424103203940e41c1541f010705e05800005103146c01c4500c10707400c0300d001d003000a4030150500f41420701c005800e01990594419070b290510180c4034a81da0364910910205005282c06220711141030348694a4001c40750711460 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 121862589 1250 121861339 121861343
    0x1006030f03021b0607110423090106050a050901060807030f0e030405030705150301061413060e0906040606020c101103070503090a0f03050d110f0d0806010f0908031e19030207 77
    0x503801ca5030840f900001c2c0540050303100902d5603042004540b41c5180f500d074680c030400d4205a075110785d0382510952000c00140e81c0d00d09130034541d807480e000f40c00c1c40c00d48501d540182e001d10000d4a052025603503a66146042d55242e240c081156a1009011000b41c884961075501d65807614261011921011008000b650300680c125084079507900c0903c01071840410140c220b414090005001040c81500e0880d58040f400e1062800e00012407005110703101076911a0000c03d001641000c000e04014040951148049400700142071a01d080603441d00140d01c6094816903c041440081c54010189200c000050504681d01c5500301d280165580d4044c0c0c9000703201e204501c00004405110300b0940050307d40c020003810001c40d03007885c00c1d42c2152041c03051104500503190000b071000d07010803640c11001515684c000c6281011000501410340c81d10017281008a0403400703204a25000048801c0c1c1c0c40c0c0c90038440c03800d0300c98031440c0981d030181c00c0c3d800000850401300d0701d4181d036144d006808198 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 121863839 1250 121862589 121862593
    0x170a02040614030907030b0408130f0501030c0305040c03110d06020d0c030e1c032a0305010303081614030a09080c0105060414160305060a0b0a0c05150702030d0e1006030f0302 77
    0x1c01010008000b40c00212005081c03540705190505c0040c118880e0b607a0001e100d24001341c01c0881400c440b0030040c1403078103d003020341080d800c204859a1f050103090055545810304111303600700703078032444248076140c0405071980110030401450350301c854a00c100c0c21030300901c0c2151a20300b52131144001d40401d82811002a0030a24082c0500d54040313100004d100002200140300d400b602410b5001d405d0705d071660b0303c0001e60060300209000c28400f24078110072582d60000b17017540c11487c0103040d59002400b500144403040404091413500701118900c061010301e01d80352280e413091050f1020700780040b8000c224150109035428ad035141504014050038048505000d841d00e83c020b6900c88042c102c0e03c903041000700c1e4034178100d028040da000a8000801038010108551202601d188940c031001c4003000280c5480b07003a40c280031050101813a00061004001d0342d500301060000e46d207000c0c40b00111903031981c0340c040001c00c138030800148030301c82c0b0342a000f030200503900d081a040c84c90520400b68054 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 121865089 1250 121863839 121863857
    0x703020f010501050f091b04030204140601020d030605060f070611070b090708010c0806010e0f0a08100b2e09050901260609060a090f020301181415040210170a020406 73
    0x136107024110143c84100103020300c002640d03151420f0003000045c03801901c6c03042c000c010100c0940c031a8020070102600d41d05e2030251030304000e800241340c151051032240c100340c1380c09010b00a6035100030460304145040e4038402d40784c10003410100c000b00080d1420070685807000031804104006000c1e600e1294600d0400d4541850791103040c40c1c20385080c8000c1a002404200c0013aa00d036010b014907404902c000b0785900d48000301314000c034031585000d41103400c040c2d00852041c0c0765030540c2d01503040009420351b2985404001e000b10394040501c2011260071740c014a010901080d449010031500070b150080014400e565103d10070722484641c181c1c9600d5090312401076400001002800d6409070b404800103201c0c95071454107000c010901d2510841301c058400450502507a424001c0925441c2045564000e142c03440c586002e1200f1455101d04954001c00501072468102c684201c0e805501541d22140c009071840b0110b4203031100c6100802e102d18000301740141c00348154060001d40b003444e2200050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 121866339 1250 121865089 121865099
    0x106050310051005042705061501030905030a14070b0c04050108130309050913050f061608040c060507020f04020703030e0d2a0318060201020924160201020f030703020f010501 77
    0x2c1e03a00440f00250007440d603100400041c01d00da401800e000340e5607211480a6500c40c1300c0f0b0782c0038000e00d4100f5102a40624207018a051a9900350703a0245024242004880101d9460701d8483c002e103203545c0207006000210b01000c010340d00c21604202c2e80000300400c24900010854015082401050300013407404000501000780700700d20101c1507405803034901100d40740800700900f11500800148103d42c4252607900040c504120b4010380c0404031015001a10348251481c1c8245407401c403602c2000328040520010488400d500b0050703d5003031505980d40d520a00101d2001c03402c02204c01d0308a440040c5180526030f259004c518070781c0d0990709684100c9000e02040b40d100c40c0003080d00c40d158404454582d140228090968150351281c181414440c0e80130211201401041d8007210150350002040f0500e0315008d4207000e0300031941c4065080195040510401c5030103840100c1e805c03078040d0b07200b41d001d580c000c10155560040300750484e80d881c90189002500c41141d80100990f9608110010813 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 121867589 1250 121866339 121866341
    0x801060f0e0d0b0402060f180f0102150703020304051507180b2104060608011404060e010c0f0f030e100e010e06062d03060403110606150d0e030d0e0106050310 70
    0x5501c0c2009001c102c40440c01d48034203852000160040b03134824000c001d41358a40d82c070000a8090f020841002d04c4100204031f00b03003c034243c4400d010038111340000d5600310303120307100c0315003580c00c0213040c9001a20384c0d65502c2d001c2d140175030010030340c1285e641c81030800840030303404094401c0800d190b803034032586144d0b2808054498040c0086101100c02d440e0b007000d03111103c0305807031640940281c03c0030a0b842e41d241c00444c21508a4030451402260300c000b04401d01000b4051044c151008400821404c88180401807014982000644c100500c00329055001c038425008000c6078080e840c150344000941c2e04c410002017826814506131542044200b006c3c074100452200e1007420058403100d9904c02d42040c5800c3c0f140c03003c00c8181e007003541d40c4001426440810203140300e24866151a041013402500c980d2130b00314010b01e464420f0254640303405080c50214180c403414903140c6000304644003200e090900398007582c036050000d1881c0070132400000c081500440200c0e902030741510741a082d44c0103150 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 121868839 1250 121867589 121867607
    0x40e070806220f08070519051f020d05070e010905031c0305040c0f0303180504050601020a03050d0605060706061505030127020f0a031a0105161b0b0a0801060f 70
    0x3032119006500012011202c0c0c1e2000c480881c0481030101c41000c039699110584440c1e031505031042c0b1030124041c410050100164814404e1490422a00c14100e94800c0d503540480211042011450084080c2d03040d010f4058a29003c2070400030710091820a00041031000440d0004c1d00141e8014000102420045070550200d010b0301e0302e0412a0380d0707940003074024100217001117a118007100400544045401d5901001e54820f40d140f4030710045a83c107200901d1506d8101c103201c0c501c3d20048c003003540e8000030911501641030030310703036141c52612507180000e140990100d5080080002c0070010809654400d005440700c00e007250124154000d403c66041c0424010f4558003200c07130b040300303203c00303051034a07000c003000042c0b40503103040345940c04d40030b4035001083c104020a440d0303259500300c0d07890300c0784503040c08400f841c0c10781c203100c0740c7c200782c0d01080c00150028004a900030950030382d02c2c01c00d002e50809080444150b40e650b4081c440010841d02007440760380c00089000e412101e400b4490720041c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 121870089 1250 121868839 121868849
    0x121a010e06040f15090b0f030423030306090601090503010c1e0306050901090e120a170c0a0507031107030c0605040611190303020921030c100203040f120905040203010f05040e07 78
    0x400c0c036003022039004c04909483c0d00d4109000901c1701c009064030b401c03001001c51442e26101640c0b6070510b46070140c415204c40c0d110340020000c00280c0c036214900002038a0780104211000c41c4141c0782d82006803601c075aa604565015401c00c103075001050b401041d00c400480c4201450714101c3c0b0f0950007201102e24a000d085e9000d5400b000411076007045801061841000100b075403603800d141c44003001e0a82c0a81d0003440460f0f001c484518035640743c1030000da840740309540a50f22b00382a001c8018030511035050000c0601400000c01c140c0603a080201102071544200304240094a4460140682d0468401c03400081d102444410403044041a1318131503900d0408006403407840bc1e6402d4000c1d40140c0b007413540000205417802c03e50310a1204d00508142e0403000b0317507540d03414003610a04100c200749103150014010800c0c0400613462000750703045140c0100100039218084e54040b01c0c40300d40c590009900c140048004204000c003004c441007151000c036010000707640d0900c049915403005100e2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 121871339 1250 121870089 121870109
    0x1b2102030903120f040b370903110610061404030b0103030203120a0c0c03110102090907030c0210200a1101020a09090506010804020d060e030c0a0605070e0a080a020f01121a010e0604 80
    0x40398080806201640e1001f007405a01c80c0c0301e0b00b400b0341c240b00c100007024941040300d4403004442c044c990040884040b5524800103000790740707020b80801200b41d161340b003002d040111401c41440011480c500340c0307000c0c59000da01a4400c0d40e41e0b0900954a4000c02810740c07800c040302022804008030351249005000140e1100c1002c21039a4400751640214003201071800d5400308084540da0fa203c0e40090304c212581c4c1c4000880072070692000b45812034400c1d4151041c0c0c40d05100c110062841c0303140d24048121100f0b00c2c3d50390900818219a81c90440100c0340d506d40c00825090ac201e904506080c0039140495400c2001c1d0755124011107410310191006504000e40c1c400c0880403500c02d4100c07010a400c64400c80745800e500b001002c4c0350841c56003065400071303074480c14170030300030b07441502d580440304112003d80103103007440c0e41c541c1c40d040c80190091042100418004099000304900c820340d900001c4100301c80042242000c8000c1c0000c560140003449140d0469140d25100090b1801d403107046031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 121872589 1250 121871339 121871341
    0xb0f0105101211041d090105070203040501090302060d0b0d03170a0203060f041a0307060306030606090501051f0c020d050a03030b0405070512040c03050604241b2102030903120f040b 80
    0x40c2d14000c0c40c40314450080c15500300300100d00350200741c280d000b0b142d0f11011481e071030745491403426084543c0540750b00215041080100126039020028806594048420710f50b00c01640c20b1544c0203080807042c1d15044002030360200145500144201c038800e00c61041e08407a65200f41c6000102c0c8000c80718142d00492a401d060a0b40c10640e0051600d2180c69a200303c22040c0f29000038a0000d20742c2c810000a919568140100b00c120b002e500024407a14006100c0340d410140001d2401450800107003806451803003c1a082e403103109160030307c513005420080714448030306089031108100074066010a0a040310103c407400e180c030074a40b1441d200d6031014240203000321816900070010304140d0701c021201c85c001c004a101171000a0056100d40c603ca140c0820350b8100510b203041d4602510071241ca0091100700060700383c628903d8441e100c0c50301d80740e9540e81c111100c0a0034403600301c82e10348620110401c02100000802401406010501012241da40e00821500c6032000c50780180100c034900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 121873839 1250 121872589 121872617
    0x30f010e1302030f0c0406051f080a06051e030105072111070b070203071703010501050414130c120f0902130b12011505012007060806030a05010501030b0f010510 71
    0xe400c540c1c0080c030904011549000e950000ba141298111445207181c0102c111290f143c5054400c8600030300c0c00740c9902c0d601010154a0081005448100710280524480007422154040c0d1105000c1c20004180074140c800071401030002c3e1030b0b02060f4032b000e90718201c040380c5458085c01c0c0c880c0b81d800c3c0305c00c00c040705244501c0c124405481480807010480ca01408400700103000c1ca1041b51241c1c41a500468881c011401d02c03203880055400044900e6030104018070159031321001f01c40c16100200902003080c9400008180c0c0130400c2807065802074035101940341120350020300c3c034901c50000c0c60180244204c0251000c1100c02c08480254084c1200b183d890740e0707140f00c0d009a15a1040141800300804d60603500302c0c03d40702d00803003054040c10004401d004540e00042c501b000c000110307109444203c506031000b030f1398543d130f40200000c0c0182d03540061220b590800204000c658041c0080c001940c0d280381840e407032042560001d2800e0503000002c212130410141d103000d990000d07a62a403000d801c00e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 121875089 1250 121873839 121873859
    0x21305010e030102071e170406020a02041802030f0f0606011b022b050307030201050106050c191103070602060a060503010c02030a030506040b04050f09011b090611070e0f150105030f01 81
    0x106881e10382554080c80148045011a064151500c04401019000500c2468034502c805501c1c05d44505240e8180400d0000650000710450ba180c1e06941c00079050840c69020300c038181040c80300a60511907e15400380015021402c011803a801c030f0111185a29420015a8841d01c620500c1048030358460b00c440141c90030b1031040b5080e0709034180b6090110411201c8000401c000d130710940340c179400010f0301e00030594240b040c94018542031502da4140311039840c02b181c807803401d1500005580745181500c130511400f42c003c40340280d0001c040790221580d490000e51681001c85d041d0300f4480c5003400c0000c2509040c00f0b15041c415447c2e01030740c035001c04510150020314001d0582900141d6036000381185484900c2114010547d4050003070300c81c900100c3c81030a44215403100b5400d01003850714040c5840e0001c41810503141e85003041d41c440c60308041c1e0b151400d0503952080c0e403c81c4c5c0c600240300150340343c1a900e601a840506044611003248001507500c2d10007030320660404c40400d4010030421100d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 121876339 1250 121875089 121875107
    0xb010e041803140c01020301061809020403150b1201020309070801050903040302211c050910210f0207020604091508010204031a040609050d090f05120c0603040507090501030c0e0a02130501 83
    0x10f025100c3c1e090100512010782281c0090308200041682680c40070151083c40c66000010300000005510b00750865941d54002c0001c010380a80e89500c807106a030056640e4610b11558a0b200d0000f151a441e00d000740d183d84055520400780f0b607518000110711000e4010044030240c0390007508642d285c2c8040062001040310f03004040b142400748c41208d65800b880300003681312581096440c9500c610440c0100711905011000c52030501c03641c807201d140400741000c0c82200c0034042c0742c00050104d2502d41940068407840343c0081d40b201e80001c000c05d1031000c5030310200000760280c072106892500d802c4898200e201c1c9010150000807080e40b9106400a6041415130140c030409021964070b8107582c0c1c803840c01d0090201240441d04580003402100c54200c1080e00804040f2918000c0d440810b0895450304250002d450144000000050501c0030130000c010007420b500c5000c010560f0b40e41890040d00c80940207000d130705074130f03880841c800c011580291040ea464941381e1084051800c0019035040368 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 121877589 1250 121876339 121876367
    0x60302031507140f070b07020a050a0323040806010f3003110102070c090c050708031b091005030103030f05041401080613060e06040e0d021e031c0b010e041803 70
    0x80724244602501c543c003014003405804601ca00c0e44a00c0c81d445c0c41440c04078003c01400455100d5107801000c101e0000e0400155505030034524840069401081038100c1154560381c90a10700040c0003601c80b000081e814100e9072a010a0a0300a40382c3c40031071002c400002e0f0352030380000740030442240703194805001444030340b003030800c640000c0c01005150f00b660080341d410f46103429940360800100c22207005000da00203042ca07007507107000130990b00c0345034501010301600301d200e03070a00483c2ca0041c5e00004a50a03044c005040d040b00511008000300300754800d000c2240000c052110700d0ba241c030700441c00c1d182a035001c40020042900f80303a00441d4125030050031164010380f10400c400c00c52000380700380c40150160401340c030f485240120600094496070390b00500e481d44040c08001503c0d80c0441c032416181c000342c1c1140c26610048807000c1c514054114850180780308040414034001c8a035000c1c80024200703072a540d901c4080803081004a4464000300c10300d4480d1314100d240000d104800c2040110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 121878839 1250 121877589 121877597
    0x613020906071a060f030c01090b09060c070e010303020111040b041403011e060302150421030c0b07030b09100f060f09030c120b150303070807060e0a0b06040b04060302031507 77
    0x1002a440e00f92800d05900348004039103403800144007443c1031100c42d81c3d25403107007940101b0744000c071040002e00b0003545211754009180003044103c00c0d5a9107008646507800c40300100d80300e068580c0d11024644101b844110003540c64031809040c0903100c04140c5003161180480681842d18001c01003841d41c1c242d0031000e6040d544d50113000146c80d0042e81c40b03003405002c244001446c50035841030000c801807800c000c44050f8810322040204e000e0100030800340c0303404107040e000b20110707e14054910001501004109003c09000c21401550641c06081190300c120b80300c0d9000e840f00c80c1c0940442d440d031300070308076140724a820074480c1b680110180c1e441250f0610703100508035502d844d142013120313843d041004410b46050380d017018061102d082a82120781100c0c540003c07110203000035900e20442600800c40f103004580c442c14403400350310404003070380702e0403e440400d40d1500c0c1501c03144100301d4106200f07910300080035215041520540d41602c0d4060b00918490390700790000361510310000c280310204 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 121880089 1250 121878839 121878847
    0x16150f08060409060e010204080c0315161101020301090b0a0b16020613120c05030d0203180d0c0305010f050610030603021c1704030302010209130e060f100801020a0504090507080613020906 83
    0x40d84901c565010b1703500080c0010f0701c5d84d00709141d00341018181c81c0c030280303c2e07444203c00f030002c030070010951900524072038072103c480c045280b0155003501c00c442c10703190a944080300004007030390290040c41f0002011a00c8a41994590001100c54054121013a03030780156524030744014208640107251100760014202c0d042a40e03408601010361031588119002c0c10510010041800e04010b4180307040d0140c006507042000b9a80040ca41000c01b41d02035104010022450003442030081c14000070715000f90090001084d005810000340c0401d4505a02034a040304040345054802e20500f010740398000c00050407240d401210f1091000e4040d426500010700c0780780b0b10b120304440001031008603c02d40000d43c8480c201030820902e591140d205140303907418032300c90102013800404d04c154091760748540d8103001d454140b415030480c48160808000c5610029080710303103a4000d0007400403a181108280015a01c0030f0341129102404d4481d6a00706940801400c1400d0403038000d09800f031405007884d410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 121881339 1250 121880089 121880093
    0x813060c09090207110901090e030d0906110c0d090605030702211201030302100e070303050406031a031f11040b040501141c0203040213060302130e01060e01030516150f08060409 78
    0x884c2d01a45003100c5069103507101c06006e0501109140c01000070010030045080a5882d694482c8165540307100041c1d501c2031803108101069000302035000c03d505840341c5400c000490141d84004a0b1028000b2418442c4001380480c0b250040741d10400c020307409000710650142c480045043c0303c6040c000c6c078680902014400d54411482c0e14001e40c0258001d0a001e114440e2101c11520003080b00310380d5801c8001d003400880d412400719011110070345000035010f02a2800390b11908484031100e070b454025400403040008405050200c1991101d00410901307001040f4400039100e6841a20151403085c403080000e0342c007400c01c441480d018221514501b0342e070000b40511182452082c4220a5030120600040d81007800940c040000c002204200c01c07030540d00019500f28900e00043c0e4401d4072801c50841c03085083d0040c000801b10003030451078a5031203250458650341581c150145d2030fa010303003000403800385e0381c01c048044900c1c1d51584284401c3d019012501c0340402803030755070840c0d164110140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 121882589 1250 121881339 121881341
    0xb12030a03152418050f09150409061b020105150607050a0b09010f23060405090102040b07050a02010809060f012907060b0301150e0118060b0720010813060c0909 71
    0x440d601c00b0f56120340364180c4918054a40b2950f0200c64004a075150b00c2440b1a489001030384d0643d042c21101000956900d10843c8000f42260003040e81050603c4203100030802250055000514003010051035600c07204030803422200100e400c4086502c91211180032424541c006095160040041c1c07240c0c0502c079102c07047c820a00b610801110384d52003031241845609031140704010a41d40101c00314078001c0013020601c59a0103404a03100303540c0c64000c180c0c01c800950494004001516450b5100e215504040d40c4861001e07005901290035540024040d000100741c66104003003040f651462a401c081003002d04510311107840e01c40d90451a0032125051f0301760041c0203403034030651021035031580b0001070500b95441020400d140c0c0c2c40c01d10040c08903454a04007181034a9002c40e40401e5110050307220005030403a0380c08a0740110300010b8220500a0305690b0908001c1c04207403809100380f00c080116201803041301c1c1040c0525801e540345000881c0c54220540341e2405141c6210695100c0120304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 121883839 1250 121882589 121882619
    0xf0203010b10020601150c051e1903032c030f0904200903010615020a08070c030b01030b0f010f0b09090603010605030607020a05010b12030f0d0f180203010b12030a0315 74
    0x10b0141c1e0208004001d20002c0e00b01100e110003440c54511501640c0340c0c0c80300ea4492038000100010324a005e00107251540420900a00e0911080c0a441040d41800c01500400014000042d000c05d01048000c045401980880c2140210b0340114a00006c2a000006541114140c99401902c555401c100780d0740320107400c140584204005036031001d500041500b1284a41d122449142d9844500036406401140a84010740c04c03402d140c2d924142803604030f100b035070b041c0c10003401c400c140d4002006008180d081184205503070301a909041c3d80b64081100140214032564805170003c120013840c80c181940300b0b80c0c000030040c0021902c00d841c1d10000b410302600311200d5005a0103000748506000090084000703224080c3c6620315202d02409841da10b030f10031810310f061000d10018007101000b030581d1100aa00c44100410825000c1e00b803136401c10051000c106070300c00e40c200145006e42e40b600c084600169180301d0010341c60a1201320090b0007070122840381c3c51111041c03400020b00c04c003c0030300368 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 121885089 1250 121883839 121883869
    0x7030c03091d150d020906010c080d14090d0507050304030206070501020d0509030a030c170606030c120103050d2a060b040204030206070b01031211060f130f12080604020702030a0f0203010b 83
    0xe00e090f0b00d041111180040d80b0030345403a202c0e01d090800403001da114124003980001c000c2c07074103944000301030030b2000c15446503a40f40c0515510305692141c488941c010720501070000e01042da2402e0b0060442144e01d03001e400000f030f1658104000400040ca0148000c1070890710450000d03040c044100301403400c0341d40c12500f038080d80d0000a1407102c81c0740d00d441b0300300c3d40b1061402d02179958a2a00a082c58001c0018035080c05100000007081c0080d010f6020340d020512403085090466859142060320788404109110128000140c50703004003844c0c14003040da0601c40a1901012600c0b61180c1025208074003040e508140d0801011016898601c020026580244510b054952451805103c1342012044140400003496041c551183d40442c5058200c41c02480a9025444500102194513031241c0c000302030014281c1010b00708210071000103084081030300d42030310f5030f5200c0c4144010f0b4070401030300a605401c079081c0000000c0c3e01c02c0100880303a001400000e07070601c0810102d01e090600300b000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 121886339 1250 121885089 121885139
    0x10303211806051005030d02070b03040c080d050a031d030304030c02060c15251b03031b030c0f0e03070302040e010f1404120216120f15020d0b031207030c0309 70
    0x10000c1035040841e4583c01000c1c00c0e0014021010f42100084d294075490142c20640ac17000000303e0107100c07540b4540d90181c40e0301d00695042c00144400a8250b0388083d040c0008241005960284d041c9410f00a000700e0392100080c40c43c2d5900c3d03980480e410070040718201d9010000380494030b000d200401c4041400382044170244070030b0030403d17030083d404000702001c0c11040f004007440e008661b0344000b1942500c4152001d41e6410011882e0130307009403076000720304129a1a040e005400341e5a15401c00301003105507848042d000c031400001100c1020121020a030141d201420400050900d54401c1c0a5100c41400000d10760794602484401e480740c691240c19103940e12001e0109000c425100200245c100340000c003072440e01e040c0c221542c2040b5120b07128203540991003090503c032061030019480c030343c00800c102869041156003c001d410007245a01c0443c48c00044209034200042c00c0f9041c02c88100d00c07039081002c5a5403c40b1011600e07e8100c0c100481010002001030f1280181103141851141c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 121887589 1250 121886339 121886341
    0x80a170c07140f12030a020f0a2001200c070902040b070201020709090b060607050a0204090311250e070203070f0302010f050c07020a141203031e0105030601030321180605 75
    0xd01d104072102280842d40d0035040000003c842080004e25100c940d55803140141c5c603541e03240307130b400300900482d15030080390f100001e0200c03907403540b000c0744040d036680c2080725030501c54084250900700c8041c403840d9000505a004610039800c07080c0702070a8a0140c030022102c020781c540c50343c241a60010780c0030035204200851044d0441da0180f0041010340210442040801c006442c1c011600d64040c1210f07005003400030b25141404000d01c4150103e40e0058414440080107140041044a492a42803401e02400030119881460480664945000c1504c1502818200085131001d818040d05071000d62008001c818005000d8200c0e00600c14041e4000041d42c020303580240d4281c8200030500c019a000820141c00141d450103024025503c1d88038114545441d950701203840d074508100303c280180f01c04000c2280300c00c60310340702c02c060320030300400a24140d84c1d49080c581e03030301e8084c0001004991020391075003460043c5090b104108411040105405020403c0c00c0850318200c001580d009490700 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 121888839 1250 121887589 121887593
    0x2090c090a1205060f0702060c0729010302030d020c0108061c0f06020a020c0603011514090607081b03030f040b0402150d0c020705030c01052b020a090303030c02010501030b04080a170c07 82
    0x1000045d48004082450085450f280c00000c4d11080010001910113401080d610700b48454000c080c00d0148801100800d80410a02c07850b007500000d00c801c82c46407295042c40b6605900c00302d61b2001021041c2c581000300d480306030403c111440000d00420801d240c2005035400b0a01c88641c0d0069180200c038010798680c107910f002410440303039001a0780205020030042042e0050400d0722240020186014517140d01c1407407a5042ca031003100c1c0003640c44400800c03580e0910046800400b0592034803c00c2840d010080b07040e0035183d010840390298038504800004001c1503669061039441407004007078034001ea200300009140e031b8101c901c3d030480c440c2d075941010413941e804000d00e070003810089004240314000880002d015106003e00d110701c1040c03002d100c1d600704020780d000003103103410298199181d868103100104960310510007500040d04008526120900601c03070030b8181c980101c1050001e9443d81c45120480d840102d4040030011150055450f80048200c1c80e07001c0e50700c4010742030762a2624 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 121890089 1250 121888839 121888843
    0xb0904030c031b0f0204242606060a0509070909110406081503060c0904020d0f050f07030506100c030e03070f080709020c030d1d0303040302031e0909010302090c090a1205 75
    0xf60000043e044403491080b008100180001141d07242d049902007204441c0d240c0700c4a00001e910800401000c14902c082280f280d03d560010807090116200303140307006404c80c69039032408169486904020402c80030702050802c07842240d0b225140781040c80580382d840020380215180d40400402100c400705051029a2340007004a8201405101c000c2154680d040003076224080036020400c2400c00046c44038180d291038050310404c54a840041103520707070400395007001c1c010403650140050354100c0001d03880350191040314050180900400c4610780d0b400d0041d02e140c4030001090382404003510991a150f80d080005a020700544690855a9450f00000c64a00182a0007070111140140600c8000900010944411140090f80826080c26002011240000c20038041e000c80c00b0000400040c190000024901c01c0e00040102100c1c0d2580e1000c000c15010302d9800301e82c8400041c004002514041040075041500d00b6155481e003004640040c1c0d50504a5004880034005010b0510a0040c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 121891339 1250 121890089 121890107
    0x30f04061d041e050702151008010e0d090605030c04030213060503060622050c04080601031202060709061209081c0e0105130317100b03070305060a090c1d040b0904030c03 75
    0x2007035a06205003082401d505000750f004030700400400f955140000c0b2007074801c0003054140444504840814201803084000031410303402024151340c00e21b41d030020081c0d0300180360500200381e076841c1c202030f90406000b15110341c405450300d0000042400b02201683c0c1c1c01e00b01e1141490b00d0703280000e10b0340c07038103042c03505184005018511400d00c9070503606034800c0b0940c01c01d00d80c004029001405941d0050482c0c0b90380203981140d48644a01c40002c0204100d40d18182101a003075003c542e02e40d6100c179812600c003591801004001011500e07a07204085541c0c12484515100741d003d0f50400c8041000340c03a480480381040302d81991648000f141021003032060036086041184100c482051a8401600f08118008000d0120407000001141102810900000b4044da0400d036650f07414043c80040c050300040e103000d4800e02150000180e0300003103200b907207030021071925a82c441e80103101c4816800341c2900542d0b5080703510b405402c800b6655030b004840c46188242c03142c41201d525420006c0011034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 121892589 1250 121891339 121891397
    0x20f0c0609012903010905010e251203030209030f0f010c0e0f0a030201051602060301090b030613030e13020f0301080d08090708060a02030702030702090403090911040b070206090102030f0406 84
    0x49040f0720110803584184110021910001c1140d1078508690b002c240100071518000d850343d4602000d4419846022602000070508c01d03c1550144211304e080c1c0000020034410b84512544112042000a021303801901760448000c0c1030341c840c00c88401200e403c041a000d030061481e5560343c041198a07810119804150f1002d90760306101d00b0110002c24102225400302905102c8046400da0004207403c40780704c0c0303099000d0001501d0356594020440070300102280b035071081c001c940004d0b050080c11814040c000e50581d0f12070518421003c240b02003c05e035400c00301c0015400300111584010540000c600030842c450003442da140a5000041801c00080c28900294102d0402044410f00025080e42c010414400040c0d5076100c03540c040c1d00d03501c900d1000035000b1500c0401c1100381764208400f83c044131007000b001d11241d400c00c0d0300400148240e0040700080e41e800c0c4286000360402d2805000a070006004680c94441030300d031810a147c01c954808400076131100480100c000f50300498413841030b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 121893839 1250 121892589 121892591
    0x60503010b070f050709091104050c0307020a0b06011101060b0c0111070c06050f09031c080c121302060c032d03040f0318170303180a050a0b0712020f0c060901 70
    0xd4100816a40c0900c180b480c003034401e0220502e040d0912205001c6031006060402c01041008804d00d400000d13101c01c01e8909118904d080b000881e403411407421a0700c5140302d82e0281101040d503070b5840c0e82c0c0000241401d070402600180842c0d00749002d00c0740c0c20150503042301c2c854491030020241401d6070000703080d085050700c05001141c0010925001181a582c0c2800c0142d2600f01d03420464015000303401d101a4903229801e001c002d1402541003a1030a40155610400140d81c0c4940040c294401d031005420705400140c009404403c2c210408101d0602c0100300c9490b1032500800b0600e19040014504c2c11610400414400404080c02c04080300765408440d0381185015241d13140c0c0c6c1a08484064180007114021807070801041e8078000161204414105241491441495a0b40c200300c820690009a058074004910f0b8000b03404103282c1d500030010305074440030f903a0350000490040d000b203003403200040580700350f01d040380050b00b11640301c4080396032a060321014413440c0260141075442c4507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 121895089 1250 121893839 121893841
    0x114030712081c060303030504050105010608090a0602090609040501061736010b0901080304030c0b07020a05102c030d08010501050301091e051305061602100b031903090f060503 78
    0x19100389610010040c0c200781c040303807142e2003041414800f8402c00196500140380413800720070180c25511050080d80108001c00c0b6907030300c0d06805e8801c501c0c1501c1550036070b8001080e010010f8126002088100310142000382400901400326059680c2138000e040403451500e520309104108840030359011280841141c000396846081800c0b80b51a241c1400d0104884108519008001d4200c440a100e025000c40444c0da91000987c0d125000b0780411615062010f900140c2c80508006403142503800804080310f940c0343c40304000c44040351401c40c1d400d2010162561203014042e0704d08140c880410040d5a03200b91801c02010f0410102035449004c0c044003900500503640d1007815281550704000001030030500c00c3c0c07104d0500d19400346c00d0449070360401c020409510701100c2e10145981c8194112036580c0c50340701116010044100c0d10000503400001c640084031015004200340c44c001034291400800300c01c59074a03102062880982c040303144c030f200402545100701c56440046c0074621313216043d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 121896339 1250 121895089 121895099
    0xa2a050301060f020a14010606090f030b01060302070c03050d03020a0e0316060e041515090b19050d1103070c03020c01020a020f1207080607020c19060e090703110d0501140307 77
    0x250006000d11403c0120400e80e004405000300310741803600c5e4000c83c80ca04c01040115403e8081c00040c000c180001c1d5181100050170034101e071200003941d90001c1500d10310307820000110001d400a6400359194042c440340003000c50801c0c8074481d0b400500b81e071b0140c2e031041c102c4000741642601c1880c03240250300200201c6c0d4100c00c078034a01400da5200785000e0b40c3c43d43e880400100039200c030a000c051000440440094907010001a8425503d0707291144401e01ea5925001c03003140c01199101d444030b0b15401001c9020620400042800d042440d60010300b802002404640c3d5030402c54070f10002c24ac109001f0414190108503800083e40248020026a109903000c2036041840c500b025014101a40c040f1031410000d01041000d0114502203901d1490b00b42e00007942e841d2403038035040c02000c0010713180c9a00401d100c5041c0c1544e80c2030311080b450941510a2140e120340c010040c1007055076030340c020900710700d0101c010b125944906c00042000d506115044900201402201e80300c0d6022030000c01c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 121897589 1250 121896339 121896347
    0x20c01231608040f03030c032c06070201020c061302031f05070806030601050a09110d0c08040c0812090d1401230108012307020a0f08040e090106052101060504050a2a 73
    0x14031aa140c40d01095520b02060154060000b200e03427101c2c5044d007200c80b038100903030302d050303003507000e0040310407140c4c03507203401c4010307801c03440b8010640c0a280c000c64001412a040000d100c840c4034805001c40e04151044c03204404411001c05041500680b00d0041c001a954405145500101e080300580f00c03d502d081c0006010408604c10440d5040e1280b0783e0348958041c2c68203880300c041c010b03c400e1088840d020002080c40200700d604807402c440140d00460b0294000a001d1505040c2e80d05003450300d120402082a14404094200c4042c405035031006440d110a0080c0e01c905000d0317403050380c0f003809010010440301d041600034a030075a01d40411400b40f0103111001c1e0304961401c40b4581119120300c1030072800c15410040180181c02c1c03059001c0104442d0500410450301150004070807500c1c2c2d00001c030700b621a5480f40c254064034040c44c01011944000310030540c0c0c0102d60000902c02d90307410204090301c901305d80745191306503910340722408184886000e1510440182e800038a124070306901030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 121898839 1250 121897589 121897613
    0x12081210050a1a07080c07030213020403240e0708070807170c061c0c020615190504020d0f0f0603022b1101051b0a050d090b0409020c0123160804 64
    0x41c0d0004109440f6501d00e0403050480311040e405c40f41c425580d1600c510030603910982da100880c058510807501520442180c800c0d0b40a50f0303880351540f0221800d01400000745060302c102c0c500700c03980d24204251003003000c00204006008010141c501c031850401da440c1403d80941c00b1005a60110040760000c040c042140094400200d60781d41e103412840c8101c44981140b11540101e203407810b04044003c039000550244105488002204451048802d1203c01c1c812070344110703103209a901d81401289025000b802500950b20400a0340121003164007060320b480341c20401d54103540f004e040c01503013044540071214a00024000c0f10800c0740041400c03454034040c601504480c2804d0700c0c815560301ca0403c131000a00000c603c00d00544030f40740b405481d08000321080ba120711a5201c2c03000118050004a8116040502080d0405117040c00341e201a51000d00700d1407041d5610004c5d42d261084051000e048105c0351003600b116894410f1262030700402c5210284144100c0c1802c101c0060303030100110b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 121900089 1250 121898839 121898849
    0x20303180703050304080723010f2111070611090604120303200d0f0519020304020a0f0609080c0108042015030c070b0f0403020c010807020712081210050a 68
    0xc400d2800e5603841801d00019820092450000144c0000c1c800c9002880d001507a00599130760050040042ca11680380500d100c04c00e001c561021042e4064070702503641402d800c0b0402d840d2417150b0071005025400c540204c1c007642c11001c070108140044c4205446450252910b41200030b24055542c000145540140d1044104c1403420a04501c1094400c0c0c001d440901400791103208081140003040e80d490300a15031052201d0701c0d001210184a403103000d00c034040c0211a462449c02d442031000c4001941c070041081e80c20001e120f00c00600c881903110044010000c1d40e0f103002056051031552810f014100020030f0400c10303441d00340800f2a500c1d9103001006036840051105100c05000810303001e18070f1f0300039044401804400c2001900c2180b00038603105204005030340b03c070360f0b4049212010070700c1940c0c0078006a110280c400101c0d4055034461360000343c4c90048640c002d5a9282240c0035030701941d001c030b030440b1012030f10040046013003034800e0300150940e00030020700c0d08101c0030403280322040c410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 121901339 1250 121900089 121900111
    0xc0c180112150203010e190938010602030a1101091208070e03060108030c01140c030103060b010c050f070329070305071107030b0906070c150218030f0604020a0f0303020303 76
    0xd100c082140340000d20b02403510712a800e40d102d603901e8140840042e030864460b001c110700d07584004032806451003404030701a801808a0244842c0e424042c2407408503402422030101081c2408814820641c4094020901580156a01c0c0e0b800c010041410100408100c0c541c1c2c1084000d4002075040e019019203440a4540710b10107688604046a02c14040784400740c060060348d0000c5002d9401200034050b031001000203000344e80c0c003400315110486045130303441000c0c442840140300041003500101045c52051500c0d9100c000c55850b41c0c1e003000030301400c10741603501c018020001c000b002c5021050200d40c01c103c0030041e2040b00020289088002c1c902010556524000303455140114107404d4030840540480d0790302600e03860034140302071080c1c0706c0403024841c03600025141ca104600000241e58813044480e400000001d0b0400a50403030704175401c04103400744070101c1c0d03078600b00410261042602c00410a42c245401840424402a008030b01039140ea0710050012940010459400c0407510340 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 121902589 1250 121901339 121901369
    0x4020901090914072006011701020c0601090501051801060c030e030f030c07080106050a261005040503071202010b010228020a0303050316030212040809040906060b0c0c1801 76
    0x10040341d03000c40c0390b00b19282442c80c001e089005031010300c441c14420105600c40ca103500140c41c02c10b26543c40042c081c0000340e81301c0801400f0614169603520b101c24010070002d030800c103c650002d82041d0003600a56a0565110010050380c0303000905600c1860050b0040021541010002030010f403c0e0304024090001140601079651020440c0d1100d2850300c5050340d440b0b420f6039940c2030310f4010074840d9224a6080c6000400d01d80b801504080c101c0b81401030141c1c1080400d10740d8000a4010f13490442907010348000000d0034525800340d5031240344035001544d070f00d501525214044810300f00c220001c580c5410001d5080e40d0b00014440000407070322840c0215420400c4101c0050a0444002500454040000070415410801447c094442d13160300028525800104a080b4001d0003011008a1420f80104010400d070000421031100f02420200d060345250701c400042c4e4003039520400e444500042d0110b1005070a120780c3c04030307000c01c0310004500b5603a4042c07480844010300a0840f0840210 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 121903839 1250 121902589 121902607
    0x2121206091305030d1406030105060a03120201020f041502060702150105040902032b08090a020306070e03030d0603081c1107140a3f0909110d0501030606061704050307020402 77
    0x4000b40314490b41c4801181d5884030b05122400181282d0b00c400311072500d905001c540e86140c1070150074401c07400034050030f020300d00c1c42c0c07076000d0003205540c111020355500300034510f00b55a0000040c0050700040345400341d6140f0460009240000c000c1802085401c80c1100c8a07290003404081411101c044501080c101b201b0f00009041406529001c985409042c03400c0800c420b12a20300c0c0441341c001d4480300080d685042e045070300e039501007d00a51580068002803c11805204040402c000180443c1c1c1016109821801294020f80041c1c5011602040c1140c420240304051048180414800d00030700851394480c40890241a038000c1000a26400094815104100512409401c00b6101e034030b424040c411103015403518110344a81c0320b0000301034404103296a5200c40c41150715514440c1d41392502030100c0090410000c00b00c03003100108201c3c61041254064180a58000c601c005119803070005c002c0c0090b51501c0810b10b41c03d00c20820400400e801106072542c00390155009030740c0310945 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 121905089 1250 121903839 121903861
    0xa09080105010321110307060c0309050307052505010504090207020301110301090b041b020c090921090f1005070b0a0908041401020c090603120c210a0212120609 71
    0x290002101036181500010601c000d600e228044000680c4011240c4241d038602201c00508840034245980c0c810010300d0001000c5a00219204074140b80000c2d9424460382c5090441d440b951040d1000c0d4040d014204001c828103904103038507038400043c0010180f40c45c001900c1401280b040004040e80419400d007952021b400800c83c2c80180d4220310350381d60316407002100070082d11501e54052840c00c41000d0040120303400000038920f060300200344501c00d030350401c03040503401400c3c40110300404403000e2030b4486407218040c818482a10958443c92120280301f0281c41c40000e03d84a0551a042144000d130000d048808041d0818145c40050341c961820034090250440b004107040c100290001c0c000410450508081e4000d9090355030f45012141004403800d01682d0b510b5164219101c01144240104000d1501414400070703902c82c54498818140350218030160341110070000505c0300d802035410f201a20b9076210400c81942007086043c10b40310003840c010801c1c6d0040c50b045020400391911 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 121906339 1250 121905089 121905107
    0x60a0c08060a0e31050106090c050702060304050705030f0a030e0a0e04140a050a03080a0b0d0b130314070c1703031603090503090901060f1403061c080d0e070321020705060a 76
    0x1110340d24498807080034a082d965134071801522694a00b01e0040741d00c0d1207900640c6a41c100710f98030a41080601d4080105a0740f000d802203400b0710910b040054961002d1001c4407802074180c2c050078600c80d16060107448a55404405c6100d403180482c00c0c004041c0b248003983d002034201408800782500385451618080e401e10015049104150600003015840038009104080e003007010300468a14005101410f588664014400118200044c140708111b4201c0b43c04140a460420184185103140b0724a580c006075090314180750310300b410311900f80180031666460240301e00552851400101c02c2d4120940142e55034205a142c0e03c9840c18002c040007640d002c2000148150101c3d650383e5006800c0c41c1100d40d1300300110f117940d40d1400c11001418203980c400c00300038280340002010700d401c404000580300e01c01c68510b107091108a0070380c0d04a106001940c513403680200071407421418100320903101942c00c50188503a00d50000802d59012449008a41059507020f4072401030750010384210702 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 121907589 1250 121906339 121906381
    0xa0e010515210c3609191b0305090a0803150109090219020c03030408060f04061419050606041d0c04182003010501050a051608030108060a0c08060a0e 66
    0x3200340c03d120846401c00d009101c500c80b118041140e9084035000d44011000308101c010103490f4083e04002c4500b071400186a100b40340c00d0310001420400c0903c54112020300782145100035170700240006945e0144100c41d0401d2500000f0010202c040d41c481c0102c0c407000f481110000141c117554240e0f640220020405401e0301e031019512030562420084a14030119030b200f00600c6010650b01c05800c0120403201504c5000300136002e20b0b5202c504400c08080003410817200c050343c03203050a24440548148600407a5800410402045121f00181c03c1d0348014003128072900080000b0800304482111704080ea8100c541480c8042c0d5031040c81e11194042d6500124080e581d0079031030000740071658000000c2071700341a07140360411103440c4008401e01090041d0b030f01007542040460700007030084001d002082c0704015044500c21640c3c0d00c0340ea450b0020790181d00145d02400034001c07a40964064010151200c2c0b4080150380b402c0344c00201d070840c1a1241401c001c8030130f00460201c0c1c1401c104a041b100c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 121908839 1250 121907589 121907647
    0x30f0a09020a0b0f0307140a0906030b13090b04030206070e0f121f090b0a05010e0601050c01020d0609050618040506070e030f0106170607081003060c18030b060a0e010515 75
    0x1c0110310501c6080c5e03004036950000030342c801e41c400ca45a1728041c1602d0078a180341d034410240c5802c0505c194000c1401c4440d0035400300d24140107544100150003004006071141c03004a10901701450f002e450118054000814890103000e06030668481e500149003840040b0346208141d04c400f0306e0786041001d10a0300418030300345006075556a10040c1c000341c02c02c41c030499030b00800c2d95903894514110f440030301940007110882c0012503081d62080000c1c00441c200c10000501c4c0024a0712054200d4500c2d5114140c641c0e107510410000d454601c1c0d9950503029141c840c09010700d083c0e03451a4271110020a94000e0100036003131000b45803000c04c004103451740000020842c0d2622420034403000241e40300c40204a106000000700c140d8451440030f40540802c48044100740e09595451014041042007c010080c9824400c0103482907070a8000c0198010600d2689030b0601c0070501c0620f58454119031400f807508001088a03403900610044500401545191204e5002241a9100c1e10620b4424144 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 121910089 1250 121908839 121908847
    0xf120b0d050c1c02090f041502041415071106030a02130306050a0c0203070507030201080c1207030c02070b090105030a020c0c1302090f1005071202280203010e03030f0a09020a0b 78
    0x24071400300041120b040242d8001c5007142c0c04101c070032410003500005103c0206607142c1c140040507030064492480c1c02230701d840700a44101260170503400500c0e07a1070314240303915890800c40c00170508041501c03251854030000340c0364245000f03201090503008050000001d001e00c41940d0588400c201560360304c8040075070f42c1c140341014000c10384800e00500d18000b01c98043c913000100320746415a10401522040703280d078005440105009104d0200100e00300f20036102044220601d92003031140c0e4a00041c9a4560b14001b403421103a604034254400c1c0403c03080800760b8014080d01c0e8004032042002d6544d982c041062401c2c0504280990340060300140106040010354000d009101002c0d58290f005c078103004100406010104c0c01240840d001308941e202045d0440081c2d03129840c1c900448400f10000d51603140c0710012480b8002600c124021100114038083c01491802d40d0258011070650600c602c100455080240510700c1c02ca99901b590303000c41d200c4ca80309400030900000c0050325 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 121911339 1250 121910089 121910093
    0x306190209041503021e1008040602070b070c050c0301361a1506040302010f0e030c0909071802040501020304051e09101d0108060a0b010e03190c150f120b0d 69
    0x1180843d030208901c207034586080113424090080510f100110024041e40c031060840006465001d4050425122035400b00080004911302c03c0205002e5029982c5900c0c640d0000d0074142d051070300c0c10071200c0c800d9040c440c01b01c0342541c5409401c42c01421280c104624220b207040070424a10602c0b0b00100586420060104503d0b100781c40ba903c180e401c010348a11041e061370401c040c0f841907000090116160a12103800b45100f1031405c24098009012101c0017110306c1c00040c140318044a102c0f049034015441440742c1c4507942080a0201e00e138107425800c01d0f06001c0040d4682c042d0b0b0040600a0481011013008200030044a4600301d2020342601002e04000c00310f201b0392205805240d01c4554007408216034555040000b034100e400e60342c007501441d100d1880c040042d003d584800340c1000134540100302d2a9409000c0400a4a554220807556021a2510402415281d400140018400c004000361290461502e00320307020035190903108030305c5106031a4024081481c3c1e0b560001d4101c040201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 121912589 1250 121911339 121911371
    0x31704150e0f0105160f05040303020706081e04060203090f150402150708040f2408010302090603100204081b0d030207092d1401080a08070209130b070201020306010f0e030619020904 80
    0x103442c04561b10214004d03e201c200380c41c240320303a100007801680185410480144289202508444418014603c5500940c4500c201030307070a440c02c0c2c0361280d0020a00150880400100c2c2c07044a922010b0b2504001c05d41d0030030603240c030050010380540e111850901c044115007080315481c1c1d40c4205115181c645612003902000100e000e41400c02049210b903c40d8051000080700e80c8191a5641a820381e08660a11060800150445030544503107180161440018000b810203880f81030020801162172081104000f640048020b01400710311041c02c0219a01141c24015252820404078400d1901801c1c500c250304411a0b2103012030510100507004d42a40c0c000c54a01800081c641030f041e600ca40c003882d22107a4900000b400c44004000082c0107050101c0382039401484008103c401408503281c0c4010404100e4003580142d50000c00c110041d03030003c02503000300c152841c0440c20414240c0c0030950b21003020317191f880c1a900c40d00301001c003905a90101c90180c40e000e40705104681920000320 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 121913839 1250 121912589 121912621
    0x1090506070c0201090e09100c030204050303070302150109021201030803040203071a0c07090612061508060106050408060c1603051b030f0a09050603040c0302011d0a0f03031704150e0f0105 83
    0x1e00142c218500090040d01803660b81d4000c402060123172000d10041c2c81000010850020b40f00c1c00d1580a0200007219035040c000b80190f01d0098000d0041030006001c00120502c0580065010500c1071204402c40812280c1c0d0b0740c1502c1d482038540790340b030303e8a000280c03401c00d00e035001210201d42200640882a44400030386408044c207000c80d00c443c1c0c0c41e01e120354107885550250a4108a818401c003003c203019400c41054015101c111807146a00d81204604003c0f00340c000034003288000401300201282000740a6022004902083c2080c215204082004c0f400d0480070b0100140461010b00c0f099082d5511040b00360344504a0f07a03642c442e4034251820b0303002981401c0100e04001c8000840c1d05142c81201c0c03055a014060008480c00c0d6401520b108003410040a801010b4251081c0552100350081000d801810f800a20640c031350300c0c1c014040b034009500e640175a41e44000340070000358089141109010580c0020540070951801c0a01d4144003041e070009075800d1070180441c5070510032485d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 121915089 1250 121913839 121913843
    0x120501090903260c0a11030a1116080d20010c020606040e0705030d0302070311030d0204090c05120114061c050108070b0f250614060f01030b0303090d0501090506070c 73
    0x12210035486050a500b061140f0340b40c001e94681c0400107444081441c00625003480203040400d0b19107031503c8010310716006080118042128110201d201d007408000d65034800181c4240040420300f00100c00e41c81d040b10380c3e02c950610551306e00e103070070510160480c81c0d400040e003002000081602c410080d500c510030344019005038505200858210008194441503410180041ca00380090200032002940700401c01cde01045102d290958602c0c4060000342104010f5001c05a107440c1000c000c0c0c800c860182c018001030103410001c1681100b1840d98950454034200429000d121070400403e03290b10501d80244008050380440100c101c04541c00141615841d4084403c9140c90304030301405c81c821040c2d2000e28000600c40c200040100da580100800b04031505040d41440070303a00c600c265602d2420080032041502c04000b010300300000000e02c0300009107000c0c440d0000080100b0b85a05c0383c0348513039001e50146080d603014000250418003805611200311801494020702c010b09400ca50402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 121916339 1250 121915089 121915097
    0x903090815190911060306030307021809100b09070c0507150903050c030a0b0406051f0303050a1d010c0f060209060304080304170f030105100e0603070306080f0a030203030c030403120501090903 85
    0x2880319440e0b07641c42040710345584040c002104074591000c2051507040100320326890b100c01c0154030016140c0284804070015420181e15407402d05942960803c6150080e0303c408505d440c04225065851444840d000360550804602b210500d0800340d0901400d6004100d5001c40064030300a11030b8000c4840d400c0f00e000b601581c410129040406d91140c600c000060110301100f0046000304286501150308502817003050081e507840e1440414084107954003c3c2d01180d0003048101c0e402d074011000a240c1c00702682181006c010f1200060600d48901401520700c4901500300c004000e280c3d4116010300c50700410550f1a031410389840c4181d43e2080310122070445c402c81c103210303115420405980a05c250262200e0846e82001c0521a0400a40003c00c041161048040c071319903c03000c0085008200703039030300415550f0804901c2031a281c504c00744031300c0650000f040071004c00d03404021340c1e0b04820310a080650300d4032182030444a201075103040702c06403881c2c04000101d840702c1307078084d04986100e600d0b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 121917589 1250 121916339 121916371
    0x40f0210021219021911060c010902031014060406080709020705070807151103090619030b0d150b0306060307090c200d0f0c020a05060d0f0509060103170a0f030903090815 75
    0x1814014940002c0204410f400c2103a16001f8a4203001914800c0144400020000304540000c2e140803030840364000e1946d41c0f0707402070480e281001a610b9002805890900c055490a45002d981e2070351441140304c880e40c040360610401a040c44a040109801e03011140041e403103410151300d503034904502e240402c05060341e0114141c80402070303511040000780314604062540307a00c0c980c03018560141a0030180d49286035940d035914890315810302d034080e01e801e071205103100003910200c0c1c90304d05a041c0b0a5000c42c08004148c1c4c0e00044020549606c0b100104407528840d4040d5520f060704032584c00c5024100d61048400403000940c004940c03007642d200701c503540da89001a2a1410759040294010851100a00050400600500450a8a580c0000c0d58941c17101d4200498100b035070b410b110f50b0030400c010020302c00582d141d040d541032174198103440c240c015036024203030b0703c600308000041c035455920320310915011350301c80030082001a095030780076800c08a000003602c40032508400704404180b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 121918839 1250 121917589 121917613
    0x30603060f0c070816050a0b060909070506160c080f06100e04081e09040e0a0606060e060a0e0a180c0305070f1202090d0813090c020105040f021002121902 68
    0x2a4000c1c0c00b4000e2014064078102c8a9112950564008030009141045c02e9482c1c07400184100b101c5661a4003551050741d060918000300442d030380002e0444183d075480100c041c445a41c07000704842800c0d0700c4030a01e1103110f0091514000d84140c40e40480003d010743c5072507111803040451410701c100c040340030803031509482c0d4280c445502c40584002c0c101010510a100c588070713a203003005115191030b080307950901c0030340300008080c0c402241d11000c2039007000c3e0b116010883e03a401481302410007820103001c80280140400c059021b0384100204008540040754010380303407160210060724020031202410980384082001502f420001c1c84002403030700c00000e0895100351410b412528166550348000b0300358041c050042d400601b202d59124189649002c000741c2080d0007010764410045100761145d107001d0366071040741c00d0314800703d05590601c801c120000d21242c0200c140d07190b040701c0710012190341034001c030701c3d00664011200c40303060b002441c050910150003c0f0722010b1140d40c2124080a044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 121920089 1250 121918839 121918861
    0x90b070216120b040212011d0703020307080318090c1603050403030806010905030d1d0a03050105091603170c010e060907050a061d01050702060f0301030f02090105060c0a030806010201091703060306 87
    0x1960b8050410200d03a004180180781181c080003aa602c002c0022895402107641c0701c42c407201504d03948a144d4041c11040003141014400c640060800d0405107041059070030015603060014503001c0c0c0301703190260004200540c9602034a20b0280203101800c2480c02c10700e00900300e580f2500003035002c113460710005255907110305c02840958a0280c05001c580d54041001d803605001031002c0c40250003041c0e03007a0007980350340294000450144002240743e080458406050940c510550005180d8110003840030603024040034281d081c0c0c6004095903031140442c0c2074010705400582860034003400c002c1c27204082001441006440003141d0700700420340d54080c00d071600c2040d2440401060001c007440340c034075030080d0060700a041c0060401c44c50414508000184c0368006d03001207400c0c0d0184440b40d0107500b4021480e6024180c1544c002c0d2a0544110300036588c1c6203192030040400015000090071079200303420840c45598403050000b11074295510141440d0000c542050087c812100002d48010034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 121921339 1250 121920089 121920119
    0x22090c09090f1b12050303041406010b0a0509041e0902040c020c011b0201050c030c0d022107060b0f0a0f0e060f10080a150905090705030c1c06090b070216 68
    0x3008030103007600c1a40b40d0381d441020000f82240312690600120010b042504c082c1c40a500910030b6019681e039140a01c1c08100101c1d480071450800e40c000c0c8018010012140c08940100641d8140503803a01c070b100340002c01808242c08101580c1101e800080107040320341e0000681144208c5040c4002e11000608a0307a03450034681c00c500042107200e103061000381351140c1520041c01071400f03903e00b00d400c42123140b0f1039214000c001026403140307015940d1240c0c10310100c61001070865001c0d4110a070011034900600075284060006652000541007660f114026500702090290034803404035928400c49a0414040c0306010310080604001555480e00c5582b08030305480c024044115140c18040889240d00300903c1421030958034988088858084002d01d0010981e4205c00306981c0b030b2403800301e030514410364011802070340303c2c000f030000541d100815110b440f8041001090400520304056020308003210000c0c024403060b40c00d1007030f455804980003010340c020405413490700e962403040f0130712010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 121922589 1250 121921339 121921343
    0xd09061415060304060209100801090c080105010504061107030204061404110c060f180a0b060f0a06051605030706020f0a08011203120207050c1e041514010e22090c0909 74
    0x803078000c480320510b080000b454000740164401401c0c0404600490080f226500e40c4c070020812410040044620900841006688628207280954540320000c1c00d01d002c0c2e40201010301c8451403040d80c400f0020090a80116001041403000d43d9a4804000750204c040d282280a0303410b0aa403525042424000c4540002c0a04005c000968800d250504c412801604c86a0701645500089400c2da608010941da802d000d020714000d2030803d03100f0405001800d5000c180111b80c01c0310108050b0360400d0550700e0b20440512400310030807803440c00300e003503106a240090105102045078108001d41c000904102820ba46403509541d88940c1c070b0128040407550002e00082d00485500e00c1c015407a001341045520038003c8958480002c030002c1c20b4440001021b18041d80c00680c0742116150902522014174501030668900608003150307680b07001842c0c4c080c141881080c0c80f4010142d00c501c6824460341e04440b180c203603070b888a1150403018000784201a5201e14420782c020409010502c50030301510303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 121923839 1250 121922589 121922611
    0x307090f0b010c0f1103100509030d0e01140708090313090f050c040b04120212150405010c09060e09040206070c060305010602120f07140106180b0a060305090706120605060d090614 79
    0x410383c0d64890b000c004d17030340325a601070080440701c05040d10f96004079401825000c010310f80360b034103001a0008403000d404800303a89a0511442508201000506c180c00c2802803400b41c200b40d448036a02c600d9441103650310005081d01450000c0c40246642c0603840000b51103001b40040c1c0c8458a030001140034500500c4205a1304000c00c008161220544040c25803014021016003002d01e2034003406c1910521f507064403c1103000c200800c208081c85130119001c11410644001ca080400c0146001d0002c2c0b040d5000e0141e40d000304055598000681d20001da110b220b4204d4075850b01d00080c0508804c4c4162009440f400003208081584031007601c03850302c0a414254140341043d122840b08010800315503845550340c1c03c1c08a4141000052101003c04410000ca0304405d5501400a44d400b035500c490105403030f080600040580110301d850440c1e03a41e15040344102803141440c4024100e030381c407490f03001400003a0481d12100a4202c1c840d854001d041c104003c1180b542080440c0c60100c42c0b15005c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 121925089 1250 121923839 121923863
    0x1030203072d08010207030f081003060b04020c0102030405070e090303011401030c0306050405010f030b0a020c06241008040204050a051015110601170f1216060b0307090f0b010c 78
    0x50030a03140c500d00c0b121041c80d09445000076460140301c62000340d000f0f10820b9400203045014103030000707070a1842e10501d00d011742d001d141c0354280707820005081c08010040354036091440019910740c0c0540310400c4072800219960b00f01407230305c40d03030718440c0744180c000d00040c07040001c0c030701540441581e0417180c0d4102c01f00441c00144004500520f400305060301071650315240462503840301c0c400e040c06026015400e0b03401c207007541001e00910400510b0141054010001c0303040e9140045103c513040072164017a1820044980c45a0000503040301000380c00c00c00c0405c0c50901668000d403035a014038000e44040000e512003002c110180c0f44100c40b6009004006401042120b000c02545101c22104d0b26100d000741c5292002241080802c6c0d01401094207001c051100b8501c050003d83c05481210006210448420480d04c0141c001c150b008c12030145400200000e100c0c0c2c03500f041800403401000d580b081c5484135040c10080420200f020701c00362501c002000c00394007460264280302c1c0c000741d6030000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 121926339 1250 121925089 121925099
    0x3141209010c080c01050709090f0e030403080a11010f0506011407050705010809010603140a020a060f0804150b060d0f0b030a052d0706050409110304080313020f0d0c05040b090103020307 82
    0x1c0c4241e490103c5601c8004c100301c0c012241e0078840c01d8090001a41c0c0c4a8403540b44c440a1410f4456006180003903d1034011100604140041100e003120b0b4451613a45d11418410003d90702440d0b15600460154209601003031203030320580c001c032f1090304262035031290300e0406c0000d001c440c0900d030340c018016800500188420760281c0c829a501240081c0041401522030792070724030898103a400800c107588000350502c00c61400b4400c42002e0561481c0004222070040d1008044080c05000074110741000e00c0c0c50f0000c1400d580000385c0c2c199014000c0c0d0354a806015024004280c4461035440c51071422645605500d0041107440341d60740c0003c020544d84000302c02c150620034000541420755a8041e110717a24018090258600800d00c544440b52a1803502c1002c00940b1810540d0540c040000c00c10000020031247c26690000700600316908030f928144085001049005c0090740d200d0780c440380040c00c01c002d44500806550060b203040c0604d400b210b051041700c180a00000358590881001842 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 121927589 1250 121926339 121926347
    0x302060a0828051e0f0a09060f0c020c010305090c060703030b0409021807080f01061d010207030204061403010e1914070509070c03030b0a0602030a1101140906010314120901 76
    0x9004601c1c90780088852242d5515105040411502028020384030802c200c5890140d500044a0481307441c19031203203103031654030b42240f218002d141686569840d5034010074000d49620100001203500c00c100612958100081c4d80d44081d44c605e9400a0f007444c0004519901c0414103c03030204018080d1400e109656605902414101041540241e691074070b80c400b6030358513200c16001d66600d00355030b45e444c14207080080403402d0045c00004204100c10040040940c0102c001e441e2181c4440254141c0480b1310040b42031901c03079070010f54401d090000c0400c0510380440c1180d40603c04800801c01c034003001c15115141c0091150342c10710341ca207030800100404c00002c20b0061621081040e02c1d1070743e488000048500c14269080c1d00080c070f44071224010550540b00c0c2030141d89080700c0d82c2a103d45440030003941d0f44600c0c3c00c0541044100c0601400c2010250082c007600b203042c03008900f207483d0003441295078807024442a80e0119814006c491402d00100e2541c500b000502501ca1070b002000006603 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 121928839 1250 121927589 121927591
    0xd020c01051e0903060a06030212030405011e03020c15100801060803040519031509200907050f0d180b010b03010f09150503030307120b010e010215060105070f08130b03010302060a08 80
    0x466914803c00005106607811701c0603034420f0415030800181c2c6030441c01841403008030b44c840c41965902c10041440282e8000460b9403040e021303181d05400101030110704401901500c1c001414074400d010718408084018542e80b4401c0e20004100024255104612401d03a840c43c42010842d800821051049040008181d001c1020301c480f903042c09907495071903026480701c0c1551160070940c2c8540d01010800018a80002140100020701d0301c0d081c48000034040c618054042c8084c040c00090042080c110001501e4803000000030401000309002d03c85503006d0904001254068022030001c5101500da105a074180c8d4900c0c10051f151505141d000c500504020309880326840f4600d000048569041009510803507080d5601001e01154040c0300b400d076180491440d0500403900492242e5984c00245118003106129840701d180d2038440040c0e0312845820405003030004404002014002840000c00c81c00d4519200101c503243d4a191080e01408203001c000d600180421092060501c1510b0007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 121930089 1250 121928839 121928887
    0x62d0a0507030905031201050a0509071d280302031203070c081c0603080d050114010c021e030a080310050303030705040b180603090f0712051c020c04050c04080d020c0105 75
    0x442c8034194907105c0c40c1d5089005403080304051a4014007150816a80d1400189002d4443c03611a0030202da000d4041c1c0e8480b02e00c0410340796940c2e04421030743c1d00c010b2307004a5007500201351038801040300300c1c002c403060325804164040e22680070042140d50450080381c1c8104180d0b84c0390306045d045d0751394044040d80b0000b40180172881c1c1c3d0701c0d05410400544902c1000718414440b1580d58960180b40b00d064600592100400001e070310145804c1e80d0b0010091400d00d0750481c0c40d0005a8820a0f00c8090b40565000058040c852a200305081108441c02580100710b84034a6006003076881041550341c4c80304443c0b034000264140420001710995101034210406555220090055840049241034100b215004010703401030300d00c031001c9541406900060203100da1919840304c02922800c0c0e5601c020420580811450400030300400d00c02e001c14000ca0200402c00c1c481c50410159040150f040b60080b01e03454002c500d030513060240001000d5030300c8041030f1606400e0200403840c100b1000e0941c0c4003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 121931339 1250 121930089 121930091
    0xc0609030a03080a09060501090209040c08041112030f040303020c01090806150d060b220e0123070504080d0210050708042001050702040906020c12032206090f0302062d0a050703 78
    0x3c201c000a0b894007c1a0182c41c2000c001a10740034941c0c01c1000f92402d01e905070381448600300610000c280d03201080d000d1403105881d400c40c80121007940910b144118a01e200503c0e10200c0c000c0200740d40031403142c0100703801b641d64001c41516070720801d841380020313034228941890070b0045c484c160070000304001d145401004001941c002940c045118400c407440455103811540d80310001d140707103078407402c000420454000c00800c000c400c0d81000100780050700d1450200984002020a4411821200030b00862826500a440140c0703020f0b580e142581400b40c101400c00e80041d148034801d002c0310b8403442e08103000c8403074144140d00000c0c00200c1000c0c0c840c108081008042c0c0981c030743e8021502c02c50b105181c0160b40c0d0414594590401d0700405a8042405041050100088060b060320584651a8110240c2d248240c9841d8006000e03000004001e010110306903400c0c5a00030410364419048600e00c91089080b45c0c0307510a0701711600d601e80440310458004204482095404268080200c1c18 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 121932589 1250 121931339 121931351
    0x18100e101214160f080706080a090c0513140601030c1e02010b100c0c05010305010807060e060403061a040c03022d07020a23030712060c03060b03011203020c0609030a03080a 76
    0x340c94107240c1c034000501c40c550511030042202503000c1d03844d88028203640c400340c00700a040101c0104401c0c0301400d103003036242d00d41e2095002e02c18404003030001080000c03e840317401c0c0c03400e8008001074140d82181d0b0f00d42007101000608294068060420000c0f507580c0c41d841d00161590710107082003d02c0d40034000719942c440382e11040d5281c1c211a102d41c02c00c2901c60046101e41480c103900d0143d400c4d0081c42c1003600746001000109000900c01040e01c6035814810080c2000402203482c0740100d901c0640004c3c01c060301107100350709070114600e14580c10f0f5402d100c1425105802d501364410000b030031030076203007442004154030031401542c0340c62311420003145e2419065400040480c0001e400112191260464000010300030140800360b1040a6003d40f803941d01e000c1c15080107034182070300501565203501c0060740701c2d842039001c42c0203402a40c90541d11303940c64402401000448000481c054401d07400e50415518003241a00c207562001401001005501d90f812640188040d140d0164162201 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 121933839 1250 121932589 121932623
    0x103080319020c030c060a0b06031b130603020c060907031104020a09120305030108070e0601050711030a0f03111006141012091208010905070e060f0918100e1012 71
    0x80002c004500a10300290f0705c2d40030140c0c109042660150111000b14030384804203c0c2a01c1d61001e40b6031008400a101b181052441486141c43c4100056840d40d007420700c001091003034250740542155010541200c15030b44c1c55052031503035001c1034000601583c1072017a081ca01450141c0007424a107440707142c48650103070340d824a95203100c480e46040f40440c4002c03005001c0050108000c034014005205e442031039041140000e021441006ca000c5c150340c1d00700d90320f024551800c02000201e65800409a0f00300845070030010080640506000002d005243d40c01030900c0c580c0c0140030940c4d02c034400d00c0306128054010441160640021b02092103000742c03c0150540051040319860390003240b080e100c4581c2184000d001210503000003403818030b08010301c050507074007810503009420103851155481e5030040c091600b81c096a50f080e80e0040a8082305040d800032128a40c0c041c0c00440400c1030181d40398448156000e400b1501c030015040030079070400000303440d042458156406400c82c407160100e51 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 121935089 1250 121933839 121933841
    0xe0102040f1403010b031902010c020a150801080c0109030314031005060c0a020f1f0e010e0604030501020d05090a0b0a02130b040b1909060f0503040507210512040e0103080319 77
    0xaa8000d00c1401424030400c2e0550a0a00808808001c12409001c01e41241c4000241e40301e03a80901a0400c1240c2e80c05008644030f062200c0702508001c030360410340300390f00e101c0200515024010007036140580300b4100341550043c1c806405995068a0320007595518611441d62a003004008500070320398200700040684410008041000542d0041c2804510340c1c014040620b0341044524000c041800f004004807803440d140c4d110860a9281c01102c00d46241d0040345d21101c00305850340d1121000400104000c415402801000c410980c2445a9074803000c01640301c0c50309460203003828044d900001c0402c6260303801400040c2e02011801c40c150b0f04c0307505010725608980c0100d410020006501003440c0a603400e5080f80d64624500055120705125005110310000802c9406105c4017002080030003038148105d0028101d002686541d42007200c100000074030303508000361114050b40c1e082c0d030440c0110000700c5080d500c05034007606071640b855980348240d41c002481611800c2c03012001e99800c0c049 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 121936339 1250 121935089 121935119
    0xe030c27040807060e0a021f0207030618020a05060a0503040305030a0906020d140a0501150c061b02150702071508090c180601110a0c090b0112051314010b01120e010204 74
    0x8108983d215903091808000f281c02e4801d80031115032000d400038005941e24030158a0710000d03000c03134000712a0000f40592800145420043c801e074200244045490344911030103022a000302d40b406201075480c400c0c80310602c10861030900040c010400240824090801980c002d4140d01c000220150b00361280e074100e800040c0c0c0608070310b03241d0000d090110103801c80d03141c20a03441c0600700f05552500382120754510401101006010f60000107406101e501e83c00b5034541440103070302d000900c0c20f600009445280080321010742010035004903800720301c00540300054075400c00c0c840344c503105c00d41025950b402008101c04103034412400607055684a62118541032002d11641c6111800c0050002d0718118032144070702c0c072551042e5640004209440000ca048540d00d03040003a01c8040040102d842c070040008113041c982c2850b05110307105000c0f001c4584c0711130082c03400341c404d900c02480040c20303200c40303200c224000340005990158402940d4001814801c880c000149040e568042865030151 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 121937589 1250 121936339 121936343
    0x504080c06030601090f0906180c0e0909010207080d02030708070f0f1812050105010e090d0c150b0a0e040203060c0c06060f0109180608120301050d0822090f0b010e030c2704 76
    0xa108c100810640400030f00d40d02c1040360380c5105101c1a1b092281c000c1c01c0c0420f6207242d51003403c1d00b8020440c004020f5044a044a8204500d03569030307000b0450a0020794002e403034150001d0701600000380003c0c811f004100310400d181d9500d5942681d190800c4a40340010400384041030403180c000501c2c010110070100a541c8a0383c0046900c3d0f160140ca192a800000d041c248282c004a44528020f9408503074150240e078070512000120300740c1c00b040d9006000041401e030b0000040000411884617152125101e240b007207040750240c4d541d6032590340c2c682c01860b56411040e4000390200b42c152030840c112154441781072400a21441d500c1c1070306900e01c0f0308481e289010540d18002030040030014440c4505060401c030000345954506008600013112064002c0c002080100b103417190329241d0802000c14503080e49014842c2502ca0b42c1100080071816082d40409103840c40740030455026a82c1c4040d801030040c043c0c03a0852024041c4006202104284071038880c680e918000680c1240030614010b034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 121938839 1250 121937589 121937591
    0x1212040314152a0a090e0a0b030a0f060b0d08030a05060d050d110c03060405120a030b0603040803071d0102100c0c060c0c02090c04050a0603020a02010e0717010605010504080c06030601090f09 84
    0x900c00b910f00380011400104800600030400820340801e422055500440700c40300095469542ca6000300d10042403001d101d075516006019501c0c05002c8011183d0a0890045000b00200b4480008000d1002a001c000800300d400900c0050700f070052541c8a168403203c0900512812690760b5651410700500b8410b500200702c01e000340300800c1504100038001150107800500150400c0d0311790680e42d0800507000982024001911020980b09403c60b5000042c0079002a440f4249803030900c6240d04100c910100040c2c141c0100d980d841c41c00300c000c0f1018a01030300588101440f00035858054075002109034284103081c200c44000030740380d2082a20420460f80c945049251610410080d41d102810362041c00c1c009200921483c0da0700705540c41114140d0038010b0303940e8009041680034100580200d00d10340945000025003009809050080300d048000800c440d0f500c070350042d2118020380c091b0034243d5114182610300b60802100451f046141410401021695120b40000740f05032a04070311015 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 121940089 1250 121938839 121938871
    0xc0201180b180301020705030301050f0d0609200d02010e10050903191106040311100311030901061e0e040204090203030403050d050c010c090324180c05121204031415 73
    0x381c0c2c40302c0c08495060004030025071414803540c03907182d60b80c04180242e46c46024041d0b40b1400c40d6860148032081594040d030180300c50811402c095040c07500c100f016864200c1444190440e5190480d00040300c940c0c140c48070700d2090305050a0040c0c101038010b42e80148442000f00d00741d685d4080104505545080380580f1090100d40780030424040120b882c203000c1c2006100c18400034050004d02c44941c0740a559244004070350070705c07c402800780d0301c1c2c0c1c080b00514004144403440006411a50603a500940010410040c0f10014029440313688600174030101d080d0040703001840c20340c001c5252980000e00b183d0500380c49440d90760504003120124070208600081c600000030b028015980300140500b0140b15580c6135495515519030710a09984914001006100150f000e0b076001e90003d08001070307061000703110fa1a00307000d00b507400e0180c2c5104141400c18001e09500c0014221110000c1541c07841c1480c2c136641d200380c100a58030669414a0040c02c4801000e0705210031914803464510f080e1440c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 121941339 1250 121940089 121940107
    0xe040213050c0301030803090a020a03030f08060a230f04050f0403030e0a0209010902031e01080a0302070e070e011107031709130608120a02010e07060f020708030a0e010c0201180b 79
    0x108580411009045414442003100010342c042c1030b01c1c11203800450403a03482d590341345d14609000c1c190100030340c401c01c00000070083c1035018040d000380440581718255207840303010030456802010310030000c030303c804404501c0d0700c2401d0452103c41003070094001340785041d60200242c2610000c440f1680302811000c200014075506015107010043c06a0280292031041c3d004103032160320500486030b40301e0300000032805000d074a12051882d50826000500c1658641d03a850740c50b036003c90f0b0250700621074000080303000310509105038002c9419440d00301284c80f070180155103a50300b0003501c564a009044000011404441c12650b40c103028041c81e40d6205885020080d03c0080c540b0101b81c0c0c0c600d8140d06000c13085001070001151454042040d40700c9500030000c80c09021011a404d80901a4500000f005900301d80034020304812a001c1d18440358450543c5543d03801140f010100182d40106131400550080d01c01010060040c90420482c4002c0c101f40926452241d1205000300e40010f29990703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 121942446 1107 121941339 121941349
    0x1030203040f02120d030b0910120c0312090f210303050603010905030f0909010501080c0a05030c0c061014010e0a03060b061b0f070e24010504080102040e0402 70
    0x9240d60164131213242c0f10400000c80b0300129050881500007480c01a5a59210b6480e4182d840d43c5945071042624003e000c002c0309480051f05100e020002c40e2062040140003196070f01c4c1c00102a1420705442c3d541003950307100d8940b9040d403001d442c400f800c05034454031041e509031070003142686481e40001c0c010940ca001c000d01600c40001e5240700100014094980c3c0c100031100c001041c0e81e0b440054500250072100c0f16804041040345019103806040515080002a4101400d22a510300d503546090320680749109000a5441c003001660030380042d0b030740460350070b180210b4806010804036641c103146002c01440f030b07030f00d50f441401c050b2103c4081e1510300303445144a101601c0c01e100c4c803544840001103e0302e01c6024080300814505000c01606000380c4440304001c03c82c03081c0000d41c0c54404842c02080381007200412000800354001d00207080640304440c00c2200d9030820740f040003 = true := by decide +kernel

theorem cover : BRFrame.Cov 121762589 121942446 := by
  have h0 := BRFrame.cov_init 121762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 121762589 ≤ n) (h2 : n < 121942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
