-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2443
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:44:03.580988+00:00
-- url     : https://prove2.me/submissions/bb4f7aff-21f1-4978-b4b1-f36798fd1116

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 439208633 ≤ n < 439388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 439209883 1250 439208633 439208639
    0x2104020a181e0f0e010e06070e0f06191b030c06050a0b0d1101030b010e0315040819020604030e010206060f01030f0207080301140a120507050d15050709210c 69
    0x4820600c030200203a2820001d40d82c0000c9200795668140300c004401007654980006030101d80c3c1d405010020b00c80c0c2002800210605000c040c2c1c0c0b41e0000380644100034080b003c1c14140d0b0f644490a1080300d400404507601d5048407241c3d00200000c0740d44e01d001061110881c1ca24081506c0101c04182d80c141d1507641e0319803420385841c000b808008050240803070b0744440030000e5a0f503552440d09010702480506041c5004000007600701c03421010340c4c505105c0b407100007008941c1c00183c803503481074204010f4400398540e450a03031400d01501400e1201c1002c141d040ca081142d0000c0d080788070b1800703a511846980009001aa01c0340002e40314075400640b080f4200d40294003e40000074040442440189040e1503621440704940080c0c000c8030160504640740041490240701c104042c212040000003451a140d81c0c065855409100307180c010481802d403801401800c0108070444640e0301c0061100e4034081100400c1d404440c0a4102c4006200c001004c40d05801841c2c0c900c2035500c00c0c501603600b41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 439211133 1250 439209883 439209899
    0xa050106320705010213030201021014040609140a0f0b0a060308181908070e060f061602060415080703060602210903010e01022109121603110d052104020a 68
    0xc002032a18014078000c00c22040020001d2004000c00c0ca81c130009500894298400241407440c81d4948003003090608800c9804a0b41312420f181e0003a9001400080c2e004051800703a0301d4800d4034940302400d003d40303c140001d00c681c05400c3d540407846400540090b40e00c07100180c1c2101d03c5800060541d05051251f450440b182c0c600601050200034444030a04403a0050286200d0b000c0e000326281d0741201004000e0760303081202082d00f04070100d5204802550800114007a801110b1600101c44540050039041d03444440856010301480000c00a21824041001e0004c40c0240c50010010f46040000030b403244c40899016881d0003080c0e40c50704031b4014500601c645800c14018151705540e99230907980128424030050070003146124a809480d003501e80d00e100c05070002850700a0640121298000221a0804440d5a01c0c0790720304400c02c1c0001c0d070030104e807900342101c4035203d1807142200340c800d0980c00a0150003a140e0200030380404030200c1102d40302d650401d940080d0800104081408401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 439212383 1250 439211133 439211207
    0x90a080a1116060f02010e071202010804030306031707020102101b050a0302040906090b120312071209050604050c0f1504030605070203120a09030806030c0a031b1703030a050106 78
    0x40880070880c0c91003550801500e009807510b6025402054a90801100c080d80a006460800b998400a03020303043c9442c281c218445070a038802410428002d00007000c140c040d6208a01554200728849002c0380910038010060780103c80a0b0301601c9031200000f41e0307140300d004203541e44008800300d90300c0c001d102d03506070303003a4003c01c01d02002c1c95001c0c4804200c01d44030784281c000801991402080b164008010b101680380100442c420300d4004001c0d42d0750044080f4a590381065540c5080d0380c640d504c000303081c0c005000d0540000d000b80524000d0000748500011010310f500000c0b1880544100c1000c1084030070a112000c03103407001000c0c0003c00224020380c1c00360381d00c40d00c6401500c0c540503603100005880e250450301283c410b55941304050a03d603000b5000769101c0015002032a40010b02e03800244800328610000744042202940290b001e1050f15522006040b5643e0f100c40721a0340850043e22500304442c0c2251107071402000062051041c00007031055000c03051261420189059550294 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 439213633 1250 439212383 439212407
    0x60b07032c040f021b0105331005070204021305041503030e1224070201060f1206090c08100911030d050a050304111002032205011b230312090a080a 65
    0xf10368207000303211190f081d80e0010313118031003000c0001480d8a040c1078454403010040c8505548160342d09205101480020251409440700b180c25518480881c4400c075920712031108020f40190011503072161180040d4819419103a044400b07101010320b241031603008413507910010700040c41810900d5154100f90002a0619401c2b800740c0d40c210690381002e00201d107042035900c5d01c4020650400045d540d080c41808017500180039418031701441d01e118415000d0341400e019081907900c2c2c08040c2040f80342094400105420420303580108000c091580080608941c10b403141e0b0340d407201007900f502e00811010304c0085c00383c49840c100042c3c0344044803150001842241c3c0c10035003046039016640c0b1540c1044c4215042c1d40256526440d0300007180c0402c2070300c50500302e814506241408142e0300084610501d403080f11a85080c02c40c00c0c140801d1080c00c102e00322599074050071580508140110050400c3d00a02d961920039480d81d4074841e036104044080905086800d00012185030700c03841c0d0040c14 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 439214883 1250 439213633 439213661
    0x61a01030b150d0e0f0706180509040201050a02160b0c1903050f0c190602030a0b031c030207030e0a060c0210020304030209040b0c07021503010f0b120c09060c01060b07032c04 77
    0x21440032011355030326183c17929040750b120f617104c03003010001c6940c0100c0c8848802642206490540c0c90700c1b02051103490054002030500102085801c41c113407080241c0003100e030f0707a5452902441c2d1788007030440070b590000e0461b20710340c01040350210680d034645007803c0c440c903450b81d40c0c140b0381422801101c0098006080c0b12045028078182d8180c61002c01e0300e40b5a810340510401a6039041c0004604200d4141004141c080c3d0000e54090080d4030303840030494103941d0141400b40c1e03900e08a01e0100c5c0d0f080781040825a001036944404503c00d40c3c0047c0303514081e032013a04c21352800200b542d0309980c1c0780283d110003907000000f000007030002800d045881da0407403001d00c552401c000250740010056000202e281000c100c01000400c03141d907910b20404018600340000703526080b010389445640c40ea00401038428140c1c0011410b41030b132100001c881d120b0340d80380c008100154039070000c10601e5105a6050340002c00c0062040b040e00017103040707040c503066801c0000200300310507414030000e40030344150060 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 439216133 1250 439214883 439214891
    0x3150306050903090f0d0201020a1101022b03060f0b04030f06090f0f1209080309040203100e0108010c080a270309050604080601091a032a0d061a01030b150d 69
    0xa6001c0c01824001c90110001e0b6844148600c2400025808815801d11400d1560184005070740c0114150a045030402810100c110388400140d00c0e00000040c18884400c0a004020401840c100c840c61841c00c00d0b0b80c1400b140c0d6460241120700c1000d0301502640c0f00c020801000028008900100380920814002c50a035880d5100ca0814100405d020b449a0b2a904500420403600809001c40500c0b6030030501100b9003840600d65072805940401d42c0110b500002045802c040e11105e40d0042010070086106980c40b020a113020342a1108840080303824007000c502011158050500d03841e448805c650322402a0388000c0c41c000c40e0662080c0d00f03005031044042025100d040090018100a6005080030751401114408032003030174044812044800e510319495540208144000202c4160556442d502c1d08243c43c2d040c03410704e2034599110288001e80d00800602e50025075602c808800c01501000200005400380c401c070703408117079000300c1507034800b2545858400907024125129000003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 439217383 1250 439216133 439216139
    0x1020403200a0911071401110909090a0f05160501090e070f120501080d090b12130515070f0219020102060a11070204090c18090213020d14180708010e0c010315 70
    0xf0101d5646030361803130000c0c600141c0f00044c8035582c40141c070300c4114400200002450b61040400500580100b04d02c07603140a00031405c1080c0c10080408160780004000c1c500c1102d038605555501003101d210540740c0301c07070440040c4544c014001001124048101d0742030a50b00c05004550207000001000c2c01e0000604400c5003085007407041601a0205000a003000f602164002d058a06640d12110f804402088000c10245169a006420503041b6060158003a26407910900306940e00c0065100d0803484020005070300e500502e118604d0039a80c094519140131152074581c0401018000390141e80550003140c40c800c820fa0081c102d107600603000d00d04000c019800502078132a600c4080e40c0c155501d82080c0000082000c02d20005e1031943d00800c032410322940071442603050114400ca0071035000c02c130002d40b43d0650b048907401600f0a042035515207400c548900c0b5241c03503400c200c2498414408041100c00051046600034960b0000034035003021410011006030a035001d0150407040621000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 439218633 1250 439217383 439217399
    0x7050f120403050c0708060105130e190b010f05030606220b0307030b07020c0904120f0c141b03031206120f0a0b0a0f091509170d0605090901020403200a 67
    0x181c0101e100e683c03081d0741c4282c81400646895495041030525401090041000740d442420403132040700d00b00c8001c07600c5814806018104602c0b440d2079038801c500c07603200b001000954001c0760706a03400d81c0348000d4550f0b1184149940c51030100d9a031a084454114618201065284e4103051000700c0000484c0c800440c002082c101702c02d5520032183c451100007405909501404004411281500c0341d405038541525402090010144070030140221000055013075489080c0080c20550405000303100c544083d1600c555070800646000c60120450440c01110315011045800c80444204c0251701c6444400c1084074445804d1841aa103124141680b41d81010511440d005207015800c50703241403500038074500c15135480351a0070342305c285041c480b6000100c40200c018280c1c4150940080d5200d06440e00041e034100000c0302c5224044003090500b06946a60080c0041c1d0310b05540c0c0511588074054001d0a0b4000c40c080248a02e02e589101c0c0344204410611082c0c00d2002042d100c209507680c070403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 439219883 1250 439218633 439218667
    0x510031a0a03081908040f0b1009181202061302060f1b150603071212020a0213060609050a0509010b030a090b0403031a011e0c0f051005070912030807050f 68
    0x10407983d680c0c02007030524211080034140e9021180500b0b04440915065031044012201c1050040070140c00d2804184558100030b62400a04068001005881c1d0600750700d005409940380101c0c0d08401d60303e01e40c0009417005c00c3c0d00e030142c956511210f4000485500300441364011003828250044141b280c1d14402103080c8000d42171101001c0a8292181081c110f0040004008d050b14001d80c81414100700318800400c0f41d200b0f80d03801a034411001c20200c00102c2c00c00082c510080d40c8030030040f0448444510a03072085040b0380554541c00c4c4010380d20b01c240b01c1050114424039030706c00b00c800d004006003d442c00041d903110b941d50f07100040741c112035580e920810805036020350000b6511200c03e40701041100c0340307808040003428225000c40910541c0140e043d80c04048104200f2180c00400412607036011900c035440d8814140c0320351f16a011a100c0041c1400c440c6d200c0014040a07000481224484040e035404d034050b503d00c01d05980d205000c1e00c8661124500090b0305004200c3d12007500c1410741 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 439221133 1250 439219883 439219889
    0xd0c0f060c050c0f0a0b060402221509050109030503090126010b13060305060a060f0e0a150813080a0c170a020109030e030f0c090402061b030a021005010510031a0a 72
    0x1030b42c80c0c8900d030079510780349800665100d2007043e51107032000502044503100f06690040e011a0003595483c080300507043c21a1000401e1660513140d4100031030908098880758244003502e940f9480208d9544004440391201c51002904580040000c05880e511440f9014000c41c21801c1d83c0c1e1103c2203011a10200324400d0f4801d0fa050100440d4070080040c0b0180880000c00451030f09100c14180480001d100066520400e02446401c800b0b03c0c024078080c2400d61102840181000d09e4281d441d00540302c1d100400c030b1802c0c00110001c0000c0d0940c1201c3c404051801e4020100c0c40c00c00081075000e6071803c04080068510507030001d40e000394020f192000300000401d0b9800824549e04625018101d041640300d00d80c07180d000705000050700c440008524802100442e62000f5a85480c000b140d00791060090701000e40b9001040c252030310b00d00000502034241180d08489214003034140d00800c030390302801810b41c05131240401d08001c51094101c0030b4070b10100045103c903007000900250310844268 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 439222383 1250 439221133 439221137
    0xf06071203022a0607030209130b011413090b0a0b0d020f0f04060509210c040b210a15090305030f041401020a0f0809010c171302032e0e0d0c0f060c 65
    0x104205540950504c006070300020780742010b40c182010b02e0002103003103800040511070595180d841c00d580380e2040b14920158860000f07680d07603504145907105005492405840003903820450300809500f8101c1000d400c81c3e5090744201c0c208242030341103c02070750203407110441d114014416150740c980c8131740c000c2c0300030000c0e603c0d0b50b03582d440e84000f402040d04d4080364240d24110300c40302201e201c0074041074401406c0c1040b1800030394100305000141c49080c3c2c80c1c80500301c0d16460740c08d00481050019221030306501942c01c04c00c03001520003507542512404135000740081c50500215424255019996420500c02d143c1c00c00040403058045003243c0000064074005600e5500445203650800c0c00950031442200c000d000c2c07440d0030b04000d0310316001c86200342459018034000806038a00080b241032200c1d4024141c9050504190204082199035613040100200d419907210002c0300324070500960303032004e8000e03011102c08040190358029035407206507488030321050a100010314038802c00c00000c141d5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 439223633 1250 439222383 439222447
    0xd060b030d09180c021f02070b040f0213020c0307030305040f021f0e010509100c03090305070b1c0b031506010c0506090609010b06070b04060908040806041a060f0607120302 76
    0x30540c0f41040004500c8000268940810018601e03400710b1440364000211507054000c031580c02c0680000e20800001404804a01b01400200500490004d0019000301d4a01c076000503501812001c1344904100d10401d64020030071980000e000341c0165500c41c1c0686403140001a07a6008070700742c000201084903040303201d090719450f81c0740c002d25130300002d40c030a02c1c0403400d20308401d000c01c00800b15025108203014001f4030300c0b42010712482c1004051503210081e1203030107568507048611504030342c04004103010b010105542c0005d251181c1d15000c40c0050051030054401e028101c45440b01622080c104045150313440c0129404000301c500809aa5004100070f243c0042c40c182150000c56160b031007501c1c1007100c10017040071101d00b640c106822110001d400545840c20400a2103154070145c2d19028038410407040c418034a48503080841d4a440c41384040e40c0e02001c2201c40024151450b9000c58207100d484040345846032440700030001400d00518045210611480d01182c00425420384445 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 439224883 1250 439223633 439223639
    0x6060102061509010b0d240504230a0c1b0b060909120a03230c0304060f05061302090d0204110a03060806070e0607060b100c1106070803060d060b030d09 67
    0x20410007281d10982e412450504035101200003000c820043c46080b092010200b030340e22200031039600101d500c00c0e01c603440c2440c2100c0e505007940c686e8420b21030359104529028084d145051038500c410b0105c400000003a00c596902140d403001020700da9212000c11040c039212096814006081000300b82c0240d4aa8582e86400300411001c06401011504203401c00c030340758200140e0900503038a90080c181404560210004030401c1070a020b8490701d00001040b0040c080e0003174000b4020f5004a010747c0c0c082c0a070f04220448003090307410550b011a007094807039940035005082c503809848100001001840305046940008080e65880f64408410410006480c0700f1a070301441100014010075001e07040c6480d2400c400b03484034040c3d10201e40140d200040050070803009500c40c0001740002800d01510f07410240b030040c0113561142c0111141d051002c96446039180c000309130303036510f039000b01960301d10350700d21007480368210013140b00b21000741e1500c000c140341e954240700c00b0000300d00075581d501e2140c1c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 439226133 1250 439224883 439224887
    0x1012051e0108240405150114090a0b0102030a0309150c0504150c0c12060e120405031510090e10050a050f16080601200708010912080c0d110417060601 66
    0x9410790140c6400e40c09125840400082c960f8404400e1803040c440c00a15034407420424241050007100100070782c0501c001140503070480340240e81c254400e0b01e00080c2c96030340103a41402c590412203481c3c0564000c0c0500d9034110b100341c02c44c005452190107404042060001108250340d140005000861004941072110065505a5083c000140e19003d0f40001143d00d6101000701c50780203000044c980c030f031201c1040c4495604455000041e0308222007061101c0001500250070034040c00b07101b40566404400241402144940a0301d80c41042c640000d14080c1c03107c0c010607002021003210301400401c45080051403242d140f16480f81c034404100c5183c0403c001d4100c036402811544040400c0409942460b440401c43c0d80c00f00c42806d00300c0e6800c0d08e400000d00da00403141c4a0900d00d02c81d642d004a0040410b403c80181d207885000003c0c240ba029000503201640100c440310304034841846a46503050113900b2008014002c4441b080c68591541c4c001201380c01991041d0704941e0150702480f80c156 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 439227383 1250 439226133 439226191
    0x91e0305300f030a0207170703021b011d040c1707020304030303110406020a021921060c080721020717030f0a02180d110619080609100302101205 64
    0x200c0480301c101c0c98003080d035040038498080079061950007540031881c00200028451003040c0420721586603500c0364038500c0c0c000d6030b4605c00510554000e82281c070b614215401003038070300701d41c0080d140d804985402a00c14440100344802ca40c604109a4000c480e0f051285041600e0140210740e0140d9610340c15070401038103680194840c0d50500d0ba04000c100907540d4003090034400e080d030440c2e0900380c0340741440fa00c400245064004800d40d1603503c04410095030069248044180324017000d00c96814487d40c10382d1001380031203400d404903281030011202c0f006245200c12403480c2a803001401e220068a9480540d8014140340000d0500002801b541c3c2d5513100840e6805003408205500c3c00d20079410ba103010011404940d4007a9005c0c803d024200b000c1c40104000c2c9420242449440f1440d5503410154882c15503080b00c041191400803482c5824100161840340d010039818147c694076507404c0c07040490b6800c47d0641040f450b46628805c0f0022809004e015441000700828840c0310280e03001098 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 439228633 1250 439227383 439227463
    0x105070f02030a02100f03150b0909061909140c0a17040503070804090b0f030a02060a0e060d0f140703050108030f07031b110f180609061507210e01091e0305 69
    0x2e5003c6404020038119501111021300062f251740760580c4940c008200325408080c00d8038180800c030318001c1001e00c090391000c00d80d1259108900902d0300c501020b100c040c4140b0140c01c0000e03c030288421043c409803000590032522a20849181801684032501c241d00303c1d800000c480ea07120740f07040c4468031b0304000d22a00a00c08a001d89100e40745980028404e102c0d06030340e0400d110040d1030500c6543d440805881d50f400c581c2d03800b40010804d802c0c40c030000305070604a48024595500100381c0092092142a060740c107054025483d0520307400f40003034580c105010807010030000041d2400c0683c031526903102400c2c4105181000804d17020f04021201e02504c4049018140006625150402514180d42c01c02c0e0140c0d03000ca896200d08000c42e205c1c014120b4048160440083e0142c1040b2410201094a1404400c0004584100f181c02c072000c0e200584203500141e02040c05200f407505502d00007504003003100c09e02e5404e640c0e82d540c7ca41080d01890000100464100c4207010640480c0701d001c5034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 439229883 1250 439228633 439228661
    0x30f120e0703022706011103040902070606030201170906010317220509090118080c0106030f080d06060c02032a0a0b070606050f0d170d05010b0c0f010b0105070f02030a02100f03 78
    0x401d5180421351303840c840c0b006007003e040141548480b4402001401180c000d0104c04809541e607011a0802030040c0490b84012400203645000ea403401d91804403505005042b000c0142c1041c0c0d203140c59500c0d428000800b08200f0400c02c010311070300b002a08025100240190ba075545035240b50004000c100c0780300400003c1c00340d041842c132110b20038070090810348496200c1100c64550f031110845a00400803900010602080940030006214482000d0038802c06c0340c107000d0008a480e1917080b00e21410950380290184c0c0070800004079201005294a000085500d141c400807282d0000140324440c1c0383c2c000340d07003600001184002d100090140d03001808007600c20312034100c0307014042000d02c94070f002e01501c0e140324007404174540c25001c001c84d0138110300c608040c1f004d035031240050710440d17120102070411441180102c1550f00350600490901c504161580340c100240354171103111010b01e52104980c07600440011a00581e51316001d425407041c00e54648100c8001c1c1d210140c2245d800070705580f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 439231133 1250 439229883 439229929
    0x40b102303070f120f05070c050d02070501090513090203010f0218120303060d061415030f0a242915041a090303070614191503030f120e070302 63
    0x10b005904a10480901c0c83c1c42e10304141c8995080840d44010300d00d1492102d1501d041c041444a2658445d00120f5040e018100b5610f68640410090342d85040c0c62260501003031448008024910b4002407024203405469000700b01001a034ac00642182e10009140c81144d038081045100e460181c90002e00300301040ea801c0c48100c0d01442166541e0200400080c401c900d00e0700710f90100041904840d00c40c0301c0d54862803640d400c045d50084001000403c041703011348202c035540c2c59101d20000c0d80c0d44e28603030058440041a0710580c0c030900494695080003568a84501001419420500c402c2860f0424140e00010000b0080100481d0b840f50b0802c0308a1120184002c1c0910010301040e030312a08a11740000780d80f4095600400d0841c056824050b1071107240240c00f502c604000c040f054421300107a4001440412094400c100300e0707540001e00b98044070841000d0002074042d004d410f611100a04120303014080000d41d4405840304200500d110b038105180400031810034403014440c3c40034001d0307148 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 439232383 1250 439231133 439231141
    0x301020f03040f0309170303071412150d02091003050d020601031124070501090b07180308030901020403080c0c1c110108190c08011a0406020604030e040b102303 71
    0x1020310300000d030000e40724400326000f0100700f5001e00a90710040c0740e9804070080c80a0003150f00d54581c0c1040b9004000303d04240e000c44a4880c20800300c032090241042d01044ca0b403100c81113206550004150b140d00104825009000350351000000c0e881911500d144403081b5056240160034408165605002d41d0f11400041c00021404003500216803400c2d40c12034041d485203207801d4048a81080030b1010100c000591000b444010340014140b01d0041c80c407000c460b15100070440b00d0140c02c1c0000241c1c000b040900b400090764034401075070003004040000d400d1070303226222801c0e6540400480c404691084804050a040c5105001008210b146a42c407003007000341c44d00b0b0288000c141c051130402400c080000c6a13003201e00110041c172014448100006100b01802424880003800348103a89180a0f2a009800341080100c80a6a034550702a220360380f00c6650640d90b8080d8419a154065120b01b03002072142c030740310210402c041290703072107001780b40381c250110440d50580041110039a80130030400c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 439233633 1250 439232383 439232407
    0x120c020102210702040509010c0207080c0d20062b020406140a09080607020f060112081209071a48150103031e0503090d210e061005030102 61
    0x80300c40c03448680d070b07101c0306542400c82c200e040744240c02c0029070081c545002d102281c4c40544c4807100301c4200d0f40031544c445844d4820140d450a4000ba03095010701c1441c041400210007004440a28140326001d00c0c036051110001412904610014204014849120002003900031302101e00f50f01012821407909080020080c40c003596141d2100e021000054243c150900c01c2661400900142050355410300b001c61000791a000b00003074005107803244400100f408400d68001c1201c240d0301003025440c00c041800d00d00300d082c100820301c0d1014000d07114009070301d9038211032192207449003148440d078801005544015101200c0c440c8601c0d2107840500d0080c1243e1181000002c1d0603240b44101c6480400c0c940d2850320304d40d1446000d080924034000410560032044190900320b01c4508600d81640c80e013401c50b01408120303444072050740001030840039240580791203103100008001800c10307220a502c5d081d05a64144010007010ba02407800c011841488680007006810124001e40c0742020325804 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 439234883 1250 439233633 439233643
    0x807050d0f0e120a06140115081e100b0703080703060e10030b0a0b1801050111160905251e0905130c0509030a0f1a06030a1104020f0f07120c020102 65
    0xd15014401000d0103145000c0f0070055000100d41c01042130240d0f168188480904d01030a1080c2003900072440c51003a140340c000c00f8075503c6211403919055075070010b0510341c00040d2000c0c0000d02e80344c0a1b03503030118410000d83e0040040d9802900d40034040e0070900e03070060469201307a00c8034030007040c60401d00c0320400f43c1301300a408907a00000001e41c1c0b40c942c3d480b80002040710320502a404804050b580000a0f41c20300751034100d410036211000c41e8207480350300036100c0130020052095441840b0050048140307643c00300e5000b0707408154003010117096494503484441300086000c00300740301780c980103942e13421010003c0d8100d51a01d00304540c42e141c08081503105140000c002803054440001125581c8100150fa200c40c0c002411149074154030b040440a05041841c180d81143c403d003500e021001d508110140243c801400401e00e10610b500e5017000580c02180f42030340079408004c1c81240d1038028004c1c0500e980c0c172198090392744440c6d00e0803450766800401c4400a201c01000e841000d42c0e00810 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 439236133 1250 439234883 439234907
    0x6020c0a240309080c01020d0605040608150406111b010f0b0621060607171c06033503150913120503070309060204032a0e190f090807050d0f 62
    0x501250283c081d24107030780180103107030300c814070740d07101207000c05690005800c550103e4034140c1d010403039503456880c0305880c2c0e10b40b0185107418003039050111703001a071554800135031900e04884260900d03402980110030040c1c121405e40640e9121020351030b41903014800d03c0c00c01a412102285804010880307034500543e00d400010000340c0000026509441d05022201d58551040d42c0c8045454400c0f100e0000c0d8112000c40d0202c0010050a08072070202e602c03074041a240c03c20303010006441e07004403030400b0301500307400414201c60f103d0003a071500b408032025600454500e502c2241010f41d02d0107000c40b11600400001042d140140f1402c0410030317000071031525070120b00d0200e0340c96940319416800b410711000e0040c4020710006001050124007900c914122545804152034542d190140b402d10940e00e0280d190b107050104042250440c513410601040c420355080030441801070000c0d00c04640b1024400e1b6590324000a1020070010103204440203441c07281800000c402e51418001c0440110403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 439237383 1250 439236133 439236137
    0x30a090219061d03070e010e010806010b04140f04020d111903050402060316050f0409020406140a0f05160203060405010c141305010f030f0219030615020a0602030c090a06020c0a24 79
    0x2603540f181c80e00c051100c3c1010340042d5500d82d1417035940e08008118a03400f4490f0031000c1c041e0350f00106e01e050701801210200c42420807400020030006080015a0038260b1030142d006508010751141c0d00554044d28026078025860315488500c03486400854034199103080301003503e080d0400c801a5144c1c000c0d6074000c420500403034500c038440c10041d64944035001c0c04c0d005110300407800040c032030f815800800580e01c0d1a81d03242c02481000b15400342034080c00044c40082060a200b203529244101c01908a101d003418640c1d45054060300420b00305001510b056669135125000400c940c0d03000710710701150000d0000703614036180002e0340c02e0710710b0416070041e00d0400c00000000181c032071084d00300b6880200008011035403980d182e2001000e0404040c40603001c00c3c00c0030000920030b01800503007408001c280c1c019143d811700a036035072002540001d00844407500c080c010717511a40c681c80c07000c402818030394006016201015081040e41e003a264811007110f43c1d8000402e40e0b490460221300791811883c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 439238633 1250 439237383 439237427
    0x612090b04060b0a031406010f0b0a080f060319050708070f150509040b060417070603050705220e040506010306150b0406030c02100e031308011a0d060b06030a09021906 74
    0x40f00054203503065540080c0c805001038004600754400480c0d600c1c100c0300c54000c3c034200c10380d450803501124001c210000021400329400075603480061510568850001002d80d00034a000a0340c0e00d07040e00d411201920248c2c448042405007040030809100503001c058814081c180c1b034050055440480d02070100c040103004200c05a1945841d0424564010020080c03600d403501e500f83c818041000705441c8043c2e01c103418000691500038800e4038000c104641c0c1d154030f00b000342000086520003452910304100480760000819040d1640950b01403480388016101039451030501a0507209078602d800c1c0d0402c40c4100070040841440112401c40e0f9140c20702162080c000d0109904003811240088102803c003204a8122400400100402800818500c0503140c640500c5401c80d1700e106c1c11450110707680d11081c8000e00d000c8810404036441500d0220700450a2000b0071620780041c1d40e5100b40c11384038107080c004c61608550720412a41030f00300c415880c524100d8010500c40e8490101019a108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 439239883 1250 439238633 439238651
    0x11a190513020705011404260c03131701020f04050411090406090b1206090a031b0c0b03070e0108040f0b06030c150c1c050301062f070612090b0406 65
    0x241085001014028a0a0020104400800065404900202d81075482c0c0035031080c82d50b80520b609406203030030808400031864140129507031070030300c040c84503010601030001d055070100c10001840c1c040c41902c03540004600d8001c40100b000090a400c9036564010f102055240702c0180c143ca040382c4007101c02041d03081d00c0c480200d240b803080404045e002800c02d80d010588800304d4100b2036a407030040d04d40d4540120744860301a1188429222075a2940007d080c18000c00d216209500f40101c4600340200c40d000c0030380c1e0f0200166000c1e4040070004501004105a0540210001c5054082801d041415240c540d079401c40c203140151000701004c242d00042407107510100035800184c00c0c040c2000c60b8800a0050745503071504094050007191081c444030b0140328140501038091200303270742c0b500c40c1140d007803090507205501c160340980091622502c0860700d940035028001040741d5428007502060303003400001805031001041c051682d90602c005140015900c501c8240d1040d0403502c0001c154179 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 439241133 1250 439239883 439239919
    0x1021c0e0109080f0105060a0f0b04090207031e110d05040305151801240b0c030a08130605040f02090c0c070603020f090306240405060f06180604090204090e011a 71
    0x2d85400c2160f440c8110f204c641d9003084154041406204d0440301e109003956503610a071a4003203d402078010980c0140000c100484590b00a410041c0c0f2078101a84141e50300701c030103168a41d00220420006a0078010404150401c0c403003070541c5c91051400925040c21500c51075921655010ba1440050880300010310b40c901550500021141c10002031001e407644a601c519200654890513002c0d9015140c0012041c000340100d81103c00000d010354102880c209007034501c4103004100141445440305414002400c034070806216520540190092000a00502c0000c00300200684541d01003080050304000c1c0c0025440c003194024034000d0383d60340c3d12004c44003580c000d0b0035109415100d00c201740501c442c0103e50000b94090400c00203908010038400300410b40704103840b926004440c5480308039090400400501d02078104500e0884609200d1000c07502540c00b6601500c1c1035680410144294140c601810008011142c02071100100030300b595460b8070404c00717200f8400d08494265030600d0b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 439242383 1250 439241133 439241147
    0x60e0d0b16020f010c0201020c0c030a0201020d0804061b480f050706091706150f03150406020d0e0a02060f13080601061806031401170c041b090501021c0e01 69
    0x11039954024410500c2c000c5e8013030302070b410010a11781c0500842500a03400c0c10300140034402950142d00401181409040a4960350009002551925125a03018070402600c4406a0815070550380300c2c42d0603014407214800a81001c005414120048030aa00c0e0b040306240c080f000e0155011059420842d803450300840760244164000d0036070165803000100c2c260002d0791038044500c903208000303024200144940c1c0f117510480301d0298024003a003100504d8200071410751000c200160890f203030a04040c803002800501101d007180c400d9000650303540611100c1c010301030300720701807401030102c00b21660006405009000100d004d210b40415500407862800400f10700030314420003aa4081d584071503005085600071841c9807001d54422100081991003440780f2503c90302c0040f05a0510307408d254007407820009000468989106d01b142039142d969440c411030100c5003c84010300301c502032824028041405581c40103040d0341086100b07944011a07000081620303602480c204103801c0400b801a40c1403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 439243633 1250 439242383 439242403
    0x42403140f01050a05010e060d0c0603020310080a0b150d0f0b153606060a120b101101110a0c0807021c05030705010f05070207122a060e0d0b1602 64
    0x5608000512140c0032042c1d00c214140d603025144d100306039480c1d08c103220800000480041414094890070410341e442a4051030b0880d01041034041c42c0d6540b03400181c905011104103031038005d000c500b449081d0101c5000d2a44048041da00752214030320316210f208140c1c1e490a0b001c0c105903a00c00000312010080c40c1c04004000e4010144502c201c2d0b6145000300303040c0c242c80302d2903190031008070303e1200158440c1041c0c81104002d01141c40c00d94a4401105d146810402404866447d0a0480031070303070301c1402020011a1f03584d1212824141014150b081d03c0d6070b42041841e02e08100000103d040e88402c9d6844c2c800d802541759580c9404a1001c568010030440700f180c070740c416016143d03080280220003055550b0168000b40b1000104041e5101210741c261000400340c3c1c011442004002011a040e07141240074061b26a800c41e0451030302554801d00030740041c800701001c0300901203607400085549820400361166030103a410303a40d400c1211140542001c810104c07842509040341d00c01c2190981c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 439244883 1250 439243633 439243663
    0x20d3e040b070803090d0206042019081014220f020418121d0112020c0a12114b011505030c10050a0c0804060206010504240314 56
    0x140b5115420110b14503002030311a030a16000b0032a13a0b445c25880000c0c0f0074029a000260f5000641605220314001080c0c2c2c5c401a42040060700d404207221585005d00700113040340e01c09007203070b4a5900c0a10040f40e001240c0c01c00c60300c1401080c000c005c3c042c1d1150949100c48884540390211182c286540e40050001b0025405810070241d000e890b400f02d48511440c2c2d104410b10050040e000c541914412010308400340c40f80040400a0744940c0701c0c1c82130040407502c03e0b0b001490080541006401c105540d00196809008402d0120429030300481140400d031001c000f0381b240c0540491071041c9854040001c0d0100001c0d2840948201d10420004400070b0502c4c0d0189044010ba00c1141d001c2c2c4880d03900da90384480b203c01c001078542000b00d1011055800180018683c0070003650a82e03044d00480c054404129031580004006804e0b00b001707101400e9a42c004007260b615000801080e0f40c221042c088601c098404150703400e05c2c40d2024102626408001425506060125107241511480100c0303e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 439246133 1250 439244883 439244887
    0x310150309031409130b0d05070e1e0108210412030c02040606030207030503060d0c0302030609010213060c030f08090c151e070507140112090501020d3e040b 69
    0x140d406500200305240b19841e080034002000240a0f502e01502c00036a40010000303490800102c4540d00c03603600e4110080c241034111f0b5194032603528145154000724080c031610418041003c41c202040324803203503c3c0e81c0c124603d6040084842c0c440b0042c0c1d03003028844c41e46480540074602c612050700d0160450061001c2d5041c12414010807031f030200c1005034040d91400302d020030458801c1c02103500003a01a183e0700d18540303440c405d1000690180c14103079a01e0380035040c0803006a03414401e1501903a0124005603c40c0407940b9111403140c81e560010060000d0040014006500803002155458460030306803500c1e62211a090709000c001c0f55502c1c0d001c00c00203100c0d00500c0030710b4040d140c00c440038110345c01200000e94109a241c815a440500301d503111500030170400b100c02c410351401d0401850118410b4a5102c000015142a040100c1c0d241e500454641040744081c858541c1e24504207521414214a10905c3c1e100505001c51440349803d24803185004001078504840042000114050f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 439247383 1250 439246133 439246169
    0x20106031e030e100c03050d0b0603040803070206100609060302030403091a0d0608031201030803040515070905010e0a0f0b090118030309062c0907020f1005010501021005041203020310 81
    0x401d12403001c0004401007001041000c0490038554408850f4550a4640030007804080d201500c00d44c0116a4058600e80c4588a8400d02e88a440185004034402d40d0f126450342001f0780e000e070038a08020310b0410a003030030a104000e500d902c1144001151042e00f00169680c0f145d040481d01c0540e25049480070101c40350003198254100030040c02c11102c0514200001d41d1240a815202c3c4240b1281c150034211800c014004156108011074000d4810702c2200c0000503280c59030704090408446200c04281059020031540d60030601c50402118200c8290250790f01f0040269203040041c000d48005600110758950f9690140040e12003414200700091000c0c1e03600d25009042c51a0780c01134134001140c184403000d1a031443c0000106400109000c89200c40c0294140104083c0013440e039170440c0f1468054901d0791209001003940c1d50601c1d203021071703c1e42c14000007902e04164058404002e514140401010441d5240b800d140109546005a0b498070390407186524170310281c10201c60003012984c05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 439248633 1250 439247383 439247423
    0x130807061b090f3807060903050306040b010816051605030c0a062d0c03020405060c0105040507150c02122407080c12040213020d09050a020f040e1c02010603 69
    0x1074012500b04683c1c004019440e0f03180344e03c00d401258025580000403019078002c000c1d05008406014904103400c034105400d544414086e540210700503070101da400000d018540c2014000c4400c9a1002c0c241203000b410100341c017400d40403425400b8820000c011407008000105c210f0b40c8100d00740c02c44101d0740c81d884841e03449031f150020440104c811030b151006e401001890281d0801c06041454400c0e481c0f04003075010440588044c00100080550801c40415540d4803034000c0d100c050b184000004451605240840c03a000d640d0304150031f180240d030100500142d2188181c1c9003540c0c103403444001e2405c8100301c54a80484440d10383e402420341c078a1001c00100b5070218610603420b07a40c0d40580e684803558941c1c428481e10420002c801d41c140300107005800c02c1080d80104a900c068010325010b00d13511140300302d6001c0081243c20380c000d080000d0643c985a11100703004d1804460400c19402d801d100c02d541c9822950044080d600c680700c0d00c0648074000c6d03010b10000d43e046880104012158182 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 439249883 1250 439248633 439248647
    0xc100302091201090b0703090c05130c031a0607240513050d0804030906030e0c0a0b1305060f1204050316140607170c2206080618130807061b 62
    0x4014091030054540d9030340364205000d80014117400c0250140c09407103154089000e01400e20007515118940701c000205601d440080c41e401038018a070020300c0e4410f45138010140d4402c02d04401c582c082b01000c3c40700b0b6584903412152500c0d88100403c450b0f960342e8122001400164185070505031a007420000005410511102e05521440a0316840d00401006580c641c2050380c3c003031300080d0b0b0203200b402054020390003800754400030741c100c40b4083c020b800010110001034202d100e07a080c01080004115010141180113807000301d59403070801109080321010fa0046800700101c0d10302d043c008c1014010240120b070f0100c407180301901c082500c54207042002062510490308544034640000351402d00c50610400101c600b00c1d004149600c03001503051032500480c03243d0314041240b40e0090000801441301400420454489110514000041040074401440141c101481d01400c204005194500101e00385a0085078561151a0382c203210340104603000038280c03000078a005030f19001d500440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 439251133 1250 439249883 439249897
    0x102071407080607080a0f090b090d031103060d030305101d0f01090905071505120f090c01021603024e0d09050d0521030405160b030403030e0c100302 66
    0xc11203a500766501d00e01ca0b41c07024210354640019044e900880d81480258120b4009a1580c036004184101c0a4480501c3c0d030200361000c0c1c1d0158081c1c45417090380c5426018180c10910185a107a0552500401140c812080c095004081641d16000030700e03060707c664006806841111504408a01059a85183c804080ea181d45880382c09000028107200030780207010b00d036903006000c0d00000703140c04030044c1c00c146200b068200f0301a0901841e006072107940c100038860080e11b240311400742000340e1030906010382884503a045420001d15241c03d2034010500c001101d5064071151424031000b584001075001100c050a8808011700e20100752910540c03000b1040821300001c001144200c0d14015500e20a00306881c01040103440b0400032171030700c144400c2d0007a0082055520070781c42e02404c0d02045540b030700d03602400c02011040c030042c81400c010001e040c880f8007130f99018460071706030800c1c0680402440202003584842c0040304140b0b041c40040d4890f00f001d46030b01c09600c00c240d0041c01a400c00c3d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 439252383 1250 439251133 439251173
    0x1180812060a050105091e1507020f0901050603180a080a050d1d101112010f03030e090408041e3804030f0210090e070903021003110406050912010207 66
    0x4003103580c82c41c00d240282e0480e00c1c161038080c42c2c142803105021400c0c0900500388141c802c01441c002494540105c841066000414a240c0d0754003240304004088240c50380d0240036000400051003540c0700c03030003102d03000b140052901ea15019000344141c83c0c072482e80390080406402150310351031f490700400070300a0314100f41020b0100d114481846e203940e4a10741c0e840103031540000c0d802d2440e0b076100e0303100d24420718428008519003003015441100300c29082e4045817020322094801c04c2415404000c15014030811200760b202400d00340c070384400c00e00a80c060315610001c0076842808031089240c07000014480c00004440200703ea09070320324401e04120f88414000c210001610b001010003080b20141e036070200c2c41610030700060b02481780071036000d90b5140c01d0010b0b262000c540210a01c0d10244201800d60795204000e00790f1041c801410496245503040c54244840c0f080f41c2082c500c240d40503100c09181180c0c55407611070002e078100c1c48c0000c200c405944002044002e001c0b0b64548681030314850 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 439253633 1250 439252383 439252417
    0x1b06080702011d1011040f0b090108070c02030604110612010e070e010309050d270b071203090209040b0a09080301080105060315010609120611030a0f0509010b03070314011808 77
    0x6a0902d455241203060402d910750003051a80300610f0443e8030417150400c00301a02414503842e10504400c03c0c429802904000c640071640c045207681c071050341c60384074001d4a0042090302d0f2030307400b0903585c0c2c40181004100081800c0da219072901c0d500180d40ca068003081440001d540e45000c40d0024041c2502e10000103148074220341d4031540a4050b1001d50340d8004000d21000b02030003800c840400600c02ca00004005448649808840030400312015050190040380e454006281c0384c454030100703801311401d250500d9046005a40c803c8101ca902c207402c00340c0040f00380c0c1d80f1000240280619407004048201c048000300c0ca00d070055100301e01ca041c054040755020780c0c02c0c03220603070042424030482000940d1500140854910030784100320242c4a0000454220703000c0306856030795007040b00d4002000341d40700070700d401c06004c034000c2c030303401507400b0000b001445000c01c0440d48501c01e0b400060b02185e94500c0703200540c03000354000e030141c0b0000d05d0040d2a013813203490119026031062090040c8074480b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 439254883 1250 439253633 439253651
    0x4060f0912030c0516080306041b09050103140c07060e120408150717010909050c0607121403070c0611040801090f0b010e060a15020a080406170c030c09010c1b0608070201 75
    0x4e08212140b01200030080e9010401e143d5818526170b000401154015484141199040303840400405829945890b00701845007010001030445003070703000c4d41160684c4081407040c40411403044903202c50300008085821800001043c0c98034143c5100c86080b110006000100c8540210714610010500804510307d91038035041207400d4100b4807211403407075452000401020103aa4403184480348038000f40e40c5155900400140380b900805d1013a40e080000c03480320700c0d41e142d10148846003038296091581c19810315400003031150315105002402d16903200c0000d21040c03020780540b002031030035000903c10000c1915080d554581a600112100030a4200108030020f008138554442c5101030920240c0506d0581c560044c03e007000782000c254096802c0890100742408000c0000d05080d03105c0740c104030f540400500108100400403182c8080c240240010803001001300c9104130300902e05000c1c5010742d420009003c1103204050656008103040c002051a042241c10b0b21a0206400070011100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 439256133 1250 439254883 439254887
    0x708090409240c02060a150e090a06021c2d0c180b071406040b070c08190504050a0503030304050a02010305311103011509020a0e120a06050108070308030105040504060f0912030c 78
    0x5140384084502c10b10380d801800680d05c034408e10b40d8001084000c8449038801a16060120f91201d080c06040301ca0b00c071030000d862100c83c040d14224003807464480801d0740300ca000d07030040d1001d24148a415070351036054160005208818040422400404404c555592a680e0301056400058212100c681d4141c62100880b0080b82540c4541d0700900d0000040c2d0710b0b01011502c002200a0848041c2c00034003802c62004100320203807900710b00d0b07500d64554803030805040000f0008507a10840c4207a20402c10000000e4000c200c02c800180d080c200459a51900c2d804000f42c000ba508000b0080003003003601854001d4000b50f0b42c06043d006680c0398610007411380600d4241d541034910f03862803016060342003103121601e50042046a0b010b162110409040d800018180d0f15480d44404e425802140c00000340500352040c01d00415060b0002c000c641d146075941d041c6404140700349445607940700001402d200c0c05401088000c2c0d5080d000700b000403098640308844007940c00c101000240b0700781140040c13034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 439257383 1250 439256133 439256141
    0x20103050c040b03010302130228020f0a1a1e090c0f0604060806120c0d0f0203120901080414030f0a0518100e0d14030309060a110708090409240c02060a 67
    0x10b9000309841e00d13682c2560240324518172035600451450380c1c00c00c440b0026a03044981040e0620038126146000c40361041d00901d0a400c5a0040201da04100e6880b0000782d000100c81d842e0442000d0200029074404c000c002c16030b060302149110654010702040345811001c145501e041c182114405000c0c0420400d000440c000c40c000d1002060b1641d001c94840d26186205520b400c0d21031007181c03081e0440501050310100e194108032896003010511004520781482160002d2030007901c698200302c01540020f00701c00c405070000d44270920030341303c00818541c00d00496001c000d00804c16a502c2494201c0100164010704458064200e004c6124106140c40404901040d80d2691061a5042401d0070010b0b1038500440481b001d0301c00c003500ea9151007040c005144200d01079400ba0546103010350b10724003550006640201200801c02880c00082c19110030782d05c15010660740090700309204e2620503801d81e81d0290044240011200d188034100c0d480d004010300c1d811950a480da00d4a0b068010820b403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 439258633 1250 439257383 439257389
    0x105100302010906181a1b010506030a081b0706201606030e03040e1f06021507030507050915040906230f03030f030708060f0d0f03030c050702031207020103050c04 72
    0x2104aa010046588100e14403040708059031741c2e040c14641d960080208070031160440070002603010505507038400c140c0442242108044000303020f141f6103100000e0319252007102c018919800030400307090707186800c2200d0031090400000c0b00c20300fa4903400007408130318082041000781d00d2a810244aa11004140101c50500d074a5500c1800b40c20004140e004d00f0300b10a540855110510002401e0040400c1c124024a14880813640ca5500000035410350315040d0803170340940d44008094554403641041c0140c4c084028a00011103445e070090446203807180c40f000d69441400099200900312040005204603400120204121b9070781d401d45080d5254540741140c60b0705410020860b180c01c1000d100da0700c00301c0c010217172850120b4421078251a50000d50301c16001a804a040040031700300108407080f560300854001000d01056a00c0104800b40440000d0405454032104030740e680c064070550b0180c5a00905841146420780e0500a0940144205a0000c0d040c440440d04030711f20402142c041e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 439259883 1250 439258633 439258637
    0xa051c050114011d010809030906071b080f0c010507060e0d0e0301050114031011130e0105100e09070c0302160e0a0b0607020d140a0b010b030414030c0c19032102010510030201 77
    0x1d100681c10046d01c43d90760041c20b681c0240020022409255a03017802030240a20402c84501007007c0540041c0310b251701500044281d0b0b01586020201c0c0308000b894440d00300e006d1074604e42e100402c2c501030001e40f03200300ca1980b06d8491800651074554002c0c60310282c05100f50000c10980c3e0f41c604c441046124040d801507016000641d9195100300e03190441390858280070200d03881c0c03010b441602a595501c1e0360200300c05030a108014840d92828a02442c080441480c2544810a00100082030003030701030400410302030050350304c408040c0217000060111103a140c074120501e50301c03141200b49200c11140001014501100b0722410f180070002d40d42c2043e009015800c80c0800d03030b0307100600007580305405140380c422025140000b90362000c03501c0c040d00c0380121141c2c50342001e2425180d690b0101ca041007164000340201c00c07240400085e140944007088511036800b90701c5200d601b41c81c3c0c00301c4e000980b9030004c00c0090100406d11080c003098401082d07008010075a100003030300200d04464000240 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 439261133 1250 439259883 439259927
    0xc010504060906080a090b0906182a040e10090c0806010305030f03090705040606030b0907030501050f0f150a02010204051c03020307080a2606100801030206040501050a051c05011401 80
    0x894450070b10198480d1031741c140060000c106440c1d0b82000c2030100c5285405501503810041a00e0088010f03010101986000b800a01c031080415043c035950000d5012500c00c3d0000c00311540d903500c1e08010258034440381500c10701d00741c40500d58081c010f200b90540306030281e401300142c03007800001d20322b040329004406141040c03000b00344d02c6c4c010340c8081c240c0c1e42e0034410341c0320211390342c1c2c1d840c42040004e046a8a00240d09a502e400f0311a030b008006200f40145450000104100d44543c041f2061203035040310f1503181ca01aa80010760140b01100031110003000100b41c0e400b01c1c0e60150f00400594000310340c410300a0410726800f903d41014031701d004005030400d004c0030000a040d440038054104441c1010245101e200710030308480c002421030700914500000601040f401d102404222804151030158515810b54002c6043c03441503220300c504110b400600500468404d074252811002c01d18000f0b4015030064850502609007805003512a0740240c160045941c0106071090f402910394134005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 439262383 1250 439261133 439261139
    0x405030417070e011202060c250608070801060e13020f0714190305130315090b0c13032d0b010e0c03190507050405062a1207080a170c09030c0105040609 67
    0x38000c5e10304118201e810160500144040510900c0142c2400b6401c0c6626000c03c0c0c3c001d820a03140c51502e0b0301000c01c0c03007a50400d2040340f6a00821080c1035a94904012388070204640200300c2c0300303550b240b10b8102c9502c04580603017082c0a03040105880d5010f41c1000410f01c684d0200c503501c4442400005101c00141601c10000030700810207050085c1148003a080c141d603481c0c4070b84200c03000005c956440556145400f00422401c03404003908942504412400e00d10140340503000c180c0c10380000384c208009131450315004c403103003000726004150403c2c001070485460b1614080d605020302400c40c8149a4038009210a104442507030302c2440782da41a0204402001041d00c005c14029105000704042004007082d9a2a02c200418003c1192500d120900c54060083c40302c00d190866008905d80125034841e00b10b0040c0c9060340c42550300140f1480d0b640c0982203051365408042c0f0040103260000800f040035030320b0050301030b00725044180c00b5510b065090380011901481540106400310b0030203807043c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 439263633 1250 439262383 439262399
    0xe07170a060b12100608010632070309060206070206131101020c090c070303050903090603041502090301140103030e01030e07172b1b0812070210050405030417070e01 73
    0x4581100c0c10480009949482e4540000d4561246006140d648480780a0103560041c46554000034001458141a2941401d40040401e1041d202c050500004070381c444d245c00019080618400d02c0b004400e59498000b4940503125400768420701c00940507070000542c18a001040003480b070346207012032071a02a41542c03000c003070411f19071201e41188264006141c85464020710540180c004008843c0c031400186801001da54004102d250035400c2403010108079107480042d0b0350440d910000c1d0504a40070155008000d01468040315499800c0414040d400c04e500c00100d41628020790780d14a503070f02108019015a0041c10071042240c0c80440c4c20000e0b0080190309282035407054050341e60b89904285c40403048019485000300900e4485000c0c0340c07807a00306071032406030f4402a8121002456646603c4101e010b081c18244902c1001c500040011380300348400303192a800741c0d2040ac2030b4207160030071b681d807a00103018614942c40c400c15062990000000d61408488032420001d401e40e00784900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 439264883 1250 439263633 439263677
    0x14060c0a0c0f050c0901060306080c030a021e12030301030c06030f0504020f0906010e130204050405061e04111b07140301020c100218090c0c0c044a030c070e07 70
    0xc20f0780c0314000c4401d00134203542d440800600803e2681c0d40410740324108140c1030305040090607141c0c8079502039004c0c40d00580325400509038142000003148403420780c4102007407410880c04000c003001c2c00000004070400180817030001c1540c0b11aa0200240d181003d6a002100c806a070080d51050741100e9107000380c0780070b1203056800441850107841000c20913011800504000180071030041c0c010400340100d0600d1700c14540c0c0810b003154130740281c80c0301242481c20582c0816a090086880c1c2880b00d005026000450394084014a45241c2c9000501000d94030340405001708800421002c150744d031b0524050027507410a22541010b00440c483c1583c2400003540222200c2541d9103c1d4101c2c5a99603488411262080f1031055881d0354076200d8255060900500c03112040c401d61030a9984250402c140d00400210381c60218400c2d88500088005d035004800e0800d25142c404800ca100b001c10f60011000e05011285c4504440700951100e9600c04a010201e0780c0000140c10126451850080300072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 439266133 1250 439264883 439264913
    0xc0b03180d26010e1b04091515030204051302070c030b090d0e0306073e030a090506210a0912200616050a090f1214120d0e0f070314060c0a0c 62
    0x740c00c40c60160707100c47d030005541009075900280452000100f012039603900010380e1a031924581140b90909010006050000716804001c88030b038040794070f4081218640045000d0b640040b004c501c24a40004e000e948c0c2c0340c1d440507200005214079070914103400c0c00680c0c1401014143c03a03026090981a89000340c03844071806084071480e240c04007007040d074090060401c01c41c041001441d55404410400740c0b030036407998801405610100010a50302407001203059107000d0a154900c00f80e228002080094440080003410003a1071a0714004891707008105420014482e8200c40c1c003a040600310f140d00da44040342c2c0080302410b10030342c2c4801c01c0d1141005000c10165420128040341c1c0303800903840342c054141c00c0384030b040100c400410103000303500e114851040d1801004002c492249080840113000c0c040d02001565242c1c00c3c11000301205010603610784104100321003025030b49044c80120904909400c00580c0070700004182d10204c41c0080b141203000c2034854040740700c9903585540000001403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 439267383 1250 439266133 439266181
    0x3030f0c010912020d170106090e06010210060e160804050a060b060f12180f0a0323030c0d0c050307090302060a0c0828020a0c0b03180d26010e 63
    0x41d2640b0002607070f4a6410455501950040064090010004c0c3c0381010b00f40c1c100100c07401e04001044030070b0f440506102035600c1c400203003126464240044c0d02c2e1001c1c0b07510048050f410321001003100c005040b1014450382d0501c072100e03010076028509070b9611000740c50140c00c80d0008100d10010030400d0700f04442040740904018600402c5a01c0000c003904103410805c141b5040e40f050000074902c6508403035000001c24050403000300c20f8141a5a9000100030042c10311040c24910b215403068107100001901d54800c1042e40e038a002c611403c000e5007d9181140301601d8621010f00d214410000e4070300c00c80c82c50b140c0e86407190440d020414035401c1811600c5c10010f02d000d0080004404001520a04820341008070349214a00580d40f003080390b014082007154046080d0f0310110b103130410710b0021a000b45044995075190b0303a01c0c0e203814131089074020700c4c50b00c1100300d11070009511004202c441c00002d14400081038179201141c0b2542d10078425440c03124003d10102e500242407004019100400c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 439268633 1250 439267383 439267391
    0x90803060415180c02011a06070605060103020c031206041107150906090807050c090604051504051306020406020325030f050a180807081516050d090b100305160503030f0c01 76
    0x25440e2124100d850414811502e03181c08502c0131243d024014800302c40780030f1920180e00088140414103500030074034060842a100c10100d9000c0e4000c0d81200d128101041c2666655480b411214004000c1610214042c1b890280c050b804201d40000341c5216607804201c00da11502c60360403640c00352940c040e040e6207560b41c4030f4080000a0300e000007000e5080c80352011300b4a0709025800c002020314014410f502503814030b42003100c0d0120104100c01401e030100c50019450f2641403450054295002c001014240b0004001c29541e4000020b4498000f4041d2940c0c0500c0c07441190744c1039018840c100501140d400b4081c8240b00f0701400160803100500d10384442e0940c0c0d66500880c400b6426800900b254001c060180171030034050240b1030480d000401180c00741d08011004280d080c004014410400501060f65681d00003aa00441a000e800003081c100030b0601010740071003c41540b00442d001d1186001c10245030110194203800c465009000e1424800740d480740c0c0065512000c1e854000d5507031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 439269883 1250 439268633 439268639
    0x70b0703090e0412021c020606150f070c0f0b07080a051803010507031d0601120227162c0906060d050a0209190b0304150b030f0a030909090803060415 66
    0x14103420ba481680140b9103681c10000c40c2d071020b800c010101e1801c517014001c2010110302250002a2190044802ea1301c0c441503940500384040b1900807100c00140001000500030144016008060140d4800202c9001c13001d5454170f003410766100721580107045a10500980b0500340c0504042c061a0510f055040080070487c030019085a40854002c80031079a0f03a611405024174062402000104d188010021035040c080301030884c8810b03803002031048400c142004e02c52060340051294080c0b9070980c0c0b2546007040d01711180142124200ca034001a020100c0d01e1006c2ea0b5400030300c464151603103822030b0304000c52080c440300300340083c00307582c0103a800c12140c41c0d40026845014416214540c0041c0c413558281c0c02c1010307207c220891400324031140d20302404140d51450440f50000e521400b011028600840c2402c098010043c80542c10b000c0d12401041c001d40c081010507100c0c0c0300341d40d01c0c082d8a813550106011919403420103000c1d100180002592400e103903128042c0010000c0500c2d14043e9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 439271133 1250 439269883 439269899
    0xc0c09200c07090606170109020c0f0307030e010e01140d0b0a080307060207020406050f01120207030201140903030a06061b0206090f040c11121c05060d1b03050f0c03070b070309 78
    0x70062080c01e007540d1042000b000b11060324401c501c00b400e01840d003104000251207a80503010b206010700d0071015400201c185650350104000101e01d5a07201c15251101c04030b080150100e91805043c5000ca043c8078000002980300c0e600d0560500c500055550500403c40114002098602e02e40e0f0f0300000c0300c0c034020960000420141160500ca404056a1192148140000d0300e07490b50103140100548050110307240e0708950720300b12000d54103100507102c0c0c0359810100e0162500010910b9186020b03018007106002c0840254492410380c001804010307076a44045507000d100c061720000605821a0840041c50700078000c064143c401450030385405240d200260484840d81846008141401c001d500380c02410b0203048203580d9180b00711407c2092100748207601020070902c0c82d074001d0b6103c002461540c0c07000f40201c18030350400500c1c0404e019014442c00200c082d400180d469200382620044500ea0001e96003d0320200580900600c920b04000c1040c55005820200d09101001d0700108040b2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 439272383 1250 439271133 439271137
    0x171b0409060609170c060304170d060306051003020a1a0d050f06120a110d02032b030e01061d04031b08070c05010c0c0b030c25060c0c0c0920 62
    0x3101403200014024505807026001421950069820451000303d6448001000c201102496011740e2015a20b58030b602d4010043d80086000500d08000802c000d4116196a40b1202c1030700d11581c0300304416101c4a0000c20300044e941b0009500c101c900009000d54a201c9010140003860006070034200420310704001e007920412130305101e20094280401040c0d10340814095000c83c3c510b405011100150740b10035480442e05c50b0814000c4640441d4881191010801094a0208510000740c112031005009440911440001000a042c4070454403515818400c01044419215481031400050f4426040c0554010300c00c0d018070150340100c2901d0242c05a40c140c10500c5410050340d80c0c40341e881c104011510030707003200d41080011044540025400041c41c010b0f01c1c03903400ba1686940d2034203603d074541d2044001c1c0740916a0b42502e07007905c00040e0241d0302f40d50b0f4030520040c88a000001401c642110b200c10010340700481110080190000950003240744260103464001c0c01108004c1c003001a03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 439273633 1250 439272383 439272389
    0xa0b0d0c18020904180c050910050d0f2114210a0b03070e0613140a090c08071211040b100c020307031205030f060303041508100e04240c171b04 63
    0x1500b0b4104034004211b1020241406020121560780b01410540d501410110050044a024004a0591409020f40400c0c070f036141c1c03984112039901c0000032022041d0a42d06103508507001c50f401c5202035486074614800c1d5030388a03d11464082c1041c017218800321030310f000500340d41c0e04240c3d940301a00e682c1c0c400380103420140a814504102c41d041c56410700070945a05203051000915040072414803a40b5009215000300d039044001ca0303884058280460708200660056469206000d0005603051982400d0782c0d000e8080c94031a41c03424164003d200070f5a4002100e554050603074004164079a0003408581c8e50180040c2c201ca003416140d0340e5208980b004d01e202100455008010800d6411404540c1c9a01580950180d801c003031900c1c0d04020981c03034111141003880100c0780001c0c0d00107104000b0030000e00040e00320800e1818641404a0544884051b000c5802311407500203d020500d8010782c02000c80715a100d45058010340b82503030311007102400314658451002c004c10102480c40020b070001d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 439274883 1250 439273633 439273661
    0x190f1d060c0f061f054603061104080d080c0409060605030609060109030201230904110909010f0315020901110604060605190806040b130503040b030a0b0d0c18020904 73
    0xf00d41001380000650002400513122100700c1084c0c280031980b03850f00006030343c40800c007408003a170100c030a804001a40640c0c8000582006240350740b070516502c0742c100116030191608000760b40716110b00c01102d01c81ca000c0c10b0201d174009441c02c94100d209034070499020f404248084c3c103282d2110903902c2540d00e035510100000f0f201000380015813030102c0010ba000042420150b80442c0385074000703428095240006182004041401d00c642a8048200c031500300009204018081d020340400c40749030001a1071301d019807145000825890080446007081d60b8020b080c024020081581c05c1010394800c40256040140240400250100c1005858000e03485204003182c07031420081440209001026147c480d80c014150030000340d28003041840d00182c2105a044042e502d5103103032000042075510040841c80000f03030008a42000750007a45c001c038040a418003007914014108010b003021713440c000d0012002c0740000c00c01108005181547c40d0b035001e4002d07040c0400791000800700c9000203803010b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 439276133 1250 439274883 439274893
    0xc120507050925051809090601090501060206070c080904090209070914060a05071101090e0109051006090303201204030606081203041a04051e03190f1d060c0f 70
    0x10507482d2601003a5400b0000e194118142110000202400c8580d08080c0301070004c0004d40000c403201d410a0301549200141c0420928184104002c0d40c4003130912450704a140352100100d000c92000c94028010b6105a8810780450b2103500d540304154098008a0380c0966034140240c0140c5031013500d503124511581740e6001e0130340303005440c964002d9003840103071080508006092090350044145d070740c440d42000d0b50610b0711031054011707140d11005030400008208510000100e580c1c964009074440c0131070401c620702260303a400c0255504215400300502140701c100714005121840301400b0f40b4005554221004440d041c4840d81080c0c1c043d42056035565200c0c0000e01c00c0d1002001314020700f0300d40e044500c1c554034040d01c54600804101202c61821400384000c10306010082003034030100200c0b450b52403100c142c001031b4241d4a0f8008000c2000c01d880d50410420b8a90007440d4005842200c0d846204034000c0d8034003031401c3d100c800700c44645c0c44002402001c880800422100c1c1c4100c000c180204 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 439277383 1250 439276133 439276139
    0x3010512010b0d124b02030d231306060501020d0509040c020c1c051b0105120711010f0c0e0a030213020d060b0d020a09091107031b020301090b060a080703110d0c120507 74
    0x4174200c20030300300640c8021809481804181d40c008111594180411030004969a400c102110014041c3c10304400005400c000d01c03a08000807a00d900e81903109240401501f0341e04e50040e41c0354000b030072000c00401c4080c0110780481c2441c0e000300901c0f400600c16910008000d82c0050300f0111032508045411305081c0c09541088020000c44070380103900d800440528080b80b0008013648181c1951203101c113610000300d02030b80c0c006c180b00750300404028000d00104a0110401c401010001c0b035040000300200304644c40c0e801e05c48103a000703a03500a0880a600743c0d507214201d02a600920105440710341c2c0c2c0c03000180300c640e01c00103420600305210303000d84d03156100c0c81c0c02018006140c004803a8945004103404107a15400d0480d00d0041d4181092440a8904059000c10719a03185000c3d4055082a941c00100018004010b228000032120680e03a1619a12010350358601404001c0203590014115905454130010206101d842540e94403201d58490710090b4189812810480385540041024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 439278633 1250 439277383 439277477
    0x209012003030a0c080f0606070203280209070509010c0813050a0e0a1512021009090f050708130515040c0b04060302031b0c0319030219020303010512010b0d12 70
    0x80860002140b60005d02420300b18000380300e107800500110721030f1304000703409001c5480601000710b400d000f40c0c000f58040f50384e02d00c100c40b1260f81d0381400c03071113800413400144045020f0700c10346d24100302c180d4440c49040340964034100f0300d5111440781d04044446200c0024103030359551184c1c010307040d0420110745500300360300001c003902c2408801019852402d0001d0200c440d05414401c4110340403181e0400850100c0020740d041452a04100c0c02c044c28001200440c18058000a0184595070340703100080d560800c445580c010000d0b0000c00300d8100d1b0703070849200020126440e80050048000d807041aa0720110308141c0d502c2640140c003c00d401004110ba0b25020080d1180e004010340c000760b10381002d0308a596240e2040f503248144018904081d601c1443c40303681990071400c0313090503e10b02c202d150340020b035a170307002485820302ca0740010390a903079800c0040c0146046a10040c000c01ca220030150346080faa80318401da050100000e0504c0c0d0711003a00001401000e1a0550703c284a030801d840c856 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 439279883 1250 439278633 439278641
    0x31c0207050c040e0a03050f09040617070801020a0c08030c0c0a050709060e04030f03150f120b24010528080f060a062a0206030109020301050a0f180209012003030a 72
    0x2c00344034a01c0c01120240d03060020a0104c50320b81e141c40c00c2030f902c8521481e01e401a0095210382c641042c03501380d02180c0c052001c0d22070742200d0040800ca034083c1d595140406c0c01d030b22a0b036a110000800c1d40881d0400039000344003540c2c01942d817210382401c03c504c0740c160514001180030309560381c1d07114030030401070700b0303820f100340400b4003031010304042ca614041d200039111110b0002e064041503a90075010070b09120800d4150301500d120010074040d241e44190180919203515000c0e84e4000030321002c1081c10b00c0d402c401100201071701c40e0080744c0848110054581ea0040301d42d01c1e0600005240e80c62270100d041e000710041c890940c40b18241402d00d00c1240403910f0340105918043c00709010b081c00a07540200072010a00641e090011000510480c44d450032005120020b401500120012440e4511034011f103060b1101503800c0d51030585d480b844200354000710300c500c80000c500036805c1ca0303d84490342c0050015600c1818280d2401c109040010b00381620a04588a5500040207107d658010740c0070f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 439281133 1250 439279883 439279903
    0x405040b06091302010512040516030305030702070602010b0a050418080f1306020a0b0a200c0706020d17040f03050c0f0109060c0207050a0b16080c0a05010b0a030f020909031c020705 80
    0x10984003d40e481e9002a1083c403810f003200d281c84a01c00001000c2040811070010306110400f40d42d0900303070f07403403a01070f00c41c1e0002e440c00400741c081d40d0b0001c600113105129008140000500c0a8500742c0740c00d0500000304200903401c03413411005040350000c110240010301c2030781c10411006a88070502a245030f6a110319410200440d0003013861440030800f084e0055411030032406000074100035011078400803003940000d030203068202060764201440003107072504c12a50301e902500c10410303121a040f2110003034556044007041c401c401060200c0d110842d01c0199601c07900309940340c01e0000c40c45514050303c102d01c06103181c0d11181c0346400c0060034064010401100c0c0000d0000d136081000150303002045014100000c0da001c21040003800821104118064200001c0f03a0f980104215080e1610140d920940f00c66081241e00042800c10a206904a030740050603220110129820000c4a01028084015620007408140b0034486130303408a0f03613000e0011000603695812441c03c2410320f0700b410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 439282383 1250 439281133 439281151
    0x509010905090c090933090f070801150918050402030c040608071202150a090f1211120709020a0201020a080109050c040b0d150e06130614060f04050405040b0609 71
    0x1900780003800c00c5103016504241c0c0304540200051b03961a040c0f101070852105104d15071200003454106404c0c0301143c0400d42401602c001c40903a8804140c80442c0034207941142c0086c154030b00400144014982302c006541c010300d8520542541c80d0010740408843c40e030706c00d2031644d136842840300710320b0f00304004c407136042c8195824025107103040c6400342c84840600c03c00c0040c0c4c1402c8180e20840d80d48240d0880c0707040380b4454094507078000c0480103200c41c0c9280211b640d070070180d0502107681c1040d440c1116802c0c1e80b20708241014000482841a02d09004074101316512a40e80d0204021f41e450020300f4030106070341cbc00141c6030401d40710010031103581a0f101100303035481c040600290015103001c460546604040c2e1a5031540d561085c40c008041045085200c41c03c58180484d010a1548008c1d00541c4104c0f01c000349000000982da007140d15500c40c41d401507564101c07035405400c069000c0d08980088200701420300351303154085410703100c007114204d400707024040030401580351a01c3c905801107401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 439283633 1250 439282383 439282399
    0xb030105090d0e03070b0d060312020606130b0607050703111320090d0c090c0806030d0c1202100609061d09120d27030f0f080a0e01020c0303070509010905 68
    0x1500e405031581c0b90308000104000e007411500c0102c1d24104800c000514142c500c107555854032400000c01021107010464010785030508500d03181d0b1000a5150041c040280104054065449640e008005003800d40d40c01410600200000c21024051034004501581d881d9040f10f0480701000761260f02c038050240d030766141c416202c0d91150030080580f042c41c03150008613900e0f90100e00090b21400f00c1000140307d102a5800810950156002400800c659882d00c3c5007940710300040644407503075040b0303010004001a4220b008100803151824114420340150744070001c105083d14143e800c9500841d02e016154a010440581800d08405254a0184404c00c050402c1c441c565210003241030302c4640b2040218190090340e10070f038881000d104c240a43e611911201e080c0007515030b030340300b0019004160b141c4c807035020942c007980c4280340d05074a43c0d071450480c0d9140030a00d00241500c081411071fa42d428005450000c00800045004005584855413507a824000060503004143c10070707401080b40d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 439284883 1250 439283633 439283641
    0x610090317030702031c0606020d0e1c140304091a0306010305031215040e0d120204081510080708060a0c05091309021503280e060402010c0c1e090b030105 68
    0x3222811060702403403140d11640d98441c0642285103006445003038640891080243c010000d00d0350201c0106c1d10030f5029036a4103001d040c4180c441e91000500e145c0c0200c0800c3c80108112a064103000c10140304a009003100d404079002c4609d950030035040015507541d9114140d60389904001c4510107800110001d000560543c1d0f540d03074480c003c010034804001001000b18242030700450500045c6100a842040303e81210303a1000e6403280c81c00c2000780400c114585020311144c1c18000c0f94155203070540100b03884900b050a00d11255030062180319407072140c0c0300c003140d054824080c0c0e2000300601c1008101d54109100440c00b01ca8249003650140801046040516282c1c051040100301d244400061000d404c4e0010400b456840200c0310787c406000420004003000411094019481070300f0a03460300e0f410b90304843c2c01c0303400f0181d0450281c1d1242c80000d00540c41038911044052042c100705444954815485074110855042500940c403d29014064003840744903901c0402d82c100c00070f000c6c0d800c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 439286133 1250 439284883 439284893
    0x1060f0509060a061d0301021804051e071b1a1b120402010c021906030204080f03070203070b030c13080604030305071805130e25052d01110607030506100903 69
    0xb4244920000d01402d201e41c1c15840040c9034600418481c042c1c025503271103003c50a2017000054000c04544218030b41008034a042851003440440520041c03143d602d65180c80909645c6021000d01022707090b61580500310004250403603014803503948611a4801e42009034544a100f01131142031342292a0600550a9100d002400240c21540a01345a000e55105002045464005203511003c1c02604c0000107012585a0b00402c00c0329201c109071840e10300b668000b282c0b81d21600320040e41c540d0100d4000d0142e030003040001e64115100c070341603c0c986005043c01e404e5107101d950000341e05401107420071040c16018011035034014582d04c2c0400292212060080302064540a01c078000c120403107501d0011030150b8001d9801c45000380840c0d00b00800d4501031803c21100c3e0840c220710f09602c201c0003e4904140e064044513250201450b802c501891640c1040d20212600050400c002c2203516508003200f400041c1c022480c5130340c003285914200341400000c40c06200070740d04000f038041081010031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 439287383 1250 439286133 439286149
    0x807020f1210110904140403020d020f03300c03040c0b04031a07030e1f15050603070323040605060a05120a0b040623010602010c020c0105041503060f0801060f050906 73
    0xb03080307070002d0780000704142c0640c00c0c00b441c00915041850180c116402450841c900c40c420f0b4800c3d42143d000490f00481240c55074641041c0300c4207540280203080107140e401c1c1c1c99240c030620010720001410220340e0f00307540c51082541d0406144000000344028400f04101c140003070691000010300d0300d071456030784002c8103031a004034940e294107160100380c052340b107508890305907000c240446000728200c1c3d00c11400c000c100e050301241c00c1d14084604030009284496502140c034028455800d41d03039910000d6010b0b02d10241e04400c0a903001000441800700142c0c0d00d405036000340d00c0045d1524001040c0b000003c201c6c1c200d5846202407080310445100700040f40409258002da8030145078a0b00d1404001400e440c0c2a140000d42180d088200003840044d40e05049400e01e5000b0711403004d00b0170059854190304020203002071010002489500c24813620740d40c24640c3da1030006603069540d2080b84c080d1801d07821000c4565190b84c0200940564025000042c102c102c407005001c2c181440015096 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 439288633 1250 439287383 439287403
    0x15090504180b25030204080c09011d071e090617040206090d050708100e060a060e1303110105070e0f040b0f150403120203041d070818010b0303070807020f12 69
    0x94040003001948405010300b400840f4800020380000e09801c01c800a0080c0d0400c0c0211204e501c20500001800c1c501a50118100c1e003d4030403a1001c400098000c03c284c030380050000060000060800f1180340b00400b1208000010341da48a20690900500404190285156084080c9079100f0310000d45d0340c820483d140c8600407103104885007484e142c01c504156441d0710401c4180140c841861002c080ba03002201031001c0442664515a9200d080b4022500a40141d4005160140000b4510b103990301041030b0190003810401c445c000110961401d40740c0403290301c8005404400d4940044c01c000d414060700c288116030234812003c030345000c2038402c18071100d11489580d01c03102039040403080000b1074010f10740150041404525012010b0740d668460b01c80c01c440c003101e880400b8455403030282c0f45030181613141d44404184d101e5103940c3c881c45040d03050b00030071950307103400e03107581a0340410082460718800c0d2080b40d2240c290b401082a00141c240d1024010107281c40e15100f60180404c0035000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 439289883 1250 439288633 439288643
    0x30c020d1d030102040305010f060503030703020703060c1e0c05070b0f0304060c1b11090703050c090f0a050d050106030b16050a0c08040f0308030603070519051c08041509050418 78
    0x60a1000c00c690490070200c84880d07a01548005404010b0100c10741014001c002084020701c10165550145070707030392088840140058001038000e0001030b400f600140c0d918440f5181159072004003104607641c000201111101042183c10200c0c2017007400d000c40c00c000c0c07902a0f084c60408039840501400d84c480117000404080da0352012a40550040000342400c040300480d0b941d0800d0140342000d240341c1c0c1c0d9580c8900c1400c42000182a543c828040c0341c2c4120180d0305800c1c20140c001042c42800030803440321031791040300158081442c3c2c40388054180101e001d0000460b0305465400d0040410001414400001d8803200000c1075484c4c0000c11140e0400c101c0c0740181c103049050518550f035008580050901001c0c1000000900041502643c01034a086090315501070795007040110000a01143c855130401c000380c03c12843c984101e83d5400c103001d44035064a410107641d41da101c154401e41280e01d051007030700004511603a10a440d00041c2c0401d40d0b04100440a6200c07810076070070b1641000706 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 439291133 1250 439289883 439289897
    0x20301210507031a1f051e0d050d050703030f0507090303080a06080102130501020115030b0c0702030a0f051e0606090117010e0d09140402071104050408210f010501030c020d 76
    0x80003000c102000081d43c21102c403810300f844514404013104002d03180306210a41507030f4075080c242c07150504441210001004889540c00c0000c120070320070b0031010a40e078040310f0b007070500c000300380c082c80072011001d82d0b80e541a50f51b00c060720b4054220340d03142e102c124841d40750a080050954100500c40140d0790036052412180d41d40c100c0b040050151a004104554004130380204030081c1c5105400580d10300760020f001503901c0781c4070342400d62800d00c809401c0214200104520680302e5004015080c0060b007178030009039103512240f140940c8508125000d038495558a00052500f40b0205d8114104a019048904054000a000300010f0040d4940c41ca00103201c1500100d0941c00303000510b035100300b0740b10305251041c000f078520089445441d888144c0540c0580c06031801d8801c035030300300303078080607042103102550103110007403200400c2180c0502e8100b1003084104103210002040c4500703554110528a0400301548c0ca061060344007505040c2081043d01586030081f50143c20001c40b490018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 439292383 1250 439291133 439291199
    0xe010b090703391d0d02010f090b03010e040b060604080307080a1116080f0106030215070215032d0f04020d0206130306020c0f07080d0f0507120e01080a020301 70
    0x95200c509561207090000c0c030b41c0070348641c404100d004030f94110703180381c9542c01c0d9208007542005012500c10380203540b01c0803c5194074019030080c8040d085c582441d01c0c040704450b484940507000c40d84203801001c00d00c41c24800300410851181180ba81c8100300361007441c105460140403d9503030082d82c03801800c10101158010070140b040303014010300d9807803c0c2101c41c02c0669200f07210041d4514040c1c2d0016000d0320540701b0304600140245030880364050841d00c24038040c5c10000102d42c10409040340d02507900884411005403030b10141d8003c1066450380000d40e0b424580342c4440300c000c0d0b114a090385d1103002c2040007114444030303441d90160301912101d0f100507062000075a01e2003002101c0001666180c1e02109003c000e0b07020f016400003280888908200c0004910f644901c1c0740306d400c2c130350b0f40f100b1401503201d84201124203c040705420494140701d09551660905150303581103034001100104c2c881c13407a6070f106079096001295100f0852a41d410440c030b04d4840101c002c900c0300c034040da4060507 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 439293633 1250 439292383 439292411
    0x61809020c0a061a04091401061403151b0f040e0f010e0a0515120a020f180115050d06090b1305150424030506010501021c050306011101020d1a01030e010b090703 71
    0x1d100c0e0390040042101501c61f14000e00010200c00c03400c40a50320384403002c03401800e966822000c038100100102240c180700085a030751150300920f2200340081c405404c0395560f6981d0040e100560b1102c10041c1ca507410801600d10918004100260500b0404010083c42200b20115904030040b0800460741c1c1e80d90701241845482c6001c080350b0400c2c54504024540f840c0450049000d47c42101c206245050580420007840945240c000010140d8401004043ca071455240281c0e002d9007000c3c1d0411110312030940803692070743d101c090629101c2e45005028600003200090224800707004018074240007040618040d012902c8034080c0c0d5503075521070300c3c0d05124a05000e9400d2008045800300e6220310309503803a4602803080030b016109000c0110300c4100c90510000340c0c001140e95060442c1e40310001100c42d038002c0b41142c20955402c211889034604c19014003802007409040c41e0011048440004048484150a00106074500618212250380711003401d86c01c1760980c9004600401c4c1c003100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 439294883 1250 439293633 439293671
    0x190918090302010e070f0f0506031501030902120307060f050c07050c060a03110f070b0f07020a061a180709050a030c151119020414061f0513061809020c0a06 69
    0x4200102c1c0304840d0f0000c6c1416140b4445003e07078030040f0f0800100c6039a50248105070106444500140201480a1000d5446a401401502c0c0000d10400240500c01e40b81803c6a019081c20744400d500c2d61401203480d9100d000e41034210142400880c640903040d2121500d4244100c14241309038030000310f8a401c24840e07007282c80003944c0c400c5041d070b0fa8107070b020304138050f6449448201c0310b19014800213a100401400c82c0d5106243d17640241680100d150307215070040c02d503010803100c0302c8500d12642c000c50b150100601d0209000b00740c1c401407414032490113002c401035580101c0c4903030040e0000744002410000071400b183d009086d41c155030785080c0800e070b07000c281c891401c0f003071403190100001e4444028468030781c016000b0380342002880000708420303c410360112151500486841c410f0407030604030b94001c10500c2c1e0b061404d5810a95000c46195000000b644001c002812132000c1ea41c000130211350395001440c04840c114a050703440401e2036280c80074a0f1000e4200780ea1500b083c4150b107198a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 439296133 1250 439294883 439294901
    0x50102090a1706010605070807081e03130b01050f01020d050f0405100c1b030f0f021807031e05010f0b0d0b0d0b07032f0f0c07080319091809030201 65
    0x90100381c203032110001052000c01400c03001c0c95204420000910034065012540000d4011144030300c0e0150640703960aa5a105410081004001c400185401d440160286003c0e1148400308004200c207800d154107000c00c1a00114030030700c203401000c203c2d80e07000940c503291100380b802c2c15a251842031a4002141c00707a07900c0180c00c003000c02c4040503980d500c400e141101600c59141e00d40c4010251144204117091804000c201c010b1010014010450106404030b0131440104030507800d940c491000a1000010742d070f07140103e83c0345d0b41c0c01d40e05500f100052506601c410142009035600d0038885d407401c94111301c581c3c0055040080d54243d404040e4014800d044400381c2514007840c0d0354504070085a9040303d036a00002d142c02900303903203460a07401204150051101d184801c020002034000c2581c040401405248030400020104c00b00070302040c80200f002078041c40e280d0345841306044000040300d814104000341200c09208a0381440f14842d48000507a00005485a5928050f40103101d01e40c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 439297383 1250 439296133 439296139
    0x319090302060a020609060f0c040b0d022b11090a060c050f010c0206160c02010e040b010e0307090605190e070e060f1605010c0201021317030909010305030909130206030402040905010209 82
    0x190f000e01d882c1d000130b885405110810300b142c800365160012020124001d40f880204444200f0003005002c01810242c25020203a41d001441c00130b054401c2443e1901c40043e40c030010741e50b921030b080521614415032400c42e8201c1c1d0304038944804000002c10f01f203001d004580c140004030724030350180041084070201182c080d600130440d00280a10207580d0b607004580c620039036000d034058040300d00d100740b000900705035060b12180f9401c041e00c804c103c080c01c141d001040c10021303002c04240d02990200510b03002040310303040c001945400d04061201800021000410a1280c10000c20001500451256004803640340c50340724ac00071710300046c00c10300c0b9524401f0807508001c50044252104c111a03610345601c01d0000300603140c810742059082c2e0250007d01c4580300c0010800f00440c0300450282840440008252480e2020030030000300c190303c0c01e8000351030980c070200da04240fa0400400b040c0c0c03c466040341c2c000c50100c0b81e900041c0d06110041c0700a025980b80c2c0e03c1641084000d4040e030703101da0300003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 439298633 1250 439297383 439297387
    0x10e101704140f0a0c12050d032004030308100501050306150a03112107080907170106090c080a0b06030402061b0f060c0a080f090316030e030a080c0f0f031909030206 73
    0x18a80ca0380e1304e8030a0881900d201c0c078000c000041c070000000d228103045500070064041c1c1c110300d460940041100000c4050000311218840243c081044010000355100c0d03154201142403001e21008a0000c50b00044d0520a0400910800350389142c440104102200040c55994049100c114040c1540308081507940c072000c5070382c0c440301c1d02039004a880111a40740e125030982e1000d60450308003000341c0e0fa4201e242c006503010f00c1a0090702c5a4081221180c0e00081230140c2d413110048100e9442c070130000c0000b84180140503010441e406100106007040300c0950860810341c001803500d104260034410b4002c00c20f000c2800041080c064000390007841004d0700c1d558a800203091206a00842c000d8000a02010010701b9880f2402151030141d6826001036007408401070442c000312201c400c050b400c1c4600c1c0d010800c038559003040307002c180b540714602090704c6080c030f0100ea910700105052042a240c12070314140d00c040000000b0b0312040180340258040d86034070b1020540e6040b0150300065004240 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 439299883 1250 439298633 439298653
    0x1060e01080a1e17282003041502010e190314032706010512071d06031204090b1e0108040b100513021b060f040209180a11010e10170414 60
    0x1004c0141510180003e000800940a00c51202c0d84507807141400010500d81c11407003044840c80440c9551248201c0200c03031509458400202c0a604854107800050303444401c401990041400301c00303642010f02c050560140c00e5554064143e5030400d483c0342c8005070220006901d6400c506084064018010407880740700c03a401e8a0f00d031a5502400351a0154850b01c0c54070103100d9000980300125000700c5186115000c03498122044480090400c41e850710851990040340c030035a03c010070081480390800209280c012091100c80950491460382d0240c0a9101100c281d800100c0582d006512a801c1314180d0759040310b4001001e41508030640001c1e44464100c4038514a43c02000380c0f607840100da6003601a440c13400341e55401b044070200f01c1a02c40b00c0c0454018204003032050f8006034068901c8004403061000c15250620400c41a284190fa0070502c0d1581d5811810b94844011b050750107100e600c1c030081c4050401c40c01000b1800718845c2600025061082c012400b03250003204000356405112 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 439301133 1250 439299883 439299923
    0x20a0909020d0b0102070518150301021201121106030408030f0604021905090a050301050903220504051906080c100c02040209030303040b010f050402040513020c010b1504030501060e01080a1e 84
    0x50903d201c18054031801101003140d1400d0503001107802009032175101640d44001114401d10f0303601400b103030190740a001000880c0c000d03010b8240a8600f4400c8200e031302d02a0b04100a80c0c51391017042a00404080003840f010448150440b40d01c48160300309250345031281c0300070030000d20440d10038442c0030303041c490705209159014006140a032412500e0891054640c0201400c03510182c5041200794000c01814a000b540000701d0711141d281301e898028415514804a020303076504075035035507502180b90f51009100b411403007184084c1100400070140031005c0c0c40030134490134258030000e0030700000180c10000c541d00c3e0380440d2030390040601641d8481c00d00e490700080752802801070801941c1c0782d40011643e82485c0c429601207510041070718a45c03200300d5030310100962010b09c04006c55500c502821400d40c481074403007201c0290501c84540c1d075a00e0350800c0c6003120050b8004969031103c10300100054074001500780447c0d40c01074040b07401c601000140c01904255940e0060090350790405503d030001c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 439302383 1250 439301133 439301141
    0x1817150c12010504060e1303110307111011120c0f010212060a06080c03040f05030d0504080a03060e0402091609090e0d03050c0a080a0c03110d1b0804080a03020a0909020d 75
    0x480540c40c440c10b90300c8204000c00d644450041c0b10700385421100280c460b250301d11904400c40c0c06410100e4200141082050556100d4441074501c0354076000710b290f8504100788a5110441d01d403504400c0140006029610750484000c0000c40e2078000c5841f81d070041c01030100c6459614601c00866072891081d5200c003001c01c0840d1f820b4403c10040b4000543c1c2c50261108074403503244c0b200c1c214a10743d00d0b95104000d42c07162140a80301032109010400d6059102d10031140185d00403c41140c5034058003400406541c8250000c0411125020038800103840f854000f07134002c1003003804812070095044044480e900d40d50b102e0041581090200c040d1310001282c0c90501d901c2543d428880c6a8401007020880d100352020070001130301420025001740740e43c1d88640340111840c900030440f24000c0c1c1c0c401c0c41641122100c0390140b951005000d046007c000805c0f0300712141402c00030140d24050721012998000c1d078030701e00e06141d000192803040a114040d020058100064115220b030908001003001f8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 439303633 1250 439302383 439302397
    0x60807060813080f1602040e0c040b3003070b01030c06030c0512070e120a140f07180b0d02100c060f180f020418120f1817150c 56
    0xc00d00e070780089466010840900c0c44116001030206140a22a01c1c80c40c00d2540009413255002c04203c00010059607030707005004400d4080c000524950130380b9010402228881c450f070500c1890314509071101e29418042c0b0303035066221010319441151310384032035030708620a18000a05400d00b1000220070000308403145015502195402c02c41454900b105451034800d40b08444070803141d030000124128400c0c6000030340709001034110321100d5035440146180105d02c0804640c8415210500c40131410200010842001e1580003004040d241c00409490407808804403203001b0b40b01c10418400f03442d001923203006e107a8040c0c18101640c444402c003e00d45e120800041350340500303002035090201103034091b24004011024000d41260b09a946c0c2031a10030704944226000360300d800e0011040840300c41c00000d00c031300410389070f4980c9001010051800d416103a80c0c0b82400307400c00c40c200e1070701c0c0d28181900a27108241300b40811100000040f81c5800f59004007543e105405c9070400120042d90000303000c0d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 439304883 1250 439303633 439303637
    0x80d09030f030b0103020327100e01362006030103030e04180803073902090702010c0509040518101b020a0506041101050705010e01060e22120e0406080706 68
    0x940c10f800004509a120030741e40d0340540c00c1850282c05e10695911000080c00101000704c1b40700811000100094400d41e00d00007426954502a02e481128505032080c1414402d0035503a600c19000d40408414080f207081c05003905188801e00111044166111004e0b2080140060b85a607960700c0c00a11010541c8025402a400c00d1550841d4051541c018682e00f5800782107541181d40d4003408a50400010012040d59140b90612110610000c200380205a00020340f4041c40c02403401881028440a03002e0702c1168907103c0c000070555482010b0354840700045801140c99100c006900c25416102c840030a40e5018404203e42002c03481c0d40880c10710181c0c40c215481940d007909060782c0383c000442000d8040d400007400600000d484000102031210141415400c0400c95280c407804c540c03420340480c12a0703540d0342c028422003d501e41076a030700545501c0d103034603082851500424500308000d00107106003c41c440a00c0d8250013200d40c01a03546000e04100103040e550a00ca070b660b03070411311880300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 439306133 1250 439304883 439304891
    0x507080601180209010c03050c010603170a1e05031f2601060503030405013e0609011d030706090201031e232e030204050108061602030c07090504080d09030f03 70
    0x88000c0a030f00130340e105108142c41d8124114491348055490f6406000c03028141d540e5441d012001409040c0c003850741404151000351030f40591140a013085034004070002600c0480c2612072006940720041700c1e4480301c40d090003440343e03440d180d200f4007100c0e2540081c0d4000b1050fa81001c120005400550700321841c00b8001e00181c0c0c0e80ea024140c9900c628002c260010b00b01c6070071500b03180c280c24040302c40710b03002e0b0b00c420040364480c1111000c001e1100e000c0b08801e0b00020180074405009016000e401d10172080c103036080d28041079000d9aa0b00c11201c00802e41c0380c0307c3ea90403081d603020f40e0003003070400e6802c440928a080401c0139040200040043c240d04030982c40c607101490000014010701c1154400c46010000300240c61311016000ca400388000a8238420002100680721030044034000c03e10700d00104050305110f424410180d04030708c0303d9011503105000d901c6981c1800210a811a070708290b0004582d02e03a8184200d41e8452481803450160a009203030041513845000b000311885240d80401c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 439307383 1250 439306133 439306169
    0x50a1e11100506061213050706120e010515011808070b0703180b09060d0b060a080601030c0212190c20010206070309020a030206091201060806012d0e06010207030507080601 76
    0xa007200d0b026030354284c201905100ca443c000441c005842e030061010704040400c101b5030b907504c42ca444120f412401c0041ca441c1e0018103080654025036a22485103c020311142c600900c072040301c0455403101c070781000090000d01c8009101c0b45100d0010303003004c4007074a42e455201d0a040c606075018034402c0b070014031080030001041014142c11815103501c26101c1c0d181c6003140b400c000c0140c01511104040503616418490b1944d50340006007501c203010b442d031004c9482c251001404845004000400307542248400714131104880c01181c09405180c80039040b07000980008541444a4540003020031000f01702e8055801182c140100740810240d080303403016a42d0fa00d0440a403014442d0007508404130785014001031800c580549503030307440544031004031920400154251000c0b54004841604264010304c405072521007940c007402003440e544000003c45c040411201c000310701c2245040f0841c0401320300b541c1c2c070901001340290f80203002c079041d451300c0301501515a0070a224040c0040d4000a1072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 439308633 1250 439307383 439307413
    0xf0210021e030c0304050111030c010213050a0e0405060a0e0a0c120b0c0406020327090f0115140403020d0314030c090906010c0206090f04061a03010311030616050a1e11 74
    0x42d500083d40714080c5040c94079020054512005080300d040340d80c081070082c0c1c80c1d00c180900c09001d00c41d40454041c8403103841c0c070701400791008041d0400c0d01e40c2d021540810005c90380000c0c034950450900040003c59a441202c1c0c641400921040217000d620950400211640d651b00350112030360040510042a44989580f90300301d100d0347c414030000da0010b114281c8104281082845400f58070aa4140046111000551841000c880f450601036140300103210b25941d180c0b44c2000000d41d410401d5004510243c40101d80c012840000e1040918988035403c145c419881140090a44684a9180d04210315458503940080c081e140c0182c1030344001502070340c403545c1c60216035a0050010391801041100307200010103d03141c0a078103c0d032240800250704040e01c13154214880c4040801c4d84a50552500742c142004c6162414401c0d030140e014001080c00b5210000184102410b0081e51401e0007801541c01e4251101c1c0b240c01d0a0140025502d4240c1000c40409400625000d40e2084060700d2a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 439309883 1250 439308633 439308637
    0x60105010e010909050411040e01020c100b1509040f14091b1f03110f0a02100204030803010b0a030b061801020f070602100b041404060c1205040f020d0f0210021e03 72
    0xd15001440002c3c04000840c1264070681d005800782d40f14410310918407001c0740598440f840a0400342e0340c0007403c83c05000c4181305a95000d4aa07440074880c8840721070009440b00c041e901c1041d00703950005030126040c0e0395a401002202c4031940c0c10700c514141c030f02044030350240c201c9000c8518068080f00e0203503c908440f01621241006002040e000d040440c80189000c400e031414041c1035440c007040705e1295802002d4403448000c403059554603045030304000d040a0040158092150040c001400001e00310429a810349521038030751622400210000c90140c0b820808142d0031010010781c00e5a000000c81c0010011242a003c03142d521003195040c0350341d5017103440350000581040114815215098120001c011030041c400300e580c40d64007111020b244416142264843d58034a2000103068000d2074083c8084402c810030401440d054603128002d442d0540002c3c0b00342d0744508524104030540300300c1f140e105d801a00c00152103040c51030195036208007051411a802000785491072403000042 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 439311133 1250 439309883 439309907
    0x5090613050d0c11190816030f11060403060608010506120f0c0108060f091819030e0607080f0a020609010e07060212031015021606090e0f060316060c0506010501 71
    0x401445207081d44001114030350043d80301111000d0000711100510b94503405d40b2014005424041e03503c2514000f40d643c5040e51098179059654110f41c41000480d05c07a040108005421002000368010b420300001c900d40b1540d040280400e251490110700800154400e51252209a48a1521405001506075aa11800c400f0541e540c4401209400d55110f503c00c1504000040d01c02c00804c03440d07000244007030108036011a200c4030101d41d841c4070020304100800682580c102090311a840c1a100209544010107207680510710020381c1c4400c002c2000119054289081c11454446015040003925840700307447e80516903082c1700d040030341c2d00c1000c501b11003207500d207030020b1940e81d840302e512020641006141102c1090712240c0000c0600301c5101c40c400d50011a0702400108601048140403a260b64001000300325030064180f202010400f48590880650003160705240c0c2c40130000f80c601003800c00b82c0c0308015000c0000040c1a030f00301c1c080e0b06c2801e2144060311116a00c40004480d404d015203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 439312383 1250 439311133 439311143
    0x403120c0f0f0501110f37180b1c1d070e0606070804080d0930020a0b0c0a0309152003040302100503010512060132030601030605090613 60
    0x407541d40040c480003101410548240c001081888003c0c9030700c0320300c0c3c100400660715140006810030b105143c0b04d12103080381041d001c10015010810b2050301607100941958011b01040001080315000172481d103100800800c003905a9035440c6200100d008001b1640b410b0b800c0741011003507202580d040e04969940b05810005105140c80c02441000c2444054280da0b0483c00401c22030002c81ca4240007040600104402088518041e080041008400c3e0b88002040301c001082181443c0c450840000d00e040e50500040440045000003403c408080d80020b10302c8a0000b80c6460ba04408905481820f000351030700c100d45030342d5001041e40350b500c0d05401400125000b0034507206403aa90000000816900100c1b400c0075142d03400301c0c608441c0000400042003001c4010800da10381240034109001d003100c0600229450314903e00e4516040940001c410300c10002480514480105041c100000007801c8074100d50390b900b855402400140c404844134002e4400107410012105e02198400d9400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 439313633 1250 439312383 439312403
    0x1502121b06010312022a040b01030605060f0913020c0c040914070305060601090603110426030403061b020c0f090a091a18150703050a090b04050c1011031e160501020403120c 76
    0x2103007c20000b000d402114078103050361080040f0780c07500c6032400f03000f504401041941e61050528104280308075100f281103000c5004001d00c1310001408142940001000d49022854a14615022401d08000701e0071003e01d100340f2400000f0f01c50000340c981d02071a000e0321014507483e15108100c6c00d5a51891405000000c1000200a1143ca0700720520010340c142900007811070144d21118255881a40291021074951a44134440c12280040501c2e2040780e0005002404604000c5102026071100d4603115040403000107402c01e042e030b0030488906602c213070204d8200d55005c61804c600c1c0c000f0f40700b0745020300b40c900e45252600c000103102c640c1461125000c207460341d0741c1202140135220081c81039003183c0d1155110800078400d403881702e000b248940d000e0610030803560144507444d00383c0d00c10b010400201c00c0784000e20850120446003a0801d07039100421004281c0c00118182c494409481b00400803100f145050060650180c02500c0c8905240040d21900704c07001c03200061500c40141001da00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 439314883 1250 439313633 439313713
    0x204090c030c112d1606050d0b011e0807030e030a0206040506011a0d050403021905030d111c0b0d020a0305070e07050306010e06090a0306020a050c06011502121b0601031202 76
    0x400f01086504000c4d401140e401c0349401000c0a80182d0950110300410004600100c03030b2855030241d002800b600317280c12000500085200d03000101c10304035820030300c4108800b09079518402c0c1c0100086500d108203caa8074840792500039500c800454081c1c40c0d1b070040d040041104000c03108880c404030b440c00300031400e02c0b048602180c000e01700900220103600c1040d0002c03009003428036000b40954040d50142d07880c0c502401c0b031142620744042d900080c0c044100310103a601d8070303900000e00c0c2c800300030307040050703201180c03400700d09075159001d0044d501842c1d0150001c01c0081c00074003017055507081240342400d501c0709001507a0600050f02d03080c3c08914250400811418440050000350100910103d90300faa00e85850003240d00c1441c414000550003c0c01c0c0c1d50070b000800c4028010015071141d001c000c503140000940b034801001600414540005800032850b29040c06008046d5110f415079046580da440c0c80d02d5488190354244001d4003400d079041940e8000d480c2071503a03090f1240d41c000e500700c030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 439316133 1250 439314883 439314943
    0x23070201080915010308040513110d0f02071401051e010509072f010b0a05060f04030305030405070e09010b09070e010c12090810090203151306020d0204090c030c11 72
    0x10000707110140c1d41c03080c4403001d103d800020300c45074001c6014000743d0355540c3c00d180030f00c80c800900d50400d0303034000e080140040ca00100d5608890360402c0e41c000010b102c0ca461054500030344903150340035290108660111421403010b40c4890b0044420030546980405543c50200c004c89091250540c041440b0002400300b40c0585c446180e521140c405851a121a82d5800603a5021076265100c65039524030149480d0f04101c1d1076000a4102202c1003400c0c0078424088420710300c61404000d08102c4c3c00f00c08a0304224041119a018003045140e0981902c2c00c0d011042c0200002142c180c4070701a0742d0081500e1074010138808211b1241a5101c0300100d01d0790b100c01c20f81030500385c55042000300082d40001c20032801d104200400303080c44008501d05556004162400348546205400e000c1c11005202c0c10700144400d080c110790b1302c500007507110429404040001e000300c3c3d00412000c0d04042d413105156606911200c54a070581d100ca50641c0303030740d0003a90f42e60104800852040a61302c8103940c2010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 439317383 1250 439316133 439316147
    0xc11010e0d140105041b080705270a0b0910050306062e0203090301140106051903090611030603160b07060b0d0c121511090d26090123070201 62
    0x5006850546040c0721a80c40c1e4484103460034120300903966803070522040004d1801000e00444042c00c4208409080c41d1203103440b0490f603c80d45106002039490701500d150380080d5a11075004042c444070b510328010b00d40d00c000e4010010002d00c0380483d100000d0b1000b508205400940c2c5000c0d004100c159142c0d401c0c07000151448401c100314101d6070040c000441da15039101c641030082d583c0996180e04e0ba00040c1800c0d204103610118403960450010312560340d204040d0343c400c0c564034621911068015400b90010080c081e400703007a0504081d2440140c18940d001580200e01c150300b265070f0304500007103c80c5015480e00940c2c1801808101c00004030b501030700800365000000f406e0518812065403808421545540581449a180006041800110304254014007022f4800f8030080061000991241c07007a6041e1a10a408040030002403080c1e5480c03a14408420400e241c5040d0108080c17005181c1000c0f01071070002e03049510882817840214500d08400d0201e0180038140b40c06940103568007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 439318633 1250 439317383 439317407
    0x303050a03090206031302010e040902030a020108330117070e130e0f150a06030b0402060c160915090207080d0203041a04120806090402030a1b090f0213060c1101 71
    0x1030b02c0e942c5040169442000450050004036034101d0307a0b1a49100150146048010300ca01c1b65190042100141e00c02080d4540d40d1582442c0c02c0500340e8a100440b0320341d00740030320040703074403104400880401c58002c038010000354000d891b0481381003600050600141400c03526000042c4560800303042070f08000301d10703203481c4480700c01c0030a01d02e642c014024540714150f0b03c400242d900640860091342d0002c8905074220f914003030b007882501c0c1152600000304a01600082c0200c0d000280710300542002e00c44041c09443c0003400440d4107079140c12036006090a01d23410500c40c1c4003254009102d100340c0c4211040903a010304141c0c204000031601c0030003500010401c0d0b030003290b400920b07aa10b80c540c5c42d40c2c0d80300d2841030000d0500201e11140007040f458008064501514244042c080540d50001c2d40c1134003e540494040460242c4c0410b0125500c030503400700e10b00c0381c1000d800e00da01101da500a4a0300400d0f441d81c0b00700a550381d00c81140e00c2c906050024141e06242c4070701d048954844c00d841d08030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 439319883 1250 439318633 439318637
    0x405070905090120040f240503060105122806210503070206270405010308090f010e060703090911030402060406080c0405130e060c0a0f0809070b0a0206101a03010303050a 75
    0x513048002d400640c6a544641c0800501c6001400f40300e501c1a41d10004080e20145610b007006072809035510100740d080c54000400e001010000643d568410070032551055a0001e031540181000400e0b0500c140f80c884500107580d021411100507402940300b40e404480c2c900c5e9500c0c10380c0c0010b4a29040c0c805400c10700fa16203010130030010b405a00c0f414010303c182540c1079000d103107007640e0038444011150981102c501c118107010040003c0b4003000d040e5000c0040440d0075014410700c850040e2080e014110480d500b003100401c5420074150080c0c400000c13148581c03070900500081c0b00d081c001ba4441103c0c000d5100d0f10900003403141c00d100d602465404400683c4140c541070300e6200082013501d007500c03503060940e16907612190400050004139005000728200c0c41c2411500c0c407020b4142244541030f1002c11003403800103141c0040810481c4014540a0001076442d449040025200c8008070351540c40801100c07400161641075111240c0c039180d00c408004e08590031a50100e0703903171f4003849601d01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 439321133 1250 439319883 439319891
    0x30907030f080f0313050c0f0a0b0d0603060609021305031207080a0243030209010b0906040b0d1d070b0a0e01030e010e100b040504050a0f03141801110604050709050901 74
    0x19a142c011001180030302805c0742ca0504103090342c07500030718000525140c14025110a9100b00c42c503120718109400743c40001044039102e146810702200180802d900142002d0f0608200144c0d0764103560007003444410920300003803016113450034981c0d103c80101c80c40d408d6240c1044041d021030041130141040000c1481a50860301250428520080005640403159610300c2e039440c01400301284264000c1c40c00d80c410002c9946540c00098801d00140f1405003041c00008030b82e5a25603a00b401c403405400f008043c103441c3e03501d178061f00f4002c0c40501c82c0d461000d64082d0360514001000a020022911070100d07403450450480002c070383c3c04941120300c41c103154486410348015007080c0903406608000f20000c01401c0d00f080a50000d442424a179180a140341a0500011900120f005003080b0307000801580702619900c5e04807020801030b030032805003c1c408203030010480c40a011045d103e4809076155560540d400e1035403170311400217860042083d80001804c20031220503402443d40200c05900000d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 439322383 1250 439321133 439321147
    0x91303180e151206090a060b0310060b0405090c042102010e03060703050a050c040812090d210210020307081501050d020f090418030c03082502030a14030907030f08 72
    0x842664156141002c0c0034522942031494208a4003d400c0455801c000b0001070510000058581c15910005050552140c02d0703200c00307840400c01600a10602102084200c1d81c400401000c1d80041c0921442151000041280c1061070000c0e20180c407030b4644042a544101c0300310300c6550444401c100c2c103211184000010555080c8002ca01c02c42c0192030106107403420300014801c0b0b8078010214441054140030a07c810300002880354401e80ca00321000f580c030708040002686480c0000c000900b0213103820b0300c04034080e18102454544981035000c0340d0150b0141c180b407000b81d00003116503000152440000a00550184052030440d407410304241d840c01e100e20729464244d0384a00d90201560f01e000505038103600701481010031046070b40d00c2032651841159001001c55111441c082d040210440200380c1d01604160080e0151502e0300e0710050460030410060f488e6004620004081400c0001709040c1140100c01c807841840c2440150030400d0560b5581d15800d42e078885c0c20744060b80b061202d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 439323633 1250 439322383 439322399
    0x1c0609080424030c0f080a06050301060b070c0b04061d0a050310090b09060403200f1906140405072105011401032f04050702010e0a0303150509130318 66
    0x40016002e46a1009608a2410992440c0c50315056590003010301d0b0003940340071558482540e910b20030051420685075120010098040c6c03070640c003c203038154039000303000440108000081c502c1911440d00740402959865010321940103502c51040442c011b0b840700c6060b101c242d160f00e0310445006015a0381662110f0200f4035000542c07600780001b40e561a0718200b070007003d4810641c0544024010a03443c501b0355001000f039003840000148d400090301b62107008240c00e200b000741050f03040781150300d80540300004800547d540c00056031924a0000c80307802c64001304902510440d0400700818032a45031100c281710200000151565004211880c000040c03020b0241d226007414510442555504505080c40c118030060709484e01a44000008900d02000c403d00309203102046400140942c0c034190140c0c00b41500055000c41e81c020004501d017019003541c0840e010311a103280315617210381c40724241b0400c1c45d010744032a082840704101880000c1d10070142000199000114031038003994400031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 439324883 1250 439323633 439323637
    0x60206060105070816060b030c0d020f010302070507030b0702010212010801020c120903010f06420c020609060a0215060109080703060c0905100503010816030f0f0203011e090515061c060908 83
    0x403a02140c0fa03e100d1f003068030341045507400180f02101e400e006204141c0c0020164100c079903419040c5500484d4074400e0100900c1814010340e00f2821060f0940b82006009000f940016030400005505030001304184205200f524905106200180352840030020400050b4204601d819810340d2240c0c1907055856290182c9401803007900140310440a8204600c0c140e0741d851400f8580750902000d0790810b0598803000e0020242d02030514045e110503074000f161040c441e070302032241c000500150000d10507a00280c001c0c4122186107043d031098480e200112840303005031145000b10f9000040900110b2002d5001a5400c00c8600742400d030a5583c00106045204a803100340100c0c0c0003000400c1103103018010480e8140d41d0000d0700020301c0c19a601c80c9000c4d02203180107072078900c0300b80444046480035413003122034500c03070b414072344443d40e407040c1a00191280780c0301103c1c0c40c002c4000c85058a44480c59003400340300d006010700d4100d1000b420810380d1200241d03041d01c1150302d0b043e00002050210b00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 439326133 1250 439324883 439324927
    0x70b1803040b040e0703021e0904090b16080c0a09090e07080706170f101415040807031406040506130f020907050a170103080a110a020a0b220602060601050708 70
    0x50b1558550345864000444404000c180c0014140100000402803424074440c2c410200300840e15030311692000d0114000b07011710523004040220500900200f480705e414011100e80050b0b441101698609145071f0300f50045001420205180400502c440d5080750000d110760302a00b01200e05540d80c40c600c0c06e2074902c09501c1600030441001d40090b66028807585698441450f0340c0705100fa0900144003060704009115a0040408503550300420340d03501c075014986c19556400c0d007034031591a1804561640040e100484051000d400c4940c41900c0c0468000e20039604040940213030350344c66003044d1012120410449072030311000340d900d0059440d81e4036107000d41480c0e035030b0380d4072101c9145004d0800360896601d100900c12080040002407003010484941d03072043c0c540340f10b02c0b800015419181c40600b650080d44250154404101c0400c0d0344060005001c03207a503080202595152800804420b40c00703801c0043e000300d070004d00395501501c01421000d01c80c0125500e040b915500700c19480541030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 439327383 1250 439326133 439326149
    0x6010c0f0b0a0207120206060604050402030601050d060807140d05060615040f0b130501110d140f040b03070314010f120c08010c0c03020c040b03030706050414061608010f0803070b180304 82
    0x7184c040184840d040c03001c1510681d40c0018002c5080110000e44180603030f108041c480c58000000911a9200707000790344950b00c10407000c0c094152203031444c41c0c5940d024002c1c518146580071120155103002c05200030400d402c0000f410403500c45606006041260100642d24540100710001e6104400100e000003404041181074480c6034038481162100e2403684078a04102e880680300682000200c0c100d9044201c44c03c0c40c070b020f40c0314160a80b00a0080601c03001c01d1600c00310b00003900040803401148070b072005680401c1401c1c000d98031040748003000e02804260070356101c02030080507088000041c00901034038650717540ca59240403890958440c040507500154440c00034404051301004442c004910803101482004050720109a8034013410b403001d0f05554840c4081000c0c441200003a003d000f5071181a105c2500c0d060340100b00c440060303115080001c0c1a1000041e1000842565030103640040f0f015604c3c04040d41c4030303040c4d840c10141c0400942042c00c50000240766040000308000c01440d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 439328633 1250 439327383 439327387
    0x215041805101a0d0e0c191415030112080d0c031508010204060f0534110901120b1005030f0705180c0304030f021c03020c100905030306010c0f0b0a02 66
    0x80403156000038240d44402c0b4803a44002d04001d0640c403c000b41c4481c034035481000118007440b03140380c0303213460104190b094200f010754024142c1001c605220790150354518400002464242c3e060010180300d448c0c0d450381c414000e1005205681c07900d000f0a02060103910190f0406038000300c81b108940d540712026010950795882100d809982c2030400004000c80c034001c41c1818500200540380d020035040400801c100064181d40d101100d0700c14801500041a102000d00251950740c984160114030907a1681244510f6481d80c2c5007440b0020305071101c1031121424000c690f603440442c034402924016040441903030101e00fa4508206e4224a8101c0750000c2c400d061401d8180280350084030403010000c4804010010140e440c0b00031a80c01c02d92501d041001c44402420407402c00340d00380c6041401000007a80070030309a5058020b000b10181101c00d40d50f81d1104103600314100d629003100107015410500024074158050220703441661b01541d910741e280c16441c1da60f25445d043c21990581d944d640 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 439329883 1250 439328633 439328641
    0x1017221205090915100c080307030b12100213080c1e01050c060a0c0f02160e0c0d02030705040f170d140c030c060a0606020d1227031116050105070215041805 69
    0x501c08100740480750304043c6c440701255181c80107641300040c4448140341d1600c960f4607050f154000c0b181c136080c0d484020760707203035551131046103000c1d601100e002064001440c401246014000c16144883e6100030705c40e86102d580301e00d58404800d405910f040c14818103210319840c8607414030013940f060078402800941650324141c040c220300e00008420045502c85e0340481000544811808280d401c8035410803243d5841c206110b01512070603503203d282a0004c0f051100142d040700c0a0420798804d10000e8904a0721410941040000c038101c08107640d0021902483c814051314880b00204103142c0d5603403800710780001052450b80b104a201c04117900c17200421142c0082841400050070080c401340881050400c001010804c60044050301d03140c4da034600800142d44690205284110f01040c040107485500340135003010303039425841502d4000c110a506810b60103109020035146c0584070075051440303d030244020409101da5110340020b081002180222800c840d00300801418031003c0313081e10b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 439331133 1250 439329883 439329889
    0x30f020d0c05060c0c010902061204110603040506060d03030e01020406020a06110309060115092601140903160c030b130c08010c0806130b1017221205090915 69
    0x2611102808001490141c0300014101044031600440c03c642115100e50380c150340d4900525134414000c1d884000000c10b07007822400391210900c070342d003c0e170f56601000b0103090900c141444100c800410ba604440001000d03481d0039416501ca040c00380ca400105510301d40a11422a44181c0100d00540d00020b20001000164050082d204d01c160704802d048d4180340c007410350780e0101070046410401d010550313042c0ca940b24481c040b004120002d11035200c580061105031183d4848002c070940c65003404040154810501760450003421000c0003035240c408412007008400e658820102c4618040110003c00305200c03002c03050080e0464840784080103c20300c0d03c0c040b41c000c1c40c0c0c06a103540e4100351180c000ba60300010b949a100381c0950b50f5a810f40b000b40e0542c0001c1054004841d0b2000e807440900781c1c4640d000e40c151010fa22000d40942c0151107136202c908520070344800c14602580c3c1c8095850000b151946591060119802c107541483d4140f00080c00300311048a40640d250808440e801c0945 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 439332383 1250 439331133 439331143
    0x51c050d0b0301020f031b0c010c0306030b16200304151e0e09060603060409060615020c0a0311060c070e0a02090108010608070903020603060607050f06010e0106050a0903031803020d030f02 83
    0x49070440c000c501d0258a038403c520203001c0205040c1540b07911010b221130381d20340c880071900c0b214141d40c02001000808200a00100040c1c001965440c58010005407646070550201200da030f41e580b600c00040e005000d0030382e0700000390b228004090000380700015a840e5249801580992a911000c0404044601403d55410000030071803c000d110000000603403628050f40760014000d80f20650f03282e030b607c004600600381c5404001d02d100c0c54148009100d50080300c00500d1a90746030f094828445010703040010001e407034000582241d080d400940b0051504a0091017000341580030307100c0503641c034008031007014401c6800c400c1c015000600b0340f20030343e030001100340981000e04000c041c41c240250010919466408024098440000400d038907503647c8064651300f55018084402d090040440e26407103000a21884480c0a440000820103600030025140910080c0d07881100481c40e54a00326418880200e0310000b03c0040307500031025880700240360050f1406500d40e03c600e40b407031502c028542 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 439333633 1250 439332383 439332401
    0xf13120f1e0b16020c0d030e1318060501031103010207020f0405040230060109020c06070f022d010f0b060d020d0b09040614060402030c040303081012140712030c0f051c050d 76
    0x40d984503001c800001303800612010386648140d410455060049820030010012041d00480009840305600e02f0403541d6040380303058034400e210407295004403e0a15003030f400343c40c5000398001d03d0726402d080503060030fa00c181c0d40540000d103500d140541107142d00c00d800703540c1304034602164001d8107040350351202005400e00410107203104515186407a0325a58403900b028111008118103501f081803d00c2c07007008444c6d1001c401c0303014500d1590449601500030441d58203580807a500b40784444460302243e00c07588060b880080c080521f40484004804001e50118409001c507541d650348201440c0c81e02c00c5954403c0380300350300000701514100700c010703080c0a00802d040e10842c01082003102020a2109480c01c499141c101212551101341c2d5140503c6e84682081d84112413111a0300144140102003031400c6441e4410303100d890b0340751041101605005003029001c00c00801c0c445000480c0e4102d29034100d401081a501030302c0c10080c10300400a110f2500724000381c00800c034224220f040d44214a14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 439334883 1250 439333633 439333639
    0xc010b0d020901050f041d0c15030106051b070e0a1406040642090f0b130b03070c02041b0e010c02151308030f13120f1e0b16020c 57
    0x9890a5400188115014000c803806101c00e407203500e21703d4440303800400c400c2d5100035110308000d00441c6002d076910402c414191060040342e4003070081525038802c403416910540d54551a10031440103510440750595080c011620070312000141300c480160845000d00b1a100b0301080c440071600c034481003004c0140203a44035030715094003004401c02c034400040000921313812143d0500ac14418204811030341801304d0189184120407a098560f04c040c0040c00d5980070709045020f00c4d19444124058040c010320042e40741c45100d001e01128150302c0c041c40d0300048070701d0400141412640410180c42685980c891040800d2103040f40c540d4001140303107603807102031a082500ca0480e800189082c00742003c0f1045900f000075403080c9074080f000094010306408421650b54440c08208a402ca40c04511403800c150046500410061208160000d04c540c1105003001d101001d0380341e650703103002104100b00c07101d81a400c1d040300203101030001c031b4890350000b082c6400072842150064280000c0012040c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 439336133 1250 439334883 439334899
    0x1060c0b010518360c190b070f06060302130e1c0806040c09050d0b040521091302040909060b09090c01050403170d0f0e0f010b0a030b04060b0409080c010b 68
    0x1008001c1843c080d54400109500c0e800384001c035410079a103840744103485041044c0c3c401d41d8908814400038800c02038200590725100b80481101e040150981e09000c1c0c40443e0008004010100b9008021804041c3c0603800009502da52a800602801c6060503603040703194540b02c6503003140c4020701c440520032a4003941020041c0b943da41c000c1c688030380240154450b40d680d000d140c0320b0510400c4100e02038a80500f103c10408203a05055020400481d800c0300c940c03146902c88800102074150303580422a2081006003058898003c100855004003072078070b0100c0d0b00b8400011b0506c0103000c0d444443e400b9410028400e0800700031320201502c010602c400940c8010140c004c00d90303101c0100c0d4100c80e0414031190301101c900c42481b20303510421451380724890a01101d14521840d9921000780300741404202c030b8403a41004003607400d070740410011680c00111028100003040ad500d105590151040600141810062002030304442014106461410001c6600003020a003480b03902a5a041220113032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 439337383 1250 439336133 439336159
    0x10305070e010311070b0f09010501080115060c110301020d06060306080a022d030615040b0f09070302090d0804060c0b0718050448080405070e070210020301060c0b0105 74
    0x142032504600c01e0307035042654900f4a030180c41d400400303580d50186d0040d00c0b401c1c6800d00710240b003045441524914415441d10000207040d031b10500c503500d0745c01c80d144c20b10442c00780f4003881a00c1003034240394140c0701101c44124900a581c2d0a2004181e50008408001016800c1c51001000c803490740d00040416844005180096910f1140091b0241c01303400300d0703a1401540d0260545030f4014030621503094803030002400134080c1000f402800b503a5060780c040103030354880010051810715141b201c1e03400003401404202464403940090040c1100a003100b10b0342c00503a5211540c1e5403159000c8400100c04144c102c08200d2000c4c08260450960319000c400d416a04080d01441005031040c00e1261b983c03009484425450b110400303070700c8044180303a00d0700c025074080c140d60526400400c0040035100383e0b840f6200c042c05044058012508807000b80603c500b89121018001c00c0a130444013036201c1ea10140820400500003180a003200d83e54100c1e08c0d00e990720b0150113040301a04030710721619111800b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 439338633 1250 439337383 439337387
    0x1503050d18050d1112030d1b0807120209012f1501060e36090d2c0607080304030905030c0d021804080f0423040c080403141314040b01030507 62
    0x3083e5081109403000740c203900001000040b0080a5a20350300020801c021f00c5030311a0b00c10095000000396400f5204904581104c20040c1154804086007551007410f006110310703409003c400b034041c1043c44103140040107841c0300380401c852400315110124103100010b03005002402c3d1054120401c642035505110b0084c0401509440b5907002d1080301502c241e0840084105400d02000740721034044220005d40e60000b03141d0111600c2c0c98a100c0c494806031034a10801c00c00c0c5824591181c10001d842e0f40b01046034504040742c40d056440708061010a02180c0810010340c0114425219900298a0700d0103041c10300c215000820f2150300c04940e020050b840d41c09481070fa03042c6c0801d01d0052540c0c0c0e840e284002d40100810070142000110f030102c0e5501110712000940812001b84103c0c0500c0802084150f40c0c04404480010b1504408a0006809441021880c452048030542465058803040e4060f40c040d074800210f100901601e950a42024840e40390708103003e107401d001615080d480 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 439339883 1250 439338633 439338649
    0xc2111040f090e0c0f1c06060b03160810050d02040b0d060e030c01060510090b0c0109080d0b09010e04050a02010525061b08010b03011e05041503170a140d1503050d1805 74
    0x80452072406c0401254204041341d84120040c0c030400459646030f04118200b2001c00a070030501c040440c0c0d022022604a21110401c001115001080880d102c20703280d0a00006d000000065a001440070400d070000800b07a000e085850780021003f1512a94070000c0e031030940d0800e91080e801248200e02c0280d0056102d6401c50640320701c4c141255030742d8504107a41c0d0040101510107000001d0210762050a070441e5042080081303001c0354803200c01e980314a4420030b040010b443c01007103540031601c110010750246003d0850f040001e0074102c07100203031071081741d01d8185240084801507074840358640c42451503001003032554458031305001958100000c0c400c6920060040d03592030b1596101e201915681c0943c95009040003402c1480034280e600d49180246401c2c1c04110b40721660685617918640800082c1d40c011180e907510a980d9010607030418501e40c4c0040b002802954890140c068000450b0759030b0001944203400034256103072003481c000c11034a03107113132420141c05a110080000e0b41e28028 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 439341133 1250 439339883 439339909
    0xd0c030503150f03070f06090602030f0a143703020a08150a05060f1b031c180605090f10020c0601141816030c2111040f090e0c0f 57
    0x220199100c012000081d60402041404035070602c00c00c0000b02c1c00701c1b00d56140d54212203107916504809921010300341c0e00c038051388100d107405200902c003896880c2d2090320300c030004c001c0ca44107280ca0103415030241808082c2111110031a15450040d503144080b6036800c00d100302542d89401c500700009100c00508500c405811000074100c1200c110020f562030901c110000c00340180b02a03510708181000100c1a00050134548540c13007401d500944c08840403013200c01d036003040002e151841c0046601d0000401c00b4030204c441001e8480d840000291462080034001e103281c400030500f991407a400c1910304440d400350585201e005010f000703100b03500041c03e10f066400720241104e8000781c10b00410a8806021002c0100c06480803d028207800100c00501e190040313903409100141c0d007104140c954010143c0c805400c3c0e5165140003c450001b07500a0b81e02403004074410b407515540350000c44100c8401d4005d0310805944841049000104000b00c0490038400d0390b8940d9a01e101c0c9000450011101c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 439342383 1250 439341133 439341151
    0x3060e060f060f0a0c0203070e070c1b03060603050120160b1305161a0a05041202030705040204140a0f0609050613050406031101030e1506010311190c050d0c030503 72
    0x1140c0c03505036503000d00b03441641d0701002d00d45883d18004080204580441740c4241e029016985010a10302023050b18640303d82100e0310782ca41198410307980e01070020710001e0079001c00c00741e01b00040001129801030780010741c041c00001c624080f0425a1144020120103428065401085034160503c03100c801c1c4450a5008288001b4680d02c24581c0c0308101c9503014020510700440c18502d200004038a0100c0c1581d0820f0520300030013031138000310280740c4a08001000131840c10b210800c29241c5410070406114400f4080e00c1c0b5080c2e883c00450207907040381e04005400b80300c1d04088034041c14081e18800040c5482000283c1240c502a405440e904050203600d0143c100003411112051084003078034020800600b0401c20b0f01d0fa241021590640550394a0b8001b07410700880c0041e91f0300016003241e1568400c0f40342111a1941c0b4015001080b106c00144c10101050042140084001140d44400c52413034035551154015407524034140f101444440e0207003e220484403001ca07078450162a030180e014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 439343633 1250 439342383 439342399
    0x40308181c17010b03040b09030c030403240e0102041e1d070c0b010e0613090209071107090608010c02010605010206090a080f0408010c111006050d0206032205070f0603060e06 77
    0x1c0d002c45008841032401540b40454100020342c10403203000840c8100e0107500c82c6006c2e501e6000c1c0f129103c2c031868000c5078480e44180003d0022030b601d1541030800e1200a00c4000780940c440002c0c0096449070303118071a4503540464100190710a0071040c0303a28a551408a03076006040213810403200c40003542c40540d4401310000610220300821031048000c0e040100000290b9440c0d660214940040300c40900032181c00072004c2152401d405402a5541d0080c40d00c0341c9c03944d603850300300d60414101c8a04801441002400106500341d8071034500503040800c0040341000b003d203030190943d038083d40b141d41150302800800000001c003203840b224240d84140b440356a886000890b101c14041da80101010754a480e003001d500342e4102d100d48410349210401e9842503203454604200715146c40c400c0e50380080010714483e0042c64528000c1d94000203940805144441c0300b06510f00c08524200e0888880d07101d04018031074080e1142100008262034a0b06005250609583d03000c000f801610107030040d005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 439344883 1250 439343633 439343683
    0x30213050a0e070e060310090b04031d06040914010602030c06071107030b071205062719050c0703141306030c0c0816061104081507111504030818 64
    0x280c200d1a071542d046000c0710111034a41c011501c0001c0151a00c82c0b19104803009141803801c140149a021504034102034415580c0f41c4003a03d00e00c24840005010700c1c0d418a03107800c1030741d51501410241078108030014000640910b07004248806030400c0d42554401c4c0600207018000054440c0d0209140c58882035412840280e03902d400803980008064400c40010040d903d0f07070114407921b80044203a018015038942c90144250440009100300020780203051062856407003030a40d9802090b40c4405000c415158a40348044030000d030740c05840c0c018000303032a005140d0b00900c214480c01a1800107450040b8892040030708404606c60035060545814a80e80c000703016000d1101640c0d00218015501e58500905111507501002e00325285841d191604030a4442501506c00b60b0340080d00a000c05400c0601c02c0c40c2c610742c010410070070000707050400f8044030030500881071600c0d00f900c40913516050034074000c1c00c4110001d0410f03c0f50300c0a07075002c02d5118800101c0040c620001c040e601b1050700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 439346133 1250 439344883 439344901
    0xf041a070602120609100302150a0c1203050f15010903030f020a0b150a090203060f120f011a010306061803031d040515090702160306020a05160b01090c0903021305 72
    0x1145005401c46101003980300e00401e542e10301c24865101110b8056060b942c038204c032002c10030315000181d01300491344081001c00341c0450042052450501746081410303c5583c4007508a00e060307103d100026280c0040c80342450305e080840360000025000103907406d02c0301c0f00003071600c1101c0c031001d001c00c06400c94050041d4001d1200364a581e4000504035003620b4a008144200388604442902480c800100007800d40036910950b40030f480002d01c82921048100200400100c0c240c1300000180a41d18541070610402d11804960070b115110701c40c540d46200700050211511580030307106025032244140541000b00d00c150060302c2d130506000104034920382034500e6060710300321003603042450030052001c5802c0004080c08030b408126001d60195464000498132251a45c10000c407003240418107000042c5070f074001e0a00c280036841c2140c1444055882840e027140c3d168016604216071000504c111070715070042030060125402c00021580c80c40e408241e048400b0090224101c0c0d58401080380c1c1c0c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 439347383 1250 439346133 439346137
    0x3090a11040209030312010503070519140a0806040605060f060304052a040914060115020a06110702060d020306030729090d120207140409030e040c0c060509030a11030f041a 76
    0x3e001a0850381c540c0c4240c1e600750700019007030107a079120b071081c00b074001074034035102d204d0442c40790100c07090030070703441c580300341c00420415607208144e12031100c6001080c041070810180348664060305003c209820320300700348a03074454803400300d5000c0d1004004101c04950300043c42c298030345425808000c004c5d00f060400d9003910344079010030361050500350903806110519401902c0d0148020035030350035036600d00030748a050610902c0702c005a0805298200440c10b280d1248841d441d041e00c0d0a890300113582c2c0082e5081c0c1c13105540000d11035010090181c1c03410108101005481180c0030051a1144040425481c1c0c1104058140e981d50005407035280e9269811a540029440060030f00e814211440c00303512071400d8003c1d07146911000d5500403442c5402e005000c041600f54482c2c40c10820154284009001d100d61007800348403080340d9900000b02c05128940c400e1641c000910b480d2414030700300400c000c0c0600c001c00c503540d2081c031844122440e41001c80d401c41d8451480c4042a1400b5102601c4034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 439348633 1250 439347383 439347397
    0x60f10061d191703070302100e0c01050c2503060f0e1009110603090a141b010f021e0106080f03071e2303030115021c0806030102040b040801060608070503090a110402 73
    0x16400300c0d03d20110780c403c0040905019413003a000c3e10001da1801500340100c0344903103507800469105117114401d03540100020600d0048400070b88000d5001c21a864038100041030002d85804400a020818004035102d214200c80924a0608c280c2e242803100c1076481c03488002d1018a1550f80d03802c08100010700ca41c80c3c0025401030324441d12458092000c5480310392518060701d41070040d0300c030301c3c04c21000800e900103d54019031590203000761038401107581551461445080d4403900c5503030020440941503420080c0d000c1000420440e040c103055078103010b402002c60960b54000c0c8450070000d004450b41d02400d200d034405012804086041135100b513004640101c100500c038000ea2014018080011410b95940d1000b2060340850300004aa03039a103d0f110b115031402d032240c41e810038036100c1c42c6003039003100004001505168580c0d49400c40d030361080e408041560340d150410040360350071001c0a544114181041400c52500107052901c8004c0303044014480300da500d0a0081c2a940c5134152450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 439349883 1250 439348633 439348649
    0x12072d031d0102070e0406020901031803020601140616110a0f06120209220605100809030d0906150801060312051905070206040b04030605240f1e03060f10061d19 71
    0x86400c0c07e00704203000b503104000c1c00380000d0400039034080240d004c2c5018803c45a065005220366860719680c101c0401c0c0c0b0840d100d5000d0340810491001521891040c5a481e0040c106840100c04d0311080240c40700d41c81e40400c4c8422010705080000c0c90b0089980010070348009409130fa92845480054481140c0c40000e10301110f500b1480c4d03c201d100c0383d1228007510402c0d2005a800f04040105861098040712132440c940d10403c094030b5511042d4003d054414803805003c21442198801030884044540190b40140e42d10340b41041404040260308ea40c500d101c5c28802d00e031120ba25085082c10f0445120182481000030745841151185811500105403412000e41c8858682c900b010180405a034945900f582c1d0030201005c0002800c5607003084040207000100c075150030000d04c9440c00124010914098146000b410551010705c4507922071070007854600040e1070f03c4148214016131075040316041007401e111040311916072a043c038000c0c0108030f500141c0c8505400180118104541220f10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 439351133 1250 439349883 439349909
    0x30c040906080a110105030c07061a2805100e0d03020c0904060207050d0327020f090406050708010e010e0f270d030b06030c030a02070512072d031d010207 68
    0x2a0248082141c1c05041d04c6407121010702010980111202e010540c0da00c28000c0041181e140020215030091410724400ca02c01d840a028440004001d00c0503a05a1240305101010b640540c812070300401019013411a80041c1501c0390043c001e1118004a01c400d0188812a4168040c1750081011103004040101314a015141915101000c0d4100d008119130511501c0f10040c2100d0180c01a5100350410440d203105c1103458600d161503000e0110800e81e0080380e110700720380036a04e500d030005100e14040d2034003241a0603c003400509100051b400945041c1051f001440500707080040d0a8200640b501e0080041c0c03584240d00d0045034902125600100380740e8066019080040313024950100551000c00c81d00e0314000600005100407074100810034403c000040c100f0401e6806020041e0260f4112614903e41790007040b0f19501c203d206075140d074803280144940811021406039403248001c0d02010f08002950050700407001c04652504281c80000d9403100d59100300080c0004101d03c0c52800707 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 439352383 1250 439351133 439351139
    0x2113140a0b09030927160302090303070b01210b190b09071d0d050c0402030c091e0406050d0b07032d0614060f0a0c0204020702090901050a0c1e05030c040906 69
    0x1d55a90320943c40c10303018034112001d0501d03050003d14a28510703007500008000381d0380c4a451116400e903443c1001b00c00c1c5030342440030500d5620108081d1091510408400880e07505101a040c03401000520307410710123111620240c001421740c0c100d950046980082c1d20000400740c440c0c0da004d8184810f500340c00200079810445c216500c003031800c0514195100ca031804020034414404050700142e03018100e940116101c10700703424242d00843e40b281080c1c102504145800d00020060114030007203542d140b15050003c441031401d40701d0b2030000d04040f0796582626560340c1d00e846252100a0142d41815601c0c1c0501c0c07003400c00f21b03224603400024041d1510341140d04a60203401401d90703016103010003110a1100000d4100042100c0ca0b1000402e109070034100c58500032969815a064105d03009602449160010788440320458084e4200200100d924074103400c1e00c3c0111000000d8401c10444090001d050384c001d0003007800c640308418a0040e64942e17501207901601d200d00e038000110300c0d151540c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 439353633 1250 439352383 439352401
    0x1c0303020306010908060702030a140c0d0f080f15061c020c0106030501060803091f0c0503040306051909080a0e21210a0f030513050a082113140a0b 65
    0x1140b00d454262100f03402d043e121101c0c07917940d980850340d100141e4130170080c120815018a00c48414050800d111901d080007804205050542020900010400d04402001c00c19003200c442540301200151011951412800e8042c810880d000c03624092603001035003280f5080c0c0300800c841071003a840c50239503891070361204450080c1268403054070154601200030030009004011100381e1200205494489000a120003802982d4010f1400510405006404c0091418000342c00114001c900010b00d40c90040c51526002030710a0340b503960549807145000004000c2001e8070702945c1c2070b292403c800b0b01c1050200e9045844000601132921408009080e07603200014070390741aa0070100d20040540300d4003092459130180040c00c0001c00e201e1031855611604c46c4c0d02c81d41e4040e89158101c8103410320381d1a4181040102c0c0004d881e030300c40000ea29000622021358032122001101404d00580c5014980503501291050000b1300084039161035103640941000300040c4030340c200c00b1080007414200c2d40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 439354883 1250 439353633 439353637
    0x1050c030108120301080a0605061f03060311030303100b0904060308070c060e0d050604030e131e0c050403110f19230109030b040f14010609022d040e061c030302 71
    0x42c06503148291a10b2000004011041d00c0c12144007100a101d0142c040d0303103c40c081d010040c40140c204180141c0034010300384060a018885203580c07000616541181450704410403082c80b514081e500030028848001c4030041400105c036240740d581510780318040006009808294400703841002c0200c0d905042c08a010320290844142d62208180ca60403a400e01200004001020f0420703005100060046400307682d030980404402025903400c040400d012604a03001c4c1301c40160790100c00801034090f040f241c810030004030b40c00d0604074202460b5036503103003201c0c000c1c14056000312a150110305003503c811034800d6031202c50f040854540c507101d0b81030401342c210203051480b641184051000180d402802800c1c1641d800c040303001c1944d51140c4400a411494210032200ca1009410450032901b080c13060101030040e200015a07103010205440c007410003805600d40044080c0708645140034032035011a01110180c180000c03050b40c41070002030706d40d861b6000c104803110482041d1020103a040d40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 439356133 1250 439354883 439354889
    0x6180f01110d0c09030c170a12030203070305060f031b0f060406050d0b0a15030e0a1e0506180d0c0305040f0b03061c02031213031a042306060d031101050c0301 70
    0x102040346515600d0100d401c4081c0744030281c846c9542070030502900003403034031580c036003000c0e141107801e00c92040e5903c2c8040c54038001c01c180001d6000c01440000d0b81d25018080e0400d40440d8442c48072640400000d45509030192408a0f441c42101c0b048900c2c0c540c80d400280c0e8010050541d601c0d5540c80e0790150040d40440003030007403186400b180e11518503141c10780764241e03072142031422910303101c0002c15001801c03164445a070500c28000da400c00500014036107090101c1010a842c02d480e06494030b54a00107000d42040000303242848692605800003404c040d0022291410f07200d440e13400d0030291045d100310340144140101380c10001c00c110031201c0080d0300400341521005c814406e0000011010414400002e40c56002154900340301071418018200c82c145081e10f54038196a03070798648001c00b00340940c1d1407584991404000600c040d040c403c82c10b11200c81080f0290b144e84a540da84c42d800020319075031042c0340041191080c18820f142c0d41100b02c003500000c010320305090a007a54103800901c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 439357383 1250 439356133 439356157
    0x1090302060c160308040f020a08161a07020f0105070506090c0906010518090622050901150311060f0403150515010f0503040204090602190c06050f01050306180f0111 73
    0x102181500c50044201d40b41c00150002c602e1801c44965011284a40040c009440018000c2c7c4454056610b0124080007031585c54001c05906540c800c40b080405407650110a5411112003214206c04540d401c90301c0107a4102d60451390840c44c02c0050b6064080c01c540500503100d0701d405c100d08000005406590382104441c0e060b107a554040044601e07118011000c83c64608501003494a400e2010314607420040040100304c03900c440024a000c9280751145100140380c0303403028000c88010a00c200e030b070305c614402c0c0e85440c2c0350700b580c0b21040004171901e9450f00440000460304044030b640d5058801a40d031103a00c04110ba81001c4562002d040309032190201c2c07419000345684998021220007800e41da403900c1e0141195036a4081000a0140c0380c0c060b0b6249408002030002034200315510a084880303501c03100c031043c0107400c00a040701d000801850f4841d00b00030062243c2d5900161150340300c1e10904c130010101042201e500d0a20944030450200c541c00e28564120b031b003091902030546010310b2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 439358633 1250 439357383 439357393
    0x90b0a020a0207140303190306120804030b0f06180703021911060c1309020903120c07060e030607090e04020a03120f021605061902030906040e01050906091b18100201090302 76
    0xe0401c1c4c0c26014200c109140c4c540d1040201500b0b2002140c281c1501c9406400c2c0080c64550f25904003241c80485442110611400101030040000340303040c880d086544910014000e10304080400d200380b4101400800e1502c0c0c1500041b10140b280e0100d6062201440c900b000040d140480544400c0803004004014041d10000618401d030075401d0701d00000001501ca01010b00d4a00d44400a40c04201600e4043c05019a04000207030407100800703480d01d000700280101c038a041d50050010502e0350032607109402c244c0c14054080e510011040a0720006000d82045841d140300041d6a501c85600003005124101034040420781c018420307002000140d000d440c404074030b14030190300d400c41c180501540510280860b131010200c400c0100261451801120315120054001a0190b0050341c0242d0300e1169040062006040180342103402003410f4412030080c1c1013562546d5020f01101d60300100000000c0b64030800820100511008400701505543c0000d080c0040240a46800030090700035100e8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 439359883 1250 439358633 439358639
    0x30c090607290402060406210204060e0a0f0806151903050c03120c0a0f0c0e090703061a0f28170105060306041203020d020904020d06030605010b0a09090f090b0a020a0207 75
    0x804910b240c41580d00400b4546482d0904100f40c400d9819440031410100000e600c03003050041c5403004101811407078950710002584442040641c54991700405801c0050b008104003412000503102e810202d00151780b48000700450102e040c4000d43d070740310204480300c03080c000140403020645107100c05040e01610024000c0c40040043c0d845500000d000c280d00505900010a1034540030400c0b55204035020720318540d403104410445078040d1000e060070b400081c010403c00c41c42d072003490311040090941810600c0c2140005d180001d0700780c0f5580c0181091041c2e00c8551121448001881c150010190000741e250340103a51180c4595071189400c0d803a04011030b05174030f0009480d40c404c84c1d111041c0313055441c3c00e0004402070740000c5141c00040e1340a10044d441592103002034140503d4080f000285140342d418481c0c10360740180d0146482c50313400c2044a40e4960321080711016100000c0d0302003404009600840014807200e00098204041c2a00384403105031075400070301d014400d9900b11061592 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 439361133 1250 439359883 439359953
    0x4120509031506180f0702100c0519020c1c110301110403290106020a120906021b0f0a03030504141c0210020a0b0a06170105041106030c090607 63
    0x4601203410341e0540c0700711004140402006001da40c81080a40502e51a034100e1307403032002003003080d107003001900b51306010018074550400c180c46250305100424091894071040242007446000000c10000410020350240d250081040400b003c4001d849940303089028001c0c6042e04144000c12204010341000401c10fa03c0c05000c0c0348020401420395134a0545103a8071080c1005456621983d11141c1b01088445004403d0589000307244503000340c0303150300241c81c004c0f01d0705a00e4280181405000c0005004445d800515250412800c01c1030344406641100000c003d9055592043d600810001c00031040690003030103882151401079104039041c0e00f030000c204045210410000401c0d11400c00c2402625000803055190085401699607101c09501c030300e0960761048038404c80e0552503400030001d40300141703209030b84145228000c00183c14030b0350720650046045050f003849014044041019500840c003280c00c09900240707456561100c1d4607260040355080d003000385010041c0460150000c07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 439362383 1250 439361133 439361137
    0xc0507140a050f2505062505070b0301061b03230712051c050411011b0b07050a0e01030b061e0c0a05010605040e06070801150905040218030c12070b180d0605041205 72
    0x5d4402850306042114090341071568060360a0074941003c0100d1465020807018041d83d000380c0b61440d00550b881d814200040e042e0f400000e62441281551224080401d80c003a801c10b213085000c10403044c2c0141071541d080118020500c0151040c140040d100050a421100500d1207401280c10a2558206040014100c90044070041c0140102c50200c8490b0742c4108070905515183c0480b507140e005064a0f200a000740484204002c18000140f0720081d9401c180954041c460902c1c003441030034203a9001c120b081c020103130b1403030000202000030b0440e41190001e44d540152800c04440c0c400d10107051a0b4041c20840c031556004501c1c11054031450389000c21968401c140c50740310281240d10300709002241401c4001c4680070401e5802001ca55699a40018503600302c420300d034421703144c1184040500700118003081c58495800004103000750750012510000710303040c0740503003a204d141c10094658000030500c2c141d503208400034620310822000f5440203010b50301400024420351940f040540e158 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 439363633 1250 439362383 439362389
    0xf01050a0e06060304020109030b090c0910080309091e1e0a0e1b1903060b04050903120a0203040609020a0602012009012309040615020c040c0507140a050f25 69
    0x49010702001505508000300116002071040c074200c48090b40e03c0d10ba0905da90019514501581c0114000e034180345094142a60050104081c0c448010714011040e03a07607201c1c05000030302918448000a5030b209180e400b1030a02400e60500014518010295544108a40790100680f400c0310012a62088840c8180036407050311400800c1403600540c0020300c0d1781403000381d40794058040c0001c414408080e10320f01004610030640030660300c082c80204020344000801c00942940140480340581c1048041d86820409003003006a59817030b50304003480a464003000194110002a00012304140d05500c4400081c00741e1005200d10461884001d000f445070180482c00540c84144413204c8140d61086007100d950314100d403a06e071011400108084d184250b002480403820118071450b9150144800182201c040b101000f00a0100401070014007405401412100b540d100c64841250b0411800102c0e036002000ca039000400102c21b1581c2c0c215030444100300c00e142001120144003158110825 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 439364883 1250 439363633 439363649
    0x1090c05010c02130e0138120c0a0b030708060f091b0c0f031c05010b0412030c02040e031818040303022a0c040b010c050d030e0f150f01050a 62
    0x4620315040045480c1c0c0d0448200703a80c414180381c1c08241d044003e10800c158603651000200c0e091040c000c0300300301e070302056511203030151800c01400b805020b17150000d107415004881c0042c5241c000c00a05140c1040380020a40010720380201048042e01d140c003a42c40394040740d03192444e543c0c84100b805000840c000c8443d40258204011600382141c819201701c00f4284a900d05082371021510303545070159400b01c2d02310303a0700f000688078a401818418000380c10801d00051000d5407610031180c0c820f100380c1c031990468203010000b030402c15101702018083c298008000b0311211001c80d42d02c0f5281d5100b0342103076074442d800c03c1c03241281d401c1a00103000602d40c1c9001e001c51030b0750f654400b50040e50080880701480140c800200c0ca4108036038a524031001c80c0a0000c00b440c400100601040b41d5801525078107201e405941e11000800000f14015100e8081c45d020070300418851001d4901184c02088102070301460440617a180b1030041c031300b40f207038000210b00c1c00b00b0f0740c0c0c8030b0500c000038415000e0290 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 439366133 1250 439364883 439364903
    0xf0e0a0b0d0b0c0c1501090615020a080703090e180601060e0913050703020d030203120a0216030f031d0a020907050a02060a11120901050a1d19170301180e0109 70
    0x204001040b440d07400300842c02d04624021381c0394640b40c2020421981140c03402c00841c0140f001480394803640000e0001410349280703002000c84080d41e10005160000e18205000400c0d5081501c00c18800000300410343c0d43c41c89034240910a201009140f417800c1c126445444000100e1078850b80010380d2040c0f019200038036540b00d030326100c0b54440412409440750321480304000010b07160f0003964074003a03000c6d40c0610780780c02c4046403015194bc8080c0031442000c2c010f03c80300301d00442c0c40303c42d0486150305081500e81045081801e130054887c1a10000e4140e0540c8070003201e5480200e030310b1405520842c1c034407441d81d58941041e281400b54030865401070b4446e000050010300160301690200d00c0810b1681e04141143c81007407940b413022681d03c0e0090f51544140041c000903070080720b46c00603085c0d00c80303a505202d4401d89583e410300c4299804003200b00c503542000f40300f0700610200312044103100d816900d60f1070b0410306111880f141c02c917009803441c16001102c2604180300d4010203da00c6542c400d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 439367383 1250 439366133 439366159
    0x915050a111912020f0f03090d080105010e090a060803180301200304021c020d060c0201182d0501060605030402100905031c031b1806080c04050409080f040f0e0a0b 72
    0x1e841401c059051040c07944c0c05c11102d10500740c560b02030080310760712414699a0386800c95240d170071300003648503075001d2220031401440300380c0c0c006c25000c40a0f4400d0790010f1150351061760400180400340d2003000c0d03e010002d01d4078001c9520761041184032500f0381c0203000381910407203448400080a500d0b003610040500100d00146003940340004010104884d2003401c17200c0e50000364042c143c03140200c0d40541d4a5400b480120340a02400ba01010180c3e0086000b124076100c0d0b1036038650010548000d581c01d80c200f070b103450500161840500390400000c10a080c0c0b500ad001e809a4020740e8164807410b4900410040540300d0b50640040d114081c001e404440311035035010762a4400c1d898200107161300d404407200d20808900c06014403071982c0d95003494404c0080704c6ca15203011240c002e84100204082003100d11628101250101d420582d00054110124200044540204a40100c1803407000400159034010500840c00743e460410300a541c9840e005926000c0310440990039070481c074920400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 439368633 1250 439367383 439367387
    0xe0d060207050a0506070509120606010f0e0307120c06020c0916081905040b0406050108151303020c031606080105122517070e06010309240915050a1119 67
    0x251452502c25021600144030030781e50513044c04d208445500c0060004150b0403403074500a41814071003600c42001d052142002c0b80000c1403c0c061140c0301d42807050039806070120307071410022a13008001c890781e0000070140900d0b18040154035441454010b11031b5803001c0409103440031505028075012001558014002c220503285003500411302c0848180031240701a0000c1280501445644a10910203a44c580340c0b030580111101a0080502c640c071010700788840f80201d048041d00301d19010107841c1c08400c0391404a00d841e164800b5144c06010f203035188202d40001014601c1500e0726500d6a542e10781c1c80b0710912020890442c039000c1981c0c8130380ca2a41c2100130400011100c4031510f400320b540f40c0c0d101c50b0003c4400c0c450203c8407101e0f42c80320b41c2c1049150f0481000640241003460140035003891500d076041c0c81003645814488a14640740020008016640880c0c1d0740c030f60001d8607000d90081790759504005c01040310143c40d41c0d07040150444410241400300e41e40361900c00c0e640d40000a03810340c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 439369883 1250 439368633 439368637
    0x907060804082b0c02190f05121207090e0c1902070503010e07030605012321060a1b09080d0e01020f16030312060b0301151b1506060e0d0602 62
    0x16142c0040c100000c86030010500001840c0310088000400032401c080c80c8001203c1d003a800c40002c54100030211007425610404040d6001c2d0040c80528090180b420454100303180c6015103800c5150004900259080c420082481043c4a031150200c1640c2c90307645410a03c42204c0d02000c08600708500c0350030001e00c444101c0d2800c050700c1141e00007034a030000700b8215880c0041400300c6d58840d40d020003c000c03003402980c0c00b600010f154001c1c60700071a20156034102c1e00342c081e54450720300500342c0c004c000e05e480c12400e500c010500c116082d604281d41c40780000c3c01440728085129030488901889940500040c00450b42e90314020604100c2d282c108035240011800b290381140580b9441c41101034041141307040c4880c0045035196101c0c07070b600c0c0c080e2086007400c403c00b802a040800402a08054106407030441d0051808071005001070384003147c160b0740c070980340143c480d102641c407010b002c102420984100306440d0200940b94031a20140d44010416949a40c020194004500096841c0e00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 439371133 1250 439369883 439369891
    0xa0f080309011e1e061412120f04060f0f0806040e100e010203060a0f0e13021c14190f08071718010207060e030631050610050102010509070608 63
    0x4000030340b00c00070340c01d10205981283d05410300302d07072540481580340030890300040a0040080701005441e1912802000e80003041500510410315000800300488040c002000514141c0c0304884e618098088441e00c190407501488000a51070005401458002e29616041c00d200c0c0e1120403044c0e96000400c0050142c074a40c42c5480e000d0140b040c0c0da8083d140c041e602c1c02d40e05000005d80c4074644241840f01340035250b40001c2400c5240c080c20044541c0071404190412003403101005507a625001040d90184102c080e400d074602c40300100c80500241c0c4005001040e10301e03050700c0c103011200c00c1c1032488284001000c1d048602800500c000030381114001e204d92403098128407190680000c01c840309810080700c0361801300e01101c0a50403580d0601002000e4032880c1007903080b100080001c2a030340c03400200444140502142c2d0307a0120f001074007412215141d007400c0c1d030401500c0e914040c0c2c2c55140c25640707011440c0c1c041c0b00c0414298018042c0c01d00c1007500344018280c0f14640300048881443c003078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 439372383 1250 439371133 439371151
    0x604020306180a02190207030b0f130b07050717031b09130e0f0a05071401051e0c0c04060906060314010302060906160606060e101103090d0c1517090a0f0803 69
    0x100303141034070441607140d5a0304246e0042c00a092560916404400c0014844030a1b000154200b00000c40000c21080200740c01412001c11580d440d4410740e103030700c14134038054021640180c001044c000f0034001035204841440303002185610340b002d810418001c40c060154000c6007070000e1b520038155503114010342d41c01c42d812204100c200da10341c0c81c14501429015030f85c64006507400c1c40311040c4042580301e4800280b90081c50300c00819110b2900c8065054402140e2030000b8044200075010464054a124000c200b0400c80d9502c2541c40018152032003078801090030550300c48039800c10144007a040700d030080c0c03030305250180c60820800325034050801036900150108000011501c50b205160107841503840d6490a56002e204005c44810f00c1d094000402c251644480c0702114003005584614001f07135040201b0f2212482d0510190140b5009445071440c14140f00355015072018103900c012a01c5050b000c25621100300807900d6400c40da0707018004415481485c000182548000c5601810071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 439373633 1250 439372383 439372387
    0x822090207050606180f060d110405010b03070e0d0215030606040b030c0a1707140901140c1006060f0f0e0607050109030305060102010b030703230f0a080408060604020306180a02 78
    0x8000240880c1c10840090300d0759840350b010800e983c00d001c0364440c03625500c0d950010007450000c07402d14040d44000c04081c001c440c15000001044120041c03000380038030041090110b580c5450101040d50421a00c00d4001141c1322010125800e0151414500e40c0e0081d1400c1034032803441030b0314001640301416031500000100302c0050304d107074244003442c01110b00169032640c5015802005043d2860316450300040b10100c024007010641010b0401c1110f00b00001d419243c01c880801650700c941140d40000b41003034002000550b4004c04184100380515800c810410702e625604100c0317024402003110300204888070b1180000b40c1c0200f01401c0703c001c00426151504900c1d60729030382520b0b00c1450407130120791a00700f806003e40e028010450521015001401e542d8a0344d200c440c030b903031081100c4a009160801c040c08508505101030000311019401b240c8000000b840c11584a41c414860340d001ea00a40002c1080792030310f802140d0192a008000c1507240840000400070031101600ca44510359003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 439374883 1250 439373633 439373639
    0x90210170c130f09050403030b0a05090f06031f060807090c09300501022d0706020d180308010e07081306021810030b0a080705030a15140a0207031b0822 67
    0xa20a80728043c01d40e130300c2c0c00b0805040c985030203000d40d80d48014103482003094100a00141c3c071008120380c2d1102100c0001401380e01c40c84040ba003441d0b07100c81904034100a0b8000200c40c026a03400800c100d558400841e4405940d03480c0b0041102c4010101c00c0004043d0030f020030148400d020502e10300a900d100b4811045020600d20f2492041954200e8080e5008180f200c0303410040307403262050100d03450500110301c011440c195040e20030340c10024001907020403c02d801310341c83d07804aa03401c1c0e0b200c900c0b00702000b000d060160001c0c0342446a1010300045074002420184034a10701801600142405c8508417a6036452902a4200d0401d981080d081000070030415558007070030906843d0180c90018040190307105120003401c003608804042d42c000d100c1080140c0f00022444185a008451040701003041c2c0107410140c13041004004842600e0003d225901206600400031207209403501c07014514800200407501c16542c1000d801c200c0c040c08641c600985000c5440c2d43d40c1d001c06103100c16551 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 439376133 1250 439374883 439374899
    0x1b1c170d060501110f0d031802090403170702010e070e07051e0a030e0f0a0204051b040608072d0f0e0d05010e0105060a1815080a06090210170c13 64
    0x2049a14039030340c840c00200080e580100b4000e03040780445018008004a10481a56420b40064080101992604a43c40300c400d181d0801240c5a4020010030880c10b00381401413602003006901004400d0000204105500510a8032003080342c59000e44840c0d0b1409960b0340342d0303100060080090020800440301c144141007081c1d03061001183d0565101d07045081c004048420135860211640d00c402d0550b0b001913800901040f107160704a50114595640410040345241c0c121140303441e940c1d01040105480307400c0b0900b113105041c0e036600d03400c1652580d04002407081c40184e142103150106451810300c14400c4450071016070180c10580410001ca0020440c50031000c10305079200c0c0d540e60a0700038032010a02510b900001c0032034250020f1400e001c2e001c011854510302a1300c00d6643ca10180324a4800d100c1d058000b0208507050311040c0c01182449005000340c010700300d2040c1c0c18405180c01c01c038068542500e02401c0c0b04500c3d451070380c0341c0d043c0d0309882d0700c480c40803881100007040001ea00d41d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 439377383 1250 439376133 439376137
    0xc06090f0405041b060c030e04051512070320060d1d07030f06051602100b01020709050103080909101505070f0b010b070302060c0a120527010606021b1c17 68
    0xb41c132661440507100072148410522041d00e41007041005200d21342100440d40c0001840540030702100c0028003911450441c14072111b400b403925401894542d28100103920214003c400c4900802d880588122018114005400d080c1c041aa1180c000d10030344200410381da100031403904d0780700b010345660428401c015280c95240da000f103454a00c2d40c982c030030170401e0a00446401144104408030450108900a1340f83c691020380c80020941d14484603095a10802c1000014001400d04000c1543c41c1d0402461583c0031400b410302501441c40070641c20f0940170300b03031002c82d004580074400703150442508440c42c0e40981029280c1034800400b00300850801c841242c000c00040c01803030b41d290354a18000e820004001c110b54010b10091041c0d500d00c41c0c220360300198100c079a4000285580c0c0720721480034034507404413600b915040015003000f044401540704078240c078025000c540410f820141000d10500154002c2d54010a040014900308000b41012604051003032240044030b48030510602059 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 439378633 1250 439377383 439377391
    0x130e0102040302030c03010213051c060f05010303021b0f0f04020403140a050d020c010203070605071e091e0f1401110a0f0b0c0307020a1b050301110d050f01080c06090f0405 76
    0x5a5400101041103190070044020704400c180c009506143c40701d48005400003491003042e01522032100c85410251199002d010503550044080180380b903d40d90550041c41e0900003140540f180c0e43c03c0706c5420b10307208000c40c100308000304201d80d00288401400100c02d0800340f201d82054003488080f001903d0742e5020300c1c00c105000000c25601142c0d080051401081100c0070056411414007416203036800700448142540092012070345071224502129040300103050310214400b480704a40c0d00c01d600c46d08200448540007911884102615841030300201e1a21601d02c24a181070010030a84c2d06229400400c803005040c81e181c2131140c440040d0a01004680465101003e02c840c503007002814002260480221400c0605500c1d2007140a55186d21000f4040e20007141220386e00307481c1081c11080409407102074003e20010f4a444c0002103a90495009503a945050100180c1c983c00d00f201524101c40b5500014184e040c1100140034580d80300e40e44c0700350810a40918040f0301c1d1620b0142a0207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 439379883 1250 439378633 439378661
    0x601110304051e0a0f0b0301060818011a042318030405190911070f350d050a0e070b0d1d060a0c020c01020a0201031a030109120e0a0e0703050613 64
    0x20b802c03c1800c01039041300a03000804040c4540000b48a0703060004166419181b43e0b04220096440340103401c03001c5000c1d0269001298200760510300e40e00b03c00c1400703043c0342806907000c4c0020450030500703644803010f0b07a00d590040002880001d811003101c5a11000240100055a1601d600d4101042d0040c204080860048113450020800700c40948280542804080030703150501017581c0c2c804a51000e000c2000e0f0070550300e6001c3d0016422200b14049040700b10144001200d00703640c9140e5490b0300212903070b0480510700400101050042c0c01112120703c2003601a01c07e8908041034014541c1048001110096a070b0b915140885080403015048401e520000c1440b0300d0700340e42c280241c030320b80358505046402003c804105660002011540303543e0909011030703803600c2010807410381e0041215041e499820940c040b42840175819010161410503030320140040300c02418003103803081c41e1240c50b10200b0a1130004007520b109a12940d044070008140c0e68004211003000004c1e03603003451450300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 439381133 1250 439379883 439379929
    0x90612010f06110601050a030305031b041404050a1505060d0204090c0e1002070e06060c0a050a03080f09030c030f09030102091f17040c06030c141909051206060111030405 75
    0x1140581081d030070b204042c00c3c080180f20540c1400c0110368481c40702d00c401000d0140100114034079446103141000b0b0020203149180c0c440da501e0540744900140d140c15a80038515120126a41254078003a04290000348890140940c4c40c1c8001e20105510124a05151a6080c003012544548a0103502c00c030300304d5130f6076140d00c032048081000382c1c00c9082000002558801002041210784948244c0e50250003140d4058480351442641400c008084078010b20b10b004880740740701003540011070075000e590328000160707a03950381c040c10a07074078460300b1024241a40107000782607500706030030b004240c0341d84080d001600303000c1ca18000c41c00c00f101040003034000010701c00054141a40c02000421a01d5800282803042e041c2503c420034421400d02442003016110302881650900440d4100354810081d074150b07035240038100381070188001c101108800580703182030029543c54100000350200300c0d1000584607580321000150348085000d000c495541c0028003002800d0341d01c45401600c07184410075503c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 439382383 1250 439381133 439381139
    0x80702010c0f081c18030302090103020c1e0d02060c0304020f0d1a0a05090115030b0408131403010c03020f03070f022401170a0b0c1e0d0207020f010f0e0105090612010f 74
    0x1c0113200078507401c070b200c5c81c00040e00c201c02c0400d2114082035405080050f698245000101e02a102d182c2151441d8480c035200b480766070011102d206110245402520003c8110380f400b2621030343c098600c0d14181d5010b101180140c500300301480030f11800244812440101d0350b81d036090381c0c540c04c04244000309640c8100715800c50703940246030b405501c400c02000305114510b401001c1c6070306404060040134140001400300001c100894442901a9061441c1e10f5524510300d0071020042802500079420f000d9030185076400307802a124a20700754000c0070708607a0355000440e01a40200081c0c0c085208a40c0b071b4803481c606490041d081d40d081010421215814080350480c9107803100c01c0f007103036540894442008a0481c1d04a190484418644c1d160b07039001146c44c0d40c40010142e2240c00244000048000070103200f6801001020b00c00da4000040f6141400151107005594000501066995100c0305140d0710410042c002040d00518040c2001120041840c0d0104241c0084030500c40e851018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 439383633 1250 439382383 439382407
    0x906040302061b0a4508071406280c0507050303090102030708160c0603090302010b15030606070311070314210f0d0212040605060414060904080702010c0f08 69
    0x2143e4443d049001d5200a1140c20b40c0c400c03a2803003000c1e01c1400b00040d011410920003445203541642d00705e051260304000b102e000da5091942001d003211109034480c210001042040070510070126510021991840c464040501003d640804941c1c6040d030381100300020001c00e0851010401d0085d03a48848061000f481c4c02894a14550000ca01c07a40c4144284040d50b80e0000032114056070100441e6180c00172a022841c40001c03001000f8805541c43d400410103590641c0000c00c0240070360700900204024809100082d07100074503680303c4d428204001100350401c0c1000380041d512a2501c0e80b28040b020642d941403c0054000b03c40c034080d49280d10510200421040307410310b0150b542004807215025144005100c1d0354205100040701003a88c0459811784d60603262034110b40720000d1140c1c90989013180090804851443c4104d11f00140c400e0742e2048451802c0c0f2610001d48010410340b900d4458480c0380e003080138120b0400c40a156003100140040b240c000b1145c0c811151581c44861803400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 439384883 1250 439383633 439383643
    0x6030602091302070b151c06051006030515120a06022a0d050405090c1b0c0418023703110f0402161205130f090b0103020702091801140906040302 64
    0xb80340011801484250089408059a20f070085100c610b40d100540c0204046500b00000605029450198403030620500c0010f804c4207108800304642c0d000c0c3e003516018180c04541080e220844407072165001000d29041280082400c080c0c010211180344135103a4503082a6030000180000168400c0e292410018100303501c10701d1200f550f00503162102841d01c00078040d0155218491292500f84e011419103007030301003200c810a101c445051814801c001000c1e5071400144201d90141d07203407899040301c3c001d00b203892080d0700c0c0e40204940c0c0b03a6150202e400038000018854003405030409144102c00c03030419041203000b0752003505003184845803001084401520a2001801a80100105803506580e2a01e0200e850307400b8021442038440c107001221180503086800088510b88800032604140f440c000004642d14800107011070718040c2c0044042c0c3c0038000000303420484980100d140700c40d910929400815124000244100c000c03d43e44111990179203140c821b50f04920184424154144a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 439386133 1250 439384883 439384909
    0x10051e121003035f090a090b030c06040e0f07050f03010b070f06051e061002370b010612090b06010e1201090308070908011509020a11010603060209 65
    0x74001c40d80a1840d200940b80840107810480200506416100022541c011592050010134007009600022141100c000031403014405450444000c00140d41c2c3c484e031046407111500a00000d101d1458008000c02411000f0311703484e030602500c520861191151000b03000102204002c0712402c1c140f41e07602844500d40604150100703d01009224006000403045a04542e24402459035490701818a5204401d0f4807200902140c2000240704007403a00211582a03005070b1090303c003550711044104040c5400c1c000115001d600114000d503840c0b034106541420544100321018408481c2403409031220108190445c1d0082003040140503050b440207404070716020300c2c03008201c1e00c3ea803034840c03850480c00108042d0402c905412030307040741d0311441c95500100075148003d003c03842c003a29016000c42c01c220307004400107030345080c00203180d2414050352038904031881c20281c000c0e041c4444680a0750041180e4024440c1544000680c9042403042000640c06140c0040e107804d1480c0c100902c1c030070414 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 439387383 1250 439386133 439386151
    0x160b0c040602030702060a1206090204080c09040f0209070918140a0b0f1003060306050a0c020c01180b070206040819030e15040b031510030902030c091510051e12 71
    0xc841070010980000840c0da420741c0490303405482d0320f01a0310403100c0d0085200030700c40709402d10f6000a0004401d0b00500142d0707901d54252a1f0360318615050204a81d030864020701b8100e0400929809420514000c0790451001e240c514803560311000d030818020364211520030300590302c9810810b108440c01e00260003a04044040c4240c00e4180001001243c101070264072542c51001d001c243c880c000c0e40844010340d80300c10180b041d4a40043c1150081c0008244c00340540035000c500c0103158070506079401c40080b201c40606c00c89041c00b40010403074004010480c5c01000411004c14980410050b000040080c215005601d00d0759143c000c2540b0b580b0200346024080003500210212004c10943d8107981845042c2a06d0b43d039540200030308200d10380ca84c01d80184580c0c1c10200e009905400c02810980254101c0d40344888441c10300c45140e00464800042e44510402102c00f4078004036001110b8515180442c00c003c1d58180c0d0309900d04011581da070507150001070603000c408150104a074070580003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 439388489 1106 439387383 439387387
    0x215010509162d030e07050607021309020d0f050c13110a08040213020c0607080108060403170a0b15090102010f050c1b0a08042607060e0f01090506160b0c 68
    0x240c2e8125618007549030b0207d09403c03d242280c44040e80545124011644c0c9a1090300404440e01d00300c1c0c1c41400010303042d0100700084031419609001300080c0280b00c483c20100240d0007500c1d603c8955240c00c0c114110120000201601c81c0304c2c00038108250710f9510303480003070ba10004021f20120f00c02d02c0814111170841c00015030510441050322140c01302d9884103407850342d80e2011100200094141c40c10192114107064815401091440c408108081044001000c490603802600d00031200866180c0f400e69090081c0c0c510800c0b150001c114604059046d01d03101c1c0b0404c8090359110013440585001140c04014988540340c02ca0400e544454a40100152020350200102ea0b10a00c298031190368a2002c61068101ca44544803917242100b500c090208a01c8800380c1103051000c14100000c041e26801d0082c1800d40f4851140074000301d0318600703440e04440c09025202c1c3c80c001 = true := by decide +kernel

theorem cover : BRFrame.Cov 439208633 439388489 := by
  have h0 := BRFrame.cov_init 439208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 439208633 ≤ n) (h2 : n < 439388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
