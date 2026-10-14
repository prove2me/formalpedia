-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0113
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:54:26.710001+00:00
-- url     : https://prove2.me/submissions/3a072701-93b7-4751-a462-8f4f2663446c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 20143891 ≤ n < 20323747 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 20145141 1250 20143891 20143897
    0x4140a0512090109061701140607060e060411060a020705060a03020d0221060d030e04020f040e010b0904050c0a0f140d15030606050405010521070506030405030309010606020c0a0603090f0602 84
    0x4034070300703015903640320380342c0010450707225036104070100419a00c1240c0d001003000307502d904580c003862014440303e12401c0000c420b8824000700502d41450440300c00d4029038040b820300d11460003082050b0508520b44284199071040320b40c01c00040c0c01504045c001460b1080203400700c07071a1460014100803601128000302e134014924481c03000440381c48400e20500450445900590a82c1d501d41d0b041d58903075020308600d401c505001d21840c0c0100d046442510150240c400501043d5510705440d40c3d00d110569456018440d000c0c022400c120000720065191000c45010100300c0c0e90313812040705640c004441500031b0600c002070901041280780c54908881c06942071030040d01c09088092461071803e40200c17100c41d8405401203003010010070260740c50501c010036024100d800c036100c884142918038201a070700e403c1f040c2d100c803010040c0802e121000000d18400c04040c0d0003000382c10f40310b80d0b059a071200309202981d40300b00b420b4410701c01d40703100713030403030381c88144110002c0c4800840342e5681410380e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 20146391 1250 20145141 20145163
    0x1a090a06020c06090705010306140105070807021503010602150112080d11030a060503100603020d0201050d0608010c0c0209060406081c02030903010203070302130b130e07020312070306060212040e04140a05 90
    0x10f8008000d10503480c0313061040e000100302c00d0800b080407500d07100080b400740001e000c02d035051020104140c03003400b20040c100c900c0c490740104094150404d2104a08281d0800c1c020038005100c1c0303c03c0004882c040010460583e0503001110201081ca952001711702c1e840f03d0890001961200f150520f2b481d01c1c07034003844c0510810a400b00b000e82c109418585007030700ca800d250704400e040600400c0941c4406800090070b44d02881c001d9585d1101100c088050320455100350f050358078002c046505142d01032021892584211240000d0b0345511042006136211405072000b02d4005486806806218160045900503580166810512554002030072608119042004a50006a00c0d081340c06e070355800102038400c160700755040005203100c034000e000c0c06005d8101080380e01d40100310710394003c02c107844403070300c0842e070303038641d614000c840140900000d1003214094450007000105a40041003580e00380c078000c00d0710182954440c3c03903050141c1d08503500f1003e0350288e14801d00100d0010300841000c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 20147641 1250 20146391 20146393
    0x9030105180d0513050f0d0c030305070309050303030f07050306010c0b0f070915080a0207020d020d060f0605041130040b070f081e150612090f0a1a090a06020c 70
    0x201c00c488103454108a81e03021208200901003010b9075070341411502c95001c0e6036056800541d601c0103c0041641c00040ca640503120440c1011b00004040e0300c0001001c2c0700307121340d64603142c0e241d4400502d80d4070b000c10364200030038401400010b0700c0b640c030620181d544a9414540340d18100c526445003001c211040d610300720301003134240400c0b00482d0480365a40041c411440d09611504000c04000e10300c09001d003180030b007290006660419076072402d00080c2d100760010302c20b4603840503910b0075400800c1142041d40b2001d0505000207440d1400303101d845c2a03c84215155403600038400802c288100081e5060400095003207240c41d0503031341301c082c0079204503c44c4901040360b0401ca01c024100001025006003000b801104100d11012500b034403084000b05050f980c2c10030784480d44441e84640ca01c010b4250010340104920480b0640c10044c18000c0d0400e1041e80d255640404003075403600d901000c0506a40c06808031a2100003070220055402a182c0080c0c1e2003000380e03503941000ba640804030410413 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 20148891 1250 20147641 20147671
    0xf0e0105030d0503010501090b0703022a10020105010501021011040906030305070c0801090201140703091e0504050901020325032007062f0f070203010606050c060703060e130302010209030105 84
    0x90742000c0020058040560810300d05661410000911101c8103006070180360002141301c0c010140204000d0101c40c200b8605040f000c0c00b101022a1484a45802a40300c2c00b5036100e420350046c0184075a9040c1c54040e0b026060348400480848040c161401089040c1d40041100007013402062007000051480307595255500c2c01d8034145101000000c0d0482400c030f924000da140c0042c1e800014060030190701c48141600d40105080590b81c51105901542c038a51800c002c21203540d502c1d022a00c15502e080b20100055110f481c641800c0303010172070340d2803000d030200403c44c1101e415141c034481a101c01480d011a910b03200c03d051010784c052515440b07103920340200d0b01c003041008500802401c046a01e0030803403565807444035090b905200c048440403a15000581c7d41e00c0341e880c0021503034086d0700500244411030341c03040028842d80c04001200c0e1280103482c045020301c4d2180c082c0380200c0341030245440458980e20541c40d00480340c044100d06540d820002c00c051a1421700402d0701c40d580045080c0e85c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 20150141 1250 20148891 20148899
    0x608040b0a0c050304020d061803050309011401080703030311041d040b0705070209040201050c070f030506010303080606040602030a120f090f02130e030d09020f030307050304050a06030603030503040215040f0e01 93
    0x64104028000114072424040e0750400c0c968070400741c1e41d010303404840d003910030b24050424000410480383c010500e0002c0640000515801100550295225034002c000096903050360380503d02007070150401ca070f00808005c1000c640300350030180d000008080b60510b09070762050380c0d83e070740615a0300c805d040c19100800c000500c04130504640e40501c06040081ca0100180d0001d542503100610003411b103c8003003200e2040c140c04010380400351020700c898440040d180d0030b01c282d48103000d00c800c80000321410006241400c00c5004c0c1d030122031840c0c009505080302c58105458205004500b00ca85a07601c00001d11140c81c203000e0030303c5260281300401c0040000b801070000c100345c24206070590b80d041a440e00000a000003c85503600811030340058512102d200160000310841c1c810395051101180c20340c1400000710080007221012100c40e9480c40c2e640701c050b001d0310361f148030181c04280188000303030142c18074421045100e185010611310b010b4407904410143d00d040d400c122a04400400180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 20151391 1250 20150141 20150153
    0x70807150e0901050f0409080d090303140105150f030c0d050a0e0d021f050406020705061e0603160303051612030207021c0f030507051006091b0c1203020c030f04060804 74
    0x102041d01c01e07200c1c1c440720340c10301000c101428240840680260b94a040341d200744020203003a11000f10342540f040c44a0b10aa00b4010090461080c100703403098026000064940740038404403c0e15929582c016050011074000002c03da0002040504c081100f0030003a40305100310710400e1300ca070641c0e1100060010903d1051480c0c0464000c2c031a0035540000b05a0f006064420558034004030301d60340214184da0740e89400c01c042e004802c4002d00c144035900a02901035082c00e8900b070b18000c00c01e820401661000f0805a542505881810800400f1141800441e206200420b03560f001c072900300d040d050050340d41199001c003901000000940c0030a20000b1850018140700000e0030a26114200403120b46070542d07841038281000b02032010008a0400b080014844000311982805041240d240d41d200050302500704004003990303121100d4032400405000311085030580d41c01145132030301401800001d40096106801c020070f10b01c801c0c8181c90300041d5010003000a49403d569156480c1810702c0e00b1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 20152641 1250 20151391 20151407
    0xa0302150412290105030601140a030f0b0105090a05010608070804050a0b0703051801060b0405101b0506060a0e040506010501080711010203161b08030403030c030902061801080718050d02010207080715 88
    0x2083c030700d1140c0401080559000241c642c1942c0070b07081c202da01c00c0d404070001010342907079038401884601000e0b034601c1401030180100741215026520210301c1d940c0ea040e9903049440901440e00031814540100e5412071003841c07156481f80c440c004603010f41c401c544885000500c22131300c0b640001e403500c04002024030450540d12042558400900c09075080c5440c0d11402e0082c2e004c0d1500400710b5250281103644103846040d0034498904040c1c19001d041d0610301d4941d5001c68103240901110a00081c0318150405910b03c1690000003810700380c1d00300307401110002c102800c56400c001c0c0521144c2100c0c2401c4c4000c501520800c03054100307188241001404803150a4645441d843d4603000d9840402c007103008580d030003a410702c1c001880408180c020360083c1800b4802a4119101050325990000c1880300500076803026243d9054541e10902d0440e01d01151018241418180000030001403d01142840d04c251050042e22202a01d94100d05d00c0d10f840d50340300101495002070b140b81e06503000101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 20153891 1250 20152641 20152703
    0x10b0a06090509091501080a170a1d0609040f090b01060203030907030b06060d0608010b04140c04030201030513060c080415020703091403010f050705040e0a0603020a0302150412 78
    0x8426414605000a0180d401c82e00c42c85024600b0480000c20311002400741c0506040d10300c102d00340658454010b20358440741d1143c100c803200e00c01f20f00d0021105182007910ba4000040c1d171280407070340c841d08a203100480c8880c40683c0081090203860059521070046100044100000282c00106400c001e50800c0c41070b4044410740d0001c000380300020030080f81c203909030b0384c000519050644030140410358501c103444440055614001010580c2e6506400406610000722010b2002c107071103010ba403034941c20545141300226010002080154000d8201503403002d008401e0604a00c1d43ea22540e055481e01000f100014240c0801c2000b0040501e4080b1002c000602045090080c686c1e005020042c0600480c0a0320010b1603282c07079940da09401091588514040500050a0503800a80703c1c0c0c1060043d230ba480c800b54400506030804030b2003580c0c1140d4000340303008270607031964003400001503070043e520807070410400021407454540100d8500f80c5101303220342128010315004100391880b407142 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 20155141 1250 20153891 20153899
    0xb2805060901050a0c11091e0a110901030b06070209040605010501140903070302040914070306061502190807020a08070602060601110114161205010f06020c0303041a09120a060509010b 81
    0x41030f68004155072021807076050545101c50305042221855001d0b0124907030000c058003c220b04d900700d40c1c40700251810386810400044d10703404410020b9982407011151104414810b9505640c801e8110010040001d490b07107103840342a40102c0d541c0c9108480540d2110b0b140c20040015507800b0790300310381e0307084003100d6641000c0c03c41001079110091448040d200300e88820080302409031044070b17005442c2e000d9088610881c0d880c50b02c000034001a101d0000c00020f05a5039600050000c034440b008156030004808050740c182d0b54a400517009400282d0300101c0041010480201c1001520013034041600108218a4440c00042c9521600000d840d1143d06109055010100d0070701c0c039541200ca03c44586d0841d40a40000b224241801c0d42920745050034170000040d0080da0401c90341c243c80e401c1e400e903440803d220050540d20322552080389135070320701c1c0401d04c1c10349648407001c2c2c102d10070002c1c9074020100114441c145415000003042d01c00f55960418000710040c01d11901c07610880545d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 20156391 1250 20155141 20155147
    0x1d010509101202060909130c1202010c080a090b040311030111121302151209070e01080316020a05090103080a0306090c12050a14070816050f03070c03030b280506 71
    0x40000304000d40c180c40342c07101a401e801c540100319030310300b01501d4075204050300404503894946040490b0110b80201525000b40c03030304c00407543c40c40715000790407402d030180c45580551030307242d6030410654403900003078080004202001c00d1001100000304000c5002e40c2c0d1b1800d017140c00100305070031503500201c216081c0d90f04214902560700d903c0c48603580001202c410110860b05d0b40040303240440528210a4099000503c65005609079016180202031160440d80d2171612007214000e045001c0c09a031010f0303402031000c03564254800d42448011880589240051a55500400c00400083c1c004458802c1d01060501d2007641c10701c00ea02c0180380360704081c8040c00e009c7c00302809181d4082070404134681c13a040001c600709401c2d08200c00c400991010700040e80b43c1040d000b0045035064030045003180d1100f11001c480d82c42403043d80c00140250008070324503218640242c484400f8035008806241d100d04e010259982d49683c407a426011a91141c2c81e0300d100a0406662042e4507000188202424 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 20157641 1250 20156391 20156401
    0x10903030e010c02011211040305150906040b040807080703030507020c030c09010b090a0305030a05070308070921020d05010e070602010c080c070f08041205011a0102010b090403051309061d010509 86
    0x102400c00c0c100702007030802200c6450140012507080340380580e41d0206038103140e4860b6482007100000c1c030440340030710240d8202100d2500440c0c0380c6402a60300c09015484600440c002c2600c09040d50b401520500119140034000d681e4621540c10101d800c0e000319031781e0340800046039010300c270308041840100d000d880c140d111342e0b0000c0c0180206004010304a080070840202d036460708600b4001442e00b00049a4560364100c40c01000da034090201280003d0000c80800c6426005510803800e07074007503124041103066024819034150603440e200b6a8070207100701d189804a0f0b401e10810089600e00405041a20300705003001c0d00356050b84000d1740402404a04100c5e65298002c1071316a059800b4001ca000110b89051081d81800b550304a4000341c041464404208401540100c0103283c0c201e5461041d81c448e8001a07089940f0381c60b0b03058201c0190000030700080e1150000b0450b02810111340103003140c0382d05010044516030380240307807044aa0342400072101c40c4c48500c540140b004954001480c03410f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 20158891 1250 20157641 20157647
    0x706030c0e0904060e0c060c0102040f0b070b0a1107080a0201050103030e1203160302010b10020d1701030b0712020d091b0807060207170a0f030309060b1c08030a060e0103030f0e01090303 82
    0x2c000c00c0680000e1755100400d6240f0010b12040f5a002d000404d80c3e80c840111707441c030318000d5015104d507050408984000280c0460b4010655220300d41104038800340d030340c1c0d100d4080094488450034860400c2c1c2003100100081004001d8004000710b98000a225030451078060180c4450542041c07240b0742c000c1400b150004000202e0340c0e100100001000c1020007481c00703a014020950701d407940203c41100440c1c4842d400108510f035030300c2d107603100b0080c0c040c071006007042001d0a01010705801803410001d200b060180d8000703204503407001d4006151180400d0200102c50b01c0e001c08079980d464a002c1c805480d1702980754103010b0b0140d440a002500e2401101030342d261203502c01e403251310a031800e03409403800701405407203682c98000000c0c00c0480c419103401401007544c000103d80b018a00605100320f8140702e140501c00e01c03210072082103c2502612144031507000100114120340d1a03c0d030110340e110b81c0401c501c0c0214484c1d281c0b04449110010082c11224007120a0380c10001c07606010800300764 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 20160141 1250 20158891 20158909
    0x50120090a05240708030f160503010302060307120c020a0213020306010903020d06150b04060318030806010518030d0503090706020a020105030a050403031d0d1409061e07140706030c0e 81
    0x3007201d001e001542c03c94203501441d5520100c94801200115130700341400f0414005607c584c9815132111034a030784040319248601c1c142c4944600141c0144014001030800000558108001f81480c5004c2c0e54400d02c03600c151100d5191010050304200300e03001c1142090840c003040f140d0072070004c0d8218a00180020001c0440d4030003c1c1c801c4000b200f00c1c0040c840581d0014415584d44201e401201f41c443c80c82d1400c5031f0180c400c00340080d181c01604e410310100b8aa6500209a06907644003558481c00d004654540100e681d1000400440340608610764042042014070301e284d4542d81e44914020712018240341c0340e5402541550040e020803801030f84e00c001180d034000ca0040001480d40c545003412801010560015601e00d6800a00e0100788080007a60402c260b5141e690124003070046c1c42a919075001d001416030b0490802c0c800c2211450100d1144501c02800b0301c01d003802d1005a4a40c0759069019001007865600812801d118950b450700a828104420b41008480c1c0f00001003c222412 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 20161391 1250 20160141 20160149
    0x80c09011b08030f010302011101021315020106120501061a03010303170406091a04021302040608041106090a0605031902030915040222020c0f0105190b0f040603050120090a 76
    0x48805400d07504100c03100d008080250400c407007030f85901d0b010307280140d10902804164007080703002a0a00c84c41da41402251103000c030302c54105144074542004089c04401a940d018195500c44002050130380200031150180743c05040041070142c680030b0301d400c10760290700401c0961081000180003080d009000c2400925004004880c15510b60a01500a1040000c0140040c00b070f01002100041901c1d80d00d40246d00880c1c0300032030a4851981001288a40d100d0380300804c45075000036006c2a050740310035443c1500035102525001004c03001406039401c81d041080032480100611004000000d51030b003000640110840c0307503050184940c2e44d100c130740035810002a0200000941192903a0150b4004d00c0840c14400c4414810f071248900a9000351800210341d108007001d001c1c010a0502a03203005000e8217030142c841109600300500a44a00e45a20740c1081c0f05c0c40d0016400c0d1558441c2038001c5000d4400005d1144400380e280e0181034460310f0341c1c03040702010300562402d5660568090129 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 20162641 1250 20161391 20161397
    0xc030316260417070305090111010614060c150c0403060606020105040305090409150216051501030b06011101020c030f09040c030603080f090111010c0f020d090f06030506010507020d050d020d080c0901 88
    0x1640c0c0c41c41c200100510782c0c440800380203c00b10341c0104040c2c021002d444101400d0700c69000d860206a2070600b200ca01e441094080300c002900c11042e42040802230007254800401e580403552140024403844109540388049407400140810a00000344140401351216100a00150619480041041c000c1c220b4640c8610b50b9292100200075070311114500c505410001592180c6141c915900848050030003034071036000300c1e003d6482c0503502090031416a54069181600380d2035400046504641c0d0500b107080b9907508011340c04485201708040e00044100300541c0756a40030040a00080d03031010744d4a2414541003407014400243d6801c00c1e07681948441310601d8403600c000c00101c41d900c0b40002181155440c0c102d041c50403d5221204402110054003226002207011100311480d200138402c0f244200454542801680d00c07941005800083c1450501d04151068001500da81884001114190710420344000c2c100c0d0144030300c1c03104070301c0d50800303801030300d4041c40603c02c501c94201d0039410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 20163891 1250 20162641 20162717
    0x20c0f06011205061e0a0b0d0c09020301090e07051003021b0106030f150b0a05040b0301020717130e0708070810050306160807020106050d0803040501090c03050a0201030f050601050702090c0f0c030316 88
    0x240780c07556000706e501d26420107274040010340d031850103c000f94002c9c02070080140c03c146c81c58100201c00140113040390005024860b00d0706d1250801c030007c0d0011040d0103a0a00701c11030340c0a508809020740000b842c0100d08905140d0441d1800c40029600100c004240b030703040940005035a038401464204903501543c003c035403009c11500090092040c0c0d07100504200c2e4403106001483d0480300038202c80602940803440e09a194481c502da00d59003140c404000444040002d080c0c036100d000b05e5034024200c003002038003194a54002a0400f20101c406008407000700040a000591040f445038020200c0d0008008036414000440c1c15900c103070101900e0f80e000003021400b042000d602c9207040c80d802034010220700e500d80c5030142e00c44161030800e900003814101102180003507889494040c04058551078500401942802805d6a004000007052101030125520050b2480d005100c40c500e000040d40c1d40b4500307200c1501c5000b00309495803013040a01c00f8039440d900c59801c0003003801d41c4001c0c0403103d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 20165141 1250 20163891 20163911
    0xa0b06030106180f0c05070b070c020406030609030c0320030708072a09050c040608010e040f060f0605030105010806010308040e13050102040608061c08040603020c0f06011205061e0a 80
    0x8050450340d80590708000900c0244025141e0320340c07100701554014413003030041c9080a10210355600651001170f0209030078501041b445401480e25265591010b40082042c59503500c03114125916103130181c01050503801d0f00410150300525100c0700d005103000f4039407072000d0404281e41e13900030024000c144082c00070703171041801042c0081300c0d5078401c000c0c0290741100d4030001504c116034503485485c00143c05d100108120f401d40d001518160340c4143d0311083e20f80c0c80e00030b003903641040151003560403130070390620f001c04075001d07000d10b68010300031260104049142806140c00c4a1059100301e01a4102e00700600005514100722400c44944e880e41c01c40c2d940b511911950040342d10540100690b100141c0040d075a034000e802144034410071118600040e0070700d44040540f100781d4400401c520410002481224060390203010300d00d0300202118045040c5403500c0386890003c1e0840ca03500c1e0700402075401002030812011fa4844040e105000020a9103110001c031444084c080b00c0105464a02e400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 20166391 1250 20165141 20165143
    0x60d03090801060f060f1403060105180409080301150c1a070212030a050f01050303070c0306110904020c0a0501050601050a0206011505070203060703060602010b0a050904080d060f09020903010b040e0a0b0603 91
    0x6409407031007000030050181e03180ba400b418003800d442280b021402140d4030504050081446d40c2c0c9500500001c03d00e03591740c00004507402c1d88229011220407100110a076042e40b16482480f40c0f030b80c07103500d42d9036a0354101100030703848003008004c0208110100b00c000000944036540651250105500e02080b070301e0f0707420243d04080603080814007903000802042080d40e00f50b0031190059035418075618960b601d40042c152648240c076406841c01c01080c8040000802c40d43c80281603040e2507036003504101101002030b059034451a41292079510172015913003488420301c201a080103007420607502e0f00740041406510b6180521070280840b11060400311000d0085040f640d0841c1d004080d52154548644080d00a00c03560107200700540c0381110740403190602d060014152140244010741036500c3c0d59864229900c096000b0740003a0b100c0c0400603101d00020940400307040ca035800541c46194440c1850708544103144050f205c6d505008494600590109054000b29000b0507040c58566406c8046 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 20167641 1250 20166391 20166407
    0x309040b0d150f0c0309020117042f030708150415060902070303020310060e0a03060e010902030a0c0e070c080d05060103140717010902070809060307110d030506040506090906060d03 80
    0xd403a61404642c10410300c40143d111002e000030100042048110b1160202c00b1a000e683d8001d011402d034020132080c1c080d060110340c1c0d00511a40e03450a00c80b001002c552980c00d9203604440d074015408050855600d0180034080207400307500c0c000d040100d103500b200f111050000d0400341c204407130a40500c000704440e41090001d0914a4000e40d80c403940c62400038002d601c12500490300201101d00816500e1003190b45811843d0000c002c000d2231411622a00300505101c031010595659036042003005032010702c880720009000b8a1240d01849c23400300b188047e160014800d500b004034184440d40003030000016509401c041103400181e66440800680c001d0102c01c4400c0181007540040005040c1e028990880c1c9d1240310035200300c41d981c2d030400d401c01da004078000105401c00611103144642403107000346500c20f086241034201c2e007142562042c101000082c01000094842c070802c0710700c1c20036016154104005036900c00c0c00e4a0030618440d101c0e90050f10320751003000c1034007168003410f1080c900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 20168891 1250 20167641 20167643
    0x30603050307030e040509010c02031c0605030d0306060206010b03041703060303130f090b0405040206160c0b03040303020909090c0a050114090405100503010b09130b13080d0606090807080309040b0d 87
    0xc4a68a810310f0078080c001c1d15403d455188541e04000006840762018021151281950b4000714185000c400c00760b00d07500303110710001152a6403200d000405503402c100914299403941c40c0041c010b03040c5a0005d080c058143c0100d03c554600704284800501d890303000c1d080c0700d0048040107481c0d88402000034118420f503905000f0214480401240b0980e0303903001001101e01804d0b0802901c100300b07080c082501c0080ba4041e522403401c0c4901718034481c0e00d81000b48a42e00c185c400c0c50304551a0b40000d00e05404c159425800641c0c08900304045040c2400190b4000e40c08400a0044074074250004000d00414001d442c1009942e01044800000d180f040d031317090f00e8000703000b40300701d151020480c0b02001c203d1142034400c0d8280307000712070070f810040c1d002030045046c207600e81c403110540c0d264101051409071140d0480d5144502000200f080f58001e8081003090520204080e4a49100100f100b942d507008003003c0d8010020400c00703031200004403191200151804600d840003803000449809034650 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 20170141 1250 20168891 20168893
    0x20d03090e0a140901060b030105060a030605030303040b090c09060619020709060303080a050604020405090c030603030f03010306051b030114010309020d0605010e1b0906090d02030c1f0207140d0305070303060305 93
    0x80c0103800109401c0010b0340d580060f40d140d01c81d0380b1000c1d66800e070b90261080c450213a40c200010b0000f42007420040040054a0901003a0a5a5180031911390b0340222816606003140c0740602428074814000c1c54001c1c2000ca5442441e41410030000d03446128525a03a00c440340260f019001450081c4240d02c01484012010006140d4070304028100110407652080704602e08000a408d920307080c4203880940c0d8001d41260000d0f505c0824240899001411590b451f1106000041c07102400b000254080d52003000013003002c1c00d16508526819000f400e000b43c000d04103100500444480e000c070f8868402092070007040c2e200c0240042041c0005515000d001ca81c100000418203c0300004801d010340442c0d20303901005003138000002c8480c014100342582c4680108001e510300d00d031200302008998001419250854034030400204540c4034901c41001075446041c5840225405102000c020f002000001440ca40804000360380c0942115000f4280600820f0050915100b64890005594420 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 20171391 1250 20170141 20170169
    0x3070c020d0c0810050105040213170709050115170603060a111b07080f010209010203070303050c0c010608011a01090302030601030201050a1e020309040605010516060f0e100e010e0a030804020d0309 87
    0x304009844540009104c1c6482d03003040000a0207040910032242c0368042a090601d80c03900b0400141c08200e845181c2c403000384a0540c0124103803039036115a034003d1001003c00303085110303801009840045400111440c482483d000c0107541e840c04a5100d50012125000046c000f4a42072210000c0c028030800c052505110444411a007030000382c100d083d04c07050001c40f030105012402d618240e22441075510f0049e01305004000000303010383c100340c1d00845841c80b40750a1440511201c1d003100c405034420a81c41e034654011461741c1202c840f9240081e9000c1c604085d20b5412341d00031a03a1000c0620009041140001d0828080c912440b00049062070304000d030f0390007103048580250340f9049088102c0c81a4a40000001c5540c011000c031200500340101c0340880070560303201c003401004e40d00c0e0360b00c0d11030391a0003c3d040d000605220091000c10034240000744030604002d220300f1100480c403001400d501181d00b038000320703804c00003c40e4040e6044807600e00100082ca4125040c0c03030113a1044000b00c03000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 20172641 1250 20171391 20171399
    0x80c01020a020c0303070c060e040b0303070c0501030b0109050303030103140a05030d05060310020a080601030b03120f030a0e010b0114070602160302030703180f03060e0102070c031a060402070803070c020d0c 91
    0x40d0020145449150308a5078101814800c15031240b00c2e0190003081c882003400b0400c461030248d0001d2046910084c00000e0200c0c0c044042400c5611403031003100c0c4590250300078000c41d0303018452944401c1e02880c14036401404d00c40400c0d82c80c40f040c08094992040d0081c410b0100404002441c1c2092340001a251901c5291440c034011340f20517181d01d0303c80d00800c9917203890380d4aa4826035149581c1541c4140158550710015401046000c12180e058081d0007080c0f10100070040040c10080c22008100b652031400740c84a1003201d603269107094080c3d040a098800c02d03a03102c206102c0700d491f2601d80543d00c03856445e25400904c2008240c3c4241e60b070310148481496000300182001600176200c0e02c125001c206100910380741c683c011002c915004040a1000c02c1c041d030700070040300721007c0c0011701d000c1c102e860b06071204445500c1141e001800d1143d061132200259240764015070150b0b019801c008003030b9a480011b010044c204000c00011003808000c1d5914140c007486001d801614032144107481b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 20173891 1250 20172641 20172643
    0xe0604030c17060718150207080706111902030a08030c0c150103050d02060106091703070b010e090f03210415050f1f05030a020420190f0813060c020703080c 69
    0x2011070b60040380e019040009604038003071081c2d90031106002e51104001170910074180d010000c010101000c6200e01d04006c194241c0420840001c0d01d11a2685031042c6019540585011b5400350250b0000158101c1c0a0051b200050103040703075a40300d42019205d6580310410b00c83c2c0c1c020f690040c1098894503400847c0c0e1400030100e01d0507a0b002d0401da5842076860f4805a0340c40307500b84202c40c000344043d4020400b00c07010002006582988109480c9002401e031a42e00e0030081c01e0300507120200c4100c1c14044007042c200302d8024004c80d082c0c0030350300340060040b20190a0741c2000499480e0708580e00014100a200c80e42d018416241880400550a191580018050040f9000004160700604d071040d000c11070f540340011501c0041c01032200300038036400e00c40a0580c0c6440c0f4860003c01603403903080c2e034604401402550104030300000860702140380081640143c41070440030721124030b00340300e4000c10703c0840d44071103a00400040303081b1483c0c9108a00d006501e50002d00402d0011940385c0c1c240e10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 20175141 1250 20173891 20173919
    0xf010c0305010e1e06060c03091306050f011404060c020f030a0c050f0a05030303010504020c0c0d03020a0b07030b0d03030b010203040f0b030907050406050117040c12030c06060906060509010e0604030c 88
    0x3203440c50603c0a41d071300c4030030811079112118054841032100f40041c4041c078004009058107039001003074030300b8521090041840c00c050320903444071080d1540c07010700582c1080007019070404000d03e4048503840818044064070700c03560180c0000c0141c40d03c00c0c00b0554880c82510040e40310044d040b652040700e80d0410290b226024010700d442a641c9041500c007524045080b54203580340240030b180740d03919040801c4020b5000c0141e40419024440c05200c80f40d6424541c0000346000e90003805d85103400e45071085160308001c00c94000d040c501140d49242d40c90784480f064840d54507090016854030b01200503032560080380d00010341c8022105010500d055500007030341c000e801a00880d22a20384402c02c20041e1640c6d80561030000f403440d41d020b0142c0360141c0c0b9403078003d800384d01511007a0381c03101d15103019912003400c1a004269204008410003201e8072400d0000d1440c2030007007021a0600400924a00c15183c1103410040d440400e514507039150750869008541c440c1c8a1400c49030740380e003410705d07000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 20176391 1250 20175141 20175149
    0x702220b010504050102030a180503030a020a0302010e03120c090a0e090307020315130305030c13030f0b0f071209031103070c050a1a09150910030209030c011b140f010c030501 77
    0x181403403640c51095000740e00340c40907640142c0155007840c1ca000d01c101d030705a014440030540b0094050000403d83c900f88020081a4079540c00381030b00b0741c2c0900b000713400e440c10b0003116549903004110000c10105610104d81d00822003d1203165180301d440006041d80d1443c0e00280c40350086001448034041002005001a5109406903403c4400c040004045400d0031146030009420030b40385540003074403070001107901181c003100b42420a500f4045500925150b5002100c1e541c010390b00e900c003800903150209520a0f251540e00d5507a01c0e264600911801e400c801556a03103445044441c10540500c6a000201d10300b1002c8a032112100d00304a04001ea0f40e20865003c0d05c11900c0101d04813400f02c3d080d0080c140740e110840e14200c004001d00940402c080a02c12541c2c1d01400303a0700040d40c96141c00300c0001081d40c3d0140c0c94188034010503003801120f5005a042c00001c618405880703988452010000740c004a0120310300c001c03a1440341c01d05840012400055281c40043d000850701750b17102c81d06076 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 20177641 1250 20176391 20176459
    0x307051005150a030c050609060c0f06010611030306011409030a021e01030e0d08060d020d020405070c060b040209011202030403031107050601140406051c021302040b03060405060102060f010314030702 88
    0x8082d6200610040c0d001d00d0201809400a0910a102604100c0000c0030381240c0900810300d0088584000c505128150103c451950440801000a903034485140c540108003c0051861400d00303c00192650501c2400700800d070030080f0300c1502c0f59500348289600680c002e001190b04410f01400c145d03001040d901e203240841c2c40c1480ca640240400964803004480c6a05d036640c0d1500e5003410001d0a0190b0034080760700540d6401c08100580301e40c02882c0c0592803603160305140c02c540f8505441645c0700c03205002d02451040c000300e111aa07210b0005030f507a50703150300c0042e505d49450074110051300f8803026411608000280038002c101c0300003a06812100741b00c0249442d59a45410801980c545103c2c007540008404144612440408600424144001c05c4494041d2800d980042030380c1140c4d000420141011080003543e0605000b01940400300b4406810240740c00d00c80e22407842410b00000c3d011004260b000c04480c1001c104841405800800d4401039002d465600c01c2e21048585042541c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 20178891 1250 20177641 20177671
    0x2010b03150403020607080a1e0902010e0301020307090902250305030405070608011409070e0405070302040314071a07080702150405010e030d02070b0d1104030317070815090601020307051005 84
    0x107030400200c401800769916134085c004644401d0001c8400050150049504070351f190030114100394441d04120b8a4021110003103080203950001400461011401d24081d07401003080164003a0b1013046003065500034440180c07148030406401c06136440082c24162605048103105080c141c000e4041c61107248142c0480e50303140c0d252032040380d18038804c0c455520b06140002c8a01c07402c3c42c041c45651380c0500b0501d0140e02a010703020000c0c099640640b6010080303940000c080c010f0041c00d001c480e8140340340a0090000c03d1034102c1e8402c400e000d0070381000f590340002c01c0690800c94075030100e510041c0c00a007900c00703101d41400d559150798007500c1420f01003804464034654a040103d10030184039100d030040d0400500d0000000006c2d07105000035a4100d59415100e1a124503013005080514000c0e13881107003c0700b0008100100c0c01c40030301864140046a0100401d01b016188480040c103800d403030140e603e8070794034010b0f03246010b0740e00000c06900591461008a085c6544400d2040c240d001d10303129 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 20180141 1250 20178891 20178913
    0x8030105090a09120c030201150b030a0c05030f070e010c0503030703060504050112051b0103180602040e0606040f120c120501050403020d0f050403020405070e0303070c051e010f080a0b030102070302010b03 90
    0x8482e14518004c01c1ca08441c0d4440e074605025200c0000000e000e0300022a0500018000e2040143e543d0440c078541c030008028008503244034407a448110503582402e80c5541009402409002e50080000c0200f01c42d21a00080030303441020380b1919503600904583c0c880c1009100a40a088203010b51340c0107a16010002490012540c00314000e0340e04800548480c0181c003410740154604030121605050301c800400c2001403017200c40c054a103004844c01600c0d43c0c10009100640c007400742c44c461003a0707030a0000740101e0341419400011a082c1716810248014149800c0c0e1041816a0086240ba4640c0400505110041d00250712441c42035003580d40e0380b400740d001a1101007611031340d8000920240424801418141d10280e00550141014002e608106002a20350340c850441141e84104150041040d8200b08420030103140d000c1c1219015440c1c140002469001c40802030402c000d00d1102045003c0c0040e805410010000340083d56035002c50309020340a0702a084c0c125010f8454120020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 20181391 1250 20180141 20180161
    0x804080303072a02010c050120090307091103010905150d03020c100503131b09020304050d031103010605030c2803060503100506030c100e04150302010e01020607080a0e03090405040803010509 84
    0x201c00c0d50f6590641114045554004650b02103c0e01021100e5640e038101d413024030301104525802d41c1000d910216a00e0f15654207041c284845588108150750a140c01c62102e190390b5000d60f415542c443c400041c959464410401c0310865110007039401169044401051650200d00c86000c444241d071500080d4180402c22102c0744401c54000080c081041a004006000035644a502d0860001c07225200c0d5142e008205c00c0742d10544007210705520000d105c402d410b4150081034280c0207002644e5003198905040034045210040080011100c0001e81c0641c10880010b88103030b001c208407010a0514000d840640244102c3c0240d41c8030307100380e220039080f6a00301e005a03071050030b014024082955004091004205401b498030092060170b030044617441e101c610a400351000340c8201e60003d945140000350942084415440c1190045410840d03055006648a904205900400148801840303521815401803419150b889420101440240455000510b050303a100b112208440d0b200c0c100301b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 20182641 1250 20181391 20181437
    0x60807020606060d0c0302190c02030601170a06022a01020c07050f1c15110301030309050603040c050f010527040e070303020703020609041e0e060612060402120109080408030307 78
    0xc03a60008040003100131001c019009103010b03007070710300303025082540c0001026901444002e5503c00103141000703075025480c04000d018010495560b001904640c0c14070380e2925040390f010040c0101c0d4000924641c00c4801c1d044201c141c45ca000c0c1c507444011103800c0014040d41c02054081300074030035808041114605840f8419208900030b0611b050846200c0314010943e5440d1015124403605154140550140e4011000d0040c0740c0c0211550301d40c1185406040745106401941c0128410310030000051000841e4100756002182d050801035841d00040f9002d1003541a100d40c103031260811034043c03d81d5580030070954481101d090024495454106075188410300c0003900580c0400c20030009410400c000303010304003010b0404100d40c81c0042c80c010308407444d46654942d860341c0b448014440301f0144803542c0c0180040b1400c001d10010703560031503074915001e48040d12a01c0c0c6034001402e145001d40c00f664242c1d0707012031155120740e9110291502c03030300100e130040086000b8800150f4405649480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 20183891 1250 20182641 20182651
    0x2104050607151b0e1c020907050412060b130603080306040f0204050310020d06120201050301060305070c0f050303060103060b040f03020105090607060e0a21050d05040507030507080a020103061202030303060d0f0204060605040608070206 103
    0x148041e01c41c5d60360200415040c02030845006d01c1010800403822812008040d44120b010702008100d40000030b05200e280d040c0702088034034542c13800c1c00500014828400316900603000312004605610380d415030300000d21a81d4070942e4984600e480c045600d0000ba00642114080e40804000b080e594107100800440703043c0000380020390410042c81181e000341c0c452a0040b11600d4840104416035690b0300341d020810000340c9480d031000c4200101980c2c140200740103811034140d4941020725280b118452620103010090610001040103003e80c2c0740c0005403111590095000e0080c2503682007060b0711156050301c181d84640000803028188030140e440c015904c030040e605c007403030100e405858600405024204036a41d0144a8002020450801c409000380050602a0001e0310240c4005030031160342d54051309250301c0319003a040141e41c001c0180c03030b40003c081c1c40c00c0945030300c01d103410b2a052901c3d1400a5209143c44804a800c50f48000640103681058031401c0d0f11352900c40c0d080e40d031f860007122 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 20185141 1250 20183891 20183929
    0x10209060702060a02150a0e0d090f0504020f071a0105030d110309040504030e040c09170a020a0e1305070b1b031315050403051507022104050607151b0e 67
    0x2240c00506040b03008041c4d040c0c00b0b1050b52400710010a0100f0195410303a98028120340f610640c4501f00c0050215450445590811080c2036203010340c0700c018444c003882500d2045a01150b0350701211145d0088401090b0701948000c0107010640402412617000c0c01500d000384505074114040c01d011305090401e10741c1220040d42441c00100800c000f80c24014800c50410502c8405200b8646850081e4400320310244c407101d034184d08182c0a2088003d0266245030b080d80f144c5005c501603251080300d40151002046c1c206559900e46544150194200c00c0040c1705124a640000780c2c2c00b504400b6150120072940b0b013403140104d201032660b49002c0c920010000407030403a800c010300845041c4055283c0e4060801508241d50398440c142071170407018840341c8038219402041503070765060203001a101580321002118a20180e240d61071030280c0c1c06468010640000d0000030302c410101a07084021a4002c20f0204054103031909250620090440e400300358200c20303050381840c22140e142c481d0001c0c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 20186391 1250 20185141 20185147
    0x12110c01140718090f0605090708040605131703090102160b010e0c03090c012a0506011d010b0d020a0207090903030903080c030106020307020d020a080601032306010b09041e0501090e070801020906 86
    0xc426001041c8589071708a102c2d50381c00380050161154148244691101d48408002d45000c1c00c003002030307a4008000d020320598a8600c3c400060100d1850607000c54401c0b44d05403642d50354040c0b0340c02031190307a00400c80752100c6441d00f8200040300003468103a40701600d2058a5454603080340c64507010554140002d900702c1c001d10401e82d44904000f400b030307140310f60300c02405440b4403603c2120402d014009446d0340e042000140200e00c1103000c00420f090b00740340d6200e50740d85400c06000590188541055074507800190045c5243d100704010f20107009411001c1003400e86503d809401807442880c02c90119499000240082041405803812245544c02031850314050360b0812441c0b5402c007804a034030110484020400603030800c5000e02951141c440000ca450189180800d0507081140c0314000f50301a1006110002140b403e40782c00d00d0381036401050400d0051016004440421581c503181c0b4908800040e081075280c2002450898400588180c00d883e0400b2a0a0f41716001e05640c00001c20 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 20187641 1250 20186391 20186399
    0xb04090213030b15011e1704050307051506010e01020106050f010c061407030501031506080a0f14010c050a090b07020604050d1e03030b01111c12110c01140718 70
    0x96002004590104809000000d489075965074480000fa1034844144000f400e04004950700100701c1801105c0803465801c10498041380149041e40305690b1440c5c45070508003180401800300b09680220768484161240d481d0400d10352521500115a482d0004000f00307090354865006101d40c4003130f55805440505000010001942e140c6204201121031503905c598400d204040303017904074012100365502280a51545c248542000300b59142d08e0303020b034500030080010420000300300c21015449021502d0804590034140c5840c030480385810700039404d1a03206000e850b03200c0005c114240291b2103201083d910380c03003804c03224099038034001d40041c0d0400c07060020380740210010000c1442041183c00f0002c584501c804d0340060440100c0120b52540303080c20031581c001000403040c0e48454010103c0d601c2502e03d19104046000c8040180684890082004103840e00400d51385081645000c1d9101d4109a14900a16403040d0590540c060100801c402c94842c062100088103480090030344103081c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 20188891 1250 20187641 20187659
    0x10507080c07120e0d0606030c030b060604080a121101090309060f1706040209041803080a0f020a05030f06030c1909050f010e0403050c07050406030b1603020a1b06060308070813060302040b04 84
    0xa0130225a80130f500031804000048140c00380c0c0015500c20700c030031105c0626604c0e00a015450117070100d4031a6005010912281400050241a4a0b0081c01400411003000700c280d40d04000d0400c03002040d420a66040e00341604000898201e40169564124500c0a404100d83c40cc9081aa00c1c0303980101101066092400d81c005d406642d0004100242256462a885245400c5108110b010946603410007900c0c404900c5603010110b000101945841000007005003284402080c5140c01c041c5d01010a180d51800c000001142d5000341964500010718004901e8001d45403280c07030401c80c1421300142c2200c018038860381c100c1c0e4041c00c1c1000301352240d6a083d18603030406440340d00e16119101c00003510303580e85e008840c021400340c40b075208681042d003441205400170080101c10306004000365501198051080188030304601c00e41e1207028158942a03014200381d42c005003528402089880900ca0704400a02e0954142d0b41c451044030b40d651401c1c0c06070700807485080b0784e00c02c05000400030300740 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 20190141 1250 20188891 20188907
    0x120703110706202205010215010e070903020405010605040306050c040501090b0307050d0f0501030201030b030604030912080904060308031012020108060409061d030a0908030f070204021317010507080c0712 90
    0x2c650b1500d40b09152842400e502c0c160003102d415001c6550301d800d004c1346100e2108402c00609001e10280c507140310007a548482000301031040e103a03003811020000740607c0c41201d140d009036500400a1001c0e50703591100400380d4200b800150f822524160108dc40c0300042d204840c21203006844064000340b070720050095907000200501c044c030108100e2080c6802e060320a50207503510070030340080c3c03550540c00014100c4541a1049000c1e42c40981807001103500040101c0803a00105a00d400000061914210170b0080360b241da900075081c0807000c030400992401651081200380a800030f020390b91b0700f41d4108000401070180c046584140403440030b080681210b0016402020041044201c400d413031100c03032180d480e04a803d034002040c0c507082980e10a02d400c2c020905e100086080c076403103065000051041c800004d12840d8001101d0408007400c400700801000c00b031094400c1c0b80b2002010b40d004e04001c4071030400083d0840005031802c00398600340c03040150007105030000c5104818064030600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 20191391 1250 20190141 20190161
    0x40207081204051c03090b1902040905040804140307030809210f0a060c050c06180a05072c0906040f0303060503120408010b030619020a0c0209010b120703110706 71
    0x30000300520090a105080d1560296105a000b00400d548031070300c0380c0400a600d01210f0403d030034030303c010010800c0a810603030051243c40a8030182580c12020200902c503903480340611505040400c800e0007004806031040343c010440c0e5030800000c042c03c01d510781c2d5460200070032800741404900341600302181c140d264021500002001458001c03002c41c078020000d80450450361001030040c00704180746c0594141c00e400782c1007a50402e0840e40c03035562220b40080c01e002a0714404031400c00188801c020800c0301c50b03041003c4e070340c03010f444441070070410740510141d0a04504000101d80c040c0c4204030b00c04d01c210000c5000d006292950740d1200c00b81983c0e603600783e0800d078407040041101d6070f080c00915104e003985200d860350390780303080ca6042c00e6035442d108092083e04220204955005101d95418040041000060f0f0750f10f40310400303540a86000c4006034000c140b010020500c5070f5444020310300548403110703004c0c0682c0d401004800b510090b08031484044418040301000502c0390f00222400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 20192641 1250 20191391 20191403
    0x80408160c08060a0c080105030a0b0a14100602071406040b03180706030207030e10081602121c1a0609041505030a050601050a080307020603040308150a09020a0905040b090105040207 80
    0xc6540341d2400004098000107082d412000911030180840d10805440e028141440f0034191b01d81800640c40d4030702100c025004408241c00502100d4080c1e114044600105980e24101c1c182582100883c400c60700a0001610880388042050031446403a0680c40f0001080c043c039140c1850348116541e00064044450b0014903100340000000920101010386502c0e5001a01d0f190a428001c060284501119014100554802405682c064101603100542106405181140070030480c40c2034050010180d12100100c0d900b500300c1c810805801c55403040c20b0b400c1c4011403d14000802c00102020019848a400c0100b20320604040d00182c00c0b07070410301c0e4500c4400d039444000c641002043c80b0101c440d90400700060101b8039007040c50310040d203148001182410441e0b800b0032007078071000d44098140320803200001d1524040b047c580c9c1207603001034290350308a03560b100c174940a034110f90b0f01200403400d6004003060600b801d10590b50780030070041449002c5d9180a041c0402584104420344003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 20193891 1250 20192641 20192677
    0x1170c09120f0a20040608030d0b0612040309051008060d061a03060f012402100504171201090c110703080c120f03060301061a1e04090e070503010608030703080408 72
    0x141007442280d0000d405000d85001400c41c2c18a82100d840c13944d80c000b44907074030301441401000300c0003042e1441c8205900300054002c010f03200041550280040100c05501401d04100401d5400034050003254002d4604100000140c4400d0380e0251081750b94907000043e00803540041141c54120001c8403211040b500e001e96220b01c0440d050002c21180d4448500000b001088060f0101d400e08000c010841d41c0840d8101c0f65010007034441a41808418119031140c2c00f10b0207110480b941c0c141d103d210070030815a01c1c50381402c0b2096040c0b091054030000e0746401490341985000e5020201c48a1580340a0944241140d5171200c05810842042d9a1413107200f54907440c03904070200074541d0702214803c4a80328a4501c08040c00e40e0410381020445001c0018000e49541c0c9513401c0d01c0030f4201054052106134040390b007940041c0201c2d44140122410070714000142c24000c228842500c00c00e50090013944c1e210036030107580b407103404002000101c8050010b00860249c1d006000480c0b07416407a942 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 20195141 1250 20193891 20193913
    0x9030b1501140d0b0f0105040b03011202060d0203090c0102010c030510050103050a02090607150b030712060f090206310506030c0f04050301020a0306091d0c0f03150406060501170c0912 81
    0x1940d0f04400800c014156451182c205289001d00c0c03040d50158091804030b24180c1000c46402c060300040c030500d400c0340c038007220510071555000d055421000410034115264a000c06405966640c1000c0d12030155182c4181c040300d0500c41d020312413294035003524225000346800d00440c0206001070212001590a0260015580d1594020304106020761460b070981e02010900740215400d4440c854461b038001d2504109440c64203034401d207125080080010040003500c010805044000e00095000e0000941000c80250880c3c419414240d4502200705040390300c0061084400710f80200c0e41d000e40306000146015014a009044406010941900300340e981c4010900b6600304000d19404207888510500c00140b0f01d10484d0682200807202400e000c0129003601e44403c1c1001800b4020345441c040200d083d14208039011105200303840c02c041d14500b80c1030180041c044c600460380002c114003064841d0742840d1000d2400707100b154205518003441d010800100401d4540d500c1e102d80038000c8196 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 20196391 1250 20195141 20195177
    0x302090a0b030115080124020a020d20040501031127070c14010207020d030513030b13020108090609030d090c030803040b09070504020406090e04030903210f09030b1501 74
    0x80200030798a6070360b4407941800c0180c1220030102007030004000700350307004201503017210446550f0f8261540d400d1528907440e41c8200e052000c00880650000801d680c21002c0060031545207244e844840b480030507019100003084107444080c48080c0010b407030311b096400d182c540241c0030210300c03a00c95407000300343c100c90041c9007010303004940d0200418000c07206030f4103100304004408000b0328910f00862820000d1340c00186045540b4801404028011441b041115980c2c1091009540c000040b0101c51900c820701e0280b44000d808120f0000d03440e10041070f07400c0c000103801c5002d412000c020750700344094081000010182c1c0c100594032411562800404078402c0001540200c0c000c1b0540882d80c83c3c15410946000d05551105014610402c000c00009921045103825140761020032034290301c8a0404844040490300054062510804d0f0094000c200000c05403071150a5101c000c02880c04003025216041140b1018140e007180c1c500240040851012821420505040500300140d58010b01c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 20197641 1250 20196391 20196409
    0x409110910020604051506090a050c0903030408030d15050901030b0601030b060d050402030c09070207030305091f050c190804030212011401060c03080c03150d030c02060f180406210201030209 84
    0x1290150308003d0610080c4041440703a640b8010304803c00200d02d08020000c03520003000180308072140c603559000310b6a10003c0004841c0d0464004088079280c40d2100402a200c2d44942c0101500d0b03490145898081c0b140b10b2610404c0325801402a00b1a80c43c546400000c1c80004100504040d6101c020b444941d803108080c0c41541c0716404001031601c1e2a205051034050011030162240102d00100061160b001810034140c0b5130500d841d68641440c000822000002c04d00249a1203980280090b039003a409005030144003200c604854524000c0c1505200800f6880d0010b051300c1d00800040c0007500309038909420594100c40000780e0310904200400d90340c20213801240c001841e480603281819400b11109803c0080700c0f004514508206510000c1e40342c01c111054096200350070320100341402403044581158025104030350f21000462805442d07400403042e60580540c1a102001900f040d02c24401a078001000d41c0e155140c0181c49281004044c0300120f04140c0c080024003039689480142e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 20198891 1250 20197641 20197669
    0x50c030d02030421030504020306060d05010e1c0f05030402030a020d0f020a14010e0f06040603050714040e0a06090912120603080c0703120503090c010e010512090f01060602070302010504091109 85
    0x940c203003604d4134080082075902c3c82050202003500380800e20001d80d8001c2030311030300003e04441c024140005441c046014100220018209004500c02e90851061b0448101303117005490355806400b0300e01c9102600e031804143d5001c0c0d0191b200c165010010704150841c10145c5004101c00c020389229070340050820609034009945550420103103c0403545c00031142c02c16250f0032608a60000c061a002c60b800f800b903442203400301a102d00105040900880ea03180096001c041e180c2e60720754541180b03110344802038410514003131404c0e00000d1400500c0c07060362095a48400a510981103a01c000c8031040d036041c81845400741d0ba04000800107104100815041c1c240c2406050141c2c40c504080c410307207500c035001c4000d2003010400c008035100c0204020003810000d091121081035080300488150040448070704602c01c00c00e051204240e0001000c00348030541000901105445070401c0f61504282d00c0001e0200e10306002c00c2c009001c80c1d8001203011a60004c0580c1081c2003440060f0244100c410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 20200141 1250 20198891 20198903
    0x5070c050105010503030f070807140a0308040302061b0d0506060405100e030115080a0311010b0607050a0506160509061b071d011202090103060f0e010c020c0a09060b0406050c030d020304 82
    0x4444003005420b000e00c0e8010039003107024505201410301341c80d881d0712070100014080c034800a110810055642810040b07a50300404940e03654a49140146c03d010041c1c3d0300382c015115150001d160004541100c94014400445082c00c0c0b498000c01c81024180282941d80d1000050201107019241c5000e95031100005607100d20440c00c40c2c0090600712000d003040c0040d40511003109101d01c1c0c03c002940c0198651514120700300b0804150b19038010894a0409544450f0000b42801030000008107010034030300601c25500700d922180a042c0e042d10314076001601288040c413942d80107182000c080d0020b441c10040d000340315000404114100750039600905061f20740b10019080740603039440000d001d0814507510640c501801d07000038000240c1480018211504c581d1641700700c404641188030200b821400a220050710711002039190b511042c20303140030340311050000680910501030141165511190107140c02d00b410700840d816488001c8880702c80c481042074841c12011440110b220380d019807 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 20201391 1250 20200141 20200157
    0x9030e060f0703030b0306060d0f0309050402120402030f010e06060d050705040e0706020d1106010312050c06100501030b030105040b0103080310030c140109092306120316030e0a0f030807150507 85
    0x89401360449102c072034030138040e6100400b04007440d10303050b507004101c6410040245a8810034602242d00e40108e41010390481c1c00460072041e44a0b2a038207090003184200c090304c03035241c03139042414201e50145070030102c035a1090340810482c3c244120003201e814041e40c2a20300e001e8455022070141c070800120094158812a8204002641800800160303016072a12501c2207140d071081030340d1410306000192038131800e0740e0040313481030080003103a04103d904015900706107030941d20f030000c0450a114150109041c010092418901889018401d40d170244030546240d0840d25242400e8100920000d40741c2180b4002102107503900d03500030010266170400c101c2018100c00010f03c42280e641c03003449001e0811400300c1c4851010300750401d040465207544034003646c86800151581d6000c0c040700200c0c0c080024689404505c802148160900a072192020400000c1c203220b209140c9106800703014140180900010b6002d000414080d070103000c0900014940c070404400321007081c0c41000200d0000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 20202641 1250 20201391 20201393
    0x1b070503040e060907020607140403050d030506010914090414011e0b01020d0306061b03050d140105040e070f0b030703150b03040203060109020a0c060b03070305012c03030103080a0309030e060f07 86
    0x11240203600007004d5651501d9400c0001c4007a540d81405403d020602c582d01d240c01c01c41d0b802c030406075402140c010007200d02884204c1d001500030001034500a00241010101044551031300d40e200d400488054044e08156a031921488030400480b48a50003030354a071448a041c50ba05107481c0340040c1c81c0c0f000c001400354544000a031512000c01e04840506040440412a9640110354444581c861003d10740d40480c45107001c07503045c130842d4a142d0200e8035003000648890002d0074064140c03202560204800d600600c5141e598071400e03c076186400054081c14098444030501071600502c3c076060100b60a04400006503372941e154002201d0510080300304800d51404215a03030040920700021490300e0f9944a0046c25891604800381003151a409491030310303102000301c5401180c028000300140300105101440d0744810171400c88460322035407103a2102410100490b030490f41d005255900c0c000500d20309402800c0e085000750140009001414866101c00008003608000340003415503c0d070321 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 20203891 1250 20202641 20202659
    0x70602060105010806130915020d061a07020919020c0a110405070f02060619150201020a020f030a0f120902120c0a17070e091e0102070b06010804030e091b07050304 72
    0x4140c2c803480c100810034013800f099031564070130f411401245040105140c801800d16800d505081c0d6108140684009074401c05100241d1246042c1c40038003014a020030f0501e13101c01c81034050490065440003240001c00c40004510f040754030f01c040b40b400054102030303034104002c0c02e005c01c2c080162910b42e00645014120320f018480e5941c045c0490604800300c40ca10780009641d054002e00c800c0c043c59281c80b004c80c115010381020001402c03440c411541480310100006c1c081c0d0000703040007001d4451080080c01080001c03042c0c94020000e583c401032560218a01141d012100101854413a40e55030006805a1104404511080d01c024001c101e0582c0c54002e0000c1c2002c9548206c200e444c401c02004031040000c60443c0031200044510102515051012030a041e80300640400900200401412041c4107402030542203004c0d80031000c480c0e0f0741d20010b460205040358010005600d4007805081403802d10400c40c0c004c05001c1c1d658500340d0700340e44400000e6125400c1504d090740042801c00c11410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 20205141 1250 20203891 20203903
    0x30b120f1b09090d12090b0a0c020d0c150c0302071a040209010506120402060304140703050f07151e02010b0a06030509060601020a020d06050601020c060a0f02060603010506060901050711060408070602 88
    0x82a100007180f8604030120540b5400c041e070100c8204182c402c2c0a00200c07810750807119810750000c20040450134015009401440e4441c800c1e405402408001540203000f66607800500e0b400260109241043c00c003500003c0c16144000e60600d507091007000c0116099010528849100d0071210f00641050b0041084c4a00e050340124030800040108406115510104607009507042c0c99190316902c81d444c12403071581040d001c00c1d001d4458400004140040000c01c00700200d80d0b04203440b4495207807041c010385003002c44007440c003084601d40d6400030940c48000d2241c03045243d1000260304031480c0006403100081c2e03800725000940301c00a1112a103002c1c0461034001800b40018070035041c42ea408100200003140019090968801c00540e061340240030f4950324000c02040e40395103250703101d005000c4440703004041d00140301d0500025a01d09052180c1c6000d80d2009103410305001c00f4000440f4030381d0020b0340843d032002c0c1d411640c1d402622040c01500c041d00301100076005031400d20100031b103841 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 20206391 1250 20205141 20205193
    0xe012a140d120b0a03060b0d02040c0c060c08011410180609051f090e090c060d14070e0609062503030c0f03050402060f03072706030e06010b0307030b120f 68
    0x40d241410f000300302e07a07801c0d0060003200d5000201046916030840092242d440002c0c1c043c0d009801c00c158025529030084a110409103d5201049103643c001001c50303c0318402d010700d0158004145c10440b032440c1c07002c000007807e0b4080c601032030003025001c1e050013111410b80c0000086881008140414a001568688240f80c45401000300e80303040c010040c021111441140c0003000301c10041075840b0000d0005115115020300b01c1551004000c5014000b042620075600c01200f560001c40c11551048049404021008041c64148038410080103901d903c4041d42d40829400d004001c0c0280c401440d41c4507200d8020340700010b003a1580040949aa03060b4090001090315210812005940d94810340d50021003042c0c4d055140d41d01d07e027003034460100c803498060441d040d02007403696086000448509440d81c076601031212000c400100d9642e80c03003e00440140d908c00307000041c00270b4440e034800c061090740104514124543c90f94070b2400d106a52451544c1504501c1c0d1340c60020b030400c000c0807103003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 20207641 1250 20206391 20206427
    0x1060314100e030a08090f060906040204060b09010e0f010507020901030b06090906070813020109030602070609020f030a08030a05150a0b0711010503040201020a02090a0f020d020306040b010e012a140d 88
    0x42e0890815442e203a204000e010400c0c411030740c001c1100f11104000091200300c1141c100e910318240b030000b10b9942e0004a400b24072440c10b007240490010b592070306552030000181c40d0a0704010401082003114142d9400c92810084140100c00c09030380c43c119154000c50050314420385504210301070080078031b00181076061a5010b903050012482e07000715065170081e00c51130700d002412464070048610000540c0040c001078000310f0740d4418002e043e4419492a8801c482e030b038007492f03504414551144148003025222440520000700c1101141d003040da4010303240d11000c0d0036401410002840c41c10f4907003040070b1242000ca08442017011080801c2072408090070305c107041d4949680001d40d505410a80240180348000c0810240c0c030442c0c21030f680241408100355250f8498001210082d0000c9031420321031814460030b400341707500900c07000500500694034100c1b00d07002040b1141342e1102e4092034500c2c050b40c1c6000c203004a0041012400503011000c064034081d565200001d288240d213031070403020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 20208891 1250 20207641 20207651
    0x11a03070c0f020402070b1f060305190b040e0f030307020601051c020409050c100e03070b040b030c1b1b04140105010207060e010504081618050402030703060b040b030106031410 78
    0x3565811001984401d5404807101c082d295061004c00c000e40903504004129a440c4014407071b26442030318000f45e5240e4000a20f890180d641c880c01c40646209070f410035000d444100d01b103888030490303400c000180394000d08003060004800001500c0c180c501c0b412600c86400100c2404400b40d4144440350050104a48800070f9420400510350b09400300c1d400248203507034901000041000510403411469001459000c4c0e01c6503488024144491542c5503d00c280a070100120302034542c0b0042e1004d8883d04114a411a660000f00c400268041007281c442d40002540e09404007008120720909000f401e1048403015000b07400b800151050101700b0319081c905480107102c1c0da45e0026961044034020b240448820820000580b0f00b44190b070040700950103040030704130744002c450b5000b4040715083d800070365220303408501440458030107070f074003e515400440b401c0011071030b0340c0c00040201d80020310002c1c0c0c208501c1c00090840301c0e00d600c00c4589080207030740000c804400780443ea080e003540b98804c0c04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 20210141 1250 20208891 20208901
    0x180f050102060c0307020a0c06020f0d02010501080c0d15020d0b09010501030203190506010908070e0f070c0f0809010e18070e0114031308090303040f080709060b030a091415011a03 79
    0x502e0b003030000d02041d20740d1808400140018800c0110040d02504416074034481c54039120700030744810481c500401e480c4a004010102144140301d01412114410b0107029400358150822048150407030382612000e800e03e02e0710300310321010302c001c0500008100001650540d24010b10012010581c86581414818000c003d07070a0781c0d210702005840300b03201c40010a0707550350005030f500e040b160300441042d1098103004182030801c210414050b644103900c0001c5a070311100c080b00c080e000440300500303170000c1c6891940000d1038180580540307101414808004001c0801103050058203044c40e2010301c4c1c000c014808016085000c002c0418020b190001c21880c0c400010021031001501102500c003e01500e1400d00030520155079006400600382c9550b180c0d0384004044200c090702034441c09015222000030410800c1c821003003102c0001400504569442c842d14006010b82c900a8908005480c20340800c0d010900c01d00402e0022043c0075904c55040640700752a00040c20000c0d1105041002800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 20211391 1250 20210141 20210143
    0x30c010506041b0e01390203060a060303050a050d0209060a170c0313020f030c04050709090e03070c03030f0e030706180506070506060d05030913050f09071a0d110a180f050102 77
    0x7844015003800c0c1540c4014400804101040b40036008062240f1b0103402403500340350320031141a180d03008408450b00780d10fa00c0800412100c41307200003030100328100104e00b2582d0041c2d001d44928140580d006050402036004251241c0c061503407000042c1d0403004001c44154030700c2c0e040350441c400c1d15030340e82140b6052044046144803004060b02c16040b800c0d00d02050f8ad400c0104004001c8050b0050019042120000c0d1074045103000381046542408408100e07036030008180e5842d15040440d00306c80a103540c8054031070001005415041101c40303010389a840c0c03020401d520046c0019581c0c01c20303188040c08030280c490f80302e400091250008100c0d060100d075001403d01d03002281120b0480c0f80505504d03219103107104106e01e1640014004c1020000c444503944000d104034526132144100d0f555029880e601d440603401a60218100303003a0009070300c42c4030405469007103c80e400c0050304040448414a1540000300b904000a00b030b00310b141031180b958040c0c540101b142c140480c2c900b6040100103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 20212641 1250 20211391 20211407
    0x10f0c0e120307020a0608010f080102070302100209030a170418020301121202101103040309080f0a060c02030903030310150519050a0903120c0605090c01020a0f020d05030c010506041b 81
    0x1078401c1105100340300501c40184102c0c1c09241d801031210402d55600c1d20040c0002409100d00e4084080c9040000751000703040c001c40382101e07815400307400a50915613940000b500700e107620036014481e100d41000040c0303030308071420801590080b4007615245441648050034240d030b06e9041c0c0840c014001009104943c5690058181e40807807200e01d80629010100c1c982034022000515042c01d107094001070010300801980214080e5443c0c0744529101c20090742d880408079284c9009500101c0c890f8089680380d071041c0e5148410340b0541e450500d1000001c0d146030000c0c1c4224120301140841000341c2e2261000d40034124041f8105a41011207940d4460342e00b801000c0d003041031040001e8903020f19031050320484003031544a4180b0b890185540d40060501c0e0900d0804c4074281d04e00303000b04003100000103100d142c080e4164000d189610355a80da200d41d41d6000783c4100e070441021101c3c180000d41c02c1c4081c0944401f00302c000101840d1000c20801a15110480c6d60001490034070341c150110740c440f43c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 20213891 1250 20212641 20212667
    0x20609010b12120708131d0105010e010e040b010207080a141e030d0509030904020417011104080a0201050c120726040e06061c1b030b0901120b0705040e0c0903010f0c 73
    0x1030b00d480e480c40f414440d00d948119016500180344664000c607402647c5134040c003952014030340c013201d82c1e0388a00c015544031040d00d0101d0f01152941200254610b0544c01c0482c44500610544030219a10b0005510f000450b0104852040c440da01e072007200c4400300040035194089804507105501c016040301c0e240d100b585c00280f1590344510004c0c00d91002003040340d0038038001a00c11036a465544002030440202501d0000c1c5035406c25103602c0600071050140c409580c0f07680094201c3d14503541c015641a40800c0744e4101c54080d010309610b012071840050700600b0700520a0b102960009507072501d00c8030704d4050310303071401e43c060005210721000d464219601003000c3c0c03080da80d200c1041c003005119020041014540c42d0078603206e43d4800f01071010b68841000142c900f8000303c030704401004040d0000740590070f000b030302400c980300105804252071034200c0c0d041d0070203d26168a03005c50901644d002c40b020040d8810005009199040902c1060848003207540200940700d4100c070010403002075810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 20215141 1250 20213891 20213923
    0x140c070c0302031c02060f04030906050d09060501140a0905070903020405040201110607120c09080606010f17070507020906031603020f0109170a02030f0703030507020603130f03020609010b12 84
    0x15068100002109614051a001811600b00341c0a5041c407003a81640c0307040d100d006004202c04501e0f41c0300d880d4107041c0901c0d89a2070300f26080c5e040203801c89549e00010000c500040c0c403400c6901c0400e5044c441c540c06040184903003d00d0f001c22a051001200d55a4449081180f41c13400b00f10810f41e001d03400c0b105683c0e048401103003a883c4c03400121012200800400228003a440601008603040804284450038812061003101c114a0082d2040c10303103841001203030740003280000c1e0198494180741a44000a0806000007004440c200d40f40002c00c994078004600000f41c40f0b03055141c49234081d0fa215a044006004088841480807085e08441c403009014881d50720503082a83e015800d0100909402d031000402409600c0045540d0300c08000241d0203402841d02c1c031804280003068503010381e41c240e140d0520b049015800e0214652000b05103c4403081030800c0080000e410010090311b00303000394014200f900f400b0f43c02a0854140e648024841c84594410382a080b00100d840d101a104e00c0c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 20216391 1250 20215141 20215147
    0x60f120c09050303030f0403110a03080a0507050f13030201090b070807030309032a020906010311040b0a0909050f07031409100509010204081903031112130c0801110d0f140c 76
    0x24003501e8a40c440d0300032540c14040031040001c241240d4001612450203961810000700d544184251529051100640003485502c0007031504582508480c7e0800040e20f001d91808900000184040c1c0141c0505440c00d80e403010204190760303005034070750041c0101e50005441e142c241e40e5440018800c1081c000c00749911000f02005150080c100141c40c2010b903811850301d02d0048444207144180c1ca00101d01c03a02084011403560351103445610480c2d146846400c0c5450f0504100000e02d4005200000802c0610300c40451805403501469001e03519803803d1182c2410b00440203416511821841207a049000b400c200c80c442000484d0f6110384181c2350001010303100c5407401406845190031500c0a4441e011010040558004180c002c2134041c0d07034100b01240030801c14900c0c034418403080d401e01e02504000300c3e100c03101e00c00446101301e100b100c030341d8440780d9143c2109003034031800b5062150005000c2070130b950714074080c0200704a00106074020088410f2200031036080d403401401e8130a002d1004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 20217641 1250 20216391 20216411
    0x6081b01180512010b01110f07061409040f02040602010b030c010207050f0a080a050d11010c1d130f020301091a03060c21011e1409010314010b1f0306060f12 69
    0x1c40c80d040c0107040060003421a018512904074040e11074007945c94000307000c40711000c28400000c40c840054061443c090140c0c603180046c200e48e40c3e1000c000d00c0e00c3c280e800300311902d001c1c5e81d2482a202c208040c26030150703c1d5442c2440207403c5945060485000e504418800310340390b80e002c920081542c1e0115200407002040c100401c4200100d07410444c10361082101ca032060110000d10b900c181c400c50341e210b21550360b1100380039003070b0b9262185090100c2c01280c1c0c0071180100c8020003071003008014040c0c5142e2120484885c00342c6041c0ca81190b035055002005124030880b500038854200c1d0b140c4441c03610300e01c00c4000319640c0c000040844e0300314100070800d620464280e02504403101100c4008040e25619080001001c481500041c88400c081075000145405462200d07202e030b4a006001d0a000d07803940d141e0070b50541c15038045e85900d540e02c06078440f1594900030300020b031611344224280400d201c00005411552140c1001c400e02090248160f607056204185800c0b25501a9010582d6104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 20218891 1250 20217641 20217677
    0x50c030906040803090a06210504030c02100305010501090801020a0503011a070209010303080f01090603050a0b0a06210515010503100c0212072004052e0302060c030d06081b01 77
    0x35518181d910a4001400103000304000000e0701c2201821502224002d50360300c0140e990702c004181f00e1460b1040c1c0090a604030003503900c1141d105000f0b0a207408110403a6002900125a1044c01c9001c650703118014001e03540d002e40f02c1c101500c03c01000710314004e180c09000d00903000501c80c2400c01c0c0c00d1481411003800f03c0c8002c3e83d5446601921943c001e5844e0300e8040e092510460300e0109041910000243c00b605601030101100d800c1030281c0001c580d030b03441e122807040f0700a18814690b81c5402c40059840c40c0c4a03d214110300038402c0342000c80707400e45842400e10001c04a0413881c2c2c5260070042c01640c0d00403548001241080b40005800c0180f040c060f130402ca042e4001c050b5034500401d0040038080746d81854038042003240b21003107281d03101504000c01c8410940750b204001000c18a1f00c200c0040000c1c0c9043c450b8554907540301034a84d45d42c0002e85a40c090201044260004034085c7c4426006000c2d01c0050410000039044010f04011240b455440f0070a0050400243c00340d1002c85c100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 20220141 1250 20218891 20218897
    0x160c0305030301080d020c0409081c060e0901020901030b0f03060c0d140705030108010c0807050906090402090904050a150606020303131a09030a09060504031104110c0102160b090a020a06050c03 85
    0x940036080c0c80d12981c2d1000299203d030000c060540160198600d111024982880f0f41c101103541302c1c110342c1c103040400402d000c804042030180c002c0075035a01c01c04911080b540e100d00c2e200d03940100c005030341d4800f00c030001400d4a8034101c000f401010034041c121070036680401d000c1e520520000c800d54562a80b0700040018240c3d4008000041c5921000d10210320341c00030085058a00c100020b005403100802d04441c90700049808100141042c851b1400074600200100031001000304050b08049100700010b01485040d5811507a69100c1d2007200200551440c400365018111003080204524000c03029499100041034101001070700e0160504021880c449881c0c050010b000150140c9000502c2507601d91004108101190312000d002911074456421641502da005000e48000040e070320a00c006000d29684400e60408248101442000c003403000d00045100c140c400d07100c401040c00c1c030190400c00a00303201041e401c90450440507031103152000d030840307040785421540ca142c0a1210341c1140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 20221391 1250 20220141 20220143
    0x1a0a060804030c0606120c060c0506010e090a050f01020304030e06040f0b090d0b070c0b0c040f09020a0314130c0501080103030203030609040501201908160c0203070302090406020c06010801020f160c03 88
    0x85c940f03400851604401e40180070560300c9600001982601c0b20130598841440380d00c001c11560000c00103000f029400a21642c000903410116000f1800503a10181410440c120320081c1360f41c04000c0006050780145941c052080548040d0320345400c043c000d42ca81e04650041704c004502c0060245503a8840c240c4504405070851031048560814a00007014188080f8003940d42440c128040b41030300b00200c00300d4003203400303481d50381c01070900c0e003000c0c20301039048036500d5002e040d5281d55600d182e2840d0099540702c1e180c0729107034121100346440c0c0300c0c0342c003c400d41000d810046070b00c0042c00000e40000c00c403504401301b1100b42c0034a6803140380150140c0b90a4034426603010420141c0c1c0409030841014002e0303480104144014184001c13021640401d00303c0780c040c03100080804034442c030f1303005881400c00d1728009410740e24491380f603401140880d18180c0341159442c1e40007d80d80001c0800b0b10089024003001002580f80c0781001c0f60103e0302d40100d04907852803c0c0080c4000301000ba2151001d0021 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 20222641 1250 20221391 20221403
    0x6080103112205040b0604022a070b0c030c0d02010b1005130305030406030b0913030206070c080d05040809030d030504110f030c04050a0902030d050307020714032a01031a0a060804030c 81
    0x102c050012016040640d0110781d20404900415203514142c000c0e94400d00030b1055807513520288040e0300a00c4e031205521701841c0c3c00340d02d00204e81600000001c01c0900340d0314000f50350314480310745172a18241c00c819026045900d4110300028607551001e02c905500d1192070225158004540a0b1410310180c1e8030040551200080016449426421030700c056401240c950111b55203080c0440c2d04040ca142c0010300581000c000074441d68020300400c403000d030043c58204d003000e480e8082c810446074103a0b025030300c000000c6038141c20351800b0002a0280140d6140600cc0c0f41015650091200c0725181d0303c902c1180702240040c01741c3c404006c1447e01140061041c800380c01c082e07030044011f040c60181640a40640100030351070500400c00c03240191001c0e401400002d150009414a140090715400d9141c054100c068020543c02d01340140d02548280c201140c0c000460005401c8418411000c641d41c080d840c1500301d5544e51030010300440700c643c10300035030f40d07509c80c43c0840340e2504244004180d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 20223891 1250 20222641 20222689
    0x50f0a060507091a0a20060c031006031e11090d060203010314070b030a1d0d120e0a02010e0f030106030c0b0712110a1709040606051201050105040608010311 69
    0x6000440d009280201c0042c0c503100c541c25211202c0000203962070040702c0d980c140c100400144540300d130b0505031107506107046c054110611810440d01380300d0251109003024070b0100c18854000305c003003107441c000c04090a00f0000b03039410000046440743d40507455002e59698138143c4115000110803601d5840d00200441c14480301841c051000703400a0009030b0759505c000e0082d03440488000b0711441a200b034095242d040d135039100e00352006400708601c0c00307040304601c90000c080060200180c03003c80d01c1c2c5450300c5241d0280071400e042152108140608254810b6046e0320142c2d812200301d4004140c1995003a1141483e040464054a01903000a1028801110008480581102401c11580304142c00d000b400084c110072165410720301401003058100d0010100020804190304c407045d21030701040c0c0c4c107141182d00000c04840b100d034000b03404188002a880d00b248004088180036003000d0030140e003000d040c10001000d601c8140402040341a01300413091107651404421440c0c071200c00d0031046 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 20225141 1250 20223891 20223893
    0x140406020307140303010b030109020306041107030e042007060504050f0d120c0302030f0609060a0504020a03020c010608030c120c0f01020d0204080607090b18010c02060d05061309030905010c050f0a 87
    0x15907984460b0060341c004200340464030740b81201100305c0b4100c841102e940350540c1d0804102e00b00070742c406001541d000d0350f203910807030003e10b40b01c014002443c080e03100c1d107985207a400b003400103a0345844100368a80c2c980007190000055401c060b520410741098000869960328500b40e454440000041c841510507090380c140d81580c011030340007503d0118542449031020b860307029000e9000541d03040c80d4000300c1000080f00d60904a100c0f1703512400003001c104500e561380d00031a00326440150349000194000607075500c601000d0040900904648006519003042418201e4503212242c1030400000c034001068403000600b04111005951060021940d842000c40840001d41c820302c62a2040c1c000c02d0001000e4034002c14010b800c440e03c0410f19440e0104202c10300b80000b28005805040c05208241c120140c1c44510103402d07480e079650400107081c11b16030b0801c98003c43e002100c400b040c0c2401c0721100000c3e40580040d00701d40083c02c000040302414504181403c2c070400361b5118501c11598500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 20226391 1250 20225141 20225143
    0x30109020706140c03010f06110606041107060f06081603020907030203040f0b010605120603030307170709030f0609020f0d0302030a0806060c0109060b0907020c011d1804050d080705030f040f0314040602 89
    0x5041f079812110a0b40c545035070700001d0321006400c2030026101d4010100140003070500380c01642c03480d0a92a121072500006070b5070709080750b0010718040325160744c0b0941841403810400a18120410840b0306503541c51940c3d000545a00000340303503a08243e000300105040040700d0120001081d402a1448003a41e12000024240d0700484510101c044072000802d200d81000300c1101c1c0110240d070344081c20200c81e45c4810120400140c003160030002c500400201003201c81000c00002841000302107024a032500401c04142070005180744203c250900100006c1d40000031a4034203090390800b1951a0f48043c0012298010308403203807095400c0070b49180800440350b02c8450860021a0140e0307880d11a914103c2c0d0703d1440c050820301042c0c0c94919a40d40310400d5081e003122820040421401030394588040342d0b641c4003900c0c11245036101e0640240f4142e04416610341c00748081c5005411480c00b8054050480b002803c00380482c108040302c10b0900d0320a420341d01421082d07103902c55540790350300002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 20227641 1250 20226391 20226397
    0x1005030d23090a0815090d090e040f030e0402070804090509121b0c1003020306012a0611070f05030c0709050411210304080c011403010608070807020c0901030c05011d06030109020706140c 82
    0x100e84280103490040a1f100c0c000c00d0100d00f543d5034007804125030b039550b40ea07003400806000c2050702400044114040d655a450009208851203030405540f1603140125410a0300e0b40a0b10343c2c1202d1708082c5540701183e03007443c02e0340c05407484146841d14040c021010344d801c0079041000560401c0b0800c58455610350580c0056000703541c20f0b40c901d402c5100301480c180c41e51520424180c08900320a82103400b05100e60000381070100c241d681c0300c0c074105590780d45d101c511000380011901c540010443c481406000e004c074000074000394001b03000c1c0349040c1d510103031003031440d00308144070345841c0360a101001c00e075801d5880c4001c00501100d64a948031002d55a80d0640c01101ca4000348211016250002661060307a0490342d042e11950502d44400005944130a001404c03030045109409036002c2e40d07901c441e046402103016080108000303040c0b20004081d5840c0c400c0070340d4030818000710030300d1903100e00c400c44c5d04560652200503280c1c0b16a252803009000e16541c0b02c1d56012283c8144800c200c900c0d001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 20228891 1250 20227641 20227651
    0x60b03010c0c110a0510030902011103040305060103050f071a0d1e061406071e030c050105010308030105010e10020d081e0103080a020613030e06130902031005030d23090a0815 77
    0x16604222001001013030b00769401455007000f0050300c401000c0d4040c0e08251001441414425124510301480c589990015030059030346034000c1e3700400c1480b00c1808101180c60200300689803990402d2182020341051811070350182d500083c020390014030603800400c40740009449484482904203190002c1d107404d00840305205000c034400c0c0d00324540308003100d840300c0d400f01255110090000b503075002d044040c0301c160180f040404540b0000740342032050b0742c080c5126080c410707121750400c0c00061055190100343d038080c4a96807490f000d020340028409849000a2a140e005940c506002c03551040c00b03400b10f001d1400c000c400100400c803020b0043c00344050a80d00b00d9142341d85100e254003081c6002c5034050041040342c01210b01d5030030410001e061041000c0756000310f103669045d403042281e00440d030038011b00c0303580c0c0818010b80c94284031035641d01489152060340c11001c00ba1103081400c10310b020302c2941c1c20000e000ba09a44a14402c280105075030000d542c840352010800c0d10f8288000c4903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 20230141 1250 20228891 20228903
    0x9190f0603021302090103140703050f070801030803040b06040b0310020d05061507110f090103050c0f01050307021002031506030420100c080a02070915090609021e07060b03010c0c 79
    0x450561610051080d9021030350002c1038205207040383c8032002c00a5014403c0141019141c0a075680c59254481104e806100f099500003a203180c44001c036041c4c03410140410082044441c01080442c403d03005480d000f49c0c0104800705031340c031072100280051090080c42a014010102529003414065001d400396001c100b0013030115a45000400280c00c0600440ca9007802044c050039002c214000c076038019100c6d0241407205600d011000041c40010242d02c03c07505a0701042d4664441c1c00d00e26401180100c1c282000303402d42c21708400194884200341584610298044001108120f80303d13211320b1464805400c45a41c2e05107810683d040310340368230281501d0a100c0b8031080040c01d05020710000307581c066840010001d0307550b0328405654804042c0f4011031003000c10100e8141364078450421500050481050840d281030790400aa440c554810b28400b40305100c0340072035411012090900c003021003802641c070308040c81d00c0802000114034150301580307040c081c0302d203660b0400e040101d00c500400d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 20231391 1250 20230141 20230151
    0xa02151003030806030c0a12080403020d140c040504020604120507030804080303070807090f120f02030616030c0302032505070b01180e01020901090519030b09030304061d030f0a05090919 82
    0x500d40c6c0c56074004410b54010f403480904010040081072003814652150030014a8156a81c000520039a10007601f50356240c01080070008190042103080c40c40c0201362400c1c00985001d0300040e0307580c001da1007000514004542c0c80c5c0d04008081c07008601541d4810b11654845403a8100c0540e603400407a2001e006c41c4410010074241406411341804450700b080402c20501d0400300c03004401c80d45840c0480f50b64802c003426200507234041c0041d0388590821b02c0b9058222030b800a0040079241c002d450b138003d1502c10402c1c01703030380d1030000e0394040e0340c03200e27030b182c20034040c054501c1100c1c00d21508101500e0350310000000700304281440d0107104c200702d44420510880c403203404818202d1140d0034030b0701d0104901003001c10030b0341001410511104c0e002d6000c4001c6590f0f0792901d019121080710710390503075000002000108401032150100200d42c048420842c0240c0c1d510f002d98038440c0302c054400304480822040c00c0c0b14800d10407101c5610003e0540707825400c003100300358072404a550003260041c1c102 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 20232641 1250 20231391 20231401
    0x80f1b031306090f0c060908100b0604090e0d0f050702090a0902010e0306010303080106090e0717040203030d090302010f050108010507050a030b0a120503070210080c1e0702060301060801150201020406050306060a021510030308 99
    0xb101fa900545840502805069400703135100801886100110760f006141408000b0701c50704103119090750a512100a8200c106107048010b040002d06040481030042c284040400751704d032040c132a5400041200f002840c210f8600059a905441d9188c5507030501c202400072042590001c0c100d4102c4034141c030b0f000134aa4880c210100c0541044408200080c102c9044690000c030921002c0e40160016007524071b03081c144900042a0703180c0180640141c1e445002200810101d071103800d004040c1c8000802940c00e000100400038401c4100c014201502c813040400306544203200000208111100d4000184080c0f03011504c9411110086e4400d41d03d400c03294003914062603a9500c074840c90f0826601e0090030f4640303416601c6280960508401c0107000b280010b0b00c81e8801180030f8100c41d2103804156141c401802d5211500c0840d4034116401070104100c200d80020640c0d0704410111403094689580e070004900d0f1050a4264150000d090401d00240c4206440c40c241900c0c0241e44040d8140c1d20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 20233891 1250 20232641 20232647
    0x7030908030307080708060f0405010f18020c0703150204050301021303060b04050103030f201501030c1406030c070501090506070e030c010206090706080702070b03070f080f1b031306090f0c06 84
    0x22224103020680350130002d031099214901c51640000007e106241c8101c080f00400c04890090308150740070301c10b803030090151602001584045540c2c1e120154504803d5035801030300c6000703a00c801040001003da000d200003000350142e801130301c806002151140b032034000f480741c100300c0d038403060341c0312442d0451031580360401d4006c20b03060760741548824030122520401181c02c0800e12000ba01009160791110314021424000d4401503024240649d2107541903003004004190280d00418a4203034184000c940c5032101001d49621143c12401c2945076222814900d015010001008011b0301071034041001c959000b21140940000a6088841d4400700742c005990341e10094418100c1f0b540030450802c44584125501680110310744103a5109680e6001ca0f10096002940c043c13000c2002203003018821a440011035500940c06141111a402d040c0780414106049484070704249030000000344a91003002c1c141d08115070b204c01c0800c8603454a080c2002079032007200c02201ca40c00380072000030310380388 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 20235141 1250 20233891 20233897
    0x7030b0103090b0601050a1106090a020a050904030e04020310030203010c020115050406050303032205070f0504050f1302191505180909060f07031506050a020d0206070f050c0705150703090803 84
    0x15101001010f42d444200056035541c0144007950300b00003c03090f203600044001c0c490b013130080d01c91400400420040b441002002d0702c0c01e40242d03001d0180b030070410020950003400d0007110301c820b990050766600c1d005440e1100c80d1141e04080e4266007003810b03414606505500440c0c02e0f04108150745459a1640c0401c801d950903232180b035915601c2480401c15242c14502c4444407600d8849054910540d6640c070142030004580c01504403071b4806104010608190003402d9016104800f403103031f5860003030f00740d05421069040190282c01c0c800b49011004c2c48910558000d40b851000d068003400a12100624550285c0700c014401c0303108a10b000b1150420528580c050752622000e00342c2030b69402100c2e000e61400070b00c648100350b281c0202c0300c85c1904045d41400503100035990f03180e407400c04501c060716085071036041c40f04641c0848200b00005500c26a0110710441c14908165645400d140c600c1ca0404182c00c42c0b6402102000101112404070004102031842521008841e82e600c0204c0c90f01c0380 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 20236391 1250 20235141 20235143
    0x30507021f0b06040e010608041b050d0308070210050a060801150501020a02130b0a09020702010305150f01050f090a0603060609091112090a14010501080f0a0c1e0909060507030b010309 81
    0x901c00c000301150140d008680708a0010301040d051542d200c003400006102a4004c0011903407500a200c20f00c00c031811891100259001d400030100d103440701242d15828100005401c200303000e00817a24551091040081d40c0f41c1d014000d001034101348010100600e19441000a10f6203800c08220052100c4111301e0200d0380140c001e00309800709502032105980040854086240d81c40b00d0905481d5200c1081d8405030100380c00c0161942078600c0003404403107002e03003502c040c40c0503100e0340c07283c51303480c8a00f60040640a103411501d0b424921084d07003842c0039081107160300c1394401d0004030f480b44e4540d2000301140c0300c1344e448808040c1d481000c1011521000140d2032000c40030052062070003246651140c220781820211582003801d82c030b5099140250000705111651940c00420142904120007040000c0590243c07040c100f040d030364002000303079500c502d6509503856081c28015015007038035a0000d042d4900140600304042ca00200101000c6600c00e001c40d141190f035850a51180c0308001d005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 20237641 1250 20236391 20236423
    0x9080309090916060206070305060d0209040204020d06080604120311030106020c0d020604031203050414010b0d0f0c0308030a02121b0706050910020f07060506010806060318030708041503050702 85
    0x8440040c040c0032002030010506211807141d21603107502446640c034008010112a4054201c9041c810300003000e407500900b900e4440c7d81c89910440241c0e482800481d001079045600595a040f0040c909002e0001b0ba03004200134001e4408103c28400326003c031102c14803d590301001100203403924007580e40002e0003030000590020030710074020b0821a075180943c0d40010720b0107081079034960b5800c03040c1d0560281600041e446009000420024207044040001c8880c021300c0305540c000c0200320000707100c01000c5d2202285051901c00d20284600e0000a1a0000c1c0803947d03919048120740e003e94085150b03e2040301e144400155491085828000340c1c1c41c1c0491007030318028071030f25481c000e88009404801e06000f1000074080100c014801421582001320f52a625124181000c400711b5800602413414004400100300c92a40e8200c00c41e640820400d0718007040040004070249035000e841c1004101c0c450001d00800c4101400c0b010340e01040c040e6505000c81c0c1d40d40c660032620340c00b0308203030046d0b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 20238891 1250 20237641 20237647
    0x30408120406020607120f060b090a0906080d030506130507170919021009050306090a0c0b1213030c0204140a150305030307050901030b040903030905150c030105060702041508010b0f01090803 84
    0x51510442280f0a083c08002c00441c9842101c0c0a24017208e02681c4a10b90100b0005095a201c0c00c1140c002e80c001c08840804228581ca442c0d182c075201d075188038811081540d00c000158240c1d45600328210701c0141c01e00108003600d408040540000c968030510a0041010000141d00040018034140000100d00049003600f4050b0701f4080c503000303440765100a00072080d40c04245a1000c004043c841c030850700080c5900d002e1370900019103100703a000700c65003120401004202d0b8010740c0c0c140350015041d4490311386020b41401c0485901e056400001d40c01800c0001d248042418215018051860005c0170400c01c103043d103444e40100c141e440000d004c0c3e0030034400210001e01440260503203140604000c640741c01a0300000d0219461004100c0c040307590f0b60510014000100681049a0b107080c680d44240c0c20080161900f50105204c0d040c40341070700080358011515150804120b8200c2d148041e0a010307103549103e0702078502032440500420f9800d0898078698421100001120b1040c1e005e546 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 20240141 1250 20238891 20238901
    0xb040b04030611090306190f02030f01030f08130303030506040c020105040f030e0a050307030c030308130c03080304030c0f050601030209160503160203072406090c0e0d020a050307080304081204060206 88
    0x1d0983c00b41c0070b2020308414404d45035942c4003400460700ca40103443c10700d07501015410721030088400111440441610510800400b80007110800781920b421130120140392004d40703099805445000360b515011811038100004064054004900424040b0f505102490089404908a40040320041c2104034504545008603018000103942c030117000d07180d060f4154444000c207107003800c140d10465081e00c46c038404001b416405403215400c542071400150014031661240d072051801d9000180c0381645c000046000c05008070881e151081e481010310f903e01e1070b0f03400c1a44d00c51800744010b90140c00e5050010702c0303c51100c20a403480101544030141076480b0740090021844286400340150b11080010b00081010354003941c4654500c0003211f0040c2105100f408280d800310341c00b4428080c20008034840c110780000250500e64005d81d07884413541e1190000820902d00c45d0b11082d0140034a40c404036194802000410983e9502d604480031001034012000841c030840c8500b60040e000301c4003140b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 20241391 1250 20240141 20240153
    0x20f010b18131401060825050907050c0c0405011502160614070f0f0f1a010609060e040603140a0501060e040b130501240509060406080d030903020f03030103030302130b040b0403 78
    0x200c2c07180c01a440340030b40b85503000c0c81d2401c440d80c0750041032040e03000582400e80b40300c0b034000d06000c00c494040040340c1146441d002c2110704601401000500c003000c80c41d601002e07020001e1120030035001780180401d503581d100d146024180b005041d4010b005807801c2c101c2c51490405544111802c0d40e442c0490750a100300c4400d0a40c00c8110201c8480b800f003c0c410020941800c24800194043e40c007985106049203030690307001c0b034000d030300703400810743e6000400515030000c0c000400c0f1812070400030f04068030500054001c280d1390708020500300c61b40125418551000469400c2c1610410007080b015840740c5846004c4001100c0003040d82c1c0c02040044c4002119a107103c59443c030130000800c45103860100006005010b21081100c103020850401007442c20360091030300030300e06941c1004030904102d180350300c07100d20944c01d0f41410b8440b8542c00415100300b060555090044041d2916942c591074002c010b03607c40200c8126503403d210003c513515443c0310071a4120741c00b03030700c5481c0b51078510350340e00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 20242641 1250 20241391 20241421
    0x70807052a060c040513050906060402071e050609010c02030c0a0311070b04140108010510080a05060f06030103050105010f0b0f0703080c0903030309010506100201091112010912020f010b18 83
    0x1d4018892007110500d0422255014141e5504400d443d40c1c00d000c240410381c0745e040600c1540b54204821701151260106809402544c1910003507a24091400c2c51446c007244002d00d59510717000403122000380040828030324045c0c4050002400380b400070a40817a80c2c0d00615600c0c1404d1303003100c0e0a050010740a13440b0680301072409001d071440d040d03032081d15294581090348240a00354004241e0b1900e5a0701c401c0c4140505022900450030002d0800000d1030000018500c01030140c0d01d00101e0380540d910340d04007180c02e070002d0419035250f859160460192100f842203018030b0f103020b1804a400503501d01940c8140c4440e2141501f00a4a900c1c211101c0e24054000224483c04118140c6561802e00042d449000c42e0000030441b4140041400403081d0540d28880031649072240100000d0900325008094640489002c01d0800d0701165450060076950030042800c11084141520160081503101d141100c2d00020041e9003070304ea042c80120791503641c0c90502d16202c040015000b0580401e0b03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 20243891 1250 20242641 20242687
    0xa050303041806080307050106050f01050a1b0201030209120109020307080f0d030f021e0a020d05040f090209030f0706020d080603030a08060103050411040203070215010b0f0909220f03030507080705 87
    0x1021030102c0d610400c4d44d003568029141a10703c0c0c3d45031903050219007800c282c82d4045c00d4003031070007038900b24a41c14014400c4407a200c1021000007a55181015603219070180c070301500b00105102c80380000c11700858020a2030710000c90107401080d000141401001c60105988800b003000341c98001144c1c0230803070061028641100920b6400e0060700c00440100d02d00b1480c03822140c803c1565546581c070080d1411000e240c1d01001c0110400080c00b0306031030711407040125a43c41c600542c540000000203820651030800c1c841542c414088005140c1d50300092000c2d0546958843d0b40644e180c0400f81900c901c20350702c0810100b80287d021882c0c0e9480303940802c0e440303401601c1e054418018500020300741c0e4800d64408006a10000322070a0b0351a104405500400340f0a940c0d51807c00d10881104142c00b4400003a40319151070000070b010034811203854060102001e624109203d03040c546a00320a03107400c01a80024030b0103001071a800c0c040c415803030140040e9155641000c0d100451301c2034580450203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 20245141 1250 20243891 20243939
    0xd050307030e1504030201150609141c0602090a14010215130b0405030a030c05040302030c040908040306060f090b0603040b0c0a02070b040b04140303070305040e04020a0b030702011a0a05030304 85
    0x40040804240721443c00410350802803445403c041c14024292030b040d202c00161100e108034100b003559048002d4500311500d225210340408050000143e01e02c0c0c410b0105034a01c086406c1401c01c010407075009100c809421505c1501160312500032241010310f0b14141400f5912501c00c0000101c0071918440d40880c001c1d488600480c402d94404140703c6055908441c5584041030419034942c05004490154005203003840c181413841d00001d5407504d1491209024039076904d202000d1110160031640616007216041c840280d8900c006000b86c0ba440c0b056221091500240c0203040c07618034200d80c02690082000101902c404400115607440342405200350b10815000040202045010300000c0c040c5c401c00075161440c040c100502000b0700c1c46498404d400401031440020303040000c0d40d003500d02000c003038045981c2c4e034408540003429680000010345c00c04410002c0c9190b054103c184020303208040f10510301d11150a000850340c4034001c00783d06030400e020502c04032400081503d0300d00300382e45c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 20246391 1250 20245141 20245151
    0x110918040f1b05060d0501050a0501021908030c040816030b0a0504110405061c06140601050a0503010b0f0d060e060a050901060906120603060501060908060c03010e060f0d0213060806010b07050d05030703 89
    0x7411617002c542d8900502c0d88450040000745480143d070402020280040d02c84003415003040c42e150200800001c141c0d010210209000d5000c0006a41c060701c41c1604684c441311048a5508110380f4500c0102c0c0ca110546002451f0003c860040d18040c0b50b1101c110300070140c100d001c200140030000c1c441d03900042d460340c002c840302da051808806680d000700400a4412410401041d40ca60003c104505104003004440f00a0f98400c04aa0442c0d10905065488076016044600b0754401c014030300a800e0308005010650310112840c00303020722000c03502540c0f42560742c018000b2506003441034001042c1c00000410020307000e00c01000c411891000000b407090384995a610446500b81c2009000418060741403002190400c502d5070003581c042c2d00142150700d40b200802000d04028803003800745c00e2002d120001c5840c2c1e05010284540d000f40803050000700c0154010042c0454031032801c0c14402c1078000076801090303804854903150090068032884680c40001e8135140d0000c1c00b03c03420181d641c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 20247641 1250 20246391 20246399
    0x40506090c1003050a1e02071a0603071a040e01030c0501020d02010b03061303090e07021f02180607020102010219050c0c04020301120311030c0604050d08010e07020d120b04110918040f1b 82
    0xf5581d00e0f40c0078524640040c0c030b0f400241402441943c2d1420300c9e0b1650001d4205201c0c0d80d55000070300300c0c201c642401d0800d8614000c4201c01c4514041e6030301401c2201062000401008015110740301610000c1e4201c076540f8041c50f030b00303d090321110240c26070160021000302d080080e0500304202200c0c000c2c10000b5a05035512055402c1c500125401d070010b800c00c2300d02030400c0785904450703c4c0381140000b0079401e164500e002d0045c080414003049108140019024003164000e40540e00e0341c041c0700c8804403ca0b051501c0140c40341d44040c500000034040d46200040d00d00e0a4400c0c0c905a69070701110103620a411360307040e500055050003145080c40140701c0201807413802c1100b1886144104084c02da11000d4602c0a0006038040c7c000c4043c100304e500400100c507900291400c4510b5951030070424a41460850300c0090002c400c403960408c1c104190700eaa520349160003002c00002c2561f51040b4100640c401c018814001c4e6030042c03e90a040c03403845e000c41c5002c4000e2400150248600407072030b680f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 20248891 1250 20247641 20247671
    0x2710030b150d050a051b031302130218010f090605040902030601030b060a030c1716080c0c0d0c0c060201110a0309080405130506040b060a1407060e0d0503040506090c1003050a 77
    0x44001901030380350f2a01c040044032592809102d420a80c00d250f41100d840c0e00030344040307a0b03000c000c099800708071444039003805650714569949200051980119aa1555550341c50b19450042c80c100e400301d0f003400d000710b1140b4421010f190442c0c895a541c40c2c2040c0c01c00700418080e500241c00341d41015160540350b44255100d4000f4802401d542c0c50000d0b803408010000b40c50348ad403c01700c1d948407003010741c2040700401d20103c0c1d002e1802060306d0281d44550750448181180c4c06040503420701881402e680980c001c2d00f20302c040200c036001d60740d000c0303510341e40d07480c228243e4142c45400e103a1590b041c004140c485000f034210030511481a07001c1410152200e000c80c142e0115101d040300815242c20500500d4213140c4500b4100480a82d6450b02c5c0c04c02d81c480240074140c0542e04180c0d80900060709000303100076a0310210070501c10000366110194440e100401030740090320140c90300d0107100041620081c00184410000c40081d000c00c01e008100b85060b00201002010b800141d900c620800c10b410f44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 20250141 1250 20248891 20248897
    0x2030f0609060a0608070501080c130323010e0a0309030b0910050709090f050411120102090a08011d0109020a060f0210050a0c020d1803020603040302030705010e032710030b15 77
    0x9001c001000030b0300c0c107101c4036001d03500700381d00492064120003c1071084d6640403c0321544610415407440d075a11012250403014241a8000341104000079948444082e4503aa04007000b038035100248402d200200300141c544880c01e60045c08120303021010000a040c10090b030703a200b83c3d103030181c80340044074000c1d00041e1602107031080d0000b0800b00042c030034900c080c4170b40f4003400000101008549800e039581c01c1940b44100c0c182e0701c0746032104012905841d0940407101c0024000e46225850307030380d44103902c0c06040d110181ea8800741c08185c001041b200144660040960010403181c1c0d900c0c54038130141c502c00e10310000f4200b1401042d141021020142c05070300e002e41c00e0400700141e006061880281066007030a003a0040202850910081c0030101a00345c040d203070115004d07a41c0b6115490281d02d14450204010029401c0010036200c0c110044042e001d0000b5041048201c04030303110f004e050500c0680708540c0d01904500002c0503842c842e5000c0c400300b0001818540e41d1070700d80c46200c003c46d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 20251391 1250 20250141 20250151
    0x12051b010603140f1b040603060e1b030a0b0109050408070b161404050108010306020d06050a03030c050d03020a0206072304030b010f09050402061204060605060309030a09050102061005010c02030f06 87
    0x69101e52040042004104101e40d5942c49031000d881c401083c100126207070720401218484c18000c0b41e81c0b401c03159849034017800085512407800c002c4025510161615284007524001010700c1c00700c804103407810049000d07072950341d106803982c4040e820032044e20000c1602030810340310705038144280f9000409503001c440c003502d0407000044050b00100c00040c00d0403840302581212620600041207584d03080503030a03055960101000d45c0300e00d24244614000e2465512960348000700b81000000d1540042103a115140500140c850a640c144030690a034801d03581c240e230050344140005824148648012013607404d001d1800154034404c42c030b040c40c007a041600f003a120341d0b107110010400c801034aa10003000300900740f0144581d241c56000200180202c10300090440d80c0c07000000d082043e55070044015000080c12291a81040b040300c6603607822905140c804280c8045001c900e0358000031b80640710304190a413000c0701e070707003008011988000d0742001260148140c28610f18000c1301404140d2242d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 20252641 1250 20251391 20251393
    0x30c0d02161a220209060301020c070621020702090f0907031515080c06030c07080c010903050c162d0504020f07030801150212090d0606030602091503010503030712051b 74
    0x116440b01d03400459030300a480110301c104038201249408850100840396260101d90300a100d550b2000400e01a119000b11010180101d1001290854203d0000100021212448041b028180e50071104911590b840690312901220000b01017070203c00115501c45022420390b03242581c1ca540300405c00000d81a800030340c41d168a2400610000d4414030740051441ca0000c010140a89000c18440e200203000c000c1005400218901800409001c0f1107440380140000c010b14007850500900c190840492020940681100040c0d500711704003c1d031064408012403840d00c0c68882c2c46c1c840c0910200281302c01c01030800e603c00910342d5150f01c0540b003000080758109a0350122880d005002030300c141c1114204004103010041d20076400201c803003c80003a0190f40780e5420311100083c803440c540310300050030b981c00c0450110400280e90060520307100182c55a030480c3c000060b12100d030340001d024164259105011210220b92544050a14000c0d2410400d10344041548080100030f20b40c8400406 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 20253891 1250 20252641 20252663
    0x901150e03070e06061b060708040b2401030e07091a0906030703030804020108040335100605070204110405090108160603020a020c090910090302010501050f010c0305030c0d0216 78
    0x218580112488248940803006402c0d49410b00c8103003a55854060049802420003081d0f009004641e031214510100180d4100c542620707004000500308501200c00305c50f003191500103e1030401d01000700665510103034250032062400040110014071701c9008444161040510000724070300c45200c0e0088903d1407071025014194403200b800b440c494080c4c01c0074082d500c060802c0011a60004006070419030918100c5030548540c1000c6030117112203c49200000701031200c0350105101c00a81e084d4071200c01c0005910382d5200560780580094610402000c1902000720000602d442da0241e1908200c06441b00d04090b150320101e01e8925090f0042d240c503600001c5890101c9107040c480e64020212440c081d85061558040203454001e84078800b8001e09868012441109090101505030342c161101041800058200203010302402e1040c0780c0944905c2d01c4001a951240c1c0440f10100d0b0107071609807842c0c4031810300b250036900030002d500d0280c0d400d01c40d06c000d4407210080700c04d850b80a80c0d00050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 20255141 1250 20253891 20253929
    0x210d0e01050412090b0a140403020405070f080a23040510020c030705150105060403060506010c06020a0509040e030f070b0702011104060306030209070e030c120309030607030507090906140f03010b0901 88
    0x203400000b140f0040c05001030f0708010088040e40c1011141d1401d0346d803402102000d05208000454095504020341c000d0801013046210b0340c0c03144281000c44250b070b99031b12194450f403041c0c2e000c40303864103600c1078585c41056102400035a10301107141c12507c00d00848032516103155020f012600002401162504000b85c0c62051090400061018502d60030060149501d03040004040e8412807000500c0c56441310006092603002e001c0343c012075a002031066640b8061498010301c2035210803441743c400c4d4600f94030294560740010559800c080b4036003001f40f070706200d034840003c10030340101481d0031503413550074403d0610340e010064002020561000701c1e58505500c1005141c5200416141c02c1085184020545a4001510700783d0b00380d00b611003483c00c0102c0b20015045d0300c11400b40b582c0520646c814031962560540c441807040f001551150030b166281c0100b0820b840b80307032041c103c0c42c8200c05441015031600000d001014036000700000307103c07030608010a1950b6400d0344160140811280208 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 20256391 1250 20255141 20255153
    0xe0d02060709050a030201110109060c03021c02030103081b12040f090e06040f031d0d0f05010e0a11100504030609060c0207080307021f0306030507030b1504090203210d0e010504 78
    0x303600500035042c45940d881c1800049401100c035440040d041150700044210b081d2400e51188080c43d401003810b000c60844104050040d41c040f012615081700e0701c11b0248840a0f452090b01e041e40e5005500a1402c980160361b080e480d0160341282c0c1c2d650084e4402c10765400c4142e4014401400892400d44503d0f00e04001141200c1e00340341400c900c1e4201e2810400050304c6498050b9544d03905040c05141e21300309800d001108098548403a030808402038544042c081c038641c1580c04da61044e4003d0040600c101c0403a616124054001040c58402c0182c084492038901c1c0712500c10003961806504180e07a90325454240c0e102d2000540304e10369107490800c00e00350305014180191005100a6160004541c00720b08a000f01044000c540e0815010052401c0c4c80b0340c01030310040d41c0120440b9a0036440381000649103d054840006480da211540d910700e04090185d01000e07030700100545920903c3c1804190700825048916111980401003841c1c1406207100c2c6c001c2f0320841d540001450f02c0c16280c20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 20257641 1250 20256391 20256403
    0xd05010b0904030e180103081909050d05010b042708030702030904020d05070e0316031502090406030332040506031512010e06180607180f0b03060f040b010801090c090305010e0d02 79
    0x42800c4141c5c450040c8041441903040310980c00c1915600803000c0c070000400c80d00c0894607008a980444002d84032401e1010542081c2c401800445d81080b030041c036280000400d03040540c040c1040203c4021290228000c0300207580d01003801e006803880c0010705800a000ca9010200380018595a0400c0c0b1000c6030307002ca0111070015083d0002c000c51415250750088a809900c40200028440c000d80294005035406075548880094014410039440c0c0c138001e012810052413512000456912191411084d8145182440c906060884c43d041c144000c0c821039510080c60701401070802400c84e0010344841e41103c1405040d8400015500303d0726a010b030414002070b01400000104043c0301607041c002007100c40e0015064100041c0c2d040d00d2100e08000280958408402e2003062000003a9020501d80110700c01c41044a0000002d00c202040008480010039624005801c01c00140305c0106180e0181c80c403003009051802c2060f90340c1d90f0341c1d0300750b42468251041c00d03088244100400f60b010402 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 20258891 1250 20257641 20257669
    0xb040806070c030210091b0b25030905040c030213150f030207081209070e09070905010602011802040507030b09090109020102060708090d1803080d0c0f050a0507020d05010b0904030e 80
    0x42080070b2075042d00d00070341e15824502c0d10425a42c1c0d07440e069003003010340c2150f1241c01c0f1610070200c000940d034401a0640350441c200c640c16038240d1300807410f401c40140851824095068441c000010b0a0105000003010103200b00001d164cc20047e03040d8440000102d44024141500002c0e4190741c4000000c1032200c5d65000701d41414010b201d50000540010140c0d4202d500480840030706540d22010f243c58030090340e0003481900844003d01010b900045001c1c4107513400014144100c0c1d9031120308900300c40618902c1c05d40c0c0c8024072500700040c5402d801003500458507190110b402d452031400903d0004c81542c4919a0340c3d541d0103480110350301402459803200c4541088003081c80d0840d000c070380b218000d680039020845500c80c0d01004c040703007800b40c070b02658102c02050b8417880300a030300307600800c6603805004c0801c003180c0c2042c00c000d00c280b048441410407959210f081080e41d0f400c0c00070030208640111030035501e030800c0162941310445264401c1c3d00990b80c10b0194111001401200010308030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 20260141 1250 20258891 20258897
    0xb0d0603020a05150d230403020109050c0f01020d03110c0706020c0a0501030915090204090602040905060901090c0f05130314030a030f09080f030402010c02030105090307050f030901080613090506010b04080607 92
    0x142d41103181d03400d807064510117940c1c0c00307000c5901c1c0701d2a009541228a01c1441c0e4a610541c5800c3c40181541580205842c034407800403903181440050130442c000544501d1a40103034001055507940d688a41c108141d020301040c085070030141403030b07102c500344070994120000603032150034180e00c5071900034840c10080c0030a007410066024075849541a80c2c44450f03201e5045520b034075002c0c0454803144d01c12442d40b46c111004544840d11502524090001507401d548183d0300d040c00440c0180b074610070109400c8141e102d0482241020800b81c441d50071503100707081c1c1c040682100001040070f0746020414005100042e565030040050050b00701c1d01514006240c0b030346044241d0300001d44120844100f03000c04c0310000e8803a5520320040301e8041c0034500c025090b509140c181719040800001801065208009503904c8032a40c80c031250741c034080c00c001c440c000342030034002c0346450801498070303541d0a41009011803600c5550321759601d050000c1e4000b00011500140810001c00144030382500804289 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 20261391 1250 20260141 20260159
    0x180b2106061602060c0a0602030103060f140601020d0c02030304090510080706020708060f0402121204080c0414060d02060408070605030615070302070306110702040911010e01081009050a060b0d0603020a05 90
    0x3030101403480b64030303000a000c3e00300043d042924850400c04904200c0c0e0210043d50b980da1249407142c060311034120502c081c01e0078800d1104100800c1c07283c1d14412401a03004120103100d06004880b50803c3c0b140070b0382c06000800c80840d07041454000c10b44115002e41c01072040c01d2814096914084555000400b1508102000c1c40006e1000c104150003804111600e010b580b02d50001170341420818000034254440c7ca052060340d00002e2020b842160b80c6107084e02d941d031001d10107000541d82041211b1020400c000006401c900c1d02201d40d4800c80d00203450319003001c0e102e44086150034039a130041130100d100402004220700d400726910450000a00c41c40c0d00340285681c0c040c0d6920250301006140648504c10449040e240308140e41d107154000780107201c40045e80c105030000e1036001e44981d00082c011110150a0750083d903500303001d5042c1c5035003d46407510707280d0040003c10300034080110b000c0d06c0b254002602002c80b400b50948040d102070000e0058a180304002d2f000040d540314a00a40861b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 20262641 1250 20261391 20261407
    0xc030607051207031812080a020702030a02040207141501031209080d030903030e0d03050103110f010c0b060609090708060102011d0705010c0503070506071d04020910180b210606 78
    0x1054800002e4590403081103601c40d164168060800f0914011519440c1c611040603c0602409081d900c2e5003a141d010366074840c0d2100509034890610301940560142e4281001401d1607401070140310b02420710001e02d9564401280d04001e880c0d0304282600890900600a11010108100e80a48a81018040e00c2c0c0317041c080a0f1688034841d5000241551000c0080625010303030003111000c501c00382503403503114080401030002c2c242800180c40d074001000c017400c1c0c14100b800002c01c001005841e00c10100c40e003991042e030303001402410385030801c83c1400200c4a40d100c01007480c1c0215155183c1505a01e8610002800c544800030312408460056075460500c1c0300106815054641c00e00c2e0605850103c0d0808a195100b40f4000800d1fa20a00042011841c0d0001c8581c01142d00324800018004e0035a01700b0040e40608502e20b075102c5520661621040e02034091603804400c08581a082140e55208514540c3c101e01c083c0e002c0b00c0c9180150f292400385c00304d030383c0340e100c602283c85078109440c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 20263891 1250 20262641 20262647
    0x405040309090b0307090e010c030506030f0307080a03060801060b0318010c0e06070503040b040e04050709090b0606090d02030f0f07060201090c03080307090806090d110a030c08030c040e0c07050c030607 89
    0x2940b01d005032640d40c40380c2d00007241c1c805001030350103882201c0c1e00780030a05440800c58000c04e1581c100100091401020800c949004104081c48500300d000031403c00e80c66845044055010802c2c60f014140c0d28000001c0030b42080c09004e005100640a1944914050301d03078181e01084401d00d0003a59240600540d56150080014000d108040d540192207108500e40030b46035202e00c2d00031403002600071400043c900c80981c05140301d20710400a5485503642c0740f0071102560030048004040d011404009801400d250014012040740102000d4403a01c0c160040f90500f030f0015031843c0c1903002a41807040000c3c00700001e000406180c4000c2213148000c0e1a40070100c0100e000c0103151080c0003000c507042a22405125010b0244101517400b0340c00d1011840c0d9840600740c1e05200800e00d140e11100141001240902d0013541607159040e10501596420700160300080000741502400d2101084030384034521204d00c41c040e441c0310341e90354103054180030345010003000e03000d03100381d210600704140745074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 20265141 1250 20263891 20263907
    0x1806030f07081b030115020c0618010e130203100509160509040902280501021513020f0103020f120604050c03011208070203070b0a0c0605010906080d050f0702220b04050403 76
    0x100c1c0c1d01e00b40345540c84080c21040c07041c03000300b09510300b514044004a12008002d0b461407603100c09030200da031110002c005005040c020480290001c802501008001d540070345204496079100a00141c102c0800052007070403030b0002e0f01c0101e0140d4030070720144071908000c804a604801d034058401080c04a00000038211310030300756543c1c092512800041c0454071160b00c90000700e510415950761150140b030040c0801d45007031003014018864428070500005005403428050000c40341c44180d045265003d0021403200c40d81c200d41010741c2000112044203292025021f403041d030104201603814014204000d8400c06040300d034608604000400c1031040d0710200220441e40f154130355807200c400c1e000003400c1c80441c0d44510880750002441800a41d0b11111405100d0b2040600700f04598960103180100c42d540e000340d00041c1c1c0300e6050070700030034000c1c80034142c0c01c2c0100b49514900701d1107501140c05810700100c59082c0362203101c0d04158500ca00e01a850814006840c200094a082d807001010300c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 20266391 1250 20265141 20265151
    0x4080901030501090b0a0306150b07050307030f03020301030c0e091501060e01020c1002031c06120605040212010c02030301230301020d021308010902130e0a020d03110c01082e0f08031806030f 84
    0x603541c9044080c2210208020001091104c00c219110f03cbe6a0516030340720342c0300700c00460000b00080314445000340280b00350303811789030071922014510f403c0540d580364a04000c1c058251511507441c6141d01c55a40c000b03424064601c40d41c50507030055024001a103085c0c1c03600320451040c62401c40c0034410341d9000054540c80320241c2243c5c504580d152a040c0010219904881b40c41d070a1240501d040c810b00703401c81c500451094071308440c0321024031055401c0f642c1461402005030010001008881e40300341c0c00d646002c0301d09c01300400402d0381200007801ca0303120b00c80084055402103904040e00d0440c2484500030480d900081c003c0307114940c0010203c0c8014140030b102c06a80d400850b00c224800c0106010190380500352844000c042d042c00b03800c80c0e44d8000400075600c20a10402c00c0e5512a4580f01c1c06140c0f001030405c54903084044a01c100c200040790302c40040c42c0000c001966503500151000105001d40281d5540d4030001094110400b650304510701a1200700280301d01d0b0100056099441 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 20267641 1250 20266391 20266403
    0x601080601050403050703060c20100b0a05041a0102010c0908060105060f2709160c020f1503010b19030209010516050c0d06060503060a0903020a030c030c080304080901030501090b0a03 81
    0x40e52104010795030741c00307070340c201808912800070040304002c4294807960041c0107580f03440400100c10b01d10b103061000d21100701d400942241c1d00841071800c0f9038000d80000b14000341112165501c0b1408a811034a20781c1360340504003002490316006503020700c81d00c85e042c41c1c1072400e03003410b50418100c01c0e9558418801c240c0541d000082448000582c0d00a4507829941c03e5080c034028030040c0d064084000511360904e1040e000c40000c071f1090080d41100f00d41c1c2c40320a071200210f13030041d5000c00c500c0100c1982c0765500900c014002140c20640300380114064111899601d032200340421000c070720740058880d0b003400d15104001084050f07800100f074a20301002061650394100d09442d08a0400c02000030351a088148003c2c4d4404000701d5800500c142d500a40c07c071006a511600964107641044401070090b0300400c4030440030038030a81c3c410566034042d04000d0000e000030f50302c0c02e0b0940c2c0100c5041c0d0301c82c2008a03103a0358640c1c0c14041d0a0050130344001c240f0218220200048500000f0b100c01020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 20268891 1250 20267641 20267657
    0x3040e0f04150c0509040b06040810050a0e0f060f070f0804020402030a0b04020d0209031504030c0b0403020106150e01020d08070801060e130c020a03021504080405011d101d01170601 80
    0x1006140e5800d075071070b149240014020315440382c001521a821030080d40e8170540c1000009401402c01c45c2c10348044942200060141811081c01d90300103203400b40800071451780700c164070500040704000f852341c0259100020001c1d490800b104c807605e80c10241c8404100403521403401001e590146000f030b0081c3d0115001682e03501c0d000588401005100c1095401500100b443c0b035120000740d024010056040c0c080c0c07401804114040e4020180c01c6070000d000c58200700890012400c1080c2c4d40b43d10521900000403900d44801c800900c05601c120130500103501184100c03800d590500041800c0340c1c0d107082c00f6070b440c02c24400c00f034511801402180304006500507102d05030f0740c6443c42040c0030f09146000f000040c3d00e00341c0083d11000c0001e400c2d805803044100d0310380c18a012541080c0708a800c00000e03820141400d004480700d00c0303d60031522030400411981d5a8541d41c41c400902c4542d42601c400c0d0440184c60042c40950003d00341d000d051184c80030716040e1072418004a198020340920748841 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 20270141 1250 20268891 20268893
    0x3070803090a021203090406060e13090c0906090902040c0c0b19110f0309070806090a03030b010e090f06042403120c0c08011a0604050102100b01050c0f06150303040e0f04 75
    0x22400d02e11403000780d07108020050070003030508088010002c040c020340d03060151946450f000c1d144d049200d9245034221001d50b0801030301c2c0b01554041220365200381d485100d4295120001c4081e20030701d0f00b0010f906941ea0950340b046203443d200e00803d400c19410206000083c03a11608a15180245610444140b0603461400074040e644403107407005411842d103888480140c4034500641080740d8100d114865a4030104001c80e0014003144500710b00e0001300707503010303882d5001c07000707048205011070611000300500020350780e542100b82d00c40d070b5180c8a502d2840c9800400c100580304103903101015548408000c200d4200c416039481c0c240d9030031028507001004413090445d540600c03008040d00050030b001002c0741900064120401040170154000d02c00e4427a1410026144110310400e805603012104c1100303411181c0d00403c50640050514070f003000f49440c40c0c503050501481041c581a08000c1c108030004915030f0013031007c070394180d00840c201410300b451400000809000b044a40c203607400020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 20271391 1250 20270141 20270143
    0x90f0a0e03070b040c051915051c0b0103050f060105180a0b12010f060212030f090a050d05120f0606120405030c03071118070e10020f0a1208180307080309 68
    0xa1800d600041265030355011070811062140e0203680032100001111400641c44c9800c61800201c0c60074141100c244a1800c0c06c50800e8a20800080d070a10000f0700c01e25500c071001088108415041034008150703000800f000400b140c100804184100c0c3e500703002d204569910005803511400d01450005480b00340c40000340c09180071f41c0c01211054000501c1102d40e82c0340900030360480b0319914103401150344594041e81c0350440d0f0440c110810b6824800038285142c0c0342c6040303400452600988541c0b0002c2e0f29020304100780b031500c00c000301d400029442d18030503080d20380b41d6118446042081c0141002000600c162145056078006042d090000c00d040c042c0501c1181c41c064031810480e551081d00b8902601d504100007002c500c84d074401102c1002c0b03690706014403840b030a45a550140e240008004002d420203440117400114421031401c400100d00400003444082e004011115481280407002044e142e0000c115011015901d040400154070000c00c2d10a608d40c82081c540d1280c3d6280001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 20272641 1250 20271391 20271401
    0x12010212040305040e07091409071b0309140f0a0303050903070b03010311011409010906080907050d0b01050f060a020a080901050c1608120c061306020705030a0906030f050402090f0a 80
    0x2400419804000703100416400800800c120b904140e014a01e80d61000c5054030800042c4c441c1c2418060f4401955646180200f111350348030300c1c94106510040c1d504110f95408141e0003604801061616405021030f100390711040c800c501c003c5a4550761526100d0119900940714440141405408aa02d41065406020060151103800000c6441e581d6a00380b800c68a400c8606c114049001c00050702c800e000e40034102c40740c00c001a15108003071407521104076541322000301541580d00900f00040b51940d160640f0364092801402207942c01c1d41000c08014083c94018001d45c400d5204000380300a25402107240382c1c02507003210070075840d0343c059001030f2000d104942c1003010b1806101030030002d61410b515540180d44110b01240c143c40d14050300c544031442141d000e410300c0d0b4000b80000d030442120030b80c0200914403070840941072126a03078030985190050f110382c10100d41c1014052041c0395041c40b880014110b140c0b0706012600306030300031460a000281c04000003e28100005440c1c1120741c01c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 20273891 1250 20272641 20272657
    0x61209100b040b0d06020a090b0c15010e0c03160306090f02031b04030f080d0b13050702150c0d090f050102070f030206060102070e0604090c0803030a020a090b03010f0b130e1602060a0515120102 85
    0x280960313a0211441c403507118013408130075000c10032f04003001241c036025141e9030920403000098013030700c0e40d06d5000a0000900c06000c008040503281e4201044240c031a0081005d444941d01d400750320b030b007080c44162880414010440d15100c0d81804108041b80300ba80501c0305007030b00901080e41d00c020541148000e81007244146130020290b01200c401042542e00c0310f4402c2c1401d03429240e1050f078011004134940c00070707156464104401d014465507407559a105032100e0344940d00c1900c02400507a41c1c242a40c0141d8001d840c4c940d01c07003440009040d0140702d02e0354800707000d201802100e03050030803140d2004c101074210750003159119252820010300303107009805031104004a907100c1c68040c01d0003020b503000b40000720002e013424100190614800f0705580c140d80c005824104113509001c4104416046140d0103034440141110020781040c2c1010003034060140e03049150080c4541a0000e4a4200d024012455075482c149c1008180100504058041c0e002107070f203800105038007902c1c0ca01900507166 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 20275141 1250 20273891 20273909
    0x7030e0607060902030703030503180105010f060e04020702040e010506130207030801090902120f030a0f02010e06040605060d060203040804050f06070b04020910080708060105120a0c03080306061209100b040b0d06020a09 96
    0x1b0b01009060300480914400c0701e05250701d82948900740130081c00d88000381708042620320413401c103201060003103410340c0c8441c2c009003005061900580002c1c083d10800e890074482d81e50348206004450030408001222030307885400c1549010340301e503070050050740c0c140703e461120b5541d110070721700f1562011049207620407000200d46222903030f10090361312680303c5e4002c01d010609040100b00c6181c0180607912205510202605040da20b40d1034031f001401c0b0080013036138850546550000040e01d80e2000e1030007140112035858545041009106a07a5000c8044038442e140034459440058020581643d000703a0560700b400c419218446100c694125a401c6220140074007000450822800600203048504c00c0350040005460706403c662a00007109020b4864082084103201144819004541280d00a01440d03d800c0100c440d42e8268002038822074080d030400c80f02aa2241404d005034580c58408580820101c10418002104017040450042c400da40200351000003600a10121000b005480c07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 20276391 1250 20275141 20275153
    0x80415030b220e0c01020618010209030a06020d050c09030a030c0510061d061002060c090105040506042601020c030d0902040b030d0c060606020712060e010b0a0902070c0b07030e060706090203 84
    0x511100001840b1030b4642e6001403a002d400964500001203109402e84182c000d8481c1d40c949080b40412110211803404556400700700e99101c0e0b417020401d441d03015008401c0107031039003032041d440400d4550240400c588405c0c1400780040c990360218012100d20f5260030080d440d440c0d2031901e24100805990491b801924101c0f002030424180c00030480c6010183d62201119a511800c000301c800080342c4000060b0b2040001600460440d4010640b01c07505042c0385041c43d96074030021350305500a030045450401010f94092038000355148040b41c42580c0e400a508154804a465a0b00d00480696140081d02d50307940b0015901c8a078403000c504013002e003c1e41c1181820a101410043d11514211a254a80784000030103501c003041d41c00c280c80d111041c045541449450701005000e80540d9030b02c1e50f55817410001650b035948503a0000401c03619202588442203801c011511024603440b80d035901104102c2c000019074400128000414211307015038503441c550420000a000c64030000750180f08103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 20277641 1250 20276391 20276419
    0x15020a23010b060301080703020a05040219180302040203010f090c0201090506061003060801060e040317040b040b07120501090b0a17030313050703060c17070e010806101202030c040501030c0507080415030b 90
    0x202c7c1240540c0c5c02a507048220650319420300c0100e01c00c0903600c440341c80c42ca040c0d95a15921a1030306002d1107501e0310041125030b4807500010200d91080c0e01c56480300042c1c00381001041c106000c2d1002400c81800204440101603d0702610b605008142c0c03807040d100021185803a6010ba030000c400713488114020007500da00c41100010851059070181c002c2103070090030081c0d448089056600ca10b0b0700c2400780b81640c840c0c1c2e40d052060040586040c0500035820a1100e502d20740e4855540200720840000c508500058140160484140c05c00e414180e001c071410140d103140001242d8021511080344c82d2247e07000d0410a003008196000207215508090211034215403042400204e030341000002c5e032054a0395442500d555104403000c6011500d4880040e26914110340c15010040d19400e04940c2c3c41c9400104200302d900171a1840c0340d10320041014040b40d68941318400c003401490802c2407620794213841d41c040a0040d44240c900e1140d0008101e120f8510940100c030788000054140c4189048ac = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 20278891 1250 20277641 20277643
    0xa110708030915130303030504020f040203090a0b010909110f0f03030703030b090f0103030210052a0301031a0c0d0209040f060b0d050901181e08040b0415020a23010b06030108 77
    0x400c480283c0b06000280c1c51600514954003180d03107610981c8980701920340356540035405410028810b07039000b9101c0310b41584540b110300065100382d20040180c00741c001c29103402e084101068020309000d500c0c0c01580c0002901003050101920000c8400a0890901900148000c0b0041c0000e03901400701040d00c104154064000c4014290110380110729030303607000341c0f92031015024440900180d00c4000090f00d004a15030016030489031018510401012103040c0b0802d4a11041001700014000801001030201c03d02440c40d4044000d00b0020300c90034900008003060107656800007005600060a071000d60300ca0f4040302c130091910400380700e02543c41c400002150048043d4070101420280041d07155501071040c3c20b41a80e1001141c00340302c440303407600200c1440d4a8815041c0c0c00c21490400045400607029000031301f001c3d01c089565a060010003100400e540d81072a0a44d8080600c0301d000500d1040c000d42184c00d00c044414003081304810180c013400940403400d4000500000102d11010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 20280141 1250 20278891 20278897
    0x60d020f03010f050301110301150c02040606090303020c0904020a05121c080402040c030e0318040209040219020d03060506030106030504051609060906050607080f090a080d120c0503060a03080a11070803 89
    0x58051001445913441c01070500381c6460600203801c0160800c01800075403401c20311144a0300701460113050100141d40420201c0d041c5400450101380100700801c00c00d90b04021050300440161a88140c41c140741d0701091150440c0e010b9188114114107204120310030400090101103e81c408101c441c04105401811502c41a1000e900075400d2071445030f0030038024010010711a825800030f51a003004c9010004408103400480b41d803041c0c08124091035560385001400072000d010108899080c9278034406841e10045140c00c074145418031000f006160382e04d0003524111419406e020070981c1c1c2e645070080c00c040c481582800d1b51a29028003194a8083d68048010f5030780c071180c1044081d40740d00401290307004540c0d00900c1b80b1000c010289081b014440600105107010345a00d440301d0725907900d9402c00800d6a00f640006101c25950100341000b0302492040d810b460038480d24508020001c116114018007010b000210000341810b9880c0c0b00b08d2400351804c50743d80036120705070303200c0455a8503a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 20281391 1250 20280141 20280149
    0xc01180308071106010b09040207060609060f050909100203070903020d03020c1306050a0308090a0b030a0509010501060804030c0204051b0708041403070503100504030207030606080607120203070e0f060d020f0301 93
    0x604084006a0814000d119620000f0401c0c0000c04c40e03680b0b00051103240d80c5c009481260403e4081c800240011340034014400034161045001c02c00c070b81014801e1040300b4040d440035205007c4202030050414021a881011141d40d810240c0c0d00d03a5000801d646102003940700a4003c101d8418107400e05030301003040b401c91070049944012aa4003001c0c0d580030f075152400f406500c005424800c10009a07001d005291001000c0c00500019a0315000f07940103401c12101031010300e4940d01000324022003071003102c0c0504190709041e0030340d04181d1070040885003000c0009008035035580200e4102c00d210048045c01c1021f00d110160348201901c0d01e5100c6400c20312076800b0a003610360982c00140341c00b00304a400e4a401030f0041280005045003000a05005403064003540030300500070011403444d00410307000c2c22480c0c00800140c10801801000c06141d5144520101e105006100c007282e4081101d000c0c0a04c22144210131142241c0011641e104110701ca02d100b510000b003100403404000c001d94103d03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 20282641 1250 20281391 20281397
    0xf0c020607080313051606020d080423030a0e0a061205090a05030d0f0506030601150818010606110607020a1e05070509070309020907020a080703080c071a0105030706140711060c011803 81
    0x46c42400c0c4943c245550039001d104003581010440c4a1054407030404240e00600a0000010520b0103543d045450141d001071114107410000e079a9240c103130010301c6844506000e07120010118900b80005080d055520101c6250f2512240440c41c018000c124214000b0f070030409581d9945411031028004041c8002a4441c5909010000301d82e807801150260403520384a103903c0795000070500c00c4902c002c0c001e11414041001b4120581201c0c400d220383c10142c60151980d00582a04154892400c100142600119400404080e0010312034420049003400042c41c0b41c042c0c0011480c10606107405a00085d400c5903200c2d0820003d01c0e0301d40c10010703000307000390fa028025481c3c0c02c2040362100c07840c220140c142c100c00c2000c440001c1c85903680c0c80c0d200d4503688071b550600e019591040301d098103c1d0500041074841600503c5075240a01190005119508096030410410b20720b000c02400b950401401d01048400000c0a41d22400c00b02d81d01031160700002c00650a45580001d20340f0014041a000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 20283891 1250 20282641 20282653
    0x20307060210060b04030b0a0b0a08060c041802190509040902090a09060c02060c03060913050a05010c0f0201020c0c0d02010e090103080a03050c0f160309050604030b0f06010509010f0c02060708031305 88
    0x1504ca00500311401d50350080015000c236514803440d50040d200c4000015000018442e0000f031000040c89054028036125109a070382e50721300000581000040800c01009030700c10040768400040b20202425500b0480c01c0071510b8141d01c10004004003110b1501030342001240c81005071001282e8401c42c45c0d43e2007440c1c1001123481c0c2502c201d80c3d42d181110f100b84140c2c420408101c6a10301000d4603580040c0e00c1d64000141d4030b8039030326a41000c015440480e4169100d03001d449009801002500c6007524600c02141401e03000441c0a58441928500328007d8010303194490959120303034110481010041c00c10042d9595a140c82c4065502030455000000e14202c08194134040200460305004040d48003d0b0030000c3d0a604103d01c00362480044080c003142d031100040544804024100031130042d51000e17406d141c165186003036428020552810010100100c81c0035a1700625100070100442c0340902c081811807010581c40c2c85000c00250111901004000c001841070340d10b0011144900d0680380303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 20285141 1250 20283891 20283899
    0xa0c020909520306020309010908070b041211030403150e0a030c0b070e010e090612160504060e0f010e0a090c031101030f0605030c0d0609060f0b0a0b030f0a0c050702030706021006 79
    0x40750300340070280214102402e00401c04920701e6005075800950030340001440c892503030f840c130420390b2150b4001c4409403040300400041c82001c1199624114082c140854a417000d89801c5031240300c3e41c04014540481c0b841901c1115825030302c603058280d100c10454001940d1070a0180122283d590221080e8410b01d000038003113403003078541d03070b081c540d040c0c5881000c41203400c2007040c50700d03000b0b00c0c1a400902e0b05100f400d091504200c1600644051000581000d0034581440700b6a102e60700950b805500c248140990140006213a5044800955140e6140d0301d03107083e01400b4001500024110100882d408410300404569000c1c5001c402d0700e04004a00c0030180d124181c1c0c4052155982c540c103c42d4002585042c000c40d440b510611520b000a0fa045d115503c40007140d4240003003480c4075659105c11001402e140c1e0070500540b1480004034150720340300311505c0c0d0070074000f8000c0c019103440c0c5003c8280680504141c03030000c0d9004007a40c080680700c020003503566100d03000d01d214281c203040e0005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 20286391 1250 20285141 20285263
    0x108010b030304031401090f03030506030c0109050609040c1115070e030a0f0201030b030c13020d06050607080405150405030a03030b0306010603060b040b0a050c06040606031101050a0c020909 84
    0x48452000603024505040c039580f41c04000038960040c0a0311552610348841c0014083c101ca4000f2300d120340c400143c1da080c082c01349450500c188a09030305001d03641e9401d10242e6201d10983d41d03e0f410489000c0b4185042d9241159078540075203442500d4461407003210389180000c42c03a03521400c3d0aa481303108a22640f01010b5503418190001b4155080c2102c801016500c0b80c1c024105580d805400c4030701d070707002c0390300482d559608800d22141002d81c0800e2021b4a25807030700443c070007801d0072510301d400d0490341c0d162888135104500c02d83d80718644242d002c8608201c00e03030503600203000007000e4802e0b880140c20054050003000f0180c9200b8040c03880003041c1140a4812041520300c03691582e4109420152101340b030b540255020390900c40103201c0102040000c05c2524481d902c1010045003036403451500c406a8006018824180581845091980c561210b1000d030a150110780340c80c1581c40f821141410f240d240104840d02d90301045807008413650b80e08912030802401c2c0d00d10329400d84800104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 20287641 1250 20286391 20286401
    0x61201080307211704111c02030607030b06030a090201020a0f06020307080601021204060e06071e03030b1f12110a020c0f090906061908030d0914061015020102070f0309030b010801 79
    0x141d020500012420814040c6504e8080c0d1151240c1c0c1142d010a584000142c950354402c00c00038a00c5604510340821414180001c0e500015181414001003050100240c4280002010401855900c214010540e0701c2003000940c490b4202501054044070350403c0c4002e54411500031021407090b60118449520004412041148500855062600780182100c41e0b560404000358031140134460348000c1079101d88000f030100c400700144181710301c151402906444004520070f200f10400151007146800d400001c0001464910700b8182200240c0e200400400951030082d458490100741509803540014109515250440702c00b103003145d902081080035001221030020a8000e0703408038100c1e08024092104941540c0e614070400c54982c8925450358001c1407504da011615070901006100c040e1100034152407004018090340e140c00e4504800144607481180050b200c8102c0c541c6400c0d200794140c80070345e0307441000c88507064494107008021442c1408182d950b5a2a8400064003801c14455 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 20288891 1250 20287641 20287703
    0xc0306060b0414010905100c170f0301030b07030603030f0305060301200c07050904020307090b030307061514010c0b070f090306060906050319050a0305070201120c030504050106150804020f061201080307 89
    0x9038030712031f42d00e880700b10780d01c080c0045c040714401c0d401c15010540e2450030b000750458070188100183c0b65855411705a1121801407c0c140034075292081c01d00106e648461f01048a101504011170191a4030010900400002c0e0701003e001c0038458034504024460002032180100d12000c40c4c2c0c0990b201c3d800c11048200c145c5000b58554040f0341d0410251226420011005200074162400e050b0380d511007000752059940041e64bc200300b603105208c80748407541c1e0102c600d80d00b0700c3c0517a0312560310707038034002d820902a08500901418440741520248140d40810195034491002c0c040329036550003d5015048600416200307004240b080c450f007021701c800001c0d120340c02c0350007058900055101692198811b0f00107034108228a400c5102034200c07401860030030303541c9680009062a2600300706007100c2c8950822810b121051190401d46036120035134941290b0101c8405c40c0a8a0403000207045104090302000007078603007400014140e00c08005080054001d400103102d2002000d0501c0c410045808 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 20290141 1250 20288891 20288899
    0x3030e12040311030114070e01030606210b060415050403060b0607050a030c080d0504140c030607020706110c12070e060609010c0303022a0304062006130c0306060b0414010905 77
    0x70007000815a5210700e400300d1007019000081c400d684140300084a0f0381110030314041000220b1071002942c0c035100e210700400701850328200c0b0520040c80104091003804440b120142c4a501c10304656680600303c8000f01071809448191520500002e441030b0031511094401c5894480200101d00300441101d007190340c0400a4800c4425542d01070719000e01c419401d40d0740ca541444911121040c0e88641400b403400341448200b036050070785d445894480d250138200c1c02504000300348002d1980025800066070308608010015410a4019038680102144110360102345451000c1c4520000300303034802914901d4802512075501c44040c0803c5215418030a400034000701104000711740700307034050070400440202e0b1017101448100d1440744100071140180080d0000103040003666000007408a481d140000c1080c400c007004004680c0340c1800900c0740002d1a43e007411802002486800701c005190f00c004100f1500d44c8500500406030428003480b079500c500007025014542c0906144d80884d28024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 20291391 1250 20290141 20290147
    0x5010e030304030c02091b031314011a010f05070210050a021b0d03030504060b0406080d0e09060a0b1b100204140108060a03110d020904080307030c090f09020a0512090a03030e12 78
    0x1600344825414010201c001f400414402e82c0c44804008000f1070040a62007103590918540b82006070100704d04100300401c80c4e14005180c00c00807541071100e07514500c2400e0240d0084081142540ca61190758002035110b010703c8040007072990004003a0182007160341c22541d00e0010404580f0202030440d144503400b040149034103000a200307030407155016109004c042817004100011606950710780d00400700d560840300030f1150059004855412040e422510400942055008500030540394010300210030b44c00944c5e11040c0041040d1107140501c1791046426035601d9070300180080d0450700030803203440c2c43c1101e2800258440c00005009007001401401c0355403031940c80180310360051004035002594225804c01680d903298070144950b024120180c1e403440d00c0e800080841e90030b80c0701c01d821b010b0b04071720920040d403c02000b04180c1c2c0c4e100d0340050750b03110018015205802a40140c1f802400c00000f0420f604030089040311409200307803000e00080d40e00c0280152941c1000486000c0c42d0424 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 20292641 1250 20291391 20291393
    0x80301090b1c030804030201050c04030206031503030f07030201150603090b07030f0612060204031104050c180102072105070b09100c0c090510080609150f18100905010e030304030c 79
    0xda408660318100080c10764444040090005942400c4494190b011444210801007419028000c20b44e0213004001e409260a0a41c0d000441500000d45039091051950f658034000752400c00489480c0684900c0c501d0310341d222403070000c0c0179050140030b01c5450b6150090000f8228000d00601c44040c0c2c0c000f4202c4039550314084100e0003001078070503003054203807100d1000807043c0b190542c1c400e04601800016039200e0450034421403000c00b64032400c2c0101d203024100301402d110f000039030304915034920081429006c1a00100d28042540d040340d00c50000c3c04844040020440c07075400c110a206106951a01d40d44205459141c043c1405480c2c1000c60400141221485000328600e0030344107906280d64180c0392501c40040310001c44510800d00e00391142400307000800c103c21680304d40c42900404100a41410038600c50001a10f00c150080b4200e01040c3e07004284000703481c1c0ca060300c02c21242200354181c0c040b0b01409402c3c106803101e501c0d02c01000d0701e40401004680c89150140c44100802007a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 20293891 1250 20292641 20292659
    0x1401090b04020f01020a0204020c070608100f03080f07020307060e100206041205090604090c030501031403090109180b03060f0a060e04050d23131706060a030206030a0e01020c0d0201060b07080301 86
    0x240c3d003581030446c000c1100b8200140d40d188090007c81c0c100354014180c0714100040540342110260801a00c82d071042d0041002d4400c030030f441030030760358080b0380c1035107417011200c1c2a0801d01840100079414020a2800310381140d024131200001c14040341d01c00310500d003001007a0384a41d0700707540217043d2203805084d0580702c07070050f00141000c1601030203c52500d03a82c7c00f426011104451448800a500c1c0d200400034080301c01d10410048500d000910314190640b0001307001608203200300c400b18034400025000984460344681021400901070795802d25100c031450400c48411a40400d0a6150960100b600070a10f41911700c135550282c0101207140740c80c00240c80b0038104031044410580030304403642c3c1800200b0007910780440a2050190070038100203950111b40c07078003001d48a05a0007041000700d55a103102c2010212a01510342a41d00c0d1507540003000a411400002d01207580005050712400500050003850050a60b0081115036210440d622040c82042e0018101c3e0b035003400103100c03a100d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 20295141 1250 20293891 20293909
    0x6110607110a060504050607111204090504080c010f2403033e0a050706110a120e04090b0a050703050402030a03030c02070e18010608060c0a0e0604030b131401090b0402 74
    0x1980c070100d91039425a640d507001501c408a8084826402c0078041c445c220340c0007085110030080b800042d00c074038001c5240c2811719000e91f10413440d01548a901190030300c10000c003144c03140710740400203000d01161903440402034050168002184114020481c5016604401c80380c00e42e0740c0b41d82c50900c09010080d184141c0d000c0e081c498944001401080d4481711038001032004440181406440c841f210340c1800d82c1010302581c0494140405000c0c110300410010403080f100a5201c2c6c213181c5802c800d4481240d20608240409070405d2810040030f040c005080342071071103003501c2042407001c3c1d0f442000840540300182ca000303415600201c0900002402030704600380e1219030748102c40741c45549040b098420001a9080c000b0764400b445682c144030000e00696010f040c442c002418103080400300c1514074410041040104169200c46201c16030701da0080310001d517042305410031141015003140e040300e003c010302111013240d92900d1400e014010301030741c0d90194105003012035690702d039001e015a0031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 20296391 1250 20295141 20295167
    0x12010c090b181017060105030708010506070f05060a0b0f0f0901030b0c0906070b07020115031101030f0e0304030501060815040c0504020306040e100203011a0408060c13030501020408010506010906110607 89
    0x1007000c2c20b0740c0c850394554110b5594085440e58414082031061884003800c1c803409031001e4104a010010040b0003504010000e04448060360350075138407502810001c050280c40c540082441c0030700f5041c4079041e00c10b43c00c8032400c1c42d0111008900714035441d080bc02c20106100e40150008480700c010004180415041d59026030b0340c0d14214580040000024059070041c43c00311421003020060180c07a03030b42440750011031489078554403c101e040d038803401010f0202c0040c207410036480302c1c10010383c007030035803c4101c44000741c0040729180d98480c500103002c0d017010300858401d840354111070210816400e50190080341c00144410115040c40d040c00065030005103203e400c25115151640c10f6002003291403c0d12007900801038503075052004404030303070854640c4c1003c407903010301c020b0040020104416400ca034654003981da8440350b100300f020009000c2e0344080c10a51000c200040e503641c1c103400440c81000f0076a5458074032602c910b010760b440760441203c03615580c8440001407400f40590303551200e81d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 20297641 1250 20296391 20296417
    0x305070501050705180402160210050c0f0a05060c040b070f0f0209040311062d06011403040b011d01060203090f0f061303021c02030d1b08031512010c090b 68
    0x10600944803503007034803801e48182e00010b4001590301400c042500544030300c03100448043d842c100e1040c20000c0728544c5000080c0c890318100041c10307000c80c014002ca031110b00152041d51030440300201102c0e00c1e04500b010503200c900840e0002121540540122016207503001c42d141c1c02c2441a44841c0035500d0100e40481d4000c0d0600c0c1980003503a41c0a0318a8402c620950314642422003071b4440700d0402a002d0178140320f5030b071106408400703600a00b1042c10383c910103802c1c0910595400700102c40c0d041003403460310440d80f400420300051211095080d4143d0b003c076604500161459801040196000d1081000580051200c84800e1410f0900020102c0d4020000d80000f80e94000040301c1e80d0200e81103850140c1d03016803c20441c10b0a4010840081c10358410180c3c07030015402103501d8003825000d940810651203040c1e40c01919000402844c903030401c9401d070312442c04800e01803901a1113036065105031400c203003031140c81005001d242040500b41d5213001d680c81c5080d8824949404c03a81c1e2441c10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 20298891 1250 20297641 20297647
    0x3060d11010201140a0c020d08070203040501080a0b060c0f01050f070801121106040b07060b040203010b1606020f0304080703030b0906030318030309040e060f01210311010f0c02070f0e0915040305 86
    0xc0070300c1c1501d1130f0b004070034010700041c000f802c03480040d1610344901c00030020300a4500030000f410750003001b500c0c2101c80a003054260ba43c0c8081864004202000015502220201d543c0410850000d5408500c4007808020001610340c084605045d40f011251400020031700c00041c0405a042040c0c1c5030541e00c1007a114042c08002c4000600715003041d08034540002c00444d040040c0415030140200e06081901c0440c07455040180110701c0f44220143e102d500300d103100d04541080000d0303045550080e60f600242d03840303080600d080d1046a006204c29000207051042c00c0c130a0386801030345c05000b400010000d62420700580c2988000b010003012080c0d2502091000c4c0c2040d40b190300980382003040c6840605000d141c03480c2e03219910581a000074090030031103843e00000d0000b42005c20132043d014103140030061807040120340541440c960099a0034100003418a046400107105810340300d4442500031700f44c0e102c1104185e03000c022142d00110398004c00461600540da901c40c0c90f04680a441d0641c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 20300141 1250 20298891 20298911
    0xb01110a030806030114010b0304060c05040902160c09051501030c1701030c060201050c0703050a2a120207080309090402040b0111030f040503060105041407031104050d050c1503060d11010201 84
    0x200300012000d09601050704241000306520f428450390a01044104075110154100301070381c005400000c00c01000142c1e100c1c4118143c0b03000303038156402800144400d6550300e68120190961450103001105d00d262400c001085a95050080c10322484040da40e1a00d0a242c1744011806041e031441d04405200c00e1000c10038130b0303840b00d208043c080d5006010086c049454140001e08442000b00300c81d01048080c4201710002c0d901c80304880c2d40c560a0300d000c43c88041c80032222292041e140b4001740740b6111441c5039030200034486070920240807080e025074010329a04d0071140e48a00c245040541d20034134050024005151aa000b0525100c1c185095019004032480b400c0c1b8540c0041e100f4101804041800c0105160800c0740f640074040507141030000c0c4540c544200d420a0740502644145038480c3c414000078040d00054900070140180340741c400710842c0c00d1558848950109a9001e08400b266521002c03440f142102c2c0228000b40c215803640c0600c3d2250011a001c03040000d04654851000c1a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 20301391 1250 20300141 20300143
    0x5063604020d09110306070504030312060e160801060203130b0f0403080304050322050a0e0703110d0b04050a0b060a08090a0813060806010914042007030203090a120203100b0111 78
    0x115690060b000210511542400758001e81ca601d4542d10944c040400c01c518558000240c40c01c4940c0b50901d4200d61210005440142c44583c1000f40601a004100306a49007200c4403020f180030036032a108001d0340c82d14000c9031213225a0150b1001509096010480d40103218010400104aa0074080c10b043e180c1e078907010268000d0f10107841540c404201c010070328400c1070100f1400509003400800035450500400c100402610030450214941000165024060342026240398806030000c0c2d640c540c1c4141c0c450040005485e03017402180f42900140402a55102d50789d00504010580c03414203455002c11190305500509094003405108010000544c920000d0900b00344102d00040c940c80c1041c41c014a040e0004215604100e02d015042204d06100e4a400080100954021580c0708600c03c00c0c0210445904455000b507200040e003509055010001d810920350859030346500e140d0b030790313000780c403010f200300010754590031034019404000d290b07074040d501c2d501c03060402d1000000c00c00701407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 20302641 1250 20301391 20301397
    0xf031603080405151801120b150301060f0201110405060703091206020909070201020711040c14040b0315120c04020a0e04020c07090506030102070b1605071e0c0506360402 75
    0x460765038002140c140081d2514101c1c80340660b914910306410011444102c111520720440014140f143c0da00c0c0341070350488560441401c400380078250121081c084184a1484d900912503440040c48044030f5003040c51060043d809155510240c80e4149810328042110507400f005044051204100300007541d00010f80b50105242d00030b500040c1c44002410500610070002440c880031640b0400034600080c4070130b102400d410005840014400031444170648080703041e16800c03001d2070f0300454000341c2c00c0d01e4070005511440d003240e00c581700541e003c018000300c0000e02802104035048540880d6282c100b031360180c141c042591030300e00f14840301880031030200c1e882043d503140182c00c034600070300c43d954450084503049070301540218500a5a42c40701400c50b0303400341901031511014040b24134118410401d80381c130b194010b1010800c0c4107160f07280700c400c02083d00044424802a81c0c0003e40c51400b070041d59101e261604050010412031070b203520300c90b0410314202824000c0c140f901c80c503945691000e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 20303891 1250 20302641 20302643
    0x6110c07030827012c060d0911030c01050301030b0a06030c060305060103052802090f09010e011703180103020702041401120308090c01050405060a05160309060809010509030301050f031603 83
    0xb082da2685030090801c038604101c24240d1100101d46601681030b6441180100700c0e24400d2584100c4212441400107003070725036070529610410224404c003600e80307598016046207124407000424803a030322092607241c101281c030481c003140c02480100041194000300981c4003c108000140c1f0682300d40d2414140301003604182e002276956010880196054410039800890704000444500c0e101d00a42e144030841021000a040d00481c24842c2c42e11280392903000c69134001c05040556071501110490302909208403c0880164514480f1070440407044840d05502070141c448070000000041d03010350b00070754040307030488c0d500c40c2840341c045000d50000d40640000c84000890785e5803410000d202c2d8402038103000c1507400a118141003681c000702110100d40c3c0640d4a030351150034242c400c0d6054040c0c41000a0000588511007040691106491064a80316207804406444500203d82240c0c0126414256640100010700480c6410f200103941e185004084070070b0142005254401c0da0b4503a80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 20305141 1250 20303891 20303903
    0x809010605090a1b090807050d05030702090a02131e0501030504030c0203060910060b18010e0d0803090a0201080901020c070332010b040b030d02060106050304060b090f06010e0a0305030706110c0703 87
    0x1038800d840c2c80e12048000b240300407615105010a0501206c01e88034241845100e1140e80150030300c10030041c0a10a442d00141c005140d1181844d0045c8540045d6000e280b807048542c4510030041030456031010869425020000031070b40a41c1000d0054006120142c801d90038850720310700150041e6401c22900d4814075100e80a4820002c2c9038034200c05480a5030004c030101c88042c84030100b41c190901e81076008100074644420360441810110700c010a404101901100000003007083c25071000480c0c0180b680300382c0e946010b5640d6107030007a080f80540c845049454000381020004941d542180c0f10a031b0b041c907805c22040410390104100703120a4a1076030340040c1d4540c40e60a44c2454030348101c002010b401d070050081100503040003503d0f08014001e00d0148640400030405001c040c1e44202c901c0c00c1c0142a0f0300560501d16080c0c850158100c45103800281141e82c9008103052140702d010880f03130310000030b41c1032417129690100507003c0c00d0030405400e402800102240102004144001c6001d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 20306391 1250 20305141 20305151
    0x4050703020109050a0612110705030c01020c060606030108190215120105090a050103030512090a02040609022a0a020607060b03010504080403060c02030a0509040c030609060609050306160f0809010605090a 90
    0x71002500c1c24800794002c500c01c0c80c80c0401046615004049462030812032600011881c06004000d0102d009a5601034554840814054801d002c15402458150b1119040b20555030341c000402c052031100340103222580c2c00c540e00d80c0724a07480c815150550741b031004140001400c100104c0104130341000c0301c404044401c54004001900b040350000342c0140354803500340415811a100a0807603c2024690400784d041c0500045a40500340500c4424948c0208207202c0075540b80c200502075000402080300184600c03405041442c0d10f00750f41c00480918070040d1055920343c0d000c101c06600040c00641c0d12640341c1c01e6513462690288100c910651065a2031074941d821030400350211010b10f050b010543d8000c0100c0b181054200c419607445540c11140031031004007030b2800728050595588102c200030b04100000c02c103613030005658004c0c1c0c0d00c180c04483c034550b40d032080c0c07a0704074040c0712101022558070311841c1d500a204081250348a1508000400d040c0d079640081121100c0894582a550f0365034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 20307641 1250 20306391 20306393
    0x60d060e0a020904051308090108101503020901020607020c100e010507020402030a02071b1d070210060b1905030f0f040819030207030e0103050609010e0a0f020705030a0e0d08071509080304050703 86
    0x510885e03802220800c005040c02420f42d945203201e22a2036501410300100b840003a1018160329036081c080c2080132030f0381600011110780a0302030b40001100300d01501640b400194403910010750380c0b044034001011858030660102c1c080e0740c141c1d0006003581c100081040040d02507100c600003140140c0109500603514141814080e501001c20300c2c81c0204404480401c20641c84e82039200e000000c40410038201a44813a94140c1c6001700885628071428100b8400164611402c80a0230704101000704030002c5c5011414110f03664801242c0c80689e140d03110011801c03d0000004060b0f11078403401120b8901803180c2d060b010030101c01da800d44002500001d0290030140e11182508034101c00b1300b0280040c1c20580d0028404100502403108507805140000710340d820b50703070024020b480d44c81008543c2c07018141441520307544502000e00214280b0300d903070a00317400c2014050016940141140307050060301d40e10000303140d100100a0b08265101d080b031b000410090230081d03005a1085004003c12491 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 20308891 1250 20307641 20307649
    0x8070501030b010503010803030411040902030604051507050408061303020f070b0301091112160306051809070b0301050a060f0e0405070c06050106030209030a0f0c0308120417030c040302060d060e0a0209 89
    0x1e004982c1c0c1004800c1c00101300714034000040d0380d0041d0344060b01c0c0c220700000b4070226004200d8600087d40c1480740409101c180840400c80e021000c59048003a03103d035690710410b540d0751244d03108140c81c541c400000210004100884110070034407900c10f4036003100d544c0428514241243d00300060748003000004100d8401503101c1c5175542c402d41c913542420003201d070744010a0040d0040440704a40103060049400078825444030000e0000140400b4100700c00104506100078102e60303034043d0744103914001c10710070310410507a4103d49004100c112001e052410403500307480c4241116090100c0210521302e60358607406400d10684030380e0b40d00c0c40001068102803082e5601a84a041803500c100040721300d030345011500d00041398100d09c24541040c020b140490100760b066002415200340070803154100c51140b04003d00039400b800b4803207050000d492304110280b1098500021403a000c01c001c00040c00d01501404190405c10790005040b541c4000b050701125040344c5551080e031f4001000116850 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 20310141 1250 20308891 20308901
    0x30f04060206090d03060e01140a030803011409090109050c060705030f030a09021801082e02040303030516030501120b071206150f08060d0f020d0f05010203011508060120010b0303040807050103 85
    0x1d803174140700c498074160030900482030601910180380c1140d0756034195611041041d000843d40400c54036529031352030b8014644e0449202e200c030701c11420000454400ca1050044032501c642000c0604402040d400070004140d1000d4000c5905000511a030404150480d001d544038420000b40495526145e10404c00005010405055090f0071b00300184241500051400c55040060300000e002d5130302c3c000590520a0303500e800080309800024007104166060f00114003814480700703045485000f03820240e0a58009005901410340741000d001c5c04644644200d6810409504001c50300d0003000d08000c0907a0900d400615000d0410b030381100303030540d101000d9400c1044a161030221801c0250000700a441d500da0b02405010f0143c03050419540c070700f0503038202c60394880080c660000c5c140c90514040d40007441a10b004203802c0c0305954201e80142105071182c04165243d5400c264582280701074450701203040b0581d90342c1c0340180c45064800700003c002038156000100341052400c800101560 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 20311391 1250 20310141 20310163
    0x100626010f031a090d030507050c1f0b06180904060204050d230d08040204020702010512040f02030606040c0e0d06060f0305070807051f08091f0203040212010c0f0809030f0406020609 80
    0x2c03041c40108904907201184078800180a841d0104450315012340448540c05a008001c10b01c2c010900c0007640650f10b9000c002441d0507440c401c0c011003840e081006214084d941c10b0103005051111000c0c120b11742107003126405440340f8401400d264031500400c001c00001c000c100d440101c0c1c0100c1381451024105046641e894040c01840890b102c6c040007004101c0260000340a60740105800341168000d9007510440400f40e40c0b010340c2c920f4103081a116411007000180e002e0300510010800c182402e0050101900c100e0326001e0590f803d60042c4104102d0034001600e145030b41d0300000c40d001c0f00c280840c800640c080d00c014140c1e181401e4540d800c03c48a58403c611403007010b02089075004042c88071130318a03103e60030142025a03490740250309290142c0060907911400500202c09522a94050b40c040c40c000c4d80c9400900440c50026401c0307510f19050340e4007003501d511407444014800e440c0d040c1d0002c4c506050b6420210200b0750460160048d400680c0540c000c041080a411030402051300c800d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 20312641 1250 20311391 20311433
    0x210a0501150501020d050c01090611030414030405060711030115081605030601030b130302030c011107030210140114011101050403090e0f040b0414030903070b13060305100626010f03 80
    0x1403494480085d60301c1003076550a4003800008918042c1a020a5020400b5103810503014003d000c941480301802c0e074002c68049590784440114214400030000555081e01c401520382c81c509032450701c81d10251440c0703a009a42c19034aa60075014005a40c1000100800500b00106031020462400bd15a01c80daa0842402075102c3c2c0c0042022408411001e0b4021864130491340805425080480c2140b103000081c9440c4d60811002840c4a6044802881304900a80c280e42034886040d10000c00d0326064042da8180c0590320005101241c0c6045200d085034030141080c1400c4410444074509555045800b030700480c0c81d89804120f00d210380407030320743c0c00504001d4458480c9004d59401e000d000010300082d1905d801107003a6540148200102c4400c1c1d900101204ca240e5601d020f0020305a101c1007244140b1030f003144000032418003074000c85005409440320040b65505000e811100c684100303540d150348003541251051115290604240a010302c0750700243c0d11400d500780a544044590940000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 20313891 1250 20312641 20312681
    0x2030a0e150f100e010605030103060c03021204030e04020c010501031a01080a030f0810030b091f11090d031b0506010f0b0a1706030c040e01051503010c05030109050402210a0501 78
    0x81c8281115501c2e4403084030300403120035481d5a0400c05000c1d40680150500000b04d40c00450001d0b0040080e40c100c0e44502e80900514981d0007044003a405600d1001c180950007402140c002401402607043c03900c00a0300040c200b8110019450035100282c0c0141c0d2440c551920004c1960b400c0151640540040c1c001001540d8441e13900034882c001c920070040030004c00e600410407611082c01c0e84001103801c0403228026081034051300b0349801e4600106841d2205243d02d01505d1400340c055180903c20090906007030403139800601a500c0c4070380d08118100401e002c44052500c241800050703916009a00810566041118441282400e500b080310030000601200b503029620020041010102d81600010b0303031240d10120b483d22649401c40341d8024100204042d04100542c0304500c60103961021200301c0c0c10a409160881c0d40000220700003aa040005000700100e58100170342051002e003071280807a10340b6480101c0d4451600d000402031300200810420b0003024001d0824030650803d2242c6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 20315141 1250 20313891 20313913
    0x2010c020706110106030b09060f061005040614040503010623010201200c0f030a020307030207050607020907110c0604060306030b0f010f060c03030209180103120512060103091b06020102030a0e 85
    0x259800d0140b0a240c10000c1c03d41048079258000e403c040015071340b03ca580c501e030b814002020303a281c26040b07801318041043e80380001e41e41c8c03504a00ea80c00062290301c401e4605420450202d912102c92501c1b803840316070400c400a4181c409204130b5005122019000030012000c00702481c603041c1d904c100c0b038110b82c100a20700c0f85000b00d1000c24055042c1e81d21f80c03251703a4139441c83c400d0300380b480c0164130281a000211301381000980100c024500c852180e07080c4c803180c13522442007201500500e0700107508203000400003421680aa084a1000c1c41e242d011240b4034010302001807841d910513000000000c0e21050200208885a0728a94000f00c5141a0030025070425182007100340440c803603201000900e03602d90040c0350090b8101e5000030b07000f0302250300c99000000600c2e103020b020f04c01181d1102940362201c503001e200744103885052000200410040d15200c0045000d040c000d8020b0305c030b0280c08080c03402039410300b107212001010542c002580740d1034a2281c4d642100c0401420160035000356107a01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 20316391 1250 20315141 20315143
    0x9030301050901150309020312090a050102030715050403020a05070303120c320f04090902090f04050303060d08040b03072c0603010306050403050408030d060305060709051c02060c12040801060602010c02 89
    0x1e042d40c0030030000901203841004c0440c0944825003005c0c0d0540102c1030004595034501006007286c000a03140108215134a100482c0e40f0300c27409102811190154600140300d400030303002250002d00030300c115803510200da101e041c207110290344201c000c01ca00d909080c1d88900107000d0840b042400b41044504420303442114016116034103030301c900b41e0f4803180702c01da1100e840d0303400d90f0b0400300d1400020b070711540c40d500d003403000b003403c460168491641080011601300c000003207a0b1140703901202450640d10b80f01d0034001e1036062900c0031615542d081c030020a4010084000e1031040e05c45507100300d4400501c02c04141400c0300c1c0c0124034481d1094088440c0c464a40c082260b0440f035000d600010b0994070303030408980c140599048685140000640c4c4034150720190030000039640510296146c6480d1003205130380d00c21f102d202d60354010151509919600340425054032089001070407040c90620405000303800e102000c0c2541c03100a001090510446009205a2000d0031030760000f045010760f400c0c030103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 20317641 1250 20316391 20316409
    0x5070206040f080d06090605091f0e100306020304031d01090501090317040312110d0801030b0f07020c030601090905150c090603070318060c030f050412050d06080d020c03060903030105 81
    0x2400b40c40c08044032008000d04003003143c40c0c1c1c1600701c2e41003200640f501e210368007030b050912400d03100c0c600803008214802c0d50203804030b5002540c1c20b0110380e46458060101c546040c024049042d10220f00c0b80000412201d000a6118034840e5032440300300d6000c5402c203080914003c460b41e0400c03011030418030103640c01c20906010349401a0740d0309541511500324061500c07491700001c00d0700c2002c11030002c1140d0000030185c00303030000c20192090303c4403403002106c1c82802480050724172901e80740428411f50310320714800d402156a01c15981072040100104e840c0c91002e0f4001c2621594910104052060a10012036240505e06044050341410500740030f650241c941a103200f40000800f044086000360310844003040d0151a11254401e5418241c000384104001d0340042824036000d028203954a12a80d81700701d90081c52545000305222084a0642043c90a81041c0b9541c0c040480c000d8820003e0384e240860a40c011328070044884140b60800d01c01620000701580305200520a9036115410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 20318891 1250 20317641 20317643
    0x7030b07030207050703020a03030512010b0310090b041d070f05060316030b03030c060106030510120510020318030408030304020f0108041208060d06050702070303110d0c02150415030c02060a0507020604 89
    0x143e1590050b04000b0b05201c0c0d070740e0000f0350000701c5503000410142c210700038101c42c1d2604850440b00341e030f075445d02280c4c03440708a0b841c484c1c0b500480b005200603400c95015002e8064042e20019000c2211018858010f60314103009090703a001403410401d80c001c01080364050003080e60083e0031030a005420144c559900601201410b84591030303a102903c042050310100d4800c1d004480c01035039518405402420207492003000626212000f040c0d00000c9003c41d1170302603019000302441005a08140d00a40000d0030300c080919078582c041800100400103030028059510142d5500d042510400a03012000402c590510180c1c10801011401a5100620403052410104100e680342400127030400d00f090001400c00749084140625aa800504842564866100c81001103103500050703540d0045a09000001681c40080d20014108080c2d44041c1c1d2945110007402e050700d480340422400b030061903060010381d440c0f0903403044541c1008419000020030004009908100790025110000208 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 20320141 1250 20318891 20318897
    0x609140d120f0b0108220f080705010507091d0c04090603050f010605090903031303031112090705010201270204020906040b03040c090203010f06030218040608030a110c01020309010c240209090907030b07 89
    0x84880080d00c4496015851154803050f00002400c03d49802382c2d03d5040329a05541640c42c210002d00054041c55481080e1000d031000d0300c0301e40020701001005d9040051266040f0401403000080130081d602860740a0342c800e2020f40f00f9800d880318100d0031a00c0035480588203900c1d00041c480112000720480f82c2040c4400712000c41650329080507406818500304c6902904400076040340c0d961103070380c40540940c1122080d00c2c55507030f550004901b13071450702000b086024000f0100e891603002d08113400111610140c00176060003c07180019031f507a00664040c21856400004101c100007030000c0c00b10141460349811802c0d941820703844070000005010751001d040d8009508590640c1034002d09504800c014800c0c000c0c035464840e051385a4000201e00408200a800309150912003c1001c1d0108079041c2c0c003c0d418031030501b00459020b0320b405000c3d100110610ba1001c442d01800041001d808402c1c10050780c3c84a40209100b1040c0008108450940280b00d040c030024a00c04a0540c04c07100e107103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 20321391 1250 20320141 20320171
    0x308070504050a1203020c030109030210090507030209160807020708060103020609040b090103030f0e010504150e010908060c091e0d020112020f0c0a0506010609120609140d120f0b0108 81
    0x144169081c0c400c1c1d402590f03100d51003810004003464450700c0c561105100c0d6003078500c0c185003c8141400e803000c100700100035811401c4c0062203080c15911045006000303800310b921070766894012903502e540980c0c0c0882644100c51407003031000e8004040b40d420003018802085000d10346012030780c4460303042c0402031180c540050782a0490742c035508040a40400100b56802d10b5a40b4a0040c1c0b01c160103c0d540c0c0d02041441140004943c012410f560440e4a000841303042c440181e43c048841c20141e6aa041c1804442d400204240004001140c411052904010b03555030143c2c040204e40c0f5a580304c4c10110700340f843c03204502604c500d85880d854550a0070701840c49801700b001c000c081c1c041c00c08541e0112002003400007811200103210001c041c000e0b820b451007a43c880c4400c5640c007140f800b418079031444200c60800040e040768800500300f0f0080d14541205120048160b003054071410421000691004810b505060184190b039143c0314039030010480c6010110018124520003066610006c1c184 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 20322641 1250 20321391 20321401
    0x70809070b1213080a09050a0909080304020909031606090b0c04150804030e030a051006080a05060403050a121404030801060207050136180c0906080c07020d080a2d0c0308 75
    0x803507507083d030750045620f5150450f03080010301c0d001e400d2003628130905640c000010750280920400d0050345d0010429461640c5503000d2142c50380001e401d48466200400000c50310300c2c10a561074143d00c6c46404042203507881428201240080078245102c4004100b104100c0e91050040d110700000742c504000c1d51954640c1420341c1c644d04074064172740d00760080d0581d00081100c0401c10360883d041100b03007006642e0729682c1d419510014110010003130360080f004074022a00600c094244504146492020b510002c04280309031000321580178413051407141403000b016044084603026103880d1000344a1545040d00080110054180046402007440c42d024240d050340c1c5402504160340483d0014503503034500c0007098000d041402103080b28507200c200900c061285020800f1141e20f43d88415103911030452202c1c1503401203808a900c803562403441c40000e0349000c007078203415426844d00c0e1048600390b85e00b02034000c08100e040c0c003800c00b0604485401c98200e1441c5100175058a000003082e502d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 20323747 1106 20322641 20322661
    0x1080106080706050d0b040207030c020414070801140111030307021606080603150a0221090106060306180c0504090501030f0201031a2b080c0105070809070b12 70
    0x1180d000c10040c4d11a6016004400b40800001601325800c0000f9049034020079003140444c0b0390b441c442e020740c6041d100f480c20080c043d88100ca2285050f01c4024007240d414000c0b207030207450415421006910411070004003140860890b0358905205801943c0c2e0107054080008004155074003080e940d03c0b4950130350140c42d000d4000d00708080701c40a403c4a0b10350041100c06856800d112200400300825001601e00301004403079002400c0c028000c030b0a560940d007140c1e00341400d000c1c080010600c640c4034422000c3c208900003901c5804914111560302c113940c890351003641004c0001c028854148029040b20b40b007600e04200390342280303240703078040204018205d80c040009042c2080b89003d4040c4c40742d580000e20400012042196202001030308480f000c000141e64407401c00591070741000c081038001d20810000c0c03244525200c0340c42003501c20090f9070240c1d40030b0380c0089030010b01c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 20143891 20323747 := by
  have h0 := BRFrame.cov_init 20143891
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20143891 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 20143891 ≤ n) (h2 : n < 20323747) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
