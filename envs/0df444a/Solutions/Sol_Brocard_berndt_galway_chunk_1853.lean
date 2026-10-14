-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1853
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:54:37.344987+00:00
-- url     : https://prove2.me/submissions/1fc4fea0-972a-4a59-8420-a9b905815782

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 333093525 ≤ n < 333273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 333094775 1250 333093525 333093557
    0x50412020609060421060606050a02060a1802040e0c040b0d03020c01080a021b01090b090304030b010b070221030a090f0302030312102c1f120503091509090c0a 70
    0x2d00004900b03070700305105000000303054485513241005500c02c801e00d50070302c074854144002a10b03056017002050040801101c00060f900080c1c40340e0207680700000041141500d94502d1580c07100c403070040c0d441818107440e580d02d003002013441108854111800c12005c02071805010951408a0740940542c01c8800600659409030072041c0e4880d84c4040014540b03101f0a0b0045010303100143c11202c540c0d0f40d01c5081042000d644880e54018400300c00a504041ca90f036103042d1080c030140a48802a40042100c0c011900c42508001c45140212884400350310207100c0180c8d00e401c0341031810002003007480c00064602d8030061040a0340d402601441c500404030503038460744c03540a41800c18010405100140900d45283c55000318007050860155000d191240c4810280015001d070124100207a211a5440d0f035030080380c01110140c41180e00e08079003a0a12034194040d40f118030360002942c40d40403038400850b50041010500480f01d01e0416100e055400d40280245000000403c1020b96445a40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 333096025 1250 333094775 333094777
    0x50108070c03030203150a122006090d0602090414040b130c0e06010903080d060608010e0f011205030903070f030b15010f0c08040503070b03100918080c0f06091605010504120206 78
    0x241d045855100d0801d03104000c1482040141c0c070a9003901c22088d004810045640908445d400300d0110140111546100041561041c8220140f00d0540c1844400412a00f07806a030703000c020062042005544150072a0f1244004950441c0c0c0d200c4110009015801e1680f04040c7c0190014414174811741040440c0c021403001401c10b60520103a2580000091300b2400105401c00e41604042031042c6080c00152640c20103030400d03c816014541000a46000c0710109411200941202010400d13181009030031441404019034044c09a40301c040785d000507030703070f03409003120300c034a6121601d641c59001c0700c0400b01054070954001584a6404a100c501c030740a260a01401a441c1d00c1c134165807440001d2a00e9000c0d4003800510300701208018840002c44890401082401403e0201240205031400001e01d1007a00811124000c04c042200000401482d68007191000c202c80d03560038001e01d460760710109a019000300300109200441c3c15407148050300d0480d000c5e4800e42d18200300d01c0e400c10482d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 333097275 1250 333096025 333096031
    0x2107050c03090409110a0305030a030608030c1203130b0405010501051005090102060718080102030f060301060b03010f0303050d063c05091b16080c0c06091e1f08060406050108070c03030203 83
    0x4051005c080c0350900d03594003a0755001140b054004655403c800e13100907007038402650050045410030301001c05200030201d0317100329518102d07140b00c2c1d496480582c1c00400c0440900044c0405044d0b83c2008204001580082d060380c4d011030f49e0410f041d240c000700310b600f803140c145400d005801280c0030a4081d80a41581c00c02c0032654107403103030030b103880705a580d0072600b0844001543c0e2003d40c0c00e01c2610304013881584c010f40502c104681c61903051aa40c1c40d9011058031006040000003d180c0c3e042c041558094405024246d000d51208072044c22541d0400f00d0640c2181d00790248260030041c00c0b45001b10800c00c4a2020706165039558030807040e034201200f0010f00003010b000800608011024903558034003014401e100c01c584030780d8040c0480d49494010501c081c001d140800c00840d40c2d13a6403203114452251450f60302107200031414082894074100d0010400d0904d425191040c81b00e8110100d603118410541e4108440c0e43e031440111001501039400c3c0010449509094020074826001558 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 333098525 1250 333097275 333097283
    0x50d0c0203120a0c0c050306040b0c1e1206010306080105190f0207170d15060c0609030306050405150405100b090111010905070905011d0606040501232107050c03090409 74
    0x20503002051001540307503010741d405400140b00c1208520800c440303000300c03d01402050b8010049460b1640c0e450703000ac00f010b4680031a421022840882c0c0c4903000343c2c42000c0042c41d40388a5195801c9070020081d1460903203046001c44e081450100b4440c03014407469104ac50425504c101d14080c011003a402403103030441c10ba0042d5001c00c540c1000c0740d03c900d4005070600034a0401c030313512603040110700c0c1241e0100c0d03d6428400a10402000007541c81101811401e401403070000e600701807441c00780c00038007150b4480e64206080a082100508128403032002500302940c0c2400781303039508400d0314060034040c050bc41c128072040c040301046502c0b03035030030340c4c141405c5c03900006030070310b49440725854030105920201885440b0741c01130120203900314074040f4080030140011311508201d00003c034135003c0c2c0d0054904210305078402c1811b0100746040b10065500e0380030f40583d0b8842d00090010302300204050602190103060118a00078821000c0360b251400440c091400c2091420412028101c150410381e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 333099775 1250 333098525 333098533
    0x151116060e0a05120304051c0f0b0c0d110a0314010509040308040f060f0506040b0409210201021e1b1906050403170f0105030618060103060203061f0f020712050d0c0203 74
    0x1c19261200c01c1e40003800840c084c020b648807071a010400041d02d0010348015810350280300c440b0005000080c000c0721442e40469000700c0740d550b910a07550705020b0f140f6110285810108001150440d40005240c4d4080c0c55500b4001c42203101c1d4056240d04081c41095009035a81c000075010070300c214100d036046407064040c4000f070096070300d0708400d50708170701c00701c2070303016a9041406403e140c10322800744d001e0000d030360620005030681c47d03002c001c42d400e407010045d445840d08046041031007036048840d00440118510f04041111601031800e4001d00544c44606500c24400c016441c070014440c3e024055004100641d10300c02d40d101c0d000380002400890901038401c408501056482d2a054071442503082c0b0750030158035003010945441030141000081c045040741021b102d420100b011410f4a40051000d650707602c0d080c0c0811211003c00c0d4110040d40600b0b0307558240740e03a00c12181c401c0c00e2026801c450180e5107a1503081001060300784024030f40c1c1e01102c440b4003014000c5020410040c0002e0541d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 333101025 1250 333099775 333099779
    0x170f070e060d0b090304050a051c020904020f04180b0109061a0c160e09060705180d11030a080a1403101502161202030f0a0201090e1f151116060e0a 65
    0x1c3c050020b001d40d4071a066030804181440b0900b040604c00e0010301c2c007192141003d8041401c06101e94003a00e20103030164149000103401e6455a8040c1c0e0361013a406401002400000d100441c40d14170140022210300030514000605480f03240969801e980d440300b00c94400c00c007050042c00f406d500804200140703000344414412050305421100e4000d00c0c0c590261507184c64506841401c101c0d004248101f800b00034800c1e2041c0c0740b00301071507624803101aa542c0c0300d90709050402c0117455002c5140c1030b5145c0702d001068801c01c681d1034058130704103003140c50700b0800108544561320140402c81d0500d01884404c84100001645604048101c60a6006403412010149099068040709422030005e454940c1424402c508003002421010100c01003c2d02188500d0350001380078240c0e07032060180c0301207418046185d804108050b40d20b80000e450342441c02075030751007030036802022444000012415841100e00304030004030705029007030070f1101030300442801c00c0c42c1a01c009041501c5d454108042041c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 333102275 1250 333101025 333101033
    0xd0908040609150c240b040c021507020c090f04081b030c0d03050f01260109051e030c1e070b070506040b071103090418050d0801170f070e060d 63
    0x40000d88a42e6650301002030406040c070072100000e1010b041042684400440482e1040704c20140245c07020440c4020058680c143d40c0250689032a41580306240031070300c904858001801402248060214001a540786e80c420f0782c48150800702a904950042c0c0080d000c00d00040c20305603c14420030740141043d0140c01d8108015420410040c415400050f510030110380c1000032090400f03442c501880507140c584400d04240006106800481104210141c282601d81e44044600c0000740300030011242030742051940d602e0031101080b40005403081d20055840c021084030806e0103d90300601244c03008010241400c66807495016039070081380c00108200184070000c004041c0544002c11a508160a0441580401800c00014401030090511900a0200540b0070842e403c40300042d40d0700c10b04403485079068140c0340003000b500840c05400852500200094180c503400f010641e4041070800615594845001850030503510421040042038021004240c0c0b1900140c02c8454851a55903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 333103525 1250 333102275 333102277
    0x3020c150708010b1c0e07080a0b0a180506060f190b07120302031017010204050d0b04031d24160507140406050a0e1b030109021e0403170d0908 63
    0x1000c1916400351040c407402540c0410041c0c05407070300c0640c5030300e0641e002c40d4001144499440c08480e04d6107985007250300d0782d41031051800030641c0b00242d4002040e18079210202d840704541c00b6614603d000c01c0754181d84014035030009615406002071185407031f010100b0210000031101d590b4006c6001c981507280303c42d06480c3c1310040010800454680710949400c86c414440e0300c80e40c008040c4180100000010041700350f404484d00849004a940f150013000c40c0a4131540c0c1240382c22490300411541004402c2c11028403490080d9600355210113900300c09200380303504c074208a1b80300708205450b60600d90000c4110004a860092442c40d0800b51240ba041c05202000c041d60103030081e46040110307284201c2c1c00740d116a0100d0f010041c0a0900000031007001e814001d0304401030b6441300040c06900c654050002e44442203d0403030b12507a503100000040e610801040170071514040c0001909081d40082e10282c9a1104816080700c0101041620b0b580101822102c010385071950000410000c070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 333104775 1250 333103525 333103543
    0x41b0504230105100804020d0314160302061b03060f030705130e1c202a0f060f070f0f12030c11030a090504150b040b040608060316030209040303020c 66
    0x101c0039901001501c60494089401680194041c410010110380181d5000341e200e03510650413181d288483e030840c10225540b0b42e0600385403a101000140961030710078108a0050a0362080d401c4900f55a02d160301f40c0d0301d9071101c2202c000071003000c9c0045842441d160707055a5420324041d0450b003100390f1364000900b90118441d48000714558933100c5260341d150a00051040001100d0388201d1a01c654000030705100d00b00c1c03079040d030f4051122425405c10f401400594905c000c4180e0045c1c402c030b020303030a000c452501a40c0252151400c405146502c3c10040d080c2c50301c0107881401141002c0060710384c3c03100d00d80b1b071410880c8c180300c03180c40c03200c0000c80d0701c22000d440024507a03000a00c1ca8604501900690043c180d140300c40d802448807040559014030701c07a060f200241c0c0c000c5151000420b40300fa40c9034031034100e002192004103022030300b01c010201070070840700c0d02eaa0716480da0311100281078a401c51170141c011180c0e6449001c0c0301500781040c1440d003041c030901d00107192010140590307042003045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 333106025 1250 333104775 333104801
    0xe0312010801140705071e020607050f0d020109050a0b0a11070501090210080603250504020a031b091a03040309091407021b030d12020d060b070c0602060609041b0504 73
    0x104014454032109100d0f14000c0d400d44901009a424446005840ca0049040040c84c40d510215004412914080d1907808294050f203d20f80301d48040c5009a1111b0150740c4041b030600c1101032004201d881401000341c082e070014080d1900c180c403511071505005004011386401900d982a42608118840040ca00c1901420001426404907c100450002a04060350411a10780d0602c2103690700440c40505002d80c2c11998850182e15040704001e014280d400158018800b003503913013625030150481c40102511151003008800000f8094416100e94003c00c0d03030400c01c5102c01440c0740c1c4003100071900140a8145815610f68900d28103003520110345800b12811205030510400c41d40400c00c6080b40e60426020354203401098000c02c0e695180321100c5000c2020b0004680385030b080d40d0741280d809818205c0d06100103500c41071440322030b50007a9011145d4083d80e00c00000c4040c0b0104840e402883c008040d400c0755142c64694440c1a60148206081c40d480d174400001d0300e554900c524000042c070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 333107275 1250 333106025 333106057
    0x12a030506010207140402090d0203061f08070b1e1606140709080c0103021b0706020114070201140a23010303180801020c0303010504020f07050d020303160e1003020d0e03 75
    0x1041401026180040e10003810356102202c00d101c011010085140580c0c415a001a120030390180018903265040c2c101a415002d124240180c410381c81700c0c080071506210321058030b46617031041c1d074580e03403c1281700d00c554a0f00244030308001d00d141889150071000e5500d81e00c0741003c05940b041e0b540192244070444580e43c3e180c60854800e113807900019848884e604085c0200707454900ca190315040311000441c105a40043d22240182c1848012202d504c15a011140d2007600c50070064024100d5440c0501c189501f1000610b003207205025003c0c40482d261034031100c2d070715820100300c040c3c41110503120b0030502200010a02502075000703c1d00940c0a965a25500c80411404455201c0660400f40795640100040c0c000c81600008890443e40203030760040c0c1c1d4415500c05040503020b8041c0050150140c8401c001d4500d034008061401107851100c01c02d420240442c09880030180941081c3d08140551040610300d4083c0c1d000d0b05800e049540e01007800491461000d0840e4044000100c203110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 333108525 1250 333107275 333107351
    0xd060b042105150108070303080106080907090b010c1406010905181510080d0f0909151e0b04090b01120204050d1101050418050108010e1513060b04020d09050607021c030e01 76
    0xa40274082d00c2c010201e60400c42000d08001e02e147c0d840313a645018462482d0b481791403080d02644036000c1920030903001300c1030191284080d104036031600d60038403540c40c0850034000403884005080610640020034400102a481e03469203008212803001807034500a10801000024901c1092200100c4200b142d1349c1e86002e15180358010300659001e030400c07121540380c80f5000e00003107075812207001070303407598a10400d00032843e0303c00c461107440b030742c10403030000300702150028141c82d00e030f000900020001d8980409503a1440415000c90280b44a00d0b80d1100300d02e9600317800f1a0405070119100c0301d041c5801d52a107500c0d810000c9407010100c1076021426690001000700300028071480c5100e4114401a0034080107070201ca100201000d402651110b0780340003007004000c03550340f04c00030400c4042d00c1035444103054041e140c000c00d6600000d503858016180004c400a20200301c211b030890150000340c440301c3e54440120024200f0040c200703d559601c217446050780210a9081d45121810003070040445 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 333109775 1250 333108525 333108527
    0x506012f24090706020712080906070c030302060115030213350d0210050106020d0f03090510020d0515010918140907030203100204050906060d0b0d080d060b042105150108070303 78
    0x194944c80f420071500010001d000d0340f609204020f00d0700d80c00040407503c810065000a90718072030000020a55110340300000100740c3c0100c2c1913030407500c01c91006a00407840d9041a0140d00c21440001c0700e003901400148801140d4601c4070840c420914021889076440200c0d51402d4001241015050ba00103900306031060360400002c004600b01c140c0030b0181394034103040a5915074411410405201411205c20749092003603016000b199081b5088405140c1c2d040b580300003d40c08241100c80140c02d1a00140d040038620071592400d01d0103030b580d0300000d894003850780b0b00e403400105103420381510f4040c0030b01c8290000c00641e00500e0b403800604092032031032040502d02441d08540304e042c00d0040c0300070400b40d0f46080605030b20a0381a281c49603503120310760040c402842d510241950003200c0d00c0d860b0040c4003203a0f0140c000318503600020402181c4861007802c00d03005034410072070803c0c440e05141c03501207082c0d42c480f03090510650440300002c50b40352003c0c1107036500760401141d643c0a81c1081081c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 333111025 1250 333109775 333109783
    0x70602070b04060b040f11180114040e07091e1419030c0905160e01080705070819030b0402040f0308160c061707030509190507090c0c02040506012f2409 67
    0x780c00181b81004904160b2128000600500b000c140c042c25015080b0469a400f07103041c40714801400c086503903111f0b01c4500c10003158100303607400000203402c1075004c034006c40e0503005401e1012152519032641890500e4020800300c00c3d11003103810601036416416103951b0104e014015521400d0302128032030401401a0032900700501002070000b40c0c41c9040d8801d40c1007404046080401e00e07183c42c550b507603414141c030b5a02c01c001004204202c00070300d00f540718019000c0c1c80031040081d58240070381002c0e01c003003205901481c01550403400c4110350400024070300c00c0061a203094040c40c00b4a42c04400d0b151a500d000803030f400f000200b00041000040070800d50101d540c041c4040c1810402810041e8449644401090400c0c0c01c0b0083d0b64000024810204039000041c41040c206000c00d82004400a102c400c02180c101d0049042002040c42503008281c008141134000c4441066078406d403140302030803002489840014001e00c4820070a64200d111625001c0e8404440490340e400d220b1056842c2c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 333112275 1250 333111025 333111041
    0x53411030c1f080601030216120e0907051b0c0a0608100510080103030c05010e060709090e15060d03030204030c0311090a140c0705010b0a080a0b151302070602070b04060b04 76
    0x3040c001840d5090980c0c034000e0000b0690900343c50100480c2c0d4407000180d000b8401d0fa02040f202000488803a41003002a10300c3c102c9040c5560b84980752020b100b003d0003500c101c1500e00c07030003046046c0107002c44c4034010260703601c11090780300490709036540c1382010a41003451074001d44000313031002c0c04002c400310440d0041d8008180940d003c84031003a009000902a2406000c014100102c4400c0601031203402d4103c1e2000c0d01007042a90406e003000100a08052107038131512540d2030515144c2510703080301064944400f200d0b1403654203540e580808001c07042840362000c4050590900020002c030f000c5200200c06103114a5500c441c0d045154100142e8400003040c4581d141e08010200030450310b00026280c11000c0d039492143c0791840c80ca00703603000d0000303102140e4100c03141d601c0009210a00246540105020340c0c2020411b88800700d80b005102e280040c3d09411071042002e21140040c10750043c1455400b400c00142002c0b1035581c0d0800c010b906840655860b0b464500650692616200c1c1201e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 333113525 1250 333112275 333112279
    0x180816110d030324080d050307050c0d08011d160c021201060b03010f0b0a120b1305041b0e010b03010b0a110d0c050c0103061802070812040807060b06030403053411030c 74
    0x40e0782440c00309102c0c0d54501141b42942000404404940070b47d0107032007500c00c104118010b591140d200341c0d10041006009204501501040258080c0f40071a0b1014840c095108180c10000c5145440b009980a0040c02001c07038121010300c9952804030f4084c455100507280c01d82c0010b9883d4076100c03901a00010315001071407042400c00190f080203130042c0d484942603211850108840201e01c0008203107009501d84201c80a050208201c200041c03519051551a01c0001c401c102a0301e034040500e40c28001d002c0c0306400d00041005109645004024142541c014a01800b030711030070f42c21141c1032000342e1909001180c03a10f0380d000d00304001804819076101082c079042040760b1900103a0301a408004080c142e0042d80085e0407000c2c4400d072030456060280d071015040540c14103291007044d5510460040d10352500d82031040710146052000c880c001c54150303580030300302340d014210002c00c0d042404212012200f002000018002102048481c240c06070312821918803064041c182003030a1592128 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 333114775 1250 333113525 333113591
    0x3023c070f032c04090602040b07060f140601050403140c0a03150c020d200a08030403080108010f06051e031f0c0207080109030c080319050c0d180816110d0303 70
    0x7400c0380441044109003d001158085004281414403500034490ba8001091880c8006191030500006400400040100c0c40d0100250380280000450148060300c52a00150040000700040703400070500403088118002075440e108201ca001400b44116a4401c54083d46510010340c822400340c40740101d2840540082c0c04019956000188440441c0302c40360402c42200c60313030f06c0c603484c0204603541056510201840d07807401d040c14090590035007403041420035800d240c4051140c1510b8000c40c0704480c40500840c5031885090030f01c1c04088813601c07540e07070580b01d18020002c81c1d9000358034100e021410700c100001d044203d6034009007080065000524a40c0c1400c051000007940001190f5205404c00b81d890340f40d81324040302440c51810003089400e440e003080240098009014010005499040340812880c4103989903000181681c49003d00292414402040c0b0516140c0040e08080e126001c0c1c0030321450340c58000380030b8440920090b0000303a039030920781d0340001c0e042d800c8210300001000c0709 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 333116025 1250 333114775 333114827
    0x30f0201030c030b1018031703061201110a03020708090d081c090b0c1e0a031d0d0801090b0f0415030b0601020a0503030a1a1215010603023c070f03 65
    0x2280c04a89051000020840006d8068004240c403003a060042d581c4071040707008540340b024041803140c00649885124206000040010303180510503210188600030642e800c00c000132005034002d412074807041c1d41c3c2450400071144107a0f11200d0300c00059104101c007a4a80d0600307940aa8200064081074414915009401f000300f00740c140201d03070022001000564400300c1c00100b1481034039088000ca02c0d800080346405c01c8507059080749075075964001076042180d400c03220b09950303080544045008150231000500a102440d003040080b508007806d80c1c1c0301040c1c80310203d011640d07000310344604105a42407d00c00c02c03401c08034054021340709100a0818204517100c1e0343d280c0c4009811130000384c0c2d0301c1803f00710700804404e030328041100003013035000048442c1c1803864a1301500e5030b94920914610001050007030180c800d4031410116208080421084000b1180242880c211070440d42e14400c000403030b5501d88000200061361240d2180000300a00d46406040300b0703001d00c4802d0000f00310300d0303403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 333117275 1250 333116025 333116029
    0x6041401022a0109140a290403110111161b06050f181003140106110c0103090c0902040f060809121602010908010606110c061206101701030f0201030c030b 68
    0x101d500318015140c0800514520b500b1518010500070780001c1c8007455480a0142d000808a655165140101e020600305003020900c12580b40014900a18008030a40810003007841400813078241c4201100010341e03210025280c402507040040510741400c2e601888908202300070f1143c0c2c00241e030000d0039038035460074080060003074019802d1001c10640081401c4524105454240400302006012302c4009401c40500a02402d0789031a00c104031105000000707503042c803500d61202e0540b5004050b144a140b0640114082c0c1401c62041d14054940030b030225101c3c80c01e10040c00200b55249101c44031030310705600500042e00c01004880c0c140c102050038918071124404075140d051600e122440221000d00c0140c803280c0d115081000250b107046c50114101d904008101040c0810b44126242944044100001c03441480c0c0c03041c5140c2c00d44400b082c09800c2c070045d6244082c2c2d0500303040030240e03904081d0320400c04e0240d0007035070041d8201300c0700c00c29543c05100700e4004034090324040c861020f80c840 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 333118525 1250 333117275 333117307
    0xb09031501060503042d060903170c16081317070b0906043303020a0e1c0305091c05030442050903010207050109120c0c0b180904050604140102 63
    0x40007408080e140303080c86606c00e8406030500c00d5102d0202c0180480c440c00e01300000204424401200410340000c0982140d1540d544980d20a0043c516814500b0b0320b80c1c1c0c00c5000180c09004100c50b0464180140300020035160100d0000d4250490400034500603042d103145880310960089114440400410f01180c4074441101e00b45c0796540c0a00b0340001500b4024600ca000045e124045025403810190811380d15070014100b41e14a40e81302c80301d01c0c8402e01046844c0c81d6415009254a0300c06211800090092028001c0c14100406003103095503c006d420180e51b034405002c5900d60000541440348074100040a1078038040343d10041040c9a1000c0741840050502c042c0034408012039514a41031489001141c20b280720180081d0b44841407480d05074060f0859980c201c1d005900041800303142441071100300a91a0401410682c0c13500d050345800c07250740034500c903d010359100e0606401603220f400145008a10401c002e041078a0582004070750900b4040d0300c440f05900410034440c023568081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 333119775 1250 333118525 333118531
    0x161b030c14041b02030426060f01031202241005150c0607030b1c0606050604080705120f030412020a0306060602030d0606140d0b0d020301050907080d03060317030a090c0b09031501060503 82
    0x861f10007100c2e401c1c0c03c00203441c00040b6003900c03414840c00d800c02001744e2046044904a0b07100703007000341424812503402d0b42c5070700c1d02e03d40d01d00c266400240c81202005031075032041e801c024110f40d9110b00940302c1c000319a00d01c4101901e810003040028004242c3d000c10020150b001070145410042000c110300000e0303003800085120b44180c4c22450680c814045035501c010001c000040015507030b0780d52070b0000c98852005110f4075128409040c0c08049004000c90714800c0c4034214005185040d0519182c0d10744440544401d0b604003d00001c04400580580300300306c00350a0540055848152030001030064030701580040c1c003080004190000800146800d9401010308000040b0b0301c424400049110502d969002960543c281300c01c1c0502c200011030b00f182594103030015201442d03803003901034082c0c4059203c003e1181003d050040043d42006001d5070300203000d00b03408070309500e25881d80319014032150080d44042100140d100003e103001c00c00e0008107011405403400d19071400c000034004d40402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 333121025 1250 333119775 333119789
    0x60601170112050c09090705010e060a090e100b0708030919170d0f14090706030b030a020603040201022a100c05100c02030c01020d050f0a02161b030c14041b020304 72
    0x2c040da100030810706000c0d911084001414510180c504000307030702d40e601c049125060120751482c1c1000c0e0207040c01421a41c2c281c000352114901280341c0540104040d070010322104681000d11000b1079035034446030040078028010034905490342803000c452400c10301078914641c15000c648440351b00241924140e02c010440440d0081e40701d0b640720313613240c01400c6404554190709261071800c00c1c4003441441290301810714035003255aa00d4a440c070940c2218071114410351b0660000c1200d000601d00507004550007071061041c1d50714029501c9000515103040300c6000d00c108010080d00342981080303084102c104505140207200c6000316210180c64a0400903424241600e8281000d0010300810032a840790440c080215514a80542d0100c0280f80503074035070b030410f0304010108040c45002e0082d2039121241801890004c3c030a0b90721221000c0642c4089088009810740000125404c03c60910040500c1200343308001501001c000c211030280345000c105200244030400b00310f600009503416076002e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 333122275 1250 333121025 333121049
    0xd0f1407021b01120e0303100311120703110f060d050403030e0c09040605100312030615050a0512041e0302061506040f06050306060712020c0102120a050d090204020d020a02030c0606011701 83
    0x4100b40201904450340f445c00b091000206201100014615a50440b0700512500310301b1004107040204003244070381c00da0b045910114041c0003143c4050128019210300820313a1821212074008241c03d50440000044d080365a882040145034044c06107a084400c0c13100a001134400040010780403003070250010748903030f41d02d0000402e20100551450b0140d5000f18442e0101403402c81c0003006404603028080007059480c0701a1a224000c400741c4050b00415150350303040000d403062900c010307640208103682d5030712410315109424102c2a03110300c030706009a01428061824101120b00c502203148d403d401004c4c04c0004105100d800901042514128035100782e407903e03030174002400f5002e4260041e103001009a80711000c10380010b0010508038081e0240c03000028188110051800f403034948001050040004640000302d590190141c244010001801c01400c2840202240c2080c08034401580c80024010b4190004120030f030b42c0b1007403d10305140b03d5106582c03da42250b2041c0300305800000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 333123525 1250 333122275 333122297
    0xf0f091103101518090605090a0501061208030103080d0605061606290111150f060f0a03031b05070e04110a080307030203071112161701060e01030f0302030d0f1407021b01 75
    0x60917820001c2c016030480c40900007420030040544d25080d281780102c40a42c0303401c4000603070390001088207004d01d810402181c11607103940c48001040e0300c0400401c4641d59620360115031a034420002c1c0c55051440c0100030503071559407a240045138030184a01d0300d91081540c02645200c0c0010142220040a190021074605003102d22440c2240070350300d24040740d8000d41003002c1d90001d4001c00b4032440e000c880a482c0900844240481c55481e400f000d00000c81c10040760901d140110b0002e04224852003ca40600343d4034845c1c040c60010903038044540400000b424595403400900460241003044041c525016a41c0c0d07003e90380c2d00c98100000d00390024016407005640e9840d605148001c03540041e40c02d10070340c0000300d507108030072800707a042c0312542842c0d40e200d17186051245000303803010949504038603405c6482d22014100c512100b101103210410000b41c81c0c003018001d801122044480106015004407255184154010211741c1150701c5200b1401c0980d119280040b41c4082c00e003050b503e611 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 333124775 1250 333123525 333123569
    0x4121101021e0309040b04050f1f030609080307080c0a0206130c1503050612030903070b0c030c030d02041d0708150a09020f031f06020d030f0f0911031015 68
    0x850080c01c1121010b0404466841506000c0000c1c03a20100458042203020400d404100440d4000c0e02d000d441c50710280001401d032001410b14540c8000d01c0c0d94415049a603a0780d4450584800c400304031130720507001c000c2c04081c0c0d800ca04104e403c083d4081a950600d04903c1340256241c900602a403201d0510103042c4040c000380c2e25002004c0e00e02448000ca9002d10784030054090001905d106006800b41d545140d40e900d400b2003a0b52800c3c2001b0083c045e11803501180002030b411686d2051814002040404480103003000180401078007000c0160300c980c070340140b040d07030b0b2408100100b000781030400c10040138a601c0300105902598106203c248040030b240071030099107598200c064040c0c8009482c40810010320003443c0300e90807817455901e0300c0c10305811001e40071840b80303d40c5c0b01503407060400c402c50900940105951032481840042c51011184000090703450440064070818004c01560b20385040500500400240c4564140100384858900f1480b0200b1403103924001c40d0401d82c02c299603 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 333126025 1250 333124775 333124783
    0x3020916090314060723091201020f16050c01080c040b0a0e1c111f050c190b0105091008071a0405030607091d07120504060e10020315060412110102 65
    0x2854010031040d083d607a1580b540d96441e07000f66901d10106817441051015810451080f40080181c541c0c4c0f01d050860245c144604002416040b100e295000c0c8006034424182c0c901800428504502001001c01107081203402c101000410a0402400004110902c0f6020003210b046031422a0710960b80da841c0300c0c044403c00215a66947d00100c0222002c1a5040303c0e0191070b0854081c00c1c1140000304905c0421440d41181005010402071400081c0310003801503000c1c02d480300201c002e403042d007403004002c0008244a10800c440c03510030440180084d0616000030703070348540c01c28502c079001c9040c040a40e87d1003000e485403070550f0a0300e0005942c219404020744004040240846400d41000c000240c03120459000d140a00c0649049100d0f2060081d28012b0003a81e031a140c00c1901a140304011015041c024070030fa07082510384040720411801003007101002c1e41650300c01616800c00c032100903901568645031900c150028002031124140000801b1b40495000c1400001091035070010703810 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 333127275 1250 333126025 333126029
    0x4050303012d03060209030d020115140a15020d08060402120606030705070b0f070e0904080306090a090206192c04050403021f020702040b0a062f120c0607090302091609 74
    0x440c001c2c90020030400303650054007030072100300e080c1d0303492a00c5148101e017220141011100c0d968409031080010403440080c025458401500162046458003010280070074480180c400503400208a882e58561203d90607401910884065182000c200c04030041014090310b010700c00c03000080440c184a000c0c00454007140c3d80000d01050a10307200f03a074012290000c03241c5002240c41014410380f24034221034058411070f84001c0c41402e50301e07017505100c15040000c0c10544104e58885640303000da560303240580840c08070120011102d2130051070081c540b01c15106d040c0225007070103001c910b0482c400045881403020560700002c007a0341e45d040492400911f1b00000302164910b01021003401e00c660000c207001030080e2410f000445040e800e000c0010044c0c41888001225a00360082c1c24050294504000112a0786040b60707141c00c84000b41480c0180f07881c00e44031500001d00f009002c9061000c990710015505010f0507075495a000f044801c140148100d04c881046907000071980c4c082c01007000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 333128525 1250 333127275 333127349
    0x105010626190c0809100203100b0304030507080403050c040f0e0d030e160e0f09060c180307030c0b0d0e1207031107120303020c0c030d05040b07030905040509070509010b030405030301 81
    0x225000c43d4001611a40060381c041c40701d8059980a00b0229201d03000302d9000d00003040c810b040c40e0b8070b029214102030300054421001c0142c1040100e011417060006040618080e5001d4408014500200400c0314402d1241c201000d003044036a600c07100020504a0442806040205603100c00f05240717810003404100b03002c6042e0003020081180382c0c510304131300d115a8130010081c446031510000540d23034200850784600445000c01810001d04580b0501061524001d01264202604c0340d0303410134000c0c8075811080c22283c001c2000c0e80c6450a501501c22180564405008032004102d41400280306114000c1c051040c41101c1c9080785004202e968002c00801c20505085051864010f0285d0b00080d414401480b500411a986140c0410084a8240607455052030540342c814160b0300354000240540c01e010320300c43c00283c152240d02411f441441118060090b50741401c0c100644514181c000c1116082e050003000001100041101d048d1661b02180784c0d41d0001b00110411900742c00e101c209 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 333129775 1250 333128525 333128531
    0xc040213030c121e05061b12090609010c050319051e04031d0906010f0f1b050d030e16030609110310060501020706020c010203121b0f0903010501062619 67
    0x207443c6000d0903a4106651207a03020503200d405443c078100d074043d6009009001c9030403030700100f00214004e01940f0418080c148945040c03008045071032800d500200c4001c8000d412040401051010a100300b1000202d00c0c200181035082c03248240d0301c0d0b041210910380b09942c0e9440400c224030000f000d120340b42008000581c0503071a10f45002002241400c529040440c802440012149031034460103200d60010782d02c092214929050803203103420003104400c01d07c20402c5000c40000504c09024592034060001442c423951901e100808070345500401e05000c3d00400104129041002d90150440781c000d81c02280108017400e00c0a1208a5026000d07418030440c1035100848046821013022600300f40c00b624441903071000d0903611510701000c0540182c004215160304040c006c50500e030054258900c40c10707119828107102c80341b644503440583d120300000c030303080200d80303024003405002d80081e1516040a1101103000001c8248a080d8282c0842c2c041700060030070110b40c181c0c4621850601c1080c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 333131025 1250 333129775 333129779
    0x1305070302130b0a090203010501050a120b03011a0a151409030c1c06050703020408030d0f481403041a180709020f0a1404032019080c040213030c 64
    0x520020503056010360b004441e00c01c80045c0914861081d03a04940341a141d0915241802c80100c1e03520241a104c48100c1d1703918403240c00c05031424071403016140c030f80c6101c0c02620354000080028a001c20390017040e21480e001104081c05601ca01d010b082d0b02c036020103154a88082c80700082c202800c00d114150800003402c1c103e500038002402c40e1921601440c4104515150791200b10168130031400313a8041a8400c000030b074440c0c69203920800600da82801c2c000b6101d032201d0356001c214540c045250a04011584031001c0d00103c2a0925204040c02580700c0009400c2a502510681051407980214040440050b0070f100c0300480c11000e64000c01d038016003a1a000c05900e0700009042d05012103403291241c0030a0342c4019100315070b400303c1814041410000003032821501c601010204030703400380e01404000000b0744103100030300f60200002c0400b409005020140958002d4280d100c02d009211900304010701030001c503080c0d2a4000503100581c0d43e00d011141150100410340c00180015881180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 333132275 1250 333131025 333131059
    0x10020f030d0204140108072f030318070e160302030403120903051804060e040825030518180415060f08070501090b1804050a0f0504050c03100c081305070302 69
    0x51090b1307207055042e8403000d04168011200e0840489079640410f1000d544515039000f03400300918481c6003080e00c1d801014042d45941c0c11604191524000c4c901d980404855104060040d034024040c682d500b5682c6140040105044403080c880c004249903000000c40c0038588102d0641c000e004040c1070606c8084c40038a40103100d030344407002613459441c0350041c42840b490315000301c101311462200d410319244c40c1e986600c1d50a9000448508049031445070780c3c43c00260603c0100c00c11402034445503183c3d076410a64031001d420400d03401e40301e0022a00c80c1e0050300c2901c054950416003201c0c041c4c164122903403686000303094a8000c15461090305800050f20140058144195803003079075030241013a0f450828498a00401b4002c600a5004c01040310250800364443c1b07521600c1d81c840481e031008002200070407540c0646003a21250054452522203007010000304181d07145507003040054a00e0800018011040070f400c03401e089a00307114000c1400410000c07000615001003000d4100d000b003d03d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 333133525 1250 333132275 333132277
    0x403020409050a15020a021228120506040603050d12110c0601080c190306050a0603020a0b0705011a0d06180b160806010e010c0204090609080f09030c040e07030210020f030d02 77
    0x1c4603000c843c103140c80131042e01802a039403980b8254005244000c0c210801071000c4d0086120142e00084d034040040041084948944013440c640d242c1400d040000410302068400003801940241d09041c010000a1000500d50165560520f44010004d55079078508024185070841c00812150110b55400003110206500307040381d4200084501664110090207900e50b40c803039009001000c42141000400e0881d0400c3c0d0344000081030002c0c000381c9960014140b00d206400a04020f14085542401c00409119140e8025241c084150a501c01e950005034a8514800020121922002103403400d0b00b02051040c4111380c4400500c40b00c0c40c1a803c141100b0070b145080e60300240e40400455015402040070a0410300c042c0d44110308004e00390240005404142c1d41158941c2d40c1c0d4012501003038181c03010f88100e41c036000c04607136548219802c06161490011003148158549100319002038400522072048079416a00e454881c40c00c035005a041503039040d240506400001012a40d06095034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 333134775 1250 333133525 333133543
    0x12010606050a1206030209010b130803030711012316020307050a050105071704050d0528080601091403150c07140105190507081b090621250c020402040302040905 71
    0xd83c036540d49141040300d2506131652440084c1d08000e0120051000c212800c00030300b01c0d0700815112424460f1760709000d920f1588101e0f14500058030700071415000c56001c0c018209031105200ca03010741c8060a203041c48407408007a152078101890202408001402801a24859078021003030303444650140c20f2940c00b0b800c0450b18000020280320301d02300b82600b4441d80a000d660000024443d90886e01401c0d2400e500c4060045034101c1d03c2c0c01070740800f2640120a607048052070b030b500c14603030502900141c40801c45820034110050311415045003034030002045202041c29103040c40c0715441d42e80c0400b800303115101c40607140011403d63710480d0f0505400680c0104042946403000320f001e00c114000310b4000b542c4510009880b20b0100e2003a9651085c81c48141c003203001600e15011003240001e07441c0c0d019010b40038900d01550410240a030000700422340c000051814151030f400030340f0415205030301c504000010700c40f0140e080e10039501eaa0303044d0b03000386901030001c0154500c1400c029546000300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 333136025 1250 333134775 333134777
    0x105240f07060e1f050414030c100b0d02010c02060901050f03010b070c0e1306050705090a0303080105040c0302040602070e04031701080105160207050a14040f050f04031b03090302040b12010606050a 87
    0x2983c1004280c5001404082c00c031900394010103007084030b40301d00c0c028090241c0241c4031b4655034a100200c2c18010300c010080c045103480200000700240214001340c3d071030b030000780c1e1044032104100c00251742c205801030510341d03044941e00c1d5180e07400401030300e041c0110016010750f01008800880c20140c0030f0020281c460250300a02e40450751901941c014920454101c0c0c284603d62034802d00140035a0040794001c4805d0038024141f250a802290604110394000e5000503c800d00410890a01c2d100d4076254005a1909501c0c0c1410588045d5654555206018540709400c0020713042c0341c4a600703510900c0308100c100140f903503900c2141a000e030005440c0c01a00803c0c4108203094603000207105400c030b0b800a000b0100003442c2100e00c00b0b20354440e00da0141c001751900d81c840300d501c0252151a05c1407180d55075116203414a810002c0111001c030002481c2d100395800700320041394012070303030104480d8100c0d40441c134264060041428198a0042400e1079030030007101041150b00800079042c00191 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 333137275 1250 333136025 333136031
    0xc0a050415080304062a230a050105090a140f1c030b06040f080115080d0c061d01090b0703022106420906031503160315050a050f0105240f0706 63
    0x250b061031030101d1a0b581d03801010200f911f003080c8040c081600702a8030002c10103054901d1500c958450500b52a07040342d1501c3c4507000740303803400c00700900402c0510034001900000c1c0f2410a2554800307035540101070840c020044280a9210203601ca41c0103e108002d003d01115151660f881d41050342d000e5500a5844c15420072284406500b0000c156404403480e440c028640340406140a540c08403049505581c4903848400c50f480047c0e10140540f03900e800140006070808060070315000704c40c40600070701c1c20117004118042210194220b05000380040c1500480a81c0300c41c4005094880007010320307002100d080481004000340c040d40d2140184034200b80d02e2500c0041002034143d8442c0014041d03225200f800491000c0500c01c401308440d0390050101c660754210700b4840e040840b4039510440307056500184010340000680181508841510001e10003400c10b00c000b501440014043c0e140200340e108844801c044078039550030312041042502e035230307603101103040710300c0a510904040c2c4001c4c0c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 333138525 1250 333137275 333137327
    0x106060305090313060e190e040b090604080d050705070f0b010f0f030f12050f0318150f040209060a09020a0203030405010b090408040e13120c140c0a05041508030406 73
    0x8010040703c03131319100d903503503078911905000054500e00031042c4d115801c0402c05031a054900d0b20212010301811072194040b109190078074007011150030050203664580c01000074000000c441c0000d40b015091296400315907070b9225070707003192540502c0c1c00150413101c0d8200381105200b450010385043c0c802c084040c042c0291585190f00c0d070502584030041605072452408008a440c01b603148800346510b03e4200e14041c0d0010610400d50019030f20f84e0702410a901e101c0210600411071a020001d504086104134075003d1018007000c2130091003c0e0140c059100050280d40e102581d58000d0724148104544034801c4400003503403a007088500319000e6180040f0b8688c240b52601c1c04c184200d07481504036140c181407003029810020040c020740c01c04000102c0901c0011031103a08602c180e15a651805880905810850622240d649107040d20f608a45070b0081c080c0c0300c0000980a64009860100d41a041035500080c0003100d41d000c2c01407808042408581242e00c0603006120025088054080d0300d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 333139775 1250 333138525 333138541
    0x19030e1e0112110408070e070906080c04050f0f0405070c0b0903040e0106050a02012a030f0606080105041104080a052b0c060b03030c010501060306080d0302040e040809150403050106060305 83
    0x11128100e1103002c11100004181c074010b0a4124800c07180c018600c590516642d840b03898944100c58001c580b145200100700441d0660060841c0300802c41d80c43c0089140c2090a0905283c3c41035002d00340c0164145699a45e1549810715502601c20f005003040007a807070042030013401c02e103015004980b014a00e401140c0348150020030f44042d11855400d48140d6484c156007075030a680706116050a41d520303500c0b01c44d2080512403850103000c41015451050100e0090010112252142001095450000d080c000e40381e202c0c1225065540c03d4070001411140d058000010f8000c030791046065228050540081081c00b0030404098030310132101c902030103031208a07031100c2e1440c44946000146c03410001800b081c91600080603802c1e0142c02d07685800c401004181c2510b2098100c24040b90f19000200845070381002425140800c0380f038114205810401030901105000d04050455000490800190341d5900082591342c4550301401c5d54540d40c0303280030f501800d200d04c22140032030f00e0400083c40f85 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 333141025 1250 333139775 333139819
    0x10e010605031f0c020f0109030905120f0a1112060a0c08070f0e060d0603061803020f01020a0203090d050102091e01020106090b0310050a150f090b010f080f04020319030e 75
    0x808402c000b040c165243c442d5a00b0010f02e035590100d000c500c40d040f40004000310038032641c1c0015019a03100e80d0f04505040c144404010f45241d80c085581c80940f5446001c20003291001d0000e07440f80300c094005c462000003548000c8080c68031940b0b405600705010040d00d0301c2d400301d88201d0054680c100c0541e1100c00503590b028040c1240c02c046000c0180500052910038000c042d45075400c9400030300e0585a48410003210001c1c3c5201c000518203080000500d43c04001101c04040d041000354902840010025164080c40c41070b1400740e540801c281c800c0000a4060f1040c0d40d2002d00341135140d40610038042003185106940c18059440c1003008a4803103094015040946005402040681036885022004100c000c1c01c141e909659440e480e841200403401c54002001c518400640a50920608000f1191708800d0241448101c4034400069608504880e5000d00601852a070035079136030020a05002144603010303100c0e000e122403c3d0800d0b40140030000c2c82c40f0103079014036044000c0c01c281c3c00b10f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 333142275 1250 333141025 333141043
    0x603030c151506071205030a020f12070e03160603050907150207170c01050702060304050a060501060903050724050c010603060609060e09010c020c1201110316080a2304081b010e01060503 82
    0x17400703803220004103450380100011a0004c40c203003001464043d00312041d01054101d85100e01c030010700001403240d0540d0120415a198034102d000e0800e0240c84043d4002502c564403c10085c103441d03100103480070b101484010018002d1800f900041000040001d446080c0da0080100c240000d2046500002c3d00041040e006001a11560314003000380d000c0148681004200300d4040c0704407510b140025650f0f0041074001e02c401d4842d102d0322400c5203001c03401e102407500456520185000c41090344544030340d903440c110103a03042c216994119214514050320680e0006800d0a08124002510300841c0d444101181d14001c005850390319060701140c00c0c0d49600c00c070040141c1c441c2c94040b0551a06001d44441d021142000003900d41c0e801c1c4901d9010340044030801004899000c0c080816604160010b621910708041040604d0035080a448802c0c070001d036a4205031035400008040191020844a01c000c10702c40c4201d41e82d680a5210380030f417401c2c0041c801d040d4244440042c0d00c0c1000518140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 333143525 1250 333142275 333142283
    0xc02010e0708030f030103030c080c0f0105010503010c020a0c17030c06010b0a120b030c09090c090c0a020c0a060f12020d1a010e030d050906070c1701020702010801050a031a0603030c15150607 84
    0x4611391035620304036901d0000c0304003940c114104001520101c4030800502d504104330500110341907142000305400c4811524241d015900a0241030000801d02c600e20815525801000c40865000286203851805207250104103489001c0000c00c81d1b0040901038800086241d4600b6860340c00001100159100040001d415a104820032400c61904000646d0b116441004884840684000007280d008003618803465040300010350f91110380c1c0c1840101c07101c07d03007959824003892419800901c80300c90002d5030750070407926801004207940c1c1a0115900524007410a03c0010040d001c0075001c40b00316040140401c4c00c3c040c0740034082c200411a802c002c1080d80700e5504110f529410b20402d6403010340100d408103c0d900d0007155006042c09c114450702001400140c8030039451002410340344c03043c1c1000340b00e007945401c1000003981400b280c5400c444c1c200e50100d429100c440200e40342d8083c00c810312019008020401720700301901c00403d84a001d0a2100101c00002d410a2050364030500102038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 333144775 1250 333143525 333143527
    0x30f07021603030c021f0e09041511090a090606021005070912140708010c0c0f08070624080c0904030c03030605100c1506050102030a0c151109010210051005010e0f040c02010e0708030f 81
    0xd0307801d1621048040e4002d00411412010a000e181c3c0401210048911515030a0021a0783351990401403022400740c00c4480701040305c0b0703042000295840100711b55600300552988001a0000d11507101f690081024540850b2641c10b40d14017145032000b032007504410f41c480c0131400203001105000d00700285149480d00c1300700181c242c035030340c1500400c02e0040e14141000c000c02c1000404500c9044540100d5805105a1007445030801000160f01d83c0710f0300e9160b0241402055030741d00c560000b5046949404c100b5101d840301d14099015200c20380c46198808811a00703100000d0f000104880d885100d09400002c0342c1e281000303402191003d004050040e40103010350807035140508a04100e680c02007000d11205920b460b519400d60360f03904110342c13880c00c011505800702e50f01003220f8919108100420702c07040c64420031007040b00865202d21410001107a90200c03445c3ca43c900c0340744480001420510410a251740040e0290824004695451240d820b000800000200551314000840c108203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 333146025 1250 333144775 333144797
    0xa051e070c0f1509200303180d06060605030603010e012f04080f0a021206060f060a03111303290403050915070303060911040506030f07021603030c021f 67
    0x116050303081c0c03401c2116800350300d4810307030045002c805005440035116040480c015402d0720b4042d20040d111040781040001755032180c85141c0d408015200300380d80003a03101006402001c00940360403002c403c064091441c02c00c6c0840c059602c140110300c0740f0bc043d4000c0c8038840c1b100d1209801c0b2510210390542850003400c862440701c554000000c846480135a0250034191140405810708070344502d8160310f6480714284408605058070318003601c11440e80a45000d20302746022509004801490900c0740e0800540200558080d0340031910703a2010400250b1200c1e81c8001c120607a2001d03020030340380014042d107000c00b4014901103011540c24000d00c20b90700398499940c1901e00340c010060702c42d030080070101844104c00740c01c000341007a14042c0ea00814003600d0001c5590443d0b10300d400c035814402c4100010b100c1c640b40c10089075045000070074180703040c1c1d40c4d034101241000341c641c40c5030401d030119107000814590700000124515000315030072108070110b0351408107010802d80c11140414224104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 333147275 1250 333146025 333146027
    0x140403080d0507030204050901080d032a110f19021806130513120c0c0b03011a0c030f0c070303031b0c0b071107060306090f0c050415110a0b0a051e07 66
    0x103d070003445508000d410f00b602c440c001822a48241c000c0040741d80100340c107100381c0d50f05000d40d0980c01c0d0048000c481424010380362402c1c003260600010705104000340d5509603000200542c90344006440e05844a1898400c0f550490042d009801d901ca200206d01786501407000c0403019000b1100204001d8071900b02030f4400b40a0007005182c01806022a02c0c000081020304a003451011916503034201304801d289025010001c481c1c102641e442420320041c0807a201030100c05080a40d0140095224205041e90700c2c69442001009044000e001c00d503501e68000020302d140035039210f5103081c801c040518122604000005208100143d4010241004900c80e4165240c1101180c034204100b04402d4070314616001c200e44c00600000da81350b204001800c0c0724450b901d542d609502080c020000402070040140c043c50040b10250013451408403422409542c006000450180c1540c1030440d241c200709844000c100c0d80c24003160706200004007600310140514502c9030742442968041e1302c40e854 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 333148525 1250 333147275 333147281
    0x91011030717040c080d0806030f060105131d16061b0b160c051501050a0f05030a082b0f140906241206010807060c05061311040e010c140403080d 64
    0x4c1d0782180d40600d000c5454034046c02034075040c0d003094840c0c83c142d08000051510301111090f06060641110006026a58842446044501c010307000400d9142c0c6c40507528115003050742e48015203129014041d1078020324140035008543c1640c070b4011001c1011620340002000c00d2100500d241c21480000d95511885001c02000540f20314003024201d00038ac0c0c1c0d842c90070a07080d04111980b0f040000401c0140f5000405034054141c003400646403528004c0442d40d60b000c408402044102c000c181d00d0181e40a0318a0a4040d044c5000c40c28107141c400045c080052680c5211345203100e0074141a0a91a604200114082c410709002041d0300d43c0c8002c041400f001900000a181d920086404a0165a91b022981c0300741c007850f0180141d5491305806034a080f5803a4000020304c8041d912240200b01d022585e81e0303108180e0300040509a0583ca004140210300c2c409842e8014581001210b070801c0542c4001144070081e25000d50420002030502c2032801944801460200d003000380e4919041a60 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 333149775 1250 333148525 333148531
    0x1031a0106050906070c0315091101050a020307020616230c060f0d0b030111040807140d0203030301060311160303021b071809020a030c08102a08071106091011030717 73
    0x408040c00320b079100c0c1d44507003440902c0c00301800412746403903d8805002c0c0b2011154840e003800d0030014901485044040d40320300401801a110343d03004260b9555051286403102c2540d80e100c070f4200d803003007070a00c3c446420312000d070303082c0800b4411300380411001d0920f8421680300c1080c070034500d410000305404080242c000070603000d4242d5203500320030b14142034107030160020300710020180403500d080c002039440c19143c2003441761142ca130411000000d070310040212070544255203400f0420b40ea01030f81c0e200c01c1c1d201e1030094805000070000e0140c01e051b0701d6400780904240074032048a9000d600081160740c0e100e5401240b449040000208001911a07440f051103144083c00c0080c8081c2d603a200c0f080e603508594069100c90304410080503074004203214400b26481910100c2d101441d51080e08014524090507030300c24085028040f82c03e207801442e4a844183da05011600d4030300e41400850f480d00210f08601921504006104141c1130740070064a201e0400c542e107110000b90041c0e0003c08220f409 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 333151025 1250 333149775 333149783
    0x40603030e1e10051206040203060609101e2601050105030123060703030902090a090b0703180b16120207121808060c04030b09060907050103020c01021b0601031a010605090607 77
    0x42c00c5040290384a00c60800380340001501d800791a22008040342d40c041100810040c0f044c3c0c810810024a030352281d00307841d000802034640d084405002c01040c1d410918100e001c044000070302c0710307410ba0345034062041c0000801f20100b00803050420301c10f00b08046000c0c005d8074089802400188881c42c94821440d8445400c8218040c4403940ca4002c94515401140182c0010303031622900710960038503030811034115034042c4040107400c5144e02d424441c0903000d04600200360302c5000741ca4071030101004414100b5007000c0001c0144c14401540c549000c00822400d0210312100c00d81c510311901c91003a20f50540e04181c90008a210310b0f81c1c21200b10b01d2908001c805100802008141050f041004500c02c40c284a0003942d580e0031130403c1d07001075030002c140c8852036102004001d081132000c110101110003e0801503120320808680170b01901401e284611507904000010102ca03d001076101d040380c0c014445481140101440c1203441002409120042501008500c1c00c90404030b004107850303802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 333152275 1250 333151025 333151069
    0x913060c0905150d051006210b040203150102060604090b010e07050403051507031b02031606060b0705100b100c1e0c18060e01080703030e060c011407030b040603030e 73
    0x540e80060400383c040e5040c0c0d55412804120300401c1102c0d40300da00e4101404c480c00106852070020300070401a483c19145241d4054030702110b1101002d5041801030403002401551640f070b100d14161980400040300d507006119640c0841c5481c2498490070741b14076000002401c190382401d8580b2002a000360140c01001002c0200001180c0184552442c0c01130840741c020035402c1030500141034a86100e0000030786191b0000f104259034000003101c1e00e456100442e40c3c99400700e81022002032003103a00410054100040d850304001d0302041d07035140c001c0d10010400245c0804c80501040c06403044401c00071034807890300540410b0f00c401003d020310340944114546044030760741d4005034000c96400301048000240002c10aa0614040c0b440601021401210316600d0030074070135942c2015110240a101c1c456140c03035403944910080340c03e6401a40700900c104800c603040408680001c072102800207140c141108024a02401038008694240e6104000d0964501c20058181043c0c0106031071040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 333153525 1250 333152275 333152279
    0x1b0f050f010203040f06110a1e0908030a11060a0501030b010e0c09030a0c0608070f0206011e1508010f0b040b0d050a09060c021c09180905070e0103200913060c09 71
    0x401d0000f51320452003001c109030007011a1603c0f009803a295070b2030303c0140605000c4c0000e260380c0300c2e41801d0b440000c0b501c042c0c0c916040305025141c41c0a00d80080c82d0034040041c0400325150800340c0180c0c034080f40740407102540c6c0d03070301c1c2020b085840a0200800300600c2400400c044a0325060140d000306482d02401c2c640018600040d1800031800c104403045100360f00d04101050708a040b079988244181031000b95100c804130000d48801050203498040c109503500c1441c500e9800c002403005d03100b043c50220081410f60b6001e448284248075007800801100000b2541148140994003118421600b81d0305081c10440204080d0800400c0c40b401503a94801810105005004007100c00d500c0d500603103402c60a20459000703500e80c401085080c403802c1941004005190316041c3c0310808482c00024480c2d08602e86503003042d0740c545c80705840c3c00c4c1075800801801101856012081d031842c0a120001642800b03100004508803001100715001c90300c030382c011803100d0b002510780c441c1c180781444582d6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 333154775 1250 333153525 333153553
    0xa14070f081c0f05010f1203270504020c0c210a0609020619090303030b0105040f0b03040614150319020306070806031204060806181306020717030411030c011b0f05 72
    0x207006805038081c229107071030041198203c6d038450f440142651031458514406a1f4034080c1902914050500072088801d80c04001c80000016603c05454020415583c4100c03550305a5034503168807102503c1442d054811880a055070b007a00d0404074940009401a04e106445602c0200603100b0180e030072071400c001145241190200c60111020740361070785562039095040050458400c1c001541c14414100020f00100450340604001c68803031451442da01e5944c3e16200000c0c0c003006031584404030101c4113000302d80300ba0b0b100c1100546030a40440d2001c200c0354050b200c03017880f12100690550010740100c2e000c14458075140342d110001804840301c134100c0000300c0c0a10313403259001c4d10004000c01c040c01031500d4904007aa1101d4400301c460521401c00d2500b0400304205000006d003400c2d400030b00d1008020341d5181d0010f2540519805e84d44903d020300301070406840c4403c0c000e04c64041d00e00e400b2000e41c019201d130b01702c10100242048420580d50307604800310003d04070948951244082c182100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 333156025 1250 333154775 333154781
    0x1140901022d070605040803071e02090115020f06160f02070503060702011406040e0303010b0304030324090e070b0313080c0304030c0302090714030609070e090c0a14070f081c 77
    0x1c09141e668901c1503503840d00e0260411070190004e8040190410041010803400810381d043c10360440120000d00c442440841a1903000080007901704241000001d810031f46401d4440841d000c5800b5201c40040c007001c156140c94044520300c100042890480404070312904060b00c0881c001e004070307100c003522400000e14141c01100c2200041c2c2d162801308401d5040c003540c1c65041482034800b07100348024010007a860b4041402600d414032008000102414460342024900506903441440c000f1007070f11030701412100501070700d42c0250a101c04610f81c904002140300886012507801815030f02c0e50101d4035080d0310040c03000c0d940500140501054640e0130f0009000440c450483d0034078641c654814400300402c000c10480c28488100680c50301c0007200720480781e201c40125090406a514107405649074600e4200c41600318a1034420000c028801000408410ba215100c03401c180c8024400c9450902c03800c40c005102c00b0720f040740701c0e00003a00c0302c01400d001001203103007a02144c07038500c50f1011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 333157275 1250 333156025 333156073
    0x60e01110a06050a1104030c1a12010f031415040b06040f06080304030201140a09091508010e06060108061c0627080702130c081f080313140108060114090102 69
    0x2d031a50b0b04144070a0008500c2460f041d0101d40c0c040e6810b051458403030443d401d94911030150030441004141400e0f641000480750103049c81281c047c42540c46101c401a002002e000c126100305040524211194001603550441400c0c9000358403150b4466507040c0320014060802a00551500070b0818078404078010304c00680740b0340c401103880c0d507d1800010580c0041c800c94180300d01c01001100056079101e202541900c00700d00d008500400e040d10009001c01042e0b00c5001103500c1c00c1d030000f6903008046100ca00817a002d9881d8102901d400c0108411190103001a0303422158070142c01001542e0740d007110003043c2c899042c1030701444590095828107044202d01712206140051508214a0055a001458185420708000904070f0340c00c05810200007400c0000c81940040aa681030650f0000b100d0140500c07409890300c484030303498041440e60385030046020100e41d140701c1c401d980d441004c480b0b02c2484140c0d45d00c009258041c2c180c8482d58020001c19046014801e01c41565036040201110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 333158525 1250 333157275 333157283
    0x20f0609060d0b090f0709090b010c02060d051005030115060c082517031005040207051204061106360a02060301170c030607020d0e010210110304020a0e060307060e01110a 75
    0x30b40c0266a0042111410000b800e881d83c2c00c1d05d610512a21a41c0300424000f6511540320011b41004504010794081c200310f44000c0d808600054200030340c00752508102d001d0b1010040300c0e8010380d00c1c1e000701400d0b1450708440d07a1080a1030481000103d22036002d41c443d450194210a00e041d52980701c801b200e12640c1a941509540c24400300c0070028100301290a0619581049081d030030000341c46130001c2c445100e00351042c1d8020501e80c0a120301840030fa66485100e15010b962250340c0c200c083c08405014140040601915001440d12a158a90070200c85240c00f0465001000c003200b281d1003000008e58464140315002170740c00140c0340c0c0b0005501070040d002c0e901c8002d039690505280b401096054450080d040710701441156600043e000b80200054281440c0c240030060040345003005040707291400038281245154110008801503001d64001d4405000050702d8a041078102d0a041d41c903075406500c10798041000074030828507441c0701ca0b814500041b01144005200d03180c010810001d039 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 333159775 1250 333158525 333158531
    0xb0c0604140106030c060507031814100c020303070204021608040303050d0609140f1b0f0c070b040f0e061f0f022104090e07150519030203060d020f0609060d 69
    0x1050150080310708280d045003000900007141559600704428200c2c1c0b040d04140170740803810f1010903000b002142c4841c002c9600c242d0b1012b5070b5181128aa1201100740c81c001c890174100e5540706031040328900e003840e80240045141c11244c2c2d00b400000c0d440004400c0084020990781c2000440c0c200c010401907000307540d80c0b61541070200e419401c54031260f00c11145680b52607400e90210712408101540520326801150340d940e6a0744510903180e100003071441c10b198000510301c2c01d4078011405010000380750003c5a540b1902c407007840e1300600c40c1d40074280017820a00410000c0d811070300d405503400038002e0700d94021019040d80509005400c01d003e07001007a12203a0303c0c100c3c00d030704021820320039841b49441d104a00070041c5025a921650003682c86554aa101c5400141c0c8100709140c010450356080008048010100500c0d5400100a98044298145c01401d40c1403003802035038060307803008150000010302c0f9800c000400307402c031507141c0d04504184440d003030703540d1140040c00040250030b0000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 333161025 1250 333159775 333159781
    0xa0201021603181401020c040c0912080409110a080c09130507170c160807020409051516020d140304150e100e0604030f0c0c0324150524040b0c06 64
    0x2102d02607070035000041c444c4420204030020b41c2c4e0001c0d83c40c4080b0780c140e800088014407980111055507482c0c01c40c4250548503c244001c00c000d11005108640c9a050104440c0104064800d640e101c0c1080d98000034408401140300007288400620041000034000484140306050020982d0f40803900303000851044007070061890200442154050308081d442c2d440c0c003200c04003010398100e0119000e002c580d0b020619030115115a030161055581010031551489140594500c500000b00c0f04862684080342802c0c094500002c1c080315409225100e00d0940c1c80000740022540d0070081054400240c90400c1c2c0540b000184035056410009101400c0120140040c01041da0304440040711107034403500030040841e0b409010f001e5201868600213030b0100340e03803e00320011091500080c20540b980030030311100035100c4485103461881e80300c00b44120304142d200201298a1441800e40124120580c010740c0140c200e0449103001e000d15074607003440d0f00e2b2000f0744550307001119000c0b1141d10440034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 333162275 1250 333161025 333161057
    0x10e06160e2b0f050703050c01090602070e0a090312050c0c0c030601120210050d050c03040b0108030c0a030e0604090f150e090a1e0f0302010903080703020705060c0a0201021603 78
    0x1600d044003042c1e5a80c2000ba07610a4100310304200c1001508400d4100300c02a02004090f07504540301c60f40000403150440c1c0c5904001d61140403140340107000c903480703070b100180484c00450b5040407a014400300c80c1702c41d0380b202c101078050314080e1011010840c02c1e9500400c0802d00e8424640644c840100c2d454039040300700d805d00d280907a01400749102e980581e00400241c00b46011f9442c400303038151101c03400718602d0742c3c0603609070080c8904080c2c0d40d424501001002c2c900c050140d8031a90007042c02c1003980e40e03503500c4240c030ba1050400038171590300000c007a8000f00b03004200702d80c1002e4010300041c6c41c0a54074050714044698405002178020b898049611608994000a00c003070440740d034800f6081e040214219903203280603030005082090074000352180c1304070f881e0051081500a403151028003014078009000301144181140030802800200d61054840e100703458009620000812890b03c1d8044000803a81168882808540d001c104004000b2442480503100520036280d41c40b4001e40e202d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 333163525 1250 333162275 333162287
    0x601080d1d041b021213090f1104030308090613030e0f01140c1605040e19020a0e04060c08070f0c0f020f0a08030c1c1d210309030f0303040b18010e0616 67
    0x340740c181c1748018086610626404d04c100d108442d0100000552005120189409032068a4801d41e1101001c100003050640044115200b9034024060b076000d980c51200860405604000140c000341180543d051a81009803580002c0c1005041180440108052060603640903070046130381a085040d1f0340310b9041000d07040b40b01801d801c0342c0038000c400403182900c1e92410016003109205003054821800c0d511000d00f480040e0065045030f445038546410050040c2c8030000500c00013641680000c1c4880340300e64080125408917545075405060261260745000e00d4401060342c0c0196942029a0306640741c0b1500c20003003010380b0107151681c2a0340403440c107010441d03070702d81e0088141549000145d40e12a03c2400005104400300c3c00054200010850590706415039009400100c00350740a040c4000014051000c4114122803070300708907121607512408192401001d41d02c035000828100040c414007c3c40415000000040c1c0b4098441458642041520a0f6000c0070320981540e41c4070764090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 333164775 1250 333163525 333163543
    0xd0902130c1b1401050406020408060f010b0d0b06192a0f150f060305060603010609090b060108180312010501090602030307300f06050f030601080d1d041b02 69
    0x92400c2181000341d0501070301c08a20241040c1400d00032140440c100544481d030420080303070fa40c008024030714280ca8038000035400b07402544028800c450014040551010800381680d038512038690074174503803007044005041d0000c0c21a521403401d0110380540304101c45001c0c640d0200ba6140d03241413205000020350308040c80100c1e850301003d2070030703140481d00f003401d60003c40b80d101040f0038001c900a1207490040c00da188140010508104002040c0080040e03403501030081107000f000b00655039101e5000710f0f051803000a152031442c02c002000340d03010b503d9459200180b065220b100074400010b00b41035600c00580914881880030040c855541d0011070000035101d40c0c002903145040000014000b503084031418458406a401c0703606070003620201010f0100e68403c814000d0740d8660840402625440c0035075401aa00328a80041a00d00010100e048601c901c0c040d06005240ca001280d00039007012800c20000110081345039541c8607441000c140300705074010210a000c07000d038004e080020003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 333166025 1250 333164775 333164809
    0x6030a09020f061905031005060a0c050106050102010b0f10180e0a06091a0f01050409060e010e0705071a130210030b10030e19020a08030307050712050f040e100b0d0902 74
    0x1880061400c03540c01c1c0003420181205e00b03000d62641d07100d00000011b05070a400583c0c021b000894001d400d580c103c061300990701d118a000340240c1740c44600481c02c81c2d440191413036200304550b404034a40e0800c007803040d0b6009902d2500414076000a80041c50380b01090307004d0459804c000080014000b040d12038040600111802032225541c8100c95180d801140301003280300701c1c01c92101804581c014412035004220060051100d290b03600101c0050703220034030440144d41402000541454030401c100c40c1401d511240c0200c0c00582a0300c60440908010582480740b07030044840c0d00582d494074200707400c244150360042207101049042c03154488143c1d82100a050410881c000544404184545140041e003401820441240001006251a940010343c5800000103003c06140d000000707000321070103000c00900144603100221071a00c40d4010b401020704082c00140300702c0140810b055001580b9114840c2c2e2503480300d000841c1903000000c45607107580e40394652011030402c134207401e411f0500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 333167275 1250 333166025 333166027
    0xd0312140601080105040b040b120d020c0a0506040b0a051c1e0623060d02040303170c0f091201090203100b01090b0721020a0f0b0406050f0709050613030206030a09020f06 75
    0x7100041d0030032406004d0903224685803041058180c89907440240104002002d4030721500c003201c0d2090316039801042400c010700075088418042d00f40030100320100e0744c014103054541407a10b80c0064040e009560003004002c0c0800c0b00500d8078413841801e41c20387c0e02e8003800181c2c9099a03090038030301d08040c4a084034154180702040042507411811070f550304142c1014070070318096010004149228144c10715403a640b0210f00441410760100b2026070f42032980420202c3d82d1603001514441e03004480c1d404403880000c1060f91202d04021503c851503110b000000700d00300105600282c01e04191f0140c0c01805503460038100d6080da0302c00c2c460002001401c1c40907240c41d100b616644d9083e0800d0300c0340000b000c6503c404620f010b20811207004c1260304802180c0500300d6615110550781da00b942c0c00d6a105041c400410104502c402c4030500410715903c42e400441e10300402d128181d007040d2808201d071541514008056110300004604c074009800f40000c20300c10600c1080380d5800f203200f80301d016902c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 333168525 1250 333167275 333167281
    0x20a120b010c39050f0d0816080c0d0e0301060f2103170a06030209060f1c031101060b070c0b0f04060e03120c030d0507020f0304230d031214 62
    0x41c100c0101d441c02e580140003030200100200801d0030141d008002e00c0c1905624049401240300f0b8402d100059501c110350003903c2e640032008000000318240c00160003a5020850312030213007280da049544182c4510b81860400c8046000c1c00d0074a903001e5044000301e140710402c00d00c10f10302803180d4400f41035445542c1000d1030410280f104101c2c44940c02140301000c1c1240c150900d0700441505800030f140c3d04500d4800d24280300c03110054625440304034060300e17802000c21014641180c9000b0600009015680f00d2081408080302d003520142040c0c0c10320686640040c4400420f0140078050010107102d01d64481171494020020580c6502001008d40e05100c5c2101107590841201c00700e5070b4034075080000e807421800003400d100c0d01c00e500803605000091a900c082d00040080e100e41d520f140400c00442c4c1d945071060fa00c83d20301201d8208150070401040c0700118580c510104441035805440440b0440b80d40483e9085074030000c260081035034416030302c00c400c225014400e42f0038032007020f64116003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 333169775 1250 333168525 333168527
    0x6060906120f0f0207050a1b0e0c1b0102030718050306010b0a050d0b03010212190501051c0c050301061e0807050306041202010207060f0b1e0906040209030f0f01020a120b01 76
    0x100038400c0360301c035281c8a4407030015000c01030300100320180d040d680442d030b5859103281c0250b40c1c1c015440c0c01c841d621b040814580144880403201c5003120342d0304011002070359803554000c149a000361a0107441c1295040d0103039030004244007640c807400803034441d2810044134241c01c0c3c0c10601143e1100703100f43e00c0207005100d00540c0340c00b5542c182405080040d11400084114009080d61441c4990950b10200308081399464020409010380e403141c00d40006142101100303002e03200240143c0760058a590341480800c800c0d011059801d50107406c4100e5410f403581c00007420740d11f2540c00b00e43d400c3c2d14850094841d02c03e810960b03008140d01e030002c04442d03240001180e100c040c010405011041601e01c0c2c803040c54000e40481d00902d80c4280104010030b01e90300d07020003c2c080c026420780036046016595820012075820070200c910b00415005240d0345940411020354000c00c4015050b005210360020641c0c01003080540c05113a844c00942c0700c0c0d1400c200200099540c880c20030ba65410049158403d0b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 333171025 1250 333169775 333169787
    0x10606022e09030903050109080a0e010c11130b491106071202070312030b09010e040203030714060a0b090c031f0f03060e0f0628060902190306060906 66
    0x10601c0103010440745181e00302035030180041c0d0310143c82d55007020310704010852400020601000e19441c5d06040784240c0004442c28080c2c5c1000816a02442043d8809460982e41c400380c0c642c054280880e030724050700049101c1d56400d8000c00000da0344072003a03000d061040c0c000b00c034500d04121001c02c95100d9003008401c88420b80c401c090036080c20f018000c0007580301c000403a05c0c1d103500701070442c54103168000000d560713219604c0181c1e0114050b0306c04d02c080c41d02c40d000f40c0361a0103000b0700031140359082c03020b032400d80000908226850300c4100054000207211a4600c0350801c1d03d1405403025252a2003620f0940303000c07083d07462244600c00b041200c1d2540090a490308512042110040c680003104042d41c0e150442e00402c24400030f0490003c1005566080354402d800f8520a0340c1c20303403105000080c1e5407201554231a6005111820318000702000400950016928613408500ea65031401d8103002ca91095204450880300ba8810300f03001c85c0c050007080020411498100c4c1d0880c0740103001020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 333172275 1250 333171025 333171103
    0x1050309060c03040201120603050d02070905090706030f14010312031a10110f12090321070201112409010e0c010807031d030f04080f060106090e090102130801060602 73
    0x40c40440410b042d0b91040c041c1f158055900c81c4108034458885c02c00969030300b84511948014071865001095001d640d0041c0c5000700b550070002c04805060a00940190a1400420400b030340c1e00c00074003609039000700e07141e402940506000ca81c071006500c00142aa0300b84194a10745000b08501c0341c005444807100005001040d1034a00040c0480c0a40681010306032071080e0483d1042034106085000f11200900c0040c0040f0100c980780075280325424184c2e43c4ea5015044540c6d41441460050350203004818861200c0f24240d03a00807041041490445201003100d9480c00b21200800011580c01d10489182181030030003000640da400e40001c00003503000f080326040640f600b0500311004c40f07600503804002150710030f8030345401d2001084a05604184903d002c80c1c0309018881403009001705180d4140ca20542e54815101d00b02000154400310280c6100c000399804c02c08013400c0c040c408074010260240c0000070890b940b40078030080c5004462600c0800140d020441519004004489450 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 333173525 1250 333172275 333172291
    0x204140f0103090501090602180f1e0604080f0601060e040e0d1407050102030c0c1e060f0408040b0c100c05040e060f24040303020706090303021f061d04060b0105030906 74
    0x51030145180100c2c00350006001c020180d40c00c240d0510300b0450300b81c0240c505107200503040b0b181e00b40800100f01e900d00490f1006500040345400404901d446200200f00c2c0c000e0141005141c956108076851034540400c3d00c2c811540c0042c1d0061101c140c1c441007850740c00100312024018400c0d03c0414a4856154885441c00d010b103000c041c048085404040c0c0301e00b240c03c407001710340300d01d42210321025507808002c007482a070103144080d0f00c101c4071428003100003014020060040d030380c4115003002c6001010b0021b540e4a0010702c0300049101401c0e00070301c80c1011a401500c0b03407000e04019402501c0500f104d035001d11030f0920042c007003520752658607540404100c3c0d841669032800ba01041003502c44840c6224118001c902c1c0007550980c1708014003c8901c6a800c031803040b0360700d44088900e50518000200140c00c44e462441060102814000d1510104440010040d503100c40608000344040c10115140c0089000c1000b48040c03481071144580c02803d1541c17462400304141921200002c003100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 333174775 1250 333173525 333173539
    0x605061306032103060518040b0906040b0f09070f171203010b0d0b041b1d0102030a08060108091e010e060f040f08030a020d0609061809210210060f0602060901020414 73
    0x2140340d62003078200c4001000d02078404904047c2c1608038484a420441d010342d000c03020203000c2a0043c9000984511880d000b07040c01c0d6850701c403101c1c3c4a0000202800165107440750483c04100a41800086801005107886507800c100c00601103a09092340230400e01181d8400780010003c0700c1c0b81030100c0c4c21003500340e0b030005030b0b841440000030004d0040c994a041c1641c0da00d02e0107a812034216614060840c030380c110060718010114012070344c07445031420140000b80e00340c000c03031241d5004592842e0003514103420b0343c501d131800714200c0f51031241d8510910038580d101c04400710148824014550040904400402c030380c42c2c41d458107070800c40c0d80c3c0c03030003400d10a0000010f14070301003550560320448030310041441010341d00c00d214005045c0300e00600d420305500c005005d4400c0751a1044400c2243d01880345880052f0f01d05004941389144070011066000381182480c030554503115100107031101300c61101c41c030781c1080c2000b89090002003521403507030b204120a2000800c0e112100350001001c44940d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 333176025 1250 333174775 333174833
    0x20c010e0913050102120c03060112060312030b1c050c040609060e1605040e160f0c02090a0506010c08282610052d0a030c150507050703060506130603 66
    0x240d4028410010414412455501403142c1d10319210b0088d8050700c02642d8040b0f840115000080031034030a07100040c01c1c000071290201070240281c06c00003484030002c01101d4540925100044020f48030b07101200c264001c00e50344072813440c0512031540034109900041007082d051a00312421f281c0003600b1058000001a2007012182c0314404076400b03401c408000101c84d080081411445621031803508001c0383da00b010302c200807440381002d940e989400410359103280c1c03100c480010083c8405405541002200b010040208000c400200a8610304030b20044000212480707811340207500f4842c180070040c05914902034036168114500e890301c2010341d245990340315004901d2030f00301c8030340c0a0303500500c607010a940080707a5220040034032040d0540c2c038410300b2400001c2040949103408001c20301d8485238000d1001c44c040c02801040301d070b01c03030403c640381c50701c0c0d078503140e14003080344d4022038503143c0302d000b04000f030300300903400c012034451708981070126608503036038840030022103490f59261075450444 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 333177275 1250 333176025 333176033
    0x51b03010e15070f03020a1e020f0114090115060c111c080a0909051902070501090206190909050601120e0a0606080d0e030d140f040306020a050406020c010e0913 71
    0x407400a100e1081c04442c40c0368003092564094000444030603010410404c3d0b40c0000d41d0082c0200d07401c081c0380759508000955100c19804c20f024403511801e0440c4288080c2c20281c480c01d12070400001c03095a6035000900c0e00743c04d218250f4180c1c485960401502c0e620402001c0e421034404054542e0183c0e9820664020401040d10340c0c81d0b00981080103105c100e01d00090000282c020b103000280c42c0c3d0f6440210b910b4039840e20070394009032100103891900c92040c01107909541d0150200d2403003080040354040543d00002c065410174102c1c0a4541083d07034070458480e4000c800000141400c40003448913141c0500040d00540c618640044074a4032400040a0340b04107000030a0003030f51107802040307001d4840d4515640d401c0c1c40311144012400041040281345000500138040740131580d02c150844006644440c015040304002c650300250500000c0f0004419002800c0c103c00169681030319189040030080c50038804607901814090302d118032000a031a00078800d58480040d94502103031550304e00d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 333178525 1250 333177275 333177281
    0x1a3607260a06090218060105040612020d0f021908010f091a1e010e03070803040303030b0a03170306010806011e03020f070c17070f14010f0c021003050f010f03051b0301 74
    0x2a034034249008804590080081960003800094029984405400e0b2100760055045009584150118030705020400a080c81403100449082da1040050300b00104051800c043d200e220200c14105900800e080c83c44146007000540e11040358685000c42d075240180040c40101240580340d0b015071680b062001a400d0007900800382c00c005403001d6070180340610802030300700022550500003044081152a1441c00007000010344444001651070989141c0d0140c005202002205402c12841800000440c1c800b019000042059640080e664904000010604c0c08010001414840c14101c03141ea141a01240c1c0138404220f4203005a95031085200e80c081e0b4041c2200042c00c0c04102600030602410404038a1481d10840044940080c2c07142c0c1c7c440844040f034000d0400e034090030780c1e00354101d611907450f042d446112410003080c0d4402c250040340414010541c007501081c0c88000340141c0702c0340d444c805401010201c24560b6007030f00b10b6840075140c07401d803c88800390950b0451281003d41e020b40c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 333179775 1250 333178525 333178589
    0x303090309080d080a05060a0b16050f0f0f19050d030506011b06060302100e010804120905060304060c020709020a2102090a0312030e06040c121a3607 66
    0x70880350040c0c500d03e0010300c81c0501300c0c2c02c0d0310414204804150542401d50f02001602c014588180c10302008c0d401c03a13005800400c4c410b541c50f205080300c1d20640c1c4028040310b03410585800c05058490386504055240050840f412003000704044101c07400700b0808104e4008402c903d01e0701181d144c840700e004850f00c040f001100a40403502c3d08545007041010740c44401241c2c402e85407080129841707441503c040c80d45d40c160f540400c147c44000f50001d00c0c002042405480c05041c00b1113951b4892000c00e400b0b4004442c00c807a4585d45889103e510b5404000e407800810f4541c0e030075407422000040080001ca08100c0940b402c480c2c83c4841018040325805540044038003030180a00d9650b039042080d0407865003120040404d00d4126007004501010602030b10584d00413201c01459483c0c82c00c800c2d91644040c00c15509800308075412a05014030021840c00f5030144020254019100340510000b483c4610310281881030329144d00b40c41e044007007200011100704541ea203050408ac0139460101d84100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 333181025 1250 333179775 333179789
    0x30209070e0901080304031e080909090f120901020f0c031b0102071203080712050402061c020c0106141504030c090e0a080c06010e0c07150e030408120304060c08130303090309 77
    0x2200020030603138400006481128080c81c80c814110300c0c00c03030002585481049010b07040399010090049582017144443ea00089840d08031800c3e0280481a1810105080e10030748520000264861441d079040001d0a0050344160103010185a4400000c0c2d17218056880205a240055001000c9038000e0148000520000170521204995443d00409581c002c640e1a400f20b400c2525aa1000d0300758030800e403040380e01a022511b003403600710740b141c41401c0307101302c009525408001206074901d0a000784402408101d80070740340924080c04201402903043c04c0444d0501061200300082140c820207a021500d100340d0014007440b011040b0343c101400c01501402c9058000f0f1200700942c3c2c0046c240e4100c0b06e00c6103c8071601d8a4903002c24400313101c2d1071800782441034001c2c1c14a8400045030b02407041404e09000300d0b4078243c0d84002c4142402000c803500c2104c00c0300401044140001030158002c4459181782c013410524240031001c108028950b4082c0405941d4640c4400b05030140d00d030600075002c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 333182275 1250 333181025 333181039
    0x3010e1b1503010905010914100b16140708010506030a0b0f07050c07140a17100c230c060f0f0414010603080c0109060c02030c0307020f0a03080c0d020c0307030309030209070e 77
    0x1110080c4005d00820b228a0740748a1070980403841c071400030b400b000d0213903c0e104148000549001c40d40d407016002010900030403007001c4500700c006034114a0031960590524058810280780045d26402c403840140703514041e41211507d000001c0c3c41c400300e281c0c00400700505121135201c1c014220f035070780901d04501c0c0c0c43d807080c0740010440e440c3c6e20f90b0750701070303c1c00c129542c0d81801c1d100d80284e1100b1600c070f8200b001541c022117400c42e0100c151f070081c28110701c0f14a8028200c0035500c2d540b42c00c4031462040818003020002c4e4407964400d041c00265404009903031606814100f440b002c0c113400c8402000540309800c50301400705c40364000e4001c803000f5900a240315488840ca038041030700a040c02d41c41100d5043c0381c8124288460300100640e500c0c1c070b10801c0030b5410500140c003400f12409000c001b156000c000034001200080340d400c05040394100e814001c00800c0d090a401030f10300035102d04070500c07a9000d4402040026848004101a66070580c3d041c2c0051703c4089050b501106140c0e24250f200c42 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 333183525 1250 333182275 333182279
    0x160f0b071407270515010c0828030903091a1e120a050720030a050901180b0a12110412020d0209090c0a0608131704080709060509010503010e1b150301 66
    0x1101c10520000c10f2a01c0600304042e884003a1000310440748460482d0105d07074584d40030790100c0d0f841c1c8090b0200b512a596210b182d6902d9507540704107102d40540c80d030b010a540341409000d01d54858201d0020785902c00760f0540b04204442c007650b4501401103090f10460541c5150b0304540b040800342d42125441d44600141414070072403200c0070b05411121200000d0400e6699034158803194800e0350480c0ca484007070361411111800c111519440029668103004104003c10540ca08082810300102011b500943d142da0b842c4000800c40ca01c4426040b18203403d1280d503c0320180070804841c1114030f240801020b010340c07071002c01c0c1c0392088010701a4bc804132010400010f006e01241188902504441d16802c190321001c0036200c0003000c0d289450003490010100000443c0e900ba1120504030408451b4103003039070fa0100c90b1500205400942e80517446040400281c1403501d2041d0240500f103000b0700c10b070b115900e8503564448015240308000c0d0044902e00d00c040d2a000c001ca11416014001181d8a40e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 333184775 1250 333183525 333183569
    0xd0212030421120e1806010c02031b030111040b162901090e07030b01170a12180b070b0f060604090c0e1002070501050318030f030405160f0b071407 65
    0x2d1648003050350002c200c40ca01c1200c1d28400c2030040ea14160080c0b0050103c640000b12021040005204605020101181c0c20150383e0421903000c60301c01c090300d00719101000c00d0516003074410f86041044e0310b090a0005000300d86000054490842007510300a0059051703003400000030510011400450070340300e042d040b000310f001c503203203040e81c1f0720342c00900850703100030300065907240c10344005000406020014044046050f01301e100c8400700c90201c0b552184aa2105400c5a103c0c650b0308021480380716075001c0c03070344000d09150002c0080d00055801c2c14510744602c0b450410060031552600c20707a10020b01140d6506084c3c4000c0e258a800030010040741c10000b80000c0f000300b255511070f0704c001d003441c00030030b20001c0ca2a0540f01d069507154156220f440086444502c0c04023549040d0005108607152136907200701951144e070144005200da40c0980034020050321954000711200204880c003840750341206400c0303503641c81d440034040c61031455405142d820503c4680085a455181c909850156 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 333186025 1250 333184775 333184829
    0xa020d0f060b120a020603090f0313031a01030b0f040f080c010207030e04060b070f080408012d051506130e010905040b0f04020d030503040218040309060f0903020d02120304 76
    0x554800c200402c0100b0020301002015040c03001c500000b50b01100b00c0e10010309001020795000803840c01203800f6031040182c128210f0308401c05c0b189150440030010001e11200c0001284d4005030301c141c2911550540d03c0f01150420010041c00840c9200e4011604021070b90264400054002c14607540b14a09a90910701070f500031502900080e4007241c0603c0585498450142128056546141761002a40d610003065007084c02c1919050780c14800010440d03001c1c050f01840003100008180d60320380e28595080b80e80315008005041618100400504000e031843c4a11132030400c982607901c83c040602801d03000055a00440403014034207000141d0b1300920b030080b60107507110312a1030b1030640d41d0100c920860351044030007942c845c40c00f00c61100072a0040c2d00079604280064500b9407000c2d41030301c0c8140700e0401a14118002068110100480c03980b12800013007605003840d011105501e9600041c0e501086d000d0040c0c412454044025241e5804104990042041c2c2c01d00400d007800010b40e49582c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 333187275 1250 333186025 333186053
    0x190c050f0313080708150c0403060228050703140c070315050403090608041e08090409030c050f0109020a0512010e07030c05011d130e010b030f011a03030a020d050a020a020d 76
    0xe070b1201c100d000320380403801280c0300003075035403090041c03e907072175085260729103a40060b01d1010080410030010000c03071281d0000700140c4d070718528150301d104044800303040c0358181c0e0750305003017004414813241000a621105014840300001705032525034849014490030b1419550000388001e40c010700707100c00c0808942106100c0c1d4000d0700c40c950390f9a076500090381c03420002c40300208140084007203c4408090007a00b0f0984a0041d8011800c190150700800c00b104c0005005401254681014100700302c0108040c844000c0960002e0054031070b2940030a040101303902683d40306045800c00a68140000d5012042d4014803030221030300647d0700c3c100f1041c0ca4401d405102c1c0050b88218641d8102d036094201030b500c2c8280a412141c0d400c8801806030000c01f80480c0401d41c5540314480154540c0d000c1000c0c03032a03845480300014201c04d070050b101d43e1621a008085029400900c101a000c039000714560443c0b071003909098bda14060724cc0201d00f0302d68940c000030340c400d101400b1501800009855441 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 333188525 1250 333187275 333187297
    0x60909060906041e05010317040305060106080a020708030903070c051917030904090b01090507030c0813021306330c08031005030601150e0405091c03110c060402100c0503190c050f03 80
    0x10f5526008c06480b024422808090f16913448003004105803840782d03103400c2e4001003030500142020081c1c0e0b84d8614036802a82c060000e644082030210500c07144450030401007000701c03030346220040c0d42000b001d0009054868811110001105030b144420103108803003560740002d000b0402c4c11007510b0700340601402800707204050f625280000d49258024890018070740d8040e21440305543d5407903001056080c0104c0102d810165411030314003035005500440b0054600c203050f03c4a10755118a0540c5504280342c070003e510b50002c0103004442e9001b561000d0055001502290b580e80d42549109450101350f01c90394040c810070000007009402c200392115001500d0345e454190080c1207040100f0303904140c4412165812411240031100281d180b00c3c0e02e00c43c0c0c0c40c107000c5140460750072041c109400007003c0c02d131603800940c00c100c2189801d60f000910780e9043c3c10001029903164842c5070b9603010b000c01c1d030074114040b4a5042c1e900d0380644080d018071f542c400100c0b07201110150265480e600020a441 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 333189775 1250 333188525 333188543
    0x150a18120317070e0d030203120a06080c191412060109020909010e0601020705100e1e01030506090411090a020412120906140d02090a12051b060909060906041e050103 73
    0x40454003408030f8021441607132915600e501c02c0c800c000039415404000c03030540c4004c00401034220a00440544a40d40080c00022b01901e000416810810740001c01885400400164500c4070790b001ca00c80d00b901d113040000f200344421035001c03400c800101d03505808940b03d100f00001d0042030b140c0051482e10000d4510400b540da0390311150700d44900a555450158210320024440f506008412400c1d1321024074124209005d404040341c070080625181141440341000c50203940d507094002c0f03a401c00d00548041117240f805490b403108024a07a4280c0348581142d2011403000d00311601903401802044030801c1080380c031031510826540355005088040f074003030345000503074074052000094130200d00070741646090590416071000b9030200c100503038401d004035000b0901c1512030050a869501c03440041500b408208105140c0403d5144414440c10041101c00130750380b10315003001c0e0481800d4610404a484000c0040c0c050a480307401d5850303420401004082c0b00800307420840c100c2e8043c407060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 333191025 1250 333189775 333189797
    0x103050d0e060702091b0405150705010c0f0f05090a0e011e050109060e062116020c03010b0f131d010f0e1207030c1e081801020c150a181203 62
    0x2c01458003038014061762041845000408842121090001d07030440045250702d020744420008622084180f4400340014002c035407101005000d21803400448054202a007840410140090803104078a24070010020042108907050b19044032020140240c10000e001c03540c0c40c2d41c5003070120103101d4a507001d2001e42660014455009080180c02e46815170f898581882549080c01401da0040a0403140005141e42054001410b090751300c0c0907002280c1049600e0131075410007071070040302003003a074440c0e403415544030800d94034612071426040069858078920251048044024007400d11400c1001c901c070070300030503039410640c0030100800b02ca0300100505490317146c11f10750300d074a12440200444020444200030074014514a04031910410940c0b88410518134610b51403103084400303c03200c46001c100d4480c0d0b02d11808856a05007420320091480000c1c40e000103016140d41c0e44425014100062246101403003168480c03c00c554800c4042015a03450400a4000d40850b0302070700050021031032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 333192275 1250 333191025 333191029
    0x1060c06140103030818120403050102120106020d09090519050c130909080d0e0a120c061103060907050a030f240b03100303050a030b030604050f120a02030409020d0902090103050d0e 80
    0x30381c2c140c9403d070b9075079112582da51400300c07004030302c408110101e441481100c090b140b01c0400208061803042001688030f0b000604010100101a00402c5c10341d001140e5106003181e229601400b1105c80d13020214040c1c0b0b071030381e0b0714990340030b040100b40620f803d0004110b080000000141041786110820407500c660b907250390300c22201046c0307004100341c40800c6000c2d030180094000800711080714064500c904403a650700307082e40044101c58008141982c418800f801038611a2290424041e0007091a42c9000700020340105801015142030000100b0212059880b0354130540c1e0b85c402101082001c072107030b0003040e0320341c1c11030303e010359900c0d001040301281004504043e00d0080308124848a015425568240c81d00d811411410042550f01c007d01c40c415501041864021401f8101401c0d109509022690a0001c500205135042e601080741c4103006a000044a00316403500f540161541ca850760b83c48058120390384080c4d4043e403008008014840c004c5804811419551a520340044420f01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 333193525 1250 333192275 333192311
    0x90c021e0f0a080d0608031201030c0501030506030d080a110a03060e0a060f18270b090619050402210601060306050f06070609060f020f180a03050a08070507030b01060c06 75
    0x48285016048801c6007400580c3c03000c040c0000366820100450035640700c0f1000761544e00100803000c0800c0d10400100180240e03a4910342c00f9140c00e180c02c1c081c91900e04040703a69940400011010045a030700020200209640702001d51035283d4805940c90084040c000d000d0f007558000d1150040000d0082581d180b510300c20002141c80c040b07040700042d8640180d80248a64010322035480644800c41c40c1c140e444240080b002c003200b140c403096010602800c081e4105c01004145200d29845102071000745401d10030313000688140c922022a2555491000c500901d0302004d19072011481d0060845c007000001c00c0150595800b541e003002059500d004200c44121641700c05a00b25000f006130030042001600a90289401054040751481000d4112030032a407203100c012400450109a9130304144590a25110782c1400701d9840000e40e055498072038a402d0064001400240000780308400c20a017403005d9002150084a0300312031707603581c61001d000880d0b0302030304451540c50580110341d900a010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 333194775 1250 333193525 333193543
    0x17031213020108040f080405040203131103010b15070602040306020c0c1008040f150902030a080301050f04140106030c02120c060114010c150b0d0b0a020a030e06040b160504090c021e 80
    0x1940303080c3d041d01c403522000c0101c2c045150a46140008000224840e2190300042d8000c522040307018450304072604110100d038085400740b0380b00343d0612010110540d5401c400917200300c0403c80c1030f681e449840c6003800080c403691303000801090000c5040b02d1030f16004503000c1074840041d11507003042c0017507102c00c481141c0c049030003e104200d02c1e02d490000c500d00300d03000703042040340c200c0c00541e07030616030002071402c02803c02c2103550140020040c0304604083c6a01a407440d003d031000d000414036541e5203105464140514410955070b401a0010f8034030170041e00003480541024582e5940c0304000309074448000340601e084544003d010616994441c4032590411a0055030302840c41200508100241c102440720b1513020070503600c460701040c04000124050803102c0b000503a20000d804014054030741c00b40d503401140c1c001004010102d80684291688500c40a002407200402110141c40c14084c40e0003003503003036141204500b11150005038480c0808221004034a00050f00011075a90310042 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 333196025 1250 333194775 333194777
    0xe060a0f080a030c0309030b10031101020706021b030a0206070c0e010b0c100b011e1e0314130222020c120306100e0402120c270a1707170312130201 65
    0x80c2d01c00c1c1c08a846401c0111400b0310034038105100c16580e8640000b400016103504074804892401001080946016030007004028005024500e1401d08040d44820301d001740102140c074500448010345d0b41c00c3c8062001241c0c010102a1110b466050800748039082e4001c0400003808240041690b8840e18191800e100321540181134200c0900d504901601d03504001e14144100100d400340c003c601d01074901030039041d9680f049104e02e9446a810f405500e902c1018041c180341c210b00451800000c140d5a074060b50300701ea44030b000c070b0191020905c02401e034032600190341030701c2c240e05c424150745800030b000c002e01ca40704880860440004141c1281301c190b40706070380700301c0340344010306c601d40500e171040c4401d04000c000506000100000030b00320b01d003c13900701090210024016142044034000a400c8049050100d0f24040c0c1000c0451071502d42c40c000c900d0364105203c10607104040420001c40580419603491000303400302850b417a03894008003035002d503d2001000240004d10400140c03520300d501 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 333197275 1250 333196025 333196033
    0x605130c09020a020a0203100b03150705030f071e09080d080c0d0c0507061503210e091909050304050103061e05040203090a0501050408031902090904110303130e060a0f08 75
    0x68110200000d601941d4880f003507016540099000d6a02402014208040a03030301040145641c030815090540c0c1c2c0c044c010b10580c03800c0600111581c0201503950003400f60001c0344d0252204c030382c2520424450103c944c01c082035050300045031507200c140c9000701d400f8a01151241e900c80744040e81c07410303170403aa0035003602c00c24080c010f00f046003504050225400d5050051070100f641e10380c0303001d482140d9000100d0320412401041041506e0340140d207400c041d040c0d0000105907810b00105070140d007140c440d00c12203031303c1b0118090520064101000354628642003042681a1508684039000392080d2404240b5000d03001900483c854a00c1500000766038590b4421401d0004120003904041c0c4864868030070002d00400144092152030301850040c4100c5e03441b480d04451084007400042d011062080c01403100c0001c540b500078034503411650180880032142d580c000801c0c61800b6107003080f00c2c041280000010303940381907012103005001c00d0340c5d0140308503150480d140e12041d8a00ca900038641c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 333198525 1250 333197275 333197279
    0x2040f0803090d080d09020402030115020601060203030f06090c0c2e020711060a03060e1801051503150a0e01060909021e03031803070f06051903230c09100203070605130c 75
    0xd01301004101c42d610401c3e0000e00d145040e00440c080380c000743c01030402408400c03000c0460300c2d010003c0c0c5006000510046203185070921a0851241024001c01d000b20900d07030201d0b060203020409c0c3c0300c0d284148002c0f600c0415440c07440158000c0038040c0030f02d0003071103160001d1071100940200e0304896000f6003182c07540c800b444244040380c1c0c01a0b402c00101541c988000c200c0346545880640111024400007080d03143c524911401c490707001c0d03e000046440d08007403d01c25100401e5000000d078401c5030350002680d9a2442d03a0142a201716080d2940d483c2410205581d100c640c030a40c0e4003070084d0380c120b0700381524048480365041e28890003a4144d00c24000c00609014081d1403c0035480e01800b9201116603171400c1c88603000ba5600500c0c04030348003207122003c50320484002503690345940f0b0705000340c0140f0901450b0b8a10585a100c00c4000c100c000181da500651003107176483e4501801d8903804411042d802510394002001c04c540039410310012804e049941c1030b44410681d08044a01c180034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 333199775 1250 333198525 333198533
    0x207060605090c04062102070b041b1203030209130e150603060f28050103030e0108090703020f040e0a0b0f010e10150f112505091504090f05030c0102040f0803090d 72
    0x10400302141b0712003174841d80c6a501c0084107400a061540d00c5495403d41e0350402c0d180c40f0b418003d050700d8040c0d4203460f0a000300b29200500060a0300300da01401e006070341d201d803480070550b000e030300c400304d01d45c00303803c20101820703c2c040001c0c0d14800303071040150880310303440d52420151940c0c81a41e1156240c010100850120882032120b200301001045520b00c415044031440c1c4250340c0240d05c00d4000c600711901d081400d580200c0340c1581b240440000d4514641940e0010350904d228080c010f01640c0d07501c060010a8070100100e0f40500d80080402c0b00701e1419031500d11100c4803d000b16804500103c1c0402c20200091460fa0180e6020300821182c2d240a0323842164203c18411503807041200d140a44010030b172042c49403031003480c4612042c680010388060a54008031043e88658050100305e0100b0152240c545441011001c0490703011401c0ca25074206003d41d00001e0764040e03c10b000010702070494480541c018021100c4803046c1d030340c0300d0b41e85004007034490240102c075a80045035048403000203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 333201025 1250 333199775 333199787
    0x309010305220c150203090d06020d0905070314010c090f060e0d0803100302100509030a0212030c06070e030705040e0a1401020f040b041a030112080306040908030a0207060605090c0406 81
    0x203450760702d180c80b40d04080340002114010302d0000c0d1440d110211080c05141d20ba070605600310f07038460009514240b218030100d520310074002805054203502041015500402d5008100510340201c110351032292039040c08440070f10052001141036103000304000c1c1060042c03c0705411140501d0304481c803507183c060203607030094410102590140303d4060401c001442040554050482d424841d11014207600c10f200303e0031003c0000c20207025046c820740742550740c00502450401e030306231164011101c1e40c4d100503146004041000005001d2072003080103a41d80030282044204040301150b0020b95261306007c1141d42d82145107003c0d41003242040c01080031220700d242d103003400344001490303e41c01e0681440145c10a4000c0841050002820005c103400d40c107006001540c55044a865545030960000501980000080401380c0c0880010141d5980390b01841d1032a030421190780d5280742c04044400254403039031301221014681040424541401c00c0d01e01d114400945d0303036038075060800f5402d840c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 333202275 1250 333201025 333201031
    0x20a090c0531060302040807060c050708120d14130605130605011403070f05010e10140a0e0907031a0111010b030304080a0b090109080f160b0f011508090309010305 72
    0x2448010070040c03441c1400400d10751000900740c040018240c02e120044003206040380d004004142c0180002d00081e40041061401c41d51103003082150038100e441c1150400505500010041c000c0c0c5038200c48111010006101e900750900d4108080030030b50002d83c0d451041a10943c1141c4040700300e00e000140140d1004d500000746406081d5503e045036100713800d84030309811280c4003090b520306d180300d00c0c2010010000a0402c02400c3d1011600f840700081009040da100284034024030a040c540c060300959200c000c1400c14440550303101c0103004050714455410413018020071422000800c0310344a445a1114801402201240c0309105401110031030a4901510415540c552000d01a9a0100020002440260003401965038203040008507810024140b8500741d0410101c40e0006400c481210101c06820000544955080c00c00c00002285040000c1101803503c0a00240c10400c1c0c81440c125202c000310407640302c54181c000c07280b010064400d2a140c1d442808a10210b40c02600240c0d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 333203525 1250 333202275 333202277
    0x30207110904060b042a080402120708160603180305250b04030e0a0609060323090c0f04091a22030f0e0d050a03030e0f03040f08010501050d020a090c 66
    0x21035405000002900020107980c00c559071943ca4481500a0505001c0d02541c13640702c26091001040ea880b001008090f040407083c20080000c4c001811541d80d01c2824250010714002c545540d0b40303810300603503122a41c001e1a030310716121020014809100740142050800c10341e0802003101000c4d9000d0700d1580150b030908000c880d10401d44044d500b2158000c1400d113010307848503421400c2506000d403824448003000c40c0501d121290620405030031000f144e0464a0350b140000d03c5010758646420103100b00720344101c0c41d400c00018080000c0000980551210084030183d0440c018881003204a81d59a24010134104061000e102d10001516095034407000046414620f81d481205041c030a10780504100c000c2901c20b095543c91a604c4105490055030540380580f144c04180c071560b0792800e8000e0000c0070036885c0c011200c0c09410910500707040740755120442e0340b141d440342e281c540e44840600910445602e0803000213414900400103414094020b849190382c1424500070b8070181602040d124 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 333204775 1250 333203525 333203543
    0x3090c040e030910050d06080105060303041424030925061107120c1404052206060b0a031a030a0314360306281a130b01020f0312010303030207 63
    0x52801d403610240e0040101c4c2c0f0703944103552070340c41101d02800c8942941061403241e03d828104091500c0010032282074440c07106000303c0c1030411000188009410381c010070112003408000002c80301c542000303140200c10a0080c0c070740c00d003800712000c40c0c414951100c13490702001c10581002200d0055003502c5c890045142900d1001d6207500707020303044c070000c00300488c1e22400c00e8004204103608542104240001103509200c5810802450407003100da1b028200314001011030036804005490344003100800c081c05506d0b440304481103018004141d0100c44210081e2045681c0e115450701140016044e503242e112000c0050301c01c02c08140c9a007007081c7c1854035110500c9244070345155101c10018a0b0480301c1c1102019060700705040c10282c0251111940c0d413501403981320480c5060b034001e0700311074032050000398030307003c20f400030850001ca40b0f80c484d0809030900340c111501c0e030150044100741c40c00b0f800f162403612100c0c080607034034402c246e20b50010380c40e03d0005100080c442d030020007003580500c9840d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 333206025 1250 333204775 333204787
    0x20408030f27030c04050a0207051002030a06080a051507090e010b07020109050405070816050702091017070f150903081303020301051803160201030e15010f0b03090c040e03 76
    0x1a031859000a0340454050008208480c480d1001c2c52181c0c9030061106559180d45030402c042035030b4411802420b48213a444800003480e503000703070b81941d10040e00f00044601d902d030561215002540140c801d00c08942c1085404112124001012070015900c0802015440c1c81c081c015110707801d0181900080054002c0001000c0c0e4410f01414060400c0500c50342c0d903400c02c0c2c80098480e1030640d100c1e5014504010401c0710b4160410300c850350012000b100c4800180c201a0300322900d05c107400300258882185424005100001c1201c1e07403d03a1f1600114100c0304054002082c7d484070070388245550030351658410301c581e6402c03c548040104182c140300c000c0300d40b65034456030290442001c01c940449540b2041055203424050300f50000122084a0311508004d400e070f985a106401928186680c11107546045901c00d600940400e00e8180030b4a6401c10840090104403100b0b2050201d400f401b41c0010a0000307400007103c0c0914001e0004103441122001800040c0284601140c000e000a00132 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 333207275 1250 333206025 333206039
    0x100509030d0905040c0f081501110304030c030b0604020f0d0e01090c0303030f0b04060f090e030403020a0312080a0212010306150f060f0801080f07290406081504090b0601120204 78
    0x214210050207440d00b0740c80c2c50402090104035030312111148108202000092036080d00104020b81207521414040b2454443c200162420580c1410a01051100040000c00c0c4803811007c0c3e41035920980c0380a00e00e0b141d11003040140d018185640c9000b0710f041080102e50282d42e8849800c01703000c040041010400342c0c0b900411040290300075804a40c80d8134030802a01454440d10f1100d2008440030400b01d42452801400d4800301d000b044070141d41c456046204887c01c0040d140203580c0201500070a070b4071781c64411001103643d061400401c150b040407948500960080d516400c03601301007074000c0c0e8a03580310040903040070741007a080c1c9031091801060101034142c480001d400741da107681d040b8280a0b40004c0c050341c0140c0c0150032540007042701a01825000c00c002c411159801183c1e013403014280d04800001c0c800c016129594000000d0005141c0e0304103d003584140440c400000005801c8418002518210040180003808034030018082e9801100902d0022403424001420320780c40f060 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 333208525 1250 333207275 333207283
    0x50301140a050a050907270c1809021216030e0a050c0109050102030705101104080102280e0310110c071d010518010b0d020c061311030c010c0210050903 67
    0x188204903085001042120340d4503009140d001a00710318100483c0c03411062150b103500c030b41c4c0101610141409280c1c07a03401241d10303080d00c500302c542d081000803005200000d081c4401a02c2e160f40960442c1d040010054681d10917500d440c118040c160f0099a200824503204840c0c496043c401d055440407609030003002042242c0489106000034015008084009015110707640d125034110351080040710001140420240040d80c10700c0404211680b0140e03500545000c0ca41111910750b1010640800b60306544566484030744400e00704030703190040d00c881200d540344190890707034060703000d4105074140b194541d0100b03040d80c0030f0002407801c21005505003400c0064907841440c0c01d0a00c0103104010088500700c0600500c0700310b55450300d0000012880000440500c100c000340c5601003079410140c0300d50b404a8014061402c00c0d101685030035450075201d003440d0ba03030030b9503e82c8440c548002d041c01d00288404070700005840307202d5420603079820005640764100c00c10b01001800d00c034294003614100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 333209775 1250 333208525 333208541
    0xb0d0e010f06050a050a08030904050601090b070302010515060301060203160501060f080309040509160611070909050105090f0309060702270103121704030e010f200d02010e060903160606050301 85
    0x18a001c10340a00c0c0c102000b0300d250840c5c01852081c55401402c001c4048000308480a41e1010f80307000c211582c80c0303001070781c000c802c1d0b0f03002c0c3c0e80b010703400a507800400da410342c0b16038071030320341c0100d0b00407420aa1018040d450009014a40160303000300804100e0280150340010400e228000114075940c5450140704201c0055200d12070aa01c042002a400c1c40e282c000c013a0f1100d4120f00900c9140000d41710190b04071a2751254006001340d604c1207180129040c00f00320050107030b01500b0300880c5400e1030060300070241165980103a0140c08541d080c0b00b4004411100106030041015090120540800c1005014074a243d8003002c80a407608050f4803001c10800e00943c004c134411219000300002c044c0c00d10740c50b05030454001d0350207410040029080a120181c4040030701e0040d441200300d140507180c113014001141c4502591840e4800c0240300010801c00c03072015071780240101480d0500d415079031042a210f06200d5041440b5803180940c010381404100b502071003001c21000c3d614408030342103920745 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 333211025 1250 333209775 333209801
    0x10b04021605010b1e060304080405212b111e0123010e04060509030c011a1504030b01060c1506090203040605150a05011b1407060305011e0b0d0e01 65
    0x1081c00710341400001c0c440d40d4402c0b802590421108002c0f100612078102c44811102c0c800c1201002040c20b101c030306c5003690081c00014011b001e0352603001c0c0e2000010603103042200c5440c800e00c40c003040341940e015980c410030031240050695065040304240c03400d50707003408050780c0c42c801c01c61182e15004540180d181260322030303c000586111101002c040c81d41648036a864000c100c07a0041248046031801150700176000440000c0c581c4601d0041800c6201d0301005418070340c204510703208102540072a080b89540c040340c55500400c00f20594406901a5100150101586a0041006a0281014040c018440c1030790ba900b0b9145038003248111071a54210022142e408400c00c020413140e03100755074110313850507000c04900e4a100c000580c000101c4c05014100404200800a0b0b486d40c8007041640d00d0740211501403c000c42c0c1c4c0c5443e03845503103100b614002402c20000007142e011b030b1404141e010006890710704a15091581040584c1e100c2135841c22301c2a40e031136084060342028440c2040b800c4503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 333212275 1250 333211025 333211057
    0xc0f0602070b0f0d0f02070615061215051c0203030406050309060606070209070f11010908072904030f050d050a0c0e01030b060a031a0628021903050309010b0402 71
    0x900400074900440340d0000c0c04048020880c5100754000b0f0000d991013558a02d401007040240d0320403031406405000401017005080511141c258107200a9080540d000355403015820100d09413000240c41c0b040e05078101c04004d2031020700c0309041030006506a00303640e6080b6a40c41c11941d0209155910651040002500110500032480ea0911240303410020840c1d04505100045d0009100b101000d40003400780000c09a0404a03240141c94800926903090f00070000c43d43c141c144886d45502851007214844104400d80c04503000700200301401070f542e420101410b58666400741c03116240354101c40244202804403e6211129000b40c51180b10203060104005120b000c010344104070b11a0054145828914003410035107507030095075000700300c0b490b010401508503014020204240515203421035000603540100d41d20303495407400c03d10f805003203060302c1480c5041c0498846086450700c480150a000c004008a44a20041c580003202c10b0000920400142c00144c12a404018840c4e04095 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 333213525 1250 333212275 333212279
    0xd08030403170c07081b12040b13170319020312040c03120f0e0f040b04020d020307080c090609060a02010e07060f09090b0a030618050102070602040312050c0d0f0c0c0f 74
    0x400c1d41c0b40c0c020308031040690406505540303c40190140280d00108101c000321292400c14040100031500c51021002c036559030386690b0398511f2903024103840d240010745201e002849407200c3c009903600c01420703c082d500f000030304030780c045e44540e40c200c4440440c403007880b050040940b40c2c0d4000d40941d2003281e4001c2060301c1d52810101500003102c010741480406000071060641003032516609500c1100d5800c440050000060010803491035800d81040c17020400c488195000c0e40254010f4246444205c0c041c0d5408107040c00718419100c01541044007480401040c4c01c0c4030000c2c00c010311907400003003058418035201518000039540250000381540500085141c0c00800d90b101911080505000d011513520200340621890300c00280010b541d81c1d11807214078150381d518200c0c076900400070b546e80c0ca16400c5c0070f0065041801300b5500902c1030301c4900d140074003903070440b5029003801c005004000356035241960294420240031081c00b40030810030700002c01c0c85040c88090041a00701c2e005481c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 333214775 1250 333213525 333213557
    0x190f080d050f0a0503041b080a02090109020304020a36020322080414061603020c011103070b06100203070b0702030403020a05060a0813210518010206040506010e04150c0e0310060605090405060d08030403 89
    0x44bc040c2c2c000030030301d8810401e100c05a140c265121b0265140c036459409880c0d01c0c909503100c175078411264041002c1024005a108107415001107000b2001352504406000968990f000240303a0702030001d100120401c8200000c903071100c04142c02d90f400502850410b854000c5500400007000710441c0103801c8240002140d40c0c1000b580340d05c42101200541c148066503031940c017512809030900c0d01c03ea17000d13144030340c602c0c2c801c00443c3c2929520054002075401c0c0544080e5580e000ba0104a204a8041802048605082083d600070395990781c3c035071005440d0100340b1f03907280d1460b1078152030040c40380e0403058021701e0101030741d4110481642c83c03036a1030100a5420204c49000043e15046410031402c0c4008904001806c5042d1103441d6602d080701d8980e490801240035240d00048112414000c0c103111301030f000211032000d1a000d405441682141c1ca0b400ca0803200c290040d0f80c01f040e801c4c00078484138207007070348429488607000c3c01807221040c0d48d80344d456054004803000c60000d00880744082040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 333216025 1250 333214775 333214789
    0x2a0f0a030213140f0d1b2304050c0d0b0a0906080a15061a210f010e1608071805090a05100603021206010c02190f080d050f0a0503041b080a02 62
    0xe111800c000c0fa11042c2000016901041d4444854490004100c58000340940004a404109a40410285180c0c0e4402d070340c402a008000c0c119803601c0c1c1c0200c0311206400c16000320381c4100d4146007143c0c5030411901c242c40c000c4c2144000b00360844400400414450950320414018044100060858000d02d180500318801a00b55022b0a182000e404001081105c103480711003c9500700440d0700e4810f4611840301c0f01284126111606001034103001969508583c801d05a070188000301840780e4a05200081039048408000000303032a134400541c1c1c617486203c04107640c1c600d0320b00d17007080540c6d2140001c94a80040e19004041c2e5920010f010391025200004c0e4010300250409504084003a41107000407200208510705102e51011040115911000c141d50b511948030500c040c45034072040381c2c240d40e40150184a9040c4100f0b100c0d400c1d401d01036001e641108508030801c0b882c01620b0001200c0d183c2000c2c1007225104060903903106c65616654409000e843c64000800768641c00c2d004000305 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 333217275 1250 333216025 333216029
    0x50405280b2706040501140f0304060c140702010804080a05040914150306010803030403031d030711030c0f0d0602070c1511010f0c0c1101110d020f12032a0f0a030213 73
    0x214024a01e02242e240c58010658040760000d0a0100441000d42c41421852043ca591801c85240000c05c100401c443c0e5841041c2ca51501ea82d000c0744604210039000359031154481c040d0103e080e00c00018001544000101020340380e9261880c2450768404500042d1620040180041701180040005184200010703400c105004c5004010325498088465140d20003c0e2000d402c043c1c072209401e10300c4254507480342e1213507421011a40d40e854a4281402005000001c00740309008004601700e0a1a12000c080080c00c80141441011039043c0c0d40d6200135441214101c581c04008000040c180780d03580b00c800148484d644075403035030080741c15409003107134100054045001e1805c44420b02c8160b0103c070480c030b003e5111051070700d204600401a584402009441c0350a840748010704500c2945c0030032204800354001c41150703814201000c1241d03203400201d80744880c20042e1000741c1c02e00300100d112981542c0900c1d0607107260105090318042c1d10790007664424042500000d03041c541c64030b08070308000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 333218525 1250 333217275 333217327
    0xb09330406090e16210501090b01081b09090714041b0f030c090f06120b03100e01060b0c0607081b0d23010321021006030b0709060807050405280b 64
    0x1851401c1103090791800c00c1740310341c407003251a044030540100035003503200d410740c550424581102507039142e03041d56483e0322081500000c0f5040e001d020409041904000d0300448842015180460400d4060301000e0002001e04c0d174011b4541e01c400f0f100c50031072645652050050390707940d03180e000781a03005416101d0429241080180340c0b1010804004134111803820b4036401c1c03900009042c8401101c01c00b0700740c1012002d6040c040d07030f20800081c0000390f0103045204903080c024008255114103622107405103023034640043d040000099946c41c400d4001b0366100e605440c03034240101e11f4200d103408540003000c0040340980c0c0da5070360240d084510400d485c011030100220150f150b0456959001d1400ca500b00b5400102e40340007110003080c028800036000001004c0108442542c0b4142011403202c1500d800f0007091100d0000720700e40d4402c0100354841c00c40c546443e8600340ca0101406280010510150700d61490100c00e007803441c1e28122914003c214440ca490707107990800349003c1c841e04035030503012 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 333219775 1250 333218525 333218563
    0x306100206013b070905120105010b040b0c070807030b04020108010e091c03060b030415050106020d05071e230f030a02070e090c0d05010f0b09330406090e 68
    0x410120f1084001112840c01c407000703125001c12014050861180c00400300303444869100704030101780d205004604136201101c84100800744150329034202c038400e0250398040ca038108414040462228010440780c40307500c0441e10700d42e50301c41c2054184500c0390011910110520305102c02e40d039111407890f01521528180b4903060909204c40e42d0f03100d074260110114076500004900613103010342d100200070140c11000a80c0d07442c140c80c2000c050140116800e10403440c5c60004a9843d01c0002c01c1054240030b912428680311054490960840b002c07171580c0c1d02203821b20480b800160080090344014455056014030781c50304504d0450506004a424070403580c02840b000c034100c0e5000035280121490011050900c2d280d03e84020f00b00640c96080503080841c8031240b0341001415405540207050b0383c50100000c80c0800200440c03140f0a17204c82d04d25089420200d8245030340d040014031440e4100b0007502e9046032a00100c1d05403000da42c454114103950b15034030901e500080c0041202e141d0044000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 333221025 1250 333219775 333219779
    0x103050c0a080402011d0a06020f061e0109090503070204060b07140d05070809150f070c05150f160b19060b0702092703070b010602100903021b0d0c0308030610020601 73
    0x7015042c00800c068100140040c819410070320700c0c0f11902c0f5001000d001c030f80030207458590195413500b154504030031324070601001400a1043e85070740a81072850922514103179180102d9840a010a850191001c3c0000c0008a005030340b90301c01e40e270040000940c0360380c96099034144055030000b1100308821b5900150440d00c00b40d5809011605800d40c0030120030340f281ea044010034242e010004c403002105400180b004011103005021f04400362003031076204425520f445c1400b0901310030040c0340401400500110b526030380500302400021011551001c1107103042d8450000380315055421400e46402162042c4100c03c1c0c0313001b400003401e40c8000b0720346007115a50108100c01801070506040344860304004c0743c1800c084070090886540c100480e620b9041504246403143c4003072049101500c66041c050120800c2c0d4019030401c95016000390070a80c0c00d041d40e882140200d050450b1f84550040001400101c803111361002460107824404c1e20391a00300140104100344d03000f00d005542c040401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 333222275 1250 333221025 333221027
    0x1020a03060512070b0301120807060504030203070209070201060803030f04060e070f05030706080f01120201110105070503070e1f0509040617030307030b0a03050c060d110703020a0215040303170c0408030c07050103050c0a 97
    0x6c0f20f0441c0d02d80c0599448004413030070900d100d400f48000040030385003000c0501050660000c060a0403034000c445000f92038840312000d9089803510b200b120415007003800010920508180d501c0ea109001d00e0011400302c03400c03400e03641000d2040e04034000840e0142003d22090804000a43c0645058145031000c0d0410200d03041d69204140701da031520814903031a4004692003504036460036012035000744090308003040060000c0c1c00456100c0d0008003031510003c12450302413006c1c3c1c4881041c0c49610084819400100ca85030300030b40c489034200703440d000c0c0000d034611501c0780c82d400c1a194a000e99100e05060310010260ba001c00540c0748190481d100c02d00c04620049480200c0130b008843c010b03038a04241201c0c5016241c500e64002550340003160840505801103041c0d01aa4401c8620302000f0000010391091400745000140014849a407100c05901407141c2071604078154018190a20750345141c00c030314603030146112030390642008904006558050107030307039000707410000058102800244 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 333223525 1250 333222275 333222277
    0x1f140105040b0a020f03040b030405011a090406051510020307050106090902100f09032103050703270f020d080a11190204090f0b01060306030b182d01020a03060512070b 74
    0x81c2840c1081d0025114803001d00070026403020740c01710020749072600e82c0c03441c0c12400c0707420480e030036510365090040c6115014000410b040c00c840e4012300c140d000b40c85945603c401000010301f6100072240441c00382c1d4966807946003480381d000d016401142d51700141c1c40c00900b504c5099006600c52410001c8030401a603917801221001c0515180800101100000032603251005038006440110325031a442c85d404040b540b9172036500c0d8192003e204903202c0100450031607807140400004031211400c02c3c0e6058010b01b6580311904d02402d60781048910700d800141031590541c2040390408800038142c0505034100c842c1442010110010309140010740f80f00b6400c054034441e00074442c1d070381c1c0c08026041064540c5015540c43e00102c0c030b048113603117844001c2c0080080c2d01083c0c0f09840520002454802e4400e091410044100c01a001c0c0003241142416420294294807960300e002c00f80503508008248094100980d540da0089402c515020a2040c0c0c540c409841c04180d4012030010700074a600c400c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 333224775 1250 333223525 333223529
    0x1091a04120f0e1003020a021c1b0302071502060103120f09180213151206081e0a1208180d02120d0f050a050a0506220b0a030b1f14010504 61
    0x428010380610300700e8811220504000f80c11070f480240c035064640c1e00d560540c043d000d40e6a154081750300b03207070301c0510901c1c440318200d42c02c60008902c800c031a010b2003043e90000c4240da1003401290b0815071144c5480d0f800d17440c1050403500503840140104184008194000342082ea85e041c00751412071958070062000703003076019400000c2c840101d142c070008080ea04030780701800e8a260401c2ca0985a0991101c0c180031502d8800001d50300c1010340c03440d450207101d0b40b0211607071000201b407850441c01d2031089048500b0840030050164050481c089040303100d0302218000a0b94a18230705241140c2e84040002203003480c0d4100350b0180b4a45080d440e00014403c4042d02c101c0d402503207031055008a000500f8010115403429420304051040c01c0e0701c00d0b08250b00070404180305100d1960340c0c070248100c5035aa4410500d6100c04000c1c84130107004140e02c01c00d42e0980c003030401c0d440e29480351a0001d00380b07000c0c3c94900300f80030200300d81c00380310036100042d002034401c000365024605030381800240755008078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 333226025 1250 333224775 333224777
    0x150d20030103030c12170a1508120403060905070e09010b090a0c0203070b04110628020a030207030b04030c021512060415030318080129010804120302090d1401091a0412 74
    0x11710b110400781d4002c1d8010030b5032518100f40703003400380343c07005c003a02c06050f80090f9982a0001c084c0045100400450f001c0d0700241c840d00c0c8142040e00c1c40e120240504032080b020f403554000e607800400c115104500300ba10944040f00041050384032141440708841c40100303c4030710185410003a49825601200701c0340016080050f400040d103550030022072208a82110b56440880010031074a20424000c000c0b082003080c2d80100e07800f0511700001d9072191080d0000400503040f903c800d0000440345241d0a411600034075003400e03001102e80c04100407020b45405900b0a05011640c0c00d140c517100c8281503446042998284807079032411520300114109400000e09000441802e010703050910081e003002000d11070700a2001c4074141c202d44403140c1c4000c1440e040c9003a031030340c910055409048503a0040c6d6020305103840c0d203d442d0300110000c0d00684175484d4450840402a804a44011450311020700c0701800003c00c1001440c01240d200c904117407503031400c01e0300d90421020828004000c0c03444034603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 333227275 1250 333226025 333226043
    0x10c02090f0601120c020d0212041203050307021f02030916081009080d0501060c050706140306150918150a030f02040504230a0201090801021201090b150d20030103030c 74
    0x81c0c2c10041e00c1c1c00c805482610320785032800000380071540c0c0c00901c016901c0b50a4099a1009100504142c451310603405040c411007440098240024401c60045a0002e01403040d103500800840e848018440c03088142c01200741c01105010b0201814005809510328240e0404902443c00880030340310b420403400003501990740c140d184e05201e078071011245003600f00e40041003190385a40000d000b00443c90004d036941e10407001c000c29035900500150414008201f503450850380d0742000c00c000031040880c0c1c03084855041c8003880584c2c803500e2240400c007107858218285032074000c4410115000106011f0301c05d500d070b5041080400e460603013190003550142c2c0d002c1942c0e5140d061405002d10b45c040003c00b0581c600451150316170f0080780168100d4400d90f185c04003143d940804e41d00380d020b010032214490741c0c60001004175050541c005001c403e80a40720310784d020011180e680440e00706641a403442d40d150740d21001d0f0405401407004e20018894002e07800c0d541161002440c6070000c160017000028 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 333228525 1250 333227275 333227281
    0x4140f100c0201091a0a18030504052407030e0913080403020f010504051201020405010e040516080604061d0405070906030507031b09020307050c06090706050a030f020903190c05010c02090f 83
    0x2100b0b411407a1138a400480704c400142014030354141040302180c030400120302c0d02110b00141c50800b0200440c4941550710242424181810840e009040b1250600402400c00c2004040030f650030113401150b000342c07103100a4038841c2d410700c00350440c020700540c4280703c1080000b00080c5d0410540d000d803074040d5091705d1a00680d500594103403282d500082c1e4056106240e030600c140e01500207000780e4200703903103001340c00e94201c1c10300c000c3d5101541d41010846c0700e0400c03084203511811400d94480001840401d0031665036043c0134942e5800d010000f400da910004200c00c0c0b000400c20031009010343e000401805155071143c40e20b941250100034900d00700700c11541408a41d02d10a4400741c441c2000031552401e0150001d04607900072070141807035025002c0041d42514000c03c0c140201c0f211500c0c0c90385444509441103005151400c00015119828040f91080391810400c00342c00705a0010038844907102070410307292070301d034582c850790400548040503001600c460581e03580040c2d81010100a6407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 333229775 1250 333228525 333228527
    0x601020c1e03010605030f0d0f0e0609010c0512031e0117071e0810020904150501140a09030f03081e070c0f061404060501090b060403200120030304140f100c 69
    0x300c2d9005e00d82c14481d00d000304c6100707000400c0155074907a00380c47d0340b0ba00803a1038200380e9003614580341d00e40e804503050000240ca940141004120b10b4403490a035552051150328607002c5810a40e200c8034071101002c550fa500d542411842405086101c3c8c164416903204140b03607658034000e000b411040e84000c640c02c4000040c14494034090508802030310000312052400300c00941086071428861820001c000a07a041c1981128007a2041a074450100d080d05840064080d84100c00301000c02c110a6400400710300442c140c80c55040c400e980c2ca1102e03090403420450f5021208103403a0701d615213a01403110b4190412010000d16a01481c10602d41d22242490b5009200c54060707480650b0a0800700000c00406a11550580300300010070000c0240c100c042c440076000c1c5c1e004c001c0480040d80078101c241034040f225550b803000c0c1454044050710030364401103a5101e01684807175888e800031090000304031700307946118201c81501000b40030101141c040c10707030b562002840c80c1b4021941e130f0f80410221 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 333231025 1250 333229775 333229781
    0xf030e030415140f0310050f0f150706050103140111030f060f01261b040302060f0912070303022b0512180307030c0b0105010306030b04060c03021c140601020c1e0301 73
    0xf14070700b80125190507803a000241d01d40d00454640c14030801001d808111440c02c005104161400034059103215502c0005200c0403116080e840200801c051040310700240c40d60282d107010310711990440000c00c8001e2286400d552024181c10585c07401881001030440240351001d51041c01254040509460f00c00182c8000c10324091503070520f90348600c014100d01150550322702620b01c0303000d0900800a034841e2003685000b103000c0203511040c100811085922010f01400810f00d000b0694078560072204007151910421707920440268200492400c4040d4107044c01c0f0315072a00c0310882d60b80d0747d109e400d0018068400c5040c00c01c0c6041145002c5207109880c00350f80c0240c5001902160303039030481410054600e004590302103814485c550004580c952003030003280d0840b9072100b00c5c0303078054a403556942c01038a14444100300b0185c0c2449210302d82070510610304150a079080001800207485061080000c01c0146441c5c10f651282d01c0b82c0d11152188010780540c50896241e2444040306000001c2c09 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 333232275 1250 333231025 333231047
    0x61205030a210c0e030c0909070506071e0c170105100306020304060912050409050a020a0203070807050c090f0105180408090d0c051216080118151e0c0f030e030415 72
    0x803450841c0743c0a1441e000020b1450312007045003250100c0c454441089078108044030918415007102004110b1400d108000d02006441b0b44100388810510400140c03203000e80d0b010559030898068802c10008584d0a4000e0b609003000c3d0007071002e07141a012000035001e00d0710009100c0b07540000007805018082c0e200b21081d90780203520b0b0141c0740f0041c1c80104260003a008a5044625250108400042d244200c070862161074000c0e5040c102c0e6511000300304c0e00000300641c0c690042d10b440c2c0290b680c6203d1042e01c107407000d820084065052030309010309010069031410052484a0034071000c03440c40002e84510500407501080d14003143e02e4003034008003a95000d07540140a03001c055042c0305020600e5541795103440620403840e541c40c06090300b0386e0070390402c094003030740000d001c1408504076030fa40003005560100c000c590080c2c0115905101c0b1100c880303041103d66038601040415900801640b000e07517081c601806007242010916407284103034451140202c0c51a08000e05290083c420944 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 333233525 1250 333232275 333232337
    0x607050d1806050a0b01050c061b04030501150f0602241b0706050901050f1006050307140a090303080106050a050301290d2c101a060715061205030a 65
    0x7880c0507a40c0b4140300980420350303900781801d080c22946442c3d54818000c0c0c50169081c2c1d00204100d44507104025442d0b51003840744100310360100000b0010071401d01034000c203107128030181c003001c3e0318141144002d0205a0041021500300c0d40c02034070181c4000842c14800c0d11541a81c04075030b202c19406104c4111030803220151a00007142c0427050211a900040c400c0e10080000d2040356166a45071002400031650005108405071050082520810140d6440080c505200c0c0040380005988881a00568858400190110700a00c00c055100241500500003800d00302d0426082e203201034101d00050040c0460300b5414541c030303a4101084252071019100c0992100d964004e026188000303000301c04274030b40e40d450740e0342d081ea46c1c103038440c0300c2080b03c00c007820740503042584203001010003801c0c040d5034040040c00c0542640803142d58880c020f000242c41120074210074051041c100095466681c0400110482919100040380002c4201d81c003041c11444c2900d06480c03803030200c54124a00d858085 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 333234775 1250 333233525 333233561
    0xc0b15060c0f010902090603070312030203060a051e03100e0309040b060708070c1508060f0d030314070309110904020d120c0b010311040e0c060d090c03021009060f09080607050d 78
    0x1002c9410103500000c0501e0080d40d602400b070307480e030b42856501e0160f880010710310403a040500913007920940c082e6801134070082c5070594180d980d00020300c110138415014044150041c030f902c0b43d203280410400a4141041e4018090a81e4851245031a8040c0c0130f4200c0c0500d4a42d50b0844050b51074000300c490301036020b01c0e00d545810780c900340f400c000d00c802d014180c00c0048103607113015420700500c2c3c0329106241c020400800110040c0620500d40c06c016001c4080c50385030710012070043c40c0c120341036114105c6c40d80e0002d00b450403130603c000210702043c0041d00800c1a0b9060102588909070b800c400f07181c10103901240b800515000f00c40c461401d21001d0100f106543c004020084900e007007540b011000c54051040010a00040b51100b8002c01c2c940d0703109004010302a400b078081c0e08012116802800c2505085999030049100000950100800124100024409a60030450750010043d440c0341c1140140d080040d41d03952120080d0144060240100341c91020489980146c402030311183c40e00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 333236025 1250 333234775 333234793
    0x61e030f0106170709090c05150c01050117160e04170d0e030d060819020f01030b130b040e120d02030c0702040c02010b01120b0f0f031612020306070c0b15060c 70
    0x1031180b015407400300502a020b44d560004d90048140502918140c1000344038034540e00d080d0806c01c081e035030b94030020a110070500800381a10300a101e03040c000d11400102c1c0421082034503400b41020455540341201000c2e42201f8001d510020761510390140c3c2c8400c041d00c0c4000010f40d51402070080200315602c1e40d00340070452182020200c00350150900080c0c1c14442c0c503460b0202152074141038403484d40d0200300b0448480144c90445951041003c040c140000e007500d583d804030b80d1040b050390101908a880b83c14404150800c0c0c4109042c4207844000303010202011481080c440c410074100754641178000c00880c400ba10307800b0031942e140364010802c0000c80301c0c03854060702800802400c140802d10100500080c400240030b20800d80c00e0007002c1c043c1c20500181001858044001e150b40c04d407084a0110401c0e601190804016004109035080510603510405161137402004002040f804482103400608086034541c1c22007600310301c2c10480250000840d045020320014003a042c4541414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 333237275 1250 333236025 333236039
    0x806130503040e0903210105100332180307030c0f0302011409060a050108031617070b041b060302090a0509061f09060305010b0a0203030103080307030221010608070206061e030f0106 80
    0xa046c10169086601d61403105070680315030b094400d100d905c0d0020b20b0407280381c400c1446540f0203440350490055041502c0c00d591134100d401c182e50340005501021a0b4280450000901112078508115500961400402c0d0f80c004010312028030b170003060f0221401110741014001e40003031089402c0c00c40070021520b00050100c0d41c44100f6079019000504c0d240002c00c0d400b01c0031080b42d0521800b03da5990520900307035528001c80c141c0044584134640144041c1c40020881c014880c0540e003e01051a460000101e8449414040b03a2065051510401500d01d41e51205841138080340c00856900c5856034030140412403900c0310394221081d680402d5140d4090341d80225261081d6001642c081041c1d0fa2102c0000d4281c3c8100e809042c09680b05000420000d800c1d88000c681c014070390f14001d4205030702c44031682e80140d10700050241320711458005118056102407400e030310409078802400f00d424400d01141c0302d400d10304070f840d054410111402d4420344007088281202c00c1058000c01c481a52040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 333238525 1250 333237275 333237277
    0x160b09120705060f031602010c08012d0303031e0b01090302150706050903040f0b03010506070b130c080303010501030f021612020f100e0f12030a0b0a03020907091a040806130503040e0903 82
    0xaa62000d081b0510310994287c0c414403845040f01600e0b100d000e003990808501c9049482108000d15450f40700d0410646200c0d0f002c00c001000394130036100070400e026456003d010241c4001001c4a1052030140303503640e01c1c0c0c0e1089564003102d4042e29401d030506070020540d041d0340b14100028143c14248424009003031400030042048502481140310000d448001741d03041480700b84a02030b40720400303001c0712022440000c1090b400140b00c040c1c020f00405160740701c0d010159540c0c0606040d80001c0010022560580900c40000120420851030601e518400c0b16011407205006010102c1209081414600800c5002c2138445190100c071500703182e640030400074211011180e541401500c41440300c0e90000280141d6500340b050145096940c0c0b105001c00401c00004110350101c0070038000000340e200c1d024400c1c0a030400b41da821714441c0c1000c03040b4000c40513011042400c904100401c0008000208029400c000308400424170f0802506240340380d03008a41204050010001c02e00c801000004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 333239775 1250 333238525 333238531
    0x209030a0308090d0509031b0a031a01090f05160e061303050c10022a0d06050103061d070b040302061e0f071502040f0618090e0a0302160b09120705060f03 68
    0x8000c0724804c800e4a0707000c4400780514030403281c00d41c1c404001c40101c1070361601450030400001c0c02d4a024180d59445405590781600b180c09080c0e4892801449a070050f40500c070020b1100340b8042c469403d1075000d500d1050140e056050070400c543c40d0f00c0c0600d544200450354228a61070226a8058407400c00903212800201d546200c0e01101036590101800811001c2000e80c002c00c51152268480015a4580a0715042983d1241e034403088240060000c2c4502406980286400103001c81c03881c18403020b80407500040b28080e40211020426010307000100e60989506139241d54640b0380c032021907092188480f010840000f0003003903481540c5114009080f0040c081c004d0ba43c01d2001c0d141c909001c0b44128041c2c5c40d0512040d820038080e943c002c0070748200c8000740c2c0113683c13212962284014119417039040400000e4103d00b804005041d03040244242e1642000c00920100749460190301c41803285d44c40c0035028119401000510a00911404000740000b805240c0e07641000c210782000c5600071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 333241025 1250 333239775 333239791
    0x204021b030415030e0a08040b07060e0303042114030705090a0f0b0306012d0518090a0618050f0f09210409050f1915030c0305030912030a0c03120209030a0308 70
    0x11112040e018880046ea406c451034004041c81e2819041810403001a445070000390b545d140c690440d5503c04008000031031060b8040c10035084600c4200b00c0109004c2d1080c851001085000003062080c0005a4102c035003210003814000d996030031000200d004000103500c80d02c4d58910401000810310906002076104400903a070b03c214105141d03424005100071045102c00c00b0340c0c02c180f8030000ba070040300102640346c8000c3d640052014424005154410100c1b000f2910030b440f1141003001403048141e8840c160b150341d5043c0310764900b00328907a400e01130051407841c1e8868071101140e00c482c0c040c84000f61460180d580d290011150b4107009142c1e0f4414414503000c9442e000004500d0240c0c04c000038080c00e840c400c50410b2411701ca039a41c002d0203221503629800480c074400000001e07441990702d802144540c0186846111341403c00c1019580c416840c4400d030410010b20454a0340040a90b595507810300700001c1e801c8007400108028002d200d4a142c03d44034140720303201032640082d0311520600300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 333242275 1250 333241025 333241031
    0x8100e1602011d0307020f060d1b080c1204060c09080604062909190204050a08010e0d0c0314031902030903030610051306110c060708070507050f0d0204021b03041503 73
    0x10907400c296214034003103d8014030b038009100201c0145007403005041810b40c0100014100504c160342c0400715000c03c1c980000143c0c041c0e02006043c1d801c000b41d02e40c486000300906061050081800e814800b0040000f041c190b500c02000550ba8083c0340c03080c001c1d280b0102240c1c110300d440d02e000c3e00241407008003444038290100e01e084408a00071f584034500348000e044a18251030340300e070120455080d040408034258080c08042140e4440008450041103a42e002050004c0030b8003206042000140440301003380c0ca40c42c1401280c0c12403a040391020441d002c081c1d036030b0b83e04500c000510f290129241d0403e80000107100c52850300001550080e40100c6130071070824100402541c8501c00c117480c504072401c1e60356007002010b000d030410441451548054602609032000041c0b00359110034000c8a0100d00464802c0a11500f0070030740000c1d2005681c5111103821034000650309100b05680203214540002e41180f1a40150031904da0f10b10000080f00c0d1a10303110141d0300020550502d0b040c0001c0c0c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 333243525 1250 333242275 333242291
    0xc04030c0b040b0f2b0f0501120203060c0307050d0507030b12011e0c0210020408060403110d021e0a0605040b1906050d060207021c0b04110315060108100e160201 71
    0x6a0308201ca044502c0f800c8154a4240ca5006070601c1d5000455415044080e40741e030303150b80c0d2a040d40550b80805407200005225186150000c1c201c40c41a0030019221003c00000d1005860010f42c180c1c000e20704801e125201e070b46103d01114288110124550f840d414041070000940e0140c000030ba0210048900d207202c1300c06a40c5d030501f00c403041c84050481241d1442c0781d01601710243e0085a07880043e20584602104c00d101c9502a43e01c40e91110030399a1044040205150b4002d0945c5e103154441e0780902841442041c0081d5520956400785000e46c000711881d214401d000c001c0001820783c012010701140c509410440c00c58101154072103003a9620352601c45c91403c80741b1640c030558070000d200a00c0c106440d25454020b411051081b40c01c41c0b50303441c5181400f9440d00800403101d10400000c803041c80e0900d45608013060110245019520070240071040c20014034240b50f0003107080c80d107101030341e079801c40c4504201e0561b8801c42c030616a56043c04140981d0703000c0d0703a42c44d034141d400a1180c80 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 333244775 1250 333243525 333243539
    0x131e0b010507030915050d050108030309160602060106050a091d070806040b030604080d021e07060f060501080604090602040b1b0d08010501090e09070b0a0c0c050103230c120c04030c 80
    0x1200b05080240000c8440c1d009200500145015002c041440d2408078200319014080d101213a03000c1c0c00c02c003d26440442008210790781040440f000b06540d21855003407926200b00030390348078010302a81003805000309100c0c185074407440101340241222a1015803032814058640920681562118001940000099040e08160207250602d90014004000355034890700c421190b43c0001640722441030f000c021600da801800c80c40c1603141c0300c1d490342d01a84c5040c0c80c9850f07003c45804810601841c1d090039801c00481c1c0e00000b00d0b591114007500d01107807414503490084002d10441d0407288000c040420341c0d002002100000e054030301850b000b21180054401e0050fa0352640c02d10861b800564041c0f01840144100d4014a42011500040701c070003a0311045401640c0d0000001c41002460000b04070303040c03000c20f002c20070007800c0a003410400d105040e42449c00c05050302c1c03152400000d644d030220348500814012544101501c440740b0025041100814035903901c6440190754003201c02c20041811 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 333246025 1250 333244775 333244777
    0x100905100603050405031603090e0a061512091b053f0313060c020918030a0e030304030c09051e0124020118051c03060b070f02131e0b0105 61
    0xa1245516800301561511800b1000340900030012541c07804148907503c5038001c00e0b4010781010344252280c0034424289400072500c25401824181c61908001c01000304040d00d49019400054628103058068404140744c0c0252802c010001d10310904c1503910107599811202c05810780d02c0859079141c00001d000a18040c02e0004401c61900c1c28032911150141ca15007102026860088000c0e03909200180308145941095035002030082580038a0302000c51134200707007030707680000b06032841d4020b24049803855a0724007a850400090104403562000030740d0742002030f240216402001035241584500c9800040c0030150b0b0540c841d101045403020183c0b150900d224143c6100c1c076800c0842d5040e40b02ca44183e612094080c0c1c0c03c0d556502140350020040c1400080700900a00c0140074441072611200d80384000d446030b00c801c051504400f401203c201400325900030307410029055a042c0b075400001d0b104500700841c212100e140c074401e02c1c0c40c020303501704542281c5e660b81410402403c2103801900c1e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 333247275 1250 333246025 333246031
    0x905040e06010b0a170c07231b0103061e08010c0c0b06040f0b04051303020f0703020604030803040512180a060c023d090305011b0807030b1302070b100905 68
    0xd80d001000180300400c009005040c0030145441c2a01c441c5002145400341d051003514082010132000a15005100301e07a003602c0c801c2206c000702d02110764041c4030036503212141901c0000700f1449a80018082c0da12076089500945140b000c2c4407192941810305c0414180c9030320a202c100c2d400d2540240301c10b800b4041c0005400d40081850f21181d89500800004080e1109504082a07549207442203a80300ca00c1044c0c4180807813551030500c0091810040c0c5000441411a452544030000a00042c1c4030002500c00f10f80c0e00c042b01b40c0c0c49403540e1500c6414946008440e416103a0040361482d0301070700c8600d00c3c00e1300d4903040d11010f17081038807514212034000c18140040c2d000304004201d813a20b24030416506e03004c003000d0040d40151400040e00081d1a04032200390070b0000e004800e0920a0042c2840380b814000302d10740310000504042100582101d0300104107005065643d0040580d54a6400f404c00d070101040394115036400c03c510b800c400c0c0780402c1e90645005400020085000b544912607240 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 333248525 1250 333247275 333247301
    0x615050a080114030703170307120204051c0614250e0109150c02041d07050306010509180106120f0b070206060303040909020102030904020d061802030f07030e0f0a060b01090504 78
    0x907482c0e090078000300c00c1c031408a9207650035210f0100000042910b07610050841c0303c5111140f0b96038181a6002400c00f001130301c0010005d88100001c00c900d80d42c3e607400b0140c11040c0a8603c0902034941003010042c8001c140a8140018a100b0003804800c80300100c05001c0381190110010204407070102c5409006183c0b89002c00c3d10000c0c00e011004034500d031070001c4d10040c074040000107650b41c00f050507070700040e071300d5411245040102001050188000c2014002c02e038000c08040d0725110010300c448a01131b05841c6030140003544218008002c0d004480035059403540c00840558502d0902c0003114111800c1e0784000d034540c086103140d0320108425004143c004c0003142010f040002060040881791070481c15403004001d681c0b910303100e038009000141307480c1c1c0300000c21070300e04141024440181c0c1542ca0803184104204107041c4000003041c3d0704000a45030004050004c0c1c1c50303039450f121109803000c000c1e104040c0d40070200300c1c01e40c2240d180f900c42039a800e441581d032101440180e82c10201540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 333249775 1250 333248525 333248537
    0x302060a060e3616050d0807030305040f2f030a050607080901181109011509140d0609050a050c01020a02031c0203040b0a0203041d15041e020d0615050a 67
    0xc141c1d48005109024144400c503000a00b002c1e208400402c3c0d01992402c40455000b564010b90b514088858140080034240c594682921840c0d4480442d88961a401414542d03200041024441d16000328040c80364000d012405a5410f0103e00c8070b6035010050001c948040d109001ca040e040120318003840ea0b9000004054680300c100056905010041540e0415075840942c4020707c030242040c8079080d80a10103131040b160000050061210050708150080c0070703490901406282e100780c503c0b01f190601550000c09020200000d150503e820308080c000504003181d40d0203200002c68100c0c44c0e03602c83e50489076459524001661512080080698036401034036000d0620030074901c00c1803002c00fa030b01c1a280741c9a110141c1d620942c1107242400b0060b400450f061100243e0102a071500c1c490750f41c070551315450441c0800301000108200c090003a501ca602191080e41c2902048566503c0c0c9101551544130106e9024000e02091141c0b5918000910428070418001c1301200c035043d0443d9580 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 333251025 1250 333249775 333249781
    0x120c04030f03030b01050c1f0f0605031002070206070213020909011a0711030a0c031208070c110409050a06060b0a08060f0a17030c01050708010e10210807020306130302060a060e 78
    0x550051503070b00421410b003c8100003200b02c81f2018096940140b20319054244010302c8401c1d44012240c00c4022014000d103442c400340000e5400058580710206c180402517541d1f0110b101094040c0205607000b9003042c813840c44a1589030003034015211480c01035408500a83c1e80316a511450200c0c80c40148050b4010001000481c5100d41c070b08000a00113402c9503440b00d0346540d0a600b040240c1e10031f852041d10012141c41c01640007403101d410611601d013040324401251601c0d82000d80d51126035200f5030b5121168170411200b440b403000f813660091010040d0035600c100352440c0f64840c00444000515080c005041c0c1c1c9018402404410f60160001a0760383c140908240803440d03250002c601c500c014072401082e00002d00581d449402242c1d503500c01540b400c0c0c4200c030741c450068144084500c101d4002d204d01c4984d07030b0381d100416034000600c228142250070013295910030100003a406001d204100090002260002020180b00380c0c01c803496503a030384091208490780d0b406010a460001008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 333252275 1250 333251025 333251027
    0x301050414070e0f04200a1b05060c072102010b0f01030203010e0406020a050f03100906060c12080c07020a1401081311010f0509120c010f05070b1306060b040803120c04030f03 77
    0x802280000e803000803820a01c1120506e00ba5484200d101107000018540c1d400d03d61200515140801d0340c81104842122980c4140d2150380042150f01818408036440302030181e151060b80600c40c6008400c5000c80407000020301074100302514501806c0c0d0109030502651080c42224100c44d040700700940d142d1115038800300a58060a4410300f00002403108041e400b40100c0154011069149181801403500040c0400c0d940f103503000d9400c0c08202895500403d03c414090b00c0050294544105241e03503150040b10f080c0208000a508120307412404104800042034011080720300b41c0702c0200300d5550380110a072110700c0040003802282c03860b8050b00345500500c50980c1c2c0481c1418450b0070141c0e44004101110400d002030091540603100004e01960055129103a5000701e1410324604095907c4501c1c2220010340320300c01d040158020402408483e034862000b5102d101e0b0340c1d81d91180d8a0841300d94036004038081c000c08620380d5000c00c22040030b1400700e404599120400130810700b03160318 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 333253525 1250 333252275 333252289
    0xb07020f1b0105091302120c070308270d08010806010b070302100507120e06040605060102010c0905190506041d161706130c02010c0215010501020a15090501110301050414070e 77
    0x21201d418444140240c0341c1130f07503d592070022640a0104c0058442d1030b40110f0540341c2401030801240ca02e4108403e1010941c041201c961000c08030101071041503251503128444460103038640100d0203000000800035034048001c5040b5400c03002107459990300c03803240c884181701e00d0794010056800113425032400009034215507400b500c981011078074035040b04007020680c0d00d004c1c0c1a0010360000010881001b170184540c50704064284000c20981c40c3d00381004d4081c5e141030142c5c0c0d10842400c0d40340c04a01c2540d0001c031000e08009000e0a44450303446003800100042440141001898140010021882541103541e840400d41d43c140555240840008403401d000c0d041982218400350782004155260240b60b41905d01070340009000b10b18940000c0c2403180c4580d0b180703408101c3d00010030140ea80015032401003038100c1c224050030183c03507107454000c020180c0001d0042d4200810048032100c1000518100e0700305650070f024210240000900300c81044a0070b4021595034602550107090403d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 333254775 1250 333253525 333253573
    0x30305062b03180b220509060f040b04020a0302030919051e19030504050310050903041406120708060a0914070818030319110414010e0103020d0510030b07020f 70
    0x100b0908031020a0f000c0940c1042d40c6074008074403000c800a80f50444d114103c0c000100003250417a030240c09030800000030070089019258510a00880740da0800355940c42d40050043c0a00401c11945c901503c1c2c4007070080d400c21203031084940200c9895110550381d00344040441544200601044003a40c1001580c00d0070300c1d001c000e0b02e031050748260100d00c14180c94200c0c0c401c4c020f480342501c451070f0004040c0b415048245800a00c0d0501c800d0104100000040d1030559508943c40011500e071980071072014060507194034902c644242c00c5c00a115008240c0d01e00134002900c1b942d034410740310354a020030703030704070441401407005600001441e6612503000300b80c2011185881305400c10340790b0891450364000b0313034030302c0040c040030038003202c00d011680f00d500c031380c3c4c0002c074241c2d828540f0304a042016042c01269060520175260410889030b8841e504440540c05401c00c20807103810403240504620309a40030440303d81081c4004101060300008552441949000081039841078020304915506450 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 333256025 1250 333254775 333254777
    0x1051e3d1806090c0e0a0b0306010203091e130912080405070504060602010b091f12020a090603060902010f021b190b0a0503041703150d0c0e13030305062b03 69
    0x900c40114a2540803503204103950032040300858024180340310001103a8034140c201040c88001c03e40748540340c079002400c034100c54503609015100c1d59281c006034198800d61f0300765a030152a5015440c07003144403e545034034613002681e00034001540f110b0b43c001210101e01018114480c209200d40000340300d8400b50346d03c644a0300907620400d90742d4020400f5107013076800c0000981d44503003400d451400c00e8201c80b0752040c4400f0001050409a910101c4410303490b0051100308140324130841c080d50bc551030000010442c0c41c0c030402091ba0750f802c0c220018104000c1c02ca0010b10750704c5031484240d10000300f07910091142840c0084078544c0000304004060041c4130710702c10100d1450f0004919040e14060b0000c110240c0301c80340c1d60b00e0306141c1080d040ca10986031a90b102e4081c41030009044080a901c03090b82002d0302c81840c01c8445080040a40a040e0300080000100c0001c002c0800c0f10024607800c49480307500c00740050788800c0c00b00b01602e40e00c40c034a0150101c03144d100020382131002064216031402 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 333257275 1250 333256025 333256141
    0x206070c0b0309010e0c240f19171014100c0614070f08090d03020a0215010f0620063105030405090c090108042301051e 53
    0xe19020441d2507003044804018907551182800460b5005001481010208654462551903582c08030202d4160082c07201d04a1000400c5940440d54840708454940c0c020f55680903842d403c15000801d80d107060084802c010f0700700070100c0c0c4030001c0320ba000ba00b9241079040e004440c00e0400140400004c0c0c500b0341c801000300d0701d140940451450b05c02e40050b51800728000e4428a000c1c2400f0f008400c0503d1400c04018181c070030404070490100710b50007028220700c0c0c09641c0d03030b07900c4000f2803070b052403001e20741c8800040d04000550001804881d90885406450322800c078400c48034030101c1e00902e90758142c0f00381c01100010303000011001820200340d540800302106006036154003a25500720b01422602c80e440001c05102629010300c000f0341c0305030060041454003041500080c1503240280c0020440c0c024149000e001f01038102100c03800040a40007040545440384a40440414030311002aa40780e18902151109101140c0e01c0c0070f01c54070700c00c0613001c040880e0074031409506601c1c0004240032b0f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 333258525 1250 333257275 333257279
    0x51615170a021e031b0f0403110607020303030a270503030406050402210d14071230060f050105040b0a0804050102130e07030606030c170406060e010b0a03060605160206070c 76
    0x103920354081c5030200760129a440c0d20307114005d601031041894024801d110b05103c010360800500c6d04a809907940a00c00304c0c404e80d2401c000c500b050180c1c1d003009603d030002000b003000c01840d84e481030041c402c6134451070888030f1503481c0445065605070b04c090400d410030400540440c00035002503070860310180c62030b0000240548071441540e010380b20883e998004480c0ca019042c0d01221200380c40d50201e084500d0910030f55501240484c0f503980c1c203824840c0c080700014458810600100340f140e0180b01d901c14181042a09400601c01d90140400702d021206000c20194840ca0a88068800204c02c00745032024002c0203450f5841e004100320340640d000c100042e160942d070f4480f80f005010b181c0140e0b205007031151002d0113403049504094101842c10300d00c141c65681c410078144800b0884120b410090300e0b20308011001c0c204a41042e0603000c001d0000051440c045802801c40a010f50b82c00c0020644945c801c607918490003444407403152030780c1d0381c50700581f40031002008198071807059030b80410b07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 333259775 1250 333258525 333258547
    0x10080a0308040b0106170406090311010c0c230303190b10090608130203030a180e04030c02101b0204020f0702040501090204090e01110f0307020a0f051615170a02 71
    0x800444000c40018090005002c01c00ca4078202c10ba02624181c1000c6400201500c00d10702468401400902084d8513912500140340c020b0303d144445030380130402805001c1c010b10020300750307078408081181c41c807243c070784e82d580c01009081c1004115003107800990720710346075618622103003041c20800184840d80c8602d88840b90303031040740800c80400c050302d0301c046a5181aa015000b25001001004450400f115070300050b0750110071106000390a080044981003036003114014040d690704068070f28a080c8051005241e000250030300440d1085039000078050b00c11800702c40140300a9041d2a40141c20b403007407c010b103025006408004070780148a814400590002800e80340d00ba4040d41d696030780045c090007100105d025031003002d90444001d102c1842d1600681056105401e59102d01920120101d141d0780c0c8207000c01140560001103811100c00d00e810526200c011200540c01c104030350620004041d201000c5882200010f40c980b07000c4002c21041d16441648002c00c84241603a081004090701 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 333261025 1250 333259775 333259783
    0x907090203011410030c0c02040f0b040f02030a0b06040f0506030a0e1b010201111c0203150303070803060a0909050d180816140d0b041b090905010c081515031008 71
    0x200003045446900f0f1210b5810b00c003e40c0c406030540c1082604020311000002c0e080305440c0303009641585d0000c0e201101e025602c004002e00d8025641c01030034134190b407030301d445d07141c02071401211141420042244644100810b5208511444500341c502500400691803d4406541c0c01400103030301203800302140804034104103000302c103450b0302940400c20851a5074248103040341d01035044485840d20f52800a030140001c0401c0412244580010010b516814100006103408402030203d03602c6d68000d1801c84184d410442d14940507280500c000116410140512a0444d4100001d03060140d000e00040310b58164021005c2da0001402e0000180d90108120855039100d1141c0c50305202400c250300001c07400c0652018074828000c861003035003c41c980484007608254020202c0c4020355030b050f0000381c465620380c8180d180e5440e00c440c1d4424800190480181c240c0c00380c0e24442c0943d103854540c15160705440c00140c20102c0808001840c1c15613600441d00180c80601c81880d44d86d0760300d00c00380f030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 333262275 1250 333261025 333261029
    0x1230906131e050a03172202030307020a030c031a0106080c21010b13080102030c16050f01020313050d0201060e070c020f06040906030c08010c1b0602160b010f050102061608090709020301 82
    0x800d84c000041d00d401d0660040c0100d507440c1e59121900d40c40d003402030300494a48802e0300b242e512403400e010140215503042040740c490703580c06010092600e949040841d2049818401a1640c0107580c054024415101d200c1c141030b01c00300c0d125a05103841e03140d0851410341111171a0311100030340f2614030568241300207400b4020300381542c003da51241c0c00301e003071011000b455012010680c014000d2059240c010320644154101a0f0310704d40211116040080c602175104220044651000003032003840d11051060310001800340044502100703954408a01301e0710700d0b04c610030150b00a0400b140d1514400d125402a460000300040062001e4a0000312203134003a50003140200ea44100c10010841ca1010040082209100821480000742d4000c0c160003503e80b0901d440c40083c2c2c8194041040d940c0c181d501c645641c64104d000350400d03181c103e20040302801030b1a848500d49074006042d40c4001003540c8541402d050040d00f0b5981003206a80001020300640d14a000322480400ea2043c103101943c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 333263525 1250 333262275 333262283
    0x60702130204061d15130f060f0e0102060412050d0b090f0610090602030708210a0b041104030206040b07240207020103061d15060d020c01230906131e 66
    0x10b0348618228000d081c1c00a403601d201c0781c00020869800e0a551010085000040844000c41ea10495100c0220b83d40c1c005800400c00000c1848011815070790140750302038408016228144210000001a039881c1c400322002003010301087e00c82d0508070322400c090904040e0f64080820452161800112400d508483d810f540050030010030810340340c281e0700e98904101c60700b44400b5a900f40f0300f0081d10fa11920001904480001032162491608800091030f40d007020b000605081c20840c4548024246040c405031045007480b030303a80c40c5040310b1401c403422032303500400300c5280c24900341d6040200c0d0054402074031a803c0145c1071040e201c4000c0c00441c030b41010482c00607942d20685c80058103ca10304d400c131034916a20600d10b07120200b01850000c0c2c000361030909501099040350f0001380c091240300c42c042d21890020807450701914054010010014442e941500b00c105019172441110f41e0480d04144940d2103400410500d51a46e541e14603610302440c003641002103c0740c00c2183c40c0c2d00c0f15504503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 333264775 1250 333263525 333263527
    0x30c11030d20070206030705070309030204060e09010f1b03200a080f0c0403030f050c0a2a080a0309050d030201061d150409050601051903020d03080603060c04030201050412020607021302 82
    0x4914504250114190402224501410083c554001c03403500d0000902607010f12900003111022306004403010b00007194010014480c8a4688105003032118041d00c69541c0ca40c24452003070b0802c8154042c914200c02c45130325216601100060460151918401940c1d00410a01342101740c0140c000090095041d107403980d01940c01c00307000c480c0c000e000040c0b00000c15a410b00c028000a540542c9910011030140307002a00c4030121441603013045503614000b02000011036200c1400d0414051005228002400e40341203a540e5018850315240f0140c2e001300051103007442403103240707042d030700c800d4001e4007034400014a251204000842001190710261110321140d00700403003c0c0100e01c1c0325507441c40c1920203201001c0b071903442e42d41e00c2c141070040604c02c0c0d40b280180d03101c816030b08007081c00440d0001c0c070b892400c040504000d0085102640c90b94028054403000449138030404c03080b0b034102ca0381a922145400e10f0401410300c101c072102c070102da03c50410000400980c0d240b21028801220b041401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 333266025 1250 333264775 333264791
    0xd0c111c0803090c1302030c0406050d15030b06010f02070b030609100915030b070c031d01020109061404030e100206070807031112060301150b0f0307050f04091407031b030c11030d 79
    0x400c9154503084007208176401041001041c3c0d151505a0b000c403203941c10416251400440030401906084102c0c410140c980b4000009010423801a43c0c060a82a26a00d01c0d0001e20030080b43c03241414010a140208100046405820130500f17481e0b016500e4906005a65181c1400a081e00c0400e10245000c2c006084240144010002c00c1c03070b0468030782c0c185001d02c45016540a085040312690000326000c5c055440c92440e4001c5d0007003007049601000c10007007031459801040c0f50401c192801d4002400400b50741c440b50500185058030001581c000f4065aa288a4101ca140c00c000305094101a190350388604451555000341c1030031804030b0764011040c6001d0080c5400c452801c110905110800c40e000c20220320790008071400e60032200c9a040d82c2e0303a0b0384e1a041e2035074420a80500141c2400140004104010313074450081d140b52462800348d541c8910750110140c800c6402a401c02d0442d40442200d0980250301ca482c82060f20b0402042281010360100d0840c0c10031040c80340425214681 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 333267275 1250 333266025 333266029
    0x8060f0a05151e12040219260d030903080c0c07030c0b07030e0103150b090d1a0a060501030209100305090f010e0102040609080d0806130b0409140d0c111c0803090c 72
    0x20403001000030070040f906210782000c1d100700896000d403001c0c0c001e01c003c682485004400a040c0005400712000744411802c00c840c20380c11018490301050054001d1003070f4a44600d110b4001c40300d60300d800d5610f0b401d40303498510000b40164062403000718507100d0300d00000001600110204028001030000d29241c1d452414040c02d005248524a0b04140c50315204580503160340d0034550a0307c1d11180d80035100c0c0544400b141e4202a1a103001e0031b01584032002600e4060300300b035104e00c2100300543c144200d43e40d5134019800c0c0d01543c403485508c005503c4a06404602c80d60240703034488c0c150001c8034100c7e100c2070050341c2121081e003641c0209075000501807099542000300384000304203a1004081c1c103903007943c0c014030910019211170310588010b24220080c0d2100c0d0003100e00b80d10020420020103074240b070b040d4002c010400001c00d40c1c1c081c0080c0c515415001d903004101040e084213814080180c05400c02c8880908901445200d140b403442d400086094003001c1d51080c29840d00030120b00840c042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 333268525 1250 333267275 333267307
    0x90a12110d0906080115020f0f0c011b080f0a120504150608210c03190509090c090a0902030901021c3908150d050d0e03030a08060f0a0515 61
    0xc014070030b2154816081011583c00552281190030900b02400d110400039812420580351540b6807846105220141040c1c000101f181d0062450036211007103e290303200c0049201d00802500940f070b000c0107100f6210355154940041c055050700c0d1912070b6804070704c2c00c9030f9011628191002d8480480d40084104400c0080c861a8060309500000f072030700c0010b2441c20941144210800420f40f000801d050101a004005540074549a190080b41584a40c200107119801011343d06209040c1140401c1c03850304a2000c84254003c0945411442d50400324200040d52010302106101d44d803c020032052920034034200c5031140700c681c401103600c50506030400c4143c03031070703049101d05012116021120b02203a65110800c0c2580c50400c0c4d006543c504c04408080301164484607000b101042c062401c011000c251051003241c3c42e151440600034107428140d4a0240c1050600032504513008100749d8507103804502070b9410b0040c46114400d031158046455050482020000c0e1080801d03041000a0041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 333269775 1250 333268525 333268543
    0x140907030b04080d20070c0509010311010804030216030b09010c14180105090a0305010506040507020d02030406120605100c060b0102010b01090311031005101d0408040509090a1211 79
    0x140040050a0440d00c40219036003028000908030040011500d02d804066000450781805c0c00025484c144061100e02c141c4d44c0c00640b0444001c1080000410249001100b65040e40c1d006104000c44c1c076000c5005680c8400d0140090b01944140c44000540d2540200020081c43c0710300201d0f0200e0a1941f2507500352003614074070000740407000d80c55602800040003661806450003070340c840562481c8006880b41c0c440d41040f550445007514010042c0103054000c0c900520702580d0401140e901c610080361901d42c1a48000c0040e00100b10130819a0b01c989031000c50690070600001d04142d075440020760f120b0382d64403840c0c0800e03004058079090080c0c81c8118840c012083c00240624280c88000800310202400700601080c000403000001d03417410842c07468400c01e0b080d020842d03414011440f410f41d084078070549048010b070043e0245102c0c1c43c1540540601d0703010303003002d04060030036080009941c0f0061809901e81320b0311200001044d0307005103040f894049034884d40360191020b06e007241007050382 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 333271025 1250 333269775 333269791
    0x170a03020f21070f0f11100207080709150906090b0a060903020a0504050c160605183c01050c13090b031f090204050c1315050307051b0303040614 64
    0xb00405070100c4803a00c80c0c0c0004002e010001503580d01c440c0342c5480991030b2480060a1004002118020042c18011164408800b01c2e1040801030340800c00b2a5170300d006020700c080642122004002ca81500d41204418501c50f8804047c400c0d1205843c60855440390300a514140c0c84e810307241c0003414060000006480580390800388a03003982c0120340b100c1400c0c42114056030f915400280b00c0d401500690f80e0b562442c030000c1030000700e00c0c10004c01500f000d881c07800070a10081c000e2070081f40009131001103107100c20154010310444c643ca24061244411703d88805034074100d50480c03803640a200d211312601030001403d484100c003000700c81103560319804c40701c3c10900d042030f07882081e540080e1078005009180510340700e400640b9100ca000e00350f004402500a803d04050005900500c0060304540340c1c0d29001c2606540d94030a10f16600d07000d0a01400402c10400103d030040344200700a00c8409120211711040d02c02c0304100924503030003154103550300c81d9241c0240c1d50b19024070920380d810200c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 333272275 1250 333271025 333271033
    0xa0507140a150c06020721030507050a1706221a120a06110c030d0504020306070306120b0403090b180f0a0609090b040f0204060c052a010c0606170a03020f 68
    0x34a140c0c6000078010700d21200c14403a01015680820a860701207406d407d034000641c2d03070281c143c00703448242614881aa0008241010001035509101d41c0994007180119580d0420fa888110701c08098008060000d640004120b10842e85e9001d60f4507102480030303d000000144054011031350716242c0e07400540c1c18801c080c4104014104c080024800303035255040b00001800403010018600c0c0780c49030103103203105400301203060380790300c8416840184224001d405a03a80d03a40c030240304400729881130283c100f2416115003043c010486007008964407610078102946459240c00d2010110381204050406140c2035034640a883d003490010510b2441041c0d441425040c04e009001e844002c1030701410f032185990360100012a5610741191800b182180c604566550315610014486098410240c3d158482d4020044c020310200003110f02040486284044a421a1004444802c2410030503a031081c1c031792a0209000b03100300b00485030030700c42d080241030708a05480c1c0a0f05207001d009a068140e08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 333273381 1106 333272275 333272279
    0x2010e100501080a17160c034119032a02030a020402210108031b0705030c01050f1207080109060905061e01030605030a0507140a 57
    0x1142098600c4200000600c5007500d80a10820415520044a5902040c2e16181e4a6400d4003078541031464981e0007808507400d5242010156188041c26004100b0850350031042804141031452049d9129003410402d440c4c480300707801e15271072050a00b03001c0003045000c0c410340440001c65004403d244915040082181c91280c100c0780b541c04421528450341490903403070290b041ea008006041c94821582408060341242080c0415070030000c0700c154598040142280c06003802d03d000315212441d00c04003200c86803014280c444180c11211082c0b00e90388000c21590400700c000e0070565901c1e036951002ca0002d2141207030722000e000008091011340c6501c0800030b4100c90720380000b480f8081c3c954403240c046400c140c1d402640300f1542550304500a40d404040780c0c1e807260505000030081d617200082418903041c00b03811500ca40000500b8040b00d11100408034094a05484a45500d8 = true := by decide +kernel

theorem cover : BRFrame.Cov 333093525 333273381 := by
  have h0 := BRFrame.cov_init 333093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 333093525 ≤ n) (h2 : n < 333273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
