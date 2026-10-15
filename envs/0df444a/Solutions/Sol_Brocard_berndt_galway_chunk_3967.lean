-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3967
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:11:42.16704+00:00
-- url     : https://prove2.me/submissions/fd9c26f5-926c-4a07-86de-b889fc6a546c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 713309352 ≤ n < 713489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 713310602 1250 713309352 713309423
    0x6011e1115091b090c070204090b0a0203092b0c050726060709060f1206050603010909150e03070201180b0a0324081b0f030a0b0f090703020904030507 66
    0x1c1c0d2a00304501800d050031642501c8035002c0490b540f40312070341c4004c07030a600700103883d0b802e9850701070510104000b441d0b4030748054107084008007048a900519001035120f82c00b40b900359020307200b01a5041420340304005100c0f00c4107441d2039090500c2c501c079850303001000740104100e4040958801c00c094560041003442ca900d1092151240c0021504001858001c0000e1601e00c0389603290040041c2003803501c207110010040691422054851643c0010000d8200201040e1303403035a6505081006085064084403802211340c145820203100780b1541344120801e20285140508035401101e030502c60008142701c030540d0200101d1000c080c000941104001d43c1c40024a03500c5120b070908070203844901003460010340c484184040a0041001c1c04c100701200361845d98659100d0001e40c0c00010040c03025010b200d00885a02480555804640039175421580c0c2c548540b580c2030000e84403006804065004030801e80810002441b0340000d005041c001c0360703500d0741c05407503c1142213100786500300141d0f07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 713311852 1250 713310602 713310643
    0xa050402161209120305030c0c0717010c0320031018050a05010816030312020f070f030801050a03170304020105120405060f0a15090b0f0306040b0f01090506011e11 72
    0x10000024920001c8000d01e0a02e1180c03e450f0801d0200f0351604000004d0030401c000c00030500103140072040d03030410808a816503503030313030386400302580b09288040e440481503090060110907140244144a040828403c00806004840c501c100c01984085c11000b1a1400c0d1100012204060ba440440740801010301140f241440101070303044d60b1060708006920380000e54817000a0030003124460840b030341030804105e1141d0b8084054020b0081c103550b40391580000982c1c6080102807141c000360366209407241d41c842d03600c034418004003502c203000060600c1c1400030501c2d62030342034902940e0701a2051600344d1070500e40210703e21103628181c404581643c04070040c408852100590b03203921018184080000d41c0036650b850742008507500c20560400e5a4001c40442c5842d010359038102d010380a41100d4003400e140c90a8144060100d40180d0803081510010442c158540a940c1c05448140d58488080c04c000d121030811001d818250740c140600c22200c1010003a041c41541c0444010220007031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 713313102 1250 713311852 713311897
    0x110906211005030a060510050d03020f0d0216060806150c0c0906041b030b0a0308030103150c050f070809120105090d0e10080c0a0c0510060504200a0e0a050402 70
    0x503890107030400420310301e500000c0c4065140081d88a541da030f00100d002c689912540822041c004407504082d40204205142809141d000111240000c08000440340d0004620317070101d13110500d00c1c011420011241c0400c2103400d00c25002c0ba03800920003030160141c03500ca0b070308203556640100404455a000320312a00f040d0b10300915003640c0301d002034a00f072041c040e004c1c00b494200c110a401c24024980c0d1800c014840c5d0702e85040030000340d40d022100954030351b184c1c101a0800c0c914400303640040380c100104041100c2c8240140d44034070b1455242d042c18181566964001d9822000301c0d20f420010031007070700089003001d00995000f01c1c1018040c00742c01524040041002c07094601e441e0082152100f46ca14450340314004940c0101d11140742601c5608a20b030464440c45000400b404500c24680100030003481c50b03101340704540b000c0703030100280701d0310b0614054600e004008000390a1028002e000d8401c4c026862140c00c407a0003403004480d50b4a0b0f90010701240c003c11940c005800020b135070314 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 713314352 1250 713313102 713313157
    0x90b0f0f033c010b2a01091e0206030114040e01090803060f09040b0a09050f0105010f0608070c120e010507050601300b07030906141e07030b0a09110906 67
    0x342c1c100d0401c5a0194551440000030402000040c81510500e6400041c200b05290322a0010f540c800246000c4070341105140c001140a042c80810590300c1d5900c0100900360b0100003c200080c06a02034060360441c2c1c03800c801c9085034018060400d8000c0d031a0303180340301c02080030b1080038074480c40742100984904000091041012039180329031f0040b6002c0080c0b001050680301019413048c003803040401c080d59035150690400e0349203c4100c80c1c542c00c20001042d580f03001120001541c9099640030b85950710741c242100c00c034035800000f801c1d25400b040130a0645108443d405500030045c14511300c0c0540b140d0381c2a103005000d0b0b105880c0032040400f95000c003416078102a50070705d0501700300550344105403a608511140036000f074040c1591000c031441081410b40000c0c1c04c5000f101400d280a1071720000c4021008509183d100004103080d0008403101d0107441241e94401c80509594035007070420801c0c0c0020100d507403440f07000b48810300140300c03036079180c400410310590008516001c10210f49402c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 713315602 1250 713314352 713314411
    0x1b0313031202070f02040c0c0807060e060f130f1103070315051006080a1e0504080a122913320402150714010c0c21090b0f0f03 56
    0x41a150b03004101c820080381078640c0315029282c040b2000100d010b44203100703541070508900010013032400481c8400034009180c1c0020f09011031442920381d550380b65440345030804c030100c4030501700c0005aa142c45c045602607a80f480d0b07a92040840c815050150000286054040d5108445268280b1541c401410082c060306401488a0190b4681982491700181c09040c009150030300c0c02e56242280502400c403c0d0b1101405d80c0400403c00c8581491304041401d60f0042010502007451203194860040c424410652030050864030204402d003e103000c3d111000b124011503030b004020070f900440203040f520461240b22002455415900d051454030000100727540b020a13680101e4104002c09600d40c01300d5117031450404481036a07140e00e240341154a07030300d10b08024a81c542c0b90214000900c2d03000f000e204800c03030281081c0407600c44440504000c0c0e04000280800148645004010706102c00020b4a49201c1d001c60403400c100040407060f0440e003048031000c1d4001001c070b18090392030001004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 713316852 1250 713315602 713315627
    0x1a21070b030c07030809070302130605091014010f050c010c0c030f020303010803040b0f0712020105010603060803031e040312090803070f020606101d0618040605090114010302031b031303 82
    0xc0381411071804229400031070003282000303800e111042000074814030050120740c3c0035507802011141700142928aa900402003400f50a0041d07038048003054045103096a040d00320351380c00c040e400c8034480c03d000448001c00580c640b001405018400501d89110a0203610007a061076070b00c01040310054100240908154042c5900b0340d00100b006106621004c4101e50965048681d00d540c0d03100c208218018510030090080d05805140b26907484159041d00a941202d031507680c2840426200d400c1da03070b10ba100a1310b0344010b0180e5108103805110740000340580c041e00a05022a5940d1078140d0303802640c0f0b042c80100c4031078200108000c071213a0330041c140200b000c284010125468818040350b8045031010340301041c8541c0c0803c031440145030066508407024090704040d103c006a040000e4080940ba003043d208908154000c03034142040b80082c0c1c1240e003014001e6520341a2240190020760020304001c00140342c03080700e40e07803c00111004501403a18030306452280005800d00410016003001c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 713318102 1250 713316852 713316869
    0xd020d0b10120b0105040c0c0204090c150212180f0634031b021201020a03020304021c03050406030905030f031312021b1e0909070e010503060c0d1a2107 67
    0x1c40b0b0001003003d41042a0640e00c007550000f4100f110b03200d042c0c4150460203002980181082110410803482498090440c0c049038000340f181e12501c541030b45c50b15500b068503110340d902441540441800b014441c0c0d82800080d10b4460318241c204081001584400d082d0107290105000640000d11840d0600381204185812a032011149a900900d0301c40c0c605604072107003200051000541da41c140c5000744d03c02241e8021582c1d044a09400b4000e034104480583c0310328103007103070000090700d00400b64920715415a18145010b00b010070550003840305074002c0d41c90344030a00c4502c10041056008502400030510064021045850415403000c115404002150051000301c3da9000c8585240c1e0aa401c0c121810412401c8800c0c11194103070044800e030b0f901201b24800d1102902000c25028281c45036810036102c2c4e6030300e80c0c06242e907030101500c803022000c1c410071022481c000b40da48011002c4c440e00c41590007528049000800d41e20310740c01e200c14810324910700c2940040741007040c80003c190b1f15 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 713319352 1250 713318102 713318129
    0x307170a06120c0e0c280e0a090c1106040b16050412082a06061e03011b0f020c0607030e0d02040f0501151409010324270b0f010e0d020d0b10 62
    0x10942081b03904051010300c1001e00240501000260042d554450b020354003401c11850a6500c45400001c2e294601c805400700b92090608580300201060051144d03800c80c615109644900d6000c18000004c030400800b040801e200c00300d080d0802c0700c050046107000c0c1c42840d4891601f1800024040041d95680c00190510441100e403c3c0d004501c8039440b080c100c03000c81d4110417103058906e198050f4048641d05501e800d03041c0e5591380000c00c550072509100d940700c060703070281c00d03800f0799684c21040e135401e07030101080c0b100303c001a11074a80340209200103410206a250594045404d4130800d00d80c496105854000501101c5007000c00095403019914103210200a00f241d42c11051040c8505581015210103110020080091000c50b0000c405a2060310880d603801465030015824014000316402c12003104010307508031301412959180080c40c00e00b40545020045d105048500d0304c160b0003030b1521113107001680d01d010001050600480081040d072500700d408030210180c03500400a02e4205c1d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 713320602 1250 713319352 713319367
    0x3080d0f0c02120f130810050f04240207060f06080f0c0f09180a110a060f022508031b01050703090b0a090206250b0c0307170a06120c0e0c 61
    0x1400c1141050f2800d40342e030345050310b8191010034420300b000305030003071002d00001882c0301340040c00d0360b0882ca40940400c40c0d901d0701301440401d03660aa802804080c0343c420030300c00300b00741003001c0040004001ca006244c10380c41d688030425640c014401850f07555981d80d08102c0718070700b80300c40690444540007074000350014070009000070015901c0c05d03005401c5c1c1400a0030403581e148035401107048080840c4c21006842c90f140b61418400e41903a03024007103103080090310601034807084030207100940107807080815101808140c42c1ca07803513040e01003107161100040d001b84141300406a008604481400c1c01e18440000c0b422755a01410300005c01d45000d0402c004201b0f44100749410162051012411550500005016001e6a00001c80ca01d46c81c070740080c3d001c0c1100440314070700d40c8201c50006065603024140c0c0f42c1d50104460041c08940c016802e50250200c1c0c240041e480902d035000004c0c6c86886165401140301d4580c422210240e4296040c816000410303143c6901801030350b8920311349000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 713321852 1250 713320602 713320607
    0x1e0902030c0126130c080a0c120f030c110a060221030f01030323030c0903011503170a1412092e02030403120e0304062d0e030f0703080d0f0c 62
    0x183c10b203200300c11a40c040400e03201d0142d00070b02058a80c01035007800c440d5440c2c0c5c081c0e54917240c844c801211010705c803c03c0001d444a1510350140919040f580d82d820303010b000c0e10103982003031000c1030803114902c100440480d2507403900402405401d2a600401207248a043e5208602a1400e06110100c2d01802000a05002054864150b0394180f501d4803841c408096401d4181541d411400e50f248800300c10840e00c8030700900584902c0c0d0f4111b00130b0084c03180500e06101550441d0202074183c401004003030324030110010040081131241c0c070b000c2c1424602c118011600f1b40001d445036005003000428800641c8082040840015120380344030004058168090032030540300c0c03603806517590003000140505000d2841e5882c0103020440501140381800d40c2d00e0f07200e9109015440200e01c21310b540118004056006002c2907801003401000d1000701e0a0903501c000092001560605c0703102d80500040906102c4840154440d00104c2c1d1252100070380401603074500382c42080c0c8c0c64070706944c1484066 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 713323102 1250 713321852 713321897
    0x302030703120513080307021f02070306021c060b0a11060f040f081b0106050316030b011703071a0103120c02011d0402090a06050d0b060405130f1e0902030c01 70
    0xa0b030050912140b4141d0040c10f4480e4010f00c521101400102c510008400e440440180041d030f01c00c45100000541c08031007030300c10b8245e24140b1801a0b0052500307100040103540246481040d00e410748440340140d0071880c003a42c403560050b010805010802503505500841e410080701181400f13000685410070124055090040020306041c4e40000c0447c180217528013101c1301d0b140480310108002c20360a4010307020702460700c80d80e0f0207817044841600c00404402d040350242e03540820401050b034602508003010724a01d8104504c1408104081c100254150388454507040e00e6890701d03105585141001e1010203016682481800720110003000140c3e8000f4102903540043e031703405c03009414010301040090090703c41e8650400307000c0384082041c41d0004090101d158001c04e050000c00c500c40144100e500482c4501508804944a00150b6040741e030094282013444a6000400320049128000760001c03801d8141103255850b00094150b040500c40d080600d076080c24040c1d0001135007080f0394042d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 713324352 1250 713323102 713323109
    0x306070302031f08030712050a02072d0e010911090609090709150c110d050c0634060f2903250509091605040f0906060e0a1503020307 59
    0xd81e0000009981c0010a83c85440038485084820f0159889006082d980c0c0c0c8440700540d2910400410f0050451007441120f1845000c0e0340a011180d140201d0305a410b810b1035071f1080890310400c241c143c1d403045141c0d140d004003080740c0a010b141d49440714110031580750001584c481e2404004946540d115001142c0030710400340c0f2202c105070b85003441203440d80281c1d00060030004915542082c0700b5401411400300034000c41401c41d55281381c00401c802c3c58194440100030341c10a0f40c1091141c82c1c00c00c081c100141c80114400308c0c6a001c007100d94504149020707c501f2441010100b034003802a0751085004800402c2c00810100d80403449081601003090403d0f00d01141a403c0c9400548060020101c003120214107200c1c2400310128038440c050250185601450a0703400103400b0f80000580b880006004c90f8480310300300d08040500015281a83e00d80c0b80503500d441001c000900705201d143c00a081d00121646541002ca81c140290341c81400244d51014103d4002d0016a0b00030800314200e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 713325602 1250 713324352 713324357
    0x909060e040b090307062a0903170309120a020318060306090631060504050708070c030e04180b0906240904060908040314070603050411040f020c01020408070e09070302030607 77
    0x150b41d80d03c038405203988592040240400d04268400e5140c481008640e41420a0000e8840b203079403a051088840d400d00b0310010301070950311140071500092940045401c43c036141c05943c0c40300340080e00300169502c0208010016480041c400300c1d1140070021411414208443e89491400c102c00050001d0001a010501ca400304044240c000b49801c49968aa0015065025000e921181440001f0b051078450a400366003483c0019515910801c4450310604158031031202040302501c00f1600400c0070f400954000c3c2c1d460544420003403002003148070076031066a10308103528002502d02c6c100400074001c600505e060308600c5a08030f007444061080f040003070300c00c2c2d5650759650a058001e0000e07260060030704d05000401205210500701801e800e00102d00440e106180e90340000c034222001100d0140c5604020001840703545082d0f00540044507110f8405402c01402e5625142241d02940c0103c1141d4000342c030400041c616140300c95401101540076089051858000c40d440d400300178189001c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 713326852 1250 713325602 713325623
    0x11a010225081002070203010f09050a120e0d0b0a0e032502032508190b070f09150f02060a1505010c14100507180311010507050a060e0304060909060e04 67
    0x141250860300402002c02c42e046842011010140f04001d43c01108160b0195081c0701c1800c034841c0c0b050140103015640304009159042040d01c441c102c01c101e0011840410005580c80140c0d951440304803440f45008007200b60300c900b00107148030b0132150411f850070a50342003804554540005010801540c41c02e0009058071401d180c8006400e048400704079040c081103c6840407017004104540b0025600380200b1203149224488036141c02080c00b0000030b005000d440300240c6500c0c0300340c040d000c000340517040407448243c840c07041d01042003031500742e58009451004d5074446107a0401070303580c1110415004111400c02d0300308411301c8030305601603181841810b40e008001c00404116065524181074151102d960080700c004019000c2521000006003040d0301c0d000754240080307580390480c0d40c4500c482d801d46803100f006541a030411002603440f40a00000035010450a006200040180102856640d400d1010140108841e504003583d414645007080c0400c0946103d4141c105030003039038030721 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 713328102 1250 713326852 713326903
    0x906100f0207050d050d090608240111060901051b070f06020a20060f010518010e0613151d090c0f0d0818130b090411120717011a0102 59
    0x2c0c035090459100c0d40d00158044e40010a010000c03910b41c03013081c6195107002055960310303421117502c1b1040d101c10340f60040e8031212006040041c0d000d00c000c000b06060034108002e00442440c140312084030322102c580d441d04108005070714200d62901c8241d400ca4142420080c3ea515401c80f0700c0381c1c81200502d4240d0018540342558010302c05410709540101d151808a0143c1c9115521940705440c2541d07800c41050000c202c1d850107078428125910004c031001c11580c42d05c441020074440203000325400035035909415420301c246010f076261030072144103100030080c90407100140507043c03420240141c8a01e002030003000c0f500800d0106000341c0c1100c03402a003008420006000120030300004145c814006840d00d26801c810384c1c82c074091700c01281d1411180c003401c544070003519221020203038010011400200006c0c461004441c86140c00f030320104000b0368a20801c0d01e03041068001c0138003006400e448200e014000d0249100041c0c032000b801c8d80445010740042d40d28001e444036415030040070304940c1c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 713329352 1250 713328102 713328107
    0x130809040e01140112030909020403050d080604110408010204030c050d020913020f06040303081006110c01050706021b100f020403020d080c0f061314072108090603010303120b0906100f 81
    0x420105118600c0c00d00783d035a4400408406072001c8030b0840c0400d4060900042e0442e903842941c0c12260084050001e01c004400112134244000b0101e950299a0b403181045071070aa50280c800f5208010006070b803541982814111549158800340c85004030082540041e00e0314207a0740e400c11f400c4042d41c52207940920004032030001242e041500101c01240020501d940854403e000380fa040124180e03241d201d8008881c80100c5881c0801c02d9880001692181e501c210f005007035642c010040142010346198401c0c2c514038100c0c580031440c1d8048480c8040900540c0310712a40f10800e920114a0070b403950340840d64403854500c016103d100082020785144000f404001039110582d001d03a505032600c840c0020001c3c80900c41643d14100c03500d1070170015000000c040059803800d5800c00b0000d954240140c211403c0000115003514080c0f000d590603460302009103020f103100e500c80100d14001d0700d40960854020b039500c580704130045403d200b0303140c5035181d41c01e9044041d49070003001c246448409 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 713330602 1250 713329352 713329361
    0xc120302190906111c0e0102070807091b0c17030402010e280e040b1512010920092a0c071e0e150d020d06090f0b130809040e01 56
    0x990904142062408000b907008071071405a850f55160051401030340d4008541e20102201e01107001440c1003c420380e0980540100e0f038040e141441100d07038083d210011a810403010740c1c42000510f4540d0301c814900c00c09129120920441032802c00011009a2580100c10300c42c249840e40710300d4004042810741e40b192880199504c0c0c0a0705040c2c001204c580c0d010110070000c1c03511082404400c5000c5520303c000d8101600480d00990031004a46450300806520682c034099070350710110105250011501c00c0c01616000c5025403e1f2503130103404c182411030074544c10405d20784500501c000300000f2140c0a440890640310600e07a08e284060290542059403266610302c030900c2c030902d04009004e01c0305070132102626000c50f924145c101e80d20034520b03040c074000765290664040049404402ea0a1000660704800d0001705010f800c4c0c4465190341c41190601e000070f48208511401543c1403250170413005400010456407005850b0184d120711b0018040e1030150703489103803201601140d0740000d402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 713331852 1250 713330602 713330617
    0x3070306031b05130e0304150912050d030b01030e030304060c090b0f1e09150f07080406030c0e01050301050a06030e0c09130302070905060a030303020a030608160501080a0203070c120302 82
    0x245481c4008002c07009110000b1244601c038440e11072000340d80741c503208600a007542c03140c40704019802c0c5800c0078400c003494101c2410200800000701400980405a8581c000311030b40103c01400140d00f240308001d00380d5040e0703841c0307034140740c10803506103c860000004c4950086d00000d0004ac05000d00380215580f040300c0c0c5c40012401c4e80030030358646500c0c0e01402811100b03400c2c000162034461a886080e02401000142540072844203164191040a24020a9181000e4180c00e1610b5102c0e601d0a519412a0f004880001d6803130340480c0f801a04001403c6c035141003420540d04661400000507017040840c021241015160309021500d008200450011604020185181d61800e020400034841c2003983c00d8006110745c0000242481c4103102d01801110301030000d507c42d0b030650f00d066019600c034028210400d80d030b030741001070300301e4052000c81e1040702441b8914050381d180100040c1209070240c9041e04051040007885440340d00f102545080580c484c0311a104003940040c1a0000d00600780c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 713333102 1250 713331852 713331863
    0x30b13020a060201020d1401150c0501110d33050105090d0c080a0c09050618061c0b092b2001060b040e010e24041d06040c0803030910020307030603 65
    0x1d001007005a0190054202414410801c0004125144402d0b00c0c1c03031420711500c50141020b1620040c00c030300c901e001c800c580d8010400440d03241c484503000d0b41c3c550300c084c441944042d0b45030201c6200e070300c00d8407528044002c4121900c0b00c0100303032120144412403a00c6124107014001465544a0321190942d403001600305140c5001c00d580e540d40c07541c969503c0c440458040c080742d500800d000c803107442194011100680700e060210320101a5800ca03c4010740300a900c07105619408050080344114281142d206825100c3c03942050441c240c0b0707011031001c240c4101c103581c44900904540d64141118603403030a00d00303003100c400c4220340800c0c00313140c40000341c000d5401c2900101c6c40c1c2640100900031184404600411680c0e5000300c42c0108000351040300451098074404402050201c0e40203110100044c030006d00c03240501e180d4866139540d2002c070485504100100700c14009c80031000c00040c4940c5001d981f440c600b40006d1034441042090030117a043e8080007050001c0e200f50300640196a018 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 713334352 1250 713333102 713333119
    0x3070e0a02040608010807080d030c09170c03060a020a350a050405071a0904090507050d15050f01033311180f0109120f0f0c030303051b0301030b1302 66
    0x4290340c00181d80305024000108428100001d2903000010703078041169080d20151020343c00140c0107d000d000f5840c060409c03c03680020205821401601da80c82c0d49025000500342d4061b100280341c1081001450f110005105201c1ca86035036800ca80694900d50845081d04d05550f0441800d91550002c1304052200c18411f4007000a200302551256004500440c211015503070350300d03410340c088a0060560028604203002c0914207040c5a08005600d511940a0381e035030030b40703480109030240c0f0300c0300c03043e03462061161410710b90080c00d00c80c41e03400c2036030040309442a40c119200c1c03180103628040f900d00a815021000034042e101003c070702400c0705115006214500000c11000f1040c1c200c440c0c2002241441d403030b400c920b840c00c80402805010b040e140c904405190600c42240b02c42e01c0c3c40f05a603540860021203000800a45629200c54440c1c1c2d1810000c900f1414002c04840d4024045000307a0b0944610b611b4959044d029613044070380c000c1c1d080c072aa0780c5000800454815041307000790000b02e00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 713335602 1250 713334352 713334361
    0xb282706030f030801050d0c050409140f0309040b030a030f0c15060e01080f0f1002090d06150f0b09150901021e0d030b0910050103050705040e09010c0f031b080603070e 74
    0xc1070740071520f80242d4600b1340c0d6907210800c00032800311600008041c681100800c011600703068102d6001e103406511810202004280860700301854000f0500301354100040403070041c6482e01c5648186030044e401019500002d9501400c8103018a00721400e201b201d280740030030072844400c208615450410244215651081c069100d12405e00a0041174043e00d02e0803102007000180704190050444001d00c83d450040340341d88000e41c01040207940211038081c0020108260340504814071501002110a00785450500c100007078443d000302100c01801c120301c1445550707186002451401c40303980c107031b40c1c0c0c03014500603881e16140c40c1001e400800e503a041c0995070000410340d0703c81e030301e01c07600c0600089840c1010054004800c0714140c642680d045014081035110f54030031742e070002050130720b02e14054540d154950801c60442c0ca0003516910356951b14401a40021000000109400c05004691a10000e07402c0002d20358820b0041080d610002219070340c04001500040072810f80900d034a050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 713336852 1250 713335602 713335613
    0x1c0203010501080f041a19110304120503090307031803150902030606030c0901030b0a1d0a0c050906010804020405060f060d05091e06010b1602060a030b28270603 71
    0xd2160380c2c00309040368005004681c402030341d10f1045a000240c800c0a101c036038030101c80c0c641c01800441212000e400890300540c0c1501c13a00e40024901000c031601c0e4609031402140d25030a900b061030800405206110300c83d0000400c0c0c810055045c1010381560496a11507000c0368825072014088807000c0d0014882d16a16070b2120f508580240d040d84c01994915090560310000080d0090704400080c0c01040031500703003c505500b050a1100c0424141c860a0b1220109007540c01c84000755005200018208650441050002c100a46180c0340c81c6c541000042c0070400000c1000c4c2c0256150350004440c3e44c3c03424404190035400614841c1c8418840b008600100011140c074445807180701040310714180150f1801082c1d45c10f15006004503030a101c007901e0b0715088100790b8600740780c445004100503038444000c1e040c1202c140d030340000c2c2d00d50107201300401300030358800c40804005640c10302c103020801400498103031119070f48801075080c2c000b20035098000741e25081180c01d82c84c0c814003008120 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 713338102 1250 713336852 713336857
    0x3390d031a1c140115030f02030a0507060207060f090510050d06181d010b030a150e03030c12070903031b0512070b04050d02150604050612010e031b12030a111c02 71
    0x1402618030030381c0c0c1a0303080002404c030341c180b001d0740007250310317101040002494642d4003041c981c0c0f024080d2160619030b40c0e03d01d803410480e9041752025821095040c0500c03030b40f040006449003220301d03010b201315140c40d012540b10701401400300d041007000501c3c0d16400300f00e030700301000410480d00040f84040d0400345081c0102451040200c8000c030240c005400200140100e410700c10b801400b0701003401c1a6900c10b000940083c20106046490b03a01c0c80e40d180d94103101440c3f00d00b0303840c503a242d0b9035400a6424044003100809100c03c2c040c00b1081800800d0340504800002d51000f08100c1402c009814414941007198500a030200400540141001b0015002c180a184074004903009100200f00a07611602000d01c0302182404110000c1e0b800d16240d0885908500007070a888140d5014500c03507400e41d20b1512850040d07510010301003d01407c10a0115440c0181d50003400e000107009614244900c0054214450316032140111071041d10010100c0380401c009000d062104019854214041d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 713339352 1250 713338102 713338159
    0x111100b10092d030b07170601022b09081f0b0307060e100e06181c0f060203060f18160c08161403390d031a 48
    0xa901100c00c10700268003807428034064804851802081202d205000714241c1112034810b1505054104000080b6082000da10301881b004d0b511008540061182d504071580c0140c0054119403040c19241d02448240b40f4001c045175a0420080000c010408129007100c1c050304030074035a015080d44d4406c0c203160012114540c4a02c4403003803040c55448002c04d601d48500c0d01c509808110505003c160b180707005104840b550700a402d01d60b480d15006004030f00f503600076441d0b151100c2c8162800040f1850704030040c2d040400c1d9814540c808080c10365800034a91445c2d08018541500400841c0142c1da404555841030800580001754a010075802e03455180416942c41712088802c400b420003881c81964070f4009160816071151030500d076041c0d1102c2c8074041c00019103884001751852541d03958144010030000d1034007a110514200000031802e08c00c4d42c0d4a0485094040040285074481c3e0042034500300c13030b040d9007800102202e802c0500c0c03200b504101051584104a0002022480c08030007195201 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 713340602 1250 713339352 713339359
    0x141b0a0c08030901050f09060d060e0a050a0e0d03151e150c080702010c020f040f0209120102160212100f02180f031908120112050d0302090d110111100b 67
    0x30641d4540903140c40384919440980000c804214503c41450b06d41c2c000d085044025140525107860a61400c04803100768020200d88400f000c184039943c180d40c014a600709d08200301c00c0110031455407142e030382d035130f841c0300003205164880c1a508025000c645071304e4010840e250100c40031009490a80c0c400c44050b01174900710341c1d0800e4041281034441d40032001025480003441d4508010754005640345220294100da202c0e000807000440c03030b11903000d0481c0c05004481c0260711041c91780c003044807500c80000540001e0784140324081c2c001e402c41a100c803104d601501c0017541d40e005920030034102a48039070081c20355403c10b10610300062440d0700030840142c0d0704040007407009088007000464019403a07441e84c141d0044000020041088212140192146603514640390000c0c5131200001030991003080c04400c5400900c050260501c8000005c4085240440c0b51040403000601910503425010f0800e900054440040d640260303401e2048140d484112540d5100742c0340894043c1107803544a502 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 713341852 1250 713340602 713340623
    0x1020f0a020601090605010e0d05010b19090f11120601120e0c040e030c0a03030515120a11150a0c030c1a0601020c0a031509051f0506010314070f141b0a 67
    0x607810410705c100003d84605a5407002200406000c00050020f0000240e83d55540c0701480100c3d940d0340d020340304c3d50b8000010710404140c6000500b008945401200207482c600b400d070084518a01c1c541260202c02054104100507146d0200480740c400c202614400490701d840e2a0721a68503001410003104041203c090000c603400b1024151a401610300c0340c801640100b01c1c00300024020307080680e0102d044103c40c1030b80350440c2c00254603020865041081c47e0002041c031170074840f070024075112002c1c0c10780354801039207814074106680344a03850301c0e1410000c0c00c903c0c0b0000c040c07046005111803500000c0d4081080e1040454602c116819140719016228081000d0a02e00b00408103104480e040b40460104071010509480502030100003124a4000e20103200c0140d00e00a10351440c04581510000b40b52510000240442d400f644010000c1000c0380c081025080e8461b002c1c0c119100c3c03515100410440181680c40103010b5226800d45903a00020002084840020b44038042d0340105200301 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 713343102 1250 713341852 713341859
    0x503010f050619031d15010e130c030f060b0a0b18120a0f020f0301060618090b1c060e030301080c010806060403020907140409140a0b1503010618050301020f0a020601 73
    0x102c2e8802c3e044403c1c44602c0c02002204400e009900014a00d104140152000b4414420803410b0000c481c0048403c4000d00005010000100d114250b00401c00b80d0b003032481e43d5590704d0300e81043c0d0041c400200302e0024240d1407010001550004032840901400403444192900b44803521074010344100b08a070301110f43c0d00d0266240c028140d281d034640c01c0c0060403030304480381c0702da0407040324071b9000344d81015006440e070415803000d02c035400c000d100c03da40b82c03180d004150140c4d00c06040d95a100350f94003800d02d2408655991340108100701400440815002290145071210250078080c2d602e103036502010000003100000810b146442003400d0381c60308160340d00c440420042d40076a010182d00001c1810002d54a9400b490285440c44980b910ba9428241d66103000340c2911100b000c4002d45c2c603c51818408083c0c00340c010348090321000caa10940159800b422020b060005100b031302c00308042207240d00040c084460b5100040c21025000395558a0315400d00c081a50201002900601c00da10000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 713344352 1250 713343102 713343109
    0x409060e0f0601081602030909070201020c19170c0f0f0303070306170a02040b120a0309060f08090c04180f0c26060f072006071e020705120106050306070503010f05 72
    0x30b1040c0c82c140c590b550b00b51201c0311803070003022100400700294070003007003442040d41d074441245108500035400585ea404860341200d08043c071080d020702c080d8418100a0340026116030003104000703413024185e40c0704e0815604003890040c5041c02103800e030041c42e1304407001d400e02000443c4240d031a40c4081c0320300c1d03503140340c0c480599001c440003030303150342214007440018a00754004900b8010010804140d480764054a603050000c1c000e07048006c640d03443c13010441e0507003000d400e05109066003403015071460084038140c0c03200c40c04104117104513640c60014048803d0340c0c03644001990022000b80396002a07140400b0040c4150042403021806940c62850700713480b448940145c0401200904061745885901c2000b030203028180005000040c00450712114001ca504d4214045d0003004200600381640701401c0d200c0140d0b450303485c44180d04442d00f00260005003800c2190025111490258480c4051500410880d00410303803501820091040c000d81c4007001d1816550700242c45540182c0e1031080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 713345602 1250 713344352 713344381
    0x916080606090a035606011209080f1803010e0102190302090612090a02010305070207120809042711010305040b0c071103030a0c060501081204051003060503030409060e 74
    0x310380c40f6450343c030b0600003d08005070b030100940100031000c2481007202c0c15083c3d00c400c00121840c19444840c00c0c821108403801104c030703110038107403510022401d01c03000080000d141a21354280c05a190315000b803c1003520001c803640c001000c6038440d00d40d0040e104040f200045d040c0c895201b9801c01c904603440c184103100310785010b00003200c400041d03601e15400741c000c0d40011406035404013003032207584901c030604401d9601c15446c581c0917164000007840054101c0d00b000d07002804551001c001800610000c4d0503e4501d10780141041b81ca803440c034000240580164050f602071684c10040c00c03265001e4010558203079a1080700030916005503000110304a90b4101d030050844406800411660035206000341440c5000f00c5860007800c6400e40481c0c9503a001d40b0781c000c000f520f003032080780c2440380c14411640540390704006000000c01080c07121700c617802507018041c466104400c01c4401d580c025131111004050103020349440710f50700d12103076000381442d215900d900c500103000a0140400c1081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 713346852 1250 713345602 713345617
    0x903040501091d1b1c0b18060901121110020618031e03070309050f1f0902090f10030f03020303060a060528090b04140a081b040b0d020916080606 64
    0x43c00d888583d43d05000c04c40b08403260750b1084200d036040121644644c18140078544081c503003440450402c07001c000384441d80252a413003440030340b01803041c0455a0f4410701e000f070454107142504941e600490410440070540303a00c0f82c95011141100b60314405401182c80c030300c2036607103620b15002c86140c2c4c00c04540b02d10800310240701000a2030740c200240903064024503041050b61a00086003903040e940d40386001e11400d06a00b01e64007107030108800c032851020b01e1010708581c540030b11414005601041144801070080b024151716840080d110800d1209110000c64001050091450450501030340329031003690341c80e008041c040c00210b407403409402110f091101040c8481c410001558414001c80c1c01440c900c01044081440003c4650074200076001038240c10720f42c110f40c00006410006501c806920a40d016005110a00c007108500071088081d0070055134085081004440014000146448025480400380341400444c024030040c80c0da44120544442c1c00d2515401d040001c940a11072 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 713348102 1250 713346852 713346899
    0x6042d05032b0905030105100f05030312040809121207020f09040f0b0c0d0e07140102060c1632010f06270609020304120f0306030b01170f0105090304050109 69
    0x800c4042e100355a03003508550359040e1400301001e5403203400003425940b003500d658002003440e45003484950003801700c000c0249802c5000307524206ea40034280200c400d0040c4003410045010418a040d0349030a40000c0007258418242e03504a02c8103d8a000c0c43e4001d1350050b03018041e07560000c83e035410721455580c000d613003100c0700c42290b0810783d413084510880241124400d0b24184001684000c69010700401b40a0030350240080500703006084504000b021000350456100005118480c00c41c90b0460b468106485141902070105041100038003040b0400c1c0705542400c5840c00e400080100c44100c2d802503010000d00c0300180068070071003a21154000c1d0711489071150851005940756003001ca000480c1c415004c20002d64449041040ba013040710305889003071407407100f003603031075440111244002c0950500700849421600d401c4460179050159030b501d6403400034600905501088083c00300b0481600038001807800b00d050035101d402038420280482d40700240461074108070040c412404130041d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 713349352 1250 713348102 713348143
    0x50f01031509110a080705150301032f0324090105040302060601030906060918022112090409020a091a040501050d0308270109140604020d080906042d0503 68
    0x212100d0005154071041115262020b00d8449180e4444c1400c06000346405d0020f4180246807a090140000c18462400c9045004000620001c2c90b09000701c01030000501ca10b2012025421072031340e8405981c0d0056503d44280d00228000340501843c2c84152000c81514003c5074803030b807041d6405c1c3c2c0d07000e0300e008001d0303000400040c2103944240c1c0300c0d1404901039000854141c2e84d8480c6541111880041004884d84d0164031070290709142c40b03c150311030490000381c0c0f4861150340501c6e031505203498410441c800001142d450716541c9400c034800160b0001d0914510b255074218a4002700b032000b007240e6130300c8994a001019032400e449814121a009496411100c41d25541161041002403101e0080004c2d45409014001407296400341030544d00000034003404c0d541000c0d101d000041d1044411030740407004110050701c5280220700c41691200200b80c890701201c0005019020719000001301002842d082e0200381007003118184100041c800224541c0d845d0f40034941c464410403905150800d60 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 713350602 1250 713349352 713349383
    0x1030c02070b0d090f0803091507140f0c030c160501030e060a0b0303210603062d0711010c051801050a051c2007030906260a0b0409030c06050f0103 65
    0x2d103030081100d04021500010440101c0da04c2e1034005286500c107072040d44000c002c205811030100500c4180018401d00c80b21350303150000c401040d04684001303444003510046540c0020410000648096020000540c1d4440c1c0c0d8000c04aa600c0300000c0305188200201c040001d100e502900c21981a0a2603402910a47c1d58040500000d801c2e02090309405210412210245000c07229003001040070840682c6a5400d28500301460217101403ca10401c01c180014540600c010314850502c0703001000003034003265140701080d20340c40000b941507022542441f00f440c04041e4013034010504994070742c902883c0c100b8614011501030203402116008100300300011000030880390b4151a5800c0101c1002c0703202000780d10400c50a00018601c0140311030089108810140c000e0080740241c01b0b54640b840c000b0542c000300580e120f440d5000d0170b0a03000d01c14080340400200f900080603031000a0800c3c092110340d807500421380f05440a0660b03211b807409001c030304411403050040d41269040041008988030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 713351852 1250 713350602 713350619
    0x1203150f04150e1b07081216090504050a140c0c01050906010f050d06090c03060609050906070f0c03030608030417070e0103030504060807021623030c0307120203150412090501030c0207 81
    0x14081d0f0454003413900c1d8225001019200802d030036882142059101e83d400340f800e000c03d10300504580d200ca000c06901c6d80c1c00b180d00c2600c01048803421540452551510b1045100802e258624a04107006100402c035050119200424203030f4001d00c000c20650742c83c1c0d03c00c0c0e51500804e000d2040c030142e1006080003680341061020305643c0c01104000b40080c1c265446080784181d940c0110368040e11303060100581e0380c1382d100e080c0d0b120016001500b81403034a510028070318104000480140a254030500c0c06240c8640c0c4860098a0782d1411a56035075154130141405d0058050b80512502c11541c01142e144d4600315018121303035061300c503603081074106201039601c9600207082004511510700f80e4000010915805401080484001d0641c403428040e07541c030001e002228140281c2c0030030741d1941a9140082d042c811070703e2032242148408403620009007403c0c51880c0017141c1030740795810700c03091250000300b0a5564a81d6180e281440d5520b100540680701c80c0710040c409a0064207080140700d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 713353102 1250 713351852 713351879
    0x30c15040b3c0402180f040204020309010213080a0b091605010507151e0e120d0c0201020408030c010e010b0108011d071404030332030106111203150f0415 68
    0x1100810600c01c10550240841280600311011400250b030300400d00043d428220b1850f0b8078814050f08103822890015002c200c0808041c00c002c1c001c0d6400800910b1000c42941520001a46210343c0c0110581d511b00b41740e0b489001402c140c1d4007001031804903141c42000114066040c0c0c82c5c0106001c910318140040d03406812500d8195101c1c4503110032003450b100188240005401d00d1141d1807614980500b4020440c2d40c0c400e180c6a19900103d501c03030098040c00c0903500c4c800d6100c0c0e804207015002c1c3c501240a030180b94007248051101040802c0c00344019004510600b2081000700201104540111010759003880382d2f9001d0070713030314101e450145100808241d010308981008200200503000414581d03015600c2900007545004041c104131810102141c5a140000305041d80207031407002c04a036620061003500c0c1402410300c903d003043c0e40c0c14405515100c08100350b094484c82c0c50301c00503d0020010300e6451203802c1e941041d60103440c1610a00740c0d00c04d02c03213141e1545141040507030105807 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 713354352 1250 713353102 713353141
    0x160605071a040807060509031e0d1b081906031208060111160e0c0a02032b150602010e0a0803011203120203090d0801080304031e1a0405030c15040b 65
    0x540403000c800103079600a14041d4000c40c440c041c03c0380e031208107081007000c0710405010000c3c84d03001000f5190901c02103001c280c02819002402d10b90712403402c100a8002d00d5002107120700b2000d080300003050070b42c008141a00c2090488040601062003012a03c2102c2050000500713a83c038a0300c95038255889400803691090060400e026940c20070900246070103160035001402c0740707284209008240083c0007580c0c100440d0390080b0708280000b500a5140d0041a403420b540340031903800805600f044143e41c40d001c000b1190104515034854500e080483c03441e0191030003660074030317010307000000380000e07081001a040704c2800e0031642002d282c130500b14071080c429803c00120020385140868030f0f100940c0612100c00040c8001c5120001c06807c6c7d64050348900c0700d031382082c0300c200081b4a414422403a1804509090880b4081a03d00038403e00040c000d40c191841148007004100940000101403e0942c1401c5a100d0049800c00040c0d00c0c00c02c82d0014484d994110120b442d45013101c044a400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 713355602 1250 713354352 713354363
    0x30604090507030b070f0c02130e031324051309020c010609110415050a14030631060f0515091c2105030411010807091e090e16060507 59
    0x284025403a040d01e03007800c2e5002580e094180c50280085541c01503a600ba400c0f22a007005600c001c965000580010b8909192121543e100e684d09a040f140a000b282d04001c18861107034281070b160000c030b800a40c80c0040e021550740c60410030080490260087e69112826500b050701e04900f0100000043e410a40682c2d09a64807604081032820a50180c80d80003110400c1c1a9102c80c94000e0704500004d403800c15034248a810083c0052407540031901d45c0d4618901e00c5a0703541c0b41c44040124810074000301022264508010310b0200808070002d81e0103030041003c00900c00e80c1d8036026444221a0f140c464140d0224012075030003c0d59080742c1c05483e003854001c10211041a020004103003924415800b160582040a0320400004105400d00d40106c681d207040c908518090340d50044078407000700d07403505001000c0c00142c3c11502c078000d0391000c0d0050038401c21150194482c030b01103c0c00c2e140204900030341041c10588840100150160594060120070b1000b5458040b054850740d11040d402d880 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 713356852 1250 713355602 713355611
    0x1150e060a1403060a0b1f030902030c0a0812070f02090103050604170901020c2803050d03050f1512100c0f020c15030f130204091202010b0f1011010e12043602030604 73
    0x100003a84078800d0070061238801041d40c641e988101400d021038980441e102c1d20078030409201c20700000510000402201c00708551755119030070141c0c000c60006400030342c0140d9400c008000c114001c20b2160180c2d1144500d44040e50200e401440240034002c480390040c2d01c0321204541500d05400d038082c102400c00291101e41d01360a40d01000401d25400640b1117a0145401d11055585031042c81d5020a07141074041490400480145070003072000c0001d489680c00120781040b0030414001c3c0030780483c0c51102000f60040005014040c80440b180140240c060401d9806c41d41c24805410b155200d0065a418074646c2c500c02080c280c00f0380540a01c080070040901040140c803644645011a801a5543c0e41e401c0e100303041c000d00395200740030f469000e400c440325054500d80781c01c1c07101c1c08442c10a040521102801402c0140100031504a60031140b05182354440c1490121000b030041c0d80040c0194003900200c0034a082c2c001380340c28084030005210507502500204150b014540100c4010004203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 713358102 1250 713356852 713356879
    0x7030213090c02030a170103020f0603091c0f09050105070b0406020f0c030705161403070501030f0b030a0606050f10020309041104030812060112060f0e0901150e060a1403060a0b 78
    0x101120011001c40380540c0c400500e0181446e04000590310090600c10860300a606542c041601110341c11030050248502001159100c4001c0c0a2002d045404e4008a041d00ca4898001010303c0903004100b0b0100782030100105165200b032080b581704c50b0700580a203085483c1d60307441c07100170340c0f02d81c205840c1d198060085508840081c00200480e5010b00c0051045031426001c01d00d51211a40c8030103400c010500708100d0585001c00e0540c01c035142400c00041d00c0580c49140b8024000c144201a4180212544401080051760140080d01c00c10b03608018003400f14002d0100120382c6821203c090b0380107102e00035aa1800390050074028081c00344060409950f42d07070304120303500719035151400402d01c94204030a9581c01030941a0322500c04005108280c601362051004840c00d0185004440520000071300650013500712503000d4010884428140b9030780c0d070494000c410181d4190744544c2c505000040ca1266078150303001d490070001c010b009152150400c0c00000c2c442802c00d20303000103004882e00c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 713359352 1250 713358102 713358119
    0x901030e120a0201050a02090117220c140102030702030a17210603060a061202060702240a020111130e0a11030907081005012105010f09060b040c09060807030213 71
    0x10301d151a5010145522420000400fa0a484004082a9080b4030501c83d0b0004c982e48100200f1446000252010403500c038089000d2110505101d409003110411000200300f1a02c1c01502080310700c9040070143d40d0007002c004903124418008040e6150380b0054054012030300d03040c10501020210011545464107a52400300807445084030b00901c10505402c101440c10b00f40039a6600100084080004908021361080b0003950781030045d0244ca40845c1c074000710b407149000440e444100122081c880602c070008a41c2c2540310204040065007003414103071100c00520700340c0ba2101c079071200b5904500c0c105030184601c0580246200364080c0c40c0c10481e1000160031000394000d103004c87c0a000d00c4e5080049041c6080c41c042c442c13021042c58800100050070300c106060b094168601106030142d85141440e5001d8503400100c03000041c6840c030210100701d10b0f80e204880300728060700c060025009036003090710400c925208590202d42c2d05400030324114481d900400d04e202c6241e00c3c0342e0b502a2140d440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 713360602 1250 713359352 713359363
    0xe010e091c0503040b060a05150a1b050a1a010f090c051b0d0f080c0d0b01140f0d0608010218060c011d070e010b2704060b13030c0f03050604080901030e 67
    0x50741c041180001070105124080c02e038a070340308a0980300d00c1081458800803c4000d000440c02d496040d0000c10000c100320b201e50541a11851a81d2400f0f44074401390600e50303100c042040c0c0840b04410480306540340d08185492290407900b10364241c25249103420315a20281032090740b00000c10004201c040c1c07500942100c003aaa01c0c840c0030040078040c114a802034801c00300e5091301c0003030000e80c6c0c04000e000503100f0201e070286608600089005500c4400507201035035031400c411410200410322904d480e041e40050a24007850401c20300039950b42da5841b80c201d1007607035665980030406a803d4840350400310010151040f42000000b4202e2024076034840200704418648070341d4100e4001004210030104407076024106a000082c60301035140f032100018041c80c0c1c0121010700c0481010800350342c132940b01400500303040c2d00459a98141e802103d6041d103e50204030f82400c000407020070500c42421505080e030354404010509911141c560900642000182904140d107401c0000c542c0a4207110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 713361852 1250 713360602 713360653
    0x50a1b0c02012f010c02060105331308010b1507030807300b0f0307051023030108030903100e0a0305071103070b0d0605010305060d0305031512030c01060902040e010e09 74
    0x1005c0341d00420013801c0110607401030f403141c00c04590743d0b04241000b00700e17100320003285400556460ba6200700603d080c0034140382c584400001c4d001c0092542c1043d048410006000c5a101c8207803104503060369401e001d0350350040c0011b03200c10300054a50740102e641c18152980002c507103c00303e4066156078080800e1140d5100d610381c8503e0607151a0500c024004145403044020704845070500000c1000e071008103144508004c8a0b0501c8410740000e1074251510710716540c50b2079a60368607680c1341503483e03001403e03881c041e04c00c41c0504131404003c0e104080340321043d0300281071a4180d9441c22501034000203016654250707401044a9980d604203d81d900406d4030074121610341900080400440e034082d40454181030903c400c10043e0364418020350840c80c0d1508256890b51203510341d8040080c200d0b640140c014100003201403981c0d000001420002c01f20f10003d1051a40382c610038016070007140b182d000c3d030030500c0b401400300598000711142e001491004440c0b5a040300748401580008801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 713363102 1250 713361852 713361947
    0x20a0b160c150b0109090905031213120c021201050f070509030304080a051e1603061d01060e0603120c0706030902060d09110915150306031f050a1b0c0201 68
    0x30f180b81181d40c000440030010f0404a10030030084a603515416183c0c82122240c0700c440610b00002406c60303604c41c143d1428190404100300e1804050b1704081d02c00008140103070710404003001e201c165410140038403486006218441c0046854040b0103884a0304501050380e49800240000305040c0020041414594050b00080083c0850b01c0800d00100302d281c201c800b9640c024000a9001d9905c5c0c3c1501c40c1200e0740402d00045500c40705850f504041c2024911b5000740d400d0500c0040c614007200d1071140100d00450035a01003201c1161600c0051069004143c0d4540010400b005490b000358482005140060941480e00841c00e4980c4121041000f046500c0003e06000390303880c0c00c01c1844558881c1c896091781c05094959000542c89101c0001951241400000000c1042d10148542080c041c3c4141185101d4107100d501180a01401c0742c11180302c510b403090b10b61020034540c2154106000039110080041850307001110345840e041d011200185031100c480381d40e111042c1280c0007540c0a003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 713364352 1250 713363102 713363111
    0x4090e0606012303071d06120420090f07050403080f0409110319050a06080a150c0e01050a08100f180509030306010e0d0c0b1306080106020a0b160c15 66
    0x601c0090304980080d201e0900c88145000300003403803030b110811260000010b041900080807170203200c1e050040c140055a810040203c1e500d802c4510110002e8011071240ca000e84441041c60183c3c40403400f94001d05901600400200d941000d42d0480a504007140b46407461505840741c8821482d50f1101e2125203045100040401642007184034104804c048040d54900c0d506001c2c3c84091111182d0a44410041e0b803040031507000c4206034420801481200291030040400d410301e451003070280441d00a101341030040c0c2c10a15031040403040c060070350503102c0904010600f03104640e8950001e0180c00d4500395000085a00301e45504180c004009503101c842260018840d12030903594090070b64a40303030b8000d1081c00956030700481203da8481d4280c444014a03039007030038648540e034901d500a103400900022400c8403030041031a083c050b107485c0e40710306069903aa294200c0c0d031501c030f00c00058005c14640707002c5900711a084201d4503169001d03142032050102a03803246604d01c50888001041c0b699903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 713365602 1250 713364352 713364361
    0x6060c0f0f070b040f0e1315060905010e0702060c0f040305060c0714010e030d090f1a010e01080d02030a08060301150803130602060c0f1608340507031704090e06 71
    0x1c20080b009030000c41c03100c80c149490101c00480d01c10540c0a012400e000e00000100d900e070086107440002c13034000740c0001010302440303204002440c00b4001d4030540d90a08001080c003013001d04600d40558000e80c021710440e95a04d09c43d00258000f40c43d840c0c102e82c42003000001091080000c10701800b116200300340e40c0e205900d40f0410301810701041c020703143d04003080e45155020100954900d03d1000c2d00105140e0454503208414640a040062040005a8443d40300764848614507061b10a01c4031507004698071588081d541e01855405000180e000700000e240c80d0384105180e039040300300030b400400e401c0c1e086028440001040d4200c4180343e800494000b092066140c130607001060603001516140c28030f5045940103100e801320800c9040710000c2d50701548140e810029091942042e0000e48030640608400030001001c042c04e20a800002840c502e5003040c0342036024010762080007064543d14560b5610701d446440d0544941c0b4110600c0009240e00c0c2901861800780e10220150845140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 713366852 1250 713365602 713365633
    0x50312070e0d0b0711150906040501110c0a060906020f0a11010609060f03061a0a080d02010c0f1b0201050921070f0302010f05030a18050102070b01050609030703060506060c0f 77
    0x81d200c14840c03141c2d94004941c1e0100e40c014501940108180c90300c081010401d4825031315081034074003000c5403078100d90100600c500011800c0c0f4002e1b88920003d004012011600f00e6640c013840d50081c1e0a50402050000081c03059070006040344e12400c005801c11590004006298000902040108888174407003604945c1c00c0c40703494081c09040c00704105060920304000086007003408000e0505039100081a00200c800c0d2001e2030704900180b2408101e0380312421162250500782c02000550b007054100144c141c0144461a03100405540780700c0410042a04411659038414060b414444100324000041e1141c0060340304030300c5030901c0d80190030101c46c0131615014040e44001c0e1540240724040c00181c0e4011159062031310b891404640300c1e01d0f00400c640080003102c102d2442e500b0800d10000c208101900178028003802268003e0503a80c1e03801c10711527240300322604035034180c01c0040144005079595002d10b0b00140041e2603541484042170703150349000c4281314520300f036506c011020f107020304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 713368102 1250 713366852 713366867
    0x141306050c04060c241d010c08150f010314071d04052203030e07060f170c040b07052d060c0702030a06091115031501050f040909030c05031207 63
    0x800c0000342440d140c43c1000040a0a10080c0000c040f030505503000389060b40709106003201c000390803c0401801c00500403203c80b074015040002c11035401c1c54411800d4500a540ca00d10854030b400f41c800f00312680b80c1c2005202450442c081d41030503034039006d0300f241403c00744204c0c2c4203070700321b46a8511003100c680c0000d41602c064404d251080f401c1500700a011826404481101c50000a15031001c511900e410340180c51006040d00f4203128181e400100a680030000040701882d5865400c16401003214011407540b04917590010b0003010001000041403d4000341b050718056401c0c3d6040801002c60040f0311145101601620303446021190700d044010f01c14a40c2121b10074642c145025856400300b41c07030300d2190b40c5c090005075503441c00c00c0078840004840b681c82800100065541869481d2844031a0420765003041d2940a40c4900300d80d65015030b0850b1b06001400c0c4900d400e10345041042030240901c201d08400304844281c82d100010010409410f40c081c281260200ca450000c80050210 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 713369352 1250 713368102 713368111
    0x21c05060406140a05010804081b010519090b06060d0e0319080108150a0b0a050d050105040b16020a1b0506040303020c0306070507153b0613030807080601020114130605 74
    0x103031250440c3c9295615500c0c02d104a03802800d0801490750f031420200742c4c50003400000a00108a404460548041980060b200d4407a8010803112000c2c00700d03e40301101e61904000b800340d00c00b840858014034104000e4008003482840105450000a4002e8116000761071006081603614000101c2d0581100805002d008104014020407510f901d4084050300050b04034011a56500141145a02c410303e200010b41405083c0c0e05020385249000c82c001c0c807045909481d21040100855a0001c401d5484098511a0340c0104a0f80105441361107408540300100000100c004078002501d444241c0640011070003034014200c07030480c4006050030104001c2c4664100801081804002440f42d092103c2e07011440c100000c49807143ca8889085100703200f500400351602010a4120240b07071180340f44105440030a8404a0b00e4411142c06d42c0c14104034002c0c0450084400154207a00c61020140d20100501c004940d01203a605a42e0000c001038803200005c0070714a03a0a000d0203a24060b55030031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 713370602 1250 713369352 713369369
    0x120f0a110901080610140f060406050304050f010c050a08060f0d05030a030501050406050a060c050a06051f1e03141510080f16060c06020405060a111207050d08040501021c05060406 79
    0x50720b005170b00068078510501400d40030b00c4070510000d800740c03102080d0300e00c1e00d500640425907660b1102406001c6030001c03034081310144180c0007100c4441c04103000b2074805248076210107091180b030100503a408000240200d030803200400b0000442d0355034807552903061340200c001d56a20f07010088002c040d2a0305801440c0074a003400401c0103d038071818040000c80b6098641501da83d05175203896030900f0f08021000d0151810003043c00b903c5074189002581c5031142c0000c4028035130351052100d42c14a0038800c00050030016600800108580f0440c820021140f603080d200b10044041e0350208800007a950490104841c90081c070010808000f6018415000002450480380d00b00c1d1116120006005081c10052403203402c008000c0e0320f406031009000001c160a44503050400c0080c5496000c0c1c1200e1400d02c614410918080310410403139080a070440043c1c0300c600b103407010544101001030700072240b42d9402c108140d00385034810000d010511800c140842c150510303000300000e03107203d03400c403041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 713371852 1250 713370602 713370613
    0x30e0f0f030f0714161809021309080408010c020d090803130b0c0c0d12181409071b030c120908061f030b0705030601090f050f120f0a11090108 63
    0x4060001041d00c0065040301d02d110303030301c0000d407030050280c00c3e000301e514429214091004496801803036442040d105942c42680e03050b00da141901094940010020b50415108d054003000009103403c00710b0214040e4066502c0e2650300c00c40d050071074080c507500f0b100603084510307031403c050f5000345c8180003800040011030034600707400d03601d10706043c492050483c82100011281d082d51070501183d680c860000300415008080c0e400c1102c041c226002607240050716225007801d400716a404880c09907050201d60851400403501449440310b4040c002009000445440e903030701c0c42203081160081031081d501c100d01114685040e0f000da0420805520500c00107002c20b022809002a141d0760201404e107c032606580844920400117039160005007170544000200010990060300a42c05100c0aa0300d00030030369610184601b4038045801010b40c840003007003070364100e0300e001d03001c41c01602a84c00a50307000e01c6a10344054580705100e1000c981101d03190901401603e011440140101078a801a1a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 713373102 1250 713371852 713371873
    0xe041103090c0f0a05121506090415051509040f05010b1005091909020f030130060506010e04180218071b061b030218010905010801180e010903030e0f 66
    0x2601c4205a0b6000b074007443c464090b640c1e02da0742e03040070b0300c0061a0151035607161001c0003400a480e01c1c1e1102101c602c107204400841d081d410000c400c944503a402500141e00740104080c039a01411014106c0c03100030010910100fa0780c0d03521107500c2c4c050380c4141607200340584549015401d44e107000c0b119601c154000c00d801142c0b5504001110000e501c00c9903001c03001201e02c804c1060300701183d0032441c10644080303590440d144051000358180d40d0b20a0031059034015000c0e54101e42c42000c52011594039410032648005045504942e03003000050400e518006c03600c03c00310b4100c6540e00c03134103249010801c06100941c104000c0804c42c905400c1200c40861601200107002c100341c8030301030030032050402c01c00418810345a020600b0009540c41844c0c603074145000003006904503003081d170214103040e41c1c0e894072503006886103000c581068444403070703076032078404128108000401400c079002d4803003100b4450a00300b80310702d27604a8400c1d2800218807005500e01440c00c0f00c1c00780064035680c403042108 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 713374352 1250 713373102 713373121
    0x2808160e0f0c030610050f0f1b070b0d0e0a06110d0f110a1b1406010303080603032115040905011a0303030708190902031f050702010b0f060f090d030e041103 69
    0x50344d000030291024048150801e208552030310507403000c1d000002010480c4020904402c00400c6140ca88d02c3d40c1140419072503a087c0c0e102c0300c903803082c0181e01070b08000811b02c50740740c2d0f04000c0030501e002047d80c4d11290700d0b4491000b603580d80315200001440004001c1d440040c0b03441107900183c0034070003c20001e008404000c4052080c510740c481407000ca5100c100702c2d00340d01e0807900e074a207500007a108100d503408407043e0b60300e042c03c2c0000c6001c80d01000c0060301c0b9040000684110b10303c03100000c866401500c81000c080742018144050803060038030f1441c4a5141e50149180080c0320348000a18a0505000051620030f000c401c0c1d0310940007003017440522540012216001030300312074608040803081c000400100310480c0000d405014102c0d0b4103042140d102200440c115071100709100f542d480c218100e081303c049104569110018140750f48103401e20801502914411100440c0b404a40d580000d03215040d409084000800c0b0700400074030750906008004203004910440c45c1941444000f0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 713375602 1250 713374352 713374357
    0x20909010e210f090303130f030c2c0c041a040f0605120a0209220c11030430050124120b0a09021807020309010219022808160e0f0c 58
    0x39507146030404940d207625a178091040301c100d400f41000d120300341607454070004c1130498144403e840980300740000042c1101d00034051a66501850710140194112004882541801800b240e03440c030300503c00840c01e0a040643c100006c0031078001d01b500c0d10703c0c106900304c5000c81034005404202d014085044100c00b80401c41e500304161120250703c404024001c48d8040300f45400950b040c503504040c02c821100d0544c0280c035500740310780d41c0d4040078003d85445540c9200741d1140401c108144000070030b40f428000d6030000c14855244200042040c952951402d490603c5043c511020010a003801c1c1c61582580f14001000c1c0381581318840c2c1040c1c2c40300020404003c18480995480c0c4655508566990100d907040c00042c0c80c0803103103404d00e000001d6480e0051400e50b4094841d02c2c400700410b4410b02040a00e165004010040c41b861416011400091815940c1c1d00042c1c40344021851074070030702407110b9100c4007000340d220142c0303810465030950340e024104a032044035450900080080382000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 713376852 1250 713375602 713375617
    0x1c05090a0b1810061805061e01140d0204080606030607090303020d0509040b0307091a0603061f0c170712230a02070e0a05061215150409020909010e21 66
    0x10908050b118490241414084480409001d00d050404203030030101502000d248540d0031030030002580c7d011709120800d42003001c2607081103201c1c00d1007041584140c2c040c9101c5096840514140380d2115115130598200e50465000c50308031408000540c00d041000320780c044180d1410107c030b1440d503200651500485415401001000102200303591034580110030003040c003400311080aca40c0c4480d10b100030080710502112002d0b6144e1090342c0f524051003500e004800041274510340e1800d08c260381d010321078084000700621034070b00c600c4804103803004005141e07820450106595098a8686100c3c544400c4404100b44a60f0815080c100343c0070344c0082844c0001d10302215030b07600300c1c09400da150406507809a840c212404041000c0b900c0c0507005030b4000c036000e03500010f429040d51021074a0781d0010100e07403007140740e1a00180010b110503038464951000a8400603681c8038a8000c81c410300386c212a18401ca079100c00d07692203911810802140f444c00d00b060202e41d8090f81c400711001600c1001d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 713378102 1250 713376852 713376871
    0x20c1f0810050d050d02010b0d02011b1a0c09090c2d130b04090c0503090316060b090705070c0e0613052502100b0a051c171c05090a0b 59
    0x40081d8000da08039451a01401c0001e0002008180030300d00b41c0d60302c4042c060b46100550907c100000c041c148030000d02c4007950705031114500b010030301c801e00f5110f10311100c0540300039203e452000342415079003900500074640d03018200c0d03131151464140a00401c000e000c0d960011410045401c10000200851400c081813882a0000c0c074040c624901c11405103188502624012060001d4030047c020020011504401020300040f000844142c80e54001100d0080e0f0342c0e001007002d21200903000ca507036600c0b180b040400050070040003021818005d0100d400d1404160009071400c10b000c40e000d005001480c0c14503025a941c5070501c08200d000c20707c040d04601140d02c0d8800f240b02250b00800c3c51b0043c400c1a8004503c49a0f1400001c0d5607490803200035014618100005003142856040c000640f00090b0110201d0741090f4110b801440140320180c031041b4040310300c1d5102044510007010003441c4103408082c0c0694500b20042242c0000e4008112640b1441c04080015122000c0070361098140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 713379352 1250 713378102 713378117
    0x80705120f04050c0604090b01020c0a0e0105090c21271b030c09090a02150f030402010f03020903070603020c011107051b010903050303131e020d021309020d05030406020c1f 76
    0xa00c3e2107440c010380c03018880e43c0201c01003000700300b034441b0780d001c940081801d908070b030b031024020301c14040c500105d400340c00c0103880a0030041c0200c0c01d208240c55004180c11901c0c2c0d01d085020724800b4041250242000013181407107042c4280944ca440c80c01d1290405a65000c1811400d109201d0360f60348044140c030070b00c0820001c091415038052000041d2188050300d00c1c44540340140d80e0b1625910311404c103d104845000ca8540c480c3d071140190b80581801038501807031034a840c0c006440c4040c12a042d0000c064080103811405e807002d00210008013480c0e04c0150b220003141000500303690048615501e804414404140810300c0003c414040e00108062898000c1d41180100c03420f07026508040c0644c4000020300149400e01c14120703c1050007161041d045284030f2082c00d50034051040d002e1351041190700c400001d8500785880c00740c20640300e030001070845500c1e404606c02401105055950f60030104040220310340601c00d17154424001c4a510130118001d4003501040c204511443e03040100c0c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 713380602 1250 713379352 713379361
    0xf050a23090613050424030803100b0a0306170309010203040308090a0e01030803091504030e01120f0609020702191809170708070c0b0a050409050c041a0307080705120f 74
    0xc0e1085956080c406011260b0303e50300c041c5084040c80c454030900f8040d80c540f042d00303000112102141d10040f00d0308042442d115155031214002074001600041100e4440c18000a0142e1908020074404009841c0818a20316000d0361509001e090240055107400030021030001d40ea0110441d8241d0343c0c0b03c0082c6403580300341c5002c00d90b41051504170312809010b0a00100901c0703d1000514440d00c80c00040b81c0307481e85600308603076030b0034001c0c1c0e401008901d995000013000c0d8014090905218000c1400180c80c40e0303030407030750010f640da650b0002640e164001141c41c15814210800345000c402c00307000c0f1050903d8840104004a621442500f0380d6079294145400c00a508090000004401044d241c035283d19051120b4558011002104c018465035800074002c1840000c0c0c80301030380c2c43c1d1100c600345442d1044040190800a04680301c888040001007040628940c0071001003107c10241c3c1c1e1245010403000c2d24158000e030041003403000500503d01801010143c45520072060552441036444 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 713381852 1250 713380602 713380667
    0x1b0d06060306060b1c020f04090203040f061a0301140f1303020f060c0d050a0e2a0303040602010203091b0f0d230102090a06140910210605010f050a 65
    0xc0030780004240c2d50a0000002c0e50a12450140080021040c02c031317120130301c1c003900001c00c80c03060310302c05899050203000800c40302204d1b50146a10901440c440040e000702613440200b02c035920181c48405441001e4100c00c241403d21800c445251014911031250510803484201c00c14020304903445940e0020b800c2c410540700784023000442035040e0072980c142c01c1110604020b40c00420000041034500400604100d5450048004034500c85015028817401022040d0f0b0410441104030446242d810400c061604c007000104000d002c0342e80016100e0402c104100c0c28a105002811500a142490041213960304050000c2e14102141c2140200d184ea141400c25405000100107084040943c00c050310001900140001002121030024498075a0402d440e020815511440100c90a004500d00d40c100304004000008180c20110440310007000940010408407002840c0c594071120200115600000741484034607081c01c0443c1452598480105603203044081d040d003401c0c079489010390070708 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 713383102 1250 713381852 713381861
    0x703120f050c070e101a0403021302130303080c070c080a030e100f051c0203091f0c051e040308070c0f172d070e10060c05120901021009060905060106021b0d06 70
    0x200c802e4a01c001c2c0e0b420750032141516001884240c0c011100391103050704ad54243e10807607004030400401003c00504544003200c14060007886e0040aa50800c0000d0100c0c001001c83d00c0240503400003000704a5080c90f005003101241c10001e070150320540e0003250f203240c001c011200c01d0b03003e51500701e4541c81310b6000a9000810b2a22086140d803002052141c01c02c408250f4070320308248013001c40000d000c040d60140c115900c0d04407141c0005c00034007508490b04d0300301c04038881c41c8402000a50805880740c482c1901a80120802c03104030b401400300b0051403107420000b8000300540d00f80640c1c40c02d90501419240d40c6444072829501c40e0036816890180810000281e450f2001d40454008540303851b0810780e02c1c0c0c1d055648408510703545000113034091180b5600310003a680040035148121f10000c0b803002c140c00154005042d4014030070140c042c07002910030f501200d8050440412188217078101682800c1040c0c0141e411034104110301418512915000072961200f2381c0e002180c001ca070b0910700e0040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 713384352 1250 713383102 713383109
    0x7020a060e0d12020a060e0309060a03110403020a0e010312020a030c02091807090911040b0a0303080a0b0d0c050405070806010206060f0102030c030c210403030e061b0703120f050c070e10 82
    0x4141c00541d0f00e91650003c0e003568550700c90fa074100011645410202e60b64020404110780c00b10041000c0103005101340c00c2081803540795160b2178105510383e0300081a0140f1038000446101080004005100456010940c0c1c6001030028118060054500800138101950068005c01d032400200c4d000d81021101a420120030400361802c1c59101d50b06a0301034690108152103811410f1035581d4a4a000d10424850300340c014152120140f440e03505403200c00005140d014070541d0341c14000d40507200d5404007844c007440b400d03160240e0750401080104a402c0a80306408001d010002c00145907000100d00f03411400864400b0748030321603140100e2840c4554400649580800705019031038100c0091aa500143c101c0300c840103c031048850042c0718000c2c1c2c40081c00050b01c0f61801403290804c1d40003000802d60b400c0340b8855060b030325106a0b1402d105a88203da038120214400030300300b5880400b1545603411890100d00e07001d88800040c1d5286100d0003200b03a40b98034000410398119114030114000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 713385602 1250 713384352 713384363
    0xc1202040311120f0f160e01050901030209041401090302030d1b170a0207140c010e091605131e0f050a03050a020423071701060822060608010e07140607020a060e0d 72
    0x205d00400708441d44410078600441d0321001030320800309205084111f802d0503554043e29502d503682c6140c0800c410a02d02410a845490a226460f810b140d070038080d080315603000c2d40082d642c44040c40641000c9426801c0a1800c2208070342c2c0c0e81004581c0603410001d035905401c000c000c02c1d1075034864103009200d07440004100001901c006c00300ca0401040c24004400e00741c80c1d0f55142049102131028180040721701090180d0142a0110b1040c00f40c2c01400020540008880b925a00c5001040031b0742e16400c41804003e4170700c0c00811200303102030704d5a00030300000e4440354107051940e500c00360f45c4d40542a00900c45c5443e04002402a0501c0c1560052031a100315900c0305420b1101d0702519410301c2c0d92010040207500c1c00007203941d0b40190001402600d03039514100c4031001240b40100318078028501215241d8031010000b030710110074002c00744504020006081100e143c03c0100c01d030b44226020982c002c40d401e1120310096940d50701548200c4410303081501d48078036100b0000d4002c0300d1001c4010b14 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 713386852 1250 713385602 713385613
    0xc020102060c0f031f0f060c0b0135150f040b161403060409061b020142090203090c19030b06010c1a070c060510030c14030304180c1202040311120f 65
    0x10443c0d0310009007240d050127203a0620560340c807141c020329044400d0700000b0043c81c49034403002c1385190041505076022150400c1d500300402803d9111100c2500340da9040d0040c2840007480706010f2030b140101d40101c0341c44604c15899040f8000940100040ba10a081120003c000644203895a421094003550322402c10000343e1040f4581008004c00054040300640ca0018801070640007007450800800c8501520b5440000840f07141c040320811ba0f04200360200c20b580001211501d03400510f00600401015000c1c172030b00c141c00e003e030122407000070b560522841e100c00c0000c54654180c00350050300a05c2c0a8400e140325040800081e1400e0300506a4181c2000c100a51241d214076014011407045100f030080b900c9051002403040752034080500356103102c40081100a81c0101983c80d0180040e09603400d240e6501c1021030040354101c080900c0c2910b5080d04051103034000c0c0c4840c100e00788200c00710f0410707045031103c110705185006040d0060788101e003960203402c010003107154680f0702542144e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 713388102 1250 713386852 713386859
    0xf0510030f02071b0b130e0702010f2901020c060d0209031903020604120305040b060907020a05190c0e0106050d021b0307050c120a0302060a1a100c020102060c0f031f0f 74
    0x61a0108240c41300b111400f8010f0702050507460034003250320411203c40d09080003401d008213081c4401c006846031003036641c0c41075800020442400303140344a046017842c02106082e840c08000d802c0070006111811508003200042107507680d0b5040e201c601320035200060319200290086842d0440751019031400004541e4141e04140c0e000a10901c100c1c8520f02c0718010b002201400d809681c010744005216134111030004455051800845601030420f20440e42801c0c443d072107030360800510491041e0705e00b040110200038040c11000304401400d00600c10940c1d580342c90b5006010380244002d1014140c3c0001d4505803100800606090021704e44040e26582c0040340f401a0703503443c07030344d241c240100f0880c014546403403030105405407100d8140c0c003e0000f07a501c0483c4903000344000940c06203a0210b00703040a034a501c6411503801058080c1d00c41340e801c00c0c954000607160000080240d0145981000307804002c010f0703003050340e8102c081c1442d020929400d031700d84156200915040104e00c0c002000001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 713389352 1250 713388102 713388113
    0x603012a030f020301050d1401060b0c012007081e09060c101b0f03201605060a180f050a060f020904140403022a040516080901060f0510030f0207 64
    0x5440314a040e8404120701025802c15000381c0c002441030b1940320031403004600102c1c05074007a4007000c0408200018000d5250030385071003030360003440402c03505079900c4511401d0110045098036000640c1000542818140e54400240380b24614002d114504494011003e0354150410781e02800c100600440d2207041c1c2070700803a500e04422000c055218207028400c21205030f5109815180c10881c1c0c1c035070080325116001903000d007090002030058158441180501c09541c0c002034402c4c0b0900b2168400101558240789140c598041c01c025091031174640c00103040342c4140202e4a07804c0d03220118451414043c00c0c19414501c591402412046c02d1010540800f52258010004100102c40400c0050224501d02192000454004000d684180300c0c840ea06954100e24a490116280ca80c40380c40031a82c4c086403d450003601d85145046903002d010494540200c801d44d8448980da0003040700718541035a40c81e4400c1148a02030107124942c2d5009000d030b00c40d422000c4a000c03050707406e40d6162a1860013 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 713390602 1250 713389352 713389421
    0x210030209040c050c190309091808040803041a0f040603051906080d021002040b0a140403060903030519140106030e01020c0604050303010509090d0804081303061508010b0109030b0f060301 83
    0x2c000e40c05884169031485030b21009440b29950550340303000b48a8107042441c270041820191502000b0b00300d8800c040000d84090041020301581c601a5072518a0503aa450484900440401486a045c011140c500d179102090703030110f5000c0d290106850700c03100d2280411b609114146400e6034201100801c030b00301c0000e42c0103000303c52542240c0e8048208020b06040303001d18080c111408800700320780390301c0d5445844007050710240700d65260724140e503a13610720049440c0e80e402103000c00e0b202c0d0100305203a80d140d40c0031301d8842400307032060001c281c204206004800b014000c02090603955040986120000d42c141d441d41807800301160510b0400d4209030380d07650800d1103a20f00c1500004000380d00c0180100d01e14000a4040c1c881c1c0c491130b1255502c0c0d501c1c0d600103c0f10811295000440040440d6450048110b0a400c4c0a15058002d05100b081030035640d0442c591810b10000240410000c1c13080c032a0640e001c0340d02d44aa081035142e20000a001d00203400346c0000200d01000116101c6118014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 713391852 1250 713390602 713390617
    0x4020d060f06140301151704060507121a092205070312050406020a0b040f0c0608090708030918060d0501050c0a02010501061e0507110a0902040306270210030209040c05 74
    0x441074030040d611001240c0907409290300806801c01800104000303d812100280107050a080c130302a80680b01c0104404414211802d840d00c644a20901ca08030b904120101d18400d10168180704c50341c44038981324034000002031094003450148000641d0442c8151106110b00890907201c42040150b0800b10380c3c1e444280000d1783c003801c11030300c070381d01c2c20380548200c0e0111601a009484403030b400713440c0c0b01040c61004000342d9104ca000c0084000168032981044050500c517291041c4a041c011050b034900441e6400c400e580f40d000f0000300100e90f40300343c80d110059003080079450865a07207101240d001c90f07992000902541c246000d000d40120882d014018824507940204096130761004216211551416044030581990b5800801644036000800e05580070301c2403000700b060000080392244092742d01819455a000c501401002401c0c018681524814024032172070910b00c81d4541c00c0e003150303032030000e01c550b04002160b42e400b400307a0145c0341c090034018002c0180340401040a00726030b101c101d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 713393102 1250 713391852 713391869
    0xc0a081501050409050703031b02061209060a0603170706090210050703080f0c07120302090306072006013605040c05040f0e061906050303040909060509030406020d0c080904020d06 79
    0x410b5500306031107000c40d9150000001e24102d40786032004c1d01c0e500414100c120340308107410b4040025840c2d03c0001c0c003e40c42c5a602c108140d18081035900d0902d40044c004080c680d00f801030030030100704d8082c801d4803401c031145a441ea42e0801c40c60246c00801c0746820007900106030103011641d45400c07002600342c4a0098a85847c1c1e42d075103082c0040310340000c0f911008482070511061012400c48038001c200440c0d64100145800089070010b441c5c07020840320000061414888500c1210f00c00c0141d4411003c0ba100424107541444210030210a820011070b0041140c00301084545420054902d904080c0403c100407900b440d00707000008581a01640f8040d505040e00c9101000480c40b504200701685800740500d9295100e41c4a003110965039a089003603106c50300814140c3e0180b00420013400414000034081c0700300e00d00102540c400034090011508184800c11145070086401d00c100813031440c01181105032843e2007016401441d13103080c0c10600c046520f0b40700b003d45d644000b0136100303801c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 713394352 1250 713393102 713393143
    0x1e090c0d05270f1002070f0506040605060f040b1c02030703300f0e0103050408040f09020304021f050f0c03040f060c030905040209011205060319030c0b06091e090c0a08 74
    0x8410b510758410341602404290f42c8161184800c40c4019400b81481030b100f492080c00c11032160315110b203010001d50b400d4902a5072441480340c149000c2c00703e00b1a0300b60035107041c0917950000303000a028003600051820910035010900d82156002c0c0180310180d0b9000086402541807420415002c100303a48120010401d51648000f03094003e40410188220030b0b56040500070344d080044000c0c00002e0030407915284280804190b03041c66a20007400b400382d1010040c2c50f8034090040000d158039521201d88405100322460501b5903015040741c050349064000b0903500c0c40e4031b03600e00b0314500c00c660200a1861041c1e60104d1b49a50021400f81824060b40e6a090703026114410041284114207a00d8046500780c0c00980d03249025411455104500805445410070344807440091007684410450001d182480344800708030a642d0020307003040040d140b42d012460140080d10281490a14400017048883e002030900d940400500c2d000550150910002c0396454400ca55030300b1141d8944010300b80030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 713395602 1250 713394352 713394421
    0x1c05010e0307050610060c0b010b0c011d150f011d04050c150a1701080606150708040611060106050906030c09030f0a060f1d0c01050702011202160b061e090c0d05 71
    0x3044d00240701034003d0a145040e92a00d40503941c00d078444880d000141d500c590062144de03080b00c98070240c66400c0d00142000c003071070f82c40200c03980c50020103120502001b10b00500c116400c1070034411000c80362850110241d07c8608145280c03032031088a09a105c08200c5212081081030f002400110110780c86010005d00fa18084826a038001d000f2840f069100e600082d8151a00000300c00000340b90400c050300d40101034496a056078429045500410500b2401342c041307200c100101401042c40b458840d0800341000009070b403510000d48140c0752500c3c0825450440e82c4c040c00f540343d56100030400c0311600501440c1c040e015251600400407414079144507000308a481251804402e10b0070f1000d4418062184e00540d8140c00584084c1c0c100490034091104036084e92009100c00708440c0d150003643c0881d850b03d40304445000b4503407800380b0034050348901d002461883c584801601150300800544d00c401c4030340003074014030b02d006603524185410310080c18072241504028204082040380344511b07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 713396852 1250 713395602 713395607
    0x1503131202060f16052101050a050a0f05151603030b090a090309031202160305100b010509090f0403110a0f050c060304030503010e10030f03081906051c05010e030705061006 76
    0x4044848241407031101c0d000070460b2500502c0b204d014400303418050b06006080060fa8070301d81c1c248195a40c42e6080a0043c00a4505170000d030000303100c11079001c2c6506040030b00c0c02c002e41c0214420706000e002d0000203c0c502031030350380a4451105541c4031300d24a2120038107004014018000e440f501070064240400e4840304203008018425404d03495003072806182d82d07101c002c810201446e000031400b406240040111030070622500a41c05134000f0302103041c80c04005411500000300807414400c00b04100e075051b840b02c0b991164400c0000c42102002d503210308054800c6412080c1021481c09080480c00400c904428030000e403a000e5000c94524000b00c1c014400c0c0d40c8016500600880c0052004210303400000f03450780ea2080d000c080881c4a59503039520181404440c00c000c42c0401c281c001000188540c070312800740030a02001007408641d20b4840402c00f034210001c010a115800c0b100c0c184103000007504040e1050460b40201c0344e440000d030500c561100c81c291603039440e4042c4035000049103031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 713398102 1250 713396852 713396863
    0xc0b040807031d0f0114040909210905090103020d0f050316151404150608031306030e1204050f030316050102090111060f06040e0c09010b0a0318110f1503131202 71
    0x3034010306055081e01c0da4200646c6c034140c2c00201003003500010000807540c0e202c60300500741520310405520405022581086044c848031a13155001c101c1d000800b080155105680c150440c3d80550b02081c20b07644038100031880840e10341018200744000149008048140032010300c0c0c0034003071082c0f0540110031461450941d00c9600d40d80c0010b22808010802140da03440342140e1305c4030103403400141c1d20f551b40072181c00e5800080d000d030b00c4400c0802d800c10406406000341e4403849580700207803500c0100c2d00340c00300060085000381c9015061000c030103a1580c0307040040b550f103d43e4580700024910150700c3c04501035804403000c180001d810021400303a0342c8001a00601032349500c1c200b04102d07922441400f000300010703016034905208402c138030a03891301d5040489004c0c1081528060342e5480e5000701a050304c4508455180d8030366201d101d6408038000700414841c1201c2205c13080185014100040c80e003070f55040200411210000512400380e090071482c80c007032446180c40ca00541a207203c181d80384c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 713399352 1250 713398102 713398157
    0x301080106080307051b0d05010906020d0b010206040f080c070f0b1801020304061d2b0209010b0705060c090303190f021519050c250c090507020d0804030c0b04080703 73
    0x141d02241204961b1b40035036559401d00c56002c0c0284044401d0360302c902d400e40340071481c1540d601c4d500090700c00c09058140914a06c02c1d10030700040684e420a6900e507007130a000100041c040b510080391207a51918180311040040440445481d000307a101c409040144d4040c4010007a01e4a5030510080303a13500200036101107454944407032180c0300e1035184801ca14000c610141e5481120309034541511205d40392483c1c40380c8900c0c5c200310656a058414801d40c0d0b601030304000840503040c010f00002450015180b03920081c0c800850b510b801072180802d2542c003a003401c03900c42201110401d5440341d8401503507181c90510354200c403071075044c0c0001c040700100d00f510558508225030100200490264202a800004180c8043d207001d480300110154224850288012800511051800e1006920f804000360012070350401040c01c1c0b150303000c0c0da90401000101c0c207010500000a047c075000340f03140300c040c41d00192210140e14051074848034960050004401040010135002e00c68200c0600b441c280b03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 713400602 1250 713399352 713399363
    0x1003060b040b09030712060e0c0406050f12013c020a14090d0b1602060f161808010614040e010b010207050409061b021c030207050d080a150b0301080106080307 70
    0x1c2030305007075038484140d000f1241a6003500c140c8100007075083c401c02141c0195409400f000644c16210498241481c0360444030500c81c42c100401442035946e200c20101e02800211f484412410070304d00300c02d02401c0040410603803181003811a5600745656500304106c01c40d070200185a6250803800c940c120b001d84841c0c3c0d000100003140c00c051081d4044020026080c0c0188180300022a5640c0c405c0c2e4010100c4110440300382014030202038540400c6810303040740e800046c05103d890034440e02c00811000c1004401005860310620411358884400c10020b4003690000303000f0b85442d0038180030244000403e00380120b180044c00340803202c061059401e0310740c05034090001c2c103141408100190441c95010b5680a9403034080e5211180d410740d50307a400c0001034010b0302c0f00080c024030501c000058043c12000380350040000100082000c500c00b03400d0701e42403c101410351a03400b02c901c000c00381140c03c00c501c1049140040b92984511000e14121002c0310001e205461325012401c2d00c0b030242c0d900007401d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 713401852 1250 713400602 713400607
    0x61e11040e0723040609060e0d111206040303090c050f18091906090c0f0e06090c090d0f0c0602011a040203042607380606090a060207051003060b 64
    0x72448011020a410040b03510303100300141c2c00911103003451036101d180c0c1000d0000000d030030003005820014502c024609805c0c0318454448110203c1c0a0350307141400182062410101c80e80c1a585281a00740200d5001d41158014600340c0340103230040986500a403600b804540c3d001913646062860700302040b0b0003070400e4194142c56442c0300040d0368080e0010046001c0c03003d81c00740c40425108101081c0c1c0c09080045402143d43c20400c031078501c1c64020500e0302e42a00c0707060100c41c0400f50b0080d0049029281c0c00910b030341e5a8559126402241035090b4011810600c106c240b0008a0151080502030304e4003d0040b51b49040a07405c0b50404943c40e0030001905981040e00c0c60300c0d070302940c0d00c1406121040a00202184502d01405448250903d40c02003c100242030041020340d000171f141e007a05404491a482810307122124040d940c1034907075140160001012038490006640c040c3d040600b00b271603a1030320f4000180d121a01030154a020311701d0f02031840121482401500212007041c1034061 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 713403102 1250 713401852 713401859
    0x1401060e240708040e090105040302030f03100b03090c01030501090506011b11030609070f060f0903060b0103090506090c0114070b01060c060908040902040501030b030c031e010e0703061e1104 84
    0x14400c8140c0c1c1d010259035965500250621007000020904144280303021135545003448205281c00401900c03030500f50f0f24082c10000020380010448192090040f03c01da26555001e4481c0301e04030054000062050021080c03006655000030000703440b050036202405a41c2c1c0710f5004c5007c951007103a145001030000300301c1500340100214929801030144d11300361992454040400c1c40c01a0a0300c11b403201d40c0c04100200704d00c995200f200000340405240c80ca840000341e4000800805032400052705207030352500300c00c4984c0c1c060b60240618690003010b0f1203052a007210100d4940001c1041d56020910000c0c1300b0365254103c1c41224820b036448250b07031402ea420100c0441c1c1403001d8541c100c0d00c9a80d611601400b240303070000600000c0c0719804001d46d455040000050948406a84041c000c0d442a03403040c00c20740c0c0101e051a0991050300740903c0c5122140c0c5003e015111109842280307000d84900030090001c1034010319616000d07461784001c0300c129000c0707084c00c59416100c10729101d0003c0c401803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 713404352 1250 713403102 713403109
    0xc1505041518060903020c01081006080403030b040e010e010507021b1003020309101a150309120a03060504050406020301210305040b030402041b08060112060e010909240e011401060e 80
    0x10b0104a15030904410062483d544010444089040650160b408291103002c550ba100c0012907010b209004c0c0f40703c1c1989402d030040c044403c0508014207150b1144505415900c49030703c04a45035a12800901c1602038441c2e44070b00030801902c4400050050758001e0108848410003440c22a0010701446610400c4940482c0290005000f4040500649542659105c92406040307001915181504828406c0da01003252407045c10490160000d000e008001414001003010b1010b4004580e4459450741d2a640440c000c0c1761503000540d000389004240002d209050b4040c40c10313524240c680c04501d0180b80b0092000d482d20302002030000700c0c204001d200d010203940c040d6410502c060000704600d2440a50070307494010009002001800b414108003813507a00c5400c4500300c00c14810200305d00360525841c4030000b0814098100b00c00d80702d0444500300580540300c0340000c444100c4ca00400014010031380050507800b003040500c1d6003030000030b1400c4215400300c14122002600e412030f43c010b034039090 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 713405602 1250 713404352 713404361
    0xa030f2414060903330a06050f101205191a10031523120321090c091b03072c0904061509020406020d180803040302060f190c15050415 59
    0x200c2c500c0901030380a24140c178000700c5a80e00a0b41c590401081c514104014400380742e442e84040d503c1036401011703d0381d00d280c019424150720951010046a5907460340700d0031010141c0213600d0780b101441c01d8085040415440541c0d450100e040345e04034506581c14200b24291060001e81400b90240c00b0f0042103e904a8004075921804606000740f00320f02d0080001e61058014004151681000490b00d0500c0c03041d11845a24140440d030b50803490410359040c80d690b50000075000e008482d500041503210325100105803002c0007905907140d60b440c101c900100880035802c10b0b909403200c4214440075819030321100b809450009803c5803826a80c540b41c90000d4881400200146112408045000e1015000a0002d413441e6001800c1c2000607081c010181902d9031103075a46940b8032a0306024038030011085030201d94040f079401e904c801640921b25414030410f1130020320a81c40d5091081c0c116084441419528014040c4807a002034000221040c1c807400c50b4010401d001d0b03040019000c00c032030b81c0b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 713406852 1250 713405602 713405653
    0x105011205121e0403060b01030b090903161515030213021e030604090c0311131103071103040e010f030b0a0b0a0501120e120903060601020a080a030f2414060903 71
    0xc40180305030044102403101e80c00364000380c07030300747d160b038100036865030035018031841074071b0503072f00c00d5817a15148120944a0041c8045034622080701d900000602a04c2d01d0b0700c800000c0380c00303000c1044501343c00d4a29686082d6101c202d0056a8041070360350802d07494402da031480d608040401c0c0c002c9420321900b0301540c0c0001e1110390301175030741c1c4500c0b0046000d1080d01030295200d444945c0d002690081007100300c005001000285d9410b040010107000780c500c0950341c00a140d400d10440000d1052036082c11030065030800b044818901c400064103040a80080f42105d004214642254442003900b609070f032800840c040e00500800e40c20405540f140342590000c114054001032140e10084950742441082051050100804500100c1c1807506026190b00100240001c1400c01401d42c0c81c034025018000380c0c0e10a150382c80008409038903640d00105454103109824481b0040d62154018140d4498010801c4a903d1500d00d0a401d041000031103584510040c004c1003081445100c6c1c2030b01500c2c0e00d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 713408102 1250 713406852 713406877
    0x1a03030f07230114011e08070515040510050a03230412121406030c0a120311010603060606080a1508100207050708030c030a02060f130f020d02090705070203010501120512 75
    0x2c542c400682000c1c801e138441c4448490360040c040d451301040c800c260404081686e100f0800b050b04025005000500c0c0d0110703641511200801c00690305008528006e642c080d80d0090f14568084480c264040000e000445041d2400c110340b82c004003100d206009003400b9404010483d0010130080780040c185065840e119140c0356411914000050050305d641d01c1c1c240e0740c038283c03600c240301d2245014051030100f0301040d9401c07a281441d180142c048011b16800290500010102009141c5003e4001002441e000141407003d503a0b10240201b81c84802c0320301c1501917140c41c1c406074040f03030608048401c0703401c0380c0001c11200b451170701a10003d42c4041030455080c8200b0b000002c03040405c0c005010004e080b800135580700c110030070010303040807401407407030000403002003c2010010f00300700380e4148540c005614107400c041a01c0810741a00060034041e601095503410448a5030380f00004020440c800c2e0001d001c1030746e0300c94160100390b42590f00140f55800800c000009881100080c0000c0c20412 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 713409352 1250 713408102 713408153
    0x12030b030a080a030b1f020607050c0106050a0f03021c080d0c0e1801030b090d1e052205030d093b070903110f01120b01090302060d1a03030f07 63
    0x10340e82c80c8015030110089a0209480d0303800c0c5070091030516564100280c807040c8084034400307070f44002525840c0040010040c0300002c00d009072074803402d47c0320f000580801380400f06020707201d00030462040c805100880c8548042183e00b080355041c8201c514003264484107450801b003120208070050807841e60f40000f004015100c03003100d03581e41d540c004d51802980f5400819941941070404c1c00302c1780200b000300030398007541c0c2404a845d0302901d00210044000044003520f5030481d4112941d10848041064540242c1c0c80110343c00e02e4581c4520803035808600300e500704c14600038290f03041d168a00c20684041101549040b07413901c210341402400d904443c2407002e500121b1a409903450080e03880e100000e1490100f401002145030039903122042c2282ca01524200d000002030418603950301c0b4070916134032140041200e0340103203048405141e00400c140c3d00c6180c1035051034014024012184141a280381031161642004800c40d03008d5180901c000e460f00c0c5a03911451500c1105c1103418000d027420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 713410602 1250 713409352 713409373
    0x1030b040207080723120307050c1606020f070503060f130503070503091306032102010b040603060f051005010507330504030e010801050102030d0b03010b04020c151312030b03 77
    0x120710003002c1142c4184002d07511942d81d8105101100e00048682c5400d580c04448161014000501c140d0001942c2e403040759650b950b00c1c000c681c0c900850400780154818000d85075103c003c0d005600050f00c085508071500303200102000c1c0d43c3c60300d0794840c89405800030008600030522100450394404110f900401e01401c1796912035145030302c81c80b000d0b1903640011940c25480e1a040d841104680d2000c802845510b0075911a25801100c3d4441c0003079462981d6140060f19000707400c0300c0c0d0640f100034410000d003640e07402e1020150129250b010041441e10001882800d038060192081e241c042e5904c1c0d060810554402078060920228048048248480740140700d1030000006980c0003103001c0401c10f820903107400fa200c0c21145010314103103ca0f600041c0704c1640d0010640703621507070901d404251504160003090040c00340295003608a0f00000d410769591000013070901c3c2c080170103500225a1ba4500b4040c01c005100810000c100c1c0c1c640104d12021548641c00404406000805407400b00c101d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 713411852 1250 713410602 713410609
    0x20d09050f061e01260c040c09050102120c0c010507050a060c0e0306060f280b13080d0206100303050a170103140c040b0901060309151e0513051b01030b 67
    0x214081041416400302d4200609a0860f400b0a07440d4003146a8a07082941040d00e82031940380708403810300d1105403024142000c5507040100e540a02c401920030406100d91300d03402002d40350180281409449517a055040140d180c80c00c80d007200c01d40501814030004103000450b010f1b480080f042e510382c41814203900106030f442c410310594405d207440e640031402200d401d05082100050a95119210106c443c603d6a01c1c1d010080b181d0000100d4000d58040d0900b200b180b2988080d04000c4085070040f4000614422100c100c00030388079014115150031150040403030b905e070707400c44110350110340030303041000040d000b0b40c0600401001400c1c0350340780ea0410280c40c842d102090f441038506900b16504640044000d000290302e001c010351b02400070304080c1c0040703200700c201031041c18200740d9104003040c24401906e4140480f06040e8005000310f4400c032000d050700001254113400c0d494500008185042640784204032459480000361252001d460309445c02240600159414941c48079052039003070341c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 713413102 1250 713411852 713411863
    0x301060e1e090726070306050f03060c090607080c010207050f0712060c0e090403090312170c07021210150b03060d032d0305090c240706141303081006050409020d0905 73
    0xb002042d031100280340191740203040c0c03805540a00e024281148e01070358141c402050103540f0a01c10003215545812000115245101e030303982c0070b0015480850224001a4103400030901280124125091450240c00841c2c0b2698a84200000c6c1000e1050b45030000f1035a030005103c41d1128284944040c0d056004904411001c803401c41c00210206424001c0000b0345030350b90110380307881c40c00039002c5105481c0c4143d00360001c0c0c14081c00a1f00400d0500440d41c4882901020700307040703402c1e1180560980400750140c03551800708410381500310700c046490341040c0252403250200400106205040b61415900c2000141d20250405032188011a04c10280b00a1010803c0c482d500062240f500d1a00c007810000203208051168081695014480d0032040303444c08181e550441c2c555540b030162030407000034440301d90305054030b840e0102000030800e44000d401c804240a610340340400d0f03031011040c00a10080340034000104005120500040b03000b070b0701600031100b8402d40012078808039250b451515 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 713414352 1250 713413102 713413157
    0x100302040614091b04140307030203070b12091b0415170a060b0a06051b160e0402031504031b02060d0504061b0905060a0c080706110301060e1e0907 65
    0x40c00065005410700f401c0101075400510814030180301e600500502d01d051003944905281a02d4085c81e00c6055641070020200950f4003c08442c1e0700b680c0c48940c5080c54002c0d501d01c2030000361090000c0c08441d40420301040b60200300400404041d4028100801841134070450b4030801202803001c02c1a81c2c6041402190344804001402c0c034240b145000e02c02d980c1c1001e99a80681d2211804001240c3c0100941e1000c0076150fa030858020345044149280c0080343d51844102400c0150010b20f0040d01000d0a02981c004e0703003070b202940c3c041c0f0701024042e00305440c02400a42da0581c810300c0030b085810700951051004068614050000c103821040d200c00f580c0c1038032680e41d42c40b00905d01d2800744503c0300c08088203007025260289408006521070142c2141d603030a003d814501942001b800c1d004036003206900860802c11b081c400700400e0102d4009008a80210742c0c0e4100071495460001c1e030219010b1001200340029101040c18000c0c0c14502400302003c1c040201100008004481c0000002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 713415602 1250 713414352 713414369
    0xa1209050a2a120803060603041e030f0305091b040506011211040915030b0406020936060f0306010b090105130303020d090906030b130201020309100c06050c03060d03081003020406 79
    0x20b440d480100714120103940e500c8501d0340c003da03400d084001141da10599603c400f08076402c503220340d0355042c89445c0c1102c01440c1328032170080e2088001010740104a190407805156030400c811394600c0c490f2a80e8400819091000e0100b08966040030320303050700b18981c404018540084440c00421111003503407041682d0400d0320001150510021040348220902d0260f40d0000119092854403481190b0f50050405000541c00180001300c94a036585100700301206d01d880540c202c00f1050603104120750320105003d400c200385010071414a41542c00034400b0700001c01030301859181c01081c3e0f1440e80140300a80c140203040c01071904c40d00d0b04c1021b403401075009801a160308172000800400101e210b421800041c1d2400ba03060000c122207881c03007980b0060031040c001d0b0308100d500040c0d00d1405602144e40d4415040c1c03e00704c103904d5005c043c4040c083e11540742440280c0355004082c0c02400308036440341e0008964000304010901c10b400d8980c11038482e0003007480e02501c81c0c0100d010b452664210511 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 713416852 1250 713415602 713415653
    0x318010e0307060c12170a0e0a1505040302060a02040b1803010b04090503071a1003060b0d081912091a04030c050106030803040b13030f0e01090b12100b0a1209050a 72
    0x14444128012000385526182c0020b141c15181d06c04070801034044c2600d18101c0d42ea0140d400d00c0c1208004680c40309410001c45030050a038203020001502d0304480c12801409000d01181c1c0341e02c40d038006d4800340d1301e48004081c2469443c5660b410386014002401d64159207400a0068a480c1d9104019146002e44050750b9204a070381042c1c0003441c0040f903a0a0007a8202c4108188003080745a002c080d0381d0302581c00710300380400f900061032a003d40200070f4107190300080d2003240241d00c07400e41210b02c3c3e25500d40000c100d1101c841801204c120b0100508940d064032070401c29604081c401551241c40782c00c2c1010000c00039101c1c0d90845000c2c0c0c00c100c0354202d00200740014040503d11043c0c2c002810008a4154861aa40103004080c098102030034080d0140c10001b450303024402502c05000b0000f1041e03207070103503044040c48100081d502d25a5a0404020109414a1013022900218050303100e42084240640e051001415081c03c00d940c41c2c0901c0202030001213442c0a40a58143c1001a485 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 713418102 1250 713416852 713416877
    0x60301031406151509030114091c02030906040e18010608010b0f121005060d051603170304030801211a07110a24021e0301060305070801080318010e030706 68
    0x1031408002510700104440000d143c1d030303210398544120160102c50040b46646569007040442d0140203000604051040365100304514404001681c15003115140d5010741c1280c40c1080c16a2244075840001e034020384c04000a000c0e40c0c100003032840c0c010040e0000129084422100c0710b003103c05035003114240d40d445060002d444c0c5407000080c0643c4004503100641094403411413a5110480c200341c40c9241c1d26100014850380d903540c0c105011f1500314041ea4508103088200f0506032020f80000c60f00e003502c100310b078070b4580c002c001038030321a03541030b2100307034182e400c041c66800803a075034448040c48881d49905100000c0e00301d05804a481454003468400307420282c0c00036140382d4401c01d0211080e8070014001020036103680d1107100c1c0000c002c034800a95003203448481d010340f103019926045210703401130075403801d01c8440046040307559517641007010b0384440f40101d402d01300030f01c12045140c0c02800601c0c0d10313554012208880c08014141480740d07903e404082402c0500c04d42c841408185102c003100e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 713419352 1250 713418102 713418143
    0xb04050601360b040603080306091302090403080907050604090b0a0501050a02030f13090903051e042d0f0f090e0f03071b090204090524030718020906030103 69
    0x35000d8200e500e03040c000c819128402522245121615596001400d50a066460907a502080b00d0341c2c030203401032183d19180c1c1820341c0340d07030b20545003280201400f81c0014210b8820001c540000c0307500810301031164580303171811a254600074000000c1c9000300f01001601d5900d00c4014402804003880c0403601014500401c0b0500d6460382c442410701004120241300c4039030110464010b80301003205c0c00c3e251101c05003501c00d006180c0d08509049442e10190805042e0402c001c1c1903070040214950b141209400c1c40c0d803100e402a4403d04c804003a039900002114841484004021800328180c9a00c241e5129008004420194840001c044207484240311300410b5014603048808083c0c000c24901c41030300c0744582e9910900c400682000400c2c0d40f102d07000306000e9660002090894420b40d111a11010300500400c0c003035900403d0980307a003011101d900154070b00300500e440003c0c06440440d2400f0586507410781d050004410050b420017100030303139644202c0610b0280d80240c0c0500303070800094100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 713420602 1250 713419352 713419363
    0x120f060c0207030b07050d0b122a0a06030c02030d050a0c022505060304050703050a05031305090618060102070e040f0201091703030606160b360312040317040b0405 72
    0x1240215045002c0900c003040c04070007495003203c010b2070072035990219680d121004050051030103501c09072581d851101000001515030b1030076041103046d01050b68501102856002c1c203041260016900b100c10042c043c0654411003100c0c1050041e207180094086440d400c55000304d0b440341071280d07242d0042180541c1041f03c1d4990006042d40b0519680d51100d0b0654070410314440c05203e0500000050304001040c80500011684041240e524031000e141954584d0462406010300c03524580340055582b600d545198055030018041c0d0030300a00311020307094948070040010b8194400c4010008031103504642042c407850040c244240c101026200041561005034001e00300c4060321000c1c6018172402000703c0c1e8201c8800c85901c1ea0341d03241041c04903200c010726100603002c0760700c0c0c0b82003021002c01d0848000b0455580b100c40d2034a000030107030186211f0070014510030741d58003c0c0804400e1060000216401c00d0007030520341c001541441d10032400c95401c403811035031019018144420400704109 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 713421852 1250 713420602 713420621
    0x1404020421031b0b1807030203070617070906120b040608070b09041b02060114010201140901200c03161a2e1505031e0c090a150503040206070507120f06 67
    0x1d8800c2402c0c4551182d0b1369140e806481000004610800c0e030104503020418100119806415140e51640e0f44201a01070148411880340e5200c14500161403644206c040d0320039a45913445018901d0b0a00c00034074000c0c140c1644071070300596600004220000c042280384000c100301000c483d5988400e4040c0001c0c0d0b8440240000c5060809070300031121074012444505480d096503612140403002d000407409801e61412040069160a00b400f02035003042d04101c0c04030030502c4001062081c1c008620342544030300306490300150000d21426880040803840d075001030f4060b94039044c0070a588140c0d0f44100c02d0a0710a20300f0001000c100c60702c0c2c10398424131404070403402c0300405101480c1c050780c110641181c41c001001c0110000000355070300003540220281c40102d804050461a001c03500791400c2e4440f0854501c10101624002044800d1500c000c0d0030b01100d945682c1180c80701e83c24880141c009a80803a1240a1010007280307024210381072900403070258020342c1070302001382480d40071034040710b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 713423102 1250 713421852 713421887
    0x150201060909170f0d09030801031a010f140d0c0e010303080c0405011b021f0203090111011a0d030504120308010e1303270b040b030906070f09140402042103 69
    0x14100c0000c81c08182c0b2044040740c3e0183c00c10f03601d2000541189045c402c07810300c4540a85045010800d0641c13203010399050342e102d45400640b09100c120b6803403904100f4420080d002d00c0700c00040c490702c80304441480e8a00005490309003c2c0306660358030141842d60340c10181010032000010814154403540880d0494023015410b0310700b0b0304000008040218154040320100211034001c000c6446484203d8141d1264a1107600c4500e10014001e48a911034040707180081d949500140d803515040c4102d034203d20100078920138212002c0240005031001080550074450103200014290740c80c9002e000c00b06100769240c42156042154081441002030141807002c144028003070000b0340c20840000e110340c810585003040c4900d5443c0c0b840b03000001c5e004000341400219002551054100266006070f42040c1541c40d182e94030641220300d5102100302c00001801d00350100039040051803606c00c001c40c06000503181030303113a0030a40040b07260180404000f940340d850002c20300d503000546a42d84400c09 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 713424352 1250 713423102 713423111
    0x140d0504050c030606151206060c100f0b04270203071a03040c0b0c0312060a12050a14010b0307121703190506010807050f0c01180c09230a051306061502010609 70
    0x21030701c02e410360047e64203a006241105002c01c20300d645603402e866050603810b0484822251242d1038070040c0502141e84a00ca034108500143c8a2503d40580705880c03560500010400082814001200e400500c4c1660180110540403a02d00304011507000d100f2615944c50b40d4905152502c401900b840b6405002c15190900280185800100446000c2026001031b19459106c000020b01c2060f129480441d40f901410030b8142002070110b071840b9014001c031680c0d080046440241426501e01044090b810f4010f03040c10f0200c00680507040c00228050407920a44035155150031a20358001d407042914012140000c955040c0c0902541360701c12002c0c40d1180d942c0c02c0000024005005000c01072204220100d01d607400a03409600c070200c0340c1842025245003140720308140756a0f417220f0144d040741c542088507214480c552221900704078220005804400d07074860500c0d0f40200406490011a0320810b000140802c106000d10005070400e202040785450176040c019084588507032009500c203060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 713425602 1250 713424352 713424379
    0x60f03010e0403081b040501050d0f0203010609210b0402010c060b31060810020a020c060a090e07020109050c061605060f1e010302030a1b0321030606031407140d0504050c030606 78
    0x1005c044d00c0032100203080c02c0d41c445848a00c1c00000d0025007000f008900e20201c000240340313600c204201e0031148a08200000d1481c0c49a440350881080e401c05400d90a0601c04503005510408030080c54900622000440750f14101c000740c40200d404854868003041840c170a151034010200050003290840380c100f1407545080d0006072962503e540b414212940480c40400f600c1c002d1121142480d4010249540c410014002030800025070103460a60300d00340c8000381005005100f0784010301e4012006002e5802c00030204115030b4000c403049182c080182541d5070000e07200300b000c00d01505420582103403c0c80c0c485a0102d0884010100b406079280c418010000750306c0105401c10100d41102c48074101c0c00e1824002c29405250f680000c14501821403000100440c0400c00380600704955414403250b9524002141034810344117515003400d80d081d010640c2d460150400000d00c443e00d50f02d00c0c0c1807046040b031910485904403000e03a02138105c981e0704080c40c5014030689501441c22110702054540 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 713426852 1250 713425602 713425651
    0x201090507060e060432090408040302060915120603240109050a0e070308040f093e13081606020304060302090609040c030905210f09060f03010e040308 67
    0x100c03441807505015a08441c04550b0700c8031130480d400342030392000800703039504a200800d4420301c180c420f00c003080140c1080542c00385426182107000d00d0700b202d081400c041c255001c1140560100c007603d03a107c220b400c43d0721000d400100240103400d594420380d60181c40d04805060521500100c080d0800000d0703028111491b80200ba80c40c190345038000000f03140e80d10000c0e044001c02d074901d609041445406c10000070003240307100800513240e800c00468181c9684002100585c3c101416800021000c0c42e29041040803442c6403540ea010040201010820345031402c124a03072000c040c6110991b500001408151010414281540c4c200140080f440b894100000e440780030704e000d48403c141d00010350107620342d00c0100b52024000000d000300105522202c01400030642c0c040203d4407801108101451341000c40b440b03e4200a290725024070303108450800c007013607a111700c25082e03005005008a0f1405031445006c2c5019000040061030741d8100b50070080d2540c1b0000b0503411150154032004e42e85180d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 713428102 1250 713426852 713426863
    0x3110304050a060c0507080106030f050706090608060103020c0a0213091b1202010c05070e3303030d0c03020d140402030609120904110c10020a0905010e1507030c05060a06051002010905 81
    0x16504c0c540310803100610b180960414240750300200d09582003110210500260105508c1c078244103000710341c2e01542e103580c2510301c07030003500c15030b00810b6483d40003840b694040c0d0000d0541e0401c60303040c1c8400074201d40c00105062541c405160505594a03d00d50410040d01d021100d40703c64040200034080c5030508030302c4401e01c80e2000070b040203081521f0004001080100308040c04110080214178a001c00c1d481c80550707240d040124060a00c0c1e1403605000c0c1880081d00c169003c050041d514021080d00314802400001190300b08041d4200802d030201c1140b88a994241608080e80c1802410140101881c1c10b9018003100082c3e040454080201c0c1c6860007141c44003013042d58040760b40100303034140e4055401443d440c410180200c070341c800c0c4031005980c001c103e0682c85413035a0a2541c0caa50044401d890718158968005141c0d00e148581d004a44020b081c4c114400e03d41101d2054880c3d0300c807420002d0640e085c0c4d0b08240c83e031106000c103140c0403041580c9858248020031941c1840e480310b030740d1503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 713429352 1250 713428102 713428109
    0x22a0f120a080412111e01050c120c03071a0f01030b0c07051506041b170c040b0c01020a02060a270512040806100f0f09020901051308060403110304050a 67
    0x1224000c000c0c406080061140d40140340e00056419200d554880208503208604403088482c600c00200c912254030380308100550044240c26200d207074510039001580c2e5a07005264681c414440e58000c400314034107090003031642900c028007079038548004d864800122054018851000b07080c4504202c5108070002400b070459400088c1c00303405403592022000707a44200360014107140503500111041c1c4038511081c03402040180c4042080b0140c11841c0941c4d222844840341c0000d807030f000003210720001440c10030340091802ca2951b20f015505c0c03040c294103a22007081c500040c4d40100b0004129074060001c2640248815003e01c030035030000c0e031140000600c00d0011003030030703882c01881d00034000e04100303040108041e0161035940e2601d0340015640e0b4a421546407048024418022a40d43e0031042204102c03403c0e4103940607014103008020002c0d4000c00b0030241082000e108c2c89428a90507024038004103040c0001d800f060038603040040c006e035505194080700c0e600410040065464150424048 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 713430602 1250 713429352 713429359
    0x1112010e07210219030902090a0e0c0108040627060f0c0c020d06110313020a120c05011b020a0608072615010306080a14280f021f022a0f 60
    0x145000e0072095000f4007134080c07031100104400381c484402c1d581590040304114000c4607101c00d180c0e107140801c4140e076010209081c4a0300190742e2045503502822110740c0103407040c0030106140d070705a21403a09101148880703880e0b402a0064280074401207100c0c078071403035001007828411a84205c401034640c201e44000203001e0800900203805204440d0b001d80c0610603800c4095a490034071158140003c070303510740281d208e190310080000d50f0400600e48002060b0740320030104a41e82c640f8005640740f0b01b40400d41c0c040d030109095404016910b11048801a02c40e0351a44022400c00e020010000307850f03803020503198070300f4200d4201100b45021842ea849442c0c1e80c01d2002c50918800120081c044c030346e20600a0b44207205051003080702208000d180d0344240401c40702c01c000010025409103561800c100c100202c103003400c10203d121504008141400038000800701603400301c8619080c4054840e54005810024034480400d01d2011004080c4541c00031413138456030800001082a07011f225518803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 713431852 1250 713430602 713430647
    0x203041a090415090606170c0a120e031e071a060d2114041202060d090515090f0f071e0b0a170c0319090201050d1112010e07 55
    0xc664040800315004180302500600c01c0416401903200b0010103402440c002c942011004607455228007a1000a20301420030b400080e107654072040c215600540182041002c1d00c030300301041100324081e040c030400ea10b4009555411310611051480c03c54918000c8000100704100004241c280e48600070500c05071520300d0440e1070751000030300c1c44400503100515010301c00c01c141020a10b2221440b0801c40c95803581c3c10136029000781c080052203240141d442c0315408503111409410408094481e60703014680002307039070a2503100e003444c046400e0660051a004c3d202044584c180c1800404131542d000030081c91480e101d0f02c0c07801d8031b85c881e9000701c1c0110007404c50300d42d83c0c483e039000b0650300070710710560750603514001c51000501a4201f5551890b500c124400400c900b800303a40b0413644282c0103994240d0000c540e00e00c030003015200f2090305030b04100040c00340c0f03a019142072141c11148000d400125940741c0e02044441100c10050748402460305a440c01c00c01c0b040d0b0451a684a06110840c1144 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 713433102 1250 713431852 713431889
    0xd1a19150914120f0706021c030b152a0102030601031a010f0810030c060203041715010b03070e04110408160602070302220c08061804020609010507060b100305040308100303020304 79
    0x44c503081100300b08010030310603c08005182034012900e00d46218254803280320400c10b01000b031b003d403452029082e4101d08c031140c2d00c9016501c4440640036036860403504648034480024a0314001c1d08101681d00665400000d0107219a09803141c209400320251154034501d034000000b03041d80841808940500280c10700142d0714561011010021b558080b000602d41520750000035900c1e040350040420803a145010350b61480c00014048080400003034420169030b080100c429201e8001424030bd0600034202c5240e2400d0341c0301c1c003405070224004444a0b03145c0d4680400b140c9003001181100003d000c000b030091100341c0e404503140d801c3e03a80550b40700030740b1500481691403510054900307060807440c01d511350b10030030750140034180035110841d01121f86038480050f15008980581e00217503c074104000302c9020394001c4c03001e0904540140d40000e40c1420010108003d800b0720356940b00026520306c100020550031000c116003041d070481d0295810742c10b540c0d0181d980e1181e40200a90b1041c030520b4074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 713434352 1250 713433102 713433139
    0x90803130204060504110406020609062404020903100c02012a0c14070e04020a05091603050a0608030309010b01090b160602031302030f0a02240d1a19150914 69
    0x74005040c0508101b140d036820760811007140c0c2050043c40d00500684001c510309400004040d4002d5000e0554520703060441d255041904420921403a0850703024000f43c80c0965090280448503940721070302250900000000a0071100c480050240f0030300549a241342e80d01500685454101c41800c0c02c1c1c4c8020601e00700301241400f658204400e40c800d440c000306039020800582e80c080ca10a42e10300035000d40b0381040110084044a0ba00e41e00d142100161400307510030303003000780c000780720800c006105034450b001c80d411613000f01c800e4001c80e0744500c0a2001c6507840307002c2a0041410314105030a10001d11041390340c2150019001e4072094012001c54a911418900700500550083c101e80d070034020003480d01e440300c1c1060303026440f440c4000c8a030a000340c0b03800c43da4540c000c00c9044281c03404441c8020f40000340102a040c80300c00400c0c001c141c4070368a50940502e10b40364815200c00c40716161450041d10140180420305c10031460610400c00740c0700c4c0d105134a200c5d200494055000004c0c10040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 713435602 1250 713434352 713434361
    0xd0f0c051e13180902010e010c0b130c230f010f0824061207020606040c020c090a0e030f04090c0512040305090f06030a0f06080d021f0f05240301090803130204 70
    0x603c10041001d150540d002c1003540c001c18105100381c95420079645120300543d21000c10040150032542102c0026103054802400281514410b032842d42c810754582411030701c444000f01c0360448000303d80c41402e8071454400900003940000340f034841d11425005034000c000c100041c01050a0440c0724007040307421101c950342111042c0002e420141c0351988441440480c2c1c0080d103401300540605804150030b801d150003804100d80c2c032a0002c0200b5500c2c40d040c00306002d40181224041681d40120100000040c001855a0505160030380d0f03c66092421603803c0300c204140b401d00f403280c00c12240400711005500543c0c069018100507031039509040200f40c48072030502040d40e10660002c100f10342c40c2416072041c21000200403081000c513451f0110f0b10390b01d040c0e00ba0120301590120250020750f81e00c014036a0720110401d000810310880075071146081e54401d8030b1040c07034680d1a0304200008660b1300500000716034124000d10044055440e812080d100280c00da000c0805982401c000f591074a420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 713436852 1250 713435602 713435609
    0x605030303100e0c0c030a0c0b061f0c031e0804050d0c0c050904080d050928050304050f030313060903330b040e0601030b040c0501110c04050604060b0d0f0c051e13 72
    0xc1c0c1e0354811f902c4000030001c1105060448254442e4004940e240c140071034032001e003460381543e40c4008440b41c0700c00d45110388151030840c10403910026444406800303400c40c2d070f5040c84545032100a81040c0c036250741000449a03401082014915010010504070a02c980031200c1c01c0c0c40100b11500e880c00d10030145c3c4a90304d2456980340c180f801307000051a001a07103c0000c2c55809091200040b621444a07007080c00c0c8402502c0c56200b40300a000a10340380304001e561903c002c080ba8a4150040d0748070041000ca41d00000124250b400e0070024005448507211f20300c110100340d070360b160301c40f140d14503d40c003801c42d82003031003076601c0503050b005454a600c03062940c1e40003411103c00b0740e564a0400e21090003120100c514401000c0d000445500603401140c100001c1d401800f08200b0741d03818030004282c010802c56000d0386411000400c410f08100900600702e002c5d5001c20302525042c10442074407000480c50080110811040e0340d48d0051740c40c11084502d0030a010380c3e40707003068a415184030340142c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 713438102 1250 713436852 713436877
    0xf1801091223010e1506190617060f09070809011e050103050c030109020102030a080910020d0e072102010c0510020c030a03050906190216150f0605030303100e0c 71
    0x681d120103020254800180002c2c002c1d40021403038042d160414240c0300301020075040340e80111248440d480c040842c3c5c5074001d030054407840782e84032024400310076009507a0200e804140400e017004040940d00c1c081690010041d15268106041000802c0c110a801444141041014030105250030003e41103051101d203280c054804014881032220002c000a100494052280040d14815030906000c0c40c0a000e805030003a40c2007401d00c000075642c40c00001c000c1e8100b401901590703492003031036201034080c4444c0741c0000110584050780c07040c5802200e806c0144004050b2940c1c15605011207000c039522036081c60104605405850094a0716080702c0861840740c1c00070444102c0802c000000c0c0851008964041c0325645814a0701c544800e02901c240040144040410060b0710b00f64008200b0074500741503042248000d030710b9804120b006103152580306a1251f0203030407a5007250041c003000c0c00d403c07805585107007846035034455801c8052040603004042280002c0503806003405498680c1001c1e03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 713439352 1250 713438102 713438129
    0x120605090f0f070612090302030306090a0e01060b090112060e010909110306040f0c1403070923041b0b120406090201110f061e060f0415180518030f180109 68
    0x1440b59a0b220300440c0a014001100319104102090700c0d40a00c4c1a00303a00764019514648600c4107001050500412130880f880c0c698510001b10701c000d1007034200405103002003540381d8105400040410310045a850a610305082d02884640ea01c543c41c1d504403084000c00203401c05541c54200c181200d00083c0380e41c503000325030820081c84080003910058500c10420480750300d480e91450321023401c00705403140e0541d01442c010300c15034020303178080e448600d140911003800d2608004040c00048044608441c0c500b00d500314868443c6016031a00c01829242980f24140a2200c0d010100b1080090000e052181c8521152056901a90f8006c503586294401d5030703104500b08126950b00d4100b510b2048002500400054a40740131000c02e50150764014102c40c40300c20810f08110150442070800341e0300142148001441030718100d00c03291071020381d0031301180c103240c0000c428100340000c0b138808809030400c02c078008941c80d0030000c941d48801d4004044c0200345002c00101c3d4440041d40044003820b508 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 713440602 1250 713439352 713439373
    0x1060822021f0e1512090319080a063302070b22330f0e010c0809040f150803130e07031103041103070f0501050d0506030a050109080309010b0901120605090f 69
    0x7800042204458041804035161034015a681d0380740310300d400c1c031040000c0c0900003040c510309c904060341d000052594003141c0c2d19159040451980c040d0702e141e286860700d80c02170011000d901000608541000e001814107180383c608010064401c0c0d07001614000481c01030480200e000d683c05501a01d42d0041d404410794400c07040342903030705c040c91261000103005a0f10703080491007281d1407200040b0958030a0703101c071400c400640315240c8410040707402c00014410001280c0f52031117117007017480d1658404a01b40500e4070742c05030300c840ca1b07410142040d081007010640410302c880344c48003200d8400d0003040781395554240840c0240718400116041c288000240018031107460588801804200d05030380b10705940f40d18800407104640301c1c04c2d001c0b903024822900c80c1c0c68540c0c0940e0780503001500740d0315400415601c041c211140b4070421680c1410200c14084880c50910403c00c00701815103e4499650402c0c3c84070b203400b80000c0000744165124000034044030341c1880154040c3c8c1004045800b112003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 713441852 1250 713440602 713440639
    0x160b1201050402070c05120f06131704270605030604140d0305220f05152502031b192001050304080d09140601060822021f0e 55
    0x1100600951015640001198502c1c1030b10894820503032000702c11203c01d113014207102034041252207036800340c0108070307180000002c1406a24418424128100390103109481c1121411141d00025284000c00780014040b03014000d000c50741c00003030100d05440d00e071282c20340341001d4043c41d04640c4c1c2500450301440708020800d0521040400340406440c0f103c0305010044044075403c0b500d2030f101d100796600c0741040e14011000a500c50780140c116500c1082d1603120185046440307001c0028403040b00081100f0460f44c4226400e1428a0446a44440c0c02c3c0b800001c5d568059002110114030080c90110100e8000300b0007030f9249103241e4150000040c40b800c0c1011440000c00e0401e401c41c0300354403c56940d40c1f003a0100d03441503500098071f9007001841c004090003400c0b03500b01180d1480c04004200700c00320b41003202e14002c7c00c03607a440000c9850010001042050071611a60041d0100701c082d01c01070f5a090780c6c5180803141883c01c03050800400d40100c038512848120641c00500302c0610400301d18 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 713443102 1250 713441852 713441857
    0xf0305090a020d240605132906120c0a02010608062509051c0201020f07061d0f03060f01090c0c030206160e060a1e0e13020c1e010507120c05090d05160b 67
    0x21012240346460700201c1c03040320140c4807071034524484a84230a810070603204910a040103080d030090400340c03e2000c20742050340c0d13078041540d10040c451000700d61300a4481e42409944007518880b0701401041c02c00501c981000b542400110160130a440070480300c40384581132000082800400001848501c20304241c1590a080016401401a103003005183c0000003880310460b0314980c0d846065030150010651940b403101c1048c0d5201000703110481050723400b008044e015800072100c501047d40b5142c88001260700041880c404d1010040c1505d002c2500403410940c007401e43c036003041c0401603502c41150b11140d096039580d0b001d040403481c4500641d004035401c1900c8a0f000400e2000e850f4a901034503030314074059642d60310103c01d20030b64100c2107150b006085040704140c00c07101281e5000100e11b00c804001c1d10300007800ea543e0303c2040300b0168002a032100000101030704000865001c90000d00602c120901035004201060300002005800c100d0f0140c100348405594000e941c45072007031401a03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 713444352 1250 713443102 713443109
    0x160f02040f09080c160f270203072703030f05130f06050406081b1b0309040603060905010c2c03070b070b10090605030307030f2601060f0305090a020d2406 68
    0x41c4551000c408019080445c4942600c0501c17840d04a101d2606001050b58903a03603000f0209001c281b10190f0702d408081c0044d601508a40d110b00208145800c140d01c0070b0001c45012062402c0071704c0003000030035008041800c00c0700c02450429610f400c0d1151304404030f5003e40c0b1506501c1020700c00000c400b42c2c000042c00646400f03558440c01911100d540700c0201e030401a041c10400b40801024490f03a190a000d19641c40c240000d80341088513400000341201c070280d0051b911103440300d02c000c0c10401c082c0308040d485016414a010075100740301005518030768002d600408920461a500003a980800c101ca0092010501145d80c614591616000f00641036400c0c00e40f0700410800030410f540c180c0146400da400c05002142040500c3e02d04540780101e0300d200100b400750207c5811140c200d40c03080300d403040d004611080019403620384000c06610021308010101840c00b002e20200c000c0205905507616012100381070300c0303d414103209507200030141c02e4038150842c8400c1c80044a041c0c0d00040101d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 713445602 1250 713444352 713444377
    0xa0e03070b0f0610110c010c050708061006080109150302041806230c0724180309031209080a060209011103030702060105090a09030807080405030d111206030102160f02040f0908 78
    0x8140041e0203039403000d4220310076030064002c4260708406c4e5101d90410070310a402482169512540c0701040ca0518101faa10351601818010060102c035801c0501c040c01014121070402c001c616030030f4401048042c030701000b072103540c44480d50b1040700c01c8010007285442e04068100510444c84a1102100f04840302a1415860703800001d6202230500017a20a402e42101004059410081c05021440100d8000041c030301d079180c0007000303041010780070100c0b241d00c2070300d0310031f03507036003982401e141645000c0d001408101c0841c005000c5082c01080364022950300590258a034440f02c030050b5509440d03540010442e02c0044100030641e0f600060042c100c0308282c0d4143d100380c46040300c540a9411201018011800d2000424051840f07540456070103070003032043d2414045507c08400c260f40c1c0c0301c421404049404a400550081e00c48101078200c10100c0085250222034036900020761403601000c0c0c079080c180c1521406540b80c50300204002c00342c0c030104000c25002c078541030703032243c0245d14001031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 713446852 1250 713445602 713445619
    0x810051005010806030303150d120503040b150a0612110c06070f0c02010f18180f0e0c0a0e041707060501080f070501022503051203040314120a0e03070b0f06 69
    0x1050350190b10144d000c0c0c04060050b601d540c0e105112140070708481421035070000c00d0b00d4031220108440300d084079092441076803090780e81e003024141800103000c003610034580703804882903c03096907441002290442e045c41c188103036601c0e41e00341084002c00042905140c00c681c00030384950305a5000c07071550f100f400f107921036400b4816083c10481c0c2d40078604d6002800f042454403c482140e002e01600d45d00304500270480d6025986585082614a800c01854800c964445403984c84c03101d058020b9418070b003d4400101070310b8142400180d50300b551031140902c0c08034120701241c180300107080c40001014440b1070440d950742091030403a0040c8403d11582001380600300240804120200b42902114016801048410340c1612119048a005401d604e0010707000e40000000030700500140080e440324141c101e45074641410050182e10400e29003002e1000204009001845007080c002d8011070070f44400102d2507103841d0610301d036100d1004003429096610040100030f2003e2003110744101c80944070480c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 713448102 1250 713446852 713446859
    0xf160806070206010506040509090c10020106062604140a0611090a230402090301090203010912020d090303091a0d1803030b0414010b09030c0a06080f0c19030e010608100510 76
    0x80e01ca200078005e40380d100d0000c100802080c80c2c00350302e454000c0080c20565000300c22000000c0e1031903822032045c00c0946d4503000b007003140c2c0d40c100d800006000084444580f000150000b0ba8240c2c1d10000c0c030040510240c1c40360603204200030400901c89a85c0708004100780d01c1c1040c0240100e801c00d4100c9449000d0198002c507a0403810401c203901c4c03480380b0302017841000320071003000040d401003c00e071500356685000080c0036960900030084990300a02a05550140500e030007401c200098207048184000c402003000001d900819450440315440718007000340108041a00e80d5204405040b90141d00b88007030005102006040301814a02c48d45003008100c07640c100f40820794540c0b40a0001034442800100190710408009200750300f0001c0586250480d00c0000a40a41450304000e00040465040190110b480c1b030101e034000c880e01046074205071001460b406111403d8400c94105600c0b440b074030100784400d42001010705451401d454000348802c02070401801704442003000b5140070103000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 713449352 1250 713448102 713448107
    0x4060503030901030c1b06060f09180f03170106031401060e0f010e0406050402030906040b0a0501231906120f0e03030c070503070503210a05090c040e0f16080607 71
    0x50089410240c0a1418418050019002840001c0d07032032003030043c441100d015060030485000442803184200040d01c0303042c000301da02010720540149121500d88400b610161a83c405007520107640034412400300d007468501103c24001007207803007007041c040000206905070917810102c0072100e010040074042c0c0e0b9946003200d0803140110035541218800200050f207501c1600c501c140023102901c00b00700303650b903080424200d9004031808281f0b070b0001c17020700c41007103e80c003038154011b41150800d0005504041c0700c0c0c004e80b40410948010f05155007022011525022841e200d0031564a00321284156508405000e000c030310b140e001c5c1c01510b84409580311880314030444400a0303480d0300a40c20760751080d1007140390303510006c42564288401e01030840024010402000800601e91600e081150041585284001c01034241c0e00514203142c200000e10f1000a41c411180c41e04860114117a142008180d04003800d002d40034940340110440c1c0400b415072050810704403040c180840c1d1140d611440c04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 713450602 1250 713449352 713449361
    0x190b0a0302090c0a0201023a05091002070f0210020105011503050903030c0a020a0b041109091b130b0409050d02580815030d17130b19050604 62
    0x2d40c081006400300342c070590300f40041c01c4100c109000041c98440031864000000e1400b41400b8080c048005007043c0c0b0210b000710208030310300141e10030f005a0505035081c9803102e00b005071001e82c860303010903010f0038044107045a0b00d1254010f00b0310341c0c41c02c01000c0000d001c0c0ca424040c92506000280046d071041e4468450782c0e00c0390025034003070350641d280d00301c0040255001001d2082144191840c1c6400300340420310b418004d62140d0711054a803a020b0041c00139100006010314016004007005018085183e002c10001c2c00d41240d1900d402444044030390700074410141410b0308a85490382d40f0081240009011550040760b4085074031030000310000741071080c1d012110340c00c01c40c0640e0700d07140d83c543c050b844291080711541801c0030038090125407042c45c80c4018141000180d0764818064503003040c461440031080d003900030709894059654058480c0c12202c807000490400100040c64035695100d480140030f5001c482410581429016030300c01c1c115612640300c2c1c070f07464103012034000d01d8140306 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 713451852 1250 713450602 713450609
    0x6050714090a140312030a05010f0605190315090c08060f09090706050d0f02031512030306061c06270b090106081f0801050709060210140c130e190b0a 66
    0x6880b00c0c90308200018042c0c800c2080740e42d070544603000c1c440d03910500a4010710b100f110601000a500e601d0080252400189a80000709002040061400d00c1c2c420640e031007a50038250130040740c418410001c00050304100c0c1d0000c580b1034038000b440070050741d210010a029144c11a8080c0c1030303054101c10020b16030b10a55108400e54000f5208121032401203000e403042032040360f4001142c610f244605c20981e482120304941d0400900115000c0b4a401c3c0b654843c54601c000083d07080d85041c0b804182503128000303444038017100b1003603502401103903608078202600c500307040c030f01024002c8040d5211280d00510280c807141e06106d140c0e40ca60808880c030794100c400303d5440c40c0140c1c81c0c81e12000c0203010503d01030010410101c07008104d00109003d034501a41607666455038507450564024103200501c400100b4540c14038202a181881d0300c0b1101c1e820005480c0744590b1f81a491307542d0b0300d41e00c0c00307a40014400c48040041092001031010f044c440d5001c0420b084c440e800225041151041c030500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 713453102 1250 713451852 713451859
    0x30911060309060f090322150c1211030906041d1501050d020708091210060f080d0f0516210c170306041107050f1606090326070605071409 61
    0x81c502c01c41540c00c082e0042050303420380c0d182403d854281c2160200e0b90381600c0d180000321f1810040341700c2009001c01841e100746800b02c9000c00641d40c010080e400f82070780101300540e021390640082014021615441c1d0001e00542d901e96561020300c00d155200e0400189014504000800c0e50240e03415250304460141c1d196850b201c80003c40304000e4006a0082c3d954520a0028044a8507400c200d030012000c0417004240e5640103400001c243c416036048150304050851041048580008020840010a0805949603070300c848003101c0c1030280c01113007055440d00200d20414098668010410301840041020a551500c5819a03812202c40401800e24000c811541c100312030b000040d540040c40240702040201d2a8984142d05801901041c5cad110380144144841c42c2d070b810499106004481d0704507075034030ba183c804013500c1d4100302d00c000752802507003c0001b04518000032010381c0344600800340640b070b0000307400c0c03040051038102ca4020110722409503408074071003280700b9114841c00c000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 713454352 1250 713453102 713453113
    0x1080705121c03020f040b03040605061302091f0201112b0b060901030b0a15110105011e061215140a0e270c041d0111040506071e02040606030911060309 67
    0x200110005d5100301c440c1c040c1081c00b0320000ca01c5000e40380c02140114014100410701e8100f24040084228441d4521814944100185c400381e455082002404071010400e411703486403040000d0b0301400c0522103002402e400007a000c140302c0507890300b01000350000e5203d902e0140f42a0106012110840354140e80100b0a01410200d50721a4008600061025000f003400954070807d03101140780102514010a17000e1800240d0b607402480380c18010f000850341e0021020305d40b100f1442c08040e0340141c60401008200072529001d0a0300050324020f028080001c000e0342c0c56004051003149004501d126901c04080003c88804443c0180d01601201c0c0111403c00502c883d440880c0603a1080e07188140100001500e540c0c1d100e01c91150424031511088159100c00700040382104c894200803188602c091105100c80d44800d01640d80c41c4c1c1c0c0c084040380f203034a14a0b81c0c00d5845082c9410095009091004c01305d0502e60603004010345038030440b039204003030601804100c040c0c0011100d032101988032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 713455602 1250 713454352 713454403
    0x3012402122703030307020a0605131e03022401030308090d140c01110414090c040e0c03070e0d060608010e060c16032c1f02070512030405090108070512 67
    0x1440600d0740c40040b1181958608070844020034110740045803c01d0141e0000031200051000600420350710007843d440103c41d020f0160f0700c40040900d03c04c00c04101d64544d921000c105402000000c04041c100b11072038600c506e103113861840101c400d001c100c1c000b6a000001c0384e001240011081c80c2080c4540701d020300042800300107019030300246070309107166480c0c40040c4400c0003100c0081010307125110010700c15104020901104000c0035040c1e15a0881c200001c0250741c2007c0146030300301420090295894403401c0c001c851103592608096805180c0780804810040030313038081c1f012214040c0090141451300b141003501c0f03031401c80da4900b101d0340403c01212588540b481d540d883c01c1c8030f4100407030039401c04d110214421001e10065203510404c480c80035124984440160704400c0260010b103054030907500000e413201c165228482c01076070049040b207030980c003d009940150401605130352032503a403044050f94588440c440c0c0380c01350010a42001c10701f00080351089511811010701980f0b91003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 713456852 1250 713455602 713455627
    0x18090311010524190b030601020f120a03110f0a0c0606080106060e090403090b03012d03081c023007050313140309041103040b1f090f0e030301240212 66
    0x907055030041d032100b21912080c0314141c1070300b400030140c424a0451606d82c034040001901c0c001038684907600c1d0b0740c06000c20612442c1d5140840310311003402d103004074041e0310300502002180110745a40505e1503020603424042da901203103265160b801a0400d00000365140340c080d007228814001e000009804a10001d042d08001c80c00c141c0152003850f00d40c0708650369103510005500280c20241c004046107000402c60006d504c0c40e540d0149000011843e101d00c0c59840c006980f1900303100251a104584081d40c3c6103800b50705890701a00c42002039114080340d0f00d41e4058200e002e400707401400300d82801250071035101e42e0950340304045d8805951140106a11007a0622007014040c0350148820401c07808151214024401d420061000250312030031b0510305200034400007040c4400c24034170701070415082c07045c0291000403142005000102c805000c0c803614080c0271101c80f4220188000400054160100c3d2071030b00440821440007910400c05950890300c0f01000100c90800c41c906125040c40840b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 713458102 1250 713456852 713456911
    0x507092705040c080109050706030c05040f050409061e020c12040b07032d090305210901030e030906160b0a02090a05010f111015140a030813180903110105 68
    0x501503d010302c003407956000842d007543d041c010111903641107804108005909801a42d81c002400d04009007041d091090540345042603100c5c65100c1c3d900c0e910440240525603119208140c0740800040b040d400740c1e00e114020394024080741c42e252180690914410040070140c1c2c0c182d41c00200418a4120380361012148040c9a2005a00d10101000b90416442031040560513245807610381030507062450802905011b12202c80c003c0c602c4600904250071105541111040c180900340098040c04440303c0510398007410407003a03000900000d410140321016600f80d80032610419040700d107980c074162024240e000301c251154018000c5841800990302540002055180741e103000b45980c2c3c1040501071800034202d41c03c0c51050f80d00d180d9050703108070500d5020302410012042c016071040d00c03008100e8481c10b501c0068044203001c21400616042c0340c2c10500100074203000885600c1054080400030520b1603000c46c0822009480c80e10803603010f0189500c100d800d25950700c2c07091101d60440316030301c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 713459352 1250 713458102 713458111
    0x140603040f111504030f0209011514220807050a061d090703090b04030306140d0f20060c030918060306070c0302010b0a080705030c040519020a0c060f0507092705 71
    0x80100e003d800700301c0c1214006000150b006102c0748441005a005000c9400010f0b001400d4162440141c410455044621045140d403140207041c0e5030003480310514440c00010300740c2d0300c0040c07501c240000c601c240041c41c0c1c4151801112041c1d170b5a543c5807001c1c0d0f921402c40c1880c0d0401614818811582c1c80c2ca404040d81c400f0040c00c0115440b501581ea02020642c00c4900b140803c0d075598081c0101c10405c1d84040d220b0000341c0c1c0c44c0c80700c1c440c40c2c0c841c40b545401c4004010701c2404201c201c1c4034240c144004140c10248080c00450310f070242010890380703c1d08500c0d4000c2c0911104445510305008148201e4000c21000d0090506a02d0b40310701200c0150301640c0640940d07480d118041416180d00e0940740c02400c2c0d0740080d183c1a400c0204160800b010054070070b10590410052090480d410124500c04203c1c0304c1d80107940d03001c4054141c50829000d00c01401d400c5c0342001711143c030862904214801c4450303543d0600145d8a0760035180c5c405000c0000c0b40c8542041c11a9000b1003241540980e800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 713460602 1250 713459352 713459359
    0xe1504080702152703010606050906090a03080a05071709060f0a02161205010b030a02100f0e0409120305060a0602060601050d09050f030a120e0a0b0a2004140603040f11 74
    0x407000c480c424100c540c0684030200304c0a44800405030758204098291101c03850481c000e1010b6460140c0040c264060120128815070b00002c032814642d8940b4030003001103500101d2940c8074482c428000d4540e400090040c3c42e400881880d81402c16082000c581e04860300900e09810032aa0414203c0150000d04111041d0311600880700d00800303080c56803000824001903400301c070300c900c1e14103282500d511130303001400381c0d200c400c8550040c0d44903800004e1014152800e40003001002c1421150352201c440309035006450404508103010340c0014400c802010354074203220301e40310002400318602e424410940160000300110741190310500040900b0403003400b022070441240d03200c3c5070801028840400143c0e1001840c0c0703245903002950070a04001d8003008128448030390114030303100e10306100001c1c000c5461f900003400c0034030305910030315030342c0e000c0040c441c00e2820200b0104100d90082c0a1043d40003c800008130311480d105003149e10a503840391402d419112180c3d1080c00d0071407404140c0341d2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 713461852 1250 713460602 713460619
    0x10030911030703050f0c0d0b0c09010203041a07030e0d05122d040f060c0f0b0c12090c01090f1404050c0403021305061e030d0c06020c0d09090e1504080702 68
    0xc0d96800b0030049018502031005001600f03001500e8525011524018500071107001c44a04040740c00e4560050340108100d610176680c1400100407070540c032581d004010324020188950b0b0700c150b0560083c0031514866190881041e541c0010070102e8500c605c40200582d1000280f000a410000c0103096104264002811181b0309150203604079001000d8000070307100c0c00f0801b0041c440001c441040141002d003403039010401d00342c031407280b0540303020005081104c03800040b9068811036000c03102001d01e464010380302c3e03007468580d0075200c00d01a0702407400140041000b00307240d07c070640b0b0101100d01e82d00c80a10304049900920001e0a001060300c002e1400610000000d41c999161455102183c954002442d00d45a02040306010f40c4540700480c87c07864030a1326011303450011f03250010000341d05145880350502c0c0740800207445804004a0240075021407054000d030400c2c00c030402d443c80341d0310910030100d12801081c1d0310b182d094040007003840d19001060208110304024030300180060236010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 713463102 1250 713461852 713461883
    0x103020609040b1f05030a05010506030103020d0b040305370503070c030e1206040c08010608030901300f0b0102060f09070302130f0c05030109180b0a2f0324100309 72
    0x44c0d40500b0810b543c0100f84000104960b0303401c0c3c0c0c490140581000c0341d046095504680110300034041c1100300401c0030b8280004101407500072010384d007020803820003404141000c3c820103510048009040c030400e800c81e803040d0707948600900c240c074804d4440c1d0343c95450781c502588044441d402a4064170742c0015440002041003501801914444c41c041c0b000845482e240260b01405c40b0300036809114960018407a1b00034503030344082080841c0139400c90003503924000300591510000306058034082c0d01d141180d060000003e98006620121098007a1051aa01c2d641501c201c950110703030006c00c40d00007000a200628004150702c419072880c460000b518042d000f260303022201029420400714402000401518a0b1402a0210030480202454001115544007540504081c0205602c162544007640407072920005540691300250704100d40005981d202c0502d1380c0c0309413404050b8540e0550041034241c002480030b544006e0140c1550820380c142041103008108858084070042400402ca0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 713464352 1250 713463102 713463139
    0xc050d0f1d0a1703030105090c03090a0803060f0d151103040b0c070f050a0303091e030807120902061201060e030706020319200d0f110318010903050d080a140103020609040b 76
    0xe20f00d14007031000319540e5050000304400030780002e003403041c070100410811100a40101c1e843d5401903010b450141c0340c1c2c82d103d0000d0721100da03104071150800020214003081c0101040c4804048a0030b0008001c4400a90048645448202c40281c0720201d01c41c00320307104000005c010319096001d6460b40c805a01c15030340301400e10045c0700040c2c0000303840342d10840c180300240b0016100381000c924150310740302070343d6070207000341500802d02004d2180c00381880011032800d41150006940c0100030640d03800c191120311280300c034280683c50000704540d010300c1c10780c2400039201c0d0564900341c00035410600c40c100180700040200482004001118540f0307803008014036903a024018164014142c0c40c200b0703200c01801c7c100110203000410941084000e088000171003100d4801ca5414002c50001e46410016a05e06440307a200800d140f05804030b204200d035001e126180280752003c41400f01c8403091503100003104c1d0a000180d4420340421905910340303000c1d4490340300e00d0390182c20902071042d103d004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 713465602 1250 713464352 713464379
    0x7030b0d0521041a03280c08010e06370303030204090b01020708032514060703050603030a09061b0b0c130b0426070e01121b0806130507050607030c050d0f1d0a 70
    0x10310706c4071500c40344e010750465005019180549058482c100007850548002111000580f902d5010360000c40680c109240c901000804102680042c040c5543d54070325006000703610a2083d140d04501d0306410010540c80445c0341d030100c80c600f00c02141840c14940c43c621000480b104902c12054245209a000500c6000f0b071154400c030000103000d0901e0441406815a04014610f07840ac0e041001410403140d00f20f12500142c0e0303142c1c984026091341100d211400920f1421010b000b40410008200810706001e000f8558030b141129001c0c0c0a5940b805081980d014500074100d0075020210700303041008114031005131500900d070403600115075845001b44d1000007a0401c400904440c000141481120040341004406a09042c6502d5203003034203490b00d54401030040d07803507140c05805090612804000d10400b800c0001c142d0342d913800c4140750180c03e241024004a683d406414803030052079004980202401c4070303685658905020410003845a19a4102d025a21034995400881c10f071140519 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 713466852 1250 713465602 713465671
    0x1701060f181d01090f05010b18060906030a1508030708160204240906080610090c09170a020a080606210a06020412020906062107030b0d0521041a03 65
    0x80700d052541048442d4096036030010f5801205e40c2404010090302c900702d003c8914203a020694110240c3c030ba040011458415606110340c05200032090011000d00340d40701d10501c01c3c040041940943e40d4010040d01d034003c0200280064809024030308609810408240c85240700401c0016140c040c0c900805511902102d00c0d8203400703000c1000d010b040c0d458403d40b00a0131000005001c0ea00d0b0410040807424064003507101007544914154010310300803801170f40039200314400f60a1050003804200d41d59001034500f64450344000e000081c8192000c22860300420f40940b060b00380702020042d022207000a01c2c4208028401d00c05400c0100742e0a101810282014140300440680035004009500f10003500e01071144400f007050083d95200b47c2e031200e03510b4401a10b98100365075440000e038028600f01c0c508541004104c048902000408140c101c1180d260108513941d01c00a119401c3c2280518000e0640002c032007900c088020340b04c04083d540c8910401d803107414002c0d00c0036444415a04005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 713468102 1250 713466852 713466899
    0x6080d0c0807171902150711060a0b0103180303020c01050705070b070f2a050d030608100504021804240b181f0b04080105010515221a09011701060f18 66
    0x2c070080c580410620071b0a41001461600d01d00700300b1440822619581c02a104030b903000d030b489a0300d0b0000e234041e0b0400d452010440c40710000861441c1000b4010754030141303039010513518140c00642c200d80140c09680506400036845411030b6510381c2c041c0c8040d00311405060038400b1400540c20817131066100e00449040f0720854640001d260f142141c034240c0d02809450900d400c00d0414003810400054000960900020118a60b2280c0c00800c4124805410450720300b1264410030040c8174101048204428480e40410800000010b118040f55006501030384d000307054011082c141e01c424888681c002d6510036905605924907248000c40f40020381c0168a41e51002c141042103130030071b1098a00502c000d8424200003c8030303100301003441c4903589420143d403504100300d400d0844c0c0c054601c00905540b0762a004400c5001c10080d03c590014101240019440c070119405d03074030001400f504a801c50388608202411400c0d0584680002142c20121010074020008188419113801540421030a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 713469352 1250 713468102 713468113
    0x80a12140114151216031e2301180e1c0206070906090e180321060310140f04171c060501021b010f0513030606080d0c0807171902 57
    0x81c020b0002a141e50301e100c1c483d852040c00082811010002d680784d12018038482001d030110900c0381078005251407004e4910441c1c1c11100300700b52022561050001f004021b2044000d01101141001507010034001c0100d500070011a401081d012500107a01340749042c01521010041b101c41208580340d50903102c03005901c00020b10a8850b0001010700241949103801e01c185400e024116507000e02c042c1184151380011404144c1e818000d10681392001400015800000403c03204040026402d55299102e405902c00d0285804200e10a43d607601c0103d00c00020300f5541c0c8143c0d103100d0f540050003134642e14928034103603910221001c000c148100104890001440e510102817048541d5900842d0540d844100b994014800340c0c01c95003038168091805803410441c455046480d40242c14a46d81c44070708800010041002c9500082c00790303041c2e4000c0301c100711a5064115407404c4110405045c1c90020058039011800031b1001d6041620104071561030158040041030703030104034091100058104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 713470602 1250 713469352 713469389
    0x19050a09020108100317090619020a120c0506040f0f020303030f090d090308030f09070f08030c010c050f04150e09090c030606060310060e03010f020403030c050705040504080a121401 80
    0xf4443e6402007100c0102941903800d658804c2040340100b03183c0d82c1125004a100c02803551000d0403581e108100b145000040e410b0601e000e940c0d01d00c0c0d104102c0c2c518030b03a80030703074107010744940300d20b5480c241c0200080009480d04c1e00d481e006000c101c0d82c1598180403071000e000268908100550090494614013219071034101e0302c3c0c40c207125044d030215003084403c80041010800d090181d036040400d840e072150682d00c81d058854904192a13001e4080c2c10141c180004110381c000c005441d2400c1ca6200900c0302015203507048a0511a00d0420b29480c1b1062000380400b6440e2502d00d416041c003401c01e0300c0410344090001c3d001210840d980d0b030256100307180040039818140300064100c641581c00e00c0c00c60402540d12000b0440314000c010400043e1009504159000d41240c5070140381104110341c2c3e0341d100d00740182040100002640c45115121000070035041a2003203500c2260050061400e2911030001140c0c450f55040e0343c01c04194136074005400a00410b031005d8000c0a000d4581d4501d40c11 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 713471852 1250 713470602 713470607
    0x20102d0f2607050301241205070c06061701060b0c03030106050a020c03030d0605031507020c060c070b0304050616050a09121113020a020f011a010c080f0f0d050c0c0a080319050a090201 81
    0x1120102c0401c03c842448100b484190020200020140847c80c041815030710035608840359040c1c0e81014180c1c606007000001d510080648131404150042d0080c0005034403005200040d1040d41c079044055441040100314141c13046019002c05103217441a11881440703440005e01d5900700305c110200c0b4075a00c040030886490100202c1400642c10b4070080350a01d0120310194413054000b840c58040c1e100051802c003205824407250f03028101c804000c0361039003400c0c1401d503580d200031102030095034041034240c0b5249000c0e009a480c4900c161342c3d40c00889007444c0c0ca00014580780c2000311094102100d10b10301980d2000140440701094000041c0c860040e42e00c002e20300000052204041e9150440b0200109044d4640c2c80c0310788420309245082d1252807a02c600e2070b20a004210340f4482c40496164055102000102100c124122042c0400d403078150b4641414444c245d071641c030300d9101c4000000005c1004010f10f602400c403000d4014812502540d01c000e9a100700c840341152907030ba045103030440d038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 713473102 1250 713471852 713471879
    0xc14191b060213051f210e07120501050f1005040c031103130201030f0b09040f0f0212010f0c17070f020f0a03030203040b070302090a0320102d0f2607050301 69
    0x400311040900040c1c4000a840c41490003c1b5040d10803c420241e80324a00b2504070740d00b50300080703085510f05a07413881e10128000030b1030b0301100d195007001c0200d01c111490802c0c0d103000704040855a0a52440c0c58100f200400416003400b00785230301c4c1c911000c1312030098009940710300d0301c1c4249101013040da80300042c1107480c1800c1d80d820b010324003102c100c480c1c2c84d0b802056621980c07007441d1a992006505142c4192840544c00951000f07001400e09401c84040d0000d524030710003100103002c0c00903844000c3d102c90329400c11940d007030300241001810480c0b060040d24509002d0380151001600313444442401d213a40d0725021740109800005010410441c0c21141c1d600142510701142049034503c0050301e0252984406001c40142000c64020328802c49041c0b03840000041c440d880c0942e003100b02a002081c01100d001c40e600f002c1c1d416201100e4442c0340040381034031136070380d0b05600d02e4000000d6850030004406400d410540d0103462461035001e1403030500454641d1203443c7c0700d61401d001d801c0c02c86c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 713474352 1250 713473102 713473129
    0x10612061d0703270323160b010807180906140112050610030c06080c122403010b0a1215020307030b030610060203030c0f070b0403030c14191b06021305 67
    0x40d80d103010701011000b1071000361003c1c0c0c1882c00d28030194400e8510505181c010100006d5207100146884100d0500c41464100710b1056501c046503030390f902059510341c410382c0700c0d45a00030803041c0e60400241c09584400c003103030301c20740c4c0010f40f04420555000c5454402d812007200c0d0003180c02e02c5000d1000c2005503550120101c1c026081590a40d40c6140c00311182d481183c040c000f0540100f03203d48450800d039114010f02d14219507142c540350300025941021810444102150b04540d188541010300035540110400740100316480d1a003020808900c0300380d10b003036514000c0000c4051107008a800158060141660301180f0301445204041c20f0400140018030944c61000e42004403a0700402640d038452110107110307032628208800b0b2101803041c1a4000c050f203045d142040101609540030b4500c8030042ea44081e4850515034400d2400d03c28081450b01c141e100c50f0f1900c0710103100e04980000144107007110041825250303a130500343d80240b86c03848900903140c0000c2c030103402c20b5414118103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 713475602 1250 713474352 713474381
    0x4051c022505063a09031205042004091407030519030c060209040e030c10050c12010302090a110a0309291501140403030309060b0414010612061d0703 66
    0x3a1481d00c8001045403003118114800030019100c03d80800744c000301c19440548189000702e202c4038200040704024400401e048003c42c00d00c400108030b42000784142842240d00010101001030380da144c5c1c9689201c142c2000d6481512503100c0300000d45800c0d6001c52002c4428000c1003900c0c1140341140c10111204280c80040c1e16103501c400202c0e50001d84a51615000400140d03540f141e01c0c0450041c101e8801401024400024100304114001540f446180314a2408000640701c0c0070442c01c2c42c1c031406440140301c0902f20014005403500501c0507421404103000010070b04a01e20900c0451380040c0300b103a011a5079200c032a010710906a02109001c18504158841d40021404801545801611a07082100f00210099140c8d00919811640c08c0138501040e80391b5030341c2d1800402030580c1c1d52040340d50600f415908a06404c1c140101c80e0300c140c85030f900b01a035a0905500721000803109120200407502d4a00000e10005482c9501d070400e08a02c103500481d180000d0080c054620520f0b520a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 713476852 1250 713475602 713475673
    0x9060302090f1303110c0603180d09051e13150602060603030703080708130804170c0a03080405090a060f030609120c0b070e2704120f09090504051c02 66
    0x102498418925525a84c5400c14441511205024910b00000000c1460b000341c400800d02090321440c07002d000c0085584c10440e00c0340d0000ca502141c4203c85445059085000c03030300c4500c12880d0042500d0700400c005070030420641e030802c890340242c1d0482095071107001d01c840b209001c803550502c16141d003c94203a005501c0c2528030340d030050104c40c000b00488104860300d8003003400b40d0001c4c4011102c1c01d400c00901500c581e19480c8441c0261030084400c0003c4c421581082100d0074051070541c1104d411042c04c82c2060315101c140190200c0003001c48000550f5800c0104610044600c11400b56004d81c400080d1a0910318000507010341d000c0c030000c10702c05000511000183c5000c0926072040007132400c02100c10058000c41e48880c034280c039075030804521400903506101940520b40c4030b60b00442c800318503040952821345a021071181000c001803c404018803560240307800154010f8400c6040710b050f0101c40702e001c2c000d1a80c041900005810003401960b9003007036001c0d5490341941001e400b0a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 713478102 1250 713476852 713476861
    0x703090c060503070e151e040501020c0d050607270305030a2604030f0309080316140a020d0311070f0c03060e01060503031903150b0909070801060c06090602040f09060302090f 77
    0x10f1101c29a61544d0384582d00c501940701c0c45078106d000b91409407820214100a428000390000d8103601702e801218014420050400c0c0c1c14038090400d1284c19802a01038a0b0f00d4540c194100d81e071030020502131124000d4100e008282115040880c0015805076000d140c40d000300080040450403840080100c60a40019249074403011701d0308150081da16003080c11491032880b1094000d820f6820010b03100410100c2000b08103808903800b0090b18000c1d503500c407018848a0f210f02143c2c0581101c801c01640110a0129014002d51015540b5510007500b1810803806503144030071710038455412a03124100540c05c00420945008000c609038010000744646820040480d540380611202c6c5041d564aa98020f15580d020b9801603030034840304074000b016681c442519200c02d500c2003030514040d4482500040c103107032044441e00e060f50341c1035441c281c08100544450010303003a568004d90720790381d0030000040d02c80071208044c40100910440411070620318010001c1020b801040044c50404040030003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 713479352 1250 713478102 713478107
    0x50717070e011101110c03090f011404030b0c07061a090106020d140708040f0b03041e03090b0c16060207180b210709060303030e010b04140a020d0b0303030703090c06050307 76
    0xa4248180c207192003191410001c200602400c8040002102c40178005602c5810800101c01881d54400903101c80b141d0144031001100c03600010030b007507600c610b810300c42440001c405a45e0590000e50303e00c1110b046c5102d944609088507109224032069003011381d5100741038282200c010340100b00c140080c020f810001076002d488140700f20300040c4240f10005e0200e0401c0a9602a10080c2c07c0e51058040080c0d101c40c14100300c1d500948041d65542e00d81c0d00d250610101c4440300901740fa030306590b00107105180c500ca04d03401d81c000f6441012580904d00101c00c01c0441c0d00d40b4200282840d500620000380f902100d41c0001d0703881020100c501e81848215403040d00c42048250b00d8145007411131060b10f200e01141404c040c0b0540180792411b0030204000103040d0b05411000107860640000c22030309199208000442e00030807200d030310003c8100001204518158068460380a4038400458011240f40002e41154000c035400004240c0d2034003001d06020191200001400c20360070701d1441c604250201 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 713480602 1250 713479352 713479367
    0xd140603300f0d0c02100e0c0909031207031a04020c03120702031902010f0b030c0f0f0d35120a02071104021303140d0507020f010c120305071707 64
    0x1406038280003490850701c0704101c1d0121110400b05411072500e4101d00760402c40070300659003210780144101c04100124550501c104800e8206241c0107180300c5100c0710a0281d07510005080b101d03207000a001844e1562000040c0500c10900e540d00000d4483c51041841044d1541904c0799000701e02c1800101a41c0314004100e07240d0100c080080c44841c1d9541104916511403821190352040308801180409901500500c105903034000c03041c48140540001d0503a141011005641d000603e00103c00541c1440355440d103000b070000e462400181655240c4060302849440740c0040c11505290304086c01100c9804103074903000ea003031719900e801080c0846a0031800090502154264001800c00810012520344920441d011304159260000f10881d41c00c0840d091000755440348003a0750001c001003010488045104068443c9802d0811540030b100050090044850510190000342e0004ca00610306905003126903550104107494000c4004107862440c00c014482008100c0c02e0010a5401403070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 713481852 1250 713480602 713480653
    0x3090604140a0506011a0c0a1410020928120b0412170408031906151d01020a1e020303041530090c2318060a0b070602040b0d140603 58
    0x4210000d9080a820380114447d4448171100c078030911407100d04005c8840c0540c000310b603650042c1c41c403516548100341c0030780c45a8502c540c1d001c1c02c02035000070001c0d09001c81010040595444000032502c40081021a44040300b0075211110020f08100801206400351034410251380740a0200d44003200d000500ca010207400101b40c0100400050b140000402c241f41240340e9000c0280000f950301d650405083e50344144401c0002c4903200c0e031030501c500c101d01d40301c50002c060380142005400e940f00c26104485002e04900d58000404184001d40d808001500103060307501c2140114500c0042d02602058900600741c4602045041c42c0a8032510070003541001c10090302e01240e004080e01e000b0780302c03040e1508011500ca4595604904c0c94550b4000e07094030a4050710f04a40042d903000341b0480020003150800e5101d6496402444040d0a5002030514a0b12880c005810641c40f40d041e004c80750090f400d400303034650350b440300140f0240d07858201a40203642600030f050b42d860404100c0590900300320 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 713483102 1250 713481852 713481869
    0x110a0e040b13020409061d0d0e01050d0b040507050a080924090a060608070519050906010c0c0801090f0b010e070e011b050f0303100f080a0b06010c020603090604140a050601 76
    0x300015500000b418a541c030055006004100f9454070f454240c0c014030411454190308a400010384405d110001081e81d40b400e9951102000300d420040111020380c0b0500100c000c16172a0962041c1c1c0b61618007950b4000c0700c46450b015255094103200030403c1c40001c2800036603500c00d00f01807680120000100c0000580c0004d508107543d14003842500c0c11030200c400500641c40e2a40000340da0a01140d440d09690301101d000030740c014102030b2000042541e020b000c0c1d0251300003011070b043e0342c084c0100462040c4141a41c0c00f1050707880411500315801d0709070995001000d0003c890411280c0c1c0002805080d2141c200403960900d1039004090605440782a414400c125007080c4c150801480b0160f40d030ad40c0300c02150888040130026903120307003091312210304061000402046106001c60864103640c1f450f001008040100d40b44d00502002c00303402141404624001000941c54610083d48035445a80003019241040d103030580b2462081c00d051111604800918400600046525030440b11100b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 713484352 1250 713483102 713483123
    0x1c0f0f0609020607060b090a020901170a0608032b1b03200d02070c050d030203071203060e090d18060e130b0402030f071421090a05010c020307110a0e04 67
    0x51400e04020661258040e41c400404100300341008266004048400030035140d00b0711075210002c5d44800d80c0039540b419404a24041104500c01d40444111a8809510301d00481c1d44c40da94044141113030310030700407955040f00801441480d0340c3c141c40716005501e007003031082150200c881c9801c130300c90042c1c00403101010b456030b9140f0703100840140c10550805c0d81002e500d540780100b0700e04100a5020750002c46219500300c0c400034183c58400b84803103205406401540c80c00b400d698034075801c140041d441c01c0c24150341e15008240060010308640c4114400001040682512000984518500028024072401c924014480304d81e00c50303100054003a0503a5100b07420041d00c1001e0303014105042010b81c0151011003081180c407440e4143c02c0c06040c03e9154141c0a15170246c0312442d43c0f2a80104100c5a6001d030000c0454006210390140d1002c40503007a00c5d501c0004d680c40600b940d0305403601074016800401ca0505000c1c283e220203070300d03110407034900b529180341c642d140c4400400200040e1030101d62 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 713485602 1250 713484352 713484383
    0x60f010c05010c17090c09010315060305120a02010e0106260a0b07200106050102060601050a020a0b01030506010f050402041206111b0607080603010c021b0a05040e010501051c0f 78
    0x106111520694008000c0c0302c400740801c8010305501010314040107040e070704004254170501c003082810041d100500100556821512110180b01407119180aa140c0e01c00700040800ea041c81035a09070405010000d98891240310000c0c00d540b104131130306440d645080001c0045400381c0c200e0000c030100711804540c0300d40707a400009040013164035000d00f002074841c081005103a4815a25502c8180d81c0042650721500005c07040c0c203c4055000e0b05015078006400305030381d0b41c010030180c00541c0030761044803403a20030349c2e0341c07000c0d580b5007a032040b525a405500180910381107101020b02820302035a0031401d03e444c0000c20300b80301b0040c00016190399620004070803d528101c04880d001002d44140307081c400c56507003040c0d50f00c50707084403402c0000710018081032140c94103000d284c400c00b020364002c01d2840450b191048500d82140604c0d54041303405800041c039030b01d503170080c610600d240800000e4298580b40900c1825404008800e40201c1000440000100420050b040c116001044440b81112 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 713486852 1250 713485602 713485607
    0xc01121401061103070510090c06090b04030b0c0904090605090c030a1502220305030703020c1e0f040612081909050303071b0f140307050109140114210906130308060f01 74
    0x440381c004d41240180c408047ea0452250814500d141c8545104107020742d940c0320890b0711440034042d43e404440d04000400c0841c0c000c4003c5a00301604045440c60032420400160441f0080c0c54101c07040344d1070f5001c1120180c414080030180c01010350183c00e001e01d080d0760b00e101e04610342900b858500d5000c202150303440113602c040046491195242040c054036828203d82c4c130303045440102c0c018820310b20020000c1c00c0140e0040003842044032041003c1541c0b40410514800440003542c0113503032841d0011385181c40542419142740204806a51031160003440c5a12240c074074004002c0c01405441080941c900004943c101c681001c400c1b00c42074034151f07000c04100319a500c030f6644030550b00c1000c61170880c003030004061140308030304503000942d41d0401550588645d06c1400500c0c8002c041200c102c2d4090042e9110440c1d0201403d8604940c002480f00c00e1034030302c03042c4000c041101c4d0401040c0c40c402c100c0c9a402413200c840b414145055950000e151300002030885d40610080000e0640590 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 713488102 1250 713486852 713486857
    0xa060e1510091a0616020f100c171213140a03210c0f05090112090b0105010215040f2a030b0619082107080c0c01121401061103 56
    0x3021194803802608010111184481550161860403460001c4620001c14512000010050040d11903030602880c2901c00c0d80e4500112016030300b01c40981a01da08513510100f241e0042c1c2d100e034a810303100407090304020b00785000c03018460304840d0041154825141202c040290302448440500115001a00d07026000d44100381030703500785110701c4d4050700405400109660301807541c44d140e0391a9041040d001403d85106c8c24000f000b00b000310101c0f610b424441c000401c860b04040c10840c0e00038903000042021242110400d5800310348400051009607414020550000c00c492180c403050300780754596074074107003203040000c184a01c44070480c0301d8a00705003003c0400344110062001025900d08007481001c0e001c56050344100759403600113507994040b017190f905036071a020040c10800616202c120320400c04a1400b07548407070034000d0303800203200c11005102c0c0c482400c0103041440e580710009401d07581e00c0032205140904100c01c0b01c8a02d03180f1400e8504407406803401030005400c040c030712410b61 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 713489208 1106 713488102 713488123
    0x90c030201120e100b040c080705040b07030e1c03090b0c070905090c100c15060302100309031808010603020f06030405030307180b03010e0a0e07080a060e 68
    0x5510407900d480c456480d03030030000f5200d4003e07071001e450004138030b1071850501d441d8420f41c030140c00c2c07901542107500c0d09410031101c0c0e410205005841c4d0302441c05040a845000700c2c940741411310480100d05080409000c0b49800c0360001c0c082001240d0703112046e40418521000040d03645501d808507940c0c0060303000503100e00d508003045407014040c060100105840742240d076494980c0d41c4a62819540229182c040e20040f1f14070380281240c4040b518103c0803071074254100050784074060360985078611481d0000e2456501c1c5819603496488485c00c20002c491904003207040041540800141d034001c03a03261581c6013000c42040b41c14841160000e00903081031000c14405801459090020700d050001025215142c03084684550002d07400440145080703800e0101d4402c0c140304554041a544016009003030902110907560300c440038004001551303c06250500040501c0400300c0c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 713309352 713489208 := by
  have h0 := BRFrame.cov_init 713309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 713309352 ≤ n) (h2 : n < 713489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
