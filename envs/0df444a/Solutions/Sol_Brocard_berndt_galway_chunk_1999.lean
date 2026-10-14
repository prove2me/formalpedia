-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1999
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:25:15.372661+00:00
-- url     : https://prove2.me/submissions/53430883-658f-4184-87d9-f8fd740ba3a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 359352517 ≤ n < 359532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 359353767 1250 359352517 359352533
    0xa090215030a020c010e061b2a0d030b1005030c0a090504290307061403091903110d1103091c0503030907030c06080c0415031508010b0a090621 63
    0x19480c4128903a0100030020350502c168040c2c88007414603c0280080032500b40d00d81d403607180c00c940c0c4060307541c03903000a60403003420138024044070510400d2000444842c0c40c5032940c000140c50007101594006031940074203e0707241c0250054168182c5241c9007590002c40e004e0f100740002040f04803c58004541510f28503c10f41d010001804050000c002c42c010903100c4028074604824840c448119210022a440c20002a0302c41180c01a541d090300540050710090196440501250301c00d1007842040b1035190b120b83c4050348064440c2d241c02610301d000ea541141061030807903101050003003120307240c0102c50002c02101d013001000c071000300c580c0001c40d40810b0184101d00018190f0301c0b0210410090110000310301050324001c0c400c01c0c445c95a1014100e4100100301c46c110b40c0558140701c00c01240e0080050482c07144940d06020036a04410280c0100c032010381e5200780080d0b91030310008081810080c03031340700252149180901480b8140300031009004c003030119400d1252002495681231103661 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 359355017 1250 359353767 359353789
    0xb0a09030f05010b040f0203090106050a0b180a211101050c1e03040314010204090e0303220212062703070f1b0312050301030201120513020f01030213060302070515040b0a0902 77
    0x1002004120400518440250802c82704030201e5860100c020901d8a4181d4084c4101e4062400b01480c0c0119075108815a18540c0e141035007207510110301149491600756030b0b0241181000900000700e02c541444820000244540c50510104100350030302c450000c58011191002181c046600d5036000b079026103036118130b51000c2e0219004001032001c1c03003010340082085407000d010600070061102001c170b803244019200d640ca9250641c521001c00001c2c00e102100322800103245c035130340c010048140740c10208100e03080d0034000c070040d040f07511b50044084c80d4082c0600020045083c00d03210381e60060385440c040c50240c02c440c000d003103a07128a40712203035160285520644521940c080d41c43d01a015800c2070004038081504041c1c1c21356495007c0c41180d10868449400002402c0140c003409181c5804603009410144c08020080c481c90044556400a00d455500103036108032506195080104c009055000c00560400b4003020030b031903400b03190b001228807030006003002213840041d00403030320303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 359356267 1250 359355017 359355019
    0x9010305060a2d02040305070f0b190c0f03120c02030c070e060301060305010c05030f070309020a05090612010527030408060105060d02090a030308071b02150d06120803040c0b0a09030f05010b 84
    0x3058000f110465401400442c0e10600c101c03011641c5810a20070341c118540154001c1c50001d01c80441406050004402c1c200e0082c00e100c00c0c84081d5886103583c2d4140e0a0081d80403451001a860031466540301c0d0904816150bc040d6007840300341d030483d507110f070218403031134a1190100f800f1800980c1c00b07502c05030045a112008028480c8503510140082e00119030340240000b1000c00a400907000703003d114201c07940245200400c5007170a080010080002d08120741190050120031412242403244600072501d03000426071082c8000300e60681c01e0505040440c80360008d0004024140c00003440c1815a182103c100303882e602e50b0a84d20009015010400d81d100d00e00708800814190001080c6025580a55501c10013229011120b0103000280030002c0d08030b40d03134100040c4001c64560242100700d41500c40811311796560310000d5030a640ad40c20582d08140300000380800c001d00160300030020401c622800d401c000070340c90b002c2c003005071030310020f0701122140f0050400c101c000c2d0705c410754802d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 359357517 1250 359356267 359356331
    0x10092102040e06041211070302010e130b0901170708030f030a0c0c0f060614040903020606150903013315080406091e020f04110f0d02040b0705010507090509010305060a 74
    0x1400707090101c42c48140c2c170359801c00b0030303075020b005151580c0105551003a2501030b103c00401512100500082076030344c2c00070020555888090450580c1c8054900c2d00174203500d90002100308012440b1030401030298080e001c01e51003008030200120802003569072110304071100081d01c0c0080310301505e003582c841d4401002c200000603000e040200603880b5806a6080120001e000c581b810306001c111014240040e000d40e000c1c40000e24140b5140b2684400307c51803200b054240500a0042401d442ea01c2c481c07200621003890000f07030010b1f00000d08019810400518804551604000c03c502d42004051722302080500340c005070904c90030b50030000c80560b01040c0521203208000384041e4058008000320311402085542c51003500e0240a521100250f81410b50300c0c0c81441c904127600ba0344604000050340c1d03001c3c0400600034001344080c000325030244001150314507064000a2403e12a80c1019220304150001071002c40d5001688641c081c012110005e0a021b4904d8030031b20b02600845103280c0c0d64 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 359358767 1250 359357517 359357521
    0x30406090b042d0506041202120c0f01051510080606071a100b040807090b0d050102030108070e0105100503130c080706200c0607120e060406090510092102040e06 71
    0x100e07030f90160700d082c100c040030111010301100c03054510280c55002600552100000c01c0100320041c0445050703203582e00440304011b424488047c55a0415040d59070150041c41ca1000d9a24007801280e034070864421b00f03c0303004410000050807103400e40110b00c0070003000c880056040d4542e0340485051a030881c4075030081e0f003031a40103c2189642150094902e031000700e00041c1e101310500540e429541c0e1400644015814107020400612050850550244100020101041080c801580a042c80c1d201034610035003029140d0040000c181d215a0040e003002004120190b80a000c0d81e0308400811061440300c21f150910030303558049500f00640900403135100103055a0840e05203591064400400c070030340102e841e9400e450700a11030800d80c01c14010416000000c6484290420841c0542030404140d0194400300d9600e4205420590115031503130070074005440c00007280b440c00c00d424982840d40f203080102c210b14818143ea105035210152000c8801107681e140c1100f40100390310300c120b038018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 359360017 1250 359358767 359358773
    0xc03120d0906050f04021305160e0a0506040b0c0d05070c050906180f180303010305070311010207080d0810051009030809060d0504050610050a080d0507060b04020a110105100515030406090b04 84
    0x840c4c2c003618120700c40d10304109007490581c440c0c00744903c103c05200400365a00e26403d820360780920910a650b500448070741c408110b503581d0720050005080381603446a10340c1c3d188401c0f280b80a202404d00000c0c041c0038080600042d4004123000305a8000b0f50b074041c15600d9083c08244251420403040b030000c421401001200c030b400420b0180b003064030389501400c0440c100b1030503480384028040603004c4d0300844018400b25070150f40e03011305540c040c03040312840b954030810503040110002c2c48000041201052109154901d00b4040c040d01c001c8860f1810141240c00240055a8a200040182e071000ca454103240d614101035031007005000109001c1842c2c07510304a5192082151824403110140c000424035003040322044041d1030540e001031141030045141504c06130003072802190302c60b07203034a01e6030680d45490001c0c10b0155001e445800703801d0810b03031105082d04c800030b14005041a03080c05c05c1000c0d5842c0e0600f07801c01340440703720076a0703529242031410103480c074410040c00410718601400300f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 359361267 1250 359360017 359360041
    0xa0b0d061b0909060f05090414030301090b0a0605120a0f0e0708010603060e1603060e0a0c0605120108010507090605070809090705040314010209090a0f14070c060e0c03120d090605 79
    0x98034541d92901c50b096115020700003114403034000c031504042002414400d504014081540160040c0d021004c2d19482d1300d9071b0351031507000741c0103510016152000602c203400c0c800303105005032405080c0036003002c201c41c81c1c0013000b90707008248000a588518049004e084c641c0d028418030306801d03043c1c655082c0c41e409003070f018248901c01100c40b145052000006100085030702d00c003418201040c02d0080b031840d00e8110140c051584041c1080c090606a2070024451600f0500103000c580c507115220180c1d004100303a2108160b018800f6a411f1400700030005500074801d100340d482a0a0803501c0e2980c40c14010210f00070781880d0358200040009111200e80c1001c06002164810104204180c1041c0c074503600381c0c083c600400d0303040030003030001c940c01034607641180b1000c41c00c020000400c81045c030b0104070460301c10703a0b1304c1307000c40d50009009084c0040390150502c248070500c010514135110801281d941c0d24000c040b038010980210f0003a072041c0f220340204c150190050010b0015007050006944 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 359362517 1250 359361267 359361311
    0xd0c03020a17060c0405090417041e140406060219030203130b040314030a020c12030c06040605070906030911061b07032913060c11060a06030302060714030a0b0d06 72
    0xb60520070000003804145804003120182e94000c0c00801031503d861ba18580c4404520100c5540c1d20418480402d58001111040c164102c4681c035600203603103000d4820b00c041c10500c0c01c00d400b550a182e024403802c0d03000200c02c901d40c004040030340e283d240f56040490440c0140305110301561600180000c540c02c0c01405402500e01500b04038111030701001555950780705170640c09001d81c0155040b900c16241182c0180130a924600c01d4034540041c00112608100007150211880ca03903c200780300d0b19680c050b01950140080e802c04004801c0107032114016144243d039410710929001030042c04024246440d44010045181100c44a5840f441c01c444031110400a4444080c0040c2d44010030800070032071716000d40460403540a01510544a0501a03c1d800102c0e40600135500300ca00e136540320420170b40d88504140c0307900203100b5055240084c20600098007030781c01c00c0444c2ca0114061174550086030f4204052500001c7c440101d000442c00296440e1000f508292408501018050300909803403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 359363767 1250 359362517 359362559
    0x80a0209070c03140d0603050f010c0e1207140f100816050a21021603051c0b01050a05070302190602120a020301060c020904150501080a0507050103050402010e0d0c03020a 75
    0x14507a01c0c10001c03182d0380240340c005070028988424a48941c1c01002c0203252140e0082c00205060b6202d0301c03400e14150b8040c0c00f280700da039550400301c1c1802d944030300c42000d000400c4620141d07981d005070181c2d65400890090481c000c02030108491030750f0f035030b80c045103510328090280c038160814540c0107002048111002e82036040b803030202c603500d248114101c1711510841c4e02c0c2d05204000701490380000c400a030301012400340c1d08010030543c1481e0561810045440780e83c406540d581c20300010600c0c07202c1914588a1030307051401321078007a03810505071102d41e41ca03498095116546400c00301d20b00001d10341410a20361007070780703040240a62038009002207041c1049000036500d681543d07008901c02481001c0006440040d5000146004a1000e40250044203842406045d080150048070000e900c0f03081c103548a13914010800005108000c0105000d0804004030720340307500040c10002c034106025214007103100d078035130030401054901c4016507009025000d07030300d403649001000c0c03000d080f07000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 359365017 1250 359363767 359363779
    0x70807150503070f0509030f061f0f082e02070303020d1a01081623070215031302040504060f0c0503060a080f0a1124030106081815091501080a02 64
    0x341100c900500440b4003c0c0d8842c0d8600030080c1d41004100c4a40e041481075031740c107014090305c5020090040100c0e45c0034801c211002c2803d03a2280300c0a030b107a100554441c442c072040c402b9041050780c4000c00e01009401d4450b90025406801840503040c003035014110404480c40894005c0034540d065002d0305036101110000c1002c803100380d85100302c01b202c1d03445450005840000107221035000b4401c1c2c20134001c41c1c1c14000350b00c205016240b52158186020a550801c001c2002800e6251201000002c1c42490b410545107040c550600074030342c5090b4401030300071900d0340080340421509074080d0070b405241c19070070408180e81000050466005540c65032007441410b1010403907160120f0b0b182d404894202c0108119074295071500071058802d000b40e588101d10720300258070401c40028441808000c98003581c0e1760740c109800030300290009000048070246000ca000760000c1c000904d5000c498042d0b000d009580c0d55680301d680f0b07000300394004594111800b800083d0710303400080c600000c03034401c07101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 359366267 1250 359365017 359365049
    0x304031b060207150203060306160917060a050f0c031302010e19090b0414150a05031228020a0f06020417060114010c0218090a06110a090603020f0a080c0c070807 71
    0x1316200340d02099949541c99009100811000a010109210040035130b00f01020000d6503402081c0b6500102e460a14082e0006002c20010181c5c501c160383c0e03c290111090145420251200c0300301c0e0100800d4480b404c0d1032400d4140035a13000d40c10701c2d10140d400400d940c446500b607000b0b200307000400e8410080050704180d01a10700780b5250103a03001104100b0803507019981c840c802650070156248403582c00c03001c015404140c2d52418010003681200d064049644d64200084040d20301680d642c050b2071a5070f03002004c000d050390129201d103c3d9504440c00002e00442030070004001d11035036004c021001080b011600c42c0322404110507048a070041445040004204015101007803030090007580700000a64444401e076484074a540c11642d046c0890f0790240c07075039554400f1503081c01c06144610340042650341806a0141c0c0400c06400070780b406600b0304d4014010b1901501500d8001c00c1440003420008880040c4207081d100c62009040403644126907400310180c48440900a04c4800c4511802d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 359367517 1250 359366267 359366303
    0x903030b0307120602030615040602060907120807061d031303110a05010509120f01090309033003020c03221514030613090f031d040e060a020304031b060207 69
    0x10400100c03000383c0d008260100c41591448002d42c00246100d900072840000500c1d40d4642001030006049260002d100c80d0810a10b43e500e041101d601000c280680c040144002407000340030b60300ca0982c04000440d060000806160880d1450110700280d8400421444007403443c49090000b103c1c001c0b20810705c211b0100092102d013001502030103000c80c4080180612605068500090301504e40c415183c0d50000030042c282522000300e02580007603000c04080c0180f04a0703420501440f101310003130303070700103907084441030080c4002e0b450300700515501141e0b904150741300340121001041c0184c101d00e0b94100c0ca40c0703c0001c54603140141e20180544511286215008100f0032031900c2c6400e2189085903078800420401c01c001340d010b01107940e1100d07040b000144100e03106c00030b007030b200e915822814200c94401e0003e40c3c0301c041c030080c4603e0520103003503500580850141d420928041025a8907603a906007940d43d0841e000300c4e0035034820400c001c0b8003440783e07981c0035040d281d100d841c42100c112030400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 359368767 1250 359367517 359367523
    0x9090c05040e1501170a0501030b07020a020f100c0f1203060b07170703030f0f0c030b031504060902010507020910051302070803131e0503071509050703030503061801090903030b03 79
    0xb000305030700e0501d4071002c1140c00008042100e8680014074108810070007a07040b01500c4d410682d40424035944990050042001600025070f00031050310040003500032540010b440c1c9451351403501d000700041500ca00416100d0300c003483c1c0c05a0401450070f8100d00903c1c01d10f000b03015580d59400040c1c0b50032400304118140c9421100d030103400511881e074200d8400c0200ca060341c8050411000e0582c0c44520b5540d102042c01109004900c0d03140004203248807807400f4064540f40f91090b88280c10086090700201080196a60415000790001612002610050350350b88600c22010f940301e03104000b0071003045c0d81c2002c00c40907203c0540e408d000a510841418041e40070740400204010b40920000b070701d405048400c1c0d500c00c2e0046070029441d94110744034042c02014058192010341002501d001407000580e040504454036030400c008441031511210f0b114181400000c042207400000f02d101c60f503450540300c0d402c1c14940d403107909550350707814444004d2105060032070120b0308000300104589004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 359370017 1250 359368767 359368769
    0x1d19060308041a040f0602010b0111061e0c160b0103060e06011226040b04050901121110050903101a041406120304080a060209280b072109090c0504 65
    0x3102505003064180b0501c08014010303107202c3c001c000c4081c000002c0c0d01c19855100b10003480290000160f80c07646800051942643c80b141052662084090080c628401078403030b80700400404a806903a1100200070b2a00d01c56400c101c80c0c0c3c04240c00302d02c014400e641c082103040300e00c40c0d0300400c0703c3c41c8102c2c051600d80c2c10901c20300c103011b140e503c0075001140c0516000703503018290402104110400301004817498105400038600d4050114080c0014102280180e014049207661807289040f40d41d6401403a11410721007038014007404001102ea280a07800307407101c0e100c00509898200d5041e4050000405480701c02ca5400000000344000c030b03040a00c600c01d8001c031040c0300e048480d614076061040d03032000540484003904c400c00000a0031441804103c80c20b500ca03010169170340741c00b0300400590200e0344180c98080d46092400b02300705080c0850b00d10403556191601502c3c0c0041d403c20b8104c5440c048090303150840e035100c0e41503000b1b40c04a016400ea840303c0c4420403c804003483e0855440c000c0e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 359371267 1250 359370017 359370023
    0xe0d08010b032212110c03030c03090409020d060e03030a0506100c060b0a1707060e0316150c0f0c090507050c07170f1c0f05030903030f04020a1d190603 67
    0x1c0022400c0390711114000741038800150300000c1c3d900740654030000300000382104c04000468010000f090b0340014480d041e90700c80100e0055040c6000131120076100d21400144521450f40c80c00503108544030700203c60004e5070405420001c11510b1826940c9a6208442000d4058504030002d1154980016585240d001c00c1e62149403100c1a80d46450081c03040d41206540b003a2841c5002400000c401540803851781e041e03000d0300c10b65160000103041c115041c4c926500c40d80089071350741c8043c000c0c0301b218002c550200c170004a403500c10200656400c502010064040c058421050b030a020507a08160100e1f00c58100c100070903603400c0c0080b203031402040c5a0307010703e0700b2a40080000c600d1541c04076103c4016a03081e203010508104071645402040d070603180540350030445c403040304c5400a50001d14400079050503032071880c00f03844890300c5e0b200c01002009900b01319001701c1c0554441c0d240c40380103420140b01811010101d6410540394140c120784007005040242c8050b840345145002d07003000c036a4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 359372517 1250 359371267 359371289
    0x20109030e0103050f130503091002071409090604060f110a0c02030601290306030c181005010507080a050c070b0c0307060e0712020907030e072c060603070f030f09060e0d0801 77
    0x110b10b90381503484400c40c84156141d1000340218020aea445404400d5082581d07001071069510b89012511800007680700c503886501000e0803c0410407022900301c1c0c0c095405140000c0e10826894020010f001240e403c0244c0e0901107180107210747c12800c0034181314003c904071001aa607a00310482c0d1074081040e0380111a40414042c951b181646d40a15080b100c014103483e00701548d42d02052070050203220100c0380e00c030041c0601000007001c26440001e4107007844d12a180034100e4950700c019101e4500d21104026000480e295007203010f01003a0b02410030f5444aa6441c84014452039a0303400c1180240c1d6181c0c40c000d238102c43d034071000503c0c5003210702e20a00104003090980070070039180700050649042c1500c550380c2c000405001c0c00a080540b00d95607440b1015100760b1321191000703910401512079080e200040c040c071580c802e0142d07644400980781c491000380c08150103e010380085108420b18505001404080000301d4100a80c100240005c540326000042400c036170f007075000e02c24000444 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 359373767 1250 359372517 359372521
    0x1504020f0f0f04090813060206060108060d11040905060601020c010306030b061c06050108033c030703090b0c0304170f042309072f060a0c02150403020109030e0103050f 74
    0x10410002204800398000c10b1828864a880007140542d211840c049032201c0001a640e24902400d14900003c0c224a20061203036103400800600784050240c0942d104000104186042082c041d417042d8515a000e8014010300d2000e240c0305941d50026a0303203a015008038400c05940b5407080c85007900b140c0d0860034a640075150002404156214903800044040c1031014000201d40b01e402514001c100810040d03548800d802003004407070740c1007211043c101d0120700700000d00f800c90310914208003525800b9150350342c603060b0042e8014040c0321401008070000104214401c0700c0c00010714801d0b0b006800020850038120894100d0f80704902400c0c20301c210038802440480c8007445006058510407107500c1098504200042c02c280003290314030001541c0840342c0c40032050426140d0160300c03201800e0105c004814414549820005002100c11a9502801401103201b0015034a10208840700c0141704c1c06c0600b40203000c0c00383c8440c254085190084041e0a41d44a0b200d240c2c80b402404120342c2c425 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 359375017 1250 359373767 359373769
    0x2070f08070c0f15091701180b0702060612030a1110090b010e060306010602150a06181a03071206020f070b0112030215060603070338031b100507031809020c1504020f 73
    0x6501c06244a805541d0317601d030043c0080340b4905040d050207009c0c1d40004072926041030004c2c5400401070505001d500c004034402030001d400030944203d02664100b01d49003006044a003850000c0f0b10499804003410481e0100c02c1c041c1514402d410f17141f140c403204d481c0c2d030750b140241a9603032800c1c8148030040e8809443e803c0c540a14030350329600055910004541d507591005604904211907500c2d00d02640c2d203182c0e410100301280c80500d00c45909074040d104252a00c100c00380c18848044010b00090b0f000100003801c1c1c1409000c8540b85588146195000c0d43c44081c45000d01c03280d01811030140c4128194040c800c5102d284040c41900c006100d58a5603aa4030000c034090300b000c2042e01c0d00c0216046841e0003038041c101c440c0c03800703040740c52020641000c003004162400c886030f507903101d020461002c1c8841ea034480100c109520781107804c09694403200d0b8541152424810303520710f00c1103580500d020072169101c0d0014140a1604012110303803048082d4074040030b4209a038001d6000c000c1000c0c424003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 359376267 1250 359375017 359375039
    0xb070f0c09060609080f28080a0806032b0e040f060312080a050907210506151e03100e03070506040f1a15010f0504080f0d030507050a0c0602070f08070c0f1509 70
    0x11150484d206d40401307507201d548608c102c1c0c004402d42c40c086200002000007a08007000034259100614401d01009102c4883c510382407685d01c0d05001c100203000195014544070360704581180e44081100f0442242d6a040c005001220303c1030800000d81250301044c1d02c0991801031900401c2d010000c0c10301079150050220365280000702c04a8617110b182c1514000c108140001c501c034845144040172004007402c10000c041c0c034032800320140b114129806906a4400241202a00130250f40010756a0071511001d0315600800c10010021712074081000100b01e0a04134100c80d05100344600582080210122101c20000b1560804011240e5103110001e620540e404003042d10141401450191a40c40c040d09100e1403081c040141e034840c0900b02c044c503515100c0c5d0b5a10513400d240840c20648a580f009041414075030014040700c0c7c0204d507075001c1c0b05940400443c069880041656a910315140002d1056610310541c900c50700d0200001529100b00c0b61000901d032015074070580000d003003c1c01038203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 359377517 1250 359376267 359376313
    0x8031801140c0c011107034103091e130c0e04110c0706020106060f03020d0b09040312060905090a022106012405130b070f0c09060609080f 61
    0x2041081816440c281070403480002e1030000480c00250492020240004d007040c41140b036011500c1d0f03c1003c0070804901c640c1d04042c0202150f41c0120034110140c81405d04c40300d18903042003080c0c821440a9821850000300402c4440004e480ea0903250480e1001c2e0392400c03040386001500a401c14500c604c2180c040c3c0e100d001d681031142030907001e4400001c00b144c100c0d03203612040c04000704001801405050304010400c001c04940c4020700c009420081c00824000c0300c071840070107054000c211002c00550681050180590182c0303103113403614040c200200290380801d000c0c070f0098680304c80410b0000403401100d21480c03800e4010150f689041d401c0c84951003886850f03251190400034445142241840424000c000381da2114100c08141c00b140702500420400860500508001c8007085810200002d0110341950b00c042d034950540d410701e000c030354010b5100280004498000424440b02d164020000e8444c0c1da0b48414440c0c1d100c0340382540d1201c456038a61511703804240441042d00311405624 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 359378767 1250 359377517 359377519
    0x312012103050d14090705040b100c0b25080a0f15120f020301050a02030441030d0e07080c150906091f030614100f141b0a06110301080318 61
    0x340c229600716001c0080c04094903050700c1c46e001654200103a150078007411841c0c46049451004c1c0d4410b0000103045082408001001e001103c000110b0040500c401d2209010360244400e03070003210043c0c01031150300205c4404001c10f1a000d48000e02d90418420410195042c007402000a03003440a040c21940d001c41003100c1480e01d03070000c100181c80a00400b4000c0e4580400541c0380d00702454145250700c121141060080002d1680071006c106022017081c0f0703811280d20710780380c038a404c06c0d00f0780c154401c08404800160900c0301540c03d0100000300c070b8044444440503204281d0840d41040070120761407401c3d0700043c009100d0f00070289042070040255103c0109a401034a51803a201089100102c9139007000c2541c1c1d920800c8034641102a00310000c2c01114042043c8040c07920141401460ba070b0010100300340b1644002011010b481214080000c2d1180c85032011054a01181e446010700320440d440380c04c0046520507100400d003038074162068440030b107041280045001c51a800210300c41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 359380017 1250 359378767 359378771
    0x60801061e0e0d02060d2f070b06040b09100302030610080a060b03190f02040b0f06031602070b070605040c060206040503040b090102010b0409060f200405010e030f010e0312012103050d 81
    0x86006170380f0750008202001c0303840c03000b1a032100d0b8203503050701140e01e0000158818111200c0300b8101100c500841d00c05a03400030b19400d01f51a07090100f0018182c40480d19007240301c1500b84061348034040c84080886c0e101320111260b0307a0b2400001444000c0c540704c3c188407613010b980703171a00241503504118586c080280445035903465070300b5040c0c030181d4546820349a030700e607520214081d41404d0041114602e4242d0300c042c40300c10410040b0303059100013082107203c480c0d03862040e25410710901c1140018851a0340454403140746041140040205590803104c2d4102ca03640020214008070b100c070f2084c1e030048061803c1c94a01800d1041c00c0d07000400980c115585c03218440d132299101e12030202d03a903000b602e00040409052403820100c802c482550b005180e1014240309080c011003040304d0940e034080c07038280c0b82600d9030070200e0b2400d141400b01e07001a50901c1a030221042001001c2c040300c488403170049074141da803007504026074480340f0158450440291110345c00700f40100000d042d580114400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 359381267 1250 359380017 359380039
    0xc03051b040e0c121c050c1204050117040203010608011109090114010912170703030f0b220b0d050f01050403170f0c160f03020607020d03021908061203030f01060801061e0e 76
    0x19042d0340c0c1000485d1440407842c045042c520103601002001e0920b00b4a81800d49882d051a00180c1046c030b1116207082645950400501152420f420070341c010003141000b8004002d4041d00a2a076405c00c1000301e001d00d00c2500001102c0014150406404c03506860724158541040c0c0740c0010000641005c0c0c41c09000c450150068501d04001000240d0203a075001801000146604082da181c00c40b0f524411031092031000c05100d0b80c5100540c2d50303071031117900060314030f000c0b004240542c03122030300601315018407400540c4e15081900250b105502c25030303c09044900c15040191a01c4082c2c0b1141001e1180d400002d1100c0301d070000620117a00031509003031040d059030b62540310101d100d4400320010381108080c800280d804000d040081081800d082d0b0138222008415a8110520210201004100b102141355512000d503c00d000c00c0501c405c0d41c5d83d80c542881c408c0059a002c2c450a0000b62000b4000500c2070311401411a0384100300660f044411000d180c11030b070b01380f142c111503940a003001c40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 359382517 1250 359381267 359381293
    0xc040e0c0c0a050601060305070e09060105160605010e0109110304121d03100906051612151a040e0601030b06030402090606090a0303020105010f1403030a030203130c03051b040e0c12 80
    0x82c6800c0144140018002c07981407080040aa0381c0140201092044600040000c0e42e54500080e41c410300a181041c3c5412003c1c0d821800c09001d42c03c0600324900d001c0022401007503d81c1c03158141d8031010000d01005902015842c0284800c176409002c2250300000341c10301034031170f440c021280e890b05a03030389041c20103000c000380c2003494084400107200e5555040300108159070140b154007542a0515102744411024080e140d40d80c0c08610301055503440d500071400c09100503902d0301400701c20000119400460b25150b10b00d521a01884d02d2002d1550b000496641c82401404c1410f64050b08040c00c64440354240300103207d020b041168010810b020400c42c42d02d80111101c02103004e680040746551401904140d80d00f85908500100c940200e4041110b44000040710030301591840e00581d0307035645a0091a0400d0b244100a00b6030020410000c24880c0000d002990001404000c2d81c2004200c0c041101720303220000070143d5030308982c000b1982840c24411006101072043c003075459003002c1038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 359383767 1250 359382517 359382523
    0xc0b0712112205031b12100c0f080603010504020a03140c030f07030c08060c040e0a060f15030c030e060a0c0c050a05150a0905030f0a050d110405011103030c040e0c0c 73
    0x282c0740304491102d19a1642d030b10100742c444500280310039001380c040718080d80c03415000c0070218142d090003414088141e20130000c1c10842e851541c10030082c2000182d0400c01d00500015014000c0c10014820001040040c50b041c450a40215030043c2004c9101c0e141d42e03101080d900100c03074054054010a002c01742183c0342403148034020062400070340001401d500d4407070038001ea00c1e0840041c51740311008001080404000b00c500b62400b400310b40c0c1480e528550782c4d00c0075182e1a04000410416614001801607031811038400c500b50984090041c214211003c030111001d0300941c0886600c02008241403000790b900000c44840c1ca45003954207000746d5119507180c66000003003180e1a40c4039481d692001a2504000783c2c200c00001010f00043c00145c80781c2d590380c02036040c2c610150000094641d1164000d204890f010602e810b810300c88105160100f0b240d50300148500d90224190701d248004c2440040201e034400c210084141e0f041504006509a0800d401802950341000400020740200810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 359385017 1250 359383767 359383777
    0xf02071a010f0e01050906010c02030a17040311040e07030209070201090215091503072f0d0e03120708040b03130803010806090c01030606170a0f0c0206060406060c0b071211 76
    0x16114461041d45001c0a000d01640300e0f034030812201c1d54801c010303c140e5071410351054103c81c00b481d05200c0e890395400020f0611781f11300030042051021920000c21110000b026000701d034003d80001c40c0d05282c520501081da960001900030a401515040c8014540b008032150032060038030001941e18034a9020680b040780108400e2511040421a1215803800c00c0000c61003d42400041c2d0071420f0004c0d01414081d4800c07950100103407480001600d02042000011001304460304607080f525008602414241036100418028000c00c940c0d881505400801c94000e039602c07a580614280c54184030055940010f0800303c1c50700c080c4450341021883d8000a180a0510031014104e0350410042907440c146c50108040c2c1898141507007000040e41183c0c0400104518410344201aa00d207c0610000c2c804407141d5846c0c00d1901031450700030b9038000b07016440303184195401c2190984420050314454002c0d000288040c1c81440081c410703c3c40b590b68090301280d071240c08112440180e0315400d10f5040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 359386267 1250 359385017 359385053
    0x100f1202130303050c0609010c050d050402060d020d09030801080c10230703180509060604060302160c060905120102031b180310020a1b0b06120309040c020303060a0801020414040f0207 81
    0x32170b078801420410700030507420601640c0204061100c2c000702030400d00408001d40220b5540340002025501d40e0320850310010501036045503102400b90f8044010301120394240c0c00a0300e0a400403514800000e584111100001c00440e03c00c4140b0a088078906102e00d90f03105030684820180340f070500008040c1c10000c2c42a282e80130706d421014040a598a05a44002c2c070079042001800b0b044e85a03403007101d007654014900540d9800300041e118165110200c1c0040c02003649c40b400240d4640d01480c500d0985000329020703110110401d0081d8240d000a03134011100b84c030340c015a07603c01090300000740382524070045a01100c00502000a040000c0034071242055500000c04002c0780b5844010044001104440404d143c1c001d606c1e00749036440000d11060190341d100c444040b0020081061710031194005000b8801c81c040a24000d441e60000d81c0c0840c00f44414440102d02d90006000f03a40980e070340c00c84050544007600e01080302030010f1000c102c14581d42040a0408104424140401008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 359387517 1250 359386267 359386277
    0x60403020a050d0305061e03010213080102031506070c050d030908060c032e0608100305032d070f02060f04080d110c03010b030613020303130e070e100f1202130303 72
    0xc0030b410b165041561020000c401c040ca00402c0110a039500f1210f07904184560003046412400304001c2802442441220000310500030b000007001d041c150021407107109072040107202c0031804020f00083c3d00540000500c0d221003400b0a1103d41001c3c8030302d4410a00914100341700701d40d2804c1c000e0a0a00545090940e40000002c00000d5a01000101412031604451000540200e0024905003085000b8403041016542c086406060510b016201131900902500e90b0b071410702e041403d001256400c0d03c00c244100c144205203000c0540240e885460300848801085d4486600b0805250302000c4408601d41b024000482c52030805c12010a00e40c0303e80c0c41e60010701600d660064900307070f44158103510070f80c1460300203a0103450106000c0d0708040c880550040c01070b403038400641540076000c00b09203910f10b04000090103192510310280902c1c616102c0140550b030b480c0500c440400f9401c01c0e900445c05c03050140c044644100240d0440401c401001410324204800e070907aa0300803a441030340062 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 359388767 1250 359387517 359387533
    0x41b0308070c060206010f0e0a0f0e1b090a0b0907260405010b03061f051203070501050c120a1406010807031b02030a171302240a0309050c0d050c04020a0e0306040302 73
    0x4e40401c1907501400400608a8550740f6059041150f010000c1c04251026103c2200c0d0568840c9500040c040f0350a0105403401d06419501500c044401c0c041807030710407a141070200b0f1120511b07114290000b07001074202c1d000c0340d491140558050800a000107201c4022660100e105000e03400d900d801540300e6000070032040c10750b108040c54900c01a06040c030456229006554081e0080598001c9072010f80d4408034404450044074214003070810068829400d00040100b060040c0008060184040844d001d403902c0f003101d020112100741100c04c541010741c0011038001d60168422641c0902c03a460081112120034400070b8505841c1e0401902580c0080307031070038940d5040511080d445040041705041890b01e810042100c81000002a00683c041442c91a51261035121918910b1448600c190b40d095010402401403d6030300c001c0d180c50080303100c2144c007031408106825480d0307042802803241344150003c01c00290b0258000200b40800e01c5e0b030b0a900c0761800d0000c1e910541c02500500102 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 359390017 1250 359388767 359388779
    0x9091302040b090906150303040509040614071b0f080910050405040e060f0103020904050a05012f09152d03040203010c0c08041e050904230d08041b0308070c 69
    0x99821440b09510459901c0c04001c80f00c580000c59940c0301400e00400800e0364410004241140704d19009907401140420400c401d200342504107041500052900e83c0031a40c90301130880b8408a2114045031301c03030441e0441004920103801d6a00c0581c0100826171034040081d0000b40030059054440d4081480824104102d10b0035205000c0c90081100192100380340403c0c5404204038140002272050088101244c01c3c4030042110a00c11035114000300400700f04041d0300001c18402004040742c0d40c001030a1850f050507c00184c40c0c3d0383c00084c003100c031f0951304481d0340503054100490301ca0300c82841b40c40440b0f00c865512803880d101c0700414409a640d05084c0185825205110442021f2141401e83e81000441010484045400180b45002d58004003070000500007a1540031950241490741400b0622040c80c15540800882c01303000d15550304e88030b041580702e0a61310100d401040713000d0001404140d246035000b880c582c1640d01540603079182c0d503440080740c110b5502954105440c84040c054 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 359391267 1250 359390017 359390021
    0x8071e080d0c1e0503041809050f070f090c02060f061210090218060102062e06170f0709090f06080a0c08011503020907032a052d04060804080909130204 67
    0x219080d030080c3d05030f55041640301c0b0740d0340344610b01c02d14a1460011202c50003407585a8000c41e010b03a80041aa6440f11900f0403007030b035801d01c6000d6442c2d4044143c40000d8021400e1060382e49802564010740200d0b41c1d07240d030100340c0300001001240c1103106030070311140003c024401541c802240d228006000c1089005000b640d2080007015001025404140030050382c002038a50741c81038a96503155085090b400310703040c00c1003200c140803c201800080120b9040d4010781544034a1103031098080032680e41d003459405600050307c014003c14a00b2205009880311781e004411515009480842d92703582d07c81c0305907c2c00c0c40b020415501061100700910140000780a02c000742c1c0c2c5a038504542c7c550450f00002d0111102404520506644e1404c000100d65001700c90303002804511030501011400c0c090290140e4420402c405038046030341740c4484d002c0000040f00c095040404651410300b4208a825220b146002d401079400180078060704103103540c1c0302042403003110503034155075441004d407061000b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 359392517 1250 359391267 359391293
    0x120c120306140a030302060415090218160201090b0114150c0307121d0607021809010b0f0409050c060f04080d050417193804120908071e080d0c 63
    0x2201d2441d294041000c00d1b40040e80940054022802d182c000c1d50103409180200401c010003034000c2c3c001109a000c0381d1840c51081e00c42c07080c91100f00c0041040b168224203da80e0008010280002c4000602ca4143d0640008040b541c0c0079040351031440c00e01d4690107058003d000502d130307140e000007451810040c5000e0800b0710410141001024042c2903001da4103070200d05600c0601424012400303405640d615010012001070440d0007122508081403400e02030508010054020406508845114200b42c8941d51001d074102c0041c200a01480c020000700b41d01c00210182c5003441804042072910091014005400786074a032a07554031b01d000c200c00030081603051f00c5070484d00040c1060303c004042c0796081000d11392041503103a510b0000030f040044907102840d51501403100741c1c03d414400c0d00002109000758013540814070580d0f400441280d805849018003a1940c001110810802d441054140000f1032500d0403464440d4540038000d02d40320014134440700060004000c3c2060100e4040e40f00c2c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 359393767 1250 359392517 359392519
    0x31b05060a020601090c09030b0708010e090c03060a020c07031709010909020415110f011a041a0d081614060711012c0a0602070f060e01020313120c12030614 69
    0x1400c015000c0c0c0082d440c3c0d40b052041c41d410b25207925104444a206900050243d6448908501c0504040c440149408800d02668812040b090041291004001224601002c0080c0105002e5946802c0c5038044d41015110b03805501c1841307004000900c403642401d180aa03500b80080c1c46a0002000504076a000d81c40b0000962040000f44400070541d41c44550744201030400311908440c1c04041c80c0b4140190040780107a51801950000545101c0d818071b2050000321001e0000070748104944104240c152101c590211440030650f0004201030041c01204401d40c4000340f085100751a220f000d0400c034459100315400120401c00c0d440c0e0480001300f440111035000700054850317070300540c0322036007146009540101072109402301d2050801100320310a51005c3c05648442c0c20b40b800400300103096000316030b41c0b070602c0341703007840c4010500c2624420740b6400e0641d00708180caa01d45108040c07200e8185000c1041500f4210b002c6400880685a0020136540024400e403910020f00722903401c00c1052 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 359395017 1250 359393767 359393779
    0x11041104080307060c1b021c080d020406031d280c06050d15180905121917100504090203101103010914090d08070c050d0305010e0a1404060b03030d0501031b05 70
    0x2004555030421301c6c020f42d0342c1510b03808091190f01d1140126a0030310980205802c000140d074150040302074029008075421030700d0030710569100c040203901e05c0740406400d0710b00d940222041c1040207154000c84010504103890700f100c10b10b540c2c1314680460b00d079400c850003050001802c10554a40d600c030381030146008103546030544d07041c0340c10003041c581d903004141006070302c80d6410003d0000500c080e4404e40c8028010356a42e19040c07071100d00c90541b094107040800c190302c84a46408900912807403050551281d500000d40c00c00b410030004010a02c001d03038040c401d218040764150305520400c10550030800400c1c0c0c4a600d0034000800360b0750910301190950401d001400400c4100060522403c41c003810214500e0f03480040489410903c8180070b011489400144410780f50141d00c118140c1e01003a00c4000e040d03644d1081141601d02c14141c50407590b10180000300407440c00d82c4008c3c0309a0000f02501d20b0803007018142c0042c0d40c2c5c01c2c3c1090710036000010554000908010450004150035190 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 359396267 1250 359395017 359395037
    0x15051b04030605101d0406021b0118060e070602030307180e0703090c09090506060909121b0c091603200c0c10080402030703120203040e040b090111090a0311041104080307060c 77
    0x9040b100070007820041c01c7da500451100a14414000340c66414070a4100805c018500034a00d0781440034000000d950013407400b0508000c0e044085030103015031329150015441c0d901d402c682100d8074201c00e08000c402c51103100d4007040340001c0d058598002c51107543c01060304102c07030810306202100b5030b1101359818508414840021000300c1c3c00e0794400000c031100ca0855503042140e500700203055100521035400050240305413200090120703503c100410850b95401c11440a00c0446e080036214a012080541c2d0300118451207a0002041c007a00340d07907038860038488400d098096410918640310306420049140d8914101020455243d80700c500e45402c5900b41500403945410041c00003900043d80780ca900901c1034020011107006080410107058189030a007408002d031681958407003da5400c0906200340c2c10310b00800c0d107100a5005010040c014556030f2205002c1e4903444059030400d4850952084010088000d040144180d00142d50b41e502e462512804581c84004c1007020705c100049 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 359397517 1250 359396267 359396309
    0x905160f0e0f09040501060503251d0c0a090e01091413080306060307050f0a0504030b070207050307061808010f0b0a0618030210050904090c051c15051b0403060510 72
    0x1a2002c0d81500343c0d00030081d503d85041813809040c3e103402241e014810034100d103048004d5000c80c030f609098803515105040384c560184009080b0300345201c0152041c414046036130300343c400d001421124000d00b064904a5034803840050203640c00d922031403e2950700c802c024034088400e0800b80c1e00c5a264000300702c00070b0290b59140850300014103410701884000c0001019203018404407003455001d80b00d00c1ea2602c0ca0000c008089a10500040f43d80c00c85140c0030400240c00001d20005440d4000c025150050030004200d61400c0c8214220740c0c010304411001601d00c0302881810000ca03004440440d00d07001c0740c1e060004c104a29401581008440d0b1106da500200c00002c80040c1c90741200d2210307500c903c02e06c1c220740501501280035402841d00c0001000c01c04543c07503900031118103455400c50381c10300354946428a0907900307001d000d01e8084100720600c0c50071a80304a40c00b440083c6040c402c1b44281341c0c8400d02e60415081150055952014411047c0d40c582140008158a2540c4c0140c4001c45c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 359398767 1250 359397517 359397529
    0x1140c132405070311070e061005070b0a0f09020607080c0c03030a090b030a022a0607020307081204022e030b0604060203090d0201030209130221061c0204060905160f0e 74
    0x200c0c00d010800049542403c0501c2881c2e03044405c500f140844080365119140302001403402d440d0761384101c08403903c140c40d080c02002540c0485030414080d5885136105c080c01406029118445140f01e41e407488450011303551364003c0d1681d45e000d80d0306680c4035200c42c5402c500d032502c2000000c0c4070ba4028000b000c00755508c40c0604007540c1d46000303150344075219000c00c4e4003e406414100700503ca950640d601303440340c0e94400a1303c010412401c0b01c01948171040f00b03036240d1140e0756002e40403d00c104031003c4404070840440390000e01c0075090701d0718a50701a00308240f1540001241c440031040700c4806000741c2d0315000350030101904030b9180d03150919040c80030b982c903c240182203018401001064003503a00940c1a075500314000780406103a070441c040ca240c003d50145a4010034450381425019201101d03000c003e21510010f4800e0309401e040302120700c0001000d0300304a81c000e0322050b002c81e000d00d0f2030007250b00030b1503080781c0721642c3d0340303010b201410000803094040200031908410440503a100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 359400017 1250 359398767 359398829
    0x150a0b030111031f0b0d020a0207050a0b040e060303162f01090303121116031223091009030903210806041805060c040f0e010b0706020a0201140c13 65
    0x110105080e596034922601c4d1100c602c2c4e000c00d140d11800b080c61082c0002d1500100400200b5500f9a050261030f901040b40392078050003640c00c072520030300007880720100f1007248980107a1700070b048038188015441103445512100104440d90395005030300480c446012400da02c09622903928210a40310202c0008001600d9480054100084012044810925507010b00308004480c80599690305d1040e600c01c07454000100102c0006104500f150a40c5645109446400b40010b268030b036600c902c80ba5944900301c0c0900000450b0080e1180d881c0e100d0428407031005828400c5d1101aa5103155080146d10040c2e8a2440070f9404404d02e42e901c042d03544084a26032082e401c45001800d84550b8951070300003014000c4c0206076220340404e211a000c0d0300b60103401142c1f0b900120f543c1c22603c411884d82c00040a100f40030007082e045c4110b00020f102c0e80c01411100c402c1384000107808109071202490307000103444001061200040c5603882038a0703801e22601038501210b00c0403e2401401c0f09100b00210 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 359401267 1250 359400017 359400031
    0x15020c030a03091415100b03100501030504170d091202010e060406050903070813080c060f0d0f020c060a1b0302040f030206030406020c06070203030a0b0108040b180f150a0b03011103 80
    0x5a0030303680b404c10503600da001200c020802e0440301442807500003003020314010b41d046105107104201c001074041005048034401d84004095448280c42d04e001503002d803134081c00480b01441c02c0e062603034001d40e409000c1d00800c12040b001140000c103030b04041e034145039144648011a41840300b00605150005603490b00598001c07000034255581e403800c00e0560040450045c00744500180c01481100541c0241007506d03800d0040d9207100f0700282c03c00c2018413820020046924082c043d155422049a0041c41e100e1084100980750102510016041101c201c031050007055070740c4000c220701030200500c1c40e003032091820b017141780c00d0800052504034800c0e0b120080c4603400000018040100d20f4040d200d1500b80380c8200d40d05c80c01d00c6000a0340300d0708100d441240081c6046d071070b050590310840d5a207005d07940054030325845e0b80741e401d44103d2055103265401c0d03542c0b14442d14125039060030411400701a508518402c2107040c03800c07000040c0d4160041c240d10907810400c0700f104c8900395404480c0c100603 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 359402517 1250 359401267 359401271
    0x19171320040b190801060b0a02060705030a090828030509070911090a0303091404090c0b0a0201150b1206040e19060e070f030201080901140106050a030b0301061215020c030a03 77
    0x111003030000e005002c1d48442250081d00304220740c0568080b003c194020740790101e00a000064440c5401c0303c42d40a241d6028006030f01032408503640c075020b14001d50300700040c1d0802044d042010303165803000d0341c44038641c04181e0403020007600c0114200c21208040180351b1a00348080d0030f11100710f582d680d81a0045030aa0b07595402140b01000c00001101ca403101c0141004002d56540d00340034000d644640700d00c109124140b08003404a182c680b00e8032a01c0c40d0700002c440d07002410401c5c901036a030024a03100c0c05642d80c9920344071042c80304080110003401294211640e840b500c0316084069507014000c1400380c1e050440d070384108030001c59034800d031140d540d007080320a2160b420b0101c09080c410307094000c1c40c09502404204901481c4288040d01e000380c8031150251560302e0018221030523014114089000440103002c1644200018011146140381c081025802c0c10000f90859085500c0300560f01800b09003c020440c85400c210680592480e04600307080300603c109441c0d21440c04d140f0304041d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 359403767 1250 359402517 359402573
    0x3110609010210062c040309060e01300f06030c03030311070c090f050f1512030f1c0b0a08070302040b131a0325030b0c191713 56
    0x191007000751945032000c40c0402e210003562406140d5403600491740d110b03500d607250380d0340e4a02400c00580729030055505640d020402460040300300d5803040f1813009035040088020018900e41d2200c1c0314120896101511a00d40c4c51407140745008950500680a0702181000b104001203212034600400300d9401d070a0216001021030303610601e91140000082a443d02414007048802d01c1da8010320745041400030422180c0c45001d42e800789108201d84514416851071384210301e90a065209542210003141240c5c14000d94019416207038014440303542000a131000e0610001203030740214140d1000603140306032110308020716151903101c5800041c0c019612a001300752551180040e1802004c506001005807203841011248503c6112603109c0c440d1088000080c0c3c0c00c20340f28020101d00c41070003402c401c21032865581c40c00810f0001c000d80d22444062101c1034456610084031059441940e84403a0b03104070440b071940e1081c0d8061300001c904070701040340c2000500c8a214400b95058820402c401394 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 359405017 1250 359403767 359403769
    0x12080601172410021b0a030b04021e040c03140c03090601090e0c1203180a060507030804050304051c03170f06010e0406090f0f050604090302120c0c150315030703110609 74
    0x18500b000c070300d034101c105018151201c0d030380443d070120000600b0001c0c415683d00e170400c00018940500020701110180004034005142400f41c0000181121503190100036002c00003070b044402d00b1741d101010a80303c515441c071500e0680c0041c0d5025003217220712811810600381150f03030742105000352003000e60382d0090742c2600101000803e0344000010104c00c9550b00100c0b9007501c1360420b204105c00c0322081d5601c2c404920b480d0001c007050360510f9480303c1c28224241c80413507002da00940190741034001044007040399110000d25481c1e0002441e000e0600121a10f0b00a00203801c1c02c0d092440c40f40711701c09005112420803170b5540c0007102440e12000e0380240800180041031540d208100107454004003502d40c403841c2e0010031140d0ba034641c040009582c0c42080c13006403901a400103006801031403450020b41081c80c050020030704850200c0e5960a0004046040b180111100310700110340803040140903412586501c0e150304e801e03130162211038078581c2e9035101c1031100d0082510650001c1644021 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 359406267 1250 359405017 359405071
    0x109150e040503042310030c080703020f0712030c140405031c02011506030c030b030309090c160c03080324030607080a021201031a0106051e0901030e06041208060117 73
    0x1e01704041025015154890089030f014503424040c6000d1498140783d055083c1c000d21500030500b42584480340556543c00c42280207621070008001448000e102c0400410f03d49444031903d11100d40300012107010001001d06046e81d031007560030045c601004140019207001c6500010064408078801c00040100780584c09410041400082440d100400040c407d5050700403040d0034040c5c0c1c0b010401001181d0605482e880350460554000a001d0045070000c5855401051800c4100c400395140090660f15500100c90540c410b4500403004002d210005e0a1100c04007064003030b07405040ca10850310404241c81d254010710500c103105240c0c0c0010403040854040b9820b03101c0540da060750340c1d80c50f071030306001070050304150484507000c1d10000710301c031401207088032003090708584400c451340c115000c444c01591104910a04050329088940e88092082015601941c460350034104108082400201902002001e190400a410254500a02c004004150444042c035080210814010700b80e0030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 359407517 1250 359406267 359406269
    0x804050f0414070305040308070216050603041b0308070303050c040e040b06010e04140a0e010c050d0b0d06050a02030603060708060d0204050603070e0c0a0201110708040e072d080109150e04050304 86
    0x70401d0307800010803c0195060f8800c1c3d105900c641c0b19a11a030f10f400c03a089a951031310000c50403413440c2000c0b00740070b146403c03005180d20a01c100c800e0500c20450403400300c603840c0d40c3d501c222140c4a001c500b201c10103405000703140c2c2c882644000c4508203454440c0010f0725060251000c0d04290118020455070f074400c000030b0200c140054070500007a02e620341c200011030b008031145403406203001004036054006009a4003444060ba403418182101690504024498581410343c06648015000002401030240d140f00d0b0100b18001604d80c5442410305090040080188082000f140100282e5580f404940420181c05072400a459550800400c0c0303040565005040c100901c0400c01285507000b1004044005503940240041554059083c4460140c03000040000b0070500040c090040c45d892159401300b25842c013400309450501001c105098101e030016242c81c900d0b020203168a070072664540c0103110403081000640031700c1d2000c01c003262003406180407412070600850b00b400b034100309030b030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 359408767 1250 359407517 359407541
    0x8060d0609020a12110f0904030f02100c0906180503071e050d060c180e01030b0a14100906060806150906040e07020d0807020a05071a040305071d06060301030804050f04 74
    0x6405603131100302d1982c1c1a010000102d4024844036032503030300c505200d0136010401e038020b44070508640740c0d40e9080d2564102140720804610034800b01c001c48118600138983c009010f40c55000c6070752700f0710740010a020328034240d00c940018102e03030030080c603140020b61204035900c111650462015030542508a0340055102c16801080010360307509128581d030024640d503007281c41d480c0c01010041501d4504666500c51000150121401080420901d0300d800e9444654248002158820349000c0c1725405000c0e10758203100000f100051007100340380d02c03a0030003401030760a090600d45000d030000b4000c0540c14500b00d0110101040c0145071392508019107002d490081103644483c540341900944c1c40104403110000501c0c1040401c5800b030020800416154000015110342800d00d0481e80500d0b5060403103c20044041000001085042c0440c402808461400340c0c1c1600c581507029000110280c030700d83c8240d10810040000520324130446084600682c0c620b01040400c90024004042100d802 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 359410017 1250 359408767 359408779
    0x170906130b120f04030206061306120507081e070b0703050c070e09150702030a08091609020c060a0b030325061b0906030203070e0d1119060e01020c0108060d060902 72
    0x10540da00804081d116001c2c1c4490381c190196596040414540402d40f0041e000da008807000c1161800c04040d1001030b0900c6050100c2d4155481c04d5490390b0030704d00e00083e61580c100d41310600140782c00f0701030101c984243d0310f50031552205c001a12500c40e005440780181a40d07002810a08142c003403010ba80001c0d41d16400d81d01d82581d82c21105010100456054580c1d00070541a10349074841c1414260040401e60b00450500c03070159000d9034080320240506109100b03400c0410000004400c220740036101c42039000d138440f018a00218a041806411084c940b0700f0802161800e440000c180c1308414040d401403449046007010796990f02e10b1505000c1c10981c10a000012021400000e81040175643d80e280d401c400d0303803598218204d010556441000413001c18800c4018648000c091541a0141010f000b000c00c01c1c20000c1c24000302044000344204019904024840d080745c48008615801c0c00602048036440b00000d00345007000f071206101e41103508184041c0499580400e000a5001d801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 359411267 1250 359410017 359410019
    0x42c0106081e07080703030c06020d06180b0102070f0e040b0403110102071208060d0209060415080a0c03050d021516020c04151509030203070e0615040f17010917090613 74
    0x1240740c50100d002d02c400351090140005100341e00060510840350555100d907459003882d601d29005c0d40c00050044049502d0b800301280180e0701c0d000c0c181041c030010b08006030406800002a00f00090b5901041c1c1e20407180b5401c01000b600784910903409540428000076035034441c0740c1560201e1811608100641c400300301c06040000390840c1000e00c044a4641c210580d5071078081182c1c5c12201603000350080c0890010406038182a0403841c2540240e5503404101da4441180324500503c801081c0d070303442d24460b010800d000c0c1c1400761480a0010b8400303007400074860440168a1030700509050644420341501462a510a00102c510b060b002007040c0445140b0070710308070702200365009000300d04800c3e4582d1300986000c2c00302d00080783d502030040c10b5024940601c078011100700810a40d08222a42684109000880010000340c01c100c5c105041880c10052064500c140d4007510103016131400d1641400304a541d03400d55000303a04850300076a603c1d40103002c20124020760341c01c1d006039258148 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 359412517 1250 359411267 359411293
    0xf060f020a230d0c0c1a10081f15120f02040608060f040f111003050a0609091a06010309080d02120601030e0a0f0203071502030c0c01021c0f1b0b06040506042c010608 73
    0x84c1640a00e5020702c1f842a020b45540c40039890f55035050a004070155000c0c002200381400342c00828046074004101494181d80e00c02e030240f00c60400744112150310900300003500310f11b4a0320882c0060140c59005000b01d20f481310304200101c0001e0000340c10703541000e5841c010082c8882c04e036050302ca40a040f5025800440710080c02400d01582d0101e079079410b12002040c08542441603510003500002100307070020b0020101c12516801900f40c074109520b5224400c0400c54050040600402c0b5410041c0c0d075010b820581070b041900500500e0406003812403407800450300180d1629081d0f005030403c1c5a400803440007a1614840d90701c400700e6542440c0400d40003e40202c058007010303240701c0a88150260801c01280c640b49200c090105000c4000841000b0324442d8010042080d41824840301c030552190317014a01c02000031044401001c0f000c204050740c1803500509400413010394060007000c928180d03210945484000c9220458014240c05100c0042500444018a0b15030700356030084598107 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 359413767 1250 359412517 359412563
    0xa140f072907030807020105070e03340303050c060714030103021e0909031e07080316090f090b0102010c080f0c071505070c021023070f060f020a230d0c0c 68
    0x5c1e00300015500e080c0000e03022034060743c0c5d4136156040041c0039120b88212449460700140240082e0f22011a17400c1f0b450b0307005510030f690710010b0350003034031541d132992201501c803441c1a00043c15a0204a1050901e400654401d0305980c113682d41103589000c40600400790550b002c42c19400194800880320038044400000700c0184010303100903000740a80e062441c9080c20754800d81c1c1004000e0b06040001405003182c5202102c078641c0e4030310b05042020340d5401032105106494100d245c00b50f0f901c107103e0550350780900c5028070003c00c40c108a50360b403a21480713592041000030449201c19800140c00400c0200e070300280010551682ca081000341040031004006281c10003080340140c60203084001e9550154a600c2c01d8074410784c6142e00380f02c0406c03507000c0080d00800000c6503207055048203c000201d003401541042e28441c00010703200d40508000400c0358908032341c01820a043e60a641041c0c901180850b11411501c1c90040360400fa164003c50320061103160103421142030850707802c004a686 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 359415017 1250 359413767 359413771
    0x20f070314210a18031502030703050f040c06180f0e0a050c073c0506060114070314030601090503070909060b090708071404170a140f0729070308 64
    0x41045442d1894488112000c100031410000e00000040c060105028440c031000c0b5000d011045508186541d81d54604142a4110a404046507004010800003a40c188500c99101000814070b0005007019143c0301c1002c2c141c0c5c080e4404100381184464070240c0c0b0310010742d00400420440ba034505685031400510104180d607101115800d101c0410016400780041c1c031020307a0440080d00c4070b00c3d026000518410028001c0ea4210050010265a82641d16043d02c038854019806440240350242c001040402091041c01800c03030148020030209600100c444000b03549169051f03541c0e10703401d0060360311110340d510807507162141c900701042042c000e0700302c4400a4425401402024078071070401200b46000c0700d2020006810340c0008400c241f1038290044081520042c1d1442c00352a58a02840416000c40c00880d560096400008021018600b0200000054054500303200601000703074540049228804000d88012003040c0e82c220b4074440080613621606006617611601d1a000d001c071141 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 359416267 1250 359415017 359415053
    0x70309031103010b15030a0f0219080702120f0d060b0705070e01060815060913020c0a171306110309030312040b0f0c0901050d2c0f0705150a020f0703 66
    0x41c40d0040034941c01c2c1405502903e80d0014000c10200100c000c501e145038000826040100b03031284034106000b0076034030042124070b00301914400c0d03140814034050003c00c80904140115400080255451500c020a07115031a0600c03045039030740c1450038422801340c01c0c1c98200c8440c03010009610f1040100c00030f01401119400342d0118038581c0d85800a48003000c08031040003a200b000c0a092502d4501480142500c031320080005d405043d20302c40040480e0841000d0320203035030020b08900140f000da0000002444070412a4070b10304440007140c255441d103d0b00c6908280b100c401200b160300c400900036030320340383e10240c1181c0d120040031541130741d191010b84003074030040c601c1c1c00861424140195418803607401c01050915080380329004540c0c95103e5800100000da50724008103450102280c1c2512501c002148026400322158089003480e01e015640380c0e46a0042c0400c000544686074081c0040c12210402900c03041d55038000ea042c0f01100404c00078034020240040100700070a2050400148 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 359417517 1250 359416267 359416283
    0x70c170d1b030912020d170c070801110a0f0507121d03011416090b030a0b090f01080a0b060406090e011b020705013e03120a09081e090607030903 64
    0xc030381c0c100603075100c418078405400100c40710414089003040e810380400003407018100300d0542d407803601c4030000544030a6250480410002c0e5907000b620041100c1c6000c1c029000081191004104c038030301d503900ca154622000d101a500d01000d9040c0240c1c15a11200e070030014800341c0190001b402041c204984e080310064445040c0300084508051080e00c00241c5501d00d100002d8031000841c016000c0542040c50402040100101d202c5011230b002e1409070b21036650100d0001070b080c08001425030003c208095245021004001181c40001d40c00e10b4103411606c3c410240e1186004100039040340d401011086042035001c6441030815482180c040320010b4a400742400b0707100040740c490016100780c500240e4a011024484007042c031110f070800e503044114050504103840701003608048000880310541022070041010f1010403011036200c101c06030204002c08090395050a01e0040c1c1005a01480304c520f00b03800c55011410480320700c00401407110b52528040d2500404072800d03408100da401c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 359418767 1250 359417517 359417537
    0x21e01020105070e030307030806031c020a02030105060409080304060e01090804030b0f0f01060207171005070801030b090303061e012007050a090b01050306130b190314060f060105070c170d 83
    0x5407180c41d8103004c0800040c003940c0380a00d46d4908a4888030054003150f451f0140b110501c000f038000003080d41100d002034003c1c2c82844a240105402c68600905050041c0c0c10456801d000800400850342e206500250000300042400e0000c1d005007540c5400414085000402205021650800f10711503208050100f50a5440d404606aa64001c1c81303100c0159011004c1881060315a11000e81d40300307142c1c1d040b503843d24904c07108841607850546801000c1013100c0010700512144407152a4007030380030001035107903041c220089039240c54015260b9005030f0010100d04410381c07207402c0d0445c1c000410035a1002d4803c1a40074076440d0030703a40c401d592149012100006102c1341034000c041c0c400c0d00585865085a9880061114041c40100c0c0b44640680e80c0040e482d40ba41c40c40c40c040c46a0130104c801005482c110b1900401e6404641003413440d5a20032010000c2144082c0302403a0711410a01e8082e441d401a49401d0490143d2500700865200341e808031846000d000140c1d01014441c2581c07148190 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 359420017 1250 359418767 359418781
    0x807030b040f050f09012a051303110a1508060d0f0203121801020106080d080c12090c1c120e03030708030f070e0d030912031202030901060303090501090506090418021e01020105 78
    0xe8007000c0380c1000c03154187c0300c0c5607280740f0030030410000c0c1c48070b604000d440c8c82c4002c000c4074a8403029800480d65140340650030341032030a040410002400c480007150300c004040840180c400c000c000d000911a07080140c0403c10010201d034959001036004c0c085900300783d800d6400f038129400004020800c442200703071a441e550700c140100422640d030f65010380403411100c8021910088010250a0141010804c0c42d07002c0300c1c4410742030f120300c124074007801c1c800c51002d00b0400304050706c0050b5820300d440f00341030f040400d00000c0441248032040c1400810758001c0d0300400e0446c059644040c19500001c4200458802d20500d120302c0380c0c04a0340c0390341e500c030450300400011001003c0083c0002d10038500520882528031441c01d40940a0b0502002d44001d2401c004241d07442201d0080300c0380d46a46d400c20806030004180400390000342000d00c14503003003030b002c9086130107480d051520071910381290140d680c0d426404003c42c681c01a210840c10100c11072581000c0c04032034804c50041d0710b88070010b920 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 359421267 1250 359420017 359420021
    0xe010506061c0c051201060c050d1e03050406060f06050301170d051b070e0915010e280908030f01140609060a030504050c090a0608150402100807030b040f050f0901 72
    0x14905480c0b0140711004408801d1400074490030500d102403142c208049000900c2241c201c900802003a0b403107003034158161030401c0c00c10408000300c8050212669445011941c144400160400186000540c0756a03d040441c090500e42d4404545040086008100d1560000c003c41c142c82004c003802111000448410b903030703902240c010b407000a00c1030044001d5038151b0142c0e1008002000304980f40503071a40f026040e64502929040141d5010410031400c1700e540901a42c010907010340060360300d161840750700c0020f60101801c11f80010400040c210034015513842080c05030b80180c03120303459103080c08003110500c000f80940191304ea0a00034100c2c2c60302e00201264845100a8249400d1820a010607805090041c10440781c074019420050300d2a1101d0082c1c503c11001d001340820060700e440c5c981814108085c0078900e420307034810200320140e01d6145560040b90300c0307840e00341e400d561042001c41c001c14120521551007400c0c5030080b480b0081035080603000d40c103c80010a85a100d1440d0b40742 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 359422517 1250 359421267 359421277
    0x17090405100b041e090c030b040509010c140904060351090f050a1211060402030a081b0a1a160909020307030f050a0203090601080d0c150b0d060e01050606 68
    0x241201c010002404590000c5811180140d45203c030000d10035201d03145e4005886120100d100007d40e90105100180f40c6409030300e070000c03c04402000b0030081a00024100b40308030110591954000801c90b24a8645502000c010b540024819404074080342203c40d00500c0c0d020802402d03000722300300080400c0406141640c000348415024481d5128803503502c050300740803a007516003641c601c0044000c02c03000d1201252480c80b0315054120404070a50280a1000501412080350312000c10000182c6000503005801c1380c12030176007a106c05401152001f01c00c0c40c1c0b84944028050410240c0c1008451090506148250008180340380e0310700441d00001d80c210320603003000881c40ca034100500740c5181e0007190040d005260128201040c20710f4082521400d0343c084040940c00820032403030080c28824a409007810b8409017092828100c8010218080d41902410310804d1404000d59140503030302c10034881e140940040f40400d91410124010a02604608440d50800c40099011f150040c01c8907 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 359423767 1250 359422517 359422529
    0x5090906010e0f060a050301020c101a01050d020d06030c12031d0102212b11031b090d020a18060602010204060c0f15021207141903181709040510 64
    0x46041e0f4070b01020700c6200303002400d01c9802290281c8003107510740b402c2c00100000004000201034860140508004581d8540141400030000c2e01c1a01c03860307070744082115512125640701584498207841844028503c40d4070041c802219100c0005204155287c1046814000c0d2281c042410009400b60650110007a43e02d0058200703104030134101101111040424490318401802c00b500807a40050003903417111041e4041091040da20405115801913035011420340d600603040d4202084102040103941c0c41c002a03009021034015481d449140c02d1001151700203011141003560b40451400c0c0048180c2181d04075400c21601040c07660050007101c00b224500d540d0018200c0d180c0c0c480e16030707904040d003003103031404442180c3c5119480c3c5400034014821501c500e0f480981440400506641100d0700a900341c1c48003408800c1e889180d1090300c081e002824180411038048110802a289403941c4005220890303190507410483c2c2c4140c09040700503400d941c104000d880b10000c06038042400e1280d9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 359425017 1250 359423767 359423789
    0xe07141204080a140d0e1009030215040f02030d0e01230301060c0503091002150709030314030903190504050a17101d01060806040c171c120501030501060509090601 72
    0x4200060390200082c0748488003403400318010b036100003501000c1d45c026010401881d0b1100d0760030240074020320070b2840d00321044800300f00c001d1560380e000c3d44801e03062241c40044d11882d0001000e211000030401c3c02c1035802015a0000c008149024002105c8440c03110b0015413149078850132003005040440b10400c1b400c03055030440c0c0c07a000c0708451408402c2401c6a69000038401c1c001c96442c4c6407901c45150310702d07070003505032003c030f8814003940c84c03100601c1201004520710701000400c2c1c000d0400d8004481c8070841b035980e0b940300c001540c074601c6200d0600342513403000724140c407076568400060401e8510848505040700e40d2801d202d9040e0720200c1c400f0049410540c60303102000300e03a5128102d00604000300707000b6004c035155007600315107255000d2406e50300f1041c100410401c01d186010080c0c4400c090782e00130392080300301d071558924001401d000e0402c22404081c600c5030003225000c1006251101c140032540c0c4a03d007950107800c1c24460f6501070940d06011500c00d40000c10003c1c1681d0041080f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 359426267 1250 359425017 359425021
    0x510140f0f0402102703030f0203040b0f0f0403080d150b120a090c050d06050708011203021f0b04110c120306060a1413150206060a060e13020c070e071412 68
    0x2c1040344082d465490040c0007004140358500c903d0300390350724214901042501c05d103d14504002d08070030014102c8800315082000300340281001001540c01c0c078117406903025141c00e0b4004229126100750b400180c00b001020620070411326071034200c0b2540c0e1003c5034954195556540d102c1d10603005004031504580c241e04009800c1c0d407400d51103910514000e081181090707594034003240040030440d000380c418545600400c000d554009030014010001c0000e0102a1000340d103000b9101d0388035003c80b6001e48054000b103c00005241c1280d054842d00a100300320340850501c0c054995840b1010000e0070740281c0a02c803903400c07880c40641380702e40f2002d4101490050f6804049800d034810711100300e5625802e200c1019001452140c0340090303c0100e01040c1410540b5001a03d0100000d02c003511502d0144400c2c0101540100005e1a1200550b110281c0c100c47c10030f408041e00920070030050a10a08400040301d25850103c0c43c0626210b444440340450300b116400f20301e103d00340070940d4160705540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 359427517 1250 359426267 359426269
    0x111305010302031b0a12180b04021e040c0c05011b090b0703090b0304082a1e010b1906090e0903070201110307140606010e0607050606040207020109030510140f0f0402 73
    0x1c0d41d0100c07414003181c0e40001c03d40c10454040d085145c0c0c010005120f02501c04040178503225050403c69150025441c0f6217450f5604101c01c100140003d010300310030300680800030740010041c1103400c0020300c1445100041d00000707240d5000d2030800c2d6807540c20030420905502d01e03102011842d0030342c2d41c0d502c1201410850209402e60201c01c0403010000518000110589800b02860199100e018000d5072070a0741d00313115002c000410f40c03008034003020141c43c65003044000341c03400c900d0554a003694210824405240d004281c0c0002c9550000c00b0410400501503001c152001510080e859800140b601d480303000710b01201c04c59041025a100708154405580030703c640503074141d4490700303c3e4604145942e91650082c1c21015920850b40801c007400b40943e049611702420300f000780c030303120304180280d2034681d60798801826642c0901d40c00100c61080d03900c501c03e50340155801c44129100e42c1c0caa00b40b010010580c6400d651440c64800010400d20030001c00c986015480c850710320802500da6070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 359428767 1250 359427517 359427521
    0x11151618091d030301091d06150f2b300c0c030218090c011b02091003200405010f060806010f1206030c0323060103080a030212130203011113050103 65
    0xd15002e1240b15001c8030180b020b8002c00045001c0e102a01004c9417024501c50100040c4400d0030200c82d181e04000108030320000c0c20840005200d4085814031303080c400070400b0a403800030f40c03080701c07800e100d12080340c0150f410007580400c842c6214030b440c0b409162102c0c04201001c6641130013208440d44100400760342c81d1047d180c0c00d20140c05480c04400441d07a0b940056140c0d40004070190f90800e4030410080c25690034001d01d044c200e001e08083d0401c003410706c40c80340104058100284100d2200001c10354080d4110304050196901c034200c6402c00038441004100c1900012803180701d80d08010000c50600d1080300f4038411100360341c4130000707a1b45401d0015a48840543c10700800c02c004d80e03600c0d0f09810200d0144038015400391495140f11800d500300440225594140c10368060040340100c94032820002c1d10b2811280c10407040c41c1c032003c960500318040e115160b2420510411002440042c80c8481c42d14040b051003140200b001c101581e018100c24003d10f00c189030003103006841003001d5402a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 359430017 1250 359428767 359428781
    0x50405070306021e041e150c230d0809060105010e10050306011413080601140a030323030a05090c040c020c01110f0a0809120303040809010e011115161809 68
    0x401200303c446036513080036801c0d0440e41c046604a403805412460180a5403085406050300980754040d5084041020300203000714803005104003000420106440301c1d1600c2c8030440000c007015684840d40065005251010a503201111030080d0400062598081c80000ca1440700181041107006000782003600c5a400c013b18180c14041c0c0300f1402c400f46a1820020f120701c0032100c1403480c03214208581769203003290507000f1000105000c04040d034141d540e00342c03420482e07625140c0040c02406010502c1c600208100d0040002c03240030003840499512070700030511171003170a0300b2600c1c506540340400c0151101c0351075580250708061142c040f81d500c18a16140203040d440c04461130b0254030641686490300442c000c0c3c0341c001004c070350204140750080c80510400d044c00c004600b10306054840040c144035031010a81444013140e0b0002d00e5134003031103030203628a202c007096580f140c0b180440e200c0008800c4034407042c00b455007134440030058007840220020104a405812046040c107614031700500c20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 359431267 1250 359430017 359430037
    0x50f040b06040e0703062003090309060903190803071e09051e1e0907090605040909020a0308120115030207030818010e0d020c010f03020702130504020402040f0902130905040507030602 81
    0x11551050443d1004001e5240154422400040c075581d0134036161a800c00c641c181180f110400b0002c0c0070a05000200b07903004011f045070130681d5075041b80b0000e0315190441001e0028a010800080240030244c00034520800c0246c48014000004c00308043c41c641c021540c0c4d0001c901400400e00060410405601c1091060421001500803082c0010040d04d4401180414034041103010050b5081c2000865040141410003158440c03d041015046010310301405a856a5440342e82c015907942685200c01550800c0c0c070299501880700b03841c8410507007405002070740a0f29428a40209229108031010780350190b407200300710b440c0c0008640c1c03a4045280030315119903c9140c40d90069005000320002c8024640041140c1e200110015019104a03100031050610505c000070150302c1c0c40020740d107410103d07400081c2a588910005000f400b5a40003031548510001022a5158235540240103c2d800c40703407003031219030f92003451500b80c590803940100540c003c110200002400c80d000340203910f00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 359432517 1250 359431267 359431271
    0x30c1c060f0f020c011a0f1f0c021003090c05240721020616031e05091c0507031103040609180f050c04090510050a0501050f1606050103020310050f040b0604 69
    0x1000782c0640c02030ba0000c0414130041d9543c3c5000c901c0c5039040d00a050701402060314604100303000040000d02a0704541310043d00c200403600c0c4008080e1080d10204003080d40205112800303ca0004000c00508080f00120fa510004c5040803405250205100d2854410f030a00030b5401c494141c0030482c1c5410402c41140d280074903680781c200f0010300c403500c0d01c5185241d41c000d1140c0e00c0c181101683c8049070358510000d0500d00703080b4104d400c601403a001e0024003101804240354584c0c4400ca440c1c0b08800c0d281a030584210103030104425400710060620714003035500d00304da60418007034081d220f1140303210303e00100b0f012031020800c1c1c070761228550002c0c00c8403c0300054805843e61220056071070448440036404000a018080070410303100e0b02e50031481080800300784900f018040351071200180101c505002001c9294403d40300c507201122020040c070026006404003501c1c080c2c014100a001c2284079002d942c4000d580b03070f81c443c0b040c0b500c140507c3c0f04186107611039856100c0c9680c80908800d404c02d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 359433767 1250 359432517 359432531
    0x51015050a0203120c0a080a090b0105100e030f160611030706051801090f031b1a0c1308100b150f18120f0c04090201081b04080d030209030c1c060f 65
    0x100030b6021070701c01c01d1700340130031691804170810040901e8030080030f03120b81e02d2a01080c0000b050100d6076030b50542d03005071a1b40c4404c41d24060141e4001c045c0c940703401d43c50320810082d0091040045801d25001203d04003030740c516030705d6060941e40005a590009890b80c02441a803020900310340019400c001c0705070b00e0301107146500c03603010f007940d50100083e18504d8001407c8000c041c0e0217015a1a40c1d04841d49840b0080c0242d40c40e07540608205d42e001c110300340c1d4003008c600c81b00404c40817101c4141550420881c0307950382d00c81c80b0780c440d0030000740d1446603454481e80d09540e003045490751a0b0001e40c6140145002104c840d05585030f00f01c0d43c100318100c1c01880040d082600d0f10003422121052038030040c000e81c2080b14803e032400484030005806030b42800242e0780181d801604494000300f050700c186c2c030b0012050220405900481d80700d0301d8203110740840f4140351a0964010401c02c1015010f98465100010900103500201b88800842c202d1940d030340c2e0f01180c1c0691100c00d10503000600400d1031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 359435017 1250 359433767 359433787
    0x703081804020c031b070e012301020c130603120c0317100b030405060f011728020a0e0f0a0c140a0e10200d020d0c03090302031f051015050a0203 64
    0x158205c5004e181c0041c905840b202c038081340800c81c4d13000070300101035a200c941d81003c004000c0c18010802c860b01034074030382c8101c0300560300901401c207004001400e24803e10441d5008007025012603c020361b02d50390080e40c1b1a481622440b03400301c0e00da8058452005516000342c5035820440010000e0310810600800400c449003648001c50096010300c0c01005c00b4204110f06c240c0044042c2e00008441080a41d0182c5100d0301180c001d250008907000200002d640481d00003040011050003580001e080c1d801284000485858500903c01076201402c1c903910310350303420100c40c0c11903007090200d070401d40914821a0070b14024080703103403a490301d986d0041aa801040c20b980c070003c00000400c04c210068a24004105000400c01450710020801102c4010010352544d60310342c0076030100001c0c88840805c0c50301620040e0001d65001e0301b103c0098400180302e00400300111070007800c03035042070301103080f081105a502c41074a10f503460140c40c014010f0403c0d1842c2d4401310603541075005c01d014001d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 359436267 1250 359435017 359435023
    0x2040501053f03180301050604150501031e0509030421050a02100507060618200a0e0d05070305011a030f0705060c0f0f070504050709060c0605190e15090703081804020c 74
    0x94400c0352001302141e03100820182928001480c45010b1440c106130204034604001c3c0d4402140c40c04e0030002800700d00c08842025021074644120b621a003084244504018000000c00c01c550044020010501d18008d10842460700c44c071001d84680d00c181c4d040005403400c41141407401d846810b05034a082001d80e2030009440e040d03070100442e03910003442034003604054001ca0385600e40c1c9100e12007030400920151801c60048448941c100240154103c00741c0c4c4030300304140f4116410034100c40c4050390768030b0654083d0280664801040142c80000e0503203060010303055010b103113050050116242408103005d541d410000d404400c5108100c0b0041504200740544256800ea01000d440c1c05820701041c0400c2d0f4602804981c104440369100300a6030b544440102c481c3c6920200c0402e15844580355040e00c030703003900012810103151945087c00038500040d8120340305000301806078581e6a50980544840803848085c04200b0100034861501e40b0120f070031a40301d213004000508040070901d03514a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 359437517 1250 359436267 359436277
    0x10050d09030806030601080a0302031803030c0604081804020f090d02040213060203071b060516030e0907050705070e0108030708090d080406091a1309181e02040501053f03 75
    0x104640c5003e1158500303003071000d0b6014120a2008000302c94455500940c0c91140c0511400b01100d19402094a40e400340210744004070150107c400c41d00302410a80865441080741011900c000582105103003894000d55420301840801d150800c4500300c14851a081c8043d401caa10950800400000a16800440c0b001d000c2035401552140541c0ca0b00c41500c8100041d4401d4224007031804110041e4417000303d50030048001403c00000d10245015114014212145039000340300324200006994003002801840b4042c0d8122901030307035240d0440041344c100307000e6101642c0041100c000400c20350b00041100c04006419048140b0103910340314281d42181d00880c0000b490b4075010040b8440101d1a20001041c981780c40346000d90f03021203a0941c0356988078054640d07858070741700c081c0042203507208114a5000f034081682c821000d07110002c500760b20b900880c4500d1410340085103d082c0708901e0300c5605100804182c095550494000c4020f16141c105d00f04808041005441041e0504c00340c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 359438767 1250 359437517 359437523
    0x40c18020901021b0906150c0303011401120504020f1903060e010b031608070303080a0b1009050a09140112150c020303060a050f09041209050303040f0603140c0910050d09 75
    0x58462003808002030a1200e004c45085010500744800107043d6108150341d500f200303045074181c0183e00c404114103840c0c02084881640c82c0004000011407980e54154050101340990707902c1100c04002d20843c0c1110015203000e908204140b0440d13001d818100d50030500b01039a0f248c6154090707030307964654054580c11081d5200e565122070b122500303401d00f0000c10030804503000b00021014101690a41c1e00c824921018082140d080d004c2003001107d0b5222603822040a04162610041e00360064600c0f032451081e01d006041000c00003e02c3c48680c4540104095580e40568150b4600840350103210310140c41a25240035a0808014981151140130303000300031500510f071649062010090a9052540024000d041c50110220142c0e00e80d50002d0340141c0c008400e80509022003403c81304140d654011580511001802103000e50116a51004864250790240484040b11449030243ea805079070b1014020380c1840020118a844918018030884070714295041c071000800010940f4424070040e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 359440017 1250 359438767 359438771
    0x60309070e060d0b0403080402010c1a04140304060c1502090a121208060f100315121b0320010507151a1906080c0c07030b01060f030b010c020603040c18 67
    0x80084905800700a0b030b100700c00b00c956501030000c0d07460341141943c0c0140300800704400e060008045a010710102414141c1040328000054140d01d80407201c200240c5e002d03191001c054140485008000003250709940381543d0700c102402c80d0f41c3d075000300701602c2c02c22120050780a100344060360306e42d003170000300500c00458508450440703403c1000705009001100405c005041c401c00186844459070185000c0040e5801e2081424440c41200203000e078078001c02c1850b80d803010000c0e6202004100401c604e02402c06c69036006500a00f0804509140c4801064259010b00032a001448001020080300060400f0be00e4081180c1d20206980d42441414078403956607020a02c4a8510710721b80391404100365101c100710102c1955000b65035000d8401c090400035600e000640703c60340d070029541841034607402c803600141c60745014180140d09000d100c000401c00171507400568031a020740a843c0d2810784401003420110340074000540d20080003500d180a401000040302c2c8040c848002245445103c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 359441267 1250 359440017 359440019
    0x305011506030c020309180411040606020c0f03210307021908210606040b0706020408030c070303020f07030c180b1201020904180b0601110f10060501080c12220206030907 75
    0x1d0304450004400720f04560040c88051400c0d03d030b8181104100003960301c1031407555100d113000c507810f50300c00d000349800c00e046c0702d0005074140c0c0000f070404901c0c5045840b4480010801c1c02c5c1a075804809141140451401102d081c11000b50001181c101c84540f050725224a114100c051981d00540d00c201d074411000141c00600e031046160034070b126540f2400c03182242c00c20500040d000d008500620010b0080020210204421941141c004160210980740c03070304c0842d2002e41d1291002d202c140d0140c025200e48403480e200219a0006899200341ca1008050030021058021031505c1401d4846070340d5820307440c4e45035903001e4504010800c400d0015a0b500c2d844805d000540d58030303064014003e52060120400283c980280b2540001301f0b1800452420b45003c0d09860582c6002400586000d00144120b02d18041c0c1c22640541c1c5003a01c5242d00c03603c5905503882d1501c02d4041182504c0c0080e0b01040800d0141400c600008480005000c81c1000580018035654003c0e1015440e541c80600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 359442517 1250 359441267 359441279
    0x504030f0f020607081801060906030c0503010501060c1205090103090b0412020d0306081c0512040b0103051504020609150903010e0601090e010c080412090905070c02030f03092803050115 82
    0x5800030203007070640b014084500303002d28060140440a0319008810b0a05041c0f24400c0009600c010010000300703078140184e585d079007045601c0050500443d4001c1d400c0c0300000c500c15003c0c5101c00d00d019406003107641610f01181701100c3c0e40e04140318140c10551507a4808020402c28003001d4010b6014050301c08036640c0014000c1d1412241c01508014035007048001c000c10603010036803410728104217010305030b6202c40c100100e690b4070034030f030a015840b500b078410310040c440c6c0803d030903053b0ba1003081152188081800002144101210000d48c006c4003005480a84e06120350002003a42c0b02030041400c0c98890b8000030709450010300c000c0803903072103a40100701214050051070010900c0500030007081c1c840720710040c11407400074809400d44100c024003000701440b80e6400d5009001c400c0f02001f42d800c05400080c501c0045450580c400d200e009450040c0707800101c12510250780c0200800c1020810081c4113410095004060750841c0030b840001012450a0144a52881c40c00d421f60f040315091035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 359443767 1250 359442517 359442527
    0x90c17070908030a11070803070309320613090203160201110a02150c0d0f0f0b0f0f0d0203010b0306010e01030309081c05030406091401021c150504050c04090504030f 73
    0x80c002420004080390401448601004403400c4903014500b200400101d00c071a60319061155101031800d00c00051450113266001d200c03101a40e1400c07055020004105142d403113000003500508076402205603035101985420801442403500c542c210480e1590f40b009000c0c100c1e08220b030004030b001c0021b203080413070f141c0c2840b501c0e0340301c130948001c0d606203921900000e40c0d640e1920502605108054045050141540103a6036005c5c0014400c1c003010b0b81e040300200242040342e4000381c0103418001e508115181848281079031100c05801042c07881c50420070041c80c0d0703070b0b205001c0c1d81556903240c0300e0b091030b1070501089000c0c0010b1403c0030903d525514000300310301c0496010070216004050400c580078151041407519100c18905075460703481e24207100c40109081c1d00700a11200341e25036862008401900a0241102c11941d011113100e4054030046c00d45034680b141070394503012000d041c0f11500c4d0541c02a500000003400e201c1c202500d4000080444200392015800310711202c0d8100382043c1d0003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 359445017 1250 359443767 359443771
    0x1200a050d1d0301180204180b04030c03090b031e0a06030606080a05330601050912061b180402130305030409050a0506120a02150c010f020d0c0c1218090c17 69
    0x40d002004903001c171000d80300c0394030840e40b0028840c07a280e4448041203038260080e1031490741c000100c1d09141c223152402404458080c0c404038041885d54030001060046d84094a11a1a403810541c403d184500342c1d40040e07500046c181030f011951900c010002c114688120006840107400412a10815081c0035242021900810500010b4050000c014800040480c0e281d03810300d10445a55880301d000588007405020505c0d0380014101142e0b0001c0c150001e041d0380030b400d54022000c00c04901103c4c0c1a00d51254180104035290100044c0841d03040c00d500030b201410b06600758010894480c1c0d5420f0865000e5480f41c84100e440c0c20501981c20360604c603984e0020320403241802840c070001030460300e0b200b41d03c2c00640301d9400000c0040301001400100d1301c1801100008112041505d820f24000390440560076002c50315042610700c6e940c1c0a0101c0f0711416422850400910804060031a148440340c8415840e1840710540050390000b1405070310745d0301000d5200e800c004c64001d10b603003040400c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 359446267 1250 359445017 359445019
    0xe011109042d09050a060c0302070b0f0106140906040308040602030a1407120f1701090606090e100b03040615120b1609090903091205060601110c01200a050d1d 70
    0x1a42d0444481c00030381c0d1500007914840c0700e00840e04000750304009003880020f07000500b01500707280d850706c0316503450790080009621602c20f03280c80f52501d40c001c41240d102401030340d004c2800511f14400711a0f8410140c01d5002006190500e003d85996814202d9000ba41c410300c0560b10206401401300d4200d4403021551500e10800340c24040941c40d583c1c00000781c034685006020000303d008800d244a060800e41400036184180070559480c01c45100802c0309214510008000b10004901c0110707951505028001c1d8183d007903c0c0d181005070702c600d5940301600440b1003c4e80c03a40c600d922000c6103c10750004208035421480c21040310b00b05450460300007030540304414ac11507115050941c00004200c00d841084200055140d02894151000c410f250020313200001c1d1084590b0030804000380481c4145401e98039240301384180b03290325680c1c0c03003602c140d1804218a00210840c0000c0f5890480d10496248102c0341031b0146a207405e410a2995071400300094102903003420140e80b048500840880 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 359447517 1250 359446267 359446301
    0x303051b09030d031820040b010203090d110d1b0f0b090108010b09060d060f15021b130f0e010606030b0f010e06072111012009090405010e01110904 65
    0xc0c1c420002034032084010501c8007495540c54890b02d40b030f245400d600b0070283d4000c1e0059183c0d1103600d85040078804207000c041c811030a01400c24501d504c08415a00d1402000d421a107035020309941d1341e48a00e282907070964104901201c91b81c040b03512074200c0007043d01c20095412a203401d180d00780c01d05103c0d0750081e1559a404000105269a00c001010f04450341001a5a00e070005440010b00c1d52207820304482c0c28070309150020036036031500e08000c0200d4481a5250181d950303c2501a03031103060b850304031607e07021b10602058ac01d080200451411410410001907400e41035211003048803030411300a64a80e54850090200341c0d058443c100f503001d01116560700d10200d5900007401c1b01841d200ba2400fa0700301044a008200c20740991810410842c14404242041160001e00c84910303103044003059820b001c2c5808141458030180c000c9405000d5009142c1a801010310045040140044500d5903a4030640d5010750303001c1c070904601450b5810b4040d541e51710070301044295801030080b074144c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 359448767 1250 359447517 359447527
    0x3110303070203101422150f02041403010b0d0203030d050c190c020a080f030412060603020a0e070306050402090906091306050112031707080402010c0503131d070206040506070e040b0d0303051b 85
    0x2e2502058480c0c4258020030301c0240c50141c7d10003102030507540d1001e0b0651400490042401c4000d41d0002080580c154000c0040018003010040a207201a5011790550020400700e045903c407031304103550184041c10583e24120600c1d0700864008189801540040c003011024011480d10765404001010b0460007440c070004100055a140d204902c00c1820700c6500b09104000c002080e00b08400658008040c0e100700c658079200050101c0c0110703100b100181c81c0800100301c1c2c0c5050300c02d80c0c00c003250123031140b40981d80310410310041c1c0d0009000605451003140c84075000407080c1c01000d01070a000b80104103040d1662401070111504e4500c0c05094030002800c211400d40d0158030250721580901e010214040e19082003070a40c03103200795407814441e0f1400f0116001024500800c00d07000005d071120f5807540d500700f040ba2140020340e03009225402020106110310302c5000d50021001c8001e2002459260b0354002a00017008103100300d000c26110400c00407401e0510000501d0b484501d80018544 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 359450017 1250 359448767 359448811
    0x40515040b092b1d031002090102070b12062b03050405040e0a050c0d0f080d02280806040542031c0804060b03390109031103030702031014 61
    0x200f06024110100b0a8507100c41d60719481040d045034442ca0054151004452001c1d03400e0040d60100f5142d5016209060340000c1070850b0304c088540242d299030b104030300b6448103000c0103084010344034a11204403401301ba1614509000d403281000324802c1c2c4907903a40f50724141c18041610001100d0543c160400c1b5031107008101c0118911803552411500803188000500e404060714800700801f400c2c004010405050f0f4901507802000c0f001c9011440301001d400200d2a03207001c0705000c24180024189101040060070f00e5001250042c2d07004c080c0101010101051070b107091806290703841400101c01d2b5824002202e038030103900300c0ba01a0f001c1d10f603806d03d6081d0b5200b00028414068100801440020180075440d801030480309002002d55260006070010800c4130354140f0704081d03403034200c46c0c0001406080d8002c0b542c000d080603120410444e10b151142001424021001905400104a44070041e50140301c00031107151007071400a0300406039a01240107950040c910f2030325003569034560400c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 359451267 1250 359450017 359450083
    0xa02060a230f0a0216060606020c0a03080912030415091406030106080403050901170403020a150b2107030b040b1006020109240b0613060311031e040515040b09 70
    0x102048440e111445030f11034580080080c4038010703000c1d0000141d01404c40c10040b02d50010301c1111004c0d401c490710151150108607840c001484001c09803242080301088030300b04012100e42c0106090192810300daa10317422079110003010703440c41e400518090401c0c4480b002e68641151003440a0350054290740c1049005080c07400c010340081e00340000400c085400fa88900c0048031440442c41840a0600b4545001307541d40d809c0101c12030702068080702240700101d0034411041c040c1001080306c0809040341110a40c000c95002c140c00e0b45010314139012001c43c401082141c0150310800d2034443c5440c040d000c1650790081da410030021a410320b040c000109207148111201020301404010280d0b000d4068100108440c2d640a50441c0d4081122041e206e49003008000b01c641d1383e1018801407450399240c040724070044620041005802000300c3c0360040b2458038a500900c200204d904901400b0140e0780c00c540c040b1001c50b4114021020041880c0c800d200b140d4042c22641c00215403181201a4598 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 359452517 1250 359451267 359451271
    0x40302060313110a0312032f07031806020c030d11060a0203060f0315090d0201141303020312010f1401020105040b0408031504090b011502030a020a06020d0b03030a02060a23 76
    0x30140c00002c0d64014001401c111544400e0010f054000c81c550341c1c6403407602a00c0c1d075407442e80880c0c94100c2c610500c854010100442c1e0074202c0354290003083c0014001c2540e04040c2c002d804004500e2000241d0610241c0c1a6000c2c0820360000d040e0001c8103010985050700c403e0b035403070810020b03141d00f5004100c00a0002d410040500c0050707240c1c0c0d1003401241780d00b40d0840506500d4800d41045050f2085144103c1d4050100401607816101c0000020307800e840208104580149601c0006914055032200f0030030b8180c0f103841500c2c68a04000b82d880074010003a00080405103400d50300300b11100101c046817449040a0009100c3c515064450701e00d20b01c402040908070340000000205400c0c0e906051202e800d9006000f08041c603150305000002107024050a107181600c511800d244500001c141d686003200c80e4010320f0948510359070600a500300c000d068000e281c491090050780e640510181407409510b50041c10340c0d203400b84d20013080e1903881c0986e54503c0b58084000034040000d1103442d13 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 359453767 1250 359452517 359452531
    0x1c05010e0108061f0603230a0c0e0f09150d21020105100b1b0708121c0603080d02090f0d060207060f02090f01080603070906030c031406060901051c0c08070e0c0403020603 75
    0x150b8004903407d01c2a0002540ca000c1c4001a0200800007055625444085c45100c10354810800190309001e1100b02d01d0300c074841550000c40240004c0744c8804c0c0c1501410030400182106a038118a6511140b074080c0300c00d000c1c8925070140b00128203460782441220350100200051100c0e892038912420090300c25100c44000101d035801d4440ba026070201705c1e03c0010490700e81101c00e61100c02031018803542100300c4419840c1030b1000000c990b1203150046ea41540d0304042403074070b0801d8811051300254401901950000e00d46007084049640d8105a590780d1400b41402680d58482454010207c0b150350402004061041c03008018903200c01003220380c204028205030a03140c84c1e8900103440c00941c0d0344800c4071a41000c1001c81017120b000c02140440e032142c00c28005200300110440e403202001c450040c0c10030140c0d0010400c61070324525840b90110741c40500c001d040c1542c1c03a00303c0200c526030400c4060b54000c20003040424446040d007680000070040301d605060441d03001801d07500c405800c103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 359455017 1250 359453767 359453771
    0xb010914060c01240603060b0a090e0405010e03190807180501230301150f0219060b0d02030d0801060e062a0f030406080609010504050405070b1c05010e0108061f0603 73
    0x1000030b2540961101407502a42898078407601c86212800c407542e2220f0241600080c101100014001199416100c4042503070305d40000703060500e92030304003001008006650540d29070b040803545810510003002d0705c060f030003003e2214001d4054094101280548418108001c0c00d015080a81903294244251902407030a0440305040e001e101c104041d1030703240f5100b41d410000000404d8080c40004d0183d0001e81c3c0c0350720380c3d000c3c039550041e42c44189064a034110305440c4080500044c00650205d03ea040e4024207a1880c085250003080c60003043ca025840400e0440c1c0041c04842d0700030003000c2141a08640e01440e06000d4041003248038010780c140d00c4841c0140103103044209050054105402440d0212a2125500d0000801a034800c0d00d105c1c3c003543c010000400c4905040c010948030f0f9030401c0041045528002c6418060f601c00a000003200400591001c0e1111072801202d00810740a199801c01d541800170b42420420081c080041c06040321b0f0110f4103440d150081481210a98100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 359456267 1250 359455017 359455027
    0x150f040f0210110f03070c24030b011205150405090f0a02060c070e0f150105030c07020f011b0506010503010f02032e1d07030e0102090105071511070f060b01091406 72
    0x5075041e000000c0003104a01613681d20f1030f03842500101405120f800340131114402a03450b10300c1d000750780c0a40d1184406d28640081086014001c3c0c000700c0354000c0615102d1241e0798210700390011110300340e5101d40e68040114640c5d806203401c1c024650042007230307009880c26649102c3c62540d0355207060b0000f0b00519000c00c01d40c603450705c1801100010003001c5075421541c507140505402d61501180e4009424208202421081d44500300740c2384100820312940c0c2ca050b05035001c02220002c401d100e0360404c10030199261450041d8003500e1200d6205000816155041404041c01e40744091402da801c10304c140100030b4480c40e5464261059208070058101091100460032291020380d00110281c44071803450034000507079006000d205054664042180711080309409080c0d00c0394155050000d0424041c810100d05100b0040015180d0310b9000510075070303201a44505a0420707070003603c50400c2c4000c0741c81442a81e01503e51810802d01e030051503542880b5914070711500b0035260b1802a440864 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 359457517 1250 359456267 359456299
    0xc0504060e0411070f0516050a09023601021902060910020f0a0f05010b1504150e040e010c020d05120c03040f020d060c020705011701051002030f030108150f040f02 72
    0x1000b194031038500081584d644040c0d0030100445000c2c0001150f040c4100260301a0b01d90503030b95484d003942c10052800300e8451802403a4400783d04182006800700400705550100d0308800f038280c000400c0b10028001a0300c00c620b001a00b032a461000e004040300142c0207240c0180d558104907050b0300401c4a109503660142c10701245481c5150810a03c1032260000340302c24840880002c5081034441e1000303011041d008014001c0e10700f03075000d4580302072009101c10310604590800602c400005450000c4070400d0801c0040c0660741c0c0d08000002130396541c05024141c0754140314501c240040b03400d01c030f4900060f012605d44100001050003002000100c04502041682c852640d040390300101241c80392201c90900320300a06880b031040004d0710070075400107200e500421810811080c00980d101050b860141400b030b5003080701c00c2001c1140000c00c5035072400402c45018601a1440000500c1c049080025034a0004c4001d4500d440880402e0200301c0003c841010303180c00603a05540d508881e8481107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 359458767 1250 359457517 359457521
    0xa0c051306081008060c2b0f050105090a0c02100c0201200307080610091215020d150504090b13020102030f0a050c0c0f0d061a0604030f060b190b0a0504180b030106090c0504060e04 79
    0x1843c0e071f242c4e503410203628601c080d0729030b0040c0b03050b034208452500ca00e80710846000c08950100140001581000ca140c00b0031034240e901421985074580000f08203807114a1100103060038003d055801031202106120f806603104600340d5100005580360801e24201c6400901084200e204d0b049001c03d405460381c04000001846801e61400140159240c0c00c45451050240c589465003005203a000da00019052401e40036a594403600203140105507284c2500c0a210b100c0c2012041e41544410080c111400383d8883c014100844c15a032260740720034254000c1170601d2500b0404501c40c12a03105c401c01c0c0ca940307001080c19510f6010400058000c5950708091500c050401c0265108001040000911040b20074080a2510401042100040c01c1041010810545442a10072040a6824005034605000601c89103842707080c950700b811f94400d4211103100c620494201c8041c0c5030b1103140e00c1418240034890151005500a00545119050040c800d014074030500707040003040036910719551156 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 359460017 1250 359458767 359458837
    0x20c01060e071706150f090f06030403050d0b0d2a05040c03020c01050a11040510120606030903080906010308160204060911130f0e0a0c051306081008060c 68
    0x5503220780c925241080e8007412009030950703000e0044407050001542840c00c452501e0b48014500c440e1400c0c2134882465402c3c54020f0860310340c0140303080204078651303925100078601c551300c00c0c2d942595402d2107214a0b01940c0d0072490346030054544041400c0000c112407001303042172451001e000101d480c034403c044501c59685c0d101c0780c3c107c0d241c2802203070000c0d0306030010580710020000a016680790060000c2c11951044064081448144428885458148035444125a80d460204d046d00f041030b0701c000c2147c0042d4020b9012070b82d1019500d08243e040302d0000d40c00010300d000f500007076140d900c446002c0c0c400c4a044044880385581d0340f80456a4a9000e9405003c22030410880350ba0312142000881e03020f04101922061014070024005c031048000c0825030f8207680d8100d500d44c41d903e00c100040e0802c0040c030024444140039055400c031103e1031550090806681e001c440c2d00b018503101d200c0e40001e40154410f50401c00030001e00d64584030840e01d44e19540301c0303061154000290380d003983ca880 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 359461267 1250 359460017 359460029
    0xa060f090b0c041401020708031209070e0906060a06051c0506060c07090e0c0a0308090103020304060608032a010e062230050403030f0810050a170d031806020c0106 72
    0x1460602c900e008200d0050410b0b02e4102283c800300c80d10020043e80c2c0e070010707403003000040e030320030040669010321002500d0b4100b03400380100e0302074548078000300707400f44802c403603a94040d4020f1042016500d441e0010340001c0070b49007000340c50f0070321049003035854511044c8429a03080d240d001003a042d881c3e100403160400c108a00b692480c0d83c84000144c050310360a4000b206070301c21117902e401d0360314001c0442800c50744e200e0340b01450156604015070207500001c2085e15255a104070000d5519400e0004040352540e5032501296640030304c0310000d0100804502d00003aa14020003800350450004100350051100043c0d450224190a8080e08582070f00c20000c103c0714000c0ca50b0688801c189982c01da400c140c40c8107001d90b0f1020044202c9041c05144000b500050b8103020140040f40110000394004c854490512007440d1500c0c04100075200c03945c42881c000d40d40400802000c2014401c0c0c0d03060319400d280620195234101000270030001c1102024100650001c2c4100404100754810402850 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 359462517 1250 359461267 359461283
    0x50409090305030901050f0c1b032106040f0216030e0f1807080901090c14010c0b0c09090105030703050c060c010e0a030c140c010518010c021801030210020a050a060f09 74
    0xc40c51400400d5078000341d039254155820480410551284884d144c0c0c40303655003001c3c140c2413540c006031101d00005038821100c03130b034041080385e2150b1150034071f520410030440601191643c2004800e000c2220302030000548070501c141308004a071404000b5269007144c141c0780c0801c00f543c0b1100042c1c1d20820322484968081480c0c0305c0d000c1d00f03510030f1150921440c07054550f4001550380104d1301c1c1c01c1c0c0d007035850020603080b508041440955000c61ba406440386e418945901620503e0351160f1180b40b0aa07480156004003061017511468185110b0b0b02400050b809130107290303d16a0358559501c02d0450041c030641001c03400e003404a00940c881c00070f00c546d00e0220713441d03c900340c10044c190030882d00e4291070b426661489106a210001480321450b4410b94443d8600701e008480b14841b41c1050b10050704006200070300130f0241e9031704499a0902c02508400c1d5086515520400603048003802c0400f06641182100e04045800407592086040d040795021843e045d04501c640010080c503000108190 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 359463767 1250 359462517 359462531
    0x7020414040507031203020c3c0124081002030711010c0905040c0305040c0303200102030c03100e0108150a0e0d0807090906080c06072f0a1406030a0c050409 69
    0x4040050304001320f9015001d80d00c1100002e2204070241e01c180e1840e1955584502e1800754180502c20545141400b460b07610103604203038203103905100d800c800c9601416034560052024004030100e040f41040318004140b400249003400700c5445039a011400e00301941d0120010350b20303500866031a000e03001d5010080000c004100c00290a44100e4003c1d41e000e140b51488a0081030f001c4e20529000c0d030303040160b48010924596048076090041003002480a00c01540210344800900180d4099590a48090340342e180894040c400d0749078a50000f0022000b0790010090f81c00007080d203071040c44550024980715503410b103420014114a81c41140700c1d01c03642c01e80c07101941c0d110103c503015003c03540d90340c604282d50f80c4200041e5803641c0240b41c11600b208281d030000d8074004004001191050002da4803c40c003102c40001c1e01d5844940e250f07101c1074000000d41c8140b801ca134840014110b00112004450039050100340359000003400d8140b02075030798a0b8456000c0c02042510020400c1840c18880c0d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 359465017 1250 359463767 359463773
    0xa0203041706100605070f060e12040e0f0604050712020705150403050901090503070510030902180c03101a030402040f0908040f03140303011a031f0906380702041404 73
    0x4540444960f4074800075241c000c10320070310810458041d50f8101c42202d984d6840303901c58400805d03121440c0003c0388250f070280d04403110640d020703100510040201e0b20041c989640c07080c2c00a1802000e0714441c0786071908008840360000c0c8400c031b82000c1d0000060701c0c2c01c018035005203404400380c95500c0b0003105c5803c020400d07a02800410211600ba666000119a9000bd269403a000c0380180c2d07a1000c0c0d404500f440c00e600caa401018854001448450f1140307462840c050002c50603258140140c50000401c280c40e06600c40e180c00814900d20100130100f0b01001d50386403400f01401c000d02c0340344ca81d100181160401d42111314080d4000311901d80c1c980d034607810800403903a03501c01254030b507141c0964074048d04404010b5074101c1d0201c02c5407108201d402007100c4003550004140200c91022485106850384641c0505405005d120400048840c1441000700d014a402d403101540303100114a8000d18006420396843c0880c1c0e0b4412080d00c900003440040c0141c54501d145002c061010800c00c024 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 359466267 1250 359465017 359465023
    0x22805041e091503110d06061a0406080f01120b09100f06060e030604051908040e0c03040b0603010b13050a1d0c0108072a080405060c010b0405090309150a02030417 72
    0x11034500c00d004110b6462040809401c1c83c0c03c0f440701400c004448550340240b4103001700c2c41102148110400190340d0388840c000d000800c890030130340011081c04201032101c02c0c2c01040054006130f10030b480341002d6141c110180c07010b41071441d00404001c802400720f003031368000f08420074603d2000344040c003c1c1e21003203d20307600600c2144501c40014000309210100e030b06011401d603000d103412002074010f07401e901441200c010040070040700c1010040100059440117207a0070ba00070081003900984d00d0400b420622607030200544020310a0745002242c204903075641c1c888040100c0003500201e000d40e02d03074000100070b145942040015490001200e42040e0303010170402c8031078070240c80f1001c0759100d00c20203e41e01c82d031458480c0320110071041c40b00011035076aa1108512407051a20520740741e144c4000c64410340000148a855a468000d81081c1d850107019030350340001c282000354101000350000800007003100340d002440c12800902a550141b080c0216800350401d030140381880d10030f00143ca69 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 359467517 1250 359466267 359466269
    0xc030c0209130b06151b030403120e01080a0e0d14041e0f080d080112050a0206072405160c060b1503010609060513030321060b090102060109022805041e 67
    0x643c1c07040180011920314041c1c03c0c0c044d18001d4a00c2180c20f00d107041c1c40f0002001c002d58011111381c88140700c000001100f42622600e2154140d8545401d0455000050100100640340005290601d641012042000034113030400840c5868203102e0101190602c03020b81c8680e0700b1600e202c80310300e0641041010f125140301c00305d812006201c00c600e0303640c40072651502a0b11b4680c8000540c81c200402402090201e518200c5008906581c074004031a8001001030780300e11000c80b0040b22404545003c1d1040b40c2c5003c4001c031030141c05203da031914041c00361400800701e2030030090210011054080c048507034890310179050041c0c88103201c0d10041300000203e800034403660740050303100310300812205d2040d030980e2030388015172040700151401c40c1c0d41510301214001c07840019200d11004000085024001d2000a1002800da0b03540d0300406000203050120582081c0c4109004000e1900c1c0c000f02030300026003440811546048480421408035158811a44a45681000761420b02c0d208410511208 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 359468767 1250 359467517 359467523
    0xf1c060b130503060906010503070303050f0c190302010b090402060307030f0219051306030612080a030e0a03030204050102010b0a030b01090203090f06100f12021e04020d0906020403020a061403070c030c020913 92
    0x500a45d81d1510b1950b46d0344c0f42402000c1c0c15400c00c1030208006406040070f8504444d02e2a4800d013442c2c0d10481051900d102a0b003c0500004000c4c82d600c00e040c0c081c4242510640c007501c1d411641d240a4011680fa4071001d8408402c052744c6541406c0d61201035415620481a16410000031020b4800005c0054000e601036003d040041a800600b66000344620303022902c6504a2070400149a151148a40c2041c0058414140c440482400c1000b0510179046094400c1d140141ca80d810113000908641001040074050101c5900a002017440000b03021b044611150002d6a00c1d038940d0015070500004028419040c4181000c0c0724013031884a0b04c000c05d8820028000010a03a200c41c4401064445400030350001e4408002d0700c05668005ca240c00500c601030805440d15682601030021284103041c241c0e51070382d001c2030a00c11898503010580003400240340031045040c041360811340c2c61001070161801d202e21100c0820030503000d030848600c0070b038000300498510720b0400a00e64070190465000c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 359470017 1250 359468767 359468773
    0x4030e130f0f2004061407080c010507080403021011040b0f0f04030b06090a0203071d01140c1c0c020a15020c13020706060512030a0e0a0503010e1b060f1c060b130503 73
    0x5800d04000701800e49040b6030300c44e82c90b10320300e00c1d41c200f08140947c002e001c1540d4019041044c881030f0002401898041e8002d031b0341c0c100703141c545410020b040ca0006452040e003182020492402c0e0203844041e46e0907a00140308296842d442c0202e0701c13a03c0e1150481c440034000b00070800005200060010724410034096800b80703240d42e039500242c8201e21044070100c0110311004102d002d0b644519821990754a41070500d891a210070b404062201e400860090115074000d1420181c1030380c460062003240c1d2060304000143c0c00b101c3c1e0004950364428014004459078408070241c1d61442080403c40c10b40b005410007004400b40038169005c0d500c100c04c03c0e40c4880c104000000c06040002e50150308000c1039001d1810030405a00c01c9680c10010380b0075640c40001080049042d60707080c41451092011a40180800c802d00081414490b0340149548e216032810311003000c650141d01c0c1240c0c501000b024a100302c010610030900020086600081d180501c08214207690210208000381501c1e011011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 359471267 1250 359470017 359470061
    0x30714070315110a0507020a080609010f0b0f06071502040f0306021801090b0d0c02120d02040602190201021b03030d0c0206091204080c06031b0a0e1804030e130f0f 72
    0x2400f40d41c46845000790240b001c010110810b40b00d48003822403c3d00c0244140001c3d03594810541c907100c005c0c0c03010102a551603074035102c1a0a0b521459500803800d9616640000c100b030002035150040c403901034151440340d12440143c6882c0d034100e0f0058440d10130f4012550b80c80c3d04210009411404140b040c111300070308040c0007580941182002c4801c501b03d914600740d030f20f1401002902c0500380000552041c45110ba20030207010014018038805400010303255841e010009241141080341c00e0300601c4a90321100140c1d0f408114403501080012410b200d00d0405000700e840c40c808c0700c007036004851900c011283c2d6150b003c41c03054050819030b411200841d031240864a500d201d1441440a642d200039145941824007a02031a40441c15442d21016030441500d02011948603101d42ca00281000c0748800c82407a194002c00540c1503000740d018124a060b9802828100d20455110312500c40003820f10b203c1010b0f5000320035030f140428014058216509107440260015104440b1951180360b9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 359472517 1250 359471267 359471303
    0x304090507020f0a120314041a0705030f07050703110a0f030905010315031101030603021519030507050d0504050709020a0513050613030f060b09040f1109010501200307140703 77
    0x1d990f1003901c40d02d400343c224003041740d460384c18003180c0040782c0052544031034801c6140700c41080442c5c400c0c6c1c0100c0d601c01007901148450070450784020011400e1240c180305012005401d00505540841d45080140d560b140604007914001d003000040141e51081c0c0794581d040100c10010180413510070f4076501c406944660040d8140c50002d020381090040c69002000803513010713a48400c07030344018100014002c0d100d0300443c4004800e826140d03011400011101d8283c0942c14a00754440340d82c1c42e0400250404260062203441034914040b10b8940790000728003800001e012110041c2041c0d8401c540d03c1699040c054441d401c90445415407100b0004005514104241211800c1858030b40440289096583c1c48200010710354040d60202d030345864625103a200c500c0080c2c0250b0040004542001507441c04c1c1c10008030040308180500c965400400c0141d801503010225102d051140800e440e4696403a40e10718015080c0142420240700e4003203484402c040b94203400e403809194010002d54502c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 359473767 1250 359472517 359472523
    0x10060306020a18060e3015060301090f0609060f15091a031c020102040f0308030a0f0b030613020315040f26030a0f0209090a290a05041d060405030409050702 69
    0x480340300c0108144044041c19882d1072003040007810604e62500d45440c00d104206c00c00d14844c418000599030048200105000460070070b1644008110000e00240703150741c0e01e0750700602140380d0040c2038949a016101c00c0081a0700703d11000c1401d10010001c9034224402c04075207562503c40c4000b40f520b070201303668448040016005020310007030700901011003054030140d042844028200c0441d50f00340008201c491999521100850013021450303164205100c08104803007401c0c03048585189048601c540315140412615070000c01c940036440d10707000600210b0f080906041500340007000d400100310411503040d02030f40000d40644004200c0c40c0e00100781c03000c040103005030282581c40a000007000142d140e007104110480841e005824060704402140014006039284080ca90b01c50b1a29803200003850703840040600140c01200110b040b01e0701280020450340209070055461300b00c02c0f40a003400000c2012003003045003c5601c03070725260400c0d90300d98019010340d0400c5c50070803000c185854800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 359475017 1250 359473767 359473769
    0x90b06040509070806240415110a030305070e1c110607031215150f02010e0a0317060402040b0415080609070e01180803040e012417060310060306020a18 67
    0x644110304a450b01101910031003401407520368001108100300003004180f50030084c940b031450951b9915242131540141c8100024541d0400300102c0e144c2c0c050740ca236400141c52102c01c0e01801d00182c2504c500c01e04580421000100c0354102c030107151800e1052866281ca00825400350b25980011884541000898820341101030001080304481e004840d0090f400b2800400d44202014138203a52404000703c0984200c090b44081024440ca056a040d028090b03000110752650140c1207429440c0d030040c102070020807000c1c540346540300018204e0b80322941182c018190803400940c40743d80c0c0b02c008800030650300300104001031141c0b0114109050602e1103600403011900c645800c1160710004545014108002c0c03030100e914100300081091044c030050016004075000e01170a03604080007180d11141a5505543c1c0c6107983e9007440203540c3c082e8480141c8040c1174075800aa485800c0080e10340300442c56040c0540c7d190840020400c40360303a00604804041c1c0d120504540c900c03e88495482c921 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 359476267 1250 359475017 359475019
    0x9060a21021606050c1209030c0106050109260a0c0f0609061e03091a01060e0a0503030a020303071d040c0e0f0a030309180f090c0825060e040f0c09090b060405 70
    0x702c25401c00018441d900100e900c030f41e82405150030300f68981c0450440e03420a8444ca42c1c107800c001113010909a0a000c0c03900039103400e08203809aa481c1046180ea181d203010030240d90584400d00104001d00b050180018868001d4a0b05003040e07220602d801c2c08003028840c6d000800c92161001800314054590028012040060040400c8030f900b000d5010308007080080341c552035801a203600c3c4545000c00103001e44401d68401503d240c0aa0621076449541e412451080c0e20038480700311244d500004407507200e602c924000265898000c04107189401505000e98010b080c040130305e501550050125100080031110301c021050103c0c148990444580006000950030b4a03061140902000c0003c00d002c0000c0d00010321408071254000440d810390b00103d40a00132160304001c02c4030101b01c0d0b1b40c11000110303a40140d01c4002c0c0c0e0119850780943c8501030034003280002c080c0007542d455205810381041084240504180e0100003090810300d030040700342e0702d0f1411801204a0611200350303019148 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 359477517 1250 359476267 359476297
    0xb0706020c1504081e1e0306010906030510120302071d0604050606070309141c050607140301061b0c080105070e0102070b0403030804060b0a0308071104060909030e0d0809060a2102 79
    0x12805c124003104018085041070f0100040010310030f201291018500e5001031a12a942c40c0e0402d00b000410413a076541c401020907041c030342800084001c03400c483c811038050f4100b080240d0303d80d18099003010415486202d40c01d0000411205002412119511801084800308250707641c0382d0800059006041010b0001038985d0028044a034180c1214812240d000303108d40c1200d0742009082c2a000c5000c0000c46541d004070092000d17154001c40d002d902c0d0b4081c2040d20f0f0866041000080c000301030380e000c08000301e001030256407e0000003055807003e041c000d002440305107050103001c0c1c800c0a010810f00d0051050304000513a0070b00c2c42c029141925419590340d0708544a40e21684080c0400d800e04503801b070003841002002540e0394000300700440c0304e1200954011074402c100400c07144103603c164050390030700a0140002c0d611492060240c841111051110125403c21030058014058402d8001c83c000400828050b00039040046c0780710b00d41040f0341a202000e8004080c1e00507240814180c038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 359478767 1250 359477517 359477527
    0x72310170a0b011b0c03020405010e220303090c032604080c06090f0a08101401050a0e0a0b0a18050907152106030305030405100e190c0b0706020c150408 67
    0x10020b400c90680320a051504000038a408035641e40342c508902803c55031802503200c1042181000d010360f9004204e03205100d01305103041d00040e400c800508140020880003112030804050003540722142c2c1c5c54000104503100d6840b0301c1c2c1400700d5402458050580c4404400c514290f02d80b080c22201650302440c06003003500c400c44180052034214002890744000201180031107a1a0405003900600f2544000e01c0002c4014050301c0844855000480c03072604040014007140d12a40e24a4080720311010015003541c3d00e0752b500f00014101c64405a500c150043c200084070b150a0002601400ca102410092500d95944c0150384401c0c0d4410400d121030b4079030580f0701550198406a0790155800d00d10f080700c040114050007244c03c1034008401040307002c070501061040402228020f00b141d0b0300d040200c02c12481c44203540e00c6551381d01030f040b400c3c0504500f00700700c0714681c01002020711200044d121595403510703102940104080d4080c038031078015101c0101038025180c90169400643d158685 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 359480017 1250 359478767 359478781
    0xb060111060c2b0f240602030702010f0512041425060503090304081006090b040c2c030a050c09060121110405060310060801060203090a0b07030207231017 68
    0x103a003100448885840d440c940c2402c190700b50707000d215040b001d43c0c04002007010301442808642101440c500000048130785c01407001c1c07600002140c2c8515024200024081c0441c0402c40f4030340724803460b821180c02c4600910041208181d0146140311560742960b030b0201902c40c60801100d01086110b002c03d403c0801082041e0043c001150416105c1065900d410b0300d03030007118500b135414042502c03200c9e61100100849212813192800018048605001c2c0021103040100001105210104100b40103000004403600800c800407000d000641a50140207883c240340f500c40c3d0b80c0501c01401000e29200280d0990b214208520909645071700c5808145040d210390801480c0c1c00d00f10500e5168100008a010b6480300080d61084110003102d400300b07400d00710000d10050301a8006803e65100340a078002030307a16041d00500751000e00049603103d4030076040c102c0c40c105051344452444c5a00c0c24407602403200044604e000c2c25015980312a0411b8000005c5941c5907001048800880c1c2141c045404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 359481267 1250 359480017 359480047
    0x7030609020102011401030506060901090c0215060a17060a0501091812031404051e011107060207060b220c0c02010f080414030a20030702010c0f0318030b060111060c 73
    0x6036006100004115039075444000c5206800c0c2c1040c1c4840c0c0c4407508010f45172410006141c094600100d00b403185180310361b0083e6071506204100007044000fa40002c600d5220758041500800c08540b01042e6a50040f01c0070b40c84800648406881300c0c100000851031681d05e000d01d00782c5510b0011406421205600c0d0a0a09101081c002c410192142c074039500705409032181c580030f00e010f8000b4055490b60250940a0030300143e508010b1641009080481e10715502d054800d0281c010f03d000d42c0d600b12500c0d1150041070707036038240c688c0483d440000084104210f41e000012141d510020410700b0300c446020385003850700e00d030000d000480000d14034504520420035180c00c82d02c945004a0001c1410030181d055412403c00c00000070003c01d0289040c03c0e000d2005120420316801a41c504019a00004c02c0400c0806000d40f40c81020665a03041500c58004072000c07285040300115001c0e143d150440e0300004c10b0300d02038001000e4200c0c1640314031000c140d01e030042d12540002843c2151450b61034030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 359482517 1250 359481267 359481281
    0x4090c051908120406020c18221202011d0a120e0d0210050a0905040612030302070c090603050c040522150609020c1005010b07030f0318200a060c0203070306 69
    0x103415410031074006082e0b01c080048071200700400140540b540d0034030500134034050360805610303c00e5092214038034291015140346074004040240504000d0b00d059081582100201c0008001e1600c0360045490a0b03070652103c0070044081c2030002109003440303400d5580f0301d030703d0101801851091a003010f4030750040f110f9044240024183c00f401c1c60003600010040000000f00002082c000030340100d0681d07014007654042c020844042000310b0400c581c2c84942ca200b1640141895070006100703080c0003c201d0303020000c100500040c4140c945900c1c1c40c617240c08120400c0790149040c00081860a41c080203241000f82c05216003604050090310360340b00c0c5044014825803e10741c1d074000442d12442d680020048900724400501075601740c00741010884038144e00c03000312280c0c188010000281d0207924004600458034001c101011403641c0c03652725007000e031001412a484541c892040e010500303140741c8101e40440c0c0a20031039aa511041c0c48001c03645000940c150001c1c1e000380300240c1c96034041c0b8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 359483767 1250 359482517 359482549
    0x1080f0604051012050a020906060a050f2a0304180e0d030c0908100e0c0102120304110102070b2107140d0e070b042405130504180803071106010504090c05 68
    0x1240240d51402c20809000f00c3e81310641d0300d0b402810019081d8141144104d80210341920741a01d04007404500801e84e010f241c40e07000c01d00e11300140d0700c0c0301d02a03e110f4540e041303070203041501051854240d0340c6070390303900c03038845c684540011030202407040b05107110b45451443e800b8090f05000781905002c900500010500344140150030002140010040010410a40480800080301641078081d185000c4a602c200350441d030220081c0c011500c41d220640b80c0007540124100001c445080040c1c4c20014a90081c0c00d40400c00314401c16000011441034007806c200031304101d00781d100c540e0100c2d01d0001e201608010440104030402c54040c590348004241c003200c3e81511940c5d40c482c00001c1c100c1d40315074803041018100c3c040b0445240024403030704110051302d082c11454103a00114041c8610010311405100381d6031a83d429071b05150008420030595403244070980d40e80340004000c1d006403401c00004665116141c000701d0942002e118052403641c1141c4440d800501d418100130910318128110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 359485017 1250 359483767 359483791
    0x1091509091107140a08070f05070801020a050316090303021e030f0a09150302040303091418040b2707031b0314010207060c0503040b1b09031509070501080f060405 72
    0x1c4030561445103000203011903401a40e15031003820559154004190403031440e4015505210020f0489005c69110a9120403510360200d110b041050403c2666480a9515400058004186680300000358446e049001e501404032884100c00c54406906020040c050317801281b11000452284a291181d80040300031070b0f14240201c0700f202c0080d04502d101c503000c1038101005104a1045211090404444d842c00314245840e50f01e0080071403a4900c10b650080c007241030b0700d00d103507158249100e01402032800683c20b1400c080c07a2410000000311020b83c1c151903070003901000d0b1502072007420b54030125040144501419031b00d94802904000010424031100c520002001424018070788420400400005803030321a1410003005071201d8141b400d0800c50108100000220048200c5420100c03d4010181548030004001d843d4070030015440d605104410a182c11031a0034250340d441894050f0590312166600c2006441400c070541d81513030f000400700001891402c00d0751290707911503150205 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 359486267 1250 359485017 359485019
    0x140f1f0c0806060313020a0312030c08190b2701030b10080604230a0308040639030605040905010915290d0b01092405010e040f0902120706020c0109030201091509 71
    0x1f88000300780d60007128105160030482404c2505446203041030445d0b420b2040c002d16002c00c991014042801c004106255100400c0c04903440710300e100d403e0513151882d00c81d01d00c0300e449103901000d48244802c864507403145001030007090075640d0100c2100e01040040c0b5140c4c8803582c404d40e246012400c3d02903075080300050820f00500170000004100d000c0e4607600a6400e0030b00303011068400107007120840503031032104a4841c0500c1c0b1a404401c40c07080e422011240358281041300074080c1c5034402a840713424007441100f440019803006139031920551184291030141010b54040d0f40c441a0480c03c050b80d900703140e0003200110780315002c5d0150001c04200341072050f80d80d8840a4902a000481c50f2580c0320407c2c82003440f00d074444603035025003030741041e11a85004002401003041f40b2020740202e4880d001c01240ca4560303000050780a600a000207407480030100310558904052051800500c1141d180400c0c070b501a003100015650181c0d01c030804641480000041c0f5901109000b04100341814 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 359487517 1250 359486267 359486269
    0x31308070807050d0201050114101103190e09070c080a02030f1207020c090906190609090308160809060601031a0915130e0d0804140f1f0c080606031302 67
    0x10040c0320851003100820744403a0142080344c64040390703e4210040d60314110046c00300c500d00000b0061200d4044807240036101084800b2911043d0602411850b4480442c242d0003009030442e804600b9103843e0380e034401e0034409004000e1041015910f010110708007a20703800c04a15800014804030140380112441c21410701c88001c105d5000c0703040c0f400c07240a46800c1c8828903078103004140c1c1d000811a0558128248412015100d5001510606014110341c0780204407204d80d030007850003080808010452102c043c140608144411140712690440e8001c0003443c2601810000b4001c021b02402007400b955090015002020707462010680d24541504480e241c0e540d0950031482520844103000900340d00809219a5402862a003000b160070076808900250340007520700c07451511454048125240c13410841559046e44e8044001405484071000400c0c40001d8010124955460341100e248840845c81003203920600207980010b40a0021a41a02d040d1001c0c60708900d4015a8003500c442e1a4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 359488767 1250 359487517 359487533
    0x20c011d1302091c0807110d03021509150a14060a030305160812040609060b040c050d051806010b04051507110d03030b06180937020d06080c0a0b1e0313 67
    0x24000c442c5e0f0080001e068042280480c014103100c14142c400788000c2c1140d0350043d45590168030042800d051450000e03a03081001c1022421400d01d009018200f41440f0030014003034a8080400c40f410802c010200e82c031410881c0b6003500700c0350541d80e118206071318031042c404405001c1209482902c0140302405203036543d0507015010b14803501c000241c0d074105140c0101900e5400d00c22500c568681184115103d4010302258140c030003100e00000d960b9148131500585500117038103079126126400020030644074140050095a0302182c40001d402d008483c0c0000e50300c10140000c06640841c4d864910b6400c0c540d4012400c40d21030b080115500300800c0200b0f030a5002512f00b00c00070340c0c016440103081e007480b041c1c1039007000bc6002c40170081c10907080061001d08610707443c5d5403000254101c000703c0c08010340c19540c1740d054250082c080b05942d411029034074041404c86078440d041140001032103125080450f114110703490b5101c100384c0e0b00410300907665080285903580c01c15040c414080080c03048 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 359490017 1250 359488767 359488819
    0xc130b0301090b09060f0a1202121204030c0e13030509011211130b090d0b0a020d0c03060303080f0708010501050f04030206190909060e011203110105010303020c011d130209 76
    0x11190014540015100b0000c004c40d024007440e0041481105020041d11800c110606032a00303861002041030951010401c010301b1a52401603a00840e510191207a004a0050040324015100f0f07640140d196007180c0005241543d180c500210002022400a030155001e800c003a2414146040b81501c80d004503402d5035407541800c0081400083c007240b8040032020350394050b00405140c98203020a580114010940703e0401800c081d0700d2800044020815030100c5031444110038003800f52081081000d0003610341030000318085207400e000074440350030b03040304144120b601d44c3c0e48a003641d1030480199801d43c01401c100a161904102c0400507071107900090241c00c0102d0011114007082400003811090990817501000d424035104201c0450b060441c00e044d50b1003a4200c050032105440d040e6031841e030780b20700d821031035083c00000406c1c0f50700418086071242c400c1e01c40b00940c000040da0484203205040035684c8c1322000c07184007138414007158064464003501414100e0860007442d4941040640 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 359491267 1250 359490017 359490029
    0x8031611120d081b040317030916080321070806011b06060f2d03020105090a080d020a1203090221030403050f030a0f111b03010b10030b1809060c130b0301 68
    0x42418040d8002004c0c1c40311400d500055241c90506046079154001c0c803544034510faa502001002192503014140041007607a04440303201d415081d80d0350740140e12030304032003640b5101c0b075110b195418142074603104141c402c80f113654802609944660045d50a01c40001c81e0519040c45020341800083c0684101d40c0940520071415244d549050300307a0038050001242c0341404031400007842c5d0100c0180209805996090824a89495800c40072a40218840c1c3c0f007a00a4804c8111a0306002d401003001207650f801804da0f03064000f1040819425201c80400c02500200b040075500c085000252410b250000c0f44d40a07030340703050b0760b9864080c540501504c07400f61744c1d0000218510301a070420301c85010f480a508046810f420601c581540b05c088000400d11001200d15140b002d90380c0a50003000e840800802030308003001030020060003055011000d602894101c0c80c99400400e81c25003e0340305000c2c0c48005d04d040c2c1d64801c064010b503008040c014080081c54100410b40345114000b440c080c0034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 359492517 1250 359491267 359491277
    0x14070f0813050c1002011a100f08062407060c03020c0709111306020d08100b04050f0103090506070e0414011214150403051908010b03150a0b180a08031611120d 70
    0x190b4400c10700103015001c0038079202e03581d000208ca03903040d000300c4403110004141c1007400c04c0d070b0342e03110210320700b070f0500301c00f2503440d0062000402151010401400c8124014001000800302d01842038080b44201143c65013030347e00c404810000b144031070300111410009034008908000d1407500e0300e040350303102d03400090250304071206240006078000055548058558801d1003400d1034004030011512807406128024041611070f0203440e4020340113002042d42c020100c0f105440d10a80c000c2c18454002c0701c0b030340300390301b01340e40700f905106811444ca06950808041118019260303a88074071090f843d488405240c09042418214841c0c28605140705501948070305543d07030286070303600402008008110092000140043c800981002d00352540301680f0071100400c0302000300007501198540c4d00410a805001410396441407001218081019064458210a503182d14080d80c4900a542580c411800b084ca90740010614030441c00c05402001381003a001181c040d41f11500f400084010311020031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 359493767 1250 359492517 359492531
    0x3041e05090a0506090112020f030a061506031506050307180e04151802060f040e0c130602031206091e0414060115090306020c1603050114070f0813050c100201 70
    0x1040c80740c200c540c000c614032400c20903440d010300061031040341800380f00741e007080c4803040c035085445d0311942401c60741c1c00030101c826400f800e24002000d480344804031954200400000240b4a00a00400342c0900c49040701100c1282070110480f140e400c0141740c2000c011602e4140e8203144103081d8000060601d007409142c4618040c20280c020f1b00303240d1003850350329140014403d84081000450b42416504903002943e903c00551220f80c14050754010041c842c02c0c8105000407450440f00034901184100c08a1b141e0f540d460b0707401d1341c50340505d100c1900100c41020009a1078908840c0b411703881062980c800061021000b001102d061040340c2c122100c07108000d030180311003c2081303010700420605200381c42c854440035000701f4210a0b0300c40200a241c0200310144480c40502000d0109142141130081c000e80c7c83c102240a80f490b0400075141a008001240300c00d03121b449112001c40740b681300c041a54480a082c0c24060030686000c1d0360380d002d000b1200d1107582e10704603864554400c2c0d5002243c51 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 359495017 1250 359493767 359493769
    0x30a020a140c060c1614130b060c01020c010b12060c030c030a1407020a03080c0c030d0b2107150203030601050702061c0c0504090b1206161b0b040311120f0c03041e05 73
    0x200b12250803902e102d4031021541c06c1150f03034083c1490038121501c64003281d0074030050041809405072000c3c4002d0355002042c2440c1c4440305500180009400700d4020300103400c044125501c0e0352065841010410042000415100d250002542c108130101000190155103204c90141000140c4004005803c0400e040c000e00d9401480c0170b0f0060100c200741d9142045002080e65030f441034014184015880304541a843d5a4003c10032581642c000b8010f40944d065810302c0c0e8640e40c1360b0084210400e921803038100c4036440001580d00c10703c0c0c1178503654900f203000d80801c526138001c49980013000c3c0038811600c00040300d40c000c0c012215100e03250162528180200300e01680c05688287c1d006407581220001c0002d0002512508441e5040380d0b51489051903004803094106105041030403040900c0b1901000900c5941da4490b41c065510300a034040b0b2841041d48a10b5120700c0456400000d1202003080046440201420880482100e02e080d0780c465014241c2d090361a03007171052445140c810021 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 359496267 1250 359495017 359495053
    0x110405010f030614010f090315020415020303010e010501080c19020c1c080d0e0712051c08100302090702150915060109031a150607050708010c02030a020a140c060c 72
    0x361003a003401c0c003041c0e09002c0184e5184c140c0031203040c10031091380c1d46841910f021f13204800185421042d240d12025040301444081c0d07015214414603030950032281d460403032001c01078a040e564031110014107030b407a02c0011101200c0260070400002d40400c0501010b8807110f280503003903516500035110b45843c11041142c0c030035a042c1010380740851988010006001c42d82104e0025a15040000c0c0381e40f1000241c0d0314201643d0002d0368035420445600060003400140d48007106071039804545d05050a010440300c00005a030002110700c80ea190510041c9044034140f0f80c0f0545620445605441b036000000c0003075025510b18905400561403503003050006403840d0740c081002e080100f4968038643d074201d282403030903591102440c5032402140101e01e240903d84030682000301220389907105c505010b904c0d83d0051040c400036620744044125501c0c004030941e4101c40280d005002c80c0c0c11291141074010300039611480c100c0c05402c03040d8041d0340d070301c6002d803030b81954050041c14137820565410794 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 359497517 1250 359496267 359496287
    0x1506091207050f011805090c0f0307020a1b08031209160e09210a111501170c1017090c030303130b0c070c030609050111040801090506130f02100e030111040501 70
    0x1304200c0c00d2850001c4180c035500c0440202c86040d80c06590030750340c2c45081c0d40d150040d40d25145030707040000b0621141c1a800118480228020104d0000a402d184441e5114401c5413040c1080c2e60018040001001141e00e01550b0065400055540c00754040f0041440c115154128010903e01c220074080c2007a400c0050f60030012003000d441d43c1c1d10040c13016030075050082c40e00d2502085254031081072101010f0150104514840982130060f5031204c0607000040900100102c0e54413074102c20034614130344500902c4110b581070321480f00c103680502c544420003800410340103092240c06511209900d04000030341c072030380308400d8038580790000d4681440341c1c850142c80d0b02c1400c1c409021340c00205080d103007100c0c02c1307981c0803100044240715032034114050a14a418030908136404200040c241d0010b4100c1e125107489113050340c0da00d81d107041c07040c2d48400c10044042c0400c2c03d079030a003000501b4400361944200c4c00c613040c12030b0003139035880000b07094500c1c03241120070090700421301300490350b00440c0b00c41c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 359498767 1250 359497517 359497519
    0x14091305010b0a1d1f0c051005070f03050f0c0f12150a080a02062b0606020f0d05030f0402100207090906020706050601230901050f1303050c0a0e1506091207050f 71
    0x1c2480c0210f00042d42601c0701c1804c08800807045a801725a95020304c1442c140d803517015040e103401a00b48902c2800501c0d0884404010800c080d13103070103089110344189031003000d030744020a6884c5c60b4060b9060300d40e081040103040040701080a010382050280034144242ca1064503011510195018405103840342e0384405056880301c0030382001681d03034100756001c1c0c6c0700c548141025031750000c00381800e0b14204840d51039401e1a040003c58650f9021401c450380d01480340495694140c41c141c01c4407648021200040c100c075440c4003080051402c490360224505091040300d50550722402484103c03100d03202c0c11074003254006101010003105014150f07015409003842003201311220030303016500c2e0030009101e00f03d403000940c000290b806941035421720010b9081b201c0d2101150000c608a40744140002d03180d03032107038000040e0540744c0840030b0400d41d002c0c176001d03006036216100100c843d480340801700f59001006001c85506602c9030313007504190410803c02841a0340c600b8007401148503800740d0403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 359500017 1250 359498767 359498807
    0x3070807030f0209030610030215040b04090b0a1d06030d110307020f1f030f11040b1210120516080a020d03051e07050105040b0708090d0809071a0d0b0f0114091305010b0a 75
    0x1040740061200550707046035807526012407914924fc00113009850309801c035001549691540c0b0640c0050342d001244268001e408a84125000756000c0e42c0404000500c010340358000c11244006080c40b080c0d400820b5005071090410070b0044018009203444051000300107a40c501c06070883d1181390185074003009410915600c1e2906200d07907822180300703004280005101c4134000c51601e1011154a04c02007040c00300802d0072040134034005850749886400000c00180b1841c000c9007850000c078151152030740c02011190090425034058034541c02000090071140030035001400c0f60305809009240d014070590001a5614091600c11203140016110504100138242000b540400000700380c020f041150501008a42d15184814545100341d00500c099038505401c4e003d031902c0d01c0703015102000542c501441040c0076001440300042d84000100d001a1301d094040010041180040c002124098030b40d12045650b2018002521001c0e4000540070500040c0744000d582c3c801c1c91880c5507404c060070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 359501267 1250 359500017 359500019
    0x405011b090501081320121203011a090d032006011a0904020702100804020901061b0314070c0f05010212070f11060d06030b06120303070807030f020903061003021504 73
    0xa00c002601e0055034140022140400e0008001e0304c821440c06506c002c944e6101d607441c04c01c2e8048500d80000b00c2d40200c3c09180c8890401c4030202e021401840b003004468110380c602203405002c1c4880c0100c01140a200b0001d15041ea158842d08104c0c0c10302945a80540d800d000da51041031911200d500e2056410580c0140020030402c07a00c100000303001c01d1b0454840c1c1c0b5120020700203105403600254001c07184210079030003a804c5842130748968002c80d5041c0160383c0c1d40702c060b2140000c0003841d2003a09000d84210300001d0090711088002c030b000f11059420700d11079950351542c014049e04100d012800e80c410030055903030b04010701104265042c0550b414840c40341e0710301007041050b0301c000380b6881d0307480f20880090700c6400c199403100204100501039160340c0e042c240013441e401c2e50070500921001c0c1800401c0d41d0008100d034060402c2e962621002e07600c0120440c001d02101c40313032400c030302d80810840400d540c00300100ca0094410b0003016445510354410048419020140310060003000e00c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 359502517 1250 359501267 359501321
    0xc0c14010f030b1305041103070e0903090d110d0302010f06051c0f03031410031a0f0a05041704030809130b03060a020f0904061410030b030703081c020a020303040501 73
    0x1000801d8102103007404241a0010382c0041d070222034025a01d85000d01d010b04000501007034128130441d08006405403600305850f002c50300c10601c001c0315101c07a00d83c002c2001907440e04100d8844036030345004542d00c010428484002640d004a56101030700140c1d140c14190300100360307600c0f5001c01042c08613200843d0601240000310707203600c16280034189101503401d10303061601a801420307030215035170028601c40c03424240800d049201c601040c0e1310240d0300042e5400802c28503100c2801044c10328210501039640c5000800501030081046800082d8000e1485200c0c0c3c51201030701c00303944103031411078442c5280d40038840d0307007492200f40c1031890f400c015140150f0f480118180d608401107502c0913a58a88401c201e581030301c03070844c009801c540351003000901070101c400c000503034a00842e4082500c004815048043d581c480e00d04503456000303039008000041907180207101c18000109040e01c01400001c4407000c03030b0170800f0b01e280903800000410003040020300c200d40c1840e0f07000c2c0f010300301b01011036 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 359503767 1250 359502517 359502527
    0x31608060f03100905012703110303010b0f07020a05060c300f0322030f12050606040920120108060702151524090f04050c0306040b011e0c0c1401 64
    0x1807010703042c0f10b94900b485024031200b904888914410b01800c20340ca40ba2600200c202c280721000305500003954141100001c3d500807084a04841c1e5540009042021030302c907180d9698800c03902240d0103211510700180649484001c1e106000d00c08000d0191014005031a014a036103d08070138595a201c440088c0c0020002e10981b03003404079054a60740c50342d80345403804041e283c1e40052900c000c0d039185003c0e020183d01402591002407644c0c1d81c00c10400120044405580081d242281c1c041010300041c01240d0040e03100c08901800001007010f0030000310070b0345d140340e80002c46005440c03e0383e20042c4408102001110f07040301c0c03180300602c00d400c804401c000c00c042011380001120138500c444405e050b56036118005c16502c5034280d103040c50210300c81070400780d40f00365082da0040040d044421a1441c09114580c450f0f5180c0c41424515500c031010000200703c125440ca05000143c0300c901800e03048a101000380c114291508200000c10381810310000c583c6030301c03220011401d50303070250305642c0c85 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 359505017 1250 359503767 359503783
    0x6050307030b0c070f0c0e0a24170c120f07081603061104090f1409030408060103121103040e07120225050715090512010207021c0215031608060f03 65
    0x198074030381d00c425607803178100c0d1070060b412400740003803203580008180c000c114544d06024404000040020048484038440700c100309180c802ca0a9489607001c01c0001c2c0c00300308580703050740d0020503580e04000050014644100c4510501d0b41c5502c0717005111049002000808090000000100380d8a4900341c80800a0070b0503010050120340c032809528491a080360580f009001c640805000684404100c600140091481c01000120300740100d5444c681c080110f405031991100580134581c29030700d4202c4903406105c010300803c86610503044509009101400c05080c0d000b001c0320b03090600040040c41c0221a41d02120960710400101c685102000e04102c2180c1e1403241e10701030386c1c1003030802c6820b08000c1e41c00780209003100c109082020342d00000940c02e813071303040300c5051200d807041c0c61071402c034018504025007040303841140079a10700340e100d0b0f030341301c002c1c0b00a00d071200c83d60600c07100a041d9001910001c00707002e40252518291a080100b1b541e0003070058801c001c004514100082ea1841c4e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 359506267 1250 359505017 359505031
    0x90c030c0d0204050409050c09150a2d180f020306060415020a151e02040e0c07080c030a030506041a03030405101b080705070e06061c02090405010306060906050307030b 74
    0x280c0781003000c0c4140c0540d002020000c0c420030030030f08241002921040c1c12107903144969420000505000d601e6007450780003542c0680b000500c00c1c18409440034084c441c0509848910104a242c00324031000c0040401030000300284196040b6500145801e50360030140101e4070314010320401c032490700c0e41000d840032914450f0b410340c41d107801d9400580c10010840009022800d000416048081041e080320404500a24031600c1034044002e90b4800c80c021801000240c41d101008200961882005090118059014507240154620401c2c1c40c59101c03821800c040f984039010040b192600b071264080d03020058052406600c00800020384074441da0141d9442003504600d644510f500c03840328011841020102d040d403c0304a170410407480c1e040885c04585070b10a42201140051750352041074090040909018207140070100c42e9500c03c0403450040d2102a401c1c080c41855640354080c071802540244400101941443e641c50161580c5401c8540a84d01000c0700700002680010003c1c0d1202c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 359507517 1250 359506267 359506291
    0xa061806020a0f0b04020415030b16021614120601182409050a090c03051c1803020f0112050709140103020a05030105062505010c091403030a0f0908011811090c03 71
    0x1707070354400280145220390f40505101442d050110070002040c10050041c16611902c0c00c0f905c11014040360f440800e074440240074184071004010301079521200ca10340004c0140030070602070f1922015031030280246d1144403048500b028400307903c8013900c00d00100e601d544d0207600c0d24001c0143c540740d9078611481180e4a0030380c0c89001410884e05644844c1e01c09a1003030700c8120059590402c2c640d1a00c0400c00700e0710590b800b00f580702c101c42c0030ba002c5210702d01110281c105d9262842d001c00281400036050306040c05410b00e82e548000303542c2d00c0707014800c0040ea00d51203040d0b424100d01c1c8404c0f50044d000141454410000f0402a5810006590445004550f040c2c2e5070802c0e2108944440c031200c8501c040e810400e064441048810341040c0389003011a550703030b84c42a83e41d011904c80c144a0b11181c6406070001c100000402d40b01c0c19252343c403d40e1700d040c03244449903075400d801c0c00c4804803498101c049c07004441240800c0031401908040f2602110300d60310504020154214902c4042e0000d1105a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 359508767 1250 359507517 359507521
    0x5030a0c0f0503070e130f05010f090209090c09030c04180b060103020a0203090409140a0f1104050412081807060504061205010506030115030908181014030a0f0b0a061806020a0f0b 79
    0x3a03106d400d0390348100c01504040c09101502030514000e00001c0c095891100080140410700d0980d6109460075400300511030502c41e210f580201c5195400981031030380502840d81c00f040715403602e0040c0320301c2d4038150512440101a60901003200c46000c0e01e500e0400d4010801c0c2a03040d0b9000041c0c85258004a400240c1e4240514000448211000300000c0034041e00c2221824012011000360303401e40604142c0b4441c0d01a2801c04c4202e070000c840050201040c01400260a1710903910942d002d030205070105804104a2103139440c100307c0c0d91200c0c6c0010000241404160350100b11201c070300400a200303100c1541080c0003e105800305020f0b03c880b1800080c0b0340c20341c45110780c2000401d190005070f8190754020342d480f0500040881e03018a80030790409400503583d284510404000310411b00c6640e825900c480c00d0700b402403c8800d1030030f0891500c4841d102040d9680c500c0d007078000c00340d54907503071246030806030450134001030b980c010015074002d6040c51001c0742c002c0140e8004c41e5070000c15a201a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 359510017 1250 359508767 359508769
    0x10c020c19120305090307080d0504140d0f0506060f090603060402012f060105011b050c1c05070905040209090604030503040219080102070606090f06050a180e0d05030a0c0f0503070e 80
    0x840c00c580c4104228550700ca40d0700103151300300000300517440e03054007910603003510341c8a04c641d219492800b840001e001044200100d496a00d002107628030300070981f20124250791a14101c0d02032023181550690043e506020440ca42421140d2503001e055403990300318030b840c4000070b80b241070003400030b07041c040c1c0c8410b8210340071005000c05200394850200700740707845101c0030803555440c424007515004c601c047001e07952030901458405d05410795100006001850150040c0803800e043d00b90030030802e000611a400006a092162902a040d80706002440d86040e004100c02d40d00042d00701c0075a6080002071201007503018040300d034450740603940c07080180b415002e0603865602c5a80700c44143d51002c1007030b000304070710344e000703c0308a96001da41442040c408540640440d511881020f600042c2400c04000c10b0303480181e020b080060f0b0000004040424901d46420f10329140030850005800208201c04030a50b84580791764910146420702c2841513450000e02140f001401d80d078140404480c0d80030407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 359511267 1250 359510017 359510059
    0x7020c0a14030d030608100e0708010c23070f030509030c120609012a21020708040906090501030b040609140f030c01050a111b070b2802010c020c 64
    0x21204040e05032000940c1d14800c03016400840c24007107100c0c0c0a50032118a406203c2d00450043c0e81c2c1003c0500025100104000000c0aa180028603640290103000405000c00c1c4236806100841c0d889640c0300e00c04811000c0c1c2e400b1064003244d050000284101000304501444c983e03507407a0f150030019500d8807a0f400292901c4060120194011039040161015000c00304c3c04c10300030703000c2500a1002582402d01c0b04000042c0581e0320303146409409004034550b02c20740c251210954401d0300035403c500394006210a89e448080107480401001034108006203251041c1d0004011341d4408004c6035045075180c8074204c1001d40301401041e02c9058907070034804002c07013414050408004503075200c03640d51101526074020403183e2806501c1d1400094080c0c900b40110300b1448804620f440c60400d02d5044003228012090080c840d41c4108000464a58007aa000f814010312031214140584410000c8a0b200e905052012003103904000c101da401c2a00000c4400c4012011600010042c4404001c006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 359512517 1250 359511267 359511283
    0x40602030a141201030f0201080a0b01020c0d1b090203180105070807052109010507030f06030f0f03050f0c03070c052211070b040f0303060807120308071e120c0c1a0702 74
    0x400c0b102c2c40000410064911b01c103040c124800c6c0c80b06900b40d074884840c4000c480d00e00300c0d13142c00358121700e42c3d251640c9044014400d5091240e12008620444645a104024491340122209640c0002401120650080345a00c060301101c020b100500d400701e4010800c100103031585040c004085003004003074400403070080000c0079070380011a040c82e0424149018110a42390140440d01e4500e040c0c00f890010700820082d00c1e0000860f00c4074004996031800765442e40ca006408009091148002c1d0201c03403002011005604401962a20b5160500c0081460302d68407492095400480030030502d41c40600350322980d400b126000500e00c0714a10340207514407aa00c0000c003603a40140400040095480c40c4800031750003075070100006a00e4034005940c91825010302c1d4956914031066900080c801c2c4c00950b80010b01e0b19140d21099060a80001c141d00c090781380303a0108189541544040c1e040f442100030112481c50030441803a0961500800801e00491415845e20504d000071030003402082142c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 359513767 1250 359512517 359512537
    0x151006231204060b06070201090b0a091a040303091508190605060a081609030503070b0901060509010305010f1506050f131703030f0603010c0801120f120306050a0506040602030a14 79
    0x1662541d6041d03244003110812181150084c0c50100842558203001003610f00c0780b541a10313400d60140c20569408182e8000145036070810080c103101050080c101040e0642098000003100c1d1980c2c118580a4010300f0700740c103c0070000001203070105100f0783c0400b4080d00880d9495015181c00c1070154041302400b556003013241c20000c005000300155034060507040c855900d0360120f824440d2015011601e140c8a0700c0050540e074401d00241c00460440d8003039940103000100000380e01135071540400e40c1100264410380e5165900d45141021010500840c200c9080c24a180d80d107850510300050681e00503014900d060142c04603140c3c1201380b080140c1c2010f4445142c00064071000e002e6881d0381c1758801c0300c1c90103611004a01040660805010b0000000d0881d10f83c1c08640c0c1c01c09006074041c01d00f01c802580c03080ba000803c640440c01d42c10708450a80e0703040c0c0d0b000c140c0c0ca060205010b49401298001c90040004002c2040402d40c080151803d130150b6203002241d40380b00b411007a0240c082c0c01c03010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 359515017 1250 359513767 359513837
    0x7200106150c1e0b01051306181a0103052502010e01150618061205060301090b07050d0e070302060717040801150612050411010e1206011205151006 65
    0x4410711541040c1c2c41c002c694403c1852181d0a03600030b241c20075042e42c4842c024440400800103100710700d040141c0480700078511400141240e80c0e02001048068400d061190b0030350b4801c075080c00e0304940031400030903141c01c1c00c0c28011400c101104050004100c581039440c00341640c1d689282e0341c800c1d0030a00c4040400300003031058245644040740102514860070010502c0406c074611084113091400b8111010790b02c0740700314420007090300c001502cbc0051442e541950703540401800075010481450269545541c0c0d1511210140040000c44081c0000c54a050b40484030810041ea2400c0490310100c0d4080540d9403000c40c0707103000c00000d0149800c00040d650074000c042c3c4181d034030348406504a9240703940e060003103079007001d26800f120782c1a54094480c081c001d040b0f845079401806c51482c6030402500a40581c0c02042c0214100582a00200100e04ca106504003e101c01000426030300507001c42c0000070750400a000749102c0c401442403005100212107194541c084617134804d480c00f40d12401e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 359516267 1250 359515017 359515049
    0x411152812090b07031401080d03111204030903020a05010207030503160606050901090c09050108061c020a05130501241b03090e07050d05091209061309020408150601050307200106 79
    0x10805018204c90301d070000303403425800c00c00f112181c001a904850340e84001e441407035402030048001e0300304542500d00f50741cac0402c4120700e110a80301281e0301c10741c040ea0740c20b0f0140d419441080502000303a840181103502501c400c1c03020440200c1140c94000c0c403c0d070300001e050000d1038540090b018036400268080101d100003d02c03211941c0004641c8660b036669032004584030001501d0f07a00c0b050704d000d80c104403507000c011900365980880024050000300f6409209640f100020300d200241820750445030707155001000540984c1c45001080c03118000f061400030a41d900080c5981c50040844505651110300b50301454000d03e05100035103c0300c0e0450900b807400a402030403da2250005510b4545032a000980350b0101040001010b6031f203490151424140204100f030a8103c44d002180d144e80300c20000405410ba880180010b06410001e4079541040c240c16003400c2c0e00040141e4140641041044521544000d550004010007041c2554814039044070320300608403074000b600c1a44403001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 359517517 1250 359516267 359516273
    0x6300507120203070e060918190e060c070201120b060c1608030a140a03020c03190f0e151305040609050910060b040501081302090103031806090e0f130605041115281209 74
    0x280c49c8106034014051244d60002d600280d91000d00301c405210000c400c0c01400c0044d07114558480c1c612200000202d5440050300014200e0740c000100c0002542c800d018081045550b00c1500b0010b0038181c001d1b6040415000018045401c07901c0300c18085440040d94404207400b0780d058440e000980022291a0f000b01c10040d03c2c51780011201d6000700302c1031110301c1c840500c280584000968050804100c8503003901c4034090795003088200d00c2009408c51000300c2c16441d40d210704401400020070205043c00c2441403181802510f0008070f804904000d010f2007074001500840303040f5a07080c6001d85040daa00f8156000034a00803a0080d40030322400000028144d200740044240010500d031005110356500d000d50302c46400d44074480c0b0981c800e0000800c21218001070940c001002c103c0a00071504a41c2d0b0030f800c0303c100b03c4040321074060802d81e01c0103509000c42102240b00003410410310b0204500c6124074621a10302180301c04030203800d210b00110784210092000095180c8050205446500d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 359518767 1250 359517517 359517541
    0x2031905090f040506011d04090b10030605071103090904020604030614010503071202031e03040f03050f011d06040b04020103021c051b0301050a06300507120203070e060918 76
    0x29500324424003a80310101980d10780f0344076240c00f500058480140d00c0260042d203a40700c1d951541c00c0d070342c05a1307560f1b04140440c01702c89030b82d40302d50f0200e603800d4400d90951800104940011b42020108020100000d6200e0000011510114000c44030035100b581c542c40051407604c80c941000303001504010100e80da42401d81540340c103a680840680c0d4030705880d041c20039400c00003c1c030041d5160f400300310b0007030200d4002007500c009400050141c0e49482d0f114050428141c001d0b60007218903a10468a0007a410030a00c10304568038a5103160149a182564079240d45140241c00506000100d8002c1021a030280e4101d860750000c05a0200b0152042900c507001800221402c0014411003804038040d6251102182d041c6c0e040142802c1c90141040ba0031203002c46d0460f080c804139181c4860424902d80041290109060246400318192030b0002e07005240d000c03601c01d4a1513050051061046081e00303d040a84005419200e09031a80b54020000d035070060039520b01981c1e60000428003036411508 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 359520017 1250 359518767 359518777
    0x40308070507060221030c0910020304290307050a090302040e0d1218120c0c0f0311090103051c030207080a091e0608060d1103300309030d0c02031905 66
    0x5941a210030b540d4415050340c032810400c0c0f090000c0001302000f0b891050300c12018540050000414904041c91003010801001381e450103500507900208080186c800c14000c0341140d0360104900c808101600d10f400040350002a2000c4244140482c104264611a800c007200540d002030007480b18103000c900864568446c5202e40e000a189002d401d80c134480305029161311031600390404a515841c039125503441c40440c8008800b000002d0a10002040ea140e1915000d420644001d1441c01c3c90343c541218203078400b00c00f0030b003d203265030b004102160f40410701403810907a0503000f943d600c044d40d400302d00a100c0c80c00d0040c1480004144110801d5004840f03806444041d10385400c415401c6ca106002a041c40c4554400507440e5000282c0e41c0c03c00202040d4080c0c400c0300f580880700b003101c00003820502c040e0908041540882c810245440009000320206802100d0300d40c6141411005036071a0300c21030404181540e1244021401e82d40308104990106020001c0400100074018000303200b0381c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 359521267 1250 359520017 359520023
    0xa0902040807080105160309030203070b010807090b04090506450c060403120516060203040b0601020c100c0b04080c070b21130b06030c030304060806100206010608240604030807 78
    0x1400740101d800f039014031669025040e01c6000410800e07a91301d00b1130282114a00c11421030006112200010b07804412560103001c00e200501503d1381810403a1040342d504892980c86182025907101c0411008144590080640a80e440d642114882c0b02c82c80d03007801410361074050280800580c1694182400c044518a102041e140c110304103904107c030034012400003400807180d814400400600a40c010402421051035100f2248070503101d01080760012130302900c003107440d4401c204071503a0501220080e040b0032580c0302c89800c0ba10800520300c8002000040a041710200400c00b404243e105540300805054111406180c55014065040d000381410190141231480789500425014000074810b80c1801e009540c2e409542d10b5241a91201038000c1740c045c01024004240354070144000c201603c0d860b1115841e0f41000070601080084215001e001c5401a8006115650f40b098240c1d07040f40300d9000316108a03051200f114201030304040c24642c04440024000100400040506030f6940 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 359522517 1250 359521267 359521273
    0xc02030c0603090d081f0b0702030d050c030d09020609030f160503150a020d061503090b01081204030803040c05090403090303030510050901051002010e01060611070902070305030408090409020a09020408 89
    0x220300050081078001541e0038040f641258144010301481501c409510600840c3c0c41c46101e007260740c070345e50020102d81040c8124000003913428150b0604000144204140386019880c00c600c01044580700e000d2500c00000310307615002e654065645040a0714040c3c43c00800341da00049d020142c030390340d441c110041c9201d120f0400b800001c080c50042441c02216500d26004c182c10342c0c903004036500030342c003a6110420956541c2c80200e4083d98459040c3c0321018291000102030031a410410448001640912807a51003031216080701e07000c0700d00790740031640d00c0030490383c40b83c071280b50403402d0212940040340c000c80c40300c040005041c2e010a515040b02c0c0207441c200007985071100c0201808000d402010b41144400004019905040c1c00d20407030307102c0030310000861408209540e030946510394451400111001903e1000c0841030005d04001d242c0080114030b0f01c03c25990103403050000401c0502864804100c04006803030319009201c1d01d51f030003001c42074440d445002c548000c1d0840d0051485c584 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 359523767 1250 359522517 359522533
    0x8060610020a0302190317070509011101181b031b05040b01030b03120c0708030c0c04110a0806130207080c06180c010e0d1a012304020f030402040c090b0a0c0203 71
    0x3400842e030000c00743c0c0c269024005a44190340c1d480c01d02600d15504504100014041c0104088030284c0e050145100c0d41d00d903582c03940d0400004010811000002380345900d01115050007520b030114028076660b02036035050060014ac042a083c0c40344580c806032808580102c001e00070306000031450305855040381c00f000b410350468011421510064030301038056002c000003600d1340d044030015020200f200011120b6a5864034809401c68002c4100950241d00071002e003007152030980100700101c2103828480e0700700f101403130f0300404000010b0078141c003550a031402ca104102c41501200d055070f0b00700007440d0782c58402e4001540d40711801c507080b1400305d00c124031412301c0c0103000c40c8402d11448140d43d546c440741c001c0d0041203400348408004a48406101100070a080d001d968485c1c020300140d0300c0020b4101d8030350801e4540a8426079200e124620406c602d40040146c8010b90340c000f50180c600040e84180c20700c0503034040143d038201214000000c511070651503800745915200c94400d4003070b20204 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 359525017 1250 359523767 359523799
    0x4060b0708090405091603030201140106050307090e0705070606030b070e03160306020d141e09070509010918051228050a0f021929190f09020901080606 67
    0x80c00340d80ca0080103808108149151440c15410150b04051010b00307503002c01c04141074581c880901984201d000d83d45404089841d030072440d036420300400750707414094031b036241849000f007040e81c040c05401255a011008544100e11550994a0081d0b110383e0400010341c5a04060765000c604aa81400080e80d02100c540542170105a2800300320380e1034561005141103540742c0d800794000ba040502001ea462112580b10b8203916a5180106201c2500d8403900c051740d09c500002400047c0304036900c0e400498100419166010300741d04541c480c5100084801d6040c101030203403500d030440030304203100301124941710054000090614081d483e295109005c050020103204040c0c141c103020214034107210b00c00030a400b403905001c0c40724162064916800b0f807101d2910000300155829201142c80c0c8030101841c5000340121140300e400b5070504145480d10350488210390b446240c51010442d240c400f04549408990011404280d000380803090b02d42c2c440f2016656a501100c0442c404e0441d42007280d41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 359526267 1250 359525017 359525039
    0x50910122c0c0109050f0103020702041517060906040f0201180b0a0e04050105060703140408030c010b01031a0a05060a02010f18030206011a070602030c0c030a02060a0507110a0b090a1403090406 85
    0xe0b02e0410b03100c0c03101c502e240c6010050002c00420045052507002c000c84070050b82ca5100e000d01d911401c401402001c1d0909210120080c69204c02812680c042804d1000002e000200640c0c010b6011482a0301c281c02440100d8800c0d02c00010780101d00100000861160501c402505505d00c460b40c50303165607085101000107652081c400da60b003181041211801007446a0a841200c03e172004c0050300e0180d9a5a03120b1035540701640c40751841e552506601025a45030023a61a603580581042ca070301d18000e00003401807181403151031301c1508009200c2100c14001e4000600d1100044c604000201c0c0d0058000032070101c01c0301c04c4005001d100000f003007452002000b080c0b0350900c62140380c1484020341c3d1380030082d840504007460b41c40c814071400c85440c0e403c0005007040700e0503034003170012030074040400380c16074902501c0038090086d203400040003c000001c0400c803480d040007500c8015201c140e000f5003804404040a00482c00350003003041400c000200410114105031800c020b441d9036141c241e0a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 359527517 1250 359526267 359526283
    0x108120703140d0905060c0301050406170c1e0409140d090803031f05040c0c060b060c0c0105030a0e0312071e0512100b031f0e07050910122c 62
    0x1c100c0e40c200e0b00c20415640000741000d00810500040c8034040c9407182485c124086034851a0400300100600c618201030146000034513001456514480c180d0100986904013955000d004448846014400740c021a502d032004140c050700410015010341024500010410461001c611507010b04004070b43c410b00010f8211303480c00c0044c60940c0c85611184034400c01994940d012015041c00101301581c1c1c5100f0000201c200b5110400e074000c142c03070184156041c080703000b8481c10303050180d06040c0d000072030103182800d000d1038120303a0703a0703140c5002500400c9210307032001c21444003060260b07511800f41a514010b00c11601e07540807180c040011050a01c1c0d0302c4005400007807051007504550b050150070680c0150081118101140e1a1000c0c1d01e601d0b041165907400202c1c26600c8541112030824100016000440e08045113241021016000c1d1080040c118000c88100043c044110310409640c10401b6640000b4031448040d080d020320003100c00c10060b45d006840039181c550040000407450 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 359528767 1250 359527517 359527523
    0x1508060609010e13020d0f0501050f0a0b0306010c060204090608012a17190912030c14090d08040b0d0b010f0c05100506031e03043b070309080a0801081207 68
    0x1d011100300009100c03400758452984001c0c4ca40a00c10150b89090340d02451030302100b0035400050300d44c035107020440103c01c00e04040340108074240052000302c038040100c0e6032103202800c100c0030b00742c411f1420500903c03440c0d1100045074035111010074030b030308103400c1058254000690f031804951225040b04071050303400300c03140214400080c02c200c0c212840c1d90301580a820707071081c00000d43c0c201400700180c0300101c3d41201c241c07018103040b0404d80e41500c6502400100c0c1e103800001d443e4000c0f1005aa403040e03506540c41842410080401c00503076404403006424401310745900d0344130000705da0028104000f6000d000c200000c01003400b00d032040504032041d9400030020701d032000e00e0000c0344004000183c1810b4150150200003c075451140d420070140714103d00007196250715000d1401002c1004184840ca81c1000d0500b468981242c2d62401c89041c16075503038000740340c88114086d0000d02d0f03555802442840085a4601025008201a07040f200418140e50900545e01c004049d85e100e03400f401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 359530017 1250 359528767 359528777
    0xa0806190b01050d1407031b0504031103190303151a03040f0314040b0c0705060903070306050705041701050f0c0f0711060702040204030b07020d02010209010f0305150a150806060901 80
    0x60401006a81c10001c0c00120604000e07140c4030b01040810b00742c8503a6003000c2c01655215041c49900341d414410200d07e00000707030303a030001e0310518a4018054820351001170b1403420078810703190090780d0030b011003080d0b01545030800020b45101e14018002e442c00b000d003040c8100c0c41140008010040201c50038600701600d8490b455543e40355039020090788111000d50030001d4400d030010b6020b01800060010f071110460b910307140d41d00110f0240c904000754011601441c4280040b01080c0c4001840000b620b50100000c0344c1562241802c079981e00466000400c155001c9501d000812019441280a06205201d110090f80c1c0e403501001d0307620600107010900f07039042058402083c18404000310036440102854685074079500024113981048d0020750f007400d20a0305001d03001d0780420911055240c540025800c00c0c4620001030300c0510281821802e16480300005115009440442480c60000900e20614242c40e041c600700c801c004042d40c0408070b181d000110740c3c00c3c40c1c0078098501e0008160741d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 359531267 1250 359530017 359530051
    0x170c0d03120509010b041e0b0f0901030807031e050a1d01081f0905070305060a17030f18030a05030c01060b0c03030a0e03070602030f0609010623030c0403050a05010b0a0806 76
    0x5007000404000300000d420b03540c0c1c2d90b00780220f562240200e01d002c40803210120103840404254a040b038403140d5000d0701c035100c1d11500641c40d40300e000909044940024020745c07a0b141608007600c1030403842020700444407181c0041211140c11402400443c0c5c2c0c0c0e991041c4486c45940151300180e6491803e00f404a49a00c00050f103152072000c040c1603000f0f270341c0c01440c100c170ba41d11070300c03400c2da0340c19114100481c1d00d0300208203582c00d21241c490010003500c403440c2054000f10702d8868981c8940000083c0f6604001010142c12180318818a000780c03002e8200c844400c00d07814244d449802031000c4561315420302c4c80002d103007003129098078000d45504000e0351942d00c0d4945140001c0040300c40c0d52041c0d000030710280380070a00900c042e46c454070414a0703a11452408104202054005030805410700c040d80d260301180f40c1e40c045245440012400c0e409560742c50b4980e20104034003803940010003034460400c000e010840e06400c0f0706001403040d104803c0142e210034401c0e480b100308a80140841c46400c403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 359532374 1107 359531267 359531297
    0x102181233070f0e010318080c0105011811042d0b13060309120f050c10021c0902030d0503060d0b0705280f12020d06170c0d03 56
    0x9402c0c035a82c0da032004090800342e0403613080b43c1010394811007642c0302d02549003106502604540702c9901c884200900342e02030705090213107007100e155400c031842104010f40620072003420903500703a90a143c14030044103034104050680c540d1540068880803040f1101c2c0da03444014005180d40f1039519500c5104410140740c0039032110702014a0983d41c07001140700054141070804991400340d00d0890100b00440301c40c0505450001a070140344001e0328010502e500a0810600c03180c0e1070007012844c4100a41140da504002039010741003020381d000b0f1f0503c103200542d400321005182100b0440e00342c075a94900c2904550a80c00300e48001050042001c90180c40104100615140d01104099142c001d0002008040001c01c1c0440b40440c02a20703403a50701514203043d07a21100b0810903581340c1d0390500d000f100008940a40c06081c9600d071250512410f05003103260103441d1400101070b404 = true := by decide +kernel

theorem cover : BRFrame.Cov 359352517 359532374 := by
  have h0 := BRFrame.cov_init 359352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 359352517 ≤ n) (h2 : n < 359532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
